/* eslint-disable indent,camelcase,no-unused-vars */

'use strict';

var options, location, input, text, peg$cache, peg$currPos;


    var pegIncludes = options.pegIncludes;
    var pegTokenizer = options.pegTokenizer;

    var env = pegTokenizer.env;
    var pipelineOpts = pegTokenizer.options;

    var DU = pegIncludes.DOMUtils;
    var TokenUtils = pegIncludes.TokenUtils;
    var Util = pegIncludes.Util;
    var JSUtils = pegIncludes.JSUtils;
    var PegTokenizer = pegIncludes.PegTokenizer;
    var TokenTypes = pegIncludes.TokenTypes;
    var constants = pegIncludes.constants;
    var tu = pegIncludes.tu;

    // define some constructor shortcuts
    const { KV, TagTk, EndTagTk, SelfclosingTagTk, NlTk, EOFTk, CommentTk } = TokenTypes;
    var lastItem = JSUtils.lastItem;

    var inlineBreaks = tu.inlineBreaks;
    var stops = new tu.SyntaxStops();

    var prevOffset = 0;

    // Some shorthands for legibility
    var startOffset = function() {
      return location().start.offset;
    };
    var endOffset = function() {
      return location().end.offset;
    };
    var tsrOffsets = function(flag) {
      return tu.tsrOffsets(location(), flag);
    };

    /*
     * Emit a chunk of tokens to our consumers.  Once this has been done, the
     * current expression can return an empty list (true).
     */
    var emitChunk = function(tokens) {
        if (env.immutable) {
            // Tokens placed in the tokenizer's cache have been frozen to
            // to catch any mutations while testing, which may have led to
            // subtle, spooky action at a distance.
            tokens = Util.unFreeze(tokens, true);
        }

        // Shift tsr of all tokens by the pipeline offset
        TokenUtils.shiftTokenTSR(tokens, options.pipelineOffset);
        env.log("trace/peg", pegTokenizer.pipelineId, "---->  ", tokens);

        var i;
        var n = tokens.length;

        // Enforce parsing resource limits
        for (i = 0; i < n; i++) {
            tu.enforceParserResourceLimits(env, tokens[i]);
        }

        // limit the size of individual chunks
        var chunkLimit = 100000;
        if (n > chunkLimit) {
            i = 0;
            while (i < n) {
                options.cb(tokens.slice(i, i + chunkLimit));
                i += chunkLimit;
            }
        } else {
            options.cb(tokens);
        }
    };

    /* ------------------------------------------------------------------------
     * Extension tags should be parsed with higher priority than anything else.
     *
     * The trick we use is to strip out the content inside a matching tag-pair
     * and not tokenize it. The content, if it needs to parsed (for example,
     * for <ref>, <*include*> tags), is parsed in a fresh tokenizer context
     * which means any error correction that needs to happen is restricted to
     * the scope of the extension content and doesn't spill over to the higher
     * level.  Ex: <math><!--foo</math>.
     *
     * IGNORE: {{ this just balances the blocks in this comment for pegjs
     *
     * This trick also lets us prevent extension content (that don't accept WT)
     * from being parsed as wikitext (Ex: <math>\frac{foo\frac{bar}}</math>)
     * We don't want the "}}" being treated as a template closing tag and
     * closing outer templates.
     * --------------------------------------------------------------------- */

    var isXMLTag = function(name, block) {
        var lName = name.toLowerCase();
        var uName = name.toUpperCase();

        var isInstalledExt = env.conf.wiki.extConfig.tags.has(lName);
        var isIncludeTag = tu.isIncludeTag(lName);

        var isHtmlTag = block ?
                TokenUtils.isBlockTag(uName) :
                constants.HTML.HTML5Tags.has(uName) || constants.HTML.OlderHTMLTags.has(uName);

        // WARNING: Be careful to pop this when `isXMLTag` is used.
        stops.push('extTag', isInstalledExt);

        return isHtmlTag || isInstalledExt || isIncludeTag;
    };

    var maybeExtensionTag = function(t) {
        var tagName = t.name.toLowerCase();

        var isInstalledExt = env.conf.wiki.extConfig.tags.has(tagName);
        var isIncludeTag = tu.isIncludeTag(tagName);

        // Extensions have higher precedence when they shadow html tags.
        if (!(isInstalledExt || isIncludeTag)) {
            return t;
        }

        var dp = t.dataAttribs;
        var skipLen = 0;

        switch (t.constructor) {
        case EndTagTk:
            if (isIncludeTag) {
                return t;
            }
            // Similar to TagTk, we rely on the sanitizer to convert to text
            // where necessary and emit tokens to ease the wikitext escaping
            // code.  However, extension tags that shadow html tags will see
            // their unmatched end tags dropped while tree building, since
            // the sanitizer will let them through.
            return t;  // not text()
        case SelfclosingTagTk:
            dp.src = input.substring(dp.tsr[0], dp.tsr[1]);
            dp.tagWidths = [dp.tsr[1] - dp.tsr[0], 0];
            if (isIncludeTag) {
                return t;
            }
            break;
        case TagTk:
            var tsr0 = dp.tsr[0];
            var endTagRE = new RegExp("^[\\s\\S]*?(</\\s*" + tagName + "\\s*>)", "mi");
            var restOfInput = input.substring(tsr0);
            var tagContent = restOfInput.match(endTagRE);

            if (!tagContent) {
                dp.src = input.substring(dp.tsr[0], dp.tsr[1]);
                dp.tagWidths = [dp.tsr[1] - dp.tsr[0], 0];
                if (isIncludeTag) {
                    return t;
                } else {
                    // This is undefined behaviour.  The php parser currently
                    // returns text here (see core commit 674e8388cba),
                    // whereas this results in unclosed
                    // extension tags that shadow html tags falling back to
                    // their html equivalent.  The sanitizer will take care
                    // of converting to text where necessary.  We do this to
                    // simplify `hasWikitextTokens` when escaping wikitext,
                    // which wants these as tokens because it's otherwise
                    // lacking in context.
                    return t;  // not text()
                }
            }

            var extSrc = tagContent[0];
            var endTagWidth = tagContent[1].length;

            if (pipelineOpts.inTemplate) {
                // Support 1-level of nesting in extensions tags while
                // tokenizing in templates to support the #tag parser function.
                //
                // It's necessary to permit this broadly in templates because
                // there's no way to distinguish whether the nesting happened
                // while expanding the #tag parser function, or just a general
                // syntax errors.  In other words,
                //
                //   hi<ref>ho<ref>hi</ref>ho</ref>
                //
                // and
                //
                //   hi{{#tag:ref|ho<ref>hi</ref>ho}}
                //
                // found in template are returned indistinguishably after a
                // preprocessing request, though the php parser renders them
                // differently.  #tag in template is probably a common enough
                // use case that we want to accept these false positives,
                // though another approach could be to drop this code here, and
                // invoke a native #tag handler and forgo those in templates.
                //
                // Expand `extSrc` as long as there is a <tagName> found in the
                // extension source body.
                var s = extSrc.substring(endOffset() - tsr0);
                while (s && s.match(new RegExp("<" + tagName + "[^/<>]*>"))) {
                    tagContent = restOfInput.substring(extSrc.length).match(endTagRE);
                    if (tagContent) {
                        s = tagContent[0];
                        endTagWidth = tagContent[1].length;
                        extSrc += s;
                    } else {
                        s = null;
                    }
                }
            }

            // Extension content source
            dp.src = extSrc;
            dp.tagWidths = [endOffset() - tsr0, endTagWidth];

            skipLen = extSrc.length - dp.tagWidths[0] - dp.tagWidths[1];

            // If the xml-tag is a known installed (not native) extension,
            // skip the end-tag as well.
            if (isInstalledExt) {
                skipLen += endTagWidth;
            }
            break;
        default:
            console.assert(false, 'Should not be reachable.');
        }

        peg$currPos += skipLen;

        if (isInstalledExt) {
            // update tsr[1] to span the start and end tags.
            dp.tsr[1] = endOffset();  // was just modified above
            return new SelfclosingTagTk('extension', [
                new KV('typeof', 'mw:Extension'),
                new KV('name', tagName),
                new KV('about', env.newAboutId()),
                new KV('source', dp.src),
                new KV('options', t.attribs),
            ], dp);
        } else if (isIncludeTag) {
            // Parse ext-content, strip eof, and shift tsr
            var extContent = dp.src.substring(dp.tagWidths[0], dp.src.length - dp.tagWidths[1]);
            var extContentToks = (new PegTokenizer(env)).tokenizeSync(extContent);
            if (dp.tagWidths[1] > 0) {
                extContentToks = TokenUtils.stripEOFTkfromTokens(extContentToks);
            }
            TokenUtils.shiftTokenTSR(extContentToks, dp.tsr[0] + dp.tagWidths[0]);
            return [t].concat(extContentToks);
        } else {
            console.assert(false, 'Should not be reachable.');
        }
    };

function rule_start() {
    var start = null;
    (function() {

      // end is passed inline as a token, as well as a separate event for now.
      emitChunk([ new EOFTk() ]);
      return true;

    })();
}
function rule_redirect() {
    var rw = null;
    var sp = null;
    var c = null;
    var wl = null;
    (function() {

      return wl.length === 1 && wl[0] && wl[0].constructor !== String;

    })();
    (function() {

    var link = wl[0];
    if (sp) { rw += sp; }
    if (c) { rw += c; }
    // Build a redirect token
    var redirect = new SelfclosingTagTk('mw:redirect',
            // Put 'href' into attributes so it gets template-expanded
            [KV.lookupKV(link.attribs, 'href')],
            {
                src: rw,
                tsr: tsrOffsets(),
                linkTk: link,
            });
    return redirect;

    })();
}
function rule_generic_newline_attributes() {
    var generic_newline_attributes = null;
}
function rule_table_attributes() {
    var table_attributes = null;
    var b = null;
    (function() {
 return b;
    })();
}
function rule_redirect_word() {
    var rw = null;
    (function() {
 return env.conf.wiki.getMagicWordMatcher('redirect').test(rw);
    })();
}
function rule_start_async() {
    (function() {

      if (endOffset() === input.length) {
          emitChunk([ new EOFTk() ]);
      }
      // terminate the loop
      return false;

    })();
}
function rule_tlb() {
    var tlb = null;
    var b = null;
    (function() {

    // Clear the tokenizer's backtracking cache after matching each
    // toplevelblock. There won't be any backtracking as a document is just a
    // sequence of toplevelblocks, so the cache for previous toplevelblocks
    // will never be needed.
    var end = startOffset();
    for (; prevOffset < end; prevOffset++) {
        peg$cache[prevOffset] = undefined;
    }

    var tokens;
    if (Array.isArray(b) && b.length) {
        tokens = tu.flattenIfArray(b);
    } else if (b && b.constructor === String) {
        tokens = [b];
    }

    // Emit tokens for this toplevelblock. This feeds a chunk to the parser pipeline.
    if (tokens) {
        emitChunk(tokens);
    }

    // We don't return any tokens to the start rule to save memory. We
    // just emitted them already to our consumers.
    return true;

    })();
}
function rule_block() {
    var r = null;
    var cil = null;
    var bl = null;
    (function() {
 return [r].concat(cil, bl || []);
    })();
    var rs = null;
    var c = null;
    (function() {
 return c;
    })();
    var bt = null;
    (function() {
 return rs;
    })();
    var s = null;
    (function() {
 return s;
    })();
}
function rule_nested_block() {
    var b = null;
    (function() {
 return b;
    })();
}
function rule_nested_block_in_table() {
    (function() {
 return stops.push('tableDataBlock', true);
    })();
    var b = null;
    (function() {

        stops.pop('tableDataBlock');
        return b;

    })();
    (function() {
 return stops.pop('tableDataBlock');
    })();
}
function rule_block_lines() {
    var s = null;
    var s2 = null;
    var os = null;
    var so = null;
    (function() {
 return os.concat(so);
    })();
    var bl = null;
    (function() {

        return s.concat(s2 || [], bl);

    })();
}
function rule_hr() {
    var d = null;
    var lineContent = null;
    (function() {
 return undefined;
    })();
    (function() {
 return true;
    })();
    (function() {

    var dataAttribs = {
      tsr: tsrOffsets(),
      lineContent: lineContent,
    };
    if (d.length > 0) {
      dataAttribs.extra_dashes = d.length;
    }
    return new SelfclosingTagTk('hr', [], dataAttribs);

    })();
}
function rule_block_line() {
    var st = null;
    var r = null;
    var tl = null;
    (function() {
 return tl;
    })();
    var bts = null;
    var bt = null;
    var stl = null;
    (function() {
 return bt.concat(stl);
    })();
    (function() {
 return bts;
    })();
    (function() {

          return st.concat(r);

    })();
}
function rule_paragraph() {
    var s1 = null;
    var s2 = null;
    var c = null;
    (function() {

      return s1.concat(s2, c);

    })();
}
function rule_br() {
    var s = null;
    (function() {

    return s.concat([
      new SelfclosingTagTk('br', [], { tsr: tsrOffsets() }),
    ]);

    })();
}
function rule_inline_breaks() {
    (function() {
 return inlineBreaks(input, endOffset(), stops);
    })();
}
function rule_inlineline() {
    var c = null;
    var r = null;
    (function() {
 return r;
    })();
    (function() {

      return tu.flattenStringlist(c);

    })();
}
function rule_inline_element() {
    var r = null;
    (function() {
 return r;
    })();
    (function() {
 return r;
    })();
    (function() {
 return r;
    })();
    (function() {
 return r;
    })();
    (function() {
 return r;
    })();
}
function rule_heading() {
    var r = null;
    (function() {
 return stops.inc('h');
    })();
    var s = null;
    var ce = null;
    var ill = null;
    (function() {
 return ill || [];
    })();
    (function() {
 return ce || s.length > 2;
    })();
    var endTPos = null;
    (function() {
 return endOffset();
    })();
    var spc = null;
    (function() {

        var c;
        var e;
        var level;
        stops.dec('h');
        if (ce) {
            c = ce[0];
            e = ce[1];
            level = Math.min(s.length, e.length);
        } else {
            // split up equal signs into two equal parts, with at least
            // one character in the middle.
            level = Math.floor((s.length - 1) / 2);
            c = ['='.repeat(s.length - 2 * level)];
            s = e = '='.repeat(level);
        }
        level = Math.min(6, level);
        // convert surplus equals into text
        // FIXME: Manipulating a potentially cached result (c) can lead to
        // subtle breakage!
        if (s.length > level) {
            var extras1 = s.substr(0, s.length - level);
            if (c[0].constructor === String) {
                c[0] = extras1 + c[0];
            } else {
                c.unshift(extras1);
            }
        }
        if (e.length > level) {
            var extras2 = e.substr(0, e.length - level);
            var lastElem = lastItem(c);
            if (lastElem.constructor === String) {
                c[c.length - 1] += extras2;
            } else {
                c.push(extras2);
            }
        }

        var tsr = tsrOffsets('start');
        tsr[1] += level;
        return [
          new TagTk('h' + level, [], { tsr: tsr }),
        ].concat(c, [
          new EndTagTk('h' + level, [], { tsr: [endTPos - level, endTPos] }),
          spc,
        ]);

    })();
    (function() {
 stops.dec('h'); return false;
    })();
    (function() {
 return r;
    })();
}
function rule_comment() {
    var c = null;
    (function() {

        var data = DU.encodeComment(c);
        return [new CommentTk(data, { tsr: tsrOffsets() })];

    })();
}
function rule_behavior_switch() {
    var bs = null;
    (function() {

    if (env.conf.wiki.isMagicWord(bs)) {
      return [
        new SelfclosingTagTk('behavior-switch', [ new KV('word', bs) ],
          { tsr: tsrOffsets(), src: bs, magicSrc: bs }
        ),
      ];
    } else {
      return [ bs ];
    }

    })();
}
function rule_behavior_text() {
}
function rule_autolink() {
    var r = null;
    var target = null;
    (function() {

        var res = [new SelfclosingTagTk('urllink', [new KV('href', target)], { tsr: tsrOffsets() })];
          return res;

    })();
    (function() {
 return r;
    })();
}
function rule_extlink() {
    var extlink = null;
    var r = null;
    (function() {
 return stops.push('extlink', true);
    })();
    var addr = null;
    var target = null;
    (function() {

          // Protocol must be valid and there ought to be at least one
          // post-protocol character.  So strip last char off target
          // before testing protocol.
          var flat = tu.flattenString([addr, target]);
          if (Array.isArray(flat)) {
             // There are templates present, alas.
             return flat.length > 0;
          }
          return Util.isProtocolValid(flat.slice(0, -1), env);

    })();
    var sp = null;
    var targetOff = null;
    (function() {
 return endOffset();
    })();
    var content = null;
    (function() {

            stops.pop('extlink');
            return [
                new SelfclosingTagTk('extlink', [
                    new KV('href', tu.flattenString([addr, target])),
                    new KV('mw:content', content || ''),
                    new KV('spaces', sp),
                ], {
                    targetOff: targetOff,
                    tsr: tsrOffsets(),
                    contentOffsets: [targetOff, endOffset() - 1],
                }),
            ];

    })();
    (function() {
 return stops.pop('extlink');
    })();
    (function() {
 return r;
    })();
}
function rule_autoref() {
    var ref = null;
    var sp = null;
    var identifier = null;
    (function() {

    var base_urls = {
      'RFC': 'https://tools.ietf.org/html/rfc%s',
      'PMID': '//www.ncbi.nlm.nih.gov/pubmed/%s?dopt=Abstract',
    };
    return [
        new SelfclosingTagTk('extlink', [
           new KV('href', tu.sprintf(base_urls[ref], identifier)),
           new KV('mw:content', tu.flattenString([ref, sp, identifier])),
           new KV('typeof', 'mw:ExtLink/' + ref),
        ],
        { stx: "magiclink", tsr: tsrOffsets() }),
    ];

    })();
}
function rule_isbn() {
    var sp = null;
    var isbn = null;
    var s = null;
    (function() {
 return s;
    })();
    var isbncode = null;
    (function() {

        // Convert isbn token-and-entity array to stripped string.
        return tu.flattenStringlist(isbn).filter(function(e) {
          return e.constructor === String;
        }).join('').replace(/[^\dX]/ig, '').toUpperCase();

    })();
    (function() {

       // ISBNs can only be 10 or 13 digits long (with a specific format)
       return isbncode.length === 10 ||
             (isbncode.length === 13 && /^97[89]/.test(isbncode));

    })();
    (function() {

      return [
        new SelfclosingTagTk('extlink', [
           new KV('href', 'Special:BookSources/' + isbncode),
           new KV('mw:content', tu.flattenString(['ISBN', sp, isbn])),
           new KV('typeof', 'mw:WikiLink/ISBN'),
        ],
        { stx: "magiclink", tsr: tsrOffsets() }),
      ];

    })();
}
function rule_url_protocol() {
    (function() {
 return Util.isProtocolValid(input.substr(endOffset()), env);
    })();
    var p = null;
    (function() {
 return p;
    })();
}
function rule_no_punctuation_char() {
}
function rule_url() {
    var url = null;
    var proto = null;
    var addr = null;
    var path = null;
    var c = null;
    (function() {
 return c;
    })();
    var s = null;
    (function() {
 return s;
    })();
    var r = null;
    var he = null;
    (function() {
 return he;
    })();
    (function() {
 return r;
    })();
    (function() {
 return addr.length > 0 || path.length > 0;
    })();
    (function() {

    return tu.flattenString([proto, addr].concat(path));

    })();
}
function rule_autourl() {
    (function() {
 return stops.push('autourl', { sawLParen: false });
    })();
    var r = null;
    var proto = null;
    var addr = null;
    var path = null;
    var c = null;
    (function() {
 return c;
    })();
    (function() {
 stops.onStack('autourl').sawLParen = true; return "(";
    })();
    var rhe = null;
    (function() {
 return /^[<>\u00A0]$/.test(rhe);
    })();
    var he = null;
    (function() {
 return he;
    })();
    (function() {
 return r;
    })();
    (function() {

    // as in Parser.php::makeFreeExternalLink, we're going to
    // yank trailing punctuation out of this match.
    var url = tu.flattenStringlist([proto, addr].concat(path));
    // only need to look at last element; HTML entities are strip-proof.
    var last = lastItem(url);
    var trim = 0;
    if (last && last.constructor === String) {
      var strip = ',;\\.:!?';
      if (!stops.onStack('autourl').sawLParen) {
        strip += ')';
      }
      strip = new RegExp('[' + JSUtils.escapeRegExp(strip) + ']*$');
      trim = strip.exec(last)[0].length;
      url[url.length - 1] = last.slice(0, last.length - trim);
    }
    url = tu.flattenStringlist(url);
    if (url.length === 1 && url[0].constructor === String && url[0].length <= proto.length) {
      return null; // ensure we haven't stripped everything: T106945
    }
    peg$currPos -= trim;
    stops.pop('autourl');
    return url;

    })();
    (function() {
 return r !== null;
    })();
    (function() {
return r;
    })();
    (function() {
 return stops.pop('autourl');
    })();
}
function rule_urladdr() {
}
function rule_tplarg_or_template() {
    (function() {

      // Refuse to recurse beyond `maxDepth` levels. Default in the PHP parser
      // is $wgMaxTemplateDepth = 40; This is to prevent crashing from
      // buggy wikitext with lots of unclosed template calls, as in
      // eswiki/Usuario:C%C3%A1rdenas/PRUEBAS?oldid=651094
      if (stops.onCount('templatedepth') === undefined ||
          stops.onCount('templatedepth') < env.conf.parsoid.maxDepth) {
        return true;
      } else {
        return false;
      }

    })();
    var t = null;
    (function() {
 return t;
    })();
}
function rule_tplarg_or_template_guarded() {
    (function() {
 return stops.inc('templatedepth');
    })();
    var r = null;
    var a = null;
    (function() {
 return a;
    })();
    var b = null;
    (function() {
 return [a].concat(b);
    })();
    (function() {
 return [a].concat(b);
    })();
    (function() {
 return a;
    })();
    (function() {

      stops.dec('templatedepth');
      return r;

    })();
    (function() {
 return stops.dec('templatedepth');
    })();
}
function rule_tplarg_or_template_or_bust() {
    var tplarg_or_template_or_bust = null;
    var r = null;
    (function() {
 return tu.flattenIfArray(r);
    })();
}
function rule_template() {
    var stopLen = null;
    (function() {
 return stops.push('preproc', /* {{ */'}}');
    })();
    var t = null;
    (function() {
 return stops.popTo('preproc', stopLen);
    })();
    (function() {
 stops.popTo('preproc', stopLen); return t;
    })();
}
function rule_broken_template() {
    (function() {
 return stops.push('preproc', 'broken');
    })();
    var t = null;
    (function() {
 return t;
    })();
}
function rule_template_preproc() {
    var target = null;
    var params = null;
    var r = null;
    var p0 = null;
    (function() {
 return endOffset();
    })();
    var v = null;
    var p = null;
    (function() {
 return endOffset();
    })();
    (function() {
 return new KV('', tu.flattenIfArray(v), [p0, p0, p0, p]);
    })();
    (function() {
 return r;
    })();
    (function() {

      // Insert target as first positional attribute, so that it can be
      // generically expanded. The TemplateHandler then needs to shift it out
      // again.
      params.unshift(new KV(tu.flattenIfArray(target.tokens), '', target.srcOffsets));
      var obj = new SelfclosingTagTk('template', params, { tsr: tsrOffsets(), src: text() });
      return obj;

    })();
}
function rule_tplarg() {
    var stopLen = null;
    (function() {
 return stops.push('preproc', /* {{ */'}}');
    })();
    var t = null;
    (function() {
 return stops.popTo('preproc', stopLen);
    })();
    (function() {
 stops.popTo('preproc', stopLen); return t;
    })();
}
function rule_tplarg_preproc() {
    var p = null;
    (function() {
 return endOffset();
    })();
    var target = null;
    var params = null;
    var r = null;
    var p0 = null;
    (function() {
 return endOffset();
    })();
    var v = null;
    var p1 = null;
    (function() {
 return endOffset();
    })();
    (function() {
 return { tokens: v, srcOffsets: [p0, p1] };
    })();
    (function() {
 return r;
    })();
    (function() {

      params = params.map(function(o) {
        var s = o.srcOffsets;
        return new KV('', tu.flattenIfArray(o.tokens), [s[0], s[0], s[0], s[1]]);
      });
      if (target === null) { target = { tokens: '', srcOffsets: [p, p, p, p] }; }
      // Insert target as first positional attribute, so that it can be
      // generically expanded. The TemplateHandler then needs to shift it out
      // again.
      params.unshift(new KV(tu.flattenIfArray(target.tokens), '', target.srcOffsets));
      var obj = new SelfclosingTagTk('templatearg', params, { tsr: tsrOffsets(), src: text() });
      return obj;

    })();
}
function rule_template_param() {
    var name = null;
    var val = null;
    var kEndPos = null;
    (function() {
 return endOffset();
    })();
    var vStartPos = null;
    (function() {
 return endOffset();
    })();
    var tpv = null;
    (function() {

            return { kEndPos: kEndPos, vStartPos: vStartPos, value: (tpv && tpv.tokens) || [] };

    })();
    (function() {

      if (val !== null) {
          if (val.value !== null) {
            return new KV(name, tu.flattenIfArray(val.value), [startOffset(), val.kEndPos, val.vStartPos, endOffset()]);
          } else {
            return new KV(tu.flattenIfArray(name), '', [startOffset(), val.kEndPos, val.vStartPos, endOffset()]);
          }
      } else {
        return new KV('', tu.flattenIfArray(name), [startOffset(), startOffset(), startOffset(), endOffset()]);
      }

    })();
    (function() {

    return new KV('', '', [startOffset(), startOffset(), startOffset(), endOffset()]);

    })();
}
function rule_template_param_name() {
    (function() {
 return stops.push('equal', true);
    })();
    var tpt = null;
    (function() {
 return '';
    })();
    (function() {

        stops.pop('equal');
        return tpt;

    })();
    (function() {
 return stops.pop('equal');
    })();
}
function rule_template_param_value() {
    (function() {
 return stops.push('equal', false);
    })();
    var tpt = null;
    (function() {

        stops.pop('equal');
        return { tokens: tpt, srcOffsets: tsrOffsets() };

    })();
    (function() {
 return stops.pop('equal');
    })();
}
function rule_template_param_text() {
    (function() {
 // re-enable tables within template parameters
        stops.push('table', false);
        stops.push('extlink', false);
        stops.push('templateArg', true);
        stops.push('tableCellArg', false);
        return stops.inc('template');

    })();
    var il = null;
    (function() {

        stops.pop('table');
        stops.pop('extlink');
        stops.pop('templateArg');
        stops.pop('tableCellArg');
        stops.dec('template');
        // il is guaranteed to be an array -- so, tu.flattenIfArray will
        // always return an array
        var r = tu.flattenIfArray(il);
        if (r.length === 1 && r[0].constructor === String) {
            r = r[0];
        }
        return r;

    })();
    (function() {
 stops.pop('table');
        stops.pop('extlink');
        stops.pop('templateArg');
        stops.pop('tableCellArg');
        return stops.dec('template');

    })();
}
function rule_lang_variant_or_tpl() {
    var a = null;
    (function() {
 return a;
    })();
    var b = null;
    (function() {
 return [a].concat(b);
    })();
    (function() {
 return [a].concat(b);
    })();
    (function() {
 return a;
    })();
}
function rule_broken_lang_variant() {
    (function() {
 return stops.push('preproc', 'broken');
    })();
    var r = null;
    (function() {
 return r;
    })();
}
function rule_lang_variant() {
    var stopLen = null;
    (function() {
 return stops.push('preproc', /* -{ */ '}-');
    })();
    var lv = null;
    (function() {
 return stops.popTo('preproc', stopLen);
    })();
    (function() {
 stops.popTo('preproc', stopLen); return lv;
    })();
}
function rule_lang_variant_preproc() {
    var lv0 = null;
    (function() {
 return startOffset();
    })();
    var f = null;
    (function() {
 return env.langConverterEnabled();
    })();
    var ff = null;
    (function() {

         // Avoid mutating cached expression results
         ff = Util.clone(ff, true);
         // if flags contains 'R', then don't treat ; or : specially inside.
         if (ff.flags) {
           ff.raw = ff.flags.has('R') || ff.flags.has('N');
         } else if (ff.variants) {
           ff.raw = true;
         }
         return ff;

    })();
    (function() {
 return !env.langConverterEnabled();
    })();
    (function() {

         // if language converter not enabled, don't try to parse inside.
         return { raw: true };

    })();
    var ts = null;
    (function() {
 return f.raw;
    })();
    var lv = null;
    (function() {
 return [{ text: lv }];
    })();
    (function() {
 return !f.raw;
    })();
    (function() {
 return lv;
    })();
    var lv1 = null;
    (function() {
 return endOffset();
    })();
    (function() {


      if (!env.langConverterEnabled()) {
        return [ "-{", ts[0].text.tokens, "}-" ];
      }
      var lvsrc = input.substring(lv0, lv1);
      var attribs = [];

      // Do a deep clone since we may be destructively modifying
      // (the `t[fld] = name;` below) the result of a cached expression
      ts = Util.clone(ts, true);

      ts.forEach(function(t) {
        // move token strings into KV attributes so that they are
        // properly expanded by early stages of the token pipeline
        ['text','from','to'].forEach(function(fld) {
          if (t[fld] === undefined) { return; }
          var name = 'mw:lv' + attribs.length;
          // Note that AttributeExpander will expect the tokens array to be
          // flattened.  We do that in lang_variant_text / lang_variant_nowiki
          attribs.push(new KV(name, t[fld].tokens, t[fld].srcOffsets));
          t[fld] = name;
        });
      });
      return [
        new SelfclosingTagTk(
          'language-variant',
           attribs,
           {
             tsr: [lv0, lv1],
             src: lvsrc,
             flags: f.flags && Array.from(f.flags).sort(),
             variants: f.variants && Array.from(f.variants).sort(),
             original: f.original,
             flagSp: f.sp,
             texts: ts,
           }),
      ];

    })();
}
function rule_opt_lang_variant_flags() {
    var f = null;
    var ff = null;
    (function() {
 return ff;
    })();
    (function() {

    // Collect & separate flags and variants into a set and ordered list
    var flags = new Set();
    var variants = new Set();
    var flagList = [];
    var flagSpace = [];
    var variantList = [];
    var variantSpace = [];
    var useVariants = false;
    var internalSp = []; // internal whitespace, for round-tripping
    if (f !== null) {
      // lang_variant_flags returns arrays in reverse order.
      f.flags.reverse();
      f.sp.reverse();
      var spPtr = 0;
      f.flags.forEach(function(item) {
        if (item.flag) {
          flagSpace.push(f.sp[spPtr++]);
          flags.add(item.flag);
          flagList.push(item.flag);
          flagSpace.push(f.sp[spPtr++]);
        }
        if (item.variant) {
          variantSpace.push(f.sp[spPtr++]);
          variants.add(item.variant);
          variantList.push(item.variant);
          variantSpace.push(f.sp[spPtr++]);
        }
      });
      if (spPtr < f.sp.length) {
        // handle space after a trailing semicolon
        flagSpace.push(f.sp[spPtr]);
        variantSpace.push(f.sp[spPtr]);
      }
    }
    // Parse flags (this logic is from core/languages/ConverterRule.php
    // in the parseFlags() function)
    if (flags.size === 0 && variants.size === 0) {
      flags.add('$S');
    } else if (flags.has('R')) {
      flags = new Set(['R']); // remove other flags
    } else if (flags.has('N')) {
      flags = new Set(['N']); // remove other flags
    } else if (flags.has('-')) {
      flags = new Set(['-']); // remove other flags
    } else if (flags.has('T') && flags.size === 1) {
      flags.add('H');
    } else if (flags.has('H')) {
      // Replace A flag, and remove other flags except T and D
      var nf = new Set(['$+', 'H']);
      if (flags.has('T')) { nf.add('T'); }
      if (flags.has('D')) { nf.add('D'); }
      flags = nf;
    } else if (variants.size > 0) {
      useVariants = true;
    } else {
      if (flags.has('A')) {
        flags.add('$+');
        flags.add('$S');
      }
      if (flags.has('D')) {
        flags.delete('$S');
      }
    }
    if (useVariants) {
      return { variants: variants, original: variantList, sp: variantSpace };
    } else {
      return { flags: flags, original: flagList, sp: flagSpace };
    }

    })();
}
function rule_lang_variant_flags() {
    var sp1 = null;
    var f = null;
    var sp2 = null;
    var more = null;
    (function() {

    var r = more && more[1] ? more[1] : { sp: [], flags: [] };
    // Note that sp and flags are in reverse order, since we're using
    // right recursion and want to push instead of unshift.
    r.sp.push(sp2.join(''));
    r.sp.push(sp1.join(''));
    r.flags.push(f);
    return r;

    })();
    var sp = null;
    (function() {

    return { sp: [ sp.join('') ], flags: [] };

    })();
}
function rule_lang_variant_flag() {
    var f = null;
    (function() {
 return { flag: f };
    })();
    var v = null;
    (function() {
 return { variant: v };
    })();
    var b = null;
    (function() {
 return { bogus: b.join('') }; /* bad flag */
    })();
}
function rule_lang_variant_name() {
    var h = null;
    var t = null;
    (function() {
 return h + t.join('');
    })();
}
function rule_lang_variant_option_list() {
    var o = null;
    var rest = null;
    var oo = null;
    (function() {
 return oo;
    })();
    var tr = null;
    (function() {

      var r = [ o ].concat(rest);
      if (tr) { r.push({ semi: true, sp: tr[1].join('') }); }
      return r;

    })();
    var lvtext = null;
    (function() {
 return [{ text: lvtext }];
    })();
}
function rule_lang_variant_option() {
    var sp1 = null;
    var lang = null;
    var sp2 = null;
    var sp3 = null;
    var lvtext = null;
    (function() {

      return {
        twoway: true,
        lang: lang,
        text: lvtext,
        sp: [sp1.join(''), sp2.join(''), sp3.join('')]
      };

    })();
    var from = null;
    var sp4 = null;
    var to = null;
    (function() {

      return {
        oneway: true,
        from: from,
        lang: lang,
        to: to,
        sp: [sp1.join(''), sp2.join(''), sp3.join(''), sp4.join('')]
      };

    })();
}
function rule_lang_variant_nowiki() {
    var start = null;
    (function() {
return startOffset();
    })();
    var n = null;
    var end = null;
    (function() {
 return endOffset();
    })();
    (function() {

  return { tokens: [ n ], srcOffsets: [start, end] };

    })();
}
function rule_lang_variant_text() {
    var start = null;
    (function() {
return startOffset();
    })();
    var tokens = null;
    var end = null;
    (function() {
return endOffset();
    })();
    (function() {
 return { tokens: tu.flattenStringlist(tokens || []), srcOffsets: [start, end] };
    })();
}
function rule_lang_variant_text_no_semi() {
    (function() {
 return stops.push('semicolon', true);
    })();
    var lvtext = null;
    (function() {
 stops.pop('semicolon'); return lvtext;
    })();
    (function() {
 return stops.pop('semicolon');
    })();
}
function rule_lang_variant_text_no_semi_or_arrow() {
    (function() {
 return stops.push('arrow', true);
    })();
    var lvtext = null;
    (function() {
 stops.pop('arrow'); return lvtext;
    })();
    (function() {
 return stops.pop('arrow');
    })();
}
function rule_wikilink_content() {
    var startPos = null;
    (function() {
 return endOffset();
    })();
    var lt = null;
    (function() {

        var maybeContent = new KV('mw:maybeContent', lt, [startPos, endOffset()]);
        maybeContent.vsrc = input.substring(startPos, endOffset());
        return maybeContent;

    })();
}
function rule_wikilink() {
    var stopLen = null;
    (function() {
 return stops.push('preproc', ']]');
    })();
    var w = null;
    (function() {
 return stops.popTo('preproc', stopLen);
    })();
    (function() {
 stops.popTo('preproc', stopLen); return w;
    })();
}
function rule_broken_wikilink() {
    (function() {
 return stops.push('preproc', 'broken');
    })();
    var a = null;
    (function() {
 return a;
    })();
}
function rule_wikilink_preproc() {
    var target = null;
    var tpos = null;
    (function() {
 return endOffset();
    })();
    var lcs = null;
    (function() {

      var pipeTrick = (lcs.length === 1 && lcs[0].v === null);
      var textTokens = [];
      if (target === null || pipeTrick) {
        textTokens.push("[[");
        if (target) {
          textTokens.push(target);
        }
        lcs.forEach(function(a) {
          // a is a mw:maybeContent attribute
          textTokens.push("|");
          if (a.v !== null) { textTokens.push(a.v); }
        });
        textTokens.push("]]");
        return textTokens;
      }
      var obj = new SelfclosingTagTk('wikilink');
      var hrefKV = new KV('href', target);
      hrefKV.vsrc = input.substring(startOffset() + 2, tpos);
      // XXX: Point to object with path, revision and input information
      // obj.source = input;
      obj.attribs.push(hrefKV);
      obj.attribs = obj.attribs.concat(lcs);
      obj.dataAttribs = {
          tsr: tsrOffsets(),
          src: text(),
      };
      return [obj];

    })();
}
function rule_link_text() {
    (function() {

      // Suppress the flag temporarily in this rule to consume the '=' here.
      stops.push('equal', false);
      return stops.push('linkdesc', true);

    })();
    var c = null;
    var r = null;
    (function() {
 return r;
    })();
    (function() {

      stops.pop('equal');
      stops.pop('linkdesc');
      return tu.flattenStringlist(c);

    })();
    (function() {
 stops.pop('equal'); return stops.pop('linkdesc');
    })();
}
function rule_quote() {
    var quotes = null;
    (function() {

    // sequences of four or more than five quotes are assumed to start
    // with some number of plain-text apostrophes.
    var plainticks = 0;
    var result = [];
    if (quotes.length === 4) {
        plainticks = 1;
    } else if (quotes.length > 5) {
        plainticks = quotes.length - 5;
    }
    if (plainticks > 0) {
        result.push(quotes.substring(0, plainticks));
    }
    // mw-quote token Will be consumed in token transforms
    var tsr = tsrOffsets();
    tsr[0] += plainticks;
    var mwq = new SelfclosingTagTk('mw-quote', [], { tsr: tsr });
    mwq.value = quotes.substring(plainticks);
    result.push(mwq);
    return result;

    })();
}
function rule_extension_tag() {
    (function() {
 return !stops.onStack('extTag');
    })();
    var extToken = null;
    (function() {
 return (Array.isArray(extToken) ? extToken[0] : extToken).name === 'extension';
    })();
    (function() {
 return extToken;
    })();
}
function rule_nowiki() {
    var extToken = null;
    (function() {
 return extToken.getAttribute('name') === 'nowiki';
    })();
    (function() {
 return extToken;
    })();
}
function rule_nowiki_content() {
    var nowiki_content = null;
    var c = null;
    (function() {
 return tu.flattenIfArray(c);
    })();
}
function rule_nowiki_text() {
    var extToken = null;
    (function() {

    var txt = Util.getExtArgInfo(extToken).dict.body.extsrc;
    return Util.decodeWtEntities(txt);

    })();
}
function rule_tag_name_chars() {
}
function rule_tag_name() {
}
function rule_space_or_newline_or_solidus() {
    var s = null;
    (function() {
 return s;
    })();
}
function rule_xmlish_tag() {
    (function() {

      // By the time we get to `doTableStuff` in the php parser, we've already
      // safely encoded element attributes. See 55313f4e in core.
      stops.push('table', false);
      stops.push('tableCellArg', false);
      return true;

    })();
    var end = null;
    var name = null;
    var tn = null;
    (function() {

      return isXMLTag(tn, false);  // NOTE: 'extTag' stop was pushed.

    })();
    var attribs = null;
    var selfclose = null;
    (function() {

        stops.pop('table');
        stops.pop('tableCellArg');
        stops.pop('extTag');

        var lcName = name.toLowerCase();

        // Extension tags don't necessarily have the same semantics as html tags,
        // so don't treat them as void elements.
        var isVoidElt = Util.isVoidElement(lcName) && !env.conf.wiki.extConfig.tags.has(lcName);

        // Support </br>
        if (lcName === 'br' && end) {
            end = null;
        }

        var res = tu.buildXMLTag(name, lcName, attribs, end, !!selfclose || isVoidElt, tsrOffsets());

        // change up data-attribs in one scenario
        // void-elts that aren't self-closed ==> useful for accurate RT-ing
        if (!selfclose && isVoidElt) {
            res.dataAttribs.selfClose = undefined;
            res.dataAttribs.noClose = true;
        }

        return maybeExtensionTag(res);

    })();
    (function() {
 return stops.pop('extTag');
    })();
    (function() {
 stops.pop('table'); return stops.pop('tableCellArg');
    })();
}
function rule_block_tag() {
    (function() {

      // By the time we get to `doTableStuff` in the php parser, we've already
      // safely encoded element attributes. See 55313f4e in core.
      stops.push('table', false);
      stops.push('tableCellArg', false);
      return true;

    })();
    var end = null;
    var name = null;
    var tn = null;
    (function() {

      return isXMLTag(tn, true);  // NOTE: 'extTag' stop was pushed.

    })();
    var attribs = null;
    var selfclose = null;
    (function() {

      stops.pop('table');
      stops.pop('tableCellArg');
      stops.pop('extTag');
      var t = tu.buildXMLTag(name, name.toLowerCase(), attribs, end, !!selfclose, tsrOffsets());
      var met = maybeExtensionTag(t);
      return Array.isArray(met) ? met : [met];

    })();
    (function() {
 return stops.pop('extTag');
    })();
    (function() {
 stops.pop('table'); return stops.pop('tableCellArg');
    })();
}
function rule_generic_newline_attribute() {
    var namePos0 = null;
    (function() {
 return endOffset();
    })();
    var name = null;
    var namePos = null;
    (function() {
 return endOffset();
    })();
    var vd = null;
    var v = null;
    (function() {
 return v;
    })();
    (function() {

    // NB: Keep in sync w/ table_attibute
    var res;
    // Encapsulate protected attributes.
    if (typeof name === 'string') {
        name = tu.protectAttrs(name);
    }
    if (vd !== null) {
        res = new KV(name, vd.value, [namePos0, namePos, vd.srcOffsets[0], vd.srcOffsets[1]]);
        res.vsrc = input.substring(vd.srcOffsets[0], vd.srcOffsets[1]);
    } else {
        res = new KV(name, '', [namePos0, namePos, namePos, namePos]);
    }
    if (Array.isArray(name)) {
        res.ksrc = input.substring(namePos0, namePos);
    }
    return res;

    })();
}
function rule_table_attribute() {
    var s = null;
    var namePos0 = null;
    (function() {
 return endOffset();
    })();
    var name = null;
    var namePos = null;
    (function() {
 return endOffset();
    })();
    var vd = null;
    var v = null;
    (function() {
 return v;
    })();
    (function() {

    // NB: Keep in sync w/ generic_newline_attribute
    var res;
    // Encapsulate protected attributes.
    if (typeof name === 'string') {
        name = tu.protectAttrs(name);
    }
    if (vd !== null) {
        res = new KV(name, vd.value, [namePos0, namePos, vd.srcOffsets[0], vd.srcOffsets[1]]);
        res.vsrc = input.substring(vd.srcOffsets[0], vd.srcOffsets[1]);
    } else {
        res = new KV(name, '', [namePos0, namePos, namePos, namePos]);
    }
    if (Array.isArray(name)) {
        res.ksrc = input.substring(namePos0, namePos);
    }
    return res;

    })();
}
function rule_less_than() {
    (function() {
 return stops.onStack('extTag');
    })();
}
function rule_generic_attribute_name() {
    var q = null;
    var r = null;
    var t = null;
    var c = null;
    (function() {
 return c;
    })();
    (function() {
 return t;
    })();
    (function() {
 return r.length > 0 || q.length > 0;
    })();
    (function() {
 return tu.flattenString([q].concat(r));
    })();
}
function rule_broken_table_attribute_name_char() {
    var c = null;
    (function() {
 return new KV(c, '');
    })();
}
function rule_table_attribute_name() {
    var q = null;
    var r = null;
    var t = null;
    var ill = null;
    (function() {
 return ill;
    })();
    var c = null;
    (function() {
 return c;
    })();
    (function() {
 return t;
    })();
    (function() {
 return r.length > 0 || q.length > 0;
    })();
    (function() {
 return tu.flattenString([q].concat(r));
    })();
}
function rule_generic_att_value() {
    var s = null;
    var t = null;
    var q = null;
    (function() {

      return tu.getAttrVal(t, startOffset() + s.length, endOffset() - q.length);

    })();
    (function() {

      return tu.getAttrVal(t, startOffset() + s.length, endOffset() - q.length);

    })();
    (function() {

      return tu.getAttrVal(t, startOffset() + s.length, endOffset());

    })();
}
function rule_table_att_value() {
    var s = null;
    var t = null;
    var q = null;
    (function() {

      return tu.getAttrVal(t, startOffset() + s.length, endOffset() - q.length);

    })();
    (function() {

      return tu.getAttrVal(t, startOffset() + s.length, endOffset() - q.length);

    })();
    (function() {

      return tu.getAttrVal(t, startOffset() + s.length, endOffset());

    })();
}
function rule_list_item() {
}
function rule_li() {
    var bullets = null;
    var c = null;
    (function() {

    // Leave bullets as an array -- list handler expects this
    var tsr = tsrOffsets('start');
    tsr[1] += bullets.length;
    var li = new TagTk('listItem', [], { tsr: tsr });
    li.bullets = bullets;
    return [ li ].concat(c || []);

    })();
}
function rule_hacky_dl_uses() {
    var bullets = null;
    var tbl = null;
    var line = null;
    (function() {

    // Leave bullets as an array -- list handler expects this
    var tsr = tsrOffsets('start');
    tsr[1] += bullets.length;
    var li = new TagTk('listItem', [], { tsr: tsr });
    li.bullets = bullets;
    return tu.flattenIfArray([li, tbl || [], line || []]);

    })();
}
function rule_dtdd() {
    var bullets = null;
    var lc = null;
    (function() {
 return lc;
    })();
    (function() {
return stops.inc('colon');
    })();
    var c = null;
    var cpos = null;
    (function() {
 return endOffset();
    })();
    (function() {
 stops.counters.colon = 0; return true;
    })();
    var d = null;
    (function() {

        // Leave bullets as an array -- list handler expects this
        // TSR: +1 for the leading ";"
        var numBullets = bullets.length + 1;
        var tsr = tsrOffsets('start');
        tsr[1] += numBullets;
        var li1 = new TagTk('listItem', [], { tsr: tsr });
        li1.bullets = bullets.slice();
        li1.bullets.push(";");
        // TSR: -1 for the intermediate ":"
        var li2 = new TagTk('listItem', [], { tsr: [cpos - 1, cpos], stx: 'row' });
        li2.bullets = bullets.slice();
        li2.bullets.push(":");

        return [ li1 ].concat(c || [], [ li2 ], d || []);

    })();
    (function() {
 stops.counters.colon = 0; return false;
    })();
}
function rule_list_char() {
}
function rule_full_table_in_link_caption() {
    var r = null;
    (function() {
 stops.push('linkdesc', false); return stops.push('table', true);
    })();
    var tbl = null;
    (function() {

            stops.pop('linkdesc');
            stops.pop('table');
            return tbl;

    })();
    (function() {
 stops.pop('linkdesc'); return stops.pop('table');
    })();
    (function() {
 return r;
    })();
}
function rule_table_line() {
    var r = null;
    (function() {
 return stops.push('table', true);
    })();
    var tl = null;
    (function() {

            stops.pop('table');
            return tl;

    })();
    (function() {
 return stops.pop('table');
    })();
    (function() {
 return r;
    })();
}
function rule_table_content_line() {
}
function rule_table_start_tag() {
    var table_start_tag = null;
    var sc = null;
    var startPos = null;
    (function() {
 return endOffset();
    })();
    var b = null;
    var p = null;
    (function() {
 return stops.push('table', false);
    })();
    var ta = null;
    (function() {
 console.assert(false); return false;
    })();
    var tsEndPos = null;
    (function() {
 stops.pop('table'); return endOffset();
    })();
    var s2 = null;
    (function() {

        var coms = tu.popComments(ta);
        if (coms) {
          tsEndPos = coms.commentStartPos;
        }

        var da = { tsr: [startPos, tsEndPos] };
        if (p !== "|") {
            // Variation from default
            da.startTagSrc = b + p;
        }

        sc.push(new TagTk('table', ta, da));
        if (coms) {
          sc = sc.concat(coms.buf);
        }
        return sc.concat(s2);

    })();
}
function rule_table_caption_tag() {
    var p = null;
    var args = null;
    var tagEndPos = null;
    (function() {
 return endOffset();
    })();
    var c = null;
    (function() {

        return tu.buildTableTokens("caption", "|+", args, [startOffset(), tagEndPos], endOffset(), c, true);

    })();
}
function rule_table_row_tag() {
    var p = null;
    var dashes = null;
    (function() {
 return stops.push('table', false);
    })();
    var a = null;
    (function() {
 console.assert(false); return false;
    })();
    var tagEndPos = null;
    (function() {
 stops.pop('table'); return endOffset();
    })();
    (function() {

        var coms = tu.popComments(a);
        if (coms) {
          tagEndPos = coms.commentStartPos;
        }

        var da = {
          tsr: [ startOffset(), tagEndPos ],
          startTagSrc: p + dashes,
        };

        // We rely on our tree builder to close the row as needed. This is
        // needed to support building tables from fragment templates with
        // individual cells or rows.
        var trToken = new TagTk('tr', a, da);

        var res = [ trToken ];
        if (coms) {
          res = res.concat(coms.buf);
        }
        return res;

    })();
}
function rule_tds() {
    var pp = null;
    var p = null;
    (function() {
 return p;
    })();
    var tdt = null;
    (function() {

        // FIXME: Manipulating a potentially cached result (tdt) can lead to
        // subtle breakage!
        var da = tdt[0].dataAttribs;
        da.stx = "row";
        da.tsr[0] -= pp.length; // include "||"
        if (pp !== "||" || (da.startTagSrc && da.startTagSrc !== pp)) {
          // Variation from default
          da.startTagSrc = pp + (da.startTagSrc ? da.startTagSrc.substring(1) : '');
        }
        return tdt;

    })();
}
function rule_table_data_tags() {
    var p = null;
    var td = null;
    var tagEndPos = null;
    (function() {
 return endOffset();
    })();
    var tds = null;
    (function() {

        // FIXME: Manipulating a potentially cached result (td) can lead to
        // subtle breakage!
        var da = td[0].dataAttribs;
        da.tsr[0] -= p.length; // include "|"
        if (p !== "|") {
            // Variation from default
            da.startTagSrc = p;
        }
        return td.concat(tds);

    })();
}
function rule_table_data_tag() {
    var arg = null;
    var tagEndPos = null;
    (function() {
 return endOffset();
    })();
    var td = null;
    (function() {

        return tu.buildTableTokens("td", "|", arg, [startOffset(), tagEndPos], endOffset(), td);

    })();
}
function rule_table_heading_tags() {
    (function() {
 return stops.push('th', endOffset());
    })();
    var th = null;
    var ths = null;
    var pp = null;
    var tht = null;
    (function() {

            // FIXME: Manipulating a potentially cached result (tht) can lead to
            // subtle breakage!
            var da = tht[0].dataAttribs;
            da.stx = 'row';
            da.tsr[0] -= pp.length; // include "!!" or "||"

            if (pp !== "!!" || (da.startTagSrc && da.startTagSrc !== pp)) {
                // Variation from default
                da.startTagSrc = pp + (da.startTagSrc ? da.startTagSrc.substring(1) : '');
            }
            return tht;

    })();
    (function() {

        stops.pop('th');
        // FIXME: Here too!
        th[0].dataAttribs.tsr[0]--; // include "!"
        return th.concat(ths);

    })();
    (function() {
 return stops.onStack('th') !== false ? stops.pop('th') : false;
    })();
}
function rule_table_heading_tag() {
    var arg = null;
    var tagEndPos = null;
    (function() {
 return endOffset();
    })();
    var c = null;
    (function() {

      // This SyntaxStop is only true until we hit the end of the line.
      if (stops.onStack('th') !== false &&
              /\n/.test(input.substring(stops.onStack('th'), endOffset()))) {
          // There's been a newline. Remove the break and continue
          // tokenizing nested_block_in_tables.
          stops.pop('th');
      }
      return true;

    })();
    var d = null;
    (function() {
 return d;
    })();
    (function() {

        return tu.buildTableTokens("th", "!", arg, [startOffset(), tagEndPos], endOffset(), c);

    })();
}
function rule_table_end_tag() {
    var sc = null;
    var startPos = null;
    (function() {
 return endOffset();
    })();
    var p = null;
    var b = null;
    (function() {

      var tblEnd = new EndTagTk('table', [], { tsr: [startPos, endOffset()] });
      if (p !== "|") {
          // p+"<brace-char>" is triggering some bug in pegJS
          // I cannot even use that expression in the comment!
          tblEnd.dataAttribs.endTagSrc = p + b;
      }
      return sc.concat([tblEnd]);

    })();
}
function rule_row_syntax_table_args() {
    (function() {
 return stops.push('tableCellArg', true);
    })();
    var as = null;
    var s = null;
    var p = null;
    (function() {

        stops.pop('tableCellArg');
        return [as, s, p];

    })();
    (function() {
 return stops.pop('tableCellArg');
    })();
}
function rule_text_char() {
}
function rule_urltext() {
    var al = null;
    (function() {
 return al;
    })();
    var he = null;
    (function() {
 return he;
    })();
    (function() {

              var toks = TokenUtils.placeholder('\u00a0', {
                src: ' ',
                tsr: tsrOffsets('start'),
                isDisplayHack: true,
              }, { tsr: tsrOffsets('end'), isDisplayHack: true });
              var typeOf = toks[0].getAttribute('typeof');
              toks[0].setAttribute('typeof', 'mw:DisplaySpace ' + typeOf);
              return toks;

    })();
    var bs = null;
    (function() {
 return bs;
    })();
}
function rule_raw_htmlentity() {
    var m = null;
    (function() {

    return Util.decodeWtEntities(m);

    })();
}
function rule_htmlentity() {
    var cc = null;
    (function() {

    // if this is an invalid entity, don't tag it with 'mw:Entity'
    if (cc.length > 2 /* decoded entity would be 1 or 2 UTF-16 characters */) {
        return cc;
    }
    return [
        new TagTk('span', [new KV('typeof', 'mw:Entity')], { src: text(), srcContent: cc, tsr: tsrOffsets('start') }),
        cc,
        new EndTagTk('span', [], { tsr: tsrOffsets('end') }),
    ];

    })();
}
function rule_spaces() {
}
function rule_space() {
}
function rule_optionalSpaceToken() {
    var s = null;
    (function() {

      if (s.length) {
          return [s];
      } else {
          return [];
      }

    })();
}
function rule_space_or_newline() {
}
function rule_end_of_word() {
}
function rule_unispace() {
}
function rule_space_or_nbsp() {
    var he = null;
    (function() {
 return Array.isArray(he) && /^\u00A0$/.test(he[1]);
    })();
    (function() {
 return he;
    })();
}
function rule_space_or_nbsp_or_dash() {
}
function rule_optionalNewlines() {
    var spc = null;
    (function() {

        if (spc.length) {
            return [spc];
        } else {
            return [];
        }

    })();
}
function rule_comment_or_includes() {
    (function() {
 return stops.push("sol_il", true);
    })();
    var i = null;
    (function() {
 stops.pop("sol_il"); return true;
    })();
    (function() {
 return i;
    })();
    (function() {
 return stops.pop("sol_il");
    })();
}
function rule_sol() {
}
function rule_sol_prefix() {
    (function() {

      // Use the sol flag only at the start of the input
      // NOTE: Explicitly check for 'false' and not a falsy value
      return endOffset() === 0 && options.sol !== false;

    })();
    (function() {
 return [];
    })();
}
function rule_empty_line_with_comments() {
    var sp = null;
    var p = null;
    (function() {
 return endOffset();
    })();
    var c = null;
    (function() {

        return [
            sp,
            new SelfclosingTagTk("meta", [new KV('typeof', 'mw:EmptyLine')], {
                tokens: tu.flattenIfArray(c),
                tsr: [p, endOffset()],
            }),
        ];

    })();
}
function rule_comment_space() {
}
function rule_nl_comment_space() {
}
function rule_include_limits() {
    var n = null;
    (function() {
 return tu.isIncludeTag(n.toLowerCase());
    })();
    var il = null;
    (function() {

    il = Array.isArray(il) ? il[0] : il;
    var lname = il.name.toLowerCase();
    if (!tu.isIncludeTag(lname)) { return false; }
    // Preserve SOL where necessary (for onlyinclude and noinclude)
    // Note that this only works because we encounter <*include*> tags in
    // the toplevel content and we rely on the php preprocessor to expand
    // templates, so we shouldn't ever be tokenizing inInclude.
    // Last line should be empty (except for comments)
    if (lname !== "includeonly" && stops.onStack("sol_il") && il.constructor === TagTk) {
        var dp = il.dataAttribs;
        var inclContent = dp.src.substring(dp.tagWidths[0], dp.src.length - dp.tagWidths[1]);
        var last = lastItem(inclContent.split('\n'));
        if (!/^(<!--([^-]|-(?!->))*-->)*$/.test(last)) {
            return false;
        }
    }
    return true;

    })();
    (function() {
 return il;
    })();
}
function rule_sof() {
    (function() {
 return endOffset() === 0 && !options.pipelineOffset;
    })();
}
function rule_eof() {
    (function() {
 return endOffset() === input.length;
    })();
}
function rule_newline() {
}
function rule_newlineToken() {
    (function() {
 return [new NlTk(tsrOffsets())];
    })();
}
function rule_eolf() {
}
function rule_comment_space_eolf() {
}
function rule_directive() {
    var v = null;
    (function() {
 return v;
    })();
    var e = null;
    (function() {
 return e;
    })();
}
function rule_wikilink_preprocessor_text() {
    var r = null;
    var t = null;
    var wr = null;
    (function() {
 return wr;
    })();
    (function() {

      return tu.flattenStringlist(r);

    })();
}
function rule_extlink_preprocessor_text() {
    (function() {

    // Prevent breaking on pipes when we're in a link description.
    // See the test, 'Images with the "|" character in the comment'.
    return stops.push('linkdesc', false);

    })();
    var r = null;
    var s = null;
    (function() {
 return s;
    })();
    (function() {

      stops.pop('linkdesc');
      return tu.flattenString(r);

    })();
    (function() {
 return stops.pop('linkdesc');
    })();
}
function rule_attribute_preprocessor_text() {
    var r = null;
    var s = null;
    (function() {
 return s;
    })();
    (function() {

    return tu.flattenString(r);

    })();
}
function rule_attribute_preprocessor_text_single() {
    var r = null;
    var s = null;
    (function() {
 return s;
    })();
    (function() {

    return tu.flattenString(r);

    })();
}
function rule_attribute_preprocessor_text_double() {
    var r = null;
    var s = null;
    (function() {
 return s;
    })();
    (function() {

    return tu.flattenString(r);

    })();
}
function rule_table_attribute_preprocessor_text() {
    var r = null;
    var s = null;
    (function() {
 return s;
    })();
    (function() {

    return tu.flattenString(r);

    })();
}
function rule_table_attribute_preprocessor_text_single() {
    var r = null;
    var s = null;
    (function() {
 return s;
    })();
    (function() {

    return tu.flattenString(r);

    })();
}
function rule_table_attribute_preprocessor_text_double() {
    var r = null;
    var s = null;
    (function() {
 return s;
    })();
    (function() {

    return tu.flattenString(r);

    })();
}
function rule_pipe() {
}
function rule_pipe_pipe() {
}
