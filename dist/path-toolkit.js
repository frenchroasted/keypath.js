(function (global, factory) {
    typeof exports === 'object' && typeof module !== 'undefined' ? module.exports = factory() :
    typeof define === 'function' && define.amd ? define(factory) :
    (global.PathToolkit = factory());
}(this, (function () { 'use strict';

/**
 * @fileOverview PathToolkit evaluates string paths as property/index sequences within objects and arrays
 * @author Aaron Brown
 * @version 1.0.3
 */

// Parsing, tokeninzing, etc
// Some constants for convenience
var UNDEF = (function(u){return u;})();

// Static strings, assigned to aid code minification
var $WILDCARD     = '*';
var $UNDEFINED    = 'undefined';
var $STRING       = 'string';
var $PARENT       = 'parent';
var $ROOT         = 'root';
var $PLACEHOLDER  = 'placeholder';
var $CONTEXT      = 'context';
var $LITERAL      = 'literal';
var $PROPERTY     = 'property';
var $COLLECTION   = 'collection';
var $EACH         = 'each';
var $SINGLEQUOTE  = 'singlequote';
var $DOUBLEQUOTE  = 'doublequote';
var $CALL         = 'call';
var $EVALPROPERTY = 'evalProperty';
    
/**
 * Tests whether a wildcard templates matches a given string.
 * ```javascript
 * var str = 'aaabbbxxxcccddd';
 * wildCardMatch('aaabbbxxxcccddd'); // true
 * wildCardMatch('*', str); // true
 * wildCardMatch('*', ''); // true
 * wildCardMatch('a*', str); // true
 * wildCardMatch('aa*ddd', str); // true
 * wildCardMatch('*d', str); // true
 * wildCardMatch('*a', str); // false
 * wildCardMatch('a*z', str); // false
 * ```
 * @private
 * @param  {String} template Wildcard pattern
 * @param  {String} str      String to match against wildcard pattern
 * @return {Boolean}          True if pattern matches string; False if not
 */
var wildCardMatch = function(template, str){
    var pos = template.indexOf($WILDCARD),
        parts = template.split($WILDCARD, 2),
        match = true;
    if (parts[0]){
        // If no wildcard present, return simple string comparison
        if (parts[0] === template){
            return parts[0] === str;
        }
        else {
            match = match && str.substr(0, parts[0].length) === parts[0];
        }
    }
    if (parts[1]){
        match = match && str.substr(-1*parts[1].length) === parts[1];
    }
    return match;
};

/**
 * Inspect input value and determine whether it is an Object or not.
 * Values of undefined and null will return "false", otherwise
 * must be of type "object" or "function".
 * @private
 * @param  {Object}  val Thing to examine, may be of any type
 * @return {Boolean}     True if thing is of type "object" or "function"
 */
var isObject = function(val){
    if (typeof val === $UNDEFINED || val === null) { return false;}
    return ( (typeof val === 'function') || (typeof val === 'object') );
};

/**
 * Convert various values to true boolean `true` or `false`.
 * For non-string values, the native javascript idea of "true" will apply.
 * For string values, the words "true", "yes", and "on" will all return `true`.
 * All other strings return `false`. The string match is non-case-sensitive.
 * @private
 */
var truthify = function(val){
    var v;
    if (typeof val !== $STRING){
        return val && true; // Use native javascript notion of "truthy"
    }
    v = val.toUpperCase();
    if (v === 'TRUE' || v === 'YES' || v === 'ON'){
        return true;
    }
    return false;
};

/**
 * Using provided quote character as prefix and suffix, escape any instances
 * of the quote character within the string and return quote+string+quote.
 * The character defined as "singlequote" may be altered by custom options,
 * so a general-purpose function is needed to quote path segments correctly.
 * @private
 * @param  {String} q   Single-character string to use as quote character
 * @param  {String} str String to be quoted.
 * @return {String}     Original string, surrounded by the quote character, possibly modified internally if the quote character exists within the string.
 */
var quoteString = function(q, str){
    var qRegEx = new RegExp(q, 'g');
    return q + str.replace(qRegEx, '\\' + q) + q;
};

/**
 * PathToolkit base object. Includes all instance-specific data (options, cache)
 * as local variables. May be passed an options hash to pre-configure the
 * instance prior to use.
 * @constructor
 * @property {Object} options Optional. Collection of configuration settings for this instance of PathToolkit. See `setOptions` function below for detailed documentation.
 */
var PathToolkit = function(options){
    var _this = this,
        cache = {},
        opt = {},
        prefixList, separatorList, containerList, containerCloseList,
        propertySeparator,
        singlequote, doublequote,
        simplePathChars, simplePathRegEx,
        allSpecials, allSpecialsRegEx,
        escapedNonSpecialsRegEx,
        escapedQuotes,
        wildcardRegEx;

    /**
     * Several regular expressions are pre-compiled for use in path interpretation.
     * These expressions are built from the current syntax configuration, so they
     * must be re-built every time the syntax changes.
     * @private
     */
    var updateRegEx = function(){
        // Lists of special characters for use in regular expressions
        prefixList = Object.keys(opt.prefixes);
        separatorList = Object.keys(opt.separators);
        containerList = Object.keys(opt.containers);
        containerCloseList = containerList.map(function(key){ return opt.containers[key].closer; });
        
        propertySeparator = '';
        Object.keys(opt.separators).forEach(function(sep){ if (opt.separators[sep].exec === $PROPERTY){ propertySeparator = sep; } });
        singlequote = '';
        doublequote = '';
        Object.keys(opt.containers).forEach(function(sep){
            if (opt.containers[sep].exec === $SINGLEQUOTE){ singlequote = sep;}
            if (opt.containers[sep].exec === $DOUBLEQUOTE){ doublequote = sep;}
        });

        // Find all special characters except property separator (. by default)
        simplePathChars = '[\\\\' + [$WILDCARD].concat(prefixList).concat(separatorList).concat(containerList).join('\\').replace('\\'+propertySeparator, '') + ']';
        simplePathRegEx = new RegExp(simplePathChars);
        
        // Find all special characters, including backslash
        allSpecials = '[\\\\\\' + [$WILDCARD].concat(prefixList).concat(separatorList).concat(containerList).concat(containerCloseList).join('\\') + ']';
        allSpecialsRegEx = new RegExp(allSpecials, 'g');
        
        // Find all escaped special characters
        // escapedSpecialsRegEx = new RegExp('\\'+allSpecials, 'g');
        // Find all escaped non-special characters, i.e. unnecessary escapes
        escapedNonSpecialsRegEx = new RegExp('\\'+allSpecials.replace(/^\[/,'[^'));
        if (singlequote || doublequote){
            escapedQuotes = new RegExp('\\['+singlequote+doublequote+']', 'g');
        }
        else {
            escapedQuotes = '';
        }
        
        // Find wildcard character
        wildcardRegEx = new RegExp('\\'+$WILDCARD);
    };

    /**
     * Sets all the default options for interpreter behavior and syntax.
     * @private
     */
    var setDefaultOptions = function(){
        opt = opt || {};
        // Default settings
        opt.useCache = true;  // cache tokenized paths for repeated use
        opt.simple = false;   // only support dot-separated paths, no other special characters
        opt.force = false;    // create intermediate properties during `set` operation

        // Default prefix special characters
        opt.prefixes = {
            '^': {
                'exec': $PARENT
            },
            '~': {
                'exec': $ROOT
            },
            '%': {
                'exec': $PLACEHOLDER
            },
            '@': {
                'exec': $CONTEXT
            },
            '!': {
                'exec': $LITERAL
            }
        };
        // Default separator special characters
        opt.separators = {
            '.': {
                'exec': $PROPERTY
                },
            ',': {
                'exec': $COLLECTION
                },
            '<': {
                'exec': $EACH
            }
        };
        // Default container special characters
        opt.containers = {
            '[': {
                'closer': ']',
                'exec': $PROPERTY
                },
            '\'': {
                'closer': '\'',
                'exec': $SINGLEQUOTE
                },
            '"': {
                'closer': '"',
                'exec': $DOUBLEQUOTE
                },
            '(': {
                'closer': ')',
                'exec': $CALL
                },
            '{': {
                'closer': '}',
                'exec': $EVALPROPERTY
                }
        };
    };

    /**
     * Test string to see if it is surrounded by single- or double-quote, using the
     * current configuration definition for those characters. If no quote container
     * is defined, this function will return false since it's not possible to quote
     * the string if there are no quotes in the syntax. Also ignores escaped quote
     * characters.
     * @param {String} str The string to test for enclosing quotes
     * @return {Boolean} true = string is enclosed in quotes; false = not quoted
     */
    var isQuoted = function(str){
        var cleanStr = str.replace(escapedQuotes, '');
        var strLen = cleanStr.length;
        if (strLen < 2){ return false; }
        return  (cleanStr[0] === cleanStr[strLen - 1]) &&
                (cleanStr[0] === singlequote || cleanStr[0] === doublequote);
    };
    
    /**
     * Remove enclosing quotes from a string. The isQuoted function will determine
     * if any change is needed. If the string is quoted, we know the first and last
     * characters are quote marks, so simply do a string slice. If the input value is
     * not quoted, return the input value unchanged. Because isQuoted is used, if
     * no quote marks are defined in the syntax, this function will return the input value.
     * @param {String} str The string to un-quote
     * @return {String} The input string without any enclosing quote marks.
     */
    var stripQuotes = function(str){
        if (isQuoted(str)){
            return str.slice(1, -1);
        }
        return str;
    };
    
    /**
     * Scan input string from left to right, one character at a time. If a special character
     * is found (one of "separators", "containers", or "prefixes"), either store the accumulated
     * word as a token or else begin watching input for end of token (finding a closing character
     * for a container or the end of a collection). If a container is found, capture the substring
     * within the container and recursively call `tokenize` on that substring. Final output will
     * be an array of tokens. A complex token (not a simple property or index) will be represented
     * as an object carrying metadata for processing.
     * @private
     * @param  {String} str Path string
     * @return {Array}     Array of tokens found in the input path
     */
    var tokenize = function (str){
        var path = '',
            simplePath = true, // path is assumed "simple" until proven otherwise
            tokens = [],
            recur = [],
            mods = {},
            pathLength = 0,
            word = '',
            hasWildcard = false,
            doEach = false, // must remember the "each" operator into the following token
            subpath = '',
            i = 0,
            opener = '',
            closer = '',
            separator = '',
            collection = [],
            depth = 0,
            escaped = 0;
console.log('tokenize:', str);

        if (opt.useCache && cache[str] !== UNDEF){ return cache[str]; }

        // Strip out any unnecessary escaping to simplify processing below
        path = str.replace(escapedNonSpecialsRegEx, '$&'.substr(1));
        pathLength = path.length;

        if (typeof str === $STRING && !simplePathRegEx.test(str)){
            tokens = path.split(propertySeparator);
            opt.useCache && (cache[str] = {t: tokens, simple: simplePath});
            return {t: tokens, simple: simplePath};
        }

        for (i = 0; i < pathLength; i++){
            // Skip escape character (`\`) and set "escaped" to the index value
            // of the character to be treated as a literal
            if (!escaped && path[i] === '\\'){
                // Next character is the escaped character
                escaped = i+1;
                i++;
            }
            // If a wildcard character is found, mark this token as having a wildcard
            if (path[i] === $WILDCARD) {
                hasWildcard = true;
            }
            // If we have already processed a container opener, treat this subpath specially
            if (depth > 0){
                // Is this character another opener from the same container? If so, add to
                // the depth level so we can match the closers correctly. (Except for quotes
                // which cannot be nested)
                // Is this character the closer? If so, back out one level of depth.
                // Be careful: quote container uses same character for opener and closer.
                !escaped && path[i] === opener && opener !== closer.closer && depth++;
                !escaped && path[i] === closer.closer && depth--;

                // While still inside the container, just add to the subpath
                if (depth > 0){
                    subpath += path[i];
                }
                // When we close off the container, time to process the subpath and add results to our tokens
                else {
                    // Handle subpath "[bar]" in foo.[bar],[baz] - we must process subpath and create a new collection
                    if (i+1 < pathLength && opt.separators[path[i+1]] && opt.separators[path[i+1]].exec === $COLLECTION){
                        if (subpath.length && closer.exec === $PROPERTY){
                            recur = stripQuotes(subpath);
                        }
                        else if (closer.exec === $SINGLEQUOTE || closer.exec === $DOUBLEQUOTE){
console.log('3quote has mods:', mods.has, mods);
                            recur = subpath;
                        }
                        else {
                            recur = tokenize(subpath);
                            if (recur === UNDEF){ return undefined; }
                            recur.exec = closer.exec;
                            recur.doEach = doEach;
                        }
                        // collection.push(closer.exec === $PROPERTY ? recur.t[0] : recur);
                        collection.push(recur);
                    }
                    // Handle subpath "[baz]" in foo.[bar],[baz] - we must process subpath and add to collection
                    else if (collection[0]){
                        if (subpath.length && closer.exec === $PROPERTY){
                            recur = stripQuotes(subpath);
                        }
                        else if (closer.exec === $SINGLEQUOTE || closer.exec === $DOUBLEQUOTE){
console.log('2quote has mods:', mods.has, mods);
                            recur = subpath;
                        }
                        else {
                            recur = tokenize(subpath);
                            if (recur === UNDEF){ return undefined; }
                            recur.exec = closer.exec;
                            recur.doEach = doEach;
                        }
                        collection.push(recur);
                        tokens.push({'tt':collection, 'doEach':doEach});
                        collection = [];
                        simplePath &= false;
                    }
                    // Simple property container is equivalent to dot-separated token. Just add this token to tokens.
                    else if (closer.exec === $PROPERTY){
                        recur = {t:[stripQuotes(subpath)]};
                        if (doEach){
                            tokens.push({'w':recur.t[0], 'mods':{}, 'doEach':true});
                            simplePath &= false;
                            doEach = false; // reset
                        }
                        else {
                            tokens.push(recur.t[0]);
                            simplePath &= true;
                        }
                    }
                    // Quoted subpath is all taken literally without token evaluation. Just add subpath to tokens as-is.
                    else if (closer.exec === $SINGLEQUOTE || closer.exec === $DOUBLEQUOTE){
                        if (mods.has){
                            word = {'w': subpath, 'mods': mods, 'doEach': doEach};
console.log('quote has mods:', mods.has, mods);
                            tokens.push(word);
                            mods = {};
                            simplePath &= false;
                        }
                        else {
                            tokens.push(subpath);
                            simplePath &= true;
                        }
                    }
                    // Otherwise, create token object to hold tokenized subpath, add to tokens.
                    else {
                        if (subpath === ''){
                            recur = {t:[],simple:true};
                        }
                        else {
                            recur = tokenize(subpath);
                        }
                        if (recur === UNDEF){ return undefined; }
                        recur.exec = closer.exec;
                        recur.doEach = doEach;
                        tokens.push(recur);
                        simplePath &= false;
                    }
                    subpath = ''; // reset subpath
                }
            }
            // If a prefix character is found, store it in `mods` for later reference.
            // Must keep count due to `parent` prefix that can be used multiple times in one token.
            else if (!escaped && path[i] in opt.prefixes && opt.prefixes[path[i]].exec){
                mods.has = true;
                if (mods[opt.prefixes[path[i]].exec]) { mods[opt.prefixes[path[i]].exec]++; }
                else { mods[opt.prefixes[path[i]].exec] = 1; }
            }
            // If a separator is found, time to store the token we've been accumulating. If
            // this token had a prefix, we store the token as an object with modifier data.
            // If the separator is the collection separator, we must either create or add
            // to a collection for this token. For simple separator, we either add the token
            // to the token list or else add to the existing collection if it exists.
            else if (!escaped && opt.separators[path[i]] && opt.separators[path[i]].exec){
                separator = opt.separators[path[i]];
                if (!word && (mods.has || hasWildcard)){
                    // found a separator, after seeing prefixes, but no token word -> invalid
                    return undefined;
                }
                // This token will require special interpreter processing due to prefix or wildcard.
                if (word && (mods.has || hasWildcard || doEach)){
                    word = {'w': word, 'mods': mods, 'doEach': doEach};
                    mods = {};
                    simplePath &= false;
                }
                // word is a plain property or end of collection
                if (separator.exec === $PROPERTY || separator.exec === $EACH){
                    // we are gathering a collection, so add last word to collection and then store
                    if (collection[0] !== UNDEF){
                        word && collection.push(word);
                        tokens.push({'tt':collection, 'doEach':doEach});
                        collection = []; // reset
                        simplePath &= false;
                    }
                    // word is a plain property
                    else {
                        word && tokens.push(word);
                        simplePath &= true;
                    }
                    // If the separator is the "each" separtor, the following word will be evaluated differently.
                    // If it's not the "each" separator, then reset "doEach"
                    doEach = separator.exec === $EACH; // reset
                }
                // word is a collection
                else if (separator.exec === $COLLECTION){
                    word && collection.push(word);
                }
                word = ''; // reset
                hasWildcard = false; // reset
            }
            // Found a container opening character. A container opening is equivalent to
            // finding a separator, so "foo.bar" is equivalent to "foo[bar]", so apply similar
            // process as separator above with respect to token we have accumulated so far.
            // Except in case collections - path may have a collection of containers, so
            // in "foo[bar],[baz]", the "[bar]" marks the end of token "foo", but "[baz]" is
            // merely another entry in the collection, so we don't close off the collection token
            // yet.
            // Set depth value for further processing.
            else if (!escaped && opt.containers[path[i]] && opt.containers[path[i]].exec){
                closer = opt.containers[path[i]];
                if (word && (mods.has || hasWildcard || doEach)){
                    if (typeof word === 'string'){
                        word = {'w': word, 'mods': mods, 'doEach':doEach};
                    }
                    else {
                        word.mods = mods;
                        word.doEach = doEach;
                    }
                    mods = {};
                }
                if (collection[0] !== UNDEF){
                    // we are gathering a collection, so add last word to collection and then store
                    word && collection.push(word);
                }
                else {
                    // word is a plain property
                    word && tokens.push(word);
                    simplePath &= true;
                }
                opener = path[i];
                // 1) don't reset doEach for empty word because this is [foo]<[bar]
                // 2) don't reset doEach for opening Call because this is a,b<fn()
                if (word && opt.containers[opener].exec !== $CALL){
                    doEach = false;
                }
                word = '';
                hasWildcard = false;
                depth++;
            }
            // Otherwise, this is just another character to add to the current token
            else if (i < pathLength) {
                word += path[i];
            }

            // If current path index matches the escape index value, reset `escaped`
            if (i < pathLength && i === escaped){
                escaped = 0;
            }
        }

        // Path ended in an escape character
        if (escaped){
            return undefined;
        }

        // Add trailing word to tokens, if present
        if (typeof word === 'string' && word && (mods.has || hasWildcard || doEach)){
            word = {'w': word, 'mods': mods, 'doEach': doEach};
            mods = {};
            simplePath &= false;
        }
        else if (word && word.mods){
            word.mods = mods;
        }
        // We are gathering a collection, so add last word to collection and then store
        if (collection[0] !== UNDEF){
            word && collection.push(word);
            tokens.push({'tt':collection, 'doEach':doEach});
            simplePath &= false;
        }
        // Word is a plain property
        else {
            word && tokens.push(word);
            simplePath &= true;
        }

        // depth != 0 means mismatched containers
        if (depth !== 0){ return undefined; }

        // If path was valid, cache the result
        opt.useCache && (cache[str] = {t: tokens, simple: simplePath});

        return {t: tokens, simple: simplePath};
    };

    /**
     * It is `resolvePath`'s job to traverse an object according to the tokens
     * derived from the keypath and either return the value found there or set
     * a new value in that location.
     * The tokens are a simple array and `reoslvePath` loops through the list
     * with a simple "while" loop. A token may itself be a nested token array,
     * which is processed through recursion.
     * As each successive value is resolved within `obj`, the current value is
     * pushed onto the "valueStack", enabling backward references (upwards in `obj`)
     * through path prefixes like "<" for "parent" and "~" for "root". The loop
     * short-circuits by returning `undefined` if the path is invalid at any point,
     * except in `set` scenario with `force` enabled.
     * @private
     * @param  {Object} obj        The data object to be read/written
     * @param  {String} path       The keypath which `resolvePath` will evaluate against `obj`. May be a pre-compiled Tokens set instead of a string.
     * @param  {Any} newValue   The new value to set at the point described by `path`. Undefined if used in `get` scenario.
     * @param  {Array} args       Array of extra arguments which may be referenced by placeholders. Undefined if no extra arguments were given.
     * @param  {Array} valueStack Stack of object contexts accumulated as the path tokens are processed in `obj`
     * @return {Any}            In `get`, returns the value found in `obj` at `path`. In `set`, returns the new value that was set in `obj`. If `get` or `set` are nto successful, returns `undefined`
     */
    var resolvePath = function (obj, path, newValue, args, valueStack){
        var change = newValue !== UNDEF, // are we setting a new value?
            tk = [],
            tkLength = 0,
            tkLastIdx = 0,
            valueStackLength = 1,
            i = 0, j = 0,
            prev = obj,
            curr = '',
            currLength = 0,
            eachLength = 0,
            wordCopy = '',
            contextProp,
            idx = 0,
            context = obj,
            ret,
            newValueHere = false,
            placeInt = 0,
            prop = '',
            callArgs;

        // For String path, either fetch tokens from cache or from `tokenize`.
        if (typeof path === $STRING){
            if (opt.useCache && cache[path]) { tk = cache[path].t; }
            else {
                tk = tokenize(path);
                if (tk === UNDEF){ return undefined; }
                tk = tk.t;
            }
        }
        // For a non-string, assume a pre-compiled token array
        else {
            tk = path.t ? path.t : [path];
        }

        tkLength = tk.length;
        if (tkLength === 0) { return undefined; }
        tkLastIdx = tkLength - 1;

        // valueStack will be an array if we are within a recursive call to `resolvePath`
        if (valueStack){
            valueStackLength = valueStack.length;
        }
        // On original entry to `resolvePath`, initialize valueStack with the base object.
        // valueStackLength was already initialized to 1.
        else {
            valueStack = [obj];
        }

        // Converted Array.reduce into while loop, still using "prev", "curr", "idx"
        // as loop values
        while (prev !== UNDEF && idx < tkLength){
            curr = tk[idx];

            // If we are setting a new value and this token is the last token, this
            // is the point where the new value must be set.
            newValueHere = (change && (idx === tkLastIdx));

            // Handle most common simple path scenario first
            if (typeof curr === $STRING){
                // If we are setting...
                if (change){
                    // If this is the final token where the new value goes, set it
                    if (newValueHere){
                        context[curr] = newValue;
                        if (context[curr] !== newValue){ return undefined; } // new value failed to set
                    }
                    // For earlier tokens, create object properties if "force" is enabled
                    else if (opt.force && typeof context[curr] === 'undefined') {
                        context[curr] = {};
                    }
                }
                // Return value is assigned as value of this object property
                ret = context[curr];

                // This basic structure is repeated in other scenarios below, so the logic
                // pattern is only documented here for brevity.
            }
            else {
                if (curr === UNDEF){
                    ret = undefined;
                }
                else if (curr.tt){
                    // Call resolvePath again with base value as evaluated value so far and
                    // each element of array as the path. Concat all the results together.
                    ret = [];
                    if (curr.doEach){
                        if (!Array.isArray(context)){
                            return undefined;
                        }
                        j = 0;
                        eachLength = context.length;
                        
                        // Path like Array->Each->Array requires a nested for loop
                        // to process the two array layers.
                        while(j < eachLength){
                            i = 0;
                            ret.push([]);
                            currLength = curr.tt.length;
                            while(i < currLength){
                                curr.tt[i].doEach = false; // This is a hack, don't know how else to disable "doEach" for collection members
                                if (newValueHere){
                                    contextProp = resolvePath(context[j], curr.tt[i], newValue, args, valueStack);
                                }
                                else if (typeof curr.tt[i] === 'string'){
                                    contextProp = context[j][curr.tt[i]];
                                }
                                else {
                                    contextProp = resolvePath(context[j], curr.tt[i], undefined, args, valueStack);
                                }
                                if (contextProp === UNDEF) { return undefined; }
        
                                if (newValueHere){
                                    if (curr.tt[i].t && curr.tt[i].exec === $EVALPROPERTY){
                                        context[j][contextProp] = newValue;
                                    } else {
                                        ret[j].push(contextProp);
                                    }
                                }
                                else {
                                    if (curr.tt[i].t && curr.tt[i].exec === $EVALPROPERTY){
                                        ret[j].push(context[j][contextProp]);
                                    } else {
                                        ret[j].push(contextProp);
                                    }
                                }
                                i++;
                            }
                            j++;
                        }
                    }
                    else {
                        i = 0;
                        currLength = curr.tt.length;
                        while(i < currLength){
                            if (newValueHere){
                                contextProp = resolvePath(context, curr.tt[i], newValue, args, valueStack);
                            }
                            else if (typeof curr.tt[i] === 'string'){
                                contextProp = context[curr.tt[i]];
                            }
                            else {
                                contextProp = resolvePath(context, curr.tt[i], undefined, args, valueStack);
                            }
                            if (contextProp === UNDEF) { return undefined; }
    
                            if (newValueHere){
                                if (curr.tt[i].t && curr.tt[i].exec === $EVALPROPERTY){
                                    context[contextProp] = newValue;
                                } else {
                                    ret.push(contextProp);
                                }
                            }
                            else {
                                if (curr.tt[i].t && curr.tt[i].exec === $EVALPROPERTY){
                                    ret.push(context[contextProp]);
                                } else {
                                    ret.push(contextProp);
                                }
                            }
                            i++;
                        }
                    }
                }
                else if (curr.w){
                    // this word token has modifiers
                    wordCopy = curr.w;
                    if (curr.mods.has){
                        if (curr.mods.parent){
                            // modify current context, shift upwards in base object one level
                            context = valueStack[valueStackLength - 1 - curr.mods.parent];
                            if (context === UNDEF) { return undefined; }
                        }
                        if (curr.mods.root){
                            // Reset context and valueStack, start over at root in this context
                            context = valueStack[0];
                            valueStack = [context];
                            valueStackLength = 1;
                        }
                        if (curr.mods.placeholder){
                            placeInt = wordCopy - 1;
                            if (args[placeInt] === UNDEF){ return undefined; }
                            // Force args[placeInt] to String, won't attempt to process
                            // arg of type function, array, or plain object
                            wordCopy = args[placeInt].toString();
                        }
                        if (curr.mods.literal){
                            // anything to do here?
                        }
                    }

                    // doEach option means to take all values in context (must be an array), apply
                    // "curr" to each one, and return the new array. Operates like Array.map.
                    if (curr.doEach){
                        if (!Array.isArray(context)){
                            return undefined;
                        }
                        ret = [];
                        i = 0;
                        eachLength = context.length;
                        while(i < eachLength){
                            // "context" modifier ("@" by default) replaces current context with a value from
                            // the arguments.
                            if (curr.mods.context){
                                placeInt = wordCopy - 1;
                                if (args[placeInt] === UNDEF){ return undefined; }
                                // Force args[placeInt] to String, won't atwordCopyt to process
                                // arg of type function, array, or plain object
                                ret.push(args[placeInt]);
                            }
                            // "literal" modifier indicates word should be taken as-is, not as
                            // a property of the current context.
                            else if (curr.mods.literal){
console.log('wordCopy:', wordCopy);
                                ret.push(wordCopy);
                            }
                            else {
                                // Repeat basic string property processing with word and modified context
                                if (context[i][wordCopy] !== UNDEF) {
                                    if (newValueHere){ context[i][wordCopy] = newValue; }
                                    ret.push(context[i][wordCopy]);
                                }
                                else if (typeof context[i] === 'function'){
                                    ret.push(wordCopy);
                                }
                                // Plain property tokens are listed as special word tokens whenever
                                // a wildcard is found within the property string. A wildcard in a
                                // property causes an array of matching properties to be returned,
                                // so loop through all properties and evaluate token for every
                                // property where `wildCardMatch` returns true.
                                else if (wildcardRegEx.test(wordCopy)){
                                    ret.push([]);
                                    for (prop in context[i]){
                                        if (wildCardMatch(wordCopy, prop)){
                                            if (newValueHere){ context[i][prop] = newValue; }
                                            ret[i].push(context[i][prop]);
                                        }
                                    }
                                }
                                else { return undefined; }
                            }
                            i++;
                        }
                    }
                    else {
                        // "context" modifier ("@" by default) replaces current context with a value from
                        // the arguments.
                        if (curr.mods.context){
                            placeInt = wordCopy - 1;
                            if (args[placeInt] === UNDEF){ return undefined; }
                            // Force args[placeInt] to String, won't atwordCopyt to process
                            // arg of type function, array, or plain object
                            ret = args[placeInt];
                        }
                        // "literal" modifier indicates word should be taken as-is, not as
                        // a property of the current context.
                        else if (curr.mods.literal){
console.log('wordCopy:', wordCopy);
                            ret.push(wordCopy);
                        }
                        else {
                            // Repeat basic string property processing with word and modified context
                            if (context[wordCopy] !== UNDEF) {
                                if (newValueHere){ context[wordCopy] = newValue; }
                                ret = context[wordCopy];
                            }
                            else if (typeof context === 'function'){
                                
                                ret = wordCopy;
                            }
                            // Plain property tokens are listed as special word tokens whenever
                            // a wildcard is found within the property string. A wildcard in a
                            // property causes an array of matching properties to be returned,
                            // so loop through all properties and evaluate token for every
                            // property where `wildCardMatch` returns true.
                            else if (wildcardRegEx.test(wordCopy)){
                                ret = [];
                                for (prop in context){
                                    if (wildCardMatch(wordCopy, prop)){
                                        if (newValueHere){ context[prop] = newValue; }
                                        ret.push(context[prop]);
                                    }
                                }
                            }
                            else { return undefined; }
                        }
                    }
                }
                // Eval Property tokens operate on a temporary context created by
                // recursively calling `resolvePath` with a copy of the valueStack.
                else if (curr.exec === $EVALPROPERTY){
                    if (curr.doEach){
                        if (!Array.isArray(context)){
                            return undefined;
                        }
                        ret = [];
                        i = 0;
                        eachLength = context.length;
                        while(i < eachLength){
                            if (curr.simple){
                                if (newValueHere){
                                    context[i][_this.get(context[i], {t:curr.t, simple:true})] = newValue;
                                }
                                ret.push(context[i][_this.get(context[i], {t:curr.t, simple:true})]);
                            }
                            else {
                                if (newValueHere){
                                    context[i][resolvePath(context[i], curr, UNDEF, args, valueStack)] = newValue;
                                }
                                ret.push(context[i][resolvePath(context[i], curr, UNDEF, args, valueStack)]);
                            }
                            i++;
                        }
                    }
                    else {
                        if (curr.simple){
                            if (newValueHere){
                                context[_this.get(context, {t: curr.t, simple:true})] = newValue;
                            }
                            ret = context[_this.get(context, {t:curr.t, simple:true})];
                        }
                        else {
                            if (newValueHere){
                                context[resolvePath(context, curr, UNDEF, args, valueStack)] = newValue;
                            }
                            ret = context[resolvePath(context, curr, UNDEF, args, valueStack)];
                        }
                    }
                }
                // Functions are called using `call` or `apply`, depending on the state of
                // the arguments within the ( ) container. Functions are executed with "this"
                // set to the context immediately prior to the function in the stack.
                // For example, "a.b.c.fn()" is equivalent to obj.a.b.c.fn.call(obj.a.b.c)
                else if (curr.exec === $CALL){
                    if (curr.doEach){
                        if (!Array.isArray(valueStack[valueStackLength - 2])){
                            return undefined;
                        }
                        ret = [];
                        i = 0;
                        eachLength = context.length;
                        while(i < eachLength){
                            // If function call has arguments, process those arguments as a new path
                            if (curr.t && curr.t.length){
                                callArgs = resolvePath(context, curr, UNDEF, args, valueStack);
                                if (callArgs === UNDEF){
                                    ret.push(context[i].apply(valueStack[valueStackLength - 2][i]));
                                }
                                else if (Array.isArray(callArgs)){
                                    ret.push(context[i].apply(valueStack[valueStackLength - 2][i], callArgs));
                                }
                                else {
                                    ret.push(context[i].call(valueStack[valueStackLength - 2][i], callArgs));
                                }
                            }
                            else {
                                ret.push(context[i].call(valueStack[valueStackLength - 2][i]));
                            }
                            i++;
                        }
                    }
                    else {
                        // If function call has arguments, process those arguments as a new path
                        if (curr.t && curr.t.length){
                            if (curr.simple){
                                callArgs = _this.get(context, curr);
                            }
                            else {
                                callArgs = resolvePath(context, curr, UNDEF, args, valueStack);
                            }
                            if (callArgs === UNDEF){
                                ret = context.apply(valueStack[valueStackLength - 2]);
                            }
                            else if (Array.isArray(callArgs)){
                                ret = context.apply(valueStack[valueStackLength - 2], callArgs);
                            }
                            else {
                                ret = context.call(valueStack[valueStackLength - 2], callArgs);
                            }
                        }
                        else {
                            ret = context.call(valueStack[valueStackLength - 2]);
                        }
                    }
                }
            }
            // Add the return value to the stack in case we must loop again.
            // Recursive calls pass the same valueStack array around, but we don't want to
            // push entries on the stack inside a recursion, so instead use fixed array
            // index references based on what **this** execution knows the valueStackLength
            // should be. That way, if a recursion adds new elements, and then we back out,
            // this context will remember the old stack length and will merely overwrite
            // those added entries, ignoring that they were there in the first place.
            valueStack[valueStackLength++] = ret;
            context = ret;
            prev = ret;
            idx++;
        }
        return context;
    };

    /**
     * Simplified path evaluation heavily optimized for performance when
     * processing paths with only property names or indices and separators.
     * If the path can be correctly processed with "path.split(separator)",
     * this function will do so. Any other special characters found in the
     * path will cause the path to be evaluated with the full `resolvePath`
     * function instead.
     * @private
     * @param  {Object} obj        The data object to be read/written
     * @param  {String} path       The keypath which `resolvePath` will evaluate against `obj`.
     * @param  {Any} newValue   The new value to set at the point described by `path`. Undefined if used in `get` scenario.
     * @return {Any}            In `get`, returns the value found in `obj` at `path`. In `set`, returns the new value that was set in `obj`. If `get` or `set` are nto successful, returns `undefined`
     */
    var quickResolveString = function(obj, path, newValue){
        var change = newValue !== UNDEF,
            tk = [],
            i = 0,
            tkLength = 0;

        tk = path.split(propertySeparator);
        opt.useCache && (cache[path] = {t: tk, simple: true});
        tkLength = tk.length;
        while (obj !== UNDEF && i < tkLength){
            if (tk[i] === ''){ return undefined; }
            else if (change){
                if (i === tkLength - 1){
                    obj[tk[i]] = newValue;
                }
                // For arrays, test current context against undefined to avoid parsing this segment as a number.
                // For anything else, use hasOwnProperty.
                else if (opt.force && typeof obj[tk[i]] === 'undefined') {
                    obj[tk[i]] = {};
                }
            }
            obj = obj[tk[i++]];
        }
        return obj;
    };

    /**
     * Simplified path evaluation heavily optimized for performance when
     * processing array of simple path tokens (plain property names).
     * This function is essentially the same as `quickResolveString` except
     * `quickResolveTokenArray` does nto need to execute path.split.
     * @private
     * @param  {Object} obj        The data object to be read/written
     * @param  {Array} tk       The token array which `resolvePath` will evaluate against `obj`.
     * @param  {Any} newValue   The new value to set at the point described by `path`. Undefined if used in `get` scenario.
     * @return {Any}            In `get`, returns the value found in `obj` at `path`. In `set`, returns the new value that was set in `obj`. If `get` or `set` are nto successful, returns `undefined`
     */
    var quickResolveTokenArray = function(obj, tk, newValue){
        var change = newValue !== UNDEF,
            i = 0,
            tkLength = tk.length;

        while (obj != null && i < tkLength){
            if (tk[i] === ''){ return undefined; }
            else if (change){
                if (i === tkLength - 1){
                    obj[tk[i]] = newValue;
                }
                // For arrays, test current context against undefined to avoid parsing this segment as a number.
                // For anything else, use hasOwnProperty.
                else if (opt.force && typeof obj[tk[i]] === 'undefined') {
                    obj[tk[i]] = {};
                }
            }
            obj = obj[tk[i++]];
        }
        return obj;
    };

    /**
     * Searches an object or array for a value, accumulating the keypath to the value along
     * the way. Operates in a recursive way until either all keys/indices have been
     * exhausted or a match is found. Return value "true" means "keep scanning", "false"
     * means "stop now". If a match is found, instead of returning a simple "false", a
     * callback function (savePath) is called which will decide whether or not to continue
     * the scan. This allows the function to find one instance of value or all instances,
     * based on logic in the callback.
     * @private
     * @param {Object} obj    The data object to scan
     * @param {Any} val The value we are looking for within `obj`
     * @param {Function} savePath Callback function which will store accumulated paths and indicate whether to continue
     * @param {String} path Accumulated keypath; undefined at first, populated in recursive calls
     * @return {Boolean} Indicates whether scan process should continue ("true"->yes, "false"->no)
     */
    var scanForValue = function(obj, val, savePath, path){
        var i, len, more, keys, prop;

        path = path ? path : '';

        // If we found the value we're looking for
        if (obj === val){
            return savePath(path); // Save the accumulated path, ask whether to continue
        }
        // This object is an array, so examine each index separately
        else if (Array.isArray(obj)){
            len = obj.length;
            for(i = 0; i < len; i++){
                // Call `scanForValue` recursively
                more = scanForValue(obj[i], val, savePath, path + propertySeparator + i);
                // Halt if that recursive call returned "false"
                if (!more){ return; }
            }
            return true; // keep looking
        }
        // This object is an object, so examine each local property separately
        else if (isObject(obj)) {
            keys = Object.keys(obj);
            len = keys.length;
            if (len > 1){ keys = keys.sort(); } // Force order of object keys to produce repeatable results
            for (i = 0; i < len; i++){
                if (obj.hasOwnProperty(keys[i])){
                    prop = keys[i];
                    // Property may include the separator character or some other special character,
                    // so quote this path segment and escape any separators within.
                    if (allSpecialsRegEx.test(prop)){
                        prop = quoteString(singlequote, prop);
                    }
                    more = scanForValue(obj[keys[i]], val, savePath, path + propertySeparator + prop);
                    if (!more){ return; }
                }
            }
            return true; // keep looking
        }
        // Leaf node (string, number, character, boolean, etc.), but didn't match
        return true; // keep looking
    };

    /**
     * Get tokenized representation of string keypath.
     * @public
     * @param {String} path Keypath
     * @return {Object} Object including the array of path tokens and a boolean indicating "simple". Simple token sets have no special operators or nested tokens, only a plain array of strings for fast evaluation.
     */
    _this.getTokens = function(path){
        var tokens = tokenize(path);
        if (typeof tokens === $UNDEFINED){ return undefined; }
        return tokens;
    };

    /**
     * Informs whether the string path has valid syntax. The path is NOT evaluated against a
     * data object, only the syntax is checked.
     * @public
     * @param {String} path Keypath
     * @return {Boolean} valid syntax -> "true"; not valid -> "false"
     */
    _this.isValid = function(path){
        return typeof tokenize(path) !== $UNDEFINED;
    };

    /**
     * Escapes any special characters found in the input string using backslash, preventing
     * these characters from causing unintended processing by PathToolkit. This function
     * DOES respect the current configured syntax, even if it has been altered from the default.
     * @public
     * @param {String} segment Segment of a keypath
     * @return {String} The original segment string with all PathToolkit special characters prepended with "\"
     */
    _this.escape = function(segment){
        return segment.replace(allSpecialsRegEx, '\\$&');
    };

    /**
     * Evaluates keypath in object and returns the value found there, if available. If the path
     * does not exist in the provided data object, returns `undefined`. For "simple" paths, which
     * don't include any operations beyond property separators, optimized resolvers will be used
     * which are more lightweight than the full-featured `resolvePath`.
     * @public
     * @param {Any} obj Source data object
     * @param {String} path Keypath to evaluate within "obj". Also accepts token array in place of a string path.
     * @return {Any} If the keypath exists in "obj", return the value at that location; If not, return `undefined`.
     */
    _this.get = function (obj, path){
        var i = 0,
            len = arguments.length,
            args;
        // For string paths, first see if path has already been cached and if the token set is simple. If
        // so, we can use the optimized token array resolver using the cached token set.
        // If there is no cached entry, use RegEx to look for special characters apart from the separator.
        // If none are found, we can use the optimized string resolver.
        if (typeof path === $STRING){
            if (opt.useCache && cache[path] && cache[path].simple){
                return quickResolveTokenArray(obj, cache[path].t);
            }
            else if (!simplePathRegEx.test(path)){
                return quickResolveString(obj, path);
            }
        }
        // For array paths (pre-compiled token sets), check for simplicity so we can use the optimized resolver.
        else if (Array.isArray(path.t) && path.simple){
            return quickResolveTokenArray(obj, path.t);
        }
        
        // If we made it this far, the path is complex and may include placeholders. Gather up any
        // extra arguments and call the full `resolvePath` function.
        args = [];
        if (len > 2){
            for (i = 2; i < len; i++) { args[i-2] = arguments[i]; }
        }
        return resolvePath(obj, path, undefined, args);
    };

    /**
     * Evaluates a keypath in object and sets a new value at the point described in the keypath. If
     * "force" is disabled, the full path must exist up to the final property, which may be created
     * by the set operation. If "force" is enabled, any missing intermediate properties will be created
     * in order to set the value on the final property. If `set` succeeds, returns "true", otherwise "false".
     * @public
     * @param {Any} obj Source data object
     * @param {String} path Keypath to evaluate within "obj". Also accepts token array in place of a string path.
     * @param {Any} val New value to set at the location described in "path"
     * @return {Boolean} "true" if the set operation succeeds; "false" if it does not succeed
     */
    _this.set = function(obj, path, val){
        var i = 0,
            len = arguments.length,
            args,
            ref,
            done = false;
            
        // Path resolution follows the same logic as `get` above, with one difference: `get` will
        // abort by returning the value as soon as it's found. `set` does not abort so the if-else
        // structure is slightly different to dictate when/if the final case should execute.
        if (typeof path === $STRING){
            if (opt.useCache && cache[path] && cache[path].simple){
                ref = quickResolveTokenArray(obj, cache[path].t, val);
                done |= true;
            }
            else if (!simplePathRegEx.test(path)){
                ref = quickResolveString(obj, path, val);
                done |= true;
            }
        }
        else if (Array.isArray(path.t) && path.simple){
            ref = quickResolveTokenArray(obj, path.t, val);
            done |= true;
        }
        
        // Path was (probably) a string and it contained complex path characters
        if (!done) {
            if (len > 3){
                args = [];
                for (i = 3; i < len; i++) { args[i-3] = arguments[i]; }
            }
            ref = resolvePath(obj, path, val, args);
        }
        
        // `set` can set a new value in multiple places if the final path segment is an array.
        // If any of those value assignments fail, `set` will return "false" indicating failure.
        if (Array.isArray(ref)){
            return ref.indexOf(undefined) === -1;
        }
        return ref !== UNDEF;
    };

    /**
     * Locate a value within an object or array. This is the publicly exposed interface to the
     * private `scanForValue` function defined above.
     * @public
     * @param {Any} obj Source data object
     * @param {Any} val The value to search for within "obj"
     * @param {String} oneOrMany Optional; If missing or "one", `find` will only return the first valid path. If "onOrMany" is any other string, `find` will scan the full object looking for all valid paths to all cases where "val" appears.
     * @return {Array} Array of keypaths to "val" or `undefined` if "val" is not found.
     */
    _this.find = function(obj, val, oneOrMany){
        var retVal = [];
        // savePath is the callback which will accumulate any found paths in a local array
        // variable.
        var savePath = function(path){
            retVal.push(path.substr(1));
            if(!oneOrMany || oneOrMany === 'one'){
                retVal = retVal[0];
                return false;
            }
            return true;
        };
        scanForValue(obj, val, savePath);
        return retVal[0] ? retVal : undefined;
    };

    /**
     * For a given special character group (e.g., separators) and character type (e.g., "property"),
     * replace an existing separator with a new character. This creates a new special character for
     * that purpose anwithin the character group and removes the old one. Also takes a "closer" argument
     * for cases where the special character is a container set.
     * @private
     * @param {Object} optionGroup Reference to current configuration for a certain type of special characters
     * @param {String} charType The type of special character to be replaced
     * @param {String} val New special character string
     * @param {String} closer Optional; New special character closer string, only used for "containers" group
     */
    var updateOptionChar = function(optionGroup, charType, val, closer){
        var oldVal = '';
        Object.keys(optionGroup).forEach(function(str){ if (optionGroup[str].exec === charType){ oldVal = str; } });

        delete optionGroup[oldVal];
        optionGroup[val] = {exec: charType};
        if (closer){ optionGroup[val].closer = closer; }
    };

    /**
     * Sets "simple" syntax in special character groups. This syntax only supports a separator
     * character and no other operators. A custom separator may be provided as an argument.
     * @private
     * @param {String} sep Optional; Separator string. If missing, the default separator (".") is used.
     */
    var setSimpleOptions = function(sep){
        var sepOpts = {};
        if (!(typeof sep === $STRING && sep.length === 1)){
            sep = '.';
        }
        sepOpts[sep] = {exec: $PROPERTY};
        opt.prefixes = {};
        opt.containers = {};
        opt.separators = sepOpts;
    };

    /**
     * Alter PathToolkit configuration. Takes an options hash which may include
     * multiple settings to change at once. If the path syntax is changed by
     * changing special characters, the cache is wiped. Each option group is
     * REPLACED by the new option group passed in. If an option group is not
     * included in the options hash, it is not changed.
     * @public
     * @param {Object} options Option hash. For sample input, see `setDefaultOptions` above.
     */
    _this.setOptions = function(options){
        if (options.prefixes){
            opt.prefixes = options.prefixes;
            cache = {};
        }
        if (options.separators){
            opt.separators = options.separators;
            cache = {};
        }
        if (options.containers){
            opt.containers = options.containers;
            cache = {};
        }
        if (typeof options.cache !== $UNDEFINED){
            opt.useCache = !!options.cache;
        }
        if (typeof options.simple !== $UNDEFINED){
            var tempCache = opt.useCache; // preserve these two options after "setDefaultOptions"
            var tempForce = opt.force;
            
            opt.simple = truthify(options.simple);
            if (opt.simple){
                setSimpleOptions();
            }
            else {
                setDefaultOptions();
                opt.useCache = tempCache;
                opt.force = tempForce;
            }
            cache = {};
        }
        if (typeof options.force !== $UNDEFINED){
            opt.force = truthify(options.force);
        }
        updateRegEx();
    };

    /**
     * Sets use of keypath cache to enabled or disabled, depending on input value.
     * @public
     * @param {Any} val Value which will be interpreted as a boolean using `truthify`. "true" will enable cache; "false" will disable.
     */
    _this.setCache = function(val){
        opt.useCache = truthify(val);
    };
    /**
     * Enables use of keypath cache.
     * @public
     */
    _this.setCacheOn = function(){
        opt.useCache = true;
    };
    /**
     * Disables use of keypath cache.
     * @public
     */
    _this.setCacheOff = function(){
        opt.useCache = false;
    };

    /**
     * Sets "force" option when setting values in an object, depending on input value.
     * @public
     * @param {Any} val Value which will be interpreted as a boolean using `truthify`. "true" enables "force"; "false" disables.
     */
    _this.setForce = function(val){
        opt.force = truthify(val);
    };
    /**
     * Enables "force" option when setting values in an object.
     * @public
     */
    _this.setForceOn = function(){
        opt.force = true;
    };
    /**
     * Disables "force" option when setting values in an object.
     * @public
     */
    _this.setForceOff = function(){
        opt.force = false;
    };

    /**
     * Shortcut function to alter PathToolkit syntax to a "simple" mode that only uses
     * separators and no other operators. "Simple" mode is enabled or disabled according
     * to the first argument and the separator may be customized with the second
     * argument when enabling "simple" mode.
     * @public
     * @param {Any} val Value which will be interpreted as a boolean using `truthify`. "true" enables "simple" mode; "false" disables.
     * @param {String} sep Separator string to use in place of the default "."
     */
    _this.setSimple = function(val, sep){
        var tempCache = opt.useCache; // preserve these two options after "setDefaultOptions"
        var tempForce = opt.force;
        opt.simple = truthify(val);
        if (opt.simple){
            setSimpleOptions(sep);
            updateRegEx();
        }
        else {
            setDefaultOptions();
            updateRegEx();
            opt.useCache = tempCache;
            opt.force = tempForce;
        }
        cache = {};
    };
    
    /**
     * Enables "simple" mode
     * @public
     * @param {String} sep Separator string to use in place of the default "."
     * @see setSimple
     */
    _this.setSimpleOn = function(sep){
        opt.simple = true;
        setSimpleOptions(sep);
        updateRegEx();
        cache = {};
    };
    
    /**
     * Disables "simple" mode, restores default PathToolkit syntax
     * @public
     * @see setSimple
     * @see setDefaultOptions
     */
    _this.setSimpleOff = function(){
        var tempCache = opt.useCache; // preserve these two options after "setDefaultOptions"
        var tempForce = opt.force;
        opt.simple = false;
        setDefaultOptions();
        updateRegEx();
        opt.useCache = tempCache;
        opt.force = tempForce;
        cache = {};
    };

    /**
     * Modify the property separator in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setSeparatorProperty = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.separators[val] || opt.separators[val].exec === $PROPERTY) && !(opt.prefixes[val] || opt.containers[val])){
                updateOptionChar(opt.separators, $PROPERTY, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setSeparatorProperty - value already in use');
            }
        }
        else {
            throw new Error('setSeparatorProperty - invalid value');
        }
    };

    /**
     * Modify the collection separator in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setSeparatorCollection = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.separators[val] || opt.separators[val].exec === $COLLECTION) && !(opt.prefixes[val] || opt.containers[val])){
                updateOptionChar(opt.separators, $COLLECTION, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setSeparatorCollection - value already in use');
            }
        }
        else {
            throw new Error('setSeparatorCollection - invalid value');
        }
    };

    /**
     * Modify the parent prefix in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setPrefixParent = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.prefixes[val] || opt.prefixes[val].exec === $PARENT) && !(opt.separators[val] || opt.containers[val])){
                updateOptionChar(opt.prefixes, $PARENT, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setPrefixParent - value already in use');
            }
        }
        else {
            throw new Error('setPrefixParent - invalid value');
        }
    };

    /**
     * Modify the root prefix in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setPrefixRoot = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.prefixes[val] || opt.prefixes[val].exec === $ROOT) && !(opt.separators[val] || opt.containers[val])){
                updateOptionChar(opt.prefixes, $ROOT, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setPrefixRoot - value already in use');
            }
        }
        else {
            throw new Error('setPrefixRoot - invalid value');
        }
    };

    /**
     * Modify the placeholder prefix in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setPrefixPlaceholder = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.prefixes[val] || opt.prefixes[val].exec === $PLACEHOLDER) && !(opt.separators[val] || opt.containers[val])){
                updateOptionChar(opt.prefixes, $PLACEHOLDER, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setPrefixPlaceholder - value already in use');
            }
        }
        else {
            throw new Error('setPrefixPlaceholder - invalid value');
        }
    };

    /**
     * Modify the context prefix in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setPrefixContext = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.prefixes[val] || opt.prefixes[val].exec === $CONTEXT) && !(opt.separators[val] || opt.containers[val])){
                updateOptionChar(opt.prefixes, $CONTEXT, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setPrefixContext - value already in use');
            }
        }
        else {
            throw new Error('setPrefixContext - invalid value');
        }
    };

    /**
     * Modify the property container characters in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for the container opener.
     * @param {String} closer New character to use for the container closer.
     */
    _this.setContainerProperty = function(val, closer){
        if (typeof val === $STRING && val.length === 1 && typeof closer === $STRING && closer.length === 1){
            if (val !== $WILDCARD && (!opt.containers[val] || opt.containers[val].exec === $PROPERTY) && !(opt.separators[val] || opt.prefixes[val])){
                updateOptionChar(opt.containers, $PROPERTY, val, closer);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setContainerProperty - value already in use');
            }
        }
        else {
            throw new Error('setContainerProperty - invalid value');
        }
    };

    /**
     * Modify the single quote container characters in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for the container opener.
     * @param {String} closer New character to use for the container closer.
     */
    _this.setContainerSinglequote = function(val, closer){
        if (typeof val === $STRING && val.length === 1 && typeof closer === $STRING && closer.length === 1){
            if (val !== $WILDCARD && (!opt.containers[val] || opt.containers[val].exec === $SINGLEQUOTE) && !(opt.separators[val] || opt.prefixes[val])){
                updateOptionChar(opt.containers, $SINGLEQUOTE, val, closer);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setContainerSinglequote - value already in use');
            }
        }
        else {
            throw new Error('setContainerSinglequote - invalid value');
        }
    };

    /**
     * Modify the double quote container characters in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for the container opener.
     * @param {String} closer New character to use for the container closer.
     */
    _this.setContainerDoublequote = function(val, closer){
        if (typeof val === $STRING && val.length === 1 && typeof closer === $STRING && closer.length === 1){
            if (val !== $WILDCARD && (!opt.containers[val] || opt.containers[val].exec === $DOUBLEQUOTE) && !(opt.separators[val] || opt.prefixes[val])){
                updateOptionChar(opt.containers, $DOUBLEQUOTE, val, closer);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setContainerDoublequote - value already in use');
            }
        }
        else {
            throw new Error('setContainerDoublequote - invalid value');
        }
    };

    /**
     * Modify the function call container characters in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for the container opener.
     * @param {String} closer New character to use for the container closer.
     */
    _this.setContainerCall = function(val, closer){
        if (typeof val === $STRING && val.length === 1 && typeof closer === $STRING && closer.length === 1){
            if (val !== $WILDCARD && (!opt.containers[val] || opt.containers[val].exec === $CALL) && !(opt.separators[val] || opt.prefixes[val])){
                updateOptionChar(opt.containers, $CALL, val, closer);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setContainerCall - value already in use');
            }
        }
        else {
            throw new Error('setContainerCall - invalid value');
        }
    };

    /**
     * Modify the eval property container characters in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for the container opener.
     * @param {String} closer New character to use for the container closer.
     */
    _this.setContainerEvalProperty = function(val, closer){
        if (typeof val === $STRING && val.length === 1 && typeof closer === $STRING && closer.length === 1){
            if (val !== $WILDCARD && (!opt.containers[val] || opt.containers[val].exec === $EVALPROPERTY) && !(opt.separators[val] || opt.prefixes[val])){
                updateOptionChar(opt.containers, $EVALPROPERTY, val, closer);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setContainerEvalProperty - value already in use');
            }
        }
        else {
            throw new Error('setContainerProperty - invalid value');
        }
    };

    /**
     * Reset all PathToolkit options to their default values.
     * @public
     */
    _this.resetOptions = function(){
        setDefaultOptions();
        updateRegEx();
        cache = {};
    };

    // Initialize option set
    setDefaultOptions();
    updateRegEx();

    // Apply custom options if provided as argument to constructor
    options && _this.setOptions(options);

};

return PathToolkit;

})));

//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjpudWxsLCJzb3VyY2VzIjpbIi9ob21lL2Fhcm9uL3Byb2plY3RzL3BhdGgtdG9vbGtpdC9zcmMvcGF0aC10b29sa2l0LmpzIl0sInNvdXJjZXNDb250ZW50IjpbIi8qKlxuICogQGZpbGVPdmVydmlldyBQYXRoVG9vbGtpdCBldmFsdWF0ZXMgc3RyaW5nIHBhdGhzIGFzIHByb3BlcnR5L2luZGV4IHNlcXVlbmNlcyB3aXRoaW4gb2JqZWN0cyBhbmQgYXJyYXlzXG4gKiBAYXV0aG9yIEFhcm9uIEJyb3duXG4gKiBAdmVyc2lvbiAxLjAuM1xuICovXG5cbi8vIFBhcnNpbmcsIHRva2VuaW56aW5nLCBldGNcbid1c2Ugc3RyaWN0JztcblxuLy8gU29tZSBjb25zdGFudHMgZm9yIGNvbnZlbmllbmNlXG52YXIgVU5ERUYgPSAoZnVuY3Rpb24odSl7cmV0dXJuIHU7fSkoKTtcblxuLy8gU3RhdGljIHN0cmluZ3MsIGFzc2lnbmVkIHRvIGFpZCBjb2RlIG1pbmlmaWNhdGlvblxudmFyICRXSUxEQ0FSRCAgICAgPSAnKicsXG4gICAgJFVOREVGSU5FRCAgICA9ICd1bmRlZmluZWQnLFxuICAgICRTVFJJTkcgICAgICAgPSAnc3RyaW5nJyxcbiAgICAkUEFSRU5UICAgICAgID0gJ3BhcmVudCcsXG4gICAgJFJPT1QgICAgICAgICA9ICdyb290JyxcbiAgICAkUExBQ0VIT0xERVIgID0gJ3BsYWNlaG9sZGVyJyxcbiAgICAkQ09OVEVYVCAgICAgID0gJ2NvbnRleHQnLFxuICAgICRMSVRFUkFMICAgICAgPSAnbGl0ZXJhbCcsXG4gICAgJFBST1BFUlRZICAgICA9ICdwcm9wZXJ0eScsXG4gICAgJENPTExFQ1RJT04gICA9ICdjb2xsZWN0aW9uJyxcbiAgICAkRUFDSCAgICAgICAgID0gJ2VhY2gnLFxuICAgICRTSU5HTEVRVU9URSAgPSAnc2luZ2xlcXVvdGUnLFxuICAgICRET1VCTEVRVU9URSAgPSAnZG91YmxlcXVvdGUnLFxuICAgICRDQUxMICAgICAgICAgPSAnY2FsbCcsXG4gICAgJEVWQUxQUk9QRVJUWSA9ICdldmFsUHJvcGVydHknO1xuICAgIFxuLyoqXG4gKiBUZXN0cyB3aGV0aGVyIGEgd2lsZGNhcmQgdGVtcGxhdGVzIG1hdGNoZXMgYSBnaXZlbiBzdHJpbmcuXG4gKiBgYGBqYXZhc2NyaXB0XG4gKiB2YXIgc3RyID0gJ2FhYWJiYnh4eGNjY2RkZCc7XG4gKiB3aWxkQ2FyZE1hdGNoKCdhYWFiYmJ4eHhjY2NkZGQnKTsgLy8gdHJ1ZVxuICogd2lsZENhcmRNYXRjaCgnKicsIHN0cik7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJyonLCAnJyk7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJ2EqJywgc3RyKTsgLy8gdHJ1ZVxuICogd2lsZENhcmRNYXRjaCgnYWEqZGRkJywgc3RyKTsgLy8gdHJ1ZVxuICogd2lsZENhcmRNYXRjaCgnKmQnLCBzdHIpOyAvLyB0cnVlXG4gKiB3aWxkQ2FyZE1hdGNoKCcqYScsIHN0cik7IC8vIGZhbHNlXG4gKiB3aWxkQ2FyZE1hdGNoKCdhKnonLCBzdHIpOyAvLyBmYWxzZVxuICogYGBgXG4gKiBAcHJpdmF0ZVxuICogQHBhcmFtICB7U3RyaW5nfSB0ZW1wbGF0ZSBXaWxkY2FyZCBwYXR0ZXJuXG4gKiBAcGFyYW0gIHtTdHJpbmd9IHN0ciAgICAgIFN0cmluZyB0byBtYXRjaCBhZ2FpbnN0IHdpbGRjYXJkIHBhdHRlcm5cbiAqIEByZXR1cm4ge0Jvb2xlYW59ICAgICAgICAgIFRydWUgaWYgcGF0dGVybiBtYXRjaGVzIHN0cmluZzsgRmFsc2UgaWYgbm90XG4gKi9cbnZhciB3aWxkQ2FyZE1hdGNoID0gZnVuY3Rpb24odGVtcGxhdGUsIHN0cil7XG4gICAgdmFyIHBvcyA9IHRlbXBsYXRlLmluZGV4T2YoJFdJTERDQVJEKSxcbiAgICAgICAgcGFydHMgPSB0ZW1wbGF0ZS5zcGxpdCgkV0lMRENBUkQsIDIpLFxuICAgICAgICBtYXRjaCA9IHRydWU7XG4gICAgaWYgKHBhcnRzWzBdKXtcbiAgICAgICAgLy8gSWYgbm8gd2lsZGNhcmQgcHJlc2VudCwgcmV0dXJuIHNpbXBsZSBzdHJpbmcgY29tcGFyaXNvblxuICAgICAgICBpZiAocGFydHNbMF0gPT09IHRlbXBsYXRlKXtcbiAgICAgICAgICAgIHJldHVybiBwYXJ0c1swXSA9PT0gc3RyO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgbWF0Y2ggPSBtYXRjaCAmJiBzdHIuc3Vic3RyKDAsIHBhcnRzWzBdLmxlbmd0aCkgPT09IHBhcnRzWzBdO1xuICAgICAgICB9XG4gICAgfVxuICAgIGlmIChwYXJ0c1sxXSl7XG4gICAgICAgIG1hdGNoID0gbWF0Y2ggJiYgc3RyLnN1YnN0cigtMSpwYXJ0c1sxXS5sZW5ndGgpID09PSBwYXJ0c1sxXTtcbiAgICB9XG4gICAgcmV0dXJuIG1hdGNoO1xufTtcblxuLyoqXG4gKiBJbnNwZWN0IGlucHV0IHZhbHVlIGFuZCBkZXRlcm1pbmUgd2hldGhlciBpdCBpcyBhbiBPYmplY3Qgb3Igbm90LlxuICogVmFsdWVzIG9mIHVuZGVmaW5lZCBhbmQgbnVsbCB3aWxsIHJldHVybiBcImZhbHNlXCIsIG90aGVyd2lzZVxuICogbXVzdCBiZSBvZiB0eXBlIFwib2JqZWN0XCIgb3IgXCJmdW5jdGlvblwiLlxuICogQHByaXZhdGVcbiAqIEBwYXJhbSAge09iamVjdH0gIHZhbCBUaGluZyB0byBleGFtaW5lLCBtYXkgYmUgb2YgYW55IHR5cGVcbiAqIEByZXR1cm4ge0Jvb2xlYW59ICAgICBUcnVlIGlmIHRoaW5nIGlzIG9mIHR5cGUgXCJvYmplY3RcIiBvciBcImZ1bmN0aW9uXCJcbiAqL1xudmFyIGlzT2JqZWN0ID0gZnVuY3Rpb24odmFsKXtcbiAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFVOREVGSU5FRCB8fCB2YWwgPT09IG51bGwpIHsgcmV0dXJuIGZhbHNlO31cbiAgICByZXR1cm4gKCAodHlwZW9mIHZhbCA9PT0gJ2Z1bmN0aW9uJykgfHwgKHR5cGVvZiB2YWwgPT09ICdvYmplY3QnKSApO1xufTtcblxuLyoqXG4gKiBDb252ZXJ0IHZhcmlvdXMgdmFsdWVzIHRvIHRydWUgYm9vbGVhbiBgdHJ1ZWAgb3IgYGZhbHNlYC5cbiAqIEZvciBub24tc3RyaW5nIHZhbHVlcywgdGhlIG5hdGl2ZSBqYXZhc2NyaXB0IGlkZWEgb2YgXCJ0cnVlXCIgd2lsbCBhcHBseS5cbiAqIEZvciBzdHJpbmcgdmFsdWVzLCB0aGUgd29yZHMgXCJ0cnVlXCIsIFwieWVzXCIsIGFuZCBcIm9uXCIgd2lsbCBhbGwgcmV0dXJuIGB0cnVlYC5cbiAqIEFsbCBvdGhlciBzdHJpbmdzIHJldHVybiBgZmFsc2VgLiBUaGUgc3RyaW5nIG1hdGNoIGlzIG5vbi1jYXNlLXNlbnNpdGl2ZS5cbiAqIEBwcml2YXRlXG4gKi9cbnZhciB0cnV0aGlmeSA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgdmFyIHY7XG4gICAgaWYgKHR5cGVvZiB2YWwgIT09ICRTVFJJTkcpe1xuICAgICAgICByZXR1cm4gdmFsICYmIHRydWU7IC8vIFVzZSBuYXRpdmUgamF2YXNjcmlwdCBub3Rpb24gb2YgXCJ0cnV0aHlcIlxuICAgIH1cbiAgICB2ID0gdmFsLnRvVXBwZXJDYXNlKCk7XG4gICAgaWYgKHYgPT09ICdUUlVFJyB8fCB2ID09PSAnWUVTJyB8fCB2ID09PSAnT04nKXtcbiAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmYWxzZTtcbn07XG5cbi8qKlxuICogVXNpbmcgcHJvdmlkZWQgcXVvdGUgY2hhcmFjdGVyIGFzIHByZWZpeCBhbmQgc3VmZml4LCBlc2NhcGUgYW55IGluc3RhbmNlc1xuICogb2YgdGhlIHF1b3RlIGNoYXJhY3RlciB3aXRoaW4gdGhlIHN0cmluZyBhbmQgcmV0dXJuIHF1b3RlK3N0cmluZytxdW90ZS5cbiAqIFRoZSBjaGFyYWN0ZXIgZGVmaW5lZCBhcyBcInNpbmdsZXF1b3RlXCIgbWF5IGJlIGFsdGVyZWQgYnkgY3VzdG9tIG9wdGlvbnMsXG4gKiBzbyBhIGdlbmVyYWwtcHVycG9zZSBmdW5jdGlvbiBpcyBuZWVkZWQgdG8gcXVvdGUgcGF0aCBzZWdtZW50cyBjb3JyZWN0bHkuXG4gKiBAcHJpdmF0ZVxuICogQHBhcmFtICB7U3RyaW5nfSBxICAgU2luZ2xlLWNoYXJhY3RlciBzdHJpbmcgdG8gdXNlIGFzIHF1b3RlIGNoYXJhY3RlclxuICogQHBhcmFtICB7U3RyaW5nfSBzdHIgU3RyaW5nIHRvIGJlIHF1b3RlZC5cbiAqIEByZXR1cm4ge1N0cmluZ30gICAgIE9yaWdpbmFsIHN0cmluZywgc3Vycm91bmRlZCBieSB0aGUgcXVvdGUgY2hhcmFjdGVyLCBwb3NzaWJseSBtb2RpZmllZCBpbnRlcm5hbGx5IGlmIHRoZSBxdW90ZSBjaGFyYWN0ZXIgZXhpc3RzIHdpdGhpbiB0aGUgc3RyaW5nLlxuICovXG52YXIgcXVvdGVTdHJpbmcgPSBmdW5jdGlvbihxLCBzdHIpe1xuICAgIHZhciBxUmVnRXggPSBuZXcgUmVnRXhwKHEsICdnJyk7XG4gICAgcmV0dXJuIHEgKyBzdHIucmVwbGFjZShxUmVnRXgsICdcXFxcJyArIHEpICsgcTtcbn07XG5cbi8qKlxuICogUGF0aFRvb2xraXQgYmFzZSBvYmplY3QuIEluY2x1ZGVzIGFsbCBpbnN0YW5jZS1zcGVjaWZpYyBkYXRhIChvcHRpb25zLCBjYWNoZSlcbiAqIGFzIGxvY2FsIHZhcmlhYmxlcy4gTWF5IGJlIHBhc3NlZCBhbiBvcHRpb25zIGhhc2ggdG8gcHJlLWNvbmZpZ3VyZSB0aGVcbiAqIGluc3RhbmNlIHByaW9yIHRvIHVzZS5cbiAqIEBjb25zdHJ1Y3RvclxuICogQHByb3BlcnR5IHtPYmplY3R9IG9wdGlvbnMgT3B0aW9uYWwuIENvbGxlY3Rpb24gb2YgY29uZmlndXJhdGlvbiBzZXR0aW5ncyBmb3IgdGhpcyBpbnN0YW5jZSBvZiBQYXRoVG9vbGtpdC4gU2VlIGBzZXRPcHRpb25zYCBmdW5jdGlvbiBiZWxvdyBmb3IgZGV0YWlsZWQgZG9jdW1lbnRhdGlvbi5cbiAqL1xudmFyIFBhdGhUb29sa2l0ID0gZnVuY3Rpb24ob3B0aW9ucyl7XG4gICAgdmFyIF90aGlzID0gdGhpcyxcbiAgICAgICAgY2FjaGUgPSB7fSxcbiAgICAgICAgb3B0ID0ge30sXG4gICAgICAgIHByZWZpeExpc3QsIHNlcGFyYXRvckxpc3QsIGNvbnRhaW5lckxpc3QsIGNvbnRhaW5lckNsb3NlTGlzdCxcbiAgICAgICAgcHJvcGVydHlTZXBhcmF0b3IsXG4gICAgICAgIHNpbmdsZXF1b3RlLCBkb3VibGVxdW90ZSxcbiAgICAgICAgc2ltcGxlUGF0aENoYXJzLCBzaW1wbGVQYXRoUmVnRXgsXG4gICAgICAgIGFsbFNwZWNpYWxzLCBhbGxTcGVjaWFsc1JlZ0V4LFxuICAgICAgICBlc2NhcGVkTm9uU3BlY2lhbHNSZWdFeCxcbiAgICAgICAgZXNjYXBlZFF1b3RlcyxcbiAgICAgICAgd2lsZGNhcmRSZWdFeDtcblxuICAgIC8qKlxuICAgICAqIFNldmVyYWwgcmVndWxhciBleHByZXNzaW9ucyBhcmUgcHJlLWNvbXBpbGVkIGZvciB1c2UgaW4gcGF0aCBpbnRlcnByZXRhdGlvbi5cbiAgICAgKiBUaGVzZSBleHByZXNzaW9ucyBhcmUgYnVpbHQgZnJvbSB0aGUgY3VycmVudCBzeW50YXggY29uZmlndXJhdGlvbiwgc28gdGhleVxuICAgICAqIG11c3QgYmUgcmUtYnVpbHQgZXZlcnkgdGltZSB0aGUgc3ludGF4IGNoYW5nZXMuXG4gICAgICogQHByaXZhdGVcbiAgICAgKi9cbiAgICB2YXIgdXBkYXRlUmVnRXggPSBmdW5jdGlvbigpe1xuICAgICAgICAvLyBMaXN0cyBvZiBzcGVjaWFsIGNoYXJhY3RlcnMgZm9yIHVzZSBpbiByZWd1bGFyIGV4cHJlc3Npb25zXG4gICAgICAgIHByZWZpeExpc3QgPSBPYmplY3Qua2V5cyhvcHQucHJlZml4ZXMpO1xuICAgICAgICBzZXBhcmF0b3JMaXN0ID0gT2JqZWN0LmtleXMob3B0LnNlcGFyYXRvcnMpO1xuICAgICAgICBjb250YWluZXJMaXN0ID0gT2JqZWN0LmtleXMob3B0LmNvbnRhaW5lcnMpO1xuICAgICAgICBjb250YWluZXJDbG9zZUxpc3QgPSBjb250YWluZXJMaXN0Lm1hcChmdW5jdGlvbihrZXkpeyByZXR1cm4gb3B0LmNvbnRhaW5lcnNba2V5XS5jbG9zZXI7IH0pO1xuICAgICAgICBcbiAgICAgICAgcHJvcGVydHlTZXBhcmF0b3IgPSAnJztcbiAgICAgICAgT2JqZWN0LmtleXMob3B0LnNlcGFyYXRvcnMpLmZvckVhY2goZnVuY3Rpb24oc2VwKXsgaWYgKG9wdC5zZXBhcmF0b3JzW3NlcF0uZXhlYyA9PT0gJFBST1BFUlRZKXsgcHJvcGVydHlTZXBhcmF0b3IgPSBzZXA7IH0gfSk7XG4gICAgICAgIHNpbmdsZXF1b3RlID0gJyc7XG4gICAgICAgIGRvdWJsZXF1b3RlID0gJyc7XG4gICAgICAgIE9iamVjdC5rZXlzKG9wdC5jb250YWluZXJzKS5mb3JFYWNoKGZ1bmN0aW9uKHNlcCl7XG4gICAgICAgICAgICBpZiAob3B0LmNvbnRhaW5lcnNbc2VwXS5leGVjID09PSAkU0lOR0xFUVVPVEUpeyBzaW5nbGVxdW90ZSA9IHNlcDt9XG4gICAgICAgICAgICBpZiAob3B0LmNvbnRhaW5lcnNbc2VwXS5leGVjID09PSAkRE9VQkxFUVVPVEUpeyBkb3VibGVxdW90ZSA9IHNlcDt9XG4gICAgICAgIH0pO1xuXG4gICAgICAgIC8vIEZpbmQgYWxsIHNwZWNpYWwgY2hhcmFjdGVycyBleGNlcHQgcHJvcGVydHkgc2VwYXJhdG9yICguIGJ5IGRlZmF1bHQpXG4gICAgICAgIHNpbXBsZVBhdGhDaGFycyA9ICdbXFxcXFxcXFwnICsgWyRXSUxEQ0FSRF0uY29uY2F0KHByZWZpeExpc3QpLmNvbmNhdChzZXBhcmF0b3JMaXN0KS5jb25jYXQoY29udGFpbmVyTGlzdCkuam9pbignXFxcXCcpLnJlcGxhY2UoJ1xcXFwnK3Byb3BlcnR5U2VwYXJhdG9yLCAnJykgKyAnXSc7XG4gICAgICAgIHNpbXBsZVBhdGhSZWdFeCA9IG5ldyBSZWdFeHAoc2ltcGxlUGF0aENoYXJzKTtcbiAgICAgICAgXG4gICAgICAgIC8vIEZpbmQgYWxsIHNwZWNpYWwgY2hhcmFjdGVycywgaW5jbHVkaW5nIGJhY2tzbGFzaFxuICAgICAgICBhbGxTcGVjaWFscyA9ICdbXFxcXFxcXFxcXFxcJyArIFskV0lMRENBUkRdLmNvbmNhdChwcmVmaXhMaXN0KS5jb25jYXQoc2VwYXJhdG9yTGlzdCkuY29uY2F0KGNvbnRhaW5lckxpc3QpLmNvbmNhdChjb250YWluZXJDbG9zZUxpc3QpLmpvaW4oJ1xcXFwnKSArICddJztcbiAgICAgICAgYWxsU3BlY2lhbHNSZWdFeCA9IG5ldyBSZWdFeHAoYWxsU3BlY2lhbHMsICdnJyk7XG4gICAgICAgIFxuICAgICAgICAvLyBGaW5kIGFsbCBlc2NhcGVkIHNwZWNpYWwgY2hhcmFjdGVyc1xuICAgICAgICAvLyBlc2NhcGVkU3BlY2lhbHNSZWdFeCA9IG5ldyBSZWdFeHAoJ1xcXFwnK2FsbFNwZWNpYWxzLCAnZycpO1xuICAgICAgICAvLyBGaW5kIGFsbCBlc2NhcGVkIG5vbi1zcGVjaWFsIGNoYXJhY3RlcnMsIGkuZS4gdW5uZWNlc3NhcnkgZXNjYXBlc1xuICAgICAgICBlc2NhcGVkTm9uU3BlY2lhbHNSZWdFeCA9IG5ldyBSZWdFeHAoJ1xcXFwnK2FsbFNwZWNpYWxzLnJlcGxhY2UoL15cXFsvLCdbXicpKTtcbiAgICAgICAgaWYgKHNpbmdsZXF1b3RlIHx8IGRvdWJsZXF1b3RlKXtcbiAgICAgICAgICAgIGVzY2FwZWRRdW90ZXMgPSBuZXcgUmVnRXhwKCdcXFxcWycrc2luZ2xlcXVvdGUrZG91YmxlcXVvdGUrJ10nLCAnZycpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgZXNjYXBlZFF1b3RlcyA9ICcnO1xuICAgICAgICB9XG4gICAgICAgIFxuICAgICAgICAvLyBGaW5kIHdpbGRjYXJkIGNoYXJhY3RlclxuICAgICAgICB3aWxkY2FyZFJlZ0V4ID0gbmV3IFJlZ0V4cCgnXFxcXCcrJFdJTERDQVJEKTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2V0cyBhbGwgdGhlIGRlZmF1bHQgb3B0aW9ucyBmb3IgaW50ZXJwcmV0ZXIgYmVoYXZpb3IgYW5kIHN5bnRheC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqL1xuICAgIHZhciBzZXREZWZhdWx0T3B0aW9ucyA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIG9wdCA9IG9wdCB8fCB7fTtcbiAgICAgICAgLy8gRGVmYXVsdCBzZXR0aW5nc1xuICAgICAgICBvcHQudXNlQ2FjaGUgPSB0cnVlOyAgLy8gY2FjaGUgdG9rZW5pemVkIHBhdGhzIGZvciByZXBlYXRlZCB1c2VcbiAgICAgICAgb3B0LnNpbXBsZSA9IGZhbHNlOyAgIC8vIG9ubHkgc3VwcG9ydCBkb3Qtc2VwYXJhdGVkIHBhdGhzLCBubyBvdGhlciBzcGVjaWFsIGNoYXJhY3RlcnNcbiAgICAgICAgb3B0LmZvcmNlID0gZmFsc2U7ICAgIC8vIGNyZWF0ZSBpbnRlcm1lZGlhdGUgcHJvcGVydGllcyBkdXJpbmcgYHNldGAgb3BlcmF0aW9uXG5cbiAgICAgICAgLy8gRGVmYXVsdCBwcmVmaXggc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICAgIG9wdC5wcmVmaXhlcyA9IHtcbiAgICAgICAgICAgICdeJzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJFBBUkVOVFxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICd+Jzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJFJPT1RcbiAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnJSc6IHtcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRQTEFDRUhPTERFUlxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICdAJzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJENPTlRFWFRcbiAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnISc6IHtcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRMSVRFUkFMXG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIC8vIERlZmF1bHQgc2VwYXJhdG9yIHNwZWNpYWwgY2hhcmFjdGVyc1xuICAgICAgICBvcHQuc2VwYXJhdG9ycyA9IHtcbiAgICAgICAgICAgICcuJzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJFBST1BFUlRZXG4gICAgICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICcsJzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJENPTExFQ1RJT05cbiAgICAgICAgICAgICAgICB9LFxuICAgICAgICAgICAgJzwnOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkRUFDSFxuICAgICAgICAgICAgfVxuICAgICAgICB9O1xuICAgICAgICAvLyBEZWZhdWx0IGNvbnRhaW5lciBzcGVjaWFsIGNoYXJhY3RlcnNcbiAgICAgICAgb3B0LmNvbnRhaW5lcnMgPSB7XG4gICAgICAgICAgICAnWyc6IHtcbiAgICAgICAgICAgICAgICAnY2xvc2VyJzogJ10nLFxuICAgICAgICAgICAgICAgICdleGVjJzogJFBST1BFUlRZXG4gICAgICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICdcXCcnOiB7XG4gICAgICAgICAgICAgICAgJ2Nsb3Nlcic6ICdcXCcnLFxuICAgICAgICAgICAgICAgICdleGVjJzogJFNJTkdMRVFVT1RFXG4gICAgICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICdcIic6IHtcbiAgICAgICAgICAgICAgICAnY2xvc2VyJzogJ1wiJyxcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRET1VCTEVRVU9URVxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnKCc6IHtcbiAgICAgICAgICAgICAgICAnY2xvc2VyJzogJyknLFxuICAgICAgICAgICAgICAgICdleGVjJzogJENBTExcbiAgICAgICAgICAgICAgICB9LFxuICAgICAgICAgICAgJ3snOiB7XG4gICAgICAgICAgICAgICAgJ2Nsb3Nlcic6ICd9JyxcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRFVkFMUFJPUEVSVFlcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFRlc3Qgc3RyaW5nIHRvIHNlZSBpZiBpdCBpcyBzdXJyb3VuZGVkIGJ5IHNpbmdsZS0gb3IgZG91YmxlLXF1b3RlLCB1c2luZyB0aGVcbiAgICAgKiBjdXJyZW50IGNvbmZpZ3VyYXRpb24gZGVmaW5pdGlvbiBmb3IgdGhvc2UgY2hhcmFjdGVycy4gSWYgbm8gcXVvdGUgY29udGFpbmVyXG4gICAgICogaXMgZGVmaW5lZCwgdGhpcyBmdW5jdGlvbiB3aWxsIHJldHVybiBmYWxzZSBzaW5jZSBpdCdzIG5vdCBwb3NzaWJsZSB0byBxdW90ZVxuICAgICAqIHRoZSBzdHJpbmcgaWYgdGhlcmUgYXJlIG5vIHF1b3RlcyBpbiB0aGUgc3ludGF4LiBBbHNvIGlnbm9yZXMgZXNjYXBlZCBxdW90ZVxuICAgICAqIGNoYXJhY3RlcnMuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHN0ciBUaGUgc3RyaW5nIHRvIHRlc3QgZm9yIGVuY2xvc2luZyBxdW90ZXNcbiAgICAgKiBAcmV0dXJuIHtCb29sZWFufSB0cnVlID0gc3RyaW5nIGlzIGVuY2xvc2VkIGluIHF1b3RlczsgZmFsc2UgPSBub3QgcXVvdGVkXG4gICAgICovXG4gICAgdmFyIGlzUXVvdGVkID0gZnVuY3Rpb24oc3RyKXtcbiAgICAgICAgdmFyIGNsZWFuU3RyID0gc3RyLnJlcGxhY2UoZXNjYXBlZFF1b3RlcywgJycpO1xuICAgICAgICB2YXIgc3RyTGVuID0gY2xlYW5TdHIubGVuZ3RoO1xuICAgICAgICBpZiAoc3RyTGVuIDwgMil7IHJldHVybiBmYWxzZTsgfVxuICAgICAgICByZXR1cm4gIChjbGVhblN0clswXSA9PT0gY2xlYW5TdHJbc3RyTGVuIC0gMV0pICYmXG4gICAgICAgICAgICAgICAgKGNsZWFuU3RyWzBdID09PSBzaW5nbGVxdW90ZSB8fCBjbGVhblN0clswXSA9PT0gZG91YmxlcXVvdGUpO1xuICAgIH07XG4gICAgXG4gICAgLyoqXG4gICAgICogUmVtb3ZlIGVuY2xvc2luZyBxdW90ZXMgZnJvbSBhIHN0cmluZy4gVGhlIGlzUXVvdGVkIGZ1bmN0aW9uIHdpbGwgZGV0ZXJtaW5lXG4gICAgICogaWYgYW55IGNoYW5nZSBpcyBuZWVkZWQuIElmIHRoZSBzdHJpbmcgaXMgcXVvdGVkLCB3ZSBrbm93IHRoZSBmaXJzdCBhbmQgbGFzdFxuICAgICAqIGNoYXJhY3RlcnMgYXJlIHF1b3RlIG1hcmtzLCBzbyBzaW1wbHkgZG8gYSBzdHJpbmcgc2xpY2UuIElmIHRoZSBpbnB1dCB2YWx1ZSBpc1xuICAgICAqIG5vdCBxdW90ZWQsIHJldHVybiB0aGUgaW5wdXQgdmFsdWUgdW5jaGFuZ2VkLiBCZWNhdXNlIGlzUXVvdGVkIGlzIHVzZWQsIGlmXG4gICAgICogbm8gcXVvdGUgbWFya3MgYXJlIGRlZmluZWQgaW4gdGhlIHN5bnRheCwgdGhpcyBmdW5jdGlvbiB3aWxsIHJldHVybiB0aGUgaW5wdXQgdmFsdWUuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHN0ciBUaGUgc3RyaW5nIHRvIHVuLXF1b3RlXG4gICAgICogQHJldHVybiB7U3RyaW5nfSBUaGUgaW5wdXQgc3RyaW5nIHdpdGhvdXQgYW55IGVuY2xvc2luZyBxdW90ZSBtYXJrcy5cbiAgICAgKi9cbiAgICB2YXIgc3RyaXBRdW90ZXMgPSBmdW5jdGlvbihzdHIpe1xuICAgICAgICBpZiAoaXNRdW90ZWQoc3RyKSl7XG4gICAgICAgICAgICByZXR1cm4gc3RyLnNsaWNlKDEsIC0xKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gc3RyO1xuICAgIH07XG4gICAgXG4gICAgLyoqXG4gICAgICogU2NhbiBpbnB1dCBzdHJpbmcgZnJvbSBsZWZ0IHRvIHJpZ2h0LCBvbmUgY2hhcmFjdGVyIGF0IGEgdGltZS4gSWYgYSBzcGVjaWFsIGNoYXJhY3RlclxuICAgICAqIGlzIGZvdW5kIChvbmUgb2YgXCJzZXBhcmF0b3JzXCIsIFwiY29udGFpbmVyc1wiLCBvciBcInByZWZpeGVzXCIpLCBlaXRoZXIgc3RvcmUgdGhlIGFjY3VtdWxhdGVkXG4gICAgICogd29yZCBhcyBhIHRva2VuIG9yIGVsc2UgYmVnaW4gd2F0Y2hpbmcgaW5wdXQgZm9yIGVuZCBvZiB0b2tlbiAoZmluZGluZyBhIGNsb3NpbmcgY2hhcmFjdGVyXG4gICAgICogZm9yIGEgY29udGFpbmVyIG9yIHRoZSBlbmQgb2YgYSBjb2xsZWN0aW9uKS4gSWYgYSBjb250YWluZXIgaXMgZm91bmQsIGNhcHR1cmUgdGhlIHN1YnN0cmluZ1xuICAgICAqIHdpdGhpbiB0aGUgY29udGFpbmVyIGFuZCByZWN1cnNpdmVseSBjYWxsIGB0b2tlbml6ZWAgb24gdGhhdCBzdWJzdHJpbmcuIEZpbmFsIG91dHB1dCB3aWxsXG4gICAgICogYmUgYW4gYXJyYXkgb2YgdG9rZW5zLiBBIGNvbXBsZXggdG9rZW4gKG5vdCBhIHNpbXBsZSBwcm9wZXJ0eSBvciBpbmRleCkgd2lsbCBiZSByZXByZXNlbnRlZFxuICAgICAqIGFzIGFuIG9iamVjdCBjYXJyeWluZyBtZXRhZGF0YSBmb3IgcHJvY2Vzc2luZy5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSAge1N0cmluZ30gc3RyIFBhdGggc3RyaW5nXG4gICAgICogQHJldHVybiB7QXJyYXl9ICAgICBBcnJheSBvZiB0b2tlbnMgZm91bmQgaW4gdGhlIGlucHV0IHBhdGhcbiAgICAgKi9cbiAgICB2YXIgdG9rZW5pemUgPSBmdW5jdGlvbiAoc3RyKXtcbiAgICAgICAgdmFyIHBhdGggPSAnJyxcbiAgICAgICAgICAgIHNpbXBsZVBhdGggPSB0cnVlLCAvLyBwYXRoIGlzIGFzc3VtZWQgXCJzaW1wbGVcIiB1bnRpbCBwcm92ZW4gb3RoZXJ3aXNlXG4gICAgICAgICAgICB0b2tlbnMgPSBbXSxcbiAgICAgICAgICAgIHJlY3VyID0gW10sXG4gICAgICAgICAgICBtb2RzID0ge30sXG4gICAgICAgICAgICBwYXRoTGVuZ3RoID0gMCxcbiAgICAgICAgICAgIHdvcmQgPSAnJyxcbiAgICAgICAgICAgIGhhc1dpbGRjYXJkID0gZmFsc2UsXG4gICAgICAgICAgICBkb0VhY2ggPSBmYWxzZSwgLy8gbXVzdCByZW1lbWJlciB0aGUgXCJlYWNoXCIgb3BlcmF0b3IgaW50byB0aGUgZm9sbG93aW5nIHRva2VuXG4gICAgICAgICAgICBzdWJwYXRoID0gJycsXG4gICAgICAgICAgICBpID0gMCxcbiAgICAgICAgICAgIG9wZW5lciA9ICcnLFxuICAgICAgICAgICAgY2xvc2VyID0gJycsXG4gICAgICAgICAgICBzZXBhcmF0b3IgPSAnJyxcbiAgICAgICAgICAgIGNvbGxlY3Rpb24gPSBbXSxcbiAgICAgICAgICAgIGRlcHRoID0gMCxcbiAgICAgICAgICAgIGVzY2FwZWQgPSAwO1xuY29uc29sZS5sb2coJ3Rva2VuaXplOicsIHN0cik7XG5cbiAgICAgICAgaWYgKG9wdC51c2VDYWNoZSAmJiBjYWNoZVtzdHJdICE9PSBVTkRFRil7IHJldHVybiBjYWNoZVtzdHJdOyB9XG5cbiAgICAgICAgLy8gU3RyaXAgb3V0IGFueSB1bm5lY2Vzc2FyeSBlc2NhcGluZyB0byBzaW1wbGlmeSBwcm9jZXNzaW5nIGJlbG93XG4gICAgICAgIHBhdGggPSBzdHIucmVwbGFjZShlc2NhcGVkTm9uU3BlY2lhbHNSZWdFeCwgJyQmJy5zdWJzdHIoMSkpO1xuICAgICAgICBwYXRoTGVuZ3RoID0gcGF0aC5sZW5ndGg7XG5cbiAgICAgICAgaWYgKHR5cGVvZiBzdHIgPT09ICRTVFJJTkcgJiYgIXNpbXBsZVBhdGhSZWdFeC50ZXN0KHN0cikpe1xuICAgICAgICAgICAgdG9rZW5zID0gcGF0aC5zcGxpdChwcm9wZXJ0eVNlcGFyYXRvcik7XG4gICAgICAgICAgICBvcHQudXNlQ2FjaGUgJiYgKGNhY2hlW3N0cl0gPSB7dDogdG9rZW5zLCBzaW1wbGU6IHNpbXBsZVBhdGh9KTtcbiAgICAgICAgICAgIHJldHVybiB7dDogdG9rZW5zLCBzaW1wbGU6IHNpbXBsZVBhdGh9O1xuICAgICAgICB9XG5cbiAgICAgICAgZm9yIChpID0gMDsgaSA8IHBhdGhMZW5ndGg7IGkrKyl7XG4gICAgICAgICAgICAvLyBTa2lwIGVzY2FwZSBjaGFyYWN0ZXIgKGBcXGApIGFuZCBzZXQgXCJlc2NhcGVkXCIgdG8gdGhlIGluZGV4IHZhbHVlXG4gICAgICAgICAgICAvLyBvZiB0aGUgY2hhcmFjdGVyIHRvIGJlIHRyZWF0ZWQgYXMgYSBsaXRlcmFsXG4gICAgICAgICAgICBpZiAoIWVzY2FwZWQgJiYgcGF0aFtpXSA9PT0gJ1xcXFwnKXtcbiAgICAgICAgICAgICAgICAvLyBOZXh0IGNoYXJhY3RlciBpcyB0aGUgZXNjYXBlZCBjaGFyYWN0ZXJcbiAgICAgICAgICAgICAgICBlc2NhcGVkID0gaSsxO1xuICAgICAgICAgICAgICAgIGkrKztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIElmIGEgd2lsZGNhcmQgY2hhcmFjdGVyIGlzIGZvdW5kLCBtYXJrIHRoaXMgdG9rZW4gYXMgaGF2aW5nIGEgd2lsZGNhcmRcbiAgICAgICAgICAgIGlmIChwYXRoW2ldID09PSAkV0lMRENBUkQpIHtcbiAgICAgICAgICAgICAgICBoYXNXaWxkY2FyZCA9IHRydWU7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBJZiB3ZSBoYXZlIGFscmVhZHkgcHJvY2Vzc2VkIGEgY29udGFpbmVyIG9wZW5lciwgdHJlYXQgdGhpcyBzdWJwYXRoIHNwZWNpYWxseVxuICAgICAgICAgICAgaWYgKGRlcHRoID4gMCl7XG4gICAgICAgICAgICAgICAgLy8gSXMgdGhpcyBjaGFyYWN0ZXIgYW5vdGhlciBvcGVuZXIgZnJvbSB0aGUgc2FtZSBjb250YWluZXI/IElmIHNvLCBhZGQgdG9cbiAgICAgICAgICAgICAgICAvLyB0aGUgZGVwdGggbGV2ZWwgc28gd2UgY2FuIG1hdGNoIHRoZSBjbG9zZXJzIGNvcnJlY3RseS4gKEV4Y2VwdCBmb3IgcXVvdGVzXG4gICAgICAgICAgICAgICAgLy8gd2hpY2ggY2Fubm90IGJlIG5lc3RlZClcbiAgICAgICAgICAgICAgICAvLyBJcyB0aGlzIGNoYXJhY3RlciB0aGUgY2xvc2VyPyBJZiBzbywgYmFjayBvdXQgb25lIGxldmVsIG9mIGRlcHRoLlxuICAgICAgICAgICAgICAgIC8vIEJlIGNhcmVmdWw6IHF1b3RlIGNvbnRhaW5lciB1c2VzIHNhbWUgY2hhcmFjdGVyIGZvciBvcGVuZXIgYW5kIGNsb3Nlci5cbiAgICAgICAgICAgICAgICAhZXNjYXBlZCAmJiBwYXRoW2ldID09PSBvcGVuZXIgJiYgb3BlbmVyICE9PSBjbG9zZXIuY2xvc2VyICYmIGRlcHRoKys7XG4gICAgICAgICAgICAgICAgIWVzY2FwZWQgJiYgcGF0aFtpXSA9PT0gY2xvc2VyLmNsb3NlciAmJiBkZXB0aC0tO1xuXG4gICAgICAgICAgICAgICAgLy8gV2hpbGUgc3RpbGwgaW5zaWRlIHRoZSBjb250YWluZXIsIGp1c3QgYWRkIHRvIHRoZSBzdWJwYXRoXG4gICAgICAgICAgICAgICAgaWYgKGRlcHRoID4gMCl7XG4gICAgICAgICAgICAgICAgICAgIHN1YnBhdGggKz0gcGF0aFtpXTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gV2hlbiB3ZSBjbG9zZSBvZmYgdGhlIGNvbnRhaW5lciwgdGltZSB0byBwcm9jZXNzIHRoZSBzdWJwYXRoIGFuZCBhZGQgcmVzdWx0cyB0byBvdXIgdG9rZW5zXG4gICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIEhhbmRsZSBzdWJwYXRoIFwiW2Jhcl1cIiBpbiBmb28uW2Jhcl0sW2Jhel0gLSB3ZSBtdXN0IHByb2Nlc3Mgc3VicGF0aCBhbmQgY3JlYXRlIGEgbmV3IGNvbGxlY3Rpb25cbiAgICAgICAgICAgICAgICAgICAgaWYgKGkrMSA8IHBhdGhMZW5ndGggJiYgb3B0LnNlcGFyYXRvcnNbcGF0aFtpKzFdXSAmJiBvcHQuc2VwYXJhdG9yc1twYXRoW2krMV1dLmV4ZWMgPT09ICRDT0xMRUNUSU9OKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChzdWJwYXRoLmxlbmd0aCAmJiBjbG9zZXIuZXhlYyA9PT0gJFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHN0cmlwUXVvdGVzKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY2xvc2VyLmV4ZWMgPT09ICRTSU5HTEVRVU9URSB8fCBjbG9zZXIuZXhlYyA9PT0gJERPVUJMRVFVT1RFKXtcbmNvbnNvbGUubG9nKCczcXVvdGUgaGFzIG1vZHM6JywgbW9kcy5oYXMsIG1vZHMpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0gc3VicGF0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0gdG9rZW5pemUoc3VicGF0aCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHJlY3VyID09PSBVTkRFRil7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ci5leGVjID0gY2xvc2VyLmV4ZWM7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIuZG9FYWNoID0gZG9FYWNoO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgLy8gY29sbGVjdGlvbi5wdXNoKGNsb3Nlci5leGVjID09PSAkUFJPUEVSVFkgPyByZWN1ci50WzBdIDogcmVjdXIpO1xuICAgICAgICAgICAgICAgICAgICAgICAgY29sbGVjdGlvbi5wdXNoKHJlY3VyKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBIYW5kbGUgc3VicGF0aCBcIltiYXpdXCIgaW4gZm9vLltiYXJdLFtiYXpdIC0gd2UgbXVzdCBwcm9jZXNzIHN1YnBhdGggYW5kIGFkZCB0byBjb2xsZWN0aW9uXG4gICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKGNvbGxlY3Rpb25bMF0pe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHN1YnBhdGgubGVuZ3RoICYmIGNsb3Nlci5leGVjID09PSAkUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0gc3RyaXBRdW90ZXMoc3VicGF0aCk7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjbG9zZXIuZXhlYyA9PT0gJFNJTkdMRVFVT1RFIHx8IGNsb3Nlci5leGVjID09PSAkRE9VQkxFUVVPVEUpe1xuY29uc29sZS5sb2coJzJxdW90ZSBoYXMgbW9kczonLCBtb2RzLmhhcywgbW9kcyk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSBzdWJwYXRoO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSB0b2tlbml6ZShzdWJwYXRoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAocmVjdXIgPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmV4ZWMgPSBjbG9zZXIuZXhlYztcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ci5kb0VhY2ggPSBkb0VhY2g7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBjb2xsZWN0aW9uLnB1c2gocmVjdXIpO1xuICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2goeyd0dCc6Y29sbGVjdGlvbiwgJ2RvRWFjaCc6ZG9FYWNofSk7XG4gICAgICAgICAgICAgICAgICAgICAgICBjb2xsZWN0aW9uID0gW107XG4gICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIFNpbXBsZSBwcm9wZXJ0eSBjb250YWluZXIgaXMgZXF1aXZhbGVudCB0byBkb3Qtc2VwYXJhdGVkIHRva2VuLiBKdXN0IGFkZCB0aGlzIHRva2VuIHRvIHRva2Vucy5cbiAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY2xvc2VyLmV4ZWMgPT09ICRQUk9QRVJUWSl7XG4gICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHt0OltzdHJpcFF1b3RlcyhzdWJwYXRoKV19O1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGRvRWFjaCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2goeyd3JzpyZWN1ci50WzBdLCAnbW9kcyc6e30sICdkb0VhY2gnOnRydWV9KTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGRvRWFjaCA9IGZhbHNlOyAvLyByZXNldFxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2gocmVjdXIudFswXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSB0cnVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIFF1b3RlZCBzdWJwYXRoIGlzIGFsbCB0YWtlbiBsaXRlcmFsbHkgd2l0aG91dCB0b2tlbiBldmFsdWF0aW9uLiBKdXN0IGFkZCBzdWJwYXRoIHRvIHRva2VucyBhcy1pcy5cbiAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY2xvc2VyLmV4ZWMgPT09ICRTSU5HTEVRVU9URSB8fCBjbG9zZXIuZXhlYyA9PT0gJERPVUJMRVFVT1RFKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChtb2RzLmhhcyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgd29yZCA9IHsndyc6IHN1YnBhdGgsICdtb2RzJzogbW9kcywgJ2RvRWFjaCc6IGRvRWFjaH07XG5jb25zb2xlLmxvZygncXVvdGUgaGFzIG1vZHM6JywgbW9kcy5oYXMsIG1vZHMpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIG1vZHMgPSB7fTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2goc3VicGF0aCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSB0cnVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIE90aGVyd2lzZSwgY3JlYXRlIHRva2VuIG9iamVjdCB0byBob2xkIHRva2VuaXplZCBzdWJwYXRoLCBhZGQgdG8gdG9rZW5zLlxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChzdWJwYXRoID09PSAnJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSB7dDpbXSxzaW1wbGU6dHJ1ZX07XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHRva2VuaXplKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHJlY3VyID09PSBVTkRFRil7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmV4ZWMgPSBjbG9zZXIuZXhlYztcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmRvRWFjaCA9IGRvRWFjaDtcbiAgICAgICAgICAgICAgICAgICAgICAgIHRva2Vucy5wdXNoKHJlY3VyKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgc3VicGF0aCA9ICcnOyAvLyByZXNldCBzdWJwYXRoXG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gSWYgYSBwcmVmaXggY2hhcmFjdGVyIGlzIGZvdW5kLCBzdG9yZSBpdCBpbiBgbW9kc2AgZm9yIGxhdGVyIHJlZmVyZW5jZS5cbiAgICAgICAgICAgIC8vIE11c3Qga2VlcCBjb3VudCBkdWUgdG8gYHBhcmVudGAgcHJlZml4IHRoYXQgY2FuIGJlIHVzZWQgbXVsdGlwbGUgdGltZXMgaW4gb25lIHRva2VuLlxuICAgICAgICAgICAgZWxzZSBpZiAoIWVzY2FwZWQgJiYgcGF0aFtpXSBpbiBvcHQucHJlZml4ZXMgJiYgb3B0LnByZWZpeGVzW3BhdGhbaV1dLmV4ZWMpe1xuICAgICAgICAgICAgICAgIG1vZHMuaGFzID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICBpZiAobW9kc1tvcHQucHJlZml4ZXNbcGF0aFtpXV0uZXhlY10pIHsgbW9kc1tvcHQucHJlZml4ZXNbcGF0aFtpXV0uZXhlY10rKzsgfVxuICAgICAgICAgICAgICAgIGVsc2UgeyBtb2RzW29wdC5wcmVmaXhlc1twYXRoW2ldXS5leGVjXSA9IDE7IH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIElmIGEgc2VwYXJhdG9yIGlzIGZvdW5kLCB0aW1lIHRvIHN0b3JlIHRoZSB0b2tlbiB3ZSd2ZSBiZWVuIGFjY3VtdWxhdGluZy4gSWZcbiAgICAgICAgICAgIC8vIHRoaXMgdG9rZW4gaGFkIGEgcHJlZml4LCB3ZSBzdG9yZSB0aGUgdG9rZW4gYXMgYW4gb2JqZWN0IHdpdGggbW9kaWZpZXIgZGF0YS5cbiAgICAgICAgICAgIC8vIElmIHRoZSBzZXBhcmF0b3IgaXMgdGhlIGNvbGxlY3Rpb24gc2VwYXJhdG9yLCB3ZSBtdXN0IGVpdGhlciBjcmVhdGUgb3IgYWRkXG4gICAgICAgICAgICAvLyB0byBhIGNvbGxlY3Rpb24gZm9yIHRoaXMgdG9rZW4uIEZvciBzaW1wbGUgc2VwYXJhdG9yLCB3ZSBlaXRoZXIgYWRkIHRoZSB0b2tlblxuICAgICAgICAgICAgLy8gdG8gdGhlIHRva2VuIGxpc3Qgb3IgZWxzZSBhZGQgdG8gdGhlIGV4aXN0aW5nIGNvbGxlY3Rpb24gaWYgaXQgZXhpc3RzLlxuICAgICAgICAgICAgZWxzZSBpZiAoIWVzY2FwZWQgJiYgb3B0LnNlcGFyYXRvcnNbcGF0aFtpXV0gJiYgb3B0LnNlcGFyYXRvcnNbcGF0aFtpXV0uZXhlYyl7XG4gICAgICAgICAgICAgICAgc2VwYXJhdG9yID0gb3B0LnNlcGFyYXRvcnNbcGF0aFtpXV07XG4gICAgICAgICAgICAgICAgaWYgKCF3b3JkICYmIChtb2RzLmhhcyB8fCBoYXNXaWxkY2FyZCkpe1xuICAgICAgICAgICAgICAgICAgICAvLyBmb3VuZCBhIHNlcGFyYXRvciwgYWZ0ZXIgc2VlaW5nIHByZWZpeGVzLCBidXQgbm8gdG9rZW4gd29yZCAtPiBpbnZhbGlkXG4gICAgICAgICAgICAgICAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIFRoaXMgdG9rZW4gd2lsbCByZXF1aXJlIHNwZWNpYWwgaW50ZXJwcmV0ZXIgcHJvY2Vzc2luZyBkdWUgdG8gcHJlZml4IG9yIHdpbGRjYXJkLlxuICAgICAgICAgICAgICAgIGlmICh3b3JkICYmIChtb2RzLmhhcyB8fCBoYXNXaWxkY2FyZCB8fCBkb0VhY2gpKXtcbiAgICAgICAgICAgICAgICAgICAgd29yZCA9IHsndyc6IHdvcmQsICdtb2RzJzogbW9kcywgJ2RvRWFjaCc6IGRvRWFjaH07XG4gICAgICAgICAgICAgICAgICAgIG1vZHMgPSB7fTtcbiAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gd29yZCBpcyBhIHBsYWluIHByb3BlcnR5IG9yIGVuZCBvZiBjb2xsZWN0aW9uXG4gICAgICAgICAgICAgICAgaWYgKHNlcGFyYXRvci5leGVjID09PSAkUFJPUEVSVFkgfHwgc2VwYXJhdG9yLmV4ZWMgPT09ICRFQUNIKXtcbiAgICAgICAgICAgICAgICAgICAgLy8gd2UgYXJlIGdhdGhlcmluZyBhIGNvbGxlY3Rpb24sIHNvIGFkZCBsYXN0IHdvcmQgdG8gY29sbGVjdGlvbiBhbmQgdGhlbiBzdG9yZVxuICAgICAgICAgICAgICAgICAgICBpZiAoY29sbGVjdGlvblswXSAhPT0gVU5ERUYpe1xuICAgICAgICAgICAgICAgICAgICAgICAgd29yZCAmJiBjb2xsZWN0aW9uLnB1c2god29yZCk7XG4gICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaCh7J3R0Jzpjb2xsZWN0aW9uLCAnZG9FYWNoJzpkb0VhY2h9KTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbGxlY3Rpb24gPSBbXTsgLy8gcmVzZXRcbiAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gd29yZCBpcyBhIHBsYWluIHByb3BlcnR5XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgd29yZCAmJiB0b2tlbnMucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBJZiB0aGUgc2VwYXJhdG9yIGlzIHRoZSBcImVhY2hcIiBzZXBhcnRvciwgdGhlIGZvbGxvd2luZyB3b3JkIHdpbGwgYmUgZXZhbHVhdGVkIGRpZmZlcmVudGx5LlxuICAgICAgICAgICAgICAgICAgICAvLyBJZiBpdCdzIG5vdCB0aGUgXCJlYWNoXCIgc2VwYXJhdG9yLCB0aGVuIHJlc2V0IFwiZG9FYWNoXCJcbiAgICAgICAgICAgICAgICAgICAgZG9FYWNoID0gc2VwYXJhdG9yLmV4ZWMgPT09ICRFQUNIOyAvLyByZXNldFxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyB3b3JkIGlzIGEgY29sbGVjdGlvblxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKHNlcGFyYXRvci5leGVjID09PSAkQ09MTEVDVElPTil7XG4gICAgICAgICAgICAgICAgICAgIHdvcmQgJiYgY29sbGVjdGlvbi5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB3b3JkID0gJyc7IC8vIHJlc2V0XG4gICAgICAgICAgICAgICAgaGFzV2lsZGNhcmQgPSBmYWxzZTsgLy8gcmVzZXRcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIEZvdW5kIGEgY29udGFpbmVyIG9wZW5pbmcgY2hhcmFjdGVyLiBBIGNvbnRhaW5lciBvcGVuaW5nIGlzIGVxdWl2YWxlbnQgdG9cbiAgICAgICAgICAgIC8vIGZpbmRpbmcgYSBzZXBhcmF0b3IsIHNvIFwiZm9vLmJhclwiIGlzIGVxdWl2YWxlbnQgdG8gXCJmb29bYmFyXVwiLCBzbyBhcHBseSBzaW1pbGFyXG4gICAgICAgICAgICAvLyBwcm9jZXNzIGFzIHNlcGFyYXRvciBhYm92ZSB3aXRoIHJlc3BlY3QgdG8gdG9rZW4gd2UgaGF2ZSBhY2N1bXVsYXRlZCBzbyBmYXIuXG4gICAgICAgICAgICAvLyBFeGNlcHQgaW4gY2FzZSBjb2xsZWN0aW9ucyAtIHBhdGggbWF5IGhhdmUgYSBjb2xsZWN0aW9uIG9mIGNvbnRhaW5lcnMsIHNvXG4gICAgICAgICAgICAvLyBpbiBcImZvb1tiYXJdLFtiYXpdXCIsIHRoZSBcIltiYXJdXCIgbWFya3MgdGhlIGVuZCBvZiB0b2tlbiBcImZvb1wiLCBidXQgXCJbYmF6XVwiIGlzXG4gICAgICAgICAgICAvLyBtZXJlbHkgYW5vdGhlciBlbnRyeSBpbiB0aGUgY29sbGVjdGlvbiwgc28gd2UgZG9uJ3QgY2xvc2Ugb2ZmIHRoZSBjb2xsZWN0aW9uIHRva2VuXG4gICAgICAgICAgICAvLyB5ZXQuXG4gICAgICAgICAgICAvLyBTZXQgZGVwdGggdmFsdWUgZm9yIGZ1cnRoZXIgcHJvY2Vzc2luZy5cbiAgICAgICAgICAgIGVsc2UgaWYgKCFlc2NhcGVkICYmIG9wdC5jb250YWluZXJzW3BhdGhbaV1dICYmIG9wdC5jb250YWluZXJzW3BhdGhbaV1dLmV4ZWMpe1xuICAgICAgICAgICAgICAgIGNsb3NlciA9IG9wdC5jb250YWluZXJzW3BhdGhbaV1dO1xuICAgICAgICAgICAgICAgIGlmICh3b3JkICYmIChtb2RzLmhhcyB8fCBoYXNXaWxkY2FyZCB8fCBkb0VhY2gpKXtcbiAgICAgICAgICAgICAgICAgICAgaWYgKHR5cGVvZiB3b3JkID09PSAnc3RyaW5nJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICB3b3JkID0geyd3Jzogd29yZCwgJ21vZHMnOiBtb2RzLCAnZG9FYWNoJzpkb0VhY2h9O1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgd29yZC5tb2RzID0gbW9kcztcbiAgICAgICAgICAgICAgICAgICAgICAgIHdvcmQuZG9FYWNoID0gZG9FYWNoO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIG1vZHMgPSB7fTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgaWYgKGNvbGxlY3Rpb25bMF0gIT09IFVOREVGKXtcbiAgICAgICAgICAgICAgICAgICAgLy8gd2UgYXJlIGdhdGhlcmluZyBhIGNvbGxlY3Rpb24sIHNvIGFkZCBsYXN0IHdvcmQgdG8gY29sbGVjdGlvbiBhbmQgdGhlbiBzdG9yZVxuICAgICAgICAgICAgICAgICAgICB3b3JkICYmIGNvbGxlY3Rpb24ucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIHdvcmQgaXMgYSBwbGFpbiBwcm9wZXJ0eVxuICAgICAgICAgICAgICAgICAgICB3b3JkICYmIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIG9wZW5lciA9IHBhdGhbaV07XG4gICAgICAgICAgICAgICAgLy8gMSkgZG9uJ3QgcmVzZXQgZG9FYWNoIGZvciBlbXB0eSB3b3JkIGJlY2F1c2UgdGhpcyBpcyBbZm9vXTxbYmFyXVxuICAgICAgICAgICAgICAgIC8vIDIpIGRvbid0IHJlc2V0IGRvRWFjaCBmb3Igb3BlbmluZyBDYWxsIGJlY2F1c2UgdGhpcyBpcyBhLGI8Zm4oKVxuICAgICAgICAgICAgICAgIGlmICh3b3JkICYmIG9wdC5jb250YWluZXJzW29wZW5lcl0uZXhlYyAhPT0gJENBTEwpe1xuICAgICAgICAgICAgICAgICAgICBkb0VhY2ggPSBmYWxzZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgd29yZCA9ICcnO1xuICAgICAgICAgICAgICAgIGhhc1dpbGRjYXJkID0gZmFsc2U7XG4gICAgICAgICAgICAgICAgZGVwdGgrKztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIE90aGVyd2lzZSwgdGhpcyBpcyBqdXN0IGFub3RoZXIgY2hhcmFjdGVyIHRvIGFkZCB0byB0aGUgY3VycmVudCB0b2tlblxuICAgICAgICAgICAgZWxzZSBpZiAoaSA8IHBhdGhMZW5ndGgpIHtcbiAgICAgICAgICAgICAgICB3b3JkICs9IHBhdGhbaV07XG4gICAgICAgICAgICB9XG5cbiAgICAgICAgICAgIC8vIElmIGN1cnJlbnQgcGF0aCBpbmRleCBtYXRjaGVzIHRoZSBlc2NhcGUgaW5kZXggdmFsdWUsIHJlc2V0IGBlc2NhcGVkYFxuICAgICAgICAgICAgaWYgKGkgPCBwYXRoTGVuZ3RoICYmIGkgPT09IGVzY2FwZWQpe1xuICAgICAgICAgICAgICAgIGVzY2FwZWQgPSAwO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG5cbiAgICAgICAgLy8gUGF0aCBlbmRlZCBpbiBhbiBlc2NhcGUgY2hhcmFjdGVyXG4gICAgICAgIGlmIChlc2NhcGVkKXtcbiAgICAgICAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgICAgIH1cblxuICAgICAgICAvLyBBZGQgdHJhaWxpbmcgd29yZCB0byB0b2tlbnMsIGlmIHByZXNlbnRcbiAgICAgICAgaWYgKHR5cGVvZiB3b3JkID09PSAnc3RyaW5nJyAmJiB3b3JkICYmIChtb2RzLmhhcyB8fCBoYXNXaWxkY2FyZCB8fCBkb0VhY2gpKXtcbiAgICAgICAgICAgIHdvcmQgPSB7J3cnOiB3b3JkLCAnbW9kcyc6IG1vZHMsICdkb0VhY2gnOiBkb0VhY2h9O1xuICAgICAgICAgICAgbW9kcyA9IHt9O1xuICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmICh3b3JkICYmIHdvcmQubW9kcyl7XG4gICAgICAgICAgICB3b3JkLm1vZHMgPSBtb2RzO1xuICAgICAgICB9XG4gICAgICAgIC8vIFdlIGFyZSBnYXRoZXJpbmcgYSBjb2xsZWN0aW9uLCBzbyBhZGQgbGFzdCB3b3JkIHRvIGNvbGxlY3Rpb24gYW5kIHRoZW4gc3RvcmVcbiAgICAgICAgaWYgKGNvbGxlY3Rpb25bMF0gIT09IFVOREVGKXtcbiAgICAgICAgICAgIHdvcmQgJiYgY29sbGVjdGlvbi5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgdG9rZW5zLnB1c2goeyd0dCc6Y29sbGVjdGlvbiwgJ2RvRWFjaCc6ZG9FYWNofSk7XG4gICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICB9XG4gICAgICAgIC8vIFdvcmQgaXMgYSBwbGFpbiBwcm9wZXJ0eVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHdvcmQgJiYgdG9rZW5zLnB1c2god29yZCk7XG4gICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgIH1cblxuICAgICAgICAvLyBkZXB0aCAhPSAwIG1lYW5zIG1pc21hdGNoZWQgY29udGFpbmVyc1xuICAgICAgICBpZiAoZGVwdGggIT09IDApeyByZXR1cm4gdW5kZWZpbmVkOyB9XG5cbiAgICAgICAgLy8gSWYgcGF0aCB3YXMgdmFsaWQsIGNhY2hlIHRoZSByZXN1bHRcbiAgICAgICAgb3B0LnVzZUNhY2hlICYmIChjYWNoZVtzdHJdID0ge3Q6IHRva2Vucywgc2ltcGxlOiBzaW1wbGVQYXRofSk7XG5cbiAgICAgICAgcmV0dXJuIHt0OiB0b2tlbnMsIHNpbXBsZTogc2ltcGxlUGF0aH07XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEl0IGlzIGByZXNvbHZlUGF0aGAncyBqb2IgdG8gdHJhdmVyc2UgYW4gb2JqZWN0IGFjY29yZGluZyB0byB0aGUgdG9rZW5zXG4gICAgICogZGVyaXZlZCBmcm9tIHRoZSBrZXlwYXRoIGFuZCBlaXRoZXIgcmV0dXJuIHRoZSB2YWx1ZSBmb3VuZCB0aGVyZSBvciBzZXRcbiAgICAgKiBhIG5ldyB2YWx1ZSBpbiB0aGF0IGxvY2F0aW9uLlxuICAgICAqIFRoZSB0b2tlbnMgYXJlIGEgc2ltcGxlIGFycmF5IGFuZCBgcmVvc2x2ZVBhdGhgIGxvb3BzIHRocm91Z2ggdGhlIGxpc3RcbiAgICAgKiB3aXRoIGEgc2ltcGxlIFwid2hpbGVcIiBsb29wLiBBIHRva2VuIG1heSBpdHNlbGYgYmUgYSBuZXN0ZWQgdG9rZW4gYXJyYXksXG4gICAgICogd2hpY2ggaXMgcHJvY2Vzc2VkIHRocm91Z2ggcmVjdXJzaW9uLlxuICAgICAqIEFzIGVhY2ggc3VjY2Vzc2l2ZSB2YWx1ZSBpcyByZXNvbHZlZCB3aXRoaW4gYG9iamAsIHRoZSBjdXJyZW50IHZhbHVlIGlzXG4gICAgICogcHVzaGVkIG9udG8gdGhlIFwidmFsdWVTdGFja1wiLCBlbmFibGluZyBiYWNrd2FyZCByZWZlcmVuY2VzICh1cHdhcmRzIGluIGBvYmpgKVxuICAgICAqIHRocm91Z2ggcGF0aCBwcmVmaXhlcyBsaWtlIFwiPFwiIGZvciBcInBhcmVudFwiIGFuZCBcIn5cIiBmb3IgXCJyb290XCIuIFRoZSBsb29wXG4gICAgICogc2hvcnQtY2lyY3VpdHMgYnkgcmV0dXJuaW5nIGB1bmRlZmluZWRgIGlmIHRoZSBwYXRoIGlzIGludmFsaWQgYXQgYW55IHBvaW50LFxuICAgICAqIGV4Y2VwdCBpbiBgc2V0YCBzY2VuYXJpbyB3aXRoIGBmb3JjZWAgZW5hYmxlZC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSAge09iamVjdH0gb2JqICAgICAgICBUaGUgZGF0YSBvYmplY3QgdG8gYmUgcmVhZC93cml0dGVuXG4gICAgICogQHBhcmFtICB7U3RyaW5nfSBwYXRoICAgICAgIFRoZSBrZXlwYXRoIHdoaWNoIGByZXNvbHZlUGF0aGAgd2lsbCBldmFsdWF0ZSBhZ2FpbnN0IGBvYmpgLiBNYXkgYmUgYSBwcmUtY29tcGlsZWQgVG9rZW5zIHNldCBpbnN0ZWFkIG9mIGEgc3RyaW5nLlxuICAgICAqIEBwYXJhbSAge0FueX0gbmV3VmFsdWUgICBUaGUgbmV3IHZhbHVlIHRvIHNldCBhdCB0aGUgcG9pbnQgZGVzY3JpYmVkIGJ5IGBwYXRoYC4gVW5kZWZpbmVkIGlmIHVzZWQgaW4gYGdldGAgc2NlbmFyaW8uXG4gICAgICogQHBhcmFtICB7QXJyYXl9IGFyZ3MgICAgICAgQXJyYXkgb2YgZXh0cmEgYXJndW1lbnRzIHdoaWNoIG1heSBiZSByZWZlcmVuY2VkIGJ5IHBsYWNlaG9sZGVycy4gVW5kZWZpbmVkIGlmIG5vIGV4dHJhIGFyZ3VtZW50cyB3ZXJlIGdpdmVuLlxuICAgICAqIEBwYXJhbSAge0FycmF5fSB2YWx1ZVN0YWNrIFN0YWNrIG9mIG9iamVjdCBjb250ZXh0cyBhY2N1bXVsYXRlZCBhcyB0aGUgcGF0aCB0b2tlbnMgYXJlIHByb2Nlc3NlZCBpbiBgb2JqYFxuICAgICAqIEByZXR1cm4ge0FueX0gICAgICAgICAgICBJbiBgZ2V0YCwgcmV0dXJucyB0aGUgdmFsdWUgZm91bmQgaW4gYG9iamAgYXQgYHBhdGhgLiBJbiBgc2V0YCwgcmV0dXJucyB0aGUgbmV3IHZhbHVlIHRoYXQgd2FzIHNldCBpbiBgb2JqYC4gSWYgYGdldGAgb3IgYHNldGAgYXJlIG50byBzdWNjZXNzZnVsLCByZXR1cm5zIGB1bmRlZmluZWRgXG4gICAgICovXG4gICAgdmFyIHJlc29sdmVQYXRoID0gZnVuY3Rpb24gKG9iaiwgcGF0aCwgbmV3VmFsdWUsIGFyZ3MsIHZhbHVlU3RhY2spe1xuICAgICAgICB2YXIgY2hhbmdlID0gbmV3VmFsdWUgIT09IFVOREVGLCAvLyBhcmUgd2Ugc2V0dGluZyBhIG5ldyB2YWx1ZT9cbiAgICAgICAgICAgIHRrID0gW10sXG4gICAgICAgICAgICB0a0xlbmd0aCA9IDAsXG4gICAgICAgICAgICB0a0xhc3RJZHggPSAwLFxuICAgICAgICAgICAgdmFsdWVTdGFja0xlbmd0aCA9IDEsXG4gICAgICAgICAgICBpID0gMCwgaiA9IDAsXG4gICAgICAgICAgICBwcmV2ID0gb2JqLFxuICAgICAgICAgICAgY3VyciA9ICcnLFxuICAgICAgICAgICAgY3Vyckxlbmd0aCA9IDAsXG4gICAgICAgICAgICBlYWNoTGVuZ3RoID0gMCxcbiAgICAgICAgICAgIHdvcmRDb3B5ID0gJycsXG4gICAgICAgICAgICBjb250ZXh0UHJvcCxcbiAgICAgICAgICAgIGlkeCA9IDAsXG4gICAgICAgICAgICBjb250ZXh0ID0gb2JqLFxuICAgICAgICAgICAgcmV0LFxuICAgICAgICAgICAgbmV3VmFsdWVIZXJlID0gZmFsc2UsXG4gICAgICAgICAgICBwbGFjZUludCA9IDAsXG4gICAgICAgICAgICBwcm9wID0gJycsXG4gICAgICAgICAgICBjYWxsQXJncztcblxuICAgICAgICAvLyBGb3IgU3RyaW5nIHBhdGgsIGVpdGhlciBmZXRjaCB0b2tlbnMgZnJvbSBjYWNoZSBvciBmcm9tIGB0b2tlbml6ZWAuXG4gICAgICAgIGlmICh0eXBlb2YgcGF0aCA9PT0gJFNUUklORyl7XG4gICAgICAgICAgICBpZiAob3B0LnVzZUNhY2hlICYmIGNhY2hlW3BhdGhdKSB7IHRrID0gY2FjaGVbcGF0aF0udDsgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGsgPSB0b2tlbml6ZShwYXRoKTtcbiAgICAgICAgICAgICAgICBpZiAodGsgPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgIHRrID0gdGsudDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICAvLyBGb3IgYSBub24tc3RyaW5nLCBhc3N1bWUgYSBwcmUtY29tcGlsZWQgdG9rZW4gYXJyYXlcbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0ayA9IHBhdGgudCA/IHBhdGgudCA6IFtwYXRoXTtcbiAgICAgICAgfVxuXG4gICAgICAgIHRrTGVuZ3RoID0gdGsubGVuZ3RoO1xuICAgICAgICBpZiAodGtMZW5ndGggPT09IDApIHsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICB0a0xhc3RJZHggPSB0a0xlbmd0aCAtIDE7XG5cbiAgICAgICAgLy8gdmFsdWVTdGFjayB3aWxsIGJlIGFuIGFycmF5IGlmIHdlIGFyZSB3aXRoaW4gYSByZWN1cnNpdmUgY2FsbCB0byBgcmVzb2x2ZVBhdGhgXG4gICAgICAgIGlmICh2YWx1ZVN0YWNrKXtcbiAgICAgICAgICAgIHZhbHVlU3RhY2tMZW5ndGggPSB2YWx1ZVN0YWNrLmxlbmd0aDtcbiAgICAgICAgfVxuICAgICAgICAvLyBPbiBvcmlnaW5hbCBlbnRyeSB0byBgcmVzb2x2ZVBhdGhgLCBpbml0aWFsaXplIHZhbHVlU3RhY2sgd2l0aCB0aGUgYmFzZSBvYmplY3QuXG4gICAgICAgIC8vIHZhbHVlU3RhY2tMZW5ndGggd2FzIGFscmVhZHkgaW5pdGlhbGl6ZWQgdG8gMS5cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB2YWx1ZVN0YWNrID0gW29ial07XG4gICAgICAgIH1cblxuICAgICAgICAvLyBDb252ZXJ0ZWQgQXJyYXkucmVkdWNlIGludG8gd2hpbGUgbG9vcCwgc3RpbGwgdXNpbmcgXCJwcmV2XCIsIFwiY3VyclwiLCBcImlkeFwiXG4gICAgICAgIC8vIGFzIGxvb3AgdmFsdWVzXG4gICAgICAgIHdoaWxlIChwcmV2ICE9PSBVTkRFRiAmJiBpZHggPCB0a0xlbmd0aCl7XG4gICAgICAgICAgICBjdXJyID0gdGtbaWR4XTtcblxuICAgICAgICAgICAgLy8gSWYgd2UgYXJlIHNldHRpbmcgYSBuZXcgdmFsdWUgYW5kIHRoaXMgdG9rZW4gaXMgdGhlIGxhc3QgdG9rZW4sIHRoaXNcbiAgICAgICAgICAgIC8vIGlzIHRoZSBwb2ludCB3aGVyZSB0aGUgbmV3IHZhbHVlIG11c3QgYmUgc2V0LlxuICAgICAgICAgICAgbmV3VmFsdWVIZXJlID0gKGNoYW5nZSAmJiAoaWR4ID09PSB0a0xhc3RJZHgpKTtcblxuICAgICAgICAgICAgLy8gSGFuZGxlIG1vc3QgY29tbW9uIHNpbXBsZSBwYXRoIHNjZW5hcmlvIGZpcnN0XG4gICAgICAgICAgICBpZiAodHlwZW9mIGN1cnIgPT09ICRTVFJJTkcpe1xuICAgICAgICAgICAgICAgIC8vIElmIHdlIGFyZSBzZXR0aW5nLi4uXG4gICAgICAgICAgICAgICAgaWYgKGNoYW5nZSl7XG4gICAgICAgICAgICAgICAgICAgIC8vIElmIHRoaXMgaXMgdGhlIGZpbmFsIHRva2VuIHdoZXJlIHRoZSBuZXcgdmFsdWUgZ29lcywgc2V0IGl0XG4gICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtjdXJyXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRbY3Vycl0gIT09IG5ld1ZhbHVlKXsgcmV0dXJuIHVuZGVmaW5lZDsgfSAvLyBuZXcgdmFsdWUgZmFpbGVkIHRvIHNldFxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIEZvciBlYXJsaWVyIHRva2VucywgY3JlYXRlIG9iamVjdCBwcm9wZXJ0aWVzIGlmIFwiZm9yY2VcIiBpcyBlbmFibGVkXG4gICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKG9wdC5mb3JjZSAmJiB0eXBlb2YgY29udGV4dFtjdXJyXSA9PT0gJ3VuZGVmaW5lZCcpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbY3Vycl0gPSB7fTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBSZXR1cm4gdmFsdWUgaXMgYXNzaWduZWQgYXMgdmFsdWUgb2YgdGhpcyBvYmplY3QgcHJvcGVydHlcbiAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0W2N1cnJdO1xuXG4gICAgICAgICAgICAgICAgLy8gVGhpcyBiYXNpYyBzdHJ1Y3R1cmUgaXMgcmVwZWF0ZWQgaW4gb3RoZXIgc2NlbmFyaW9zIGJlbG93LCBzbyB0aGUgbG9naWNcbiAgICAgICAgICAgICAgICAvLyBwYXR0ZXJuIGlzIG9ubHkgZG9jdW1lbnRlZCBoZXJlIGZvciBicmV2aXR5LlxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGN1cnIgPT09IFVOREVGKXtcbiAgICAgICAgICAgICAgICAgICAgcmV0ID0gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChjdXJyLnR0KXtcbiAgICAgICAgICAgICAgICAgICAgLy8gQ2FsbCByZXNvbHZlUGF0aCBhZ2FpbiB3aXRoIGJhc2UgdmFsdWUgYXMgZXZhbHVhdGVkIHZhbHVlIHNvIGZhciBhbmRcbiAgICAgICAgICAgICAgICAgICAgLy8gZWFjaCBlbGVtZW50IG9mIGFycmF5IGFzIHRoZSBwYXRoLiBDb25jYXQgYWxsIHRoZSByZXN1bHRzIHRvZ2V0aGVyLlxuICAgICAgICAgICAgICAgICAgICByZXQgPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuZG9FYWNoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmICghQXJyYXkuaXNBcnJheShjb250ZXh0KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGogPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgZWFjaExlbmd0aCA9IGNvbnRleHQubGVuZ3RoO1xuICAgICAgICAgICAgICAgICAgICAgICAgXG4gICAgICAgICAgICAgICAgICAgICAgICAvLyBQYXRoIGxpa2UgQXJyYXktPkVhY2gtPkFycmF5IHJlcXVpcmVzIGEgbmVzdGVkIGZvciBsb29wXG4gICAgICAgICAgICAgICAgICAgICAgICAvLyB0byBwcm9jZXNzIHRoZSB0d28gYXJyYXkgbGF5ZXJzLlxuICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaiA8IGVhY2hMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGkgPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKFtdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBjdXJyTGVuZ3RoID0gY3Vyci50dC5sZW5ndGg7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaSA8IGN1cnJMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjdXJyLnR0W2ldLmRvRWFjaCA9IGZhbHNlOyAvLyBUaGlzIGlzIGEgaGFjaywgZG9uJ3Qga25vdyBob3cgZWxzZSB0byBkaXNhYmxlIFwiZG9FYWNoXCIgZm9yIGNvbGxlY3Rpb24gbWVtYmVyc1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gcmVzb2x2ZVBhdGgoY29udGV4dFtqXSwgY3Vyci50dFtpXSwgbmV3VmFsdWUsIGFyZ3MsIHZhbHVlU3RhY2spO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHR5cGVvZiBjdXJyLnR0W2ldID09PSAnc3RyaW5nJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0UHJvcCA9IGNvbnRleHRbal1bY3Vyci50dFtpXV07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0UHJvcCA9IHJlc29sdmVQYXRoKGNvbnRleHRbal0sIGN1cnIudHRbaV0sIHVuZGVmaW5lZCwgYXJncywgdmFsdWVTdGFjayk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRQcm9wID09PSBVTkRFRikgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgIFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnR0W2ldLnQgJiYgY3Vyci50dFtpXS5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W2pdW2NvbnRleHRQcm9wXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXRbal0ucHVzaChjb250ZXh0UHJvcCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci50dFtpXS50ICYmIGN1cnIudHRbaV0uZXhlYyA9PT0gJEVWQUxQUk9QRVJUWSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0W2pdLnB1c2goY29udGV4dFtqXVtjb250ZXh0UHJvcF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXRbal0ucHVzaChjb250ZXh0UHJvcCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBqKys7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpID0gMDtcbiAgICAgICAgICAgICAgICAgICAgICAgIGN1cnJMZW5ndGggPSBjdXJyLnR0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdoaWxlKGkgPCBjdXJyTGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSByZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLnR0W2ldLCBuZXdWYWx1ZSwgYXJncywgdmFsdWVTdGFjayk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHR5cGVvZiBjdXJyLnR0W2ldID09PSAnc3RyaW5nJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gY29udGV4dFtjdXJyLnR0W2ldXTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gcmVzb2x2ZVBhdGgoY29udGV4dCwgY3Vyci50dFtpXSwgdW5kZWZpbmVkLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRQcm9wID09PSBVTkRFRikgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnR0W2ldLnQgJiYgY3Vyci50dFtpXS5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbY29udGV4dFByb3BdID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0UHJvcCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnR0W2ldLnQgJiYgY3Vyci50dFtpXS5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbY29udGV4dFByb3BdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRQcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpKys7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoY3Vyci53KXtcbiAgICAgICAgICAgICAgICAgICAgLy8gdGhpcyB3b3JkIHRva2VuIGhhcyBtb2RpZmllcnNcbiAgICAgICAgICAgICAgICAgICAgd29yZENvcHkgPSBjdXJyLnc7XG4gICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMuaGFzKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMucGFyZW50KXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBtb2RpZnkgY3VycmVudCBjb250ZXh0LCBzaGlmdCB1cHdhcmRzIGluIGJhc2Ugb2JqZWN0IG9uZSBsZXZlbFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHQgPSB2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAxIC0gY3Vyci5tb2RzLnBhcmVudF07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHQgPT09IFVOREVGKSB7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMucm9vdCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gUmVzZXQgY29udGV4dCBhbmQgdmFsdWVTdGFjaywgc3RhcnQgb3ZlciBhdCByb290IGluIHRoaXMgY29udGV4dFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHQgPSB2YWx1ZVN0YWNrWzBdO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHZhbHVlU3RhY2sgPSBbY29udGV4dF07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdmFsdWVTdGFja0xlbmd0aCA9IDE7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5tb2RzLnBsYWNlaG9sZGVyKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBwbGFjZUludCA9IHdvcmRDb3B5IC0gMTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoYXJnc1twbGFjZUludF0gPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIEZvcmNlIGFyZ3NbcGxhY2VJbnRdIHRvIFN0cmluZywgd29uJ3QgYXR0ZW1wdCB0byBwcm9jZXNzXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gYXJnIG9mIHR5cGUgZnVuY3Rpb24sIGFycmF5LCBvciBwbGFpbiBvYmplY3RcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB3b3JkQ29weSA9IGFyZ3NbcGxhY2VJbnRdLnRvU3RyaW5nKCk7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5tb2RzLmxpdGVyYWwpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGFueXRoaW5nIHRvIGRvIGhlcmU/XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cblxuICAgICAgICAgICAgICAgICAgICAvLyBkb0VhY2ggb3B0aW9uIG1lYW5zIHRvIHRha2UgYWxsIHZhbHVlcyBpbiBjb250ZXh0IChtdXN0IGJlIGFuIGFycmF5KSwgYXBwbHlcbiAgICAgICAgICAgICAgICAgICAgLy8gXCJjdXJyXCIgdG8gZWFjaCBvbmUsIGFuZCByZXR1cm4gdGhlIG5ldyBhcnJheS4gT3BlcmF0ZXMgbGlrZSBBcnJheS5tYXAuXG4gICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLmRvRWFjaCl7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoIUFycmF5LmlzQXJyYXkoY29udGV4dCkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGkgPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgZWFjaExlbmd0aCA9IGNvbnRleHQubGVuZ3RoO1xuICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaSA8IGVhY2hMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIFwiY29udGV4dFwiIG1vZGlmaWVyIChcIkBcIiBieSBkZWZhdWx0KSByZXBsYWNlcyBjdXJyZW50IGNvbnRleHQgd2l0aCBhIHZhbHVlIGZyb21cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyB0aGUgYXJndW1lbnRzLlxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMuY29udGV4dCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHBsYWNlSW50ID0gd29yZENvcHkgLSAxO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoYXJnc1twbGFjZUludF0gPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBGb3JjZSBhcmdzW3BsYWNlSW50XSB0byBTdHJpbmcsIHdvbid0IGF0d29yZENvcHl0IHRvIHByb2Nlc3NcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gYXJnIG9mIHR5cGUgZnVuY3Rpb24sIGFycmF5LCBvciBwbGFpbiBvYmplY3RcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goYXJnc1twbGFjZUludF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBcImxpdGVyYWxcIiBtb2RpZmllciBpbmRpY2F0ZXMgd29yZCBzaG91bGQgYmUgdGFrZW4gYXMtaXMsIG5vdCBhc1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGEgcHJvcGVydHkgb2YgdGhlIGN1cnJlbnQgY29udGV4dC5cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjdXJyLm1vZHMubGl0ZXJhbCl7XG5jb25zb2xlLmxvZygnd29yZENvcHk6Jywgd29yZENvcHkpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaCh3b3JkQ29weSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBSZXBlYXQgYmFzaWMgc3RyaW5nIHByb3BlcnR5IHByb2Nlc3Npbmcgd2l0aCB3b3JkIGFuZCBtb2RpZmllZCBjb250ZXh0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjb250ZXh0W2ldW3dvcmRDb3B5XSAhPT0gVU5ERUYpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpeyBjb250ZXh0W2ldW3dvcmRDb3B5XSA9IG5ld1ZhbHVlOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldW3dvcmRDb3B5XSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAodHlwZW9mIGNvbnRleHRbaV0gPT09ICdmdW5jdGlvbicpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2god29yZENvcHkpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIFBsYWluIHByb3BlcnR5IHRva2VucyBhcmUgbGlzdGVkIGFzIHNwZWNpYWwgd29yZCB0b2tlbnMgd2hlbmV2ZXJcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gYSB3aWxkY2FyZCBpcyBmb3VuZCB3aXRoaW4gdGhlIHByb3BlcnR5IHN0cmluZy4gQSB3aWxkY2FyZCBpbiBhXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHByb3BlcnR5IGNhdXNlcyBhbiBhcnJheSBvZiBtYXRjaGluZyBwcm9wZXJ0aWVzIHRvIGJlIHJldHVybmVkLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBzbyBsb29wIHRocm91Z2ggYWxsIHByb3BlcnRpZXMgYW5kIGV2YWx1YXRlIHRva2VuIGZvciBldmVyeVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBwcm9wZXJ0eSB3aGVyZSBgd2lsZENhcmRNYXRjaGAgcmV0dXJucyB0cnVlLlxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmICh3aWxkY2FyZFJlZ0V4LnRlc3Qod29yZENvcHkpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKFtdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGZvciAocHJvcCBpbiBjb250ZXh0W2ldKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAod2lsZENhcmRNYXRjaCh3b3JkQ29weSwgcHJvcCkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXsgY29udGV4dFtpXVtwcm9wXSA9IG5ld1ZhbHVlOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldFtpXS5wdXNoKGNvbnRleHRbaV1bcHJvcF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpKys7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAvLyBcImNvbnRleHRcIiBtb2RpZmllciAoXCJAXCIgYnkgZGVmYXVsdCkgcmVwbGFjZXMgY3VycmVudCBjb250ZXh0IHdpdGggYSB2YWx1ZSBmcm9tXG4gICAgICAgICAgICAgICAgICAgICAgICAvLyB0aGUgYXJndW1lbnRzLlxuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5jb250ZXh0KXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBwbGFjZUludCA9IHdvcmRDb3B5IC0gMTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoYXJnc1twbGFjZUludF0gPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIEZvcmNlIGFyZ3NbcGxhY2VJbnRdIHRvIFN0cmluZywgd29uJ3QgYXR3b3JkQ29weXQgdG8gcHJvY2Vzc1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGFyZyBvZiB0eXBlIGZ1bmN0aW9uLCBhcnJheSwgb3IgcGxhaW4gb2JqZWN0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gYXJnc1twbGFjZUludF07XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAvLyBcImxpdGVyYWxcIiBtb2RpZmllciBpbmRpY2F0ZXMgd29yZCBzaG91bGQgYmUgdGFrZW4gYXMtaXMsIG5vdCBhc1xuICAgICAgICAgICAgICAgICAgICAgICAgLy8gYSBwcm9wZXJ0eSBvZiB0aGUgY3VycmVudCBjb250ZXh0LlxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY3Vyci5tb2RzLmxpdGVyYWwpe1xuY29uc29sZS5sb2coJ3dvcmRDb3B5OicsIHdvcmRDb3B5KTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaCh3b3JkQ29weSk7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBSZXBlYXQgYmFzaWMgc3RyaW5nIHByb3BlcnR5IHByb2Nlc3Npbmcgd2l0aCB3b3JkIGFuZCBtb2RpZmllZCBjb250ZXh0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRbd29yZENvcHldICE9PSBVTkRFRikge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXsgY29udGV4dFt3b3JkQ29weV0gPSBuZXdWYWx1ZTsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0W3dvcmRDb3B5XTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAodHlwZW9mIGNvbnRleHQgPT09ICdmdW5jdGlvbicpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gd29yZENvcHk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIFBsYWluIHByb3BlcnR5IHRva2VucyBhcmUgbGlzdGVkIGFzIHNwZWNpYWwgd29yZCB0b2tlbnMgd2hlbmV2ZXJcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBhIHdpbGRjYXJkIGlzIGZvdW5kIHdpdGhpbiB0aGUgcHJvcGVydHkgc3RyaW5nLiBBIHdpbGRjYXJkIGluIGFcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBwcm9wZXJ0eSBjYXVzZXMgYW4gYXJyYXkgb2YgbWF0Y2hpbmcgcHJvcGVydGllcyB0byBiZSByZXR1cm5lZCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBzbyBsb29wIHRocm91Z2ggYWxsIHByb3BlcnRpZXMgYW5kIGV2YWx1YXRlIHRva2VuIGZvciBldmVyeVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHByb3BlcnR5IHdoZXJlIGB3aWxkQ2FyZE1hdGNoYCByZXR1cm5zIHRydWUuXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAod2lsZGNhcmRSZWdFeC50ZXN0KHdvcmRDb3B5KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IFtdO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBmb3IgKHByb3AgaW4gY29udGV4dCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAod2lsZENhcmRNYXRjaCh3b3JkQ29weSwgcHJvcCkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpeyBjb250ZXh0W3Byb3BdID0gbmV3VmFsdWU7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W3Byb3BdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIEV2YWwgUHJvcGVydHkgdG9rZW5zIG9wZXJhdGUgb24gYSB0ZW1wb3JhcnkgY29udGV4dCBjcmVhdGVkIGJ5XG4gICAgICAgICAgICAgICAgLy8gcmVjdXJzaXZlbHkgY2FsbGluZyBgcmVzb2x2ZVBhdGhgIHdpdGggYSBjb3B5IG9mIHRoZSB2YWx1ZVN0YWNrLlxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKGN1cnIuZXhlYyA9PT0gJEVWQUxQUk9QRVJUWSl7XG4gICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLmRvRWFjaCl7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoIUFycmF5LmlzQXJyYXkoY29udGV4dCkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGkgPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgZWFjaExlbmd0aCA9IGNvbnRleHQubGVuZ3RoO1xuICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaSA8IGVhY2hMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnNpbXBsZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtpXVtfdGhpcy5nZXQoY29udGV4dFtpXSwge3Q6Y3Vyci50LCBzaW1wbGU6dHJ1ZX0pXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbaV1bX3RoaXMuZ2V0KGNvbnRleHRbaV0sIHt0OmN1cnIudCwgc2ltcGxlOnRydWV9KV0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W2ldW3Jlc29sdmVQYXRoKGNvbnRleHRbaV0sIGN1cnIsIFVOREVGLCBhcmdzLCB2YWx1ZVN0YWNrKV0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldW3Jlc29sdmVQYXRoKGNvbnRleHRbaV0sIGN1cnIsIFVOREVGLCBhcmdzLCB2YWx1ZVN0YWNrKV0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpKys7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5zaW1wbGUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W190aGlzLmdldChjb250ZXh0LCB7dDogY3Vyci50LCBzaW1wbGU6dHJ1ZX0pXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0W190aGlzLmdldChjb250ZXh0LCB7dDpjdXJyLnQsIHNpbXBsZTp0cnVlfSldO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbcmVzb2x2ZVBhdGgoY29udGV4dCwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0W3Jlc29sdmVQYXRoKGNvbnRleHQsIGN1cnIsIFVOREVGLCBhcmdzLCB2YWx1ZVN0YWNrKV07XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gRnVuY3Rpb25zIGFyZSBjYWxsZWQgdXNpbmcgYGNhbGxgIG9yIGBhcHBseWAsIGRlcGVuZGluZyBvbiB0aGUgc3RhdGUgb2ZcbiAgICAgICAgICAgICAgICAvLyB0aGUgYXJndW1lbnRzIHdpdGhpbiB0aGUgKCApIGNvbnRhaW5lci4gRnVuY3Rpb25zIGFyZSBleGVjdXRlZCB3aXRoIFwidGhpc1wiXG4gICAgICAgICAgICAgICAgLy8gc2V0IHRvIHRoZSBjb250ZXh0IGltbWVkaWF0ZWx5IHByaW9yIHRvIHRoZSBmdW5jdGlvbiBpbiB0aGUgc3RhY2suXG4gICAgICAgICAgICAgICAgLy8gRm9yIGV4YW1wbGUsIFwiYS5iLmMuZm4oKVwiIGlzIGVxdWl2YWxlbnQgdG8gb2JqLmEuYi5jLmZuLmNhbGwob2JqLmEuYi5jKVxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKGN1cnIuZXhlYyA9PT0gJENBTEwpe1xuICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5kb0VhY2gpe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKCFBcnJheS5pc0FycmF5KHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdKSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IFtdO1xuICAgICAgICAgICAgICAgICAgICAgICAgaSA9IDA7XG4gICAgICAgICAgICAgICAgICAgICAgICBlYWNoTGVuZ3RoID0gY29udGV4dC5sZW5ndGg7XG4gICAgICAgICAgICAgICAgICAgICAgICB3aGlsZShpIDwgZWFjaExlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gSWYgZnVuY3Rpb24gY2FsbCBoYXMgYXJndW1lbnRzLCBwcm9jZXNzIHRob3NlIGFyZ3VtZW50cyBhcyBhIG5ldyBwYXRoXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIudCAmJiBjdXJyLnQubGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY2FsbEFyZ3MgPSByZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjYWxsQXJncyA9PT0gVU5ERUYpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXS5hcHBseSh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXVtpXSkpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkoY2FsbEFyZ3MpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbaV0uYXBwbHkodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl1baV0sIGNhbGxBcmdzKSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldLmNhbGwodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl1baV0sIGNhbGxBcmdzKSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbaV0uY2FsbCh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXVtpXSkpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpKys7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAvLyBJZiBmdW5jdGlvbiBjYWxsIGhhcyBhcmd1bWVudHMsIHByb2Nlc3MgdGhvc2UgYXJndW1lbnRzIGFzIGEgbmV3IHBhdGhcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnQgJiYgY3Vyci50Lmxlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuc2ltcGxlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY2FsbEFyZ3MgPSBfdGhpcy5nZXQoY29udGV4dCwgY3Vycik7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjYWxsQXJncyA9IHJlc29sdmVQYXRoKGNvbnRleHQsIGN1cnIsIFVOREVGLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNhbGxBcmdzID09PSBVTkRFRil7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHQuYXBwbHkodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChBcnJheS5pc0FycmF5KGNhbGxBcmdzKSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHQuYXBwbHkodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl0sIGNhbGxBcmdzKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHQuY2FsbCh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXSwgY2FsbEFyZ3MpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHQuY2FsbCh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBBZGQgdGhlIHJldHVybiB2YWx1ZSB0byB0aGUgc3RhY2sgaW4gY2FzZSB3ZSBtdXN0IGxvb3AgYWdhaW4uXG4gICAgICAgICAgICAvLyBSZWN1cnNpdmUgY2FsbHMgcGFzcyB0aGUgc2FtZSB2YWx1ZVN0YWNrIGFycmF5IGFyb3VuZCwgYnV0IHdlIGRvbid0IHdhbnQgdG9cbiAgICAgICAgICAgIC8vIHB1c2ggZW50cmllcyBvbiB0aGUgc3RhY2sgaW5zaWRlIGEgcmVjdXJzaW9uLCBzbyBpbnN0ZWFkIHVzZSBmaXhlZCBhcnJheVxuICAgICAgICAgICAgLy8gaW5kZXggcmVmZXJlbmNlcyBiYXNlZCBvbiB3aGF0ICoqdGhpcyoqIGV4ZWN1dGlvbiBrbm93cyB0aGUgdmFsdWVTdGFja0xlbmd0aFxuICAgICAgICAgICAgLy8gc2hvdWxkIGJlLiBUaGF0IHdheSwgaWYgYSByZWN1cnNpb24gYWRkcyBuZXcgZWxlbWVudHMsIGFuZCB0aGVuIHdlIGJhY2sgb3V0LFxuICAgICAgICAgICAgLy8gdGhpcyBjb250ZXh0IHdpbGwgcmVtZW1iZXIgdGhlIG9sZCBzdGFjayBsZW5ndGggYW5kIHdpbGwgbWVyZWx5IG92ZXJ3cml0ZVxuICAgICAgICAgICAgLy8gdGhvc2UgYWRkZWQgZW50cmllcywgaWdub3JpbmcgdGhhdCB0aGV5IHdlcmUgdGhlcmUgaW4gdGhlIGZpcnN0IHBsYWNlLlxuICAgICAgICAgICAgdmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoKytdID0gcmV0O1xuICAgICAgICAgICAgY29udGV4dCA9IHJldDtcbiAgICAgICAgICAgIHByZXYgPSByZXQ7XG4gICAgICAgICAgICBpZHgrKztcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gY29udGV4dDtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2ltcGxpZmllZCBwYXRoIGV2YWx1YXRpb24gaGVhdmlseSBvcHRpbWl6ZWQgZm9yIHBlcmZvcm1hbmNlIHdoZW5cbiAgICAgKiBwcm9jZXNzaW5nIHBhdGhzIHdpdGggb25seSBwcm9wZXJ0eSBuYW1lcyBvciBpbmRpY2VzIGFuZCBzZXBhcmF0b3JzLlxuICAgICAqIElmIHRoZSBwYXRoIGNhbiBiZSBjb3JyZWN0bHkgcHJvY2Vzc2VkIHdpdGggXCJwYXRoLnNwbGl0KHNlcGFyYXRvcilcIixcbiAgICAgKiB0aGlzIGZ1bmN0aW9uIHdpbGwgZG8gc28uIEFueSBvdGhlciBzcGVjaWFsIGNoYXJhY3RlcnMgZm91bmQgaW4gdGhlXG4gICAgICogcGF0aCB3aWxsIGNhdXNlIHRoZSBwYXRoIHRvIGJlIGV2YWx1YXRlZCB3aXRoIHRoZSBmdWxsIGByZXNvbHZlUGF0aGBcbiAgICAgKiBmdW5jdGlvbiBpbnN0ZWFkLlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtICB7T2JqZWN0fSBvYmogICAgICAgIFRoZSBkYXRhIG9iamVjdCB0byBiZSByZWFkL3dyaXR0ZW5cbiAgICAgKiBAcGFyYW0gIHtTdHJpbmd9IHBhdGggICAgICAgVGhlIGtleXBhdGggd2hpY2ggYHJlc29sdmVQYXRoYCB3aWxsIGV2YWx1YXRlIGFnYWluc3QgYG9iamAuXG4gICAgICogQHBhcmFtICB7QW55fSBuZXdWYWx1ZSAgIFRoZSBuZXcgdmFsdWUgdG8gc2V0IGF0IHRoZSBwb2ludCBkZXNjcmliZWQgYnkgYHBhdGhgLiBVbmRlZmluZWQgaWYgdXNlZCBpbiBgZ2V0YCBzY2VuYXJpby5cbiAgICAgKiBAcmV0dXJuIHtBbnl9ICAgICAgICAgICAgSW4gYGdldGAsIHJldHVybnMgdGhlIHZhbHVlIGZvdW5kIGluIGBvYmpgIGF0IGBwYXRoYC4gSW4gYHNldGAsIHJldHVybnMgdGhlIG5ldyB2YWx1ZSB0aGF0IHdhcyBzZXQgaW4gYG9iamAuIElmIGBnZXRgIG9yIGBzZXRgIGFyZSBudG8gc3VjY2Vzc2Z1bCwgcmV0dXJucyBgdW5kZWZpbmVkYFxuICAgICAqL1xuICAgIHZhciBxdWlja1Jlc29sdmVTdHJpbmcgPSBmdW5jdGlvbihvYmosIHBhdGgsIG5ld1ZhbHVlKXtcbiAgICAgICAgdmFyIGNoYW5nZSA9IG5ld1ZhbHVlICE9PSBVTkRFRixcbiAgICAgICAgICAgIHRrID0gW10sXG4gICAgICAgICAgICBpID0gMCxcbiAgICAgICAgICAgIHRrTGVuZ3RoID0gMDtcblxuICAgICAgICB0ayA9IHBhdGguc3BsaXQocHJvcGVydHlTZXBhcmF0b3IpO1xuICAgICAgICBvcHQudXNlQ2FjaGUgJiYgKGNhY2hlW3BhdGhdID0ge3Q6IHRrLCBzaW1wbGU6IHRydWV9KTtcbiAgICAgICAgdGtMZW5ndGggPSB0ay5sZW5ndGg7XG4gICAgICAgIHdoaWxlIChvYmogIT09IFVOREVGICYmIGkgPCB0a0xlbmd0aCl7XG4gICAgICAgICAgICBpZiAodGtbaV0gPT09ICcnKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgZWxzZSBpZiAoY2hhbmdlKXtcbiAgICAgICAgICAgICAgICBpZiAoaSA9PT0gdGtMZW5ndGggLSAxKXtcbiAgICAgICAgICAgICAgICAgICAgb2JqW3RrW2ldXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBGb3IgYXJyYXlzLCB0ZXN0IGN1cnJlbnQgY29udGV4dCBhZ2FpbnN0IHVuZGVmaW5lZCB0byBhdm9pZCBwYXJzaW5nIHRoaXMgc2VnbWVudCBhcyBhIG51bWJlci5cbiAgICAgICAgICAgICAgICAvLyBGb3IgYW55dGhpbmcgZWxzZSwgdXNlIGhhc093blByb3BlcnR5LlxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKG9wdC5mb3JjZSAmJiB0eXBlb2Ygb2JqW3RrW2ldXSA9PT0gJ3VuZGVmaW5lZCcpIHtcbiAgICAgICAgICAgICAgICAgICAgb2JqW3RrW2ldXSA9IHt9O1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIG9iaiA9IG9ialt0a1tpKytdXTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gb2JqO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTaW1wbGlmaWVkIHBhdGggZXZhbHVhdGlvbiBoZWF2aWx5IG9wdGltaXplZCBmb3IgcGVyZm9ybWFuY2Ugd2hlblxuICAgICAqIHByb2Nlc3NpbmcgYXJyYXkgb2Ygc2ltcGxlIHBhdGggdG9rZW5zIChwbGFpbiBwcm9wZXJ0eSBuYW1lcykuXG4gICAgICogVGhpcyBmdW5jdGlvbiBpcyBlc3NlbnRpYWxseSB0aGUgc2FtZSBhcyBgcXVpY2tSZXNvbHZlU3RyaW5nYCBleGNlcHRcbiAgICAgKiBgcXVpY2tSZXNvbHZlVG9rZW5BcnJheWAgZG9lcyBudG8gbmVlZCB0byBleGVjdXRlIHBhdGguc3BsaXQuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0gIHtPYmplY3R9IG9iaiAgICAgICAgVGhlIGRhdGEgb2JqZWN0IHRvIGJlIHJlYWQvd3JpdHRlblxuICAgICAqIEBwYXJhbSAge0FycmF5fSB0ayAgICAgICBUaGUgdG9rZW4gYXJyYXkgd2hpY2ggYHJlc29sdmVQYXRoYCB3aWxsIGV2YWx1YXRlIGFnYWluc3QgYG9iamAuXG4gICAgICogQHBhcmFtICB7QW55fSBuZXdWYWx1ZSAgIFRoZSBuZXcgdmFsdWUgdG8gc2V0IGF0IHRoZSBwb2ludCBkZXNjcmliZWQgYnkgYHBhdGhgLiBVbmRlZmluZWQgaWYgdXNlZCBpbiBgZ2V0YCBzY2VuYXJpby5cbiAgICAgKiBAcmV0dXJuIHtBbnl9ICAgICAgICAgICAgSW4gYGdldGAsIHJldHVybnMgdGhlIHZhbHVlIGZvdW5kIGluIGBvYmpgIGF0IGBwYXRoYC4gSW4gYHNldGAsIHJldHVybnMgdGhlIG5ldyB2YWx1ZSB0aGF0IHdhcyBzZXQgaW4gYG9iamAuIElmIGBnZXRgIG9yIGBzZXRgIGFyZSBudG8gc3VjY2Vzc2Z1bCwgcmV0dXJucyBgdW5kZWZpbmVkYFxuICAgICAqL1xuICAgIHZhciBxdWlja1Jlc29sdmVUb2tlbkFycmF5ID0gZnVuY3Rpb24ob2JqLCB0aywgbmV3VmFsdWUpe1xuICAgICAgICB2YXIgY2hhbmdlID0gbmV3VmFsdWUgIT09IFVOREVGLFxuICAgICAgICAgICAgaSA9IDAsXG4gICAgICAgICAgICB0a0xlbmd0aCA9IHRrLmxlbmd0aDtcblxuICAgICAgICB3aGlsZSAob2JqICE9IG51bGwgJiYgaSA8IHRrTGVuZ3RoKXtcbiAgICAgICAgICAgIGlmICh0a1tpXSA9PT0gJycpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICBlbHNlIGlmIChjaGFuZ2Upe1xuICAgICAgICAgICAgICAgIGlmIChpID09PSB0a0xlbmd0aCAtIDEpe1xuICAgICAgICAgICAgICAgICAgICBvYmpbdGtbaV1dID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIEZvciBhcnJheXMsIHRlc3QgY3VycmVudCBjb250ZXh0IGFnYWluc3QgdW5kZWZpbmVkIHRvIGF2b2lkIHBhcnNpbmcgdGhpcyBzZWdtZW50IGFzIGEgbnVtYmVyLlxuICAgICAgICAgICAgICAgIC8vIEZvciBhbnl0aGluZyBlbHNlLCB1c2UgaGFzT3duUHJvcGVydHkuXG4gICAgICAgICAgICAgICAgZWxzZSBpZiAob3B0LmZvcmNlICYmIHR5cGVvZiBvYmpbdGtbaV1dID09PSAndW5kZWZpbmVkJykge1xuICAgICAgICAgICAgICAgICAgICBvYmpbdGtbaV1dID0ge307XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgb2JqID0gb2JqW3RrW2krK11dO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBvYmo7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNlYXJjaGVzIGFuIG9iamVjdCBvciBhcnJheSBmb3IgYSB2YWx1ZSwgYWNjdW11bGF0aW5nIHRoZSBrZXlwYXRoIHRvIHRoZSB2YWx1ZSBhbG9uZ1xuICAgICAqIHRoZSB3YXkuIE9wZXJhdGVzIGluIGEgcmVjdXJzaXZlIHdheSB1bnRpbCBlaXRoZXIgYWxsIGtleXMvaW5kaWNlcyBoYXZlIGJlZW5cbiAgICAgKiBleGhhdXN0ZWQgb3IgYSBtYXRjaCBpcyBmb3VuZC4gUmV0dXJuIHZhbHVlIFwidHJ1ZVwiIG1lYW5zIFwia2VlcCBzY2FubmluZ1wiLCBcImZhbHNlXCJcbiAgICAgKiBtZWFucyBcInN0b3Agbm93XCIuIElmIGEgbWF0Y2ggaXMgZm91bmQsIGluc3RlYWQgb2YgcmV0dXJuaW5nIGEgc2ltcGxlIFwiZmFsc2VcIiwgYVxuICAgICAqIGNhbGxiYWNrIGZ1bmN0aW9uIChzYXZlUGF0aCkgaXMgY2FsbGVkIHdoaWNoIHdpbGwgZGVjaWRlIHdoZXRoZXIgb3Igbm90IHRvIGNvbnRpbnVlXG4gICAgICogdGhlIHNjYW4uIFRoaXMgYWxsb3dzIHRoZSBmdW5jdGlvbiB0byBmaW5kIG9uZSBpbnN0YW5jZSBvZiB2YWx1ZSBvciBhbGwgaW5zdGFuY2VzLFxuICAgICAqIGJhc2VkIG9uIGxvZ2ljIGluIHRoZSBjYWxsYmFjay5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSB7T2JqZWN0fSBvYmogICAgVGhlIGRhdGEgb2JqZWN0IHRvIHNjYW5cbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFRoZSB2YWx1ZSB3ZSBhcmUgbG9va2luZyBmb3Igd2l0aGluIGBvYmpgXG4gICAgICogQHBhcmFtIHtGdW5jdGlvbn0gc2F2ZVBhdGggQ2FsbGJhY2sgZnVuY3Rpb24gd2hpY2ggd2lsbCBzdG9yZSBhY2N1bXVsYXRlZCBwYXRocyBhbmQgaW5kaWNhdGUgd2hldGhlciB0byBjb250aW51ZVxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBwYXRoIEFjY3VtdWxhdGVkIGtleXBhdGg7IHVuZGVmaW5lZCBhdCBmaXJzdCwgcG9wdWxhdGVkIGluIHJlY3Vyc2l2ZSBjYWxsc1xuICAgICAqIEByZXR1cm4ge0Jvb2xlYW59IEluZGljYXRlcyB3aGV0aGVyIHNjYW4gcHJvY2VzcyBzaG91bGQgY29udGludWUgKFwidHJ1ZVwiLT55ZXMsIFwiZmFsc2VcIi0+bm8pXG4gICAgICovXG4gICAgdmFyIHNjYW5Gb3JWYWx1ZSA9IGZ1bmN0aW9uKG9iaiwgdmFsLCBzYXZlUGF0aCwgcGF0aCl7XG4gICAgICAgIHZhciBpLCBsZW4sIG1vcmUsIGtleXMsIHByb3A7XG5cbiAgICAgICAgcGF0aCA9IHBhdGggPyBwYXRoIDogJyc7XG5cbiAgICAgICAgLy8gSWYgd2UgZm91bmQgdGhlIHZhbHVlIHdlJ3JlIGxvb2tpbmcgZm9yXG4gICAgICAgIGlmIChvYmogPT09IHZhbCl7XG4gICAgICAgICAgICByZXR1cm4gc2F2ZVBhdGgocGF0aCk7IC8vIFNhdmUgdGhlIGFjY3VtdWxhdGVkIHBhdGgsIGFzayB3aGV0aGVyIHRvIGNvbnRpbnVlXG4gICAgICAgIH1cbiAgICAgICAgLy8gVGhpcyBvYmplY3QgaXMgYW4gYXJyYXksIHNvIGV4YW1pbmUgZWFjaCBpbmRleCBzZXBhcmF0ZWx5XG4gICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkob2JqKSl7XG4gICAgICAgICAgICBsZW4gPSBvYmoubGVuZ3RoO1xuICAgICAgICAgICAgZm9yKGkgPSAwOyBpIDwgbGVuOyBpKyspe1xuICAgICAgICAgICAgICAgIC8vIENhbGwgYHNjYW5Gb3JWYWx1ZWAgcmVjdXJzaXZlbHlcbiAgICAgICAgICAgICAgICBtb3JlID0gc2NhbkZvclZhbHVlKG9ialtpXSwgdmFsLCBzYXZlUGF0aCwgcGF0aCArIHByb3BlcnR5U2VwYXJhdG9yICsgaSk7XG4gICAgICAgICAgICAgICAgLy8gSGFsdCBpZiB0aGF0IHJlY3Vyc2l2ZSBjYWxsIHJldHVybmVkIFwiZmFsc2VcIlxuICAgICAgICAgICAgICAgIGlmICghbW9yZSl7IHJldHVybjsgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7IC8vIGtlZXAgbG9va2luZ1xuICAgICAgICB9XG4gICAgICAgIC8vIFRoaXMgb2JqZWN0IGlzIGFuIG9iamVjdCwgc28gZXhhbWluZSBlYWNoIGxvY2FsIHByb3BlcnR5IHNlcGFyYXRlbHlcbiAgICAgICAgZWxzZSBpZiAoaXNPYmplY3Qob2JqKSkge1xuICAgICAgICAgICAga2V5cyA9IE9iamVjdC5rZXlzKG9iaik7XG4gICAgICAgICAgICBsZW4gPSBrZXlzLmxlbmd0aDtcbiAgICAgICAgICAgIGlmIChsZW4gPiAxKXsga2V5cyA9IGtleXMuc29ydCgpOyB9IC8vIEZvcmNlIG9yZGVyIG9mIG9iamVjdCBrZXlzIHRvIHByb2R1Y2UgcmVwZWF0YWJsZSByZXN1bHRzXG4gICAgICAgICAgICBmb3IgKGkgPSAwOyBpIDwgbGVuOyBpKyspe1xuICAgICAgICAgICAgICAgIGlmIChvYmouaGFzT3duUHJvcGVydHkoa2V5c1tpXSkpe1xuICAgICAgICAgICAgICAgICAgICBwcm9wID0ga2V5c1tpXTtcbiAgICAgICAgICAgICAgICAgICAgLy8gUHJvcGVydHkgbWF5IGluY2x1ZGUgdGhlIHNlcGFyYXRvciBjaGFyYWN0ZXIgb3Igc29tZSBvdGhlciBzcGVjaWFsIGNoYXJhY3RlcixcbiAgICAgICAgICAgICAgICAgICAgLy8gc28gcXVvdGUgdGhpcyBwYXRoIHNlZ21lbnQgYW5kIGVzY2FwZSBhbnkgc2VwYXJhdG9ycyB3aXRoaW4uXG4gICAgICAgICAgICAgICAgICAgIGlmIChhbGxTcGVjaWFsc1JlZ0V4LnRlc3QocHJvcCkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgcHJvcCA9IHF1b3RlU3RyaW5nKHNpbmdsZXF1b3RlLCBwcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBtb3JlID0gc2NhbkZvclZhbHVlKG9ialtrZXlzW2ldXSwgdmFsLCBzYXZlUGF0aCwgcGF0aCArIHByb3BlcnR5U2VwYXJhdG9yICsgcHJvcCk7XG4gICAgICAgICAgICAgICAgICAgIGlmICghbW9yZSl7IHJldHVybjsgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlOyAvLyBrZWVwIGxvb2tpbmdcbiAgICAgICAgfVxuICAgICAgICAvLyBMZWFmIG5vZGUgKHN0cmluZywgbnVtYmVyLCBjaGFyYWN0ZXIsIGJvb2xlYW4sIGV0Yy4pLCBidXQgZGlkbid0IG1hdGNoXG4gICAgICAgIHJldHVybiB0cnVlOyAvLyBrZWVwIGxvb2tpbmdcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogR2V0IHRva2VuaXplZCByZXByZXNlbnRhdGlvbiBvZiBzdHJpbmcga2V5cGF0aC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHBhdGggS2V5cGF0aFxuICAgICAqIEByZXR1cm4ge09iamVjdH0gT2JqZWN0IGluY2x1ZGluZyB0aGUgYXJyYXkgb2YgcGF0aCB0b2tlbnMgYW5kIGEgYm9vbGVhbiBpbmRpY2F0aW5nIFwic2ltcGxlXCIuIFNpbXBsZSB0b2tlbiBzZXRzIGhhdmUgbm8gc3BlY2lhbCBvcGVyYXRvcnMgb3IgbmVzdGVkIHRva2Vucywgb25seSBhIHBsYWluIGFycmF5IG9mIHN0cmluZ3MgZm9yIGZhc3QgZXZhbHVhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5nZXRUb2tlbnMgPSBmdW5jdGlvbihwYXRoKXtcbiAgICAgICAgdmFyIHRva2VucyA9IHRva2VuaXplKHBhdGgpO1xuICAgICAgICBpZiAodHlwZW9mIHRva2VucyA9PT0gJFVOREVGSU5FRCl7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgcmV0dXJuIHRva2VucztcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogSW5mb3JtcyB3aGV0aGVyIHRoZSBzdHJpbmcgcGF0aCBoYXMgdmFsaWQgc3ludGF4LiBUaGUgcGF0aCBpcyBOT1QgZXZhbHVhdGVkIGFnYWluc3QgYVxuICAgICAqIGRhdGEgb2JqZWN0LCBvbmx5IHRoZSBzeW50YXggaXMgY2hlY2tlZC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHBhdGggS2V5cGF0aFxuICAgICAqIEByZXR1cm4ge0Jvb2xlYW59IHZhbGlkIHN5bnRheCAtPiBcInRydWVcIjsgbm90IHZhbGlkIC0+IFwiZmFsc2VcIlxuICAgICAqL1xuICAgIF90aGlzLmlzVmFsaWQgPSBmdW5jdGlvbihwYXRoKXtcbiAgICAgICAgcmV0dXJuIHR5cGVvZiB0b2tlbml6ZShwYXRoKSAhPT0gJFVOREVGSU5FRDtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogRXNjYXBlcyBhbnkgc3BlY2lhbCBjaGFyYWN0ZXJzIGZvdW5kIGluIHRoZSBpbnB1dCBzdHJpbmcgdXNpbmcgYmFja3NsYXNoLCBwcmV2ZW50aW5nXG4gICAgICogdGhlc2UgY2hhcmFjdGVycyBmcm9tIGNhdXNpbmcgdW5pbnRlbmRlZCBwcm9jZXNzaW5nIGJ5IFBhdGhUb29sa2l0LiBUaGlzIGZ1bmN0aW9uXG4gICAgICogRE9FUyByZXNwZWN0IHRoZSBjdXJyZW50IGNvbmZpZ3VyZWQgc3ludGF4LCBldmVuIGlmIGl0IGhhcyBiZWVuIGFsdGVyZWQgZnJvbSB0aGUgZGVmYXVsdC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHNlZ21lbnQgU2VnbWVudCBvZiBhIGtleXBhdGhcbiAgICAgKiBAcmV0dXJuIHtTdHJpbmd9IFRoZSBvcmlnaW5hbCBzZWdtZW50IHN0cmluZyB3aXRoIGFsbCBQYXRoVG9vbGtpdCBzcGVjaWFsIGNoYXJhY3RlcnMgcHJlcGVuZGVkIHdpdGggXCJcXFwiXG4gICAgICovXG4gICAgX3RoaXMuZXNjYXBlID0gZnVuY3Rpb24oc2VnbWVudCl7XG4gICAgICAgIHJldHVybiBzZWdtZW50LnJlcGxhY2UoYWxsU3BlY2lhbHNSZWdFeCwgJ1xcXFwkJicpO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBFdmFsdWF0ZXMga2V5cGF0aCBpbiBvYmplY3QgYW5kIHJldHVybnMgdGhlIHZhbHVlIGZvdW5kIHRoZXJlLCBpZiBhdmFpbGFibGUuIElmIHRoZSBwYXRoXG4gICAgICogZG9lcyBub3QgZXhpc3QgaW4gdGhlIHByb3ZpZGVkIGRhdGEgb2JqZWN0LCByZXR1cm5zIGB1bmRlZmluZWRgLiBGb3IgXCJzaW1wbGVcIiBwYXRocywgd2hpY2hcbiAgICAgKiBkb24ndCBpbmNsdWRlIGFueSBvcGVyYXRpb25zIGJleW9uZCBwcm9wZXJ0eSBzZXBhcmF0b3JzLCBvcHRpbWl6ZWQgcmVzb2x2ZXJzIHdpbGwgYmUgdXNlZFxuICAgICAqIHdoaWNoIGFyZSBtb3JlIGxpZ2h0d2VpZ2h0IHRoYW4gdGhlIGZ1bGwtZmVhdHVyZWQgYHJlc29sdmVQYXRoYC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IG9iaiBTb3VyY2UgZGF0YSBvYmplY3RcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBLZXlwYXRoIHRvIGV2YWx1YXRlIHdpdGhpbiBcIm9ialwiLiBBbHNvIGFjY2VwdHMgdG9rZW4gYXJyYXkgaW4gcGxhY2Ugb2YgYSBzdHJpbmcgcGF0aC5cbiAgICAgKiBAcmV0dXJuIHtBbnl9IElmIHRoZSBrZXlwYXRoIGV4aXN0cyBpbiBcIm9ialwiLCByZXR1cm4gdGhlIHZhbHVlIGF0IHRoYXQgbG9jYXRpb247IElmIG5vdCwgcmV0dXJuIGB1bmRlZmluZWRgLlxuICAgICAqL1xuICAgIF90aGlzLmdldCA9IGZ1bmN0aW9uIChvYmosIHBhdGgpe1xuICAgICAgICB2YXIgaSA9IDAsXG4gICAgICAgICAgICBsZW4gPSBhcmd1bWVudHMubGVuZ3RoLFxuICAgICAgICAgICAgYXJncztcbiAgICAgICAgLy8gRm9yIHN0cmluZyBwYXRocywgZmlyc3Qgc2VlIGlmIHBhdGggaGFzIGFscmVhZHkgYmVlbiBjYWNoZWQgYW5kIGlmIHRoZSB0b2tlbiBzZXQgaXMgc2ltcGxlLiBJZlxuICAgICAgICAvLyBzbywgd2UgY2FuIHVzZSB0aGUgb3B0aW1pemVkIHRva2VuIGFycmF5IHJlc29sdmVyIHVzaW5nIHRoZSBjYWNoZWQgdG9rZW4gc2V0LlxuICAgICAgICAvLyBJZiB0aGVyZSBpcyBubyBjYWNoZWQgZW50cnksIHVzZSBSZWdFeCB0byBsb29rIGZvciBzcGVjaWFsIGNoYXJhY3RlcnMgYXBhcnQgZnJvbSB0aGUgc2VwYXJhdG9yLlxuICAgICAgICAvLyBJZiBub25lIGFyZSBmb3VuZCwgd2UgY2FuIHVzZSB0aGUgb3B0aW1pemVkIHN0cmluZyByZXNvbHZlci5cbiAgICAgICAgaWYgKHR5cGVvZiBwYXRoID09PSAkU1RSSU5HKXtcbiAgICAgICAgICAgIGlmIChvcHQudXNlQ2FjaGUgJiYgY2FjaGVbcGF0aF0gJiYgY2FjaGVbcGF0aF0uc2ltcGxlKXtcbiAgICAgICAgICAgICAgICByZXR1cm4gcXVpY2tSZXNvbHZlVG9rZW5BcnJheShvYmosIGNhY2hlW3BhdGhdLnQpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoIXNpbXBsZVBhdGhSZWdFeC50ZXN0KHBhdGgpKXtcbiAgICAgICAgICAgICAgICByZXR1cm4gcXVpY2tSZXNvbHZlU3RyaW5nKG9iaiwgcGF0aCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgLy8gRm9yIGFycmF5IHBhdGhzIChwcmUtY29tcGlsZWQgdG9rZW4gc2V0cyksIGNoZWNrIGZvciBzaW1wbGljaXR5IHNvIHdlIGNhbiB1c2UgdGhlIG9wdGltaXplZCByZXNvbHZlci5cbiAgICAgICAgZWxzZSBpZiAoQXJyYXkuaXNBcnJheShwYXRoLnQpICYmIHBhdGguc2ltcGxlKXtcbiAgICAgICAgICAgIHJldHVybiBxdWlja1Jlc29sdmVUb2tlbkFycmF5KG9iaiwgcGF0aC50KTtcbiAgICAgICAgfVxuICAgICAgICBcbiAgICAgICAgLy8gSWYgd2UgbWFkZSBpdCB0aGlzIGZhciwgdGhlIHBhdGggaXMgY29tcGxleCBhbmQgbWF5IGluY2x1ZGUgcGxhY2Vob2xkZXJzLiBHYXRoZXIgdXAgYW55XG4gICAgICAgIC8vIGV4dHJhIGFyZ3VtZW50cyBhbmQgY2FsbCB0aGUgZnVsbCBgcmVzb2x2ZVBhdGhgIGZ1bmN0aW9uLlxuICAgICAgICBhcmdzID0gW107XG4gICAgICAgIGlmIChsZW4gPiAyKXtcbiAgICAgICAgICAgIGZvciAoaSA9IDI7IGkgPCBsZW47IGkrKykgeyBhcmdzW2ktMl0gPSBhcmd1bWVudHNbaV07IH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gcmVzb2x2ZVBhdGgob2JqLCBwYXRoLCB1bmRlZmluZWQsIGFyZ3MpO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBFdmFsdWF0ZXMgYSBrZXlwYXRoIGluIG9iamVjdCBhbmQgc2V0cyBhIG5ldyB2YWx1ZSBhdCB0aGUgcG9pbnQgZGVzY3JpYmVkIGluIHRoZSBrZXlwYXRoLiBJZlxuICAgICAqIFwiZm9yY2VcIiBpcyBkaXNhYmxlZCwgdGhlIGZ1bGwgcGF0aCBtdXN0IGV4aXN0IHVwIHRvIHRoZSBmaW5hbCBwcm9wZXJ0eSwgd2hpY2ggbWF5IGJlIGNyZWF0ZWRcbiAgICAgKiBieSB0aGUgc2V0IG9wZXJhdGlvbi4gSWYgXCJmb3JjZVwiIGlzIGVuYWJsZWQsIGFueSBtaXNzaW5nIGludGVybWVkaWF0ZSBwcm9wZXJ0aWVzIHdpbGwgYmUgY3JlYXRlZFxuICAgICAqIGluIG9yZGVyIHRvIHNldCB0aGUgdmFsdWUgb24gdGhlIGZpbmFsIHByb3BlcnR5LiBJZiBgc2V0YCBzdWNjZWVkcywgcmV0dXJucyBcInRydWVcIiwgb3RoZXJ3aXNlIFwiZmFsc2VcIi5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IG9iaiBTb3VyY2UgZGF0YSBvYmplY3RcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBLZXlwYXRoIHRvIGV2YWx1YXRlIHdpdGhpbiBcIm9ialwiLiBBbHNvIGFjY2VwdHMgdG9rZW4gYXJyYXkgaW4gcGxhY2Ugb2YgYSBzdHJpbmcgcGF0aC5cbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIE5ldyB2YWx1ZSB0byBzZXQgYXQgdGhlIGxvY2F0aW9uIGRlc2NyaWJlZCBpbiBcInBhdGhcIlxuICAgICAqIEByZXR1cm4ge0Jvb2xlYW59IFwidHJ1ZVwiIGlmIHRoZSBzZXQgb3BlcmF0aW9uIHN1Y2NlZWRzOyBcImZhbHNlXCIgaWYgaXQgZG9lcyBub3Qgc3VjY2VlZFxuICAgICAqL1xuICAgIF90aGlzLnNldCA9IGZ1bmN0aW9uKG9iaiwgcGF0aCwgdmFsKXtcbiAgICAgICAgdmFyIGkgPSAwLFxuICAgICAgICAgICAgbGVuID0gYXJndW1lbnRzLmxlbmd0aCxcbiAgICAgICAgICAgIGFyZ3MsXG4gICAgICAgICAgICByZWYsXG4gICAgICAgICAgICBkb25lID0gZmFsc2U7XG4gICAgICAgICAgICBcbiAgICAgICAgLy8gUGF0aCByZXNvbHV0aW9uIGZvbGxvd3MgdGhlIHNhbWUgbG9naWMgYXMgYGdldGAgYWJvdmUsIHdpdGggb25lIGRpZmZlcmVuY2U6IGBnZXRgIHdpbGxcbiAgICAgICAgLy8gYWJvcnQgYnkgcmV0dXJuaW5nIHRoZSB2YWx1ZSBhcyBzb29uIGFzIGl0J3MgZm91bmQuIGBzZXRgIGRvZXMgbm90IGFib3J0IHNvIHRoZSBpZi1lbHNlXG4gICAgICAgIC8vIHN0cnVjdHVyZSBpcyBzbGlnaHRseSBkaWZmZXJlbnQgdG8gZGljdGF0ZSB3aGVuL2lmIHRoZSBmaW5hbCBjYXNlIHNob3VsZCBleGVjdXRlLlxuICAgICAgICBpZiAodHlwZW9mIHBhdGggPT09ICRTVFJJTkcpe1xuICAgICAgICAgICAgaWYgKG9wdC51c2VDYWNoZSAmJiBjYWNoZVtwYXRoXSAmJiBjYWNoZVtwYXRoXS5zaW1wbGUpe1xuICAgICAgICAgICAgICAgIHJlZiA9IHF1aWNrUmVzb2x2ZVRva2VuQXJyYXkob2JqLCBjYWNoZVtwYXRoXS50LCB2YWwpO1xuICAgICAgICAgICAgICAgIGRvbmUgfD0gdHJ1ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKCFzaW1wbGVQYXRoUmVnRXgudGVzdChwYXRoKSl7XG4gICAgICAgICAgICAgICAgcmVmID0gcXVpY2tSZXNvbHZlU3RyaW5nKG9iaiwgcGF0aCwgdmFsKTtcbiAgICAgICAgICAgICAgICBkb25lIHw9IHRydWU7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoQXJyYXkuaXNBcnJheShwYXRoLnQpICYmIHBhdGguc2ltcGxlKXtcbiAgICAgICAgICAgIHJlZiA9IHF1aWNrUmVzb2x2ZVRva2VuQXJyYXkob2JqLCBwYXRoLnQsIHZhbCk7XG4gICAgICAgICAgICBkb25lIHw9IHRydWU7XG4gICAgICAgIH1cbiAgICAgICAgXG4gICAgICAgIC8vIFBhdGggd2FzIChwcm9iYWJseSkgYSBzdHJpbmcgYW5kIGl0IGNvbnRhaW5lZCBjb21wbGV4IHBhdGggY2hhcmFjdGVyc1xuICAgICAgICBpZiAoIWRvbmUpIHtcbiAgICAgICAgICAgIGlmIChsZW4gPiAzKXtcbiAgICAgICAgICAgICAgICBhcmdzID0gW107XG4gICAgICAgICAgICAgICAgZm9yIChpID0gMzsgaSA8IGxlbjsgaSsrKSB7IGFyZ3NbaS0zXSA9IGFyZ3VtZW50c1tpXTsgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmVmID0gcmVzb2x2ZVBhdGgob2JqLCBwYXRoLCB2YWwsIGFyZ3MpO1xuICAgICAgICB9XG4gICAgICAgIFxuICAgICAgICAvLyBgc2V0YCBjYW4gc2V0IGEgbmV3IHZhbHVlIGluIG11bHRpcGxlIHBsYWNlcyBpZiB0aGUgZmluYWwgcGF0aCBzZWdtZW50IGlzIGFuIGFycmF5LlxuICAgICAgICAvLyBJZiBhbnkgb2YgdGhvc2UgdmFsdWUgYXNzaWdubWVudHMgZmFpbCwgYHNldGAgd2lsbCByZXR1cm4gXCJmYWxzZVwiIGluZGljYXRpbmcgZmFpbHVyZS5cbiAgICAgICAgaWYgKEFycmF5LmlzQXJyYXkocmVmKSl7XG4gICAgICAgICAgICByZXR1cm4gcmVmLmluZGV4T2YodW5kZWZpbmVkKSA9PT0gLTE7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHJlZiAhPT0gVU5ERUY7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIExvY2F0ZSBhIHZhbHVlIHdpdGhpbiBhbiBvYmplY3Qgb3IgYXJyYXkuIFRoaXMgaXMgdGhlIHB1YmxpY2x5IGV4cG9zZWQgaW50ZXJmYWNlIHRvIHRoZVxuICAgICAqIHByaXZhdGUgYHNjYW5Gb3JWYWx1ZWAgZnVuY3Rpb24gZGVmaW5lZCBhYm92ZS5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IG9iaiBTb3VyY2UgZGF0YSBvYmplY3RcbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFRoZSB2YWx1ZSB0byBzZWFyY2ggZm9yIHdpdGhpbiBcIm9ialwiXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IG9uZU9yTWFueSBPcHRpb25hbDsgSWYgbWlzc2luZyBvciBcIm9uZVwiLCBgZmluZGAgd2lsbCBvbmx5IHJldHVybiB0aGUgZmlyc3QgdmFsaWQgcGF0aC4gSWYgXCJvbk9yTWFueVwiIGlzIGFueSBvdGhlciBzdHJpbmcsIGBmaW5kYCB3aWxsIHNjYW4gdGhlIGZ1bGwgb2JqZWN0IGxvb2tpbmcgZm9yIGFsbCB2YWxpZCBwYXRocyB0byBhbGwgY2FzZXMgd2hlcmUgXCJ2YWxcIiBhcHBlYXJzLlxuICAgICAqIEByZXR1cm4ge0FycmF5fSBBcnJheSBvZiBrZXlwYXRocyB0byBcInZhbFwiIG9yIGB1bmRlZmluZWRgIGlmIFwidmFsXCIgaXMgbm90IGZvdW5kLlxuICAgICAqL1xuICAgIF90aGlzLmZpbmQgPSBmdW5jdGlvbihvYmosIHZhbCwgb25lT3JNYW55KXtcbiAgICAgICAgdmFyIHJldFZhbCA9IFtdO1xuICAgICAgICAvLyBzYXZlUGF0aCBpcyB0aGUgY2FsbGJhY2sgd2hpY2ggd2lsbCBhY2N1bXVsYXRlIGFueSBmb3VuZCBwYXRocyBpbiBhIGxvY2FsIGFycmF5XG4gICAgICAgIC8vIHZhcmlhYmxlLlxuICAgICAgICB2YXIgc2F2ZVBhdGggPSBmdW5jdGlvbihwYXRoKXtcbiAgICAgICAgICAgIHJldFZhbC5wdXNoKHBhdGguc3Vic3RyKDEpKTtcbiAgICAgICAgICAgIGlmKCFvbmVPck1hbnkgfHwgb25lT3JNYW55ID09PSAnb25lJyl7XG4gICAgICAgICAgICAgICAgcmV0VmFsID0gcmV0VmFsWzBdO1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICB9O1xuICAgICAgICBzY2FuRm9yVmFsdWUob2JqLCB2YWwsIHNhdmVQYXRoKTtcbiAgICAgICAgcmV0dXJuIHJldFZhbFswXSA/IHJldFZhbCA6IHVuZGVmaW5lZDtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogRm9yIGEgZ2l2ZW4gc3BlY2lhbCBjaGFyYWN0ZXIgZ3JvdXAgKGUuZy4sIHNlcGFyYXRvcnMpIGFuZCBjaGFyYWN0ZXIgdHlwZSAoZS5nLiwgXCJwcm9wZXJ0eVwiKSxcbiAgICAgKiByZXBsYWNlIGFuIGV4aXN0aW5nIHNlcGFyYXRvciB3aXRoIGEgbmV3IGNoYXJhY3Rlci4gVGhpcyBjcmVhdGVzIGEgbmV3IHNwZWNpYWwgY2hhcmFjdGVyIGZvclxuICAgICAqIHRoYXQgcHVycG9zZSBhbndpdGhpbiB0aGUgY2hhcmFjdGVyIGdyb3VwIGFuZCByZW1vdmVzIHRoZSBvbGQgb25lLiBBbHNvIHRha2VzIGEgXCJjbG9zZXJcIiBhcmd1bWVudFxuICAgICAqIGZvciBjYXNlcyB3aGVyZSB0aGUgc3BlY2lhbCBjaGFyYWN0ZXIgaXMgYSBjb250YWluZXIgc2V0LlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtIHtPYmplY3R9IG9wdGlvbkdyb3VwIFJlZmVyZW5jZSB0byBjdXJyZW50IGNvbmZpZ3VyYXRpb24gZm9yIGEgY2VydGFpbiB0eXBlIG9mIHNwZWNpYWwgY2hhcmFjdGVyc1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjaGFyVHlwZSBUaGUgdHlwZSBvZiBzcGVjaWFsIGNoYXJhY3RlciB0byBiZSByZXBsYWNlZFxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IHNwZWNpYWwgY2hhcmFjdGVyIHN0cmluZ1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgT3B0aW9uYWw7IE5ldyBzcGVjaWFsIGNoYXJhY3RlciBjbG9zZXIgc3RyaW5nLCBvbmx5IHVzZWQgZm9yIFwiY29udGFpbmVyc1wiIGdyb3VwXG4gICAgICovXG4gICAgdmFyIHVwZGF0ZU9wdGlvbkNoYXIgPSBmdW5jdGlvbihvcHRpb25Hcm91cCwgY2hhclR5cGUsIHZhbCwgY2xvc2VyKXtcbiAgICAgICAgdmFyIG9sZFZhbCA9ICcnO1xuICAgICAgICBPYmplY3Qua2V5cyhvcHRpb25Hcm91cCkuZm9yRWFjaChmdW5jdGlvbihzdHIpeyBpZiAob3B0aW9uR3JvdXBbc3RyXS5leGVjID09PSBjaGFyVHlwZSl7IG9sZFZhbCA9IHN0cjsgfSB9KTtcblxuICAgICAgICBkZWxldGUgb3B0aW9uR3JvdXBbb2xkVmFsXTtcbiAgICAgICAgb3B0aW9uR3JvdXBbdmFsXSA9IHtleGVjOiBjaGFyVHlwZX07XG4gICAgICAgIGlmIChjbG9zZXIpeyBvcHRpb25Hcm91cFt2YWxdLmNsb3NlciA9IGNsb3NlcjsgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTZXRzIFwic2ltcGxlXCIgc3ludGF4IGluIHNwZWNpYWwgY2hhcmFjdGVyIGdyb3Vwcy4gVGhpcyBzeW50YXggb25seSBzdXBwb3J0cyBhIHNlcGFyYXRvclxuICAgICAqIGNoYXJhY3RlciBhbmQgbm8gb3RoZXIgb3BlcmF0b3JzLiBBIGN1c3RvbSBzZXBhcmF0b3IgbWF5IGJlIHByb3ZpZGVkIGFzIGFuIGFyZ3VtZW50LlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHNlcCBPcHRpb25hbDsgU2VwYXJhdG9yIHN0cmluZy4gSWYgbWlzc2luZywgdGhlIGRlZmF1bHQgc2VwYXJhdG9yIChcIi5cIikgaXMgdXNlZC5cbiAgICAgKi9cbiAgICB2YXIgc2V0U2ltcGxlT3B0aW9ucyA9IGZ1bmN0aW9uKHNlcCl7XG4gICAgICAgIHZhciBzZXBPcHRzID0ge307XG4gICAgICAgIGlmICghKHR5cGVvZiBzZXAgPT09ICRTVFJJTkcgJiYgc2VwLmxlbmd0aCA9PT0gMSkpe1xuICAgICAgICAgICAgc2VwID0gJy4nO1xuICAgICAgICB9XG4gICAgICAgIHNlcE9wdHNbc2VwXSA9IHtleGVjOiAkUFJPUEVSVFl9O1xuICAgICAgICBvcHQucHJlZml4ZXMgPSB7fTtcbiAgICAgICAgb3B0LmNvbnRhaW5lcnMgPSB7fTtcbiAgICAgICAgb3B0LnNlcGFyYXRvcnMgPSBzZXBPcHRzO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBBbHRlciBQYXRoVG9vbGtpdCBjb25maWd1cmF0aW9uLiBUYWtlcyBhbiBvcHRpb25zIGhhc2ggd2hpY2ggbWF5IGluY2x1ZGVcbiAgICAgKiBtdWx0aXBsZSBzZXR0aW5ncyB0byBjaGFuZ2UgYXQgb25jZS4gSWYgdGhlIHBhdGggc3ludGF4IGlzIGNoYW5nZWQgYnlcbiAgICAgKiBjaGFuZ2luZyBzcGVjaWFsIGNoYXJhY3RlcnMsIHRoZSBjYWNoZSBpcyB3aXBlZC4gRWFjaCBvcHRpb24gZ3JvdXAgaXNcbiAgICAgKiBSRVBMQUNFRCBieSB0aGUgbmV3IG9wdGlvbiBncm91cCBwYXNzZWQgaW4uIElmIGFuIG9wdGlvbiBncm91cCBpcyBub3RcbiAgICAgKiBpbmNsdWRlZCBpbiB0aGUgb3B0aW9ucyBoYXNoLCBpdCBpcyBub3QgY2hhbmdlZC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtPYmplY3R9IG9wdGlvbnMgT3B0aW9uIGhhc2guIEZvciBzYW1wbGUgaW5wdXQsIHNlZSBgc2V0RGVmYXVsdE9wdGlvbnNgIGFib3ZlLlxuICAgICAqL1xuICAgIF90aGlzLnNldE9wdGlvbnMgPSBmdW5jdGlvbihvcHRpb25zKXtcbiAgICAgICAgaWYgKG9wdGlvbnMucHJlZml4ZXMpe1xuICAgICAgICAgICAgb3B0LnByZWZpeGVzID0gb3B0aW9ucy5wcmVmaXhlcztcbiAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG9wdGlvbnMuc2VwYXJhdG9ycyl7XG4gICAgICAgICAgICBvcHQuc2VwYXJhdG9ycyA9IG9wdGlvbnMuc2VwYXJhdG9ycztcbiAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG9wdGlvbnMuY29udGFpbmVycyl7XG4gICAgICAgICAgICBvcHQuY29udGFpbmVycyA9IG9wdGlvbnMuY29udGFpbmVycztcbiAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHR5cGVvZiBvcHRpb25zLmNhY2hlICE9PSAkVU5ERUZJTkVEKXtcbiAgICAgICAgICAgIG9wdC51c2VDYWNoZSA9ICEhb3B0aW9ucy5jYWNoZTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodHlwZW9mIG9wdGlvbnMuc2ltcGxlICE9PSAkVU5ERUZJTkVEKXtcbiAgICAgICAgICAgIHZhciB0ZW1wQ2FjaGUgPSBvcHQudXNlQ2FjaGU7IC8vIHByZXNlcnZlIHRoZXNlIHR3byBvcHRpb25zIGFmdGVyIFwic2V0RGVmYXVsdE9wdGlvbnNcIlxuICAgICAgICAgICAgdmFyIHRlbXBGb3JjZSA9IG9wdC5mb3JjZTtcbiAgICAgICAgICAgIFxuICAgICAgICAgICAgb3B0LnNpbXBsZSA9IHRydXRoaWZ5KG9wdGlvbnMuc2ltcGxlKTtcbiAgICAgICAgICAgIGlmIChvcHQuc2ltcGxlKXtcbiAgICAgICAgICAgICAgICBzZXRTaW1wbGVPcHRpb25zKCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBzZXREZWZhdWx0T3B0aW9ucygpO1xuICAgICAgICAgICAgICAgIG9wdC51c2VDYWNoZSA9IHRlbXBDYWNoZTtcbiAgICAgICAgICAgICAgICBvcHQuZm9yY2UgPSB0ZW1wRm9yY2U7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICB9XG4gICAgICAgIGlmICh0eXBlb2Ygb3B0aW9ucy5mb3JjZSAhPT0gJFVOREVGSU5FRCl7XG4gICAgICAgICAgICBvcHQuZm9yY2UgPSB0cnV0aGlmeShvcHRpb25zLmZvcmNlKTtcbiAgICAgICAgfVxuICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTZXRzIHVzZSBvZiBrZXlwYXRoIGNhY2hlIHRvIGVuYWJsZWQgb3IgZGlzYWJsZWQsIGRlcGVuZGluZyBvbiBpbnB1dCB2YWx1ZS5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IHZhbCBWYWx1ZSB3aGljaCB3aWxsIGJlIGludGVycHJldGVkIGFzIGEgYm9vbGVhbiB1c2luZyBgdHJ1dGhpZnlgLiBcInRydWVcIiB3aWxsIGVuYWJsZSBjYWNoZTsgXCJmYWxzZVwiIHdpbGwgZGlzYWJsZS5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDYWNoZSA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIG9wdC51c2VDYWNoZSA9IHRydXRoaWZ5KHZhbCk7XG4gICAgfTtcbiAgICAvKipcbiAgICAgKiBFbmFibGVzIHVzZSBvZiBrZXlwYXRoIGNhY2hlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDYWNoZU9uID0gZnVuY3Rpb24oKXtcbiAgICAgICAgb3B0LnVzZUNhY2hlID0gdHJ1ZTtcbiAgICB9O1xuICAgIC8qKlxuICAgICAqIERpc2FibGVzIHVzZSBvZiBrZXlwYXRoIGNhY2hlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDYWNoZU9mZiA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIG9wdC51c2VDYWNoZSA9IGZhbHNlO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTZXRzIFwiZm9yY2VcIiBvcHRpb24gd2hlbiBzZXR0aW5nIHZhbHVlcyBpbiBhbiBvYmplY3QsIGRlcGVuZGluZyBvbiBpbnB1dCB2YWx1ZS5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IHZhbCBWYWx1ZSB3aGljaCB3aWxsIGJlIGludGVycHJldGVkIGFzIGEgYm9vbGVhbiB1c2luZyBgdHJ1dGhpZnlgLiBcInRydWVcIiBlbmFibGVzIFwiZm9yY2VcIjsgXCJmYWxzZVwiIGRpc2FibGVzLlxuICAgICAqL1xuICAgIF90aGlzLnNldEZvcmNlID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgb3B0LmZvcmNlID0gdHJ1dGhpZnkodmFsKTtcbiAgICB9O1xuICAgIC8qKlxuICAgICAqIEVuYWJsZXMgXCJmb3JjZVwiIG9wdGlvbiB3aGVuIHNldHRpbmcgdmFsdWVzIGluIGFuIG9iamVjdC5cbiAgICAgKiBAcHVibGljXG4gICAgICovXG4gICAgX3RoaXMuc2V0Rm9yY2VPbiA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIG9wdC5mb3JjZSA9IHRydWU7XG4gICAgfTtcbiAgICAvKipcbiAgICAgKiBEaXNhYmxlcyBcImZvcmNlXCIgb3B0aW9uIHdoZW4gc2V0dGluZyB2YWx1ZXMgaW4gYW4gb2JqZWN0LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKi9cbiAgICBfdGhpcy5zZXRGb3JjZU9mZiA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIG9wdC5mb3JjZSA9IGZhbHNlO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTaG9ydGN1dCBmdW5jdGlvbiB0byBhbHRlciBQYXRoVG9vbGtpdCBzeW50YXggdG8gYSBcInNpbXBsZVwiIG1vZGUgdGhhdCBvbmx5IHVzZXNcbiAgICAgKiBzZXBhcmF0b3JzIGFuZCBubyBvdGhlciBvcGVyYXRvcnMuIFwiU2ltcGxlXCIgbW9kZSBpcyBlbmFibGVkIG9yIGRpc2FibGVkIGFjY29yZGluZ1xuICAgICAqIHRvIHRoZSBmaXJzdCBhcmd1bWVudCBhbmQgdGhlIHNlcGFyYXRvciBtYXkgYmUgY3VzdG9taXplZCB3aXRoIHRoZSBzZWNvbmRcbiAgICAgKiBhcmd1bWVudCB3aGVuIGVuYWJsaW5nIFwic2ltcGxlXCIgbW9kZS5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IHZhbCBWYWx1ZSB3aGljaCB3aWxsIGJlIGludGVycHJldGVkIGFzIGEgYm9vbGVhbiB1c2luZyBgdHJ1dGhpZnlgLiBcInRydWVcIiBlbmFibGVzIFwic2ltcGxlXCIgbW9kZTsgXCJmYWxzZVwiIGRpc2FibGVzLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBzZXAgU2VwYXJhdG9yIHN0cmluZyB0byB1c2UgaW4gcGxhY2Ugb2YgdGhlIGRlZmF1bHQgXCIuXCJcbiAgICAgKi9cbiAgICBfdGhpcy5zZXRTaW1wbGUgPSBmdW5jdGlvbih2YWwsIHNlcCl7XG4gICAgICAgIHZhciB0ZW1wQ2FjaGUgPSBvcHQudXNlQ2FjaGU7IC8vIHByZXNlcnZlIHRoZXNlIHR3byBvcHRpb25zIGFmdGVyIFwic2V0RGVmYXVsdE9wdGlvbnNcIlxuICAgICAgICB2YXIgdGVtcEZvcmNlID0gb3B0LmZvcmNlO1xuICAgICAgICBvcHQuc2ltcGxlID0gdHJ1dGhpZnkodmFsKTtcbiAgICAgICAgaWYgKG9wdC5zaW1wbGUpe1xuICAgICAgICAgICAgc2V0U2ltcGxlT3B0aW9ucyhzZXApO1xuICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHNldERlZmF1bHRPcHRpb25zKCk7XG4gICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgb3B0LnVzZUNhY2hlID0gdGVtcENhY2hlO1xuICAgICAgICAgICAgb3B0LmZvcmNlID0gdGVtcEZvcmNlO1xuICAgICAgICB9XG4gICAgICAgIGNhY2hlID0ge307XG4gICAgfTtcbiAgICBcbiAgICAvKipcbiAgICAgKiBFbmFibGVzIFwic2ltcGxlXCIgbW9kZVxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc2VwIFNlcGFyYXRvciBzdHJpbmcgdG8gdXNlIGluIHBsYWNlIG9mIHRoZSBkZWZhdWx0IFwiLlwiXG4gICAgICogQHNlZSBzZXRTaW1wbGVcbiAgICAgKi9cbiAgICBfdGhpcy5zZXRTaW1wbGVPbiA9IGZ1bmN0aW9uKHNlcCl7XG4gICAgICAgIG9wdC5zaW1wbGUgPSB0cnVlO1xuICAgICAgICBzZXRTaW1wbGVPcHRpb25zKHNlcCk7XG4gICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgIGNhY2hlID0ge307XG4gICAgfTtcbiAgICBcbiAgICAvKipcbiAgICAgKiBEaXNhYmxlcyBcInNpbXBsZVwiIG1vZGUsIHJlc3RvcmVzIGRlZmF1bHQgUGF0aFRvb2xraXQgc3ludGF4XG4gICAgICogQHB1YmxpY1xuICAgICAqIEBzZWUgc2V0U2ltcGxlXG4gICAgICogQHNlZSBzZXREZWZhdWx0T3B0aW9uc1xuICAgICAqL1xuICAgIF90aGlzLnNldFNpbXBsZU9mZiA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIHZhciB0ZW1wQ2FjaGUgPSBvcHQudXNlQ2FjaGU7IC8vIHByZXNlcnZlIHRoZXNlIHR3byBvcHRpb25zIGFmdGVyIFwic2V0RGVmYXVsdE9wdGlvbnNcIlxuICAgICAgICB2YXIgdGVtcEZvcmNlID0gb3B0LmZvcmNlO1xuICAgICAgICBvcHQuc2ltcGxlID0gZmFsc2U7XG4gICAgICAgIHNldERlZmF1bHRPcHRpb25zKCk7XG4gICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgIG9wdC51c2VDYWNoZSA9IHRlbXBDYWNoZTtcbiAgICAgICAgb3B0LmZvcmNlID0gdGVtcEZvcmNlO1xuICAgICAgICBjYWNoZSA9IHt9O1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIHByb3BlcnR5IHNlcGFyYXRvciBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGlzIG9wZXJhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRTZXBhcmF0b3JQcm9wZXJ0eSA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuc2VwYXJhdG9yc1t2YWxdLmV4ZWMgPT09ICRQUk9QRVJUWSkgJiYgIShvcHQucHJlZml4ZXNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuc2VwYXJhdG9ycywgJFBST1BFUlRZLCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0U2VwYXJhdG9yUHJvcGVydHkgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRTZXBhcmF0b3JQcm9wZXJ0eSAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIGNvbGxlY3Rpb24gc2VwYXJhdG9yIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoaXMgb3BlcmF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLnNldFNlcGFyYXRvckNvbGxlY3Rpb24gPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnNlcGFyYXRvcnNbdmFsXS5leGVjID09PSAkQ09MTEVDVElPTikgJiYgIShvcHQucHJlZml4ZXNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuc2VwYXJhdG9ycywgJENPTExFQ1RJT04sIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRTZXBhcmF0b3JDb2xsZWN0aW9uIC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0U2VwYXJhdG9yQ29sbGVjdGlvbiAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIHBhcmVudCBwcmVmaXggaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0UHJlZml4UGFyZW50ID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQucHJlZml4ZXNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXS5leGVjID09PSAkUEFSRU5UKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LnByZWZpeGVzLCAkUEFSRU5ULCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4UGFyZW50IC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4UGFyZW50IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgcm9vdCBwcmVmaXggaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0UHJlZml4Um9vdCA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnByZWZpeGVzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0uZXhlYyA9PT0gJFJPT1QpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQucHJlZml4ZXMsICRST09ULCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4Um9vdCAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeFJvb3QgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBwbGFjZWhvbGRlciBwcmVmaXggaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0UHJlZml4UGxhY2Vob2xkZXIgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdLmV4ZWMgPT09ICRQTEFDRUhPTERFUikgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5wcmVmaXhlcywgJFBMQUNFSE9MREVSLCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4UGxhY2Vob2xkZXIgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhQbGFjZWhvbGRlciAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIGNvbnRleHQgcHJlZml4IGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoaXMgb3BlcmF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLnNldFByZWZpeENvbnRleHQgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdLmV4ZWMgPT09ICRDT05URVhUKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LnByZWZpeGVzLCAkQ09OVEVYVCwgdmFsKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeENvbnRleHQgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhDb250ZXh0IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgcHJvcGVydHkgY29udGFpbmVyIGNoYXJhY3RlcnMgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBvcGVuZXIuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNsb3NlciBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBjbG9zZXIuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q29udGFpbmVyUHJvcGVydHkgPSBmdW5jdGlvbih2YWwsIGNsb3Nlcil7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEgJiYgdHlwZW9mIGNsb3NlciA9PT0gJFNUUklORyAmJiBjbG9zZXIubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5jb250YWluZXJzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXS5leGVjID09PSAkUFJPUEVSVFkpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LmNvbnRhaW5lcnMsICRQUk9QRVJUWSwgdmFsLCBjbG9zZXIpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyUHJvcGVydHkgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJQcm9wZXJ0eSAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIHNpbmdsZSBxdW90ZSBjb250YWluZXIgY2hhcmFjdGVycyBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIG9wZW5lci5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gY2xvc2VyIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIGNsb3Nlci5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDb250YWluZXJTaW5nbGVxdW90ZSA9IGZ1bmN0aW9uKHZhbCwgY2xvc2VyKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSAmJiB0eXBlb2YgY2xvc2VyID09PSAkU1RSSU5HICYmIGNsb3Nlci5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LmNvbnRhaW5lcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdLmV4ZWMgPT09ICRTSU5HTEVRVU9URSkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuY29udGFpbmVycywgJFNJTkdMRVFVT1RFLCB2YWwsIGNsb3Nlcik7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJTaW5nbGVxdW90ZSAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lclNpbmdsZXF1b3RlIC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgZG91YmxlIHF1b3RlIGNvbnRhaW5lciBjaGFyYWN0ZXJzIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgb3BlbmVyLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgY2xvc2VyLlxuICAgICAqL1xuICAgIF90aGlzLnNldENvbnRhaW5lckRvdWJsZXF1b3RlID0gZnVuY3Rpb24odmFsLCBjbG9zZXIpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxICYmIHR5cGVvZiBjbG9zZXIgPT09ICRTVFJJTkcgJiYgY2xvc2VyLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQuY29udGFpbmVyc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0uZXhlYyA9PT0gJERPVUJMRVFVT1RFKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5jb250YWluZXJzLCAkRE9VQkxFUVVPVEUsIHZhbCwgY2xvc2VyKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lckRvdWJsZXF1b3RlIC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyRG91YmxlcXVvdGUgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBmdW5jdGlvbiBjYWxsIGNvbnRhaW5lciBjaGFyYWN0ZXJzIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgb3BlbmVyLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgY2xvc2VyLlxuICAgICAqL1xuICAgIF90aGlzLnNldENvbnRhaW5lckNhbGwgPSBmdW5jdGlvbih2YWwsIGNsb3Nlcil7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEgJiYgdHlwZW9mIGNsb3NlciA9PT0gJFNUUklORyAmJiBjbG9zZXIubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5jb250YWluZXJzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXS5leGVjID09PSAkQ0FMTCkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuY29udGFpbmVycywgJENBTEwsIHZhbCwgY2xvc2VyKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lckNhbGwgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJDYWxsIC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgZXZhbCBwcm9wZXJ0eSBjb250YWluZXIgY2hhcmFjdGVycyBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIG9wZW5lci5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gY2xvc2VyIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIGNsb3Nlci5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDb250YWluZXJFdmFsUHJvcGVydHkgPSBmdW5jdGlvbih2YWwsIGNsb3Nlcil7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEgJiYgdHlwZW9mIGNsb3NlciA9PT0gJFNUUklORyAmJiBjbG9zZXIubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5jb250YWluZXJzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXS5leGVjID09PSAkRVZBTFBST1BFUlRZKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5jb250YWluZXJzLCAkRVZBTFBST1BFUlRZLCB2YWwsIGNsb3Nlcik7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJFdmFsUHJvcGVydHkgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJQcm9wZXJ0eSAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBSZXNldCBhbGwgUGF0aFRvb2xraXQgb3B0aW9ucyB0byB0aGVpciBkZWZhdWx0IHZhbHVlcy5cbiAgICAgKiBAcHVibGljXG4gICAgICovXG4gICAgX3RoaXMucmVzZXRPcHRpb25zID0gZnVuY3Rpb24oKXtcbiAgICAgICAgc2V0RGVmYXVsdE9wdGlvbnMoKTtcbiAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgY2FjaGUgPSB7fTtcbiAgICB9O1xuXG4gICAgLy8gSW5pdGlhbGl6ZSBvcHRpb24gc2V0XG4gICAgc2V0RGVmYXVsdE9wdGlvbnMoKTtcbiAgICB1cGRhdGVSZWdFeCgpO1xuXG4gICAgLy8gQXBwbHkgY3VzdG9tIG9wdGlvbnMgaWYgcHJvdmlkZWQgYXMgYXJndW1lbnQgdG8gY29uc3RydWN0b3JcbiAgICBvcHRpb25zICYmIF90aGlzLnNldE9wdGlvbnMob3B0aW9ucyk7XG5cbn07XG5cbmV4cG9ydCBkZWZhdWx0IFBhdGhUb29sa2l0O1xuIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiI7Ozs7OztBQUFBOzs7Ozs7O0FBT0EsQUFFQTtBQUNBLElBQUksS0FBSyxHQUFHLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxPQUFPLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDOzs7QUFHdkMsSUFBSSxTQUFTLE9BQU8sR0FBRztJQUNuQixVQUFVLE1BQU0sV0FBVztJQUMzQixPQUFPLFNBQVMsUUFBUTtJQUN4QixPQUFPLFNBQVMsUUFBUTtJQUN4QixLQUFLLFdBQVcsTUFBTTtJQUN0QixZQUFZLElBQUksYUFBYTtJQUM3QixRQUFRLFFBQVEsU0FBUztJQUN6QixRQUFRLFFB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