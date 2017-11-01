(function (global, factory) {
    typeof exports === 'object' && typeof module !== 'undefined' ? module.exports = factory() :
    typeof define === 'function' && define.amd ? define(factory) :
    (global.PathToolkit = factory());
}(this, (function () { 'use strict';

/**
 * @fileOverview PathToolkit evaluates string paths as property/index sequences within objects and arrays
 * @author Aaron Brown
 * @version 1.1.0
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
 * Inspect input value and determine whether it is an Integer or not.
 * Values of undefined and null will return "false".
 * @private
 * @param  {String}  val String to examine
 * @return {Boolean}     True if thing consists of at least one digit and only of digits (no . or ,)
 */
var digitsRegex = /^\d+$/;
var isDigits = function(val){
    return digitsRegex.test(val);
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
                            if (mods.has){
                                recur = {'w': subpath, 'mods': mods, 'doEach': doEach};
                                // tokens.push(word);
                                mods = {};
                                simplePath &= false;
                            }
                            else {
                                recur = subpath;
                                simplePath &= true;
                            }
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
                            if (mods.has){
                                recur = {'w': subpath, 'mods': mods, 'doEach': doEach};
                                // tokens.push(word);
                                mods = {};
                                simplePath &= false;
                            }
                            else {
                                recur = subpath;
                                simplePath &= true;
                            }
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
                            // tokens.push(word);
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
            word = {'w': word, 'mods': word.mods || mods, 'doEach': doEach};
            mods = {};
            simplePath &= false;
        }
        else if (word && mods.has){
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

console.log('Tokens:', JSON.stringify(tokens,undefined,2));
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
                                if (isDigits(wordCopy)){
                                    placeInt = wordCopy - 1;
                                    if (args[placeInt] === UNDEF){ return undefined; }
                                    // Force args[placeInt] to String, won't atwordCopyt to process
                                    // arg of type function, array, or plain object
                                    ret.push(args[placeInt]);
                                }
                                else {
                                    ret = wordCopy;
                                }
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
                            if (isDigits(wordCopy)){
                                placeInt = wordCopy - 1;
                                if (args[placeInt] === UNDEF){ return undefined; }
                                // Force args[placeInt] to String, won't atwordCopyt to process
                                // arg of type function, array, or plain object
                                ret = args[placeInt];
                            } else {
                                ret = wordCopy;
                            }
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

//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjpudWxsLCJzb3VyY2VzIjpbIi9ob21lL3VidW50dS93b3Jrc3BhY2Uvc3JjL3BhdGgtdG9vbGtpdC5qcyJdLCJzb3VyY2VzQ29udGVudCI6WyIvKipcbiAqIEBmaWxlT3ZlcnZpZXcgUGF0aFRvb2xraXQgZXZhbHVhdGVzIHN0cmluZyBwYXRocyBhcyBwcm9wZXJ0eS9pbmRleCBzZXF1ZW5jZXMgd2l0aGluIG9iamVjdHMgYW5kIGFycmF5c1xuICogQGF1dGhvciBBYXJvbiBCcm93blxuICogQHZlcnNpb24gMS4xLjBcbiAqL1xuXG4vLyBQYXJzaW5nLCB0b2tlbmluemluZywgZXRjXG4ndXNlIHN0cmljdCc7XG5cbi8vIFNvbWUgY29uc3RhbnRzIGZvciBjb252ZW5pZW5jZVxudmFyIFVOREVGID0gKGZ1bmN0aW9uKHUpe3JldHVybiB1O30pKCk7XG5cbi8vIFN0YXRpYyBzdHJpbmdzLCBhc3NpZ25lZCB0byBhaWQgY29kZSBtaW5pZmljYXRpb25cbnZhciAkV0lMRENBUkQgICAgID0gJyonLFxuICAgICRVTkRFRklORUQgICAgPSAndW5kZWZpbmVkJyxcbiAgICAkU1RSSU5HICAgICAgID0gJ3N0cmluZycsXG4gICAgJFBBUkVOVCAgICAgICA9ICdwYXJlbnQnLFxuICAgICRST09UICAgICAgICAgPSAncm9vdCcsXG4gICAgJFBMQUNFSE9MREVSICA9ICdwbGFjZWhvbGRlcicsXG4gICAgJENPTlRFWFQgICAgICA9ICdjb250ZXh0JyxcbiAgICAkUFJPUEVSVFkgICAgID0gJ3Byb3BlcnR5JyxcbiAgICAkQ09MTEVDVElPTiAgID0gJ2NvbGxlY3Rpb24nLFxuICAgICRFQUNIICAgICAgICAgPSAnZWFjaCcsXG4gICAgJFNJTkdMRVFVT1RFICA9ICdzaW5nbGVxdW90ZScsXG4gICAgJERPVUJMRVFVT1RFICA9ICdkb3VibGVxdW90ZScsXG4gICAgJENBTEwgICAgICAgICA9ICdjYWxsJyxcbiAgICAkRVZBTFBST1BFUlRZID0gJ2V2YWxQcm9wZXJ0eSc7XG4gICAgXG4vKipcbiAqIFRlc3RzIHdoZXRoZXIgYSB3aWxkY2FyZCB0ZW1wbGF0ZXMgbWF0Y2hlcyBhIGdpdmVuIHN0cmluZy5cbiAqIGBgYGphdmFzY3JpcHRcbiAqIHZhciBzdHIgPSAnYWFhYmJieHh4Y2NjZGRkJztcbiAqIHdpbGRDYXJkTWF0Y2goJ2FhYWJiYnh4eGNjY2RkZCcpOyAvLyB0cnVlXG4gKiB3aWxkQ2FyZE1hdGNoKCcqJywgc3RyKTsgLy8gdHJ1ZVxuICogd2lsZENhcmRNYXRjaCgnKicsICcnKTsgLy8gdHJ1ZVxuICogd2lsZENhcmRNYXRjaCgnYSonLCBzdHIpOyAvLyB0cnVlXG4gKiB3aWxkQ2FyZE1hdGNoKCdhYSpkZGQnLCBzdHIpOyAvLyB0cnVlXG4gKiB3aWxkQ2FyZE1hdGNoKCcqZCcsIHN0cik7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJyphJywgc3RyKTsgLy8gZmFsc2VcbiAqIHdpbGRDYXJkTWF0Y2goJ2EqeicsIHN0cik7IC8vIGZhbHNlXG4gKiBgYGBcbiAqIEBwcml2YXRlXG4gKiBAcGFyYW0gIHtTdHJpbmd9IHRlbXBsYXRlIFdpbGRjYXJkIHBhdHRlcm5cbiAqIEBwYXJhbSAge1N0cmluZ30gc3RyICAgICAgU3RyaW5nIHRvIG1hdGNoIGFnYWluc3Qgd2lsZGNhcmQgcGF0dGVyblxuICogQHJldHVybiB7Qm9vbGVhbn0gICAgICAgICAgVHJ1ZSBpZiBwYXR0ZXJuIG1hdGNoZXMgc3RyaW5nOyBGYWxzZSBpZiBub3RcbiAqL1xudmFyIHdpbGRDYXJkTWF0Y2ggPSBmdW5jdGlvbih0ZW1wbGF0ZSwgc3RyKXtcbiAgICB2YXIgcG9zID0gdGVtcGxhdGUuaW5kZXhPZigkV0lMRENBUkQpLFxuICAgICAgICBwYXJ0cyA9IHRlbXBsYXRlLnNwbGl0KCRXSUxEQ0FSRCwgMiksXG4gICAgICAgIG1hdGNoID0gdHJ1ZTtcbiAgICBpZiAocGFydHNbMF0pe1xuICAgICAgICAvLyBJZiBubyB3aWxkY2FyZCBwcmVzZW50LCByZXR1cm4gc2ltcGxlIHN0cmluZyBjb21wYXJpc29uXG4gICAgICAgIGlmIChwYXJ0c1swXSA9PT0gdGVtcGxhdGUpe1xuICAgICAgICAgICAgcmV0dXJuIHBhcnRzWzBdID09PSBzdHI7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBtYXRjaCA9IG1hdGNoICYmIHN0ci5zdWJzdHIoMCwgcGFydHNbMF0ubGVuZ3RoKSA9PT0gcGFydHNbMF07XG4gICAgICAgIH1cbiAgICB9XG4gICAgaWYgKHBhcnRzWzFdKXtcbiAgICAgICAgbWF0Y2ggPSBtYXRjaCAmJiBzdHIuc3Vic3RyKC0xKnBhcnRzWzFdLmxlbmd0aCkgPT09IHBhcnRzWzFdO1xuICAgIH1cbiAgICByZXR1cm4gbWF0Y2g7XG59O1xuXG4vKipcbiAqIEluc3BlY3QgaW5wdXQgdmFsdWUgYW5kIGRldGVybWluZSB3aGV0aGVyIGl0IGlzIGFuIE9iamVjdCBvciBub3QuXG4gKiBWYWx1ZXMgb2YgdW5kZWZpbmVkIGFuZCBudWxsIHdpbGwgcmV0dXJuIFwiZmFsc2VcIiwgb3RoZXJ3aXNlXG4gKiBtdXN0IGJlIG9mIHR5cGUgXCJvYmplY3RcIiBvciBcImZ1bmN0aW9uXCIuXG4gKiBAcHJpdmF0ZVxuICogQHBhcmFtICB7T2JqZWN0fSAgdmFsIFRoaW5nIHRvIGV4YW1pbmUsIG1heSBiZSBvZiBhbnkgdHlwZVxuICogQHJldHVybiB7Qm9vbGVhbn0gICAgIFRydWUgaWYgdGhpbmcgaXMgb2YgdHlwZSBcIm9iamVjdFwiIG9yIFwiZnVuY3Rpb25cIlxuICovXG52YXIgaXNPYmplY3QgPSBmdW5jdGlvbih2YWwpe1xuICAgIGlmICh0eXBlb2YgdmFsID09PSAkVU5ERUZJTkVEIHx8IHZhbCA9PT0gbnVsbCkgeyByZXR1cm4gZmFsc2U7fVxuICAgIHJldHVybiAoICh0eXBlb2YgdmFsID09PSAnZnVuY3Rpb24nKSB8fCAodHlwZW9mIHZhbCA9PT0gJ29iamVjdCcpICk7XG59O1xuXG4vKipcbiAqIEluc3BlY3QgaW5wdXQgdmFsdWUgYW5kIGRldGVybWluZSB3aGV0aGVyIGl0IGlzIGFuIEludGVnZXIgb3Igbm90LlxuICogVmFsdWVzIG9mIHVuZGVmaW5lZCBhbmQgbnVsbCB3aWxsIHJldHVybiBcImZhbHNlXCIuXG4gKiBAcHJpdmF0ZVxuICogQHBhcmFtICB7U3RyaW5nfSAgdmFsIFN0cmluZyB0byBleGFtaW5lXG4gKiBAcmV0dXJuIHtCb29sZWFufSAgICAgVHJ1ZSBpZiB0aGluZyBjb25zaXN0cyBvZiBhdCBsZWFzdCBvbmUgZGlnaXQgYW5kIG9ubHkgb2YgZGlnaXRzIChubyAuIG9yICwpXG4gKi9cbnZhciBkaWdpdHNSZWdleCA9IC9eXFxkKyQvO1xudmFyIGlzRGlnaXRzID0gZnVuY3Rpb24odmFsKXtcbiAgICByZXR1cm4gZGlnaXRzUmVnZXgudGVzdCh2YWwpO1xufTtcblxuLyoqXG4gKiBDb252ZXJ0IHZhcmlvdXMgdmFsdWVzIHRvIHRydWUgYm9vbGVhbiBgdHJ1ZWAgb3IgYGZhbHNlYC5cbiAqIEZvciBub24tc3RyaW5nIHZhbHVlcywgdGhlIG5hdGl2ZSBqYXZhc2NyaXB0IGlkZWEgb2YgXCJ0cnVlXCIgd2lsbCBhcHBseS5cbiAqIEZvciBzdHJpbmcgdmFsdWVzLCB0aGUgd29yZHMgXCJ0cnVlXCIsIFwieWVzXCIsIGFuZCBcIm9uXCIgd2lsbCBhbGwgcmV0dXJuIGB0cnVlYC5cbiAqIEFsbCBvdGhlciBzdHJpbmdzIHJldHVybiBgZmFsc2VgLiBUaGUgc3RyaW5nIG1hdGNoIGlzIG5vbi1jYXNlLXNlbnNpdGl2ZS5cbiAqIEBwcml2YXRlXG4gKi9cbnZhciB0cnV0aGlmeSA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgdmFyIHY7XG4gICAgaWYgKHR5cGVvZiB2YWwgIT09ICRTVFJJTkcpe1xuICAgICAgICByZXR1cm4gdmFsICYmIHRydWU7IC8vIFVzZSBuYXRpdmUgamF2YXNjcmlwdCBub3Rpb24gb2YgXCJ0cnV0aHlcIlxuICAgIH1cbiAgICB2ID0gdmFsLnRvVXBwZXJDYXNlKCk7XG4gICAgaWYgKHYgPT09ICdUUlVFJyB8fCB2ID09PSAnWUVTJyB8fCB2ID09PSAnT04nKXtcbiAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmYWxzZTtcbn07XG5cbi8qKlxuICogVXNpbmcgcHJvdmlkZWQgcXVvdGUgY2hhcmFjdGVyIGFzIHByZWZpeCBhbmQgc3VmZml4LCBlc2NhcGUgYW55IGluc3RhbmNlc1xuICogb2YgdGhlIHF1b3RlIGNoYXJhY3RlciB3aXRoaW4gdGhlIHN0cmluZyBhbmQgcmV0dXJuIHF1b3RlK3N0cmluZytxdW90ZS5cbiAqIFRoZSBjaGFyYWN0ZXIgZGVmaW5lZCBhcyBcInNpbmdsZXF1b3RlXCIgbWF5IGJlIGFsdGVyZWQgYnkgY3VzdG9tIG9wdGlvbnMsXG4gKiBzbyBhIGdlbmVyYWwtcHVycG9zZSBmdW5jdGlvbiBpcyBuZWVkZWQgdG8gcXVvdGUgcGF0aCBzZWdtZW50cyBjb3JyZWN0bHkuXG4gKiBAcHJpdmF0ZVxuICogQHBhcmFtICB7U3RyaW5nfSBxICAgU2luZ2xlLWNoYXJhY3RlciBzdHJpbmcgdG8gdXNlIGFzIHF1b3RlIGNoYXJhY3RlclxuICogQHBhcmFtICB7U3RyaW5nfSBzdHIgU3RyaW5nIHRvIGJlIHF1b3RlZC5cbiAqIEByZXR1cm4ge1N0cmluZ30gICAgIE9yaWdpbmFsIHN0cmluZywgc3Vycm91bmRlZCBieSB0aGUgcXVvdGUgY2hhcmFjdGVyLCBwb3NzaWJseSBtb2RpZmllZCBpbnRlcm5hbGx5IGlmIHRoZSBxdW90ZSBjaGFyYWN0ZXIgZXhpc3RzIHdpdGhpbiB0aGUgc3RyaW5nLlxuICovXG52YXIgcXVvdGVTdHJpbmcgPSBmdW5jdGlvbihxLCBzdHIpe1xuICAgIHZhciBxUmVnRXggPSBuZXcgUmVnRXhwKHEsICdnJyk7XG4gICAgcmV0dXJuIHEgKyBzdHIucmVwbGFjZShxUmVnRXgsICdcXFxcJyArIHEpICsgcTtcbn07XG5cbi8qKlxuICogUGF0aFRvb2xraXQgYmFzZSBvYmplY3QuIEluY2x1ZGVzIGFsbCBpbnN0YW5jZS1zcGVjaWZpYyBkYXRhIChvcHRpb25zLCBjYWNoZSlcbiAqIGFzIGxvY2FsIHZhcmlhYmxlcy4gTWF5IGJlIHBhc3NlZCBhbiBvcHRpb25zIGhhc2ggdG8gcHJlLWNvbmZpZ3VyZSB0aGVcbiAqIGluc3RhbmNlIHByaW9yIHRvIHVzZS5cbiAqIEBjb25zdHJ1Y3RvclxuICogQHByb3BlcnR5IHtPYmplY3R9IG9wdGlvbnMgT3B0aW9uYWwuIENvbGxlY3Rpb24gb2YgY29uZmlndXJhdGlvbiBzZXR0aW5ncyBmb3IgdGhpcyBpbnN0YW5jZSBvZiBQYXRoVG9vbGtpdC4gU2VlIGBzZXRPcHRpb25zYCBmdW5jdGlvbiBiZWxvdyBmb3IgZGV0YWlsZWQgZG9jdW1lbnRhdGlvbi5cbiAqL1xudmFyIFBhdGhUb29sa2l0ID0gZnVuY3Rpb24ob3B0aW9ucyl7XG4gICAgdmFyIF90aGlzID0gdGhpcyxcbiAgICAgICAgY2FjaGUgPSB7fSxcbiAgICAgICAgb3B0ID0ge30sXG4gICAgICAgIHByZWZpeExpc3QsIHNlcGFyYXRvckxpc3QsIGNvbnRhaW5lckxpc3QsIGNvbnRhaW5lckNsb3NlTGlzdCxcbiAgICAgICAgcHJvcGVydHlTZXBhcmF0b3IsXG4gICAgICAgIHNpbmdsZXF1b3RlLCBkb3VibGVxdW90ZSxcbiAgICAgICAgc2ltcGxlUGF0aENoYXJzLCBzaW1wbGVQYXRoUmVnRXgsXG4gICAgICAgIGFsbFNwZWNpYWxzLCBhbGxTcGVjaWFsc1JlZ0V4LFxuICAgICAgICBlc2NhcGVkTm9uU3BlY2lhbHNSZWdFeCxcbiAgICAgICAgZXNjYXBlZFF1b3RlcyxcbiAgICAgICAgd2lsZGNhcmRSZWdFeDtcblxuICAgIC8qKlxuICAgICAqIFNldmVyYWwgcmVndWxhciBleHByZXNzaW9ucyBhcmUgcHJlLWNvbXBpbGVkIGZvciB1c2UgaW4gcGF0aCBpbnRlcnByZXRhdGlvbi5cbiAgICAgKiBUaGVzZSBleHByZXNzaW9ucyBhcmUgYnVpbHQgZnJvbSB0aGUgY3VycmVudCBzeW50YXggY29uZmlndXJhdGlvbiwgc28gdGhleVxuICAgICAqIG11c3QgYmUgcmUtYnVpbHQgZXZlcnkgdGltZSB0aGUgc3ludGF4IGNoYW5nZXMuXG4gICAgICogQHByaXZhdGVcbiAgICAgKi9cbiAgICB2YXIgdXBkYXRlUmVnRXggPSBmdW5jdGlvbigpe1xuICAgICAgICAvLyBMaXN0cyBvZiBzcGVjaWFsIGNoYXJhY3RlcnMgZm9yIHVzZSBpbiByZWd1bGFyIGV4cHJlc3Npb25zXG4gICAgICAgIHByZWZpeExpc3QgPSBPYmplY3Qua2V5cyhvcHQucHJlZml4ZXMpO1xuICAgICAgICBzZXBhcmF0b3JMaXN0ID0gT2JqZWN0LmtleXMob3B0LnNlcGFyYXRvcnMpO1xuICAgICAgICBjb250YWluZXJMaXN0ID0gT2JqZWN0LmtleXMob3B0LmNvbnRhaW5lcnMpO1xuICAgICAgICBjb250YWluZXJDbG9zZUxpc3QgPSBjb250YWluZXJMaXN0Lm1hcChmdW5jdGlvbihrZXkpeyByZXR1cm4gb3B0LmNvbnRhaW5lcnNba2V5XS5jbG9zZXI7IH0pO1xuICAgICAgICBcbiAgICAgICAgcHJvcGVydHlTZXBhcmF0b3IgPSAnJztcbiAgICAgICAgT2JqZWN0LmtleXMob3B0LnNlcGFyYXRvcnMpLmZvckVhY2goZnVuY3Rpb24oc2VwKXsgaWYgKG9wdC5zZXBhcmF0b3JzW3NlcF0uZXhlYyA9PT0gJFBST1BFUlRZKXsgcHJvcGVydHlTZXBhcmF0b3IgPSBzZXA7IH0gfSk7XG4gICAgICAgIHNpbmdsZXF1b3RlID0gJyc7XG4gICAgICAgIGRvdWJsZXF1b3RlID0gJyc7XG4gICAgICAgIE9iamVjdC5rZXlzKG9wdC5jb250YWluZXJzKS5mb3JFYWNoKGZ1bmN0aW9uKHNlcCl7XG4gICAgICAgICAgICBpZiAob3B0LmNvbnRhaW5lcnNbc2VwXS5leGVjID09PSAkU0lOR0xFUVVPVEUpeyBzaW5nbGVxdW90ZSA9IHNlcDt9XG4gICAgICAgICAgICBpZiAob3B0LmNvbnRhaW5lcnNbc2VwXS5leGVjID09PSAkRE9VQkxFUVVPVEUpeyBkb3VibGVxdW90ZSA9IHNlcDt9XG4gICAgICAgIH0pO1xuXG4gICAgICAgIC8vIEZpbmQgYWxsIHNwZWNpYWwgY2hhcmFjdGVycyBleGNlcHQgcHJvcGVydHkgc2VwYXJhdG9yICguIGJ5IGRlZmF1bHQpXG4gICAgICAgIHNpbXBsZVBhdGhDaGFycyA9ICdbXFxcXFxcXFwnICsgWyRXSUxEQ0FSRF0uY29uY2F0KHByZWZpeExpc3QpLmNvbmNhdChzZXBhcmF0b3JMaXN0KS5jb25jYXQoY29udGFpbmVyTGlzdCkuam9pbignXFxcXCcpLnJlcGxhY2UoJ1xcXFwnK3Byb3BlcnR5U2VwYXJhdG9yLCAnJykgKyAnXSc7XG4gICAgICAgIHNpbXBsZVBhdGhSZWdFeCA9IG5ldyBSZWdFeHAoc2ltcGxlUGF0aENoYXJzKTtcbiAgICAgICAgXG4gICAgICAgIC8vIEZpbmQgYWxsIHNwZWNpYWwgY2hhcmFjdGVycywgaW5jbHVkaW5nIGJhY2tzbGFzaFxuICAgICAgICBhbGxTcGVjaWFscyA9ICdbXFxcXFxcXFxcXFxcJyArIFskV0lMRENBUkRdLmNvbmNhdChwcmVmaXhMaXN0KS5jb25jYXQoc2VwYXJhdG9yTGlzdCkuY29uY2F0KGNvbnRhaW5lckxpc3QpLmNvbmNhdChjb250YWluZXJDbG9zZUxpc3QpLmpvaW4oJ1xcXFwnKSArICddJztcbiAgICAgICAgYWxsU3BlY2lhbHNSZWdFeCA9IG5ldyBSZWdFeHAoYWxsU3BlY2lhbHMsICdnJyk7XG4gICAgICAgIFxuICAgICAgICAvLyBGaW5kIGFsbCBlc2NhcGVkIHNwZWNpYWwgY2hhcmFjdGVyc1xuICAgICAgICAvLyBlc2NhcGVkU3BlY2lhbHNSZWdFeCA9IG5ldyBSZWdFeHAoJ1xcXFwnK2FsbFNwZWNpYWxzLCAnZycpO1xuICAgICAgICAvLyBGaW5kIGFsbCBlc2NhcGVkIG5vbi1zcGVjaWFsIGNoYXJhY3RlcnMsIGkuZS4gdW5uZWNlc3NhcnkgZXNjYXBlc1xuICAgICAgICBlc2NhcGVkTm9uU3BlY2lhbHNSZWdFeCA9IG5ldyBSZWdFeHAoJ1xcXFwnK2FsbFNwZWNpYWxzLnJlcGxhY2UoL15cXFsvLCdbXicpKTtcbiAgICAgICAgaWYgKHNpbmdsZXF1b3RlIHx8IGRvdWJsZXF1b3RlKXtcbiAgICAgICAgICAgIGVzY2FwZWRRdW90ZXMgPSBuZXcgUmVnRXhwKCdcXFxcWycrc2luZ2xlcXVvdGUrZG91YmxlcXVvdGUrJ10nLCAnZycpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgZXNjYXBlZFF1b3RlcyA9ICcnO1xuICAgICAgICB9XG4gICAgICAgIFxuICAgICAgICAvLyBGaW5kIHdpbGRjYXJkIGNoYXJhY3RlclxuICAgICAgICB3aWxkY2FyZFJlZ0V4ID0gbmV3IFJlZ0V4cCgnXFxcXCcrJFdJTERDQVJEKTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2V0cyBhbGwgdGhlIGRlZmF1bHQgb3B0aW9ucyBmb3IgaW50ZXJwcmV0ZXIgYmVoYXZpb3IgYW5kIHN5bnRheC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqL1xuICAgIHZhciBzZXREZWZhdWx0T3B0aW9ucyA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIG9wdCA9IG9wdCB8fCB7fTtcbiAgICAgICAgLy8gRGVmYXVsdCBzZXR0aW5nc1xuICAgICAgICBvcHQudXNlQ2FjaGUgPSB0cnVlOyAgLy8gY2FjaGUgdG9rZW5pemVkIHBhdGhzIGZvciByZXBlYXRlZCB1c2VcbiAgICAgICAgb3B0LnNpbXBsZSA9IGZhbHNlOyAgIC8vIG9ubHkgc3VwcG9ydCBkb3Qtc2VwYXJhdGVkIHBhdGhzLCBubyBvdGhlciBzcGVjaWFsIGNoYXJhY3RlcnNcbiAgICAgICAgb3B0LmZvcmNlID0gZmFsc2U7ICAgIC8vIGNyZWF0ZSBpbnRlcm1lZGlhdGUgcHJvcGVydGllcyBkdXJpbmcgYHNldGAgb3BlcmF0aW9uXG5cbiAgICAgICAgLy8gRGVmYXVsdCBwcmVmaXggc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICAgIG9wdC5wcmVmaXhlcyA9IHtcbiAgICAgICAgICAgICdeJzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJFBBUkVOVFxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICd+Jzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJFJPT1RcbiAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnJSc6IHtcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRQTEFDRUhPTERFUlxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICdAJzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJENPTlRFWFRcbiAgICAgICAgICAgIH1cbiAgICAgICAgfTtcbiAgICAgICAgLy8gRGVmYXVsdCBzZXBhcmF0b3Igc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICAgIG9wdC5zZXBhcmF0b3JzID0ge1xuICAgICAgICAgICAgJy4nOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkUFJPUEVSVFlcbiAgICAgICAgICAgICAgICB9LFxuICAgICAgICAgICAgJywnOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkQ09MTEVDVElPTlxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnPCc6IHtcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRFQUNIXG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIC8vIERlZmF1bHQgY29udGFpbmVyIHNwZWNpYWwgY2hhcmFjdGVyc1xuICAgICAgICBvcHQuY29udGFpbmVycyA9IHtcbiAgICAgICAgICAgICdbJzoge1xuICAgICAgICAgICAgICAgICdjbG9zZXInOiAnXScsXG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkUFJPUEVSVFlcbiAgICAgICAgICAgICAgICB9LFxuICAgICAgICAgICAgJ1xcJyc6IHtcbiAgICAgICAgICAgICAgICAnY2xvc2VyJzogJ1xcJycsXG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkU0lOR0xFUVVPVEVcbiAgICAgICAgICAgICAgICB9LFxuICAgICAgICAgICAgJ1wiJzoge1xuICAgICAgICAgICAgICAgICdjbG9zZXInOiAnXCInLFxuICAgICAgICAgICAgICAgICdleGVjJzogJERPVUJMRVFVT1RFXG4gICAgICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICcoJzoge1xuICAgICAgICAgICAgICAgICdjbG9zZXInOiAnKScsXG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkQ0FMTFxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAneyc6IHtcbiAgICAgICAgICAgICAgICAnY2xvc2VyJzogJ30nLFxuICAgICAgICAgICAgICAgICdleGVjJzogJEVWQUxQUk9QRVJUWVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgfTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogVGVzdCBzdHJpbmcgdG8gc2VlIGlmIGl0IGlzIHN1cnJvdW5kZWQgYnkgc2luZ2xlLSBvciBkb3VibGUtcXVvdGUsIHVzaW5nIHRoZVxuICAgICAqIGN1cnJlbnQgY29uZmlndXJhdGlvbiBkZWZpbml0aW9uIGZvciB0aG9zZSBjaGFyYWN0ZXJzLiBJZiBubyBxdW90ZSBjb250YWluZXJcbiAgICAgKiBpcyBkZWZpbmVkLCB0aGlzIGZ1bmN0aW9uIHdpbGwgcmV0dXJuIGZhbHNlIHNpbmNlIGl0J3Mgbm90IHBvc3NpYmxlIHRvIHF1b3RlXG4gICAgICogdGhlIHN0cmluZyBpZiB0aGVyZSBhcmUgbm8gcXVvdGVzIGluIHRoZSBzeW50YXguIEFsc28gaWdub3JlcyBlc2NhcGVkIHF1b3RlXG4gICAgICogY2hhcmFjdGVycy5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc3RyIFRoZSBzdHJpbmcgdG8gdGVzdCBmb3IgZW5jbG9zaW5nIHF1b3Rlc1xuICAgICAqIEByZXR1cm4ge0Jvb2xlYW59IHRydWUgPSBzdHJpbmcgaXMgZW5jbG9zZWQgaW4gcXVvdGVzOyBmYWxzZSA9IG5vdCBxdW90ZWRcbiAgICAgKi9cbiAgICB2YXIgaXNRdW90ZWQgPSBmdW5jdGlvbihzdHIpe1xuICAgICAgICB2YXIgY2xlYW5TdHIgPSBzdHIucmVwbGFjZShlc2NhcGVkUXVvdGVzLCAnJyk7XG4gICAgICAgIHZhciBzdHJMZW4gPSBjbGVhblN0ci5sZW5ndGg7XG4gICAgICAgIGlmIChzdHJMZW4gPCAyKXsgcmV0dXJuIGZhbHNlOyB9XG4gICAgICAgIHJldHVybiAgKGNsZWFuU3RyWzBdID09PSBjbGVhblN0cltzdHJMZW4gLSAxXSkgJiZcbiAgICAgICAgICAgICAgICAoY2xlYW5TdHJbMF0gPT09IHNpbmdsZXF1b3RlIHx8IGNsZWFuU3RyWzBdID09PSBkb3VibGVxdW90ZSk7XG4gICAgfTtcbiAgICBcbiAgICAvKipcbiAgICAgKiBSZW1vdmUgZW5jbG9zaW5nIHF1b3RlcyBmcm9tIGEgc3RyaW5nLiBUaGUgaXNRdW90ZWQgZnVuY3Rpb24gd2lsbCBkZXRlcm1pbmVcbiAgICAgKiBpZiBhbnkgY2hhbmdlIGlzIG5lZWRlZC4gSWYgdGhlIHN0cmluZyBpcyBxdW90ZWQsIHdlIGtub3cgdGhlIGZpcnN0IGFuZCBsYXN0XG4gICAgICogY2hhcmFjdGVycyBhcmUgcXVvdGUgbWFya3MsIHNvIHNpbXBseSBkbyBhIHN0cmluZyBzbGljZS4gSWYgdGhlIGlucHV0IHZhbHVlIGlzXG4gICAgICogbm90IHF1b3RlZCwgcmV0dXJuIHRoZSBpbnB1dCB2YWx1ZSB1bmNoYW5nZWQuIEJlY2F1c2UgaXNRdW90ZWQgaXMgdXNlZCwgaWZcbiAgICAgKiBubyBxdW90ZSBtYXJrcyBhcmUgZGVmaW5lZCBpbiB0aGUgc3ludGF4LCB0aGlzIGZ1bmN0aW9uIHdpbGwgcmV0dXJuIHRoZSBpbnB1dCB2YWx1ZS5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc3RyIFRoZSBzdHJpbmcgdG8gdW4tcXVvdGVcbiAgICAgKiBAcmV0dXJuIHtTdHJpbmd9IFRoZSBpbnB1dCBzdHJpbmcgd2l0aG91dCBhbnkgZW5jbG9zaW5nIHF1b3RlIG1hcmtzLlxuICAgICAqL1xuICAgIHZhciBzdHJpcFF1b3RlcyA9IGZ1bmN0aW9uKHN0cil7XG4gICAgICAgIGlmIChpc1F1b3RlZChzdHIpKXtcbiAgICAgICAgICAgIHJldHVybiBzdHIuc2xpY2UoMSwgLTEpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBzdHI7XG4gICAgfTtcbiAgICBcbiAgICAvKipcbiAgICAgKiBTY2FuIGlucHV0IHN0cmluZyBmcm9tIGxlZnQgdG8gcmlnaHQsIG9uZSBjaGFyYWN0ZXIgYXQgYSB0aW1lLiBJZiBhIHNwZWNpYWwgY2hhcmFjdGVyXG4gICAgICogaXMgZm91bmQgKG9uZSBvZiBcInNlcGFyYXRvcnNcIiwgXCJjb250YWluZXJzXCIsIG9yIFwicHJlZml4ZXNcIiksIGVpdGhlciBzdG9yZSB0aGUgYWNjdW11bGF0ZWRcbiAgICAgKiB3b3JkIGFzIGEgdG9rZW4gb3IgZWxzZSBiZWdpbiB3YXRjaGluZyBpbnB1dCBmb3IgZW5kIG9mIHRva2VuIChmaW5kaW5nIGEgY2xvc2luZyBjaGFyYWN0ZXJcbiAgICAgKiBmb3IgYSBjb250YWluZXIgb3IgdGhlIGVuZCBvZiBhIGNvbGxlY3Rpb24pLiBJZiBhIGNvbnRhaW5lciBpcyBmb3VuZCwgY2FwdHVyZSB0aGUgc3Vic3RyaW5nXG4gICAgICogd2l0aGluIHRoZSBjb250YWluZXIgYW5kIHJlY3Vyc2l2ZWx5IGNhbGwgYHRva2VuaXplYCBvbiB0aGF0IHN1YnN0cmluZy4gRmluYWwgb3V0cHV0IHdpbGxcbiAgICAgKiBiZSBhbiBhcnJheSBvZiB0b2tlbnMuIEEgY29tcGxleCB0b2tlbiAobm90IGEgc2ltcGxlIHByb3BlcnR5IG9yIGluZGV4KSB3aWxsIGJlIHJlcHJlc2VudGVkXG4gICAgICogYXMgYW4gb2JqZWN0IGNhcnJ5aW5nIG1ldGFkYXRhIGZvciBwcm9jZXNzaW5nLlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtICB7U3RyaW5nfSBzdHIgUGF0aCBzdHJpbmdcbiAgICAgKiBAcmV0dXJuIHtBcnJheX0gICAgIEFycmF5IG9mIHRva2VucyBmb3VuZCBpbiB0aGUgaW5wdXQgcGF0aFxuICAgICAqL1xuICAgIHZhciB0b2tlbml6ZSA9IGZ1bmN0aW9uIChzdHIpe1xuICAgICAgICB2YXIgcGF0aCA9ICcnLFxuICAgICAgICAgICAgc2ltcGxlUGF0aCA9IHRydWUsIC8vIHBhdGggaXMgYXNzdW1lZCBcInNpbXBsZVwiIHVudGlsIHByb3ZlbiBvdGhlcndpc2VcbiAgICAgICAgICAgIHRva2VucyA9IFtdLFxuICAgICAgICAgICAgcmVjdXIgPSBbXSxcbiAgICAgICAgICAgIG1vZHMgPSB7fSxcbiAgICAgICAgICAgIHBhdGhMZW5ndGggPSAwLFxuICAgICAgICAgICAgd29yZCA9ICcnLFxuICAgICAgICAgICAgaGFzV2lsZGNhcmQgPSBmYWxzZSxcbiAgICAgICAgICAgIGRvRWFjaCA9IGZhbHNlLCAvLyBtdXN0IHJlbWVtYmVyIHRoZSBcImVhY2hcIiBvcGVyYXRvciBpbnRvIHRoZSBmb2xsb3dpbmcgdG9rZW5cbiAgICAgICAgICAgIHN1YnBhdGggPSAnJyxcbiAgICAgICAgICAgIGkgPSAwLFxuICAgICAgICAgICAgb3BlbmVyID0gJycsXG4gICAgICAgICAgICBjbG9zZXIgPSAnJyxcbiAgICAgICAgICAgIHNlcGFyYXRvciA9ICcnLFxuICAgICAgICAgICAgY29sbGVjdGlvbiA9IFtdLFxuICAgICAgICAgICAgZGVwdGggPSAwLFxuICAgICAgICAgICAgZXNjYXBlZCA9IDA7XG5cbiAgICAgICAgaWYgKG9wdC51c2VDYWNoZSAmJiBjYWNoZVtzdHJdICE9PSBVTkRFRil7IHJldHVybiBjYWNoZVtzdHJdOyB9XG5cbiAgICAgICAgLy8gU3RyaXAgb3V0IGFueSB1bm5lY2Vzc2FyeSBlc2NhcGluZyB0byBzaW1wbGlmeSBwcm9jZXNzaW5nIGJlbG93XG4gICAgICAgIHBhdGggPSBzdHIucmVwbGFjZShlc2NhcGVkTm9uU3BlY2lhbHNSZWdFeCwgJyQmJy5zdWJzdHIoMSkpO1xuICAgICAgICBwYXRoTGVuZ3RoID0gcGF0aC5sZW5ndGg7XG5cbiAgICAgICAgaWYgKHR5cGVvZiBzdHIgPT09ICRTVFJJTkcgJiYgIXNpbXBsZVBhdGhSZWdFeC50ZXN0KHN0cikpe1xuICAgICAgICAgICAgdG9rZW5zID0gcGF0aC5zcGxpdChwcm9wZXJ0eVNlcGFyYXRvcik7XG4gICAgICAgICAgICBvcHQudXNlQ2FjaGUgJiYgKGNhY2hlW3N0cl0gPSB7dDogdG9rZW5zLCBzaW1wbGU6IHNpbXBsZVBhdGh9KTtcbiAgICAgICAgICAgIHJldHVybiB7dDogdG9rZW5zLCBzaW1wbGU6IHNpbXBsZVBhdGh9O1xuICAgICAgICB9XG5cbiAgICAgICAgZm9yIChpID0gMDsgaSA8IHBhdGhMZW5ndGg7IGkrKyl7XG4gICAgICAgICAgICAvLyBTa2lwIGVzY2FwZSBjaGFyYWN0ZXIgKGBcXGApIGFuZCBzZXQgXCJlc2NhcGVkXCIgdG8gdGhlIGluZGV4IHZhbHVlXG4gICAgICAgICAgICAvLyBvZiB0aGUgY2hhcmFjdGVyIHRvIGJlIHRyZWF0ZWQgYXMgYSBsaXRlcmFsXG4gICAgICAgICAgICBpZiAoIWVzY2FwZWQgJiYgcGF0aFtpXSA9PT0gJ1xcXFwnKXtcbiAgICAgICAgICAgICAgICAvLyBOZXh0IGNoYXJhY3RlciBpcyB0aGUgZXNjYXBlZCBjaGFyYWN0ZXJcbiAgICAgICAgICAgICAgICBlc2NhcGVkID0gaSsxO1xuICAgICAgICAgICAgICAgIGkrKztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIElmIGEgd2lsZGNhcmQgY2hhcmFjdGVyIGlzIGZvdW5kLCBtYXJrIHRoaXMgdG9rZW4gYXMgaGF2aW5nIGEgd2lsZGNhcmRcbiAgICAgICAgICAgIGlmIChwYXRoW2ldID09PSAkV0lMRENBUkQpIHtcbiAgICAgICAgICAgICAgICBoYXNXaWxkY2FyZCA9IHRydWU7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBJZiB3ZSBoYXZlIGFscmVhZHkgcHJvY2Vzc2VkIGEgY29udGFpbmVyIG9wZW5lciwgdHJlYXQgdGhpcyBzdWJwYXRoIHNwZWNpYWxseVxuICAgICAgICAgICAgaWYgKGRlcHRoID4gMCl7XG4gICAgICAgICAgICAgICAgLy8gSXMgdGhpcyBjaGFyYWN0ZXIgYW5vdGhlciBvcGVuZXIgZnJvbSB0aGUgc2FtZSBjb250YWluZXI/IElmIHNvLCBhZGQgdG9cbiAgICAgICAgICAgICAgICAvLyB0aGUgZGVwdGggbGV2ZWwgc28gd2UgY2FuIG1hdGNoIHRoZSBjbG9zZXJzIGNvcnJlY3RseS4gKEV4Y2VwdCBmb3IgcXVvdGVzXG4gICAgICAgICAgICAgICAgLy8gd2hpY2ggY2Fubm90IGJlIG5lc3RlZClcbiAgICAgICAgICAgICAgICAvLyBJcyB0aGlzIGNoYXJhY3RlciB0aGUgY2xvc2VyPyBJZiBzbywgYmFjayBvdXQgb25lIGxldmVsIG9mIGRlcHRoLlxuICAgICAgICAgICAgICAgIC8vIEJlIGNhcmVmdWw6IHF1b3RlIGNvbnRhaW5lciB1c2VzIHNhbWUgY2hhcmFjdGVyIGZvciBvcGVuZXIgYW5kIGNsb3Nlci5cbiAgICAgICAgICAgICAgICAhZXNjYXBlZCAmJiBwYXRoW2ldID09PSBvcGVuZXIgJiYgb3BlbmVyICE9PSBjbG9zZXIuY2xvc2VyICYmIGRlcHRoKys7XG4gICAgICAgICAgICAgICAgIWVzY2FwZWQgJiYgcGF0aFtpXSA9PT0gY2xvc2VyLmNsb3NlciAmJiBkZXB0aC0tO1xuXG4gICAgICAgICAgICAgICAgLy8gV2hpbGUgc3RpbGwgaW5zaWRlIHRoZSBjb250YWluZXIsIGp1c3QgYWRkIHRvIHRoZSBzdWJwYXRoXG4gICAgICAgICAgICAgICAgaWYgKGRlcHRoID4gMCl7XG4gICAgICAgICAgICAgICAgICAgIHN1YnBhdGggKz0gcGF0aFtpXTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gV2hlbiB3ZSBjbG9zZSBvZmYgdGhlIGNvbnRhaW5lciwgdGltZSB0byBwcm9jZXNzIHRoZSBzdWJwYXRoIGFuZCBhZGQgcmVzdWx0cyB0byBvdXIgdG9rZW5zXG4gICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIEhhbmRsZSBzdWJwYXRoIFwiW2Jhcl1cIiBpbiBmb28uW2Jhcl0sW2Jhel0gLSB3ZSBtdXN0IHByb2Nlc3Mgc3VicGF0aCBhbmQgY3JlYXRlIGEgbmV3IGNvbGxlY3Rpb25cbiAgICAgICAgICAgICAgICAgICAgaWYgKGkrMSA8IHBhdGhMZW5ndGggJiYgb3B0LnNlcGFyYXRvcnNbcGF0aFtpKzFdXSAmJiBvcHQuc2VwYXJhdG9yc1twYXRoW2krMV1dLmV4ZWMgPT09ICRDT0xMRUNUSU9OKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChzdWJwYXRoLmxlbmd0aCAmJiBjbG9zZXIuZXhlYyA9PT0gJFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHN0cmlwUXVvdGVzKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY2xvc2VyLmV4ZWMgPT09ICRTSU5HTEVRVU9URSB8fCBjbG9zZXIuZXhlYyA9PT0gJERPVUJMRVFVT1RFKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobW9kcy5oYXMpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHsndyc6IHN1YnBhdGgsICdtb2RzJzogbW9kcywgJ2RvRWFjaCc6IGRvRWFjaH07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHN1YnBhdGg7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHRva2VuaXplKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChyZWN1ciA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIuZXhlYyA9IGNsb3Nlci5leGVjO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmRvRWFjaCA9IGRvRWFjaDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIGNvbGxlY3Rpb24ucHVzaChjbG9zZXIuZXhlYyA9PT0gJFBST1BFUlRZID8gcmVjdXIudFswXSA6IHJlY3VyKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbGxlY3Rpb24ucHVzaChyZWN1cik7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gSGFuZGxlIHN1YnBhdGggXCJbYmF6XVwiIGluIGZvby5bYmFyXSxbYmF6XSAtIHdlIG11c3QgcHJvY2VzcyBzdWJwYXRoIGFuZCBhZGQgdG8gY29sbGVjdGlvblxuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjb2xsZWN0aW9uWzBdKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChzdWJwYXRoLmxlbmd0aCAmJiBjbG9zZXIuZXhlYyA9PT0gJFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHN0cmlwUXVvdGVzKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY2xvc2VyLmV4ZWMgPT09ICRTSU5HTEVRVU9URSB8fCBjbG9zZXIuZXhlYyA9PT0gJERPVUJMRVFVT1RFKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobW9kcy5oYXMpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHsndyc6IHN1YnBhdGgsICdtb2RzJzogbW9kcywgJ2RvRWFjaCc6IGRvRWFjaH07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHN1YnBhdGg7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHRva2VuaXplKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChyZWN1ciA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIuZXhlYyA9IGNsb3Nlci5leGVjO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmRvRWFjaCA9IGRvRWFjaDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbGxlY3Rpb24ucHVzaChyZWN1cik7XG4gICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaCh7J3R0Jzpjb2xsZWN0aW9uLCAnZG9FYWNoJzpkb0VhY2h9KTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbGxlY3Rpb24gPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gU2ltcGxlIHByb3BlcnR5IGNvbnRhaW5lciBpcyBlcXVpdmFsZW50IHRvIGRvdC1zZXBhcmF0ZWQgdG9rZW4uIEp1c3QgYWRkIHRoaXMgdG9rZW4gdG8gdG9rZW5zLlxuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjbG9zZXIuZXhlYyA9PT0gJFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0ge3Q6W3N0cmlwUXVvdGVzKHN1YnBhdGgpXX07XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoZG9FYWNoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaCh7J3cnOnJlY3VyLnRbMF0sICdtb2RzJzp7fSwgJ2RvRWFjaCc6dHJ1ZX0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZG9FYWNoID0gZmFsc2U7IC8vIHJlc2V0XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaChyZWN1ci50WzBdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gUXVvdGVkIHN1YnBhdGggaXMgYWxsIHRha2VuIGxpdGVyYWxseSB3aXRob3V0IHRva2VuIGV2YWx1YXRpb24uIEp1c3QgYWRkIHN1YnBhdGggdG8gdG9rZW5zIGFzLWlzLlxuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjbG9zZXIuZXhlYyA9PT0gJFNJTkdMRVFVT1RFIHx8IGNsb3Nlci5leGVjID09PSAkRE9VQkxFUVVPVEUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG1vZHMuaGFzKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB3b3JkID0geyd3Jzogc3VicGF0aCwgJ21vZHMnOiBtb2RzLCAnZG9FYWNoJzogZG9FYWNofTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyB0b2tlbnMucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHRva2Vucy5wdXNoKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBPdGhlcndpc2UsIGNyZWF0ZSB0b2tlbiBvYmplY3QgdG8gaG9sZCB0b2tlbml6ZWQgc3VicGF0aCwgYWRkIHRvIHRva2Vucy5cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoc3VicGF0aCA9PT0gJycpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0ge3Q6W10sc2ltcGxlOnRydWV9O1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSB0b2tlbml6ZShzdWJwYXRoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChyZWN1ciA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICByZWN1ci5leGVjID0gY2xvc2VyLmV4ZWM7XG4gICAgICAgICAgICAgICAgICAgICAgICByZWN1ci5kb0VhY2ggPSBkb0VhY2g7XG4gICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaChyZWN1cik7XG4gICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIHN1YnBhdGggPSAnJzsgLy8gcmVzZXQgc3VicGF0aFxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIElmIGEgcHJlZml4IGNoYXJhY3RlciBpcyBmb3VuZCwgc3RvcmUgaXQgaW4gYG1vZHNgIGZvciBsYXRlciByZWZlcmVuY2UuXG4gICAgICAgICAgICAvLyBNdXN0IGtlZXAgY291bnQgZHVlIHRvIGBwYXJlbnRgIHByZWZpeCB0aGF0IGNhbiBiZSB1c2VkIG11bHRpcGxlIHRpbWVzIGluIG9uZSB0b2tlbi5cbiAgICAgICAgICAgIGVsc2UgaWYgKCFlc2NhcGVkICYmIHBhdGhbaV0gaW4gb3B0LnByZWZpeGVzICYmIG9wdC5wcmVmaXhlc1twYXRoW2ldXS5leGVjKXtcbiAgICAgICAgICAgICAgICBtb2RzLmhhcyA9IHRydWU7XG4gICAgICAgICAgICAgICAgaWYgKG1vZHNbb3B0LnByZWZpeGVzW3BhdGhbaV1dLmV4ZWNdKSB7IG1vZHNbb3B0LnByZWZpeGVzW3BhdGhbaV1dLmV4ZWNdKys7IH1cbiAgICAgICAgICAgICAgICBlbHNlIHsgbW9kc1tvcHQucHJlZml4ZXNbcGF0aFtpXV0uZXhlY10gPSAxOyB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBJZiBhIHNlcGFyYXRvciBpcyBmb3VuZCwgdGltZSB0byBzdG9yZSB0aGUgdG9rZW4gd2UndmUgYmVlbiBhY2N1bXVsYXRpbmcuIElmXG4gICAgICAgICAgICAvLyB0aGlzIHRva2VuIGhhZCBhIHByZWZpeCwgd2Ugc3RvcmUgdGhlIHRva2VuIGFzIGFuIG9iamVjdCB3aXRoIG1vZGlmaWVyIGRhdGEuXG4gICAgICAgICAgICAvLyBJZiB0aGUgc2VwYXJhdG9yIGlzIHRoZSBjb2xsZWN0aW9uIHNlcGFyYXRvciwgd2UgbXVzdCBlaXRoZXIgY3JlYXRlIG9yIGFkZFxuICAgICAgICAgICAgLy8gdG8gYSBjb2xsZWN0aW9uIGZvciB0aGlzIHRva2VuLiBGb3Igc2ltcGxlIHNlcGFyYXRvciwgd2UgZWl0aGVyIGFkZCB0aGUgdG9rZW5cbiAgICAgICAgICAgIC8vIHRvIHRoZSB0b2tlbiBsaXN0IG9yIGVsc2UgYWRkIHRvIHRoZSBleGlzdGluZyBjb2xsZWN0aW9uIGlmIGl0IGV4aXN0cy5cbiAgICAgICAgICAgIGVsc2UgaWYgKCFlc2NhcGVkICYmIG9wdC5zZXBhcmF0b3JzW3BhdGhbaV1dICYmIG9wdC5zZXBhcmF0b3JzW3BhdGhbaV1dLmV4ZWMpe1xuICAgICAgICAgICAgICAgIHNlcGFyYXRvciA9IG9wdC5zZXBhcmF0b3JzW3BhdGhbaV1dO1xuICAgICAgICAgICAgICAgIGlmICghd29yZCAmJiAobW9kcy5oYXMgfHwgaGFzV2lsZGNhcmQpKXtcbiAgICAgICAgICAgICAgICAgICAgLy8gZm91bmQgYSBzZXBhcmF0b3IsIGFmdGVyIHNlZWluZyBwcmVmaXhlcywgYnV0IG5vIHRva2VuIHdvcmQgLT4gaW52YWxpZFxuICAgICAgICAgICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBUaGlzIHRva2VuIHdpbGwgcmVxdWlyZSBzcGVjaWFsIGludGVycHJldGVyIHByb2Nlc3NpbmcgZHVlIHRvIHByZWZpeCBvciB3aWxkY2FyZC5cbiAgICAgICAgICAgICAgICBpZiAod29yZCAmJiAobW9kcy5oYXMgfHwgaGFzV2lsZGNhcmQgfHwgZG9FYWNoKSl7XG4gICAgICAgICAgICAgICAgICAgIHdvcmQgPSB7J3cnOiB3b3JkLCAnbW9kcyc6IG1vZHMsICdkb0VhY2gnOiBkb0VhY2h9O1xuICAgICAgICAgICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIHdvcmQgaXMgYSBwbGFpbiBwcm9wZXJ0eSBvciBlbmQgb2YgY29sbGVjdGlvblxuICAgICAgICAgICAgICAgIGlmIChzZXBhcmF0b3IuZXhlYyA9PT0gJFBST1BFUlRZIHx8IHNlcGFyYXRvci5leGVjID09PSAkRUFDSCl7XG4gICAgICAgICAgICAgICAgICAgIC8vIHdlIGFyZSBnYXRoZXJpbmcgYSBjb2xsZWN0aW9uLCBzbyBhZGQgbGFzdCB3b3JkIHRvIGNvbGxlY3Rpb24gYW5kIHRoZW4gc3RvcmVcbiAgICAgICAgICAgICAgICAgICAgaWYgKGNvbGxlY3Rpb25bMF0gIT09IFVOREVGKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdvcmQgJiYgY29sbGVjdGlvbi5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2goeyd0dCc6Y29sbGVjdGlvbiwgJ2RvRWFjaCc6ZG9FYWNofSk7XG4gICAgICAgICAgICAgICAgICAgICAgICBjb2xsZWN0aW9uID0gW107IC8vIHJlc2V0XG4gICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIHdvcmQgaXMgYSBwbGFpbiBwcm9wZXJ0eVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdvcmQgJiYgdG9rZW5zLnB1c2god29yZCk7XG4gICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gSWYgdGhlIHNlcGFyYXRvciBpcyB0aGUgXCJlYWNoXCIgc2VwYXJ0b3IsIHRoZSBmb2xsb3dpbmcgd29yZCB3aWxsIGJlIGV2YWx1YXRlZCBkaWZmZXJlbnRseS5cbiAgICAgICAgICAgICAgICAgICAgLy8gSWYgaXQncyBub3QgdGhlIFwiZWFjaFwiIHNlcGFyYXRvciwgdGhlbiByZXNldCBcImRvRWFjaFwiXG4gICAgICAgICAgICAgICAgICAgIGRvRWFjaCA9IHNlcGFyYXRvci5leGVjID09PSAkRUFDSDsgLy8gcmVzZXRcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gd29yZCBpcyBhIGNvbGxlY3Rpb25cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChzZXBhcmF0b3IuZXhlYyA9PT0gJENPTExFQ1RJT04pe1xuICAgICAgICAgICAgICAgICAgICB3b3JkICYmIGNvbGxlY3Rpb24ucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgd29yZCA9ICcnOyAvLyByZXNldFxuICAgICAgICAgICAgICAgIGhhc1dpbGRjYXJkID0gZmFsc2U7IC8vIHJlc2V0XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBGb3VuZCBhIGNvbnRhaW5lciBvcGVuaW5nIGNoYXJhY3Rlci4gQSBjb250YWluZXIgb3BlbmluZyBpcyBlcXVpdmFsZW50IHRvXG4gICAgICAgICAgICAvLyBmaW5kaW5nIGEgc2VwYXJhdG9yLCBzbyBcImZvby5iYXJcIiBpcyBlcXVpdmFsZW50IHRvIFwiZm9vW2Jhcl1cIiwgc28gYXBwbHkgc2ltaWxhclxuICAgICAgICAgICAgLy8gcHJvY2VzcyBhcyBzZXBhcmF0b3IgYWJvdmUgd2l0aCByZXNwZWN0IHRvIHRva2VuIHdlIGhhdmUgYWNjdW11bGF0ZWQgc28gZmFyLlxuICAgICAgICAgICAgLy8gRXhjZXB0IGluIGNhc2UgY29sbGVjdGlvbnMgLSBwYXRoIG1heSBoYXZlIGEgY29sbGVjdGlvbiBvZiBjb250YWluZXJzLCBzb1xuICAgICAgICAgICAgLy8gaW4gXCJmb29bYmFyXSxbYmF6XVwiLCB0aGUgXCJbYmFyXVwiIG1hcmtzIHRoZSBlbmQgb2YgdG9rZW4gXCJmb29cIiwgYnV0IFwiW2Jhel1cIiBpc1xuICAgICAgICAgICAgLy8gbWVyZWx5IGFub3RoZXIgZW50cnkgaW4gdGhlIGNvbGxlY3Rpb24sIHNvIHdlIGRvbid0IGNsb3NlIG9mZiB0aGUgY29sbGVjdGlvbiB0b2tlblxuICAgICAgICAgICAgLy8geWV0LlxuICAgICAgICAgICAgLy8gU2V0IGRlcHRoIHZhbHVlIGZvciBmdXJ0aGVyIHByb2Nlc3NpbmcuXG4gICAgICAgICAgICBlbHNlIGlmICghZXNjYXBlZCAmJiBvcHQuY29udGFpbmVyc1twYXRoW2ldXSAmJiBvcHQuY29udGFpbmVyc1twYXRoW2ldXS5leGVjKXtcbiAgICAgICAgICAgICAgICBjbG9zZXIgPSBvcHQuY29udGFpbmVyc1twYXRoW2ldXTtcbiAgICAgICAgICAgICAgICBpZiAod29yZCAmJiAobW9kcy5oYXMgfHwgaGFzV2lsZGNhcmQgfHwgZG9FYWNoKSl7XG4gICAgICAgICAgICAgICAgICAgIGlmICh0eXBlb2Ygd29yZCA9PT0gJ3N0cmluZycpe1xuICAgICAgICAgICAgICAgICAgICAgICAgd29yZCA9IHsndyc6IHdvcmQsICdtb2RzJzogbW9kcywgJ2RvRWFjaCc6ZG9FYWNofTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdvcmQubW9kcyA9IG1vZHM7XG4gICAgICAgICAgICAgICAgICAgICAgICB3b3JkLmRvRWFjaCA9IGRvRWFjaDtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGlmIChjb2xsZWN0aW9uWzBdICE9PSBVTkRFRil7XG4gICAgICAgICAgICAgICAgICAgIC8vIHdlIGFyZSBnYXRoZXJpbmcgYSBjb2xsZWN0aW9uLCBzbyBhZGQgbGFzdCB3b3JkIHRvIGNvbGxlY3Rpb24gYW5kIHRoZW4gc3RvcmVcbiAgICAgICAgICAgICAgICAgICAgd29yZCAmJiBjb2xsZWN0aW9uLnB1c2god29yZCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAvLyB3b3JkIGlzIGEgcGxhaW4gcHJvcGVydHlcbiAgICAgICAgICAgICAgICAgICAgd29yZCAmJiB0b2tlbnMucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSB0cnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBvcGVuZXIgPSBwYXRoW2ldO1xuICAgICAgICAgICAgICAgIC8vIDEpIGRvbid0IHJlc2V0IGRvRWFjaCBmb3IgZW1wdHkgd29yZCBiZWNhdXNlIHRoaXMgaXMgW2Zvb108W2Jhcl1cbiAgICAgICAgICAgICAgICAvLyAyKSBkb24ndCByZXNldCBkb0VhY2ggZm9yIG9wZW5pbmcgQ2FsbCBiZWNhdXNlIHRoaXMgaXMgYSxiPGZuKClcbiAgICAgICAgICAgICAgICBpZiAod29yZCAmJiBvcHQuY29udGFpbmVyc1tvcGVuZXJdLmV4ZWMgIT09ICRDQUxMKXtcbiAgICAgICAgICAgICAgICAgICAgZG9FYWNoID0gZmFsc2U7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHdvcmQgPSAnJztcbiAgICAgICAgICAgICAgICBoYXNXaWxkY2FyZCA9IGZhbHNlO1xuICAgICAgICAgICAgICAgIGRlcHRoKys7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBPdGhlcndpc2UsIHRoaXMgaXMganVzdCBhbm90aGVyIGNoYXJhY3RlciB0byBhZGQgdG8gdGhlIGN1cnJlbnQgdG9rZW5cbiAgICAgICAgICAgIGVsc2UgaWYgKGkgPCBwYXRoTGVuZ3RoKSB7XG4gICAgICAgICAgICAgICAgd29yZCArPSBwYXRoW2ldO1xuICAgICAgICAgICAgfVxuXG4gICAgICAgICAgICAvLyBJZiBjdXJyZW50IHBhdGggaW5kZXggbWF0Y2hlcyB0aGUgZXNjYXBlIGluZGV4IHZhbHVlLCByZXNldCBgZXNjYXBlZGBcbiAgICAgICAgICAgIGlmIChpIDwgcGF0aExlbmd0aCAmJiBpID09PSBlc2NhcGVkKXtcbiAgICAgICAgICAgICAgICBlc2NhcGVkID0gMDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuXG4gICAgICAgIC8vIFBhdGggZW5kZWQgaW4gYW4gZXNjYXBlIGNoYXJhY3RlclxuICAgICAgICBpZiAoZXNjYXBlZCl7XG4gICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gQWRkIHRyYWlsaW5nIHdvcmQgdG8gdG9rZW5zLCBpZiBwcmVzZW50XG4gICAgICAgIGlmICh0eXBlb2Ygd29yZCA9PT0gJ3N0cmluZycgJiYgd29yZCAmJiAobW9kcy5oYXMgfHwgaGFzV2lsZGNhcmQgfHwgZG9FYWNoKSl7XG4gICAgICAgICAgICB3b3JkID0geyd3Jzogd29yZCwgJ21vZHMnOiB3b3JkLm1vZHMgfHwgbW9kcywgJ2RvRWFjaCc6IGRvRWFjaH07XG4gICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKHdvcmQgJiYgbW9kcy5oYXMpe1xuICAgICAgICAgICAgd29yZC5tb2RzID0gbW9kcztcbiAgICAgICAgfVxuICAgICAgICAvLyBXZSBhcmUgZ2F0aGVyaW5nIGEgY29sbGVjdGlvbiwgc28gYWRkIGxhc3Qgd29yZCB0byBjb2xsZWN0aW9uIGFuZCB0aGVuIHN0b3JlXG4gICAgICAgIGlmIChjb2xsZWN0aW9uWzBdICE9PSBVTkRFRil7XG4gICAgICAgICAgICB3b3JkICYmIGNvbGxlY3Rpb24ucHVzaCh3b3JkKTtcbiAgICAgICAgICAgIHRva2Vucy5wdXNoKHsndHQnOmNvbGxlY3Rpb24sICdkb0VhY2gnOmRvRWFjaH0pO1xuICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgICAvLyBXb3JkIGlzIGEgcGxhaW4gcHJvcGVydHlcbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB3b3JkICYmIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSB0cnVlO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gZGVwdGggIT0gMCBtZWFucyBtaXNtYXRjaGVkIGNvbnRhaW5lcnNcbiAgICAgICAgaWYgKGRlcHRoICE9PSAwKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuXG4gICAgICAgIC8vIElmIHBhdGggd2FzIHZhbGlkLCBjYWNoZSB0aGUgcmVzdWx0XG4gICAgICAgIG9wdC51c2VDYWNoZSAmJiAoY2FjaGVbc3RyXSA9IHt0OiB0b2tlbnMsIHNpbXBsZTogc2ltcGxlUGF0aH0pO1xuXG5jb25zb2xlLmxvZygnVG9rZW5zOicsIEpTT04uc3RyaW5naWZ5KHRva2Vucyx1bmRlZmluZWQsMikpO1xuICAgICAgICByZXR1cm4ge3Q6IHRva2Vucywgc2ltcGxlOiBzaW1wbGVQYXRofTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogSXQgaXMgYHJlc29sdmVQYXRoYCdzIGpvYiB0byB0cmF2ZXJzZSBhbiBvYmplY3QgYWNjb3JkaW5nIHRvIHRoZSB0b2tlbnNcbiAgICAgKiBkZXJpdmVkIGZyb20gdGhlIGtleXBhdGggYW5kIGVpdGhlciByZXR1cm4gdGhlIHZhbHVlIGZvdW5kIHRoZXJlIG9yIHNldFxuICAgICAqIGEgbmV3IHZhbHVlIGluIHRoYXQgbG9jYXRpb24uXG4gICAgICogVGhlIHRva2VucyBhcmUgYSBzaW1wbGUgYXJyYXkgYW5kIGByZW9zbHZlUGF0aGAgbG9vcHMgdGhyb3VnaCB0aGUgbGlzdFxuICAgICAqIHdpdGggYSBzaW1wbGUgXCJ3aGlsZVwiIGxvb3AuIEEgdG9rZW4gbWF5IGl0c2VsZiBiZSBhIG5lc3RlZCB0b2tlbiBhcnJheSxcbiAgICAgKiB3aGljaCBpcyBwcm9jZXNzZWQgdGhyb3VnaCByZWN1cnNpb24uXG4gICAgICogQXMgZWFjaCBzdWNjZXNzaXZlIHZhbHVlIGlzIHJlc29sdmVkIHdpdGhpbiBgb2JqYCwgdGhlIGN1cnJlbnQgdmFsdWUgaXNcbiAgICAgKiBwdXNoZWQgb250byB0aGUgXCJ2YWx1ZVN0YWNrXCIsIGVuYWJsaW5nIGJhY2t3YXJkIHJlZmVyZW5jZXMgKHVwd2FyZHMgaW4gYG9iamApXG4gICAgICogdGhyb3VnaCBwYXRoIHByZWZpeGVzIGxpa2UgXCI8XCIgZm9yIFwicGFyZW50XCIgYW5kIFwiflwiIGZvciBcInJvb3RcIi4gVGhlIGxvb3BcbiAgICAgKiBzaG9ydC1jaXJjdWl0cyBieSByZXR1cm5pbmcgYHVuZGVmaW5lZGAgaWYgdGhlIHBhdGggaXMgaW52YWxpZCBhdCBhbnkgcG9pbnQsXG4gICAgICogZXhjZXB0IGluIGBzZXRgIHNjZW5hcmlvIHdpdGggYGZvcmNlYCBlbmFibGVkLlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtICB7T2JqZWN0fSBvYmogICAgICAgIFRoZSBkYXRhIG9iamVjdCB0byBiZSByZWFkL3dyaXR0ZW5cbiAgICAgKiBAcGFyYW0gIHtTdHJpbmd9IHBhdGggICAgICAgVGhlIGtleXBhdGggd2hpY2ggYHJlc29sdmVQYXRoYCB3aWxsIGV2YWx1YXRlIGFnYWluc3QgYG9iamAuIE1heSBiZSBhIHByZS1jb21waWxlZCBUb2tlbnMgc2V0IGluc3RlYWQgb2YgYSBzdHJpbmcuXG4gICAgICogQHBhcmFtICB7QW55fSBuZXdWYWx1ZSAgIFRoZSBuZXcgdmFsdWUgdG8gc2V0IGF0IHRoZSBwb2ludCBkZXNjcmliZWQgYnkgYHBhdGhgLiBVbmRlZmluZWQgaWYgdXNlZCBpbiBgZ2V0YCBzY2VuYXJpby5cbiAgICAgKiBAcGFyYW0gIHtBcnJheX0gYXJncyAgICAgICBBcnJheSBvZiBleHRyYSBhcmd1bWVudHMgd2hpY2ggbWF5IGJlIHJlZmVyZW5jZWQgYnkgcGxhY2Vob2xkZXJzLiBVbmRlZmluZWQgaWYgbm8gZXh0cmEgYXJndW1lbnRzIHdlcmUgZ2l2ZW4uXG4gICAgICogQHBhcmFtICB7QXJyYXl9IHZhbHVlU3RhY2sgU3RhY2sgb2Ygb2JqZWN0IGNvbnRleHRzIGFjY3VtdWxhdGVkIGFzIHRoZSBwYXRoIHRva2VucyBhcmUgcHJvY2Vzc2VkIGluIGBvYmpgXG4gICAgICogQHJldHVybiB7QW55fSAgICAgICAgICAgIEluIGBnZXRgLCByZXR1cm5zIHRoZSB2YWx1ZSBmb3VuZCBpbiBgb2JqYCBhdCBgcGF0aGAuIEluIGBzZXRgLCByZXR1cm5zIHRoZSBuZXcgdmFsdWUgdGhhdCB3YXMgc2V0IGluIGBvYmpgLiBJZiBgZ2V0YCBvciBgc2V0YCBhcmUgbnRvIHN1Y2Nlc3NmdWwsIHJldHVybnMgYHVuZGVmaW5lZGBcbiAgICAgKi9cbiAgICB2YXIgcmVzb2x2ZVBhdGggPSBmdW5jdGlvbiAob2JqLCBwYXRoLCBuZXdWYWx1ZSwgYXJncywgdmFsdWVTdGFjayl7XG4gICAgICAgIHZhciBjaGFuZ2UgPSBuZXdWYWx1ZSAhPT0gVU5ERUYsIC8vIGFyZSB3ZSBzZXR0aW5nIGEgbmV3IHZhbHVlP1xuICAgICAgICAgICAgdGsgPSBbXSxcbiAgICAgICAgICAgIHRrTGVuZ3RoID0gMCxcbiAgICAgICAgICAgIHRrTGFzdElkeCA9IDAsXG4gICAgICAgICAgICB2YWx1ZVN0YWNrTGVuZ3RoID0gMSxcbiAgICAgICAgICAgIGkgPSAwLCBqID0gMCxcbiAgICAgICAgICAgIHByZXYgPSBvYmosXG4gICAgICAgICAgICBjdXJyID0gJycsXG4gICAgICAgICAgICBjdXJyTGVuZ3RoID0gMCxcbiAgICAgICAgICAgIGVhY2hMZW5ndGggPSAwLFxuICAgICAgICAgICAgd29yZENvcHkgPSAnJyxcbiAgICAgICAgICAgIGNvbnRleHRQcm9wLFxuICAgICAgICAgICAgaWR4ID0gMCxcbiAgICAgICAgICAgIGNvbnRleHQgPSBvYmosXG4gICAgICAgICAgICByZXQsXG4gICAgICAgICAgICBuZXdWYWx1ZUhlcmUgPSBmYWxzZSxcbiAgICAgICAgICAgIHBsYWNlSW50ID0gMCxcbiAgICAgICAgICAgIHByb3AgPSAnJyxcbiAgICAgICAgICAgIGNhbGxBcmdzO1xuXG4gICAgICAgIC8vIEZvciBTdHJpbmcgcGF0aCwgZWl0aGVyIGZldGNoIHRva2VucyBmcm9tIGNhY2hlIG9yIGZyb20gYHRva2VuaXplYC5cbiAgICAgICAgaWYgKHR5cGVvZiBwYXRoID09PSAkU1RSSU5HKXtcbiAgICAgICAgICAgIGlmIChvcHQudXNlQ2FjaGUgJiYgY2FjaGVbcGF0aF0pIHsgdGsgPSBjYWNoZVtwYXRoXS50OyB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0ayA9IHRva2VuaXplKHBhdGgpO1xuICAgICAgICAgICAgICAgIGlmICh0ayA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgdGsgPSB0ay50O1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIC8vIEZvciBhIG5vbi1zdHJpbmcsIGFzc3VtZSBhIHByZS1jb21waWxlZCB0b2tlbiBhcnJheVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRrID0gcGF0aC50ID8gcGF0aC50IDogW3BhdGhdO1xuICAgICAgICB9XG5cbiAgICAgICAgdGtMZW5ndGggPSB0ay5sZW5ndGg7XG4gICAgICAgIGlmICh0a0xlbmd0aCA9PT0gMCkgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgIHRrTGFzdElkeCA9IHRrTGVuZ3RoIC0gMTtcblxuICAgICAgICAvLyB2YWx1ZVN0YWNrIHdpbGwgYmUgYW4gYXJyYXkgaWYgd2UgYXJlIHdpdGhpbiBhIHJlY3Vyc2l2ZSBjYWxsIHRvIGByZXNvbHZlUGF0aGBcbiAgICAgICAgaWYgKHZhbHVlU3RhY2spe1xuICAgICAgICAgICAgdmFsdWVTdGFja0xlbmd0aCA9IHZhbHVlU3RhY2subGVuZ3RoO1xuICAgICAgICB9XG4gICAgICAgIC8vIE9uIG9yaWdpbmFsIGVudHJ5IHRvIGByZXNvbHZlUGF0aGAsIGluaXRpYWxpemUgdmFsdWVTdGFjayB3aXRoIHRoZSBiYXNlIG9iamVjdC5cbiAgICAgICAgLy8gdmFsdWVTdGFja0xlbmd0aCB3YXMgYWxyZWFkeSBpbml0aWFsaXplZCB0byAxLlxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHZhbHVlU3RhY2sgPSBbb2JqXTtcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIENvbnZlcnRlZCBBcnJheS5yZWR1Y2UgaW50byB3aGlsZSBsb29wLCBzdGlsbCB1c2luZyBcInByZXZcIiwgXCJjdXJyXCIsIFwiaWR4XCJcbiAgICAgICAgLy8gYXMgbG9vcCB2YWx1ZXNcbiAgICAgICAgd2hpbGUgKHByZXYgIT09IFVOREVGICYmIGlkeCA8IHRrTGVuZ3RoKXtcbiAgICAgICAgICAgIGN1cnIgPSB0a1tpZHhdO1xuXG4gICAgICAgICAgICAvLyBJZiB3ZSBhcmUgc2V0dGluZyBhIG5ldyB2YWx1ZSBhbmQgdGhpcyB0b2tlbiBpcyB0aGUgbGFzdCB0b2tlbiwgdGhpc1xuICAgICAgICAgICAgLy8gaXMgdGhlIHBvaW50IHdoZXJlIHRoZSBuZXcgdmFsdWUgbXVzdCBiZSBzZXQuXG4gICAgICAgICAgICBuZXdWYWx1ZUhlcmUgPSAoY2hhbmdlICYmIChpZHggPT09IHRrTGFzdElkeCkpO1xuXG4gICAgICAgICAgICAvLyBIYW5kbGUgbW9zdCBjb21tb24gc2ltcGxlIHBhdGggc2NlbmFyaW8gZmlyc3RcbiAgICAgICAgICAgIGlmICh0eXBlb2YgY3VyciA9PT0gJFNUUklORyl7XG4gICAgICAgICAgICAgICAgLy8gSWYgd2UgYXJlIHNldHRpbmcuLi5cbiAgICAgICAgICAgICAgICBpZiAoY2hhbmdlKXtcbiAgICAgICAgICAgICAgICAgICAgLy8gSWYgdGhpcyBpcyB0aGUgZmluYWwgdG9rZW4gd2hlcmUgdGhlIG5ldyB2YWx1ZSBnb2VzLCBzZXQgaXRcbiAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W2N1cnJdID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dFtjdXJyXSAhPT0gbmV3VmFsdWUpeyByZXR1cm4gdW5kZWZpbmVkOyB9IC8vIG5ldyB2YWx1ZSBmYWlsZWQgdG8gc2V0XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gRm9yIGVhcmxpZXIgdG9rZW5zLCBjcmVhdGUgb2JqZWN0IHByb3BlcnRpZXMgaWYgXCJmb3JjZVwiIGlzIGVuYWJsZWRcbiAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAob3B0LmZvcmNlICYmIHR5cGVvZiBjb250ZXh0W2N1cnJdID09PSAndW5kZWZpbmVkJykge1xuICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtjdXJyXSA9IHt9O1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIFJldHVybiB2YWx1ZSBpcyBhc3NpZ25lZCBhcyB2YWx1ZSBvZiB0aGlzIG9iamVjdCBwcm9wZXJ0eVxuICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHRbY3Vycl07XG5cbiAgICAgICAgICAgICAgICAvLyBUaGlzIGJhc2ljIHN0cnVjdHVyZSBpcyByZXBlYXRlZCBpbiBvdGhlciBzY2VuYXJpb3MgYmVsb3csIHNvIHRoZSBsb2dpY1xuICAgICAgICAgICAgICAgIC8vIHBhdHRlcm4gaXMgb25seSBkb2N1bWVudGVkIGhlcmUgZm9yIGJyZXZpdHkuXG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBpZiAoY3VyciA9PT0gVU5ERUYpe1xuICAgICAgICAgICAgICAgICAgICByZXQgPSB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKGN1cnIudHQpe1xuICAgICAgICAgICAgICAgICAgICAvLyBDYWxsIHJlc29sdmVQYXRoIGFnYWluIHdpdGggYmFzZSB2YWx1ZSBhcyBldmFsdWF0ZWQgdmFsdWUgc28gZmFyIGFuZFxuICAgICAgICAgICAgICAgICAgICAvLyBlYWNoIGVsZW1lbnQgb2YgYXJyYXkgYXMgdGhlIHBhdGguIENvbmNhdCBhbGwgdGhlIHJlc3VsdHMgdG9nZXRoZXIuXG4gICAgICAgICAgICAgICAgICAgIHJldCA9IFtdO1xuICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5kb0VhY2gpe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKCFBcnJheS5pc0FycmF5KGNvbnRleHQpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgaiA9IDA7XG4gICAgICAgICAgICAgICAgICAgICAgICBlYWNoTGVuZ3RoID0gY29udGV4dC5sZW5ndGg7XG4gICAgICAgICAgICAgICAgICAgICAgICBcbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIFBhdGggbGlrZSBBcnJheS0+RWFjaC0+QXJyYXkgcmVxdWlyZXMgYSBuZXN0ZWQgZm9yIGxvb3BcbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIHRvIHByb2Nlc3MgdGhlIHR3byBhcnJheSBsYXllcnMuXG4gICAgICAgICAgICAgICAgICAgICAgICB3aGlsZShqIDwgZWFjaExlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaSA9IDA7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goW10pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGN1cnJMZW5ndGggPSBjdXJyLnR0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB3aGlsZShpIDwgY3Vyckxlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGN1cnIudHRbaV0uZG9FYWNoID0gZmFsc2U7IC8vIFRoaXMgaXMgYSBoYWNrLCBkb24ndCBrbm93IGhvdyBlbHNlIHRvIGRpc2FibGUgXCJkb0VhY2hcIiBmb3IgY29sbGVjdGlvbiBtZW1iZXJzXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSByZXNvbHZlUGF0aChjb250ZXh0W2pdLCBjdXJyLnR0W2ldLCBuZXdWYWx1ZSwgYXJncywgdmFsdWVTdGFjayk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAodHlwZW9mIGN1cnIudHRbaV0gPT09ICdzdHJpbmcnKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gY29udGV4dFtqXVtjdXJyLnR0W2ldXTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gcmVzb2x2ZVBhdGgoY29udGV4dFtqXSwgY3Vyci50dFtpXSwgdW5kZWZpbmVkLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dFByb3AgPT09IFVOREVGKSB7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIudHRbaV0udCAmJiBjdXJyLnR0W2ldLmV4ZWMgPT09ICRFVkFMUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbal1bY29udGV4dFByb3BdID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldFtqXS5wdXNoKGNvbnRleHRQcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnR0W2ldLnQgJiYgY3Vyci50dFtpXS5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXRbal0ucHVzaChjb250ZXh0W2pdW2NvbnRleHRQcm9wXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldFtqXS5wdXNoKGNvbnRleHRQcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpKys7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGorKztcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGkgPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgY3Vyckxlbmd0aCA9IGN1cnIudHQubGVuZ3RoO1xuICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaSA8IGN1cnJMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0UHJvcCA9IHJlc29sdmVQYXRoKGNvbnRleHQsIGN1cnIudHRbaV0sIG5ld1ZhbHVlLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAodHlwZW9mIGN1cnIudHRbaV0gPT09ICdzdHJpbmcnKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSBjb250ZXh0W2N1cnIudHRbaV1dO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSByZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLnR0W2ldLCB1bmRlZmluZWQsIGFyZ3MsIHZhbHVlU3RhY2spO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dFByb3AgPT09IFVOREVGKSB7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICBcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIudHRbaV0udCAmJiBjdXJyLnR0W2ldLmV4ZWMgPT09ICRFVkFMUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtjb250ZXh0UHJvcF0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRQcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIudHRbaV0udCAmJiBjdXJyLnR0W2ldLmV4ZWMgPT09ICRFVkFMUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtjb250ZXh0UHJvcF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFByb3ApO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGkrKztcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChjdXJyLncpe1xuICAgICAgICAgICAgICAgICAgICAvLyB0aGlzIHdvcmQgdG9rZW4gaGFzIG1vZGlmaWVyc1xuICAgICAgICAgICAgICAgICAgICB3b3JkQ29weSA9IGN1cnIudztcbiAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5oYXMpe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5wYXJlbnQpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIG1vZGlmeSBjdXJyZW50IGNvbnRleHQsIHNoaWZ0IHVwd2FyZHMgaW4gYmFzZSBvYmplY3Qgb25lIGxldmVsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dCA9IHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDEgLSBjdXJyLm1vZHMucGFyZW50XTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dCA9PT0gVU5ERUYpIHsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5yb290KXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBSZXNldCBjb250ZXh0IGFuZCB2YWx1ZVN0YWNrLCBzdGFydCBvdmVyIGF0IHJvb3QgaW4gdGhpcyBjb250ZXh0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dCA9IHZhbHVlU3RhY2tbMF07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdmFsdWVTdGFjayA9IFtjb250ZXh0XTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB2YWx1ZVN0YWNrTGVuZ3RoID0gMTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMucGxhY2Vob2xkZXIpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHBsYWNlSW50ID0gd29yZENvcHkgLSAxO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChhcmdzW3BsYWNlSW50XSA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gRm9yY2UgYXJnc1twbGFjZUludF0gdG8gU3RyaW5nLCB3b24ndCBhdHRlbXB0IHRvIHByb2Nlc3NcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBhcmcgb2YgdHlwZSBmdW5jdGlvbiwgYXJyYXksIG9yIHBsYWluIG9iamVjdFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHdvcmRDb3B5ID0gYXJnc1twbGFjZUludF0udG9TdHJpbmcoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuXG4gICAgICAgICAgICAgICAgICAgIC8vIGRvRWFjaCBvcHRpb24gbWVhbnMgdG8gdGFrZSBhbGwgdmFsdWVzIGluIGNvbnRleHQgKG11c3QgYmUgYW4gYXJyYXkpLCBhcHBseVxuICAgICAgICAgICAgICAgICAgICAvLyBcImN1cnJcIiB0byBlYWNoIG9uZSwgYW5kIHJldHVybiB0aGUgbmV3IGFycmF5LiBPcGVyYXRlcyBsaWtlIEFycmF5Lm1hcC5cbiAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuZG9FYWNoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmICghQXJyYXkuaXNBcnJheShjb250ZXh0KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IFtdO1xuICAgICAgICAgICAgICAgICAgICAgICAgaSA9IDA7XG4gICAgICAgICAgICAgICAgICAgICAgICBlYWNoTGVuZ3RoID0gY29udGV4dC5sZW5ndGg7XG4gICAgICAgICAgICAgICAgICAgICAgICB3aGlsZShpIDwgZWFjaExlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gXCJjb250ZXh0XCIgbW9kaWZpZXIgKFwiQFwiIGJ5IGRlZmF1bHQpIHJlcGxhY2VzIGN1cnJlbnQgY29udGV4dCB3aXRoIGEgdmFsdWUgZnJvbVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHRoZSBhcmd1bWVudHMuXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5jb250ZXh0KXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGlzRGlnaXRzKHdvcmRDb3B5KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBwbGFjZUludCA9IHdvcmRDb3B5IC0gMTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChhcmdzW3BsYWNlSW50XSA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBGb3JjZSBhcmdzW3BsYWNlSW50XSB0byBTdHJpbmcsIHdvbid0IGF0d29yZENvcHl0IHRvIHByb2Nlc3NcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGFyZyBvZiB0eXBlIGZ1bmN0aW9uLCBhcnJheSwgb3IgcGxhaW4gb2JqZWN0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChhcmdzW3BsYWNlSW50XSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSB3b3JkQ29weTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gUmVwZWF0IGJhc2ljIHN0cmluZyBwcm9wZXJ0eSBwcm9jZXNzaW5nIHdpdGggd29yZCBhbmQgbW9kaWZpZWQgY29udGV4dFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dFtpXVt3b3JkQ29weV0gIT09IFVOREVGKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXsgY29udGV4dFtpXVt3b3JkQ29weV0gPSBuZXdWYWx1ZTsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXVt3b3JkQ29weV0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHR5cGVvZiBjb250ZXh0W2ldID09PSAnZnVuY3Rpb24nKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKHdvcmRDb3B5KTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBQbGFpbiBwcm9wZXJ0eSB0b2tlbnMgYXJlIGxpc3RlZCBhcyBzcGVjaWFsIHdvcmQgdG9rZW5zIHdoZW5ldmVyXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGEgd2lsZGNhcmQgaXMgZm91bmQgd2l0aGluIHRoZSBwcm9wZXJ0eSBzdHJpbmcuIEEgd2lsZGNhcmQgaW4gYVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBwcm9wZXJ0eSBjYXVzZXMgYW4gYXJyYXkgb2YgbWF0Y2hpbmcgcHJvcGVydGllcyB0byBiZSByZXR1cm5lZCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gc28gbG9vcCB0aHJvdWdoIGFsbCBwcm9wZXJ0aWVzIGFuZCBldmFsdWF0ZSB0b2tlbiBmb3IgZXZlcnlcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gcHJvcGVydHkgd2hlcmUgYHdpbGRDYXJkTWF0Y2hgIHJldHVybnMgdHJ1ZS5cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAod2lsZGNhcmRSZWdFeC50ZXN0KHdvcmRDb3B5KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChbXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBmb3IgKHByb3AgaW4gY29udGV4dFtpXSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHdpbGRDYXJkTWF0Y2god29yZENvcHksIHByb3ApKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7IGNvbnRleHRbaV1bcHJvcF0gPSBuZXdWYWx1ZTsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXRbaV0ucHVzaChjb250ZXh0W2ldW3Byb3BdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgLy8gXCJjb250ZXh0XCIgbW9kaWZpZXIgKFwiQFwiIGJ5IGRlZmF1bHQpIHJlcGxhY2VzIGN1cnJlbnQgY29udGV4dCB3aXRoIGEgdmFsdWUgZnJvbVxuICAgICAgICAgICAgICAgICAgICAgICAgLy8gdGhlIGFyZ3VtZW50cy5cbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMuY29udGV4dCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGlzRGlnaXRzKHdvcmRDb3B5KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHBsYWNlSW50ID0gd29yZENvcHkgLSAxO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoYXJnc1twbGFjZUludF0gPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBGb3JjZSBhcmdzW3BsYWNlSW50XSB0byBTdHJpbmcsIHdvbid0IGF0d29yZENvcHl0IHRvIHByb2Nlc3NcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gYXJnIG9mIHR5cGUgZnVuY3Rpb24sIGFycmF5LCBvciBwbGFpbiBvYmplY3RcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gYXJnc1twbGFjZUludF07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gd29yZENvcHk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gUmVwZWF0IGJhc2ljIHN0cmluZyBwcm9wZXJ0eSBwcm9jZXNzaW5nIHdpdGggd29yZCBhbmQgbW9kaWZpZWQgY29udGV4dFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjb250ZXh0W3dvcmRDb3B5XSAhPT0gVU5ERUYpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7IGNvbnRleHRbd29yZENvcHldID0gbmV3VmFsdWU7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dFt3b3JkQ29weV07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHR5cGVvZiBjb250ZXh0ID09PSAnZnVuY3Rpb24nKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IHdvcmRDb3B5O1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBQbGFpbiBwcm9wZXJ0eSB0b2tlbnMgYXJlIGxpc3RlZCBhcyBzcGVjaWFsIHdvcmQgdG9rZW5zIHdoZW5ldmVyXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gYSB3aWxkY2FyZCBpcyBmb3VuZCB3aXRoaW4gdGhlIHByb3BlcnR5IHN0cmluZy4gQSB3aWxkY2FyZCBpbiBhXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gcHJvcGVydHkgY2F1c2VzIGFuIGFycmF5IG9mIG1hdGNoaW5nIHByb3BlcnRpZXMgdG8gYmUgcmV0dXJuZWQsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gc28gbG9vcCB0aHJvdWdoIGFsbCBwcm9wZXJ0aWVzIGFuZCBldmFsdWF0ZSB0b2tlbiBmb3IgZXZlcnlcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBwcm9wZXJ0eSB3aGVyZSBgd2lsZENhcmRNYXRjaGAgcmV0dXJucyB0cnVlLlxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHdpbGRjYXJkUmVnRXgudGVzdCh3b3JkQ29weSkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZm9yIChwcm9wIGluIGNvbnRleHQpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHdpbGRDYXJkTWF0Y2god29yZENvcHksIHByb3ApKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXsgY29udGV4dFtwcm9wXSA9IG5ld1ZhbHVlOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtwcm9wXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBFdmFsIFByb3BlcnR5IHRva2VucyBvcGVyYXRlIG9uIGEgdGVtcG9yYXJ5IGNvbnRleHQgY3JlYXRlZCBieVxuICAgICAgICAgICAgICAgIC8vIHJlY3Vyc2l2ZWx5IGNhbGxpbmcgYHJlc29sdmVQYXRoYCB3aXRoIGEgY29weSBvZiB0aGUgdmFsdWVTdGFjay5cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChjdXJyLmV4ZWMgPT09ICRFVkFMUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5kb0VhY2gpe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKCFBcnJheS5pc0FycmF5KGNvbnRleHQpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gW107XG4gICAgICAgICAgICAgICAgICAgICAgICBpID0gMDtcbiAgICAgICAgICAgICAgICAgICAgICAgIGVhY2hMZW5ndGggPSBjb250ZXh0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdoaWxlKGkgPCBlYWNoTGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5zaW1wbGUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbaV1bX3RoaXMuZ2V0KGNvbnRleHRbaV0sIHt0OmN1cnIudCwgc2ltcGxlOnRydWV9KV0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldW190aGlzLmdldChjb250ZXh0W2ldLCB7dDpjdXJyLnQsIHNpbXBsZTp0cnVlfSldKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtpXVtyZXNvbHZlUGF0aChjb250ZXh0W2ldLCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayldID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXVtyZXNvbHZlUGF0aChjb250ZXh0W2ldLCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayldKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuc2ltcGxlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtfdGhpcy5nZXQoY29udGV4dCwge3Q6IGN1cnIudCwgc2ltcGxlOnRydWV9KV0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dFtfdGhpcy5nZXQoY29udGV4dCwge3Q6Y3Vyci50LCBzaW1wbGU6dHJ1ZX0pXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W3Jlc29sdmVQYXRoKGNvbnRleHQsIGN1cnIsIFVOREVGLCBhcmdzLCB2YWx1ZVN0YWNrKV0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dFtyZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayldO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIEZ1bmN0aW9ucyBhcmUgY2FsbGVkIHVzaW5nIGBjYWxsYCBvciBgYXBwbHlgLCBkZXBlbmRpbmcgb24gdGhlIHN0YXRlIG9mXG4gICAgICAgICAgICAgICAgLy8gdGhlIGFyZ3VtZW50cyB3aXRoaW4gdGhlICggKSBjb250YWluZXIuIEZ1bmN0aW9ucyBhcmUgZXhlY3V0ZWQgd2l0aCBcInRoaXNcIlxuICAgICAgICAgICAgICAgIC8vIHNldCB0byB0aGUgY29udGV4dCBpbW1lZGlhdGVseSBwcmlvciB0byB0aGUgZnVuY3Rpb24gaW4gdGhlIHN0YWNrLlxuICAgICAgICAgICAgICAgIC8vIEZvciBleGFtcGxlLCBcImEuYi5jLmZuKClcIiBpcyBlcXVpdmFsZW50IHRvIG9iai5hLmIuYy5mbi5jYWxsKG9iai5hLmIuYylcbiAgICAgICAgICAgICAgICBlbHNlIGlmIChjdXJyLmV4ZWMgPT09ICRDQUxMKXtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuZG9FYWNoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmICghQXJyYXkuaXNBcnJheSh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXSkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGkgPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgZWFjaExlbmd0aCA9IGNvbnRleHQubGVuZ3RoO1xuICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaSA8IGVhY2hMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIElmIGZ1bmN0aW9uIGNhbGwgaGFzIGFyZ3VtZW50cywgcHJvY2VzcyB0aG9zZSBhcmd1bWVudHMgYXMgYSBuZXcgcGF0aFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnQgJiYgY3Vyci50Lmxlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNhbGxBcmdzID0gcmVzb2x2ZVBhdGgoY29udGV4dCwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY2FsbEFyZ3MgPT09IFVOREVGKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbaV0uYXBwbHkodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl1baV0pKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChBcnJheS5pc0FycmF5KGNhbGxBcmdzKSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldLmFwcGx5KHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdW2ldLCBjYWxsQXJncykpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXS5jYWxsKHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdW2ldLCBjYWxsQXJncykpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldLmNhbGwodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl1baV0pKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgLy8gSWYgZnVuY3Rpb24gY2FsbCBoYXMgYXJndW1lbnRzLCBwcm9jZXNzIHRob3NlIGFyZ3VtZW50cyBhcyBhIG5ldyBwYXRoXG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci50ICYmIGN1cnIudC5sZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnNpbXBsZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNhbGxBcmdzID0gX3RoaXMuZ2V0KGNvbnRleHQsIGN1cnIpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY2FsbEFyZ3MgPSByZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjYWxsQXJncyA9PT0gVU5ERUYpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0LmFwcGx5KHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoQXJyYXkuaXNBcnJheShjYWxsQXJncykpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0LmFwcGx5KHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdLCBjYWxsQXJncyk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0LmNhbGwodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl0sIGNhbGxBcmdzKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0LmNhbGwodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gQWRkIHRoZSByZXR1cm4gdmFsdWUgdG8gdGhlIHN0YWNrIGluIGNhc2Ugd2UgbXVzdCBsb29wIGFnYWluLlxuICAgICAgICAgICAgLy8gUmVjdXJzaXZlIGNhbGxzIHBhc3MgdGhlIHNhbWUgdmFsdWVTdGFjayBhcnJheSBhcm91bmQsIGJ1dCB3ZSBkb24ndCB3YW50IHRvXG4gICAgICAgICAgICAvLyBwdXNoIGVudHJpZXMgb24gdGhlIHN0YWNrIGluc2lkZSBhIHJlY3Vyc2lvbiwgc28gaW5zdGVhZCB1c2UgZml4ZWQgYXJyYXlcbiAgICAgICAgICAgIC8vIGluZGV4IHJlZmVyZW5jZXMgYmFzZWQgb24gd2hhdCAqKnRoaXMqKiBleGVjdXRpb24ga25vd3MgdGhlIHZhbHVlU3RhY2tMZW5ndGhcbiAgICAgICAgICAgIC8vIHNob3VsZCBiZS4gVGhhdCB3YXksIGlmIGEgcmVjdXJzaW9uIGFkZHMgbmV3IGVsZW1lbnRzLCBhbmQgdGhlbiB3ZSBiYWNrIG91dCxcbiAgICAgICAgICAgIC8vIHRoaXMgY29udGV4dCB3aWxsIHJlbWVtYmVyIHRoZSBvbGQgc3RhY2sgbGVuZ3RoIGFuZCB3aWxsIG1lcmVseSBvdmVyd3JpdGVcbiAgICAgICAgICAgIC8vIHRob3NlIGFkZGVkIGVudHJpZXMsIGlnbm9yaW5nIHRoYXQgdGhleSB3ZXJlIHRoZXJlIGluIHRoZSBmaXJzdCBwbGFjZS5cbiAgICAgICAgICAgIHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCsrXSA9IHJldDtcbiAgICAgICAgICAgIGNvbnRleHQgPSByZXQ7XG4gICAgICAgICAgICBwcmV2ID0gcmV0O1xuICAgICAgICAgICAgaWR4Kys7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIGNvbnRleHQ7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNpbXBsaWZpZWQgcGF0aCBldmFsdWF0aW9uIGhlYXZpbHkgb3B0aW1pemVkIGZvciBwZXJmb3JtYW5jZSB3aGVuXG4gICAgICogcHJvY2Vzc2luZyBwYXRocyB3aXRoIG9ubHkgcHJvcGVydHkgbmFtZXMgb3IgaW5kaWNlcyBhbmQgc2VwYXJhdG9ycy5cbiAgICAgKiBJZiB0aGUgcGF0aCBjYW4gYmUgY29ycmVjdGx5IHByb2Nlc3NlZCB3aXRoIFwicGF0aC5zcGxpdChzZXBhcmF0b3IpXCIsXG4gICAgICogdGhpcyBmdW5jdGlvbiB3aWxsIGRvIHNvLiBBbnkgb3RoZXIgc3BlY2lhbCBjaGFyYWN0ZXJzIGZvdW5kIGluIHRoZVxuICAgICAqIHBhdGggd2lsbCBjYXVzZSB0aGUgcGF0aCB0byBiZSBldmFsdWF0ZWQgd2l0aCB0aGUgZnVsbCBgcmVzb2x2ZVBhdGhgXG4gICAgICogZnVuY3Rpb24gaW5zdGVhZC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSAge09iamVjdH0gb2JqICAgICAgICBUaGUgZGF0YSBvYmplY3QgdG8gYmUgcmVhZC93cml0dGVuXG4gICAgICogQHBhcmFtICB7U3RyaW5nfSBwYXRoICAgICAgIFRoZSBrZXlwYXRoIHdoaWNoIGByZXNvbHZlUGF0aGAgd2lsbCBldmFsdWF0ZSBhZ2FpbnN0IGBvYmpgLlxuICAgICAqIEBwYXJhbSAge0FueX0gbmV3VmFsdWUgICBUaGUgbmV3IHZhbHVlIHRvIHNldCBhdCB0aGUgcG9pbnQgZGVzY3JpYmVkIGJ5IGBwYXRoYC4gVW5kZWZpbmVkIGlmIHVzZWQgaW4gYGdldGAgc2NlbmFyaW8uXG4gICAgICogQHJldHVybiB7QW55fSAgICAgICAgICAgIEluIGBnZXRgLCByZXR1cm5zIHRoZSB2YWx1ZSBmb3VuZCBpbiBgb2JqYCBhdCBgcGF0aGAuIEluIGBzZXRgLCByZXR1cm5zIHRoZSBuZXcgdmFsdWUgdGhhdCB3YXMgc2V0IGluIGBvYmpgLiBJZiBgZ2V0YCBvciBgc2V0YCBhcmUgbnRvIHN1Y2Nlc3NmdWwsIHJldHVybnMgYHVuZGVmaW5lZGBcbiAgICAgKi9cbiAgICB2YXIgcXVpY2tSZXNvbHZlU3RyaW5nID0gZnVuY3Rpb24ob2JqLCBwYXRoLCBuZXdWYWx1ZSl7XG4gICAgICAgIHZhciBjaGFuZ2UgPSBuZXdWYWx1ZSAhPT0gVU5ERUYsXG4gICAgICAgICAgICB0ayA9IFtdLFxuICAgICAgICAgICAgaSA9IDAsXG4gICAgICAgICAgICB0a0xlbmd0aCA9IDA7XG5cbiAgICAgICAgdGsgPSBwYXRoLnNwbGl0KHByb3BlcnR5U2VwYXJhdG9yKTtcbiAgICAgICAgb3B0LnVzZUNhY2hlICYmIChjYWNoZVtwYXRoXSA9IHt0OiB0aywgc2ltcGxlOiB0cnVlfSk7XG4gICAgICAgIHRrTGVuZ3RoID0gdGsubGVuZ3RoO1xuICAgICAgICB3aGlsZSAob2JqICE9PSBVTkRFRiAmJiBpIDwgdGtMZW5ndGgpe1xuICAgICAgICAgICAgaWYgKHRrW2ldID09PSAnJyl7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgIGVsc2UgaWYgKGNoYW5nZSl7XG4gICAgICAgICAgICAgICAgaWYgKGkgPT09IHRrTGVuZ3RoIC0gMSl7XG4gICAgICAgICAgICAgICAgICAgIG9ialt0a1tpXV0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gRm9yIGFycmF5cywgdGVzdCBjdXJyZW50IGNvbnRleHQgYWdhaW5zdCB1bmRlZmluZWQgdG8gYXZvaWQgcGFyc2luZyB0aGlzIHNlZ21lbnQgYXMgYSBudW1iZXIuXG4gICAgICAgICAgICAgICAgLy8gRm9yIGFueXRoaW5nIGVsc2UsIHVzZSBoYXNPd25Qcm9wZXJ0eS5cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChvcHQuZm9yY2UgJiYgdHlwZW9mIG9ialt0a1tpXV0gPT09ICd1bmRlZmluZWQnKSB7XG4gICAgICAgICAgICAgICAgICAgIG9ialt0a1tpXV0gPSB7fTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBvYmogPSBvYmpbdGtbaSsrXV07XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG9iajtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2ltcGxpZmllZCBwYXRoIGV2YWx1YXRpb24gaGVhdmlseSBvcHRpbWl6ZWQgZm9yIHBlcmZvcm1hbmNlIHdoZW5cbiAgICAgKiBwcm9jZXNzaW5nIGFycmF5IG9mIHNpbXBsZSBwYXRoIHRva2VucyAocGxhaW4gcHJvcGVydHkgbmFtZXMpLlxuICAgICAqIFRoaXMgZnVuY3Rpb24gaXMgZXNzZW50aWFsbHkgdGhlIHNhbWUgYXMgYHF1aWNrUmVzb2x2ZVN0cmluZ2AgZXhjZXB0XG4gICAgICogYHF1aWNrUmVzb2x2ZVRva2VuQXJyYXlgIGRvZXMgbnRvIG5lZWQgdG8gZXhlY3V0ZSBwYXRoLnNwbGl0LlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtICB7T2JqZWN0fSBvYmogICAgICAgIFRoZSBkYXRhIG9iamVjdCB0byBiZSByZWFkL3dyaXR0ZW5cbiAgICAgKiBAcGFyYW0gIHtBcnJheX0gdGsgICAgICAgVGhlIHRva2VuIGFycmF5IHdoaWNoIGByZXNvbHZlUGF0aGAgd2lsbCBldmFsdWF0ZSBhZ2FpbnN0IGBvYmpgLlxuICAgICAqIEBwYXJhbSAge0FueX0gbmV3VmFsdWUgICBUaGUgbmV3IHZhbHVlIHRvIHNldCBhdCB0aGUgcG9pbnQgZGVzY3JpYmVkIGJ5IGBwYXRoYC4gVW5kZWZpbmVkIGlmIHVzZWQgaW4gYGdldGAgc2NlbmFyaW8uXG4gICAgICogQHJldHVybiB7QW55fSAgICAgICAgICAgIEluIGBnZXRgLCByZXR1cm5zIHRoZSB2YWx1ZSBmb3VuZCBpbiBgb2JqYCBhdCBgcGF0aGAuIEluIGBzZXRgLCByZXR1cm5zIHRoZSBuZXcgdmFsdWUgdGhhdCB3YXMgc2V0IGluIGBvYmpgLiBJZiBgZ2V0YCBvciBgc2V0YCBhcmUgbnRvIHN1Y2Nlc3NmdWwsIHJldHVybnMgYHVuZGVmaW5lZGBcbiAgICAgKi9cbiAgICB2YXIgcXVpY2tSZXNvbHZlVG9rZW5BcnJheSA9IGZ1bmN0aW9uKG9iaiwgdGssIG5ld1ZhbHVlKXtcbiAgICAgICAgdmFyIGNoYW5nZSA9IG5ld1ZhbHVlICE9PSBVTkRFRixcbiAgICAgICAgICAgIGkgPSAwLFxuICAgICAgICAgICAgdGtMZW5ndGggPSB0ay5sZW5ndGg7XG5cbiAgICAgICAgd2hpbGUgKG9iaiAhPSBudWxsICYmIGkgPCB0a0xlbmd0aCl7XG4gICAgICAgICAgICBpZiAodGtbaV0gPT09ICcnKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgZWxzZSBpZiAoY2hhbmdlKXtcbiAgICAgICAgICAgICAgICBpZiAoaSA9PT0gdGtMZW5ndGggLSAxKXtcbiAgICAgICAgICAgICAgICAgICAgb2JqW3RrW2ldXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBGb3IgYXJyYXlzLCB0ZXN0IGN1cnJlbnQgY29udGV4dCBhZ2FpbnN0IHVuZGVmaW5lZCB0byBhdm9pZCBwYXJzaW5nIHRoaXMgc2VnbWVudCBhcyBhIG51bWJlci5cbiAgICAgICAgICAgICAgICAvLyBGb3IgYW55dGhpbmcgZWxzZSwgdXNlIGhhc093blByb3BlcnR5LlxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKG9wdC5mb3JjZSAmJiB0eXBlb2Ygb2JqW3RrW2ldXSA9PT0gJ3VuZGVmaW5lZCcpIHtcbiAgICAgICAgICAgICAgICAgICAgb2JqW3RrW2ldXSA9IHt9O1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIG9iaiA9IG9ialt0a1tpKytdXTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gb2JqO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTZWFyY2hlcyBhbiBvYmplY3Qgb3IgYXJyYXkgZm9yIGEgdmFsdWUsIGFjY3VtdWxhdGluZyB0aGUga2V5cGF0aCB0byB0aGUgdmFsdWUgYWxvbmdcbiAgICAgKiB0aGUgd2F5LiBPcGVyYXRlcyBpbiBhIHJlY3Vyc2l2ZSB3YXkgdW50aWwgZWl0aGVyIGFsbCBrZXlzL2luZGljZXMgaGF2ZSBiZWVuXG4gICAgICogZXhoYXVzdGVkIG9yIGEgbWF0Y2ggaXMgZm91bmQuIFJldHVybiB2YWx1ZSBcInRydWVcIiBtZWFucyBcImtlZXAgc2Nhbm5pbmdcIiwgXCJmYWxzZVwiXG4gICAgICogbWVhbnMgXCJzdG9wIG5vd1wiLiBJZiBhIG1hdGNoIGlzIGZvdW5kLCBpbnN0ZWFkIG9mIHJldHVybmluZyBhIHNpbXBsZSBcImZhbHNlXCIsIGFcbiAgICAgKiBjYWxsYmFjayBmdW5jdGlvbiAoc2F2ZVBhdGgpIGlzIGNhbGxlZCB3aGljaCB3aWxsIGRlY2lkZSB3aGV0aGVyIG9yIG5vdCB0byBjb250aW51ZVxuICAgICAqIHRoZSBzY2FuLiBUaGlzIGFsbG93cyB0aGUgZnVuY3Rpb24gdG8gZmluZCBvbmUgaW5zdGFuY2Ugb2YgdmFsdWUgb3IgYWxsIGluc3RhbmNlcyxcbiAgICAgKiBiYXNlZCBvbiBsb2dpYyBpbiB0aGUgY2FsbGJhY2suXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0ge09iamVjdH0gb2JqICAgIFRoZSBkYXRhIG9iamVjdCB0byBzY2FuXG4gICAgICogQHBhcmFtIHtBbnl9IHZhbCBUaGUgdmFsdWUgd2UgYXJlIGxvb2tpbmcgZm9yIHdpdGhpbiBgb2JqYFxuICAgICAqIEBwYXJhbSB7RnVuY3Rpb259IHNhdmVQYXRoIENhbGxiYWNrIGZ1bmN0aW9uIHdoaWNoIHdpbGwgc3RvcmUgYWNjdW11bGF0ZWQgcGF0aHMgYW5kIGluZGljYXRlIHdoZXRoZXIgdG8gY29udGludWVcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBBY2N1bXVsYXRlZCBrZXlwYXRoOyB1bmRlZmluZWQgYXQgZmlyc3QsIHBvcHVsYXRlZCBpbiByZWN1cnNpdmUgY2FsbHNcbiAgICAgKiBAcmV0dXJuIHtCb29sZWFufSBJbmRpY2F0ZXMgd2hldGhlciBzY2FuIHByb2Nlc3Mgc2hvdWxkIGNvbnRpbnVlIChcInRydWVcIi0+eWVzLCBcImZhbHNlXCItPm5vKVxuICAgICAqL1xuICAgIHZhciBzY2FuRm9yVmFsdWUgPSBmdW5jdGlvbihvYmosIHZhbCwgc2F2ZVBhdGgsIHBhdGgpe1xuICAgICAgICB2YXIgaSwgbGVuLCBtb3JlLCBrZXlzLCBwcm9wO1xuXG4gICAgICAgIHBhdGggPSBwYXRoID8gcGF0aCA6ICcnO1xuXG4gICAgICAgIC8vIElmIHdlIGZvdW5kIHRoZSB2YWx1ZSB3ZSdyZSBsb29raW5nIGZvclxuICAgICAgICBpZiAob2JqID09PSB2YWwpe1xuICAgICAgICAgICAgcmV0dXJuIHNhdmVQYXRoKHBhdGgpOyAvLyBTYXZlIHRoZSBhY2N1bXVsYXRlZCBwYXRoLCBhc2sgd2hldGhlciB0byBjb250aW51ZVxuICAgICAgICB9XG4gICAgICAgIC8vIFRoaXMgb2JqZWN0IGlzIGFuIGFycmF5LCBzbyBleGFtaW5lIGVhY2ggaW5kZXggc2VwYXJhdGVseVxuICAgICAgICBlbHNlIGlmIChBcnJheS5pc0FycmF5KG9iaikpe1xuICAgICAgICAgICAgbGVuID0gb2JqLmxlbmd0aDtcbiAgICAgICAgICAgIGZvcihpID0gMDsgaSA8IGxlbjsgaSsrKXtcbiAgICAgICAgICAgICAgICAvLyBDYWxsIGBzY2FuRm9yVmFsdWVgIHJlY3Vyc2l2ZWx5XG4gICAgICAgICAgICAgICAgbW9yZSA9IHNjYW5Gb3JWYWx1ZShvYmpbaV0sIHZhbCwgc2F2ZVBhdGgsIHBhdGggKyBwcm9wZXJ0eVNlcGFyYXRvciArIGkpO1xuICAgICAgICAgICAgICAgIC8vIEhhbHQgaWYgdGhhdCByZWN1cnNpdmUgY2FsbCByZXR1cm5lZCBcImZhbHNlXCJcbiAgICAgICAgICAgICAgICBpZiAoIW1vcmUpeyByZXR1cm47IH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlOyAvLyBrZWVwIGxvb2tpbmdcbiAgICAgICAgfVxuICAgICAgICAvLyBUaGlzIG9iamVjdCBpcyBhbiBvYmplY3QsIHNvIGV4YW1pbmUgZWFjaCBsb2NhbCBwcm9wZXJ0eSBzZXBhcmF0ZWx5XG4gICAgICAgIGVsc2UgaWYgKGlzT2JqZWN0KG9iaikpIHtcbiAgICAgICAgICAgIGtleXMgPSBPYmplY3Qua2V5cyhvYmopO1xuICAgICAgICAgICAgbGVuID0ga2V5cy5sZW5ndGg7XG4gICAgICAgICAgICBpZiAobGVuID4gMSl7IGtleXMgPSBrZXlzLnNvcnQoKTsgfSAvLyBGb3JjZSBvcmRlciBvZiBvYmplY3Qga2V5cyB0byBwcm9kdWNlIHJlcGVhdGFibGUgcmVzdWx0c1xuICAgICAgICAgICAgZm9yIChpID0gMDsgaSA8IGxlbjsgaSsrKXtcbiAgICAgICAgICAgICAgICBpZiAob2JqLmhhc093blByb3BlcnR5KGtleXNbaV0pKXtcbiAgICAgICAgICAgICAgICAgICAgcHJvcCA9IGtleXNbaV07XG4gICAgICAgICAgICAgICAgICAgIC8vIFByb3BlcnR5IG1heSBpbmNsdWRlIHRoZSBzZXBhcmF0b3IgY2hhcmFjdGVyIG9yIHNvbWUgb3RoZXIgc3BlY2lhbCBjaGFyYWN0ZXIsXG4gICAgICAgICAgICAgICAgICAgIC8vIHNvIHF1b3RlIHRoaXMgcGF0aCBzZWdtZW50IGFuZCBlc2NhcGUgYW55IHNlcGFyYXRvcnMgd2l0aGluLlxuICAgICAgICAgICAgICAgICAgICBpZiAoYWxsU3BlY2lhbHNSZWdFeC50ZXN0KHByb3ApKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIHByb3AgPSBxdW90ZVN0cmluZyhzaW5nbGVxdW90ZSwgcHJvcCk7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgbW9yZSA9IHNjYW5Gb3JWYWx1ZShvYmpba2V5c1tpXV0sIHZhbCwgc2F2ZVBhdGgsIHBhdGggKyBwcm9wZXJ0eVNlcGFyYXRvciArIHByb3ApO1xuICAgICAgICAgICAgICAgICAgICBpZiAoIW1vcmUpeyByZXR1cm47IH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTsgLy8ga2VlcCBsb29raW5nXG4gICAgICAgIH1cbiAgICAgICAgLy8gTGVhZiBub2RlIChzdHJpbmcsIG51bWJlciwgY2hhcmFjdGVyLCBib29sZWFuLCBldGMuKSwgYnV0IGRpZG4ndCBtYXRjaFxuICAgICAgICByZXR1cm4gdHJ1ZTsgLy8ga2VlcCBsb29raW5nXG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEdldCB0b2tlbml6ZWQgcmVwcmVzZW50YXRpb24gb2Ygc3RyaW5nIGtleXBhdGguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBwYXRoIEtleXBhdGhcbiAgICAgKiBAcmV0dXJuIHtPYmplY3R9IE9iamVjdCBpbmNsdWRpbmcgdGhlIGFycmF5IG9mIHBhdGggdG9rZW5zIGFuZCBhIGJvb2xlYW4gaW5kaWNhdGluZyBcInNpbXBsZVwiLiBTaW1wbGUgdG9rZW4gc2V0cyBoYXZlIG5vIHNwZWNpYWwgb3BlcmF0b3JzIG9yIG5lc3RlZCB0b2tlbnMsIG9ubHkgYSBwbGFpbiBhcnJheSBvZiBzdHJpbmdzIGZvciBmYXN0IGV2YWx1YXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuZ2V0VG9rZW5zID0gZnVuY3Rpb24ocGF0aCl7XG4gICAgICAgIHZhciB0b2tlbnMgPSB0b2tlbml6ZShwYXRoKTtcbiAgICAgICAgaWYgKHR5cGVvZiB0b2tlbnMgPT09ICRVTkRFRklORUQpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgIHJldHVybiB0b2tlbnM7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEluZm9ybXMgd2hldGhlciB0aGUgc3RyaW5nIHBhdGggaGFzIHZhbGlkIHN5bnRheC4gVGhlIHBhdGggaXMgTk9UIGV2YWx1YXRlZCBhZ2FpbnN0IGFcbiAgICAgKiBkYXRhIG9iamVjdCwgb25seSB0aGUgc3ludGF4IGlzIGNoZWNrZWQuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBwYXRoIEtleXBhdGhcbiAgICAgKiBAcmV0dXJuIHtCb29sZWFufSB2YWxpZCBzeW50YXggLT4gXCJ0cnVlXCI7IG5vdCB2YWxpZCAtPiBcImZhbHNlXCJcbiAgICAgKi9cbiAgICBfdGhpcy5pc1ZhbGlkID0gZnVuY3Rpb24ocGF0aCl7XG4gICAgICAgIHJldHVybiB0eXBlb2YgdG9rZW5pemUocGF0aCkgIT09ICRVTkRFRklORUQ7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEVzY2FwZXMgYW55IHNwZWNpYWwgY2hhcmFjdGVycyBmb3VuZCBpbiB0aGUgaW5wdXQgc3RyaW5nIHVzaW5nIGJhY2tzbGFzaCwgcHJldmVudGluZ1xuICAgICAqIHRoZXNlIGNoYXJhY3RlcnMgZnJvbSBjYXVzaW5nIHVuaW50ZW5kZWQgcHJvY2Vzc2luZyBieSBQYXRoVG9vbGtpdC4gVGhpcyBmdW5jdGlvblxuICAgICAqIERPRVMgcmVzcGVjdCB0aGUgY3VycmVudCBjb25maWd1cmVkIHN5bnRheCwgZXZlbiBpZiBpdCBoYXMgYmVlbiBhbHRlcmVkIGZyb20gdGhlIGRlZmF1bHQuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBzZWdtZW50IFNlZ21lbnQgb2YgYSBrZXlwYXRoXG4gICAgICogQHJldHVybiB7U3RyaW5nfSBUaGUgb3JpZ2luYWwgc2VnbWVudCBzdHJpbmcgd2l0aCBhbGwgUGF0aFRvb2xraXQgc3BlY2lhbCBjaGFyYWN0ZXJzIHByZXBlbmRlZCB3aXRoIFwiXFxcIlxuICAgICAqL1xuICAgIF90aGlzLmVzY2FwZSA9IGZ1bmN0aW9uKHNlZ21lbnQpe1xuICAgICAgICByZXR1cm4gc2VnbWVudC5yZXBsYWNlKGFsbFNwZWNpYWxzUmVnRXgsICdcXFxcJCYnKTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogRXZhbHVhdGVzIGtleXBhdGggaW4gb2JqZWN0IGFuZCByZXR1cm5zIHRoZSB2YWx1ZSBmb3VuZCB0aGVyZSwgaWYgYXZhaWxhYmxlLiBJZiB0aGUgcGF0aFxuICAgICAqIGRvZXMgbm90IGV4aXN0IGluIHRoZSBwcm92aWRlZCBkYXRhIG9iamVjdCwgcmV0dXJucyBgdW5kZWZpbmVkYC4gRm9yIFwic2ltcGxlXCIgcGF0aHMsIHdoaWNoXG4gICAgICogZG9uJ3QgaW5jbHVkZSBhbnkgb3BlcmF0aW9ucyBiZXlvbmQgcHJvcGVydHkgc2VwYXJhdG9ycywgb3B0aW1pemVkIHJlc29sdmVycyB3aWxsIGJlIHVzZWRcbiAgICAgKiB3aGljaCBhcmUgbW9yZSBsaWdodHdlaWdodCB0aGFuIHRoZSBmdWxsLWZlYXR1cmVkIGByZXNvbHZlUGF0aGAuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSBvYmogU291cmNlIGRhdGEgb2JqZWN0XG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHBhdGggS2V5cGF0aCB0byBldmFsdWF0ZSB3aXRoaW4gXCJvYmpcIi4gQWxzbyBhY2NlcHRzIHRva2VuIGFycmF5IGluIHBsYWNlIG9mIGEgc3RyaW5nIHBhdGguXG4gICAgICogQHJldHVybiB7QW55fSBJZiB0aGUga2V5cGF0aCBleGlzdHMgaW4gXCJvYmpcIiwgcmV0dXJuIHRoZSB2YWx1ZSBhdCB0aGF0IGxvY2F0aW9uOyBJZiBub3QsIHJldHVybiBgdW5kZWZpbmVkYC5cbiAgICAgKi9cbiAgICBfdGhpcy5nZXQgPSBmdW5jdGlvbiAob2JqLCBwYXRoKXtcbiAgICAgICAgdmFyIGkgPSAwLFxuICAgICAgICAgICAgbGVuID0gYXJndW1lbnRzLmxlbmd0aCxcbiAgICAgICAgICAgIGFyZ3M7XG4gICAgICAgIC8vIEZvciBzdHJpbmcgcGF0aHMsIGZpcnN0IHNlZSBpZiBwYXRoIGhhcyBhbHJlYWR5IGJlZW4gY2FjaGVkIGFuZCBpZiB0aGUgdG9rZW4gc2V0IGlzIHNpbXBsZS4gSWZcbiAgICAgICAgLy8gc28sIHdlIGNhbiB1c2UgdGhlIG9wdGltaXplZCB0b2tlbiBhcnJheSByZXNvbHZlciB1c2luZyB0aGUgY2FjaGVkIHRva2VuIHNldC5cbiAgICAgICAgLy8gSWYgdGhlcmUgaXMgbm8gY2FjaGVkIGVudHJ5LCB1c2UgUmVnRXggdG8gbG9vayBmb3Igc3BlY2lhbCBjaGFyYWN0ZXJzIGFwYXJ0IGZyb20gdGhlIHNlcGFyYXRvci5cbiAgICAgICAgLy8gSWYgbm9uZSBhcmUgZm91bmQsIHdlIGNhbiB1c2UgdGhlIG9wdGltaXplZCBzdHJpbmcgcmVzb2x2ZXIuXG4gICAgICAgIGlmICh0eXBlb2YgcGF0aCA9PT0gJFNUUklORyl7XG4gICAgICAgICAgICBpZiAob3B0LnVzZUNhY2hlICYmIGNhY2hlW3BhdGhdICYmIGNhY2hlW3BhdGhdLnNpbXBsZSl7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHF1aWNrUmVzb2x2ZVRva2VuQXJyYXkob2JqLCBjYWNoZVtwYXRoXS50KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKCFzaW1wbGVQYXRoUmVnRXgudGVzdChwYXRoKSl7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHF1aWNrUmVzb2x2ZVN0cmluZyhvYmosIHBhdGgpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIC8vIEZvciBhcnJheSBwYXRocyAocHJlLWNvbXBpbGVkIHRva2VuIHNldHMpLCBjaGVjayBmb3Igc2ltcGxpY2l0eSBzbyB3ZSBjYW4gdXNlIHRoZSBvcHRpbWl6ZWQgcmVzb2x2ZXIuXG4gICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkocGF0aC50KSAmJiBwYXRoLnNpbXBsZSl7XG4gICAgICAgICAgICByZXR1cm4gcXVpY2tSZXNvbHZlVG9rZW5BcnJheShvYmosIHBhdGgudCk7XG4gICAgICAgIH1cbiAgICAgICAgXG4gICAgICAgIC8vIElmIHdlIG1hZGUgaXQgdGhpcyBmYXIsIHRoZSBwYXRoIGlzIGNvbXBsZXggYW5kIG1heSBpbmNsdWRlIHBsYWNlaG9sZGVycy4gR2F0aGVyIHVwIGFueVxuICAgICAgICAvLyBleHRyYSBhcmd1bWVudHMgYW5kIGNhbGwgdGhlIGZ1bGwgYHJlc29sdmVQYXRoYCBmdW5jdGlvbi5cbiAgICAgICAgYXJncyA9IFtdO1xuICAgICAgICBpZiAobGVuID4gMil7XG4gICAgICAgICAgICBmb3IgKGkgPSAyOyBpIDwgbGVuOyBpKyspIHsgYXJnc1tpLTJdID0gYXJndW1lbnRzW2ldOyB9XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHJlc29sdmVQYXRoKG9iaiwgcGF0aCwgdW5kZWZpbmVkLCBhcmdzKTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogRXZhbHVhdGVzIGEga2V5cGF0aCBpbiBvYmplY3QgYW5kIHNldHMgYSBuZXcgdmFsdWUgYXQgdGhlIHBvaW50IGRlc2NyaWJlZCBpbiB0aGUga2V5cGF0aC4gSWZcbiAgICAgKiBcImZvcmNlXCIgaXMgZGlzYWJsZWQsIHRoZSBmdWxsIHBhdGggbXVzdCBleGlzdCB1cCB0byB0aGUgZmluYWwgcHJvcGVydHksIHdoaWNoIG1heSBiZSBjcmVhdGVkXG4gICAgICogYnkgdGhlIHNldCBvcGVyYXRpb24uIElmIFwiZm9yY2VcIiBpcyBlbmFibGVkLCBhbnkgbWlzc2luZyBpbnRlcm1lZGlhdGUgcHJvcGVydGllcyB3aWxsIGJlIGNyZWF0ZWRcbiAgICAgKiBpbiBvcmRlciB0byBzZXQgdGhlIHZhbHVlIG9uIHRoZSBmaW5hbCBwcm9wZXJ0eS4gSWYgYHNldGAgc3VjY2VlZHMsIHJldHVybnMgXCJ0cnVlXCIsIG90aGVyd2lzZSBcImZhbHNlXCIuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSBvYmogU291cmNlIGRhdGEgb2JqZWN0XG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHBhdGggS2V5cGF0aCB0byBldmFsdWF0ZSB3aXRoaW4gXCJvYmpcIi4gQWxzbyBhY2NlcHRzIHRva2VuIGFycmF5IGluIHBsYWNlIG9mIGEgc3RyaW5nIHBhdGguXG4gICAgICogQHBhcmFtIHtBbnl9IHZhbCBOZXcgdmFsdWUgdG8gc2V0IGF0IHRoZSBsb2NhdGlvbiBkZXNjcmliZWQgaW4gXCJwYXRoXCJcbiAgICAgKiBAcmV0dXJuIHtCb29sZWFufSBcInRydWVcIiBpZiB0aGUgc2V0IG9wZXJhdGlvbiBzdWNjZWVkczsgXCJmYWxzZVwiIGlmIGl0IGRvZXMgbm90IHN1Y2NlZWRcbiAgICAgKi9cbiAgICBfdGhpcy5zZXQgPSBmdW5jdGlvbihvYmosIHBhdGgsIHZhbCl7XG4gICAgICAgIHZhciBpID0gMCxcbiAgICAgICAgICAgIGxlbiA9IGFyZ3VtZW50cy5sZW5ndGgsXG4gICAgICAgICAgICBhcmdzLFxuICAgICAgICAgICAgcmVmLFxuICAgICAgICAgICAgZG9uZSA9IGZhbHNlO1xuICAgICAgICAgICAgXG4gICAgICAgIC8vIFBhdGggcmVzb2x1dGlvbiBmb2xsb3dzIHRoZSBzYW1lIGxvZ2ljIGFzIGBnZXRgIGFib3ZlLCB3aXRoIG9uZSBkaWZmZXJlbmNlOiBgZ2V0YCB3aWxsXG4gICAgICAgIC8vIGFib3J0IGJ5IHJldHVybmluZyB0aGUgdmFsdWUgYXMgc29vbiBhcyBpdCdzIGZvdW5kLiBgc2V0YCBkb2VzIG5vdCBhYm9ydCBzbyB0aGUgaWYtZWxzZVxuICAgICAgICAvLyBzdHJ1Y3R1cmUgaXMgc2xpZ2h0bHkgZGlmZmVyZW50IHRvIGRpY3RhdGUgd2hlbi9pZiB0aGUgZmluYWwgY2FzZSBzaG91bGQgZXhlY3V0ZS5cbiAgICAgICAgaWYgKHR5cGVvZiBwYXRoID09PSAkU1RSSU5HKXtcbiAgICAgICAgICAgIGlmIChvcHQudXNlQ2FjaGUgJiYgY2FjaGVbcGF0aF0gJiYgY2FjaGVbcGF0aF0uc2ltcGxlKXtcbiAgICAgICAgICAgICAgICByZWYgPSBxdWlja1Jlc29sdmVUb2tlbkFycmF5KG9iaiwgY2FjaGVbcGF0aF0udCwgdmFsKTtcbiAgICAgICAgICAgICAgICBkb25lIHw9IHRydWU7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmICghc2ltcGxlUGF0aFJlZ0V4LnRlc3QocGF0aCkpe1xuICAgICAgICAgICAgICAgIHJlZiA9IHF1aWNrUmVzb2x2ZVN0cmluZyhvYmosIHBhdGgsIHZhbCk7XG4gICAgICAgICAgICAgICAgZG9uZSB8PSB0cnVlO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkocGF0aC50KSAmJiBwYXRoLnNpbXBsZSl7XG4gICAgICAgICAgICByZWYgPSBxdWlja1Jlc29sdmVUb2tlbkFycmF5KG9iaiwgcGF0aC50LCB2YWwpO1xuICAgICAgICAgICAgZG9uZSB8PSB0cnVlO1xuICAgICAgICB9XG4gICAgICAgIFxuICAgICAgICAvLyBQYXRoIHdhcyAocHJvYmFibHkpIGEgc3RyaW5nIGFuZCBpdCBjb250YWluZWQgY29tcGxleCBwYXRoIGNoYXJhY3RlcnNcbiAgICAgICAgaWYgKCFkb25lKSB7XG4gICAgICAgICAgICBpZiAobGVuID4gMyl7XG4gICAgICAgICAgICAgICAgYXJncyA9IFtdO1xuICAgICAgICAgICAgICAgIGZvciAoaSA9IDM7IGkgPCBsZW47IGkrKykgeyBhcmdzW2ktM10gPSBhcmd1bWVudHNbaV07IH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJlZiA9IHJlc29sdmVQYXRoKG9iaiwgcGF0aCwgdmFsLCBhcmdzKTtcbiAgICAgICAgfVxuICAgICAgICBcbiAgICAgICAgLy8gYHNldGAgY2FuIHNldCBhIG5ldyB2YWx1ZSBpbiBtdWx0aXBsZSBwbGFjZXMgaWYgdGhlIGZpbmFsIHBhdGggc2VnbWVudCBpcyBhbiBhcnJheS5cbiAgICAgICAgLy8gSWYgYW55IG9mIHRob3NlIHZhbHVlIGFzc2lnbm1lbnRzIGZhaWwsIGBzZXRgIHdpbGwgcmV0dXJuIFwiZmFsc2VcIiBpbmRpY2F0aW5nIGZhaWx1cmUuXG4gICAgICAgIGlmIChBcnJheS5pc0FycmF5KHJlZikpe1xuICAgICAgICAgICAgcmV0dXJuIHJlZi5pbmRleE9mKHVuZGVmaW5lZCkgPT09IC0xO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiByZWYgIT09IFVOREVGO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBMb2NhdGUgYSB2YWx1ZSB3aXRoaW4gYW4gb2JqZWN0IG9yIGFycmF5LiBUaGlzIGlzIHRoZSBwdWJsaWNseSBleHBvc2VkIGludGVyZmFjZSB0byB0aGVcbiAgICAgKiBwcml2YXRlIGBzY2FuRm9yVmFsdWVgIGZ1bmN0aW9uIGRlZmluZWQgYWJvdmUuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSBvYmogU291cmNlIGRhdGEgb2JqZWN0XG4gICAgICogQHBhcmFtIHtBbnl9IHZhbCBUaGUgdmFsdWUgdG8gc2VhcmNoIGZvciB3aXRoaW4gXCJvYmpcIlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBvbmVPck1hbnkgT3B0aW9uYWw7IElmIG1pc3Npbmcgb3IgXCJvbmVcIiwgYGZpbmRgIHdpbGwgb25seSByZXR1cm4gdGhlIGZpcnN0IHZhbGlkIHBhdGguIElmIFwib25Pck1hbnlcIiBpcyBhbnkgb3RoZXIgc3RyaW5nLCBgZmluZGAgd2lsbCBzY2FuIHRoZSBmdWxsIG9iamVjdCBsb29raW5nIGZvciBhbGwgdmFsaWQgcGF0aHMgdG8gYWxsIGNhc2VzIHdoZXJlIFwidmFsXCIgYXBwZWFycy5cbiAgICAgKiBAcmV0dXJuIHtBcnJheX0gQXJyYXkgb2Yga2V5cGF0aHMgdG8gXCJ2YWxcIiBvciBgdW5kZWZpbmVkYCBpZiBcInZhbFwiIGlzIG5vdCBmb3VuZC5cbiAgICAgKi9cbiAgICBfdGhpcy5maW5kID0gZnVuY3Rpb24ob2JqLCB2YWwsIG9uZU9yTWFueSl7XG4gICAgICAgIHZhciByZXRWYWwgPSBbXTtcbiAgICAgICAgLy8gc2F2ZVBhdGggaXMgdGhlIGNhbGxiYWNrIHdoaWNoIHdpbGwgYWNjdW11bGF0ZSBhbnkgZm91bmQgcGF0aHMgaW4gYSBsb2NhbCBhcnJheVxuICAgICAgICAvLyB2YXJpYWJsZS5cbiAgICAgICAgdmFyIHNhdmVQYXRoID0gZnVuY3Rpb24ocGF0aCl7XG4gICAgICAgICAgICByZXRWYWwucHVzaChwYXRoLnN1YnN0cigxKSk7XG4gICAgICAgICAgICBpZighb25lT3JNYW55IHx8IG9uZU9yTWFueSA9PT0gJ29uZScpe1xuICAgICAgICAgICAgICAgIHJldFZhbCA9IHJldFZhbFswXTtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfTtcbiAgICAgICAgc2NhbkZvclZhbHVlKG9iaiwgdmFsLCBzYXZlUGF0aCk7XG4gICAgICAgIHJldHVybiByZXRWYWxbMF0gPyByZXRWYWwgOiB1bmRlZmluZWQ7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEZvciBhIGdpdmVuIHNwZWNpYWwgY2hhcmFjdGVyIGdyb3VwIChlLmcuLCBzZXBhcmF0b3JzKSBhbmQgY2hhcmFjdGVyIHR5cGUgKGUuZy4sIFwicHJvcGVydHlcIiksXG4gICAgICogcmVwbGFjZSBhbiBleGlzdGluZyBzZXBhcmF0b3Igd2l0aCBhIG5ldyBjaGFyYWN0ZXIuIFRoaXMgY3JlYXRlcyBhIG5ldyBzcGVjaWFsIGNoYXJhY3RlciBmb3JcbiAgICAgKiB0aGF0IHB1cnBvc2UgYW53aXRoaW4gdGhlIGNoYXJhY3RlciBncm91cCBhbmQgcmVtb3ZlcyB0aGUgb2xkIG9uZS4gQWxzbyB0YWtlcyBhIFwiY2xvc2VyXCIgYXJndW1lbnRcbiAgICAgKiBmb3IgY2FzZXMgd2hlcmUgdGhlIHNwZWNpYWwgY2hhcmFjdGVyIGlzIGEgY29udGFpbmVyIHNldC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSB7T2JqZWN0fSBvcHRpb25Hcm91cCBSZWZlcmVuY2UgdG8gY3VycmVudCBjb25maWd1cmF0aW9uIGZvciBhIGNlcnRhaW4gdHlwZSBvZiBzcGVjaWFsIGNoYXJhY3RlcnNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gY2hhclR5cGUgVGhlIHR5cGUgb2Ygc3BlY2lhbCBjaGFyYWN0ZXIgdG8gYmUgcmVwbGFjZWRcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBzcGVjaWFsIGNoYXJhY3RlciBzdHJpbmdcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gY2xvc2VyIE9wdGlvbmFsOyBOZXcgc3BlY2lhbCBjaGFyYWN0ZXIgY2xvc2VyIHN0cmluZywgb25seSB1c2VkIGZvciBcImNvbnRhaW5lcnNcIiBncm91cFxuICAgICAqL1xuICAgIHZhciB1cGRhdGVPcHRpb25DaGFyID0gZnVuY3Rpb24ob3B0aW9uR3JvdXAsIGNoYXJUeXBlLCB2YWwsIGNsb3Nlcil7XG4gICAgICAgIHZhciBvbGRWYWwgPSAnJztcbiAgICAgICAgT2JqZWN0LmtleXMob3B0aW9uR3JvdXApLmZvckVhY2goZnVuY3Rpb24oc3RyKXsgaWYgKG9wdGlvbkdyb3VwW3N0cl0uZXhlYyA9PT0gY2hhclR5cGUpeyBvbGRWYWwgPSBzdHI7IH0gfSk7XG5cbiAgICAgICAgZGVsZXRlIG9wdGlvbkdyb3VwW29sZFZhbF07XG4gICAgICAgIG9wdGlvbkdyb3VwW3ZhbF0gPSB7ZXhlYzogY2hhclR5cGV9O1xuICAgICAgICBpZiAoY2xvc2VyKXsgb3B0aW9uR3JvdXBbdmFsXS5jbG9zZXIgPSBjbG9zZXI7IH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2V0cyBcInNpbXBsZVwiIHN5bnRheCBpbiBzcGVjaWFsIGNoYXJhY3RlciBncm91cHMuIFRoaXMgc3ludGF4IG9ubHkgc3VwcG9ydHMgYSBzZXBhcmF0b3JcbiAgICAgKiBjaGFyYWN0ZXIgYW5kIG5vIG90aGVyIG9wZXJhdG9ycy4gQSBjdXN0b20gc2VwYXJhdG9yIG1heSBiZSBwcm92aWRlZCBhcyBhbiBhcmd1bWVudC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBzZXAgT3B0aW9uYWw7IFNlcGFyYXRvciBzdHJpbmcuIElmIG1pc3NpbmcsIHRoZSBkZWZhdWx0IHNlcGFyYXRvciAoXCIuXCIpIGlzIHVzZWQuXG4gICAgICovXG4gICAgdmFyIHNldFNpbXBsZU9wdGlvbnMgPSBmdW5jdGlvbihzZXApe1xuICAgICAgICB2YXIgc2VwT3B0cyA9IHt9O1xuICAgICAgICBpZiAoISh0eXBlb2Ygc2VwID09PSAkU1RSSU5HICYmIHNlcC5sZW5ndGggPT09IDEpKXtcbiAgICAgICAgICAgIHNlcCA9ICcuJztcbiAgICAgICAgfVxuICAgICAgICBzZXBPcHRzW3NlcF0gPSB7ZXhlYzogJFBST1BFUlRZfTtcbiAgICAgICAgb3B0LnByZWZpeGVzID0ge307XG4gICAgICAgIG9wdC5jb250YWluZXJzID0ge307XG4gICAgICAgIG9wdC5zZXBhcmF0b3JzID0gc2VwT3B0cztcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogQWx0ZXIgUGF0aFRvb2xraXQgY29uZmlndXJhdGlvbi4gVGFrZXMgYW4gb3B0aW9ucyBoYXNoIHdoaWNoIG1heSBpbmNsdWRlXG4gICAgICogbXVsdGlwbGUgc2V0dGluZ3MgdG8gY2hhbmdlIGF0IG9uY2UuIElmIHRoZSBwYXRoIHN5bnRheCBpcyBjaGFuZ2VkIGJ5XG4gICAgICogY2hhbmdpbmcgc3BlY2lhbCBjaGFyYWN0ZXJzLCB0aGUgY2FjaGUgaXMgd2lwZWQuIEVhY2ggb3B0aW9uIGdyb3VwIGlzXG4gICAgICogUkVQTEFDRUQgYnkgdGhlIG5ldyBvcHRpb24gZ3JvdXAgcGFzc2VkIGluLiBJZiBhbiBvcHRpb24gZ3JvdXAgaXMgbm90XG4gICAgICogaW5jbHVkZWQgaW4gdGhlIG9wdGlvbnMgaGFzaCwgaXQgaXMgbm90IGNoYW5nZWQuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7T2JqZWN0fSBvcHRpb25zIE9wdGlvbiBoYXNoLiBGb3Igc2FtcGxlIGlucHV0LCBzZWUgYHNldERlZmF1bHRPcHRpb25zYCBhYm92ZS5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRPcHRpb25zID0gZnVuY3Rpb24ob3B0aW9ucyl7XG4gICAgICAgIGlmIChvcHRpb25zLnByZWZpeGVzKXtcbiAgICAgICAgICAgIG9wdC5wcmVmaXhlcyA9IG9wdGlvbnMucHJlZml4ZXM7XG4gICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICB9XG4gICAgICAgIGlmIChvcHRpb25zLnNlcGFyYXRvcnMpe1xuICAgICAgICAgICAgb3B0LnNlcGFyYXRvcnMgPSBvcHRpb25zLnNlcGFyYXRvcnM7XG4gICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICB9XG4gICAgICAgIGlmIChvcHRpb25zLmNvbnRhaW5lcnMpe1xuICAgICAgICAgICAgb3B0LmNvbnRhaW5lcnMgPSBvcHRpb25zLmNvbnRhaW5lcnM7XG4gICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICB9XG4gICAgICAgIGlmICh0eXBlb2Ygb3B0aW9ucy5jYWNoZSAhPT0gJFVOREVGSU5FRCl7XG4gICAgICAgICAgICBvcHQudXNlQ2FjaGUgPSAhIW9wdGlvbnMuY2FjaGU7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHR5cGVvZiBvcHRpb25zLnNpbXBsZSAhPT0gJFVOREVGSU5FRCl7XG4gICAgICAgICAgICB2YXIgdGVtcENhY2hlID0gb3B0LnVzZUNhY2hlOyAvLyBwcmVzZXJ2ZSB0aGVzZSB0d28gb3B0aW9ucyBhZnRlciBcInNldERlZmF1bHRPcHRpb25zXCJcbiAgICAgICAgICAgIHZhciB0ZW1wRm9yY2UgPSBvcHQuZm9yY2U7XG4gICAgICAgICAgICBcbiAgICAgICAgICAgIG9wdC5zaW1wbGUgPSB0cnV0aGlmeShvcHRpb25zLnNpbXBsZSk7XG4gICAgICAgICAgICBpZiAob3B0LnNpbXBsZSl7XG4gICAgICAgICAgICAgICAgc2V0U2ltcGxlT3B0aW9ucygpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgc2V0RGVmYXVsdE9wdGlvbnMoKTtcbiAgICAgICAgICAgICAgICBvcHQudXNlQ2FjaGUgPSB0ZW1wQ2FjaGU7XG4gICAgICAgICAgICAgICAgb3B0LmZvcmNlID0gdGVtcEZvcmNlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodHlwZW9mIG9wdGlvbnMuZm9yY2UgIT09ICRVTkRFRklORUQpe1xuICAgICAgICAgICAgb3B0LmZvcmNlID0gdHJ1dGhpZnkob3B0aW9ucy5mb3JjZSk7XG4gICAgICAgIH1cbiAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2V0cyB1c2Ugb2Yga2V5cGF0aCBjYWNoZSB0byBlbmFibGVkIG9yIGRpc2FibGVkLCBkZXBlbmRpbmcgb24gaW5wdXQgdmFsdWUuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVmFsdWUgd2hpY2ggd2lsbCBiZSBpbnRlcnByZXRlZCBhcyBhIGJvb2xlYW4gdXNpbmcgYHRydXRoaWZ5YC4gXCJ0cnVlXCIgd2lsbCBlbmFibGUgY2FjaGU7IFwiZmFsc2VcIiB3aWxsIGRpc2FibGUuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q2FjaGUgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBvcHQudXNlQ2FjaGUgPSB0cnV0aGlmeSh2YWwpO1xuICAgIH07XG4gICAgLyoqXG4gICAgICogRW5hYmxlcyB1c2Ugb2Yga2V5cGF0aCBjYWNoZS5cbiAgICAgKiBAcHVibGljXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q2FjaGVPbiA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIG9wdC51c2VDYWNoZSA9IHRydWU7XG4gICAgfTtcbiAgICAvKipcbiAgICAgKiBEaXNhYmxlcyB1c2Ugb2Yga2V5cGF0aCBjYWNoZS5cbiAgICAgKiBAcHVibGljXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q2FjaGVPZmYgPSBmdW5jdGlvbigpe1xuICAgICAgICBvcHQudXNlQ2FjaGUgPSBmYWxzZTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2V0cyBcImZvcmNlXCIgb3B0aW9uIHdoZW4gc2V0dGluZyB2YWx1ZXMgaW4gYW4gb2JqZWN0LCBkZXBlbmRpbmcgb24gaW5wdXQgdmFsdWUuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVmFsdWUgd2hpY2ggd2lsbCBiZSBpbnRlcnByZXRlZCBhcyBhIGJvb2xlYW4gdXNpbmcgYHRydXRoaWZ5YC4gXCJ0cnVlXCIgZW5hYmxlcyBcImZvcmNlXCI7IFwiZmFsc2VcIiBkaXNhYmxlcy5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRGb3JjZSA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIG9wdC5mb3JjZSA9IHRydXRoaWZ5KHZhbCk7XG4gICAgfTtcbiAgICAvKipcbiAgICAgKiBFbmFibGVzIFwiZm9yY2VcIiBvcHRpb24gd2hlbiBzZXR0aW5nIHZhbHVlcyBpbiBhbiBvYmplY3QuXG4gICAgICogQHB1YmxpY1xuICAgICAqL1xuICAgIF90aGlzLnNldEZvcmNlT24gPSBmdW5jdGlvbigpe1xuICAgICAgICBvcHQuZm9yY2UgPSB0cnVlO1xuICAgIH07XG4gICAgLyoqXG4gICAgICogRGlzYWJsZXMgXCJmb3JjZVwiIG9wdGlvbiB3aGVuIHNldHRpbmcgdmFsdWVzIGluIGFuIG9iamVjdC5cbiAgICAgKiBAcHVibGljXG4gICAgICovXG4gICAgX3RoaXMuc2V0Rm9yY2VPZmYgPSBmdW5jdGlvbigpe1xuICAgICAgICBvcHQuZm9yY2UgPSBmYWxzZTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2hvcnRjdXQgZnVuY3Rpb24gdG8gYWx0ZXIgUGF0aFRvb2xraXQgc3ludGF4IHRvIGEgXCJzaW1wbGVcIiBtb2RlIHRoYXQgb25seSB1c2VzXG4gICAgICogc2VwYXJhdG9ycyBhbmQgbm8gb3RoZXIgb3BlcmF0b3JzLiBcIlNpbXBsZVwiIG1vZGUgaXMgZW5hYmxlZCBvciBkaXNhYmxlZCBhY2NvcmRpbmdcbiAgICAgKiB0byB0aGUgZmlyc3QgYXJndW1lbnQgYW5kIHRoZSBzZXBhcmF0b3IgbWF5IGJlIGN1c3RvbWl6ZWQgd2l0aCB0aGUgc2Vjb25kXG4gICAgICogYXJndW1lbnQgd2hlbiBlbmFibGluZyBcInNpbXBsZVwiIG1vZGUuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVmFsdWUgd2hpY2ggd2lsbCBiZSBpbnRlcnByZXRlZCBhcyBhIGJvb2xlYW4gdXNpbmcgYHRydXRoaWZ5YC4gXCJ0cnVlXCIgZW5hYmxlcyBcInNpbXBsZVwiIG1vZGU7IFwiZmFsc2VcIiBkaXNhYmxlcy5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc2VwIFNlcGFyYXRvciBzdHJpbmcgdG8gdXNlIGluIHBsYWNlIG9mIHRoZSBkZWZhdWx0IFwiLlwiXG4gICAgICovXG4gICAgX3RoaXMuc2V0U2ltcGxlID0gZnVuY3Rpb24odmFsLCBzZXApe1xuICAgICAgICB2YXIgdGVtcENhY2hlID0gb3B0LnVzZUNhY2hlOyAvLyBwcmVzZXJ2ZSB0aGVzZSB0d28gb3B0aW9ucyBhZnRlciBcInNldERlZmF1bHRPcHRpb25zXCJcbiAgICAgICAgdmFyIHRlbXBGb3JjZSA9IG9wdC5mb3JjZTtcbiAgICAgICAgb3B0LnNpbXBsZSA9IHRydXRoaWZ5KHZhbCk7XG4gICAgICAgIGlmIChvcHQuc2ltcGxlKXtcbiAgICAgICAgICAgIHNldFNpbXBsZU9wdGlvbnMoc2VwKTtcbiAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBzZXREZWZhdWx0T3B0aW9ucygpO1xuICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgIG9wdC51c2VDYWNoZSA9IHRlbXBDYWNoZTtcbiAgICAgICAgICAgIG9wdC5mb3JjZSA9IHRlbXBGb3JjZTtcbiAgICAgICAgfVxuICAgICAgICBjYWNoZSA9IHt9O1xuICAgIH07XG4gICAgXG4gICAgLyoqXG4gICAgICogRW5hYmxlcyBcInNpbXBsZVwiIG1vZGVcbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHNlcCBTZXBhcmF0b3Igc3RyaW5nIHRvIHVzZSBpbiBwbGFjZSBvZiB0aGUgZGVmYXVsdCBcIi5cIlxuICAgICAqIEBzZWUgc2V0U2ltcGxlXG4gICAgICovXG4gICAgX3RoaXMuc2V0U2ltcGxlT24gPSBmdW5jdGlvbihzZXApe1xuICAgICAgICBvcHQuc2ltcGxlID0gdHJ1ZTtcbiAgICAgICAgc2V0U2ltcGxlT3B0aW9ucyhzZXApO1xuICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICBjYWNoZSA9IHt9O1xuICAgIH07XG4gICAgXG4gICAgLyoqXG4gICAgICogRGlzYWJsZXMgXCJzaW1wbGVcIiBtb2RlLCByZXN0b3JlcyBkZWZhdWx0IFBhdGhUb29sa2l0IHN5bnRheFxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAc2VlIHNldFNpbXBsZVxuICAgICAqIEBzZWUgc2V0RGVmYXVsdE9wdGlvbnNcbiAgICAgKi9cbiAgICBfdGhpcy5zZXRTaW1wbGVPZmYgPSBmdW5jdGlvbigpe1xuICAgICAgICB2YXIgdGVtcENhY2hlID0gb3B0LnVzZUNhY2hlOyAvLyBwcmVzZXJ2ZSB0aGVzZSB0d28gb3B0aW9ucyBhZnRlciBcInNldERlZmF1bHRPcHRpb25zXCJcbiAgICAgICAgdmFyIHRlbXBGb3JjZSA9IG9wdC5mb3JjZTtcbiAgICAgICAgb3B0LnNpbXBsZSA9IGZhbHNlO1xuICAgICAgICBzZXREZWZhdWx0T3B0aW9ucygpO1xuICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICBvcHQudXNlQ2FjaGUgPSB0ZW1wQ2FjaGU7XG4gICAgICAgIG9wdC5mb3JjZSA9IHRlbXBGb3JjZTtcbiAgICAgICAgY2FjaGUgPSB7fTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBwcm9wZXJ0eSBzZXBhcmF0b3IgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0U2VwYXJhdG9yUHJvcGVydHkgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnNlcGFyYXRvcnNbdmFsXS5leGVjID09PSAkUFJPUEVSVFkpICYmICEob3B0LnByZWZpeGVzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LnNlcGFyYXRvcnMsICRQUk9QRVJUWSwgdmFsKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFNlcGFyYXRvclByb3BlcnR5IC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0U2VwYXJhdG9yUHJvcGVydHkgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBjb2xsZWN0aW9uIHNlcGFyYXRvciBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGlzIG9wZXJhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRTZXBhcmF0b3JDb2xsZWN0aW9uID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5zZXBhcmF0b3JzW3ZhbF0uZXhlYyA9PT0gJENPTExFQ1RJT04pICYmICEob3B0LnByZWZpeGVzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LnNlcGFyYXRvcnMsICRDT0xMRUNUSU9OLCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0U2VwYXJhdG9yQ29sbGVjdGlvbiAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFNlcGFyYXRvckNvbGxlY3Rpb24gLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBwYXJlbnQgcHJlZml4IGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoaXMgb3BlcmF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLnNldFByZWZpeFBhcmVudCA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnByZWZpeGVzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0uZXhlYyA9PT0gJFBBUkVOVCkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5wcmVmaXhlcywgJFBBUkVOVCwgdmFsKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeFBhcmVudCAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeFBhcmVudCAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIHJvb3QgcHJlZml4IGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoaXMgb3BlcmF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLnNldFByZWZpeFJvb3QgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdLmV4ZWMgPT09ICRST09UKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LnByZWZpeGVzLCAkUk9PVCwgdmFsKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeFJvb3QgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhSb290IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgcGxhY2Vob2xkZXIgcHJlZml4IGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoaXMgb3BlcmF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLnNldFByZWZpeFBsYWNlaG9sZGVyID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQucHJlZml4ZXNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXS5leGVjID09PSAkUExBQ0VIT0xERVIpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQucHJlZml4ZXMsICRQTEFDRUhPTERFUiwgdmFsKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeFBsYWNlaG9sZGVyIC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4UGxhY2Vob2xkZXIgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBjb250ZXh0IHByZWZpeCBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGlzIG9wZXJhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRQcmVmaXhDb250ZXh0ID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQucHJlZml4ZXNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXS5leGVjID09PSAkQ09OVEVYVCkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5wcmVmaXhlcywgJENPTlRFWFQsIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhDb250ZXh0IC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4Q29udGV4dCAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIHByb3BlcnR5IGNvbnRhaW5lciBjaGFyYWN0ZXJzIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgb3BlbmVyLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgY2xvc2VyLlxuICAgICAqL1xuICAgIF90aGlzLnNldENvbnRhaW5lclByb3BlcnR5ID0gZnVuY3Rpb24odmFsLCBjbG9zZXIpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxICYmIHR5cGVvZiBjbG9zZXIgPT09ICRTVFJJTkcgJiYgY2xvc2VyLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQuY29udGFpbmVyc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0uZXhlYyA9PT0gJFBST1BFUlRZKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5jb250YWluZXJzLCAkUFJPUEVSVFksIHZhbCwgY2xvc2VyKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lclByb3BlcnR5IC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyUHJvcGVydHkgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBzaW5nbGUgcXVvdGUgY29udGFpbmVyIGNoYXJhY3RlcnMgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBvcGVuZXIuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNsb3NlciBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBjbG9zZXIuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q29udGFpbmVyU2luZ2xlcXVvdGUgPSBmdW5jdGlvbih2YWwsIGNsb3Nlcil7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEgJiYgdHlwZW9mIGNsb3NlciA9PT0gJFNUUklORyAmJiBjbG9zZXIubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5jb250YWluZXJzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXS5leGVjID09PSAkU0lOR0xFUVVPVEUpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LmNvbnRhaW5lcnMsICRTSU5HTEVRVU9URSwgdmFsLCBjbG9zZXIpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyU2luZ2xlcXVvdGUgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJTaW5nbGVxdW90ZSAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIGRvdWJsZSBxdW90ZSBjb250YWluZXIgY2hhcmFjdGVycyBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIG9wZW5lci5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gY2xvc2VyIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIGNsb3Nlci5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDb250YWluZXJEb3VibGVxdW90ZSA9IGZ1bmN0aW9uKHZhbCwgY2xvc2VyKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSAmJiB0eXBlb2YgY2xvc2VyID09PSAkU1RSSU5HICYmIGNsb3Nlci5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LmNvbnRhaW5lcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdLmV4ZWMgPT09ICRET1VCTEVRVU9URSkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuY29udGFpbmVycywgJERPVUJMRVFVT1RFLCB2YWwsIGNsb3Nlcik7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJEb3VibGVxdW90ZSAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lckRvdWJsZXF1b3RlIC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgZnVuY3Rpb24gY2FsbCBjb250YWluZXIgY2hhcmFjdGVycyBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIG9wZW5lci5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gY2xvc2VyIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIGNsb3Nlci5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDb250YWluZXJDYWxsID0gZnVuY3Rpb24odmFsLCBjbG9zZXIpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxICYmIHR5cGVvZiBjbG9zZXIgPT09ICRTVFJJTkcgJiYgY2xvc2VyLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQuY29udGFpbmVyc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0uZXhlYyA9PT0gJENBTEwpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LmNvbnRhaW5lcnMsICRDQUxMLCB2YWwsIGNsb3Nlcik7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJDYWxsIC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyQ2FsbCAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIGV2YWwgcHJvcGVydHkgY29udGFpbmVyIGNoYXJhY3RlcnMgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBvcGVuZXIuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNsb3NlciBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBjbG9zZXIuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q29udGFpbmVyRXZhbFByb3BlcnR5ID0gZnVuY3Rpb24odmFsLCBjbG9zZXIpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxICYmIHR5cGVvZiBjbG9zZXIgPT09ICRTVFJJTkcgJiYgY2xvc2VyLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQuY29udGFpbmVyc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0uZXhlYyA9PT0gJEVWQUxQUk9QRVJUWSkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuY29udGFpbmVycywgJEVWQUxQUk9QRVJUWSwgdmFsLCBjbG9zZXIpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyRXZhbFByb3BlcnR5IC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyUHJvcGVydHkgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogUmVzZXQgYWxsIFBhdGhUb29sa2l0IG9wdGlvbnMgdG8gdGhlaXIgZGVmYXVsdCB2YWx1ZXMuXG4gICAgICogQHB1YmxpY1xuICAgICAqL1xuICAgIF90aGlzLnJlc2V0T3B0aW9ucyA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIHNldERlZmF1bHRPcHRpb25zKCk7XG4gICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgIGNhY2hlID0ge307XG4gICAgfTtcblxuICAgIC8vIEluaXRpYWxpemUgb3B0aW9uIHNldFxuICAgIHNldERlZmF1bHRPcHRpb25zKCk7XG4gICAgdXBkYXRlUmVnRXgoKTtcblxuICAgIC8vIEFwcGx5IGN1c3RvbSBvcHRpb25zIGlmIHByb3ZpZGVkIGFzIGFyZ3VtZW50IHRvIGNvbnN0cnVjdG9yXG4gICAgb3B0aW9ucyAmJiBfdGhpcy5zZXRPcHRpb25zKG9wdGlvbnMpO1xuXG59O1xuXG5leHBvcnQgZGVmYXVsdCBQYXRoVG9vbGtpdDtcbiJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiOzs7Ozs7QUFBQTs7Ozs7OztBQU9BLEFBRUE7QUFDQSxJQUFJLEtBQUssR0FBRyxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUMsT0FBTyxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQzs7O0FBR3ZDLElBQUksU0FBUyxPQUFPLEdBQUc7SUFDbkIsVUFBVSxNQUFNLFdBQVc7SUFDM0IsT0FBTyxTQUFTLFFBQVE7SUFDeEIsT0FBTyxTQUFTLFFBQVE7SUFDeEIsS0FBSyxXQUFXLE1BQU07SUFDdEIsWUFBWSxJQUFJLGFBQWE7SUFDN0IsUUFBUSxRQUFRLFNBQVM7SUFDekIsU0FBUyxPQUFPLFVBQVU7SUFDMUIsV0FBVyxLQUFLLFlBQVk7SUFDNUIsS0FBSyxXQUFXLE1BQU07SUFDdEIsWUFBWSxJQUFJLGFBQWE7SUFDN0IsWUFBWSxJQUFJLGFBQWE7SUFDN0IsS0FBSyxXQUFXLE1BQU07SUFDdEIsYUFBYSxHQUFHLGNBQWMsQ0FBQzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7QUFvQm5DLElBQUksYUFBYSxHQUFHLFNBQVMsUUFBUSxFQUFFLEdBQUcsQ0FB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