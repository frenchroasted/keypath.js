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

//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjpudWxsLCJzb3VyY2VzIjpbIi9ob21lL2Fhcm9uL3Byb2plY3RzL3BhdGgtdG9vbGtpdC9zcmMvcGF0aC10b29sa2l0LmpzIl0sInNvdXJjZXNDb250ZW50IjpbIi8qKlxuICogQGZpbGVPdmVydmlldyBQYXRoVG9vbGtpdCBldmFsdWF0ZXMgc3RyaW5nIHBhdGhzIGFzIHByb3BlcnR5L2luZGV4IHNlcXVlbmNlcyB3aXRoaW4gb2JqZWN0cyBhbmQgYXJyYXlzXG4gKiBAYXV0aG9yIEFhcm9uIEJyb3duXG4gKiBAdmVyc2lvbiAxLjEuMFxuICovXG5cbi8vIFBhcnNpbmcsIHRva2VuaW56aW5nLCBldGNcbid1c2Ugc3RyaWN0JztcblxuLy8gU29tZSBjb25zdGFudHMgZm9yIGNvbnZlbmllbmNlXG52YXIgVU5ERUYgPSAoZnVuY3Rpb24odSl7cmV0dXJuIHU7fSkoKTtcblxuLy8gU3RhdGljIHN0cmluZ3MsIGFzc2lnbmVkIHRvIGFpZCBjb2RlIG1pbmlmaWNhdGlvblxudmFyICRXSUxEQ0FSRCAgICAgPSAnKicsXG4gICAgJFVOREVGSU5FRCAgICA9ICd1bmRlZmluZWQnLFxuICAgICRTVFJJTkcgICAgICAgPSAnc3RyaW5nJyxcbiAgICAkUEFSRU5UICAgICAgID0gJ3BhcmVudCcsXG4gICAgJFJPT1QgICAgICAgICA9ICdyb290JyxcbiAgICAkUExBQ0VIT0xERVIgID0gJ3BsYWNlaG9sZGVyJyxcbiAgICAkQ09OVEVYVCAgICAgID0gJ2NvbnRleHQnLFxuICAgICRQUk9QRVJUWSAgICAgPSAncHJvcGVydHknLFxuICAgICRDT0xMRUNUSU9OICAgPSAnY29sbGVjdGlvbicsXG4gICAgJEVBQ0ggICAgICAgICA9ICdlYWNoJyxcbiAgICAkU0lOR0xFUVVPVEUgID0gJ3NpbmdsZXF1b3RlJyxcbiAgICAkRE9VQkxFUVVPVEUgID0gJ2RvdWJsZXF1b3RlJyxcbiAgICAkQ0FMTCAgICAgICAgID0gJ2NhbGwnLFxuICAgICRFVkFMUFJPUEVSVFkgPSAnZXZhbFByb3BlcnR5JztcbiAgICBcbi8qKlxuICogVGVzdHMgd2hldGhlciBhIHdpbGRjYXJkIHRlbXBsYXRlcyBtYXRjaGVzIGEgZ2l2ZW4gc3RyaW5nLlxuICogYGBgamF2YXNjcmlwdFxuICogdmFyIHN0ciA9ICdhYWFiYmJ4eHhjY2NkZGQnO1xuICogd2lsZENhcmRNYXRjaCgnYWFhYmJieHh4Y2NjZGRkJyk7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJyonLCBzdHIpOyAvLyB0cnVlXG4gKiB3aWxkQ2FyZE1hdGNoKCcqJywgJycpOyAvLyB0cnVlXG4gKiB3aWxkQ2FyZE1hdGNoKCdhKicsIHN0cik7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJ2FhKmRkZCcsIHN0cik7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJypkJywgc3RyKTsgLy8gdHJ1ZVxuICogd2lsZENhcmRNYXRjaCgnKmEnLCBzdHIpOyAvLyBmYWxzZVxuICogd2lsZENhcmRNYXRjaCgnYSp6Jywgc3RyKTsgLy8gZmFsc2VcbiAqIGBgYFxuICogQHByaXZhdGVcbiAqIEBwYXJhbSAge1N0cmluZ30gdGVtcGxhdGUgV2lsZGNhcmQgcGF0dGVyblxuICogQHBhcmFtICB7U3RyaW5nfSBzdHIgICAgICBTdHJpbmcgdG8gbWF0Y2ggYWdhaW5zdCB3aWxkY2FyZCBwYXR0ZXJuXG4gKiBAcmV0dXJuIHtCb29sZWFufSAgICAgICAgICBUcnVlIGlmIHBhdHRlcm4gbWF0Y2hlcyBzdHJpbmc7IEZhbHNlIGlmIG5vdFxuICovXG52YXIgd2lsZENhcmRNYXRjaCA9IGZ1bmN0aW9uKHRlbXBsYXRlLCBzdHIpe1xuICAgIHZhciBwb3MgPSB0ZW1wbGF0ZS5pbmRleE9mKCRXSUxEQ0FSRCksXG4gICAgICAgIHBhcnRzID0gdGVtcGxhdGUuc3BsaXQoJFdJTERDQVJELCAyKSxcbiAgICAgICAgbWF0Y2ggPSB0cnVlO1xuICAgIGlmIChwYXJ0c1swXSl7XG4gICAgICAgIC8vIElmIG5vIHdpbGRjYXJkIHByZXNlbnQsIHJldHVybiBzaW1wbGUgc3RyaW5nIGNvbXBhcmlzb25cbiAgICAgICAgaWYgKHBhcnRzWzBdID09PSB0ZW1wbGF0ZSl7XG4gICAgICAgICAgICByZXR1cm4gcGFydHNbMF0gPT09IHN0cjtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIG1hdGNoID0gbWF0Y2ggJiYgc3RyLnN1YnN0cigwLCBwYXJ0c1swXS5sZW5ndGgpID09PSBwYXJ0c1swXTtcbiAgICAgICAgfVxuICAgIH1cbiAgICBpZiAocGFydHNbMV0pe1xuICAgICAgICBtYXRjaCA9IG1hdGNoICYmIHN0ci5zdWJzdHIoLTEqcGFydHNbMV0ubGVuZ3RoKSA9PT0gcGFydHNbMV07XG4gICAgfVxuICAgIHJldHVybiBtYXRjaDtcbn07XG5cbi8qKlxuICogSW5zcGVjdCBpbnB1dCB2YWx1ZSBhbmQgZGV0ZXJtaW5lIHdoZXRoZXIgaXQgaXMgYW4gT2JqZWN0IG9yIG5vdC5cbiAqIFZhbHVlcyBvZiB1bmRlZmluZWQgYW5kIG51bGwgd2lsbCByZXR1cm4gXCJmYWxzZVwiLCBvdGhlcndpc2VcbiAqIG11c3QgYmUgb2YgdHlwZSBcIm9iamVjdFwiIG9yIFwiZnVuY3Rpb25cIi5cbiAqIEBwcml2YXRlXG4gKiBAcGFyYW0gIHtPYmplY3R9ICB2YWwgVGhpbmcgdG8gZXhhbWluZSwgbWF5IGJlIG9mIGFueSB0eXBlXG4gKiBAcmV0dXJuIHtCb29sZWFufSAgICAgVHJ1ZSBpZiB0aGluZyBpcyBvZiB0eXBlIFwib2JqZWN0XCIgb3IgXCJmdW5jdGlvblwiXG4gKi9cbnZhciBpc09iamVjdCA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgaWYgKHR5cGVvZiB2YWwgPT09ICRVTkRFRklORUQgfHwgdmFsID09PSBudWxsKSB7IHJldHVybiBmYWxzZTt9XG4gICAgcmV0dXJuICggKHR5cGVvZiB2YWwgPT09ICdmdW5jdGlvbicpIHx8ICh0eXBlb2YgdmFsID09PSAnb2JqZWN0JykgKTtcbn07XG5cbi8qKlxuICogSW5zcGVjdCBpbnB1dCB2YWx1ZSBhbmQgZGV0ZXJtaW5lIHdoZXRoZXIgaXQgaXMgYW4gSW50ZWdlciBvciBub3QuXG4gKiBWYWx1ZXMgb2YgdW5kZWZpbmVkIGFuZCBudWxsIHdpbGwgcmV0dXJuIFwiZmFsc2VcIi5cbiAqIEBwcml2YXRlXG4gKiBAcGFyYW0gIHtTdHJpbmd9ICB2YWwgU3RyaW5nIHRvIGV4YW1pbmVcbiAqIEByZXR1cm4ge0Jvb2xlYW59ICAgICBUcnVlIGlmIHRoaW5nIGNvbnNpc3RzIG9mIGF0IGxlYXN0IG9uZSBkaWdpdCBhbmQgb25seSBvZiBkaWdpdHMgKG5vIC4gb3IgLClcbiAqL1xudmFyIGRpZ2l0c1JlZ2V4ID0gL15cXGQrJC87XG52YXIgaXNEaWdpdHMgPSBmdW5jdGlvbih2YWwpe1xuICAgIHJldHVybiBkaWdpdHNSZWdleC50ZXN0KHZhbCk7XG59O1xuXG4vKipcbiAqIENvbnZlcnQgdmFyaW91cyB2YWx1ZXMgdG8gdHJ1ZSBib29sZWFuIGB0cnVlYCBvciBgZmFsc2VgLlxuICogRm9yIG5vbi1zdHJpbmcgdmFsdWVzLCB0aGUgbmF0aXZlIGphdmFzY3JpcHQgaWRlYSBvZiBcInRydWVcIiB3aWxsIGFwcGx5LlxuICogRm9yIHN0cmluZyB2YWx1ZXMsIHRoZSB3b3JkcyBcInRydWVcIiwgXCJ5ZXNcIiwgYW5kIFwib25cIiB3aWxsIGFsbCByZXR1cm4gYHRydWVgLlxuICogQWxsIG90aGVyIHN0cmluZ3MgcmV0dXJuIGBmYWxzZWAuIFRoZSBzdHJpbmcgbWF0Y2ggaXMgbm9uLWNhc2Utc2Vuc2l0aXZlLlxuICogQHByaXZhdGVcbiAqL1xudmFyIHRydXRoaWZ5ID0gZnVuY3Rpb24odmFsKXtcbiAgICB2YXIgdjtcbiAgICBpZiAodHlwZW9mIHZhbCAhPT0gJFNUUklORyl7XG4gICAgICAgIHJldHVybiB2YWwgJiYgdHJ1ZTsgLy8gVXNlIG5hdGl2ZSBqYXZhc2NyaXB0IG5vdGlvbiBvZiBcInRydXRoeVwiXG4gICAgfVxuICAgIHYgPSB2YWwudG9VcHBlckNhc2UoKTtcbiAgICBpZiAodiA9PT0gJ1RSVUUnIHx8IHYgPT09ICdZRVMnIHx8IHYgPT09ICdPTicpe1xuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZhbHNlO1xufTtcblxuLyoqXG4gKiBVc2luZyBwcm92aWRlZCBxdW90ZSBjaGFyYWN0ZXIgYXMgcHJlZml4IGFuZCBzdWZmaXgsIGVzY2FwZSBhbnkgaW5zdGFuY2VzXG4gKiBvZiB0aGUgcXVvdGUgY2hhcmFjdGVyIHdpdGhpbiB0aGUgc3RyaW5nIGFuZCByZXR1cm4gcXVvdGUrc3RyaW5nK3F1b3RlLlxuICogVGhlIGNoYXJhY3RlciBkZWZpbmVkIGFzIFwic2luZ2xlcXVvdGVcIiBtYXkgYmUgYWx0ZXJlZCBieSBjdXN0b20gb3B0aW9ucyxcbiAqIHNvIGEgZ2VuZXJhbC1wdXJwb3NlIGZ1bmN0aW9uIGlzIG5lZWRlZCB0byBxdW90ZSBwYXRoIHNlZ21lbnRzIGNvcnJlY3RseS5cbiAqIEBwcml2YXRlXG4gKiBAcGFyYW0gIHtTdHJpbmd9IHEgICBTaW5nbGUtY2hhcmFjdGVyIHN0cmluZyB0byB1c2UgYXMgcXVvdGUgY2hhcmFjdGVyXG4gKiBAcGFyYW0gIHtTdHJpbmd9IHN0ciBTdHJpbmcgdG8gYmUgcXVvdGVkLlxuICogQHJldHVybiB7U3RyaW5nfSAgICAgT3JpZ2luYWwgc3RyaW5nLCBzdXJyb3VuZGVkIGJ5IHRoZSBxdW90ZSBjaGFyYWN0ZXIsIHBvc3NpYmx5IG1vZGlmaWVkIGludGVybmFsbHkgaWYgdGhlIHF1b3RlIGNoYXJhY3RlciBleGlzdHMgd2l0aGluIHRoZSBzdHJpbmcuXG4gKi9cbnZhciBxdW90ZVN0cmluZyA9IGZ1bmN0aW9uKHEsIHN0cil7XG4gICAgdmFyIHFSZWdFeCA9IG5ldyBSZWdFeHAocSwgJ2cnKTtcbiAgICByZXR1cm4gcSArIHN0ci5yZXBsYWNlKHFSZWdFeCwgJ1xcXFwnICsgcSkgKyBxO1xufTtcblxuLyoqXG4gKiBQYXRoVG9vbGtpdCBiYXNlIG9iamVjdC4gSW5jbHVkZXMgYWxsIGluc3RhbmNlLXNwZWNpZmljIGRhdGEgKG9wdGlvbnMsIGNhY2hlKVxuICogYXMgbG9jYWwgdmFyaWFibGVzLiBNYXkgYmUgcGFzc2VkIGFuIG9wdGlvbnMgaGFzaCB0byBwcmUtY29uZmlndXJlIHRoZVxuICogaW5zdGFuY2UgcHJpb3IgdG8gdXNlLlxuICogQGNvbnN0cnVjdG9yXG4gKiBAcHJvcGVydHkge09iamVjdH0gb3B0aW9ucyBPcHRpb25hbC4gQ29sbGVjdGlvbiBvZiBjb25maWd1cmF0aW9uIHNldHRpbmdzIGZvciB0aGlzIGluc3RhbmNlIG9mIFBhdGhUb29sa2l0LiBTZWUgYHNldE9wdGlvbnNgIGZ1bmN0aW9uIGJlbG93IGZvciBkZXRhaWxlZCBkb2N1bWVudGF0aW9uLlxuICovXG52YXIgUGF0aFRvb2xraXQgPSBmdW5jdGlvbihvcHRpb25zKXtcbiAgICB2YXIgX3RoaXMgPSB0aGlzLFxuICAgICAgICBjYWNoZSA9IHt9LFxuICAgICAgICBvcHQgPSB7fSxcbiAgICAgICAgcHJlZml4TGlzdCwgc2VwYXJhdG9yTGlzdCwgY29udGFpbmVyTGlzdCwgY29udGFpbmVyQ2xvc2VMaXN0LFxuICAgICAgICBwcm9wZXJ0eVNlcGFyYXRvcixcbiAgICAgICAgc2luZ2xlcXVvdGUsIGRvdWJsZXF1b3RlLFxuICAgICAgICBzaW1wbGVQYXRoQ2hhcnMsIHNpbXBsZVBhdGhSZWdFeCxcbiAgICAgICAgYWxsU3BlY2lhbHMsIGFsbFNwZWNpYWxzUmVnRXgsXG4gICAgICAgIGVzY2FwZWROb25TcGVjaWFsc1JlZ0V4LFxuICAgICAgICBlc2NhcGVkUXVvdGVzLFxuICAgICAgICB3aWxkY2FyZFJlZ0V4O1xuXG4gICAgLyoqXG4gICAgICogU2V2ZXJhbCByZWd1bGFyIGV4cHJlc3Npb25zIGFyZSBwcmUtY29tcGlsZWQgZm9yIHVzZSBpbiBwYXRoIGludGVycHJldGF0aW9uLlxuICAgICAqIFRoZXNlIGV4cHJlc3Npb25zIGFyZSBidWlsdCBmcm9tIHRoZSBjdXJyZW50IHN5bnRheCBjb25maWd1cmF0aW9uLCBzbyB0aGV5XG4gICAgICogbXVzdCBiZSByZS1idWlsdCBldmVyeSB0aW1lIHRoZSBzeW50YXggY2hhbmdlcy5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqL1xuICAgIHZhciB1cGRhdGVSZWdFeCA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIC8vIExpc3RzIG9mIHNwZWNpYWwgY2hhcmFjdGVycyBmb3IgdXNlIGluIHJlZ3VsYXIgZXhwcmVzc2lvbnNcbiAgICAgICAgcHJlZml4TGlzdCA9IE9iamVjdC5rZXlzKG9wdC5wcmVmaXhlcyk7XG4gICAgICAgIHNlcGFyYXRvckxpc3QgPSBPYmplY3Qua2V5cyhvcHQuc2VwYXJhdG9ycyk7XG4gICAgICAgIGNvbnRhaW5lckxpc3QgPSBPYmplY3Qua2V5cyhvcHQuY29udGFpbmVycyk7XG4gICAgICAgIGNvbnRhaW5lckNsb3NlTGlzdCA9IGNvbnRhaW5lckxpc3QubWFwKGZ1bmN0aW9uKGtleSl7IHJldHVybiBvcHQuY29udGFpbmVyc1trZXldLmNsb3NlcjsgfSk7XG4gICAgICAgIFxuICAgICAgICBwcm9wZXJ0eVNlcGFyYXRvciA9ICcnO1xuICAgICAgICBPYmplY3Qua2V5cyhvcHQuc2VwYXJhdG9ycykuZm9yRWFjaChmdW5jdGlvbihzZXApeyBpZiAob3B0LnNlcGFyYXRvcnNbc2VwXS5leGVjID09PSAkUFJPUEVSVFkpeyBwcm9wZXJ0eVNlcGFyYXRvciA9IHNlcDsgfSB9KTtcbiAgICAgICAgc2luZ2xlcXVvdGUgPSAnJztcbiAgICAgICAgZG91YmxlcXVvdGUgPSAnJztcbiAgICAgICAgT2JqZWN0LmtleXMob3B0LmNvbnRhaW5lcnMpLmZvckVhY2goZnVuY3Rpb24oc2VwKXtcbiAgICAgICAgICAgIGlmIChvcHQuY29udGFpbmVyc1tzZXBdLmV4ZWMgPT09ICRTSU5HTEVRVU9URSl7IHNpbmdsZXF1b3RlID0gc2VwO31cbiAgICAgICAgICAgIGlmIChvcHQuY29udGFpbmVyc1tzZXBdLmV4ZWMgPT09ICRET1VCTEVRVU9URSl7IGRvdWJsZXF1b3RlID0gc2VwO31cbiAgICAgICAgfSk7XG5cbiAgICAgICAgLy8gRmluZCBhbGwgc3BlY2lhbCBjaGFyYWN0ZXJzIGV4Y2VwdCBwcm9wZXJ0eSBzZXBhcmF0b3IgKC4gYnkgZGVmYXVsdClcbiAgICAgICAgc2ltcGxlUGF0aENoYXJzID0gJ1tcXFxcXFxcXCcgKyBbJFdJTERDQVJEXS5jb25jYXQocHJlZml4TGlzdCkuY29uY2F0KHNlcGFyYXRvckxpc3QpLmNvbmNhdChjb250YWluZXJMaXN0KS5qb2luKCdcXFxcJykucmVwbGFjZSgnXFxcXCcrcHJvcGVydHlTZXBhcmF0b3IsICcnKSArICddJztcbiAgICAgICAgc2ltcGxlUGF0aFJlZ0V4ID0gbmV3IFJlZ0V4cChzaW1wbGVQYXRoQ2hhcnMpO1xuICAgICAgICBcbiAgICAgICAgLy8gRmluZCBhbGwgc3BlY2lhbCBjaGFyYWN0ZXJzLCBpbmNsdWRpbmcgYmFja3NsYXNoXG4gICAgICAgIGFsbFNwZWNpYWxzID0gJ1tcXFxcXFxcXFxcXFwnICsgWyRXSUxEQ0FSRF0uY29uY2F0KHByZWZpeExpc3QpLmNvbmNhdChzZXBhcmF0b3JMaXN0KS5jb25jYXQoY29udGFpbmVyTGlzdCkuY29uY2F0KGNvbnRhaW5lckNsb3NlTGlzdCkuam9pbignXFxcXCcpICsgJ10nO1xuICAgICAgICBhbGxTcGVjaWFsc1JlZ0V4ID0gbmV3IFJlZ0V4cChhbGxTcGVjaWFscywgJ2cnKTtcbiAgICAgICAgXG4gICAgICAgIC8vIEZpbmQgYWxsIGVzY2FwZWQgc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICAgIC8vIGVzY2FwZWRTcGVjaWFsc1JlZ0V4ID0gbmV3IFJlZ0V4cCgnXFxcXCcrYWxsU3BlY2lhbHMsICdnJyk7XG4gICAgICAgIC8vIEZpbmQgYWxsIGVzY2FwZWQgbm9uLXNwZWNpYWwgY2hhcmFjdGVycywgaS5lLiB1bm5lY2Vzc2FyeSBlc2NhcGVzXG4gICAgICAgIGVzY2FwZWROb25TcGVjaWFsc1JlZ0V4ID0gbmV3IFJlZ0V4cCgnXFxcXCcrYWxsU3BlY2lhbHMucmVwbGFjZSgvXlxcWy8sJ1teJykpO1xuICAgICAgICBpZiAoc2luZ2xlcXVvdGUgfHwgZG91YmxlcXVvdGUpe1xuICAgICAgICAgICAgZXNjYXBlZFF1b3RlcyA9IG5ldyBSZWdFeHAoJ1xcXFxbJytzaW5nbGVxdW90ZStkb3VibGVxdW90ZSsnXScsICdnJyk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBlc2NhcGVkUXVvdGVzID0gJyc7XG4gICAgICAgIH1cbiAgICAgICAgXG4gICAgICAgIC8vIEZpbmQgd2lsZGNhcmQgY2hhcmFjdGVyXG4gICAgICAgIHdpbGRjYXJkUmVnRXggPSBuZXcgUmVnRXhwKCdcXFxcJyskV0lMRENBUkQpO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTZXRzIGFsbCB0aGUgZGVmYXVsdCBvcHRpb25zIGZvciBpbnRlcnByZXRlciBiZWhhdmlvciBhbmQgc3ludGF4LlxuICAgICAqIEBwcml2YXRlXG4gICAgICovXG4gICAgdmFyIHNldERlZmF1bHRPcHRpb25zID0gZnVuY3Rpb24oKXtcbiAgICAgICAgb3B0ID0gb3B0IHx8IHt9O1xuICAgICAgICAvLyBEZWZhdWx0IHNldHRpbmdzXG4gICAgICAgIG9wdC51c2VDYWNoZSA9IHRydWU7ICAvLyBjYWNoZSB0b2tlbml6ZWQgcGF0aHMgZm9yIHJlcGVhdGVkIHVzZVxuICAgICAgICBvcHQuc2ltcGxlID0gZmFsc2U7ICAgLy8gb25seSBzdXBwb3J0IGRvdC1zZXBhcmF0ZWQgcGF0aHMsIG5vIG90aGVyIHNwZWNpYWwgY2hhcmFjdGVyc1xuICAgICAgICBvcHQuZm9yY2UgPSBmYWxzZTsgICAgLy8gY3JlYXRlIGludGVybWVkaWF0ZSBwcm9wZXJ0aWVzIGR1cmluZyBgc2V0YCBvcGVyYXRpb25cblxuICAgICAgICAvLyBEZWZhdWx0IHByZWZpeCBzcGVjaWFsIGNoYXJhY3RlcnNcbiAgICAgICAgb3B0LnByZWZpeGVzID0ge1xuICAgICAgICAgICAgJ14nOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkUEFSRU5UXG4gICAgICAgICAgICB9LFxuICAgICAgICAgICAgJ34nOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkUk9PVFxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICclJzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJFBMQUNFSE9MREVSXG4gICAgICAgICAgICB9LFxuICAgICAgICAgICAgJ0AnOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkQ09OVEVYVFxuICAgICAgICAgICAgfVxuICAgICAgICB9O1xuICAgICAgICAvLyBEZWZhdWx0IHNlcGFyYXRvciBzcGVjaWFsIGNoYXJhY3RlcnNcbiAgICAgICAgb3B0LnNlcGFyYXRvcnMgPSB7XG4gICAgICAgICAgICAnLic6IHtcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRQUk9QRVJUWVxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnLCc6IHtcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRDT0xMRUNUSU9OXG4gICAgICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICc8Jzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJEVBQ0hcbiAgICAgICAgICAgIH1cbiAgICAgICAgfTtcbiAgICAgICAgLy8gRGVmYXVsdCBjb250YWluZXIgc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICAgIG9wdC5jb250YWluZXJzID0ge1xuICAgICAgICAgICAgJ1snOiB7XG4gICAgICAgICAgICAgICAgJ2Nsb3Nlcic6ICddJyxcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRQUk9QRVJUWVxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnXFwnJzoge1xuICAgICAgICAgICAgICAgICdjbG9zZXInOiAnXFwnJyxcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRTSU5HTEVRVU9URVxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnXCInOiB7XG4gICAgICAgICAgICAgICAgJ2Nsb3Nlcic6ICdcIicsXG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkRE9VQkxFUVVPVEVcbiAgICAgICAgICAgICAgICB9LFxuICAgICAgICAgICAgJygnOiB7XG4gICAgICAgICAgICAgICAgJ2Nsb3Nlcic6ICcpJyxcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRDQUxMXG4gICAgICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICd7Jzoge1xuICAgICAgICAgICAgICAgICdjbG9zZXInOiAnfScsXG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkRVZBTFBST1BFUlRZXG4gICAgICAgICAgICAgICAgfVxuICAgICAgICB9O1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBUZXN0IHN0cmluZyB0byBzZWUgaWYgaXQgaXMgc3Vycm91bmRlZCBieSBzaW5nbGUtIG9yIGRvdWJsZS1xdW90ZSwgdXNpbmcgdGhlXG4gICAgICogY3VycmVudCBjb25maWd1cmF0aW9uIGRlZmluaXRpb24gZm9yIHRob3NlIGNoYXJhY3RlcnMuIElmIG5vIHF1b3RlIGNvbnRhaW5lclxuICAgICAqIGlzIGRlZmluZWQsIHRoaXMgZnVuY3Rpb24gd2lsbCByZXR1cm4gZmFsc2Ugc2luY2UgaXQncyBub3QgcG9zc2libGUgdG8gcXVvdGVcbiAgICAgKiB0aGUgc3RyaW5nIGlmIHRoZXJlIGFyZSBubyBxdW90ZXMgaW4gdGhlIHN5bnRheC4gQWxzbyBpZ25vcmVzIGVzY2FwZWQgcXVvdGVcbiAgICAgKiBjaGFyYWN0ZXJzLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBzdHIgVGhlIHN0cmluZyB0byB0ZXN0IGZvciBlbmNsb3NpbmcgcXVvdGVzXG4gICAgICogQHJldHVybiB7Qm9vbGVhbn0gdHJ1ZSA9IHN0cmluZyBpcyBlbmNsb3NlZCBpbiBxdW90ZXM7IGZhbHNlID0gbm90IHF1b3RlZFxuICAgICAqL1xuICAgIHZhciBpc1F1b3RlZCA9IGZ1bmN0aW9uKHN0cil7XG4gICAgICAgIHZhciBjbGVhblN0ciA9IHN0ci5yZXBsYWNlKGVzY2FwZWRRdW90ZXMsICcnKTtcbiAgICAgICAgdmFyIHN0ckxlbiA9IGNsZWFuU3RyLmxlbmd0aDtcbiAgICAgICAgaWYgKHN0ckxlbiA8IDIpeyByZXR1cm4gZmFsc2U7IH1cbiAgICAgICAgcmV0dXJuICAoY2xlYW5TdHJbMF0gPT09IGNsZWFuU3RyW3N0ckxlbiAtIDFdKSAmJlxuICAgICAgICAgICAgICAgIChjbGVhblN0clswXSA9PT0gc2luZ2xlcXVvdGUgfHwgY2xlYW5TdHJbMF0gPT09IGRvdWJsZXF1b3RlKTtcbiAgICB9O1xuICAgIFxuICAgIC8qKlxuICAgICAqIFJlbW92ZSBlbmNsb3NpbmcgcXVvdGVzIGZyb20gYSBzdHJpbmcuIFRoZSBpc1F1b3RlZCBmdW5jdGlvbiB3aWxsIGRldGVybWluZVxuICAgICAqIGlmIGFueSBjaGFuZ2UgaXMgbmVlZGVkLiBJZiB0aGUgc3RyaW5nIGlzIHF1b3RlZCwgd2Uga25vdyB0aGUgZmlyc3QgYW5kIGxhc3RcbiAgICAgKiBjaGFyYWN0ZXJzIGFyZSBxdW90ZSBtYXJrcywgc28gc2ltcGx5IGRvIGEgc3RyaW5nIHNsaWNlLiBJZiB0aGUgaW5wdXQgdmFsdWUgaXNcbiAgICAgKiBub3QgcXVvdGVkLCByZXR1cm4gdGhlIGlucHV0IHZhbHVlIHVuY2hhbmdlZC4gQmVjYXVzZSBpc1F1b3RlZCBpcyB1c2VkLCBpZlxuICAgICAqIG5vIHF1b3RlIG1hcmtzIGFyZSBkZWZpbmVkIGluIHRoZSBzeW50YXgsIHRoaXMgZnVuY3Rpb24gd2lsbCByZXR1cm4gdGhlIGlucHV0IHZhbHVlLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBzdHIgVGhlIHN0cmluZyB0byB1bi1xdW90ZVxuICAgICAqIEByZXR1cm4ge1N0cmluZ30gVGhlIGlucHV0IHN0cmluZyB3aXRob3V0IGFueSBlbmNsb3NpbmcgcXVvdGUgbWFya3MuXG4gICAgICovXG4gICAgdmFyIHN0cmlwUXVvdGVzID0gZnVuY3Rpb24oc3RyKXtcbiAgICAgICAgaWYgKGlzUXVvdGVkKHN0cikpe1xuICAgICAgICAgICAgcmV0dXJuIHN0ci5zbGljZSgxLCAtMSk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHN0cjtcbiAgICB9O1xuICAgIFxuICAgIC8qKlxuICAgICAqIFNjYW4gaW5wdXQgc3RyaW5nIGZyb20gbGVmdCB0byByaWdodCwgb25lIGNoYXJhY3RlciBhdCBhIHRpbWUuIElmIGEgc3BlY2lhbCBjaGFyYWN0ZXJcbiAgICAgKiBpcyBmb3VuZCAob25lIG9mIFwic2VwYXJhdG9yc1wiLCBcImNvbnRhaW5lcnNcIiwgb3IgXCJwcmVmaXhlc1wiKSwgZWl0aGVyIHN0b3JlIHRoZSBhY2N1bXVsYXRlZFxuICAgICAqIHdvcmQgYXMgYSB0b2tlbiBvciBlbHNlIGJlZ2luIHdhdGNoaW5nIGlucHV0IGZvciBlbmQgb2YgdG9rZW4gKGZpbmRpbmcgYSBjbG9zaW5nIGNoYXJhY3RlclxuICAgICAqIGZvciBhIGNvbnRhaW5lciBvciB0aGUgZW5kIG9mIGEgY29sbGVjdGlvbikuIElmIGEgY29udGFpbmVyIGlzIGZvdW5kLCBjYXB0dXJlIHRoZSBzdWJzdHJpbmdcbiAgICAgKiB3aXRoaW4gdGhlIGNvbnRhaW5lciBhbmQgcmVjdXJzaXZlbHkgY2FsbCBgdG9rZW5pemVgIG9uIHRoYXQgc3Vic3RyaW5nLiBGaW5hbCBvdXRwdXQgd2lsbFxuICAgICAqIGJlIGFuIGFycmF5IG9mIHRva2Vucy4gQSBjb21wbGV4IHRva2VuIChub3QgYSBzaW1wbGUgcHJvcGVydHkgb3IgaW5kZXgpIHdpbGwgYmUgcmVwcmVzZW50ZWRcbiAgICAgKiBhcyBhbiBvYmplY3QgY2FycnlpbmcgbWV0YWRhdGEgZm9yIHByb2Nlc3NpbmcuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0gIHtTdHJpbmd9IHN0ciBQYXRoIHN0cmluZ1xuICAgICAqIEByZXR1cm4ge0FycmF5fSAgICAgQXJyYXkgb2YgdG9rZW5zIGZvdW5kIGluIHRoZSBpbnB1dCBwYXRoXG4gICAgICovXG4gICAgdmFyIHRva2VuaXplID0gZnVuY3Rpb24gKHN0cil7XG4gICAgICAgIHZhciBwYXRoID0gJycsXG4gICAgICAgICAgICBzaW1wbGVQYXRoID0gdHJ1ZSwgLy8gcGF0aCBpcyBhc3N1bWVkIFwic2ltcGxlXCIgdW50aWwgcHJvdmVuIG90aGVyd2lzZVxuICAgICAgICAgICAgdG9rZW5zID0gW10sXG4gICAgICAgICAgICByZWN1ciA9IFtdLFxuICAgICAgICAgICAgbW9kcyA9IHt9LFxuICAgICAgICAgICAgcGF0aExlbmd0aCA9IDAsXG4gICAgICAgICAgICB3b3JkID0gJycsXG4gICAgICAgICAgICBoYXNXaWxkY2FyZCA9IGZhbHNlLFxuICAgICAgICAgICAgZG9FYWNoID0gZmFsc2UsIC8vIG11c3QgcmVtZW1iZXIgdGhlIFwiZWFjaFwiIG9wZXJhdG9yIGludG8gdGhlIGZvbGxvd2luZyB0b2tlblxuICAgICAgICAgICAgc3VicGF0aCA9ICcnLFxuICAgICAgICAgICAgaSA9IDAsXG4gICAgICAgICAgICBvcGVuZXIgPSAnJyxcbiAgICAgICAgICAgIGNsb3NlciA9ICcnLFxuICAgICAgICAgICAgc2VwYXJhdG9yID0gJycsXG4gICAgICAgICAgICBjb2xsZWN0aW9uID0gW10sXG4gICAgICAgICAgICBkZXB0aCA9IDAsXG4gICAgICAgICAgICBlc2NhcGVkID0gMDtcblxuICAgICAgICBpZiAob3B0LnVzZUNhY2hlICYmIGNhY2hlW3N0cl0gIT09IFVOREVGKXsgcmV0dXJuIGNhY2hlW3N0cl07IH1cblxuICAgICAgICAvLyBTdHJpcCBvdXQgYW55IHVubmVjZXNzYXJ5IGVzY2FwaW5nIHRvIHNpbXBsaWZ5IHByb2Nlc3NpbmcgYmVsb3dcbiAgICAgICAgcGF0aCA9IHN0ci5yZXBsYWNlKGVzY2FwZWROb25TcGVjaWFsc1JlZ0V4LCAnJCYnLnN1YnN0cigxKSk7XG4gICAgICAgIHBhdGhMZW5ndGggPSBwYXRoLmxlbmd0aDtcblxuICAgICAgICBpZiAodHlwZW9mIHN0ciA9PT0gJFNUUklORyAmJiAhc2ltcGxlUGF0aFJlZ0V4LnRlc3Qoc3RyKSl7XG4gICAgICAgICAgICB0b2tlbnMgPSBwYXRoLnNwbGl0KHByb3BlcnR5U2VwYXJhdG9yKTtcbiAgICAgICAgICAgIG9wdC51c2VDYWNoZSAmJiAoY2FjaGVbc3RyXSA9IHt0OiB0b2tlbnMsIHNpbXBsZTogc2ltcGxlUGF0aH0pO1xuICAgICAgICAgICAgcmV0dXJuIHt0OiB0b2tlbnMsIHNpbXBsZTogc2ltcGxlUGF0aH07XG4gICAgICAgIH1cblxuICAgICAgICBmb3IgKGkgPSAwOyBpIDwgcGF0aExlbmd0aDsgaSsrKXtcbiAgICAgICAgICAgIC8vIFNraXAgZXNjYXBlIGNoYXJhY3RlciAoYFxcYCkgYW5kIHNldCBcImVzY2FwZWRcIiB0byB0aGUgaW5kZXggdmFsdWVcbiAgICAgICAgICAgIC8vIG9mIHRoZSBjaGFyYWN0ZXIgdG8gYmUgdHJlYXRlZCBhcyBhIGxpdGVyYWxcbiAgICAgICAgICAgIGlmICghZXNjYXBlZCAmJiBwYXRoW2ldID09PSAnXFxcXCcpe1xuICAgICAgICAgICAgICAgIC8vIE5leHQgY2hhcmFjdGVyIGlzIHRoZSBlc2NhcGVkIGNoYXJhY3RlclxuICAgICAgICAgICAgICAgIGVzY2FwZWQgPSBpKzE7XG4gICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gSWYgYSB3aWxkY2FyZCBjaGFyYWN0ZXIgaXMgZm91bmQsIG1hcmsgdGhpcyB0b2tlbiBhcyBoYXZpbmcgYSB3aWxkY2FyZFxuICAgICAgICAgICAgaWYgKHBhdGhbaV0gPT09ICRXSUxEQ0FSRCkge1xuICAgICAgICAgICAgICAgIGhhc1dpbGRjYXJkID0gdHJ1ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIElmIHdlIGhhdmUgYWxyZWFkeSBwcm9jZXNzZWQgYSBjb250YWluZXIgb3BlbmVyLCB0cmVhdCB0aGlzIHN1YnBhdGggc3BlY2lhbGx5XG4gICAgICAgICAgICBpZiAoZGVwdGggPiAwKXtcbiAgICAgICAgICAgICAgICAvLyBJcyB0aGlzIGNoYXJhY3RlciBhbm90aGVyIG9wZW5lciBmcm9tIHRoZSBzYW1lIGNvbnRhaW5lcj8gSWYgc28sIGFkZCB0b1xuICAgICAgICAgICAgICAgIC8vIHRoZSBkZXB0aCBsZXZlbCBzbyB3ZSBjYW4gbWF0Y2ggdGhlIGNsb3NlcnMgY29ycmVjdGx5LiAoRXhjZXB0IGZvciBxdW90ZXNcbiAgICAgICAgICAgICAgICAvLyB3aGljaCBjYW5ub3QgYmUgbmVzdGVkKVxuICAgICAgICAgICAgICAgIC8vIElzIHRoaXMgY2hhcmFjdGVyIHRoZSBjbG9zZXI/IElmIHNvLCBiYWNrIG91dCBvbmUgbGV2ZWwgb2YgZGVwdGguXG4gICAgICAgICAgICAgICAgLy8gQmUgY2FyZWZ1bDogcXVvdGUgY29udGFpbmVyIHVzZXMgc2FtZSBjaGFyYWN0ZXIgZm9yIG9wZW5lciBhbmQgY2xvc2VyLlxuICAgICAgICAgICAgICAgICFlc2NhcGVkICYmIHBhdGhbaV0gPT09IG9wZW5lciAmJiBvcGVuZXIgIT09IGNsb3Nlci5jbG9zZXIgJiYgZGVwdGgrKztcbiAgICAgICAgICAgICAgICAhZXNjYXBlZCAmJiBwYXRoW2ldID09PSBjbG9zZXIuY2xvc2VyICYmIGRlcHRoLS07XG5cbiAgICAgICAgICAgICAgICAvLyBXaGlsZSBzdGlsbCBpbnNpZGUgdGhlIGNvbnRhaW5lciwganVzdCBhZGQgdG8gdGhlIHN1YnBhdGhcbiAgICAgICAgICAgICAgICBpZiAoZGVwdGggPiAwKXtcbiAgICAgICAgICAgICAgICAgICAgc3VicGF0aCArPSBwYXRoW2ldO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBXaGVuIHdlIGNsb3NlIG9mZiB0aGUgY29udGFpbmVyLCB0aW1lIHRvIHByb2Nlc3MgdGhlIHN1YnBhdGggYW5kIGFkZCByZXN1bHRzIHRvIG91ciB0b2tlbnNcbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gSGFuZGxlIHN1YnBhdGggXCJbYmFyXVwiIGluIGZvby5bYmFyXSxbYmF6XSAtIHdlIG11c3QgcHJvY2VzcyBzdWJwYXRoIGFuZCBjcmVhdGUgYSBuZXcgY29sbGVjdGlvblxuICAgICAgICAgICAgICAgICAgICBpZiAoaSsxIDwgcGF0aExlbmd0aCAmJiBvcHQuc2VwYXJhdG9yc1twYXRoW2krMV1dICYmIG9wdC5zZXBhcmF0b3JzW3BhdGhbaSsxXV0uZXhlYyA9PT0gJENPTExFQ1RJT04pe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHN1YnBhdGgubGVuZ3RoICYmIGNsb3Nlci5leGVjID09PSAkUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0gc3RyaXBRdW90ZXMoc3VicGF0aCk7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjbG9zZXIuZXhlYyA9PT0gJFNJTkdMRVFVT1RFIHx8IGNsb3Nlci5leGVjID09PSAkRE9VQkxFUVVPVEUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0gc3VicGF0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0gdG9rZW5pemUoc3VicGF0aCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHJlY3VyID09PSBVTkRFRil7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ci5leGVjID0gY2xvc2VyLmV4ZWM7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIuZG9FYWNoID0gZG9FYWNoO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgLy8gY29sbGVjdGlvbi5wdXNoKGNsb3Nlci5leGVjID09PSAkUFJPUEVSVFkgPyByZWN1ci50WzBdIDogcmVjdXIpO1xuICAgICAgICAgICAgICAgICAgICAgICAgY29sbGVjdGlvbi5wdXNoKHJlY3VyKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBIYW5kbGUgc3VicGF0aCBcIltiYXpdXCIgaW4gZm9vLltiYXJdLFtiYXpdIC0gd2UgbXVzdCBwcm9jZXNzIHN1YnBhdGggYW5kIGFkZCB0byBjb2xsZWN0aW9uXG4gICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKGNvbGxlY3Rpb25bMF0pe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHN1YnBhdGgubGVuZ3RoICYmIGNsb3Nlci5leGVjID09PSAkUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0gc3RyaXBRdW90ZXMoc3VicGF0aCk7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjbG9zZXIuZXhlYyA9PT0gJFNJTkdMRVFVT1RFIHx8IGNsb3Nlci5leGVjID09PSAkRE9VQkxFUVVPVEUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0gc3VicGF0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0gdG9rZW5pemUoc3VicGF0aCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHJlY3VyID09PSBVTkRFRil7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ci5leGVjID0gY2xvc2VyLmV4ZWM7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIuZG9FYWNoID0gZG9FYWNoO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgY29sbGVjdGlvbi5wdXNoKHJlY3VyKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHRva2Vucy5wdXNoKHsndHQnOmNvbGxlY3Rpb24sICdkb0VhY2gnOmRvRWFjaH0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgY29sbGVjdGlvbiA9IFtdO1xuICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBTaW1wbGUgcHJvcGVydHkgY29udGFpbmVyIGlzIGVxdWl2YWxlbnQgdG8gZG90LXNlcGFyYXRlZCB0b2tlbi4gSnVzdCBhZGQgdGhpcyB0b2tlbiB0byB0b2tlbnMuXG4gICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKGNsb3Nlci5leGVjID09PSAkUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSB7dDpbc3RyaXBRdW90ZXMoc3VicGF0aCldfTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChkb0VhY2gpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHRva2Vucy5wdXNoKHsndyc6cmVjdXIudFswXSwgJ21vZHMnOnt9LCAnZG9FYWNoJzp0cnVlfSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBkb0VhY2ggPSBmYWxzZTsgLy8gcmVzZXRcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHRva2Vucy5wdXNoKHJlY3VyLnRbMF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBRdW90ZWQgc3VicGF0aCBpcyBhbGwgdGFrZW4gbGl0ZXJhbGx5IHdpdGhvdXQgdG9rZW4gZXZhbHVhdGlvbi4gSnVzdCBhZGQgc3VicGF0aCB0byB0b2tlbnMgYXMtaXMuXG4gICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKGNsb3Nlci5leGVjID09PSAkU0lOR0xFUVVPVEUgfHwgY2xvc2VyLmV4ZWMgPT09ICRET1VCTEVRVU9URSl7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAobW9kcy5oYXMpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHdvcmQgPSB7J3cnOiBzdWJwYXRoLCAnbW9kcyc6IG1vZHMsICdkb0VhY2gnOiBkb0VhY2h9O1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIG1vZHMgPSB7fTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2goc3VicGF0aCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSB0cnVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIE90aGVyd2lzZSwgY3JlYXRlIHRva2VuIG9iamVjdCB0byBob2xkIHRva2VuaXplZCBzdWJwYXRoLCBhZGQgdG8gdG9rZW5zLlxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChzdWJwYXRoID09PSAnJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSB7dDpbXSxzaW1wbGU6dHJ1ZX07XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHRva2VuaXplKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHJlY3VyID09PSBVTkRFRil7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmV4ZWMgPSBjbG9zZXIuZXhlYztcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmRvRWFjaCA9IGRvRWFjaDtcbiAgICAgICAgICAgICAgICAgICAgICAgIHRva2Vucy5wdXNoKHJlY3VyKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgc3VicGF0aCA9ICcnOyAvLyByZXNldCBzdWJwYXRoXG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gSWYgYSBwcmVmaXggY2hhcmFjdGVyIGlzIGZvdW5kLCBzdG9yZSBpdCBpbiBgbW9kc2AgZm9yIGxhdGVyIHJlZmVyZW5jZS5cbiAgICAgICAgICAgIC8vIE11c3Qga2VlcCBjb3VudCBkdWUgdG8gYHBhcmVudGAgcHJlZml4IHRoYXQgY2FuIGJlIHVzZWQgbXVsdGlwbGUgdGltZXMgaW4gb25lIHRva2VuLlxuICAgICAgICAgICAgZWxzZSBpZiAoIWVzY2FwZWQgJiYgcGF0aFtpXSBpbiBvcHQucHJlZml4ZXMgJiYgb3B0LnByZWZpeGVzW3BhdGhbaV1dLmV4ZWMpe1xuICAgICAgICAgICAgICAgIG1vZHMuaGFzID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICBpZiAobW9kc1tvcHQucHJlZml4ZXNbcGF0aFtpXV0uZXhlY10pIHsgbW9kc1tvcHQucHJlZml4ZXNbcGF0aFtpXV0uZXhlY10rKzsgfVxuICAgICAgICAgICAgICAgIGVsc2UgeyBtb2RzW29wdC5wcmVmaXhlc1twYXRoW2ldXS5leGVjXSA9IDE7IH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIElmIGEgc2VwYXJhdG9yIGlzIGZvdW5kLCB0aW1lIHRvIHN0b3JlIHRoZSB0b2tlbiB3ZSd2ZSBiZWVuIGFjY3VtdWxhdGluZy4gSWZcbiAgICAgICAgICAgIC8vIHRoaXMgdG9rZW4gaGFkIGEgcHJlZml4LCB3ZSBzdG9yZSB0aGUgdG9rZW4gYXMgYW4gb2JqZWN0IHdpdGggbW9kaWZpZXIgZGF0YS5cbiAgICAgICAgICAgIC8vIElmIHRoZSBzZXBhcmF0b3IgaXMgdGhlIGNvbGxlY3Rpb24gc2VwYXJhdG9yLCB3ZSBtdXN0IGVpdGhlciBjcmVhdGUgb3IgYWRkXG4gICAgICAgICAgICAvLyB0byBhIGNvbGxlY3Rpb24gZm9yIHRoaXMgdG9rZW4uIEZvciBzaW1wbGUgc2VwYXJhdG9yLCB3ZSBlaXRoZXIgYWRkIHRoZSB0b2tlblxuICAgICAgICAgICAgLy8gdG8gdGhlIHRva2VuIGxpc3Qgb3IgZWxzZSBhZGQgdG8gdGhlIGV4aXN0aW5nIGNvbGxlY3Rpb24gaWYgaXQgZXhpc3RzLlxuICAgICAgICAgICAgZWxzZSBpZiAoIWVzY2FwZWQgJiYgb3B0LnNlcGFyYXRvcnNbcGF0aFtpXV0gJiYgb3B0LnNlcGFyYXRvcnNbcGF0aFtpXV0uZXhlYyl7XG4gICAgICAgICAgICAgICAgc2VwYXJhdG9yID0gb3B0LnNlcGFyYXRvcnNbcGF0aFtpXV07XG4gICAgICAgICAgICAgICAgaWYgKCF3b3JkICYmIChtb2RzLmhhcyB8fCBoYXNXaWxkY2FyZCkpe1xuICAgICAgICAgICAgICAgICAgICAvLyBmb3VuZCBhIHNlcGFyYXRvciwgYWZ0ZXIgc2VlaW5nIHByZWZpeGVzLCBidXQgbm8gdG9rZW4gd29yZCAtPiBpbnZhbGlkXG4gICAgICAgICAgICAgICAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIFRoaXMgdG9rZW4gd2lsbCByZXF1aXJlIHNwZWNpYWwgaW50ZXJwcmV0ZXIgcHJvY2Vzc2luZyBkdWUgdG8gcHJlZml4IG9yIHdpbGRjYXJkLlxuICAgICAgICAgICAgICAgIGlmICh3b3JkICYmIChtb2RzLmhhcyB8fCBoYXNXaWxkY2FyZCB8fCBkb0VhY2gpKXtcbiAgICAgICAgICAgICAgICAgICAgd29yZCA9IHsndyc6IHdvcmQsICdtb2RzJzogbW9kcywgJ2RvRWFjaCc6IGRvRWFjaH07XG4gICAgICAgICAgICAgICAgICAgIG1vZHMgPSB7fTtcbiAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gd29yZCBpcyBhIHBsYWluIHByb3BlcnR5IG9yIGVuZCBvZiBjb2xsZWN0aW9uXG4gICAgICAgICAgICAgICAgaWYgKHNlcGFyYXRvci5leGVjID09PSAkUFJPUEVSVFkgfHwgc2VwYXJhdG9yLmV4ZWMgPT09ICRFQUNIKXtcbiAgICAgICAgICAgICAgICAgICAgLy8gd2UgYXJlIGdhdGhlcmluZyBhIGNvbGxlY3Rpb24sIHNvIGFkZCBsYXN0IHdvcmQgdG8gY29sbGVjdGlvbiBhbmQgdGhlbiBzdG9yZVxuICAgICAgICAgICAgICAgICAgICBpZiAoY29sbGVjdGlvblswXSAhPT0gVU5ERUYpe1xuICAgICAgICAgICAgICAgICAgICAgICAgd29yZCAmJiBjb2xsZWN0aW9uLnB1c2god29yZCk7XG4gICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaCh7J3R0Jzpjb2xsZWN0aW9uLCAnZG9FYWNoJzpkb0VhY2h9KTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbGxlY3Rpb24gPSBbXTsgLy8gcmVzZXRcbiAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gd29yZCBpcyBhIHBsYWluIHByb3BlcnR5XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgd29yZCAmJiB0b2tlbnMucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBJZiB0aGUgc2VwYXJhdG9yIGlzIHRoZSBcImVhY2hcIiBzZXBhcnRvciwgdGhlIGZvbGxvd2luZyB3b3JkIHdpbGwgYmUgZXZhbHVhdGVkIGRpZmZlcmVudGx5LlxuICAgICAgICAgICAgICAgICAgICAvLyBJZiBpdCdzIG5vdCB0aGUgXCJlYWNoXCIgc2VwYXJhdG9yLCB0aGVuIHJlc2V0IFwiZG9FYWNoXCJcbiAgICAgICAgICAgICAgICAgICAgZG9FYWNoID0gc2VwYXJhdG9yLmV4ZWMgPT09ICRFQUNIOyAvLyByZXNldFxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyB3b3JkIGlzIGEgY29sbGVjdGlvblxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKHNlcGFyYXRvci5leGVjID09PSAkQ09MTEVDVElPTil7XG4gICAgICAgICAgICAgICAgICAgIHdvcmQgJiYgY29sbGVjdGlvbi5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB3b3JkID0gJyc7IC8vIHJlc2V0XG4gICAgICAgICAgICAgICAgaGFzV2lsZGNhcmQgPSBmYWxzZTsgLy8gcmVzZXRcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIEZvdW5kIGEgY29udGFpbmVyIG9wZW5pbmcgY2hhcmFjdGVyLiBBIGNvbnRhaW5lciBvcGVuaW5nIGlzIGVxdWl2YWxlbnQgdG9cbiAgICAgICAgICAgIC8vIGZpbmRpbmcgYSBzZXBhcmF0b3IsIHNvIFwiZm9vLmJhclwiIGlzIGVxdWl2YWxlbnQgdG8gXCJmb29bYmFyXVwiLCBzbyBhcHBseSBzaW1pbGFyXG4gICAgICAgICAgICAvLyBwcm9jZXNzIGFzIHNlcGFyYXRvciBhYm92ZSB3aXRoIHJlc3BlY3QgdG8gdG9rZW4gd2UgaGF2ZSBhY2N1bXVsYXRlZCBzbyBmYXIuXG4gICAgICAgICAgICAvLyBFeGNlcHQgaW4gY2FzZSBjb2xsZWN0aW9ucyAtIHBhdGggbWF5IGhhdmUgYSBjb2xsZWN0aW9uIG9mIGNvbnRhaW5lcnMsIHNvXG4gICAgICAgICAgICAvLyBpbiBcImZvb1tiYXJdLFtiYXpdXCIsIHRoZSBcIltiYXJdXCIgbWFya3MgdGhlIGVuZCBvZiB0b2tlbiBcImZvb1wiLCBidXQgXCJbYmF6XVwiIGlzXG4gICAgICAgICAgICAvLyBtZXJlbHkgYW5vdGhlciBlbnRyeSBpbiB0aGUgY29sbGVjdGlvbiwgc28gd2UgZG9uJ3QgY2xvc2Ugb2ZmIHRoZSBjb2xsZWN0aW9uIHRva2VuXG4gICAgICAgICAgICAvLyB5ZXQuXG4gICAgICAgICAgICAvLyBTZXQgZGVwdGggdmFsdWUgZm9yIGZ1cnRoZXIgcHJvY2Vzc2luZy5cbiAgICAgICAgICAgIGVsc2UgaWYgKCFlc2NhcGVkICYmIG9wdC5jb250YWluZXJzW3BhdGhbaV1dICYmIG9wdC5jb250YWluZXJzW3BhdGhbaV1dLmV4ZWMpe1xuICAgICAgICAgICAgICAgIGNsb3NlciA9IG9wdC5jb250YWluZXJzW3BhdGhbaV1dO1xuICAgICAgICAgICAgICAgIGlmICh3b3JkICYmIChtb2RzLmhhcyB8fCBoYXNXaWxkY2FyZCB8fCBkb0VhY2gpKXtcbiAgICAgICAgICAgICAgICAgICAgaWYgKHR5cGVvZiB3b3JkID09PSAnc3RyaW5nJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICB3b3JkID0geyd3Jzogd29yZCwgJ21vZHMnOiBtb2RzLCAnZG9FYWNoJzpkb0VhY2h9O1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgd29yZC5tb2RzID0gbW9kcztcbiAgICAgICAgICAgICAgICAgICAgICAgIHdvcmQuZG9FYWNoID0gZG9FYWNoO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIG1vZHMgPSB7fTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgaWYgKGNvbGxlY3Rpb25bMF0gIT09IFVOREVGKXtcbiAgICAgICAgICAgICAgICAgICAgLy8gd2UgYXJlIGdhdGhlcmluZyBhIGNvbGxlY3Rpb24sIHNvIGFkZCBsYXN0IHdvcmQgdG8gY29sbGVjdGlvbiBhbmQgdGhlbiBzdG9yZVxuICAgICAgICAgICAgICAgICAgICB3b3JkICYmIGNvbGxlY3Rpb24ucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIHdvcmQgaXMgYSBwbGFpbiBwcm9wZXJ0eVxuICAgICAgICAgICAgICAgICAgICB3b3JkICYmIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIG9wZW5lciA9IHBhdGhbaV07XG4gICAgICAgICAgICAgICAgLy8gMSkgZG9uJ3QgcmVzZXQgZG9FYWNoIGZvciBlbXB0eSB3b3JkIGJlY2F1c2UgdGhpcyBpcyBbZm9vXTxbYmFyXVxuICAgICAgICAgICAgICAgIC8vIDIpIGRvbid0IHJlc2V0IGRvRWFjaCBmb3Igb3BlbmluZyBDYWxsIGJlY2F1c2UgdGhpcyBpcyBhLGI8Zm4oKVxuICAgICAgICAgICAgICAgIGlmICh3b3JkICYmIG9wdC5jb250YWluZXJzW29wZW5lcl0uZXhlYyAhPT0gJENBTEwpe1xuICAgICAgICAgICAgICAgICAgICBkb0VhY2ggPSBmYWxzZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgd29yZCA9ICcnO1xuICAgICAgICAgICAgICAgIGhhc1dpbGRjYXJkID0gZmFsc2U7XG4gICAgICAgICAgICAgICAgZGVwdGgrKztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIE90aGVyd2lzZSwgdGhpcyBpcyBqdXN0IGFub3RoZXIgY2hhcmFjdGVyIHRvIGFkZCB0byB0aGUgY3VycmVudCB0b2tlblxuICAgICAgICAgICAgZWxzZSBpZiAoaSA8IHBhdGhMZW5ndGgpIHtcbiAgICAgICAgICAgICAgICB3b3JkICs9IHBhdGhbaV07XG4gICAgICAgICAgICB9XG5cbiAgICAgICAgICAgIC8vIElmIGN1cnJlbnQgcGF0aCBpbmRleCBtYXRjaGVzIHRoZSBlc2NhcGUgaW5kZXggdmFsdWUsIHJlc2V0IGBlc2NhcGVkYFxuICAgICAgICAgICAgaWYgKGkgPCBwYXRoTGVuZ3RoICYmIGkgPT09IGVzY2FwZWQpe1xuICAgICAgICAgICAgICAgIGVzY2FwZWQgPSAwO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG5cbiAgICAgICAgLy8gUGF0aCBlbmRlZCBpbiBhbiBlc2NhcGUgY2hhcmFjdGVyXG4gICAgICAgIGlmIChlc2NhcGVkKXtcbiAgICAgICAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgICAgIH1cblxuICAgICAgICAvLyBBZGQgdHJhaWxpbmcgd29yZCB0byB0b2tlbnMsIGlmIHByZXNlbnRcbiAgICAgICAgaWYgKHR5cGVvZiB3b3JkID09PSAnc3RyaW5nJyAmJiB3b3JkICYmIChtb2RzLmhhcyB8fCBoYXNXaWxkY2FyZCB8fCBkb0VhY2gpKXtcbiAgICAgICAgICAgIHdvcmQgPSB7J3cnOiB3b3JkLCAnbW9kcyc6IHdvcmQubW9kcyB8fCBtb2RzLCAnZG9FYWNoJzogZG9FYWNofTtcbiAgICAgICAgICAgIG1vZHMgPSB7fTtcbiAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAod29yZCAmJiBtb2RzLmhhcyl7XG4gICAgICAgICAgICB3b3JkLm1vZHMgPSBtb2RzO1xuICAgICAgICB9XG4gICAgICAgIC8vIFdlIGFyZSBnYXRoZXJpbmcgYSBjb2xsZWN0aW9uLCBzbyBhZGQgbGFzdCB3b3JkIHRvIGNvbGxlY3Rpb24gYW5kIHRoZW4gc3RvcmVcbiAgICAgICAgaWYgKGNvbGxlY3Rpb25bMF0gIT09IFVOREVGKXtcbiAgICAgICAgICAgIHdvcmQgJiYgY29sbGVjdGlvbi5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgdG9rZW5zLnB1c2goeyd0dCc6Y29sbGVjdGlvbiwgJ2RvRWFjaCc6ZG9FYWNofSk7XG4gICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICB9XG4gICAgICAgIC8vIFdvcmQgaXMgYSBwbGFpbiBwcm9wZXJ0eVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHdvcmQgJiYgdG9rZW5zLnB1c2god29yZCk7XG4gICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgIH1cblxuICAgICAgICAvLyBkZXB0aCAhPSAwIG1lYW5zIG1pc21hdGNoZWQgY29udGFpbmVyc1xuICAgICAgICBpZiAoZGVwdGggIT09IDApeyByZXR1cm4gdW5kZWZpbmVkOyB9XG5cbiAgICAgICAgLy8gSWYgcGF0aCB3YXMgdmFsaWQsIGNhY2hlIHRoZSByZXN1bHRcbiAgICAgICAgb3B0LnVzZUNhY2hlICYmIChjYWNoZVtzdHJdID0ge3Q6IHRva2Vucywgc2ltcGxlOiBzaW1wbGVQYXRofSk7XG5cbiAgICAgICAgcmV0dXJuIHt0OiB0b2tlbnMsIHNpbXBsZTogc2ltcGxlUGF0aH07XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEl0IGlzIGByZXNvbHZlUGF0aGAncyBqb2IgdG8gdHJhdmVyc2UgYW4gb2JqZWN0IGFjY29yZGluZyB0byB0aGUgdG9rZW5zXG4gICAgICogZGVyaXZlZCBmcm9tIHRoZSBrZXlwYXRoIGFuZCBlaXRoZXIgcmV0dXJuIHRoZSB2YWx1ZSBmb3VuZCB0aGVyZSBvciBzZXRcbiAgICAgKiBhIG5ldyB2YWx1ZSBpbiB0aGF0IGxvY2F0aW9uLlxuICAgICAqIFRoZSB0b2tlbnMgYXJlIGEgc2ltcGxlIGFycmF5IGFuZCBgcmVvc2x2ZVBhdGhgIGxvb3BzIHRocm91Z2ggdGhlIGxpc3RcbiAgICAgKiB3aXRoIGEgc2ltcGxlIFwid2hpbGVcIiBsb29wLiBBIHRva2VuIG1heSBpdHNlbGYgYmUgYSBuZXN0ZWQgdG9rZW4gYXJyYXksXG4gICAgICogd2hpY2ggaXMgcHJvY2Vzc2VkIHRocm91Z2ggcmVjdXJzaW9uLlxuICAgICAqIEFzIGVhY2ggc3VjY2Vzc2l2ZSB2YWx1ZSBpcyByZXNvbHZlZCB3aXRoaW4gYG9iamAsIHRoZSBjdXJyZW50IHZhbHVlIGlzXG4gICAgICogcHVzaGVkIG9udG8gdGhlIFwidmFsdWVTdGFja1wiLCBlbmFibGluZyBiYWNrd2FyZCByZWZlcmVuY2VzICh1cHdhcmRzIGluIGBvYmpgKVxuICAgICAqIHRocm91Z2ggcGF0aCBwcmVmaXhlcyBsaWtlIFwiPFwiIGZvciBcInBhcmVudFwiIGFuZCBcIn5cIiBmb3IgXCJyb290XCIuIFRoZSBsb29wXG4gICAgICogc2hvcnQtY2lyY3VpdHMgYnkgcmV0dXJuaW5nIGB1bmRlZmluZWRgIGlmIHRoZSBwYXRoIGlzIGludmFsaWQgYXQgYW55IHBvaW50LFxuICAgICAqIGV4Y2VwdCBpbiBgc2V0YCBzY2VuYXJpbyB3aXRoIGBmb3JjZWAgZW5hYmxlZC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSAge09iamVjdH0gb2JqICAgICAgICBUaGUgZGF0YSBvYmplY3QgdG8gYmUgcmVhZC93cml0dGVuXG4gICAgICogQHBhcmFtICB7U3RyaW5nfSBwYXRoICAgICAgIFRoZSBrZXlwYXRoIHdoaWNoIGByZXNvbHZlUGF0aGAgd2lsbCBldmFsdWF0ZSBhZ2FpbnN0IGBvYmpgLiBNYXkgYmUgYSBwcmUtY29tcGlsZWQgVG9rZW5zIHNldCBpbnN0ZWFkIG9mIGEgc3RyaW5nLlxuICAgICAqIEBwYXJhbSAge0FueX0gbmV3VmFsdWUgICBUaGUgbmV3IHZhbHVlIHRvIHNldCBhdCB0aGUgcG9pbnQgZGVzY3JpYmVkIGJ5IGBwYXRoYC4gVW5kZWZpbmVkIGlmIHVzZWQgaW4gYGdldGAgc2NlbmFyaW8uXG4gICAgICogQHBhcmFtICB7QXJyYXl9IGFyZ3MgICAgICAgQXJyYXkgb2YgZXh0cmEgYXJndW1lbnRzIHdoaWNoIG1heSBiZSByZWZlcmVuY2VkIGJ5IHBsYWNlaG9sZGVycy4gVW5kZWZpbmVkIGlmIG5vIGV4dHJhIGFyZ3VtZW50cyB3ZXJlIGdpdmVuLlxuICAgICAqIEBwYXJhbSAge0FycmF5fSB2YWx1ZVN0YWNrIFN0YWNrIG9mIG9iamVjdCBjb250ZXh0cyBhY2N1bXVsYXRlZCBhcyB0aGUgcGF0aCB0b2tlbnMgYXJlIHByb2Nlc3NlZCBpbiBgb2JqYFxuICAgICAqIEByZXR1cm4ge0FueX0gICAgICAgICAgICBJbiBgZ2V0YCwgcmV0dXJucyB0aGUgdmFsdWUgZm91bmQgaW4gYG9iamAgYXQgYHBhdGhgLiBJbiBgc2V0YCwgcmV0dXJucyB0aGUgbmV3IHZhbHVlIHRoYXQgd2FzIHNldCBpbiBgb2JqYC4gSWYgYGdldGAgb3IgYHNldGAgYXJlIG50byBzdWNjZXNzZnVsLCByZXR1cm5zIGB1bmRlZmluZWRgXG4gICAgICovXG4gICAgdmFyIHJlc29sdmVQYXRoID0gZnVuY3Rpb24gKG9iaiwgcGF0aCwgbmV3VmFsdWUsIGFyZ3MsIHZhbHVlU3RhY2spe1xuICAgICAgICB2YXIgY2hhbmdlID0gbmV3VmFsdWUgIT09IFVOREVGLCAvLyBhcmUgd2Ugc2V0dGluZyBhIG5ldyB2YWx1ZT9cbiAgICAgICAgICAgIHRrID0gW10sXG4gICAgICAgICAgICB0a0xlbmd0aCA9IDAsXG4gICAgICAgICAgICB0a0xhc3RJZHggPSAwLFxuICAgICAgICAgICAgdmFsdWVTdGFja0xlbmd0aCA9IDEsXG4gICAgICAgICAgICBpID0gMCwgaiA9IDAsXG4gICAgICAgICAgICBwcmV2ID0gb2JqLFxuICAgICAgICAgICAgY3VyciA9ICcnLFxuICAgICAgICAgICAgY3Vyckxlbmd0aCA9IDAsXG4gICAgICAgICAgICBlYWNoTGVuZ3RoID0gMCxcbiAgICAgICAgICAgIHdvcmRDb3B5ID0gJycsXG4gICAgICAgICAgICBjb250ZXh0UHJvcCxcbiAgICAgICAgICAgIGlkeCA9IDAsXG4gICAgICAgICAgICBjb250ZXh0ID0gb2JqLFxuICAgICAgICAgICAgcmV0LFxuICAgICAgICAgICAgbmV3VmFsdWVIZXJlID0gZmFsc2UsXG4gICAgICAgICAgICBwbGFjZUludCA9IDAsXG4gICAgICAgICAgICBwcm9wID0gJycsXG4gICAgICAgICAgICBjYWxsQXJncztcblxuICAgICAgICAvLyBGb3IgU3RyaW5nIHBhdGgsIGVpdGhlciBmZXRjaCB0b2tlbnMgZnJvbSBjYWNoZSBvciBmcm9tIGB0b2tlbml6ZWAuXG4gICAgICAgIGlmICh0eXBlb2YgcGF0aCA9PT0gJFNUUklORyl7XG4gICAgICAgICAgICBpZiAob3B0LnVzZUNhY2hlICYmIGNhY2hlW3BhdGhdKSB7IHRrID0gY2FjaGVbcGF0aF0udDsgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGsgPSB0b2tlbml6ZShwYXRoKTtcbiAgICAgICAgICAgICAgICBpZiAodGsgPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgIHRrID0gdGsudDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICAvLyBGb3IgYSBub24tc3RyaW5nLCBhc3N1bWUgYSBwcmUtY29tcGlsZWQgdG9rZW4gYXJyYXlcbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0ayA9IHBhdGgudCA/IHBhdGgudCA6IFtwYXRoXTtcbiAgICAgICAgfVxuXG4gICAgICAgIHRrTGVuZ3RoID0gdGsubGVuZ3RoO1xuICAgICAgICBpZiAodGtMZW5ndGggPT09IDApIHsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICB0a0xhc3RJZHggPSB0a0xlbmd0aCAtIDE7XG5cbiAgICAgICAgLy8gdmFsdWVTdGFjayB3aWxsIGJlIGFuIGFycmF5IGlmIHdlIGFyZSB3aXRoaW4gYSByZWN1cnNpdmUgY2FsbCB0byBgcmVzb2x2ZVBhdGhgXG4gICAgICAgIGlmICh2YWx1ZVN0YWNrKXtcbiAgICAgICAgICAgIHZhbHVlU3RhY2tMZW5ndGggPSB2YWx1ZVN0YWNrLmxlbmd0aDtcbiAgICAgICAgfVxuICAgICAgICAvLyBPbiBvcmlnaW5hbCBlbnRyeSB0byBgcmVzb2x2ZVBhdGhgLCBpbml0aWFsaXplIHZhbHVlU3RhY2sgd2l0aCB0aGUgYmFzZSBvYmplY3QuXG4gICAgICAgIC8vIHZhbHVlU3RhY2tMZW5ndGggd2FzIGFscmVhZHkgaW5pdGlhbGl6ZWQgdG8gMS5cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB2YWx1ZVN0YWNrID0gW29ial07XG4gICAgICAgIH1cblxuICAgICAgICAvLyBDb252ZXJ0ZWQgQXJyYXkucmVkdWNlIGludG8gd2hpbGUgbG9vcCwgc3RpbGwgdXNpbmcgXCJwcmV2XCIsIFwiY3VyclwiLCBcImlkeFwiXG4gICAgICAgIC8vIGFzIGxvb3AgdmFsdWVzXG4gICAgICAgIHdoaWxlIChwcmV2ICE9PSBVTkRFRiAmJiBpZHggPCB0a0xlbmd0aCl7XG4gICAgICAgICAgICBjdXJyID0gdGtbaWR4XTtcblxuICAgICAgICAgICAgLy8gSWYgd2UgYXJlIHNldHRpbmcgYSBuZXcgdmFsdWUgYW5kIHRoaXMgdG9rZW4gaXMgdGhlIGxhc3QgdG9rZW4sIHRoaXNcbiAgICAgICAgICAgIC8vIGlzIHRoZSBwb2ludCB3aGVyZSB0aGUgbmV3IHZhbHVlIG11c3QgYmUgc2V0LlxuICAgICAgICAgICAgbmV3VmFsdWVIZXJlID0gKGNoYW5nZSAmJiAoaWR4ID09PSB0a0xhc3RJZHgpKTtcblxuICAgICAgICAgICAgLy8gSGFuZGxlIG1vc3QgY29tbW9uIHNpbXBsZSBwYXRoIHNjZW5hcmlvIGZpcnN0XG4gICAgICAgICAgICBpZiAodHlwZW9mIGN1cnIgPT09ICRTVFJJTkcpe1xuICAgICAgICAgICAgICAgIC8vIElmIHdlIGFyZSBzZXR0aW5nLi4uXG4gICAgICAgICAgICAgICAgaWYgKGNoYW5nZSl7XG4gICAgICAgICAgICAgICAgICAgIC8vIElmIHRoaXMgaXMgdGhlIGZpbmFsIHRva2VuIHdoZXJlIHRoZSBuZXcgdmFsdWUgZ29lcywgc2V0IGl0XG4gICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtjdXJyXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRbY3Vycl0gIT09IG5ld1ZhbHVlKXsgcmV0dXJuIHVuZGVmaW5lZDsgfSAvLyBuZXcgdmFsdWUgZmFpbGVkIHRvIHNldFxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIEZvciBlYXJsaWVyIHRva2VucywgY3JlYXRlIG9iamVjdCBwcm9wZXJ0aWVzIGlmIFwiZm9yY2VcIiBpcyBlbmFibGVkXG4gICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKG9wdC5mb3JjZSAmJiB0eXBlb2YgY29udGV4dFtjdXJyXSA9PT0gJ3VuZGVmaW5lZCcpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbY3Vycl0gPSB7fTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBSZXR1cm4gdmFsdWUgaXMgYXNzaWduZWQgYXMgdmFsdWUgb2YgdGhpcyBvYmplY3QgcHJvcGVydHlcbiAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0W2N1cnJdO1xuXG4gICAgICAgICAgICAgICAgLy8gVGhpcyBiYXNpYyBzdHJ1Y3R1cmUgaXMgcmVwZWF0ZWQgaW4gb3RoZXIgc2NlbmFyaW9zIGJlbG93LCBzbyB0aGUgbG9naWNcbiAgICAgICAgICAgICAgICAvLyBwYXR0ZXJuIGlzIG9ubHkgZG9jdW1lbnRlZCBoZXJlIGZvciBicmV2aXR5LlxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGN1cnIgPT09IFVOREVGKXtcbiAgICAgICAgICAgICAgICAgICAgcmV0ID0gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChjdXJyLnR0KXtcbiAgICAgICAgICAgICAgICAgICAgLy8gQ2FsbCByZXNvbHZlUGF0aCBhZ2FpbiB3aXRoIGJhc2UgdmFsdWUgYXMgZXZhbHVhdGVkIHZhbHVlIHNvIGZhciBhbmRcbiAgICAgICAgICAgICAgICAgICAgLy8gZWFjaCBlbGVtZW50IG9mIGFycmF5IGFzIHRoZSBwYXRoLiBDb25jYXQgYWxsIHRoZSByZXN1bHRzIHRvZ2V0aGVyLlxuICAgICAgICAgICAgICAgICAgICByZXQgPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuZG9FYWNoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmICghQXJyYXkuaXNBcnJheShjb250ZXh0KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGogPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgZWFjaExlbmd0aCA9IGNvbnRleHQubGVuZ3RoO1xuICAgICAgICAgICAgICAgICAgICAgICAgXG4gICAgICAgICAgICAgICAgICAgICAgICAvLyBQYXRoIGxpa2UgQXJyYXktPkVhY2gtPkFycmF5IHJlcXVpcmVzIGEgbmVzdGVkIGZvciBsb29wXG4gICAgICAgICAgICAgICAgICAgICAgICAvLyB0byBwcm9jZXNzIHRoZSB0d28gYXJyYXkgbGF5ZXJzLlxuICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaiA8IGVhY2hMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGkgPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKFtdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBjdXJyTGVuZ3RoID0gY3Vyci50dC5sZW5ndGg7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaSA8IGN1cnJMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjdXJyLnR0W2ldLmRvRWFjaCA9IGZhbHNlOyAvLyBUaGlzIGlzIGEgaGFjaywgZG9uJ3Qga25vdyBob3cgZWxzZSB0byBkaXNhYmxlIFwiZG9FYWNoXCIgZm9yIGNvbGxlY3Rpb24gbWVtYmVyc1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gcmVzb2x2ZVBhdGgoY29udGV4dFtqXSwgY3Vyci50dFtpXSwgbmV3VmFsdWUsIGFyZ3MsIHZhbHVlU3RhY2spO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHR5cGVvZiBjdXJyLnR0W2ldID09PSAnc3RyaW5nJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0UHJvcCA9IGNvbnRleHRbal1bY3Vyci50dFtpXV07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0UHJvcCA9IHJlc29sdmVQYXRoKGNvbnRleHRbal0sIGN1cnIudHRbaV0sIHVuZGVmaW5lZCwgYXJncywgdmFsdWVTdGFjayk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRQcm9wID09PSBVTkRFRikgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgIFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnR0W2ldLnQgJiYgY3Vyci50dFtpXS5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W2pdW2NvbnRleHRQcm9wXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXRbal0ucHVzaChjb250ZXh0UHJvcCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci50dFtpXS50ICYmIGN1cnIudHRbaV0uZXhlYyA9PT0gJEVWQUxQUk9QRVJUWSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0W2pdLnB1c2goY29udGV4dFtqXVtjb250ZXh0UHJvcF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXRbal0ucHVzaChjb250ZXh0UHJvcCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBqKys7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpID0gMDtcbiAgICAgICAgICAgICAgICAgICAgICAgIGN1cnJMZW5ndGggPSBjdXJyLnR0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdoaWxlKGkgPCBjdXJyTGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSByZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLnR0W2ldLCBuZXdWYWx1ZSwgYXJncywgdmFsdWVTdGFjayk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHR5cGVvZiBjdXJyLnR0W2ldID09PSAnc3RyaW5nJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gY29udGV4dFtjdXJyLnR0W2ldXTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gcmVzb2x2ZVBhdGgoY29udGV4dCwgY3Vyci50dFtpXSwgdW5kZWZpbmVkLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRQcm9wID09PSBVTkRFRikgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnR0W2ldLnQgJiYgY3Vyci50dFtpXS5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbY29udGV4dFByb3BdID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0UHJvcCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnR0W2ldLnQgJiYgY3Vyci50dFtpXS5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbY29udGV4dFByb3BdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRQcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpKys7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoY3Vyci53KXtcbiAgICAgICAgICAgICAgICAgICAgLy8gdGhpcyB3b3JkIHRva2VuIGhhcyBtb2RpZmllcnNcbiAgICAgICAgICAgICAgICAgICAgd29yZENvcHkgPSBjdXJyLnc7XG4gICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMuaGFzKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMucGFyZW50KXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBtb2RpZnkgY3VycmVudCBjb250ZXh0LCBzaGlmdCB1cHdhcmRzIGluIGJhc2Ugb2JqZWN0IG9uZSBsZXZlbFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHQgPSB2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAxIC0gY3Vyci5tb2RzLnBhcmVudF07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHQgPT09IFVOREVGKSB7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMucm9vdCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gUmVzZXQgY29udGV4dCBhbmQgdmFsdWVTdGFjaywgc3RhcnQgb3ZlciBhdCByb290IGluIHRoaXMgY29udGV4dFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHQgPSB2YWx1ZVN0YWNrWzBdO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHZhbHVlU3RhY2sgPSBbY29udGV4dF07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdmFsdWVTdGFja0xlbmd0aCA9IDE7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5tb2RzLnBsYWNlaG9sZGVyKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBwbGFjZUludCA9IHdvcmRDb3B5IC0gMTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoYXJnc1twbGFjZUludF0gPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIEZvcmNlIGFyZ3NbcGxhY2VJbnRdIHRvIFN0cmluZywgd29uJ3QgYXR0ZW1wdCB0byBwcm9jZXNzXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gYXJnIG9mIHR5cGUgZnVuY3Rpb24sIGFycmF5LCBvciBwbGFpbiBvYmplY3RcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB3b3JkQ29weSA9IGFyZ3NbcGxhY2VJbnRdLnRvU3RyaW5nKCk7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cblxuICAgICAgICAgICAgICAgICAgICAvLyBkb0VhY2ggb3B0aW9uIG1lYW5zIHRvIHRha2UgYWxsIHZhbHVlcyBpbiBjb250ZXh0IChtdXN0IGJlIGFuIGFycmF5KSwgYXBwbHlcbiAgICAgICAgICAgICAgICAgICAgLy8gXCJjdXJyXCIgdG8gZWFjaCBvbmUsIGFuZCByZXR1cm4gdGhlIG5ldyBhcnJheS4gT3BlcmF0ZXMgbGlrZSBBcnJheS5tYXAuXG4gICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLmRvRWFjaCl7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoIUFycmF5LmlzQXJyYXkoY29udGV4dCkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGkgPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgZWFjaExlbmd0aCA9IGNvbnRleHQubGVuZ3RoO1xuICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaSA8IGVhY2hMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIFwiY29udGV4dFwiIG1vZGlmaWVyIChcIkBcIiBieSBkZWZhdWx0KSByZXBsYWNlcyBjdXJyZW50IGNvbnRleHQgd2l0aCBhIHZhbHVlIGZyb21cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyB0aGUgYXJndW1lbnRzLlxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMuY29udGV4dCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChpc0RpZ2l0cyh3b3JkQ29weSkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcGxhY2VJbnQgPSB3b3JkQ29weSAtIDE7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoYXJnc1twbGFjZUludF0gPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gRm9yY2UgYXJnc1twbGFjZUludF0gdG8gU3RyaW5nLCB3b24ndCBhdHdvcmRDb3B5dCB0byBwcm9jZXNzXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBhcmcgb2YgdHlwZSBmdW5jdGlvbiwgYXJyYXksIG9yIHBsYWluIG9iamVjdFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goYXJnc1twbGFjZUludF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gd29yZENvcHk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIFJlcGVhdCBiYXNpYyBzdHJpbmcgcHJvcGVydHkgcHJvY2Vzc2luZyB3aXRoIHdvcmQgYW5kIG1vZGlmaWVkIGNvbnRleHRcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRbaV1bd29yZENvcHldICE9PSBVTkRFRikge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7IGNvbnRleHRbaV1bd29yZENvcHldID0gbmV3VmFsdWU7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbaV1bd29yZENvcHldKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmICh0eXBlb2YgY29udGV4dFtpXSA9PT0gJ2Z1bmN0aW9uJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaCh3b3JkQ29weSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gUGxhaW4gcHJvcGVydHkgdG9rZW5zIGFyZSBsaXN0ZWQgYXMgc3BlY2lhbCB3b3JkIHRva2VucyB3aGVuZXZlclxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBhIHdpbGRjYXJkIGlzIGZvdW5kIHdpdGhpbiB0aGUgcHJvcGVydHkgc3RyaW5nLiBBIHdpbGRjYXJkIGluIGFcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gcHJvcGVydHkgY2F1c2VzIGFuIGFycmF5IG9mIG1hdGNoaW5nIHByb3BlcnRpZXMgdG8gYmUgcmV0dXJuZWQsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHNvIGxvb3AgdGhyb3VnaCBhbGwgcHJvcGVydGllcyBhbmQgZXZhbHVhdGUgdG9rZW4gZm9yIGV2ZXJ5XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHByb3BlcnR5IHdoZXJlIGB3aWxkQ2FyZE1hdGNoYCByZXR1cm5zIHRydWUuXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHdpbGRjYXJkUmVnRXgudGVzdCh3b3JkQ29weSkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goW10pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZm9yIChwcm9wIGluIGNvbnRleHRbaV0pe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmICh3aWxkQ2FyZE1hdGNoKHdvcmRDb3B5LCBwcm9wKSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpeyBjb250ZXh0W2ldW3Byb3BdID0gbmV3VmFsdWU7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0W2ldLnB1c2goY29udGV4dFtpXVtwcm9wXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGkrKztcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIFwiY29udGV4dFwiIG1vZGlmaWVyIChcIkBcIiBieSBkZWZhdWx0KSByZXBsYWNlcyBjdXJyZW50IGNvbnRleHQgd2l0aCBhIHZhbHVlIGZyb21cbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIHRoZSBhcmd1bWVudHMuXG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5tb2RzLmNvbnRleHQpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChpc0RpZ2l0cyh3b3JkQ29weSkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBwbGFjZUludCA9IHdvcmRDb3B5IC0gMTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGFyZ3NbcGxhY2VJbnRdID09PSBVTkRFRil7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gRm9yY2UgYXJnc1twbGFjZUludF0gdG8gU3RyaW5nLCB3b24ndCBhdHdvcmRDb3B5dCB0byBwcm9jZXNzXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGFyZyBvZiB0eXBlIGZ1bmN0aW9uLCBhcnJheSwgb3IgcGxhaW4gb2JqZWN0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IGFyZ3NbcGxhY2VJbnRdO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IHdvcmRDb3B5O1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIFJlcGVhdCBiYXNpYyBzdHJpbmcgcHJvcGVydHkgcHJvY2Vzc2luZyB3aXRoIHdvcmQgYW5kIG1vZGlmaWVkIGNvbnRleHRcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dFt3b3JkQ29weV0gIT09IFVOREVGKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpeyBjb250ZXh0W3dvcmRDb3B5XSA9IG5ld1ZhbHVlOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHRbd29yZENvcHldO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmICh0eXBlb2YgY29udGV4dCA9PT0gJ2Z1bmN0aW9uJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSB3b3JkQ29weTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gUGxhaW4gcHJvcGVydHkgdG9rZW5zIGFyZSBsaXN0ZWQgYXMgc3BlY2lhbCB3b3JkIHRva2VucyB3aGVuZXZlclxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGEgd2lsZGNhcmQgaXMgZm91bmQgd2l0aGluIHRoZSBwcm9wZXJ0eSBzdHJpbmcuIEEgd2lsZGNhcmQgaW4gYVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHByb3BlcnR5IGNhdXNlcyBhbiBhcnJheSBvZiBtYXRjaGluZyBwcm9wZXJ0aWVzIHRvIGJlIHJldHVybmVkLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHNvIGxvb3AgdGhyb3VnaCBhbGwgcHJvcGVydGllcyBhbmQgZXZhbHVhdGUgdG9rZW4gZm9yIGV2ZXJ5XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gcHJvcGVydHkgd2hlcmUgYHdpbGRDYXJkTWF0Y2hgIHJldHVybnMgdHJ1ZS5cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmICh3aWxkY2FyZFJlZ0V4LnRlc3Qod29yZENvcHkpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gW107XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGZvciAocHJvcCBpbiBjb250ZXh0KXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmICh3aWxkQ2FyZE1hdGNoKHdvcmRDb3B5LCBwcm9wKSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7IGNvbnRleHRbcHJvcF0gPSBuZXdWYWx1ZTsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbcHJvcF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gRXZhbCBQcm9wZXJ0eSB0b2tlbnMgb3BlcmF0ZSBvbiBhIHRlbXBvcmFyeSBjb250ZXh0IGNyZWF0ZWQgYnlcbiAgICAgICAgICAgICAgICAvLyByZWN1cnNpdmVseSBjYWxsaW5nIGByZXNvbHZlUGF0aGAgd2l0aCBhIGNvcHkgb2YgdGhlIHZhbHVlU3RhY2suXG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoY3Vyci5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuZG9FYWNoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmICghQXJyYXkuaXNBcnJheShjb250ZXh0KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IFtdO1xuICAgICAgICAgICAgICAgICAgICAgICAgaSA9IDA7XG4gICAgICAgICAgICAgICAgICAgICAgICBlYWNoTGVuZ3RoID0gY29udGV4dC5sZW5ndGg7XG4gICAgICAgICAgICAgICAgICAgICAgICB3aGlsZShpIDwgZWFjaExlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuc2ltcGxlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W2ldW190aGlzLmdldChjb250ZXh0W2ldLCB7dDpjdXJyLnQsIHNpbXBsZTp0cnVlfSldID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXVtfdGhpcy5nZXQoY29udGV4dFtpXSwge3Q6Y3Vyci50LCBzaW1wbGU6dHJ1ZX0pXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbaV1bcmVzb2x2ZVBhdGgoY29udGV4dFtpXSwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbaV1bcmVzb2x2ZVBhdGgoY29udGV4dFtpXSwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGkrKztcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnNpbXBsZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbX3RoaXMuZ2V0KGNvbnRleHQsIHt0OiBjdXJyLnQsIHNpbXBsZTp0cnVlfSldID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHRbX3RoaXMuZ2V0KGNvbnRleHQsIHt0OmN1cnIudCwgc2ltcGxlOnRydWV9KV07XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtyZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayldID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHRbcmVzb2x2ZVBhdGgoY29udGV4dCwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBGdW5jdGlvbnMgYXJlIGNhbGxlZCB1c2luZyBgY2FsbGAgb3IgYGFwcGx5YCwgZGVwZW5kaW5nIG9uIHRoZSBzdGF0ZSBvZlxuICAgICAgICAgICAgICAgIC8vIHRoZSBhcmd1bWVudHMgd2l0aGluIHRoZSAoICkgY29udGFpbmVyLiBGdW5jdGlvbnMgYXJlIGV4ZWN1dGVkIHdpdGggXCJ0aGlzXCJcbiAgICAgICAgICAgICAgICAvLyBzZXQgdG8gdGhlIGNvbnRleHQgaW1tZWRpYXRlbHkgcHJpb3IgdG8gdGhlIGZ1bmN0aW9uIGluIHRoZSBzdGFjay5cbiAgICAgICAgICAgICAgICAvLyBGb3IgZXhhbXBsZSwgXCJhLmIuYy5mbigpXCIgaXMgZXF1aXZhbGVudCB0byBvYmouYS5iLmMuZm4uY2FsbChvYmouYS5iLmMpXG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoY3Vyci5leGVjID09PSAkQ0FMTCl7XG4gICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLmRvRWFjaCl7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoIUFycmF5LmlzQXJyYXkodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl0pKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gW107XG4gICAgICAgICAgICAgICAgICAgICAgICBpID0gMDtcbiAgICAgICAgICAgICAgICAgICAgICAgIGVhY2hMZW5ndGggPSBjb250ZXh0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdoaWxlKGkgPCBlYWNoTGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBJZiBmdW5jdGlvbiBjYWxsIGhhcyBhcmd1bWVudHMsIHByb2Nlc3MgdGhvc2UgYXJndW1lbnRzIGFzIGEgbmV3IHBhdGhcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci50ICYmIGN1cnIudC5sZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjYWxsQXJncyA9IHJlc29sdmVQYXRoKGNvbnRleHQsIGN1cnIsIFVOREVGLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNhbGxBcmdzID09PSBVTkRFRil7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldLmFwcGx5KHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdW2ldKSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoQXJyYXkuaXNBcnJheShjYWxsQXJncykpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXS5hcHBseSh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXVtpXSwgY2FsbEFyZ3MpKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbaV0uY2FsbCh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXVtpXSwgY2FsbEFyZ3MpKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXS5jYWxsKHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdW2ldKSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGkrKztcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIElmIGZ1bmN0aW9uIGNhbGwgaGFzIGFyZ3VtZW50cywgcHJvY2VzcyB0aG9zZSBhcmd1bWVudHMgYXMgYSBuZXcgcGF0aFxuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIudCAmJiBjdXJyLnQubGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5zaW1wbGUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjYWxsQXJncyA9IF90aGlzLmdldChjb250ZXh0LCBjdXJyKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNhbGxBcmdzID0gcmVzb2x2ZVBhdGgoY29udGV4dCwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY2FsbEFyZ3MgPT09IFVOREVGKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dC5hcHBseSh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkoY2FsbEFyZ3MpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dC5hcHBseSh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXSwgY2FsbEFyZ3MpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dC5jYWxsKHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdLCBjYWxsQXJncyk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dC5jYWxsKHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIEFkZCB0aGUgcmV0dXJuIHZhbHVlIHRvIHRoZSBzdGFjayBpbiBjYXNlIHdlIG11c3QgbG9vcCBhZ2Fpbi5cbiAgICAgICAgICAgIC8vIFJlY3Vyc2l2ZSBjYWxscyBwYXNzIHRoZSBzYW1lIHZhbHVlU3RhY2sgYXJyYXkgYXJvdW5kLCBidXQgd2UgZG9uJ3Qgd2FudCB0b1xuICAgICAgICAgICAgLy8gcHVzaCBlbnRyaWVzIG9uIHRoZSBzdGFjayBpbnNpZGUgYSByZWN1cnNpb24sIHNvIGluc3RlYWQgdXNlIGZpeGVkIGFycmF5XG4gICAgICAgICAgICAvLyBpbmRleCByZWZlcmVuY2VzIGJhc2VkIG9uIHdoYXQgKip0aGlzKiogZXhlY3V0aW9uIGtub3dzIHRoZSB2YWx1ZVN0YWNrTGVuZ3RoXG4gICAgICAgICAgICAvLyBzaG91bGQgYmUuIFRoYXQgd2F5LCBpZiBhIHJlY3Vyc2lvbiBhZGRzIG5ldyBlbGVtZW50cywgYW5kIHRoZW4gd2UgYmFjayBvdXQsXG4gICAgICAgICAgICAvLyB0aGlzIGNvbnRleHQgd2lsbCByZW1lbWJlciB0aGUgb2xkIHN0YWNrIGxlbmd0aCBhbmQgd2lsbCBtZXJlbHkgb3ZlcndyaXRlXG4gICAgICAgICAgICAvLyB0aG9zZSBhZGRlZCBlbnRyaWVzLCBpZ25vcmluZyB0aGF0IHRoZXkgd2VyZSB0aGVyZSBpbiB0aGUgZmlyc3QgcGxhY2UuXG4gICAgICAgICAgICB2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGgrK10gPSByZXQ7XG4gICAgICAgICAgICBjb250ZXh0ID0gcmV0O1xuICAgICAgICAgICAgcHJldiA9IHJldDtcbiAgICAgICAgICAgIGlkeCsrO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBjb250ZXh0O1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTaW1wbGlmaWVkIHBhdGggZXZhbHVhdGlvbiBoZWF2aWx5IG9wdGltaXplZCBmb3IgcGVyZm9ybWFuY2Ugd2hlblxuICAgICAqIHByb2Nlc3NpbmcgcGF0aHMgd2l0aCBvbmx5IHByb3BlcnR5IG5hbWVzIG9yIGluZGljZXMgYW5kIHNlcGFyYXRvcnMuXG4gICAgICogSWYgdGhlIHBhdGggY2FuIGJlIGNvcnJlY3RseSBwcm9jZXNzZWQgd2l0aCBcInBhdGguc3BsaXQoc2VwYXJhdG9yKVwiLFxuICAgICAqIHRoaXMgZnVuY3Rpb24gd2lsbCBkbyBzby4gQW55IG90aGVyIHNwZWNpYWwgY2hhcmFjdGVycyBmb3VuZCBpbiB0aGVcbiAgICAgKiBwYXRoIHdpbGwgY2F1c2UgdGhlIHBhdGggdG8gYmUgZXZhbHVhdGVkIHdpdGggdGhlIGZ1bGwgYHJlc29sdmVQYXRoYFxuICAgICAqIGZ1bmN0aW9uIGluc3RlYWQuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0gIHtPYmplY3R9IG9iaiAgICAgICAgVGhlIGRhdGEgb2JqZWN0IHRvIGJlIHJlYWQvd3JpdHRlblxuICAgICAqIEBwYXJhbSAge1N0cmluZ30gcGF0aCAgICAgICBUaGUga2V5cGF0aCB3aGljaCBgcmVzb2x2ZVBhdGhgIHdpbGwgZXZhbHVhdGUgYWdhaW5zdCBgb2JqYC5cbiAgICAgKiBAcGFyYW0gIHtBbnl9IG5ld1ZhbHVlICAgVGhlIG5ldyB2YWx1ZSB0byBzZXQgYXQgdGhlIHBvaW50IGRlc2NyaWJlZCBieSBgcGF0aGAuIFVuZGVmaW5lZCBpZiB1c2VkIGluIGBnZXRgIHNjZW5hcmlvLlxuICAgICAqIEByZXR1cm4ge0FueX0gICAgICAgICAgICBJbiBgZ2V0YCwgcmV0dXJucyB0aGUgdmFsdWUgZm91bmQgaW4gYG9iamAgYXQgYHBhdGhgLiBJbiBgc2V0YCwgcmV0dXJucyB0aGUgbmV3IHZhbHVlIHRoYXQgd2FzIHNldCBpbiBgb2JqYC4gSWYgYGdldGAgb3IgYHNldGAgYXJlIG50byBzdWNjZXNzZnVsLCByZXR1cm5zIGB1bmRlZmluZWRgXG4gICAgICovXG4gICAgdmFyIHF1aWNrUmVzb2x2ZVN0cmluZyA9IGZ1bmN0aW9uKG9iaiwgcGF0aCwgbmV3VmFsdWUpe1xuICAgICAgICB2YXIgY2hhbmdlID0gbmV3VmFsdWUgIT09IFVOREVGLFxuICAgICAgICAgICAgdGsgPSBbXSxcbiAgICAgICAgICAgIGkgPSAwLFxuICAgICAgICAgICAgdGtMZW5ndGggPSAwO1xuXG4gICAgICAgIHRrID0gcGF0aC5zcGxpdChwcm9wZXJ0eVNlcGFyYXRvcik7XG4gICAgICAgIG9wdC51c2VDYWNoZSAmJiAoY2FjaGVbcGF0aF0gPSB7dDogdGssIHNpbXBsZTogdHJ1ZX0pO1xuICAgICAgICB0a0xlbmd0aCA9IHRrLmxlbmd0aDtcbiAgICAgICAgd2hpbGUgKG9iaiAhPT0gVU5ERUYgJiYgaSA8IHRrTGVuZ3RoKXtcbiAgICAgICAgICAgIGlmICh0a1tpXSA9PT0gJycpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICBlbHNlIGlmIChjaGFuZ2Upe1xuICAgICAgICAgICAgICAgIGlmIChpID09PSB0a0xlbmd0aCAtIDEpe1xuICAgICAgICAgICAgICAgICAgICBvYmpbdGtbaV1dID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIEZvciBhcnJheXMsIHRlc3QgY3VycmVudCBjb250ZXh0IGFnYWluc3QgdW5kZWZpbmVkIHRvIGF2b2lkIHBhcnNpbmcgdGhpcyBzZWdtZW50IGFzIGEgbnVtYmVyLlxuICAgICAgICAgICAgICAgIC8vIEZvciBhbnl0aGluZyBlbHNlLCB1c2UgaGFzT3duUHJvcGVydHkuXG4gICAgICAgICAgICAgICAgZWxzZSBpZiAob3B0LmZvcmNlICYmIHR5cGVvZiBvYmpbdGtbaV1dID09PSAndW5kZWZpbmVkJykge1xuICAgICAgICAgICAgICAgICAgICBvYmpbdGtbaV1dID0ge307XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgb2JqID0gb2JqW3RrW2krK11dO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBvYmo7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNpbXBsaWZpZWQgcGF0aCBldmFsdWF0aW9uIGhlYXZpbHkgb3B0aW1pemVkIGZvciBwZXJmb3JtYW5jZSB3aGVuXG4gICAgICogcHJvY2Vzc2luZyBhcnJheSBvZiBzaW1wbGUgcGF0aCB0b2tlbnMgKHBsYWluIHByb3BlcnR5IG5hbWVzKS5cbiAgICAgKiBUaGlzIGZ1bmN0aW9uIGlzIGVzc2VudGlhbGx5IHRoZSBzYW1lIGFzIGBxdWlja1Jlc29sdmVTdHJpbmdgIGV4Y2VwdFxuICAgICAqIGBxdWlja1Jlc29sdmVUb2tlbkFycmF5YCBkb2VzIG50byBuZWVkIHRvIGV4ZWN1dGUgcGF0aC5zcGxpdC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSAge09iamVjdH0gb2JqICAgICAgICBUaGUgZGF0YSBvYmplY3QgdG8gYmUgcmVhZC93cml0dGVuXG4gICAgICogQHBhcmFtICB7QXJyYXl9IHRrICAgICAgIFRoZSB0b2tlbiBhcnJheSB3aGljaCBgcmVzb2x2ZVBhdGhgIHdpbGwgZXZhbHVhdGUgYWdhaW5zdCBgb2JqYC5cbiAgICAgKiBAcGFyYW0gIHtBbnl9IG5ld1ZhbHVlICAgVGhlIG5ldyB2YWx1ZSB0byBzZXQgYXQgdGhlIHBvaW50IGRlc2NyaWJlZCBieSBgcGF0aGAuIFVuZGVmaW5lZCBpZiB1c2VkIGluIGBnZXRgIHNjZW5hcmlvLlxuICAgICAqIEByZXR1cm4ge0FueX0gICAgICAgICAgICBJbiBgZ2V0YCwgcmV0dXJucyB0aGUgdmFsdWUgZm91bmQgaW4gYG9iamAgYXQgYHBhdGhgLiBJbiBgc2V0YCwgcmV0dXJucyB0aGUgbmV3IHZhbHVlIHRoYXQgd2FzIHNldCBpbiBgb2JqYC4gSWYgYGdldGAgb3IgYHNldGAgYXJlIG50byBzdWNjZXNzZnVsLCByZXR1cm5zIGB1bmRlZmluZWRgXG4gICAgICovXG4gICAgdmFyIHF1aWNrUmVzb2x2ZVRva2VuQXJyYXkgPSBmdW5jdGlvbihvYmosIHRrLCBuZXdWYWx1ZSl7XG4gICAgICAgIHZhciBjaGFuZ2UgPSBuZXdWYWx1ZSAhPT0gVU5ERUYsXG4gICAgICAgICAgICBpID0gMCxcbiAgICAgICAgICAgIHRrTGVuZ3RoID0gdGsubGVuZ3RoO1xuXG4gICAgICAgIHdoaWxlIChvYmogIT0gbnVsbCAmJiBpIDwgdGtMZW5ndGgpe1xuICAgICAgICAgICAgaWYgKHRrW2ldID09PSAnJyl7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgIGVsc2UgaWYgKGNoYW5nZSl7XG4gICAgICAgICAgICAgICAgaWYgKGkgPT09IHRrTGVuZ3RoIC0gMSl7XG4gICAgICAgICAgICAgICAgICAgIG9ialt0a1tpXV0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gRm9yIGFycmF5cywgdGVzdCBjdXJyZW50IGNvbnRleHQgYWdhaW5zdCB1bmRlZmluZWQgdG8gYXZvaWQgcGFyc2luZyB0aGlzIHNlZ21lbnQgYXMgYSBudW1iZXIuXG4gICAgICAgICAgICAgICAgLy8gRm9yIGFueXRoaW5nIGVsc2UsIHVzZSBoYXNPd25Qcm9wZXJ0eS5cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChvcHQuZm9yY2UgJiYgdHlwZW9mIG9ialt0a1tpXV0gPT09ICd1bmRlZmluZWQnKSB7XG4gICAgICAgICAgICAgICAgICAgIG9ialt0a1tpXV0gPSB7fTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBvYmogPSBvYmpbdGtbaSsrXV07XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG9iajtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2VhcmNoZXMgYW4gb2JqZWN0IG9yIGFycmF5IGZvciBhIHZhbHVlLCBhY2N1bXVsYXRpbmcgdGhlIGtleXBhdGggdG8gdGhlIHZhbHVlIGFsb25nXG4gICAgICogdGhlIHdheS4gT3BlcmF0ZXMgaW4gYSByZWN1cnNpdmUgd2F5IHVudGlsIGVpdGhlciBhbGwga2V5cy9pbmRpY2VzIGhhdmUgYmVlblxuICAgICAqIGV4aGF1c3RlZCBvciBhIG1hdGNoIGlzIGZvdW5kLiBSZXR1cm4gdmFsdWUgXCJ0cnVlXCIgbWVhbnMgXCJrZWVwIHNjYW5uaW5nXCIsIFwiZmFsc2VcIlxuICAgICAqIG1lYW5zIFwic3RvcCBub3dcIi4gSWYgYSBtYXRjaCBpcyBmb3VuZCwgaW5zdGVhZCBvZiByZXR1cm5pbmcgYSBzaW1wbGUgXCJmYWxzZVwiLCBhXG4gICAgICogY2FsbGJhY2sgZnVuY3Rpb24gKHNhdmVQYXRoKSBpcyBjYWxsZWQgd2hpY2ggd2lsbCBkZWNpZGUgd2hldGhlciBvciBub3QgdG8gY29udGludWVcbiAgICAgKiB0aGUgc2Nhbi4gVGhpcyBhbGxvd3MgdGhlIGZ1bmN0aW9uIHRvIGZpbmQgb25lIGluc3RhbmNlIG9mIHZhbHVlIG9yIGFsbCBpbnN0YW5jZXMsXG4gICAgICogYmFzZWQgb24gbG9naWMgaW4gdGhlIGNhbGxiYWNrLlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtIHtPYmplY3R9IG9iaiAgICBUaGUgZGF0YSBvYmplY3QgdG8gc2NhblxuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVGhlIHZhbHVlIHdlIGFyZSBsb29raW5nIGZvciB3aXRoaW4gYG9iamBcbiAgICAgKiBAcGFyYW0ge0Z1bmN0aW9ufSBzYXZlUGF0aCBDYWxsYmFjayBmdW5jdGlvbiB3aGljaCB3aWxsIHN0b3JlIGFjY3VtdWxhdGVkIHBhdGhzIGFuZCBpbmRpY2F0ZSB3aGV0aGVyIHRvIGNvbnRpbnVlXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHBhdGggQWNjdW11bGF0ZWQga2V5cGF0aDsgdW5kZWZpbmVkIGF0IGZpcnN0LCBwb3B1bGF0ZWQgaW4gcmVjdXJzaXZlIGNhbGxzXG4gICAgICogQHJldHVybiB7Qm9vbGVhbn0gSW5kaWNhdGVzIHdoZXRoZXIgc2NhbiBwcm9jZXNzIHNob3VsZCBjb250aW51ZSAoXCJ0cnVlXCItPnllcywgXCJmYWxzZVwiLT5ubylcbiAgICAgKi9cbiAgICB2YXIgc2NhbkZvclZhbHVlID0gZnVuY3Rpb24ob2JqLCB2YWwsIHNhdmVQYXRoLCBwYXRoKXtcbiAgICAgICAgdmFyIGksIGxlbiwgbW9yZSwga2V5cywgcHJvcDtcblxuICAgICAgICBwYXRoID0gcGF0aCA/IHBhdGggOiAnJztcblxuICAgICAgICAvLyBJZiB3ZSBmb3VuZCB0aGUgdmFsdWUgd2UncmUgbG9va2luZyBmb3JcbiAgICAgICAgaWYgKG9iaiA9PT0gdmFsKXtcbiAgICAgICAgICAgIHJldHVybiBzYXZlUGF0aChwYXRoKTsgLy8gU2F2ZSB0aGUgYWNjdW11bGF0ZWQgcGF0aCwgYXNrIHdoZXRoZXIgdG8gY29udGludWVcbiAgICAgICAgfVxuICAgICAgICAvLyBUaGlzIG9iamVjdCBpcyBhbiBhcnJheSwgc28gZXhhbWluZSBlYWNoIGluZGV4IHNlcGFyYXRlbHlcbiAgICAgICAgZWxzZSBpZiAoQXJyYXkuaXNBcnJheShvYmopKXtcbiAgICAgICAgICAgIGxlbiA9IG9iai5sZW5ndGg7XG4gICAgICAgICAgICBmb3IoaSA9IDA7IGkgPCBsZW47IGkrKyl7XG4gICAgICAgICAgICAgICAgLy8gQ2FsbCBgc2NhbkZvclZhbHVlYCByZWN1cnNpdmVseVxuICAgICAgICAgICAgICAgIG1vcmUgPSBzY2FuRm9yVmFsdWUob2JqW2ldLCB2YWwsIHNhdmVQYXRoLCBwYXRoICsgcHJvcGVydHlTZXBhcmF0b3IgKyBpKTtcbiAgICAgICAgICAgICAgICAvLyBIYWx0IGlmIHRoYXQgcmVjdXJzaXZlIGNhbGwgcmV0dXJuZWQgXCJmYWxzZVwiXG4gICAgICAgICAgICAgICAgaWYgKCFtb3JlKXsgcmV0dXJuOyB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTsgLy8ga2VlcCBsb29raW5nXG4gICAgICAgIH1cbiAgICAgICAgLy8gVGhpcyBvYmplY3QgaXMgYW4gb2JqZWN0LCBzbyBleGFtaW5lIGVhY2ggbG9jYWwgcHJvcGVydHkgc2VwYXJhdGVseVxuICAgICAgICBlbHNlIGlmIChpc09iamVjdChvYmopKSB7XG4gICAgICAgICAgICBrZXlzID0gT2JqZWN0LmtleXMob2JqKTtcbiAgICAgICAgICAgIGxlbiA9IGtleXMubGVuZ3RoO1xuICAgICAgICAgICAgaWYgKGxlbiA+IDEpeyBrZXlzID0ga2V5cy5zb3J0KCk7IH0gLy8gRm9yY2Ugb3JkZXIgb2Ygb2JqZWN0IGtleXMgdG8gcHJvZHVjZSByZXBlYXRhYmxlIHJlc3VsdHNcbiAgICAgICAgICAgIGZvciAoaSA9IDA7IGkgPCBsZW47IGkrKyl7XG4gICAgICAgICAgICAgICAgaWYgKG9iai5oYXNPd25Qcm9wZXJ0eShrZXlzW2ldKSl7XG4gICAgICAgICAgICAgICAgICAgIHByb3AgPSBrZXlzW2ldO1xuICAgICAgICAgICAgICAgICAgICAvLyBQcm9wZXJ0eSBtYXkgaW5jbHVkZSB0aGUgc2VwYXJhdG9yIGNoYXJhY3RlciBvciBzb21lIG90aGVyIHNwZWNpYWwgY2hhcmFjdGVyLFxuICAgICAgICAgICAgICAgICAgICAvLyBzbyBxdW90ZSB0aGlzIHBhdGggc2VnbWVudCBhbmQgZXNjYXBlIGFueSBzZXBhcmF0b3JzIHdpdGhpbi5cbiAgICAgICAgICAgICAgICAgICAgaWYgKGFsbFNwZWNpYWxzUmVnRXgudGVzdChwcm9wKSl7XG4gICAgICAgICAgICAgICAgICAgICAgICBwcm9wID0gcXVvdGVTdHJpbmcoc2luZ2xlcXVvdGUsIHByb3ApO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIG1vcmUgPSBzY2FuRm9yVmFsdWUob2JqW2tleXNbaV1dLCB2YWwsIHNhdmVQYXRoLCBwYXRoICsgcHJvcGVydHlTZXBhcmF0b3IgKyBwcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgaWYgKCFtb3JlKXsgcmV0dXJuOyB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7IC8vIGtlZXAgbG9va2luZ1xuICAgICAgICB9XG4gICAgICAgIC8vIExlYWYgbm9kZSAoc3RyaW5nLCBudW1iZXIsIGNoYXJhY3RlciwgYm9vbGVhbiwgZXRjLiksIGJ1dCBkaWRuJ3QgbWF0Y2hcbiAgICAgICAgcmV0dXJuIHRydWU7IC8vIGtlZXAgbG9va2luZ1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBHZXQgdG9rZW5pemVkIHJlcHJlc2VudGF0aW9uIG9mIHN0cmluZyBrZXlwYXRoLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBLZXlwYXRoXG4gICAgICogQHJldHVybiB7T2JqZWN0fSBPYmplY3QgaW5jbHVkaW5nIHRoZSBhcnJheSBvZiBwYXRoIHRva2VucyBhbmQgYSBib29sZWFuIGluZGljYXRpbmcgXCJzaW1wbGVcIi4gU2ltcGxlIHRva2VuIHNldHMgaGF2ZSBubyBzcGVjaWFsIG9wZXJhdG9ycyBvciBuZXN0ZWQgdG9rZW5zLCBvbmx5IGEgcGxhaW4gYXJyYXkgb2Ygc3RyaW5ncyBmb3IgZmFzdCBldmFsdWF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLmdldFRva2VucyA9IGZ1bmN0aW9uKHBhdGgpe1xuICAgICAgICB2YXIgdG9rZW5zID0gdG9rZW5pemUocGF0aCk7XG4gICAgICAgIGlmICh0eXBlb2YgdG9rZW5zID09PSAkVU5ERUZJTkVEKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICByZXR1cm4gdG9rZW5zO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBJbmZvcm1zIHdoZXRoZXIgdGhlIHN0cmluZyBwYXRoIGhhcyB2YWxpZCBzeW50YXguIFRoZSBwYXRoIGlzIE5PVCBldmFsdWF0ZWQgYWdhaW5zdCBhXG4gICAgICogZGF0YSBvYmplY3QsIG9ubHkgdGhlIHN5bnRheCBpcyBjaGVja2VkLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBLZXlwYXRoXG4gICAgICogQHJldHVybiB7Qm9vbGVhbn0gdmFsaWQgc3ludGF4IC0+IFwidHJ1ZVwiOyBub3QgdmFsaWQgLT4gXCJmYWxzZVwiXG4gICAgICovXG4gICAgX3RoaXMuaXNWYWxpZCA9IGZ1bmN0aW9uKHBhdGgpe1xuICAgICAgICByZXR1cm4gdHlwZW9mIHRva2VuaXplKHBhdGgpICE9PSAkVU5ERUZJTkVEO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBFc2NhcGVzIGFueSBzcGVjaWFsIGNoYXJhY3RlcnMgZm91bmQgaW4gdGhlIGlucHV0IHN0cmluZyB1c2luZyBiYWNrc2xhc2gsIHByZXZlbnRpbmdcbiAgICAgKiB0aGVzZSBjaGFyYWN0ZXJzIGZyb20gY2F1c2luZyB1bmludGVuZGVkIHByb2Nlc3NpbmcgYnkgUGF0aFRvb2xraXQuIFRoaXMgZnVuY3Rpb25cbiAgICAgKiBET0VTIHJlc3BlY3QgdGhlIGN1cnJlbnQgY29uZmlndXJlZCBzeW50YXgsIGV2ZW4gaWYgaXQgaGFzIGJlZW4gYWx0ZXJlZCBmcm9tIHRoZSBkZWZhdWx0LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc2VnbWVudCBTZWdtZW50IG9mIGEga2V5cGF0aFxuICAgICAqIEByZXR1cm4ge1N0cmluZ30gVGhlIG9yaWdpbmFsIHNlZ21lbnQgc3RyaW5nIHdpdGggYWxsIFBhdGhUb29sa2l0IHNwZWNpYWwgY2hhcmFjdGVycyBwcmVwZW5kZWQgd2l0aCBcIlxcXCJcbiAgICAgKi9cbiAgICBfdGhpcy5lc2NhcGUgPSBmdW5jdGlvbihzZWdtZW50KXtcbiAgICAgICAgcmV0dXJuIHNlZ21lbnQucmVwbGFjZShhbGxTcGVjaWFsc1JlZ0V4LCAnXFxcXCQmJyk7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEV2YWx1YXRlcyBrZXlwYXRoIGluIG9iamVjdCBhbmQgcmV0dXJucyB0aGUgdmFsdWUgZm91bmQgdGhlcmUsIGlmIGF2YWlsYWJsZS4gSWYgdGhlIHBhdGhcbiAgICAgKiBkb2VzIG5vdCBleGlzdCBpbiB0aGUgcHJvdmlkZWQgZGF0YSBvYmplY3QsIHJldHVybnMgYHVuZGVmaW5lZGAuIEZvciBcInNpbXBsZVwiIHBhdGhzLCB3aGljaFxuICAgICAqIGRvbid0IGluY2x1ZGUgYW55IG9wZXJhdGlvbnMgYmV5b25kIHByb3BlcnR5IHNlcGFyYXRvcnMsIG9wdGltaXplZCByZXNvbHZlcnMgd2lsbCBiZSB1c2VkXG4gICAgICogd2hpY2ggYXJlIG1vcmUgbGlnaHR3ZWlnaHQgdGhhbiB0aGUgZnVsbC1mZWF0dXJlZCBgcmVzb2x2ZVBhdGhgLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gb2JqIFNvdXJjZSBkYXRhIG9iamVjdFxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBwYXRoIEtleXBhdGggdG8gZXZhbHVhdGUgd2l0aGluIFwib2JqXCIuIEFsc28gYWNjZXB0cyB0b2tlbiBhcnJheSBpbiBwbGFjZSBvZiBhIHN0cmluZyBwYXRoLlxuICAgICAqIEByZXR1cm4ge0FueX0gSWYgdGhlIGtleXBhdGggZXhpc3RzIGluIFwib2JqXCIsIHJldHVybiB0aGUgdmFsdWUgYXQgdGhhdCBsb2NhdGlvbjsgSWYgbm90LCByZXR1cm4gYHVuZGVmaW5lZGAuXG4gICAgICovXG4gICAgX3RoaXMuZ2V0ID0gZnVuY3Rpb24gKG9iaiwgcGF0aCl7XG4gICAgICAgIHZhciBpID0gMCxcbiAgICAgICAgICAgIGxlbiA9IGFyZ3VtZW50cy5sZW5ndGgsXG4gICAgICAgICAgICBhcmdzO1xuICAgICAgICAvLyBGb3Igc3RyaW5nIHBhdGhzLCBmaXJzdCBzZWUgaWYgcGF0aCBoYXMgYWxyZWFkeSBiZWVuIGNhY2hlZCBhbmQgaWYgdGhlIHRva2VuIHNldCBpcyBzaW1wbGUuIElmXG4gICAgICAgIC8vIHNvLCB3ZSBjYW4gdXNlIHRoZSBvcHRpbWl6ZWQgdG9rZW4gYXJyYXkgcmVzb2x2ZXIgdXNpbmcgdGhlIGNhY2hlZCB0b2tlbiBzZXQuXG4gICAgICAgIC8vIElmIHRoZXJlIGlzIG5vIGNhY2hlZCBlbnRyeSwgdXNlIFJlZ0V4IHRvIGxvb2sgZm9yIHNwZWNpYWwgY2hhcmFjdGVycyBhcGFydCBmcm9tIHRoZSBzZXBhcmF0b3IuXG4gICAgICAgIC8vIElmIG5vbmUgYXJlIGZvdW5kLCB3ZSBjYW4gdXNlIHRoZSBvcHRpbWl6ZWQgc3RyaW5nIHJlc29sdmVyLlxuICAgICAgICBpZiAodHlwZW9mIHBhdGggPT09ICRTVFJJTkcpe1xuICAgICAgICAgICAgaWYgKG9wdC51c2VDYWNoZSAmJiBjYWNoZVtwYXRoXSAmJiBjYWNoZVtwYXRoXS5zaW1wbGUpe1xuICAgICAgICAgICAgICAgIHJldHVybiBxdWlja1Jlc29sdmVUb2tlbkFycmF5KG9iaiwgY2FjaGVbcGF0aF0udCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmICghc2ltcGxlUGF0aFJlZ0V4LnRlc3QocGF0aCkpe1xuICAgICAgICAgICAgICAgIHJldHVybiBxdWlja1Jlc29sdmVTdHJpbmcob2JqLCBwYXRoKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICAvLyBGb3IgYXJyYXkgcGF0aHMgKHByZS1jb21waWxlZCB0b2tlbiBzZXRzKSwgY2hlY2sgZm9yIHNpbXBsaWNpdHkgc28gd2UgY2FuIHVzZSB0aGUgb3B0aW1pemVkIHJlc29sdmVyLlxuICAgICAgICBlbHNlIGlmIChBcnJheS5pc0FycmF5KHBhdGgudCkgJiYgcGF0aC5zaW1wbGUpe1xuICAgICAgICAgICAgcmV0dXJuIHF1aWNrUmVzb2x2ZVRva2VuQXJyYXkob2JqLCBwYXRoLnQpO1xuICAgICAgICB9XG4gICAgICAgIFxuICAgICAgICAvLyBJZiB3ZSBtYWRlIGl0IHRoaXMgZmFyLCB0aGUgcGF0aCBpcyBjb21wbGV4IGFuZCBtYXkgaW5jbHVkZSBwbGFjZWhvbGRlcnMuIEdhdGhlciB1cCBhbnlcbiAgICAgICAgLy8gZXh0cmEgYXJndW1lbnRzIGFuZCBjYWxsIHRoZSBmdWxsIGByZXNvbHZlUGF0aGAgZnVuY3Rpb24uXG4gICAgICAgIGFyZ3MgPSBbXTtcbiAgICAgICAgaWYgKGxlbiA+IDIpe1xuICAgICAgICAgICAgZm9yIChpID0gMjsgaSA8IGxlbjsgaSsrKSB7IGFyZ3NbaS0yXSA9IGFyZ3VtZW50c1tpXTsgfVxuICAgICAgICB9XG4gICAgICAgIHJldHVybiByZXNvbHZlUGF0aChvYmosIHBhdGgsIHVuZGVmaW5lZCwgYXJncyk7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEV2YWx1YXRlcyBhIGtleXBhdGggaW4gb2JqZWN0IGFuZCBzZXRzIGEgbmV3IHZhbHVlIGF0IHRoZSBwb2ludCBkZXNjcmliZWQgaW4gdGhlIGtleXBhdGguIElmXG4gICAgICogXCJmb3JjZVwiIGlzIGRpc2FibGVkLCB0aGUgZnVsbCBwYXRoIG11c3QgZXhpc3QgdXAgdG8gdGhlIGZpbmFsIHByb3BlcnR5LCB3aGljaCBtYXkgYmUgY3JlYXRlZFxuICAgICAqIGJ5IHRoZSBzZXQgb3BlcmF0aW9uLiBJZiBcImZvcmNlXCIgaXMgZW5hYmxlZCwgYW55IG1pc3NpbmcgaW50ZXJtZWRpYXRlIHByb3BlcnRpZXMgd2lsbCBiZSBjcmVhdGVkXG4gICAgICogaW4gb3JkZXIgdG8gc2V0IHRoZSB2YWx1ZSBvbiB0aGUgZmluYWwgcHJvcGVydHkuIElmIGBzZXRgIHN1Y2NlZWRzLCByZXR1cm5zIFwidHJ1ZVwiLCBvdGhlcndpc2UgXCJmYWxzZVwiLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gb2JqIFNvdXJjZSBkYXRhIG9iamVjdFxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBwYXRoIEtleXBhdGggdG8gZXZhbHVhdGUgd2l0aGluIFwib2JqXCIuIEFsc28gYWNjZXB0cyB0b2tlbiBhcnJheSBpbiBwbGFjZSBvZiBhIHN0cmluZyBwYXRoLlxuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgTmV3IHZhbHVlIHRvIHNldCBhdCB0aGUgbG9jYXRpb24gZGVzY3JpYmVkIGluIFwicGF0aFwiXG4gICAgICogQHJldHVybiB7Qm9vbGVhbn0gXCJ0cnVlXCIgaWYgdGhlIHNldCBvcGVyYXRpb24gc3VjY2VlZHM7IFwiZmFsc2VcIiBpZiBpdCBkb2VzIG5vdCBzdWNjZWVkXG4gICAgICovXG4gICAgX3RoaXMuc2V0ID0gZnVuY3Rpb24ob2JqLCBwYXRoLCB2YWwpe1xuICAgICAgICB2YXIgaSA9IDAsXG4gICAgICAgICAgICBsZW4gPSBhcmd1bWVudHMubGVuZ3RoLFxuICAgICAgICAgICAgYXJncyxcbiAgICAgICAgICAgIHJlZixcbiAgICAgICAgICAgIGRvbmUgPSBmYWxzZTtcbiAgICAgICAgICAgIFxuICAgICAgICAvLyBQYXRoIHJlc29sdXRpb24gZm9sbG93cyB0aGUgc2FtZSBsb2dpYyBhcyBgZ2V0YCBhYm92ZSwgd2l0aCBvbmUgZGlmZmVyZW5jZTogYGdldGAgd2lsbFxuICAgICAgICAvLyBhYm9ydCBieSByZXR1cm5pbmcgdGhlIHZhbHVlIGFzIHNvb24gYXMgaXQncyBmb3VuZC4gYHNldGAgZG9lcyBub3QgYWJvcnQgc28gdGhlIGlmLWVsc2VcbiAgICAgICAgLy8gc3RydWN0dXJlIGlzIHNsaWdodGx5IGRpZmZlcmVudCB0byBkaWN0YXRlIHdoZW4vaWYgdGhlIGZpbmFsIGNhc2Ugc2hvdWxkIGV4ZWN1dGUuXG4gICAgICAgIGlmICh0eXBlb2YgcGF0aCA9PT0gJFNUUklORyl7XG4gICAgICAgICAgICBpZiAob3B0LnVzZUNhY2hlICYmIGNhY2hlW3BhdGhdICYmIGNhY2hlW3BhdGhdLnNpbXBsZSl7XG4gICAgICAgICAgICAgICAgcmVmID0gcXVpY2tSZXNvbHZlVG9rZW5BcnJheShvYmosIGNhY2hlW3BhdGhdLnQsIHZhbCk7XG4gICAgICAgICAgICAgICAgZG9uZSB8PSB0cnVlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoIXNpbXBsZVBhdGhSZWdFeC50ZXN0KHBhdGgpKXtcbiAgICAgICAgICAgICAgICByZWYgPSBxdWlja1Jlc29sdmVTdHJpbmcob2JqLCBwYXRoLCB2YWwpO1xuICAgICAgICAgICAgICAgIGRvbmUgfD0gdHJ1ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChBcnJheS5pc0FycmF5KHBhdGgudCkgJiYgcGF0aC5zaW1wbGUpe1xuICAgICAgICAgICAgcmVmID0gcXVpY2tSZXNvbHZlVG9rZW5BcnJheShvYmosIHBhdGgudCwgdmFsKTtcbiAgICAgICAgICAgIGRvbmUgfD0gdHJ1ZTtcbiAgICAgICAgfVxuICAgICAgICBcbiAgICAgICAgLy8gUGF0aCB3YXMgKHByb2JhYmx5KSBhIHN0cmluZyBhbmQgaXQgY29udGFpbmVkIGNvbXBsZXggcGF0aCBjaGFyYWN0ZXJzXG4gICAgICAgIGlmICghZG9uZSkge1xuICAgICAgICAgICAgaWYgKGxlbiA+IDMpe1xuICAgICAgICAgICAgICAgIGFyZ3MgPSBbXTtcbiAgICAgICAgICAgICAgICBmb3IgKGkgPSAzOyBpIDwgbGVuOyBpKyspIHsgYXJnc1tpLTNdID0gYXJndW1lbnRzW2ldOyB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZWYgPSByZXNvbHZlUGF0aChvYmosIHBhdGgsIHZhbCwgYXJncyk7XG4gICAgICAgIH1cbiAgICAgICAgXG4gICAgICAgIC8vIGBzZXRgIGNhbiBzZXQgYSBuZXcgdmFsdWUgaW4gbXVsdGlwbGUgcGxhY2VzIGlmIHRoZSBmaW5hbCBwYXRoIHNlZ21lbnQgaXMgYW4gYXJyYXkuXG4gICAgICAgIC8vIElmIGFueSBvZiB0aG9zZSB2YWx1ZSBhc3NpZ25tZW50cyBmYWlsLCBgc2V0YCB3aWxsIHJldHVybiBcImZhbHNlXCIgaW5kaWNhdGluZyBmYWlsdXJlLlxuICAgICAgICBpZiAoQXJyYXkuaXNBcnJheShyZWYpKXtcbiAgICAgICAgICAgIHJldHVybiByZWYuaW5kZXhPZih1bmRlZmluZWQpID09PSAtMTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gcmVmICE9PSBVTkRFRjtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTG9jYXRlIGEgdmFsdWUgd2l0aGluIGFuIG9iamVjdCBvciBhcnJheS4gVGhpcyBpcyB0aGUgcHVibGljbHkgZXhwb3NlZCBpbnRlcmZhY2UgdG8gdGhlXG4gICAgICogcHJpdmF0ZSBgc2NhbkZvclZhbHVlYCBmdW5jdGlvbiBkZWZpbmVkIGFib3ZlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gb2JqIFNvdXJjZSBkYXRhIG9iamVjdFxuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVGhlIHZhbHVlIHRvIHNlYXJjaCBmb3Igd2l0aGluIFwib2JqXCJcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gb25lT3JNYW55IE9wdGlvbmFsOyBJZiBtaXNzaW5nIG9yIFwib25lXCIsIGBmaW5kYCB3aWxsIG9ubHkgcmV0dXJuIHRoZSBmaXJzdCB2YWxpZCBwYXRoLiBJZiBcIm9uT3JNYW55XCIgaXMgYW55IG90aGVyIHN0cmluZywgYGZpbmRgIHdpbGwgc2NhbiB0aGUgZnVsbCBvYmplY3QgbG9va2luZyBmb3IgYWxsIHZhbGlkIHBhdGhzIHRvIGFsbCBjYXNlcyB3aGVyZSBcInZhbFwiIGFwcGVhcnMuXG4gICAgICogQHJldHVybiB7QXJyYXl9IEFycmF5IG9mIGtleXBhdGhzIHRvIFwidmFsXCIgb3IgYHVuZGVmaW5lZGAgaWYgXCJ2YWxcIiBpcyBub3QgZm91bmQuXG4gICAgICovXG4gICAgX3RoaXMuZmluZCA9IGZ1bmN0aW9uKG9iaiwgdmFsLCBvbmVPck1hbnkpe1xuICAgICAgICB2YXIgcmV0VmFsID0gW107XG4gICAgICAgIC8vIHNhdmVQYXRoIGlzIHRoZSBjYWxsYmFjayB3aGljaCB3aWxsIGFjY3VtdWxhdGUgYW55IGZvdW5kIHBhdGhzIGluIGEgbG9jYWwgYXJyYXlcbiAgICAgICAgLy8gdmFyaWFibGUuXG4gICAgICAgIHZhciBzYXZlUGF0aCA9IGZ1bmN0aW9uKHBhdGgpe1xuICAgICAgICAgICAgcmV0VmFsLnB1c2gocGF0aC5zdWJzdHIoMSkpO1xuICAgICAgICAgICAgaWYoIW9uZU9yTWFueSB8fCBvbmVPck1hbnkgPT09ICdvbmUnKXtcbiAgICAgICAgICAgICAgICByZXRWYWwgPSByZXRWYWxbMF07XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH07XG4gICAgICAgIHNjYW5Gb3JWYWx1ZShvYmosIHZhbCwgc2F2ZVBhdGgpO1xuICAgICAgICByZXR1cm4gcmV0VmFsWzBdID8gcmV0VmFsIDogdW5kZWZpbmVkO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBGb3IgYSBnaXZlbiBzcGVjaWFsIGNoYXJhY3RlciBncm91cCAoZS5nLiwgc2VwYXJhdG9ycykgYW5kIGNoYXJhY3RlciB0eXBlIChlLmcuLCBcInByb3BlcnR5XCIpLFxuICAgICAqIHJlcGxhY2UgYW4gZXhpc3Rpbmcgc2VwYXJhdG9yIHdpdGggYSBuZXcgY2hhcmFjdGVyLiBUaGlzIGNyZWF0ZXMgYSBuZXcgc3BlY2lhbCBjaGFyYWN0ZXIgZm9yXG4gICAgICogdGhhdCBwdXJwb3NlIGFud2l0aGluIHRoZSBjaGFyYWN0ZXIgZ3JvdXAgYW5kIHJlbW92ZXMgdGhlIG9sZCBvbmUuIEFsc28gdGFrZXMgYSBcImNsb3NlclwiIGFyZ3VtZW50XG4gICAgICogZm9yIGNhc2VzIHdoZXJlIHRoZSBzcGVjaWFsIGNoYXJhY3RlciBpcyBhIGNvbnRhaW5lciBzZXQuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0ge09iamVjdH0gb3B0aW9uR3JvdXAgUmVmZXJlbmNlIHRvIGN1cnJlbnQgY29uZmlndXJhdGlvbiBmb3IgYSBjZXJ0YWluIHR5cGUgb2Ygc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNoYXJUeXBlIFRoZSB0eXBlIG9mIHNwZWNpYWwgY2hhcmFjdGVyIHRvIGJlIHJlcGxhY2VkXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgc3BlY2lhbCBjaGFyYWN0ZXIgc3RyaW5nXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNsb3NlciBPcHRpb25hbDsgTmV3IHNwZWNpYWwgY2hhcmFjdGVyIGNsb3NlciBzdHJpbmcsIG9ubHkgdXNlZCBmb3IgXCJjb250YWluZXJzXCIgZ3JvdXBcbiAgICAgKi9cbiAgICB2YXIgdXBkYXRlT3B0aW9uQ2hhciA9IGZ1bmN0aW9uKG9wdGlvbkdyb3VwLCBjaGFyVHlwZSwgdmFsLCBjbG9zZXIpe1xuICAgICAgICB2YXIgb2xkVmFsID0gJyc7XG4gICAgICAgIE9iamVjdC5rZXlzKG9wdGlvbkdyb3VwKS5mb3JFYWNoKGZ1bmN0aW9uKHN0cil7IGlmIChvcHRpb25Hcm91cFtzdHJdLmV4ZWMgPT09IGNoYXJUeXBlKXsgb2xkVmFsID0gc3RyOyB9IH0pO1xuXG4gICAgICAgIGRlbGV0ZSBvcHRpb25Hcm91cFtvbGRWYWxdO1xuICAgICAgICBvcHRpb25Hcm91cFt2YWxdID0ge2V4ZWM6IGNoYXJUeXBlfTtcbiAgICAgICAgaWYgKGNsb3Nlcil7IG9wdGlvbkdyb3VwW3ZhbF0uY2xvc2VyID0gY2xvc2VyOyB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNldHMgXCJzaW1wbGVcIiBzeW50YXggaW4gc3BlY2lhbCBjaGFyYWN0ZXIgZ3JvdXBzLiBUaGlzIHN5bnRheCBvbmx5IHN1cHBvcnRzIGEgc2VwYXJhdG9yXG4gICAgICogY2hhcmFjdGVyIGFuZCBubyBvdGhlciBvcGVyYXRvcnMuIEEgY3VzdG9tIHNlcGFyYXRvciBtYXkgYmUgcHJvdmlkZWQgYXMgYW4gYXJndW1lbnQuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc2VwIE9wdGlvbmFsOyBTZXBhcmF0b3Igc3RyaW5nLiBJZiBtaXNzaW5nLCB0aGUgZGVmYXVsdCBzZXBhcmF0b3IgKFwiLlwiKSBpcyB1c2VkLlxuICAgICAqL1xuICAgIHZhciBzZXRTaW1wbGVPcHRpb25zID0gZnVuY3Rpb24oc2VwKXtcbiAgICAgICAgdmFyIHNlcE9wdHMgPSB7fTtcbiAgICAgICAgaWYgKCEodHlwZW9mIHNlcCA9PT0gJFNUUklORyAmJiBzZXAubGVuZ3RoID09PSAxKSl7XG4gICAgICAgICAgICBzZXAgPSAnLic7XG4gICAgICAgIH1cbiAgICAgICAgc2VwT3B0c1tzZXBdID0ge2V4ZWM6ICRQUk9QRVJUWX07XG4gICAgICAgIG9wdC5wcmVmaXhlcyA9IHt9O1xuICAgICAgICBvcHQuY29udGFpbmVycyA9IHt9O1xuICAgICAgICBvcHQuc2VwYXJhdG9ycyA9IHNlcE9wdHM7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEFsdGVyIFBhdGhUb29sa2l0IGNvbmZpZ3VyYXRpb24uIFRha2VzIGFuIG9wdGlvbnMgaGFzaCB3aGljaCBtYXkgaW5jbHVkZVxuICAgICAqIG11bHRpcGxlIHNldHRpbmdzIHRvIGNoYW5nZSBhdCBvbmNlLiBJZiB0aGUgcGF0aCBzeW50YXggaXMgY2hhbmdlZCBieVxuICAgICAqIGNoYW5naW5nIHNwZWNpYWwgY2hhcmFjdGVycywgdGhlIGNhY2hlIGlzIHdpcGVkLiBFYWNoIG9wdGlvbiBncm91cCBpc1xuICAgICAqIFJFUExBQ0VEIGJ5IHRoZSBuZXcgb3B0aW9uIGdyb3VwIHBhc3NlZCBpbi4gSWYgYW4gb3B0aW9uIGdyb3VwIGlzIG5vdFxuICAgICAqIGluY2x1ZGVkIGluIHRoZSBvcHRpb25zIGhhc2gsIGl0IGlzIG5vdCBjaGFuZ2VkLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge09iamVjdH0gb3B0aW9ucyBPcHRpb24gaGFzaC4gRm9yIHNhbXBsZSBpbnB1dCwgc2VlIGBzZXREZWZhdWx0T3B0aW9uc2AgYWJvdmUuXG4gICAgICovXG4gICAgX3RoaXMuc2V0T3B0aW9ucyA9IGZ1bmN0aW9uKG9wdGlvbnMpe1xuICAgICAgICBpZiAob3B0aW9ucy5wcmVmaXhlcyl7XG4gICAgICAgICAgICBvcHQucHJlZml4ZXMgPSBvcHRpb25zLnByZWZpeGVzO1xuICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgfVxuICAgICAgICBpZiAob3B0aW9ucy5zZXBhcmF0b3JzKXtcbiAgICAgICAgICAgIG9wdC5zZXBhcmF0b3JzID0gb3B0aW9ucy5zZXBhcmF0b3JzO1xuICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgfVxuICAgICAgICBpZiAob3B0aW9ucy5jb250YWluZXJzKXtcbiAgICAgICAgICAgIG9wdC5jb250YWluZXJzID0gb3B0aW9ucy5jb250YWluZXJzO1xuICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodHlwZW9mIG9wdGlvbnMuY2FjaGUgIT09ICRVTkRFRklORUQpe1xuICAgICAgICAgICAgb3B0LnVzZUNhY2hlID0gISFvcHRpb25zLmNhY2hlO1xuICAgICAgICB9XG4gICAgICAgIGlmICh0eXBlb2Ygb3B0aW9ucy5zaW1wbGUgIT09ICRVTkRFRklORUQpe1xuICAgICAgICAgICAgdmFyIHRlbXBDYWNoZSA9IG9wdC51c2VDYWNoZTsgLy8gcHJlc2VydmUgdGhlc2UgdHdvIG9wdGlvbnMgYWZ0ZXIgXCJzZXREZWZhdWx0T3B0aW9uc1wiXG4gICAgICAgICAgICB2YXIgdGVtcEZvcmNlID0gb3B0LmZvcmNlO1xuICAgICAgICAgICAgXG4gICAgICAgICAgICBvcHQuc2ltcGxlID0gdHJ1dGhpZnkob3B0aW9ucy5zaW1wbGUpO1xuICAgICAgICAgICAgaWYgKG9wdC5zaW1wbGUpe1xuICAgICAgICAgICAgICAgIHNldFNpbXBsZU9wdGlvbnMoKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHNldERlZmF1bHRPcHRpb25zKCk7XG4gICAgICAgICAgICAgICAgb3B0LnVzZUNhY2hlID0gdGVtcENhY2hlO1xuICAgICAgICAgICAgICAgIG9wdC5mb3JjZSA9IHRlbXBGb3JjZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHR5cGVvZiBvcHRpb25zLmZvcmNlICE9PSAkVU5ERUZJTkVEKXtcbiAgICAgICAgICAgIG9wdC5mb3JjZSA9IHRydXRoaWZ5KG9wdGlvbnMuZm9yY2UpO1xuICAgICAgICB9XG4gICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNldHMgdXNlIG9mIGtleXBhdGggY2FjaGUgdG8gZW5hYmxlZCBvciBkaXNhYmxlZCwgZGVwZW5kaW5nIG9uIGlucHV0IHZhbHVlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFZhbHVlIHdoaWNoIHdpbGwgYmUgaW50ZXJwcmV0ZWQgYXMgYSBib29sZWFuIHVzaW5nIGB0cnV0aGlmeWAuIFwidHJ1ZVwiIHdpbGwgZW5hYmxlIGNhY2hlOyBcImZhbHNlXCIgd2lsbCBkaXNhYmxlLlxuICAgICAqL1xuICAgIF90aGlzLnNldENhY2hlID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgb3B0LnVzZUNhY2hlID0gdHJ1dGhpZnkodmFsKTtcbiAgICB9O1xuICAgIC8qKlxuICAgICAqIEVuYWJsZXMgdXNlIG9mIGtleXBhdGggY2FjaGUuXG4gICAgICogQHB1YmxpY1xuICAgICAqL1xuICAgIF90aGlzLnNldENhY2hlT24gPSBmdW5jdGlvbigpe1xuICAgICAgICBvcHQudXNlQ2FjaGUgPSB0cnVlO1xuICAgIH07XG4gICAgLyoqXG4gICAgICogRGlzYWJsZXMgdXNlIG9mIGtleXBhdGggY2FjaGUuXG4gICAgICogQHB1YmxpY1xuICAgICAqL1xuICAgIF90aGlzLnNldENhY2hlT2ZmID0gZnVuY3Rpb24oKXtcbiAgICAgICAgb3B0LnVzZUNhY2hlID0gZmFsc2U7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNldHMgXCJmb3JjZVwiIG9wdGlvbiB3aGVuIHNldHRpbmcgdmFsdWVzIGluIGFuIG9iamVjdCwgZGVwZW5kaW5nIG9uIGlucHV0IHZhbHVlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFZhbHVlIHdoaWNoIHdpbGwgYmUgaW50ZXJwcmV0ZWQgYXMgYSBib29sZWFuIHVzaW5nIGB0cnV0aGlmeWAuIFwidHJ1ZVwiIGVuYWJsZXMgXCJmb3JjZVwiOyBcImZhbHNlXCIgZGlzYWJsZXMuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Rm9yY2UgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBvcHQuZm9yY2UgPSB0cnV0aGlmeSh2YWwpO1xuICAgIH07XG4gICAgLyoqXG4gICAgICogRW5hYmxlcyBcImZvcmNlXCIgb3B0aW9uIHdoZW4gc2V0dGluZyB2YWx1ZXMgaW4gYW4gb2JqZWN0LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKi9cbiAgICBfdGhpcy5zZXRGb3JjZU9uID0gZnVuY3Rpb24oKXtcbiAgICAgICAgb3B0LmZvcmNlID0gdHJ1ZTtcbiAgICB9O1xuICAgIC8qKlxuICAgICAqIERpc2FibGVzIFwiZm9yY2VcIiBvcHRpb24gd2hlbiBzZXR0aW5nIHZhbHVlcyBpbiBhbiBvYmplY3QuXG4gICAgICogQHB1YmxpY1xuICAgICAqL1xuICAgIF90aGlzLnNldEZvcmNlT2ZmID0gZnVuY3Rpb24oKXtcbiAgICAgICAgb3B0LmZvcmNlID0gZmFsc2U7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNob3J0Y3V0IGZ1bmN0aW9uIHRvIGFsdGVyIFBhdGhUb29sa2l0IHN5bnRheCB0byBhIFwic2ltcGxlXCIgbW9kZSB0aGF0IG9ubHkgdXNlc1xuICAgICAqIHNlcGFyYXRvcnMgYW5kIG5vIG90aGVyIG9wZXJhdG9ycy4gXCJTaW1wbGVcIiBtb2RlIGlzIGVuYWJsZWQgb3IgZGlzYWJsZWQgYWNjb3JkaW5nXG4gICAgICogdG8gdGhlIGZpcnN0IGFyZ3VtZW50IGFuZCB0aGUgc2VwYXJhdG9yIG1heSBiZSBjdXN0b21pemVkIHdpdGggdGhlIHNlY29uZFxuICAgICAqIGFyZ3VtZW50IHdoZW4gZW5hYmxpbmcgXCJzaW1wbGVcIiBtb2RlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFZhbHVlIHdoaWNoIHdpbGwgYmUgaW50ZXJwcmV0ZWQgYXMgYSBib29sZWFuIHVzaW5nIGB0cnV0aGlmeWAuIFwidHJ1ZVwiIGVuYWJsZXMgXCJzaW1wbGVcIiBtb2RlOyBcImZhbHNlXCIgZGlzYWJsZXMuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHNlcCBTZXBhcmF0b3Igc3RyaW5nIHRvIHVzZSBpbiBwbGFjZSBvZiB0aGUgZGVmYXVsdCBcIi5cIlxuICAgICAqL1xuICAgIF90aGlzLnNldFNpbXBsZSA9IGZ1bmN0aW9uKHZhbCwgc2VwKXtcbiAgICAgICAgdmFyIHRlbXBDYWNoZSA9IG9wdC51c2VDYWNoZTsgLy8gcHJlc2VydmUgdGhlc2UgdHdvIG9wdGlvbnMgYWZ0ZXIgXCJzZXREZWZhdWx0T3B0aW9uc1wiXG4gICAgICAgIHZhciB0ZW1wRm9yY2UgPSBvcHQuZm9yY2U7XG4gICAgICAgIG9wdC5zaW1wbGUgPSB0cnV0aGlmeSh2YWwpO1xuICAgICAgICBpZiAob3B0LnNpbXBsZSl7XG4gICAgICAgICAgICBzZXRTaW1wbGVPcHRpb25zKHNlcCk7XG4gICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgc2V0RGVmYXVsdE9wdGlvbnMoKTtcbiAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICBvcHQudXNlQ2FjaGUgPSB0ZW1wQ2FjaGU7XG4gICAgICAgICAgICBvcHQuZm9yY2UgPSB0ZW1wRm9yY2U7XG4gICAgICAgIH1cbiAgICAgICAgY2FjaGUgPSB7fTtcbiAgICB9O1xuICAgIFxuICAgIC8qKlxuICAgICAqIEVuYWJsZXMgXCJzaW1wbGVcIiBtb2RlXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBzZXAgU2VwYXJhdG9yIHN0cmluZyB0byB1c2UgaW4gcGxhY2Ugb2YgdGhlIGRlZmF1bHQgXCIuXCJcbiAgICAgKiBAc2VlIHNldFNpbXBsZVxuICAgICAqL1xuICAgIF90aGlzLnNldFNpbXBsZU9uID0gZnVuY3Rpb24oc2VwKXtcbiAgICAgICAgb3B0LnNpbXBsZSA9IHRydWU7XG4gICAgICAgIHNldFNpbXBsZU9wdGlvbnMoc2VwKTtcbiAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgY2FjaGUgPSB7fTtcbiAgICB9O1xuICAgIFxuICAgIC8qKlxuICAgICAqIERpc2FibGVzIFwic2ltcGxlXCIgbW9kZSwgcmVzdG9yZXMgZGVmYXVsdCBQYXRoVG9vbGtpdCBzeW50YXhcbiAgICAgKiBAcHVibGljXG4gICAgICogQHNlZSBzZXRTaW1wbGVcbiAgICAgKiBAc2VlIHNldERlZmF1bHRPcHRpb25zXG4gICAgICovXG4gICAgX3RoaXMuc2V0U2ltcGxlT2ZmID0gZnVuY3Rpb24oKXtcbiAgICAgICAgdmFyIHRlbXBDYWNoZSA9IG9wdC51c2VDYWNoZTsgLy8gcHJlc2VydmUgdGhlc2UgdHdvIG9wdGlvbnMgYWZ0ZXIgXCJzZXREZWZhdWx0T3B0aW9uc1wiXG4gICAgICAgIHZhciB0ZW1wRm9yY2UgPSBvcHQuZm9yY2U7XG4gICAgICAgIG9wdC5zaW1wbGUgPSBmYWxzZTtcbiAgICAgICAgc2V0RGVmYXVsdE9wdGlvbnMoKTtcbiAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgb3B0LnVzZUNhY2hlID0gdGVtcENhY2hlO1xuICAgICAgICBvcHQuZm9yY2UgPSB0ZW1wRm9yY2U7XG4gICAgICAgIGNhY2hlID0ge307XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgcHJvcGVydHkgc2VwYXJhdG9yIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoaXMgb3BlcmF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLnNldFNlcGFyYXRvclByb3BlcnR5ID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5zZXBhcmF0b3JzW3ZhbF0uZXhlYyA9PT0gJFBST1BFUlRZKSAmJiAhKG9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5zZXBhcmF0b3JzLCAkUFJPUEVSVFksIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRTZXBhcmF0b3JQcm9wZXJ0eSAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFNlcGFyYXRvclByb3BlcnR5IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgY29sbGVjdGlvbiBzZXBhcmF0b3IgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0U2VwYXJhdG9yQ29sbGVjdGlvbiA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuc2VwYXJhdG9yc1t2YWxdLmV4ZWMgPT09ICRDT0xMRUNUSU9OKSAmJiAhKG9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5zZXBhcmF0b3JzLCAkQ09MTEVDVElPTiwgdmFsKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFNlcGFyYXRvckNvbGxlY3Rpb24gLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRTZXBhcmF0b3JDb2xsZWN0aW9uIC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgcGFyZW50IHByZWZpeCBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGlzIG9wZXJhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRQcmVmaXhQYXJlbnQgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdLmV4ZWMgPT09ICRQQVJFTlQpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQucHJlZml4ZXMsICRQQVJFTlQsIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhQYXJlbnQgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhQYXJlbnQgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSByb290IHByZWZpeCBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGlzIG9wZXJhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRQcmVmaXhSb290ID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQucHJlZml4ZXNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXS5leGVjID09PSAkUk9PVCkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5wcmVmaXhlcywgJFJPT1QsIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhSb290IC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4Um9vdCAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIHBsYWNlaG9sZGVyIHByZWZpeCBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGlzIG9wZXJhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRQcmVmaXhQbGFjZWhvbGRlciA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnByZWZpeGVzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0uZXhlYyA9PT0gJFBMQUNFSE9MREVSKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LnByZWZpeGVzLCAkUExBQ0VIT0xERVIsIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhQbGFjZWhvbGRlciAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeFBsYWNlaG9sZGVyIC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgY29udGV4dCBwcmVmaXggaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0UHJlZml4Q29udGV4dCA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnByZWZpeGVzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0uZXhlYyA9PT0gJENPTlRFWFQpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQucHJlZml4ZXMsICRDT05URVhULCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4Q29udGV4dCAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeENvbnRleHQgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBwcm9wZXJ0eSBjb250YWluZXIgY2hhcmFjdGVycyBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIG9wZW5lci5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gY2xvc2VyIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIGNsb3Nlci5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDb250YWluZXJQcm9wZXJ0eSA9IGZ1bmN0aW9uKHZhbCwgY2xvc2VyKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSAmJiB0eXBlb2YgY2xvc2VyID09PSAkU1RSSU5HICYmIGNsb3Nlci5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LmNvbnRhaW5lcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdLmV4ZWMgPT09ICRQUk9QRVJUWSkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuY29udGFpbmVycywgJFBST1BFUlRZLCB2YWwsIGNsb3Nlcik7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJQcm9wZXJ0eSAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lclByb3BlcnR5IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgc2luZ2xlIHF1b3RlIGNvbnRhaW5lciBjaGFyYWN0ZXJzIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgb3BlbmVyLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgY2xvc2VyLlxuICAgICAqL1xuICAgIF90aGlzLnNldENvbnRhaW5lclNpbmdsZXF1b3RlID0gZnVuY3Rpb24odmFsLCBjbG9zZXIpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxICYmIHR5cGVvZiBjbG9zZXIgPT09ICRTVFJJTkcgJiYgY2xvc2VyLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQuY29udGFpbmVyc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0uZXhlYyA9PT0gJFNJTkdMRVFVT1RFKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5jb250YWluZXJzLCAkU0lOR0xFUVVPVEUsIHZhbCwgY2xvc2VyKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lclNpbmdsZXF1b3RlIC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyU2luZ2xlcXVvdGUgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBkb3VibGUgcXVvdGUgY29udGFpbmVyIGNoYXJhY3RlcnMgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBvcGVuZXIuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNsb3NlciBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBjbG9zZXIuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q29udGFpbmVyRG91YmxlcXVvdGUgPSBmdW5jdGlvbih2YWwsIGNsb3Nlcil7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEgJiYgdHlwZW9mIGNsb3NlciA9PT0gJFNUUklORyAmJiBjbG9zZXIubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5jb250YWluZXJzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXS5leGVjID09PSAkRE9VQkxFUVVPVEUpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LmNvbnRhaW5lcnMsICRET1VCTEVRVU9URSwgdmFsLCBjbG9zZXIpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyRG91YmxlcXVvdGUgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJEb3VibGVxdW90ZSAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIGZ1bmN0aW9uIGNhbGwgY29udGFpbmVyIGNoYXJhY3RlcnMgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBvcGVuZXIuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNsb3NlciBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBjbG9zZXIuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q29udGFpbmVyQ2FsbCA9IGZ1bmN0aW9uKHZhbCwgY2xvc2VyKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSAmJiB0eXBlb2YgY2xvc2VyID09PSAkU1RSSU5HICYmIGNsb3Nlci5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LmNvbnRhaW5lcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdLmV4ZWMgPT09ICRDQUxMKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5jb250YWluZXJzLCAkQ0FMTCwgdmFsLCBjbG9zZXIpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyQ2FsbCAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lckNhbGwgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBldmFsIHByb3BlcnR5IGNvbnRhaW5lciBjaGFyYWN0ZXJzIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgb3BlbmVyLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgY2xvc2VyLlxuICAgICAqL1xuICAgIF90aGlzLnNldENvbnRhaW5lckV2YWxQcm9wZXJ0eSA9IGZ1bmN0aW9uKHZhbCwgY2xvc2VyKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSAmJiB0eXBlb2YgY2xvc2VyID09PSAkU1RSSU5HICYmIGNsb3Nlci5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LmNvbnRhaW5lcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdLmV4ZWMgPT09ICRFVkFMUFJPUEVSVFkpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LmNvbnRhaW5lcnMsICRFVkFMUFJPUEVSVFksIHZhbCwgY2xvc2VyKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lckV2YWxQcm9wZXJ0eSAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lclByb3BlcnR5IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFJlc2V0IGFsbCBQYXRoVG9vbGtpdCBvcHRpb25zIHRvIHRoZWlyIGRlZmF1bHQgdmFsdWVzLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKi9cbiAgICBfdGhpcy5yZXNldE9wdGlvbnMgPSBmdW5jdGlvbigpe1xuICAgICAgICBzZXREZWZhdWx0T3B0aW9ucygpO1xuICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICBjYWNoZSA9IHt9O1xuICAgIH07XG5cbiAgICAvLyBJbml0aWFsaXplIG9wdGlvbiBzZXRcbiAgICBzZXREZWZhdWx0T3B0aW9ucygpO1xuICAgIHVwZGF0ZVJlZ0V4KCk7XG5cbiAgICAvLyBBcHBseSBjdXN0b20gb3B0aW9ucyBpZiBwcm92aWRlZCBhcyBhcmd1bWVudCB0byBjb25zdHJ1Y3RvclxuICAgIG9wdGlvbnMgJiYgX3RoaXMuc2V0T3B0aW9ucyhvcHRpb25zKTtcblxufTtcblxuZXhwb3J0IGRlZmF1bHQgUGF0aFRvb2xraXQ7XG4iXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6Ijs7Ozs7O0FBQUE7Ozs7Ozs7QUFPQSxBQUVBO0FBQ0EsSUFBSSxLQUFLLEdBQUcsQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUM7OztBQUd2QyxJQUFJLFNBQVMsT0FBTyxHQUFHO0lBQ25CLFVBQVUsTUFBTSxXQUFXO0lBQzNCLE9BQU8sU0FBUyxRQUFRO0lBQ3hCLE9BQU8sU0FBUyxRQUFRO0lBQ3hCLEtBQUssV0FBVyxNQUFNO0lBQ3RCLFlBQVksSUFBSSxhQUFhO0lBQzdCLFFBQVEsUUFBUSxTQUFTO0lBQ3pCLFNBQVMsT0FBTyxVQUFVO0lBQzFCLFdBQVcsS0FBSyxZQUFZO0lBQzVCLEtBQUssV0FBVyxNQUFNO0lBQ3RCLFlBQVksSUFBSSxhQUFhO0lBQzdCLFlBQVksSUFBSSxhQUFhO0lBQzdCLEtBQUssV0FBVyxNQUFNO0lBQ3RCLGFBQWEsR0FBRyxjQUFjLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7O0FBb0JuQyxJQUFJLGFBQWEsR0FBRyxTQUFTLFFBQVEsRUFBRSxHQUFHLENBQUM7SUFDdkMsSUFBSSxHQUFHLEdBQUcsUUFBUSxDQUFD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