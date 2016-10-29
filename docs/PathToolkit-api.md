# PathToolkit
The PathToolkit keypath interpreter supports dot notation ('foo.bar.2') for object/array property lookup. It also supports relative paths, referencing other property values as a key within a path, function calls (with arguments), numbered placeholders within keypaths, wildcard paths, collections, and escaped keypaths. In addition, the operators in the interpreter may be configured if, for example, it's more convenient to use : instead of . as the separator.

PathToolkit is a constructor which is used to create PathToolkit instances. Each instance independently tracks its own configuration, so different instances may be created to process different path syntaxes.

```javascript
var PathToolkit = require('path-toolkit-min');
var ptk = new PathToolkit( /* options */ );
```

The constructor accepts an optional argument: an options object which can be used to override the default configuration at the point of instantiation. See `setOptions` documentation below for details - the constructor calls `setOptions` to process the options argument, if present.

## Examples
### get
```javascript
var val1 = ptk.get(obj, path);
var val2 = ptk.get(obj, path, arg1, arg2,..., argN);
```

If the keypath is invalid or does not exist within the target object, `get` returns `undefined`. The `get` function will short circuit and return as soon as `undefined` is detected to prevent unexpected object reference exceptions.

Simple keypaths with dot notation and no special operators are optimally executed in standalone code for high performance.
```javascript
var data = {
    foo: {
        bar: ['a','b','c']
    }
};
ptk.get(data, 'foo.bar.2'); // 'c'
```

#### Separators
Enclosing a path segment in `[ ]` is equivalent to surrounding it with the separator (`.` by default). Use of the separator character is optional adjacent to the `[ ]` container. The path `a.b.c.d` is equivalent to `a[b]c[d]`.
```javascript
var data = {
    foo: {
        bar: ['a','b','c']
    }
};
ptk.get(data, 'foo.[bar].2'); // 'c'
ptk.get(data, 'foo[bar]2'); // 'c'
ptk.get(data, 'foo[bar][2]'); // 'c'
```

#### Quotes
Quotes, either single or double (`'` and `"`) may be used to mark a path segment as literal text - any special characters within the quoted text will be treated as plain text and will not be acted upon. Quoted path segments may appear as part of the main path string or within other containers.
```javascript
var data = {
    foo: {
        bar: ['a','b','c'],
        'abc': 'def',
        '"abc"': 'xyz',
        'one.two': 'three'
    }
};
ptk.get(data, "foo['bar']2"); // 'c'
ptk.get(data, 'foo["bar"]2'); // 'c'
ptk.get(data, '"abc"'); // 'def'
ptk.get(data, '["abc"]'); // 'def'
ptk.get(data, '\\"abc\\"'); // 'xyz' (see escaped strings below)
ptk.get(data, '"one.two"'); // 'three'
ptk.get(data, '["one.two"]'); // 'three'
```

#### Collections
Collections are implemented with `,`.
```javascript
var data = {
    foo: {
        bar: ['a','b','c'],
        a: 'z',
        b: 'y'
    }
};
ptk.get(data, 'foo.bar.0,2'); // ['a', 'c']
ptk.get(data, 'foo.bar[0,2]'); // ['a', 'c']
ptk.get(data, 'foo.bar.a,b'); // ['z', 'y']
```

#### Each separator
The "Each" separator is `<` by default. This can also be thought of as a "fork" operator. When this separator is used following an array, either an array created through the path using a Collection or an array that is evaluated from the data object, the token following `<` will be evaluated separately against each index of the array, and the results are accumulated into a new array. It is much like Array.map except that "map" executes a function against each index while the Each separator can return a property or any other PathToolkit evaluation from each index.

The Collection separator creates an array at that point, and generally the following token will be an index or some function that operates on an array. The result will either be an array or a single value, depending on the evaluated result. The Each separator will create a new array as a result of applying its token to each element of the prior array, so that token should be one that operates on the element, not on the array as a whole. These Each tokens may be chained together.
```javascript
var data = {
    foo: {
        bar: ['a','b','c']
    },
    people: [
        {
            id: 1,
            name: 'John'
        },
        {
            id: 2,
            name: 'Jane'
        },
        {
            id: 3,
            name: 'Mephistopholes'
        }
    ]
};
// The following two code sections produce equivalent results:
// 1.
// Intermediate step: ptk.get(data, 'foo.bar.0,2'); // ['a', 'c']
ptk.get(data, 'foo.bar.0,2<toUpperCase()'); // ['A', 'C'] - note that "toUpperCase" is a string function, not an array function

// 2
[data.foo.bar[0], data.foo.bar[1]].map(function(val){ return val.toUpperCase(); }); // ['A', 'C']

ptk.get(data, 'foo.bar.*'); // ['a', 'b', 'c']
ptk.get(data, 'foo.bar.*<toUpperCase()'); // ['A', 'B', 'C']

ptk.get(data, 'people.*<id'); // [1, 2, 3]
ptk.get(data, 'people.*<id,name'); // [ [1, 'John'], [2, 'Jane'], [3, 'Mephistopholes'] ]

```

#### Function execution
Functions may be called with `( )`.
```javascript
var data = {
    foo: {
        bar: ['a','b','c']
    }
};
ptk.get(data, 'foo.bar.2,0.sort()'); // ['a', 'c']
ptk.get(data, 'foo.bar.2,0.sort().0'); // 'a'
```

#### Indirect or Evaluated Properties
Indirect property references are implemented with `{ }`. Use of these can be confusing at times, and they don't work quite the same way as the javascript `[ ]` object property operator. A `{ }` container is expected to contain a valid keypath. This keypath is interpreted from the context of the evaluated value at that point in the keypath, and the result is **then** interpreted as the property of the preceding path. Once the sub-keypath has been evaluated, the context is returned to the evaluation point before proceeding. Here are some examples to illustrate.
```javascript
var data = {
    foo: {
        bar: ['a','b','c'],
        a: 'one',
        b: 'two'
    }
};
ptk.get(data, 'foo.bar.0'); // 'a'
ptk.get(data, 'foo.a'); // 'one'
// Use the value at "foo.bar.0" as a property of "foo"...
ptk.get(data, 'foo{bar.0}'); // 'one'
ptk.get(data, 'foo{bar.0,2.sort().0}'); // 'one'
```

#### Context modifiers
Object context can be shifted upwards using prefixes `^` for 'parent' and `~` for 'root'. These prefixes apply in the base keypath as well as internal sub-keypaths.
```javascript
var data = {
    foo: {
        bar: ['a','b','c'],
        a: 'one',
        b: 'two'
    }
};
ptk.get(data, 'foo.bar.0'); // 'a'
ptk.get(data, 'foo.a'); // 'one'
ptk.get(data, 'foo.bar.^a'); // 'one'
ptk.get(data, 'foo.bar.~foo.bar.0'); // 'a'
```

#### Placeholders
Numbered placeholders, indicated with `%n`, are supported as extra arguments to `get`. By numbering the placeholders according to their place in the args list, these values may be used in multiple places within the keypath. Using placeholders is another way to include string values which may contain reserved keypath characters since the placeholder values are not interpreted further; they are used as-is. **The numbering sequence begins at 1.**
```javascript
var data = {
    foo: {
        bar: ['a','b','c'],
        a: 'one',
        b: 'two'
    }
};
ptk.get(data, 'foo.bar.0'); // 'a'
ptk.get(data, 'foo.%1.%2', 'bar', (2-2)); // 'a'
ptk.get(data, 'foo{%1.0,%1.1', 'bar'); // ['one','two']
ptk.get(data, 'foo.bar.~foo.bar.0'); // 'a'
```

#### Context Placeholders
Numbered context placeholders are indicated with `@n`, again as extra arguments to `get`. These placeholders are tied to arguments in the same way as the `%n` placeholders described above. However, **context** placeholders are different in that they allow references to objects external to the original data object being processed. They are called "context placeholders" because their use will replace the current object context with the referenced value instead. This provides a way to, for example, call functions defined in the programs variable scope or to pluck property names from other objects.
```javascript
var data = {
    foo: {
        bar: ['a','b','c'],
        a: 'one',
        b: 'two',
        xx: 'blah'
    }
};
var fn = function(str){ return str+str; }
var other = {
    prop: 'bar'
};

ptk.get(data, 'foo.bar.0'); // 'a'
ptk.get(data, 'foo.@1.prop', other); // 'bar'
ptk.get(data, 'foo{@1.prop}0', other); // 'a'
ptk.get(data, 'foo{@1(%2)}', fn, 'x'); // 'blah'
```
Use of the context placeholder is most likely to be helpful within the indirect property container (`{ }`) since that container creates a temporary context for evaluation, then returns to the original data context. In the above examples, the path `'foo.@1.prop'` will replace the original data context for the remainder of the evaluation. The net result is exactly the same as finding `other.prop` directly, except with more work and obfuscation. Within the indirect property container, though, this mechanism can be used to create data transformations or to run locally defined functions that are not native to the values.

### set
```javascript
var result1 = ptk.set(obj, path, newVal);
var result2 = ptk.set(obj, path, newVal, arg1, arg2,..., argN);
```

Any property specified in a keypath may be set to a new value. The set function returns `true` if the set was successful, `false` if not. By default, only the final property in the keypath may be set - any intermediate properties must be defined and valid or `set` will fail. The final property does not need to exist prior to `set`, it will be created if necessary. This behavior is equivalent to setting an object property in plain javascript code.

This behavior may be changed using `setOptions` (see below), by enabling the "force" option (`ptk.setForceOn();`, see "Options" below). The "force" option will only change `set` behavior for simple dot-separated paths. The use of other mechanisms such as collections, indirect properties, etc. will prevent `set` from succeeding due to the difficulty in guessing how and what properties to create in some advanced scenarios. **Note:** If an intermediate value must be created, it will **always** be created as a plain object, never an array, even if the following path segment is an integer. Since all paths are Strings, it is impossible to guess whether the path segment "12345" is the integer 12,345 or the ZIP code "12345", for example, and it could be computationally expensive to create an array with only one defined index when that index is a very high number. Therefore, be aware that when "force" is enabled, the target object may acquire objects within in places where arrays are expected. If this is a risk in the program, it would be best to initialize these values before calling `set` or else leave "force" set to `false`.
```javascript
var data = {
    'foo': {}
};
data.foo.bar = 1;  // valid
data.foo.a.b.c = 2; // NOT valid because "data.foo.a" is undefined, so "data.foo.a.b" throws an error
ptk.set(data, 'foo.bar', 1); // 1
ptk.set(data, 'foo.a.b.c', 2); // undefined (ptk.set fails)
ptk.setOptions({force: true});
ptk.set(data, 'foo.a.b.c', 2); // 2 (ptk.set creates foo.a, foo.a.b, and foo.a.b.c, setting foo.a.b.c = 2)
```

All keypaths that are valid for `get` will behave in the same way for `set`. One special case is worth noting: If the final path segment is a collection, then every property in that collection will be set to the new value.
```javascript
var data = {
    foo: {
        bar: ['a','b','c']
    }
};
ptk.set(data, 'foo.bar.0,1', 'xxx'); // 'xxx'
ptk.get(data, 'foo.bar.0,1,2'); // ['xxx', 'xxx', 'c']
```

### find
```javascript
var path = ptk.find(obj, val); // first found path to value
var allPaths = ptk.find(obj, val, 'all'); // all paths to value
```

Does a seep scan through the data object, executing a `===` test on each node against the provided value. If the equals test returns true, the path is returned. By default, only one path is returned and the `find` function aborts as soon as it succeeds. If the last argument is 'all', `find` will scan the full object and return all paths with matching values.

`find` returns a path that is compliant with the current options. If a keypath segment includes special characters, it will be quoted with the current "singlequote" container character, and that quote will be escaped in the segment if it appears.

**Note:** Object keys are sorted in processing, so repeated calls to `find` should produce repeatable results.

```javascript
var data = {
    foo: {
        bar: ['a','b','c']
    },
    xyz: 'b'
};
ptk.find(data, 'b'); // 'foo.bar.1'
ptk.find(data, 'b', 'all'); // ['foo.bar.1','xyz']
```

### escape
```javascript
var str = 'John Q. Doe';
var escapedPathSegment = ptk.escape(str);
ptk.get(data, ['people', escapedPathSegment, 'address'].join('.'));
```

The path interpreter supports escaped characters using backslash (`\`). This is another way to deal with data where operators may be present in the data object as property names. For example, an object that uses full names as keys may include `.` or an object using phone numbers as keys may include `( )`. By pre-processing the path segment with `escape`, these operators will all be prepended with `\`, making the path safe for execution.

**Important:** Do **not** execute `escape` on your full keypath, since it will escape all the separators (`.`), turning your keypath into a single property name. This function is meant to be executed on only a single keypath segment, and is most useful when building a keypath dynamically using unknown values.

The `escape` function will obey whatever characters are currently defined as operators at the time of execution. If using non-standard operators, simply call `setOptions` before executing `escape` to make sure `escape` is looking for the correct operators.

### isValid

```javascript
var bool = ptk.isValid(keypath);
```

Returns a boolean value: true if the keypath is syntactically valid, false if not. This `isValid` does not take a data object; it does not test whether the keypath exists in an object. It merely evaluates the syntax and indicates if it is improper. This can help when dynamically building a keypath or using complex nested structures. `isValid` will identify mismatched containers and a keypath that ends in `\`, with no characters following to escape.

### getTokens
```javascript
var tokens = ptk.getTokens(keypath);
```

Returns the tokenized object representing the keypath. This tokens object may be used when calling `get` or `set` in place of a string keypath. When used, those functions will skip the tokenizing step. `getTokens` may be used to pre-compile a keypath for later use, making the `get` and `set` functions slightly more efficient for some keypaths. If the keypath is invalid, `undefined` is returned.

### Options

The PathToolkit library's path interpreter can be customized in many ways. Behavior like caching and whether `set` will create intermediate properties as well as most special characters may be customized. There are a variety of ways to set these options, ranging from the all-at-once `setOptions` function to individual "turn this option on or off" and "change this particular character to a different character" functions.

Options are stored locally within each PathToolkit instance, so multiple instances may carry different options.

Any time the path syntax is altered through any of the following functions, the PathToolkit instance's local cache is cleared so that paths will be re-evaluated with the new syntax.

#### resetOptions
```javascript
ptk.resetOptions();
```
Resets all options to their default state.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

The default options are as follows:
```javascript
{
    cache: true,
    force: false,
    simple: false,
    separators: {
        '.': {
            'exec': 'property'
        },
        ',': {
            'exec': 'collection'
        },
        '<': {
            'exec': 'each'
        }
    },
    prefixes: {
        '^': {
            'exec': 'parent'
        },
        '~': {
            'exec': 'root'
        },
        '%': {
            'exec': 'placeholder'
        },
        '@': {
            'exec': 'context'
        }
    },
    containers: {
        '[': {
            'closer': ']',
            'exec': 'property'
        },
        '\'': {
            'closer': '\'',
            'exec': 'singlequote'
        },
        '"': {
            'closer': '"',
            'exec': 'doublequote'
        },
        '(': {
            'closer': ')',
            'exec': 'call'
        },
        '{': {
            'closer': '}',
            'exec': 'evalProperty'
        }
    }
}
```

#### setCache, setCacheOn/Off
```javascript
ptk.setCache(true);  // Enables cache. Also accepts 'on', 'yes', 'true'; not case-sensitive.
                    // Any non-string value that javascript considers "truthy" will enable cache.
ptk.setCache(false); // Disables cache. Any non-string value considered "falsy" will disable cache.

ptk.setCacheOn();    // enables cache
ptk.setCacheOff();   // disables cache
```
For any path beyond the simple case (see `get` above), a tokenizing function parses the path before it is resolved. By default, the results of the tokenizing function are cached so repeated calls for the same path string can skip the tokenizing step. If cache is disabled, any new path evaluation will execute the tokenizing routine, even if the path was stored in cache prior to cache being disabled. Any new paths processed while cache is disabled will not be stored in cache.

Each PathToolkit instance carries its own cache.

#### setForce, setForceOn/Off
```javascript
ptk.setForce(true);  // Enables forced property creation. Also accepts 'on', 'yes', 'true'; not case-sensitive.
                    // Any non-string value that javascript considers "truthy" will enable this option.
ptk.setForce(false); // Disables forced property creation. Any non-string value considered "falsy" will disable.

ptk.setForceOn();    // enables forced property creation
ptk.setForceOff();   // disables forced property creation
```
This option dictates whether the `set` function will create intermediate properties as needed to set a value at the end of a path. This feature is described above in the documentation for `set`.

#### setSimple, setSimpleOn/Off
```javascript
ptk.setSimple(true, separator);  // Enables simple path syntax. Also accepts 'on', 'yes', 'true'; not case-sensitive.
                                // Any non-string value that javascript considers "truthy" will enable this option.
ptk.setSimple(false); // Disables simple path syntax. Any non-string value considered "falsy" will disable.
                     // SEE NOTE BELOW

ptk.setSimpleOn(separator);    // enables simple path syntax
ptk.setSimpleOff();            // disables simple path syntax; SEE NOTE BELOW
```
The "separator" argument is optional. If not provided, the default separator "." will be used.

In many cases, the more advanced features offered here are not necessary and only simple, character-separated paths will be processed. In this case, it can be convenient to disable all the unnecessary special characters to avoid escaping them if they occur as property names in the paths. The "simple" option removes all special characters from the path syntax except for a single separator character. That character is "." by default, but it can be set to any other character as needed ("/", for example). Any character is allowed as long as it is only one character.

**NOTE:** When "simple" mode is **disabled**, the full set of default characters will be restored. Calling `setSimpleOff()` is nearly equivalent to calling `resetOptions()` except that the "cache" and "force" options are not affected by `setSimpleOff()`. The same is true for `setSimple(false)`.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

#### setSeparatorProperty
```javascript
ptk.setSeparatorProperty('/'); // 'one.two.three' -> 'one/two/three'
```
Removes the existing character used for this purpose and sets the new character instead. The code above is merely an example: any new character is allowed as long as it is only one character.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setSeparatorCollection
```javascript
ptk.setSeparatorCollection('/'); // 'one.two,three.four' -> 'one.two/three.four'
```
Removes the existing character used for this purpose and sets the new character instead. The code above is merely an example: any new character is allowed as long as it is only one character.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setPrefixParent
```javascript
ptk.setPrefixParent('!'); // 'one{^two.three}four' -> 'one{!two.three}four'
```
Removes the existing character used for this purpose and sets the new character instead. The code above is merely an example: any new character is allowed as long as it is only one character.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setPrefixRoot
```javascript
ptk.setPrefixRoot('#'); // 'one{~two.three}four' -> 'one{#two.three}four'
```
Removes the existing character used for this purpose and sets the new character instead. The code above is merely an example: any new character is allowed as long as it is only one character.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setPrefixPlaceholder
```javascript
ptk.setPrefixPlaceholder('&'); // 'one.%1.three' -> 'one.&1.three'
```
Removes the existing character used for this purpose and sets the new character instead. The code above is merely an example: any new character is allowed as long as it is only one character.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setPrefixContext
```javascript
ptk.setPrefixContext('+'); // 'one.@1()' -> 'one.+1()'
```
Removes the existing character used for this purpose and sets the new character instead. The code above is merely an example: any new character is allowed as long as it is only one character.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setContainerProperty
```javascript
ptk.setContainerProperty('^', '>'); // 'one[two]three' -> 'one^two>three'
```
Container characters are set in pairs. The first argument is the "opener" and the second is the "closer". In most cases, paths are easier to read if the arguments are different (e.g. "[" and "]"). If the opener and closer are different, it's also possible to nest the container ("a[b[c]]d". For cases like quotes, where the opener typically is the same as the closer, quotes cannot be nested directly.

Both areguments are **required**.

Removes the existing characters used for this purpose and sets the new characters instead. The code above is merely an example: any new characters are allowed as long as each argument is only one character long.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setContainerSinglequote
```javascript
ptk.setContainerSinglequote('|', '|'); // "one['two']three" -> "one[|two|]three"
```
Container characters are set in pairs. The first argument is the "opener" and the second is the "closer". In most cases, paths are easier to read if the arguments are different (e.g. "[" and "]"). If the opener and closer are different, it's also possible to nest the container ("a[b[c]]d"). For cases like quotes, where the opener typically is the same as the closer, quotes cannot be nested directly.

Both areguments are **required**.

Removes the existing characters used for this purpose and sets the new characters instead. The code above is merely an example: any new characters are allowed as long as each argument is only one character long.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setContainerDoublequote
```javascript
ptk.setContainerDoublequote('|', '|'); // 'one["two"]three' -> 'one[|two|]three'
```
Container characters are set in pairs. The first argument is the "opener" and the second is the "closer". In most cases, paths are easier to read if the arguments are different (e.g. "[" and "]"). If the opener and closer are different, it's also possible to nest the container ("a[b[c]]d". For cases like quotes, where the opener typically is the same as the closer, quotes cannot be nested directly.

Both areguments are **required**.

Removes the existing characters used for this purpose and sets the new characters instead. The code above is merely an example: any new characters are allowed as long as each argument is only one character long.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setContainerCall
```javascript
ptk.setContainerCall('^', '>'); // 'one.fn()' -> 'one.fn^>'
```
Container characters are set in pairs. The first argument is the "opener" and the second is the "closer". In most cases, paths are easier to read if the arguments are different (e.g. "[" and "]"). If the opener and closer are different, it's also possible to nest the container ("a[b[c]]d". For cases like quotes, where the opener typically is the same as the closer, quotes cannot be nested directly.

Both areguments are **required**.

Removes the existing characters used for this purpose and sets the new characters instead. The code above is merely an example: any new characters are allowed as long as each argument is only one character long.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setContainerEvalProperty
```javascript
ptk.setContainerEvalProperty('^', '>'); // 'one{two.three}four' -> 'one^two.three>four'
```
Container characters are set in pairs. The first argument is the "opener" and the second is the "closer". In most cases, paths are easier to read if the arguments are different (e.g. "[" and "]"). If the opener and closer are different, it's also possible to nest the container ("a[b[c]]d". For cases like quotes, where the opener typically is the same as the closer, quotes cannot be nested directly.

Both areguments are **required**.

Removes the existing characters used for this purpose and sets the new characters instead. The code above is merely an example: any new characters are allowed as long as each argument is only one character long.

Clears the cache to force all paths to be re-evaluated with the new path syntax.

Throws error if: argument is missing or empty string; argument is more than one character long; argument is already in use for some other purpose in the path syntax.

#### setOptions
```javascript
ptk.setOptions(opts);
```
Takes an options object as an argument and can set one, some, or all options at once. The operator characters come in three categories: separators, prefixes, and containers. Any or all of these may be set when calling `setOptions`, the function will simply **replace** the existing group with whatever is found in the provided options object. If an option (like "cache" or "force") or a character group (like "separators") is not present in the options argument, that option or character group will not be changed.

```javascript
// This command is equivalent to "setSimpleOn('/')"
ptk.setOptions({
    // "cache" and "force" are not altered
    simple: true,
    separators: {
        '/': {
            exec: 'property'
        }
        // the "collection" character is removed from the syntax
    },
    // "prefixes" and "containers" are erased, these characters are removed from the syntax
    prefixes: {},
    containers: {}
});

// Equivalent to "setCacheOff()"
ptk.setOptions({ cache: false });
```

If any of the character groups is set using setOptions, the cache is cleared to force all paths to be re-evaluated with the new path syntax.
