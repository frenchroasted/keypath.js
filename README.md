# PathToolkit

> A configurable, high-speed, feature-rich object path resolver.

## Installation

### Git

`git clone https://github.com/frenchroasted/path-toolkit.git path-toolkit`

### NPM

`npm install path-toolkit`

### Bower

`bower install path-toolkit`

## Documentation

* [API](docs/API.md)

## Usage

```javascript
var PathToolkit = require('path-toolkit');
var ptk = new PathToolkit();
var obj = {
    foo: {
        bar: [ 'a', 'b', 'c']
    }
};
ptk.get(obj, 'foo.bar.1'); // 'b'
ptk.set(obj, 'foo.bar.0', 'x'); // true
ptk.get(obj, 'foo.bar.sort().reverse().0'); // 'x'
```

PathToolkit includes many more features, all documented with example code in the [API](docs/API.md). The path syntax is completely configurable, the interpreter is fast in general, and is very, very fast when processing simple property-sequence paths.
