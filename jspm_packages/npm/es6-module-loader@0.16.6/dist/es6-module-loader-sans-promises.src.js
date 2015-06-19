/* */ 
"format cjs";
(function(process) {
  (function(__global) {
    $__Object$getPrototypeOf = Object.getPrototypeOf || function(obj) {
      return obj.__proto__;
    };
    var $__Object$defineProperty;
    (function() {
      try {
        if (!!Object.defineProperty({}, 'a', {})) {
          $__Object$defineProperty = Object.defineProperty;
        }
      } catch (e) {
        $__Object$defineProperty = function(obj, prop, opt) {
          try {
            obj[prop] = opt.value || opt.get.call(obj);
          } catch (e) {}
        };
      }
    }());
    $__Object$create = Object.create || function(o, props) {
      function F() {}
      F.prototype = o;
      if (typeof(props) === "object") {
        for (prop in props) {
          if (props.hasOwnProperty((prop))) {
            F[prop] = props[prop];
          }
        }
      }
      return new F();
    };
    (function() {
      var Promise = __global.Promise || require("when/es6-shim/Promise");
      if (__global.console)
        console.assert = console.assert || function() {};
      var indexOf = Array.prototype.indexOf || function(item) {
        for (var i = 0,
            thisLen = this.length; i < thisLen; i++) {
          if (this[i] === item) {
            return i;
          }
        }
        return -1;
      };
      var defineProperty = $__Object$defineProperty;
      function createLoaderLoad(object) {
        return {
          modules: {},
          loads: [],
          loaderObj: object
        };
      }
      function createLoad(name) {
        return {
          status: 'loading',
          name: name,
          linkSets: [],
          dependencies: [],
          metadata: {}
        };
      }
      function loadModule(loader, name, options) {
        return new Promise(asyncStartLoadPartwayThrough({
          step: options.address ? 'fetch' : 'locate',
          loader: loader,
          moduleName: name,
          moduleMetadata: options && options.metadata || {},
          moduleSource: options.source,
          moduleAddress: options.address
        }));
      }
      function requestLoad(loader, request, refererName, refererAddress) {
        return new Promise(function(resolve, reject) {
          resolve(loader.loaderObj.normalize(request, refererName, refererAddress));
        }).then(function(name) {
          var load;
          if (loader.modules[name]) {
            load = createLoad(name);
            load.status = 'linked';
            load.module = loader.modules[name];
            return load;
          }
          for (var i = 0,
              l = loader.loads.length; i < l; i++) {
            load = loader.loads[i];
            if (load.name != name)
              continue;
            console.assert(load.status == 'loading' || load.status == 'loaded', 'loading or loaded');
            return load;
          }
          load = createLoad(name);
          loader.loads.push(load);
          proceedToLocate(loader, load);
          return load;
        });
      }
      function proceedToLocate(loader, load) {
        proceedToFetch(loader, load, Promise.resolve().then(function() {
          return loader.loaderObj.locate({
            name: load.name,
            metadata: load.metadata
          });
        }));
      }
      function proceedToFetch(loader, load, p) {
        proceedToTranslate(loader, load, p.then(function(address) {
          if (load.status != 'loading')
            return ;
          load.address = address;
          return loader.loaderObj.fetch({
            name: load.name,
            metadata: load.metadata,
            address: address
          });
        }));
      }
      var anonCnt = 0;
      function proceedToTranslate(loader, load, p) {
        p.then(function(source) {
          if (load.status != 'loading')
            return ;
          return Promise.resolve(loader.loaderObj.translate({
            name: load.name,
            metadata: load.metadata,
            address: load.address,
            source: source
          })).then(function(source) {
            load.source = source;
            return loader.loaderObj.instantiate({
              name: load.name,
              metadata: load.metadata,
              address: load.address,
              source: source
            });
          }).then(function(instantiateResult) {
            if (instantiateResult === undefined) {
              load.address = load.address || '<Anonymous Module ' + ++anonCnt + '>';
              load.isDeclarative = true;
              return loader.loaderObj.transpile(load).then(function(transpiled) {
                var curSystem = __global.System;
                var curRegister = curSystem.register;
                curSystem.register = function(name, deps, declare) {
                  if (typeof name != 'string') {
                    declare = deps;
                    deps = name;
                  }
                  load.declare = declare;
                  load.depsList = deps;
                };
                __eval(transpiled, __global, load);
                curSystem.register = curRegister;
              });
            } else if (typeof instantiateResult == 'object') {
              load.depsList = instantiateResult.deps || [];
              load.execute = instantiateResult.execute;
              load.isDeclarative = false;
            } else
              throw TypeError('Invalid instantiate return value');
          }).then(function() {
            load.dependencies = [];
            var depsList = load.depsList;
            var loadPromises = [];
            for (var i = 0,
                l = depsList.length; i < l; i++)
              (function(request, index) {
                loadPromises.push(requestLoad(loader, request, load.name, load.address).then(function(depLoad) {
                  load.dependencies[index] = {
                    key: request,
                    value: depLoad.name
                  };
                  if (depLoad.status != 'linked') {
                    var linkSets = load.linkSets.concat([]);
                    for (var i = 0,
                        l = linkSets.length; i < l; i++)
                      addLoadToLinkSet(linkSets[i], depLoad);
                  }
                }));
              })(depsList[i], i);
            return Promise.all(loadPromises);
          }).then(function() {
            console.assert(load.status == 'loading', 'is loading');
            load.status = 'loaded';
            var linkSets = load.linkSets.concat([]);
            for (var i = 0,
                l = linkSets.length; i < l; i++)
              updateLinkSetOnLoad(linkSets[i], load);
          });
        })['catch'](function(exc) {
          load.status = 'failed';
          load.exception = exc;
          var linkSets = load.linkSets.concat([]);
          for (var i = 0,
              l = linkSets.length; i < l; i++) {
            linkSetFailed(linkSets[i], load, exc);
          }
          console.assert(load.linkSets.length == 0, 'linkSets not removed');
        });
      }
      function asyncStartLoadPartwayThrough(stepState) {
        return function(resolve, reject) {
          var loader = stepState.loader;
          var name = stepState.moduleName;
          var step = stepState.step;
          if (loader.modules[name])
            throw new TypeError('"' + name + '" already exists in the module table');
          var existingLoad;
          for (var i = 0,
              l = loader.loads.length; i < l; i++) {
            if (loader.loads[i].name == name) {
              existingLoad = loader.loads[i];
              if (step == 'translate' && !existingLoad.source) {
                existingLoad.address = stepState.moduleAddress;
                proceedToTranslate(loader, existingLoad, Promise.resolve(stepState.moduleSource));
              }
              return existingLoad.linkSets[0].done.then(function() {
                resolve(existingLoad);
              });
            }
          }
          var load = createLoad(name);
          load.metadata = stepState.moduleMetadata;
          var linkSet = createLinkSet(loader, load);
          loader.loads.push(load);
          resolve(linkSet.done);
          if (step == 'locate')
            proceedToLocate(loader, load);
          else if (step == 'fetch')
            proceedToFetch(loader, load, Promise.resolve(stepState.moduleAddress));
          else {
            console.assert(step == 'translate', 'translate step');
            load.address = stepState.moduleAddress;
            proceedToTranslate(loader, load, Promise.resolve(stepState.moduleSource));
          }
        };
      }
      function createLinkSet(loader, startingLoad) {
        var linkSet = {
          loader: loader,
          loads: [],
          startingLoad: startingLoad,
          loadingCount: 0
        };
        linkSet.done = new Promise(function(resolve, reject) {
          linkSet.resolve = resolve;
          linkSet.reject = reject;
        });
        addLoadToLinkSet(linkSet, startingLoad);
        return linkSet;
      }
      function addLoadToLinkSet(linkSet, load) {
        console.assert(load.status == 'loading' || load.status == 'loaded', 'loading or loaded on link set');
        for (var i = 0,
            l = linkSet.loads.length; i < l; i++)
          if (linkSet.loads[i] == load)
            return ;
        linkSet.loads.push(load);
        load.linkSets.push(linkSet);
        if (load.status != 'loaded') {
          linkSet.loadingCount++;
        }
        var loader = linkSet.loader;
        for (var i = 0,
            l = load.dependencies.length; i < l; i++) {
          var name = load.dependencies[i].value;
          if (loader.modules[name])
            continue;
          for (var j = 0,
              d = loader.loads.length; j < d; j++) {
            if (loader.loads[j].name != name)
              continue;
            addLoadToLinkSet(linkSet, loader.loads[j]);
            break;
          }
        }
      }
      function doLink(linkSet) {
        var error = false;
        try {
          link(linkSet, function(load, exc) {
            linkSetFailed(linkSet, load, exc);
            error = true;
          });
        } catch (e) {
          linkSetFailed(linkSet, null, e);
          error = true;
        }
        return error;
      }
      function updateLinkSetOnLoad(linkSet, load) {
        console.assert(load.status == 'loaded' || load.status == 'linked', 'loaded or linked');
        linkSet.loadingCount--;
        if (linkSet.loadingCount > 0)
          return ;
        var startingLoad = linkSet.startingLoad;
        if (linkSet.loader.loaderObj.execute === false) {
          var loads = [].concat(linkSet.loads);
          for (var i = 0,
              l = loads.length; i < l; i++) {
            var load = loads[i];
            load.module = !load.isDeclarative ? {module: _newModule({})} : {
              name: load.name,
              module: _newModule({}),
              evaluated: true
            };
            load.status = 'linked';
            finishLoad(linkSet.loader, load);
          }
          return linkSet.resolve(startingLoad);
        }
        var abrupt = doLink(linkSet);
        if (abrupt)
          return ;
        console.assert(linkSet.loads.length == 0, 'loads cleared');
        linkSet.resolve(startingLoad);
      }
      function linkSetFailed(linkSet, load, exc) {
        var loader = linkSet.loader;
        if (load && linkSet.loads[0].name != load.name)
          exc = addToError(exc, 'Error loading "' + load.name + '" from "' + linkSet.loads[0].name + '" at ' + (linkSet.loads[0].address || '<unknown>') + '\n');
        if (load)
          exc = addToError(exc, 'Error loading "' + load.name + '" at ' + (load.address || '<unknown>') + '\n');
        var loads = linkSet.loads.concat([]);
        for (var i = 0,
            l = loads.length; i < l; i++) {
          var load = loads[i];
          loader.loaderObj.failed = loader.loaderObj.failed || [];
          if (indexOf.call(loader.loaderObj.failed, load) == -1)
            loader.loaderObj.failed.push(load);
          var linkIndex = indexOf.call(load.linkSets, linkSet);
          console.assert(linkIndex != -1, 'link not present');
          load.linkSets.splice(linkIndex, 1);
          if (load.linkSets.length == 0) {
            var globalLoadsIndex = indexOf.call(linkSet.loader.loads, load);
            if (globalLoadsIndex != -1)
              linkSet.loader.loads.splice(globalLoadsIndex, 1);
          }
        }
        linkSet.reject(exc);
      }
      function finishLoad(loader, load) {
        if (loader.loaderObj.trace) {
          if (!loader.loaderObj.loads)
            loader.loaderObj.loads = {};
          var depMap = {};
          load.dependencies.forEach(function(dep) {
            depMap[dep.key] = dep.value;
          });
          loader.loaderObj.loads[load.name] = {
            name: load.name,
            deps: load.dependencies.map(function(dep) {
              return dep.key;
            }),
            depMap: depMap,
            address: load.address,
            metadata: load.metadata,
            source: load.source,
            kind: load.isDeclarative ? 'declarative' : 'dynamic'
          };
        }
        if (load.name) {
          console.assert(!loader.modules[load.name], 'load not in module table');
          loader.modules[load.name] = load.module;
        }
        var loadIndex = indexOf.call(loader.loads, load);
        if (loadIndex != -1)
          loader.loads.splice(loadIndex, 1);
        for (var i = 0,
            l = load.linkSets.length; i < l; i++) {
          loadIndex = indexOf.call(load.linkSets[i].loads, load);
          if (loadIndex != -1)
            load.linkSets[i].loads.splice(loadIndex, 1);
        }
        load.linkSets.splice(0, load.linkSets.length);
      }
      function buildLinkageGroups(load, loads, groups) {
        groups[load.groupIndex] = groups[load.groupIndex] || [];
        if (indexOf.call(groups[load.groupIndex], load) != -1)
          return ;
        groups[load.groupIndex].push(load);
        for (var i = 0,
            l = loads.length; i < l; i++) {
          var loadDep = loads[i];
          for (var j = 0; j < load.dependencies.length; j++) {
            if (loadDep.name == load.dependencies[j].value) {
              console.assert(loadDep.status == 'loaded', 'Load in linkSet not loaded!');
              var loadDepGroupIndex = load.groupIndex + (loadDep.isDeclarative != load.isDeclarative);
              if (loadDep.groupIndex === undefined || loadDep.groupIndex < loadDepGroupIndex) {
                if (loadDep.groupIndex !== undefined) {
                  groups[loadDep.groupIndex].splice(indexOf.call(groups[loadDep.groupIndex], loadDep), 1);
                  if (groups[loadDep.groupIndex].length == 0)
                    throw new TypeError("Mixed dependency cycle detected");
                }
                loadDep.groupIndex = loadDepGroupIndex;
              }
              buildLinkageGroups(loadDep, loads, groups);
            }
          }
        }
      }
      function doDynamicExecute(linkSet, load, linkError) {
        try {
          var module = load.execute();
        } catch (e) {
          linkError(load, e);
          return ;
        }
        if (!module || !(module instanceof Module))
          linkError(load, new TypeError('Execution must define a Module instance'));
        else
          return module;
      }
      function link(linkSet, linkError) {
        var loader = linkSet.loader;
        if (!linkSet.loads.length)
          return ;
        var groups = [];
        var startingLoad = linkSet.loads[0];
        startingLoad.groupIndex = 0;
        buildLinkageGroups(startingLoad, linkSet.loads, groups);
        var curGroupDeclarative = startingLoad.isDeclarative == groups.length % 2;
        for (var i = groups.length - 1; i >= 0; i--) {
          var group = groups[i];
          for (var j = 0; j < group.length; j++) {
            var load = group[j];
            if (curGroupDeclarative) {
              linkDeclarativeModule(load, linkSet.loads, loader);
            } else {
              var module = doDynamicExecute(linkSet, load, linkError);
              if (!module)
                return ;
              load.module = {
                name: load.name,
                module: module
              };
              load.status = 'linked';
            }
            finishLoad(loader, load);
          }
          curGroupDeclarative = !curGroupDeclarative;
        }
      }
      function getOrCreateModuleRecord(name, loader) {
        var moduleRecords = loader.moduleRecords;
        return moduleRecords[name] || (moduleRecords[name] = {
          name: name,
          dependencies: [],
          module: new Module(),
          importers: []
        });
      }
      function linkDeclarativeModule(load, loads, loader) {
        if (load.module)
          return ;
        var module = load.module = getOrCreateModuleRecord(load.name, loader);
        var moduleObj = load.module.module;
        var registryEntry = load.declare.call(__global, function(name, value) {
          module.locked = true;
          moduleObj[name] = value;
          for (var i = 0,
              l = module.importers.length; i < l; i++) {
            var importerModule = module.importers[i];
            if (!importerModule.locked) {
              var importerIndex = indexOf.call(importerModule.dependencies, module);
              importerModule.setters[importerIndex](moduleObj);
            }
          }
          module.locked = false;
          return value;
        });
        module.setters = registryEntry.setters;
        module.execute = registryEntry.execute;
        for (var i = 0,
            l = load.dependencies.length; i < l; i++) {
          var depName = load.dependencies[i].value;
          var depModule = loader.modules[depName];
          if (!depModule) {
            for (var j = 0; j < loads.length; j++) {
              if (loads[j].name != depName)
                continue;
              if (!loads[j].module) {
                linkDeclarativeModule(loads[j], loads, loader);
                depModule = loads[j].module;
              } else {
                depModule = getOrCreateModuleRecord(depName, loader);
              }
            }
          }
          if (depModule.importers) {
            module.dependencies.push(depModule);
            depModule.importers.push(module);
          } else {
            module.dependencies.push(null);
          }
          if (module.setters[i])
            module.setters[i](depModule.module);
        }
        load.status = 'linked';
      }
      function evaluateLoadedModule(loader, load) {
        console.assert(load.status == 'linked', 'is linked ' + load.name);
        doEnsureEvaluated(load.module, [], loader);
        return load.module.module;
      }
      function doExecute(module) {
        try {
          module.execute.call(__global);
        } catch (e) {
          return e;
        }
      }
      function doEnsureEvaluated(module, seen, loader) {
        var err = ensureEvaluated(module, seen, loader);
        if (err)
          throw err;
      }
      function ensureEvaluated(module, seen, loader) {
        if (module.evaluated || !module.dependencies)
          return ;
        seen.push(module);
        var deps = module.dependencies;
        var err;
        for (var i = 0,
            l = deps.length; i < l; i++) {
          var dep = deps[i];
          if (!dep)
            continue;
          if (indexOf.call(seen, dep) == -1) {
            err = ensureEvaluated(dep, seen, loader);
            if (err) {
              err = addToError(err, 'Error evaluating ' + dep.name + '\n');
              return err;
            }
          }
        }
        if (module.failed)
          return new Error('Module failed execution.');
        if (module.evaluated)
          return ;
        module.evaluated = true;
        err = doExecute(module);
        if (err) {
          module.failed = true;
        } else if (Object.preventExtensions) {
          Object.preventExtensions(module.module);
        }
        module.execute = undefined;
        return err;
      }
      function addToError(err, msg) {
        if (err instanceof Error)
          err.message = msg + err.message;
        else
          err = msg + err;
        return err;
      }
      function Loader(options) {
        if (typeof options != 'object')
          throw new TypeError('Options must be an object');
        if (options.normalize)
          this.normalize = options.normalize;
        if (options.locate)
          this.locate = options.locate;
        if (options.fetch)
          this.fetch = options.fetch;
        if (options.translate)
          this.translate = options.translate;
        if (options.instantiate)
          this.instantiate = options.instantiate;
        this._loader = {
          loaderObj: this,
          loads: [],
          modules: {},
          importPromises: {},
          moduleRecords: {}
        };
        defineProperty(this, 'global', {get: function() {
            return __global;
          }});
      }
      function Module() {}
      function createImportPromise(loader, name, promise) {
        var importPromises = loader._loader.importPromises;
        return importPromises[name] = promise.then(function(m) {
          importPromises[name] = undefined;
          return m;
        }, function(e) {
          importPromises[name] = undefined;
          throw e;
        });
      }
      Loader.prototype = {
        constructor: Loader,
        define: function(name, source, options) {
          if (this._loader.importPromises[name])
            throw new TypeError('Module is already loading.');
          return createImportPromise(this, name, new Promise(asyncStartLoadPartwayThrough({
            step: 'translate',
            loader: this._loader,
            moduleName: name,
            moduleMetadata: options && options.metadata || {},
            moduleSource: source,
            moduleAddress: options && options.address
          })));
        },
        'delete': function(name) {
          var loader = this._loader;
          delete loader.importPromises[name];
          delete loader.moduleRecords[name];
          return loader.modules[name] ? delete loader.modules[name] : false;
        },
        get: function(key) {
          if (!this._loader.modules[key])
            return ;
          doEnsureEvaluated(this._loader.modules[key], [], this);
          return this._loader.modules[key].module;
        },
        has: function(name) {
          return !!this._loader.modules[name];
        },
        'import': function(name, options) {
          var loaderObj = this;
          return Promise.resolve(loaderObj.normalize(name, options && options.name, options && options.address)).then(function(name) {
            var loader = loaderObj._loader;
            if (loader.modules[name]) {
              doEnsureEvaluated(loader.modules[name], [], loader._loader);
              return loader.modules[name].module;
            }
            return loader.importPromises[name] || createImportPromise(loaderObj, name, loadModule(loader, name, options || {}).then(function(load) {
              delete loader.importPromises[name];
              return evaluateLoadedModule(loader, load);
            }));
          });
        },
        load: function(name, options) {
          if (this._loader.modules[name]) {
            doEnsureEvaluated(this._loader.modules[name], [], this._loader);
            return Promise.resolve(this._loader.modules[name].module);
          }
          return this._loader.importPromises[name] || createImportPromise(this, name, loadModule(this._loader, name, {}));
        },
        module: function(source, options) {
          var load = createLoad();
          load.address = options && options.address;
          var linkSet = createLinkSet(this._loader, load);
          var sourcePromise = Promise.resolve(source);
          var loader = this._loader;
          var p = linkSet.done.then(function() {
            return evaluateLoadedModule(loader, load);
          });
          proceedToTranslate(loader, load, sourcePromise);
          return p;
        },
        newModule: function(obj) {
          if (typeof obj != 'object')
            throw new TypeError('Expected object');
          var m = new Module();
          var pNames;
          if (Object.getOwnPropertyNames && obj != null) {
            pNames = Object.getOwnPropertyNames(obj);
          } else {
            pNames = [];
            for (var key in obj)
              pNames.push(key);
          }
          for (var i = 0; i < pNames.length; i++)
            (function(key) {
              defineProperty(m, key, {
                configurable: false,
                enumerable: true,
                get: function() {
                  return obj[key];
                }
              });
            })(pNames[i]);
          if (Object.preventExtensions)
            Object.preventExtensions(m);
          return m;
        },
        set: function(name, module) {
          if (!(module instanceof Module))
            throw new TypeError('Loader.set(' + name + ', module) must be a module');
          this._loader.modules[name] = {module: module};
        },
        normalize: function(name, referrerName, referrerAddress) {
          return name;
        },
        locate: function(load) {
          return load.name;
        },
        fetch: function(load) {
          throw new TypeError('Fetch not implemented');
        },
        translate: function(load) {
          return load.source;
        },
        instantiate: function(load) {}
      };
      var _newModule = Loader.prototype.newModule;
      if (typeof exports === 'object')
        module.exports = Loader;
      __global.Reflect = __global.Reflect || {};
      __global.Reflect.Loader = __global.Reflect.Loader || Loader;
      __global.Reflect.global = __global.Reflect.global || __global;
      __global.LoaderPolyfill = Loader;
    })();
    (function(Loader) {
      var g = __global;
      function getTranspilerModule(loader, globalName) {
        return loader.newModule({
          'default': g[globalName],
          __useDefault: true
        });
      }
      Loader.prototype.transpiler = 'traceur';
      Loader.prototype.transpile = function(load) {
        var self = this;
        if (!self.transpilerHasRun) {
          if (g.traceur && !self.has('traceur'))
            self.set('traceur', getTranspilerModule(self, 'traceur'));
          if (g.babel && !self.has('babel'))
            self.set('babel', getTranspilerModule(self, 'babel'));
          self.transpilerHasRun = true;
        }
        return self['import'](self.transpiler).then(function(transpiler) {
          if (transpiler.__useDefault)
            transpiler = transpiler['default'];
          return 'var __moduleAddress = "' + load.address + '";' + (transpiler.Compiler ? traceurTranspile : babelTranspile).call(self, load, transpiler);
        });
      };
      Loader.prototype.instantiate = function(load) {
        var self = this;
        return Promise.resolve(self.normalize(self.transpiler)).then(function(transpilerNormalized) {
          if (load.name === transpilerNormalized) {
            return {
              deps: [],
              execute: function() {
                var curSystem = g.System;
                var curLoader = g.Reflect.Loader;
                __eval('(function(require,exports,module){' + load.source + '})();', g, load);
                g.System = curSystem;
                g.Reflect.Loader = curLoader;
                return getTranspilerModule(self, load.name);
              }
            };
          }
        });
      };
      function traceurTranspile(load, traceur) {
        var options = this.traceurOptions || {};
        options.modules = 'instantiate';
        options.script = false;
        options.sourceMaps = 'inline';
        options.filename = load.address;
        options.inputSourceMap = load.metadata.sourceMap;
        options.moduleName = false;
        var compiler = new traceur.Compiler(options);
        var source = doTraceurCompile(load.source, compiler, options.filename);
        return source + '\n//# sourceURL=' + load.address + '!eval';
      }
      function doTraceurCompile(source, compiler, filename) {
        try {
          return compiler.compile(source, filename);
        } catch (e) {
          throw e[0];
        }
      }
      function babelTranspile(load, babel) {
        var options = this.babelOptions || {};
        options.modules = 'system';
        options.sourceMap = 'inline';
        options.filename = load.address;
        options.code = true;
        options.ast = false;
        if (!options.blacklist)
          options.blacklist = ['react'];
        var source = babel.transform(load.source, options).code;
        return source + '\n//# sourceURL=' + load.address + '!eval';
      }
    })(__global.LoaderPolyfill);
    (function() {
      var isBrowser = typeof window != 'undefined' && typeof document != 'undefined';
      var isWindows = typeof process != 'undefined' && !!process.platform.match(/^win/);
      var Promise = __global.Promise || require("when/es6-shim/Promise");
      function parseURI(url) {
        var m = String(url).replace(/^\s+|\s+$/g, '').match(/^([^:\/?#]+:)?(\/\/(?:[^:@\/?#]*(?::[^:@\/?#]*)?@)?(([^:\/?#]*)(?::(\d*))?))?([^?#]*)(\?[^#]*)?(#[\s\S]*)?/);
        return (m ? {
          href: m[0] || '',
          protocol: m[1] || '',
          authority: m[2] || '',
          host: m[3] || '',
          hostname: m[4] || '',
          port: m[5] || '',
          pathname: m[6] || '',
          search: m[7] || '',
          hash: m[8] || ''
        } : null);
      }
      function removeDotSegments(input) {
        var output = [];
        input.replace(/^(\.\.?(\/|$))+/, '').replace(/\/(\.(\/|$))+/g, '/').replace(/\/\.\.$/, '/../').replace(/\/?[^\/]*/g, function(p) {
          if (p === '/..')
            output.pop();
          else
            output.push(p);
        });
        return output.join('').replace(/^\//, input.charAt(0) === '/' ? '/' : '');
      }
      function toAbsoluteURL(base, href) {
        if (isWindows)
          href = href.replace(/\\/g, '/');
        href = parseURI(href || '');
        base = parseURI(base || '');
        return !href || !base ? null : (href.protocol || base.protocol) + (href.protocol || href.authority ? href.authority : base.authority) + removeDotSegments(href.protocol || href.authority || href.pathname.charAt(0) === '/' ? href.pathname : (href.pathname ? ((base.authority && !base.pathname ? '/' : '') + base.pathname.slice(0, base.pathname.lastIndexOf('/') + 1) + href.pathname) : base.pathname)) + (href.protocol || href.authority || href.pathname ? href.search : (href.search || base.search)) + href.hash;
      }
      var fetchTextFromURL;
      if (typeof XMLHttpRequest != 'undefined') {
        fetchTextFromURL = function(url, fulfill, reject) {
          var xhr = new XMLHttpRequest();
          var sameDomain = true;
          var doTimeout = false;
          if (!('withCredentials' in xhr)) {
            var domainCheck = /^(\w+:)?\/\/([^\/]+)/.exec(url);
            if (domainCheck) {
              sameDomain = domainCheck[2] === window.location.host;
              if (domainCheck[1])
                sameDomain &= domainCheck[1] === window.location.protocol;
            }
          }
          if (!sameDomain && typeof XDomainRequest != 'undefined') {
            xhr = new XDomainRequest();
            xhr.onload = load;
            xhr.onerror = error;
            xhr.ontimeout = error;
            xhr.onprogress = function() {};
            xhr.timeout = 0;
            doTimeout = true;
          }
          function load() {
            fulfill(xhr.responseText);
          }
          function error() {
            reject(xhr.statusText + ': ' + url || 'XHR error');
          }
          xhr.onreadystatechange = function() {
            if (xhr.readyState === 4) {
              if (xhr.status === 200 || (xhr.status == 0 && xhr.responseText)) {
                load();
              } else {
                error();
              }
            }
          };
          xhr.open("GET", url, true);
          if (doTimeout)
            setTimeout(function() {
              xhr.send();
            }, 0);
          xhr.send(null);
        };
      } else if (typeof require != 'undefined') {
        var fs;
        fetchTextFromURL = function(url, fulfill, reject) {
          if (url.substr(0, 5) != 'file:')
            throw 'Only file URLs of the form file: allowed running in Node.';
          fs = fs || require("fs");
          url = url.substr(5);
          if (isWindows)
            url = url.replace(/\//g, '\\');
          return fs.readFile(url, function(err, data) {
            if (err)
              return reject(err);
            else
              fulfill(data + '');
          });
        };
      } else {
        throw new TypeError('No environment fetch API available.');
      }
      var SystemLoader = function($__super) {
        function SystemLoader(options) {
          $__super.call(this, options || {});
          if (typeof location != 'undefined' && location.href) {
            var href = __global.location.href.split('#')[0].split('?')[0];
            this.baseURL = href.substring(0, href.lastIndexOf('/') + 1);
          } else if (typeof process != 'undefined' && process.cwd) {
            this.baseURL = 'file:' + process.cwd() + '/';
            if (isWindows)
              this.baseURL = this.baseURL.replace(/\\/g, '/');
          } else {
            throw new TypeError('No environment baseURL');
          }
          this.paths = {'*': '*.js'};
        }
        SystemLoader.__proto__ = ($__super !== null ? $__super : Function.prototype);
        SystemLoader.prototype = $__Object$create(($__super !== null ? $__super.prototype : null));
        $__Object$defineProperty(SystemLoader.prototype, "constructor", {value: SystemLoader});
        $__Object$defineProperty(SystemLoader.prototype, "global", {
          get: function() {
            return __global;
          },
          enumerable: false
        });
        $__Object$defineProperty(SystemLoader.prototype, "strict", {
          get: function() {
            return true;
          },
          enumerable: false
        });
        $__Object$defineProperty(SystemLoader.prototype, "normalize", {
          value: function(name, parentName, parentAddress) {
            if (typeof name != 'string')
              throw new TypeError('Module name must be a string');
            var segments = name.split('/');
            if (segments.length == 0)
              throw new TypeError('No module name provided');
            var i = 0;
            var rel = false;
            var dotdots = 0;
            if (segments[0] == '.') {
              i++;
              if (i == segments.length)
                throw new TypeError('Illegal module name "' + name + '"');
              rel = true;
            } else {
              while (segments[i] == '..') {
                i++;
                if (i == segments.length)
                  throw new TypeError('Illegal module name "' + name + '"');
              }
              if (i)
                rel = true;
              dotdots = i;
            }
            for (var j = i; j < segments.length; j++) {
              var segment = segments[j];
              if (segment == '' || segment == '.' || segment == '..')
                throw new TypeError('Illegal module name "' + name + '"');
            }
            if (!rel)
              return name;
            var normalizedParts = [];
            var parentParts = (parentName || '').split('/');
            var normalizedLen = parentParts.length - 1 - dotdots;
            normalizedParts = normalizedParts.concat(parentParts.splice(0, parentParts.length - 1 - dotdots));
            normalizedParts = normalizedParts.concat(segments.splice(i, segments.length - i));
            return normalizedParts.join('/');
          },
          enumerable: false,
          writable: true
        });
        $__Object$defineProperty(SystemLoader.prototype, "locate", {
          value: function(load) {
            var name = load.name;
            var pathMatch = '',
                wildcard;
            for (var p in this.paths) {
              var pathParts = p.split('*');
              if (pathParts.length > 2)
                throw new TypeError('Only one wildcard in a path is permitted');
              if (pathParts.length == 1) {
                if (name == p && p.length > pathMatch.length) {
                  pathMatch = p;
                  break;
                }
              } else {
                if (name.substr(0, pathParts[0].length) == pathParts[0] && name.substr(name.length - pathParts[1].length) == pathParts[1]) {
                  pathMatch = p;
                  wildcard = name.substr(pathParts[0].length, name.length - pathParts[1].length - pathParts[0].length);
                }
              }
            }
            var outPath = this.paths[pathMatch];
            if (wildcard)
              outPath = outPath.replace('*', wildcard);
            if (isBrowser)
              outPath = outPath.replace(/#/g, '%23');
            return toAbsoluteURL(this.baseURL, outPath);
          },
          enumerable: false,
          writable: true
        });
        $__Object$defineProperty(SystemLoader.prototype, "fetch", {
          value: function(load) {
            var self = this;
            return new Promise(function(resolve, reject) {
              fetchTextFromURL(toAbsoluteURL(self.baseURL, load.address), function(source) {
                resolve(source);
              }, reject);
            });
          },
          enumerable: false,
          writable: true
        });
        return SystemLoader;
      }(__global.LoaderPolyfill);
      var System = new SystemLoader();
      if (typeof exports === 'object')
        module.exports = System;
      __global.System = System;
      if (isBrowser && document.getElementsByTagName) {
        var curScript = document.getElementsByTagName('script');
        curScript = curScript[curScript.length - 1];
        function completed() {
          document.removeEventListener("DOMContentLoaded", completed, false);
          window.removeEventListener("load", completed, false);
          ready();
        }
        function ready() {
          var scripts = document.getElementsByTagName('script');
          for (var i = 0; i < scripts.length; i++) {
            var script = scripts[i];
            if (script.type == 'module') {
              var source = script.innerHTML.substr(1);
              __global.System.module(source)['catch'](function(err) {
                setTimeout(function() {
                  throw err;
                });
              });
            }
          }
        }
        if (document.readyState === 'complete') {
          setTimeout(ready);
        } else if (document.addEventListener) {
          document.addEventListener('DOMContentLoaded', completed, false);
          window.addEventListener('load', completed, false);
        }
        if (curScript.getAttribute('data-init'))
          window[curScript.getAttribute('data-init')]();
      }
    })();
    function __eval(__source, __global, __load) {
      try {
        eval('(function() { var __moduleName = "' + (__load.name || '').replace('"', '\"') + '"; ' + __source + ' \n }).call(__global);');
      } catch (e) {
        if (e.name == 'SyntaxError' || e.name == 'TypeError')
          e.message = 'Evaluating ' + (__load.name || load.address) + '\n\t' + e.message;
        throw e;
      }
    }
  })(typeof window != 'undefined' ? window : (typeof global != 'undefined' ? global : self));
})(require("process"));
