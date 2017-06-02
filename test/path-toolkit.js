'use strict';

var chai        = require( 'chai' ),
    PathToolkit = require( '../dist/path-toolkit' ),
    expect      = chai.expect;

var ptk = new PathToolkit();

describe( 'PathToolkit', function(){
    var data, other;

    beforeEach(function(){
        data = {
            'undef': undefined,
            'propA': 'one',
            'propB': 'two',
            'propC': 'three',
            'foo.bar': 'FooBar',
            'blah': 'quoted',
            'John "Johnny" Doe': 'a name',
            'commonProp': 'common',
            'accounts': [
                /* 0 */ { 'ary': [9,8,7,6], 'common': 'A' },
                /* 1 */ {
                            'checking': {
                                'balance': 123.00,
                                'id': '12345',
                                'fn': function(){ return 'Function return value'; },
                                'fnArg': function(){ var args = Array.prototype.slice.call(arguments); return args.join(','); },
                                'repeat': 'propA'
                            },
                            'indices': [0,1,2,3],
                            'savX': 'X',
                            'savY': 'Y',
                            'savZ': 'Z',
                            'savAa': 'aa',
                            'savAb': 'ab',
                            'savAc': 'ac',
                            'savBa': 'ba',
                            'savBb': 'bb',
                            'savBc': 'bc',
                            'test1': 'propA',
                            'test2': 'propB',
                            'test3': 'propC',
                            'common': 'B'
                        },
                /* 2 */ function(){ return 1;},
                /* 3 */ { 'propAry': ['savBa', 'savBb'], 'common': 'C' }
            ],
            'people': [
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
                    name: 'Mary'
                }
            ]
        };
        
        other = {
            'x': 'propA',
            'y': 'propB',
            'z': 'checking'
        };

    });

    // it('should be the PathToolkit prototype', function () {
    //     expect(PathToolkit).to.be.a.function;
    // });

    // it('should provide instances with "new"', function () {
    //     expect(new PathToolkit()).to.be.an.instanceOf(PathToolkit);
    // });

    // xdescribe( 'disable', function(){
    // describe( 'get', function(){
    //     it( 'should get simple dot-separated properties', function(){
    //         var str = 'accounts.1.checking.id';
    //         expect(ptk.get(data, str)).to.equal(data.accounts[1].checking.id);
    //     } );

    //     it( 'should return undefined for paths that do not exist', function(){
    //         var str = 'xaccounts.1.checking.id';
    //         expect(ptk.get(data, str)).to.be.undefined;
    //         str = 'accounts.9.checking.id';
    //         expect(ptk.get(data, str)).to.be.undefined;
    //         str = 'accounts.1.checking.x';
    //         expect(ptk.get(data, str)).to.be.undefined;
    //         expect(ptk.get(undefined, str)).to.be.undefined;
    //     } );

    //     it( 'should be able to evaluate container and execute function', function(){
    //         var str = 'accounts{2()}checking.id';
    //         var tmp = data.accounts[2]();
    //         expect(ptk.get(data, str)).to.equal(data.accounts[tmp].checking.id);
    //     } );

    //     it( 'should execute function at tail of path', function(){
    //         var str = 'accounts{2()}checking.fn()';
    //         var tmp = data.accounts[2]();
    //         expect(ptk.get(data, str)).to.equal(data.accounts[tmp].checking.fn());
    //     } );
        
    //     it( 'should execute functions defined on base types', function(){
    //         var str = 'accounts.0.ary.sort()';
    //         expect(ptk.get(data, str)).to.equal(data.accounts[0].ary.sort());
    //     } );
        
    //     it( 'should allow wildcard * for array indices, resolved as array of values', function(){
    //         var str = 'accounts.0.ary.*';
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(data.accounts[0].ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(data.accounts[0].ary.join(','));
    //     } );
        
    //     it( 'should allow wildcards for properties, resulting array may be further evaluated', function(){
    //         var str = 'accounts.1.sav*.sort().0';
    //         var ary = [];
    //         for(var prop in data.accounts[1]){
    //             if (prop.substr(0,3) === 'sav'){
    //                 ary.push(data.accounts[1][prop]);
    //             }
    //         }
    //         expect(ptk.get(data, str)).to.equal(ary.sort()[0]);
    //     } );
        
    //     it( 'should allow interior wildcards', function(){
    //         var str = 'accounts.1.sav*a';
    //         var ary = [];
    //         for(var prop in data.accounts[1]){
    //             if (prop.substr(0,3) === 'sav' && prop.substr(4,1) === 'a'){
    //                 ary.push(data.accounts[1][prop]);
    //             }
    //         }
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
    //     } );

    //     it('should allow parent prefix to shift context within object', function () {
    //         var str = 'accounts.0.^1.checking.id';
    //         expect(ptk.get(data, str)).to.equal(data.accounts[1].checking.id);
    //     });
        
    //     it('should allow root prefix to shift context within object', function () {
    //         var str = 'accounts.0.~accounts.1.checking.id';
    //         expect(ptk.get(data, str)).to.equal(data.accounts[1].checking.id);
    //     });
        
    //     it('should allow multiple prefixes in one word', function () {
    //         var str = 'accounts.3.propAry.^^1.checking.id';
    //         expect(ptk.get(data, str)).to.equal(data.accounts[1].checking.id);
    //     });
        
    //     it('should allow container to leave outer context alone while processing internal prefix paths', function () {
    //         var str = 'accounts.1.{^3.propAry.0}';
    //         var str2 = 'accounts.1.{~accounts.3.propAry.0}';
    //         var val = data.accounts[1][ data.accounts[3].propAry[0] ];
    //         expect(ptk.get(data, str)).to.equal(val);
    //         expect(ptk.get(data, str2)).to.equal(val);
    //     });
        
    //     it('should allow parent prefix to shift context for all wildcard props', function () {
    //         var str = 'accounts.1.checking.^test*.sort()';
    //         var ary = [];
    //         for(var prop in data.accounts[1]){
    //             if (prop.substr(0,4) === 'test'){
    //                 ary.push(data.accounts[1][prop]);
    //             }
    //         }
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.sort().join(','));
    //     });

    //     it( 'should let collection separator create array of results', function(){
    //         var str = 'accounts.0.ary.0,2,3';
    //         var ary = [];
    //         ary.push(data.accounts[0].ary[0]);
    //         ary.push(data.accounts[0].ary[2]);
    //         ary.push(data.accounts[0].ary[3]);
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
    //     } );
        
    //     it('should continue to process collection results with further properties', function () {
    //         var str = 'accounts.1.test1,test2.0';
    //         expect(ptk.get(data, str)).to.equal(data.accounts[1].test1);
    //         var str2 = 'accounts.1.[test1],[test2].0';
    //         expect(ptk.get(data, str2)).to.equal(data.accounts[1].test1);
    //         var str3 = 'accounts.1."test1","test2".0';
    //         expect(ptk.get(data, str3)).to.equal(data.accounts[1].test1);
    //         var str4 = 'accounts.1.["test1"],["test2"].0';
    //         expect(ptk.get(data, str4)).to.equal(data.accounts[1].test1);
    //     });

    //     it( 'should allow wildcards inside group', function(){
    //         var str = 'accounts.1.savA*,savBa';
    //         var ary = [];
    //         ary.push([]); ary.push([]);
    //         for(var prop in data.accounts[1]){
    //             if (prop.substr(0,4) === 'savA'){
    //                 ary[0].push(data.accounts[1][prop]);
    //             }
    //         }
    //         ary[1].push(data.accounts[1].savBa);
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
    //     } );
        
    //     it( 'should allow container inside group', function(){
    //         var str = 'accounts.1.{^3.propAry.0},savA*';
    //         var ary = [];
    //         ary.push(data.accounts[1][ data.accounts[3].propAry[0] ]);
    //         ary.push([]);
    //         for(var prop in data.accounts[1]){
    //             if (prop.substr(0,4) === 'savA'){
    //                 ary[1].push(data.accounts[1][prop]);
    //             }
    //         }
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
    //     } );
        
    //     it( 'should allow path of only a comma group', function(){
    //         var str = '{accounts.1.test1},{accounts.1.test2}';
    //         var ary = [];
    //         ary.push(data[data.accounts[1].test1]);
    //         ary.push(data[data.accounts[1].test2]);
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
    //     } );

    //     it( 'should process placeholders', function(){
    //         var str = 'accounts.%1.%2';
    //         var key = 'savX';
    //         expect(ptk.get(data, str, 1, key)).to.equal(data.accounts[1].savX);
    //     });
        
    //     it( 'should call functions with placeholder arg', function(){
    //         var str = 'accounts.1.checking.fnArg(%1)';
    //         var key = 'hello';
    //         expect(ptk.get(data, str, key)).to.equal(data.accounts[1].checking.fnArg(key));
    //     });

    //     it( 'should call functions with multiple placeholder args', function(){
    //         var str = 'accounts.1.checking.fnArg(%1, %2)';
    //         var key = 'hello';
    //         expect(ptk.get(data, str, key, key)).to.equal(data.accounts[1].checking.fnArg(key, key));
    //     });

    //     it('should not cache placeholder values, only placeholders', function () {
    //         var str1 = 'accounts[0]ary.%1';
    //         expect(ptk.get(data, str1, 0)).to.equal(data.accounts[0].ary[0]);
    //         expect(ptk.get(data, str1, 1)).to.equal(data.accounts[0].ary[1]);
    //     });

    //     it('should get undefined as result', function () {
    //         var empty;
    //         var str = ''; // empty string
    //         expect(ptk.get(data, str)).to.be.undefined;
    //         str = 'accounts.1..checking.id'; // empty segment
    //         expect(ptk.get(data, str)).to.be.undefined;
    //         str = 'accounts{2()checking.id'; // mismatched container
    //         expect(ptk.get(data, str)).to.be.undefined;
    //         str = 'accounts.1.checking.id,missing'; // cannot get missing property inside collection
    //         expect(ptk.get(data, str)).to.be.undefined;
    //         str = 'accounts.undef'; // data object is undefined
    //         expect(ptk.get(empty, str)).to.be.undefined;
    //         str = {t: ['propA', undefined, 'propB']}; // undefined path segment in token list
    //         expect(ptk.get(data, str)).to.be.undefined;
    //         str = 'accounts.1.^^^^checking'; // too many parent refs
    //         expect(ptk.get(data, str)).to.be.undefined;
    //         str = 'accounts.%.checking.id'; // missing placeholder number
    //         expect(ptk.get(data, str, 1)).to.be.undefined;
    //         str = 'accounts.%1.checking.id'; // missing placeholder argument
    //         expect(ptk.get(data, str)).to.be.undefined;
    //         str = 'accounts.1.^missing.id'; // invalid property using modifier
    //         expect(ptk.get(data, str)).to.be.undefined;
    //     });

    //     it('should execute crazy function path', function () {
    //         var fn = function(){
    //             return function(){
    //                 return function(){
    //                     return 'abc';
    //                 }
    //             }
    //         }
    //         var str = '()()()'
    //         expect(ptk.get(fn, str)).to.equal('abc');
    //     });

    //     it('should handle plain property container, treats contents as property name', function () {
    //         var str1 = 'accounts[0]ary[0]';
    //         expect(ptk.get(data, str1)).to.equal(data.accounts[0].ary[0]);
    //         var str2 = '["foo.bar"]';
    //         expect(ptk.get(data, str2)).to.equal(data['foo.bar']);
    //         var str3 = 'accounts.[0].ary[0]';
    //         expect(ptk.get(data, str3)).to.equal(data.accounts[0].ary[0]);
    //     });

    //     it('should handle quotes inside plain property container, treats contents as property name', function () {
    //         var str1 = 'accounts[\'0\']ary["0"]';
    //         expect(ptk.get(data, str1)).to.equal(data.accounts[0].ary[0]);
    //         var str2 = '["foo.bar"]';
    //         expect(ptk.get(data, str2)).to.equal(data['foo.bar']);
    //         var str3 = '[\'foo.bar\']';
    //         expect(ptk.get(data, str3)).to.equal(data['foo.bar']);
    //     });

    //     it('should treat quotes as normal characters when not inside property container', function () {
    //         var str1 = '"blah"';
    //         expect(ptk.get(data, str1)).to.equal(data['blah']);
    //         var str2 = '[\'John "Johnny" Doe\']';
    //         expect(ptk.get(data, str2)).to.equal(data['John "Johnny" Doe']);
    //     });

    //     it( 'should process context placeholders', function(){
    //         var str = '{@1.x}';
    //         expect(ptk.get(data, str, other)).to.equal(data[other.x]);
    //     });
        
    //     it( 'should switch processing from base data to new object if context placeholder is used as path segment', function(){
    //         var str = 'accounts.1.@1.x';
    //         expect(ptk.get(data, str, other)).to.equal(other.x);
    //     });
        
    //     it( 'should preserve use of context stack when handling context placeholders', function(){
    //         var str = 'accounts.1{@1.z}id';
    //         var fn = function(x){ return x; }
    //         var str2 = 'accounts.1{@1(%2)}id';
    //         expect(ptk.get(data, str, other)).to.equal(data.accounts[1][other.z].id);
    //         expect(ptk.get(data, str2, fn, 'checking')).to.equal(data.accounts[1][fn('checking')].id);
    //     });

    //     it( 'should allow plain property array notation', function(){
    //         var str = 'accounts.0.ary[0],[1]';
    //         var ary = [];
    //         ary.push(data.accounts[0].ary[0]);
    //         ary.push(data.accounts[0].ary[1]);
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));

    //         var str2 = 'accounts.1["test1"],["test2"]';
    //         var ary2 = [];
    //         ary2.push(data.accounts[1].test1);
    //         ary2.push(data.accounts[1].test2);
    //         expect(ptk.get(data, str2)).to.be.an.array;
    //         expect(ptk.get(data, str2).length).to.equal(ary2.length);
    //         expect(ptk.get(data, str2).join(',')).to.equal(ary2.join(','));

    //         var str3 = 'accounts.1[test1],[test2]';
    //         var ary3 = [];
    //         ary3.push(data.accounts[1].test1);
    //         ary3.push(data.accounts[1].test2);
    //         expect(ptk.get(data, str3)).to.be.an.array;
    //         expect(ptk.get(data, str3).length).to.equal(ary3.length);
    //         expect(ptk.get(data, str3).join(',')).to.equal(ary3.join(','));
    //     } );
        
    //     it('should support "each" operator to return array', function(){
    //         var str = 'accounts.0,1,3<common';
    //         var ary = [data.accounts[0].common, data.accounts[1].common, data.accounts[3].common];
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
    //     });
        
    //     it('should support "each" operator to return array', function(){
    //         var str = 'accounts.0,1,3<common';
    //         var ary = [data.accounts[0].common, data.accounts[1].common, data.accounts[3].common];
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
    //     });
        
    //     it('should support "each" operator to execute function on each array elememt, return array of results', function(){
    //         var str = 'accounts.0,1,3<common<toLowerCase()';
    //         var ary = [data.accounts[0].common.toLowerCase(), data.accounts[1].common.toLowerCase(), data.accounts[3].common.toLowerCase()];
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
            
    //         var str2 = 'accounts.0,1,3<common<concat(@1)';
    //         var ary2 = [data.accounts[0].common.concat("X"), data.accounts[1].common.concat("X"), data.accounts[3].common.concat("X")];
    //         expect(ptk.get(data, str2, 'X')).to.be.an.array;
    //         expect(ptk.get(data, str2, 'X').length).to.equal(ary2.length);
    //         expect(ptk.get(data, str2, 'X').join(',')).to.equal(ary2.join(','));
            
    //         var str2 = 'accounts.0,1,3<common<@1(@2)';
    //         var ary2 = [data.accounts[0].common.concat("X"), data.accounts[1].common.concat("X"), data.accounts[3].common.concat("X")];
    //         expect(ptk.get(data, str2, String.prototype.concat, 'X')).to.be.an.array;
    //         expect(ptk.get(data, str2, String.prototype.concat, 'X').length).to.equal(ary2.length);
    //         expect(ptk.get(data, str2, String.prototype.concat, 'X').join(',')).to.equal(ary2.join(','));
    //     });
        
    //     it('should support "each" operator with bracket properties', function(){
    //         var str = 'accounts.[0],[1],[3]<[common]<toLowerCase()';
    //         var ary = [data.accounts[0].common.toLowerCase(), data.accounts[1].common.toLowerCase(), data.accounts[3].common.toLowerCase()];
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
            
    //         var str2 = 'accounts.0,1,3<["common"]<toLowerCase()';
    //         expect(ptk.get(data, str2)).to.be.an.array;
    //         expect(ptk.get(data, str2).length).to.equal(ary.length);
    //         expect(ptk.get(data, str2).join(',')).to.equal(ary.join(','));
    //     });
        
    //     it('should support "each" operator with wildcard properties', function(){
    //         var str = 'accounts.0,1<comm*';
    //         var ary = [data.accounts[0].common, data.accounts[1].common];
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
    //     });
        
    //     it('should support "each" operator with eval properties', function(){
    //         var str = 'accounts.0,1,3<{~commonProp}';
    //         var ary = [data.accounts[0].common, data.accounts[1].common, data.accounts[3].common];
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str).join(',')).to.equal(ary.join(','));
    //     });
        
    //     it('should support "each" for collection maps of collections', function(){
    //         var str = 'people.*<id,name';
    //         var ary = [];
    //         ary.push([data.people[0].id, data.people[0].name]);
    //         ary.push([data.people[1].id, data.people[1].name]);
    //         ary.push([data.people[2].id, data.people[2].name]);
    //         expect(ptk.get(data, str)).to.be.an.array;
    //         expect(ptk.get(data, str).length).to.equal(ary.length);
    //         expect(ptk.get(data, str)[0]).to.be.an.array;
    //         expect(ptk.get(data, str)[0].length).to.equal(ary[0].length);
    //         expect(ptk.get(data, str)[0].join(',')).to.equal(ary[0].join(','));
    //         expect(ptk.get(data, str)[1].join(',')).to.equal(ary[1].join(','));
    //         expect(ptk.get(data, str)[2].join(',')).to.equal(ary[2].join(','));
    //     });
    // });

    // describe( 'set', function(){

    //     it( 'should set simple dot-separated properties', function(){
    //         var str = 'accounts.1.checking.id';
    //         var newVal = 'new';
    //         ptk.set(data, str, newVal);
    //         expect(ptk.get(data, str)).to.equal(newVal);
    //     } );

    //     it( 'should return true if set was successful', function(){
    //         var str = 'accounts.1.checking.id';
    //         var newVal = 'new';
    //         expect(ptk.set(data, str, newVal)).to.be.true;
    //         expect(ptk.get(data, str)).to.equal(newVal);
    //     } );

    //     it( 'should return false if set was not successful', function(){
    //         var str = 'accounts.1.checking.newProperty';
    //         var strBad = 'accounts.1.badProperty.newProperty';
    //         var newVal = 'new';
    //         expect(ptk.set(data, str, newVal)).to.be.true;
    //         expect(ptk.get(data, str)).to.equal(newVal);
    //         expect(ptk.set(data, strBad, newVal)).to.be.false;
    //     } );

    //     it( 'should set value to all entries in array for wildcard path', function(){
    //         var str = 'accounts.1.sav*';
    //         var newVal = 'new';
    //         expect(ptk.set(data, str, newVal)).to.be.true;

    //         var ary = [];
    //         var testAry = [];
    //         for(var prop in data.accounts[1]){
    //             if (prop.substr(0,3) === 'sav'){
    //                 ary.push(data.accounts[1][prop]);
    //                 testAry.push(newVal);
    //             }
    //         }
    //         expect(ary.join(',')).to.equal(testAry.join(','));
    //     });

    //     it( 'should set value to all entries in simple comma group', function(){
    //         var str = 'accounts.1.savX,savY';
    //         var newVal = 'new';
    //         expect(ptk.set(data, str, newVal)).to.be.true;
    //         expect(data.accounts[1].savX).to.equal(newVal);
    //         expect(data.accounts[1].savY).to.equal(newVal);
    //     });

    //     it( 'should set value to all entries in comma group mixing properties and wildcards', function(){
    //         var str = 'accounts.1.savX,savY,savA*';
    //         var newVal = 'new';
    //         var oldNotAry = [];
    //         var prop;
    //         for(prop in data.accounts[1]){
    //             if (prop !== 'savX' && prop !== 'savY' && prop.substr(0,4) !== 'savA'){
    //                 oldNotAry.push(data.accounts[1][prop]);
    //             }
    //         }
    //         expect(ptk.set(data, str, newVal)).to.be.true;

    //         var ary = [];
    //         var testAry = [];
    //         var notAry = [];
    //         for(prop in data.accounts[1]){
    //             if (prop.substr(0,4) === 'savA'){
    //                 ary.push(data.accounts[1][prop]);
    //                 testAry.push(newVal);
    //             }
    //             else if (prop !== 'savX' && prop !== 'savY') {
    //                 notAry.push(data.accounts[1][prop]);
    //             }
    //         }
    //         expect(data.accounts[1].savX).to.equal(newVal);
    //         expect(data.accounts[1].savY).to.equal(newVal);
    //         expect(notAry.join(',')).to.equal(oldNotAry.join(','));
    //     });

    //     it('should allow parent prefix to shift context for all wildcard props', function () {
    //         var str = 'accounts.1.checking.^test*';
    //         var newVal = 'new';
    //         var ary = [];
    //         var resultAry = [];

    //         ptk.set(data, str, newVal);
    //         for(var prop in data.accounts[1]){
    //             if (prop.substr(0,4) === 'test'){
    //                 ary.push(data.accounts[1][prop]);
    //                 resultAry.push('new');
    //             }
    //         }
    //         expect(ary.sort().join(',')).to.equal(resultAry.sort().join(','));
    //     });

    //     it( 'should set value to all entries in comma group of containers', function(){
    //         var str = '{accounts.1.test1},{accounts.1.test2}';
    //         var newVal = 'new';
    //         expect(ptk.set(data, str, newVal)).to.be.true;
    //         expect(data[data.accounts[1].test1]).to.equal(newVal);
    //         expect(data[data.accounts[1].test2]).to.equal(newVal);
    //         expect(data[data.accounts[1].test3]).to.not.equal(newVal);
    //     });

    //     it('should allow container to leave outer context alone while processing internal prefix paths', function () {
    //         var str = 'accounts.1.{^3.propAry.0}';
    //         var str2 = 'accounts.1.{~accounts.3.propAry.0}';
    //         var newVal = 'new';
    //         var newVal2 = 'new2';
    //         ptk.set(data, str, newVal);
    //         expect(data.accounts[1][ data.accounts[3].propAry[0] ]).to.equal(newVal);
    //         ptk.set(data, str2, newVal2);
    //         expect(data.accounts[1][ data.accounts[3].propAry[0] ]).to.equal(newVal2);
    //     });
        
    //     it('should allow last segment to process prefix paths and set value', function () {
    //         var str = 'accounts.1.checking.^savX';
    //         var newVal = 'new';
    //         ptk.set(data, str, newVal);
    //         expect(data.accounts[1].savX).to.equal(newVal);
    //     });

    //     it( 'should process placeholders when setting new value', function(){
    //         var str = 'accounts.1.%1.id';
    //         var key = 'checking'
    //         var newVal = 'new';
    //         ptk.set(data, str, newVal, key);
    //         expect(ptk.get(data, str, key)).to.equal(newVal);
    //         expect(data.accounts[1].checking.id).to.equal(newVal);
    //     } );

    //     it( 'should process pre-processed tokens for both simple and complex paths', function(){
    //         var tokens1 = {t:['accounts','1','checking','id']};
    //         var newVal = 'new';
    //         ptk.set(data, tokens1, newVal);
    //         expect(ptk.get(data, tokens1)).to.equal(newVal);
    //         expect(data.accounts[1].checking.id).to.equal(newVal);
    //         var key = 'checking';
    //         var tokens2 = {"t":["accounts","1",{"w":"1","mods":{"has":true,"placeholder":1}},"id"]};
    //         var newVal2 = 'new2';
    //         ptk.set(data, tokens2, newVal2, key);
    //         expect(ptk.get(data, tokens2, key)).to.equal(newVal2);
    //         expect(data.accounts[1].checking.id).to.equal(newVal2);
    //     } );
        
    //     it('should support "each" operator set values in array', function(){
    //         var str = 'accounts.0,1,3<common';
    //         var result = ptk.set(data, str, 'NEW');
    //         var ary = [data.accounts[0].common, data.accounts[1].common, data.accounts[3].common];
    //         expect(result).to.be.true;
    //         expect(ary.join(',')).to.equal('NEW,NEW,NEW');
    //     });
        
    //     it('should support "each" operator with wildcard properties', function(){
    //         var str = 'accounts.0,1<comm*';
    //         var result = ptk.set(data, str, 'BETTER');
    //         var ary = [data.accounts[0].common, data.accounts[1].common];
    //         expect(result).to.be.true;
    //         expect(ary.join(',')).to.equal('BETTER,BETTER');
    //     });
        
    //     it('should support "each" operator with eval properties', function(){
    //         var str = 'accounts.0,1,3<{~commonProp}';
    //         var result = ptk.set(data, str, 'NEW');
    //         var ary = [data.accounts[0].common, data.accounts[1].common, data.accounts[3].common];
    //         expect(result).to.be.true;
    //         expect(ary.join(',')).to.equal('NEW,NEW,NEW');
    //     });
    // });

    // describe( 'find', function(){
    //     it( 'should return a valid path to the value if present in the root object', function(){
    //         var val = data.accounts[1].test2;
    //         expect(ptk.find(data, val)).to.equal('accounts.1.test2');
    //         expect(ptk.get(data, ptk.find(data, val))).to.equal(val);
    //     });

    //     it( 'should be identity: get(find) and find(get)', function(){
    //         var val = data.accounts[1].test2;
    //         var str = 'accounts.1.test2';
    //         expect(ptk.get(data, ptk.find(data, val))).to.equal(val);
    //         expect(ptk.find(data, ptk.get(data, str))).to.equal(str);
    //     });

    //     it('should quote path segments with special characters', function () {
    //         var val = 'FooBar';
    //         expect(ptk.find(data, val)).to.equal("'foo.bar'");
    //         expect(ptk.get(data, ptk.find(data, val))).to.equal(val);
    //     });

    //     it( 'should return undefined if no path found', function(){
    //         var val = 12345;
    //         expect(ptk.find(data, val)).to.be.undefined;
    //     });

    //     it( 'should return undefined for empty data object', function(){
    //         var val = 12345;
    //         expect(ptk.find(null, val)).to.be.undefined;
    //         expect(ptk.find(undefined, val)).to.be.undefined;
    //     });

    //     it( 'should return one valid path if "one" option is set or if not specified', function(){
    //         var val = data.accounts[1].test2;
    //         expect(ptk.find(data, val)).to.be.a.string;
    //         expect(ptk.find(data, val, 'one')).to.be.a.string;
    //     });

    //     it( 'should return all valid path if "many" option is set', function(){
    //         var val = data.accounts[1].test1;
    //         expect(ptk.find(data, val, 'many')).to.be.an.array;
    //         expect(ptk.find(data, val, 'many').sort().join(',')).to.equal('accounts.1.checking.repeat,accounts.1.test1');
    //     });

    // });

    // describe('getTokens', function () {
    //     it('should return a token array from a string path', function () {
    //         var str = 'accounts.1.test2';
    //         var tokens = ptk.getTokens(str);
    //         expect(tokens).to.be.an.object;
    //         expect(tokens.t).to.be.an.array;
    //         expect(tokens.t.length).to.equal(3);
    //     });
    //     it('should return a token array from an escaped string path', function () {
    //         var str = 'f\\(oo\\).b\\.ar';
    //         var tokens = ptk.getTokens(str);
    //         expect(tokens).to.be.an.object;
    //         expect(tokens.t).to.be.an.array;
    //         expect(tokens.t.length).to.equal(2);
    //         expect(tokens.t.join('|')).to.equal('f(oo)|b.ar');
    //     });
    //     it('should return undefined if path ends in an escape character', function () {
    //         var str = 'foo.bar\\';
    //         expect(ptk.getTokens(str)).to.be.undefined;
    //     });
    // });

    // describe('isValid', function(){
    //     it('should correctly identify valid and invalid paths', function(){
    //         expect(ptk.isValid('accounts.1.test2')).to.be.true;
    //         expect(ptk.isValid('accounts.{1.test2')).to.be.false;
    //         expect(ptk.isValid('accounts(.test2')).to.be.false;
    //         expect(ptk.isValid('accounts{{a()},{b.c,d}}')).to.be.true;
    //         expect(ptk.isValid('accounts{{a(),{b.c,d}}')).to.be.false;
    //     });
    // });

    // describe('escape', function(){
    //     it('should escape special characters', function(){
    //         expect(ptk.escape('accounts.1.test2')).to.equal('accounts\\.1\\.test2');
    //         expect(ptk.escape('accounts{{a()},{b.c,d}}')).to.equal('accounts\\{\\{a\\(\\)\\}\\,\\{b\\.c\\,d\\}\\}');
    //     });
    // });
    
    // describe('setOptions and resetOptions', function(){
    //     it('requires setCacheOn/Off to work for testing', function(){
    //         var path = 'x.y.z';
    //         var tokens1 = ptk.getTokens(path);
    //         var tokens2 = ptk.getTokens(path);
    //         expect(tokens1.t === tokens2.t).to.be.true;
    //         ptk.setCacheOff();
    //         var tokens3 = ptk.getTokens(path);
    //         expect(tokens1.t === tokens3.t).to.be.false;
    //         ptk.setCacheOn();
    //         var tokens4 = ptk.getTokens(path);
    //         expect(tokens1.t === tokens4.t).to.be.true;
    //     });
    //     it('requires setCache(true/false) to work for testing', function(){
    //         var path = 'x.y.z';
    //         var tokens1 = ptk.getTokens(path);
    //         var tokens2 = ptk.getTokens(path);
    //         expect(tokens1.t === tokens2.t).to.be.true;
    //         ptk.setCache('off');
    //         var tokens3 = ptk.getTokens(path);
    //         expect(tokens1.t === tokens3.t).to.be.false;
    //         ptk.setCache('yes');
    //         var tokens4 = ptk.getTokens(path);
    //         expect(tokens1.t === tokens4.t).to.be.true;
    //     });
    //     it('requires setOptions and resetOptions for future unit tests', function(){
    //         expect(ptk.getTokens('a.b.c').t.length).to.equal(3);
    //         ptk.setOptions({
    //             'separators': {
    //                 '#': {
    //                     'exec': 'property'
    //                 }
    //             }
    //         });
    //         expect(ptk.getTokens('a.b.c').t.length).to.equal(1);
    //         expect(ptk.getTokens('a#b#c').t.length).to.equal(3);
            
    //         ptk.resetOptions();
    //         expect(ptk.getTokens('a.b.c').t.length).to.equal(3);
    //         expect(ptk.getTokens('a#b#c').t.length).to.equal(1);
    //     });
    // });
    
    // describe('setOptions', function(){
    //     afterEach(function(){
    //         ptk.resetOptions();
    //     });
        
    //     it('should allow special characters to be re-defined', function () {
    //         ptk.setOptions({
    //             'cache': true,
    //             'prefixes': {
    //                 '<': {
    //                     'exec': 'parent'
    //                 },
    //                 '~': {
    //                     'exec': 'root'
    //                 },
    //                 '%': {
    //                     'exec': 'placeholder'
    //                 }
    //             },
    //             'separators': {
    //                 '!': {
    //                     'exec': 'property'
    //                 },
    //                 ';': {
    //                     'exec': 'collection'
    //                 }
    //             },
    //             'containers': {
    //                 '(': {
    //                     'closer': ')',
    //                     'exec': 'call'
    //                 },
    //                 '[': {
    //                     'closer': ']',
    //                     'exec': 'evalProperty'
    //                 },
    //                 '{': {
    //                     'closer': '}',
    //                     'exec': 'property'
    //                 }
    //             }
    //         });
    //         var str1 = 'accounts!1!test2';
    //         var val1 = data.accounts[1].test2;
    //         expect(ptk.get(data, str1)).to.equal(val1);
    //         var str2 = 'accounts[2()]checking!id';
    //         var val2 = data.accounts[2]();
    //         expect(ptk.get(data, str2)).to.equal(data.accounts[val2].checking.id);
    //         var str3 = 'accounts!0!<1!checking!id';
    //         expect(ptk.get(data, str3)).to.equal(data.accounts[1].checking.id);
    //         var str4 = 'accounts!0!ary!0;2';
    //         var ary4 = [];
    //         ary4.push(data.accounts[0].ary[0]);
    //         ary4.push(data.accounts[0].ary[2]);
    //         expect(ptk.get(data, str4)).to.be.an.array;
    //         expect(ptk.get(data, str4).length).to.equal(ary4.length);
    //         expect(ptk.get(data, str4).join(',')).to.equal(ary4.join(','));
    //     });
    // });
    
    // describe('options', function(){
    //     afterEach(function(){
    //         ptk.resetOptions();
    //     });

    //     describe('force', function(){
    //        it('should create intermediate properties if they don\'t exist', function(){
    //             var str = 'accounts.1.newPropA.newPropB';
    //             var newVal = 'new';
    //             var result;
    //             ptk.setOptions({force:true});
                
    //             result = ptk.set(data, str, newVal);
    //             expect(ptk.get(data, str)).to.equal(newVal);
    //             expect(data.accounts[1].newPropA.newPropB).to.equal(newVal);
    //             expect(result).to.be.true;
                
    //             str = 'accounts.1["new.PropC"]newPropD';
    //             var newVal2 = 'new2';
    //             result = ptk.set(data, str, newVal2);
    //             expect(ptk.get(data, str)).to.equal(newVal2);
    //             expect(data.accounts[1]['new.PropC'].newPropD).to.equal(newVal2);
    //             expect(result).to.be.true;
                
    //             var tokens = {t:['accounts','1','newPropE','newPropF']};
    //             var newVal3 = 'new3';
    //             result = ptk.set(data, tokens, newVal3);
    //             expect(ptk.get(data, tokens)).to.equal(newVal3);
    //             expect(data.accounts[1].newPropE.newPropF).to.equal(newVal3);
    //             expect(result).to.be.true;
    //        });
           
    //        it('should work with setForceOn()', function(){
    //             var str = 'accounts.1.newPropA.newPropB';
    //             var newVal = 'new';
    //             var result;
    //             ptk.setForceOn();
    //             result = ptk.set(data, str, newVal);
    //             expect(ptk.get(data, str)).to.equal(newVal);
    //             expect(data.accounts[1].newPropA.newPropB).to.equal(newVal);
    //             expect(result).to.be.true;
                
    //             str = 'accounts.1["new.PropA"]newPropB';
    //             result = ptk.set(data, str, newVal);
    //             expect(ptk.get(data, str)).to.equal(newVal);
    //             expect(data.accounts[1]['new.PropA'].newPropB).to.equal(newVal);
    //             expect(result).to.be.true;
    //        });
           
    //        it('should work with setForce(true)', function(){
    //             var str = 'accounts.1.newPropA.newPropB';
    //             var newVal = 'new';
    //             var result;
    //             ptk.setForce(true);
    //             result = ptk.set(data, str, newVal);
    //             expect(ptk.get(data, str)).to.equal(newVal);
    //             expect(data.accounts[1].newPropA.newPropB).to.equal(newVal);
    //             expect(result).to.be.true;
                
    //             str = 'accounts.1["new.PropA"]newPropB';
    //             result = ptk.set(data, str, newVal);
    //             expect(ptk.get(data, str)).to.equal(newVal);
    //             expect(data.accounts[1]['new.PropA'].newPropB).to.equal(newVal);
    //             expect(result).to.be.true;
    //        });
           
    //        it('should NOT create intermediate properties if force is off', function(){
    //             var str = 'accounts.1.newPropA.newPropB';
    //             var newVal = 'new';
    //             var result;
    //             ptk.setForceOff();
    //             result = ptk.set(data, str, newVal);
    //             expect(ptk.get(data, str)).to.be.undefined;
    //             expect(result).to.be.false;
    //        });
           
    //     });
        
    //     describe('simple', function(){
    //        it('"true" should still process simple dot-separated string paths', function(){
    //             var str = 'accounts.1.checking.id';
    //             var val = data.accounts[1].checking.id;
    //             ptk.setOptions({simple:true});
                
    //             expect(ptk.get(data, str)).to.equal(val);
    //        });
           
    //        it('"true" should disable use of other special characters', function(){
    //             var str = 'accounts.1.checking.id';
    //             var val = data.accounts[1].checking.id;
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.equal(val);
                
    //             ptk.setOptions({simple:true});
                
    //             expect(ptk.get(data, 'accounts.1.checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.be.undefined;
    //        });
           
    //        it('should work with setSimpleOn()', function(){
    //             var str = 'accounts.1.checking.id';
    //             var val = data.accounts[1].checking.id;
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.equal(val);
                
    //             ptk.setSimpleOn();
                
    //             expect(ptk.get(data, 'accounts.1.checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.be.undefined;
    //        });
           
    //        it('should be able to declare a different separator with setSimpleOn(separator)', function(){
    //             var str = 'accounts.1.checking.id';
    //             var val = data.accounts[1].checking.id;
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.equal(val);
                
    //             ptk.setSimpleOn(',');
                
    //             expect(ptk.get(data, 'accounts,1,checking,id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.be.undefined;
    //        });
           
    //        it('should work with setSimple(true)', function(){
    //             var str = 'accounts.1.checking.id';
    //             var val = data.accounts[1].checking.id;
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.equal(val);
                
    //             ptk.setSimple(true);
                
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.be.undefined;
    //        });
           
    //        it('should be able to declare a different separator with setSimple(true, separator)', function(){
    //             var str = 'accounts.1.checking.id';
    //             var val = data.accounts[1].checking.id;
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.equal(val);
                
    //             ptk.setSimple(true, ',');
                
    //             expect(ptk.get(data, 'accounts,1,checking,id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.be.undefined;
    //        });
           
    //        it('"false" should restore full suite of path features', function(){
    //             var str = 'accounts.1.checking.id';
    //             var val = data.accounts[1].checking.id;
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.equal(val);
                
    //             ptk.setSimpleOn();
                
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.be.undefined;
                
    //             ptk.setSimpleOff();
                
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.equal(val);
                
    //             ptk.setSimple(true);
                
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.be.undefined;
                
    //             ptk.setSimple(false);
                
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.equal(val);
                
    //             ptk.setOptions({simple:true});
                
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.be.undefined;
                
    //             ptk.setOptions({simple:false});
                
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.equal(val);
    //             expect(ptk.get(data, 'accounts.%1.checking.id', '1')).to.equal(val);
    //        });
    //     });
        
    //     describe('separators', function(){
    //         it('should allow all separators to be changed at once', function(){
    //             ptk.setOptions({
    //                 separators: {
    //                     '#': { exec: 'property' }
    //                 }
    //             });
    //             expect(ptk.getTokens('a.b.c').t.length).to.equal(1);
    //             expect(ptk.getTokens('a#b#c').t.length).to.equal(3);
    //             expect(ptk.getTokens('a,b,c').t.length).to.equal(1);
    //         });
            
    //         it('should modify individual separators with setSeparatorProperty', function(){
    //             ptk.setSeparatorProperty('#');
    //             expect(ptk.getTokens('a.b.c').t.length).to.equal(1);
    //             expect(ptk.getTokens('a#b#c').t.length).to.equal(3);
    //             expect(ptk.getTokens('a,b,c').t.length).to.equal(1);
    //             expect(ptk.getTokens('a,b,c').t[0].tt.length).to.equal(3);
    //             // expect(ptk.getTokens('a,b,c').t[0].length).to.equal(3);
    //         });
            
    //         it('should modify individual separators with setSeparatorCollection', function(){
    //             ptk.setSeparatorCollection('#');
    //             expect(ptk.getTokens('a.b.c').t.length).to.equal(3);
    //             expect(ptk.getTokens('a#b#c').t.length).to.equal(1);
    //             expect(ptk.getTokens('a#b#c').t[0].tt).to.be.an.array;
    //             expect(ptk.getTokens('a#b#c').t[0].tt.length).to.equal(3);
    //             expect(ptk.getTokens('a,b,c').t.length).to.equal(1);
    //             expect(ptk.getTokens('a,b,c').t[0]).to.be.a.string;
    //         });
    //     });
        
    //     describe('prefixes', function(){
    //         it('should allow all prefixes to be changed at once', function(){
    //             ptk.setOptions({
    //                 prefixes: {
    //                     '#': { exec: 'root' }
    //                 }
    //             });
    //             expect(ptk.get(data, 'accounts.1.checking.~propA')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.1.checking.#propA')).to.equal(data.propA);
    //             expect(ptk.get(data, 'accounts.1.checking.^test1')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.1.checking.%propA')).to.be.undefined;
    //         });
            
    //         it('should modify individual prefixes with setPrefixParent', function(){
    //             ptk.setPrefixParent('#');
    //             expect(ptk.get(data, 'accounts.1.checking.~propA')).to.equal(data.propA);
    //             expect(ptk.get(data, 'accounts.1.checking.#test1')).to.equal(data.accounts[1].test1);
    //             expect(ptk.get(data, 'accounts.1.checking.^test1')).to.be.undefined;
    //         });
            
    //         it('should modify individual prefixes with setPrefixRoot', function(){
    //             ptk.setPrefixRoot('#');
    //             expect(ptk.get(data, 'accounts.1.checking.~propA')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.1.checking.#propA')).to.equal(data.propA);
    //             expect(ptk.get(data, 'accounts.1.checking.^test1')).to.equal(data.accounts[1].test1);
    //         });
            
    //         it('should modify individual prefixes with setPrefixPlaceholder', function(){
    //             ptk.setPrefixPlaceholder('#');
    //             expect(ptk.get(data, 'accounts.1.%1.id', 'checking')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.1.#1.id', 'checking')).to.equal(data.accounts[1].checking.id);
    //             expect(ptk.get(data, 'accounts.1.checking.^test1')).to.equal(data.accounts[1].test1);
    //         });
            
    //         it('should modify individual prefixes with setPrefixContext', function(){
    //             ptk.setPrefixContext('#');
    //             expect(ptk.get(data, 'accounts.1.@1.0', 'checking')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.1.#1.0', 'checking')).to.equal('c');
    //             expect(ptk.get(data, 'accounts.1.%1.id', 'checking')).to.equal(data.accounts[1].checking.id);
    //             expect(ptk.get(data, 'accounts.1.checking.^test1')).to.equal(data.accounts[1].test1);
    //         });
            
    //     });
        
    //     describe('containers', function(){
    //         it('should allow all containers to be changed at once', function(){
    //             ptk.setOptions({
    //                 containers: {
    //                     '|': {
    //                         exec: 'property',
    //                         closer: '|'
    //                     }
    //                 }
    //             });
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts|1|checking.id')).to.equal(data.accounts[1].checking.id);
    //         });
            
    //         it('should modify individual containers with setContainerProperty', function(){
    //             ptk.setContainerProperty('|', '|');
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts|1|checking.id')).to.equal(data.accounts[1].checking.id);
    //         });
            
    //         it('should modify individual containers with setContainerEvalProperty', function(){
    //             ptk.setContainerEvalProperty('|', '|');
    //             expect(ptk.get(data, 'accounts[1]checking.id')).to.equal(data.accounts[1].checking.id);
    //             expect(ptk.get(data, '{accounts.1.test1}')).to.be.undefined;
    //             expect(ptk.get(data, '|accounts.1.test1|')).to.equal(data[data.accounts[1].test1]);
    //         });
            
    //         it('should modify individual containers with setContainerSinglequote', function(){
    //             ptk.setContainerSinglequote('|', '|');
    //             expect(ptk.get(data, 'accounts.\'1\'.checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts|1|checking.id')).to.equal(data.accounts[1].checking.id);
    //             expect(ptk.get(data, 'accounts."1".checking.id')).to.equal(data.accounts[1].checking.id);
    //         });
            
    //         it('should modify individual containers with setContainerDoublequote', function(){
    //             ptk.setContainerDoublequote('|', '|');
    //             expect(ptk.get(data, 'accounts."1".checking.id')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts|1|checking.id')).to.equal(data.accounts[1].checking.id);
    //             expect(ptk.get(data, 'accounts.\'1\'.checking.id')).to.equal(data.accounts[1].checking.id);
    //         });
            
    //         it('should modify individual containers with setContainerCall', function(){
    //             ptk.setContainerCall('|', '|');
    //             expect(ptk.get(data, 'accounts.0.ary.sort().0')).to.be.undefined;
    //             expect(ptk.get(data, 'accounts.0.ary.sort||.0')).to.equal(data.accounts[0].ary.sort()[0]);
    //             expect(ptk.get(data, 'accounts."1".checking.id')).to.equal(data.accounts[1].checking.id);
    //         });
            
    //     });
        
    //     describe('errors', function(){
    //         it('should throw error when new character is missing', function(){
    //             expect(function(){ptk.setSeparatorProperty();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setSeparatorProperty('');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setSeparatorProperty('..');}).to.throw(/invalid value/);
                
    //             expect(function(){ptk.setSeparatorCollection();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setSeparatorCollection('');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setSeparatorCollection('..');}).to.throw(/invalid value/);
                
    //             expect(function(){ptk.setPrefixParent();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setPrefixParent('');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setPrefixParent('..');}).to.throw(/invalid value/);
                
    //             expect(function(){ptk.setPrefixRoot();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setPrefixRoot('');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setPrefixRoot('..');}).to.throw(/invalid value/);
                
    //             expect(function(){ptk.setPrefixPlaceholder();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setPrefixPlaceholder('');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setPrefixPlaceholder('..');}).to.throw(/invalid value/);
                
    //             expect(function(){ptk.setPrefixContext();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setPrefixContext('');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setPrefixContext('..');}).to.throw(/invalid value/);
                
    //             expect(function(){ptk.setContainerProperty();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerProperty('','|');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerProperty('|','');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerProperty('..','|');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerProperty('|','..');}).to.throw(/invalid value/);
                
    //             expect(function(){ptk.setContainerSinglequote();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerSinglequote('','|');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerSinglequote('|','');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerSinglequote('..','|');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerSinglequote('|','..');}).to.throw(/invalid value/);
                
    //             expect(function(){ptk.setContainerDoublequote();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerDoublequote('','|');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerDoublequote('|','');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerDoublequote('..','|');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerDoublequote('|','..');}).to.throw(/invalid value/);
                
    //             expect(function(){ptk.setContainerCall();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerCall('','|');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerCall('|','');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerCall('..','|');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerCall('|','..');}).to.throw(/invalid value/);
                
    //             expect(function(){ptk.setContainerEvalProperty();}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerEvalProperty('','|');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerEvalProperty('|','');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerEvalProperty('..','|');}).to.throw(/invalid value/);
    //             expect(function(){ptk.setContainerEvalProperty('|','..');}).to.throw(/invalid value/);
    //         });
            
    //         it('should throw error when character is in use for another purpose', function(){
    //             expect(function(){ptk.setSeparatorProperty(',');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setSeparatorProperty('*');}).to.throw(/value already in use/);

    //             expect(function(){ptk.setSeparatorCollection('.');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setSeparatorCollection('*');}).to.throw(/value already in use/);

    //             expect(function(){ptk.setPrefixParent('.');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setPrefixParent('*');}).to.throw(/value already in use/);

    //             expect(function(){ptk.setPrefixRoot('.');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setPrefixRoot('*');}).to.throw(/value already in use/);

    //             expect(function(){ptk.setPrefixPlaceholder('.');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setPrefixPlaceholder('*');}).to.throw(/value already in use/);

    //             expect(function(){ptk.setPrefixContext('.');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setPrefixContext('*');}).to.throw(/value already in use/);

    //             expect(function(){ptk.setContainerProperty('.','|');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setContainerProperty('*','|');}).to.throw(/value already in use/);

    //             expect(function(){ptk.setContainerSinglequote('.','|');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setContainerSinglequote('*','|');}).to.throw(/value already in use/);

    //             expect(function(){ptk.setContainerDoublequote('.','|');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setContainerDoublequote('*','|');}).to.throw(/value already in use/);

    //             expect(function(){ptk.setContainerCall('.','|');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setContainerCall('*','|');}).to.throw(/value already in use/);

    //             expect(function(){ptk.setContainerEvalProperty('.','|');}).to.throw(/value already in use/);
    //             expect(function(){ptk.setContainerEvalProperty('*','|');}).to.throw(/value already in use/);
    //         });
    //     });

    //     describe('PathToolkit constructor', function () {
    //         it('should take options as an argument', function () {
    //             var localptk = new PathToolkit({
    //                 separators:{
    //                     '#': {exec:'property'}
    //                 },
    //                 containers: {}
    //             });
    //             expect(localptk.getTokens('a.b.c').t.length).to.equal(1);
    //             expect(localptk.getTokens('a#b#c').t.length).to.equal(3);
    //             expect(localptk.getTokens('a#b#c()').t.length).to.equal(3);
    //             expect(localptk.getTokens('a#b#c()#~d').t.length).to.equal(4);
    //             expect(localptk.getTokens('a#b#c()#~d').t[3]).not.to.be.a.string;
    //         });
    //     });
    // });
    // });

    describe( 'debug', function(){
        xit( 'should take literal prefix (!) and treat token as string literal instead of context property', function(){
            var str = 'accounts.1.test1.indexOf(!rop)';
            expect(ptk.get(data, str)).to.equal(data.accounts[1].test1.indexOf('rop'));
        } );
        it( 'should take literal prefix (!) and treat quoted token as string literal instead of context property', function(){
            var str = 'accounts.1.test1.indexOf(!"op")';
            // expect(ptk.get(data, str)).to.equal(data.accounts[1].test1.indexOf('op'));
            console.log('idx:', ptk.get(data, str));
        } );
    });

} );
