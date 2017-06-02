'use strict';

var PathToolkit = require( './index.js' );

var ptk = new PathToolkit();

var data = {
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



var str = 'accounts.1.test1.indexOf(!"op")';
// expect(ptk.get(data, str)).to.equal(data.accounts[1].test1.indexOf('op'));
console.log('tokens:', JSON.stringify(ptk.getTokens(str)));
console.log('idx:', ptk.get(data, str));
