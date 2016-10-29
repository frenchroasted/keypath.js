'use strict';

var PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    
    tkpath = '["foo"]"bar","qux"<["baz"]',
    tkpathSimplified = 'foo.bar,qux<baz',
    data = {
        foo: {
            bar: {
                baz: 123
            },
            qux: {
                baz: 456
            }
        }
    };

module.exports = {
    name: 'Run:Get:Bracket:Property:Sequence',
    maxTime: 5,
    tests: {
        'tk#get': function(){
            tk.get( data, tkpath );
        },
        'tk#get-simplified': function(){
            tk.get( data, tkpathSimplified );
        }
    }
};
