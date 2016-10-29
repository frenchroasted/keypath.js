'use strict';

var PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    loget = require( 'lodash.get' ),
    keypather = require( 'keypather' )(),
    
    path1 = 'foo.bar()',
    path2 = 'foo.baz(2)',
    data = {
        foo: {
            bar: function(){ return 1; },
            baz: function(x){ return x; }
        }
    },

    tkTokens1 = tk.getTokens( path1 ),
    tkTokens2 = tk.getTokens( path2 );

module.exports = {
    name: 'Precompiled:Get:FunctionCall:Property',
    maxTime: 5,
    tests: {
        'tk#get        ()': function(){
            tk.get( data, path1 );
        },
        'tk#get        (arg)': function(){
            tk.get( data, path2 );
        }

        // lodash#get does not support this syntax
    }
};
