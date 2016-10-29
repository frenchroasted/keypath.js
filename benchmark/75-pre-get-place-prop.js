'use strict';

var PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    loget = require( 'lodash.get' ),
    keypather = require( 'keypather' )(),
    
    data = {
        foo: {
            bar: {
                qux: {
                    'baz': true
                }
            }
        }
    },

    tkTokens = tk.getTokens( 'foo.%2.qux.%1' );
    
module.exports = {
    name: 'Precompiled:Get:Placeholder:Property',
    maxTime: 5,
    tests: {
        'tk#get-tokenized': function(){
            tk.get( data, tkTokens, 'baz', 'bar' );
        }
    }
};
