'use strict';

var PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    loget = require( 'lodash.get' ),
    keypather = require( 'keypather' )(),
    
    path = 'foo.bar.qux.baz',
    data = {
        foo: {
            bar: {
                qux: {
                    'baz': true
                }
            }
        }
    },
    tkTokens = tk.getTokens( path );

module.exports = {
    name: 'Precompiled:Get:Dot:Property',
    maxTime: 5,
    tests: {
        'tk#get-tokenized': function(){
            tk.get( data, tkTokens );
        },
        'lodash#get': function(){
            loget( data, tkTokens.t );
        }
    }
};