'use strict';

var KeyPathExp = require( '../dist/keypath-umd' ),
    kp = require( '../dist/kp-umd' ),
    tk = require( '../dist/tk-umd' ),
    loget = require( 'lodash.get' ),
    keypather = require( 'keypather' )(),
    
    path = 'foo.%2.qux.%1',
    data = {
        foo: {
            bar: {
                qux: {
                    'baz': true
                }
            }
        }
    },

    kpex = new KeyPathExp( path ),
    tkTokens = tk.getTokens( path );

module.exports = {
    name: 'Precompiled:Get:Placeholder:Property',
    maxTime: 5,
    tests: {
        'KeyPathExp#get': function(){
            kpex.get( data, ['baz', 'bar'] );
        },
        'tk#get-tokenized': function(){
            tk.get( data, tkTokens, 'baz', 'bar' );
        }
    }
};