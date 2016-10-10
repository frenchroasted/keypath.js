'use strict';

var KeyPathExp = require( '../dist/keypath-umd' ),
    kp = require( '../dist/kp-umd' ),
    tk = require( '../dist/tk-umd' ),
    loget = require( 'lodash.get' ),
    keypather = require( 'keypather' )(),
    
    path = 'foo[0][1][0]',
    data = {
        foo: [
            [ [ 123 ], [ 456 ], [ 789 ] ],
            [ [ 123 ], [ 456 ], [ 789 ] ]
        ]
    },

    kpex = new KeyPathExp( path ),
    tkTokens = tk.getTokens( path );

module.exports = {
    name: 'Bracket Notation: Get indices',
    maxTime: 5,
    tests: {
        'KeyPathExp#get': function(){
            kpex.get( data );
        },
        'kp': function(){
            kp`foo[0][1][0]`( data );
        },
        'tk#get': function(){
            tk.get( data, path );
        },
        'tk#get-tokenized': function(){
            tk.get( data, tkTokens );
        },
        'keypather#get': function(){
            keypather.get( data, path );
        },
        'lodash#get': function(){
            loget( data, path );
        },
    }
};