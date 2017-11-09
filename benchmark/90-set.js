'use strict';

var PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    loset = require( 'lodash.set' ),
    moutset = require( 'mout/object/set' ),
    keypather = require( 'keypather' )(),
    
    path = 'foo.bar.qux.baz',
    data = {},

    tkTokens = tk.getTokens( path );

module.exports = {
    name: 'Dot Notation: Set',
    maxTime: 5,
    tests: {
        'tk#set': function(){
            tk.set( data, path, 123 );
        },
        'tk#set-tokenized': function(){
            tk.set( data, tkTokens, 123 );
        },
        'keypather#set': function(){
            keypather.set( data, path, 123 );
        },
        'lodash#set': function(){
            loset( data, path, 123 );
        },
        'mout#set': function(){
            moutset( data, path, 123 );
        }
    }
};