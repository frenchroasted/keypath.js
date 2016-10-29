'use strict';

var esprima = require( 'esprima' ),
    PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    
    dPath = 'foo.bar.qux.baz',
    bPath = '["foo"]["bar"]["qux"]["baz"]',
    pPath = 'foo(123)(456)(789)';
    
tk.setOptions({cache:false});

module.exports = {
    name: 'Lexing',
    maxTime: 5,
    tests: {
        'tk#getTokens-dot': function(){
            tk.getTokens( dPath );
        },
        'esprima#tokenize-dot': function(){
            esprima.tokenize( dPath );
        },
        'tk#getTokens-bracket': function(){
            tk.getTokens( bPath );
        },
        'esprima#tokenize-bracket': function(){
            esprima.tokenize( bPath );
        },
        'tk#getTokens-paren': function(){
            tk.getTokens( pPath );
        },
        'esprima#tokenize-paren': function(){
            esprima.tokenize( pPath );
        }
    }
};