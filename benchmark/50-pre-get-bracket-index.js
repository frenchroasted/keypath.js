'use strict';

var PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    loget = require( 'lodash.get' ),
    keypather = require( 'keypather' )(),
    
    path = '[2][0][1][0]',
    data = [ 'a', 'b',
        [
            [ [ 123, 1 ], [ 456, 2 ], [ 789, 3 ] ],
            [ [ 123, 4 ], [ 456, 5 ], [ 789, 6 ] ]
        ]
    ],
    tkTokens = tk.getTokens( path );

module.exports = {
    name: 'Precompiled:Get:Bracket:Index',
    maxTime: 5,
    tests: {
        'tk#get-tokenized': function(){
            tk.get( data, tkTokens );
        }
    }
};
