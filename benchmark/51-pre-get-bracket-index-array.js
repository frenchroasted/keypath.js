'use strict';

var PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    
    tkpath = '1,2<[1]<[0]',
    data = [
        [ [ 1 ], [ 2 ] ],// 0
        [ [ 3 ], [ 4 ] ],// 1
        [ [ 5 ], [ 6 ] ],// 2
        [ [ 7 ], [ 8 ] ] // 3
    ],
    
    tkTokens = tk.getTokens( tkpath );
    
module.exports = {
    name: 'Precompiled:Get:Bracket:Index:Array',
    maxTime: 5,
    tests: {
        'tk#get-tokenized': function(){
            tk.get( data, tkTokens );
        }
    }
};
