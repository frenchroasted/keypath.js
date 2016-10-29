'use strict';

var PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    
    tkpath = '[2][0],[1]<[0]',
    tkpathSimplified = '2.0,1<0',
    data = [
        [ [ 1 ], [ 2 ] ],// 0
        [ [ 3 ], [ 4 ] ],// 1
        [ [ 5 ], [ 6 ] ],// 2
        [ [ 7 ], [ 8 ] ] // 3
    ];

module.exports = {
    name: 'Run:Get:Bracket:Index:Sequence',
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
