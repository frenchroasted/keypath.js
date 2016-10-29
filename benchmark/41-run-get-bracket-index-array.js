'use strict';

var PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    
    tkpath = '[1],[2]<[1]<[0]',
    tkpathSimplified = '1,2<1<0',
    data = [
        [ [ 1 ], [ 2 ] ],// 0
        [ [ 3 ], [ 4 ] ],// 1
        [ [ 5 ], [ 6 ] ],// 2
        [ [ 7 ], [ 8 ] ] // 3
    ];

module.exports = {
    name: 'Run:Get:Bracket:Index:Array',
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
