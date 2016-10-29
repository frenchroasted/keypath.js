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
    };
    
module.exports = {
    name: 'Runtime:Get:Placeholder:Property',
    maxTime: 5,
    tests: {
        'tk#get': function(){
            tk.get( data, 'foo.%2.qux.%1', 'baz', 'bar' );
        }
    }
};
