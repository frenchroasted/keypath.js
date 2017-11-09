'use strict';

var PathToolkit = require( '../dist/path-toolkit-min' ),
    tk = new PathToolkit(),
    tkNoCache = new PathToolkit({cache:false}),
    loget = require( 'lodash.get' ),
    moutget = require( 'mout/object/get' ),
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
    native = function(data){
        return data.foo.bar.qux.baz;
    };

module.exports = {
    name: 'Runtime:Get:Dot:Property',
    maxTime: 5,
    tests: {
        'tk#get': function(){
            tk.get( data, path );
        },
        'tkNoCache#get': function(){
            tkNoCache.get( data, path );
        },
        'keypather#get': function(){
            keypather.get( data, path );
        },
        'lodash#get': function(){
            loget( data, path );
        },
        'mout#get': function(){
            moutget( data, path );
        },
        'native#dot': function(){
            native(data);
        }
    }
};