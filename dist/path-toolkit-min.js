!function(e,t){"object"==typeof exports&&"undefined"!=typeof module?module.exports=t():"function"==typeof define&&define.amd?define(t):e.PathToolkit=t()}(this,function(){"use strict";var e=function(e){return e}(),t="*",r="undefined",o="string",i="parent",s="root",n="placeholder",p="context",a="property",h="collection",c="singlequote",f="doublequote",l="call",u="evalProperty",_=function(e){e._.prefixList=Object.keys(e._.opt.prefixes),e._.propertySeparator=e.find(e._.opt.separators,a).substr(0,1),e._.separatorList=Object.keys(e._.opt.separators),e._.containerList=Object.keys(e._.opt.containers),e._.containerCloseList=e._.containerList.map(function(t){return e._.opt.containers[t].closer}),e._.simplePathChars="[\\\\"+[t].concat(e._.prefixList).concat(e._.separatorList).concat(e._.containerList).join("\\").replace("\\"+e._.propertySeparator,"")+"]",e._.simplePathRegEx=new RegExp(e._.simplePathChars),e._.allSpecials="[\\\\\\"+[t].concat(e._.prefixList).concat(e._.separatorList).concat(e._.containerList).concat(e._.containerCloseList).join("\\")+"]",e._.allSpecialsRegEx=new RegExp(e._.allSpecials,"g"),e._.escapedNonSpecialsRegEx=new RegExp("\\"+e._.allSpecials.replace(/^\[/,"[^")),e._.wildcardRegEx=new RegExp("\\"+t)},y=function(e){e._.opt=e._.opt||{},e._.opt.useCache=!0,e._.opt.simple=!1,e._.opt.force=!1,e._.opt.prefixes={"<":{exec:i},"~":{exec:s},"%":{exec:n},"@":{exec:p}},e._.opt.separators={".":{exec:a},",":{exec:h}},e._.opt.containers={"[":{closer:"]",exec:a},"'":{closer:"'",exec:c},'"':{closer:'"',exec:f},"(":{closer:")",exec:l},"{":{closer:"}",exec:u}}},x=function(e,r){var o=(e.indexOf(t),e.split(t,2)),i=!0;if(o[0]){if(o[0]===e)return o[0]===r;i=i&&r.substr(0,o[0].length)===o[0]}return o[1]&&(i=i&&r.substr(-1*o[1].length)===o[1]),i},d=function(e){return typeof e===r||null===e?!1:"function"==typeof e||"object"==typeof e},w=function(e){var t;return typeof e!==o?e&&!0:(t=e.toUpperCase(),"TRUE"===t||"YES"===t||"ON"===t)},v=function(r,i){var s="",n=[],p=[],l={},u=0,_="",y=!1,x="",d=0,w="",g="",C="",P=[],E=0,m=0;if(r._.opt.useCache&&r._.cache[i]!==e)return r._.cache[i];if(s=i.replace(r._.escapedNonSpecialsRegEx,"$&".substr(1)),u=s.length,typeof i===o&&!r._.simplePathRegEx.test(i))return n=s.split(r._.propertySeparator),r._.opt.useCache&&(r._.cache[i]=n),n;for(d=0;u>d;d++){if(m||"\\"!==s[d]||(m=d+1,d++),s[d]===t&&(y=!0),E>0)if(!m&&s[d]===w&&w!==g.closer&&E++,!m&&s[d]===g.closer&&E--,E>0)x+=s[d];else{if(u>d+1&&r._.opt.separators[s[d+1]]&&r._.opt.separators[s[d+1]].exec===h){if(p=v(r,x),p===e)return;P.push({t:p,exec:g.exec})}else if(P[0]){if(p=v(r,x),p===e)return;P.push({t:p,exec:g.exec}),n.push(P),P=[]}else if(g.exec===a){if(p=v(r,x),p===e)return;n=n.concat(p)}else if(g.exec===c||g.exec===f)n.push(x);else{if(p=v(r,x),p===e)return;n.push({t:p,exec:g.exec})}x=""}else if(!m&&s[d]in r._.opt.prefixes&&r._.opt.prefixes[s[d]].exec)l.has=!0,l[r._.opt.prefixes[s[d]].exec]?l[r._.opt.prefixes[s[d]].exec]++:l[r._.opt.prefixes[s[d]].exec]=1;else if(!m&&r._.opt.separators.hasOwnProperty(s[d])&&r._.opt.separators[s[d]].exec){if(C=r._.opt.separators[s[d]],!_&&(l.has||y))return;_&&(l.has||y)&&(_={w:_,mods:l},l={}),C.exec===a?P[0]!==e?(_&&P.push(_),n.push(P),P=[]):_&&n.push(_):C.exec===h&&_&&P.push(_),_="",y=!1}else!m&&r._.opt.containers.hasOwnProperty(s[d])&&r._.opt.containers[s[d]].exec?(g=r._.opt.containers[s[d]],_&&(l.has||y)&&(_={w:_,mods:l},l={}),P[0]!==e?_&&P.push(_):_&&n.push(_),_="",y=!1,w=s[d],E++):u>d&&(_+=s[d]);u>d&&d===m&&(m=0)}return m||(_&&(l.has||y)&&(_={w:_,mods:l},l={}),P[0]!==e?(_&&P.push(_),n.push(P)):_&&n.push(_),0!==E)?void 0:(r._.opt.useCache&&(r._.cache[i]=n),n)},g=function(t,r,i,s,n,p){var a,h,c,f=s!==e,_=[],y=0,d=0,w=1,C=0,P=r,E="",m=0,O="",S=0,b=r,A=!1,R=0,L="";if(typeof i===o){if(t._.opt.useCache&&t._.cache[i])_=t._.cache[i];else if(_=v(t,i),_===e)return}else _=i.t?i.t:[i];if(y=_.length,0!==y){for(d=y-1,p?w=p.length:p=[r];P!==e&&y>S;){if(E=_[S],A=f&&S===d,typeof E===o){if(f)if(A){if(b[E]=s,b[E]!==s)return}else t._.opt.force&&(Array.isArray(P)?b[E]!==e:!b.hasOwnProperty(E))&&(b[E]={});h=b[E]}else if(E===e)h=void 0;else if(Array.isArray(E))for(h=[],m=E.length,C=0;m>C;C++){if(a=g(t,b,E[C],s,n,p.slice()),a===e)return;A?E[C].t&&E[C].exec===u?b[a]=s:h=h.concat(a):h=E[C].t&&E[C].exec===u?h.concat(b[a]):h.concat(a)}else if(E.w){if(O=E.w+"",E.mods.parent&&(b=p[w-1-E.mods.parent],b===e))return;if(E.mods.root&&(b=p[0],p=[b],w=1),E.mods.placeholder){if(R=O-1,n[R]===e)return;O=n[R].toString()}if(E.mods.context){if(R=O-1,n[R]===e)return;h=n[R]}else if(b[O]!==e)A&&(b[O]=s),h=b[O];else if("function"==typeof b)h=O;else{if(!(t._.wildcardRegEx.test(O)>-1))return;h=[];for(L in b)b.hasOwnProperty(L)&&x(O,L)&&(A&&(b[L]=s),h.push(b[L]))}}else E.exec===u?(A&&(b[g(t,b,E,e,n,p.slice())]=s),h=b[g(t,b,E,e,n,p.slice())]):E.exec===l&&(E.t&&E.t.length?(c=g(t,b,E,e,n),h=c===e?b.apply(p[w-2]):Array.isArray(c)?b.apply(p[w-2],c):b.call(p[w-2],c)):h=b.call(p[w-2]));p.push(h),w++,b=h,P=h,S++}return b}},C=function(t,r,o,i){var s=i!==e,n=[],p=0,a=0;for(n=o.split(t._.propertySeparator),a=n.length;r!==e&&a>p;){if(""===n[p])return;s&&(p===a-1?r[n[p]]=i:t._.opt.force&&(Array.isArray(r)?r[n[p]]!==e:!r.hasOwnProperty(n[p]))&&(r[n[p]]={})),r=r[n[p++]]}return r},P=function(t,r,o,i){for(var s=i!==e,n=0,p=o.length;null!=r&&p>n;){if(""===o[n])return;s&&(n===p-1?r[o[n]]=i:t._.opt.force&&(Array.isArray(r)?r[o[n]]!==e:!r.hasOwnProperty(o[n]))&&(r[o[n]]={})),r=r[o[n++]]}return r},E=function(e,t,r,o){var i,s,n,p;if(o=o?o:"",e===t)return r(o);if(Array.isArray(e)){for(s=e.length,i=0;s>i;i++)if(n=E(e[i],t,r,o+"."+i),!n)return;return!0}if(d(e)){for(p=Object.keys(e),s=p.length,s>1&&(p=p.sort()),i=0;s>i;i++)if(e.hasOwnProperty(p[i])&&(n=E(e[p[i]],t,r,o+"."+p[i]),!n))return;return!0}return!0},m=function(e){this._={},this._.cache={},y(this),_(this),e&&this.setOptions(e)};m.prototype.getTokens=function(e){var t=v(this,e);if(typeof t!==r)return{t:t}},m.prototype.isValid=function(e){return typeof v(this,e)!==r},m.prototype.escape=function(e){return e.replace(this._.allSpecialsRegEx,"\\$&")},m.prototype.get=function(e,t){var r,i=0,s=arguments.length;if(typeof t===o&&!this._.simplePathRegEx.test(t))return C(this,e,t);if(Object.hasOwnProperty.call(t,"t")&&Array.isArray(t.t)){for(i=t.t.length-1;i>=0;i--)if(typeof t.t[i]!==o){if(r=[],s>2)for(i=2;s>i;i++)r[i-2]=arguments[i];return g(this,e,t,void 0,r)}return P(this,e,t.t)}if(r=[],s>2)for(i=2;s>i;i++)r[i-2]=arguments[i];return g(this,e,t,void 0,r)},m.prototype.set=function(t,r,i){var s,n,p=0,a=arguments.length,h=!1;if(typeof r!==o||this._.simplePathRegEx.test(r))if(Object.hasOwnProperty.call(r,"t")&&Array.isArray(r.t)){for(p=r.t.length-1;p>=0;p--)if(!h&&typeof r.t[p]!==o){if(s=[],a>3)for(p=3;a>p;p++)s[p-3]=arguments[p];n=g(this,t,r,i,s),h=!0}h||(n=P(this,t,r.t,i))}else{if(a>3)for(s=[],p=3;a>p;p++)s[p-3]=arguments[p];n=g(this,t,r,i,s)}else n=C(this,t,r,i),h=!0;return Array.isArray(n)?-1===n.indexOf(void 0):n!==e},m.prototype.find=function(e,t,r){var o=[],i=function(e){return o.push(e.substr(1)),r&&"one"!==r?!0:(o=o[0],!1)};return E(e,t,i),o[0]?o:void 0};var O=function(e,t,r,o,i){var s=e.find(t,r),n=s.substr(0,1);delete t[n],t[o]={exec:r},i&&(t[o].closer=i)},S=function(e,t){var r={};typeof t===o&&1===t.length||(t="."),r[t]={exec:a},e._.opt.prefixes={},e._.opt.containers={},e._.opt.separators=r};return m.prototype.setOptions=function(e){if(e.prefixes&&(this._.opt.prefixes=e.prefixes),e.separators&&(this._.opt.separators=e.separators),e.containers&&(this._.opt.containers=e.containers),typeof e.cache!==r&&(this._.opt.useCache=!!e.cache),typeof e.simple!==r){var t=this._.opt.useCache,o=this._.opt.force;this._.opt.simple=w(e.simple),this._.opt.simple?S(this):(y(this),this._.opt.useCache=t,this._.opt.force=o)}typeof e.force!==r&&(this._.opt.force=w(e.force)),_(this)},m.prototype.setCache=function(e){this._.opt.useCache=w(e)},m.prototype.setCacheOn=function(){this._.opt.useCache=!0},m.prototype.setCacheOff=function(){this._.opt.useCache=!1},m.prototype.setForce=function(e){this._.opt.force=w(e)},m.prototype.setForceOn=function(){this._.opt.force=!0},m.prototype.setForceOff=function(){this._.opt.force=!1},m.prototype.setSimple=function(e,t){var r=this._.opt.useCache,o=this._.opt.force;this._.opt.simple=w(e),this._.opt.simple?(S(this,t),_(this)):(y(this),_(this),this._.opt.useCache=r,this._.opt.force=o)},m.prototype.setSimpleOn=function(e){this._.opt.simple=!0,S(this,e),_(this)},m.prototype.setSimpleOff=function(){var e=this._.opt.useCache,t=this._.opt.force;this._.opt.simple=!1,y(this),_(this),this._.opt.useCache=e,this._.opt.force=t},m.prototype.setSeparatorProperty=function(e){if(typeof e!==o||1!==e.length)throw new Error("setSeparatorProperty - invalid value");if(e===t||this._.opt.separators[e]&&this._.opt.separators[e].exec!==a||this._.opt.prefixes[e]||this._.opt.containers[e])throw new Error("setSeparatorProperty - value already in use");O(this,this._.opt.separators,a,e),_(this)},m.prototype.setSeparatorCollection=function(e){if(typeof e!==o||1!==e.length)throw new Error("setSeparatorCollection - invalid value");if(e===t||this._.opt.separators[e]&&this._.opt.separators[e].exec!==h||this._.opt.prefixes[e]||this._.opt.containers[e])throw new Error("setSeparatorCollection - value already in use");O(this,this._.opt.separators,h,e),_(this)},m.prototype.setPrefixParent=function(e){if(typeof e!==o||1!==e.length)throw new Error("setPrefixParent - invalid value");if(e===t||this._.opt.prefixes[e]&&this._.opt.prefixes[e].exec!==i||this._.opt.separators[e]||this._.opt.containers[e])throw new Error("setPrefixParent - value already in use");O(this,this._.opt.prefixes,i,e),_(this)},m.prototype.setPrefixRoot=function(e){if(typeof e!==o||1!==e.length)throw new Error("setPrefixRoot - invalid value");if(e===t||this._.opt.prefixes[e]&&this._.opt.prefixes[e].exec!==s||this._.opt.separators[e]||this._.opt.containers[e])throw new Error("setPrefixRoot - value already in use");O(this,this._.opt.prefixes,s,e),_(this)},m.prototype.setPrefixPlaceholder=function(e){if(typeof e!==o||1!==e.length)throw new Error("setPrefixPlaceholder - invalid value");if(e===t||this._.opt.prefixes[e]&&this._.opt.prefixes[e].exec!==n||this._.opt.separators[e]||this._.opt.containers[e])throw new Error("setPrefixPlaceholder - value already in use");O(this,this._.opt.prefixes,n,e),_(this)},m.prototype.setPrefixContext=function(e){if(typeof e!==o||1!==e.length)throw new Error("setPrefixContext - invalid value");if(e===t||this._.opt.prefixes[e]&&this._.opt.prefixes[e].exec!==p||this._.opt.separators[e]||this._.opt.containers[e])throw new Error("setPrefixContext - value already in use");O(this,this._.opt.prefixes,p,e),_(this)},m.prototype.setContainerProperty=function(e,r){if(typeof e!==o||1!==e.length||typeof r!==o||1!==r.length)throw new Error("setContainerProperty - invalid value");if(e===t||this._.opt.containers[e]&&this._.opt.containers[e].exec!==a||this._.opt.separators[e]||this._.opt.prefixes[e])throw new Error("setContainerProperty - value already in use");O(this,this._.opt.containers,a,e,r),_(this)},m.prototype.setContainerSinglequote=function(e,r){if(typeof e!==o||1!==e.length||typeof r!==o||1!==r.length)throw new Error("setContainerSinglequote - invalid value");if(e===t||this._.opt.containers[e]&&this._.opt.containers[e].exec!==c||this._.opt.separators[e]||this._.opt.prefixes[e])throw new Error("setContainerSinglequote - value already in use");O(this,this._.opt.containers,c,e,r),_(this)},m.prototype.setContainerDoublequote=function(e,r){if(typeof e!==o||1!==e.length||typeof r!==o||1!==r.length)throw new Error("setContainerDoublequote - invalid value");if(e===t||this._.opt.containers[e]&&this._.opt.containers[e].exec!==f||this._.opt.separators[e]||this._.opt.prefixes[e])throw new Error("setContainerDoublequote - value already in use");O(this,this._.opt.containers,f,e,r),_(this)},m.prototype.setContainerCall=function(e,r){if(typeof e!==o||1!==e.length||typeof r!==o||1!==r.length)throw new Error("setContainerCall - invalid value");if(e===t||this._.opt.containers[e]&&this._.opt.containers[e].exec!==l||this._.opt.separators[e]||this._.opt.prefixes[e])throw new Error("setContainerCall - value already in use");O(this,this._.opt.containers,l,e,r),_(this)},m.prototype.setContainerEvalProperty=function(e,r){if(typeof e!==o||1!==e.length||typeof r!==o||1!==r.length)throw new Error("setContainerProperty - invalid value");if(e===t||this._.opt.containers[e]&&this._.opt.containers[e].exec!==u||this._.opt.separators[e]||this._.opt.prefixes[e])throw new Error("setContainerEvalProperty - value already in use");O(this,this._.opt.containers,u,e,r),_(this)},m.prototype.resetOptions=function(){y(this),_(this)},m});
//# sourceMappingURL=path-toolkit-min.js.map