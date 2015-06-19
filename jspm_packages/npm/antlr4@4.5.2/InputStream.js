/* */ 
var Token = require("./Token").Token;
function _loadString(stream) {
  stream._index = 0;
  stream.data = [];
  for (var i = 0; i < stream.strdata.length; i++) {
    stream.data.push(stream.strdata.charCodeAt(i));
  }
  stream._size = stream.data.length;
}
function InputStream(data) {
  this.name = "<empty>";
  this.strdata = data;
  _loadString(this);
  return this;
}
Object.defineProperty(InputStream.prototype, "index", {get: function() {
    return this._index;
  }});
Object.defineProperty(InputStream.prototype, "size", {get: function() {
    return this._size;
  }});
InputStream.prototype.reset = function() {
  this._index = 0;
};
InputStream.prototype.consume = function() {
  if (this._index >= this._size) {
    throw ("cannot consume EOF");
  }
  this._index += 1;
};
InputStream.prototype.LA = function(offset) {
  if (offset === 0) {
    return 0;
  }
  if (offset < 0) {
    offset += 1;
  }
  var pos = this._index + offset - 1;
  if (pos < 0 || pos >= this._size) {
    return Token.EOF;
  }
  return this.data[pos];
};
InputStream.prototype.LT = function(offset) {
  return this.LA(offset);
};
InputStream.prototype.mark = function() {
  return -1;
};
InputStream.prototype.release = function(marker) {};
InputStream.prototype.seek = function(_index) {
  if (_index <= this._index) {
    this._index = _index;
    return ;
  }
  this._index = Math.min(_index, this._size);
};
InputStream.prototype.getText = function(start, stop) {
  if (stop >= this._size) {
    stop = this._size - 1;
  }
  if (start >= this._size) {
    return "";
  } else {
    return this.strdata.slice(start, stop + 1);
  }
};
InputStream.prototype.toString = function() {
  return this.strdata;
};
exports.InputStream = InputStream;
