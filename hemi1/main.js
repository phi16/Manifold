"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(","));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("Math.pow("));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr(")"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=function(_G,_H){return new T1(1,new T2(1,_B,new T2(1,_G,new T2(1,_z,new T2(1,_H,_E)))));},_I=new T(function(){return B(unCStr("Math.acos("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_E)));},_M=new T(function(){return B(unCStr("Math.acosh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_E)));},_Q=new T(function(){return B(unCStr("Math.asin("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_E)));},_U=new T(function(){return B(unCStr("Math.asinh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_E)));},_Y=new T(function(){return B(unCStr("Math.atan("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_E)));},_12=new T(function(){return B(unCStr("Math.atanh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_E)));},_16=new T(function(){return B(unCStr("Math.cos("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_E)));},_1a=new T(function(){return B(unCStr("Math.cosh("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_E)));},_1e=new T(function(){return B(unCStr("Math.exp("));}),_1f=new T1(0,_1e),_1g=function(_1h){return new T1(1,new T2(1,_1f,new T2(1,_1h,_E)));},_1i=new T(function(){return B(unCStr("Math.log("));}),_1j=new T1(0,_1i),_1k=function(_1l){return new T1(1,new T2(1,_1j,new T2(1,_1l,_E)));},_1m=new T(function(){return B(unCStr(")/Math.log("));}),_1n=new T1(0,_1m),_1o=function(_1p,_1q){return new T1(1,new T2(1,_1j,new T2(1,_1q,new T2(1,_1n,new T2(1,_1p,_E)))));},_1r=new T(function(){return B(unCStr("Math.PI"));}),_1s=new T1(0,_1r),_1t=new T(function(){return B(unCStr("Math.sin("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_E)));},_1x=new T(function(){return B(unCStr("Math.sinh("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_E)));},_1B=new T(function(){return B(unCStr("Math.sqrt("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_E)));},_1F=new T(function(){return B(unCStr("Math.tan("));}),_1G=new T1(0,_1F),_1H=function(_1I){return new T1(1,new T2(1,_1G,new T2(1,_1I,_E)));},_1J=new T(function(){return B(unCStr("Math.tanh("));}),_1K=new T1(0,_1J),_1L=function(_1M){return new T1(1,new T2(1,_1K,new T2(1,_1M,_E)));},_1N=new T(function(){return B(unCStr("("));}),_1O=new T1(0,_1N),_1P=new T(function(){return B(unCStr(")/("));}),_1Q=new T1(0,_1P),_1R=function(_1S,_1T){return new T1(1,new T2(1,_1O,new T2(1,_1S,new T2(1,_1Q,new T2(1,_1T,_E)))));},_1U=new T1(0,1),_1V=function(_1W,_1X){var _1Y=E(_1W);if(!_1Y._){var _1Z=_1Y.a,_20=E(_1X);if(!_20._){var _21=_20.a;return (_1Z!=_21)?(_1Z>_21)?2:0:1;}else{var _22=I_compareInt(_20.a,_1Z);return (_22<=0)?(_22>=0)?1:2:0;}}else{var _23=_1Y.a,_24=E(_1X);if(!_24._){var _25=I_compareInt(_23,_24.a);return (_25>=0)?(_25<=0)?1:2:0;}else{var _26=I_compare(_23,_24.a);return (_26>=0)?(_26<=0)?1:2:0;}}},_27=new T(function(){return B(unCStr("base"));}),_28=new T(function(){return B(unCStr("GHC.Exception"));}),_29=new T(function(){return B(unCStr("ArithException"));}),_2a=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_27,_28,_29),_2b=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2a,_w,_w),_2c=function(_2d){return E(_2b);},_2e=function(_2f){return E(E(_2f).a);},_2g=function(_2h,_2i,_2j){var _2k=B(A1(_2h,_)),_2l=B(A1(_2i,_)),_2m=hs_eqWord64(_2k.a,_2l.a);if(!_2m){return __Z;}else{var _2n=hs_eqWord64(_2k.b,_2l.b);return (!_2n)?__Z:new T1(1,_2j);}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _2g(B(_2e(_2q.a)),_2c,_2q.b);});},_2r=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2s=new T(function(){return B(unCStr("denormal"));}),_2t=new T(function(){return B(unCStr("divide by zero"));}),_2u=new T(function(){return B(unCStr("loss of precision"));}),_2v=new T(function(){return B(unCStr("arithmetic underflow"));}),_2w=new T(function(){return B(unCStr("arithmetic overflow"));}),_2x=function(_2y,_2z){switch(E(_2y)){case 0:return new F(function(){return _n(_2w,_2z);});break;case 1:return new F(function(){return _n(_2v,_2z);});break;case 2:return new F(function(){return _n(_2u,_2z);});break;case 3:return new F(function(){return _n(_2t,_2z);});break;case 4:return new F(function(){return _n(_2s,_2z);});break;default:return new F(function(){return _n(_2r,_2z);});}},_2A=function(_2B){return new F(function(){return _2x(_2B,_w);});},_2C=function(_2D,_2E,_2F){return new F(function(){return _2x(_2E,_2F);});},_2G=44,_2H=93,_2I=91,_2J=function(_2K,_2L,_2M){var _2N=E(_2L);if(!_2N._){return new F(function(){return unAppCStr("[]",_2M);});}else{var _2O=new T(function(){var _2P=new T(function(){var _2Q=function(_2R){var _2S=E(_2R);if(!_2S._){return E(new T2(1,_2H,_2M));}else{var _2T=new T(function(){return B(A2(_2K,_2S.a,new T(function(){return B(_2Q(_2S.b));})));});return new T2(1,_2G,_2T);}};return B(_2Q(_2N.b));});return B(A2(_2K,_2N.a,_2P));});return new T2(1,_2I,_2O);}},_2U=function(_2V,_2W){return new F(function(){return _2J(_2x,_2V,_2W);});},_2X=new T3(0,_2C,_2A,_2U),_2Y=new T(function(){return new T5(0,_2c,_2X,_2Z,_2o,_2A);}),_2Z=function(_30){return new T2(0,_2Y,_30);},_31=3,_32=new T(function(){return B(_2Z(_31));}),_33=new T(function(){return die(_32);}),_34=function(_35,_36){var _37=E(_35);return (_37._==0)?_37.a*Math.pow(2,_36):I_toNumber(_37.a)*Math.pow(2,_36);},_38=function(_39,_3a){var _3b=E(_39);if(!_3b._){var _3c=_3b.a,_3d=E(_3a);return (_3d._==0)?_3c==_3d.a:(I_compareInt(_3d.a,_3c)==0)?true:false;}else{var _3e=_3b.a,_3f=E(_3a);return (_3f._==0)?(I_compareInt(_3e,_3f.a)==0)?true:false:(I_compare(_3e,_3f.a)==0)?true:false;}},_3g=function(_3h){var _3i=E(_3h);if(!_3i._){return E(_3i.a);}else{return new F(function(){return I_toInt(_3i.a);});}},_3j=function(_3k,_3l){while(1){var _3m=E(_3k);if(!_3m._){var _3n=_3m.a,_3o=E(_3l);if(!_3o._){var _3p=_3o.a,_3q=addC(_3n,_3p);if(!E(_3q.b)){return new T1(0,_3q.a);}else{_3k=new T1(1,I_fromInt(_3n));_3l=new T1(1,I_fromInt(_3p));continue;}}else{_3k=new T1(1,I_fromInt(_3n));_3l=_3o;continue;}}else{var _3r=E(_3l);if(!_3r._){_3k=_3m;_3l=new T1(1,I_fromInt(_3r.a));continue;}else{return new T1(1,I_add(_3m.a,_3r.a));}}}},_3s=function(_3t,_3u){while(1){var _3v=E(_3t);if(!_3v._){var _3w=E(_3v.a);if(_3w==(-2147483648)){_3t=new T1(1,I_fromInt(-2147483648));continue;}else{var _3x=E(_3u);if(!_3x._){var _3y=_3x.a;return new T2(0,new T1(0,quot(_3w,_3y)),new T1(0,_3w%_3y));}else{_3t=new T1(1,I_fromInt(_3w));_3u=_3x;continue;}}}else{var _3z=E(_3u);if(!_3z._){_3t=_3v;_3u=new T1(1,I_fromInt(_3z.a));continue;}else{var _3A=I_quotRem(_3v.a,_3z.a);return new T2(0,new T1(1,_3A.a),new T1(1,_3A.b));}}}},_3B=new T1(0,0),_3C=function(_3D,_3E){while(1){var _3F=E(_3D);if(!_3F._){_3D=new T1(1,I_fromInt(_3F.a));continue;}else{return new T1(1,I_shiftLeft(_3F.a,_3E));}}},_3G=function(_3H,_3I,_3J){if(!B(_38(_3J,_3B))){var _3K=B(_3s(_3I,_3J)),_3L=_3K.a;switch(B(_1V(B(_3C(_3K.b,1)),_3J))){case 0:return new F(function(){return _34(_3L,_3H);});break;case 1:if(!(B(_3g(_3L))&1)){return new F(function(){return _34(_3L,_3H);});}else{return new F(function(){return _34(B(_3j(_3L,_1U)),_3H);});}break;default:return new F(function(){return _34(B(_3j(_3L,_1U)),_3H);});}}else{return E(_33);}},_3M=function(_3N,_3O){var _3P=E(_3N);if(!_3P._){var _3Q=_3P.a,_3R=E(_3O);return (_3R._==0)?_3Q>_3R.a:I_compareInt(_3R.a,_3Q)<0;}else{var _3S=_3P.a,_3T=E(_3O);return (_3T._==0)?I_compareInt(_3S,_3T.a)>0:I_compare(_3S,_3T.a)>0;}},_3U=new T1(0,1),_3V=function(_3W,_3X){var _3Y=E(_3W);if(!_3Y._){var _3Z=_3Y.a,_40=E(_3X);return (_40._==0)?_3Z<_40.a:I_compareInt(_40.a,_3Z)>0;}else{var _41=_3Y.a,_42=E(_3X);return (_42._==0)?I_compareInt(_41,_42.a)<0:I_compare(_41,_42.a)<0;}},_43=new T(function(){return B(unCStr("base"));}),_44=new T(function(){return B(unCStr("Control.Exception.Base"));}),_45=new T(function(){return B(unCStr("PatternMatchFail"));}),_46=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_43,_44,_45),_47=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_46,_w,_w),_48=function(_49){return E(_47);},_4a=function(_4b){var _4c=E(_4b);return new F(function(){return _2g(B(_2e(_4c.a)),_48,_4c.b);});},_4d=function(_4e){return E(E(_4e).a);},_4f=function(_4g){return new T2(0,_4h,_4g);},_4i=function(_4j,_4k){return new F(function(){return _n(E(_4j).a,_4k);});},_4l=function(_4m,_4n){return new F(function(){return _2J(_4i,_4m,_4n);});},_4o=function(_4p,_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=new T3(0,_4o,_4d,_4l),_4h=new T(function(){return new T5(0,_48,_4s,_4f,_4a,_4d);}),_4t=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4u=function(_4v){return E(E(_4v).c);},_4w=function(_4x,_4y){return new F(function(){return die(new T(function(){return B(A2(_4u,_4y,_4x));}));});},_4z=function(_4A,_30){return new F(function(){return _4w(_4A,_30);});},_4B=function(_4C,_4D){var _4E=E(_4D);if(!_4E._){return new T2(0,_w,_w);}else{var _4F=_4E.a;if(!B(A1(_4C,_4F))){return new T2(0,_w,_4E);}else{var _4G=new T(function(){var _4H=B(_4B(_4C,_4E.b));return new T2(0,_4H.a,_4H.b);});return new T2(0,new T2(1,_4F,new T(function(){return E(E(_4G).a);})),new T(function(){return E(E(_4G).b);}));}}},_4I=32,_4J=new T(function(){return B(unCStr("\n"));}),_4K=function(_4L){return (E(_4L)==124)?false:true;},_4M=function(_4N,_4O){var _4P=B(_4B(_4K,B(unCStr(_4N)))),_4Q=_4P.a,_4R=function(_4S,_4T){var _4U=new T(function(){var _4V=new T(function(){return B(_n(_4O,new T(function(){return B(_n(_4T,_4J));},1)));});return B(unAppCStr(": ",_4V));},1);return new F(function(){return _n(_4S,_4U);});},_4W=E(_4P.b);if(!_4W._){return new F(function(){return _4R(_4Q,_w);});}else{if(E(_4W.a)==124){return new F(function(){return _4R(_4Q,new T2(1,_4I,_4W.b));});}else{return new F(function(){return _4R(_4Q,_w);});}}},_4X=function(_4Y){return new F(function(){return _4z(new T1(0,new T(function(){return B(_4M(_4Y,_4t));})),_4h);});},_4Z=function(_50){var _51=function(_52,_53){while(1){if(!B(_3V(_52,_50))){if(!B(_3M(_52,_50))){if(!B(_38(_52,_50))){return new F(function(){return _4X("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_53);}}else{return _53-1|0;}}else{var _54=B(_3C(_52,1)),_55=_53+1|0;_52=_54;_53=_55;continue;}}};return new F(function(){return _51(_3U,0);});},_56=function(_57){var _58=E(_57);if(!_58._){var _59=_58.a>>>0;if(!_59){return -1;}else{var _5a=function(_5b,_5c){while(1){if(_5b>=_59){if(_5b<=_59){if(_5b!=_59){return new F(function(){return _4X("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5c);}}else{return _5c-1|0;}}else{var _5d=imul(_5b,2)>>>0,_5e=_5c+1|0;_5b=_5d;_5c=_5e;continue;}}};return new F(function(){return _5a(1,0);});}}else{return new F(function(){return _4Z(_58);});}},_5f=function(_5g){var _5h=E(_5g);if(!_5h._){var _5i=_5h.a>>>0;if(!_5i){return new T2(0,-1,0);}else{var _5j=function(_5k,_5l){while(1){if(_5k>=_5i){if(_5k<=_5i){if(_5k!=_5i){return new F(function(){return _4X("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5l);}}else{return _5l-1|0;}}else{var _5m=imul(_5k,2)>>>0,_5n=_5l+1|0;_5k=_5m;_5l=_5n;continue;}}};return new T2(0,B(_5j(1,0)),(_5i&_5i-1>>>0)>>>0&4294967295);}}else{var _5o=_5h.a;return new T2(0,B(_56(_5h)),I_compareInt(I_and(_5o,I_sub(_5o,I_fromInt(1))),0));}},_5p=function(_5q,_5r){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);return (_5u._==0)?_5t<=_5u.a:I_compareInt(_5u.a,_5t)>=0;}else{var _5v=_5s.a,_5w=E(_5r);return (_5w._==0)?I_compareInt(_5v,_5w.a)<=0:I_compare(_5v,_5w.a)<=0;}},_5x=function(_5y,_5z){while(1){var _5A=E(_5y);if(!_5A._){var _5B=_5A.a,_5C=E(_5z);if(!_5C._){return new T1(0,(_5B>>>0&_5C.a>>>0)>>>0&4294967295);}else{_5y=new T1(1,I_fromInt(_5B));_5z=_5C;continue;}}else{var _5D=E(_5z);if(!_5D._){_5y=_5A;_5z=new T1(1,I_fromInt(_5D.a));continue;}else{return new T1(1,I_and(_5A.a,_5D.a));}}}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){var _5K=_5J.a,_5L=subC(_5I,_5K);if(!E(_5L.b)){return new T1(0,_5L.a);}else{_5F=new T1(1,I_fromInt(_5I));_5G=new T1(1,I_fromInt(_5K));continue;}}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5M=E(_5G);if(!_5M._){_5F=_5H;_5G=new T1(1,I_fromInt(_5M.a));continue;}else{return new T1(1,I_sub(_5H.a,_5M.a));}}}},_5N=new T1(0,2),_5O=function(_5P,_5Q){var _5R=E(_5P);if(!_5R._){var _5S=(_5R.a>>>0&(2<<_5Q>>>0)-1>>>0)>>>0,_5T=1<<_5Q>>>0;return (_5T<=_5S)?(_5T>=_5S)?1:2:0;}else{var _5U=B(_5x(_5R,B(_5E(B(_3C(_5N,_5Q)),_3U)))),_5V=B(_3C(_3U,_5Q));return (!B(_3M(_5V,_5U)))?(!B(_3V(_5V,_5U)))?1:2:0;}},_5W=function(_5X,_5Y){while(1){var _5Z=E(_5X);if(!_5Z._){_5X=new T1(1,I_fromInt(_5Z.a));continue;}else{return new T1(1,I_shiftRight(_5Z.a,_5Y));}}},_60=function(_61,_62,_63,_64){var _65=B(_5f(_64)),_66=_65.a;if(!E(_65.b)){var _67=B(_56(_63));if(_67<((_66+_61|0)-1|0)){var _68=_66+(_61-_62|0)|0;if(_68>0){if(_68>_67){if(_68<=(_67+1|0)){if(!E(B(_5f(_63)).b)){return 0;}else{return new F(function(){return _34(_1U,_61-_62|0);});}}else{return 0;}}else{var _69=B(_5W(_63,_68));switch(B(_5O(_63,_68-1|0))){case 0:return new F(function(){return _34(_69,_61-_62|0);});break;case 1:if(!(B(_3g(_69))&1)){return new F(function(){return _34(_69,_61-_62|0);});}else{return new F(function(){return _34(B(_3j(_69,_1U)),_61-_62|0);});}break;default:return new F(function(){return _34(B(_3j(_69,_1U)),_61-_62|0);});}}}else{return new F(function(){return _34(_63,(_61-_62|0)-_68|0);});}}else{if(_67>=_62){var _6a=B(_5W(_63,(_67+1|0)-_62|0));switch(B(_5O(_63,_67-_62|0))){case 0:return new F(function(){return _34(_6a,((_67-_66|0)+1|0)-_62|0);});break;case 2:return new F(function(){return _34(B(_3j(_6a,_1U)),((_67-_66|0)+1|0)-_62|0);});break;default:if(!(B(_3g(_6a))&1)){return new F(function(){return _34(_6a,((_67-_66|0)+1|0)-_62|0);});}else{return new F(function(){return _34(B(_3j(_6a,_1U)),((_67-_66|0)+1|0)-_62|0);});}}}else{return new F(function(){return _34(_63, -_66);});}}}else{var _6b=B(_56(_63))-_66|0,_6c=function(_6d){var _6e=function(_6f,_6g){if(!B(_5p(B(_3C(_6g,_62)),_6f))){return new F(function(){return _3G(_6d-_62|0,_6f,_6g);});}else{return new F(function(){return _3G((_6d-_62|0)+1|0,_6f,B(_3C(_6g,1)));});}};if(_6d>=_62){if(_6d!=_62){return new F(function(){return _6e(_63,new T(function(){return B(_3C(_64,_6d-_62|0));}));});}else{return new F(function(){return _6e(_63,_64);});}}else{return new F(function(){return _6e(new T(function(){return B(_3C(_63,_62-_6d|0));}),_64);});}};if(_61>_6b){return new F(function(){return _6c(_61);});}else{return new F(function(){return _6c(_6b);});}}},_6h=new T1(0,2147483647),_6i=new T(function(){return B(_3j(_6h,_3U));}),_6j=function(_6k){var _6l=E(_6k);if(!_6l._){var _6m=E(_6l.a);return (_6m==(-2147483648))?E(_6i):new T1(0, -_6m);}else{return new T1(1,I_negate(_6l.a));}},_6n=new T(function(){return 0/0;}),_6o=new T(function(){return -1/0;}),_6p=new T(function(){return 1/0;}),_6q=0,_6r=function(_6s,_6t){if(!B(_38(_6t,_3B))){if(!B(_38(_6s,_3B))){if(!B(_3V(_6s,_3B))){return new F(function(){return _60(-1021,53,_6s,_6t);});}else{return  -B(_60(-1021,53,B(_6j(_6s)),_6t));}}else{return E(_6q);}}else{return (!B(_38(_6s,_3B)))?(!B(_3V(_6s,_3B)))?E(_6p):E(_6o):E(_6n);}},_6u=function(_6v){return new T1(0,new T(function(){var _6w=E(_6v),_6x=jsShow(B(_6r(_6w.a,_6w.b)));return fromJSStr(_6x);}));},_6y=new T(function(){return B(unCStr("1/("));}),_6z=new T1(0,_6y),_6A=function(_6B){return new T1(1,new T2(1,_6z,new T2(1,_6B,_E)));},_6C=new T(function(){return B(unCStr(")+("));}),_6D=new T1(0,_6C),_6E=function(_6F,_6G){return new T1(1,new T2(1,_1O,new T2(1,_6F,new T2(1,_6D,new T2(1,_6G,_E)))));},_6H=new T(function(){return B(unCStr("-("));}),_6I=new T1(0,_6H),_6J=function(_6K){return new T1(1,new T2(1,_6I,new T2(1,_6K,_E)));},_6L=new T(function(){return B(unCStr(")*("));}),_6M=new T1(0,_6L),_6N=function(_6O,_6P){return new T1(1,new T2(1,_1O,new T2(1,_6O,new T2(1,_6M,new T2(1,_6P,_E)))));},_6Q=function(_6R){return E(E(_6R).a);},_6S=function(_6T){return E(E(_6T).d);},_6U=function(_6V,_6W){return new F(function(){return A3(_6Q,_6X,_6V,new T(function(){return B(A2(_6S,_6X,_6W));}));});},_6Y=new T(function(){return B(unCStr("Math.abs("));}),_6Z=new T1(0,_6Y),_70=function(_71){return new T1(1,new T2(1,_6Z,new T2(1,_71,_E)));},_72=function(_73){while(1){var _74=E(_73);if(!_74._){_73=new T1(1,I_fromInt(_74.a));continue;}else{return new F(function(){return I_toString(_74.a);});}}},_75=function(_76,_77){return new F(function(){return _n(fromJSStr(B(_72(_76))),_77);});},_78=41,_79=40,_7a=new T1(0,0),_7b=function(_7c,_7d,_7e){if(_7c<=6){return new F(function(){return _75(_7d,_7e);});}else{if(!B(_3V(_7d,_7a))){return new F(function(){return _75(_7d,_7e);});}else{return new T2(1,_79,new T(function(){return B(_n(fromJSStr(B(_72(_7d))),new T2(1,_78,_7e)));}));}}},_7f=new T(function(){return B(unCStr("."));}),_7g=function(_7h){return new T1(0,new T(function(){return B(_n(B(_7b(0,_7h,_w)),_7f));}));},_7i=new T(function(){return B(unCStr("Math.sign("));}),_7j=new T1(0,_7i),_7k=function(_7l){return new T1(1,new T2(1,_7j,new T2(1,_7l,_E)));},_6X=new T(function(){return {_:0,a:_6E,b:_6U,c:_6N,d:_6J,e:_70,f:_7k,g:_7g};}),_7m=new T4(0,_6X,_1R,_6A,_6u),_7n={_:0,a:_7m,b:_1s,c:_1g,d:_1k,e:_1D,f:_F,g:_1o,h:_1v,i:_18,j:_1H,k:_S,l:_K,m:_10,n:_1z,o:_1c,p:_1L,q:_W,r:_O,s:_14},_7o=function(_7p,_7q){var _7r=E(_7p);return E(_7q);},_7s=function(_7t,_7u){var _7v=E(_7u);return E(_7t);},_7w=function(_7x,_7y){var _7z=E(_7x),_7A=E(_7y);return new T3(0,E(B(A1(_7z.a,_7A.a))),E(B(A1(_7z.b,_7A.b))),E(B(A1(_7z.c,_7A.c))));},_7B=function(_7C,_7D,_7E){return new T3(0,E(_7C),E(_7D),E(_7E));},_7F=function(_7G){return new F(function(){return _7B(_7G,_7G,_7G);});},_7H=function(_7I,_7J){var _7K=E(_7J),_7L=E(_7I);return new T3(0,E(_7L),E(_7L),E(_7L));},_7M=function(_7N,_7O){var _7P=E(_7O);return new T3(0,E(B(A1(_7N,_7P.a))),E(B(A1(_7N,_7P.b))),E(B(A1(_7N,_7P.c))));},_7Q=new T2(0,_7M,_7H),_7R=new T5(0,_7Q,_7F,_7w,_7o,_7s),_7S=new T1(0,0),_7T=new T1(0,1),_7U=function(_7V){return E(E(_7V).g);},_7W=function(_7X){var _7Y=B(A2(_7U,_7X,_7T)),_7Z=B(A2(_7U,_7X,_7S));return new T3(0,E(new T3(0,E(_7Y),E(_7Z),E(_7Z))),E(new T3(0,E(_7Z),E(_7Y),E(_7Z))),E(new T3(0,E(_7Z),E(_7Z),E(_7Y))));},_80=function(_81){return E(E(_81).a);},_82=function(_83){return E(E(_83).a);},_84=function(_85){return E(E(_85).a);},_86=function(_87){return E(E(_87).a);},_88=function(_89,_8a,_8b){var _8c=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_89).c).a);})));})));}),_8d=new T(function(){return B(A3(_86,B(_84(E(_89).a)),new T(function(){return B(_6S(_8c));}),_8b));});return new T2(0,new T(function(){return B(A2(_6S,_8c,_8a));}),_8d);},_8e=function(_8f){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_8f));}))));});},_8g=new T(function(){return B(_8e("ww_s4CO Ord a"));}),_8h=function(_8i,_8j,_8k,_8l){var _8m=new T(function(){return B(_82(new T(function(){return B(_80(_8i));})));}),_8n=B(A2(_7U,_8m,_7S));return E(B(_88(new T3(0,_7R,_7W,new T2(0,_8i,_8g)),_8k,new T3(0,E(_8n),E(B(A2(_7U,_8m,_7T))),E(_8n)))).b);},_8o=new T(function(){return B(unCStr("x"));}),_8p=new T1(0,_8o),_8q=new T(function(){return B(unCStr("y"));}),_8r=new T1(0,_8q),_8s=new T(function(){return B(unCStr("z"));}),_8t=new T1(0,_8s),_8u=new T(function(){return B(_8h(_7n,_8p,_8r,_8t));}),_8v=new T(function(){return E(E(_8u).a);}),_8w=new T(function(){return B(unCStr(",y:"));}),_8x=new T1(0,_8w),_8y=new T(function(){return E(E(_8u).b);}),_8z=new T(function(){return B(unCStr(",z:"));}),_8A=new T1(0,_8z),_8B=new T(function(){return E(E(_8u).c);}),_8C=new T(function(){return B(unCStr("})"));}),_8D=new T1(0,_8C),_8E=new T2(1,_8D,_w),_8F=new T2(1,_8B,_8E),_8G=new T2(1,_8A,_8F),_8H=new T2(1,_8y,_8G),_8I=new T2(1,_8x,_8H),_8J=new T2(1,_8v,_8I),_8K=new T(function(){return B(unCStr("({x:"));}),_8L=new T1(0,_8K),_8M=new T2(1,_8L,_8J),_8N=function(_8O){return E(_8O);},_8P=new T(function(){return toJSStr(B(_e(_x,_8N,_8M)));}),_8Q=new T2(1,_8r,_E),_8R=new T2(1,_6I,_8Q),_8S=new T(function(){return toJSStr(B(_e(_x,_8N,_8R)));}),_8T=function(_8U,_8V,_8W){var _8X=E(_8W);if(!_8X._){return new F(function(){return A1(_8V,_8X.a);});}else{var _8Y=new T(function(){return B(_0(_8U));}),_8Z=new T(function(){return B(_2(_8U));}),_90=function(_91){var _92=E(_91);if(!_92._){return E(_8Z);}else{return new F(function(){return A2(_8Y,new T(function(){return B(_8T(_8U,_8V,_92.a));}),new T(function(){return B(_90(_92.b));}));});}};return new F(function(){return _90(_8X.a);});}},_93=function(_94,_95,_96){var _97=new T(function(){return B(_0(_94));}),_98=new T(function(){return B(_2(_94));}),_99=function(_9a){var _9b=E(_9a);if(!_9b._){return E(_98);}else{return new F(function(){return A2(_97,new T(function(){return B(_8T(_94,_95,_9b.a));}),new T(function(){return B(_99(_9b.b));}));});}};return new F(function(){return _99(_96);});},_9c=new T(function(){return B(unCStr("-("));}),_9d=new T1(0,_9c),_9e=new T(function(){return B(unCStr(")"));}),_9f=new T1(0,_9e),_9g=new T2(1,_9f,_w),_9h=new T(function(){return B(unCStr("y"));}),_9i=new T1(0,_9h),_9j=new T2(1,_9i,_9g),_9k=new T2(1,_9d,_9j),_9l=new T(function(){return toJSStr(B(_93(_x,_8N,_9k)));}),_9m=new T(function(){return eval("__strict(compile)");}),_9n=new T(function(){return B(unCStr(","));}),_9o=new T1(0,_9n),_9p=new T(function(){return B(unCStr("pow("));}),_9q=new T1(0,_9p),_9r=function(_9s,_9t){return new T1(1,new T2(1,_9q,new T2(1,_9s,new T2(1,_9o,new T2(1,_9t,_9g)))));},_9u=new T(function(){return B(unCStr("acos("));}),_9v=new T1(0,_9u),_9w=function(_9x){return new T1(1,new T2(1,_9v,new T2(1,_9x,_9g)));},_9y=new T(function(){return B(unCStr("acosh("));}),_9z=new T1(0,_9y),_9A=function(_9B){return new T1(1,new T2(1,_9z,new T2(1,_9B,_9g)));},_9C=new T(function(){return B(unCStr("asin("));}),_9D=new T1(0,_9C),_9E=function(_9F){return new T1(1,new T2(1,_9D,new T2(1,_9F,_9g)));},_9G=new T(function(){return B(unCStr("asinh("));}),_9H=new T1(0,_9G),_9I=function(_9J){return new T1(1,new T2(1,_9H,new T2(1,_9J,_9g)));},_9K=new T(function(){return B(unCStr("atan("));}),_9L=new T1(0,_9K),_9M=function(_9N){return new T1(1,new T2(1,_9L,new T2(1,_9N,_9g)));},_9O=new T(function(){return B(unCStr("atanh("));}),_9P=new T1(0,_9O),_9Q=function(_9R){return new T1(1,new T2(1,_9P,new T2(1,_9R,_9g)));},_9S=new T(function(){return B(unCStr("cos("));}),_9T=new T1(0,_9S),_9U=function(_9V){return new T1(1,new T2(1,_9T,new T2(1,_9V,_9g)));},_9W=new T(function(){return B(unCStr("cosh("));}),_9X=new T1(0,_9W),_9Y=function(_9Z){return new T1(1,new T2(1,_9X,new T2(1,_9Z,_9g)));},_a0=new T(function(){return B(unCStr("exp("));}),_a1=new T1(0,_a0),_a2=function(_a3){return new T1(1,new T2(1,_a1,new T2(1,_a3,_9g)));},_a4=new T(function(){return B(unCStr("log("));}),_a5=new T1(0,_a4),_a6=function(_a7){return new T1(1,new T2(1,_a5,new T2(1,_a7,_9g)));},_a8=new T(function(){return B(unCStr(")/log("));}),_a9=new T1(0,_a8),_aa=function(_ab,_ac){return new T1(1,new T2(1,_a5,new T2(1,_ac,new T2(1,_a9,new T2(1,_ab,_9g)))));},_ad=new T(function(){return B(unCStr("pi"));}),_ae=new T1(0,_ad),_af=new T(function(){return B(unCStr("sin("));}),_ag=new T1(0,_af),_ah=function(_ai){return new T1(1,new T2(1,_ag,new T2(1,_ai,_9g)));},_aj=new T(function(){return B(unCStr("sinh("));}),_ak=new T1(0,_aj),_al=function(_am){return new T1(1,new T2(1,_ak,new T2(1,_am,_9g)));},_an=new T(function(){return B(unCStr("sqrt("));}),_ao=new T1(0,_an),_ap=function(_aq){return new T1(1,new T2(1,_ao,new T2(1,_aq,_9g)));},_ar=new T(function(){return B(unCStr("tan("));}),_as=new T1(0,_ar),_at=function(_au){return new T1(1,new T2(1,_as,new T2(1,_au,_9g)));},_av=new T(function(){return B(unCStr("tanh("));}),_aw=new T1(0,_av),_ax=function(_ay){return new T1(1,new T2(1,_aw,new T2(1,_ay,_9g)));},_az=new T(function(){return B(unCStr("("));}),_aA=new T1(0,_az),_aB=new T(function(){return B(unCStr(")/("));}),_aC=new T1(0,_aB),_aD=function(_aE,_aF){return new T1(1,new T2(1,_aA,new T2(1,_aE,new T2(1,_aC,new T2(1,_aF,_9g)))));},_aG=function(_aH){return new T1(0,new T(function(){var _aI=E(_aH),_aJ=jsShow(B(_6r(_aI.a,_aI.b)));return fromJSStr(_aJ);}));},_aK=new T(function(){return B(unCStr("1./("));}),_aL=new T1(0,_aK),_aM=function(_aN){return new T1(1,new T2(1,_aL,new T2(1,_aN,_9g)));},_aO=new T(function(){return B(unCStr(")+("));}),_aP=new T1(0,_aO),_aQ=function(_aR,_aS){return new T1(1,new T2(1,_aA,new T2(1,_aR,new T2(1,_aP,new T2(1,_aS,_9g)))));},_aT=function(_aU){return new T1(1,new T2(1,_9d,new T2(1,_aU,_9g)));},_aV=new T(function(){return B(unCStr(")*("));}),_aW=new T1(0,_aV),_aX=function(_aY,_aZ){return new T1(1,new T2(1,_aA,new T2(1,_aY,new T2(1,_aW,new T2(1,_aZ,_9g)))));},_b0=function(_b1,_b2){return new F(function(){return A3(_6Q,_b3,_b1,new T(function(){return B(A2(_6S,_b3,_b2));}));});},_b4=new T(function(){return B(unCStr("abs("));}),_b5=new T1(0,_b4),_b6=function(_b7){return new T1(1,new T2(1,_b5,new T2(1,_b7,_9g)));},_b8=new T(function(){return B(unCStr("."));}),_b9=function(_ba){return new T1(0,new T(function(){return B(_n(B(_7b(0,_ba,_w)),_b8));}));},_bb=new T(function(){return B(unCStr("sign("));}),_bc=new T1(0,_bb),_bd=function(_be){return new T1(1,new T2(1,_bc,new T2(1,_be,_9g)));},_b3=new T(function(){return {_:0,a:_aQ,b:_b0,c:_aX,d:_aT,e:_b6,f:_bd,g:_b9};}),_bf=new T4(0,_b3,_aD,_aM,_aG),_bg={_:0,a:_bf,b:_ae,c:_a2,d:_a6,e:_ap,f:_9r,g:_aa,h:_ah,i:_9U,j:_at,k:_9E,l:_9w,m:_9M,n:_al,o:_9Y,p:_ax,q:_9I,r:_9A,s:_9Q},_bh=function(_bi){return E(E(_bi).c);},_bj=function(_bk,_bl,_bm,_bn,_bo,_bp,_bq){var _br=B(_82(B(_80(_bk)))),_bs=new T(function(){return B(A3(_6Q,_br,new T(function(){return B(A3(_bh,_br,_bl,_bo));}),new T(function(){return B(A3(_bh,_br,_bm,_bp));})));});return new F(function(){return A3(_6Q,_br,_bs,new T(function(){return B(A3(_bh,_br,_bn,_bq));}));});},_bt=function(_bu){return E(E(_bu).b);},_bv=function(_bw){return E(E(_bw).e);},_bx=function(_by,_bz){var _bA=B(_82(B(_80(_by)))),_bB=new T(function(){return B(A2(_bv,_by,new T(function(){var _bC=E(_bz),_bD=_bC.a,_bE=_bC.b,_bF=_bC.c;return B(_bj(_by,_bD,_bE,_bF,_bD,_bE,_bF));})));});return new F(function(){return A3(_bt,_bA,_bB,new T(function(){return B(A2(_7U,_bA,_7T));}));});},_bG=new T(function(){return B(unCStr("x"));}),_bH=new T1(0,_bG),_bI=new T(function(){return B(unCStr("z"));}),_bJ=new T1(0,_bI),_bK=new T3(0,E(_bH),E(_9i),E(_bJ)),_bL=new T(function(){return B(_bx(_bg,_bK));}),_bM=new T(function(){return toJSStr(B(_8T(_x,_8N,_bL)));}),_bN=new T(function(){return B(unCStr("(/=) is not defined"));}),_bO=new T(function(){return B(err(_bN));}),_bP=new T(function(){return B(unCStr("(==) is not defined"));}),_bQ=new T(function(){return B(err(_bP));}),_bR=new T2(0,_bQ,_bO),_bS=new T(function(){return B(unCStr("(<) is not defined"));}),_bT=new T(function(){return B(err(_bS));}),_bU=new T(function(){return B(unCStr("(<=) is not defined"));}),_bV=new T(function(){return B(err(_bU));}),_bW=new T(function(){return B(unCStr("(>) is not defined"));}),_bX=new T(function(){return B(err(_bW));}),_bY=new T(function(){return B(unCStr("(>=) is not defined"));}),_bZ=new T(function(){return B(err(_bY));}),_c0=new T(function(){return B(unCStr("compare is not defined"));}),_c1=new T(function(){return B(err(_c0));}),_c2=new T(function(){return B(unCStr("max("));}),_c3=new T1(0,_c2),_c4=function(_c5,_c6){return new T1(1,new T2(1,_c3,new T2(1,_c5,new T2(1,_9o,new T2(1,_c6,_9g)))));},_c7=new T(function(){return B(unCStr("min("));}),_c8=new T1(0,_c7),_c9=function(_ca,_cb){return new T1(1,new T2(1,_c8,new T2(1,_ca,new T2(1,_9o,new T2(1,_cb,_9g)))));},_cc={_:0,a:_bR,b:_c1,c:_bT,d:_bV,e:_bX,f:_bZ,g:_c4,h:_c9},_cd=new T2(0,_bg,_cc),_ce=function(_cf){return E(E(_cf).f);},_cg=function(_ch){return E(E(_ch).b);},_ci=function(_cj){return E(E(_cj).c);},_ck=function(_cl){return E(E(_cl).d);},_cm=function(_cn,_co,_cp,_cq,_cr){var _cs=new T(function(){return E(E(E(_cn).c).a);}),_ct=new T(function(){var _cu=E(_cn).a,_cv=new T(function(){var _cw=new T(function(){return B(_80(_cs));}),_cx=new T(function(){return B(_82(_cw));}),_cy=new T(function(){return B(A2(_ck,_cs,_co));}),_cz=new T(function(){return B(A3(_ce,_cs,_co,_cq));}),_cA=function(_cB,_cC){var _cD=new T(function(){var _cE=new T(function(){return B(A3(_cg,_cw,new T(function(){return B(A3(_bh,_cx,_cq,_cB));}),_co));});return B(A3(_6Q,_cx,_cE,new T(function(){return B(A3(_bh,_cx,_cC,_cy));})));});return new F(function(){return A3(_bh,_cx,_cz,_cD);});};return B(A3(_86,B(_84(_cu)),_cA,_cp));});return B(A3(_ci,_cu,_cv,_cr));});return new T2(0,new T(function(){return B(A3(_ce,_cs,_co,_cq));}),_ct);},_cF=function(_cG,_cH,_cI,_cJ){var _cK=E(_cI),_cL=E(_cJ),_cM=B(_cm(_cH,_cK.a,_cK.b,_cL.a,_cL.b));return new T2(0,_cM.a,_cM.b);},_cN=new T1(0,1),_cO=function(_cP){return E(E(_cP).l);},_cQ=function(_cR,_cS,_cT){var _cU=new T(function(){return E(E(E(_cR).c).a);}),_cV=new T(function(){var _cW=new T(function(){return B(_80(_cU));}),_cX=new T(function(){var _cY=B(_82(_cW)),_cZ=new T(function(){var _d0=new T(function(){return B(A3(_bt,_cY,new T(function(){return B(A2(_7U,_cY,_cN));}),new T(function(){return B(A3(_bh,_cY,_cS,_cS));})));});return B(A2(_bv,_cU,_d0));});return B(A2(_6S,_cY,_cZ));});return B(A3(_86,B(_84(E(_cR).a)),function(_d1){return new F(function(){return A3(_cg,_cW,_d1,_cX);});},_cT));});return new T2(0,new T(function(){return B(A2(_cO,_cU,_cS));}),_cV);},_d2=function(_d3,_d4,_d5){var _d6=E(_d5),_d7=B(_cQ(_d4,_d6.a,_d6.b));return new T2(0,_d7.a,_d7.b);},_d8=function(_d9){return E(E(_d9).r);},_da=function(_db,_dc,_dd){var _de=new T(function(){return E(E(E(_db).c).a);}),_df=new T(function(){var _dg=new T(function(){return B(_80(_de));}),_dh=new T(function(){var _di=new T(function(){var _dj=B(_82(_dg));return B(A3(_bt,_dj,new T(function(){return B(A3(_bh,_dj,_dc,_dc));}),new T(function(){return B(A2(_7U,_dj,_cN));})));});return B(A2(_bv,_de,_di));});return B(A3(_86,B(_84(E(_db).a)),function(_dk){return new F(function(){return A3(_cg,_dg,_dk,_dh);});},_dd));});return new T2(0,new T(function(){return B(A2(_d8,_de,_dc));}),_df);},_dl=function(_dm,_dn,_do){var _dp=E(_do),_dq=B(_da(_dn,_dp.a,_dp.b));return new T2(0,_dq.a,_dq.b);},_dr=function(_ds){return E(E(_ds).k);},_dt=function(_du,_dv,_dw){var _dx=new T(function(){return E(E(E(_du).c).a);}),_dy=new T(function(){var _dz=new T(function(){return B(_80(_dx));}),_dA=new T(function(){var _dB=new T(function(){var _dC=B(_82(_dz));return B(A3(_bt,_dC,new T(function(){return B(A2(_7U,_dC,_cN));}),new T(function(){return B(A3(_bh,_dC,_dv,_dv));})));});return B(A2(_bv,_dx,_dB));});return B(A3(_86,B(_84(E(_du).a)),function(_dD){return new F(function(){return A3(_cg,_dz,_dD,_dA);});},_dw));});return new T2(0,new T(function(){return B(A2(_dr,_dx,_dv));}),_dy);},_dE=function(_dF,_dG,_dH){var _dI=E(_dH),_dJ=B(_dt(_dG,_dI.a,_dI.b));return new T2(0,_dJ.a,_dJ.b);},_dK=function(_dL){return E(E(_dL).q);},_dM=function(_dN,_dO,_dP){var _dQ=new T(function(){return E(E(E(_dN).c).a);}),_dR=new T(function(){var _dS=new T(function(){return B(_80(_dQ));}),_dT=new T(function(){var _dU=new T(function(){var _dV=B(_82(_dS));return B(A3(_6Q,_dV,new T(function(){return B(A3(_bh,_dV,_dO,_dO));}),new T(function(){return B(A2(_7U,_dV,_cN));})));});return B(A2(_bv,_dQ,_dU));});return B(A3(_86,B(_84(E(_dN).a)),function(_dW){return new F(function(){return A3(_cg,_dS,_dW,_dT);});},_dP));});return new T2(0,new T(function(){return B(A2(_dK,_dQ,_dO));}),_dR);},_dX=function(_dY,_dZ,_e0){var _e1=E(_e0),_e2=B(_dM(_dZ,_e1.a,_e1.b));return new T2(0,_e2.a,_e2.b);},_e3=function(_e4){return E(E(_e4).m);},_e5=function(_e6,_e7,_e8){var _e9=new T(function(){return E(E(E(_e6).c).a);}),_ea=new T(function(){var _eb=new T(function(){return B(_80(_e9));}),_ec=new T(function(){var _ed=B(_82(_eb));return B(A3(_6Q,_ed,new T(function(){return B(A2(_7U,_ed,_cN));}),new T(function(){return B(A3(_bh,_ed,_e7,_e7));})));});return B(A3(_86,B(_84(E(_e6).a)),function(_ee){return new F(function(){return A3(_cg,_eb,_ee,_ec);});},_e8));});return new T2(0,new T(function(){return B(A2(_e3,_e9,_e7));}),_ea);},_ef=function(_eg,_eh,_ei){var _ej=E(_ei),_ek=B(_e5(_eh,_ej.a,_ej.b));return new T2(0,_ek.a,_ek.b);},_el=function(_em){return E(E(_em).s);},_en=function(_eo,_ep,_eq){var _er=new T(function(){return E(E(E(_eo).c).a);}),_es=new T(function(){var _et=new T(function(){return B(_80(_er));}),_eu=new T(function(){var _ev=B(_82(_et));return B(A3(_bt,_ev,new T(function(){return B(A2(_7U,_ev,_cN));}),new T(function(){return B(A3(_bh,_ev,_ep,_ep));})));});return B(A3(_86,B(_84(E(_eo).a)),function(_ew){return new F(function(){return A3(_cg,_et,_ew,_eu);});},_eq));});return new T2(0,new T(function(){return B(A2(_el,_er,_ep));}),_es);},_ex=function(_ey,_ez,_eA){var _eB=E(_eA),_eC=B(_en(_ez,_eB.a,_eB.b));return new T2(0,_eC.a,_eC.b);},_eD=function(_eE){return E(E(_eE).i);},_eF=function(_eG){return E(E(_eG).h);},_eH=function(_eI,_eJ,_eK){var _eL=new T(function(){return E(E(E(_eI).c).a);}),_eM=new T(function(){var _eN=new T(function(){return B(_82(new T(function(){return B(_80(_eL));})));}),_eO=new T(function(){return B(A2(_6S,_eN,new T(function(){return B(A2(_eF,_eL,_eJ));})));});return B(A3(_86,B(_84(E(_eI).a)),function(_eP){return new F(function(){return A3(_bh,_eN,_eP,_eO);});},_eK));});return new T2(0,new T(function(){return B(A2(_eD,_eL,_eJ));}),_eM);},_eQ=function(_eR,_eS,_eT){var _eU=E(_eT),_eV=B(_eH(_eS,_eU.a,_eU.b));return new T2(0,_eV.a,_eV.b);},_eW=function(_eX){return E(E(_eX).o);},_eY=function(_eZ){return E(E(_eZ).n);},_f0=function(_f1,_f2,_f3){var _f4=new T(function(){return E(E(E(_f1).c).a);}),_f5=new T(function(){var _f6=new T(function(){return B(_82(new T(function(){return B(_80(_f4));})));}),_f7=new T(function(){return B(A2(_eY,_f4,_f2));});return B(A3(_86,B(_84(E(_f1).a)),function(_f8){return new F(function(){return A3(_bh,_f6,_f8,_f7);});},_f3));});return new T2(0,new T(function(){return B(A2(_eW,_f4,_f2));}),_f5);},_f9=function(_fa,_fb,_fc){var _fd=E(_fc),_fe=B(_f0(_fb,_fd.a,_fd.b));return new T2(0,_fe.a,_fe.b);},_ff=function(_fg){return E(E(_fg).c);},_fh=function(_fi,_fj,_fk){var _fl=new T(function(){return E(E(E(_fi).c).a);}),_fm=new T(function(){var _fn=new T(function(){return B(_82(new T(function(){return B(_80(_fl));})));}),_fo=new T(function(){return B(A2(_ff,_fl,_fj));});return B(A3(_86,B(_84(E(_fi).a)),function(_fp){return new F(function(){return A3(_bh,_fn,_fp,_fo);});},_fk));});return new T2(0,new T(function(){return B(A2(_ff,_fl,_fj));}),_fm);},_fq=function(_fr,_fs,_ft){var _fu=E(_ft),_fv=B(_fh(_fs,_fu.a,_fu.b));return new T2(0,_fv.a,_fv.b);},_fw=function(_fx,_fy,_fz){var _fA=new T(function(){return E(E(E(_fx).c).a);}),_fB=new T(function(){var _fC=new T(function(){return B(_80(_fA));}),_fD=new T(function(){return B(_82(_fC));}),_fE=new T(function(){return B(A3(_cg,_fC,new T(function(){return B(A2(_7U,_fD,_cN));}),_fy));});return B(A3(_86,B(_84(E(_fx).a)),function(_fF){return new F(function(){return A3(_bh,_fD,_fF,_fE);});},_fz));});return new T2(0,new T(function(){return B(A2(_ck,_fA,_fy));}),_fB);},_fG=function(_fH,_fI,_fJ){var _fK=E(_fJ),_fL=B(_fw(_fI,_fK.a,_fK.b));return new T2(0,_fL.a,_fL.b);},_fM=function(_fN,_fO,_fP,_fQ){var _fR=new T(function(){return E(E(_fO).c);}),_fS=new T3(0,new T(function(){return E(E(_fO).a);}),new T(function(){return E(E(_fO).b);}),new T2(0,new T(function(){return E(E(_fR).a);}),new T(function(){return E(E(_fR).b);})));return new F(function(){return A3(_cg,_fN,new T(function(){var _fT=E(_fQ),_fU=B(_fw(_fS,_fT.a,_fT.b));return new T2(0,_fU.a,_fU.b);}),new T(function(){var _fV=E(_fP),_fW=B(_fw(_fS,_fV.a,_fV.b));return new T2(0,_fW.a,_fW.b);}));});},_fX=new T1(0,0),_fY=function(_fZ){return E(E(_fZ).b);},_g0=function(_g1){return E(E(_g1).b);},_g2=function(_g3){var _g4=new T(function(){return E(E(E(_g3).c).a);}),_g5=new T(function(){return B(A2(_g0,E(_g3).a,new T(function(){return B(A2(_7U,B(_82(B(_80(_g4)))),_fX));})));});return new T2(0,new T(function(){return B(_fY(_g4));}),_g5);},_g6=function(_g7,_g8){var _g9=B(_g2(_g8));return new T2(0,_g9.a,_g9.b);},_ga=function(_gb,_gc,_gd){var _ge=new T(function(){return E(E(E(_gb).c).a);}),_gf=new T(function(){var _gg=new T(function(){return B(_82(new T(function(){return B(_80(_ge));})));}),_gh=new T(function(){return B(A2(_eD,_ge,_gc));});return B(A3(_86,B(_84(E(_gb).a)),function(_gi){return new F(function(){return A3(_bh,_gg,_gi,_gh);});},_gd));});return new T2(0,new T(function(){return B(A2(_eF,_ge,_gc));}),_gf);},_gj=function(_gk,_gl,_gm){var _gn=E(_gm),_go=B(_ga(_gl,_gn.a,_gn.b));return new T2(0,_go.a,_go.b);},_gp=function(_gq,_gr,_gs){var _gt=new T(function(){return E(E(E(_gq).c).a);}),_gu=new T(function(){var _gv=new T(function(){return B(_82(new T(function(){return B(_80(_gt));})));}),_gw=new T(function(){return B(A2(_eW,_gt,_gr));});return B(A3(_86,B(_84(E(_gq).a)),function(_gx){return new F(function(){return A3(_bh,_gv,_gx,_gw);});},_gs));});return new T2(0,new T(function(){return B(A2(_eY,_gt,_gr));}),_gu);},_gy=function(_gz,_gA,_gB){var _gC=E(_gB),_gD=B(_gp(_gA,_gC.a,_gC.b));return new T2(0,_gD.a,_gD.b);},_gE=new T1(0,2),_gF=function(_gG,_gH,_gI){var _gJ=new T(function(){return E(E(E(_gG).c).a);}),_gK=new T(function(){var _gL=new T(function(){return B(_80(_gJ));}),_gM=new T(function(){return B(_82(_gL));}),_gN=new T(function(){var _gO=new T(function(){return B(A3(_cg,_gL,new T(function(){return B(A2(_7U,_gM,_cN));}),new T(function(){return B(A2(_7U,_gM,_gE));})));});return B(A3(_cg,_gL,_gO,new T(function(){return B(A2(_bv,_gJ,_gH));})));});return B(A3(_86,B(_84(E(_gG).a)),function(_gP){return new F(function(){return A3(_bh,_gM,_gP,_gN);});},_gI));});return new T2(0,new T(function(){return B(A2(_bv,_gJ,_gH));}),_gK);},_gQ=function(_gR,_gS,_gT){var _gU=E(_gT),_gV=B(_gF(_gS,_gU.a,_gU.b));return new T2(0,_gV.a,_gV.b);},_gW=function(_gX){return E(E(_gX).j);},_gY=function(_gZ,_h0,_h1){var _h2=new T(function(){return E(E(E(_gZ).c).a);}),_h3=new T(function(){var _h4=new T(function(){return B(_80(_h2));}),_h5=new T(function(){var _h6=new T(function(){return B(A2(_eD,_h2,_h0));});return B(A3(_bh,B(_82(_h4)),_h6,_h6));});return B(A3(_86,B(_84(E(_gZ).a)),function(_h7){return new F(function(){return A3(_cg,_h4,_h7,_h5);});},_h1));});return new T2(0,new T(function(){return B(A2(_gW,_h2,_h0));}),_h3);},_h8=function(_h9,_ha,_hb){var _hc=E(_hb),_hd=B(_gY(_ha,_hc.a,_hc.b));return new T2(0,_hd.a,_hd.b);},_he=function(_hf){return E(E(_hf).p);},_hg=function(_hh,_hi,_hj){var _hk=new T(function(){return E(E(E(_hh).c).a);}),_hl=new T(function(){var _hm=new T(function(){return B(_80(_hk));}),_hn=new T(function(){var _ho=new T(function(){return B(A2(_eW,_hk,_hi));});return B(A3(_bh,B(_82(_hm)),_ho,_ho));});return B(A3(_86,B(_84(E(_hh).a)),function(_hp){return new F(function(){return A3(_cg,_hm,_hp,_hn);});},_hj));});return new T2(0,new T(function(){return B(A2(_he,_hk,_hi));}),_hl);},_hq=function(_hr,_hs,_ht){var _hu=E(_ht),_hv=B(_hg(_hs,_hu.a,_hu.b));return new T2(0,_hv.a,_hv.b);},_hw=function(_hx,_hy){return {_:0,a:_hx,b:new T(function(){return B(_g6(_hx,_hy));}),c:function(_hz){return new F(function(){return _fq(_hx,_hy,_hz);});},d:function(_hz){return new F(function(){return _fG(_hx,_hy,_hz);});},e:function(_hz){return new F(function(){return _gQ(_hx,_hy,_hz);});},f:function(_hA,_hz){return new F(function(){return _cF(_hx,_hy,_hA,_hz);});},g:function(_hA,_hz){return new F(function(){return _fM(_hx,_hy,_hA,_hz);});},h:function(_hz){return new F(function(){return _gj(_hx,_hy,_hz);});},i:function(_hz){return new F(function(){return _eQ(_hx,_hy,_hz);});},j:function(_hz){return new F(function(){return _h8(_hx,_hy,_hz);});},k:function(_hz){return new F(function(){return _dE(_hx,_hy,_hz);});},l:function(_hz){return new F(function(){return _d2(_hx,_hy,_hz);});},m:function(_hz){return new F(function(){return _ef(_hx,_hy,_hz);});},n:function(_hz){return new F(function(){return _gy(_hx,_hy,_hz);});},o:function(_hz){return new F(function(){return _f9(_hx,_hy,_hz);});},p:function(_hz){return new F(function(){return _hq(_hx,_hy,_hz);});},q:function(_hz){return new F(function(){return _dX(_hx,_hy,_hz);});},r:function(_hz){return new F(function(){return _dl(_hx,_hy,_hz);});},s:function(_hz){return new F(function(){return _ex(_hx,_hy,_hz);});}};},_hB=function(_hC,_hD,_hE,_hF,_hG){var _hH=new T(function(){return B(_80(new T(function(){return E(E(E(_hC).c).a);})));}),_hI=new T(function(){var _hJ=E(_hC).a,_hK=new T(function(){var _hL=new T(function(){return B(_82(_hH));}),_hM=new T(function(){return B(A3(_bh,_hL,_hF,_hF));}),_hN=function(_hO,_hP){var _hQ=new T(function(){return B(A3(_bt,_hL,new T(function(){return B(A3(_bh,_hL,_hO,_hF));}),new T(function(){return B(A3(_bh,_hL,_hD,_hP));})));});return new F(function(){return A3(_cg,_hH,_hQ,_hM);});};return B(A3(_86,B(_84(_hJ)),_hN,_hE));});return B(A3(_ci,_hJ,_hK,_hG));});return new T2(0,new T(function(){return B(A3(_cg,_hH,_hD,_hF));}),_hI);},_hR=function(_hS,_hT,_hU,_hV){var _hW=E(_hU),_hX=E(_hV),_hY=B(_hB(_hT,_hW.a,_hW.b,_hX.a,_hX.b));return new T2(0,_hY.a,_hY.b);},_hZ=function(_i0){return E(E(_i0).d);},_i1=function(_i2,_i3){var _i4=new T(function(){return B(_80(new T(function(){return E(E(E(_i2).c).a);})));}),_i5=new T(function(){return B(A2(_g0,E(_i2).a,new T(function(){return B(A2(_7U,B(_82(_i4)),_fX));})));});return new T2(0,new T(function(){return B(A2(_hZ,_i4,_i3));}),_i5);},_i6=function(_i7,_i8,_i9){var _ia=B(_i1(_i8,_i9));return new T2(0,_ia.a,_ia.b);},_ib=function(_ic,_id,_ie){var _if=new T(function(){return B(_80(new T(function(){return E(E(E(_ic).c).a);})));}),_ig=new T(function(){return B(_82(_if));}),_ih=new T(function(){var _ii=new T(function(){var _ij=new T(function(){return B(A3(_cg,_if,new T(function(){return B(A2(_7U,_ig,_cN));}),new T(function(){return B(A3(_bh,_ig,_id,_id));})));});return B(A2(_6S,_ig,_ij));});return B(A3(_86,B(_84(E(_ic).a)),function(_ik){return new F(function(){return A3(_bh,_ig,_ik,_ii);});},_ie));}),_il=new T(function(){return B(A3(_cg,_if,new T(function(){return B(A2(_7U,_ig,_cN));}),_id));});return new T2(0,_il,_ih);},_im=function(_in,_io,_ip){var _iq=E(_ip),_ir=B(_ib(_io,_iq.a,_iq.b));return new T2(0,_ir.a,_ir.b);},_is=function(_it,_iu){return new T4(0,_it,function(_hA,_hz){return new F(function(){return _hR(_it,_iu,_hA,_hz);});},function(_hz){return new F(function(){return _im(_it,_iu,_hz);});},function(_hz){return new F(function(){return _i6(_it,_iu,_hz);});});},_iv=function(_iw,_ix,_iy,_iz,_iA){var _iB=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_iw).c).a);})));})));}),_iC=new T(function(){var _iD=E(_iw).a,_iE=new T(function(){var _iF=function(_iG,_iH){return new F(function(){return A3(_6Q,_iB,new T(function(){return B(A3(_bh,_iB,_ix,_iH));}),new T(function(){return B(A3(_bh,_iB,_iG,_iz));}));});};return B(A3(_86,B(_84(_iD)),_iF,_iy));});return B(A3(_ci,_iD,_iE,_iA));});return new T2(0,new T(function(){return B(A3(_bh,_iB,_ix,_iz));}),_iC);},_iI=function(_iJ,_iK,_iL){var _iM=E(_iK),_iN=E(_iL),_iO=B(_iv(_iJ,_iM.a,_iM.b,_iN.a,_iN.b));return new T2(0,_iO.a,_iO.b);},_iP=function(_iQ,_iR,_iS,_iT,_iU){var _iV=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_iQ).c).a);})));})));}),_iW=new T(function(){var _iX=E(_iQ).a,_iY=new T(function(){return B(A3(_86,B(_84(_iX)),new T(function(){return B(_6Q(_iV));}),_iS));});return B(A3(_ci,_iX,_iY,_iU));});return new T2(0,new T(function(){return B(A3(_6Q,_iV,_iR,_iT));}),_iW);},_iZ=function(_j0,_j1,_j2){var _j3=E(_j1),_j4=E(_j2),_j5=B(_iP(_j0,_j3.a,_j3.b,_j4.a,_j4.b));return new T2(0,_j5.a,_j5.b);},_j6=function(_j7,_j8,_j9){var _ja=B(_jb(_j7));return new F(function(){return A3(_6Q,_ja,_j8,new T(function(){return B(A2(_6S,_ja,_j9));}));});},_jc=function(_jd){return E(E(_jd).e);},_je=function(_jf){return E(E(_jf).f);},_jg=function(_jh,_ji,_jj){var _jk=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_jh).c).a);})));})));}),_jl=new T(function(){var _jm=new T(function(){return B(A2(_je,_jk,_ji));});return B(A3(_86,B(_84(E(_jh).a)),function(_jn){return new F(function(){return A3(_bh,_jk,_jn,_jm);});},_jj));});return new T2(0,new T(function(){return B(A2(_jc,_jk,_ji));}),_jl);},_jo=function(_jp,_jq){var _jr=E(_jq),_js=B(_jg(_jp,_jr.a,_jr.b));return new T2(0,_js.a,_js.b);},_jt=function(_ju,_jv){var _jw=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_ju).c).a);})));})));}),_jx=new T(function(){return B(A2(_g0,E(_ju).a,new T(function(){return B(A2(_7U,_jw,_fX));})));});return new T2(0,new T(function(){return B(A2(_7U,_jw,_jv));}),_jx);},_jy=function(_jz,_jA){var _jB=B(_jt(_jz,_jA));return new T2(0,_jB.a,_jB.b);},_jC=function(_jD,_jE){var _jF=E(_jE),_jG=B(_88(_jD,_jF.a,_jF.b));return new T2(0,_jG.a,_jG.b);},_jH=function(_jI,_jJ){var _jK=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_jI).c).a);})));})));}),_jL=new T(function(){return B(A2(_g0,E(_jI).a,new T(function(){return B(A2(_7U,_jK,_fX));})));});return new T2(0,new T(function(){return B(A2(_je,_jK,_jJ));}),_jL);},_jM=function(_jN,_jO){var _jP=B(_jH(_jN,E(_jO).a));return new T2(0,_jP.a,_jP.b);},_jb=function(_jQ){return {_:0,a:function(_hA,_hz){return new F(function(){return _iZ(_jQ,_hA,_hz);});},b:function(_hA,_hz){return new F(function(){return _j6(_jQ,_hA,_hz);});},c:function(_hA,_hz){return new F(function(){return _iI(_jQ,_hA,_hz);});},d:function(_hz){return new F(function(){return _jC(_jQ,_hz);});},e:function(_hz){return new F(function(){return _jo(_jQ,_hz);});},f:function(_hz){return new F(function(){return _jM(_jQ,_hz);});},g:function(_hz){return new F(function(){return _jy(_jQ,_hz);});}};},_jR=function(_jS){var _jT=new T(function(){return E(E(_jS).a);}),_jU=new T3(0,_7R,_7W,new T2(0,_jT,new T(function(){return E(E(_jS).b);}))),_jV=new T(function(){return B(_hw(new T(function(){return B(_is(new T(function(){return B(_jb(_jU));}),_jU));}),_jU));}),_jW=new T(function(){return B(_82(new T(function(){return B(_80(_jT));})));}),_jX=function(_jY){return E(B(_bx(_jV,new T(function(){var _jZ=E(_jY),_k0=B(A2(_7U,_jW,_7T)),_k1=B(A2(_7U,_jW,_7S));return new T3(0,E(new T2(0,_jZ.a,new T3(0,E(_k0),E(_k1),E(_k1)))),E(new T2(0,_jZ.b,new T3(0,E(_k1),E(_k0),E(_k1)))),E(new T2(0,_jZ.c,new T3(0,E(_k1),E(_k1),E(_k0)))));}))).b);};return E(_jX);},_k2=new T(function(){return B(_jR(_cd));}),_k3=function(_k4,_k5){var _k6=E(_k5);return (_k6._==0)?__Z:new T2(1,_k4,new T2(1,_k6.a,new T(function(){return B(_k3(_k4,_k6.b));})));},_k7=new T(function(){var _k8=B(A1(_k2,_bK));return new T2(1,_k8.a,new T(function(){return B(_k3(_9o,new T2(1,_k8.b,new T2(1,_k8.c,_w))));}));}),_k9=new T1(1,_k7),_ka=new T2(1,_k9,_9g),_kb=new T(function(){return B(unCStr("vec3("));}),_kc=new T1(0,_kb),_kd=new T2(1,_kc,_ka),_ke=new T(function(){return toJSStr(B(_93(_x,_8N,_kd)));}),_kf="enclose",_kg="outline",_kh="polygon",_ki="z",_kj="y",_kk="x",_kl=0,_km=function(_kn){var _ko=__new(),_kp=_ko,_kq=function(_kr,_){while(1){var _ks=E(_kr);if(!_ks._){return _kl;}else{var _kt=E(_ks.a),_ku=__set(_kp,E(_kt.a),E(_kt.b));_kr=_ks.b;continue;}}},_kv=B(_kq(_kn,_));return E(_kp);},_kw=function(_kx){return new F(function(){return _km(new T2(1,new T2(0,_kk,new T(function(){return E(E(E(E(_kx).d).a).a);})),new T2(1,new T2(0,_kj,new T(function(){return E(E(E(E(_kx).d).a).b);})),new T2(1,new T2(0,_ki,new T(function(){return E(E(E(E(_kx).d).a).c);})),new T2(1,new T2(0,_kh,new T(function(){return E(_kx).h;})),new T2(1,new T2(0,_kg,new T(function(){return E(_kx).i;})),new T2(1,new T2(0,_kf,new T(function(){return E(_kx).j;})),_w)))))));});},_ky=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_kz=new T(function(){return B(err(_ky));}),_kA=new T(function(){return eval("__strict(drawObjects)");}),_kB=new T(function(){return eval("__strict(draw)");}),_kC=function(_kD,_kE){var _kF=jsShowI(_kD);return new F(function(){return _n(fromJSStr(_kF),_kE);});},_kG=function(_kH,_kI,_kJ){if(_kI>=0){return new F(function(){return _kC(_kI,_kJ);});}else{if(_kH<=6){return new F(function(){return _kC(_kI,_kJ);});}else{return new T2(1,_79,new T(function(){var _kK=jsShowI(_kI);return B(_n(fromJSStr(_kK),new T2(1,_78,_kJ)));}));}}},_kL=new T(function(){return B(unCStr(")"));}),_kM=function(_kN,_kO){var _kP=new T(function(){var _kQ=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_kG(0,_kN,_w)),_kL));})));},1);return B(_n(B(_kG(0,_kO,_w)),_kQ));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_kP)));});},_kR=new T2(1,_kl,_w),_kS=function(_kT){return E(_kT);},_kU=function(_kV){return E(_kV);},_kW=function(_kX,_kY){return E(_kY);},_kZ=function(_l0,_l1){return E(_l0);},_l2=function(_l3){return E(_l3);},_l4=new T2(0,_l2,_kZ),_l5=function(_l6,_l7){return E(_l6);},_l8=new T5(0,_l4,_kU,_kS,_kW,_l5),_l9=function(_la){var _lb=E(_la);return new F(function(){return Math.log(_lb+(_lb+1)*Math.sqrt((_lb-1)/(_lb+1)));});},_lc=function(_ld){var _le=E(_ld);return new F(function(){return Math.log(_le+Math.sqrt(1+_le*_le));});},_lf=function(_lg){var _lh=E(_lg);return 0.5*Math.log((1+_lh)/(1-_lh));},_li=function(_lj,_lk){return Math.log(E(_lk))/Math.log(E(_lj));},_ll=3.141592653589793,_lm=function(_ln){var _lo=E(_ln);return new F(function(){return _6r(_lo.a,_lo.b);});},_lp=function(_lq){return 1/E(_lq);},_lr=function(_ls){var _lt=E(_ls),_lu=E(_lt);return (_lu==0)?E(_6q):(_lu<=0)? -_lu:E(_lt);},_lv=function(_lw){var _lx=E(_lw);if(!_lx._){return _lx.a;}else{return new F(function(){return I_toNumber(_lx.a);});}},_ly=function(_lz){return new F(function(){return _lv(_lz);});},_lA=1,_lB=-1,_lC=function(_lD){var _lE=E(_lD);return (_lE<=0)?(_lE>=0)?E(_lE):E(_lB):E(_lA);},_lF=function(_lG,_lH){return E(_lG)-E(_lH);},_lI=function(_lJ){return  -E(_lJ);},_lK=function(_lL,_lM){return E(_lL)+E(_lM);},_lN=function(_lO,_lP){return E(_lO)*E(_lP);},_lQ={_:0,a:_lK,b:_lF,c:_lN,d:_lI,e:_lr,f:_lC,g:_ly},_lR=function(_lS,_lT){return E(_lS)/E(_lT);},_lU=new T4(0,_lQ,_lR,_lp,_lm),_lV=function(_lW){return new F(function(){return Math.acos(E(_lW));});},_lX=function(_lY){return new F(function(){return Math.asin(E(_lY));});},_lZ=function(_m0){return new F(function(){return Math.atan(E(_m0));});},_m1=function(_m2){return new F(function(){return Math.cos(E(_m2));});},_m3=function(_m4){return new F(function(){return cosh(E(_m4));});},_m5=function(_m6){return new F(function(){return Math.exp(E(_m6));});},_m7=function(_m8){return new F(function(){return Math.log(E(_m8));});},_m9=function(_ma,_mb){return new F(function(){return Math.pow(E(_ma),E(_mb));});},_mc=function(_md){return new F(function(){return Math.sin(E(_md));});},_me=function(_mf){return new F(function(){return sinh(E(_mf));});},_mg=function(_mh){return new F(function(){return Math.sqrt(E(_mh));});},_mi=function(_mj){return new F(function(){return Math.tan(E(_mj));});},_mk=function(_ml){return new F(function(){return tanh(E(_ml));});},_mm={_:0,a:_lU,b:_ll,c:_m5,d:_m7,e:_mg,f:_m9,g:_li,h:_mc,i:_m1,j:_mi,k:_lX,l:_lV,m:_lZ,n:_me,o:_m3,p:_mk,q:_lc,r:_l9,s:_lf},_mn="flipped2",_mo="flipped1",_mp="c1y",_mq="c1x",_mr="w2z",_ms="w2y",_mt="w2x",_mu="w1z",_mv="w1y",_mw="w1x",_mx="d2z",_my="d2y",_mz="d2x",_mA="d1z",_mB="d1y",_mC="d1x",_mD="c2y",_mE="c2x",_mF=function(_mG,_){var _mH=__get(_mG,E(_mw)),_mI=__get(_mG,E(_mv)),_mJ=__get(_mG,E(_mu)),_mK=__get(_mG,E(_mt)),_mL=__get(_mG,E(_ms)),_mM=__get(_mG,E(_mr)),_mN=__get(_mG,E(_mq)),_mO=__get(_mG,E(_mp)),_mP=__get(_mG,E(_mE)),_mQ=__get(_mG,E(_mD)),_mR=__get(_mG,E(_mC)),_mS=__get(_mG,E(_mB)),_mT=__get(_mG,E(_mA)),_mU=__get(_mG,E(_mz)),_mV=__get(_mG,E(_my)),_mW=__get(_mG,E(_mx)),_mX=__get(_mG,E(_mo)),_mY=__get(_mG,E(_mn));return {_:0,a:E(new T3(0,E(_mH),E(_mI),E(_mJ))),b:E(new T3(0,E(_mK),E(_mL),E(_mM))),c:E(new T2(0,E(_mN),E(_mO))),d:E(new T2(0,E(_mP),E(_mQ))),e:E(new T3(0,E(_mR),E(_mS),E(_mT))),f:E(new T3(0,E(_mU),E(_mV),E(_mW))),g:E(_mX),h:E(_mY)};},_mZ=function(_n0,_){var _n1=E(_n0);if(!_n1._){return _w;}else{var _n2=B(_mF(E(_n1.a),_)),_n3=B(_mZ(_n1.b,_));return new T2(1,_n2,_n3);}},_n4=function(_n5){var _n6=E(_n5);return (E(_n6.b)-E(_n6.a)|0)+1|0;},_n7=function(_n8,_n9){var _na=E(_n8),_nb=E(_n9);return (E(_na.a)>_nb)?false:_nb<=E(_na.b);},_nc=function(_nd){return new F(function(){return _kG(0,E(_nd),_w);});},_ne=function(_nf,_ng,_nh){return new F(function(){return _kG(E(_nf),E(_ng),_nh);});},_ni=function(_nj,_nk){return new F(function(){return _kG(0,E(_nj),_nk);});},_nl=function(_nm,_nn){return new F(function(){return _2J(_ni,_nm,_nn);});},_no=new T3(0,_ne,_nc,_nl),_np=0,_nq=function(_nr,_ns,_nt){return new F(function(){return A1(_nr,new T2(1,_2G,new T(function(){return B(A1(_ns,_nt));})));});},_nu=new T(function(){return B(unCStr(": empty list"));}),_nv=new T(function(){return B(unCStr("Prelude."));}),_nw=function(_nx){return new F(function(){return err(B(_n(_nv,new T(function(){return B(_n(_nx,_nu));},1))));});},_ny=new T(function(){return B(unCStr("foldr1"));}),_nz=new T(function(){return B(_nw(_ny));}),_nA=function(_nB,_nC){var _nD=E(_nC);if(!_nD._){return E(_nz);}else{var _nE=_nD.a,_nF=E(_nD.b);if(!_nF._){return E(_nE);}else{return new F(function(){return A2(_nB,_nE,new T(function(){return B(_nA(_nB,_nF));}));});}}},_nG=new T(function(){return B(unCStr(" out of range "));}),_nH=new T(function(){return B(unCStr("}.index: Index "));}),_nI=new T(function(){return B(unCStr("Ix{"));}),_nJ=new T2(1,_78,_w),_nK=new T2(1,_78,_nJ),_nL=0,_nM=function(_nN){return E(E(_nN).a);},_nO=function(_nP,_nQ,_nR,_nS,_nT){var _nU=new T(function(){var _nV=new T(function(){var _nW=new T(function(){var _nX=new T(function(){var _nY=new T(function(){return B(A3(_nA,_nq,new T2(1,new T(function(){return B(A3(_nM,_nR,_nL,_nS));}),new T2(1,new T(function(){return B(A3(_nM,_nR,_nL,_nT));}),_w)),_nK));});return B(_n(_nG,new T2(1,_79,new T2(1,_79,_nY))));});return B(A(_nM,[_nR,_np,_nQ,new T2(1,_78,_nX)]));});return B(_n(_nH,new T2(1,_79,_nW)));},1);return B(_n(_nP,_nV));},1);return new F(function(){return err(B(_n(_nI,_nU)));});},_nZ=function(_o0,_o1,_o2,_o3,_o4){return new F(function(){return _nO(_o0,_o1,_o4,_o2,_o3);});},_o5=function(_o6,_o7,_o8,_o9){var _oa=E(_o8);return new F(function(){return _nZ(_o6,_o7,_oa.a,_oa.b,_o9);});},_ob=function(_oc,_od,_oe,_of){return new F(function(){return _o5(_of,_oe,_od,_oc);});},_og=new T(function(){return B(unCStr("Int"));}),_oh=function(_oi,_oj){return new F(function(){return _ob(_no,_oj,_oi,_og);});},_ok=function(_ol,_om){var _on=E(_ol),_oo=E(_on.a),_op=E(_om);if(_oo>_op){return new F(function(){return _oh(_op,_on);});}else{if(_op>E(_on.b)){return new F(function(){return _oh(_op,_on);});}else{return _op-_oo|0;}}},_oq=function(_or,_os){if(_or<=_os){var _ot=function(_ou){return new T2(1,_ou,new T(function(){if(_ou!=_os){return B(_ot(_ou+1|0));}else{return __Z;}}));};return new F(function(){return _ot(_or);});}else{return __Z;}},_ov=function(_ow,_ox){return new F(function(){return _oq(E(_ow),E(_ox));});},_oy=function(_oz){var _oA=E(_oz);return new F(function(){return _ov(_oA.a,_oA.b);});},_oB=function(_oC){var _oD=E(_oC),_oE=E(_oD.a),_oF=E(_oD.b);return (_oE>_oF)?E(_np):(_oF-_oE|0)+1|0;},_oG=function(_oH,_oI){return E(_oH)-E(_oI)|0;},_oJ=function(_oK,_oL){return new F(function(){return _oG(_oL,E(_oK).a);});},_oM=function(_oN,_oO){return E(_oN)==E(_oO);},_oP=function(_oQ,_oR){return E(_oQ)!=E(_oR);},_oS=new T2(0,_oM,_oP),_oT=function(_oU,_oV){var _oW=E(_oU),_oX=E(_oV);return (_oW>_oX)?E(_oW):E(_oX);},_oY=function(_oZ,_p0){var _p1=E(_oZ),_p2=E(_p0);return (_p1>_p2)?E(_p2):E(_p1);},_p3=function(_p4,_p5){return (_p4>=_p5)?(_p4!=_p5)?2:1:0;},_p6=function(_p7,_p8){return new F(function(){return _p3(E(_p7),E(_p8));});},_p9=function(_pa,_pb){return E(_pa)>=E(_pb);},_pc=function(_pd,_pe){return E(_pd)>E(_pe);},_pf=function(_pg,_ph){return E(_pg)<=E(_ph);},_pi=function(_pj,_pk){return E(_pj)<E(_pk);},_pl={_:0,a:_oS,b:_p6,c:_pi,d:_pf,e:_pc,f:_p9,g:_oT,h:_oY},_pm={_:0,a:_pl,b:_oy,c:_ok,d:_oJ,e:_n7,f:_oB,g:_n4},_pn=function(_po,_pp,_){while(1){var _pq=B((function(_pr,_ps,_){var _pt=E(_pr);if(!_pt._){return new T2(0,_kl,_ps);}else{var _pu=B(A2(_pt.a,_ps,_));_po=_pt.b;_pp=new T(function(){return E(E(_pu).b);});return __continue;}})(_po,_pp,_));if(_pq!=__continue){return _pq;}}},_pv=function(_pw,_px){return new T2(1,_pw,_px);},_py=function(_pz,_pA){var _pB=E(_pA);return new T2(0,_pB.a,_pB.b);},_pC=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_pD=new T(function(){return B(err(_pC));}),_pE=new T(function(){return B(unCStr("Negative range size"));}),_pF=new T(function(){return B(err(_pE));}),_pG=function(_pH){return E(E(_pH).f);},_pI=function(_pJ){var _pK=B(A1(_pJ,_));return E(_pK);},_pL=function(_pM,_pN,_pO){var _pP=E(_pN),_pQ=_pP.a,_pR=_pP.b,_pS=function(_){var _pT=B(A2(_pG,_pM,_pP));if(_pT>=0){var _pU=newArr(_pT,_pD),_pV=_pU,_pW=E(_pT);if(!_pW){return new T(function(){return new T4(0,E(_pQ),E(_pR),0,_pV);});}else{var _pX=function(_pY,_pZ,_){while(1){var _q0=E(_pY);if(!_q0._){return E(_);}else{var _=_pV[_pZ]=_q0.a;if(_pZ!=(_pW-1|0)){var _q1=_pZ+1|0;_pY=_q0.b;_pZ=_q1;continue;}else{return E(_);}}}},_=B(_pX(_pO,0,_));return new T(function(){return new T4(0,E(_pQ),E(_pR),_pW,_pV);});}}else{return E(_pF);}};return new F(function(){return _pI(_pS);});},_q2=function(_q3,_q4,_q5,_q6){var _q7=new T(function(){var _q8=E(_q6),_q9=_q8.c-1|0,_qa=new T(function(){return B(A2(_g0,_q4,_w));});if(0<=_q9){var _qb=new T(function(){return B(_84(_q4));}),_qc=function(_qd){var _qe=new T(function(){var _qf=new T(function(){return B(A1(_q5,new T(function(){return E(_q8.d[_qd]);})));});return B(A3(_86,_qb,_pv,_qf));});return new F(function(){return A3(_ci,_q4,_qe,new T(function(){if(_qd!=_q9){return B(_qc(_qd+1|0));}else{return E(_qa);}}));});};return B(_qc(0));}else{return E(_qa);}}),_qg=new T(function(){return B(_py(_q3,_q6));});return new F(function(){return A3(_86,B(_84(_q4)),function(_qh){return new F(function(){return _pL(_q3,_qg,_qh);});},_q7);});},_qi=function(_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr){var _qs=B(_bh(_qj));return new T2(0,new T3(0,E(B(A1(B(A1(_qs,_qk)),_qo))),E(B(A1(B(A1(_qs,_ql)),_qp))),E(B(A1(B(A1(_qs,_qm)),_qq)))),B(A1(B(A1(_qs,_qn)),_qr)));},_qt=function(_qu,_qv,_qw,_qx,_qy,_qz,_qA,_qB,_qC){var _qD=B(_6Q(_qu));return new T2(0,new T3(0,E(B(A1(B(A1(_qD,_qv)),_qz))),E(B(A1(B(A1(_qD,_qw)),_qA))),E(B(A1(B(A1(_qD,_qx)),_qB)))),B(A1(B(A1(_qD,_qy)),_qC)));},_qE=function(_qF,_qG){return (E(_qF)!=E(_qG))?true:false;},_qH=function(_qI,_qJ){return E(_qI)==E(_qJ);},_qK=new T2(0,_qH,_qE),_qL=function(_qM,_qN){return E(_qM)<E(_qN);},_qO=function(_qP,_qQ){return E(_qP)<=E(_qQ);},_qR=function(_qS,_qT){return E(_qS)>E(_qT);},_qU=function(_qV,_qW){return E(_qV)>=E(_qW);},_qX=function(_qY,_qZ){var _r0=E(_qY),_r1=E(_qZ);return (_r0>=_r1)?(_r0!=_r1)?2:1:0;},_r2=function(_r3,_r4){var _r5=E(_r3),_r6=E(_r4);return (_r5>_r6)?E(_r5):E(_r6);},_r7=function(_r8,_r9){var _ra=E(_r8),_rb=E(_r9);return (_ra>_rb)?E(_rb):E(_ra);},_rc={_:0,a:_qK,b:_qX,c:_qL,d:_qO,e:_qR,f:_qU,g:_r2,h:_r7},_rd="dz",_re="wy",_rf="wx",_rg="dy",_rh="dx",_ri="t",_rj="a",_rk="r",_rl="ly",_rm="lx",_rn="wz",_ro=function(_rp,_rq,_rr,_rs,_rt,_ru,_rv,_rw,_rx){return new F(function(){return _km(new T2(1,new T2(0,_rf,_rp),new T2(1,new T2(0,_re,_rq),new T2(1,new T2(0,_rn,_rr),new T2(1,new T2(0,_rm,_rs*_rt*Math.cos(_ru)),new T2(1,new T2(0,_rl,_rs*_rt*Math.sin(_ru)),new T2(1,new T2(0,_rk,_rs),new T2(1,new T2(0,_rj,_rt),new T2(1,new T2(0,_ri,_ru),new T2(1,new T2(0,_rh,_rv),new T2(1,new T2(0,_rg,_rw),new T2(1,new T2(0,_rd,_rx),_w))))))))))));});},_ry=function(_rz){var _rA=E(_rz),_rB=E(_rA.a),_rC=E(_rA.b),_rD=E(_rA.d);return new F(function(){return _ro(_rB.a,_rB.b,_rB.c,E(_rC.a),E(_rC.b),E(_rA.c),_rD.a,_rD.b,_rD.c);});},_rE=function(_rF,_rG){var _rH=E(_rG);return (_rH._==0)?__Z:new T2(1,new T(function(){return B(A1(_rF,_rH.a));}),new T(function(){return B(_rE(_rF,_rH.b));}));},_rI=function(_rJ,_rK,_rL){var _rM=__lst2arr(B(_rE(_ry,new T2(1,_rJ,new T2(1,_rK,new T2(1,_rL,_w))))));return E(_rM);},_rN=function(_rO){var _rP=E(_rO);return new F(function(){return _rI(_rP.a,_rP.b,_rP.c);});},_rQ=new T2(0,_mm,_rc),_rR=function(_rS,_rT,_rU,_rV){var _rW=B(_80(_rS)),_rX=new T(function(){return B(A2(_bv,_rS,new T(function(){return B(_bj(_rS,_rT,_rU,_rV,_rT,_rU,_rV));})));});return new T3(0,B(A3(_cg,_rW,_rT,_rX)),B(A3(_cg,_rW,_rU,_rX)),B(A3(_cg,_rW,_rV,_rX)));},_rY=function(_rZ,_s0,_s1,_s2,_s3,_s4,_s5){var _s6=B(_bh(_rZ));return new T3(0,B(A1(B(A1(_s6,_s0)),_s3)),B(A1(B(A1(_s6,_s1)),_s4)),B(A1(B(A1(_s6,_s2)),_s5)));},_s7=function(_s8,_s9,_sa,_sb,_sc,_sd,_se){var _sf=B(_6Q(_s8));return new T3(0,B(A1(B(A1(_sf,_s9)),_sc)),B(A1(B(A1(_sf,_sa)),_sd)),B(A1(B(A1(_sf,_sb)),_se)));},_sg=function(_sh,_si){var _sj=new T(function(){return E(E(_sh).a);}),_sk=new T(function(){return B(A2(_jR,new T2(0,_sj,new T(function(){return E(E(_sh).b);})),_si));}),_sl=new T(function(){var _sm=E(_sk),_sn=B(_rR(_sj,_sm.a,_sm.b,_sm.c));return new T3(0,E(_sn.a),E(_sn.b),E(_sn.c));}),_so=new T(function(){var _sp=E(_si),_sq=E(_sl),_sr=B(_80(_sj)),_ss=new T(function(){return B(A2(_bv,_sj,new T(function(){var _st=E(_sk),_su=_st.a,_sv=_st.b,_sw=_st.c;return B(_bj(_sj,_su,_sv,_sw,_su,_sv,_sw));})));}),_sx=B(A3(_cg,_sr,new T(function(){return B(_bx(_sj,_sp));}),_ss)),_sy=B(_82(_sr)),_sz=B(_rY(_sy,_sq.a,_sq.b,_sq.c,_sx,_sx,_sx)),_sA=B(_6S(_sy)),_sB=B(_s7(_sy,_sp.a,_sp.b,_sp.c,B(A1(_sA,_sz.a)),B(A1(_sA,_sz.b)),B(A1(_sA,_sz.c))));return new T3(0,E(_sB.a),E(_sB.b),E(_sB.c));});return new T2(0,_so,_sl);},_sC=function(_sD){return E(E(_sD).a);},_sE=function(_sF,_sG,_sH,_sI,_sJ,_sK,_sL){var _sM=B(_bj(_sF,_sJ,_sK,_sL,_sG,_sH,_sI)),_sN=B(_82(B(_80(_sF)))),_sO=B(_rY(_sN,_sJ,_sK,_sL,_sM,_sM,_sM)),_sP=B(_6S(_sN));return new F(function(){return _s7(_sN,_sG,_sH,_sI,B(A1(_sP,_sO.a)),B(A1(_sP,_sO.b)),B(A1(_sP,_sO.c)));});},_sQ=function(_sR){return E(E(_sR).a);},_sS=function(_sT,_sU,_sV,_sW){var _sX=new T(function(){var _sY=E(_sW),_sZ=E(_sV),_t0=B(_sE(_sT,_sY.a,_sY.b,_sY.c,_sZ.a,_sZ.b,_sZ.c));return new T3(0,E(_t0.a),E(_t0.b),E(_t0.c));}),_t1=new T(function(){return B(A2(_bv,_sT,new T(function(){var _t2=E(_sX),_t3=_t2.a,_t4=_t2.b,_t5=_t2.c;return B(_bj(_sT,_t3,_t4,_t5,_t3,_t4,_t5));})));});if(!B(A3(_sQ,B(_sC(_sU)),_t1,new T(function(){return B(A2(_7U,B(_82(B(_80(_sT)))),_7S));})))){var _t6=E(_sX),_t7=B(_rR(_sT,_t6.a,_t6.b,_t6.c)),_t8=B(A2(_bv,_sT,new T(function(){var _t9=E(_sW),_ta=_t9.a,_tb=_t9.b,_tc=_t9.c;return B(_bj(_sT,_ta,_tb,_tc,_ta,_tb,_tc));}))),_td=B(_bh(new T(function(){return B(_82(new T(function(){return B(_80(_sT));})));})));return new T3(0,B(A1(B(A1(_td,_t7.a)),_t8)),B(A1(B(A1(_td,_t7.b)),_t8)),B(A1(B(A1(_td,_t7.c)),_t8)));}else{var _te=B(A2(_7U,B(_82(B(_80(_sT)))),_7S));return new T3(0,_te,_te,_te);}},_tf=0,_tg=new T3(0,E(_tf),E(_tf),E(_tf)),_th=function(_ti,_tj){while(1){var _tk=E(_ti);if(!_tk._){return E(_tj);}else{var _tl=_tk.b,_tm=E(_tk.a);if(_tj>_tm){_ti=_tl;continue;}else{_ti=_tl;_tj=_tm;continue;}}}},_tn=new T(function(){var _to=eval("angleCount"),_tp=Number(_to);return jsTrunc(_tp);}),_tq=new T(function(){return E(_tn);}),_tr=new T(function(){return B(unCStr("head"));}),_ts=new T(function(){return B(_nw(_tr));}),_tt=function(_tu,_tv,_tw){var _tx=E(_tu);if(!_tx._){return __Z;}else{var _ty=E(_tv);if(!_ty._){return __Z;}else{var _tz=_ty.a,_tA=E(_tw);if(!_tA._){return __Z;}else{var _tB=E(_tA.a),_tC=_tB.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_tx.a),E(_tz),E(_tC));}),new T2(1,new T(function(){return new T3(0,E(_tz),E(_tC),E(_tB.b));}),_w)),new T(function(){return B(_tt(_tx.b,_ty.b,_tA.b));},1));});}}}},_tD=new T(function(){return B(unCStr("tail"));}),_tE=new T(function(){return B(_nw(_tD));}),_tF=function(_tG,_tH){var _tI=E(_tG);if(!_tI._){return __Z;}else{var _tJ=E(_tH);return (_tJ._==0)?__Z:new T2(1,new T2(0,_tI.a,_tJ.a),new T(function(){return B(_tF(_tI.b,_tJ.b));}));}},_tK=function(_tL,_tM){var _tN=E(_tL);if(!_tN._){return __Z;}else{var _tO=E(_tM);if(!_tO._){return __Z;}else{var _tP=E(_tN.a),_tQ=_tP.b,_tR=E(_tO.a).b,_tS=new T(function(){var _tT=new T(function(){return B(_tF(_tR,new T(function(){var _tU=E(_tR);if(!_tU._){return E(_tE);}else{return E(_tU.b);}},1)));},1);return B(_tt(_tQ,new T(function(){var _tV=E(_tQ);if(!_tV._){return E(_tE);}else{return E(_tV.b);}},1),_tT));});return new F(function(){return _n(new T2(1,new T(function(){var _tW=E(_tQ);if(!_tW._){return E(_ts);}else{var _tX=E(_tR);if(!_tX._){return E(_ts);}else{return new T3(0,E(_tP.a),E(_tW.a),E(_tX.a));}}}),_tS),new T(function(){return B(_tK(_tN.b,_tO.b));},1));});}}},_tY=new T(function(){return 6.283185307179586/E(_tq);}),_tZ=new T(function(){return E(_tq)-1;}),_u0=new T1(0,1),_u1=function(_u2,_u3){var _u4=E(_u3),_u5=new T(function(){var _u6=B(_82(_u2)),_u7=B(_u1(_u2,B(A3(_6Q,_u6,_u4,new T(function(){return B(A2(_7U,_u6,_u0));})))));return new T2(1,_u7.a,_u7.b);});return new T2(0,_u4,_u5);},_u8=function(_u9){return E(E(_u9).d);},_ua=new T1(0,2),_ub=function(_uc,_ud){var _ue=E(_ud);if(!_ue._){return __Z;}else{var _uf=_ue.a;return (!B(A1(_uc,_uf)))?__Z:new T2(1,_uf,new T(function(){return B(_ub(_uc,_ue.b));}));}},_ug=function(_uh,_ui,_uj,_uk){var _ul=B(_u1(_ui,_uj)),_um=new T(function(){var _un=B(_82(_ui)),_uo=new T(function(){return B(A3(_cg,_ui,new T(function(){return B(A2(_7U,_un,_u0));}),new T(function(){return B(A2(_7U,_un,_ua));})));});return B(A3(_6Q,_un,_uk,_uo));});return new F(function(){return _ub(function(_up){return new F(function(){return A3(_u8,_uh,_up,_um);});},new T2(1,_ul.a,_ul.b));});},_uq=new T(function(){return B(_ug(_rc,_lU,_tf,_tZ));}),_ur=function(_us,_ut){while(1){var _uu=E(_us);if(!_uu._){return E(_ut);}else{_us=_uu.b;_ut=_uu.a;continue;}}},_uv=new T(function(){return B(unCStr("last"));}),_uw=new T(function(){return B(_nw(_uv));}),_ux=function(_uy){return new F(function(){return _ur(_uy,_uw);});},_uz=function(_uA){return new F(function(){return _ux(E(_uA).b);});},_uB=new T(function(){return B(unCStr("maximum"));}),_uC=new T(function(){return B(_nw(_uB));}),_uD=new T(function(){var _uE=eval("proceedCount"),_uF=Number(_uE);return jsTrunc(_uF);}),_uG=new T(function(){return E(_uD);}),_uH=1,_uI=new T(function(){return B(_ug(_rc,_lU,_uH,_uG));}),_uJ=function(_uK,_uL,_uM,_uN,_uO,_uP,_uQ,_uR,_uS,_uT,_uU,_uV,_uW,_uX){var _uY=new T(function(){var _uZ=new T(function(){var _v0=E(_uT),_v1=E(_uX),_v2=E(_uW),_v3=E(_uU),_v4=E(_uV),_v5=E(_uS);return new T3(0,_v0*_v1-_v2*_v3,_v3*_v4-_v1*_v5,_v5*_v2-_v4*_v0);}),_v6=function(_v7){var _v8=new T(function(){var _v9=E(_v7)/E(_tq);return (_v9+_v9)*3.141592653589793;}),_va=new T(function(){return B(A1(_uK,_v8));}),_vb=new T(function(){var _vc=new T(function(){var _vd=E(_va)/E(_uG);return new T3(0,E(_vd),E(_vd),E(_vd));}),_ve=function(_vf,_vg){var _vh=E(_vf);if(!_vh._){return new T2(0,_w,_vg);}else{var _vi=new T(function(){var _vj=B(_sg(_rQ,new T(function(){var _vk=E(_vg),_vl=E(_vk.a),_vm=E(_vk.b),_vn=E(_vc);return new T3(0,E(_vl.a)+E(_vm.a)*E(_vn.a),E(_vl.b)+E(_vm.b)*E(_vn.b),E(_vl.c)+E(_vm.c)*E(_vn.c));}))),_vo=_vj.a,_vp=new T(function(){var _vq=E(_vj.b),_vr=E(E(_vg).b),_vs=B(_sE(_mm,_vr.a,_vr.b,_vr.c,_vq.a,_vq.b,_vq.c)),_vt=B(_rR(_mm,_vs.a,_vs.b,_vs.c));return new T3(0,E(_vt.a),E(_vt.b),E(_vt.c));});return new T2(0,new T(function(){var _vu=E(_va),_vv=E(_v8);return new T4(0,E(_vo),E(new T2(0,E(_vh.a)/E(_uG),E(_vu))),E(_vv),E(_vp));}),new T2(0,_vo,_vp));}),_vw=new T(function(){var _vx=B(_ve(_vh.b,new T(function(){return E(E(_vi).b);})));return new T2(0,_vx.a,_vx.b);});return new T2(0,new T2(1,new T(function(){return E(E(_vi).a);}),new T(function(){return E(E(_vw).a);})),new T(function(){return E(E(_vw).b);}));}},_vy=function(_vz,_vA,_vB,_vC,_vD){var _vE=E(_vz);if(!_vE._){return new T2(0,_w,new T2(0,new T3(0,E(_vA),E(_vB),E(_vC)),_vD));}else{var _vF=new T(function(){var _vG=B(_sg(_rQ,new T(function(){var _vH=E(_vD),_vI=E(_vc);return new T3(0,E(_vA)+E(_vH.a)*E(_vI.a),E(_vB)+E(_vH.b)*E(_vI.b),E(_vC)+E(_vH.c)*E(_vI.c));}))),_vJ=_vG.a,_vK=new T(function(){var _vL=E(_vG.b),_vM=E(_vD),_vN=B(_sE(_mm,_vM.a,_vM.b,_vM.c,_vL.a,_vL.b,_vL.c)),_vO=B(_rR(_mm,_vN.a,_vN.b,_vN.c));return new T3(0,E(_vO.a),E(_vO.b),E(_vO.c));});return new T2(0,new T(function(){var _vP=E(_va),_vQ=E(_v8);return new T4(0,E(_vJ),E(new T2(0,E(_vE.a)/E(_uG),E(_vP))),E(_vQ),E(_vK));}),new T2(0,_vJ,_vK));}),_vR=new T(function(){var _vS=B(_ve(_vE.b,new T(function(){return E(E(_vF).b);})));return new T2(0,_vS.a,_vS.b);});return new T2(0,new T2(1,new T(function(){return E(E(_vF).a);}),new T(function(){return E(E(_vR).a);})),new T(function(){return E(E(_vR).b);}));}};return E(B(_vy(_uI,_uN,_uO,_uP,new T(function(){var _vT=E(_uZ),_vU=E(_v8)+_uQ,_vV=Math.cos(_vU),_vW=Math.sin(_vU);return new T3(0,E(_uS)*_vV+E(_vT.a)*_vW,E(_uT)*_vV+E(_vT.b)*_vW,E(_uU)*_vV+E(_vT.c)*_vW);}))).a);});return new T2(0,new T(function(){var _vX=E(_va),_vY=E(_v8);return new T4(0,E(new T3(0,E(_uN),E(_uO),E(_uP))),E(new T2(0,E(_tf),E(_vX))),E(_vY),E(_tg));}),_vb);};return B(_rE(_v6,_uq));}),_vZ=new T(function(){var _w0=function(_w1){return new F(function(){return A1(_uK,new T(function(){return B(_lN(_w1,_tY));}));});},_w2=B(_rE(_w0,_uq));if(!_w2._){return E(_uC);}else{return B(_th(_w2.b,E(_w2.a)));}}),_w3=new T(function(){var _w4=new T(function(){var _w5=B(_n(_uY,new T2(1,new T(function(){var _w6=E(_uY);if(!_w6._){return E(_ts);}else{return E(_w6.a);}}),_w)));if(!_w5._){return E(_tE);}else{return E(_w5.b);}},1);return B(_tK(_uY,_w4));});return new T3(0,_w3,new T(function(){return B(_rE(_uz,_uY));}),_vZ);},_w7=function(_w8,_w9,_wa,_wb,_wc,_wd,_we,_wf,_wg,_wh,_wi,_wj,_wk,_wl,_wm,_wn,_wo,_wp){var _wq=B(_sg(_rQ,new T3(0,E(_wb),E(_wc),E(_wd)))),_wr=_wq.b,_ws=E(_wq.a),_wt=B(_sS(_mm,_rc,_wr,new T3(0,E(_wf),E(_wg),E(_wh)))),_wu=E(_wr),_wv=_wu.a,_ww=_wu.b,_wx=_wu.c,_wy=B(_sE(_mm,_wj,_wk,_wl,_wv,_ww,_wx)),_wz=B(_rR(_mm,_wy.a,_wy.b,_wy.c)),_wA=_wz.a,_wB=_wz.b,_wC=_wz.c,_wD=E(_we),_wE=new T2(0,E(new T3(0,E(_wt.a),E(_wt.b),E(_wt.c))),E(_wi)),_wF=B(_uJ(_w8,_w9,_wa,_ws.a,_ws.b,_ws.c,_wD,_wE,_wA,_wB,_wC,_wv,_ww,_wx)),_wG=__lst2arr(B(_rE(_rN,_wF.a))),_wH=__lst2arr(B(_rE(_ry,_wF.b)));return {_:0,a:_w8,b:_w9,c:_wa,d:new T2(0,E(_ws),E(_wD)),e:_wE,f:new T3(0,E(_wA),E(_wB),E(_wC)),g:_wu,h:_wG,i:_wH,j:E(_wF.c)};},_wI=1.0e-2,_wJ=function(_wK,_wL,_wM,_wN,_wO,_wP,_wQ,_wR,_wS,_wT,_wU,_wV,_wW,_wX,_wY,_wZ,_x0,_x1){var _x2=B(_qi(_lQ,_wR,_wS,_wT,_wU,_wI,_wI,_wI,_wI)),_x3=E(_x2.a),_x4=B(_qt(_lQ,_wN,_wO,_wP,_wQ,_x3.a,_x3.b,_x3.c,_x2.b)),_x5=E(_x4.a);return new F(function(){return _w7(_wK,_wL,_wM,_x5.a,_x5.b,_x5.c,_x4.b,_wR,_wS,_wT,_wU,_wV,_wW,_wX,_wY,_wZ,_x0,_x1);});},_x6=function(_x7){var _x8=E(_x7),_x9=E(_x8.d),_xa=E(_x9.a),_xb=E(_x8.e),_xc=E(_xb.a),_xd=E(_x8.f),_xe=B(_wJ(_x8.a,_x8.b,_x8.c,_xa.a,_xa.b,_xa.c,_x9.b,_xc.a,_xc.b,_xc.c,_xb.b,_xd.a,_xd.b,_xd.c,_x8.g,_x8.h,_x8.i,_x8.j));return {_:0,a:E(_xe.a),b:E(_xe.b),c:E(_xe.c),d:E(_xe.d),e:E(_xe.e),f:E(_xe.f),g:E(_xe.g),h:_xe.h,i:_xe.i,j:_xe.j};},_xf=function(_xg,_xh,_xi,_xj,_xk,_xl,_xm,_xn,_xo){var _xp=B(_82(B(_80(_xg))));return new F(function(){return A3(_6Q,_xp,new T(function(){return B(_bj(_xg,_xh,_xi,_xj,_xl,_xm,_xn));}),new T(function(){return B(A3(_bh,_xp,_xk,_xo));}));});},_xq=new T(function(){return B(unCStr("base"));}),_xr=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_xs=new T(function(){return B(unCStr("IOException"));}),_xt=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_xq,_xr,_xs),_xu=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_xt,_w,_w),_xv=function(_xw){return E(_xu);},_xx=function(_xy){var _xz=E(_xy);return new F(function(){return _2g(B(_2e(_xz.a)),_xv,_xz.b);});},_xA=new T(function(){return B(unCStr(": "));}),_xB=new T(function(){return B(unCStr(")"));}),_xC=new T(function(){return B(unCStr(" ("));}),_xD=new T(function(){return B(unCStr("interrupted"));}),_xE=new T(function(){return B(unCStr("system error"));}),_xF=new T(function(){return B(unCStr("unsatisified constraints"));}),_xG=new T(function(){return B(unCStr("user error"));}),_xH=new T(function(){return B(unCStr("permission denied"));}),_xI=new T(function(){return B(unCStr("illegal operation"));}),_xJ=new T(function(){return B(unCStr("end of file"));}),_xK=new T(function(){return B(unCStr("resource exhausted"));}),_xL=new T(function(){return B(unCStr("resource busy"));}),_xM=new T(function(){return B(unCStr("does not exist"));}),_xN=new T(function(){return B(unCStr("already exists"));}),_xO=new T(function(){return B(unCStr("resource vanished"));}),_xP=new T(function(){return B(unCStr("timeout"));}),_xQ=new T(function(){return B(unCStr("unsupported operation"));}),_xR=new T(function(){return B(unCStr("hardware fault"));}),_xS=new T(function(){return B(unCStr("inappropriate type"));}),_xT=new T(function(){return B(unCStr("invalid argument"));}),_xU=new T(function(){return B(unCStr("failed"));}),_xV=new T(function(){return B(unCStr("protocol error"));}),_xW=function(_xX,_xY){switch(E(_xX)){case 0:return new F(function(){return _n(_xN,_xY);});break;case 1:return new F(function(){return _n(_xM,_xY);});break;case 2:return new F(function(){return _n(_xL,_xY);});break;case 3:return new F(function(){return _n(_xK,_xY);});break;case 4:return new F(function(){return _n(_xJ,_xY);});break;case 5:return new F(function(){return _n(_xI,_xY);});break;case 6:return new F(function(){return _n(_xH,_xY);});break;case 7:return new F(function(){return _n(_xG,_xY);});break;case 8:return new F(function(){return _n(_xF,_xY);});break;case 9:return new F(function(){return _n(_xE,_xY);});break;case 10:return new F(function(){return _n(_xV,_xY);});break;case 11:return new F(function(){return _n(_xU,_xY);});break;case 12:return new F(function(){return _n(_xT,_xY);});break;case 13:return new F(function(){return _n(_xS,_xY);});break;case 14:return new F(function(){return _n(_xR,_xY);});break;case 15:return new F(function(){return _n(_xQ,_xY);});break;case 16:return new F(function(){return _n(_xP,_xY);});break;case 17:return new F(function(){return _n(_xO,_xY);});break;default:return new F(function(){return _n(_xD,_xY);});}},_xZ=new T(function(){return B(unCStr("}"));}),_y0=new T(function(){return B(unCStr("{handle: "));}),_y1=function(_y2,_y3,_y4,_y5,_y6,_y7){var _y8=new T(function(){var _y9=new T(function(){var _ya=new T(function(){var _yb=E(_y5);if(!_yb._){return E(_y7);}else{var _yc=new T(function(){return B(_n(_yb,new T(function(){return B(_n(_xB,_y7));},1)));},1);return B(_n(_xC,_yc));}},1);return B(_xW(_y3,_ya));}),_yd=E(_y4);if(!_yd._){return E(_y9);}else{return B(_n(_yd,new T(function(){return B(_n(_xA,_y9));},1)));}}),_ye=E(_y6);if(!_ye._){var _yf=E(_y2);if(!_yf._){return E(_y8);}else{var _yg=E(_yf.a);if(!_yg._){var _yh=new T(function(){var _yi=new T(function(){return B(_n(_xZ,new T(function(){return B(_n(_xA,_y8));},1)));},1);return B(_n(_yg.a,_yi));},1);return new F(function(){return _n(_y0,_yh);});}else{var _yj=new T(function(){var _yk=new T(function(){return B(_n(_xZ,new T(function(){return B(_n(_xA,_y8));},1)));},1);return B(_n(_yg.a,_yk));},1);return new F(function(){return _n(_y0,_yj);});}}}else{return new F(function(){return _n(_ye.a,new T(function(){return B(_n(_xA,_y8));},1));});}},_yl=function(_ym){var _yn=E(_ym);return new F(function(){return _y1(_yn.a,_yn.b,_yn.c,_yn.d,_yn.f,_w);});},_yo=function(_yp,_yq,_yr){var _ys=E(_yq);return new F(function(){return _y1(_ys.a,_ys.b,_ys.c,_ys.d,_ys.f,_yr);});},_yt=function(_yu,_yv){var _yw=E(_yu);return new F(function(){return _y1(_yw.a,_yw.b,_yw.c,_yw.d,_yw.f,_yv);});},_yx=function(_yy,_yz){return new F(function(){return _2J(_yt,_yy,_yz);});},_yA=new T3(0,_yo,_yl,_yx),_yB=new T(function(){return new T5(0,_xv,_yA,_yC,_xx,_yl);}),_yC=function(_yD){return new T2(0,_yB,_yD);},_yE=__Z,_yF=7,_yG=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_yH=new T6(0,_yE,_yF,_w,_yG,_yE,_yE),_yI=new T(function(){return B(_yC(_yH));}),_yJ=function(_){return new F(function(){return die(_yI);});},_yK=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_yL=new T6(0,_yE,_yF,_w,_yK,_yE,_yE),_yM=new T(function(){return B(_yC(_yL));}),_yN=function(_){return new F(function(){return die(_yM);});},_yO=function(_yP,_){return new T2(0,_w,_yP);},_yQ=0.6,_yR=1,_yS=new T(function(){return B(unCStr(")"));}),_yT=function(_yU,_yV){var _yW=new T(function(){var _yX=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_kG(0,_yU,_w)),_yS));})));},1);return B(_n(B(_kG(0,_yV,_w)),_yX));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_yW)));});},_yY=function(_yZ,_z0){var _z1=new T(function(){var _z2=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_kG(0,_z0,_w)),_yS));})));},1);return B(_n(B(_kG(0,_yZ,_w)),_z2));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_z1)));});},_z3=function(_z4){var _z5=E(_z4);if(!_z5._){return E(_yO);}else{var _z6=new T(function(){return B(_z3(_z5.b));}),_z7=function(_z8){var _z9=E(_z8);if(!_z9._){return E(_z6);}else{var _za=_z9.a,_zb=new T(function(){return B(_z7(_z9.b));}),_zc=new T(function(){return 0.1*E(E(_za).e)/1.0e-2;}),_zd=new T(function(){var _ze=E(_za);if(_ze.a!=_ze.b){return E(_yR);}else{return E(_yQ);}}),_zf=function(_zg,_){var _zh=E(_zg),_zi=_zh.c,_zj=_zh.d,_zk=E(_zh.a),_zl=E(_zh.b),_zm=E(_za),_zn=_zm.a,_zo=_zm.b,_zp=E(_zm.c),_zq=_zp.b,_zr=E(_zp.a),_zs=_zr.a,_zt=_zr.b,_zu=_zr.c,_zv=E(_zm.d),_zw=_zv.b,_zx=E(_zv.a),_zy=_zx.a,_zz=_zx.b,_zA=_zx.c;if(_zk>_zn){return new F(function(){return _yN(_);});}else{if(_zn>_zl){return new F(function(){return _yN(_);});}else{if(_zk>_zo){return new F(function(){return _yJ(_);});}else{if(_zo>_zl){return new F(function(){return _yJ(_);});}else{var _zB=_zn-_zk|0;if(0>_zB){return new F(function(){return _yT(_zi,_zB);});}else{if(_zB>=_zi){return new F(function(){return _yT(_zi,_zB);});}else{var _zC=E(_zj[_zB]),_zD=E(_zC.c),_zE=_zD.b,_zF=E(_zD.a),_zG=_zF.a,_zH=_zF.b,_zI=_zF.c,_zJ=E(_zC.e),_zK=E(_zJ.a),_zL=B(_qi(_lQ,_zs,_zt,_zu,_zq,_zG,_zH,_zI,_zE)),_zM=E(_zL.a),_zN=B(_qi(_lQ,_zM.a,_zM.b,_zM.c,_zL.b,_zs,_zt,_zu,_zq)),_zO=E(_zN.a),_zP=_zo-_zk|0;if(0>_zP){return new F(function(){return _yY(_zP,_zi);});}else{if(_zP>=_zi){return new F(function(){return _yY(_zP,_zi);});}else{var _zQ=E(_zj[_zP]),_zR=E(_zQ.c),_zS=_zR.b,_zT=E(_zR.a),_zU=_zT.a,_zV=_zT.b,_zW=_zT.c,_zX=E(_zQ.e),_zY=E(_zX.a),_zZ=B(_qi(_lQ,_zy,_zz,_zA,_zw,_zU,_zV,_zW,_zS)),_A0=E(_zZ.a),_A1=B(_qi(_lQ,_A0.a,_A0.b,_A0.c,_zZ.b,_zy,_zz,_zA,_zw)),_A2=E(_A1.a),_A3=E(_zO.a)+E(_zO.b)+E(_zO.c)+E(_zN.b)+E(_A2.a)+E(_A2.b)+E(_A2.c)+E(_A1.b);if(!_A3){var _A4=B(A2(_zb,_zh,_));return new T2(0,new T2(1,_kl,new T(function(){return E(E(_A4).a);})),new T(function(){return E(E(_A4).b);}));}else{var _A5=new T(function(){return  -((B(_xf(_mm,_zK.a,_zK.b,_zK.c,_zJ.b,_zs,_zt,_zu,_zq))-B(_xf(_mm,_zY.a,_zY.b,_zY.c,_zX.b,_zy,_zz,_zA,_zw))-E(_zc))/_A3);}),_A6=function(_A7,_A8,_A9,_Aa,_){var _Ab=new T(function(){var _Ac=function(_Ad,_Ae,_Af,_Ag,_Ah){if(_Ad>_zo){return E(_Ah);}else{if(_zo>_Ae){return E(_Ah);}else{var _Ai=function(_){var _Aj=newArr(_Af,_pD),_Ak=_Aj,_Al=function(_Am,_){while(1){if(_Am!=_Af){var _=_Ak[_Am]=_Ag[_Am],_An=_Am+1|0;_Am=_An;continue;}else{return E(_);}}},_=B(_Al(0,_)),_Ao=_zo-_Ad|0;if(0>_Ao){return new F(function(){return _yY(_Ao,_Af);});}else{if(_Ao>=_Af){return new F(function(){return _yY(_Ao,_Af);});}else{var _=_Ak[_Ao]=new T(function(){var _Ap=E(_Ag[_Ao]),_Aq=E(_Ap.e),_Ar=E(_Aq.a),_As=B(_qi(_lQ,_zU,_zV,_zW,_zS,_zy,_zz,_zA,_zw)),_At=E(_As.a),_Au=E(_A5)*E(_zd),_Av=B(_qi(_lQ,_At.a,_At.b,_At.c,_As.b,_Au,_Au,_Au,_Au)),_Aw=E(_Av.a),_Ax=B(_qt(_lQ,_Ar.a,_Ar.b,_Ar.c,_Aq.b, -E(_Aw.a), -E(_Aw.b), -E(_Aw.c), -E(_Av.b)));return {_:0,a:E(_Ap.a),b:E(_Ap.b),c:E(_Ap.c),d:E(_Ap.d),e:E(new T2(0,E(_Ax.a),E(_Ax.b))),f:E(_Ap.f),g:E(_Ap.g),h:_Ap.h,i:_Ap.i,j:_Ap.j};});return new T4(0,E(_Ad),E(_Ae),_Af,_Ak);}}};return new F(function(){return _pI(_Ai);});}}};if(_A7>_zn){return B(_Ac(_A7,_A8,_A9,_Aa,new T4(0,E(_A7),E(_A8),_A9,_Aa)));}else{if(_zn>_A8){return B(_Ac(_A7,_A8,_A9,_Aa,new T4(0,E(_A7),E(_A8),_A9,_Aa)));}else{var _Ay=function(_){var _Az=newArr(_A9,_pD),_AA=_Az,_AB=function(_AC,_){while(1){if(_AC!=_A9){var _=_AA[_AC]=_Aa[_AC],_AD=_AC+1|0;_AC=_AD;continue;}else{return E(_);}}},_=B(_AB(0,_)),_AE=_zn-_A7|0;if(0>_AE){return new F(function(){return _yT(_A9,_AE);});}else{if(_AE>=_A9){return new F(function(){return _yT(_A9,_AE);});}else{var _=_AA[_AE]=new T(function(){var _AF=E(_Aa[_AE]),_AG=E(_AF.e),_AH=E(_AG.a),_AI=B(_qi(_lQ,_zG,_zH,_zI,_zE,_zs,_zt,_zu,_zq)),_AJ=E(_AI.a),_AK=E(_A5)*E(_zd),_AL=B(_qi(_lQ,_AJ.a,_AJ.b,_AJ.c,_AI.b,_AK,_AK,_AK,_AK)),_AM=E(_AL.a),_AN=B(_qt(_lQ,_AH.a,_AH.b,_AH.c,_AG.b,_AM.a,_AM.b,_AM.c,_AL.b));return {_:0,a:E(_AF.a),b:E(_AF.b),c:E(_AF.c),d:E(_AF.d),e:E(new T2(0,E(_AN.a),E(_AN.b))),f:E(_AF.f),g:E(_AF.g),h:_AF.h,i:_AF.i,j:_AF.j};});return new T4(0,E(_A7),E(_A8),_A9,_AA);}}},_AO=B(_pI(_Ay));return B(_Ac(E(_AO.a),E(_AO.b),_AO.c,_AO.d,_AO));}}});return new T2(0,_kl,_Ab);};if(!E(_zm.f)){var _AP=B(_A6(_zk,_zl,_zi,_zj,_)),_AQ=B(A2(_zb,new T(function(){return E(E(_AP).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_AP).a);}),new T(function(){return E(E(_AQ).a);})),new T(function(){return E(E(_AQ).b);}));}else{if(E(_A5)<0){var _AR=B(A2(_zb,_zh,_));return new T2(0,new T2(1,_kl,new T(function(){return E(E(_AR).a);})),new T(function(){return E(E(_AR).b);}));}else{var _AS=B(_A6(_zk,_zl,_zi,_zj,_)),_AT=B(A2(_zb,new T(function(){return E(E(_AS).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_AS).a);}),new T(function(){return E(E(_AT).a);})),new T(function(){return E(E(_AT).b);}));}}}}}}}}}}}};return E(_zf);}};return new F(function(){return _z7(_z5.a);});}},_AU=function(_,_AV){var _AW=new T(function(){return B(_z3(E(_AV).a));}),_AX=function(_AY){var _AZ=E(_AY);return (_AZ==1)?E(new T2(1,_AW,_w)):new T2(1,_AW,new T(function(){return B(_AX(_AZ-1|0));}));},_B0=B(_pn(B(_AX(5)),new T(function(){return E(E(_AV).b);}),_)),_B1=new T(function(){return B(_q2(_pm,_l8,_x6,new T(function(){return E(E(_B0).b);})));});return new T2(0,_kl,_B1);},_B2=function(_B3,_B4,_B5,_B6,_B7){var _B8=B(_82(B(_80(_B3))));return new F(function(){return A3(_6Q,_B8,new T(function(){return B(A3(_bh,_B8,_B4,_B6));}),new T(function(){return B(A3(_bh,_B8,_B5,_B7));}));});},_B9=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Ba=new T6(0,_yE,_yF,_w,_B9,_yE,_yE),_Bb=new T(function(){return B(_yC(_Ba));}),_Bc=function(_){return new F(function(){return die(_Bb);});},_Bd=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Be=new T6(0,_yE,_yF,_w,_Bd,_yE,_yE),_Bf=new T(function(){return B(_yC(_Be));}),_Bg=function(_){return new F(function(){return die(_Bf);});},_Bh=false,_Bi=true,_Bj=function(_Bk){var _Bl=E(_Bk),_Bm=_Bl.b,_Bn=E(_Bl.d),_Bo=E(_Bl.e),_Bp=E(_Bo.a),_Bq=E(_Bl.g),_Br=B(A1(_Bm,_Bn.a)),_Bs=B(_sE(_mm,_Br.a,_Br.b,_Br.c,_Bq.a,_Bq.b,_Bq.c));return {_:0,a:E(_Bl.a),b:E(_Bm),c:E(_Bl.c),d:E(_Bn),e:E(new T2(0,E(new T3(0,E(_Bp.a)+E(_Bs.a)*1.0e-2,E(_Bp.b)+E(_Bs.b)*1.0e-2,E(_Bp.c)+E(_Bs.c)*1.0e-2)),E(_Bo.b))),f:E(_Bl.f),g:E(_Bq),h:_Bl.h,i:_Bl.i,j:_Bl.j};},_Bt=new T(function(){return eval("__strict(collideBound)");}),_Bu=new T(function(){return eval("__strict(mouseContact)");}),_Bv=new T(function(){return eval("__strict(collide)");}),_Bw=function(_Bx){var _By=E(_Bx);if(!_By._){return __Z;}else{return new F(function(){return _n(_By.a,new T(function(){return B(_Bw(_By.b));},1));});}},_Bz=0,_BA=new T3(0,E(_Bz),E(_Bz),E(_Bz)),_BB=new T2(0,E(_BA),E(_Bz)),_BC=new T2(0,_mm,_rc),_BD=new T(function(){return B(_jR(_BC));}),_BE=function(_BF,_){var _BG=B(_q2(_pm,_l8,_Bj,_BF)),_BH=E(_BG.a),_BI=E(_BG.b);if(_BH<=_BI){var _BJ=function(_BK,_BL,_BM,_BN,_BO,_){if(_BL>_BK){return new F(function(){return _Bg(_);});}else{if(_BK>_BM){return new F(function(){return _Bg(_);});}else{var _BP=new T(function(){var _BQ=_BK-_BL|0;if(0>_BQ){return B(_yY(_BQ,_BN));}else{if(_BQ>=_BN){return B(_yY(_BQ,_BN));}else{return E(_BO[_BQ]);}}}),_BR=function(_BS,_BT,_BU,_BV,_BW,_){var _BX=E(_BS);if(!_BX._){return new T2(0,_w,new T4(0,E(_BT),E(_BU),_BV,_BW));}else{var _BY=E(_BX.a);if(_BT>_BY){return new F(function(){return _Bc(_);});}else{if(_BY>_BU){return new F(function(){return _Bc(_);});}else{var _BZ=_BY-_BT|0;if(0>_BZ){return new F(function(){return _yT(_BV,_BZ);});}else{if(_BZ>=_BV){return new F(function(){return _yT(_BV,_BZ);});}else{var _C0=__app2(E(_Bv),B(_kw(E(_BP))),B(_kw(E(_BW[_BZ])))),_C1=__arr2lst(0,_C0),_C2=B(_mZ(_C1,_)),_C3=B(_BR(_BX.b,_BT,_BU,_BV,_BW,_)),_C4=new T(function(){var _C5=new T(function(){return _BK!=_BY;}),_C6=function(_C7){var _C8=E(_C7);if(!_C8._){return __Z;}else{var _C9=_C8.b,_Ca=E(_C8.a),_Cb=E(_Ca.b),_Cc=E(_Ca.a),_Cd=E(_Ca.c),_Ce=_Cd.a,_Cf=_Cd.b,_Cg=E(_Ca.e),_Ch=E(_Ca.d),_Ci=_Ch.a,_Cj=_Ch.b,_Ck=E(_Ca.f),_Cl=new T(function(){var _Cm=B(_rR(_mm,_Ck.a,_Ck.b,_Ck.c)),_Cn=Math.sqrt(B(_B2(_mm,_Ci,_Cj,_Ci,_Cj)));return new T3(0,_Cn*E(_Cm.a),_Cn*E(_Cm.b),_Cn*E(_Cm.c));}),_Co=new T(function(){var _Cp=B(_rR(_mm,_Cg.a,_Cg.b,_Cg.c)),_Cq=Math.sqrt(B(_B2(_mm,_Ce,_Cf,_Ce,_Cf)));return new T3(0,_Cq*E(_Cp.a),_Cq*E(_Cp.b),_Cq*E(_Cp.c));}),_Cr=new T(function(){var _Cs=B(A1(_BD,_Cb)),_Ct=B(_rR(_mm,_Cs.a,_Cs.b,_Cs.c));return new T3(0,E(_Ct.a),E(_Ct.b),E(_Ct.c));}),_Cu=new T(function(){var _Cv=B(A1(_BD,_Cc)),_Cw=B(_rR(_mm,_Cv.a,_Cv.b,_Cv.c));return new T3(0,E(_Cw.a),E(_Cw.b),E(_Cw.c));}),_Cx=E(_Cb.a)+ -E(_Cc.a),_Cy=E(_Cb.b)+ -E(_Cc.b),_Cz=E(_Cb.c)+ -E(_Cc.c),_CA=new T(function(){return Math.sqrt(B(_bj(_mm,_Cx,_Cy,_Cz,_Cx,_Cy,_Cz)));}),_CB=new T(function(){var _CC=1/E(_CA);return new T3(0,_Cx*_CC,_Cy*_CC,_Cz*_CC);}),_CD=new T(function(){if(!E(_Ca.g)){return E(_CB);}else{var _CE=E(_CB);return new T3(0,-1*E(_CE.a),-1*E(_CE.b),-1*E(_CE.c));}}),_CF=new T(function(){if(!E(_Ca.h)){return E(_CB);}else{var _CG=E(_CB);return new T3(0,-1*E(_CG.a),-1*E(_CG.b),-1*E(_CG.c));}});return (!E(_C5))?new T2(1,new T(function(){var _CH=E(_CD),_CI=E(_CH.b),_CJ=E(_CH.c),_CK=E(_CH.a),_CL=E(_Cu),_CM=E(_CL.c),_CN=E(_CL.b),_CO=E(_CL.a),_CP=E(_Co),_CQ=E(_CP.c),_CR=E(_CP.b),_CS=E(_CP.a),_CT=_CI*_CM-_CN*_CJ,_CU=_CJ*_CO-_CM*_CK,_CV=_CK*_CN-_CO*_CI,_CW=B(_bj(_mm,_CU*_CQ-_CR*_CV,_CV*_CS-_CQ*_CT,_CT*_CR-_CS*_CU,_CO,_CN,_CM));return new T6(0,_BK,_BY,E(new T2(0,E(new T3(0,E(_CT),E(_CU),E(_CV))),E(_CW))),E(_BB),_CA,_Bh);}),new T2(1,new T(function(){var _CX=E(_CF),_CY=E(_CX.b),_CZ=E(_CX.c),_D0=E(_CX.a),_D1=E(_Cr),_D2=E(_D1.c),_D3=E(_D1.b),_D4=E(_D1.a),_D5=E(_Cl),_D6=E(_D5.c),_D7=E(_D5.b),_D8=E(_D5.a),_D9=_CY*_D2-_D3*_CZ,_Da=_CZ*_D4-_D2*_D0,_Db=_D0*_D3-_D4*_CY,_Dc=B(_bj(_mm,_Da*_D6-_D7*_Db,_Db*_D8-_D6*_D9,_D9*_D7-_D8*_Da,_D4,_D3,_D2));return new T6(0,_BK,_BY,E(_BB),E(new T2(0,E(new T3(0,E(_D9),E(_Da),E(_Db))),E(_Dc))),_CA,_Bh);}),new T(function(){return B(_C6(_C9));}))):new T2(1,new T(function(){var _Dd=E(_CD),_De=E(_Dd.b),_Df=E(_Dd.c),_Dg=E(_Dd.a),_Dh=E(_Cu),_Di=_Dh.a,_Dj=_Dh.b,_Dk=_Dh.c,_Dl=B(_sE(_mm,_Dg,_De,_Df,_Di,_Dj,_Dk)),_Dm=E(_Co),_Dn=E(_Dm.c),_Do=E(_Dm.b),_Dp=E(_Dm.a),_Dq=B(_bj(_mm,_De*_Dn-_Do*_Df,_Df*_Dp-_Dn*_Dg,_Dg*_Do-_Dp*_De,_Di,_Dj,_Dk)),_Dr=E(_CF),_Ds=E(_Dr.b),_Dt=E(_Dr.c),_Du=E(_Dr.a),_Dv=E(_Cr),_Dw=_Dv.a,_Dx=_Dv.b,_Dy=_Dv.c,_Dz=B(_sE(_mm,_Du,_Ds,_Dt,_Dw,_Dx,_Dy)),_DA=E(_Cl),_DB=E(_DA.c),_DC=E(_DA.b),_DD=E(_DA.a),_DE=B(_bj(_mm,_Ds*_DB-_DC*_Dt,_Dt*_DD-_DB*_Du,_Du*_DC-_DD*_Ds,_Dw,_Dx,_Dy));return new T6(0,_BK,_BY,E(new T2(0,E(new T3(0,E(_Dl.a),E(_Dl.b),E(_Dl.c))),E(_Dq))),E(new T2(0,E(new T3(0,E(_Dz.a),E(_Dz.b),E(_Dz.c))),E(_DE))),_CA,_Bi);}),new T(function(){return B(_C6(_C9));}));}};return B(_C6(_C2));});return new T2(0,new T2(1,_C4,new T(function(){return E(E(_C3).a);})),new T(function(){return E(E(_C3).b);}));}}}}}},_DF=B(_BR(B(_oq(_BK,_BI)),_BL,_BM,_BN,_BO,_)),_DG=E(_BP),_DH=E(_DG.d).a,_DI=__app1(E(_Bt),B(_kw(_DG))),_DJ=__arr2lst(0,_DI),_DK=B(_mZ(_DJ,_)),_DL=__app1(E(_Bu),_BK),_DM=__arr2lst(0,_DL),_DN=B(_mZ(_DM,_));if(_BK!=_BI){var _DO=E(_DF),_DP=E(_DO.b),_DQ=B(_BJ(_BK+1|0,E(_DP.a),E(_DP.b),_DP.c,_DP.d,_)),_DR=new T(function(){var _DS=new T(function(){var _DT=B(A1(_BD,_DH)),_DU=B(_rR(_mm,_DT.a,_DT.b,_DT.c));return new T3(0,E(_DU.a),E(_DU.b),E(_DU.c));}),_DV=new T(function(){var _DW=new T(function(){return B(_Bw(_DO.a));}),_DX=function(_DY){var _DZ=E(_DY);if(!_DZ._){return E(_DW);}else{var _E0=E(_DZ.a),_E1=E(_E0.b),_E2=E(_E0.a),_E3=E(_E0.c),_E4=_E3.a,_E5=_E3.b,_E6=E(_E0.e);return new T2(1,new T(function(){var _E7=E(_E1.a)+ -E(_E2.a),_E8=E(_E1.b)+ -E(_E2.b),_E9=E(_E1.c)+ -E(_E2.c),_Ea=B(A1(_BD,_E2)),_Eb=B(_rR(_mm,_Ea.a,_Ea.b,_Ea.c)),_Ec=_Eb.a,_Ed=_Eb.b,_Ee=_Eb.c,_Ef=Math.sqrt(B(_bj(_mm,_E7,_E8,_E9,_E7,_E8,_E9))),_Eg=1/_Ef,_Eh=_E7*_Eg,_Ei=_E8*_Eg,_Ej=_E9*_Eg,_Ek=B(_sE(_mm,_Eh,_Ei,_Ej,_Ec,_Ed,_Ee)),_El=B(_rR(_mm,_E6.a,_E6.b,_E6.c)),_Em=Math.sqrt(B(_B2(_mm,_E4,_E5,_E4,_E5))),_En=_Em*E(_El.a),_Eo=_Em*E(_El.b),_Ep=_Em*E(_El.c),_Eq=B(_bj(_mm,_Ei*_Ep-_Eo*_Ej,_Ej*_En-_Ep*_Eh,_Eh*_Eo-_En*_Ei,_Ec,_Ed,_Ee));return new T6(0,_BK,_BK,E(new T2(0,E(new T3(0,E(_Ek.a),E(_Ek.b),E(_Ek.c))),E(_Eq))),E(_BB),_Ef,_Bi);}),new T(function(){return B(_DX(_DZ.b));}));}};return B(_DX(_DK));}),_Er=function(_Es){var _Et=E(_Es);if(!_Et._){return E(_DV);}else{var _Eu=E(_Et.a),_Ev=E(_Eu.b),_Ew=new T(function(){var _Ex=E(_DH),_Ey=E(_Ev.c)+ -E(_Ex.c),_Ez=E(_Ev.b)+ -E(_Ex.b),_EA=E(_Ev.a)+ -E(_Ex.a),_EB=Math.sqrt(B(_bj(_mm,_EA,_Ez,_Ey,_EA,_Ez,_Ey))),_EC=function(_ED,_EE,_EF){var _EG=E(_DS),_EH=_EG.a,_EI=_EG.b,_EJ=_EG.c,_EK=B(_sE(_mm,_ED,_EE,_EF,_EH,_EI,_EJ)),_EL=B(_bj(_mm,_EE*0-0*_EF,_EF*0-0*_ED,_ED*0-0*_EE,_EH,_EI,_EJ));return new T6(0,_BK,_BK,new T2(0,E(new T3(0,E(_EK.a),E(_EK.b),E(_EK.c))),E(_EL)),_BB,_EB,_Bi);};if(!E(_Eu.g)){var _EM=1/_EB,_EN=B(_EC(_EA*_EM,_Ez*_EM,_Ey*_EM));return new T6(0,_EN.a,_EN.b,E(_EN.c),E(_EN.d),_EN.e,_EN.f);}else{var _EO=1/_EB,_EP=B(_EC(-1*_EA*_EO,-1*_Ez*_EO,-1*_Ey*_EO));return new T6(0,_EP.a,_EP.b,E(_EP.c),E(_EP.d),_EP.e,_EP.f);}});return new T2(1,_Ew,new T(function(){return B(_Er(_Et.b));}));}};return B(_Er(_DN));});return new T2(0,new T2(1,_DR,new T(function(){return E(E(_DQ).a);})),new T(function(){return E(E(_DQ).b);}));}else{var _EQ=new T(function(){var _ER=new T(function(){var _ES=B(A1(_BD,_DH)),_ET=B(_rR(_mm,_ES.a,_ES.b,_ES.c));return new T3(0,E(_ET.a),E(_ET.b),E(_ET.c));}),_EU=new T(function(){var _EV=new T(function(){return B(_Bw(E(_DF).a));}),_EW=function(_EX){var _EY=E(_EX);if(!_EY._){return E(_EV);}else{var _EZ=E(_EY.a),_F0=E(_EZ.b),_F1=E(_EZ.a),_F2=E(_EZ.c),_F3=_F2.a,_F4=_F2.b,_F5=E(_EZ.e);return new T2(1,new T(function(){var _F6=E(_F0.a)+ -E(_F1.a),_F7=E(_F0.b)+ -E(_F1.b),_F8=E(_F0.c)+ -E(_F1.c),_F9=B(A1(_BD,_F1)),_Fa=B(_rR(_mm,_F9.a,_F9.b,_F9.c)),_Fb=_Fa.a,_Fc=_Fa.b,_Fd=_Fa.c,_Fe=Math.sqrt(B(_bj(_mm,_F6,_F7,_F8,_F6,_F7,_F8))),_Ff=1/_Fe,_Fg=_F6*_Ff,_Fh=_F7*_Ff,_Fi=_F8*_Ff,_Fj=B(_sE(_mm,_Fg,_Fh,_Fi,_Fb,_Fc,_Fd)),_Fk=B(_rR(_mm,_F5.a,_F5.b,_F5.c)),_Fl=Math.sqrt(B(_B2(_mm,_F3,_F4,_F3,_F4))),_Fm=_Fl*E(_Fk.a),_Fn=_Fl*E(_Fk.b),_Fo=_Fl*E(_Fk.c),_Fp=B(_bj(_mm,_Fh*_Fo-_Fn*_Fi,_Fi*_Fm-_Fo*_Fg,_Fg*_Fn-_Fm*_Fh,_Fb,_Fc,_Fd));return new T6(0,_BK,_BK,E(new T2(0,E(new T3(0,E(_Fj.a),E(_Fj.b),E(_Fj.c))),E(_Fp))),E(_BB),_Fe,_Bi);}),new T(function(){return B(_EW(_EY.b));}));}};return B(_EW(_DK));}),_Fq=function(_Fr){var _Fs=E(_Fr);if(!_Fs._){return E(_EU);}else{var _Ft=E(_Fs.a),_Fu=E(_Ft.b),_Fv=new T(function(){var _Fw=E(_DH),_Fx=E(_Fu.c)+ -E(_Fw.c),_Fy=E(_Fu.b)+ -E(_Fw.b),_Fz=E(_Fu.a)+ -E(_Fw.a),_FA=Math.sqrt(B(_bj(_mm,_Fz,_Fy,_Fx,_Fz,_Fy,_Fx))),_FB=function(_FC,_FD,_FE){var _FF=E(_ER),_FG=_FF.a,_FH=_FF.b,_FI=_FF.c,_FJ=B(_sE(_mm,_FC,_FD,_FE,_FG,_FH,_FI)),_FK=B(_bj(_mm,_FD*0-0*_FE,_FE*0-0*_FC,_FC*0-0*_FD,_FG,_FH,_FI));return new T6(0,_BK,_BK,new T2(0,E(new T3(0,E(_FJ.a),E(_FJ.b),E(_FJ.c))),E(_FK)),_BB,_FA,_Bi);};if(!E(_Ft.g)){var _FL=1/_FA,_FM=B(_FB(_Fz*_FL,_Fy*_FL,_Fx*_FL));return new T6(0,_FM.a,_FM.b,E(_FM.c),E(_FM.d),_FM.e,_FM.f);}else{var _FN=1/_FA,_FO=B(_FB(-1*_Fz*_FN,-1*_Fy*_FN,-1*_Fx*_FN));return new T6(0,_FO.a,_FO.b,E(_FO.c),E(_FO.d),_FO.e,_FO.f);}});return new T2(1,_Fv,new T(function(){return B(_Fq(_Fs.b));}));}};return B(_Fq(_DN));});return new T2(0,new T2(1,_EQ,_w),new T(function(){return E(E(_DF).b);}));}}}},_FP=B(_BJ(_BH,_BH,_BI,_BG.c,_BG.d,_));return new F(function(){return _AU(_,_FP);});}else{return new F(function(){return _AU(_,new T2(0,_w,_BG));});}},_FQ=new T(function(){return eval("__strict(passObject)");}),_FR=new T(function(){return eval("__strict(refresh)");}),_FS=function(_FT,_){var _FU=__app0(E(_FR)),_FV=__app0(E(_kB)),_FW=E(_FT),_FX=_FW.c,_FY=_FW.d,_FZ=E(_FW.a),_G0=E(_FW.b);if(_FZ<=_G0){if(_FZ>_G0){return E(_kz);}else{if(0>=_FX){return new F(function(){return _kM(_FX,0);});}else{var _G1=E(_FQ),_G2=__app2(_G1,_FZ,B(_kw(E(_FY[0]))));if(_FZ!=_G0){var _G3=function(_G4,_){if(_FZ>_G4){return E(_kz);}else{if(_G4>_G0){return E(_kz);}else{var _G5=_G4-_FZ|0;if(0>_G5){return new F(function(){return _kM(_FX,_G5);});}else{if(_G5>=_FX){return new F(function(){return _kM(_FX,_G5);});}else{var _G6=__app2(_G1,_G4,B(_kw(E(_FY[_G5]))));if(_G4!=_G0){var _G7=B(_G3(_G4+1|0,_));return new T2(1,_kl,_G7);}else{return _kR;}}}}}},_G8=B(_G3(_FZ+1|0,_)),_G9=__app0(E(_kA)),_Ga=B(_BE(_FW,_));return new T(function(){return E(E(_Ga).b);});}else{var _Gb=__app0(E(_kA)),_Gc=B(_BE(_FW,_));return new T(function(){return E(E(_Gc).b);});}}}}else{var _Gd=__app0(E(_kA)),_Ge=B(_BE(_FW,_));return new T(function(){return E(E(_Ge).b);});}},_Gf=new T(function(){return B(unCStr("Negative exponent"));}),_Gg=new T(function(){return B(err(_Gf));}),_Gh=function(_Gi,_Gj,_Gk){while(1){if(!(_Gj%2)){var _Gl=_Gi*_Gi,_Gm=quot(_Gj,2);_Gi=_Gl;_Gj=_Gm;continue;}else{var _Gn=E(_Gj);if(_Gn==1){return _Gi*_Gk;}else{var _Gl=_Gi*_Gi,_Go=_Gi*_Gk;_Gi=_Gl;_Gj=quot(_Gn-1|0,2);_Gk=_Go;continue;}}}},_Gp=function(_Gq,_Gr){while(1){if(!(_Gr%2)){var _Gs=_Gq*_Gq,_Gt=quot(_Gr,2);_Gq=_Gs;_Gr=_Gt;continue;}else{var _Gu=E(_Gr);if(_Gu==1){return E(_Gq);}else{return new F(function(){return _Gh(_Gq*_Gq,quot(_Gu-1|0,2),_Gq);});}}}},_Gv=-4,_Gw=new T3(0,E(_tf),E(_Gv),E(_tf)),_Gx=function(_Gy){return E(_Gw);},_Gz=function(_){return new F(function(){return __jsNull();});},_GA=function(_GB){var _GC=B(A1(_GB,_));return E(_GC);},_GD=new T(function(){return B(_GA(_Gz));}),_GE=function(_GF,_GG,_GH,_GI,_GJ,_GK,_GL,_GM,_GN,_GO,_GP,_GQ,_GR){var _GS=function(_GT){var _GU=E(_tY),_GV=2+_GT|0,_GW=_GV-1|0,_GX=(2+_GT)*(1+_GT),_GY=E(_uq);if(!_GY._){return _GU*0;}else{var _GZ=_GY.a,_H0=_GY.b,_H1=B(A1(_GF,new T(function(){return 6.283185307179586*E(_GZ)/E(_tq);}))),_H2=B(A1(_GF,new T(function(){return 6.283185307179586*(E(_GZ)+1)/E(_tq);})));if(_H1!=_H2){if(_GV>=0){var _H3=E(_GV);if(!_H3){var _H4=function(_H5,_H6){while(1){var _H7=B((function(_H8,_H9){var _Ha=E(_H8);if(!_Ha._){return E(_H9);}else{var _Hb=_Ha.a,_Hc=_Ha.b,_Hd=B(A1(_GF,new T(function(){return 6.283185307179586*E(_Hb)/E(_tq);}))),_He=B(A1(_GF,new T(function(){return 6.283185307179586*(E(_Hb)+1)/E(_tq);})));if(_Hd!=_He){var _Hf=_H9+0/(_Hd-_He)/_GX;_H5=_Hc;_H6=_Hf;return __continue;}else{if(_GW>=0){var _Hg=E(_GW);if(!_Hg){var _Hf=_H9+_GV/_GX;_H5=_Hc;_H6=_Hf;return __continue;}else{var _Hf=_H9+_GV*B(_Gp(_Hd,_Hg))/_GX;_H5=_Hc;_H6=_Hf;return __continue;}}else{return E(_Gg);}}}})(_H5,_H6));if(_H7!=__continue){return _H7;}}};return _GU*B(_H4(_H0,0/(_H1-_H2)/_GX));}else{var _Hh=function(_Hi,_Hj){while(1){var _Hk=B((function(_Hl,_Hm){var _Hn=E(_Hl);if(!_Hn._){return E(_Hm);}else{var _Ho=_Hn.a,_Hp=_Hn.b,_Hq=B(A1(_GF,new T(function(){return 6.283185307179586*E(_Ho)/E(_tq);}))),_Hr=B(A1(_GF,new T(function(){return 6.283185307179586*(E(_Ho)+1)/E(_tq);})));if(_Hq!=_Hr){if(_H3>=0){var _Hs=_Hm+(B(_Gp(_Hq,_H3))-B(_Gp(_Hr,_H3)))/(_Hq-_Hr)/_GX;_Hi=_Hp;_Hj=_Hs;return __continue;}else{return E(_Gg);}}else{if(_GW>=0){var _Ht=E(_GW);if(!_Ht){var _Hs=_Hm+_GV/_GX;_Hi=_Hp;_Hj=_Hs;return __continue;}else{var _Hs=_Hm+_GV*B(_Gp(_Hq,_Ht))/_GX;_Hi=_Hp;_Hj=_Hs;return __continue;}}else{return E(_Gg);}}}})(_Hi,_Hj));if(_Hk!=__continue){return _Hk;}}};return _GU*B(_Hh(_H0,(B(_Gp(_H1,_H3))-B(_Gp(_H2,_H3)))/(_H1-_H2)/_GX));}}else{return E(_Gg);}}else{if(_GW>=0){var _Hu=E(_GW);if(!_Hu){var _Hv=function(_Hw,_Hx){while(1){var _Hy=B((function(_Hz,_HA){var _HB=E(_Hz);if(!_HB._){return E(_HA);}else{var _HC=_HB.a,_HD=_HB.b,_HE=B(A1(_GF,new T(function(){return 6.283185307179586*E(_HC)/E(_tq);}))),_HF=B(A1(_GF,new T(function(){return 6.283185307179586*(E(_HC)+1)/E(_tq);})));if(_HE!=_HF){if(_GV>=0){var _HG=E(_GV);if(!_HG){var _HH=_HA+0/(_HE-_HF)/_GX;_Hw=_HD;_Hx=_HH;return __continue;}else{var _HH=_HA+(B(_Gp(_HE,_HG))-B(_Gp(_HF,_HG)))/(_HE-_HF)/_GX;_Hw=_HD;_Hx=_HH;return __continue;}}else{return E(_Gg);}}else{var _HH=_HA+_GV/_GX;_Hw=_HD;_Hx=_HH;return __continue;}}})(_Hw,_Hx));if(_Hy!=__continue){return _Hy;}}};return _GU*B(_Hv(_H0,_GV/_GX));}else{var _HI=function(_HJ,_HK){while(1){var _HL=B((function(_HM,_HN){var _HO=E(_HM);if(!_HO._){return E(_HN);}else{var _HP=_HO.a,_HQ=_HO.b,_HR=B(A1(_GF,new T(function(){return 6.283185307179586*E(_HP)/E(_tq);}))),_HS=B(A1(_GF,new T(function(){return 6.283185307179586*(E(_HP)+1)/E(_tq);})));if(_HR!=_HS){if(_GV>=0){var _HT=E(_GV);if(!_HT){var _HU=_HN+0/(_HR-_HS)/_GX;_HJ=_HQ;_HK=_HU;return __continue;}else{var _HU=_HN+(B(_Gp(_HR,_HT))-B(_Gp(_HS,_HT)))/(_HR-_HS)/_GX;_HJ=_HQ;_HK=_HU;return __continue;}}else{return E(_Gg);}}else{if(_Hu>=0){var _HU=_HN+_GV*B(_Gp(_HR,_Hu))/_GX;_HJ=_HQ;_HK=_HU;return __continue;}else{return E(_Gg);}}}})(_HJ,_HK));if(_HL!=__continue){return _HL;}}};return _GU*B(_HI(_H0,_GV*B(_Gp(_H1,_Hu))/_GX));}}else{return E(_Gg);}}}},_HV=E(_GD),_HW=1/(B(_GS(1))*_GG);return new F(function(){return _w7(_GF,_Gx,new T2(0,E(new T3(0,E(_HW),E(_HW),E(_HW))),1/(B(_GS(3))*_GG)),_GH,_GI,_GJ,_GK,_GL,_GM,_GN,_GO,_GP,_GQ,_GR,_tg,_HV,_HV,0);});},_HX=0.5,_HY=1,_HZ=0,_I0=0.3,_I1=function(_I2){return E(_I0);},_I3=new T(function(){var _I4=B(_GE(_I1,1.2,_HZ,_HY,_HX,_HZ,_HZ,_HZ,_HZ,_HZ,_HY,_HY,_HY));return {_:0,a:E(_I4.a),b:E(_I4.b),c:E(_I4.c),d:E(_I4.d),e:E(_I4.e),f:E(_I4.f),g:E(_I4.g),h:_I4.h,i:_I4.i,j:_I4.j};}),_I5=0,_I6=function(_){var _I7=newArr(1,_pD),_=_I7[0]=_I3;return new T4(0,E(_I5),E(_I5),1,_I7);},_I8=new T(function(){return B(_pI(_I6));}),_I9=function(_Ia,_){while(1){var _Ib=E(_Ia);if(!_Ib._){return _kl;}else{var _Ic=_Ib.b,_Id=E(_Ib.a);switch(_Id._){case 0:var _Ie=B(A1(_Id.a,_));_Ia=B(_n(_Ic,new T2(1,_Ie,_w)));continue;case 1:_Ia=B(_n(_Ic,_Id.a));continue;default:_Ia=_Ic;continue;}}}},_If=function(_Ig,_Ih,_){var _Ii=E(_Ig);switch(_Ii._){case 0:var _Ij=B(A1(_Ii.a,_));return new F(function(){return _I9(B(_n(_Ih,new T2(1,_Ij,_w))),_);});break;case 1:return new F(function(){return _I9(B(_n(_Ih,_Ii.a)),_);});break;default:return new F(function(){return _I9(_Ih,_);});}},_Ik=new T0(2),_Il=function(_Im){return new T0(2);},_In=function(_Io,_Ip,_Iq){return function(_){var _Ir=E(_Io),_Is=rMV(_Ir),_It=E(_Is);if(!_It._){var _Iu=new T(function(){var _Iv=new T(function(){return B(A1(_Iq,_kl));});return B(_n(_It.b,new T2(1,new T2(0,_Ip,function(_Iw){return E(_Iv);}),_w)));}),_=wMV(_Ir,new T2(0,_It.a,_Iu));return _Ik;}else{var _Ix=E(_It.a);if(!_Ix._){var _=wMV(_Ir,new T2(0,_Ip,_w));return new T(function(){return B(A1(_Iq,_kl));});}else{var _=wMV(_Ir,new T1(1,_Ix.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Iq,_kl));}),new T2(1,new T(function(){return B(A2(_Ix.a,_Ip,_Il));}),_w)));}}};},_Iy=new T(function(){return E(_GD);}),_Iz=new T(function(){return eval("window.requestAnimationFrame");}),_IA=new T1(1,_w),_IB=function(_IC,_ID){return function(_){var _IE=E(_IC),_IF=rMV(_IE),_IG=E(_IF);if(!_IG._){var _IH=_IG.a,_II=E(_IG.b);if(!_II._){var _=wMV(_IE,_IA);return new T(function(){return B(A1(_ID,_IH));});}else{var _IJ=E(_II.a),_=wMV(_IE,new T2(0,_IJ.a,_II.b));return new T1(1,new T2(1,new T(function(){return B(A1(_ID,_IH));}),new T2(1,new T(function(){return B(A1(_IJ.b,_Il));}),_w)));}}else{var _IK=new T(function(){var _IL=function(_IM){var _IN=new T(function(){return B(A1(_ID,_IM));});return function(_IO){return E(_IN);};};return B(_n(_IG.a,new T2(1,_IL,_w)));}),_=wMV(_IE,new T1(1,_IK));return _Ik;}};},_IP=function(_IQ,_IR){return new T1(0,B(_IB(_IQ,_IR)));},_IS=function(_IT,_IU){var _IV=new T(function(){return new T1(0,B(_In(_IT,_kl,_Il)));});return function(_){var _IW=__createJSFunc(2,function(_IX,_){var _IY=B(_If(_IV,_w,_));return _Iy;}),_IZ=__app1(E(_Iz),_IW);return new T(function(){return B(_IP(_IT,_IU));});};},_J0=new T1(1,_w),_J1=function(_J2,_J3,_){var _J4=function(_){var _J5=nMV(_J2),_J6=_J5;return new T(function(){var _J7=new T(function(){return B(_J8(_));}),_J9=function(_){var _Ja=rMV(_J6),_Jb=B(A2(_J3,_Ja,_)),_=wMV(_J6,_Jb),_Jc=function(_){var _Jd=nMV(_J0);return new T(function(){return new T1(0,B(_IS(_Jd,function(_Je){return E(_J7);})));});};return new T1(0,_Jc);},_Jf=new T(function(){return new T1(0,_J9);}),_J8=function(_Jg){return E(_Jf);};return B(_J8(_));});};return new F(function(){return _If(new T1(0,_J4),_w,_);});},_Jh=new T(function(){return eval("__strict(setBounds)");}),_Ji=function(_){var _Jj=__app3(E(_9m),E(_bM),E(_ke),E(_9l)),_Jk=__app2(E(_Jh),E(_8S),E(_8P));return new F(function(){return _J1(_I8,_FS,_);});},_Jl=function(_){return new F(function(){return _Ji(_);});};
var hasteMain = function() {B(A(_Jl, [0]));};window.onload = hasteMain;