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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=function(_i,_j,_k){return new F(function(){return A1(_i,function(_l){return new F(function(){return A2(_j,_l,_k);});});});},_m=function(_n,_o,_p){var _q=function(_r){var _s=new T(function(){return B(A1(_p,_r));});return new F(function(){return A1(_o,function(_t){return E(_s);});});};return new F(function(){return A1(_n,_q);});},_u=function(_v,_w,_x){var _y=new T(function(){return B(A1(_w,function(_z){return new F(function(){return A1(_x,_z);});}));});return new F(function(){return A1(_v,function(_A){return E(_y);});});},_B=function(_C,_D,_E){var _F=function(_G){var _H=function(_I){return new F(function(){return A1(_E,new T(function(){return B(A1(_G,_I));}));});};return new F(function(){return A1(_D,_H);});};return new F(function(){return A1(_C,_F);});},_J=function(_K,_L){return new F(function(){return A1(_L,_K);});},_M=function(_N,_O,_P){var _Q=new T(function(){return B(A1(_P,_N));});return new F(function(){return A1(_O,function(_R){return E(_Q);});});},_S=function(_T,_U,_V){var _W=function(_X){return new F(function(){return A1(_V,new T(function(){return B(A1(_T,_X));}));});};return new F(function(){return A1(_U,_W);});},_Y=new T2(0,_S,_M),_Z=new T5(0,_Y,_J,_B,_u,_m),_10=function(_11){return E(E(_11).b);},_12=function(_13,_14){return new F(function(){return A3(_10,_15,_13,function(_16){return E(_14);});});},_17=function(_18){return new F(function(){return err(_18);});},_15=new T(function(){return new T5(0,_Z,_h,_12,_J,_17);}),_19=function(_1a){return new T0(2);},_1b=function(_1c){var _1d=new T(function(){return B(A1(_1c,_19));}),_1e=function(_1f){return new T1(1,new T2(1,new T(function(){return B(A1(_1f,_5));}),new T2(1,_1d,_4)));};return E(_1e);},_1g=function(_1h){return E(_1h);},_1i=new T3(0,_15,_1g,_1b),_1j=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1k=new T(function(){return B(err(_1j));}),_1l=0,_1m=new T3(0,_1l,_1l,_1l),_1n=1,_1o=new T3(0,_1l,_1n,_1l),_1p=40,_1q=new T1(0,_1p),_1r=1.5707963267948966,_1s=80,_1t=new T(function(){return eval("scrW");}),_1u=new T(function(){return E(_1t)/2-1;}),_1v=new T3(0,_1u,_1s,_1r),_1w=2.4867959858108646e-7,_1x=1.9894367886486917e-4,_1y=new T3(0,_1x,_1x,_1w),_1z=new T5(0,_1q,_1v,_1m,_1o,_1y),_1A=60,_1B=new T(function(){return E(_1t)/2-2;}),_1C=new T3(0,_1B,_1A,_1r),_1D=new T5(0,_1q,_1C,_1m,_1o,_1y),_1E=2,_1F=0,_1G=new T(function(){return E(_1t)/2-3;}),_1H=100,_1I=new T3(0,_1G,_1H,_1r),_1J=new T5(0,_1q,_1I,_1m,_1o,_1y),_1K=function(_){var _1L=newArr(3,_1k),_=_1L[0]=_1D,_=_1L[1]=_1z,_=_1L[2]=_1J;return new T4(0,E(_1F),E(_1E),3,_1L);},_1M=function(_1N){var _1O=B(A1(_1N,_));return E(_1O);},_1P=new T(function(){return B(_1M(_1K));}),_1Q=function(_1R,_1S,_){var _1T=B(A1(_1R,_)),_1U=B(A1(_1S,_));return _1T;},_1V=function(_1W,_1X,_){var _1Y=B(A1(_1W,_)),_1Z=B(A1(_1X,_));return new T(function(){return B(A1(_1Y,_1Z));});},_20=function(_21,_22,_){var _23=B(A1(_22,_));return _21;},_24=function(_25,_26,_){var _27=B(A1(_26,_));return new T(function(){return B(A1(_25,_27));});},_28=new T2(0,_24,_20),_29=function(_2a,_){return _2a;},_2b=function(_2c,_2d,_){var _2e=B(A1(_2c,_));return new F(function(){return A1(_2d,_);});},_2f=new T5(0,_28,_29,_1V,_2b,_1Q),_2g=function(_2h){var _2i=E(_2h);return (E(_2i.b)-E(_2i.a)|0)+1|0;},_2j=function(_2k,_2l){var _2m=E(_2k),_2n=E(_2l);return (E(_2m.a)>_2n)?false:_2n<=E(_2m.b);},_2o=function(_2p,_2q){var _2r=jsShowI(_2p);return new F(function(){return _0(fromJSStr(_2r),_2q);});},_2s=41,_2t=40,_2u=function(_2v,_2w,_2x){if(_2w>=0){return new F(function(){return _2o(_2w,_2x);});}else{if(_2v<=6){return new F(function(){return _2o(_2w,_2x);});}else{return new T2(1,_2t,new T(function(){var _2y=jsShowI(_2w);return B(_0(fromJSStr(_2y),new T2(1,_2s,_2x)));}));}}},_2z=function(_2A){return new F(function(){return _2u(0,E(_2A),_4);});},_2B=function(_2C,_2D,_2E){return new F(function(){return _2u(E(_2C),E(_2D),_2E);});},_2F=44,_2G=93,_2H=91,_2I=function(_2J,_2K,_2L){var _2M=E(_2K);if(!_2M._){return new F(function(){return unAppCStr("[]",_2L);});}else{var _2N=new T(function(){var _2O=new T(function(){var _2P=function(_2Q){var _2R=E(_2Q);if(!_2R._){return E(new T2(1,_2G,_2L));}else{var _2S=new T(function(){return B(A2(_2J,_2R.a,new T(function(){return B(_2P(_2R.b));})));});return new T2(1,_2F,_2S);}};return B(_2P(_2M.b));});return B(A2(_2J,_2M.a,_2O));});return new T2(1,_2H,_2N);}},_2T=function(_2U,_2V){return new F(function(){return _2u(0,E(_2U),_2V);});},_2W=function(_2X,_2Y){return new F(function(){return _2I(_2T,_2X,_2Y);});},_2Z=new T3(0,_2B,_2z,_2W),_30=0,_31=function(_32,_33,_34){return new F(function(){return A1(_32,new T2(1,_2F,new T(function(){return B(A1(_33,_34));})));});},_35=new T(function(){return B(unCStr(": empty list"));}),_36=new T(function(){return B(unCStr("Prelude."));}),_37=function(_38){return new F(function(){return err(B(_0(_36,new T(function(){return B(_0(_38,_35));},1))));});},_39=new T(function(){return B(unCStr("foldr1"));}),_3a=new T(function(){return B(_37(_39));}),_3b=function(_3c,_3d){var _3e=E(_3d);if(!_3e._){return E(_3a);}else{var _3f=_3e.a,_3g=E(_3e.b);if(!_3g._){return E(_3f);}else{return new F(function(){return A2(_3c,_3f,new T(function(){return B(_3b(_3c,_3g));}));});}}},_3h=new T(function(){return B(unCStr(" out of range "));}),_3i=new T(function(){return B(unCStr("}.index: Index "));}),_3j=new T(function(){return B(unCStr("Ix{"));}),_3k=new T2(1,_2s,_4),_3l=new T2(1,_2s,_3k),_3m=0,_3n=function(_3o){return E(E(_3o).a);},_3p=function(_3q,_3r,_3s,_3t,_3u){var _3v=new T(function(){var _3w=new T(function(){var _3x=new T(function(){var _3y=new T(function(){var _3z=new T(function(){return B(A3(_3b,_31,new T2(1,new T(function(){return B(A3(_3n,_3s,_3m,_3t));}),new T2(1,new T(function(){return B(A3(_3n,_3s,_3m,_3u));}),_4)),_3l));});return B(_0(_3h,new T2(1,_2t,new T2(1,_2t,_3z))));});return B(A(_3n,[_3s,_30,_3r,new T2(1,_2s,_3y)]));});return B(_0(_3i,new T2(1,_2t,_3x)));},1);return B(_0(_3q,_3w));},1);return new F(function(){return err(B(_0(_3j,_3v)));});},_3A=function(_3B,_3C,_3D,_3E,_3F){return new F(function(){return _3p(_3B,_3C,_3F,_3D,_3E);});},_3G=function(_3H,_3I,_3J,_3K){var _3L=E(_3J);return new F(function(){return _3A(_3H,_3I,_3L.a,_3L.b,_3K);});},_3M=function(_3N,_3O,_3P,_3Q){return new F(function(){return _3G(_3Q,_3P,_3O,_3N);});},_3R=new T(function(){return B(unCStr("Int"));}),_3S=function(_3T,_3U){return new F(function(){return _3M(_2Z,_3U,_3T,_3R);});},_3V=function(_3W,_3X){var _3Y=E(_3W),_3Z=E(_3Y.a),_40=E(_3X);if(_3Z>_40){return new F(function(){return _3S(_40,_3Y);});}else{if(_40>E(_3Y.b)){return new F(function(){return _3S(_40,_3Y);});}else{return _40-_3Z|0;}}},_41=function(_42,_43){if(_42<=_43){var _44=function(_45){return new T2(1,_45,new T(function(){if(_45!=_43){return B(_44(_45+1|0));}else{return __Z;}}));};return new F(function(){return _44(_42);});}else{return __Z;}},_46=function(_47,_48){return new F(function(){return _41(E(_47),E(_48));});},_49=function(_4a){var _4b=E(_4a);return new F(function(){return _46(_4b.a,_4b.b);});},_4c=function(_4d){var _4e=E(_4d),_4f=E(_4e.a),_4g=E(_4e.b);return (_4f>_4g)?E(_30):(_4g-_4f|0)+1|0;},_4h=function(_4i,_4j){return E(_4i)-E(_4j)|0;},_4k=function(_4l,_4m){return new F(function(){return _4h(_4m,E(_4l).a);});},_4n=function(_4o,_4p){return E(_4o)==E(_4p);},_4q=function(_4r,_4s){return E(_4r)!=E(_4s);},_4t=new T2(0,_4n,_4q),_4u=function(_4v,_4w){var _4x=E(_4v),_4y=E(_4w);return (_4x>_4y)?E(_4x):E(_4y);},_4z=function(_4A,_4B){var _4C=E(_4A),_4D=E(_4B);return (_4C>_4D)?E(_4D):E(_4C);},_4E=function(_4F,_4G){return (_4F>=_4G)?(_4F!=_4G)?2:1:0;},_4H=function(_4I,_4J){return new F(function(){return _4E(E(_4I),E(_4J));});},_4K=function(_4L,_4M){return E(_4L)>=E(_4M);},_4N=function(_4O,_4P){return E(_4O)>E(_4P);},_4Q=function(_4R,_4S){return E(_4R)<=E(_4S);},_4T=function(_4U,_4V){return E(_4U)<E(_4V);},_4W={_:0,a:_4t,b:_4H,c:_4T,d:_4Q,e:_4N,f:_4K,g:_4u,h:_4z},_4X={_:0,a:_4W,b:_49,c:_3V,d:_4k,e:_2j,f:_4c,g:_2g},_4Y=function(_4Z){return E(E(_4Z).a);},_50=function(_51,_52){return new T2(1,_51,_52);},_53=function(_54){return E(E(_54).c);},_55=function(_56,_57){var _58=E(_57);return new T2(0,_58.a,_58.b);},_59=function(_5a){return E(E(_5a).a);},_5b=new T(function(){return B(unCStr("Negative range size"));}),_5c=new T(function(){return B(err(_5b));}),_5d=function(_5e){return E(E(_5e).f);},_5f=function(_5g,_5h,_5i){var _5j=E(_5h),_5k=_5j.a,_5l=_5j.b,_5m=function(_){var _5n=B(A2(_5d,_5g,_5j));if(_5n>=0){var _5o=newArr(_5n,_1k),_5p=_5o,_5q=E(_5n);if(!_5q){return new T(function(){return new T4(0,E(_5k),E(_5l),0,_5p);});}else{var _5r=function(_5s,_5t,_){while(1){var _5u=E(_5s);if(!_5u._){return E(_);}else{var _=_5p[_5t]=_5u.a;if(_5t!=(_5q-1|0)){var _5v=_5t+1|0;_5s=_5u.b;_5t=_5v;continue;}else{return E(_);}}}},_=B(_5r(_5i,0,_));return new T(function(){return new T4(0,E(_5k),E(_5l),_5q,_5p);});}}else{return E(_5c);}};return new F(function(){return _1M(_5m);});},_5w=function(_5x){return E(E(_5x).b);},_5y=function(_5z,_5A,_5B,_5C){var _5D=new T(function(){var _5E=E(_5C),_5F=_5E.c-1|0,_5G=new T(function(){return B(A2(_5w,_5A,_4));});if(0<=_5F){var _5H=new T(function(){return B(_4Y(_5A));}),_5I=function(_5J){var _5K=new T(function(){var _5L=new T(function(){return B(A1(_5B,new T(function(){return E(_5E.d[_5J]);})));});return B(A3(_59,_5H,_50,_5L));});return new F(function(){return A3(_53,_5A,_5K,new T(function(){if(_5J!=_5F){return B(_5I(_5J+1|0));}else{return E(_5G);}}));});};return B(_5I(0));}else{return E(_5G);}}),_5M=new T(function(){return B(_55(_5z,_5C));});return new F(function(){return A3(_59,B(_4Y(_5A)),function(_5N){return new F(function(){return _5f(_5z,_5M,_5N);});},_5D);});},_5O=new T(function(){return eval("draw");}),_5P=function(_){return _5;},_5Q=new T(function(){return eval("drawCircle");}),_5R=function(_5S,_5T,_){var _5U=E(_5S);if(!_5U._){var _5V=E(_5T),_5W=__app4(E(_5Q),E(_5V.a),E(_5V.b),E(_5V.c),E(_5U.a));return new F(function(){return _5P(_);});}else{return _5;}},_5X=function(_5Y,_){var _5Z=E(_5Y);return new F(function(){return _5R(_5Z.a,_5Z.b,_);});},_60=function(_61){return E(_61);},_62=function(_63){return E(_63);},_64=function(_65,_66){return E(_66);},_67=function(_68,_69){return E(_68);},_6a=function(_6b){return E(_6b);},_6c=new T2(0,_6a,_67),_6d=function(_6e,_6f){return E(_6e);},_6g=new T5(0,_6c,_62,_60,_64,_6d),_6h=function(_6i,_6j,_){while(1){var _6k=B((function(_6l,_6m,_){var _6n=E(_6l);if(!_6n._){return new T2(0,_5,_6m);}else{var _6o=B(A2(_6n.a,_6m,_));_6i=_6n.b;_6j=new T(function(){return E(E(_6o).b);});return __continue;}})(_6i,_6j,_));if(_6k!=__continue){return _6k;}}},_6p=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_6q=new T(function(){return B(err(_6p));}),_6r=1,_6s=-1,_6t=function(_6u,_6v){return E(_6u)-E(_6v);},_6w=function(_6x,_6y){var _6z=E(_6x),_6A=E(_6y);return new T2(0,new T(function(){return B(_6t(_6z.a,_6A.a));}),new T(function(){return B(_6t(_6z.b,_6A.b));}));},_6B=function(_6C,_6D){return new F(function(){return _6w(_6D,_6C);});},_6E=new T(function(){return B(unCStr("!!: negative index"));}),_6F=new T(function(){return B(_0(_36,_6E));}),_6G=new T(function(){return B(err(_6F));}),_6H=new T(function(){return B(unCStr("!!: index too large"));}),_6I=new T(function(){return B(_0(_36,_6H));}),_6J=new T(function(){return B(err(_6I));}),_6K=function(_6L,_6M){while(1){var _6N=E(_6L);if(!_6N._){return E(_6J);}else{var _6O=E(_6M);if(!_6O){return E(_6N.a);}else{_6L=_6N.b;_6M=_6O-1|0;continue;}}}},_6P=function(_6Q,_6R){if(_6R>=0){return new F(function(){return _6K(_6Q,_6R);});}else{return E(_6G);}},_6S=__Z,_6T=function(_6U,_6V,_6W){while(1){var _6X=E(_6U);if(!_6X._){return new T2(0,_6V,_6W);}else{var _6Y=_6X.b,_6Z=E(_6X.a),_70=_6Z.a,_71=_6Z.b,_72=E(_6V);if(!_72._){if(!E(_70)._){var _73=E(_6W),_74=E(_71);if(_73>_74){_6U=_6Y;_6V=_6S;_6W=_74;continue;}else{_6U=_6Y;_6V=_6S;_6W=_73;continue;}}else{_6U=_6Y;_6V=_6S;continue;}}else{var _75=E(_70);if(!_75._){_6U=_6Y;_6V=_6S;_6W=_71;continue;}else{var _76=E(_72.a),_77=E(_75.a);if(_76>=_77){if(_76!=_77){_6U=_6Y;_6V=_75;_6W=_71;continue;}else{var _78=E(_6W),_79=E(_71);if(_78>_79){_6U=_6Y;_6V=_75;_6W=_79;continue;}else{_6U=_6Y;_6V=_72;_6W=_78;continue;}}}else{_6U=_6Y;_6V=_72;continue;}}}}}},_7a=function(_7b,_7c,_7d){while(1){var _7e=E(_7b);if(!_7e._){return new T2(0,_7c,_7d);}else{var _7f=_7e.b,_7g=E(_7e.a),_7h=_7g.a,_7i=_7g.b,_7j=E(_7c);if(!_7j._){var _7k=E(_7h);if(!_7k._){var _7l=E(_7d),_7m=E(_7i);if(_7l>_7m){_7b=_7f;_7c=_6S;_7d=_7l;continue;}else{_7b=_7f;_7c=_6S;_7d=_7m;continue;}}else{_7b=_7f;_7c=_7k;_7d=_7i;continue;}}else{var _7n=E(_7h);if(!_7n._){_7b=_7f;_7c=_7j;continue;}else{var _7o=E(_7j.a),_7p=E(_7n.a);if(_7o>=_7p){if(_7o!=_7p){_7b=_7f;_7c=_7j;continue;}else{var _7q=E(_7d),_7r=E(_7i);if(_7q>_7r){_7b=_7f;_7c=_7j;_7d=_7q;continue;}else{_7b=_7f;_7c=_7n;_7d=_7r;continue;}}}else{_7b=_7f;_7c=_7n;_7d=_7i;continue;}}}}}},_7s=function(_7t,_7u,_7v){while(1){var _7w=E(_7t);if(!_7w._){return new T2(0,_7u,_7v);}else{var _7x=_7w.b,_7y=E(_7w.a),_7z=_7y.a,_7A=_7y.b,_7B=E(_7u);if(!_7B._){var _7C=E(_7z);if(!_7C._){var _7D=E(_7v),_7E=E(_7A);if(_7D>_7E){_7t=_7x;_7u=_6S;_7v=_7D;continue;}else{_7t=_7x;_7u=_6S;_7v=_7E;continue;}}else{_7t=_7x;_7u=_7C;_7v=_7A;continue;}}else{var _7F=E(_7z);if(!_7F._){_7t=_7x;_7u=_7B;continue;}else{var _7G=E(_7B.a),_7H=E(_7F.a);if(_7G>=_7H){if(_7G!=_7H){_7t=_7x;_7u=_7B;continue;}else{var _7I=E(_7v),_7J=E(_7A);if(_7I>_7J){_7t=_7x;_7u=_7B;_7v=_7I;continue;}else{_7t=_7x;_7u=_7F;_7v=_7J;continue;}}}else{_7t=_7x;_7u=_7F;_7v=_7A;continue;}}}}}},_7K=function(_7L,_7M){while(1){var _7N=B((function(_7O,_7P){var _7Q=E(_7P);if(!_7Q._){return __Z;}else{var _7R=_7Q.a,_7S=_7Q.b;if(!B(A1(_7O,_7R))){var _7T=_7O;_7L=_7T;_7M=_7S;return __continue;}else{return new T2(1,_7R,new T(function(){return B(_7K(_7O,_7S));}));}}})(_7L,_7M));if(_7N!=__continue){return _7N;}}},_7U=function(_7V){return E(E(_7V).a);},_7W=function(_7X,_7Y){var _7Z=E(_7X);if(!_7Z._){var _80=E(_7Y);return __Z;}else{var _81=E(_7Y);return (_81._==0)?__Z:(E(_7Z.a)>E(_81.a))?E(_81):E(_7Z);}},_82=function(_83,_84){while(1){var _85=E(_83);if(!_85._){return E(_84);}else{var _86=B(_7W(_84,_85.a));_83=_85.b;_84=_86;continue;}}},_87=function(_88,_89){while(1){var _8a=E(_88);if(!_8a._){return E(_89);}else{var _8b=B(_7W(_89,_8a.a));_88=_8a.b;_89=_8b;continue;}}},_8c=function(_8d){return (E(_8d)._==0)?false:true;},_8e=new T(function(){return B(unCStr("minimum"));}),_8f=new T(function(){return B(_37(_8e));}),_8g=function(_8h,_8i){var _8j=E(_8h);if(!_8j._){return __Z;}else{var _8k=E(_8i);return (_8k._==0)?__Z:new T2(1,new T2(0,new T(function(){var _8l=B(_7K(_8c,_8j.a));if(!_8l._){return E(_8f);}else{return B(_87(_8l.b,_8l.a));}}),_8k.a),new T(function(){return B(_8g(_8j.b,_8k.b));}));}},_8m=function(_8n,_8o){while(1){var _8p=E(_8n);if(!_8p._){return E(_8o);}else{var _8q=B(_7W(_8o,_8p.a));_8n=_8p.b;_8o=_8q;continue;}}},_8r=function(_8s,_8t){while(1){var _8u=E(_8s);if(!_8u._){return E(_8t);}else{var _8v=B(_7W(_8t,_8u.a));_8s=_8u.b;_8t=_8v;continue;}}},_8w=function(_8x,_8y){var _8z=E(_8x);if(!_8z._){return __Z;}else{var _8A=E(_8y);return (_8A._==0)?__Z:new T2(1,new T2(0,new T(function(){var _8B=B(_7K(_8c,_8z.a));if(!_8B._){return E(_8f);}else{return B(_8r(_8B.b,_8B.a));}}),_8A.a),new T(function(){return B(_8w(_8z.b,_8A.b));}));}},_8C=function(_8D){while(1){var _8E=E(_8D);if(!_8E._){return true;}else{if(!E(_8E.a)._){_8D=_8E.b;continue;}else{return false;}}}},_8F=function(_8G){while(1){var _8H=E(_8G);if(!_8H._){return false;}else{if(!B(_8C(_8H.a))){_8G=_8H.b;continue;}else{return true;}}}},_8I=function(_8J,_8K){var _8L=E(_8J),_8M=E(_8L.a),_8N=E(_8M.a),_8O=E(_8M.b),_8P=E(_8L.b),_8Q=E(_8K),_8R= -(E(_8P.b)-_8O),_8S=E(_8P.a)-_8N,_8T=(_8R*E(_8Q.a)+_8S*E(_8Q.b)-(_8R*_8N+_8S*_8O))/Math.sqrt(_8R*_8R+_8S*_8S);return (_8T<0)?new T1(1,_8T):__Z;},_8U=0,_8V=1,_8W=new T(function(){return B(_37(_8e));}),_8X=new T(function(){return B(_41(0,3));}),_8Y=new T(function(){return B(unCStr("base"));}),_8Z=new T(function(){return B(unCStr("Control.Exception.Base"));}),_90=new T(function(){return B(unCStr("PatternMatchFail"));}),_91=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_8Y,_8Z,_90),_92=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_91,_4,_4),_93=function(_94){return E(_92);},_95=function(_96){return E(E(_96).a);},_97=function(_98,_99,_9a){var _9b=B(A1(_98,_)),_9c=B(A1(_99,_)),_9d=hs_eqWord64(_9b.a,_9c.a);if(!_9d){return __Z;}else{var _9e=hs_eqWord64(_9b.b,_9c.b);return (!_9e)?__Z:new T1(1,_9a);}},_9f=function(_9g){var _9h=E(_9g);return new F(function(){return _97(B(_95(_9h.a)),_93,_9h.b);});},_9i=function(_9j){return E(E(_9j).a);},_9k=function(_9l){return new T2(0,_9m,_9l);},_9n=function(_9o,_9p){return new F(function(){return _0(E(_9o).a,_9p);});},_9q=function(_9r,_9s){return new F(function(){return _2I(_9n,_9r,_9s);});},_9t=function(_9u,_9v,_9w){return new F(function(){return _0(E(_9v).a,_9w);});},_9x=new T3(0,_9t,_9i,_9q),_9m=new T(function(){return new T5(0,_93,_9x,_9k,_9f,_9i);}),_9y=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_9z=function(_9A){return E(E(_9A).c);},_9B=function(_9C,_9D){return new F(function(){return die(new T(function(){return B(A2(_9z,_9D,_9C));}));});},_9E=function(_9F,_9G){return new F(function(){return _9B(_9F,_9G);});},_9H=function(_9I,_9J){var _9K=E(_9J);if(!_9K._){return new T2(0,_4,_4);}else{var _9L=_9K.a;if(!B(A1(_9I,_9L))){return new T2(0,_4,_9K);}else{var _9M=new T(function(){var _9N=B(_9H(_9I,_9K.b));return new T2(0,_9N.a,_9N.b);});return new T2(0,new T2(1,_9L,new T(function(){return E(E(_9M).a);})),new T(function(){return E(E(_9M).b);}));}}},_9O=32,_9P=new T(function(){return B(unCStr("\n"));}),_9Q=function(_9R){return (E(_9R)==124)?false:true;},_9S=function(_9T,_9U){var _9V=B(_9H(_9Q,B(unCStr(_9T)))),_9W=_9V.a,_9X=function(_9Y,_9Z){var _a0=new T(function(){var _a1=new T(function(){return B(_0(_9U,new T(function(){return B(_0(_9Z,_9P));},1)));});return B(unAppCStr(": ",_a1));},1);return new F(function(){return _0(_9Y,_a0);});},_a2=E(_9V.b);if(!_a2._){return new F(function(){return _9X(_9W,_4);});}else{if(E(_a2.a)==124){return new F(function(){return _9X(_9W,new T2(1,_9O,_a2.b));});}else{return new F(function(){return _9X(_9W,_4);});}}},_a3=function(_a4){return new F(function(){return _9E(new T1(0,new T(function(){return B(_9S(_a4,_9y));})),_9m);});},_a5=new T(function(){return B(_a3("Lib\\Physics.hs:96:13-61|(Just d\', f\')"));}),_a6=new T2(0,_1n,_1l),_a7=function(_a8){return  -E(_a8);},_a9=function(_aa){var _ab=E(_aa);return new T2(0,new T(function(){return B(_a7(_ab.a));}),new T(function(){return B(_a7(_ab.b));}));},_ac=function(_ad){var _ae=E(_ad);return new T5(0,_ae.b,_ae.a,new T(function(){return B(_a9(_ae.d));}),new T(function(){return B(_a9(_ae.c));}),_ae.e);},_af=new T(function(){return B(unCStr("Non-exhaustive guards in"));}),_ag=function(_ah){return new F(function(){return _9E(new T1(0,new T(function(){return B(_9S(_ah,_af));})),_9m);});},_ai=new T(function(){return B(_ag("Lib\\Physics.hs:(58,26)-(61,63)|multi-way if"));}),_aj=new T(function(){return B(unCStr("maximum"));}),_ak=new T(function(){return B(_37(_aj));}),_al=function(_am,_an){var _ao=E(_an);return (_ao._==0)?__Z:new T2(1,new T(function(){return B(A1(_am,_ao.a));}),new T(function(){return B(_al(_am,_ao.b));}));},_ap=function(_aq,_ar){var _as=_aq%_ar;if(_aq<=0){if(_aq>=0){return E(_as);}else{if(_ar<=0){return E(_as);}else{var _at=E(_as);return (_at==0)?0:_at+_ar|0;}}}else{if(_ar>=0){if(_aq>=0){return E(_as);}else{if(_ar<=0){return E(_as);}else{var _au=E(_as);return (_au==0)?0:_au+_ar|0;}}}else{var _av=E(_as);return (_av==0)?0:_av+_ar|0;}}},_aw=function(_ax){return E(E(_ax).b);},_ay=new T(function(){return B(unCStr("tail"));}),_az=new T(function(){return B(_37(_ay));}),_aA=-1,_aB=new T2(0,_aA,_aA),_aC=new T2(0,_aA,_8V),_aD=new T2(0,_8V,_8V),_aE=new T2(0,_8V,_aA),_aF=new T2(1,_aB,_4),_aG=new T2(1,_aE,_aF),_aH=new T2(1,_aD,_aG),_aI=new T2(1,_aC,_aH),_aJ=new T2(1,_aB,_aI),_aK=function(_aL,_aM){var _aN=E(_aL);if(!_aN._){return __Z;}else{var _aO=E(_aM);return (_aO._==0)?__Z:new T2(1,new T2(0,_aN.a,_aO.a),new T(function(){return B(_aK(_aN.b,_aO.b));}));}},_aP=function(_aQ,_aR,_aS,_aT){var _aU=E(_aR);if(!_aU._){return __Z;}else{var _aV=E(_aS);if(!_aV._){return __Z;}else{var _aW=E(_aT);return (_aW._==0)?__Z:new T2(1,new T(function(){return B(A3(_aQ,_aU.a,_aV.a,_aW.a));}),new T(function(){return B(_aP(_aQ,_aU.b,_aV.b,_aW.b));}));}}},_aX=function(_aY,_aZ,_b0,_b1){var _b2=E(_aY);if(!_b2._){var _b3=_b2.a,_b4=E(_b0);if(!_b4._){var _b5=E(_aZ),_b6=E(_b1),_b7=E(_b3),_b8=E(_b4.a),_b9=E(_b5.a)-E(_b6.a),_ba=E(_b5.b)-E(_b6.b),_bb=Math.sqrt(_b9*_b9+_ba*_ba),_bc=_b7+_b8;if(_bb<=_bc){var _bd=new T(function(){var _be=E(_bb);if(!_be){return E(_a6);}else{return new T2(0,new T(function(){return _b9/_be;}),new T(function(){return _ba/_be;}));}}),_bf=new T(function(){var _bg=E(_bd);return new T2(0,new T(function(){return E(_bg.a)*_b8;}),new T(function(){return E(_bg.b)*_b8;}));}),_bh=new T(function(){var _bi=E(_bd);return new T2(0,new T(function(){return  -(E(_bi.a)*_b7);}),new T(function(){return  -(E(_bi.b)*_b7);}));});return new T2(1,new T5(0,_bh,_bf,_bd,_bd,_bc-_bb),_4);}else{return __Z;}}else{var _bj=E(_aZ),_bk=E(_bj.a),_bl=E(_b1),_bm=E(_bl.a),_bn=E(_bl.c),_bo=E(_bj.b),_bp=E(_bl.b),_bq=E(_b4.a),_br=_bk-_bm,_bs= -_bn,_bt=_bo-_bp,_bu=_br*Math.cos(_bs)-_bt*Math.sin(_bs),_bv= -(_bq/2),_bw=_bq/2,_bx=function(_by){var _bz=E(_b4.b),_bA=_br*Math.sin(_bs)+_bt*Math.cos(_bs),_bB= -(_bz/2),_bC=_bz/2,_bD=function(_bE){var _bF=E(_b3),_bG=_bu-_by,_bH=_bA-_bE,_bI=Math.sqrt(_bG*_bG+_bH*_bH);if(_bI<=_bF){var _bJ=new T(function(){var _bK=function(_bL){if(_bL>0){var _bM=function(_bN){if(_bN>0){return (_bL>_bN)?(_bL<_bN)?E(_ai):new T2(0,new T2(0,_8U,new T(function(){if(_bH<=0){if(_bH>=0){return _bH;}else{return E(_6s);}}else{return E(_6r);}})),_bF+_bN):new T2(0,new T2(0,new T(function(){if(_bG<=0){if(_bG>=0){return _bG;}else{return E(_6s);}}else{return E(_6r);}}),_8U),_bF+_bL);}else{var _bO=new T(function(){var _bP=E(_bI);if(!_bP){return E(_a6);}else{return new T2(0,new T(function(){return _bG/_bP;}),new T(function(){return _bH/_bP;}));}});return new T2(0,_bO,_bF-_bI);}},_bQ=E(_bA);if(!_bQ){return new F(function(){return _bM(_bz/2);});}else{if(_bQ<=0){return new F(function(){return _bM(_bz/2+_bQ);});}else{return new F(function(){return _bM(_bz/2-_bQ);});}}}else{var _bR=new T(function(){var _bS=E(_bI);if(!_bS){return E(_a6);}else{return new T2(0,new T(function(){return _bG/_bS;}),new T(function(){return _bH/_bS;}));}});return new T2(0,_bR,_bF-_bI);}},_bT=E(_bu);if(!_bT){var _bU=B(_bK(_bq/2));return new T2(0,_bU.a,_bU.b);}else{if(_bT<=0){var _bV=B(_bK(_bq/2+_bT));return new T2(0,_bV.a,_bV.b);}else{var _bW=B(_bK(_bq/2-_bT));return new T2(0,_bW.a,_bW.b);}}}),_bX=new T(function(){return E(E(_bJ).b);}),_bY=new T(function(){var _bZ=E(E(_bJ).a),_c0=_bZ.a,_c1=_bZ.b;return new T2(0,new T(function(){return E(_c0)*Math.cos(_bn)-E(_c1)*Math.sin(_bn);}),new T(function(){return E(_c0)*Math.sin(_bn)+E(_c1)*Math.cos(_bn);}));}),_c2=new T(function(){var _c3=E(_bY);return new T2(0,new T(function(){return _bk-E(_c3.a)*_bF;}),new T(function(){return _bo-E(_c3.b)*_bF;}));}),_c4=new T(function(){var _c5=E(_c2),_c6=E(_bY);return new T2(0,new T(function(){return E(_c5.a)+E(_c6.a)*E(_bX)-_bm;}),new T(function(){return E(_c5.b)+E(_c6.b)*E(_bX)-_bp;}));}),_c7=new T(function(){var _c8=E(_c2);return new T2(0,new T(function(){return E(_c8.a)-_bk;}),new T(function(){return E(_c8.b)-_bo;}));});return new T2(1,new T5(0,_c7,_c4,_bY,_bY,_bX),_4);}else{return __Z;}};if(_bB>_bA){if(_bC>_bB){return new F(function(){return _bD(_bB);});}else{return new F(function(){return _bD(_bC);});}}else{if(_bC>_bA){return new F(function(){return _bD(_bA);});}else{return new F(function(){return _bD(_bC);});}}};if(_bv>_bu){if(_bw>_bv){return new F(function(){return _bx(_bv);});}else{return new F(function(){return _bx(_bw);});}}else{if(_bw>_bu){return new F(function(){return _bx(_bu);});}else{return new F(function(){return _bx(_bw);});}}}}else{var _c9=E(_b0);if(!_c9._){return new F(function(){return _al(_ac,B(_aX(_c9,_b1,_b2,_aZ)));});}else{var _ca=new T(function(){var _cb=function(_cc){var _cd=E(_cc),_ce=new T(function(){return E(E(_b1).c);}),_cf=new T(function(){return E(_cd.a)*E(_c9.a)*0.5;}),_cg=new T(function(){return E(_cd.b)*E(_c9.b)*0.5;});return new T2(0,new T(function(){var _ch=E(_ce);return E(E(_b1).a)+(E(_cf)*Math.cos(_ch)-E(_cg)*Math.sin(_ch));}),new T(function(){var _ci=E(_ce);return E(E(_b1).b)+E(_cf)*Math.sin(_ci)+E(_cg)*Math.cos(_ci);}));};return B(_al(_cb,_aJ));}),_cj=new T(function(){return B(_aK(_ca,new T(function(){var _ck=E(_ca);if(!_ck._){return E(_az);}else{return E(_ck.b);}},1)));}),_cl=function(_cm){var _cn=E(_cm),_co=new T(function(){return E(E(_aZ).c);}),_cp=new T(function(){return E(_cn.a)*E(_b2.a)*0.5;}),_cq=new T(function(){return E(_cn.b)*E(_b2.b)*0.5;});return new T2(0,new T(function(){var _cr=E(_co);return E(E(_aZ).a)+(E(_cp)*Math.cos(_cr)-E(_cq)*Math.sin(_cr));}),new T(function(){var _cs=E(_co);return E(E(_aZ).b)+E(_cp)*Math.sin(_cs)+E(_cq)*Math.cos(_cs);}));},_ct=B(_al(_cl,_aJ)),_cu=new T(function(){var _cv=function(_cw){var _cx=E(_ct);if(!_cx._){return E(_az);}else{return new F(function(){return _al(function(_cy){return new F(function(){return _8I(_cw,_cy);});},_cx.b);});}};return B(_al(_cv,_cj));}),_cz=B(_aK(_ct,new T(function(){var _cA=E(_ct);if(!_cA._){return E(_az);}else{return E(_cA.b);}},1))),_cB=function(_cC){var _cD=E(_ca);if(!_cD._){return E(_az);}else{return new F(function(){return _al(function(_cy){return new F(function(){return _8I(_cC,_cy);});},_cD.b);});}},_cE=B(_al(_cB,_cz));if(!B(_8F(B(_0(_cE,_cu))))){var _cF=B(_8w(_cE,_8X));if(!_cF._){return E(_ak);}else{var _cG=E(_cF.a),_cH=E(B(_7s(_cF.b,_cG.a,_cG.b)).b),_cI=B(_7K(_8c,B(_6P(_cE,_cH))));if(!_cI._){return E(_8f);}else{var _cJ=B(_8g(_cu,_8X));if(!_cJ._){return E(_ak);}else{var _cK=E(_cJ.a),_cL=E(B(_7a(_cJ.b,_cK.a,_cK.b)).b),_cM=B(_7K(_8c,B(_6P(_cu,_cL))));if(!_cM._){return E(_8f);}else{var _cN=B(_82(_cM.b,_cM.a)),_cO=B(_8m(_cI.b,_cI.a)),_cP=E(_cO);if(!_cP._){var _cQ=E(_cN),_cR=false;}else{var _cS=E(_cN);if(!_cS._){var _cT=true;}else{var _cT=E(_cP.a)>E(_cS.a);}var _cR=_cT;}var _cU=function(_cV,_cW){var _cX=function(_cY,_cZ,_d0,_d1){var _d2=E(_d0),_d3=E(_d1),_d4=E(_d2.a),_d5=E(_d2.b),_d6=E(_d3.a),_d7=E(_d3.b),_d8=_d6-_d4,_d9=_d7-_d5,_da=Math.sqrt(_d8*_d8+_d9*_d9);if(!_da){var _db=E(_cY),_dc=E(_db.a),_dd=E(_db.b),_de=E(_cZ),_df= -(E(_de.b)-_dd),_dg=E(_de.a)-_dc,_dh=function(_di,_dj,_dk){var _dl=E(_dj),_dm=E(_dk),_dn=_d4+_d5*0,_do=_d6+_d7*0-_dn,_dp=new T(function(){var _dq=E(E(_di).a);return (E(_dq.a)+E(_dq.b)*0-_dn)/_do;}),_dr=new T(function(){var _ds=E(E(_di).b);return (E(_ds.a)+E(_ds.b)*0-_dn)/_do;}),_dt=function(_du){var _dv=new T(function(){var _dw=E(_du);if(0>_dw){return E(_8U);}else{if(1>_dw){return E(_dw);}else{return E(_8V);}}}),_dx=new T(function(){return E(_dr)-E(_dv);}),_dy=new T(function(){return E(_dv)-E(_dp);});return new T2(0,new T(function(){var _dz=E(_dx),_dA=E(_dy);return (E(_dl.a)*_dz+E(_dm.a)*_dA)/(_dz+_dA);}),new T(function(){var _dB=E(_dx),_dC=E(_dy);return (E(_dl.b)*_dB+E(_dm.b)*_dC)/(_dB+_dC);}));},_dD=B(_dt(_dp)),_dE=E(_dD.a),_dF=E(_dD.b),_dG=new T(function(){var _dH=B(_dt(_dr)),_dI=E(_dH.a),_dJ=E(_dH.b),_dK=(_df*_dI+_dg*_dJ-(_df*_dc+_dg*_dd))/Math.sqrt(_df*_df+_dg*_dg);if(_dK<0){return new T2(1,new T2(0,new T2(0,_dI,_dJ), -_dK),_4);}else{return __Z;}}),_dL=(_df*_dE+_dg*_dF-(_df*_dc+_dg*_dd))/Math.sqrt(_df*_df+_dg*_dg);if(_dL<0){var _dM=new T2(1,new T2(0,new T2(0,_dE,_dF), -_dL),_dG);}else{var _dM=E(_dG);}var _dN=new T(function(){return B(_al(_7U,_dM));}),_dO= -0,_dP=new T(function(){var _dQ=function(_dR){var _dS=E(_dR),_dT=_dS.b,_dU=E(_dS.a);return new T2(0,new T(function(){return E(_dU.a)+_dO*E(_dT);}),new T(function(){return E(_dU.b)+E(_dT);}));};return B(_al(_dQ,_dM));}),_dV=new T(function(){if(!E(_cR)){var _dW=new T(function(){return E(E(_b1).b);}),_dX=new T(function(){return E(E(_b1).a);});return B(_al(function(_cy){return new F(function(){return _6B(new T2(0,_dX,_dW),_cy);});},_dP));}else{var _dY=new T(function(){return E(E(_b1).b);}),_dZ=new T(function(){return E(E(_b1).a);});return B(_al(function(_cy){return new F(function(){return _6B(new T2(0,_dZ,_dY),_cy);});},_dN));}}),_e0=new T(function(){if(!E(_cR)){return new T2(0,_dO,1);}else{return new T2(0, -_dO,-1);}}),_e1=function(_e2,_e3,_e4){return new T5(0,_e2,_e3,_e0,_e0,_e4);};if(!E(_cR)){var _e5=new T(function(){return E(E(_aZ).b);}),_e6=new T(function(){return E(E(_aZ).a);});return new F(function(){return _aP(_e1,B(_al(function(_cy){return new F(function(){return _6B(new T2(0,_e6,_e5),_cy);});},_dN)),_dV,new T(function(){return B(_al(_aw,_dM));},1));});}else{var _e7=new T(function(){return E(E(_aZ).b);}),_e8=new T(function(){return E(E(_aZ).a);});return new F(function(){return _aP(_e1,B(_al(function(_cy){return new F(function(){return _6B(new T2(0,_e8,_e7),_cy);});},_dP)),_dV,new T(function(){return B(_al(_aw,_dM));},1));});}},_e9=function(_ea){var _eb=function(_ec,_ed){while(1){var _ee=B((function(_ef,_eg){var _eh=E(_ef);if(!_eh._){return __Z;}else{var _ei=_eh.b,_ej=E(_eg);if(!_ej._){return __Z;}else{var _ek=_ej.b,_el=E(_eh.a),_em=(_df*E(_el.a)+_dg*E(_el.b)-(_df*_dc+_dg*_dd))/Math.sqrt(_df*_df+_dg*_dg);if(_em<0){return new T2(1,new T2(0,new T1(1,_em),_ej.a),new T(function(){return B(_eb(_ei,_ek));}));}else{_ec=_ei;_ed=_ek;return __continue;}}}})(_ec,_ed));if(_ee!=__continue){return _ee;}}};return new F(function(){return _eb(_ea,_8X);});},_en=function(_eo){var _ep=B(_6P(_cW,_eo)),_eq=E(_ep.a),_er=E(_ep.b),_es=E(_eq.a)-E(_er.a),_et=E(_eq.b)-E(_er.b),_eu=function(_ev,_ew){var _ex=function(_ey){var _ez=B(_6P(_cW,B(_ap(_eo+1|0,4)))),_eA=E(_ez.b),_eB=E(_ez.a),_eC=E(_eA.a)-E(_eB.a),_eD=E(_eA.b)-E(_eB.b),_eE=Math.sqrt(_eC*_eC+_eD*_eD);if(!_eE){return (_ey<=1)?new T3(0,_ez,_eB,_eA):new T3(0,new T2(0,_er,_eq),_er,_eq);}else{var _eF=_eC/_eE+0*(_eD/_eE);return (_eF==0)?(_ey<=0)?new T3(0,_ez,_eB,_eA):new T3(0,new T2(0,_er,_eq),_er,_eq):(_eF<=0)?(_ey<= -_eF)?new T3(0,_ez,_eB,_eA):new T3(0,new T2(0,_er,_eq),_er,_eq):(_ey<=_eF)?new T3(0,_ez,_eB,_eA):new T3(0,new T2(0,_er,_eq),_er,_eq);}},_eG=_ev+0*_ew;if(!_eG){return new F(function(){return _ex(0);});}else{if(_eG<=0){return new F(function(){return _ex( -_eG);});}else{return new F(function(){return _ex(_eG);});}}},_eH=Math.sqrt(_es*_es+_et*_et);if(!_eH){return new F(function(){return _eu(1,0);});}else{return new F(function(){return _eu(_es/_eH,_et/_eH);});}};if(!E(_cR)){var _eI=E(_ct);if(!_eI._){return E(_az);}else{var _eJ=B(_e9(_eI.b));if(!_eJ._){return E(_8W);}else{var _eK=E(_eJ.a),_eL=B(_en(E(B(_6T(_eJ.b,_eK.a,_eK.b)).b)));return new F(function(){return _dh(_eL.a,_eL.b,_eL.c);});}}}else{var _eM=E(_ca);if(!_eM._){return E(_az);}else{var _eN=B(_e9(_eM.b));if(!_eN._){return E(_8W);}else{var _eO=E(_eN.a),_eP=B(_en(E(B(_6T(_eN.b,_eO.a,_eO.b)).b)));return new F(function(){return _dh(_eP.a,_eP.b,_eP.c);});}}}}else{var _eQ=_d8/_da,_eR=_d9/_da,_eS=E(_cY),_eT=E(_eS.a),_eU=E(_eS.b),_eV=E(_cZ),_eW= -(E(_eV.b)-_eU),_eX=E(_eV.a)-_eT,_eY=function(_eZ,_f0,_f1){var _f2=E(_f0),_f3=E(_f1),_f4=_d4*_eQ+_d5*_eR,_f5=_d6*_eQ+_d7*_eR-_f4,_f6=new T(function(){var _f7=E(E(_eZ).a);return (E(_f7.a)*_eQ+E(_f7.b)*_eR-_f4)/_f5;}),_f8=new T(function(){var _f9=E(E(_eZ).b);return (E(_f9.a)*_eQ+E(_f9.b)*_eR-_f4)/_f5;}),_fa=function(_fb){var _fc=new T(function(){var _fd=E(_fb);if(0>_fd){return E(_8U);}else{if(1>_fd){return E(_fd);}else{return E(_8V);}}}),_fe=new T(function(){return E(_f8)-E(_fc);}),_ff=new T(function(){return E(_fc)-E(_f6);});return new T2(0,new T(function(){var _fg=E(_fe),_fh=E(_ff);return (E(_f2.a)*_fg+E(_f3.a)*_fh)/(_fg+_fh);}),new T(function(){var _fi=E(_fe),_fj=E(_ff);return (E(_f2.b)*_fi+E(_f3.b)*_fj)/(_fi+_fj);}));},_fk=B(_fa(_f6)),_fl=E(_fk.a),_fm=E(_fk.b),_fn=new T(function(){var _fo=B(_fa(_f8)),_fp=E(_fo.a),_fq=E(_fo.b),_fr=(_eW*_fp+_eX*_fq-(_eW*_eT+_eX*_eU))/Math.sqrt(_eW*_eW+_eX*_eX);if(_fr<0){return new T2(1,new T2(0,new T2(0,_fp,_fq), -_fr),_4);}else{return __Z;}}),_fs=(_eW*_fl+_eX*_fm-(_eW*_eT+_eX*_eU))/Math.sqrt(_eW*_eW+_eX*_eX);if(_fs<0){var _ft=new T2(1,new T2(0,new T2(0,_fl,_fm), -_fs),_fn);}else{var _ft=E(_fn);}var _fu=new T(function(){return B(_al(_7U,_ft));}),_fv= -_eR,_fw=new T(function(){var _fx=function(_fy){var _fz=E(_fy),_fA=_fz.b,_fB=E(_fz.a);return new T2(0,new T(function(){return E(_fB.a)+_fv*E(_fA);}),new T(function(){return E(_fB.b)+_eQ*E(_fA);}));};return B(_al(_fx,_ft));}),_fC=new T(function(){if(!E(_cR)){var _fD=new T(function(){return E(E(_b1).b);}),_fE=new T(function(){return E(E(_b1).a);});return B(_al(function(_cy){return new F(function(){return _6B(new T2(0,_fE,_fD),_cy);});},_fw));}else{var _fF=new T(function(){return E(E(_b1).b);}),_fG=new T(function(){return E(E(_b1).a);});return B(_al(function(_cy){return new F(function(){return _6B(new T2(0,_fG,_fF),_cy);});},_fu));}}),_fH=new T(function(){if(!E(_cR)){return new T2(0,_fv,_eQ);}else{return new T2(0, -_fv, -_eQ);}}),_fI=function(_fJ,_fK,_fL){return new T5(0,_fJ,_fK,_fH,_fH,_fL);};if(!E(_cR)){var _fM=new T(function(){return E(E(_aZ).b);}),_fN=new T(function(){return E(E(_aZ).a);});return new F(function(){return _aP(_fI,B(_al(function(_cy){return new F(function(){return _6B(new T2(0,_fN,_fM),_cy);});},_fu)),_fC,new T(function(){return B(_al(_aw,_ft));},1));});}else{var _fO=new T(function(){return E(E(_aZ).b);}),_fP=new T(function(){return E(E(_aZ).a);});return new F(function(){return _aP(_fI,B(_al(function(_cy){return new F(function(){return _6B(new T2(0,_fP,_fO),_cy);});},_fw)),_fC,new T(function(){return B(_al(_aw,_ft));},1));});}},_fQ=function(_fR){var _fS=function(_fT,_fU){while(1){var _fV=B((function(_fW,_fX){var _fY=E(_fW);if(!_fY._){return __Z;}else{var _fZ=_fY.b,_g0=E(_fX);if(!_g0._){return __Z;}else{var _g1=_g0.b,_g2=E(_fY.a),_g3=(_eW*E(_g2.a)+_eX*E(_g2.b)-(_eW*_eT+_eX*_eU))/Math.sqrt(_eW*_eW+_eX*_eX);if(_g3<0){return new T2(1,new T2(0,new T1(1,_g3),_g0.a),new T(function(){return B(_fS(_fZ,_g1));}));}else{_fT=_fZ;_fU=_g1;return __continue;}}}})(_fT,_fU));if(_fV!=__continue){return _fV;}}};return new F(function(){return _fS(_fR,_8X);});},_g4=function(_g5){var _g6=B(_6P(_cW,_g5)),_g7=E(_g6.a),_g8=E(_g6.b),_g9=E(_g7.a)-E(_g8.a),_ga=E(_g7.b)-E(_g8.b),_gb=function(_gc,_gd){var _ge=function(_gf){var _gg=B(_6P(_cW,B(_ap(_g5+1|0,4)))),_gh=E(_gg.b),_gi=E(_gg.a),_gj=E(_gh.a)-E(_gi.a),_gk=E(_gh.b)-E(_gi.b),_gl=Math.sqrt(_gj*_gj+_gk*_gk);if(!_gl){var _gm=_eQ+_eR*0;return (_gm==0)?(_gf<=0)?new T3(0,_gg,_gi,_gh):new T3(0,new T2(0,_g8,_g7),_g8,_g7):(_gm<=0)?(_gf<= -_gm)?new T3(0,_gg,_gi,_gh):new T3(0,new T2(0,_g8,_g7),_g8,_g7):(_gf<=_gm)?new T3(0,_gg,_gi,_gh):new T3(0,new T2(0,_g8,_g7),_g8,_g7);}else{var _gn=_eQ*(_gj/_gl)+_eR*(_gk/_gl);return (_gn==0)?(_gf<=0)?new T3(0,_gg,_gi,_gh):new T3(0,new T2(0,_g8,_g7),_g8,_g7):(_gn<=0)?(_gf<= -_gn)?new T3(0,_gg,_gi,_gh):new T3(0,new T2(0,_g8,_g7),_g8,_g7):(_gf<=_gn)?new T3(0,_gg,_gi,_gh):new T3(0,new T2(0,_g8,_g7),_g8,_g7);}},_go=_eQ*_gc+_eR*_gd;if(!_go){return new F(function(){return _ge(0);});}else{if(_go<=0){return new F(function(){return _ge( -_go);});}else{return new F(function(){return _ge(_go);});}}},_gp=Math.sqrt(_g9*_g9+_ga*_ga);if(!_gp){return new F(function(){return _gb(1,0);});}else{return new F(function(){return _gb(_g9/_gp,_ga/_gp);});}};if(!E(_cR)){var _gq=E(_ct);if(!_gq._){return E(_az);}else{var _gr=B(_fQ(_gq.b));if(!_gr._){return E(_8W);}else{var _gs=E(_gr.a),_gt=B(_g4(E(B(_6T(_gr.b,_gs.a,_gs.b)).b)));return new F(function(){return _eY(_gt.a,_gt.b,_gt.c);});}}}else{var _gu=E(_ca);if(!_gu._){return E(_az);}else{var _gv=B(_fQ(_gu.b));if(!_gv._){return E(_8W);}else{var _gw=E(_gv.a),_gx=B(_g4(E(B(_6T(_gv.b,_gw.a,_gw.b)).b)));return new F(function(){return _eY(_gx.a,_gx.b,_gx.c);});}}}}};if(!E(_cR)){if(!E(_cN)._){return E(_a5);}else{var _gy=B(_6P(_cV,_cL)),_gz=_gy.a,_gA=_gy.b;return new F(function(){return _cX(_gz,_gA,_gz,_gA);});}}else{if(!E(_cO)._){return E(_a5);}else{var _gB=B(_6P(_cV,_cH)),_gC=_gB.a,_gD=_gB.b;return new F(function(){return _cX(_gC,_gD,_gC,_gD);});}}};if(!E(_cR)){return new F(function(){return _cU(_cj,_cz);});}else{return new F(function(){return _cU(_cz,_cj);});}}}}}}else{return __Z;}}}},_gE=new T(function(){return B(_41(-1,1));}),_gF=new T(function(){return eval("scrH");}),_gG=function(_gH,_gI){var _gJ=new T(function(){var _gK=E(E(_gH).b),_gL=E(E(_gI).b);if(E(_gK.a)!=E(_gL.a)){return false;}else{if(E(_gK.b)!=E(_gL.b)){return false;}else{return E(_gK.c)==E(_gL.c);}}}),_gM=new T(function(){return E(E(_gI).a);}),_gN=function(_gO){var _gP=E(_gO);if(!_gP._){return __Z;}else{var _gQ=_gP.a,_gR=new T(function(){return B(_gN(_gP.b));}),_gS=function(_gT){var _gU=E(_gT);if(!_gU._){return E(_gR);}else{var _gV=_gU.a,_gW=new T(function(){return B(_gS(_gU.b));}),_gX=function(_gY){var _gZ=E(_gH),_h0=new T(function(){var _h1=E(E(_gI).b);return new T3(0,new T(function(){return E(_h1.a)+E(_gQ)*E(_1t);}),new T(function(){return E(_h1.b)+E(_gV)*E(_gF);}),_h1.c);});return new F(function(){return _0(B(_aX(_gZ.a,_gZ.b,_gM,_h0)),_gW);});};if(!E(_gJ)){return new F(function(){return _gX(_);});}else{if(!E(_gQ)){if(!E(_gV)){return E(_gW);}else{return new F(function(){return _gX(_);});}}else{return new F(function(){return _gX(_);});}}}};return new F(function(){return _gS(_gE);});}};return new F(function(){return _gN(_gE);});},_h2=function(_h3,_h4){var _h5=E(_h3),_h6=E(_h4);return E(_h5.a)*E(_h6.b)-E(_h6.a)*E(_h5.b);},_h7=function(_h8){var _h9=E(_h8);if(!_h9._){return __Z;}else{return new F(function(){return _0(_h9.a,new T(function(){return B(_h7(_h9.b));},1));});}},_ha=function(_hb){var _hc=E(_hb);if(!_hc._){return __Z;}else{return new F(function(){return _0(_hc.a,new T(function(){return B(_ha(_hc.b));},1));});}},_hd=new T(function(){return B(unCStr(")"));}),_he=function(_hf,_hg){var _hh=new T(function(){var _hi=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_2u(0,_hg,_4)),_hd));})));},1);return B(_0(B(_2u(0,_hf,_4)),_hi));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_hh)));});},_hj=function(_hk,_hl,_hm,_hn,_ho,_){if(_hk<=_hl){var _hp=function(_hq,_hr,_){var _hs=_hq+1|0;if(_hs<=_hl){var _ht=new T(function(){if(_hk>_hq){return E(_6q);}else{if(_hq>_hl){return E(_6q);}else{var _hu=_hq-_hk|0;if(0>_hu){return B(_he(_hu,_hm));}else{if(_hu>=_hm){return B(_he(_hu,_hm));}else{return E(_hn[_hu]);}}}}}),_hv=function(_hw,_hx,_){var _hy=new T(function(){var _hz=function(_hA){var _hB=E(_hA),_hC=_hB.c,_hD=_hB.d;return new T5(0,_hq,_hw,new T3(0,new T(function(){return E(E(_hC).a);}),new T(function(){return E(E(_hC).b);}),new T(function(){return B(_h2(_hB.a,_hC));})),new T3(0,new T(function(){return E(E(_hD).a);}),new T(function(){return E(E(_hD).b);}),new T(function(){return B(_h2(_hB.b,_hD));})),_hB.e);};return B(_al(_hz,B(_gG(_ht,new T(function(){if(_hk>_hw){return E(_6q);}else{if(_hw>_hl){return E(_6q);}else{var _hE=_hw-_hk|0;if(0>_hE){return B(_he(_hE,_hm));}else{if(_hE>=_hm){return B(_he(_hE,_hm));}else{return E(_hn[_hE]);}}}}})))));});if(_hw!=_hl){var _hF=B(_hv(_hw+1|0,_hx,_));return new T2(0,new T2(1,_hy,new T(function(){return E(E(_hF).a);})),new T(function(){return E(E(_hF).b);}));}else{return new T2(0,new T2(1,_hy,_4),_hx);}},_hG=B(_hv(_hs,_hr,_));if(_hq!=_hl){var _hH=B(_hp(_hs,new T(function(){return E(E(_hG).b);}),_));return new T2(0,new T2(1,new T(function(){return B(_ha(E(_hG).a));}),new T(function(){return E(E(_hH).a);})),new T(function(){return E(E(_hH).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_ha(E(_hG).a));}),_4),new T(function(){return E(E(_hG).b);}));}}else{if(_hq!=_hl){var _hI=B(_hp(_hs,_hr,_));return new T2(0,new T2(1,_4,new T(function(){return E(E(_hI).a);})),new T(function(){return E(E(_hI).b);}));}else{return new T2(0,new T2(1,_4,_4),_hr);}}},_hJ=B(_hp(_hk,_ho,_));return new T2(0,new T(function(){return B(_h7(E(_hJ).a));}),new T(function(){return E(E(_hJ).b);}));}else{return new T2(0,_4,_ho);}},_hK=function(_hL){var _hM=E(_hL),_hN=_hM.c,_hO=new T(function(){var _hP=E(_hM.b),_hQ=E(_hN);return new T3(0,new T(function(){return E(_hP.a)+E(_hQ.a)*0.2;}),new T(function(){return E(_hP.b)+E(_hQ.b)*0.2;}),new T(function(){return E(_hP.c)+E(_hQ.c)*0.2;}));});return new T5(0,_hM.a,_hO,_hN,_hM.d,_hM.e);},_hR=function(_hS,_hT,_hU,_hV,_hW){var _hX=new T(function(){var _hY=E(_hU),_hZ=E(_hV),_i0=new T(function(){var _i1=E(E(_hT).b)/E(_gF);return 0.2*Math.sin((_i1+_i1)*3.141592653589793);});return new T3(0,new T(function(){return E(_hY.a)+E(_hZ.a)*E(_i0);}),new T(function(){return E(_hY.b)+E(_hZ.b)*E(_i0);}),new T(function(){return E(_hY.c)+E(_hZ.c)*E(_i0);}));});return new T5(0,_hS,_hT,_hX,_hV,_hW);},_i2=function(_i3){var _i4=E(_i3),_i5=B(_hR(_i4.a,_i4.b,_i4.c,_i4.d,_i4.e));return new T5(0,_i5.a,_i5.b,_i5.c,_i5.d,_i5.e);},_i6=function(_i7,_){return new T2(0,_4,_i7);},_i8=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_i9=new T(function(){return B(err(_i8));}),_ia=function(_ib,_ic){var _id=new T(function(){var _ie=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_2u(0,_ib,_4)),_hd));})));},1);return B(_0(B(_2u(0,_ic,_4)),_ie));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_id)));});},_if=0.6,_ig=function(_ih){var _ii=E(_ih);if(!_ii._){return E(_i6);}else{var _ij=_ii.a,_ik=new T(function(){return B(_ig(_ii.b));}),_il=new T(function(){return 0.1*E(E(_ij).e)/0.2;}),_im=new T(function(){var _in=E(_ij);if(E(_in.a)!=E(_in.b)){return E(_8V);}else{return E(_if);}}),_io=function(_ip,_){var _iq=E(_ip),_ir=_iq.c,_is=_iq.d,_it=E(_iq.a),_iu=E(_iq.b),_iv=E(_ij),_iw=E(_iv.a);if(_it>_iw){return E(_i9);}else{if(_iw>_iu){return E(_i9);}else{var _ix=_iw-_it|0;if(0>_ix){return new F(function(){return _ia(_ir,_ix);});}else{if(_ix>=_ir){return new F(function(){return _ia(_ir,_ix);});}else{var _iy=E(_is[_ix]),_iz=E(_iy.e),_iA=E(_iz.a),_iB=E(_iz.b),_iC=E(_iz.c),_iD=E(_iv.c),_iE=E(_iD.a),_iF=E(_iD.b),_iG=E(_iD.c),_iH=E(_iv.b);if(_it>_iH){return E(_i9);}else{if(_iH>_iu){return E(_i9);}else{var _iI=_iH-_it|0;if(0>_iI){return new F(function(){return _he(_iI,_ir);});}else{if(_iI>=_ir){return new F(function(){return _he(_iI,_ir);});}else{var _iJ=E(_is[_iI]),_iK=E(_iJ.e),_iL=E(_iK.a),_iM=E(_iK.b),_iN=E(_iK.c),_iO=E(_iv.d),_iP=E(_iO.a),_iQ=E(_iO.b),_iR=E(_iO.c),_iS=_iE*_iA*_iE+_iF*_iB*_iF+_iG*_iC*_iG+_iP*_iL*_iP+_iQ*_iM*_iQ+_iR*_iN*_iR;if(!_iS){var _iT=B(A2(_ik,_iq,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_iT).a);})),new T(function(){return E(E(_iT).b);}));}else{var _iU=E(_iy.c),_iV=E(_iU.a),_iW=E(_iU.b),_iX=E(_iU.c),_iY=E(_iJ.c),_iZ= -((_iV*_iE+_iW*_iF+_iX*_iG-(E(_iY.a)*_iP+E(_iY.b)*_iQ+E(_iY.c)*_iR)-E(_il))/_iS);if(_iZ<0){var _j0=B(A2(_ik,_iq,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_j0).a);})),new T(function(){return E(E(_j0).b);}));}else{var _j1=new T(function(){var _j2=function(_){var _j3=newArr(_ir,_1k),_j4=_j3,_j5=function(_j6,_){while(1){if(_j6!=_ir){var _=_j4[_j6]=_is[_j6],_j7=_j6+1|0;_j6=_j7;continue;}else{return E(_);}}},_=B(_j5(0,_)),_j8=new T(function(){return _iZ*E(_im);}),_=_j4[_ix]=new T5(0,_iy.a,_iy.b,new T3(0,new T(function(){return _iV+_iA*_iE*E(_j8);}),new T(function(){return _iW+_iB*_iF*E(_j8);}),new T(function(){return _iX+_iC*_iG*E(_j8);})),_iy.d,_iz);return new T4(0,E(_it),E(_iu),_ir,_j4);},_j9=B(_1M(_j2)),_ja=_j9.c,_jb=_j9.d,_jc=E(_j9.a),_jd=E(_j9.b);if(_jc>_iH){return E(_j9);}else{if(_iH>_jd){return E(_j9);}else{var _je=function(_){var _jf=newArr(_ja,_1k),_jg=_jf,_jh=function(_ji,_){while(1){if(_ji!=_ja){var _=_jg[_ji]=_jb[_ji],_jj=_ji+1|0;_ji=_jj;continue;}else{return E(_);}}},_=B(_jh(0,_)),_jk=_iH-_jc|0;if(0>_jk){return new F(function(){return _he(_jk,_ja);});}else{if(_jk>=_ja){return new F(function(){return _he(_jk,_ja);});}else{var _jl=new T(function(){var _jm=E(_jb[_jk]),_jn=new T(function(){return _iZ*E(_im);}),_jo=new T(function(){var _jp=E(_jm.c);return new T3(0,new T(function(){return E(_jp.a)-_iL*_iP*E(_jn);}),new T(function(){return E(_jp.b)-_iM*_iQ*E(_jn);}),new T(function(){return E(_jp.c)-_iN*_iR*E(_jn);}));});return new T5(0,_jm.a,_jm.b,_jo,_jm.d,_jm.e);}),_=_jg[_jk]=_jl;return new T4(0,E(_jc),E(_jd),_ja,_jg);}}};return B(_1M(_je));}}}),_jq=B(A2(_ik,_j1,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_jq).a);})),new T(function(){return E(E(_jq).b);}));}}}}}}}}}}};return E(_io);}},_jr=new T1(0,1),_js=function(_jt,_ju){var _jv=E(_jt);if(!_jv._){var _jw=_jv.a,_jx=E(_ju);if(!_jx._){var _jy=_jx.a;return (_jw!=_jy)?(_jw>_jy)?2:0:1;}else{var _jz=I_compareInt(_jx.a,_jw);return (_jz<=0)?(_jz>=0)?1:2:0;}}else{var _jA=_jv.a,_jB=E(_ju);if(!_jB._){var _jC=I_compareInt(_jA,_jB.a);return (_jC>=0)?(_jC<=0)?1:2:0;}else{var _jD=I_compare(_jA,_jB.a);return (_jD>=0)?(_jD<=0)?1:2:0;}}},_jE=new T(function(){return B(unCStr("base"));}),_jF=new T(function(){return B(unCStr("GHC.Exception"));}),_jG=new T(function(){return B(unCStr("ArithException"));}),_jH=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_jE,_jF,_jG),_jI=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_jH,_4,_4),_jJ=function(_jK){return E(_jI);},_jL=function(_jM){var _jN=E(_jM);return new F(function(){return _97(B(_95(_jN.a)),_jJ,_jN.b);});},_jO=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_jP=new T(function(){return B(unCStr("denormal"));}),_jQ=new T(function(){return B(unCStr("divide by zero"));}),_jR=new T(function(){return B(unCStr("loss of precision"));}),_jS=new T(function(){return B(unCStr("arithmetic underflow"));}),_jT=new T(function(){return B(unCStr("arithmetic overflow"));}),_jU=function(_jV,_jW){switch(E(_jV)){case 0:return new F(function(){return _0(_jT,_jW);});break;case 1:return new F(function(){return _0(_jS,_jW);});break;case 2:return new F(function(){return _0(_jR,_jW);});break;case 3:return new F(function(){return _0(_jQ,_jW);});break;case 4:return new F(function(){return _0(_jP,_jW);});break;default:return new F(function(){return _0(_jO,_jW);});}},_jX=function(_jY){return new F(function(){return _jU(_jY,_4);});},_jZ=function(_k0,_k1,_k2){return new F(function(){return _jU(_k1,_k2);});},_k3=function(_k4,_k5){return new F(function(){return _2I(_jU,_k4,_k5);});},_k6=new T3(0,_jZ,_jX,_k3),_k7=new T(function(){return new T5(0,_jJ,_k6,_k8,_jL,_jX);}),_k8=function(_9G){return new T2(0,_k7,_9G);},_k9=3,_ka=new T(function(){return B(_k8(_k9));}),_kb=new T(function(){return die(_ka);}),_kc=function(_kd,_ke){var _kf=E(_kd);return (_kf._==0)?_kf.a*Math.pow(2,_ke):I_toNumber(_kf.a)*Math.pow(2,_ke);},_kg=function(_kh,_ki){var _kj=E(_kh);if(!_kj._){var _kk=_kj.a,_kl=E(_ki);return (_kl._==0)?_kk==_kl.a:(I_compareInt(_kl.a,_kk)==0)?true:false;}else{var _km=_kj.a,_kn=E(_ki);return (_kn._==0)?(I_compareInt(_km,_kn.a)==0)?true:false:(I_compare(_km,_kn.a)==0)?true:false;}},_ko=function(_kp){var _kq=E(_kp);if(!_kq._){return E(_kq.a);}else{return new F(function(){return I_toInt(_kq.a);});}},_kr=function(_ks,_kt){while(1){var _ku=E(_ks);if(!_ku._){var _kv=_ku.a,_kw=E(_kt);if(!_kw._){var _kx=_kw.a,_ky=addC(_kv,_kx);if(!E(_ky.b)){return new T1(0,_ky.a);}else{_ks=new T1(1,I_fromInt(_kv));_kt=new T1(1,I_fromInt(_kx));continue;}}else{_ks=new T1(1,I_fromInt(_kv));_kt=_kw;continue;}}else{var _kz=E(_kt);if(!_kz._){_ks=_ku;_kt=new T1(1,I_fromInt(_kz.a));continue;}else{return new T1(1,I_add(_ku.a,_kz.a));}}}},_kA=function(_kB,_kC){while(1){var _kD=E(_kB);if(!_kD._){var _kE=E(_kD.a);if(_kE==(-2147483648)){_kB=new T1(1,I_fromInt(-2147483648));continue;}else{var _kF=E(_kC);if(!_kF._){var _kG=_kF.a;return new T2(0,new T1(0,quot(_kE,_kG)),new T1(0,_kE%_kG));}else{_kB=new T1(1,I_fromInt(_kE));_kC=_kF;continue;}}}else{var _kH=E(_kC);if(!_kH._){_kB=_kD;_kC=new T1(1,I_fromInt(_kH.a));continue;}else{var _kI=I_quotRem(_kD.a,_kH.a);return new T2(0,new T1(1,_kI.a),new T1(1,_kI.b));}}}},_kJ=new T1(0,0),_kK=function(_kL,_kM){while(1){var _kN=E(_kL);if(!_kN._){_kL=new T1(1,I_fromInt(_kN.a));continue;}else{return new T1(1,I_shiftLeft(_kN.a,_kM));}}},_kO=function(_kP,_kQ,_kR){if(!B(_kg(_kR,_kJ))){var _kS=B(_kA(_kQ,_kR)),_kT=_kS.a;switch(B(_js(B(_kK(_kS.b,1)),_kR))){case 0:return new F(function(){return _kc(_kT,_kP);});break;case 1:if(!(B(_ko(_kT))&1)){return new F(function(){return _kc(_kT,_kP);});}else{return new F(function(){return _kc(B(_kr(_kT,_jr)),_kP);});}break;default:return new F(function(){return _kc(B(_kr(_kT,_jr)),_kP);});}}else{return E(_kb);}},_kU=function(_kV,_kW){var _kX=E(_kV);if(!_kX._){var _kY=_kX.a,_kZ=E(_kW);return (_kZ._==0)?_kY>_kZ.a:I_compareInt(_kZ.a,_kY)<0;}else{var _l0=_kX.a,_l1=E(_kW);return (_l1._==0)?I_compareInt(_l0,_l1.a)>0:I_compare(_l0,_l1.a)>0;}},_l2=new T1(0,1),_l3=function(_l4,_l5){var _l6=E(_l4);if(!_l6._){var _l7=_l6.a,_l8=E(_l5);return (_l8._==0)?_l7<_l8.a:I_compareInt(_l8.a,_l7)>0;}else{var _l9=_l6.a,_la=E(_l5);return (_la._==0)?I_compareInt(_l9,_la.a)<0:I_compare(_l9,_la.a)<0;}},_lb=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_lc=function(_ld){return new F(function(){return _9E(new T1(0,new T(function(){return B(_9S(_ld,_lb));})),_9m);});},_le=function(_lf){var _lg=function(_lh,_li){while(1){if(!B(_l3(_lh,_lf))){if(!B(_kU(_lh,_lf))){if(!B(_kg(_lh,_lf))){return new F(function(){return _lc("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_li);}}else{return _li-1|0;}}else{var _lj=B(_kK(_lh,1)),_lk=_li+1|0;_lh=_lj;_li=_lk;continue;}}};return new F(function(){return _lg(_l2,0);});},_ll=function(_lm){var _ln=E(_lm);if(!_ln._){var _lo=_ln.a>>>0;if(!_lo){return -1;}else{var _lp=function(_lq,_lr){while(1){if(_lq>=_lo){if(_lq<=_lo){if(_lq!=_lo){return new F(function(){return _lc("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_lr);}}else{return _lr-1|0;}}else{var _ls=imul(_lq,2)>>>0,_lt=_lr+1|0;_lq=_ls;_lr=_lt;continue;}}};return new F(function(){return _lp(1,0);});}}else{return new F(function(){return _le(_ln);});}},_lu=function(_lv){var _lw=E(_lv);if(!_lw._){var _lx=_lw.a>>>0;if(!_lx){return new T2(0,-1,0);}else{var _ly=function(_lz,_lA){while(1){if(_lz>=_lx){if(_lz<=_lx){if(_lz!=_lx){return new F(function(){return _lc("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_lA);}}else{return _lA-1|0;}}else{var _lB=imul(_lz,2)>>>0,_lC=_lA+1|0;_lz=_lB;_lA=_lC;continue;}}};return new T2(0,B(_ly(1,0)),(_lx&_lx-1>>>0)>>>0&4294967295);}}else{var _lD=_lw.a;return new T2(0,B(_ll(_lw)),I_compareInt(I_and(_lD,I_sub(_lD,I_fromInt(1))),0));}},_lE=function(_lF,_lG){var _lH=E(_lF);if(!_lH._){var _lI=_lH.a,_lJ=E(_lG);return (_lJ._==0)?_lI<=_lJ.a:I_compareInt(_lJ.a,_lI)>=0;}else{var _lK=_lH.a,_lL=E(_lG);return (_lL._==0)?I_compareInt(_lK,_lL.a)<=0:I_compare(_lK,_lL.a)<=0;}},_lM=function(_lN,_lO){while(1){var _lP=E(_lN);if(!_lP._){var _lQ=_lP.a,_lR=E(_lO);if(!_lR._){return new T1(0,(_lQ>>>0&_lR.a>>>0)>>>0&4294967295);}else{_lN=new T1(1,I_fromInt(_lQ));_lO=_lR;continue;}}else{var _lS=E(_lO);if(!_lS._){_lN=_lP;_lO=new T1(1,I_fromInt(_lS.a));continue;}else{return new T1(1,I_and(_lP.a,_lS.a));}}}},_lT=function(_lU,_lV){while(1){var _lW=E(_lU);if(!_lW._){var _lX=_lW.a,_lY=E(_lV);if(!_lY._){var _lZ=_lY.a,_m0=subC(_lX,_lZ);if(!E(_m0.b)){return new T1(0,_m0.a);}else{_lU=new T1(1,I_fromInt(_lX));_lV=new T1(1,I_fromInt(_lZ));continue;}}else{_lU=new T1(1,I_fromInt(_lX));_lV=_lY;continue;}}else{var _m1=E(_lV);if(!_m1._){_lU=_lW;_lV=new T1(1,I_fromInt(_m1.a));continue;}else{return new T1(1,I_sub(_lW.a,_m1.a));}}}},_m2=new T1(0,2),_m3=function(_m4,_m5){var _m6=E(_m4);if(!_m6._){var _m7=(_m6.a>>>0&(2<<_m5>>>0)-1>>>0)>>>0,_m8=1<<_m5>>>0;return (_m8<=_m7)?(_m8>=_m7)?1:2:0;}else{var _m9=B(_lM(_m6,B(_lT(B(_kK(_m2,_m5)),_l2)))),_ma=B(_kK(_l2,_m5));return (!B(_kU(_ma,_m9)))?(!B(_l3(_ma,_m9)))?1:2:0;}},_mb=function(_mc,_md){while(1){var _me=E(_mc);if(!_me._){_mc=new T1(1,I_fromInt(_me.a));continue;}else{return new T1(1,I_shiftRight(_me.a,_md));}}},_mf=function(_mg,_mh,_mi,_mj){var _mk=B(_lu(_mj)),_ml=_mk.a;if(!E(_mk.b)){var _mm=B(_ll(_mi));if(_mm<((_ml+_mg|0)-1|0)){var _mn=_ml+(_mg-_mh|0)|0;if(_mn>0){if(_mn>_mm){if(_mn<=(_mm+1|0)){if(!E(B(_lu(_mi)).b)){return 0;}else{return new F(function(){return _kc(_jr,_mg-_mh|0);});}}else{return 0;}}else{var _mo=B(_mb(_mi,_mn));switch(B(_m3(_mi,_mn-1|0))){case 0:return new F(function(){return _kc(_mo,_mg-_mh|0);});break;case 1:if(!(B(_ko(_mo))&1)){return new F(function(){return _kc(_mo,_mg-_mh|0);});}else{return new F(function(){return _kc(B(_kr(_mo,_jr)),_mg-_mh|0);});}break;default:return new F(function(){return _kc(B(_kr(_mo,_jr)),_mg-_mh|0);});}}}else{return new F(function(){return _kc(_mi,(_mg-_mh|0)-_mn|0);});}}else{if(_mm>=_mh){var _mp=B(_mb(_mi,(_mm+1|0)-_mh|0));switch(B(_m3(_mi,_mm-_mh|0))){case 0:return new F(function(){return _kc(_mp,((_mm-_ml|0)+1|0)-_mh|0);});break;case 2:return new F(function(){return _kc(B(_kr(_mp,_jr)),((_mm-_ml|0)+1|0)-_mh|0);});break;default:if(!(B(_ko(_mp))&1)){return new F(function(){return _kc(_mp,((_mm-_ml|0)+1|0)-_mh|0);});}else{return new F(function(){return _kc(B(_kr(_mp,_jr)),((_mm-_ml|0)+1|0)-_mh|0);});}}}else{return new F(function(){return _kc(_mi, -_ml);});}}}else{var _mq=B(_ll(_mi))-_ml|0,_mr=function(_ms){var _mt=function(_mu,_mv){if(!B(_lE(B(_kK(_mv,_mh)),_mu))){return new F(function(){return _kO(_ms-_mh|0,_mu,_mv);});}else{return new F(function(){return _kO((_ms-_mh|0)+1|0,_mu,B(_kK(_mv,1)));});}};if(_ms>=_mh){if(_ms!=_mh){return new F(function(){return _mt(_mi,new T(function(){return B(_kK(_mj,_ms-_mh|0));}));});}else{return new F(function(){return _mt(_mi,_mj);});}}else{return new F(function(){return _mt(new T(function(){return B(_kK(_mi,_mh-_ms|0));}),_mj);});}};if(_mg>_mq){return new F(function(){return _mr(_mg);});}else{return new F(function(){return _mr(_mq);});}}},_mw=new T1(0,2147483647),_mx=new T(function(){return B(_kr(_mw,_l2));}),_my=function(_mz){var _mA=E(_mz);if(!_mA._){var _mB=E(_mA.a);return (_mB==(-2147483648))?E(_mx):new T1(0, -_mB);}else{return new T1(1,I_negate(_mA.a));}},_mC=new T(function(){return 0/0;}),_mD=new T(function(){return -1/0;}),_mE=new T(function(){return 1/0;}),_mF=0,_mG=function(_mH,_mI){if(!B(_kg(_mI,_kJ))){if(!B(_kg(_mH,_kJ))){if(!B(_l3(_mH,_kJ))){return new F(function(){return _mf(-1021,53,_mH,_mI);});}else{return  -B(_mf(-1021,53,B(_my(_mH)),_mI));}}else{return E(_mF);}}else{return (!B(_kg(_mH,_kJ)))?(!B(_l3(_mH,_kJ)))?E(_mE):E(_mD):E(_mC);}},_mJ=function(_mK){var _mL=E(_mK);return new F(function(){return _mG(_mL.a,_mL.b);});},_mM=function(_mN){return 1/E(_mN);},_mO=function(_mP){var _mQ=E(_mP),_mR=E(_mQ);return (_mR==0)?E(_mF):(_mR<=0)? -_mR:E(_mQ);},_mS=function(_mT){var _mU=E(_mT);if(!_mU._){return _mU.a;}else{return new F(function(){return I_toNumber(_mU.a);});}},_mV=function(_mW){return new F(function(){return _mS(_mW);});},_mX=function(_mY){var _mZ=E(_mY);return (_mZ<=0)?(_mZ>=0)?E(_mZ):E(_6s):E(_6r);},_n0=function(_n1,_n2){return E(_n1)+E(_n2);},_n3=function(_n4,_n5){return E(_n4)*E(_n5);},_n6={_:0,a:_n0,b:_6t,c:_n3,d:_a7,e:_mO,f:_mX,g:_mV},_n7=function(_n8,_n9){return E(_n8)/E(_n9);},_na=new T4(0,_n6,_n7,_mM,_mJ),_nb=function(_nc,_nd){return (E(_nc)!=E(_nd))?true:false;},_ne=function(_nf,_ng){return E(_nf)==E(_ng);},_nh=new T2(0,_ne,_nb),_ni=function(_nj,_nk){return E(_nj)<E(_nk);},_nl=function(_nm,_nn){return E(_nm)<=E(_nn);},_no=function(_np,_nq){return E(_np)>E(_nq);},_nr=function(_ns,_nt){return E(_ns)>=E(_nt);},_nu=function(_nv,_nw){var _nx=E(_nv),_ny=E(_nw);return (_nx>=_ny)?(_nx!=_ny)?2:1:0;},_nz=function(_nA,_nB){var _nC=E(_nA),_nD=E(_nB);return (_nC>_nD)?E(_nC):E(_nD);},_nE=function(_nF,_nG){var _nH=E(_nF),_nI=E(_nG);return (_nH>_nI)?E(_nI):E(_nH);},_nJ={_:0,a:_nh,b:_nu,c:_ni,d:_nl,e:_no,f:_nr,g:_nz,h:_nE},_nK=function(_nL){var _nM=I_decodeDouble(_nL);return new T2(0,new T1(1,_nM.b),_nM.a);},_nN=function(_nO){return new T1(0,_nO);},_nP=function(_nQ){var _nR=hs_intToInt64(2147483647),_nS=hs_leInt64(_nQ,_nR);if(!_nS){return new T1(1,I_fromInt64(_nQ));}else{var _nT=hs_intToInt64(-2147483648),_nU=hs_geInt64(_nQ,_nT);if(!_nU){return new T1(1,I_fromInt64(_nQ));}else{var _nV=hs_int64ToInt(_nQ);return new F(function(){return _nN(_nV);});}}},_nW=new T(function(){var _nX=newByteArr(256),_nY=_nX,_=_nY["v"]["i8"][0]=8,_nZ=function(_o0,_o1,_o2,_){while(1){if(_o2>=256){if(_o0>=256){return E(_);}else{var _o3=imul(2,_o0)|0,_o4=_o1+1|0,_o5=_o0;_o0=_o3;_o1=_o4;_o2=_o5;continue;}}else{var _=_nY["v"]["i8"][_o2]=_o1,_o5=_o2+_o0|0;_o2=_o5;continue;}}},_=B(_nZ(2,0,1,_));return _nY;}),_o6=function(_o7,_o8){var _o9=hs_int64ToInt(_o7),_oa=E(_nW),_ob=_oa["v"]["i8"][(255&_o9>>>0)>>>0&4294967295];if(_o8>_ob){if(_ob>=8){var _oc=hs_uncheckedIShiftRA64(_o7,8),_od=function(_oe,_of){while(1){var _og=B((function(_oh,_oi){var _oj=hs_int64ToInt(_oh),_ok=_oa["v"]["i8"][(255&_oj>>>0)>>>0&4294967295];if(_oi>_ok){if(_ok>=8){var _ol=hs_uncheckedIShiftRA64(_oh,8),_om=_oi-8|0;_oe=_ol;_of=_om;return __continue;}else{return new T2(0,new T(function(){var _on=hs_uncheckedIShiftRA64(_oh,_ok);return B(_nP(_on));}),_oi-_ok|0);}}else{return new T2(0,new T(function(){var _oo=hs_uncheckedIShiftRA64(_oh,_oi);return B(_nP(_oo));}),0);}})(_oe,_of));if(_og!=__continue){return _og;}}};return new F(function(){return _od(_oc,_o8-8|0);});}else{return new T2(0,new T(function(){var _op=hs_uncheckedIShiftRA64(_o7,_ob);return B(_nP(_op));}),_o8-_ob|0);}}else{return new T2(0,new T(function(){var _oq=hs_uncheckedIShiftRA64(_o7,_o8);return B(_nP(_oq));}),0);}},_or=function(_os){var _ot=hs_intToInt64(_os);return E(_ot);},_ou=function(_ov){var _ow=E(_ov);if(!_ow._){return new F(function(){return _or(_ow.a);});}else{return new F(function(){return I_toInt64(_ow.a);});}},_ox=function(_oy){return I_toInt(_oy)>>>0;},_oz=function(_oA){var _oB=E(_oA);if(!_oB._){return _oB.a>>>0;}else{return new F(function(){return _ox(_oB.a);});}},_oC=function(_oD){var _oE=B(_nK(_oD)),_oF=_oE.a,_oG=_oE.b;if(_oG<0){var _oH=function(_oI){if(!_oI){return new T2(0,E(_oF),B(_kK(_jr, -_oG)));}else{var _oJ=B(_o6(B(_ou(_oF)), -_oG));return new T2(0,E(_oJ.a),B(_kK(_jr,_oJ.b)));}};if(!((B(_oz(_oF))&1)>>>0)){return new F(function(){return _oH(1);});}else{return new F(function(){return _oH(0);});}}else{return new T2(0,B(_kK(_oF,_oG)),_jr);}},_oK=function(_oL){var _oM=B(_oC(E(_oL)));return new T2(0,E(_oM.a),E(_oM.b));},_oN=new T3(0,_n6,_nJ,_oK),_oO=function(_oP){return E(E(_oP).a);},_oQ=function(_oR){return E(E(_oR).a);},_oS=new T1(0,1),_oT=function(_oU){return new F(function(){return _41(E(_oU),2147483647);});},_oV=function(_oW,_oX,_oY){if(_oY<=_oX){var _oZ=new T(function(){var _p0=_oX-_oW|0,_p1=function(_p2){return (_p2>=(_oY-_p0|0))?new T2(1,_p2,new T(function(){return B(_p1(_p2+_p0|0));})):new T2(1,_p2,_4);};return B(_p1(_oX));});return new T2(1,_oW,_oZ);}else{return (_oY<=_oW)?new T2(1,_oW,_4):__Z;}},_p3=function(_p4,_p5,_p6){if(_p6>=_p5){var _p7=new T(function(){var _p8=_p5-_p4|0,_p9=function(_pa){return (_pa<=(_p6-_p8|0))?new T2(1,_pa,new T(function(){return B(_p9(_pa+_p8|0));})):new T2(1,_pa,_4);};return B(_p9(_p5));});return new T2(1,_p4,_p7);}else{return (_p6>=_p4)?new T2(1,_p4,_4):__Z;}},_pb=function(_pc,_pd){if(_pd<_pc){return new F(function(){return _oV(_pc,_pd,-2147483648);});}else{return new F(function(){return _p3(_pc,_pd,2147483647);});}},_pe=function(_pf,_pg){return new F(function(){return _pb(E(_pf),E(_pg));});},_ph=function(_pi,_pj,_pk){if(_pj<_pi){return new F(function(){return _oV(_pi,_pj,_pk);});}else{return new F(function(){return _p3(_pi,_pj,_pk);});}},_pl=function(_pm,_pn,_po){return new F(function(){return _ph(E(_pm),E(_pn),E(_po));});},_pp=function(_pq){return E(_pq);},_pr=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_ps=new T(function(){return B(err(_pr));}),_pt=function(_pu){var _pv=E(_pu);return (_pv==(-2147483648))?E(_ps):_pv-1|0;},_pw=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_px=new T(function(){return B(err(_pw));}),_py=function(_pz){var _pA=E(_pz);return (_pA==2147483647)?E(_px):_pA+1|0;},_pB={_:0,a:_py,b:_pt,c:_pp,d:_pp,e:_oT,f:_pe,g:_46,h:_pl},_pC=function(_pD,_pE){if(_pD<=0){if(_pD>=0){return new F(function(){return quot(_pD,_pE);});}else{if(_pE<=0){return new F(function(){return quot(_pD,_pE);});}else{return quot(_pD+1|0,_pE)-1|0;}}}else{if(_pE>=0){if(_pD>=0){return new F(function(){return quot(_pD,_pE);});}else{if(_pE<=0){return new F(function(){return quot(_pD,_pE);});}else{return quot(_pD+1|0,_pE)-1|0;}}}else{return quot(_pD-1|0,_pE)-1|0;}}},_pF=0,_pG=new T(function(){return B(_k8(_pF));}),_pH=new T(function(){return die(_pG);}),_pI=function(_pJ,_pK){var _pL=E(_pK);switch(_pL){case -1:var _pM=E(_pJ);if(_pM==(-2147483648)){return E(_pH);}else{return new F(function(){return _pC(_pM,-1);});}break;case 0:return E(_kb);default:return new F(function(){return _pC(_pJ,_pL);});}},_pN=function(_pO,_pP){return new F(function(){return _pI(E(_pO),E(_pP));});},_pQ=0,_pR=new T2(0,_pH,_pQ),_pS=function(_pT,_pU){var _pV=E(_pT),_pW=E(_pU);switch(_pW){case -1:var _pX=E(_pV);if(_pX==(-2147483648)){return E(_pR);}else{if(_pX<=0){if(_pX>=0){var _pY=quotRemI(_pX,-1);return new T2(0,_pY.a,_pY.b);}else{var _pZ=quotRemI(_pX,-1);return new T2(0,_pZ.a,_pZ.b);}}else{var _q0=quotRemI(_pX-1|0,-1);return new T2(0,_q0.a-1|0,(_q0.b+(-1)|0)+1|0);}}break;case 0:return E(_kb);default:if(_pV<=0){if(_pV>=0){var _q1=quotRemI(_pV,_pW);return new T2(0,_q1.a,_q1.b);}else{if(_pW<=0){var _q2=quotRemI(_pV,_pW);return new T2(0,_q2.a,_q2.b);}else{var _q3=quotRemI(_pV+1|0,_pW);return new T2(0,_q3.a-1|0,(_q3.b+_pW|0)-1|0);}}}else{if(_pW>=0){if(_pV>=0){var _q4=quotRemI(_pV,_pW);return new T2(0,_q4.a,_q4.b);}else{if(_pW<=0){var _q5=quotRemI(_pV,_pW);return new T2(0,_q5.a,_q5.b);}else{var _q6=quotRemI(_pV+1|0,_pW);return new T2(0,_q6.a-1|0,(_q6.b+_pW|0)-1|0);}}}else{var _q7=quotRemI(_pV-1|0,_pW);return new T2(0,_q7.a-1|0,(_q7.b+_pW|0)+1|0);}}}},_q8=function(_q9,_qa){var _qb=E(_qa);switch(_qb){case -1:return E(_pQ);case 0:return E(_kb);default:return new F(function(){return _ap(E(_q9),_qb);});}},_qc=function(_qd,_qe){var _qf=E(_qd),_qg=E(_qe);switch(_qg){case -1:var _qh=E(_qf);if(_qh==(-2147483648)){return E(_pH);}else{return new F(function(){return quot(_qh,-1);});}break;case 0:return E(_kb);default:return new F(function(){return quot(_qf,_qg);});}},_qi=function(_qj,_qk){var _ql=E(_qj),_qm=E(_qk);switch(_qm){case -1:var _qn=E(_ql);if(_qn==(-2147483648)){return E(_pR);}else{var _qo=quotRemI(_qn,-1);return new T2(0,_qo.a,_qo.b);}break;case 0:return E(_kb);default:var _qp=quotRemI(_ql,_qm);return new T2(0,_qp.a,_qp.b);}},_qq=function(_qr,_qs){var _qt=E(_qs);switch(_qt){case -1:return E(_pQ);case 0:return E(_kb);default:return E(_qr)%_qt;}},_qu=function(_qv){return new F(function(){return _nN(E(_qv));});},_qw=function(_qx){return new T2(0,E(B(_nN(E(_qx)))),E(_oS));},_qy=function(_qz,_qA){return imul(E(_qz),E(_qA))|0;},_qB=function(_qC,_qD){return E(_qC)+E(_qD)|0;},_qE=function(_qF){var _qG=E(_qF);return (_qG<0)? -_qG:E(_qG);},_qH=function(_qI){return new F(function(){return _ko(_qI);});},_qJ=function(_qK){return  -E(_qK);},_qL=-1,_qM=0,_qN=1,_qO=function(_qP){var _qQ=E(_qP);return (_qQ>=0)?(E(_qQ)==0)?E(_qM):E(_qN):E(_qL);},_qR={_:0,a:_qB,b:_4h,c:_qy,d:_qJ,e:_qE,f:_qO,g:_qH},_qS=new T3(0,_qR,_4W,_qw),_qT={_:0,a:_qS,b:_pB,c:_qc,d:_qq,e:_pN,f:_q8,g:_qi,h:_pS,i:_qu},_qU=new T1(0,2),_qV=function(_qW,_qX){while(1){var _qY=E(_qW);if(!_qY._){var _qZ=_qY.a,_r0=E(_qX);if(!_r0._){var _r1=_r0.a;if(!(imul(_qZ,_r1)|0)){return new T1(0,imul(_qZ,_r1)|0);}else{_qW=new T1(1,I_fromInt(_qZ));_qX=new T1(1,I_fromInt(_r1));continue;}}else{_qW=new T1(1,I_fromInt(_qZ));_qX=_r0;continue;}}else{var _r2=E(_qX);if(!_r2._){_qW=_qY;_qX=new T1(1,I_fromInt(_r2.a));continue;}else{return new T1(1,I_mul(_qY.a,_r2.a));}}}},_r3=function(_r4,_r5,_r6){while(1){if(!(_r5%2)){var _r7=B(_qV(_r4,_r4)),_r8=quot(_r5,2);_r4=_r7;_r5=_r8;continue;}else{var _r9=E(_r5);if(_r9==1){return new F(function(){return _qV(_r4,_r6);});}else{var _r7=B(_qV(_r4,_r4)),_ra=B(_qV(_r4,_r6));_r4=_r7;_r5=quot(_r9-1|0,2);_r6=_ra;continue;}}}},_rb=function(_rc,_rd){while(1){if(!(_rd%2)){var _re=B(_qV(_rc,_rc)),_rf=quot(_rd,2);_rc=_re;_rd=_rf;continue;}else{var _rg=E(_rd);if(_rg==1){return E(_rc);}else{return new F(function(){return _r3(B(_qV(_rc,_rc)),quot(_rg-1|0,2),_rc);});}}}},_rh=function(_ri){return E(E(_ri).c);},_rj=function(_rk){return E(E(_rk).a);},_rl=function(_rm){return E(E(_rm).b);},_rn=function(_ro){return E(E(_ro).b);},_rp=function(_rq){return E(E(_rq).c);},_rr=function(_rs){return E(E(_rs).a);},_rt=new T1(0,0),_ru=new T1(0,2),_rv=function(_rw){return E(E(_rw).g);},_rx=function(_ry){return E(E(_ry).d);},_rz=function(_rA,_rB){var _rC=B(_oO(_rA)),_rD=new T(function(){return B(_oQ(_rC));}),_rE=new T(function(){return B(A3(_rx,_rA,_rB,new T(function(){return B(A2(_rv,_rD,_ru));})));});return new F(function(){return A3(_rr,B(_rj(B(_rl(_rC)))),_rE,new T(function(){return B(A2(_rv,_rD,_rt));}));});},_rF=new T(function(){return B(unCStr("Negative exponent"));}),_rG=new T(function(){return B(err(_rF));}),_rH=function(_rI){return E(E(_rI).c);},_rJ=function(_rK,_rL,_rM,_rN){var _rO=B(_oO(_rL)),_rP=new T(function(){return B(_oQ(_rO));}),_rQ=B(_rl(_rO));if(!B(A3(_rp,_rQ,_rN,new T(function(){return B(A2(_rv,_rP,_rt));})))){if(!B(A3(_rr,B(_rj(_rQ)),_rN,new T(function(){return B(A2(_rv,_rP,_rt));})))){var _rR=new T(function(){return B(A2(_rv,_rP,_ru));}),_rS=new T(function(){return B(A2(_rv,_rP,_oS));}),_rT=B(_rj(_rQ)),_rU=function(_rV,_rW,_rX){while(1){var _rY=B((function(_rZ,_s0,_s1){if(!B(_rz(_rL,_s0))){if(!B(A3(_rr,_rT,_s0,_rS))){var _s2=new T(function(){return B(A3(_rH,_rL,new T(function(){return B(A3(_rn,_rP,_s0,_rS));}),_rR));});_rV=new T(function(){return B(A3(_rh,_rK,_rZ,_rZ));});_rW=_s2;_rX=new T(function(){return B(A3(_rh,_rK,_rZ,_s1));});return __continue;}else{return new F(function(){return A3(_rh,_rK,_rZ,_s1);});}}else{var _s3=_s1;_rV=new T(function(){return B(A3(_rh,_rK,_rZ,_rZ));});_rW=new T(function(){return B(A3(_rH,_rL,_s0,_rR));});_rX=_s3;return __continue;}})(_rV,_rW,_rX));if(_rY!=__continue){return _rY;}}},_s4=function(_s5,_s6){while(1){var _s7=B((function(_s8,_s9){if(!B(_rz(_rL,_s9))){if(!B(A3(_rr,_rT,_s9,_rS))){var _sa=new T(function(){return B(A3(_rH,_rL,new T(function(){return B(A3(_rn,_rP,_s9,_rS));}),_rR));});return new F(function(){return _rU(new T(function(){return B(A3(_rh,_rK,_s8,_s8));}),_sa,_s8);});}else{return E(_s8);}}else{_s5=new T(function(){return B(A3(_rh,_rK,_s8,_s8));});_s6=new T(function(){return B(A3(_rH,_rL,_s9,_rR));});return __continue;}})(_s5,_s6));if(_s7!=__continue){return _s7;}}};return new F(function(){return _s4(_rM,_rN);});}else{return new F(function(){return A2(_rv,_rK,_oS);});}}else{return E(_rG);}},_sb=new T(function(){return B(err(_rF));}),_sc=function(_sd,_se){var _sf=B(_nK(_se)),_sg=_sf.a,_sh=_sf.b,_si=new T(function(){return B(_oQ(new T(function(){return B(_oO(_sd));})));});if(_sh<0){var _sj= -_sh;if(_sj>=0){var _sk=E(_sj);if(!_sk){var _sl=E(_oS);}else{var _sl=B(_rb(_qU,_sk));}if(!B(_kg(_sl,_kJ))){var _sm=B(_kA(_sg,_sl));return new T2(0,new T(function(){return B(A2(_rv,_si,_sm.a));}),new T(function(){return B(_kc(_sm.b,_sh));}));}else{return E(_kb);}}else{return E(_sb);}}else{var _sn=new T(function(){var _so=new T(function(){return B(_rJ(_si,_qT,new T(function(){return B(A2(_rv,_si,_qU));}),_sh));});return B(A3(_rh,_si,new T(function(){return B(A2(_rv,_si,_sg));}),_so));});return new T2(0,_sn,_mF);}},_sp=function(_sq){return E(E(_sq).a);},_sr=function(_ss,_st){var _su=B(_sc(_ss,E(_st))),_sv=_su.a;if(E(_su.b)<=0){return E(_sv);}else{var _sw=B(_oQ(B(_oO(_ss))));return new F(function(){return A3(_sp,_sw,_sv,new T(function(){return B(A2(_rv,_sw,_jr));}));});}},_sx=function(_sy,_sz){var _sA=B(_sc(_sy,E(_sz))),_sB=_sA.a;if(E(_sA.b)>=0){return E(_sB);}else{var _sC=B(_oQ(B(_oO(_sy))));return new F(function(){return A3(_rn,_sC,_sB,new T(function(){return B(A2(_rv,_sC,_jr));}));});}},_sD=function(_sE,_sF){var _sG=B(_sc(_sE,E(_sF)));return new T2(0,_sG.a,_sG.b);},_sH=function(_sI,_sJ){var _sK=B(_sc(_sI,_sJ)),_sL=_sK.a,_sM=E(_sK.b),_sN=new T(function(){var _sO=B(_oQ(B(_oO(_sI))));if(_sM>=0){return B(A3(_sp,_sO,_sL,new T(function(){return B(A2(_rv,_sO,_jr));})));}else{return B(A3(_rn,_sO,_sL,new T(function(){return B(A2(_rv,_sO,_jr));})));}}),_sP=function(_sQ){var _sR=_sQ-0.5;return (_sR>=0)?(E(_sR)==0)?(!B(_rz(_sI,_sL)))?E(_sN):E(_sL):E(_sN):E(_sL);},_sS=E(_sM);if(!_sS){return new F(function(){return _sP(0);});}else{if(_sS<=0){var _sT= -_sS-0.5;return (_sT>=0)?(E(_sT)==0)?(!B(_rz(_sI,_sL)))?E(_sN):E(_sL):E(_sN):E(_sL);}else{return new F(function(){return _sP(_sS);});}}},_sU=function(_sV,_sW){return new F(function(){return _sH(_sV,E(_sW));});},_sX=function(_sY,_sZ){return E(B(_sc(_sY,E(_sZ))).a);},_t0={_:0,a:_oN,b:_na,c:_sD,d:_sX,e:_sU,f:_sr,g:_sx},_t1=new T1(0,1),_t2=function(_t3,_t4){var _t5=E(_t3);return new T2(0,_t5,new T(function(){var _t6=B(_t2(B(_kr(_t5,_t4)),_t4));return new T2(1,_t6.a,_t6.b);}));},_t7=function(_t8){var _t9=B(_t2(_t8,_t1));return new T2(1,_t9.a,_t9.b);},_ta=function(_tb,_tc){var _td=B(_t2(_tb,new T(function(){return B(_lT(_tc,_tb));})));return new T2(1,_td.a,_td.b);},_te=new T1(0,0),_tf=function(_tg,_th){var _ti=E(_tg);if(!_ti._){var _tj=_ti.a,_tk=E(_th);return (_tk._==0)?_tj>=_tk.a:I_compareInt(_tk.a,_tj)<=0;}else{var _tl=_ti.a,_tm=E(_th);return (_tm._==0)?I_compareInt(_tl,_tm.a)>=0:I_compare(_tl,_tm.a)>=0;}},_tn=function(_to,_tp,_tq){if(!B(_tf(_tp,_te))){var _tr=function(_ts){return (!B(_l3(_ts,_tq)))?new T2(1,_ts,new T(function(){return B(_tr(B(_kr(_ts,_tp))));})):__Z;};return new F(function(){return _tr(_to);});}else{var _tt=function(_tu){return (!B(_kU(_tu,_tq)))?new T2(1,_tu,new T(function(){return B(_tt(B(_kr(_tu,_tp))));})):__Z;};return new F(function(){return _tt(_to);});}},_tv=function(_tw,_tx,_ty){return new F(function(){return _tn(_tw,B(_lT(_tx,_tw)),_ty);});},_tz=function(_tA,_tB){return new F(function(){return _tn(_tA,_t1,_tB);});},_tC=function(_tD){return new F(function(){return _ko(_tD);});},_tE=function(_tF){return new F(function(){return _lT(_tF,_t1);});},_tG=function(_tH){return new F(function(){return _kr(_tH,_t1);});},_tI=function(_tJ){return new F(function(){return _nN(E(_tJ));});},_tK={_:0,a:_tG,b:_tE,c:_tI,d:_tC,e:_t7,f:_ta,g:_tz,h:_tv},_tL=function(_tM,_tN){while(1){var _tO=E(_tM);if(!_tO._){var _tP=E(_tO.a);if(_tP==(-2147483648)){_tM=new T1(1,I_fromInt(-2147483648));continue;}else{var _tQ=E(_tN);if(!_tQ._){return new T1(0,B(_pC(_tP,_tQ.a)));}else{_tM=new T1(1,I_fromInt(_tP));_tN=_tQ;continue;}}}else{var _tR=_tO.a,_tS=E(_tN);return (_tS._==0)?new T1(1,I_div(_tR,I_fromInt(_tS.a))):new T1(1,I_div(_tR,_tS.a));}}},_tT=function(_tU,_tV){if(!B(_kg(_tV,_rt))){return new F(function(){return _tL(_tU,_tV);});}else{return E(_kb);}},_tW=function(_tX,_tY){while(1){var _tZ=E(_tX);if(!_tZ._){var _u0=E(_tZ.a);if(_u0==(-2147483648)){_tX=new T1(1,I_fromInt(-2147483648));continue;}else{var _u1=E(_tY);if(!_u1._){var _u2=_u1.a;return new T2(0,new T1(0,B(_pC(_u0,_u2))),new T1(0,B(_ap(_u0,_u2))));}else{_tX=new T1(1,I_fromInt(_u0));_tY=_u1;continue;}}}else{var _u3=E(_tY);if(!_u3._){_tX=_tZ;_tY=new T1(1,I_fromInt(_u3.a));continue;}else{var _u4=I_divMod(_tZ.a,_u3.a);return new T2(0,new T1(1,_u4.a),new T1(1,_u4.b));}}}},_u5=function(_u6,_u7){if(!B(_kg(_u7,_rt))){var _u8=B(_tW(_u6,_u7));return new T2(0,_u8.a,_u8.b);}else{return E(_kb);}},_u9=function(_ua,_ub){while(1){var _uc=E(_ua);if(!_uc._){var _ud=E(_uc.a);if(_ud==(-2147483648)){_ua=new T1(1,I_fromInt(-2147483648));continue;}else{var _ue=E(_ub);if(!_ue._){return new T1(0,B(_ap(_ud,_ue.a)));}else{_ua=new T1(1,I_fromInt(_ud));_ub=_ue;continue;}}}else{var _uf=_uc.a,_ug=E(_ub);return (_ug._==0)?new T1(1,I_mod(_uf,I_fromInt(_ug.a))):new T1(1,I_mod(_uf,_ug.a));}}},_uh=function(_ui,_uj){if(!B(_kg(_uj,_rt))){return new F(function(){return _u9(_ui,_uj);});}else{return E(_kb);}},_uk=function(_ul,_um){while(1){var _un=E(_ul);if(!_un._){var _uo=E(_un.a);if(_uo==(-2147483648)){_ul=new T1(1,I_fromInt(-2147483648));continue;}else{var _up=E(_um);if(!_up._){return new T1(0,quot(_uo,_up.a));}else{_ul=new T1(1,I_fromInt(_uo));_um=_up;continue;}}}else{var _uq=_un.a,_ur=E(_um);return (_ur._==0)?new T1(0,I_toInt(I_quot(_uq,I_fromInt(_ur.a)))):new T1(1,I_quot(_uq,_ur.a));}}},_us=function(_ut,_uu){if(!B(_kg(_uu,_rt))){return new F(function(){return _uk(_ut,_uu);});}else{return E(_kb);}},_uv=function(_uw,_ux){if(!B(_kg(_ux,_rt))){var _uy=B(_kA(_uw,_ux));return new T2(0,_uy.a,_uy.b);}else{return E(_kb);}},_uz=function(_uA,_uB){while(1){var _uC=E(_uA);if(!_uC._){var _uD=E(_uC.a);if(_uD==(-2147483648)){_uA=new T1(1,I_fromInt(-2147483648));continue;}else{var _uE=E(_uB);if(!_uE._){return new T1(0,_uD%_uE.a);}else{_uA=new T1(1,I_fromInt(_uD));_uB=_uE;continue;}}}else{var _uF=_uC.a,_uG=E(_uB);return (_uG._==0)?new T1(1,I_rem(_uF,I_fromInt(_uG.a))):new T1(1,I_rem(_uF,_uG.a));}}},_uH=function(_uI,_uJ){if(!B(_kg(_uJ,_rt))){return new F(function(){return _uz(_uI,_uJ);});}else{return E(_kb);}},_uK=function(_uL){return E(_uL);},_uM=function(_uN){return E(_uN);},_uO=function(_uP){var _uQ=E(_uP);if(!_uQ._){var _uR=E(_uQ.a);return (_uR==(-2147483648))?E(_mx):(_uR<0)?new T1(0, -_uR):E(_uQ);}else{var _uS=_uQ.a;return (I_compareInt(_uS,0)>=0)?E(_uQ):new T1(1,I_negate(_uS));}},_uT=new T1(0,0),_uU=new T1(0,-1),_uV=function(_uW){var _uX=E(_uW);if(!_uX._){var _uY=_uX.a;return (_uY>=0)?(E(_uY)==0)?E(_uT):E(_l2):E(_uU);}else{var _uZ=I_compareInt(_uX.a,0);return (_uZ<=0)?(E(_uZ)==0)?E(_uT):E(_uU):E(_l2);}},_v0={_:0,a:_kr,b:_lT,c:_qV,d:_my,e:_uO,f:_uV,g:_uM},_v1=function(_v2,_v3){var _v4=E(_v2);if(!_v4._){var _v5=_v4.a,_v6=E(_v3);return (_v6._==0)?_v5!=_v6.a:(I_compareInt(_v6.a,_v5)==0)?false:true;}else{var _v7=_v4.a,_v8=E(_v3);return (_v8._==0)?(I_compareInt(_v7,_v8.a)==0)?false:true:(I_compare(_v7,_v8.a)==0)?false:true;}},_v9=new T2(0,_kg,_v1),_va=function(_vb,_vc){return (!B(_lE(_vb,_vc)))?E(_vb):E(_vc);},_vd=function(_ve,_vf){return (!B(_lE(_ve,_vf)))?E(_vf):E(_ve);},_vg={_:0,a:_v9,b:_js,c:_l3,d:_lE,e:_kU,f:_tf,g:_va,h:_vd},_vh=function(_vi){return new T2(0,E(_vi),E(_oS));},_vj=new T3(0,_v0,_vg,_vh),_vk={_:0,a:_vj,b:_tK,c:_us,d:_uH,e:_tT,f:_uh,g:_uv,h:_u5,i:_uK},_vl=function(_vm){return E(E(_vm).a);},_vn=function(_vo){return E(E(_vo).b);},_vp=function(_vq){return E(E(_vq).b);},_vr=function(_vs){return E(E(_vs).g);},_vt=new T1(0,1),_vu=function(_vv){return E(E(_vv).d);},_vw=function(_vx,_vy,_vz){var _vA=B(_vn(_vx)),_vB=B(_vl(_vA)),_vC=new T(function(){var _vD=new T(function(){var _vE=new T(function(){var _vF=new T(function(){return B(A3(_vr,_vx,_vk,new T(function(){return B(A3(_vp,_vA,_vy,_vz));})));});return B(A2(_rv,_vB,_vF));}),_vG=new T(function(){return B(A2(_vu,_vB,new T(function(){return B(A2(_rv,_vB,_vt));})));});return B(A3(_rh,_vB,_vG,_vE));});return B(A3(_rh,_vB,_vD,_vz));});return new F(function(){return A3(_sp,_vB,_vy,_vC);});},_vH=function(_vI){var _vJ=new T(function(){var _vK=E(E(_vI).b);return new T3(0,new T(function(){return B(_vw(_t0,_vK.a,_1t));}),new T(function(){return B(_vw(_t0,_vK.b,_gF));}),_vK.c);});return new T5(0,new T(function(){return E(E(_vI).a);}),_vJ,new T(function(){return E(E(_vI).c);}),new T(function(){return E(E(_vI).d);}),new T(function(){return E(E(_vI).e);}));},_vL=function(_vM,_){var _vN=B(_5y(_4X,_6g,_i2,_vM)),_vO=B(_hj(E(_vN.a),E(_vN.b),_vN.c,_vN.d,_vN,_)),_vP=new T(function(){return B(_ig(E(_vO).a));}),_vQ=function(_vR){var _vS=E(_vR);return (_vS==1)?E(new T2(1,_vP,_4)):new T2(1,_vP,new T(function(){return B(_vQ(_vS-1|0));}));},_vT=B(_6h(B(_vQ(5)),new T(function(){return E(E(_vO).b);}),_)),_vU=new T(function(){var _vV=new T(function(){return B(_5y(_4X,_6g,_hK,new T(function(){return E(E(_vT).b);})));});return B(_5y(_4X,_6g,_vH,_vV));});return new T2(0,_5,_vU);},_vW=new T(function(){return eval("refresh");}),_vX=function(_vY,_){var _vZ=__app0(E(_vW)),_w0=B(A(_5y,[_4X,_2f,_5X,_vY,_])),_w1=__app0(E(_5O)),_w2=B(_vL(_vY,_));return new T(function(){return E(E(_w2).b);});},_w3=function(_w4,_w5,_w6){var _w7=function(_){var _w8=B(_vX(_w4,_));return new T(function(){return B(A1(_w6,new T1(1,_w8)));});};return new T1(0,_w7);},_w9=new T0(2),_wa=function(_wb,_wc,_wd){return function(_){var _we=E(_wb),_wf=rMV(_we),_wg=E(_wf);if(!_wg._){var _wh=new T(function(){var _wi=new T(function(){return B(A1(_wd,_5));});return B(_0(_wg.b,new T2(1,new T2(0,_wc,function(_wj){return E(_wi);}),_4)));}),_=wMV(_we,new T2(0,_wg.a,_wh));return _w9;}else{var _wk=E(_wg.a);if(!_wk._){var _=wMV(_we,new T2(0,_wc,_4));return new T(function(){return B(A1(_wd,_5));});}else{var _=wMV(_we,new T1(1,_wk.b));return new T1(1,new T2(1,new T(function(){return B(A1(_wd,_5));}),new T2(1,new T(function(){return B(A2(_wk.a,_wc,_19));}),_4)));}}};},_wl=function(_wm){return E(E(_wm).b);},_wn=function(_wo,_wp,_wq){var _wr=new T(function(){return new T1(0,B(_wa(_wp,_wq,_19)));}),_ws=function(_wt){return new T1(1,new T2(1,new T(function(){return B(A1(_wt,_5));}),new T2(1,_wr,_4)));};return new F(function(){return A2(_wl,_wo,_ws);});},_wu=new T1(1,_4),_wv=function(_ww,_wx){return function(_){var _wy=E(_ww),_wz=rMV(_wy),_wA=E(_wz);if(!_wA._){var _wB=_wA.a,_wC=E(_wA.b);if(!_wC._){var _=wMV(_wy,_wu);return new T(function(){return B(A1(_wx,_wB));});}else{var _wD=E(_wC.a),_=wMV(_wy,new T2(0,_wD.a,_wC.b));return new T1(1,new T2(1,new T(function(){return B(A1(_wx,_wB));}),new T2(1,new T(function(){return B(A1(_wD.b,_19));}),_4)));}}else{var _wE=new T(function(){var _wF=function(_wG){var _wH=new T(function(){return B(A1(_wx,_wG));});return function(_wI){return E(_wH);};};return B(_0(_wA.a,new T2(1,_wF,_4)));}),_=wMV(_wy,new T1(1,_wE));return _w9;}};},_wJ=function(_){return new F(function(){return __jsNull();});},_wK=function(_wL){var _wM=B(A1(_wL,_));return E(_wM);},_wN=new T(function(){return B(_wK(_wJ));}),_wO=new T(function(){return E(_wN);}),_wP=new T(function(){return eval("window.requestAnimationFrame");}),_wQ=new T1(1,_4),_wR=function(_wS){var _wT=new T(function(){return B(_wU(_));}),_wV=new T(function(){var _wW=function(_wX){return E(_wT);},_wY=function(_){var _wZ=nMV(_wQ),_x0=_wZ,_x1=new T(function(){return new T1(0,B(_wa(_x0,_5,_19)));}),_x2=function(_){var _x3=__createJSFunc(2,function(_x4,_){var _x5=B(_c(_x1,_4,_));return _wO;}),_x6=__app1(E(_wP),_x3);return new T(function(){return new T1(0,B(_wv(_x0,_wW)));});};return new T1(0,_x2);};return B(A(_wn,[_1i,_wS,_5,function(_x7){return E(new T1(0,_wY));}]));}),_wU=function(_x8){return E(_wV);};return new F(function(){return _wU(_);});},_x9=function(_xa){return E(E(_xa).a);},_xb=function(_xc){return E(E(_xc).d);},_xd=function(_xe){return E(E(_xe).c);},_xf=function(_xg){return E(E(_xg).c);},_xh=new T1(1,_4),_xi=function(_xj){var _xk=function(_){var _xl=nMV(_xh);return new T(function(){return B(A1(_xj,_xl));});};return new T1(0,_xk);},_xm=function(_xn,_xo){var _xp=new T(function(){return B(_xf(_xn));}),_xq=B(_x9(_xn)),_xr=function(_xs){var _xt=new T(function(){return B(A1(_xp,new T(function(){return B(A1(_xo,_xs));})));});return new F(function(){return A3(_xd,_xq,_xt,new T(function(){return B(A2(_xb,_xq,_xs));}));});};return new F(function(){return A3(_10,_xq,new T(function(){return B(A2(_wl,_xn,_xi));}),_xr);});},_xu=function(_xv,_xw){return new T1(0,B(_wv(_xv,_xw)));},_xx=function(_xy,_xz,_xA){var _xB=new T(function(){return B(_x9(_xy));}),_xC=new T(function(){return B(A2(_xb,_xB,_5));}),_xD=function(_xE,_xF){var _xG=new T(function(){var _xH=new T(function(){return B(A2(_wl,_xy,function(_xI){return new F(function(){return _xu(_xF,_xI);});}));});return B(A3(_10,_xB,_xH,new T(function(){return B(A1(_xA,_xE));})));});return new F(function(){return A3(_10,_xB,_xG,function(_xJ){var _xK=E(_xJ);if(!_xK._){return E(_xC);}else{return new F(function(){return _xD(_xK.a,_xF);});}});});};return new F(function(){return _xm(_xy,function(_xI){return new F(function(){return _xD(_xz,_xI);});});});},_xL=new T(function(){return B(A(_xx,[_1i,_1P,_w3,_wR]));}),_xM=function(_){return new F(function(){return _c(_xL,_4,_);});},_xN=function(_){return new F(function(){return _xM(_);});};
var hasteMain = function() {B(A(_xN, [0]));};window.onload = hasteMain;