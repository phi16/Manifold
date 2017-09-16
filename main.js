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

var _0=function(_1,_2,_3){return new F(function(){return A1(_1,function(_4){return new F(function(){return A2(_2,_4,_3);});});});},_5=function(_6,_7,_8){var _9=function(_a){var _b=new T(function(){return B(A1(_8,_a));});return new F(function(){return A1(_7,function(_c){return E(_b);});});};return new F(function(){return A1(_6,_9);});},_d=function(_e,_f,_g){var _h=new T(function(){return B(A1(_f,function(_i){return new F(function(){return A1(_g,_i);});}));});return new F(function(){return A1(_e,function(_j){return E(_h);});});},_k=function(_l,_m,_n){var _o=function(_p){var _q=function(_r){return new F(function(){return A1(_n,new T(function(){return B(A1(_p,_r));}));});};return new F(function(){return A1(_m,_q);});};return new F(function(){return A1(_l,_o);});},_s=function(_t,_u){return new F(function(){return A1(_u,_t);});},_v=function(_w,_x,_y){var _z=new T(function(){return B(A1(_y,_w));});return new F(function(){return A1(_x,function(_A){return E(_z);});});},_B=function(_C,_D,_E){var _F=function(_G){return new F(function(){return A1(_E,new T(function(){return B(A1(_C,_G));}));});};return new F(function(){return A1(_D,_F);});},_H=new T2(0,_B,_v),_I=new T5(0,_H,_s,_k,_d,_5),_J=function(_K){return E(E(_K).b);},_L=function(_M,_N){return new F(function(){return A3(_J,_O,_M,function(_P){return E(_N);});});},_Q=function(_R){return new F(function(){return err(_R);});},_O=new T(function(){return new T5(0,_I,_0,_L,_s,_Q);}),_S=0,_T=__Z,_U=function(_V){return new T0(2);},_W=function(_X){var _Y=new T(function(){return B(A1(_X,_U));}),_Z=function(_10){return new T1(1,new T2(1,new T(function(){return B(A1(_10,_S));}),new T2(1,_Y,_T)));};return E(_Z);},_11=function(_12){return E(_12);},_13=new T3(0,_O,_11,_W),_14=function(_15,_16){var _17=E(_15);return (_17._==0)?E(_16):new T2(1,_17.a,new T(function(){return B(_14(_17.b,_16));}));},_18=function(_19,_){while(1){var _1a=E(_19);if(!_1a._){return _S;}else{var _1b=_1a.b,_1c=E(_1a.a);switch(_1c._){case 0:var _1d=B(A1(_1c.a,_));_19=B(_14(_1b,new T2(1,_1d,_T)));continue;case 1:_19=B(_14(_1b,_1c.a));continue;default:_19=_1b;continue;}}}},_1e=function(_1f,_1g,_){var _1h=E(_1f);switch(_1h._){case 0:var _1i=B(A1(_1h.a,_));return new F(function(){return _18(B(_14(_1g,new T2(1,_1i,_T))),_);});break;case 1:return new F(function(){return _18(B(_14(_1g,_1h.a)),_);});break;default:return new F(function(){return _18(_1g,_);});}},_1j=new T(function(){return eval("compile");}),_1k=function(_1l){return E(E(_1l).b);},_1m=function(_1n){return E(E(_1n).a);},_1o=function(_1p,_1q,_1r){var _1s=E(_1r);if(!_1s._){return new F(function(){return A1(_1q,_1s.a);});}else{var _1t=new T(function(){return B(_1k(_1p));}),_1u=new T(function(){return B(_1m(_1p));}),_1v=function(_1w){var _1x=E(_1w);if(!_1x._){return E(_1u);}else{return new F(function(){return A2(_1t,new T(function(){return B(_1o(_1p,_1q,_1x.a));}),new T(function(){return B(_1v(_1x.b));}));});}};return new F(function(){return _1v(_1s.a);});}},_1y=function(_1z){var _1A=E(_1z);if(!_1A._){return __Z;}else{return new F(function(){return _14(_1A.a,new T(function(){return B(_1y(_1A.b));},1));});}},_1B=function(_1C){return new F(function(){return _1y(_1C);});},_1D=new T3(0,_T,_14,_1B),_1E=new T(function(){return B(unCStr("z"));}),_1F=new T1(0,_1E),_1G=new T(function(){return B(unCStr("y"));}),_1H=new T1(0,_1G),_1I=new T(function(){return B(unCStr("x"));}),_1J=new T1(0,_1I),_1K=new T3(0,_1J,_1H,_1F),_1L=new T1(0,0),_1M=function(_1N){return E(E(_1N).a);},_1O=function(_1P){return E(E(_1P).a);},_1Q=function(_1R){return E(E(_1R).c);},_1S=function(_1T){return E(E(_1T).a);},_1U=function(_1V,_1W,_1X,_1Y,_1Z,_20,_21){var _22=B(_1O(B(_1M(_1V)))),_23=new T(function(){return B(A3(_1S,_22,new T(function(){return B(A3(_1Q,_22,_1W,_1Z));}),new T(function(){return B(A3(_1Q,_22,_1X,_20));})));});return new F(function(){return A3(_1S,_22,_23,new T(function(){return B(A3(_1Q,_22,_1Y,_21));}));});},_24=function(_25){return E(E(_25).b);},_26=function(_27){return E(E(_27).e);},_28=function(_29){return E(E(_29).g);},_2a=function(_2b){return E(E(_2b).d);},_2c=new T1(0,10),_2d=new T1(0,3),_2e=new T2(0,E(_2d),E(_2c)),_2f=new T1(0,5),_2g=new T2(0,E(_2d),E(_2f)),_2h=function(_2i){return E(E(_2i).g);},_2j=function(_2k){return E(E(_2k).h);},_2l=function(_2m){return E(E(_2m).d);},_2n=function(_2o){return E(E(_2o).e);},_2p=function(_2q){var _2r=new T(function(){return E(E(_2q).a);}),_2s=new T(function(){return B(_1M(_2r));}),_2t=new T(function(){return B(_1O(_2s));}),_2u=new T(function(){return B(A2(_28,_2t,_1L));}),_2v=new T(function(){return B(A2(_2l,_2t,new T(function(){return B(A2(_2a,_2s,_2g));})));}),_2w=new T(function(){return E(E(_2q).b);}),_2x=new T(function(){return B(_1S(_2t));}),_2y=new T(function(){return B(_26(_2t));}),_2z=new T(function(){return B(A2(_2a,_2s,_2e));}),_2A=function(_2B){var _2C=new T(function(){var _2D=new T(function(){var _2E=E(_2B),_2F=new T(function(){return B(A2(_2x,new T(function(){return B(A1(_2y,_2E.c));}),_2v));}),_2G=new T(function(){return B(A2(_2x,new T(function(){return B(A1(_2y,_2E.b));}),_2v));}),_2H=new T(function(){return B(A2(_2x,new T(function(){return B(A1(_2y,_2E.a));}),_2v));});return new T3(0,_2H,_2G,_2F);}),_2I=new T(function(){var _2J=new T(function(){var _2K=new T(function(){return B(A3(_2h,_2w,new T(function(){return E(E(_2D).a);}),_2u));}),_2L=new T(function(){return B(A3(_2h,_2w,new T(function(){return E(E(_2D).b);}),_2u));}),_2M=new T(function(){return B(A3(_2h,_2w,new T(function(){return E(E(_2D).c);}),_2u));});return B(_1U(_2r,_2K,_2L,_2M,_2K,_2L,_2M));});return B(A2(_2n,_2r,_2J));}),_2N=new T(function(){var _2O=new T(function(){var _2P=new T(function(){return B(A3(_2h,_2w,new T(function(){return E(E(_2D).a);}),new T(function(){return E(E(_2D).b);})));});return B(A3(_2h,_2w,_2P,new T(function(){return E(E(_2D).c);})));});return B(A3(_2j,_2w,_2u,_2O));});return B(A3(_1S,_2t,_2N,_2I));});return new F(function(){return A3(_24,_2t,_2C,_2z);});};return E(_2A);},_2Q=new T(function(){return B(unCStr(","));}),_2R=new T1(0,_2Q),_2S=new T(function(){return B(unCStr("pow("));}),_2T=new T1(0,_2S),_2U=new T(function(){return B(unCStr(")"));}),_2V=new T1(0,_2U),_2W=new T2(1,_2V,_T),_2X=function(_2Y,_2Z){return new T1(1,new T2(1,_2T,new T2(1,_2Y,new T2(1,_2R,new T2(1,_2Z,_2W)))));},_30=new T(function(){return B(unCStr("acos("));}),_31=new T1(0,_30),_32=function(_33){return new T1(1,new T2(1,_31,new T2(1,_33,_2W)));},_34=new T(function(){return B(unCStr("acosh("));}),_35=new T1(0,_34),_36=function(_37){return new T1(1,new T2(1,_35,new T2(1,_37,_2W)));},_38=new T(function(){return B(unCStr("asin("));}),_39=new T1(0,_38),_3a=function(_3b){return new T1(1,new T2(1,_39,new T2(1,_3b,_2W)));},_3c=new T(function(){return B(unCStr("asinh("));}),_3d=new T1(0,_3c),_3e=function(_3f){return new T1(1,new T2(1,_3d,new T2(1,_3f,_2W)));},_3g=new T(function(){return B(unCStr("atan("));}),_3h=new T1(0,_3g),_3i=function(_3j){return new T1(1,new T2(1,_3h,new T2(1,_3j,_2W)));},_3k=new T(function(){return B(unCStr("atanh("));}),_3l=new T1(0,_3k),_3m=function(_3n){return new T1(1,new T2(1,_3l,new T2(1,_3n,_2W)));},_3o=new T(function(){return B(unCStr("cos("));}),_3p=new T1(0,_3o),_3q=function(_3r){return new T1(1,new T2(1,_3p,new T2(1,_3r,_2W)));},_3s=new T(function(){return B(unCStr("cosh("));}),_3t=new T1(0,_3s),_3u=function(_3v){return new T1(1,new T2(1,_3t,new T2(1,_3v,_2W)));},_3w=new T(function(){return B(unCStr("exp("));}),_3x=new T1(0,_3w),_3y=function(_3z){return new T1(1,new T2(1,_3x,new T2(1,_3z,_2W)));},_3A=new T(function(){return B(unCStr("log("));}),_3B=new T1(0,_3A),_3C=function(_3D){return new T1(1,new T2(1,_3B,new T2(1,_3D,_2W)));},_3E=new T(function(){return B(unCStr(")/log("));}),_3F=new T1(0,_3E),_3G=function(_3H,_3I){return new T1(1,new T2(1,_3B,new T2(1,_3I,new T2(1,_3F,new T2(1,_3H,_2W)))));},_3J=new T(function(){return B(unCStr("pi"));}),_3K=new T1(0,_3J),_3L=new T(function(){return B(unCStr("sin("));}),_3M=new T1(0,_3L),_3N=function(_3O){return new T1(1,new T2(1,_3M,new T2(1,_3O,_2W)));},_3P=new T(function(){return B(unCStr("sinh("));}),_3Q=new T1(0,_3P),_3R=function(_3S){return new T1(1,new T2(1,_3Q,new T2(1,_3S,_2W)));},_3T=new T(function(){return B(unCStr("sqrt("));}),_3U=new T1(0,_3T),_3V=function(_3W){return new T1(1,new T2(1,_3U,new T2(1,_3W,_2W)));},_3X=new T(function(){return B(unCStr("tan("));}),_3Y=new T1(0,_3X),_3Z=function(_40){return new T1(1,new T2(1,_3Y,new T2(1,_40,_2W)));},_41=new T(function(){return B(unCStr("tanh("));}),_42=new T1(0,_41),_43=function(_44){return new T1(1,new T2(1,_42,new T2(1,_44,_2W)));},_45=new T(function(){return B(unCStr("("));}),_46=new T1(0,_45),_47=new T(function(){return B(unCStr(")/("));}),_48=new T1(0,_47),_49=function(_4a,_4b){return new T1(1,new T2(1,_46,new T2(1,_4a,new T2(1,_48,new T2(1,_4b,_2W)))));},_4c=new T1(0,1),_4d=function(_4e,_4f){var _4g=E(_4e);if(!_4g._){var _4h=_4g.a,_4i=E(_4f);if(!_4i._){var _4j=_4i.a;return (_4h!=_4j)?(_4h>_4j)?2:0:1;}else{var _4k=I_compareInt(_4i.a,_4h);return (_4k<=0)?(_4k>=0)?1:2:0;}}else{var _4l=_4g.a,_4m=E(_4f);if(!_4m._){var _4n=I_compareInt(_4l,_4m.a);return (_4n>=0)?(_4n<=0)?1:2:0;}else{var _4o=I_compare(_4l,_4m.a);return (_4o>=0)?(_4o<=0)?1:2:0;}}},_4p=new T(function(){return B(unCStr("base"));}),_4q=new T(function(){return B(unCStr("GHC.Exception"));}),_4r=new T(function(){return B(unCStr("ArithException"));}),_4s=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_4p,_4q,_4r),_4t=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_4s,_T,_T),_4u=function(_4v){return E(_4t);},_4w=function(_4x){return E(E(_4x).a);},_4y=function(_4z,_4A,_4B){var _4C=B(A1(_4z,_)),_4D=B(A1(_4A,_)),_4E=hs_eqWord64(_4C.a,_4D.a);if(!_4E){return __Z;}else{var _4F=hs_eqWord64(_4C.b,_4D.b);return (!_4F)?__Z:new T1(1,_4B);}},_4G=function(_4H){var _4I=E(_4H);return new F(function(){return _4y(B(_4w(_4I.a)),_4u,_4I.b);});},_4J=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_4K=new T(function(){return B(unCStr("denormal"));}),_4L=new T(function(){return B(unCStr("divide by zero"));}),_4M=new T(function(){return B(unCStr("loss of precision"));}),_4N=new T(function(){return B(unCStr("arithmetic underflow"));}),_4O=new T(function(){return B(unCStr("arithmetic overflow"));}),_4P=function(_4Q,_4R){switch(E(_4Q)){case 0:return new F(function(){return _14(_4O,_4R);});break;case 1:return new F(function(){return _14(_4N,_4R);});break;case 2:return new F(function(){return _14(_4M,_4R);});break;case 3:return new F(function(){return _14(_4L,_4R);});break;case 4:return new F(function(){return _14(_4K,_4R);});break;default:return new F(function(){return _14(_4J,_4R);});}},_4S=function(_4T){return new F(function(){return _4P(_4T,_T);});},_4U=function(_4V,_4W,_4X){return new F(function(){return _4P(_4W,_4X);});},_4Y=44,_4Z=93,_50=91,_51=function(_52,_53,_54){var _55=E(_53);if(!_55._){return new F(function(){return unAppCStr("[]",_54);});}else{var _56=new T(function(){var _57=new T(function(){var _58=function(_59){var _5a=E(_59);if(!_5a._){return E(new T2(1,_4Z,_54));}else{var _5b=new T(function(){return B(A2(_52,_5a.a,new T(function(){return B(_58(_5a.b));})));});return new T2(1,_4Y,_5b);}};return B(_58(_55.b));});return B(A2(_52,_55.a,_57));});return new T2(1,_50,_56);}},_5c=function(_5d,_5e){return new F(function(){return _51(_4P,_5d,_5e);});},_5f=new T3(0,_4U,_4S,_5c),_5g=new T(function(){return new T5(0,_4u,_5f,_5h,_4G,_4S);}),_5h=function(_5i){return new T2(0,_5g,_5i);},_5j=3,_5k=new T(function(){return B(_5h(_5j));}),_5l=new T(function(){return die(_5k);}),_5m=function(_5n,_5o){var _5p=E(_5n);return (_5p._==0)?_5p.a*Math.pow(2,_5o):I_toNumber(_5p.a)*Math.pow(2,_5o);},_5q=function(_5r,_5s){var _5t=E(_5r);if(!_5t._){var _5u=_5t.a,_5v=E(_5s);return (_5v._==0)?_5u==_5v.a:(I_compareInt(_5v.a,_5u)==0)?true:false;}else{var _5w=_5t.a,_5x=E(_5s);return (_5x._==0)?(I_compareInt(_5w,_5x.a)==0)?true:false:(I_compare(_5w,_5x.a)==0)?true:false;}},_5y=function(_5z){var _5A=E(_5z);if(!_5A._){return E(_5A.a);}else{return new F(function(){return I_toInt(_5A.a);});}},_5B=function(_5C,_5D){while(1){var _5E=E(_5C);if(!_5E._){var _5F=_5E.a,_5G=E(_5D);if(!_5G._){var _5H=_5G.a,_5I=addC(_5F,_5H);if(!E(_5I.b)){return new T1(0,_5I.a);}else{_5C=new T1(1,I_fromInt(_5F));_5D=new T1(1,I_fromInt(_5H));continue;}}else{_5C=new T1(1,I_fromInt(_5F));_5D=_5G;continue;}}else{var _5J=E(_5D);if(!_5J._){_5C=_5E;_5D=new T1(1,I_fromInt(_5J.a));continue;}else{return new T1(1,I_add(_5E.a,_5J.a));}}}},_5K=function(_5L,_5M){while(1){var _5N=E(_5L);if(!_5N._){var _5O=E(_5N.a);if(_5O==(-2147483648)){_5L=new T1(1,I_fromInt(-2147483648));continue;}else{var _5P=E(_5M);if(!_5P._){var _5Q=_5P.a;return new T2(0,new T1(0,quot(_5O,_5Q)),new T1(0,_5O%_5Q));}else{_5L=new T1(1,I_fromInt(_5O));_5M=_5P;continue;}}}else{var _5R=E(_5M);if(!_5R._){_5L=_5N;_5M=new T1(1,I_fromInt(_5R.a));continue;}else{var _5S=I_quotRem(_5N.a,_5R.a);return new T2(0,new T1(1,_5S.a),new T1(1,_5S.b));}}}},_5T=new T1(0,0),_5U=function(_5V,_5W){while(1){var _5X=E(_5V);if(!_5X._){_5V=new T1(1,I_fromInt(_5X.a));continue;}else{return new T1(1,I_shiftLeft(_5X.a,_5W));}}},_5Y=function(_5Z,_60,_61){if(!B(_5q(_61,_5T))){var _62=B(_5K(_60,_61)),_63=_62.a;switch(B(_4d(B(_5U(_62.b,1)),_61))){case 0:return new F(function(){return _5m(_63,_5Z);});break;case 1:if(!(B(_5y(_63))&1)){return new F(function(){return _5m(_63,_5Z);});}else{return new F(function(){return _5m(B(_5B(_63,_4c)),_5Z);});}break;default:return new F(function(){return _5m(B(_5B(_63,_4c)),_5Z);});}}else{return E(_5l);}},_64=function(_65,_66){var _67=E(_65);if(!_67._){var _68=_67.a,_69=E(_66);return (_69._==0)?_68>_69.a:I_compareInt(_69.a,_68)<0;}else{var _6a=_67.a,_6b=E(_66);return (_6b._==0)?I_compareInt(_6a,_6b.a)>0:I_compare(_6a,_6b.a)>0;}},_6c=new T1(0,1),_6d=function(_6e,_6f){var _6g=E(_6e);if(!_6g._){var _6h=_6g.a,_6i=E(_6f);return (_6i._==0)?_6h<_6i.a:I_compareInt(_6i.a,_6h)>0;}else{var _6j=_6g.a,_6k=E(_6f);return (_6k._==0)?I_compareInt(_6j,_6k.a)<0:I_compare(_6j,_6k.a)<0;}},_6l=new T(function(){return B(unCStr("base"));}),_6m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6n=new T(function(){return B(unCStr("PatternMatchFail"));}),_6o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6l,_6m,_6n),_6p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6o,_T,_T),_6q=function(_6r){return E(_6p);},_6s=function(_6t){var _6u=E(_6t);return new F(function(){return _4y(B(_4w(_6u.a)),_6q,_6u.b);});},_6v=function(_6w){return E(E(_6w).a);},_6x=function(_6y){return new T2(0,_6z,_6y);},_6A=function(_6B,_6C){return new F(function(){return _14(E(_6B).a,_6C);});},_6D=function(_6E,_6F){return new F(function(){return _51(_6A,_6E,_6F);});},_6G=function(_6H,_6I,_6J){return new F(function(){return _14(E(_6I).a,_6J);});},_6K=new T3(0,_6G,_6v,_6D),_6z=new T(function(){return new T5(0,_6q,_6K,_6x,_6s,_6v);}),_6L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6M=function(_6N){return E(E(_6N).c);},_6O=function(_6P,_6Q){return new F(function(){return die(new T(function(){return B(A2(_6M,_6Q,_6P));}));});},_6R=function(_6S,_5i){return new F(function(){return _6O(_6S,_5i);});},_6T=function(_6U,_6V){var _6W=E(_6V);if(!_6W._){return new T2(0,_T,_T);}else{var _6X=_6W.a;if(!B(A1(_6U,_6X))){return new T2(0,_T,_6W);}else{var _6Y=new T(function(){var _6Z=B(_6T(_6U,_6W.b));return new T2(0,_6Z.a,_6Z.b);});return new T2(0,new T2(1,_6X,new T(function(){return E(E(_6Y).a);})),new T(function(){return E(E(_6Y).b);}));}}},_70=32,_71=new T(function(){return B(unCStr("\n"));}),_72=function(_73){return (E(_73)==124)?false:true;},_74=function(_75,_76){var _77=B(_6T(_72,B(unCStr(_75)))),_78=_77.a,_79=function(_7a,_7b){var _7c=new T(function(){var _7d=new T(function(){return B(_14(_76,new T(function(){return B(_14(_7b,_71));},1)));});return B(unAppCStr(": ",_7d));},1);return new F(function(){return _14(_7a,_7c);});},_7e=E(_77.b);if(!_7e._){return new F(function(){return _79(_78,_T);});}else{if(E(_7e.a)==124){return new F(function(){return _79(_78,new T2(1,_70,_7e.b));});}else{return new F(function(){return _79(_78,_T);});}}},_7f=function(_7g){return new F(function(){return _6R(new T1(0,new T(function(){return B(_74(_7g,_6L));})),_6z);});},_7h=function(_7i){var _7j=function(_7k,_7l){while(1){if(!B(_6d(_7k,_7i))){if(!B(_64(_7k,_7i))){if(!B(_5q(_7k,_7i))){return new F(function(){return _7f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_7l);}}else{return _7l-1|0;}}else{var _7m=B(_5U(_7k,1)),_7n=_7l+1|0;_7k=_7m;_7l=_7n;continue;}}};return new F(function(){return _7j(_6c,0);});},_7o=function(_7p){var _7q=E(_7p);if(!_7q._){var _7r=_7q.a>>>0;if(!_7r){return -1;}else{var _7s=function(_7t,_7u){while(1){if(_7t>=_7r){if(_7t<=_7r){if(_7t!=_7r){return new F(function(){return _7f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_7u);}}else{return _7u-1|0;}}else{var _7v=imul(_7t,2)>>>0,_7w=_7u+1|0;_7t=_7v;_7u=_7w;continue;}}};return new F(function(){return _7s(1,0);});}}else{return new F(function(){return _7h(_7q);});}},_7x=function(_7y){var _7z=E(_7y);if(!_7z._){var _7A=_7z.a>>>0;if(!_7A){return new T2(0,-1,0);}else{var _7B=function(_7C,_7D){while(1){if(_7C>=_7A){if(_7C<=_7A){if(_7C!=_7A){return new F(function(){return _7f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_7D);}}else{return _7D-1|0;}}else{var _7E=imul(_7C,2)>>>0,_7F=_7D+1|0;_7C=_7E;_7D=_7F;continue;}}};return new T2(0,B(_7B(1,0)),(_7A&_7A-1>>>0)>>>0&4294967295);}}else{var _7G=_7z.a;return new T2(0,B(_7o(_7z)),I_compareInt(I_and(_7G,I_sub(_7G,I_fromInt(1))),0));}},_7H=function(_7I,_7J){var _7K=E(_7I);if(!_7K._){var _7L=_7K.a,_7M=E(_7J);return (_7M._==0)?_7L<=_7M.a:I_compareInt(_7M.a,_7L)>=0;}else{var _7N=_7K.a,_7O=E(_7J);return (_7O._==0)?I_compareInt(_7N,_7O.a)<=0:I_compare(_7N,_7O.a)<=0;}},_7P=function(_7Q,_7R){while(1){var _7S=E(_7Q);if(!_7S._){var _7T=_7S.a,_7U=E(_7R);if(!_7U._){return new T1(0,(_7T>>>0&_7U.a>>>0)>>>0&4294967295);}else{_7Q=new T1(1,I_fromInt(_7T));_7R=_7U;continue;}}else{var _7V=E(_7R);if(!_7V._){_7Q=_7S;_7R=new T1(1,I_fromInt(_7V.a));continue;}else{return new T1(1,I_and(_7S.a,_7V.a));}}}},_7W=function(_7X,_7Y){while(1){var _7Z=E(_7X);if(!_7Z._){var _80=_7Z.a,_81=E(_7Y);if(!_81._){var _82=_81.a,_83=subC(_80,_82);if(!E(_83.b)){return new T1(0,_83.a);}else{_7X=new T1(1,I_fromInt(_80));_7Y=new T1(1,I_fromInt(_82));continue;}}else{_7X=new T1(1,I_fromInt(_80));_7Y=_81;continue;}}else{var _84=E(_7Y);if(!_84._){_7X=_7Z;_7Y=new T1(1,I_fromInt(_84.a));continue;}else{return new T1(1,I_sub(_7Z.a,_84.a));}}}},_85=new T1(0,2),_86=function(_87,_88){var _89=E(_87);if(!_89._){var _8a=(_89.a>>>0&(2<<_88>>>0)-1>>>0)>>>0,_8b=1<<_88>>>0;return (_8b<=_8a)?(_8b>=_8a)?1:2:0;}else{var _8c=B(_7P(_89,B(_7W(B(_5U(_85,_88)),_6c)))),_8d=B(_5U(_6c,_88));return (!B(_64(_8d,_8c)))?(!B(_6d(_8d,_8c)))?1:2:0;}},_8e=function(_8f,_8g){while(1){var _8h=E(_8f);if(!_8h._){_8f=new T1(1,I_fromInt(_8h.a));continue;}else{return new T1(1,I_shiftRight(_8h.a,_8g));}}},_8i=function(_8j,_8k,_8l,_8m){var _8n=B(_7x(_8m)),_8o=_8n.a;if(!E(_8n.b)){var _8p=B(_7o(_8l));if(_8p<((_8o+_8j|0)-1|0)){var _8q=_8o+(_8j-_8k|0)|0;if(_8q>0){if(_8q>_8p){if(_8q<=(_8p+1|0)){if(!E(B(_7x(_8l)).b)){return 0;}else{return new F(function(){return _5m(_4c,_8j-_8k|0);});}}else{return 0;}}else{var _8r=B(_8e(_8l,_8q));switch(B(_86(_8l,_8q-1|0))){case 0:return new F(function(){return _5m(_8r,_8j-_8k|0);});break;case 1:if(!(B(_5y(_8r))&1)){return new F(function(){return _5m(_8r,_8j-_8k|0);});}else{return new F(function(){return _5m(B(_5B(_8r,_4c)),_8j-_8k|0);});}break;default:return new F(function(){return _5m(B(_5B(_8r,_4c)),_8j-_8k|0);});}}}else{return new F(function(){return _5m(_8l,(_8j-_8k|0)-_8q|0);});}}else{if(_8p>=_8k){var _8s=B(_8e(_8l,(_8p+1|0)-_8k|0));switch(B(_86(_8l,_8p-_8k|0))){case 0:return new F(function(){return _5m(_8s,((_8p-_8o|0)+1|0)-_8k|0);});break;case 2:return new F(function(){return _5m(B(_5B(_8s,_4c)),((_8p-_8o|0)+1|0)-_8k|0);});break;default:if(!(B(_5y(_8s))&1)){return new F(function(){return _5m(_8s,((_8p-_8o|0)+1|0)-_8k|0);});}else{return new F(function(){return _5m(B(_5B(_8s,_4c)),((_8p-_8o|0)+1|0)-_8k|0);});}}}else{return new F(function(){return _5m(_8l, -_8o);});}}}else{var _8t=B(_7o(_8l))-_8o|0,_8u=function(_8v){var _8w=function(_8x,_8y){if(!B(_7H(B(_5U(_8y,_8k)),_8x))){return new F(function(){return _5Y(_8v-_8k|0,_8x,_8y);});}else{return new F(function(){return _5Y((_8v-_8k|0)+1|0,_8x,B(_5U(_8y,1)));});}};if(_8v>=_8k){if(_8v!=_8k){return new F(function(){return _8w(_8l,new T(function(){return B(_5U(_8m,_8v-_8k|0));}));});}else{return new F(function(){return _8w(_8l,_8m);});}}else{return new F(function(){return _8w(new T(function(){return B(_5U(_8l,_8k-_8v|0));}),_8m);});}};if(_8j>_8t){return new F(function(){return _8u(_8j);});}else{return new F(function(){return _8u(_8t);});}}},_8z=new T1(0,2147483647),_8A=new T(function(){return B(_5B(_8z,_6c));}),_8B=function(_8C){var _8D=E(_8C);if(!_8D._){var _8E=E(_8D.a);return (_8E==(-2147483648))?E(_8A):new T1(0, -_8E);}else{return new T1(1,I_negate(_8D.a));}},_8F=new T(function(){return 0/0;}),_8G=new T(function(){return -1/0;}),_8H=new T(function(){return 1/0;}),_8I=0,_8J=function(_8K,_8L){if(!B(_5q(_8L,_5T))){if(!B(_5q(_8K,_5T))){if(!B(_6d(_8K,_5T))){return new F(function(){return _8i(-1021,53,_8K,_8L);});}else{return  -B(_8i(-1021,53,B(_8B(_8K)),_8L));}}else{return E(_8I);}}else{return (!B(_5q(_8K,_5T)))?(!B(_6d(_8K,_5T)))?E(_8H):E(_8G):E(_8F);}},_8M=function(_8N){return new T1(0,new T(function(){var _8O=E(_8N),_8P=jsShow(B(_8J(_8O.a,_8O.b)));return fromJSStr(_8P);}));},_8Q=new T(function(){return B(unCStr("1./("));}),_8R=new T1(0,_8Q),_8S=function(_8T){return new T1(1,new T2(1,_8R,new T2(1,_8T,_2W)));},_8U=new T(function(){return B(unCStr(")+("));}),_8V=new T1(0,_8U),_8W=function(_8X,_8Y){return new T1(1,new T2(1,_46,new T2(1,_8X,new T2(1,_8V,new T2(1,_8Y,_2W)))));},_8Z=new T(function(){return B(unCStr("-("));}),_90=new T1(0,_8Z),_91=function(_92){return new T1(1,new T2(1,_90,new T2(1,_92,_2W)));},_93=new T(function(){return B(unCStr(")*("));}),_94=new T1(0,_93),_95=function(_96,_97){return new T1(1,new T2(1,_46,new T2(1,_96,new T2(1,_94,new T2(1,_97,_2W)))));},_98=function(_99,_9a){return new F(function(){return A3(_1S,_9b,_99,new T(function(){return B(A2(_2l,_9b,_9a));}));});},_9c=new T(function(){return B(unCStr("abs("));}),_9d=new T1(0,_9c),_9e=function(_9f){return new T1(1,new T2(1,_9d,new T2(1,_9f,_2W)));},_9g=function(_9h){while(1){var _9i=E(_9h);if(!_9i._){_9h=new T1(1,I_fromInt(_9i.a));continue;}else{return new F(function(){return I_toString(_9i.a);});}}},_9j=function(_9k,_9l){return new F(function(){return _14(fromJSStr(B(_9g(_9k))),_9l);});},_9m=41,_9n=40,_9o=new T1(0,0),_9p=function(_9q,_9r,_9s){if(_9q<=6){return new F(function(){return _9j(_9r,_9s);});}else{if(!B(_6d(_9r,_9o))){return new F(function(){return _9j(_9r,_9s);});}else{return new T2(1,_9n,new T(function(){return B(_14(fromJSStr(B(_9g(_9r))),new T2(1,_9m,_9s)));}));}}},_9t=new T(function(){return B(unCStr("."));}),_9u=function(_9v){return new T1(0,new T(function(){return B(_14(B(_9p(0,_9v,_T)),_9t));}));},_9w=new T(function(){return B(unCStr("sign("));}),_9x=new T1(0,_9w),_9y=function(_9z){return new T1(1,new T2(1,_9x,new T2(1,_9z,_2W)));},_9b=new T(function(){return {_:0,a:_8W,b:_98,c:_95,d:_91,e:_9e,f:_9y,g:_9u};}),_9A=new T4(0,_9b,_49,_8S,_8M),_9B={_:0,a:_9A,b:_3K,c:_3y,d:_3C,e:_3V,f:_2X,g:_3G,h:_3N,i:_3q,j:_3Z,k:_3a,l:_32,m:_3i,n:_3R,o:_3u,p:_43,q:_3e,r:_36,s:_3m},_9C=new T(function(){return B(unCStr("(/=) is not defined"));}),_9D=new T(function(){return B(err(_9C));}),_9E=new T(function(){return B(unCStr("(==) is not defined"));}),_9F=new T(function(){return B(err(_9E));}),_9G=new T2(0,_9F,_9D),_9H=new T(function(){return B(unCStr("(<) is not defined"));}),_9I=new T(function(){return B(err(_9H));}),_9J=new T(function(){return B(unCStr("(<=) is not defined"));}),_9K=new T(function(){return B(err(_9J));}),_9L=new T(function(){return B(unCStr("(>) is not defined"));}),_9M=new T(function(){return B(err(_9L));}),_9N=new T(function(){return B(unCStr("(>=) is not defined"));}),_9O=new T(function(){return B(err(_9N));}),_9P=new T(function(){return B(unCStr("compare is not defined"));}),_9Q=new T(function(){return B(err(_9P));}),_9R=new T(function(){return B(unCStr("max("));}),_9S=new T1(0,_9R),_9T=function(_9U,_9V){return new T1(1,new T2(1,_9S,new T2(1,_9U,new T2(1,_2R,new T2(1,_9V,_2W)))));},_9W=new T(function(){return B(unCStr("min("));}),_9X=new T1(0,_9W),_9Y=function(_9Z,_a0){return new T1(1,new T2(1,_9X,new T2(1,_9Z,new T2(1,_2R,new T2(1,_a0,_2W)))));},_a1={_:0,a:_9G,b:_9Q,c:_9I,d:_9K,e:_9M,f:_9O,g:_9T,h:_9Y},_a2=new T2(0,_9B,_a1),_a3=new T(function(){return B(_2p(_a2));}),_a4=new T(function(){return B(A1(_a3,_1K));}),_a5=new T(function(){return toJSStr(B(_1o(_1D,_11,_a4)));}),_a6=function(_a7,_a8,_a9){var _aa=new T(function(){return B(_1k(_a7));}),_ab=new T(function(){return B(_1m(_a7));}),_ac=function(_ad){var _ae=E(_ad);if(!_ae._){return E(_ab);}else{return new F(function(){return A2(_aa,new T(function(){return B(_1o(_a7,_a8,_ae.a));}),new T(function(){return B(_ac(_ae.b));}));});}};return new F(function(){return _ac(_a9);});},_af=function(_ag,_ah){var _ai=E(_ag);return E(_ah);},_aj=function(_ak,_al){var _am=E(_ak),_an=E(_al);return new T3(0,new T(function(){return B(A1(_am.a,_an.a));}),new T(function(){return B(A1(_am.b,_an.b));}),new T(function(){return B(A1(_am.c,_an.c));}));},_ao=function(_ap){return new T3(0,_ap,_ap,_ap);},_aq=function(_ar,_as){var _at=E(_as);return new T3(0,_ar,_ar,_ar);},_au=function(_av,_aw){var _ax=E(_aw);return new T3(0,new T(function(){return B(A1(_av,_ax.a));}),new T(function(){return B(A1(_av,_ax.b));}),new T(function(){return B(A1(_av,_ax.c));}));},_ay=new T2(0,_au,_aq),_az=function(_aA,_aB){var _aC=E(_aA),_aD=E(_aB);return new T3(0,_aC.a,_aC.b,_aC.c);},_aE=new T5(0,_ay,_ao,_aj,_af,_az),_aF=new T1(0,1),_aG=function(_aH){return new T3(0,new T3(0,new T(function(){return B(A2(_28,_aH,_aF));}),new T(function(){return B(A2(_28,_aH,_1L));}),new T(function(){return B(A2(_28,_aH,_1L));})),new T3(0,new T(function(){return B(A2(_28,_aH,_1L));}),new T(function(){return B(A2(_28,_aH,_aF));}),new T(function(){return B(A2(_28,_aH,_1L));})),new T3(0,new T(function(){return B(A2(_28,_aH,_1L));}),new T(function(){return B(A2(_28,_aH,_1L));}),new T(function(){return B(A2(_28,_aH,_aF));})));},_aI=function(_aJ){var _aK=B(_aG(_aJ));return new T3(0,_aK.a,_aK.b,_aK.c);},_aL=new T(function(){return B(unCStr("(/=) is not defined"));}),_aM=new T(function(){return B(err(_aL));}),_aN=new T(function(){return B(unCStr("(==) is not defined"));}),_aO=new T(function(){return B(err(_aN));}),_aP=new T2(0,_aO,_aM),_aQ=function(_aR){return E(_aP);},_aS=function(_aT){return E(E(_aT).a);},_aU=function(_aV){return E(E(_aV).f);},_aW=function(_aX){return E(E(_aX).b);},_aY=function(_aZ){return E(E(_aZ).c);},_b0=function(_b1){return E(E(_b1).a);},_b2=function(_b3){return E(E(_b3).d);},_b4=function(_b5,_b6,_b7,_b8,_b9){var _ba=new T(function(){return E(E(E(_b5).c).a);}),_bb=new T(function(){var _bc=E(_b5).a,_bd=new T(function(){var _be=new T(function(){return B(_1M(_ba));}),_bf=new T(function(){return B(_1O(_be));}),_bg=new T(function(){return B(A2(_b2,_ba,_b6));}),_bh=new T(function(){return B(A3(_aU,_ba,_b6,_b8));}),_bi=function(_bj,_bk){var _bl=new T(function(){var _bm=new T(function(){return B(A3(_aW,_be,new T(function(){return B(A3(_1Q,_bf,_b8,_bj));}),_b6));});return B(A3(_1S,_bf,_bm,new T(function(){return B(A3(_1Q,_bf,_bk,_bg));})));});return new F(function(){return A3(_1Q,_bf,_bh,_bl);});};return B(A3(_b0,B(_aS(_bc)),_bi,_b7));});return B(A3(_aY,_bc,_bd,_b9));});return new T2(0,new T(function(){return B(A3(_aU,_ba,_b6,_b8));}),_bb);},_bn=function(_bo,_bp,_bq,_br){var _bs=E(_bq),_bt=E(_br),_bu=B(_b4(_bp,_bs.a,_bs.b,_bt.a,_bt.b));return new T2(0,_bu.a,_bu.b);},_bv=new T1(0,1),_bw=function(_bx){return E(E(_bx).l);},_by=function(_bz,_bA,_bB){var _bC=new T(function(){return E(E(E(_bz).c).a);}),_bD=new T(function(){var _bE=new T(function(){return B(_1M(_bC));}),_bF=new T(function(){var _bG=B(_1O(_bE)),_bH=new T(function(){var _bI=new T(function(){return B(A3(_24,_bG,new T(function(){return B(A2(_28,_bG,_bv));}),new T(function(){return B(A3(_1Q,_bG,_bA,_bA));})));});return B(A2(_2n,_bC,_bI));});return B(A2(_2l,_bG,_bH));});return B(A3(_b0,B(_aS(E(_bz).a)),function(_bJ){return new F(function(){return A3(_aW,_bE,_bJ,_bF);});},_bB));});return new T2(0,new T(function(){return B(A2(_bw,_bC,_bA));}),_bD);},_bK=function(_bL,_bM,_bN){var _bO=E(_bN),_bP=B(_by(_bM,_bO.a,_bO.b));return new T2(0,_bP.a,_bP.b);},_bQ=function(_bR){return E(E(_bR).r);},_bS=function(_bT,_bU,_bV){var _bW=new T(function(){return E(E(E(_bT).c).a);}),_bX=new T(function(){var _bY=new T(function(){return B(_1M(_bW));}),_bZ=new T(function(){var _c0=new T(function(){var _c1=B(_1O(_bY));return B(A3(_24,_c1,new T(function(){return B(A3(_1Q,_c1,_bU,_bU));}),new T(function(){return B(A2(_28,_c1,_bv));})));});return B(A2(_2n,_bW,_c0));});return B(A3(_b0,B(_aS(E(_bT).a)),function(_c2){return new F(function(){return A3(_aW,_bY,_c2,_bZ);});},_bV));});return new T2(0,new T(function(){return B(A2(_bQ,_bW,_bU));}),_bX);},_c3=function(_c4,_c5,_c6){var _c7=E(_c6),_c8=B(_bS(_c5,_c7.a,_c7.b));return new T2(0,_c8.a,_c8.b);},_c9=function(_ca){return E(E(_ca).k);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_1M(_cf));}),_ci=new T(function(){var _cj=new T(function(){var _ck=B(_1O(_ch));return B(A3(_24,_ck,new T(function(){return B(A2(_28,_ck,_bv));}),new T(function(){return B(A3(_1Q,_ck,_cd,_cd));})));});return B(A2(_2n,_cf,_cj));});return B(A3(_b0,B(_aS(E(_cc).a)),function(_cl){return new F(function(){return A3(_aW,_ch,_cl,_ci);});},_ce));});return new T2(0,new T(function(){return B(A2(_c9,_cf,_cd));}),_cg);},_cm=function(_cn,_co,_cp){var _cq=E(_cp),_cr=B(_cb(_co,_cq.a,_cq.b));return new T2(0,_cr.a,_cr.b);},_cs=function(_ct){return E(E(_ct).q);},_cu=function(_cv,_cw,_cx){var _cy=new T(function(){return E(E(E(_cv).c).a);}),_cz=new T(function(){var _cA=new T(function(){return B(_1M(_cy));}),_cB=new T(function(){var _cC=new T(function(){var _cD=B(_1O(_cA));return B(A3(_1S,_cD,new T(function(){return B(A3(_1Q,_cD,_cw,_cw));}),new T(function(){return B(A2(_28,_cD,_bv));})));});return B(A2(_2n,_cy,_cC));});return B(A3(_b0,B(_aS(E(_cv).a)),function(_cE){return new F(function(){return A3(_aW,_cA,_cE,_cB);});},_cx));});return new T2(0,new T(function(){return B(A2(_cs,_cy,_cw));}),_cz);},_cF=function(_cG,_cH,_cI){var _cJ=E(_cI),_cK=B(_cu(_cH,_cJ.a,_cJ.b));return new T2(0,_cK.a,_cK.b);},_cL=function(_cM){return E(E(_cM).m);},_cN=function(_cO,_cP,_cQ){var _cR=new T(function(){return E(E(E(_cO).c).a);}),_cS=new T(function(){var _cT=new T(function(){return B(_1M(_cR));}),_cU=new T(function(){var _cV=B(_1O(_cT));return B(A3(_1S,_cV,new T(function(){return B(A2(_28,_cV,_bv));}),new T(function(){return B(A3(_1Q,_cV,_cP,_cP));})));});return B(A3(_b0,B(_aS(E(_cO).a)),function(_cW){return new F(function(){return A3(_aW,_cT,_cW,_cU);});},_cQ));});return new T2(0,new T(function(){return B(A2(_cL,_cR,_cP));}),_cS);},_cX=function(_cY,_cZ,_d0){var _d1=E(_d0),_d2=B(_cN(_cZ,_d1.a,_d1.b));return new T2(0,_d2.a,_d2.b);},_d3=function(_d4){return E(E(_d4).s);},_d5=function(_d6,_d7,_d8){var _d9=new T(function(){return E(E(E(_d6).c).a);}),_da=new T(function(){var _db=new T(function(){return B(_1M(_d9));}),_dc=new T(function(){var _dd=B(_1O(_db));return B(A3(_24,_dd,new T(function(){return B(A2(_28,_dd,_bv));}),new T(function(){return B(A3(_1Q,_dd,_d7,_d7));})));});return B(A3(_b0,B(_aS(E(_d6).a)),function(_de){return new F(function(){return A3(_aW,_db,_de,_dc);});},_d8));});return new T2(0,new T(function(){return B(A2(_d3,_d9,_d7));}),_da);},_df=function(_dg,_dh,_di){var _dj=E(_di),_dk=B(_d5(_dh,_dj.a,_dj.b));return new T2(0,_dk.a,_dk.b);},_dl=function(_dm){return E(E(_dm).i);},_dn=function(_do){return E(E(_do).h);},_dp=function(_dq,_dr,_ds){var _dt=new T(function(){return E(E(E(_dq).c).a);}),_du=new T(function(){var _dv=new T(function(){return B(_1O(new T(function(){return B(_1M(_dt));})));}),_dw=new T(function(){return B(A2(_2l,_dv,new T(function(){return B(A2(_dn,_dt,_dr));})));});return B(A3(_b0,B(_aS(E(_dq).a)),function(_dx){return new F(function(){return A3(_1Q,_dv,_dx,_dw);});},_ds));});return new T2(0,new T(function(){return B(A2(_dl,_dt,_dr));}),_du);},_dy=function(_dz,_dA,_dB){var _dC=E(_dB),_dD=B(_dp(_dA,_dC.a,_dC.b));return new T2(0,_dD.a,_dD.b);},_dE=function(_dF){return E(E(_dF).o);},_dG=function(_dH){return E(E(_dH).n);},_dI=function(_dJ,_dK,_dL){var _dM=new T(function(){return E(E(E(_dJ).c).a);}),_dN=new T(function(){var _dO=new T(function(){return B(_1O(new T(function(){return B(_1M(_dM));})));}),_dP=new T(function(){return B(A2(_dG,_dM,_dK));});return B(A3(_b0,B(_aS(E(_dJ).a)),function(_dQ){return new F(function(){return A3(_1Q,_dO,_dQ,_dP);});},_dL));});return new T2(0,new T(function(){return B(A2(_dE,_dM,_dK));}),_dN);},_dR=function(_dS,_dT,_dU){var _dV=E(_dU),_dW=B(_dI(_dT,_dV.a,_dV.b));return new T2(0,_dW.a,_dW.b);},_dX=function(_dY){return E(E(_dY).c);},_dZ=function(_e0,_e1,_e2){var _e3=new T(function(){return E(E(E(_e0).c).a);}),_e4=new T(function(){var _e5=new T(function(){return B(_1O(new T(function(){return B(_1M(_e3));})));}),_e6=new T(function(){return B(A2(_dX,_e3,_e1));});return B(A3(_b0,B(_aS(E(_e0).a)),function(_e7){return new F(function(){return A3(_1Q,_e5,_e7,_e6);});},_e2));});return new T2(0,new T(function(){return B(A2(_dX,_e3,_e1));}),_e4);},_e8=function(_e9,_ea,_eb){var _ec=E(_eb),_ed=B(_dZ(_ea,_ec.a,_ec.b));return new T2(0,_ed.a,_ed.b);},_ee=function(_ef,_eg,_eh){var _ei=new T(function(){return E(E(E(_ef).c).a);}),_ej=new T(function(){var _ek=new T(function(){return B(_1M(_ei));}),_el=new T(function(){return B(_1O(_ek));}),_em=new T(function(){return B(A3(_aW,_ek,new T(function(){return B(A2(_28,_el,_bv));}),_eg));});return B(A3(_b0,B(_aS(E(_ef).a)),function(_en){return new F(function(){return A3(_1Q,_el,_en,_em);});},_eh));});return new T2(0,new T(function(){return B(A2(_b2,_ei,_eg));}),_ej);},_eo=function(_ep,_eq,_er){var _es=E(_er),_et=B(_ee(_eq,_es.a,_es.b));return new T2(0,_et.a,_et.b);},_eu=function(_ev,_ew,_ex,_ey){var _ez=new T(function(){return E(E(_ew).c);}),_eA=new T3(0,new T(function(){return E(E(_ew).a);}),new T(function(){return E(E(_ew).b);}),new T2(0,new T(function(){return E(E(_ez).a);}),new T(function(){return E(E(_ez).b);})));return new F(function(){return A3(_aW,_ev,new T(function(){var _eB=E(_ey),_eC=B(_ee(_eA,_eB.a,_eB.b));return new T2(0,_eC.a,_eC.b);}),new T(function(){var _eD=E(_ex),_eE=B(_ee(_eA,_eD.a,_eD.b));return new T2(0,_eE.a,_eE.b);}));});},_eF=new T1(0,0),_eG=function(_eH){return E(E(_eH).b);},_eI=function(_eJ){return E(E(_eJ).b);},_eK=function(_eL){var _eM=new T(function(){return E(E(E(_eL).c).a);}),_eN=new T(function(){return B(A2(_eI,E(_eL).a,new T(function(){return B(A2(_28,B(_1O(B(_1M(_eM)))),_eF));})));});return new T2(0,new T(function(){return B(_eG(_eM));}),_eN);},_eO=function(_eP,_eQ){var _eR=B(_eK(_eQ));return new T2(0,_eR.a,_eR.b);},_eS=function(_eT,_eU,_eV){var _eW=new T(function(){return E(E(E(_eT).c).a);}),_eX=new T(function(){var _eY=new T(function(){return B(_1O(new T(function(){return B(_1M(_eW));})));}),_eZ=new T(function(){return B(A2(_dl,_eW,_eU));});return B(A3(_b0,B(_aS(E(_eT).a)),function(_f0){return new F(function(){return A3(_1Q,_eY,_f0,_eZ);});},_eV));});return new T2(0,new T(function(){return B(A2(_dn,_eW,_eU));}),_eX);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eS(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9,_fa){var _fb=new T(function(){return E(E(E(_f8).c).a);}),_fc=new T(function(){var _fd=new T(function(){return B(_1O(new T(function(){return B(_1M(_fb));})));}),_fe=new T(function(){return B(A2(_dE,_fb,_f9));});return B(A3(_b0,B(_aS(E(_f8).a)),function(_ff){return new F(function(){return A3(_1Q,_fd,_ff,_fe);});},_fa));});return new T2(0,new T(function(){return B(A2(_dG,_fb,_f9));}),_fc);},_fg=function(_fh,_fi,_fj){var _fk=E(_fj),_fl=B(_f7(_fi,_fk.a,_fk.b));return new T2(0,_fl.a,_fl.b);},_fm=new T1(0,2),_fn=function(_fo,_fp,_fq){var _fr=new T(function(){return E(E(E(_fo).c).a);}),_fs=new T(function(){var _ft=new T(function(){return B(_1M(_fr));}),_fu=new T(function(){return B(_1O(_ft));}),_fv=new T(function(){var _fw=new T(function(){return B(A3(_aW,_ft,new T(function(){return B(A2(_28,_fu,_bv));}),new T(function(){return B(A2(_28,_fu,_fm));})));});return B(A3(_aW,_ft,_fw,new T(function(){return B(A2(_2n,_fr,_fp));})));});return B(A3(_b0,B(_aS(E(_fo).a)),function(_fx){return new F(function(){return A3(_1Q,_fu,_fx,_fv);});},_fq));});return new T2(0,new T(function(){return B(A2(_2n,_fr,_fp));}),_fs);},_fy=function(_fz,_fA,_fB){var _fC=E(_fB),_fD=B(_fn(_fA,_fC.a,_fC.b));return new T2(0,_fD.a,_fD.b);},_fE=function(_fF){return E(E(_fF).j);},_fG=function(_fH,_fI,_fJ){var _fK=new T(function(){return E(E(E(_fH).c).a);}),_fL=new T(function(){var _fM=new T(function(){return B(_1M(_fK));}),_fN=new T(function(){var _fO=new T(function(){return B(A2(_dl,_fK,_fI));});return B(A3(_1Q,B(_1O(_fM)),_fO,_fO));});return B(A3(_b0,B(_aS(E(_fH).a)),function(_fP){return new F(function(){return A3(_aW,_fM,_fP,_fN);});},_fJ));});return new T2(0,new T(function(){return B(A2(_fE,_fK,_fI));}),_fL);},_fQ=function(_fR,_fS,_fT){var _fU=E(_fT),_fV=B(_fG(_fS,_fU.a,_fU.b));return new T2(0,_fV.a,_fV.b);},_fW=function(_fX){return E(E(_fX).p);},_fY=function(_fZ,_g0,_g1){var _g2=new T(function(){return E(E(E(_fZ).c).a);}),_g3=new T(function(){var _g4=new T(function(){return B(_1M(_g2));}),_g5=new T(function(){var _g6=new T(function(){return B(A2(_dE,_g2,_g0));});return B(A3(_1Q,B(_1O(_g4)),_g6,_g6));});return B(A3(_b0,B(_aS(E(_fZ).a)),function(_g7){return new F(function(){return A3(_aW,_g4,_g7,_g5);});},_g1));});return new T2(0,new T(function(){return B(A2(_fW,_g2,_g0));}),_g3);},_g8=function(_g9,_ga,_gb){var _gc=E(_gb),_gd=B(_fY(_ga,_gc.a,_gc.b));return new T2(0,_gd.a,_gd.b);},_ge=function(_gf,_gg){return {_:0,a:_gf,b:new T(function(){return B(_eO(_gf,_gg));}),c:function(_gh){return new F(function(){return _e8(_gf,_gg,_gh);});},d:function(_gh){return new F(function(){return _eo(_gf,_gg,_gh);});},e:function(_gh){return new F(function(){return _fy(_gf,_gg,_gh);});},f:function(_gi,_gh){return new F(function(){return _bn(_gf,_gg,_gi,_gh);});},g:function(_gi,_gh){return new F(function(){return _eu(_gf,_gg,_gi,_gh);});},h:function(_gh){return new F(function(){return _f1(_gf,_gg,_gh);});},i:function(_gh){return new F(function(){return _dy(_gf,_gg,_gh);});},j:function(_gh){return new F(function(){return _fQ(_gf,_gg,_gh);});},k:function(_gh){return new F(function(){return _cm(_gf,_gg,_gh);});},l:function(_gh){return new F(function(){return _bK(_gf,_gg,_gh);});},m:function(_gh){return new F(function(){return _cX(_gf,_gg,_gh);});},n:function(_gh){return new F(function(){return _fg(_gf,_gg,_gh);});},o:function(_gh){return new F(function(){return _dR(_gf,_gg,_gh);});},p:function(_gh){return new F(function(){return _g8(_gf,_gg,_gh);});},q:function(_gh){return new F(function(){return _cF(_gf,_gg,_gh);});},r:function(_gh){return new F(function(){return _c3(_gf,_gg,_gh);});},s:function(_gh){return new F(function(){return _df(_gf,_gg,_gh);});}};},_gj=function(_gk,_gl,_gm,_gn,_go){var _gp=new T(function(){return B(_1M(new T(function(){return E(E(E(_gk).c).a);})));}),_gq=new T(function(){var _gr=E(_gk).a,_gs=new T(function(){var _gt=new T(function(){return B(_1O(_gp));}),_gu=new T(function(){return B(A3(_1Q,_gt,_gn,_gn));}),_gv=function(_gw,_gx){var _gy=new T(function(){return B(A3(_24,_gt,new T(function(){return B(A3(_1Q,_gt,_gw,_gn));}),new T(function(){return B(A3(_1Q,_gt,_gl,_gx));})));});return new F(function(){return A3(_aW,_gp,_gy,_gu);});};return B(A3(_b0,B(_aS(_gr)),_gv,_gm));});return B(A3(_aY,_gr,_gs,_go));});return new T2(0,new T(function(){return B(A3(_aW,_gp,_gl,_gn));}),_gq);},_gz=function(_gA,_gB,_gC,_gD){var _gE=E(_gC),_gF=E(_gD),_gG=B(_gj(_gB,_gE.a,_gE.b,_gF.a,_gF.b));return new T2(0,_gG.a,_gG.b);},_gH=function(_gI,_gJ){var _gK=new T(function(){return B(_1M(new T(function(){return E(E(E(_gI).c).a);})));}),_gL=new T(function(){return B(A2(_eI,E(_gI).a,new T(function(){return B(A2(_28,B(_1O(_gK)),_eF));})));});return new T2(0,new T(function(){return B(A2(_2a,_gK,_gJ));}),_gL);},_gM=function(_gN,_gO,_gP){var _gQ=B(_gH(_gO,_gP));return new T2(0,_gQ.a,_gQ.b);},_gR=function(_gS,_gT,_gU){var _gV=new T(function(){return B(_1M(new T(function(){return E(E(E(_gS).c).a);})));}),_gW=new T(function(){return B(_1O(_gV));}),_gX=new T(function(){var _gY=new T(function(){var _gZ=new T(function(){return B(A3(_aW,_gV,new T(function(){return B(A2(_28,_gW,_bv));}),new T(function(){return B(A3(_1Q,_gW,_gT,_gT));})));});return B(A2(_2l,_gW,_gZ));});return B(A3(_b0,B(_aS(E(_gS).a)),function(_h0){return new F(function(){return A3(_1Q,_gW,_h0,_gY);});},_gU));}),_h1=new T(function(){return B(A3(_aW,_gV,new T(function(){return B(A2(_28,_gW,_bv));}),_gT));});return new T2(0,_h1,_gX);},_h2=function(_h3,_h4,_h5){var _h6=E(_h5),_h7=B(_gR(_h4,_h6.a,_h6.b));return new T2(0,_h7.a,_h7.b);},_h8=function(_h9,_ha){return new T4(0,_h9,function(_gi,_gh){return new F(function(){return _gz(_h9,_ha,_gi,_gh);});},function(_gh){return new F(function(){return _h2(_h9,_ha,_gh);});},function(_gh){return new F(function(){return _gM(_h9,_ha,_gh);});});},_hb=function(_hc,_hd,_he,_hf,_hg){var _hh=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_hc).c).a);})));})));}),_hi=new T(function(){var _hj=E(_hc).a,_hk=new T(function(){var _hl=function(_hm,_hn){return new F(function(){return A3(_1S,_hh,new T(function(){return B(A3(_1Q,_hh,_hd,_hn));}),new T(function(){return B(A3(_1Q,_hh,_hm,_hf));}));});};return B(A3(_b0,B(_aS(_hj)),_hl,_he));});return B(A3(_aY,_hj,_hk,_hg));});return new T2(0,new T(function(){return B(A3(_1Q,_hh,_hd,_hf));}),_hi);},_ho=function(_hp,_hq,_hr){var _hs=E(_hq),_ht=E(_hr),_hu=B(_hb(_hp,_hs.a,_hs.b,_ht.a,_ht.b));return new T2(0,_hu.a,_hu.b);},_hv=function(_hw,_hx,_hy,_hz,_hA){var _hB=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_hw).c).a);})));})));}),_hC=new T(function(){var _hD=E(_hw).a,_hE=new T(function(){return B(A3(_b0,B(_aS(_hD)),new T(function(){return B(_1S(_hB));}),_hy));});return B(A3(_aY,_hD,_hE,_hA));});return new T2(0,new T(function(){return B(A3(_1S,_hB,_hx,_hz));}),_hC);},_hF=function(_hG,_hH,_hI){var _hJ=E(_hH),_hK=E(_hI),_hL=B(_hv(_hG,_hJ.a,_hJ.b,_hK.a,_hK.b));return new T2(0,_hL.a,_hL.b);},_hM=function(_hN,_hO,_hP){var _hQ=B(_hR(_hN));return new F(function(){return A3(_1S,_hQ,_hO,new T(function(){return B(A2(_2l,_hQ,_hP));}));});},_hS=function(_hT){return E(E(_hT).f);},_hU=function(_hV,_hW,_hX){var _hY=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_hV).c).a);})));})));}),_hZ=new T(function(){var _i0=new T(function(){return B(A2(_hS,_hY,_hW));});return B(A3(_b0,B(_aS(E(_hV).a)),function(_i1){return new F(function(){return A3(_1Q,_hY,_i1,_i0);});},_hX));});return new T2(0,new T(function(){return B(A2(_26,_hY,_hW));}),_hZ);},_i2=function(_i3,_i4){var _i5=E(_i4),_i6=B(_hU(_i3,_i5.a,_i5.b));return new T2(0,_i6.a,_i6.b);},_i7=function(_i8,_i9){var _ia=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_i8).c).a);})));})));}),_ib=new T(function(){return B(A2(_eI,E(_i8).a,new T(function(){return B(A2(_28,_ia,_eF));})));});return new T2(0,new T(function(){return B(A2(_28,_ia,_i9));}),_ib);},_ic=function(_id,_ie){var _if=B(_i7(_id,_ie));return new T2(0,_if.a,_if.b);},_ig=function(_ih,_ii,_ij){var _ik=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_ih).c).a);})));})));}),_il=new T(function(){return B(A3(_b0,B(_aS(E(_ih).a)),new T(function(){return B(_2l(_ik));}),_ij));});return new T2(0,new T(function(){return B(A2(_2l,_ik,_ii));}),_il);},_im=function(_in,_io){var _ip=E(_io),_iq=B(_ig(_in,_ip.a,_ip.b));return new T2(0,_iq.a,_iq.b);},_ir=function(_is,_it){var _iu=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_is).c).a);})));})));}),_iv=new T(function(){return B(A2(_eI,E(_is).a,new T(function(){return B(A2(_28,_iu,_eF));})));});return new T2(0,new T(function(){return B(A2(_hS,_iu,_it));}),_iv);},_iw=function(_ix,_iy){var _iz=B(_ir(_ix,E(_iy).a));return new T2(0,_iz.a,_iz.b);},_hR=function(_iA){return {_:0,a:function(_gi,_gh){return new F(function(){return _hF(_iA,_gi,_gh);});},b:function(_gi,_gh){return new F(function(){return _hM(_iA,_gi,_gh);});},c:function(_gi,_gh){return new F(function(){return _ho(_iA,_gi,_gh);});},d:function(_gh){return new F(function(){return _im(_iA,_gh);});},e:function(_gh){return new F(function(){return _i2(_iA,_gh);});},f:function(_gh){return new F(function(){return _iw(_iA,_gh);});},g:function(_gh){return new F(function(){return _ic(_iA,_gh);});}};},_iB=new T(function(){return B(unCStr("(>=) is not defined"));}),_iC=new T(function(){return B(err(_iB));}),_iD=new T(function(){return B(unCStr("(>) is not defined"));}),_iE=new T(function(){return B(err(_iD));}),_iF=new T(function(){return B(unCStr("(<=) is not defined"));}),_iG=new T(function(){return B(err(_iF));}),_iH=new T(function(){return B(unCStr("(<) is not defined"));}),_iI=new T(function(){return B(err(_iH));}),_iJ=new T(function(){return B(unCStr("compare is not defined"));}),_iK=new T(function(){return B(err(_iJ));}),_iL=new T2(0,E(_bv),E(_fm)),_iM=function(_iN,_iO,_iP,_iQ){var _iR=new T(function(){return B(A3(_1Q,_iN,new T(function(){return B(A3(_24,_iN,_iP,_iO));}),_iQ));});return new F(function(){return A3(_1S,_iN,_iO,_iR);});},_iS=function(_iT,_iU,_iV,_iW,_iX){var _iY=new T(function(){return E(E(_iT).c);}),_iZ=new T(function(){var _j0=E(_iT).a,_j1=new T(function(){var _j2=new T(function(){return B(_1M(new T(function(){return E(E(_iY).a);})));}),_j3=new T(function(){return B(_1O(_j2));}),_j4=new T(function(){var _j5=new T(function(){var _j6=new T(function(){return B(A2(_hS,_j3,new T(function(){return B(A3(_24,_j3,_iW,_iU));})));});return B(A3(_1Q,_j3,_j6,new T(function(){return B(A2(_2a,_j2,_iL));})));});return B(A3(_1S,_j3,_j5,new T(function(){return B(A2(_2a,_j2,_iL));})));});return B(A3(_b0,B(_aS(_j0)),function(_j7,_j8){return new F(function(){return _iM(_j3,_j7,_j8,_j4);});},_iV));});return B(A3(_aY,_j0,_j1,_iX));});return new T2(0,new T(function(){return B(A3(_2h,E(_iY).b,_iU,_iW));}),_iZ);},_j9=function(_ja,_jb,_jc,_jd){var _je=E(_jc),_jf=E(_jd),_jg=B(_iS(_jb,_je.a,_je.b,_jf.a,_jf.b));return new T2(0,_jg.a,_jg.b);},_jh=function(_ji,_jj,_jk,_jl,_jm){var _jn=new T(function(){return E(E(_ji).c);}),_jo=new T(function(){var _jp=E(_ji).a,_jq=new T(function(){var _jr=new T(function(){return B(_1M(new T(function(){return E(E(_jn).a);})));}),_js=new T(function(){return B(_1O(_jr));}),_jt=new T(function(){var _ju=new T(function(){var _jv=new T(function(){return B(A2(_hS,_js,new T(function(){return B(A3(_24,_js,_jl,_jj));})));});return B(A3(_1Q,_js,_jv,new T(function(){return B(A2(_2a,_jr,_iL));})));});return B(A3(_1S,_js,_ju,new T(function(){return B(A2(_2a,_jr,_iL));})));});return B(A3(_b0,B(_aS(_jp)),function(_jw,_jx){return new F(function(){return _iM(_js,_jx,_jw,_jt);});},_jk));});return B(A3(_aY,_jp,_jq,_jm));});return new T2(0,new T(function(){return B(A3(_2j,E(_jn).b,_jj,_jl));}),_jo);},_jy=function(_jz,_jA,_jB,_jC){var _jD=E(_jB),_jE=E(_jC),_jF=B(_jh(_jA,_jD.a,_jD.b,_jE.a,_jE.b));return new T2(0,_jF.a,_jF.b);},_jG=function(_jH,_jI){return {_:0,a:_jH,b:_iK,c:_iI,d:_iG,e:_iE,f:_iC,g:function(_gi,_gh){return new F(function(){return _j9(_jH,_jI,_gi,_gh);});},h:function(_gi,_gh){return new F(function(){return _jy(_jH,_jI,_gi,_gh);});}};},_jJ=function(_gi,_gh){return new T2(0,_gi,_gh);},_jK=function(_jL,_jM,_jN){var _jO=new T(function(){var _jP=E(_jL),_jQ=_jP.a,_jR=new T(function(){return B(A1(_jP.b,new T(function(){return B(_1O(B(_1M(E(_jP.c).a))));})));});return B(A3(_aY,_jQ,new T(function(){return B(A3(_b0,B(_aS(_jQ)),_jJ,_jN));}),_jR));});return E(B(A1(_jM,_jO)).b);},_jS=function(_jT){var _jU=new T(function(){return E(E(_jT).a);}),_jV=new T(function(){return E(E(_jT).b);}),_jW=new T(function(){var _jX=new T(function(){return B(_jG(new T(function(){return B(_aQ(new T3(0,_aE,_aI,new T2(0,_jU,_jV))));}),new T3(0,_aE,_aI,new T2(0,_jU,_jV))));}),_jY=new T(function(){var _jZ=new T(function(){return B(_h8(new T(function(){return B(_hR(new T3(0,_aE,_aI,new T2(0,_jU,_jV))));}),new T3(0,_aE,_aI,new T2(0,_jU,_jV))));});return B(_ge(_jZ,new T3(0,_aE,_aI,new T2(0,_jU,_jV))));});return B(_2p(new T2(0,_jY,_jX)));});return function(_k0){return new F(function(){return _jK(new T3(0,_aE,_aI,new T2(0,_jU,_jV)),_jW,_k0);});};},_k1=new T(function(){return B(_jS(_a2));}),_k2=function(_k3,_k4){var _k5=E(_k4);return (_k5._==0)?__Z:new T2(1,_k3,new T2(1,_k5.a,new T(function(){return B(_k2(_k3,_k5.b));})));},_k6=new T(function(){var _k7=B(A1(_k1,_1K));return new T2(1,_k7.a,new T(function(){return B(_k2(_2R,new T2(1,_k7.b,new T2(1,_k7.c,_T))));}));}),_k8=new T1(1,_k6),_k9=new T2(1,_k8,_2W),_ka=new T(function(){return B(unCStr("vec3("));}),_kb=new T1(0,_ka),_kc=new T2(1,_kb,_k9),_kd=new T(function(){return toJSStr(B(_a6(_1D,_11,_kc)));}),_ke=function(_kf,_kg){while(1){var _kh=E(_kf);if(!_kh._){return E(_kg);}else{var _ki=_kg+1|0;_kf=_kh.b;_kg=_ki;continue;}}},_kj=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_kk=new T(function(){return B(err(_kj));}),_kl=new T(function(){return B(unCStr("Negative exponent"));}),_km=new T(function(){return B(err(_kl));}),_kn=function(_ko,_kp,_kq){while(1){if(!(_kp%2)){var _kr=_ko*_ko,_ks=quot(_kp,2);_ko=_kr;_kp=_ks;continue;}else{var _kt=E(_kp);if(_kt==1){return _ko*_kq;}else{var _kr=_ko*_ko,_ku=_ko*_kq;_ko=_kr;_kp=quot(_kt-1|0,2);_kq=_ku;continue;}}}},_kv=function(_kw,_kx){while(1){if(!(_kx%2)){var _ky=_kw*_kw,_kz=quot(_kx,2);_kw=_ky;_kx=_kz;continue;}else{var _kA=E(_kx);if(_kA==1){return E(_kw);}else{return new F(function(){return _kn(_kw*_kw,quot(_kA-1|0,2),_kw);});}}}},_kB=function(_kC){var _kD=E(_kC);return new F(function(){return Math.log(_kD+(_kD+1)*Math.sqrt((_kD-1)/(_kD+1)));});},_kE=function(_kF){var _kG=E(_kF);return new F(function(){return Math.log(_kG+Math.sqrt(1+_kG*_kG));});},_kH=function(_kI){var _kJ=E(_kI);return 0.5*Math.log((1+_kJ)/(1-_kJ));},_kK=function(_kL,_kM){return Math.log(E(_kM))/Math.log(E(_kL));},_kN=3.141592653589793,_kO=function(_kP){var _kQ=E(_kP);return new F(function(){return _8J(_kQ.a,_kQ.b);});},_kR=function(_kS){return 1/E(_kS);},_kT=function(_kU){var _kV=E(_kU),_kW=E(_kV);return (_kW==0)?E(_8I):(_kW<=0)? -_kW:E(_kV);},_kX=function(_kY){var _kZ=E(_kY);if(!_kZ._){return _kZ.a;}else{return new F(function(){return I_toNumber(_kZ.a);});}},_l0=function(_l1){return new F(function(){return _kX(_l1);});},_l2=1,_l3=-1,_l4=function(_l5){var _l6=E(_l5);return (_l6<=0)?(_l6>=0)?E(_l6):E(_l3):E(_l2);},_l7=function(_l8,_l9){return E(_l8)-E(_l9);},_la=function(_lb){return  -E(_lb);},_lc=function(_ld,_le){return E(_ld)+E(_le);},_lf=function(_lg,_lh){return E(_lg)*E(_lh);},_li={_:0,a:_lc,b:_l7,c:_lf,d:_la,e:_kT,f:_l4,g:_l0},_lj=function(_lk,_ll){return E(_lk)/E(_ll);},_lm=new T4(0,_li,_lj,_kR,_kO),_ln=function(_lo){return new F(function(){return Math.acos(E(_lo));});},_lp=function(_lq){return new F(function(){return Math.asin(E(_lq));});},_lr=function(_ls){return new F(function(){return Math.atan(E(_ls));});},_lt=function(_lu){return new F(function(){return Math.cos(E(_lu));});},_lv=function(_lw){return new F(function(){return cosh(E(_lw));});},_lx=function(_ly){return new F(function(){return Math.exp(E(_ly));});},_lz=function(_lA){return new F(function(){return Math.log(E(_lA));});},_lB=function(_lC,_lD){return new F(function(){return Math.pow(E(_lC),E(_lD));});},_lE=function(_lF){return new F(function(){return Math.sin(E(_lF));});},_lG=function(_lH){return new F(function(){return sinh(E(_lH));});},_lI=function(_lJ){return new F(function(){return Math.sqrt(E(_lJ));});},_lK=function(_lL){return new F(function(){return Math.tan(E(_lL));});},_lM=function(_lN){return new F(function(){return tanh(E(_lN));});},_lO={_:0,a:_lm,b:_kN,c:_lx,d:_lz,e:_lI,f:_lB,g:_kK,h:_lE,i:_lt,j:_lK,k:_lp,l:_ln,m:_lr,n:_lG,o:_lv,p:_lM,q:_kE,r:_kB,s:_kH},_lP=function(_lQ,_lR){return (E(_lQ)!=E(_lR))?true:false;},_lS=function(_lT,_lU){return E(_lT)==E(_lU);},_lV=new T2(0,_lS,_lP),_lW=function(_lX,_lY){return E(_lX)<E(_lY);},_lZ=function(_m0,_m1){return E(_m0)<=E(_m1);},_m2=function(_m3,_m4){return E(_m3)>E(_m4);},_m5=function(_m6,_m7){return E(_m6)>=E(_m7);},_m8=function(_m9,_ma){var _mb=E(_m9),_mc=E(_ma);return (_mb>=_mc)?(_mb!=_mc)?2:1:0;},_md=function(_me,_mf){var _mg=E(_me),_mh=E(_mf);return (_mg>_mh)?E(_mg):E(_mh);},_mi=function(_mj,_mk){var _ml=E(_mj),_mm=E(_mk);return (_ml>_mm)?E(_mm):E(_ml);},_mn={_:0,a:_lV,b:_m8,c:_lW,d:_lZ,e:_m2,f:_m5,g:_md,h:_mi},_mo=new T2(0,_lO,_mn),_mp=function(_mq,_mr,_ms,_mt){var _mu=new T(function(){return E(E(_mq).a);}),_mv=new T(function(){return B(_1M(_mu));}),_mw=new T(function(){return B(A2(_2n,_mu,new T(function(){return B(_1U(_mu,_mr,_ms,_mt,_mr,_ms,_mt));})));});return new T3(0,new T(function(){return B(A3(_aW,_mv,_mr,_mw));}),new T(function(){return B(A3(_aW,_mv,_ms,_mw));}),new T(function(){return B(A3(_aW,_mv,_mt,_mw));}));},_mx=function(_my,_mz){var _mA=new T(function(){return E(E(_my).a);}),_mB=new T(function(){return E(E(_my).b);}),_mC=new T(function(){return B(A2(_jS,new T2(0,_mA,_mB),_mz));}),_mD=new T(function(){var _mE=E(_mC),_mF=B(_mp(new T2(0,_mA,_mB),_mE.a,_mE.b,_mE.c));return new T3(0,_mF.a,_mF.b,_mF.c);}),_mG=new T(function(){var _mH=E(_mz),_mI=E(_mD),_mJ=new T(function(){return B(_1M(_mA));}),_mK=new T(function(){return B(_1O(_mJ));}),_mL=new T(function(){return B(_1S(_mK));}),_mM=new T(function(){return B(_2l(_mK));}),_mN=new T(function(){return B(_1Q(_mK));}),_mO=new T(function(){var _mP=new T(function(){return B(A2(_2n,_mA,new T(function(){var _mQ=E(_mC),_mR=_mQ.a,_mS=_mQ.b,_mT=_mQ.c;return B(_1U(_mA,_mR,_mS,_mT,_mR,_mS,_mT));})));});return B(A3(_aW,_mJ,new T(function(){return B(A2(_2p,new T2(0,_mA,_mB),_mH));}),_mP));}),_mU=new T(function(){var _mV=new T(function(){return B(A1(_mM,new T(function(){return B(A2(_mN,_mI.c,_mO));})));});return B(A2(_mL,_mH.c,_mV));}),_mW=new T(function(){var _mX=new T(function(){return B(A1(_mM,new T(function(){return B(A2(_mN,_mI.b,_mO));})));});return B(A2(_mL,_mH.b,_mX));}),_mY=new T(function(){var _mZ=new T(function(){return B(A1(_mM,new T(function(){return B(A2(_mN,_mI.a,_mO));})));});return B(A2(_mL,_mH.a,_mZ));});return new T3(0,_mY,_mW,_mU);});return new T2(0,_mG,_mD);},_n0=function(_n1,_n2,_n3,_n4,_n5,_n6,_n7){var _n8=new T(function(){return E(E(_n1).a);}),_n9=new T(function(){return B(_1O(new T(function(){return B(_1M(_n8));})));}),_na=new T(function(){return B(_1S(_n9));}),_nb=new T(function(){return B(_2l(_n9));}),_nc=new T(function(){return B(_1Q(_n9));}),_nd=new T(function(){return B(_1U(_n8,_n5,_n6,_n7,_n2,_n3,_n4));}),_ne=new T(function(){var _nf=new T(function(){return B(A1(_nb,new T(function(){return B(A2(_nc,_n7,_nd));})));});return B(A2(_na,_n4,_nf));}),_ng=new T(function(){var _nh=new T(function(){return B(A1(_nb,new T(function(){return B(A2(_nc,_n6,_nd));})));});return B(A2(_na,_n3,_nh));}),_ni=new T(function(){var _nj=new T(function(){return B(A1(_nb,new T(function(){return B(A2(_nc,_n5,_nd));})));});return B(A2(_na,_n2,_nj));});return new T3(0,_ni,_ng,_ne);},_nk=function(_nl){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_nl));}))));});},_nm=new T(function(){return B(_nk("$dOrd_s3I8 Ord a"));}),_nn=function(_no,_np,_nq,_nr,_ns,_nt,_nu){var _nv=new T(function(){return E(E(_no).a);}),_nw=B(_n0(new T2(0,_nv,_nm),_ns,_nt,_nu,_np,_nq,_nr));return new F(function(){return _mp(new T2(0,_nv,_nm),_nw.a,_nw.b,_nw.c);});},_nx=function(_ny){return E(E(_ny).a);},_nz=function(_nA){return E(E(_nA).a);},_nB=function(_nC,_nD,_nE,_nF){var _nG=new T(function(){var _nH=E(_nF),_nI=E(_nE),_nJ=B(_n0(new T2(0,_nC,_nD),_nH.a,_nH.b,_nH.c,_nI.a,_nI.b,_nI.c));return new T3(0,_nJ.a,_nJ.b,_nJ.c);}),_nK=new T(function(){return B(A2(_2n,_nC,new T(function(){var _nL=E(_nG),_nM=_nL.a,_nN=_nL.b,_nO=_nL.c;return B(_1U(_nC,_nM,_nN,_nO,_nM,_nN,_nO));})));});if(!B(A3(_nz,B(_nx(_nD)),_nK,new T(function(){return B(A2(_28,B(_1O(B(_1M(_nC)))),_1L));})))){var _nP=E(_nG),_nQ=B(_mp(new T2(0,_nC,_nD),_nP.a,_nP.b,_nP.c)),_nR=new T(function(){return B(_1Q(new T(function(){return B(_1O(new T(function(){return B(_1M(_nC));})));})));}),_nS=new T(function(){return B(A2(_2n,_nC,new T(function(){var _nT=E(_nF),_nU=_nT.a,_nV=_nT.b,_nW=_nT.c;return B(_1U(_nC,_nU,_nV,_nW,_nU,_nV,_nW));})));});return new T3(0,new T(function(){return B(A2(_nR,_nQ.a,_nS));}),new T(function(){return B(A2(_nR,_nQ.b,_nS));}),new T(function(){return B(A2(_nR,_nQ.c,_nS));}));}else{var _nX=new T(function(){return B(A2(_28,B(_1O(B(_1M(_nC)))),_1L));});return new T3(0,_nX,_nX,_nX);}},_nY=0,_nZ=new T(function(){var _o0=eval("angleCount"),_o1=Number(_o0);return jsTrunc(_o1);}),_o2=new T(function(){return E(_nZ);}),_o3=new T(function(){return B(unCStr(": empty list"));}),_o4=new T(function(){return B(unCStr("Prelude."));}),_o5=function(_o6){return new F(function(){return err(B(_14(_o4,new T(function(){return B(_14(_o6,_o3));},1))));});},_o7=new T(function(){return B(unCStr("head"));}),_o8=new T(function(){return B(_o5(_o7));}),_o9=function(_oa,_ob,_oc){var _od=E(_oa);if(!_od._){return __Z;}else{var _oe=E(_ob);if(!_oe._){return __Z;}else{var _of=_oe.a,_og=E(_oc);if(!_og._){return __Z;}else{var _oh=E(_og.a),_oi=_oh.a;return new F(function(){return _14(new T2(1,new T3(0,_od.a,_of,_oi),new T2(1,new T3(0,_of,_oi,_oh.b),_T)),new T(function(){return B(_o9(_od.b,_oe.b,_og.b));},1));});}}}},_oj=new T(function(){return B(unCStr("tail"));}),_ok=new T(function(){return B(_o5(_oj));}),_ol=function(_om,_on){var _oo=E(_om);if(!_oo._){return __Z;}else{var _op=E(_on);return (_op._==0)?__Z:new T2(1,new T2(0,_oo.a,_op.a),new T(function(){return B(_ol(_oo.b,_op.b));}));}},_oq=function(_or,_os){var _ot=E(_or);if(!_ot._){return __Z;}else{var _ou=E(_os);if(!_ou._){return __Z;}else{var _ov=E(_ot.a),_ow=_ov.b,_ox=E(_ou.a).b,_oy=new T(function(){var _oz=new T(function(){return B(_ol(_ox,new T(function(){var _oA=E(_ox);if(!_oA._){return E(_ok);}else{return E(_oA.b);}},1)));},1);return B(_o9(_ow,new T(function(){var _oB=E(_ow);if(!_oB._){return E(_ok);}else{return E(_oB.b);}},1),_oz));});return new F(function(){return _14(new T2(1,new T3(0,_ov.a,new T(function(){var _oC=E(_ow);if(!_oC._){return E(_o8);}else{return E(_oC.a);}}),new T(function(){var _oD=E(_ox);if(!_oD._){return E(_o8);}else{return E(_oD.a);}})),_oy),new T(function(){return B(_oq(_ot.b,_ou.b));},1));});}}},_oE=new T(function(){return E(_o2)-1;}),_oF=new T1(0,1),_oG=function(_oH,_oI){var _oJ=E(_oI),_oK=new T(function(){var _oL=B(_1O(_oH)),_oM=B(_oG(_oH,B(A3(_1S,_oL,_oJ,new T(function(){return B(A2(_28,_oL,_oF));})))));return new T2(1,_oM.a,_oM.b);});return new T2(0,_oJ,_oK);},_oN=function(_oO){return E(E(_oO).d);},_oP=new T1(0,2),_oQ=function(_oR,_oS){var _oT=E(_oS);if(!_oT._){return __Z;}else{var _oU=_oT.a;return (!B(A1(_oR,_oU)))?__Z:new T2(1,_oU,new T(function(){return B(_oQ(_oR,_oT.b));}));}},_oV=function(_oW,_oX,_oY,_oZ){var _p0=B(_oG(_oX,_oY)),_p1=new T(function(){var _p2=B(_1O(_oX)),_p3=new T(function(){return B(A3(_aW,_oX,new T(function(){return B(A2(_28,_p2,_oF));}),new T(function(){return B(A2(_28,_p2,_oP));})));});return B(A3(_1S,_p2,_oZ,_p3));});return new F(function(){return _oQ(function(_p4){return new F(function(){return A3(_oN,_oW,_p4,_p1);});},new T2(1,_p0.a,_p0.b));});},_p5=new T(function(){return B(_oV(_mn,_lm,_nY,_oE));}),_p6=function(_p7,_p8){var _p9=E(_p8);return (_p9._==0)?__Z:new T2(1,new T(function(){return B(A1(_p7,_p9.a));}),new T(function(){return B(_p6(_p7,_p9.b));}));},_pa=new T(function(){var _pb=eval("proceedCount"),_pc=Number(_pb);return jsTrunc(_pc);}),_pd=new T(function(){return E(_pa);}),_pe=1,_pf=new T(function(){return B(_oV(_mn,_lm,_pe,_pd));}),_pg=function(_ph,_pi,_pj,_pk,_pl){var _pm=new T(function(){var _pn=E(_pk),_po=_pn.a,_pp=_pn.b,_pq=_pn.c,_pr=E(_pl),_ps=_pr.a,_pt=_pr.b,_pu=_pr.c;return new T3(0,new T(function(){return E(_pp)*E(_pu)-E(_pt)*E(_pq);}),new T(function(){return E(_pq)*E(_ps)-E(_pu)*E(_po);}),new T(function(){return E(_po)*E(_pt)-E(_ps)*E(_pp);}));}),_pv=function(_pw){var _px=new T(function(){var _py=E(_pw)/E(_o2);return (_py+_py)*3.141592653589793;}),_pz=new T(function(){return B(A1(_ph,_px));}),_pA=new T(function(){return E(_px)+E(_pj);}),_pB=new T(function(){var _pC=new T(function(){return E(_pz)/E(_pd);}),_pD=function(_pE,_pF){var _pG=E(_pE);if(!_pG._){return new T2(0,_T,_pF);}else{var _pH=new T(function(){var _pI=new T(function(){var _pJ=E(_pF),_pK=E(_pJ.a),_pL=E(_pJ.b);return new T3(0,new T(function(){return E(_pK.a)+E(_pL.a)*E(_pC);}),new T(function(){return E(_pK.b)+E(_pL.b)*E(_pC);}),new T(function(){return E(_pK.c)+E(_pL.c)*E(_pC);}));}),_pM=B(_mx(_mo,_pI)),_pN=_pM.a;return new T2(0,new T3(0,_pN,new T2(0,new T(function(){return E(_pG.a)/E(_pd);}),_pz),_pA),new T2(0,_pN,new T(function(){var _pO=E(_pM.b),_pP=E(E(_pF).b),_pQ=B(_nn(_mo,_pO.a,_pO.b,_pO.c,_pP.a,_pP.b,_pP.c));return new T3(0,_pQ.a,_pQ.b,_pQ.c);})));}),_pR=new T(function(){var _pS=B(_pD(_pG.b,new T(function(){return E(E(_pH).b);})));return new T2(0,_pS.a,_pS.b);});return new T2(0,new T2(1,new T(function(){return E(E(_pH).a);}),new T(function(){return E(E(_pR).a);})),new T(function(){return E(E(_pR).b);}));}},_pT=function(_pU,_pV,_pW){var _pX=E(_pU);if(!_pX._){return new T2(0,_T,new T2(0,_pV,_pW));}else{var _pY=new T(function(){var _pZ=new T(function(){var _q0=E(_pV),_q1=E(_pW);return new T3(0,new T(function(){return E(_q0.a)+E(_q1.a)*E(_pC);}),new T(function(){return E(_q0.b)+E(_q1.b)*E(_pC);}),new T(function(){return E(_q0.c)+E(_q1.c)*E(_pC);}));}),_q2=B(_mx(_mo,_pZ)),_q3=_q2.a;return new T2(0,new T3(0,_q3,new T2(0,new T(function(){return E(_pX.a)/E(_pd);}),_pz),_pA),new T2(0,_q3,new T(function(){var _q4=E(_q2.b),_q5=E(_pW),_q6=B(_nn(_mo,_q4.a,_q4.b,_q4.c,_q5.a,_q5.b,_q5.c));return new T3(0,_q6.a,_q6.b,_q6.c);})));}),_q7=new T(function(){var _q8=B(_pD(_pX.b,new T(function(){return E(E(_pY).b);})));return new T2(0,_q8.a,_q8.b);});return new T2(0,new T2(1,new T(function(){return E(E(_pY).a);}),new T(function(){return E(E(_q7).a);})),new T(function(){return E(E(_q7).b);}));}},_q9=new T(function(){var _qa=E(_pk),_qb=E(_pm),_qc=new T(function(){return Math.cos(E(_pA));}),_qd=new T(function(){return Math.sin(E(_pA));});return new T3(0,new T(function(){return E(_qa.a)*E(_qc)+E(_qb.a)*E(_qd);}),new T(function(){return E(_qa.b)*E(_qc)+E(_qb.b)*E(_qd);}),new T(function(){return E(_qa.c)*E(_qc)+E(_qb.c)*E(_qd);}));});return E(B(_pT(_pf,_pi,_q9)).a);});return new T2(0,new T3(0,_pi,new T2(0,_nY,_pz),_pA),_pB);},_qe=B(_p6(_pv,_p5)),_qf=new T(function(){var _qg=B(_14(_qe,new T2(1,new T(function(){var _qh=E(_qe);if(!_qh._){return E(_o8);}else{return E(_qh.a);}}),_T)));if(!_qg._){return E(_ok);}else{return E(_qg.b);}},1);return new F(function(){return _oq(_qe,_qf);});},_qi=function(_qj,_qk,_ql,_qm,_qn,_qo){var _qp=new T(function(){var _qq=B(_mx(_mo,new T(function(){return E(E(_qm).a);})));return new T2(0,_qq.a,_qq.b);}),_qr=new T(function(){return new T2(0,new T(function(){return E(E(_qp).a);}),E(_qm).b);}),_qs=new T(function(){return E(E(_qp).b);}),_qt=new T(function(){var _qu=E(_qs),_qv=E(_qo),_qw=B(_nn(_mo,_qu.a,_qu.b,_qu.c,_qv.a,_qv.b,_qv.c));return new T3(0,_qw.a,_qw.b,_qw.c);}),_qx=new T(function(){var _qy=E(_qn);return new T2(0,new T(function(){var _qz=B(_nB(_lO,_mn,_qs,_qy.a));return new T3(0,_qz.a,_qz.b,_qz.c);}),_qy.b);});return {_:0,a:_qj,b:_qk,c:_ql,d:_qr,e:_qx,f:_qt,g:_qs,h:new T(function(){var _qA=E(_qr);return B(_pg(_qj,_qA.a,_qA.b,_qt,_qs));})};},_qB=function(_qC,_qD){if(_qC<=_qD){var _qE=function(_qF){return new T2(1,_qF,new T(function(){if(_qF!=_qD){return B(_qE(_qF+1|0));}else{return __Z;}}));};return new F(function(){return _qE(_qC);});}else{return __Z;}},_qG=-1,_qH=0.5,_qI=new T3(0,_nY,_qH,_qG),_qJ=new T(function(){return 6.283185307179586/E(_o2);}),_qK=function(_qL,_qM,_qN,_qO,_qP){var _qQ=function(_qR){var _qS=E(_qJ),_qT=2+_qR|0,_qU=_qT-1|0,_qV=new T(function(){return B(_qB(0,_qT-1|0));}),_qW=E(_p5);if(!_qW._){return _qS*0;}else{var _qX=_qW.a,_qY=new T(function(){return B(A1(_qL,new T(function(){return 6.283185307179586*E(_qX)/E(_o2);})));}),_qZ=new T(function(){return B(A1(_qL,new T(function(){return 6.283185307179586*(E(_qX)+1)/E(_o2);})));}),_r0=function(_r1,_r2){while(1){var _r3=B((function(_r4,_r5){var _r6=E(_r4);if(!_r6._){return E(_r5);}else{var _r7=_r6.b,_r8=E(_r6.a);if(_r8>=0){var _r9=function(_ra){var _rb=_qU-_r8|0;if(_rb>=0){var _rc=E(_rb);return (_rc==0)?_r5+_ra:_r5+_ra*B(_kv(E(_qZ),_rc));}else{return E(_km);}},_rd=E(_r8);if(!_rd){_r1=_r7;_r2=B(_r9(1));return __continue;}else{var _re=E(_qY),_rf=function(_rg,_rh){while(1){var _ri=B((function(_rj,_rk){var _rl=E(_rj);if(!_rl._){return E(_rk);}else{var _rm=_rl.b,_rn=E(_rl.a);if(_rn>=0){var _ro=function(_rp){var _rq=_qU-_rn|0;if(_rq>=0){var _rr=E(_rq);return (_rr==0)?_rk+_rp:_rk+_rp*B(_kv(E(_qZ),_rr));}else{return E(_km);}},_rs=E(_rn);if(!_rs){_rg=_rm;_rh=B(_ro(1));return __continue;}else{_rg=_rm;_rh=B(_ro(B(_kv(_re,_rs))));return __continue;}}else{return E(_km);}}})(_rg,_rh));if(_ri!=__continue){return _ri;}}};return new F(function(){return _rf(_r7,B(_r9(B(_kv(_re,_rd)))));});}}else{return E(_km);}}})(_r1,_r2));if(_r3!=__continue){return _r3;}}},_rt=(2+_qR)*(1+_qR),_ru=function(_rv,_rw){while(1){var _rx=B((function(_ry,_rz){var _rA=E(_ry);if(!_rA._){return E(_rz);}else{var _rB=_rA.a,_rC=new T(function(){return B(A1(_qL,new T(function(){return 6.283185307179586*E(_rB)/E(_o2);})));}),_rD=new T(function(){return B(A1(_qL,new T(function(){return 6.283185307179586*(E(_rB)+1)/E(_o2);})));}),_rE=function(_rF,_rG){while(1){var _rH=B((function(_rI,_rJ){var _rK=E(_rI);if(!_rK._){return E(_rJ);}else{var _rL=_rK.b,_rM=E(_rK.a);if(_rM>=0){var _rN=function(_rO){var _rP=_qU-_rM|0;if(_rP>=0){var _rQ=E(_rP);return (_rQ==0)?_rJ+_rO:_rJ+_rO*B(_kv(E(_rD),_rQ));}else{return E(_km);}},_rR=E(_rM);if(!_rR){_rF=_rL;_rG=B(_rN(1));return __continue;}else{var _rS=E(_rC),_rT=function(_rU,_rV){while(1){var _rW=B((function(_rX,_rY){var _rZ=E(_rX);if(!_rZ._){return E(_rY);}else{var _s0=_rZ.b,_s1=E(_rZ.a);if(_s1>=0){var _s2=function(_s3){var _s4=_qU-_s1|0;if(_s4>=0){var _s5=E(_s4);return (_s5==0)?_rY+_s3:_rY+_s3*B(_kv(E(_rD),_s5));}else{return E(_km);}},_s6=E(_s1);if(!_s6){_rU=_s0;_rV=B(_s2(1));return __continue;}else{_rU=_s0;_rV=B(_s2(B(_kv(_rS,_s6))));return __continue;}}else{return E(_km);}}})(_rU,_rV));if(_rW!=__continue){return _rW;}}};return new F(function(){return _rT(_rL,B(_rN(B(_kv(_rS,_rR)))));});}}else{return E(_km);}}})(_rF,_rG));if(_rH!=__continue){return _rH;}}},_s7=_rz+B(_rE(_qV,0))/_rt;_rv=_rA.b;_rw=_s7;return __continue;}})(_rv,_rw));if(_rx!=__continue){return _rx;}}};return _qS*B(_ru(_qW.b,B(_r0(_qV,0))/_rt));}},_s8=new T(function(){return 1/(B(_qQ(1))*E(_qM));});return new F(function(){return _qi(_qL,_qI,new T2(0,new T3(0,_s8,_s8,_s8),new T(function(){return 1/(B(_qQ(3))*E(_qM));})),_qN,_qO,_qP);});},_s9=1.2,_sa=-0.2,_sb=1,_sc=0,_sd=new T3(0,_sa,_sc,_sb),_se=new T2(0,_sd,_sc),_sf=0.5,_sg=-0.8,_sh=new T3(0,_sg,_sf,_sc),_si=new T2(0,_sh,_sc),_sj=0.2,_sk=function(_sl){return E(_sj);},_sm=new T3(0,_sc,_sc,_sb),_sn=new T(function(){var _so=B(_qK(_sk,_s9,_si,_se,_sm));return {_:0,a:_so.a,b:_so.b,c:_so.c,d:_so.d,e:_so.e,f:_so.f,g:_so.g,h:_so.h};}),_sp=0,_sq=1.3,_sr=new T3(0,_sq,_sc,_sc),_ss=new T2(0,_sr,_sc),_st=function(_su){var _sv=I_decodeDouble(_su);return new T2(0,new T1(1,_sv.b),_sv.a);},_sw=function(_sx){return new T1(0,_sx);},_sy=function(_sz){var _sA=hs_intToInt64(2147483647),_sB=hs_leInt64(_sz,_sA);if(!_sB){return new T1(1,I_fromInt64(_sz));}else{var _sC=hs_intToInt64(-2147483648),_sD=hs_geInt64(_sz,_sC);if(!_sD){return new T1(1,I_fromInt64(_sz));}else{var _sE=hs_int64ToInt(_sz);return new F(function(){return _sw(_sE);});}}},_sF=new T(function(){var _sG=newByteArr(256),_sH=_sG,_=_sH["v"]["i8"][0]=8,_sI=function(_sJ,_sK,_sL,_){while(1){if(_sL>=256){if(_sJ>=256){return E(_);}else{var _sM=imul(2,_sJ)|0,_sN=_sK+1|0,_sO=_sJ;_sJ=_sM;_sK=_sN;_sL=_sO;continue;}}else{var _=_sH["v"]["i8"][_sL]=_sK,_sO=_sL+_sJ|0;_sL=_sO;continue;}}},_=B(_sI(2,0,1,_));return _sH;}),_sP=function(_sQ,_sR){var _sS=hs_int64ToInt(_sQ),_sT=E(_sF),_sU=_sT["v"]["i8"][(255&_sS>>>0)>>>0&4294967295];if(_sR>_sU){if(_sU>=8){var _sV=hs_uncheckedIShiftRA64(_sQ,8),_sW=function(_sX,_sY){while(1){var _sZ=B((function(_t0,_t1){var _t2=hs_int64ToInt(_t0),_t3=_sT["v"]["i8"][(255&_t2>>>0)>>>0&4294967295];if(_t1>_t3){if(_t3>=8){var _t4=hs_uncheckedIShiftRA64(_t0,8),_t5=_t1-8|0;_sX=_t4;_sY=_t5;return __continue;}else{return new T2(0,new T(function(){var _t6=hs_uncheckedIShiftRA64(_t0,_t3);return B(_sy(_t6));}),_t1-_t3|0);}}else{return new T2(0,new T(function(){var _t7=hs_uncheckedIShiftRA64(_t0,_t1);return B(_sy(_t7));}),0);}})(_sX,_sY));if(_sZ!=__continue){return _sZ;}}};return new F(function(){return _sW(_sV,_sR-8|0);});}else{return new T2(0,new T(function(){var _t8=hs_uncheckedIShiftRA64(_sQ,_sU);return B(_sy(_t8));}),_sR-_sU|0);}}else{return new T2(0,new T(function(){var _t9=hs_uncheckedIShiftRA64(_sQ,_sR);return B(_sy(_t9));}),0);}},_ta=function(_tb){var _tc=hs_intToInt64(_tb);return E(_tc);},_td=function(_te){var _tf=E(_te);if(!_tf._){return new F(function(){return _ta(_tf.a);});}else{return new F(function(){return I_toInt64(_tf.a);});}},_tg=function(_th){return I_toInt(_th)>>>0;},_ti=function(_tj){var _tk=E(_tj);if(!_tk._){return _tk.a>>>0;}else{return new F(function(){return _tg(_tk.a);});}},_tl=function(_tm){var _tn=B(_st(_tm)),_to=_tn.a,_tp=_tn.b;if(_tp<0){var _tq=function(_tr){if(!_tr){return new T2(0,E(_to),B(_5U(_4c, -_tp)));}else{var _ts=B(_sP(B(_td(_to)), -_tp));return new T2(0,E(_ts.a),B(_5U(_4c,_ts.b)));}};if(!((B(_ti(_to))&1)>>>0)){return new F(function(){return _tq(1);});}else{return new F(function(){return _tq(0);});}}else{return new T2(0,B(_5U(_to,_tp)),_4c);}},_tt=function(_tu){var _tv=B(_tl(E(_tu)));return new T2(0,E(_tv.a),E(_tv.b));},_tw=new T3(0,_li,_mn,_tt),_tx=function(_ty){return E(E(_ty).a);},_tz=function(_tA){return E(E(_tA).a);},_tB=function(_tC){return new F(function(){return _qB(E(_tC),2147483647);});},_tD=function(_tE,_tF,_tG){if(_tG<=_tF){var _tH=new T(function(){var _tI=_tF-_tE|0,_tJ=function(_tK){return (_tK>=(_tG-_tI|0))?new T2(1,_tK,new T(function(){return B(_tJ(_tK+_tI|0));})):new T2(1,_tK,_T);};return B(_tJ(_tF));});return new T2(1,_tE,_tH);}else{return (_tG<=_tE)?new T2(1,_tE,_T):__Z;}},_tL=function(_tM,_tN,_tO){if(_tO>=_tN){var _tP=new T(function(){var _tQ=_tN-_tM|0,_tR=function(_tS){return (_tS<=(_tO-_tQ|0))?new T2(1,_tS,new T(function(){return B(_tR(_tS+_tQ|0));})):new T2(1,_tS,_T);};return B(_tR(_tN));});return new T2(1,_tM,_tP);}else{return (_tO>=_tM)?new T2(1,_tM,_T):__Z;}},_tT=function(_tU,_tV){if(_tV<_tU){return new F(function(){return _tD(_tU,_tV,-2147483648);});}else{return new F(function(){return _tL(_tU,_tV,2147483647);});}},_tW=function(_tX,_tY){return new F(function(){return _tT(E(_tX),E(_tY));});},_tZ=function(_u0,_u1,_u2){if(_u1<_u0){return new F(function(){return _tD(_u0,_u1,_u2);});}else{return new F(function(){return _tL(_u0,_u1,_u2);});}},_u3=function(_u4,_u5,_u6){return new F(function(){return _tZ(E(_u4),E(_u5),E(_u6));});},_u7=function(_u8,_u9){return new F(function(){return _qB(E(_u8),E(_u9));});},_ua=function(_ub){return E(_ub);},_uc=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_ud=new T(function(){return B(err(_uc));}),_ue=function(_uf){var _ug=E(_uf);return (_ug==(-2147483648))?E(_ud):_ug-1|0;},_uh=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_ui=new T(function(){return B(err(_uh));}),_uj=function(_uk){var _ul=E(_uk);return (_ul==2147483647)?E(_ui):_ul+1|0;},_um={_:0,a:_uj,b:_ue,c:_ua,d:_ua,e:_tB,f:_tW,g:_u7,h:_u3},_un=function(_uo,_up){if(_uo<=0){if(_uo>=0){return new F(function(){return quot(_uo,_up);});}else{if(_up<=0){return new F(function(){return quot(_uo,_up);});}else{return quot(_uo+1|0,_up)-1|0;}}}else{if(_up>=0){if(_uo>=0){return new F(function(){return quot(_uo,_up);});}else{if(_up<=0){return new F(function(){return quot(_uo,_up);});}else{return quot(_uo+1|0,_up)-1|0;}}}else{return quot(_uo-1|0,_up)-1|0;}}},_uq=0,_ur=new T(function(){return B(_5h(_uq));}),_us=new T(function(){return die(_ur);}),_ut=function(_uu,_uv){var _uw=E(_uv);switch(_uw){case -1:var _ux=E(_uu);if(_ux==(-2147483648)){return E(_us);}else{return new F(function(){return _un(_ux,-1);});}break;case 0:return E(_5l);default:return new F(function(){return _un(_uu,_uw);});}},_uy=function(_uz,_uA){return new F(function(){return _ut(E(_uz),E(_uA));});},_uB=0,_uC=new T2(0,_us,_uB),_uD=function(_uE,_uF){var _uG=E(_uE),_uH=E(_uF);switch(_uH){case -1:var _uI=E(_uG);if(_uI==(-2147483648)){return E(_uC);}else{if(_uI<=0){if(_uI>=0){var _uJ=quotRemI(_uI,-1);return new T2(0,_uJ.a,_uJ.b);}else{var _uK=quotRemI(_uI,-1);return new T2(0,_uK.a,_uK.b);}}else{var _uL=quotRemI(_uI-1|0,-1);return new T2(0,_uL.a-1|0,(_uL.b+(-1)|0)+1|0);}}break;case 0:return E(_5l);default:if(_uG<=0){if(_uG>=0){var _uM=quotRemI(_uG,_uH);return new T2(0,_uM.a,_uM.b);}else{if(_uH<=0){var _uN=quotRemI(_uG,_uH);return new T2(0,_uN.a,_uN.b);}else{var _uO=quotRemI(_uG+1|0,_uH);return new T2(0,_uO.a-1|0,(_uO.b+_uH|0)-1|0);}}}else{if(_uH>=0){if(_uG>=0){var _uP=quotRemI(_uG,_uH);return new T2(0,_uP.a,_uP.b);}else{if(_uH<=0){var _uQ=quotRemI(_uG,_uH);return new T2(0,_uQ.a,_uQ.b);}else{var _uR=quotRemI(_uG+1|0,_uH);return new T2(0,_uR.a-1|0,(_uR.b+_uH|0)-1|0);}}}else{var _uS=quotRemI(_uG-1|0,_uH);return new T2(0,_uS.a-1|0,(_uS.b+_uH|0)+1|0);}}}},_uT=function(_uU,_uV){var _uW=_uU%_uV;if(_uU<=0){if(_uU>=0){return E(_uW);}else{if(_uV<=0){return E(_uW);}else{var _uX=E(_uW);return (_uX==0)?0:_uX+_uV|0;}}}else{if(_uV>=0){if(_uU>=0){return E(_uW);}else{if(_uV<=0){return E(_uW);}else{var _uY=E(_uW);return (_uY==0)?0:_uY+_uV|0;}}}else{var _uZ=E(_uW);return (_uZ==0)?0:_uZ+_uV|0;}}},_v0=function(_v1,_v2){var _v3=E(_v2);switch(_v3){case -1:return E(_uB);case 0:return E(_5l);default:return new F(function(){return _uT(E(_v1),_v3);});}},_v4=function(_v5,_v6){var _v7=E(_v5),_v8=E(_v6);switch(_v8){case -1:var _v9=E(_v7);if(_v9==(-2147483648)){return E(_us);}else{return new F(function(){return quot(_v9,-1);});}break;case 0:return E(_5l);default:return new F(function(){return quot(_v7,_v8);});}},_va=function(_vb,_vc){var _vd=E(_vb),_ve=E(_vc);switch(_ve){case -1:var _vf=E(_vd);if(_vf==(-2147483648)){return E(_uC);}else{var _vg=quotRemI(_vf,-1);return new T2(0,_vg.a,_vg.b);}break;case 0:return E(_5l);default:var _vh=quotRemI(_vd,_ve);return new T2(0,_vh.a,_vh.b);}},_vi=function(_vj,_vk){var _vl=E(_vk);switch(_vl){case -1:return E(_uB);case 0:return E(_5l);default:return E(_vj)%_vl;}},_vm=function(_vn){return new F(function(){return _sw(E(_vn));});},_vo=function(_vp){return new T2(0,E(B(_sw(E(_vp)))),E(_oF));},_vq=function(_vr,_vs){return imul(E(_vr),E(_vs))|0;},_vt=function(_vu,_vv){return E(_vu)+E(_vv)|0;},_vw=function(_vx,_vy){return E(_vx)-E(_vy)|0;},_vz=function(_vA){var _vB=E(_vA);return (_vB<0)? -_vB:E(_vB);},_vC=function(_vD){return new F(function(){return _5y(_vD);});},_vE=function(_vF){return  -E(_vF);},_vG=-1,_vH=0,_vI=1,_vJ=function(_vK){var _vL=E(_vK);return (_vL>=0)?(E(_vL)==0)?E(_vH):E(_vI):E(_vG);},_vM={_:0,a:_vt,b:_vw,c:_vq,d:_vE,e:_vz,f:_vJ,g:_vC},_vN=function(_vO,_vP){return E(_vO)==E(_vP);},_vQ=function(_vR,_vS){return E(_vR)!=E(_vS);},_vT=new T2(0,_vN,_vQ),_vU=function(_vV,_vW){var _vX=E(_vV),_vY=E(_vW);return (_vX>_vY)?E(_vX):E(_vY);},_vZ=function(_w0,_w1){var _w2=E(_w0),_w3=E(_w1);return (_w2>_w3)?E(_w3):E(_w2);},_w4=function(_w5,_w6){return (_w5>=_w6)?(_w5!=_w6)?2:1:0;},_w7=function(_w8,_w9){return new F(function(){return _w4(E(_w8),E(_w9));});},_wa=function(_wb,_wc){return E(_wb)>=E(_wc);},_wd=function(_we,_wf){return E(_we)>E(_wf);},_wg=function(_wh,_wi){return E(_wh)<=E(_wi);},_wj=function(_wk,_wl){return E(_wk)<E(_wl);},_wm={_:0,a:_vT,b:_w7,c:_wj,d:_wg,e:_wd,f:_wa,g:_vU,h:_vZ},_wn=new T3(0,_vM,_wm,_vo),_wo={_:0,a:_wn,b:_um,c:_v4,d:_vi,e:_uy,f:_v0,g:_va,h:_uD,i:_vm},_wp=new T1(0,2),_wq=function(_wr,_ws){while(1){var _wt=E(_wr);if(!_wt._){var _wu=_wt.a,_wv=E(_ws);if(!_wv._){var _ww=_wv.a;if(!(imul(_wu,_ww)|0)){return new T1(0,imul(_wu,_ww)|0);}else{_wr=new T1(1,I_fromInt(_wu));_ws=new T1(1,I_fromInt(_ww));continue;}}else{_wr=new T1(1,I_fromInt(_wu));_ws=_wv;continue;}}else{var _wx=E(_ws);if(!_wx._){_wr=_wt;_ws=new T1(1,I_fromInt(_wx.a));continue;}else{return new T1(1,I_mul(_wt.a,_wx.a));}}}},_wy=function(_wz,_wA,_wB){while(1){if(!(_wA%2)){var _wC=B(_wq(_wz,_wz)),_wD=quot(_wA,2);_wz=_wC;_wA=_wD;continue;}else{var _wE=E(_wA);if(_wE==1){return new F(function(){return _wq(_wz,_wB);});}else{var _wC=B(_wq(_wz,_wz)),_wF=B(_wq(_wz,_wB));_wz=_wC;_wA=quot(_wE-1|0,2);_wB=_wF;continue;}}}},_wG=function(_wH,_wI){while(1){if(!(_wI%2)){var _wJ=B(_wq(_wH,_wH)),_wK=quot(_wI,2);_wH=_wJ;_wI=_wK;continue;}else{var _wL=E(_wI);if(_wL==1){return E(_wH);}else{return new F(function(){return _wy(B(_wq(_wH,_wH)),quot(_wL-1|0,2),_wH);});}}}},_wM=function(_wN){return E(E(_wN).b);},_wO=function(_wP){return E(E(_wP).c);},_wQ=new T1(0,0),_wR=function(_wS){return E(E(_wS).d);},_wT=function(_wU,_wV){var _wW=B(_tx(_wU)),_wX=new T(function(){return B(_tz(_wW));}),_wY=new T(function(){return B(A3(_wR,_wU,_wV,new T(function(){return B(A2(_28,_wX,_oP));})));});return new F(function(){return A3(_nz,B(_nx(B(_wM(_wW)))),_wY,new T(function(){return B(A2(_28,_wX,_wQ));}));});},_wZ=new T(function(){return B(unCStr("Negative exponent"));}),_x0=new T(function(){return B(err(_wZ));}),_x1=function(_x2){return E(E(_x2).c);},_x3=function(_x4,_x5,_x6,_x7){var _x8=B(_tx(_x5)),_x9=new T(function(){return B(_tz(_x8));}),_xa=B(_wM(_x8));if(!B(A3(_wO,_xa,_x7,new T(function(){return B(A2(_28,_x9,_wQ));})))){if(!B(A3(_nz,B(_nx(_xa)),_x7,new T(function(){return B(A2(_28,_x9,_wQ));})))){var _xb=new T(function(){return B(A2(_28,_x9,_oP));}),_xc=new T(function(){return B(A2(_28,_x9,_oF));}),_xd=B(_nx(_xa)),_xe=function(_xf,_xg,_xh){while(1){var _xi=B((function(_xj,_xk,_xl){if(!B(_wT(_x5,_xk))){if(!B(A3(_nz,_xd,_xk,_xc))){var _xm=new T(function(){return B(A3(_x1,_x5,new T(function(){return B(A3(_24,_x9,_xk,_xc));}),_xb));});_xf=new T(function(){return B(A3(_1Q,_x4,_xj,_xj));});_xg=_xm;_xh=new T(function(){return B(A3(_1Q,_x4,_xj,_xl));});return __continue;}else{return new F(function(){return A3(_1Q,_x4,_xj,_xl);});}}else{var _xn=_xl;_xf=new T(function(){return B(A3(_1Q,_x4,_xj,_xj));});_xg=new T(function(){return B(A3(_x1,_x5,_xk,_xb));});_xh=_xn;return __continue;}})(_xf,_xg,_xh));if(_xi!=__continue){return _xi;}}},_xo=function(_xp,_xq){while(1){var _xr=B((function(_xs,_xt){if(!B(_wT(_x5,_xt))){if(!B(A3(_nz,_xd,_xt,_xc))){var _xu=new T(function(){return B(A3(_x1,_x5,new T(function(){return B(A3(_24,_x9,_xt,_xc));}),_xb));});return new F(function(){return _xe(new T(function(){return B(A3(_1Q,_x4,_xs,_xs));}),_xu,_xs);});}else{return E(_xs);}}else{_xp=new T(function(){return B(A3(_1Q,_x4,_xs,_xs));});_xq=new T(function(){return B(A3(_x1,_x5,_xt,_xb));});return __continue;}})(_xp,_xq));if(_xr!=__continue){return _xr;}}};return new F(function(){return _xo(_x6,_x7);});}else{return new F(function(){return A2(_28,_x4,_oF);});}}else{return E(_x0);}},_xv=new T(function(){return B(err(_wZ));}),_xw=function(_xx,_xy){var _xz=B(_st(_xy)),_xA=_xz.a,_xB=_xz.b,_xC=new T(function(){return B(_tz(new T(function(){return B(_tx(_xx));})));});if(_xB<0){var _xD= -_xB;if(_xD>=0){var _xE=E(_xD);if(!_xE){var _xF=E(_oF);}else{var _xF=B(_wG(_wp,_xE));}if(!B(_5q(_xF,_5T))){var _xG=B(_5K(_xA,_xF));return new T2(0,new T(function(){return B(A2(_28,_xC,_xG.a));}),new T(function(){return B(_5m(_xG.b,_xB));}));}else{return E(_5l);}}else{return E(_xv);}}else{var _xH=new T(function(){var _xI=new T(function(){return B(_x3(_xC,_wo,new T(function(){return B(A2(_28,_xC,_wp));}),_xB));});return B(A3(_1Q,_xC,new T(function(){return B(A2(_28,_xC,_xA));}),_xI));});return new T2(0,_xH,_8I);}},_xJ=function(_xK,_xL){var _xM=B(_xw(_xK,E(_xL))),_xN=_xM.a;if(E(_xM.b)<=0){return E(_xN);}else{var _xO=B(_tz(B(_tx(_xK))));return new F(function(){return A3(_1S,_xO,_xN,new T(function(){return B(A2(_28,_xO,_4c));}));});}},_xP=function(_xQ,_xR){var _xS=B(_xw(_xQ,E(_xR))),_xT=_xS.a;if(E(_xS.b)>=0){return E(_xT);}else{var _xU=B(_tz(B(_tx(_xQ))));return new F(function(){return A3(_24,_xU,_xT,new T(function(){return B(A2(_28,_xU,_4c));}));});}},_xV=function(_xW,_xX){var _xY=B(_xw(_xW,E(_xX)));return new T2(0,_xY.a,_xY.b);},_xZ=function(_y0,_y1){var _y2=B(_xw(_y0,_y1)),_y3=_y2.a,_y4=E(_y2.b),_y5=new T(function(){var _y6=B(_tz(B(_tx(_y0))));if(_y4>=0){return B(A3(_1S,_y6,_y3,new T(function(){return B(A2(_28,_y6,_4c));})));}else{return B(A3(_24,_y6,_y3,new T(function(){return B(A2(_28,_y6,_4c));})));}}),_y7=function(_y8){var _y9=_y8-0.5;return (_y9>=0)?(E(_y9)==0)?(!B(_wT(_y0,_y3)))?E(_y5):E(_y3):E(_y5):E(_y3);},_ya=E(_y4);if(!_ya){return new F(function(){return _y7(0);});}else{if(_ya<=0){var _yb= -_ya-0.5;return (_yb>=0)?(E(_yb)==0)?(!B(_wT(_y0,_y3)))?E(_y5):E(_y3):E(_y5):E(_y3);}else{return new F(function(){return _y7(_ya);});}}},_yc=function(_yd,_ye){return new F(function(){return _xZ(_yd,E(_ye));});},_yf=function(_yg,_yh){return E(B(_xw(_yg,E(_yh))).a);},_yi={_:0,a:_tw,b:_lm,c:_xV,d:_yf,e:_yc,f:_xJ,g:_xP},_yj=new T1(0,1),_yk=function(_yl,_ym){var _yn=E(_yl);return new T2(0,_yn,new T(function(){var _yo=B(_yk(B(_5B(_yn,_ym)),_ym));return new T2(1,_yo.a,_yo.b);}));},_yp=function(_yq){var _yr=B(_yk(_yq,_yj));return new T2(1,_yr.a,_yr.b);},_ys=function(_yt,_yu){var _yv=B(_yk(_yt,new T(function(){return B(_7W(_yu,_yt));})));return new T2(1,_yv.a,_yv.b);},_yw=new T1(0,0),_yx=function(_yy,_yz){var _yA=E(_yy);if(!_yA._){var _yB=_yA.a,_yC=E(_yz);return (_yC._==0)?_yB>=_yC.a:I_compareInt(_yC.a,_yB)<=0;}else{var _yD=_yA.a,_yE=E(_yz);return (_yE._==0)?I_compareInt(_yD,_yE.a)>=0:I_compare(_yD,_yE.a)>=0;}},_yF=function(_yG,_yH,_yI){if(!B(_yx(_yH,_yw))){var _yJ=function(_yK){return (!B(_6d(_yK,_yI)))?new T2(1,_yK,new T(function(){return B(_yJ(B(_5B(_yK,_yH))));})):__Z;};return new F(function(){return _yJ(_yG);});}else{var _yL=function(_yM){return (!B(_64(_yM,_yI)))?new T2(1,_yM,new T(function(){return B(_yL(B(_5B(_yM,_yH))));})):__Z;};return new F(function(){return _yL(_yG);});}},_yN=function(_yO,_yP,_yQ){return new F(function(){return _yF(_yO,B(_7W(_yP,_yO)),_yQ);});},_yR=function(_yS,_yT){return new F(function(){return _yF(_yS,_yj,_yT);});},_yU=function(_yV){return new F(function(){return _5y(_yV);});},_yW=function(_yX){return new F(function(){return _7W(_yX,_yj);});},_yY=function(_yZ){return new F(function(){return _5B(_yZ,_yj);});},_z0=function(_z1){return new F(function(){return _sw(E(_z1));});},_z2={_:0,a:_yY,b:_yW,c:_z0,d:_yU,e:_yp,f:_ys,g:_yR,h:_yN},_z3=function(_z4,_z5){while(1){var _z6=E(_z4);if(!_z6._){var _z7=E(_z6.a);if(_z7==(-2147483648)){_z4=new T1(1,I_fromInt(-2147483648));continue;}else{var _z8=E(_z5);if(!_z8._){return new T1(0,B(_un(_z7,_z8.a)));}else{_z4=new T1(1,I_fromInt(_z7));_z5=_z8;continue;}}}else{var _z9=_z6.a,_za=E(_z5);return (_za._==0)?new T1(1,I_div(_z9,I_fromInt(_za.a))):new T1(1,I_div(_z9,_za.a));}}},_zb=function(_zc,_zd){if(!B(_5q(_zd,_wQ))){return new F(function(){return _z3(_zc,_zd);});}else{return E(_5l);}},_ze=function(_zf,_zg){while(1){var _zh=E(_zf);if(!_zh._){var _zi=E(_zh.a);if(_zi==(-2147483648)){_zf=new T1(1,I_fromInt(-2147483648));continue;}else{var _zj=E(_zg);if(!_zj._){var _zk=_zj.a;return new T2(0,new T1(0,B(_un(_zi,_zk))),new T1(0,B(_uT(_zi,_zk))));}else{_zf=new T1(1,I_fromInt(_zi));_zg=_zj;continue;}}}else{var _zl=E(_zg);if(!_zl._){_zf=_zh;_zg=new T1(1,I_fromInt(_zl.a));continue;}else{var _zm=I_divMod(_zh.a,_zl.a);return new T2(0,new T1(1,_zm.a),new T1(1,_zm.b));}}}},_zn=function(_zo,_zp){if(!B(_5q(_zp,_wQ))){var _zq=B(_ze(_zo,_zp));return new T2(0,_zq.a,_zq.b);}else{return E(_5l);}},_zr=function(_zs,_zt){while(1){var _zu=E(_zs);if(!_zu._){var _zv=E(_zu.a);if(_zv==(-2147483648)){_zs=new T1(1,I_fromInt(-2147483648));continue;}else{var _zw=E(_zt);if(!_zw._){return new T1(0,B(_uT(_zv,_zw.a)));}else{_zs=new T1(1,I_fromInt(_zv));_zt=_zw;continue;}}}else{var _zx=_zu.a,_zy=E(_zt);return (_zy._==0)?new T1(1,I_mod(_zx,I_fromInt(_zy.a))):new T1(1,I_mod(_zx,_zy.a));}}},_zz=function(_zA,_zB){if(!B(_5q(_zB,_wQ))){return new F(function(){return _zr(_zA,_zB);});}else{return E(_5l);}},_zC=function(_zD,_zE){while(1){var _zF=E(_zD);if(!_zF._){var _zG=E(_zF.a);if(_zG==(-2147483648)){_zD=new T1(1,I_fromInt(-2147483648));continue;}else{var _zH=E(_zE);if(!_zH._){return new T1(0,quot(_zG,_zH.a));}else{_zD=new T1(1,I_fromInt(_zG));_zE=_zH;continue;}}}else{var _zI=_zF.a,_zJ=E(_zE);return (_zJ._==0)?new T1(0,I_toInt(I_quot(_zI,I_fromInt(_zJ.a)))):new T1(1,I_quot(_zI,_zJ.a));}}},_zK=function(_zL,_zM){if(!B(_5q(_zM,_wQ))){return new F(function(){return _zC(_zL,_zM);});}else{return E(_5l);}},_zN=function(_zO,_zP){if(!B(_5q(_zP,_wQ))){var _zQ=B(_5K(_zO,_zP));return new T2(0,_zQ.a,_zQ.b);}else{return E(_5l);}},_zR=function(_zS,_zT){while(1){var _zU=E(_zS);if(!_zU._){var _zV=E(_zU.a);if(_zV==(-2147483648)){_zS=new T1(1,I_fromInt(-2147483648));continue;}else{var _zW=E(_zT);if(!_zW._){return new T1(0,_zV%_zW.a);}else{_zS=new T1(1,I_fromInt(_zV));_zT=_zW;continue;}}}else{var _zX=_zU.a,_zY=E(_zT);return (_zY._==0)?new T1(1,I_rem(_zX,I_fromInt(_zY.a))):new T1(1,I_rem(_zX,_zY.a));}}},_zZ=function(_A0,_A1){if(!B(_5q(_A1,_wQ))){return new F(function(){return _zR(_A0,_A1);});}else{return E(_5l);}},_A2=function(_A3){return E(_A3);},_A4=function(_A5){return E(_A5);},_A6=function(_A7){var _A8=E(_A7);if(!_A8._){var _A9=E(_A8.a);return (_A9==(-2147483648))?E(_8A):(_A9<0)?new T1(0, -_A9):E(_A8);}else{var _Aa=_A8.a;return (I_compareInt(_Aa,0)>=0)?E(_A8):new T1(1,I_negate(_Aa));}},_Ab=new T1(0,0),_Ac=new T1(0,-1),_Ad=function(_Ae){var _Af=E(_Ae);if(!_Af._){var _Ag=_Af.a;return (_Ag>=0)?(E(_Ag)==0)?E(_Ab):E(_6c):E(_Ac);}else{var _Ah=I_compareInt(_Af.a,0);return (_Ah<=0)?(E(_Ah)==0)?E(_Ab):E(_Ac):E(_6c);}},_Ai={_:0,a:_5B,b:_7W,c:_wq,d:_8B,e:_A6,f:_Ad,g:_A4},_Aj=function(_Ak,_Al){var _Am=E(_Ak);if(!_Am._){var _An=_Am.a,_Ao=E(_Al);return (_Ao._==0)?_An!=_Ao.a:(I_compareInt(_Ao.a,_An)==0)?false:true;}else{var _Ap=_Am.a,_Aq=E(_Al);return (_Aq._==0)?(I_compareInt(_Ap,_Aq.a)==0)?false:true:(I_compare(_Ap,_Aq.a)==0)?false:true;}},_Ar=new T2(0,_5q,_Aj),_As=function(_At,_Au){return (!B(_7H(_At,_Au)))?E(_At):E(_Au);},_Av=function(_Aw,_Ax){return (!B(_7H(_Aw,_Ax)))?E(_Ax):E(_Aw);},_Ay={_:0,a:_Ar,b:_4d,c:_6d,d:_7H,e:_64,f:_yx,g:_As,h:_Av},_Az=function(_AA){return new T2(0,E(_AA),E(_oF));},_AB=new T3(0,_Ai,_Ay,_Az),_AC={_:0,a:_AB,b:_z2,c:_zK,d:_zZ,e:_zb,f:_zz,g:_zN,h:_zn,i:_A2},_AD=function(_AE){return E(E(_AE).b);},_AF=function(_AG){return E(E(_AG).g);},_AH=new T1(0,1),_AI=function(_AJ,_AK,_AL){var _AM=B(_AD(_AJ)),_AN=B(_1O(_AM)),_AO=new T(function(){var _AP=new T(function(){var _AQ=new T(function(){var _AR=new T(function(){return B(A3(_AF,_AJ,_AC,new T(function(){return B(A3(_aW,_AM,_AK,_AL));})));});return B(A2(_28,_AN,_AR));}),_AS=new T(function(){return B(A2(_2l,_AN,new T(function(){return B(A2(_28,_AN,_AH));})));});return B(A3(_1Q,_AN,_AS,_AQ));});return B(A3(_1Q,_AN,_AP,_AL));});return new F(function(){return A3(_1S,_AN,_AK,_AO);});},_AT=1.5707963267948966,_AU=function(_AV){return 0.2/Math.cos(B(_AI(_yi,_AV,_AT))-0.7853981633974483);},_AW=0.3,_AX=-0.1,_AY=new T3(0,_sc,_AX,_AW),_AZ=new T2(0,_AY,_sc),_B0=new T(function(){var _B1=B(_qK(_AU,_s9,_ss,_AZ,_sm));return {_:0,a:_B1.a,b:_B1.b,c:_B1.c,d:_B1.d,e:_B1.e,f:_B1.f,g:_B1.g,h:_B1.h};}),_B2=new T2(1,_B0,_T),_B3=new T2(1,_sn,_B2),_B4=new T(function(){return B(unCStr("Negative range size"));}),_B5=new T(function(){return B(err(_B4));}),_B6=function(_){var _B7=B(_ke(_B3,0))-1|0,_B8=function(_B9){if(_B9>=0){var _Ba=newArr(_B9,_kk),_Bb=_Ba,_Bc=E(_B9);if(!_Bc){return new T4(0,E(_sp),E(_B7),0,_Bb);}else{var _Bd=function(_Be,_Bf,_){while(1){var _Bg=E(_Be);if(!_Bg._){return E(_);}else{var _=_Bb[_Bf]=_Bg.a;if(_Bf!=(_Bc-1|0)){var _Bh=_Bf+1|0;_Be=_Bg.b;_Bf=_Bh;continue;}else{return E(_);}}}},_=B((function(_Bi,_Bj,_Bk,_){var _=_Bb[_Bk]=_Bi;if(_Bk!=(_Bc-1|0)){return new F(function(){return _Bd(_Bj,_Bk+1|0,_);});}else{return E(_);}})(_sn,_B2,0,_));return new T4(0,E(_sp),E(_B7),_Bc,_Bb);}}else{return E(_B5);}};if(0>_B7){return new F(function(){return _B8(0);});}else{return new F(function(){return _B8(_B7+1|0);});}},_Bl=function(_Bm){var _Bn=B(A1(_Bm,_));return E(_Bn);},_Bo=new T(function(){return B(_Bl(_B6));}),_Bp=function(_Bq,_Br,_){var _Bs=B(A1(_Bq,_)),_Bt=B(A1(_Br,_));return _Bs;},_Bu=function(_Bv,_Bw,_){var _Bx=B(A1(_Bv,_)),_By=B(A1(_Bw,_));return new T(function(){return B(A1(_Bx,_By));});},_Bz=function(_BA,_BB,_){var _BC=B(A1(_BB,_));return _BA;},_BD=function(_BE,_BF,_){var _BG=B(A1(_BF,_));return new T(function(){return B(A1(_BE,_BG));});},_BH=new T2(0,_BD,_Bz),_BI=function(_BJ,_){return _BJ;},_BK=function(_BL,_BM,_){var _BN=B(A1(_BL,_));return new F(function(){return A1(_BM,_);});},_BO=new T5(0,_BH,_BI,_Bu,_BK,_Bp),_BP=function(_BQ){var _BR=E(_BQ);return (E(_BR.b)-E(_BR.a)|0)+1|0;},_BS=function(_BT,_BU){var _BV=E(_BT),_BW=E(_BU);return (E(_BV.a)>_BW)?false:_BW<=E(_BV.b);},_BX=function(_BY,_BZ){var _C0=jsShowI(_BY);return new F(function(){return _14(fromJSStr(_C0),_BZ);});},_C1=function(_C2,_C3,_C4){if(_C3>=0){return new F(function(){return _BX(_C3,_C4);});}else{if(_C2<=6){return new F(function(){return _BX(_C3,_C4);});}else{return new T2(1,_9n,new T(function(){var _C5=jsShowI(_C3);return B(_14(fromJSStr(_C5),new T2(1,_9m,_C4)));}));}}},_C6=function(_C7){return new F(function(){return _C1(0,E(_C7),_T);});},_C8=function(_C9,_Ca,_Cb){return new F(function(){return _C1(E(_C9),E(_Ca),_Cb);});},_Cc=function(_Cd,_Ce){return new F(function(){return _C1(0,E(_Cd),_Ce);});},_Cf=function(_Cg,_Ch){return new F(function(){return _51(_Cc,_Cg,_Ch);});},_Ci=new T3(0,_C8,_C6,_Cf),_Cj=0,_Ck=function(_Cl,_Cm,_Cn){return new F(function(){return A1(_Cl,new T2(1,_4Y,new T(function(){return B(A1(_Cm,_Cn));})));});},_Co=new T(function(){return B(unCStr("foldr1"));}),_Cp=new T(function(){return B(_o5(_Co));}),_Cq=function(_Cr,_Cs){var _Ct=E(_Cs);if(!_Ct._){return E(_Cp);}else{var _Cu=_Ct.a,_Cv=E(_Ct.b);if(!_Cv._){return E(_Cu);}else{return new F(function(){return A2(_Cr,_Cu,new T(function(){return B(_Cq(_Cr,_Cv));}));});}}},_Cw=new T(function(){return B(unCStr(" out of range "));}),_Cx=new T(function(){return B(unCStr("}.index: Index "));}),_Cy=new T(function(){return B(unCStr("Ix{"));}),_Cz=new T2(1,_9m,_T),_CA=new T2(1,_9m,_Cz),_CB=0,_CC=function(_CD){return E(E(_CD).a);},_CE=function(_CF,_CG,_CH,_CI,_CJ){var _CK=new T(function(){var _CL=new T(function(){var _CM=new T(function(){var _CN=new T(function(){var _CO=new T(function(){return B(A3(_Cq,_Ck,new T2(1,new T(function(){return B(A3(_CC,_CH,_CB,_CI));}),new T2(1,new T(function(){return B(A3(_CC,_CH,_CB,_CJ));}),_T)),_CA));});return B(_14(_Cw,new T2(1,_9n,new T2(1,_9n,_CO))));});return B(A(_CC,[_CH,_Cj,_CG,new T2(1,_9m,_CN)]));});return B(_14(_Cx,new T2(1,_9n,_CM)));},1);return B(_14(_CF,_CL));},1);return new F(function(){return err(B(_14(_Cy,_CK)));});},_CP=function(_CQ,_CR,_CS,_CT,_CU){return new F(function(){return _CE(_CQ,_CR,_CU,_CS,_CT);});},_CV=function(_CW,_CX,_CY,_CZ){var _D0=E(_CY);return new F(function(){return _CP(_CW,_CX,_D0.a,_D0.b,_CZ);});},_D1=function(_D2,_D3,_D4,_D5){return new F(function(){return _CV(_D5,_D4,_D3,_D2);});},_D6=new T(function(){return B(unCStr("Int"));}),_D7=function(_D8,_D9){return new F(function(){return _D1(_Ci,_D9,_D8,_D6);});},_Da=function(_Db,_Dc){var _Dd=E(_Db),_De=E(_Dd.a),_Df=E(_Dc);if(_De>_Df){return new F(function(){return _D7(_Df,_Dd);});}else{if(_Df>E(_Dd.b)){return new F(function(){return _D7(_Df,_Dd);});}else{return _Df-_De|0;}}},_Dg=function(_Dh){var _Di=E(_Dh);return new F(function(){return _u7(_Di.a,_Di.b);});},_Dj=function(_Dk){var _Dl=E(_Dk),_Dm=E(_Dl.a),_Dn=E(_Dl.b);return (_Dm>_Dn)?E(_Cj):(_Dn-_Dm|0)+1|0;},_Do=function(_Dp,_Dq){return new F(function(){return _vw(_Dq,E(_Dp).a);});},_Dr={_:0,a:_wm,b:_Dg,c:_Da,d:_Do,e:_BS,f:_Dj,g:_BP},_Ds=function(_Dt,_Du){return new T2(1,_Dt,_Du);},_Dv=function(_Dw,_Dx){var _Dy=E(_Dx);return new T2(0,_Dy.a,_Dy.b);},_Dz=function(_DA){return E(E(_DA).f);},_DB=function(_DC,_DD,_DE){var _DF=E(_DD),_DG=_DF.a,_DH=_DF.b,_DI=function(_){var _DJ=B(A2(_Dz,_DC,_DF));if(_DJ>=0){var _DK=newArr(_DJ,_kk),_DL=_DK,_DM=E(_DJ);if(!_DM){return new T(function(){return new T4(0,E(_DG),E(_DH),0,_DL);});}else{var _DN=function(_DO,_DP,_){while(1){var _DQ=E(_DO);if(!_DQ._){return E(_);}else{var _=_DL[_DP]=_DQ.a;if(_DP!=(_DM-1|0)){var _DR=_DP+1|0;_DO=_DQ.b;_DP=_DR;continue;}else{return E(_);}}}},_=B(_DN(_DE,0,_));return new T(function(){return new T4(0,E(_DG),E(_DH),_DM,_DL);});}}else{return E(_B5);}};return new F(function(){return _Bl(_DI);});},_DS=function(_DT,_DU,_DV,_DW){var _DX=new T(function(){var _DY=E(_DW),_DZ=_DY.c-1|0,_E0=new T(function(){return B(A2(_eI,_DU,_T));});if(0<=_DZ){var _E1=new T(function(){return B(_aS(_DU));}),_E2=function(_E3){var _E4=new T(function(){var _E5=new T(function(){return B(A1(_DV,new T(function(){return E(_DY.d[_E3]);})));});return B(A3(_b0,_E1,_Ds,_E5));});return new F(function(){return A3(_aY,_DU,_E4,new T(function(){if(_E3!=_DZ){return B(_E2(_E3+1|0));}else{return E(_E0);}}));});};return B(_E2(0));}else{return E(_E0);}}),_E6=new T(function(){return B(_Dv(_DT,_DW));});return new F(function(){return A3(_b0,B(_aS(_DU)),function(_E7){return new F(function(){return _DB(_DT,_E6,_E7);});},_DX);});},_E8=function(_){return _S;},_E9=new T(function(){return eval("vertex");}),_Ea=function(_Eb,_Ec,_Ed,_Ee,_Ef,_Eg,_){var _Eh=__apply(E(_E9),new T2(1,_Eg,new T2(1,_Ef,new T2(1,_Ee,new T2(1,_Ed,new T2(1,_Ec,new T2(1,_Eb,_T)))))));return new F(function(){return _E8(_);});},_Ei=function(_Ej,_){while(1){var _Ek=E(_Ej);if(!_Ek._){return _S;}else{var _El=E(_Ek.a),_Em=E(_El.a),_En=E(_Em.a),_Eo=E(_Em.b),_Ep=B(_Ea(E(_En.a),E(_En.b),E(_En.c),E(_Eo.a),E(_Eo.b),E(_Em.c),_)),_Eq=E(_El.b),_Er=E(_Eq.a),_Es=E(_Eq.b),_Et=B(_Ea(E(_Er.a),E(_Er.b),E(_Er.c),E(_Es.a),E(_Es.b),E(_Eq.c),_)),_Eu=E(_El.c),_Ev=E(_Eu.a),_Ew=E(_Eu.b),_Ex=B(_Ea(E(_Ev.a),E(_Ev.b),E(_Ev.c),E(_Ew.a),E(_Ew.b),E(_Eu.c),_));_Ej=_Ek.b;continue;}}},_Ey=new T(function(){return eval("drawTriangles");}),_Ez=function(_){var _EA=__app0(E(_Ey));return new F(function(){return _E8(_);});},_EB=function(_EC,_){var _ED=B(_Ei(_EC,_));return new F(function(){return _Ez(_);});},_EE=function(_EF,_){return new F(function(){return _EB(E(_EF).h,_);});},_EG=new T(function(){return eval("draw");}),_EH=function(_EI){return E(_EI);},_EJ=function(_EK){return E(_EK);},_EL=function(_EM,_EN){return E(_EN);},_EO=function(_EP,_EQ){return E(_EP);},_ER=function(_ES){return E(_ES);},_ET=new T2(0,_ER,_EO),_EU=function(_EV,_EW){return E(_EV);},_EX=new T5(0,_ET,_EJ,_EH,_EL,_EU),_EY=function(_EZ,_F0,_F1,_F2,_F3,_F4){var _F5=new T(function(){var _F6=E(_F2),_F7=E(_F3),_F8=new T(function(){var _F9=E(_F6.a),_Fa=E(_F7.a);return new T3(0,new T(function(){return E(_F9.a)+E(_Fa.a)*5.0e-2;}),new T(function(){return E(_F9.b)+E(_Fa.b)*5.0e-2;}),new T(function(){return E(_F9.c)+E(_Fa.c)*5.0e-2;}));});return new T2(0,_F8,new T(function(){return E(_F6.b)+E(_F7.b)*5.0e-2;}));});return new F(function(){return _qi(_EZ,_F0,_F1,_F5,_F3,_F4);});},_Fb=new T2(0,_lO,_mn),_Fc=function(_Fd){var _Fe=E(_Fd),_Ff=_Fe.b,_Fg=_Fe.g,_Fh=new T(function(){var _Fi=E(_Fe.e),_Fj=new T(function(){var _Fk=E(_Fi.a),_Fl=E(_Ff),_Fm=E(_Fg),_Fn=B(_n0(_Fb,_Fl.a,_Fl.b,_Fl.c,_Fm.a,_Fm.b,_Fm.c));return new T3(0,new T(function(){return E(_Fk.a)+E(_Fn.a)*5.0e-2;}),new T(function(){return E(_Fk.b)+E(_Fn.b)*5.0e-2;}),new T(function(){return E(_Fk.c)+E(_Fn.c)*5.0e-2;}));});return new T2(0,_Fj,_Fi.b);});return {_:0,a:_Fe.a,b:_Ff,c:_Fe.c,d:_Fe.d,e:_Fh,f:_Fe.f,g:_Fg,h:_Fe.h};},_Fo=function(_Fp){var _Fq=E(_Fp),_Fr=B(_EY(_Fq.a,_Fq.b,_Fq.c,_Fq.d,_Fq.e,_Fq.f));return {_:0,a:_Fr.a,b:_Fr.b,c:_Fr.c,d:_Fr.d,e:_Fr.e,f:_Fr.f,g:_Fr.g,h:_Fr.h};},_Fs=function(_Ft){var _Fu=E(_Ft);if(!_Fu._){return __Z;}else{return new F(function(){return _14(_Fu.a,new T(function(){return B(_Fs(_Fu.b));},1));});}},_Fv=new T(function(){return B(unCStr("base"));}),_Fw=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Fx=new T(function(){return B(unCStr("IOException"));}),_Fy=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fv,_Fw,_Fx),_Fz=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fy,_T,_T),_FA=function(_FB){return E(_Fz);},_FC=function(_FD){var _FE=E(_FD);return new F(function(){return _4y(B(_4w(_FE.a)),_FA,_FE.b);});},_FF=new T(function(){return B(unCStr(": "));}),_FG=new T(function(){return B(unCStr(")"));}),_FH=new T(function(){return B(unCStr(" ("));}),_FI=new T(function(){return B(unCStr("interrupted"));}),_FJ=new T(function(){return B(unCStr("system error"));}),_FK=new T(function(){return B(unCStr("unsatisified constraints"));}),_FL=new T(function(){return B(unCStr("user error"));}),_FM=new T(function(){return B(unCStr("permission denied"));}),_FN=new T(function(){return B(unCStr("illegal operation"));}),_FO=new T(function(){return B(unCStr("end of file"));}),_FP=new T(function(){return B(unCStr("resource exhausted"));}),_FQ=new T(function(){return B(unCStr("resource busy"));}),_FR=new T(function(){return B(unCStr("does not exist"));}),_FS=new T(function(){return B(unCStr("already exists"));}),_FT=new T(function(){return B(unCStr("resource vanished"));}),_FU=new T(function(){return B(unCStr("timeout"));}),_FV=new T(function(){return B(unCStr("unsupported operation"));}),_FW=new T(function(){return B(unCStr("hardware fault"));}),_FX=new T(function(){return B(unCStr("inappropriate type"));}),_FY=new T(function(){return B(unCStr("invalid argument"));}),_FZ=new T(function(){return B(unCStr("failed"));}),_G0=new T(function(){return B(unCStr("protocol error"));}),_G1=function(_G2,_G3){switch(E(_G2)){case 0:return new F(function(){return _14(_FS,_G3);});break;case 1:return new F(function(){return _14(_FR,_G3);});break;case 2:return new F(function(){return _14(_FQ,_G3);});break;case 3:return new F(function(){return _14(_FP,_G3);});break;case 4:return new F(function(){return _14(_FO,_G3);});break;case 5:return new F(function(){return _14(_FN,_G3);});break;case 6:return new F(function(){return _14(_FM,_G3);});break;case 7:return new F(function(){return _14(_FL,_G3);});break;case 8:return new F(function(){return _14(_FK,_G3);});break;case 9:return new F(function(){return _14(_FJ,_G3);});break;case 10:return new F(function(){return _14(_G0,_G3);});break;case 11:return new F(function(){return _14(_FZ,_G3);});break;case 12:return new F(function(){return _14(_FY,_G3);});break;case 13:return new F(function(){return _14(_FX,_G3);});break;case 14:return new F(function(){return _14(_FW,_G3);});break;case 15:return new F(function(){return _14(_FV,_G3);});break;case 16:return new F(function(){return _14(_FU,_G3);});break;case 17:return new F(function(){return _14(_FT,_G3);});break;default:return new F(function(){return _14(_FI,_G3);});}},_G4=new T(function(){return B(unCStr("}"));}),_G5=new T(function(){return B(unCStr("{handle: "));}),_G6=function(_G7,_G8,_G9,_Ga,_Gb,_Gc){var _Gd=new T(function(){var _Ge=new T(function(){var _Gf=new T(function(){var _Gg=E(_Ga);if(!_Gg._){return E(_Gc);}else{var _Gh=new T(function(){return B(_14(_Gg,new T(function(){return B(_14(_FG,_Gc));},1)));},1);return B(_14(_FH,_Gh));}},1);return B(_G1(_G8,_Gf));}),_Gi=E(_G9);if(!_Gi._){return E(_Ge);}else{return B(_14(_Gi,new T(function(){return B(_14(_FF,_Ge));},1)));}}),_Gj=E(_Gb);if(!_Gj._){var _Gk=E(_G7);if(!_Gk._){return E(_Gd);}else{var _Gl=E(_Gk.a);if(!_Gl._){var _Gm=new T(function(){var _Gn=new T(function(){return B(_14(_G4,new T(function(){return B(_14(_FF,_Gd));},1)));},1);return B(_14(_Gl.a,_Gn));},1);return new F(function(){return _14(_G5,_Gm);});}else{var _Go=new T(function(){var _Gp=new T(function(){return B(_14(_G4,new T(function(){return B(_14(_FF,_Gd));},1)));},1);return B(_14(_Gl.a,_Gp));},1);return new F(function(){return _14(_G5,_Go);});}}}else{return new F(function(){return _14(_Gj.a,new T(function(){return B(_14(_FF,_Gd));},1));});}},_Gq=function(_Gr){var _Gs=E(_Gr);return new F(function(){return _G6(_Gs.a,_Gs.b,_Gs.c,_Gs.d,_Gs.f,_T);});},_Gt=function(_Gu,_Gv,_Gw){var _Gx=E(_Gv);return new F(function(){return _G6(_Gx.a,_Gx.b,_Gx.c,_Gx.d,_Gx.f,_Gw);});},_Gy=function(_Gz,_GA){var _GB=E(_Gz);return new F(function(){return _G6(_GB.a,_GB.b,_GB.c,_GB.d,_GB.f,_GA);});},_GC=function(_GD,_GE){return new F(function(){return _51(_Gy,_GD,_GE);});},_GF=new T3(0,_Gt,_Gq,_GC),_GG=new T(function(){return new T5(0,_FA,_GF,_GH,_FC,_Gq);}),_GH=function(_GI){return new T2(0,_GG,_GI);},_GJ=__Z,_GK=7,_GL=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:43:7-13"));}),_GM=new T6(0,_GJ,_GK,_T,_GL,_GJ,_GJ),_GN=new T(function(){return B(_GH(_GM));}),_GO=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:44:7-13"));}),_GP=new T6(0,_GJ,_GK,_T,_GO,_GJ,_GJ),_GQ=new T(function(){return B(_GH(_GP));}),_GR=new T2(1,_T,_T),_GS=function(_GT,_){var _GU=B(_DS(_Dr,_EX,_Fc,_GT)),_GV=_GU.c,_GW=_GU.d,_GX=E(_GU.a),_GY=E(_GU.b);if(_GX<=_GY){var _GZ=function(_H0,_H1,_){if(_H0<=_GY){var _H2=E(_H1),_H3=function(_H4,_H5,_H6,_H7,_H8,_){if(_H5>_H0){return new F(function(){return die(_GN);});}else{if(_H0>_H6){return new F(function(){return die(_GN);});}else{if(_H5>_H4){return new F(function(){return die(_GQ);});}else{if(_H4>_H6){return new F(function(){return die(_GQ);});}else{if(_H4!=_GY){var _H9=B(_H3(_H4+1|0,_H5,_H6,_H7,_H8,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_H9).a);})),new T(function(){return E(E(_H9).b);}));}else{return new T2(0,_GR,new T4(0,E(_H5),E(_H6),_H7,_H8));}}}}}},_Ha=B(_H3(_H0,E(_H2.a),E(_H2.b),_H2.c,_H2.d,_));if(_H0!=_GY){var _Hb=B(_GZ(_H0+1|0,new T(function(){return E(E(_Ha).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Fs(E(_Ha).a));}),new T(function(){return E(E(_Hb).a);})),new T(function(){return E(E(_Hb).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Fs(E(_Ha).a));}),_T),new T(function(){return E(E(_Ha).b);}));}}else{if(_H0!=_GY){var _Hc=B(_GZ(_H0+1|0,_H1,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_Hc).a);})),new T(function(){return E(E(_Hc).b);}));}else{return new T2(0,new T2(1,_T,_T),_H1);}}},_Hd=function(_He,_Hf,_Hg,_Hh,_Hi,_){if(_He<=_GY){var _Hj=function(_Hk,_Hl,_Hm,_Hn,_Ho,_){if(_Hl>_He){return new F(function(){return die(_GN);});}else{if(_He>_Hm){return new F(function(){return die(_GN);});}else{if(_Hl>_Hk){return new F(function(){return die(_GQ);});}else{if(_Hk>_Hm){return new F(function(){return die(_GQ);});}else{if(_Hk!=_GY){var _Hp=B(_Hj(_Hk+1|0,_Hl,_Hm,_Hn,_Ho,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_Hp).a);})),new T(function(){return E(E(_Hp).b);}));}else{return new T2(0,_GR,new T4(0,E(_Hl),E(_Hm),_Hn,_Ho));}}}}}},_Hq=B(_Hj(_He,_Hf,_Hg,_Hh,_Hi,_));if(_He!=_GY){var _Hr=B(_GZ(_He+1|0,new T(function(){return E(E(_Hq).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Fs(E(_Hq).a));}),new T(function(){return E(E(_Hr).a);})),new T(function(){return E(E(_Hr).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Fs(E(_Hq).a));}),_T),new T(function(){return E(E(_Hq).b);}));}}else{if(_He!=_GY){var _Hs=B(_Hd(_He+1|0,_Hf,_Hg,_Hh,_Hi,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_Hs).a);})),new T(function(){return E(E(_Hs).b);}));}else{return new T2(0,new T2(1,_T,_T),new T4(0,E(_Hf),E(_Hg),_Hh,_Hi));}}},_Ht=B(_Hd(_GX,_GX,_GY,_GV,_GW,_)),_Hu=new T(function(){return B(_DS(_Dr,_EX,_Fo,new T(function(){return E(E(_Ht).b);})));});return new T2(0,_S,_Hu);}else{var _Hv=new T(function(){var _Hw=function(_){var _Hx=function(_Hy){if(_Hy>=0){var _Hz=newArr(_Hy,_kk),_HA=_Hz,_HB=E(_Hy);if(!_HB){return new T4(0,E(_GX),E(_GY),0,_HA);}else{var _HC=_GV-1|0,_HD=function(_HE,_HF,_){while(1){var _HG=E(_HE);if(!_HG._){return E(_);}else{var _=_HA[_HF]=_HG.a;if(_HF!=(_HB-1|0)){var _HH=_HF+1|0;_HE=_HG.b;_HF=_HH;continue;}else{return E(_);}}}};if(0<=_HC){var _HI=function(_HJ){return new T2(1,new T(function(){var _HK=E(_GW[_HJ]),_HL=B(_EY(_HK.a,_HK.b,_HK.c,_HK.d,_HK.e,_HK.f));return {_:0,a:_HL.a,b:_HL.b,c:_HL.c,d:_HL.d,e:_HL.e,f:_HL.f,g:_HL.g,h:_HL.h};}),new T(function(){if(_HJ!=_HC){return B(_HI(_HJ+1|0));}else{return __Z;}}));},_=B(_HD(B(_HI(0)),0,_));return new T4(0,E(_GX),E(_GY),_HB,_HA);}else{return new T4(0,E(_GX),E(_GY),_HB,_HA);}}}else{return E(_B5);}};if(_GX>_GY){return new F(function(){return _Hx(0);});}else{return new F(function(){return _Hx((_GY-_GX|0)+1|0);});}};return B(_Bl(_Hw));});return new T2(0,_S,_Hv);}},_HM=new T(function(){return eval("refresh");}),_HN=function(_HO,_){var _HP=__app0(E(_HM)),_HQ=__app0(E(_EG)),_HR=B(A(_DS,[_Dr,_BO,_EE,_HO,_])),_HS=B(_GS(_HO,_));return new T(function(){return E(E(_HS).b);});},_HT=function(_HU,_HV,_HW){var _HX=function(_){var _HY=B(_HN(_HU,_));return new T(function(){return B(A1(_HW,new T1(1,_HY)));});};return new T1(0,_HX);},_HZ=new T0(2),_I0=function(_I1,_I2,_I3){return function(_){var _I4=E(_I1),_I5=rMV(_I4),_I6=E(_I5);if(!_I6._){var _I7=new T(function(){var _I8=new T(function(){return B(A1(_I3,_S));});return B(_14(_I6.b,new T2(1,new T2(0,_I2,function(_I9){return E(_I8);}),_T)));}),_=wMV(_I4,new T2(0,_I6.a,_I7));return _HZ;}else{var _Ia=E(_I6.a);if(!_Ia._){var _=wMV(_I4,new T2(0,_I2,_T));return new T(function(){return B(A1(_I3,_S));});}else{var _=wMV(_I4,new T1(1,_Ia.b));return new T1(1,new T2(1,new T(function(){return B(A1(_I3,_S));}),new T2(1,new T(function(){return B(A2(_Ia.a,_I2,_U));}),_T)));}}};},_Ib=function(_Ic){return E(E(_Ic).b);},_Id=function(_Ie,_If,_Ig){var _Ih=new T(function(){return new T1(0,B(_I0(_If,_Ig,_U)));}),_Ii=function(_Ij){return new T1(1,new T2(1,new T(function(){return B(A1(_Ij,_S));}),new T2(1,_Ih,_T)));};return new F(function(){return A2(_Ib,_Ie,_Ii);});},_Ik=function(_){return new F(function(){return __jsNull();});},_Il=function(_Im){var _In=B(A1(_Im,_));return E(_In);},_Io=new T(function(){return B(_Il(_Ik));}),_Ip=new T(function(){return E(_Io);}),_Iq=new T(function(){return eval("window.requestAnimationFrame");}),_Ir=new T1(1,_T),_Is=function(_It,_Iu){return function(_){var _Iv=E(_It),_Iw=rMV(_Iv),_Ix=E(_Iw);if(!_Ix._){var _Iy=_Ix.a,_Iz=E(_Ix.b);if(!_Iz._){var _=wMV(_Iv,_Ir);return new T(function(){return B(A1(_Iu,_Iy));});}else{var _IA=E(_Iz.a),_=wMV(_Iv,new T2(0,_IA.a,_Iz.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Iu,_Iy));}),new T2(1,new T(function(){return B(A1(_IA.b,_U));}),_T)));}}else{var _IB=new T(function(){var _IC=function(_ID){var _IE=new T(function(){return B(A1(_Iu,_ID));});return function(_IF){return E(_IE);};};return B(_14(_Ix.a,new T2(1,_IC,_T)));}),_=wMV(_Iv,new T1(1,_IB));return _HZ;}};},_IG=function(_IH,_II){return new T1(0,B(_Is(_IH,_II)));},_IJ=function(_IK,_IL){var _IM=new T(function(){return new T1(0,B(_I0(_IK,_S,_U)));});return function(_){var _IN=__createJSFunc(2,function(_IO,_){var _IP=B(_1e(_IM,_T,_));return _Ip;}),_IQ=__app1(E(_Iq),_IN);return new T(function(){return B(_IG(_IK,_IL));});};},_IR=new T1(1,_T),_IS=function(_IT){var _IU=new T(function(){return B(_IV(_));}),_IW=new T(function(){var _IX=function(_IY){return E(_IU);},_IZ=function(_){var _J0=nMV(_IR);return new T(function(){return new T1(0,B(_IJ(_J0,_IX)));});};return B(A(_Id,[_13,_IT,_S,function(_J1){return E(new T1(0,_IZ));}]));}),_IV=function(_J2){return E(_IW);};return new F(function(){return _IV(_);});},_J3=function(_J4){return E(E(_J4).a);},_J5=function(_J6){return E(E(_J6).d);},_J7=function(_J8){return E(E(_J8).c);},_J9=function(_Ja){return E(E(_Ja).c);},_Jb=new T1(1,_T),_Jc=function(_Jd){var _Je=function(_){var _Jf=nMV(_Jb);return new T(function(){return B(A1(_Jd,_Jf));});};return new T1(0,_Je);},_Jg=function(_Jh,_Ji){var _Jj=new T(function(){return B(_J9(_Jh));}),_Jk=B(_J3(_Jh)),_Jl=function(_Jm){var _Jn=new T(function(){return B(A1(_Jj,new T(function(){return B(A1(_Ji,_Jm));})));});return new F(function(){return A3(_J7,_Jk,_Jn,new T(function(){return B(A2(_J5,_Jk,_Jm));}));});};return new F(function(){return A3(_J,_Jk,new T(function(){return B(A2(_Ib,_Jh,_Jc));}),_Jl);});},_Jo=function(_Jp,_Jq,_Jr){var _Js=new T(function(){return B(_J3(_Jp));}),_Jt=new T(function(){return B(A2(_J5,_Js,_S));}),_Ju=function(_Jv,_Jw){var _Jx=new T(function(){var _Jy=new T(function(){return B(A2(_Ib,_Jp,function(_Jz){return new F(function(){return _IG(_Jw,_Jz);});}));});return B(A3(_J,_Js,_Jy,new T(function(){return B(A1(_Jr,_Jv));})));});return new F(function(){return A3(_J,_Js,_Jx,function(_JA){var _JB=E(_JA);if(!_JB._){return E(_Jt);}else{return new F(function(){return _Ju(_JB.a,_Jw);});}});});};return new F(function(){return _Jg(_Jp,function(_Jz){return new F(function(){return _Ju(_Jq,_Jz);});});});},_JC=function(_){var _JD=__app2(E(_1j),E(_a5),E(_kd));return new F(function(){return _1e(new T(function(){return B(A(_Jo,[_13,_Bo,_HT,_IS]));}),_T,_);});},_JE=function(_){return new F(function(){return _JC(_);});};
var hasteMain = function() {B(A(_JE, [0]));};window.onload = hasteMain;