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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=new T1(0,10),_hP=new T1(0,7),_hQ=new T2(0,E(_hP),E(_hO)),_hR=new T1(0,9),_hS=new T2(0,E(_hR),E(_hO)),_hT=function(_hU){var _hV=new T(function(){return E(E(_hU).a);}),_hW=new T(function(){return B(_8H(_hV));}),_hX=new T(function(){return B(A2(_eE,_hW,_hS));}),_hY=new T(function(){return B(A2(_eE,_hW,_hQ));}),_hZ=new T(function(){return B(_8J(_hW));}),_i0=new T(function(){return B(A2(_8s,_hZ,_8r));}),_i1=new T(function(){return E(E(_hU).b);}),_i2=function(_i3){var _i4=new T(function(){var _i5=new T(function(){return B(A2(_fR,_hZ,new T(function(){return E(E(_i3).c);})));});return B(A3(_9p,_hZ,_i5,_i0));}),_i6=new T(function(){var _i7=new T(function(){var _i8=new T(function(){var _i9=new T(function(){return B(A3(_8L,_hZ,new T(function(){return E(E(_i3).c);}),_hX));});return B(A3(_9p,_hZ,_i9,_hY));});return B(A2(_bU,_hV,_i8));}),_ia=new T(function(){return B(A2(_fR,_hZ,new T(function(){return E(E(_i3).a);})));});return B(A3(_9p,_hZ,_ia,_i7));});return new F(function(){return A3(_gN,_i1,_i6,_i4);});};return E(_i2);},_ib=function(_ef,_ee){return new T2(0,_ef,_ee);},_ic=function(_id,_ie,_if){var _ig=new T(function(){var _ih=E(_id),_ii=_ih.a,_ij=new T(function(){return B(A1(_ih.b,new T(function(){return B(_8J(B(_8H(E(_ih.c).a))));})));});return B(A3(_8R,_ii,new T(function(){return B(A3(_8T,B(_8F(_ii)),_ib,_if));}),_ij));});return E(B(A1(_ie,_ig)).b);},_ik=function(_il){var _im=new T(function(){return E(E(_il).a);}),_in=new T(function(){return E(E(_il).b);}),_io=new T(function(){var _ip=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_im,_in))));}),new T3(0,_8p,_8u,new T2(0,_im,_in))));}),_iq=new T(function(){var _ir=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_im,_in))));}),new T3(0,_8p,_8u,new T2(0,_im,_in))));});return B(_eb(_ir,new T3(0,_8p,_8u,new T2(0,_im,_in))));});return B(_hT(new T2(0,_iq,_ip)));});return function(_is){return new F(function(){return _ic(new T3(0,_8p,_8u,new T2(0,_im,_in)),_io,_is);});};},_it=new T(function(){return B(_ik(_7V));}),_iu=new T(function(){return B(A1(_it,_E));}),_iv=new T(function(){return E(E(_iu).a);}),_iw=new T(function(){return B(unCStr(",y:"));}),_ix=new T1(0,_iw),_iy=new T(function(){return E(E(_iu).b);}),_iz=new T(function(){return B(unCStr(",z:"));}),_iA=new T1(0,_iz),_iB=new T(function(){return E(E(_iu).c);}),_iC=new T(function(){return B(unCStr("})"));}),_iD=new T1(0,_iC),_iE=new T2(1,_iD,_w),_iF=new T2(1,_iB,_iE),_iG=new T2(1,_iA,_iF),_iH=new T2(1,_iy,_iG),_iI=new T2(1,_ix,_iH),_iJ=new T2(1,_iv,_iI),_iK=new T(function(){return B(unCStr("({x:"));}),_iL=new T1(0,_iK),_iM=new T2(1,_iL,_iJ),_iN=function(_iO){return E(_iO);},_iP=new T(function(){return toJSStr(B(_e(_x,_iN,_iM)));}),_iQ=new T(function(){return B(_hT(_7V));}),_iR=new T(function(){return B(A1(_iQ,_E));}),_iS=new T(function(){return toJSStr(B(_4(_x,_iN,_iR)));}),_iT=function(_iU,_iV,_iW){var _iX=E(_iW);if(!_iX._){return new F(function(){return A1(_iV,_iX.a);});}else{var _iY=new T(function(){return B(_0(_iU));}),_iZ=new T(function(){return B(_2(_iU));}),_j0=function(_j1){var _j2=E(_j1);if(!_j2._){return E(_iZ);}else{return new F(function(){return A2(_iY,new T(function(){return B(_iT(_iU,_iV,_j2.a));}),new T(function(){return B(_j0(_j2.b));}));});}};return new F(function(){return _j0(_iX.a);});}},_j3=new T(function(){return B(unCStr("x"));}),_j4=new T1(0,_j3),_j5=new T(function(){return B(unCStr("y"));}),_j6=new T1(0,_j5),_j7=new T(function(){return B(unCStr("z"));}),_j8=new T1(0,_j7),_j9=new T3(0,E(_j4),E(_j6),E(_j8)),_ja=new T(function(){return B(unCStr(","));}),_jb=new T1(0,_ja),_jc=new T(function(){return B(unCStr("pow("));}),_jd=new T1(0,_jc),_je=new T(function(){return B(unCStr(")"));}),_jf=new T1(0,_je),_jg=new T2(1,_jf,_w),_jh=function(_ji,_jj){return new T1(1,new T2(1,_jd,new T2(1,_ji,new T2(1,_jb,new T2(1,_jj,_jg)))));},_jk=new T(function(){return B(unCStr("acos("));}),_jl=new T1(0,_jk),_jm=function(_jn){return new T1(1,new T2(1,_jl,new T2(1,_jn,_jg)));},_jo=new T(function(){return B(unCStr("acosh("));}),_jp=new T1(0,_jo),_jq=function(_jr){return new T1(1,new T2(1,_jp,new T2(1,_jr,_jg)));},_js=new T(function(){return B(unCStr("asin("));}),_jt=new T1(0,_js),_ju=function(_jv){return new T1(1,new T2(1,_jt,new T2(1,_jv,_jg)));},_jw=new T(function(){return B(unCStr("asinh("));}),_jx=new T1(0,_jw),_jy=function(_jz){return new T1(1,new T2(1,_jx,new T2(1,_jz,_jg)));},_jA=new T(function(){return B(unCStr("atan("));}),_jB=new T1(0,_jA),_jC=function(_jD){return new T1(1,new T2(1,_jB,new T2(1,_jD,_jg)));},_jE=new T(function(){return B(unCStr("atanh("));}),_jF=new T1(0,_jE),_jG=function(_jH){return new T1(1,new T2(1,_jF,new T2(1,_jH,_jg)));},_jI=new T(function(){return B(unCStr("cos("));}),_jJ=new T1(0,_jI),_jK=function(_jL){return new T1(1,new T2(1,_jJ,new T2(1,_jL,_jg)));},_jM=new T(function(){return B(unCStr("cosh("));}),_jN=new T1(0,_jM),_jO=function(_jP){return new T1(1,new T2(1,_jN,new T2(1,_jP,_jg)));},_jQ=new T(function(){return B(unCStr("exp("));}),_jR=new T1(0,_jQ),_jS=function(_jT){return new T1(1,new T2(1,_jR,new T2(1,_jT,_jg)));},_jU=new T(function(){return B(unCStr("log("));}),_jV=new T1(0,_jU),_jW=function(_jX){return new T1(1,new T2(1,_jV,new T2(1,_jX,_jg)));},_jY=new T(function(){return B(unCStr(")/log("));}),_jZ=new T1(0,_jY),_k0=function(_k1,_k2){return new T1(1,new T2(1,_jV,new T2(1,_k2,new T2(1,_jZ,new T2(1,_k1,_jg)))));},_k3=new T(function(){return B(unCStr("pi"));}),_k4=new T1(0,_k3),_k5=new T(function(){return B(unCStr("sin("));}),_k6=new T1(0,_k5),_k7=function(_k8){return new T1(1,new T2(1,_k6,new T2(1,_k8,_jg)));},_k9=new T(function(){return B(unCStr("sinh("));}),_ka=new T1(0,_k9),_kb=function(_kc){return new T1(1,new T2(1,_ka,new T2(1,_kc,_jg)));},_kd=new T(function(){return B(unCStr("sqrt("));}),_ke=new T1(0,_kd),_kf=function(_kg){return new T1(1,new T2(1,_ke,new T2(1,_kg,_jg)));},_kh=new T(function(){return B(unCStr("tan("));}),_ki=new T1(0,_kh),_kj=function(_kk){return new T1(1,new T2(1,_ki,new T2(1,_kk,_jg)));},_kl=new T(function(){return B(unCStr("tanh("));}),_km=new T1(0,_kl),_kn=function(_ko){return new T1(1,new T2(1,_km,new T2(1,_ko,_jg)));},_kp=new T(function(){return B(unCStr("("));}),_kq=new T1(0,_kp),_kr=new T(function(){return B(unCStr(")/("));}),_ks=new T1(0,_kr),_kt=function(_ku,_kv){return new T1(1,new T2(1,_kq,new T2(1,_ku,new T2(1,_ks,new T2(1,_kv,_jg)))));},_kw=function(_kx){return new T1(0,new T(function(){var _ky=E(_kx),_kz=jsShow(B(_6y(_ky.a,_ky.b)));return fromJSStr(_kz);}));},_kA=new T(function(){return B(unCStr("1./("));}),_kB=new T1(0,_kA),_kC=function(_kD){return new T1(1,new T2(1,_kB,new T2(1,_kD,_jg)));},_kE=new T(function(){return B(unCStr(")+("));}),_kF=new T1(0,_kE),_kG=function(_kH,_kI){return new T1(1,new T2(1,_kq,new T2(1,_kH,new T2(1,_kF,new T2(1,_kI,_jg)))));},_kJ=new T(function(){return B(unCStr("-("));}),_kK=new T1(0,_kJ),_kL=function(_kM){return new T1(1,new T2(1,_kK,new T2(1,_kM,_jg)));},_kN=new T(function(){return B(unCStr(")*("));}),_kO=new T1(0,_kN),_kP=function(_kQ,_kR){return new T1(1,new T2(1,_kq,new T2(1,_kQ,new T2(1,_kO,new T2(1,_kR,_jg)))));},_kS=function(_kT,_kU){return new F(function(){return A3(_6X,_kV,_kT,new T(function(){return B(A2(_6Z,_kV,_kU));}));});},_kW=new T(function(){return B(unCStr("abs("));}),_kX=new T1(0,_kW),_kY=function(_kZ){return new T1(1,new T2(1,_kX,new T2(1,_kZ,_jg)));},_l0=new T(function(){return B(unCStr("."));}),_l1=function(_l2){return new T1(0,new T(function(){return B(_n(B(_7i(0,_l2,_w)),_l0));}));},_l3=new T(function(){return B(unCStr("sign("));}),_l4=new T1(0,_l3),_l5=function(_l6){return new T1(1,new T2(1,_l4,new T2(1,_l6,_jg)));},_kV=new T(function(){return {_:0,a:_kG,b:_kS,c:_kP,d:_kL,e:_kY,f:_l5,g:_l1};}),_l7=new T4(0,_kV,_kt,_kC,_kw),_l8={_:0,a:_l7,b:_k4,c:_jS,d:_jW,e:_kf,f:_jh,g:_k0,h:_k7,i:_jK,j:_kj,k:_ju,l:_jm,m:_jC,n:_kb,o:_jO,p:_kn,q:_jy,r:_jq,s:_jG},_l9=new T(function(){return B(unCStr("(/=) is not defined"));}),_la=new T(function(){return B(err(_l9));}),_lb=new T(function(){return B(unCStr("(==) is not defined"));}),_lc=new T(function(){return B(err(_lb));}),_ld=new T2(0,_lc,_la),_le=new T(function(){return B(unCStr("(<) is not defined"));}),_lf=new T(function(){return B(err(_le));}),_lg=new T(function(){return B(unCStr("(<=) is not defined"));}),_lh=new T(function(){return B(err(_lg));}),_li=new T(function(){return B(unCStr("(>) is not defined"));}),_lj=new T(function(){return B(err(_li));}),_lk=new T(function(){return B(unCStr("(>=) is not defined"));}),_ll=new T(function(){return B(err(_lk));}),_lm=new T(function(){return B(unCStr("compare is not defined"));}),_ln=new T(function(){return B(err(_lm));}),_lo=new T(function(){return B(unCStr("max("));}),_lp=new T1(0,_lo),_lq=function(_lr,_ls){return new T1(1,new T2(1,_lp,new T2(1,_lr,new T2(1,_jb,new T2(1,_ls,_jg)))));},_lt=new T(function(){return B(unCStr("min("));}),_lu=new T1(0,_lt),_lv=function(_lw,_lx){return new T1(1,new T2(1,_lu,new T2(1,_lw,new T2(1,_jb,new T2(1,_lx,_jg)))));},_ly={_:0,a:_ld,b:_ln,c:_lf,d:_lh,e:_lj,f:_ll,g:_lq,h:_lv},_lz=new T2(0,_l8,_ly),_lA=new T(function(){return B(_hT(_lz));}),_lB=new T(function(){return B(A1(_lA,_j9));}),_lC=new T(function(){return toJSStr(B(_iT(_x,_iN,_lB)));}),_lD=new T(function(){return eval("__strict(compile)");}),_lE=new T(function(){return toJSStr(E(_j5));}),_lF=function(_lG,_lH,_lI){var _lJ=new T(function(){return B(_0(_lG));}),_lK=new T(function(){return B(_2(_lG));}),_lL=function(_lM){var _lN=E(_lM);if(!_lN._){return E(_lK);}else{return new F(function(){return A2(_lJ,new T(function(){return B(_iT(_lG,_lH,_lN.a));}),new T(function(){return B(_lL(_lN.b));}));});}};return new F(function(){return _lL(_lI);});},_lO=new T(function(){return B(unCStr("vec3("));}),_lP=new T1(0,_lO),_lQ=new T(function(){return B(_7i(0,_8r,_w));}),_lR=new T(function(){return B(_n(_lQ,_l0));}),_lS=new T1(0,_lR),_lT=new T(function(){return B(_7i(0,_8q,_w));}),_lU=new T(function(){return B(_n(_lT,_l0));}),_lV=new T1(0,_lU),_lW=new T2(1,_lV,_w),_lX=new T2(1,_lS,_lW),_lY=function(_lZ,_m0){var _m1=E(_m0);return (_m1._==0)?__Z:new T2(1,_lZ,new T2(1,_m1.a,new T(function(){return B(_lY(_lZ,_m1.b));})));},_m2=new T(function(){return B(_lY(_jb,_lX));}),_m3=new T2(1,_lV,_m2),_m4=new T1(1,_m3),_m5=new T2(1,_m4,_jg),_m6=new T2(1,_lP,_m5),_m7=new T(function(){return toJSStr(B(_lF(_x,_iN,_m6)));}),_m8=function(_m9,_ma){while(1){var _mb=E(_m9);if(!_mb._){return E(_ma);}else{var _mc=_ma+1|0;_m9=_mb.b;_ma=_mc;continue;}}},_md=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_me=new T(function(){return B(err(_md));}),_mf=0,_mg=new T3(0,E(_mf),E(_mf),E(_mf)),_mh=new T(function(){return B(unCStr("Negative exponent"));}),_mi=new T(function(){return B(err(_mh));}),_mj=function(_mk,_ml,_mm){while(1){if(!(_ml%2)){var _mn=_mk*_mk,_mo=quot(_ml,2);_mk=_mn;_ml=_mo;continue;}else{var _mp=E(_ml);if(_mp==1){return _mk*_mm;}else{var _mn=_mk*_mk,_mq=_mk*_mm;_mk=_mn;_ml=quot(_mp-1|0,2);_mm=_mq;continue;}}}},_mr=function(_ms,_mt){while(1){if(!(_mt%2)){var _mu=_ms*_ms,_mv=quot(_mt,2);_ms=_mu;_mt=_mv;continue;}else{var _mw=E(_mt);if(_mw==1){return E(_ms);}else{return new F(function(){return _mj(_ms*_ms,quot(_mw-1|0,2),_ms);});}}}},_mx=function(_my){var _mz=E(_my);return new F(function(){return Math.log(_mz+(_mz+1)*Math.sqrt((_mz-1)/(_mz+1)));});},_mA=function(_mB){var _mC=E(_mB);return new F(function(){return Math.log(_mC+Math.sqrt(1+_mC*_mC));});},_mD=function(_mE){var _mF=E(_mE);return 0.5*Math.log((1+_mF)/(1-_mF));},_mG=function(_mH,_mI){return Math.log(E(_mI))/Math.log(E(_mH));},_mJ=3.141592653589793,_mK=function(_mL){var _mM=E(_mL);return new F(function(){return _6y(_mM.a,_mM.b);});},_mN=function(_mO){return 1/E(_mO);},_mP=function(_mQ){var _mR=E(_mQ),_mS=E(_mR);return (_mS==0)?E(_6x):(_mS<=0)? -_mS:E(_mR);},_mT=function(_mU){var _mV=E(_mU);if(!_mV._){return _mV.a;}else{return new F(function(){return I_toNumber(_mV.a);});}},_mW=function(_mX){return new F(function(){return _mT(_mX);});},_mY=1,_mZ=-1,_n0=function(_n1){var _n2=E(_n1);return (_n2<=0)?(_n2>=0)?E(_n2):E(_mZ):E(_mY);},_n3=function(_n4,_n5){return E(_n4)-E(_n5);},_n6=function(_n7){return  -E(_n7);},_n8=function(_n9,_na){return E(_n9)+E(_na);},_nb=function(_nc,_nd){return E(_nc)*E(_nd);},_ne={_:0,a:_n8,b:_n3,c:_nb,d:_n6,e:_mP,f:_n0,g:_mW},_nf=function(_ng,_nh){return E(_ng)/E(_nh);},_ni=new T4(0,_ne,_nf,_mN,_mK),_nj=function(_nk){return new F(function(){return Math.acos(E(_nk));});},_nl=function(_nm){return new F(function(){return Math.asin(E(_nm));});},_nn=function(_no){return new F(function(){return Math.atan(E(_no));});},_np=function(_nq){return new F(function(){return Math.cos(E(_nq));});},_nr=function(_ns){return new F(function(){return cosh(E(_ns));});},_nt=function(_nu){return new F(function(){return Math.exp(E(_nu));});},_nv=function(_nw){return new F(function(){return Math.log(E(_nw));});},_nx=function(_ny,_nz){return new F(function(){return Math.pow(E(_ny),E(_nz));});},_nA=function(_nB){return new F(function(){return Math.sin(E(_nB));});},_nC=function(_nD){return new F(function(){return sinh(E(_nD));});},_nE=function(_nF){return new F(function(){return Math.sqrt(E(_nF));});},_nG=function(_nH){return new F(function(){return Math.tan(E(_nH));});},_nI=function(_nJ){return new F(function(){return tanh(E(_nJ));});},_nK={_:0,a:_ni,b:_mJ,c:_nt,d:_nv,e:_nE,f:_nx,g:_mG,h:_nA,i:_np,j:_nG,k:_nl,l:_nj,m:_nn,n:_nC,o:_nr,p:_nI,q:_mA,r:_mx,s:_mD},_nL=function(_nM,_nN){return (E(_nM)!=E(_nN))?true:false;},_nO=function(_nP,_nQ){return E(_nP)==E(_nQ);},_nR=new T2(0,_nO,_nL),_nS=function(_nT,_nU){return E(_nT)<E(_nU);},_nV=function(_nW,_nX){return E(_nW)<=E(_nX);},_nY=function(_nZ,_o0){return E(_nZ)>E(_o0);},_o1=function(_o2,_o3){return E(_o2)>=E(_o3);},_o4=function(_o5,_o6){var _o7=E(_o5),_o8=E(_o6);return (_o7>=_o8)?(_o7!=_o8)?2:1:0;},_o9=function(_oa,_ob){var _oc=E(_oa),_od=E(_ob);return (_oc>_od)?E(_oc):E(_od);},_oe=function(_of,_og){var _oh=E(_of),_oi=E(_og);return (_oh>_oi)?E(_oi):E(_oh);},_oj={_:0,a:_nR,b:_o4,c:_nS,d:_nV,e:_nY,f:_o1,g:_o9,h:_oe},_ok="dz",_ol="wy",_om="wx",_on="dy",_oo="dx",_op="t",_oq="a",_or="r",_os="ly",_ot="lx",_ou="wz",_ov=0,_ow=function(_ox){var _oy=__new(),_oz=_oy,_oA=function(_oB,_){while(1){var _oC=E(_oB);if(!_oC._){return _ov;}else{var _oD=E(_oC.a),_oE=__set(_oz,E(_oD.a),E(_oD.b));_oB=_oC.b;continue;}}},_oF=B(_oA(_ox,_));return E(_oz);},_oG=function(_oH,_oI,_oJ,_oK,_oL,_oM,_oN,_oO,_oP){return new F(function(){return _ow(new T2(1,new T2(0,_om,_oH),new T2(1,new T2(0,_ol,_oI),new T2(1,new T2(0,_ou,_oJ),new T2(1,new T2(0,_ot,_oK*_oL*Math.cos(_oM)),new T2(1,new T2(0,_os,_oK*_oL*Math.sin(_oM)),new T2(1,new T2(0,_or,_oK),new T2(1,new T2(0,_oq,_oL),new T2(1,new T2(0,_op,_oM),new T2(1,new T2(0,_oo,_oN),new T2(1,new T2(0,_on,_oO),new T2(1,new T2(0,_ok,_oP),_w))))))))))));});},_oQ=function(_oR){var _oS=E(_oR),_oT=E(_oS.a),_oU=E(_oS.b),_oV=E(_oS.d);return new F(function(){return _oG(_oT.a,_oT.b,_oT.c,E(_oU.a),E(_oU.b),E(_oS.c),_oV.a,_oV.b,_oV.c);});},_oW=function(_oX,_oY){var _oZ=E(_oY);return (_oZ._==0)?__Z:new T2(1,new T(function(){return B(A1(_oX,_oZ.a));}),new T(function(){return B(_oW(_oX,_oZ.b));}));},_p0=function(_p1,_p2,_p3){var _p4=__lst2arr(B(_oW(_oQ,new T2(1,_p1,new T2(1,_p2,new T2(1,_p3,_w))))));return E(_p4);},_p5=function(_p6){var _p7=E(_p6);return new F(function(){return _p0(_p7.a,_p7.b,_p7.c);});},_p8=new T2(0,_nK,_oj),_p9=function(_pa,_pb,_pc,_pd,_pe,_pf,_pg){var _ph=B(_8J(B(_8H(_pa)))),_pi=new T(function(){return B(A3(_6X,_ph,new T(function(){return B(A3(_8L,_ph,_pb,_pe));}),new T(function(){return B(A3(_8L,_ph,_pc,_pf));})));});return new F(function(){return A3(_6X,_ph,_pi,new T(function(){return B(A3(_8L,_ph,_pd,_pg));}));});},_pj=function(_pk,_pl,_pm,_pn){var _po=B(_8H(_pk)),_pp=new T(function(){return B(A2(_9t,_pk,new T(function(){return B(_p9(_pk,_pl,_pm,_pn,_pl,_pm,_pn));})));});return new T3(0,B(A3(_8P,_po,_pl,_pp)),B(A3(_8P,_po,_pm,_pp)),B(A3(_8P,_po,_pn,_pp)));},_pq=function(_pr,_ps,_pt,_pu,_pv,_pw,_px){var _py=B(_8L(_pr));return new T3(0,B(A1(B(A1(_py,_ps)),_pv)),B(A1(B(A1(_py,_pt)),_pw)),B(A1(B(A1(_py,_pu)),_px)));},_pz=function(_pA,_pB,_pC,_pD,_pE,_pF,_pG){var _pH=B(_6X(_pA));return new T3(0,B(A1(B(A1(_pH,_pB)),_pE)),B(A1(B(A1(_pH,_pC)),_pF)),B(A1(B(A1(_pH,_pD)),_pG)));},_pI=function(_pJ,_pK){var _pL=new T(function(){return E(E(_pJ).a);}),_pM=new T(function(){var _pN=E(_pK),_pO=new T(function(){return B(_8J(new T(function(){return B(_8H(_pL));})));}),_pP=B(A2(_8s,_pO,_8q));return new T3(0,E(_pP),E(B(A2(_8s,_pO,_8r))),E(_pP));}),_pQ=new T(function(){var _pR=E(_pM),_pS=B(_pj(_pL,_pR.a,_pR.b,_pR.c));return new T3(0,E(_pS.a),E(_pS.b),E(_pS.c));}),_pT=new T(function(){var _pU=E(_pK),_pV=_pU.b,_pW=E(_pQ),_pX=B(_8H(_pL)),_pY=new T(function(){return B(A2(_9t,_pL,new T(function(){var _pZ=E(_pM),_q0=_pZ.a,_q1=_pZ.b,_q2=_pZ.c;return B(_p9(_pL,_q0,_q1,_q2,_q0,_q1,_q2));})));}),_q3=B(A3(_8P,_pX,_pV,_pY)),_q4=B(_8J(_pX)),_q5=B(_pq(_q4,_pW.a,_pW.b,_pW.c,_q3,_q3,_q3)),_q6=B(_6Z(_q4)),_q7=B(_pz(_q4,_pU.a,_pV,_pU.c,B(A1(_q6,_q5.a)),B(A1(_q6,_q5.b)),B(A1(_q6,_q5.c))));return new T3(0,E(_q7.a),E(_q7.b),E(_q7.c));});return new T2(0,_pT,_pQ);},_q8=function(_q9){return E(E(_q9).a);},_qa=function(_qb,_qc,_qd,_qe,_qf,_qg,_qh){var _qi=B(_p9(_qb,_qf,_qg,_qh,_qc,_qd,_qe)),_qj=B(_8J(B(_8H(_qb)))),_qk=B(_pq(_qj,_qf,_qg,_qh,_qi,_qi,_qi)),_ql=B(_6Z(_qj));return new F(function(){return _pz(_qj,_qc,_qd,_qe,B(A1(_ql,_qk.a)),B(A1(_ql,_qk.b)),B(A1(_ql,_qk.c)));});},_qm=function(_qn){return E(E(_qn).a);},_qo=function(_qp,_qq,_qr,_qs){var _qt=new T(function(){var _qu=E(_qs),_qv=E(_qr),_qw=B(_qa(_qp,_qu.a,_qu.b,_qu.c,_qv.a,_qv.b,_qv.c));return new T3(0,E(_qw.a),E(_qw.b),E(_qw.c));}),_qx=new T(function(){return B(A2(_9t,_qp,new T(function(){var _qy=E(_qt),_qz=_qy.a,_qA=_qy.b,_qB=_qy.c;return B(_p9(_qp,_qz,_qA,_qB,_qz,_qA,_qB));})));});if(!B(A3(_qm,B(_q8(_qq)),_qx,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_qp)))),_8q));})))){var _qC=E(_qt),_qD=B(_pj(_qp,_qC.a,_qC.b,_qC.c)),_qE=B(A2(_9t,_qp,new T(function(){var _qF=E(_qs),_qG=_qF.a,_qH=_qF.b,_qI=_qF.c;return B(_p9(_qp,_qG,_qH,_qI,_qG,_qH,_qI));}))),_qJ=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_qp));})));})));return new T3(0,B(A1(B(A1(_qJ,_qD.a)),_qE)),B(A1(B(A1(_qJ,_qD.b)),_qE)),B(A1(B(A1(_qJ,_qD.c)),_qE)));}else{var _qK=B(A2(_8s,B(_8J(B(_8H(_qp)))),_8q));return new T3(0,_qK,_qK,_qK);}},_qL=function(_qM,_qN){while(1){var _qO=E(_qM);if(!_qO._){return E(_qN);}else{var _qP=_qO.b,_qQ=E(_qO.a);if(_qN>_qQ){_qM=_qP;continue;}else{_qM=_qP;_qN=_qQ;continue;}}}},_qR=new T(function(){var _qS=eval("angleCount"),_qT=Number(_qS);return jsTrunc(_qT);}),_qU=new T(function(){return E(_qR);}),_qV=new T(function(){return B(unCStr(": empty list"));}),_qW=new T(function(){return B(unCStr("Prelude."));}),_qX=function(_qY){return new F(function(){return err(B(_n(_qW,new T(function(){return B(_n(_qY,_qV));},1))));});},_qZ=new T(function(){return B(unCStr("head"));}),_r0=new T(function(){return B(_qX(_qZ));}),_r1=function(_r2,_r3,_r4){var _r5=E(_r2);if(!_r5._){return __Z;}else{var _r6=E(_r3);if(!_r6._){return __Z;}else{var _r7=_r6.a,_r8=E(_r4);if(!_r8._){return __Z;}else{var _r9=E(_r8.a),_ra=_r9.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_r5.a),E(_r7),E(_ra));}),new T2(1,new T(function(){return new T3(0,E(_r7),E(_ra),E(_r9.b));}),_w)),new T(function(){return B(_r1(_r5.b,_r6.b,_r8.b));},1));});}}}},_rb=new T(function(){return B(unCStr("tail"));}),_rc=new T(function(){return B(_qX(_rb));}),_rd=function(_re,_rf){var _rg=E(_re);if(!_rg._){return __Z;}else{var _rh=E(_rf);return (_rh._==0)?__Z:new T2(1,new T2(0,_rg.a,_rh.a),new T(function(){return B(_rd(_rg.b,_rh.b));}));}},_ri=function(_rj,_rk){var _rl=E(_rj);if(!_rl._){return __Z;}else{var _rm=E(_rk);if(!_rm._){return __Z;}else{var _rn=E(_rl.a),_ro=_rn.b,_rp=E(_rm.a).b,_rq=new T(function(){var _rr=new T(function(){return B(_rd(_rp,new T(function(){var _rs=E(_rp);if(!_rs._){return E(_rc);}else{return E(_rs.b);}},1)));},1);return B(_r1(_ro,new T(function(){var _rt=E(_ro);if(!_rt._){return E(_rc);}else{return E(_rt.b);}},1),_rr));});return new F(function(){return _n(new T2(1,new T(function(){var _ru=E(_ro);if(!_ru._){return E(_r0);}else{var _rv=E(_rp);if(!_rv._){return E(_r0);}else{return new T3(0,E(_rn.a),E(_ru.a),E(_rv.a));}}}),_rq),new T(function(){return B(_ri(_rl.b,_rm.b));},1));});}}},_rw=new T(function(){return 6.283185307179586/E(_qU);}),_rx=new T(function(){return E(_qU)-1;}),_ry=new T1(0,1),_rz=function(_rA,_rB){var _rC=E(_rB),_rD=new T(function(){var _rE=B(_8J(_rA)),_rF=B(_rz(_rA,B(A3(_6X,_rE,_rC,new T(function(){return B(A2(_8s,_rE,_ry));})))));return new T2(1,_rF.a,_rF.b);});return new T2(0,_rC,_rD);},_rG=function(_rH){return E(E(_rH).d);},_rI=new T1(0,2),_rJ=function(_rK,_rL){var _rM=E(_rL);if(!_rM._){return __Z;}else{var _rN=_rM.a;return (!B(A1(_rK,_rN)))?__Z:new T2(1,_rN,new T(function(){return B(_rJ(_rK,_rM.b));}));}},_rO=function(_rP,_rQ,_rR,_rS){var _rT=B(_rz(_rQ,_rR)),_rU=new T(function(){var _rV=B(_8J(_rQ)),_rW=new T(function(){return B(A3(_8P,_rQ,new T(function(){return B(A2(_8s,_rV,_ry));}),new T(function(){return B(A2(_8s,_rV,_rI));})));});return B(A3(_6X,_rV,_rS,_rW));});return new F(function(){return _rJ(function(_rX){return new F(function(){return A3(_rG,_rP,_rX,_rU);});},new T2(1,_rT.a,_rT.b));});},_rY=new T(function(){return B(_rO(_oj,_ni,_mf,_rx));}),_rZ=function(_s0,_s1){while(1){var _s2=E(_s0);if(!_s2._){return E(_s1);}else{_s0=_s2.b;_s1=_s2.a;continue;}}},_s3=new T(function(){return B(unCStr("last"));}),_s4=new T(function(){return B(_qX(_s3));}),_s5=function(_s6){return new F(function(){return _rZ(_s6,_s4);});},_s7=function(_s8){return new F(function(){return _s5(E(_s8).b);});},_s9=new T(function(){return B(unCStr("maximum"));}),_sa=new T(function(){return B(_qX(_s9));}),_sb=new T(function(){var _sc=eval("proceedCount"),_sd=Number(_sc);return jsTrunc(_sd);}),_se=new T(function(){return E(_sb);}),_sf=1,_sg=new T(function(){return B(_rO(_oj,_ni,_sf,_se));}),_sh=function(_si,_sj,_sk,_sl,_sm,_sn,_so,_sp,_sq,_sr,_ss,_st,_su,_sv){var _sw=new T(function(){var _sx=new T(function(){var _sy=E(_sr),_sz=E(_sv),_sA=E(_su),_sB=E(_ss),_sC=E(_st),_sD=E(_sq);return new T3(0,_sy*_sz-_sA*_sB,_sB*_sC-_sz*_sD,_sD*_sA-_sC*_sy);}),_sE=function(_sF){var _sG=new T(function(){var _sH=E(_sF)/E(_qU);return (_sH+_sH)*3.141592653589793;}),_sI=new T(function(){return B(A1(_si,_sG));}),_sJ=new T(function(){var _sK=new T(function(){var _sL=E(_sI)/E(_se);return new T3(0,E(_sL),E(_sL),E(_sL));}),_sM=function(_sN,_sO){var _sP=E(_sN);if(!_sP._){return new T2(0,_w,_sO);}else{var _sQ=new T(function(){var _sR=B(_pI(_p8,new T(function(){var _sS=E(_sO),_sT=E(_sS.a),_sU=E(_sS.b),_sV=E(_sK);return new T3(0,E(_sT.a)+E(_sU.a)*E(_sV.a),E(_sT.b)+E(_sU.b)*E(_sV.b),E(_sT.c)+E(_sU.c)*E(_sV.c));}))),_sW=_sR.a,_sX=new T(function(){var _sY=E(_sR.b),_sZ=E(E(_sO).b),_t0=B(_qa(_nK,_sZ.a,_sZ.b,_sZ.c,_sY.a,_sY.b,_sY.c)),_t1=B(_pj(_nK,_t0.a,_t0.b,_t0.c));return new T3(0,E(_t1.a),E(_t1.b),E(_t1.c));});return new T2(0,new T(function(){var _t2=E(_sI),_t3=E(_sG);return new T4(0,E(_sW),E(new T2(0,E(_sP.a)/E(_se),E(_t2))),E(_t3),E(_sX));}),new T2(0,_sW,_sX));}),_t4=new T(function(){var _t5=B(_sM(_sP.b,new T(function(){return E(E(_sQ).b);})));return new T2(0,_t5.a,_t5.b);});return new T2(0,new T2(1,new T(function(){return E(E(_sQ).a);}),new T(function(){return E(E(_t4).a);})),new T(function(){return E(E(_t4).b);}));}},_t6=function(_t7,_t8,_t9,_ta,_tb){var _tc=E(_t7);if(!_tc._){return new T2(0,_w,new T2(0,new T3(0,E(_t8),E(_t9),E(_ta)),_tb));}else{var _td=new T(function(){var _te=B(_pI(_p8,new T(function(){var _tf=E(_tb),_tg=E(_sK);return new T3(0,E(_t8)+E(_tf.a)*E(_tg.a),E(_t9)+E(_tf.b)*E(_tg.b),E(_ta)+E(_tf.c)*E(_tg.c));}))),_th=_te.a,_ti=new T(function(){var _tj=E(_te.b),_tk=E(_tb),_tl=B(_qa(_nK,_tk.a,_tk.b,_tk.c,_tj.a,_tj.b,_tj.c)),_tm=B(_pj(_nK,_tl.a,_tl.b,_tl.c));return new T3(0,E(_tm.a),E(_tm.b),E(_tm.c));});return new T2(0,new T(function(){var _tn=E(_sI),_to=E(_sG);return new T4(0,E(_th),E(new T2(0,E(_tc.a)/E(_se),E(_tn))),E(_to),E(_ti));}),new T2(0,_th,_ti));}),_tp=new T(function(){var _tq=B(_sM(_tc.b,new T(function(){return E(E(_td).b);})));return new T2(0,_tq.a,_tq.b);});return new T2(0,new T2(1,new T(function(){return E(E(_td).a);}),new T(function(){return E(E(_tp).a);})),new T(function(){return E(E(_tp).b);}));}};return E(B(_t6(_sg,_sl,_sm,_sn,new T(function(){var _tr=E(_sx),_ts=E(_sG)+_so,_tt=Math.cos(_ts),_tu=Math.sin(_ts);return new T3(0,E(_sq)*_tt+E(_tr.a)*_tu,E(_sr)*_tt+E(_tr.b)*_tu,E(_ss)*_tt+E(_tr.c)*_tu);}))).a);});return new T2(0,new T(function(){var _tv=E(_sI),_tw=E(_sG);return new T4(0,E(new T3(0,E(_sl),E(_sm),E(_sn))),E(new T2(0,E(_mf),E(_tv))),E(_tw),E(_mg));}),_sJ);};return B(_oW(_sE,_rY));}),_tx=new T(function(){var _ty=function(_tz){return new F(function(){return A1(_si,new T(function(){return B(_nb(_tz,_rw));}));});},_tA=B(_oW(_ty,_rY));if(!_tA._){return E(_sa);}else{return B(_qL(_tA.b,E(_tA.a)));}}),_tB=new T(function(){var _tC=new T(function(){var _tD=B(_n(_sw,new T2(1,new T(function(){var _tE=E(_sw);if(!_tE._){return E(_r0);}else{return E(_tE.a);}}),_w)));if(!_tD._){return E(_rc);}else{return E(_tD.b);}},1);return B(_ri(_sw,_tC));});return new T3(0,_tB,new T(function(){return B(_oW(_s7,_sw));}),_tx);},_tF=function(_tG,_tH,_tI,_tJ,_tK,_tL,_tM,_tN,_tO,_tP,_tQ,_tR,_tS,_tT,_tU,_tV,_tW,_tX){var _tY=B(_pI(_p8,new T3(0,E(_tJ),E(_tK),E(_tL)))),_tZ=_tY.b,_u0=E(_tY.a),_u1=B(_qo(_nK,_oj,_tZ,new T3(0,E(_tN),E(_tO),E(_tP)))),_u2=E(_tZ),_u3=_u2.a,_u4=_u2.b,_u5=_u2.c,_u6=B(_qa(_nK,_tR,_tS,_tT,_u3,_u4,_u5)),_u7=B(_pj(_nK,_u6.a,_u6.b,_u6.c)),_u8=_u7.a,_u9=_u7.b,_ua=_u7.c,_ub=E(_tM),_uc=new T2(0,E(new T3(0,E(_u1.a),E(_u1.b),E(_u1.c))),E(_tQ)),_ud=B(_sh(_tG,_tH,_tI,_u0.a,_u0.b,_u0.c,_ub,_uc,_u8,_u9,_ua,_u3,_u4,_u5)),_ue=__lst2arr(B(_oW(_p5,_ud.a))),_uf=__lst2arr(B(_oW(_oQ,_ud.b)));return {_:0,a:_tG,b:_tH,c:_tI,d:new T2(0,E(_u0),E(_ub)),e:_uc,f:new T3(0,E(_u8),E(_u9),E(_ua)),g:_u2,h:_ue,i:_uf,j:E(_ud.c)};},_ug=-4,_uh=new T3(0,E(_mf),E(_mf),E(_ug)),_ui=function(_uj){return E(_uh);},_uk=function(_){return new F(function(){return __jsNull();});},_ul=function(_um){var _un=B(A1(_um,_));return E(_un);},_uo=new T(function(){return B(_ul(_uk));}),_up=function(_uq,_ur,_us,_ut,_uu,_uv,_uw,_ux,_uy,_uz,_uA,_uB,_uC){var _uD=function(_uE){var _uF=E(_rw),_uG=2+_uE|0,_uH=_uG-1|0,_uI=(2+_uE)*(1+_uE),_uJ=E(_rY);if(!_uJ._){return _uF*0;}else{var _uK=_uJ.a,_uL=_uJ.b,_uM=B(A1(_uq,new T(function(){return 6.283185307179586*E(_uK)/E(_qU);}))),_uN=B(A1(_uq,new T(function(){return 6.283185307179586*(E(_uK)+1)/E(_qU);})));if(_uM!=_uN){if(_uG>=0){var _uO=E(_uG);if(!_uO){var _uP=function(_uQ,_uR){while(1){var _uS=B((function(_uT,_uU){var _uV=E(_uT);if(!_uV._){return E(_uU);}else{var _uW=_uV.a,_uX=_uV.b,_uY=B(A1(_uq,new T(function(){return 6.283185307179586*E(_uW)/E(_qU);}))),_uZ=B(A1(_uq,new T(function(){return 6.283185307179586*(E(_uW)+1)/E(_qU);})));if(_uY!=_uZ){var _v0=_uU+0/(_uY-_uZ)/_uI;_uQ=_uX;_uR=_v0;return __continue;}else{if(_uH>=0){var _v1=E(_uH);if(!_v1){var _v0=_uU+_uG/_uI;_uQ=_uX;_uR=_v0;return __continue;}else{var _v0=_uU+_uG*B(_mr(_uY,_v1))/_uI;_uQ=_uX;_uR=_v0;return __continue;}}else{return E(_mi);}}}})(_uQ,_uR));if(_uS!=__continue){return _uS;}}};return _uF*B(_uP(_uL,0/(_uM-_uN)/_uI));}else{var _v2=function(_v3,_v4){while(1){var _v5=B((function(_v6,_v7){var _v8=E(_v6);if(!_v8._){return E(_v7);}else{var _v9=_v8.a,_va=_v8.b,_vb=B(A1(_uq,new T(function(){return 6.283185307179586*E(_v9)/E(_qU);}))),_vc=B(A1(_uq,new T(function(){return 6.283185307179586*(E(_v9)+1)/E(_qU);})));if(_vb!=_vc){if(_uO>=0){var _vd=_v7+(B(_mr(_vb,_uO))-B(_mr(_vc,_uO)))/(_vb-_vc)/_uI;_v3=_va;_v4=_vd;return __continue;}else{return E(_mi);}}else{if(_uH>=0){var _ve=E(_uH);if(!_ve){var _vd=_v7+_uG/_uI;_v3=_va;_v4=_vd;return __continue;}else{var _vd=_v7+_uG*B(_mr(_vb,_ve))/_uI;_v3=_va;_v4=_vd;return __continue;}}else{return E(_mi);}}}})(_v3,_v4));if(_v5!=__continue){return _v5;}}};return _uF*B(_v2(_uL,(B(_mr(_uM,_uO))-B(_mr(_uN,_uO)))/(_uM-_uN)/_uI));}}else{return E(_mi);}}else{if(_uH>=0){var _vf=E(_uH);if(!_vf){var _vg=function(_vh,_vi){while(1){var _vj=B((function(_vk,_vl){var _vm=E(_vk);if(!_vm._){return E(_vl);}else{var _vn=_vm.a,_vo=_vm.b,_vp=B(A1(_uq,new T(function(){return 6.283185307179586*E(_vn)/E(_qU);}))),_vq=B(A1(_uq,new T(function(){return 6.283185307179586*(E(_vn)+1)/E(_qU);})));if(_vp!=_vq){if(_uG>=0){var _vr=E(_uG);if(!_vr){var _vs=_vl+0/(_vp-_vq)/_uI;_vh=_vo;_vi=_vs;return __continue;}else{var _vs=_vl+(B(_mr(_vp,_vr))-B(_mr(_vq,_vr)))/(_vp-_vq)/_uI;_vh=_vo;_vi=_vs;return __continue;}}else{return E(_mi);}}else{var _vs=_vl+_uG/_uI;_vh=_vo;_vi=_vs;return __continue;}}})(_vh,_vi));if(_vj!=__continue){return _vj;}}};return _uF*B(_vg(_uL,_uG/_uI));}else{var _vt=function(_vu,_vv){while(1){var _vw=B((function(_vx,_vy){var _vz=E(_vx);if(!_vz._){return E(_vy);}else{var _vA=_vz.a,_vB=_vz.b,_vC=B(A1(_uq,new T(function(){return 6.283185307179586*E(_vA)/E(_qU);}))),_vD=B(A1(_uq,new T(function(){return 6.283185307179586*(E(_vA)+1)/E(_qU);})));if(_vC!=_vD){if(_uG>=0){var _vE=E(_uG);if(!_vE){var _vF=_vy+0/(_vC-_vD)/_uI;_vu=_vB;_vv=_vF;return __continue;}else{var _vF=_vy+(B(_mr(_vC,_vE))-B(_mr(_vD,_vE)))/(_vC-_vD)/_uI;_vu=_vB;_vv=_vF;return __continue;}}else{return E(_mi);}}else{if(_vf>=0){var _vF=_vy+_uG*B(_mr(_vC,_vf))/_uI;_vu=_vB;_vv=_vF;return __continue;}else{return E(_mi);}}}})(_vu,_vv));if(_vw!=__continue){return _vw;}}};return _uF*B(_vt(_uL,_uG*B(_mr(_uM,_vf))/_uI));}}else{return E(_mi);}}}},_vG=E(_uo),_vH=1/(B(_uD(1))*_ur);return new F(function(){return _tF(_uq,_ui,new T2(0,E(new T3(0,E(_vH),E(_vH),E(_vH))),1/(B(_uD(3))*_ur)),_us,_ut,_uu,_uv,_uw,_ux,_uy,_uz,_uA,_uB,_uC,_mg,_vG,_vG,0);});},_vI=1,_vJ=function(_vK){var _vL=I_decodeDouble(_vK);return new T2(0,new T1(1,_vL.b),_vL.a);},_vM=function(_vN){return new T1(0,_vN);},_vO=function(_vP){var _vQ=hs_intToInt64(2147483647),_vR=hs_leInt64(_vP,_vQ);if(!_vR){return new T1(1,I_fromInt64(_vP));}else{var _vS=hs_intToInt64(-2147483648),_vT=hs_geInt64(_vP,_vS);if(!_vT){return new T1(1,I_fromInt64(_vP));}else{var _vU=hs_int64ToInt(_vP);return new F(function(){return _vM(_vU);});}}},_vV=new T(function(){var _vW=newByteArr(256),_vX=_vW,_=_vX["v"]["i8"][0]=8,_vY=function(_vZ,_w0,_w1,_){while(1){if(_w1>=256){if(_vZ>=256){return E(_);}else{var _w2=imul(2,_vZ)|0,_w3=_w0+1|0,_w4=_vZ;_vZ=_w2;_w0=_w3;_w1=_w4;continue;}}else{var _=_vX["v"]["i8"][_w1]=_w0,_w4=_w1+_vZ|0;_w1=_w4;continue;}}},_=B(_vY(2,0,1,_));return _vX;}),_w5=function(_w6,_w7){var _w8=hs_int64ToInt(_w6),_w9=E(_vV),_wa=_w9["v"]["i8"][(255&_w8>>>0)>>>0&4294967295];if(_w7>_wa){if(_wa>=8){var _wb=hs_uncheckedIShiftRA64(_w6,8),_wc=function(_wd,_we){while(1){var _wf=B((function(_wg,_wh){var _wi=hs_int64ToInt(_wg),_wj=_w9["v"]["i8"][(255&_wi>>>0)>>>0&4294967295];if(_wh>_wj){if(_wj>=8){var _wk=hs_uncheckedIShiftRA64(_wg,8),_wl=_wh-8|0;_wd=_wk;_we=_wl;return __continue;}else{return new T2(0,new T(function(){var _wm=hs_uncheckedIShiftRA64(_wg,_wj);return B(_vO(_wm));}),_wh-_wj|0);}}else{return new T2(0,new T(function(){var _wn=hs_uncheckedIShiftRA64(_wg,_wh);return B(_vO(_wn));}),0);}})(_wd,_we));if(_wf!=__continue){return _wf;}}};return new F(function(){return _wc(_wb,_w7-8|0);});}else{return new T2(0,new T(function(){var _wo=hs_uncheckedIShiftRA64(_w6,_wa);return B(_vO(_wo));}),_w7-_wa|0);}}else{return new T2(0,new T(function(){var _wp=hs_uncheckedIShiftRA64(_w6,_w7);return B(_vO(_wp));}),0);}},_wq=function(_wr){var _ws=hs_intToInt64(_wr);return E(_ws);},_wt=function(_wu){var _wv=E(_wu);if(!_wv._){return new F(function(){return _wq(_wv.a);});}else{return new F(function(){return I_toInt64(_wv.a);});}},_ww=function(_wx){return I_toInt(_wx)>>>0;},_wy=function(_wz){var _wA=E(_wz);if(!_wA._){return _wA.a>>>0;}else{return new F(function(){return _ww(_wA.a);});}},_wB=function(_wC){var _wD=B(_vJ(_wC)),_wE=_wD.a,_wF=_wD.b;if(_wF<0){var _wG=function(_wH){if(!_wH){return new T2(0,E(_wE),B(_3J(_21, -_wF)));}else{var _wI=B(_w5(B(_wt(_wE)), -_wF));return new T2(0,E(_wI.a),B(_3J(_21,_wI.b)));}};if(!((B(_wy(_wE))&1)>>>0)){return new F(function(){return _wG(1);});}else{return new F(function(){return _wG(0);});}}else{return new T2(0,B(_3J(_wE,_wF)),_21);}},_wJ=function(_wK){var _wL=B(_wB(E(_wK)));return new T2(0,E(_wL.a),E(_wL.b));},_wM=new T3(0,_ne,_oj,_wJ),_wN=function(_wO){return E(E(_wO).a);},_wP=function(_wQ){return E(E(_wQ).a);},_wR=function(_wS,_wT){if(_wS<=_wT){var _wU=function(_wV){return new T2(1,_wV,new T(function(){if(_wV!=_wT){return B(_wU(_wV+1|0));}else{return __Z;}}));};return new F(function(){return _wU(_wS);});}else{return __Z;}},_wW=function(_wX){return new F(function(){return _wR(E(_wX),2147483647);});},_wY=function(_wZ,_x0,_x1){if(_x1<=_x0){var _x2=new T(function(){var _x3=_x0-_wZ|0,_x4=function(_x5){return (_x5>=(_x1-_x3|0))?new T2(1,_x5,new T(function(){return B(_x4(_x5+_x3|0));})):new T2(1,_x5,_w);};return B(_x4(_x0));});return new T2(1,_wZ,_x2);}else{return (_x1<=_wZ)?new T2(1,_wZ,_w):__Z;}},_x6=function(_x7,_x8,_x9){if(_x9>=_x8){var _xa=new T(function(){var _xb=_x8-_x7|0,_xc=function(_xd){return (_xd<=(_x9-_xb|0))?new T2(1,_xd,new T(function(){return B(_xc(_xd+_xb|0));})):new T2(1,_xd,_w);};return B(_xc(_x8));});return new T2(1,_x7,_xa);}else{return (_x9>=_x7)?new T2(1,_x7,_w):__Z;}},_xe=function(_xf,_xg){if(_xg<_xf){return new F(function(){return _wY(_xf,_xg,-2147483648);});}else{return new F(function(){return _x6(_xf,_xg,2147483647);});}},_xh=function(_xi,_xj){return new F(function(){return _xe(E(_xi),E(_xj));});},_xk=function(_xl,_xm,_xn){if(_xm<_xl){return new F(function(){return _wY(_xl,_xm,_xn);});}else{return new F(function(){return _x6(_xl,_xm,_xn);});}},_xo=function(_xp,_xq,_xr){return new F(function(){return _xk(E(_xp),E(_xq),E(_xr));});},_xs=function(_xt,_xu){return new F(function(){return _wR(E(_xt),E(_xu));});},_xv=function(_xw){return E(_xw);},_xx=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_xy=new T(function(){return B(err(_xx));}),_xz=function(_xA){var _xB=E(_xA);return (_xB==(-2147483648))?E(_xy):_xB-1|0;},_xC=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_xD=new T(function(){return B(err(_xC));}),_xE=function(_xF){var _xG=E(_xF);return (_xG==2147483647)?E(_xD):_xG+1|0;},_xH={_:0,a:_xE,b:_xz,c:_xv,d:_xv,e:_wW,f:_xh,g:_xs,h:_xo},_xI=function(_xJ,_xK){if(_xJ<=0){if(_xJ>=0){return new F(function(){return quot(_xJ,_xK);});}else{if(_xK<=0){return new F(function(){return quot(_xJ,_xK);});}else{return quot(_xJ+1|0,_xK)-1|0;}}}else{if(_xK>=0){if(_xJ>=0){return new F(function(){return quot(_xJ,_xK);});}else{if(_xK<=0){return new F(function(){return quot(_xJ,_xK);});}else{return quot(_xJ+1|0,_xK)-1|0;}}}else{return quot(_xJ-1|0,_xK)-1|0;}}},_xL=0,_xM=new T(function(){return B(_36(_xL));}),_xN=new T(function(){return die(_xM);}),_xO=function(_xP,_xQ){var _xR=E(_xQ);switch(_xR){case -1:var _xS=E(_xP);if(_xS==(-2147483648)){return E(_xN);}else{return new F(function(){return _xI(_xS,-1);});}break;case 0:return E(_3a);default:return new F(function(){return _xI(_xP,_xR);});}},_xT=function(_xU,_xV){return new F(function(){return _xO(E(_xU),E(_xV));});},_xW=0,_xX=new T2(0,_xN,_xW),_xY=function(_xZ,_y0){var _y1=E(_xZ),_y2=E(_y0);switch(_y2){case -1:var _y3=E(_y1);if(_y3==(-2147483648)){return E(_xX);}else{if(_y3<=0){if(_y3>=0){var _y4=quotRemI(_y3,-1);return new T2(0,_y4.a,_y4.b);}else{var _y5=quotRemI(_y3,-1);return new T2(0,_y5.a,_y5.b);}}else{var _y6=quotRemI(_y3-1|0,-1);return new T2(0,_y6.a-1|0,(_y6.b+(-1)|0)+1|0);}}break;case 0:return E(_3a);default:if(_y1<=0){if(_y1>=0){var _y7=quotRemI(_y1,_y2);return new T2(0,_y7.a,_y7.b);}else{if(_y2<=0){var _y8=quotRemI(_y1,_y2);return new T2(0,_y8.a,_y8.b);}else{var _y9=quotRemI(_y1+1|0,_y2);return new T2(0,_y9.a-1|0,(_y9.b+_y2|0)-1|0);}}}else{if(_y2>=0){if(_y1>=0){var _ya=quotRemI(_y1,_y2);return new T2(0,_ya.a,_ya.b);}else{if(_y2<=0){var _yb=quotRemI(_y1,_y2);return new T2(0,_yb.a,_yb.b);}else{var _yc=quotRemI(_y1+1|0,_y2);return new T2(0,_yc.a-1|0,(_yc.b+_y2|0)-1|0);}}}else{var _yd=quotRemI(_y1-1|0,_y2);return new T2(0,_yd.a-1|0,(_yd.b+_y2|0)+1|0);}}}},_ye=function(_yf,_yg){var _yh=_yf%_yg;if(_yf<=0){if(_yf>=0){return E(_yh);}else{if(_yg<=0){return E(_yh);}else{var _yi=E(_yh);return (_yi==0)?0:_yi+_yg|0;}}}else{if(_yg>=0){if(_yf>=0){return E(_yh);}else{if(_yg<=0){return E(_yh);}else{var _yj=E(_yh);return (_yj==0)?0:_yj+_yg|0;}}}else{var _yk=E(_yh);return (_yk==0)?0:_yk+_yg|0;}}},_yl=function(_ym,_yn){var _yo=E(_yn);switch(_yo){case -1:return E(_xW);case 0:return E(_3a);default:return new F(function(){return _ye(E(_ym),_yo);});}},_yp=function(_yq,_yr){var _ys=E(_yq),_yt=E(_yr);switch(_yt){case -1:var _yu=E(_ys);if(_yu==(-2147483648)){return E(_xN);}else{return new F(function(){return quot(_yu,-1);});}break;case 0:return E(_3a);default:return new F(function(){return quot(_ys,_yt);});}},_yv=function(_yw,_yx){var _yy=E(_yw),_yz=E(_yx);switch(_yz){case -1:var _yA=E(_yy);if(_yA==(-2147483648)){return E(_xX);}else{var _yB=quotRemI(_yA,-1);return new T2(0,_yB.a,_yB.b);}break;case 0:return E(_3a);default:var _yC=quotRemI(_yy,_yz);return new T2(0,_yC.a,_yC.b);}},_yD=function(_yE,_yF){var _yG=E(_yF);switch(_yG){case -1:return E(_xW);case 0:return E(_3a);default:return E(_yE)%_yG;}},_yH=function(_yI){return new F(function(){return _vM(E(_yI));});},_yJ=function(_yK){return new T2(0,E(B(_vM(E(_yK)))),E(_ry));},_yL=function(_yM,_yN){return imul(E(_yM),E(_yN))|0;},_yO=function(_yP,_yQ){return E(_yP)+E(_yQ)|0;},_yR=function(_yS,_yT){return E(_yS)-E(_yT)|0;},_yU=function(_yV){var _yW=E(_yV);return (_yW<0)? -_yW:E(_yW);},_yX=function(_yY){return new F(function(){return _3n(_yY);});},_yZ=function(_z0){return  -E(_z0);},_z1=-1,_z2=0,_z3=1,_z4=function(_z5){var _z6=E(_z5);return (_z6>=0)?(E(_z6)==0)?E(_z2):E(_z3):E(_z1);},_z7={_:0,a:_yO,b:_yR,c:_yL,d:_yZ,e:_yU,f:_z4,g:_yX},_z8=function(_z9,_za){return E(_z9)==E(_za);},_zb=function(_zc,_zd){return E(_zc)!=E(_zd);},_ze=new T2(0,_z8,_zb),_zf=function(_zg,_zh){var _zi=E(_zg),_zj=E(_zh);return (_zi>_zj)?E(_zi):E(_zj);},_zk=function(_zl,_zm){var _zn=E(_zl),_zo=E(_zm);return (_zn>_zo)?E(_zo):E(_zn);},_zp=function(_zq,_zr){return (_zq>=_zr)?(_zq!=_zr)?2:1:0;},_zs=function(_zt,_zu){return new F(function(){return _zp(E(_zt),E(_zu));});},_zv=function(_zw,_zx){return E(_zw)>=E(_zx);},_zy=function(_zz,_zA){return E(_zz)>E(_zA);},_zB=function(_zC,_zD){return E(_zC)<=E(_zD);},_zE=function(_zF,_zG){return E(_zF)<E(_zG);},_zH={_:0,a:_ze,b:_zs,c:_zE,d:_zB,e:_zy,f:_zv,g:_zf,h:_zk},_zI=new T3(0,_z7,_zH,_yJ),_zJ={_:0,a:_zI,b:_xH,c:_yp,d:_yD,e:_xT,f:_yl,g:_yv,h:_xY,i:_yH},_zK=new T1(0,2),_zL=function(_zM,_zN){while(1){var _zO=E(_zM);if(!_zO._){var _zP=_zO.a,_zQ=E(_zN);if(!_zQ._){var _zR=_zQ.a;if(!(imul(_zP,_zR)|0)){return new T1(0,imul(_zP,_zR)|0);}else{_zM=new T1(1,I_fromInt(_zP));_zN=new T1(1,I_fromInt(_zR));continue;}}else{_zM=new T1(1,I_fromInt(_zP));_zN=_zQ;continue;}}else{var _zS=E(_zN);if(!_zS._){_zM=_zO;_zN=new T1(1,I_fromInt(_zS.a));continue;}else{return new T1(1,I_mul(_zO.a,_zS.a));}}}},_zT=function(_zU,_zV,_zW){while(1){if(!(_zV%2)){var _zX=B(_zL(_zU,_zU)),_zY=quot(_zV,2);_zU=_zX;_zV=_zY;continue;}else{var _zZ=E(_zV);if(_zZ==1){return new F(function(){return _zL(_zU,_zW);});}else{var _zX=B(_zL(_zU,_zU)),_A0=B(_zL(_zU,_zW));_zU=_zX;_zV=quot(_zZ-1|0,2);_zW=_A0;continue;}}}},_A1=function(_A2,_A3){while(1){if(!(_A3%2)){var _A4=B(_zL(_A2,_A2)),_A5=quot(_A3,2);_A2=_A4;_A3=_A5;continue;}else{var _A6=E(_A3);if(_A6==1){return E(_A2);}else{return new F(function(){return _zT(B(_zL(_A2,_A2)),quot(_A6-1|0,2),_A2);});}}}},_A7=function(_A8){return E(E(_A8).b);},_A9=function(_Aa){return E(E(_Aa).c);},_Ab=new T1(0,0),_Ac=function(_Ad){return E(E(_Ad).d);},_Ae=function(_Af,_Ag){var _Ah=B(_wN(_Af)),_Ai=new T(function(){return B(_wP(_Ah));}),_Aj=new T(function(){return B(A3(_Ac,_Af,_Ag,new T(function(){return B(A2(_8s,_Ai,_rI));})));});return new F(function(){return A3(_qm,B(_q8(B(_A7(_Ah)))),_Aj,new T(function(){return B(A2(_8s,_Ai,_Ab));}));});},_Ak=new T(function(){return B(unCStr("Negative exponent"));}),_Al=new T(function(){return B(err(_Ak));}),_Am=function(_An){return E(E(_An).c);},_Ao=function(_Ap,_Aq,_Ar,_As){var _At=B(_wN(_Aq)),_Au=new T(function(){return B(_wP(_At));}),_Av=B(_A7(_At));if(!B(A3(_A9,_Av,_As,new T(function(){return B(A2(_8s,_Au,_Ab));})))){if(!B(A3(_qm,B(_q8(_Av)),_As,new T(function(){return B(A2(_8s,_Au,_Ab));})))){var _Aw=new T(function(){return B(A2(_8s,_Au,_rI));}),_Ax=new T(function(){return B(A2(_8s,_Au,_ry));}),_Ay=B(_q8(_Av)),_Az=function(_AA,_AB,_AC){while(1){var _AD=B((function(_AE,_AF,_AG){if(!B(_Ae(_Aq,_AF))){if(!B(A3(_qm,_Ay,_AF,_Ax))){var _AH=new T(function(){return B(A3(_Am,_Aq,new T(function(){return B(A3(_9p,_Au,_AF,_Ax));}),_Aw));});_AA=new T(function(){return B(A3(_8L,_Ap,_AE,_AE));});_AB=_AH;_AC=new T(function(){return B(A3(_8L,_Ap,_AE,_AG));});return __continue;}else{return new F(function(){return A3(_8L,_Ap,_AE,_AG);});}}else{var _AI=_AG;_AA=new T(function(){return B(A3(_8L,_Ap,_AE,_AE));});_AB=new T(function(){return B(A3(_Am,_Aq,_AF,_Aw));});_AC=_AI;return __continue;}})(_AA,_AB,_AC));if(_AD!=__continue){return _AD;}}},_AJ=function(_AK,_AL){while(1){var _AM=B((function(_AN,_AO){if(!B(_Ae(_Aq,_AO))){if(!B(A3(_qm,_Ay,_AO,_Ax))){var _AP=new T(function(){return B(A3(_Am,_Aq,new T(function(){return B(A3(_9p,_Au,_AO,_Ax));}),_Aw));});return new F(function(){return _Az(new T(function(){return B(A3(_8L,_Ap,_AN,_AN));}),_AP,_AN);});}else{return E(_AN);}}else{_AK=new T(function(){return B(A3(_8L,_Ap,_AN,_AN));});_AL=new T(function(){return B(A3(_Am,_Aq,_AO,_Aw));});return __continue;}})(_AK,_AL));if(_AM!=__continue){return _AM;}}};return new F(function(){return _AJ(_Ar,_As);});}else{return new F(function(){return A2(_8s,_Ap,_ry);});}}else{return E(_Al);}},_AQ=new T(function(){return B(err(_Ak));}),_AR=function(_AS,_AT){var _AU=B(_vJ(_AT)),_AV=_AU.a,_AW=_AU.b,_AX=new T(function(){return B(_wP(new T(function(){return B(_wN(_AS));})));});if(_AW<0){var _AY= -_AW;if(_AY>=0){var _AZ=E(_AY);if(!_AZ){var _B0=E(_ry);}else{var _B0=B(_A1(_zK,_AZ));}if(!B(_3f(_B0,_3I))){var _B1=B(_3z(_AV,_B0));return new T2(0,new T(function(){return B(A2(_8s,_AX,_B1.a));}),new T(function(){return B(_3b(_B1.b,_AW));}));}else{return E(_3a);}}else{return E(_AQ);}}else{var _B2=new T(function(){var _B3=new T(function(){return B(_Ao(_AX,_zJ,new T(function(){return B(A2(_8s,_AX,_zK));}),_AW));});return B(A3(_8L,_AX,new T(function(){return B(A2(_8s,_AX,_AV));}),_B3));});return new T2(0,_B2,_6x);}},_B4=function(_B5,_B6){var _B7=B(_AR(_B5,E(_B6))),_B8=_B7.a;if(E(_B7.b)<=0){return E(_B8);}else{var _B9=B(_wP(B(_wN(_B5))));return new F(function(){return A3(_6X,_B9,_B8,new T(function(){return B(A2(_8s,_B9,_21));}));});}},_Ba=function(_Bb,_Bc){var _Bd=B(_AR(_Bb,E(_Bc))),_Be=_Bd.a;if(E(_Bd.b)>=0){return E(_Be);}else{var _Bf=B(_wP(B(_wN(_Bb))));return new F(function(){return A3(_9p,_Bf,_Be,new T(function(){return B(A2(_8s,_Bf,_21));}));});}},_Bg=function(_Bh,_Bi){var _Bj=B(_AR(_Bh,E(_Bi)));return new T2(0,_Bj.a,_Bj.b);},_Bk=function(_Bl,_Bm){var _Bn=B(_AR(_Bl,_Bm)),_Bo=_Bn.a,_Bp=E(_Bn.b),_Bq=new T(function(){var _Br=B(_wP(B(_wN(_Bl))));if(_Bp>=0){return B(A3(_6X,_Br,_Bo,new T(function(){return B(A2(_8s,_Br,_21));})));}else{return B(A3(_9p,_Br,_Bo,new T(function(){return B(A2(_8s,_Br,_21));})));}}),_Bs=function(_Bt){var _Bu=_Bt-0.5;return (_Bu>=0)?(E(_Bu)==0)?(!B(_Ae(_Bl,_Bo)))?E(_Bq):E(_Bo):E(_Bq):E(_Bo);},_Bv=E(_Bp);if(!_Bv){return new F(function(){return _Bs(0);});}else{if(_Bv<=0){var _Bw= -_Bv-0.5;return (_Bw>=0)?(E(_Bw)==0)?(!B(_Ae(_Bl,_Bo)))?E(_Bq):E(_Bo):E(_Bq):E(_Bo);}else{return new F(function(){return _Bs(_Bv);});}}},_Bx=function(_By,_Bz){return new F(function(){return _Bk(_By,E(_Bz));});},_BA=function(_BB,_BC){return E(B(_AR(_BB,E(_BC))).a);},_BD={_:0,a:_wM,b:_ni,c:_Bg,d:_BA,e:_Bx,f:_B4,g:_Ba},_BE=new T1(0,1),_BF=function(_BG,_BH){var _BI=E(_BG);return new T2(0,_BI,new T(function(){var _BJ=B(_BF(B(_3q(_BI,_BH)),_BH));return new T2(1,_BJ.a,_BJ.b);}));},_BK=function(_BL){var _BM=B(_BF(_BL,_BE));return new T2(1,_BM.a,_BM.b);},_BN=function(_BO,_BP){var _BQ=B(_BF(_BO,new T(function(){return B(_5L(_BP,_BO));})));return new T2(1,_BQ.a,_BQ.b);},_BR=new T1(0,0),_BS=function(_BT,_BU){var _BV=E(_BT);if(!_BV._){var _BW=_BV.a,_BX=E(_BU);return (_BX._==0)?_BW>=_BX.a:I_compareInt(_BX.a,_BW)<=0;}else{var _BY=_BV.a,_BZ=E(_BU);return (_BZ._==0)?I_compareInt(_BY,_BZ.a)>=0:I_compare(_BY,_BZ.a)>=0;}},_C0=function(_C1,_C2,_C3){if(!B(_BS(_C2,_BR))){var _C4=function(_C5){return (!B(_42(_C5,_C3)))?new T2(1,_C5,new T(function(){return B(_C4(B(_3q(_C5,_C2))));})):__Z;};return new F(function(){return _C4(_C1);});}else{var _C6=function(_C7){return (!B(_3T(_C7,_C3)))?new T2(1,_C7,new T(function(){return B(_C6(B(_3q(_C7,_C2))));})):__Z;};return new F(function(){return _C6(_C1);});}},_C8=function(_C9,_Ca,_Cb){return new F(function(){return _C0(_C9,B(_5L(_Ca,_C9)),_Cb);});},_Cc=function(_Cd,_Ce){return new F(function(){return _C0(_Cd,_BE,_Ce);});},_Cf=function(_Cg){return new F(function(){return _3n(_Cg);});},_Ch=function(_Ci){return new F(function(){return _5L(_Ci,_BE);});},_Cj=function(_Ck){return new F(function(){return _3q(_Ck,_BE);});},_Cl=function(_Cm){return new F(function(){return _vM(E(_Cm));});},_Cn={_:0,a:_Cj,b:_Ch,c:_Cl,d:_Cf,e:_BK,f:_BN,g:_Cc,h:_C8},_Co=function(_Cp,_Cq){while(1){var _Cr=E(_Cp);if(!_Cr._){var _Cs=E(_Cr.a);if(_Cs==(-2147483648)){_Cp=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ct=E(_Cq);if(!_Ct._){return new T1(0,B(_xI(_Cs,_Ct.a)));}else{_Cp=new T1(1,I_fromInt(_Cs));_Cq=_Ct;continue;}}}else{var _Cu=_Cr.a,_Cv=E(_Cq);return (_Cv._==0)?new T1(1,I_div(_Cu,I_fromInt(_Cv.a))):new T1(1,I_div(_Cu,_Cv.a));}}},_Cw=function(_Cx,_Cy){if(!B(_3f(_Cy,_Ab))){return new F(function(){return _Co(_Cx,_Cy);});}else{return E(_3a);}},_Cz=function(_CA,_CB){while(1){var _CC=E(_CA);if(!_CC._){var _CD=E(_CC.a);if(_CD==(-2147483648)){_CA=new T1(1,I_fromInt(-2147483648));continue;}else{var _CE=E(_CB);if(!_CE._){var _CF=_CE.a;return new T2(0,new T1(0,B(_xI(_CD,_CF))),new T1(0,B(_ye(_CD,_CF))));}else{_CA=new T1(1,I_fromInt(_CD));_CB=_CE;continue;}}}else{var _CG=E(_CB);if(!_CG._){_CA=_CC;_CB=new T1(1,I_fromInt(_CG.a));continue;}else{var _CH=I_divMod(_CC.a,_CG.a);return new T2(0,new T1(1,_CH.a),new T1(1,_CH.b));}}}},_CI=function(_CJ,_CK){if(!B(_3f(_CK,_Ab))){var _CL=B(_Cz(_CJ,_CK));return new T2(0,_CL.a,_CL.b);}else{return E(_3a);}},_CM=function(_CN,_CO){while(1){var _CP=E(_CN);if(!_CP._){var _CQ=E(_CP.a);if(_CQ==(-2147483648)){_CN=new T1(1,I_fromInt(-2147483648));continue;}else{var _CR=E(_CO);if(!_CR._){return new T1(0,B(_ye(_CQ,_CR.a)));}else{_CN=new T1(1,I_fromInt(_CQ));_CO=_CR;continue;}}}else{var _CS=_CP.a,_CT=E(_CO);return (_CT._==0)?new T1(1,I_mod(_CS,I_fromInt(_CT.a))):new T1(1,I_mod(_CS,_CT.a));}}},_CU=function(_CV,_CW){if(!B(_3f(_CW,_Ab))){return new F(function(){return _CM(_CV,_CW);});}else{return E(_3a);}},_CX=function(_CY,_CZ){while(1){var _D0=E(_CY);if(!_D0._){var _D1=E(_D0.a);if(_D1==(-2147483648)){_CY=new T1(1,I_fromInt(-2147483648));continue;}else{var _D2=E(_CZ);if(!_D2._){return new T1(0,quot(_D1,_D2.a));}else{_CY=new T1(1,I_fromInt(_D1));_CZ=_D2;continue;}}}else{var _D3=_D0.a,_D4=E(_CZ);return (_D4._==0)?new T1(0,I_toInt(I_quot(_D3,I_fromInt(_D4.a)))):new T1(1,I_quot(_D3,_D4.a));}}},_D5=function(_D6,_D7){if(!B(_3f(_D7,_Ab))){return new F(function(){return _CX(_D6,_D7);});}else{return E(_3a);}},_D8=function(_D9,_Da){if(!B(_3f(_Da,_Ab))){var _Db=B(_3z(_D9,_Da));return new T2(0,_Db.a,_Db.b);}else{return E(_3a);}},_Dc=function(_Dd,_De){while(1){var _Df=E(_Dd);if(!_Df._){var _Dg=E(_Df.a);if(_Dg==(-2147483648)){_Dd=new T1(1,I_fromInt(-2147483648));continue;}else{var _Dh=E(_De);if(!_Dh._){return new T1(0,_Dg%_Dh.a);}else{_Dd=new T1(1,I_fromInt(_Dg));_De=_Dh;continue;}}}else{var _Di=_Df.a,_Dj=E(_De);return (_Dj._==0)?new T1(1,I_rem(_Di,I_fromInt(_Dj.a))):new T1(1,I_rem(_Di,_Dj.a));}}},_Dk=function(_Dl,_Dm){if(!B(_3f(_Dm,_Ab))){return new F(function(){return _Dc(_Dl,_Dm);});}else{return E(_3a);}},_Dn=function(_Do){return E(_Do);},_Dp=function(_Dq){return E(_Dq);},_Dr=function(_Ds){var _Dt=E(_Ds);if(!_Dt._){var _Du=E(_Dt.a);return (_Du==(-2147483648))?E(_6p):(_Du<0)?new T1(0, -_Du):E(_Dt);}else{var _Dv=_Dt.a;return (I_compareInt(_Dv,0)>=0)?E(_Dt):new T1(1,I_negate(_Dv));}},_Dw=new T1(0,0),_Dx=new T1(0,-1),_Dy=function(_Dz){var _DA=E(_Dz);if(!_DA._){var _DB=_DA.a;return (_DB>=0)?(E(_DB)==0)?E(_Dw):E(_41):E(_Dx);}else{var _DC=I_compareInt(_DA.a,0);return (_DC<=0)?(E(_DC)==0)?E(_Dw):E(_Dx):E(_41);}},_DD={_:0,a:_3q,b:_5L,c:_zL,d:_6q,e:_Dr,f:_Dy,g:_Dp},_DE=function(_DF,_DG){var _DH=E(_DF);if(!_DH._){var _DI=_DH.a,_DJ=E(_DG);return (_DJ._==0)?_DI!=_DJ.a:(I_compareInt(_DJ.a,_DI)==0)?false:true;}else{var _DK=_DH.a,_DL=E(_DG);return (_DL._==0)?(I_compareInt(_DK,_DL.a)==0)?false:true:(I_compare(_DK,_DL.a)==0)?false:true;}},_DM=new T2(0,_3f,_DE),_DN=function(_DO,_DP){return (!B(_5w(_DO,_DP)))?E(_DO):E(_DP);},_DQ=function(_DR,_DS){return (!B(_5w(_DR,_DS)))?E(_DS):E(_DR);},_DT={_:0,a:_DM,b:_22,c:_42,d:_5w,e:_3T,f:_BS,g:_DN,h:_DQ},_DU=function(_DV){return new T2(0,E(_DV),E(_ry));},_DW=new T3(0,_DD,_DT,_DU),_DX={_:0,a:_DW,b:_Cn,c:_D5,d:_Dk,e:_Cw,f:_CU,g:_D8,h:_CI,i:_Dn},_DY=function(_DZ){return E(E(_DZ).b);},_E0=function(_E1){return E(E(_E1).g);},_E2=new T1(0,1),_E3=function(_E4,_E5,_E6){var _E7=B(_DY(_E4)),_E8=B(_8J(_E7)),_E9=new T(function(){var _Ea=new T(function(){var _Eb=new T(function(){var _Ec=new T(function(){return B(A3(_E0,_E4,_DX,new T(function(){return B(A3(_8P,_E7,_E5,_E6));})));});return B(A2(_8s,_E8,_Ec));}),_Ed=new T(function(){return B(A2(_6Z,_E8,new T(function(){return B(A2(_8s,_E8,_E2));})));});return B(A3(_8L,_E8,_Ed,_Eb));});return B(A3(_8L,_E8,_Ea,_E6));});return new F(function(){return A3(_6X,_E8,_E5,_E9);});},_Ee=1.5707963267948966,_Ef=function(_Eg){return 0.2/Math.cos(B(_E3(_BD,_Eg,_Ee))-0.7853981633974483);},_Eh=0,_Ei=new T(function(){var _Ej=B(_up(_Ef,1.2,_Eh,_Eh,_vI,_Eh,_Eh,_Eh,_Eh,_Eh,_vI,_vI,_vI));return {_:0,a:E(_Ej.a),b:E(_Ej.b),c:E(_Ej.c),d:E(_Ej.d),e:E(_Ej.e),f:E(_Ej.f),g:E(_Ej.g),h:_Ej.h,i:_Ej.i,j:_Ej.j};}),_Ek=0,_El=0.3,_Em=function(_En){return E(_El);},_Eo=new T(function(){var _Ep=B(_up(_Em,1.2,_vI,_Eh,_vI,_Eh,_Eh,_Eh,_Eh,_Eh,_vI,_vI,_vI));return {_:0,a:E(_Ep.a),b:E(_Ep.b),c:E(_Ep.c),d:E(_Ep.d),e:E(_Ep.e),f:E(_Ep.f),g:E(_Ep.g),h:_Ep.h,i:_Ep.i,j:_Ep.j};}),_Eq=new T(function(){var _Er=B(_up(_Em,1.2,_vI,_vI,_Eh,_Eh,_Eh,_Eh,_Eh,_Eh,_vI,_vI,_vI));return {_:0,a:E(_Er.a),b:E(_Er.b),c:E(_Er.c),d:E(_Er.d),e:E(_Er.e),f:E(_Er.f),g:E(_Er.g),h:_Er.h,i:_Er.i,j:_Er.j};}),_Es=2,_Et=function(_Eu){return 0.3/Math.cos(B(_E3(_BD,_Eu,_Ee))-0.7853981633974483);},_Ev=new T(function(){var _Ew=B(_up(_Et,1.2,_Es,_vI,_vI,_Eh,_Eh,_Eh,_Eh,_Eh,_vI,_vI,_vI));return {_:0,a:E(_Ew.a),b:E(_Ew.b),c:E(_Ew.c),d:E(_Ew.d),e:E(_Ew.e),f:E(_Ew.f),g:E(_Ew.g),h:_Ew.h,i:_Ew.i,j:_Ew.j};}),_Ex=new T2(1,_Ev,_w),_Ey=new T2(1,_Eq,_Ex),_Ez=new T2(1,_Eo,_Ey),_EA=new T2(1,_Ei,_Ez),_EB=new T(function(){return B(unCStr("Negative range size"));}),_EC=new T(function(){return B(err(_EB));}),_ED=function(_){var _EE=B(_m8(_EA,0))-1|0,_EF=function(_EG){if(_EG>=0){var _EH=newArr(_EG,_me),_EI=_EH,_EJ=E(_EG);if(!_EJ){return new T4(0,E(_Ek),E(_EE),0,_EI);}else{var _EK=function(_EL,_EM,_){while(1){var _EN=E(_EL);if(!_EN._){return E(_);}else{var _=_EI[_EM]=_EN.a;if(_EM!=(_EJ-1|0)){var _EO=_EM+1|0;_EL=_EN.b;_EM=_EO;continue;}else{return E(_);}}}},_=B((function(_EP,_EQ,_ER,_){var _=_EI[_ER]=_EP;if(_ER!=(_EJ-1|0)){return new F(function(){return _EK(_EQ,_ER+1|0,_);});}else{return E(_);}})(_Ei,_Ez,0,_));return new T4(0,E(_Ek),E(_EE),_EJ,_EI);}}else{return E(_EC);}};if(0>_EE){return new F(function(){return _EF(0);});}else{return new F(function(){return _EF(_EE+1|0);});}},_ES=function(_ET){var _EU=B(A1(_ET,_));return E(_EU);},_EV=new T(function(){return B(_ES(_ED));}),_EW="enclose",_EX="outline",_EY="polygon",_EZ="z",_F0="y",_F1="x",_F2=function(_F3){return new F(function(){return _ow(new T2(1,new T2(0,_F1,new T(function(){return E(E(E(E(_F3).d).a).a);})),new T2(1,new T2(0,_F0,new T(function(){return E(E(E(E(_F3).d).a).b);})),new T2(1,new T2(0,_EZ,new T(function(){return E(E(E(E(_F3).d).a).c);})),new T2(1,new T2(0,_EY,new T(function(){return E(_F3).h;})),new T2(1,new T2(0,_EX,new T(function(){return E(_F3).i;})),new T2(1,new T2(0,_EW,new T(function(){return E(_F3).j;})),_w)))))));});},_F4=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_F5=new T(function(){return B(err(_F4));}),_F6=new T(function(){return eval("__strict(drawObjects)");}),_F7=new T(function(){return eval("__strict(draw)");}),_F8=function(_F9,_Fa){var _Fb=jsShowI(_F9);return new F(function(){return _n(fromJSStr(_Fb),_Fa);});},_Fc=function(_Fd,_Fe,_Ff){if(_Fe>=0){return new F(function(){return _F8(_Fe,_Ff);});}else{if(_Fd<=6){return new F(function(){return _F8(_Fe,_Ff);});}else{return new T2(1,_7g,new T(function(){var _Fg=jsShowI(_Fe);return B(_n(fromJSStr(_Fg),new T2(1,_7f,_Ff)));}));}}},_Fh=new T(function(){return B(unCStr(")"));}),_Fi=function(_Fj,_Fk){var _Fl=new T(function(){var _Fm=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Fc(0,_Fj,_w)),_Fh));})));},1);return B(_n(B(_Fc(0,_Fk,_w)),_Fm));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Fl)));});},_Fn=new T2(1,_ov,_w),_Fo=function(_Fp){return E(_Fp);},_Fq=function(_Fr){return E(_Fr);},_Fs=function(_Ft,_Fu){return E(_Fu);},_Fv=function(_Fw,_Fx){return E(_Fw);},_Fy=function(_Fz){return E(_Fz);},_FA=new T2(0,_Fy,_Fv),_FB=function(_FC,_FD){return E(_FC);},_FE=new T5(0,_FA,_Fq,_Fo,_Fs,_FB),_FF="flipped2",_FG="flipped1",_FH="c1y",_FI="c1x",_FJ="w2z",_FK="w2y",_FL="w2x",_FM="w1z",_FN="w1y",_FO="w1x",_FP="d2z",_FQ="d2y",_FR="d2x",_FS="d1z",_FT="d1y",_FU="d1x",_FV="c2y",_FW="c2x",_FX=function(_FY,_){var _FZ=__get(_FY,E(_FO)),_G0=__get(_FY,E(_FN)),_G1=__get(_FY,E(_FM)),_G2=__get(_FY,E(_FL)),_G3=__get(_FY,E(_FK)),_G4=__get(_FY,E(_FJ)),_G5=__get(_FY,E(_FI)),_G6=__get(_FY,E(_FH)),_G7=__get(_FY,E(_FW)),_G8=__get(_FY,E(_FV)),_G9=__get(_FY,E(_FU)),_Ga=__get(_FY,E(_FT)),_Gb=__get(_FY,E(_FS)),_Gc=__get(_FY,E(_FR)),_Gd=__get(_FY,E(_FQ)),_Ge=__get(_FY,E(_FP)),_Gf=__get(_FY,E(_FG)),_Gg=__get(_FY,E(_FF));return {_:0,a:E(new T3(0,E(_FZ),E(_G0),E(_G1))),b:E(new T3(0,E(_G2),E(_G3),E(_G4))),c:E(new T2(0,E(_G5),E(_G6))),d:E(new T2(0,E(_G7),E(_G8))),e:E(new T3(0,E(_G9),E(_Ga),E(_Gb))),f:E(new T3(0,E(_Gc),E(_Gd),E(_Ge))),g:E(_Gf),h:E(_Gg)};},_Gh=function(_Gi,_){var _Gj=E(_Gi);if(!_Gj._){return _w;}else{var _Gk=B(_FX(E(_Gj.a),_)),_Gl=B(_Gh(_Gj.b,_));return new T2(1,_Gk,_Gl);}},_Gm=function(_Gn){var _Go=E(_Gn);return (E(_Go.b)-E(_Go.a)|0)+1|0;},_Gp=function(_Gq,_Gr){var _Gs=E(_Gq),_Gt=E(_Gr);return (E(_Gs.a)>_Gt)?false:_Gt<=E(_Gs.b);},_Gu=function(_Gv){return new F(function(){return _Fc(0,E(_Gv),_w);});},_Gw=function(_Gx,_Gy,_Gz){return new F(function(){return _Fc(E(_Gx),E(_Gy),_Gz);});},_GA=function(_GB,_GC){return new F(function(){return _Fc(0,E(_GB),_GC);});},_GD=function(_GE,_GF){return new F(function(){return _2Q(_GA,_GE,_GF);});},_GG=new T3(0,_Gw,_Gu,_GD),_GH=0,_GI=function(_GJ,_GK,_GL){return new F(function(){return A1(_GJ,new T2(1,_2N,new T(function(){return B(A1(_GK,_GL));})));});},_GM=new T(function(){return B(unCStr("foldr1"));}),_GN=new T(function(){return B(_qX(_GM));}),_GO=function(_GP,_GQ){var _GR=E(_GQ);if(!_GR._){return E(_GN);}else{var _GS=_GR.a,_GT=E(_GR.b);if(!_GT._){return E(_GS);}else{return new F(function(){return A2(_GP,_GS,new T(function(){return B(_GO(_GP,_GT));}));});}}},_GU=new T(function(){return B(unCStr(" out of range "));}),_GV=new T(function(){return B(unCStr("}.index: Index "));}),_GW=new T(function(){return B(unCStr("Ix{"));}),_GX=new T2(1,_7f,_w),_GY=new T2(1,_7f,_GX),_GZ=0,_H0=function(_H1){return E(E(_H1).a);},_H2=function(_H3,_H4,_H5,_H6,_H7){var _H8=new T(function(){var _H9=new T(function(){var _Ha=new T(function(){var _Hb=new T(function(){var _Hc=new T(function(){return B(A3(_GO,_GI,new T2(1,new T(function(){return B(A3(_H0,_H5,_GZ,_H6));}),new T2(1,new T(function(){return B(A3(_H0,_H5,_GZ,_H7));}),_w)),_GY));});return B(_n(_GU,new T2(1,_7g,new T2(1,_7g,_Hc))));});return B(A(_H0,[_H5,_GH,_H4,new T2(1,_7f,_Hb)]));});return B(_n(_GV,new T2(1,_7g,_Ha)));},1);return B(_n(_H3,_H9));},1);return new F(function(){return err(B(_n(_GW,_H8)));});},_Hd=function(_He,_Hf,_Hg,_Hh,_Hi){return new F(function(){return _H2(_He,_Hf,_Hi,_Hg,_Hh);});},_Hj=function(_Hk,_Hl,_Hm,_Hn){var _Ho=E(_Hm);return new F(function(){return _Hd(_Hk,_Hl,_Ho.a,_Ho.b,_Hn);});},_Hp=function(_Hq,_Hr,_Hs,_Ht){return new F(function(){return _Hj(_Ht,_Hs,_Hr,_Hq);});},_Hu=new T(function(){return B(unCStr("Int"));}),_Hv=function(_Hw,_Hx){return new F(function(){return _Hp(_GG,_Hx,_Hw,_Hu);});},_Hy=function(_Hz,_HA){var _HB=E(_Hz),_HC=E(_HB.a),_HD=E(_HA);if(_HC>_HD){return new F(function(){return _Hv(_HD,_HB);});}else{if(_HD>E(_HB.b)){return new F(function(){return _Hv(_HD,_HB);});}else{return _HD-_HC|0;}}},_HE=function(_HF){var _HG=E(_HF);return new F(function(){return _xs(_HG.a,_HG.b);});},_HH=function(_HI){var _HJ=E(_HI),_HK=E(_HJ.a),_HL=E(_HJ.b);return (_HK>_HL)?E(_GH):(_HL-_HK|0)+1|0;},_HM=function(_HN,_HO){return new F(function(){return _yR(_HO,E(_HN).a);});},_HP={_:0,a:_zH,b:_HE,c:_Hy,d:_HM,e:_Gp,f:_HH,g:_Gm},_HQ=function(_HR,_HS,_){while(1){var _HT=B((function(_HU,_HV,_){var _HW=E(_HU);if(!_HW._){return new T2(0,_ov,_HV);}else{var _HX=B(A2(_HW.a,_HV,_));_HR=_HW.b;_HS=new T(function(){return E(E(_HX).b);});return __continue;}})(_HR,_HS,_));if(_HT!=__continue){return _HT;}}},_HY=function(_HZ,_I0){return new T2(1,_HZ,_I0);},_I1=function(_I2,_I3){var _I4=E(_I3);return new T2(0,_I4.a,_I4.b);},_I5=function(_I6){return E(E(_I6).f);},_I7=function(_I8,_I9,_Ia){var _Ib=E(_I9),_Ic=_Ib.a,_Id=_Ib.b,_Ie=function(_){var _If=B(A2(_I5,_I8,_Ib));if(_If>=0){var _Ig=newArr(_If,_me),_Ih=_Ig,_Ii=E(_If);if(!_Ii){return new T(function(){return new T4(0,E(_Ic),E(_Id),0,_Ih);});}else{var _Ij=function(_Ik,_Il,_){while(1){var _Im=E(_Ik);if(!_Im._){return E(_);}else{var _=_Ih[_Il]=_Im.a;if(_Il!=(_Ii-1|0)){var _In=_Il+1|0;_Ik=_Im.b;_Il=_In;continue;}else{return E(_);}}}},_=B(_Ij(_Ia,0,_));return new T(function(){return new T4(0,E(_Ic),E(_Id),_Ii,_Ih);});}}else{return E(_EC);}};return new F(function(){return _ES(_Ie);});},_Io=function(_Ip,_Iq,_Ir,_Is){var _It=new T(function(){var _Iu=E(_Is),_Iv=_Iu.c-1|0,_Iw=new T(function(){return B(A2(_cF,_Iq,_w));});if(0<=_Iv){var _Ix=new T(function(){return B(_8F(_Iq));}),_Iy=function(_Iz){var _IA=new T(function(){var _IB=new T(function(){return B(A1(_Ir,new T(function(){return E(_Iu.d[_Iz]);})));});return B(A3(_8T,_Ix,_HY,_IB));});return new F(function(){return A3(_8R,_Iq,_IA,new T(function(){if(_Iz!=_Iv){return B(_Iy(_Iz+1|0));}else{return E(_Iw);}}));});};return B(_Iy(0));}else{return E(_Iw);}}),_IC=new T(function(){return B(_I1(_Ip,_Is));});return new F(function(){return A3(_8T,B(_8F(_Iq)),function(_ID){return new F(function(){return _I7(_Ip,_IC,_ID);});},_It);});},_IE=function(_IF,_IG,_IH,_II,_IJ,_IK,_IL,_IM,_IN){var _IO=B(_8L(_IF));return new T2(0,new T3(0,E(B(A1(B(A1(_IO,_IG)),_IK))),E(B(A1(B(A1(_IO,_IH)),_IL))),E(B(A1(B(A1(_IO,_II)),_IM)))),B(A1(B(A1(_IO,_IJ)),_IN)));},_IP=function(_IQ,_IR,_IS,_IT,_IU,_IV,_IW,_IX,_IY){var _IZ=B(_6X(_IQ));return new T2(0,new T3(0,E(B(A1(B(A1(_IZ,_IR)),_IV))),E(B(A1(B(A1(_IZ,_IS)),_IW))),E(B(A1(B(A1(_IZ,_IT)),_IX)))),B(A1(B(A1(_IZ,_IU)),_IY)));},_J0=1.0e-2,_J1=function(_J2,_J3,_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb,_Jc,_Jd,_Je,_Jf,_Jg,_Jh,_Ji,_Jj){var _Jk=B(_IE(_ne,_J9,_Ja,_Jb,_Jc,_J0,_J0,_J0,_J0)),_Jl=E(_Jk.a),_Jm=B(_IP(_ne,_J5,_J6,_J7,_J8,_Jl.a,_Jl.b,_Jl.c,_Jk.b)),_Jn=E(_Jm.a);return new F(function(){return _tF(_J2,_J3,_J4,_Jn.a,_Jn.b,_Jn.c,_Jm.b,_J9,_Ja,_Jb,_Jc,_Jd,_Je,_Jf,_Jg,_Jh,_Ji,_Jj);});},_Jo=function(_Jp){var _Jq=E(_Jp),_Jr=E(_Jq.d),_Js=E(_Jr.a),_Jt=E(_Jq.e),_Ju=E(_Jt.a),_Jv=E(_Jq.f),_Jw=B(_J1(_Jq.a,_Jq.b,_Jq.c,_Js.a,_Js.b,_Js.c,_Jr.b,_Ju.a,_Ju.b,_Ju.c,_Jt.b,_Jv.a,_Jv.b,_Jv.c,_Jq.g,_Jq.h,_Jq.i,_Jq.j));return {_:0,a:E(_Jw.a),b:E(_Jw.b),c:E(_Jw.c),d:E(_Jw.d),e:E(_Jw.e),f:E(_Jw.f),g:E(_Jw.g),h:_Jw.h,i:_Jw.i,j:_Jw.j};},_Jx=function(_Jy,_Jz,_JA,_JB,_JC,_JD,_JE,_JF,_JG){var _JH=B(_8J(B(_8H(_Jy))));return new F(function(){return A3(_6X,_JH,new T(function(){return B(_p9(_Jy,_Jz,_JA,_JB,_JD,_JE,_JF));}),new T(function(){return B(A3(_8L,_JH,_JC,_JG));}));});},_JI=new T(function(){return B(unCStr("base"));}),_JJ=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_JK=new T(function(){return B(unCStr("IOException"));}),_JL=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_JI,_JJ,_JK),_JM=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_JL,_w,_w),_JN=function(_JO){return E(_JM);},_JP=function(_JQ){var _JR=E(_JQ);return new F(function(){return _2n(B(_2l(_JR.a)),_JN,_JR.b);});},_JS=new T(function(){return B(unCStr(": "));}),_JT=new T(function(){return B(unCStr(")"));}),_JU=new T(function(){return B(unCStr(" ("));}),_JV=new T(function(){return B(unCStr("interrupted"));}),_JW=new T(function(){return B(unCStr("system error"));}),_JX=new T(function(){return B(unCStr("unsatisified constraints"));}),_JY=new T(function(){return B(unCStr("user error"));}),_JZ=new T(function(){return B(unCStr("permission denied"));}),_K0=new T(function(){return B(unCStr("illegal operation"));}),_K1=new T(function(){return B(unCStr("end of file"));}),_K2=new T(function(){return B(unCStr("resource exhausted"));}),_K3=new T(function(){return B(unCStr("resource busy"));}),_K4=new T(function(){return B(unCStr("does not exist"));}),_K5=new T(function(){return B(unCStr("already exists"));}),_K6=new T(function(){return B(unCStr("resource vanished"));}),_K7=new T(function(){return B(unCStr("timeout"));}),_K8=new T(function(){return B(unCStr("unsupported operation"));}),_K9=new T(function(){return B(unCStr("hardware fault"));}),_Ka=new T(function(){return B(unCStr("inappropriate type"));}),_Kb=new T(function(){return B(unCStr("invalid argument"));}),_Kc=new T(function(){return B(unCStr("failed"));}),_Kd=new T(function(){return B(unCStr("protocol error"));}),_Ke=function(_Kf,_Kg){switch(E(_Kf)){case 0:return new F(function(){return _n(_K5,_Kg);});break;case 1:return new F(function(){return _n(_K4,_Kg);});break;case 2:return new F(function(){return _n(_K3,_Kg);});break;case 3:return new F(function(){return _n(_K2,_Kg);});break;case 4:return new F(function(){return _n(_K1,_Kg);});break;case 5:return new F(function(){return _n(_K0,_Kg);});break;case 6:return new F(function(){return _n(_JZ,_Kg);});break;case 7:return new F(function(){return _n(_JY,_Kg);});break;case 8:return new F(function(){return _n(_JX,_Kg);});break;case 9:return new F(function(){return _n(_JW,_Kg);});break;case 10:return new F(function(){return _n(_Kd,_Kg);});break;case 11:return new F(function(){return _n(_Kc,_Kg);});break;case 12:return new F(function(){return _n(_Kb,_Kg);});break;case 13:return new F(function(){return _n(_Ka,_Kg);});break;case 14:return new F(function(){return _n(_K9,_Kg);});break;case 15:return new F(function(){return _n(_K8,_Kg);});break;case 16:return new F(function(){return _n(_K7,_Kg);});break;case 17:return new F(function(){return _n(_K6,_Kg);});break;default:return new F(function(){return _n(_JV,_Kg);});}},_Kh=new T(function(){return B(unCStr("}"));}),_Ki=new T(function(){return B(unCStr("{handle: "));}),_Kj=function(_Kk,_Kl,_Km,_Kn,_Ko,_Kp){var _Kq=new T(function(){var _Kr=new T(function(){var _Ks=new T(function(){var _Kt=E(_Kn);if(!_Kt._){return E(_Kp);}else{var _Ku=new T(function(){return B(_n(_Kt,new T(function(){return B(_n(_JT,_Kp));},1)));},1);return B(_n(_JU,_Ku));}},1);return B(_Ke(_Kl,_Ks));}),_Kv=E(_Km);if(!_Kv._){return E(_Kr);}else{return B(_n(_Kv,new T(function(){return B(_n(_JS,_Kr));},1)));}}),_Kw=E(_Ko);if(!_Kw._){var _Kx=E(_Kk);if(!_Kx._){return E(_Kq);}else{var _Ky=E(_Kx.a);if(!_Ky._){var _Kz=new T(function(){var _KA=new T(function(){return B(_n(_Kh,new T(function(){return B(_n(_JS,_Kq));},1)));},1);return B(_n(_Ky.a,_KA));},1);return new F(function(){return _n(_Ki,_Kz);});}else{var _KB=new T(function(){var _KC=new T(function(){return B(_n(_Kh,new T(function(){return B(_n(_JS,_Kq));},1)));},1);return B(_n(_Ky.a,_KC));},1);return new F(function(){return _n(_Ki,_KB);});}}}else{return new F(function(){return _n(_Kw.a,new T(function(){return B(_n(_JS,_Kq));},1));});}},_KD=function(_KE){var _KF=E(_KE);return new F(function(){return _Kj(_KF.a,_KF.b,_KF.c,_KF.d,_KF.f,_w);});},_KG=function(_KH,_KI,_KJ){var _KK=E(_KI);return new F(function(){return _Kj(_KK.a,_KK.b,_KK.c,_KK.d,_KK.f,_KJ);});},_KL=function(_KM,_KN){var _KO=E(_KM);return new F(function(){return _Kj(_KO.a,_KO.b,_KO.c,_KO.d,_KO.f,_KN);});},_KP=function(_KQ,_KR){return new F(function(){return _2Q(_KL,_KQ,_KR);});},_KS=new T3(0,_KG,_KD,_KP),_KT=new T(function(){return new T5(0,_JN,_KS,_KU,_JP,_KD);}),_KU=function(_KV){return new T2(0,_KT,_KV);},_KW=__Z,_KX=7,_KY=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_KZ=new T6(0,_KW,_KX,_w,_KY,_KW,_KW),_L0=new T(function(){return B(_KU(_KZ));}),_L1=function(_){return new F(function(){return die(_L0);});},_L2=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_L3=new T6(0,_KW,_KX,_w,_L2,_KW,_KW),_L4=new T(function(){return B(_KU(_L3));}),_L5=function(_){return new F(function(){return die(_L4);});},_L6=function(_L7,_){return new T2(0,_w,_L7);},_L8=0.6,_L9=1,_La=new T(function(){return B(unCStr(")"));}),_Lb=function(_Lc,_Ld){var _Le=new T(function(){var _Lf=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Fc(0,_Lc,_w)),_La));})));},1);return B(_n(B(_Fc(0,_Ld,_w)),_Lf));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Le)));});},_Lg=function(_Lh,_Li){var _Lj=new T(function(){var _Lk=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Fc(0,_Li,_w)),_La));})));},1);return B(_n(B(_Fc(0,_Lh,_w)),_Lk));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Lj)));});},_Ll=function(_Lm){var _Ln=E(_Lm);if(!_Ln._){return E(_L6);}else{var _Lo=new T(function(){return B(_Ll(_Ln.b));}),_Lp=function(_Lq){var _Lr=E(_Lq);if(!_Lr._){return E(_Lo);}else{var _Ls=_Lr.a,_Lt=new T(function(){return B(_Lp(_Lr.b));}),_Lu=new T(function(){return 0.1*E(E(_Ls).e)/1.0e-2;}),_Lv=new T(function(){var _Lw=E(_Ls);if(_Lw.a!=_Lw.b){return E(_L9);}else{return E(_L8);}}),_Lx=function(_Ly,_){var _Lz=E(_Ly),_LA=_Lz.c,_LB=_Lz.d,_LC=E(_Lz.a),_LD=E(_Lz.b),_LE=E(_Ls),_LF=_LE.a,_LG=_LE.b,_LH=E(_LE.c),_LI=_LH.b,_LJ=E(_LH.a),_LK=_LJ.a,_LL=_LJ.b,_LM=_LJ.c,_LN=E(_LE.d),_LO=_LN.b,_LP=E(_LN.a),_LQ=_LP.a,_LR=_LP.b,_LS=_LP.c;if(_LC>_LF){return new F(function(){return _L5(_);});}else{if(_LF>_LD){return new F(function(){return _L5(_);});}else{if(_LC>_LG){return new F(function(){return _L1(_);});}else{if(_LG>_LD){return new F(function(){return _L1(_);});}else{var _LT=_LF-_LC|0;if(0>_LT){return new F(function(){return _Lb(_LA,_LT);});}else{if(_LT>=_LA){return new F(function(){return _Lb(_LA,_LT);});}else{var _LU=E(_LB[_LT]),_LV=E(_LU.c),_LW=_LV.b,_LX=E(_LV.a),_LY=_LX.a,_LZ=_LX.b,_M0=_LX.c,_M1=E(_LU.e),_M2=E(_M1.a),_M3=B(_IE(_ne,_LK,_LL,_LM,_LI,_LY,_LZ,_M0,_LW)),_M4=E(_M3.a),_M5=B(_IE(_ne,_M4.a,_M4.b,_M4.c,_M3.b,_LK,_LL,_LM,_LI)),_M6=E(_M5.a),_M7=_LG-_LC|0;if(0>_M7){return new F(function(){return _Lg(_M7,_LA);});}else{if(_M7>=_LA){return new F(function(){return _Lg(_M7,_LA);});}else{var _M8=E(_LB[_M7]),_M9=E(_M8.c),_Ma=_M9.b,_Mb=E(_M9.a),_Mc=_Mb.a,_Md=_Mb.b,_Me=_Mb.c,_Mf=E(_M8.e),_Mg=E(_Mf.a),_Mh=B(_IE(_ne,_LQ,_LR,_LS,_LO,_Mc,_Md,_Me,_Ma)),_Mi=E(_Mh.a),_Mj=B(_IE(_ne,_Mi.a,_Mi.b,_Mi.c,_Mh.b,_LQ,_LR,_LS,_LO)),_Mk=E(_Mj.a),_Ml=E(_M6.a)+E(_M6.b)+E(_M6.c)+E(_M5.b)+E(_Mk.a)+E(_Mk.b)+E(_Mk.c)+E(_Mj.b);if(!_Ml){var _Mm=B(A2(_Lt,_Lz,_));return new T2(0,new T2(1,_ov,new T(function(){return E(E(_Mm).a);})),new T(function(){return E(E(_Mm).b);}));}else{var _Mn=new T(function(){return  -((B(_Jx(_nK,_M2.a,_M2.b,_M2.c,_M1.b,_LK,_LL,_LM,_LI))-B(_Jx(_nK,_Mg.a,_Mg.b,_Mg.c,_Mf.b,_LQ,_LR,_LS,_LO))-E(_Lu))/_Ml);}),_Mo=function(_Mp,_Mq,_Mr,_Ms,_){var _Mt=new T(function(){var _Mu=function(_Mv,_Mw,_Mx,_My,_Mz){if(_Mv>_LG){return E(_Mz);}else{if(_LG>_Mw){return E(_Mz);}else{var _MA=function(_){var _MB=newArr(_Mx,_me),_MC=_MB,_MD=function(_ME,_){while(1){if(_ME!=_Mx){var _=_MC[_ME]=_My[_ME],_MF=_ME+1|0;_ME=_MF;continue;}else{return E(_);}}},_=B(_MD(0,_)),_MG=_LG-_Mv|0;if(0>_MG){return new F(function(){return _Lg(_MG,_Mx);});}else{if(_MG>=_Mx){return new F(function(){return _Lg(_MG,_Mx);});}else{var _=_MC[_MG]=new T(function(){var _MH=E(_My[_MG]),_MI=E(_MH.e),_MJ=E(_MI.a),_MK=B(_IE(_ne,_Mc,_Md,_Me,_Ma,_LQ,_LR,_LS,_LO)),_ML=E(_MK.a),_MM=E(_Mn)*E(_Lv),_MN=B(_IE(_ne,_ML.a,_ML.b,_ML.c,_MK.b,_MM,_MM,_MM,_MM)),_MO=E(_MN.a),_MP=B(_IP(_ne,_MJ.a,_MJ.b,_MJ.c,_MI.b, -E(_MO.a), -E(_MO.b), -E(_MO.c), -E(_MN.b)));return {_:0,a:E(_MH.a),b:E(_MH.b),c:E(_MH.c),d:E(_MH.d),e:E(new T2(0,E(_MP.a),E(_MP.b))),f:E(_MH.f),g:E(_MH.g),h:_MH.h,i:_MH.i,j:_MH.j};});return new T4(0,E(_Mv),E(_Mw),_Mx,_MC);}}};return new F(function(){return _ES(_MA);});}}};if(_Mp>_LF){return B(_Mu(_Mp,_Mq,_Mr,_Ms,new T4(0,E(_Mp),E(_Mq),_Mr,_Ms)));}else{if(_LF>_Mq){return B(_Mu(_Mp,_Mq,_Mr,_Ms,new T4(0,E(_Mp),E(_Mq),_Mr,_Ms)));}else{var _MQ=function(_){var _MR=newArr(_Mr,_me),_MS=_MR,_MT=function(_MU,_){while(1){if(_MU!=_Mr){var _=_MS[_MU]=_Ms[_MU],_MV=_MU+1|0;_MU=_MV;continue;}else{return E(_);}}},_=B(_MT(0,_)),_MW=_LF-_Mp|0;if(0>_MW){return new F(function(){return _Lb(_Mr,_MW);});}else{if(_MW>=_Mr){return new F(function(){return _Lb(_Mr,_MW);});}else{var _=_MS[_MW]=new T(function(){var _MX=E(_Ms[_MW]),_MY=E(_MX.e),_MZ=E(_MY.a),_N0=B(_IE(_ne,_LY,_LZ,_M0,_LW,_LK,_LL,_LM,_LI)),_N1=E(_N0.a),_N2=E(_Mn)*E(_Lv),_N3=B(_IE(_ne,_N1.a,_N1.b,_N1.c,_N0.b,_N2,_N2,_N2,_N2)),_N4=E(_N3.a),_N5=B(_IP(_ne,_MZ.a,_MZ.b,_MZ.c,_MY.b,_N4.a,_N4.b,_N4.c,_N3.b));return {_:0,a:E(_MX.a),b:E(_MX.b),c:E(_MX.c),d:E(_MX.d),e:E(new T2(0,E(_N5.a),E(_N5.b))),f:E(_MX.f),g:E(_MX.g),h:_MX.h,i:_MX.i,j:_MX.j};});return new T4(0,E(_Mp),E(_Mq),_Mr,_MS);}}},_N6=B(_ES(_MQ));return B(_Mu(E(_N6.a),E(_N6.b),_N6.c,_N6.d,_N6));}}});return new T2(0,_ov,_Mt);};if(!E(_LE.f)){var _N7=B(_Mo(_LC,_LD,_LA,_LB,_)),_N8=B(A2(_Lt,new T(function(){return E(E(_N7).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_N7).a);}),new T(function(){return E(E(_N8).a);})),new T(function(){return E(E(_N8).b);}));}else{if(E(_Mn)<0){var _N9=B(A2(_Lt,_Lz,_));return new T2(0,new T2(1,_ov,new T(function(){return E(E(_N9).a);})),new T(function(){return E(E(_N9).b);}));}else{var _Na=B(_Mo(_LC,_LD,_LA,_LB,_)),_Nb=B(A2(_Lt,new T(function(){return E(E(_Na).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_Na).a);}),new T(function(){return E(E(_Nb).a);})),new T(function(){return E(E(_Nb).b);}));}}}}}}}}}}}};return E(_Lx);}};return new F(function(){return _Lp(_Ln.a);});}},_Nc=function(_,_Nd){var _Ne=new T(function(){return B(_Ll(E(_Nd).a));}),_Nf=function(_Ng){var _Nh=E(_Ng);return (_Nh==1)?E(new T2(1,_Ne,_w)):new T2(1,_Ne,new T(function(){return B(_Nf(_Nh-1|0));}));},_Ni=B(_HQ(B(_Nf(5)),new T(function(){return E(E(_Nd).b);}),_)),_Nj=new T(function(){return B(_Io(_HP,_FE,_Jo,new T(function(){return E(E(_Ni).b);})));});return new T2(0,_ov,_Nj);},_Nk=function(_Nl,_Nm,_Nn,_No,_Np){var _Nq=B(_8J(B(_8H(_Nl))));return new F(function(){return A3(_6X,_Nq,new T(function(){return B(A3(_8L,_Nq,_Nm,_No));}),new T(function(){return B(A3(_8L,_Nq,_Nn,_Np));}));});},_Nr=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Ns=new T6(0,_KW,_KX,_w,_Nr,_KW,_KW),_Nt=new T(function(){return B(_KU(_Ns));}),_Nu=function(_){return new F(function(){return die(_Nt);});},_Nv=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Nw=new T6(0,_KW,_KX,_w,_Nv,_KW,_KW),_Nx=new T(function(){return B(_KU(_Nw));}),_Ny=function(_){return new F(function(){return die(_Nx);});},_Nz=function(_NA,_NB,_NC,_ND){var _NE=new T(function(){return B(_8J(new T(function(){return B(_8H(_NA));})));}),_NF=B(A2(_8s,_NE,_8q));return new F(function(){return _pj(_NA,_NF,B(A2(_8s,_NE,_8r)),_NF);});},_NG=false,_NH=true,_NI=function(_NJ){var _NK=E(_NJ),_NL=_NK.b,_NM=E(_NK.d),_NN=E(_NK.e),_NO=E(_NN.a),_NP=E(_NK.g),_NQ=B(A1(_NL,_NM.a)),_NR=B(_qa(_nK,_NQ.a,_NQ.b,_NQ.c,_NP.a,_NP.b,_NP.c));return {_:0,a:E(_NK.a),b:E(_NL),c:E(_NK.c),d:E(_NM),e:E(new T2(0,E(new T3(0,E(_NO.a)+E(_NR.a)*1.0e-2,E(_NO.b)+E(_NR.b)*1.0e-2,E(_NO.c)+E(_NR.c)*1.0e-2)),E(_NN.b))),f:E(_NK.f),g:E(_NP),h:_NK.h,i:_NK.i,j:_NK.j};},_NS=new T(function(){return eval("__strict(collideBound)");}),_NT=new T(function(){return eval("__strict(mouseContact)");}),_NU=new T(function(){return eval("__strict(collide)");}),_NV=function(_NW){var _NX=E(_NW);if(!_NX._){return __Z;}else{return new F(function(){return _n(_NX.a,new T(function(){return B(_NV(_NX.b));},1));});}},_NY=0,_NZ=new T3(0,E(_NY),E(_NY),E(_NY)),_O0=new T2(0,E(_NZ),E(_NY)),_O1=function(_O2,_){var _O3=B(_Io(_HP,_FE,_NI,_O2)),_O4=E(_O3.a),_O5=E(_O3.b);if(_O4<=_O5){var _O6=function(_O7,_O8,_O9,_Oa,_Ob,_){if(_O8>_O7){return new F(function(){return _Ny(_);});}else{if(_O7>_O9){return new F(function(){return _Ny(_);});}else{var _Oc=new T(function(){var _Od=_O7-_O8|0;if(0>_Od){return B(_Lg(_Od,_Oa));}else{if(_Od>=_Oa){return B(_Lg(_Od,_Oa));}else{return E(_Ob[_Od]);}}}),_Oe=function(_Of,_Og,_Oh,_Oi,_Oj,_){var _Ok=E(_Of);if(!_Ok._){return new T2(0,_w,new T4(0,E(_Og),E(_Oh),_Oi,_Oj));}else{var _Ol=E(_Ok.a);if(_Og>_Ol){return new F(function(){return _Nu(_);});}else{if(_Ol>_Oh){return new F(function(){return _Nu(_);});}else{var _Om=_Ol-_Og|0;if(0>_Om){return new F(function(){return _Lb(_Oi,_Om);});}else{if(_Om>=_Oi){return new F(function(){return _Lb(_Oi,_Om);});}else{var _On=__app2(E(_NU),B(_F2(E(_Oc))),B(_F2(E(_Oj[_Om])))),_Oo=__arr2lst(0,_On),_Op=B(_Gh(_Oo,_)),_Oq=B(_Oe(_Ok.b,_Og,_Oh,_Oi,_Oj,_)),_Or=new T(function(){var _Os=new T(function(){return _O7!=_Ol;}),_Ot=function(_Ou){var _Ov=E(_Ou);if(!_Ov._){return __Z;}else{var _Ow=_Ov.b,_Ox=E(_Ov.a),_Oy=E(_Ox.b),_Oz=E(_Ox.a),_OA=E(_Oz.a),_OB=E(_Oz.b),_OC=E(_Oz.c),_OD=E(_Oy.a),_OE=E(_Oy.b),_OF=E(_Oy.c),_OG=E(_Ox.c),_OH=_OG.a,_OI=_OG.b,_OJ=E(_Ox.e),_OK=E(_Ox.d),_OL=_OK.a,_OM=_OK.b,_ON=E(_Ox.f),_OO=new T(function(){var _OP=B(_pj(_nK,_ON.a,_ON.b,_ON.c)),_OQ=Math.sqrt(B(_Nk(_nK,_OL,_OM,_OL,_OM)));return new T3(0,_OQ*E(_OP.a),_OQ*E(_OP.b),_OQ*E(_OP.c));}),_OR=new T(function(){var _OS=B(_pj(_nK,_OJ.a,_OJ.b,_OJ.c)),_OT=Math.sqrt(B(_Nk(_nK,_OH,_OI,_OH,_OI)));return new T3(0,_OT*E(_OS.a),_OT*E(_OS.b),_OT*E(_OS.c));}),_OU=new T(function(){var _OV=B(_Nz(_nK,_OD,_OE,_OF));return new T3(0,E(_OV.a),E(_OV.b),E(_OV.c));}),_OW=new T(function(){var _OX=B(_Nz(_nK,_OA,_OB,_OC));return new T3(0,E(_OX.a),E(_OX.b),E(_OX.c));}),_OY=_OD+ -_OA,_OZ=_OE+ -_OB,_P0=_OF+ -_OC,_P1=new T(function(){return Math.sqrt(B(_p9(_nK,_OY,_OZ,_P0,_OY,_OZ,_P0)));}),_P2=new T(function(){var _P3=1/E(_P1);return new T3(0,_OY*_P3,_OZ*_P3,_P0*_P3);}),_P4=new T(function(){if(!E(_Ox.g)){return E(_P2);}else{var _P5=E(_P2);return new T3(0,-1*E(_P5.a),-1*E(_P5.b),-1*E(_P5.c));}}),_P6=new T(function(){if(!E(_Ox.h)){return E(_P2);}else{var _P7=E(_P2);return new T3(0,-1*E(_P7.a),-1*E(_P7.b),-1*E(_P7.c));}});return (!E(_Os))?new T2(1,new T(function(){var _P8=E(_P4),_P9=E(_P8.b),_Pa=E(_P8.c),_Pb=E(_P8.a),_Pc=E(_OW),_Pd=E(_Pc.c),_Pe=E(_Pc.b),_Pf=E(_Pc.a),_Pg=E(_OR),_Ph=E(_Pg.c),_Pi=E(_Pg.b),_Pj=E(_Pg.a),_Pk=_P9*_Pd-_Pe*_Pa,_Pl=_Pa*_Pf-_Pd*_Pb,_Pm=_Pb*_Pe-_Pf*_P9,_Pn=B(_p9(_nK,_Pl*_Ph-_Pi*_Pm,_Pm*_Pj-_Ph*_Pk,_Pk*_Pi-_Pj*_Pl,_Pf,_Pe,_Pd));return new T6(0,_O7,_Ol,E(new T2(0,E(new T3(0,E(_Pk),E(_Pl),E(_Pm))),E(_Pn))),E(_O0),_P1,_NG);}),new T2(1,new T(function(){var _Po=E(_P6),_Pp=E(_Po.b),_Pq=E(_Po.c),_Pr=E(_Po.a),_Ps=E(_OU),_Pt=E(_Ps.c),_Pu=E(_Ps.b),_Pv=E(_Ps.a),_Pw=E(_OO),_Px=E(_Pw.c),_Py=E(_Pw.b),_Pz=E(_Pw.a),_PA=_Pp*_Pt-_Pu*_Pq,_PB=_Pq*_Pv-_Pt*_Pr,_PC=_Pr*_Pu-_Pv*_Pp,_PD=B(_p9(_nK,_PB*_Px-_Py*_PC,_PC*_Pz-_Px*_PA,_PA*_Py-_Pz*_PB,_Pv,_Pu,_Pt));return new T6(0,_O7,_Ol,E(_O0),E(new T2(0,E(new T3(0,E(_PA),E(_PB),E(_PC))),E(_PD))),_P1,_NG);}),new T(function(){return B(_Ot(_Ow));}))):new T2(1,new T(function(){var _PE=E(_P4),_PF=E(_PE.b),_PG=E(_PE.c),_PH=E(_PE.a),_PI=E(_OW),_PJ=_PI.a,_PK=_PI.b,_PL=_PI.c,_PM=B(_qa(_nK,_PH,_PF,_PG,_PJ,_PK,_PL)),_PN=E(_OR),_PO=E(_PN.c),_PP=E(_PN.b),_PQ=E(_PN.a),_PR=B(_p9(_nK,_PF*_PO-_PP*_PG,_PG*_PQ-_PO*_PH,_PH*_PP-_PQ*_PF,_PJ,_PK,_PL)),_PS=E(_P6),_PT=E(_PS.b),_PU=E(_PS.c),_PV=E(_PS.a),_PW=E(_OU),_PX=_PW.a,_PY=_PW.b,_PZ=_PW.c,_Q0=B(_qa(_nK,_PV,_PT,_PU,_PX,_PY,_PZ)),_Q1=E(_OO),_Q2=E(_Q1.c),_Q3=E(_Q1.b),_Q4=E(_Q1.a),_Q5=B(_p9(_nK,_PT*_Q2-_Q3*_PU,_PU*_Q4-_Q2*_PV,_PV*_Q3-_Q4*_PT,_PX,_PY,_PZ));return new T6(0,_O7,_Ol,E(new T2(0,E(new T3(0,E(_PM.a),E(_PM.b),E(_PM.c))),E(_PR))),E(new T2(0,E(new T3(0,E(_Q0.a),E(_Q0.b),E(_Q0.c))),E(_Q5))),_P1,_NH);}),new T(function(){return B(_Ot(_Ow));}));}};return B(_Ot(_Op));});return new T2(0,new T2(1,_Or,new T(function(){return E(E(_Oq).a);})),new T(function(){return E(E(_Oq).b);}));}}}}}},_Q6=B(_Oe(B(_wR(_O7,_O5)),_O8,_O9,_Oa,_Ob,_)),_Q7=E(_Oc),_Q8=E(_Q7.d).a,_Q9=__app1(E(_NS),B(_F2(_Q7))),_Qa=__arr2lst(0,_Q9),_Qb=B(_Gh(_Qa,_)),_Qc=__app1(E(_NT),_O7),_Qd=__arr2lst(0,_Qc),_Qe=B(_Gh(_Qd,_));if(_O7!=_O5){var _Qf=E(_Q6),_Qg=E(_Qf.b),_Qh=B(_O6(_O7+1|0,E(_Qg.a),E(_Qg.b),_Qg.c,_Qg.d,_)),_Qi=new T(function(){var _Qj=new T(function(){var _Qk=E(_Q8),_Ql=B(_Nz(_nK,_Qk.a,_Qk.b,_Qk.c));return new T3(0,E(_Ql.a),E(_Ql.b),E(_Ql.c));}),_Qm=new T(function(){var _Qn=new T(function(){return B(_NV(_Qf.a));}),_Qo=function(_Qp){var _Qq=E(_Qp);if(!_Qq._){return E(_Qn);}else{var _Qr=E(_Qq.a),_Qs=E(_Qr.b),_Qt=E(_Qr.a),_Qu=E(_Qt.a),_Qv=E(_Qt.b),_Qw=E(_Qt.c),_Qx=E(_Qr.c),_Qy=_Qx.a,_Qz=_Qx.b,_QA=E(_Qr.e);return new T2(1,new T(function(){var _QB=E(_Qs.a)+ -_Qu,_QC=E(_Qs.b)+ -_Qv,_QD=E(_Qs.c)+ -_Qw,_QE=B(_Nz(_nK,_Qu,_Qv,_Qw)),_QF=_QE.a,_QG=_QE.b,_QH=_QE.c,_QI=Math.sqrt(B(_p9(_nK,_QB,_QC,_QD,_QB,_QC,_QD))),_QJ=1/_QI,_QK=_QB*_QJ,_QL=_QC*_QJ,_QM=_QD*_QJ,_QN=B(_qa(_nK,_QK,_QL,_QM,_QF,_QG,_QH)),_QO=B(_pj(_nK,_QA.a,_QA.b,_QA.c)),_QP=Math.sqrt(B(_Nk(_nK,_Qy,_Qz,_Qy,_Qz))),_QQ=_QP*E(_QO.a),_QR=_QP*E(_QO.b),_QS=_QP*E(_QO.c),_QT=B(_p9(_nK,_QL*_QS-_QR*_QM,_QM*_QQ-_QS*_QK,_QK*_QR-_QQ*_QL,_QF,_QG,_QH));return new T6(0,_O7,_O7,E(new T2(0,E(new T3(0,E(_QN.a),E(_QN.b),E(_QN.c))),E(_QT))),E(_O0),_QI,_NH);}),new T(function(){return B(_Qo(_Qq.b));}));}};return B(_Qo(_Qb));}),_QU=function(_QV){var _QW=E(_QV);if(!_QW._){return E(_Qm);}else{var _QX=E(_QW.a),_QY=E(_QX.b),_QZ=new T(function(){var _R0=E(_Q8),_R1=E(_QY.c)+ -E(_R0.c),_R2=E(_QY.b)+ -E(_R0.b),_R3=E(_QY.a)+ -E(_R0.a),_R4=Math.sqrt(B(_p9(_nK,_R3,_R2,_R1,_R3,_R2,_R1))),_R5=function(_R6,_R7,_R8){var _R9=E(_Qj),_Ra=_R9.a,_Rb=_R9.b,_Rc=_R9.c,_Rd=B(_qa(_nK,_R6,_R7,_R8,_Ra,_Rb,_Rc)),_Re=B(_p9(_nK,_R7*0-0*_R8,_R8*0-0*_R6,_R6*0-0*_R7,_Ra,_Rb,_Rc));return new T6(0,_O7,_O7,new T2(0,E(new T3(0,E(_Rd.a),E(_Rd.b),E(_Rd.c))),E(_Re)),_O0,_R4,_NH);};if(!E(_QX.g)){var _Rf=1/_R4,_Rg=B(_R5(_R3*_Rf,_R2*_Rf,_R1*_Rf));return new T6(0,_Rg.a,_Rg.b,E(_Rg.c),E(_Rg.d),_Rg.e,_Rg.f);}else{var _Rh=1/_R4,_Ri=B(_R5(-1*_R3*_Rh,-1*_R2*_Rh,-1*_R1*_Rh));return new T6(0,_Ri.a,_Ri.b,E(_Ri.c),E(_Ri.d),_Ri.e,_Ri.f);}});return new T2(1,_QZ,new T(function(){return B(_QU(_QW.b));}));}};return B(_QU(_Qe));});return new T2(0,new T2(1,_Qi,new T(function(){return E(E(_Qh).a);})),new T(function(){return E(E(_Qh).b);}));}else{var _Rj=new T(function(){var _Rk=new T(function(){var _Rl=E(_Q8),_Rm=B(_Nz(_nK,_Rl.a,_Rl.b,_Rl.c));return new T3(0,E(_Rm.a),E(_Rm.b),E(_Rm.c));}),_Rn=new T(function(){var _Ro=new T(function(){return B(_NV(E(_Q6).a));}),_Rp=function(_Rq){var _Rr=E(_Rq);if(!_Rr._){return E(_Ro);}else{var _Rs=E(_Rr.a),_Rt=E(_Rs.b),_Ru=E(_Rs.a),_Rv=E(_Ru.a),_Rw=E(_Ru.b),_Rx=E(_Ru.c),_Ry=E(_Rs.c),_Rz=_Ry.a,_RA=_Ry.b,_RB=E(_Rs.e);return new T2(1,new T(function(){var _RC=E(_Rt.a)+ -_Rv,_RD=E(_Rt.b)+ -_Rw,_RE=E(_Rt.c)+ -_Rx,_RF=B(_Nz(_nK,_Rv,_Rw,_Rx)),_RG=_RF.a,_RH=_RF.b,_RI=_RF.c,_RJ=Math.sqrt(B(_p9(_nK,_RC,_RD,_RE,_RC,_RD,_RE))),_RK=1/_RJ,_RL=_RC*_RK,_RM=_RD*_RK,_RN=_RE*_RK,_RO=B(_qa(_nK,_RL,_RM,_RN,_RG,_RH,_RI)),_RP=B(_pj(_nK,_RB.a,_RB.b,_RB.c)),_RQ=Math.sqrt(B(_Nk(_nK,_Rz,_RA,_Rz,_RA))),_RR=_RQ*E(_RP.a),_RS=_RQ*E(_RP.b),_RT=_RQ*E(_RP.c),_RU=B(_p9(_nK,_RM*_RT-_RS*_RN,_RN*_RR-_RT*_RL,_RL*_RS-_RR*_RM,_RG,_RH,_RI));return new T6(0,_O7,_O7,E(new T2(0,E(new T3(0,E(_RO.a),E(_RO.b),E(_RO.c))),E(_RU))),E(_O0),_RJ,_NH);}),new T(function(){return B(_Rp(_Rr.b));}));}};return B(_Rp(_Qb));}),_RV=function(_RW){var _RX=E(_RW);if(!_RX._){return E(_Rn);}else{var _RY=E(_RX.a),_RZ=E(_RY.b),_S0=new T(function(){var _S1=E(_Q8),_S2=E(_RZ.c)+ -E(_S1.c),_S3=E(_RZ.b)+ -E(_S1.b),_S4=E(_RZ.a)+ -E(_S1.a),_S5=Math.sqrt(B(_p9(_nK,_S4,_S3,_S2,_S4,_S3,_S2))),_S6=function(_S7,_S8,_S9){var _Sa=E(_Rk),_Sb=_Sa.a,_Sc=_Sa.b,_Sd=_Sa.c,_Se=B(_qa(_nK,_S7,_S8,_S9,_Sb,_Sc,_Sd)),_Sf=B(_p9(_nK,_S8*0-0*_S9,_S9*0-0*_S7,_S7*0-0*_S8,_Sb,_Sc,_Sd));return new T6(0,_O7,_O7,new T2(0,E(new T3(0,E(_Se.a),E(_Se.b),E(_Se.c))),E(_Sf)),_O0,_S5,_NH);};if(!E(_RY.g)){var _Sg=1/_S5,_Sh=B(_S6(_S4*_Sg,_S3*_Sg,_S2*_Sg));return new T6(0,_Sh.a,_Sh.b,E(_Sh.c),E(_Sh.d),_Sh.e,_Sh.f);}else{var _Si=1/_S5,_Sj=B(_S6(-1*_S4*_Si,-1*_S3*_Si,-1*_S2*_Si));return new T6(0,_Sj.a,_Sj.b,E(_Sj.c),E(_Sj.d),_Sj.e,_Sj.f);}});return new T2(1,_S0,new T(function(){return B(_RV(_RX.b));}));}};return B(_RV(_Qe));});return new T2(0,new T2(1,_Rj,_w),new T(function(){return E(E(_Q6).b);}));}}}},_Sk=B(_O6(_O4,_O4,_O5,_O3.c,_O3.d,_));return new F(function(){return _Nc(_,_Sk);});}else{return new F(function(){return _Nc(_,new T2(0,_w,_O3));});}},_Sl=new T(function(){return eval("__strict(passObject)");}),_Sm=new T(function(){return eval("__strict(refresh)");}),_Sn=function(_So,_){var _Sp=__app0(E(_Sm)),_Sq=__app0(E(_F7)),_Sr=E(_So),_Ss=_Sr.c,_St=_Sr.d,_Su=E(_Sr.a),_Sv=E(_Sr.b);if(_Su<=_Sv){if(_Su>_Sv){return E(_F5);}else{if(0>=_Ss){return new F(function(){return _Fi(_Ss,0);});}else{var _Sw=E(_Sl),_Sx=__app2(_Sw,_Su,B(_F2(E(_St[0]))));if(_Su!=_Sv){var _Sy=function(_Sz,_){if(_Su>_Sz){return E(_F5);}else{if(_Sz>_Sv){return E(_F5);}else{var _SA=_Sz-_Su|0;if(0>_SA){return new F(function(){return _Fi(_Ss,_SA);});}else{if(_SA>=_Ss){return new F(function(){return _Fi(_Ss,_SA);});}else{var _SB=__app2(_Sw,_Sz,B(_F2(E(_St[_SA]))));if(_Sz!=_Sv){var _SC=B(_Sy(_Sz+1|0,_));return new T2(1,_ov,_SC);}else{return _Fn;}}}}}},_SD=B(_Sy(_Su+1|0,_)),_SE=__app0(E(_F6)),_SF=B(_O1(_Sr,_));return new T(function(){return E(E(_SF).b);});}else{var _SG=__app0(E(_F6)),_SH=B(_O1(_Sr,_));return new T(function(){return E(E(_SH).b);});}}}}else{var _SI=__app0(E(_F6)),_SJ=B(_O1(_Sr,_));return new T(function(){return E(E(_SJ).b);});}},_SK=function(_SL,_){while(1){var _SM=E(_SL);if(!_SM._){return _ov;}else{var _SN=_SM.b,_SO=E(_SM.a);switch(_SO._){case 0:var _SP=B(A1(_SO.a,_));_SL=B(_n(_SN,new T2(1,_SP,_w)));continue;case 1:_SL=B(_n(_SN,_SO.a));continue;default:_SL=_SN;continue;}}}},_SQ=function(_SR,_SS,_){var _ST=E(_SR);switch(_ST._){case 0:var _SU=B(A1(_ST.a,_));return new F(function(){return _SK(B(_n(_SS,new T2(1,_SU,_w))),_);});break;case 1:return new F(function(){return _SK(B(_n(_SS,_ST.a)),_);});break;default:return new F(function(){return _SK(_SS,_);});}},_SV=new T0(2),_SW=function(_SX){return new T0(2);},_SY=function(_SZ,_T0,_T1){return function(_){var _T2=E(_SZ),_T3=rMV(_T2),_T4=E(_T3);if(!_T4._){var _T5=new T(function(){var _T6=new T(function(){return B(A1(_T1,_ov));});return B(_n(_T4.b,new T2(1,new T2(0,_T0,function(_T7){return E(_T6);}),_w)));}),_=wMV(_T2,new T2(0,_T4.a,_T5));return _SV;}else{var _T8=E(_T4.a);if(!_T8._){var _=wMV(_T2,new T2(0,_T0,_w));return new T(function(){return B(A1(_T1,_ov));});}else{var _=wMV(_T2,new T1(1,_T8.b));return new T1(1,new T2(1,new T(function(){return B(A1(_T1,_ov));}),new T2(1,new T(function(){return B(A2(_T8.a,_T0,_SW));}),_w)));}}};},_T9=new T(function(){return E(_uo);}),_Ta=new T(function(){return eval("window.requestAnimationFrame");}),_Tb=new T1(1,_w),_Tc=function(_Td,_Te){return function(_){var _Tf=E(_Td),_Tg=rMV(_Tf),_Th=E(_Tg);if(!_Th._){var _Ti=_Th.a,_Tj=E(_Th.b);if(!_Tj._){var _=wMV(_Tf,_Tb);return new T(function(){return B(A1(_Te,_Ti));});}else{var _Tk=E(_Tj.a),_=wMV(_Tf,new T2(0,_Tk.a,_Tj.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Te,_Ti));}),new T2(1,new T(function(){return B(A1(_Tk.b,_SW));}),_w)));}}else{var _Tl=new T(function(){var _Tm=function(_Tn){var _To=new T(function(){return B(A1(_Te,_Tn));});return function(_Tp){return E(_To);};};return B(_n(_Th.a,new T2(1,_Tm,_w)));}),_=wMV(_Tf,new T1(1,_Tl));return _SV;}};},_Tq=function(_Tr,_Ts){return new T1(0,B(_Tc(_Tr,_Ts)));},_Tt=function(_Tu,_Tv){var _Tw=new T(function(){return new T1(0,B(_SY(_Tu,_ov,_SW)));});return function(_){var _Tx=__createJSFunc(2,function(_Ty,_){var _Tz=B(_SQ(_Tw,_w,_));return _T9;}),_TA=__app1(E(_Ta),_Tx);return new T(function(){return B(_Tq(_Tu,_Tv));});};},_TB=new T1(1,_w),_TC=function(_TD,_TE,_){var _TF=function(_){var _TG=nMV(_TD),_TH=_TG;return new T(function(){var _TI=new T(function(){return B(_TJ(_));}),_TK=function(_){var _TL=rMV(_TH),_TM=B(A2(_TE,_TL,_)),_=wMV(_TH,_TM),_TN=function(_){var _TO=nMV(_TB);return new T(function(){return new T1(0,B(_Tt(_TO,function(_TP){return E(_TI);})));});};return new T1(0,_TN);},_TQ=new T(function(){return new T1(0,_TK);}),_TJ=function(_TR){return E(_TQ);};return B(_TJ(_));});};return new F(function(){return _SQ(new T1(0,_TF),_w,_);});},_TS=new T(function(){return eval("__strict(setBounds)");}),_TT=function(_){var _TU=__app3(E(_lD),E(_lE),E(_m7),E(_lC)),_TV=__app2(E(_TS),E(_iS),E(_iP));return new F(function(){return _TC(_EV,_Sn,_);});},_TW=function(_){return new F(function(){return _TT(_);});};
var hasteMain = function() {B(A(_TW, [0]));};window.onload = hasteMain;