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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=new T(function(){return eval("compile");}),_i=function(_j){return E(E(_j).b);},_k=function(_l){return E(E(_l).a);},_m=function(_n,_o,_p){var _q=E(_p);if(!_q._){return new F(function(){return A1(_o,_q.a);});}else{var _r=new T(function(){return B(_i(_n));}),_s=new T(function(){return B(_k(_n));}),_t=function(_u){var _v=E(_u);if(!_v._){return E(_s);}else{return new F(function(){return A2(_r,new T(function(){return B(_m(_n,_o,_v.a));}),new T(function(){return B(_t(_v.b));}));});}};return new F(function(){return _t(_q.a);});}},_w=function(_x){var _y=E(_x);if(!_y._){return __Z;}else{return new F(function(){return _0(_y.a,new T(function(){return B(_w(_y.b));},1));});}},_z=function(_A){return new F(function(){return _w(_A);});},_B=new T3(0,_4,_0,_z),_C=new T(function(){return B(unCStr(","));}),_D=new T1(0,_C),_E=new T(function(){return B(unCStr("pow("));}),_F=new T1(0,_E),_G=new T(function(){return B(unCStr(")"));}),_H=new T1(0,_G),_I=new T2(1,_H,_4),_J=function(_K,_L){return new T1(1,new T2(1,_F,new T2(1,_K,new T2(1,_D,new T2(1,_L,_I)))));},_M=new T(function(){return B(unCStr("acos("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_I)));},_Q=new T(function(){return B(unCStr("acosh("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_I)));},_U=new T(function(){return B(unCStr("asin("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_I)));},_Y=new T(function(){return B(unCStr("asinh("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_I)));},_12=new T(function(){return B(unCStr("atan("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_I)));},_16=new T(function(){return B(unCStr("atanh("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_I)));},_1a=new T(function(){return B(unCStr("cos("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_I)));},_1e=new T(function(){return B(unCStr("cosh("));}),_1f=new T1(0,_1e),_1g=function(_1h){return new T1(1,new T2(1,_1f,new T2(1,_1h,_I)));},_1i=new T(function(){return B(unCStr("exp("));}),_1j=new T1(0,_1i),_1k=function(_1l){return new T1(1,new T2(1,_1j,new T2(1,_1l,_I)));},_1m=new T(function(){return B(unCStr("log("));}),_1n=new T1(0,_1m),_1o=function(_1p){return new T1(1,new T2(1,_1n,new T2(1,_1p,_I)));},_1q=new T(function(){return B(unCStr(")/log("));}),_1r=new T1(0,_1q),_1s=function(_1t,_1u){return new T1(1,new T2(1,_1n,new T2(1,_1u,new T2(1,_1r,new T2(1,_1t,_I)))));},_1v=new T(function(){return B(unCStr("pi"));}),_1w=new T1(0,_1v),_1x=new T(function(){return B(unCStr("sin("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_I)));},_1B=new T(function(){return B(unCStr("sinh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_I)));},_1F=new T(function(){return B(unCStr("sqrt("));}),_1G=new T1(0,_1F),_1H=function(_1I){return new T1(1,new T2(1,_1G,new T2(1,_1I,_I)));},_1J=new T(function(){return B(unCStr("tan("));}),_1K=new T1(0,_1J),_1L=function(_1M){return new T1(1,new T2(1,_1K,new T2(1,_1M,_I)));},_1N=new T(function(){return B(unCStr("tanh("));}),_1O=new T1(0,_1N),_1P=function(_1Q){return new T1(1,new T2(1,_1O,new T2(1,_1Q,_I)));},_1R=new T(function(){return B(unCStr("("));}),_1S=new T1(0,_1R),_1T=new T(function(){return B(unCStr(")/("));}),_1U=new T1(0,_1T),_1V=function(_1W,_1X){return new T1(1,new T2(1,_1S,new T2(1,_1W,new T2(1,_1U,new T2(1,_1X,_I)))));},_1Y=new T1(0,1),_1Z=function(_20,_21){var _22=E(_20);if(!_22._){var _23=_22.a,_24=E(_21);if(!_24._){var _25=_24.a;return (_23!=_25)?(_23>_25)?2:0:1;}else{var _26=I_compareInt(_24.a,_23);return (_26<=0)?(_26>=0)?1:2:0;}}else{var _27=_22.a,_28=E(_21);if(!_28._){var _29=I_compareInt(_27,_28.a);return (_29>=0)?(_29<=0)?1:2:0;}else{var _2a=I_compare(_27,_28.a);return (_2a>=0)?(_2a<=0)?1:2:0;}}},_2b=new T(function(){return B(unCStr("base"));}),_2c=new T(function(){return B(unCStr("GHC.Exception"));}),_2d=new T(function(){return B(unCStr("ArithException"));}),_2e=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2b,_2c,_2d),_2f=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_4,_4),_2g=function(_2h){return E(_2f);},_2i=function(_2j){return E(E(_2j).a);},_2k=function(_2l,_2m,_2n){var _2o=B(A1(_2l,_)),_2p=B(A1(_2m,_)),_2q=hs_eqWord64(_2o.a,_2p.a);if(!_2q){return __Z;}else{var _2r=hs_eqWord64(_2o.b,_2p.b);return (!_2r)?__Z:new T1(1,_2n);}},_2s=function(_2t){var _2u=E(_2t);return new F(function(){return _2k(B(_2i(_2u.a)),_2g,_2u.b);});},_2v=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2w=new T(function(){return B(unCStr("denormal"));}),_2x=new T(function(){return B(unCStr("divide by zero"));}),_2y=new T(function(){return B(unCStr("loss of precision"));}),_2z=new T(function(){return B(unCStr("arithmetic underflow"));}),_2A=new T(function(){return B(unCStr("arithmetic overflow"));}),_2B=function(_2C,_2D){switch(E(_2C)){case 0:return new F(function(){return _0(_2A,_2D);});break;case 1:return new F(function(){return _0(_2z,_2D);});break;case 2:return new F(function(){return _0(_2y,_2D);});break;case 3:return new F(function(){return _0(_2x,_2D);});break;case 4:return new F(function(){return _0(_2w,_2D);});break;default:return new F(function(){return _0(_2v,_2D);});}},_2E=function(_2F){return new F(function(){return _2B(_2F,_4);});},_2G=function(_2H,_2I,_2J){return new F(function(){return _2B(_2I,_2J);});},_2K=44,_2L=93,_2M=91,_2N=function(_2O,_2P,_2Q){var _2R=E(_2P);if(!_2R._){return new F(function(){return unAppCStr("[]",_2Q);});}else{var _2S=new T(function(){var _2T=new T(function(){var _2U=function(_2V){var _2W=E(_2V);if(!_2W._){return E(new T2(1,_2L,_2Q));}else{var _2X=new T(function(){return B(A2(_2O,_2W.a,new T(function(){return B(_2U(_2W.b));})));});return new T2(1,_2K,_2X);}};return B(_2U(_2R.b));});return B(A2(_2O,_2R.a,_2T));});return new T2(1,_2M,_2S);}},_2Y=function(_2Z,_30){return new F(function(){return _2N(_2B,_2Z,_30);});},_31=new T3(0,_2G,_2E,_2Y),_32=new T(function(){return new T5(0,_2g,_31,_33,_2s,_2E);}),_33=function(_34){return new T2(0,_32,_34);},_35=3,_36=new T(function(){return B(_33(_35));}),_37=new T(function(){return die(_36);}),_38=function(_39,_3a){var _3b=E(_39);return (_3b._==0)?_3b.a*Math.pow(2,_3a):I_toNumber(_3b.a)*Math.pow(2,_3a);},_3c=function(_3d,_3e){var _3f=E(_3d);if(!_3f._){var _3g=_3f.a,_3h=E(_3e);return (_3h._==0)?_3g==_3h.a:(I_compareInt(_3h.a,_3g)==0)?true:false;}else{var _3i=_3f.a,_3j=E(_3e);return (_3j._==0)?(I_compareInt(_3i,_3j.a)==0)?true:false:(I_compare(_3i,_3j.a)==0)?true:false;}},_3k=function(_3l){var _3m=E(_3l);if(!_3m._){return E(_3m.a);}else{return new F(function(){return I_toInt(_3m.a);});}},_3n=function(_3o,_3p){while(1){var _3q=E(_3o);if(!_3q._){var _3r=_3q.a,_3s=E(_3p);if(!_3s._){var _3t=_3s.a,_3u=addC(_3r,_3t);if(!E(_3u.b)){return new T1(0,_3u.a);}else{_3o=new T1(1,I_fromInt(_3r));_3p=new T1(1,I_fromInt(_3t));continue;}}else{_3o=new T1(1,I_fromInt(_3r));_3p=_3s;continue;}}else{var _3v=E(_3p);if(!_3v._){_3o=_3q;_3p=new T1(1,I_fromInt(_3v.a));continue;}else{return new T1(1,I_add(_3q.a,_3v.a));}}}},_3w=function(_3x,_3y){while(1){var _3z=E(_3x);if(!_3z._){var _3A=E(_3z.a);if(_3A==(-2147483648)){_3x=new T1(1,I_fromInt(-2147483648));continue;}else{var _3B=E(_3y);if(!_3B._){var _3C=_3B.a;return new T2(0,new T1(0,quot(_3A,_3C)),new T1(0,_3A%_3C));}else{_3x=new T1(1,I_fromInt(_3A));_3y=_3B;continue;}}}else{var _3D=E(_3y);if(!_3D._){_3x=_3z;_3y=new T1(1,I_fromInt(_3D.a));continue;}else{var _3E=I_quotRem(_3z.a,_3D.a);return new T2(0,new T1(1,_3E.a),new T1(1,_3E.b));}}}},_3F=new T1(0,0),_3G=function(_3H,_3I){while(1){var _3J=E(_3H);if(!_3J._){_3H=new T1(1,I_fromInt(_3J.a));continue;}else{return new T1(1,I_shiftLeft(_3J.a,_3I));}}},_3K=function(_3L,_3M,_3N){if(!B(_3c(_3N,_3F))){var _3O=B(_3w(_3M,_3N)),_3P=_3O.a;switch(B(_1Z(B(_3G(_3O.b,1)),_3N))){case 0:return new F(function(){return _38(_3P,_3L);});break;case 1:if(!(B(_3k(_3P))&1)){return new F(function(){return _38(_3P,_3L);});}else{return new F(function(){return _38(B(_3n(_3P,_1Y)),_3L);});}break;default:return new F(function(){return _38(B(_3n(_3P,_1Y)),_3L);});}}else{return E(_37);}},_3Q=function(_3R,_3S){var _3T=E(_3R);if(!_3T._){var _3U=_3T.a,_3V=E(_3S);return (_3V._==0)?_3U>_3V.a:I_compareInt(_3V.a,_3U)<0;}else{var _3W=_3T.a,_3X=E(_3S);return (_3X._==0)?I_compareInt(_3W,_3X.a)>0:I_compare(_3W,_3X.a)>0;}},_3Y=new T1(0,1),_3Z=function(_40,_41){var _42=E(_40);if(!_42._){var _43=_42.a,_44=E(_41);return (_44._==0)?_43<_44.a:I_compareInt(_44.a,_43)>0;}else{var _45=_42.a,_46=E(_41);return (_46._==0)?I_compareInt(_45,_46.a)<0:I_compare(_45,_46.a)<0;}},_47=new T(function(){return B(unCStr("base"));}),_48=new T(function(){return B(unCStr("Control.Exception.Base"));}),_49=new T(function(){return B(unCStr("PatternMatchFail"));}),_4a=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_47,_48,_49),_4b=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4,_4),_4c=function(_4d){return E(_4b);},_4e=function(_4f){var _4g=E(_4f);return new F(function(){return _2k(B(_2i(_4g.a)),_4c,_4g.b);});},_4h=function(_4i){return E(E(_4i).a);},_4j=function(_4k){return new T2(0,_4l,_4k);},_4m=function(_4n,_4o){return new F(function(){return _0(E(_4n).a,_4o);});},_4p=function(_4q,_4r){return new F(function(){return _2N(_4m,_4q,_4r);});},_4s=function(_4t,_4u,_4v){return new F(function(){return _0(E(_4u).a,_4v);});},_4w=new T3(0,_4s,_4h,_4p),_4l=new T(function(){return new T5(0,_4c,_4w,_4j,_4e,_4h);}),_4x=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4y=function(_4z){return E(E(_4z).c);},_4A=function(_4B,_4C){return new F(function(){return die(new T(function(){return B(A2(_4y,_4C,_4B));}));});},_4D=function(_4E,_34){return new F(function(){return _4A(_4E,_34);});},_4F=function(_4G,_4H){var _4I=E(_4H);if(!_4I._){return new T2(0,_4,_4);}else{var _4J=_4I.a;if(!B(A1(_4G,_4J))){return new T2(0,_4,_4I);}else{var _4K=new T(function(){var _4L=B(_4F(_4G,_4I.b));return new T2(0,_4L.a,_4L.b);});return new T2(0,new T2(1,_4J,new T(function(){return E(E(_4K).a);})),new T(function(){return E(E(_4K).b);}));}}},_4M=32,_4N=new T(function(){return B(unCStr("\n"));}),_4O=function(_4P){return (E(_4P)==124)?false:true;},_4Q=function(_4R,_4S){var _4T=B(_4F(_4O,B(unCStr(_4R)))),_4U=_4T.a,_4V=function(_4W,_4X){var _4Y=new T(function(){var _4Z=new T(function(){return B(_0(_4S,new T(function(){return B(_0(_4X,_4N));},1)));});return B(unAppCStr(": ",_4Z));},1);return new F(function(){return _0(_4W,_4Y);});},_50=E(_4T.b);if(!_50._){return new F(function(){return _4V(_4U,_4);});}else{if(E(_50.a)==124){return new F(function(){return _4V(_4U,new T2(1,_4M,_50.b));});}else{return new F(function(){return _4V(_4U,_4);});}}},_51=function(_52){return new F(function(){return _4D(new T1(0,new T(function(){return B(_4Q(_52,_4x));})),_4l);});},_53=function(_54){var _55=function(_56,_57){while(1){if(!B(_3Z(_56,_54))){if(!B(_3Q(_56,_54))){if(!B(_3c(_56,_54))){return new F(function(){return _51("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_57);}}else{return _57-1|0;}}else{var _58=B(_3G(_56,1)),_59=_57+1|0;_56=_58;_57=_59;continue;}}};return new F(function(){return _55(_3Y,0);});},_5a=function(_5b){var _5c=E(_5b);if(!_5c._){var _5d=_5c.a>>>0;if(!_5d){return -1;}else{var _5e=function(_5f,_5g){while(1){if(_5f>=_5d){if(_5f<=_5d){if(_5f!=_5d){return new F(function(){return _51("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5g);}}else{return _5g-1|0;}}else{var _5h=imul(_5f,2)>>>0,_5i=_5g+1|0;_5f=_5h;_5g=_5i;continue;}}};return new F(function(){return _5e(1,0);});}}else{return new F(function(){return _53(_5c);});}},_5j=function(_5k){var _5l=E(_5k);if(!_5l._){var _5m=_5l.a>>>0;if(!_5m){return new T2(0,-1,0);}else{var _5n=function(_5o,_5p){while(1){if(_5o>=_5m){if(_5o<=_5m){if(_5o!=_5m){return new F(function(){return _51("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5p);}}else{return _5p-1|0;}}else{var _5q=imul(_5o,2)>>>0,_5r=_5p+1|0;_5o=_5q;_5p=_5r;continue;}}};return new T2(0,B(_5n(1,0)),(_5m&_5m-1>>>0)>>>0&4294967295);}}else{var _5s=_5l.a;return new T2(0,B(_5a(_5l)),I_compareInt(I_and(_5s,I_sub(_5s,I_fromInt(1))),0));}},_5t=function(_5u,_5v){var _5w=E(_5u);if(!_5w._){var _5x=_5w.a,_5y=E(_5v);return (_5y._==0)?_5x<=_5y.a:I_compareInt(_5y.a,_5x)>=0;}else{var _5z=_5w.a,_5A=E(_5v);return (_5A._==0)?I_compareInt(_5z,_5A.a)<=0:I_compare(_5z,_5A.a)<=0;}},_5B=function(_5C,_5D){while(1){var _5E=E(_5C);if(!_5E._){var _5F=_5E.a,_5G=E(_5D);if(!_5G._){return new T1(0,(_5F>>>0&_5G.a>>>0)>>>0&4294967295);}else{_5C=new T1(1,I_fromInt(_5F));_5D=_5G;continue;}}else{var _5H=E(_5D);if(!_5H._){_5C=_5E;_5D=new T1(1,I_fromInt(_5H.a));continue;}else{return new T1(1,I_and(_5E.a,_5H.a));}}}},_5I=function(_5J,_5K){while(1){var _5L=E(_5J);if(!_5L._){var _5M=_5L.a,_5N=E(_5K);if(!_5N._){var _5O=_5N.a,_5P=subC(_5M,_5O);if(!E(_5P.b)){return new T1(0,_5P.a);}else{_5J=new T1(1,I_fromInt(_5M));_5K=new T1(1,I_fromInt(_5O));continue;}}else{_5J=new T1(1,I_fromInt(_5M));_5K=_5N;continue;}}else{var _5Q=E(_5K);if(!_5Q._){_5J=_5L;_5K=new T1(1,I_fromInt(_5Q.a));continue;}else{return new T1(1,I_sub(_5L.a,_5Q.a));}}}},_5R=new T1(0,2),_5S=function(_5T,_5U){var _5V=E(_5T);if(!_5V._){var _5W=(_5V.a>>>0&(2<<_5U>>>0)-1>>>0)>>>0,_5X=1<<_5U>>>0;return (_5X<=_5W)?(_5X>=_5W)?1:2:0;}else{var _5Y=B(_5B(_5V,B(_5I(B(_3G(_5R,_5U)),_3Y)))),_5Z=B(_3G(_3Y,_5U));return (!B(_3Q(_5Z,_5Y)))?(!B(_3Z(_5Z,_5Y)))?1:2:0;}},_60=function(_61,_62){while(1){var _63=E(_61);if(!_63._){_61=new T1(1,I_fromInt(_63.a));continue;}else{return new T1(1,I_shiftRight(_63.a,_62));}}},_64=function(_65,_66,_67,_68){var _69=B(_5j(_68)),_6a=_69.a;if(!E(_69.b)){var _6b=B(_5a(_67));if(_6b<((_6a+_65|0)-1|0)){var _6c=_6a+(_65-_66|0)|0;if(_6c>0){if(_6c>_6b){if(_6c<=(_6b+1|0)){if(!E(B(_5j(_67)).b)){return 0;}else{return new F(function(){return _38(_1Y,_65-_66|0);});}}else{return 0;}}else{var _6d=B(_60(_67,_6c));switch(B(_5S(_67,_6c-1|0))){case 0:return new F(function(){return _38(_6d,_65-_66|0);});break;case 1:if(!(B(_3k(_6d))&1)){return new F(function(){return _38(_6d,_65-_66|0);});}else{return new F(function(){return _38(B(_3n(_6d,_1Y)),_65-_66|0);});}break;default:return new F(function(){return _38(B(_3n(_6d,_1Y)),_65-_66|0);});}}}else{return new F(function(){return _38(_67,(_65-_66|0)-_6c|0);});}}else{if(_6b>=_66){var _6e=B(_60(_67,(_6b+1|0)-_66|0));switch(B(_5S(_67,_6b-_66|0))){case 0:return new F(function(){return _38(_6e,((_6b-_6a|0)+1|0)-_66|0);});break;case 2:return new F(function(){return _38(B(_3n(_6e,_1Y)),((_6b-_6a|0)+1|0)-_66|0);});break;default:if(!(B(_3k(_6e))&1)){return new F(function(){return _38(_6e,((_6b-_6a|0)+1|0)-_66|0);});}else{return new F(function(){return _38(B(_3n(_6e,_1Y)),((_6b-_6a|0)+1|0)-_66|0);});}}}else{return new F(function(){return _38(_67, -_6a);});}}}else{var _6f=B(_5a(_67))-_6a|0,_6g=function(_6h){var _6i=function(_6j,_6k){if(!B(_5t(B(_3G(_6k,_66)),_6j))){return new F(function(){return _3K(_6h-_66|0,_6j,_6k);});}else{return new F(function(){return _3K((_6h-_66|0)+1|0,_6j,B(_3G(_6k,1)));});}};if(_6h>=_66){if(_6h!=_66){return new F(function(){return _6i(_67,new T(function(){return B(_3G(_68,_6h-_66|0));}));});}else{return new F(function(){return _6i(_67,_68);});}}else{return new F(function(){return _6i(new T(function(){return B(_3G(_67,_66-_6h|0));}),_68);});}};if(_65>_6f){return new F(function(){return _6g(_65);});}else{return new F(function(){return _6g(_6f);});}}},_6l=new T1(0,2147483647),_6m=new T(function(){return B(_3n(_6l,_3Y));}),_6n=function(_6o){var _6p=E(_6o);if(!_6p._){var _6q=E(_6p.a);return (_6q==(-2147483648))?E(_6m):new T1(0, -_6q);}else{return new T1(1,I_negate(_6p.a));}},_6r=new T(function(){return 0/0;}),_6s=new T(function(){return -1/0;}),_6t=new T(function(){return 1/0;}),_6u=0,_6v=function(_6w,_6x){if(!B(_3c(_6x,_3F))){if(!B(_3c(_6w,_3F))){if(!B(_3Z(_6w,_3F))){return new F(function(){return _64(-1021,53,_6w,_6x);});}else{return  -B(_64(-1021,53,B(_6n(_6w)),_6x));}}else{return E(_6u);}}else{return (!B(_3c(_6w,_3F)))?(!B(_3Z(_6w,_3F)))?E(_6t):E(_6s):E(_6r);}},_6y=function(_6z){return new T1(0,new T(function(){var _6A=E(_6z),_6B=jsShow(B(_6v(_6A.a,_6A.b)));return fromJSStr(_6B);}));},_6C=new T(function(){return B(unCStr("1./("));}),_6D=new T1(0,_6C),_6E=function(_6F){return new T1(1,new T2(1,_6D,new T2(1,_6F,_I)));},_6G=new T(function(){return B(unCStr(")+("));}),_6H=new T1(0,_6G),_6I=function(_6J,_6K){return new T1(1,new T2(1,_1S,new T2(1,_6J,new T2(1,_6H,new T2(1,_6K,_I)))));},_6L=new T(function(){return B(unCStr("-("));}),_6M=new T1(0,_6L),_6N=function(_6O){return new T1(1,new T2(1,_6M,new T2(1,_6O,_I)));},_6P=new T(function(){return B(unCStr(")*("));}),_6Q=new T1(0,_6P),_6R=function(_6S,_6T){return new T1(1,new T2(1,_1S,new T2(1,_6S,new T2(1,_6Q,new T2(1,_6T,_I)))));},_6U=function(_6V){return E(E(_6V).a);},_6W=function(_6X){return E(E(_6X).d);},_6Y=function(_6Z,_70){return new F(function(){return A3(_6U,_71,_6Z,new T(function(){return B(A2(_6W,_71,_70));}));});},_72=new T(function(){return B(unCStr("abs("));}),_73=new T1(0,_72),_74=function(_75){return new T1(1,new T2(1,_73,new T2(1,_75,_I)));},_76=function(_77){while(1){var _78=E(_77);if(!_78._){_77=new T1(1,I_fromInt(_78.a));continue;}else{return new F(function(){return I_toString(_78.a);});}}},_79=function(_7a,_7b){return new F(function(){return _0(fromJSStr(B(_76(_7a))),_7b);});},_7c=41,_7d=40,_7e=new T1(0,0),_7f=function(_7g,_7h,_7i){if(_7g<=6){return new F(function(){return _79(_7h,_7i);});}else{if(!B(_3Z(_7h,_7e))){return new F(function(){return _79(_7h,_7i);});}else{return new T2(1,_7d,new T(function(){return B(_0(fromJSStr(B(_76(_7h))),new T2(1,_7c,_7i)));}));}}},_7j=new T(function(){return B(unCStr("."));}),_7k=function(_7l){return new T1(0,new T(function(){return B(_0(B(_7f(0,_7l,_4)),_7j));}));},_7m=new T(function(){return B(unCStr("sign("));}),_7n=new T1(0,_7m),_7o=function(_7p){return new T1(1,new T2(1,_7n,new T2(1,_7p,_I)));},_71=new T(function(){return {_:0,a:_6I,b:_6Y,c:_6R,d:_6N,e:_74,f:_7o,g:_7k};}),_7q=new T4(0,_71,_1V,_6E,_6y),_7r={_:0,a:_7q,b:_1w,c:_1k,d:_1o,e:_1H,f:_J,g:_1s,h:_1z,i:_1c,j:_1L,k:_W,l:_O,m:_14,n:_1D,o:_1g,p:_1P,q:_10,r:_S,s:_18},_7s=function(_7t){return E(E(_7t).a);},_7u=function(_7v){return E(E(_7v).a);},_7w=function(_7x){return E(E(_7x).c);},_7y=function(_7z){return E(E(_7z).b);},_7A=function(_7B){return E(E(_7B).d);},_7C=new T1(0,1),_7D=new T1(0,2),_7E=new T2(0,E(_7C),E(_7D)),_7F=new T1(0,5),_7G=new T1(0,4),_7H=new T2(0,E(_7G),E(_7F)),_7I=function(_7J){return E(E(_7J).e);},_7K=function(_7L,_7M,_7N,_7O){var _7P=B(_7s(_7L)),_7Q=B(_7u(_7P)),_7R=new T(function(){var _7S=new T(function(){var _7T=new T(function(){var _7U=new T(function(){var _7V=new T(function(){var _7W=new T(function(){return B(A3(_6U,_7Q,new T(function(){return B(A3(_7w,_7Q,_7M,_7M));}),new T(function(){return B(A3(_7w,_7Q,_7O,_7O));})));});return B(A2(_7I,_7L,_7W));});return B(A3(_7y,_7Q,_7V,new T(function(){return B(A2(_7A,_7P,_7H));})));});return B(A3(_7w,_7Q,_7U,_7U));});return B(A3(_6U,_7Q,_7T,new T(function(){return B(A3(_7w,_7Q,_7N,_7N));})));});return B(A2(_7I,_7L,_7S));});return new F(function(){return A3(_7y,_7Q,_7R,new T(function(){return B(A2(_7A,_7P,_7E));}));});},_7X=new T(function(){return B(unCStr("z"));}),_7Y=new T1(0,_7X),_7Z=new T(function(){return B(unCStr("y"));}),_80=new T1(0,_7Z),_81=new T(function(){return B(unCStr("x"));}),_82=new T1(0,_81),_83=new T(function(){return B(_7K(_7r,_82,_80,_7Y));}),_84=function(_85){return E(_85);},_86=new T(function(){return toJSStr(B(_m(_B,_84,_83)));}),_87=function(_88,_89,_8a){var _8b=new T(function(){return B(_i(_88));}),_8c=new T(function(){return B(_k(_88));}),_8d=function(_8e){var _8f=E(_8e);if(!_8f._){return E(_8c);}else{return new F(function(){return A2(_8b,new T(function(){return B(_m(_88,_89,_8f.a));}),new T(function(){return B(_8d(_8f.b));}));});}};return new F(function(){return _8d(_8a);});},_8g=new T(function(){return B(unCStr("vec3("));}),_8h=new T1(0,_8g),_8i=new T3(0,_82,_80,_7Y),_8j=function(_8k,_8l){var _8m=E(_8k);return E(_8l);},_8n=function(_8o,_8p){var _8q=E(_8o),_8r=E(_8p);return new T3(0,new T(function(){return B(A1(_8q.a,_8r.a));}),new T(function(){return B(A1(_8q.b,_8r.b));}),new T(function(){return B(A1(_8q.c,_8r.c));}));},_8s=function(_8t){return new T3(0,_8t,_8t,_8t);},_8u=function(_8v,_8w){var _8x=E(_8w);return new T3(0,_8v,_8v,_8v);},_8y=function(_8z,_8A){var _8B=E(_8A);return new T3(0,new T(function(){return B(A1(_8z,_8B.a));}),new T(function(){return B(A1(_8z,_8B.b));}),new T(function(){return B(A1(_8z,_8B.c));}));},_8C=new T2(0,_8y,_8u),_8D=function(_8E,_8F){var _8G=E(_8E),_8H=E(_8F);return new T3(0,_8G.a,_8G.b,_8G.c);},_8I=new T5(0,_8C,_8s,_8n,_8j,_8D),_8J=new T1(0,0),_8K=function(_8L){return E(E(_8L).g);},_8M=function(_8N){return new T3(0,new T3(0,new T(function(){return B(A2(_8K,_8N,_7C));}),new T(function(){return B(A2(_8K,_8N,_8J));}),new T(function(){return B(A2(_8K,_8N,_8J));})),new T3(0,new T(function(){return B(A2(_8K,_8N,_8J));}),new T(function(){return B(A2(_8K,_8N,_7C));}),new T(function(){return B(A2(_8K,_8N,_8J));})),new T3(0,new T(function(){return B(A2(_8K,_8N,_8J));}),new T(function(){return B(A2(_8K,_8N,_8J));}),new T(function(){return B(A2(_8K,_8N,_7C));})));},_8O=function(_8P){var _8Q=B(_8M(_8P));return new T3(0,_8Q.a,_8Q.b,_8Q.c);},_8R=function(_8S){return E(E(_8S).a);},_8T=function(_8U){return E(E(_8U).f);},_8V=function(_8W){return E(E(_8W).b);},_8X=function(_8Y){return E(E(_8Y).c);},_8Z=function(_90){return E(E(_90).a);},_91=function(_92){return E(E(_92).d);},_93=function(_94,_95,_96,_97,_98){var _99=new T(function(){return E(E(_94).d);}),_9a=new T(function(){var _9b=E(_94).b,_9c=new T(function(){var _9d=new T(function(){return B(_7s(_99));}),_9e=new T(function(){return B(_7u(_9d));}),_9f=new T(function(){return B(A2(_91,_99,_95));}),_9g=new T(function(){return B(A3(_8T,_99,_95,_97));}),_9h=function(_9i,_9j){var _9k=new T(function(){var _9l=new T(function(){return B(A3(_8V,_9d,new T(function(){return B(A3(_7w,_9e,_97,_9i));}),_95));});return B(A3(_6U,_9e,_9l,new T(function(){return B(A3(_7w,_9e,_9j,_9f));})));});return new F(function(){return A3(_7w,_9e,_9g,_9k);});};return B(A3(_8Z,B(_8R(_9b)),_9h,_96));});return B(A3(_8X,_9b,_9c,_98));});return new T2(0,new T(function(){return B(A3(_8T,_99,_95,_97));}),_9a);},_9m=function(_9n,_9o,_9p,_9q){var _9r=E(_9p),_9s=E(_9q),_9t=B(_93(_9o,_9r.a,_9r.b,_9s.a,_9s.b));return new T2(0,_9t.a,_9t.b);},_9u=new T1(0,1),_9v=function(_9w){return E(E(_9w).l);},_9x=function(_9y,_9z,_9A){var _9B=new T(function(){return E(E(_9y).d);}),_9C=new T(function(){var _9D=new T(function(){return B(_7s(_9B));}),_9E=new T(function(){var _9F=B(_7u(_9D)),_9G=new T(function(){var _9H=new T(function(){return B(A3(_7y,_9F,new T(function(){return B(A2(_8K,_9F,_9u));}),new T(function(){return B(A3(_7w,_9F,_9z,_9z));})));});return B(A2(_7I,_9B,_9H));});return B(A2(_6W,_9F,_9G));});return B(A3(_8Z,B(_8R(E(_9y).b)),function(_9I){return new F(function(){return A3(_8V,_9D,_9I,_9E);});},_9A));});return new T2(0,new T(function(){return B(A2(_9v,_9B,_9z));}),_9C);},_9J=function(_9K,_9L,_9M){var _9N=E(_9M),_9O=B(_9x(_9L,_9N.a,_9N.b));return new T2(0,_9O.a,_9O.b);},_9P=function(_9Q){return E(E(_9Q).r);},_9R=function(_9S,_9T,_9U){var _9V=new T(function(){return E(E(_9S).d);}),_9W=new T(function(){var _9X=new T(function(){return B(_7s(_9V));}),_9Y=new T(function(){var _9Z=new T(function(){var _a0=B(_7u(_9X));return B(A3(_7y,_a0,new T(function(){return B(A3(_7w,_a0,_9T,_9T));}),new T(function(){return B(A2(_8K,_a0,_9u));})));});return B(A2(_7I,_9V,_9Z));});return B(A3(_8Z,B(_8R(E(_9S).b)),function(_a1){return new F(function(){return A3(_8V,_9X,_a1,_9Y);});},_9U));});return new T2(0,new T(function(){return B(A2(_9P,_9V,_9T));}),_9W);},_a2=function(_a3,_a4,_a5){var _a6=E(_a5),_a7=B(_9R(_a4,_a6.a,_a6.b));return new T2(0,_a7.a,_a7.b);},_a8=function(_a9){return E(E(_a9).k);},_aa=function(_ab,_ac,_ad){var _ae=new T(function(){return E(E(_ab).d);}),_af=new T(function(){var _ag=new T(function(){return B(_7s(_ae));}),_ah=new T(function(){var _ai=new T(function(){var _aj=B(_7u(_ag));return B(A3(_7y,_aj,new T(function(){return B(A2(_8K,_aj,_9u));}),new T(function(){return B(A3(_7w,_aj,_ac,_ac));})));});return B(A2(_7I,_ae,_ai));});return B(A3(_8Z,B(_8R(E(_ab).b)),function(_ak){return new F(function(){return A3(_8V,_ag,_ak,_ah);});},_ad));});return new T2(0,new T(function(){return B(A2(_a8,_ae,_ac));}),_af);},_al=function(_am,_an,_ao){var _ap=E(_ao),_aq=B(_aa(_an,_ap.a,_ap.b));return new T2(0,_aq.a,_aq.b);},_ar=function(_as){return E(E(_as).q);},_at=function(_au,_av,_aw){var _ax=new T(function(){return E(E(_au).d);}),_ay=new T(function(){var _az=new T(function(){return B(_7s(_ax));}),_aA=new T(function(){var _aB=new T(function(){var _aC=B(_7u(_az));return B(A3(_6U,_aC,new T(function(){return B(A3(_7w,_aC,_av,_av));}),new T(function(){return B(A2(_8K,_aC,_9u));})));});return B(A2(_7I,_ax,_aB));});return B(A3(_8Z,B(_8R(E(_au).b)),function(_aD){return new F(function(){return A3(_8V,_az,_aD,_aA);});},_aw));});return new T2(0,new T(function(){return B(A2(_ar,_ax,_av));}),_ay);},_aE=function(_aF,_aG,_aH){var _aI=E(_aH),_aJ=B(_at(_aG,_aI.a,_aI.b));return new T2(0,_aJ.a,_aJ.b);},_aK=function(_aL){return E(E(_aL).m);},_aM=function(_aN,_aO,_aP){var _aQ=new T(function(){return E(E(_aN).d);}),_aR=new T(function(){var _aS=new T(function(){return B(_7s(_aQ));}),_aT=new T(function(){var _aU=B(_7u(_aS));return B(A3(_6U,_aU,new T(function(){return B(A2(_8K,_aU,_9u));}),new T(function(){return B(A3(_7w,_aU,_aO,_aO));})));});return B(A3(_8Z,B(_8R(E(_aN).b)),function(_aV){return new F(function(){return A3(_8V,_aS,_aV,_aT);});},_aP));});return new T2(0,new T(function(){return B(A2(_aK,_aQ,_aO));}),_aR);},_aW=function(_aX,_aY,_aZ){var _b0=E(_aZ),_b1=B(_aM(_aY,_b0.a,_b0.b));return new T2(0,_b1.a,_b1.b);},_b2=function(_b3){return E(E(_b3).s);},_b4=function(_b5,_b6,_b7){var _b8=new T(function(){return E(E(_b5).d);}),_b9=new T(function(){var _ba=new T(function(){return B(_7s(_b8));}),_bb=new T(function(){var _bc=B(_7u(_ba));return B(A3(_7y,_bc,new T(function(){return B(A2(_8K,_bc,_9u));}),new T(function(){return B(A3(_7w,_bc,_b6,_b6));})));});return B(A3(_8Z,B(_8R(E(_b5).b)),function(_bd){return new F(function(){return A3(_8V,_ba,_bd,_bb);});},_b7));});return new T2(0,new T(function(){return B(A2(_b2,_b8,_b6));}),_b9);},_be=function(_bf,_bg,_bh){var _bi=E(_bh),_bj=B(_b4(_bg,_bi.a,_bi.b));return new T2(0,_bj.a,_bj.b);},_bk=function(_bl){return E(E(_bl).i);},_bm=function(_bn){return E(E(_bn).h);},_bo=function(_bp,_bq,_br){var _bs=new T(function(){return E(E(_bp).d);}),_bt=new T(function(){var _bu=new T(function(){return B(_7u(new T(function(){return B(_7s(_bs));})));}),_bv=new T(function(){return B(A2(_6W,_bu,new T(function(){return B(A2(_bm,_bs,_bq));})));});return B(A3(_8Z,B(_8R(E(_bp).b)),function(_bw){return new F(function(){return A3(_7w,_bu,_bw,_bv);});},_br));});return new T2(0,new T(function(){return B(A2(_bk,_bs,_bq));}),_bt);},_bx=function(_by,_bz,_bA){var _bB=E(_bA),_bC=B(_bo(_bz,_bB.a,_bB.b));return new T2(0,_bC.a,_bC.b);},_bD=function(_bE){return E(E(_bE).o);},_bF=function(_bG){return E(E(_bG).n);},_bH=function(_bI,_bJ,_bK){var _bL=new T(function(){return E(E(_bI).d);}),_bM=new T(function(){var _bN=new T(function(){return B(_7u(new T(function(){return B(_7s(_bL));})));}),_bO=new T(function(){return B(A2(_bF,_bL,_bJ));});return B(A3(_8Z,B(_8R(E(_bI).b)),function(_bP){return new F(function(){return A3(_7w,_bN,_bP,_bO);});},_bK));});return new T2(0,new T(function(){return B(A2(_bD,_bL,_bJ));}),_bM);},_bQ=function(_bR,_bS,_bT){var _bU=E(_bT),_bV=B(_bH(_bS,_bU.a,_bU.b));return new T2(0,_bV.a,_bV.b);},_bW=function(_bX){return E(E(_bX).c);},_bY=function(_bZ,_c0,_c1){var _c2=new T(function(){return E(E(_bZ).d);}),_c3=new T(function(){var _c4=new T(function(){return B(_7u(new T(function(){return B(_7s(_c2));})));}),_c5=new T(function(){return B(A2(_bW,_c2,_c0));});return B(A3(_8Z,B(_8R(E(_bZ).b)),function(_c6){return new F(function(){return A3(_7w,_c4,_c6,_c5);});},_c1));});return new T2(0,new T(function(){return B(A2(_bW,_c2,_c0));}),_c3);},_c7=function(_c8,_c9,_ca){var _cb=E(_ca),_cc=B(_bY(_c9,_cb.a,_cb.b));return new T2(0,_cc.a,_cc.b);},_cd=function(_ce,_cf,_cg){var _ch=new T(function(){return E(E(_ce).d);}),_ci=new T(function(){var _cj=new T(function(){return B(_7s(_ch));}),_ck=new T(function(){return B(_7u(_cj));}),_cl=new T(function(){return B(A3(_8V,_cj,new T(function(){return B(A2(_8K,_ck,_9u));}),_cf));});return B(A3(_8Z,B(_8R(E(_ce).b)),function(_cm){return new F(function(){return A3(_7w,_ck,_cm,_cl);});},_cg));});return new T2(0,new T(function(){return B(A2(_91,_ch,_cf));}),_ci);},_cn=function(_co,_cp,_cq){var _cr=E(_cq),_cs=B(_cd(_cp,_cr.a,_cr.b));return new T2(0,_cs.a,_cs.b);},_ct=function(_cu,_cv,_cw,_cx){var _cy=new T4(0,new T(function(){return E(E(_cv).a);}),new T(function(){return E(E(_cv).b);}),new T(function(){return E(E(_cv).c);}),new T(function(){return E(E(_cv).d);}));return new F(function(){return A3(_8V,_cu,new T(function(){var _cz=E(_cx),_cA=B(_cd(_cy,_cz.a,_cz.b));return new T2(0,_cA.a,_cA.b);}),new T(function(){var _cB=E(_cw),_cC=B(_cd(_cy,_cB.a,_cB.b));return new T2(0,_cC.a,_cC.b);}));});},_cD=new T1(0,0),_cE=function(_cF){return E(E(_cF).b);},_cG=function(_cH){return E(E(_cH).b);},_cI=function(_cJ){var _cK=new T(function(){return E(E(_cJ).d);}),_cL=new T(function(){return B(A2(_cG,E(_cJ).b,new T(function(){return B(A2(_8K,B(_7u(B(_7s(_cK)))),_cD));})));});return new T2(0,new T(function(){return B(_cE(_cK));}),_cL);},_cM=function(_cN,_cO){var _cP=B(_cI(_cO));return new T2(0,_cP.a,_cP.b);},_cQ=function(_cR,_cS,_cT){var _cU=new T(function(){return E(E(_cR).d);}),_cV=new T(function(){var _cW=new T(function(){return B(_7u(new T(function(){return B(_7s(_cU));})));}),_cX=new T(function(){return B(A2(_bk,_cU,_cS));});return B(A3(_8Z,B(_8R(E(_cR).b)),function(_cY){return new F(function(){return A3(_7w,_cW,_cY,_cX);});},_cT));});return new T2(0,new T(function(){return B(A2(_bm,_cU,_cS));}),_cV);},_cZ=function(_d0,_d1,_d2){var _d3=E(_d2),_d4=B(_cQ(_d1,_d3.a,_d3.b));return new T2(0,_d4.a,_d4.b);},_d5=function(_d6,_d7,_d8){var _d9=new T(function(){return E(E(_d6).d);}),_da=new T(function(){var _db=new T(function(){return B(_7u(new T(function(){return B(_7s(_d9));})));}),_dc=new T(function(){return B(A2(_bD,_d9,_d7));});return B(A3(_8Z,B(_8R(E(_d6).b)),function(_dd){return new F(function(){return A3(_7w,_db,_dd,_dc);});},_d8));});return new T2(0,new T(function(){return B(A2(_bF,_d9,_d7));}),_da);},_de=function(_df,_dg,_dh){var _di=E(_dh),_dj=B(_d5(_dg,_di.a,_di.b));return new T2(0,_dj.a,_dj.b);},_dk=new T1(0,2),_dl=function(_dm,_dn,_do){var _dp=new T(function(){return E(E(_dm).d);}),_dq=new T(function(){var _dr=new T(function(){return B(_7s(_dp));}),_ds=new T(function(){return B(_7u(_dr));}),_dt=new T(function(){var _du=new T(function(){return B(A3(_8V,_dr,new T(function(){return B(A2(_8K,_ds,_9u));}),new T(function(){return B(A2(_8K,_ds,_dk));})));});return B(A3(_8V,_dr,_du,new T(function(){return B(A2(_7I,_dp,_dn));})));});return B(A3(_8Z,B(_8R(E(_dm).b)),function(_dv){return new F(function(){return A3(_7w,_ds,_dv,_dt);});},_do));});return new T2(0,new T(function(){return B(A2(_7I,_dp,_dn));}),_dq);},_dw=function(_dx,_dy,_dz){var _dA=E(_dz),_dB=B(_dl(_dy,_dA.a,_dA.b));return new T2(0,_dB.a,_dB.b);},_dC=function(_dD){return E(E(_dD).j);},_dE=function(_dF,_dG,_dH){var _dI=new T(function(){return E(E(_dF).d);}),_dJ=new T(function(){var _dK=new T(function(){return B(_7s(_dI));}),_dL=new T(function(){var _dM=new T(function(){return B(A2(_bk,_dI,_dG));});return B(A3(_7w,B(_7u(_dK)),_dM,_dM));});return B(A3(_8Z,B(_8R(E(_dF).b)),function(_dN){return new F(function(){return A3(_8V,_dK,_dN,_dL);});},_dH));});return new T2(0,new T(function(){return B(A2(_dC,_dI,_dG));}),_dJ);},_dO=function(_dP,_dQ,_dR){var _dS=E(_dR),_dT=B(_dE(_dQ,_dS.a,_dS.b));return new T2(0,_dT.a,_dT.b);},_dU=function(_dV){return E(E(_dV).p);},_dW=function(_dX,_dY,_dZ){var _e0=new T(function(){return E(E(_dX).d);}),_e1=new T(function(){var _e2=new T(function(){return B(_7s(_e0));}),_e3=new T(function(){var _e4=new T(function(){return B(A2(_bD,_e0,_dY));});return B(A3(_7w,B(_7u(_e2)),_e4,_e4));});return B(A3(_8Z,B(_8R(E(_dX).b)),function(_e5){return new F(function(){return A3(_8V,_e2,_e5,_e3);});},_dZ));});return new T2(0,new T(function(){return B(A2(_dU,_e0,_dY));}),_e1);},_e6=function(_e7,_e8,_e9){var _ea=E(_e9),_eb=B(_dW(_e8,_ea.a,_ea.b));return new T2(0,_eb.a,_eb.b);},_ec=function(_ed,_ee){return {_:0,a:_ed,b:new T(function(){return B(_cM(_ed,_ee));}),c:function(_ef){return new F(function(){return _c7(_ed,_ee,_ef);});},d:function(_ef){return new F(function(){return _cn(_ed,_ee,_ef);});},e:function(_ef){return new F(function(){return _dw(_ed,_ee,_ef);});},f:function(_eg,_ef){return new F(function(){return _9m(_ed,_ee,_eg,_ef);});},g:function(_eg,_ef){return new F(function(){return _ct(_ed,_ee,_eg,_ef);});},h:function(_ef){return new F(function(){return _cZ(_ed,_ee,_ef);});},i:function(_ef){return new F(function(){return _bx(_ed,_ee,_ef);});},j:function(_ef){return new F(function(){return _dO(_ed,_ee,_ef);});},k:function(_ef){return new F(function(){return _al(_ed,_ee,_ef);});},l:function(_ef){return new F(function(){return _9J(_ed,_ee,_ef);});},m:function(_ef){return new F(function(){return _aW(_ed,_ee,_ef);});},n:function(_ef){return new F(function(){return _de(_ed,_ee,_ef);});},o:function(_ef){return new F(function(){return _bQ(_ed,_ee,_ef);});},p:function(_ef){return new F(function(){return _e6(_ed,_ee,_ef);});},q:function(_ef){return new F(function(){return _aE(_ed,_ee,_ef);});},r:function(_ef){return new F(function(){return _a2(_ed,_ee,_ef);});},s:function(_ef){return new F(function(){return _be(_ed,_ee,_ef);});}};},_eh=function(_ei,_ej,_ek,_el,_em){var _en=new T(function(){return B(_7s(new T(function(){return E(E(_ei).d);})));}),_eo=new T(function(){var _ep=E(_ei).b,_eq=new T(function(){var _er=new T(function(){return B(_7u(_en));}),_es=new T(function(){return B(A3(_7w,_er,_el,_el));}),_et=function(_eu,_ev){var _ew=new T(function(){return B(A3(_7y,_er,new T(function(){return B(A3(_7w,_er,_eu,_el));}),new T(function(){return B(A3(_7w,_er,_ej,_ev));})));});return new F(function(){return A3(_8V,_en,_ew,_es);});};return B(A3(_8Z,B(_8R(_ep)),_et,_ek));});return B(A3(_8X,_ep,_eq,_em));});return new T2(0,new T(function(){return B(A3(_8V,_en,_ej,_el));}),_eo);},_ex=function(_ey,_ez,_eA,_eB){var _eC=E(_eA),_eD=E(_eB),_eE=B(_eh(_ez,_eC.a,_eC.b,_eD.a,_eD.b));return new T2(0,_eE.a,_eE.b);},_eF=function(_eG,_eH){var _eI=new T(function(){return B(_7s(new T(function(){return E(E(_eG).d);})));}),_eJ=new T(function(){return B(A2(_cG,E(_eG).b,new T(function(){return B(A2(_8K,B(_7u(_eI)),_cD));})));});return new T2(0,new T(function(){return B(A2(_7A,_eI,_eH));}),_eJ);},_eK=function(_eL,_eM,_eN){var _eO=B(_eF(_eM,_eN));return new T2(0,_eO.a,_eO.b);},_eP=function(_eQ,_eR,_eS){var _eT=new T(function(){return B(_7s(new T(function(){return E(E(_eQ).d);})));}),_eU=new T(function(){return B(_7u(_eT));}),_eV=new T(function(){var _eW=new T(function(){var _eX=new T(function(){return B(A3(_8V,_eT,new T(function(){return B(A2(_8K,_eU,_9u));}),new T(function(){return B(A3(_7w,_eU,_eR,_eR));})));});return B(A2(_6W,_eU,_eX));});return B(A3(_8Z,B(_8R(E(_eQ).b)),function(_eY){return new F(function(){return A3(_7w,_eU,_eY,_eW);});},_eS));}),_eZ=new T(function(){return B(A3(_8V,_eT,new T(function(){return B(A2(_8K,_eU,_9u));}),_eR));});return new T2(0,_eZ,_eV);},_f0=function(_f1,_f2,_f3){var _f4=E(_f3),_f5=B(_eP(_f2,_f4.a,_f4.b));return new T2(0,_f5.a,_f5.b);},_f6=function(_f7,_f8){return new T4(0,_f7,function(_eg,_ef){return new F(function(){return _ex(_f7,_f8,_eg,_ef);});},function(_ef){return new F(function(){return _f0(_f7,_f8,_ef);});},function(_ef){return new F(function(){return _eK(_f7,_f8,_ef);});});},_f9=function(_fa,_fb,_fc,_fd,_fe){var _ff=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_fa).d);})));})));}),_fg=new T(function(){var _fh=E(_fa).b,_fi=new T(function(){var _fj=function(_fk,_fl){return new F(function(){return A3(_6U,_ff,new T(function(){return B(A3(_7w,_ff,_fb,_fl));}),new T(function(){return B(A3(_7w,_ff,_fk,_fd));}));});};return B(A3(_8Z,B(_8R(_fh)),_fj,_fc));});return B(A3(_8X,_fh,_fi,_fe));});return new T2(0,new T(function(){return B(A3(_7w,_ff,_fb,_fd));}),_fg);},_fm=function(_fn,_fo,_fp){var _fq=E(_fo),_fr=E(_fp),_fs=B(_f9(_fn,_fq.a,_fq.b,_fr.a,_fr.b));return new T2(0,_fs.a,_fs.b);},_ft=function(_fu,_fv,_fw,_fx,_fy){var _fz=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_fu).d);})));})));}),_fA=new T(function(){var _fB=E(_fu).b,_fC=new T(function(){return B(A3(_8Z,B(_8R(_fB)),new T(function(){return B(_6U(_fz));}),_fw));});return B(A3(_8X,_fB,_fC,_fy));});return new T2(0,new T(function(){return B(A3(_6U,_fz,_fv,_fx));}),_fA);},_fD=function(_fE,_fF,_fG){var _fH=E(_fF),_fI=E(_fG),_fJ=B(_ft(_fE,_fH.a,_fH.b,_fI.a,_fI.b));return new T2(0,_fJ.a,_fJ.b);},_fK=function(_fL,_fM,_fN){var _fO=B(_fP(_fL));return new F(function(){return A3(_6U,_fO,_fM,new T(function(){return B(A2(_6W,_fO,_fN));}));});},_fQ=function(_fR){return E(E(_fR).e);},_fS=function(_fT){return E(E(_fT).f);},_fU=function(_fV,_fW,_fX){var _fY=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_fV).d);})));})));}),_fZ=new T(function(){var _g0=new T(function(){return B(A2(_fS,_fY,_fW));});return B(A3(_8Z,B(_8R(E(_fV).b)),function(_g1){return new F(function(){return A3(_7w,_fY,_g1,_g0);});},_fX));});return new T2(0,new T(function(){return B(A2(_fQ,_fY,_fW));}),_fZ);},_g2=function(_g3,_g4){var _g5=E(_g4),_g6=B(_fU(_g3,_g5.a,_g5.b));return new T2(0,_g6.a,_g6.b);},_g7=function(_g8,_g9){var _ga=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_g8).d);})));})));}),_gb=new T(function(){return B(A2(_cG,E(_g8).b,new T(function(){return B(A2(_8K,_ga,_cD));})));});return new T2(0,new T(function(){return B(A2(_8K,_ga,_g9));}),_gb);},_gc=function(_gd,_ge){var _gf=B(_g7(_gd,_ge));return new T2(0,_gf.a,_gf.b);},_gg=function(_gh,_gi,_gj){var _gk=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_gh).d);})));})));}),_gl=new T(function(){return B(A3(_8Z,B(_8R(E(_gh).b)),new T(function(){return B(_6W(_gk));}),_gj));});return new T2(0,new T(function(){return B(A2(_6W,_gk,_gi));}),_gl);},_gm=function(_gn,_go){var _gp=E(_go),_gq=B(_gg(_gn,_gp.a,_gp.b));return new T2(0,_gq.a,_gq.b);},_gr=function(_gs,_gt){var _gu=new T(function(){return B(_7u(new T(function(){return B(_7s(new T(function(){return E(E(_gs).d);})));})));}),_gv=new T(function(){return B(A2(_cG,E(_gs).b,new T(function(){return B(A2(_8K,_gu,_cD));})));});return new T2(0,new T(function(){return B(A2(_fS,_gu,_gt));}),_gv);},_gw=function(_gx,_gy){var _gz=B(_gr(_gx,E(_gy).a));return new T2(0,_gz.a,_gz.b);},_fP=function(_gA){return {_:0,a:function(_eg,_ef){return new F(function(){return _fD(_gA,_eg,_ef);});},b:function(_eg,_ef){return new F(function(){return _fK(_gA,_eg,_ef);});},c:function(_eg,_ef){return new F(function(){return _fm(_gA,_eg,_ef);});},d:function(_ef){return new F(function(){return _gm(_gA,_ef);});},e:function(_ef){return new F(function(){return _g2(_gA,_ef);});},f:function(_ef){return new F(function(){return _gw(_gA,_ef);});},g:function(_ef){return new F(function(){return _gc(_gA,_ef);});}};},_gB=function(_gC,_gD,_gE){var _gF=E(_gE),_gG=new T(function(){return B(A2(_gC,_gF.b,new T(function(){return B(A2(_gC,_gF.c,_gD));})));});return new F(function(){return A2(_gC,_gF.a,_gG);});},_gH=function(_gI,_gJ){var _gK=E(_gJ);return new F(function(){return A3(_7w,_gI,_gK.a,new T(function(){return B(A3(_7w,_gI,_gK.b,_gK.c));}));});},_gL=function(_gM,_gN){var _gO=E(_gN);return new F(function(){return A3(_6U,_gM,_gO.a,new T(function(){return B(A3(_6U,_gM,_gO.b,_gO.c));}));});},_gP=function(_gQ){return E(E(_gQ).a);},_gR=function(_gS,_gT){var _gU=new T(function(){return B(A2(_gP,_gS,_gT));});return function(_gV){var _gW=E(_gV);if(!B(A1(_gU,_gW.a))){if(!B(A1(_gU,_gW.b))){return new F(function(){return A1(_gU,_gW.c);});}else{return true;}}else{return true;}};},_gX=function(_gY,_gZ,_h0,_h1,_h2){var _h3=new T(function(){return B(A3(_i,_gY,new T(function(){return B(A1(_gZ,_h1));}),new T(function(){return B(A1(_gZ,_h2));})));});return new F(function(){return A3(_i,_gY,new T(function(){return B(A1(_gZ,_h0));}),_h3);});},_h4=function(_h5,_h6,_h7){var _h8=E(_h7);return new F(function(){return _gX(_h5,_h6,_h8.a,_h8.b,_h8.c);});},_h9=function(_ha,_hb,_hc){var _hd=E(_hc),_he=new T(function(){return B(A2(_ha,new T(function(){return B(A2(_ha,_hb,_hd.a));}),_hd.b));});return new F(function(){return A2(_ha,_he,_hd.c);});},_hf=function(_hg,_hh,_hi,_hj,_hk){return new F(function(){return A2(_hg,B(A2(_hg,B(A2(_hg,_hh,_hi)),_hj)),_hk);});},_hl=function(_hm,_hn,_ho){var _hp=E(_ho);return new F(function(){return _hf(_hm,_hn,_hp.a,_hp.b,_hp.c);});},_hq=function(_hr,_hs){var _ht=E(_hs);return new F(function(){return A2(_hr,new T(function(){return B(A2(_hr,_ht.a,_ht.b));}),_ht.c);});},_hu=function(_hv,_hw,_hx,_hy,_hz){return new F(function(){return A2(_hv,_hx,B(A2(_hv,_hy,B(A2(_hv,_hz,_hw)))));});},_hA=function(_hB,_hC,_hD){var _hE=E(_hD);return new F(function(){return _hu(_hB,_hC,_hE.a,_hE.b,_hE.c);});},_hF=function(_hG,_hH){var _hI=E(_hH);return new F(function(){return A2(_hG,_hI.a,new T(function(){return B(A2(_hG,_hI.b,_hI.c));}));});},_hJ=3,_hK=function(_hL){var _hM=E(_hL);return E(_hJ);},_hN=function(_hO){return E(E(_hO).f);},_hP=function(_hQ,_hR,_hS,_hT){return (!B(A3(_hN,_hQ,_hS,_hT)))?(!B(A3(_hN,_hQ,_hR,_hT)))?E(_hT):E(_hR):(!B(A3(_hN,_hQ,_hR,_hS)))?E(_hS):E(_hR);},_hU=function(_hV,_hW){var _hX=E(_hW);return new F(function(){return _hP(_hV,_hX.a,_hX.b,_hX.c);});},_hY=function(_hZ){return E(E(_hZ).d);},_i0=function(_i1,_i2,_i3,_i4){return (!B(A3(_hY,_i1,_i3,_i4)))?(!B(A3(_hY,_i1,_i2,_i4)))?E(_i4):E(_i2):(!B(A3(_hY,_i1,_i2,_i3)))?E(_i3):E(_i2);},_i5=function(_i6,_i7){var _i8=E(_i7);return new F(function(){return _i0(_i6,_i8.a,_i8.b,_i8.c);});},_i9=function(_ia){var _ib=E(_ia);return false;},_ic=function(_id,_ie){return new T2(1,_id,_ie);},_if=function(_ig){return E(E(_ig).c);},_ih=function(_ii){return new F(function(){return A(_if,[_ij,_ic,_4,_ii]);});},_ik=function(_il,_im){var _in=E(_im);return new F(function(){return A3(_i,_il,_in.a,new T(function(){return B(A3(_i,_il,_in.b,_in.c));}));});},_ij=new T(function(){return {_:0,a:_ik,b:_h4,c:_gB,d:_hA,e:_h9,f:_hl,g:_hF,h:_hq,i:_ih,j:_i9,k:_hK,l:_gR,m:_hU,n:_i5,o:_gL,p:_gH};}),_io=function(_ip){return E(E(_ip).a);},_iq=function(_ir,_is,_it){return new T3(0,_ir,_is,_it);},_iu=function(_iv,_iw,_ix,_iy,_iz){var _iA=new T(function(){var _iB=new T(function(){return B(A3(_8Z,B(_8R(_iv)),_iq,new T(function(){return B(A1(_iw,_ix));})));});return B(A3(_8X,_iv,_iB,new T(function(){return B(A1(_iw,_iy));})));});return new F(function(){return A3(_8X,_iv,_iA,new T(function(){return B(A1(_iw,_iz));}));});},_iC=function(_iD,_iE,_iF){var _iG=E(_iF);return new F(function(){return _iu(B(_io(_iD)),_iE,_iG.a,_iG.b,_iG.c);});},_iH=function(_iI,_iJ){var _iK=E(_iJ),_iL=new T(function(){return B(_io(_iI));}),_iM=new T(function(){return B(A3(_8X,_iL,new T(function(){return B(A3(_8Z,B(_8R(_iL)),_iq,_iK.a));}),_iK.b));});return new F(function(){return A3(_8X,_iL,_iM,_iK.c);});},_iN=function(_iO,_iP){var _iQ=E(_iP),_iR=new T(function(){return B(A3(_8X,_iO,new T(function(){return B(A3(_8Z,B(_8R(_iO)),_iq,_iQ.a));}),_iQ.b));});return new F(function(){return A3(_8X,_iO,_iR,_iQ.c);});},_iS=function(_iT,_iU,_iV){var _iW=E(_iV);return new F(function(){return _iu(_iT,_iU,_iW.a,_iW.b,_iW.c);});},_iX=new T6(0,_8C,_ij,_iS,_iN,_iC,_iH),_iY=function(_iZ){var _j0=new T4(0,_iX,_8I,_8O,_iZ),_j1=new T(function(){return B(_ec(new T(function(){return B(_f6(new T(function(){return B(_fP(_j0));}),_j0));}),_j0));}),_j2=new T(function(){return B(_7u(new T(function(){return B(_7s(_iZ));})));});return function(_j3){var _j4=E(_j3),_j5=B(_8M(_j2));return E(B(_7K(_j1,new T2(0,_j4.a,_j5.a),new T2(0,_j4.b,_j5.b),new T2(0,_j4.c,_j5.c))).b);};},_j6=new T(function(){return B(_iY(_7r));}),_j7=new T(function(){return B(A1(_j6,_8i));}),_j8=new T(function(){return E(E(_j7).a);}),_j9=new T(function(){return E(E(_j7).b);}),_ja=new T(function(){return E(E(_j7).c);}),_jb=new T2(1,_ja,_I),_jc=new T2(1,_D,_jb),_jd=new T2(1,_j9,_jc),_je=new T2(1,_D,_jd),_jf=new T2(1,_j8,_je),_jg=new T2(1,_8h,_jf),_jh=new T(function(){return toJSStr(B(_87(_B,_84,_jg)));}),_ji=function(_jj,_jk,_jl){return new F(function(){return A1(_jj,function(_jm){return new F(function(){return A2(_jk,_jm,_jl);});});});},_jn=function(_jo,_jp,_jq){var _jr=function(_js){var _jt=new T(function(){return B(A1(_jq,_js));});return new F(function(){return A1(_jp,function(_ju){return E(_jt);});});};return new F(function(){return A1(_jo,_jr);});},_jv=function(_jw,_jx,_jy){var _jz=new T(function(){return B(A1(_jx,function(_jA){return new F(function(){return A1(_jy,_jA);});}));});return new F(function(){return A1(_jw,function(_jB){return E(_jz);});});},_jC=function(_jD,_jE,_jF){var _jG=function(_jH){var _jI=function(_jJ){return new F(function(){return A1(_jF,new T(function(){return B(A1(_jH,_jJ));}));});};return new F(function(){return A1(_jE,_jI);});};return new F(function(){return A1(_jD,_jG);});},_jK=function(_jL,_jM){return new F(function(){return A1(_jM,_jL);});},_jN=function(_jO,_jP,_jQ){var _jR=new T(function(){return B(A1(_jQ,_jO));});return new F(function(){return A1(_jP,function(_jS){return E(_jR);});});},_jT=function(_jU,_jV,_jW){var _jX=function(_jY){return new F(function(){return A1(_jW,new T(function(){return B(A1(_jU,_jY));}));});};return new F(function(){return A1(_jV,_jX);});},_jZ=new T2(0,_jT,_jN),_k0=new T5(0,_jZ,_jK,_jC,_jv,_jn),_k1=function(_k2){return E(E(_k2).b);},_k3=function(_k4,_k5){return new F(function(){return A3(_k1,_k6,_k4,function(_k7){return E(_k5);});});},_k8=function(_k9){return new F(function(){return err(_k9);});},_k6=new T(function(){return new T5(0,_k0,_ji,_k3,_jK,_k8);}),_ka=function(_kb){return new T0(2);},_kc=function(_kd){var _ke=new T(function(){return B(A1(_kd,_ka));}),_kf=function(_kg){return new T1(1,new T2(1,new T(function(){return B(A1(_kg,_5));}),new T2(1,_ke,_4)));};return E(_kf);},_kh=new T3(0,_k6,_84,_kc),_ki=1,_kj=0,_kk=new T3(0,_kj,_kj,_ki),_kl=function(_km){var _kn=E(_km);return new F(function(){return Math.log(_kn+(_kn+1)*Math.sqrt((_kn-1)/(_kn+1)));});},_ko=function(_kp){var _kq=E(_kp);return new F(function(){return Math.log(_kq+Math.sqrt(1+_kq*_kq));});},_kr=function(_ks){var _kt=E(_ks);return 0.5*Math.log((1+_kt)/(1-_kt));},_ku=function(_kv,_kw){return Math.log(E(_kw))/Math.log(E(_kv));},_kx=3.141592653589793,_ky=function(_kz){var _kA=E(_kz);return new F(function(){return _6v(_kA.a,_kA.b);});},_kB=function(_kC){return 1/E(_kC);},_kD=function(_kE){var _kF=E(_kE),_kG=E(_kF);return (_kG==0)?E(_6u):(_kG<=0)? -_kG:E(_kF);},_kH=function(_kI){var _kJ=E(_kI);if(!_kJ._){return _kJ.a;}else{return new F(function(){return I_toNumber(_kJ.a);});}},_kK=function(_kL){return new F(function(){return _kH(_kL);});},_kM=1,_kN=-1,_kO=function(_kP){var _kQ=E(_kP);return (_kQ<=0)?(_kQ>=0)?E(_kQ):E(_kN):E(_kM);},_kR=function(_kS,_kT){return E(_kS)-E(_kT);},_kU=function(_kV){return  -E(_kV);},_kW=function(_kX,_kY){return E(_kX)+E(_kY);},_kZ=function(_l0,_l1){return E(_l0)*E(_l1);},_l2={_:0,a:_kW,b:_kR,c:_kZ,d:_kU,e:_kD,f:_kO,g:_kK},_l3=function(_l4,_l5){return E(_l4)/E(_l5);},_l6=new T4(0,_l2,_l3,_kB,_ky),_l7=function(_l8){return new F(function(){return Math.acos(E(_l8));});},_l9=function(_la){return new F(function(){return Math.asin(E(_la));});},_lb=function(_lc){return new F(function(){return Math.atan(E(_lc));});},_ld=function(_le){return new F(function(){return Math.cos(E(_le));});},_lf=function(_lg){return new F(function(){return cosh(E(_lg));});},_lh=function(_li){return new F(function(){return Math.exp(E(_li));});},_lj=function(_lk){return new F(function(){return Math.log(E(_lk));});},_ll=function(_lm,_ln){return new F(function(){return Math.pow(E(_lm),E(_ln));});},_lo=function(_lp){return new F(function(){return Math.sin(E(_lp));});},_lq=function(_lr){return new F(function(){return sinh(E(_lr));});},_ls=function(_lt){return new F(function(){return Math.sqrt(E(_lt));});},_lu=function(_lv){return new F(function(){return Math.tan(E(_lv));});},_lw=function(_lx){return new F(function(){return tanh(E(_lx));});},_ly={_:0,a:_l6,b:_kx,c:_lh,d:_lj,e:_ls,f:_ll,g:_ku,h:_lo,i:_ld,j:_lu,k:_l9,l:_l7,m:_lb,n:_lq,o:_lf,p:_lw,q:_ko,r:_kl,s:_kr},_lz=function(_lA,_lB,_lC,_lD,_lE,_lF,_lG){var _lH=B(_7u(B(_7s(_lA)))),_lI=new T(function(){return B(A3(_6U,_lH,new T(function(){return B(A3(_7w,_lH,_lB,_lE));}),new T(function(){return B(A3(_7w,_lH,_lC,_lF));})));});return new F(function(){return A3(_6U,_lH,_lI,new T(function(){return B(A3(_7w,_lH,_lD,_lG));}));});},_lJ=function(_lK,_lL,_lM,_lN){var _lO=new T(function(){return B(_7s(_lK));}),_lP=new T(function(){return B(A2(_7I,_lK,new T(function(){return B(_lz(_lK,_lL,_lM,_lN,_lL,_lM,_lN));})));});return new T3(0,new T(function(){return B(A3(_8V,_lO,_lL,_lP));}),new T(function(){return B(A3(_8V,_lO,_lM,_lP));}),new T(function(){return B(A3(_8V,_lO,_lN,_lP));}));},_lQ=0.2,_lR=new T(function(){var _lS=B(_lJ(_ly,_kj,_ki,_lQ));return new T3(0,_lS.a,_lS.b,_lS.c);}),_lT=-1.3,_lU=new T3(0,_lT,_kj,_kj),_lV=new T3(0,_lU,_lR,_kk),_lW=function(_lX,_lY){return new F(function(){return A3(_8V,B(_7s(_lX)),new T(function(){var _lZ=E(_lY);return B(_7K(_lX,_lZ.a,_lZ.b,_lZ.c));}),new T(function(){var _m0=B(A2(_iY,_lX,_lY)),_m1=_m0.a,_m2=_m0.b,_m3=_m0.c;return B(_lz(_lX,_m1,_m2,_m3,_m1,_m2,_m3));}));});},_m4=new T(function(){return eval("draw");}),_m5=new T(function(){return B(_iY(_ly));}),_m6=new T(function(){return eval("refresh");}),_m7=function(_m8,_m9,_ma,_mb,_mc,_md,_me,_){var _mf=__app0(E(_m6)),_mg=E(_m8),_mh=E(_m9),_mi=E(_ma),_mj=E(_mc),_mk=E(_md),_ml=E(_me),_mm=__apply(E(_m4),new T2(1,_ml,new T2(1,_mk,new T2(1,_mj,new T2(1,_mi,new T2(1,_mh,new T2(1,_mg,_4))))))),_mn=new T(function(){var _mo=E(_mb),_mp=new T(function(){return _mi+E(_mo.c)*2.0e-2;}),_mq=new T(function(){return _mh+E(_mo.b)*2.0e-2;}),_mr=new T(function(){return _mg+E(_mo.a)*2.0e-2;}),_ms=new T3(0,_mr,_mq,_mp),_mt=B(A1(_m5,_ms)),_mu=B(_lJ(_ly,_mt.a,_mt.b,_mt.c)),_mv=new T(function(){return B(_lW(_ly,_ms));});return new T3(0,new T(function(){return E(_mr)+ -(E(_mv)*E(_mu.a));}),new T(function(){return E(_mq)+ -(E(_mv)*E(_mu.b));}),new T(function(){return E(_mp)+ -(E(_mv)*E(_mu.c));}));}),_mw=new T(function(){var _mx=B(A1(_m5,_mn)),_my=B(_lJ(_ly,_mx.a,_mx.b,_mx.c));return new T3(0,_my.a,_my.b,_my.c);}),_mz=new T(function(){var _mA=E(_mw),_mB=_mA.a,_mC=_mA.b,_mD=_mA.c,_mE=new T(function(){return  -B(_lz(_ly,_mj,_mk,_ml,_mB,_mC,_mD));}),_mF=new T(function(){return _mj+E(_mB)*E(_mE);}),_mG=new T(function(){return _mk+E(_mC)*E(_mE);}),_mH=new T(function(){return _ml+E(_mD)*E(_mE);}),_mI=new T(function(){return Math.sqrt(B(_lz(_ly,_mF,_mG,_mH,_mF,_mG,_mH)));});return new T3(0,new T(function(){return B(_l3(_mF,_mI));}),new T(function(){return B(_l3(_mG,_mI));}),new T(function(){return B(_l3(_mH,_mI));}));}),_mJ=new T(function(){var _mK=E(_mb),_mL=_mK.a,_mM=_mK.b,_mN=_mK.c,_mO=E(_mw),_mP=_mO.a,_mQ=_mO.b,_mR=_mO.c,_mS=new T(function(){return Math.sqrt(B(_lz(_ly,_mL,_mM,_mN,_mL,_mM,_mN)));}),_mT=new T(function(){return  -B(_lz(_ly,_mL,_mM,_mN,_mP,_mQ,_mR));}),_mU=new T(function(){return E(_mL)+E(_mP)*E(_mT);}),_mV=new T(function(){return E(_mM)+E(_mQ)*E(_mT);}),_mW=new T(function(){return E(_mN)+E(_mR)*E(_mT);}),_mX=new T(function(){return Math.sqrt(B(_lz(_ly,_mU,_mV,_mW,_mU,_mV,_mW)));});return new T3(0,new T(function(){return E(_mS)*(E(_mU)/E(_mX));}),new T(function(){return E(_mS)*(E(_mV)/E(_mX));}),new T(function(){return E(_mS)*(E(_mW)/E(_mX));}));});return new T3(0,_mn,_mJ,_mz);},_mY=function(_mZ,_n0,_n1){var _n2=function(_){var _n3=E(_mZ),_n4=E(_n3.a),_n5=E(_n3.c),_n6=B(_m7(_n4.a,_n4.b,_n4.c,_n3.b,_n5.a,_n5.b,_n5.c,_));return new T(function(){return B(A1(_n1,new T1(1,_n6)));});};return new T1(0,_n2);},_n7=new T0(2),_n8=function(_n9,_na,_nb){return function(_){var _nc=E(_n9),_nd=rMV(_nc),_ne=E(_nd);if(!_ne._){var _nf=new T(function(){var _ng=new T(function(){return B(A1(_nb,_5));});return B(_0(_ne.b,new T2(1,new T2(0,_na,function(_nh){return E(_ng);}),_4)));}),_=wMV(_nc,new T2(0,_ne.a,_nf));return _n7;}else{var _ni=E(_ne.a);if(!_ni._){var _=wMV(_nc,new T2(0,_na,_4));return new T(function(){return B(A1(_nb,_5));});}else{var _=wMV(_nc,new T1(1,_ni.b));return new T1(1,new T2(1,new T(function(){return B(A1(_nb,_5));}),new T2(1,new T(function(){return B(A2(_ni.a,_na,_ka));}),_4)));}}};},_nj=function(_nk){return E(E(_nk).b);},_nl=function(_nm,_nn,_no){var _np=new T(function(){return new T1(0,B(_n8(_nn,_no,_ka)));}),_nq=function(_nr){return new T1(1,new T2(1,new T(function(){return B(A1(_nr,_5));}),new T2(1,_np,_4)));};return new F(function(){return A2(_nj,_nm,_nq);});},_ns=function(_){return new F(function(){return __jsNull();});},_nt=function(_nu){var _nv=B(A1(_nu,_));return E(_nv);},_nw=new T(function(){return B(_nt(_ns));}),_nx=new T(function(){return E(_nw);}),_ny=new T(function(){return eval("window.requestAnimationFrame");}),_nz=new T1(1,_4),_nA=function(_nB,_nC){return function(_){var _nD=E(_nB),_nE=rMV(_nD),_nF=E(_nE);if(!_nF._){var _nG=_nF.a,_nH=E(_nF.b);if(!_nH._){var _=wMV(_nD,_nz);return new T(function(){return B(A1(_nC,_nG));});}else{var _nI=E(_nH.a),_=wMV(_nD,new T2(0,_nI.a,_nH.b));return new T1(1,new T2(1,new T(function(){return B(A1(_nC,_nG));}),new T2(1,new T(function(){return B(A1(_nI.b,_ka));}),_4)));}}else{var _nJ=new T(function(){var _nK=function(_nL){var _nM=new T(function(){return B(A1(_nC,_nL));});return function(_nN){return E(_nM);};};return B(_0(_nF.a,new T2(1,_nK,_4)));}),_=wMV(_nD,new T1(1,_nJ));return _n7;}};},_nO=function(_nP,_nQ){return new T1(0,B(_nA(_nP,_nQ)));},_nR=function(_nS,_nT){var _nU=new T(function(){return new T1(0,B(_n8(_nS,_5,_ka)));});return function(_){var _nV=__createJSFunc(2,function(_nW,_){var _nX=B(_c(_nU,_4,_));return _nx;}),_nY=__app1(E(_ny),_nV);return new T(function(){return B(_nO(_nS,_nT));});};},_nZ=new T1(1,_4),_o0=function(_o1){var _o2=new T(function(){return B(_o3(_));}),_o4=new T(function(){var _o5=function(_o6){return E(_o2);},_o7=function(_){var _o8=nMV(_nZ);return new T(function(){return new T1(0,B(_nR(_o8,_o5)));});};return B(A(_nl,[_kh,_o1,_5,function(_o9){return E(new T1(0,_o7));}]));}),_o3=function(_oa){return E(_o4);};return new F(function(){return _o3(_);});},_ob=function(_oc){return E(E(_oc).a);},_od=function(_oe){return E(E(_oe).d);},_of=function(_og){return E(E(_og).c);},_oh=function(_oi){return E(E(_oi).c);},_oj=new T1(1,_4),_ok=function(_ol){var _om=function(_){var _on=nMV(_oj);return new T(function(){return B(A1(_ol,_on));});};return new T1(0,_om);},_oo=function(_op,_oq){var _or=new T(function(){return B(_oh(_op));}),_os=B(_ob(_op)),_ot=function(_ou){var _ov=new T(function(){return B(A1(_or,new T(function(){return B(A1(_oq,_ou));})));});return new F(function(){return A3(_of,_os,_ov,new T(function(){return B(A2(_od,_os,_ou));}));});};return new F(function(){return A3(_k1,_os,new T(function(){return B(A2(_nj,_op,_ok));}),_ot);});},_ow=function(_ox,_oy,_oz){var _oA=new T(function(){return B(_ob(_ox));}),_oB=new T(function(){return B(A2(_od,_oA,_5));}),_oC=function(_oD,_oE){var _oF=new T(function(){var _oG=new T(function(){return B(A2(_nj,_ox,function(_oH){return new F(function(){return _nO(_oE,_oH);});}));});return B(A3(_k1,_oA,_oG,new T(function(){return B(A1(_oz,_oD));})));});return new F(function(){return A3(_k1,_oA,_oF,function(_oI){var _oJ=E(_oI);if(!_oJ._){return E(_oB);}else{return new F(function(){return _oC(_oJ.a,_oE);});}});});};return new F(function(){return _oo(_ox,function(_oH){return new F(function(){return _oC(_oy,_oH);});});});},_oK=new T(function(){return B(A(_ow,[_kh,_lV,_mY,_o0]));}),_oL=function(_){var _oM=__app2(E(_h),E(_86),E(_jh));return new F(function(){return _c(_oK,_4,_);});},_oN=function(_){return new F(function(){return _oL(_);});};
var hasteMain = function() {B(A(_oN, [0]));};window.onload = hasteMain;