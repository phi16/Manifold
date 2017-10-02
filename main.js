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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=function(_hP){var _hQ=new T(function(){return E(E(_hP).a);}),_hR=new T(function(){return B(_8J(new T(function(){return B(_8H(_hQ));})));}),_hS=new T(function(){return B(A2(_8s,_hR,_8r));}),_hT=function(_hU){var _hV=new T(function(){var _hW=new T(function(){var _hX=new T(function(){var _hY=new T(function(){return E(E(_hU).c);});return B(A3(_8L,_hR,_hY,_hY));}),_hZ=new T(function(){var _i0=new T(function(){return E(E(_hU).a);});return B(A3(_8L,_hR,_i0,_i0));});return B(A3(_6X,_hR,_hZ,_hX));});return B(A2(_9t,_hQ,_hW));});return new F(function(){return A3(_9p,_hR,_hV,_hS);});};return E(_hT);},_i1=function(_ef,_ee){return new T2(0,_ef,_ee);},_i2=function(_i3,_i4,_i5){var _i6=new T(function(){var _i7=E(_i3),_i8=_i7.a,_i9=new T(function(){return B(A1(_i7.b,new T(function(){return B(_8J(B(_8H(E(_i7.c).a))));})));});return B(A3(_8R,_i8,new T(function(){return B(A3(_8T,B(_8F(_i8)),_i1,_i5));}),_i9));});return E(B(A1(_i4,_i6)).b);},_ia=function(_ib){var _ic=new T(function(){return E(E(_ib).a);}),_id=new T(function(){return E(E(_ib).b);}),_ie=new T(function(){var _if=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),_ig=new T(function(){var _ih=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_eb(_ih,new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_hO(new T2(0,_ig,_if)));});return function(_ii){return new F(function(){return _i2(new T3(0,_8p,_8u,new T2(0,_ic,_id)),_ie,_ii);});};},_ij=new T(function(){return B(_ia(_7V));}),_ik=new T(function(){return B(A1(_ij,_E));}),_il=new T(function(){return E(E(_ik).a);}),_im=new T(function(){return B(unCStr(",y:"));}),_in=new T1(0,_im),_io=new T(function(){return E(E(_ik).b);}),_ip=new T(function(){return B(unCStr(",z:"));}),_iq=new T1(0,_ip),_ir=new T(function(){return E(E(_ik).c);}),_is=new T(function(){return B(unCStr("})"));}),_it=new T1(0,_is),_iu=new T2(1,_it,_w),_iv=new T2(1,_ir,_iu),_iw=new T2(1,_iq,_iv),_ix=new T2(1,_io,_iw),_iy=new T2(1,_in,_ix),_iz=new T2(1,_il,_iy),_iA=new T(function(){return B(unCStr("({x:"));}),_iB=new T1(0,_iA),_iC=new T2(1,_iB,_iz),_iD=function(_iE){return E(_iE);},_iF=new T(function(){return toJSStr(B(_e(_x,_iD,_iC)));}),_iG=new T(function(){return B(_hO(_7V));}),_iH=new T(function(){return B(A1(_iG,_E));}),_iI=new T(function(){return toJSStr(B(_4(_x,_iD,_iH)));}),_iJ=function(_iK,_iL,_iM){var _iN=E(_iM);if(!_iN._){return new F(function(){return A1(_iL,_iN.a);});}else{var _iO=new T(function(){return B(_0(_iK));}),_iP=new T(function(){return B(_2(_iK));}),_iQ=function(_iR){var _iS=E(_iR);if(!_iS._){return E(_iP);}else{return new F(function(){return A2(_iO,new T(function(){return B(_iJ(_iK,_iL,_iS.a));}),new T(function(){return B(_iQ(_iS.b));}));});}};return new F(function(){return _iQ(_iN.a);});}},_iT=new T(function(){return B(unCStr("x"));}),_iU=new T1(0,_iT),_iV=new T(function(){return B(unCStr("y"));}),_iW=new T1(0,_iV),_iX=new T(function(){return B(unCStr("z"));}),_iY=new T1(0,_iX),_iZ=new T3(0,E(_iU),E(_iW),E(_iY)),_j0=new T(function(){return B(unCStr(","));}),_j1=new T1(0,_j0),_j2=new T(function(){return B(unCStr("pow("));}),_j3=new T1(0,_j2),_j4=new T(function(){return B(unCStr(")"));}),_j5=new T1(0,_j4),_j6=new T2(1,_j5,_w),_j7=function(_j8,_j9){return new T1(1,new T2(1,_j3,new T2(1,_j8,new T2(1,_j1,new T2(1,_j9,_j6)))));},_ja=new T(function(){return B(unCStr("acos("));}),_jb=new T1(0,_ja),_jc=function(_jd){return new T1(1,new T2(1,_jb,new T2(1,_jd,_j6)));},_je=new T(function(){return B(unCStr("acosh("));}),_jf=new T1(0,_je),_jg=function(_jh){return new T1(1,new T2(1,_jf,new T2(1,_jh,_j6)));},_ji=new T(function(){return B(unCStr("asin("));}),_jj=new T1(0,_ji),_jk=function(_jl){return new T1(1,new T2(1,_jj,new T2(1,_jl,_j6)));},_jm=new T(function(){return B(unCStr("asinh("));}),_jn=new T1(0,_jm),_jo=function(_jp){return new T1(1,new T2(1,_jn,new T2(1,_jp,_j6)));},_jq=new T(function(){return B(unCStr("atan("));}),_jr=new T1(0,_jq),_js=function(_jt){return new T1(1,new T2(1,_jr,new T2(1,_jt,_j6)));},_ju=new T(function(){return B(unCStr("atanh("));}),_jv=new T1(0,_ju),_jw=function(_jx){return new T1(1,new T2(1,_jv,new T2(1,_jx,_j6)));},_jy=new T(function(){return B(unCStr("cos("));}),_jz=new T1(0,_jy),_jA=function(_jB){return new T1(1,new T2(1,_jz,new T2(1,_jB,_j6)));},_jC=new T(function(){return B(unCStr("cosh("));}),_jD=new T1(0,_jC),_jE=function(_jF){return new T1(1,new T2(1,_jD,new T2(1,_jF,_j6)));},_jG=new T(function(){return B(unCStr("exp("));}),_jH=new T1(0,_jG),_jI=function(_jJ){return new T1(1,new T2(1,_jH,new T2(1,_jJ,_j6)));},_jK=new T(function(){return B(unCStr("log("));}),_jL=new T1(0,_jK),_jM=function(_jN){return new T1(1,new T2(1,_jL,new T2(1,_jN,_j6)));},_jO=new T(function(){return B(unCStr(")/log("));}),_jP=new T1(0,_jO),_jQ=function(_jR,_jS){return new T1(1,new T2(1,_jL,new T2(1,_jS,new T2(1,_jP,new T2(1,_jR,_j6)))));},_jT=new T(function(){return B(unCStr("pi"));}),_jU=new T1(0,_jT),_jV=new T(function(){return B(unCStr("sin("));}),_jW=new T1(0,_jV),_jX=function(_jY){return new T1(1,new T2(1,_jW,new T2(1,_jY,_j6)));},_jZ=new T(function(){return B(unCStr("sinh("));}),_k0=new T1(0,_jZ),_k1=function(_k2){return new T1(1,new T2(1,_k0,new T2(1,_k2,_j6)));},_k3=new T(function(){return B(unCStr("sqrt("));}),_k4=new T1(0,_k3),_k5=function(_k6){return new T1(1,new T2(1,_k4,new T2(1,_k6,_j6)));},_k7=new T(function(){return B(unCStr("tan("));}),_k8=new T1(0,_k7),_k9=function(_ka){return new T1(1,new T2(1,_k8,new T2(1,_ka,_j6)));},_kb=new T(function(){return B(unCStr("tanh("));}),_kc=new T1(0,_kb),_kd=function(_ke){return new T1(1,new T2(1,_kc,new T2(1,_ke,_j6)));},_kf=new T(function(){return B(unCStr("("));}),_kg=new T1(0,_kf),_kh=new T(function(){return B(unCStr(")/("));}),_ki=new T1(0,_kh),_kj=function(_kk,_kl){return new T1(1,new T2(1,_kg,new T2(1,_kk,new T2(1,_ki,new T2(1,_kl,_j6)))));},_km=function(_kn){return new T1(0,new T(function(){var _ko=E(_kn),_kp=jsShow(B(_6y(_ko.a,_ko.b)));return fromJSStr(_kp);}));},_kq=new T(function(){return B(unCStr("1./("));}),_kr=new T1(0,_kq),_ks=function(_kt){return new T1(1,new T2(1,_kr,new T2(1,_kt,_j6)));},_ku=new T(function(){return B(unCStr(")+("));}),_kv=new T1(0,_ku),_kw=function(_kx,_ky){return new T1(1,new T2(1,_kg,new T2(1,_kx,new T2(1,_kv,new T2(1,_ky,_j6)))));},_kz=new T(function(){return B(unCStr("-("));}),_kA=new T1(0,_kz),_kB=function(_kC){return new T1(1,new T2(1,_kA,new T2(1,_kC,_j6)));},_kD=new T(function(){return B(unCStr(")*("));}),_kE=new T1(0,_kD),_kF=function(_kG,_kH){return new T1(1,new T2(1,_kg,new T2(1,_kG,new T2(1,_kE,new T2(1,_kH,_j6)))));},_kI=function(_kJ,_kK){return new F(function(){return A3(_6X,_kL,_kJ,new T(function(){return B(A2(_6Z,_kL,_kK));}));});},_kM=new T(function(){return B(unCStr("abs("));}),_kN=new T1(0,_kM),_kO=function(_kP){return new T1(1,new T2(1,_kN,new T2(1,_kP,_j6)));},_kQ=new T(function(){return B(unCStr("."));}),_kR=function(_kS){return new T1(0,new T(function(){return B(_n(B(_7i(0,_kS,_w)),_kQ));}));},_kT=new T(function(){return B(unCStr("sign("));}),_kU=new T1(0,_kT),_kV=function(_kW){return new T1(1,new T2(1,_kU,new T2(1,_kW,_j6)));},_kL=new T(function(){return {_:0,a:_kw,b:_kI,c:_kF,d:_kB,e:_kO,f:_kV,g:_kR};}),_kX=new T4(0,_kL,_kj,_ks,_km),_kY={_:0,a:_kX,b:_jU,c:_jI,d:_jM,e:_k5,f:_j7,g:_jQ,h:_jX,i:_jA,j:_k9,k:_jk,l:_jc,m:_js,n:_k1,o:_jE,p:_kd,q:_jo,r:_jg,s:_jw},_kZ=new T(function(){return B(unCStr("(/=) is not defined"));}),_l0=new T(function(){return B(err(_kZ));}),_l1=new T(function(){return B(unCStr("(==) is not defined"));}),_l2=new T(function(){return B(err(_l1));}),_l3=new T2(0,_l2,_l0),_l4=new T(function(){return B(unCStr("(<) is not defined"));}),_l5=new T(function(){return B(err(_l4));}),_l6=new T(function(){return B(unCStr("(<=) is not defined"));}),_l7=new T(function(){return B(err(_l6));}),_l8=new T(function(){return B(unCStr("(>) is not defined"));}),_l9=new T(function(){return B(err(_l8));}),_la=new T(function(){return B(unCStr("(>=) is not defined"));}),_lb=new T(function(){return B(err(_la));}),_lc=new T(function(){return B(unCStr("compare is not defined"));}),_ld=new T(function(){return B(err(_lc));}),_le=new T(function(){return B(unCStr("max("));}),_lf=new T1(0,_le),_lg=function(_lh,_li){return new T1(1,new T2(1,_lf,new T2(1,_lh,new T2(1,_j1,new T2(1,_li,_j6)))));},_lj=new T(function(){return B(unCStr("min("));}),_lk=new T1(0,_lj),_ll=function(_lm,_ln){return new T1(1,new T2(1,_lk,new T2(1,_lm,new T2(1,_j1,new T2(1,_ln,_j6)))));},_lo={_:0,a:_l3,b:_ld,c:_l5,d:_l7,e:_l9,f:_lb,g:_lg,h:_ll},_lp=new T2(0,_kY,_lo),_lq=new T(function(){return B(_hO(_lp));}),_lr=new T(function(){return B(A1(_lq,_iZ));}),_ls=new T(function(){return toJSStr(B(_iJ(_x,_iD,_lr)));}),_lt=new T(function(){return eval("__strict(compile)");}),_lu=function(_lv,_lw,_lx,_ly){var _lz=B(_8J(B(_8H(_lv)))),_lA=new T(function(){var _lB=new T(function(){return B(A3(_6X,_lz,new T(function(){return B(A3(_8L,_lz,_lw,_lw));}),new T(function(){return B(A3(_8L,_lz,_ly,_ly));})));});return B(A2(_9t,_lv,_lB));});return new F(function(){return A3(_9p,_lz,_lA,new T(function(){return B(A2(_bU,_lv,_lx));}));});},_lC=new T(function(){return B(_lu(_kY,_iU,_iW,_iY));}),_lD=new T(function(){return toJSStr(B(_iJ(_x,_iD,_lC)));}),_lE=function(_lF,_lG,_lH){var _lI=new T(function(){return B(_0(_lF));}),_lJ=new T(function(){return B(_2(_lF));}),_lK=function(_lL){var _lM=E(_lL);if(!_lM._){return E(_lJ);}else{return new F(function(){return A2(_lI,new T(function(){return B(_iJ(_lF,_lG,_lM.a));}),new T(function(){return B(_lK(_lM.b));}));});}};return new F(function(){return _lK(_lH);});},_lN=function(_lO){var _lP=new T(function(){return E(E(_lO).a);}),_lQ=new T3(0,_8p,_8u,new T2(0,_lP,new T(function(){return E(E(_lO).b);}))),_lR=new T(function(){return B(_eb(new T(function(){return B(_f7(new T(function(){return B(_fQ(_lQ));}),_lQ));}),_lQ));}),_lS=new T(function(){return B(_8J(new T(function(){return B(_8H(_lP));})));});return function(_lT){var _lU=E(_lT),_lV=B(A2(_8s,_lS,_8r)),_lW=B(A2(_8s,_lS,_8q));return E(B(_lu(_lR,new T2(0,_lU.a,new T3(0,E(_lV),E(_lW),E(_lW))),new T2(0,_lU.b,new T3(0,E(_lW),E(_lV),E(_lW))),new T2(0,_lU.c,new T3(0,E(_lW),E(_lW),E(_lV))))).b);};},_lX=new T(function(){return B(_lN(_lp));}),_lY=function(_lZ,_m0){var _m1=E(_m0);return (_m1._==0)?__Z:new T2(1,_lZ,new T2(1,_m1.a,new T(function(){return B(_lY(_lZ,_m1.b));})));},_m2=new T(function(){var _m3=B(A1(_lX,_iZ));return new T2(1,_m3.a,new T(function(){return B(_lY(_j1,new T2(1,_m3.b,new T2(1,_m3.c,_w))));}));}),_m4=new T1(1,_m2),_m5=new T2(1,_m4,_j6),_m6=new T(function(){return B(unCStr("vec3("));}),_m7=new T1(0,_m6),_m8=new T2(1,_m7,_m5),_m9=new T(function(){return toJSStr(B(_lE(_x,_iD,_m8)));}),_ma=function(_mb,_mc){while(1){var _md=E(_mb);if(!_md._){return E(_mc);}else{var _me=_mc+1|0;_mb=_md.b;_mc=_me;continue;}}},_mf=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_mg=new T(function(){return B(err(_mf));}),_mh=0,_mi=new T3(0,E(_mh),E(_mh),E(_mh)),_mj=new T(function(){return B(unCStr("Negative exponent"));}),_mk=new T(function(){return B(err(_mj));}),_ml=function(_mm,_mn,_mo){while(1){if(!(_mn%2)){var _mp=_mm*_mm,_mq=quot(_mn,2);_mm=_mp;_mn=_mq;continue;}else{var _mr=E(_mn);if(_mr==1){return _mm*_mo;}else{var _mp=_mm*_mm,_ms=_mm*_mo;_mm=_mp;_mn=quot(_mr-1|0,2);_mo=_ms;continue;}}}},_mt=function(_mu,_mv){while(1){if(!(_mv%2)){var _mw=_mu*_mu,_mx=quot(_mv,2);_mu=_mw;_mv=_mx;continue;}else{var _my=E(_mv);if(_my==1){return E(_mu);}else{return new F(function(){return _ml(_mu*_mu,quot(_my-1|0,2),_mu);});}}}},_mz=function(_mA){var _mB=E(_mA);return new F(function(){return Math.log(_mB+(_mB+1)*Math.sqrt((_mB-1)/(_mB+1)));});},_mC=function(_mD){var _mE=E(_mD);return new F(function(){return Math.log(_mE+Math.sqrt(1+_mE*_mE));});},_mF=function(_mG){var _mH=E(_mG);return 0.5*Math.log((1+_mH)/(1-_mH));},_mI=function(_mJ,_mK){return Math.log(E(_mK))/Math.log(E(_mJ));},_mL=3.141592653589793,_mM=function(_mN){var _mO=E(_mN);return new F(function(){return _6y(_mO.a,_mO.b);});},_mP=function(_mQ){return 1/E(_mQ);},_mR=function(_mS){var _mT=E(_mS),_mU=E(_mT);return (_mU==0)?E(_6x):(_mU<=0)? -_mU:E(_mT);},_mV=function(_mW){var _mX=E(_mW);if(!_mX._){return _mX.a;}else{return new F(function(){return I_toNumber(_mX.a);});}},_mY=function(_mZ){return new F(function(){return _mV(_mZ);});},_n0=1,_n1=-1,_n2=function(_n3){var _n4=E(_n3);return (_n4<=0)?(_n4>=0)?E(_n4):E(_n1):E(_n0);},_n5=function(_n6,_n7){return E(_n6)-E(_n7);},_n8=function(_n9){return  -E(_n9);},_na=function(_nb,_nc){return E(_nb)+E(_nc);},_nd=function(_ne,_nf){return E(_ne)*E(_nf);},_ng={_:0,a:_na,b:_n5,c:_nd,d:_n8,e:_mR,f:_n2,g:_mY},_nh=function(_ni,_nj){return E(_ni)/E(_nj);},_nk=new T4(0,_ng,_nh,_mP,_mM),_nl=function(_nm){return new F(function(){return Math.acos(E(_nm));});},_nn=function(_no){return new F(function(){return Math.asin(E(_no));});},_np=function(_nq){return new F(function(){return Math.atan(E(_nq));});},_nr=function(_ns){return new F(function(){return Math.cos(E(_ns));});},_nt=function(_nu){return new F(function(){return cosh(E(_nu));});},_nv=function(_nw){return new F(function(){return Math.exp(E(_nw));});},_nx=function(_ny){return new F(function(){return Math.log(E(_ny));});},_nz=function(_nA,_nB){return new F(function(){return Math.pow(E(_nA),E(_nB));});},_nC=function(_nD){return new F(function(){return Math.sin(E(_nD));});},_nE=function(_nF){return new F(function(){return sinh(E(_nF));});},_nG=function(_nH){return new F(function(){return Math.sqrt(E(_nH));});},_nI=function(_nJ){return new F(function(){return Math.tan(E(_nJ));});},_nK=function(_nL){return new F(function(){return tanh(E(_nL));});},_nM={_:0,a:_nk,b:_mL,c:_nv,d:_nx,e:_nG,f:_nz,g:_mI,h:_nC,i:_nr,j:_nI,k:_nn,l:_nl,m:_np,n:_nE,o:_nt,p:_nK,q:_mC,r:_mz,s:_mF},_nN=function(_nO,_nP){return (E(_nO)!=E(_nP))?true:false;},_nQ=function(_nR,_nS){return E(_nR)==E(_nS);},_nT=new T2(0,_nQ,_nN),_nU=function(_nV,_nW){return E(_nV)<E(_nW);},_nX=function(_nY,_nZ){return E(_nY)<=E(_nZ);},_o0=function(_o1,_o2){return E(_o1)>E(_o2);},_o3=function(_o4,_o5){return E(_o4)>=E(_o5);},_o6=function(_o7,_o8){var _o9=E(_o7),_oa=E(_o8);return (_o9>=_oa)?(_o9!=_oa)?2:1:0;},_ob=function(_oc,_od){var _oe=E(_oc),_of=E(_od);return (_oe>_of)?E(_oe):E(_of);},_og=function(_oh,_oi){var _oj=E(_oh),_ok=E(_oi);return (_oj>_ok)?E(_ok):E(_oj);},_ol={_:0,a:_nT,b:_o6,c:_nU,d:_nX,e:_o0,f:_o3,g:_ob,h:_og},_om="dz",_on="wy",_oo="wx",_op="dy",_oq="dx",_or="t",_os="a",_ot="r",_ou="ly",_ov="lx",_ow="wz",_ox=0,_oy=function(_oz){var _oA=__new(),_oB=_oA,_oC=function(_oD,_){while(1){var _oE=E(_oD);if(!_oE._){return _ox;}else{var _oF=E(_oE.a),_oG=__set(_oB,E(_oF.a),E(_oF.b));_oD=_oE.b;continue;}}},_oH=B(_oC(_oz,_));return E(_oB);},_oI=function(_oJ,_oK,_oL,_oM,_oN,_oO,_oP,_oQ,_oR){return new F(function(){return _oy(new T2(1,new T2(0,_oo,_oJ),new T2(1,new T2(0,_on,_oK),new T2(1,new T2(0,_ow,_oL),new T2(1,new T2(0,_ov,_oM*_oN*Math.cos(_oO)),new T2(1,new T2(0,_ou,_oM*_oN*Math.sin(_oO)),new T2(1,new T2(0,_ot,_oM),new T2(1,new T2(0,_os,_oN),new T2(1,new T2(0,_or,_oO),new T2(1,new T2(0,_oq,_oP),new T2(1,new T2(0,_op,_oQ),new T2(1,new T2(0,_om,_oR),_w))))))))))));});},_oS=function(_oT){var _oU=E(_oT),_oV=E(_oU.a),_oW=E(_oU.b),_oX=E(_oU.d);return new F(function(){return _oI(_oV.a,_oV.b,_oV.c,E(_oW.a),E(_oW.b),E(_oU.c),_oX.a,_oX.b,_oX.c);});},_oY=function(_oZ,_p0){var _p1=E(_p0);return (_p1._==0)?__Z:new T2(1,new T(function(){return B(A1(_oZ,_p1.a));}),new T(function(){return B(_oY(_oZ,_p1.b));}));},_p2=function(_p3,_p4,_p5){var _p6=__lst2arr(B(_oY(_oS,new T2(1,_p3,new T2(1,_p4,new T2(1,_p5,_w))))));return E(_p6);},_p7=function(_p8){var _p9=E(_p8);return new F(function(){return _p2(_p9.a,_p9.b,_p9.c);});},_pa=new T2(0,_nM,_ol),_pb=function(_pc,_pd,_pe,_pf,_pg,_ph,_pi){var _pj=B(_8J(B(_8H(_pc)))),_pk=new T(function(){return B(A3(_6X,_pj,new T(function(){return B(A3(_8L,_pj,_pd,_pg));}),new T(function(){return B(A3(_8L,_pj,_pe,_ph));})));});return new F(function(){return A3(_6X,_pj,_pk,new T(function(){return B(A3(_8L,_pj,_pf,_pi));}));});},_pl=function(_pm,_pn,_po,_pp){var _pq=B(_8H(_pm)),_pr=new T(function(){return B(A2(_9t,_pm,new T(function(){return B(_pb(_pm,_pn,_po,_pp,_pn,_po,_pp));})));});return new T3(0,B(A3(_8P,_pq,_pn,_pr)),B(A3(_8P,_pq,_po,_pr)),B(A3(_8P,_pq,_pp,_pr)));},_ps=function(_pt,_pu,_pv,_pw,_px,_py,_pz){var _pA=B(_8L(_pt));return new T3(0,B(A1(B(A1(_pA,_pu)),_px)),B(A1(B(A1(_pA,_pv)),_py)),B(A1(B(A1(_pA,_pw)),_pz)));},_pB=function(_pC,_pD,_pE,_pF,_pG,_pH,_pI){var _pJ=B(_6X(_pC));return new T3(0,B(A1(B(A1(_pJ,_pD)),_pG)),B(A1(B(A1(_pJ,_pE)),_pH)),B(A1(B(A1(_pJ,_pF)),_pI)));},_pK=function(_pL,_pM){var _pN=new T(function(){return E(E(_pL).a);}),_pO=new T(function(){return B(A2(_lN,new T2(0,_pN,new T(function(){return E(E(_pL).b);})),_pM));}),_pP=new T(function(){var _pQ=E(_pO),_pR=B(_pl(_pN,_pQ.a,_pQ.b,_pQ.c));return new T3(0,E(_pR.a),E(_pR.b),E(_pR.c));}),_pS=new T(function(){var _pT=E(_pM),_pU=_pT.a,_pV=_pT.b,_pW=_pT.c,_pX=E(_pP),_pY=B(_8H(_pN)),_pZ=new T(function(){return B(A2(_9t,_pN,new T(function(){var _q0=E(_pO),_q1=_q0.a,_q2=_q0.b,_q3=_q0.c;return B(_pb(_pN,_q1,_q2,_q3,_q1,_q2,_q3));})));}),_q4=B(A3(_8P,_pY,new T(function(){return B(_lu(_pN,_pU,_pV,_pW));}),_pZ)),_q5=B(_8J(_pY)),_q6=B(_ps(_q5,_pX.a,_pX.b,_pX.c,_q4,_q4,_q4)),_q7=B(_6Z(_q5)),_q8=B(_pB(_q5,_pU,_pV,_pW,B(A1(_q7,_q6.a)),B(A1(_q7,_q6.b)),B(A1(_q7,_q6.c))));return new T3(0,E(_q8.a),E(_q8.b),E(_q8.c));});return new T2(0,_pS,_pP);},_q9=function(_qa){return E(E(_qa).a);},_qb=function(_qc,_qd,_qe,_qf,_qg,_qh,_qi){var _qj=B(_pb(_qc,_qg,_qh,_qi,_qd,_qe,_qf)),_qk=B(_8J(B(_8H(_qc)))),_ql=B(_ps(_qk,_qg,_qh,_qi,_qj,_qj,_qj)),_qm=B(_6Z(_qk));return new F(function(){return _pB(_qk,_qd,_qe,_qf,B(A1(_qm,_ql.a)),B(A1(_qm,_ql.b)),B(A1(_qm,_ql.c)));});},_qn=function(_qo){return E(E(_qo).a);},_qp=function(_qq,_qr,_qs,_qt){var _qu=new T(function(){var _qv=E(_qt),_qw=E(_qs),_qx=B(_qb(_qq,_qv.a,_qv.b,_qv.c,_qw.a,_qw.b,_qw.c));return new T3(0,E(_qx.a),E(_qx.b),E(_qx.c));}),_qy=new T(function(){return B(A2(_9t,_qq,new T(function(){var _qz=E(_qu),_qA=_qz.a,_qB=_qz.b,_qC=_qz.c;return B(_pb(_qq,_qA,_qB,_qC,_qA,_qB,_qC));})));});if(!B(A3(_qn,B(_q9(_qr)),_qy,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_qq)))),_8q));})))){var _qD=E(_qu),_qE=B(_pl(_qq,_qD.a,_qD.b,_qD.c)),_qF=B(A2(_9t,_qq,new T(function(){var _qG=E(_qt),_qH=_qG.a,_qI=_qG.b,_qJ=_qG.c;return B(_pb(_qq,_qH,_qI,_qJ,_qH,_qI,_qJ));}))),_qK=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_qq));})));})));return new T3(0,B(A1(B(A1(_qK,_qE.a)),_qF)),B(A1(B(A1(_qK,_qE.b)),_qF)),B(A1(B(A1(_qK,_qE.c)),_qF)));}else{var _qL=B(A2(_8s,B(_8J(B(_8H(_qq)))),_8q));return new T3(0,_qL,_qL,_qL);}},_qM=function(_qN,_qO){while(1){var _qP=E(_qN);if(!_qP._){return E(_qO);}else{var _qQ=_qP.b,_qR=E(_qP.a);if(_qO>_qR){_qN=_qQ;continue;}else{_qN=_qQ;_qO=_qR;continue;}}}},_qS=new T(function(){var _qT=eval("angleCount"),_qU=Number(_qT);return jsTrunc(_qU);}),_qV=new T(function(){return E(_qS);}),_qW=new T(function(){return B(unCStr(": empty list"));}),_qX=new T(function(){return B(unCStr("Prelude."));}),_qY=function(_qZ){return new F(function(){return err(B(_n(_qX,new T(function(){return B(_n(_qZ,_qW));},1))));});},_r0=new T(function(){return B(unCStr("head"));}),_r1=new T(function(){return B(_qY(_r0));}),_r2=function(_r3,_r4,_r5){var _r6=E(_r3);if(!_r6._){return __Z;}else{var _r7=E(_r4);if(!_r7._){return __Z;}else{var _r8=_r7.a,_r9=E(_r5);if(!_r9._){return __Z;}else{var _ra=E(_r9.a),_rb=_ra.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_r6.a),E(_r8),E(_rb));}),new T2(1,new T(function(){return new T3(0,E(_r8),E(_rb),E(_ra.b));}),_w)),new T(function(){return B(_r2(_r6.b,_r7.b,_r9.b));},1));});}}}},_rc=new T(function(){return B(unCStr("tail"));}),_rd=new T(function(){return B(_qY(_rc));}),_re=function(_rf,_rg){var _rh=E(_rf);if(!_rh._){return __Z;}else{var _ri=E(_rg);return (_ri._==0)?__Z:new T2(1,new T2(0,_rh.a,_ri.a),new T(function(){return B(_re(_rh.b,_ri.b));}));}},_rj=function(_rk,_rl){var _rm=E(_rk);if(!_rm._){return __Z;}else{var _rn=E(_rl);if(!_rn._){return __Z;}else{var _ro=E(_rm.a),_rp=_ro.b,_rq=E(_rn.a).b,_rr=new T(function(){var _rs=new T(function(){return B(_re(_rq,new T(function(){var _rt=E(_rq);if(!_rt._){return E(_rd);}else{return E(_rt.b);}},1)));},1);return B(_r2(_rp,new T(function(){var _ru=E(_rp);if(!_ru._){return E(_rd);}else{return E(_ru.b);}},1),_rs));});return new F(function(){return _n(new T2(1,new T(function(){var _rv=E(_rp);if(!_rv._){return E(_r1);}else{var _rw=E(_rq);if(!_rw._){return E(_r1);}else{return new T3(0,E(_ro.a),E(_rv.a),E(_rw.a));}}}),_rr),new T(function(){return B(_rj(_rm.b,_rn.b));},1));});}}},_rx=new T(function(){return 6.283185307179586/E(_qV);}),_ry=new T(function(){return E(_qV)-1;}),_rz=new T1(0,1),_rA=function(_rB,_rC){var _rD=E(_rC),_rE=new T(function(){var _rF=B(_8J(_rB)),_rG=B(_rA(_rB,B(A3(_6X,_rF,_rD,new T(function(){return B(A2(_8s,_rF,_rz));})))));return new T2(1,_rG.a,_rG.b);});return new T2(0,_rD,_rE);},_rH=function(_rI){return E(E(_rI).d);},_rJ=new T1(0,2),_rK=function(_rL,_rM){var _rN=E(_rM);if(!_rN._){return __Z;}else{var _rO=_rN.a;return (!B(A1(_rL,_rO)))?__Z:new T2(1,_rO,new T(function(){return B(_rK(_rL,_rN.b));}));}},_rP=function(_rQ,_rR,_rS,_rT){var _rU=B(_rA(_rR,_rS)),_rV=new T(function(){var _rW=B(_8J(_rR)),_rX=new T(function(){return B(A3(_8P,_rR,new T(function(){return B(A2(_8s,_rW,_rz));}),new T(function(){return B(A2(_8s,_rW,_rJ));})));});return B(A3(_6X,_rW,_rT,_rX));});return new F(function(){return _rK(function(_rY){return new F(function(){return A3(_rH,_rQ,_rY,_rV);});},new T2(1,_rU.a,_rU.b));});},_rZ=new T(function(){return B(_rP(_ol,_nk,_mh,_ry));}),_s0=function(_s1,_s2){while(1){var _s3=E(_s1);if(!_s3._){return E(_s2);}else{_s1=_s3.b;_s2=_s3.a;continue;}}},_s4=new T(function(){return B(unCStr("last"));}),_s5=new T(function(){return B(_qY(_s4));}),_s6=function(_s7){return new F(function(){return _s0(_s7,_s5);});},_s8=function(_s9){return new F(function(){return _s6(E(_s9).b);});},_sa=new T(function(){return B(unCStr("maximum"));}),_sb=new T(function(){return B(_qY(_sa));}),_sc=new T(function(){var _sd=eval("proceedCount"),_se=Number(_sd);return jsTrunc(_se);}),_sf=new T(function(){return E(_sc);}),_sg=1,_sh=new T(function(){return B(_rP(_ol,_nk,_sg,_sf));}),_si=function(_sj,_sk,_sl,_sm,_sn,_so,_sp,_sq,_sr,_ss,_st,_su,_sv,_sw){var _sx=new T(function(){var _sy=new T(function(){var _sz=E(_ss),_sA=E(_sw),_sB=E(_sv),_sC=E(_st),_sD=E(_su),_sE=E(_sr);return new T3(0,_sz*_sA-_sB*_sC,_sC*_sD-_sA*_sE,_sE*_sB-_sD*_sz);}),_sF=function(_sG){var _sH=new T(function(){var _sI=E(_sG)/E(_qV);return (_sI+_sI)*3.141592653589793;}),_sJ=new T(function(){return B(A1(_sj,_sH));}),_sK=new T(function(){var _sL=new T(function(){var _sM=E(_sJ)/E(_sf);return new T3(0,E(_sM),E(_sM),E(_sM));}),_sN=function(_sO,_sP){var _sQ=E(_sO);if(!_sQ._){return new T2(0,_w,_sP);}else{var _sR=new T(function(){var _sS=B(_pK(_pa,new T(function(){var _sT=E(_sP),_sU=E(_sT.a),_sV=E(_sT.b),_sW=E(_sL);return new T3(0,E(_sU.a)+E(_sV.a)*E(_sW.a),E(_sU.b)+E(_sV.b)*E(_sW.b),E(_sU.c)+E(_sV.c)*E(_sW.c));}))),_sX=_sS.a,_sY=new T(function(){var _sZ=E(_sS.b),_t0=E(E(_sP).b),_t1=B(_qb(_nM,_t0.a,_t0.b,_t0.c,_sZ.a,_sZ.b,_sZ.c)),_t2=B(_pl(_nM,_t1.a,_t1.b,_t1.c));return new T3(0,E(_t2.a),E(_t2.b),E(_t2.c));});return new T2(0,new T(function(){var _t3=E(_sJ),_t4=E(_sH);return new T4(0,E(_sX),E(new T2(0,E(_sQ.a)/E(_sf),E(_t3))),E(_t4),E(_sY));}),new T2(0,_sX,_sY));}),_t5=new T(function(){var _t6=B(_sN(_sQ.b,new T(function(){return E(E(_sR).b);})));return new T2(0,_t6.a,_t6.b);});return new T2(0,new T2(1,new T(function(){return E(E(_sR).a);}),new T(function(){return E(E(_t5).a);})),new T(function(){return E(E(_t5).b);}));}},_t7=function(_t8,_t9,_ta,_tb,_tc){var _td=E(_t8);if(!_td._){return new T2(0,_w,new T2(0,new T3(0,E(_t9),E(_ta),E(_tb)),_tc));}else{var _te=new T(function(){var _tf=B(_pK(_pa,new T(function(){var _tg=E(_tc),_th=E(_sL);return new T3(0,E(_t9)+E(_tg.a)*E(_th.a),E(_ta)+E(_tg.b)*E(_th.b),E(_tb)+E(_tg.c)*E(_th.c));}))),_ti=_tf.a,_tj=new T(function(){var _tk=E(_tf.b),_tl=E(_tc),_tm=B(_qb(_nM,_tl.a,_tl.b,_tl.c,_tk.a,_tk.b,_tk.c)),_tn=B(_pl(_nM,_tm.a,_tm.b,_tm.c));return new T3(0,E(_tn.a),E(_tn.b),E(_tn.c));});return new T2(0,new T(function(){var _to=E(_sJ),_tp=E(_sH);return new T4(0,E(_ti),E(new T2(0,E(_td.a)/E(_sf),E(_to))),E(_tp),E(_tj));}),new T2(0,_ti,_tj));}),_tq=new T(function(){var _tr=B(_sN(_td.b,new T(function(){return E(E(_te).b);})));return new T2(0,_tr.a,_tr.b);});return new T2(0,new T2(1,new T(function(){return E(E(_te).a);}),new T(function(){return E(E(_tq).a);})),new T(function(){return E(E(_tq).b);}));}};return E(B(_t7(_sh,_sm,_sn,_so,new T(function(){var _ts=E(_sy),_tt=E(_sH)+_sp,_tu=Math.cos(_tt),_tv=Math.sin(_tt);return new T3(0,E(_sr)*_tu+E(_ts.a)*_tv,E(_ss)*_tu+E(_ts.b)*_tv,E(_st)*_tu+E(_ts.c)*_tv);}))).a);});return new T2(0,new T(function(){var _tw=E(_sJ),_tx=E(_sH);return new T4(0,E(new T3(0,E(_sm),E(_sn),E(_so))),E(new T2(0,E(_mh),E(_tw))),E(_tx),E(_mi));}),_sK);};return B(_oY(_sF,_rZ));}),_ty=new T(function(){var _tz=function(_tA){return new F(function(){return A1(_sj,new T(function(){return B(_nd(_tA,_rx));}));});},_tB=B(_oY(_tz,_rZ));if(!_tB._){return E(_sb);}else{return B(_qM(_tB.b,E(_tB.a)));}}),_tC=new T(function(){var _tD=new T(function(){var _tE=B(_n(_sx,new T2(1,new T(function(){var _tF=E(_sx);if(!_tF._){return E(_r1);}else{return E(_tF.a);}}),_w)));if(!_tE._){return E(_rd);}else{return E(_tE.b);}},1);return B(_rj(_sx,_tD));});return new T3(0,_tC,new T(function(){return B(_oY(_s8,_sx));}),_ty);},_tG=function(_tH,_tI,_tJ,_tK,_tL,_tM,_tN,_tO,_tP,_tQ,_tR,_tS,_tT,_tU,_tV,_tW,_tX,_tY){var _tZ=B(_pK(_pa,new T3(0,E(_tK),E(_tL),E(_tM)))),_u0=_tZ.b,_u1=E(_tZ.a),_u2=B(_qp(_nM,_ol,_u0,new T3(0,E(_tO),E(_tP),E(_tQ)))),_u3=E(_u0),_u4=_u3.a,_u5=_u3.b,_u6=_u3.c,_u7=B(_qb(_nM,_tS,_tT,_tU,_u4,_u5,_u6)),_u8=B(_pl(_nM,_u7.a,_u7.b,_u7.c)),_u9=_u8.a,_ua=_u8.b,_ub=_u8.c,_uc=E(_tN),_ud=new T2(0,E(new T3(0,E(_u2.a),E(_u2.b),E(_u2.c))),E(_tR)),_ue=B(_si(_tH,_tI,_tJ,_u1.a,_u1.b,_u1.c,_uc,_ud,_u9,_ua,_ub,_u4,_u5,_u6)),_uf=__lst2arr(B(_oY(_p7,_ue.a))),_ug=__lst2arr(B(_oY(_oS,_ue.b)));return {_:0,a:_tH,b:_tI,c:_tJ,d:new T2(0,E(_u1),E(_uc)),e:_ud,f:new T3(0,E(_u9),E(_ua),E(_ub)),g:_u3,h:_uf,i:_ug,j:E(_ue.c)};},_uh=-0.6,_ui=new T3(0,E(_mh),E(_uh),E(_mh)),_uj=function(_uk){return E(_ui);},_ul=function(_){return new F(function(){return __jsNull();});},_um=function(_un){var _uo=B(A1(_un,_));return E(_uo);},_up=new T(function(){return B(_um(_ul));}),_uq=function(_ur,_us,_ut,_uu,_uv,_uw,_ux,_uy,_uz,_uA,_uB,_uC,_uD){var _uE=function(_uF){var _uG=E(_rx),_uH=2+_uF|0,_uI=_uH-1|0,_uJ=(2+_uF)*(1+_uF),_uK=E(_rZ);if(!_uK._){return _uG*0;}else{var _uL=_uK.a,_uM=_uK.b,_uN=B(A1(_ur,new T(function(){return 6.283185307179586*E(_uL)/E(_qV);}))),_uO=B(A1(_ur,new T(function(){return 6.283185307179586*(E(_uL)+1)/E(_qV);})));if(_uN!=_uO){if(_uH>=0){var _uP=E(_uH);if(!_uP){var _uQ=function(_uR,_uS){while(1){var _uT=B((function(_uU,_uV){var _uW=E(_uU);if(!_uW._){return E(_uV);}else{var _uX=_uW.a,_uY=_uW.b,_uZ=B(A1(_ur,new T(function(){return 6.283185307179586*E(_uX)/E(_qV);}))),_v0=B(A1(_ur,new T(function(){return 6.283185307179586*(E(_uX)+1)/E(_qV);})));if(_uZ!=_v0){var _v1=_uV+0/(_uZ-_v0)/_uJ;_uR=_uY;_uS=_v1;return __continue;}else{if(_uI>=0){var _v2=E(_uI);if(!_v2){var _v1=_uV+_uH/_uJ;_uR=_uY;_uS=_v1;return __continue;}else{var _v1=_uV+_uH*B(_mt(_uZ,_v2))/_uJ;_uR=_uY;_uS=_v1;return __continue;}}else{return E(_mk);}}}})(_uR,_uS));if(_uT!=__continue){return _uT;}}};return _uG*B(_uQ(_uM,0/(_uN-_uO)/_uJ));}else{var _v3=function(_v4,_v5){while(1){var _v6=B((function(_v7,_v8){var _v9=E(_v7);if(!_v9._){return E(_v8);}else{var _va=_v9.a,_vb=_v9.b,_vc=B(A1(_ur,new T(function(){return 6.283185307179586*E(_va)/E(_qV);}))),_vd=B(A1(_ur,new T(function(){return 6.283185307179586*(E(_va)+1)/E(_qV);})));if(_vc!=_vd){if(_uP>=0){var _ve=_v8+(B(_mt(_vc,_uP))-B(_mt(_vd,_uP)))/(_vc-_vd)/_uJ;_v4=_vb;_v5=_ve;return __continue;}else{return E(_mk);}}else{if(_uI>=0){var _vf=E(_uI);if(!_vf){var _ve=_v8+_uH/_uJ;_v4=_vb;_v5=_ve;return __continue;}else{var _ve=_v8+_uH*B(_mt(_vc,_vf))/_uJ;_v4=_vb;_v5=_ve;return __continue;}}else{return E(_mk);}}}})(_v4,_v5));if(_v6!=__continue){return _v6;}}};return _uG*B(_v3(_uM,(B(_mt(_uN,_uP))-B(_mt(_uO,_uP)))/(_uN-_uO)/_uJ));}}else{return E(_mk);}}else{if(_uI>=0){var _vg=E(_uI);if(!_vg){var _vh=function(_vi,_vj){while(1){var _vk=B((function(_vl,_vm){var _vn=E(_vl);if(!_vn._){return E(_vm);}else{var _vo=_vn.a,_vp=_vn.b,_vq=B(A1(_ur,new T(function(){return 6.283185307179586*E(_vo)/E(_qV);}))),_vr=B(A1(_ur,new T(function(){return 6.283185307179586*(E(_vo)+1)/E(_qV);})));if(_vq!=_vr){if(_uH>=0){var _vs=E(_uH);if(!_vs){var _vt=_vm+0/(_vq-_vr)/_uJ;_vi=_vp;_vj=_vt;return __continue;}else{var _vt=_vm+(B(_mt(_vq,_vs))-B(_mt(_vr,_vs)))/(_vq-_vr)/_uJ;_vi=_vp;_vj=_vt;return __continue;}}else{return E(_mk);}}else{var _vt=_vm+_uH/_uJ;_vi=_vp;_vj=_vt;return __continue;}}})(_vi,_vj));if(_vk!=__continue){return _vk;}}};return _uG*B(_vh(_uM,_uH/_uJ));}else{var _vu=function(_vv,_vw){while(1){var _vx=B((function(_vy,_vz){var _vA=E(_vy);if(!_vA._){return E(_vz);}else{var _vB=_vA.a,_vC=_vA.b,_vD=B(A1(_ur,new T(function(){return 6.283185307179586*E(_vB)/E(_qV);}))),_vE=B(A1(_ur,new T(function(){return 6.283185307179586*(E(_vB)+1)/E(_qV);})));if(_vD!=_vE){if(_uH>=0){var _vF=E(_uH);if(!_vF){var _vG=_vz+0/(_vD-_vE)/_uJ;_vv=_vC;_vw=_vG;return __continue;}else{var _vG=_vz+(B(_mt(_vD,_vF))-B(_mt(_vE,_vF)))/(_vD-_vE)/_uJ;_vv=_vC;_vw=_vG;return __continue;}}else{return E(_mk);}}else{if(_vg>=0){var _vG=_vz+_uH*B(_mt(_vD,_vg))/_uJ;_vv=_vC;_vw=_vG;return __continue;}else{return E(_mk);}}}})(_vv,_vw));if(_vx!=__continue){return _vx;}}};return _uG*B(_vu(_uM,_uH*B(_mt(_uN,_vg))/_uJ));}}else{return E(_mk);}}}},_vH=E(_up),_vI=1/(B(_uE(1))*_us);return new F(function(){return _tG(_ur,_uj,new T2(0,E(new T3(0,E(_vI),E(_vI),E(_vI))),1/(B(_uE(3))*_us)),_ut,_uu,_uv,_uw,_ux,_uy,_uz,_uA,_uB,_uC,_uD,_mi,_vH,_vH,0);});},_vJ=1,_vK=function(_vL){var _vM=I_decodeDouble(_vL);return new T2(0,new T1(1,_vM.b),_vM.a);},_vN=function(_vO){return new T1(0,_vO);},_vP=function(_vQ){var _vR=hs_intToInt64(2147483647),_vS=hs_leInt64(_vQ,_vR);if(!_vS){return new T1(1,I_fromInt64(_vQ));}else{var _vT=hs_intToInt64(-2147483648),_vU=hs_geInt64(_vQ,_vT);if(!_vU){return new T1(1,I_fromInt64(_vQ));}else{var _vV=hs_int64ToInt(_vQ);return new F(function(){return _vN(_vV);});}}},_vW=new T(function(){var _vX=newByteArr(256),_vY=_vX,_=_vY["v"]["i8"][0]=8,_vZ=function(_w0,_w1,_w2,_){while(1){if(_w2>=256){if(_w0>=256){return E(_);}else{var _w3=imul(2,_w0)|0,_w4=_w1+1|0,_w5=_w0;_w0=_w3;_w1=_w4;_w2=_w5;continue;}}else{var _=_vY["v"]["i8"][_w2]=_w1,_w5=_w2+_w0|0;_w2=_w5;continue;}}},_=B(_vZ(2,0,1,_));return _vY;}),_w6=function(_w7,_w8){var _w9=hs_int64ToInt(_w7),_wa=E(_vW),_wb=_wa["v"]["i8"][(255&_w9>>>0)>>>0&4294967295];if(_w8>_wb){if(_wb>=8){var _wc=hs_uncheckedIShiftRA64(_w7,8),_wd=function(_we,_wf){while(1){var _wg=B((function(_wh,_wi){var _wj=hs_int64ToInt(_wh),_wk=_wa["v"]["i8"][(255&_wj>>>0)>>>0&4294967295];if(_wi>_wk){if(_wk>=8){var _wl=hs_uncheckedIShiftRA64(_wh,8),_wm=_wi-8|0;_we=_wl;_wf=_wm;return __continue;}else{return new T2(0,new T(function(){var _wn=hs_uncheckedIShiftRA64(_wh,_wk);return B(_vP(_wn));}),_wi-_wk|0);}}else{return new T2(0,new T(function(){var _wo=hs_uncheckedIShiftRA64(_wh,_wi);return B(_vP(_wo));}),0);}})(_we,_wf));if(_wg!=__continue){return _wg;}}};return new F(function(){return _wd(_wc,_w8-8|0);});}else{return new T2(0,new T(function(){var _wp=hs_uncheckedIShiftRA64(_w7,_wb);return B(_vP(_wp));}),_w8-_wb|0);}}else{return new T2(0,new T(function(){var _wq=hs_uncheckedIShiftRA64(_w7,_w8);return B(_vP(_wq));}),0);}},_wr=function(_ws){var _wt=hs_intToInt64(_ws);return E(_wt);},_wu=function(_wv){var _ww=E(_wv);if(!_ww._){return new F(function(){return _wr(_ww.a);});}else{return new F(function(){return I_toInt64(_ww.a);});}},_wx=function(_wy){return I_toInt(_wy)>>>0;},_wz=function(_wA){var _wB=E(_wA);if(!_wB._){return _wB.a>>>0;}else{return new F(function(){return _wx(_wB.a);});}},_wC=function(_wD){var _wE=B(_vK(_wD)),_wF=_wE.a,_wG=_wE.b;if(_wG<0){var _wH=function(_wI){if(!_wI){return new T2(0,E(_wF),B(_3J(_21, -_wG)));}else{var _wJ=B(_w6(B(_wu(_wF)), -_wG));return new T2(0,E(_wJ.a),B(_3J(_21,_wJ.b)));}};if(!((B(_wz(_wF))&1)>>>0)){return new F(function(){return _wH(1);});}else{return new F(function(){return _wH(0);});}}else{return new T2(0,B(_3J(_wF,_wG)),_21);}},_wK=function(_wL){var _wM=B(_wC(E(_wL)));return new T2(0,E(_wM.a),E(_wM.b));},_wN=new T3(0,_ng,_ol,_wK),_wO=function(_wP){return E(E(_wP).a);},_wQ=function(_wR){return E(E(_wR).a);},_wS=function(_wT,_wU){if(_wT<=_wU){var _wV=function(_wW){return new T2(1,_wW,new T(function(){if(_wW!=_wU){return B(_wV(_wW+1|0));}else{return __Z;}}));};return new F(function(){return _wV(_wT);});}else{return __Z;}},_wX=function(_wY){return new F(function(){return _wS(E(_wY),2147483647);});},_wZ=function(_x0,_x1,_x2){if(_x2<=_x1){var _x3=new T(function(){var _x4=_x1-_x0|0,_x5=function(_x6){return (_x6>=(_x2-_x4|0))?new T2(1,_x6,new T(function(){return B(_x5(_x6+_x4|0));})):new T2(1,_x6,_w);};return B(_x5(_x1));});return new T2(1,_x0,_x3);}else{return (_x2<=_x0)?new T2(1,_x0,_w):__Z;}},_x7=function(_x8,_x9,_xa){if(_xa>=_x9){var _xb=new T(function(){var _xc=_x9-_x8|0,_xd=function(_xe){return (_xe<=(_xa-_xc|0))?new T2(1,_xe,new T(function(){return B(_xd(_xe+_xc|0));})):new T2(1,_xe,_w);};return B(_xd(_x9));});return new T2(1,_x8,_xb);}else{return (_xa>=_x8)?new T2(1,_x8,_w):__Z;}},_xf=function(_xg,_xh){if(_xh<_xg){return new F(function(){return _wZ(_xg,_xh,-2147483648);});}else{return new F(function(){return _x7(_xg,_xh,2147483647);});}},_xi=function(_xj,_xk){return new F(function(){return _xf(E(_xj),E(_xk));});},_xl=function(_xm,_xn,_xo){if(_xn<_xm){return new F(function(){return _wZ(_xm,_xn,_xo);});}else{return new F(function(){return _x7(_xm,_xn,_xo);});}},_xp=function(_xq,_xr,_xs){return new F(function(){return _xl(E(_xq),E(_xr),E(_xs));});},_xt=function(_xu,_xv){return new F(function(){return _wS(E(_xu),E(_xv));});},_xw=function(_xx){return E(_xx);},_xy=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_xz=new T(function(){return B(err(_xy));}),_xA=function(_xB){var _xC=E(_xB);return (_xC==(-2147483648))?E(_xz):_xC-1|0;},_xD=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_xE=new T(function(){return B(err(_xD));}),_xF=function(_xG){var _xH=E(_xG);return (_xH==2147483647)?E(_xE):_xH+1|0;},_xI={_:0,a:_xF,b:_xA,c:_xw,d:_xw,e:_wX,f:_xi,g:_xt,h:_xp},_xJ=function(_xK,_xL){if(_xK<=0){if(_xK>=0){return new F(function(){return quot(_xK,_xL);});}else{if(_xL<=0){return new F(function(){return quot(_xK,_xL);});}else{return quot(_xK+1|0,_xL)-1|0;}}}else{if(_xL>=0){if(_xK>=0){return new F(function(){return quot(_xK,_xL);});}else{if(_xL<=0){return new F(function(){return quot(_xK,_xL);});}else{return quot(_xK+1|0,_xL)-1|0;}}}else{return quot(_xK-1|0,_xL)-1|0;}}},_xM=0,_xN=new T(function(){return B(_36(_xM));}),_xO=new T(function(){return die(_xN);}),_xP=function(_xQ,_xR){var _xS=E(_xR);switch(_xS){case -1:var _xT=E(_xQ);if(_xT==(-2147483648)){return E(_xO);}else{return new F(function(){return _xJ(_xT,-1);});}break;case 0:return E(_3a);default:return new F(function(){return _xJ(_xQ,_xS);});}},_xU=function(_xV,_xW){return new F(function(){return _xP(E(_xV),E(_xW));});},_xX=0,_xY=new T2(0,_xO,_xX),_xZ=function(_y0,_y1){var _y2=E(_y0),_y3=E(_y1);switch(_y3){case -1:var _y4=E(_y2);if(_y4==(-2147483648)){return E(_xY);}else{if(_y4<=0){if(_y4>=0){var _y5=quotRemI(_y4,-1);return new T2(0,_y5.a,_y5.b);}else{var _y6=quotRemI(_y4,-1);return new T2(0,_y6.a,_y6.b);}}else{var _y7=quotRemI(_y4-1|0,-1);return new T2(0,_y7.a-1|0,(_y7.b+(-1)|0)+1|0);}}break;case 0:return E(_3a);default:if(_y2<=0){if(_y2>=0){var _y8=quotRemI(_y2,_y3);return new T2(0,_y8.a,_y8.b);}else{if(_y3<=0){var _y9=quotRemI(_y2,_y3);return new T2(0,_y9.a,_y9.b);}else{var _ya=quotRemI(_y2+1|0,_y3);return new T2(0,_ya.a-1|0,(_ya.b+_y3|0)-1|0);}}}else{if(_y3>=0){if(_y2>=0){var _yb=quotRemI(_y2,_y3);return new T2(0,_yb.a,_yb.b);}else{if(_y3<=0){var _yc=quotRemI(_y2,_y3);return new T2(0,_yc.a,_yc.b);}else{var _yd=quotRemI(_y2+1|0,_y3);return new T2(0,_yd.a-1|0,(_yd.b+_y3|0)-1|0);}}}else{var _ye=quotRemI(_y2-1|0,_y3);return new T2(0,_ye.a-1|0,(_ye.b+_y3|0)+1|0);}}}},_yf=function(_yg,_yh){var _yi=_yg%_yh;if(_yg<=0){if(_yg>=0){return E(_yi);}else{if(_yh<=0){return E(_yi);}else{var _yj=E(_yi);return (_yj==0)?0:_yj+_yh|0;}}}else{if(_yh>=0){if(_yg>=0){return E(_yi);}else{if(_yh<=0){return E(_yi);}else{var _yk=E(_yi);return (_yk==0)?0:_yk+_yh|0;}}}else{var _yl=E(_yi);return (_yl==0)?0:_yl+_yh|0;}}},_ym=function(_yn,_yo){var _yp=E(_yo);switch(_yp){case -1:return E(_xX);case 0:return E(_3a);default:return new F(function(){return _yf(E(_yn),_yp);});}},_yq=function(_yr,_ys){var _yt=E(_yr),_yu=E(_ys);switch(_yu){case -1:var _yv=E(_yt);if(_yv==(-2147483648)){return E(_xO);}else{return new F(function(){return quot(_yv,-1);});}break;case 0:return E(_3a);default:return new F(function(){return quot(_yt,_yu);});}},_yw=function(_yx,_yy){var _yz=E(_yx),_yA=E(_yy);switch(_yA){case -1:var _yB=E(_yz);if(_yB==(-2147483648)){return E(_xY);}else{var _yC=quotRemI(_yB,-1);return new T2(0,_yC.a,_yC.b);}break;case 0:return E(_3a);default:var _yD=quotRemI(_yz,_yA);return new T2(0,_yD.a,_yD.b);}},_yE=function(_yF,_yG){var _yH=E(_yG);switch(_yH){case -1:return E(_xX);case 0:return E(_3a);default:return E(_yF)%_yH;}},_yI=function(_yJ){return new F(function(){return _vN(E(_yJ));});},_yK=function(_yL){return new T2(0,E(B(_vN(E(_yL)))),E(_rz));},_yM=function(_yN,_yO){return imul(E(_yN),E(_yO))|0;},_yP=function(_yQ,_yR){return E(_yQ)+E(_yR)|0;},_yS=function(_yT,_yU){return E(_yT)-E(_yU)|0;},_yV=function(_yW){var _yX=E(_yW);return (_yX<0)? -_yX:E(_yX);},_yY=function(_yZ){return new F(function(){return _3n(_yZ);});},_z0=function(_z1){return  -E(_z1);},_z2=-1,_z3=0,_z4=1,_z5=function(_z6){var _z7=E(_z6);return (_z7>=0)?(E(_z7)==0)?E(_z3):E(_z4):E(_z2);},_z8={_:0,a:_yP,b:_yS,c:_yM,d:_z0,e:_yV,f:_z5,g:_yY},_z9=function(_za,_zb){return E(_za)==E(_zb);},_zc=function(_zd,_ze){return E(_zd)!=E(_ze);},_zf=new T2(0,_z9,_zc),_zg=function(_zh,_zi){var _zj=E(_zh),_zk=E(_zi);return (_zj>_zk)?E(_zj):E(_zk);},_zl=function(_zm,_zn){var _zo=E(_zm),_zp=E(_zn);return (_zo>_zp)?E(_zp):E(_zo);},_zq=function(_zr,_zs){return (_zr>=_zs)?(_zr!=_zs)?2:1:0;},_zt=function(_zu,_zv){return new F(function(){return _zq(E(_zu),E(_zv));});},_zw=function(_zx,_zy){return E(_zx)>=E(_zy);},_zz=function(_zA,_zB){return E(_zA)>E(_zB);},_zC=function(_zD,_zE){return E(_zD)<=E(_zE);},_zF=function(_zG,_zH){return E(_zG)<E(_zH);},_zI={_:0,a:_zf,b:_zt,c:_zF,d:_zC,e:_zz,f:_zw,g:_zg,h:_zl},_zJ=new T3(0,_z8,_zI,_yK),_zK={_:0,a:_zJ,b:_xI,c:_yq,d:_yE,e:_xU,f:_ym,g:_yw,h:_xZ,i:_yI},_zL=new T1(0,2),_zM=function(_zN,_zO){while(1){var _zP=E(_zN);if(!_zP._){var _zQ=_zP.a,_zR=E(_zO);if(!_zR._){var _zS=_zR.a;if(!(imul(_zQ,_zS)|0)){return new T1(0,imul(_zQ,_zS)|0);}else{_zN=new T1(1,I_fromInt(_zQ));_zO=new T1(1,I_fromInt(_zS));continue;}}else{_zN=new T1(1,I_fromInt(_zQ));_zO=_zR;continue;}}else{var _zT=E(_zO);if(!_zT._){_zN=_zP;_zO=new T1(1,I_fromInt(_zT.a));continue;}else{return new T1(1,I_mul(_zP.a,_zT.a));}}}},_zU=function(_zV,_zW,_zX){while(1){if(!(_zW%2)){var _zY=B(_zM(_zV,_zV)),_zZ=quot(_zW,2);_zV=_zY;_zW=_zZ;continue;}else{var _A0=E(_zW);if(_A0==1){return new F(function(){return _zM(_zV,_zX);});}else{var _zY=B(_zM(_zV,_zV)),_A1=B(_zM(_zV,_zX));_zV=_zY;_zW=quot(_A0-1|0,2);_zX=_A1;continue;}}}},_A2=function(_A3,_A4){while(1){if(!(_A4%2)){var _A5=B(_zM(_A3,_A3)),_A6=quot(_A4,2);_A3=_A5;_A4=_A6;continue;}else{var _A7=E(_A4);if(_A7==1){return E(_A3);}else{return new F(function(){return _zU(B(_zM(_A3,_A3)),quot(_A7-1|0,2),_A3);});}}}},_A8=function(_A9){return E(E(_A9).b);},_Aa=function(_Ab){return E(E(_Ab).c);},_Ac=new T1(0,0),_Ad=function(_Ae){return E(E(_Ae).d);},_Af=function(_Ag,_Ah){var _Ai=B(_wO(_Ag)),_Aj=new T(function(){return B(_wQ(_Ai));}),_Ak=new T(function(){return B(A3(_Ad,_Ag,_Ah,new T(function(){return B(A2(_8s,_Aj,_rJ));})));});return new F(function(){return A3(_qn,B(_q9(B(_A8(_Ai)))),_Ak,new T(function(){return B(A2(_8s,_Aj,_Ac));}));});},_Al=new T(function(){return B(unCStr("Negative exponent"));}),_Am=new T(function(){return B(err(_Al));}),_An=function(_Ao){return E(E(_Ao).c);},_Ap=function(_Aq,_Ar,_As,_At){var _Au=B(_wO(_Ar)),_Av=new T(function(){return B(_wQ(_Au));}),_Aw=B(_A8(_Au));if(!B(A3(_Aa,_Aw,_At,new T(function(){return B(A2(_8s,_Av,_Ac));})))){if(!B(A3(_qn,B(_q9(_Aw)),_At,new T(function(){return B(A2(_8s,_Av,_Ac));})))){var _Ax=new T(function(){return B(A2(_8s,_Av,_rJ));}),_Ay=new T(function(){return B(A2(_8s,_Av,_rz));}),_Az=B(_q9(_Aw)),_AA=function(_AB,_AC,_AD){while(1){var _AE=B((function(_AF,_AG,_AH){if(!B(_Af(_Ar,_AG))){if(!B(A3(_qn,_Az,_AG,_Ay))){var _AI=new T(function(){return B(A3(_An,_Ar,new T(function(){return B(A3(_9p,_Av,_AG,_Ay));}),_Ax));});_AB=new T(function(){return B(A3(_8L,_Aq,_AF,_AF));});_AC=_AI;_AD=new T(function(){return B(A3(_8L,_Aq,_AF,_AH));});return __continue;}else{return new F(function(){return A3(_8L,_Aq,_AF,_AH);});}}else{var _AJ=_AH;_AB=new T(function(){return B(A3(_8L,_Aq,_AF,_AF));});_AC=new T(function(){return B(A3(_An,_Ar,_AG,_Ax));});_AD=_AJ;return __continue;}})(_AB,_AC,_AD));if(_AE!=__continue){return _AE;}}},_AK=function(_AL,_AM){while(1){var _AN=B((function(_AO,_AP){if(!B(_Af(_Ar,_AP))){if(!B(A3(_qn,_Az,_AP,_Ay))){var _AQ=new T(function(){return B(A3(_An,_Ar,new T(function(){return B(A3(_9p,_Av,_AP,_Ay));}),_Ax));});return new F(function(){return _AA(new T(function(){return B(A3(_8L,_Aq,_AO,_AO));}),_AQ,_AO);});}else{return E(_AO);}}else{_AL=new T(function(){return B(A3(_8L,_Aq,_AO,_AO));});_AM=new T(function(){return B(A3(_An,_Ar,_AP,_Ax));});return __continue;}})(_AL,_AM));if(_AN!=__continue){return _AN;}}};return new F(function(){return _AK(_As,_At);});}else{return new F(function(){return A2(_8s,_Aq,_rz);});}}else{return E(_Am);}},_AR=new T(function(){return B(err(_Al));}),_AS=function(_AT,_AU){var _AV=B(_vK(_AU)),_AW=_AV.a,_AX=_AV.b,_AY=new T(function(){return B(_wQ(new T(function(){return B(_wO(_AT));})));});if(_AX<0){var _AZ= -_AX;if(_AZ>=0){var _B0=E(_AZ);if(!_B0){var _B1=E(_rz);}else{var _B1=B(_A2(_zL,_B0));}if(!B(_3f(_B1,_3I))){var _B2=B(_3z(_AW,_B1));return new T2(0,new T(function(){return B(A2(_8s,_AY,_B2.a));}),new T(function(){return B(_3b(_B2.b,_AX));}));}else{return E(_3a);}}else{return E(_AR);}}else{var _B3=new T(function(){var _B4=new T(function(){return B(_Ap(_AY,_zK,new T(function(){return B(A2(_8s,_AY,_zL));}),_AX));});return B(A3(_8L,_AY,new T(function(){return B(A2(_8s,_AY,_AW));}),_B4));});return new T2(0,_B3,_6x);}},_B5=function(_B6,_B7){var _B8=B(_AS(_B6,E(_B7))),_B9=_B8.a;if(E(_B8.b)<=0){return E(_B9);}else{var _Ba=B(_wQ(B(_wO(_B6))));return new F(function(){return A3(_6X,_Ba,_B9,new T(function(){return B(A2(_8s,_Ba,_21));}));});}},_Bb=function(_Bc,_Bd){var _Be=B(_AS(_Bc,E(_Bd))),_Bf=_Be.a;if(E(_Be.b)>=0){return E(_Bf);}else{var _Bg=B(_wQ(B(_wO(_Bc))));return new F(function(){return A3(_9p,_Bg,_Bf,new T(function(){return B(A2(_8s,_Bg,_21));}));});}},_Bh=function(_Bi,_Bj){var _Bk=B(_AS(_Bi,E(_Bj)));return new T2(0,_Bk.a,_Bk.b);},_Bl=function(_Bm,_Bn){var _Bo=B(_AS(_Bm,_Bn)),_Bp=_Bo.a,_Bq=E(_Bo.b),_Br=new T(function(){var _Bs=B(_wQ(B(_wO(_Bm))));if(_Bq>=0){return B(A3(_6X,_Bs,_Bp,new T(function(){return B(A2(_8s,_Bs,_21));})));}else{return B(A3(_9p,_Bs,_Bp,new T(function(){return B(A2(_8s,_Bs,_21));})));}}),_Bt=function(_Bu){var _Bv=_Bu-0.5;return (_Bv>=0)?(E(_Bv)==0)?(!B(_Af(_Bm,_Bp)))?E(_Br):E(_Bp):E(_Br):E(_Bp);},_Bw=E(_Bq);if(!_Bw){return new F(function(){return _Bt(0);});}else{if(_Bw<=0){var _Bx= -_Bw-0.5;return (_Bx>=0)?(E(_Bx)==0)?(!B(_Af(_Bm,_Bp)))?E(_Br):E(_Bp):E(_Br):E(_Bp);}else{return new F(function(){return _Bt(_Bw);});}}},_By=function(_Bz,_BA){return new F(function(){return _Bl(_Bz,E(_BA));});},_BB=function(_BC,_BD){return E(B(_AS(_BC,E(_BD))).a);},_BE={_:0,a:_wN,b:_nk,c:_Bh,d:_BB,e:_By,f:_B5,g:_Bb},_BF=new T1(0,1),_BG=function(_BH,_BI){var _BJ=E(_BH);return new T2(0,_BJ,new T(function(){var _BK=B(_BG(B(_3q(_BJ,_BI)),_BI));return new T2(1,_BK.a,_BK.b);}));},_BL=function(_BM){var _BN=B(_BG(_BM,_BF));return new T2(1,_BN.a,_BN.b);},_BO=function(_BP,_BQ){var _BR=B(_BG(_BP,new T(function(){return B(_5L(_BQ,_BP));})));return new T2(1,_BR.a,_BR.b);},_BS=new T1(0,0),_BT=function(_BU,_BV){var _BW=E(_BU);if(!_BW._){var _BX=_BW.a,_BY=E(_BV);return (_BY._==0)?_BX>=_BY.a:I_compareInt(_BY.a,_BX)<=0;}else{var _BZ=_BW.a,_C0=E(_BV);return (_C0._==0)?I_compareInt(_BZ,_C0.a)>=0:I_compare(_BZ,_C0.a)>=0;}},_C1=function(_C2,_C3,_C4){if(!B(_BT(_C3,_BS))){var _C5=function(_C6){return (!B(_42(_C6,_C4)))?new T2(1,_C6,new T(function(){return B(_C5(B(_3q(_C6,_C3))));})):__Z;};return new F(function(){return _C5(_C2);});}else{var _C7=function(_C8){return (!B(_3T(_C8,_C4)))?new T2(1,_C8,new T(function(){return B(_C7(B(_3q(_C8,_C3))));})):__Z;};return new F(function(){return _C7(_C2);});}},_C9=function(_Ca,_Cb,_Cc){return new F(function(){return _C1(_Ca,B(_5L(_Cb,_Ca)),_Cc);});},_Cd=function(_Ce,_Cf){return new F(function(){return _C1(_Ce,_BF,_Cf);});},_Cg=function(_Ch){return new F(function(){return _3n(_Ch);});},_Ci=function(_Cj){return new F(function(){return _5L(_Cj,_BF);});},_Ck=function(_Cl){return new F(function(){return _3q(_Cl,_BF);});},_Cm=function(_Cn){return new F(function(){return _vN(E(_Cn));});},_Co={_:0,a:_Ck,b:_Ci,c:_Cm,d:_Cg,e:_BL,f:_BO,g:_Cd,h:_C9},_Cp=function(_Cq,_Cr){while(1){var _Cs=E(_Cq);if(!_Cs._){var _Ct=E(_Cs.a);if(_Ct==(-2147483648)){_Cq=new T1(1,I_fromInt(-2147483648));continue;}else{var _Cu=E(_Cr);if(!_Cu._){return new T1(0,B(_xJ(_Ct,_Cu.a)));}else{_Cq=new T1(1,I_fromInt(_Ct));_Cr=_Cu;continue;}}}else{var _Cv=_Cs.a,_Cw=E(_Cr);return (_Cw._==0)?new T1(1,I_div(_Cv,I_fromInt(_Cw.a))):new T1(1,I_div(_Cv,_Cw.a));}}},_Cx=function(_Cy,_Cz){if(!B(_3f(_Cz,_Ac))){return new F(function(){return _Cp(_Cy,_Cz);});}else{return E(_3a);}},_CA=function(_CB,_CC){while(1){var _CD=E(_CB);if(!_CD._){var _CE=E(_CD.a);if(_CE==(-2147483648)){_CB=new T1(1,I_fromInt(-2147483648));continue;}else{var _CF=E(_CC);if(!_CF._){var _CG=_CF.a;return new T2(0,new T1(0,B(_xJ(_CE,_CG))),new T1(0,B(_yf(_CE,_CG))));}else{_CB=new T1(1,I_fromInt(_CE));_CC=_CF;continue;}}}else{var _CH=E(_CC);if(!_CH._){_CB=_CD;_CC=new T1(1,I_fromInt(_CH.a));continue;}else{var _CI=I_divMod(_CD.a,_CH.a);return new T2(0,new T1(1,_CI.a),new T1(1,_CI.b));}}}},_CJ=function(_CK,_CL){if(!B(_3f(_CL,_Ac))){var _CM=B(_CA(_CK,_CL));return new T2(0,_CM.a,_CM.b);}else{return E(_3a);}},_CN=function(_CO,_CP){while(1){var _CQ=E(_CO);if(!_CQ._){var _CR=E(_CQ.a);if(_CR==(-2147483648)){_CO=new T1(1,I_fromInt(-2147483648));continue;}else{var _CS=E(_CP);if(!_CS._){return new T1(0,B(_yf(_CR,_CS.a)));}else{_CO=new T1(1,I_fromInt(_CR));_CP=_CS;continue;}}}else{var _CT=_CQ.a,_CU=E(_CP);return (_CU._==0)?new T1(1,I_mod(_CT,I_fromInt(_CU.a))):new T1(1,I_mod(_CT,_CU.a));}}},_CV=function(_CW,_CX){if(!B(_3f(_CX,_Ac))){return new F(function(){return _CN(_CW,_CX);});}else{return E(_3a);}},_CY=function(_CZ,_D0){while(1){var _D1=E(_CZ);if(!_D1._){var _D2=E(_D1.a);if(_D2==(-2147483648)){_CZ=new T1(1,I_fromInt(-2147483648));continue;}else{var _D3=E(_D0);if(!_D3._){return new T1(0,quot(_D2,_D3.a));}else{_CZ=new T1(1,I_fromInt(_D2));_D0=_D3;continue;}}}else{var _D4=_D1.a,_D5=E(_D0);return (_D5._==0)?new T1(0,I_toInt(I_quot(_D4,I_fromInt(_D5.a)))):new T1(1,I_quot(_D4,_D5.a));}}},_D6=function(_D7,_D8){if(!B(_3f(_D8,_Ac))){return new F(function(){return _CY(_D7,_D8);});}else{return E(_3a);}},_D9=function(_Da,_Db){if(!B(_3f(_Db,_Ac))){var _Dc=B(_3z(_Da,_Db));return new T2(0,_Dc.a,_Dc.b);}else{return E(_3a);}},_Dd=function(_De,_Df){while(1){var _Dg=E(_De);if(!_Dg._){var _Dh=E(_Dg.a);if(_Dh==(-2147483648)){_De=new T1(1,I_fromInt(-2147483648));continue;}else{var _Di=E(_Df);if(!_Di._){return new T1(0,_Dh%_Di.a);}else{_De=new T1(1,I_fromInt(_Dh));_Df=_Di;continue;}}}else{var _Dj=_Dg.a,_Dk=E(_Df);return (_Dk._==0)?new T1(1,I_rem(_Dj,I_fromInt(_Dk.a))):new T1(1,I_rem(_Dj,_Dk.a));}}},_Dl=function(_Dm,_Dn){if(!B(_3f(_Dn,_Ac))){return new F(function(){return _Dd(_Dm,_Dn);});}else{return E(_3a);}},_Do=function(_Dp){return E(_Dp);},_Dq=function(_Dr){return E(_Dr);},_Ds=function(_Dt){var _Du=E(_Dt);if(!_Du._){var _Dv=E(_Du.a);return (_Dv==(-2147483648))?E(_6p):(_Dv<0)?new T1(0, -_Dv):E(_Du);}else{var _Dw=_Du.a;return (I_compareInt(_Dw,0)>=0)?E(_Du):new T1(1,I_negate(_Dw));}},_Dx=new T1(0,0),_Dy=new T1(0,-1),_Dz=function(_DA){var _DB=E(_DA);if(!_DB._){var _DC=_DB.a;return (_DC>=0)?(E(_DC)==0)?E(_Dx):E(_41):E(_Dy);}else{var _DD=I_compareInt(_DB.a,0);return (_DD<=0)?(E(_DD)==0)?E(_Dx):E(_Dy):E(_41);}},_DE={_:0,a:_3q,b:_5L,c:_zM,d:_6q,e:_Ds,f:_Dz,g:_Dq},_DF=function(_DG,_DH){var _DI=E(_DG);if(!_DI._){var _DJ=_DI.a,_DK=E(_DH);return (_DK._==0)?_DJ!=_DK.a:(I_compareInt(_DK.a,_DJ)==0)?false:true;}else{var _DL=_DI.a,_DM=E(_DH);return (_DM._==0)?(I_compareInt(_DL,_DM.a)==0)?false:true:(I_compare(_DL,_DM.a)==0)?false:true;}},_DN=new T2(0,_3f,_DF),_DO=function(_DP,_DQ){return (!B(_5w(_DP,_DQ)))?E(_DP):E(_DQ);},_DR=function(_DS,_DT){return (!B(_5w(_DS,_DT)))?E(_DT):E(_DS);},_DU={_:0,a:_DN,b:_22,c:_42,d:_5w,e:_3T,f:_BT,g:_DO,h:_DR},_DV=function(_DW){return new T2(0,E(_DW),E(_rz));},_DX=new T3(0,_DE,_DU,_DV),_DY={_:0,a:_DX,b:_Co,c:_D6,d:_Dl,e:_Cx,f:_CV,g:_D9,h:_CJ,i:_Do},_DZ=function(_E0){return E(E(_E0).b);},_E1=function(_E2){return E(E(_E2).g);},_E3=new T1(0,1),_E4=function(_E5,_E6,_E7){var _E8=B(_DZ(_E5)),_E9=B(_8J(_E8)),_Ea=new T(function(){var _Eb=new T(function(){var _Ec=new T(function(){var _Ed=new T(function(){return B(A3(_E1,_E5,_DY,new T(function(){return B(A3(_8P,_E8,_E6,_E7));})));});return B(A2(_8s,_E9,_Ed));}),_Ee=new T(function(){return B(A2(_6Z,_E9,new T(function(){return B(A2(_8s,_E9,_E3));})));});return B(A3(_8L,_E9,_Ee,_Ec));});return B(A3(_8L,_E9,_Eb,_E7));});return new F(function(){return A3(_6X,_E9,_E6,_Ea);});},_Ef=1.5707963267948966,_Eg=function(_Eh){return 0.2/Math.cos(B(_E4(_BE,_Eh,_Ef))-0.7853981633974483);},_Ei=0,_Ej=new T(function(){var _Ek=B(_uq(_Eg,1.2,_Ei,_Ei,_vJ,_Ei,_Ei,_Ei,_Ei,_Ei,_vJ,_vJ,_vJ));return {_:0,a:E(_Ek.a),b:E(_Ek.b),c:E(_Ek.c),d:E(_Ek.d),e:E(_Ek.e),f:E(_Ek.f),g:E(_Ek.g),h:_Ek.h,i:_Ek.i,j:_Ek.j};}),_El=0,_Em=0.3,_En=function(_Eo){return E(_Em);},_Ep=new T(function(){var _Eq=B(_uq(_En,1.2,_vJ,_Ei,_vJ,_Ei,_Ei,_Ei,_Ei,_Ei,_vJ,_vJ,_vJ));return {_:0,a:E(_Eq.a),b:E(_Eq.b),c:E(_Eq.c),d:E(_Eq.d),e:E(_Eq.e),f:E(_Eq.f),g:E(_Eq.g),h:_Eq.h,i:_Eq.i,j:_Eq.j};}),_Er=new T(function(){var _Es=B(_uq(_En,1.2,_vJ,_vJ,_Ei,_Ei,_Ei,_Ei,_Ei,_Ei,_vJ,_vJ,_vJ));return {_:0,a:E(_Es.a),b:E(_Es.b),c:E(_Es.c),d:E(_Es.d),e:E(_Es.e),f:E(_Es.f),g:E(_Es.g),h:_Es.h,i:_Es.i,j:_Es.j};}),_Et=2,_Eu=function(_Ev){return 0.3/Math.cos(B(_E4(_BE,_Ev,_Ef))-0.7853981633974483);},_Ew=new T(function(){var _Ex=B(_uq(_Eu,1.2,_Et,_vJ,_vJ,_Ei,_Ei,_Ei,_Ei,_Ei,_vJ,_vJ,_vJ));return {_:0,a:E(_Ex.a),b:E(_Ex.b),c:E(_Ex.c),d:E(_Ex.d),e:E(_Ex.e),f:E(_Ex.f),g:E(_Ex.g),h:_Ex.h,i:_Ex.i,j:_Ex.j};}),_Ey=new T2(1,_Ew,_w),_Ez=new T2(1,_Er,_Ey),_EA=new T2(1,_Ep,_Ez),_EB=new T2(1,_Ej,_EA),_EC=new T(function(){return B(unCStr("Negative range size"));}),_ED=new T(function(){return B(err(_EC));}),_EE=function(_){var _EF=B(_ma(_EB,0))-1|0,_EG=function(_EH){if(_EH>=0){var _EI=newArr(_EH,_mg),_EJ=_EI,_EK=E(_EH);if(!_EK){return new T4(0,E(_El),E(_EF),0,_EJ);}else{var _EL=function(_EM,_EN,_){while(1){var _EO=E(_EM);if(!_EO._){return E(_);}else{var _=_EJ[_EN]=_EO.a;if(_EN!=(_EK-1|0)){var _EP=_EN+1|0;_EM=_EO.b;_EN=_EP;continue;}else{return E(_);}}}},_=B((function(_EQ,_ER,_ES,_){var _=_EJ[_ES]=_EQ;if(_ES!=(_EK-1|0)){return new F(function(){return _EL(_ER,_ES+1|0,_);});}else{return E(_);}})(_Ej,_EA,0,_));return new T4(0,E(_El),E(_EF),_EK,_EJ);}}else{return E(_ED);}};if(0>_EF){return new F(function(){return _EG(0);});}else{return new F(function(){return _EG(_EF+1|0);});}},_ET=function(_EU){var _EV=B(A1(_EU,_));return E(_EV);},_EW=new T(function(){return B(_ET(_EE));}),_EX="enclose",_EY="outline",_EZ="polygon",_F0="z",_F1="y",_F2="x",_F3=function(_F4){return new F(function(){return _oy(new T2(1,new T2(0,_F2,new T(function(){return E(E(E(E(_F4).d).a).a);})),new T2(1,new T2(0,_F1,new T(function(){return E(E(E(E(_F4).d).a).b);})),new T2(1,new T2(0,_F0,new T(function(){return E(E(E(E(_F4).d).a).c);})),new T2(1,new T2(0,_EZ,new T(function(){return E(_F4).h;})),new T2(1,new T2(0,_EY,new T(function(){return E(_F4).i;})),new T2(1,new T2(0,_EX,new T(function(){return E(_F4).j;})),_w)))))));});},_F5=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_F6=new T(function(){return B(err(_F5));}),_F7=new T(function(){return eval("__strict(drawObjects)");}),_F8=new T(function(){return eval("__strict(draw)");}),_F9=function(_Fa,_Fb){var _Fc=jsShowI(_Fa);return new F(function(){return _n(fromJSStr(_Fc),_Fb);});},_Fd=function(_Fe,_Ff,_Fg){if(_Ff>=0){return new F(function(){return _F9(_Ff,_Fg);});}else{if(_Fe<=6){return new F(function(){return _F9(_Ff,_Fg);});}else{return new T2(1,_7g,new T(function(){var _Fh=jsShowI(_Ff);return B(_n(fromJSStr(_Fh),new T2(1,_7f,_Fg)));}));}}},_Fi=new T(function(){return B(unCStr(")"));}),_Fj=function(_Fk,_Fl){var _Fm=new T(function(){var _Fn=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Fd(0,_Fk,_w)),_Fi));})));},1);return B(_n(B(_Fd(0,_Fl,_w)),_Fn));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Fm)));});},_Fo=new T2(1,_ox,_w),_Fp=function(_Fq){return E(_Fq);},_Fr=function(_Fs){return E(_Fs);},_Ft=function(_Fu,_Fv){return E(_Fv);},_Fw=function(_Fx,_Fy){return E(_Fx);},_Fz=function(_FA){return E(_FA);},_FB=new T2(0,_Fz,_Fw),_FC=function(_FD,_FE){return E(_FD);},_FF=new T5(0,_FB,_Fr,_Fp,_Ft,_FC),_FG="flipped2",_FH="flipped1",_FI="c1y",_FJ="c1x",_FK="w2z",_FL="w2y",_FM="w2x",_FN="w1z",_FO="w1y",_FP="w1x",_FQ="d2z",_FR="d2y",_FS="d2x",_FT="d1z",_FU="d1y",_FV="d1x",_FW="c2y",_FX="c2x",_FY=function(_FZ,_){var _G0=__get(_FZ,E(_FP)),_G1=__get(_FZ,E(_FO)),_G2=__get(_FZ,E(_FN)),_G3=__get(_FZ,E(_FM)),_G4=__get(_FZ,E(_FL)),_G5=__get(_FZ,E(_FK)),_G6=__get(_FZ,E(_FJ)),_G7=__get(_FZ,E(_FI)),_G8=__get(_FZ,E(_FX)),_G9=__get(_FZ,E(_FW)),_Ga=__get(_FZ,E(_FV)),_Gb=__get(_FZ,E(_FU)),_Gc=__get(_FZ,E(_FT)),_Gd=__get(_FZ,E(_FS)),_Ge=__get(_FZ,E(_FR)),_Gf=__get(_FZ,E(_FQ)),_Gg=__get(_FZ,E(_FH)),_Gh=__get(_FZ,E(_FG));return {_:0,a:E(new T3(0,E(_G0),E(_G1),E(_G2))),b:E(new T3(0,E(_G3),E(_G4),E(_G5))),c:E(new T2(0,E(_G6),E(_G7))),d:E(new T2(0,E(_G8),E(_G9))),e:E(new T3(0,E(_Ga),E(_Gb),E(_Gc))),f:E(new T3(0,E(_Gd),E(_Ge),E(_Gf))),g:E(_Gg),h:E(_Gh)};},_Gi=function(_Gj,_){var _Gk=E(_Gj);if(!_Gk._){return _w;}else{var _Gl=B(_FY(E(_Gk.a),_)),_Gm=B(_Gi(_Gk.b,_));return new T2(1,_Gl,_Gm);}},_Gn=function(_Go){var _Gp=E(_Go);return (E(_Gp.b)-E(_Gp.a)|0)+1|0;},_Gq=function(_Gr,_Gs){var _Gt=E(_Gr),_Gu=E(_Gs);return (E(_Gt.a)>_Gu)?false:_Gu<=E(_Gt.b);},_Gv=function(_Gw){return new F(function(){return _Fd(0,E(_Gw),_w);});},_Gx=function(_Gy,_Gz,_GA){return new F(function(){return _Fd(E(_Gy),E(_Gz),_GA);});},_GB=function(_GC,_GD){return new F(function(){return _Fd(0,E(_GC),_GD);});},_GE=function(_GF,_GG){return new F(function(){return _2Q(_GB,_GF,_GG);});},_GH=new T3(0,_Gx,_Gv,_GE),_GI=0,_GJ=function(_GK,_GL,_GM){return new F(function(){return A1(_GK,new T2(1,_2N,new T(function(){return B(A1(_GL,_GM));})));});},_GN=new T(function(){return B(unCStr("foldr1"));}),_GO=new T(function(){return B(_qY(_GN));}),_GP=function(_GQ,_GR){var _GS=E(_GR);if(!_GS._){return E(_GO);}else{var _GT=_GS.a,_GU=E(_GS.b);if(!_GU._){return E(_GT);}else{return new F(function(){return A2(_GQ,_GT,new T(function(){return B(_GP(_GQ,_GU));}));});}}},_GV=new T(function(){return B(unCStr(" out of range "));}),_GW=new T(function(){return B(unCStr("}.index: Index "));}),_GX=new T(function(){return B(unCStr("Ix{"));}),_GY=new T2(1,_7f,_w),_GZ=new T2(1,_7f,_GY),_H0=0,_H1=function(_H2){return E(E(_H2).a);},_H3=function(_H4,_H5,_H6,_H7,_H8){var _H9=new T(function(){var _Ha=new T(function(){var _Hb=new T(function(){var _Hc=new T(function(){var _Hd=new T(function(){return B(A3(_GP,_GJ,new T2(1,new T(function(){return B(A3(_H1,_H6,_H0,_H7));}),new T2(1,new T(function(){return B(A3(_H1,_H6,_H0,_H8));}),_w)),_GZ));});return B(_n(_GV,new T2(1,_7g,new T2(1,_7g,_Hd))));});return B(A(_H1,[_H6,_GI,_H5,new T2(1,_7f,_Hc)]));});return B(_n(_GW,new T2(1,_7g,_Hb)));},1);return B(_n(_H4,_Ha));},1);return new F(function(){return err(B(_n(_GX,_H9)));});},_He=function(_Hf,_Hg,_Hh,_Hi,_Hj){return new F(function(){return _H3(_Hf,_Hg,_Hj,_Hh,_Hi);});},_Hk=function(_Hl,_Hm,_Hn,_Ho){var _Hp=E(_Hn);return new F(function(){return _He(_Hl,_Hm,_Hp.a,_Hp.b,_Ho);});},_Hq=function(_Hr,_Hs,_Ht,_Hu){return new F(function(){return _Hk(_Hu,_Ht,_Hs,_Hr);});},_Hv=new T(function(){return B(unCStr("Int"));}),_Hw=function(_Hx,_Hy){return new F(function(){return _Hq(_GH,_Hy,_Hx,_Hv);});},_Hz=function(_HA,_HB){var _HC=E(_HA),_HD=E(_HC.a),_HE=E(_HB);if(_HD>_HE){return new F(function(){return _Hw(_HE,_HC);});}else{if(_HE>E(_HC.b)){return new F(function(){return _Hw(_HE,_HC);});}else{return _HE-_HD|0;}}},_HF=function(_HG){var _HH=E(_HG);return new F(function(){return _xt(_HH.a,_HH.b);});},_HI=function(_HJ){var _HK=E(_HJ),_HL=E(_HK.a),_HM=E(_HK.b);return (_HL>_HM)?E(_GI):(_HM-_HL|0)+1|0;},_HN=function(_HO,_HP){return new F(function(){return _yS(_HP,E(_HO).a);});},_HQ={_:0,a:_zI,b:_HF,c:_Hz,d:_HN,e:_Gq,f:_HI,g:_Gn},_HR=function(_HS,_HT,_){while(1){var _HU=B((function(_HV,_HW,_){var _HX=E(_HV);if(!_HX._){return new T2(0,_ox,_HW);}else{var _HY=B(A2(_HX.a,_HW,_));_HS=_HX.b;_HT=new T(function(){return E(E(_HY).b);});return __continue;}})(_HS,_HT,_));if(_HU!=__continue){return _HU;}}},_HZ=function(_I0,_I1){return new T2(1,_I0,_I1);},_I2=function(_I3,_I4){var _I5=E(_I4);return new T2(0,_I5.a,_I5.b);},_I6=function(_I7){return E(E(_I7).f);},_I8=function(_I9,_Ia,_Ib){var _Ic=E(_Ia),_Id=_Ic.a,_Ie=_Ic.b,_If=function(_){var _Ig=B(A2(_I6,_I9,_Ic));if(_Ig>=0){var _Ih=newArr(_Ig,_mg),_Ii=_Ih,_Ij=E(_Ig);if(!_Ij){return new T(function(){return new T4(0,E(_Id),E(_Ie),0,_Ii);});}else{var _Ik=function(_Il,_Im,_){while(1){var _In=E(_Il);if(!_In._){return E(_);}else{var _=_Ii[_Im]=_In.a;if(_Im!=(_Ij-1|0)){var _Io=_Im+1|0;_Il=_In.b;_Im=_Io;continue;}else{return E(_);}}}},_=B(_Ik(_Ib,0,_));return new T(function(){return new T4(0,E(_Id),E(_Ie),_Ij,_Ii);});}}else{return E(_ED);}};return new F(function(){return _ET(_If);});},_Ip=function(_Iq,_Ir,_Is,_It){var _Iu=new T(function(){var _Iv=E(_It),_Iw=_Iv.c-1|0,_Ix=new T(function(){return B(A2(_cF,_Ir,_w));});if(0<=_Iw){var _Iy=new T(function(){return B(_8F(_Ir));}),_Iz=function(_IA){var _IB=new T(function(){var _IC=new T(function(){return B(A1(_Is,new T(function(){return E(_Iv.d[_IA]);})));});return B(A3(_8T,_Iy,_HZ,_IC));});return new F(function(){return A3(_8R,_Ir,_IB,new T(function(){if(_IA!=_Iw){return B(_Iz(_IA+1|0));}else{return E(_Ix);}}));});};return B(_Iz(0));}else{return E(_Ix);}}),_ID=new T(function(){return B(_I2(_Iq,_It));});return new F(function(){return A3(_8T,B(_8F(_Ir)),function(_IE){return new F(function(){return _I8(_Iq,_ID,_IE);});},_Iu);});},_IF=function(_IG,_IH,_II,_IJ,_IK,_IL,_IM,_IN,_IO){var _IP=B(_8L(_IG));return new T2(0,new T3(0,E(B(A1(B(A1(_IP,_IH)),_IL))),E(B(A1(B(A1(_IP,_II)),_IM))),E(B(A1(B(A1(_IP,_IJ)),_IN)))),B(A1(B(A1(_IP,_IK)),_IO)));},_IQ=function(_IR,_IS,_IT,_IU,_IV,_IW,_IX,_IY,_IZ){var _J0=B(_6X(_IR));return new T2(0,new T3(0,E(B(A1(B(A1(_J0,_IS)),_IW))),E(B(A1(B(A1(_J0,_IT)),_IX))),E(B(A1(B(A1(_J0,_IU)),_IY)))),B(A1(B(A1(_J0,_IV)),_IZ)));},_J1=1.0e-2,_J2=function(_J3,_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb,_Jc,_Jd,_Je,_Jf,_Jg,_Jh,_Ji,_Jj,_Jk){var _Jl=B(_IF(_ng,_Ja,_Jb,_Jc,_Jd,_J1,_J1,_J1,_J1)),_Jm=E(_Jl.a),_Jn=B(_IQ(_ng,_J6,_J7,_J8,_J9,_Jm.a,_Jm.b,_Jm.c,_Jl.b)),_Jo=E(_Jn.a);return new F(function(){return _tG(_J3,_J4,_J5,_Jo.a,_Jo.b,_Jo.c,_Jn.b,_Ja,_Jb,_Jc,_Jd,_Je,_Jf,_Jg,_Jh,_Ji,_Jj,_Jk);});},_Jp=function(_Jq){var _Jr=E(_Jq),_Js=E(_Jr.d),_Jt=E(_Js.a),_Ju=E(_Jr.e),_Jv=E(_Ju.a),_Jw=E(_Jr.f),_Jx=B(_J2(_Jr.a,_Jr.b,_Jr.c,_Jt.a,_Jt.b,_Jt.c,_Js.b,_Jv.a,_Jv.b,_Jv.c,_Ju.b,_Jw.a,_Jw.b,_Jw.c,_Jr.g,_Jr.h,_Jr.i,_Jr.j));return {_:0,a:E(_Jx.a),b:E(_Jx.b),c:E(_Jx.c),d:E(_Jx.d),e:E(_Jx.e),f:E(_Jx.f),g:E(_Jx.g),h:_Jx.h,i:_Jx.i,j:_Jx.j};},_Jy=function(_Jz,_JA,_JB,_JC,_JD,_JE,_JF,_JG,_JH){var _JI=B(_8J(B(_8H(_Jz))));return new F(function(){return A3(_6X,_JI,new T(function(){return B(_pb(_Jz,_JA,_JB,_JC,_JE,_JF,_JG));}),new T(function(){return B(A3(_8L,_JI,_JD,_JH));}));});},_JJ=new T(function(){return B(unCStr("base"));}),_JK=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_JL=new T(function(){return B(unCStr("IOException"));}),_JM=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_JJ,_JK,_JL),_JN=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_JM,_w,_w),_JO=function(_JP){return E(_JN);},_JQ=function(_JR){var _JS=E(_JR);return new F(function(){return _2n(B(_2l(_JS.a)),_JO,_JS.b);});},_JT=new T(function(){return B(unCStr(": "));}),_JU=new T(function(){return B(unCStr(")"));}),_JV=new T(function(){return B(unCStr(" ("));}),_JW=new T(function(){return B(unCStr("interrupted"));}),_JX=new T(function(){return B(unCStr("system error"));}),_JY=new T(function(){return B(unCStr("unsatisified constraints"));}),_JZ=new T(function(){return B(unCStr("user error"));}),_K0=new T(function(){return B(unCStr("permission denied"));}),_K1=new T(function(){return B(unCStr("illegal operation"));}),_K2=new T(function(){return B(unCStr("end of file"));}),_K3=new T(function(){return B(unCStr("resource exhausted"));}),_K4=new T(function(){return B(unCStr("resource busy"));}),_K5=new T(function(){return B(unCStr("does not exist"));}),_K6=new T(function(){return B(unCStr("already exists"));}),_K7=new T(function(){return B(unCStr("resource vanished"));}),_K8=new T(function(){return B(unCStr("timeout"));}),_K9=new T(function(){return B(unCStr("unsupported operation"));}),_Ka=new T(function(){return B(unCStr("hardware fault"));}),_Kb=new T(function(){return B(unCStr("inappropriate type"));}),_Kc=new T(function(){return B(unCStr("invalid argument"));}),_Kd=new T(function(){return B(unCStr("failed"));}),_Ke=new T(function(){return B(unCStr("protocol error"));}),_Kf=function(_Kg,_Kh){switch(E(_Kg)){case 0:return new F(function(){return _n(_K6,_Kh);});break;case 1:return new F(function(){return _n(_K5,_Kh);});break;case 2:return new F(function(){return _n(_K4,_Kh);});break;case 3:return new F(function(){return _n(_K3,_Kh);});break;case 4:return new F(function(){return _n(_K2,_Kh);});break;case 5:return new F(function(){return _n(_K1,_Kh);});break;case 6:return new F(function(){return _n(_K0,_Kh);});break;case 7:return new F(function(){return _n(_JZ,_Kh);});break;case 8:return new F(function(){return _n(_JY,_Kh);});break;case 9:return new F(function(){return _n(_JX,_Kh);});break;case 10:return new F(function(){return _n(_Ke,_Kh);});break;case 11:return new F(function(){return _n(_Kd,_Kh);});break;case 12:return new F(function(){return _n(_Kc,_Kh);});break;case 13:return new F(function(){return _n(_Kb,_Kh);});break;case 14:return new F(function(){return _n(_Ka,_Kh);});break;case 15:return new F(function(){return _n(_K9,_Kh);});break;case 16:return new F(function(){return _n(_K8,_Kh);});break;case 17:return new F(function(){return _n(_K7,_Kh);});break;default:return new F(function(){return _n(_JW,_Kh);});}},_Ki=new T(function(){return B(unCStr("}"));}),_Kj=new T(function(){return B(unCStr("{handle: "));}),_Kk=function(_Kl,_Km,_Kn,_Ko,_Kp,_Kq){var _Kr=new T(function(){var _Ks=new T(function(){var _Kt=new T(function(){var _Ku=E(_Ko);if(!_Ku._){return E(_Kq);}else{var _Kv=new T(function(){return B(_n(_Ku,new T(function(){return B(_n(_JU,_Kq));},1)));},1);return B(_n(_JV,_Kv));}},1);return B(_Kf(_Km,_Kt));}),_Kw=E(_Kn);if(!_Kw._){return E(_Ks);}else{return B(_n(_Kw,new T(function(){return B(_n(_JT,_Ks));},1)));}}),_Kx=E(_Kp);if(!_Kx._){var _Ky=E(_Kl);if(!_Ky._){return E(_Kr);}else{var _Kz=E(_Ky.a);if(!_Kz._){var _KA=new T(function(){var _KB=new T(function(){return B(_n(_Ki,new T(function(){return B(_n(_JT,_Kr));},1)));},1);return B(_n(_Kz.a,_KB));},1);return new F(function(){return _n(_Kj,_KA);});}else{var _KC=new T(function(){var _KD=new T(function(){return B(_n(_Ki,new T(function(){return B(_n(_JT,_Kr));},1)));},1);return B(_n(_Kz.a,_KD));},1);return new F(function(){return _n(_Kj,_KC);});}}}else{return new F(function(){return _n(_Kx.a,new T(function(){return B(_n(_JT,_Kr));},1));});}},_KE=function(_KF){var _KG=E(_KF);return new F(function(){return _Kk(_KG.a,_KG.b,_KG.c,_KG.d,_KG.f,_w);});},_KH=function(_KI,_KJ,_KK){var _KL=E(_KJ);return new F(function(){return _Kk(_KL.a,_KL.b,_KL.c,_KL.d,_KL.f,_KK);});},_KM=function(_KN,_KO){var _KP=E(_KN);return new F(function(){return _Kk(_KP.a,_KP.b,_KP.c,_KP.d,_KP.f,_KO);});},_KQ=function(_KR,_KS){return new F(function(){return _2Q(_KM,_KR,_KS);});},_KT=new T3(0,_KH,_KE,_KQ),_KU=new T(function(){return new T5(0,_JO,_KT,_KV,_JQ,_KE);}),_KV=function(_KW){return new T2(0,_KU,_KW);},_KX=__Z,_KY=7,_KZ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_L0=new T6(0,_KX,_KY,_w,_KZ,_KX,_KX),_L1=new T(function(){return B(_KV(_L0));}),_L2=function(_){return new F(function(){return die(_L1);});},_L3=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_L4=new T6(0,_KX,_KY,_w,_L3,_KX,_KX),_L5=new T(function(){return B(_KV(_L4));}),_L6=function(_){return new F(function(){return die(_L5);});},_L7=function(_L8,_){return new T2(0,_w,_L8);},_L9=0.6,_La=1,_Lb=new T(function(){return B(unCStr(")"));}),_Lc=function(_Ld,_Le){var _Lf=new T(function(){var _Lg=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Fd(0,_Ld,_w)),_Lb));})));},1);return B(_n(B(_Fd(0,_Le,_w)),_Lg));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Lf)));});},_Lh=function(_Li,_Lj){var _Lk=new T(function(){var _Ll=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Fd(0,_Lj,_w)),_Lb));})));},1);return B(_n(B(_Fd(0,_Li,_w)),_Ll));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Lk)));});},_Lm=function(_Ln){var _Lo=E(_Ln);if(!_Lo._){return E(_L7);}else{var _Lp=new T(function(){return B(_Lm(_Lo.b));}),_Lq=function(_Lr){var _Ls=E(_Lr);if(!_Ls._){return E(_Lp);}else{var _Lt=_Ls.a,_Lu=new T(function(){return B(_Lq(_Ls.b));}),_Lv=new T(function(){return 0.1*E(E(_Lt).e)/1.0e-2;}),_Lw=new T(function(){var _Lx=E(_Lt);if(_Lx.a!=_Lx.b){return E(_La);}else{return E(_L9);}}),_Ly=function(_Lz,_){var _LA=E(_Lz),_LB=_LA.c,_LC=_LA.d,_LD=E(_LA.a),_LE=E(_LA.b),_LF=E(_Lt),_LG=_LF.a,_LH=_LF.b,_LI=E(_LF.c),_LJ=_LI.b,_LK=E(_LI.a),_LL=_LK.a,_LM=_LK.b,_LN=_LK.c,_LO=E(_LF.d),_LP=_LO.b,_LQ=E(_LO.a),_LR=_LQ.a,_LS=_LQ.b,_LT=_LQ.c;if(_LD>_LG){return new F(function(){return _L6(_);});}else{if(_LG>_LE){return new F(function(){return _L6(_);});}else{if(_LD>_LH){return new F(function(){return _L2(_);});}else{if(_LH>_LE){return new F(function(){return _L2(_);});}else{var _LU=_LG-_LD|0;if(0>_LU){return new F(function(){return _Lc(_LB,_LU);});}else{if(_LU>=_LB){return new F(function(){return _Lc(_LB,_LU);});}else{var _LV=E(_LC[_LU]),_LW=E(_LV.c),_LX=_LW.b,_LY=E(_LW.a),_LZ=_LY.a,_M0=_LY.b,_M1=_LY.c,_M2=E(_LV.e),_M3=E(_M2.a),_M4=B(_IF(_ng,_LL,_LM,_LN,_LJ,_LZ,_M0,_M1,_LX)),_M5=E(_M4.a),_M6=B(_IF(_ng,_M5.a,_M5.b,_M5.c,_M4.b,_LL,_LM,_LN,_LJ)),_M7=E(_M6.a),_M8=_LH-_LD|0;if(0>_M8){return new F(function(){return _Lh(_M8,_LB);});}else{if(_M8>=_LB){return new F(function(){return _Lh(_M8,_LB);});}else{var _M9=E(_LC[_M8]),_Ma=E(_M9.c),_Mb=_Ma.b,_Mc=E(_Ma.a),_Md=_Mc.a,_Me=_Mc.b,_Mf=_Mc.c,_Mg=E(_M9.e),_Mh=E(_Mg.a),_Mi=B(_IF(_ng,_LR,_LS,_LT,_LP,_Md,_Me,_Mf,_Mb)),_Mj=E(_Mi.a),_Mk=B(_IF(_ng,_Mj.a,_Mj.b,_Mj.c,_Mi.b,_LR,_LS,_LT,_LP)),_Ml=E(_Mk.a),_Mm=E(_M7.a)+E(_M7.b)+E(_M7.c)+E(_M6.b)+E(_Ml.a)+E(_Ml.b)+E(_Ml.c)+E(_Mk.b);if(!_Mm){var _Mn=B(A2(_Lu,_LA,_));return new T2(0,new T2(1,_ox,new T(function(){return E(E(_Mn).a);})),new T(function(){return E(E(_Mn).b);}));}else{var _Mo=new T(function(){return  -((B(_Jy(_nM,_M3.a,_M3.b,_M3.c,_M2.b,_LL,_LM,_LN,_LJ))-B(_Jy(_nM,_Mh.a,_Mh.b,_Mh.c,_Mg.b,_LR,_LS,_LT,_LP))-E(_Lv))/_Mm);}),_Mp=function(_Mq,_Mr,_Ms,_Mt,_){var _Mu=new T(function(){var _Mv=function(_Mw,_Mx,_My,_Mz,_MA){if(_Mw>_LH){return E(_MA);}else{if(_LH>_Mx){return E(_MA);}else{var _MB=function(_){var _MC=newArr(_My,_mg),_MD=_MC,_ME=function(_MF,_){while(1){if(_MF!=_My){var _=_MD[_MF]=_Mz[_MF],_MG=_MF+1|0;_MF=_MG;continue;}else{return E(_);}}},_=B(_ME(0,_)),_MH=_LH-_Mw|0;if(0>_MH){return new F(function(){return _Lh(_MH,_My);});}else{if(_MH>=_My){return new F(function(){return _Lh(_MH,_My);});}else{var _=_MD[_MH]=new T(function(){var _MI=E(_Mz[_MH]),_MJ=E(_MI.e),_MK=E(_MJ.a),_ML=B(_IF(_ng,_Md,_Me,_Mf,_Mb,_LR,_LS,_LT,_LP)),_MM=E(_ML.a),_MN=E(_Mo)*E(_Lw),_MO=B(_IF(_ng,_MM.a,_MM.b,_MM.c,_ML.b,_MN,_MN,_MN,_MN)),_MP=E(_MO.a),_MQ=B(_IQ(_ng,_MK.a,_MK.b,_MK.c,_MJ.b, -E(_MP.a), -E(_MP.b), -E(_MP.c), -E(_MO.b)));return {_:0,a:E(_MI.a),b:E(_MI.b),c:E(_MI.c),d:E(_MI.d),e:E(new T2(0,E(_MQ.a),E(_MQ.b))),f:E(_MI.f),g:E(_MI.g),h:_MI.h,i:_MI.i,j:_MI.j};});return new T4(0,E(_Mw),E(_Mx),_My,_MD);}}};return new F(function(){return _ET(_MB);});}}};if(_Mq>_LG){return B(_Mv(_Mq,_Mr,_Ms,_Mt,new T4(0,E(_Mq),E(_Mr),_Ms,_Mt)));}else{if(_LG>_Mr){return B(_Mv(_Mq,_Mr,_Ms,_Mt,new T4(0,E(_Mq),E(_Mr),_Ms,_Mt)));}else{var _MR=function(_){var _MS=newArr(_Ms,_mg),_MT=_MS,_MU=function(_MV,_){while(1){if(_MV!=_Ms){var _=_MT[_MV]=_Mt[_MV],_MW=_MV+1|0;_MV=_MW;continue;}else{return E(_);}}},_=B(_MU(0,_)),_MX=_LG-_Mq|0;if(0>_MX){return new F(function(){return _Lc(_Ms,_MX);});}else{if(_MX>=_Ms){return new F(function(){return _Lc(_Ms,_MX);});}else{var _=_MT[_MX]=new T(function(){var _MY=E(_Mt[_MX]),_MZ=E(_MY.e),_N0=E(_MZ.a),_N1=B(_IF(_ng,_LZ,_M0,_M1,_LX,_LL,_LM,_LN,_LJ)),_N2=E(_N1.a),_N3=E(_Mo)*E(_Lw),_N4=B(_IF(_ng,_N2.a,_N2.b,_N2.c,_N1.b,_N3,_N3,_N3,_N3)),_N5=E(_N4.a),_N6=B(_IQ(_ng,_N0.a,_N0.b,_N0.c,_MZ.b,_N5.a,_N5.b,_N5.c,_N4.b));return {_:0,a:E(_MY.a),b:E(_MY.b),c:E(_MY.c),d:E(_MY.d),e:E(new T2(0,E(_N6.a),E(_N6.b))),f:E(_MY.f),g:E(_MY.g),h:_MY.h,i:_MY.i,j:_MY.j};});return new T4(0,E(_Mq),E(_Mr),_Ms,_MT);}}},_N7=B(_ET(_MR));return B(_Mv(E(_N7.a),E(_N7.b),_N7.c,_N7.d,_N7));}}});return new T2(0,_ox,_Mu);};if(!E(_LF.f)){var _N8=B(_Mp(_LD,_LE,_LB,_LC,_)),_N9=B(A2(_Lu,new T(function(){return E(E(_N8).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_N8).a);}),new T(function(){return E(E(_N9).a);})),new T(function(){return E(E(_N9).b);}));}else{if(E(_Mo)<0){var _Na=B(A2(_Lu,_LA,_));return new T2(0,new T2(1,_ox,new T(function(){return E(E(_Na).a);})),new T(function(){return E(E(_Na).b);}));}else{var _Nb=B(_Mp(_LD,_LE,_LB,_LC,_)),_Nc=B(A2(_Lu,new T(function(){return E(E(_Nb).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_Nb).a);}),new T(function(){return E(E(_Nc).a);})),new T(function(){return E(E(_Nc).b);}));}}}}}}}}}}}};return E(_Ly);}};return new F(function(){return _Lq(_Lo.a);});}},_Nd=function(_,_Ne){var _Nf=new T(function(){return B(_Lm(E(_Ne).a));}),_Ng=function(_Nh){var _Ni=E(_Nh);return (_Ni==1)?E(new T2(1,_Nf,_w)):new T2(1,_Nf,new T(function(){return B(_Ng(_Ni-1|0));}));},_Nj=B(_HR(B(_Ng(5)),new T(function(){return E(E(_Ne).b);}),_)),_Nk=new T(function(){return B(_Ip(_HQ,_FF,_Jp,new T(function(){return E(E(_Nj).b);})));});return new T2(0,_ox,_Nk);},_Nl=function(_Nm,_Nn,_No,_Np,_Nq){var _Nr=B(_8J(B(_8H(_Nm))));return new F(function(){return A3(_6X,_Nr,new T(function(){return B(A3(_8L,_Nr,_Nn,_Np));}),new T(function(){return B(A3(_8L,_Nr,_No,_Nq));}));});},_Ns=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Nt=new T6(0,_KX,_KY,_w,_Ns,_KX,_KX),_Nu=new T(function(){return B(_KV(_Nt));}),_Nv=function(_){return new F(function(){return die(_Nu);});},_Nw=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Nx=new T6(0,_KX,_KY,_w,_Nw,_KX,_KX),_Ny=new T(function(){return B(_KV(_Nx));}),_Nz=function(_){return new F(function(){return die(_Ny);});},_NA=false,_NB=true,_NC=function(_ND){var _NE=E(_ND),_NF=_NE.b,_NG=E(_NE.d),_NH=E(_NE.e),_NI=E(_NH.a),_NJ=E(_NE.g),_NK=B(A1(_NF,_NG.a)),_NL=B(_qb(_nM,_NK.a,_NK.b,_NK.c,_NJ.a,_NJ.b,_NJ.c));return {_:0,a:E(_NE.a),b:E(_NF),c:E(_NE.c),d:E(_NG),e:E(new T2(0,E(new T3(0,E(_NI.a)+E(_NL.a)*1.0e-2,E(_NI.b)+E(_NL.b)*1.0e-2,E(_NI.c)+E(_NL.c)*1.0e-2)),E(_NH.b))),f:E(_NE.f),g:E(_NJ),h:_NE.h,i:_NE.i,j:_NE.j};},_NM=new T(function(){return eval("__strict(collideBound)");}),_NN=new T(function(){return eval("__strict(mouseContact)");}),_NO=new T(function(){return eval("__strict(collide)");}),_NP=function(_NQ){var _NR=E(_NQ);if(!_NR._){return __Z;}else{return new F(function(){return _n(_NR.a,new T(function(){return B(_NP(_NR.b));},1));});}},_NS=0,_NT=new T3(0,E(_NS),E(_NS),E(_NS)),_NU=new T2(0,E(_NT),E(_NS)),_NV=new T2(0,_nM,_ol),_NW=new T(function(){return B(_lN(_NV));}),_NX=function(_NY,_){var _NZ=B(_Ip(_HQ,_FF,_NC,_NY)),_O0=E(_NZ.a),_O1=E(_NZ.b);if(_O0<=_O1){var _O2=function(_O3,_O4,_O5,_O6,_O7,_){if(_O4>_O3){return new F(function(){return _Nz(_);});}else{if(_O3>_O5){return new F(function(){return _Nz(_);});}else{var _O8=new T(function(){var _O9=_O3-_O4|0;if(0>_O9){return B(_Lh(_O9,_O6));}else{if(_O9>=_O6){return B(_Lh(_O9,_O6));}else{return E(_O7[_O9]);}}}),_Oa=function(_Ob,_Oc,_Od,_Oe,_Of,_){var _Og=E(_Ob);if(!_Og._){return new T2(0,_w,new T4(0,E(_Oc),E(_Od),_Oe,_Of));}else{var _Oh=E(_Og.a);if(_Oc>_Oh){return new F(function(){return _Nv(_);});}else{if(_Oh>_Od){return new F(function(){return _Nv(_);});}else{var _Oi=_Oh-_Oc|0;if(0>_Oi){return new F(function(){return _Lc(_Oe,_Oi);});}else{if(_Oi>=_Oe){return new F(function(){return _Lc(_Oe,_Oi);});}else{var _Oj=__app2(E(_NO),B(_F3(E(_O8))),B(_F3(E(_Of[_Oi])))),_Ok=__arr2lst(0,_Oj),_Ol=B(_Gi(_Ok,_)),_Om=B(_Oa(_Og.b,_Oc,_Od,_Oe,_Of,_)),_On=new T(function(){var _Oo=new T(function(){return _O3!=_Oh;}),_Op=function(_Oq){var _Or=E(_Oq);if(!_Or._){return __Z;}else{var _Os=_Or.b,_Ot=E(_Or.a),_Ou=E(_Ot.b),_Ov=E(_Ot.a),_Ow=E(_Ot.c),_Ox=_Ow.a,_Oy=_Ow.b,_Oz=E(_Ot.e),_OA=E(_Ot.d),_OB=_OA.a,_OC=_OA.b,_OD=E(_Ot.f),_OE=new T(function(){var _OF=B(_pl(_nM,_OD.a,_OD.b,_OD.c)),_OG=Math.sqrt(B(_Nl(_nM,_OB,_OC,_OB,_OC)));return new T3(0,_OG*E(_OF.a),_OG*E(_OF.b),_OG*E(_OF.c));}),_OH=new T(function(){var _OI=B(_pl(_nM,_Oz.a,_Oz.b,_Oz.c)),_OJ=Math.sqrt(B(_Nl(_nM,_Ox,_Oy,_Ox,_Oy)));return new T3(0,_OJ*E(_OI.a),_OJ*E(_OI.b),_OJ*E(_OI.c));}),_OK=new T(function(){var _OL=B(A1(_NW,_Ou)),_OM=B(_pl(_nM,_OL.a,_OL.b,_OL.c));return new T3(0,E(_OM.a),E(_OM.b),E(_OM.c));}),_ON=new T(function(){var _OO=B(A1(_NW,_Ov)),_OP=B(_pl(_nM,_OO.a,_OO.b,_OO.c));return new T3(0,E(_OP.a),E(_OP.b),E(_OP.c));}),_OQ=E(_Ou.a)+ -E(_Ov.a),_OR=E(_Ou.b)+ -E(_Ov.b),_OS=E(_Ou.c)+ -E(_Ov.c),_OT=new T(function(){return Math.sqrt(B(_pb(_nM,_OQ,_OR,_OS,_OQ,_OR,_OS)));}),_OU=new T(function(){var _OV=1/E(_OT);return new T3(0,_OQ*_OV,_OR*_OV,_OS*_OV);}),_OW=new T(function(){if(!E(_Ot.g)){return E(_OU);}else{var _OX=E(_OU);return new T3(0,-1*E(_OX.a),-1*E(_OX.b),-1*E(_OX.c));}}),_OY=new T(function(){if(!E(_Ot.h)){return E(_OU);}else{var _OZ=E(_OU);return new T3(0,-1*E(_OZ.a),-1*E(_OZ.b),-1*E(_OZ.c));}});return (!E(_Oo))?new T2(1,new T(function(){var _P0=E(_OW),_P1=E(_P0.b),_P2=E(_P0.c),_P3=E(_P0.a),_P4=E(_ON),_P5=E(_P4.c),_P6=E(_P4.b),_P7=E(_P4.a),_P8=E(_OH),_P9=E(_P8.c),_Pa=E(_P8.b),_Pb=E(_P8.a),_Pc=_P1*_P5-_P6*_P2,_Pd=_P2*_P7-_P5*_P3,_Pe=_P3*_P6-_P7*_P1,_Pf=B(_pb(_nM,_Pd*_P9-_Pa*_Pe,_Pe*_Pb-_P9*_Pc,_Pc*_Pa-_Pb*_Pd,_P7,_P6,_P5));return new T6(0,_O3,_Oh,E(new T2(0,E(new T3(0,E(_Pc),E(_Pd),E(_Pe))),E(_Pf))),E(_NU),_OT,_NA);}),new T2(1,new T(function(){var _Pg=E(_OY),_Ph=E(_Pg.b),_Pi=E(_Pg.c),_Pj=E(_Pg.a),_Pk=E(_OK),_Pl=E(_Pk.c),_Pm=E(_Pk.b),_Pn=E(_Pk.a),_Po=E(_OE),_Pp=E(_Po.c),_Pq=E(_Po.b),_Pr=E(_Po.a),_Ps=_Ph*_Pl-_Pm*_Pi,_Pt=_Pi*_Pn-_Pl*_Pj,_Pu=_Pj*_Pm-_Pn*_Ph,_Pv=B(_pb(_nM,_Pt*_Pp-_Pq*_Pu,_Pu*_Pr-_Pp*_Ps,_Ps*_Pq-_Pr*_Pt,_Pn,_Pm,_Pl));return new T6(0,_O3,_Oh,E(_NU),E(new T2(0,E(new T3(0,E(_Ps),E(_Pt),E(_Pu))),E(_Pv))),_OT,_NA);}),new T(function(){return B(_Op(_Os));}))):new T2(1,new T(function(){var _Pw=E(_OW),_Px=E(_Pw.b),_Py=E(_Pw.c),_Pz=E(_Pw.a),_PA=E(_ON),_PB=_PA.a,_PC=_PA.b,_PD=_PA.c,_PE=B(_qb(_nM,_Pz,_Px,_Py,_PB,_PC,_PD)),_PF=E(_OH),_PG=E(_PF.c),_PH=E(_PF.b),_PI=E(_PF.a),_PJ=B(_pb(_nM,_Px*_PG-_PH*_Py,_Py*_PI-_PG*_Pz,_Pz*_PH-_PI*_Px,_PB,_PC,_PD)),_PK=E(_OY),_PL=E(_PK.b),_PM=E(_PK.c),_PN=E(_PK.a),_PO=E(_OK),_PP=_PO.a,_PQ=_PO.b,_PR=_PO.c,_PS=B(_qb(_nM,_PN,_PL,_PM,_PP,_PQ,_PR)),_PT=E(_OE),_PU=E(_PT.c),_PV=E(_PT.b),_PW=E(_PT.a),_PX=B(_pb(_nM,_PL*_PU-_PV*_PM,_PM*_PW-_PU*_PN,_PN*_PV-_PW*_PL,_PP,_PQ,_PR));return new T6(0,_O3,_Oh,E(new T2(0,E(new T3(0,E(_PE.a),E(_PE.b),E(_PE.c))),E(_PJ))),E(new T2(0,E(new T3(0,E(_PS.a),E(_PS.b),E(_PS.c))),E(_PX))),_OT,_NB);}),new T(function(){return B(_Op(_Os));}));}};return B(_Op(_Ol));});return new T2(0,new T2(1,_On,new T(function(){return E(E(_Om).a);})),new T(function(){return E(E(_Om).b);}));}}}}}},_PY=B(_Oa(B(_wS(_O3,_O1)),_O4,_O5,_O6,_O7,_)),_PZ=E(_O8),_Q0=E(_PZ.d).a,_Q1=__app1(E(_NM),B(_F3(_PZ))),_Q2=__arr2lst(0,_Q1),_Q3=B(_Gi(_Q2,_)),_Q4=__app1(E(_NN),_O3),_Q5=__arr2lst(0,_Q4),_Q6=B(_Gi(_Q5,_));if(_O3!=_O1){var _Q7=E(_PY),_Q8=E(_Q7.b),_Q9=B(_O2(_O3+1|0,E(_Q8.a),E(_Q8.b),_Q8.c,_Q8.d,_)),_Qa=new T(function(){var _Qb=new T(function(){var _Qc=B(A1(_NW,_Q0)),_Qd=B(_pl(_nM,_Qc.a,_Qc.b,_Qc.c));return new T3(0,E(_Qd.a),E(_Qd.b),E(_Qd.c));}),_Qe=new T(function(){var _Qf=new T(function(){return B(_NP(_Q7.a));}),_Qg=function(_Qh){var _Qi=E(_Qh);if(!_Qi._){return E(_Qf);}else{var _Qj=E(_Qi.a),_Qk=E(_Qj.b),_Ql=E(_Qj.a),_Qm=E(_Qj.c),_Qn=_Qm.a,_Qo=_Qm.b,_Qp=E(_Qj.e);return new T2(1,new T(function(){var _Qq=E(_Qk.a)+ -E(_Ql.a),_Qr=E(_Qk.b)+ -E(_Ql.b),_Qs=E(_Qk.c)+ -E(_Ql.c),_Qt=B(A1(_NW,_Ql)),_Qu=B(_pl(_nM,_Qt.a,_Qt.b,_Qt.c)),_Qv=_Qu.a,_Qw=_Qu.b,_Qx=_Qu.c,_Qy=Math.sqrt(B(_pb(_nM,_Qq,_Qr,_Qs,_Qq,_Qr,_Qs))),_Qz=1/_Qy,_QA=_Qq*_Qz,_QB=_Qr*_Qz,_QC=_Qs*_Qz,_QD=B(_qb(_nM,_QA,_QB,_QC,_Qv,_Qw,_Qx)),_QE=B(_pl(_nM,_Qp.a,_Qp.b,_Qp.c)),_QF=Math.sqrt(B(_Nl(_nM,_Qn,_Qo,_Qn,_Qo))),_QG=_QF*E(_QE.a),_QH=_QF*E(_QE.b),_QI=_QF*E(_QE.c),_QJ=B(_pb(_nM,_QB*_QI-_QH*_QC,_QC*_QG-_QI*_QA,_QA*_QH-_QG*_QB,_Qv,_Qw,_Qx));return new T6(0,_O3,_O3,E(new T2(0,E(new T3(0,E(_QD.a),E(_QD.b),E(_QD.c))),E(_QJ))),E(_NU),_Qy,_NB);}),new T(function(){return B(_Qg(_Qi.b));}));}};return B(_Qg(_Q3));}),_QK=function(_QL){var _QM=E(_QL);if(!_QM._){return E(_Qe);}else{var _QN=E(_QM.a),_QO=E(_QN.b),_QP=new T(function(){var _QQ=E(_Q0),_QR=E(_QO.c)+ -E(_QQ.c),_QS=E(_QO.b)+ -E(_QQ.b),_QT=E(_QO.a)+ -E(_QQ.a),_QU=Math.sqrt(B(_pb(_nM,_QT,_QS,_QR,_QT,_QS,_QR))),_QV=function(_QW,_QX,_QY){var _QZ=E(_Qb),_R0=_QZ.a,_R1=_QZ.b,_R2=_QZ.c,_R3=B(_qb(_nM,_QW,_QX,_QY,_R0,_R1,_R2)),_R4=B(_pb(_nM,_QX*0-0*_QY,_QY*0-0*_QW,_QW*0-0*_QX,_R0,_R1,_R2));return new T6(0,_O3,_O3,new T2(0,E(new T3(0,E(_R3.a),E(_R3.b),E(_R3.c))),E(_R4)),_NU,_QU,_NB);};if(!E(_QN.g)){var _R5=1/_QU,_R6=B(_QV(_QT*_R5,_QS*_R5,_QR*_R5));return new T6(0,_R6.a,_R6.b,E(_R6.c),E(_R6.d),_R6.e,_R6.f);}else{var _R7=1/_QU,_R8=B(_QV(-1*_QT*_R7,-1*_QS*_R7,-1*_QR*_R7));return new T6(0,_R8.a,_R8.b,E(_R8.c),E(_R8.d),_R8.e,_R8.f);}});return new T2(1,_QP,new T(function(){return B(_QK(_QM.b));}));}};return B(_QK(_Q6));});return new T2(0,new T2(1,_Qa,new T(function(){return E(E(_Q9).a);})),new T(function(){return E(E(_Q9).b);}));}else{var _R9=new T(function(){var _Ra=new T(function(){var _Rb=B(A1(_NW,_Q0)),_Rc=B(_pl(_nM,_Rb.a,_Rb.b,_Rb.c));return new T3(0,E(_Rc.a),E(_Rc.b),E(_Rc.c));}),_Rd=new T(function(){var _Re=new T(function(){return B(_NP(E(_PY).a));}),_Rf=function(_Rg){var _Rh=E(_Rg);if(!_Rh._){return E(_Re);}else{var _Ri=E(_Rh.a),_Rj=E(_Ri.b),_Rk=E(_Ri.a),_Rl=E(_Ri.c),_Rm=_Rl.a,_Rn=_Rl.b,_Ro=E(_Ri.e);return new T2(1,new T(function(){var _Rp=E(_Rj.a)+ -E(_Rk.a),_Rq=E(_Rj.b)+ -E(_Rk.b),_Rr=E(_Rj.c)+ -E(_Rk.c),_Rs=B(A1(_NW,_Rk)),_Rt=B(_pl(_nM,_Rs.a,_Rs.b,_Rs.c)),_Ru=_Rt.a,_Rv=_Rt.b,_Rw=_Rt.c,_Rx=Math.sqrt(B(_pb(_nM,_Rp,_Rq,_Rr,_Rp,_Rq,_Rr))),_Ry=1/_Rx,_Rz=_Rp*_Ry,_RA=_Rq*_Ry,_RB=_Rr*_Ry,_RC=B(_qb(_nM,_Rz,_RA,_RB,_Ru,_Rv,_Rw)),_RD=B(_pl(_nM,_Ro.a,_Ro.b,_Ro.c)),_RE=Math.sqrt(B(_Nl(_nM,_Rm,_Rn,_Rm,_Rn))),_RF=_RE*E(_RD.a),_RG=_RE*E(_RD.b),_RH=_RE*E(_RD.c),_RI=B(_pb(_nM,_RA*_RH-_RG*_RB,_RB*_RF-_RH*_Rz,_Rz*_RG-_RF*_RA,_Ru,_Rv,_Rw));return new T6(0,_O3,_O3,E(new T2(0,E(new T3(0,E(_RC.a),E(_RC.b),E(_RC.c))),E(_RI))),E(_NU),_Rx,_NB);}),new T(function(){return B(_Rf(_Rh.b));}));}};return B(_Rf(_Q3));}),_RJ=function(_RK){var _RL=E(_RK);if(!_RL._){return E(_Rd);}else{var _RM=E(_RL.a),_RN=E(_RM.b),_RO=new T(function(){var _RP=E(_Q0),_RQ=E(_RN.c)+ -E(_RP.c),_RR=E(_RN.b)+ -E(_RP.b),_RS=E(_RN.a)+ -E(_RP.a),_RT=Math.sqrt(B(_pb(_nM,_RS,_RR,_RQ,_RS,_RR,_RQ))),_RU=function(_RV,_RW,_RX){var _RY=E(_Ra),_RZ=_RY.a,_S0=_RY.b,_S1=_RY.c,_S2=B(_qb(_nM,_RV,_RW,_RX,_RZ,_S0,_S1)),_S3=B(_pb(_nM,_RW*0-0*_RX,_RX*0-0*_RV,_RV*0-0*_RW,_RZ,_S0,_S1));return new T6(0,_O3,_O3,new T2(0,E(new T3(0,E(_S2.a),E(_S2.b),E(_S2.c))),E(_S3)),_NU,_RT,_NB);};if(!E(_RM.g)){var _S4=1/_RT,_S5=B(_RU(_RS*_S4,_RR*_S4,_RQ*_S4));return new T6(0,_S5.a,_S5.b,E(_S5.c),E(_S5.d),_S5.e,_S5.f);}else{var _S6=1/_RT,_S7=B(_RU(-1*_RS*_S6,-1*_RR*_S6,-1*_RQ*_S6));return new T6(0,_S7.a,_S7.b,E(_S7.c),E(_S7.d),_S7.e,_S7.f);}});return new T2(1,_RO,new T(function(){return B(_RJ(_RL.b));}));}};return B(_RJ(_Q6));});return new T2(0,new T2(1,_R9,_w),new T(function(){return E(E(_PY).b);}));}}}},_S8=B(_O2(_O0,_O0,_O1,_NZ.c,_NZ.d,_));return new F(function(){return _Nd(_,_S8);});}else{return new F(function(){return _Nd(_,new T2(0,_w,_NZ));});}},_S9=new T(function(){return eval("__strict(passObject)");}),_Sa=new T(function(){return eval("__strict(refresh)");}),_Sb=function(_Sc,_){var _Sd=__app0(E(_Sa)),_Se=__app0(E(_F8)),_Sf=E(_Sc),_Sg=_Sf.c,_Sh=_Sf.d,_Si=E(_Sf.a),_Sj=E(_Sf.b);if(_Si<=_Sj){if(_Si>_Sj){return E(_F6);}else{if(0>=_Sg){return new F(function(){return _Fj(_Sg,0);});}else{var _Sk=E(_S9),_Sl=__app2(_Sk,_Si,B(_F3(E(_Sh[0]))));if(_Si!=_Sj){var _Sm=function(_Sn,_){if(_Si>_Sn){return E(_F6);}else{if(_Sn>_Sj){return E(_F6);}else{var _So=_Sn-_Si|0;if(0>_So){return new F(function(){return _Fj(_Sg,_So);});}else{if(_So>=_Sg){return new F(function(){return _Fj(_Sg,_So);});}else{var _Sp=__app2(_Sk,_Sn,B(_F3(E(_Sh[_So]))));if(_Sn!=_Sj){var _Sq=B(_Sm(_Sn+1|0,_));return new T2(1,_ox,_Sq);}else{return _Fo;}}}}}},_Sr=B(_Sm(_Si+1|0,_)),_Ss=__app0(E(_F7)),_St=B(_NX(_Sf,_));return new T(function(){return E(E(_St).b);});}else{var _Su=__app0(E(_F7)),_Sv=B(_NX(_Sf,_));return new T(function(){return E(E(_Sv).b);});}}}}else{var _Sw=__app0(E(_F7)),_Sx=B(_NX(_Sf,_));return new T(function(){return E(E(_Sx).b);});}},_Sy=function(_Sz,_){while(1){var _SA=E(_Sz);if(!_SA._){return _ox;}else{var _SB=_SA.b,_SC=E(_SA.a);switch(_SC._){case 0:var _SD=B(A1(_SC.a,_));_Sz=B(_n(_SB,new T2(1,_SD,_w)));continue;case 1:_Sz=B(_n(_SB,_SC.a));continue;default:_Sz=_SB;continue;}}}},_SE=function(_SF,_SG,_){var _SH=E(_SF);switch(_SH._){case 0:var _SI=B(A1(_SH.a,_));return new F(function(){return _Sy(B(_n(_SG,new T2(1,_SI,_w))),_);});break;case 1:return new F(function(){return _Sy(B(_n(_SG,_SH.a)),_);});break;default:return new F(function(){return _Sy(_SG,_);});}},_SJ=new T0(2),_SK=function(_SL){return new T0(2);},_SM=function(_SN,_SO,_SP){return function(_){var _SQ=E(_SN),_SR=rMV(_SQ),_SS=E(_SR);if(!_SS._){var _ST=new T(function(){var _SU=new T(function(){return B(A1(_SP,_ox));});return B(_n(_SS.b,new T2(1,new T2(0,_SO,function(_SV){return E(_SU);}),_w)));}),_=wMV(_SQ,new T2(0,_SS.a,_ST));return _SJ;}else{var _SW=E(_SS.a);if(!_SW._){var _=wMV(_SQ,new T2(0,_SO,_w));return new T(function(){return B(A1(_SP,_ox));});}else{var _=wMV(_SQ,new T1(1,_SW.b));return new T1(1,new T2(1,new T(function(){return B(A1(_SP,_ox));}),new T2(1,new T(function(){return B(A2(_SW.a,_SO,_SK));}),_w)));}}};},_SX=new T(function(){return E(_up);}),_SY=new T(function(){return eval("window.requestAnimationFrame");}),_SZ=new T1(1,_w),_T0=function(_T1,_T2){return function(_){var _T3=E(_T1),_T4=rMV(_T3),_T5=E(_T4);if(!_T5._){var _T6=_T5.a,_T7=E(_T5.b);if(!_T7._){var _=wMV(_T3,_SZ);return new T(function(){return B(A1(_T2,_T6));});}else{var _T8=E(_T7.a),_=wMV(_T3,new T2(0,_T8.a,_T7.b));return new T1(1,new T2(1,new T(function(){return B(A1(_T2,_T6));}),new T2(1,new T(function(){return B(A1(_T8.b,_SK));}),_w)));}}else{var _T9=new T(function(){var _Ta=function(_Tb){var _Tc=new T(function(){return B(A1(_T2,_Tb));});return function(_Td){return E(_Tc);};};return B(_n(_T5.a,new T2(1,_Ta,_w)));}),_=wMV(_T3,new T1(1,_T9));return _SJ;}};},_Te=function(_Tf,_Tg){return new T1(0,B(_T0(_Tf,_Tg)));},_Th=function(_Ti,_Tj){var _Tk=new T(function(){return new T1(0,B(_SM(_Ti,_ox,_SK)));});return function(_){var _Tl=__createJSFunc(2,function(_Tm,_){var _Tn=B(_SE(_Tk,_w,_));return _SX;}),_To=__app1(E(_SY),_Tl);return new T(function(){return B(_Te(_Ti,_Tj));});};},_Tp=new T1(1,_w),_Tq=function(_Tr,_Ts,_){var _Tt=function(_){var _Tu=nMV(_Tr),_Tv=_Tu;return new T(function(){var _Tw=new T(function(){return B(_Tx(_));}),_Ty=function(_){var _Tz=rMV(_Tv),_TA=B(A2(_Ts,_Tz,_)),_=wMV(_Tv,_TA),_TB=function(_){var _TC=nMV(_Tp);return new T(function(){return new T1(0,B(_Th(_TC,function(_TD){return E(_Tw);})));});};return new T1(0,_TB);},_TE=new T(function(){return new T1(0,_Ty);}),_Tx=function(_TF){return E(_TE);};return B(_Tx(_));});};return new F(function(){return _SE(new T1(0,_Tt),_w,_);});},_TG=new T(function(){return eval("__strict(setBounds)");}),_TH=function(_){var _TI=__app3(E(_lt),E(_lD),E(_m9),E(_ls)),_TJ=__app2(E(_TG),E(_iI),E(_iF));return new F(function(){return _Tq(_EW,_Sb,_);});},_TK=function(_){return new F(function(){return _TH(_);});};
var hasteMain = function() {B(A(_TK, [0]));};window.onload = hasteMain;