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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=function(_hP){var _hQ=new T(function(){return E(E(_hP).a);}),_hR=new T(function(){return B(_8J(new T(function(){return B(_8H(_hQ));})));}),_hS=new T(function(){return B(A2(_8s,_hR,_8r));}),_hT=function(_hU){var _hV=new T(function(){var _hW=new T(function(){var _hX=new T(function(){var _hY=new T(function(){return E(E(_hU).c);});return B(A3(_8L,_hR,_hY,_hY));}),_hZ=new T(function(){var _i0=new T(function(){return E(E(_hU).a);});return B(A3(_8L,_hR,_i0,_i0));});return B(A3(_6X,_hR,_hZ,_hX));});return B(A2(_9t,_hQ,_hW));});return new F(function(){return A3(_9p,_hR,_hV,_hS);});};return E(_hT);},_i1=function(_ef,_ee){return new T2(0,_ef,_ee);},_i2=function(_i3,_i4,_i5){var _i6=new T(function(){var _i7=E(_i3),_i8=_i7.a,_i9=new T(function(){return B(A1(_i7.b,new T(function(){return B(_8J(B(_8H(E(_i7.c).a))));})));});return B(A3(_8R,_i8,new T(function(){return B(A3(_8T,B(_8F(_i8)),_i1,_i5));}),_i9));});return E(B(A1(_i4,_i6)).b);},_ia=function(_ib){var _ic=new T(function(){return E(E(_ib).a);}),_id=new T(function(){return E(E(_ib).b);}),_ie=new T(function(){var _if=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),_ig=new T(function(){var _ih=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_eb(_ih,new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_hO(new T2(0,_ig,_if)));});return function(_ii){return new F(function(){return _i2(new T3(0,_8p,_8u,new T2(0,_ic,_id)),_ie,_ii);});};},_ij=new T(function(){return B(_ia(_7V));}),_ik=new T(function(){return B(A1(_ij,_E));}),_il=new T(function(){return E(E(_ik).a);}),_im=new T(function(){return B(unCStr(",y:"));}),_in=new T1(0,_im),_io=new T(function(){return E(E(_ik).b);}),_ip=new T(function(){return B(unCStr(",z:"));}),_iq=new T1(0,_ip),_ir=new T(function(){return E(E(_ik).c);}),_is=new T(function(){return B(unCStr("})"));}),_it=new T1(0,_is),_iu=new T2(1,_it,_w),_iv=new T2(1,_ir,_iu),_iw=new T2(1,_iq,_iv),_ix=new T2(1,_io,_iw),_iy=new T2(1,_in,_ix),_iz=new T2(1,_il,_iy),_iA=new T(function(){return B(unCStr("({x:"));}),_iB=new T1(0,_iA),_iC=new T2(1,_iB,_iz),_iD=function(_iE){return E(_iE);},_iF=new T(function(){return toJSStr(B(_e(_x,_iD,_iC)));}),_iG=new T(function(){return B(_hO(_7V));}),_iH=new T(function(){return B(A1(_iG,_E));}),_iI=new T(function(){return toJSStr(B(_4(_x,_iD,_iH)));}),_iJ=function(_iK,_iL,_iM){var _iN=E(_iM);if(!_iN._){return new F(function(){return A1(_iL,_iN.a);});}else{var _iO=new T(function(){return B(_0(_iK));}),_iP=new T(function(){return B(_2(_iK));}),_iQ=function(_iR){var _iS=E(_iR);if(!_iS._){return E(_iP);}else{return new F(function(){return A2(_iO,new T(function(){return B(_iJ(_iK,_iL,_iS.a));}),new T(function(){return B(_iQ(_iS.b));}));});}};return new F(function(){return _iQ(_iN.a);});}},_iT=new T(function(){return B(unCStr("x"));}),_iU=new T1(0,_iT),_iV=new T(function(){return B(unCStr("y"));}),_iW=new T1(0,_iV),_iX=new T(function(){return B(unCStr("z"));}),_iY=new T1(0,_iX),_iZ=new T3(0,E(_iU),E(_iW),E(_iY)),_j0=new T(function(){return B(unCStr(","));}),_j1=new T1(0,_j0),_j2=new T(function(){return B(unCStr("pow("));}),_j3=new T1(0,_j2),_j4=new T(function(){return B(unCStr(")"));}),_j5=new T1(0,_j4),_j6=new T2(1,_j5,_w),_j7=function(_j8,_j9){return new T1(1,new T2(1,_j3,new T2(1,_j8,new T2(1,_j1,new T2(1,_j9,_j6)))));},_ja=new T(function(){return B(unCStr("acos("));}),_jb=new T1(0,_ja),_jc=function(_jd){return new T1(1,new T2(1,_jb,new T2(1,_jd,_j6)));},_je=new T(function(){return B(unCStr("acosh("));}),_jf=new T1(0,_je),_jg=function(_jh){return new T1(1,new T2(1,_jf,new T2(1,_jh,_j6)));},_ji=new T(function(){return B(unCStr("asin("));}),_jj=new T1(0,_ji),_jk=function(_jl){return new T1(1,new T2(1,_jj,new T2(1,_jl,_j6)));},_jm=new T(function(){return B(unCStr("asinh("));}),_jn=new T1(0,_jm),_jo=function(_jp){return new T1(1,new T2(1,_jn,new T2(1,_jp,_j6)));},_jq=new T(function(){return B(unCStr("atan("));}),_jr=new T1(0,_jq),_js=function(_jt){return new T1(1,new T2(1,_jr,new T2(1,_jt,_j6)));},_ju=new T(function(){return B(unCStr("atanh("));}),_jv=new T1(0,_ju),_jw=function(_jx){return new T1(1,new T2(1,_jv,new T2(1,_jx,_j6)));},_jy=new T(function(){return B(unCStr("cos("));}),_jz=new T1(0,_jy),_jA=function(_jB){return new T1(1,new T2(1,_jz,new T2(1,_jB,_j6)));},_jC=new T(function(){return B(unCStr("cosh("));}),_jD=new T1(0,_jC),_jE=function(_jF){return new T1(1,new T2(1,_jD,new T2(1,_jF,_j6)));},_jG=new T(function(){return B(unCStr("exp("));}),_jH=new T1(0,_jG),_jI=function(_jJ){return new T1(1,new T2(1,_jH,new T2(1,_jJ,_j6)));},_jK=new T(function(){return B(unCStr("log("));}),_jL=new T1(0,_jK),_jM=function(_jN){return new T1(1,new T2(1,_jL,new T2(1,_jN,_j6)));},_jO=new T(function(){return B(unCStr(")/log("));}),_jP=new T1(0,_jO),_jQ=function(_jR,_jS){return new T1(1,new T2(1,_jL,new T2(1,_jS,new T2(1,_jP,new T2(1,_jR,_j6)))));},_jT=new T(function(){return B(unCStr("pi"));}),_jU=new T1(0,_jT),_jV=new T(function(){return B(unCStr("sin("));}),_jW=new T1(0,_jV),_jX=function(_jY){return new T1(1,new T2(1,_jW,new T2(1,_jY,_j6)));},_jZ=new T(function(){return B(unCStr("sinh("));}),_k0=new T1(0,_jZ),_k1=function(_k2){return new T1(1,new T2(1,_k0,new T2(1,_k2,_j6)));},_k3=new T(function(){return B(unCStr("sqrt("));}),_k4=new T1(0,_k3),_k5=function(_k6){return new T1(1,new T2(1,_k4,new T2(1,_k6,_j6)));},_k7=new T(function(){return B(unCStr("tan("));}),_k8=new T1(0,_k7),_k9=function(_ka){return new T1(1,new T2(1,_k8,new T2(1,_ka,_j6)));},_kb=new T(function(){return B(unCStr("tanh("));}),_kc=new T1(0,_kb),_kd=function(_ke){return new T1(1,new T2(1,_kc,new T2(1,_ke,_j6)));},_kf=new T(function(){return B(unCStr("("));}),_kg=new T1(0,_kf),_kh=new T(function(){return B(unCStr(")/("));}),_ki=new T1(0,_kh),_kj=function(_kk,_kl){return new T1(1,new T2(1,_kg,new T2(1,_kk,new T2(1,_ki,new T2(1,_kl,_j6)))));},_km=function(_kn){return new T1(0,new T(function(){var _ko=E(_kn),_kp=jsShow(B(_6y(_ko.a,_ko.b)));return fromJSStr(_kp);}));},_kq=new T(function(){return B(unCStr("1./("));}),_kr=new T1(0,_kq),_ks=function(_kt){return new T1(1,new T2(1,_kr,new T2(1,_kt,_j6)));},_ku=new T(function(){return B(unCStr(")+("));}),_kv=new T1(0,_ku),_kw=function(_kx,_ky){return new T1(1,new T2(1,_kg,new T2(1,_kx,new T2(1,_kv,new T2(1,_ky,_j6)))));},_kz=new T(function(){return B(unCStr("-("));}),_kA=new T1(0,_kz),_kB=function(_kC){return new T1(1,new T2(1,_kA,new T2(1,_kC,_j6)));},_kD=new T(function(){return B(unCStr(")*("));}),_kE=new T1(0,_kD),_kF=function(_kG,_kH){return new T1(1,new T2(1,_kg,new T2(1,_kG,new T2(1,_kE,new T2(1,_kH,_j6)))));},_kI=function(_kJ,_kK){return new F(function(){return A3(_6X,_kL,_kJ,new T(function(){return B(A2(_6Z,_kL,_kK));}));});},_kM=new T(function(){return B(unCStr("abs("));}),_kN=new T1(0,_kM),_kO=function(_kP){return new T1(1,new T2(1,_kN,new T2(1,_kP,_j6)));},_kQ=new T(function(){return B(unCStr("."));}),_kR=function(_kS){return new T1(0,new T(function(){return B(_n(B(_7i(0,_kS,_w)),_kQ));}));},_kT=new T(function(){return B(unCStr("sign("));}),_kU=new T1(0,_kT),_kV=function(_kW){return new T1(1,new T2(1,_kU,new T2(1,_kW,_j6)));},_kL=new T(function(){return {_:0,a:_kw,b:_kI,c:_kF,d:_kB,e:_kO,f:_kV,g:_kR};}),_kX=new T4(0,_kL,_kj,_ks,_km),_kY={_:0,a:_kX,b:_jU,c:_jI,d:_jM,e:_k5,f:_j7,g:_jQ,h:_jX,i:_jA,j:_k9,k:_jk,l:_jc,m:_js,n:_k1,o:_jE,p:_kd,q:_jo,r:_jg,s:_jw},_kZ=new T(function(){return B(unCStr("(/=) is not defined"));}),_l0=new T(function(){return B(err(_kZ));}),_l1=new T(function(){return B(unCStr("(==) is not defined"));}),_l2=new T(function(){return B(err(_l1));}),_l3=new T2(0,_l2,_l0),_l4=new T(function(){return B(unCStr("(<) is not defined"));}),_l5=new T(function(){return B(err(_l4));}),_l6=new T(function(){return B(unCStr("(<=) is not defined"));}),_l7=new T(function(){return B(err(_l6));}),_l8=new T(function(){return B(unCStr("(>) is not defined"));}),_l9=new T(function(){return B(err(_l8));}),_la=new T(function(){return B(unCStr("(>=) is not defined"));}),_lb=new T(function(){return B(err(_la));}),_lc=new T(function(){return B(unCStr("compare is not defined"));}),_ld=new T(function(){return B(err(_lc));}),_le=new T(function(){return B(unCStr("max("));}),_lf=new T1(0,_le),_lg=function(_lh,_li){return new T1(1,new T2(1,_lf,new T2(1,_lh,new T2(1,_j1,new T2(1,_li,_j6)))));},_lj=new T(function(){return B(unCStr("min("));}),_lk=new T1(0,_lj),_ll=function(_lm,_ln){return new T1(1,new T2(1,_lk,new T2(1,_lm,new T2(1,_j1,new T2(1,_ln,_j6)))));},_lo={_:0,a:_l3,b:_ld,c:_l5,d:_l7,e:_l9,f:_lb,g:_lg,h:_ll},_lp=new T2(0,_kY,_lo),_lq=new T(function(){return B(_hO(_lp));}),_lr=new T(function(){return B(A1(_lq,_iZ));}),_ls=new T(function(){return toJSStr(B(_iJ(_x,_iD,_lr)));}),_lt=new T(function(){return eval("__strict(compile)");}),_lu=new T(function(){return toJSStr(E(_iV));}),_lv=function(_lw,_lx,_ly){var _lz=new T(function(){return B(_0(_lw));}),_lA=new T(function(){return B(_2(_lw));}),_lB=function(_lC){var _lD=E(_lC);if(!_lD._){return E(_lA);}else{return new F(function(){return A2(_lz,new T(function(){return B(_iJ(_lw,_lx,_lD.a));}),new T(function(){return B(_lB(_lD.b));}));});}};return new F(function(){return _lB(_ly);});},_lE=new T(function(){return B(unCStr("vec3("));}),_lF=new T1(0,_lE),_lG=new T(function(){return B(_7i(0,_8r,_w));}),_lH=new T(function(){return B(_n(_lG,_kQ));}),_lI=new T1(0,_lH),_lJ=new T(function(){return B(_7i(0,_8q,_w));}),_lK=new T(function(){return B(_n(_lJ,_kQ));}),_lL=new T1(0,_lK),_lM=new T2(1,_lL,_w),_lN=new T2(1,_lI,_lM),_lO=function(_lP,_lQ){var _lR=E(_lQ);return (_lR._==0)?__Z:new T2(1,_lP,new T2(1,_lR.a,new T(function(){return B(_lO(_lP,_lR.b));})));},_lS=new T(function(){return B(_lO(_j1,_lN));}),_lT=new T2(1,_lL,_lS),_lU=new T1(1,_lT),_lV=new T2(1,_lU,_j6),_lW=new T2(1,_lF,_lV),_lX=new T(function(){return toJSStr(B(_lv(_x,_iD,_lW)));}),_lY=function(_lZ,_m0){while(1){var _m1=E(_lZ);if(!_m1._){return E(_m0);}else{var _m2=_m0+1|0;_lZ=_m1.b;_m0=_m2;continue;}}},_m3=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_m4=new T(function(){return B(err(_m3));}),_m5=0,_m6=new T3(0,E(_m5),E(_m5),E(_m5)),_m7=new T(function(){return B(unCStr("Negative exponent"));}),_m8=new T(function(){return B(err(_m7));}),_m9=function(_ma,_mb,_mc){while(1){if(!(_mb%2)){var _md=_ma*_ma,_me=quot(_mb,2);_ma=_md;_mb=_me;continue;}else{var _mf=E(_mb);if(_mf==1){return _ma*_mc;}else{var _md=_ma*_ma,_mg=_ma*_mc;_ma=_md;_mb=quot(_mf-1|0,2);_mc=_mg;continue;}}}},_mh=function(_mi,_mj){while(1){if(!(_mj%2)){var _mk=_mi*_mi,_ml=quot(_mj,2);_mi=_mk;_mj=_ml;continue;}else{var _mm=E(_mj);if(_mm==1){return E(_mi);}else{return new F(function(){return _m9(_mi*_mi,quot(_mm-1|0,2),_mi);});}}}},_mn=function(_mo){var _mp=E(_mo);return new F(function(){return Math.log(_mp+(_mp+1)*Math.sqrt((_mp-1)/(_mp+1)));});},_mq=function(_mr){var _ms=E(_mr);return new F(function(){return Math.log(_ms+Math.sqrt(1+_ms*_ms));});},_mt=function(_mu){var _mv=E(_mu);return 0.5*Math.log((1+_mv)/(1-_mv));},_mw=function(_mx,_my){return Math.log(E(_my))/Math.log(E(_mx));},_mz=3.141592653589793,_mA=function(_mB){var _mC=E(_mB);return new F(function(){return _6y(_mC.a,_mC.b);});},_mD=function(_mE){return 1/E(_mE);},_mF=function(_mG){var _mH=E(_mG),_mI=E(_mH);return (_mI==0)?E(_6x):(_mI<=0)? -_mI:E(_mH);},_mJ=function(_mK){var _mL=E(_mK);if(!_mL._){return _mL.a;}else{return new F(function(){return I_toNumber(_mL.a);});}},_mM=function(_mN){return new F(function(){return _mJ(_mN);});},_mO=1,_mP=-1,_mQ=function(_mR){var _mS=E(_mR);return (_mS<=0)?(_mS>=0)?E(_mS):E(_mP):E(_mO);},_mT=function(_mU,_mV){return E(_mU)-E(_mV);},_mW=function(_mX){return  -E(_mX);},_mY=function(_mZ,_n0){return E(_mZ)+E(_n0);},_n1=function(_n2,_n3){return E(_n2)*E(_n3);},_n4={_:0,a:_mY,b:_mT,c:_n1,d:_mW,e:_mF,f:_mQ,g:_mM},_n5=function(_n6,_n7){return E(_n6)/E(_n7);},_n8=new T4(0,_n4,_n5,_mD,_mA),_n9=function(_na){return new F(function(){return Math.acos(E(_na));});},_nb=function(_nc){return new F(function(){return Math.asin(E(_nc));});},_nd=function(_ne){return new F(function(){return Math.atan(E(_ne));});},_nf=function(_ng){return new F(function(){return Math.cos(E(_ng));});},_nh=function(_ni){return new F(function(){return cosh(E(_ni));});},_nj=function(_nk){return new F(function(){return Math.exp(E(_nk));});},_nl=function(_nm){return new F(function(){return Math.log(E(_nm));});},_nn=function(_no,_np){return new F(function(){return Math.pow(E(_no),E(_np));});},_nq=function(_nr){return new F(function(){return Math.sin(E(_nr));});},_ns=function(_nt){return new F(function(){return sinh(E(_nt));});},_nu=function(_nv){return new F(function(){return Math.sqrt(E(_nv));});},_nw=function(_nx){return new F(function(){return Math.tan(E(_nx));});},_ny=function(_nz){return new F(function(){return tanh(E(_nz));});},_nA={_:0,a:_n8,b:_mz,c:_nj,d:_nl,e:_nu,f:_nn,g:_mw,h:_nq,i:_nf,j:_nw,k:_nb,l:_n9,m:_nd,n:_ns,o:_nh,p:_ny,q:_mq,r:_mn,s:_mt},_nB=function(_nC,_nD){return (E(_nC)!=E(_nD))?true:false;},_nE=function(_nF,_nG){return E(_nF)==E(_nG);},_nH=new T2(0,_nE,_nB),_nI=function(_nJ,_nK){return E(_nJ)<E(_nK);},_nL=function(_nM,_nN){return E(_nM)<=E(_nN);},_nO=function(_nP,_nQ){return E(_nP)>E(_nQ);},_nR=function(_nS,_nT){return E(_nS)>=E(_nT);},_nU=function(_nV,_nW){var _nX=E(_nV),_nY=E(_nW);return (_nX>=_nY)?(_nX!=_nY)?2:1:0;},_nZ=function(_o0,_o1){var _o2=E(_o0),_o3=E(_o1);return (_o2>_o3)?E(_o2):E(_o3);},_o4=function(_o5,_o6){var _o7=E(_o5),_o8=E(_o6);return (_o7>_o8)?E(_o8):E(_o7);},_o9={_:0,a:_nH,b:_nU,c:_nI,d:_nL,e:_nO,f:_nR,g:_nZ,h:_o4},_oa="dz",_ob="wy",_oc="wx",_od="dy",_oe="dx",_of="t",_og="a",_oh="r",_oi="ly",_oj="lx",_ok="wz",_ol=0,_om=function(_on){var _oo=__new(),_op=_oo,_oq=function(_or,_){while(1){var _os=E(_or);if(!_os._){return _ol;}else{var _ot=E(_os.a),_ou=__set(_op,E(_ot.a),E(_ot.b));_or=_os.b;continue;}}},_ov=B(_oq(_on,_));return E(_op);},_ow=function(_ox,_oy,_oz,_oA,_oB,_oC,_oD,_oE,_oF){return new F(function(){return _om(new T2(1,new T2(0,_oc,_ox),new T2(1,new T2(0,_ob,_oy),new T2(1,new T2(0,_ok,_oz),new T2(1,new T2(0,_oj,_oA*_oB*Math.cos(_oC)),new T2(1,new T2(0,_oi,_oA*_oB*Math.sin(_oC)),new T2(1,new T2(0,_oh,_oA),new T2(1,new T2(0,_og,_oB),new T2(1,new T2(0,_of,_oC),new T2(1,new T2(0,_oe,_oD),new T2(1,new T2(0,_od,_oE),new T2(1,new T2(0,_oa,_oF),_w))))))))))));});},_oG=function(_oH){var _oI=E(_oH),_oJ=E(_oI.a),_oK=E(_oI.b),_oL=E(_oI.d);return new F(function(){return _ow(_oJ.a,_oJ.b,_oJ.c,E(_oK.a),E(_oK.b),E(_oI.c),_oL.a,_oL.b,_oL.c);});},_oM=function(_oN,_oO){var _oP=E(_oO);return (_oP._==0)?__Z:new T2(1,new T(function(){return B(A1(_oN,_oP.a));}),new T(function(){return B(_oM(_oN,_oP.b));}));},_oQ=function(_oR,_oS,_oT){var _oU=__lst2arr(B(_oM(_oG,new T2(1,_oR,new T2(1,_oS,new T2(1,_oT,_w))))));return E(_oU);},_oV=function(_oW){var _oX=E(_oW);return new F(function(){return _oQ(_oX.a,_oX.b,_oX.c);});},_oY=new T2(0,_nA,_o9),_oZ=function(_p0,_p1,_p2,_p3,_p4,_p5,_p6){var _p7=B(_8J(B(_8H(_p0)))),_p8=new T(function(){return B(A3(_6X,_p7,new T(function(){return B(A3(_8L,_p7,_p1,_p4));}),new T(function(){return B(A3(_8L,_p7,_p2,_p5));})));});return new F(function(){return A3(_6X,_p7,_p8,new T(function(){return B(A3(_8L,_p7,_p3,_p6));}));});},_p9=function(_pa,_pb,_pc,_pd){var _pe=B(_8H(_pa)),_pf=new T(function(){return B(A2(_9t,_pa,new T(function(){return B(_oZ(_pa,_pb,_pc,_pd,_pb,_pc,_pd));})));});return new T3(0,B(A3(_8P,_pe,_pb,_pf)),B(A3(_8P,_pe,_pc,_pf)),B(A3(_8P,_pe,_pd,_pf)));},_pg=function(_ph,_pi,_pj,_pk,_pl,_pm,_pn){var _po=B(_8L(_ph));return new T3(0,B(A1(B(A1(_po,_pi)),_pl)),B(A1(B(A1(_po,_pj)),_pm)),B(A1(B(A1(_po,_pk)),_pn)));},_pp=function(_pq,_pr,_ps,_pt,_pu,_pv,_pw){var _px=B(_6X(_pq));return new T3(0,B(A1(B(A1(_px,_pr)),_pu)),B(A1(B(A1(_px,_ps)),_pv)),B(A1(B(A1(_px,_pt)),_pw)));},_py=function(_pz,_pA){var _pB=new T(function(){return E(E(_pz).a);}),_pC=new T(function(){var _pD=E(_pA),_pE=new T(function(){return B(_8J(new T(function(){return B(_8H(_pB));})));}),_pF=B(A2(_8s,_pE,_8q));return new T3(0,E(_pF),E(B(A2(_8s,_pE,_8r))),E(_pF));}),_pG=new T(function(){var _pH=E(_pC),_pI=B(_p9(_pB,_pH.a,_pH.b,_pH.c));return new T3(0,E(_pI.a),E(_pI.b),E(_pI.c));}),_pJ=new T(function(){var _pK=E(_pA),_pL=_pK.b,_pM=E(_pG),_pN=B(_8H(_pB)),_pO=new T(function(){return B(A2(_9t,_pB,new T(function(){var _pP=E(_pC),_pQ=_pP.a,_pR=_pP.b,_pS=_pP.c;return B(_oZ(_pB,_pQ,_pR,_pS,_pQ,_pR,_pS));})));}),_pT=B(A3(_8P,_pN,_pL,_pO)),_pU=B(_8J(_pN)),_pV=B(_pg(_pU,_pM.a,_pM.b,_pM.c,_pT,_pT,_pT)),_pW=B(_6Z(_pU)),_pX=B(_pp(_pU,_pK.a,_pL,_pK.c,B(A1(_pW,_pV.a)),B(A1(_pW,_pV.b)),B(A1(_pW,_pV.c))));return new T3(0,E(_pX.a),E(_pX.b),E(_pX.c));});return new T2(0,_pJ,_pG);},_pY=function(_pZ){return E(E(_pZ).a);},_q0=function(_q1,_q2,_q3,_q4,_q5,_q6,_q7){var _q8=B(_oZ(_q1,_q5,_q6,_q7,_q2,_q3,_q4)),_q9=B(_8J(B(_8H(_q1)))),_qa=B(_pg(_q9,_q5,_q6,_q7,_q8,_q8,_q8)),_qb=B(_6Z(_q9));return new F(function(){return _pp(_q9,_q2,_q3,_q4,B(A1(_qb,_qa.a)),B(A1(_qb,_qa.b)),B(A1(_qb,_qa.c)));});},_qc=function(_qd){return E(E(_qd).a);},_qe=function(_qf,_qg,_qh,_qi){var _qj=new T(function(){var _qk=E(_qi),_ql=E(_qh),_qm=B(_q0(_qf,_qk.a,_qk.b,_qk.c,_ql.a,_ql.b,_ql.c));return new T3(0,E(_qm.a),E(_qm.b),E(_qm.c));}),_qn=new T(function(){return B(A2(_9t,_qf,new T(function(){var _qo=E(_qj),_qp=_qo.a,_qq=_qo.b,_qr=_qo.c;return B(_oZ(_qf,_qp,_qq,_qr,_qp,_qq,_qr));})));});if(!B(A3(_qc,B(_pY(_qg)),_qn,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_qf)))),_8q));})))){var _qs=E(_qj),_qt=B(_p9(_qf,_qs.a,_qs.b,_qs.c)),_qu=B(A2(_9t,_qf,new T(function(){var _qv=E(_qi),_qw=_qv.a,_qx=_qv.b,_qy=_qv.c;return B(_oZ(_qf,_qw,_qx,_qy,_qw,_qx,_qy));}))),_qz=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_qf));})));})));return new T3(0,B(A1(B(A1(_qz,_qt.a)),_qu)),B(A1(B(A1(_qz,_qt.b)),_qu)),B(A1(B(A1(_qz,_qt.c)),_qu)));}else{var _qA=B(A2(_8s,B(_8J(B(_8H(_qf)))),_8q));return new T3(0,_qA,_qA,_qA);}},_qB=function(_qC,_qD){while(1){var _qE=E(_qC);if(!_qE._){return E(_qD);}else{var _qF=_qE.b,_qG=E(_qE.a);if(_qD>_qG){_qC=_qF;continue;}else{_qC=_qF;_qD=_qG;continue;}}}},_qH=new T(function(){var _qI=eval("angleCount"),_qJ=Number(_qI);return jsTrunc(_qJ);}),_qK=new T(function(){return E(_qH);}),_qL=new T(function(){return B(unCStr(": empty list"));}),_qM=new T(function(){return B(unCStr("Prelude."));}),_qN=function(_qO){return new F(function(){return err(B(_n(_qM,new T(function(){return B(_n(_qO,_qL));},1))));});},_qP=new T(function(){return B(unCStr("head"));}),_qQ=new T(function(){return B(_qN(_qP));}),_qR=function(_qS,_qT,_qU){var _qV=E(_qS);if(!_qV._){return __Z;}else{var _qW=E(_qT);if(!_qW._){return __Z;}else{var _qX=_qW.a,_qY=E(_qU);if(!_qY._){return __Z;}else{var _qZ=E(_qY.a),_r0=_qZ.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_qV.a),E(_qX),E(_r0));}),new T2(1,new T(function(){return new T3(0,E(_qX),E(_r0),E(_qZ.b));}),_w)),new T(function(){return B(_qR(_qV.b,_qW.b,_qY.b));},1));});}}}},_r1=new T(function(){return B(unCStr("tail"));}),_r2=new T(function(){return B(_qN(_r1));}),_r3=function(_r4,_r5){var _r6=E(_r4);if(!_r6._){return __Z;}else{var _r7=E(_r5);return (_r7._==0)?__Z:new T2(1,new T2(0,_r6.a,_r7.a),new T(function(){return B(_r3(_r6.b,_r7.b));}));}},_r8=function(_r9,_ra){var _rb=E(_r9);if(!_rb._){return __Z;}else{var _rc=E(_ra);if(!_rc._){return __Z;}else{var _rd=E(_rb.a),_re=_rd.b,_rf=E(_rc.a).b,_rg=new T(function(){var _rh=new T(function(){return B(_r3(_rf,new T(function(){var _ri=E(_rf);if(!_ri._){return E(_r2);}else{return E(_ri.b);}},1)));},1);return B(_qR(_re,new T(function(){var _rj=E(_re);if(!_rj._){return E(_r2);}else{return E(_rj.b);}},1),_rh));});return new F(function(){return _n(new T2(1,new T(function(){var _rk=E(_re);if(!_rk._){return E(_qQ);}else{var _rl=E(_rf);if(!_rl._){return E(_qQ);}else{return new T3(0,E(_rd.a),E(_rk.a),E(_rl.a));}}}),_rg),new T(function(){return B(_r8(_rb.b,_rc.b));},1));});}}},_rm=new T(function(){return 6.283185307179586/E(_qK);}),_rn=new T(function(){return E(_qK)-1;}),_ro=new T1(0,1),_rp=function(_rq,_rr){var _rs=E(_rr),_rt=new T(function(){var _ru=B(_8J(_rq)),_rv=B(_rp(_rq,B(A3(_6X,_ru,_rs,new T(function(){return B(A2(_8s,_ru,_ro));})))));return new T2(1,_rv.a,_rv.b);});return new T2(0,_rs,_rt);},_rw=function(_rx){return E(E(_rx).d);},_ry=new T1(0,2),_rz=function(_rA,_rB){var _rC=E(_rB);if(!_rC._){return __Z;}else{var _rD=_rC.a;return (!B(A1(_rA,_rD)))?__Z:new T2(1,_rD,new T(function(){return B(_rz(_rA,_rC.b));}));}},_rE=function(_rF,_rG,_rH,_rI){var _rJ=B(_rp(_rG,_rH)),_rK=new T(function(){var _rL=B(_8J(_rG)),_rM=new T(function(){return B(A3(_8P,_rG,new T(function(){return B(A2(_8s,_rL,_ro));}),new T(function(){return B(A2(_8s,_rL,_ry));})));});return B(A3(_6X,_rL,_rI,_rM));});return new F(function(){return _rz(function(_rN){return new F(function(){return A3(_rw,_rF,_rN,_rK);});},new T2(1,_rJ.a,_rJ.b));});},_rO=new T(function(){return B(_rE(_o9,_n8,_m5,_rn));}),_rP=function(_rQ,_rR){while(1){var _rS=E(_rQ);if(!_rS._){return E(_rR);}else{_rQ=_rS.b;_rR=_rS.a;continue;}}},_rT=new T(function(){return B(unCStr("last"));}),_rU=new T(function(){return B(_qN(_rT));}),_rV=function(_rW){return new F(function(){return _rP(_rW,_rU);});},_rX=function(_rY){return new F(function(){return _rV(E(_rY).b);});},_rZ=new T(function(){return B(unCStr("maximum"));}),_s0=new T(function(){return B(_qN(_rZ));}),_s1=new T(function(){var _s2=eval("proceedCount"),_s3=Number(_s2);return jsTrunc(_s3);}),_s4=new T(function(){return E(_s1);}),_s5=1,_s6=new T(function(){return B(_rE(_o9,_n8,_s5,_s4));}),_s7=function(_s8,_s9,_sa,_sb,_sc,_sd,_se,_sf,_sg,_sh,_si,_sj,_sk,_sl){var _sm=new T(function(){var _sn=new T(function(){var _so=E(_sh),_sp=E(_sl),_sq=E(_sk),_sr=E(_si),_ss=E(_sj),_st=E(_sg);return new T3(0,_so*_sp-_sq*_sr,_sr*_ss-_sp*_st,_st*_sq-_ss*_so);}),_su=function(_sv){var _sw=new T(function(){var _sx=E(_sv)/E(_qK);return (_sx+_sx)*3.141592653589793;}),_sy=new T(function(){return B(A1(_s8,_sw));}),_sz=new T(function(){var _sA=new T(function(){var _sB=E(_sy)/E(_s4);return new T3(0,E(_sB),E(_sB),E(_sB));}),_sC=function(_sD,_sE){var _sF=E(_sD);if(!_sF._){return new T2(0,_w,_sE);}else{var _sG=new T(function(){var _sH=B(_py(_oY,new T(function(){var _sI=E(_sE),_sJ=E(_sI.a),_sK=E(_sI.b),_sL=E(_sA);return new T3(0,E(_sJ.a)+E(_sK.a)*E(_sL.a),E(_sJ.b)+E(_sK.b)*E(_sL.b),E(_sJ.c)+E(_sK.c)*E(_sL.c));}))),_sM=_sH.a,_sN=new T(function(){var _sO=E(_sH.b),_sP=E(E(_sE).b),_sQ=B(_q0(_nA,_sP.a,_sP.b,_sP.c,_sO.a,_sO.b,_sO.c)),_sR=B(_p9(_nA,_sQ.a,_sQ.b,_sQ.c));return new T3(0,E(_sR.a),E(_sR.b),E(_sR.c));});return new T2(0,new T(function(){var _sS=E(_sy),_sT=E(_sw);return new T4(0,E(_sM),E(new T2(0,E(_sF.a)/E(_s4),E(_sS))),E(_sT),E(_sN));}),new T2(0,_sM,_sN));}),_sU=new T(function(){var _sV=B(_sC(_sF.b,new T(function(){return E(E(_sG).b);})));return new T2(0,_sV.a,_sV.b);});return new T2(0,new T2(1,new T(function(){return E(E(_sG).a);}),new T(function(){return E(E(_sU).a);})),new T(function(){return E(E(_sU).b);}));}},_sW=function(_sX,_sY,_sZ,_t0,_t1){var _t2=E(_sX);if(!_t2._){return new T2(0,_w,new T2(0,new T3(0,E(_sY),E(_sZ),E(_t0)),_t1));}else{var _t3=new T(function(){var _t4=B(_py(_oY,new T(function(){var _t5=E(_t1),_t6=E(_sA);return new T3(0,E(_sY)+E(_t5.a)*E(_t6.a),E(_sZ)+E(_t5.b)*E(_t6.b),E(_t0)+E(_t5.c)*E(_t6.c));}))),_t7=_t4.a,_t8=new T(function(){var _t9=E(_t4.b),_ta=E(_t1),_tb=B(_q0(_nA,_ta.a,_ta.b,_ta.c,_t9.a,_t9.b,_t9.c)),_tc=B(_p9(_nA,_tb.a,_tb.b,_tb.c));return new T3(0,E(_tc.a),E(_tc.b),E(_tc.c));});return new T2(0,new T(function(){var _td=E(_sy),_te=E(_sw);return new T4(0,E(_t7),E(new T2(0,E(_t2.a)/E(_s4),E(_td))),E(_te),E(_t8));}),new T2(0,_t7,_t8));}),_tf=new T(function(){var _tg=B(_sC(_t2.b,new T(function(){return E(E(_t3).b);})));return new T2(0,_tg.a,_tg.b);});return new T2(0,new T2(1,new T(function(){return E(E(_t3).a);}),new T(function(){return E(E(_tf).a);})),new T(function(){return E(E(_tf).b);}));}};return E(B(_sW(_s6,_sb,_sc,_sd,new T(function(){var _th=E(_sn),_ti=E(_sw)+_se,_tj=Math.cos(_ti),_tk=Math.sin(_ti);return new T3(0,E(_sg)*_tj+E(_th.a)*_tk,E(_sh)*_tj+E(_th.b)*_tk,E(_si)*_tj+E(_th.c)*_tk);}))).a);});return new T2(0,new T(function(){var _tl=E(_sy),_tm=E(_sw);return new T4(0,E(new T3(0,E(_sb),E(_sc),E(_sd))),E(new T2(0,E(_m5),E(_tl))),E(_tm),E(_m6));}),_sz);};return B(_oM(_su,_rO));}),_tn=new T(function(){var _to=function(_tp){return new F(function(){return A1(_s8,new T(function(){return B(_n1(_tp,_rm));}));});},_tq=B(_oM(_to,_rO));if(!_tq._){return E(_s0);}else{return B(_qB(_tq.b,E(_tq.a)));}}),_tr=new T(function(){var _ts=new T(function(){var _tt=B(_n(_sm,new T2(1,new T(function(){var _tu=E(_sm);if(!_tu._){return E(_qQ);}else{return E(_tu.a);}}),_w)));if(!_tt._){return E(_r2);}else{return E(_tt.b);}},1);return B(_r8(_sm,_ts));});return new T3(0,_tr,new T(function(){return B(_oM(_rX,_sm));}),_tn);},_tv=function(_tw,_tx,_ty,_tz,_tA,_tB,_tC,_tD,_tE,_tF,_tG,_tH,_tI,_tJ,_tK,_tL,_tM,_tN){var _tO=B(_py(_oY,new T3(0,E(_tz),E(_tA),E(_tB)))),_tP=_tO.b,_tQ=E(_tO.a),_tR=B(_qe(_nA,_o9,_tP,new T3(0,E(_tD),E(_tE),E(_tF)))),_tS=E(_tP),_tT=_tS.a,_tU=_tS.b,_tV=_tS.c,_tW=B(_q0(_nA,_tH,_tI,_tJ,_tT,_tU,_tV)),_tX=B(_p9(_nA,_tW.a,_tW.b,_tW.c)),_tY=_tX.a,_tZ=_tX.b,_u0=_tX.c,_u1=E(_tC),_u2=new T2(0,E(new T3(0,E(_tR.a),E(_tR.b),E(_tR.c))),E(_tG)),_u3=B(_s7(_tw,_tx,_ty,_tQ.a,_tQ.b,_tQ.c,_u1,_u2,_tY,_tZ,_u0,_tT,_tU,_tV)),_u4=__lst2arr(B(_oM(_oV,_u3.a))),_u5=__lst2arr(B(_oM(_oG,_u3.b)));return {_:0,a:_tw,b:_tx,c:_ty,d:new T2(0,E(_tQ),E(_u1)),e:_u2,f:new T3(0,E(_tY),E(_tZ),E(_u0)),g:_tS,h:_u4,i:_u5,j:E(_u3.c)};},_u6=-4,_u7=new T3(0,E(_m5),E(_m5),E(_u6)),_u8=function(_u9){return E(_u7);},_ua=function(_){return new F(function(){return __jsNull();});},_ub=function(_uc){var _ud=B(A1(_uc,_));return E(_ud);},_ue=new T(function(){return B(_ub(_ua));}),_uf=function(_ug,_uh,_ui,_uj,_uk,_ul,_um,_un,_uo,_up,_uq,_ur,_us){var _ut=function(_uu){var _uv=E(_rm),_uw=2+_uu|0,_ux=_uw-1|0,_uy=(2+_uu)*(1+_uu),_uz=E(_rO);if(!_uz._){return _uv*0;}else{var _uA=_uz.a,_uB=_uz.b,_uC=B(A1(_ug,new T(function(){return 6.283185307179586*E(_uA)/E(_qK);}))),_uD=B(A1(_ug,new T(function(){return 6.283185307179586*(E(_uA)+1)/E(_qK);})));if(_uC!=_uD){if(_uw>=0){var _uE=E(_uw);if(!_uE){var _uF=function(_uG,_uH){while(1){var _uI=B((function(_uJ,_uK){var _uL=E(_uJ);if(!_uL._){return E(_uK);}else{var _uM=_uL.a,_uN=_uL.b,_uO=B(A1(_ug,new T(function(){return 6.283185307179586*E(_uM)/E(_qK);}))),_uP=B(A1(_ug,new T(function(){return 6.283185307179586*(E(_uM)+1)/E(_qK);})));if(_uO!=_uP){var _uQ=_uK+0/(_uO-_uP)/_uy;_uG=_uN;_uH=_uQ;return __continue;}else{if(_ux>=0){var _uR=E(_ux);if(!_uR){var _uQ=_uK+_uw/_uy;_uG=_uN;_uH=_uQ;return __continue;}else{var _uQ=_uK+_uw*B(_mh(_uO,_uR))/_uy;_uG=_uN;_uH=_uQ;return __continue;}}else{return E(_m8);}}}})(_uG,_uH));if(_uI!=__continue){return _uI;}}};return _uv*B(_uF(_uB,0/(_uC-_uD)/_uy));}else{var _uS=function(_uT,_uU){while(1){var _uV=B((function(_uW,_uX){var _uY=E(_uW);if(!_uY._){return E(_uX);}else{var _uZ=_uY.a,_v0=_uY.b,_v1=B(A1(_ug,new T(function(){return 6.283185307179586*E(_uZ)/E(_qK);}))),_v2=B(A1(_ug,new T(function(){return 6.283185307179586*(E(_uZ)+1)/E(_qK);})));if(_v1!=_v2){if(_uE>=0){var _v3=_uX+(B(_mh(_v1,_uE))-B(_mh(_v2,_uE)))/(_v1-_v2)/_uy;_uT=_v0;_uU=_v3;return __continue;}else{return E(_m8);}}else{if(_ux>=0){var _v4=E(_ux);if(!_v4){var _v3=_uX+_uw/_uy;_uT=_v0;_uU=_v3;return __continue;}else{var _v3=_uX+_uw*B(_mh(_v1,_v4))/_uy;_uT=_v0;_uU=_v3;return __continue;}}else{return E(_m8);}}}})(_uT,_uU));if(_uV!=__continue){return _uV;}}};return _uv*B(_uS(_uB,(B(_mh(_uC,_uE))-B(_mh(_uD,_uE)))/(_uC-_uD)/_uy));}}else{return E(_m8);}}else{if(_ux>=0){var _v5=E(_ux);if(!_v5){var _v6=function(_v7,_v8){while(1){var _v9=B((function(_va,_vb){var _vc=E(_va);if(!_vc._){return E(_vb);}else{var _vd=_vc.a,_ve=_vc.b,_vf=B(A1(_ug,new T(function(){return 6.283185307179586*E(_vd)/E(_qK);}))),_vg=B(A1(_ug,new T(function(){return 6.283185307179586*(E(_vd)+1)/E(_qK);})));if(_vf!=_vg){if(_uw>=0){var _vh=E(_uw);if(!_vh){var _vi=_vb+0/(_vf-_vg)/_uy;_v7=_ve;_v8=_vi;return __continue;}else{var _vi=_vb+(B(_mh(_vf,_vh))-B(_mh(_vg,_vh)))/(_vf-_vg)/_uy;_v7=_ve;_v8=_vi;return __continue;}}else{return E(_m8);}}else{var _vi=_vb+_uw/_uy;_v7=_ve;_v8=_vi;return __continue;}}})(_v7,_v8));if(_v9!=__continue){return _v9;}}};return _uv*B(_v6(_uB,_uw/_uy));}else{var _vj=function(_vk,_vl){while(1){var _vm=B((function(_vn,_vo){var _vp=E(_vn);if(!_vp._){return E(_vo);}else{var _vq=_vp.a,_vr=_vp.b,_vs=B(A1(_ug,new T(function(){return 6.283185307179586*E(_vq)/E(_qK);}))),_vt=B(A1(_ug,new T(function(){return 6.283185307179586*(E(_vq)+1)/E(_qK);})));if(_vs!=_vt){if(_uw>=0){var _vu=E(_uw);if(!_vu){var _vv=_vo+0/(_vs-_vt)/_uy;_vk=_vr;_vl=_vv;return __continue;}else{var _vv=_vo+(B(_mh(_vs,_vu))-B(_mh(_vt,_vu)))/(_vs-_vt)/_uy;_vk=_vr;_vl=_vv;return __continue;}}else{return E(_m8);}}else{if(_v5>=0){var _vv=_vo+_uw*B(_mh(_vs,_v5))/_uy;_vk=_vr;_vl=_vv;return __continue;}else{return E(_m8);}}}})(_vk,_vl));if(_vm!=__continue){return _vm;}}};return _uv*B(_vj(_uB,_uw*B(_mh(_uC,_v5))/_uy));}}else{return E(_m8);}}}},_vw=E(_ue),_vx=1/(B(_ut(1))*_uh);return new F(function(){return _tv(_ug,_u8,new T2(0,E(new T3(0,E(_vx),E(_vx),E(_vx))),1/(B(_ut(3))*_uh)),_ui,_uj,_uk,_ul,_um,_un,_uo,_up,_uq,_ur,_us,_m6,_vw,_vw,0);});},_vy=1,_vz=0,_vA=function(_vB){var _vC=I_decodeDouble(_vB);return new T2(0,new T1(1,_vC.b),_vC.a);},_vD=function(_vE){return new T1(0,_vE);},_vF=function(_vG){var _vH=hs_intToInt64(2147483647),_vI=hs_leInt64(_vG,_vH);if(!_vI){return new T1(1,I_fromInt64(_vG));}else{var _vJ=hs_intToInt64(-2147483648),_vK=hs_geInt64(_vG,_vJ);if(!_vK){return new T1(1,I_fromInt64(_vG));}else{var _vL=hs_int64ToInt(_vG);return new F(function(){return _vD(_vL);});}}},_vM=new T(function(){var _vN=newByteArr(256),_vO=_vN,_=_vO["v"]["i8"][0]=8,_vP=function(_vQ,_vR,_vS,_){while(1){if(_vS>=256){if(_vQ>=256){return E(_);}else{var _vT=imul(2,_vQ)|0,_vU=_vR+1|0,_vV=_vQ;_vQ=_vT;_vR=_vU;_vS=_vV;continue;}}else{var _=_vO["v"]["i8"][_vS]=_vR,_vV=_vS+_vQ|0;_vS=_vV;continue;}}},_=B(_vP(2,0,1,_));return _vO;}),_vW=function(_vX,_vY){var _vZ=hs_int64ToInt(_vX),_w0=E(_vM),_w1=_w0["v"]["i8"][(255&_vZ>>>0)>>>0&4294967295];if(_vY>_w1){if(_w1>=8){var _w2=hs_uncheckedIShiftRA64(_vX,8),_w3=function(_w4,_w5){while(1){var _w6=B((function(_w7,_w8){var _w9=hs_int64ToInt(_w7),_wa=_w0["v"]["i8"][(255&_w9>>>0)>>>0&4294967295];if(_w8>_wa){if(_wa>=8){var _wb=hs_uncheckedIShiftRA64(_w7,8),_wc=_w8-8|0;_w4=_wb;_w5=_wc;return __continue;}else{return new T2(0,new T(function(){var _wd=hs_uncheckedIShiftRA64(_w7,_wa);return B(_vF(_wd));}),_w8-_wa|0);}}else{return new T2(0,new T(function(){var _we=hs_uncheckedIShiftRA64(_w7,_w8);return B(_vF(_we));}),0);}})(_w4,_w5));if(_w6!=__continue){return _w6;}}};return new F(function(){return _w3(_w2,_vY-8|0);});}else{return new T2(0,new T(function(){var _wf=hs_uncheckedIShiftRA64(_vX,_w1);return B(_vF(_wf));}),_vY-_w1|0);}}else{return new T2(0,new T(function(){var _wg=hs_uncheckedIShiftRA64(_vX,_vY);return B(_vF(_wg));}),0);}},_wh=function(_wi){var _wj=hs_intToInt64(_wi);return E(_wj);},_wk=function(_wl){var _wm=E(_wl);if(!_wm._){return new F(function(){return _wh(_wm.a);});}else{return new F(function(){return I_toInt64(_wm.a);});}},_wn=function(_wo){return I_toInt(_wo)>>>0;},_wp=function(_wq){var _wr=E(_wq);if(!_wr._){return _wr.a>>>0;}else{return new F(function(){return _wn(_wr.a);});}},_ws=function(_wt){var _wu=B(_vA(_wt)),_wv=_wu.a,_ww=_wu.b;if(_ww<0){var _wx=function(_wy){if(!_wy){return new T2(0,E(_wv),B(_3J(_21, -_ww)));}else{var _wz=B(_vW(B(_wk(_wv)), -_ww));return new T2(0,E(_wz.a),B(_3J(_21,_wz.b)));}};if(!((B(_wp(_wv))&1)>>>0)){return new F(function(){return _wx(1);});}else{return new F(function(){return _wx(0);});}}else{return new T2(0,B(_3J(_wv,_ww)),_21);}},_wA=function(_wB){var _wC=B(_ws(E(_wB)));return new T2(0,E(_wC.a),E(_wC.b));},_wD=new T3(0,_n4,_o9,_wA),_wE=function(_wF){return E(E(_wF).a);},_wG=function(_wH){return E(E(_wH).a);},_wI=function(_wJ,_wK){if(_wJ<=_wK){var _wL=function(_wM){return new T2(1,_wM,new T(function(){if(_wM!=_wK){return B(_wL(_wM+1|0));}else{return __Z;}}));};return new F(function(){return _wL(_wJ);});}else{return __Z;}},_wN=function(_wO){return new F(function(){return _wI(E(_wO),2147483647);});},_wP=function(_wQ,_wR,_wS){if(_wS<=_wR){var _wT=new T(function(){var _wU=_wR-_wQ|0,_wV=function(_wW){return (_wW>=(_wS-_wU|0))?new T2(1,_wW,new T(function(){return B(_wV(_wW+_wU|0));})):new T2(1,_wW,_w);};return B(_wV(_wR));});return new T2(1,_wQ,_wT);}else{return (_wS<=_wQ)?new T2(1,_wQ,_w):__Z;}},_wX=function(_wY,_wZ,_x0){if(_x0>=_wZ){var _x1=new T(function(){var _x2=_wZ-_wY|0,_x3=function(_x4){return (_x4<=(_x0-_x2|0))?new T2(1,_x4,new T(function(){return B(_x3(_x4+_x2|0));})):new T2(1,_x4,_w);};return B(_x3(_wZ));});return new T2(1,_wY,_x1);}else{return (_x0>=_wY)?new T2(1,_wY,_w):__Z;}},_x5=function(_x6,_x7){if(_x7<_x6){return new F(function(){return _wP(_x6,_x7,-2147483648);});}else{return new F(function(){return _wX(_x6,_x7,2147483647);});}},_x8=function(_x9,_xa){return new F(function(){return _x5(E(_x9),E(_xa));});},_xb=function(_xc,_xd,_xe){if(_xd<_xc){return new F(function(){return _wP(_xc,_xd,_xe);});}else{return new F(function(){return _wX(_xc,_xd,_xe);});}},_xf=function(_xg,_xh,_xi){return new F(function(){return _xb(E(_xg),E(_xh),E(_xi));});},_xj=function(_xk,_xl){return new F(function(){return _wI(E(_xk),E(_xl));});},_xm=function(_xn){return E(_xn);},_xo=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_xp=new T(function(){return B(err(_xo));}),_xq=function(_xr){var _xs=E(_xr);return (_xs==(-2147483648))?E(_xp):_xs-1|0;},_xt=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_xu=new T(function(){return B(err(_xt));}),_xv=function(_xw){var _xx=E(_xw);return (_xx==2147483647)?E(_xu):_xx+1|0;},_xy={_:0,a:_xv,b:_xq,c:_xm,d:_xm,e:_wN,f:_x8,g:_xj,h:_xf},_xz=function(_xA,_xB){if(_xA<=0){if(_xA>=0){return new F(function(){return quot(_xA,_xB);});}else{if(_xB<=0){return new F(function(){return quot(_xA,_xB);});}else{return quot(_xA+1|0,_xB)-1|0;}}}else{if(_xB>=0){if(_xA>=0){return new F(function(){return quot(_xA,_xB);});}else{if(_xB<=0){return new F(function(){return quot(_xA,_xB);});}else{return quot(_xA+1|0,_xB)-1|0;}}}else{return quot(_xA-1|0,_xB)-1|0;}}},_xC=0,_xD=new T(function(){return B(_36(_xC));}),_xE=new T(function(){return die(_xD);}),_xF=function(_xG,_xH){var _xI=E(_xH);switch(_xI){case -1:var _xJ=E(_xG);if(_xJ==(-2147483648)){return E(_xE);}else{return new F(function(){return _xz(_xJ,-1);});}break;case 0:return E(_3a);default:return new F(function(){return _xz(_xG,_xI);});}},_xK=function(_xL,_xM){return new F(function(){return _xF(E(_xL),E(_xM));});},_xN=0,_xO=new T2(0,_xE,_xN),_xP=function(_xQ,_xR){var _xS=E(_xQ),_xT=E(_xR);switch(_xT){case -1:var _xU=E(_xS);if(_xU==(-2147483648)){return E(_xO);}else{if(_xU<=0){if(_xU>=0){var _xV=quotRemI(_xU,-1);return new T2(0,_xV.a,_xV.b);}else{var _xW=quotRemI(_xU,-1);return new T2(0,_xW.a,_xW.b);}}else{var _xX=quotRemI(_xU-1|0,-1);return new T2(0,_xX.a-1|0,(_xX.b+(-1)|0)+1|0);}}break;case 0:return E(_3a);default:if(_xS<=0){if(_xS>=0){var _xY=quotRemI(_xS,_xT);return new T2(0,_xY.a,_xY.b);}else{if(_xT<=0){var _xZ=quotRemI(_xS,_xT);return new T2(0,_xZ.a,_xZ.b);}else{var _y0=quotRemI(_xS+1|0,_xT);return new T2(0,_y0.a-1|0,(_y0.b+_xT|0)-1|0);}}}else{if(_xT>=0){if(_xS>=0){var _y1=quotRemI(_xS,_xT);return new T2(0,_y1.a,_y1.b);}else{if(_xT<=0){var _y2=quotRemI(_xS,_xT);return new T2(0,_y2.a,_y2.b);}else{var _y3=quotRemI(_xS+1|0,_xT);return new T2(0,_y3.a-1|0,(_y3.b+_xT|0)-1|0);}}}else{var _y4=quotRemI(_xS-1|0,_xT);return new T2(0,_y4.a-1|0,(_y4.b+_xT|0)+1|0);}}}},_y5=function(_y6,_y7){var _y8=_y6%_y7;if(_y6<=0){if(_y6>=0){return E(_y8);}else{if(_y7<=0){return E(_y8);}else{var _y9=E(_y8);return (_y9==0)?0:_y9+_y7|0;}}}else{if(_y7>=0){if(_y6>=0){return E(_y8);}else{if(_y7<=0){return E(_y8);}else{var _ya=E(_y8);return (_ya==0)?0:_ya+_y7|0;}}}else{var _yb=E(_y8);return (_yb==0)?0:_yb+_y7|0;}}},_yc=function(_yd,_ye){var _yf=E(_ye);switch(_yf){case -1:return E(_xN);case 0:return E(_3a);default:return new F(function(){return _y5(E(_yd),_yf);});}},_yg=function(_yh,_yi){var _yj=E(_yh),_yk=E(_yi);switch(_yk){case -1:var _yl=E(_yj);if(_yl==(-2147483648)){return E(_xE);}else{return new F(function(){return quot(_yl,-1);});}break;case 0:return E(_3a);default:return new F(function(){return quot(_yj,_yk);});}},_ym=function(_yn,_yo){var _yp=E(_yn),_yq=E(_yo);switch(_yq){case -1:var _yr=E(_yp);if(_yr==(-2147483648)){return E(_xO);}else{var _ys=quotRemI(_yr,-1);return new T2(0,_ys.a,_ys.b);}break;case 0:return E(_3a);default:var _yt=quotRemI(_yp,_yq);return new T2(0,_yt.a,_yt.b);}},_yu=function(_yv,_yw){var _yx=E(_yw);switch(_yx){case -1:return E(_xN);case 0:return E(_3a);default:return E(_yv)%_yx;}},_yy=function(_yz){return new F(function(){return _vD(E(_yz));});},_yA=function(_yB){return new T2(0,E(B(_vD(E(_yB)))),E(_ro));},_yC=function(_yD,_yE){return imul(E(_yD),E(_yE))|0;},_yF=function(_yG,_yH){return E(_yG)+E(_yH)|0;},_yI=function(_yJ,_yK){return E(_yJ)-E(_yK)|0;},_yL=function(_yM){var _yN=E(_yM);return (_yN<0)? -_yN:E(_yN);},_yO=function(_yP){return new F(function(){return _3n(_yP);});},_yQ=function(_yR){return  -E(_yR);},_yS=-1,_yT=0,_yU=1,_yV=function(_yW){var _yX=E(_yW);return (_yX>=0)?(E(_yX)==0)?E(_yT):E(_yU):E(_yS);},_yY={_:0,a:_yF,b:_yI,c:_yC,d:_yQ,e:_yL,f:_yV,g:_yO},_yZ=function(_z0,_z1){return E(_z0)==E(_z1);},_z2=function(_z3,_z4){return E(_z3)!=E(_z4);},_z5=new T2(0,_yZ,_z2),_z6=function(_z7,_z8){var _z9=E(_z7),_za=E(_z8);return (_z9>_za)?E(_z9):E(_za);},_zb=function(_zc,_zd){var _ze=E(_zc),_zf=E(_zd);return (_ze>_zf)?E(_zf):E(_ze);},_zg=function(_zh,_zi){return (_zh>=_zi)?(_zh!=_zi)?2:1:0;},_zj=function(_zk,_zl){return new F(function(){return _zg(E(_zk),E(_zl));});},_zm=function(_zn,_zo){return E(_zn)>=E(_zo);},_zp=function(_zq,_zr){return E(_zq)>E(_zr);},_zs=function(_zt,_zu){return E(_zt)<=E(_zu);},_zv=function(_zw,_zx){return E(_zw)<E(_zx);},_zy={_:0,a:_z5,b:_zj,c:_zv,d:_zs,e:_zp,f:_zm,g:_z6,h:_zb},_zz=new T3(0,_yY,_zy,_yA),_zA={_:0,a:_zz,b:_xy,c:_yg,d:_yu,e:_xK,f:_yc,g:_ym,h:_xP,i:_yy},_zB=new T1(0,2),_zC=function(_zD,_zE){while(1){var _zF=E(_zD);if(!_zF._){var _zG=_zF.a,_zH=E(_zE);if(!_zH._){var _zI=_zH.a;if(!(imul(_zG,_zI)|0)){return new T1(0,imul(_zG,_zI)|0);}else{_zD=new T1(1,I_fromInt(_zG));_zE=new T1(1,I_fromInt(_zI));continue;}}else{_zD=new T1(1,I_fromInt(_zG));_zE=_zH;continue;}}else{var _zJ=E(_zE);if(!_zJ._){_zD=_zF;_zE=new T1(1,I_fromInt(_zJ.a));continue;}else{return new T1(1,I_mul(_zF.a,_zJ.a));}}}},_zK=function(_zL,_zM,_zN){while(1){if(!(_zM%2)){var _zO=B(_zC(_zL,_zL)),_zP=quot(_zM,2);_zL=_zO;_zM=_zP;continue;}else{var _zQ=E(_zM);if(_zQ==1){return new F(function(){return _zC(_zL,_zN);});}else{var _zO=B(_zC(_zL,_zL)),_zR=B(_zC(_zL,_zN));_zL=_zO;_zM=quot(_zQ-1|0,2);_zN=_zR;continue;}}}},_zS=function(_zT,_zU){while(1){if(!(_zU%2)){var _zV=B(_zC(_zT,_zT)),_zW=quot(_zU,2);_zT=_zV;_zU=_zW;continue;}else{var _zX=E(_zU);if(_zX==1){return E(_zT);}else{return new F(function(){return _zK(B(_zC(_zT,_zT)),quot(_zX-1|0,2),_zT);});}}}},_zY=function(_zZ){return E(E(_zZ).b);},_A0=function(_A1){return E(E(_A1).c);},_A2=new T1(0,0),_A3=function(_A4){return E(E(_A4).d);},_A5=function(_A6,_A7){var _A8=B(_wE(_A6)),_A9=new T(function(){return B(_wG(_A8));}),_Aa=new T(function(){return B(A3(_A3,_A6,_A7,new T(function(){return B(A2(_8s,_A9,_ry));})));});return new F(function(){return A3(_qc,B(_pY(B(_zY(_A8)))),_Aa,new T(function(){return B(A2(_8s,_A9,_A2));}));});},_Ab=new T(function(){return B(unCStr("Negative exponent"));}),_Ac=new T(function(){return B(err(_Ab));}),_Ad=function(_Ae){return E(E(_Ae).c);},_Af=function(_Ag,_Ah,_Ai,_Aj){var _Ak=B(_wE(_Ah)),_Al=new T(function(){return B(_wG(_Ak));}),_Am=B(_zY(_Ak));if(!B(A3(_A0,_Am,_Aj,new T(function(){return B(A2(_8s,_Al,_A2));})))){if(!B(A3(_qc,B(_pY(_Am)),_Aj,new T(function(){return B(A2(_8s,_Al,_A2));})))){var _An=new T(function(){return B(A2(_8s,_Al,_ry));}),_Ao=new T(function(){return B(A2(_8s,_Al,_ro));}),_Ap=B(_pY(_Am)),_Aq=function(_Ar,_As,_At){while(1){var _Au=B((function(_Av,_Aw,_Ax){if(!B(_A5(_Ah,_Aw))){if(!B(A3(_qc,_Ap,_Aw,_Ao))){var _Ay=new T(function(){return B(A3(_Ad,_Ah,new T(function(){return B(A3(_9p,_Al,_Aw,_Ao));}),_An));});_Ar=new T(function(){return B(A3(_8L,_Ag,_Av,_Av));});_As=_Ay;_At=new T(function(){return B(A3(_8L,_Ag,_Av,_Ax));});return __continue;}else{return new F(function(){return A3(_8L,_Ag,_Av,_Ax);});}}else{var _Az=_Ax;_Ar=new T(function(){return B(A3(_8L,_Ag,_Av,_Av));});_As=new T(function(){return B(A3(_Ad,_Ah,_Aw,_An));});_At=_Az;return __continue;}})(_Ar,_As,_At));if(_Au!=__continue){return _Au;}}},_AA=function(_AB,_AC){while(1){var _AD=B((function(_AE,_AF){if(!B(_A5(_Ah,_AF))){if(!B(A3(_qc,_Ap,_AF,_Ao))){var _AG=new T(function(){return B(A3(_Ad,_Ah,new T(function(){return B(A3(_9p,_Al,_AF,_Ao));}),_An));});return new F(function(){return _Aq(new T(function(){return B(A3(_8L,_Ag,_AE,_AE));}),_AG,_AE);});}else{return E(_AE);}}else{_AB=new T(function(){return B(A3(_8L,_Ag,_AE,_AE));});_AC=new T(function(){return B(A3(_Ad,_Ah,_AF,_An));});return __continue;}})(_AB,_AC));if(_AD!=__continue){return _AD;}}};return new F(function(){return _AA(_Ai,_Aj);});}else{return new F(function(){return A2(_8s,_Ag,_ro);});}}else{return E(_Ac);}},_AH=new T(function(){return B(err(_Ab));}),_AI=function(_AJ,_AK){var _AL=B(_vA(_AK)),_AM=_AL.a,_AN=_AL.b,_AO=new T(function(){return B(_wG(new T(function(){return B(_wE(_AJ));})));});if(_AN<0){var _AP= -_AN;if(_AP>=0){var _AQ=E(_AP);if(!_AQ){var _AR=E(_ro);}else{var _AR=B(_zS(_zB,_AQ));}if(!B(_3f(_AR,_3I))){var _AS=B(_3z(_AM,_AR));return new T2(0,new T(function(){return B(A2(_8s,_AO,_AS.a));}),new T(function(){return B(_3b(_AS.b,_AN));}));}else{return E(_3a);}}else{return E(_AH);}}else{var _AT=new T(function(){var _AU=new T(function(){return B(_Af(_AO,_zA,new T(function(){return B(A2(_8s,_AO,_zB));}),_AN));});return B(A3(_8L,_AO,new T(function(){return B(A2(_8s,_AO,_AM));}),_AU));});return new T2(0,_AT,_6x);}},_AV=function(_AW,_AX){var _AY=B(_AI(_AW,E(_AX))),_AZ=_AY.a;if(E(_AY.b)<=0){return E(_AZ);}else{var _B0=B(_wG(B(_wE(_AW))));return new F(function(){return A3(_6X,_B0,_AZ,new T(function(){return B(A2(_8s,_B0,_21));}));});}},_B1=function(_B2,_B3){var _B4=B(_AI(_B2,E(_B3))),_B5=_B4.a;if(E(_B4.b)>=0){return E(_B5);}else{var _B6=B(_wG(B(_wE(_B2))));return new F(function(){return A3(_9p,_B6,_B5,new T(function(){return B(A2(_8s,_B6,_21));}));});}},_B7=function(_B8,_B9){var _Ba=B(_AI(_B8,E(_B9)));return new T2(0,_Ba.a,_Ba.b);},_Bb=function(_Bc,_Bd){var _Be=B(_AI(_Bc,_Bd)),_Bf=_Be.a,_Bg=E(_Be.b),_Bh=new T(function(){var _Bi=B(_wG(B(_wE(_Bc))));if(_Bg>=0){return B(A3(_6X,_Bi,_Bf,new T(function(){return B(A2(_8s,_Bi,_21));})));}else{return B(A3(_9p,_Bi,_Bf,new T(function(){return B(A2(_8s,_Bi,_21));})));}}),_Bj=function(_Bk){var _Bl=_Bk-0.5;return (_Bl>=0)?(E(_Bl)==0)?(!B(_A5(_Bc,_Bf)))?E(_Bh):E(_Bf):E(_Bh):E(_Bf);},_Bm=E(_Bg);if(!_Bm){return new F(function(){return _Bj(0);});}else{if(_Bm<=0){var _Bn= -_Bm-0.5;return (_Bn>=0)?(E(_Bn)==0)?(!B(_A5(_Bc,_Bf)))?E(_Bh):E(_Bf):E(_Bh):E(_Bf);}else{return new F(function(){return _Bj(_Bm);});}}},_Bo=function(_Bp,_Bq){return new F(function(){return _Bb(_Bp,E(_Bq));});},_Br=function(_Bs,_Bt){return E(B(_AI(_Bs,E(_Bt))).a);},_Bu={_:0,a:_wD,b:_n8,c:_B7,d:_Br,e:_Bo,f:_AV,g:_B1},_Bv=new T1(0,1),_Bw=function(_Bx,_By){var _Bz=E(_Bx);return new T2(0,_Bz,new T(function(){var _BA=B(_Bw(B(_3q(_Bz,_By)),_By));return new T2(1,_BA.a,_BA.b);}));},_BB=function(_BC){var _BD=B(_Bw(_BC,_Bv));return new T2(1,_BD.a,_BD.b);},_BE=function(_BF,_BG){var _BH=B(_Bw(_BF,new T(function(){return B(_5L(_BG,_BF));})));return new T2(1,_BH.a,_BH.b);},_BI=new T1(0,0),_BJ=function(_BK,_BL){var _BM=E(_BK);if(!_BM._){var _BN=_BM.a,_BO=E(_BL);return (_BO._==0)?_BN>=_BO.a:I_compareInt(_BO.a,_BN)<=0;}else{var _BP=_BM.a,_BQ=E(_BL);return (_BQ._==0)?I_compareInt(_BP,_BQ.a)>=0:I_compare(_BP,_BQ.a)>=0;}},_BR=function(_BS,_BT,_BU){if(!B(_BJ(_BT,_BI))){var _BV=function(_BW){return (!B(_42(_BW,_BU)))?new T2(1,_BW,new T(function(){return B(_BV(B(_3q(_BW,_BT))));})):__Z;};return new F(function(){return _BV(_BS);});}else{var _BX=function(_BY){return (!B(_3T(_BY,_BU)))?new T2(1,_BY,new T(function(){return B(_BX(B(_3q(_BY,_BT))));})):__Z;};return new F(function(){return _BX(_BS);});}},_BZ=function(_C0,_C1,_C2){return new F(function(){return _BR(_C0,B(_5L(_C1,_C0)),_C2);});},_C3=function(_C4,_C5){return new F(function(){return _BR(_C4,_Bv,_C5);});},_C6=function(_C7){return new F(function(){return _3n(_C7);});},_C8=function(_C9){return new F(function(){return _5L(_C9,_Bv);});},_Ca=function(_Cb){return new F(function(){return _3q(_Cb,_Bv);});},_Cc=function(_Cd){return new F(function(){return _vD(E(_Cd));});},_Ce={_:0,a:_Ca,b:_C8,c:_Cc,d:_C6,e:_BB,f:_BE,g:_C3,h:_BZ},_Cf=function(_Cg,_Ch){while(1){var _Ci=E(_Cg);if(!_Ci._){var _Cj=E(_Ci.a);if(_Cj==(-2147483648)){_Cg=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ck=E(_Ch);if(!_Ck._){return new T1(0,B(_xz(_Cj,_Ck.a)));}else{_Cg=new T1(1,I_fromInt(_Cj));_Ch=_Ck;continue;}}}else{var _Cl=_Ci.a,_Cm=E(_Ch);return (_Cm._==0)?new T1(1,I_div(_Cl,I_fromInt(_Cm.a))):new T1(1,I_div(_Cl,_Cm.a));}}},_Cn=function(_Co,_Cp){if(!B(_3f(_Cp,_A2))){return new F(function(){return _Cf(_Co,_Cp);});}else{return E(_3a);}},_Cq=function(_Cr,_Cs){while(1){var _Ct=E(_Cr);if(!_Ct._){var _Cu=E(_Ct.a);if(_Cu==(-2147483648)){_Cr=new T1(1,I_fromInt(-2147483648));continue;}else{var _Cv=E(_Cs);if(!_Cv._){var _Cw=_Cv.a;return new T2(0,new T1(0,B(_xz(_Cu,_Cw))),new T1(0,B(_y5(_Cu,_Cw))));}else{_Cr=new T1(1,I_fromInt(_Cu));_Cs=_Cv;continue;}}}else{var _Cx=E(_Cs);if(!_Cx._){_Cr=_Ct;_Cs=new T1(1,I_fromInt(_Cx.a));continue;}else{var _Cy=I_divMod(_Ct.a,_Cx.a);return new T2(0,new T1(1,_Cy.a),new T1(1,_Cy.b));}}}},_Cz=function(_CA,_CB){if(!B(_3f(_CB,_A2))){var _CC=B(_Cq(_CA,_CB));return new T2(0,_CC.a,_CC.b);}else{return E(_3a);}},_CD=function(_CE,_CF){while(1){var _CG=E(_CE);if(!_CG._){var _CH=E(_CG.a);if(_CH==(-2147483648)){_CE=new T1(1,I_fromInt(-2147483648));continue;}else{var _CI=E(_CF);if(!_CI._){return new T1(0,B(_y5(_CH,_CI.a)));}else{_CE=new T1(1,I_fromInt(_CH));_CF=_CI;continue;}}}else{var _CJ=_CG.a,_CK=E(_CF);return (_CK._==0)?new T1(1,I_mod(_CJ,I_fromInt(_CK.a))):new T1(1,I_mod(_CJ,_CK.a));}}},_CL=function(_CM,_CN){if(!B(_3f(_CN,_A2))){return new F(function(){return _CD(_CM,_CN);});}else{return E(_3a);}},_CO=function(_CP,_CQ){while(1){var _CR=E(_CP);if(!_CR._){var _CS=E(_CR.a);if(_CS==(-2147483648)){_CP=new T1(1,I_fromInt(-2147483648));continue;}else{var _CT=E(_CQ);if(!_CT._){return new T1(0,quot(_CS,_CT.a));}else{_CP=new T1(1,I_fromInt(_CS));_CQ=_CT;continue;}}}else{var _CU=_CR.a,_CV=E(_CQ);return (_CV._==0)?new T1(0,I_toInt(I_quot(_CU,I_fromInt(_CV.a)))):new T1(1,I_quot(_CU,_CV.a));}}},_CW=function(_CX,_CY){if(!B(_3f(_CY,_A2))){return new F(function(){return _CO(_CX,_CY);});}else{return E(_3a);}},_CZ=function(_D0,_D1){if(!B(_3f(_D1,_A2))){var _D2=B(_3z(_D0,_D1));return new T2(0,_D2.a,_D2.b);}else{return E(_3a);}},_D3=function(_D4,_D5){while(1){var _D6=E(_D4);if(!_D6._){var _D7=E(_D6.a);if(_D7==(-2147483648)){_D4=new T1(1,I_fromInt(-2147483648));continue;}else{var _D8=E(_D5);if(!_D8._){return new T1(0,_D7%_D8.a);}else{_D4=new T1(1,I_fromInt(_D7));_D5=_D8;continue;}}}else{var _D9=_D6.a,_Da=E(_D5);return (_Da._==0)?new T1(1,I_rem(_D9,I_fromInt(_Da.a))):new T1(1,I_rem(_D9,_Da.a));}}},_Db=function(_Dc,_Dd){if(!B(_3f(_Dd,_A2))){return new F(function(){return _D3(_Dc,_Dd);});}else{return E(_3a);}},_De=function(_Df){return E(_Df);},_Dg=function(_Dh){return E(_Dh);},_Di=function(_Dj){var _Dk=E(_Dj);if(!_Dk._){var _Dl=E(_Dk.a);return (_Dl==(-2147483648))?E(_6p):(_Dl<0)?new T1(0, -_Dl):E(_Dk);}else{var _Dm=_Dk.a;return (I_compareInt(_Dm,0)>=0)?E(_Dk):new T1(1,I_negate(_Dm));}},_Dn=new T1(0,0),_Do=new T1(0,-1),_Dp=function(_Dq){var _Dr=E(_Dq);if(!_Dr._){var _Ds=_Dr.a;return (_Ds>=0)?(E(_Ds)==0)?E(_Dn):E(_41):E(_Do);}else{var _Dt=I_compareInt(_Dr.a,0);return (_Dt<=0)?(E(_Dt)==0)?E(_Dn):E(_Do):E(_41);}},_Du={_:0,a:_3q,b:_5L,c:_zC,d:_6q,e:_Di,f:_Dp,g:_Dg},_Dv=function(_Dw,_Dx){var _Dy=E(_Dw);if(!_Dy._){var _Dz=_Dy.a,_DA=E(_Dx);return (_DA._==0)?_Dz!=_DA.a:(I_compareInt(_DA.a,_Dz)==0)?false:true;}else{var _DB=_Dy.a,_DC=E(_Dx);return (_DC._==0)?(I_compareInt(_DB,_DC.a)==0)?false:true:(I_compare(_DB,_DC.a)==0)?false:true;}},_DD=new T2(0,_3f,_Dv),_DE=function(_DF,_DG){return (!B(_5w(_DF,_DG)))?E(_DF):E(_DG);},_DH=function(_DI,_DJ){return (!B(_5w(_DI,_DJ)))?E(_DJ):E(_DI);},_DK={_:0,a:_DD,b:_22,c:_42,d:_5w,e:_3T,f:_BJ,g:_DE,h:_DH},_DL=function(_DM){return new T2(0,E(_DM),E(_ro));},_DN=new T3(0,_Du,_DK,_DL),_DO={_:0,a:_DN,b:_Ce,c:_CW,d:_Db,e:_Cn,f:_CL,g:_CZ,h:_Cz,i:_De},_DP=function(_DQ){return E(E(_DQ).b);},_DR=function(_DS){return E(E(_DS).g);},_DT=new T1(0,1),_DU=function(_DV,_DW,_DX){var _DY=B(_DP(_DV)),_DZ=B(_8J(_DY)),_E0=new T(function(){var _E1=new T(function(){var _E2=new T(function(){var _E3=new T(function(){return B(A3(_DR,_DV,_DO,new T(function(){return B(A3(_8P,_DY,_DW,_DX));})));});return B(A2(_8s,_DZ,_E3));}),_E4=new T(function(){return B(A2(_6Z,_DZ,new T(function(){return B(A2(_8s,_DZ,_DT));})));});return B(A3(_8L,_DZ,_E4,_E2));});return B(A3(_8L,_DZ,_E1,_DX));});return new F(function(){return A3(_6X,_DZ,_DW,_E0);});},_E5=1.5707963267948966,_E6=function(_E7){return 0.2/Math.cos(B(_DU(_Bu,_E7,_E5))-0.7853981633974483);},_E8=new T(function(){var _E9=B(_uf(_E6,1.2,_vz,_vz,_vy,_vz,_vz,_vz,_vz,_vz,_vy,_vy,_vy));return {_:0,a:E(_E9.a),b:E(_E9.b),c:E(_E9.c),d:E(_E9.d),e:E(_E9.e),f:E(_E9.f),g:E(_E9.g),h:_E9.h,i:_E9.i,j:_E9.j};}),_Ea=0,_Eb=0.3,_Ec=function(_Ed){return E(_Eb);},_Ee=new T(function(){var _Ef=B(_uf(_Ec,1.2,_vy,_vz,_vy,_vz,_vz,_vz,_vz,_vz,_vy,_vy,_vy));return {_:0,a:E(_Ef.a),b:E(_Ef.b),c:E(_Ef.c),d:E(_Ef.d),e:E(_Ef.e),f:E(_Ef.f),g:E(_Ef.g),h:_Ef.h,i:_Ef.i,j:_Ef.j};}),_Eg=new T(function(){var _Eh=B(_uf(_Ec,1.2,_vy,_vy,_vz,_vz,_vz,_vz,_vz,_vz,_vy,_vy,_vy));return {_:0,a:E(_Eh.a),b:E(_Eh.b),c:E(_Eh.c),d:E(_Eh.d),e:E(_Eh.e),f:E(_Eh.f),g:E(_Eh.g),h:_Eh.h,i:_Eh.i,j:_Eh.j};}),_Ei=2,_Ej=function(_Ek){return 0.3/Math.cos(B(_DU(_Bu,_Ek,_E5))-0.7853981633974483);},_El=new T(function(){var _Em=B(_uf(_Ej,1.2,_Ei,_vy,_vy,_vz,_vz,_vz,_vz,_vz,_vy,_vy,_vy));return {_:0,a:E(_Em.a),b:E(_Em.b),c:E(_Em.c),d:E(_Em.d),e:E(_Em.e),f:E(_Em.f),g:E(_Em.g),h:_Em.h,i:_Em.i,j:_Em.j};}),_En=0.5,_Eo=new T(function(){var _Ep=B(_uf(_Ec,1.2,_vz,_vy,_En,_vz,_vz,_vz,_vz,_vz,_vy,_vy,_vy));return {_:0,a:E(_Ep.a),b:E(_Ep.b),c:E(_Ep.c),d:E(_Ep.d),e:E(_Ep.e),f:E(_Ep.f),g:E(_Ep.g),h:_Ep.h,i:_Ep.i,j:_Ep.j};}),_Eq=new T2(1,_Eo,_w),_Er=new T2(1,_El,_Eq),_Es=new T2(1,_Eg,_Er),_Et=new T2(1,_Ee,_Es),_Eu=new T2(1,_E8,_Et),_Ev=new T(function(){return B(unCStr("Negative range size"));}),_Ew=new T(function(){return B(err(_Ev));}),_Ex=function(_){var _Ey=B(_lY(_Eu,0))-1|0,_Ez=function(_EA){if(_EA>=0){var _EB=newArr(_EA,_m4),_EC=_EB,_ED=E(_EA);if(!_ED){return new T4(0,E(_Ea),E(_Ey),0,_EC);}else{var _EE=function(_EF,_EG,_){while(1){var _EH=E(_EF);if(!_EH._){return E(_);}else{var _=_EC[_EG]=_EH.a;if(_EG!=(_ED-1|0)){var _EI=_EG+1|0;_EF=_EH.b;_EG=_EI;continue;}else{return E(_);}}}},_=B((function(_EJ,_EK,_EL,_){var _=_EC[_EL]=_EJ;if(_EL!=(_ED-1|0)){return new F(function(){return _EE(_EK,_EL+1|0,_);});}else{return E(_);}})(_E8,_Et,0,_));return new T4(0,E(_Ea),E(_Ey),_ED,_EC);}}else{return E(_Ew);}};if(0>_Ey){return new F(function(){return _Ez(0);});}else{return new F(function(){return _Ez(_Ey+1|0);});}},_EM=function(_EN){var _EO=B(A1(_EN,_));return E(_EO);},_EP=new T(function(){return B(_EM(_Ex));}),_EQ="enclose",_ER="outline",_ES="polygon",_ET="z",_EU="y",_EV="x",_EW=function(_EX){return new F(function(){return _om(new T2(1,new T2(0,_EV,new T(function(){return E(E(E(E(_EX).d).a).a);})),new T2(1,new T2(0,_EU,new T(function(){return E(E(E(E(_EX).d).a).b);})),new T2(1,new T2(0,_ET,new T(function(){return E(E(E(E(_EX).d).a).c);})),new T2(1,new T2(0,_ES,new T(function(){return E(_EX).h;})),new T2(1,new T2(0,_ER,new T(function(){return E(_EX).i;})),new T2(1,new T2(0,_EQ,new T(function(){return E(_EX).j;})),_w)))))));});},_EY=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_EZ=new T(function(){return B(err(_EY));}),_F0=new T(function(){return eval("__strict(drawObjects)");}),_F1=new T(function(){return eval("__strict(draw)");}),_F2=function(_F3,_F4){var _F5=jsShowI(_F3);return new F(function(){return _n(fromJSStr(_F5),_F4);});},_F6=function(_F7,_F8,_F9){if(_F8>=0){return new F(function(){return _F2(_F8,_F9);});}else{if(_F7<=6){return new F(function(){return _F2(_F8,_F9);});}else{return new T2(1,_7g,new T(function(){var _Fa=jsShowI(_F8);return B(_n(fromJSStr(_Fa),new T2(1,_7f,_F9)));}));}}},_Fb=new T(function(){return B(unCStr(")"));}),_Fc=function(_Fd,_Fe){var _Ff=new T(function(){var _Fg=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_F6(0,_Fd,_w)),_Fb));})));},1);return B(_n(B(_F6(0,_Fe,_w)),_Fg));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Ff)));});},_Fh=new T2(1,_ol,_w),_Fi=function(_Fj){return E(_Fj);},_Fk=function(_Fl){return E(_Fl);},_Fm=function(_Fn,_Fo){return E(_Fo);},_Fp=function(_Fq,_Fr){return E(_Fq);},_Fs=function(_Ft){return E(_Ft);},_Fu=new T2(0,_Fs,_Fp),_Fv=function(_Fw,_Fx){return E(_Fw);},_Fy=new T5(0,_Fu,_Fk,_Fi,_Fm,_Fv),_Fz="flipped2",_FA="flipped1",_FB="c1y",_FC="c1x",_FD="w2z",_FE="w2y",_FF="w2x",_FG="w1z",_FH="w1y",_FI="w1x",_FJ="d2z",_FK="d2y",_FL="d2x",_FM="d1z",_FN="d1y",_FO="d1x",_FP="c2y",_FQ="c2x",_FR=function(_FS,_){var _FT=__get(_FS,E(_FI)),_FU=__get(_FS,E(_FH)),_FV=__get(_FS,E(_FG)),_FW=__get(_FS,E(_FF)),_FX=__get(_FS,E(_FE)),_FY=__get(_FS,E(_FD)),_FZ=__get(_FS,E(_FC)),_G0=__get(_FS,E(_FB)),_G1=__get(_FS,E(_FQ)),_G2=__get(_FS,E(_FP)),_G3=__get(_FS,E(_FO)),_G4=__get(_FS,E(_FN)),_G5=__get(_FS,E(_FM)),_G6=__get(_FS,E(_FL)),_G7=__get(_FS,E(_FK)),_G8=__get(_FS,E(_FJ)),_G9=__get(_FS,E(_FA)),_Ga=__get(_FS,E(_Fz));return {_:0,a:E(new T3(0,E(_FT),E(_FU),E(_FV))),b:E(new T3(0,E(_FW),E(_FX),E(_FY))),c:E(new T2(0,E(_FZ),E(_G0))),d:E(new T2(0,E(_G1),E(_G2))),e:E(new T3(0,E(_G3),E(_G4),E(_G5))),f:E(new T3(0,E(_G6),E(_G7),E(_G8))),g:E(_G9),h:E(_Ga)};},_Gb=function(_Gc,_){var _Gd=E(_Gc);if(!_Gd._){return _w;}else{var _Ge=B(_FR(E(_Gd.a),_)),_Gf=B(_Gb(_Gd.b,_));return new T2(1,_Ge,_Gf);}},_Gg=function(_Gh){var _Gi=E(_Gh);return (E(_Gi.b)-E(_Gi.a)|0)+1|0;},_Gj=function(_Gk,_Gl){var _Gm=E(_Gk),_Gn=E(_Gl);return (E(_Gm.a)>_Gn)?false:_Gn<=E(_Gm.b);},_Go=function(_Gp){return new F(function(){return _F6(0,E(_Gp),_w);});},_Gq=function(_Gr,_Gs,_Gt){return new F(function(){return _F6(E(_Gr),E(_Gs),_Gt);});},_Gu=function(_Gv,_Gw){return new F(function(){return _F6(0,E(_Gv),_Gw);});},_Gx=function(_Gy,_Gz){return new F(function(){return _2Q(_Gu,_Gy,_Gz);});},_GA=new T3(0,_Gq,_Go,_Gx),_GB=0,_GC=function(_GD,_GE,_GF){return new F(function(){return A1(_GD,new T2(1,_2N,new T(function(){return B(A1(_GE,_GF));})));});},_GG=new T(function(){return B(unCStr("foldr1"));}),_GH=new T(function(){return B(_qN(_GG));}),_GI=function(_GJ,_GK){var _GL=E(_GK);if(!_GL._){return E(_GH);}else{var _GM=_GL.a,_GN=E(_GL.b);if(!_GN._){return E(_GM);}else{return new F(function(){return A2(_GJ,_GM,new T(function(){return B(_GI(_GJ,_GN));}));});}}},_GO=new T(function(){return B(unCStr(" out of range "));}),_GP=new T(function(){return B(unCStr("}.index: Index "));}),_GQ=new T(function(){return B(unCStr("Ix{"));}),_GR=new T2(1,_7f,_w),_GS=new T2(1,_7f,_GR),_GT=0,_GU=function(_GV){return E(E(_GV).a);},_GW=function(_GX,_GY,_GZ,_H0,_H1){var _H2=new T(function(){var _H3=new T(function(){var _H4=new T(function(){var _H5=new T(function(){var _H6=new T(function(){return B(A3(_GI,_GC,new T2(1,new T(function(){return B(A3(_GU,_GZ,_GT,_H0));}),new T2(1,new T(function(){return B(A3(_GU,_GZ,_GT,_H1));}),_w)),_GS));});return B(_n(_GO,new T2(1,_7g,new T2(1,_7g,_H6))));});return B(A(_GU,[_GZ,_GB,_GY,new T2(1,_7f,_H5)]));});return B(_n(_GP,new T2(1,_7g,_H4)));},1);return B(_n(_GX,_H3));},1);return new F(function(){return err(B(_n(_GQ,_H2)));});},_H7=function(_H8,_H9,_Ha,_Hb,_Hc){return new F(function(){return _GW(_H8,_H9,_Hc,_Ha,_Hb);});},_Hd=function(_He,_Hf,_Hg,_Hh){var _Hi=E(_Hg);return new F(function(){return _H7(_He,_Hf,_Hi.a,_Hi.b,_Hh);});},_Hj=function(_Hk,_Hl,_Hm,_Hn){return new F(function(){return _Hd(_Hn,_Hm,_Hl,_Hk);});},_Ho=new T(function(){return B(unCStr("Int"));}),_Hp=function(_Hq,_Hr){return new F(function(){return _Hj(_GA,_Hr,_Hq,_Ho);});},_Hs=function(_Ht,_Hu){var _Hv=E(_Ht),_Hw=E(_Hv.a),_Hx=E(_Hu);if(_Hw>_Hx){return new F(function(){return _Hp(_Hx,_Hv);});}else{if(_Hx>E(_Hv.b)){return new F(function(){return _Hp(_Hx,_Hv);});}else{return _Hx-_Hw|0;}}},_Hy=function(_Hz){var _HA=E(_Hz);return new F(function(){return _xj(_HA.a,_HA.b);});},_HB=function(_HC){var _HD=E(_HC),_HE=E(_HD.a),_HF=E(_HD.b);return (_HE>_HF)?E(_GB):(_HF-_HE|0)+1|0;},_HG=function(_HH,_HI){return new F(function(){return _yI(_HI,E(_HH).a);});},_HJ={_:0,a:_zy,b:_Hy,c:_Hs,d:_HG,e:_Gj,f:_HB,g:_Gg},_HK=function(_HL,_HM,_){while(1){var _HN=B((function(_HO,_HP,_){var _HQ=E(_HO);if(!_HQ._){return new T2(0,_ol,_HP);}else{var _HR=B(A2(_HQ.a,_HP,_));_HL=_HQ.b;_HM=new T(function(){return E(E(_HR).b);});return __continue;}})(_HL,_HM,_));if(_HN!=__continue){return _HN;}}},_HS=function(_HT,_HU){return new T2(1,_HT,_HU);},_HV=function(_HW,_HX){var _HY=E(_HX);return new T2(0,_HY.a,_HY.b);},_HZ=function(_I0){return E(E(_I0).f);},_I1=function(_I2,_I3,_I4){var _I5=E(_I3),_I6=_I5.a,_I7=_I5.b,_I8=function(_){var _I9=B(A2(_HZ,_I2,_I5));if(_I9>=0){var _Ia=newArr(_I9,_m4),_Ib=_Ia,_Ic=E(_I9);if(!_Ic){return new T(function(){return new T4(0,E(_I6),E(_I7),0,_Ib);});}else{var _Id=function(_Ie,_If,_){while(1){var _Ig=E(_Ie);if(!_Ig._){return E(_);}else{var _=_Ib[_If]=_Ig.a;if(_If!=(_Ic-1|0)){var _Ih=_If+1|0;_Ie=_Ig.b;_If=_Ih;continue;}else{return E(_);}}}},_=B(_Id(_I4,0,_));return new T(function(){return new T4(0,E(_I6),E(_I7),_Ic,_Ib);});}}else{return E(_Ew);}};return new F(function(){return _EM(_I8);});},_Ii=function(_Ij,_Ik,_Il,_Im){var _In=new T(function(){var _Io=E(_Im),_Ip=_Io.c-1|0,_Iq=new T(function(){return B(A2(_cF,_Ik,_w));});if(0<=_Ip){var _Ir=new T(function(){return B(_8F(_Ik));}),_Is=function(_It){var _Iu=new T(function(){var _Iv=new T(function(){return B(A1(_Il,new T(function(){return E(_Io.d[_It]);})));});return B(A3(_8T,_Ir,_HS,_Iv));});return new F(function(){return A3(_8R,_Ik,_Iu,new T(function(){if(_It!=_Ip){return B(_Is(_It+1|0));}else{return E(_Iq);}}));});};return B(_Is(0));}else{return E(_Iq);}}),_Iw=new T(function(){return B(_HV(_Ij,_Im));});return new F(function(){return A3(_8T,B(_8F(_Ik)),function(_Ix){return new F(function(){return _I1(_Ij,_Iw,_Ix);});},_In);});},_Iy=function(_Iz,_IA,_IB,_IC,_ID,_IE,_IF,_IG,_IH){var _II=B(_8L(_Iz));return new T2(0,new T3(0,E(B(A1(B(A1(_II,_IA)),_IE))),E(B(A1(B(A1(_II,_IB)),_IF))),E(B(A1(B(A1(_II,_IC)),_IG)))),B(A1(B(A1(_II,_ID)),_IH)));},_IJ=function(_IK,_IL,_IM,_IN,_IO,_IP,_IQ,_IR,_IS){var _IT=B(_6X(_IK));return new T2(0,new T3(0,E(B(A1(B(A1(_IT,_IL)),_IP))),E(B(A1(B(A1(_IT,_IM)),_IQ))),E(B(A1(B(A1(_IT,_IN)),_IR)))),B(A1(B(A1(_IT,_IO)),_IS)));},_IU=1.0e-2,_IV=function(_IW,_IX,_IY,_IZ,_J0,_J1,_J2,_J3,_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb,_Jc,_Jd){var _Je=B(_Iy(_n4,_J3,_J4,_J5,_J6,_IU,_IU,_IU,_IU)),_Jf=E(_Je.a),_Jg=B(_IJ(_n4,_IZ,_J0,_J1,_J2,_Jf.a,_Jf.b,_Jf.c,_Je.b)),_Jh=E(_Jg.a);return new F(function(){return _tv(_IW,_IX,_IY,_Jh.a,_Jh.b,_Jh.c,_Jg.b,_J3,_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb,_Jc,_Jd);});},_Ji=function(_Jj){var _Jk=E(_Jj),_Jl=E(_Jk.d),_Jm=E(_Jl.a),_Jn=E(_Jk.e),_Jo=E(_Jn.a),_Jp=E(_Jk.f),_Jq=B(_IV(_Jk.a,_Jk.b,_Jk.c,_Jm.a,_Jm.b,_Jm.c,_Jl.b,_Jo.a,_Jo.b,_Jo.c,_Jn.b,_Jp.a,_Jp.b,_Jp.c,_Jk.g,_Jk.h,_Jk.i,_Jk.j));return {_:0,a:E(_Jq.a),b:E(_Jq.b),c:E(_Jq.c),d:E(_Jq.d),e:E(_Jq.e),f:E(_Jq.f),g:E(_Jq.g),h:_Jq.h,i:_Jq.i,j:_Jq.j};},_Jr=function(_Js,_Jt,_Ju,_Jv,_Jw,_Jx,_Jy,_Jz,_JA){var _JB=B(_8J(B(_8H(_Js))));return new F(function(){return A3(_6X,_JB,new T(function(){return B(_oZ(_Js,_Jt,_Ju,_Jv,_Jx,_Jy,_Jz));}),new T(function(){return B(A3(_8L,_JB,_Jw,_JA));}));});},_JC=new T(function(){return B(unCStr("base"));}),_JD=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_JE=new T(function(){return B(unCStr("IOException"));}),_JF=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_JC,_JD,_JE),_JG=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_JF,_w,_w),_JH=function(_JI){return E(_JG);},_JJ=function(_JK){var _JL=E(_JK);return new F(function(){return _2n(B(_2l(_JL.a)),_JH,_JL.b);});},_JM=new T(function(){return B(unCStr(": "));}),_JN=new T(function(){return B(unCStr(")"));}),_JO=new T(function(){return B(unCStr(" ("));}),_JP=new T(function(){return B(unCStr("interrupted"));}),_JQ=new T(function(){return B(unCStr("system error"));}),_JR=new T(function(){return B(unCStr("unsatisified constraints"));}),_JS=new T(function(){return B(unCStr("user error"));}),_JT=new T(function(){return B(unCStr("permission denied"));}),_JU=new T(function(){return B(unCStr("illegal operation"));}),_JV=new T(function(){return B(unCStr("end of file"));}),_JW=new T(function(){return B(unCStr("resource exhausted"));}),_JX=new T(function(){return B(unCStr("resource busy"));}),_JY=new T(function(){return B(unCStr("does not exist"));}),_JZ=new T(function(){return B(unCStr("already exists"));}),_K0=new T(function(){return B(unCStr("resource vanished"));}),_K1=new T(function(){return B(unCStr("timeout"));}),_K2=new T(function(){return B(unCStr("unsupported operation"));}),_K3=new T(function(){return B(unCStr("hardware fault"));}),_K4=new T(function(){return B(unCStr("inappropriate type"));}),_K5=new T(function(){return B(unCStr("invalid argument"));}),_K6=new T(function(){return B(unCStr("failed"));}),_K7=new T(function(){return B(unCStr("protocol error"));}),_K8=function(_K9,_Ka){switch(E(_K9)){case 0:return new F(function(){return _n(_JZ,_Ka);});break;case 1:return new F(function(){return _n(_JY,_Ka);});break;case 2:return new F(function(){return _n(_JX,_Ka);});break;case 3:return new F(function(){return _n(_JW,_Ka);});break;case 4:return new F(function(){return _n(_JV,_Ka);});break;case 5:return new F(function(){return _n(_JU,_Ka);});break;case 6:return new F(function(){return _n(_JT,_Ka);});break;case 7:return new F(function(){return _n(_JS,_Ka);});break;case 8:return new F(function(){return _n(_JR,_Ka);});break;case 9:return new F(function(){return _n(_JQ,_Ka);});break;case 10:return new F(function(){return _n(_K7,_Ka);});break;case 11:return new F(function(){return _n(_K6,_Ka);});break;case 12:return new F(function(){return _n(_K5,_Ka);});break;case 13:return new F(function(){return _n(_K4,_Ka);});break;case 14:return new F(function(){return _n(_K3,_Ka);});break;case 15:return new F(function(){return _n(_K2,_Ka);});break;case 16:return new F(function(){return _n(_K1,_Ka);});break;case 17:return new F(function(){return _n(_K0,_Ka);});break;default:return new F(function(){return _n(_JP,_Ka);});}},_Kb=new T(function(){return B(unCStr("}"));}),_Kc=new T(function(){return B(unCStr("{handle: "));}),_Kd=function(_Ke,_Kf,_Kg,_Kh,_Ki,_Kj){var _Kk=new T(function(){var _Kl=new T(function(){var _Km=new T(function(){var _Kn=E(_Kh);if(!_Kn._){return E(_Kj);}else{var _Ko=new T(function(){return B(_n(_Kn,new T(function(){return B(_n(_JN,_Kj));},1)));},1);return B(_n(_JO,_Ko));}},1);return B(_K8(_Kf,_Km));}),_Kp=E(_Kg);if(!_Kp._){return E(_Kl);}else{return B(_n(_Kp,new T(function(){return B(_n(_JM,_Kl));},1)));}}),_Kq=E(_Ki);if(!_Kq._){var _Kr=E(_Ke);if(!_Kr._){return E(_Kk);}else{var _Ks=E(_Kr.a);if(!_Ks._){var _Kt=new T(function(){var _Ku=new T(function(){return B(_n(_Kb,new T(function(){return B(_n(_JM,_Kk));},1)));},1);return B(_n(_Ks.a,_Ku));},1);return new F(function(){return _n(_Kc,_Kt);});}else{var _Kv=new T(function(){var _Kw=new T(function(){return B(_n(_Kb,new T(function(){return B(_n(_JM,_Kk));},1)));},1);return B(_n(_Ks.a,_Kw));},1);return new F(function(){return _n(_Kc,_Kv);});}}}else{return new F(function(){return _n(_Kq.a,new T(function(){return B(_n(_JM,_Kk));},1));});}},_Kx=function(_Ky){var _Kz=E(_Ky);return new F(function(){return _Kd(_Kz.a,_Kz.b,_Kz.c,_Kz.d,_Kz.f,_w);});},_KA=function(_KB,_KC,_KD){var _KE=E(_KC);return new F(function(){return _Kd(_KE.a,_KE.b,_KE.c,_KE.d,_KE.f,_KD);});},_KF=function(_KG,_KH){var _KI=E(_KG);return new F(function(){return _Kd(_KI.a,_KI.b,_KI.c,_KI.d,_KI.f,_KH);});},_KJ=function(_KK,_KL){return new F(function(){return _2Q(_KF,_KK,_KL);});},_KM=new T3(0,_KA,_Kx,_KJ),_KN=new T(function(){return new T5(0,_JH,_KM,_KO,_JJ,_Kx);}),_KO=function(_KP){return new T2(0,_KN,_KP);},_KQ=__Z,_KR=7,_KS=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_KT=new T6(0,_KQ,_KR,_w,_KS,_KQ,_KQ),_KU=new T(function(){return B(_KO(_KT));}),_KV=function(_){return new F(function(){return die(_KU);});},_KW=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_KX=new T6(0,_KQ,_KR,_w,_KW,_KQ,_KQ),_KY=new T(function(){return B(_KO(_KX));}),_KZ=function(_){return new F(function(){return die(_KY);});},_L0=function(_L1,_){return new T2(0,_w,_L1);},_L2=0.6,_L3=1,_L4=new T(function(){return B(unCStr(")"));}),_L5=function(_L6,_L7){var _L8=new T(function(){var _L9=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_F6(0,_L6,_w)),_L4));})));},1);return B(_n(B(_F6(0,_L7,_w)),_L9));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_L8)));});},_La=function(_Lb,_Lc){var _Ld=new T(function(){var _Le=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_F6(0,_Lc,_w)),_L4));})));},1);return B(_n(B(_F6(0,_Lb,_w)),_Le));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Ld)));});},_Lf=function(_Lg){var _Lh=E(_Lg);if(!_Lh._){return E(_L0);}else{var _Li=new T(function(){return B(_Lf(_Lh.b));}),_Lj=function(_Lk){var _Ll=E(_Lk);if(!_Ll._){return E(_Li);}else{var _Lm=_Ll.a,_Ln=new T(function(){return B(_Lj(_Ll.b));}),_Lo=new T(function(){return 0.1*E(E(_Lm).e)/1.0e-2;}),_Lp=new T(function(){var _Lq=E(_Lm);if(_Lq.a!=_Lq.b){return E(_L3);}else{return E(_L2);}}),_Lr=function(_Ls,_){var _Lt=E(_Ls),_Lu=_Lt.c,_Lv=_Lt.d,_Lw=E(_Lt.a),_Lx=E(_Lt.b),_Ly=E(_Lm),_Lz=_Ly.a,_LA=_Ly.b,_LB=E(_Ly.c),_LC=_LB.b,_LD=E(_LB.a),_LE=_LD.a,_LF=_LD.b,_LG=_LD.c,_LH=E(_Ly.d),_LI=_LH.b,_LJ=E(_LH.a),_LK=_LJ.a,_LL=_LJ.b,_LM=_LJ.c;if(_Lw>_Lz){return new F(function(){return _KZ(_);});}else{if(_Lz>_Lx){return new F(function(){return _KZ(_);});}else{if(_Lw>_LA){return new F(function(){return _KV(_);});}else{if(_LA>_Lx){return new F(function(){return _KV(_);});}else{var _LN=_Lz-_Lw|0;if(0>_LN){return new F(function(){return _L5(_Lu,_LN);});}else{if(_LN>=_Lu){return new F(function(){return _L5(_Lu,_LN);});}else{var _LO=E(_Lv[_LN]),_LP=E(_LO.c),_LQ=_LP.b,_LR=E(_LP.a),_LS=_LR.a,_LT=_LR.b,_LU=_LR.c,_LV=E(_LO.e),_LW=E(_LV.a),_LX=B(_Iy(_n4,_LE,_LF,_LG,_LC,_LS,_LT,_LU,_LQ)),_LY=E(_LX.a),_LZ=B(_Iy(_n4,_LY.a,_LY.b,_LY.c,_LX.b,_LE,_LF,_LG,_LC)),_M0=E(_LZ.a),_M1=_LA-_Lw|0;if(0>_M1){return new F(function(){return _La(_M1,_Lu);});}else{if(_M1>=_Lu){return new F(function(){return _La(_M1,_Lu);});}else{var _M2=E(_Lv[_M1]),_M3=E(_M2.c),_M4=_M3.b,_M5=E(_M3.a),_M6=_M5.a,_M7=_M5.b,_M8=_M5.c,_M9=E(_M2.e),_Ma=E(_M9.a),_Mb=B(_Iy(_n4,_LK,_LL,_LM,_LI,_M6,_M7,_M8,_M4)),_Mc=E(_Mb.a),_Md=B(_Iy(_n4,_Mc.a,_Mc.b,_Mc.c,_Mb.b,_LK,_LL,_LM,_LI)),_Me=E(_Md.a),_Mf=E(_M0.a)+E(_M0.b)+E(_M0.c)+E(_LZ.b)+E(_Me.a)+E(_Me.b)+E(_Me.c)+E(_Md.b);if(!_Mf){var _Mg=B(A2(_Ln,_Lt,_));return new T2(0,new T2(1,_ol,new T(function(){return E(E(_Mg).a);})),new T(function(){return E(E(_Mg).b);}));}else{var _Mh=new T(function(){return  -((B(_Jr(_nA,_LW.a,_LW.b,_LW.c,_LV.b,_LE,_LF,_LG,_LC))-B(_Jr(_nA,_Ma.a,_Ma.b,_Ma.c,_M9.b,_LK,_LL,_LM,_LI))-E(_Lo))/_Mf);}),_Mi=function(_Mj,_Mk,_Ml,_Mm,_){var _Mn=new T(function(){var _Mo=function(_Mp,_Mq,_Mr,_Ms,_Mt){if(_Mp>_LA){return E(_Mt);}else{if(_LA>_Mq){return E(_Mt);}else{var _Mu=function(_){var _Mv=newArr(_Mr,_m4),_Mw=_Mv,_Mx=function(_My,_){while(1){if(_My!=_Mr){var _=_Mw[_My]=_Ms[_My],_Mz=_My+1|0;_My=_Mz;continue;}else{return E(_);}}},_=B(_Mx(0,_)),_MA=_LA-_Mp|0;if(0>_MA){return new F(function(){return _La(_MA,_Mr);});}else{if(_MA>=_Mr){return new F(function(){return _La(_MA,_Mr);});}else{var _=_Mw[_MA]=new T(function(){var _MB=E(_Ms[_MA]),_MC=E(_MB.e),_MD=E(_MC.a),_ME=B(_Iy(_n4,_M6,_M7,_M8,_M4,_LK,_LL,_LM,_LI)),_MF=E(_ME.a),_MG=E(_Mh)*E(_Lp),_MH=B(_Iy(_n4,_MF.a,_MF.b,_MF.c,_ME.b,_MG,_MG,_MG,_MG)),_MI=E(_MH.a),_MJ=B(_IJ(_n4,_MD.a,_MD.b,_MD.c,_MC.b, -E(_MI.a), -E(_MI.b), -E(_MI.c), -E(_MH.b)));return {_:0,a:E(_MB.a),b:E(_MB.b),c:E(_MB.c),d:E(_MB.d),e:E(new T2(0,E(_MJ.a),E(_MJ.b))),f:E(_MB.f),g:E(_MB.g),h:_MB.h,i:_MB.i,j:_MB.j};});return new T4(0,E(_Mp),E(_Mq),_Mr,_Mw);}}};return new F(function(){return _EM(_Mu);});}}};if(_Mj>_Lz){return B(_Mo(_Mj,_Mk,_Ml,_Mm,new T4(0,E(_Mj),E(_Mk),_Ml,_Mm)));}else{if(_Lz>_Mk){return B(_Mo(_Mj,_Mk,_Ml,_Mm,new T4(0,E(_Mj),E(_Mk),_Ml,_Mm)));}else{var _MK=function(_){var _ML=newArr(_Ml,_m4),_MM=_ML,_MN=function(_MO,_){while(1){if(_MO!=_Ml){var _=_MM[_MO]=_Mm[_MO],_MP=_MO+1|0;_MO=_MP;continue;}else{return E(_);}}},_=B(_MN(0,_)),_MQ=_Lz-_Mj|0;if(0>_MQ){return new F(function(){return _L5(_Ml,_MQ);});}else{if(_MQ>=_Ml){return new F(function(){return _L5(_Ml,_MQ);});}else{var _=_MM[_MQ]=new T(function(){var _MR=E(_Mm[_MQ]),_MS=E(_MR.e),_MT=E(_MS.a),_MU=B(_Iy(_n4,_LS,_LT,_LU,_LQ,_LE,_LF,_LG,_LC)),_MV=E(_MU.a),_MW=E(_Mh)*E(_Lp),_MX=B(_Iy(_n4,_MV.a,_MV.b,_MV.c,_MU.b,_MW,_MW,_MW,_MW)),_MY=E(_MX.a),_MZ=B(_IJ(_n4,_MT.a,_MT.b,_MT.c,_MS.b,_MY.a,_MY.b,_MY.c,_MX.b));return {_:0,a:E(_MR.a),b:E(_MR.b),c:E(_MR.c),d:E(_MR.d),e:E(new T2(0,E(_MZ.a),E(_MZ.b))),f:E(_MR.f),g:E(_MR.g),h:_MR.h,i:_MR.i,j:_MR.j};});return new T4(0,E(_Mj),E(_Mk),_Ml,_MM);}}},_N0=B(_EM(_MK));return B(_Mo(E(_N0.a),E(_N0.b),_N0.c,_N0.d,_N0));}}});return new T2(0,_ol,_Mn);};if(!E(_Ly.f)){var _N1=B(_Mi(_Lw,_Lx,_Lu,_Lv,_)),_N2=B(A2(_Ln,new T(function(){return E(E(_N1).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_N1).a);}),new T(function(){return E(E(_N2).a);})),new T(function(){return E(E(_N2).b);}));}else{if(E(_Mh)<0){var _N3=B(A2(_Ln,_Lt,_));return new T2(0,new T2(1,_ol,new T(function(){return E(E(_N3).a);})),new T(function(){return E(E(_N3).b);}));}else{var _N4=B(_Mi(_Lw,_Lx,_Lu,_Lv,_)),_N5=B(A2(_Ln,new T(function(){return E(E(_N4).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_N4).a);}),new T(function(){return E(E(_N5).a);})),new T(function(){return E(E(_N5).b);}));}}}}}}}}}}}};return E(_Lr);}};return new F(function(){return _Lj(_Lh.a);});}},_N6=function(_,_N7){var _N8=new T(function(){return B(_Lf(E(_N7).a));}),_N9=function(_Na){var _Nb=E(_Na);return (_Nb==1)?E(new T2(1,_N8,_w)):new T2(1,_N8,new T(function(){return B(_N9(_Nb-1|0));}));},_Nc=B(_HK(B(_N9(5)),new T(function(){return E(E(_N7).b);}),_)),_Nd=new T(function(){return B(_Ii(_HJ,_Fy,_Ji,new T(function(){return E(E(_Nc).b);})));});return new T2(0,_ol,_Nd);},_Ne=function(_Nf,_Ng,_Nh,_Ni,_Nj){var _Nk=B(_8J(B(_8H(_Nf))));return new F(function(){return A3(_6X,_Nk,new T(function(){return B(A3(_8L,_Nk,_Ng,_Ni));}),new T(function(){return B(A3(_8L,_Nk,_Nh,_Nj));}));});},_Nl=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Nm=new T6(0,_KQ,_KR,_w,_Nl,_KQ,_KQ),_Nn=new T(function(){return B(_KO(_Nm));}),_No=function(_){return new F(function(){return die(_Nn);});},_Np=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Nq=new T6(0,_KQ,_KR,_w,_Np,_KQ,_KQ),_Nr=new T(function(){return B(_KO(_Nq));}),_Ns=function(_){return new F(function(){return die(_Nr);});},_Nt=function(_Nu,_Nv,_Nw,_Nx){var _Ny=new T(function(){return B(_8J(new T(function(){return B(_8H(_Nu));})));}),_Nz=B(A2(_8s,_Ny,_8q));return new F(function(){return _p9(_Nu,_Nz,B(A2(_8s,_Ny,_8r)),_Nz);});},_NA=false,_NB=true,_NC=function(_ND){var _NE=E(_ND),_NF=_NE.b,_NG=E(_NE.d),_NH=E(_NE.e),_NI=E(_NH.a),_NJ=E(_NE.g),_NK=B(A1(_NF,_NG.a)),_NL=B(_q0(_nA,_NK.a,_NK.b,_NK.c,_NJ.a,_NJ.b,_NJ.c));return {_:0,a:E(_NE.a),b:E(_NF),c:E(_NE.c),d:E(_NG),e:E(new T2(0,E(new T3(0,E(_NI.a)+E(_NL.a)*1.0e-2,E(_NI.b)+E(_NL.b)*1.0e-2,E(_NI.c)+E(_NL.c)*1.0e-2)),E(_NH.b))),f:E(_NE.f),g:E(_NJ),h:_NE.h,i:_NE.i,j:_NE.j};},_NM=new T(function(){return eval("__strict(collideBound)");}),_NN=new T(function(){return eval("__strict(mouseContact)");}),_NO=new T(function(){return eval("__strict(collide)");}),_NP=function(_NQ){var _NR=E(_NQ);if(!_NR._){return __Z;}else{return new F(function(){return _n(_NR.a,new T(function(){return B(_NP(_NR.b));},1));});}},_NS=0,_NT=new T3(0,E(_NS),E(_NS),E(_NS)),_NU=new T2(0,E(_NT),E(_NS)),_NV=function(_NW,_){var _NX=B(_Ii(_HJ,_Fy,_NC,_NW)),_NY=E(_NX.a),_NZ=E(_NX.b);if(_NY<=_NZ){var _O0=function(_O1,_O2,_O3,_O4,_O5,_){if(_O2>_O1){return new F(function(){return _Ns(_);});}else{if(_O1>_O3){return new F(function(){return _Ns(_);});}else{var _O6=new T(function(){var _O7=_O1-_O2|0;if(0>_O7){return B(_La(_O7,_O4));}else{if(_O7>=_O4){return B(_La(_O7,_O4));}else{return E(_O5[_O7]);}}}),_O8=function(_O9,_Oa,_Ob,_Oc,_Od,_){var _Oe=E(_O9);if(!_Oe._){return new T2(0,_w,new T4(0,E(_Oa),E(_Ob),_Oc,_Od));}else{var _Of=E(_Oe.a);if(_Oa>_Of){return new F(function(){return _No(_);});}else{if(_Of>_Ob){return new F(function(){return _No(_);});}else{var _Og=_Of-_Oa|0;if(0>_Og){return new F(function(){return _L5(_Oc,_Og);});}else{if(_Og>=_Oc){return new F(function(){return _L5(_Oc,_Og);});}else{var _Oh=__app2(E(_NO),B(_EW(E(_O6))),B(_EW(E(_Od[_Og])))),_Oi=__arr2lst(0,_Oh),_Oj=B(_Gb(_Oi,_)),_Ok=B(_O8(_Oe.b,_Oa,_Ob,_Oc,_Od,_)),_Ol=new T(function(){var _Om=new T(function(){return _O1!=_Of;}),_On=function(_Oo){var _Op=E(_Oo);if(!_Op._){return __Z;}else{var _Oq=_Op.b,_Or=E(_Op.a),_Os=E(_Or.b),_Ot=E(_Or.a),_Ou=E(_Ot.a),_Ov=E(_Ot.b),_Ow=E(_Ot.c),_Ox=E(_Os.a),_Oy=E(_Os.b),_Oz=E(_Os.c),_OA=E(_Or.c),_OB=_OA.a,_OC=_OA.b,_OD=E(_Or.e),_OE=E(_Or.d),_OF=_OE.a,_OG=_OE.b,_OH=E(_Or.f),_OI=new T(function(){var _OJ=B(_p9(_nA,_OH.a,_OH.b,_OH.c)),_OK=Math.sqrt(B(_Ne(_nA,_OF,_OG,_OF,_OG)));return new T3(0,_OK*E(_OJ.a),_OK*E(_OJ.b),_OK*E(_OJ.c));}),_OL=new T(function(){var _OM=B(_p9(_nA,_OD.a,_OD.b,_OD.c)),_ON=Math.sqrt(B(_Ne(_nA,_OB,_OC,_OB,_OC)));return new T3(0,_ON*E(_OM.a),_ON*E(_OM.b),_ON*E(_OM.c));}),_OO=new T(function(){var _OP=B(_Nt(_nA,_Ox,_Oy,_Oz));return new T3(0,E(_OP.a),E(_OP.b),E(_OP.c));}),_OQ=new T(function(){var _OR=B(_Nt(_nA,_Ou,_Ov,_Ow));return new T3(0,E(_OR.a),E(_OR.b),E(_OR.c));}),_OS=_Ox+ -_Ou,_OT=_Oy+ -_Ov,_OU=_Oz+ -_Ow,_OV=new T(function(){return Math.sqrt(B(_oZ(_nA,_OS,_OT,_OU,_OS,_OT,_OU)));}),_OW=new T(function(){var _OX=1/E(_OV);return new T3(0,_OS*_OX,_OT*_OX,_OU*_OX);}),_OY=new T(function(){if(!E(_Or.g)){return E(_OW);}else{var _OZ=E(_OW);return new T3(0,-1*E(_OZ.a),-1*E(_OZ.b),-1*E(_OZ.c));}}),_P0=new T(function(){if(!E(_Or.h)){return E(_OW);}else{var _P1=E(_OW);return new T3(0,-1*E(_P1.a),-1*E(_P1.b),-1*E(_P1.c));}});return (!E(_Om))?new T2(1,new T(function(){var _P2=E(_OY),_P3=E(_P2.b),_P4=E(_P2.c),_P5=E(_P2.a),_P6=E(_OQ),_P7=E(_P6.c),_P8=E(_P6.b),_P9=E(_P6.a),_Pa=E(_OL),_Pb=E(_Pa.c),_Pc=E(_Pa.b),_Pd=E(_Pa.a),_Pe=_P3*_P7-_P8*_P4,_Pf=_P4*_P9-_P7*_P5,_Pg=_P5*_P8-_P9*_P3,_Ph=B(_oZ(_nA,_Pf*_Pb-_Pc*_Pg,_Pg*_Pd-_Pb*_Pe,_Pe*_Pc-_Pd*_Pf,_P9,_P8,_P7));return new T6(0,_O1,_Of,E(new T2(0,E(new T3(0,E(_Pe),E(_Pf),E(_Pg))),E(_Ph))),E(_NU),_OV,_NA);}),new T2(1,new T(function(){var _Pi=E(_P0),_Pj=E(_Pi.b),_Pk=E(_Pi.c),_Pl=E(_Pi.a),_Pm=E(_OO),_Pn=E(_Pm.c),_Po=E(_Pm.b),_Pp=E(_Pm.a),_Pq=E(_OI),_Pr=E(_Pq.c),_Ps=E(_Pq.b),_Pt=E(_Pq.a),_Pu=_Pj*_Pn-_Po*_Pk,_Pv=_Pk*_Pp-_Pn*_Pl,_Pw=_Pl*_Po-_Pp*_Pj,_Px=B(_oZ(_nA,_Pv*_Pr-_Ps*_Pw,_Pw*_Pt-_Pr*_Pu,_Pu*_Ps-_Pt*_Pv,_Pp,_Po,_Pn));return new T6(0,_O1,_Of,E(_NU),E(new T2(0,E(new T3(0,E(_Pu),E(_Pv),E(_Pw))),E(_Px))),_OV,_NA);}),new T(function(){return B(_On(_Oq));}))):new T2(1,new T(function(){var _Py=E(_OY),_Pz=E(_Py.b),_PA=E(_Py.c),_PB=E(_Py.a),_PC=E(_OQ),_PD=_PC.a,_PE=_PC.b,_PF=_PC.c,_PG=B(_q0(_nA,_PB,_Pz,_PA,_PD,_PE,_PF)),_PH=E(_OL),_PI=E(_PH.c),_PJ=E(_PH.b),_PK=E(_PH.a),_PL=B(_oZ(_nA,_Pz*_PI-_PJ*_PA,_PA*_PK-_PI*_PB,_PB*_PJ-_PK*_Pz,_PD,_PE,_PF)),_PM=E(_P0),_PN=E(_PM.b),_PO=E(_PM.c),_PP=E(_PM.a),_PQ=E(_OO),_PR=_PQ.a,_PS=_PQ.b,_PT=_PQ.c,_PU=B(_q0(_nA,_PP,_PN,_PO,_PR,_PS,_PT)),_PV=E(_OI),_PW=E(_PV.c),_PX=E(_PV.b),_PY=E(_PV.a),_PZ=B(_oZ(_nA,_PN*_PW-_PX*_PO,_PO*_PY-_PW*_PP,_PP*_PX-_PY*_PN,_PR,_PS,_PT));return new T6(0,_O1,_Of,E(new T2(0,E(new T3(0,E(_PG.a),E(_PG.b),E(_PG.c))),E(_PL))),E(new T2(0,E(new T3(0,E(_PU.a),E(_PU.b),E(_PU.c))),E(_PZ))),_OV,_NB);}),new T(function(){return B(_On(_Oq));}));}};return B(_On(_Oj));});return new T2(0,new T2(1,_Ol,new T(function(){return E(E(_Ok).a);})),new T(function(){return E(E(_Ok).b);}));}}}}}},_Q0=B(_O8(B(_wI(_O1,_NZ)),_O2,_O3,_O4,_O5,_)),_Q1=E(_O6),_Q2=E(_Q1.d).a,_Q3=__app1(E(_NM),B(_EW(_Q1))),_Q4=__arr2lst(0,_Q3),_Q5=B(_Gb(_Q4,_)),_Q6=__app1(E(_NN),_O1),_Q7=__arr2lst(0,_Q6),_Q8=B(_Gb(_Q7,_));if(_O1!=_NZ){var _Q9=E(_Q0),_Qa=E(_Q9.b),_Qb=B(_O0(_O1+1|0,E(_Qa.a),E(_Qa.b),_Qa.c,_Qa.d,_)),_Qc=new T(function(){var _Qd=new T(function(){var _Qe=E(_Q2),_Qf=B(_Nt(_nA,_Qe.a,_Qe.b,_Qe.c));return new T3(0,E(_Qf.a),E(_Qf.b),E(_Qf.c));}),_Qg=new T(function(){var _Qh=new T(function(){return B(_NP(_Q9.a));}),_Qi=function(_Qj){var _Qk=E(_Qj);if(!_Qk._){return E(_Qh);}else{var _Ql=E(_Qk.a),_Qm=E(_Ql.b),_Qn=E(_Ql.a),_Qo=E(_Qn.a),_Qp=E(_Qn.b),_Qq=E(_Qn.c),_Qr=E(_Ql.c),_Qs=_Qr.a,_Qt=_Qr.b,_Qu=E(_Ql.e);return new T2(1,new T(function(){var _Qv=E(_Qm.a)+ -_Qo,_Qw=E(_Qm.b)+ -_Qp,_Qx=E(_Qm.c)+ -_Qq,_Qy=B(_Nt(_nA,_Qo,_Qp,_Qq)),_Qz=_Qy.a,_QA=_Qy.b,_QB=_Qy.c,_QC=Math.sqrt(B(_oZ(_nA,_Qv,_Qw,_Qx,_Qv,_Qw,_Qx))),_QD=1/_QC,_QE=_Qv*_QD,_QF=_Qw*_QD,_QG=_Qx*_QD,_QH=B(_q0(_nA,_QE,_QF,_QG,_Qz,_QA,_QB)),_QI=B(_p9(_nA,_Qu.a,_Qu.b,_Qu.c)),_QJ=Math.sqrt(B(_Ne(_nA,_Qs,_Qt,_Qs,_Qt))),_QK=_QJ*E(_QI.a),_QL=_QJ*E(_QI.b),_QM=_QJ*E(_QI.c),_QN=B(_oZ(_nA,_QF*_QM-_QL*_QG,_QG*_QK-_QM*_QE,_QE*_QL-_QK*_QF,_Qz,_QA,_QB));return new T6(0,_O1,_O1,E(new T2(0,E(new T3(0,E(_QH.a),E(_QH.b),E(_QH.c))),E(_QN))),E(_NU),_QC,_NB);}),new T(function(){return B(_Qi(_Qk.b));}));}};return B(_Qi(_Q5));}),_QO=function(_QP){var _QQ=E(_QP);if(!_QQ._){return E(_Qg);}else{var _QR=E(_QQ.a),_QS=E(_QR.b),_QT=new T(function(){var _QU=E(_Q2),_QV=E(_QS.c)+ -E(_QU.c),_QW=E(_QS.b)+ -E(_QU.b),_QX=E(_QS.a)+ -E(_QU.a),_QY=Math.sqrt(B(_oZ(_nA,_QX,_QW,_QV,_QX,_QW,_QV))),_QZ=function(_R0,_R1,_R2){var _R3=E(_Qd),_R4=_R3.a,_R5=_R3.b,_R6=_R3.c,_R7=B(_q0(_nA,_R0,_R1,_R2,_R4,_R5,_R6)),_R8=B(_oZ(_nA,_R1*0-0*_R2,_R2*0-0*_R0,_R0*0-0*_R1,_R4,_R5,_R6));return new T6(0,_O1,_O1,new T2(0,E(new T3(0,E(_R7.a),E(_R7.b),E(_R7.c))),E(_R8)),_NU,_QY,_NB);};if(!E(_QR.g)){var _R9=1/_QY,_Ra=B(_QZ(_QX*_R9,_QW*_R9,_QV*_R9));return new T6(0,_Ra.a,_Ra.b,E(_Ra.c),E(_Ra.d),_Ra.e,_Ra.f);}else{var _Rb=1/_QY,_Rc=B(_QZ(-1*_QX*_Rb,-1*_QW*_Rb,-1*_QV*_Rb));return new T6(0,_Rc.a,_Rc.b,E(_Rc.c),E(_Rc.d),_Rc.e,_Rc.f);}});return new T2(1,_QT,new T(function(){return B(_QO(_QQ.b));}));}};return B(_QO(_Q8));});return new T2(0,new T2(1,_Qc,new T(function(){return E(E(_Qb).a);})),new T(function(){return E(E(_Qb).b);}));}else{var _Rd=new T(function(){var _Re=new T(function(){var _Rf=E(_Q2),_Rg=B(_Nt(_nA,_Rf.a,_Rf.b,_Rf.c));return new T3(0,E(_Rg.a),E(_Rg.b),E(_Rg.c));}),_Rh=new T(function(){var _Ri=new T(function(){return B(_NP(E(_Q0).a));}),_Rj=function(_Rk){var _Rl=E(_Rk);if(!_Rl._){return E(_Ri);}else{var _Rm=E(_Rl.a),_Rn=E(_Rm.b),_Ro=E(_Rm.a),_Rp=E(_Ro.a),_Rq=E(_Ro.b),_Rr=E(_Ro.c),_Rs=E(_Rm.c),_Rt=_Rs.a,_Ru=_Rs.b,_Rv=E(_Rm.e);return new T2(1,new T(function(){var _Rw=E(_Rn.a)+ -_Rp,_Rx=E(_Rn.b)+ -_Rq,_Ry=E(_Rn.c)+ -_Rr,_Rz=B(_Nt(_nA,_Rp,_Rq,_Rr)),_RA=_Rz.a,_RB=_Rz.b,_RC=_Rz.c,_RD=Math.sqrt(B(_oZ(_nA,_Rw,_Rx,_Ry,_Rw,_Rx,_Ry))),_RE=1/_RD,_RF=_Rw*_RE,_RG=_Rx*_RE,_RH=_Ry*_RE,_RI=B(_q0(_nA,_RF,_RG,_RH,_RA,_RB,_RC)),_RJ=B(_p9(_nA,_Rv.a,_Rv.b,_Rv.c)),_RK=Math.sqrt(B(_Ne(_nA,_Rt,_Ru,_Rt,_Ru))),_RL=_RK*E(_RJ.a),_RM=_RK*E(_RJ.b),_RN=_RK*E(_RJ.c),_RO=B(_oZ(_nA,_RG*_RN-_RM*_RH,_RH*_RL-_RN*_RF,_RF*_RM-_RL*_RG,_RA,_RB,_RC));return new T6(0,_O1,_O1,E(new T2(0,E(new T3(0,E(_RI.a),E(_RI.b),E(_RI.c))),E(_RO))),E(_NU),_RD,_NB);}),new T(function(){return B(_Rj(_Rl.b));}));}};return B(_Rj(_Q5));}),_RP=function(_RQ){var _RR=E(_RQ);if(!_RR._){return E(_Rh);}else{var _RS=E(_RR.a),_RT=E(_RS.b),_RU=new T(function(){var _RV=E(_Q2),_RW=E(_RT.c)+ -E(_RV.c),_RX=E(_RT.b)+ -E(_RV.b),_RY=E(_RT.a)+ -E(_RV.a),_RZ=Math.sqrt(B(_oZ(_nA,_RY,_RX,_RW,_RY,_RX,_RW))),_S0=function(_S1,_S2,_S3){var _S4=E(_Re),_S5=_S4.a,_S6=_S4.b,_S7=_S4.c,_S8=B(_q0(_nA,_S1,_S2,_S3,_S5,_S6,_S7)),_S9=B(_oZ(_nA,_S2*0-0*_S3,_S3*0-0*_S1,_S1*0-0*_S2,_S5,_S6,_S7));return new T6(0,_O1,_O1,new T2(0,E(new T3(0,E(_S8.a),E(_S8.b),E(_S8.c))),E(_S9)),_NU,_RZ,_NB);};if(!E(_RS.g)){var _Sa=1/_RZ,_Sb=B(_S0(_RY*_Sa,_RX*_Sa,_RW*_Sa));return new T6(0,_Sb.a,_Sb.b,E(_Sb.c),E(_Sb.d),_Sb.e,_Sb.f);}else{var _Sc=1/_RZ,_Sd=B(_S0(-1*_RY*_Sc,-1*_RX*_Sc,-1*_RW*_Sc));return new T6(0,_Sd.a,_Sd.b,E(_Sd.c),E(_Sd.d),_Sd.e,_Sd.f);}});return new T2(1,_RU,new T(function(){return B(_RP(_RR.b));}));}};return B(_RP(_Q8));});return new T2(0,new T2(1,_Rd,_w),new T(function(){return E(E(_Q0).b);}));}}}},_Se=B(_O0(_NY,_NY,_NZ,_NX.c,_NX.d,_));return new F(function(){return _N6(_,_Se);});}else{return new F(function(){return _N6(_,new T2(0,_w,_NX));});}},_Sf=new T(function(){return eval("__strict(passObject)");}),_Sg=new T(function(){return eval("__strict(refresh)");}),_Sh=function(_Si,_){var _Sj=__app0(E(_Sg)),_Sk=__app0(E(_F1)),_Sl=E(_Si),_Sm=_Sl.c,_Sn=_Sl.d,_So=E(_Sl.a),_Sp=E(_Sl.b);if(_So<=_Sp){if(_So>_Sp){return E(_EZ);}else{if(0>=_Sm){return new F(function(){return _Fc(_Sm,0);});}else{var _Sq=E(_Sf),_Sr=__app2(_Sq,_So,B(_EW(E(_Sn[0]))));if(_So!=_Sp){var _Ss=function(_St,_){if(_So>_St){return E(_EZ);}else{if(_St>_Sp){return E(_EZ);}else{var _Su=_St-_So|0;if(0>_Su){return new F(function(){return _Fc(_Sm,_Su);});}else{if(_Su>=_Sm){return new F(function(){return _Fc(_Sm,_Su);});}else{var _Sv=__app2(_Sq,_St,B(_EW(E(_Sn[_Su]))));if(_St!=_Sp){var _Sw=B(_Ss(_St+1|0,_));return new T2(1,_ol,_Sw);}else{return _Fh;}}}}}},_Sx=B(_Ss(_So+1|0,_)),_Sy=__app0(E(_F0)),_Sz=B(_NV(_Sl,_));return new T(function(){return E(E(_Sz).b);});}else{var _SA=__app0(E(_F0)),_SB=B(_NV(_Sl,_));return new T(function(){return E(E(_SB).b);});}}}}else{var _SC=__app0(E(_F0)),_SD=B(_NV(_Sl,_));return new T(function(){return E(E(_SD).b);});}},_SE=function(_SF,_){while(1){var _SG=E(_SF);if(!_SG._){return _ol;}else{var _SH=_SG.b,_SI=E(_SG.a);switch(_SI._){case 0:var _SJ=B(A1(_SI.a,_));_SF=B(_n(_SH,new T2(1,_SJ,_w)));continue;case 1:_SF=B(_n(_SH,_SI.a));continue;default:_SF=_SH;continue;}}}},_SK=function(_SL,_SM,_){var _SN=E(_SL);switch(_SN._){case 0:var _SO=B(A1(_SN.a,_));return new F(function(){return _SE(B(_n(_SM,new T2(1,_SO,_w))),_);});break;case 1:return new F(function(){return _SE(B(_n(_SM,_SN.a)),_);});break;default:return new F(function(){return _SE(_SM,_);});}},_SP=new T0(2),_SQ=function(_SR){return new T0(2);},_SS=function(_ST,_SU,_SV){return function(_){var _SW=E(_ST),_SX=rMV(_SW),_SY=E(_SX);if(!_SY._){var _SZ=new T(function(){var _T0=new T(function(){return B(A1(_SV,_ol));});return B(_n(_SY.b,new T2(1,new T2(0,_SU,function(_T1){return E(_T0);}),_w)));}),_=wMV(_SW,new T2(0,_SY.a,_SZ));return _SP;}else{var _T2=E(_SY.a);if(!_T2._){var _=wMV(_SW,new T2(0,_SU,_w));return new T(function(){return B(A1(_SV,_ol));});}else{var _=wMV(_SW,new T1(1,_T2.b));return new T1(1,new T2(1,new T(function(){return B(A1(_SV,_ol));}),new T2(1,new T(function(){return B(A2(_T2.a,_SU,_SQ));}),_w)));}}};},_T3=new T(function(){return E(_ue);}),_T4=new T(function(){return eval("window.requestAnimationFrame");}),_T5=new T1(1,_w),_T6=function(_T7,_T8){return function(_){var _T9=E(_T7),_Ta=rMV(_T9),_Tb=E(_Ta);if(!_Tb._){var _Tc=_Tb.a,_Td=E(_Tb.b);if(!_Td._){var _=wMV(_T9,_T5);return new T(function(){return B(A1(_T8,_Tc));});}else{var _Te=E(_Td.a),_=wMV(_T9,new T2(0,_Te.a,_Td.b));return new T1(1,new T2(1,new T(function(){return B(A1(_T8,_Tc));}),new T2(1,new T(function(){return B(A1(_Te.b,_SQ));}),_w)));}}else{var _Tf=new T(function(){var _Tg=function(_Th){var _Ti=new T(function(){return B(A1(_T8,_Th));});return function(_Tj){return E(_Ti);};};return B(_n(_Tb.a,new T2(1,_Tg,_w)));}),_=wMV(_T9,new T1(1,_Tf));return _SP;}};},_Tk=function(_Tl,_Tm){return new T1(0,B(_T6(_Tl,_Tm)));},_Tn=function(_To,_Tp){var _Tq=new T(function(){return new T1(0,B(_SS(_To,_ol,_SQ)));});return function(_){var _Tr=__createJSFunc(2,function(_Ts,_){var _Tt=B(_SK(_Tq,_w,_));return _T3;}),_Tu=__app1(E(_T4),_Tr);return new T(function(){return B(_Tk(_To,_Tp));});};},_Tv=new T1(1,_w),_Tw=function(_Tx,_Ty,_){var _Tz=function(_){var _TA=nMV(_Tx),_TB=_TA;return new T(function(){var _TC=new T(function(){return B(_TD(_));}),_TE=function(_){var _TF=rMV(_TB),_TG=B(A2(_Ty,_TF,_)),_=wMV(_TB,_TG),_TH=function(_){var _TI=nMV(_Tv);return new T(function(){return new T1(0,B(_Tn(_TI,function(_TJ){return E(_TC);})));});};return new T1(0,_TH);},_TK=new T(function(){return new T1(0,_TE);}),_TD=function(_TL){return E(_TK);};return B(_TD(_));});};return new F(function(){return _SK(new T1(0,_Tz),_w,_);});},_TM=new T(function(){return eval("__strict(setBounds)");}),_TN=function(_){var _TO=__app3(E(_lt),E(_lu),E(_lX),E(_ls)),_TP=__app2(E(_TM),E(_iI),E(_iF));return new F(function(){return _Tw(_EP,_Sh,_);});},_TQ=function(_){return new F(function(){return _TN(_);});};
var hasteMain = function() {B(A(_TQ, [0]));};window.onload = hasteMain;