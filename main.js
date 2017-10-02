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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(",y:"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr(",z:"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("})"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=new T(function(){return B(unCStr("-("));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr(")"));}),_I=new T1(0,_H),_J=new T2(1,_I,_w),_K=new T(function(){return B(unCStr("."));}),_L=new T1(0,0),_M=function(_N){while(1){var _O=E(_N);if(!_O._){_N=new T1(1,I_fromInt(_O.a));continue;}else{return new F(function(){return I_toString(_O.a);});}}},_P=function(_Q,_R){return new F(function(){return _n(fromJSStr(B(_M(_Q))),_R);});},_S=function(_T,_U){var _V=E(_T);if(!_V._){var _W=_V.a,_X=E(_U);return (_X._==0)?_W<_X.a:I_compareInt(_X.a,_W)>0;}else{var _Y=_V.a,_Z=E(_U);return (_Z._==0)?I_compareInt(_Y,_Z.a)<0:I_compare(_Y,_Z.a)<0;}},_10=41,_11=40,_12=new T1(0,0),_13=function(_14,_15,_16){if(_14<=6){return new F(function(){return _P(_15,_16);});}else{if(!B(_S(_15,_12))){return new F(function(){return _P(_15,_16);});}else{return new T2(1,_11,new T(function(){return B(_n(fromJSStr(B(_M(_15))),new T2(1,_10,_16)));}));}}},_17=new T(function(){return B(_13(0,_L,_w));}),_18=new T(function(){return B(_n(_17,_K));}),_19=new T1(0,_18),_1a=new T2(1,_19,_J),_1b=new T2(1,_G,_1a),_1c=new T1(1,_1b),_1d=new T2(1,_1c,_E),_1e=new T2(1,_B,_1d),_1f=new T2(1,_1c,_1e),_1g=new T2(1,_z,_1f),_1h=new T2(1,_1c,_1g),_1i=new T(function(){return B(unCStr("({x:"));}),_1j=new T1(0,_1i),_1k=new T2(1,_1j,_1h),_1l=function(_1m){return E(_1m);},_1n=new T(function(){return toJSStr(B(_e(_x,_1l,_1k)));}),_1o=new T1(0,1),_1p=new T(function(){return B(_13(0,_1o,_w));}),_1q=new T(function(){return B(_n(_1p,_K));}),_1r=new T1(0,_1q),_1s=new T2(1,_1r,_J),_1t=new T2(1,_G,_1s),_1u=new T(function(){return toJSStr(B(_e(_x,_1l,_1t)));}),_1v=function(_1w,_1x,_1y){var _1z=E(_1y);if(!_1z._){return new F(function(){return A1(_1x,_1z.a);});}else{var _1A=new T(function(){return B(_0(_1w));}),_1B=new T(function(){return B(_2(_1w));}),_1C=function(_1D){var _1E=E(_1D);if(!_1E._){return E(_1B);}else{return new F(function(){return A2(_1A,new T(function(){return B(_1v(_1w,_1x,_1E.a));}),new T(function(){return B(_1C(_1E.b));}));});}};return new F(function(){return _1C(_1z.a);});}},_1F=function(_1G,_1H,_1I){var _1J=new T(function(){return B(_0(_1G));}),_1K=new T(function(){return B(_2(_1G));}),_1L=function(_1M){var _1N=E(_1M);if(!_1N._){return E(_1K);}else{return new F(function(){return A2(_1J,new T(function(){return B(_1v(_1G,_1H,_1N.a));}),new T(function(){return B(_1L(_1N.b));}));});}};return new F(function(){return _1L(_1I);});},_1O=new T(function(){return B(unCStr("-("));}),_1P=new T1(0,_1O),_1Q=new T(function(){return B(unCStr(")"));}),_1R=new T1(0,_1Q),_1S=new T2(1,_1R,_w),_1T=new T(function(){return B(unCStr("."));}),_1U=new T(function(){return B(_13(0,_1o,_w));}),_1V=new T(function(){return B(_n(_1U,_1T));}),_1W=new T1(0,_1V),_1X=new T2(1,_1W,_1S),_1Y=new T2(1,_1P,_1X),_1Z=new T(function(){return toJSStr(B(_1F(_x,_1l,_1Y)));}),_20=new T(function(){return eval("__strict(compile)");}),_21=new T(function(){return B(unCStr(","));}),_22=new T1(0,_21),_23=new T(function(){return B(unCStr("pow("));}),_24=new T1(0,_23),_25=function(_26,_27){return new T1(1,new T2(1,_24,new T2(1,_26,new T2(1,_22,new T2(1,_27,_1S)))));},_28=new T(function(){return B(unCStr("acos("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1S)));},_2c=new T(function(){return B(unCStr("acosh("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1S)));},_2g=new T(function(){return B(unCStr("asin("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1S)));},_2k=new T(function(){return B(unCStr("asinh("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1S)));},_2o=new T(function(){return B(unCStr("atan("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1S)));},_2s=new T(function(){return B(unCStr("atanh("));}),_2t=new T1(0,_2s),_2u=function(_2v){return new T1(1,new T2(1,_2t,new T2(1,_2v,_1S)));},_2w=new T(function(){return B(unCStr("cos("));}),_2x=new T1(0,_2w),_2y=function(_2z){return new T1(1,new T2(1,_2x,new T2(1,_2z,_1S)));},_2A=new T(function(){return B(unCStr("cosh("));}),_2B=new T1(0,_2A),_2C=function(_2D){return new T1(1,new T2(1,_2B,new T2(1,_2D,_1S)));},_2E=new T(function(){return B(unCStr("exp("));}),_2F=new T1(0,_2E),_2G=function(_2H){return new T1(1,new T2(1,_2F,new T2(1,_2H,_1S)));},_2I=new T(function(){return B(unCStr("log("));}),_2J=new T1(0,_2I),_2K=function(_2L){return new T1(1,new T2(1,_2J,new T2(1,_2L,_1S)));},_2M=new T(function(){return B(unCStr(")/log("));}),_2N=new T1(0,_2M),_2O=function(_2P,_2Q){return new T1(1,new T2(1,_2J,new T2(1,_2Q,new T2(1,_2N,new T2(1,_2P,_1S)))));},_2R=new T(function(){return B(unCStr("pi"));}),_2S=new T1(0,_2R),_2T=new T(function(){return B(unCStr("sin("));}),_2U=new T1(0,_2T),_2V=function(_2W){return new T1(1,new T2(1,_2U,new T2(1,_2W,_1S)));},_2X=new T(function(){return B(unCStr("sinh("));}),_2Y=new T1(0,_2X),_2Z=function(_30){return new T1(1,new T2(1,_2Y,new T2(1,_30,_1S)));},_31=new T(function(){return B(unCStr("sqrt("));}),_32=new T1(0,_31),_33=function(_34){return new T1(1,new T2(1,_32,new T2(1,_34,_1S)));},_35=new T(function(){return B(unCStr("tan("));}),_36=new T1(0,_35),_37=function(_38){return new T1(1,new T2(1,_36,new T2(1,_38,_1S)));},_39=new T(function(){return B(unCStr("tanh("));}),_3a=new T1(0,_39),_3b=function(_3c){return new T1(1,new T2(1,_3a,new T2(1,_3c,_1S)));},_3d=new T(function(){return B(unCStr("("));}),_3e=new T1(0,_3d),_3f=new T(function(){return B(unCStr(")/("));}),_3g=new T1(0,_3f),_3h=function(_3i,_3j){return new T1(1,new T2(1,_3e,new T2(1,_3i,new T2(1,_3g,new T2(1,_3j,_1S)))));},_3k=new T1(0,1),_3l=function(_3m,_3n){var _3o=E(_3m);if(!_3o._){var _3p=_3o.a,_3q=E(_3n);if(!_3q._){var _3r=_3q.a;return (_3p!=_3r)?(_3p>_3r)?2:0:1;}else{var _3s=I_compareInt(_3q.a,_3p);return (_3s<=0)?(_3s>=0)?1:2:0;}}else{var _3t=_3o.a,_3u=E(_3n);if(!_3u._){var _3v=I_compareInt(_3t,_3u.a);return (_3v>=0)?(_3v<=0)?1:2:0;}else{var _3w=I_compare(_3t,_3u.a);return (_3w>=0)?(_3w<=0)?1:2:0;}}},_3x=new T(function(){return B(unCStr("base"));}),_3y=new T(function(){return B(unCStr("GHC.Exception"));}),_3z=new T(function(){return B(unCStr("ArithException"));}),_3A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3x,_3y,_3z),_3B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3A,_w,_w),_3C=function(_3D){return E(_3B);},_3E=function(_3F){return E(E(_3F).a);},_3G=function(_3H,_3I,_3J){var _3K=B(A1(_3H,_)),_3L=B(A1(_3I,_)),_3M=hs_eqWord64(_3K.a,_3L.a);if(!_3M){return __Z;}else{var _3N=hs_eqWord64(_3K.b,_3L.b);return (!_3N)?__Z:new T1(1,_3J);}},_3O=function(_3P){var _3Q=E(_3P);return new F(function(){return _3G(B(_3E(_3Q.a)),_3C,_3Q.b);});},_3R=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3S=new T(function(){return B(unCStr("denormal"));}),_3T=new T(function(){return B(unCStr("divide by zero"));}),_3U=new T(function(){return B(unCStr("loss of precision"));}),_3V=new T(function(){return B(unCStr("arithmetic underflow"));}),_3W=new T(function(){return B(unCStr("arithmetic overflow"));}),_3X=function(_3Y,_3Z){switch(E(_3Y)){case 0:return new F(function(){return _n(_3W,_3Z);});break;case 1:return new F(function(){return _n(_3V,_3Z);});break;case 2:return new F(function(){return _n(_3U,_3Z);});break;case 3:return new F(function(){return _n(_3T,_3Z);});break;case 4:return new F(function(){return _n(_3S,_3Z);});break;default:return new F(function(){return _n(_3R,_3Z);});}},_40=function(_41){return new F(function(){return _3X(_41,_w);});},_42=function(_43,_44,_45){return new F(function(){return _3X(_44,_45);});},_46=44,_47=93,_48=91,_49=function(_4a,_4b,_4c){var _4d=E(_4b);if(!_4d._){return new F(function(){return unAppCStr("[]",_4c);});}else{var _4e=new T(function(){var _4f=new T(function(){var _4g=function(_4h){var _4i=E(_4h);if(!_4i._){return E(new T2(1,_47,_4c));}else{var _4j=new T(function(){return B(A2(_4a,_4i.a,new T(function(){return B(_4g(_4i.b));})));});return new T2(1,_46,_4j);}};return B(_4g(_4d.b));});return B(A2(_4a,_4d.a,_4f));});return new T2(1,_48,_4e);}},_4k=function(_4l,_4m){return new F(function(){return _49(_3X,_4l,_4m);});},_4n=new T3(0,_42,_40,_4k),_4o=new T(function(){return new T5(0,_3C,_4n,_4p,_3O,_40);}),_4p=function(_4q){return new T2(0,_4o,_4q);},_4r=3,_4s=new T(function(){return B(_4p(_4r));}),_4t=new T(function(){return die(_4s);}),_4u=function(_4v,_4w){var _4x=E(_4v);return (_4x._==0)?_4x.a*Math.pow(2,_4w):I_toNumber(_4x.a)*Math.pow(2,_4w);},_4y=function(_4z,_4A){var _4B=E(_4z);if(!_4B._){var _4C=_4B.a,_4D=E(_4A);return (_4D._==0)?_4C==_4D.a:(I_compareInt(_4D.a,_4C)==0)?true:false;}else{var _4E=_4B.a,_4F=E(_4A);return (_4F._==0)?(I_compareInt(_4E,_4F.a)==0)?true:false:(I_compare(_4E,_4F.a)==0)?true:false;}},_4G=function(_4H){var _4I=E(_4H);if(!_4I._){return E(_4I.a);}else{return new F(function(){return I_toInt(_4I.a);});}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a,_4Q=addC(_4N,_4P);if(!E(_4Q.b)){return new T1(0,_4Q.a);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R._){_4K=_4M;_4L=new T1(1,I_fromInt(_4R.a));continue;}else{return new T1(1,I_add(_4M.a,_4R.a));}}}},_4S=function(_4T,_4U){while(1){var _4V=E(_4T);if(!_4V._){var _4W=E(_4V.a);if(_4W==(-2147483648)){_4T=new T1(1,I_fromInt(-2147483648));continue;}else{var _4X=E(_4U);if(!_4X._){var _4Y=_4X.a;return new T2(0,new T1(0,quot(_4W,_4Y)),new T1(0,_4W%_4Y));}else{_4T=new T1(1,I_fromInt(_4W));_4U=_4X;continue;}}}else{var _4Z=E(_4U);if(!_4Z._){_4T=_4V;_4U=new T1(1,I_fromInt(_4Z.a));continue;}else{var _50=I_quotRem(_4V.a,_4Z.a);return new T2(0,new T1(1,_50.a),new T1(1,_50.b));}}}},_51=new T1(0,0),_52=function(_53,_54){while(1){var _55=E(_53);if(!_55._){_53=new T1(1,I_fromInt(_55.a));continue;}else{return new T1(1,I_shiftLeft(_55.a,_54));}}},_56=function(_57,_58,_59){if(!B(_4y(_59,_51))){var _5a=B(_4S(_58,_59)),_5b=_5a.a;switch(B(_3l(B(_52(_5a.b,1)),_59))){case 0:return new F(function(){return _4u(_5b,_57);});break;case 1:if(!(B(_4G(_5b))&1)){return new F(function(){return _4u(_5b,_57);});}else{return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}break;default:return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}}else{return E(_4t);}},_5c=function(_5d,_5e){var _5f=E(_5d);if(!_5f._){var _5g=_5f.a,_5h=E(_5e);return (_5h._==0)?_5g>_5h.a:I_compareInt(_5h.a,_5g)<0;}else{var _5i=_5f.a,_5j=E(_5e);return (_5j._==0)?I_compareInt(_5i,_5j.a)>0:I_compare(_5i,_5j.a)>0;}},_5k=new T1(0,1),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5n=new T(function(){return B(unCStr("PatternMatchFail"));}),_5o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5l,_5m,_5n),_5p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5o,_w,_w),_5q=function(_5r){return E(_5p);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _3G(B(_3E(_5u.a)),_5q,_5u.b);});},_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return new T2(0,_5z,_5y);},_5A=function(_5B,_5C){return new F(function(){return _n(E(_5B).a,_5C);});},_5D=function(_5E,_5F){return new F(function(){return _49(_5A,_5E,_5F);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _n(E(_5I).a,_5J);});},_5K=new T3(0,_5G,_5v,_5D),_5z=new T(function(){return new T5(0,_5q,_5K,_5x,_5s,_5v);}),_5L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5M=function(_5N){return E(E(_5N).c);},_5O=function(_5P,_5Q){return new F(function(){return die(new T(function(){return B(A2(_5M,_5Q,_5P));}));});},_5R=function(_5S,_4q){return new F(function(){return _5O(_5S,_4q);});},_5T=function(_5U,_5V){var _5W=E(_5V);if(!_5W._){return new T2(0,_w,_w);}else{var _5X=_5W.a;if(!B(A1(_5U,_5X))){return new T2(0,_w,_5W);}else{var _5Y=new T(function(){var _5Z=B(_5T(_5U,_5W.b));return new T2(0,_5Z.a,_5Z.b);});return new T2(0,new T2(1,_5X,new T(function(){return E(E(_5Y).a);})),new T(function(){return E(E(_5Y).b);}));}}},_60=32,_61=new T(function(){return B(unCStr("\n"));}),_62=function(_63){return (E(_63)==124)?false:true;},_64=function(_65,_66){var _67=B(_5T(_62,B(unCStr(_65)))),_68=_67.a,_69=function(_6a,_6b){var _6c=new T(function(){var _6d=new T(function(){return B(_n(_66,new T(function(){return B(_n(_6b,_61));},1)));});return B(unAppCStr(": ",_6d));},1);return new F(function(){return _n(_6a,_6c);});},_6e=E(_67.b);if(!_6e._){return new F(function(){return _69(_68,_w);});}else{if(E(_6e.a)==124){return new F(function(){return _69(_68,new T2(1,_60,_6e.b));});}else{return new F(function(){return _69(_68,_w);});}}},_6f=function(_6g){return new F(function(){return _5R(new T1(0,new T(function(){return B(_64(_6g,_5L));})),_5z);});},_6h=function(_6i){var _6j=function(_6k,_6l){while(1){if(!B(_S(_6k,_6i))){if(!B(_5c(_6k,_6i))){if(!B(_4y(_6k,_6i))){return new F(function(){return _6f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_6l);}}else{return _6l-1|0;}}else{var _6m=B(_52(_6k,1)),_6n=_6l+1|0;_6k=_6m;_6l=_6n;continue;}}};return new F(function(){return _6j(_5k,0);});},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){var _6r=_6q.a>>>0;if(!_6r){return -1;}else{var _6s=function(_6t,_6u){while(1){if(_6t>=_6r){if(_6t<=_6r){if(_6t!=_6r){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6u);}}else{return _6u-1|0;}}else{var _6v=imul(_6t,2)>>>0,_6w=_6u+1|0;_6t=_6v;_6u=_6w;continue;}}};return new F(function(){return _6s(1,0);});}}else{return new F(function(){return _6h(_6q);});}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){var _6A=_6z.a>>>0;if(!_6A){return new T2(0,-1,0);}else{var _6B=function(_6C,_6D){while(1){if(_6C>=_6A){if(_6C<=_6A){if(_6C!=_6A){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6D);}}else{return _6D-1|0;}}else{var _6E=imul(_6C,2)>>>0,_6F=_6D+1|0;_6C=_6E;_6D=_6F;continue;}}};return new T2(0,B(_6B(1,0)),(_6A&_6A-1>>>0)>>>0&4294967295);}}else{var _6G=_6z.a;return new T2(0,B(_6o(_6z)),I_compareInt(I_and(_6G,I_sub(_6G,I_fromInt(1))),0));}},_6H=function(_6I,_6J){var _6K=E(_6I);if(!_6K._){var _6L=_6K.a,_6M=E(_6J);return (_6M._==0)?_6L<=_6M.a:I_compareInt(_6M.a,_6L)>=0;}else{var _6N=_6K.a,_6O=E(_6J);return (_6O._==0)?I_compareInt(_6N,_6O.a)<=0:I_compare(_6N,_6O.a)<=0;}},_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){var _6T=_6S.a,_6U=E(_6R);if(!_6U._){return new T1(0,(_6T>>>0&_6U.a>>>0)>>>0&4294967295);}else{_6Q=new T1(1,I_fromInt(_6T));_6R=_6U;continue;}}else{var _6V=E(_6R);if(!_6V._){_6Q=_6S;_6R=new T1(1,I_fromInt(_6V.a));continue;}else{return new T1(1,I_and(_6S.a,_6V.a));}}}},_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){var _70=_6Z.a,_71=E(_6Y);if(!_71._){var _72=_71.a,_73=subC(_70,_72);if(!E(_73.b)){return new T1(0,_73.a);}else{_6X=new T1(1,I_fromInt(_70));_6Y=new T1(1,I_fromInt(_72));continue;}}else{_6X=new T1(1,I_fromInt(_70));_6Y=_71;continue;}}else{var _74=E(_6Y);if(!_74._){_6X=_6Z;_6Y=new T1(1,I_fromInt(_74.a));continue;}else{return new T1(1,I_sub(_6Z.a,_74.a));}}}},_75=new T1(0,2),_76=function(_77,_78){var _79=E(_77);if(!_79._){var _7a=(_79.a>>>0&(2<<_78>>>0)-1>>>0)>>>0,_7b=1<<_78>>>0;return (_7b<=_7a)?(_7b>=_7a)?1:2:0;}else{var _7c=B(_6P(_79,B(_6W(B(_52(_75,_78)),_5k)))),_7d=B(_52(_5k,_78));return (!B(_5c(_7d,_7c)))?(!B(_S(_7d,_7c)))?1:2:0;}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){_7f=new T1(1,I_fromInt(_7h.a));continue;}else{return new T1(1,I_shiftRight(_7h.a,_7g));}}},_7i=function(_7j,_7k,_7l,_7m){var _7n=B(_6x(_7m)),_7o=_7n.a;if(!E(_7n.b)){var _7p=B(_6o(_7l));if(_7p<((_7o+_7j|0)-1|0)){var _7q=_7o+(_7j-_7k|0)|0;if(_7q>0){if(_7q>_7p){if(_7q<=(_7p+1|0)){if(!E(B(_6x(_7l)).b)){return 0;}else{return new F(function(){return _4u(_3k,_7j-_7k|0);});}}else{return 0;}}else{var _7r=B(_7e(_7l,_7q));switch(B(_76(_7l,_7q-1|0))){case 0:return new F(function(){return _4u(_7r,_7j-_7k|0);});break;case 1:if(!(B(_4G(_7r))&1)){return new F(function(){return _4u(_7r,_7j-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}break;default:return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}}}else{return new F(function(){return _4u(_7l,(_7j-_7k|0)-_7q|0);});}}else{if(_7p>=_7k){var _7s=B(_7e(_7l,(_7p+1|0)-_7k|0));switch(B(_76(_7l,_7p-_7k|0))){case 0:return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});break;case 2:return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});break;default:if(!(B(_4G(_7s))&1)){return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});}}}else{return new F(function(){return _4u(_7l, -_7o);});}}}else{var _7t=B(_6o(_7l))-_7o|0,_7u=function(_7v){var _7w=function(_7x,_7y){if(!B(_6H(B(_52(_7y,_7k)),_7x))){return new F(function(){return _56(_7v-_7k|0,_7x,_7y);});}else{return new F(function(){return _56((_7v-_7k|0)+1|0,_7x,B(_52(_7y,1)));});}};if(_7v>=_7k){if(_7v!=_7k){return new F(function(){return _7w(_7l,new T(function(){return B(_52(_7m,_7v-_7k|0));}));});}else{return new F(function(){return _7w(_7l,_7m);});}}else{return new F(function(){return _7w(new T(function(){return B(_52(_7l,_7k-_7v|0));}),_7m);});}};if(_7j>_7t){return new F(function(){return _7u(_7j);});}else{return new F(function(){return _7u(_7t);});}}},_7z=new T1(0,2147483647),_7A=new T(function(){return B(_4J(_7z,_5k));}),_7B=function(_7C){var _7D=E(_7C);if(!_7D._){var _7E=E(_7D.a);return (_7E==(-2147483648))?E(_7A):new T1(0, -_7E);}else{return new T1(1,I_negate(_7D.a));}},_7F=new T(function(){return 0/0;}),_7G=new T(function(){return -1/0;}),_7H=new T(function(){return 1/0;}),_7I=0,_7J=function(_7K,_7L){if(!B(_4y(_7L,_51))){if(!B(_4y(_7K,_51))){if(!B(_S(_7K,_51))){return new F(function(){return _7i(-1021,53,_7K,_7L);});}else{return  -B(_7i(-1021,53,B(_7B(_7K)),_7L));}}else{return E(_7I);}}else{return (!B(_4y(_7K,_51)))?(!B(_S(_7K,_51)))?E(_7H):E(_7G):E(_7F);}},_7M=function(_7N){return new T1(0,new T(function(){var _7O=E(_7N),_7P=jsShow(B(_7J(_7O.a,_7O.b)));return fromJSStr(_7P);}));},_7Q=new T(function(){return B(unCStr("1./("));}),_7R=new T1(0,_7Q),_7S=function(_7T){return new T1(1,new T2(1,_7R,new T2(1,_7T,_1S)));},_7U=new T(function(){return B(unCStr(")+("));}),_7V=new T1(0,_7U),_7W=function(_7X,_7Y){return new T1(1,new T2(1,_3e,new T2(1,_7X,new T2(1,_7V,new T2(1,_7Y,_1S)))));},_7Z=function(_80){return new T1(1,new T2(1,_1P,new T2(1,_80,_1S)));},_81=new T(function(){return B(unCStr(")*("));}),_82=new T1(0,_81),_83=function(_84,_85){return new T1(1,new T2(1,_3e,new T2(1,_84,new T2(1,_82,new T2(1,_85,_1S)))));},_86=function(_87){return E(E(_87).a);},_88=function(_89){return E(E(_89).d);},_8a=function(_8b,_8c){return new F(function(){return A3(_86,_8d,_8b,new T(function(){return B(A2(_88,_8d,_8c));}));});},_8e=new T(function(){return B(unCStr("abs("));}),_8f=new T1(0,_8e),_8g=function(_8h){return new T1(1,new T2(1,_8f,new T2(1,_8h,_1S)));},_8i=function(_8j){return new T1(0,new T(function(){return B(_n(B(_13(0,_8j,_w)),_1T));}));},_8k=new T(function(){return B(unCStr("sign("));}),_8l=new T1(0,_8k),_8m=function(_8n){return new T1(1,new T2(1,_8l,new T2(1,_8n,_1S)));},_8d=new T(function(){return {_:0,a:_7W,b:_8a,c:_83,d:_7Z,e:_8g,f:_8m,g:_8i};}),_8o=new T4(0,_8d,_3h,_7S,_7M),_8p={_:0,a:_8o,b:_2S,c:_2G,d:_2K,e:_33,f:_25,g:_2O,h:_2V,i:_2y,j:_37,k:_2i,l:_2a,m:_2q,n:_2Z,o:_2C,p:_3b,q:_2m,r:_2e,s:_2u},_8q=function(_8r){return E(E(_8r).a);},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v){return E(E(_8v).c);},_8w=function(_8x,_8y,_8z,_8A,_8B,_8C,_8D){var _8E=B(_8s(B(_8q(_8x)))),_8F=new T(function(){return B(A3(_86,_8E,new T(function(){return B(A3(_8u,_8E,_8y,_8B));}),new T(function(){return B(A3(_8u,_8E,_8z,_8C));})));});return new F(function(){return A3(_86,_8E,_8F,new T(function(){return B(A3(_8u,_8E,_8A,_8D));}));});},_8G=function(_8H){return E(E(_8H).b);},_8I=function(_8J){return E(E(_8J).g);},_8K=function(_8L){return E(E(_8L).e);},_8M=function(_8N,_8O){var _8P=B(_8s(B(_8q(_8N)))),_8Q=new T(function(){return B(A2(_8K,_8N,new T(function(){var _8R=E(_8O),_8S=_8R.a,_8T=_8R.b,_8U=_8R.c;return B(_8w(_8N,_8S,_8T,_8U,_8S,_8T,_8U));})));});return new F(function(){return A3(_8G,_8P,_8Q,new T(function(){return B(A2(_8I,_8P,_1o));}));});},_8V=new T(function(){return B(unCStr("x"));}),_8W=new T1(0,_8V),_8X=new T(function(){return B(unCStr("y"));}),_8Y=new T1(0,_8X),_8Z=new T(function(){return B(unCStr("z"));}),_90=new T1(0,_8Z),_91=new T3(0,E(_8W),E(_8Y),E(_90)),_92=new T(function(){return B(_8M(_8p,_91));}),_93=new T(function(){return toJSStr(B(_1v(_x,_1l,_92)));}),_94=new T(function(){return B(unCStr("(/=) is not defined"));}),_95=new T(function(){return B(err(_94));}),_96=new T(function(){return B(unCStr("(==) is not defined"));}),_97=new T(function(){return B(err(_96));}),_98=new T2(0,_97,_95),_99=new T(function(){return B(unCStr("(<) is not defined"));}),_9a=new T(function(){return B(err(_99));}),_9b=new T(function(){return B(unCStr("(<=) is not defined"));}),_9c=new T(function(){return B(err(_9b));}),_9d=new T(function(){return B(unCStr("(>) is not defined"));}),_9e=new T(function(){return B(err(_9d));}),_9f=new T(function(){return B(unCStr("(>=) is not defined"));}),_9g=new T(function(){return B(err(_9f));}),_9h=new T(function(){return B(unCStr("compare is not defined"));}),_9i=new T(function(){return B(err(_9h));}),_9j=new T(function(){return B(unCStr("max("));}),_9k=new T1(0,_9j),_9l=function(_9m,_9n){return new T1(1,new T2(1,_9k,new T2(1,_9m,new T2(1,_22,new T2(1,_9n,_1S)))));},_9o=new T(function(){return B(unCStr("min("));}),_9p=new T1(0,_9o),_9q=function(_9r,_9s){return new T1(1,new T2(1,_9p,new T2(1,_9r,new T2(1,_22,new T2(1,_9s,_1S)))));},_9t={_:0,a:_98,b:_9i,c:_9a,d:_9c,e:_9e,f:_9g,g:_9l,h:_9q},_9u=new T2(0,_8p,_9t),_9v=function(_9w,_9x){var _9y=E(_9w);return E(_9x);},_9z=function(_9A,_9B){var _9C=E(_9B);return E(_9A);},_9D=function(_9E,_9F){var _9G=E(_9E),_9H=E(_9F);return new T3(0,E(B(A1(_9G.a,_9H.a))),E(B(A1(_9G.b,_9H.b))),E(B(A1(_9G.c,_9H.c))));},_9I=function(_9J,_9K,_9L){return new T3(0,E(_9J),E(_9K),E(_9L));},_9M=function(_9N){return new F(function(){return _9I(_9N,_9N,_9N);});},_9O=function(_9P,_9Q){var _9R=E(_9Q),_9S=E(_9P);return new T3(0,E(_9S),E(_9S),E(_9S));},_9T=function(_9U,_9V){var _9W=E(_9V);return new T3(0,E(B(A1(_9U,_9W.a))),E(B(A1(_9U,_9W.b))),E(B(A1(_9U,_9W.c))));},_9X=new T2(0,_9T,_9O),_9Y=new T5(0,_9X,_9M,_9D,_9v,_9z),_9Z=new T1(0,0),_a0=function(_a1){var _a2=B(A2(_8I,_a1,_1o)),_a3=B(A2(_8I,_a1,_9Z));return new T3(0,E(new T3(0,E(_a2),E(_a3),E(_a3))),E(new T3(0,E(_a3),E(_a2),E(_a3))),E(new T3(0,E(_a3),E(_a3),E(_a2))));},_a4=function(_a5){return E(E(_a5).a);},_a6=function(_a7){return E(E(_a7).f);},_a8=function(_a9){return E(E(_a9).b);},_aa=function(_ab){return E(E(_ab).c);},_ac=function(_ad){return E(E(_ad).a);},_ae=function(_af){return E(E(_af).d);},_ag=function(_ah,_ai,_aj,_ak,_al){var _am=new T(function(){return E(E(E(_ah).c).a);}),_an=new T(function(){var _ao=E(_ah).a,_ap=new T(function(){var _aq=new T(function(){return B(_8q(_am));}),_ar=new T(function(){return B(_8s(_aq));}),_as=new T(function(){return B(A2(_ae,_am,_ai));}),_at=new T(function(){return B(A3(_a6,_am,_ai,_ak));}),_au=function(_av,_aw){var _ax=new T(function(){var _ay=new T(function(){return B(A3(_a8,_aq,new T(function(){return B(A3(_8u,_ar,_ak,_av));}),_ai));});return B(A3(_86,_ar,_ay,new T(function(){return B(A3(_8u,_ar,_aw,_as));})));});return new F(function(){return A3(_8u,_ar,_at,_ax);});};return B(A3(_ac,B(_a4(_ao)),_au,_aj));});return B(A3(_aa,_ao,_ap,_al));});return new T2(0,new T(function(){return B(A3(_a6,_am,_ai,_ak));}),_an);},_az=function(_aA,_aB,_aC,_aD){var _aE=E(_aC),_aF=E(_aD),_aG=B(_ag(_aB,_aE.a,_aE.b,_aF.a,_aF.b));return new T2(0,_aG.a,_aG.b);},_aH=new T1(0,1),_aI=function(_aJ){return E(E(_aJ).l);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8q(_aO));}),_aR=new T(function(){var _aS=B(_8s(_aQ)),_aT=new T(function(){var _aU=new T(function(){return B(A3(_8G,_aS,new T(function(){return B(A2(_8I,_aS,_aH));}),new T(function(){return B(A3(_8u,_aS,_aM,_aM));})));});return B(A2(_8K,_aO,_aU));});return B(A2(_88,_aS,_aT));});return B(A3(_ac,B(_a4(E(_aL).a)),function(_aV){return new F(function(){return A3(_a8,_aQ,_aV,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aW=function(_aX,_aY,_aZ){var _b0=E(_aZ),_b1=B(_aK(_aY,_b0.a,_b0.b));return new T2(0,_b1.a,_b1.b);},_b2=function(_b3){return E(E(_b3).r);},_b4=function(_b5,_b6,_b7){var _b8=new T(function(){return E(E(E(_b5).c).a);}),_b9=new T(function(){var _ba=new T(function(){return B(_8q(_b8));}),_bb=new T(function(){var _bc=new T(function(){var _bd=B(_8s(_ba));return B(A3(_8G,_bd,new T(function(){return B(A3(_8u,_bd,_b6,_b6));}),new T(function(){return B(A2(_8I,_bd,_aH));})));});return B(A2(_8K,_b8,_bc));});return B(A3(_ac,B(_a4(E(_b5).a)),function(_be){return new F(function(){return A3(_a8,_ba,_be,_bb);});},_b7));});return new T2(0,new T(function(){return B(A2(_b2,_b8,_b6));}),_b9);},_bf=function(_bg,_bh,_bi){var _bj=E(_bi),_bk=B(_b4(_bh,_bj.a,_bj.b));return new T2(0,_bk.a,_bk.b);},_bl=function(_bm){return E(E(_bm).k);},_bn=function(_bo,_bp,_bq){var _br=new T(function(){return E(E(E(_bo).c).a);}),_bs=new T(function(){var _bt=new T(function(){return B(_8q(_br));}),_bu=new T(function(){var _bv=new T(function(){var _bw=B(_8s(_bt));return B(A3(_8G,_bw,new T(function(){return B(A2(_8I,_bw,_aH));}),new T(function(){return B(A3(_8u,_bw,_bp,_bp));})));});return B(A2(_8K,_br,_bv));});return B(A3(_ac,B(_a4(E(_bo).a)),function(_bx){return new F(function(){return A3(_a8,_bt,_bx,_bu);});},_bq));});return new T2(0,new T(function(){return B(A2(_bl,_br,_bp));}),_bs);},_by=function(_bz,_bA,_bB){var _bC=E(_bB),_bD=B(_bn(_bA,_bC.a,_bC.b));return new T2(0,_bD.a,_bD.b);},_bE=function(_bF){return E(E(_bF).q);},_bG=function(_bH,_bI,_bJ){var _bK=new T(function(){return E(E(E(_bH).c).a);}),_bL=new T(function(){var _bM=new T(function(){return B(_8q(_bK));}),_bN=new T(function(){var _bO=new T(function(){var _bP=B(_8s(_bM));return B(A3(_86,_bP,new T(function(){return B(A3(_8u,_bP,_bI,_bI));}),new T(function(){return B(A2(_8I,_bP,_aH));})));});return B(A2(_8K,_bK,_bO));});return B(A3(_ac,B(_a4(E(_bH).a)),function(_bQ){return new F(function(){return A3(_a8,_bM,_bQ,_bN);});},_bJ));});return new T2(0,new T(function(){return B(A2(_bE,_bK,_bI));}),_bL);},_bR=function(_bS,_bT,_bU){var _bV=E(_bU),_bW=B(_bG(_bT,_bV.a,_bV.b));return new T2(0,_bW.a,_bW.b);},_bX=function(_bY){return E(E(_bY).m);},_bZ=function(_c0,_c1,_c2){var _c3=new T(function(){return E(E(E(_c0).c).a);}),_c4=new T(function(){var _c5=new T(function(){return B(_8q(_c3));}),_c6=new T(function(){var _c7=B(_8s(_c5));return B(A3(_86,_c7,new T(function(){return B(A2(_8I,_c7,_aH));}),new T(function(){return B(A3(_8u,_c7,_c1,_c1));})));});return B(A3(_ac,B(_a4(E(_c0).a)),function(_c8){return new F(function(){return A3(_a8,_c5,_c8,_c6);});},_c2));});return new T2(0,new T(function(){return B(A2(_bX,_c3,_c1));}),_c4);},_c9=function(_ca,_cb,_cc){var _cd=E(_cc),_ce=B(_bZ(_cb,_cd.a,_cd.b));return new T2(0,_ce.a,_ce.b);},_cf=function(_cg){return E(E(_cg).s);},_ch=function(_ci,_cj,_ck){var _cl=new T(function(){return E(E(E(_ci).c).a);}),_cm=new T(function(){var _cn=new T(function(){return B(_8q(_cl));}),_co=new T(function(){var _cp=B(_8s(_cn));return B(A3(_8G,_cp,new T(function(){return B(A2(_8I,_cp,_aH));}),new T(function(){return B(A3(_8u,_cp,_cj,_cj));})));});return B(A3(_ac,B(_a4(E(_ci).a)),function(_cq){return new F(function(){return A3(_a8,_cn,_cq,_co);});},_ck));});return new T2(0,new T(function(){return B(A2(_cf,_cl,_cj));}),_cm);},_cr=function(_cs,_ct,_cu){var _cv=E(_cu),_cw=B(_ch(_ct,_cv.a,_cv.b));return new T2(0,_cw.a,_cw.b);},_cx=function(_cy){return E(E(_cy).i);},_cz=function(_cA){return E(E(_cA).h);},_cB=function(_cC,_cD,_cE){var _cF=new T(function(){return E(E(E(_cC).c).a);}),_cG=new T(function(){var _cH=new T(function(){return B(_8s(new T(function(){return B(_8q(_cF));})));}),_cI=new T(function(){return B(A2(_88,_cH,new T(function(){return B(A2(_cz,_cF,_cD));})));});return B(A3(_ac,B(_a4(E(_cC).a)),function(_cJ){return new F(function(){return A3(_8u,_cH,_cJ,_cI);});},_cE));});return new T2(0,new T(function(){return B(A2(_cx,_cF,_cD));}),_cG);},_cK=function(_cL,_cM,_cN){var _cO=E(_cN),_cP=B(_cB(_cM,_cO.a,_cO.b));return new T2(0,_cP.a,_cP.b);},_cQ=function(_cR){return E(E(_cR).o);},_cS=function(_cT){return E(E(_cT).n);},_cU=function(_cV,_cW,_cX){var _cY=new T(function(){return E(E(E(_cV).c).a);}),_cZ=new T(function(){var _d0=new T(function(){return B(_8s(new T(function(){return B(_8q(_cY));})));}),_d1=new T(function(){return B(A2(_cS,_cY,_cW));});return B(A3(_ac,B(_a4(E(_cV).a)),function(_d2){return new F(function(){return A3(_8u,_d0,_d2,_d1);});},_cX));});return new T2(0,new T(function(){return B(A2(_cQ,_cY,_cW));}),_cZ);},_d3=function(_d4,_d5,_d6){var _d7=E(_d6),_d8=B(_cU(_d5,_d7.a,_d7.b));return new T2(0,_d8.a,_d8.b);},_d9=function(_da){return E(E(_da).c);},_db=function(_dc,_dd,_de){var _df=new T(function(){return E(E(E(_dc).c).a);}),_dg=new T(function(){var _dh=new T(function(){return B(_8s(new T(function(){return B(_8q(_df));})));}),_di=new T(function(){return B(A2(_d9,_df,_dd));});return B(A3(_ac,B(_a4(E(_dc).a)),function(_dj){return new F(function(){return A3(_8u,_dh,_dj,_di);});},_de));});return new T2(0,new T(function(){return B(A2(_d9,_df,_dd));}),_dg);},_dk=function(_dl,_dm,_dn){var _do=E(_dn),_dp=B(_db(_dm,_do.a,_do.b));return new T2(0,_dp.a,_dp.b);},_dq=function(_dr,_ds,_dt){var _du=new T(function(){return E(E(E(_dr).c).a);}),_dv=new T(function(){var _dw=new T(function(){return B(_8q(_du));}),_dx=new T(function(){return B(_8s(_dw));}),_dy=new T(function(){return B(A3(_a8,_dw,new T(function(){return B(A2(_8I,_dx,_aH));}),_ds));});return B(A3(_ac,B(_a4(E(_dr).a)),function(_dz){return new F(function(){return A3(_8u,_dx,_dz,_dy);});},_dt));});return new T2(0,new T(function(){return B(A2(_ae,_du,_ds));}),_dv);},_dA=function(_dB,_dC,_dD){var _dE=E(_dD),_dF=B(_dq(_dC,_dE.a,_dE.b));return new T2(0,_dF.a,_dF.b);},_dG=function(_dH,_dI,_dJ,_dK){var _dL=new T(function(){return E(E(_dI).c);}),_dM=new T3(0,new T(function(){return E(E(_dI).a);}),new T(function(){return E(E(_dI).b);}),new T2(0,new T(function(){return E(E(_dL).a);}),new T(function(){return E(E(_dL).b);})));return new F(function(){return A3(_a8,_dH,new T(function(){var _dN=E(_dK),_dO=B(_dq(_dM,_dN.a,_dN.b));return new T2(0,_dO.a,_dO.b);}),new T(function(){var _dP=E(_dJ),_dQ=B(_dq(_dM,_dP.a,_dP.b));return new T2(0,_dQ.a,_dQ.b);}));});},_dR=function(_dS){return E(E(_dS).b);},_dT=function(_dU){return E(E(_dU).b);},_dV=function(_dW){var _dX=new T(function(){return E(E(E(_dW).c).a);}),_dY=new T(function(){return B(A2(_dT,E(_dW).a,new T(function(){return B(A2(_8I,B(_8s(B(_8q(_dX)))),_L));})));});return new T2(0,new T(function(){return B(_dR(_dX));}),_dY);},_dZ=function(_e0,_e1){var _e2=B(_dV(_e1));return new T2(0,_e2.a,_e2.b);},_e3=function(_e4,_e5,_e6){var _e7=new T(function(){return E(E(E(_e4).c).a);}),_e8=new T(function(){var _e9=new T(function(){return B(_8s(new T(function(){return B(_8q(_e7));})));}),_ea=new T(function(){return B(A2(_cx,_e7,_e5));});return B(A3(_ac,B(_a4(E(_e4).a)),function(_eb){return new F(function(){return A3(_8u,_e9,_eb,_ea);});},_e6));});return new T2(0,new T(function(){return B(A2(_cz,_e7,_e5));}),_e8);},_ec=function(_ed,_ee,_ef){var _eg=E(_ef),_eh=B(_e3(_ee,_eg.a,_eg.b));return new T2(0,_eh.a,_eh.b);},_ei=function(_ej,_ek,_el){var _em=new T(function(){return E(E(E(_ej).c).a);}),_en=new T(function(){var _eo=new T(function(){return B(_8s(new T(function(){return B(_8q(_em));})));}),_ep=new T(function(){return B(A2(_cQ,_em,_ek));});return B(A3(_ac,B(_a4(E(_ej).a)),function(_eq){return new F(function(){return A3(_8u,_eo,_eq,_ep);});},_el));});return new T2(0,new T(function(){return B(A2(_cS,_em,_ek));}),_en);},_er=function(_es,_et,_eu){var _ev=E(_eu),_ew=B(_ei(_et,_ev.a,_ev.b));return new T2(0,_ew.a,_ew.b);},_ex=new T1(0,2),_ey=function(_ez,_eA,_eB){var _eC=new T(function(){return E(E(E(_ez).c).a);}),_eD=new T(function(){var _eE=new T(function(){return B(_8q(_eC));}),_eF=new T(function(){return B(_8s(_eE));}),_eG=new T(function(){var _eH=new T(function(){return B(A3(_a8,_eE,new T(function(){return B(A2(_8I,_eF,_aH));}),new T(function(){return B(A2(_8I,_eF,_ex));})));});return B(A3(_a8,_eE,_eH,new T(function(){return B(A2(_8K,_eC,_eA));})));});return B(A3(_ac,B(_a4(E(_ez).a)),function(_eI){return new F(function(){return A3(_8u,_eF,_eI,_eG);});},_eB));});return new T2(0,new T(function(){return B(A2(_8K,_eC,_eA));}),_eD);},_eJ=function(_eK,_eL,_eM){var _eN=E(_eM),_eO=B(_ey(_eL,_eN.a,_eN.b));return new T2(0,_eO.a,_eO.b);},_eP=function(_eQ){return E(E(_eQ).j);},_eR=function(_eS,_eT,_eU){var _eV=new T(function(){return E(E(E(_eS).c).a);}),_eW=new T(function(){var _eX=new T(function(){return B(_8q(_eV));}),_eY=new T(function(){var _eZ=new T(function(){return B(A2(_cx,_eV,_eT));});return B(A3(_8u,B(_8s(_eX)),_eZ,_eZ));});return B(A3(_ac,B(_a4(E(_eS).a)),function(_f0){return new F(function(){return A3(_a8,_eX,_f0,_eY);});},_eU));});return new T2(0,new T(function(){return B(A2(_eP,_eV,_eT));}),_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eR(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8){return E(E(_f8).p);},_f9=function(_fa,_fb,_fc){var _fd=new T(function(){return E(E(E(_fa).c).a);}),_fe=new T(function(){var _ff=new T(function(){return B(_8q(_fd));}),_fg=new T(function(){var _fh=new T(function(){return B(A2(_cQ,_fd,_fb));});return B(A3(_8u,B(_8s(_ff)),_fh,_fh));});return B(A3(_ac,B(_a4(E(_fa).a)),function(_fi){return new F(function(){return A3(_a8,_ff,_fi,_fg);});},_fc));});return new T2(0,new T(function(){return B(A2(_f7,_fd,_fb));}),_fe);},_fj=function(_fk,_fl,_fm){var _fn=E(_fm),_fo=B(_f9(_fl,_fn.a,_fn.b));return new T2(0,_fo.a,_fo.b);},_fp=function(_fq,_fr){return {_:0,a:_fq,b:new T(function(){return B(_dZ(_fq,_fr));}),c:function(_fs){return new F(function(){return _dk(_fq,_fr,_fs);});},d:function(_fs){return new F(function(){return _dA(_fq,_fr,_fs);});},e:function(_fs){return new F(function(){return _eJ(_fq,_fr,_fs);});},f:function(_ft,_fs){return new F(function(){return _az(_fq,_fr,_ft,_fs);});},g:function(_ft,_fs){return new F(function(){return _dG(_fq,_fr,_ft,_fs);});},h:function(_fs){return new F(function(){return _ec(_fq,_fr,_fs);});},i:function(_fs){return new F(function(){return _cK(_fq,_fr,_fs);});},j:function(_fs){return new F(function(){return _f1(_fq,_fr,_fs);});},k:function(_fs){return new F(function(){return _by(_fq,_fr,_fs);});},l:function(_fs){return new F(function(){return _aW(_fq,_fr,_fs);});},m:function(_fs){return new F(function(){return _c9(_fq,_fr,_fs);});},n:function(_fs){return new F(function(){return _er(_fq,_fr,_fs);});},o:function(_fs){return new F(function(){return _d3(_fq,_fr,_fs);});},p:function(_fs){return new F(function(){return _fj(_fq,_fr,_fs);});},q:function(_fs){return new F(function(){return _bR(_fq,_fr,_fs);});},r:function(_fs){return new F(function(){return _bf(_fq,_fr,_fs);});},s:function(_fs){return new F(function(){return _cr(_fq,_fr,_fs);});}};},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8q(new T(function(){return E(E(E(_fv).c).a);})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){var _fE=new T(function(){return B(_8s(_fA));}),_fF=new T(function(){return B(A3(_8u,_fE,_fy,_fy));}),_fG=function(_fH,_fI){var _fJ=new T(function(){return B(A3(_8G,_fE,new T(function(){return B(A3(_8u,_fE,_fH,_fy));}),new T(function(){return B(A3(_8u,_fE,_fw,_fI));})));});return new F(function(){return A3(_a8,_fA,_fJ,_fF);});};return B(A3(_ac,B(_a4(_fC)),_fG,_fx));});return B(A3(_aa,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_a8,_fA,_fw,_fy));}),_fB);},_fK=function(_fL,_fM,_fN,_fO){var _fP=E(_fN),_fQ=E(_fO),_fR=B(_fu(_fM,_fP.a,_fP.b,_fQ.a,_fQ.b));return new T2(0,_fR.a,_fR.b);},_fS=function(_fT){return E(E(_fT).d);},_fU=function(_fV,_fW){var _fX=new T(function(){return B(_8q(new T(function(){return E(E(E(_fV).c).a);})));}),_fY=new T(function(){return B(A2(_dT,E(_fV).a,new T(function(){return B(A2(_8I,B(_8s(_fX)),_L));})));});return new T2(0,new T(function(){return B(A2(_fS,_fX,_fW));}),_fY);},_fZ=function(_g0,_g1,_g2){var _g3=B(_fU(_g1,_g2));return new T2(0,_g3.a,_g3.b);},_g4=function(_g5,_g6,_g7){var _g8=new T(function(){return B(_8q(new T(function(){return E(E(E(_g5).c).a);})));}),_g9=new T(function(){return B(_8s(_g8));}),_ga=new T(function(){var _gb=new T(function(){var _gc=new T(function(){return B(A3(_a8,_g8,new T(function(){return B(A2(_8I,_g9,_aH));}),new T(function(){return B(A3(_8u,_g9,_g6,_g6));})));});return B(A2(_88,_g9,_gc));});return B(A3(_ac,B(_a4(E(_g5).a)),function(_gd){return new F(function(){return A3(_8u,_g9,_gd,_gb);});},_g7));}),_ge=new T(function(){return B(A3(_a8,_g8,new T(function(){return B(A2(_8I,_g9,_aH));}),_g6));});return new T2(0,_ge,_ga);},_gf=function(_gg,_gh,_gi){var _gj=E(_gi),_gk=B(_g4(_gh,_gj.a,_gj.b));return new T2(0,_gk.a,_gk.b);},_gl=function(_gm,_gn){return new T4(0,_gm,function(_ft,_fs){return new F(function(){return _fK(_gm,_gn,_ft,_fs);});},function(_fs){return new F(function(){return _gf(_gm,_gn,_fs);});},function(_fs){return new F(function(){return _fZ(_gm,_gn,_fs);});});},_go=function(_gp,_gq,_gr,_gs,_gt){var _gu=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gp).c).a);})));})));}),_gv=new T(function(){var _gw=E(_gp).a,_gx=new T(function(){var _gy=function(_gz,_gA){return new F(function(){return A3(_86,_gu,new T(function(){return B(A3(_8u,_gu,_gq,_gA));}),new T(function(){return B(A3(_8u,_gu,_gz,_gs));}));});};return B(A3(_ac,B(_a4(_gw)),_gy,_gr));});return B(A3(_aa,_gw,_gx,_gt));});return new T2(0,new T(function(){return B(A3(_8u,_gu,_gq,_gs));}),_gv);},_gB=function(_gC,_gD,_gE){var _gF=E(_gD),_gG=E(_gE),_gH=B(_go(_gC,_gF.a,_gF.b,_gG.a,_gG.b));return new T2(0,_gH.a,_gH.b);},_gI=function(_gJ,_gK,_gL,_gM,_gN){var _gO=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gJ).c).a);})));})));}),_gP=new T(function(){var _gQ=E(_gJ).a,_gR=new T(function(){return B(A3(_ac,B(_a4(_gQ)),new T(function(){return B(_86(_gO));}),_gL));});return B(A3(_aa,_gQ,_gR,_gN));});return new T2(0,new T(function(){return B(A3(_86,_gO,_gK,_gM));}),_gP);},_gS=function(_gT,_gU,_gV){var _gW=E(_gU),_gX=E(_gV),_gY=B(_gI(_gT,_gW.a,_gW.b,_gX.a,_gX.b));return new T2(0,_gY.a,_gY.b);},_gZ=function(_h0,_h1,_h2){var _h3=B(_h4(_h0));return new F(function(){return A3(_86,_h3,_h1,new T(function(){return B(A2(_88,_h3,_h2));}));});},_h5=function(_h6){return E(E(_h6).e);},_h7=function(_h8){return E(E(_h8).f);},_h9=function(_ha,_hb,_hc){var _hd=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_ha).c).a);})));})));}),_he=new T(function(){var _hf=new T(function(){return B(A2(_h7,_hd,_hb));});return B(A3(_ac,B(_a4(E(_ha).a)),function(_hg){return new F(function(){return A3(_8u,_hd,_hg,_hf);});},_hc));});return new T2(0,new T(function(){return B(A2(_h5,_hd,_hb));}),_he);},_hh=function(_hi,_hj){var _hk=E(_hj),_hl=B(_h9(_hi,_hk.a,_hk.b));return new T2(0,_hl.a,_hl.b);},_hm=function(_hn,_ho){var _hp=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hn).c).a);})));})));}),_hq=new T(function(){return B(A2(_dT,E(_hn).a,new T(function(){return B(A2(_8I,_hp,_L));})));});return new T2(0,new T(function(){return B(A2(_8I,_hp,_ho));}),_hq);},_hr=function(_hs,_ht){var _hu=B(_hm(_hs,_ht));return new T2(0,_hu.a,_hu.b);},_hv=function(_hw,_hx,_hy){var _hz=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hw).c).a);})));})));}),_hA=new T(function(){return B(A3(_ac,B(_a4(E(_hw).a)),new T(function(){return B(_88(_hz));}),_hy));});return new T2(0,new T(function(){return B(A2(_88,_hz,_hx));}),_hA);},_hB=function(_hC,_hD){var _hE=E(_hD),_hF=B(_hv(_hC,_hE.a,_hE.b));return new T2(0,_hF.a,_hF.b);},_hG=function(_hH,_hI){var _hJ=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hH).c).a);})));})));}),_hK=new T(function(){return B(A2(_dT,E(_hH).a,new T(function(){return B(A2(_8I,_hJ,_L));})));});return new T2(0,new T(function(){return B(A2(_h7,_hJ,_hI));}),_hK);},_hL=function(_hM,_hN){var _hO=B(_hG(_hM,E(_hN).a));return new T2(0,_hO.a,_hO.b);},_h4=function(_hP){return {_:0,a:function(_ft,_fs){return new F(function(){return _gS(_hP,_ft,_fs);});},b:function(_ft,_fs){return new F(function(){return _gZ(_hP,_ft,_fs);});},c:function(_ft,_fs){return new F(function(){return _gB(_hP,_ft,_fs);});},d:function(_fs){return new F(function(){return _hB(_hP,_fs);});},e:function(_fs){return new F(function(){return _hh(_hP,_fs);});},f:function(_fs){return new F(function(){return _hL(_hP,_fs);});},g:function(_fs){return new F(function(){return _hr(_hP,_fs);});}};},_hQ=function(_hR){var _hS=new T(function(){return E(E(_hR).a);}),_hT=new T3(0,_9Y,_a0,new T2(0,_hS,new T(function(){return E(E(_hR).b);}))),_hU=new T(function(){return B(_fp(new T(function(){return B(_gl(new T(function(){return B(_h4(_hT));}),_hT));}),_hT));}),_hV=new T(function(){return B(_8s(new T(function(){return B(_8q(_hS));})));}),_hW=function(_hX){return E(B(_8M(_hU,new T(function(){var _hY=E(_hX),_hZ=B(A2(_8I,_hV,_1o)),_i0=B(A2(_8I,_hV,_9Z));return new T3(0,E(new T2(0,_hY.a,new T3(0,E(_hZ),E(_i0),E(_i0)))),E(new T2(0,_hY.b,new T3(0,E(_i0),E(_hZ),E(_i0)))),E(new T2(0,_hY.c,new T3(0,E(_i0),E(_i0),E(_hZ)))));}))).b);};return E(_hW);},_i1=new T(function(){return B(_hQ(_9u));}),_i2=function(_i3,_i4){var _i5=E(_i4);return (_i5._==0)?__Z:new T2(1,_i3,new T2(1,_i5.a,new T(function(){return B(_i2(_i3,_i5.b));})));},_i6=new T(function(){var _i7=B(A1(_i1,_91));return new T2(1,_i7.a,new T(function(){return B(_i2(_22,new T2(1,_i7.b,new T2(1,_i7.c,_w))));}));}),_i8=new T1(1,_i6),_i9=new T2(1,_i8,_1S),_ia=new T(function(){return B(unCStr("vec3("));}),_ib=new T1(0,_ia),_ic=new T2(1,_ib,_i9),_id=new T(function(){return toJSStr(B(_1F(_x,_1l,_ic)));}),_ie=function(_if,_ig){while(1){var _ih=E(_if);if(!_ih._){return E(_ig);}else{var _ii=_ig+1|0;_if=_ih.b;_ig=_ii;continue;}}},_ij=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_ik=new T(function(){return B(err(_ij));}),_il=0,_im=new T3(0,E(_il),E(_il),E(_il)),_in=new T(function(){return B(unCStr("Negative exponent"));}),_io=new T(function(){return B(err(_in));}),_ip=function(_iq,_ir,_is){while(1){if(!(_ir%2)){var _it=_iq*_iq,_iu=quot(_ir,2);_iq=_it;_ir=_iu;continue;}else{var _iv=E(_ir);if(_iv==1){return _iq*_is;}else{var _it=_iq*_iq,_iw=_iq*_is;_iq=_it;_ir=quot(_iv-1|0,2);_is=_iw;continue;}}}},_ix=function(_iy,_iz){while(1){if(!(_iz%2)){var _iA=_iy*_iy,_iB=quot(_iz,2);_iy=_iA;_iz=_iB;continue;}else{var _iC=E(_iz);if(_iC==1){return E(_iy);}else{return new F(function(){return _ip(_iy*_iy,quot(_iC-1|0,2),_iy);});}}}},_iD=function(_iE){var _iF=E(_iE);return new F(function(){return Math.log(_iF+(_iF+1)*Math.sqrt((_iF-1)/(_iF+1)));});},_iG=function(_iH){var _iI=E(_iH);return new F(function(){return Math.log(_iI+Math.sqrt(1+_iI*_iI));});},_iJ=function(_iK){var _iL=E(_iK);return 0.5*Math.log((1+_iL)/(1-_iL));},_iM=function(_iN,_iO){return Math.log(E(_iO))/Math.log(E(_iN));},_iP=3.141592653589793,_iQ=function(_iR){var _iS=E(_iR);return new F(function(){return _7J(_iS.a,_iS.b);});},_iT=function(_iU){return 1/E(_iU);},_iV=function(_iW){var _iX=E(_iW),_iY=E(_iX);return (_iY==0)?E(_7I):(_iY<=0)? -_iY:E(_iX);},_iZ=function(_j0){var _j1=E(_j0);if(!_j1._){return _j1.a;}else{return new F(function(){return I_toNumber(_j1.a);});}},_j2=function(_j3){return new F(function(){return _iZ(_j3);});},_j4=1,_j5=-1,_j6=function(_j7){var _j8=E(_j7);return (_j8<=0)?(_j8>=0)?E(_j8):E(_j5):E(_j4);},_j9=function(_ja,_jb){return E(_ja)-E(_jb);},_jc=function(_jd){return  -E(_jd);},_je=function(_jf,_jg){return E(_jf)+E(_jg);},_jh=function(_ji,_jj){return E(_ji)*E(_jj);},_jk={_:0,a:_je,b:_j9,c:_jh,d:_jc,e:_iV,f:_j6,g:_j2},_jl=function(_jm,_jn){return E(_jm)/E(_jn);},_jo=new T4(0,_jk,_jl,_iT,_iQ),_jp=function(_jq){return new F(function(){return Math.acos(E(_jq));});},_jr=function(_js){return new F(function(){return Math.asin(E(_js));});},_jt=function(_ju){return new F(function(){return Math.atan(E(_ju));});},_jv=function(_jw){return new F(function(){return Math.cos(E(_jw));});},_jx=function(_jy){return new F(function(){return cosh(E(_jy));});},_jz=function(_jA){return new F(function(){return Math.exp(E(_jA));});},_jB=function(_jC){return new F(function(){return Math.log(E(_jC));});},_jD=function(_jE,_jF){return new F(function(){return Math.pow(E(_jE),E(_jF));});},_jG=function(_jH){return new F(function(){return Math.sin(E(_jH));});},_jI=function(_jJ){return new F(function(){return sinh(E(_jJ));});},_jK=function(_jL){return new F(function(){return Math.sqrt(E(_jL));});},_jM=function(_jN){return new F(function(){return Math.tan(E(_jN));});},_jO=function(_jP){return new F(function(){return tanh(E(_jP));});},_jQ={_:0,a:_jo,b:_iP,c:_jz,d:_jB,e:_jK,f:_jD,g:_iM,h:_jG,i:_jv,j:_jM,k:_jr,l:_jp,m:_jt,n:_jI,o:_jx,p:_jO,q:_iG,r:_iD,s:_iJ},_jR=function(_jS,_jT){return (E(_jS)!=E(_jT))?true:false;},_jU=function(_jV,_jW){return E(_jV)==E(_jW);},_jX=new T2(0,_jU,_jR),_jY=function(_jZ,_k0){return E(_jZ)<E(_k0);},_k1=function(_k2,_k3){return E(_k2)<=E(_k3);},_k4=function(_k5,_k6){return E(_k5)>E(_k6);},_k7=function(_k8,_k9){return E(_k8)>=E(_k9);},_ka=function(_kb,_kc){var _kd=E(_kb),_ke=E(_kc);return (_kd>=_ke)?(_kd!=_ke)?2:1:0;},_kf=function(_kg,_kh){var _ki=E(_kg),_kj=E(_kh);return (_ki>_kj)?E(_ki):E(_kj);},_kk=function(_kl,_km){var _kn=E(_kl),_ko=E(_km);return (_kn>_ko)?E(_ko):E(_kn);},_kp={_:0,a:_jX,b:_ka,c:_jY,d:_k1,e:_k4,f:_k7,g:_kf,h:_kk},_kq="dz",_kr="wy",_ks="wx",_kt="dy",_ku="dx",_kv="t",_kw="a",_kx="r",_ky="ly",_kz="lx",_kA="wz",_kB=0,_kC=function(_kD){var _kE=__new(),_kF=_kE,_kG=function(_kH,_){while(1){var _kI=E(_kH);if(!_kI._){return _kB;}else{var _kJ=E(_kI.a),_kK=__set(_kF,E(_kJ.a),E(_kJ.b));_kH=_kI.b;continue;}}},_kL=B(_kG(_kD,_));return E(_kF);},_kM=function(_kN,_kO,_kP,_kQ,_kR,_kS,_kT,_kU,_kV){return new F(function(){return _kC(new T2(1,new T2(0,_ks,_kN),new T2(1,new T2(0,_kr,_kO),new T2(1,new T2(0,_kA,_kP),new T2(1,new T2(0,_kz,_kQ*_kR*Math.cos(_kS)),new T2(1,new T2(0,_ky,_kQ*_kR*Math.sin(_kS)),new T2(1,new T2(0,_kx,_kQ),new T2(1,new T2(0,_kw,_kR),new T2(1,new T2(0,_kv,_kS),new T2(1,new T2(0,_ku,_kT),new T2(1,new T2(0,_kt,_kU),new T2(1,new T2(0,_kq,_kV),_w))))))))))));});},_kW=function(_kX){var _kY=E(_kX),_kZ=E(_kY.a),_l0=E(_kY.b),_l1=E(_kY.d);return new F(function(){return _kM(_kZ.a,_kZ.b,_kZ.c,E(_l0.a),E(_l0.b),E(_kY.c),_l1.a,_l1.b,_l1.c);});},_l2=function(_l3,_l4){var _l5=E(_l4);return (_l5._==0)?__Z:new T2(1,new T(function(){return B(A1(_l3,_l5.a));}),new T(function(){return B(_l2(_l3,_l5.b));}));},_l6=function(_l7,_l8,_l9){var _la=__lst2arr(B(_l2(_kW,new T2(1,_l7,new T2(1,_l8,new T2(1,_l9,_w))))));return E(_la);},_lb=function(_lc){var _ld=E(_lc);return new F(function(){return _l6(_ld.a,_ld.b,_ld.c);});},_le=new T2(0,_jQ,_kp),_lf=function(_lg,_lh,_li,_lj){var _lk=B(_8q(_lg)),_ll=new T(function(){return B(A2(_8K,_lg,new T(function(){return B(_8w(_lg,_lh,_li,_lj,_lh,_li,_lj));})));});return new T3(0,B(A3(_a8,_lk,_lh,_ll)),B(A3(_a8,_lk,_li,_ll)),B(A3(_a8,_lk,_lj,_ll)));},_lm=function(_ln,_lo,_lp,_lq,_lr,_ls,_lt){var _lu=B(_8u(_ln));return new T3(0,B(A1(B(A1(_lu,_lo)),_lr)),B(A1(B(A1(_lu,_lp)),_ls)),B(A1(B(A1(_lu,_lq)),_lt)));},_lv=function(_lw,_lx,_ly,_lz,_lA,_lB,_lC){var _lD=B(_86(_lw));return new T3(0,B(A1(B(A1(_lD,_lx)),_lA)),B(A1(B(A1(_lD,_ly)),_lB)),B(A1(B(A1(_lD,_lz)),_lC)));},_lE=function(_lF,_lG){var _lH=new T(function(){return E(E(_lF).a);}),_lI=new T(function(){return B(A2(_hQ,new T2(0,_lH,new T(function(){return E(E(_lF).b);})),_lG));}),_lJ=new T(function(){var _lK=E(_lI),_lL=B(_lf(_lH,_lK.a,_lK.b,_lK.c));return new T3(0,E(_lL.a),E(_lL.b),E(_lL.c));}),_lM=new T(function(){var _lN=E(_lG),_lO=E(_lJ),_lP=B(_8q(_lH)),_lQ=new T(function(){return B(A2(_8K,_lH,new T(function(){var _lR=E(_lI),_lS=_lR.a,_lT=_lR.b,_lU=_lR.c;return B(_8w(_lH,_lS,_lT,_lU,_lS,_lT,_lU));})));}),_lV=B(A3(_a8,_lP,new T(function(){return B(_8M(_lH,_lN));}),_lQ)),_lW=B(_8s(_lP)),_lX=B(_lm(_lW,_lO.a,_lO.b,_lO.c,_lV,_lV,_lV)),_lY=B(_88(_lW)),_lZ=B(_lv(_lW,_lN.a,_lN.b,_lN.c,B(A1(_lY,_lX.a)),B(A1(_lY,_lX.b)),B(A1(_lY,_lX.c))));return new T3(0,E(_lZ.a),E(_lZ.b),E(_lZ.c));});return new T2(0,_lM,_lJ);},_m0=function(_m1){return E(E(_m1).a);},_m2=function(_m3,_m4,_m5,_m6,_m7,_m8,_m9){var _ma=B(_8w(_m3,_m7,_m8,_m9,_m4,_m5,_m6)),_mb=B(_8s(B(_8q(_m3)))),_mc=B(_lm(_mb,_m7,_m8,_m9,_ma,_ma,_ma)),_md=B(_88(_mb));return new F(function(){return _lv(_mb,_m4,_m5,_m6,B(A1(_md,_mc.a)),B(A1(_md,_mc.b)),B(A1(_md,_mc.c)));});},_me=function(_mf){return E(E(_mf).a);},_mg=function(_mh,_mi,_mj,_mk){var _ml=new T(function(){var _mm=E(_mk),_mn=E(_mj),_mo=B(_m2(_mh,_mm.a,_mm.b,_mm.c,_mn.a,_mn.b,_mn.c));return new T3(0,E(_mo.a),E(_mo.b),E(_mo.c));}),_mp=new T(function(){return B(A2(_8K,_mh,new T(function(){var _mq=E(_ml),_mr=_mq.a,_ms=_mq.b,_mt=_mq.c;return B(_8w(_mh,_mr,_ms,_mt,_mr,_ms,_mt));})));});if(!B(A3(_me,B(_m0(_mi)),_mp,new T(function(){return B(A2(_8I,B(_8s(B(_8q(_mh)))),_9Z));})))){var _mu=E(_ml),_mv=B(_lf(_mh,_mu.a,_mu.b,_mu.c)),_mw=B(A2(_8K,_mh,new T(function(){var _mx=E(_mk),_my=_mx.a,_mz=_mx.b,_mA=_mx.c;return B(_8w(_mh,_my,_mz,_mA,_my,_mz,_mA));}))),_mB=B(_8u(new T(function(){return B(_8s(new T(function(){return B(_8q(_mh));})));})));return new T3(0,B(A1(B(A1(_mB,_mv.a)),_mw)),B(A1(B(A1(_mB,_mv.b)),_mw)),B(A1(B(A1(_mB,_mv.c)),_mw)));}else{var _mC=B(A2(_8I,B(_8s(B(_8q(_mh)))),_9Z));return new T3(0,_mC,_mC,_mC);}},_mD=function(_mE,_mF){while(1){var _mG=E(_mE);if(!_mG._){return E(_mF);}else{var _mH=_mG.b,_mI=E(_mG.a);if(_mF>_mI){_mE=_mH;continue;}else{_mE=_mH;_mF=_mI;continue;}}}},_mJ=new T(function(){var _mK=eval("angleCount"),_mL=Number(_mK);return jsTrunc(_mL);}),_mM=new T(function(){return E(_mJ);}),_mN=new T(function(){return B(unCStr(": empty list"));}),_mO=new T(function(){return B(unCStr("Prelude."));}),_mP=function(_mQ){return new F(function(){return err(B(_n(_mO,new T(function(){return B(_n(_mQ,_mN));},1))));});},_mR=new T(function(){return B(unCStr("head"));}),_mS=new T(function(){return B(_mP(_mR));}),_mT=function(_mU,_mV,_mW){var _mX=E(_mU);if(!_mX._){return __Z;}else{var _mY=E(_mV);if(!_mY._){return __Z;}else{var _mZ=_mY.a,_n0=E(_mW);if(!_n0._){return __Z;}else{var _n1=E(_n0.a),_n2=_n1.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_mX.a),E(_mZ),E(_n2));}),new T2(1,new T(function(){return new T3(0,E(_mZ),E(_n2),E(_n1.b));}),_w)),new T(function(){return B(_mT(_mX.b,_mY.b,_n0.b));},1));});}}}},_n3=new T(function(){return B(unCStr("tail"));}),_n4=new T(function(){return B(_mP(_n3));}),_n5=function(_n6,_n7){var _n8=E(_n6);if(!_n8._){return __Z;}else{var _n9=E(_n7);return (_n9._==0)?__Z:new T2(1,new T2(0,_n8.a,_n9.a),new T(function(){return B(_n5(_n8.b,_n9.b));}));}},_na=function(_nb,_nc){var _nd=E(_nb);if(!_nd._){return __Z;}else{var _ne=E(_nc);if(!_ne._){return __Z;}else{var _nf=E(_nd.a),_ng=_nf.b,_nh=E(_ne.a).b,_ni=new T(function(){var _nj=new T(function(){return B(_n5(_nh,new T(function(){var _nk=E(_nh);if(!_nk._){return E(_n4);}else{return E(_nk.b);}},1)));},1);return B(_mT(_ng,new T(function(){var _nl=E(_ng);if(!_nl._){return E(_n4);}else{return E(_nl.b);}},1),_nj));});return new F(function(){return _n(new T2(1,new T(function(){var _nm=E(_ng);if(!_nm._){return E(_mS);}else{var _nn=E(_nh);if(!_nn._){return E(_mS);}else{return new T3(0,E(_nf.a),E(_nm.a),E(_nn.a));}}}),_ni),new T(function(){return B(_na(_nd.b,_ne.b));},1));});}}},_no=new T(function(){return 6.283185307179586/E(_mM);}),_np=new T(function(){return E(_mM)-1;}),_nq=new T1(0,1),_nr=function(_ns,_nt){var _nu=E(_nt),_nv=new T(function(){var _nw=B(_8s(_ns)),_nx=B(_nr(_ns,B(A3(_86,_nw,_nu,new T(function(){return B(A2(_8I,_nw,_nq));})))));return new T2(1,_nx.a,_nx.b);});return new T2(0,_nu,_nv);},_ny=function(_nz){return E(E(_nz).d);},_nA=new T1(0,2),_nB=function(_nC,_nD){var _nE=E(_nD);if(!_nE._){return __Z;}else{var _nF=_nE.a;return (!B(A1(_nC,_nF)))?__Z:new T2(1,_nF,new T(function(){return B(_nB(_nC,_nE.b));}));}},_nG=function(_nH,_nI,_nJ,_nK){var _nL=B(_nr(_nI,_nJ)),_nM=new T(function(){var _nN=B(_8s(_nI)),_nO=new T(function(){return B(A3(_a8,_nI,new T(function(){return B(A2(_8I,_nN,_nq));}),new T(function(){return B(A2(_8I,_nN,_nA));})));});return B(A3(_86,_nN,_nK,_nO));});return new F(function(){return _nB(function(_nP){return new F(function(){return A3(_ny,_nH,_nP,_nM);});},new T2(1,_nL.a,_nL.b));});},_nQ=new T(function(){return B(_nG(_kp,_jo,_il,_np));}),_nR=function(_nS,_nT){while(1){var _nU=E(_nS);if(!_nU._){return E(_nT);}else{_nS=_nU.b;_nT=_nU.a;continue;}}},_nV=new T(function(){return B(unCStr("last"));}),_nW=new T(function(){return B(_mP(_nV));}),_nX=function(_nY){return new F(function(){return _nR(_nY,_nW);});},_nZ=function(_o0){return new F(function(){return _nX(E(_o0).b);});},_o1=new T(function(){return B(unCStr("maximum"));}),_o2=new T(function(){return B(_mP(_o1));}),_o3=new T(function(){var _o4=eval("proceedCount"),_o5=Number(_o4);return jsTrunc(_o5);}),_o6=new T(function(){return E(_o3);}),_o7=1,_o8=new T(function(){return B(_nG(_kp,_jo,_o7,_o6));}),_o9=function(_oa,_ob,_oc,_od,_oe,_of,_og,_oh,_oi,_oj,_ok,_ol,_om,_on){var _oo=new T(function(){var _op=new T(function(){var _oq=E(_oj),_or=E(_on),_os=E(_om),_ot=E(_ok),_ou=E(_ol),_ov=E(_oi);return new T3(0,_oq*_or-_os*_ot,_ot*_ou-_or*_ov,_ov*_os-_ou*_oq);}),_ow=function(_ox){var _oy=new T(function(){var _oz=E(_ox)/E(_mM);return (_oz+_oz)*3.141592653589793;}),_oA=new T(function(){return B(A1(_oa,_oy));}),_oB=new T(function(){var _oC=new T(function(){var _oD=E(_oA)/E(_o6);return new T3(0,E(_oD),E(_oD),E(_oD));}),_oE=function(_oF,_oG){var _oH=E(_oF);if(!_oH._){return new T2(0,_w,_oG);}else{var _oI=new T(function(){var _oJ=B(_lE(_le,new T(function(){var _oK=E(_oG),_oL=E(_oK.a),_oM=E(_oK.b),_oN=E(_oC);return new T3(0,E(_oL.a)+E(_oM.a)*E(_oN.a),E(_oL.b)+E(_oM.b)*E(_oN.b),E(_oL.c)+E(_oM.c)*E(_oN.c));}))),_oO=_oJ.a,_oP=new T(function(){var _oQ=E(_oJ.b),_oR=E(E(_oG).b),_oS=B(_m2(_jQ,_oR.a,_oR.b,_oR.c,_oQ.a,_oQ.b,_oQ.c)),_oT=B(_lf(_jQ,_oS.a,_oS.b,_oS.c));return new T3(0,E(_oT.a),E(_oT.b),E(_oT.c));});return new T2(0,new T(function(){var _oU=E(_oA),_oV=E(_oy);return new T4(0,E(_oO),E(new T2(0,E(_oH.a)/E(_o6),E(_oU))),E(_oV),E(_oP));}),new T2(0,_oO,_oP));}),_oW=new T(function(){var _oX=B(_oE(_oH.b,new T(function(){return E(E(_oI).b);})));return new T2(0,_oX.a,_oX.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oI).a);}),new T(function(){return E(E(_oW).a);})),new T(function(){return E(E(_oW).b);}));}},_oY=function(_oZ,_p0,_p1,_p2,_p3){var _p4=E(_oZ);if(!_p4._){return new T2(0,_w,new T2(0,new T3(0,E(_p0),E(_p1),E(_p2)),_p3));}else{var _p5=new T(function(){var _p6=B(_lE(_le,new T(function(){var _p7=E(_p3),_p8=E(_oC);return new T3(0,E(_p0)+E(_p7.a)*E(_p8.a),E(_p1)+E(_p7.b)*E(_p8.b),E(_p2)+E(_p7.c)*E(_p8.c));}))),_p9=_p6.a,_pa=new T(function(){var _pb=E(_p6.b),_pc=E(_p3),_pd=B(_m2(_jQ,_pc.a,_pc.b,_pc.c,_pb.a,_pb.b,_pb.c)),_pe=B(_lf(_jQ,_pd.a,_pd.b,_pd.c));return new T3(0,E(_pe.a),E(_pe.b),E(_pe.c));});return new T2(0,new T(function(){var _pf=E(_oA),_pg=E(_oy);return new T4(0,E(_p9),E(new T2(0,E(_p4.a)/E(_o6),E(_pf))),E(_pg),E(_pa));}),new T2(0,_p9,_pa));}),_ph=new T(function(){var _pi=B(_oE(_p4.b,new T(function(){return E(E(_p5).b);})));return new T2(0,_pi.a,_pi.b);});return new T2(0,new T2(1,new T(function(){return E(E(_p5).a);}),new T(function(){return E(E(_ph).a);})),new T(function(){return E(E(_ph).b);}));}};return E(B(_oY(_o8,_od,_oe,_of,new T(function(){var _pj=E(_op),_pk=E(_oy)+_og,_pl=Math.cos(_pk),_pm=Math.sin(_pk);return new T3(0,E(_oi)*_pl+E(_pj.a)*_pm,E(_oj)*_pl+E(_pj.b)*_pm,E(_ok)*_pl+E(_pj.c)*_pm);}))).a);});return new T2(0,new T(function(){var _pn=E(_oA),_po=E(_oy);return new T4(0,E(new T3(0,E(_od),E(_oe),E(_of))),E(new T2(0,E(_il),E(_pn))),E(_po),E(_im));}),_oB);};return B(_l2(_ow,_nQ));}),_pp=new T(function(){var _pq=function(_pr){return new F(function(){return A1(_oa,new T(function(){return B(_jh(_pr,_no));}));});},_ps=B(_l2(_pq,_nQ));if(!_ps._){return E(_o2);}else{return B(_mD(_ps.b,E(_ps.a)));}}),_pt=new T(function(){var _pu=new T(function(){var _pv=B(_n(_oo,new T2(1,new T(function(){var _pw=E(_oo);if(!_pw._){return E(_mS);}else{return E(_pw.a);}}),_w)));if(!_pv._){return E(_n4);}else{return E(_pv.b);}},1);return B(_na(_oo,_pu));});return new T3(0,_pt,new T(function(){return B(_l2(_nZ,_oo));}),_pp);},_px=function(_py,_pz,_pA,_pB,_pC,_pD,_pE,_pF,_pG,_pH,_pI,_pJ,_pK,_pL,_pM,_pN,_pO,_pP){var _pQ=B(_lE(_le,new T3(0,E(_pB),E(_pC),E(_pD)))),_pR=_pQ.b,_pS=E(_pQ.a),_pT=B(_mg(_jQ,_kp,_pR,new T3(0,E(_pF),E(_pG),E(_pH)))),_pU=E(_pR),_pV=_pU.a,_pW=_pU.b,_pX=_pU.c,_pY=B(_m2(_jQ,_pJ,_pK,_pL,_pV,_pW,_pX)),_pZ=B(_lf(_jQ,_pY.a,_pY.b,_pY.c)),_q0=_pZ.a,_q1=_pZ.b,_q2=_pZ.c,_q3=E(_pE),_q4=new T2(0,E(new T3(0,E(_pT.a),E(_pT.b),E(_pT.c))),E(_pI)),_q5=B(_o9(_py,_pz,_pA,_pS.a,_pS.b,_pS.c,_q3,_q4,_q0,_q1,_q2,_pV,_pW,_pX)),_q6=__lst2arr(B(_l2(_lb,_q5.a))),_q7=__lst2arr(B(_l2(_kW,_q5.b)));return {_:0,a:_py,b:_pz,c:_pA,d:new T2(0,E(_pS),E(_q3)),e:_q4,f:new T3(0,E(_q0),E(_q1),E(_q2)),g:_pU,h:_q6,i:_q7,j:E(_q5.c)};},_q8=-4,_q9=new T3(0,E(_il),E(_q8),E(_il)),_qa=function(_qb){return E(_q9);},_qc=function(_){return new F(function(){return __jsNull();});},_qd=function(_qe){var _qf=B(A1(_qe,_));return E(_qf);},_qg=new T(function(){return B(_qd(_qc));}),_qh=function(_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu){var _qv=function(_qw){var _qx=E(_no),_qy=2+_qw|0,_qz=_qy-1|0,_qA=(2+_qw)*(1+_qw),_qB=E(_nQ);if(!_qB._){return _qx*0;}else{var _qC=_qB.a,_qD=_qB.b,_qE=B(A1(_qi,new T(function(){return 6.283185307179586*E(_qC)/E(_mM);}))),_qF=B(A1(_qi,new T(function(){return 6.283185307179586*(E(_qC)+1)/E(_mM);})));if(_qE!=_qF){if(_qy>=0){var _qG=E(_qy);if(!_qG){var _qH=function(_qI,_qJ){while(1){var _qK=B((function(_qL,_qM){var _qN=E(_qL);if(!_qN._){return E(_qM);}else{var _qO=_qN.a,_qP=_qN.b,_qQ=B(A1(_qi,new T(function(){return 6.283185307179586*E(_qO)/E(_mM);}))),_qR=B(A1(_qi,new T(function(){return 6.283185307179586*(E(_qO)+1)/E(_mM);})));if(_qQ!=_qR){var _qS=_qM+0/(_qQ-_qR)/_qA;_qI=_qP;_qJ=_qS;return __continue;}else{if(_qz>=0){var _qT=E(_qz);if(!_qT){var _qS=_qM+_qy/_qA;_qI=_qP;_qJ=_qS;return __continue;}else{var _qS=_qM+_qy*B(_ix(_qQ,_qT))/_qA;_qI=_qP;_qJ=_qS;return __continue;}}else{return E(_io);}}}})(_qI,_qJ));if(_qK!=__continue){return _qK;}}};return _qx*B(_qH(_qD,0/(_qE-_qF)/_qA));}else{var _qU=function(_qV,_qW){while(1){var _qX=B((function(_qY,_qZ){var _r0=E(_qY);if(!_r0._){return E(_qZ);}else{var _r1=_r0.a,_r2=_r0.b,_r3=B(A1(_qi,new T(function(){return 6.283185307179586*E(_r1)/E(_mM);}))),_r4=B(A1(_qi,new T(function(){return 6.283185307179586*(E(_r1)+1)/E(_mM);})));if(_r3!=_r4){if(_qG>=0){var _r5=_qZ+(B(_ix(_r3,_qG))-B(_ix(_r4,_qG)))/(_r3-_r4)/_qA;_qV=_r2;_qW=_r5;return __continue;}else{return E(_io);}}else{if(_qz>=0){var _r6=E(_qz);if(!_r6){var _r5=_qZ+_qy/_qA;_qV=_r2;_qW=_r5;return __continue;}else{var _r5=_qZ+_qy*B(_ix(_r3,_r6))/_qA;_qV=_r2;_qW=_r5;return __continue;}}else{return E(_io);}}}})(_qV,_qW));if(_qX!=__continue){return _qX;}}};return _qx*B(_qU(_qD,(B(_ix(_qE,_qG))-B(_ix(_qF,_qG)))/(_qE-_qF)/_qA));}}else{return E(_io);}}else{if(_qz>=0){var _r7=E(_qz);if(!_r7){var _r8=function(_r9,_ra){while(1){var _rb=B((function(_rc,_rd){var _re=E(_rc);if(!_re._){return E(_rd);}else{var _rf=_re.a,_rg=_re.b,_rh=B(A1(_qi,new T(function(){return 6.283185307179586*E(_rf)/E(_mM);}))),_ri=B(A1(_qi,new T(function(){return 6.283185307179586*(E(_rf)+1)/E(_mM);})));if(_rh!=_ri){if(_qy>=0){var _rj=E(_qy);if(!_rj){var _rk=_rd+0/(_rh-_ri)/_qA;_r9=_rg;_ra=_rk;return __continue;}else{var _rk=_rd+(B(_ix(_rh,_rj))-B(_ix(_ri,_rj)))/(_rh-_ri)/_qA;_r9=_rg;_ra=_rk;return __continue;}}else{return E(_io);}}else{var _rk=_rd+_qy/_qA;_r9=_rg;_ra=_rk;return __continue;}}})(_r9,_ra));if(_rb!=__continue){return _rb;}}};return _qx*B(_r8(_qD,_qy/_qA));}else{var _rl=function(_rm,_rn){while(1){var _ro=B((function(_rp,_rq){var _rr=E(_rp);if(!_rr._){return E(_rq);}else{var _rs=_rr.a,_rt=_rr.b,_ru=B(A1(_qi,new T(function(){return 6.283185307179586*E(_rs)/E(_mM);}))),_rv=B(A1(_qi,new T(function(){return 6.283185307179586*(E(_rs)+1)/E(_mM);})));if(_ru!=_rv){if(_qy>=0){var _rw=E(_qy);if(!_rw){var _rx=_rq+0/(_ru-_rv)/_qA;_rm=_rt;_rn=_rx;return __continue;}else{var _rx=_rq+(B(_ix(_ru,_rw))-B(_ix(_rv,_rw)))/(_ru-_rv)/_qA;_rm=_rt;_rn=_rx;return __continue;}}else{return E(_io);}}else{if(_r7>=0){var _rx=_rq+_qy*B(_ix(_ru,_r7))/_qA;_rm=_rt;_rn=_rx;return __continue;}else{return E(_io);}}}})(_rm,_rn));if(_ro!=__continue){return _ro;}}};return _qx*B(_rl(_qD,_qy*B(_ix(_qE,_r7))/_qA));}}else{return E(_io);}}}},_ry=E(_qg),_rz=1/(B(_qv(1))*_qj);return new F(function(){return _px(_qi,_qa,new T2(0,E(new T3(0,E(_rz),E(_rz),E(_rz))),1/(B(_qv(3))*_qj)),_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu,_im,_ry,_ry,0);});},_rA=1,_rB=0,_rC=function(_rD){var _rE=I_decodeDouble(_rD);return new T2(0,new T1(1,_rE.b),_rE.a);},_rF=function(_rG){return new T1(0,_rG);},_rH=function(_rI){var _rJ=hs_intToInt64(2147483647),_rK=hs_leInt64(_rI,_rJ);if(!_rK){return new T1(1,I_fromInt64(_rI));}else{var _rL=hs_intToInt64(-2147483648),_rM=hs_geInt64(_rI,_rL);if(!_rM){return new T1(1,I_fromInt64(_rI));}else{var _rN=hs_int64ToInt(_rI);return new F(function(){return _rF(_rN);});}}},_rO=new T(function(){var _rP=newByteArr(256),_rQ=_rP,_=_rQ["v"]["i8"][0]=8,_rR=function(_rS,_rT,_rU,_){while(1){if(_rU>=256){if(_rS>=256){return E(_);}else{var _rV=imul(2,_rS)|0,_rW=_rT+1|0,_rX=_rS;_rS=_rV;_rT=_rW;_rU=_rX;continue;}}else{var _=_rQ["v"]["i8"][_rU]=_rT,_rX=_rU+_rS|0;_rU=_rX;continue;}}},_=B(_rR(2,0,1,_));return _rQ;}),_rY=function(_rZ,_s0){var _s1=hs_int64ToInt(_rZ),_s2=E(_rO),_s3=_s2["v"]["i8"][(255&_s1>>>0)>>>0&4294967295];if(_s0>_s3){if(_s3>=8){var _s4=hs_uncheckedIShiftRA64(_rZ,8),_s5=function(_s6,_s7){while(1){var _s8=B((function(_s9,_sa){var _sb=hs_int64ToInt(_s9),_sc=_s2["v"]["i8"][(255&_sb>>>0)>>>0&4294967295];if(_sa>_sc){if(_sc>=8){var _sd=hs_uncheckedIShiftRA64(_s9,8),_se=_sa-8|0;_s6=_sd;_s7=_se;return __continue;}else{return new T2(0,new T(function(){var _sf=hs_uncheckedIShiftRA64(_s9,_sc);return B(_rH(_sf));}),_sa-_sc|0);}}else{return new T2(0,new T(function(){var _sg=hs_uncheckedIShiftRA64(_s9,_sa);return B(_rH(_sg));}),0);}})(_s6,_s7));if(_s8!=__continue){return _s8;}}};return new F(function(){return _s5(_s4,_s0-8|0);});}else{return new T2(0,new T(function(){var _sh=hs_uncheckedIShiftRA64(_rZ,_s3);return B(_rH(_sh));}),_s0-_s3|0);}}else{return new T2(0,new T(function(){var _si=hs_uncheckedIShiftRA64(_rZ,_s0);return B(_rH(_si));}),0);}},_sj=function(_sk){var _sl=hs_intToInt64(_sk);return E(_sl);},_sm=function(_sn){var _so=E(_sn);if(!_so._){return new F(function(){return _sj(_so.a);});}else{return new F(function(){return I_toInt64(_so.a);});}},_sp=function(_sq){return I_toInt(_sq)>>>0;},_sr=function(_ss){var _st=E(_ss);if(!_st._){return _st.a>>>0;}else{return new F(function(){return _sp(_st.a);});}},_su=function(_sv){var _sw=B(_rC(_sv)),_sx=_sw.a,_sy=_sw.b;if(_sy<0){var _sz=function(_sA){if(!_sA){return new T2(0,E(_sx),B(_52(_3k, -_sy)));}else{var _sB=B(_rY(B(_sm(_sx)), -_sy));return new T2(0,E(_sB.a),B(_52(_3k,_sB.b)));}};if(!((B(_sr(_sx))&1)>>>0)){return new F(function(){return _sz(1);});}else{return new F(function(){return _sz(0);});}}else{return new T2(0,B(_52(_sx,_sy)),_3k);}},_sC=function(_sD){var _sE=B(_su(E(_sD)));return new T2(0,E(_sE.a),E(_sE.b));},_sF=new T3(0,_jk,_kp,_sC),_sG=function(_sH){return E(E(_sH).a);},_sI=function(_sJ){return E(E(_sJ).a);},_sK=function(_sL,_sM){if(_sL<=_sM){var _sN=function(_sO){return new T2(1,_sO,new T(function(){if(_sO!=_sM){return B(_sN(_sO+1|0));}else{return __Z;}}));};return new F(function(){return _sN(_sL);});}else{return __Z;}},_sP=function(_sQ){return new F(function(){return _sK(E(_sQ),2147483647);});},_sR=function(_sS,_sT,_sU){if(_sU<=_sT){var _sV=new T(function(){var _sW=_sT-_sS|0,_sX=function(_sY){return (_sY>=(_sU-_sW|0))?new T2(1,_sY,new T(function(){return B(_sX(_sY+_sW|0));})):new T2(1,_sY,_w);};return B(_sX(_sT));});return new T2(1,_sS,_sV);}else{return (_sU<=_sS)?new T2(1,_sS,_w):__Z;}},_sZ=function(_t0,_t1,_t2){if(_t2>=_t1){var _t3=new T(function(){var _t4=_t1-_t0|0,_t5=function(_t6){return (_t6<=(_t2-_t4|0))?new T2(1,_t6,new T(function(){return B(_t5(_t6+_t4|0));})):new T2(1,_t6,_w);};return B(_t5(_t1));});return new T2(1,_t0,_t3);}else{return (_t2>=_t0)?new T2(1,_t0,_w):__Z;}},_t7=function(_t8,_t9){if(_t9<_t8){return new F(function(){return _sR(_t8,_t9,-2147483648);});}else{return new F(function(){return _sZ(_t8,_t9,2147483647);});}},_ta=function(_tb,_tc){return new F(function(){return _t7(E(_tb),E(_tc));});},_td=function(_te,_tf,_tg){if(_tf<_te){return new F(function(){return _sR(_te,_tf,_tg);});}else{return new F(function(){return _sZ(_te,_tf,_tg);});}},_th=function(_ti,_tj,_tk){return new F(function(){return _td(E(_ti),E(_tj),E(_tk));});},_tl=function(_tm,_tn){return new F(function(){return _sK(E(_tm),E(_tn));});},_to=function(_tp){return E(_tp);},_tq=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_tr=new T(function(){return B(err(_tq));}),_ts=function(_tt){var _tu=E(_tt);return (_tu==(-2147483648))?E(_tr):_tu-1|0;},_tv=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_tw=new T(function(){return B(err(_tv));}),_tx=function(_ty){var _tz=E(_ty);return (_tz==2147483647)?E(_tw):_tz+1|0;},_tA={_:0,a:_tx,b:_ts,c:_to,d:_to,e:_sP,f:_ta,g:_tl,h:_th},_tB=function(_tC,_tD){if(_tC<=0){if(_tC>=0){return new F(function(){return quot(_tC,_tD);});}else{if(_tD<=0){return new F(function(){return quot(_tC,_tD);});}else{return quot(_tC+1|0,_tD)-1|0;}}}else{if(_tD>=0){if(_tC>=0){return new F(function(){return quot(_tC,_tD);});}else{if(_tD<=0){return new F(function(){return quot(_tC,_tD);});}else{return quot(_tC+1|0,_tD)-1|0;}}}else{return quot(_tC-1|0,_tD)-1|0;}}},_tE=0,_tF=new T(function(){return B(_4p(_tE));}),_tG=new T(function(){return die(_tF);}),_tH=function(_tI,_tJ){var _tK=E(_tJ);switch(_tK){case -1:var _tL=E(_tI);if(_tL==(-2147483648)){return E(_tG);}else{return new F(function(){return _tB(_tL,-1);});}break;case 0:return E(_4t);default:return new F(function(){return _tB(_tI,_tK);});}},_tM=function(_tN,_tO){return new F(function(){return _tH(E(_tN),E(_tO));});},_tP=0,_tQ=new T2(0,_tG,_tP),_tR=function(_tS,_tT){var _tU=E(_tS),_tV=E(_tT);switch(_tV){case -1:var _tW=E(_tU);if(_tW==(-2147483648)){return E(_tQ);}else{if(_tW<=0){if(_tW>=0){var _tX=quotRemI(_tW,-1);return new T2(0,_tX.a,_tX.b);}else{var _tY=quotRemI(_tW,-1);return new T2(0,_tY.a,_tY.b);}}else{var _tZ=quotRemI(_tW-1|0,-1);return new T2(0,_tZ.a-1|0,(_tZ.b+(-1)|0)+1|0);}}break;case 0:return E(_4t);default:if(_tU<=0){if(_tU>=0){var _u0=quotRemI(_tU,_tV);return new T2(0,_u0.a,_u0.b);}else{if(_tV<=0){var _u1=quotRemI(_tU,_tV);return new T2(0,_u1.a,_u1.b);}else{var _u2=quotRemI(_tU+1|0,_tV);return new T2(0,_u2.a-1|0,(_u2.b+_tV|0)-1|0);}}}else{if(_tV>=0){if(_tU>=0){var _u3=quotRemI(_tU,_tV);return new T2(0,_u3.a,_u3.b);}else{if(_tV<=0){var _u4=quotRemI(_tU,_tV);return new T2(0,_u4.a,_u4.b);}else{var _u5=quotRemI(_tU+1|0,_tV);return new T2(0,_u5.a-1|0,(_u5.b+_tV|0)-1|0);}}}else{var _u6=quotRemI(_tU-1|0,_tV);return new T2(0,_u6.a-1|0,(_u6.b+_tV|0)+1|0);}}}},_u7=function(_u8,_u9){var _ua=_u8%_u9;if(_u8<=0){if(_u8>=0){return E(_ua);}else{if(_u9<=0){return E(_ua);}else{var _ub=E(_ua);return (_ub==0)?0:_ub+_u9|0;}}}else{if(_u9>=0){if(_u8>=0){return E(_ua);}else{if(_u9<=0){return E(_ua);}else{var _uc=E(_ua);return (_uc==0)?0:_uc+_u9|0;}}}else{var _ud=E(_ua);return (_ud==0)?0:_ud+_u9|0;}}},_ue=function(_uf,_ug){var _uh=E(_ug);switch(_uh){case -1:return E(_tP);case 0:return E(_4t);default:return new F(function(){return _u7(E(_uf),_uh);});}},_ui=function(_uj,_uk){var _ul=E(_uj),_um=E(_uk);switch(_um){case -1:var _un=E(_ul);if(_un==(-2147483648)){return E(_tG);}else{return new F(function(){return quot(_un,-1);});}break;case 0:return E(_4t);default:return new F(function(){return quot(_ul,_um);});}},_uo=function(_up,_uq){var _ur=E(_up),_us=E(_uq);switch(_us){case -1:var _ut=E(_ur);if(_ut==(-2147483648)){return E(_tQ);}else{var _uu=quotRemI(_ut,-1);return new T2(0,_uu.a,_uu.b);}break;case 0:return E(_4t);default:var _uv=quotRemI(_ur,_us);return new T2(0,_uv.a,_uv.b);}},_uw=function(_ux,_uy){var _uz=E(_uy);switch(_uz){case -1:return E(_tP);case 0:return E(_4t);default:return E(_ux)%_uz;}},_uA=function(_uB){return new F(function(){return _rF(E(_uB));});},_uC=function(_uD){return new T2(0,E(B(_rF(E(_uD)))),E(_nq));},_uE=function(_uF,_uG){return imul(E(_uF),E(_uG))|0;},_uH=function(_uI,_uJ){return E(_uI)+E(_uJ)|0;},_uK=function(_uL,_uM){return E(_uL)-E(_uM)|0;},_uN=function(_uO){var _uP=E(_uO);return (_uP<0)? -_uP:E(_uP);},_uQ=function(_uR){return new F(function(){return _4G(_uR);});},_uS=function(_uT){return  -E(_uT);},_uU=-1,_uV=0,_uW=1,_uX=function(_uY){var _uZ=E(_uY);return (_uZ>=0)?(E(_uZ)==0)?E(_uV):E(_uW):E(_uU);},_v0={_:0,a:_uH,b:_uK,c:_uE,d:_uS,e:_uN,f:_uX,g:_uQ},_v1=function(_v2,_v3){return E(_v2)==E(_v3);},_v4=function(_v5,_v6){return E(_v5)!=E(_v6);},_v7=new T2(0,_v1,_v4),_v8=function(_v9,_va){var _vb=E(_v9),_vc=E(_va);return (_vb>_vc)?E(_vb):E(_vc);},_vd=function(_ve,_vf){var _vg=E(_ve),_vh=E(_vf);return (_vg>_vh)?E(_vh):E(_vg);},_vi=function(_vj,_vk){return (_vj>=_vk)?(_vj!=_vk)?2:1:0;},_vl=function(_vm,_vn){return new F(function(){return _vi(E(_vm),E(_vn));});},_vo=function(_vp,_vq){return E(_vp)>=E(_vq);},_vr=function(_vs,_vt){return E(_vs)>E(_vt);},_vu=function(_vv,_vw){return E(_vv)<=E(_vw);},_vx=function(_vy,_vz){return E(_vy)<E(_vz);},_vA={_:0,a:_v7,b:_vl,c:_vx,d:_vu,e:_vr,f:_vo,g:_v8,h:_vd},_vB=new T3(0,_v0,_vA,_uC),_vC={_:0,a:_vB,b:_tA,c:_ui,d:_uw,e:_tM,f:_ue,g:_uo,h:_tR,i:_uA},_vD=new T1(0,2),_vE=function(_vF,_vG){while(1){var _vH=E(_vF);if(!_vH._){var _vI=_vH.a,_vJ=E(_vG);if(!_vJ._){var _vK=_vJ.a;if(!(imul(_vI,_vK)|0)){return new T1(0,imul(_vI,_vK)|0);}else{_vF=new T1(1,I_fromInt(_vI));_vG=new T1(1,I_fromInt(_vK));continue;}}else{_vF=new T1(1,I_fromInt(_vI));_vG=_vJ;continue;}}else{var _vL=E(_vG);if(!_vL._){_vF=_vH;_vG=new T1(1,I_fromInt(_vL.a));continue;}else{return new T1(1,I_mul(_vH.a,_vL.a));}}}},_vM=function(_vN,_vO,_vP){while(1){if(!(_vO%2)){var _vQ=B(_vE(_vN,_vN)),_vR=quot(_vO,2);_vN=_vQ;_vO=_vR;continue;}else{var _vS=E(_vO);if(_vS==1){return new F(function(){return _vE(_vN,_vP);});}else{var _vQ=B(_vE(_vN,_vN)),_vT=B(_vE(_vN,_vP));_vN=_vQ;_vO=quot(_vS-1|0,2);_vP=_vT;continue;}}}},_vU=function(_vV,_vW){while(1){if(!(_vW%2)){var _vX=B(_vE(_vV,_vV)),_vY=quot(_vW,2);_vV=_vX;_vW=_vY;continue;}else{var _vZ=E(_vW);if(_vZ==1){return E(_vV);}else{return new F(function(){return _vM(B(_vE(_vV,_vV)),quot(_vZ-1|0,2),_vV);});}}}},_w0=function(_w1){return E(E(_w1).b);},_w2=function(_w3){return E(E(_w3).c);},_w4=new T1(0,0),_w5=function(_w6){return E(E(_w6).d);},_w7=function(_w8,_w9){var _wa=B(_sG(_w8)),_wb=new T(function(){return B(_sI(_wa));}),_wc=new T(function(){return B(A3(_w5,_w8,_w9,new T(function(){return B(A2(_8I,_wb,_nA));})));});return new F(function(){return A3(_me,B(_m0(B(_w0(_wa)))),_wc,new T(function(){return B(A2(_8I,_wb,_w4));}));});},_wd=new T(function(){return B(unCStr("Negative exponent"));}),_we=new T(function(){return B(err(_wd));}),_wf=function(_wg){return E(E(_wg).c);},_wh=function(_wi,_wj,_wk,_wl){var _wm=B(_sG(_wj)),_wn=new T(function(){return B(_sI(_wm));}),_wo=B(_w0(_wm));if(!B(A3(_w2,_wo,_wl,new T(function(){return B(A2(_8I,_wn,_w4));})))){if(!B(A3(_me,B(_m0(_wo)),_wl,new T(function(){return B(A2(_8I,_wn,_w4));})))){var _wp=new T(function(){return B(A2(_8I,_wn,_nA));}),_wq=new T(function(){return B(A2(_8I,_wn,_nq));}),_wr=B(_m0(_wo)),_ws=function(_wt,_wu,_wv){while(1){var _ww=B((function(_wx,_wy,_wz){if(!B(_w7(_wj,_wy))){if(!B(A3(_me,_wr,_wy,_wq))){var _wA=new T(function(){return B(A3(_wf,_wj,new T(function(){return B(A3(_8G,_wn,_wy,_wq));}),_wp));});_wt=new T(function(){return B(A3(_8u,_wi,_wx,_wx));});_wu=_wA;_wv=new T(function(){return B(A3(_8u,_wi,_wx,_wz));});return __continue;}else{return new F(function(){return A3(_8u,_wi,_wx,_wz);});}}else{var _wB=_wz;_wt=new T(function(){return B(A3(_8u,_wi,_wx,_wx));});_wu=new T(function(){return B(A3(_wf,_wj,_wy,_wp));});_wv=_wB;return __continue;}})(_wt,_wu,_wv));if(_ww!=__continue){return _ww;}}},_wC=function(_wD,_wE){while(1){var _wF=B((function(_wG,_wH){if(!B(_w7(_wj,_wH))){if(!B(A3(_me,_wr,_wH,_wq))){var _wI=new T(function(){return B(A3(_wf,_wj,new T(function(){return B(A3(_8G,_wn,_wH,_wq));}),_wp));});return new F(function(){return _ws(new T(function(){return B(A3(_8u,_wi,_wG,_wG));}),_wI,_wG);});}else{return E(_wG);}}else{_wD=new T(function(){return B(A3(_8u,_wi,_wG,_wG));});_wE=new T(function(){return B(A3(_wf,_wj,_wH,_wp));});return __continue;}})(_wD,_wE));if(_wF!=__continue){return _wF;}}};return new F(function(){return _wC(_wk,_wl);});}else{return new F(function(){return A2(_8I,_wi,_nq);});}}else{return E(_we);}},_wJ=new T(function(){return B(err(_wd));}),_wK=function(_wL,_wM){var _wN=B(_rC(_wM)),_wO=_wN.a,_wP=_wN.b,_wQ=new T(function(){return B(_sI(new T(function(){return B(_sG(_wL));})));});if(_wP<0){var _wR= -_wP;if(_wR>=0){var _wS=E(_wR);if(!_wS){var _wT=E(_nq);}else{var _wT=B(_vU(_vD,_wS));}if(!B(_4y(_wT,_51))){var _wU=B(_4S(_wO,_wT));return new T2(0,new T(function(){return B(A2(_8I,_wQ,_wU.a));}),new T(function(){return B(_4u(_wU.b,_wP));}));}else{return E(_4t);}}else{return E(_wJ);}}else{var _wV=new T(function(){var _wW=new T(function(){return B(_wh(_wQ,_vC,new T(function(){return B(A2(_8I,_wQ,_vD));}),_wP));});return B(A3(_8u,_wQ,new T(function(){return B(A2(_8I,_wQ,_wO));}),_wW));});return new T2(0,_wV,_7I);}},_wX=function(_wY,_wZ){var _x0=B(_wK(_wY,E(_wZ))),_x1=_x0.a;if(E(_x0.b)<=0){return E(_x1);}else{var _x2=B(_sI(B(_sG(_wY))));return new F(function(){return A3(_86,_x2,_x1,new T(function(){return B(A2(_8I,_x2,_3k));}));});}},_x3=function(_x4,_x5){var _x6=B(_wK(_x4,E(_x5))),_x7=_x6.a;if(E(_x6.b)>=0){return E(_x7);}else{var _x8=B(_sI(B(_sG(_x4))));return new F(function(){return A3(_8G,_x8,_x7,new T(function(){return B(A2(_8I,_x8,_3k));}));});}},_x9=function(_xa,_xb){var _xc=B(_wK(_xa,E(_xb)));return new T2(0,_xc.a,_xc.b);},_xd=function(_xe,_xf){var _xg=B(_wK(_xe,_xf)),_xh=_xg.a,_xi=E(_xg.b),_xj=new T(function(){var _xk=B(_sI(B(_sG(_xe))));if(_xi>=0){return B(A3(_86,_xk,_xh,new T(function(){return B(A2(_8I,_xk,_3k));})));}else{return B(A3(_8G,_xk,_xh,new T(function(){return B(A2(_8I,_xk,_3k));})));}}),_xl=function(_xm){var _xn=_xm-0.5;return (_xn>=0)?(E(_xn)==0)?(!B(_w7(_xe,_xh)))?E(_xj):E(_xh):E(_xj):E(_xh);},_xo=E(_xi);if(!_xo){return new F(function(){return _xl(0);});}else{if(_xo<=0){var _xp= -_xo-0.5;return (_xp>=0)?(E(_xp)==0)?(!B(_w7(_xe,_xh)))?E(_xj):E(_xh):E(_xj):E(_xh);}else{return new F(function(){return _xl(_xo);});}}},_xq=function(_xr,_xs){return new F(function(){return _xd(_xr,E(_xs));});},_xt=function(_xu,_xv){return E(B(_wK(_xu,E(_xv))).a);},_xw={_:0,a:_sF,b:_jo,c:_x9,d:_xt,e:_xq,f:_wX,g:_x3},_xx=new T1(0,1),_xy=function(_xz,_xA){var _xB=E(_xz);return new T2(0,_xB,new T(function(){var _xC=B(_xy(B(_4J(_xB,_xA)),_xA));return new T2(1,_xC.a,_xC.b);}));},_xD=function(_xE){var _xF=B(_xy(_xE,_xx));return new T2(1,_xF.a,_xF.b);},_xG=function(_xH,_xI){var _xJ=B(_xy(_xH,new T(function(){return B(_6W(_xI,_xH));})));return new T2(1,_xJ.a,_xJ.b);},_xK=new T1(0,0),_xL=function(_xM,_xN){var _xO=E(_xM);if(!_xO._){var _xP=_xO.a,_xQ=E(_xN);return (_xQ._==0)?_xP>=_xQ.a:I_compareInt(_xQ.a,_xP)<=0;}else{var _xR=_xO.a,_xS=E(_xN);return (_xS._==0)?I_compareInt(_xR,_xS.a)>=0:I_compare(_xR,_xS.a)>=0;}},_xT=function(_xU,_xV,_xW){if(!B(_xL(_xV,_xK))){var _xX=function(_xY){return (!B(_S(_xY,_xW)))?new T2(1,_xY,new T(function(){return B(_xX(B(_4J(_xY,_xV))));})):__Z;};return new F(function(){return _xX(_xU);});}else{var _xZ=function(_y0){return (!B(_5c(_y0,_xW)))?new T2(1,_y0,new T(function(){return B(_xZ(B(_4J(_y0,_xV))));})):__Z;};return new F(function(){return _xZ(_xU);});}},_y1=function(_y2,_y3,_y4){return new F(function(){return _xT(_y2,B(_6W(_y3,_y2)),_y4);});},_y5=function(_y6,_y7){return new F(function(){return _xT(_y6,_xx,_y7);});},_y8=function(_y9){return new F(function(){return _4G(_y9);});},_ya=function(_yb){return new F(function(){return _6W(_yb,_xx);});},_yc=function(_yd){return new F(function(){return _4J(_yd,_xx);});},_ye=function(_yf){return new F(function(){return _rF(E(_yf));});},_yg={_:0,a:_yc,b:_ya,c:_ye,d:_y8,e:_xD,f:_xG,g:_y5,h:_y1},_yh=function(_yi,_yj){while(1){var _yk=E(_yi);if(!_yk._){var _yl=E(_yk.a);if(_yl==(-2147483648)){_yi=new T1(1,I_fromInt(-2147483648));continue;}else{var _ym=E(_yj);if(!_ym._){return new T1(0,B(_tB(_yl,_ym.a)));}else{_yi=new T1(1,I_fromInt(_yl));_yj=_ym;continue;}}}else{var _yn=_yk.a,_yo=E(_yj);return (_yo._==0)?new T1(1,I_div(_yn,I_fromInt(_yo.a))):new T1(1,I_div(_yn,_yo.a));}}},_yp=function(_yq,_yr){if(!B(_4y(_yr,_w4))){return new F(function(){return _yh(_yq,_yr);});}else{return E(_4t);}},_ys=function(_yt,_yu){while(1){var _yv=E(_yt);if(!_yv._){var _yw=E(_yv.a);if(_yw==(-2147483648)){_yt=new T1(1,I_fromInt(-2147483648));continue;}else{var _yx=E(_yu);if(!_yx._){var _yy=_yx.a;return new T2(0,new T1(0,B(_tB(_yw,_yy))),new T1(0,B(_u7(_yw,_yy))));}else{_yt=new T1(1,I_fromInt(_yw));_yu=_yx;continue;}}}else{var _yz=E(_yu);if(!_yz._){_yt=_yv;_yu=new T1(1,I_fromInt(_yz.a));continue;}else{var _yA=I_divMod(_yv.a,_yz.a);return new T2(0,new T1(1,_yA.a),new T1(1,_yA.b));}}}},_yB=function(_yC,_yD){if(!B(_4y(_yD,_w4))){var _yE=B(_ys(_yC,_yD));return new T2(0,_yE.a,_yE.b);}else{return E(_4t);}},_yF=function(_yG,_yH){while(1){var _yI=E(_yG);if(!_yI._){var _yJ=E(_yI.a);if(_yJ==(-2147483648)){_yG=new T1(1,I_fromInt(-2147483648));continue;}else{var _yK=E(_yH);if(!_yK._){return new T1(0,B(_u7(_yJ,_yK.a)));}else{_yG=new T1(1,I_fromInt(_yJ));_yH=_yK;continue;}}}else{var _yL=_yI.a,_yM=E(_yH);return (_yM._==0)?new T1(1,I_mod(_yL,I_fromInt(_yM.a))):new T1(1,I_mod(_yL,_yM.a));}}},_yN=function(_yO,_yP){if(!B(_4y(_yP,_w4))){return new F(function(){return _yF(_yO,_yP);});}else{return E(_4t);}},_yQ=function(_yR,_yS){while(1){var _yT=E(_yR);if(!_yT._){var _yU=E(_yT.a);if(_yU==(-2147483648)){_yR=new T1(1,I_fromInt(-2147483648));continue;}else{var _yV=E(_yS);if(!_yV._){return new T1(0,quot(_yU,_yV.a));}else{_yR=new T1(1,I_fromInt(_yU));_yS=_yV;continue;}}}else{var _yW=_yT.a,_yX=E(_yS);return (_yX._==0)?new T1(0,I_toInt(I_quot(_yW,I_fromInt(_yX.a)))):new T1(1,I_quot(_yW,_yX.a));}}},_yY=function(_yZ,_z0){if(!B(_4y(_z0,_w4))){return new F(function(){return _yQ(_yZ,_z0);});}else{return E(_4t);}},_z1=function(_z2,_z3){if(!B(_4y(_z3,_w4))){var _z4=B(_4S(_z2,_z3));return new T2(0,_z4.a,_z4.b);}else{return E(_4t);}},_z5=function(_z6,_z7){while(1){var _z8=E(_z6);if(!_z8._){var _z9=E(_z8.a);if(_z9==(-2147483648)){_z6=new T1(1,I_fromInt(-2147483648));continue;}else{var _za=E(_z7);if(!_za._){return new T1(0,_z9%_za.a);}else{_z6=new T1(1,I_fromInt(_z9));_z7=_za;continue;}}}else{var _zb=_z8.a,_zc=E(_z7);return (_zc._==0)?new T1(1,I_rem(_zb,I_fromInt(_zc.a))):new T1(1,I_rem(_zb,_zc.a));}}},_zd=function(_ze,_zf){if(!B(_4y(_zf,_w4))){return new F(function(){return _z5(_ze,_zf);});}else{return E(_4t);}},_zg=function(_zh){return E(_zh);},_zi=function(_zj){return E(_zj);},_zk=function(_zl){var _zm=E(_zl);if(!_zm._){var _zn=E(_zm.a);return (_zn==(-2147483648))?E(_7A):(_zn<0)?new T1(0, -_zn):E(_zm);}else{var _zo=_zm.a;return (I_compareInt(_zo,0)>=0)?E(_zm):new T1(1,I_negate(_zo));}},_zp=new T1(0,0),_zq=new T1(0,-1),_zr=function(_zs){var _zt=E(_zs);if(!_zt._){var _zu=_zt.a;return (_zu>=0)?(E(_zu)==0)?E(_zp):E(_5k):E(_zq);}else{var _zv=I_compareInt(_zt.a,0);return (_zv<=0)?(E(_zv)==0)?E(_zp):E(_zq):E(_5k);}},_zw={_:0,a:_4J,b:_6W,c:_vE,d:_7B,e:_zk,f:_zr,g:_zi},_zx=function(_zy,_zz){var _zA=E(_zy);if(!_zA._){var _zB=_zA.a,_zC=E(_zz);return (_zC._==0)?_zB!=_zC.a:(I_compareInt(_zC.a,_zB)==0)?false:true;}else{var _zD=_zA.a,_zE=E(_zz);return (_zE._==0)?(I_compareInt(_zD,_zE.a)==0)?false:true:(I_compare(_zD,_zE.a)==0)?false:true;}},_zF=new T2(0,_4y,_zx),_zG=function(_zH,_zI){return (!B(_6H(_zH,_zI)))?E(_zH):E(_zI);},_zJ=function(_zK,_zL){return (!B(_6H(_zK,_zL)))?E(_zL):E(_zK);},_zM={_:0,a:_zF,b:_3l,c:_S,d:_6H,e:_5c,f:_xL,g:_zG,h:_zJ},_zN=function(_zO){return new T2(0,E(_zO),E(_nq));},_zP=new T3(0,_zw,_zM,_zN),_zQ={_:0,a:_zP,b:_yg,c:_yY,d:_zd,e:_yp,f:_yN,g:_z1,h:_yB,i:_zg},_zR=function(_zS){return E(E(_zS).b);},_zT=function(_zU){return E(E(_zU).g);},_zV=new T1(0,1),_zW=function(_zX,_zY,_zZ){var _A0=B(_zR(_zX)),_A1=B(_8s(_A0)),_A2=new T(function(){var _A3=new T(function(){var _A4=new T(function(){var _A5=new T(function(){return B(A3(_zT,_zX,_zQ,new T(function(){return B(A3(_a8,_A0,_zY,_zZ));})));});return B(A2(_8I,_A1,_A5));}),_A6=new T(function(){return B(A2(_88,_A1,new T(function(){return B(A2(_8I,_A1,_zV));})));});return B(A3(_8u,_A1,_A6,_A4));});return B(A3(_8u,_A1,_A3,_zZ));});return new F(function(){return A3(_86,_A1,_zY,_A2);});},_A7=1.5707963267948966,_A8=function(_A9){return 0.2/Math.cos(B(_zW(_xw,_A9,_A7))-0.7853981633974483);},_Aa=new T(function(){var _Ab=B(_qh(_A8,1.2,_rB,_rB,_rA,_rB,_rB,_rB,_rB,_rB,_rA,_rA,_rA));return {_:0,a:E(_Ab.a),b:E(_Ab.b),c:E(_Ab.c),d:E(_Ab.d),e:E(_Ab.e),f:E(_Ab.f),g:E(_Ab.g),h:_Ab.h,i:_Ab.i,j:_Ab.j};}),_Ac=0,_Ad=0.3,_Ae=function(_Af){return E(_Ad);},_Ag=new T(function(){var _Ah=B(_qh(_Ae,1.2,_rA,_rB,_rA,_rB,_rB,_rB,_rB,_rB,_rA,_rA,_rA));return {_:0,a:E(_Ah.a),b:E(_Ah.b),c:E(_Ah.c),d:E(_Ah.d),e:E(_Ah.e),f:E(_Ah.f),g:E(_Ah.g),h:_Ah.h,i:_Ah.i,j:_Ah.j};}),_Ai=new T(function(){var _Aj=B(_qh(_Ae,1.2,_rA,_rA,_rB,_rB,_rB,_rB,_rB,_rB,_rA,_rA,_rA));return {_:0,a:E(_Aj.a),b:E(_Aj.b),c:E(_Aj.c),d:E(_Aj.d),e:E(_Aj.e),f:E(_Aj.f),g:E(_Aj.g),h:_Aj.h,i:_Aj.i,j:_Aj.j};}),_Ak=2,_Al=function(_Am){return 0.3/Math.cos(B(_zW(_xw,_Am,_A7))-0.7853981633974483);},_An=new T(function(){var _Ao=B(_qh(_Al,1.2,_Ak,_rA,_rA,_rB,_rB,_rB,_rB,_rB,_rA,_rA,_rA));return {_:0,a:E(_Ao.a),b:E(_Ao.b),c:E(_Ao.c),d:E(_Ao.d),e:E(_Ao.e),f:E(_Ao.f),g:E(_Ao.g),h:_Ao.h,i:_Ao.i,j:_Ao.j};}),_Ap=0.5,_Aq=new T(function(){var _Ar=B(_qh(_Ae,1.2,_rB,_rA,_Ap,_rB,_rB,_rB,_rB,_rB,_rA,_rA,_rA));return {_:0,a:E(_Ar.a),b:E(_Ar.b),c:E(_Ar.c),d:E(_Ar.d),e:E(_Ar.e),f:E(_Ar.f),g:E(_Ar.g),h:_Ar.h,i:_Ar.i,j:_Ar.j};}),_As=new T2(1,_Aq,_w),_At=new T2(1,_An,_As),_Au=new T2(1,_Ai,_At),_Av=new T2(1,_Ag,_Au),_Aw=new T2(1,_Aa,_Av),_Ax=new T(function(){return B(unCStr("Negative range size"));}),_Ay=new T(function(){return B(err(_Ax));}),_Az=function(_){var _AA=B(_ie(_Aw,0))-1|0,_AB=function(_AC){if(_AC>=0){var _AD=newArr(_AC,_ik),_AE=_AD,_AF=E(_AC);if(!_AF){return new T4(0,E(_Ac),E(_AA),0,_AE);}else{var _AG=function(_AH,_AI,_){while(1){var _AJ=E(_AH);if(!_AJ._){return E(_);}else{var _=_AE[_AI]=_AJ.a;if(_AI!=(_AF-1|0)){var _AK=_AI+1|0;_AH=_AJ.b;_AI=_AK;continue;}else{return E(_);}}}},_=B((function(_AL,_AM,_AN,_){var _=_AE[_AN]=_AL;if(_AN!=(_AF-1|0)){return new F(function(){return _AG(_AM,_AN+1|0,_);});}else{return E(_);}})(_Aa,_Av,0,_));return new T4(0,E(_Ac),E(_AA),_AF,_AE);}}else{return E(_Ay);}};if(0>_AA){return new F(function(){return _AB(0);});}else{return new F(function(){return _AB(_AA+1|0);});}},_AO=function(_AP){var _AQ=B(A1(_AP,_));return E(_AQ);},_AR=new T(function(){return B(_AO(_Az));}),_AS="enclose",_AT="outline",_AU="polygon",_AV="z",_AW="y",_AX="x",_AY=function(_AZ){return new F(function(){return _kC(new T2(1,new T2(0,_AX,new T(function(){return E(E(E(E(_AZ).d).a).a);})),new T2(1,new T2(0,_AW,new T(function(){return E(E(E(E(_AZ).d).a).b);})),new T2(1,new T2(0,_AV,new T(function(){return E(E(E(E(_AZ).d).a).c);})),new T2(1,new T2(0,_AU,new T(function(){return E(_AZ).h;})),new T2(1,new T2(0,_AT,new T(function(){return E(_AZ).i;})),new T2(1,new T2(0,_AS,new T(function(){return E(_AZ).j;})),_w)))))));});},_B0=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_B1=new T(function(){return B(err(_B0));}),_B2=new T(function(){return eval("__strict(drawObjects)");}),_B3=new T(function(){return eval("__strict(draw)");}),_B4=function(_B5,_B6){var _B7=jsShowI(_B5);return new F(function(){return _n(fromJSStr(_B7),_B6);});},_B8=function(_B9,_Ba,_Bb){if(_Ba>=0){return new F(function(){return _B4(_Ba,_Bb);});}else{if(_B9<=6){return new F(function(){return _B4(_Ba,_Bb);});}else{return new T2(1,_11,new T(function(){var _Bc=jsShowI(_Ba);return B(_n(fromJSStr(_Bc),new T2(1,_10,_Bb)));}));}}},_Bd=new T(function(){return B(unCStr(")"));}),_Be=function(_Bf,_Bg){var _Bh=new T(function(){var _Bi=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_B8(0,_Bf,_w)),_Bd));})));},1);return B(_n(B(_B8(0,_Bg,_w)),_Bi));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Bh)));});},_Bj=new T2(1,_kB,_w),_Bk=function(_Bl){return E(_Bl);},_Bm=function(_Bn){return E(_Bn);},_Bo=function(_Bp,_Bq){return E(_Bq);},_Br=function(_Bs,_Bt){return E(_Bs);},_Bu=function(_Bv){return E(_Bv);},_Bw=new T2(0,_Bu,_Br),_Bx=function(_By,_Bz){return E(_By);},_BA=new T5(0,_Bw,_Bm,_Bk,_Bo,_Bx),_BB="flipped2",_BC="flipped1",_BD="c1y",_BE="c1x",_BF="w2z",_BG="w2y",_BH="w2x",_BI="w1z",_BJ="w1y",_BK="w1x",_BL="d2z",_BM="d2y",_BN="d2x",_BO="d1z",_BP="d1y",_BQ="d1x",_BR="c2y",_BS="c2x",_BT=function(_BU,_){var _BV=__get(_BU,E(_BK)),_BW=__get(_BU,E(_BJ)),_BX=__get(_BU,E(_BI)),_BY=__get(_BU,E(_BH)),_BZ=__get(_BU,E(_BG)),_C0=__get(_BU,E(_BF)),_C1=__get(_BU,E(_BE)),_C2=__get(_BU,E(_BD)),_C3=__get(_BU,E(_BS)),_C4=__get(_BU,E(_BR)),_C5=__get(_BU,E(_BQ)),_C6=__get(_BU,E(_BP)),_C7=__get(_BU,E(_BO)),_C8=__get(_BU,E(_BN)),_C9=__get(_BU,E(_BM)),_Ca=__get(_BU,E(_BL)),_Cb=__get(_BU,E(_BC)),_Cc=__get(_BU,E(_BB));return {_:0,a:E(new T3(0,E(_BV),E(_BW),E(_BX))),b:E(new T3(0,E(_BY),E(_BZ),E(_C0))),c:E(new T2(0,E(_C1),E(_C2))),d:E(new T2(0,E(_C3),E(_C4))),e:E(new T3(0,E(_C5),E(_C6),E(_C7))),f:E(new T3(0,E(_C8),E(_C9),E(_Ca))),g:E(_Cb),h:E(_Cc)};},_Cd=function(_Ce,_){var _Cf=E(_Ce);if(!_Cf._){return _w;}else{var _Cg=B(_BT(E(_Cf.a),_)),_Ch=B(_Cd(_Cf.b,_));return new T2(1,_Cg,_Ch);}},_Ci=function(_Cj){var _Ck=E(_Cj);return (E(_Ck.b)-E(_Ck.a)|0)+1|0;},_Cl=function(_Cm,_Cn){var _Co=E(_Cm),_Cp=E(_Cn);return (E(_Co.a)>_Cp)?false:_Cp<=E(_Co.b);},_Cq=function(_Cr){return new F(function(){return _B8(0,E(_Cr),_w);});},_Cs=function(_Ct,_Cu,_Cv){return new F(function(){return _B8(E(_Ct),E(_Cu),_Cv);});},_Cw=function(_Cx,_Cy){return new F(function(){return _B8(0,E(_Cx),_Cy);});},_Cz=function(_CA,_CB){return new F(function(){return _49(_Cw,_CA,_CB);});},_CC=new T3(0,_Cs,_Cq,_Cz),_CD=0,_CE=function(_CF,_CG,_CH){return new F(function(){return A1(_CF,new T2(1,_46,new T(function(){return B(A1(_CG,_CH));})));});},_CI=new T(function(){return B(unCStr("foldr1"));}),_CJ=new T(function(){return B(_mP(_CI));}),_CK=function(_CL,_CM){var _CN=E(_CM);if(!_CN._){return E(_CJ);}else{var _CO=_CN.a,_CP=E(_CN.b);if(!_CP._){return E(_CO);}else{return new F(function(){return A2(_CL,_CO,new T(function(){return B(_CK(_CL,_CP));}));});}}},_CQ=new T(function(){return B(unCStr(" out of range "));}),_CR=new T(function(){return B(unCStr("}.index: Index "));}),_CS=new T(function(){return B(unCStr("Ix{"));}),_CT=new T2(1,_10,_w),_CU=new T2(1,_10,_CT),_CV=0,_CW=function(_CX){return E(E(_CX).a);},_CY=function(_CZ,_D0,_D1,_D2,_D3){var _D4=new T(function(){var _D5=new T(function(){var _D6=new T(function(){var _D7=new T(function(){var _D8=new T(function(){return B(A3(_CK,_CE,new T2(1,new T(function(){return B(A3(_CW,_D1,_CV,_D2));}),new T2(1,new T(function(){return B(A3(_CW,_D1,_CV,_D3));}),_w)),_CU));});return B(_n(_CQ,new T2(1,_11,new T2(1,_11,_D8))));});return B(A(_CW,[_D1,_CD,_D0,new T2(1,_10,_D7)]));});return B(_n(_CR,new T2(1,_11,_D6)));},1);return B(_n(_CZ,_D5));},1);return new F(function(){return err(B(_n(_CS,_D4)));});},_D9=function(_Da,_Db,_Dc,_Dd,_De){return new F(function(){return _CY(_Da,_Db,_De,_Dc,_Dd);});},_Df=function(_Dg,_Dh,_Di,_Dj){var _Dk=E(_Di);return new F(function(){return _D9(_Dg,_Dh,_Dk.a,_Dk.b,_Dj);});},_Dl=function(_Dm,_Dn,_Do,_Dp){return new F(function(){return _Df(_Dp,_Do,_Dn,_Dm);});},_Dq=new T(function(){return B(unCStr("Int"));}),_Dr=function(_Ds,_Dt){return new F(function(){return _Dl(_CC,_Dt,_Ds,_Dq);});},_Du=function(_Dv,_Dw){var _Dx=E(_Dv),_Dy=E(_Dx.a),_Dz=E(_Dw);if(_Dy>_Dz){return new F(function(){return _Dr(_Dz,_Dx);});}else{if(_Dz>E(_Dx.b)){return new F(function(){return _Dr(_Dz,_Dx);});}else{return _Dz-_Dy|0;}}},_DA=function(_DB){var _DC=E(_DB);return new F(function(){return _tl(_DC.a,_DC.b);});},_DD=function(_DE){var _DF=E(_DE),_DG=E(_DF.a),_DH=E(_DF.b);return (_DG>_DH)?E(_CD):(_DH-_DG|0)+1|0;},_DI=function(_DJ,_DK){return new F(function(){return _uK(_DK,E(_DJ).a);});},_DL={_:0,a:_vA,b:_DA,c:_Du,d:_DI,e:_Cl,f:_DD,g:_Ci},_DM=function(_DN,_DO,_){while(1){var _DP=B((function(_DQ,_DR,_){var _DS=E(_DQ);if(!_DS._){return new T2(0,_kB,_DR);}else{var _DT=B(A2(_DS.a,_DR,_));_DN=_DS.b;_DO=new T(function(){return E(E(_DT).b);});return __continue;}})(_DN,_DO,_));if(_DP!=__continue){return _DP;}}},_DU=function(_DV,_DW){return new T2(1,_DV,_DW);},_DX=function(_DY,_DZ){var _E0=E(_DZ);return new T2(0,_E0.a,_E0.b);},_E1=function(_E2){return E(E(_E2).f);},_E3=function(_E4,_E5,_E6){var _E7=E(_E5),_E8=_E7.a,_E9=_E7.b,_Ea=function(_){var _Eb=B(A2(_E1,_E4,_E7));if(_Eb>=0){var _Ec=newArr(_Eb,_ik),_Ed=_Ec,_Ee=E(_Eb);if(!_Ee){return new T(function(){return new T4(0,E(_E8),E(_E9),0,_Ed);});}else{var _Ef=function(_Eg,_Eh,_){while(1){var _Ei=E(_Eg);if(!_Ei._){return E(_);}else{var _=_Ed[_Eh]=_Ei.a;if(_Eh!=(_Ee-1|0)){var _Ej=_Eh+1|0;_Eg=_Ei.b;_Eh=_Ej;continue;}else{return E(_);}}}},_=B(_Ef(_E6,0,_));return new T(function(){return new T4(0,E(_E8),E(_E9),_Ee,_Ed);});}}else{return E(_Ay);}};return new F(function(){return _AO(_Ea);});},_Ek=function(_El,_Em,_En,_Eo){var _Ep=new T(function(){var _Eq=E(_Eo),_Er=_Eq.c-1|0,_Es=new T(function(){return B(A2(_dT,_Em,_w));});if(0<=_Er){var _Et=new T(function(){return B(_a4(_Em));}),_Eu=function(_Ev){var _Ew=new T(function(){var _Ex=new T(function(){return B(A1(_En,new T(function(){return E(_Eq.d[_Ev]);})));});return B(A3(_ac,_Et,_DU,_Ex));});return new F(function(){return A3(_aa,_Em,_Ew,new T(function(){if(_Ev!=_Er){return B(_Eu(_Ev+1|0));}else{return E(_Es);}}));});};return B(_Eu(0));}else{return E(_Es);}}),_Ey=new T(function(){return B(_DX(_El,_Eo));});return new F(function(){return A3(_ac,B(_a4(_Em)),function(_Ez){return new F(function(){return _E3(_El,_Ey,_Ez);});},_Ep);});},_EA=function(_EB,_EC,_ED,_EE,_EF,_EG,_EH,_EI,_EJ){var _EK=B(_8u(_EB));return new T2(0,new T3(0,E(B(A1(B(A1(_EK,_EC)),_EG))),E(B(A1(B(A1(_EK,_ED)),_EH))),E(B(A1(B(A1(_EK,_EE)),_EI)))),B(A1(B(A1(_EK,_EF)),_EJ)));},_EL=function(_EM,_EN,_EO,_EP,_EQ,_ER,_ES,_ET,_EU){var _EV=B(_86(_EM));return new T2(0,new T3(0,E(B(A1(B(A1(_EV,_EN)),_ER))),E(B(A1(B(A1(_EV,_EO)),_ES))),E(B(A1(B(A1(_EV,_EP)),_ET)))),B(A1(B(A1(_EV,_EQ)),_EU)));},_EW=1.0e-2,_EX=function(_EY,_EZ,_F0,_F1,_F2,_F3,_F4,_F5,_F6,_F7,_F8,_F9,_Fa,_Fb,_Fc,_Fd,_Fe,_Ff){var _Fg=B(_EA(_jk,_F5,_F6,_F7,_F8,_EW,_EW,_EW,_EW)),_Fh=E(_Fg.a),_Fi=B(_EL(_jk,_F1,_F2,_F3,_F4,_Fh.a,_Fh.b,_Fh.c,_Fg.b)),_Fj=E(_Fi.a);return new F(function(){return _px(_EY,_EZ,_F0,_Fj.a,_Fj.b,_Fj.c,_Fi.b,_F5,_F6,_F7,_F8,_F9,_Fa,_Fb,_Fc,_Fd,_Fe,_Ff);});},_Fk=function(_Fl){var _Fm=E(_Fl),_Fn=E(_Fm.d),_Fo=E(_Fn.a),_Fp=E(_Fm.e),_Fq=E(_Fp.a),_Fr=E(_Fm.f),_Fs=B(_EX(_Fm.a,_Fm.b,_Fm.c,_Fo.a,_Fo.b,_Fo.c,_Fn.b,_Fq.a,_Fq.b,_Fq.c,_Fp.b,_Fr.a,_Fr.b,_Fr.c,_Fm.g,_Fm.h,_Fm.i,_Fm.j));return {_:0,a:E(_Fs.a),b:E(_Fs.b),c:E(_Fs.c),d:E(_Fs.d),e:E(_Fs.e),f:E(_Fs.f),g:E(_Fs.g),h:_Fs.h,i:_Fs.i,j:_Fs.j};},_Ft=function(_Fu,_Fv,_Fw,_Fx,_Fy,_Fz,_FA,_FB,_FC){var _FD=B(_8s(B(_8q(_Fu))));return new F(function(){return A3(_86,_FD,new T(function(){return B(_8w(_Fu,_Fv,_Fw,_Fx,_Fz,_FA,_FB));}),new T(function(){return B(A3(_8u,_FD,_Fy,_FC));}));});},_FE=new T(function(){return B(unCStr("base"));}),_FF=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_FG=new T(function(){return B(unCStr("IOException"));}),_FH=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_FE,_FF,_FG),_FI=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_FH,_w,_w),_FJ=function(_FK){return E(_FI);},_FL=function(_FM){var _FN=E(_FM);return new F(function(){return _3G(B(_3E(_FN.a)),_FJ,_FN.b);});},_FO=new T(function(){return B(unCStr(": "));}),_FP=new T(function(){return B(unCStr(")"));}),_FQ=new T(function(){return B(unCStr(" ("));}),_FR=new T(function(){return B(unCStr("interrupted"));}),_FS=new T(function(){return B(unCStr("system error"));}),_FT=new T(function(){return B(unCStr("unsatisified constraints"));}),_FU=new T(function(){return B(unCStr("user error"));}),_FV=new T(function(){return B(unCStr("permission denied"));}),_FW=new T(function(){return B(unCStr("illegal operation"));}),_FX=new T(function(){return B(unCStr("end of file"));}),_FY=new T(function(){return B(unCStr("resource exhausted"));}),_FZ=new T(function(){return B(unCStr("resource busy"));}),_G0=new T(function(){return B(unCStr("does not exist"));}),_G1=new T(function(){return B(unCStr("already exists"));}),_G2=new T(function(){return B(unCStr("resource vanished"));}),_G3=new T(function(){return B(unCStr("timeout"));}),_G4=new T(function(){return B(unCStr("unsupported operation"));}),_G5=new T(function(){return B(unCStr("hardware fault"));}),_G6=new T(function(){return B(unCStr("inappropriate type"));}),_G7=new T(function(){return B(unCStr("invalid argument"));}),_G8=new T(function(){return B(unCStr("failed"));}),_G9=new T(function(){return B(unCStr("protocol error"));}),_Ga=function(_Gb,_Gc){switch(E(_Gb)){case 0:return new F(function(){return _n(_G1,_Gc);});break;case 1:return new F(function(){return _n(_G0,_Gc);});break;case 2:return new F(function(){return _n(_FZ,_Gc);});break;case 3:return new F(function(){return _n(_FY,_Gc);});break;case 4:return new F(function(){return _n(_FX,_Gc);});break;case 5:return new F(function(){return _n(_FW,_Gc);});break;case 6:return new F(function(){return _n(_FV,_Gc);});break;case 7:return new F(function(){return _n(_FU,_Gc);});break;case 8:return new F(function(){return _n(_FT,_Gc);});break;case 9:return new F(function(){return _n(_FS,_Gc);});break;case 10:return new F(function(){return _n(_G9,_Gc);});break;case 11:return new F(function(){return _n(_G8,_Gc);});break;case 12:return new F(function(){return _n(_G7,_Gc);});break;case 13:return new F(function(){return _n(_G6,_Gc);});break;case 14:return new F(function(){return _n(_G5,_Gc);});break;case 15:return new F(function(){return _n(_G4,_Gc);});break;case 16:return new F(function(){return _n(_G3,_Gc);});break;case 17:return new F(function(){return _n(_G2,_Gc);});break;default:return new F(function(){return _n(_FR,_Gc);});}},_Gd=new T(function(){return B(unCStr("}"));}),_Ge=new T(function(){return B(unCStr("{handle: "));}),_Gf=function(_Gg,_Gh,_Gi,_Gj,_Gk,_Gl){var _Gm=new T(function(){var _Gn=new T(function(){var _Go=new T(function(){var _Gp=E(_Gj);if(!_Gp._){return E(_Gl);}else{var _Gq=new T(function(){return B(_n(_Gp,new T(function(){return B(_n(_FP,_Gl));},1)));},1);return B(_n(_FQ,_Gq));}},1);return B(_Ga(_Gh,_Go));}),_Gr=E(_Gi);if(!_Gr._){return E(_Gn);}else{return B(_n(_Gr,new T(function(){return B(_n(_FO,_Gn));},1)));}}),_Gs=E(_Gk);if(!_Gs._){var _Gt=E(_Gg);if(!_Gt._){return E(_Gm);}else{var _Gu=E(_Gt.a);if(!_Gu._){var _Gv=new T(function(){var _Gw=new T(function(){return B(_n(_Gd,new T(function(){return B(_n(_FO,_Gm));},1)));},1);return B(_n(_Gu.a,_Gw));},1);return new F(function(){return _n(_Ge,_Gv);});}else{var _Gx=new T(function(){var _Gy=new T(function(){return B(_n(_Gd,new T(function(){return B(_n(_FO,_Gm));},1)));},1);return B(_n(_Gu.a,_Gy));},1);return new F(function(){return _n(_Ge,_Gx);});}}}else{return new F(function(){return _n(_Gs.a,new T(function(){return B(_n(_FO,_Gm));},1));});}},_Gz=function(_GA){var _GB=E(_GA);return new F(function(){return _Gf(_GB.a,_GB.b,_GB.c,_GB.d,_GB.f,_w);});},_GC=function(_GD,_GE,_GF){var _GG=E(_GE);return new F(function(){return _Gf(_GG.a,_GG.b,_GG.c,_GG.d,_GG.f,_GF);});},_GH=function(_GI,_GJ){var _GK=E(_GI);return new F(function(){return _Gf(_GK.a,_GK.b,_GK.c,_GK.d,_GK.f,_GJ);});},_GL=function(_GM,_GN){return new F(function(){return _49(_GH,_GM,_GN);});},_GO=new T3(0,_GC,_Gz,_GL),_GP=new T(function(){return new T5(0,_FJ,_GO,_GQ,_FL,_Gz);}),_GQ=function(_GR){return new T2(0,_GP,_GR);},_GS=__Z,_GT=7,_GU=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_GV=new T6(0,_GS,_GT,_w,_GU,_GS,_GS),_GW=new T(function(){return B(_GQ(_GV));}),_GX=function(_){return new F(function(){return die(_GW);});},_GY=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_GZ=new T6(0,_GS,_GT,_w,_GY,_GS,_GS),_H0=new T(function(){return B(_GQ(_GZ));}),_H1=function(_){return new F(function(){return die(_H0);});},_H2=function(_H3,_){return new T2(0,_w,_H3);},_H4=0.6,_H5=1,_H6=new T(function(){return B(unCStr(")"));}),_H7=function(_H8,_H9){var _Ha=new T(function(){var _Hb=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_B8(0,_H8,_w)),_H6));})));},1);return B(_n(B(_B8(0,_H9,_w)),_Hb));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Ha)));});},_Hc=function(_Hd,_He){var _Hf=new T(function(){var _Hg=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_B8(0,_He,_w)),_H6));})));},1);return B(_n(B(_B8(0,_Hd,_w)),_Hg));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Hf)));});},_Hh=function(_Hi){var _Hj=E(_Hi);if(!_Hj._){return E(_H2);}else{var _Hk=new T(function(){return B(_Hh(_Hj.b));}),_Hl=function(_Hm){var _Hn=E(_Hm);if(!_Hn._){return E(_Hk);}else{var _Ho=_Hn.a,_Hp=new T(function(){return B(_Hl(_Hn.b));}),_Hq=new T(function(){return 0.1*E(E(_Ho).e)/1.0e-2;}),_Hr=new T(function(){var _Hs=E(_Ho);if(_Hs.a!=_Hs.b){return E(_H5);}else{return E(_H4);}}),_Ht=function(_Hu,_){var _Hv=E(_Hu),_Hw=_Hv.c,_Hx=_Hv.d,_Hy=E(_Hv.a),_Hz=E(_Hv.b),_HA=E(_Ho),_HB=_HA.a,_HC=_HA.b,_HD=E(_HA.c),_HE=_HD.b,_HF=E(_HD.a),_HG=_HF.a,_HH=_HF.b,_HI=_HF.c,_HJ=E(_HA.d),_HK=_HJ.b,_HL=E(_HJ.a),_HM=_HL.a,_HN=_HL.b,_HO=_HL.c;if(_Hy>_HB){return new F(function(){return _H1(_);});}else{if(_HB>_Hz){return new F(function(){return _H1(_);});}else{if(_Hy>_HC){return new F(function(){return _GX(_);});}else{if(_HC>_Hz){return new F(function(){return _GX(_);});}else{var _HP=_HB-_Hy|0;if(0>_HP){return new F(function(){return _H7(_Hw,_HP);});}else{if(_HP>=_Hw){return new F(function(){return _H7(_Hw,_HP);});}else{var _HQ=E(_Hx[_HP]),_HR=E(_HQ.c),_HS=_HR.b,_HT=E(_HR.a),_HU=_HT.a,_HV=_HT.b,_HW=_HT.c,_HX=E(_HQ.e),_HY=E(_HX.a),_HZ=B(_EA(_jk,_HG,_HH,_HI,_HE,_HU,_HV,_HW,_HS)),_I0=E(_HZ.a),_I1=B(_EA(_jk,_I0.a,_I0.b,_I0.c,_HZ.b,_HG,_HH,_HI,_HE)),_I2=E(_I1.a),_I3=_HC-_Hy|0;if(0>_I3){return new F(function(){return _Hc(_I3,_Hw);});}else{if(_I3>=_Hw){return new F(function(){return _Hc(_I3,_Hw);});}else{var _I4=E(_Hx[_I3]),_I5=E(_I4.c),_I6=_I5.b,_I7=E(_I5.a),_I8=_I7.a,_I9=_I7.b,_Ia=_I7.c,_Ib=E(_I4.e),_Ic=E(_Ib.a),_Id=B(_EA(_jk,_HM,_HN,_HO,_HK,_I8,_I9,_Ia,_I6)),_Ie=E(_Id.a),_If=B(_EA(_jk,_Ie.a,_Ie.b,_Ie.c,_Id.b,_HM,_HN,_HO,_HK)),_Ig=E(_If.a),_Ih=E(_I2.a)+E(_I2.b)+E(_I2.c)+E(_I1.b)+E(_Ig.a)+E(_Ig.b)+E(_Ig.c)+E(_If.b);if(!_Ih){var _Ii=B(A2(_Hp,_Hv,_));return new T2(0,new T2(1,_kB,new T(function(){return E(E(_Ii).a);})),new T(function(){return E(E(_Ii).b);}));}else{var _Ij=new T(function(){return  -((B(_Ft(_jQ,_HY.a,_HY.b,_HY.c,_HX.b,_HG,_HH,_HI,_HE))-B(_Ft(_jQ,_Ic.a,_Ic.b,_Ic.c,_Ib.b,_HM,_HN,_HO,_HK))-E(_Hq))/_Ih);}),_Ik=function(_Il,_Im,_In,_Io,_){var _Ip=new T(function(){var _Iq=function(_Ir,_Is,_It,_Iu,_Iv){if(_Ir>_HC){return E(_Iv);}else{if(_HC>_Is){return E(_Iv);}else{var _Iw=function(_){var _Ix=newArr(_It,_ik),_Iy=_Ix,_Iz=function(_IA,_){while(1){if(_IA!=_It){var _=_Iy[_IA]=_Iu[_IA],_IB=_IA+1|0;_IA=_IB;continue;}else{return E(_);}}},_=B(_Iz(0,_)),_IC=_HC-_Ir|0;if(0>_IC){return new F(function(){return _Hc(_IC,_It);});}else{if(_IC>=_It){return new F(function(){return _Hc(_IC,_It);});}else{var _=_Iy[_IC]=new T(function(){var _ID=E(_Iu[_IC]),_IE=E(_ID.e),_IF=E(_IE.a),_IG=B(_EA(_jk,_I8,_I9,_Ia,_I6,_HM,_HN,_HO,_HK)),_IH=E(_IG.a),_II=E(_Ij)*E(_Hr),_IJ=B(_EA(_jk,_IH.a,_IH.b,_IH.c,_IG.b,_II,_II,_II,_II)),_IK=E(_IJ.a),_IL=B(_EL(_jk,_IF.a,_IF.b,_IF.c,_IE.b, -E(_IK.a), -E(_IK.b), -E(_IK.c), -E(_IJ.b)));return {_:0,a:E(_ID.a),b:E(_ID.b),c:E(_ID.c),d:E(_ID.d),e:E(new T2(0,E(_IL.a),E(_IL.b))),f:E(_ID.f),g:E(_ID.g),h:_ID.h,i:_ID.i,j:_ID.j};});return new T4(0,E(_Ir),E(_Is),_It,_Iy);}}};return new F(function(){return _AO(_Iw);});}}};if(_Il>_HB){return B(_Iq(_Il,_Im,_In,_Io,new T4(0,E(_Il),E(_Im),_In,_Io)));}else{if(_HB>_Im){return B(_Iq(_Il,_Im,_In,_Io,new T4(0,E(_Il),E(_Im),_In,_Io)));}else{var _IM=function(_){var _IN=newArr(_In,_ik),_IO=_IN,_IP=function(_IQ,_){while(1){if(_IQ!=_In){var _=_IO[_IQ]=_Io[_IQ],_IR=_IQ+1|0;_IQ=_IR;continue;}else{return E(_);}}},_=B(_IP(0,_)),_IS=_HB-_Il|0;if(0>_IS){return new F(function(){return _H7(_In,_IS);});}else{if(_IS>=_In){return new F(function(){return _H7(_In,_IS);});}else{var _=_IO[_IS]=new T(function(){var _IT=E(_Io[_IS]),_IU=E(_IT.e),_IV=E(_IU.a),_IW=B(_EA(_jk,_HU,_HV,_HW,_HS,_HG,_HH,_HI,_HE)),_IX=E(_IW.a),_IY=E(_Ij)*E(_Hr),_IZ=B(_EA(_jk,_IX.a,_IX.b,_IX.c,_IW.b,_IY,_IY,_IY,_IY)),_J0=E(_IZ.a),_J1=B(_EL(_jk,_IV.a,_IV.b,_IV.c,_IU.b,_J0.a,_J0.b,_J0.c,_IZ.b));return {_:0,a:E(_IT.a),b:E(_IT.b),c:E(_IT.c),d:E(_IT.d),e:E(new T2(0,E(_J1.a),E(_J1.b))),f:E(_IT.f),g:E(_IT.g),h:_IT.h,i:_IT.i,j:_IT.j};});return new T4(0,E(_Il),E(_Im),_In,_IO);}}},_J2=B(_AO(_IM));return B(_Iq(E(_J2.a),E(_J2.b),_J2.c,_J2.d,_J2));}}});return new T2(0,_kB,_Ip);};if(!E(_HA.f)){var _J3=B(_Ik(_Hy,_Hz,_Hw,_Hx,_)),_J4=B(A2(_Hp,new T(function(){return E(E(_J3).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_J3).a);}),new T(function(){return E(E(_J4).a);})),new T(function(){return E(E(_J4).b);}));}else{if(E(_Ij)<0){var _J5=B(A2(_Hp,_Hv,_));return new T2(0,new T2(1,_kB,new T(function(){return E(E(_J5).a);})),new T(function(){return E(E(_J5).b);}));}else{var _J6=B(_Ik(_Hy,_Hz,_Hw,_Hx,_)),_J7=B(A2(_Hp,new T(function(){return E(E(_J6).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_J6).a);}),new T(function(){return E(E(_J7).a);})),new T(function(){return E(E(_J7).b);}));}}}}}}}}}}}};return E(_Ht);}};return new F(function(){return _Hl(_Hj.a);});}},_J8=function(_,_J9){var _Ja=new T(function(){return B(_Hh(E(_J9).a));}),_Jb=function(_Jc){var _Jd=E(_Jc);return (_Jd==1)?E(new T2(1,_Ja,_w)):new T2(1,_Ja,new T(function(){return B(_Jb(_Jd-1|0));}));},_Je=B(_DM(B(_Jb(5)),new T(function(){return E(E(_J9).b);}),_)),_Jf=new T(function(){return B(_Ek(_DL,_BA,_Fk,new T(function(){return E(E(_Je).b);})));});return new T2(0,_kB,_Jf);},_Jg=function(_Jh,_Ji,_Jj,_Jk,_Jl){var _Jm=B(_8s(B(_8q(_Jh))));return new F(function(){return A3(_86,_Jm,new T(function(){return B(A3(_8u,_Jm,_Ji,_Jk));}),new T(function(){return B(A3(_8u,_Jm,_Jj,_Jl));}));});},_Jn=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Jo=new T6(0,_GS,_GT,_w,_Jn,_GS,_GS),_Jp=new T(function(){return B(_GQ(_Jo));}),_Jq=function(_){return new F(function(){return die(_Jp);});},_Jr=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Js=new T6(0,_GS,_GT,_w,_Jr,_GS,_GS),_Jt=new T(function(){return B(_GQ(_Js));}),_Ju=function(_){return new F(function(){return die(_Jt);});},_Jv=false,_Jw=true,_Jx=function(_Jy){var _Jz=E(_Jy),_JA=_Jz.b,_JB=E(_Jz.d),_JC=E(_Jz.e),_JD=E(_JC.a),_JE=E(_Jz.g),_JF=B(A1(_JA,_JB.a)),_JG=B(_m2(_jQ,_JF.a,_JF.b,_JF.c,_JE.a,_JE.b,_JE.c));return {_:0,a:E(_Jz.a),b:E(_JA),c:E(_Jz.c),d:E(_JB),e:E(new T2(0,E(new T3(0,E(_JD.a)+E(_JG.a)*1.0e-2,E(_JD.b)+E(_JG.b)*1.0e-2,E(_JD.c)+E(_JG.c)*1.0e-2)),E(_JC.b))),f:E(_Jz.f),g:E(_JE),h:_Jz.h,i:_Jz.i,j:_Jz.j};},_JH=new T(function(){return eval("__strict(collideBound)");}),_JI=new T(function(){return eval("__strict(mouseContact)");}),_JJ=new T(function(){return eval("__strict(collide)");}),_JK=function(_JL){var _JM=E(_JL);if(!_JM._){return __Z;}else{return new F(function(){return _n(_JM.a,new T(function(){return B(_JK(_JM.b));},1));});}},_JN=0,_JO=new T3(0,E(_JN),E(_JN),E(_JN)),_JP=new T2(0,E(_JO),E(_JN)),_JQ=new T2(0,_jQ,_kp),_JR=new T(function(){return B(_hQ(_JQ));}),_JS=function(_JT,_){var _JU=B(_Ek(_DL,_BA,_Jx,_JT)),_JV=E(_JU.a),_JW=E(_JU.b);if(_JV<=_JW){var _JX=function(_JY,_JZ,_K0,_K1,_K2,_){if(_JZ>_JY){return new F(function(){return _Ju(_);});}else{if(_JY>_K0){return new F(function(){return _Ju(_);});}else{var _K3=new T(function(){var _K4=_JY-_JZ|0;if(0>_K4){return B(_Hc(_K4,_K1));}else{if(_K4>=_K1){return B(_Hc(_K4,_K1));}else{return E(_K2[_K4]);}}}),_K5=function(_K6,_K7,_K8,_K9,_Ka,_){var _Kb=E(_K6);if(!_Kb._){return new T2(0,_w,new T4(0,E(_K7),E(_K8),_K9,_Ka));}else{var _Kc=E(_Kb.a);if(_K7>_Kc){return new F(function(){return _Jq(_);});}else{if(_Kc>_K8){return new F(function(){return _Jq(_);});}else{var _Kd=_Kc-_K7|0;if(0>_Kd){return new F(function(){return _H7(_K9,_Kd);});}else{if(_Kd>=_K9){return new F(function(){return _H7(_K9,_Kd);});}else{var _Ke=__app2(E(_JJ),B(_AY(E(_K3))),B(_AY(E(_Ka[_Kd])))),_Kf=__arr2lst(0,_Ke),_Kg=B(_Cd(_Kf,_)),_Kh=B(_K5(_Kb.b,_K7,_K8,_K9,_Ka,_)),_Ki=new T(function(){var _Kj=new T(function(){return _JY!=_Kc;}),_Kk=function(_Kl){var _Km=E(_Kl);if(!_Km._){return __Z;}else{var _Kn=_Km.b,_Ko=E(_Km.a),_Kp=E(_Ko.b),_Kq=E(_Ko.a),_Kr=E(_Ko.c),_Ks=_Kr.a,_Kt=_Kr.b,_Ku=E(_Ko.e),_Kv=E(_Ko.d),_Kw=_Kv.a,_Kx=_Kv.b,_Ky=E(_Ko.f),_Kz=new T(function(){var _KA=B(_lf(_jQ,_Ky.a,_Ky.b,_Ky.c)),_KB=Math.sqrt(B(_Jg(_jQ,_Kw,_Kx,_Kw,_Kx)));return new T3(0,_KB*E(_KA.a),_KB*E(_KA.b),_KB*E(_KA.c));}),_KC=new T(function(){var _KD=B(_lf(_jQ,_Ku.a,_Ku.b,_Ku.c)),_KE=Math.sqrt(B(_Jg(_jQ,_Ks,_Kt,_Ks,_Kt)));return new T3(0,_KE*E(_KD.a),_KE*E(_KD.b),_KE*E(_KD.c));}),_KF=new T(function(){var _KG=B(A1(_JR,_Kp)),_KH=B(_lf(_jQ,_KG.a,_KG.b,_KG.c));return new T3(0,E(_KH.a),E(_KH.b),E(_KH.c));}),_KI=new T(function(){var _KJ=B(A1(_JR,_Kq)),_KK=B(_lf(_jQ,_KJ.a,_KJ.b,_KJ.c));return new T3(0,E(_KK.a),E(_KK.b),E(_KK.c));}),_KL=E(_Kp.a)+ -E(_Kq.a),_KM=E(_Kp.b)+ -E(_Kq.b),_KN=E(_Kp.c)+ -E(_Kq.c),_KO=new T(function(){return Math.sqrt(B(_8w(_jQ,_KL,_KM,_KN,_KL,_KM,_KN)));}),_KP=new T(function(){var _KQ=1/E(_KO);return new T3(0,_KL*_KQ,_KM*_KQ,_KN*_KQ);}),_KR=new T(function(){if(!E(_Ko.g)){return E(_KP);}else{var _KS=E(_KP);return new T3(0,-1*E(_KS.a),-1*E(_KS.b),-1*E(_KS.c));}}),_KT=new T(function(){if(!E(_Ko.h)){return E(_KP);}else{var _KU=E(_KP);return new T3(0,-1*E(_KU.a),-1*E(_KU.b),-1*E(_KU.c));}});return (!E(_Kj))?new T2(1,new T(function(){var _KV=E(_KR),_KW=E(_KV.b),_KX=E(_KV.c),_KY=E(_KV.a),_KZ=E(_KI),_L0=E(_KZ.c),_L1=E(_KZ.b),_L2=E(_KZ.a),_L3=E(_KC),_L4=E(_L3.c),_L5=E(_L3.b),_L6=E(_L3.a),_L7=_KW*_L0-_L1*_KX,_L8=_KX*_L2-_L0*_KY,_L9=_KY*_L1-_L2*_KW,_La=B(_8w(_jQ,_L8*_L4-_L5*_L9,_L9*_L6-_L4*_L7,_L7*_L5-_L6*_L8,_L2,_L1,_L0));return new T6(0,_JY,_Kc,E(new T2(0,E(new T3(0,E(_L7),E(_L8),E(_L9))),E(_La))),E(_JP),_KO,_Jv);}),new T2(1,new T(function(){var _Lb=E(_KT),_Lc=E(_Lb.b),_Ld=E(_Lb.c),_Le=E(_Lb.a),_Lf=E(_KF),_Lg=E(_Lf.c),_Lh=E(_Lf.b),_Li=E(_Lf.a),_Lj=E(_Kz),_Lk=E(_Lj.c),_Ll=E(_Lj.b),_Lm=E(_Lj.a),_Ln=_Lc*_Lg-_Lh*_Ld,_Lo=_Ld*_Li-_Lg*_Le,_Lp=_Le*_Lh-_Li*_Lc,_Lq=B(_8w(_jQ,_Lo*_Lk-_Ll*_Lp,_Lp*_Lm-_Lk*_Ln,_Ln*_Ll-_Lm*_Lo,_Li,_Lh,_Lg));return new T6(0,_JY,_Kc,E(_JP),E(new T2(0,E(new T3(0,E(_Ln),E(_Lo),E(_Lp))),E(_Lq))),_KO,_Jv);}),new T(function(){return B(_Kk(_Kn));}))):new T2(1,new T(function(){var _Lr=E(_KR),_Ls=E(_Lr.b),_Lt=E(_Lr.c),_Lu=E(_Lr.a),_Lv=E(_KI),_Lw=_Lv.a,_Lx=_Lv.b,_Ly=_Lv.c,_Lz=B(_m2(_jQ,_Lu,_Ls,_Lt,_Lw,_Lx,_Ly)),_LA=E(_KC),_LB=E(_LA.c),_LC=E(_LA.b),_LD=E(_LA.a),_LE=B(_8w(_jQ,_Ls*_LB-_LC*_Lt,_Lt*_LD-_LB*_Lu,_Lu*_LC-_LD*_Ls,_Lw,_Lx,_Ly)),_LF=E(_KT),_LG=E(_LF.b),_LH=E(_LF.c),_LI=E(_LF.a),_LJ=E(_KF),_LK=_LJ.a,_LL=_LJ.b,_LM=_LJ.c,_LN=B(_m2(_jQ,_LI,_LG,_LH,_LK,_LL,_LM)),_LO=E(_Kz),_LP=E(_LO.c),_LQ=E(_LO.b),_LR=E(_LO.a),_LS=B(_8w(_jQ,_LG*_LP-_LQ*_LH,_LH*_LR-_LP*_LI,_LI*_LQ-_LR*_LG,_LK,_LL,_LM));return new T6(0,_JY,_Kc,E(new T2(0,E(new T3(0,E(_Lz.a),E(_Lz.b),E(_Lz.c))),E(_LE))),E(new T2(0,E(new T3(0,E(_LN.a),E(_LN.b),E(_LN.c))),E(_LS))),_KO,_Jw);}),new T(function(){return B(_Kk(_Kn));}));}};return B(_Kk(_Kg));});return new T2(0,new T2(1,_Ki,new T(function(){return E(E(_Kh).a);})),new T(function(){return E(E(_Kh).b);}));}}}}}},_LT=B(_K5(B(_sK(_JY,_JW)),_JZ,_K0,_K1,_K2,_)),_LU=E(_K3),_LV=E(_LU.d).a,_LW=__app1(E(_JH),B(_AY(_LU))),_LX=__arr2lst(0,_LW),_LY=B(_Cd(_LX,_)),_LZ=__app1(E(_JI),_JY),_M0=__arr2lst(0,_LZ),_M1=B(_Cd(_M0,_));if(_JY!=_JW){var _M2=E(_LT),_M3=E(_M2.b),_M4=B(_JX(_JY+1|0,E(_M3.a),E(_M3.b),_M3.c,_M3.d,_)),_M5=new T(function(){var _M6=new T(function(){var _M7=B(A1(_JR,_LV)),_M8=B(_lf(_jQ,_M7.a,_M7.b,_M7.c));return new T3(0,E(_M8.a),E(_M8.b),E(_M8.c));}),_M9=new T(function(){var _Ma=new T(function(){return B(_JK(_M2.a));}),_Mb=function(_Mc){var _Md=E(_Mc);if(!_Md._){return E(_Ma);}else{var _Me=E(_Md.a),_Mf=E(_Me.b),_Mg=E(_Me.a),_Mh=E(_Me.c),_Mi=_Mh.a,_Mj=_Mh.b,_Mk=E(_Me.e);return new T2(1,new T(function(){var _Ml=E(_Mf.a)+ -E(_Mg.a),_Mm=E(_Mf.b)+ -E(_Mg.b),_Mn=E(_Mf.c)+ -E(_Mg.c),_Mo=B(A1(_JR,_Mg)),_Mp=B(_lf(_jQ,_Mo.a,_Mo.b,_Mo.c)),_Mq=_Mp.a,_Mr=_Mp.b,_Ms=_Mp.c,_Mt=Math.sqrt(B(_8w(_jQ,_Ml,_Mm,_Mn,_Ml,_Mm,_Mn))),_Mu=1/_Mt,_Mv=_Ml*_Mu,_Mw=_Mm*_Mu,_Mx=_Mn*_Mu,_My=B(_m2(_jQ,_Mv,_Mw,_Mx,_Mq,_Mr,_Ms)),_Mz=B(_lf(_jQ,_Mk.a,_Mk.b,_Mk.c)),_MA=Math.sqrt(B(_Jg(_jQ,_Mi,_Mj,_Mi,_Mj))),_MB=_MA*E(_Mz.a),_MC=_MA*E(_Mz.b),_MD=_MA*E(_Mz.c),_ME=B(_8w(_jQ,_Mw*_MD-_MC*_Mx,_Mx*_MB-_MD*_Mv,_Mv*_MC-_MB*_Mw,_Mq,_Mr,_Ms));return new T6(0,_JY,_JY,E(new T2(0,E(new T3(0,E(_My.a),E(_My.b),E(_My.c))),E(_ME))),E(_JP),_Mt,_Jw);}),new T(function(){return B(_Mb(_Md.b));}));}};return B(_Mb(_LY));}),_MF=function(_MG){var _MH=E(_MG);if(!_MH._){return E(_M9);}else{var _MI=E(_MH.a),_MJ=E(_MI.b),_MK=new T(function(){var _ML=E(_LV),_MM=E(_MJ.c)+ -E(_ML.c),_MN=E(_MJ.b)+ -E(_ML.b),_MO=E(_MJ.a)+ -E(_ML.a),_MP=Math.sqrt(B(_8w(_jQ,_MO,_MN,_MM,_MO,_MN,_MM))),_MQ=function(_MR,_MS,_MT){var _MU=E(_M6),_MV=_MU.a,_MW=_MU.b,_MX=_MU.c,_MY=B(_m2(_jQ,_MR,_MS,_MT,_MV,_MW,_MX)),_MZ=B(_8w(_jQ,_MS*0-0*_MT,_MT*0-0*_MR,_MR*0-0*_MS,_MV,_MW,_MX));return new T6(0,_JY,_JY,new T2(0,E(new T3(0,E(_MY.a),E(_MY.b),E(_MY.c))),E(_MZ)),_JP,_MP,_Jw);};if(!E(_MI.g)){var _N0=1/_MP,_N1=B(_MQ(_MO*_N0,_MN*_N0,_MM*_N0));return new T6(0,_N1.a,_N1.b,E(_N1.c),E(_N1.d),_N1.e,_N1.f);}else{var _N2=1/_MP,_N3=B(_MQ(-1*_MO*_N2,-1*_MN*_N2,-1*_MM*_N2));return new T6(0,_N3.a,_N3.b,E(_N3.c),E(_N3.d),_N3.e,_N3.f);}});return new T2(1,_MK,new T(function(){return B(_MF(_MH.b));}));}};return B(_MF(_M1));});return new T2(0,new T2(1,_M5,new T(function(){return E(E(_M4).a);})),new T(function(){return E(E(_M4).b);}));}else{var _N4=new T(function(){var _N5=new T(function(){var _N6=B(A1(_JR,_LV)),_N7=B(_lf(_jQ,_N6.a,_N6.b,_N6.c));return new T3(0,E(_N7.a),E(_N7.b),E(_N7.c));}),_N8=new T(function(){var _N9=new T(function(){return B(_JK(E(_LT).a));}),_Na=function(_Nb){var _Nc=E(_Nb);if(!_Nc._){return E(_N9);}else{var _Nd=E(_Nc.a),_Ne=E(_Nd.b),_Nf=E(_Nd.a),_Ng=E(_Nd.c),_Nh=_Ng.a,_Ni=_Ng.b,_Nj=E(_Nd.e);return new T2(1,new T(function(){var _Nk=E(_Ne.a)+ -E(_Nf.a),_Nl=E(_Ne.b)+ -E(_Nf.b),_Nm=E(_Ne.c)+ -E(_Nf.c),_Nn=B(A1(_JR,_Nf)),_No=B(_lf(_jQ,_Nn.a,_Nn.b,_Nn.c)),_Np=_No.a,_Nq=_No.b,_Nr=_No.c,_Ns=Math.sqrt(B(_8w(_jQ,_Nk,_Nl,_Nm,_Nk,_Nl,_Nm))),_Nt=1/_Ns,_Nu=_Nk*_Nt,_Nv=_Nl*_Nt,_Nw=_Nm*_Nt,_Nx=B(_m2(_jQ,_Nu,_Nv,_Nw,_Np,_Nq,_Nr)),_Ny=B(_lf(_jQ,_Nj.a,_Nj.b,_Nj.c)),_Nz=Math.sqrt(B(_Jg(_jQ,_Nh,_Ni,_Nh,_Ni))),_NA=_Nz*E(_Ny.a),_NB=_Nz*E(_Ny.b),_NC=_Nz*E(_Ny.c),_ND=B(_8w(_jQ,_Nv*_NC-_NB*_Nw,_Nw*_NA-_NC*_Nu,_Nu*_NB-_NA*_Nv,_Np,_Nq,_Nr));return new T6(0,_JY,_JY,E(new T2(0,E(new T3(0,E(_Nx.a),E(_Nx.b),E(_Nx.c))),E(_ND))),E(_JP),_Ns,_Jw);}),new T(function(){return B(_Na(_Nc.b));}));}};return B(_Na(_LY));}),_NE=function(_NF){var _NG=E(_NF);if(!_NG._){return E(_N8);}else{var _NH=E(_NG.a),_NI=E(_NH.b),_NJ=new T(function(){var _NK=E(_LV),_NL=E(_NI.c)+ -E(_NK.c),_NM=E(_NI.b)+ -E(_NK.b),_NN=E(_NI.a)+ -E(_NK.a),_NO=Math.sqrt(B(_8w(_jQ,_NN,_NM,_NL,_NN,_NM,_NL))),_NP=function(_NQ,_NR,_NS){var _NT=E(_N5),_NU=_NT.a,_NV=_NT.b,_NW=_NT.c,_NX=B(_m2(_jQ,_NQ,_NR,_NS,_NU,_NV,_NW)),_NY=B(_8w(_jQ,_NR*0-0*_NS,_NS*0-0*_NQ,_NQ*0-0*_NR,_NU,_NV,_NW));return new T6(0,_JY,_JY,new T2(0,E(new T3(0,E(_NX.a),E(_NX.b),E(_NX.c))),E(_NY)),_JP,_NO,_Jw);};if(!E(_NH.g)){var _NZ=1/_NO,_O0=B(_NP(_NN*_NZ,_NM*_NZ,_NL*_NZ));return new T6(0,_O0.a,_O0.b,E(_O0.c),E(_O0.d),_O0.e,_O0.f);}else{var _O1=1/_NO,_O2=B(_NP(-1*_NN*_O1,-1*_NM*_O1,-1*_NL*_O1));return new T6(0,_O2.a,_O2.b,E(_O2.c),E(_O2.d),_O2.e,_O2.f);}});return new T2(1,_NJ,new T(function(){return B(_NE(_NG.b));}));}};return B(_NE(_M1));});return new T2(0,new T2(1,_N4,_w),new T(function(){return E(E(_LT).b);}));}}}},_O3=B(_JX(_JV,_JV,_JW,_JU.c,_JU.d,_));return new F(function(){return _J8(_,_O3);});}else{return new F(function(){return _J8(_,new T2(0,_w,_JU));});}},_O4=new T(function(){return eval("__strict(passObject)");}),_O5=new T(function(){return eval("__strict(refresh)");}),_O6=function(_O7,_){var _O8=__app0(E(_O5)),_O9=__app0(E(_B3)),_Oa=E(_O7),_Ob=_Oa.c,_Oc=_Oa.d,_Od=E(_Oa.a),_Oe=E(_Oa.b);if(_Od<=_Oe){if(_Od>_Oe){return E(_B1);}else{if(0>=_Ob){return new F(function(){return _Be(_Ob,0);});}else{var _Of=E(_O4),_Og=__app2(_Of,_Od,B(_AY(E(_Oc[0]))));if(_Od!=_Oe){var _Oh=function(_Oi,_){if(_Od>_Oi){return E(_B1);}else{if(_Oi>_Oe){return E(_B1);}else{var _Oj=_Oi-_Od|0;if(0>_Oj){return new F(function(){return _Be(_Ob,_Oj);});}else{if(_Oj>=_Ob){return new F(function(){return _Be(_Ob,_Oj);});}else{var _Ok=__app2(_Of,_Oi,B(_AY(E(_Oc[_Oj]))));if(_Oi!=_Oe){var _Ol=B(_Oh(_Oi+1|0,_));return new T2(1,_kB,_Ol);}else{return _Bj;}}}}}},_Om=B(_Oh(_Od+1|0,_)),_On=__app0(E(_B2)),_Oo=B(_JS(_Oa,_));return new T(function(){return E(E(_Oo).b);});}else{var _Op=__app0(E(_B2)),_Oq=B(_JS(_Oa,_));return new T(function(){return E(E(_Oq).b);});}}}}else{var _Or=__app0(E(_B2)),_Os=B(_JS(_Oa,_));return new T(function(){return E(E(_Os).b);});}},_Ot=function(_Ou,_){while(1){var _Ov=E(_Ou);if(!_Ov._){return _kB;}else{var _Ow=_Ov.b,_Ox=E(_Ov.a);switch(_Ox._){case 0:var _Oy=B(A1(_Ox.a,_));_Ou=B(_n(_Ow,new T2(1,_Oy,_w)));continue;case 1:_Ou=B(_n(_Ow,_Ox.a));continue;default:_Ou=_Ow;continue;}}}},_Oz=function(_OA,_OB,_){var _OC=E(_OA);switch(_OC._){case 0:var _OD=B(A1(_OC.a,_));return new F(function(){return _Ot(B(_n(_OB,new T2(1,_OD,_w))),_);});break;case 1:return new F(function(){return _Ot(B(_n(_OB,_OC.a)),_);});break;default:return new F(function(){return _Ot(_OB,_);});}},_OE=new T0(2),_OF=function(_OG){return new T0(2);},_OH=function(_OI,_OJ,_OK){return function(_){var _OL=E(_OI),_OM=rMV(_OL),_ON=E(_OM);if(!_ON._){var _OO=new T(function(){var _OP=new T(function(){return B(A1(_OK,_kB));});return B(_n(_ON.b,new T2(1,new T2(0,_OJ,function(_OQ){return E(_OP);}),_w)));}),_=wMV(_OL,new T2(0,_ON.a,_OO));return _OE;}else{var _OR=E(_ON.a);if(!_OR._){var _=wMV(_OL,new T2(0,_OJ,_w));return new T(function(){return B(A1(_OK,_kB));});}else{var _=wMV(_OL,new T1(1,_OR.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OK,_kB));}),new T2(1,new T(function(){return B(A2(_OR.a,_OJ,_OF));}),_w)));}}};},_OS=new T(function(){return E(_qg);}),_OT=new T(function(){return eval("window.requestAnimationFrame");}),_OU=new T1(1,_w),_OV=function(_OW,_OX){return function(_){var _OY=E(_OW),_OZ=rMV(_OY),_P0=E(_OZ);if(!_P0._){var _P1=_P0.a,_P2=E(_P0.b);if(!_P2._){var _=wMV(_OY,_OU);return new T(function(){return B(A1(_OX,_P1));});}else{var _P3=E(_P2.a),_=wMV(_OY,new T2(0,_P3.a,_P2.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OX,_P1));}),new T2(1,new T(function(){return B(A1(_P3.b,_OF));}),_w)));}}else{var _P4=new T(function(){var _P5=function(_P6){var _P7=new T(function(){return B(A1(_OX,_P6));});return function(_P8){return E(_P7);};};return B(_n(_P0.a,new T2(1,_P5,_w)));}),_=wMV(_OY,new T1(1,_P4));return _OE;}};},_P9=function(_Pa,_Pb){return new T1(0,B(_OV(_Pa,_Pb)));},_Pc=function(_Pd,_Pe){var _Pf=new T(function(){return new T1(0,B(_OH(_Pd,_kB,_OF)));});return function(_){var _Pg=__createJSFunc(2,function(_Ph,_){var _Pi=B(_Oz(_Pf,_w,_));return _OS;}),_Pj=__app1(E(_OT),_Pg);return new T(function(){return B(_P9(_Pd,_Pe));});};},_Pk=new T1(1,_w),_Pl=function(_Pm,_Pn,_){var _Po=function(_){var _Pp=nMV(_Pm),_Pq=_Pp;return new T(function(){var _Pr=new T(function(){return B(_Ps(_));}),_Pt=function(_){var _Pu=rMV(_Pq),_Pv=B(A2(_Pn,_Pu,_)),_=wMV(_Pq,_Pv),_Pw=function(_){var _Px=nMV(_Pk);return new T(function(){return new T1(0,B(_Pc(_Px,function(_Py){return E(_Pr);})));});};return new T1(0,_Pw);},_Pz=new T(function(){return new T1(0,_Pt);}),_Ps=function(_PA){return E(_Pz);};return B(_Ps(_));});};return new F(function(){return _Oz(new T1(0,_Po),_w,_);});},_PB=new T(function(){return eval("__strict(setBounds)");}),_PC=function(_){var _PD=__app3(E(_20),E(_93),E(_id),E(_1Z)),_PE=__app2(E(_PB),E(_1u),E(_1n));return new F(function(){return _Pl(_AR,_O6,_);});},_PF=function(_){return new F(function(){return _PC(_);});};
var hasteMain = function() {B(A(_PF, [0]));};window.onload = hasteMain;