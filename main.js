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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(","));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("Math.pow("));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr(")"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=function(_G,_H){return new T1(1,new T2(1,_B,new T2(1,_G,new T2(1,_z,new T2(1,_H,_E)))));},_I=new T(function(){return B(unCStr("Math.acos("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_E)));},_M=new T(function(){return B(unCStr("Math.acosh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_E)));},_Q=new T(function(){return B(unCStr("Math.asin("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_E)));},_U=new T(function(){return B(unCStr("Math.asinh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_E)));},_Y=new T(function(){return B(unCStr("Math.atan("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_E)));},_12=new T(function(){return B(unCStr("Math.atanh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_E)));},_16=new T(function(){return B(unCStr("Math.cos("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_E)));},_1a=new T(function(){return B(unCStr("Math.cosh("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_E)));},_1e=new T(function(){return B(unCStr("Math.exp("));}),_1f=new T1(0,_1e),_1g=function(_1h){return new T1(1,new T2(1,_1f,new T2(1,_1h,_E)));},_1i=new T(function(){return B(unCStr("Math.log("));}),_1j=new T1(0,_1i),_1k=function(_1l){return new T1(1,new T2(1,_1j,new T2(1,_1l,_E)));},_1m=new T(function(){return B(unCStr(")/Math.log("));}),_1n=new T1(0,_1m),_1o=function(_1p,_1q){return new T1(1,new T2(1,_1j,new T2(1,_1q,new T2(1,_1n,new T2(1,_1p,_E)))));},_1r=new T(function(){return B(unCStr("Math.PI"));}),_1s=new T1(0,_1r),_1t=new T(function(){return B(unCStr("Math.sin("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_E)));},_1x=new T(function(){return B(unCStr("Math.sinh("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_E)));},_1B=new T(function(){return B(unCStr("Math.sqrt("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_E)));},_1F=new T(function(){return B(unCStr("Math.tan("));}),_1G=new T1(0,_1F),_1H=function(_1I){return new T1(1,new T2(1,_1G,new T2(1,_1I,_E)));},_1J=new T(function(){return B(unCStr("Math.tanh("));}),_1K=new T1(0,_1J),_1L=function(_1M){return new T1(1,new T2(1,_1K,new T2(1,_1M,_E)));},_1N=new T(function(){return B(unCStr("("));}),_1O=new T1(0,_1N),_1P=new T(function(){return B(unCStr(")/("));}),_1Q=new T1(0,_1P),_1R=function(_1S,_1T){return new T1(1,new T2(1,_1O,new T2(1,_1S,new T2(1,_1Q,new T2(1,_1T,_E)))));},_1U=new T1(0,1),_1V=function(_1W,_1X){var _1Y=E(_1W);if(!_1Y._){var _1Z=_1Y.a,_20=E(_1X);if(!_20._){var _21=_20.a;return (_1Z!=_21)?(_1Z>_21)?2:0:1;}else{var _22=I_compareInt(_20.a,_1Z);return (_22<=0)?(_22>=0)?1:2:0;}}else{var _23=_1Y.a,_24=E(_1X);if(!_24._){var _25=I_compareInt(_23,_24.a);return (_25>=0)?(_25<=0)?1:2:0;}else{var _26=I_compare(_23,_24.a);return (_26>=0)?(_26<=0)?1:2:0;}}},_27=new T(function(){return B(unCStr("base"));}),_28=new T(function(){return B(unCStr("GHC.Exception"));}),_29=new T(function(){return B(unCStr("ArithException"));}),_2a=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_27,_28,_29),_2b=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2a,_w,_w),_2c=function(_2d){return E(_2b);},_2e=function(_2f){return E(E(_2f).a);},_2g=function(_2h,_2i,_2j){var _2k=B(A1(_2h,_)),_2l=B(A1(_2i,_)),_2m=hs_eqWord64(_2k.a,_2l.a);if(!_2m){return __Z;}else{var _2n=hs_eqWord64(_2k.b,_2l.b);return (!_2n)?__Z:new T1(1,_2j);}},_2o=function(_2p){var _2q=E(_2p);return new F(function(){return _2g(B(_2e(_2q.a)),_2c,_2q.b);});},_2r=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2s=new T(function(){return B(unCStr("denormal"));}),_2t=new T(function(){return B(unCStr("divide by zero"));}),_2u=new T(function(){return B(unCStr("loss of precision"));}),_2v=new T(function(){return B(unCStr("arithmetic underflow"));}),_2w=new T(function(){return B(unCStr("arithmetic overflow"));}),_2x=function(_2y,_2z){switch(E(_2y)){case 0:return new F(function(){return _n(_2w,_2z);});break;case 1:return new F(function(){return _n(_2v,_2z);});break;case 2:return new F(function(){return _n(_2u,_2z);});break;case 3:return new F(function(){return _n(_2t,_2z);});break;case 4:return new F(function(){return _n(_2s,_2z);});break;default:return new F(function(){return _n(_2r,_2z);});}},_2A=function(_2B){return new F(function(){return _2x(_2B,_w);});},_2C=function(_2D,_2E,_2F){return new F(function(){return _2x(_2E,_2F);});},_2G=44,_2H=93,_2I=91,_2J=function(_2K,_2L,_2M){var _2N=E(_2L);if(!_2N._){return new F(function(){return unAppCStr("[]",_2M);});}else{var _2O=new T(function(){var _2P=new T(function(){var _2Q=function(_2R){var _2S=E(_2R);if(!_2S._){return E(new T2(1,_2H,_2M));}else{var _2T=new T(function(){return B(A2(_2K,_2S.a,new T(function(){return B(_2Q(_2S.b));})));});return new T2(1,_2G,_2T);}};return B(_2Q(_2N.b));});return B(A2(_2K,_2N.a,_2P));});return new T2(1,_2I,_2O);}},_2U=function(_2V,_2W){return new F(function(){return _2J(_2x,_2V,_2W);});},_2X=new T3(0,_2C,_2A,_2U),_2Y=new T(function(){return new T5(0,_2c,_2X,_2Z,_2o,_2A);}),_2Z=function(_30){return new T2(0,_2Y,_30);},_31=3,_32=new T(function(){return B(_2Z(_31));}),_33=new T(function(){return die(_32);}),_34=function(_35,_36){var _37=E(_35);return (_37._==0)?_37.a*Math.pow(2,_36):I_toNumber(_37.a)*Math.pow(2,_36);},_38=function(_39,_3a){var _3b=E(_39);if(!_3b._){var _3c=_3b.a,_3d=E(_3a);return (_3d._==0)?_3c==_3d.a:(I_compareInt(_3d.a,_3c)==0)?true:false;}else{var _3e=_3b.a,_3f=E(_3a);return (_3f._==0)?(I_compareInt(_3e,_3f.a)==0)?true:false:(I_compare(_3e,_3f.a)==0)?true:false;}},_3g=function(_3h){var _3i=E(_3h);if(!_3i._){return E(_3i.a);}else{return new F(function(){return I_toInt(_3i.a);});}},_3j=function(_3k,_3l){while(1){var _3m=E(_3k);if(!_3m._){var _3n=_3m.a,_3o=E(_3l);if(!_3o._){var _3p=_3o.a,_3q=addC(_3n,_3p);if(!E(_3q.b)){return new T1(0,_3q.a);}else{_3k=new T1(1,I_fromInt(_3n));_3l=new T1(1,I_fromInt(_3p));continue;}}else{_3k=new T1(1,I_fromInt(_3n));_3l=_3o;continue;}}else{var _3r=E(_3l);if(!_3r._){_3k=_3m;_3l=new T1(1,I_fromInt(_3r.a));continue;}else{return new T1(1,I_add(_3m.a,_3r.a));}}}},_3s=function(_3t,_3u){while(1){var _3v=E(_3t);if(!_3v._){var _3w=E(_3v.a);if(_3w==(-2147483648)){_3t=new T1(1,I_fromInt(-2147483648));continue;}else{var _3x=E(_3u);if(!_3x._){var _3y=_3x.a;return new T2(0,new T1(0,quot(_3w,_3y)),new T1(0,_3w%_3y));}else{_3t=new T1(1,I_fromInt(_3w));_3u=_3x;continue;}}}else{var _3z=E(_3u);if(!_3z._){_3t=_3v;_3u=new T1(1,I_fromInt(_3z.a));continue;}else{var _3A=I_quotRem(_3v.a,_3z.a);return new T2(0,new T1(1,_3A.a),new T1(1,_3A.b));}}}},_3B=new T1(0,0),_3C=function(_3D,_3E){while(1){var _3F=E(_3D);if(!_3F._){_3D=new T1(1,I_fromInt(_3F.a));continue;}else{return new T1(1,I_shiftLeft(_3F.a,_3E));}}},_3G=function(_3H,_3I,_3J){if(!B(_38(_3J,_3B))){var _3K=B(_3s(_3I,_3J)),_3L=_3K.a;switch(B(_1V(B(_3C(_3K.b,1)),_3J))){case 0:return new F(function(){return _34(_3L,_3H);});break;case 1:if(!(B(_3g(_3L))&1)){return new F(function(){return _34(_3L,_3H);});}else{return new F(function(){return _34(B(_3j(_3L,_1U)),_3H);});}break;default:return new F(function(){return _34(B(_3j(_3L,_1U)),_3H);});}}else{return E(_33);}},_3M=function(_3N,_3O){var _3P=E(_3N);if(!_3P._){var _3Q=_3P.a,_3R=E(_3O);return (_3R._==0)?_3Q>_3R.a:I_compareInt(_3R.a,_3Q)<0;}else{var _3S=_3P.a,_3T=E(_3O);return (_3T._==0)?I_compareInt(_3S,_3T.a)>0:I_compare(_3S,_3T.a)>0;}},_3U=new T1(0,1),_3V=function(_3W,_3X){var _3Y=E(_3W);if(!_3Y._){var _3Z=_3Y.a,_40=E(_3X);return (_40._==0)?_3Z<_40.a:I_compareInt(_40.a,_3Z)>0;}else{var _41=_3Y.a,_42=E(_3X);return (_42._==0)?I_compareInt(_41,_42.a)<0:I_compare(_41,_42.a)<0;}},_43=new T(function(){return B(unCStr("base"));}),_44=new T(function(){return B(unCStr("Control.Exception.Base"));}),_45=new T(function(){return B(unCStr("PatternMatchFail"));}),_46=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_43,_44,_45),_47=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_46,_w,_w),_48=function(_49){return E(_47);},_4a=function(_4b){var _4c=E(_4b);return new F(function(){return _2g(B(_2e(_4c.a)),_48,_4c.b);});},_4d=function(_4e){return E(E(_4e).a);},_4f=function(_4g){return new T2(0,_4h,_4g);},_4i=function(_4j,_4k){return new F(function(){return _n(E(_4j).a,_4k);});},_4l=function(_4m,_4n){return new F(function(){return _2J(_4i,_4m,_4n);});},_4o=function(_4p,_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=new T3(0,_4o,_4d,_4l),_4h=new T(function(){return new T5(0,_48,_4s,_4f,_4a,_4d);}),_4t=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4u=function(_4v){return E(E(_4v).c);},_4w=function(_4x,_4y){return new F(function(){return die(new T(function(){return B(A2(_4u,_4y,_4x));}));});},_4z=function(_4A,_30){return new F(function(){return _4w(_4A,_30);});},_4B=function(_4C,_4D){var _4E=E(_4D);if(!_4E._){return new T2(0,_w,_w);}else{var _4F=_4E.a;if(!B(A1(_4C,_4F))){return new T2(0,_w,_4E);}else{var _4G=new T(function(){var _4H=B(_4B(_4C,_4E.b));return new T2(0,_4H.a,_4H.b);});return new T2(0,new T2(1,_4F,new T(function(){return E(E(_4G).a);})),new T(function(){return E(E(_4G).b);}));}}},_4I=32,_4J=new T(function(){return B(unCStr("\n"));}),_4K=function(_4L){return (E(_4L)==124)?false:true;},_4M=function(_4N,_4O){var _4P=B(_4B(_4K,B(unCStr(_4N)))),_4Q=_4P.a,_4R=function(_4S,_4T){var _4U=new T(function(){var _4V=new T(function(){return B(_n(_4O,new T(function(){return B(_n(_4T,_4J));},1)));});return B(unAppCStr(": ",_4V));},1);return new F(function(){return _n(_4S,_4U);});},_4W=E(_4P.b);if(!_4W._){return new F(function(){return _4R(_4Q,_w);});}else{if(E(_4W.a)==124){return new F(function(){return _4R(_4Q,new T2(1,_4I,_4W.b));});}else{return new F(function(){return _4R(_4Q,_w);});}}},_4X=function(_4Y){return new F(function(){return _4z(new T1(0,new T(function(){return B(_4M(_4Y,_4t));})),_4h);});},_4Z=function(_50){var _51=function(_52,_53){while(1){if(!B(_3V(_52,_50))){if(!B(_3M(_52,_50))){if(!B(_38(_52,_50))){return new F(function(){return _4X("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_53);}}else{return _53-1|0;}}else{var _54=B(_3C(_52,1)),_55=_53+1|0;_52=_54;_53=_55;continue;}}};return new F(function(){return _51(_3U,0);});},_56=function(_57){var _58=E(_57);if(!_58._){var _59=_58.a>>>0;if(!_59){return -1;}else{var _5a=function(_5b,_5c){while(1){if(_5b>=_59){if(_5b<=_59){if(_5b!=_59){return new F(function(){return _4X("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5c);}}else{return _5c-1|0;}}else{var _5d=imul(_5b,2)>>>0,_5e=_5c+1|0;_5b=_5d;_5c=_5e;continue;}}};return new F(function(){return _5a(1,0);});}}else{return new F(function(){return _4Z(_58);});}},_5f=function(_5g){var _5h=E(_5g);if(!_5h._){var _5i=_5h.a>>>0;if(!_5i){return new T2(0,-1,0);}else{var _5j=function(_5k,_5l){while(1){if(_5k>=_5i){if(_5k<=_5i){if(_5k!=_5i){return new F(function(){return _4X("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5l);}}else{return _5l-1|0;}}else{var _5m=imul(_5k,2)>>>0,_5n=_5l+1|0;_5k=_5m;_5l=_5n;continue;}}};return new T2(0,B(_5j(1,0)),(_5i&_5i-1>>>0)>>>0&4294967295);}}else{var _5o=_5h.a;return new T2(0,B(_56(_5h)),I_compareInt(I_and(_5o,I_sub(_5o,I_fromInt(1))),0));}},_5p=function(_5q,_5r){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);return (_5u._==0)?_5t<=_5u.a:I_compareInt(_5u.a,_5t)>=0;}else{var _5v=_5s.a,_5w=E(_5r);return (_5w._==0)?I_compareInt(_5v,_5w.a)<=0:I_compare(_5v,_5w.a)<=0;}},_5x=function(_5y,_5z){while(1){var _5A=E(_5y);if(!_5A._){var _5B=_5A.a,_5C=E(_5z);if(!_5C._){return new T1(0,(_5B>>>0&_5C.a>>>0)>>>0&4294967295);}else{_5y=new T1(1,I_fromInt(_5B));_5z=_5C;continue;}}else{var _5D=E(_5z);if(!_5D._){_5y=_5A;_5z=new T1(1,I_fromInt(_5D.a));continue;}else{return new T1(1,I_and(_5A.a,_5D.a));}}}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){var _5K=_5J.a,_5L=subC(_5I,_5K);if(!E(_5L.b)){return new T1(0,_5L.a);}else{_5F=new T1(1,I_fromInt(_5I));_5G=new T1(1,I_fromInt(_5K));continue;}}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5M=E(_5G);if(!_5M._){_5F=_5H;_5G=new T1(1,I_fromInt(_5M.a));continue;}else{return new T1(1,I_sub(_5H.a,_5M.a));}}}},_5N=new T1(0,2),_5O=function(_5P,_5Q){var _5R=E(_5P);if(!_5R._){var _5S=(_5R.a>>>0&(2<<_5Q>>>0)-1>>>0)>>>0,_5T=1<<_5Q>>>0;return (_5T<=_5S)?(_5T>=_5S)?1:2:0;}else{var _5U=B(_5x(_5R,B(_5E(B(_3C(_5N,_5Q)),_3U)))),_5V=B(_3C(_3U,_5Q));return (!B(_3M(_5V,_5U)))?(!B(_3V(_5V,_5U)))?1:2:0;}},_5W=function(_5X,_5Y){while(1){var _5Z=E(_5X);if(!_5Z._){_5X=new T1(1,I_fromInt(_5Z.a));continue;}else{return new T1(1,I_shiftRight(_5Z.a,_5Y));}}},_60=function(_61,_62,_63,_64){var _65=B(_5f(_64)),_66=_65.a;if(!E(_65.b)){var _67=B(_56(_63));if(_67<((_66+_61|0)-1|0)){var _68=_66+(_61-_62|0)|0;if(_68>0){if(_68>_67){if(_68<=(_67+1|0)){if(!E(B(_5f(_63)).b)){return 0;}else{return new F(function(){return _34(_1U,_61-_62|0);});}}else{return 0;}}else{var _69=B(_5W(_63,_68));switch(B(_5O(_63,_68-1|0))){case 0:return new F(function(){return _34(_69,_61-_62|0);});break;case 1:if(!(B(_3g(_69))&1)){return new F(function(){return _34(_69,_61-_62|0);});}else{return new F(function(){return _34(B(_3j(_69,_1U)),_61-_62|0);});}break;default:return new F(function(){return _34(B(_3j(_69,_1U)),_61-_62|0);});}}}else{return new F(function(){return _34(_63,(_61-_62|0)-_68|0);});}}else{if(_67>=_62){var _6a=B(_5W(_63,(_67+1|0)-_62|0));switch(B(_5O(_63,_67-_62|0))){case 0:return new F(function(){return _34(_6a,((_67-_66|0)+1|0)-_62|0);});break;case 2:return new F(function(){return _34(B(_3j(_6a,_1U)),((_67-_66|0)+1|0)-_62|0);});break;default:if(!(B(_3g(_6a))&1)){return new F(function(){return _34(_6a,((_67-_66|0)+1|0)-_62|0);});}else{return new F(function(){return _34(B(_3j(_6a,_1U)),((_67-_66|0)+1|0)-_62|0);});}}}else{return new F(function(){return _34(_63, -_66);});}}}else{var _6b=B(_56(_63))-_66|0,_6c=function(_6d){var _6e=function(_6f,_6g){if(!B(_5p(B(_3C(_6g,_62)),_6f))){return new F(function(){return _3G(_6d-_62|0,_6f,_6g);});}else{return new F(function(){return _3G((_6d-_62|0)+1|0,_6f,B(_3C(_6g,1)));});}};if(_6d>=_62){if(_6d!=_62){return new F(function(){return _6e(_63,new T(function(){return B(_3C(_64,_6d-_62|0));}));});}else{return new F(function(){return _6e(_63,_64);});}}else{return new F(function(){return _6e(new T(function(){return B(_3C(_63,_62-_6d|0));}),_64);});}};if(_61>_6b){return new F(function(){return _6c(_61);});}else{return new F(function(){return _6c(_6b);});}}},_6h=new T1(0,2147483647),_6i=new T(function(){return B(_3j(_6h,_3U));}),_6j=function(_6k){var _6l=E(_6k);if(!_6l._){var _6m=E(_6l.a);return (_6m==(-2147483648))?E(_6i):new T1(0, -_6m);}else{return new T1(1,I_negate(_6l.a));}},_6n=new T(function(){return 0/0;}),_6o=new T(function(){return -1/0;}),_6p=new T(function(){return 1/0;}),_6q=0,_6r=function(_6s,_6t){if(!B(_38(_6t,_3B))){if(!B(_38(_6s,_3B))){if(!B(_3V(_6s,_3B))){return new F(function(){return _60(-1021,53,_6s,_6t);});}else{return  -B(_60(-1021,53,B(_6j(_6s)),_6t));}}else{return E(_6q);}}else{return (!B(_38(_6s,_3B)))?(!B(_3V(_6s,_3B)))?E(_6p):E(_6o):E(_6n);}},_6u=function(_6v){return new T1(0,new T(function(){var _6w=E(_6v),_6x=jsShow(B(_6r(_6w.a,_6w.b)));return fromJSStr(_6x);}));},_6y=new T(function(){return B(unCStr("1/("));}),_6z=new T1(0,_6y),_6A=function(_6B){return new T1(1,new T2(1,_6z,new T2(1,_6B,_E)));},_6C=new T(function(){return B(unCStr(")+("));}),_6D=new T1(0,_6C),_6E=function(_6F,_6G){return new T1(1,new T2(1,_1O,new T2(1,_6F,new T2(1,_6D,new T2(1,_6G,_E)))));},_6H=new T(function(){return B(unCStr("-("));}),_6I=new T1(0,_6H),_6J=function(_6K){return new T1(1,new T2(1,_6I,new T2(1,_6K,_E)));},_6L=new T(function(){return B(unCStr(")*("));}),_6M=new T1(0,_6L),_6N=function(_6O,_6P){return new T1(1,new T2(1,_1O,new T2(1,_6O,new T2(1,_6M,new T2(1,_6P,_E)))));},_6Q=function(_6R){return E(E(_6R).a);},_6S=function(_6T){return E(E(_6T).d);},_6U=function(_6V,_6W){return new F(function(){return A3(_6Q,_6X,_6V,new T(function(){return B(A2(_6S,_6X,_6W));}));});},_6Y=new T(function(){return B(unCStr("Math.abs("));}),_6Z=new T1(0,_6Y),_70=function(_71){return new T1(1,new T2(1,_6Z,new T2(1,_71,_E)));},_72=function(_73){while(1){var _74=E(_73);if(!_74._){_73=new T1(1,I_fromInt(_74.a));continue;}else{return new F(function(){return I_toString(_74.a);});}}},_75=function(_76,_77){return new F(function(){return _n(fromJSStr(B(_72(_76))),_77);});},_78=41,_79=40,_7a=new T1(0,0),_7b=function(_7c,_7d,_7e){if(_7c<=6){return new F(function(){return _75(_7d,_7e);});}else{if(!B(_3V(_7d,_7a))){return new F(function(){return _75(_7d,_7e);});}else{return new T2(1,_79,new T(function(){return B(_n(fromJSStr(B(_72(_7d))),new T2(1,_78,_7e)));}));}}},_7f=new T(function(){return B(unCStr("."));}),_7g=function(_7h){return new T1(0,new T(function(){return B(_n(B(_7b(0,_7h,_w)),_7f));}));},_7i=new T(function(){return B(unCStr("Math.sign("));}),_7j=new T1(0,_7i),_7k=function(_7l){return new T1(1,new T2(1,_7j,new T2(1,_7l,_E)));},_6X=new T(function(){return {_:0,a:_6E,b:_6U,c:_6N,d:_6J,e:_70,f:_7k,g:_7g};}),_7m=new T4(0,_6X,_1R,_6A,_6u),_7n={_:0,a:_7m,b:_1s,c:_1g,d:_1k,e:_1D,f:_F,g:_1o,h:_1v,i:_18,j:_1H,k:_S,l:_K,m:_10,n:_1z,o:_1c,p:_1L,q:_W,r:_O,s:_14},_7o=function(_7p,_7q){var _7r=E(_7p);return E(_7q);},_7s=function(_7t,_7u){var _7v=E(_7u);return E(_7t);},_7w=function(_7x,_7y){var _7z=E(_7x),_7A=E(_7y);return new T3(0,E(B(A1(_7z.a,_7A.a))),E(B(A1(_7z.b,_7A.b))),E(B(A1(_7z.c,_7A.c))));},_7B=function(_7C,_7D,_7E){return new T3(0,E(_7C),E(_7D),E(_7E));},_7F=function(_7G){return new F(function(){return _7B(_7G,_7G,_7G);});},_7H=function(_7I,_7J){var _7K=E(_7J),_7L=E(_7I);return new T3(0,E(_7L),E(_7L),E(_7L));},_7M=function(_7N,_7O){var _7P=E(_7O);return new T3(0,E(B(A1(_7N,_7P.a))),E(B(A1(_7N,_7P.b))),E(B(A1(_7N,_7P.c))));},_7Q=new T2(0,_7M,_7H),_7R=new T5(0,_7Q,_7F,_7w,_7o,_7s),_7S=new T1(0,0),_7T=new T1(0,1),_7U=function(_7V){return E(E(_7V).g);},_7W=function(_7X){var _7Y=B(A2(_7U,_7X,_7T)),_7Z=B(A2(_7U,_7X,_7S));return new T3(0,E(new T3(0,E(_7Y),E(_7Z),E(_7Z))),E(new T3(0,E(_7Z),E(_7Y),E(_7Z))),E(new T3(0,E(_7Z),E(_7Z),E(_7Y))));},_80=function(_81){return E(E(_81).a);},_82=function(_83){return E(E(_83).a);},_84=function(_85){return E(E(_85).a);},_86=function(_87){return E(E(_87).a);},_88=function(_89,_8a,_8b){var _8c=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_89).c).a);})));})));}),_8d=new T(function(){return B(A3(_86,B(_84(E(_89).a)),new T(function(){return B(_6S(_8c));}),_8b));});return new T2(0,new T(function(){return B(A2(_6S,_8c,_8a));}),_8d);},_8e=function(_8f){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_8f));}))));});},_8g=new T(function(){return B(_8e("ww_s4CO Ord a"));}),_8h=function(_8i,_8j,_8k,_8l){var _8m=new T(function(){return B(_82(new T(function(){return B(_80(_8i));})));}),_8n=B(A2(_7U,_8m,_7S));return E(B(_88(new T3(0,_7R,_7W,new T2(0,_8i,_8g)),_8k,new T3(0,E(_8n),E(B(A2(_7U,_8m,_7T))),E(_8n)))).b);},_8o=new T(function(){return B(unCStr("x"));}),_8p=new T1(0,_8o),_8q=new T(function(){return B(unCStr("y"));}),_8r=new T1(0,_8q),_8s=new T(function(){return B(unCStr("z"));}),_8t=new T1(0,_8s),_8u=new T(function(){return B(_8h(_7n,_8p,_8r,_8t));}),_8v=new T(function(){return E(E(_8u).a);}),_8w=new T(function(){return B(unCStr(",y:"));}),_8x=new T1(0,_8w),_8y=new T(function(){return E(E(_8u).b);}),_8z=new T(function(){return B(unCStr(",z:"));}),_8A=new T1(0,_8z),_8B=new T(function(){return E(E(_8u).c);}),_8C=new T(function(){return B(unCStr("})"));}),_8D=new T1(0,_8C),_8E=new T2(1,_8D,_w),_8F=new T2(1,_8B,_8E),_8G=new T2(1,_8A,_8F),_8H=new T2(1,_8y,_8G),_8I=new T2(1,_8x,_8H),_8J=new T2(1,_8v,_8I),_8K=new T(function(){return B(unCStr("({x:"));}),_8L=new T1(0,_8K),_8M=new T2(1,_8L,_8J),_8N=function(_8O){return E(_8O);},_8P=new T(function(){return toJSStr(B(_e(_x,_8N,_8M)));}),_8Q=new T2(1,_8r,_E),_8R=new T2(1,_6I,_8Q),_8S=new T(function(){return toJSStr(B(_e(_x,_8N,_8R)));}),_8T=function(_8U,_8V,_8W){var _8X=E(_8W);if(!_8X._){return new F(function(){return A1(_8V,_8X.a);});}else{var _8Y=new T(function(){return B(_0(_8U));}),_8Z=new T(function(){return B(_2(_8U));}),_90=function(_91){var _92=E(_91);if(!_92._){return E(_8Z);}else{return new F(function(){return A2(_8Y,new T(function(){return B(_8T(_8U,_8V,_92.a));}),new T(function(){return B(_90(_92.b));}));});}};return new F(function(){return _90(_8X.a);});}},_93=function(_94,_95,_96){var _97=new T(function(){return B(_0(_94));}),_98=new T(function(){return B(_2(_94));}),_99=function(_9a){var _9b=E(_9a);if(!_9b._){return E(_98);}else{return new F(function(){return A2(_97,new T(function(){return B(_8T(_94,_95,_9b.a));}),new T(function(){return B(_99(_9b.b));}));});}};return new F(function(){return _99(_96);});},_9c=new T(function(){return B(unCStr("-("));}),_9d=new T1(0,_9c),_9e=new T(function(){return B(unCStr(")"));}),_9f=new T1(0,_9e),_9g=new T2(1,_9f,_w),_9h=new T(function(){return B(unCStr("y"));}),_9i=new T1(0,_9h),_9j=new T2(1,_9i,_9g),_9k=new T2(1,_9d,_9j),_9l=new T(function(){return toJSStr(B(_93(_x,_8N,_9k)));}),_9m=new T(function(){return eval("__strict(compile)");}),_9n=new T(function(){return B(unCStr(","));}),_9o=new T1(0,_9n),_9p=new T(function(){return B(unCStr("pow("));}),_9q=new T1(0,_9p),_9r=function(_9s,_9t){return new T1(1,new T2(1,_9q,new T2(1,_9s,new T2(1,_9o,new T2(1,_9t,_9g)))));},_9u=new T(function(){return B(unCStr("acos("));}),_9v=new T1(0,_9u),_9w=function(_9x){return new T1(1,new T2(1,_9v,new T2(1,_9x,_9g)));},_9y=new T(function(){return B(unCStr("acosh("));}),_9z=new T1(0,_9y),_9A=function(_9B){return new T1(1,new T2(1,_9z,new T2(1,_9B,_9g)));},_9C=new T(function(){return B(unCStr("asin("));}),_9D=new T1(0,_9C),_9E=function(_9F){return new T1(1,new T2(1,_9D,new T2(1,_9F,_9g)));},_9G=new T(function(){return B(unCStr("asinh("));}),_9H=new T1(0,_9G),_9I=function(_9J){return new T1(1,new T2(1,_9H,new T2(1,_9J,_9g)));},_9K=new T(function(){return B(unCStr("atan("));}),_9L=new T1(0,_9K),_9M=function(_9N){return new T1(1,new T2(1,_9L,new T2(1,_9N,_9g)));},_9O=new T(function(){return B(unCStr("atanh("));}),_9P=new T1(0,_9O),_9Q=function(_9R){return new T1(1,new T2(1,_9P,new T2(1,_9R,_9g)));},_9S=new T(function(){return B(unCStr("cos("));}),_9T=new T1(0,_9S),_9U=function(_9V){return new T1(1,new T2(1,_9T,new T2(1,_9V,_9g)));},_9W=new T(function(){return B(unCStr("cosh("));}),_9X=new T1(0,_9W),_9Y=function(_9Z){return new T1(1,new T2(1,_9X,new T2(1,_9Z,_9g)));},_a0=new T(function(){return B(unCStr("exp("));}),_a1=new T1(0,_a0),_a2=function(_a3){return new T1(1,new T2(1,_a1,new T2(1,_a3,_9g)));},_a4=new T(function(){return B(unCStr("log("));}),_a5=new T1(0,_a4),_a6=function(_a7){return new T1(1,new T2(1,_a5,new T2(1,_a7,_9g)));},_a8=new T(function(){return B(unCStr(")/log("));}),_a9=new T1(0,_a8),_aa=function(_ab,_ac){return new T1(1,new T2(1,_a5,new T2(1,_ac,new T2(1,_a9,new T2(1,_ab,_9g)))));},_ad=new T(function(){return B(unCStr("pi"));}),_ae=new T1(0,_ad),_af=new T(function(){return B(unCStr("sin("));}),_ag=new T1(0,_af),_ah=function(_ai){return new T1(1,new T2(1,_ag,new T2(1,_ai,_9g)));},_aj=new T(function(){return B(unCStr("sinh("));}),_ak=new T1(0,_aj),_al=function(_am){return new T1(1,new T2(1,_ak,new T2(1,_am,_9g)));},_an=new T(function(){return B(unCStr("sqrt("));}),_ao=new T1(0,_an),_ap=function(_aq){return new T1(1,new T2(1,_ao,new T2(1,_aq,_9g)));},_ar=new T(function(){return B(unCStr("tan("));}),_as=new T1(0,_ar),_at=function(_au){return new T1(1,new T2(1,_as,new T2(1,_au,_9g)));},_av=new T(function(){return B(unCStr("tanh("));}),_aw=new T1(0,_av),_ax=function(_ay){return new T1(1,new T2(1,_aw,new T2(1,_ay,_9g)));},_az=new T(function(){return B(unCStr("("));}),_aA=new T1(0,_az),_aB=new T(function(){return B(unCStr(")/("));}),_aC=new T1(0,_aB),_aD=function(_aE,_aF){return new T1(1,new T2(1,_aA,new T2(1,_aE,new T2(1,_aC,new T2(1,_aF,_9g)))));},_aG=function(_aH){return new T1(0,new T(function(){var _aI=E(_aH),_aJ=jsShow(B(_6r(_aI.a,_aI.b)));return fromJSStr(_aJ);}));},_aK=new T(function(){return B(unCStr("1./("));}),_aL=new T1(0,_aK),_aM=function(_aN){return new T1(1,new T2(1,_aL,new T2(1,_aN,_9g)));},_aO=new T(function(){return B(unCStr(")+("));}),_aP=new T1(0,_aO),_aQ=function(_aR,_aS){return new T1(1,new T2(1,_aA,new T2(1,_aR,new T2(1,_aP,new T2(1,_aS,_9g)))));},_aT=function(_aU){return new T1(1,new T2(1,_9d,new T2(1,_aU,_9g)));},_aV=new T(function(){return B(unCStr(")*("));}),_aW=new T1(0,_aV),_aX=function(_aY,_aZ){return new T1(1,new T2(1,_aA,new T2(1,_aY,new T2(1,_aW,new T2(1,_aZ,_9g)))));},_b0=function(_b1,_b2){return new F(function(){return A3(_6Q,_b3,_b1,new T(function(){return B(A2(_6S,_b3,_b2));}));});},_b4=new T(function(){return B(unCStr("abs("));}),_b5=new T1(0,_b4),_b6=function(_b7){return new T1(1,new T2(1,_b5,new T2(1,_b7,_9g)));},_b8=new T(function(){return B(unCStr("."));}),_b9=function(_ba){return new T1(0,new T(function(){return B(_n(B(_7b(0,_ba,_w)),_b8));}));},_bb=new T(function(){return B(unCStr("sign("));}),_bc=new T1(0,_bb),_bd=function(_be){return new T1(1,new T2(1,_bc,new T2(1,_be,_9g)));},_b3=new T(function(){return {_:0,a:_aQ,b:_b0,c:_aX,d:_aT,e:_b6,f:_bd,g:_b9};}),_bf=new T4(0,_b3,_aD,_aM,_aG),_bg={_:0,a:_bf,b:_ae,c:_a2,d:_a6,e:_ap,f:_9r,g:_aa,h:_ah,i:_9U,j:_at,k:_9E,l:_9w,m:_9M,n:_al,o:_9Y,p:_ax,q:_9I,r:_9A,s:_9Q},_bh=function(_bi){return E(E(_bi).c);},_bj=function(_bk,_bl,_bm,_bn,_bo,_bp,_bq){var _br=B(_82(B(_80(_bk)))),_bs=new T(function(){return B(A3(_6Q,_br,new T(function(){return B(A3(_bh,_br,_bl,_bo));}),new T(function(){return B(A3(_bh,_br,_bm,_bp));})));});return new F(function(){return A3(_6Q,_br,_bs,new T(function(){return B(A3(_bh,_br,_bn,_bq));}));});},_bt=function(_bu){return E(E(_bu).b);},_bv=function(_bw){return E(E(_bw).e);},_bx=function(_by,_bz){var _bA=B(_82(B(_80(_by)))),_bB=new T(function(){return B(A2(_bv,_by,new T(function(){var _bC=E(_bz),_bD=_bC.a,_bE=_bC.b,_bF=_bC.c;return B(_bj(_by,_bD,_bE,_bF,_bD,_bE,_bF));})));});return new F(function(){return A3(_bt,_bA,_bB,new T(function(){return B(A2(_7U,_bA,_7T));}));});},_bG=new T(function(){return B(unCStr("x"));}),_bH=new T1(0,_bG),_bI=new T(function(){return B(unCStr("z"));}),_bJ=new T1(0,_bI),_bK=new T3(0,E(_bH),E(_9i),E(_bJ)),_bL=new T(function(){return B(_bx(_bg,_bK));}),_bM=new T(function(){return toJSStr(B(_8T(_x,_8N,_bL)));}),_bN=new T(function(){return B(unCStr("(/=) is not defined"));}),_bO=new T(function(){return B(err(_bN));}),_bP=new T(function(){return B(unCStr("(==) is not defined"));}),_bQ=new T(function(){return B(err(_bP));}),_bR=new T2(0,_bQ,_bO),_bS=new T(function(){return B(unCStr("(<) is not defined"));}),_bT=new T(function(){return B(err(_bS));}),_bU=new T(function(){return B(unCStr("(<=) is not defined"));}),_bV=new T(function(){return B(err(_bU));}),_bW=new T(function(){return B(unCStr("(>) is not defined"));}),_bX=new T(function(){return B(err(_bW));}),_bY=new T(function(){return B(unCStr("(>=) is not defined"));}),_bZ=new T(function(){return B(err(_bY));}),_c0=new T(function(){return B(unCStr("compare is not defined"));}),_c1=new T(function(){return B(err(_c0));}),_c2=new T(function(){return B(unCStr("max("));}),_c3=new T1(0,_c2),_c4=function(_c5,_c6){return new T1(1,new T2(1,_c3,new T2(1,_c5,new T2(1,_9o,new T2(1,_c6,_9g)))));},_c7=new T(function(){return B(unCStr("min("));}),_c8=new T1(0,_c7),_c9=function(_ca,_cb){return new T1(1,new T2(1,_c8,new T2(1,_ca,new T2(1,_9o,new T2(1,_cb,_9g)))));},_cc={_:0,a:_bR,b:_c1,c:_bT,d:_bV,e:_bX,f:_bZ,g:_c4,h:_c9},_cd=new T2(0,_bg,_cc),_ce=function(_cf){return E(E(_cf).f);},_cg=function(_ch){return E(E(_ch).b);},_ci=function(_cj){return E(E(_cj).c);},_ck=function(_cl){return E(E(_cl).d);},_cm=function(_cn,_co,_cp,_cq,_cr){var _cs=new T(function(){return E(E(E(_cn).c).a);}),_ct=new T(function(){var _cu=E(_cn).a,_cv=new T(function(){var _cw=new T(function(){return B(_80(_cs));}),_cx=new T(function(){return B(_82(_cw));}),_cy=new T(function(){return B(A2(_ck,_cs,_co));}),_cz=new T(function(){return B(A3(_ce,_cs,_co,_cq));}),_cA=function(_cB,_cC){var _cD=new T(function(){var _cE=new T(function(){return B(A3(_cg,_cw,new T(function(){return B(A3(_bh,_cx,_cq,_cB));}),_co));});return B(A3(_6Q,_cx,_cE,new T(function(){return B(A3(_bh,_cx,_cC,_cy));})));});return new F(function(){return A3(_bh,_cx,_cz,_cD);});};return B(A3(_86,B(_84(_cu)),_cA,_cp));});return B(A3(_ci,_cu,_cv,_cr));});return new T2(0,new T(function(){return B(A3(_ce,_cs,_co,_cq));}),_ct);},_cF=function(_cG,_cH,_cI,_cJ){var _cK=E(_cI),_cL=E(_cJ),_cM=B(_cm(_cH,_cK.a,_cK.b,_cL.a,_cL.b));return new T2(0,_cM.a,_cM.b);},_cN=new T1(0,1),_cO=function(_cP){return E(E(_cP).l);},_cQ=function(_cR,_cS,_cT){var _cU=new T(function(){return E(E(E(_cR).c).a);}),_cV=new T(function(){var _cW=new T(function(){return B(_80(_cU));}),_cX=new T(function(){var _cY=B(_82(_cW)),_cZ=new T(function(){var _d0=new T(function(){return B(A3(_bt,_cY,new T(function(){return B(A2(_7U,_cY,_cN));}),new T(function(){return B(A3(_bh,_cY,_cS,_cS));})));});return B(A2(_bv,_cU,_d0));});return B(A2(_6S,_cY,_cZ));});return B(A3(_86,B(_84(E(_cR).a)),function(_d1){return new F(function(){return A3(_cg,_cW,_d1,_cX);});},_cT));});return new T2(0,new T(function(){return B(A2(_cO,_cU,_cS));}),_cV);},_d2=function(_d3,_d4,_d5){var _d6=E(_d5),_d7=B(_cQ(_d4,_d6.a,_d6.b));return new T2(0,_d7.a,_d7.b);},_d8=function(_d9){return E(E(_d9).r);},_da=function(_db,_dc,_dd){var _de=new T(function(){return E(E(E(_db).c).a);}),_df=new T(function(){var _dg=new T(function(){return B(_80(_de));}),_dh=new T(function(){var _di=new T(function(){var _dj=B(_82(_dg));return B(A3(_bt,_dj,new T(function(){return B(A3(_bh,_dj,_dc,_dc));}),new T(function(){return B(A2(_7U,_dj,_cN));})));});return B(A2(_bv,_de,_di));});return B(A3(_86,B(_84(E(_db).a)),function(_dk){return new F(function(){return A3(_cg,_dg,_dk,_dh);});},_dd));});return new T2(0,new T(function(){return B(A2(_d8,_de,_dc));}),_df);},_dl=function(_dm,_dn,_do){var _dp=E(_do),_dq=B(_da(_dn,_dp.a,_dp.b));return new T2(0,_dq.a,_dq.b);},_dr=function(_ds){return E(E(_ds).k);},_dt=function(_du,_dv,_dw){var _dx=new T(function(){return E(E(E(_du).c).a);}),_dy=new T(function(){var _dz=new T(function(){return B(_80(_dx));}),_dA=new T(function(){var _dB=new T(function(){var _dC=B(_82(_dz));return B(A3(_bt,_dC,new T(function(){return B(A2(_7U,_dC,_cN));}),new T(function(){return B(A3(_bh,_dC,_dv,_dv));})));});return B(A2(_bv,_dx,_dB));});return B(A3(_86,B(_84(E(_du).a)),function(_dD){return new F(function(){return A3(_cg,_dz,_dD,_dA);});},_dw));});return new T2(0,new T(function(){return B(A2(_dr,_dx,_dv));}),_dy);},_dE=function(_dF,_dG,_dH){var _dI=E(_dH),_dJ=B(_dt(_dG,_dI.a,_dI.b));return new T2(0,_dJ.a,_dJ.b);},_dK=function(_dL){return E(E(_dL).q);},_dM=function(_dN,_dO,_dP){var _dQ=new T(function(){return E(E(E(_dN).c).a);}),_dR=new T(function(){var _dS=new T(function(){return B(_80(_dQ));}),_dT=new T(function(){var _dU=new T(function(){var _dV=B(_82(_dS));return B(A3(_6Q,_dV,new T(function(){return B(A3(_bh,_dV,_dO,_dO));}),new T(function(){return B(A2(_7U,_dV,_cN));})));});return B(A2(_bv,_dQ,_dU));});return B(A3(_86,B(_84(E(_dN).a)),function(_dW){return new F(function(){return A3(_cg,_dS,_dW,_dT);});},_dP));});return new T2(0,new T(function(){return B(A2(_dK,_dQ,_dO));}),_dR);},_dX=function(_dY,_dZ,_e0){var _e1=E(_e0),_e2=B(_dM(_dZ,_e1.a,_e1.b));return new T2(0,_e2.a,_e2.b);},_e3=function(_e4){return E(E(_e4).m);},_e5=function(_e6,_e7,_e8){var _e9=new T(function(){return E(E(E(_e6).c).a);}),_ea=new T(function(){var _eb=new T(function(){return B(_80(_e9));}),_ec=new T(function(){var _ed=B(_82(_eb));return B(A3(_6Q,_ed,new T(function(){return B(A2(_7U,_ed,_cN));}),new T(function(){return B(A3(_bh,_ed,_e7,_e7));})));});return B(A3(_86,B(_84(E(_e6).a)),function(_ee){return new F(function(){return A3(_cg,_eb,_ee,_ec);});},_e8));});return new T2(0,new T(function(){return B(A2(_e3,_e9,_e7));}),_ea);},_ef=function(_eg,_eh,_ei){var _ej=E(_ei),_ek=B(_e5(_eh,_ej.a,_ej.b));return new T2(0,_ek.a,_ek.b);},_el=function(_em){return E(E(_em).s);},_en=function(_eo,_ep,_eq){var _er=new T(function(){return E(E(E(_eo).c).a);}),_es=new T(function(){var _et=new T(function(){return B(_80(_er));}),_eu=new T(function(){var _ev=B(_82(_et));return B(A3(_bt,_ev,new T(function(){return B(A2(_7U,_ev,_cN));}),new T(function(){return B(A3(_bh,_ev,_ep,_ep));})));});return B(A3(_86,B(_84(E(_eo).a)),function(_ew){return new F(function(){return A3(_cg,_et,_ew,_eu);});},_eq));});return new T2(0,new T(function(){return B(A2(_el,_er,_ep));}),_es);},_ex=function(_ey,_ez,_eA){var _eB=E(_eA),_eC=B(_en(_ez,_eB.a,_eB.b));return new T2(0,_eC.a,_eC.b);},_eD=function(_eE){return E(E(_eE).i);},_eF=function(_eG){return E(E(_eG).h);},_eH=function(_eI,_eJ,_eK){var _eL=new T(function(){return E(E(E(_eI).c).a);}),_eM=new T(function(){var _eN=new T(function(){return B(_82(new T(function(){return B(_80(_eL));})));}),_eO=new T(function(){return B(A2(_6S,_eN,new T(function(){return B(A2(_eF,_eL,_eJ));})));});return B(A3(_86,B(_84(E(_eI).a)),function(_eP){return new F(function(){return A3(_bh,_eN,_eP,_eO);});},_eK));});return new T2(0,new T(function(){return B(A2(_eD,_eL,_eJ));}),_eM);},_eQ=function(_eR,_eS,_eT){var _eU=E(_eT),_eV=B(_eH(_eS,_eU.a,_eU.b));return new T2(0,_eV.a,_eV.b);},_eW=function(_eX){return E(E(_eX).o);},_eY=function(_eZ){return E(E(_eZ).n);},_f0=function(_f1,_f2,_f3){var _f4=new T(function(){return E(E(E(_f1).c).a);}),_f5=new T(function(){var _f6=new T(function(){return B(_82(new T(function(){return B(_80(_f4));})));}),_f7=new T(function(){return B(A2(_eY,_f4,_f2));});return B(A3(_86,B(_84(E(_f1).a)),function(_f8){return new F(function(){return A3(_bh,_f6,_f8,_f7);});},_f3));});return new T2(0,new T(function(){return B(A2(_eW,_f4,_f2));}),_f5);},_f9=function(_fa,_fb,_fc){var _fd=E(_fc),_fe=B(_f0(_fb,_fd.a,_fd.b));return new T2(0,_fe.a,_fe.b);},_ff=function(_fg){return E(E(_fg).c);},_fh=function(_fi,_fj,_fk){var _fl=new T(function(){return E(E(E(_fi).c).a);}),_fm=new T(function(){var _fn=new T(function(){return B(_82(new T(function(){return B(_80(_fl));})));}),_fo=new T(function(){return B(A2(_ff,_fl,_fj));});return B(A3(_86,B(_84(E(_fi).a)),function(_fp){return new F(function(){return A3(_bh,_fn,_fp,_fo);});},_fk));});return new T2(0,new T(function(){return B(A2(_ff,_fl,_fj));}),_fm);},_fq=function(_fr,_fs,_ft){var _fu=E(_ft),_fv=B(_fh(_fs,_fu.a,_fu.b));return new T2(0,_fv.a,_fv.b);},_fw=function(_fx,_fy,_fz){var _fA=new T(function(){return E(E(E(_fx).c).a);}),_fB=new T(function(){var _fC=new T(function(){return B(_80(_fA));}),_fD=new T(function(){return B(_82(_fC));}),_fE=new T(function(){return B(A3(_cg,_fC,new T(function(){return B(A2(_7U,_fD,_cN));}),_fy));});return B(A3(_86,B(_84(E(_fx).a)),function(_fF){return new F(function(){return A3(_bh,_fD,_fF,_fE);});},_fz));});return new T2(0,new T(function(){return B(A2(_ck,_fA,_fy));}),_fB);},_fG=function(_fH,_fI,_fJ){var _fK=E(_fJ),_fL=B(_fw(_fI,_fK.a,_fK.b));return new T2(0,_fL.a,_fL.b);},_fM=function(_fN,_fO,_fP,_fQ){var _fR=new T(function(){return E(E(_fO).c);}),_fS=new T3(0,new T(function(){return E(E(_fO).a);}),new T(function(){return E(E(_fO).b);}),new T2(0,new T(function(){return E(E(_fR).a);}),new T(function(){return E(E(_fR).b);})));return new F(function(){return A3(_cg,_fN,new T(function(){var _fT=E(_fQ),_fU=B(_fw(_fS,_fT.a,_fT.b));return new T2(0,_fU.a,_fU.b);}),new T(function(){var _fV=E(_fP),_fW=B(_fw(_fS,_fV.a,_fV.b));return new T2(0,_fW.a,_fW.b);}));});},_fX=new T1(0,0),_fY=function(_fZ){return E(E(_fZ).b);},_g0=function(_g1){return E(E(_g1).b);},_g2=function(_g3){var _g4=new T(function(){return E(E(E(_g3).c).a);}),_g5=new T(function(){return B(A2(_g0,E(_g3).a,new T(function(){return B(A2(_7U,B(_82(B(_80(_g4)))),_fX));})));});return new T2(0,new T(function(){return B(_fY(_g4));}),_g5);},_g6=function(_g7,_g8){var _g9=B(_g2(_g8));return new T2(0,_g9.a,_g9.b);},_ga=function(_gb,_gc,_gd){var _ge=new T(function(){return E(E(E(_gb).c).a);}),_gf=new T(function(){var _gg=new T(function(){return B(_82(new T(function(){return B(_80(_ge));})));}),_gh=new T(function(){return B(A2(_eD,_ge,_gc));});return B(A3(_86,B(_84(E(_gb).a)),function(_gi){return new F(function(){return A3(_bh,_gg,_gi,_gh);});},_gd));});return new T2(0,new T(function(){return B(A2(_eF,_ge,_gc));}),_gf);},_gj=function(_gk,_gl,_gm){var _gn=E(_gm),_go=B(_ga(_gl,_gn.a,_gn.b));return new T2(0,_go.a,_go.b);},_gp=function(_gq,_gr,_gs){var _gt=new T(function(){return E(E(E(_gq).c).a);}),_gu=new T(function(){var _gv=new T(function(){return B(_82(new T(function(){return B(_80(_gt));})));}),_gw=new T(function(){return B(A2(_eW,_gt,_gr));});return B(A3(_86,B(_84(E(_gq).a)),function(_gx){return new F(function(){return A3(_bh,_gv,_gx,_gw);});},_gs));});return new T2(0,new T(function(){return B(A2(_eY,_gt,_gr));}),_gu);},_gy=function(_gz,_gA,_gB){var _gC=E(_gB),_gD=B(_gp(_gA,_gC.a,_gC.b));return new T2(0,_gD.a,_gD.b);},_gE=new T1(0,2),_gF=function(_gG,_gH,_gI){var _gJ=new T(function(){return E(E(E(_gG).c).a);}),_gK=new T(function(){var _gL=new T(function(){return B(_80(_gJ));}),_gM=new T(function(){return B(_82(_gL));}),_gN=new T(function(){var _gO=new T(function(){return B(A3(_cg,_gL,new T(function(){return B(A2(_7U,_gM,_cN));}),new T(function(){return B(A2(_7U,_gM,_gE));})));});return B(A3(_cg,_gL,_gO,new T(function(){return B(A2(_bv,_gJ,_gH));})));});return B(A3(_86,B(_84(E(_gG).a)),function(_gP){return new F(function(){return A3(_bh,_gM,_gP,_gN);});},_gI));});return new T2(0,new T(function(){return B(A2(_bv,_gJ,_gH));}),_gK);},_gQ=function(_gR,_gS,_gT){var _gU=E(_gT),_gV=B(_gF(_gS,_gU.a,_gU.b));return new T2(0,_gV.a,_gV.b);},_gW=function(_gX){return E(E(_gX).j);},_gY=function(_gZ,_h0,_h1){var _h2=new T(function(){return E(E(E(_gZ).c).a);}),_h3=new T(function(){var _h4=new T(function(){return B(_80(_h2));}),_h5=new T(function(){var _h6=new T(function(){return B(A2(_eD,_h2,_h0));});return B(A3(_bh,B(_82(_h4)),_h6,_h6));});return B(A3(_86,B(_84(E(_gZ).a)),function(_h7){return new F(function(){return A3(_cg,_h4,_h7,_h5);});},_h1));});return new T2(0,new T(function(){return B(A2(_gW,_h2,_h0));}),_h3);},_h8=function(_h9,_ha,_hb){var _hc=E(_hb),_hd=B(_gY(_ha,_hc.a,_hc.b));return new T2(0,_hd.a,_hd.b);},_he=function(_hf){return E(E(_hf).p);},_hg=function(_hh,_hi,_hj){var _hk=new T(function(){return E(E(E(_hh).c).a);}),_hl=new T(function(){var _hm=new T(function(){return B(_80(_hk));}),_hn=new T(function(){var _ho=new T(function(){return B(A2(_eW,_hk,_hi));});return B(A3(_bh,B(_82(_hm)),_ho,_ho));});return B(A3(_86,B(_84(E(_hh).a)),function(_hp){return new F(function(){return A3(_cg,_hm,_hp,_hn);});},_hj));});return new T2(0,new T(function(){return B(A2(_he,_hk,_hi));}),_hl);},_hq=function(_hr,_hs,_ht){var _hu=E(_ht),_hv=B(_hg(_hs,_hu.a,_hu.b));return new T2(0,_hv.a,_hv.b);},_hw=function(_hx,_hy){return {_:0,a:_hx,b:new T(function(){return B(_g6(_hx,_hy));}),c:function(_hz){return new F(function(){return _fq(_hx,_hy,_hz);});},d:function(_hz){return new F(function(){return _fG(_hx,_hy,_hz);});},e:function(_hz){return new F(function(){return _gQ(_hx,_hy,_hz);});},f:function(_hA,_hz){return new F(function(){return _cF(_hx,_hy,_hA,_hz);});},g:function(_hA,_hz){return new F(function(){return _fM(_hx,_hy,_hA,_hz);});},h:function(_hz){return new F(function(){return _gj(_hx,_hy,_hz);});},i:function(_hz){return new F(function(){return _eQ(_hx,_hy,_hz);});},j:function(_hz){return new F(function(){return _h8(_hx,_hy,_hz);});},k:function(_hz){return new F(function(){return _dE(_hx,_hy,_hz);});},l:function(_hz){return new F(function(){return _d2(_hx,_hy,_hz);});},m:function(_hz){return new F(function(){return _ef(_hx,_hy,_hz);});},n:function(_hz){return new F(function(){return _gy(_hx,_hy,_hz);});},o:function(_hz){return new F(function(){return _f9(_hx,_hy,_hz);});},p:function(_hz){return new F(function(){return _hq(_hx,_hy,_hz);});},q:function(_hz){return new F(function(){return _dX(_hx,_hy,_hz);});},r:function(_hz){return new F(function(){return _dl(_hx,_hy,_hz);});},s:function(_hz){return new F(function(){return _ex(_hx,_hy,_hz);});}};},_hB=function(_hC,_hD,_hE,_hF,_hG){var _hH=new T(function(){return B(_80(new T(function(){return E(E(E(_hC).c).a);})));}),_hI=new T(function(){var _hJ=E(_hC).a,_hK=new T(function(){var _hL=new T(function(){return B(_82(_hH));}),_hM=new T(function(){return B(A3(_bh,_hL,_hF,_hF));}),_hN=function(_hO,_hP){var _hQ=new T(function(){return B(A3(_bt,_hL,new T(function(){return B(A3(_bh,_hL,_hO,_hF));}),new T(function(){return B(A3(_bh,_hL,_hD,_hP));})));});return new F(function(){return A3(_cg,_hH,_hQ,_hM);});};return B(A3(_86,B(_84(_hJ)),_hN,_hE));});return B(A3(_ci,_hJ,_hK,_hG));});return new T2(0,new T(function(){return B(A3(_cg,_hH,_hD,_hF));}),_hI);},_hR=function(_hS,_hT,_hU,_hV){var _hW=E(_hU),_hX=E(_hV),_hY=B(_hB(_hT,_hW.a,_hW.b,_hX.a,_hX.b));return new T2(0,_hY.a,_hY.b);},_hZ=function(_i0){return E(E(_i0).d);},_i1=function(_i2,_i3){var _i4=new T(function(){return B(_80(new T(function(){return E(E(E(_i2).c).a);})));}),_i5=new T(function(){return B(A2(_g0,E(_i2).a,new T(function(){return B(A2(_7U,B(_82(_i4)),_fX));})));});return new T2(0,new T(function(){return B(A2(_hZ,_i4,_i3));}),_i5);},_i6=function(_i7,_i8,_i9){var _ia=B(_i1(_i8,_i9));return new T2(0,_ia.a,_ia.b);},_ib=function(_ic,_id,_ie){var _if=new T(function(){return B(_80(new T(function(){return E(E(E(_ic).c).a);})));}),_ig=new T(function(){return B(_82(_if));}),_ih=new T(function(){var _ii=new T(function(){var _ij=new T(function(){return B(A3(_cg,_if,new T(function(){return B(A2(_7U,_ig,_cN));}),new T(function(){return B(A3(_bh,_ig,_id,_id));})));});return B(A2(_6S,_ig,_ij));});return B(A3(_86,B(_84(E(_ic).a)),function(_ik){return new F(function(){return A3(_bh,_ig,_ik,_ii);});},_ie));}),_il=new T(function(){return B(A3(_cg,_if,new T(function(){return B(A2(_7U,_ig,_cN));}),_id));});return new T2(0,_il,_ih);},_im=function(_in,_io,_ip){var _iq=E(_ip),_ir=B(_ib(_io,_iq.a,_iq.b));return new T2(0,_ir.a,_ir.b);},_is=function(_it,_iu){return new T4(0,_it,function(_hA,_hz){return new F(function(){return _hR(_it,_iu,_hA,_hz);});},function(_hz){return new F(function(){return _im(_it,_iu,_hz);});},function(_hz){return new F(function(){return _i6(_it,_iu,_hz);});});},_iv=function(_iw,_ix,_iy,_iz,_iA){var _iB=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_iw).c).a);})));})));}),_iC=new T(function(){var _iD=E(_iw).a,_iE=new T(function(){var _iF=function(_iG,_iH){return new F(function(){return A3(_6Q,_iB,new T(function(){return B(A3(_bh,_iB,_ix,_iH));}),new T(function(){return B(A3(_bh,_iB,_iG,_iz));}));});};return B(A3(_86,B(_84(_iD)),_iF,_iy));});return B(A3(_ci,_iD,_iE,_iA));});return new T2(0,new T(function(){return B(A3(_bh,_iB,_ix,_iz));}),_iC);},_iI=function(_iJ,_iK,_iL){var _iM=E(_iK),_iN=E(_iL),_iO=B(_iv(_iJ,_iM.a,_iM.b,_iN.a,_iN.b));return new T2(0,_iO.a,_iO.b);},_iP=function(_iQ,_iR,_iS,_iT,_iU){var _iV=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_iQ).c).a);})));})));}),_iW=new T(function(){var _iX=E(_iQ).a,_iY=new T(function(){return B(A3(_86,B(_84(_iX)),new T(function(){return B(_6Q(_iV));}),_iS));});return B(A3(_ci,_iX,_iY,_iU));});return new T2(0,new T(function(){return B(A3(_6Q,_iV,_iR,_iT));}),_iW);},_iZ=function(_j0,_j1,_j2){var _j3=E(_j1),_j4=E(_j2),_j5=B(_iP(_j0,_j3.a,_j3.b,_j4.a,_j4.b));return new T2(0,_j5.a,_j5.b);},_j6=function(_j7,_j8,_j9){var _ja=B(_jb(_j7));return new F(function(){return A3(_6Q,_ja,_j8,new T(function(){return B(A2(_6S,_ja,_j9));}));});},_jc=function(_jd){return E(E(_jd).e);},_je=function(_jf){return E(E(_jf).f);},_jg=function(_jh,_ji,_jj){var _jk=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_jh).c).a);})));})));}),_jl=new T(function(){var _jm=new T(function(){return B(A2(_je,_jk,_ji));});return B(A3(_86,B(_84(E(_jh).a)),function(_jn){return new F(function(){return A3(_bh,_jk,_jn,_jm);});},_jj));});return new T2(0,new T(function(){return B(A2(_jc,_jk,_ji));}),_jl);},_jo=function(_jp,_jq){var _jr=E(_jq),_js=B(_jg(_jp,_jr.a,_jr.b));return new T2(0,_js.a,_js.b);},_jt=function(_ju,_jv){var _jw=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_ju).c).a);})));})));}),_jx=new T(function(){return B(A2(_g0,E(_ju).a,new T(function(){return B(A2(_7U,_jw,_fX));})));});return new T2(0,new T(function(){return B(A2(_7U,_jw,_jv));}),_jx);},_jy=function(_jz,_jA){var _jB=B(_jt(_jz,_jA));return new T2(0,_jB.a,_jB.b);},_jC=function(_jD,_jE){var _jF=E(_jE),_jG=B(_88(_jD,_jF.a,_jF.b));return new T2(0,_jG.a,_jG.b);},_jH=function(_jI,_jJ){var _jK=new T(function(){return B(_82(new T(function(){return B(_80(new T(function(){return E(E(E(_jI).c).a);})));})));}),_jL=new T(function(){return B(A2(_g0,E(_jI).a,new T(function(){return B(A2(_7U,_jK,_fX));})));});return new T2(0,new T(function(){return B(A2(_je,_jK,_jJ));}),_jL);},_jM=function(_jN,_jO){var _jP=B(_jH(_jN,E(_jO).a));return new T2(0,_jP.a,_jP.b);},_jb=function(_jQ){return {_:0,a:function(_hA,_hz){return new F(function(){return _iZ(_jQ,_hA,_hz);});},b:function(_hA,_hz){return new F(function(){return _j6(_jQ,_hA,_hz);});},c:function(_hA,_hz){return new F(function(){return _iI(_jQ,_hA,_hz);});},d:function(_hz){return new F(function(){return _jC(_jQ,_hz);});},e:function(_hz){return new F(function(){return _jo(_jQ,_hz);});},f:function(_hz){return new F(function(){return _jM(_jQ,_hz);});},g:function(_hz){return new F(function(){return _jy(_jQ,_hz);});}};},_jR=function(_jS){var _jT=new T(function(){return E(E(_jS).a);}),_jU=new T3(0,_7R,_7W,new T2(0,_jT,new T(function(){return E(E(_jS).b);}))),_jV=new T(function(){return B(_hw(new T(function(){return B(_is(new T(function(){return B(_jb(_jU));}),_jU));}),_jU));}),_jW=new T(function(){return B(_82(new T(function(){return B(_80(_jT));})));}),_jX=function(_jY){return E(B(_bx(_jV,new T(function(){var _jZ=E(_jY),_k0=B(A2(_7U,_jW,_7T)),_k1=B(A2(_7U,_jW,_7S));return new T3(0,E(new T2(0,_jZ.a,new T3(0,E(_k0),E(_k1),E(_k1)))),E(new T2(0,_jZ.b,new T3(0,E(_k1),E(_k0),E(_k1)))),E(new T2(0,_jZ.c,new T3(0,E(_k1),E(_k1),E(_k0)))));}))).b);};return E(_jX);},_k2=new T(function(){return B(_jR(_cd));}),_k3=function(_k4,_k5){var _k6=E(_k5);return (_k6._==0)?__Z:new T2(1,_k4,new T2(1,_k6.a,new T(function(){return B(_k3(_k4,_k6.b));})));},_k7=new T(function(){var _k8=B(A1(_k2,_bK));return new T2(1,_k8.a,new T(function(){return B(_k3(_9o,new T2(1,_k8.b,new T2(1,_k8.c,_w))));}));}),_k9=new T1(1,_k7),_ka=new T2(1,_k9,_9g),_kb=new T(function(){return B(unCStr("vec3("));}),_kc=new T1(0,_kb),_kd=new T2(1,_kc,_ka),_ke=new T(function(){return toJSStr(B(_93(_x,_8N,_kd)));}),_kf=function(_kg,_kh){while(1){var _ki=E(_kg);if(!_ki._){return E(_kh);}else{var _kj=_kh+1|0;_kg=_ki.b;_kh=_kj;continue;}}},_kk=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_kl=new T(function(){return B(err(_kk));}),_km=0,_kn=new T3(0,E(_km),E(_km),E(_km)),_ko=new T(function(){return B(unCStr("Negative exponent"));}),_kp=new T(function(){return B(err(_ko));}),_kq=function(_kr,_ks,_kt){while(1){if(!(_ks%2)){var _ku=_kr*_kr,_kv=quot(_ks,2);_kr=_ku;_ks=_kv;continue;}else{var _kw=E(_ks);if(_kw==1){return _kr*_kt;}else{var _ku=_kr*_kr,_kx=_kr*_kt;_kr=_ku;_ks=quot(_kw-1|0,2);_kt=_kx;continue;}}}},_ky=function(_kz,_kA){while(1){if(!(_kA%2)){var _kB=_kz*_kz,_kC=quot(_kA,2);_kz=_kB;_kA=_kC;continue;}else{var _kD=E(_kA);if(_kD==1){return E(_kz);}else{return new F(function(){return _kq(_kz*_kz,quot(_kD-1|0,2),_kz);});}}}},_kE=function(_kF){var _kG=E(_kF);return new F(function(){return Math.log(_kG+(_kG+1)*Math.sqrt((_kG-1)/(_kG+1)));});},_kH=function(_kI){var _kJ=E(_kI);return new F(function(){return Math.log(_kJ+Math.sqrt(1+_kJ*_kJ));});},_kK=function(_kL){var _kM=E(_kL);return 0.5*Math.log((1+_kM)/(1-_kM));},_kN=function(_kO,_kP){return Math.log(E(_kP))/Math.log(E(_kO));},_kQ=3.141592653589793,_kR=function(_kS){var _kT=E(_kS);return new F(function(){return _6r(_kT.a,_kT.b);});},_kU=function(_kV){return 1/E(_kV);},_kW=function(_kX){var _kY=E(_kX),_kZ=E(_kY);return (_kZ==0)?E(_6q):(_kZ<=0)? -_kZ:E(_kY);},_l0=function(_l1){var _l2=E(_l1);if(!_l2._){return _l2.a;}else{return new F(function(){return I_toNumber(_l2.a);});}},_l3=function(_l4){return new F(function(){return _l0(_l4);});},_l5=1,_l6=-1,_l7=function(_l8){var _l9=E(_l8);return (_l9<=0)?(_l9>=0)?E(_l9):E(_l6):E(_l5);},_la=function(_lb,_lc){return E(_lb)-E(_lc);},_ld=function(_le){return  -E(_le);},_lf=function(_lg,_lh){return E(_lg)+E(_lh);},_li=function(_lj,_lk){return E(_lj)*E(_lk);},_ll={_:0,a:_lf,b:_la,c:_li,d:_ld,e:_kW,f:_l7,g:_l3},_lm=function(_ln,_lo){return E(_ln)/E(_lo);},_lp=new T4(0,_ll,_lm,_kU,_kR),_lq=function(_lr){return new F(function(){return Math.acos(E(_lr));});},_ls=function(_lt){return new F(function(){return Math.asin(E(_lt));});},_lu=function(_lv){return new F(function(){return Math.atan(E(_lv));});},_lw=function(_lx){return new F(function(){return Math.cos(E(_lx));});},_ly=function(_lz){return new F(function(){return cosh(E(_lz));});},_lA=function(_lB){return new F(function(){return Math.exp(E(_lB));});},_lC=function(_lD){return new F(function(){return Math.log(E(_lD));});},_lE=function(_lF,_lG){return new F(function(){return Math.pow(E(_lF),E(_lG));});},_lH=function(_lI){return new F(function(){return Math.sin(E(_lI));});},_lJ=function(_lK){return new F(function(){return sinh(E(_lK));});},_lL=function(_lM){return new F(function(){return Math.sqrt(E(_lM));});},_lN=function(_lO){return new F(function(){return Math.tan(E(_lO));});},_lP=function(_lQ){return new F(function(){return tanh(E(_lQ));});},_lR={_:0,a:_lp,b:_kQ,c:_lA,d:_lC,e:_lL,f:_lE,g:_kN,h:_lH,i:_lw,j:_lN,k:_ls,l:_lq,m:_lu,n:_lJ,o:_ly,p:_lP,q:_kH,r:_kE,s:_kK},_lS=function(_lT,_lU){return (E(_lT)!=E(_lU))?true:false;},_lV=function(_lW,_lX){return E(_lW)==E(_lX);},_lY=new T2(0,_lV,_lS),_lZ=function(_m0,_m1){return E(_m0)<E(_m1);},_m2=function(_m3,_m4){return E(_m3)<=E(_m4);},_m5=function(_m6,_m7){return E(_m6)>E(_m7);},_m8=function(_m9,_ma){return E(_m9)>=E(_ma);},_mb=function(_mc,_md){var _me=E(_mc),_mf=E(_md);return (_me>=_mf)?(_me!=_mf)?2:1:0;},_mg=function(_mh,_mi){var _mj=E(_mh),_mk=E(_mi);return (_mj>_mk)?E(_mj):E(_mk);},_ml=function(_mm,_mn){var _mo=E(_mm),_mp=E(_mn);return (_mo>_mp)?E(_mp):E(_mo);},_mq={_:0,a:_lY,b:_mb,c:_lZ,d:_m2,e:_m5,f:_m8,g:_mg,h:_ml},_mr="dz",_ms="wy",_mt="wx",_mu="dy",_mv="dx",_mw="t",_mx="a",_my="r",_mz="ly",_mA="lx",_mB="wz",_mC=0,_mD=function(_mE){var _mF=__new(),_mG=_mF,_mH=function(_mI,_){while(1){var _mJ=E(_mI);if(!_mJ._){return _mC;}else{var _mK=E(_mJ.a),_mL=__set(_mG,E(_mK.a),E(_mK.b));_mI=_mJ.b;continue;}}},_mM=B(_mH(_mE,_));return E(_mG);},_mN=function(_mO,_mP,_mQ,_mR,_mS,_mT,_mU,_mV,_mW){return new F(function(){return _mD(new T2(1,new T2(0,_mt,_mO),new T2(1,new T2(0,_ms,_mP),new T2(1,new T2(0,_mB,_mQ),new T2(1,new T2(0,_mA,_mR*_mS*Math.cos(_mT)),new T2(1,new T2(0,_mz,_mR*_mS*Math.sin(_mT)),new T2(1,new T2(0,_my,_mR),new T2(1,new T2(0,_mx,_mS),new T2(1,new T2(0,_mw,_mT),new T2(1,new T2(0,_mv,_mU),new T2(1,new T2(0,_mu,_mV),new T2(1,new T2(0,_mr,_mW),_w))))))))))));});},_mX=function(_mY){var _mZ=E(_mY),_n0=E(_mZ.a),_n1=E(_mZ.b),_n2=E(_mZ.d);return new F(function(){return _mN(_n0.a,_n0.b,_n0.c,E(_n1.a),E(_n1.b),E(_mZ.c),_n2.a,_n2.b,_n2.c);});},_n3=function(_n4,_n5){var _n6=E(_n5);return (_n6._==0)?__Z:new T2(1,new T(function(){return B(A1(_n4,_n6.a));}),new T(function(){return B(_n3(_n4,_n6.b));}));},_n7=function(_n8,_n9,_na){var _nb=__lst2arr(B(_n3(_mX,new T2(1,_n8,new T2(1,_n9,new T2(1,_na,_w))))));return E(_nb);},_nc=function(_nd){var _ne=E(_nd);return new F(function(){return _n7(_ne.a,_ne.b,_ne.c);});},_nf=new T2(0,_lR,_mq),_ng=function(_nh,_ni,_nj,_nk){var _nl=B(_80(_nh)),_nm=new T(function(){return B(A2(_bv,_nh,new T(function(){return B(_bj(_nh,_ni,_nj,_nk,_ni,_nj,_nk));})));});return new T3(0,B(A3(_cg,_nl,_ni,_nm)),B(A3(_cg,_nl,_nj,_nm)),B(A3(_cg,_nl,_nk,_nm)));},_nn=function(_no,_np,_nq,_nr,_ns,_nt,_nu){var _nv=B(_bh(_no));return new T3(0,B(A1(B(A1(_nv,_np)),_ns)),B(A1(B(A1(_nv,_nq)),_nt)),B(A1(B(A1(_nv,_nr)),_nu)));},_nw=function(_nx,_ny,_nz,_nA,_nB,_nC,_nD){var _nE=B(_6Q(_nx));return new T3(0,B(A1(B(A1(_nE,_ny)),_nB)),B(A1(B(A1(_nE,_nz)),_nC)),B(A1(B(A1(_nE,_nA)),_nD)));},_nF=function(_nG,_nH){var _nI=new T(function(){return E(E(_nG).a);}),_nJ=new T(function(){return B(A2(_jR,new T2(0,_nI,new T(function(){return E(E(_nG).b);})),_nH));}),_nK=new T(function(){var _nL=E(_nJ),_nM=B(_ng(_nI,_nL.a,_nL.b,_nL.c));return new T3(0,E(_nM.a),E(_nM.b),E(_nM.c));}),_nN=new T(function(){var _nO=E(_nH),_nP=E(_nK),_nQ=B(_80(_nI)),_nR=new T(function(){return B(A2(_bv,_nI,new T(function(){var _nS=E(_nJ),_nT=_nS.a,_nU=_nS.b,_nV=_nS.c;return B(_bj(_nI,_nT,_nU,_nV,_nT,_nU,_nV));})));}),_nW=B(A3(_cg,_nQ,new T(function(){return B(_bx(_nI,_nO));}),_nR)),_nX=B(_82(_nQ)),_nY=B(_nn(_nX,_nP.a,_nP.b,_nP.c,_nW,_nW,_nW)),_nZ=B(_6S(_nX)),_o0=B(_nw(_nX,_nO.a,_nO.b,_nO.c,B(A1(_nZ,_nY.a)),B(A1(_nZ,_nY.b)),B(A1(_nZ,_nY.c))));return new T3(0,E(_o0.a),E(_o0.b),E(_o0.c));});return new T2(0,_nN,_nK);},_o1=function(_o2){return E(E(_o2).a);},_o3=function(_o4,_o5,_o6,_o7,_o8,_o9,_oa){var _ob=B(_bj(_o4,_o8,_o9,_oa,_o5,_o6,_o7)),_oc=B(_82(B(_80(_o4)))),_od=B(_nn(_oc,_o8,_o9,_oa,_ob,_ob,_ob)),_oe=B(_6S(_oc));return new F(function(){return _nw(_oc,_o5,_o6,_o7,B(A1(_oe,_od.a)),B(A1(_oe,_od.b)),B(A1(_oe,_od.c)));});},_of=function(_og){return E(E(_og).a);},_oh=function(_oi,_oj,_ok,_ol){var _om=new T(function(){var _on=E(_ol),_oo=E(_ok),_op=B(_o3(_oi,_on.a,_on.b,_on.c,_oo.a,_oo.b,_oo.c));return new T3(0,E(_op.a),E(_op.b),E(_op.c));}),_oq=new T(function(){return B(A2(_bv,_oi,new T(function(){var _or=E(_om),_os=_or.a,_ot=_or.b,_ou=_or.c;return B(_bj(_oi,_os,_ot,_ou,_os,_ot,_ou));})));});if(!B(A3(_of,B(_o1(_oj)),_oq,new T(function(){return B(A2(_7U,B(_82(B(_80(_oi)))),_7S));})))){var _ov=E(_om),_ow=B(_ng(_oi,_ov.a,_ov.b,_ov.c)),_ox=B(A2(_bv,_oi,new T(function(){var _oy=E(_ol),_oz=_oy.a,_oA=_oy.b,_oB=_oy.c;return B(_bj(_oi,_oz,_oA,_oB,_oz,_oA,_oB));}))),_oC=B(_bh(new T(function(){return B(_82(new T(function(){return B(_80(_oi));})));})));return new T3(0,B(A1(B(A1(_oC,_ow.a)),_ox)),B(A1(B(A1(_oC,_ow.b)),_ox)),B(A1(B(A1(_oC,_ow.c)),_ox)));}else{var _oD=B(A2(_7U,B(_82(B(_80(_oi)))),_7S));return new T3(0,_oD,_oD,_oD);}},_oE=new T(function(){var _oF=eval("angleCount"),_oG=Number(_oF);return jsTrunc(_oG);}),_oH=new T(function(){return E(_oE);}),_oI=new T(function(){return B(unCStr(": empty list"));}),_oJ=new T(function(){return B(unCStr("Prelude."));}),_oK=function(_oL){return new F(function(){return err(B(_n(_oJ,new T(function(){return B(_n(_oL,_oI));},1))));});},_oM=new T(function(){return B(unCStr("head"));}),_oN=new T(function(){return B(_oK(_oM));}),_oO=function(_oP,_oQ,_oR){var _oS=E(_oP);if(!_oS._){return __Z;}else{var _oT=E(_oQ);if(!_oT._){return __Z;}else{var _oU=_oT.a,_oV=E(_oR);if(!_oV._){return __Z;}else{var _oW=E(_oV.a),_oX=_oW.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_oS.a),E(_oU),E(_oX));}),new T2(1,new T(function(){return new T3(0,E(_oU),E(_oX),E(_oW.b));}),_w)),new T(function(){return B(_oO(_oS.b,_oT.b,_oV.b));},1));});}}}},_oY=new T(function(){return B(unCStr("tail"));}),_oZ=new T(function(){return B(_oK(_oY));}),_p0=function(_p1,_p2){var _p3=E(_p1);if(!_p3._){return __Z;}else{var _p4=E(_p2);return (_p4._==0)?__Z:new T2(1,new T2(0,_p3.a,_p4.a),new T(function(){return B(_p0(_p3.b,_p4.b));}));}},_p5=function(_p6,_p7){var _p8=E(_p6);if(!_p8._){return __Z;}else{var _p9=E(_p7);if(!_p9._){return __Z;}else{var _pa=E(_p8.a),_pb=_pa.b,_pc=E(_p9.a).b,_pd=new T(function(){var _pe=new T(function(){return B(_p0(_pc,new T(function(){var _pf=E(_pc);if(!_pf._){return E(_oZ);}else{return E(_pf.b);}},1)));},1);return B(_oO(_pb,new T(function(){var _pg=E(_pb);if(!_pg._){return E(_oZ);}else{return E(_pg.b);}},1),_pe));});return new F(function(){return _n(new T2(1,new T(function(){var _ph=E(_pb);if(!_ph._){return E(_oN);}else{var _pi=E(_pc);if(!_pi._){return E(_oN);}else{return new T3(0,E(_pa.a),E(_ph.a),E(_pi.a));}}}),_pd),new T(function(){return B(_p5(_p8.b,_p9.b));},1));});}}},_pj=new T(function(){return E(_oH)-1;}),_pk=new T1(0,1),_pl=function(_pm,_pn){var _po=E(_pn),_pp=new T(function(){var _pq=B(_82(_pm)),_pr=B(_pl(_pm,B(A3(_6Q,_pq,_po,new T(function(){return B(A2(_7U,_pq,_pk));})))));return new T2(1,_pr.a,_pr.b);});return new T2(0,_po,_pp);},_ps=function(_pt){return E(E(_pt).d);},_pu=new T1(0,2),_pv=function(_pw,_px){var _py=E(_px);if(!_py._){return __Z;}else{var _pz=_py.a;return (!B(A1(_pw,_pz)))?__Z:new T2(1,_pz,new T(function(){return B(_pv(_pw,_py.b));}));}},_pA=function(_pB,_pC,_pD,_pE){var _pF=B(_pl(_pC,_pD)),_pG=new T(function(){var _pH=B(_82(_pC)),_pI=new T(function(){return B(A3(_cg,_pC,new T(function(){return B(A2(_7U,_pH,_pk));}),new T(function(){return B(A2(_7U,_pH,_pu));})));});return B(A3(_6Q,_pH,_pE,_pI));});return new F(function(){return _pv(function(_pJ){return new F(function(){return A3(_ps,_pB,_pJ,_pG);});},new T2(1,_pF.a,_pF.b));});},_pK=new T(function(){return B(_pA(_mq,_lp,_km,_pj));}),_pL=function(_pM,_pN){while(1){var _pO=E(_pM);if(!_pO._){return E(_pN);}else{_pM=_pO.b;_pN=_pO.a;continue;}}},_pP=new T(function(){return B(unCStr("last"));}),_pQ=new T(function(){return B(_oK(_pP));}),_pR=function(_pS){return new F(function(){return _pL(_pS,_pQ);});},_pT=function(_pU){return new F(function(){return _pR(E(_pU).b);});},_pV=new T(function(){var _pW=eval("proceedCount"),_pX=Number(_pW);return jsTrunc(_pX);}),_pY=new T(function(){return E(_pV);}),_pZ=1,_q0=new T(function(){return B(_pA(_mq,_lp,_pZ,_pY));}),_q1=function(_q2,_q3,_q4,_q5,_q6,_q7,_q8,_q9,_qa,_qb,_qc,_qd,_qe,_qf){var _qg=new T(function(){var _qh=new T(function(){var _qi=E(_qb),_qj=E(_qf),_qk=E(_qe),_ql=E(_qc),_qm=E(_qd),_qn=E(_qa);return new T3(0,_qi*_qj-_qk*_ql,_ql*_qm-_qj*_qn,_qn*_qk-_qm*_qi);}),_qo=function(_qp){var _qq=new T(function(){var _qr=E(_qp)/E(_oH);return (_qr+_qr)*3.141592653589793;}),_qs=new T(function(){return B(A1(_q2,_qq));}),_qt=new T(function(){var _qu=new T(function(){var _qv=E(_qs)/E(_pY);return new T3(0,E(_qv),E(_qv),E(_qv));}),_qw=function(_qx,_qy){var _qz=E(_qx);if(!_qz._){return new T2(0,_w,_qy);}else{var _qA=new T(function(){var _qB=B(_nF(_nf,new T(function(){var _qC=E(_qy),_qD=E(_qC.a),_qE=E(_qC.b),_qF=E(_qu);return new T3(0,E(_qD.a)+E(_qE.a)*E(_qF.a),E(_qD.b)+E(_qE.b)*E(_qF.b),E(_qD.c)+E(_qE.c)*E(_qF.c));}))),_qG=_qB.a,_qH=new T(function(){var _qI=E(_qB.b),_qJ=E(E(_qy).b),_qK=B(_o3(_lR,_qJ.a,_qJ.b,_qJ.c,_qI.a,_qI.b,_qI.c)),_qL=B(_ng(_lR,_qK.a,_qK.b,_qK.c));return new T3(0,E(_qL.a),E(_qL.b),E(_qL.c));});return new T2(0,new T(function(){var _qM=E(_qs),_qN=E(_qq);return new T4(0,E(_qG),E(new T2(0,E(_qz.a)/E(_pY),E(_qM))),E(_qN),E(_qH));}),new T2(0,_qG,_qH));}),_qO=new T(function(){var _qP=B(_qw(_qz.b,new T(function(){return E(E(_qA).b);})));return new T2(0,_qP.a,_qP.b);});return new T2(0,new T2(1,new T(function(){return E(E(_qA).a);}),new T(function(){return E(E(_qO).a);})),new T(function(){return E(E(_qO).b);}));}},_qQ=function(_qR,_qS,_qT,_qU,_qV){var _qW=E(_qR);if(!_qW._){return new T2(0,_w,new T2(0,new T3(0,E(_qS),E(_qT),E(_qU)),_qV));}else{var _qX=new T(function(){var _qY=B(_nF(_nf,new T(function(){var _qZ=E(_qV),_r0=E(_qu);return new T3(0,E(_qS)+E(_qZ.a)*E(_r0.a),E(_qT)+E(_qZ.b)*E(_r0.b),E(_qU)+E(_qZ.c)*E(_r0.c));}))),_r1=_qY.a,_r2=new T(function(){var _r3=E(_qY.b),_r4=E(_qV),_r5=B(_o3(_lR,_r4.a,_r4.b,_r4.c,_r3.a,_r3.b,_r3.c)),_r6=B(_ng(_lR,_r5.a,_r5.b,_r5.c));return new T3(0,E(_r6.a),E(_r6.b),E(_r6.c));});return new T2(0,new T(function(){var _r7=E(_qs),_r8=E(_qq);return new T4(0,E(_r1),E(new T2(0,E(_qW.a)/E(_pY),E(_r7))),E(_r8),E(_r2));}),new T2(0,_r1,_r2));}),_r9=new T(function(){var _ra=B(_qw(_qW.b,new T(function(){return E(E(_qX).b);})));return new T2(0,_ra.a,_ra.b);});return new T2(0,new T2(1,new T(function(){return E(E(_qX).a);}),new T(function(){return E(E(_r9).a);})),new T(function(){return E(E(_r9).b);}));}};return E(B(_qQ(_q0,_q5,_q6,_q7,new T(function(){var _rb=E(_qh),_rc=E(_qq)+_q8,_rd=Math.cos(_rc),_re=Math.sin(_rc);return new T3(0,E(_qa)*_rd+E(_rb.a)*_re,E(_qb)*_rd+E(_rb.b)*_re,E(_qc)*_rd+E(_rb.c)*_re);}))).a);});return new T2(0,new T(function(){var _rf=E(_qs),_rg=E(_qq);return new T4(0,E(new T3(0,E(_q5),E(_q6),E(_q7))),E(new T2(0,E(_km),E(_rf))),E(_rg),E(_kn));}),_qt);};return B(_n3(_qo,_pK));}),_rh=new T(function(){var _ri=new T(function(){var _rj=B(_n(_qg,new T2(1,new T(function(){var _rk=E(_qg);if(!_rk._){return E(_oN);}else{return E(_rk.a);}}),_w)));if(!_rj._){return E(_oZ);}else{return E(_rj.b);}},1);return B(_p5(_qg,_ri));});return new T2(0,_rh,new T(function(){return B(_n3(_pT,_qg));}));},_rl=function(_rm,_rn,_ro,_rp,_rq,_rr,_rs,_rt,_ru,_rv,_rw,_rx,_ry,_rz,_rA,_rB,_rC){var _rD=B(_nF(_nf,new T3(0,E(_rp),E(_rq),E(_rr)))),_rE=_rD.b,_rF=E(_rD.a),_rG=B(_oh(_lR,_mq,_rE,new T3(0,E(_rt),E(_ru),E(_rv)))),_rH=E(_rE),_rI=_rH.a,_rJ=_rH.b,_rK=_rH.c,_rL=B(_o3(_lR,_rx,_ry,_rz,_rI,_rJ,_rK)),_rM=B(_ng(_lR,_rL.a,_rL.b,_rL.c)),_rN=_rM.a,_rO=_rM.b,_rP=_rM.c,_rQ=E(_rs),_rR=new T2(0,E(new T3(0,E(_rG.a),E(_rG.b),E(_rG.c))),E(_rw)),_rS=B(_q1(_rm,_rn,_ro,_rF.a,_rF.b,_rF.c,_rQ,_rR,_rN,_rO,_rP,_rI,_rJ,_rK)),_rT=__lst2arr(B(_n3(_nc,_rS.a))),_rU=__lst2arr(B(_n3(_mX,_rS.b)));return {_:0,a:_rm,b:_rn,c:_ro,d:new T2(0,E(_rF),E(_rQ)),e:_rR,f:new T3(0,E(_rN),E(_rO),E(_rP)),g:_rH,h:_rT,i:_rU};},_rV=-4,_rW=new T3(0,E(_km),E(_rV),E(_km)),_rX=function(_rY){return E(_rW);},_rZ=new T(function(){return 6.283185307179586/E(_oH);}),_s0=function(_){return new F(function(){return __jsNull();});},_s1=function(_s2){var _s3=B(A1(_s2,_));return E(_s3);},_s4=new T(function(){return B(_s1(_s0));}),_s5=function(_s6,_s7,_s8,_s9,_sa,_sb,_sc,_sd,_se,_sf,_sg,_sh,_si){var _sj=function(_sk){var _sl=E(_rZ),_sm=2+_sk|0,_sn=_sm-1|0,_so=(2+_sk)*(1+_sk),_sp=E(_pK);if(!_sp._){return _sl*0;}else{var _sq=_sp.a,_sr=_sp.b,_ss=B(A1(_s6,new T(function(){return 6.283185307179586*E(_sq)/E(_oH);}))),_st=B(A1(_s6,new T(function(){return 6.283185307179586*(E(_sq)+1)/E(_oH);})));if(_ss!=_st){if(_sm>=0){var _su=E(_sm);if(!_su){var _sv=function(_sw,_sx){while(1){var _sy=B((function(_sz,_sA){var _sB=E(_sz);if(!_sB._){return E(_sA);}else{var _sC=_sB.a,_sD=_sB.b,_sE=B(A1(_s6,new T(function(){return 6.283185307179586*E(_sC)/E(_oH);}))),_sF=B(A1(_s6,new T(function(){return 6.283185307179586*(E(_sC)+1)/E(_oH);})));if(_sE!=_sF){var _sG=_sA+0/(_sE-_sF)/_so;_sw=_sD;_sx=_sG;return __continue;}else{if(_sn>=0){var _sH=E(_sn);if(!_sH){var _sG=_sA+_sm/_so;_sw=_sD;_sx=_sG;return __continue;}else{var _sG=_sA+_sm*B(_ky(_sE,_sH))/_so;_sw=_sD;_sx=_sG;return __continue;}}else{return E(_kp);}}}})(_sw,_sx));if(_sy!=__continue){return _sy;}}};return _sl*B(_sv(_sr,0/(_ss-_st)/_so));}else{var _sI=function(_sJ,_sK){while(1){var _sL=B((function(_sM,_sN){var _sO=E(_sM);if(!_sO._){return E(_sN);}else{var _sP=_sO.a,_sQ=_sO.b,_sR=B(A1(_s6,new T(function(){return 6.283185307179586*E(_sP)/E(_oH);}))),_sS=B(A1(_s6,new T(function(){return 6.283185307179586*(E(_sP)+1)/E(_oH);})));if(_sR!=_sS){if(_su>=0){var _sT=_sN+(B(_ky(_sR,_su))-B(_ky(_sS,_su)))/(_sR-_sS)/_so;_sJ=_sQ;_sK=_sT;return __continue;}else{return E(_kp);}}else{if(_sn>=0){var _sU=E(_sn);if(!_sU){var _sT=_sN+_sm/_so;_sJ=_sQ;_sK=_sT;return __continue;}else{var _sT=_sN+_sm*B(_ky(_sR,_sU))/_so;_sJ=_sQ;_sK=_sT;return __continue;}}else{return E(_kp);}}}})(_sJ,_sK));if(_sL!=__continue){return _sL;}}};return _sl*B(_sI(_sr,(B(_ky(_ss,_su))-B(_ky(_st,_su)))/(_ss-_st)/_so));}}else{return E(_kp);}}else{if(_sn>=0){var _sV=E(_sn);if(!_sV){var _sW=function(_sX,_sY){while(1){var _sZ=B((function(_t0,_t1){var _t2=E(_t0);if(!_t2._){return E(_t1);}else{var _t3=_t2.a,_t4=_t2.b,_t5=B(A1(_s6,new T(function(){return 6.283185307179586*E(_t3)/E(_oH);}))),_t6=B(A1(_s6,new T(function(){return 6.283185307179586*(E(_t3)+1)/E(_oH);})));if(_t5!=_t6){if(_sm>=0){var _t7=E(_sm);if(!_t7){var _t8=_t1+0/(_t5-_t6)/_so;_sX=_t4;_sY=_t8;return __continue;}else{var _t8=_t1+(B(_ky(_t5,_t7))-B(_ky(_t6,_t7)))/(_t5-_t6)/_so;_sX=_t4;_sY=_t8;return __continue;}}else{return E(_kp);}}else{var _t8=_t1+_sm/_so;_sX=_t4;_sY=_t8;return __continue;}}})(_sX,_sY));if(_sZ!=__continue){return _sZ;}}};return _sl*B(_sW(_sr,_sm/_so));}else{var _t9=function(_ta,_tb){while(1){var _tc=B((function(_td,_te){var _tf=E(_td);if(!_tf._){return E(_te);}else{var _tg=_tf.a,_th=_tf.b,_ti=B(A1(_s6,new T(function(){return 6.283185307179586*E(_tg)/E(_oH);}))),_tj=B(A1(_s6,new T(function(){return 6.283185307179586*(E(_tg)+1)/E(_oH);})));if(_ti!=_tj){if(_sm>=0){var _tk=E(_sm);if(!_tk){var _tl=_te+0/(_ti-_tj)/_so;_ta=_th;_tb=_tl;return __continue;}else{var _tl=_te+(B(_ky(_ti,_tk))-B(_ky(_tj,_tk)))/(_ti-_tj)/_so;_ta=_th;_tb=_tl;return __continue;}}else{return E(_kp);}}else{if(_sV>=0){var _tl=_te+_sm*B(_ky(_ti,_sV))/_so;_ta=_th;_tb=_tl;return __continue;}else{return E(_kp);}}}})(_ta,_tb));if(_tc!=__continue){return _tc;}}};return _sl*B(_t9(_sr,_sm*B(_ky(_ss,_sV))/_so));}}else{return E(_kp);}}}},_tm=E(_s4),_tn=1/(B(_sj(1))*_s7);return new F(function(){return _rl(_s6,_rX,new T2(0,E(new T3(0,E(_tn),E(_tn),E(_tn))),1/(B(_sj(3))*_s7)),_s8,_s9,_sa,_sb,_sc,_sd,_se,_sf,_sg,_sh,_si,_kn,_tm,_tm);});},_to=1,_tp=0,_tq=function(_tr){var _ts=I_decodeDouble(_tr);return new T2(0,new T1(1,_ts.b),_ts.a);},_tt=function(_tu){return new T1(0,_tu);},_tv=function(_tw){var _tx=hs_intToInt64(2147483647),_ty=hs_leInt64(_tw,_tx);if(!_ty){return new T1(1,I_fromInt64(_tw));}else{var _tz=hs_intToInt64(-2147483648),_tA=hs_geInt64(_tw,_tz);if(!_tA){return new T1(1,I_fromInt64(_tw));}else{var _tB=hs_int64ToInt(_tw);return new F(function(){return _tt(_tB);});}}},_tC=new T(function(){var _tD=newByteArr(256),_tE=_tD,_=_tE["v"]["i8"][0]=8,_tF=function(_tG,_tH,_tI,_){while(1){if(_tI>=256){if(_tG>=256){return E(_);}else{var _tJ=imul(2,_tG)|0,_tK=_tH+1|0,_tL=_tG;_tG=_tJ;_tH=_tK;_tI=_tL;continue;}}else{var _=_tE["v"]["i8"][_tI]=_tH,_tL=_tI+_tG|0;_tI=_tL;continue;}}},_=B(_tF(2,0,1,_));return _tE;}),_tM=function(_tN,_tO){var _tP=hs_int64ToInt(_tN),_tQ=E(_tC),_tR=_tQ["v"]["i8"][(255&_tP>>>0)>>>0&4294967295];if(_tO>_tR){if(_tR>=8){var _tS=hs_uncheckedIShiftRA64(_tN,8),_tT=function(_tU,_tV){while(1){var _tW=B((function(_tX,_tY){var _tZ=hs_int64ToInt(_tX),_u0=_tQ["v"]["i8"][(255&_tZ>>>0)>>>0&4294967295];if(_tY>_u0){if(_u0>=8){var _u1=hs_uncheckedIShiftRA64(_tX,8),_u2=_tY-8|0;_tU=_u1;_tV=_u2;return __continue;}else{return new T2(0,new T(function(){var _u3=hs_uncheckedIShiftRA64(_tX,_u0);return B(_tv(_u3));}),_tY-_u0|0);}}else{return new T2(0,new T(function(){var _u4=hs_uncheckedIShiftRA64(_tX,_tY);return B(_tv(_u4));}),0);}})(_tU,_tV));if(_tW!=__continue){return _tW;}}};return new F(function(){return _tT(_tS,_tO-8|0);});}else{return new T2(0,new T(function(){var _u5=hs_uncheckedIShiftRA64(_tN,_tR);return B(_tv(_u5));}),_tO-_tR|0);}}else{return new T2(0,new T(function(){var _u6=hs_uncheckedIShiftRA64(_tN,_tO);return B(_tv(_u6));}),0);}},_u7=function(_u8){var _u9=hs_intToInt64(_u8);return E(_u9);},_ua=function(_ub){var _uc=E(_ub);if(!_uc._){return new F(function(){return _u7(_uc.a);});}else{return new F(function(){return I_toInt64(_uc.a);});}},_ud=function(_ue){return I_toInt(_ue)>>>0;},_uf=function(_ug){var _uh=E(_ug);if(!_uh._){return _uh.a>>>0;}else{return new F(function(){return _ud(_uh.a);});}},_ui=function(_uj){var _uk=B(_tq(_uj)),_ul=_uk.a,_um=_uk.b;if(_um<0){var _un=function(_uo){if(!_uo){return new T2(0,E(_ul),B(_3C(_1U, -_um)));}else{var _up=B(_tM(B(_ua(_ul)), -_um));return new T2(0,E(_up.a),B(_3C(_1U,_up.b)));}};if(!((B(_uf(_ul))&1)>>>0)){return new F(function(){return _un(1);});}else{return new F(function(){return _un(0);});}}else{return new T2(0,B(_3C(_ul,_um)),_1U);}},_uq=function(_ur){var _us=B(_ui(E(_ur)));return new T2(0,E(_us.a),E(_us.b));},_ut=new T3(0,_ll,_mq,_uq),_uu=function(_uv){return E(E(_uv).a);},_uw=function(_ux){return E(E(_ux).a);},_uy=function(_uz,_uA){if(_uz<=_uA){var _uB=function(_uC){return new T2(1,_uC,new T(function(){if(_uC!=_uA){return B(_uB(_uC+1|0));}else{return __Z;}}));};return new F(function(){return _uB(_uz);});}else{return __Z;}},_uD=function(_uE){return new F(function(){return _uy(E(_uE),2147483647);});},_uF=function(_uG,_uH,_uI){if(_uI<=_uH){var _uJ=new T(function(){var _uK=_uH-_uG|0,_uL=function(_uM){return (_uM>=(_uI-_uK|0))?new T2(1,_uM,new T(function(){return B(_uL(_uM+_uK|0));})):new T2(1,_uM,_w);};return B(_uL(_uH));});return new T2(1,_uG,_uJ);}else{return (_uI<=_uG)?new T2(1,_uG,_w):__Z;}},_uN=function(_uO,_uP,_uQ){if(_uQ>=_uP){var _uR=new T(function(){var _uS=_uP-_uO|0,_uT=function(_uU){return (_uU<=(_uQ-_uS|0))?new T2(1,_uU,new T(function(){return B(_uT(_uU+_uS|0));})):new T2(1,_uU,_w);};return B(_uT(_uP));});return new T2(1,_uO,_uR);}else{return (_uQ>=_uO)?new T2(1,_uO,_w):__Z;}},_uV=function(_uW,_uX){if(_uX<_uW){return new F(function(){return _uF(_uW,_uX,-2147483648);});}else{return new F(function(){return _uN(_uW,_uX,2147483647);});}},_uY=function(_uZ,_v0){return new F(function(){return _uV(E(_uZ),E(_v0));});},_v1=function(_v2,_v3,_v4){if(_v3<_v2){return new F(function(){return _uF(_v2,_v3,_v4);});}else{return new F(function(){return _uN(_v2,_v3,_v4);});}},_v5=function(_v6,_v7,_v8){return new F(function(){return _v1(E(_v6),E(_v7),E(_v8));});},_v9=function(_va,_vb){return new F(function(){return _uy(E(_va),E(_vb));});},_vc=function(_vd){return E(_vd);},_ve=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_vf=new T(function(){return B(err(_ve));}),_vg=function(_vh){var _vi=E(_vh);return (_vi==(-2147483648))?E(_vf):_vi-1|0;},_vj=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_vk=new T(function(){return B(err(_vj));}),_vl=function(_vm){var _vn=E(_vm);return (_vn==2147483647)?E(_vk):_vn+1|0;},_vo={_:0,a:_vl,b:_vg,c:_vc,d:_vc,e:_uD,f:_uY,g:_v9,h:_v5},_vp=function(_vq,_vr){if(_vq<=0){if(_vq>=0){return new F(function(){return quot(_vq,_vr);});}else{if(_vr<=0){return new F(function(){return quot(_vq,_vr);});}else{return quot(_vq+1|0,_vr)-1|0;}}}else{if(_vr>=0){if(_vq>=0){return new F(function(){return quot(_vq,_vr);});}else{if(_vr<=0){return new F(function(){return quot(_vq,_vr);});}else{return quot(_vq+1|0,_vr)-1|0;}}}else{return quot(_vq-1|0,_vr)-1|0;}}},_vs=0,_vt=new T(function(){return B(_2Z(_vs));}),_vu=new T(function(){return die(_vt);}),_vv=function(_vw,_vx){var _vy=E(_vx);switch(_vy){case -1:var _vz=E(_vw);if(_vz==(-2147483648)){return E(_vu);}else{return new F(function(){return _vp(_vz,-1);});}break;case 0:return E(_33);default:return new F(function(){return _vp(_vw,_vy);});}},_vA=function(_vB,_vC){return new F(function(){return _vv(E(_vB),E(_vC));});},_vD=0,_vE=new T2(0,_vu,_vD),_vF=function(_vG,_vH){var _vI=E(_vG),_vJ=E(_vH);switch(_vJ){case -1:var _vK=E(_vI);if(_vK==(-2147483648)){return E(_vE);}else{if(_vK<=0){if(_vK>=0){var _vL=quotRemI(_vK,-1);return new T2(0,_vL.a,_vL.b);}else{var _vM=quotRemI(_vK,-1);return new T2(0,_vM.a,_vM.b);}}else{var _vN=quotRemI(_vK-1|0,-1);return new T2(0,_vN.a-1|0,(_vN.b+(-1)|0)+1|0);}}break;case 0:return E(_33);default:if(_vI<=0){if(_vI>=0){var _vO=quotRemI(_vI,_vJ);return new T2(0,_vO.a,_vO.b);}else{if(_vJ<=0){var _vP=quotRemI(_vI,_vJ);return new T2(0,_vP.a,_vP.b);}else{var _vQ=quotRemI(_vI+1|0,_vJ);return new T2(0,_vQ.a-1|0,(_vQ.b+_vJ|0)-1|0);}}}else{if(_vJ>=0){if(_vI>=0){var _vR=quotRemI(_vI,_vJ);return new T2(0,_vR.a,_vR.b);}else{if(_vJ<=0){var _vS=quotRemI(_vI,_vJ);return new T2(0,_vS.a,_vS.b);}else{var _vT=quotRemI(_vI+1|0,_vJ);return new T2(0,_vT.a-1|0,(_vT.b+_vJ|0)-1|0);}}}else{var _vU=quotRemI(_vI-1|0,_vJ);return new T2(0,_vU.a-1|0,(_vU.b+_vJ|0)+1|0);}}}},_vV=function(_vW,_vX){var _vY=_vW%_vX;if(_vW<=0){if(_vW>=0){return E(_vY);}else{if(_vX<=0){return E(_vY);}else{var _vZ=E(_vY);return (_vZ==0)?0:_vZ+_vX|0;}}}else{if(_vX>=0){if(_vW>=0){return E(_vY);}else{if(_vX<=0){return E(_vY);}else{var _w0=E(_vY);return (_w0==0)?0:_w0+_vX|0;}}}else{var _w1=E(_vY);return (_w1==0)?0:_w1+_vX|0;}}},_w2=function(_w3,_w4){var _w5=E(_w4);switch(_w5){case -1:return E(_vD);case 0:return E(_33);default:return new F(function(){return _vV(E(_w3),_w5);});}},_w6=function(_w7,_w8){var _w9=E(_w7),_wa=E(_w8);switch(_wa){case -1:var _wb=E(_w9);if(_wb==(-2147483648)){return E(_vu);}else{return new F(function(){return quot(_wb,-1);});}break;case 0:return E(_33);default:return new F(function(){return quot(_w9,_wa);});}},_wc=function(_wd,_we){var _wf=E(_wd),_wg=E(_we);switch(_wg){case -1:var _wh=E(_wf);if(_wh==(-2147483648)){return E(_vE);}else{var _wi=quotRemI(_wh,-1);return new T2(0,_wi.a,_wi.b);}break;case 0:return E(_33);default:var _wj=quotRemI(_wf,_wg);return new T2(0,_wj.a,_wj.b);}},_wk=function(_wl,_wm){var _wn=E(_wm);switch(_wn){case -1:return E(_vD);case 0:return E(_33);default:return E(_wl)%_wn;}},_wo=function(_wp){return new F(function(){return _tt(E(_wp));});},_wq=function(_wr){return new T2(0,E(B(_tt(E(_wr)))),E(_pk));},_ws=function(_wt,_wu){return imul(E(_wt),E(_wu))|0;},_wv=function(_ww,_wx){return E(_ww)+E(_wx)|0;},_wy=function(_wz,_wA){return E(_wz)-E(_wA)|0;},_wB=function(_wC){var _wD=E(_wC);return (_wD<0)? -_wD:E(_wD);},_wE=function(_wF){return new F(function(){return _3g(_wF);});},_wG=function(_wH){return  -E(_wH);},_wI=-1,_wJ=0,_wK=1,_wL=function(_wM){var _wN=E(_wM);return (_wN>=0)?(E(_wN)==0)?E(_wJ):E(_wK):E(_wI);},_wO={_:0,a:_wv,b:_wy,c:_ws,d:_wG,e:_wB,f:_wL,g:_wE},_wP=function(_wQ,_wR){return E(_wQ)==E(_wR);},_wS=function(_wT,_wU){return E(_wT)!=E(_wU);},_wV=new T2(0,_wP,_wS),_wW=function(_wX,_wY){var _wZ=E(_wX),_x0=E(_wY);return (_wZ>_x0)?E(_wZ):E(_x0);},_x1=function(_x2,_x3){var _x4=E(_x2),_x5=E(_x3);return (_x4>_x5)?E(_x5):E(_x4);},_x6=function(_x7,_x8){return (_x7>=_x8)?(_x7!=_x8)?2:1:0;},_x9=function(_xa,_xb){return new F(function(){return _x6(E(_xa),E(_xb));});},_xc=function(_xd,_xe){return E(_xd)>=E(_xe);},_xf=function(_xg,_xh){return E(_xg)>E(_xh);},_xi=function(_xj,_xk){return E(_xj)<=E(_xk);},_xl=function(_xm,_xn){return E(_xm)<E(_xn);},_xo={_:0,a:_wV,b:_x9,c:_xl,d:_xi,e:_xf,f:_xc,g:_wW,h:_x1},_xp=new T3(0,_wO,_xo,_wq),_xq={_:0,a:_xp,b:_vo,c:_w6,d:_wk,e:_vA,f:_w2,g:_wc,h:_vF,i:_wo},_xr=new T1(0,2),_xs=function(_xt,_xu){while(1){var _xv=E(_xt);if(!_xv._){var _xw=_xv.a,_xx=E(_xu);if(!_xx._){var _xy=_xx.a;if(!(imul(_xw,_xy)|0)){return new T1(0,imul(_xw,_xy)|0);}else{_xt=new T1(1,I_fromInt(_xw));_xu=new T1(1,I_fromInt(_xy));continue;}}else{_xt=new T1(1,I_fromInt(_xw));_xu=_xx;continue;}}else{var _xz=E(_xu);if(!_xz._){_xt=_xv;_xu=new T1(1,I_fromInt(_xz.a));continue;}else{return new T1(1,I_mul(_xv.a,_xz.a));}}}},_xA=function(_xB,_xC,_xD){while(1){if(!(_xC%2)){var _xE=B(_xs(_xB,_xB)),_xF=quot(_xC,2);_xB=_xE;_xC=_xF;continue;}else{var _xG=E(_xC);if(_xG==1){return new F(function(){return _xs(_xB,_xD);});}else{var _xE=B(_xs(_xB,_xB)),_xH=B(_xs(_xB,_xD));_xB=_xE;_xC=quot(_xG-1|0,2);_xD=_xH;continue;}}}},_xI=function(_xJ,_xK){while(1){if(!(_xK%2)){var _xL=B(_xs(_xJ,_xJ)),_xM=quot(_xK,2);_xJ=_xL;_xK=_xM;continue;}else{var _xN=E(_xK);if(_xN==1){return E(_xJ);}else{return new F(function(){return _xA(B(_xs(_xJ,_xJ)),quot(_xN-1|0,2),_xJ);});}}}},_xO=function(_xP){return E(E(_xP).b);},_xQ=function(_xR){return E(E(_xR).c);},_xS=new T1(0,0),_xT=function(_xU){return E(E(_xU).d);},_xV=function(_xW,_xX){var _xY=B(_uu(_xW)),_xZ=new T(function(){return B(_uw(_xY));}),_y0=new T(function(){return B(A3(_xT,_xW,_xX,new T(function(){return B(A2(_7U,_xZ,_pu));})));});return new F(function(){return A3(_of,B(_o1(B(_xO(_xY)))),_y0,new T(function(){return B(A2(_7U,_xZ,_xS));}));});},_y1=new T(function(){return B(unCStr("Negative exponent"));}),_y2=new T(function(){return B(err(_y1));}),_y3=function(_y4){return E(E(_y4).c);},_y5=function(_y6,_y7,_y8,_y9){var _ya=B(_uu(_y7)),_yb=new T(function(){return B(_uw(_ya));}),_yc=B(_xO(_ya));if(!B(A3(_xQ,_yc,_y9,new T(function(){return B(A2(_7U,_yb,_xS));})))){if(!B(A3(_of,B(_o1(_yc)),_y9,new T(function(){return B(A2(_7U,_yb,_xS));})))){var _yd=new T(function(){return B(A2(_7U,_yb,_pu));}),_ye=new T(function(){return B(A2(_7U,_yb,_pk));}),_yf=B(_o1(_yc)),_yg=function(_yh,_yi,_yj){while(1){var _yk=B((function(_yl,_ym,_yn){if(!B(_xV(_y7,_ym))){if(!B(A3(_of,_yf,_ym,_ye))){var _yo=new T(function(){return B(A3(_y3,_y7,new T(function(){return B(A3(_bt,_yb,_ym,_ye));}),_yd));});_yh=new T(function(){return B(A3(_bh,_y6,_yl,_yl));});_yi=_yo;_yj=new T(function(){return B(A3(_bh,_y6,_yl,_yn));});return __continue;}else{return new F(function(){return A3(_bh,_y6,_yl,_yn);});}}else{var _yp=_yn;_yh=new T(function(){return B(A3(_bh,_y6,_yl,_yl));});_yi=new T(function(){return B(A3(_y3,_y7,_ym,_yd));});_yj=_yp;return __continue;}})(_yh,_yi,_yj));if(_yk!=__continue){return _yk;}}},_yq=function(_yr,_ys){while(1){var _yt=B((function(_yu,_yv){if(!B(_xV(_y7,_yv))){if(!B(A3(_of,_yf,_yv,_ye))){var _yw=new T(function(){return B(A3(_y3,_y7,new T(function(){return B(A3(_bt,_yb,_yv,_ye));}),_yd));});return new F(function(){return _yg(new T(function(){return B(A3(_bh,_y6,_yu,_yu));}),_yw,_yu);});}else{return E(_yu);}}else{_yr=new T(function(){return B(A3(_bh,_y6,_yu,_yu));});_ys=new T(function(){return B(A3(_y3,_y7,_yv,_yd));});return __continue;}})(_yr,_ys));if(_yt!=__continue){return _yt;}}};return new F(function(){return _yq(_y8,_y9);});}else{return new F(function(){return A2(_7U,_y6,_pk);});}}else{return E(_y2);}},_yx=new T(function(){return B(err(_y1));}),_yy=function(_yz,_yA){var _yB=B(_tq(_yA)),_yC=_yB.a,_yD=_yB.b,_yE=new T(function(){return B(_uw(new T(function(){return B(_uu(_yz));})));});if(_yD<0){var _yF= -_yD;if(_yF>=0){var _yG=E(_yF);if(!_yG){var _yH=E(_pk);}else{var _yH=B(_xI(_xr,_yG));}if(!B(_38(_yH,_3B))){var _yI=B(_3s(_yC,_yH));return new T2(0,new T(function(){return B(A2(_7U,_yE,_yI.a));}),new T(function(){return B(_34(_yI.b,_yD));}));}else{return E(_33);}}else{return E(_yx);}}else{var _yJ=new T(function(){var _yK=new T(function(){return B(_y5(_yE,_xq,new T(function(){return B(A2(_7U,_yE,_xr));}),_yD));});return B(A3(_bh,_yE,new T(function(){return B(A2(_7U,_yE,_yC));}),_yK));});return new T2(0,_yJ,_6q);}},_yL=function(_yM,_yN){var _yO=B(_yy(_yM,E(_yN))),_yP=_yO.a;if(E(_yO.b)<=0){return E(_yP);}else{var _yQ=B(_uw(B(_uu(_yM))));return new F(function(){return A3(_6Q,_yQ,_yP,new T(function(){return B(A2(_7U,_yQ,_1U));}));});}},_yR=function(_yS,_yT){var _yU=B(_yy(_yS,E(_yT))),_yV=_yU.a;if(E(_yU.b)>=0){return E(_yV);}else{var _yW=B(_uw(B(_uu(_yS))));return new F(function(){return A3(_bt,_yW,_yV,new T(function(){return B(A2(_7U,_yW,_1U));}));});}},_yX=function(_yY,_yZ){var _z0=B(_yy(_yY,E(_yZ)));return new T2(0,_z0.a,_z0.b);},_z1=function(_z2,_z3){var _z4=B(_yy(_z2,_z3)),_z5=_z4.a,_z6=E(_z4.b),_z7=new T(function(){var _z8=B(_uw(B(_uu(_z2))));if(_z6>=0){return B(A3(_6Q,_z8,_z5,new T(function(){return B(A2(_7U,_z8,_1U));})));}else{return B(A3(_bt,_z8,_z5,new T(function(){return B(A2(_7U,_z8,_1U));})));}}),_z9=function(_za){var _zb=_za-0.5;return (_zb>=0)?(E(_zb)==0)?(!B(_xV(_z2,_z5)))?E(_z7):E(_z5):E(_z7):E(_z5);},_zc=E(_z6);if(!_zc){return new F(function(){return _z9(0);});}else{if(_zc<=0){var _zd= -_zc-0.5;return (_zd>=0)?(E(_zd)==0)?(!B(_xV(_z2,_z5)))?E(_z7):E(_z5):E(_z7):E(_z5);}else{return new F(function(){return _z9(_zc);});}}},_ze=function(_zf,_zg){return new F(function(){return _z1(_zf,E(_zg));});},_zh=function(_zi,_zj){return E(B(_yy(_zi,E(_zj))).a);},_zk={_:0,a:_ut,b:_lp,c:_yX,d:_zh,e:_ze,f:_yL,g:_yR},_zl=new T1(0,1),_zm=function(_zn,_zo){var _zp=E(_zn);return new T2(0,_zp,new T(function(){var _zq=B(_zm(B(_3j(_zp,_zo)),_zo));return new T2(1,_zq.a,_zq.b);}));},_zr=function(_zs){var _zt=B(_zm(_zs,_zl));return new T2(1,_zt.a,_zt.b);},_zu=function(_zv,_zw){var _zx=B(_zm(_zv,new T(function(){return B(_5E(_zw,_zv));})));return new T2(1,_zx.a,_zx.b);},_zy=new T1(0,0),_zz=function(_zA,_zB){var _zC=E(_zA);if(!_zC._){var _zD=_zC.a,_zE=E(_zB);return (_zE._==0)?_zD>=_zE.a:I_compareInt(_zE.a,_zD)<=0;}else{var _zF=_zC.a,_zG=E(_zB);return (_zG._==0)?I_compareInt(_zF,_zG.a)>=0:I_compare(_zF,_zG.a)>=0;}},_zH=function(_zI,_zJ,_zK){if(!B(_zz(_zJ,_zy))){var _zL=function(_zM){return (!B(_3V(_zM,_zK)))?new T2(1,_zM,new T(function(){return B(_zL(B(_3j(_zM,_zJ))));})):__Z;};return new F(function(){return _zL(_zI);});}else{var _zN=function(_zO){return (!B(_3M(_zO,_zK)))?new T2(1,_zO,new T(function(){return B(_zN(B(_3j(_zO,_zJ))));})):__Z;};return new F(function(){return _zN(_zI);});}},_zP=function(_zQ,_zR,_zS){return new F(function(){return _zH(_zQ,B(_5E(_zR,_zQ)),_zS);});},_zT=function(_zU,_zV){return new F(function(){return _zH(_zU,_zl,_zV);});},_zW=function(_zX){return new F(function(){return _3g(_zX);});},_zY=function(_zZ){return new F(function(){return _5E(_zZ,_zl);});},_A0=function(_A1){return new F(function(){return _3j(_A1,_zl);});},_A2=function(_A3){return new F(function(){return _tt(E(_A3));});},_A4={_:0,a:_A0,b:_zY,c:_A2,d:_zW,e:_zr,f:_zu,g:_zT,h:_zP},_A5=function(_A6,_A7){while(1){var _A8=E(_A6);if(!_A8._){var _A9=E(_A8.a);if(_A9==(-2147483648)){_A6=new T1(1,I_fromInt(-2147483648));continue;}else{var _Aa=E(_A7);if(!_Aa._){return new T1(0,B(_vp(_A9,_Aa.a)));}else{_A6=new T1(1,I_fromInt(_A9));_A7=_Aa;continue;}}}else{var _Ab=_A8.a,_Ac=E(_A7);return (_Ac._==0)?new T1(1,I_div(_Ab,I_fromInt(_Ac.a))):new T1(1,I_div(_Ab,_Ac.a));}}},_Ad=function(_Ae,_Af){if(!B(_38(_Af,_xS))){return new F(function(){return _A5(_Ae,_Af);});}else{return E(_33);}},_Ag=function(_Ah,_Ai){while(1){var _Aj=E(_Ah);if(!_Aj._){var _Ak=E(_Aj.a);if(_Ak==(-2147483648)){_Ah=new T1(1,I_fromInt(-2147483648));continue;}else{var _Al=E(_Ai);if(!_Al._){var _Am=_Al.a;return new T2(0,new T1(0,B(_vp(_Ak,_Am))),new T1(0,B(_vV(_Ak,_Am))));}else{_Ah=new T1(1,I_fromInt(_Ak));_Ai=_Al;continue;}}}else{var _An=E(_Ai);if(!_An._){_Ah=_Aj;_Ai=new T1(1,I_fromInt(_An.a));continue;}else{var _Ao=I_divMod(_Aj.a,_An.a);return new T2(0,new T1(1,_Ao.a),new T1(1,_Ao.b));}}}},_Ap=function(_Aq,_Ar){if(!B(_38(_Ar,_xS))){var _As=B(_Ag(_Aq,_Ar));return new T2(0,_As.a,_As.b);}else{return E(_33);}},_At=function(_Au,_Av){while(1){var _Aw=E(_Au);if(!_Aw._){var _Ax=E(_Aw.a);if(_Ax==(-2147483648)){_Au=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ay=E(_Av);if(!_Ay._){return new T1(0,B(_vV(_Ax,_Ay.a)));}else{_Au=new T1(1,I_fromInt(_Ax));_Av=_Ay;continue;}}}else{var _Az=_Aw.a,_AA=E(_Av);return (_AA._==0)?new T1(1,I_mod(_Az,I_fromInt(_AA.a))):new T1(1,I_mod(_Az,_AA.a));}}},_AB=function(_AC,_AD){if(!B(_38(_AD,_xS))){return new F(function(){return _At(_AC,_AD);});}else{return E(_33);}},_AE=function(_AF,_AG){while(1){var _AH=E(_AF);if(!_AH._){var _AI=E(_AH.a);if(_AI==(-2147483648)){_AF=new T1(1,I_fromInt(-2147483648));continue;}else{var _AJ=E(_AG);if(!_AJ._){return new T1(0,quot(_AI,_AJ.a));}else{_AF=new T1(1,I_fromInt(_AI));_AG=_AJ;continue;}}}else{var _AK=_AH.a,_AL=E(_AG);return (_AL._==0)?new T1(0,I_toInt(I_quot(_AK,I_fromInt(_AL.a)))):new T1(1,I_quot(_AK,_AL.a));}}},_AM=function(_AN,_AO){if(!B(_38(_AO,_xS))){return new F(function(){return _AE(_AN,_AO);});}else{return E(_33);}},_AP=function(_AQ,_AR){if(!B(_38(_AR,_xS))){var _AS=B(_3s(_AQ,_AR));return new T2(0,_AS.a,_AS.b);}else{return E(_33);}},_AT=function(_AU,_AV){while(1){var _AW=E(_AU);if(!_AW._){var _AX=E(_AW.a);if(_AX==(-2147483648)){_AU=new T1(1,I_fromInt(-2147483648));continue;}else{var _AY=E(_AV);if(!_AY._){return new T1(0,_AX%_AY.a);}else{_AU=new T1(1,I_fromInt(_AX));_AV=_AY;continue;}}}else{var _AZ=_AW.a,_B0=E(_AV);return (_B0._==0)?new T1(1,I_rem(_AZ,I_fromInt(_B0.a))):new T1(1,I_rem(_AZ,_B0.a));}}},_B1=function(_B2,_B3){if(!B(_38(_B3,_xS))){return new F(function(){return _AT(_B2,_B3);});}else{return E(_33);}},_B4=function(_B5){return E(_B5);},_B6=function(_B7){return E(_B7);},_B8=function(_B9){var _Ba=E(_B9);if(!_Ba._){var _Bb=E(_Ba.a);return (_Bb==(-2147483648))?E(_6i):(_Bb<0)?new T1(0, -_Bb):E(_Ba);}else{var _Bc=_Ba.a;return (I_compareInt(_Bc,0)>=0)?E(_Ba):new T1(1,I_negate(_Bc));}},_Bd=new T1(0,0),_Be=new T1(0,-1),_Bf=function(_Bg){var _Bh=E(_Bg);if(!_Bh._){var _Bi=_Bh.a;return (_Bi>=0)?(E(_Bi)==0)?E(_Bd):E(_3U):E(_Be);}else{var _Bj=I_compareInt(_Bh.a,0);return (_Bj<=0)?(E(_Bj)==0)?E(_Bd):E(_Be):E(_3U);}},_Bk={_:0,a:_3j,b:_5E,c:_xs,d:_6j,e:_B8,f:_Bf,g:_B6},_Bl=function(_Bm,_Bn){var _Bo=E(_Bm);if(!_Bo._){var _Bp=_Bo.a,_Bq=E(_Bn);return (_Bq._==0)?_Bp!=_Bq.a:(I_compareInt(_Bq.a,_Bp)==0)?false:true;}else{var _Br=_Bo.a,_Bs=E(_Bn);return (_Bs._==0)?(I_compareInt(_Br,_Bs.a)==0)?false:true:(I_compare(_Br,_Bs.a)==0)?false:true;}},_Bt=new T2(0,_38,_Bl),_Bu=function(_Bv,_Bw){return (!B(_5p(_Bv,_Bw)))?E(_Bv):E(_Bw);},_Bx=function(_By,_Bz){return (!B(_5p(_By,_Bz)))?E(_Bz):E(_By);},_BA={_:0,a:_Bt,b:_1V,c:_3V,d:_5p,e:_3M,f:_zz,g:_Bu,h:_Bx},_BB=function(_BC){return new T2(0,E(_BC),E(_pk));},_BD=new T3(0,_Bk,_BA,_BB),_BE={_:0,a:_BD,b:_A4,c:_AM,d:_B1,e:_Ad,f:_AB,g:_AP,h:_Ap,i:_B4},_BF=function(_BG){return E(E(_BG).b);},_BH=function(_BI){return E(E(_BI).g);},_BJ=new T1(0,1),_BK=function(_BL,_BM,_BN){var _BO=B(_BF(_BL)),_BP=B(_82(_BO)),_BQ=new T(function(){var _BR=new T(function(){var _BS=new T(function(){var _BT=new T(function(){return B(A3(_BH,_BL,_BE,new T(function(){return B(A3(_cg,_BO,_BM,_BN));})));});return B(A2(_7U,_BP,_BT));}),_BU=new T(function(){return B(A2(_6S,_BP,new T(function(){return B(A2(_7U,_BP,_BJ));})));});return B(A3(_bh,_BP,_BU,_BS));});return B(A3(_bh,_BP,_BR,_BN));});return new F(function(){return A3(_6Q,_BP,_BM,_BQ);});},_BV=1.5707963267948966,_BW=function(_BX){return 0.2/Math.cos(B(_BK(_zk,_BX,_BV))-0.7853981633974483);},_BY=new T(function(){var _BZ=B(_s5(_BW,1.2,_tp,_tp,_to,_tp,_tp,_tp,_tp,_tp,_to,_to,_to));return {_:0,a:E(_BZ.a),b:E(_BZ.b),c:E(_BZ.c),d:E(_BZ.d),e:E(_BZ.e),f:E(_BZ.f),g:E(_BZ.g),h:_BZ.h,i:_BZ.i};}),_C0=0,_C1=0.3,_C2=function(_C3){return E(_C1);},_C4=new T(function(){var _C5=B(_s5(_C2,1.2,_to,_tp,_to,_tp,_tp,_tp,_tp,_tp,_to,_to,_to));return {_:0,a:E(_C5.a),b:E(_C5.b),c:E(_C5.c),d:E(_C5.d),e:E(_C5.e),f:E(_C5.f),g:E(_C5.g),h:_C5.h,i:_C5.i};}),_C6=new T(function(){var _C7=B(_s5(_C2,1.2,_to,_to,_tp,_tp,_tp,_tp,_tp,_tp,_to,_to,_to));return {_:0,a:E(_C7.a),b:E(_C7.b),c:E(_C7.c),d:E(_C7.d),e:E(_C7.e),f:E(_C7.f),g:E(_C7.g),h:_C7.h,i:_C7.i};}),_C8=2,_C9=function(_Ca){return 0.3/Math.cos(B(_BK(_zk,_Ca,_BV))-0.7853981633974483);},_Cb=new T(function(){var _Cc=B(_s5(_C9,1.2,_C8,_to,_to,_tp,_tp,_tp,_tp,_tp,_to,_to,_to));return {_:0,a:E(_Cc.a),b:E(_Cc.b),c:E(_Cc.c),d:E(_Cc.d),e:E(_Cc.e),f:E(_Cc.f),g:E(_Cc.g),h:_Cc.h,i:_Cc.i};}),_Cd=0.5,_Ce=new T(function(){var _Cf=B(_s5(_C2,1.2,_tp,_to,_Cd,_tp,_tp,_tp,_tp,_tp,_to,_to,_to));return {_:0,a:E(_Cf.a),b:E(_Cf.b),c:E(_Cf.c),d:E(_Cf.d),e:E(_Cf.e),f:E(_Cf.f),g:E(_Cf.g),h:_Cf.h,i:_Cf.i};}),_Cg=new T2(1,_Ce,_w),_Ch=new T2(1,_Cb,_Cg),_Ci=new T2(1,_C6,_Ch),_Cj=new T2(1,_C4,_Ci),_Ck=new T2(1,_BY,_Cj),_Cl=new T(function(){return B(unCStr("Negative range size"));}),_Cm=new T(function(){return B(err(_Cl));}),_Cn=function(_){var _Co=B(_kf(_Ck,0))-1|0,_Cp=function(_Cq){if(_Cq>=0){var _Cr=newArr(_Cq,_kl),_Cs=_Cr,_Ct=E(_Cq);if(!_Ct){return new T4(0,E(_C0),E(_Co),0,_Cs);}else{var _Cu=function(_Cv,_Cw,_){while(1){var _Cx=E(_Cv);if(!_Cx._){return E(_);}else{var _=_Cs[_Cw]=_Cx.a;if(_Cw!=(_Ct-1|0)){var _Cy=_Cw+1|0;_Cv=_Cx.b;_Cw=_Cy;continue;}else{return E(_);}}}},_=B((function(_Cz,_CA,_CB,_){var _=_Cs[_CB]=_Cz;if(_CB!=(_Ct-1|0)){return new F(function(){return _Cu(_CA,_CB+1|0,_);});}else{return E(_);}})(_BY,_Cj,0,_));return new T4(0,E(_C0),E(_Co),_Ct,_Cs);}}else{return E(_Cm);}};if(0>_Co){return new F(function(){return _Cp(0);});}else{return new F(function(){return _Cp(_Co+1|0);});}},_CC=function(_CD){var _CE=B(A1(_CD,_));return E(_CE);},_CF=new T(function(){return B(_CC(_Cn));}),_CG="outline",_CH="polygon",_CI=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_CJ=new T(function(){return B(err(_CI));}),_CK=new T(function(){return eval("__strict(drawObjects)");}),_CL=new T(function(){return eval("__strict(draw)");}),_CM=function(_CN,_CO){var _CP=jsShowI(_CN);return new F(function(){return _n(fromJSStr(_CP),_CO);});},_CQ=function(_CR,_CS,_CT){if(_CS>=0){return new F(function(){return _CM(_CS,_CT);});}else{if(_CR<=6){return new F(function(){return _CM(_CS,_CT);});}else{return new T2(1,_79,new T(function(){var _CU=jsShowI(_CS);return B(_n(fromJSStr(_CU),new T2(1,_78,_CT)));}));}}},_CV=new T(function(){return B(unCStr(")"));}),_CW=function(_CX,_CY){var _CZ=new T(function(){var _D0=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_CQ(0,_CX,_w)),_CV));})));},1);return B(_n(B(_CQ(0,_CY,_w)),_D0));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_CZ)));});},_D1=new T2(1,_mC,_w),_D2=function(_D3){return E(_D3);},_D4=function(_D5){return E(_D5);},_D6=function(_D7,_D8){return E(_D8);},_D9=function(_Da,_Db){return E(_Da);},_Dc=function(_Dd){return E(_Dd);},_De=new T2(0,_Dc,_D9),_Df=function(_Dg,_Dh){return E(_Dg);},_Di=new T5(0,_De,_D4,_D2,_D6,_Df),_Dj="flipped2",_Dk="flipped1",_Dl="c1y",_Dm="c1x",_Dn="w2z",_Do="w2y",_Dp="w2x",_Dq="w1z",_Dr="w1y",_Ds="w1x",_Dt="d2z",_Du="d2y",_Dv="d2x",_Dw="d1z",_Dx="d1y",_Dy="d1x",_Dz="c2y",_DA="c2x",_DB=function(_DC,_){var _DD=__get(_DC,E(_Ds)),_DE=__get(_DC,E(_Dr)),_DF=__get(_DC,E(_Dq)),_DG=__get(_DC,E(_Dp)),_DH=__get(_DC,E(_Do)),_DI=__get(_DC,E(_Dn)),_DJ=__get(_DC,E(_Dm)),_DK=__get(_DC,E(_Dl)),_DL=__get(_DC,E(_DA)),_DM=__get(_DC,E(_Dz)),_DN=__get(_DC,E(_Dy)),_DO=__get(_DC,E(_Dx)),_DP=__get(_DC,E(_Dw)),_DQ=__get(_DC,E(_Dv)),_DR=__get(_DC,E(_Du)),_DS=__get(_DC,E(_Dt)),_DT=__get(_DC,E(_Dk)),_DU=__get(_DC,E(_Dj));return {_:0,a:E(new T3(0,E(_DD),E(_DE),E(_DF))),b:E(new T3(0,E(_DG),E(_DH),E(_DI))),c:E(new T2(0,E(_DJ),E(_DK))),d:E(new T2(0,E(_DL),E(_DM))),e:E(new T3(0,E(_DN),E(_DO),E(_DP))),f:E(new T3(0,E(_DQ),E(_DR),E(_DS))),g:E(_DT),h:E(_DU)};},_DV=function(_DW,_){var _DX=E(_DW);if(!_DX._){return _w;}else{var _DY=B(_DB(E(_DX.a),_)),_DZ=B(_DV(_DX.b,_));return new T2(1,_DY,_DZ);}},_E0=function(_E1){var _E2=E(_E1);return (E(_E2.b)-E(_E2.a)|0)+1|0;},_E3=function(_E4,_E5){var _E6=E(_E4),_E7=E(_E5);return (E(_E6.a)>_E7)?false:_E7<=E(_E6.b);},_E8=function(_E9){return new F(function(){return _CQ(0,E(_E9),_w);});},_Ea=function(_Eb,_Ec,_Ed){return new F(function(){return _CQ(E(_Eb),E(_Ec),_Ed);});},_Ee=function(_Ef,_Eg){return new F(function(){return _CQ(0,E(_Ef),_Eg);});},_Eh=function(_Ei,_Ej){return new F(function(){return _2J(_Ee,_Ei,_Ej);});},_Ek=new T3(0,_Ea,_E8,_Eh),_El=0,_Em=function(_En,_Eo,_Ep){return new F(function(){return A1(_En,new T2(1,_2G,new T(function(){return B(A1(_Eo,_Ep));})));});},_Eq=new T(function(){return B(unCStr("foldr1"));}),_Er=new T(function(){return B(_oK(_Eq));}),_Es=function(_Et,_Eu){var _Ev=E(_Eu);if(!_Ev._){return E(_Er);}else{var _Ew=_Ev.a,_Ex=E(_Ev.b);if(!_Ex._){return E(_Ew);}else{return new F(function(){return A2(_Et,_Ew,new T(function(){return B(_Es(_Et,_Ex));}));});}}},_Ey=new T(function(){return B(unCStr(" out of range "));}),_Ez=new T(function(){return B(unCStr("}.index: Index "));}),_EA=new T(function(){return B(unCStr("Ix{"));}),_EB=new T2(1,_78,_w),_EC=new T2(1,_78,_EB),_ED=0,_EE=function(_EF){return E(E(_EF).a);},_EG=function(_EH,_EI,_EJ,_EK,_EL){var _EM=new T(function(){var _EN=new T(function(){var _EO=new T(function(){var _EP=new T(function(){var _EQ=new T(function(){return B(A3(_Es,_Em,new T2(1,new T(function(){return B(A3(_EE,_EJ,_ED,_EK));}),new T2(1,new T(function(){return B(A3(_EE,_EJ,_ED,_EL));}),_w)),_EC));});return B(_n(_Ey,new T2(1,_79,new T2(1,_79,_EQ))));});return B(A(_EE,[_EJ,_El,_EI,new T2(1,_78,_EP)]));});return B(_n(_Ez,new T2(1,_79,_EO)));},1);return B(_n(_EH,_EN));},1);return new F(function(){return err(B(_n(_EA,_EM)));});},_ER=function(_ES,_ET,_EU,_EV,_EW){return new F(function(){return _EG(_ES,_ET,_EW,_EU,_EV);});},_EX=function(_EY,_EZ,_F0,_F1){var _F2=E(_F0);return new F(function(){return _ER(_EY,_EZ,_F2.a,_F2.b,_F1);});},_F3=function(_F4,_F5,_F6,_F7){return new F(function(){return _EX(_F7,_F6,_F5,_F4);});},_F8=new T(function(){return B(unCStr("Int"));}),_F9=function(_Fa,_Fb){return new F(function(){return _F3(_Ek,_Fb,_Fa,_F8);});},_Fc=function(_Fd,_Fe){var _Ff=E(_Fd),_Fg=E(_Ff.a),_Fh=E(_Fe);if(_Fg>_Fh){return new F(function(){return _F9(_Fh,_Ff);});}else{if(_Fh>E(_Ff.b)){return new F(function(){return _F9(_Fh,_Ff);});}else{return _Fh-_Fg|0;}}},_Fi=function(_Fj){var _Fk=E(_Fj);return new F(function(){return _v9(_Fk.a,_Fk.b);});},_Fl=function(_Fm){var _Fn=E(_Fm),_Fo=E(_Fn.a),_Fp=E(_Fn.b);return (_Fo>_Fp)?E(_El):(_Fp-_Fo|0)+1|0;},_Fq=function(_Fr,_Fs){return new F(function(){return _wy(_Fs,E(_Fr).a);});},_Ft={_:0,a:_xo,b:_Fi,c:_Fc,d:_Fq,e:_E3,f:_Fl,g:_E0},_Fu=function(_Fv,_Fw,_){while(1){var _Fx=B((function(_Fy,_Fz,_){var _FA=E(_Fy);if(!_FA._){return new T2(0,_mC,_Fz);}else{var _FB=B(A2(_FA.a,_Fz,_));_Fv=_FA.b;_Fw=new T(function(){return E(E(_FB).b);});return __continue;}})(_Fv,_Fw,_));if(_Fx!=__continue){return _Fx;}}},_FC=function(_FD,_FE){return new T2(1,_FD,_FE);},_FF=function(_FG,_FH){var _FI=E(_FH);return new T2(0,_FI.a,_FI.b);},_FJ=function(_FK){return E(E(_FK).f);},_FL=function(_FM,_FN,_FO){var _FP=E(_FN),_FQ=_FP.a,_FR=_FP.b,_FS=function(_){var _FT=B(A2(_FJ,_FM,_FP));if(_FT>=0){var _FU=newArr(_FT,_kl),_FV=_FU,_FW=E(_FT);if(!_FW){return new T(function(){return new T4(0,E(_FQ),E(_FR),0,_FV);});}else{var _FX=function(_FY,_FZ,_){while(1){var _G0=E(_FY);if(!_G0._){return E(_);}else{var _=_FV[_FZ]=_G0.a;if(_FZ!=(_FW-1|0)){var _G1=_FZ+1|0;_FY=_G0.b;_FZ=_G1;continue;}else{return E(_);}}}},_=B(_FX(_FO,0,_));return new T(function(){return new T4(0,E(_FQ),E(_FR),_FW,_FV);});}}else{return E(_Cm);}};return new F(function(){return _CC(_FS);});},_G2=function(_G3,_G4,_G5,_G6){var _G7=new T(function(){var _G8=E(_G6),_G9=_G8.c-1|0,_Ga=new T(function(){return B(A2(_g0,_G4,_w));});if(0<=_G9){var _Gb=new T(function(){return B(_84(_G4));}),_Gc=function(_Gd){var _Ge=new T(function(){var _Gf=new T(function(){return B(A1(_G5,new T(function(){return E(_G8.d[_Gd]);})));});return B(A3(_86,_Gb,_FC,_Gf));});return new F(function(){return A3(_ci,_G4,_Ge,new T(function(){if(_Gd!=_G9){return B(_Gc(_Gd+1|0));}else{return E(_Ga);}}));});};return B(_Gc(0));}else{return E(_Ga);}}),_Gg=new T(function(){return B(_FF(_G3,_G6));});return new F(function(){return A3(_86,B(_84(_G4)),function(_Gh){return new F(function(){return _FL(_G3,_Gg,_Gh);});},_G7);});},_Gi=function(_Gj,_Gk,_Gl,_Gm,_Gn,_Go,_Gp,_Gq,_Gr){var _Gs=B(_bh(_Gj));return new T2(0,new T3(0,E(B(A1(B(A1(_Gs,_Gk)),_Go))),E(B(A1(B(A1(_Gs,_Gl)),_Gp))),E(B(A1(B(A1(_Gs,_Gm)),_Gq)))),B(A1(B(A1(_Gs,_Gn)),_Gr)));},_Gt=function(_Gu,_Gv,_Gw,_Gx,_Gy,_Gz,_GA,_GB,_GC){var _GD=B(_6Q(_Gu));return new T2(0,new T3(0,E(B(A1(B(A1(_GD,_Gv)),_Gz))),E(B(A1(B(A1(_GD,_Gw)),_GA))),E(B(A1(B(A1(_GD,_Gx)),_GB)))),B(A1(B(A1(_GD,_Gy)),_GC)));},_GE=1.0e-2,_GF=function(_GG,_GH,_GI,_GJ,_GK,_GL,_GM,_GN,_GO,_GP,_GQ,_GR,_GS,_GT,_GU,_GV,_GW){var _GX=B(_Gi(_ll,_GN,_GO,_GP,_GQ,_GE,_GE,_GE,_GE)),_GY=E(_GX.a),_GZ=B(_Gt(_ll,_GJ,_GK,_GL,_GM,_GY.a,_GY.b,_GY.c,_GX.b)),_H0=E(_GZ.a);return new F(function(){return _rl(_GG,_GH,_GI,_H0.a,_H0.b,_H0.c,_GZ.b,_GN,_GO,_GP,_GQ,_GR,_GS,_GT,_GU,_GV,_GW);});},_H1=function(_H2){var _H3=E(_H2),_H4=E(_H3.d),_H5=E(_H4.a),_H6=E(_H3.e),_H7=E(_H6.a),_H8=E(_H3.f),_H9=B(_GF(_H3.a,_H3.b,_H3.c,_H5.a,_H5.b,_H5.c,_H4.b,_H7.a,_H7.b,_H7.c,_H6.b,_H8.a,_H8.b,_H8.c,_H3.g,_H3.h,_H3.i));return {_:0,a:E(_H9.a),b:E(_H9.b),c:E(_H9.c),d:E(_H9.d),e:E(_H9.e),f:E(_H9.f),g:E(_H9.g),h:_H9.h,i:_H9.i};},_Ha=function(_Hb,_Hc,_Hd,_He,_Hf,_Hg,_Hh,_Hi,_Hj){var _Hk=B(_82(B(_80(_Hb))));return new F(function(){return A3(_6Q,_Hk,new T(function(){return B(_bj(_Hb,_Hc,_Hd,_He,_Hg,_Hh,_Hi));}),new T(function(){return B(A3(_bh,_Hk,_Hf,_Hj));}));});},_Hl=new T(function(){return B(unCStr("base"));}),_Hm=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Hn=new T(function(){return B(unCStr("IOException"));}),_Ho=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Hl,_Hm,_Hn),_Hp=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Ho,_w,_w),_Hq=function(_Hr){return E(_Hp);},_Hs=function(_Ht){var _Hu=E(_Ht);return new F(function(){return _2g(B(_2e(_Hu.a)),_Hq,_Hu.b);});},_Hv=new T(function(){return B(unCStr(": "));}),_Hw=new T(function(){return B(unCStr(")"));}),_Hx=new T(function(){return B(unCStr(" ("));}),_Hy=new T(function(){return B(unCStr("interrupted"));}),_Hz=new T(function(){return B(unCStr("system error"));}),_HA=new T(function(){return B(unCStr("unsatisified constraints"));}),_HB=new T(function(){return B(unCStr("user error"));}),_HC=new T(function(){return B(unCStr("permission denied"));}),_HD=new T(function(){return B(unCStr("illegal operation"));}),_HE=new T(function(){return B(unCStr("end of file"));}),_HF=new T(function(){return B(unCStr("resource exhausted"));}),_HG=new T(function(){return B(unCStr("resource busy"));}),_HH=new T(function(){return B(unCStr("does not exist"));}),_HI=new T(function(){return B(unCStr("already exists"));}),_HJ=new T(function(){return B(unCStr("resource vanished"));}),_HK=new T(function(){return B(unCStr("timeout"));}),_HL=new T(function(){return B(unCStr("unsupported operation"));}),_HM=new T(function(){return B(unCStr("hardware fault"));}),_HN=new T(function(){return B(unCStr("inappropriate type"));}),_HO=new T(function(){return B(unCStr("invalid argument"));}),_HP=new T(function(){return B(unCStr("failed"));}),_HQ=new T(function(){return B(unCStr("protocol error"));}),_HR=function(_HS,_HT){switch(E(_HS)){case 0:return new F(function(){return _n(_HI,_HT);});break;case 1:return new F(function(){return _n(_HH,_HT);});break;case 2:return new F(function(){return _n(_HG,_HT);});break;case 3:return new F(function(){return _n(_HF,_HT);});break;case 4:return new F(function(){return _n(_HE,_HT);});break;case 5:return new F(function(){return _n(_HD,_HT);});break;case 6:return new F(function(){return _n(_HC,_HT);});break;case 7:return new F(function(){return _n(_HB,_HT);});break;case 8:return new F(function(){return _n(_HA,_HT);});break;case 9:return new F(function(){return _n(_Hz,_HT);});break;case 10:return new F(function(){return _n(_HQ,_HT);});break;case 11:return new F(function(){return _n(_HP,_HT);});break;case 12:return new F(function(){return _n(_HO,_HT);});break;case 13:return new F(function(){return _n(_HN,_HT);});break;case 14:return new F(function(){return _n(_HM,_HT);});break;case 15:return new F(function(){return _n(_HL,_HT);});break;case 16:return new F(function(){return _n(_HK,_HT);});break;case 17:return new F(function(){return _n(_HJ,_HT);});break;default:return new F(function(){return _n(_Hy,_HT);});}},_HU=new T(function(){return B(unCStr("}"));}),_HV=new T(function(){return B(unCStr("{handle: "));}),_HW=function(_HX,_HY,_HZ,_I0,_I1,_I2){var _I3=new T(function(){var _I4=new T(function(){var _I5=new T(function(){var _I6=E(_I0);if(!_I6._){return E(_I2);}else{var _I7=new T(function(){return B(_n(_I6,new T(function(){return B(_n(_Hw,_I2));},1)));},1);return B(_n(_Hx,_I7));}},1);return B(_HR(_HY,_I5));}),_I8=E(_HZ);if(!_I8._){return E(_I4);}else{return B(_n(_I8,new T(function(){return B(_n(_Hv,_I4));},1)));}}),_I9=E(_I1);if(!_I9._){var _Ia=E(_HX);if(!_Ia._){return E(_I3);}else{var _Ib=E(_Ia.a);if(!_Ib._){var _Ic=new T(function(){var _Id=new T(function(){return B(_n(_HU,new T(function(){return B(_n(_Hv,_I3));},1)));},1);return B(_n(_Ib.a,_Id));},1);return new F(function(){return _n(_HV,_Ic);});}else{var _Ie=new T(function(){var _If=new T(function(){return B(_n(_HU,new T(function(){return B(_n(_Hv,_I3));},1)));},1);return B(_n(_Ib.a,_If));},1);return new F(function(){return _n(_HV,_Ie);});}}}else{return new F(function(){return _n(_I9.a,new T(function(){return B(_n(_Hv,_I3));},1));});}},_Ig=function(_Ih){var _Ii=E(_Ih);return new F(function(){return _HW(_Ii.a,_Ii.b,_Ii.c,_Ii.d,_Ii.f,_w);});},_Ij=function(_Ik,_Il,_Im){var _In=E(_Il);return new F(function(){return _HW(_In.a,_In.b,_In.c,_In.d,_In.f,_Im);});},_Io=function(_Ip,_Iq){var _Ir=E(_Ip);return new F(function(){return _HW(_Ir.a,_Ir.b,_Ir.c,_Ir.d,_Ir.f,_Iq);});},_Is=function(_It,_Iu){return new F(function(){return _2J(_Io,_It,_Iu);});},_Iv=new T3(0,_Ij,_Ig,_Is),_Iw=new T(function(){return new T5(0,_Hq,_Iv,_Ix,_Hs,_Ig);}),_Ix=function(_Iy){return new T2(0,_Iw,_Iy);},_Iz=__Z,_IA=7,_IB=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_IC=new T6(0,_Iz,_IA,_w,_IB,_Iz,_Iz),_ID=new T(function(){return B(_Ix(_IC));}),_IE=function(_){return new F(function(){return die(_ID);});},_IF=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_IG=new T6(0,_Iz,_IA,_w,_IF,_Iz,_Iz),_IH=new T(function(){return B(_Ix(_IG));}),_II=function(_){return new F(function(){return die(_IH);});},_IJ=function(_IK,_){return new T2(0,_w,_IK);},_IL=0.6,_IM=1,_IN=new T(function(){return B(unCStr(")"));}),_IO=function(_IP,_IQ){var _IR=new T(function(){var _IS=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_CQ(0,_IP,_w)),_IN));})));},1);return B(_n(B(_CQ(0,_IQ,_w)),_IS));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_IR)));});},_IT=function(_IU,_IV){var _IW=new T(function(){var _IX=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_CQ(0,_IV,_w)),_IN));})));},1);return B(_n(B(_CQ(0,_IU,_w)),_IX));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_IW)));});},_IY=function(_IZ){var _J0=E(_IZ);if(!_J0._){return E(_IJ);}else{var _J1=new T(function(){return B(_IY(_J0.b));}),_J2=function(_J3){var _J4=E(_J3);if(!_J4._){return E(_J1);}else{var _J5=_J4.a,_J6=new T(function(){return B(_J2(_J4.b));}),_J7=new T(function(){return 0.1*E(E(_J5).e)/1.0e-2;}),_J8=new T(function(){var _J9=E(_J5);if(_J9.a!=_J9.b){return E(_IM);}else{return E(_IL);}}),_Ja=function(_Jb,_){var _Jc=E(_Jb),_Jd=_Jc.c,_Je=_Jc.d,_Jf=E(_Jc.a),_Jg=E(_Jc.b),_Jh=E(_J5),_Ji=_Jh.a,_Jj=_Jh.b,_Jk=E(_Jh.c),_Jl=_Jk.b,_Jm=E(_Jk.a),_Jn=_Jm.a,_Jo=_Jm.b,_Jp=_Jm.c,_Jq=E(_Jh.d),_Jr=_Jq.b,_Js=E(_Jq.a),_Jt=_Js.a,_Ju=_Js.b,_Jv=_Js.c;if(_Jf>_Ji){return new F(function(){return _II(_);});}else{if(_Ji>_Jg){return new F(function(){return _II(_);});}else{if(_Jf>_Jj){return new F(function(){return _IE(_);});}else{if(_Jj>_Jg){return new F(function(){return _IE(_);});}else{var _Jw=_Ji-_Jf|0;if(0>_Jw){return new F(function(){return _IO(_Jd,_Jw);});}else{if(_Jw>=_Jd){return new F(function(){return _IO(_Jd,_Jw);});}else{var _Jx=E(_Je[_Jw]),_Jy=E(_Jx.c),_Jz=_Jy.b,_JA=E(_Jy.a),_JB=_JA.a,_JC=_JA.b,_JD=_JA.c,_JE=E(_Jx.e),_JF=E(_JE.a),_JG=B(_Gi(_ll,_Jn,_Jo,_Jp,_Jl,_JB,_JC,_JD,_Jz)),_JH=E(_JG.a),_JI=B(_Gi(_ll,_JH.a,_JH.b,_JH.c,_JG.b,_Jn,_Jo,_Jp,_Jl)),_JJ=E(_JI.a),_JK=_Jj-_Jf|0;if(0>_JK){return new F(function(){return _IT(_JK,_Jd);});}else{if(_JK>=_Jd){return new F(function(){return _IT(_JK,_Jd);});}else{var _JL=E(_Je[_JK]),_JM=E(_JL.c),_JN=_JM.b,_JO=E(_JM.a),_JP=_JO.a,_JQ=_JO.b,_JR=_JO.c,_JS=E(_JL.e),_JT=E(_JS.a),_JU=B(_Gi(_ll,_Jt,_Ju,_Jv,_Jr,_JP,_JQ,_JR,_JN)),_JV=E(_JU.a),_JW=B(_Gi(_ll,_JV.a,_JV.b,_JV.c,_JU.b,_Jt,_Ju,_Jv,_Jr)),_JX=E(_JW.a),_JY=E(_JJ.a)+E(_JJ.b)+E(_JJ.c)+E(_JI.b)+E(_JX.a)+E(_JX.b)+E(_JX.c)+E(_JW.b);if(!_JY){var _JZ=B(A2(_J6,_Jc,_));return new T2(0,new T2(1,_mC,new T(function(){return E(E(_JZ).a);})),new T(function(){return E(E(_JZ).b);}));}else{var _K0=new T(function(){return  -((B(_Ha(_lR,_JF.a,_JF.b,_JF.c,_JE.b,_Jn,_Jo,_Jp,_Jl))-B(_Ha(_lR,_JT.a,_JT.b,_JT.c,_JS.b,_Jt,_Ju,_Jv,_Jr))-E(_J7))/_JY);}),_K1=function(_K2,_K3,_K4,_K5,_){var _K6=new T(function(){var _K7=function(_K8,_K9,_Ka,_Kb,_Kc){if(_K8>_Jj){return E(_Kc);}else{if(_Jj>_K9){return E(_Kc);}else{var _Kd=function(_){var _Ke=newArr(_Ka,_kl),_Kf=_Ke,_Kg=function(_Kh,_){while(1){if(_Kh!=_Ka){var _=_Kf[_Kh]=_Kb[_Kh],_Ki=_Kh+1|0;_Kh=_Ki;continue;}else{return E(_);}}},_=B(_Kg(0,_)),_Kj=_Jj-_K8|0;if(0>_Kj){return new F(function(){return _IT(_Kj,_Ka);});}else{if(_Kj>=_Ka){return new F(function(){return _IT(_Kj,_Ka);});}else{var _=_Kf[_Kj]=new T(function(){var _Kk=E(_Kb[_Kj]),_Kl=E(_Kk.e),_Km=E(_Kl.a),_Kn=B(_Gi(_ll,_JP,_JQ,_JR,_JN,_Jt,_Ju,_Jv,_Jr)),_Ko=E(_Kn.a),_Kp=E(_K0)*E(_J8),_Kq=B(_Gi(_ll,_Ko.a,_Ko.b,_Ko.c,_Kn.b,_Kp,_Kp,_Kp,_Kp)),_Kr=E(_Kq.a),_Ks=B(_Gt(_ll,_Km.a,_Km.b,_Km.c,_Kl.b, -E(_Kr.a), -E(_Kr.b), -E(_Kr.c), -E(_Kq.b)));return {_:0,a:E(_Kk.a),b:E(_Kk.b),c:E(_Kk.c),d:E(_Kk.d),e:E(new T2(0,E(_Ks.a),E(_Ks.b))),f:E(_Kk.f),g:E(_Kk.g),h:_Kk.h,i:_Kk.i};});return new T4(0,E(_K8),E(_K9),_Ka,_Kf);}}};return new F(function(){return _CC(_Kd);});}}};if(_K2>_Ji){return B(_K7(_K2,_K3,_K4,_K5,new T4(0,E(_K2),E(_K3),_K4,_K5)));}else{if(_Ji>_K3){return B(_K7(_K2,_K3,_K4,_K5,new T4(0,E(_K2),E(_K3),_K4,_K5)));}else{var _Kt=function(_){var _Ku=newArr(_K4,_kl),_Kv=_Ku,_Kw=function(_Kx,_){while(1){if(_Kx!=_K4){var _=_Kv[_Kx]=_K5[_Kx],_Ky=_Kx+1|0;_Kx=_Ky;continue;}else{return E(_);}}},_=B(_Kw(0,_)),_Kz=_Ji-_K2|0;if(0>_Kz){return new F(function(){return _IO(_K4,_Kz);});}else{if(_Kz>=_K4){return new F(function(){return _IO(_K4,_Kz);});}else{var _=_Kv[_Kz]=new T(function(){var _KA=E(_K5[_Kz]),_KB=E(_KA.e),_KC=E(_KB.a),_KD=B(_Gi(_ll,_JB,_JC,_JD,_Jz,_Jn,_Jo,_Jp,_Jl)),_KE=E(_KD.a),_KF=E(_K0)*E(_J8),_KG=B(_Gi(_ll,_KE.a,_KE.b,_KE.c,_KD.b,_KF,_KF,_KF,_KF)),_KH=E(_KG.a),_KI=B(_Gt(_ll,_KC.a,_KC.b,_KC.c,_KB.b,_KH.a,_KH.b,_KH.c,_KG.b));return {_:0,a:E(_KA.a),b:E(_KA.b),c:E(_KA.c),d:E(_KA.d),e:E(new T2(0,E(_KI.a),E(_KI.b))),f:E(_KA.f),g:E(_KA.g),h:_KA.h,i:_KA.i};});return new T4(0,E(_K2),E(_K3),_K4,_Kv);}}},_KJ=B(_CC(_Kt));return B(_K7(E(_KJ.a),E(_KJ.b),_KJ.c,_KJ.d,_KJ));}}});return new T2(0,_mC,_K6);};if(!E(_Jh.f)){var _KK=B(_K1(_Jf,_Jg,_Jd,_Je,_)),_KL=B(A2(_J6,new T(function(){return E(E(_KK).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_KK).a);}),new T(function(){return E(E(_KL).a);})),new T(function(){return E(E(_KL).b);}));}else{if(E(_K0)<0){var _KM=B(A2(_J6,_Jc,_));return new T2(0,new T2(1,_mC,new T(function(){return E(E(_KM).a);})),new T(function(){return E(E(_KM).b);}));}else{var _KN=B(_K1(_Jf,_Jg,_Jd,_Je,_)),_KO=B(A2(_J6,new T(function(){return E(E(_KN).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_KN).a);}),new T(function(){return E(E(_KO).a);})),new T(function(){return E(E(_KO).b);}));}}}}}}}}}}}};return E(_Ja);}};return new F(function(){return _J2(_J0.a);});}},_KP=function(_,_KQ){var _KR=new T(function(){return B(_IY(E(_KQ).a));}),_KS=function(_KT){var _KU=E(_KT);return (_KU==1)?E(new T2(1,_KR,_w)):new T2(1,_KR,new T(function(){return B(_KS(_KU-1|0));}));},_KV=B(_Fu(B(_KS(5)),new T(function(){return E(E(_KQ).b);}),_)),_KW=new T(function(){return B(_G2(_Ft,_Di,_H1,new T(function(){return E(E(_KV).b);})));});return new T2(0,_mC,_KW);},_KX=function(_KY,_KZ,_L0,_L1,_L2){var _L3=B(_82(B(_80(_KY))));return new F(function(){return A3(_6Q,_L3,new T(function(){return B(A3(_bh,_L3,_KZ,_L1));}),new T(function(){return B(A3(_bh,_L3,_L0,_L2));}));});},_L4=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_L5=new T6(0,_Iz,_IA,_w,_L4,_Iz,_Iz),_L6=new T(function(){return B(_Ix(_L5));}),_L7=function(_){return new F(function(){return die(_L6);});},_L8=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_L9=new T6(0,_Iz,_IA,_w,_L8,_Iz,_Iz),_La=new T(function(){return B(_Ix(_L9));}),_Lb=function(_){return new F(function(){return die(_La);});},_Lc=false,_Ld=true,_Le=function(_Lf){var _Lg=E(_Lf),_Lh=_Lg.b,_Li=E(_Lg.d),_Lj=E(_Lg.e),_Lk=E(_Lj.a),_Ll=E(_Lg.g),_Lm=B(A1(_Lh,_Li.a)),_Ln=B(_o3(_lR,_Lm.a,_Lm.b,_Lm.c,_Ll.a,_Ll.b,_Ll.c));return {_:0,a:E(_Lg.a),b:E(_Lh),c:E(_Lg.c),d:E(_Li),e:E(new T2(0,E(new T3(0,E(_Lk.a)+E(_Ln.a)*1.0e-2,E(_Lk.b)+E(_Ln.b)*1.0e-2,E(_Lk.c)+E(_Ln.c)*1.0e-2)),E(_Lj.b))),f:E(_Lg.f),g:E(_Ll),h:_Lg.h,i:_Lg.i};},_Lo=new T(function(){return eval("__strict(collideBound)");}),_Lp=new T(function(){return eval("__strict(mouseContact)");}),_Lq=new T(function(){return eval("__strict(collide)");}),_Lr=function(_Ls){var _Lt=E(_Ls);if(!_Lt._){return __Z;}else{return new F(function(){return _n(_Lt.a,new T(function(){return B(_Lr(_Lt.b));},1));});}},_Lu=0,_Lv=new T3(0,E(_Lu),E(_Lu),E(_Lu)),_Lw=new T2(0,E(_Lv),E(_Lu)),_Lx=new T2(0,_lR,_mq),_Ly=new T(function(){return B(_jR(_Lx));}),_Lz=function(_LA,_){var _LB=B(_G2(_Ft,_Di,_Le,_LA)),_LC=E(_LB.a),_LD=E(_LB.b);if(_LC<=_LD){var _LE=function(_LF,_LG,_LH,_LI,_LJ,_){if(_LG>_LF){return new F(function(){return _Lb(_);});}else{if(_LF>_LH){return new F(function(){return _Lb(_);});}else{var _LK=new T(function(){var _LL=_LF-_LG|0;if(0>_LL){return B(_IT(_LL,_LI));}else{if(_LL>=_LI){return B(_IT(_LL,_LI));}else{return E(_LJ[_LL]);}}}),_LM=function(_LN,_LO,_LP,_LQ,_LR,_){var _LS=E(_LN);if(!_LS._){return new T2(0,_w,new T4(0,E(_LO),E(_LP),_LQ,_LR));}else{var _LT=E(_LS.a);if(_LO>_LT){return new F(function(){return _L7(_);});}else{if(_LT>_LP){return new F(function(){return _L7(_);});}else{var _LU=E(_LK),_LV=_LT-_LO|0;if(0>_LV){return new F(function(){return _IO(_LQ,_LV);});}else{if(_LV>=_LQ){return new F(function(){return _IO(_LQ,_LV);});}else{var _LW=E(_LR[_LV]),_LX=__app2(E(_Lq),B(_mD(new T2(1,new T2(0,_CH,_LU.h),new T2(1,new T2(0,_CG,_LU.i),_w)))),B(_mD(new T2(1,new T2(0,_CH,_LW.h),new T2(1,new T2(0,_CG,_LW.i),_w))))),_LY=__arr2lst(0,_LX),_LZ=B(_DV(_LY,_)),_M0=B(_LM(_LS.b,_LO,_LP,_LQ,_LR,_)),_M1=new T(function(){var _M2=new T(function(){return _LF!=_LT;}),_M3=function(_M4){var _M5=E(_M4);if(!_M5._){return __Z;}else{var _M6=_M5.b,_M7=E(_M5.a),_M8=E(_M7.b),_M9=E(_M7.a),_Ma=E(_M7.c),_Mb=_Ma.a,_Mc=_Ma.b,_Md=E(_M7.e),_Me=E(_M7.d),_Mf=_Me.a,_Mg=_Me.b,_Mh=E(_M7.f),_Mi=new T(function(){var _Mj=B(_ng(_lR,_Mh.a,_Mh.b,_Mh.c)),_Mk=Math.sqrt(B(_KX(_lR,_Mf,_Mg,_Mf,_Mg)));return new T3(0,_Mk*E(_Mj.a),_Mk*E(_Mj.b),_Mk*E(_Mj.c));}),_Ml=new T(function(){var _Mm=B(_ng(_lR,_Md.a,_Md.b,_Md.c)),_Mn=Math.sqrt(B(_KX(_lR,_Mb,_Mc,_Mb,_Mc)));return new T3(0,_Mn*E(_Mm.a),_Mn*E(_Mm.b),_Mn*E(_Mm.c));}),_Mo=new T(function(){var _Mp=B(A1(_Ly,_M8)),_Mq=B(_ng(_lR,_Mp.a,_Mp.b,_Mp.c));return new T3(0,E(_Mq.a),E(_Mq.b),E(_Mq.c));}),_Mr=new T(function(){var _Ms=B(A1(_Ly,_M9)),_Mt=B(_ng(_lR,_Ms.a,_Ms.b,_Ms.c));return new T3(0,E(_Mt.a),E(_Mt.b),E(_Mt.c));}),_Mu=E(_M8.a)+ -E(_M9.a),_Mv=E(_M8.b)+ -E(_M9.b),_Mw=E(_M8.c)+ -E(_M9.c),_Mx=new T(function(){return Math.sqrt(B(_bj(_lR,_Mu,_Mv,_Mw,_Mu,_Mv,_Mw)));}),_My=new T(function(){var _Mz=1/E(_Mx);return new T3(0,_Mu*_Mz,_Mv*_Mz,_Mw*_Mz);}),_MA=new T(function(){if(!E(_M7.g)){return E(_My);}else{var _MB=E(_My);return new T3(0,-1*E(_MB.a),-1*E(_MB.b),-1*E(_MB.c));}}),_MC=new T(function(){if(!E(_M7.h)){return E(_My);}else{var _MD=E(_My);return new T3(0,-1*E(_MD.a),-1*E(_MD.b),-1*E(_MD.c));}});return (!E(_M2))?new T2(1,new T(function(){var _ME=E(_MA),_MF=E(_ME.b),_MG=E(_ME.c),_MH=E(_ME.a),_MI=E(_Mr),_MJ=E(_MI.c),_MK=E(_MI.b),_ML=E(_MI.a),_MM=E(_Ml),_MN=E(_MM.c),_MO=E(_MM.b),_MP=E(_MM.a),_MQ=_MF*_MJ-_MK*_MG,_MR=_MG*_ML-_MJ*_MH,_MS=_MH*_MK-_ML*_MF,_MT=B(_bj(_lR,_MR*_MN-_MO*_MS,_MS*_MP-_MN*_MQ,_MQ*_MO-_MP*_MR,_ML,_MK,_MJ));return new T6(0,_LF,_LT,E(new T2(0,E(new T3(0,E(_MQ),E(_MR),E(_MS))),E(_MT))),E(_Lw),_Mx,_Lc);}),new T2(1,new T(function(){var _MU=E(_MC),_MV=E(_MU.b),_MW=E(_MU.c),_MX=E(_MU.a),_MY=E(_Mo),_MZ=E(_MY.c),_N0=E(_MY.b),_N1=E(_MY.a),_N2=E(_Mi),_N3=E(_N2.c),_N4=E(_N2.b),_N5=E(_N2.a),_N6=_MV*_MZ-_N0*_MW,_N7=_MW*_N1-_MZ*_MX,_N8=_MX*_N0-_N1*_MV,_N9=B(_bj(_lR,_N7*_N3-_N4*_N8,_N8*_N5-_N3*_N6,_N6*_N4-_N5*_N7,_N1,_N0,_MZ));return new T6(0,_LF,_LT,E(_Lw),E(new T2(0,E(new T3(0,E(_N6),E(_N7),E(_N8))),E(_N9))),_Mx,_Lc);}),new T(function(){return B(_M3(_M6));}))):new T2(1,new T(function(){var _Na=E(_MA),_Nb=E(_Na.b),_Nc=E(_Na.c),_Nd=E(_Na.a),_Ne=E(_Mr),_Nf=_Ne.a,_Ng=_Ne.b,_Nh=_Ne.c,_Ni=B(_o3(_lR,_Nd,_Nb,_Nc,_Nf,_Ng,_Nh)),_Nj=E(_Ml),_Nk=E(_Nj.c),_Nl=E(_Nj.b),_Nm=E(_Nj.a),_Nn=B(_bj(_lR,_Nb*_Nk-_Nl*_Nc,_Nc*_Nm-_Nk*_Nd,_Nd*_Nl-_Nm*_Nb,_Nf,_Ng,_Nh)),_No=E(_MC),_Np=E(_No.b),_Nq=E(_No.c),_Nr=E(_No.a),_Ns=E(_Mo),_Nt=_Ns.a,_Nu=_Ns.b,_Nv=_Ns.c,_Nw=B(_o3(_lR,_Nr,_Np,_Nq,_Nt,_Nu,_Nv)),_Nx=E(_Mi),_Ny=E(_Nx.c),_Nz=E(_Nx.b),_NA=E(_Nx.a),_NB=B(_bj(_lR,_Np*_Ny-_Nz*_Nq,_Nq*_NA-_Ny*_Nr,_Nr*_Nz-_NA*_Np,_Nt,_Nu,_Nv));return new T6(0,_LF,_LT,E(new T2(0,E(new T3(0,E(_Ni.a),E(_Ni.b),E(_Ni.c))),E(_Nn))),E(new T2(0,E(new T3(0,E(_Nw.a),E(_Nw.b),E(_Nw.c))),E(_NB))),_Mx,_Ld);}),new T(function(){return B(_M3(_M6));}));}};return B(_M3(_LZ));});return new T2(0,new T2(1,_M1,new T(function(){return E(E(_M0).a);})),new T(function(){return E(E(_M0).b);}));}}}}}},_NC=B(_LM(B(_uy(_LF,_LD)),_LG,_LH,_LI,_LJ,_)),_ND=E(_LK),_NE=E(_ND.d).a,_NF=__app1(E(_Lo),B(_mD(new T2(1,new T2(0,_CH,_ND.h),new T2(1,new T2(0,_CG,_ND.i),_w))))),_NG=__arr2lst(0,_NF),_NH=B(_DV(_NG,_)),_NI=__app1(E(_Lp),_LF),_NJ=__arr2lst(0,_NI),_NK=B(_DV(_NJ,_));if(_LF!=_LD){var _NL=E(_NC),_NM=E(_NL.b),_NN=B(_LE(_LF+1|0,E(_NM.a),E(_NM.b),_NM.c,_NM.d,_)),_NO=new T(function(){var _NP=new T(function(){var _NQ=B(A1(_Ly,_NE)),_NR=B(_ng(_lR,_NQ.a,_NQ.b,_NQ.c));return new T3(0,E(_NR.a),E(_NR.b),E(_NR.c));}),_NS=new T(function(){var _NT=new T(function(){return B(_Lr(_NL.a));}),_NU=function(_NV){var _NW=E(_NV);if(!_NW._){return E(_NT);}else{var _NX=E(_NW.a),_NY=E(_NX.b),_NZ=E(_NX.a),_O0=E(_NX.c),_O1=_O0.a,_O2=_O0.b,_O3=E(_NX.e);return new T2(1,new T(function(){var _O4=E(_NY.a)+ -E(_NZ.a),_O5=E(_NY.b)+ -E(_NZ.b),_O6=E(_NY.c)+ -E(_NZ.c),_O7=B(A1(_Ly,_NZ)),_O8=B(_ng(_lR,_O7.a,_O7.b,_O7.c)),_O9=_O8.a,_Oa=_O8.b,_Ob=_O8.c,_Oc=Math.sqrt(B(_bj(_lR,_O4,_O5,_O6,_O4,_O5,_O6))),_Od=1/_Oc,_Oe=_O4*_Od,_Of=_O5*_Od,_Og=_O6*_Od,_Oh=B(_o3(_lR,_Oe,_Of,_Og,_O9,_Oa,_Ob)),_Oi=B(_ng(_lR,_O3.a,_O3.b,_O3.c)),_Oj=Math.sqrt(B(_KX(_lR,_O1,_O2,_O1,_O2))),_Ok=_Oj*E(_Oi.a),_Ol=_Oj*E(_Oi.b),_Om=_Oj*E(_Oi.c),_On=B(_bj(_lR,_Of*_Om-_Ol*_Og,_Og*_Ok-_Om*_Oe,_Oe*_Ol-_Ok*_Of,_O9,_Oa,_Ob));return new T6(0,_LF,_LF,E(new T2(0,E(new T3(0,E(_Oh.a),E(_Oh.b),E(_Oh.c))),E(_On))),E(_Lw),_Oc,_Ld);}),new T(function(){return B(_NU(_NW.b));}));}};return B(_NU(_NH));}),_Oo=function(_Op){var _Oq=E(_Op);if(!_Oq._){return E(_NS);}else{var _Or=E(_Oq.a),_Os=E(_Or.b),_Ot=new T(function(){var _Ou=E(_NE),_Ov=E(_Os.c)+ -E(_Ou.c),_Ow=E(_Os.b)+ -E(_Ou.b),_Ox=E(_Os.a)+ -E(_Ou.a),_Oy=Math.sqrt(B(_bj(_lR,_Ox,_Ow,_Ov,_Ox,_Ow,_Ov))),_Oz=function(_OA,_OB,_OC){var _OD=E(_NP),_OE=_OD.a,_OF=_OD.b,_OG=_OD.c,_OH=B(_o3(_lR,_OA,_OB,_OC,_OE,_OF,_OG)),_OI=B(_bj(_lR,_OB*0-0*_OC,_OC*0-0*_OA,_OA*0-0*_OB,_OE,_OF,_OG));return new T6(0,_LF,_LF,new T2(0,E(new T3(0,E(_OH.a),E(_OH.b),E(_OH.c))),E(_OI)),_Lw,_Oy,_Ld);};if(!E(_Or.g)){var _OJ=1/_Oy,_OK=B(_Oz(_Ox*_OJ,_Ow*_OJ,_Ov*_OJ));return new T6(0,_OK.a,_OK.b,E(_OK.c),E(_OK.d),_OK.e,_OK.f);}else{var _OL=1/_Oy,_OM=B(_Oz(-1*_Ox*_OL,-1*_Ow*_OL,-1*_Ov*_OL));return new T6(0,_OM.a,_OM.b,E(_OM.c),E(_OM.d),_OM.e,_OM.f);}});return new T2(1,_Ot,new T(function(){return B(_Oo(_Oq.b));}));}};return B(_Oo(_NK));});return new T2(0,new T2(1,_NO,new T(function(){return E(E(_NN).a);})),new T(function(){return E(E(_NN).b);}));}else{var _ON=new T(function(){var _OO=new T(function(){var _OP=B(A1(_Ly,_NE)),_OQ=B(_ng(_lR,_OP.a,_OP.b,_OP.c));return new T3(0,E(_OQ.a),E(_OQ.b),E(_OQ.c));}),_OR=new T(function(){var _OS=new T(function(){return B(_Lr(E(_NC).a));}),_OT=function(_OU){var _OV=E(_OU);if(!_OV._){return E(_OS);}else{var _OW=E(_OV.a),_OX=E(_OW.b),_OY=E(_OW.a),_OZ=E(_OW.c),_P0=_OZ.a,_P1=_OZ.b,_P2=E(_OW.e);return new T2(1,new T(function(){var _P3=E(_OX.a)+ -E(_OY.a),_P4=E(_OX.b)+ -E(_OY.b),_P5=E(_OX.c)+ -E(_OY.c),_P6=B(A1(_Ly,_OY)),_P7=B(_ng(_lR,_P6.a,_P6.b,_P6.c)),_P8=_P7.a,_P9=_P7.b,_Pa=_P7.c,_Pb=Math.sqrt(B(_bj(_lR,_P3,_P4,_P5,_P3,_P4,_P5))),_Pc=1/_Pb,_Pd=_P3*_Pc,_Pe=_P4*_Pc,_Pf=_P5*_Pc,_Pg=B(_o3(_lR,_Pd,_Pe,_Pf,_P8,_P9,_Pa)),_Ph=B(_ng(_lR,_P2.a,_P2.b,_P2.c)),_Pi=Math.sqrt(B(_KX(_lR,_P0,_P1,_P0,_P1))),_Pj=_Pi*E(_Ph.a),_Pk=_Pi*E(_Ph.b),_Pl=_Pi*E(_Ph.c),_Pm=B(_bj(_lR,_Pe*_Pl-_Pk*_Pf,_Pf*_Pj-_Pl*_Pd,_Pd*_Pk-_Pj*_Pe,_P8,_P9,_Pa));return new T6(0,_LF,_LF,E(new T2(0,E(new T3(0,E(_Pg.a),E(_Pg.b),E(_Pg.c))),E(_Pm))),E(_Lw),_Pb,_Ld);}),new T(function(){return B(_OT(_OV.b));}));}};return B(_OT(_NH));}),_Pn=function(_Po){var _Pp=E(_Po);if(!_Pp._){return E(_OR);}else{var _Pq=E(_Pp.a),_Pr=E(_Pq.b),_Ps=new T(function(){var _Pt=E(_NE),_Pu=E(_Pr.c)+ -E(_Pt.c),_Pv=E(_Pr.b)+ -E(_Pt.b),_Pw=E(_Pr.a)+ -E(_Pt.a),_Px=Math.sqrt(B(_bj(_lR,_Pw,_Pv,_Pu,_Pw,_Pv,_Pu))),_Py=function(_Pz,_PA,_PB){var _PC=E(_OO),_PD=_PC.a,_PE=_PC.b,_PF=_PC.c,_PG=B(_o3(_lR,_Pz,_PA,_PB,_PD,_PE,_PF)),_PH=B(_bj(_lR,_PA*0-0*_PB,_PB*0-0*_Pz,_Pz*0-0*_PA,_PD,_PE,_PF));return new T6(0,_LF,_LF,new T2(0,E(new T3(0,E(_PG.a),E(_PG.b),E(_PG.c))),E(_PH)),_Lw,_Px,_Ld);};if(!E(_Pq.g)){var _PI=1/_Px,_PJ=B(_Py(_Pw*_PI,_Pv*_PI,_Pu*_PI));return new T6(0,_PJ.a,_PJ.b,E(_PJ.c),E(_PJ.d),_PJ.e,_PJ.f);}else{var _PK=1/_Px,_PL=B(_Py(-1*_Pw*_PK,-1*_Pv*_PK,-1*_Pu*_PK));return new T6(0,_PL.a,_PL.b,E(_PL.c),E(_PL.d),_PL.e,_PL.f);}});return new T2(1,_Ps,new T(function(){return B(_Pn(_Pp.b));}));}};return B(_Pn(_NK));});return new T2(0,new T2(1,_ON,_w),new T(function(){return E(E(_NC).b);}));}}}},_PM=B(_LE(_LC,_LC,_LD,_LB.c,_LB.d,_));return new F(function(){return _KP(_,_PM);});}else{return new F(function(){return _KP(_,new T2(0,_w,_LB));});}},_PN=new T(function(){return eval("__strict(passObject)");}),_PO=new T(function(){return eval("__strict(refresh)");}),_PP=function(_PQ,_){var _PR=__app0(E(_PO)),_PS=__app0(E(_CL)),_PT=E(_PQ),_PU=_PT.c,_PV=_PT.d,_PW=E(_PT.a),_PX=E(_PT.b);if(_PW<=_PX){if(_PW>_PX){return E(_CJ);}else{if(0>=_PU){return new F(function(){return _CW(_PU,0);});}else{var _PY=E(_PV[0]),_PZ=E(_PN),_Q0=__app2(_PZ,_PW,B(_mD(new T2(1,new T2(0,_CH,_PY.h),new T2(1,new T2(0,_CG,_PY.i),_w)))));if(_PW!=_PX){var _Q1=function(_Q2,_){if(_PW>_Q2){return E(_CJ);}else{if(_Q2>_PX){return E(_CJ);}else{var _Q3=_Q2-_PW|0;if(0>_Q3){return new F(function(){return _CW(_PU,_Q3);});}else{if(_Q3>=_PU){return new F(function(){return _CW(_PU,_Q3);});}else{var _Q4=E(_PV[_Q3]),_Q5=__app2(_PZ,_Q2,B(_mD(new T2(1,new T2(0,_CH,_Q4.h),new T2(1,new T2(0,_CG,_Q4.i),_w)))));if(_Q2!=_PX){var _Q6=B(_Q1(_Q2+1|0,_));return new T2(1,_mC,_Q6);}else{return _D1;}}}}}},_Q7=B(_Q1(_PW+1|0,_)),_Q8=__app0(E(_CK)),_Q9=B(_Lz(_PT,_));return new T(function(){return E(E(_Q9).b);});}else{var _Qa=__app0(E(_CK)),_Qb=B(_Lz(_PT,_));return new T(function(){return E(E(_Qb).b);});}}}}else{var _Qc=__app0(E(_CK)),_Qd=B(_Lz(_PT,_));return new T(function(){return E(E(_Qd).b);});}},_Qe=function(_Qf,_){while(1){var _Qg=E(_Qf);if(!_Qg._){return _mC;}else{var _Qh=_Qg.b,_Qi=E(_Qg.a);switch(_Qi._){case 0:var _Qj=B(A1(_Qi.a,_));_Qf=B(_n(_Qh,new T2(1,_Qj,_w)));continue;case 1:_Qf=B(_n(_Qh,_Qi.a));continue;default:_Qf=_Qh;continue;}}}},_Qk=function(_Ql,_Qm,_){var _Qn=E(_Ql);switch(_Qn._){case 0:var _Qo=B(A1(_Qn.a,_));return new F(function(){return _Qe(B(_n(_Qm,new T2(1,_Qo,_w))),_);});break;case 1:return new F(function(){return _Qe(B(_n(_Qm,_Qn.a)),_);});break;default:return new F(function(){return _Qe(_Qm,_);});}},_Qp=new T0(2),_Qq=function(_Qr){return new T0(2);},_Qs=function(_Qt,_Qu,_Qv){return function(_){var _Qw=E(_Qt),_Qx=rMV(_Qw),_Qy=E(_Qx);if(!_Qy._){var _Qz=new T(function(){var _QA=new T(function(){return B(A1(_Qv,_mC));});return B(_n(_Qy.b,new T2(1,new T2(0,_Qu,function(_QB){return E(_QA);}),_w)));}),_=wMV(_Qw,new T2(0,_Qy.a,_Qz));return _Qp;}else{var _QC=E(_Qy.a);if(!_QC._){var _=wMV(_Qw,new T2(0,_Qu,_w));return new T(function(){return B(A1(_Qv,_mC));});}else{var _=wMV(_Qw,new T1(1,_QC.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Qv,_mC));}),new T2(1,new T(function(){return B(A2(_QC.a,_Qu,_Qq));}),_w)));}}};},_QD=new T(function(){return E(_s4);}),_QE=new T(function(){return eval("window.requestAnimationFrame");}),_QF=new T1(1,_w),_QG=function(_QH,_QI){return function(_){var _QJ=E(_QH),_QK=rMV(_QJ),_QL=E(_QK);if(!_QL._){var _QM=_QL.a,_QN=E(_QL.b);if(!_QN._){var _=wMV(_QJ,_QF);return new T(function(){return B(A1(_QI,_QM));});}else{var _QO=E(_QN.a),_=wMV(_QJ,new T2(0,_QO.a,_QN.b));return new T1(1,new T2(1,new T(function(){return B(A1(_QI,_QM));}),new T2(1,new T(function(){return B(A1(_QO.b,_Qq));}),_w)));}}else{var _QP=new T(function(){var _QQ=function(_QR){var _QS=new T(function(){return B(A1(_QI,_QR));});return function(_QT){return E(_QS);};};return B(_n(_QL.a,new T2(1,_QQ,_w)));}),_=wMV(_QJ,new T1(1,_QP));return _Qp;}};},_QU=function(_QV,_QW){return new T1(0,B(_QG(_QV,_QW)));},_QX=function(_QY,_QZ){var _R0=new T(function(){return new T1(0,B(_Qs(_QY,_mC,_Qq)));});return function(_){var _R1=__createJSFunc(2,function(_R2,_){var _R3=B(_Qk(_R0,_w,_));return _QD;}),_R4=__app1(E(_QE),_R1);return new T(function(){return B(_QU(_QY,_QZ));});};},_R5=new T1(1,_w),_R6=function(_R7,_R8,_){var _R9=function(_){var _Ra=nMV(_R7),_Rb=_Ra;return new T(function(){var _Rc=new T(function(){return B(_Rd(_));}),_Re=function(_){var _Rf=rMV(_Rb),_Rg=B(A2(_R8,_Rf,_)),_=wMV(_Rb,_Rg),_Rh=function(_){var _Ri=nMV(_R5);return new T(function(){return new T1(0,B(_QX(_Ri,function(_Rj){return E(_Rc);})));});};return new T1(0,_Rh);},_Rk=new T(function(){return new T1(0,_Re);}),_Rd=function(_Rl){return E(_Rk);};return B(_Rd(_));});};return new F(function(){return _Qk(new T1(0,_R9),_w,_);});},_Rm=new T(function(){return eval("__strict(setBounds)");}),_Rn=function(_){var _Ro=__app3(E(_9m),E(_bM),E(_ke),E(_9l)),_Rp=__app2(E(_Rm),E(_8S),E(_8P));return new F(function(){return _R6(_CF,_PP,_);});},_Rq=function(_){return new F(function(){return _Rn(_);});};
var hasteMain = function() {B(A(_Rq, [0]));};window.onload = hasteMain;