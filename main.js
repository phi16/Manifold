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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(",y:"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr(",z:"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("})"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=new T(function(){return B(unCStr("-("));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr(")"));}),_I=new T1(0,_H),_J=new T2(1,_I,_w),_K=new T(function(){return B(unCStr("."));}),_L=new T1(0,0),_M=function(_N){while(1){var _O=E(_N);if(!_O._){_N=new T1(1,I_fromInt(_O.a));continue;}else{return new F(function(){return I_toString(_O.a);});}}},_P=function(_Q,_R){return new F(function(){return _n(fromJSStr(B(_M(_Q))),_R);});},_S=function(_T,_U){var _V=E(_T);if(!_V._){var _W=_V.a,_X=E(_U);return (_X._==0)?_W<_X.a:I_compareInt(_X.a,_W)>0;}else{var _Y=_V.a,_Z=E(_U);return (_Z._==0)?I_compareInt(_Y,_Z.a)<0:I_compare(_Y,_Z.a)<0;}},_10=41,_11=40,_12=new T1(0,0),_13=function(_14,_15,_16){if(_14<=6){return new F(function(){return _P(_15,_16);});}else{if(!B(_S(_15,_12))){return new F(function(){return _P(_15,_16);});}else{return new T2(1,_11,new T(function(){return B(_n(fromJSStr(B(_M(_15))),new T2(1,_10,_16)));}));}}},_17=new T(function(){return B(_13(0,_L,_w));}),_18=new T(function(){return B(_n(_17,_K));}),_19=new T1(0,_18),_1a=new T2(1,_19,_J),_1b=new T2(1,_G,_1a),_1c=new T1(1,_1b),_1d=new T2(1,_1c,_E),_1e=new T2(1,_B,_1d),_1f=new T2(1,_1c,_1e),_1g=new T2(1,_z,_1f),_1h=new T2(1,_1c,_1g),_1i=new T(function(){return B(unCStr("({x:"));}),_1j=new T1(0,_1i),_1k=new T2(1,_1j,_1h),_1l=function(_1m){return E(_1m);},_1n=new T(function(){return toJSStr(B(_e(_x,_1l,_1k)));}),_1o=new T1(0,1),_1p=new T(function(){return B(_13(0,_1o,_w));}),_1q=new T(function(){return B(_n(_1p,_K));}),_1r=new T1(0,_1q),_1s=new T2(1,_1r,_J),_1t=new T2(1,_G,_1s),_1u=new T(function(){return toJSStr(B(_e(_x,_1l,_1t)));}),_1v=function(_1w,_1x,_1y){var _1z=E(_1y);if(!_1z._){return new F(function(){return A1(_1x,_1z.a);});}else{var _1A=new T(function(){return B(_0(_1w));}),_1B=new T(function(){return B(_2(_1w));}),_1C=function(_1D){var _1E=E(_1D);if(!_1E._){return E(_1B);}else{return new F(function(){return A2(_1A,new T(function(){return B(_1v(_1w,_1x,_1E.a));}),new T(function(){return B(_1C(_1E.b));}));});}};return new F(function(){return _1C(_1z.a);});}},_1F=function(_1G,_1H,_1I){var _1J=new T(function(){return B(_0(_1G));}),_1K=new T(function(){return B(_2(_1G));}),_1L=function(_1M){var _1N=E(_1M);if(!_1N._){return E(_1K);}else{return new F(function(){return A2(_1J,new T(function(){return B(_1v(_1G,_1H,_1N.a));}),new T(function(){return B(_1L(_1N.b));}));});}};return new F(function(){return _1L(_1I);});},_1O=new T(function(){return B(unCStr("-("));}),_1P=new T1(0,_1O),_1Q=new T(function(){return B(unCStr(")"));}),_1R=new T1(0,_1Q),_1S=new T2(1,_1R,_w),_1T=new T(function(){return B(unCStr("."));}),_1U=new T(function(){return B(_13(0,_1o,_w));}),_1V=new T(function(){return B(_n(_1U,_1T));}),_1W=new T1(0,_1V),_1X=new T2(1,_1W,_1S),_1Y=new T2(1,_1P,_1X),_1Z=new T(function(){return toJSStr(B(_1F(_x,_1l,_1Y)));}),_20=new T(function(){return eval("__strict(compile)");}),_21=new T(function(){return B(unCStr(","));}),_22=new T1(0,_21),_23=new T(function(){return B(unCStr("pow("));}),_24=new T1(0,_23),_25=function(_26,_27){return new T1(1,new T2(1,_24,new T2(1,_26,new T2(1,_22,new T2(1,_27,_1S)))));},_28=new T(function(){return B(unCStr("acos("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1S)));},_2c=new T(function(){return B(unCStr("acosh("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1S)));},_2g=new T(function(){return B(unCStr("asin("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1S)));},_2k=new T(function(){return B(unCStr("asinh("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1S)));},_2o=new T(function(){return B(unCStr("atan("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1S)));},_2s=new T(function(){return B(unCStr("atanh("));}),_2t=new T1(0,_2s),_2u=function(_2v){return new T1(1,new T2(1,_2t,new T2(1,_2v,_1S)));},_2w=new T(function(){return B(unCStr("cos("));}),_2x=new T1(0,_2w),_2y=function(_2z){return new T1(1,new T2(1,_2x,new T2(1,_2z,_1S)));},_2A=new T(function(){return B(unCStr("cosh("));}),_2B=new T1(0,_2A),_2C=function(_2D){return new T1(1,new T2(1,_2B,new T2(1,_2D,_1S)));},_2E=new T(function(){return B(unCStr("exp("));}),_2F=new T1(0,_2E),_2G=function(_2H){return new T1(1,new T2(1,_2F,new T2(1,_2H,_1S)));},_2I=new T(function(){return B(unCStr("log("));}),_2J=new T1(0,_2I),_2K=function(_2L){return new T1(1,new T2(1,_2J,new T2(1,_2L,_1S)));},_2M=new T(function(){return B(unCStr(")/log("));}),_2N=new T1(0,_2M),_2O=function(_2P,_2Q){return new T1(1,new T2(1,_2J,new T2(1,_2Q,new T2(1,_2N,new T2(1,_2P,_1S)))));},_2R=new T(function(){return B(unCStr("pi"));}),_2S=new T1(0,_2R),_2T=new T(function(){return B(unCStr("sin("));}),_2U=new T1(0,_2T),_2V=function(_2W){return new T1(1,new T2(1,_2U,new T2(1,_2W,_1S)));},_2X=new T(function(){return B(unCStr("sinh("));}),_2Y=new T1(0,_2X),_2Z=function(_30){return new T1(1,new T2(1,_2Y,new T2(1,_30,_1S)));},_31=new T(function(){return B(unCStr("sqrt("));}),_32=new T1(0,_31),_33=function(_34){return new T1(1,new T2(1,_32,new T2(1,_34,_1S)));},_35=new T(function(){return B(unCStr("tan("));}),_36=new T1(0,_35),_37=function(_38){return new T1(1,new T2(1,_36,new T2(1,_38,_1S)));},_39=new T(function(){return B(unCStr("tanh("));}),_3a=new T1(0,_39),_3b=function(_3c){return new T1(1,new T2(1,_3a,new T2(1,_3c,_1S)));},_3d=new T(function(){return B(unCStr("("));}),_3e=new T1(0,_3d),_3f=new T(function(){return B(unCStr(")/("));}),_3g=new T1(0,_3f),_3h=function(_3i,_3j){return new T1(1,new T2(1,_3e,new T2(1,_3i,new T2(1,_3g,new T2(1,_3j,_1S)))));},_3k=new T1(0,1),_3l=function(_3m,_3n){var _3o=E(_3m);if(!_3o._){var _3p=_3o.a,_3q=E(_3n);if(!_3q._){var _3r=_3q.a;return (_3p!=_3r)?(_3p>_3r)?2:0:1;}else{var _3s=I_compareInt(_3q.a,_3p);return (_3s<=0)?(_3s>=0)?1:2:0;}}else{var _3t=_3o.a,_3u=E(_3n);if(!_3u._){var _3v=I_compareInt(_3t,_3u.a);return (_3v>=0)?(_3v<=0)?1:2:0;}else{var _3w=I_compare(_3t,_3u.a);return (_3w>=0)?(_3w<=0)?1:2:0;}}},_3x=new T(function(){return B(unCStr("base"));}),_3y=new T(function(){return B(unCStr("GHC.Exception"));}),_3z=new T(function(){return B(unCStr("ArithException"));}),_3A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3x,_3y,_3z),_3B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3A,_w,_w),_3C=function(_3D){return E(_3B);},_3E=function(_3F){return E(E(_3F).a);},_3G=function(_3H,_3I,_3J){var _3K=B(A1(_3H,_)),_3L=B(A1(_3I,_)),_3M=hs_eqWord64(_3K.a,_3L.a);if(!_3M){return __Z;}else{var _3N=hs_eqWord64(_3K.b,_3L.b);return (!_3N)?__Z:new T1(1,_3J);}},_3O=function(_3P){var _3Q=E(_3P);return new F(function(){return _3G(B(_3E(_3Q.a)),_3C,_3Q.b);});},_3R=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3S=new T(function(){return B(unCStr("denormal"));}),_3T=new T(function(){return B(unCStr("divide by zero"));}),_3U=new T(function(){return B(unCStr("loss of precision"));}),_3V=new T(function(){return B(unCStr("arithmetic underflow"));}),_3W=new T(function(){return B(unCStr("arithmetic overflow"));}),_3X=function(_3Y,_3Z){switch(E(_3Y)){case 0:return new F(function(){return _n(_3W,_3Z);});break;case 1:return new F(function(){return _n(_3V,_3Z);});break;case 2:return new F(function(){return _n(_3U,_3Z);});break;case 3:return new F(function(){return _n(_3T,_3Z);});break;case 4:return new F(function(){return _n(_3S,_3Z);});break;default:return new F(function(){return _n(_3R,_3Z);});}},_40=function(_41){return new F(function(){return _3X(_41,_w);});},_42=function(_43,_44,_45){return new F(function(){return _3X(_44,_45);});},_46=44,_47=93,_48=91,_49=function(_4a,_4b,_4c){var _4d=E(_4b);if(!_4d._){return new F(function(){return unAppCStr("[]",_4c);});}else{var _4e=new T(function(){var _4f=new T(function(){var _4g=function(_4h){var _4i=E(_4h);if(!_4i._){return E(new T2(1,_47,_4c));}else{var _4j=new T(function(){return B(A2(_4a,_4i.a,new T(function(){return B(_4g(_4i.b));})));});return new T2(1,_46,_4j);}};return B(_4g(_4d.b));});return B(A2(_4a,_4d.a,_4f));});return new T2(1,_48,_4e);}},_4k=function(_4l,_4m){return new F(function(){return _49(_3X,_4l,_4m);});},_4n=new T3(0,_42,_40,_4k),_4o=new T(function(){return new T5(0,_3C,_4n,_4p,_3O,_40);}),_4p=function(_4q){return new T2(0,_4o,_4q);},_4r=3,_4s=new T(function(){return B(_4p(_4r));}),_4t=new T(function(){return die(_4s);}),_4u=function(_4v,_4w){var _4x=E(_4v);return (_4x._==0)?_4x.a*Math.pow(2,_4w):I_toNumber(_4x.a)*Math.pow(2,_4w);},_4y=function(_4z,_4A){var _4B=E(_4z);if(!_4B._){var _4C=_4B.a,_4D=E(_4A);return (_4D._==0)?_4C==_4D.a:(I_compareInt(_4D.a,_4C)==0)?true:false;}else{var _4E=_4B.a,_4F=E(_4A);return (_4F._==0)?(I_compareInt(_4E,_4F.a)==0)?true:false:(I_compare(_4E,_4F.a)==0)?true:false;}},_4G=function(_4H){var _4I=E(_4H);if(!_4I._){return E(_4I.a);}else{return new F(function(){return I_toInt(_4I.a);});}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a,_4Q=addC(_4N,_4P);if(!E(_4Q.b)){return new T1(0,_4Q.a);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R._){_4K=_4M;_4L=new T1(1,I_fromInt(_4R.a));continue;}else{return new T1(1,I_add(_4M.a,_4R.a));}}}},_4S=function(_4T,_4U){while(1){var _4V=E(_4T);if(!_4V._){var _4W=E(_4V.a);if(_4W==(-2147483648)){_4T=new T1(1,I_fromInt(-2147483648));continue;}else{var _4X=E(_4U);if(!_4X._){var _4Y=_4X.a;return new T2(0,new T1(0,quot(_4W,_4Y)),new T1(0,_4W%_4Y));}else{_4T=new T1(1,I_fromInt(_4W));_4U=_4X;continue;}}}else{var _4Z=E(_4U);if(!_4Z._){_4T=_4V;_4U=new T1(1,I_fromInt(_4Z.a));continue;}else{var _50=I_quotRem(_4V.a,_4Z.a);return new T2(0,new T1(1,_50.a),new T1(1,_50.b));}}}},_51=new T1(0,0),_52=function(_53,_54){while(1){var _55=E(_53);if(!_55._){_53=new T1(1,I_fromInt(_55.a));continue;}else{return new T1(1,I_shiftLeft(_55.a,_54));}}},_56=function(_57,_58,_59){if(!B(_4y(_59,_51))){var _5a=B(_4S(_58,_59)),_5b=_5a.a;switch(B(_3l(B(_52(_5a.b,1)),_59))){case 0:return new F(function(){return _4u(_5b,_57);});break;case 1:if(!(B(_4G(_5b))&1)){return new F(function(){return _4u(_5b,_57);});}else{return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}break;default:return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}}else{return E(_4t);}},_5c=function(_5d,_5e){var _5f=E(_5d);if(!_5f._){var _5g=_5f.a,_5h=E(_5e);return (_5h._==0)?_5g>_5h.a:I_compareInt(_5h.a,_5g)<0;}else{var _5i=_5f.a,_5j=E(_5e);return (_5j._==0)?I_compareInt(_5i,_5j.a)>0:I_compare(_5i,_5j.a)>0;}},_5k=new T1(0,1),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5n=new T(function(){return B(unCStr("PatternMatchFail"));}),_5o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5l,_5m,_5n),_5p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5o,_w,_w),_5q=function(_5r){return E(_5p);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _3G(B(_3E(_5u.a)),_5q,_5u.b);});},_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return new T2(0,_5z,_5y);},_5A=function(_5B,_5C){return new F(function(){return _n(E(_5B).a,_5C);});},_5D=function(_5E,_5F){return new F(function(){return _49(_5A,_5E,_5F);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _n(E(_5I).a,_5J);});},_5K=new T3(0,_5G,_5v,_5D),_5z=new T(function(){return new T5(0,_5q,_5K,_5x,_5s,_5v);}),_5L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5M=function(_5N){return E(E(_5N).c);},_5O=function(_5P,_5Q){return new F(function(){return die(new T(function(){return B(A2(_5M,_5Q,_5P));}));});},_5R=function(_5S,_4q){return new F(function(){return _5O(_5S,_4q);});},_5T=function(_5U,_5V){var _5W=E(_5V);if(!_5W._){return new T2(0,_w,_w);}else{var _5X=_5W.a;if(!B(A1(_5U,_5X))){return new T2(0,_w,_5W);}else{var _5Y=new T(function(){var _5Z=B(_5T(_5U,_5W.b));return new T2(0,_5Z.a,_5Z.b);});return new T2(0,new T2(1,_5X,new T(function(){return E(E(_5Y).a);})),new T(function(){return E(E(_5Y).b);}));}}},_60=32,_61=new T(function(){return B(unCStr("\n"));}),_62=function(_63){return (E(_63)==124)?false:true;},_64=function(_65,_66){var _67=B(_5T(_62,B(unCStr(_65)))),_68=_67.a,_69=function(_6a,_6b){var _6c=new T(function(){var _6d=new T(function(){return B(_n(_66,new T(function(){return B(_n(_6b,_61));},1)));});return B(unAppCStr(": ",_6d));},1);return new F(function(){return _n(_6a,_6c);});},_6e=E(_67.b);if(!_6e._){return new F(function(){return _69(_68,_w);});}else{if(E(_6e.a)==124){return new F(function(){return _69(_68,new T2(1,_60,_6e.b));});}else{return new F(function(){return _69(_68,_w);});}}},_6f=function(_6g){return new F(function(){return _5R(new T1(0,new T(function(){return B(_64(_6g,_5L));})),_5z);});},_6h=function(_6i){var _6j=function(_6k,_6l){while(1){if(!B(_S(_6k,_6i))){if(!B(_5c(_6k,_6i))){if(!B(_4y(_6k,_6i))){return new F(function(){return _6f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_6l);}}else{return _6l-1|0;}}else{var _6m=B(_52(_6k,1)),_6n=_6l+1|0;_6k=_6m;_6l=_6n;continue;}}};return new F(function(){return _6j(_5k,0);});},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){var _6r=_6q.a>>>0;if(!_6r){return -1;}else{var _6s=function(_6t,_6u){while(1){if(_6t>=_6r){if(_6t<=_6r){if(_6t!=_6r){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6u);}}else{return _6u-1|0;}}else{var _6v=imul(_6t,2)>>>0,_6w=_6u+1|0;_6t=_6v;_6u=_6w;continue;}}};return new F(function(){return _6s(1,0);});}}else{return new F(function(){return _6h(_6q);});}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){var _6A=_6z.a>>>0;if(!_6A){return new T2(0,-1,0);}else{var _6B=function(_6C,_6D){while(1){if(_6C>=_6A){if(_6C<=_6A){if(_6C!=_6A){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6D);}}else{return _6D-1|0;}}else{var _6E=imul(_6C,2)>>>0,_6F=_6D+1|0;_6C=_6E;_6D=_6F;continue;}}};return new T2(0,B(_6B(1,0)),(_6A&_6A-1>>>0)>>>0&4294967295);}}else{var _6G=_6z.a;return new T2(0,B(_6o(_6z)),I_compareInt(I_and(_6G,I_sub(_6G,I_fromInt(1))),0));}},_6H=function(_6I,_6J){var _6K=E(_6I);if(!_6K._){var _6L=_6K.a,_6M=E(_6J);return (_6M._==0)?_6L<=_6M.a:I_compareInt(_6M.a,_6L)>=0;}else{var _6N=_6K.a,_6O=E(_6J);return (_6O._==0)?I_compareInt(_6N,_6O.a)<=0:I_compare(_6N,_6O.a)<=0;}},_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){var _6T=_6S.a,_6U=E(_6R);if(!_6U._){return new T1(0,(_6T>>>0&_6U.a>>>0)>>>0&4294967295);}else{_6Q=new T1(1,I_fromInt(_6T));_6R=_6U;continue;}}else{var _6V=E(_6R);if(!_6V._){_6Q=_6S;_6R=new T1(1,I_fromInt(_6V.a));continue;}else{return new T1(1,I_and(_6S.a,_6V.a));}}}},_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){var _70=_6Z.a,_71=E(_6Y);if(!_71._){var _72=_71.a,_73=subC(_70,_72);if(!E(_73.b)){return new T1(0,_73.a);}else{_6X=new T1(1,I_fromInt(_70));_6Y=new T1(1,I_fromInt(_72));continue;}}else{_6X=new T1(1,I_fromInt(_70));_6Y=_71;continue;}}else{var _74=E(_6Y);if(!_74._){_6X=_6Z;_6Y=new T1(1,I_fromInt(_74.a));continue;}else{return new T1(1,I_sub(_6Z.a,_74.a));}}}},_75=new T1(0,2),_76=function(_77,_78){var _79=E(_77);if(!_79._){var _7a=(_79.a>>>0&(2<<_78>>>0)-1>>>0)>>>0,_7b=1<<_78>>>0;return (_7b<=_7a)?(_7b>=_7a)?1:2:0;}else{var _7c=B(_6P(_79,B(_6W(B(_52(_75,_78)),_5k)))),_7d=B(_52(_5k,_78));return (!B(_5c(_7d,_7c)))?(!B(_S(_7d,_7c)))?1:2:0;}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){_7f=new T1(1,I_fromInt(_7h.a));continue;}else{return new T1(1,I_shiftRight(_7h.a,_7g));}}},_7i=function(_7j,_7k,_7l,_7m){var _7n=B(_6x(_7m)),_7o=_7n.a;if(!E(_7n.b)){var _7p=B(_6o(_7l));if(_7p<((_7o+_7j|0)-1|0)){var _7q=_7o+(_7j-_7k|0)|0;if(_7q>0){if(_7q>_7p){if(_7q<=(_7p+1|0)){if(!E(B(_6x(_7l)).b)){return 0;}else{return new F(function(){return _4u(_3k,_7j-_7k|0);});}}else{return 0;}}else{var _7r=B(_7e(_7l,_7q));switch(B(_76(_7l,_7q-1|0))){case 0:return new F(function(){return _4u(_7r,_7j-_7k|0);});break;case 1:if(!(B(_4G(_7r))&1)){return new F(function(){return _4u(_7r,_7j-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}break;default:return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}}}else{return new F(function(){return _4u(_7l,(_7j-_7k|0)-_7q|0);});}}else{if(_7p>=_7k){var _7s=B(_7e(_7l,(_7p+1|0)-_7k|0));switch(B(_76(_7l,_7p-_7k|0))){case 0:return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});break;case 2:return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});break;default:if(!(B(_4G(_7s))&1)){return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});}}}else{return new F(function(){return _4u(_7l, -_7o);});}}}else{var _7t=B(_6o(_7l))-_7o|0,_7u=function(_7v){var _7w=function(_7x,_7y){if(!B(_6H(B(_52(_7y,_7k)),_7x))){return new F(function(){return _56(_7v-_7k|0,_7x,_7y);});}else{return new F(function(){return _56((_7v-_7k|0)+1|0,_7x,B(_52(_7y,1)));});}};if(_7v>=_7k){if(_7v!=_7k){return new F(function(){return _7w(_7l,new T(function(){return B(_52(_7m,_7v-_7k|0));}));});}else{return new F(function(){return _7w(_7l,_7m);});}}else{return new F(function(){return _7w(new T(function(){return B(_52(_7l,_7k-_7v|0));}),_7m);});}};if(_7j>_7t){return new F(function(){return _7u(_7j);});}else{return new F(function(){return _7u(_7t);});}}},_7z=new T1(0,2147483647),_7A=new T(function(){return B(_4J(_7z,_5k));}),_7B=function(_7C){var _7D=E(_7C);if(!_7D._){var _7E=E(_7D.a);return (_7E==(-2147483648))?E(_7A):new T1(0, -_7E);}else{return new T1(1,I_negate(_7D.a));}},_7F=new T(function(){return 0/0;}),_7G=new T(function(){return -1/0;}),_7H=new T(function(){return 1/0;}),_7I=0,_7J=function(_7K,_7L){if(!B(_4y(_7L,_51))){if(!B(_4y(_7K,_51))){if(!B(_S(_7K,_51))){return new F(function(){return _7i(-1021,53,_7K,_7L);});}else{return  -B(_7i(-1021,53,B(_7B(_7K)),_7L));}}else{return E(_7I);}}else{return (!B(_4y(_7K,_51)))?(!B(_S(_7K,_51)))?E(_7H):E(_7G):E(_7F);}},_7M=function(_7N){return new T1(0,new T(function(){var _7O=E(_7N),_7P=jsShow(B(_7J(_7O.a,_7O.b)));return fromJSStr(_7P);}));},_7Q=new T(function(){return B(unCStr("1./("));}),_7R=new T1(0,_7Q),_7S=function(_7T){return new T1(1,new T2(1,_7R,new T2(1,_7T,_1S)));},_7U=new T(function(){return B(unCStr(")+("));}),_7V=new T1(0,_7U),_7W=function(_7X,_7Y){return new T1(1,new T2(1,_3e,new T2(1,_7X,new T2(1,_7V,new T2(1,_7Y,_1S)))));},_7Z=function(_80){return new T1(1,new T2(1,_1P,new T2(1,_80,_1S)));},_81=new T(function(){return B(unCStr(")*("));}),_82=new T1(0,_81),_83=function(_84,_85){return new T1(1,new T2(1,_3e,new T2(1,_84,new T2(1,_82,new T2(1,_85,_1S)))));},_86=function(_87){return E(E(_87).a);},_88=function(_89){return E(E(_89).d);},_8a=function(_8b,_8c){return new F(function(){return A3(_86,_8d,_8b,new T(function(){return B(A2(_88,_8d,_8c));}));});},_8e=new T(function(){return B(unCStr("abs("));}),_8f=new T1(0,_8e),_8g=function(_8h){return new T1(1,new T2(1,_8f,new T2(1,_8h,_1S)));},_8i=function(_8j){return new T1(0,new T(function(){return B(_n(B(_13(0,_8j,_w)),_1T));}));},_8k=new T(function(){return B(unCStr("sign("));}),_8l=new T1(0,_8k),_8m=function(_8n){return new T1(1,new T2(1,_8l,new T2(1,_8n,_1S)));},_8d=new T(function(){return {_:0,a:_7W,b:_8a,c:_83,d:_7Z,e:_8g,f:_8m,g:_8i};}),_8o=new T4(0,_8d,_3h,_7S,_7M),_8p={_:0,a:_8o,b:_2S,c:_2G,d:_2K,e:_33,f:_25,g:_2O,h:_2V,i:_2y,j:_37,k:_2i,l:_2a,m:_2q,n:_2Z,o:_2C,p:_3b,q:_2m,r:_2e,s:_2u},_8q=function(_8r){return E(E(_8r).a);},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v){return E(E(_8v).c);},_8w=function(_8x){return E(E(_8x).b);},_8y=function(_8z){return E(E(_8z).d);},_8A=new T1(0,2),_8B=new T2(0,E(_1o),E(_8A)),_8C=new T1(0,5),_8D=new T1(0,4),_8E=new T2(0,E(_8D),E(_8C)),_8F=function(_8G){return E(E(_8G).e);},_8H=function(_8I,_8J,_8K,_8L){var _8M=B(_8q(_8I)),_8N=B(_8s(_8M)),_8O=new T(function(){var _8P=new T(function(){var _8Q=new T(function(){var _8R=new T(function(){var _8S=new T(function(){var _8T=new T(function(){return B(A3(_86,_8N,new T(function(){return B(A3(_8u,_8N,_8J,_8J));}),new T(function(){return B(A3(_8u,_8N,_8L,_8L));})));});return B(A2(_8F,_8I,_8T));});return B(A3(_8w,_8N,_8S,new T(function(){return B(A2(_8y,_8M,_8E));})));});return B(A3(_8u,_8N,_8R,_8R));});return B(A3(_86,_8N,_8Q,new T(function(){return B(A3(_8u,_8N,_8K,_8K));})));});return B(A2(_8F,_8I,_8P));});return new F(function(){return A3(_8w,_8N,_8O,new T(function(){return B(A2(_8y,_8M,_8B));}));});},_8U=new T(function(){return B(unCStr("x"));}),_8V=new T1(0,_8U),_8W=new T(function(){return B(unCStr("y"));}),_8X=new T1(0,_8W),_8Y=new T(function(){return B(unCStr("z"));}),_8Z=new T1(0,_8Y),_90=new T(function(){return B(_8H(_8p,_8V,_8X,_8Z));}),_91=new T(function(){return toJSStr(B(_1v(_x,_1l,_90)));}),_92=new T3(0,E(_8V),E(_8X),E(_8Z)),_93=new T(function(){return B(unCStr("(/=) is not defined"));}),_94=new T(function(){return B(err(_93));}),_95=new T(function(){return B(unCStr("(==) is not defined"));}),_96=new T(function(){return B(err(_95));}),_97=new T2(0,_96,_94),_98=new T(function(){return B(unCStr("(<) is not defined"));}),_99=new T(function(){return B(err(_98));}),_9a=new T(function(){return B(unCStr("(<=) is not defined"));}),_9b=new T(function(){return B(err(_9a));}),_9c=new T(function(){return B(unCStr("(>) is not defined"));}),_9d=new T(function(){return B(err(_9c));}),_9e=new T(function(){return B(unCStr("(>=) is not defined"));}),_9f=new T(function(){return B(err(_9e));}),_9g=new T(function(){return B(unCStr("compare is not defined"));}),_9h=new T(function(){return B(err(_9g));}),_9i=new T(function(){return B(unCStr("max("));}),_9j=new T1(0,_9i),_9k=function(_9l,_9m){return new T1(1,new T2(1,_9j,new T2(1,_9l,new T2(1,_22,new T2(1,_9m,_1S)))));},_9n=new T(function(){return B(unCStr("min("));}),_9o=new T1(0,_9n),_9p=function(_9q,_9r){return new T1(1,new T2(1,_9o,new T2(1,_9q,new T2(1,_22,new T2(1,_9r,_1S)))));},_9s={_:0,a:_97,b:_9h,c:_99,d:_9b,e:_9d,f:_9f,g:_9k,h:_9p},_9t=new T2(0,_8p,_9s),_9u=function(_9v,_9w){var _9x=E(_9v);return E(_9w);},_9y=function(_9z,_9A){var _9B=E(_9A);return E(_9z);},_9C=function(_9D,_9E){var _9F=E(_9D),_9G=E(_9E);return new T3(0,E(B(A1(_9F.a,_9G.a))),E(B(A1(_9F.b,_9G.b))),E(B(A1(_9F.c,_9G.c))));},_9H=function(_9I,_9J,_9K){return new T3(0,E(_9I),E(_9J),E(_9K));},_9L=function(_9M){return new F(function(){return _9H(_9M,_9M,_9M);});},_9N=function(_9O,_9P){var _9Q=E(_9P),_9R=E(_9O);return new T3(0,E(_9R),E(_9R),E(_9R));},_9S=function(_9T,_9U){var _9V=E(_9U);return new T3(0,E(B(A1(_9T,_9V.a))),E(B(A1(_9T,_9V.b))),E(B(A1(_9T,_9V.c))));},_9W=new T2(0,_9S,_9N),_9X=new T5(0,_9W,_9L,_9C,_9u,_9y),_9Y=new T1(0,0),_9Z=function(_a0){return E(E(_a0).g);},_a1=function(_a2){var _a3=B(A2(_9Z,_a2,_1o)),_a4=B(A2(_9Z,_a2,_9Y));return new T3(0,E(new T3(0,E(_a3),E(_a4),E(_a4))),E(new T3(0,E(_a4),E(_a3),E(_a4))),E(new T3(0,E(_a4),E(_a4),E(_a3))));},_a5=function(_a6){return E(E(_a6).a);},_a7=function(_a8){return E(E(_a8).f);},_a9=function(_aa){return E(E(_aa).b);},_ab=function(_ac){return E(E(_ac).c);},_ad=function(_ae){return E(E(_ae).a);},_af=function(_ag){return E(E(_ag).d);},_ah=function(_ai,_aj,_ak,_al,_am){var _an=new T(function(){return E(E(E(_ai).c).a);}),_ao=new T(function(){var _ap=E(_ai).a,_aq=new T(function(){var _ar=new T(function(){return B(_8q(_an));}),_as=new T(function(){return B(_8s(_ar));}),_at=new T(function(){return B(A2(_af,_an,_aj));}),_au=new T(function(){return B(A3(_a7,_an,_aj,_al));}),_av=function(_aw,_ax){var _ay=new T(function(){var _az=new T(function(){return B(A3(_a9,_ar,new T(function(){return B(A3(_8u,_as,_al,_aw));}),_aj));});return B(A3(_86,_as,_az,new T(function(){return B(A3(_8u,_as,_ax,_at));})));});return new F(function(){return A3(_8u,_as,_au,_ay);});};return B(A3(_ad,B(_a5(_ap)),_av,_ak));});return B(A3(_ab,_ap,_aq,_am));});return new T2(0,new T(function(){return B(A3(_a7,_an,_aj,_al));}),_ao);},_aA=function(_aB,_aC,_aD,_aE){var _aF=E(_aD),_aG=E(_aE),_aH=B(_ah(_aC,_aF.a,_aF.b,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=new T1(0,1),_aJ=function(_aK){return E(E(_aK).l);},_aL=function(_aM,_aN,_aO){var _aP=new T(function(){return E(E(E(_aM).c).a);}),_aQ=new T(function(){var _aR=new T(function(){return B(_8q(_aP));}),_aS=new T(function(){var _aT=B(_8s(_aR)),_aU=new T(function(){var _aV=new T(function(){return B(A3(_8w,_aT,new T(function(){return B(A2(_9Z,_aT,_aI));}),new T(function(){return B(A3(_8u,_aT,_aN,_aN));})));});return B(A2(_8F,_aP,_aV));});return B(A2(_88,_aT,_aU));});return B(A3(_ad,B(_a5(E(_aM).a)),function(_aW){return new F(function(){return A3(_a9,_aR,_aW,_aS);});},_aO));});return new T2(0,new T(function(){return B(A2(_aJ,_aP,_aN));}),_aQ);},_aX=function(_aY,_aZ,_b0){var _b1=E(_b0),_b2=B(_aL(_aZ,_b1.a,_b1.b));return new T2(0,_b2.a,_b2.b);},_b3=function(_b4){return E(E(_b4).r);},_b5=function(_b6,_b7,_b8){var _b9=new T(function(){return E(E(E(_b6).c).a);}),_ba=new T(function(){var _bb=new T(function(){return B(_8q(_b9));}),_bc=new T(function(){var _bd=new T(function(){var _be=B(_8s(_bb));return B(A3(_8w,_be,new T(function(){return B(A3(_8u,_be,_b7,_b7));}),new T(function(){return B(A2(_9Z,_be,_aI));})));});return B(A2(_8F,_b9,_bd));});return B(A3(_ad,B(_a5(E(_b6).a)),function(_bf){return new F(function(){return A3(_a9,_bb,_bf,_bc);});},_b8));});return new T2(0,new T(function(){return B(A2(_b3,_b9,_b7));}),_ba);},_bg=function(_bh,_bi,_bj){var _bk=E(_bj),_bl=B(_b5(_bi,_bk.a,_bk.b));return new T2(0,_bl.a,_bl.b);},_bm=function(_bn){return E(E(_bn).k);},_bo=function(_bp,_bq,_br){var _bs=new T(function(){return E(E(E(_bp).c).a);}),_bt=new T(function(){var _bu=new T(function(){return B(_8q(_bs));}),_bv=new T(function(){var _bw=new T(function(){var _bx=B(_8s(_bu));return B(A3(_8w,_bx,new T(function(){return B(A2(_9Z,_bx,_aI));}),new T(function(){return B(A3(_8u,_bx,_bq,_bq));})));});return B(A2(_8F,_bs,_bw));});return B(A3(_ad,B(_a5(E(_bp).a)),function(_by){return new F(function(){return A3(_a9,_bu,_by,_bv);});},_br));});return new T2(0,new T(function(){return B(A2(_bm,_bs,_bq));}),_bt);},_bz=function(_bA,_bB,_bC){var _bD=E(_bC),_bE=B(_bo(_bB,_bD.a,_bD.b));return new T2(0,_bE.a,_bE.b);},_bF=function(_bG){return E(E(_bG).q);},_bH=function(_bI,_bJ,_bK){var _bL=new T(function(){return E(E(E(_bI).c).a);}),_bM=new T(function(){var _bN=new T(function(){return B(_8q(_bL));}),_bO=new T(function(){var _bP=new T(function(){var _bQ=B(_8s(_bN));return B(A3(_86,_bQ,new T(function(){return B(A3(_8u,_bQ,_bJ,_bJ));}),new T(function(){return B(A2(_9Z,_bQ,_aI));})));});return B(A2(_8F,_bL,_bP));});return B(A3(_ad,B(_a5(E(_bI).a)),function(_bR){return new F(function(){return A3(_a9,_bN,_bR,_bO);});},_bK));});return new T2(0,new T(function(){return B(A2(_bF,_bL,_bJ));}),_bM);},_bS=function(_bT,_bU,_bV){var _bW=E(_bV),_bX=B(_bH(_bU,_bW.a,_bW.b));return new T2(0,_bX.a,_bX.b);},_bY=function(_bZ){return E(E(_bZ).m);},_c0=function(_c1,_c2,_c3){var _c4=new T(function(){return E(E(E(_c1).c).a);}),_c5=new T(function(){var _c6=new T(function(){return B(_8q(_c4));}),_c7=new T(function(){var _c8=B(_8s(_c6));return B(A3(_86,_c8,new T(function(){return B(A2(_9Z,_c8,_aI));}),new T(function(){return B(A3(_8u,_c8,_c2,_c2));})));});return B(A3(_ad,B(_a5(E(_c1).a)),function(_c9){return new F(function(){return A3(_a9,_c6,_c9,_c7);});},_c3));});return new T2(0,new T(function(){return B(A2(_bY,_c4,_c2));}),_c5);},_ca=function(_cb,_cc,_cd){var _ce=E(_cd),_cf=B(_c0(_cc,_ce.a,_ce.b));return new T2(0,_cf.a,_cf.b);},_cg=function(_ch){return E(E(_ch).s);},_ci=function(_cj,_ck,_cl){var _cm=new T(function(){return E(E(E(_cj).c).a);}),_cn=new T(function(){var _co=new T(function(){return B(_8q(_cm));}),_cp=new T(function(){var _cq=B(_8s(_co));return B(A3(_8w,_cq,new T(function(){return B(A2(_9Z,_cq,_aI));}),new T(function(){return B(A3(_8u,_cq,_ck,_ck));})));});return B(A3(_ad,B(_a5(E(_cj).a)),function(_cr){return new F(function(){return A3(_a9,_co,_cr,_cp);});},_cl));});return new T2(0,new T(function(){return B(A2(_cg,_cm,_ck));}),_cn);},_cs=function(_ct,_cu,_cv){var _cw=E(_cv),_cx=B(_ci(_cu,_cw.a,_cw.b));return new T2(0,_cx.a,_cx.b);},_cy=function(_cz){return E(E(_cz).i);},_cA=function(_cB){return E(E(_cB).h);},_cC=function(_cD,_cE,_cF){var _cG=new T(function(){return E(E(E(_cD).c).a);}),_cH=new T(function(){var _cI=new T(function(){return B(_8s(new T(function(){return B(_8q(_cG));})));}),_cJ=new T(function(){return B(A2(_88,_cI,new T(function(){return B(A2(_cA,_cG,_cE));})));});return B(A3(_ad,B(_a5(E(_cD).a)),function(_cK){return new F(function(){return A3(_8u,_cI,_cK,_cJ);});},_cF));});return new T2(0,new T(function(){return B(A2(_cy,_cG,_cE));}),_cH);},_cL=function(_cM,_cN,_cO){var _cP=E(_cO),_cQ=B(_cC(_cN,_cP.a,_cP.b));return new T2(0,_cQ.a,_cQ.b);},_cR=function(_cS){return E(E(_cS).o);},_cT=function(_cU){return E(E(_cU).n);},_cV=function(_cW,_cX,_cY){var _cZ=new T(function(){return E(E(E(_cW).c).a);}),_d0=new T(function(){var _d1=new T(function(){return B(_8s(new T(function(){return B(_8q(_cZ));})));}),_d2=new T(function(){return B(A2(_cT,_cZ,_cX));});return B(A3(_ad,B(_a5(E(_cW).a)),function(_d3){return new F(function(){return A3(_8u,_d1,_d3,_d2);});},_cY));});return new T2(0,new T(function(){return B(A2(_cR,_cZ,_cX));}),_d0);},_d4=function(_d5,_d6,_d7){var _d8=E(_d7),_d9=B(_cV(_d6,_d8.a,_d8.b));return new T2(0,_d9.a,_d9.b);},_da=function(_db){return E(E(_db).c);},_dc=function(_dd,_de,_df){var _dg=new T(function(){return E(E(E(_dd).c).a);}),_dh=new T(function(){var _di=new T(function(){return B(_8s(new T(function(){return B(_8q(_dg));})));}),_dj=new T(function(){return B(A2(_da,_dg,_de));});return B(A3(_ad,B(_a5(E(_dd).a)),function(_dk){return new F(function(){return A3(_8u,_di,_dk,_dj);});},_df));});return new T2(0,new T(function(){return B(A2(_da,_dg,_de));}),_dh);},_dl=function(_dm,_dn,_do){var _dp=E(_do),_dq=B(_dc(_dn,_dp.a,_dp.b));return new T2(0,_dq.a,_dq.b);},_dr=function(_ds,_dt,_du){var _dv=new T(function(){return E(E(E(_ds).c).a);}),_dw=new T(function(){var _dx=new T(function(){return B(_8q(_dv));}),_dy=new T(function(){return B(_8s(_dx));}),_dz=new T(function(){return B(A3(_a9,_dx,new T(function(){return B(A2(_9Z,_dy,_aI));}),_dt));});return B(A3(_ad,B(_a5(E(_ds).a)),function(_dA){return new F(function(){return A3(_8u,_dy,_dA,_dz);});},_du));});return new T2(0,new T(function(){return B(A2(_af,_dv,_dt));}),_dw);},_dB=function(_dC,_dD,_dE){var _dF=E(_dE),_dG=B(_dr(_dD,_dF.a,_dF.b));return new T2(0,_dG.a,_dG.b);},_dH=function(_dI,_dJ,_dK,_dL){var _dM=new T(function(){return E(E(_dJ).c);}),_dN=new T3(0,new T(function(){return E(E(_dJ).a);}),new T(function(){return E(E(_dJ).b);}),new T2(0,new T(function(){return E(E(_dM).a);}),new T(function(){return E(E(_dM).b);})));return new F(function(){return A3(_a9,_dI,new T(function(){var _dO=E(_dL),_dP=B(_dr(_dN,_dO.a,_dO.b));return new T2(0,_dP.a,_dP.b);}),new T(function(){var _dQ=E(_dK),_dR=B(_dr(_dN,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);}));});},_dS=function(_dT){return E(E(_dT).b);},_dU=function(_dV){return E(E(_dV).b);},_dW=function(_dX){var _dY=new T(function(){return E(E(E(_dX).c).a);}),_dZ=new T(function(){return B(A2(_dU,E(_dX).a,new T(function(){return B(A2(_9Z,B(_8s(B(_8q(_dY)))),_L));})));});return new T2(0,new T(function(){return B(_dS(_dY));}),_dZ);},_e0=function(_e1,_e2){var _e3=B(_dW(_e2));return new T2(0,_e3.a,_e3.b);},_e4=function(_e5,_e6,_e7){var _e8=new T(function(){return E(E(E(_e5).c).a);}),_e9=new T(function(){var _ea=new T(function(){return B(_8s(new T(function(){return B(_8q(_e8));})));}),_eb=new T(function(){return B(A2(_cy,_e8,_e6));});return B(A3(_ad,B(_a5(E(_e5).a)),function(_ec){return new F(function(){return A3(_8u,_ea,_ec,_eb);});},_e7));});return new T2(0,new T(function(){return B(A2(_cA,_e8,_e6));}),_e9);},_ed=function(_ee,_ef,_eg){var _eh=E(_eg),_ei=B(_e4(_ef,_eh.a,_eh.b));return new T2(0,_ei.a,_ei.b);},_ej=function(_ek,_el,_em){var _en=new T(function(){return E(E(E(_ek).c).a);}),_eo=new T(function(){var _ep=new T(function(){return B(_8s(new T(function(){return B(_8q(_en));})));}),_eq=new T(function(){return B(A2(_cR,_en,_el));});return B(A3(_ad,B(_a5(E(_ek).a)),function(_er){return new F(function(){return A3(_8u,_ep,_er,_eq);});},_em));});return new T2(0,new T(function(){return B(A2(_cT,_en,_el));}),_eo);},_es=function(_et,_eu,_ev){var _ew=E(_ev),_ex=B(_ej(_eu,_ew.a,_ew.b));return new T2(0,_ex.a,_ex.b);},_ey=new T1(0,2),_ez=function(_eA,_eB,_eC){var _eD=new T(function(){return E(E(E(_eA).c).a);}),_eE=new T(function(){var _eF=new T(function(){return B(_8q(_eD));}),_eG=new T(function(){return B(_8s(_eF));}),_eH=new T(function(){var _eI=new T(function(){return B(A3(_a9,_eF,new T(function(){return B(A2(_9Z,_eG,_aI));}),new T(function(){return B(A2(_9Z,_eG,_ey));})));});return B(A3(_a9,_eF,_eI,new T(function(){return B(A2(_8F,_eD,_eB));})));});return B(A3(_ad,B(_a5(E(_eA).a)),function(_eJ){return new F(function(){return A3(_8u,_eG,_eJ,_eH);});},_eC));});return new T2(0,new T(function(){return B(A2(_8F,_eD,_eB));}),_eE);},_eK=function(_eL,_eM,_eN){var _eO=E(_eN),_eP=B(_ez(_eM,_eO.a,_eO.b));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR){return E(E(_eR).j);},_eS=function(_eT,_eU,_eV){var _eW=new T(function(){return E(E(E(_eT).c).a);}),_eX=new T(function(){var _eY=new T(function(){return B(_8q(_eW));}),_eZ=new T(function(){var _f0=new T(function(){return B(A2(_cy,_eW,_eU));});return B(A3(_8u,B(_8s(_eY)),_f0,_f0));});return B(A3(_ad,B(_a5(E(_eT).a)),function(_f1){return new F(function(){return A3(_a9,_eY,_f1,_eZ);});},_eV));});return new T2(0,new T(function(){return B(A2(_eQ,_eW,_eU));}),_eX);},_f2=function(_f3,_f4,_f5){var _f6=E(_f5),_f7=B(_eS(_f4,_f6.a,_f6.b));return new T2(0,_f7.a,_f7.b);},_f8=function(_f9){return E(E(_f9).p);},_fa=function(_fb,_fc,_fd){var _fe=new T(function(){return E(E(E(_fb).c).a);}),_ff=new T(function(){var _fg=new T(function(){return B(_8q(_fe));}),_fh=new T(function(){var _fi=new T(function(){return B(A2(_cR,_fe,_fc));});return B(A3(_8u,B(_8s(_fg)),_fi,_fi));});return B(A3(_ad,B(_a5(E(_fb).a)),function(_fj){return new F(function(){return A3(_a9,_fg,_fj,_fh);});},_fd));});return new T2(0,new T(function(){return B(A2(_f8,_fe,_fc));}),_ff);},_fk=function(_fl,_fm,_fn){var _fo=E(_fn),_fp=B(_fa(_fm,_fo.a,_fo.b));return new T2(0,_fp.a,_fp.b);},_fq=function(_fr,_fs){return {_:0,a:_fr,b:new T(function(){return B(_e0(_fr,_fs));}),c:function(_ft){return new F(function(){return _dl(_fr,_fs,_ft);});},d:function(_ft){return new F(function(){return _dB(_fr,_fs,_ft);});},e:function(_ft){return new F(function(){return _eK(_fr,_fs,_ft);});},f:function(_fu,_ft){return new F(function(){return _aA(_fr,_fs,_fu,_ft);});},g:function(_fu,_ft){return new F(function(){return _dH(_fr,_fs,_fu,_ft);});},h:function(_ft){return new F(function(){return _ed(_fr,_fs,_ft);});},i:function(_ft){return new F(function(){return _cL(_fr,_fs,_ft);});},j:function(_ft){return new F(function(){return _f2(_fr,_fs,_ft);});},k:function(_ft){return new F(function(){return _bz(_fr,_fs,_ft);});},l:function(_ft){return new F(function(){return _aX(_fr,_fs,_ft);});},m:function(_ft){return new F(function(){return _ca(_fr,_fs,_ft);});},n:function(_ft){return new F(function(){return _es(_fr,_fs,_ft);});},o:function(_ft){return new F(function(){return _d4(_fr,_fs,_ft);});},p:function(_ft){return new F(function(){return _fk(_fr,_fs,_ft);});},q:function(_ft){return new F(function(){return _bS(_fr,_fs,_ft);});},r:function(_ft){return new F(function(){return _bg(_fr,_fs,_ft);});},s:function(_ft){return new F(function(){return _cs(_fr,_fs,_ft);});}};},_fv=function(_fw,_fx,_fy,_fz,_fA){var _fB=new T(function(){return B(_8q(new T(function(){return E(E(E(_fw).c).a);})));}),_fC=new T(function(){var _fD=E(_fw).a,_fE=new T(function(){var _fF=new T(function(){return B(_8s(_fB));}),_fG=new T(function(){return B(A3(_8u,_fF,_fz,_fz));}),_fH=function(_fI,_fJ){var _fK=new T(function(){return B(A3(_8w,_fF,new T(function(){return B(A3(_8u,_fF,_fI,_fz));}),new T(function(){return B(A3(_8u,_fF,_fx,_fJ));})));});return new F(function(){return A3(_a9,_fB,_fK,_fG);});};return B(A3(_ad,B(_a5(_fD)),_fH,_fy));});return B(A3(_ab,_fD,_fE,_fA));});return new T2(0,new T(function(){return B(A3(_a9,_fB,_fx,_fz));}),_fC);},_fL=function(_fM,_fN,_fO,_fP){var _fQ=E(_fO),_fR=E(_fP),_fS=B(_fv(_fN,_fQ.a,_fQ.b,_fR.a,_fR.b));return new T2(0,_fS.a,_fS.b);},_fT=function(_fU,_fV){var _fW=new T(function(){return B(_8q(new T(function(){return E(E(E(_fU).c).a);})));}),_fX=new T(function(){return B(A2(_dU,E(_fU).a,new T(function(){return B(A2(_9Z,B(_8s(_fW)),_L));})));});return new T2(0,new T(function(){return B(A2(_8y,_fW,_fV));}),_fX);},_fY=function(_fZ,_g0,_g1){var _g2=B(_fT(_g0,_g1));return new T2(0,_g2.a,_g2.b);},_g3=function(_g4,_g5,_g6){var _g7=new T(function(){return B(_8q(new T(function(){return E(E(E(_g4).c).a);})));}),_g8=new T(function(){return B(_8s(_g7));}),_g9=new T(function(){var _ga=new T(function(){var _gb=new T(function(){return B(A3(_a9,_g7,new T(function(){return B(A2(_9Z,_g8,_aI));}),new T(function(){return B(A3(_8u,_g8,_g5,_g5));})));});return B(A2(_88,_g8,_gb));});return B(A3(_ad,B(_a5(E(_g4).a)),function(_gc){return new F(function(){return A3(_8u,_g8,_gc,_ga);});},_g6));}),_gd=new T(function(){return B(A3(_a9,_g7,new T(function(){return B(A2(_9Z,_g8,_aI));}),_g5));});return new T2(0,_gd,_g9);},_ge=function(_gf,_gg,_gh){var _gi=E(_gh),_gj=B(_g3(_gg,_gi.a,_gi.b));return new T2(0,_gj.a,_gj.b);},_gk=function(_gl,_gm){return new T4(0,_gl,function(_fu,_ft){return new F(function(){return _fL(_gl,_gm,_fu,_ft);});},function(_ft){return new F(function(){return _ge(_gl,_gm,_ft);});},function(_ft){return new F(function(){return _fY(_gl,_gm,_ft);});});},_gn=function(_go,_gp,_gq,_gr,_gs){var _gt=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_go).c).a);})));})));}),_gu=new T(function(){var _gv=E(_go).a,_gw=new T(function(){var _gx=function(_gy,_gz){return new F(function(){return A3(_86,_gt,new T(function(){return B(A3(_8u,_gt,_gp,_gz));}),new T(function(){return B(A3(_8u,_gt,_gy,_gr));}));});};return B(A3(_ad,B(_a5(_gv)),_gx,_gq));});return B(A3(_ab,_gv,_gw,_gs));});return new T2(0,new T(function(){return B(A3(_8u,_gt,_gp,_gr));}),_gu);},_gA=function(_gB,_gC,_gD){var _gE=E(_gC),_gF=E(_gD),_gG=B(_gn(_gB,_gE.a,_gE.b,_gF.a,_gF.b));return new T2(0,_gG.a,_gG.b);},_gH=function(_gI,_gJ,_gK,_gL,_gM){var _gN=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gI).c).a);})));})));}),_gO=new T(function(){var _gP=E(_gI).a,_gQ=new T(function(){return B(A3(_ad,B(_a5(_gP)),new T(function(){return B(_86(_gN));}),_gK));});return B(A3(_ab,_gP,_gQ,_gM));});return new T2(0,new T(function(){return B(A3(_86,_gN,_gJ,_gL));}),_gO);},_gR=function(_gS,_gT,_gU){var _gV=E(_gT),_gW=E(_gU),_gX=B(_gH(_gS,_gV.a,_gV.b,_gW.a,_gW.b));return new T2(0,_gX.a,_gX.b);},_gY=function(_gZ,_h0,_h1){var _h2=B(_h3(_gZ));return new F(function(){return A3(_86,_h2,_h0,new T(function(){return B(A2(_88,_h2,_h1));}));});},_h4=function(_h5){return E(E(_h5).e);},_h6=function(_h7){return E(E(_h7).f);},_h8=function(_h9,_ha,_hb){var _hc=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_h9).c).a);})));})));}),_hd=new T(function(){var _he=new T(function(){return B(A2(_h6,_hc,_ha));});return B(A3(_ad,B(_a5(E(_h9).a)),function(_hf){return new F(function(){return A3(_8u,_hc,_hf,_he);});},_hb));});return new T2(0,new T(function(){return B(A2(_h4,_hc,_ha));}),_hd);},_hg=function(_hh,_hi){var _hj=E(_hi),_hk=B(_h8(_hh,_hj.a,_hj.b));return new T2(0,_hk.a,_hk.b);},_hl=function(_hm,_hn){var _ho=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hm).c).a);})));})));}),_hp=new T(function(){return B(A2(_dU,E(_hm).a,new T(function(){return B(A2(_9Z,_ho,_L));})));});return new T2(0,new T(function(){return B(A2(_9Z,_ho,_hn));}),_hp);},_hq=function(_hr,_hs){var _ht=B(_hl(_hr,_hs));return new T2(0,_ht.a,_ht.b);},_hu=function(_hv,_hw,_hx){var _hy=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hv).c).a);})));})));}),_hz=new T(function(){return B(A3(_ad,B(_a5(E(_hv).a)),new T(function(){return B(_88(_hy));}),_hx));});return new T2(0,new T(function(){return B(A2(_88,_hy,_hw));}),_hz);},_hA=function(_hB,_hC){var _hD=E(_hC),_hE=B(_hu(_hB,_hD.a,_hD.b));return new T2(0,_hE.a,_hE.b);},_hF=function(_hG,_hH){var _hI=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hG).c).a);})));})));}),_hJ=new T(function(){return B(A2(_dU,E(_hG).a,new T(function(){return B(A2(_9Z,_hI,_L));})));});return new T2(0,new T(function(){return B(A2(_h6,_hI,_hH));}),_hJ);},_hK=function(_hL,_hM){var _hN=B(_hF(_hL,E(_hM).a));return new T2(0,_hN.a,_hN.b);},_h3=function(_hO){return {_:0,a:function(_fu,_ft){return new F(function(){return _gR(_hO,_fu,_ft);});},b:function(_fu,_ft){return new F(function(){return _gY(_hO,_fu,_ft);});},c:function(_fu,_ft){return new F(function(){return _gA(_hO,_fu,_ft);});},d:function(_ft){return new F(function(){return _hA(_hO,_ft);});},e:function(_ft){return new F(function(){return _hg(_hO,_ft);});},f:function(_ft){return new F(function(){return _hK(_hO,_ft);});},g:function(_ft){return new F(function(){return _hq(_hO,_ft);});}};},_hP=function(_hQ){var _hR=new T(function(){return E(E(_hQ).a);}),_hS=new T3(0,_9X,_a1,new T2(0,_hR,new T(function(){return E(E(_hQ).b);}))),_hT=new T(function(){return B(_fq(new T(function(){return B(_gk(new T(function(){return B(_h3(_hS));}),_hS));}),_hS));}),_hU=new T(function(){return B(_8s(new T(function(){return B(_8q(_hR));})));});return function(_hV){var _hW=E(_hV),_hX=B(A2(_9Z,_hU,_1o)),_hY=B(A2(_9Z,_hU,_9Y));return E(B(_8H(_hT,new T2(0,_hW.a,new T3(0,E(_hX),E(_hY),E(_hY))),new T2(0,_hW.b,new T3(0,E(_hY),E(_hX),E(_hY))),new T2(0,_hW.c,new T3(0,E(_hY),E(_hY),E(_hX))))).b);};},_hZ=new T(function(){return B(_hP(_9t));}),_i0=function(_i1,_i2){var _i3=E(_i2);return (_i3._==0)?__Z:new T2(1,_i1,new T2(1,_i3.a,new T(function(){return B(_i0(_i1,_i3.b));})));},_i4=new T(function(){var _i5=B(A1(_hZ,_92));return new T2(1,_i5.a,new T(function(){return B(_i0(_22,new T2(1,_i5.b,new T2(1,_i5.c,_w))));}));}),_i6=new T1(1,_i4),_i7=new T2(1,_i6,_1S),_i8=new T(function(){return B(unCStr("vec3("));}),_i9=new T1(0,_i8),_ia=new T2(1,_i9,_i7),_ib=new T(function(){return toJSStr(B(_1F(_x,_1l,_ia)));}),_ic=function(_id,_ie){while(1){var _if=E(_id);if(!_if._){return E(_ie);}else{var _ig=_ie+1|0;_id=_if.b;_ie=_ig;continue;}}},_ih=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_ii=new T(function(){return B(err(_ih));}),_ij=0,_ik=new T3(0,E(_ij),E(_ij),E(_ij)),_il=new T(function(){return B(unCStr("Negative exponent"));}),_im=new T(function(){return B(err(_il));}),_in=function(_io,_ip,_iq){while(1){if(!(_ip%2)){var _ir=_io*_io,_is=quot(_ip,2);_io=_ir;_ip=_is;continue;}else{var _it=E(_ip);if(_it==1){return _io*_iq;}else{var _ir=_io*_io,_iu=_io*_iq;_io=_ir;_ip=quot(_it-1|0,2);_iq=_iu;continue;}}}},_iv=function(_iw,_ix){while(1){if(!(_ix%2)){var _iy=_iw*_iw,_iz=quot(_ix,2);_iw=_iy;_ix=_iz;continue;}else{var _iA=E(_ix);if(_iA==1){return E(_iw);}else{return new F(function(){return _in(_iw*_iw,quot(_iA-1|0,2),_iw);});}}}},_iB=function(_iC){var _iD=E(_iC);return new F(function(){return Math.log(_iD+(_iD+1)*Math.sqrt((_iD-1)/(_iD+1)));});},_iE=function(_iF){var _iG=E(_iF);return new F(function(){return Math.log(_iG+Math.sqrt(1+_iG*_iG));});},_iH=function(_iI){var _iJ=E(_iI);return 0.5*Math.log((1+_iJ)/(1-_iJ));},_iK=function(_iL,_iM){return Math.log(E(_iM))/Math.log(E(_iL));},_iN=3.141592653589793,_iO=function(_iP){var _iQ=E(_iP);return new F(function(){return _7J(_iQ.a,_iQ.b);});},_iR=function(_iS){return 1/E(_iS);},_iT=function(_iU){var _iV=E(_iU),_iW=E(_iV);return (_iW==0)?E(_7I):(_iW<=0)? -_iW:E(_iV);},_iX=function(_iY){var _iZ=E(_iY);if(!_iZ._){return _iZ.a;}else{return new F(function(){return I_toNumber(_iZ.a);});}},_j0=function(_j1){return new F(function(){return _iX(_j1);});},_j2=1,_j3=-1,_j4=function(_j5){var _j6=E(_j5);return (_j6<=0)?(_j6>=0)?E(_j6):E(_j3):E(_j2);},_j7=function(_j8,_j9){return E(_j8)-E(_j9);},_ja=function(_jb){return  -E(_jb);},_jc=function(_jd,_je){return E(_jd)+E(_je);},_jf=function(_jg,_jh){return E(_jg)*E(_jh);},_ji={_:0,a:_jc,b:_j7,c:_jf,d:_ja,e:_iT,f:_j4,g:_j0},_jj=function(_jk,_jl){return E(_jk)/E(_jl);},_jm=new T4(0,_ji,_jj,_iR,_iO),_jn=function(_jo){return new F(function(){return Math.acos(E(_jo));});},_jp=function(_jq){return new F(function(){return Math.asin(E(_jq));});},_jr=function(_js){return new F(function(){return Math.atan(E(_js));});},_jt=function(_ju){return new F(function(){return Math.cos(E(_ju));});},_jv=function(_jw){return new F(function(){return cosh(E(_jw));});},_jx=function(_jy){return new F(function(){return Math.exp(E(_jy));});},_jz=function(_jA){return new F(function(){return Math.log(E(_jA));});},_jB=function(_jC,_jD){return new F(function(){return Math.pow(E(_jC),E(_jD));});},_jE=function(_jF){return new F(function(){return Math.sin(E(_jF));});},_jG=function(_jH){return new F(function(){return sinh(E(_jH));});},_jI=function(_jJ){return new F(function(){return Math.sqrt(E(_jJ));});},_jK=function(_jL){return new F(function(){return Math.tan(E(_jL));});},_jM=function(_jN){return new F(function(){return tanh(E(_jN));});},_jO={_:0,a:_jm,b:_iN,c:_jx,d:_jz,e:_jI,f:_jB,g:_iK,h:_jE,i:_jt,j:_jK,k:_jp,l:_jn,m:_jr,n:_jG,o:_jv,p:_jM,q:_iE,r:_iB,s:_iH},_jP=function(_jQ,_jR){return (E(_jQ)!=E(_jR))?true:false;},_jS=function(_jT,_jU){return E(_jT)==E(_jU);},_jV=new T2(0,_jS,_jP),_jW=function(_jX,_jY){return E(_jX)<E(_jY);},_jZ=function(_k0,_k1){return E(_k0)<=E(_k1);},_k2=function(_k3,_k4){return E(_k3)>E(_k4);},_k5=function(_k6,_k7){return E(_k6)>=E(_k7);},_k8=function(_k9,_ka){var _kb=E(_k9),_kc=E(_ka);return (_kb>=_kc)?(_kb!=_kc)?2:1:0;},_kd=function(_ke,_kf){var _kg=E(_ke),_kh=E(_kf);return (_kg>_kh)?E(_kg):E(_kh);},_ki=function(_kj,_kk){var _kl=E(_kj),_km=E(_kk);return (_kl>_km)?E(_km):E(_kl);},_kn={_:0,a:_jV,b:_k8,c:_jW,d:_jZ,e:_k2,f:_k5,g:_kd,h:_ki},_ko="dz",_kp="wy",_kq="wx",_kr="dy",_ks="dx",_kt="t",_ku="a",_kv="r",_kw="ly",_kx="lx",_ky="wz",_kz=0,_kA=function(_kB){var _kC=__new(),_kD=_kC,_kE=function(_kF,_){while(1){var _kG=E(_kF);if(!_kG._){return _kz;}else{var _kH=E(_kG.a),_kI=__set(_kD,E(_kH.a),E(_kH.b));_kF=_kG.b;continue;}}},_kJ=B(_kE(_kB,_));return E(_kD);},_kK=function(_kL,_kM,_kN,_kO,_kP,_kQ,_kR,_kS,_kT){return new F(function(){return _kA(new T2(1,new T2(0,_kq,_kL),new T2(1,new T2(0,_kp,_kM),new T2(1,new T2(0,_ky,_kN),new T2(1,new T2(0,_kx,_kO*_kP*Math.cos(_kQ)),new T2(1,new T2(0,_kw,_kO*_kP*Math.sin(_kQ)),new T2(1,new T2(0,_kv,_kO),new T2(1,new T2(0,_ku,_kP),new T2(1,new T2(0,_kt,_kQ),new T2(1,new T2(0,_ks,_kR),new T2(1,new T2(0,_kr,_kS),new T2(1,new T2(0,_ko,_kT),_w))))))))))));});},_kU=function(_kV){var _kW=E(_kV),_kX=E(_kW.a),_kY=E(_kW.b),_kZ=E(_kW.d);return new F(function(){return _kK(_kX.a,_kX.b,_kX.c,E(_kY.a),E(_kY.b),E(_kW.c),_kZ.a,_kZ.b,_kZ.c);});},_l0=function(_l1,_l2){var _l3=E(_l2);return (_l3._==0)?__Z:new T2(1,new T(function(){return B(A1(_l1,_l3.a));}),new T(function(){return B(_l0(_l1,_l3.b));}));},_l4=function(_l5,_l6,_l7){var _l8=__lst2arr(B(_l0(_kU,new T2(1,_l5,new T2(1,_l6,new T2(1,_l7,_w))))));return E(_l8);},_l9=function(_la){var _lb=E(_la);return new F(function(){return _l4(_lb.a,_lb.b,_lb.c);});},_lc=new T2(0,_jO,_kn),_ld=function(_le,_lf,_lg,_lh,_li,_lj,_lk){var _ll=B(_8s(B(_8q(_le)))),_lm=new T(function(){return B(A3(_86,_ll,new T(function(){return B(A3(_8u,_ll,_lf,_li));}),new T(function(){return B(A3(_8u,_ll,_lg,_lj));})));});return new F(function(){return A3(_86,_ll,_lm,new T(function(){return B(A3(_8u,_ll,_lh,_lk));}));});},_ln=function(_lo,_lp,_lq,_lr){var _ls=B(_8q(_lo)),_lt=new T(function(){return B(A2(_8F,_lo,new T(function(){return B(_ld(_lo,_lp,_lq,_lr,_lp,_lq,_lr));})));});return new T3(0,B(A3(_a9,_ls,_lp,_lt)),B(A3(_a9,_ls,_lq,_lt)),B(A3(_a9,_ls,_lr,_lt)));},_lu=function(_lv,_lw,_lx,_ly,_lz,_lA,_lB){var _lC=B(_8u(_lv));return new T3(0,B(A1(B(A1(_lC,_lw)),_lz)),B(A1(B(A1(_lC,_lx)),_lA)),B(A1(B(A1(_lC,_ly)),_lB)));},_lD=function(_lE,_lF,_lG,_lH,_lI,_lJ,_lK){var _lL=B(_86(_lE));return new T3(0,B(A1(B(A1(_lL,_lF)),_lI)),B(A1(B(A1(_lL,_lG)),_lJ)),B(A1(B(A1(_lL,_lH)),_lK)));},_lM=function(_lN,_lO){var _lP=new T(function(){return E(E(_lN).a);}),_lQ=new T(function(){return B(A2(_hP,new T2(0,_lP,new T(function(){return E(E(_lN).b);})),_lO));}),_lR=new T(function(){var _lS=E(_lQ),_lT=B(_ln(_lP,_lS.a,_lS.b,_lS.c));return new T3(0,E(_lT.a),E(_lT.b),E(_lT.c));}),_lU=new T(function(){var _lV=E(_lO),_lW=_lV.a,_lX=_lV.b,_lY=_lV.c,_lZ=E(_lR),_m0=B(_8q(_lP)),_m1=new T(function(){return B(A2(_8F,_lP,new T(function(){var _m2=E(_lQ),_m3=_m2.a,_m4=_m2.b,_m5=_m2.c;return B(_ld(_lP,_m3,_m4,_m5,_m3,_m4,_m5));})));}),_m6=B(A3(_a9,_m0,new T(function(){return B(_8H(_lP,_lW,_lX,_lY));}),_m1)),_m7=B(_8s(_m0)),_m8=B(_lu(_m7,_lZ.a,_lZ.b,_lZ.c,_m6,_m6,_m6)),_m9=B(_88(_m7)),_ma=B(_lD(_m7,_lW,_lX,_lY,B(A1(_m9,_m8.a)),B(A1(_m9,_m8.b)),B(A1(_m9,_m8.c))));return new T3(0,E(_ma.a),E(_ma.b),E(_ma.c));});return new T2(0,_lU,_lR);},_mb=function(_mc){return E(E(_mc).a);},_md=function(_me,_mf,_mg,_mh,_mi,_mj,_mk){var _ml=B(_ld(_me,_mi,_mj,_mk,_mf,_mg,_mh)),_mm=B(_8s(B(_8q(_me)))),_mn=B(_lu(_mm,_mi,_mj,_mk,_ml,_ml,_ml)),_mo=B(_88(_mm));return new F(function(){return _lD(_mm,_mf,_mg,_mh,B(A1(_mo,_mn.a)),B(A1(_mo,_mn.b)),B(A1(_mo,_mn.c)));});},_mp=function(_mq){return E(E(_mq).a);},_mr=function(_ms,_mt,_mu,_mv){var _mw=new T(function(){var _mx=E(_mv),_my=E(_mu),_mz=B(_md(_ms,_mx.a,_mx.b,_mx.c,_my.a,_my.b,_my.c));return new T3(0,E(_mz.a),E(_mz.b),E(_mz.c));}),_mA=new T(function(){return B(A2(_8F,_ms,new T(function(){var _mB=E(_mw),_mC=_mB.a,_mD=_mB.b,_mE=_mB.c;return B(_ld(_ms,_mC,_mD,_mE,_mC,_mD,_mE));})));});if(!B(A3(_mp,B(_mb(_mt)),_mA,new T(function(){return B(A2(_9Z,B(_8s(B(_8q(_ms)))),_9Y));})))){var _mF=E(_mw),_mG=B(_ln(_ms,_mF.a,_mF.b,_mF.c)),_mH=B(A2(_8F,_ms,new T(function(){var _mI=E(_mv),_mJ=_mI.a,_mK=_mI.b,_mL=_mI.c;return B(_ld(_ms,_mJ,_mK,_mL,_mJ,_mK,_mL));}))),_mM=B(_8u(new T(function(){return B(_8s(new T(function(){return B(_8q(_ms));})));})));return new T3(0,B(A1(B(A1(_mM,_mG.a)),_mH)),B(A1(B(A1(_mM,_mG.b)),_mH)),B(A1(B(A1(_mM,_mG.c)),_mH)));}else{var _mN=B(A2(_9Z,B(_8s(B(_8q(_ms)))),_9Y));return new T3(0,_mN,_mN,_mN);}},_mO=new T(function(){var _mP=eval("angleCount"),_mQ=Number(_mP);return jsTrunc(_mQ);}),_mR=new T(function(){return E(_mO);}),_mS=new T(function(){return B(unCStr(": empty list"));}),_mT=new T(function(){return B(unCStr("Prelude."));}),_mU=function(_mV){return new F(function(){return err(B(_n(_mT,new T(function(){return B(_n(_mV,_mS));},1))));});},_mW=new T(function(){return B(unCStr("head"));}),_mX=new T(function(){return B(_mU(_mW));}),_mY=function(_mZ,_n0,_n1){var _n2=E(_mZ);if(!_n2._){return __Z;}else{var _n3=E(_n0);if(!_n3._){return __Z;}else{var _n4=_n3.a,_n5=E(_n1);if(!_n5._){return __Z;}else{var _n6=E(_n5.a),_n7=_n6.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_n2.a),E(_n4),E(_n7));}),new T2(1,new T(function(){return new T3(0,E(_n4),E(_n7),E(_n6.b));}),_w)),new T(function(){return B(_mY(_n2.b,_n3.b,_n5.b));},1));});}}}},_n8=new T(function(){return B(unCStr("tail"));}),_n9=new T(function(){return B(_mU(_n8));}),_na=function(_nb,_nc){var _nd=E(_nb);if(!_nd._){return __Z;}else{var _ne=E(_nc);return (_ne._==0)?__Z:new T2(1,new T2(0,_nd.a,_ne.a),new T(function(){return B(_na(_nd.b,_ne.b));}));}},_nf=function(_ng,_nh){var _ni=E(_ng);if(!_ni._){return __Z;}else{var _nj=E(_nh);if(!_nj._){return __Z;}else{var _nk=E(_ni.a),_nl=_nk.b,_nm=E(_nj.a).b,_nn=new T(function(){var _no=new T(function(){return B(_na(_nm,new T(function(){var _np=E(_nm);if(!_np._){return E(_n9);}else{return E(_np.b);}},1)));},1);return B(_mY(_nl,new T(function(){var _nq=E(_nl);if(!_nq._){return E(_n9);}else{return E(_nq.b);}},1),_no));});return new F(function(){return _n(new T2(1,new T(function(){var _nr=E(_nl);if(!_nr._){return E(_mX);}else{var _ns=E(_nm);if(!_ns._){return E(_mX);}else{return new T3(0,E(_nk.a),E(_nr.a),E(_ns.a));}}}),_nn),new T(function(){return B(_nf(_ni.b,_nj.b));},1));});}}},_nt=new T(function(){return E(_mR)-1;}),_nu=new T1(0,1),_nv=function(_nw,_nx){var _ny=E(_nx),_nz=new T(function(){var _nA=B(_8s(_nw)),_nB=B(_nv(_nw,B(A3(_86,_nA,_ny,new T(function(){return B(A2(_9Z,_nA,_nu));})))));return new T2(1,_nB.a,_nB.b);});return new T2(0,_ny,_nz);},_nC=function(_nD){return E(E(_nD).d);},_nE=new T1(0,2),_nF=function(_nG,_nH){var _nI=E(_nH);if(!_nI._){return __Z;}else{var _nJ=_nI.a;return (!B(A1(_nG,_nJ)))?__Z:new T2(1,_nJ,new T(function(){return B(_nF(_nG,_nI.b));}));}},_nK=function(_nL,_nM,_nN,_nO){var _nP=B(_nv(_nM,_nN)),_nQ=new T(function(){var _nR=B(_8s(_nM)),_nS=new T(function(){return B(A3(_a9,_nM,new T(function(){return B(A2(_9Z,_nR,_nu));}),new T(function(){return B(A2(_9Z,_nR,_nE));})));});return B(A3(_86,_nR,_nO,_nS));});return new F(function(){return _nF(function(_nT){return new F(function(){return A3(_nC,_nL,_nT,_nQ);});},new T2(1,_nP.a,_nP.b));});},_nU=new T(function(){return B(_nK(_kn,_jm,_ij,_nt));}),_nV=function(_nW,_nX){while(1){var _nY=E(_nW);if(!_nY._){return E(_nX);}else{_nW=_nY.b;_nX=_nY.a;continue;}}},_nZ=new T(function(){return B(unCStr("last"));}),_o0=new T(function(){return B(_mU(_nZ));}),_o1=function(_o2){return new F(function(){return _nV(_o2,_o0);});},_o3=function(_o4){return new F(function(){return _o1(E(_o4).b);});},_o5=new T(function(){var _o6=eval("proceedCount"),_o7=Number(_o6);return jsTrunc(_o7);}),_o8=new T(function(){return E(_o5);}),_o9=1,_oa=new T(function(){return B(_nK(_kn,_jm,_o9,_o8));}),_ob=function(_oc,_od,_oe,_of,_og,_oh,_oi,_oj,_ok,_ol,_om,_on,_oo,_op){var _oq=new T(function(){var _or=new T(function(){var _os=E(_ol),_ot=E(_op),_ou=E(_oo),_ov=E(_om),_ow=E(_on),_ox=E(_ok);return new T3(0,_os*_ot-_ou*_ov,_ov*_ow-_ot*_ox,_ox*_ou-_ow*_os);}),_oy=function(_oz){var _oA=new T(function(){var _oB=E(_oz)/E(_mR);return (_oB+_oB)*3.141592653589793;}),_oC=new T(function(){return B(A1(_oc,_oA));}),_oD=new T(function(){var _oE=new T(function(){var _oF=E(_oC)/E(_o8);return new T3(0,E(_oF),E(_oF),E(_oF));}),_oG=function(_oH,_oI){var _oJ=E(_oH);if(!_oJ._){return new T2(0,_w,_oI);}else{var _oK=new T(function(){var _oL=B(_lM(_lc,new T(function(){var _oM=E(_oI),_oN=E(_oM.a),_oO=E(_oM.b),_oP=E(_oE);return new T3(0,E(_oN.a)+E(_oO.a)*E(_oP.a),E(_oN.b)+E(_oO.b)*E(_oP.b),E(_oN.c)+E(_oO.c)*E(_oP.c));}))),_oQ=_oL.a,_oR=new T(function(){var _oS=E(_oL.b),_oT=E(E(_oI).b),_oU=B(_md(_jO,_oT.a,_oT.b,_oT.c,_oS.a,_oS.b,_oS.c)),_oV=B(_ln(_jO,_oU.a,_oU.b,_oU.c));return new T3(0,E(_oV.a),E(_oV.b),E(_oV.c));});return new T2(0,new T(function(){var _oW=E(_oC),_oX=E(_oA);return new T4(0,E(_oQ),E(new T2(0,E(_oJ.a)/E(_o8),E(_oW))),E(_oX),E(_oR));}),new T2(0,_oQ,_oR));}),_oY=new T(function(){var _oZ=B(_oG(_oJ.b,new T(function(){return E(E(_oK).b);})));return new T2(0,_oZ.a,_oZ.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oK).a);}),new T(function(){return E(E(_oY).a);})),new T(function(){return E(E(_oY).b);}));}},_p0=function(_p1,_p2,_p3,_p4,_p5){var _p6=E(_p1);if(!_p6._){return new T2(0,_w,new T2(0,new T3(0,E(_p2),E(_p3),E(_p4)),_p5));}else{var _p7=new T(function(){var _p8=B(_lM(_lc,new T(function(){var _p9=E(_p5),_pa=E(_oE);return new T3(0,E(_p2)+E(_p9.a)*E(_pa.a),E(_p3)+E(_p9.b)*E(_pa.b),E(_p4)+E(_p9.c)*E(_pa.c));}))),_pb=_p8.a,_pc=new T(function(){var _pd=E(_p8.b),_pe=E(_p5),_pf=B(_md(_jO,_pe.a,_pe.b,_pe.c,_pd.a,_pd.b,_pd.c)),_pg=B(_ln(_jO,_pf.a,_pf.b,_pf.c));return new T3(0,E(_pg.a),E(_pg.b),E(_pg.c));});return new T2(0,new T(function(){var _ph=E(_oC),_pi=E(_oA);return new T4(0,E(_pb),E(new T2(0,E(_p6.a)/E(_o8),E(_ph))),E(_pi),E(_pc));}),new T2(0,_pb,_pc));}),_pj=new T(function(){var _pk=B(_oG(_p6.b,new T(function(){return E(E(_p7).b);})));return new T2(0,_pk.a,_pk.b);});return new T2(0,new T2(1,new T(function(){return E(E(_p7).a);}),new T(function(){return E(E(_pj).a);})),new T(function(){return E(E(_pj).b);}));}};return E(B(_p0(_oa,_of,_og,_oh,new T(function(){var _pl=E(_or),_pm=E(_oA)+_oi,_pn=Math.cos(_pm),_po=Math.sin(_pm);return new T3(0,E(_ok)*_pn+E(_pl.a)*_po,E(_ol)*_pn+E(_pl.b)*_po,E(_om)*_pn+E(_pl.c)*_po);}))).a);});return new T2(0,new T(function(){var _pp=E(_oC),_pq=E(_oA);return new T4(0,E(new T3(0,E(_of),E(_og),E(_oh))),E(new T2(0,E(_ij),E(_pp))),E(_pq),E(_ik));}),_oD);};return B(_l0(_oy,_nU));}),_pr=new T(function(){var _ps=new T(function(){var _pt=B(_n(_oq,new T2(1,new T(function(){var _pu=E(_oq);if(!_pu._){return E(_mX);}else{return E(_pu.a);}}),_w)));if(!_pt._){return E(_n9);}else{return E(_pt.b);}},1);return B(_nf(_oq,_ps));});return new T2(0,_pr,new T(function(){return B(_l0(_o3,_oq));}));},_pv=function(_pw,_px,_py,_pz,_pA,_pB,_pC,_pD,_pE,_pF,_pG,_pH,_pI,_pJ,_pK,_pL,_pM){var _pN=B(_lM(_lc,new T3(0,E(_pz),E(_pA),E(_pB)))),_pO=_pN.b,_pP=E(_pN.a),_pQ=B(_mr(_jO,_kn,_pO,new T3(0,E(_pD),E(_pE),E(_pF)))),_pR=E(_pO),_pS=_pR.a,_pT=_pR.b,_pU=_pR.c,_pV=B(_md(_jO,_pH,_pI,_pJ,_pS,_pT,_pU)),_pW=B(_ln(_jO,_pV.a,_pV.b,_pV.c)),_pX=_pW.a,_pY=_pW.b,_pZ=_pW.c,_q0=E(_pC),_q1=new T2(0,E(new T3(0,E(_pQ.a),E(_pQ.b),E(_pQ.c))),E(_pG)),_q2=B(_ob(_pw,_px,_py,_pP.a,_pP.b,_pP.c,_q0,_q1,_pX,_pY,_pZ,_pS,_pT,_pU)),_q3=__lst2arr(B(_l0(_l9,_q2.a))),_q4=__lst2arr(B(_l0(_kU,_q2.b)));return {_:0,a:_pw,b:_px,c:_py,d:new T2(0,E(_pP),E(_q0)),e:_q1,f:new T3(0,E(_pX),E(_pY),E(_pZ)),g:_pR,h:_q3,i:_q4};},_q5=-4,_q6=new T3(0,E(_ij),E(_ij),E(_q5)),_q7=function(_q8){return E(_q6);},_q9=new T(function(){return 6.283185307179586/E(_mR);}),_qa=function(_){return new F(function(){return __jsNull();});},_qb=function(_qc){var _qd=B(A1(_qc,_));return E(_qd);},_qe=new T(function(){return B(_qb(_qa));}),_qf=function(_qg,_qh,_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs){var _qt=function(_qu){var _qv=E(_q9),_qw=2+_qu|0,_qx=_qw-1|0,_qy=(2+_qu)*(1+_qu),_qz=E(_nU);if(!_qz._){return _qv*0;}else{var _qA=_qz.a,_qB=_qz.b,_qC=B(A1(_qg,new T(function(){return 6.283185307179586*E(_qA)/E(_mR);}))),_qD=B(A1(_qg,new T(function(){return 6.283185307179586*(E(_qA)+1)/E(_mR);})));if(_qC!=_qD){if(_qw>=0){var _qE=E(_qw);if(!_qE){var _qF=function(_qG,_qH){while(1){var _qI=B((function(_qJ,_qK){var _qL=E(_qJ);if(!_qL._){return E(_qK);}else{var _qM=_qL.a,_qN=_qL.b,_qO=B(A1(_qg,new T(function(){return 6.283185307179586*E(_qM)/E(_mR);}))),_qP=B(A1(_qg,new T(function(){return 6.283185307179586*(E(_qM)+1)/E(_mR);})));if(_qO!=_qP){var _qQ=_qK+0/(_qO-_qP)/_qy;_qG=_qN;_qH=_qQ;return __continue;}else{if(_qx>=0){var _qR=E(_qx);if(!_qR){var _qQ=_qK+_qw/_qy;_qG=_qN;_qH=_qQ;return __continue;}else{var _qQ=_qK+_qw*B(_iv(_qO,_qR))/_qy;_qG=_qN;_qH=_qQ;return __continue;}}else{return E(_im);}}}})(_qG,_qH));if(_qI!=__continue){return _qI;}}};return _qv*B(_qF(_qB,0/(_qC-_qD)/_qy));}else{var _qS=function(_qT,_qU){while(1){var _qV=B((function(_qW,_qX){var _qY=E(_qW);if(!_qY._){return E(_qX);}else{var _qZ=_qY.a,_r0=_qY.b,_r1=B(A1(_qg,new T(function(){return 6.283185307179586*E(_qZ)/E(_mR);}))),_r2=B(A1(_qg,new T(function(){return 6.283185307179586*(E(_qZ)+1)/E(_mR);})));if(_r1!=_r2){if(_qE>=0){var _r3=_qX+(B(_iv(_r1,_qE))-B(_iv(_r2,_qE)))/(_r1-_r2)/_qy;_qT=_r0;_qU=_r3;return __continue;}else{return E(_im);}}else{if(_qx>=0){var _r4=E(_qx);if(!_r4){var _r3=_qX+_qw/_qy;_qT=_r0;_qU=_r3;return __continue;}else{var _r3=_qX+_qw*B(_iv(_r1,_r4))/_qy;_qT=_r0;_qU=_r3;return __continue;}}else{return E(_im);}}}})(_qT,_qU));if(_qV!=__continue){return _qV;}}};return _qv*B(_qS(_qB,(B(_iv(_qC,_qE))-B(_iv(_qD,_qE)))/(_qC-_qD)/_qy));}}else{return E(_im);}}else{if(_qx>=0){var _r5=E(_qx);if(!_r5){var _r6=function(_r7,_r8){while(1){var _r9=B((function(_ra,_rb){var _rc=E(_ra);if(!_rc._){return E(_rb);}else{var _rd=_rc.a,_re=_rc.b,_rf=B(A1(_qg,new T(function(){return 6.283185307179586*E(_rd)/E(_mR);}))),_rg=B(A1(_qg,new T(function(){return 6.283185307179586*(E(_rd)+1)/E(_mR);})));if(_rf!=_rg){if(_qw>=0){var _rh=E(_qw);if(!_rh){var _ri=_rb+0/(_rf-_rg)/_qy;_r7=_re;_r8=_ri;return __continue;}else{var _ri=_rb+(B(_iv(_rf,_rh))-B(_iv(_rg,_rh)))/(_rf-_rg)/_qy;_r7=_re;_r8=_ri;return __continue;}}else{return E(_im);}}else{var _ri=_rb+_qw/_qy;_r7=_re;_r8=_ri;return __continue;}}})(_r7,_r8));if(_r9!=__continue){return _r9;}}};return _qv*B(_r6(_qB,_qw/_qy));}else{var _rj=function(_rk,_rl){while(1){var _rm=B((function(_rn,_ro){var _rp=E(_rn);if(!_rp._){return E(_ro);}else{var _rq=_rp.a,_rr=_rp.b,_rs=B(A1(_qg,new T(function(){return 6.283185307179586*E(_rq)/E(_mR);}))),_rt=B(A1(_qg,new T(function(){return 6.283185307179586*(E(_rq)+1)/E(_mR);})));if(_rs!=_rt){if(_qw>=0){var _ru=E(_qw);if(!_ru){var _rv=_ro+0/(_rs-_rt)/_qy;_rk=_rr;_rl=_rv;return __continue;}else{var _rv=_ro+(B(_iv(_rs,_ru))-B(_iv(_rt,_ru)))/(_rs-_rt)/_qy;_rk=_rr;_rl=_rv;return __continue;}}else{return E(_im);}}else{if(_r5>=0){var _rv=_ro+_qw*B(_iv(_rs,_r5))/_qy;_rk=_rr;_rl=_rv;return __continue;}else{return E(_im);}}}})(_rk,_rl));if(_rm!=__continue){return _rm;}}};return _qv*B(_rj(_qB,_qw*B(_iv(_qC,_r5))/_qy));}}else{return E(_im);}}}},_rw=E(_qe),_rx=1/(B(_qt(1))*_qh);return new F(function(){return _pv(_qg,_q7,new T2(0,E(new T3(0,E(_rx),E(_rx),E(_rx))),1/(B(_qt(3))*_qh)),_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_ik,_rw,_rw);});},_ry=1,_rz=0,_rA=function(_rB){var _rC=I_decodeDouble(_rB);return new T2(0,new T1(1,_rC.b),_rC.a);},_rD=function(_rE){return new T1(0,_rE);},_rF=function(_rG){var _rH=hs_intToInt64(2147483647),_rI=hs_leInt64(_rG,_rH);if(!_rI){return new T1(1,I_fromInt64(_rG));}else{var _rJ=hs_intToInt64(-2147483648),_rK=hs_geInt64(_rG,_rJ);if(!_rK){return new T1(1,I_fromInt64(_rG));}else{var _rL=hs_int64ToInt(_rG);return new F(function(){return _rD(_rL);});}}},_rM=new T(function(){var _rN=newByteArr(256),_rO=_rN,_=_rO["v"]["i8"][0]=8,_rP=function(_rQ,_rR,_rS,_){while(1){if(_rS>=256){if(_rQ>=256){return E(_);}else{var _rT=imul(2,_rQ)|0,_rU=_rR+1|0,_rV=_rQ;_rQ=_rT;_rR=_rU;_rS=_rV;continue;}}else{var _=_rO["v"]["i8"][_rS]=_rR,_rV=_rS+_rQ|0;_rS=_rV;continue;}}},_=B(_rP(2,0,1,_));return _rO;}),_rW=function(_rX,_rY){var _rZ=hs_int64ToInt(_rX),_s0=E(_rM),_s1=_s0["v"]["i8"][(255&_rZ>>>0)>>>0&4294967295];if(_rY>_s1){if(_s1>=8){var _s2=hs_uncheckedIShiftRA64(_rX,8),_s3=function(_s4,_s5){while(1){var _s6=B((function(_s7,_s8){var _s9=hs_int64ToInt(_s7),_sa=_s0["v"]["i8"][(255&_s9>>>0)>>>0&4294967295];if(_s8>_sa){if(_sa>=8){var _sb=hs_uncheckedIShiftRA64(_s7,8),_sc=_s8-8|0;_s4=_sb;_s5=_sc;return __continue;}else{return new T2(0,new T(function(){var _sd=hs_uncheckedIShiftRA64(_s7,_sa);return B(_rF(_sd));}),_s8-_sa|0);}}else{return new T2(0,new T(function(){var _se=hs_uncheckedIShiftRA64(_s7,_s8);return B(_rF(_se));}),0);}})(_s4,_s5));if(_s6!=__continue){return _s6;}}};return new F(function(){return _s3(_s2,_rY-8|0);});}else{return new T2(0,new T(function(){var _sf=hs_uncheckedIShiftRA64(_rX,_s1);return B(_rF(_sf));}),_rY-_s1|0);}}else{return new T2(0,new T(function(){var _sg=hs_uncheckedIShiftRA64(_rX,_rY);return B(_rF(_sg));}),0);}},_sh=function(_si){var _sj=hs_intToInt64(_si);return E(_sj);},_sk=function(_sl){var _sm=E(_sl);if(!_sm._){return new F(function(){return _sh(_sm.a);});}else{return new F(function(){return I_toInt64(_sm.a);});}},_sn=function(_so){return I_toInt(_so)>>>0;},_sp=function(_sq){var _sr=E(_sq);if(!_sr._){return _sr.a>>>0;}else{return new F(function(){return _sn(_sr.a);});}},_ss=function(_st){var _su=B(_rA(_st)),_sv=_su.a,_sw=_su.b;if(_sw<0){var _sx=function(_sy){if(!_sy){return new T2(0,E(_sv),B(_52(_3k, -_sw)));}else{var _sz=B(_rW(B(_sk(_sv)), -_sw));return new T2(0,E(_sz.a),B(_52(_3k,_sz.b)));}};if(!((B(_sp(_sv))&1)>>>0)){return new F(function(){return _sx(1);});}else{return new F(function(){return _sx(0);});}}else{return new T2(0,B(_52(_sv,_sw)),_3k);}},_sA=function(_sB){var _sC=B(_ss(E(_sB)));return new T2(0,E(_sC.a),E(_sC.b));},_sD=new T3(0,_ji,_kn,_sA),_sE=function(_sF){return E(E(_sF).a);},_sG=function(_sH){return E(E(_sH).a);},_sI=function(_sJ,_sK){if(_sJ<=_sK){var _sL=function(_sM){return new T2(1,_sM,new T(function(){if(_sM!=_sK){return B(_sL(_sM+1|0));}else{return __Z;}}));};return new F(function(){return _sL(_sJ);});}else{return __Z;}},_sN=function(_sO){return new F(function(){return _sI(E(_sO),2147483647);});},_sP=function(_sQ,_sR,_sS){if(_sS<=_sR){var _sT=new T(function(){var _sU=_sR-_sQ|0,_sV=function(_sW){return (_sW>=(_sS-_sU|0))?new T2(1,_sW,new T(function(){return B(_sV(_sW+_sU|0));})):new T2(1,_sW,_w);};return B(_sV(_sR));});return new T2(1,_sQ,_sT);}else{return (_sS<=_sQ)?new T2(1,_sQ,_w):__Z;}},_sX=function(_sY,_sZ,_t0){if(_t0>=_sZ){var _t1=new T(function(){var _t2=_sZ-_sY|0,_t3=function(_t4){return (_t4<=(_t0-_t2|0))?new T2(1,_t4,new T(function(){return B(_t3(_t4+_t2|0));})):new T2(1,_t4,_w);};return B(_t3(_sZ));});return new T2(1,_sY,_t1);}else{return (_t0>=_sY)?new T2(1,_sY,_w):__Z;}},_t5=function(_t6,_t7){if(_t7<_t6){return new F(function(){return _sP(_t6,_t7,-2147483648);});}else{return new F(function(){return _sX(_t6,_t7,2147483647);});}},_t8=function(_t9,_ta){return new F(function(){return _t5(E(_t9),E(_ta));});},_tb=function(_tc,_td,_te){if(_td<_tc){return new F(function(){return _sP(_tc,_td,_te);});}else{return new F(function(){return _sX(_tc,_td,_te);});}},_tf=function(_tg,_th,_ti){return new F(function(){return _tb(E(_tg),E(_th),E(_ti));});},_tj=function(_tk,_tl){return new F(function(){return _sI(E(_tk),E(_tl));});},_tm=function(_tn){return E(_tn);},_to=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_tp=new T(function(){return B(err(_to));}),_tq=function(_tr){var _ts=E(_tr);return (_ts==(-2147483648))?E(_tp):_ts-1|0;},_tt=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_tu=new T(function(){return B(err(_tt));}),_tv=function(_tw){var _tx=E(_tw);return (_tx==2147483647)?E(_tu):_tx+1|0;},_ty={_:0,a:_tv,b:_tq,c:_tm,d:_tm,e:_sN,f:_t8,g:_tj,h:_tf},_tz=function(_tA,_tB){if(_tA<=0){if(_tA>=0){return new F(function(){return quot(_tA,_tB);});}else{if(_tB<=0){return new F(function(){return quot(_tA,_tB);});}else{return quot(_tA+1|0,_tB)-1|0;}}}else{if(_tB>=0){if(_tA>=0){return new F(function(){return quot(_tA,_tB);});}else{if(_tB<=0){return new F(function(){return quot(_tA,_tB);});}else{return quot(_tA+1|0,_tB)-1|0;}}}else{return quot(_tA-1|0,_tB)-1|0;}}},_tC=0,_tD=new T(function(){return B(_4p(_tC));}),_tE=new T(function(){return die(_tD);}),_tF=function(_tG,_tH){var _tI=E(_tH);switch(_tI){case -1:var _tJ=E(_tG);if(_tJ==(-2147483648)){return E(_tE);}else{return new F(function(){return _tz(_tJ,-1);});}break;case 0:return E(_4t);default:return new F(function(){return _tz(_tG,_tI);});}},_tK=function(_tL,_tM){return new F(function(){return _tF(E(_tL),E(_tM));});},_tN=0,_tO=new T2(0,_tE,_tN),_tP=function(_tQ,_tR){var _tS=E(_tQ),_tT=E(_tR);switch(_tT){case -1:var _tU=E(_tS);if(_tU==(-2147483648)){return E(_tO);}else{if(_tU<=0){if(_tU>=0){var _tV=quotRemI(_tU,-1);return new T2(0,_tV.a,_tV.b);}else{var _tW=quotRemI(_tU,-1);return new T2(0,_tW.a,_tW.b);}}else{var _tX=quotRemI(_tU-1|0,-1);return new T2(0,_tX.a-1|0,(_tX.b+(-1)|0)+1|0);}}break;case 0:return E(_4t);default:if(_tS<=0){if(_tS>=0){var _tY=quotRemI(_tS,_tT);return new T2(0,_tY.a,_tY.b);}else{if(_tT<=0){var _tZ=quotRemI(_tS,_tT);return new T2(0,_tZ.a,_tZ.b);}else{var _u0=quotRemI(_tS+1|0,_tT);return new T2(0,_u0.a-1|0,(_u0.b+_tT|0)-1|0);}}}else{if(_tT>=0){if(_tS>=0){var _u1=quotRemI(_tS,_tT);return new T2(0,_u1.a,_u1.b);}else{if(_tT<=0){var _u2=quotRemI(_tS,_tT);return new T2(0,_u2.a,_u2.b);}else{var _u3=quotRemI(_tS+1|0,_tT);return new T2(0,_u3.a-1|0,(_u3.b+_tT|0)-1|0);}}}else{var _u4=quotRemI(_tS-1|0,_tT);return new T2(0,_u4.a-1|0,(_u4.b+_tT|0)+1|0);}}}},_u5=function(_u6,_u7){var _u8=_u6%_u7;if(_u6<=0){if(_u6>=0){return E(_u8);}else{if(_u7<=0){return E(_u8);}else{var _u9=E(_u8);return (_u9==0)?0:_u9+_u7|0;}}}else{if(_u7>=0){if(_u6>=0){return E(_u8);}else{if(_u7<=0){return E(_u8);}else{var _ua=E(_u8);return (_ua==0)?0:_ua+_u7|0;}}}else{var _ub=E(_u8);return (_ub==0)?0:_ub+_u7|0;}}},_uc=function(_ud,_ue){var _uf=E(_ue);switch(_uf){case -1:return E(_tN);case 0:return E(_4t);default:return new F(function(){return _u5(E(_ud),_uf);});}},_ug=function(_uh,_ui){var _uj=E(_uh),_uk=E(_ui);switch(_uk){case -1:var _ul=E(_uj);if(_ul==(-2147483648)){return E(_tE);}else{return new F(function(){return quot(_ul,-1);});}break;case 0:return E(_4t);default:return new F(function(){return quot(_uj,_uk);});}},_um=function(_un,_uo){var _up=E(_un),_uq=E(_uo);switch(_uq){case -1:var _ur=E(_up);if(_ur==(-2147483648)){return E(_tO);}else{var _us=quotRemI(_ur,-1);return new T2(0,_us.a,_us.b);}break;case 0:return E(_4t);default:var _ut=quotRemI(_up,_uq);return new T2(0,_ut.a,_ut.b);}},_uu=function(_uv,_uw){var _ux=E(_uw);switch(_ux){case -1:return E(_tN);case 0:return E(_4t);default:return E(_uv)%_ux;}},_uy=function(_uz){return new F(function(){return _rD(E(_uz));});},_uA=function(_uB){return new T2(0,E(B(_rD(E(_uB)))),E(_nu));},_uC=function(_uD,_uE){return imul(E(_uD),E(_uE))|0;},_uF=function(_uG,_uH){return E(_uG)+E(_uH)|0;},_uI=function(_uJ,_uK){return E(_uJ)-E(_uK)|0;},_uL=function(_uM){var _uN=E(_uM);return (_uN<0)? -_uN:E(_uN);},_uO=function(_uP){return new F(function(){return _4G(_uP);});},_uQ=function(_uR){return  -E(_uR);},_uS=-1,_uT=0,_uU=1,_uV=function(_uW){var _uX=E(_uW);return (_uX>=0)?(E(_uX)==0)?E(_uT):E(_uU):E(_uS);},_uY={_:0,a:_uF,b:_uI,c:_uC,d:_uQ,e:_uL,f:_uV,g:_uO},_uZ=function(_v0,_v1){return E(_v0)==E(_v1);},_v2=function(_v3,_v4){return E(_v3)!=E(_v4);},_v5=new T2(0,_uZ,_v2),_v6=function(_v7,_v8){var _v9=E(_v7),_va=E(_v8);return (_v9>_va)?E(_v9):E(_va);},_vb=function(_vc,_vd){var _ve=E(_vc),_vf=E(_vd);return (_ve>_vf)?E(_vf):E(_ve);},_vg=function(_vh,_vi){return (_vh>=_vi)?(_vh!=_vi)?2:1:0;},_vj=function(_vk,_vl){return new F(function(){return _vg(E(_vk),E(_vl));});},_vm=function(_vn,_vo){return E(_vn)>=E(_vo);},_vp=function(_vq,_vr){return E(_vq)>E(_vr);},_vs=function(_vt,_vu){return E(_vt)<=E(_vu);},_vv=function(_vw,_vx){return E(_vw)<E(_vx);},_vy={_:0,a:_v5,b:_vj,c:_vv,d:_vs,e:_vp,f:_vm,g:_v6,h:_vb},_vz=new T3(0,_uY,_vy,_uA),_vA={_:0,a:_vz,b:_ty,c:_ug,d:_uu,e:_tK,f:_uc,g:_um,h:_tP,i:_uy},_vB=new T1(0,2),_vC=function(_vD,_vE){while(1){var _vF=E(_vD);if(!_vF._){var _vG=_vF.a,_vH=E(_vE);if(!_vH._){var _vI=_vH.a;if(!(imul(_vG,_vI)|0)){return new T1(0,imul(_vG,_vI)|0);}else{_vD=new T1(1,I_fromInt(_vG));_vE=new T1(1,I_fromInt(_vI));continue;}}else{_vD=new T1(1,I_fromInt(_vG));_vE=_vH;continue;}}else{var _vJ=E(_vE);if(!_vJ._){_vD=_vF;_vE=new T1(1,I_fromInt(_vJ.a));continue;}else{return new T1(1,I_mul(_vF.a,_vJ.a));}}}},_vK=function(_vL,_vM,_vN){while(1){if(!(_vM%2)){var _vO=B(_vC(_vL,_vL)),_vP=quot(_vM,2);_vL=_vO;_vM=_vP;continue;}else{var _vQ=E(_vM);if(_vQ==1){return new F(function(){return _vC(_vL,_vN);});}else{var _vO=B(_vC(_vL,_vL)),_vR=B(_vC(_vL,_vN));_vL=_vO;_vM=quot(_vQ-1|0,2);_vN=_vR;continue;}}}},_vS=function(_vT,_vU){while(1){if(!(_vU%2)){var _vV=B(_vC(_vT,_vT)),_vW=quot(_vU,2);_vT=_vV;_vU=_vW;continue;}else{var _vX=E(_vU);if(_vX==1){return E(_vT);}else{return new F(function(){return _vK(B(_vC(_vT,_vT)),quot(_vX-1|0,2),_vT);});}}}},_vY=function(_vZ){return E(E(_vZ).b);},_w0=function(_w1){return E(E(_w1).c);},_w2=new T1(0,0),_w3=function(_w4){return E(E(_w4).d);},_w5=function(_w6,_w7){var _w8=B(_sE(_w6)),_w9=new T(function(){return B(_sG(_w8));}),_wa=new T(function(){return B(A3(_w3,_w6,_w7,new T(function(){return B(A2(_9Z,_w9,_nE));})));});return new F(function(){return A3(_mp,B(_mb(B(_vY(_w8)))),_wa,new T(function(){return B(A2(_9Z,_w9,_w2));}));});},_wb=new T(function(){return B(unCStr("Negative exponent"));}),_wc=new T(function(){return B(err(_wb));}),_wd=function(_we){return E(E(_we).c);},_wf=function(_wg,_wh,_wi,_wj){var _wk=B(_sE(_wh)),_wl=new T(function(){return B(_sG(_wk));}),_wm=B(_vY(_wk));if(!B(A3(_w0,_wm,_wj,new T(function(){return B(A2(_9Z,_wl,_w2));})))){if(!B(A3(_mp,B(_mb(_wm)),_wj,new T(function(){return B(A2(_9Z,_wl,_w2));})))){var _wn=new T(function(){return B(A2(_9Z,_wl,_nE));}),_wo=new T(function(){return B(A2(_9Z,_wl,_nu));}),_wp=B(_mb(_wm)),_wq=function(_wr,_ws,_wt){while(1){var _wu=B((function(_wv,_ww,_wx){if(!B(_w5(_wh,_ww))){if(!B(A3(_mp,_wp,_ww,_wo))){var _wy=new T(function(){return B(A3(_wd,_wh,new T(function(){return B(A3(_8w,_wl,_ww,_wo));}),_wn));});_wr=new T(function(){return B(A3(_8u,_wg,_wv,_wv));});_ws=_wy;_wt=new T(function(){return B(A3(_8u,_wg,_wv,_wx));});return __continue;}else{return new F(function(){return A3(_8u,_wg,_wv,_wx);});}}else{var _wz=_wx;_wr=new T(function(){return B(A3(_8u,_wg,_wv,_wv));});_ws=new T(function(){return B(A3(_wd,_wh,_ww,_wn));});_wt=_wz;return __continue;}})(_wr,_ws,_wt));if(_wu!=__continue){return _wu;}}},_wA=function(_wB,_wC){while(1){var _wD=B((function(_wE,_wF){if(!B(_w5(_wh,_wF))){if(!B(A3(_mp,_wp,_wF,_wo))){var _wG=new T(function(){return B(A3(_wd,_wh,new T(function(){return B(A3(_8w,_wl,_wF,_wo));}),_wn));});return new F(function(){return _wq(new T(function(){return B(A3(_8u,_wg,_wE,_wE));}),_wG,_wE);});}else{return E(_wE);}}else{_wB=new T(function(){return B(A3(_8u,_wg,_wE,_wE));});_wC=new T(function(){return B(A3(_wd,_wh,_wF,_wn));});return __continue;}})(_wB,_wC));if(_wD!=__continue){return _wD;}}};return new F(function(){return _wA(_wi,_wj);});}else{return new F(function(){return A2(_9Z,_wg,_nu);});}}else{return E(_wc);}},_wH=new T(function(){return B(err(_wb));}),_wI=function(_wJ,_wK){var _wL=B(_rA(_wK)),_wM=_wL.a,_wN=_wL.b,_wO=new T(function(){return B(_sG(new T(function(){return B(_sE(_wJ));})));});if(_wN<0){var _wP= -_wN;if(_wP>=0){var _wQ=E(_wP);if(!_wQ){var _wR=E(_nu);}else{var _wR=B(_vS(_vB,_wQ));}if(!B(_4y(_wR,_51))){var _wS=B(_4S(_wM,_wR));return new T2(0,new T(function(){return B(A2(_9Z,_wO,_wS.a));}),new T(function(){return B(_4u(_wS.b,_wN));}));}else{return E(_4t);}}else{return E(_wH);}}else{var _wT=new T(function(){var _wU=new T(function(){return B(_wf(_wO,_vA,new T(function(){return B(A2(_9Z,_wO,_vB));}),_wN));});return B(A3(_8u,_wO,new T(function(){return B(A2(_9Z,_wO,_wM));}),_wU));});return new T2(0,_wT,_7I);}},_wV=function(_wW,_wX){var _wY=B(_wI(_wW,E(_wX))),_wZ=_wY.a;if(E(_wY.b)<=0){return E(_wZ);}else{var _x0=B(_sG(B(_sE(_wW))));return new F(function(){return A3(_86,_x0,_wZ,new T(function(){return B(A2(_9Z,_x0,_3k));}));});}},_x1=function(_x2,_x3){var _x4=B(_wI(_x2,E(_x3))),_x5=_x4.a;if(E(_x4.b)>=0){return E(_x5);}else{var _x6=B(_sG(B(_sE(_x2))));return new F(function(){return A3(_8w,_x6,_x5,new T(function(){return B(A2(_9Z,_x6,_3k));}));});}},_x7=function(_x8,_x9){var _xa=B(_wI(_x8,E(_x9)));return new T2(0,_xa.a,_xa.b);},_xb=function(_xc,_xd){var _xe=B(_wI(_xc,_xd)),_xf=_xe.a,_xg=E(_xe.b),_xh=new T(function(){var _xi=B(_sG(B(_sE(_xc))));if(_xg>=0){return B(A3(_86,_xi,_xf,new T(function(){return B(A2(_9Z,_xi,_3k));})));}else{return B(A3(_8w,_xi,_xf,new T(function(){return B(A2(_9Z,_xi,_3k));})));}}),_xj=function(_xk){var _xl=_xk-0.5;return (_xl>=0)?(E(_xl)==0)?(!B(_w5(_xc,_xf)))?E(_xh):E(_xf):E(_xh):E(_xf);},_xm=E(_xg);if(!_xm){return new F(function(){return _xj(0);});}else{if(_xm<=0){var _xn= -_xm-0.5;return (_xn>=0)?(E(_xn)==0)?(!B(_w5(_xc,_xf)))?E(_xh):E(_xf):E(_xh):E(_xf);}else{return new F(function(){return _xj(_xm);});}}},_xo=function(_xp,_xq){return new F(function(){return _xb(_xp,E(_xq));});},_xr=function(_xs,_xt){return E(B(_wI(_xs,E(_xt))).a);},_xu={_:0,a:_sD,b:_jm,c:_x7,d:_xr,e:_xo,f:_wV,g:_x1},_xv=new T1(0,1),_xw=function(_xx,_xy){var _xz=E(_xx);return new T2(0,_xz,new T(function(){var _xA=B(_xw(B(_4J(_xz,_xy)),_xy));return new T2(1,_xA.a,_xA.b);}));},_xB=function(_xC){var _xD=B(_xw(_xC,_xv));return new T2(1,_xD.a,_xD.b);},_xE=function(_xF,_xG){var _xH=B(_xw(_xF,new T(function(){return B(_6W(_xG,_xF));})));return new T2(1,_xH.a,_xH.b);},_xI=new T1(0,0),_xJ=function(_xK,_xL){var _xM=E(_xK);if(!_xM._){var _xN=_xM.a,_xO=E(_xL);return (_xO._==0)?_xN>=_xO.a:I_compareInt(_xO.a,_xN)<=0;}else{var _xP=_xM.a,_xQ=E(_xL);return (_xQ._==0)?I_compareInt(_xP,_xQ.a)>=0:I_compare(_xP,_xQ.a)>=0;}},_xR=function(_xS,_xT,_xU){if(!B(_xJ(_xT,_xI))){var _xV=function(_xW){return (!B(_S(_xW,_xU)))?new T2(1,_xW,new T(function(){return B(_xV(B(_4J(_xW,_xT))));})):__Z;};return new F(function(){return _xV(_xS);});}else{var _xX=function(_xY){return (!B(_5c(_xY,_xU)))?new T2(1,_xY,new T(function(){return B(_xX(B(_4J(_xY,_xT))));})):__Z;};return new F(function(){return _xX(_xS);});}},_xZ=function(_y0,_y1,_y2){return new F(function(){return _xR(_y0,B(_6W(_y1,_y0)),_y2);});},_y3=function(_y4,_y5){return new F(function(){return _xR(_y4,_xv,_y5);});},_y6=function(_y7){return new F(function(){return _4G(_y7);});},_y8=function(_y9){return new F(function(){return _6W(_y9,_xv);});},_ya=function(_yb){return new F(function(){return _4J(_yb,_xv);});},_yc=function(_yd){return new F(function(){return _rD(E(_yd));});},_ye={_:0,a:_ya,b:_y8,c:_yc,d:_y6,e:_xB,f:_xE,g:_y3,h:_xZ},_yf=function(_yg,_yh){while(1){var _yi=E(_yg);if(!_yi._){var _yj=E(_yi.a);if(_yj==(-2147483648)){_yg=new T1(1,I_fromInt(-2147483648));continue;}else{var _yk=E(_yh);if(!_yk._){return new T1(0,B(_tz(_yj,_yk.a)));}else{_yg=new T1(1,I_fromInt(_yj));_yh=_yk;continue;}}}else{var _yl=_yi.a,_ym=E(_yh);return (_ym._==0)?new T1(1,I_div(_yl,I_fromInt(_ym.a))):new T1(1,I_div(_yl,_ym.a));}}},_yn=function(_yo,_yp){if(!B(_4y(_yp,_w2))){return new F(function(){return _yf(_yo,_yp);});}else{return E(_4t);}},_yq=function(_yr,_ys){while(1){var _yt=E(_yr);if(!_yt._){var _yu=E(_yt.a);if(_yu==(-2147483648)){_yr=new T1(1,I_fromInt(-2147483648));continue;}else{var _yv=E(_ys);if(!_yv._){var _yw=_yv.a;return new T2(0,new T1(0,B(_tz(_yu,_yw))),new T1(0,B(_u5(_yu,_yw))));}else{_yr=new T1(1,I_fromInt(_yu));_ys=_yv;continue;}}}else{var _yx=E(_ys);if(!_yx._){_yr=_yt;_ys=new T1(1,I_fromInt(_yx.a));continue;}else{var _yy=I_divMod(_yt.a,_yx.a);return new T2(0,new T1(1,_yy.a),new T1(1,_yy.b));}}}},_yz=function(_yA,_yB){if(!B(_4y(_yB,_w2))){var _yC=B(_yq(_yA,_yB));return new T2(0,_yC.a,_yC.b);}else{return E(_4t);}},_yD=function(_yE,_yF){while(1){var _yG=E(_yE);if(!_yG._){var _yH=E(_yG.a);if(_yH==(-2147483648)){_yE=new T1(1,I_fromInt(-2147483648));continue;}else{var _yI=E(_yF);if(!_yI._){return new T1(0,B(_u5(_yH,_yI.a)));}else{_yE=new T1(1,I_fromInt(_yH));_yF=_yI;continue;}}}else{var _yJ=_yG.a,_yK=E(_yF);return (_yK._==0)?new T1(1,I_mod(_yJ,I_fromInt(_yK.a))):new T1(1,I_mod(_yJ,_yK.a));}}},_yL=function(_yM,_yN){if(!B(_4y(_yN,_w2))){return new F(function(){return _yD(_yM,_yN);});}else{return E(_4t);}},_yO=function(_yP,_yQ){while(1){var _yR=E(_yP);if(!_yR._){var _yS=E(_yR.a);if(_yS==(-2147483648)){_yP=new T1(1,I_fromInt(-2147483648));continue;}else{var _yT=E(_yQ);if(!_yT._){return new T1(0,quot(_yS,_yT.a));}else{_yP=new T1(1,I_fromInt(_yS));_yQ=_yT;continue;}}}else{var _yU=_yR.a,_yV=E(_yQ);return (_yV._==0)?new T1(0,I_toInt(I_quot(_yU,I_fromInt(_yV.a)))):new T1(1,I_quot(_yU,_yV.a));}}},_yW=function(_yX,_yY){if(!B(_4y(_yY,_w2))){return new F(function(){return _yO(_yX,_yY);});}else{return E(_4t);}},_yZ=function(_z0,_z1){if(!B(_4y(_z1,_w2))){var _z2=B(_4S(_z0,_z1));return new T2(0,_z2.a,_z2.b);}else{return E(_4t);}},_z3=function(_z4,_z5){while(1){var _z6=E(_z4);if(!_z6._){var _z7=E(_z6.a);if(_z7==(-2147483648)){_z4=new T1(1,I_fromInt(-2147483648));continue;}else{var _z8=E(_z5);if(!_z8._){return new T1(0,_z7%_z8.a);}else{_z4=new T1(1,I_fromInt(_z7));_z5=_z8;continue;}}}else{var _z9=_z6.a,_za=E(_z5);return (_za._==0)?new T1(1,I_rem(_z9,I_fromInt(_za.a))):new T1(1,I_rem(_z9,_za.a));}}},_zb=function(_zc,_zd){if(!B(_4y(_zd,_w2))){return new F(function(){return _z3(_zc,_zd);});}else{return E(_4t);}},_ze=function(_zf){return E(_zf);},_zg=function(_zh){return E(_zh);},_zi=function(_zj){var _zk=E(_zj);if(!_zk._){var _zl=E(_zk.a);return (_zl==(-2147483648))?E(_7A):(_zl<0)?new T1(0, -_zl):E(_zk);}else{var _zm=_zk.a;return (I_compareInt(_zm,0)>=0)?E(_zk):new T1(1,I_negate(_zm));}},_zn=new T1(0,0),_zo=new T1(0,-1),_zp=function(_zq){var _zr=E(_zq);if(!_zr._){var _zs=_zr.a;return (_zs>=0)?(E(_zs)==0)?E(_zn):E(_5k):E(_zo);}else{var _zt=I_compareInt(_zr.a,0);return (_zt<=0)?(E(_zt)==0)?E(_zn):E(_zo):E(_5k);}},_zu={_:0,a:_4J,b:_6W,c:_vC,d:_7B,e:_zi,f:_zp,g:_zg},_zv=function(_zw,_zx){var _zy=E(_zw);if(!_zy._){var _zz=_zy.a,_zA=E(_zx);return (_zA._==0)?_zz!=_zA.a:(I_compareInt(_zA.a,_zz)==0)?false:true;}else{var _zB=_zy.a,_zC=E(_zx);return (_zC._==0)?(I_compareInt(_zB,_zC.a)==0)?false:true:(I_compare(_zB,_zC.a)==0)?false:true;}},_zD=new T2(0,_4y,_zv),_zE=function(_zF,_zG){return (!B(_6H(_zF,_zG)))?E(_zF):E(_zG);},_zH=function(_zI,_zJ){return (!B(_6H(_zI,_zJ)))?E(_zJ):E(_zI);},_zK={_:0,a:_zD,b:_3l,c:_S,d:_6H,e:_5c,f:_xJ,g:_zE,h:_zH},_zL=function(_zM){return new T2(0,E(_zM),E(_nu));},_zN=new T3(0,_zu,_zK,_zL),_zO={_:0,a:_zN,b:_ye,c:_yW,d:_zb,e:_yn,f:_yL,g:_yZ,h:_yz,i:_ze},_zP=function(_zQ){return E(E(_zQ).b);},_zR=function(_zS){return E(E(_zS).g);},_zT=new T1(0,1),_zU=function(_zV,_zW,_zX){var _zY=B(_zP(_zV)),_zZ=B(_8s(_zY)),_A0=new T(function(){var _A1=new T(function(){var _A2=new T(function(){var _A3=new T(function(){return B(A3(_zR,_zV,_zO,new T(function(){return B(A3(_a9,_zY,_zW,_zX));})));});return B(A2(_9Z,_zZ,_A3));}),_A4=new T(function(){return B(A2(_88,_zZ,new T(function(){return B(A2(_9Z,_zZ,_zT));})));});return B(A3(_8u,_zZ,_A4,_A2));});return B(A3(_8u,_zZ,_A1,_zX));});return new F(function(){return A3(_86,_zZ,_zW,_A0);});},_A5=1.5707963267948966,_A6=function(_A7){return 0.2/Math.cos(B(_zU(_xu,_A7,_A5))-0.7853981633974483);},_A8=new T(function(){var _A9=B(_qf(_A6,1.2,_rz,_rz,_ry,_rz,_rz,_rz,_rz,_rz,_ry,_ry,_ry));return {_:0,a:E(_A9.a),b:E(_A9.b),c:E(_A9.c),d:E(_A9.d),e:E(_A9.e),f:E(_A9.f),g:E(_A9.g),h:_A9.h,i:_A9.i};}),_Aa=0,_Ab=0.3,_Ac=function(_Ad){return E(_Ab);},_Ae=new T(function(){var _Af=B(_qf(_Ac,1.2,_ry,_rz,_ry,_rz,_rz,_rz,_rz,_rz,_ry,_ry,_ry));return {_:0,a:E(_Af.a),b:E(_Af.b),c:E(_Af.c),d:E(_Af.d),e:E(_Af.e),f:E(_Af.f),g:E(_Af.g),h:_Af.h,i:_Af.i};}),_Ag=new T(function(){var _Ah=B(_qf(_Ac,1.2,_ry,_ry,_rz,_rz,_rz,_rz,_rz,_rz,_ry,_ry,_ry));return {_:0,a:E(_Ah.a),b:E(_Ah.b),c:E(_Ah.c),d:E(_Ah.d),e:E(_Ah.e),f:E(_Ah.f),g:E(_Ah.g),h:_Ah.h,i:_Ah.i};}),_Ai=2,_Aj=function(_Ak){return 0.3/Math.cos(B(_zU(_xu,_Ak,_A5))-0.7853981633974483);},_Al=new T(function(){var _Am=B(_qf(_Aj,1.2,_Ai,_ry,_ry,_rz,_rz,_rz,_rz,_rz,_ry,_ry,_ry));return {_:0,a:E(_Am.a),b:E(_Am.b),c:E(_Am.c),d:E(_Am.d),e:E(_Am.e),f:E(_Am.f),g:E(_Am.g),h:_Am.h,i:_Am.i};}),_An=0.5,_Ao=new T(function(){var _Ap=B(_qf(_Ac,1.2,_rz,_ry,_An,_rz,_rz,_rz,_rz,_rz,_ry,_ry,_ry));return {_:0,a:E(_Ap.a),b:E(_Ap.b),c:E(_Ap.c),d:E(_Ap.d),e:E(_Ap.e),f:E(_Ap.f),g:E(_Ap.g),h:_Ap.h,i:_Ap.i};}),_Aq=new T2(1,_Ao,_w),_Ar=new T2(1,_Al,_Aq),_As=new T2(1,_Ag,_Ar),_At=new T2(1,_Ae,_As),_Au=new T2(1,_A8,_At),_Av=new T(function(){return B(unCStr("Negative range size"));}),_Aw=new T(function(){return B(err(_Av));}),_Ax=function(_){var _Ay=B(_ic(_Au,0))-1|0,_Az=function(_AA){if(_AA>=0){var _AB=newArr(_AA,_ii),_AC=_AB,_AD=E(_AA);if(!_AD){return new T4(0,E(_Aa),E(_Ay),0,_AC);}else{var _AE=function(_AF,_AG,_){while(1){var _AH=E(_AF);if(!_AH._){return E(_);}else{var _=_AC[_AG]=_AH.a;if(_AG!=(_AD-1|0)){var _AI=_AG+1|0;_AF=_AH.b;_AG=_AI;continue;}else{return E(_);}}}},_=B((function(_AJ,_AK,_AL,_){var _=_AC[_AL]=_AJ;if(_AL!=(_AD-1|0)){return new F(function(){return _AE(_AK,_AL+1|0,_);});}else{return E(_);}})(_A8,_At,0,_));return new T4(0,E(_Aa),E(_Ay),_AD,_AC);}}else{return E(_Aw);}};if(0>_Ay){return new F(function(){return _Az(0);});}else{return new F(function(){return _Az(_Ay+1|0);});}},_AM=function(_AN){var _AO=B(A1(_AN,_));return E(_AO);},_AP=new T(function(){return B(_AM(_Ax));}),_AQ="outline",_AR="polygon",_AS=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_AT=new T(function(){return B(err(_AS));}),_AU=new T(function(){return eval("__strict(drawObjects)");}),_AV=new T(function(){return eval("__strict(draw)");}),_AW=function(_AX,_AY){var _AZ=jsShowI(_AX);return new F(function(){return _n(fromJSStr(_AZ),_AY);});},_B0=function(_B1,_B2,_B3){if(_B2>=0){return new F(function(){return _AW(_B2,_B3);});}else{if(_B1<=6){return new F(function(){return _AW(_B2,_B3);});}else{return new T2(1,_11,new T(function(){var _B4=jsShowI(_B2);return B(_n(fromJSStr(_B4),new T2(1,_10,_B3)));}));}}},_B5=new T(function(){return B(unCStr(")"));}),_B6=function(_B7,_B8){var _B9=new T(function(){var _Ba=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_B0(0,_B7,_w)),_B5));})));},1);return B(_n(B(_B0(0,_B8,_w)),_Ba));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_B9)));});},_Bb=new T2(1,_kz,_w),_Bc=function(_Bd){return E(_Bd);},_Be=function(_Bf){return E(_Bf);},_Bg=function(_Bh,_Bi){return E(_Bi);},_Bj=function(_Bk,_Bl){return E(_Bk);},_Bm=function(_Bn){return E(_Bn);},_Bo=new T2(0,_Bm,_Bj),_Bp=function(_Bq,_Br){return E(_Bq);},_Bs=new T5(0,_Bo,_Be,_Bc,_Bg,_Bp),_Bt="flipped2",_Bu="flipped1",_Bv="c1y",_Bw="c1x",_Bx="w2z",_By="w2y",_Bz="w2x",_BA="w1z",_BB="w1y",_BC="w1x",_BD="d2z",_BE="d2y",_BF="d2x",_BG="d1z",_BH="d1y",_BI="d1x",_BJ="c2y",_BK="c2x",_BL=function(_BM,_){var _BN=__get(_BM,E(_BC)),_BO=__get(_BM,E(_BB)),_BP=__get(_BM,E(_BA)),_BQ=__get(_BM,E(_Bz)),_BR=__get(_BM,E(_By)),_BS=__get(_BM,E(_Bx)),_BT=__get(_BM,E(_Bw)),_BU=__get(_BM,E(_Bv)),_BV=__get(_BM,E(_BK)),_BW=__get(_BM,E(_BJ)),_BX=__get(_BM,E(_BI)),_BY=__get(_BM,E(_BH)),_BZ=__get(_BM,E(_BG)),_C0=__get(_BM,E(_BF)),_C1=__get(_BM,E(_BE)),_C2=__get(_BM,E(_BD)),_C3=__get(_BM,E(_Bu)),_C4=__get(_BM,E(_Bt));return {_:0,a:E(new T3(0,E(_BN),E(_BO),E(_BP))),b:E(new T3(0,E(_BQ),E(_BR),E(_BS))),c:E(new T2(0,E(_BT),E(_BU))),d:E(new T2(0,E(_BV),E(_BW))),e:E(new T3(0,E(_BX),E(_BY),E(_BZ))),f:E(new T3(0,E(_C0),E(_C1),E(_C2))),g:E(_C3),h:E(_C4)};},_C5=function(_C6,_){var _C7=E(_C6);if(!_C7._){return _w;}else{var _C8=B(_BL(E(_C7.a),_)),_C9=B(_C5(_C7.b,_));return new T2(1,_C8,_C9);}},_Ca=function(_Cb){var _Cc=E(_Cb);return (E(_Cc.b)-E(_Cc.a)|0)+1|0;},_Cd=function(_Ce,_Cf){var _Cg=E(_Ce),_Ch=E(_Cf);return (E(_Cg.a)>_Ch)?false:_Ch<=E(_Cg.b);},_Ci=function(_Cj){return new F(function(){return _B0(0,E(_Cj),_w);});},_Ck=function(_Cl,_Cm,_Cn){return new F(function(){return _B0(E(_Cl),E(_Cm),_Cn);});},_Co=function(_Cp,_Cq){return new F(function(){return _B0(0,E(_Cp),_Cq);});},_Cr=function(_Cs,_Ct){return new F(function(){return _49(_Co,_Cs,_Ct);});},_Cu=new T3(0,_Ck,_Ci,_Cr),_Cv=0,_Cw=function(_Cx,_Cy,_Cz){return new F(function(){return A1(_Cx,new T2(1,_46,new T(function(){return B(A1(_Cy,_Cz));})));});},_CA=new T(function(){return B(unCStr("foldr1"));}),_CB=new T(function(){return B(_mU(_CA));}),_CC=function(_CD,_CE){var _CF=E(_CE);if(!_CF._){return E(_CB);}else{var _CG=_CF.a,_CH=E(_CF.b);if(!_CH._){return E(_CG);}else{return new F(function(){return A2(_CD,_CG,new T(function(){return B(_CC(_CD,_CH));}));});}}},_CI=new T(function(){return B(unCStr(" out of range "));}),_CJ=new T(function(){return B(unCStr("}.index: Index "));}),_CK=new T(function(){return B(unCStr("Ix{"));}),_CL=new T2(1,_10,_w),_CM=new T2(1,_10,_CL),_CN=0,_CO=function(_CP){return E(E(_CP).a);},_CQ=function(_CR,_CS,_CT,_CU,_CV){var _CW=new T(function(){var _CX=new T(function(){var _CY=new T(function(){var _CZ=new T(function(){var _D0=new T(function(){return B(A3(_CC,_Cw,new T2(1,new T(function(){return B(A3(_CO,_CT,_CN,_CU));}),new T2(1,new T(function(){return B(A3(_CO,_CT,_CN,_CV));}),_w)),_CM));});return B(_n(_CI,new T2(1,_11,new T2(1,_11,_D0))));});return B(A(_CO,[_CT,_Cv,_CS,new T2(1,_10,_CZ)]));});return B(_n(_CJ,new T2(1,_11,_CY)));},1);return B(_n(_CR,_CX));},1);return new F(function(){return err(B(_n(_CK,_CW)));});},_D1=function(_D2,_D3,_D4,_D5,_D6){return new F(function(){return _CQ(_D2,_D3,_D6,_D4,_D5);});},_D7=function(_D8,_D9,_Da,_Db){var _Dc=E(_Da);return new F(function(){return _D1(_D8,_D9,_Dc.a,_Dc.b,_Db);});},_Dd=function(_De,_Df,_Dg,_Dh){return new F(function(){return _D7(_Dh,_Dg,_Df,_De);});},_Di=new T(function(){return B(unCStr("Int"));}),_Dj=function(_Dk,_Dl){return new F(function(){return _Dd(_Cu,_Dl,_Dk,_Di);});},_Dm=function(_Dn,_Do){var _Dp=E(_Dn),_Dq=E(_Dp.a),_Dr=E(_Do);if(_Dq>_Dr){return new F(function(){return _Dj(_Dr,_Dp);});}else{if(_Dr>E(_Dp.b)){return new F(function(){return _Dj(_Dr,_Dp);});}else{return _Dr-_Dq|0;}}},_Ds=function(_Dt){var _Du=E(_Dt);return new F(function(){return _tj(_Du.a,_Du.b);});},_Dv=function(_Dw){var _Dx=E(_Dw),_Dy=E(_Dx.a),_Dz=E(_Dx.b);return (_Dy>_Dz)?E(_Cv):(_Dz-_Dy|0)+1|0;},_DA=function(_DB,_DC){return new F(function(){return _uI(_DC,E(_DB).a);});},_DD={_:0,a:_vy,b:_Ds,c:_Dm,d:_DA,e:_Cd,f:_Dv,g:_Ca},_DE=function(_DF,_DG,_){while(1){var _DH=B((function(_DI,_DJ,_){var _DK=E(_DI);if(!_DK._){return new T2(0,_kz,_DJ);}else{var _DL=B(A2(_DK.a,_DJ,_));_DF=_DK.b;_DG=new T(function(){return E(E(_DL).b);});return __continue;}})(_DF,_DG,_));if(_DH!=__continue){return _DH;}}},_DM=function(_DN,_DO){return new T2(1,_DN,_DO);},_DP=function(_DQ,_DR){var _DS=E(_DR);return new T2(0,_DS.a,_DS.b);},_DT=function(_DU){return E(E(_DU).f);},_DV=function(_DW,_DX,_DY){var _DZ=E(_DX),_E0=_DZ.a,_E1=_DZ.b,_E2=function(_){var _E3=B(A2(_DT,_DW,_DZ));if(_E3>=0){var _E4=newArr(_E3,_ii),_E5=_E4,_E6=E(_E3);if(!_E6){return new T(function(){return new T4(0,E(_E0),E(_E1),0,_E5);});}else{var _E7=function(_E8,_E9,_){while(1){var _Ea=E(_E8);if(!_Ea._){return E(_);}else{var _=_E5[_E9]=_Ea.a;if(_E9!=(_E6-1|0)){var _Eb=_E9+1|0;_E8=_Ea.b;_E9=_Eb;continue;}else{return E(_);}}}},_=B(_E7(_DY,0,_));return new T(function(){return new T4(0,E(_E0),E(_E1),_E6,_E5);});}}else{return E(_Aw);}};return new F(function(){return _AM(_E2);});},_Ec=function(_Ed,_Ee,_Ef,_Eg){var _Eh=new T(function(){var _Ei=E(_Eg),_Ej=_Ei.c-1|0,_Ek=new T(function(){return B(A2(_dU,_Ee,_w));});if(0<=_Ej){var _El=new T(function(){return B(_a5(_Ee));}),_Em=function(_En){var _Eo=new T(function(){var _Ep=new T(function(){return B(A1(_Ef,new T(function(){return E(_Ei.d[_En]);})));});return B(A3(_ad,_El,_DM,_Ep));});return new F(function(){return A3(_ab,_Ee,_Eo,new T(function(){if(_En!=_Ej){return B(_Em(_En+1|0));}else{return E(_Ek);}}));});};return B(_Em(0));}else{return E(_Ek);}}),_Eq=new T(function(){return B(_DP(_Ed,_Eg));});return new F(function(){return A3(_ad,B(_a5(_Ee)),function(_Er){return new F(function(){return _DV(_Ed,_Eq,_Er);});},_Eh);});},_Es=function(_Et,_Eu,_Ev,_Ew,_Ex,_Ey,_Ez,_EA,_EB){var _EC=B(_8u(_Et));return new T2(0,new T3(0,E(B(A1(B(A1(_EC,_Eu)),_Ey))),E(B(A1(B(A1(_EC,_Ev)),_Ez))),E(B(A1(B(A1(_EC,_Ew)),_EA)))),B(A1(B(A1(_EC,_Ex)),_EB)));},_ED=function(_EE,_EF,_EG,_EH,_EI,_EJ,_EK,_EL,_EM){var _EN=B(_86(_EE));return new T2(0,new T3(0,E(B(A1(B(A1(_EN,_EF)),_EJ))),E(B(A1(B(A1(_EN,_EG)),_EK))),E(B(A1(B(A1(_EN,_EH)),_EL)))),B(A1(B(A1(_EN,_EI)),_EM)));},_EO=1.0e-2,_EP=function(_EQ,_ER,_ES,_ET,_EU,_EV,_EW,_EX,_EY,_EZ,_F0,_F1,_F2,_F3,_F4,_F5,_F6){var _F7=B(_Es(_ji,_EX,_EY,_EZ,_F0,_EO,_EO,_EO,_EO)),_F8=E(_F7.a),_F9=B(_ED(_ji,_ET,_EU,_EV,_EW,_F8.a,_F8.b,_F8.c,_F7.b)),_Fa=E(_F9.a);return new F(function(){return _pv(_EQ,_ER,_ES,_Fa.a,_Fa.b,_Fa.c,_F9.b,_EX,_EY,_EZ,_F0,_F1,_F2,_F3,_F4,_F5,_F6);});},_Fb=function(_Fc){var _Fd=E(_Fc),_Fe=E(_Fd.d),_Ff=E(_Fe.a),_Fg=E(_Fd.e),_Fh=E(_Fg.a),_Fi=E(_Fd.f),_Fj=B(_EP(_Fd.a,_Fd.b,_Fd.c,_Ff.a,_Ff.b,_Ff.c,_Fe.b,_Fh.a,_Fh.b,_Fh.c,_Fg.b,_Fi.a,_Fi.b,_Fi.c,_Fd.g,_Fd.h,_Fd.i));return {_:0,a:E(_Fj.a),b:E(_Fj.b),c:E(_Fj.c),d:E(_Fj.d),e:E(_Fj.e),f:E(_Fj.f),g:E(_Fj.g),h:_Fj.h,i:_Fj.i};},_Fk=function(_Fl,_Fm,_Fn,_Fo,_Fp,_Fq,_Fr,_Fs,_Ft){var _Fu=B(_8s(B(_8q(_Fl))));return new F(function(){return A3(_86,_Fu,new T(function(){return B(_ld(_Fl,_Fm,_Fn,_Fo,_Fq,_Fr,_Fs));}),new T(function(){return B(A3(_8u,_Fu,_Fp,_Ft));}));});},_Fv=new T(function(){return B(unCStr("base"));}),_Fw=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Fx=new T(function(){return B(unCStr("IOException"));}),_Fy=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fv,_Fw,_Fx),_Fz=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fy,_w,_w),_FA=function(_FB){return E(_Fz);},_FC=function(_FD){var _FE=E(_FD);return new F(function(){return _3G(B(_3E(_FE.a)),_FA,_FE.b);});},_FF=new T(function(){return B(unCStr(": "));}),_FG=new T(function(){return B(unCStr(")"));}),_FH=new T(function(){return B(unCStr(" ("));}),_FI=new T(function(){return B(unCStr("interrupted"));}),_FJ=new T(function(){return B(unCStr("system error"));}),_FK=new T(function(){return B(unCStr("unsatisified constraints"));}),_FL=new T(function(){return B(unCStr("user error"));}),_FM=new T(function(){return B(unCStr("permission denied"));}),_FN=new T(function(){return B(unCStr("illegal operation"));}),_FO=new T(function(){return B(unCStr("end of file"));}),_FP=new T(function(){return B(unCStr("resource exhausted"));}),_FQ=new T(function(){return B(unCStr("resource busy"));}),_FR=new T(function(){return B(unCStr("does not exist"));}),_FS=new T(function(){return B(unCStr("already exists"));}),_FT=new T(function(){return B(unCStr("resource vanished"));}),_FU=new T(function(){return B(unCStr("timeout"));}),_FV=new T(function(){return B(unCStr("unsupported operation"));}),_FW=new T(function(){return B(unCStr("hardware fault"));}),_FX=new T(function(){return B(unCStr("inappropriate type"));}),_FY=new T(function(){return B(unCStr("invalid argument"));}),_FZ=new T(function(){return B(unCStr("failed"));}),_G0=new T(function(){return B(unCStr("protocol error"));}),_G1=function(_G2,_G3){switch(E(_G2)){case 0:return new F(function(){return _n(_FS,_G3);});break;case 1:return new F(function(){return _n(_FR,_G3);});break;case 2:return new F(function(){return _n(_FQ,_G3);});break;case 3:return new F(function(){return _n(_FP,_G3);});break;case 4:return new F(function(){return _n(_FO,_G3);});break;case 5:return new F(function(){return _n(_FN,_G3);});break;case 6:return new F(function(){return _n(_FM,_G3);});break;case 7:return new F(function(){return _n(_FL,_G3);});break;case 8:return new F(function(){return _n(_FK,_G3);});break;case 9:return new F(function(){return _n(_FJ,_G3);});break;case 10:return new F(function(){return _n(_G0,_G3);});break;case 11:return new F(function(){return _n(_FZ,_G3);});break;case 12:return new F(function(){return _n(_FY,_G3);});break;case 13:return new F(function(){return _n(_FX,_G3);});break;case 14:return new F(function(){return _n(_FW,_G3);});break;case 15:return new F(function(){return _n(_FV,_G3);});break;case 16:return new F(function(){return _n(_FU,_G3);});break;case 17:return new F(function(){return _n(_FT,_G3);});break;default:return new F(function(){return _n(_FI,_G3);});}},_G4=new T(function(){return B(unCStr("}"));}),_G5=new T(function(){return B(unCStr("{handle: "));}),_G6=function(_G7,_G8,_G9,_Ga,_Gb,_Gc){var _Gd=new T(function(){var _Ge=new T(function(){var _Gf=new T(function(){var _Gg=E(_Ga);if(!_Gg._){return E(_Gc);}else{var _Gh=new T(function(){return B(_n(_Gg,new T(function(){return B(_n(_FG,_Gc));},1)));},1);return B(_n(_FH,_Gh));}},1);return B(_G1(_G8,_Gf));}),_Gi=E(_G9);if(!_Gi._){return E(_Ge);}else{return B(_n(_Gi,new T(function(){return B(_n(_FF,_Ge));},1)));}}),_Gj=E(_Gb);if(!_Gj._){var _Gk=E(_G7);if(!_Gk._){return E(_Gd);}else{var _Gl=E(_Gk.a);if(!_Gl._){var _Gm=new T(function(){var _Gn=new T(function(){return B(_n(_G4,new T(function(){return B(_n(_FF,_Gd));},1)));},1);return B(_n(_Gl.a,_Gn));},1);return new F(function(){return _n(_G5,_Gm);});}else{var _Go=new T(function(){var _Gp=new T(function(){return B(_n(_G4,new T(function(){return B(_n(_FF,_Gd));},1)));},1);return B(_n(_Gl.a,_Gp));},1);return new F(function(){return _n(_G5,_Go);});}}}else{return new F(function(){return _n(_Gj.a,new T(function(){return B(_n(_FF,_Gd));},1));});}},_Gq=function(_Gr){var _Gs=E(_Gr);return new F(function(){return _G6(_Gs.a,_Gs.b,_Gs.c,_Gs.d,_Gs.f,_w);});},_Gt=function(_Gu,_Gv,_Gw){var _Gx=E(_Gv);return new F(function(){return _G6(_Gx.a,_Gx.b,_Gx.c,_Gx.d,_Gx.f,_Gw);});},_Gy=function(_Gz,_GA){var _GB=E(_Gz);return new F(function(){return _G6(_GB.a,_GB.b,_GB.c,_GB.d,_GB.f,_GA);});},_GC=function(_GD,_GE){return new F(function(){return _49(_Gy,_GD,_GE);});},_GF=new T3(0,_Gt,_Gq,_GC),_GG=new T(function(){return new T5(0,_FA,_GF,_GH,_FC,_Gq);}),_GH=function(_GI){return new T2(0,_GG,_GI);},_GJ=__Z,_GK=7,_GL=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_GM=new T6(0,_GJ,_GK,_w,_GL,_GJ,_GJ),_GN=new T(function(){return B(_GH(_GM));}),_GO=function(_){return new F(function(){return die(_GN);});},_GP=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_GQ=new T6(0,_GJ,_GK,_w,_GP,_GJ,_GJ),_GR=new T(function(){return B(_GH(_GQ));}),_GS=function(_){return new F(function(){return die(_GR);});},_GT=function(_GU,_){return new T2(0,_w,_GU);},_GV=0.6,_GW=1,_GX=new T(function(){return B(unCStr(")"));}),_GY=function(_GZ,_H0){var _H1=new T(function(){var _H2=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_B0(0,_GZ,_w)),_GX));})));},1);return B(_n(B(_B0(0,_H0,_w)),_H2));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_H1)));});},_H3=function(_H4,_H5){var _H6=new T(function(){var _H7=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_B0(0,_H5,_w)),_GX));})));},1);return B(_n(B(_B0(0,_H4,_w)),_H7));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_H6)));});},_H8=function(_H9){var _Ha=E(_H9);if(!_Ha._){return E(_GT);}else{var _Hb=new T(function(){return B(_H8(_Ha.b));}),_Hc=function(_Hd){var _He=E(_Hd);if(!_He._){return E(_Hb);}else{var _Hf=_He.a,_Hg=new T(function(){return B(_Hc(_He.b));}),_Hh=new T(function(){return 0.1*E(E(_Hf).e)/1.0e-2;}),_Hi=new T(function(){var _Hj=E(_Hf);if(_Hj.a!=_Hj.b){return E(_GW);}else{return E(_GV);}}),_Hk=function(_Hl,_){var _Hm=E(_Hl),_Hn=_Hm.c,_Ho=_Hm.d,_Hp=E(_Hm.a),_Hq=E(_Hm.b),_Hr=E(_Hf),_Hs=_Hr.a,_Ht=_Hr.b,_Hu=E(_Hr.c),_Hv=_Hu.b,_Hw=E(_Hu.a),_Hx=_Hw.a,_Hy=_Hw.b,_Hz=_Hw.c,_HA=E(_Hr.d),_HB=_HA.b,_HC=E(_HA.a),_HD=_HC.a,_HE=_HC.b,_HF=_HC.c;if(_Hp>_Hs){return new F(function(){return _GS(_);});}else{if(_Hs>_Hq){return new F(function(){return _GS(_);});}else{if(_Hp>_Ht){return new F(function(){return _GO(_);});}else{if(_Ht>_Hq){return new F(function(){return _GO(_);});}else{var _HG=_Hs-_Hp|0;if(0>_HG){return new F(function(){return _GY(_Hn,_HG);});}else{if(_HG>=_Hn){return new F(function(){return _GY(_Hn,_HG);});}else{var _HH=E(_Ho[_HG]),_HI=E(_HH.c),_HJ=_HI.b,_HK=E(_HI.a),_HL=_HK.a,_HM=_HK.b,_HN=_HK.c,_HO=E(_HH.e),_HP=E(_HO.a),_HQ=B(_Es(_ji,_Hx,_Hy,_Hz,_Hv,_HL,_HM,_HN,_HJ)),_HR=E(_HQ.a),_HS=B(_Es(_ji,_HR.a,_HR.b,_HR.c,_HQ.b,_Hx,_Hy,_Hz,_Hv)),_HT=E(_HS.a),_HU=_Ht-_Hp|0;if(0>_HU){return new F(function(){return _H3(_HU,_Hn);});}else{if(_HU>=_Hn){return new F(function(){return _H3(_HU,_Hn);});}else{var _HV=E(_Ho[_HU]),_HW=E(_HV.c),_HX=_HW.b,_HY=E(_HW.a),_HZ=_HY.a,_I0=_HY.b,_I1=_HY.c,_I2=E(_HV.e),_I3=E(_I2.a),_I4=B(_Es(_ji,_HD,_HE,_HF,_HB,_HZ,_I0,_I1,_HX)),_I5=E(_I4.a),_I6=B(_Es(_ji,_I5.a,_I5.b,_I5.c,_I4.b,_HD,_HE,_HF,_HB)),_I7=E(_I6.a),_I8=E(_HT.a)+E(_HT.b)+E(_HT.c)+E(_HS.b)+E(_I7.a)+E(_I7.b)+E(_I7.c)+E(_I6.b);if(!_I8){var _I9=B(A2(_Hg,_Hm,_));return new T2(0,new T2(1,_kz,new T(function(){return E(E(_I9).a);})),new T(function(){return E(E(_I9).b);}));}else{var _Ia=new T(function(){return  -((B(_Fk(_jO,_HP.a,_HP.b,_HP.c,_HO.b,_Hx,_Hy,_Hz,_Hv))-B(_Fk(_jO,_I3.a,_I3.b,_I3.c,_I2.b,_HD,_HE,_HF,_HB))-E(_Hh))/_I8);}),_Ib=function(_Ic,_Id,_Ie,_If,_){var _Ig=new T(function(){var _Ih=function(_Ii,_Ij,_Ik,_Il,_Im){if(_Ii>_Ht){return E(_Im);}else{if(_Ht>_Ij){return E(_Im);}else{var _In=function(_){var _Io=newArr(_Ik,_ii),_Ip=_Io,_Iq=function(_Ir,_){while(1){if(_Ir!=_Ik){var _=_Ip[_Ir]=_Il[_Ir],_Is=_Ir+1|0;_Ir=_Is;continue;}else{return E(_);}}},_=B(_Iq(0,_)),_It=_Ht-_Ii|0;if(0>_It){return new F(function(){return _H3(_It,_Ik);});}else{if(_It>=_Ik){return new F(function(){return _H3(_It,_Ik);});}else{var _=_Ip[_It]=new T(function(){var _Iu=E(_Il[_It]),_Iv=E(_Iu.e),_Iw=E(_Iv.a),_Ix=B(_Es(_ji,_HZ,_I0,_I1,_HX,_HD,_HE,_HF,_HB)),_Iy=E(_Ix.a),_Iz=E(_Ia)*E(_Hi),_IA=B(_Es(_ji,_Iy.a,_Iy.b,_Iy.c,_Ix.b,_Iz,_Iz,_Iz,_Iz)),_IB=E(_IA.a),_IC=B(_ED(_ji,_Iw.a,_Iw.b,_Iw.c,_Iv.b, -E(_IB.a), -E(_IB.b), -E(_IB.c), -E(_IA.b)));return {_:0,a:E(_Iu.a),b:E(_Iu.b),c:E(_Iu.c),d:E(_Iu.d),e:E(new T2(0,E(_IC.a),E(_IC.b))),f:E(_Iu.f),g:E(_Iu.g),h:_Iu.h,i:_Iu.i};});return new T4(0,E(_Ii),E(_Ij),_Ik,_Ip);}}};return new F(function(){return _AM(_In);});}}};if(_Ic>_Hs){return B(_Ih(_Ic,_Id,_Ie,_If,new T4(0,E(_Ic),E(_Id),_Ie,_If)));}else{if(_Hs>_Id){return B(_Ih(_Ic,_Id,_Ie,_If,new T4(0,E(_Ic),E(_Id),_Ie,_If)));}else{var _ID=function(_){var _IE=newArr(_Ie,_ii),_IF=_IE,_IG=function(_IH,_){while(1){if(_IH!=_Ie){var _=_IF[_IH]=_If[_IH],_II=_IH+1|0;_IH=_II;continue;}else{return E(_);}}},_=B(_IG(0,_)),_IJ=_Hs-_Ic|0;if(0>_IJ){return new F(function(){return _GY(_Ie,_IJ);});}else{if(_IJ>=_Ie){return new F(function(){return _GY(_Ie,_IJ);});}else{var _=_IF[_IJ]=new T(function(){var _IK=E(_If[_IJ]),_IL=E(_IK.e),_IM=E(_IL.a),_IN=B(_Es(_ji,_HL,_HM,_HN,_HJ,_Hx,_Hy,_Hz,_Hv)),_IO=E(_IN.a),_IP=E(_Ia)*E(_Hi),_IQ=B(_Es(_ji,_IO.a,_IO.b,_IO.c,_IN.b,_IP,_IP,_IP,_IP)),_IR=E(_IQ.a),_IS=B(_ED(_ji,_IM.a,_IM.b,_IM.c,_IL.b,_IR.a,_IR.b,_IR.c,_IQ.b));return {_:0,a:E(_IK.a),b:E(_IK.b),c:E(_IK.c),d:E(_IK.d),e:E(new T2(0,E(_IS.a),E(_IS.b))),f:E(_IK.f),g:E(_IK.g),h:_IK.h,i:_IK.i};});return new T4(0,E(_Ic),E(_Id),_Ie,_IF);}}},_IT=B(_AM(_ID));return B(_Ih(E(_IT.a),E(_IT.b),_IT.c,_IT.d,_IT));}}});return new T2(0,_kz,_Ig);};if(!E(_Hr.f)){var _IU=B(_Ib(_Hp,_Hq,_Hn,_Ho,_)),_IV=B(A2(_Hg,new T(function(){return E(E(_IU).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IU).a);}),new T(function(){return E(E(_IV).a);})),new T(function(){return E(E(_IV).b);}));}else{if(E(_Ia)<0){var _IW=B(A2(_Hg,_Hm,_));return new T2(0,new T2(1,_kz,new T(function(){return E(E(_IW).a);})),new T(function(){return E(E(_IW).b);}));}else{var _IX=B(_Ib(_Hp,_Hq,_Hn,_Ho,_)),_IY=B(A2(_Hg,new T(function(){return E(E(_IX).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_IX).a);}),new T(function(){return E(E(_IY).a);})),new T(function(){return E(E(_IY).b);}));}}}}}}}}}}}};return E(_Hk);}};return new F(function(){return _Hc(_Ha.a);});}},_IZ=function(_,_J0){var _J1=new T(function(){return B(_H8(E(_J0).a));}),_J2=function(_J3){var _J4=E(_J3);return (_J4==1)?E(new T2(1,_J1,_w)):new T2(1,_J1,new T(function(){return B(_J2(_J4-1|0));}));},_J5=B(_DE(B(_J2(5)),new T(function(){return E(E(_J0).b);}),_)),_J6=new T(function(){return B(_Ec(_DD,_Bs,_Fb,new T(function(){return E(E(_J5).b);})));});return new T2(0,_kz,_J6);},_J7=function(_J8,_J9,_Ja,_Jb,_Jc){var _Jd=B(_8s(B(_8q(_J8))));return new F(function(){return A3(_86,_Jd,new T(function(){return B(A3(_8u,_Jd,_J9,_Jb));}),new T(function(){return B(A3(_8u,_Jd,_Ja,_Jc));}));});},_Je=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Jf=new T6(0,_GJ,_GK,_w,_Je,_GJ,_GJ),_Jg=new T(function(){return B(_GH(_Jf));}),_Jh=function(_){return new F(function(){return die(_Jg);});},_Ji=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Jj=new T6(0,_GJ,_GK,_w,_Ji,_GJ,_GJ),_Jk=new T(function(){return B(_GH(_Jj));}),_Jl=function(_){return new F(function(){return die(_Jk);});},_Jm=false,_Jn=true,_Jo=function(_Jp){var _Jq=E(_Jp),_Jr=_Jq.b,_Js=E(_Jq.d),_Jt=E(_Jq.e),_Ju=E(_Jt.a),_Jv=E(_Jq.g),_Jw=B(A1(_Jr,_Js.a)),_Jx=B(_md(_jO,_Jw.a,_Jw.b,_Jw.c,_Jv.a,_Jv.b,_Jv.c));return {_:0,a:E(_Jq.a),b:E(_Jr),c:E(_Jq.c),d:E(_Js),e:E(new T2(0,E(new T3(0,E(_Ju.a)+E(_Jx.a)*1.0e-2,E(_Ju.b)+E(_Jx.b)*1.0e-2,E(_Ju.c)+E(_Jx.c)*1.0e-2)),E(_Jt.b))),f:E(_Jq.f),g:E(_Jv),h:_Jq.h,i:_Jq.i};},_Jy=new T(function(){return eval("__strict(collideBound)");}),_Jz=new T(function(){return eval("__strict(mouseContact)");}),_JA=new T(function(){return eval("__strict(collide)");}),_JB=function(_JC){var _JD=E(_JC);if(!_JD._){return __Z;}else{return new F(function(){return _n(_JD.a,new T(function(){return B(_JB(_JD.b));},1));});}},_JE=0,_JF=new T3(0,E(_JE),E(_JE),E(_JE)),_JG=new T2(0,E(_JF),E(_JE)),_JH=new T2(0,_jO,_kn),_JI=new T(function(){return B(_hP(_JH));}),_JJ=function(_JK,_){var _JL=B(_Ec(_DD,_Bs,_Jo,_JK)),_JM=E(_JL.a),_JN=E(_JL.b);if(_JM<=_JN){var _JO=function(_JP,_JQ,_JR,_JS,_JT,_){if(_JQ>_JP){return new F(function(){return _Jl(_);});}else{if(_JP>_JR){return new F(function(){return _Jl(_);});}else{var _JU=new T(function(){var _JV=_JP-_JQ|0;if(0>_JV){return B(_H3(_JV,_JS));}else{if(_JV>=_JS){return B(_H3(_JV,_JS));}else{return E(_JT[_JV]);}}}),_JW=function(_JX,_JY,_JZ,_K0,_K1,_){var _K2=E(_JX);if(!_K2._){return new T2(0,_w,new T4(0,E(_JY),E(_JZ),_K0,_K1));}else{var _K3=E(_K2.a);if(_JY>_K3){return new F(function(){return _Jh(_);});}else{if(_K3>_JZ){return new F(function(){return _Jh(_);});}else{var _K4=E(_JU),_K5=_K3-_JY|0;if(0>_K5){return new F(function(){return _GY(_K0,_K5);});}else{if(_K5>=_K0){return new F(function(){return _GY(_K0,_K5);});}else{var _K6=E(_K1[_K5]),_K7=__app2(E(_JA),B(_kA(new T2(1,new T2(0,_AR,_K4.h),new T2(1,new T2(0,_AQ,_K4.i),_w)))),B(_kA(new T2(1,new T2(0,_AR,_K6.h),new T2(1,new T2(0,_AQ,_K6.i),_w))))),_K8=__arr2lst(0,_K7),_K9=B(_C5(_K8,_)),_Ka=B(_JW(_K2.b,_JY,_JZ,_K0,_K1,_)),_Kb=new T(function(){var _Kc=new T(function(){return _JP!=_K3;}),_Kd=function(_Ke){var _Kf=E(_Ke);if(!_Kf._){return __Z;}else{var _Kg=_Kf.b,_Kh=E(_Kf.a),_Ki=E(_Kh.b),_Kj=E(_Kh.a),_Kk=E(_Kh.c),_Kl=_Kk.a,_Km=_Kk.b,_Kn=E(_Kh.e),_Ko=E(_Kh.d),_Kp=_Ko.a,_Kq=_Ko.b,_Kr=E(_Kh.f),_Ks=new T(function(){var _Kt=B(_ln(_jO,_Kr.a,_Kr.b,_Kr.c)),_Ku=Math.sqrt(B(_J7(_jO,_Kp,_Kq,_Kp,_Kq)));return new T3(0,_Ku*E(_Kt.a),_Ku*E(_Kt.b),_Ku*E(_Kt.c));}),_Kv=new T(function(){var _Kw=B(_ln(_jO,_Kn.a,_Kn.b,_Kn.c)),_Kx=Math.sqrt(B(_J7(_jO,_Kl,_Km,_Kl,_Km)));return new T3(0,_Kx*E(_Kw.a),_Kx*E(_Kw.b),_Kx*E(_Kw.c));}),_Ky=new T(function(){var _Kz=B(A1(_JI,_Ki)),_KA=B(_ln(_jO,_Kz.a,_Kz.b,_Kz.c));return new T3(0,E(_KA.a),E(_KA.b),E(_KA.c));}),_KB=new T(function(){var _KC=B(A1(_JI,_Kj)),_KD=B(_ln(_jO,_KC.a,_KC.b,_KC.c));return new T3(0,E(_KD.a),E(_KD.b),E(_KD.c));}),_KE=E(_Ki.a)+ -E(_Kj.a),_KF=E(_Ki.b)+ -E(_Kj.b),_KG=E(_Ki.c)+ -E(_Kj.c),_KH=new T(function(){return Math.sqrt(B(_ld(_jO,_KE,_KF,_KG,_KE,_KF,_KG)));}),_KI=new T(function(){var _KJ=1/E(_KH);return new T3(0,_KE*_KJ,_KF*_KJ,_KG*_KJ);}),_KK=new T(function(){if(!E(_Kh.g)){return E(_KI);}else{var _KL=E(_KI);return new T3(0,-1*E(_KL.a),-1*E(_KL.b),-1*E(_KL.c));}}),_KM=new T(function(){if(!E(_Kh.h)){return E(_KI);}else{var _KN=E(_KI);return new T3(0,-1*E(_KN.a),-1*E(_KN.b),-1*E(_KN.c));}});return (!E(_Kc))?new T2(1,new T(function(){var _KO=E(_KK),_KP=E(_KO.b),_KQ=E(_KO.c),_KR=E(_KO.a),_KS=E(_KB),_KT=E(_KS.c),_KU=E(_KS.b),_KV=E(_KS.a),_KW=E(_Kv),_KX=E(_KW.c),_KY=E(_KW.b),_KZ=E(_KW.a),_L0=_KP*_KT-_KU*_KQ,_L1=_KQ*_KV-_KT*_KR,_L2=_KR*_KU-_KV*_KP,_L3=B(_ld(_jO,_L1*_KX-_KY*_L2,_L2*_KZ-_KX*_L0,_L0*_KY-_KZ*_L1,_KV,_KU,_KT));return new T6(0,_JP,_K3,E(new T2(0,E(new T3(0,E(_L0),E(_L1),E(_L2))),E(_L3))),E(_JG),_KH,_Jm);}),new T2(1,new T(function(){var _L4=E(_KM),_L5=E(_L4.b),_L6=E(_L4.c),_L7=E(_L4.a),_L8=E(_Ky),_L9=E(_L8.c),_La=E(_L8.b),_Lb=E(_L8.a),_Lc=E(_Ks),_Ld=E(_Lc.c),_Le=E(_Lc.b),_Lf=E(_Lc.a),_Lg=_L5*_L9-_La*_L6,_Lh=_L6*_Lb-_L9*_L7,_Li=_L7*_La-_Lb*_L5,_Lj=B(_ld(_jO,_Lh*_Ld-_Le*_Li,_Li*_Lf-_Ld*_Lg,_Lg*_Le-_Lf*_Lh,_Lb,_La,_L9));return new T6(0,_JP,_K3,E(_JG),E(new T2(0,E(new T3(0,E(_Lg),E(_Lh),E(_Li))),E(_Lj))),_KH,_Jm);}),new T(function(){return B(_Kd(_Kg));}))):new T2(1,new T(function(){var _Lk=E(_KK),_Ll=E(_Lk.b),_Lm=E(_Lk.c),_Ln=E(_Lk.a),_Lo=E(_KB),_Lp=_Lo.a,_Lq=_Lo.b,_Lr=_Lo.c,_Ls=B(_md(_jO,_Ln,_Ll,_Lm,_Lp,_Lq,_Lr)),_Lt=E(_Kv),_Lu=E(_Lt.c),_Lv=E(_Lt.b),_Lw=E(_Lt.a),_Lx=B(_ld(_jO,_Ll*_Lu-_Lv*_Lm,_Lm*_Lw-_Lu*_Ln,_Ln*_Lv-_Lw*_Ll,_Lp,_Lq,_Lr)),_Ly=E(_KM),_Lz=E(_Ly.b),_LA=E(_Ly.c),_LB=E(_Ly.a),_LC=E(_Ky),_LD=_LC.a,_LE=_LC.b,_LF=_LC.c,_LG=B(_md(_jO,_LB,_Lz,_LA,_LD,_LE,_LF)),_LH=E(_Ks),_LI=E(_LH.c),_LJ=E(_LH.b),_LK=E(_LH.a),_LL=B(_ld(_jO,_Lz*_LI-_LJ*_LA,_LA*_LK-_LI*_LB,_LB*_LJ-_LK*_Lz,_LD,_LE,_LF));return new T6(0,_JP,_K3,E(new T2(0,E(new T3(0,E(_Ls.a),E(_Ls.b),E(_Ls.c))),E(_Lx))),E(new T2(0,E(new T3(0,E(_LG.a),E(_LG.b),E(_LG.c))),E(_LL))),_KH,_Jn);}),new T(function(){return B(_Kd(_Kg));}));}};return B(_Kd(_K9));});return new T2(0,new T2(1,_Kb,new T(function(){return E(E(_Ka).a);})),new T(function(){return E(E(_Ka).b);}));}}}}}},_LM=B(_JW(B(_sI(_JP,_JN)),_JQ,_JR,_JS,_JT,_)),_LN=E(_JU),_LO=E(_LN.d).a,_LP=__app1(E(_Jy),B(_kA(new T2(1,new T2(0,_AR,_LN.h),new T2(1,new T2(0,_AQ,_LN.i),_w))))),_LQ=__arr2lst(0,_LP),_LR=B(_C5(_LQ,_)),_LS=__app1(E(_Jz),_JP),_LT=__arr2lst(0,_LS),_LU=B(_C5(_LT,_));if(_JP!=_JN){var _LV=E(_LM),_LW=E(_LV.b),_LX=B(_JO(_JP+1|0,E(_LW.a),E(_LW.b),_LW.c,_LW.d,_)),_LY=new T(function(){var _LZ=new T(function(){var _M0=B(A1(_JI,_LO)),_M1=B(_ln(_jO,_M0.a,_M0.b,_M0.c));return new T3(0,E(_M1.a),E(_M1.b),E(_M1.c));}),_M2=new T(function(){var _M3=new T(function(){return B(_JB(_LV.a));}),_M4=function(_M5){var _M6=E(_M5);if(!_M6._){return E(_M3);}else{var _M7=E(_M6.a),_M8=E(_M7.b),_M9=E(_M7.a),_Ma=E(_M7.c),_Mb=_Ma.a,_Mc=_Ma.b,_Md=E(_M7.e);return new T2(1,new T(function(){var _Me=E(_M8.a)+ -E(_M9.a),_Mf=E(_M8.b)+ -E(_M9.b),_Mg=E(_M8.c)+ -E(_M9.c),_Mh=B(A1(_JI,_M9)),_Mi=B(_ln(_jO,_Mh.a,_Mh.b,_Mh.c)),_Mj=_Mi.a,_Mk=_Mi.b,_Ml=_Mi.c,_Mm=Math.sqrt(B(_ld(_jO,_Me,_Mf,_Mg,_Me,_Mf,_Mg))),_Mn=1/_Mm,_Mo=_Me*_Mn,_Mp=_Mf*_Mn,_Mq=_Mg*_Mn,_Mr=B(_md(_jO,_Mo,_Mp,_Mq,_Mj,_Mk,_Ml)),_Ms=B(_ln(_jO,_Md.a,_Md.b,_Md.c)),_Mt=Math.sqrt(B(_J7(_jO,_Mb,_Mc,_Mb,_Mc))),_Mu=_Mt*E(_Ms.a),_Mv=_Mt*E(_Ms.b),_Mw=_Mt*E(_Ms.c),_Mx=B(_ld(_jO,_Mp*_Mw-_Mv*_Mq,_Mq*_Mu-_Mw*_Mo,_Mo*_Mv-_Mu*_Mp,_Mj,_Mk,_Ml));return new T6(0,_JP,_JP,E(new T2(0,E(new T3(0,E(_Mr.a),E(_Mr.b),E(_Mr.c))),E(_Mx))),E(_JG),_Mm,_Jn);}),new T(function(){return B(_M4(_M6.b));}));}};return B(_M4(_LR));}),_My=function(_Mz){var _MA=E(_Mz);if(!_MA._){return E(_M2);}else{var _MB=E(_MA.a),_MC=E(_MB.b),_MD=new T(function(){var _ME=E(_LO),_MF=E(_MC.c)+ -E(_ME.c),_MG=E(_MC.b)+ -E(_ME.b),_MH=E(_MC.a)+ -E(_ME.a),_MI=Math.sqrt(B(_ld(_jO,_MH,_MG,_MF,_MH,_MG,_MF))),_MJ=function(_MK,_ML,_MM){var _MN=E(_LZ),_MO=_MN.a,_MP=_MN.b,_MQ=_MN.c,_MR=B(_md(_jO,_MK,_ML,_MM,_MO,_MP,_MQ)),_MS=B(_ld(_jO,_ML*0-0*_MM,_MM*0-0*_MK,_MK*0-0*_ML,_MO,_MP,_MQ));return new T6(0,_JP,_JP,new T2(0,E(new T3(0,E(_MR.a),E(_MR.b),E(_MR.c))),E(_MS)),_JG,_MI,_Jn);};if(!E(_MB.g)){var _MT=1/_MI,_MU=B(_MJ(_MH*_MT,_MG*_MT,_MF*_MT));return new T6(0,_MU.a,_MU.b,E(_MU.c),E(_MU.d),_MU.e,_MU.f);}else{var _MV=1/_MI,_MW=B(_MJ(-1*_MH*_MV,-1*_MG*_MV,-1*_MF*_MV));return new T6(0,_MW.a,_MW.b,E(_MW.c),E(_MW.d),_MW.e,_MW.f);}});return new T2(1,_MD,new T(function(){return B(_My(_MA.b));}));}};return B(_My(_LU));});return new T2(0,new T2(1,_LY,new T(function(){return E(E(_LX).a);})),new T(function(){return E(E(_LX).b);}));}else{var _MX=new T(function(){var _MY=new T(function(){var _MZ=B(A1(_JI,_LO)),_N0=B(_ln(_jO,_MZ.a,_MZ.b,_MZ.c));return new T3(0,E(_N0.a),E(_N0.b),E(_N0.c));}),_N1=new T(function(){var _N2=new T(function(){return B(_JB(E(_LM).a));}),_N3=function(_N4){var _N5=E(_N4);if(!_N5._){return E(_N2);}else{var _N6=E(_N5.a),_N7=E(_N6.b),_N8=E(_N6.a),_N9=E(_N6.c),_Na=_N9.a,_Nb=_N9.b,_Nc=E(_N6.e);return new T2(1,new T(function(){var _Nd=E(_N7.a)+ -E(_N8.a),_Ne=E(_N7.b)+ -E(_N8.b),_Nf=E(_N7.c)+ -E(_N8.c),_Ng=B(A1(_JI,_N8)),_Nh=B(_ln(_jO,_Ng.a,_Ng.b,_Ng.c)),_Ni=_Nh.a,_Nj=_Nh.b,_Nk=_Nh.c,_Nl=Math.sqrt(B(_ld(_jO,_Nd,_Ne,_Nf,_Nd,_Ne,_Nf))),_Nm=1/_Nl,_Nn=_Nd*_Nm,_No=_Ne*_Nm,_Np=_Nf*_Nm,_Nq=B(_md(_jO,_Nn,_No,_Np,_Ni,_Nj,_Nk)),_Nr=B(_ln(_jO,_Nc.a,_Nc.b,_Nc.c)),_Ns=Math.sqrt(B(_J7(_jO,_Na,_Nb,_Na,_Nb))),_Nt=_Ns*E(_Nr.a),_Nu=_Ns*E(_Nr.b),_Nv=_Ns*E(_Nr.c),_Nw=B(_ld(_jO,_No*_Nv-_Nu*_Np,_Np*_Nt-_Nv*_Nn,_Nn*_Nu-_Nt*_No,_Ni,_Nj,_Nk));return new T6(0,_JP,_JP,E(new T2(0,E(new T3(0,E(_Nq.a),E(_Nq.b),E(_Nq.c))),E(_Nw))),E(_JG),_Nl,_Jn);}),new T(function(){return B(_N3(_N5.b));}));}};return B(_N3(_LR));}),_Nx=function(_Ny){var _Nz=E(_Ny);if(!_Nz._){return E(_N1);}else{var _NA=E(_Nz.a),_NB=E(_NA.b),_NC=new T(function(){var _ND=E(_LO),_NE=E(_NB.c)+ -E(_ND.c),_NF=E(_NB.b)+ -E(_ND.b),_NG=E(_NB.a)+ -E(_ND.a),_NH=Math.sqrt(B(_ld(_jO,_NG,_NF,_NE,_NG,_NF,_NE))),_NI=function(_NJ,_NK,_NL){var _NM=E(_MY),_NN=_NM.a,_NO=_NM.b,_NP=_NM.c,_NQ=B(_md(_jO,_NJ,_NK,_NL,_NN,_NO,_NP)),_NR=B(_ld(_jO,_NK*0-0*_NL,_NL*0-0*_NJ,_NJ*0-0*_NK,_NN,_NO,_NP));return new T6(0,_JP,_JP,new T2(0,E(new T3(0,E(_NQ.a),E(_NQ.b),E(_NQ.c))),E(_NR)),_JG,_NH,_Jn);};if(!E(_NA.g)){var _NS=1/_NH,_NT=B(_NI(_NG*_NS,_NF*_NS,_NE*_NS));return new T6(0,_NT.a,_NT.b,E(_NT.c),E(_NT.d),_NT.e,_NT.f);}else{var _NU=1/_NH,_NV=B(_NI(-1*_NG*_NU,-1*_NF*_NU,-1*_NE*_NU));return new T6(0,_NV.a,_NV.b,E(_NV.c),E(_NV.d),_NV.e,_NV.f);}});return new T2(1,_NC,new T(function(){return B(_Nx(_Nz.b));}));}};return B(_Nx(_LU));});return new T2(0,new T2(1,_MX,_w),new T(function(){return E(E(_LM).b);}));}}}},_NW=B(_JO(_JM,_JM,_JN,_JL.c,_JL.d,_));return new F(function(){return _IZ(_,_NW);});}else{return new F(function(){return _IZ(_,new T2(0,_w,_JL));});}},_NX=new T(function(){return eval("__strict(passObject)");}),_NY=new T(function(){return eval("__strict(refresh)");}),_NZ=function(_O0,_){var _O1=__app0(E(_NY)),_O2=__app0(E(_AV)),_O3=E(_O0),_O4=_O3.c,_O5=_O3.d,_O6=E(_O3.a),_O7=E(_O3.b);if(_O6<=_O7){if(_O6>_O7){return E(_AT);}else{if(0>=_O4){return new F(function(){return _B6(_O4,0);});}else{var _O8=E(_O5[0]),_O9=E(_NX),_Oa=__app2(_O9,_O6,B(_kA(new T2(1,new T2(0,_AR,_O8.h),new T2(1,new T2(0,_AQ,_O8.i),_w)))));if(_O6!=_O7){var _Ob=function(_Oc,_){if(_O6>_Oc){return E(_AT);}else{if(_Oc>_O7){return E(_AT);}else{var _Od=_Oc-_O6|0;if(0>_Od){return new F(function(){return _B6(_O4,_Od);});}else{if(_Od>=_O4){return new F(function(){return _B6(_O4,_Od);});}else{var _Oe=E(_O5[_Od]),_Of=__app2(_O9,_Oc,B(_kA(new T2(1,new T2(0,_AR,_Oe.h),new T2(1,new T2(0,_AQ,_Oe.i),_w)))));if(_Oc!=_O7){var _Og=B(_Ob(_Oc+1|0,_));return new T2(1,_kz,_Og);}else{return _Bb;}}}}}},_Oh=B(_Ob(_O6+1|0,_)),_Oi=__app0(E(_AU)),_Oj=B(_JJ(_O3,_));return new T(function(){return E(E(_Oj).b);});}else{var _Ok=__app0(E(_AU)),_Ol=B(_JJ(_O3,_));return new T(function(){return E(E(_Ol).b);});}}}}else{var _Om=__app0(E(_AU)),_On=B(_JJ(_O3,_));return new T(function(){return E(E(_On).b);});}},_Oo=function(_Op,_){while(1){var _Oq=E(_Op);if(!_Oq._){return _kz;}else{var _Or=_Oq.b,_Os=E(_Oq.a);switch(_Os._){case 0:var _Ot=B(A1(_Os.a,_));_Op=B(_n(_Or,new T2(1,_Ot,_w)));continue;case 1:_Op=B(_n(_Or,_Os.a));continue;default:_Op=_Or;continue;}}}},_Ou=function(_Ov,_Ow,_){var _Ox=E(_Ov);switch(_Ox._){case 0:var _Oy=B(A1(_Ox.a,_));return new F(function(){return _Oo(B(_n(_Ow,new T2(1,_Oy,_w))),_);});break;case 1:return new F(function(){return _Oo(B(_n(_Ow,_Ox.a)),_);});break;default:return new F(function(){return _Oo(_Ow,_);});}},_Oz=new T0(2),_OA=function(_OB){return new T0(2);},_OC=function(_OD,_OE,_OF){return function(_){var _OG=E(_OD),_OH=rMV(_OG),_OI=E(_OH);if(!_OI._){var _OJ=new T(function(){var _OK=new T(function(){return B(A1(_OF,_kz));});return B(_n(_OI.b,new T2(1,new T2(0,_OE,function(_OL){return E(_OK);}),_w)));}),_=wMV(_OG,new T2(0,_OI.a,_OJ));return _Oz;}else{var _OM=E(_OI.a);if(!_OM._){var _=wMV(_OG,new T2(0,_OE,_w));return new T(function(){return B(A1(_OF,_kz));});}else{var _=wMV(_OG,new T1(1,_OM.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OF,_kz));}),new T2(1,new T(function(){return B(A2(_OM.a,_OE,_OA));}),_w)));}}};},_ON=new T(function(){return E(_qe);}),_OO=new T(function(){return eval("window.requestAnimationFrame");}),_OP=new T1(1,_w),_OQ=function(_OR,_OS){return function(_){var _OT=E(_OR),_OU=rMV(_OT),_OV=E(_OU);if(!_OV._){var _OW=_OV.a,_OX=E(_OV.b);if(!_OX._){var _=wMV(_OT,_OP);return new T(function(){return B(A1(_OS,_OW));});}else{var _OY=E(_OX.a),_=wMV(_OT,new T2(0,_OY.a,_OX.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OS,_OW));}),new T2(1,new T(function(){return B(A1(_OY.b,_OA));}),_w)));}}else{var _OZ=new T(function(){var _P0=function(_P1){var _P2=new T(function(){return B(A1(_OS,_P1));});return function(_P3){return E(_P2);};};return B(_n(_OV.a,new T2(1,_P0,_w)));}),_=wMV(_OT,new T1(1,_OZ));return _Oz;}};},_P4=function(_P5,_P6){return new T1(0,B(_OQ(_P5,_P6)));},_P7=function(_P8,_P9){var _Pa=new T(function(){return new T1(0,B(_OC(_P8,_kz,_OA)));});return function(_){var _Pb=__createJSFunc(2,function(_Pc,_){var _Pd=B(_Ou(_Pa,_w,_));return _ON;}),_Pe=__app1(E(_OO),_Pb);return new T(function(){return B(_P4(_P8,_P9));});};},_Pf=new T1(1,_w),_Pg=function(_Ph,_Pi,_){var _Pj=function(_){var _Pk=nMV(_Ph),_Pl=_Pk;return new T(function(){var _Pm=new T(function(){return B(_Pn(_));}),_Po=function(_){var _Pp=rMV(_Pl),_Pq=B(A2(_Pi,_Pp,_)),_=wMV(_Pl,_Pq),_Pr=function(_){var _Ps=nMV(_Pf);return new T(function(){return new T1(0,B(_P7(_Ps,function(_Pt){return E(_Pm);})));});};return new T1(0,_Pr);},_Pu=new T(function(){return new T1(0,_Po);}),_Pn=function(_Pv){return E(_Pu);};return B(_Pn(_));});};return new F(function(){return _Ou(new T1(0,_Pj),_w,_);});},_Pw=new T(function(){return eval("__strict(setBounds)");}),_Px=function(_){var _Py=__app3(E(_20),E(_91),E(_ib),E(_1Z)),_Pz=__app2(E(_Pw),E(_1u),E(_1n));return new F(function(){return _Pg(_AP,_NZ,_);});},_PA=function(_){return new F(function(){return _Px(_);});};
var hasteMain = function() {B(A(_PA, [0]));};window.onload = hasteMain;