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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=function(_i,_j,_k){return new F(function(){return A1(_i,function(_l){return new F(function(){return A2(_j,_l,_k);});});});},_m=function(_n,_o,_p){var _q=function(_r){var _s=new T(function(){return B(A1(_p,_r));});return new F(function(){return A1(_o,function(_t){return E(_s);});});};return new F(function(){return A1(_n,_q);});},_u=function(_v,_w,_x){var _y=new T(function(){return B(A1(_w,function(_z){return new F(function(){return A1(_x,_z);});}));});return new F(function(){return A1(_v,function(_A){return E(_y);});});},_B=function(_C,_D,_E){var _F=function(_G){var _H=function(_I){return new F(function(){return A1(_E,new T(function(){return B(A1(_G,_I));}));});};return new F(function(){return A1(_D,_H);});};return new F(function(){return A1(_C,_F);});},_J=function(_K,_L){return new F(function(){return A1(_L,_K);});},_M=function(_N,_O,_P){var _Q=new T(function(){return B(A1(_P,_N));});return new F(function(){return A1(_O,function(_R){return E(_Q);});});},_S=function(_T,_U,_V){var _W=function(_X){return new F(function(){return A1(_V,new T(function(){return B(A1(_T,_X));}));});};return new F(function(){return A1(_U,_W);});},_Y=new T2(0,_S,_M),_Z=new T5(0,_Y,_J,_B,_u,_m),_10=function(_11){return E(E(_11).b);},_12=function(_13,_14){return new F(function(){return A3(_10,_15,_13,function(_16){return E(_14);});});},_17=function(_18){return new F(function(){return err(_18);});},_15=new T(function(){return new T5(0,_Z,_h,_12,_J,_17);}),_19=function(_1a){return new T0(2);},_1b=function(_1c){var _1d=new T(function(){return B(A1(_1c,_19));}),_1e=function(_1f){return new T1(1,new T2(1,new T(function(){return B(A1(_1f,_5));}),new T2(1,_1d,_4)));};return E(_1e);},_1g=function(_1h){return E(_1h);},_1i=new T3(0,_15,_1g,_1b),_1j=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1k=new T(function(){return B(err(_1j));}),_1l=0,_1m=new T3(0,_1l,_1l,_1l),_1n=1,_1o=new T3(0,_1l,_1n,_1l),_1p=40,_1q=new T1(0,_1p),_1r=80,_1s=new T(function(){return eval("scrW");}),_1t=new T(function(){return E(_1s)/2-1;}),_1u=new T3(0,_1t,_1r,_1l),_1v=2.4867959858108646e-7,_1w=1.9894367886486917e-4,_1x=new T3(0,_1w,_1w,_1v),_1y=new T5(0,_1q,_1u,_1m,_1o,_1x),_1z=60,_1A=new T(function(){return E(_1s)/2-2;}),_1B=new T3(0,_1A,_1z,_1l),_1C=new T5(0,_1q,_1B,_1m,_1o,_1x),_1D=2,_1E=0,_1F=new T(function(){return E(_1s)/2-3;}),_1G=100,_1H=new T3(0,_1F,_1G,_1l),_1I=new T5(0,_1q,_1H,_1m,_1o,_1x),_1J=function(_){var _1K=newArr(3,_1k),_=_1K[0]=_1C,_=_1K[1]=_1y,_=_1K[2]=_1I;return new T4(0,E(_1E),E(_1D),3,_1K);},_1L=function(_1M){var _1N=B(A1(_1M,_));return E(_1N);},_1O=new T(function(){return B(_1L(_1J));}),_1P=function(_1Q,_1R,_){var _1S=B(A1(_1Q,_)),_1T=B(A1(_1R,_));return _1S;},_1U=function(_1V,_1W,_){var _1X=B(A1(_1V,_)),_1Y=B(A1(_1W,_));return new T(function(){return B(A1(_1X,_1Y));});},_1Z=function(_20,_21,_){var _22=B(A1(_21,_));return _20;},_23=function(_24,_25,_){var _26=B(A1(_25,_));return new T(function(){return B(A1(_24,_26));});},_27=new T2(0,_23,_1Z),_28=function(_29,_){return _29;},_2a=function(_2b,_2c,_){var _2d=B(A1(_2b,_));return new F(function(){return A1(_2c,_);});},_2e=new T5(0,_27,_28,_1U,_2a,_1P),_2f=function(_2g){var _2h=E(_2g);return (E(_2h.b)-E(_2h.a)|0)+1|0;},_2i=function(_2j,_2k){var _2l=E(_2j),_2m=E(_2k);return (E(_2l.a)>_2m)?false:_2m<=E(_2l.b);},_2n=function(_2o,_2p){var _2q=jsShowI(_2o);return new F(function(){return _0(fromJSStr(_2q),_2p);});},_2r=41,_2s=40,_2t=function(_2u,_2v,_2w){if(_2v>=0){return new F(function(){return _2n(_2v,_2w);});}else{if(_2u<=6){return new F(function(){return _2n(_2v,_2w);});}else{return new T2(1,_2s,new T(function(){var _2x=jsShowI(_2v);return B(_0(fromJSStr(_2x),new T2(1,_2r,_2w)));}));}}},_2y=function(_2z){return new F(function(){return _2t(0,E(_2z),_4);});},_2A=function(_2B,_2C,_2D){return new F(function(){return _2t(E(_2B),E(_2C),_2D);});},_2E=44,_2F=93,_2G=91,_2H=function(_2I,_2J,_2K){var _2L=E(_2J);if(!_2L._){return new F(function(){return unAppCStr("[]",_2K);});}else{var _2M=new T(function(){var _2N=new T(function(){var _2O=function(_2P){var _2Q=E(_2P);if(!_2Q._){return E(new T2(1,_2F,_2K));}else{var _2R=new T(function(){return B(A2(_2I,_2Q.a,new T(function(){return B(_2O(_2Q.b));})));});return new T2(1,_2E,_2R);}};return B(_2O(_2L.b));});return B(A2(_2I,_2L.a,_2N));});return new T2(1,_2G,_2M);}},_2S=function(_2T,_2U){return new F(function(){return _2t(0,E(_2T),_2U);});},_2V=function(_2W,_2X){return new F(function(){return _2H(_2S,_2W,_2X);});},_2Y=new T3(0,_2A,_2y,_2V),_2Z=0,_30=function(_31,_32,_33){return new F(function(){return A1(_31,new T2(1,_2E,new T(function(){return B(A1(_32,_33));})));});},_34=new T(function(){return B(unCStr(": empty list"));}),_35=new T(function(){return B(unCStr("Prelude."));}),_36=function(_37){return new F(function(){return err(B(_0(_35,new T(function(){return B(_0(_37,_34));},1))));});},_38=new T(function(){return B(unCStr("foldr1"));}),_39=new T(function(){return B(_36(_38));}),_3a=function(_3b,_3c){var _3d=E(_3c);if(!_3d._){return E(_39);}else{var _3e=_3d.a,_3f=E(_3d.b);if(!_3f._){return E(_3e);}else{return new F(function(){return A2(_3b,_3e,new T(function(){return B(_3a(_3b,_3f));}));});}}},_3g=new T(function(){return B(unCStr(" out of range "));}),_3h=new T(function(){return B(unCStr("}.index: Index "));}),_3i=new T(function(){return B(unCStr("Ix{"));}),_3j=new T2(1,_2r,_4),_3k=new T2(1,_2r,_3j),_3l=0,_3m=function(_3n){return E(E(_3n).a);},_3o=function(_3p,_3q,_3r,_3s,_3t){var _3u=new T(function(){var _3v=new T(function(){var _3w=new T(function(){var _3x=new T(function(){var _3y=new T(function(){return B(A3(_3a,_30,new T2(1,new T(function(){return B(A3(_3m,_3r,_3l,_3s));}),new T2(1,new T(function(){return B(A3(_3m,_3r,_3l,_3t));}),_4)),_3k));});return B(_0(_3g,new T2(1,_2s,new T2(1,_2s,_3y))));});return B(A(_3m,[_3r,_2Z,_3q,new T2(1,_2r,_3x)]));});return B(_0(_3h,new T2(1,_2s,_3w)));},1);return B(_0(_3p,_3v));},1);return new F(function(){return err(B(_0(_3i,_3u)));});},_3z=function(_3A,_3B,_3C,_3D,_3E){return new F(function(){return _3o(_3A,_3B,_3E,_3C,_3D);});},_3F=function(_3G,_3H,_3I,_3J){var _3K=E(_3I);return new F(function(){return _3z(_3G,_3H,_3K.a,_3K.b,_3J);});},_3L=function(_3M,_3N,_3O,_3P){return new F(function(){return _3F(_3P,_3O,_3N,_3M);});},_3Q=new T(function(){return B(unCStr("Int"));}),_3R=function(_3S,_3T){return new F(function(){return _3L(_2Y,_3T,_3S,_3Q);});},_3U=function(_3V,_3W){var _3X=E(_3V),_3Y=E(_3X.a),_3Z=E(_3W);if(_3Y>_3Z){return new F(function(){return _3R(_3Z,_3X);});}else{if(_3Z>E(_3X.b)){return new F(function(){return _3R(_3Z,_3X);});}else{return _3Z-_3Y|0;}}},_40=function(_41,_42){if(_41<=_42){var _43=function(_44){return new T2(1,_44,new T(function(){if(_44!=_42){return B(_43(_44+1|0));}else{return __Z;}}));};return new F(function(){return _43(_41);});}else{return __Z;}},_45=function(_46,_47){return new F(function(){return _40(E(_46),E(_47));});},_48=function(_49){var _4a=E(_49);return new F(function(){return _45(_4a.a,_4a.b);});},_4b=function(_4c){var _4d=E(_4c),_4e=E(_4d.a),_4f=E(_4d.b);return (_4e>_4f)?E(_2Z):(_4f-_4e|0)+1|0;},_4g=function(_4h,_4i){return E(_4h)-E(_4i)|0;},_4j=function(_4k,_4l){return new F(function(){return _4g(_4l,E(_4k).a);});},_4m=function(_4n,_4o){return E(_4n)==E(_4o);},_4p=function(_4q,_4r){return E(_4q)!=E(_4r);},_4s=new T2(0,_4m,_4p),_4t=function(_4u,_4v){var _4w=E(_4u),_4x=E(_4v);return (_4w>_4x)?E(_4w):E(_4x);},_4y=function(_4z,_4A){var _4B=E(_4z),_4C=E(_4A);return (_4B>_4C)?E(_4C):E(_4B);},_4D=function(_4E,_4F){return (_4E>=_4F)?(_4E!=_4F)?2:1:0;},_4G=function(_4H,_4I){return new F(function(){return _4D(E(_4H),E(_4I));});},_4J=function(_4K,_4L){return E(_4K)>=E(_4L);},_4M=function(_4N,_4O){return E(_4N)>E(_4O);},_4P=function(_4Q,_4R){return E(_4Q)<=E(_4R);},_4S=function(_4T,_4U){return E(_4T)<E(_4U);},_4V={_:0,a:_4s,b:_4G,c:_4S,d:_4P,e:_4M,f:_4J,g:_4t,h:_4y},_4W={_:0,a:_4V,b:_48,c:_3U,d:_4j,e:_2i,f:_4b,g:_2f},_4X=function(_4Y){return E(E(_4Y).a);},_4Z=function(_50,_51){return new T2(1,_50,_51);},_52=function(_53){return E(E(_53).c);},_54=function(_55,_56){var _57=E(_56);return new T2(0,_57.a,_57.b);},_58=function(_59){return E(E(_59).a);},_5a=new T(function(){return B(unCStr("Negative range size"));}),_5b=new T(function(){return B(err(_5a));}),_5c=function(_5d){return E(E(_5d).f);},_5e=function(_5f,_5g,_5h){var _5i=E(_5g),_5j=_5i.a,_5k=_5i.b,_5l=function(_){var _5m=B(A2(_5c,_5f,_5i));if(_5m>=0){var _5n=newArr(_5m,_1k),_5o=_5n,_5p=E(_5m);if(!_5p){return new T(function(){return new T4(0,E(_5j),E(_5k),0,_5o);});}else{var _5q=function(_5r,_5s,_){while(1){var _5t=E(_5r);if(!_5t._){return E(_);}else{var _=_5o[_5s]=_5t.a;if(_5s!=(_5p-1|0)){var _5u=_5s+1|0;_5r=_5t.b;_5s=_5u;continue;}else{return E(_);}}}},_=B(_5q(_5h,0,_));return new T(function(){return new T4(0,E(_5j),E(_5k),_5p,_5o);});}}else{return E(_5b);}};return new F(function(){return _1L(_5l);});},_5v=function(_5w){return E(E(_5w).b);},_5x=function(_5y,_5z,_5A,_5B){var _5C=new T(function(){var _5D=E(_5B),_5E=_5D.c-1|0,_5F=new T(function(){return B(A2(_5v,_5z,_4));});if(0<=_5E){var _5G=new T(function(){return B(_4X(_5z));}),_5H=function(_5I){var _5J=new T(function(){var _5K=new T(function(){return B(A1(_5A,new T(function(){return E(_5D.d[_5I]);})));});return B(A3(_58,_5G,_4Z,_5K));});return new F(function(){return A3(_52,_5z,_5J,new T(function(){if(_5I!=_5E){return B(_5H(_5I+1|0));}else{return E(_5F);}}));});};return B(_5H(0));}else{return E(_5F);}}),_5L=new T(function(){return B(_54(_5y,_5B));});return new F(function(){return A3(_58,B(_4X(_5z)),function(_5M){return new F(function(){return _5e(_5y,_5L,_5M);});},_5C);});},_5N=new T(function(){return eval("draw");}),_5O=function(_){return _5;},_5P=new T(function(){return eval("drawCircle");}),_5Q=function(_5R,_5S,_){var _5T=E(_5R);if(!_5T._){var _5U=E(_5S),_5V=__app4(E(_5P),E(_5U.a),E(_5U.b),E(_5U.c),E(_5T.a));return new F(function(){return _5O(_);});}else{return _5;}},_5W=function(_5X,_){var _5Y=E(_5X);return new F(function(){return _5Q(_5Y.a,_5Y.b,_);});},_5Z=function(_60){return E(_60);},_61=function(_62){return E(_62);},_63=function(_64,_65){return E(_65);},_66=function(_67,_68){return E(_67);},_69=function(_6a){return E(_6a);},_6b=new T2(0,_69,_66),_6c=function(_6d,_6e){return E(_6d);},_6f=new T5(0,_6b,_61,_5Z,_63,_6c),_6g=function(_6h,_6i,_){while(1){var _6j=B((function(_6k,_6l,_){var _6m=E(_6k);if(!_6m._){return new T2(0,_5,_6l);}else{var _6n=B(A2(_6m.a,_6l,_));_6h=_6m.b;_6i=new T(function(){return E(E(_6n).b);});return __continue;}})(_6h,_6i,_));if(_6j!=__continue){return _6j;}}},_6o=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_6p=new T(function(){return B(err(_6o));}),_6q=1,_6r=-1,_6s=function(_6t,_6u){return E(_6t)-E(_6u);},_6v=function(_6w,_6x){var _6y=E(_6w),_6z=E(_6x);return new T2(0,new T(function(){return B(_6s(_6y.a,_6z.a));}),new T(function(){return B(_6s(_6y.b,_6z.b));}));},_6A=function(_6B,_6C){return new F(function(){return _6v(_6C,_6B);});},_6D=new T(function(){return B(unCStr("!!: negative index"));}),_6E=new T(function(){return B(_0(_35,_6D));}),_6F=new T(function(){return B(err(_6E));}),_6G=new T(function(){return B(unCStr("!!: index too large"));}),_6H=new T(function(){return B(_0(_35,_6G));}),_6I=new T(function(){return B(err(_6H));}),_6J=function(_6K,_6L){while(1){var _6M=E(_6K);if(!_6M._){return E(_6I);}else{var _6N=E(_6L);if(!_6N){return E(_6M.a);}else{_6K=_6M.b;_6L=_6N-1|0;continue;}}}},_6O=function(_6P,_6Q){if(_6Q>=0){return new F(function(){return _6J(_6P,_6Q);});}else{return E(_6F);}},_6R=__Z,_6S=function(_6T,_6U,_6V){while(1){var _6W=E(_6T);if(!_6W._){return new T2(0,_6U,_6V);}else{var _6X=_6W.b,_6Y=E(_6W.a),_6Z=_6Y.a,_70=_6Y.b,_71=E(_6U);if(!_71._){if(!E(_6Z)._){var _72=E(_6V),_73=E(_70);if(_72>_73){_6T=_6X;_6U=_6R;_6V=_73;continue;}else{_6T=_6X;_6U=_6R;_6V=_72;continue;}}else{_6T=_6X;_6U=_6R;continue;}}else{var _74=E(_6Z);if(!_74._){_6T=_6X;_6U=_6R;_6V=_70;continue;}else{var _75=E(_71.a),_76=E(_74.a);if(_75>=_76){if(_75!=_76){_6T=_6X;_6U=_74;_6V=_70;continue;}else{var _77=E(_6V),_78=E(_70);if(_77>_78){_6T=_6X;_6U=_74;_6V=_78;continue;}else{_6T=_6X;_6U=_71;_6V=_77;continue;}}}else{_6T=_6X;_6U=_71;continue;}}}}}},_79=function(_7a,_7b,_7c){while(1){var _7d=E(_7a);if(!_7d._){return new T2(0,_7b,_7c);}else{var _7e=_7d.b,_7f=E(_7d.a),_7g=_7f.a,_7h=_7f.b,_7i=E(_7b);if(!_7i._){var _7j=E(_7g);if(!_7j._){var _7k=E(_7c),_7l=E(_7h);if(_7k>_7l){_7a=_7e;_7b=_6R;_7c=_7k;continue;}else{_7a=_7e;_7b=_6R;_7c=_7l;continue;}}else{_7a=_7e;_7b=_7j;_7c=_7h;continue;}}else{var _7m=E(_7g);if(!_7m._){_7a=_7e;_7b=_7i;continue;}else{var _7n=E(_7i.a),_7o=E(_7m.a);if(_7n>=_7o){if(_7n!=_7o){_7a=_7e;_7b=_7i;continue;}else{var _7p=E(_7c),_7q=E(_7h);if(_7p>_7q){_7a=_7e;_7b=_7i;_7c=_7p;continue;}else{_7a=_7e;_7b=_7m;_7c=_7q;continue;}}}else{_7a=_7e;_7b=_7m;_7c=_7h;continue;}}}}}},_7r=function(_7s,_7t,_7u){while(1){var _7v=E(_7s);if(!_7v._){return new T2(0,_7t,_7u);}else{var _7w=_7v.b,_7x=E(_7v.a),_7y=_7x.a,_7z=_7x.b,_7A=E(_7t);if(!_7A._){var _7B=E(_7y);if(!_7B._){var _7C=E(_7u),_7D=E(_7z);if(_7C>_7D){_7s=_7w;_7t=_6R;_7u=_7C;continue;}else{_7s=_7w;_7t=_6R;_7u=_7D;continue;}}else{_7s=_7w;_7t=_7B;_7u=_7z;continue;}}else{var _7E=E(_7y);if(!_7E._){_7s=_7w;_7t=_7A;continue;}else{var _7F=E(_7A.a),_7G=E(_7E.a);if(_7F>=_7G){if(_7F!=_7G){_7s=_7w;_7t=_7A;continue;}else{var _7H=E(_7u),_7I=E(_7z);if(_7H>_7I){_7s=_7w;_7t=_7A;_7u=_7H;continue;}else{_7s=_7w;_7t=_7E;_7u=_7I;continue;}}}else{_7s=_7w;_7t=_7E;_7u=_7z;continue;}}}}}},_7J=function(_7K,_7L){while(1){var _7M=B((function(_7N,_7O){var _7P=E(_7O);if(!_7P._){return __Z;}else{var _7Q=_7P.a,_7R=_7P.b;if(!B(A1(_7N,_7Q))){var _7S=_7N;_7K=_7S;_7L=_7R;return __continue;}else{return new T2(1,_7Q,new T(function(){return B(_7J(_7N,_7R));}));}}})(_7K,_7L));if(_7M!=__continue){return _7M;}}},_7T=function(_7U){return E(E(_7U).a);},_7V=function(_7W,_7X){var _7Y=E(_7W);if(!_7Y._){var _7Z=E(_7X);return __Z;}else{var _80=E(_7X);return (_80._==0)?__Z:(E(_7Y.a)>E(_80.a))?E(_80):E(_7Y);}},_81=function(_82,_83){while(1){var _84=E(_82);if(!_84._){return E(_83);}else{var _85=B(_7V(_83,_84.a));_82=_84.b;_83=_85;continue;}}},_86=function(_87,_88){while(1){var _89=E(_87);if(!_89._){return E(_88);}else{var _8a=B(_7V(_88,_89.a));_87=_89.b;_88=_8a;continue;}}},_8b=function(_8c){return (E(_8c)._==0)?false:true;},_8d=new T(function(){return B(unCStr("minimum"));}),_8e=new T(function(){return B(_36(_8d));}),_8f=function(_8g,_8h){var _8i=E(_8g);if(!_8i._){return __Z;}else{var _8j=E(_8h);return (_8j._==0)?__Z:new T2(1,new T2(0,new T(function(){var _8k=B(_7J(_8b,_8i.a));if(!_8k._){return E(_8e);}else{return B(_86(_8k.b,_8k.a));}}),_8j.a),new T(function(){return B(_8f(_8i.b,_8j.b));}));}},_8l=function(_8m,_8n){while(1){var _8o=E(_8m);if(!_8o._){return E(_8n);}else{var _8p=B(_7V(_8n,_8o.a));_8m=_8o.b;_8n=_8p;continue;}}},_8q=function(_8r,_8s){while(1){var _8t=E(_8r);if(!_8t._){return E(_8s);}else{var _8u=B(_7V(_8s,_8t.a));_8r=_8t.b;_8s=_8u;continue;}}},_8v=function(_8w,_8x){var _8y=E(_8w);if(!_8y._){return __Z;}else{var _8z=E(_8x);return (_8z._==0)?__Z:new T2(1,new T2(0,new T(function(){var _8A=B(_7J(_8b,_8y.a));if(!_8A._){return E(_8e);}else{return B(_8q(_8A.b,_8A.a));}}),_8z.a),new T(function(){return B(_8v(_8y.b,_8z.b));}));}},_8B=function(_8C){while(1){var _8D=E(_8C);if(!_8D._){return true;}else{if(!E(_8D.a)._){_8C=_8D.b;continue;}else{return false;}}}},_8E=function(_8F){while(1){var _8G=E(_8F);if(!_8G._){return false;}else{if(!B(_8B(_8G.a))){_8F=_8G.b;continue;}else{return true;}}}},_8H=function(_8I,_8J){var _8K=E(_8I),_8L=E(_8K.a),_8M=E(_8L.a),_8N=E(_8L.b),_8O=E(_8K.b),_8P=E(_8J),_8Q= -(E(_8O.b)-_8N),_8R=E(_8O.a)-_8M,_8S=(_8Q*E(_8P.a)+_8R*E(_8P.b)-(_8Q*_8M+_8R*_8N))/Math.sqrt(_8Q*_8Q+_8R*_8R);return (_8S<0)?new T1(1,_8S):__Z;},_8T=0,_8U=1,_8V=new T(function(){return B(unCStr("maximum"));}),_8W=new T(function(){return B(_36(_8V));}),_8X=new T(function(){return B(_36(_8d));}),_8Y=new T(function(){return B(_40(0,3));}),_8Z=new T(function(){return B(unCStr("base"));}),_90=new T(function(){return B(unCStr("Control.Exception.Base"));}),_91=new T(function(){return B(unCStr("PatternMatchFail"));}),_92=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_8Z,_90,_91),_93=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_92,_4,_4),_94=function(_95){return E(_93);},_96=function(_97){return E(E(_97).a);},_98=function(_99,_9a,_9b){var _9c=B(A1(_99,_)),_9d=B(A1(_9a,_)),_9e=hs_eqWord64(_9c.a,_9d.a);if(!_9e){return __Z;}else{var _9f=hs_eqWord64(_9c.b,_9d.b);return (!_9f)?__Z:new T1(1,_9b);}},_9g=function(_9h){var _9i=E(_9h);return new F(function(){return _98(B(_96(_9i.a)),_94,_9i.b);});},_9j=function(_9k){return E(E(_9k).a);},_9l=function(_9m){return new T2(0,_9n,_9m);},_9o=function(_9p,_9q){return new F(function(){return _0(E(_9p).a,_9q);});},_9r=function(_9s,_9t){return new F(function(){return _2H(_9o,_9s,_9t);});},_9u=function(_9v,_9w,_9x){return new F(function(){return _0(E(_9w).a,_9x);});},_9y=new T3(0,_9u,_9j,_9r),_9n=new T(function(){return new T5(0,_94,_9y,_9l,_9g,_9j);}),_9z=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_9A=function(_9B){return E(E(_9B).c);},_9C=function(_9D,_9E){return new F(function(){return die(new T(function(){return B(A2(_9A,_9E,_9D));}));});},_9F=function(_9G,_9H){return new F(function(){return _9C(_9G,_9H);});},_9I=function(_9J,_9K){var _9L=E(_9K);if(!_9L._){return new T2(0,_4,_4);}else{var _9M=_9L.a;if(!B(A1(_9J,_9M))){return new T2(0,_4,_9L);}else{var _9N=new T(function(){var _9O=B(_9I(_9J,_9L.b));return new T2(0,_9O.a,_9O.b);});return new T2(0,new T2(1,_9M,new T(function(){return E(E(_9N).a);})),new T(function(){return E(E(_9N).b);}));}}},_9P=32,_9Q=new T(function(){return B(unCStr("\n"));}),_9R=function(_9S){return (E(_9S)==124)?false:true;},_9T=function(_9U,_9V){var _9W=B(_9I(_9R,B(unCStr(_9U)))),_9X=_9W.a,_9Y=function(_9Z,_a0){var _a1=new T(function(){var _a2=new T(function(){return B(_0(_9V,new T(function(){return B(_0(_a0,_9Q));},1)));});return B(unAppCStr(": ",_a2));},1);return new F(function(){return _0(_9Z,_a1);});},_a3=E(_9W.b);if(!_a3._){return new F(function(){return _9Y(_9X,_4);});}else{if(E(_a3.a)==124){return new F(function(){return _9Y(_9X,new T2(1,_9P,_a3.b));});}else{return new F(function(){return _9Y(_9X,_4);});}}},_a4=function(_a5){return new F(function(){return _9F(new T1(0,new T(function(){return B(_9T(_a5,_9z));})),_9n);});},_a6=new T(function(){return B(_a4("Lib\\Physics.hs:96:13-61|(Just d\', f\')"));}),_a7=new T2(0,_1n,_1l),_a8=function(_a9){return  -E(_a9);},_aa=function(_ab){var _ac=E(_ab);return new T2(0,new T(function(){return B(_a8(_ac.a));}),new T(function(){return B(_a8(_ac.b));}));},_ad=function(_ae){var _af=E(_ae);return new T5(0,_af.b,_af.a,new T(function(){return B(_aa(_af.d));}),new T(function(){return B(_aa(_af.c));}),_af.e);},_ag=new T(function(){return B(unCStr("Non-exhaustive guards in"));}),_ah=function(_ai){return new F(function(){return _9F(new T1(0,new T(function(){return B(_9T(_ai,_ag));})),_9n);});},_aj=new T(function(){return B(_ah("Lib\\Physics.hs:(58,26)-(61,63)|multi-way if"));}),_ak=function(_al,_am){var _an=E(_am);return (_an._==0)?__Z:new T2(1,new T(function(){return B(A1(_al,_an.a));}),new T(function(){return B(_ak(_al,_an.b));}));},_ao=function(_ap,_aq){var _ar=_ap%_aq;if(_ap<=0){if(_ap>=0){return E(_ar);}else{if(_aq<=0){return E(_ar);}else{var _as=E(_ar);return (_as==0)?0:_as+_aq|0;}}}else{if(_aq>=0){if(_ap>=0){return E(_ar);}else{if(_aq<=0){return E(_ar);}else{var _at=E(_ar);return (_at==0)?0:_at+_aq|0;}}}else{var _au=E(_ar);return (_au==0)?0:_au+_aq|0;}}},_av=function(_aw){return E(E(_aw).b);},_ax=new T(function(){return B(unCStr("tail"));}),_ay=new T(function(){return B(_36(_ax));}),_az=-1,_aA=new T2(0,_az,_az),_aB=new T2(0,_az,_8U),_aC=new T2(0,_8U,_8U),_aD=new T2(0,_8U,_az),_aE=new T2(1,_aA,_4),_aF=new T2(1,_aD,_aE),_aG=new T2(1,_aC,_aF),_aH=new T2(1,_aB,_aG),_aI=new T2(1,_aA,_aH),_aJ=function(_aK,_aL){var _aM=E(_aK);if(!_aM._){return __Z;}else{var _aN=E(_aL);return (_aN._==0)?__Z:new T2(1,new T2(0,_aM.a,_aN.a),new T(function(){return B(_aJ(_aM.b,_aN.b));}));}},_aO=function(_aP,_aQ,_aR,_aS){var _aT=E(_aQ);if(!_aT._){return __Z;}else{var _aU=E(_aR);if(!_aU._){return __Z;}else{var _aV=E(_aS);return (_aV._==0)?__Z:new T2(1,new T(function(){return B(A3(_aP,_aT.a,_aU.a,_aV.a));}),new T(function(){return B(_aO(_aP,_aT.b,_aU.b,_aV.b));}));}}},_aW=function(_aX,_aY,_aZ,_b0){var _b1=E(_aX);if(!_b1._){var _b2=_b1.a,_b3=E(_aZ);if(!_b3._){var _b4=E(_aY),_b5=E(_b0),_b6=E(_b2),_b7=E(_b3.a),_b8=E(_b4.a)-E(_b5.a),_b9=E(_b4.b)-E(_b5.b),_ba=Math.sqrt(_b8*_b8+_b9*_b9),_bb=_b6+_b7;if(_ba<=_bb){var _bc=new T(function(){var _bd=E(_ba);if(!_bd){return E(_a7);}else{return new T2(0,new T(function(){return _b8/_bd;}),new T(function(){return _b9/_bd;}));}}),_be=new T(function(){var _bf=E(_bc);return new T2(0,new T(function(){return E(_bf.a)*_b7;}),new T(function(){return E(_bf.b)*_b7;}));}),_bg=new T(function(){var _bh=E(_bc);return new T2(0,new T(function(){return  -(E(_bh.a)*_b6);}),new T(function(){return  -(E(_bh.b)*_b6);}));});return new T2(1,new T5(0,_bg,_be,_bc,_bc,_bb-_ba),_4);}else{return __Z;}}else{var _bi=E(_aY),_bj=E(_bi.a),_bk=E(_b0),_bl=E(_bk.a),_bm=E(_bk.c),_bn=E(_bi.b),_bo=E(_bk.b),_bp=E(_b3.a),_bq=_bj-_bl,_br= -_bm,_bs=_bn-_bo,_bt=_bq*Math.cos(_br)-_bs*Math.sin(_br),_bu= -(_bp/2),_bv=_bp/2,_bw=function(_bx){var _by=E(_b3.b),_bz=_bq*Math.sin(_br)+_bs*Math.cos(_br),_bA= -(_by/2),_bB=_by/2,_bC=function(_bD){var _bE=E(_b2),_bF=_bt-_bx,_bG=_bz-_bD,_bH=Math.sqrt(_bF*_bF+_bG*_bG);if(_bH<=_bE){var _bI=new T(function(){var _bJ=function(_bK){if(_bK>0){var _bL=function(_bM){if(_bM>0){return (_bK>_bM)?(_bK<_bM)?E(_aj):new T2(0,new T2(0,_8T,new T(function(){if(_bG<=0){if(_bG>=0){return _bG;}else{return E(_6r);}}else{return E(_6q);}})),_bE+_bM):new T2(0,new T2(0,new T(function(){if(_bF<=0){if(_bF>=0){return _bF;}else{return E(_6r);}}else{return E(_6q);}}),_8T),_bE+_bK);}else{var _bN=new T(function(){var _bO=E(_bH);if(!_bO){return E(_a7);}else{return new T2(0,new T(function(){return _bF/_bO;}),new T(function(){return _bG/_bO;}));}});return new T2(0,_bN,_bE-_bH);}},_bP=E(_bz);if(!_bP){return new F(function(){return _bL(_by/2);});}else{if(_bP<=0){return new F(function(){return _bL(_by/2+_bP);});}else{return new F(function(){return _bL(_by/2-_bP);});}}}else{var _bQ=new T(function(){var _bR=E(_bH);if(!_bR){return E(_a7);}else{return new T2(0,new T(function(){return _bF/_bR;}),new T(function(){return _bG/_bR;}));}});return new T2(0,_bQ,_bE-_bH);}},_bS=E(_bt);if(!_bS){var _bT=B(_bJ(_bp/2));return new T2(0,_bT.a,_bT.b);}else{if(_bS<=0){var _bU=B(_bJ(_bp/2+_bS));return new T2(0,_bU.a,_bU.b);}else{var _bV=B(_bJ(_bp/2-_bS));return new T2(0,_bV.a,_bV.b);}}}),_bW=new T(function(){return E(E(_bI).b);}),_bX=new T(function(){var _bY=E(E(_bI).a),_bZ=_bY.a,_c0=_bY.b;return new T2(0,new T(function(){return E(_bZ)*Math.cos(_bm)-E(_c0)*Math.sin(_bm);}),new T(function(){return E(_bZ)*Math.sin(_bm)+E(_c0)*Math.cos(_bm);}));}),_c1=new T(function(){var _c2=E(_bX);return new T2(0,new T(function(){return _bj-E(_c2.a)*_bE;}),new T(function(){return _bn-E(_c2.b)*_bE;}));}),_c3=new T(function(){var _c4=E(_c1),_c5=E(_bX);return new T2(0,new T(function(){return E(_c4.a)+E(_c5.a)*E(_bW)-_bl;}),new T(function(){return E(_c4.b)+E(_c5.b)*E(_bW)-_bo;}));}),_c6=new T(function(){var _c7=E(_c1);return new T2(0,new T(function(){return E(_c7.a)-_bj;}),new T(function(){return E(_c7.b)-_bn;}));});return new T2(1,new T5(0,_c6,_c3,_bX,_bX,_bW),_4);}else{return __Z;}};if(_bA>_bz){if(_bB>_bA){return new F(function(){return _bC(_bA);});}else{return new F(function(){return _bC(_bB);});}}else{if(_bB>_bz){return new F(function(){return _bC(_bz);});}else{return new F(function(){return _bC(_bB);});}}};if(_bu>_bt){if(_bv>_bu){return new F(function(){return _bw(_bu);});}else{return new F(function(){return _bw(_bv);});}}else{if(_bv>_bt){return new F(function(){return _bw(_bt);});}else{return new F(function(){return _bw(_bv);});}}}}else{var _c8=E(_aZ);if(!_c8._){return new F(function(){return _ak(_ad,B(_aW(_c8,_b0,_b1,_aY)));});}else{var _c9=new T(function(){var _ca=function(_cb){var _cc=E(_cb),_cd=new T(function(){return E(E(_b0).c);}),_ce=new T(function(){return E(_cc.a)*E(_c8.a)*0.5;}),_cf=new T(function(){return E(_cc.b)*E(_c8.b)*0.5;});return new T2(0,new T(function(){var _cg=E(_cd);return E(E(_b0).a)+(E(_ce)*Math.cos(_cg)-E(_cf)*Math.sin(_cg));}),new T(function(){var _ch=E(_cd);return E(E(_b0).b)+E(_ce)*Math.sin(_ch)+E(_cf)*Math.cos(_ch);}));};return B(_ak(_ca,_aI));}),_ci=new T(function(){return B(_aJ(_c9,new T(function(){var _cj=E(_c9);if(!_cj._){return E(_ay);}else{return E(_cj.b);}},1)));}),_ck=function(_cl){var _cm=E(_cl),_cn=new T(function(){return E(E(_aY).c);}),_co=new T(function(){return E(_cm.a)*E(_b1.a)*0.5;}),_cp=new T(function(){return E(_cm.b)*E(_b1.b)*0.5;});return new T2(0,new T(function(){var _cq=E(_cn);return E(E(_aY).a)+(E(_co)*Math.cos(_cq)-E(_cp)*Math.sin(_cq));}),new T(function(){var _cr=E(_cn);return E(E(_aY).b)+E(_co)*Math.sin(_cr)+E(_cp)*Math.cos(_cr);}));},_cs=B(_ak(_ck,_aI)),_ct=new T(function(){var _cu=function(_cv){var _cw=E(_cs);if(!_cw._){return E(_ay);}else{return new F(function(){return _ak(function(_cx){return new F(function(){return _8H(_cv,_cx);});},_cw.b);});}};return B(_ak(_cu,_ci));}),_cy=B(_aJ(_cs,new T(function(){var _cz=E(_cs);if(!_cz._){return E(_ay);}else{return E(_cz.b);}},1))),_cA=function(_cB){var _cC=E(_c9);if(!_cC._){return E(_ay);}else{return new F(function(){return _ak(function(_cx){return new F(function(){return _8H(_cB,_cx);});},_cC.b);});}},_cD=B(_ak(_cA,_cy));if(!B(_8E(B(_0(_cD,_ct))))){var _cE=B(_8v(_cD,_8Y));if(!_cE._){return E(_8W);}else{var _cF=E(_cE.a),_cG=E(B(_7r(_cE.b,_cF.a,_cF.b)).b),_cH=B(_7J(_8b,B(_6O(_cD,_cG))));if(!_cH._){return E(_8e);}else{var _cI=B(_8f(_ct,_8Y));if(!_cI._){return E(_8W);}else{var _cJ=E(_cI.a),_cK=E(B(_79(_cI.b,_cJ.a,_cJ.b)).b),_cL=B(_7J(_8b,B(_6O(_ct,_cK))));if(!_cL._){return E(_8e);}else{var _cM=B(_81(_cL.b,_cL.a)),_cN=B(_8l(_cH.b,_cH.a)),_cO=E(_cN);if(!_cO._){var _cP=E(_cM),_cQ=false;}else{var _cR=E(_cM);if(!_cR._){var _cS=true;}else{var _cS=E(_cO.a)>E(_cR.a);}var _cQ=_cS;}var _cT=function(_cU,_cV){var _cW=function(_cX,_cY,_cZ,_d0){var _d1=E(_cZ),_d2=E(_d0),_d3=E(_d1.a),_d4=E(_d1.b),_d5=E(_d2.a),_d6=E(_d2.b),_d7=_d5-_d3,_d8=_d6-_d4,_d9=Math.sqrt(_d7*_d7+_d8*_d8);if(!_d9){var _da=E(_cX),_db=E(_da.a),_dc=E(_da.b),_dd=E(_cY),_de= -(E(_dd.b)-_dc),_df=E(_dd.a)-_db,_dg=function(_dh,_di,_dj){var _dk=E(_di),_dl=E(_dj),_dm=_d3+_d4*0,_dn=_d5+_d6*0-_dm,_do=new T(function(){var _dp=E(E(_dh).a);return (E(_dp.a)+E(_dp.b)*0-_dm)/_dn;}),_dq=new T(function(){var _dr=E(E(_dh).b);return (E(_dr.a)+E(_dr.b)*0-_dm)/_dn;}),_ds=function(_dt){var _du=new T(function(){var _dv=E(_dt);if(0>_dv){return E(_8T);}else{if(1>_dv){return E(_dv);}else{return E(_8U);}}}),_dw=new T(function(){return E(_dq)-E(_du);}),_dx=new T(function(){return E(_du)-E(_do);});return new T2(0,new T(function(){var _dy=E(_dw),_dz=E(_dx);return (E(_dk.a)*_dy+E(_dl.a)*_dz)/(_dy+_dz);}),new T(function(){var _dA=E(_dw),_dB=E(_dx);return (E(_dk.b)*_dA+E(_dl.b)*_dB)/(_dA+_dB);}));},_dC=B(_ds(_do)),_dD=E(_dC.a),_dE=E(_dC.b),_dF=new T(function(){var _dG=B(_ds(_dq)),_dH=E(_dG.a),_dI=E(_dG.b),_dJ=(_de*_dH+_df*_dI-(_de*_db+_df*_dc))/Math.sqrt(_de*_de+_df*_df);if(_dJ<0){return new T2(1,new T2(0,new T2(0,_dH,_dI), -_dJ),_4);}else{return __Z;}}),_dK=(_de*_dD+_df*_dE-(_de*_db+_df*_dc))/Math.sqrt(_de*_de+_df*_df);if(_dK<0){var _dL=new T2(1,new T2(0,new T2(0,_dD,_dE), -_dK),_dF);}else{var _dL=E(_dF);}var _dM=new T(function(){return B(_ak(_7T,_dL));}),_dN= -0,_dO=new T(function(){var _dP=function(_dQ){var _dR=E(_dQ),_dS=_dR.b,_dT=E(_dR.a);return new T2(0,new T(function(){return E(_dT.a)+_dN*E(_dS);}),new T(function(){return E(_dT.b)+E(_dS);}));};return B(_ak(_dP,_dL));}),_dU=new T(function(){if(!E(_cQ)){var _dV=new T(function(){return E(E(_b0).b);}),_dW=new T(function(){return E(E(_b0).a);});return B(_ak(function(_cx){return new F(function(){return _6A(new T2(0,_dW,_dV),_cx);});},_dO));}else{var _dX=new T(function(){return E(E(_b0).b);}),_dY=new T(function(){return E(E(_b0).a);});return B(_ak(function(_cx){return new F(function(){return _6A(new T2(0,_dY,_dX),_cx);});},_dM));}}),_dZ=new T(function(){if(!E(_cQ)){return new T2(0,_dN,1);}else{return new T2(0, -_dN,-1);}}),_e0=function(_e1,_e2,_e3){return new T5(0,_e1,_e2,_dZ,_dZ,_e3);};if(!E(_cQ)){var _e4=new T(function(){return E(E(_aY).b);}),_e5=new T(function(){return E(E(_aY).a);});return new F(function(){return _aO(_e0,B(_ak(function(_cx){return new F(function(){return _6A(new T2(0,_e5,_e4),_cx);});},_dM)),_dU,new T(function(){return B(_ak(_av,_dL));},1));});}else{var _e6=new T(function(){return E(E(_aY).b);}),_e7=new T(function(){return E(E(_aY).a);});return new F(function(){return _aO(_e0,B(_ak(function(_cx){return new F(function(){return _6A(new T2(0,_e7,_e6),_cx);});},_dO)),_dU,new T(function(){return B(_ak(_av,_dL));},1));});}},_e8=function(_e9){var _ea=function(_eb,_ec){while(1){var _ed=B((function(_ee,_ef){var _eg=E(_ee);if(!_eg._){return __Z;}else{var _eh=_eg.b,_ei=E(_ef);if(!_ei._){return __Z;}else{var _ej=_ei.b,_ek=E(_eg.a),_el=(_de*E(_ek.a)+_df*E(_ek.b)-(_de*_db+_df*_dc))/Math.sqrt(_de*_de+_df*_df);if(_el<0){return new T2(1,new T2(0,new T1(1,_el),_ei.a),new T(function(){return B(_ea(_eh,_ej));}));}else{_eb=_eh;_ec=_ej;return __continue;}}}})(_eb,_ec));if(_ed!=__continue){return _ed;}}};return new F(function(){return _ea(_e9,_8Y);});},_em=function(_en){var _eo=B(_6O(_cV,_en)),_ep=E(_eo.a),_eq=E(_eo.b),_er=E(_ep.a)-E(_eq.a),_es=E(_ep.b)-E(_eq.b),_et=function(_eu,_ev){var _ew=function(_ex){var _ey=B(_6O(_cV,B(_ao(_en+1|0,4)))),_ez=E(_ey.b),_eA=E(_ey.a),_eB=E(_ez.a)-E(_eA.a),_eC=E(_ez.b)-E(_eA.b),_eD=Math.sqrt(_eB*_eB+_eC*_eC);if(!_eD){return (_ex<=1)?new T3(0,_ey,_eA,_ez):new T3(0,new T2(0,_eq,_ep),_eq,_ep);}else{var _eE=_eB/_eD+0*(_eC/_eD);return (_eE==0)?(_ex<=0)?new T3(0,_ey,_eA,_ez):new T3(0,new T2(0,_eq,_ep),_eq,_ep):(_eE<=0)?(_ex<= -_eE)?new T3(0,_ey,_eA,_ez):new T3(0,new T2(0,_eq,_ep),_eq,_ep):(_ex<=_eE)?new T3(0,_ey,_eA,_ez):new T3(0,new T2(0,_eq,_ep),_eq,_ep);}},_eF=_eu+0*_ev;if(!_eF){return new F(function(){return _ew(0);});}else{if(_eF<=0){return new F(function(){return _ew( -_eF);});}else{return new F(function(){return _ew(_eF);});}}},_eG=Math.sqrt(_er*_er+_es*_es);if(!_eG){return new F(function(){return _et(1,0);});}else{return new F(function(){return _et(_er/_eG,_es/_eG);});}};if(!E(_cQ)){var _eH=E(_cs);if(!_eH._){return E(_ay);}else{var _eI=B(_e8(_eH.b));if(!_eI._){return E(_8X);}else{var _eJ=E(_eI.a),_eK=B(_em(E(B(_6S(_eI.b,_eJ.a,_eJ.b)).b)));return new F(function(){return _dg(_eK.a,_eK.b,_eK.c);});}}}else{var _eL=E(_c9);if(!_eL._){return E(_ay);}else{var _eM=B(_e8(_eL.b));if(!_eM._){return E(_8X);}else{var _eN=E(_eM.a),_eO=B(_em(E(B(_6S(_eM.b,_eN.a,_eN.b)).b)));return new F(function(){return _dg(_eO.a,_eO.b,_eO.c);});}}}}else{var _eP=_d7/_d9,_eQ=_d8/_d9,_eR=E(_cX),_eS=E(_eR.a),_eT=E(_eR.b),_eU=E(_cY),_eV= -(E(_eU.b)-_eT),_eW=E(_eU.a)-_eS,_eX=function(_eY,_eZ,_f0){var _f1=E(_eZ),_f2=E(_f0),_f3=_d3*_eP+_d4*_eQ,_f4=_d5*_eP+_d6*_eQ-_f3,_f5=new T(function(){var _f6=E(E(_eY).a);return (E(_f6.a)*_eP+E(_f6.b)*_eQ-_f3)/_f4;}),_f7=new T(function(){var _f8=E(E(_eY).b);return (E(_f8.a)*_eP+E(_f8.b)*_eQ-_f3)/_f4;}),_f9=function(_fa){var _fb=new T(function(){var _fc=E(_fa);if(0>_fc){return E(_8T);}else{if(1>_fc){return E(_fc);}else{return E(_8U);}}}),_fd=new T(function(){return E(_f7)-E(_fb);}),_fe=new T(function(){return E(_fb)-E(_f5);});return new T2(0,new T(function(){var _ff=E(_fd),_fg=E(_fe);return (E(_f1.a)*_ff+E(_f2.a)*_fg)/(_ff+_fg);}),new T(function(){var _fh=E(_fd),_fi=E(_fe);return (E(_f1.b)*_fh+E(_f2.b)*_fi)/(_fh+_fi);}));},_fj=B(_f9(_f5)),_fk=E(_fj.a),_fl=E(_fj.b),_fm=new T(function(){var _fn=B(_f9(_f7)),_fo=E(_fn.a),_fp=E(_fn.b),_fq=(_eV*_fo+_eW*_fp-(_eV*_eS+_eW*_eT))/Math.sqrt(_eV*_eV+_eW*_eW);if(_fq<0){return new T2(1,new T2(0,new T2(0,_fo,_fp), -_fq),_4);}else{return __Z;}}),_fr=(_eV*_fk+_eW*_fl-(_eV*_eS+_eW*_eT))/Math.sqrt(_eV*_eV+_eW*_eW);if(_fr<0){var _fs=new T2(1,new T2(0,new T2(0,_fk,_fl), -_fr),_fm);}else{var _fs=E(_fm);}var _ft=new T(function(){return B(_ak(_7T,_fs));}),_fu= -_eQ,_fv=new T(function(){var _fw=function(_fx){var _fy=E(_fx),_fz=_fy.b,_fA=E(_fy.a);return new T2(0,new T(function(){return E(_fA.a)+_fu*E(_fz);}),new T(function(){return E(_fA.b)+_eP*E(_fz);}));};return B(_ak(_fw,_fs));}),_fB=new T(function(){if(!E(_cQ)){var _fC=new T(function(){return E(E(_b0).b);}),_fD=new T(function(){return E(E(_b0).a);});return B(_ak(function(_cx){return new F(function(){return _6A(new T2(0,_fD,_fC),_cx);});},_fv));}else{var _fE=new T(function(){return E(E(_b0).b);}),_fF=new T(function(){return E(E(_b0).a);});return B(_ak(function(_cx){return new F(function(){return _6A(new T2(0,_fF,_fE),_cx);});},_ft));}}),_fG=new T(function(){if(!E(_cQ)){return new T2(0,_fu,_eP);}else{return new T2(0, -_fu, -_eP);}}),_fH=function(_fI,_fJ,_fK){return new T5(0,_fI,_fJ,_fG,_fG,_fK);};if(!E(_cQ)){var _fL=new T(function(){return E(E(_aY).b);}),_fM=new T(function(){return E(E(_aY).a);});return new F(function(){return _aO(_fH,B(_ak(function(_cx){return new F(function(){return _6A(new T2(0,_fM,_fL),_cx);});},_ft)),_fB,new T(function(){return B(_ak(_av,_fs));},1));});}else{var _fN=new T(function(){return E(E(_aY).b);}),_fO=new T(function(){return E(E(_aY).a);});return new F(function(){return _aO(_fH,B(_ak(function(_cx){return new F(function(){return _6A(new T2(0,_fO,_fN),_cx);});},_fv)),_fB,new T(function(){return B(_ak(_av,_fs));},1));});}},_fP=function(_fQ){var _fR=function(_fS,_fT){while(1){var _fU=B((function(_fV,_fW){var _fX=E(_fV);if(!_fX._){return __Z;}else{var _fY=_fX.b,_fZ=E(_fW);if(!_fZ._){return __Z;}else{var _g0=_fZ.b,_g1=E(_fX.a),_g2=(_eV*E(_g1.a)+_eW*E(_g1.b)-(_eV*_eS+_eW*_eT))/Math.sqrt(_eV*_eV+_eW*_eW);if(_g2<0){return new T2(1,new T2(0,new T1(1,_g2),_fZ.a),new T(function(){return B(_fR(_fY,_g0));}));}else{_fS=_fY;_fT=_g0;return __continue;}}}})(_fS,_fT));if(_fU!=__continue){return _fU;}}};return new F(function(){return _fR(_fQ,_8Y);});},_g3=function(_g4){var _g5=B(_6O(_cV,_g4)),_g6=E(_g5.a),_g7=E(_g5.b),_g8=E(_g6.a)-E(_g7.a),_g9=E(_g6.b)-E(_g7.b),_ga=function(_gb,_gc){var _gd=function(_ge){var _gf=B(_6O(_cV,B(_ao(_g4+1|0,4)))),_gg=E(_gf.b),_gh=E(_gf.a),_gi=E(_gg.a)-E(_gh.a),_gj=E(_gg.b)-E(_gh.b),_gk=Math.sqrt(_gi*_gi+_gj*_gj);if(!_gk){var _gl=_eP+_eQ*0;return (_gl==0)?(_ge<=0)?new T3(0,_gf,_gh,_gg):new T3(0,new T2(0,_g7,_g6),_g7,_g6):(_gl<=0)?(_ge<= -_gl)?new T3(0,_gf,_gh,_gg):new T3(0,new T2(0,_g7,_g6),_g7,_g6):(_ge<=_gl)?new T3(0,_gf,_gh,_gg):new T3(0,new T2(0,_g7,_g6),_g7,_g6);}else{var _gm=_eP*(_gi/_gk)+_eQ*(_gj/_gk);return (_gm==0)?(_ge<=0)?new T3(0,_gf,_gh,_gg):new T3(0,new T2(0,_g7,_g6),_g7,_g6):(_gm<=0)?(_ge<= -_gm)?new T3(0,_gf,_gh,_gg):new T3(0,new T2(0,_g7,_g6),_g7,_g6):(_ge<=_gm)?new T3(0,_gf,_gh,_gg):new T3(0,new T2(0,_g7,_g6),_g7,_g6);}},_gn=_eP*_gb+_eQ*_gc;if(!_gn){return new F(function(){return _gd(0);});}else{if(_gn<=0){return new F(function(){return _gd( -_gn);});}else{return new F(function(){return _gd(_gn);});}}},_go=Math.sqrt(_g8*_g8+_g9*_g9);if(!_go){return new F(function(){return _ga(1,0);});}else{return new F(function(){return _ga(_g8/_go,_g9/_go);});}};if(!E(_cQ)){var _gp=E(_cs);if(!_gp._){return E(_ay);}else{var _gq=B(_fP(_gp.b));if(!_gq._){return E(_8X);}else{var _gr=E(_gq.a),_gs=B(_g3(E(B(_6S(_gq.b,_gr.a,_gr.b)).b)));return new F(function(){return _eX(_gs.a,_gs.b,_gs.c);});}}}else{var _gt=E(_c9);if(!_gt._){return E(_ay);}else{var _gu=B(_fP(_gt.b));if(!_gu._){return E(_8X);}else{var _gv=E(_gu.a),_gw=B(_g3(E(B(_6S(_gu.b,_gv.a,_gv.b)).b)));return new F(function(){return _eX(_gw.a,_gw.b,_gw.c);});}}}}};if(!E(_cQ)){if(!E(_cM)._){return E(_a6);}else{var _gx=B(_6O(_cU,_cK)),_gy=_gx.a,_gz=_gx.b;return new F(function(){return _cW(_gy,_gz,_gy,_gz);});}}else{if(!E(_cN)._){return E(_a6);}else{var _gA=B(_6O(_cU,_cG)),_gB=_gA.a,_gC=_gA.b;return new F(function(){return _cW(_gB,_gC,_gB,_gC);});}}};if(!E(_cQ)){return new F(function(){return _cT(_ci,_cy);});}else{return new F(function(){return _cT(_cy,_ci);});}}}}}}else{return __Z;}}}},_gD=new T(function(){return B(_40(-1,1));}),_gE=new T(function(){return eval("scrH");}),_gF=function(_gG,_gH){var _gI=new T(function(){var _gJ=E(E(_gG).b),_gK=E(E(_gH).b);if(E(_gJ.a)!=E(_gK.a)){return false;}else{if(E(_gJ.b)!=E(_gK.b)){return false;}else{return E(_gJ.c)==E(_gK.c);}}}),_gL=new T(function(){return E(E(_gH).a);}),_gM=function(_gN){var _gO=E(_gN);if(!_gO._){return __Z;}else{var _gP=_gO.a,_gQ=new T(function(){return B(_gM(_gO.b));}),_gR=function(_gS){var _gT=E(_gS);if(!_gT._){return E(_gQ);}else{var _gU=_gT.a,_gV=new T(function(){return B(_gR(_gT.b));}),_gW=function(_gX){var _gY=E(_gG),_gZ=new T(function(){var _h0=E(E(_gH).b);return new T3(0,new T(function(){return E(_h0.a)+E(_gP)*E(_1s);}),new T(function(){return E(_h0.b)+E(_gU)*E(_gE);}),_h0.c);});return new F(function(){return _0(B(_aW(_gY.a,_gY.b,_gL,_gZ)),_gV);});};if(!E(_gI)){return new F(function(){return _gW(_);});}else{if(!E(_gP)){if(!E(_gU)){return E(_gV);}else{return new F(function(){return _gW(_);});}}else{return new F(function(){return _gW(_);});}}}};return new F(function(){return _gR(_gD);});}};return new F(function(){return _gM(_gD);});},_h1=function(_h2,_h3){var _h4=E(_h2),_h5=E(_h3);return E(_h4.a)*E(_h5.b)-E(_h5.a)*E(_h4.b);},_h6=function(_h7){var _h8=E(_h7);if(!_h8._){return __Z;}else{return new F(function(){return _0(_h8.a,new T(function(){return B(_h6(_h8.b));},1));});}},_h9=function(_ha){var _hb=E(_ha);if(!_hb._){return __Z;}else{return new F(function(){return _0(_hb.a,new T(function(){return B(_h9(_hb.b));},1));});}},_hc=new T(function(){return B(unCStr(")"));}),_hd=function(_he,_hf){var _hg=new T(function(){var _hh=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_2t(0,_hf,_4)),_hc));})));},1);return B(_0(B(_2t(0,_he,_4)),_hh));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_hg)));});},_hi=function(_hj,_hk,_hl,_hm,_hn,_){if(_hj<=_hk){var _ho=function(_hp,_hq,_){var _hr=_hp+1|0;if(_hr<=_hk){var _hs=new T(function(){if(_hj>_hp){return E(_6p);}else{if(_hp>_hk){return E(_6p);}else{var _ht=_hp-_hj|0;if(0>_ht){return B(_hd(_ht,_hl));}else{if(_ht>=_hl){return B(_hd(_ht,_hl));}else{return E(_hm[_ht]);}}}}}),_hu=function(_hv,_hw,_){var _hx=new T(function(){var _hy=function(_hz){var _hA=E(_hz),_hB=_hA.c,_hC=_hA.d;return new T5(0,_hp,_hv,new T3(0,new T(function(){return E(E(_hB).a);}),new T(function(){return E(E(_hB).b);}),new T(function(){return B(_h1(_hA.a,_hB));})),new T3(0,new T(function(){return E(E(_hC).a);}),new T(function(){return E(E(_hC).b);}),new T(function(){return B(_h1(_hA.b,_hC));})),_hA.e);};return B(_ak(_hy,B(_gF(_hs,new T(function(){if(_hj>_hv){return E(_6p);}else{if(_hv>_hk){return E(_6p);}else{var _hD=_hv-_hj|0;if(0>_hD){return B(_hd(_hD,_hl));}else{if(_hD>=_hl){return B(_hd(_hD,_hl));}else{return E(_hm[_hD]);}}}}})))));});if(_hv!=_hk){var _hE=B(_hu(_hv+1|0,_hw,_));return new T2(0,new T2(1,_hx,new T(function(){return E(E(_hE).a);})),new T(function(){return E(E(_hE).b);}));}else{return new T2(0,new T2(1,_hx,_4),_hw);}},_hF=B(_hu(_hr,_hq,_));if(_hp!=_hk){var _hG=B(_ho(_hr,new T(function(){return E(E(_hF).b);}),_));return new T2(0,new T2(1,new T(function(){return B(_h9(E(_hF).a));}),new T(function(){return E(E(_hG).a);})),new T(function(){return E(E(_hG).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_h9(E(_hF).a));}),_4),new T(function(){return E(E(_hF).b);}));}}else{if(_hp!=_hk){var _hH=B(_ho(_hr,_hq,_));return new T2(0,new T2(1,_4,new T(function(){return E(E(_hH).a);})),new T(function(){return E(E(_hH).b);}));}else{return new T2(0,new T2(1,_4,_4),_hq);}}},_hI=B(_ho(_hj,_hn,_));return new T2(0,new T(function(){return B(_h6(E(_hI).a));}),new T(function(){return E(E(_hI).b);}));}else{return new T2(0,_4,_hn);}},_hJ=function(_hK){var _hL=E(_hK),_hM=_hL.c,_hN=new T(function(){var _hO=E(_hL.b),_hP=E(_hM);return new T3(0,new T(function(){return E(_hO.a)+E(_hP.a)*0.2;}),new T(function(){return E(_hO.b)+E(_hP.b)*0.2;}),new T(function(){return E(_hO.c)+E(_hP.c)*0.2;}));});return new T5(0,_hL.a,_hN,_hM,_hL.d,_hL.e);},_hQ=function(_hR,_hS,_hT,_hU,_hV){var _hW=new T(function(){var _hX=E(_hT),_hY=E(_hU),_hZ=new T(function(){var _i0=E(E(_hS).b)/E(_gE);return 0.2*Math.sin((_i0+_i0)*3.141592653589793);});return new T3(0,new T(function(){return E(_hX.a)+E(_hY.a)*E(_hZ);}),new T(function(){return E(_hX.b)+E(_hY.b)*E(_hZ);}),new T(function(){return E(_hX.c)+E(_hY.c)*E(_hZ);}));});return new T5(0,_hR,_hS,_hW,_hU,_hV);},_i1=function(_i2){var _i3=E(_i2),_i4=B(_hQ(_i3.a,_i3.b,_i3.c,_i3.d,_i3.e));return new T5(0,_i4.a,_i4.b,_i4.c,_i4.d,_i4.e);},_i5=function(_i6,_){return new T2(0,_4,_i6);},_i7=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_i8=new T(function(){return B(err(_i7));}),_i9=function(_ia,_ib){var _ic=new T(function(){var _id=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_2t(0,_ia,_4)),_hc));})));},1);return B(_0(B(_2t(0,_ib,_4)),_id));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_ic)));});},_ie=0.6,_if=function(_ig){var _ih=E(_ig);if(!_ih._){return E(_i5);}else{var _ii=_ih.a,_ij=new T(function(){return B(_if(_ih.b));}),_ik=new T(function(){return 0.1*E(E(_ii).e)/0.2;}),_il=new T(function(){var _im=E(_ii);if(E(_im.a)!=E(_im.b)){return E(_8U);}else{return E(_ie);}}),_in=function(_io,_){var _ip=E(_io),_iq=_ip.c,_ir=_ip.d,_is=E(_ip.a),_it=E(_ip.b),_iu=E(_ii),_iv=E(_iu.a);if(_is>_iv){return E(_i8);}else{if(_iv>_it){return E(_i8);}else{var _iw=_iv-_is|0;if(0>_iw){return new F(function(){return _i9(_iq,_iw);});}else{if(_iw>=_iq){return new F(function(){return _i9(_iq,_iw);});}else{var _ix=E(_ir[_iw]),_iy=E(_ix.e),_iz=E(_iy.a),_iA=E(_iy.b),_iB=E(_iy.c),_iC=E(_iu.c),_iD=E(_iC.a),_iE=E(_iC.b),_iF=E(_iC.c),_iG=E(_iu.b);if(_is>_iG){return E(_i8);}else{if(_iG>_it){return E(_i8);}else{var _iH=_iG-_is|0;if(0>_iH){return new F(function(){return _hd(_iH,_iq);});}else{if(_iH>=_iq){return new F(function(){return _hd(_iH,_iq);});}else{var _iI=E(_ir[_iH]),_iJ=E(_iI.e),_iK=E(_iJ.a),_iL=E(_iJ.b),_iM=E(_iJ.c),_iN=E(_iu.d),_iO=E(_iN.a),_iP=E(_iN.b),_iQ=E(_iN.c),_iR=_iD*_iz*_iD+_iE*_iA*_iE+_iF*_iB*_iF+_iO*_iK*_iO+_iP*_iL*_iP+_iQ*_iM*_iQ;if(!_iR){var _iS=B(A2(_ij,_ip,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_iS).a);})),new T(function(){return E(E(_iS).b);}));}else{var _iT=E(_ix.c),_iU=E(_iT.a),_iV=E(_iT.b),_iW=E(_iT.c),_iX=E(_iI.c),_iY= -((_iU*_iD+_iV*_iE+_iW*_iF-(E(_iX.a)*_iO+E(_iX.b)*_iP+E(_iX.c)*_iQ)-E(_ik))/_iR);if(_iY<0){var _iZ=B(A2(_ij,_ip,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_iZ).a);})),new T(function(){return E(E(_iZ).b);}));}else{var _j0=new T(function(){var _j1=function(_){var _j2=newArr(_iq,_1k),_j3=_j2,_j4=function(_j5,_){while(1){if(_j5!=_iq){var _=_j3[_j5]=_ir[_j5],_j6=_j5+1|0;_j5=_j6;continue;}else{return E(_);}}},_=B(_j4(0,_)),_j7=new T(function(){return _iY*E(_il);}),_=_j3[_iw]=new T5(0,_ix.a,_ix.b,new T3(0,new T(function(){return _iU+_iz*_iD*E(_j7);}),new T(function(){return _iV+_iA*_iE*E(_j7);}),new T(function(){return _iW+_iB*_iF*E(_j7);})),_ix.d,_iy);return new T4(0,E(_is),E(_it),_iq,_j3);},_j8=B(_1L(_j1)),_j9=_j8.c,_ja=_j8.d,_jb=E(_j8.a),_jc=E(_j8.b);if(_jb>_iG){return E(_j8);}else{if(_iG>_jc){return E(_j8);}else{var _jd=function(_){var _je=newArr(_j9,_1k),_jf=_je,_jg=function(_jh,_){while(1){if(_jh!=_j9){var _=_jf[_jh]=_ja[_jh],_ji=_jh+1|0;_jh=_ji;continue;}else{return E(_);}}},_=B(_jg(0,_)),_jj=_iG-_jb|0;if(0>_jj){return new F(function(){return _hd(_jj,_j9);});}else{if(_jj>=_j9){return new F(function(){return _hd(_jj,_j9);});}else{var _jk=new T(function(){var _jl=E(_ja[_jj]),_jm=new T(function(){return _iY*E(_il);}),_jn=new T(function(){var _jo=E(_jl.c);return new T3(0,new T(function(){return E(_jo.a)-_iK*_iO*E(_jm);}),new T(function(){return E(_jo.b)-_iL*_iP*E(_jm);}),new T(function(){return E(_jo.c)-_iM*_iQ*E(_jm);}));});return new T5(0,_jl.a,_jl.b,_jn,_jl.d,_jl.e);}),_=_jf[_jj]=_jk;return new T4(0,E(_jb),E(_jc),_j9,_jf);}}};return B(_1L(_jd));}}}),_jp=B(A2(_ij,_j0,_));return new T2(0,new T2(1,_5,new T(function(){return E(E(_jp).a);})),new T(function(){return E(E(_jp).b);}));}}}}}}}}}}};return E(_in);}},_jq=new T1(0,1),_jr=function(_js,_jt){var _ju=E(_js);if(!_ju._){var _jv=_ju.a,_jw=E(_jt);if(!_jw._){var _jx=_jw.a;return (_jv!=_jx)?(_jv>_jx)?2:0:1;}else{var _jy=I_compareInt(_jw.a,_jv);return (_jy<=0)?(_jy>=0)?1:2:0;}}else{var _jz=_ju.a,_jA=E(_jt);if(!_jA._){var _jB=I_compareInt(_jz,_jA.a);return (_jB>=0)?(_jB<=0)?1:2:0;}else{var _jC=I_compare(_jz,_jA.a);return (_jC>=0)?(_jC<=0)?1:2:0;}}},_jD=new T(function(){return B(unCStr("base"));}),_jE=new T(function(){return B(unCStr("GHC.Exception"));}),_jF=new T(function(){return B(unCStr("ArithException"));}),_jG=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_jD,_jE,_jF),_jH=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_jG,_4,_4),_jI=function(_jJ){return E(_jH);},_jK=function(_jL){var _jM=E(_jL);return new F(function(){return _98(B(_96(_jM.a)),_jI,_jM.b);});},_jN=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_jO=new T(function(){return B(unCStr("denormal"));}),_jP=new T(function(){return B(unCStr("divide by zero"));}),_jQ=new T(function(){return B(unCStr("loss of precision"));}),_jR=new T(function(){return B(unCStr("arithmetic underflow"));}),_jS=new T(function(){return B(unCStr("arithmetic overflow"));}),_jT=function(_jU,_jV){switch(E(_jU)){case 0:return new F(function(){return _0(_jS,_jV);});break;case 1:return new F(function(){return _0(_jR,_jV);});break;case 2:return new F(function(){return _0(_jQ,_jV);});break;case 3:return new F(function(){return _0(_jP,_jV);});break;case 4:return new F(function(){return _0(_jO,_jV);});break;default:return new F(function(){return _0(_jN,_jV);});}},_jW=function(_jX){return new F(function(){return _jT(_jX,_4);});},_jY=function(_jZ,_k0,_k1){return new F(function(){return _jT(_k0,_k1);});},_k2=function(_k3,_k4){return new F(function(){return _2H(_jT,_k3,_k4);});},_k5=new T3(0,_jY,_jW,_k2),_k6=new T(function(){return new T5(0,_jI,_k5,_k7,_jK,_jW);}),_k7=function(_9H){return new T2(0,_k6,_9H);},_k8=3,_k9=new T(function(){return B(_k7(_k8));}),_ka=new T(function(){return die(_k9);}),_kb=function(_kc,_kd){var _ke=E(_kc);return (_ke._==0)?_ke.a*Math.pow(2,_kd):I_toNumber(_ke.a)*Math.pow(2,_kd);},_kf=function(_kg,_kh){var _ki=E(_kg);if(!_ki._){var _kj=_ki.a,_kk=E(_kh);return (_kk._==0)?_kj==_kk.a:(I_compareInt(_kk.a,_kj)==0)?true:false;}else{var _kl=_ki.a,_km=E(_kh);return (_km._==0)?(I_compareInt(_kl,_km.a)==0)?true:false:(I_compare(_kl,_km.a)==0)?true:false;}},_kn=function(_ko){var _kp=E(_ko);if(!_kp._){return E(_kp.a);}else{return new F(function(){return I_toInt(_kp.a);});}},_kq=function(_kr,_ks){while(1){var _kt=E(_kr);if(!_kt._){var _ku=_kt.a,_kv=E(_ks);if(!_kv._){var _kw=_kv.a,_kx=addC(_ku,_kw);if(!E(_kx.b)){return new T1(0,_kx.a);}else{_kr=new T1(1,I_fromInt(_ku));_ks=new T1(1,I_fromInt(_kw));continue;}}else{_kr=new T1(1,I_fromInt(_ku));_ks=_kv;continue;}}else{var _ky=E(_ks);if(!_ky._){_kr=_kt;_ks=new T1(1,I_fromInt(_ky.a));continue;}else{return new T1(1,I_add(_kt.a,_ky.a));}}}},_kz=function(_kA,_kB){while(1){var _kC=E(_kA);if(!_kC._){var _kD=E(_kC.a);if(_kD==(-2147483648)){_kA=new T1(1,I_fromInt(-2147483648));continue;}else{var _kE=E(_kB);if(!_kE._){var _kF=_kE.a;return new T2(0,new T1(0,quot(_kD,_kF)),new T1(0,_kD%_kF));}else{_kA=new T1(1,I_fromInt(_kD));_kB=_kE;continue;}}}else{var _kG=E(_kB);if(!_kG._){_kA=_kC;_kB=new T1(1,I_fromInt(_kG.a));continue;}else{var _kH=I_quotRem(_kC.a,_kG.a);return new T2(0,new T1(1,_kH.a),new T1(1,_kH.b));}}}},_kI=new T1(0,0),_kJ=function(_kK,_kL){while(1){var _kM=E(_kK);if(!_kM._){_kK=new T1(1,I_fromInt(_kM.a));continue;}else{return new T1(1,I_shiftLeft(_kM.a,_kL));}}},_kN=function(_kO,_kP,_kQ){if(!B(_kf(_kQ,_kI))){var _kR=B(_kz(_kP,_kQ)),_kS=_kR.a;switch(B(_jr(B(_kJ(_kR.b,1)),_kQ))){case 0:return new F(function(){return _kb(_kS,_kO);});break;case 1:if(!(B(_kn(_kS))&1)){return new F(function(){return _kb(_kS,_kO);});}else{return new F(function(){return _kb(B(_kq(_kS,_jq)),_kO);});}break;default:return new F(function(){return _kb(B(_kq(_kS,_jq)),_kO);});}}else{return E(_ka);}},_kT=function(_kU,_kV){var _kW=E(_kU);if(!_kW._){var _kX=_kW.a,_kY=E(_kV);return (_kY._==0)?_kX>_kY.a:I_compareInt(_kY.a,_kX)<0;}else{var _kZ=_kW.a,_l0=E(_kV);return (_l0._==0)?I_compareInt(_kZ,_l0.a)>0:I_compare(_kZ,_l0.a)>0;}},_l1=new T1(0,1),_l2=function(_l3,_l4){var _l5=E(_l3);if(!_l5._){var _l6=_l5.a,_l7=E(_l4);return (_l7._==0)?_l6<_l7.a:I_compareInt(_l7.a,_l6)>0;}else{var _l8=_l5.a,_l9=E(_l4);return (_l9._==0)?I_compareInt(_l8,_l9.a)<0:I_compare(_l8,_l9.a)<0;}},_la=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_lb=function(_lc){return new F(function(){return _9F(new T1(0,new T(function(){return B(_9T(_lc,_la));})),_9n);});},_ld=function(_le){var _lf=function(_lg,_lh){while(1){if(!B(_l2(_lg,_le))){if(!B(_kT(_lg,_le))){if(!B(_kf(_lg,_le))){return new F(function(){return _lb("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_lh);}}else{return _lh-1|0;}}else{var _li=B(_kJ(_lg,1)),_lj=_lh+1|0;_lg=_li;_lh=_lj;continue;}}};return new F(function(){return _lf(_l1,0);});},_lk=function(_ll){var _lm=E(_ll);if(!_lm._){var _ln=_lm.a>>>0;if(!_ln){return -1;}else{var _lo=function(_lp,_lq){while(1){if(_lp>=_ln){if(_lp<=_ln){if(_lp!=_ln){return new F(function(){return _lb("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_lq);}}else{return _lq-1|0;}}else{var _lr=imul(_lp,2)>>>0,_ls=_lq+1|0;_lp=_lr;_lq=_ls;continue;}}};return new F(function(){return _lo(1,0);});}}else{return new F(function(){return _ld(_lm);});}},_lt=function(_lu){var _lv=E(_lu);if(!_lv._){var _lw=_lv.a>>>0;if(!_lw){return new T2(0,-1,0);}else{var _lx=function(_ly,_lz){while(1){if(_ly>=_lw){if(_ly<=_lw){if(_ly!=_lw){return new F(function(){return _lb("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_lz);}}else{return _lz-1|0;}}else{var _lA=imul(_ly,2)>>>0,_lB=_lz+1|0;_ly=_lA;_lz=_lB;continue;}}};return new T2(0,B(_lx(1,0)),(_lw&_lw-1>>>0)>>>0&4294967295);}}else{var _lC=_lv.a;return new T2(0,B(_lk(_lv)),I_compareInt(I_and(_lC,I_sub(_lC,I_fromInt(1))),0));}},_lD=function(_lE,_lF){var _lG=E(_lE);if(!_lG._){var _lH=_lG.a,_lI=E(_lF);return (_lI._==0)?_lH<=_lI.a:I_compareInt(_lI.a,_lH)>=0;}else{var _lJ=_lG.a,_lK=E(_lF);return (_lK._==0)?I_compareInt(_lJ,_lK.a)<=0:I_compare(_lJ,_lK.a)<=0;}},_lL=function(_lM,_lN){while(1){var _lO=E(_lM);if(!_lO._){var _lP=_lO.a,_lQ=E(_lN);if(!_lQ._){return new T1(0,(_lP>>>0&_lQ.a>>>0)>>>0&4294967295);}else{_lM=new T1(1,I_fromInt(_lP));_lN=_lQ;continue;}}else{var _lR=E(_lN);if(!_lR._){_lM=_lO;_lN=new T1(1,I_fromInt(_lR.a));continue;}else{return new T1(1,I_and(_lO.a,_lR.a));}}}},_lS=function(_lT,_lU){while(1){var _lV=E(_lT);if(!_lV._){var _lW=_lV.a,_lX=E(_lU);if(!_lX._){var _lY=_lX.a,_lZ=subC(_lW,_lY);if(!E(_lZ.b)){return new T1(0,_lZ.a);}else{_lT=new T1(1,I_fromInt(_lW));_lU=new T1(1,I_fromInt(_lY));continue;}}else{_lT=new T1(1,I_fromInt(_lW));_lU=_lX;continue;}}else{var _m0=E(_lU);if(!_m0._){_lT=_lV;_lU=new T1(1,I_fromInt(_m0.a));continue;}else{return new T1(1,I_sub(_lV.a,_m0.a));}}}},_m1=new T1(0,2),_m2=function(_m3,_m4){var _m5=E(_m3);if(!_m5._){var _m6=(_m5.a>>>0&(2<<_m4>>>0)-1>>>0)>>>0,_m7=1<<_m4>>>0;return (_m7<=_m6)?(_m7>=_m6)?1:2:0;}else{var _m8=B(_lL(_m5,B(_lS(B(_kJ(_m1,_m4)),_l1)))),_m9=B(_kJ(_l1,_m4));return (!B(_kT(_m9,_m8)))?(!B(_l2(_m9,_m8)))?1:2:0;}},_ma=function(_mb,_mc){while(1){var _md=E(_mb);if(!_md._){_mb=new T1(1,I_fromInt(_md.a));continue;}else{return new T1(1,I_shiftRight(_md.a,_mc));}}},_me=function(_mf,_mg,_mh,_mi){var _mj=B(_lt(_mi)),_mk=_mj.a;if(!E(_mj.b)){var _ml=B(_lk(_mh));if(_ml<((_mk+_mf|0)-1|0)){var _mm=_mk+(_mf-_mg|0)|0;if(_mm>0){if(_mm>_ml){if(_mm<=(_ml+1|0)){if(!E(B(_lt(_mh)).b)){return 0;}else{return new F(function(){return _kb(_jq,_mf-_mg|0);});}}else{return 0;}}else{var _mn=B(_ma(_mh,_mm));switch(B(_m2(_mh,_mm-1|0))){case 0:return new F(function(){return _kb(_mn,_mf-_mg|0);});break;case 1:if(!(B(_kn(_mn))&1)){return new F(function(){return _kb(_mn,_mf-_mg|0);});}else{return new F(function(){return _kb(B(_kq(_mn,_jq)),_mf-_mg|0);});}break;default:return new F(function(){return _kb(B(_kq(_mn,_jq)),_mf-_mg|0);});}}}else{return new F(function(){return _kb(_mh,(_mf-_mg|0)-_mm|0);});}}else{if(_ml>=_mg){var _mo=B(_ma(_mh,(_ml+1|0)-_mg|0));switch(B(_m2(_mh,_ml-_mg|0))){case 0:return new F(function(){return _kb(_mo,((_ml-_mk|0)+1|0)-_mg|0);});break;case 2:return new F(function(){return _kb(B(_kq(_mo,_jq)),((_ml-_mk|0)+1|0)-_mg|0);});break;default:if(!(B(_kn(_mo))&1)){return new F(function(){return _kb(_mo,((_ml-_mk|0)+1|0)-_mg|0);});}else{return new F(function(){return _kb(B(_kq(_mo,_jq)),((_ml-_mk|0)+1|0)-_mg|0);});}}}else{return new F(function(){return _kb(_mh, -_mk);});}}}else{var _mp=B(_lk(_mh))-_mk|0,_mq=function(_mr){var _ms=function(_mt,_mu){if(!B(_lD(B(_kJ(_mu,_mg)),_mt))){return new F(function(){return _kN(_mr-_mg|0,_mt,_mu);});}else{return new F(function(){return _kN((_mr-_mg|0)+1|0,_mt,B(_kJ(_mu,1)));});}};if(_mr>=_mg){if(_mr!=_mg){return new F(function(){return _ms(_mh,new T(function(){return B(_kJ(_mi,_mr-_mg|0));}));});}else{return new F(function(){return _ms(_mh,_mi);});}}else{return new F(function(){return _ms(new T(function(){return B(_kJ(_mh,_mg-_mr|0));}),_mi);});}};if(_mf>_mp){return new F(function(){return _mq(_mf);});}else{return new F(function(){return _mq(_mp);});}}},_mv=new T1(0,2147483647),_mw=new T(function(){return B(_kq(_mv,_l1));}),_mx=function(_my){var _mz=E(_my);if(!_mz._){var _mA=E(_mz.a);return (_mA==(-2147483648))?E(_mw):new T1(0, -_mA);}else{return new T1(1,I_negate(_mz.a));}},_mB=new T(function(){return 0/0;}),_mC=new T(function(){return -1/0;}),_mD=new T(function(){return 1/0;}),_mE=0,_mF=function(_mG,_mH){if(!B(_kf(_mH,_kI))){if(!B(_kf(_mG,_kI))){if(!B(_l2(_mG,_kI))){return new F(function(){return _me(-1021,53,_mG,_mH);});}else{return  -B(_me(-1021,53,B(_mx(_mG)),_mH));}}else{return E(_mE);}}else{return (!B(_kf(_mG,_kI)))?(!B(_l2(_mG,_kI)))?E(_mD):E(_mC):E(_mB);}},_mI=function(_mJ){var _mK=E(_mJ);return new F(function(){return _mF(_mK.a,_mK.b);});},_mL=function(_mM){return 1/E(_mM);},_mN=function(_mO){var _mP=E(_mO),_mQ=E(_mP);return (_mQ==0)?E(_mE):(_mQ<=0)? -_mQ:E(_mP);},_mR=function(_mS){var _mT=E(_mS);if(!_mT._){return _mT.a;}else{return new F(function(){return I_toNumber(_mT.a);});}},_mU=function(_mV){return new F(function(){return _mR(_mV);});},_mW=function(_mX){var _mY=E(_mX);return (_mY<=0)?(_mY>=0)?E(_mY):E(_6r):E(_6q);},_mZ=function(_n0,_n1){return E(_n0)+E(_n1);},_n2=function(_n3,_n4){return E(_n3)*E(_n4);},_n5={_:0,a:_mZ,b:_6s,c:_n2,d:_a8,e:_mN,f:_mW,g:_mU},_n6=function(_n7,_n8){return E(_n7)/E(_n8);},_n9=new T4(0,_n5,_n6,_mL,_mI),_na=function(_nb,_nc){return (E(_nb)!=E(_nc))?true:false;},_nd=function(_ne,_nf){return E(_ne)==E(_nf);},_ng=new T2(0,_nd,_na),_nh=function(_ni,_nj){return E(_ni)<E(_nj);},_nk=function(_nl,_nm){return E(_nl)<=E(_nm);},_nn=function(_no,_np){return E(_no)>E(_np);},_nq=function(_nr,_ns){return E(_nr)>=E(_ns);},_nt=function(_nu,_nv){var _nw=E(_nu),_nx=E(_nv);return (_nw>=_nx)?(_nw!=_nx)?2:1:0;},_ny=function(_nz,_nA){var _nB=E(_nz),_nC=E(_nA);return (_nB>_nC)?E(_nB):E(_nC);},_nD=function(_nE,_nF){var _nG=E(_nE),_nH=E(_nF);return (_nG>_nH)?E(_nH):E(_nG);},_nI={_:0,a:_ng,b:_nt,c:_nh,d:_nk,e:_nn,f:_nq,g:_ny,h:_nD},_nJ=function(_nK){var _nL=I_decodeDouble(_nK);return new T2(0,new T1(1,_nL.b),_nL.a);},_nM=function(_nN){return new T1(0,_nN);},_nO=function(_nP){var _nQ=hs_intToInt64(2147483647),_nR=hs_leInt64(_nP,_nQ);if(!_nR){return new T1(1,I_fromInt64(_nP));}else{var _nS=hs_intToInt64(-2147483648),_nT=hs_geInt64(_nP,_nS);if(!_nT){return new T1(1,I_fromInt64(_nP));}else{var _nU=hs_int64ToInt(_nP);return new F(function(){return _nM(_nU);});}}},_nV=new T(function(){var _nW=newByteArr(256),_nX=_nW,_=_nX["v"]["i8"][0]=8,_nY=function(_nZ,_o0,_o1,_){while(1){if(_o1>=256){if(_nZ>=256){return E(_);}else{var _o2=imul(2,_nZ)|0,_o3=_o0+1|0,_o4=_nZ;_nZ=_o2;_o0=_o3;_o1=_o4;continue;}}else{var _=_nX["v"]["i8"][_o1]=_o0,_o4=_o1+_nZ|0;_o1=_o4;continue;}}},_=B(_nY(2,0,1,_));return _nX;}),_o5=function(_o6,_o7){var _o8=hs_int64ToInt(_o6),_o9=E(_nV),_oa=_o9["v"]["i8"][(255&_o8>>>0)>>>0&4294967295];if(_o7>_oa){if(_oa>=8){var _ob=hs_uncheckedIShiftRA64(_o6,8),_oc=function(_od,_oe){while(1){var _of=B((function(_og,_oh){var _oi=hs_int64ToInt(_og),_oj=_o9["v"]["i8"][(255&_oi>>>0)>>>0&4294967295];if(_oh>_oj){if(_oj>=8){var _ok=hs_uncheckedIShiftRA64(_og,8),_ol=_oh-8|0;_od=_ok;_oe=_ol;return __continue;}else{return new T2(0,new T(function(){var _om=hs_uncheckedIShiftRA64(_og,_oj);return B(_nO(_om));}),_oh-_oj|0);}}else{return new T2(0,new T(function(){var _on=hs_uncheckedIShiftRA64(_og,_oh);return B(_nO(_on));}),0);}})(_od,_oe));if(_of!=__continue){return _of;}}};return new F(function(){return _oc(_ob,_o7-8|0);});}else{return new T2(0,new T(function(){var _oo=hs_uncheckedIShiftRA64(_o6,_oa);return B(_nO(_oo));}),_o7-_oa|0);}}else{return new T2(0,new T(function(){var _op=hs_uncheckedIShiftRA64(_o6,_o7);return B(_nO(_op));}),0);}},_oq=function(_or){var _os=hs_intToInt64(_or);return E(_os);},_ot=function(_ou){var _ov=E(_ou);if(!_ov._){return new F(function(){return _oq(_ov.a);});}else{return new F(function(){return I_toInt64(_ov.a);});}},_ow=function(_ox){return I_toInt(_ox)>>>0;},_oy=function(_oz){var _oA=E(_oz);if(!_oA._){return _oA.a>>>0;}else{return new F(function(){return _ow(_oA.a);});}},_oB=function(_oC){var _oD=B(_nJ(_oC)),_oE=_oD.a,_oF=_oD.b;if(_oF<0){var _oG=function(_oH){if(!_oH){return new T2(0,E(_oE),B(_kJ(_jq, -_oF)));}else{var _oI=B(_o5(B(_ot(_oE)), -_oF));return new T2(0,E(_oI.a),B(_kJ(_jq,_oI.b)));}};if(!((B(_oy(_oE))&1)>>>0)){return new F(function(){return _oG(1);});}else{return new F(function(){return _oG(0);});}}else{return new T2(0,B(_kJ(_oE,_oF)),_jq);}},_oJ=function(_oK){var _oL=B(_oB(E(_oK)));return new T2(0,E(_oL.a),E(_oL.b));},_oM=new T3(0,_n5,_nI,_oJ),_oN=function(_oO){return E(E(_oO).a);},_oP=function(_oQ){return E(E(_oQ).a);},_oR=new T1(0,1),_oS=function(_oT){return new F(function(){return _40(E(_oT),2147483647);});},_oU=function(_oV,_oW,_oX){if(_oX<=_oW){var _oY=new T(function(){var _oZ=_oW-_oV|0,_p0=function(_p1){return (_p1>=(_oX-_oZ|0))?new T2(1,_p1,new T(function(){return B(_p0(_p1+_oZ|0));})):new T2(1,_p1,_4);};return B(_p0(_oW));});return new T2(1,_oV,_oY);}else{return (_oX<=_oV)?new T2(1,_oV,_4):__Z;}},_p2=function(_p3,_p4,_p5){if(_p5>=_p4){var _p6=new T(function(){var _p7=_p4-_p3|0,_p8=function(_p9){return (_p9<=(_p5-_p7|0))?new T2(1,_p9,new T(function(){return B(_p8(_p9+_p7|0));})):new T2(1,_p9,_4);};return B(_p8(_p4));});return new T2(1,_p3,_p6);}else{return (_p5>=_p3)?new T2(1,_p3,_4):__Z;}},_pa=function(_pb,_pc){if(_pc<_pb){return new F(function(){return _oU(_pb,_pc,-2147483648);});}else{return new F(function(){return _p2(_pb,_pc,2147483647);});}},_pd=function(_pe,_pf){return new F(function(){return _pa(E(_pe),E(_pf));});},_pg=function(_ph,_pi,_pj){if(_pi<_ph){return new F(function(){return _oU(_ph,_pi,_pj);});}else{return new F(function(){return _p2(_ph,_pi,_pj);});}},_pk=function(_pl,_pm,_pn){return new F(function(){return _pg(E(_pl),E(_pm),E(_pn));});},_po=function(_pp){return E(_pp);},_pq=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_pr=new T(function(){return B(err(_pq));}),_ps=function(_pt){var _pu=E(_pt);return (_pu==(-2147483648))?E(_pr):_pu-1|0;},_pv=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_pw=new T(function(){return B(err(_pv));}),_px=function(_py){var _pz=E(_py);return (_pz==2147483647)?E(_pw):_pz+1|0;},_pA={_:0,a:_px,b:_ps,c:_po,d:_po,e:_oS,f:_pd,g:_45,h:_pk},_pB=function(_pC,_pD){if(_pC<=0){if(_pC>=0){return new F(function(){return quot(_pC,_pD);});}else{if(_pD<=0){return new F(function(){return quot(_pC,_pD);});}else{return quot(_pC+1|0,_pD)-1|0;}}}else{if(_pD>=0){if(_pC>=0){return new F(function(){return quot(_pC,_pD);});}else{if(_pD<=0){return new F(function(){return quot(_pC,_pD);});}else{return quot(_pC+1|0,_pD)-1|0;}}}else{return quot(_pC-1|0,_pD)-1|0;}}},_pE=0,_pF=new T(function(){return B(_k7(_pE));}),_pG=new T(function(){return die(_pF);}),_pH=function(_pI,_pJ){var _pK=E(_pJ);switch(_pK){case -1:var _pL=E(_pI);if(_pL==(-2147483648)){return E(_pG);}else{return new F(function(){return _pB(_pL,-1);});}break;case 0:return E(_ka);default:return new F(function(){return _pB(_pI,_pK);});}},_pM=function(_pN,_pO){return new F(function(){return _pH(E(_pN),E(_pO));});},_pP=0,_pQ=new T2(0,_pG,_pP),_pR=function(_pS,_pT){var _pU=E(_pS),_pV=E(_pT);switch(_pV){case -1:var _pW=E(_pU);if(_pW==(-2147483648)){return E(_pQ);}else{if(_pW<=0){if(_pW>=0){var _pX=quotRemI(_pW,-1);return new T2(0,_pX.a,_pX.b);}else{var _pY=quotRemI(_pW,-1);return new T2(0,_pY.a,_pY.b);}}else{var _pZ=quotRemI(_pW-1|0,-1);return new T2(0,_pZ.a-1|0,(_pZ.b+(-1)|0)+1|0);}}break;case 0:return E(_ka);default:if(_pU<=0){if(_pU>=0){var _q0=quotRemI(_pU,_pV);return new T2(0,_q0.a,_q0.b);}else{if(_pV<=0){var _q1=quotRemI(_pU,_pV);return new T2(0,_q1.a,_q1.b);}else{var _q2=quotRemI(_pU+1|0,_pV);return new T2(0,_q2.a-1|0,(_q2.b+_pV|0)-1|0);}}}else{if(_pV>=0){if(_pU>=0){var _q3=quotRemI(_pU,_pV);return new T2(0,_q3.a,_q3.b);}else{if(_pV<=0){var _q4=quotRemI(_pU,_pV);return new T2(0,_q4.a,_q4.b);}else{var _q5=quotRemI(_pU+1|0,_pV);return new T2(0,_q5.a-1|0,(_q5.b+_pV|0)-1|0);}}}else{var _q6=quotRemI(_pU-1|0,_pV);return new T2(0,_q6.a-1|0,(_q6.b+_pV|0)+1|0);}}}},_q7=function(_q8,_q9){var _qa=E(_q9);switch(_qa){case -1:return E(_pP);case 0:return E(_ka);default:return new F(function(){return _ao(E(_q8),_qa);});}},_qb=function(_qc,_qd){var _qe=E(_qc),_qf=E(_qd);switch(_qf){case -1:var _qg=E(_qe);if(_qg==(-2147483648)){return E(_pG);}else{return new F(function(){return quot(_qg,-1);});}break;case 0:return E(_ka);default:return new F(function(){return quot(_qe,_qf);});}},_qh=function(_qi,_qj){var _qk=E(_qi),_ql=E(_qj);switch(_ql){case -1:var _qm=E(_qk);if(_qm==(-2147483648)){return E(_pQ);}else{var _qn=quotRemI(_qm,-1);return new T2(0,_qn.a,_qn.b);}break;case 0:return E(_ka);default:var _qo=quotRemI(_qk,_ql);return new T2(0,_qo.a,_qo.b);}},_qp=function(_qq,_qr){var _qs=E(_qr);switch(_qs){case -1:return E(_pP);case 0:return E(_ka);default:return E(_qq)%_qs;}},_qt=function(_qu){return new F(function(){return _nM(E(_qu));});},_qv=function(_qw){return new T2(0,E(B(_nM(E(_qw)))),E(_oR));},_qx=function(_qy,_qz){return imul(E(_qy),E(_qz))|0;},_qA=function(_qB,_qC){return E(_qB)+E(_qC)|0;},_qD=function(_qE){var _qF=E(_qE);return (_qF<0)? -_qF:E(_qF);},_qG=function(_qH){return new F(function(){return _kn(_qH);});},_qI=function(_qJ){return  -E(_qJ);},_qK=-1,_qL=0,_qM=1,_qN=function(_qO){var _qP=E(_qO);return (_qP>=0)?(E(_qP)==0)?E(_qL):E(_qM):E(_qK);},_qQ={_:0,a:_qA,b:_4g,c:_qx,d:_qI,e:_qD,f:_qN,g:_qG},_qR=new T3(0,_qQ,_4V,_qv),_qS={_:0,a:_qR,b:_pA,c:_qb,d:_qp,e:_pM,f:_q7,g:_qh,h:_pR,i:_qt},_qT=new T1(0,2),_qU=function(_qV,_qW){while(1){var _qX=E(_qV);if(!_qX._){var _qY=_qX.a,_qZ=E(_qW);if(!_qZ._){var _r0=_qZ.a;if(!(imul(_qY,_r0)|0)){return new T1(0,imul(_qY,_r0)|0);}else{_qV=new T1(1,I_fromInt(_qY));_qW=new T1(1,I_fromInt(_r0));continue;}}else{_qV=new T1(1,I_fromInt(_qY));_qW=_qZ;continue;}}else{var _r1=E(_qW);if(!_r1._){_qV=_qX;_qW=new T1(1,I_fromInt(_r1.a));continue;}else{return new T1(1,I_mul(_qX.a,_r1.a));}}}},_r2=function(_r3,_r4,_r5){while(1){if(!(_r4%2)){var _r6=B(_qU(_r3,_r3)),_r7=quot(_r4,2);_r3=_r6;_r4=_r7;continue;}else{var _r8=E(_r4);if(_r8==1){return new F(function(){return _qU(_r3,_r5);});}else{var _r6=B(_qU(_r3,_r3)),_r9=B(_qU(_r3,_r5));_r3=_r6;_r4=quot(_r8-1|0,2);_r5=_r9;continue;}}}},_ra=function(_rb,_rc){while(1){if(!(_rc%2)){var _rd=B(_qU(_rb,_rb)),_re=quot(_rc,2);_rb=_rd;_rc=_re;continue;}else{var _rf=E(_rc);if(_rf==1){return E(_rb);}else{return new F(function(){return _r2(B(_qU(_rb,_rb)),quot(_rf-1|0,2),_rb);});}}}},_rg=function(_rh){return E(E(_rh).c);},_ri=function(_rj){return E(E(_rj).a);},_rk=function(_rl){return E(E(_rl).b);},_rm=function(_rn){return E(E(_rn).b);},_ro=function(_rp){return E(E(_rp).c);},_rq=function(_rr){return E(E(_rr).a);},_rs=new T1(0,0),_rt=new T1(0,2),_ru=function(_rv){return E(E(_rv).g);},_rw=function(_rx){return E(E(_rx).d);},_ry=function(_rz,_rA){var _rB=B(_oN(_rz)),_rC=new T(function(){return B(_oP(_rB));}),_rD=new T(function(){return B(A3(_rw,_rz,_rA,new T(function(){return B(A2(_ru,_rC,_rt));})));});return new F(function(){return A3(_rq,B(_ri(B(_rk(_rB)))),_rD,new T(function(){return B(A2(_ru,_rC,_rs));}));});},_rE=new T(function(){return B(unCStr("Negative exponent"));}),_rF=new T(function(){return B(err(_rE));}),_rG=function(_rH){return E(E(_rH).c);},_rI=function(_rJ,_rK,_rL,_rM){var _rN=B(_oN(_rK)),_rO=new T(function(){return B(_oP(_rN));}),_rP=B(_rk(_rN));if(!B(A3(_ro,_rP,_rM,new T(function(){return B(A2(_ru,_rO,_rs));})))){if(!B(A3(_rq,B(_ri(_rP)),_rM,new T(function(){return B(A2(_ru,_rO,_rs));})))){var _rQ=new T(function(){return B(A2(_ru,_rO,_rt));}),_rR=new T(function(){return B(A2(_ru,_rO,_oR));}),_rS=B(_ri(_rP)),_rT=function(_rU,_rV,_rW){while(1){var _rX=B((function(_rY,_rZ,_s0){if(!B(_ry(_rK,_rZ))){if(!B(A3(_rq,_rS,_rZ,_rR))){var _s1=new T(function(){return B(A3(_rG,_rK,new T(function(){return B(A3(_rm,_rO,_rZ,_rR));}),_rQ));});_rU=new T(function(){return B(A3(_rg,_rJ,_rY,_rY));});_rV=_s1;_rW=new T(function(){return B(A3(_rg,_rJ,_rY,_s0));});return __continue;}else{return new F(function(){return A3(_rg,_rJ,_rY,_s0);});}}else{var _s2=_s0;_rU=new T(function(){return B(A3(_rg,_rJ,_rY,_rY));});_rV=new T(function(){return B(A3(_rG,_rK,_rZ,_rQ));});_rW=_s2;return __continue;}})(_rU,_rV,_rW));if(_rX!=__continue){return _rX;}}},_s3=function(_s4,_s5){while(1){var _s6=B((function(_s7,_s8){if(!B(_ry(_rK,_s8))){if(!B(A3(_rq,_rS,_s8,_rR))){var _s9=new T(function(){return B(A3(_rG,_rK,new T(function(){return B(A3(_rm,_rO,_s8,_rR));}),_rQ));});return new F(function(){return _rT(new T(function(){return B(A3(_rg,_rJ,_s7,_s7));}),_s9,_s7);});}else{return E(_s7);}}else{_s4=new T(function(){return B(A3(_rg,_rJ,_s7,_s7));});_s5=new T(function(){return B(A3(_rG,_rK,_s8,_rQ));});return __continue;}})(_s4,_s5));if(_s6!=__continue){return _s6;}}};return new F(function(){return _s3(_rL,_rM);});}else{return new F(function(){return A2(_ru,_rJ,_oR);});}}else{return E(_rF);}},_sa=new T(function(){return B(err(_rE));}),_sb=function(_sc,_sd){var _se=B(_nJ(_sd)),_sf=_se.a,_sg=_se.b,_sh=new T(function(){return B(_oP(new T(function(){return B(_oN(_sc));})));});if(_sg<0){var _si= -_sg;if(_si>=0){var _sj=E(_si);if(!_sj){var _sk=E(_oR);}else{var _sk=B(_ra(_qT,_sj));}if(!B(_kf(_sk,_kI))){var _sl=B(_kz(_sf,_sk));return new T2(0,new T(function(){return B(A2(_ru,_sh,_sl.a));}),new T(function(){return B(_kb(_sl.b,_sg));}));}else{return E(_ka);}}else{return E(_sa);}}else{var _sm=new T(function(){var _sn=new T(function(){return B(_rI(_sh,_qS,new T(function(){return B(A2(_ru,_sh,_qT));}),_sg));});return B(A3(_rg,_sh,new T(function(){return B(A2(_ru,_sh,_sf));}),_sn));});return new T2(0,_sm,_mE);}},_so=function(_sp){return E(E(_sp).a);},_sq=function(_sr,_ss){var _st=B(_sb(_sr,E(_ss))),_su=_st.a;if(E(_st.b)<=0){return E(_su);}else{var _sv=B(_oP(B(_oN(_sr))));return new F(function(){return A3(_so,_sv,_su,new T(function(){return B(A2(_ru,_sv,_jq));}));});}},_sw=function(_sx,_sy){var _sz=B(_sb(_sx,E(_sy))),_sA=_sz.a;if(E(_sz.b)>=0){return E(_sA);}else{var _sB=B(_oP(B(_oN(_sx))));return new F(function(){return A3(_rm,_sB,_sA,new T(function(){return B(A2(_ru,_sB,_jq));}));});}},_sC=function(_sD,_sE){var _sF=B(_sb(_sD,E(_sE)));return new T2(0,_sF.a,_sF.b);},_sG=function(_sH,_sI){var _sJ=B(_sb(_sH,_sI)),_sK=_sJ.a,_sL=E(_sJ.b),_sM=new T(function(){var _sN=B(_oP(B(_oN(_sH))));if(_sL>=0){return B(A3(_so,_sN,_sK,new T(function(){return B(A2(_ru,_sN,_jq));})));}else{return B(A3(_rm,_sN,_sK,new T(function(){return B(A2(_ru,_sN,_jq));})));}}),_sO=function(_sP){var _sQ=_sP-0.5;return (_sQ>=0)?(E(_sQ)==0)?(!B(_ry(_sH,_sK)))?E(_sM):E(_sK):E(_sM):E(_sK);},_sR=E(_sL);if(!_sR){return new F(function(){return _sO(0);});}else{if(_sR<=0){var _sS= -_sR-0.5;return (_sS>=0)?(E(_sS)==0)?(!B(_ry(_sH,_sK)))?E(_sM):E(_sK):E(_sM):E(_sK);}else{return new F(function(){return _sO(_sR);});}}},_sT=function(_sU,_sV){return new F(function(){return _sG(_sU,E(_sV));});},_sW=function(_sX,_sY){return E(B(_sb(_sX,E(_sY))).a);},_sZ={_:0,a:_oM,b:_n9,c:_sC,d:_sW,e:_sT,f:_sq,g:_sw},_t0=new T1(0,1),_t1=function(_t2,_t3){var _t4=E(_t2);return new T2(0,_t4,new T(function(){var _t5=B(_t1(B(_kq(_t4,_t3)),_t3));return new T2(1,_t5.a,_t5.b);}));},_t6=function(_t7){var _t8=B(_t1(_t7,_t0));return new T2(1,_t8.a,_t8.b);},_t9=function(_ta,_tb){var _tc=B(_t1(_ta,new T(function(){return B(_lS(_tb,_ta));})));return new T2(1,_tc.a,_tc.b);},_td=new T1(0,0),_te=function(_tf,_tg){var _th=E(_tf);if(!_th._){var _ti=_th.a,_tj=E(_tg);return (_tj._==0)?_ti>=_tj.a:I_compareInt(_tj.a,_ti)<=0;}else{var _tk=_th.a,_tl=E(_tg);return (_tl._==0)?I_compareInt(_tk,_tl.a)>=0:I_compare(_tk,_tl.a)>=0;}},_tm=function(_tn,_to,_tp){if(!B(_te(_to,_td))){var _tq=function(_tr){return (!B(_l2(_tr,_tp)))?new T2(1,_tr,new T(function(){return B(_tq(B(_kq(_tr,_to))));})):__Z;};return new F(function(){return _tq(_tn);});}else{var _ts=function(_tt){return (!B(_kT(_tt,_tp)))?new T2(1,_tt,new T(function(){return B(_ts(B(_kq(_tt,_to))));})):__Z;};return new F(function(){return _ts(_tn);});}},_tu=function(_tv,_tw,_tx){return new F(function(){return _tm(_tv,B(_lS(_tw,_tv)),_tx);});},_ty=function(_tz,_tA){return new F(function(){return _tm(_tz,_t0,_tA);});},_tB=function(_tC){return new F(function(){return _kn(_tC);});},_tD=function(_tE){return new F(function(){return _lS(_tE,_t0);});},_tF=function(_tG){return new F(function(){return _kq(_tG,_t0);});},_tH=function(_tI){return new F(function(){return _nM(E(_tI));});},_tJ={_:0,a:_tF,b:_tD,c:_tH,d:_tB,e:_t6,f:_t9,g:_ty,h:_tu},_tK=function(_tL,_tM){while(1){var _tN=E(_tL);if(!_tN._){var _tO=E(_tN.a);if(_tO==(-2147483648)){_tL=new T1(1,I_fromInt(-2147483648));continue;}else{var _tP=E(_tM);if(!_tP._){return new T1(0,B(_pB(_tO,_tP.a)));}else{_tL=new T1(1,I_fromInt(_tO));_tM=_tP;continue;}}}else{var _tQ=_tN.a,_tR=E(_tM);return (_tR._==0)?new T1(1,I_div(_tQ,I_fromInt(_tR.a))):new T1(1,I_div(_tQ,_tR.a));}}},_tS=function(_tT,_tU){if(!B(_kf(_tU,_rs))){return new F(function(){return _tK(_tT,_tU);});}else{return E(_ka);}},_tV=function(_tW,_tX){while(1){var _tY=E(_tW);if(!_tY._){var _tZ=E(_tY.a);if(_tZ==(-2147483648)){_tW=new T1(1,I_fromInt(-2147483648));continue;}else{var _u0=E(_tX);if(!_u0._){var _u1=_u0.a;return new T2(0,new T1(0,B(_pB(_tZ,_u1))),new T1(0,B(_ao(_tZ,_u1))));}else{_tW=new T1(1,I_fromInt(_tZ));_tX=_u0;continue;}}}else{var _u2=E(_tX);if(!_u2._){_tW=_tY;_tX=new T1(1,I_fromInt(_u2.a));continue;}else{var _u3=I_divMod(_tY.a,_u2.a);return new T2(0,new T1(1,_u3.a),new T1(1,_u3.b));}}}},_u4=function(_u5,_u6){if(!B(_kf(_u6,_rs))){var _u7=B(_tV(_u5,_u6));return new T2(0,_u7.a,_u7.b);}else{return E(_ka);}},_u8=function(_u9,_ua){while(1){var _ub=E(_u9);if(!_ub._){var _uc=E(_ub.a);if(_uc==(-2147483648)){_u9=new T1(1,I_fromInt(-2147483648));continue;}else{var _ud=E(_ua);if(!_ud._){return new T1(0,B(_ao(_uc,_ud.a)));}else{_u9=new T1(1,I_fromInt(_uc));_ua=_ud;continue;}}}else{var _ue=_ub.a,_uf=E(_ua);return (_uf._==0)?new T1(1,I_mod(_ue,I_fromInt(_uf.a))):new T1(1,I_mod(_ue,_uf.a));}}},_ug=function(_uh,_ui){if(!B(_kf(_ui,_rs))){return new F(function(){return _u8(_uh,_ui);});}else{return E(_ka);}},_uj=function(_uk,_ul){while(1){var _um=E(_uk);if(!_um._){var _un=E(_um.a);if(_un==(-2147483648)){_uk=new T1(1,I_fromInt(-2147483648));continue;}else{var _uo=E(_ul);if(!_uo._){return new T1(0,quot(_un,_uo.a));}else{_uk=new T1(1,I_fromInt(_un));_ul=_uo;continue;}}}else{var _up=_um.a,_uq=E(_ul);return (_uq._==0)?new T1(0,I_toInt(I_quot(_up,I_fromInt(_uq.a)))):new T1(1,I_quot(_up,_uq.a));}}},_ur=function(_us,_ut){if(!B(_kf(_ut,_rs))){return new F(function(){return _uj(_us,_ut);});}else{return E(_ka);}},_uu=function(_uv,_uw){if(!B(_kf(_uw,_rs))){var _ux=B(_kz(_uv,_uw));return new T2(0,_ux.a,_ux.b);}else{return E(_ka);}},_uy=function(_uz,_uA){while(1){var _uB=E(_uz);if(!_uB._){var _uC=E(_uB.a);if(_uC==(-2147483648)){_uz=new T1(1,I_fromInt(-2147483648));continue;}else{var _uD=E(_uA);if(!_uD._){return new T1(0,_uC%_uD.a);}else{_uz=new T1(1,I_fromInt(_uC));_uA=_uD;continue;}}}else{var _uE=_uB.a,_uF=E(_uA);return (_uF._==0)?new T1(1,I_rem(_uE,I_fromInt(_uF.a))):new T1(1,I_rem(_uE,_uF.a));}}},_uG=function(_uH,_uI){if(!B(_kf(_uI,_rs))){return new F(function(){return _uy(_uH,_uI);});}else{return E(_ka);}},_uJ=function(_uK){return E(_uK);},_uL=function(_uM){return E(_uM);},_uN=function(_uO){var _uP=E(_uO);if(!_uP._){var _uQ=E(_uP.a);return (_uQ==(-2147483648))?E(_mw):(_uQ<0)?new T1(0, -_uQ):E(_uP);}else{var _uR=_uP.a;return (I_compareInt(_uR,0)>=0)?E(_uP):new T1(1,I_negate(_uR));}},_uS=new T1(0,0),_uT=new T1(0,-1),_uU=function(_uV){var _uW=E(_uV);if(!_uW._){var _uX=_uW.a;return (_uX>=0)?(E(_uX)==0)?E(_uS):E(_l1):E(_uT);}else{var _uY=I_compareInt(_uW.a,0);return (_uY<=0)?(E(_uY)==0)?E(_uS):E(_uT):E(_l1);}},_uZ={_:0,a:_kq,b:_lS,c:_qU,d:_mx,e:_uN,f:_uU,g:_uL},_v0=function(_v1,_v2){var _v3=E(_v1);if(!_v3._){var _v4=_v3.a,_v5=E(_v2);return (_v5._==0)?_v4!=_v5.a:(I_compareInt(_v5.a,_v4)==0)?false:true;}else{var _v6=_v3.a,_v7=E(_v2);return (_v7._==0)?(I_compareInt(_v6,_v7.a)==0)?false:true:(I_compare(_v6,_v7.a)==0)?false:true;}},_v8=new T2(0,_kf,_v0),_v9=function(_va,_vb){return (!B(_lD(_va,_vb)))?E(_va):E(_vb);},_vc=function(_vd,_ve){return (!B(_lD(_vd,_ve)))?E(_ve):E(_vd);},_vf={_:0,a:_v8,b:_jr,c:_l2,d:_lD,e:_kT,f:_te,g:_v9,h:_vc},_vg=function(_vh){return new T2(0,E(_vh),E(_oR));},_vi=new T3(0,_uZ,_vf,_vg),_vj={_:0,a:_vi,b:_tJ,c:_ur,d:_uG,e:_tS,f:_ug,g:_uu,h:_u4,i:_uJ},_vk=function(_vl){return E(E(_vl).a);},_vm=function(_vn){return E(E(_vn).b);},_vo=function(_vp){return E(E(_vp).b);},_vq=function(_vr){return E(E(_vr).g);},_vs=new T1(0,1),_vt=function(_vu){return E(E(_vu).d);},_vv=function(_vw,_vx,_vy){var _vz=B(_vm(_vw)),_vA=B(_vk(_vz)),_vB=new T(function(){var _vC=new T(function(){var _vD=new T(function(){var _vE=new T(function(){return B(A3(_vq,_vw,_vj,new T(function(){return B(A3(_vo,_vz,_vx,_vy));})));});return B(A2(_ru,_vA,_vE));}),_vF=new T(function(){return B(A2(_vt,_vA,new T(function(){return B(A2(_ru,_vA,_vs));})));});return B(A3(_rg,_vA,_vF,_vD));});return B(A3(_rg,_vA,_vC,_vy));});return new F(function(){return A3(_so,_vA,_vx,_vB);});},_vG=function(_vH){var _vI=new T(function(){var _vJ=E(E(_vH).b);return new T3(0,new T(function(){return B(_vv(_sZ,_vJ.a,_1s));}),new T(function(){return B(_vv(_sZ,_vJ.b,_gE));}),_vJ.c);});return new T5(0,new T(function(){return E(E(_vH).a);}),_vI,new T(function(){return E(E(_vH).c);}),new T(function(){return E(E(_vH).d);}),new T(function(){return E(E(_vH).e);}));},_vK=function(_vL,_){var _vM=B(_5x(_4W,_6f,_i1,_vL)),_vN=B(_hi(E(_vM.a),E(_vM.b),_vM.c,_vM.d,_vM,_)),_vO=new T(function(){return B(_if(E(_vN).a));}),_vP=function(_vQ){var _vR=E(_vQ);return (_vR==1)?E(new T2(1,_vO,_4)):new T2(1,_vO,new T(function(){return B(_vP(_vR-1|0));}));},_vS=B(_6g(B(_vP(5)),new T(function(){return E(E(_vN).b);}),_)),_vT=new T(function(){var _vU=new T(function(){return B(_5x(_4W,_6f,_hJ,new T(function(){return E(E(_vS).b);})));});return B(_5x(_4W,_6f,_vG,_vU));});return new T2(0,_5,_vT);},_vV=new T(function(){return eval("refresh");}),_vW=function(_vX,_){var _vY=__app0(E(_vV)),_vZ=B(A(_5x,[_4W,_2e,_5W,_vX,_])),_w0=__app0(E(_5N)),_w1=B(_vK(_vX,_));return new T(function(){return E(E(_w1).b);});},_w2=function(_w3,_w4,_w5){var _w6=function(_){var _w7=B(_vW(_w3,_));return new T(function(){return B(A1(_w5,new T1(1,_w7)));});};return new T1(0,_w6);},_w8=new T0(2),_w9=function(_wa,_wb,_wc){return function(_){var _wd=E(_wa),_we=rMV(_wd),_wf=E(_we);if(!_wf._){var _wg=new T(function(){var _wh=new T(function(){return B(A1(_wc,_5));});return B(_0(_wf.b,new T2(1,new T2(0,_wb,function(_wi){return E(_wh);}),_4)));}),_=wMV(_wd,new T2(0,_wf.a,_wg));return _w8;}else{var _wj=E(_wf.a);if(!_wj._){var _=wMV(_wd,new T2(0,_wb,_4));return new T(function(){return B(A1(_wc,_5));});}else{var _=wMV(_wd,new T1(1,_wj.b));return new T1(1,new T2(1,new T(function(){return B(A1(_wc,_5));}),new T2(1,new T(function(){return B(A2(_wj.a,_wb,_19));}),_4)));}}};},_wk=function(_wl){return E(E(_wl).b);},_wm=function(_wn,_wo,_wp){var _wq=new T(function(){return new T1(0,B(_w9(_wo,_wp,_19)));}),_wr=function(_ws){return new T1(1,new T2(1,new T(function(){return B(A1(_ws,_5));}),new T2(1,_wq,_4)));};return new F(function(){return A2(_wk,_wn,_wr);});},_wt=new T1(1,_4),_wu=function(_wv,_ww){return function(_){var _wx=E(_wv),_wy=rMV(_wx),_wz=E(_wy);if(!_wz._){var _wA=_wz.a,_wB=E(_wz.b);if(!_wB._){var _=wMV(_wx,_wt);return new T(function(){return B(A1(_ww,_wA));});}else{var _wC=E(_wB.a),_=wMV(_wx,new T2(0,_wC.a,_wB.b));return new T1(1,new T2(1,new T(function(){return B(A1(_ww,_wA));}),new T2(1,new T(function(){return B(A1(_wC.b,_19));}),_4)));}}else{var _wD=new T(function(){var _wE=function(_wF){var _wG=new T(function(){return B(A1(_ww,_wF));});return function(_wH){return E(_wG);};};return B(_0(_wz.a,new T2(1,_wE,_4)));}),_=wMV(_wx,new T1(1,_wD));return _w8;}};},_wI=function(_){return new F(function(){return __jsNull();});},_wJ=function(_wK){var _wL=B(A1(_wK,_));return E(_wL);},_wM=new T(function(){return B(_wJ(_wI));}),_wN=new T(function(){return E(_wM);}),_wO=new T(function(){return eval("window.requestAnimationFrame");}),_wP=new T1(1,_4),_wQ=function(_wR){var _wS=new T(function(){return B(_wT(_));}),_wU=new T(function(){var _wV=function(_wW){return E(_wS);},_wX=function(_){var _wY=nMV(_wP),_wZ=_wY,_x0=new T(function(){return new T1(0,B(_w9(_wZ,_5,_19)));}),_x1=function(_){var _x2=__createJSFunc(2,function(_x3,_){var _x4=B(_c(_x0,_4,_));return _wN;}),_x5=__app1(E(_wO),_x2);return new T(function(){return new T1(0,B(_wu(_wZ,_wV)));});};return new T1(0,_x1);};return B(A(_wm,[_1i,_wR,_5,function(_x6){return E(new T1(0,_wX));}]));}),_wT=function(_x7){return E(_wU);};return new F(function(){return _wT(_);});},_x8=function(_x9){return E(E(_x9).a);},_xa=function(_xb){return E(E(_xb).d);},_xc=function(_xd){return E(E(_xd).c);},_xe=function(_xf){return E(E(_xf).c);},_xg=new T1(1,_4),_xh=function(_xi){var _xj=function(_){var _xk=nMV(_xg);return new T(function(){return B(A1(_xi,_xk));});};return new T1(0,_xj);},_xl=function(_xm,_xn){var _xo=new T(function(){return B(_xe(_xm));}),_xp=B(_x8(_xm)),_xq=function(_xr){var _xs=new T(function(){return B(A1(_xo,new T(function(){return B(A1(_xn,_xr));})));});return new F(function(){return A3(_xc,_xp,_xs,new T(function(){return B(A2(_xa,_xp,_xr));}));});};return new F(function(){return A3(_10,_xp,new T(function(){return B(A2(_wk,_xm,_xh));}),_xq);});},_xt=function(_xu,_xv){return new T1(0,B(_wu(_xu,_xv)));},_xw=function(_xx,_xy,_xz){var _xA=new T(function(){return B(_x8(_xx));}),_xB=new T(function(){return B(A2(_xa,_xA,_5));}),_xC=function(_xD,_xE){var _xF=new T(function(){var _xG=new T(function(){return B(A2(_wk,_xx,function(_xH){return new F(function(){return _xt(_xE,_xH);});}));});return B(A3(_10,_xA,_xG,new T(function(){return B(A1(_xz,_xD));})));});return new F(function(){return A3(_10,_xA,_xF,function(_xI){var _xJ=E(_xI);if(!_xJ._){return E(_xB);}else{return new F(function(){return _xC(_xJ.a,_xE);});}});});};return new F(function(){return _xl(_xx,function(_xH){return new F(function(){return _xC(_xy,_xH);});});});},_xK=new T(function(){return B(A(_xw,[_1i,_1O,_w2,_wQ]));}),_xL=function(_){return new F(function(){return _c(_xK,_4,_);});},_xM=function(_){return new F(function(){return _xL(_);});};
var hasteMain = function() {B(A(_xM, [0]));};window.onload = hasteMain;