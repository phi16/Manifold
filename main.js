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

var _0=new T(function(){return eval("__strict(compile)");}),_1=function(_2){return E(E(_2).b);},_3=function(_4){return E(E(_4).a);},_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){return new F(function(){return A1(_7,_9.a);});}else{var _a=new T(function(){return B(_1(_6));}),_b=new T(function(){return B(_3(_6));}),_c=function(_d){var _e=E(_d);if(!_e._){return E(_b);}else{return new F(function(){return A2(_a,new T(function(){return B(_5(_6,_7,_e.a));}),new T(function(){return B(_c(_e.b));}));});}};return new F(function(){return _c(_9.a);});}},_f=function(_g,_h){var _i=E(_g);return (_i._==0)?E(_h):new T2(1,_i.a,new T(function(){return B(_f(_i.b,_h));}));},_j=function(_k){var _l=E(_k);if(!_l._){return __Z;}else{return new F(function(){return _f(_l.a,new T(function(){return B(_j(_l.b));},1));});}},_m=function(_n){return new F(function(){return _j(_n);});},_o=__Z,_p=new T3(0,_o,_f,_m),_q=new T(function(){return B(unCStr(","));}),_r=new T1(0,_q),_s=new T(function(){return B(unCStr("pow("));}),_t=new T1(0,_s),_u=new T(function(){return B(unCStr(")"));}),_v=new T1(0,_u),_w=new T2(1,_v,_o),_x=function(_y,_z){return new T1(1,new T2(1,_t,new T2(1,_y,new T2(1,_r,new T2(1,_z,_w)))));},_A=new T(function(){return B(unCStr("acos("));}),_B=new T1(0,_A),_C=function(_D){return new T1(1,new T2(1,_B,new T2(1,_D,_w)));},_E=new T(function(){return B(unCStr("acosh("));}),_F=new T1(0,_E),_G=function(_H){return new T1(1,new T2(1,_F,new T2(1,_H,_w)));},_I=new T(function(){return B(unCStr("asin("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_w)));},_M=new T(function(){return B(unCStr("asinh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_w)));},_Q=new T(function(){return B(unCStr("atan("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_w)));},_U=new T(function(){return B(unCStr("atanh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_w)));},_Y=new T(function(){return B(unCStr("cos("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_w)));},_12=new T(function(){return B(unCStr("cosh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_w)));},_16=new T(function(){return B(unCStr("exp("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_w)));},_1a=new T(function(){return B(unCStr("log("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_w)));},_1e=new T(function(){return B(unCStr(")/log("));}),_1f=new T1(0,_1e),_1g=function(_1h,_1i){return new T1(1,new T2(1,_1b,new T2(1,_1i,new T2(1,_1f,new T2(1,_1h,_w)))));},_1j=new T(function(){return B(unCStr("pi"));}),_1k=new T1(0,_1j),_1l=new T(function(){return B(unCStr("sin("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_w)));},_1p=new T(function(){return B(unCStr("sinh("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_w)));},_1t=new T(function(){return B(unCStr("sqrt("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_w)));},_1x=new T(function(){return B(unCStr("tan("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_w)));},_1B=new T(function(){return B(unCStr("tanh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_w)));},_1F=new T(function(){return B(unCStr("("));}),_1G=new T1(0,_1F),_1H=new T(function(){return B(unCStr(")/("));}),_1I=new T1(0,_1H),_1J=function(_1K,_1L){return new T1(1,new T2(1,_1G,new T2(1,_1K,new T2(1,_1I,new T2(1,_1L,_w)))));},_1M=new T1(0,1),_1N=function(_1O,_1P){var _1Q=E(_1O);if(!_1Q._){var _1R=_1Q.a,_1S=E(_1P);if(!_1S._){var _1T=_1S.a;return (_1R!=_1T)?(_1R>_1T)?2:0:1;}else{var _1U=I_compareInt(_1S.a,_1R);return (_1U<=0)?(_1U>=0)?1:2:0;}}else{var _1V=_1Q.a,_1W=E(_1P);if(!_1W._){var _1X=I_compareInt(_1V,_1W.a);return (_1X>=0)?(_1X<=0)?1:2:0;}else{var _1Y=I_compare(_1V,_1W.a);return (_1Y>=0)?(_1Y<=0)?1:2:0;}}},_1Z=new T(function(){return B(unCStr("base"));}),_20=new T(function(){return B(unCStr("GHC.Exception"));}),_21=new T(function(){return B(unCStr("ArithException"));}),_22=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_1Z,_20,_21),_23=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_22,_o,_o),_24=function(_25){return E(_23);},_26=function(_27){return E(E(_27).a);},_28=function(_29,_2a,_2b){var _2c=B(A1(_29,_)),_2d=B(A1(_2a,_)),_2e=hs_eqWord64(_2c.a,_2d.a);if(!_2e){return __Z;}else{var _2f=hs_eqWord64(_2c.b,_2d.b);return (!_2f)?__Z:new T1(1,_2b);}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _28(B(_26(_2i.a)),_24,_2i.b);});},_2j=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2k=new T(function(){return B(unCStr("denormal"));}),_2l=new T(function(){return B(unCStr("divide by zero"));}),_2m=new T(function(){return B(unCStr("loss of precision"));}),_2n=new T(function(){return B(unCStr("arithmetic underflow"));}),_2o=new T(function(){return B(unCStr("arithmetic overflow"));}),_2p=function(_2q,_2r){switch(E(_2q)){case 0:return new F(function(){return _f(_2o,_2r);});break;case 1:return new F(function(){return _f(_2n,_2r);});break;case 2:return new F(function(){return _f(_2m,_2r);});break;case 3:return new F(function(){return _f(_2l,_2r);});break;case 4:return new F(function(){return _f(_2k,_2r);});break;default:return new F(function(){return _f(_2j,_2r);});}},_2s=function(_2t){return new F(function(){return _2p(_2t,_o);});},_2u=function(_2v,_2w,_2x){return new F(function(){return _2p(_2w,_2x);});},_2y=44,_2z=93,_2A=91,_2B=function(_2C,_2D,_2E){var _2F=E(_2D);if(!_2F._){return new F(function(){return unAppCStr("[]",_2E);});}else{var _2G=new T(function(){var _2H=new T(function(){var _2I=function(_2J){var _2K=E(_2J);if(!_2K._){return E(new T2(1,_2z,_2E));}else{var _2L=new T(function(){return B(A2(_2C,_2K.a,new T(function(){return B(_2I(_2K.b));})));});return new T2(1,_2y,_2L);}};return B(_2I(_2F.b));});return B(A2(_2C,_2F.a,_2H));});return new T2(1,_2A,_2G);}},_2M=function(_2N,_2O){return new F(function(){return _2B(_2p,_2N,_2O);});},_2P=new T3(0,_2u,_2s,_2M),_2Q=new T(function(){return new T5(0,_24,_2P,_2R,_2g,_2s);}),_2R=function(_2S){return new T2(0,_2Q,_2S);},_2T=3,_2U=new T(function(){return B(_2R(_2T));}),_2V=new T(function(){return die(_2U);}),_2W=function(_2X,_2Y){var _2Z=E(_2X);return (_2Z._==0)?_2Z.a*Math.pow(2,_2Y):I_toNumber(_2Z.a)*Math.pow(2,_2Y);},_30=function(_31,_32){var _33=E(_31);if(!_33._){var _34=_33.a,_35=E(_32);return (_35._==0)?_34==_35.a:(I_compareInt(_35.a,_34)==0)?true:false;}else{var _36=_33.a,_37=E(_32);return (_37._==0)?(I_compareInt(_36,_37.a)==0)?true:false:(I_compare(_36,_37.a)==0)?true:false;}},_38=function(_39){var _3a=E(_39);if(!_3a._){return E(_3a.a);}else{return new F(function(){return I_toInt(_3a.a);});}},_3b=function(_3c,_3d){while(1){var _3e=E(_3c);if(!_3e._){var _3f=_3e.a,_3g=E(_3d);if(!_3g._){var _3h=_3g.a,_3i=addC(_3f,_3h);if(!E(_3i.b)){return new T1(0,_3i.a);}else{_3c=new T1(1,I_fromInt(_3f));_3d=new T1(1,I_fromInt(_3h));continue;}}else{_3c=new T1(1,I_fromInt(_3f));_3d=_3g;continue;}}else{var _3j=E(_3d);if(!_3j._){_3c=_3e;_3d=new T1(1,I_fromInt(_3j.a));continue;}else{return new T1(1,I_add(_3e.a,_3j.a));}}}},_3k=function(_3l,_3m){while(1){var _3n=E(_3l);if(!_3n._){var _3o=E(_3n.a);if(_3o==(-2147483648)){_3l=new T1(1,I_fromInt(-2147483648));continue;}else{var _3p=E(_3m);if(!_3p._){var _3q=_3p.a;return new T2(0,new T1(0,quot(_3o,_3q)),new T1(0,_3o%_3q));}else{_3l=new T1(1,I_fromInt(_3o));_3m=_3p;continue;}}}else{var _3r=E(_3m);if(!_3r._){_3l=_3n;_3m=new T1(1,I_fromInt(_3r.a));continue;}else{var _3s=I_quotRem(_3n.a,_3r.a);return new T2(0,new T1(1,_3s.a),new T1(1,_3s.b));}}}},_3t=new T1(0,0),_3u=function(_3v,_3w){while(1){var _3x=E(_3v);if(!_3x._){_3v=new T1(1,I_fromInt(_3x.a));continue;}else{return new T1(1,I_shiftLeft(_3x.a,_3w));}}},_3y=function(_3z,_3A,_3B){if(!B(_30(_3B,_3t))){var _3C=B(_3k(_3A,_3B)),_3D=_3C.a;switch(B(_1N(B(_3u(_3C.b,1)),_3B))){case 0:return new F(function(){return _2W(_3D,_3z);});break;case 1:if(!(B(_38(_3D))&1)){return new F(function(){return _2W(_3D,_3z);});}else{return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}break;default:return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}}else{return E(_2V);}},_3E=function(_3F,_3G){var _3H=E(_3F);if(!_3H._){var _3I=_3H.a,_3J=E(_3G);return (_3J._==0)?_3I>_3J.a:I_compareInt(_3J.a,_3I)<0;}else{var _3K=_3H.a,_3L=E(_3G);return (_3L._==0)?I_compareInt(_3K,_3L.a)>0:I_compare(_3K,_3L.a)>0;}},_3M=new T1(0,1),_3N=function(_3O,_3P){var _3Q=E(_3O);if(!_3Q._){var _3R=_3Q.a,_3S=E(_3P);return (_3S._==0)?_3R<_3S.a:I_compareInt(_3S.a,_3R)>0;}else{var _3T=_3Q.a,_3U=E(_3P);return (_3U._==0)?I_compareInt(_3T,_3U.a)<0:I_compare(_3T,_3U.a)<0;}},_3V=new T(function(){return B(unCStr("base"));}),_3W=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3X=new T(function(){return B(unCStr("PatternMatchFail"));}),_3Y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3V,_3W,_3X),_3Z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3Y,_o,_o),_40=function(_41){return E(_3Z);},_42=function(_43){var _44=E(_43);return new F(function(){return _28(B(_26(_44.a)),_40,_44.b);});},_45=function(_46){return E(E(_46).a);},_47=function(_48){return new T2(0,_49,_48);},_4a=function(_4b,_4c){return new F(function(){return _f(E(_4b).a,_4c);});},_4d=function(_4e,_4f){return new F(function(){return _2B(_4a,_4e,_4f);});},_4g=function(_4h,_4i,_4j){return new F(function(){return _f(E(_4i).a,_4j);});},_4k=new T3(0,_4g,_45,_4d),_49=new T(function(){return new T5(0,_40,_4k,_47,_42,_45);}),_4l=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4m=function(_4n){return E(E(_4n).c);},_4o=function(_4p,_4q){return new F(function(){return die(new T(function(){return B(A2(_4m,_4q,_4p));}));});},_4r=function(_4s,_2S){return new F(function(){return _4o(_4s,_2S);});},_4t=function(_4u,_4v){var _4w=E(_4v);if(!_4w._){return new T2(0,_o,_o);}else{var _4x=_4w.a;if(!B(A1(_4u,_4x))){return new T2(0,_o,_4w);}else{var _4y=new T(function(){var _4z=B(_4t(_4u,_4w.b));return new T2(0,_4z.a,_4z.b);});return new T2(0,new T2(1,_4x,new T(function(){return E(E(_4y).a);})),new T(function(){return E(E(_4y).b);}));}}},_4A=32,_4B=new T(function(){return B(unCStr("\n"));}),_4C=function(_4D){return (E(_4D)==124)?false:true;},_4E=function(_4F,_4G){var _4H=B(_4t(_4C,B(unCStr(_4F)))),_4I=_4H.a,_4J=function(_4K,_4L){var _4M=new T(function(){var _4N=new T(function(){return B(_f(_4G,new T(function(){return B(_f(_4L,_4B));},1)));});return B(unAppCStr(": ",_4N));},1);return new F(function(){return _f(_4K,_4M);});},_4O=E(_4H.b);if(!_4O._){return new F(function(){return _4J(_4I,_o);});}else{if(E(_4O.a)==124){return new F(function(){return _4J(_4I,new T2(1,_4A,_4O.b));});}else{return new F(function(){return _4J(_4I,_o);});}}},_4P=function(_4Q){return new F(function(){return _4r(new T1(0,new T(function(){return B(_4E(_4Q,_4l));})),_49);});},_4R=function(_4S){var _4T=function(_4U,_4V){while(1){if(!B(_3N(_4U,_4S))){if(!B(_3E(_4U,_4S))){if(!B(_30(_4U,_4S))){return new F(function(){return _4P("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_4V);}}else{return _4V-1|0;}}else{var _4W=B(_3u(_4U,1)),_4X=_4V+1|0;_4U=_4W;_4V=_4X;continue;}}};return new F(function(){return _4T(_3M,0);});},_4Y=function(_4Z){var _50=E(_4Z);if(!_50._){var _51=_50.a>>>0;if(!_51){return -1;}else{var _52=function(_53,_54){while(1){if(_53>=_51){if(_53<=_51){if(_53!=_51){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_54);}}else{return _54-1|0;}}else{var _55=imul(_53,2)>>>0,_56=_54+1|0;_53=_55;_54=_56;continue;}}};return new F(function(){return _52(1,0);});}}else{return new F(function(){return _4R(_50);});}},_57=function(_58){var _59=E(_58);if(!_59._){var _5a=_59.a>>>0;if(!_5a){return new T2(0,-1,0);}else{var _5b=function(_5c,_5d){while(1){if(_5c>=_5a){if(_5c<=_5a){if(_5c!=_5a){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5d);}}else{return _5d-1|0;}}else{var _5e=imul(_5c,2)>>>0,_5f=_5d+1|0;_5c=_5e;_5d=_5f;continue;}}};return new T2(0,B(_5b(1,0)),(_5a&_5a-1>>>0)>>>0&4294967295);}}else{var _5g=_59.a;return new T2(0,B(_4Y(_59)),I_compareInt(I_and(_5g,I_sub(_5g,I_fromInt(1))),0));}},_5h=function(_5i,_5j){var _5k=E(_5i);if(!_5k._){var _5l=_5k.a,_5m=E(_5j);return (_5m._==0)?_5l<=_5m.a:I_compareInt(_5m.a,_5l)>=0;}else{var _5n=_5k.a,_5o=E(_5j);return (_5o._==0)?I_compareInt(_5n,_5o.a)<=0:I_compare(_5n,_5o.a)<=0;}},_5p=function(_5q,_5r){while(1){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);if(!_5u._){return new T1(0,(_5t>>>0&_5u.a>>>0)>>>0&4294967295);}else{_5q=new T1(1,I_fromInt(_5t));_5r=_5u;continue;}}else{var _5v=E(_5r);if(!_5v._){_5q=_5s;_5r=new T1(1,I_fromInt(_5v.a));continue;}else{return new T1(1,I_and(_5s.a,_5v.a));}}}},_5w=function(_5x,_5y){while(1){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);if(!_5B._){var _5C=_5B.a,_5D=subC(_5A,_5C);if(!E(_5D.b)){return new T1(0,_5D.a);}else{_5x=new T1(1,I_fromInt(_5A));_5y=new T1(1,I_fromInt(_5C));continue;}}else{_5x=new T1(1,I_fromInt(_5A));_5y=_5B;continue;}}else{var _5E=E(_5y);if(!_5E._){_5x=_5z;_5y=new T1(1,I_fromInt(_5E.a));continue;}else{return new T1(1,I_sub(_5z.a,_5E.a));}}}},_5F=new T1(0,2),_5G=function(_5H,_5I){var _5J=E(_5H);if(!_5J._){var _5K=(_5J.a>>>0&(2<<_5I>>>0)-1>>>0)>>>0,_5L=1<<_5I>>>0;return (_5L<=_5K)?(_5L>=_5K)?1:2:0;}else{var _5M=B(_5p(_5J,B(_5w(B(_3u(_5F,_5I)),_3M)))),_5N=B(_3u(_3M,_5I));return (!B(_3E(_5N,_5M)))?(!B(_3N(_5N,_5M)))?1:2:0;}},_5O=function(_5P,_5Q){while(1){var _5R=E(_5P);if(!_5R._){_5P=new T1(1,I_fromInt(_5R.a));continue;}else{return new T1(1,I_shiftRight(_5R.a,_5Q));}}},_5S=function(_5T,_5U,_5V,_5W){var _5X=B(_57(_5W)),_5Y=_5X.a;if(!E(_5X.b)){var _5Z=B(_4Y(_5V));if(_5Z<((_5Y+_5T|0)-1|0)){var _60=_5Y+(_5T-_5U|0)|0;if(_60>0){if(_60>_5Z){if(_60<=(_5Z+1|0)){if(!E(B(_57(_5V)).b)){return 0;}else{return new F(function(){return _2W(_1M,_5T-_5U|0);});}}else{return 0;}}else{var _61=B(_5O(_5V,_60));switch(B(_5G(_5V,_60-1|0))){case 0:return new F(function(){return _2W(_61,_5T-_5U|0);});break;case 1:if(!(B(_38(_61))&1)){return new F(function(){return _2W(_61,_5T-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}break;default:return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}}}else{return new F(function(){return _2W(_5V,(_5T-_5U|0)-_60|0);});}}else{if(_5Z>=_5U){var _62=B(_5O(_5V,(_5Z+1|0)-_5U|0));switch(B(_5G(_5V,_5Z-_5U|0))){case 0:return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});break;case 2:return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});break;default:if(!(B(_38(_62))&1)){return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});}}}else{return new F(function(){return _2W(_5V, -_5Y);});}}}else{var _63=B(_4Y(_5V))-_5Y|0,_64=function(_65){var _66=function(_67,_68){if(!B(_5h(B(_3u(_68,_5U)),_67))){return new F(function(){return _3y(_65-_5U|0,_67,_68);});}else{return new F(function(){return _3y((_65-_5U|0)+1|0,_67,B(_3u(_68,1)));});}};if(_65>=_5U){if(_65!=_5U){return new F(function(){return _66(_5V,new T(function(){return B(_3u(_5W,_65-_5U|0));}));});}else{return new F(function(){return _66(_5V,_5W);});}}else{return new F(function(){return _66(new T(function(){return B(_3u(_5V,_5U-_65|0));}),_5W);});}};if(_5T>_63){return new F(function(){return _64(_5T);});}else{return new F(function(){return _64(_63);});}}},_69=new T1(0,2147483647),_6a=new T(function(){return B(_3b(_69,_3M));}),_6b=function(_6c){var _6d=E(_6c);if(!_6d._){var _6e=E(_6d.a);return (_6e==(-2147483648))?E(_6a):new T1(0, -_6e);}else{return new T1(1,I_negate(_6d.a));}},_6f=new T(function(){return 0/0;}),_6g=new T(function(){return -1/0;}),_6h=new T(function(){return 1/0;}),_6i=0,_6j=function(_6k,_6l){if(!B(_30(_6l,_3t))){if(!B(_30(_6k,_3t))){if(!B(_3N(_6k,_3t))){return new F(function(){return _5S(-1021,53,_6k,_6l);});}else{return  -B(_5S(-1021,53,B(_6b(_6k)),_6l));}}else{return E(_6i);}}else{return (!B(_30(_6k,_3t)))?(!B(_3N(_6k,_3t)))?E(_6h):E(_6g):E(_6f);}},_6m=function(_6n){return new T1(0,new T(function(){var _6o=E(_6n),_6p=jsShow(B(_6j(_6o.a,_6o.b)));return fromJSStr(_6p);}));},_6q=new T(function(){return B(unCStr("1./("));}),_6r=new T1(0,_6q),_6s=function(_6t){return new T1(1,new T2(1,_6r,new T2(1,_6t,_w)));},_6u=new T(function(){return B(unCStr(")+("));}),_6v=new T1(0,_6u),_6w=function(_6x,_6y){return new T1(1,new T2(1,_1G,new T2(1,_6x,new T2(1,_6v,new T2(1,_6y,_w)))));},_6z=new T(function(){return B(unCStr("-("));}),_6A=new T1(0,_6z),_6B=function(_6C){return new T1(1,new T2(1,_6A,new T2(1,_6C,_w)));},_6D=new T(function(){return B(unCStr(")*("));}),_6E=new T1(0,_6D),_6F=function(_6G,_6H){return new T1(1,new T2(1,_1G,new T2(1,_6G,new T2(1,_6E,new T2(1,_6H,_w)))));},_6I=function(_6J){return E(E(_6J).a);},_6K=function(_6L){return E(E(_6L).d);},_6M=function(_6N,_6O){return new F(function(){return A3(_6I,_6P,_6N,new T(function(){return B(A2(_6K,_6P,_6O));}));});},_6Q=new T(function(){return B(unCStr("abs("));}),_6R=new T1(0,_6Q),_6S=function(_6T){return new T1(1,new T2(1,_6R,new T2(1,_6T,_w)));},_6U=function(_6V){while(1){var _6W=E(_6V);if(!_6W._){_6V=new T1(1,I_fromInt(_6W.a));continue;}else{return new F(function(){return I_toString(_6W.a);});}}},_6X=function(_6Y,_6Z){return new F(function(){return _f(fromJSStr(B(_6U(_6Y))),_6Z);});},_70=41,_71=40,_72=new T1(0,0),_73=function(_74,_75,_76){if(_74<=6){return new F(function(){return _6X(_75,_76);});}else{if(!B(_3N(_75,_72))){return new F(function(){return _6X(_75,_76);});}else{return new T2(1,_71,new T(function(){return B(_f(fromJSStr(B(_6U(_75))),new T2(1,_70,_76)));}));}}},_77=new T(function(){return B(unCStr("."));}),_78=function(_79){return new T1(0,new T(function(){return B(_f(B(_73(0,_79,_o)),_77));}));},_7a=new T(function(){return B(unCStr("sign("));}),_7b=new T1(0,_7a),_7c=function(_7d){return new T1(1,new T2(1,_7b,new T2(1,_7d,_w)));},_6P=new T(function(){return {_:0,a:_6w,b:_6M,c:_6F,d:_6B,e:_6S,f:_7c,g:_78};}),_7e=new T4(0,_6P,_1J,_6s,_6m),_7f={_:0,a:_7e,b:_1k,c:_18,d:_1c,e:_1v,f:_x,g:_1g,h:_1n,i:_10,j:_1z,k:_K,l:_C,m:_S,n:_1r,o:_14,p:_1D,q:_O,r:_G,s:_W},_7g=new T1(0,1),_7h=function(_7i){return E(E(_7i).a);},_7j=function(_7k){return E(E(_7k).a);},_7l=function(_7m){return E(E(_7m).c);},_7n=function(_7o,_7p,_7q,_7r,_7s,_7t,_7u){var _7v=B(_7j(B(_7h(_7o)))),_7w=new T(function(){return B(A3(_6I,_7v,new T(function(){return B(A3(_7l,_7v,_7p,_7s));}),new T(function(){return B(A3(_7l,_7v,_7q,_7t));})));});return new F(function(){return A3(_6I,_7v,_7w,new T(function(){return B(A3(_7l,_7v,_7r,_7u));}));});},_7x=function(_7y){return E(E(_7y).b);},_7z=function(_7A){return E(E(_7A).g);},_7B=function(_7C){return E(E(_7C).e);},_7D=function(_7E,_7F){var _7G=B(_7j(B(_7h(_7E)))),_7H=new T(function(){return B(A2(_7B,_7E,new T(function(){var _7I=E(_7F),_7J=_7I.a,_7K=_7I.b,_7L=_7I.c;return B(_7n(_7E,_7J,_7K,_7L,_7J,_7K,_7L));})));});return new F(function(){return A3(_7x,_7G,_7H,new T(function(){return B(A2(_7z,_7G,_7g));}));});},_7M=new T(function(){return B(unCStr("x"));}),_7N=new T1(0,_7M),_7O=new T(function(){return B(unCStr("y"));}),_7P=new T1(0,_7O),_7Q=new T(function(){return B(unCStr("z"));}),_7R=new T1(0,_7Q),_7S=new T3(0,E(_7N),E(_7P),E(_7R)),_7T=new T(function(){return B(_7D(_7f,_7S));}),_7U=function(_7V){return E(_7V);},_7W=new T(function(){return toJSStr(B(_5(_p,_7U,_7T)));}),_7X=function(_7Y,_7Z,_80){var _81=new T(function(){return B(_1(_7Y));}),_82=new T(function(){return B(_3(_7Y));}),_83=function(_84){var _85=E(_84);if(!_85._){return E(_82);}else{return new F(function(){return A2(_81,new T(function(){return B(_5(_7Y,_7Z,_85.a));}),new T(function(){return B(_83(_85.b));}));});}};return new F(function(){return _83(_80);});},_86=new T(function(){return B(unCStr("(/=) is not defined"));}),_87=new T(function(){return B(err(_86));}),_88=new T(function(){return B(unCStr("(==) is not defined"));}),_89=new T(function(){return B(err(_88));}),_8a=new T2(0,_89,_87),_8b=new T(function(){return B(unCStr("(<) is not defined"));}),_8c=new T(function(){return B(err(_8b));}),_8d=new T(function(){return B(unCStr("(<=) is not defined"));}),_8e=new T(function(){return B(err(_8d));}),_8f=new T(function(){return B(unCStr("(>) is not defined"));}),_8g=new T(function(){return B(err(_8f));}),_8h=new T(function(){return B(unCStr("(>=) is not defined"));}),_8i=new T(function(){return B(err(_8h));}),_8j=new T(function(){return B(unCStr("compare is not defined"));}),_8k=new T(function(){return B(err(_8j));}),_8l=new T(function(){return B(unCStr("max("));}),_8m=new T1(0,_8l),_8n=function(_8o,_8p){return new T1(1,new T2(1,_8m,new T2(1,_8o,new T2(1,_r,new T2(1,_8p,_w)))));},_8q=new T(function(){return B(unCStr("min("));}),_8r=new T1(0,_8q),_8s=function(_8t,_8u){return new T1(1,new T2(1,_8r,new T2(1,_8t,new T2(1,_r,new T2(1,_8u,_w)))));},_8v={_:0,a:_8a,b:_8k,c:_8c,d:_8e,e:_8g,f:_8i,g:_8n,h:_8s},_8w=new T2(0,_7f,_8v),_8x=function(_8y,_8z){var _8A=E(_8y);return E(_8z);},_8B=function(_8C,_8D){var _8E=E(_8D);return E(_8C);},_8F=function(_8G,_8H){var _8I=E(_8G),_8J=E(_8H);return new T3(0,E(B(A1(_8I.a,_8J.a))),E(B(A1(_8I.b,_8J.b))),E(B(A1(_8I.c,_8J.c))));},_8K=function(_8L,_8M,_8N){return new T3(0,E(_8L),E(_8M),E(_8N));},_8O=function(_8P){return new F(function(){return _8K(_8P,_8P,_8P);});},_8Q=function(_8R,_8S){var _8T=E(_8S),_8U=E(_8R);return new T3(0,E(_8U),E(_8U),E(_8U));},_8V=function(_8W,_8X){var _8Y=E(_8X);return new T3(0,E(B(A1(_8W,_8Y.a))),E(B(A1(_8W,_8Y.b))),E(B(A1(_8W,_8Y.c))));},_8Z=new T2(0,_8V,_8Q),_90=new T5(0,_8Z,_8O,_8F,_8x,_8B),_91=new T1(0,0),_92=function(_93){var _94=B(A2(_7z,_93,_7g)),_95=B(A2(_7z,_93,_91));return new T3(0,E(new T3(0,E(_94),E(_95),E(_95))),E(new T3(0,E(_95),E(_94),E(_95))),E(new T3(0,E(_95),E(_95),E(_94))));},_96=function(_97){return E(E(_97).a);},_98=function(_99){return E(E(_99).f);},_9a=function(_9b){return E(E(_9b).b);},_9c=function(_9d){return E(E(_9d).c);},_9e=function(_9f){return E(E(_9f).a);},_9g=function(_9h){return E(E(_9h).d);},_9i=function(_9j,_9k,_9l,_9m,_9n){var _9o=new T(function(){return E(E(E(_9j).c).a);}),_9p=new T(function(){var _9q=E(_9j).a,_9r=new T(function(){var _9s=new T(function(){return B(_7h(_9o));}),_9t=new T(function(){return B(_7j(_9s));}),_9u=new T(function(){return B(A2(_9g,_9o,_9k));}),_9v=new T(function(){return B(A3(_98,_9o,_9k,_9m));}),_9w=function(_9x,_9y){var _9z=new T(function(){var _9A=new T(function(){return B(A3(_9a,_9s,new T(function(){return B(A3(_7l,_9t,_9m,_9x));}),_9k));});return B(A3(_6I,_9t,_9A,new T(function(){return B(A3(_7l,_9t,_9y,_9u));})));});return new F(function(){return A3(_7l,_9t,_9v,_9z);});};return B(A3(_9e,B(_96(_9q)),_9w,_9l));});return B(A3(_9c,_9q,_9r,_9n));});return new T2(0,new T(function(){return B(A3(_98,_9o,_9k,_9m));}),_9p);},_9B=function(_9C,_9D,_9E,_9F){var _9G=E(_9E),_9H=E(_9F),_9I=B(_9i(_9D,_9G.a,_9G.b,_9H.a,_9H.b));return new T2(0,_9I.a,_9I.b);},_9J=new T1(0,1),_9K=function(_9L){return E(E(_9L).l);},_9M=function(_9N,_9O,_9P){var _9Q=new T(function(){return E(E(E(_9N).c).a);}),_9R=new T(function(){var _9S=new T(function(){return B(_7h(_9Q));}),_9T=new T(function(){var _9U=B(_7j(_9S)),_9V=new T(function(){var _9W=new T(function(){return B(A3(_7x,_9U,new T(function(){return B(A2(_7z,_9U,_9J));}),new T(function(){return B(A3(_7l,_9U,_9O,_9O));})));});return B(A2(_7B,_9Q,_9W));});return B(A2(_6K,_9U,_9V));});return B(A3(_9e,B(_96(E(_9N).a)),function(_9X){return new F(function(){return A3(_9a,_9S,_9X,_9T);});},_9P));});return new T2(0,new T(function(){return B(A2(_9K,_9Q,_9O));}),_9R);},_9Y=function(_9Z,_a0,_a1){var _a2=E(_a1),_a3=B(_9M(_a0,_a2.a,_a2.b));return new T2(0,_a3.a,_a3.b);},_a4=function(_a5){return E(E(_a5).r);},_a6=function(_a7,_a8,_a9){var _aa=new T(function(){return E(E(E(_a7).c).a);}),_ab=new T(function(){var _ac=new T(function(){return B(_7h(_aa));}),_ad=new T(function(){var _ae=new T(function(){var _af=B(_7j(_ac));return B(A3(_7x,_af,new T(function(){return B(A3(_7l,_af,_a8,_a8));}),new T(function(){return B(A2(_7z,_af,_9J));})));});return B(A2(_7B,_aa,_ae));});return B(A3(_9e,B(_96(E(_a7).a)),function(_ag){return new F(function(){return A3(_9a,_ac,_ag,_ad);});},_a9));});return new T2(0,new T(function(){return B(A2(_a4,_aa,_a8));}),_ab);},_ah=function(_ai,_aj,_ak){var _al=E(_ak),_am=B(_a6(_aj,_al.a,_al.b));return new T2(0,_am.a,_am.b);},_an=function(_ao){return E(E(_ao).k);},_ap=function(_aq,_ar,_as){var _at=new T(function(){return E(E(E(_aq).c).a);}),_au=new T(function(){var _av=new T(function(){return B(_7h(_at));}),_aw=new T(function(){var _ax=new T(function(){var _ay=B(_7j(_av));return B(A3(_7x,_ay,new T(function(){return B(A2(_7z,_ay,_9J));}),new T(function(){return B(A3(_7l,_ay,_ar,_ar));})));});return B(A2(_7B,_at,_ax));});return B(A3(_9e,B(_96(E(_aq).a)),function(_az){return new F(function(){return A3(_9a,_av,_az,_aw);});},_as));});return new T2(0,new T(function(){return B(A2(_an,_at,_ar));}),_au);},_aA=function(_aB,_aC,_aD){var _aE=E(_aD),_aF=B(_ap(_aC,_aE.a,_aE.b));return new T2(0,_aF.a,_aF.b);},_aG=function(_aH){return E(E(_aH).q);},_aI=function(_aJ,_aK,_aL){var _aM=new T(function(){return E(E(E(_aJ).c).a);}),_aN=new T(function(){var _aO=new T(function(){return B(_7h(_aM));}),_aP=new T(function(){var _aQ=new T(function(){var _aR=B(_7j(_aO));return B(A3(_6I,_aR,new T(function(){return B(A3(_7l,_aR,_aK,_aK));}),new T(function(){return B(A2(_7z,_aR,_9J));})));});return B(A2(_7B,_aM,_aQ));});return B(A3(_9e,B(_96(E(_aJ).a)),function(_aS){return new F(function(){return A3(_9a,_aO,_aS,_aP);});},_aL));});return new T2(0,new T(function(){return B(A2(_aG,_aM,_aK));}),_aN);},_aT=function(_aU,_aV,_aW){var _aX=E(_aW),_aY=B(_aI(_aV,_aX.a,_aX.b));return new T2(0,_aY.a,_aY.b);},_aZ=function(_b0){return E(E(_b0).m);},_b1=function(_b2,_b3,_b4){var _b5=new T(function(){return E(E(E(_b2).c).a);}),_b6=new T(function(){var _b7=new T(function(){return B(_7h(_b5));}),_b8=new T(function(){var _b9=B(_7j(_b7));return B(A3(_6I,_b9,new T(function(){return B(A2(_7z,_b9,_9J));}),new T(function(){return B(A3(_7l,_b9,_b3,_b3));})));});return B(A3(_9e,B(_96(E(_b2).a)),function(_ba){return new F(function(){return A3(_9a,_b7,_ba,_b8);});},_b4));});return new T2(0,new T(function(){return B(A2(_aZ,_b5,_b3));}),_b6);},_bb=function(_bc,_bd,_be){var _bf=E(_be),_bg=B(_b1(_bd,_bf.a,_bf.b));return new T2(0,_bg.a,_bg.b);},_bh=function(_bi){return E(E(_bi).s);},_bj=function(_bk,_bl,_bm){var _bn=new T(function(){return E(E(E(_bk).c).a);}),_bo=new T(function(){var _bp=new T(function(){return B(_7h(_bn));}),_bq=new T(function(){var _br=B(_7j(_bp));return B(A3(_7x,_br,new T(function(){return B(A2(_7z,_br,_9J));}),new T(function(){return B(A3(_7l,_br,_bl,_bl));})));});return B(A3(_9e,B(_96(E(_bk).a)),function(_bs){return new F(function(){return A3(_9a,_bp,_bs,_bq);});},_bm));});return new T2(0,new T(function(){return B(A2(_bh,_bn,_bl));}),_bo);},_bt=function(_bu,_bv,_bw){var _bx=E(_bw),_by=B(_bj(_bv,_bx.a,_bx.b));return new T2(0,_by.a,_by.b);},_bz=function(_bA){return E(E(_bA).i);},_bB=function(_bC){return E(E(_bC).h);},_bD=function(_bE,_bF,_bG){var _bH=new T(function(){return E(E(E(_bE).c).a);}),_bI=new T(function(){var _bJ=new T(function(){return B(_7j(new T(function(){return B(_7h(_bH));})));}),_bK=new T(function(){return B(A2(_6K,_bJ,new T(function(){return B(A2(_bB,_bH,_bF));})));});return B(A3(_9e,B(_96(E(_bE).a)),function(_bL){return new F(function(){return A3(_7l,_bJ,_bL,_bK);});},_bG));});return new T2(0,new T(function(){return B(A2(_bz,_bH,_bF));}),_bI);},_bM=function(_bN,_bO,_bP){var _bQ=E(_bP),_bR=B(_bD(_bO,_bQ.a,_bQ.b));return new T2(0,_bR.a,_bR.b);},_bS=function(_bT){return E(E(_bT).o);},_bU=function(_bV){return E(E(_bV).n);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_7j(new T(function(){return B(_7h(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_9e,B(_96(E(_bX).a)),function(_c4){return new F(function(){return A3(_7l,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bS,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc){return E(E(_cc).c);},_cd=function(_ce,_cf,_cg){var _ch=new T(function(){return E(E(E(_ce).c).a);}),_ci=new T(function(){var _cj=new T(function(){return B(_7j(new T(function(){return B(_7h(_ch));})));}),_ck=new T(function(){return B(A2(_cb,_ch,_cf));});return B(A3(_9e,B(_96(E(_ce).a)),function(_cl){return new F(function(){return A3(_7l,_cj,_cl,_ck);});},_cg));});return new T2(0,new T(function(){return B(A2(_cb,_ch,_cf));}),_ci);},_cm=function(_cn,_co,_cp){var _cq=E(_cp),_cr=B(_cd(_co,_cq.a,_cq.b));return new T2(0,_cr.a,_cr.b);},_cs=function(_ct,_cu,_cv){var _cw=new T(function(){return E(E(E(_ct).c).a);}),_cx=new T(function(){var _cy=new T(function(){return B(_7h(_cw));}),_cz=new T(function(){return B(_7j(_cy));}),_cA=new T(function(){return B(A3(_9a,_cy,new T(function(){return B(A2(_7z,_cz,_9J));}),_cu));});return B(A3(_9e,B(_96(E(_ct).a)),function(_cB){return new F(function(){return A3(_7l,_cz,_cB,_cA);});},_cv));});return new T2(0,new T(function(){return B(A2(_9g,_cw,_cu));}),_cx);},_cC=function(_cD,_cE,_cF){var _cG=E(_cF),_cH=B(_cs(_cE,_cG.a,_cG.b));return new T2(0,_cH.a,_cH.b);},_cI=function(_cJ,_cK,_cL,_cM){var _cN=new T(function(){return E(E(_cK).c);}),_cO=new T3(0,new T(function(){return E(E(_cK).a);}),new T(function(){return E(E(_cK).b);}),new T2(0,new T(function(){return E(E(_cN).a);}),new T(function(){return E(E(_cN).b);})));return new F(function(){return A3(_9a,_cJ,new T(function(){var _cP=E(_cM),_cQ=B(_cs(_cO,_cP.a,_cP.b));return new T2(0,_cQ.a,_cQ.b);}),new T(function(){var _cR=E(_cL),_cS=B(_cs(_cO,_cR.a,_cR.b));return new T2(0,_cS.a,_cS.b);}));});},_cT=new T1(0,0),_cU=function(_cV){return E(E(_cV).b);},_cW=function(_cX){return E(E(_cX).b);},_cY=function(_cZ){var _d0=new T(function(){return E(E(E(_cZ).c).a);}),_d1=new T(function(){return B(A2(_cW,E(_cZ).a,new T(function(){return B(A2(_7z,B(_7j(B(_7h(_d0)))),_cT));})));});return new T2(0,new T(function(){return B(_cU(_d0));}),_d1);},_d2=function(_d3,_d4){var _d5=B(_cY(_d4));return new T2(0,_d5.a,_d5.b);},_d6=function(_d7,_d8,_d9){var _da=new T(function(){return E(E(E(_d7).c).a);}),_db=new T(function(){var _dc=new T(function(){return B(_7j(new T(function(){return B(_7h(_da));})));}),_dd=new T(function(){return B(A2(_bz,_da,_d8));});return B(A3(_9e,B(_96(E(_d7).a)),function(_de){return new F(function(){return A3(_7l,_dc,_de,_dd);});},_d9));});return new T2(0,new T(function(){return B(A2(_bB,_da,_d8));}),_db);},_df=function(_dg,_dh,_di){var _dj=E(_di),_dk=B(_d6(_dh,_dj.a,_dj.b));return new T2(0,_dk.a,_dk.b);},_dl=function(_dm,_dn,_do){var _dp=new T(function(){return E(E(E(_dm).c).a);}),_dq=new T(function(){var _dr=new T(function(){return B(_7j(new T(function(){return B(_7h(_dp));})));}),_ds=new T(function(){return B(A2(_bS,_dp,_dn));});return B(A3(_9e,B(_96(E(_dm).a)),function(_dt){return new F(function(){return A3(_7l,_dr,_dt,_ds);});},_do));});return new T2(0,new T(function(){return B(A2(_bU,_dp,_dn));}),_dq);},_du=function(_dv,_dw,_dx){var _dy=E(_dx),_dz=B(_dl(_dw,_dy.a,_dy.b));return new T2(0,_dz.a,_dz.b);},_dA=new T1(0,2),_dB=function(_dC,_dD,_dE){var _dF=new T(function(){return E(E(E(_dC).c).a);}),_dG=new T(function(){var _dH=new T(function(){return B(_7h(_dF));}),_dI=new T(function(){return B(_7j(_dH));}),_dJ=new T(function(){var _dK=new T(function(){return B(A3(_9a,_dH,new T(function(){return B(A2(_7z,_dI,_9J));}),new T(function(){return B(A2(_7z,_dI,_dA));})));});return B(A3(_9a,_dH,_dK,new T(function(){return B(A2(_7B,_dF,_dD));})));});return B(A3(_9e,B(_96(E(_dC).a)),function(_dL){return new F(function(){return A3(_7l,_dI,_dL,_dJ);});},_dE));});return new T2(0,new T(function(){return B(A2(_7B,_dF,_dD));}),_dG);},_dM=function(_dN,_dO,_dP){var _dQ=E(_dP),_dR=B(_dB(_dO,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);},_dS=function(_dT){return E(E(_dT).j);},_dU=function(_dV,_dW,_dX){var _dY=new T(function(){return E(E(E(_dV).c).a);}),_dZ=new T(function(){var _e0=new T(function(){return B(_7h(_dY));}),_e1=new T(function(){var _e2=new T(function(){return B(A2(_bz,_dY,_dW));});return B(A3(_7l,B(_7j(_e0)),_e2,_e2));});return B(A3(_9e,B(_96(E(_dV).a)),function(_e3){return new F(function(){return A3(_9a,_e0,_e3,_e1);});},_dX));});return new T2(0,new T(function(){return B(A2(_dS,_dY,_dW));}),_dZ);},_e4=function(_e5,_e6,_e7){var _e8=E(_e7),_e9=B(_dU(_e6,_e8.a,_e8.b));return new T2(0,_e9.a,_e9.b);},_ea=function(_eb){return E(E(_eb).p);},_ec=function(_ed,_ee,_ef){var _eg=new T(function(){return E(E(E(_ed).c).a);}),_eh=new T(function(){var _ei=new T(function(){return B(_7h(_eg));}),_ej=new T(function(){var _ek=new T(function(){return B(A2(_bS,_eg,_ee));});return B(A3(_7l,B(_7j(_ei)),_ek,_ek));});return B(A3(_9e,B(_96(E(_ed).a)),function(_el){return new F(function(){return A3(_9a,_ei,_el,_ej);});},_ef));});return new T2(0,new T(function(){return B(A2(_ea,_eg,_ee));}),_eh);},_em=function(_en,_eo,_ep){var _eq=E(_ep),_er=B(_ec(_eo,_eq.a,_eq.b));return new T2(0,_er.a,_er.b);},_es=function(_et,_eu){return {_:0,a:_et,b:new T(function(){return B(_d2(_et,_eu));}),c:function(_ev){return new F(function(){return _cm(_et,_eu,_ev);});},d:function(_ev){return new F(function(){return _cC(_et,_eu,_ev);});},e:function(_ev){return new F(function(){return _dM(_et,_eu,_ev);});},f:function(_ew,_ev){return new F(function(){return _9B(_et,_eu,_ew,_ev);});},g:function(_ew,_ev){return new F(function(){return _cI(_et,_eu,_ew,_ev);});},h:function(_ev){return new F(function(){return _df(_et,_eu,_ev);});},i:function(_ev){return new F(function(){return _bM(_et,_eu,_ev);});},j:function(_ev){return new F(function(){return _e4(_et,_eu,_ev);});},k:function(_ev){return new F(function(){return _aA(_et,_eu,_ev);});},l:function(_ev){return new F(function(){return _9Y(_et,_eu,_ev);});},m:function(_ev){return new F(function(){return _bb(_et,_eu,_ev);});},n:function(_ev){return new F(function(){return _du(_et,_eu,_ev);});},o:function(_ev){return new F(function(){return _c5(_et,_eu,_ev);});},p:function(_ev){return new F(function(){return _em(_et,_eu,_ev);});},q:function(_ev){return new F(function(){return _aT(_et,_eu,_ev);});},r:function(_ev){return new F(function(){return _ah(_et,_eu,_ev);});},s:function(_ev){return new F(function(){return _bt(_et,_eu,_ev);});}};},_ex=function(_ey,_ez,_eA,_eB,_eC){var _eD=new T(function(){return B(_7h(new T(function(){return E(E(E(_ey).c).a);})));}),_eE=new T(function(){var _eF=E(_ey).a,_eG=new T(function(){var _eH=new T(function(){return B(_7j(_eD));}),_eI=new T(function(){return B(A3(_7l,_eH,_eB,_eB));}),_eJ=function(_eK,_eL){var _eM=new T(function(){return B(A3(_7x,_eH,new T(function(){return B(A3(_7l,_eH,_eK,_eB));}),new T(function(){return B(A3(_7l,_eH,_ez,_eL));})));});return new F(function(){return A3(_9a,_eD,_eM,_eI);});};return B(A3(_9e,B(_96(_eF)),_eJ,_eA));});return B(A3(_9c,_eF,_eG,_eC));});return new T2(0,new T(function(){return B(A3(_9a,_eD,_ez,_eB));}),_eE);},_eN=function(_eO,_eP,_eQ,_eR){var _eS=E(_eQ),_eT=E(_eR),_eU=B(_ex(_eP,_eS.a,_eS.b,_eT.a,_eT.b));return new T2(0,_eU.a,_eU.b);},_eV=function(_eW){return E(E(_eW).d);},_eX=function(_eY,_eZ){var _f0=new T(function(){return B(_7h(new T(function(){return E(E(E(_eY).c).a);})));}),_f1=new T(function(){return B(A2(_cW,E(_eY).a,new T(function(){return B(A2(_7z,B(_7j(_f0)),_cT));})));});return new T2(0,new T(function(){return B(A2(_eV,_f0,_eZ));}),_f1);},_f2=function(_f3,_f4,_f5){var _f6=B(_eX(_f4,_f5));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9,_fa){var _fb=new T(function(){return B(_7h(new T(function(){return E(E(E(_f8).c).a);})));}),_fc=new T(function(){return B(_7j(_fb));}),_fd=new T(function(){var _fe=new T(function(){var _ff=new T(function(){return B(A3(_9a,_fb,new T(function(){return B(A2(_7z,_fc,_9J));}),new T(function(){return B(A3(_7l,_fc,_f9,_f9));})));});return B(A2(_6K,_fc,_ff));});return B(A3(_9e,B(_96(E(_f8).a)),function(_fg){return new F(function(){return A3(_7l,_fc,_fg,_fe);});},_fa));}),_fh=new T(function(){return B(A3(_9a,_fb,new T(function(){return B(A2(_7z,_fc,_9J));}),_f9));});return new T2(0,_fh,_fd);},_fi=function(_fj,_fk,_fl){var _fm=E(_fl),_fn=B(_f7(_fk,_fm.a,_fm.b));return new T2(0,_fn.a,_fn.b);},_fo=function(_fp,_fq){return new T4(0,_fp,function(_ew,_ev){return new F(function(){return _eN(_fp,_fq,_ew,_ev);});},function(_ev){return new F(function(){return _fi(_fp,_fq,_ev);});},function(_ev){return new F(function(){return _f2(_fp,_fq,_ev);});});},_fr=function(_fs,_ft,_fu,_fv,_fw){var _fx=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_fs).c).a);})));})));}),_fy=new T(function(){var _fz=E(_fs).a,_fA=new T(function(){var _fB=function(_fC,_fD){return new F(function(){return A3(_6I,_fx,new T(function(){return B(A3(_7l,_fx,_ft,_fD));}),new T(function(){return B(A3(_7l,_fx,_fC,_fv));}));});};return B(A3(_9e,B(_96(_fz)),_fB,_fu));});return B(A3(_9c,_fz,_fA,_fw));});return new T2(0,new T(function(){return B(A3(_7l,_fx,_ft,_fv));}),_fy);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fr(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO,_fP,_fQ){var _fR=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_fM).c).a);})));})));}),_fS=new T(function(){var _fT=E(_fM).a,_fU=new T(function(){return B(A3(_9e,B(_96(_fT)),new T(function(){return B(_6I(_fR));}),_fO));});return B(A3(_9c,_fT,_fU,_fQ));});return new T2(0,new T(function(){return B(A3(_6I,_fR,_fN,_fP));}),_fS);},_fV=function(_fW,_fX,_fY){var _fZ=E(_fX),_g0=E(_fY),_g1=B(_fL(_fW,_fZ.a,_fZ.b,_g0.a,_g0.b));return new T2(0,_g1.a,_g1.b);},_g2=function(_g3,_g4,_g5){var _g6=B(_g7(_g3));return new F(function(){return A3(_6I,_g6,_g4,new T(function(){return B(A2(_6K,_g6,_g5));}));});},_g8=function(_g9){return E(E(_g9).e);},_ga=function(_gb){return E(E(_gb).f);},_gc=function(_gd,_ge,_gf){var _gg=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gd).c).a);})));})));}),_gh=new T(function(){var _gi=new T(function(){return B(A2(_ga,_gg,_ge));});return B(A3(_9e,B(_96(E(_gd).a)),function(_gj){return new F(function(){return A3(_7l,_gg,_gj,_gi);});},_gf));});return new T2(0,new T(function(){return B(A2(_g8,_gg,_ge));}),_gh);},_gk=function(_gl,_gm){var _gn=E(_gm),_go=B(_gc(_gl,_gn.a,_gn.b));return new T2(0,_go.a,_go.b);},_gp=function(_gq,_gr){var _gs=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gq).c).a);})));})));}),_gt=new T(function(){return B(A2(_cW,E(_gq).a,new T(function(){return B(A2(_7z,_gs,_cT));})));});return new T2(0,new T(function(){return B(A2(_7z,_gs,_gr));}),_gt);},_gu=function(_gv,_gw){var _gx=B(_gp(_gv,_gw));return new T2(0,_gx.a,_gx.b);},_gy=function(_gz,_gA,_gB){var _gC=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gz).c).a);})));})));}),_gD=new T(function(){return B(A3(_9e,B(_96(E(_gz).a)),new T(function(){return B(_6K(_gC));}),_gB));});return new T2(0,new T(function(){return B(A2(_6K,_gC,_gA));}),_gD);},_gE=function(_gF,_gG){var _gH=E(_gG),_gI=B(_gy(_gF,_gH.a,_gH.b));return new T2(0,_gI.a,_gI.b);},_gJ=function(_gK,_gL){var _gM=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gK).c).a);})));})));}),_gN=new T(function(){return B(A2(_cW,E(_gK).a,new T(function(){return B(A2(_7z,_gM,_cT));})));});return new T2(0,new T(function(){return B(A2(_ga,_gM,_gL));}),_gN);},_gO=function(_gP,_gQ){var _gR=B(_gJ(_gP,E(_gQ).a));return new T2(0,_gR.a,_gR.b);},_g7=function(_gS){return {_:0,a:function(_ew,_ev){return new F(function(){return _fV(_gS,_ew,_ev);});},b:function(_ew,_ev){return new F(function(){return _g2(_gS,_ew,_ev);});},c:function(_ew,_ev){return new F(function(){return _fE(_gS,_ew,_ev);});},d:function(_ev){return new F(function(){return _gE(_gS,_ev);});},e:function(_ev){return new F(function(){return _gk(_gS,_ev);});},f:function(_ev){return new F(function(){return _gO(_gS,_ev);});},g:function(_ev){return new F(function(){return _gu(_gS,_ev);});}};},_gT=function(_gU){var _gV=new T(function(){return E(E(_gU).a);}),_gW=new T3(0,_90,_92,new T2(0,_gV,new T(function(){return E(E(_gU).b);}))),_gX=new T(function(){return B(_es(new T(function(){return B(_fo(new T(function(){return B(_g7(_gW));}),_gW));}),_gW));}),_gY=new T(function(){return B(_7j(new T(function(){return B(_7h(_gV));})));}),_gZ=function(_h0){return E(B(_7D(_gX,new T(function(){var _h1=E(_h0),_h2=B(A2(_7z,_gY,_7g)),_h3=B(A2(_7z,_gY,_91));return new T3(0,E(new T2(0,_h1.a,new T3(0,E(_h2),E(_h3),E(_h3)))),E(new T2(0,_h1.b,new T3(0,E(_h3),E(_h2),E(_h3)))),E(new T2(0,_h1.c,new T3(0,E(_h3),E(_h3),E(_h2)))));}))).b);};return E(_gZ);},_h4=new T(function(){return B(_gT(_8w));}),_h5=function(_h6,_h7){var _h8=E(_h7);return (_h8._==0)?__Z:new T2(1,_h6,new T2(1,_h8.a,new T(function(){return B(_h5(_h6,_h8.b));})));},_h9=new T(function(){var _ha=B(A1(_h4,_7S));return new T2(1,_ha.a,new T(function(){return B(_h5(_r,new T2(1,_ha.b,new T2(1,_ha.c,_o))));}));}),_hb=new T1(1,_h9),_hc=new T2(1,_hb,_w),_hd=new T(function(){return B(unCStr("vec3("));}),_he=new T1(0,_hd),_hf=new T2(1,_he,_hc),_hg=new T(function(){return toJSStr(B(_7X(_p,_7U,_hf)));}),_hh=function(_hi,_hj){while(1){var _hk=E(_hi);if(!_hk._){return E(_hj);}else{var _hl=_hj+1|0;_hi=_hk.b;_hj=_hl;continue;}}},_hm=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_hn=new T(function(){return B(err(_hm));}),_ho=0,_hp=new T3(0,E(_ho),E(_ho),E(_ho)),_hq=new T2(0,E(_hp),E(_ho)),_hr=new T(function(){return B(unCStr("Negative exponent"));}),_hs=new T(function(){return B(err(_hr));}),_ht=function(_hu,_hv,_hw){while(1){if(!(_hv%2)){var _hx=_hu*_hu,_hy=quot(_hv,2);_hu=_hx;_hv=_hy;continue;}else{var _hz=E(_hv);if(_hz==1){return _hu*_hw;}else{var _hx=_hu*_hu,_hA=_hu*_hw;_hu=_hx;_hv=quot(_hz-1|0,2);_hw=_hA;continue;}}}},_hB=function(_hC,_hD){while(1){if(!(_hD%2)){var _hE=_hC*_hC,_hF=quot(_hD,2);_hC=_hE;_hD=_hF;continue;}else{var _hG=E(_hD);if(_hG==1){return E(_hC);}else{return new F(function(){return _ht(_hC*_hC,quot(_hG-1|0,2),_hC);});}}}},_hH=function(_hI){var _hJ=E(_hI);return new F(function(){return Math.log(_hJ+(_hJ+1)*Math.sqrt((_hJ-1)/(_hJ+1)));});},_hK=function(_hL){var _hM=E(_hL);return new F(function(){return Math.log(_hM+Math.sqrt(1+_hM*_hM));});},_hN=function(_hO){var _hP=E(_hO);return 0.5*Math.log((1+_hP)/(1-_hP));},_hQ=function(_hR,_hS){return Math.log(E(_hS))/Math.log(E(_hR));},_hT=3.141592653589793,_hU=function(_hV){var _hW=E(_hV);return new F(function(){return _6j(_hW.a,_hW.b);});},_hX=function(_hY){return 1/E(_hY);},_hZ=function(_i0){var _i1=E(_i0),_i2=E(_i1);return (_i2==0)?E(_6i):(_i2<=0)? -_i2:E(_i1);},_i3=function(_i4){var _i5=E(_i4);if(!_i5._){return _i5.a;}else{return new F(function(){return I_toNumber(_i5.a);});}},_i6=function(_i7){return new F(function(){return _i3(_i7);});},_i8=1,_i9=-1,_ia=function(_ib){var _ic=E(_ib);return (_ic<=0)?(_ic>=0)?E(_ic):E(_i9):E(_i8);},_id=function(_ie,_if){return E(_ie)-E(_if);},_ig=function(_ih){return  -E(_ih);},_ii=function(_ij,_ik){return E(_ij)+E(_ik);},_il=function(_im,_in){return E(_im)*E(_in);},_io={_:0,a:_ii,b:_id,c:_il,d:_ig,e:_hZ,f:_ia,g:_i6},_ip=function(_iq,_ir){return E(_iq)/E(_ir);},_is=new T4(0,_io,_ip,_hX,_hU),_it=function(_iu){return new F(function(){return Math.acos(E(_iu));});},_iv=function(_iw){return new F(function(){return Math.asin(E(_iw));});},_ix=function(_iy){return new F(function(){return Math.atan(E(_iy));});},_iz=function(_iA){return new F(function(){return Math.cos(E(_iA));});},_iB=function(_iC){return new F(function(){return cosh(E(_iC));});},_iD=function(_iE){return new F(function(){return Math.exp(E(_iE));});},_iF=function(_iG){return new F(function(){return Math.log(E(_iG));});},_iH=function(_iI,_iJ){return new F(function(){return Math.pow(E(_iI),E(_iJ));});},_iK=function(_iL){return new F(function(){return Math.sin(E(_iL));});},_iM=function(_iN){return new F(function(){return sinh(E(_iN));});},_iO=function(_iP){return new F(function(){return Math.sqrt(E(_iP));});},_iQ=function(_iR){return new F(function(){return Math.tan(E(_iR));});},_iS=function(_iT){return new F(function(){return tanh(E(_iT));});},_iU={_:0,a:_is,b:_hT,c:_iD,d:_iF,e:_iO,f:_iH,g:_hQ,h:_iK,i:_iz,j:_iQ,k:_iv,l:_it,m:_ix,n:_iM,o:_iB,p:_iS,q:_hK,r:_hH,s:_hN},_iV=function(_iW,_iX){return (E(_iW)!=E(_iX))?true:false;},_iY=function(_iZ,_j0){return E(_iZ)==E(_j0);},_j1=new T2(0,_iY,_iV),_j2=function(_j3,_j4){return E(_j3)<E(_j4);},_j5=function(_j6,_j7){return E(_j6)<=E(_j7);},_j8=function(_j9,_ja){return E(_j9)>E(_ja);},_jb=function(_jc,_jd){return E(_jc)>=E(_jd);},_je=function(_jf,_jg){var _jh=E(_jf),_ji=E(_jg);return (_jh>=_ji)?(_jh!=_ji)?2:1:0;},_jj=function(_jk,_jl){var _jm=E(_jk),_jn=E(_jl);return (_jm>_jn)?E(_jm):E(_jn);},_jo=function(_jp,_jq){var _jr=E(_jp),_js=E(_jq);return (_jr>_js)?E(_js):E(_jr);},_jt={_:0,a:_j1,b:_je,c:_j2,d:_j5,e:_j8,f:_jb,g:_jj,h:_jo},_ju="dz",_jv="wy",_jw="wx",_jx="dy",_jy="dx",_jz="t",_jA="a",_jB="r",_jC="ly",_jD="lx",_jE="wz",_jF=0,_jG=function(_jH){var _jI=__new(),_jJ=_jI,_jK=function(_jL,_){while(1){var _jM=E(_jL);if(!_jM._){return _jF;}else{var _jN=E(_jM.a),_jO=__set(_jJ,E(_jN.a),E(_jN.b));_jL=_jM.b;continue;}}},_jP=B(_jK(_jH,_));return E(_jJ);},_jQ=function(_jR,_jS,_jT,_jU,_jV,_jW,_jX,_jY,_jZ){return new F(function(){return _jG(new T2(1,new T2(0,_jw,_jR),new T2(1,new T2(0,_jv,_jS),new T2(1,new T2(0,_jE,_jT),new T2(1,new T2(0,_jD,_jU*_jV*Math.cos(_jW)),new T2(1,new T2(0,_jC,_jU*_jV*Math.sin(_jW)),new T2(1,new T2(0,_jB,_jU),new T2(1,new T2(0,_jA,_jV),new T2(1,new T2(0,_jz,_jW),new T2(1,new T2(0,_jy,_jX),new T2(1,new T2(0,_jx,_jY),new T2(1,new T2(0,_ju,_jZ),_o))))))))))));});},_k0=function(_k1){var _k2=E(_k1),_k3=E(_k2.a),_k4=E(_k2.b),_k5=E(_k2.d);return new F(function(){return _jQ(_k3.a,_k3.b,_k3.c,E(_k4.a),E(_k4.b),E(_k2.c),_k5.a,_k5.b,_k5.c);});},_k6=function(_k7,_k8){var _k9=E(_k8);return (_k9._==0)?__Z:new T2(1,new T(function(){return B(A1(_k7,_k9.a));}),new T(function(){return B(_k6(_k7,_k9.b));}));},_ka=function(_kb,_kc,_kd){var _ke=__lst2arr(B(_k6(_k0,new T2(1,_kb,new T2(1,_kc,new T2(1,_kd,_o))))));return E(_ke);},_kf=function(_kg){var _kh=E(_kg);return new F(function(){return _ka(_kh.a,_kh.b,_kh.c);});},_ki=new T2(0,_iU,_jt),_kj=function(_kk,_kl,_km,_kn){var _ko=B(_7h(_kk)),_kp=new T(function(){return B(A2(_7B,_kk,new T(function(){return B(_7n(_kk,_kl,_km,_kn,_kl,_km,_kn));})));});return new T3(0,B(A3(_9a,_ko,_kl,_kp)),B(A3(_9a,_ko,_km,_kp)),B(A3(_9a,_ko,_kn,_kp)));},_kq=function(_kr,_ks,_kt,_ku,_kv,_kw,_kx){var _ky=B(_7l(_kr));return new T3(0,B(A1(B(A1(_ky,_ks)),_kv)),B(A1(B(A1(_ky,_kt)),_kw)),B(A1(B(A1(_ky,_ku)),_kx)));},_kz=function(_kA,_kB,_kC,_kD,_kE,_kF,_kG){var _kH=B(_6I(_kA));return new T3(0,B(A1(B(A1(_kH,_kB)),_kE)),B(A1(B(A1(_kH,_kC)),_kF)),B(A1(B(A1(_kH,_kD)),_kG)));},_kI=function(_kJ,_kK){var _kL=new T(function(){return E(E(_kJ).a);}),_kM=new T(function(){return B(A2(_gT,new T2(0,_kL,new T(function(){return E(E(_kJ).b);})),_kK));}),_kN=new T(function(){var _kO=E(_kM),_kP=B(_kj(_kL,_kO.a,_kO.b,_kO.c));return new T3(0,E(_kP.a),E(_kP.b),E(_kP.c));}),_kQ=new T(function(){var _kR=E(_kK),_kS=E(_kN),_kT=B(_7h(_kL)),_kU=new T(function(){return B(A2(_7B,_kL,new T(function(){var _kV=E(_kM),_kW=_kV.a,_kX=_kV.b,_kY=_kV.c;return B(_7n(_kL,_kW,_kX,_kY,_kW,_kX,_kY));})));}),_kZ=B(A3(_9a,_kT,new T(function(){return B(_7D(_kL,_kR));}),_kU)),_l0=B(_7j(_kT)),_l1=B(_kq(_l0,_kS.a,_kS.b,_kS.c,_kZ,_kZ,_kZ)),_l2=B(_6K(_l0)),_l3=B(_kz(_l0,_kR.a,_kR.b,_kR.c,B(A1(_l2,_l1.a)),B(A1(_l2,_l1.b)),B(A1(_l2,_l1.c))));return new T3(0,E(_l3.a),E(_l3.b),E(_l3.c));});return new T2(0,_kQ,_kN);},_l4=function(_l5){return E(E(_l5).a);},_l6=function(_l7,_l8,_l9,_la,_lb,_lc,_ld){var _le=B(_7n(_l7,_lb,_lc,_ld,_l8,_l9,_la)),_lf=B(_7j(B(_7h(_l7)))),_lg=B(_kq(_lf,_lb,_lc,_ld,_le,_le,_le)),_lh=B(_6K(_lf));return new F(function(){return _kz(_lf,_l8,_l9,_la,B(A1(_lh,_lg.a)),B(A1(_lh,_lg.b)),B(A1(_lh,_lg.c)));});},_li=function(_lj){return E(E(_lj).a);},_lk=function(_ll,_lm,_ln,_lo){var _lp=new T(function(){var _lq=E(_lo),_lr=E(_ln),_ls=B(_l6(_ll,_lq.a,_lq.b,_lq.c,_lr.a,_lr.b,_lr.c));return new T3(0,E(_ls.a),E(_ls.b),E(_ls.c));}),_lt=new T(function(){return B(A2(_7B,_ll,new T(function(){var _lu=E(_lp),_lv=_lu.a,_lw=_lu.b,_lx=_lu.c;return B(_7n(_ll,_lv,_lw,_lx,_lv,_lw,_lx));})));});if(!B(A3(_li,B(_l4(_lm)),_lt,new T(function(){return B(A2(_7z,B(_7j(B(_7h(_ll)))),_91));})))){var _ly=E(_lp),_lz=B(_kj(_ll,_ly.a,_ly.b,_ly.c)),_lA=B(A2(_7B,_ll,new T(function(){var _lB=E(_lo),_lC=_lB.a,_lD=_lB.b,_lE=_lB.c;return B(_7n(_ll,_lC,_lD,_lE,_lC,_lD,_lE));}))),_lF=B(_7l(new T(function(){return B(_7j(new T(function(){return B(_7h(_ll));})));})));return new T3(0,B(A1(B(A1(_lF,_lz.a)),_lA)),B(A1(B(A1(_lF,_lz.b)),_lA)),B(A1(B(A1(_lF,_lz.c)),_lA)));}else{var _lG=B(A2(_7z,B(_7j(B(_7h(_ll)))),_91));return new T3(0,_lG,_lG,_lG);}},_lH=new T(function(){var _lI=eval("angleCount"),_lJ=Number(_lI);return jsTrunc(_lJ);}),_lK=new T(function(){return E(_lH);}),_lL=new T(function(){return B(unCStr(": empty list"));}),_lM=new T(function(){return B(unCStr("Prelude."));}),_lN=function(_lO){return new F(function(){return err(B(_f(_lM,new T(function(){return B(_f(_lO,_lL));},1))));});},_lP=new T(function(){return B(unCStr("head"));}),_lQ=new T(function(){return B(_lN(_lP));}),_lR=function(_lS,_lT,_lU){var _lV=E(_lS);if(!_lV._){return __Z;}else{var _lW=E(_lT);if(!_lW._){return __Z;}else{var _lX=_lW.a,_lY=E(_lU);if(!_lY._){return __Z;}else{var _lZ=E(_lY.a),_m0=_lZ.a;return new F(function(){return _f(new T2(1,new T(function(){return new T3(0,E(_lV.a),E(_lX),E(_m0));}),new T2(1,new T(function(){return new T3(0,E(_lX),E(_m0),E(_lZ.b));}),_o)),new T(function(){return B(_lR(_lV.b,_lW.b,_lY.b));},1));});}}}},_m1=new T(function(){return B(unCStr("tail"));}),_m2=new T(function(){return B(_lN(_m1));}),_m3=function(_m4,_m5){var _m6=E(_m4);if(!_m6._){return __Z;}else{var _m7=E(_m5);return (_m7._==0)?__Z:new T2(1,new T2(0,_m6.a,_m7.a),new T(function(){return B(_m3(_m6.b,_m7.b));}));}},_m8=function(_m9,_ma){var _mb=E(_m9);if(!_mb._){return __Z;}else{var _mc=E(_ma);if(!_mc._){return __Z;}else{var _md=E(_mb.a),_me=_md.b,_mf=E(_mc.a).b,_mg=new T(function(){var _mh=new T(function(){return B(_m3(_mf,new T(function(){var _mi=E(_mf);if(!_mi._){return E(_m2);}else{return E(_mi.b);}},1)));},1);return B(_lR(_me,new T(function(){var _mj=E(_me);if(!_mj._){return E(_m2);}else{return E(_mj.b);}},1),_mh));});return new F(function(){return _f(new T2(1,new T(function(){var _mk=E(_me);if(!_mk._){return E(_lQ);}else{var _ml=E(_mf);if(!_ml._){return E(_lQ);}else{return new T3(0,E(_md.a),E(_mk.a),E(_ml.a));}}}),_mg),new T(function(){return B(_m8(_mb.b,_mc.b));},1));});}}},_mm=new T(function(){return E(_lK)-1;}),_mn=new T1(0,1),_mo=function(_mp,_mq){var _mr=E(_mq),_ms=new T(function(){var _mt=B(_7j(_mp)),_mu=B(_mo(_mp,B(A3(_6I,_mt,_mr,new T(function(){return B(A2(_7z,_mt,_mn));})))));return new T2(1,_mu.a,_mu.b);});return new T2(0,_mr,_ms);},_mv=function(_mw){return E(E(_mw).d);},_mx=new T1(0,2),_my=function(_mz,_mA){var _mB=E(_mA);if(!_mB._){return __Z;}else{var _mC=_mB.a;return (!B(A1(_mz,_mC)))?__Z:new T2(1,_mC,new T(function(){return B(_my(_mz,_mB.b));}));}},_mD=function(_mE,_mF,_mG,_mH){var _mI=B(_mo(_mF,_mG)),_mJ=new T(function(){var _mK=B(_7j(_mF)),_mL=new T(function(){return B(A3(_9a,_mF,new T(function(){return B(A2(_7z,_mK,_mn));}),new T(function(){return B(A2(_7z,_mK,_mx));})));});return B(A3(_6I,_mK,_mH,_mL));});return new F(function(){return _my(function(_mM){return new F(function(){return A3(_mv,_mE,_mM,_mJ);});},new T2(1,_mI.a,_mI.b));});},_mN=new T(function(){return B(_mD(_jt,_is,_ho,_mm));}),_mO=function(_mP,_mQ){while(1){var _mR=E(_mP);if(!_mR._){return E(_mQ);}else{_mP=_mR.b;_mQ=_mR.a;continue;}}},_mS=new T(function(){return B(unCStr("last"));}),_mT=new T(function(){return B(_lN(_mS));}),_mU=function(_mV){return new F(function(){return _mO(_mV,_mT);});},_mW=function(_mX){return new F(function(){return _mU(E(_mX).b);});},_mY=new T(function(){var _mZ=eval("proceedCount"),_n0=Number(_mZ);return jsTrunc(_n0);}),_n1=new T(function(){return E(_mY);}),_n2=1,_n3=new T(function(){return B(_mD(_jt,_is,_n2,_n1));}),_n4=function(_n5,_n6,_n7,_n8,_n9,_na,_nb,_nc,_nd,_ne,_nf,_ng,_nh,_ni){var _nj=new T(function(){var _nk=new T(function(){var _nl=E(_ne),_nm=E(_ni),_nn=E(_nh),_no=E(_nf),_np=E(_ng),_nq=E(_nd);return new T3(0,_nl*_nm-_nn*_no,_no*_np-_nm*_nq,_nq*_nn-_np*_nl);}),_nr=function(_ns){var _nt=new T(function(){var _nu=E(_ns)/E(_lK);return (_nu+_nu)*3.141592653589793;}),_nv=new T(function(){return B(A1(_n5,_nt));}),_nw=new T(function(){var _nx=new T(function(){var _ny=E(_nv)/E(_n1);return new T3(0,E(_ny),E(_ny),E(_ny));}),_nz=function(_nA,_nB){var _nC=E(_nA);if(!_nC._){return new T2(0,_o,_nB);}else{var _nD=new T(function(){var _nE=B(_kI(_ki,new T(function(){var _nF=E(_nB),_nG=E(_nF.a),_nH=E(_nF.b),_nI=E(_nx);return new T3(0,E(_nG.a)+E(_nH.a)*E(_nI.a),E(_nG.b)+E(_nH.b)*E(_nI.b),E(_nG.c)+E(_nH.c)*E(_nI.c));}))),_nJ=_nE.a,_nK=new T(function(){var _nL=E(_nE.b),_nM=E(E(_nB).b),_nN=B(_l6(_iU,_nM.a,_nM.b,_nM.c,_nL.a,_nL.b,_nL.c)),_nO=B(_kj(_iU,_nN.a,_nN.b,_nN.c));return new T3(0,E(_nO.a),E(_nO.b),E(_nO.c));});return new T2(0,new T(function(){var _nP=E(_nv),_nQ=E(_nt);return new T4(0,E(_nJ),E(new T2(0,E(_nC.a)/E(_n1),E(_nP))),E(_nQ),E(_nK));}),new T2(0,_nJ,_nK));}),_nR=new T(function(){var _nS=B(_nz(_nC.b,new T(function(){return E(E(_nD).b);})));return new T2(0,_nS.a,_nS.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nD).a);}),new T(function(){return E(E(_nR).a);})),new T(function(){return E(E(_nR).b);}));}},_nT=function(_nU,_nV,_nW,_nX,_nY){var _nZ=E(_nU);if(!_nZ._){return new T2(0,_o,new T2(0,new T3(0,E(_nV),E(_nW),E(_nX)),_nY));}else{var _o0=new T(function(){var _o1=B(_kI(_ki,new T(function(){var _o2=E(_nY),_o3=E(_nx);return new T3(0,E(_nV)+E(_o2.a)*E(_o3.a),E(_nW)+E(_o2.b)*E(_o3.b),E(_nX)+E(_o2.c)*E(_o3.c));}))),_o4=_o1.a,_o5=new T(function(){var _o6=E(_o1.b),_o7=E(_nY),_o8=B(_l6(_iU,_o7.a,_o7.b,_o7.c,_o6.a,_o6.b,_o6.c)),_o9=B(_kj(_iU,_o8.a,_o8.b,_o8.c));return new T3(0,E(_o9.a),E(_o9.b),E(_o9.c));});return new T2(0,new T(function(){var _oa=E(_nv),_ob=E(_nt);return new T4(0,E(_o4),E(new T2(0,E(_nZ.a)/E(_n1),E(_oa))),E(_ob),E(_o5));}),new T2(0,_o4,_o5));}),_oc=new T(function(){var _od=B(_nz(_nZ.b,new T(function(){return E(E(_o0).b);})));return new T2(0,_od.a,_od.b);});return new T2(0,new T2(1,new T(function(){return E(E(_o0).a);}),new T(function(){return E(E(_oc).a);})),new T(function(){return E(E(_oc).b);}));}};return E(B(_nT(_n3,_n8,_n9,_na,new T(function(){var _oe=E(_nk),_of=E(_nt)+_nb,_og=Math.cos(_of),_oh=Math.sin(_of);return new T3(0,E(_nd)*_og+E(_oe.a)*_oh,E(_ne)*_og+E(_oe.b)*_oh,E(_nf)*_og+E(_oe.c)*_oh);}))).a);});return new T2(0,new T(function(){var _oi=E(_nv),_oj=E(_nt);return new T4(0,E(new T3(0,E(_n8),E(_n9),E(_na))),E(new T2(0,E(_ho),E(_oi))),E(_oj),E(_hp));}),_nw);};return B(_k6(_nr,_mN));}),_ok=new T(function(){var _ol=new T(function(){var _om=B(_f(_nj,new T2(1,new T(function(){var _on=E(_nj);if(!_on._){return E(_lQ);}else{return E(_on.a);}}),_o)));if(!_om._){return E(_m2);}else{return E(_om.b);}},1);return B(_m8(_nj,_ol));});return new T2(0,_ok,new T(function(){return B(_k6(_mW,_nj));}));},_oo=function(_op,_oq,_or,_os,_ot,_ou,_ov,_ow,_ox,_oy,_oz,_oA,_oB,_oC,_oD,_oE,_oF){var _oG=B(_kI(_ki,new T3(0,E(_os),E(_ot),E(_ou)))),_oH=_oG.b,_oI=E(_oG.a),_oJ=B(_lk(_iU,_jt,_oH,new T3(0,E(_ow),E(_ox),E(_oy)))),_oK=E(_oH),_oL=_oK.a,_oM=_oK.b,_oN=_oK.c,_oO=B(_l6(_iU,_oA,_oB,_oC,_oL,_oM,_oN)),_oP=B(_kj(_iU,_oO.a,_oO.b,_oO.c)),_oQ=_oP.a,_oR=_oP.b,_oS=_oP.c,_oT=E(_ov),_oU=new T2(0,E(new T3(0,E(_oJ.a),E(_oJ.b),E(_oJ.c))),E(_oz)),_oV=B(_n4(_op,_oq,_or,_oI.a,_oI.b,_oI.c,_oT,_oU,_oQ,_oR,_oS,_oL,_oM,_oN)),_oW=__lst2arr(B(_k6(_kf,_oV.a))),_oX=__lst2arr(B(_k6(_k0,_oV.b)));return {_:0,a:_op,b:_oq,c:_or,d:new T2(0,E(_oI),E(_oT)),e:_oU,f:new T3(0,E(_oQ),E(_oR),E(_oS)),g:_oK,h:_oW,i:_oX};},_oY=function(_oZ){var _p0=E(_oZ);return new T3(0, -E(_p0.a), -E(_p0.c),E(_p0.b));},_p1=new T(function(){return 6.283185307179586/E(_lK);}),_p2=function(_){return new F(function(){return __jsNull();});},_p3=function(_p4){var _p5=B(A1(_p4,_));return E(_p5);},_p6=new T(function(){return B(_p3(_p2));}),_p7=function(_p8,_p9,_pa,_pb,_pc,_pd,_pe,_pf,_pg,_ph,_pi,_pj,_pk){var _pl=function(_pm){var _pn=E(_p1),_po=2+_pm|0,_pp=_po-1|0,_pq=(2+_pm)*(1+_pm),_pr=E(_mN);if(!_pr._){return _pn*0;}else{var _ps=_pr.a,_pt=_pr.b,_pu=B(A1(_p8,new T(function(){return 6.283185307179586*E(_ps)/E(_lK);}))),_pv=B(A1(_p8,new T(function(){return 6.283185307179586*(E(_ps)+1)/E(_lK);})));if(_pu!=_pv){if(_po>=0){var _pw=E(_po);if(!_pw){var _px=function(_py,_pz){while(1){var _pA=B((function(_pB,_pC){var _pD=E(_pB);if(!_pD._){return E(_pC);}else{var _pE=_pD.a,_pF=_pD.b,_pG=B(A1(_p8,new T(function(){return 6.283185307179586*E(_pE)/E(_lK);}))),_pH=B(A1(_p8,new T(function(){return 6.283185307179586*(E(_pE)+1)/E(_lK);})));if(_pG!=_pH){var _pI=_pC+0/(_pG-_pH)/_pq;_py=_pF;_pz=_pI;return __continue;}else{if(_pp>=0){var _pJ=E(_pp);if(!_pJ){var _pI=_pC+_po/_pq;_py=_pF;_pz=_pI;return __continue;}else{var _pI=_pC+_po*B(_hB(_pG,_pJ))/_pq;_py=_pF;_pz=_pI;return __continue;}}else{return E(_hs);}}}})(_py,_pz));if(_pA!=__continue){return _pA;}}};return _pn*B(_px(_pt,0/(_pu-_pv)/_pq));}else{var _pK=function(_pL,_pM){while(1){var _pN=B((function(_pO,_pP){var _pQ=E(_pO);if(!_pQ._){return E(_pP);}else{var _pR=_pQ.a,_pS=_pQ.b,_pT=B(A1(_p8,new T(function(){return 6.283185307179586*E(_pR)/E(_lK);}))),_pU=B(A1(_p8,new T(function(){return 6.283185307179586*(E(_pR)+1)/E(_lK);})));if(_pT!=_pU){if(_pw>=0){var _pV=_pP+(B(_hB(_pT,_pw))-B(_hB(_pU,_pw)))/(_pT-_pU)/_pq;_pL=_pS;_pM=_pV;return __continue;}else{return E(_hs);}}else{if(_pp>=0){var _pW=E(_pp);if(!_pW){var _pV=_pP+_po/_pq;_pL=_pS;_pM=_pV;return __continue;}else{var _pV=_pP+_po*B(_hB(_pT,_pW))/_pq;_pL=_pS;_pM=_pV;return __continue;}}else{return E(_hs);}}}})(_pL,_pM));if(_pN!=__continue){return _pN;}}};return _pn*B(_pK(_pt,(B(_hB(_pu,_pw))-B(_hB(_pv,_pw)))/(_pu-_pv)/_pq));}}else{return E(_hs);}}else{if(_pp>=0){var _pX=E(_pp);if(!_pX){var _pY=function(_pZ,_q0){while(1){var _q1=B((function(_q2,_q3){var _q4=E(_q2);if(!_q4._){return E(_q3);}else{var _q5=_q4.a,_q6=_q4.b,_q7=B(A1(_p8,new T(function(){return 6.283185307179586*E(_q5)/E(_lK);}))),_q8=B(A1(_p8,new T(function(){return 6.283185307179586*(E(_q5)+1)/E(_lK);})));if(_q7!=_q8){if(_po>=0){var _q9=E(_po);if(!_q9){var _qa=_q3+0/(_q7-_q8)/_pq;_pZ=_q6;_q0=_qa;return __continue;}else{var _qa=_q3+(B(_hB(_q7,_q9))-B(_hB(_q8,_q9)))/(_q7-_q8)/_pq;_pZ=_q6;_q0=_qa;return __continue;}}else{return E(_hs);}}else{var _qa=_q3+_po/_pq;_pZ=_q6;_q0=_qa;return __continue;}}})(_pZ,_q0));if(_q1!=__continue){return _q1;}}};return _pn*B(_pY(_pt,_po/_pq));}else{var _qb=function(_qc,_qd){while(1){var _qe=B((function(_qf,_qg){var _qh=E(_qf);if(!_qh._){return E(_qg);}else{var _qi=_qh.a,_qj=_qh.b,_qk=B(A1(_p8,new T(function(){return 6.283185307179586*E(_qi)/E(_lK);}))),_ql=B(A1(_p8,new T(function(){return 6.283185307179586*(E(_qi)+1)/E(_lK);})));if(_qk!=_ql){if(_po>=0){var _qm=E(_po);if(!_qm){var _qn=_qg+0/(_qk-_ql)/_pq;_qc=_qj;_qd=_qn;return __continue;}else{var _qn=_qg+(B(_hB(_qk,_qm))-B(_hB(_ql,_qm)))/(_qk-_ql)/_pq;_qc=_qj;_qd=_qn;return __continue;}}else{return E(_hs);}}else{if(_pX>=0){var _qn=_qg+_po*B(_hB(_qk,_pX))/_pq;_qc=_qj;_qd=_qn;return __continue;}else{return E(_hs);}}}})(_qc,_qd));if(_qe!=__continue){return _qe;}}};return _pn*B(_qb(_pt,_po*B(_hB(_pu,_pX))/_pq));}}else{return E(_hs);}}}},_qo=E(_p6),_qp=1/(B(_pl(1))*_p9);return new F(function(){return _oo(_p8,_oY,new T2(0,E(new T3(0,E(_qp),E(_qp),E(_qp))),1/(B(_pl(3))*_p9)),_pa,_pb,_pc,_pd,_pe,_pf,_pg,_ph,_pi,_pj,_pk,_hp,_qo,_qo);});},_qq=0,_qr=function(_qs){return E(_hp);},_qt=0.7853981633974483,_qu=function(_qv){var _qw=I_decodeDouble(_qv);return new T2(0,new T1(1,_qw.b),_qw.a);},_qx=function(_qy){return new T1(0,_qy);},_qz=function(_qA){var _qB=hs_intToInt64(2147483647),_qC=hs_leInt64(_qA,_qB);if(!_qC){return new T1(1,I_fromInt64(_qA));}else{var _qD=hs_intToInt64(-2147483648),_qE=hs_geInt64(_qA,_qD);if(!_qE){return new T1(1,I_fromInt64(_qA));}else{var _qF=hs_int64ToInt(_qA);return new F(function(){return _qx(_qF);});}}},_qG=new T(function(){var _qH=newByteArr(256),_qI=_qH,_=_qI["v"]["i8"][0]=8,_qJ=function(_qK,_qL,_qM,_){while(1){if(_qM>=256){if(_qK>=256){return E(_);}else{var _qN=imul(2,_qK)|0,_qO=_qL+1|0,_qP=_qK;_qK=_qN;_qL=_qO;_qM=_qP;continue;}}else{var _=_qI["v"]["i8"][_qM]=_qL,_qP=_qM+_qK|0;_qM=_qP;continue;}}},_=B(_qJ(2,0,1,_));return _qI;}),_qQ=function(_qR,_qS){var _qT=hs_int64ToInt(_qR),_qU=E(_qG),_qV=_qU["v"]["i8"][(255&_qT>>>0)>>>0&4294967295];if(_qS>_qV){if(_qV>=8){var _qW=hs_uncheckedIShiftRA64(_qR,8),_qX=function(_qY,_qZ){while(1){var _r0=B((function(_r1,_r2){var _r3=hs_int64ToInt(_r1),_r4=_qU["v"]["i8"][(255&_r3>>>0)>>>0&4294967295];if(_r2>_r4){if(_r4>=8){var _r5=hs_uncheckedIShiftRA64(_r1,8),_r6=_r2-8|0;_qY=_r5;_qZ=_r6;return __continue;}else{return new T2(0,new T(function(){var _r7=hs_uncheckedIShiftRA64(_r1,_r4);return B(_qz(_r7));}),_r2-_r4|0);}}else{return new T2(0,new T(function(){var _r8=hs_uncheckedIShiftRA64(_r1,_r2);return B(_qz(_r8));}),0);}})(_qY,_qZ));if(_r0!=__continue){return _r0;}}};return new F(function(){return _qX(_qW,_qS-8|0);});}else{return new T2(0,new T(function(){var _r9=hs_uncheckedIShiftRA64(_qR,_qV);return B(_qz(_r9));}),_qS-_qV|0);}}else{return new T2(0,new T(function(){var _ra=hs_uncheckedIShiftRA64(_qR,_qS);return B(_qz(_ra));}),0);}},_rb=function(_rc){var _rd=hs_intToInt64(_rc);return E(_rd);},_re=function(_rf){var _rg=E(_rf);if(!_rg._){return new F(function(){return _rb(_rg.a);});}else{return new F(function(){return I_toInt64(_rg.a);});}},_rh=function(_ri){return I_toInt(_ri)>>>0;},_rj=function(_rk){var _rl=E(_rk);if(!_rl._){return _rl.a>>>0;}else{return new F(function(){return _rh(_rl.a);});}},_rm=function(_rn){var _ro=B(_qu(_rn)),_rp=_ro.a,_rq=_ro.b;if(_rq<0){var _rr=function(_rs){if(!_rs){return new T2(0,E(_rp),B(_3u(_1M, -_rq)));}else{var _rt=B(_qQ(B(_re(_rp)), -_rq));return new T2(0,E(_rt.a),B(_3u(_1M,_rt.b)));}};if(!((B(_rj(_rp))&1)>>>0)){return new F(function(){return _rr(1);});}else{return new F(function(){return _rr(0);});}}else{return new T2(0,B(_3u(_rp,_rq)),_1M);}},_ru=function(_rv){var _rw=B(_rm(E(_rv)));return new T2(0,E(_rw.a),E(_rw.b));},_rx=new T3(0,_io,_jt,_ru),_ry=function(_rz){return E(E(_rz).a);},_rA=function(_rB){return E(E(_rB).a);},_rC=function(_rD,_rE){if(_rD<=_rE){var _rF=function(_rG){return new T2(1,_rG,new T(function(){if(_rG!=_rE){return B(_rF(_rG+1|0));}else{return __Z;}}));};return new F(function(){return _rF(_rD);});}else{return __Z;}},_rH=function(_rI){return new F(function(){return _rC(E(_rI),2147483647);});},_rJ=function(_rK,_rL,_rM){if(_rM<=_rL){var _rN=new T(function(){var _rO=_rL-_rK|0,_rP=function(_rQ){return (_rQ>=(_rM-_rO|0))?new T2(1,_rQ,new T(function(){return B(_rP(_rQ+_rO|0));})):new T2(1,_rQ,_o);};return B(_rP(_rL));});return new T2(1,_rK,_rN);}else{return (_rM<=_rK)?new T2(1,_rK,_o):__Z;}},_rR=function(_rS,_rT,_rU){if(_rU>=_rT){var _rV=new T(function(){var _rW=_rT-_rS|0,_rX=function(_rY){return (_rY<=(_rU-_rW|0))?new T2(1,_rY,new T(function(){return B(_rX(_rY+_rW|0));})):new T2(1,_rY,_o);};return B(_rX(_rT));});return new T2(1,_rS,_rV);}else{return (_rU>=_rS)?new T2(1,_rS,_o):__Z;}},_rZ=function(_s0,_s1){if(_s1<_s0){return new F(function(){return _rJ(_s0,_s1,-2147483648);});}else{return new F(function(){return _rR(_s0,_s1,2147483647);});}},_s2=function(_s3,_s4){return new F(function(){return _rZ(E(_s3),E(_s4));});},_s5=function(_s6,_s7,_s8){if(_s7<_s6){return new F(function(){return _rJ(_s6,_s7,_s8);});}else{return new F(function(){return _rR(_s6,_s7,_s8);});}},_s9=function(_sa,_sb,_sc){return new F(function(){return _s5(E(_sa),E(_sb),E(_sc));});},_sd=function(_se,_sf){return new F(function(){return _rC(E(_se),E(_sf));});},_sg=function(_sh){return E(_sh);},_si=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_sj=new T(function(){return B(err(_si));}),_sk=function(_sl){var _sm=E(_sl);return (_sm==(-2147483648))?E(_sj):_sm-1|0;},_sn=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_so=new T(function(){return B(err(_sn));}),_sp=function(_sq){var _sr=E(_sq);return (_sr==2147483647)?E(_so):_sr+1|0;},_ss={_:0,a:_sp,b:_sk,c:_sg,d:_sg,e:_rH,f:_s2,g:_sd,h:_s9},_st=function(_su,_sv){if(_su<=0){if(_su>=0){return new F(function(){return quot(_su,_sv);});}else{if(_sv<=0){return new F(function(){return quot(_su,_sv);});}else{return quot(_su+1|0,_sv)-1|0;}}}else{if(_sv>=0){if(_su>=0){return new F(function(){return quot(_su,_sv);});}else{if(_sv<=0){return new F(function(){return quot(_su,_sv);});}else{return quot(_su+1|0,_sv)-1|0;}}}else{return quot(_su-1|0,_sv)-1|0;}}},_sw=0,_sx=new T(function(){return B(_2R(_sw));}),_sy=new T(function(){return die(_sx);}),_sz=function(_sA,_sB){var _sC=E(_sB);switch(_sC){case -1:var _sD=E(_sA);if(_sD==(-2147483648)){return E(_sy);}else{return new F(function(){return _st(_sD,-1);});}break;case 0:return E(_2V);default:return new F(function(){return _st(_sA,_sC);});}},_sE=function(_sF,_sG){return new F(function(){return _sz(E(_sF),E(_sG));});},_sH=0,_sI=new T2(0,_sy,_sH),_sJ=function(_sK,_sL){var _sM=E(_sK),_sN=E(_sL);switch(_sN){case -1:var _sO=E(_sM);if(_sO==(-2147483648)){return E(_sI);}else{if(_sO<=0){if(_sO>=0){var _sP=quotRemI(_sO,-1);return new T2(0,_sP.a,_sP.b);}else{var _sQ=quotRemI(_sO,-1);return new T2(0,_sQ.a,_sQ.b);}}else{var _sR=quotRemI(_sO-1|0,-1);return new T2(0,_sR.a-1|0,(_sR.b+(-1)|0)+1|0);}}break;case 0:return E(_2V);default:if(_sM<=0){if(_sM>=0){var _sS=quotRemI(_sM,_sN);return new T2(0,_sS.a,_sS.b);}else{if(_sN<=0){var _sT=quotRemI(_sM,_sN);return new T2(0,_sT.a,_sT.b);}else{var _sU=quotRemI(_sM+1|0,_sN);return new T2(0,_sU.a-1|0,(_sU.b+_sN|0)-1|0);}}}else{if(_sN>=0){if(_sM>=0){var _sV=quotRemI(_sM,_sN);return new T2(0,_sV.a,_sV.b);}else{if(_sN<=0){var _sW=quotRemI(_sM,_sN);return new T2(0,_sW.a,_sW.b);}else{var _sX=quotRemI(_sM+1|0,_sN);return new T2(0,_sX.a-1|0,(_sX.b+_sN|0)-1|0);}}}else{var _sY=quotRemI(_sM-1|0,_sN);return new T2(0,_sY.a-1|0,(_sY.b+_sN|0)+1|0);}}}},_sZ=function(_t0,_t1){var _t2=_t0%_t1;if(_t0<=0){if(_t0>=0){return E(_t2);}else{if(_t1<=0){return E(_t2);}else{var _t3=E(_t2);return (_t3==0)?0:_t3+_t1|0;}}}else{if(_t1>=0){if(_t0>=0){return E(_t2);}else{if(_t1<=0){return E(_t2);}else{var _t4=E(_t2);return (_t4==0)?0:_t4+_t1|0;}}}else{var _t5=E(_t2);return (_t5==0)?0:_t5+_t1|0;}}},_t6=function(_t7,_t8){var _t9=E(_t8);switch(_t9){case -1:return E(_sH);case 0:return E(_2V);default:return new F(function(){return _sZ(E(_t7),_t9);});}},_ta=function(_tb,_tc){var _td=E(_tb),_te=E(_tc);switch(_te){case -1:var _tf=E(_td);if(_tf==(-2147483648)){return E(_sy);}else{return new F(function(){return quot(_tf,-1);});}break;case 0:return E(_2V);default:return new F(function(){return quot(_td,_te);});}},_tg=function(_th,_ti){var _tj=E(_th),_tk=E(_ti);switch(_tk){case -1:var _tl=E(_tj);if(_tl==(-2147483648)){return E(_sI);}else{var _tm=quotRemI(_tl,-1);return new T2(0,_tm.a,_tm.b);}break;case 0:return E(_2V);default:var _tn=quotRemI(_tj,_tk);return new T2(0,_tn.a,_tn.b);}},_to=function(_tp,_tq){var _tr=E(_tq);switch(_tr){case -1:return E(_sH);case 0:return E(_2V);default:return E(_tp)%_tr;}},_ts=function(_tt){return new F(function(){return _qx(E(_tt));});},_tu=function(_tv){return new T2(0,E(B(_qx(E(_tv)))),E(_mn));},_tw=function(_tx,_ty){return imul(E(_tx),E(_ty))|0;},_tz=function(_tA,_tB){return E(_tA)+E(_tB)|0;},_tC=function(_tD,_tE){return E(_tD)-E(_tE)|0;},_tF=function(_tG){var _tH=E(_tG);return (_tH<0)? -_tH:E(_tH);},_tI=function(_tJ){return new F(function(){return _38(_tJ);});},_tK=function(_tL){return  -E(_tL);},_tM=-1,_tN=0,_tO=1,_tP=function(_tQ){var _tR=E(_tQ);return (_tR>=0)?(E(_tR)==0)?E(_tN):E(_tO):E(_tM);},_tS={_:0,a:_tz,b:_tC,c:_tw,d:_tK,e:_tF,f:_tP,g:_tI},_tT=function(_tU,_tV){return E(_tU)==E(_tV);},_tW=function(_tX,_tY){return E(_tX)!=E(_tY);},_tZ=new T2(0,_tT,_tW),_u0=function(_u1,_u2){var _u3=E(_u1),_u4=E(_u2);return (_u3>_u4)?E(_u3):E(_u4);},_u5=function(_u6,_u7){var _u8=E(_u6),_u9=E(_u7);return (_u8>_u9)?E(_u9):E(_u8);},_ua=function(_ub,_uc){return (_ub>=_uc)?(_ub!=_uc)?2:1:0;},_ud=function(_ue,_uf){return new F(function(){return _ua(E(_ue),E(_uf));});},_ug=function(_uh,_ui){return E(_uh)>=E(_ui);},_uj=function(_uk,_ul){return E(_uk)>E(_ul);},_um=function(_un,_uo){return E(_un)<=E(_uo);},_up=function(_uq,_ur){return E(_uq)<E(_ur);},_us={_:0,a:_tZ,b:_ud,c:_up,d:_um,e:_uj,f:_ug,g:_u0,h:_u5},_ut=new T3(0,_tS,_us,_tu),_uu={_:0,a:_ut,b:_ss,c:_ta,d:_to,e:_sE,f:_t6,g:_tg,h:_sJ,i:_ts},_uv=new T1(0,2),_uw=function(_ux,_uy){while(1){var _uz=E(_ux);if(!_uz._){var _uA=_uz.a,_uB=E(_uy);if(!_uB._){var _uC=_uB.a;if(!(imul(_uA,_uC)|0)){return new T1(0,imul(_uA,_uC)|0);}else{_ux=new T1(1,I_fromInt(_uA));_uy=new T1(1,I_fromInt(_uC));continue;}}else{_ux=new T1(1,I_fromInt(_uA));_uy=_uB;continue;}}else{var _uD=E(_uy);if(!_uD._){_ux=_uz;_uy=new T1(1,I_fromInt(_uD.a));continue;}else{return new T1(1,I_mul(_uz.a,_uD.a));}}}},_uE=function(_uF,_uG,_uH){while(1){if(!(_uG%2)){var _uI=B(_uw(_uF,_uF)),_uJ=quot(_uG,2);_uF=_uI;_uG=_uJ;continue;}else{var _uK=E(_uG);if(_uK==1){return new F(function(){return _uw(_uF,_uH);});}else{var _uI=B(_uw(_uF,_uF)),_uL=B(_uw(_uF,_uH));_uF=_uI;_uG=quot(_uK-1|0,2);_uH=_uL;continue;}}}},_uM=function(_uN,_uO){while(1){if(!(_uO%2)){var _uP=B(_uw(_uN,_uN)),_uQ=quot(_uO,2);_uN=_uP;_uO=_uQ;continue;}else{var _uR=E(_uO);if(_uR==1){return E(_uN);}else{return new F(function(){return _uE(B(_uw(_uN,_uN)),quot(_uR-1|0,2),_uN);});}}}},_uS=function(_uT){return E(E(_uT).b);},_uU=function(_uV){return E(E(_uV).c);},_uW=new T1(0,0),_uX=function(_uY){return E(E(_uY).d);},_uZ=function(_v0,_v1){var _v2=B(_ry(_v0)),_v3=new T(function(){return B(_rA(_v2));}),_v4=new T(function(){return B(A3(_uX,_v0,_v1,new T(function(){return B(A2(_7z,_v3,_mx));})));});return new F(function(){return A3(_li,B(_l4(B(_uS(_v2)))),_v4,new T(function(){return B(A2(_7z,_v3,_uW));}));});},_v5=new T(function(){return B(unCStr("Negative exponent"));}),_v6=new T(function(){return B(err(_v5));}),_v7=function(_v8){return E(E(_v8).c);},_v9=function(_va,_vb,_vc,_vd){var _ve=B(_ry(_vb)),_vf=new T(function(){return B(_rA(_ve));}),_vg=B(_uS(_ve));if(!B(A3(_uU,_vg,_vd,new T(function(){return B(A2(_7z,_vf,_uW));})))){if(!B(A3(_li,B(_l4(_vg)),_vd,new T(function(){return B(A2(_7z,_vf,_uW));})))){var _vh=new T(function(){return B(A2(_7z,_vf,_mx));}),_vi=new T(function(){return B(A2(_7z,_vf,_mn));}),_vj=B(_l4(_vg)),_vk=function(_vl,_vm,_vn){while(1){var _vo=B((function(_vp,_vq,_vr){if(!B(_uZ(_vb,_vq))){if(!B(A3(_li,_vj,_vq,_vi))){var _vs=new T(function(){return B(A3(_v7,_vb,new T(function(){return B(A3(_7x,_vf,_vq,_vi));}),_vh));});_vl=new T(function(){return B(A3(_7l,_va,_vp,_vp));});_vm=_vs;_vn=new T(function(){return B(A3(_7l,_va,_vp,_vr));});return __continue;}else{return new F(function(){return A3(_7l,_va,_vp,_vr);});}}else{var _vt=_vr;_vl=new T(function(){return B(A3(_7l,_va,_vp,_vp));});_vm=new T(function(){return B(A3(_v7,_vb,_vq,_vh));});_vn=_vt;return __continue;}})(_vl,_vm,_vn));if(_vo!=__continue){return _vo;}}},_vu=function(_vv,_vw){while(1){var _vx=B((function(_vy,_vz){if(!B(_uZ(_vb,_vz))){if(!B(A3(_li,_vj,_vz,_vi))){var _vA=new T(function(){return B(A3(_v7,_vb,new T(function(){return B(A3(_7x,_vf,_vz,_vi));}),_vh));});return new F(function(){return _vk(new T(function(){return B(A3(_7l,_va,_vy,_vy));}),_vA,_vy);});}else{return E(_vy);}}else{_vv=new T(function(){return B(A3(_7l,_va,_vy,_vy));});_vw=new T(function(){return B(A3(_v7,_vb,_vz,_vh));});return __continue;}})(_vv,_vw));if(_vx!=__continue){return _vx;}}};return new F(function(){return _vu(_vc,_vd);});}else{return new F(function(){return A2(_7z,_va,_mn);});}}else{return E(_v6);}},_vB=new T(function(){return B(err(_v5));}),_vC=function(_vD,_vE){var _vF=B(_qu(_vE)),_vG=_vF.a,_vH=_vF.b,_vI=new T(function(){return B(_rA(new T(function(){return B(_ry(_vD));})));});if(_vH<0){var _vJ= -_vH;if(_vJ>=0){var _vK=E(_vJ);if(!_vK){var _vL=E(_mn);}else{var _vL=B(_uM(_uv,_vK));}if(!B(_30(_vL,_3t))){var _vM=B(_3k(_vG,_vL));return new T2(0,new T(function(){return B(A2(_7z,_vI,_vM.a));}),new T(function(){return B(_2W(_vM.b,_vH));}));}else{return E(_2V);}}else{return E(_vB);}}else{var _vN=new T(function(){var _vO=new T(function(){return B(_v9(_vI,_uu,new T(function(){return B(A2(_7z,_vI,_uv));}),_vH));});return B(A3(_7l,_vI,new T(function(){return B(A2(_7z,_vI,_vG));}),_vO));});return new T2(0,_vN,_6i);}},_vP=function(_vQ,_vR){var _vS=B(_vC(_vQ,E(_vR))),_vT=_vS.a;if(E(_vS.b)<=0){return E(_vT);}else{var _vU=B(_rA(B(_ry(_vQ))));return new F(function(){return A3(_6I,_vU,_vT,new T(function(){return B(A2(_7z,_vU,_1M));}));});}},_vV=function(_vW,_vX){var _vY=B(_vC(_vW,E(_vX))),_vZ=_vY.a;if(E(_vY.b)>=0){return E(_vZ);}else{var _w0=B(_rA(B(_ry(_vW))));return new F(function(){return A3(_7x,_w0,_vZ,new T(function(){return B(A2(_7z,_w0,_1M));}));});}},_w1=function(_w2,_w3){var _w4=B(_vC(_w2,E(_w3)));return new T2(0,_w4.a,_w4.b);},_w5=function(_w6,_w7){var _w8=B(_vC(_w6,_w7)),_w9=_w8.a,_wa=E(_w8.b),_wb=new T(function(){var _wc=B(_rA(B(_ry(_w6))));if(_wa>=0){return B(A3(_6I,_wc,_w9,new T(function(){return B(A2(_7z,_wc,_1M));})));}else{return B(A3(_7x,_wc,_w9,new T(function(){return B(A2(_7z,_wc,_1M));})));}}),_wd=function(_we){var _wf=_we-0.5;return (_wf>=0)?(E(_wf)==0)?(!B(_uZ(_w6,_w9)))?E(_wb):E(_w9):E(_wb):E(_w9);},_wg=E(_wa);if(!_wg){return new F(function(){return _wd(0);});}else{if(_wg<=0){var _wh= -_wg-0.5;return (_wh>=0)?(E(_wh)==0)?(!B(_uZ(_w6,_w9)))?E(_wb):E(_w9):E(_wb):E(_w9);}else{return new F(function(){return _wd(_wg);});}}},_wi=function(_wj,_wk){return new F(function(){return _w5(_wj,E(_wk));});},_wl=function(_wm,_wn){return E(B(_vC(_wm,E(_wn))).a);},_wo={_:0,a:_rx,b:_is,c:_w1,d:_wl,e:_wi,f:_vP,g:_vV},_wp=new T1(0,1),_wq=function(_wr,_ws){var _wt=E(_wr);return new T2(0,_wt,new T(function(){var _wu=B(_wq(B(_3b(_wt,_ws)),_ws));return new T2(1,_wu.a,_wu.b);}));},_wv=function(_ww){var _wx=B(_wq(_ww,_wp));return new T2(1,_wx.a,_wx.b);},_wy=function(_wz,_wA){var _wB=B(_wq(_wz,new T(function(){return B(_5w(_wA,_wz));})));return new T2(1,_wB.a,_wB.b);},_wC=new T1(0,0),_wD=function(_wE,_wF){var _wG=E(_wE);if(!_wG._){var _wH=_wG.a,_wI=E(_wF);return (_wI._==0)?_wH>=_wI.a:I_compareInt(_wI.a,_wH)<=0;}else{var _wJ=_wG.a,_wK=E(_wF);return (_wK._==0)?I_compareInt(_wJ,_wK.a)>=0:I_compare(_wJ,_wK.a)>=0;}},_wL=function(_wM,_wN,_wO){if(!B(_wD(_wN,_wC))){var _wP=function(_wQ){return (!B(_3N(_wQ,_wO)))?new T2(1,_wQ,new T(function(){return B(_wP(B(_3b(_wQ,_wN))));})):__Z;};return new F(function(){return _wP(_wM);});}else{var _wR=function(_wS){return (!B(_3E(_wS,_wO)))?new T2(1,_wS,new T(function(){return B(_wR(B(_3b(_wS,_wN))));})):__Z;};return new F(function(){return _wR(_wM);});}},_wT=function(_wU,_wV,_wW){return new F(function(){return _wL(_wU,B(_5w(_wV,_wU)),_wW);});},_wX=function(_wY,_wZ){return new F(function(){return _wL(_wY,_wp,_wZ);});},_x0=function(_x1){return new F(function(){return _38(_x1);});},_x2=function(_x3){return new F(function(){return _5w(_x3,_wp);});},_x4=function(_x5){return new F(function(){return _3b(_x5,_wp);});},_x6=function(_x7){return new F(function(){return _qx(E(_x7));});},_x8={_:0,a:_x4,b:_x2,c:_x6,d:_x0,e:_wv,f:_wy,g:_wX,h:_wT},_x9=function(_xa,_xb){while(1){var _xc=E(_xa);if(!_xc._){var _xd=E(_xc.a);if(_xd==(-2147483648)){_xa=new T1(1,I_fromInt(-2147483648));continue;}else{var _xe=E(_xb);if(!_xe._){return new T1(0,B(_st(_xd,_xe.a)));}else{_xa=new T1(1,I_fromInt(_xd));_xb=_xe;continue;}}}else{var _xf=_xc.a,_xg=E(_xb);return (_xg._==0)?new T1(1,I_div(_xf,I_fromInt(_xg.a))):new T1(1,I_div(_xf,_xg.a));}}},_xh=function(_xi,_xj){if(!B(_30(_xj,_uW))){return new F(function(){return _x9(_xi,_xj);});}else{return E(_2V);}},_xk=function(_xl,_xm){while(1){var _xn=E(_xl);if(!_xn._){var _xo=E(_xn.a);if(_xo==(-2147483648)){_xl=new T1(1,I_fromInt(-2147483648));continue;}else{var _xp=E(_xm);if(!_xp._){var _xq=_xp.a;return new T2(0,new T1(0,B(_st(_xo,_xq))),new T1(0,B(_sZ(_xo,_xq))));}else{_xl=new T1(1,I_fromInt(_xo));_xm=_xp;continue;}}}else{var _xr=E(_xm);if(!_xr._){_xl=_xn;_xm=new T1(1,I_fromInt(_xr.a));continue;}else{var _xs=I_divMod(_xn.a,_xr.a);return new T2(0,new T1(1,_xs.a),new T1(1,_xs.b));}}}},_xt=function(_xu,_xv){if(!B(_30(_xv,_uW))){var _xw=B(_xk(_xu,_xv));return new T2(0,_xw.a,_xw.b);}else{return E(_2V);}},_xx=function(_xy,_xz){while(1){var _xA=E(_xy);if(!_xA._){var _xB=E(_xA.a);if(_xB==(-2147483648)){_xy=new T1(1,I_fromInt(-2147483648));continue;}else{var _xC=E(_xz);if(!_xC._){return new T1(0,B(_sZ(_xB,_xC.a)));}else{_xy=new T1(1,I_fromInt(_xB));_xz=_xC;continue;}}}else{var _xD=_xA.a,_xE=E(_xz);return (_xE._==0)?new T1(1,I_mod(_xD,I_fromInt(_xE.a))):new T1(1,I_mod(_xD,_xE.a));}}},_xF=function(_xG,_xH){if(!B(_30(_xH,_uW))){return new F(function(){return _xx(_xG,_xH);});}else{return E(_2V);}},_xI=function(_xJ,_xK){while(1){var _xL=E(_xJ);if(!_xL._){var _xM=E(_xL.a);if(_xM==(-2147483648)){_xJ=new T1(1,I_fromInt(-2147483648));continue;}else{var _xN=E(_xK);if(!_xN._){return new T1(0,quot(_xM,_xN.a));}else{_xJ=new T1(1,I_fromInt(_xM));_xK=_xN;continue;}}}else{var _xO=_xL.a,_xP=E(_xK);return (_xP._==0)?new T1(0,I_toInt(I_quot(_xO,I_fromInt(_xP.a)))):new T1(1,I_quot(_xO,_xP.a));}}},_xQ=function(_xR,_xS){if(!B(_30(_xS,_uW))){return new F(function(){return _xI(_xR,_xS);});}else{return E(_2V);}},_xT=function(_xU,_xV){if(!B(_30(_xV,_uW))){var _xW=B(_3k(_xU,_xV));return new T2(0,_xW.a,_xW.b);}else{return E(_2V);}},_xX=function(_xY,_xZ){while(1){var _y0=E(_xY);if(!_y0._){var _y1=E(_y0.a);if(_y1==(-2147483648)){_xY=new T1(1,I_fromInt(-2147483648));continue;}else{var _y2=E(_xZ);if(!_y2._){return new T1(0,_y1%_y2.a);}else{_xY=new T1(1,I_fromInt(_y1));_xZ=_y2;continue;}}}else{var _y3=_y0.a,_y4=E(_xZ);return (_y4._==0)?new T1(1,I_rem(_y3,I_fromInt(_y4.a))):new T1(1,I_rem(_y3,_y4.a));}}},_y5=function(_y6,_y7){if(!B(_30(_y7,_uW))){return new F(function(){return _xX(_y6,_y7);});}else{return E(_2V);}},_y8=function(_y9){return E(_y9);},_ya=function(_yb){return E(_yb);},_yc=function(_yd){var _ye=E(_yd);if(!_ye._){var _yf=E(_ye.a);return (_yf==(-2147483648))?E(_6a):(_yf<0)?new T1(0, -_yf):E(_ye);}else{var _yg=_ye.a;return (I_compareInt(_yg,0)>=0)?E(_ye):new T1(1,I_negate(_yg));}},_yh=new T1(0,0),_yi=new T1(0,-1),_yj=function(_yk){var _yl=E(_yk);if(!_yl._){var _ym=_yl.a;return (_ym>=0)?(E(_ym)==0)?E(_yh):E(_3M):E(_yi);}else{var _yn=I_compareInt(_yl.a,0);return (_yn<=0)?(E(_yn)==0)?E(_yh):E(_yi):E(_3M);}},_yo={_:0,a:_3b,b:_5w,c:_uw,d:_6b,e:_yc,f:_yj,g:_ya},_yp=function(_yq,_yr){var _ys=E(_yq);if(!_ys._){var _yt=_ys.a,_yu=E(_yr);return (_yu._==0)?_yt!=_yu.a:(I_compareInt(_yu.a,_yt)==0)?false:true;}else{var _yv=_ys.a,_yw=E(_yr);return (_yw._==0)?(I_compareInt(_yv,_yw.a)==0)?false:true:(I_compare(_yv,_yw.a)==0)?false:true;}},_yx=new T2(0,_30,_yp),_yy=function(_yz,_yA){return (!B(_5h(_yz,_yA)))?E(_yz):E(_yA);},_yB=function(_yC,_yD){return (!B(_5h(_yC,_yD)))?E(_yD):E(_yC);},_yE={_:0,a:_yx,b:_1N,c:_3N,d:_5h,e:_3E,f:_wD,g:_yy,h:_yB},_yF=function(_yG){return new T2(0,E(_yG),E(_mn));},_yH=new T3(0,_yo,_yE,_yF),_yI={_:0,a:_yH,b:_x8,c:_xQ,d:_y5,e:_xh,f:_xF,g:_xT,h:_xt,i:_y8},_yJ=function(_yK){return E(E(_yK).b);},_yL=function(_yM){return E(E(_yM).g);},_yN=new T1(0,1),_yO=function(_yP,_yQ,_yR){var _yS=B(_yJ(_yP)),_yT=B(_7j(_yS)),_yU=new T(function(){var _yV=new T(function(){var _yW=new T(function(){var _yX=new T(function(){return B(A3(_yL,_yP,_yI,new T(function(){return B(A3(_9a,_yS,_yQ,_yR));})));});return B(A2(_7z,_yT,_yX));}),_yY=new T(function(){return B(A2(_6K,_yT,new T(function(){return B(A2(_7z,_yT,_yN));})));});return B(A3(_7l,_yT,_yY,_yW));});return B(A3(_7l,_yT,_yV,_yR));});return new F(function(){return A3(_6I,_yT,_yQ,_yU);});},_yZ=1.5707963267948966,_z0=function(_z1){return 0.2/Math.cos(B(_yO(_wo,_z1,_yZ))-0.7853981633974483);},_z2=1,_z3=new T(function(){var _z4=B(_p7(_z0,1.2,_qq,_qq,_z2,_qt,_qq,_qq,_qq,_qq,_qq,_z2,_qq));return {_:0,a:E(_z4.a),b:E(_qr),c:E(_hq),d:E(_z4.d),e:E(_z4.e),f:E(_z4.f),g:E(_z4.g),h:_z4.h,i:_z4.i};}),_z5=0,_z6=0.3,_z7=function(_z8){return E(_z6);},_z9=new T(function(){var _za=B(_p7(_z7,1.2,_z2,_qq,_z2,_qq,_qq,_qq,_qq,_qq,_qq,_z2,_qq));return {_:0,a:E(_za.a),b:E(_za.b),c:E(_za.c),d:E(_za.d),e:E(_za.e),f:E(_za.f),g:E(_za.g),h:_za.h,i:_za.i};}),_zb=new T(function(){var _zc=B(_p7(_z7,1.2,_z2,_z2,_qq,_qq,_qq,_qq,_qq,_qq,_qq,_z2,_qq));return {_:0,a:E(_zc.a),b:E(_zc.b),c:E(_zc.c),d:E(_zc.d),e:E(_zc.e),f:E(_zc.f),g:E(_zc.g),h:_zc.h,i:_zc.i};}),_zd=function(_ze){return 0.3/Math.cos(B(_yO(_wo,_ze,_yZ))-0.7853981633974483);},_zf=new T(function(){var _zg=B(_p7(_zd,1.2,_qq,_z2,_z2,_qq,_qq,_qq,_qq,_qq,_qq,_z2,_qq));return {_:0,a:E(_zg.a),b:E(_zg.b),c:E(_zg.c),d:E(_zg.d),e:E(_zg.e),f:E(_zg.f),g:E(_zg.g),h:_zg.h,i:_zg.i};}),_zh=new T2(1,_zf,_o),_zi=new T2(1,_zb,_zh),_zj=new T2(1,_z9,_zi),_zk=new T2(1,_z3,_zj),_zl=new T(function(){return B(unCStr("Negative range size"));}),_zm=new T(function(){return B(err(_zl));}),_zn=function(_){var _zo=B(_hh(_zk,0))-1|0,_zp=function(_zq){if(_zq>=0){var _zr=newArr(_zq,_hn),_zs=_zr,_zt=E(_zq);if(!_zt){return new T4(0,E(_z5),E(_zo),0,_zs);}else{var _zu=function(_zv,_zw,_){while(1){var _zx=E(_zv);if(!_zx._){return E(_);}else{var _=_zs[_zw]=_zx.a;if(_zw!=(_zt-1|0)){var _zy=_zw+1|0;_zv=_zx.b;_zw=_zy;continue;}else{return E(_);}}}},_=B((function(_zz,_zA,_zB,_){var _=_zs[_zB]=_zz;if(_zB!=(_zt-1|0)){return new F(function(){return _zu(_zA,_zB+1|0,_);});}else{return E(_);}})(_z3,_zj,0,_));return new T4(0,E(_z5),E(_zo),_zt,_zs);}}else{return E(_zm);}};if(0>_zo){return new F(function(){return _zp(0);});}else{return new F(function(){return _zp(_zo+1|0);});}},_zC=function(_zD){var _zE=B(A1(_zD,_));return E(_zE);},_zF=new T(function(){return B(_zC(_zn));}),_zG="outline",_zH="polygon",_zI=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_zJ=new T(function(){return B(err(_zI));}),_zK=new T(function(){return eval("__strict(drawObjects)");}),_zL=new T(function(){return eval("__strict(draw)");}),_zM=function(_zN,_zO){var _zP=jsShowI(_zN);return new F(function(){return _f(fromJSStr(_zP),_zO);});},_zQ=function(_zR,_zS,_zT){if(_zS>=0){return new F(function(){return _zM(_zS,_zT);});}else{if(_zR<=6){return new F(function(){return _zM(_zS,_zT);});}else{return new T2(1,_71,new T(function(){var _zU=jsShowI(_zS);return B(_f(fromJSStr(_zU),new T2(1,_70,_zT)));}));}}},_zV=new T(function(){return B(unCStr(")"));}),_zW=function(_zX,_zY){var _zZ=new T(function(){var _A0=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_zQ(0,_zX,_o)),_zV));})));},1);return B(_f(B(_zQ(0,_zY,_o)),_A0));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_zZ)));});},_A1=new T2(1,_jF,_o),_A2=function(_A3){return E(_A3);},_A4=function(_A5){return E(_A5);},_A6=function(_A7,_A8){return E(_A8);},_A9=function(_Aa,_Ab){return E(_Aa);},_Ac=function(_Ad){return E(_Ad);},_Ae=new T2(0,_Ac,_A9),_Af=function(_Ag,_Ah){return E(_Ag);},_Ai=new T5(0,_Ae,_A4,_A2,_A6,_Af),_Aj="flipped2",_Ak="flipped1",_Al="c1y",_Am="c1x",_An="w2z",_Ao="w2y",_Ap="w2x",_Aq="w1z",_Ar="w1y",_As="w1x",_At="d2z",_Au="d2y",_Av="d2x",_Aw="d1z",_Ax="d1y",_Ay="d1x",_Az="c2y",_AA="c2x",_AB=function(_AC,_){var _AD=__get(_AC,E(_As)),_AE=__get(_AC,E(_Ar)),_AF=__get(_AC,E(_Aq)),_AG=__get(_AC,E(_Ap)),_AH=__get(_AC,E(_Ao)),_AI=__get(_AC,E(_An)),_AJ=__get(_AC,E(_Am)),_AK=__get(_AC,E(_Al)),_AL=__get(_AC,E(_AA)),_AM=__get(_AC,E(_Az)),_AN=__get(_AC,E(_Ay)),_AO=__get(_AC,E(_Ax)),_AP=__get(_AC,E(_Aw)),_AQ=__get(_AC,E(_Av)),_AR=__get(_AC,E(_Au)),_AS=__get(_AC,E(_At)),_AT=__get(_AC,E(_Ak)),_AU=__get(_AC,E(_Aj));return {_:0,a:E(new T3(0,E(_AD),E(_AE),E(_AF))),b:E(new T3(0,E(_AG),E(_AH),E(_AI))),c:E(new T2(0,E(_AJ),E(_AK))),d:E(new T2(0,E(_AL),E(_AM))),e:E(new T3(0,E(_AN),E(_AO),E(_AP))),f:E(new T3(0,E(_AQ),E(_AR),E(_AS))),g:E(_AT),h:E(_AU)};},_AV=function(_AW,_){var _AX=E(_AW);if(!_AX._){return _o;}else{var _AY=B(_AB(E(_AX.a),_)),_AZ=B(_AV(_AX.b,_));return new T2(1,_AY,_AZ);}},_B0=function(_B1){var _B2=E(_B1);return (E(_B2.b)-E(_B2.a)|0)+1|0;},_B3=function(_B4,_B5){var _B6=E(_B4),_B7=E(_B5);return (E(_B6.a)>_B7)?false:_B7<=E(_B6.b);},_B8=function(_B9){return new F(function(){return _zQ(0,E(_B9),_o);});},_Ba=function(_Bb,_Bc,_Bd){return new F(function(){return _zQ(E(_Bb),E(_Bc),_Bd);});},_Be=function(_Bf,_Bg){return new F(function(){return _zQ(0,E(_Bf),_Bg);});},_Bh=function(_Bi,_Bj){return new F(function(){return _2B(_Be,_Bi,_Bj);});},_Bk=new T3(0,_Ba,_B8,_Bh),_Bl=0,_Bm=function(_Bn,_Bo,_Bp){return new F(function(){return A1(_Bn,new T2(1,_2y,new T(function(){return B(A1(_Bo,_Bp));})));});},_Bq=new T(function(){return B(unCStr("foldr1"));}),_Br=new T(function(){return B(_lN(_Bq));}),_Bs=function(_Bt,_Bu){var _Bv=E(_Bu);if(!_Bv._){return E(_Br);}else{var _Bw=_Bv.a,_Bx=E(_Bv.b);if(!_Bx._){return E(_Bw);}else{return new F(function(){return A2(_Bt,_Bw,new T(function(){return B(_Bs(_Bt,_Bx));}));});}}},_By=new T(function(){return B(unCStr(" out of range "));}),_Bz=new T(function(){return B(unCStr("}.index: Index "));}),_BA=new T(function(){return B(unCStr("Ix{"));}),_BB=new T2(1,_70,_o),_BC=new T2(1,_70,_BB),_BD=0,_BE=function(_BF){return E(E(_BF).a);},_BG=function(_BH,_BI,_BJ,_BK,_BL){var _BM=new T(function(){var _BN=new T(function(){var _BO=new T(function(){var _BP=new T(function(){var _BQ=new T(function(){return B(A3(_Bs,_Bm,new T2(1,new T(function(){return B(A3(_BE,_BJ,_BD,_BK));}),new T2(1,new T(function(){return B(A3(_BE,_BJ,_BD,_BL));}),_o)),_BC));});return B(_f(_By,new T2(1,_71,new T2(1,_71,_BQ))));});return B(A(_BE,[_BJ,_Bl,_BI,new T2(1,_70,_BP)]));});return B(_f(_Bz,new T2(1,_71,_BO)));},1);return B(_f(_BH,_BN));},1);return new F(function(){return err(B(_f(_BA,_BM)));});},_BR=function(_BS,_BT,_BU,_BV,_BW){return new F(function(){return _BG(_BS,_BT,_BW,_BU,_BV);});},_BX=function(_BY,_BZ,_C0,_C1){var _C2=E(_C0);return new F(function(){return _BR(_BY,_BZ,_C2.a,_C2.b,_C1);});},_C3=function(_C4,_C5,_C6,_C7){return new F(function(){return _BX(_C7,_C6,_C5,_C4);});},_C8=new T(function(){return B(unCStr("Int"));}),_C9=function(_Ca,_Cb){return new F(function(){return _C3(_Bk,_Cb,_Ca,_C8);});},_Cc=function(_Cd,_Ce){var _Cf=E(_Cd),_Cg=E(_Cf.a),_Ch=E(_Ce);if(_Cg>_Ch){return new F(function(){return _C9(_Ch,_Cf);});}else{if(_Ch>E(_Cf.b)){return new F(function(){return _C9(_Ch,_Cf);});}else{return _Ch-_Cg|0;}}},_Ci=function(_Cj){var _Ck=E(_Cj);return new F(function(){return _sd(_Ck.a,_Ck.b);});},_Cl=function(_Cm){var _Cn=E(_Cm),_Co=E(_Cn.a),_Cp=E(_Cn.b);return (_Co>_Cp)?E(_Bl):(_Cp-_Co|0)+1|0;},_Cq=function(_Cr,_Cs){return new F(function(){return _tC(_Cs,E(_Cr).a);});},_Ct={_:0,a:_us,b:_Ci,c:_Cc,d:_Cq,e:_B3,f:_Cl,g:_B0},_Cu=function(_Cv,_Cw,_){while(1){var _Cx=B((function(_Cy,_Cz,_){var _CA=E(_Cy);if(!_CA._){return new T2(0,_jF,_Cz);}else{var _CB=B(A2(_CA.a,_Cz,_));_Cv=_CA.b;_Cw=new T(function(){return E(E(_CB).b);});return __continue;}})(_Cv,_Cw,_));if(_Cx!=__continue){return _Cx;}}},_CC=function(_CD,_CE){return new T2(1,_CD,_CE);},_CF=function(_CG,_CH){var _CI=E(_CH);return new T2(0,_CI.a,_CI.b);},_CJ=function(_CK){return E(E(_CK).f);},_CL=function(_CM,_CN,_CO){var _CP=E(_CN),_CQ=_CP.a,_CR=_CP.b,_CS=function(_){var _CT=B(A2(_CJ,_CM,_CP));if(_CT>=0){var _CU=newArr(_CT,_hn),_CV=_CU,_CW=E(_CT);if(!_CW){return new T(function(){return new T4(0,E(_CQ),E(_CR),0,_CV);});}else{var _CX=function(_CY,_CZ,_){while(1){var _D0=E(_CY);if(!_D0._){return E(_);}else{var _=_CV[_CZ]=_D0.a;if(_CZ!=(_CW-1|0)){var _D1=_CZ+1|0;_CY=_D0.b;_CZ=_D1;continue;}else{return E(_);}}}},_=B(_CX(_CO,0,_));return new T(function(){return new T4(0,E(_CQ),E(_CR),_CW,_CV);});}}else{return E(_zm);}};return new F(function(){return _zC(_CS);});},_D2=function(_D3,_D4,_D5,_D6){var _D7=new T(function(){var _D8=E(_D6),_D9=_D8.c-1|0,_Da=new T(function(){return B(A2(_cW,_D4,_o));});if(0<=_D9){var _Db=new T(function(){return B(_96(_D4));}),_Dc=function(_Dd){var _De=new T(function(){var _Df=new T(function(){return B(A1(_D5,new T(function(){return E(_D8.d[_Dd]);})));});return B(A3(_9e,_Db,_CC,_Df));});return new F(function(){return A3(_9c,_D4,_De,new T(function(){if(_Dd!=_D9){return B(_Dc(_Dd+1|0));}else{return E(_Da);}}));});};return B(_Dc(0));}else{return E(_Da);}}),_Dg=new T(function(){return B(_CF(_D3,_D6));});return new F(function(){return A3(_9e,B(_96(_D4)),function(_Dh){return new F(function(){return _CL(_D3,_Dg,_Dh);});},_D7);});},_Di=function(_Dj,_Dk,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr){var _Ds=B(_7l(_Dj));return new T2(0,new T3(0,E(B(A1(B(A1(_Ds,_Dk)),_Do))),E(B(A1(B(A1(_Ds,_Dl)),_Dp))),E(B(A1(B(A1(_Ds,_Dm)),_Dq)))),B(A1(B(A1(_Ds,_Dn)),_Dr)));},_Dt=function(_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC){var _DD=B(_6I(_Du));return new T2(0,new T3(0,E(B(A1(B(A1(_DD,_Dv)),_Dz))),E(B(A1(B(A1(_DD,_Dw)),_DA))),E(B(A1(B(A1(_DD,_Dx)),_DB)))),B(A1(B(A1(_DD,_Dy)),_DC)));},_DE=1.0e-2,_DF=function(_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO,_DP,_DQ,_DR,_DS,_DT,_DU,_DV,_DW){var _DX=B(_Di(_io,_DN,_DO,_DP,_DQ,_DE,_DE,_DE,_DE)),_DY=E(_DX.a),_DZ=B(_Dt(_io,_DJ,_DK,_DL,_DM,_DY.a,_DY.b,_DY.c,_DX.b)),_E0=E(_DZ.a);return new F(function(){return _oo(_DG,_DH,_DI,_E0.a,_E0.b,_E0.c,_DZ.b,_DN,_DO,_DP,_DQ,_DR,_DS,_DT,_DU,_DV,_DW);});},_E1=function(_E2){var _E3=E(_E2),_E4=E(_E3.d),_E5=E(_E4.a),_E6=E(_E3.e),_E7=E(_E6.a),_E8=E(_E3.f),_E9=B(_DF(_E3.a,_E3.b,_E3.c,_E5.a,_E5.b,_E5.c,_E4.b,_E7.a,_E7.b,_E7.c,_E6.b,_E8.a,_E8.b,_E8.c,_E3.g,_E3.h,_E3.i));return {_:0,a:E(_E9.a),b:E(_E9.b),c:E(_E9.c),d:E(_E9.d),e:E(_E9.e),f:E(_E9.f),g:E(_E9.g),h:_E9.h,i:_E9.i};},_Ea=function(_Eb,_Ec,_Ed,_Ee,_Ef,_Eg,_Eh,_Ei,_Ej){var _Ek=B(_7j(B(_7h(_Eb))));return new F(function(){return A3(_6I,_Ek,new T(function(){return B(_7n(_Eb,_Ec,_Ed,_Ee,_Eg,_Eh,_Ei));}),new T(function(){return B(A3(_7l,_Ek,_Ef,_Ej));}));});},_El=new T(function(){return B(unCStr("base"));}),_Em=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_En=new T(function(){return B(unCStr("IOException"));}),_Eo=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_El,_Em,_En),_Ep=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Eo,_o,_o),_Eq=function(_Er){return E(_Ep);},_Es=function(_Et){var _Eu=E(_Et);return new F(function(){return _28(B(_26(_Eu.a)),_Eq,_Eu.b);});},_Ev=new T(function(){return B(unCStr(": "));}),_Ew=new T(function(){return B(unCStr(")"));}),_Ex=new T(function(){return B(unCStr(" ("));}),_Ey=new T(function(){return B(unCStr("interrupted"));}),_Ez=new T(function(){return B(unCStr("system error"));}),_EA=new T(function(){return B(unCStr("unsatisified constraints"));}),_EB=new T(function(){return B(unCStr("user error"));}),_EC=new T(function(){return B(unCStr("permission denied"));}),_ED=new T(function(){return B(unCStr("illegal operation"));}),_EE=new T(function(){return B(unCStr("end of file"));}),_EF=new T(function(){return B(unCStr("resource exhausted"));}),_EG=new T(function(){return B(unCStr("resource busy"));}),_EH=new T(function(){return B(unCStr("does not exist"));}),_EI=new T(function(){return B(unCStr("already exists"));}),_EJ=new T(function(){return B(unCStr("resource vanished"));}),_EK=new T(function(){return B(unCStr("timeout"));}),_EL=new T(function(){return B(unCStr("unsupported operation"));}),_EM=new T(function(){return B(unCStr("hardware fault"));}),_EN=new T(function(){return B(unCStr("inappropriate type"));}),_EO=new T(function(){return B(unCStr("invalid argument"));}),_EP=new T(function(){return B(unCStr("failed"));}),_EQ=new T(function(){return B(unCStr("protocol error"));}),_ER=function(_ES,_ET){switch(E(_ES)){case 0:return new F(function(){return _f(_EI,_ET);});break;case 1:return new F(function(){return _f(_EH,_ET);});break;case 2:return new F(function(){return _f(_EG,_ET);});break;case 3:return new F(function(){return _f(_EF,_ET);});break;case 4:return new F(function(){return _f(_EE,_ET);});break;case 5:return new F(function(){return _f(_ED,_ET);});break;case 6:return new F(function(){return _f(_EC,_ET);});break;case 7:return new F(function(){return _f(_EB,_ET);});break;case 8:return new F(function(){return _f(_EA,_ET);});break;case 9:return new F(function(){return _f(_Ez,_ET);});break;case 10:return new F(function(){return _f(_EQ,_ET);});break;case 11:return new F(function(){return _f(_EP,_ET);});break;case 12:return new F(function(){return _f(_EO,_ET);});break;case 13:return new F(function(){return _f(_EN,_ET);});break;case 14:return new F(function(){return _f(_EM,_ET);});break;case 15:return new F(function(){return _f(_EL,_ET);});break;case 16:return new F(function(){return _f(_EK,_ET);});break;case 17:return new F(function(){return _f(_EJ,_ET);});break;default:return new F(function(){return _f(_Ey,_ET);});}},_EU=new T(function(){return B(unCStr("}"));}),_EV=new T(function(){return B(unCStr("{handle: "));}),_EW=function(_EX,_EY,_EZ,_F0,_F1,_F2){var _F3=new T(function(){var _F4=new T(function(){var _F5=new T(function(){var _F6=E(_F0);if(!_F6._){return E(_F2);}else{var _F7=new T(function(){return B(_f(_F6,new T(function(){return B(_f(_Ew,_F2));},1)));},1);return B(_f(_Ex,_F7));}},1);return B(_ER(_EY,_F5));}),_F8=E(_EZ);if(!_F8._){return E(_F4);}else{return B(_f(_F8,new T(function(){return B(_f(_Ev,_F4));},1)));}}),_F9=E(_F1);if(!_F9._){var _Fa=E(_EX);if(!_Fa._){return E(_F3);}else{var _Fb=E(_Fa.a);if(!_Fb._){var _Fc=new T(function(){var _Fd=new T(function(){return B(_f(_EU,new T(function(){return B(_f(_Ev,_F3));},1)));},1);return B(_f(_Fb.a,_Fd));},1);return new F(function(){return _f(_EV,_Fc);});}else{var _Fe=new T(function(){var _Ff=new T(function(){return B(_f(_EU,new T(function(){return B(_f(_Ev,_F3));},1)));},1);return B(_f(_Fb.a,_Ff));},1);return new F(function(){return _f(_EV,_Fe);});}}}else{return new F(function(){return _f(_F9.a,new T(function(){return B(_f(_Ev,_F3));},1));});}},_Fg=function(_Fh){var _Fi=E(_Fh);return new F(function(){return _EW(_Fi.a,_Fi.b,_Fi.c,_Fi.d,_Fi.f,_o);});},_Fj=function(_Fk,_Fl,_Fm){var _Fn=E(_Fl);return new F(function(){return _EW(_Fn.a,_Fn.b,_Fn.c,_Fn.d,_Fn.f,_Fm);});},_Fo=function(_Fp,_Fq){var _Fr=E(_Fp);return new F(function(){return _EW(_Fr.a,_Fr.b,_Fr.c,_Fr.d,_Fr.f,_Fq);});},_Fs=function(_Ft,_Fu){return new F(function(){return _2B(_Fo,_Ft,_Fu);});},_Fv=new T3(0,_Fj,_Fg,_Fs),_Fw=new T(function(){return new T5(0,_Eq,_Fv,_Fx,_Es,_Fg);}),_Fx=function(_Fy){return new T2(0,_Fw,_Fy);},_Fz=__Z,_FA=7,_FB=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:85:3-9"));}),_FC=new T6(0,_Fz,_FA,_o,_FB,_Fz,_Fz),_FD=new T(function(){return B(_Fx(_FC));}),_FE=function(_){return new F(function(){return die(_FD);});},_FF=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:84:3-9"));}),_FG=new T6(0,_Fz,_FA,_o,_FF,_Fz,_Fz),_FH=new T(function(){return B(_Fx(_FG));}),_FI=function(_){return new F(function(){return die(_FH);});},_FJ=function(_FK,_){return new T2(0,_o,_FK);},_FL=1,_FM=new T(function(){return B(unCStr(")"));}),_FN=function(_FO,_FP){var _FQ=new T(function(){var _FR=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_zQ(0,_FO,_o)),_FM));})));},1);return B(_f(B(_zQ(0,_FP,_o)),_FR));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_FQ)));});},_FS=function(_FT,_FU){var _FV=new T(function(){var _FW=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_zQ(0,_FU,_o)),_FM));})));},1);return B(_f(B(_zQ(0,_FT,_o)),_FW));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_FV)));});},_FX=0.6,_FY=function(_FZ){var _G0=E(_FZ);if(!_G0._){return E(_FJ);}else{var _G1=new T(function(){return B(_FY(_G0.b));}),_G2=function(_G3){var _G4=E(_G3);if(!_G4._){return E(_G1);}else{var _G5=_G4.a,_G6=new T(function(){return B(_G2(_G4.b));}),_G7=new T(function(){return 0.1*E(E(_G5).e)/1.0e-2;}),_G8=new T(function(){var _G9=E(_G5);if(_G9.a!=_G9.b){return E(_FL);}else{return E(_FX);}}),_Ga=function(_Gb,_){var _Gc=E(_Gb),_Gd=_Gc.c,_Ge=_Gc.d,_Gf=E(_Gc.a),_Gg=E(_Gc.b),_Gh=E(_G5),_Gi=_Gh.a,_Gj=_Gh.b,_Gk=E(_Gh.c),_Gl=_Gk.b,_Gm=E(_Gk.a),_Gn=_Gm.a,_Go=_Gm.b,_Gp=_Gm.c,_Gq=E(_Gh.d),_Gr=_Gq.b,_Gs=E(_Gq.a),_Gt=_Gs.a,_Gu=_Gs.b,_Gv=_Gs.c;if(_Gf>_Gi){return new F(function(){return _FI(_);});}else{if(_Gi>_Gg){return new F(function(){return _FI(_);});}else{if(_Gf>_Gj){return new F(function(){return _FE(_);});}else{if(_Gj>_Gg){return new F(function(){return _FE(_);});}else{var _Gw=_Gi-_Gf|0;if(0>_Gw){return new F(function(){return _FN(_Gd,_Gw);});}else{if(_Gw>=_Gd){return new F(function(){return _FN(_Gd,_Gw);});}else{var _Gx=E(_Ge[_Gw]),_Gy=E(_Gx.c),_Gz=_Gy.b,_GA=E(_Gy.a),_GB=_GA.a,_GC=_GA.b,_GD=_GA.c,_GE=E(_Gx.e),_GF=E(_GE.a),_GG=B(_Di(_io,_Gn,_Go,_Gp,_Gl,_GB,_GC,_GD,_Gz)),_GH=E(_GG.a),_GI=B(_Di(_io,_GH.a,_GH.b,_GH.c,_GG.b,_Gn,_Go,_Gp,_Gl)),_GJ=E(_GI.a),_GK=_Gj-_Gf|0;if(0>_GK){return new F(function(){return _FS(_GK,_Gd);});}else{if(_GK>=_Gd){return new F(function(){return _FS(_GK,_Gd);});}else{var _GL=E(_Ge[_GK]),_GM=E(_GL.c),_GN=_GM.b,_GO=E(_GM.a),_GP=_GO.a,_GQ=_GO.b,_GR=_GO.c,_GS=E(_GL.e),_GT=E(_GS.a),_GU=B(_Di(_io,_Gt,_Gu,_Gv,_Gr,_GP,_GQ,_GR,_GN)),_GV=E(_GU.a),_GW=B(_Di(_io,_GV.a,_GV.b,_GV.c,_GU.b,_Gt,_Gu,_Gv,_Gr)),_GX=E(_GW.a),_GY=E(_GJ.a)+E(_GJ.b)+E(_GJ.c)+E(_GI.b)+E(_GX.a)+E(_GX.b)+E(_GX.c)+E(_GW.b);if(!_GY){var _GZ=B(A2(_G6,_Gc,_));return new T2(0,new T2(1,_jF,new T(function(){return E(E(_GZ).a);})),new T(function(){return E(E(_GZ).b);}));}else{var _H0=new T(function(){return  -((B(_Ea(_iU,_GF.a,_GF.b,_GF.c,_GE.b,_Gn,_Go,_Gp,_Gl))-B(_Ea(_iU,_GT.a,_GT.b,_GT.c,_GS.b,_Gt,_Gu,_Gv,_Gr))-E(_G7))/_GY);}),_H1=function(_H2,_H3,_H4,_H5,_){var _H6=new T(function(){var _H7=function(_H8,_H9,_Ha,_Hb,_Hc){if(_H8>_Gj){return E(_Hc);}else{if(_Gj>_H9){return E(_Hc);}else{var _Hd=function(_){var _He=newArr(_Ha,_hn),_Hf=_He,_Hg=function(_Hh,_){while(1){if(_Hh!=_Ha){var _=_Hf[_Hh]=_Hb[_Hh],_Hi=_Hh+1|0;_Hh=_Hi;continue;}else{return E(_);}}},_=B(_Hg(0,_)),_Hj=_Gj-_H8|0;if(0>_Hj){return new F(function(){return _FS(_Hj,_Ha);});}else{if(_Hj>=_Ha){return new F(function(){return _FS(_Hj,_Ha);});}else{var _=_Hf[_Hj]=new T(function(){var _Hk=E(_Hb[_Hj]),_Hl=E(_Hk.e),_Hm=E(_Hl.a),_Hn=B(_Di(_io,_GP,_GQ,_GR,_GN,_Gt,_Gu,_Gv,_Gr)),_Ho=E(_Hn.a),_Hp=E(_H0)*E(_G8),_Hq=B(_Di(_io,_Ho.a,_Ho.b,_Ho.c,_Hn.b,_Hp,_Hp,_Hp,_Hp)),_Hr=E(_Hq.a),_Hs=B(_Dt(_io,_Hm.a,_Hm.b,_Hm.c,_Hl.b, -E(_Hr.a), -E(_Hr.b), -E(_Hr.c), -E(_Hq.b)));return {_:0,a:E(_Hk.a),b:E(_Hk.b),c:E(_Hk.c),d:E(_Hk.d),e:E(new T2(0,E(_Hs.a),E(_Hs.b))),f:E(_Hk.f),g:E(_Hk.g),h:_Hk.h,i:_Hk.i};});return new T4(0,E(_H8),E(_H9),_Ha,_Hf);}}};return new F(function(){return _zC(_Hd);});}}};if(_H2>_Gi){return B(_H7(_H2,_H3,_H4,_H5,new T4(0,E(_H2),E(_H3),_H4,_H5)));}else{if(_Gi>_H3){return B(_H7(_H2,_H3,_H4,_H5,new T4(0,E(_H2),E(_H3),_H4,_H5)));}else{var _Ht=function(_){var _Hu=newArr(_H4,_hn),_Hv=_Hu,_Hw=function(_Hx,_){while(1){if(_Hx!=_H4){var _=_Hv[_Hx]=_H5[_Hx],_Hy=_Hx+1|0;_Hx=_Hy;continue;}else{return E(_);}}},_=B(_Hw(0,_)),_Hz=_Gi-_H2|0;if(0>_Hz){return new F(function(){return _FN(_H4,_Hz);});}else{if(_Hz>=_H4){return new F(function(){return _FN(_H4,_Hz);});}else{var _=_Hv[_Hz]=new T(function(){var _HA=E(_H5[_Hz]),_HB=E(_HA.e),_HC=E(_HB.a),_HD=B(_Di(_io,_GB,_GC,_GD,_Gz,_Gn,_Go,_Gp,_Gl)),_HE=E(_HD.a),_HF=E(_H0)*E(_G8),_HG=B(_Di(_io,_HE.a,_HE.b,_HE.c,_HD.b,_HF,_HF,_HF,_HF)),_HH=E(_HG.a),_HI=B(_Dt(_io,_HC.a,_HC.b,_HC.c,_HB.b,_HH.a,_HH.b,_HH.c,_HG.b));return {_:0,a:E(_HA.a),b:E(_HA.b),c:E(_HA.c),d:E(_HA.d),e:E(new T2(0,E(_HI.a),E(_HI.b))),f:E(_HA.f),g:E(_HA.g),h:_HA.h,i:_HA.i};});return new T4(0,E(_H2),E(_H3),_H4,_Hv);}}},_HJ=B(_zC(_Ht));return B(_H7(E(_HJ.a),E(_HJ.b),_HJ.c,_HJ.d,_HJ));}}});return new T2(0,_jF,_H6);};if(!E(_Gh.f)){var _HK=B(_H1(_Gf,_Gg,_Gd,_Ge,_)),_HL=B(A2(_G6,new T(function(){return E(E(_HK).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_HK).a);}),new T(function(){return E(E(_HL).a);})),new T(function(){return E(E(_HL).b);}));}else{if(E(_H0)<0){var _HM=B(A2(_G6,_Gc,_));return new T2(0,new T2(1,_jF,new T(function(){return E(E(_HM).a);})),new T(function(){return E(E(_HM).b);}));}else{var _HN=B(_H1(_Gf,_Gg,_Gd,_Ge,_)),_HO=B(A2(_G6,new T(function(){return E(E(_HN).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_HN).a);}),new T(function(){return E(E(_HO).a);})),new T(function(){return E(E(_HO).b);}));}}}}}}}}}}}};return E(_Ga);}};return new F(function(){return _G2(_G0.a);});}},_HP=function(_,_HQ){var _HR=new T(function(){return B(_FY(E(_HQ).a));}),_HS=function(_HT){var _HU=E(_HT);return (_HU==1)?E(new T2(1,_HR,_o)):new T2(1,_HR,new T(function(){return B(_HS(_HU-1|0));}));},_HV=B(_Cu(B(_HS(5)),new T(function(){return E(E(_HQ).b);}),_)),_HW=new T(function(){return B(_D2(_Ct,_Ai,_E1,new T(function(){return E(E(_HV).b);})));});return new T2(0,_jF,_HW);},_HX=function(_HY,_HZ,_I0,_I1,_I2){var _I3=B(_7j(B(_7h(_HY))));return new F(function(){return A3(_6I,_I3,new T(function(){return B(A3(_7l,_I3,_HZ,_I1));}),new T(function(){return B(A3(_7l,_I3,_I0,_I2));}));});},_I4=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:55:7-13"));}),_I5=new T6(0,_Fz,_FA,_o,_I4,_Fz,_Fz),_I6=new T(function(){return B(_Fx(_I5));}),_I7=function(_){return new F(function(){return die(_I6);});},_I8=false,_I9=true,_Ia=function(_Ib){var _Ic=E(_Ib),_Id=_Ic.b,_Ie=E(_Ic.d),_If=E(_Ic.e),_Ig=E(_If.a),_Ih=E(_Ic.g),_Ii=B(A1(_Id,_Ie.a)),_Ij=B(_l6(_iU,_Ii.a,_Ii.b,_Ii.c,_Ih.a,_Ih.b,_Ih.c));return {_:0,a:E(_Ic.a),b:E(_Id),c:E(_Ic.c),d:E(_Ie),e:E(new T2(0,E(new T3(0,E(_Ig.a)+E(_Ij.a)*1.0e-2,E(_Ig.b)+E(_Ij.b)*1.0e-2,E(_Ig.c)+E(_Ij.c)*1.0e-2)),E(_If.b))),f:E(_Ic.f),g:E(_Ih),h:_Ic.h,i:_Ic.i};},_Ik=new T(function(){return eval("collide");}),_Il=function(_Im){var _In=E(_Im);if(!_In._){return __Z;}else{return new F(function(){return _f(_In.a,new T(function(){return B(_Il(_In.b));},1));});}},_Io=0,_Ip=new T3(0,E(_Io),E(_Io),E(_Io)),_Iq=new T2(0,E(_Ip),E(_Io)),_Ir=new T2(0,_iU,_jt),_Is=new T(function(){return B(_gT(_Ir));}),_It=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:54:7-13"));}),_Iu=new T6(0,_Fz,_FA,_o,_It,_Fz,_Fz),_Iv=new T(function(){return B(_Fx(_Iu));}),_Iw=function(_Ix,_){var _Iy=B(_D2(_Ct,_Ai,_Ia,_Ix)),_Iz=E(_Iy.a),_IA=E(_Iy.b);if(_Iz<=_IA){var _IB=function(_IC,_ID,_){if(_IC<=_IA){var _IE=E(_ID),_IF=function(_IG,_IH,_II,_IJ,_IK,_){if(_IH>_IC){return new F(function(){return die(_Iv);});}else{if(_IC>_II){return new F(function(){return die(_Iv);});}else{if(_IH>_IG){return new F(function(){return _I7(_);});}else{if(_IG>_II){return new F(function(){return _I7(_);});}else{var _IL=_IC-_IH|0;if(0>_IL){return new F(function(){return _FS(_IL,_IJ);});}else{if(_IL>=_IJ){return new F(function(){return _FS(_IL,_IJ);});}else{var _IM=E(_IK[_IL]),_IN=_IG-_IH|0;if(0>_IN){return new F(function(){return _FS(_IN,_IJ);});}else{if(_IN>=_IJ){return new F(function(){return _FS(_IN,_IJ);});}else{var _IO=E(_IK[_IN]),_IP=__app2(E(_Ik),B(_jG(new T2(1,new T2(0,_zH,_IM.h),new T2(1,new T2(0,_zG,_IM.i),_o)))),B(_jG(new T2(1,new T2(0,_zH,_IO.h),new T2(1,new T2(0,_zG,_IO.i),_o))))),_IQ=__arr2lst(0,_IP),_IR=B(_AV(_IQ,_));if(_IG!=_IA){var _IS=B(_IF(_IG+1|0,_IH,_II,_IJ,_IK,_)),_IT=new T(function(){var _IU=new T(function(){return _IC!=_IG;}),_IV=function(_IW){var _IX=E(_IW);if(!_IX._){return __Z;}else{var _IY=_IX.b,_IZ=E(_IX.a),_J0=E(_IZ.b),_J1=E(_IZ.a),_J2=E(_IZ.c),_J3=_J2.a,_J4=_J2.b,_J5=E(_IZ.e),_J6=E(_IZ.d),_J7=_J6.a,_J8=_J6.b,_J9=E(_IZ.f),_Ja=new T(function(){var _Jb=B(_kj(_iU,_J9.a,_J9.b,_J9.c)),_Jc=Math.sqrt(B(_HX(_iU,_J7,_J8,_J7,_J8)));return new T3(0,_Jc*E(_Jb.a),_Jc*E(_Jb.b),_Jc*E(_Jb.c));}),_Jd=new T(function(){var _Je=B(_kj(_iU,_J5.a,_J5.b,_J5.c)),_Jf=Math.sqrt(B(_HX(_iU,_J3,_J4,_J3,_J4)));return new T3(0,_Jf*E(_Je.a),_Jf*E(_Je.b),_Jf*E(_Je.c));}),_Jg=new T(function(){var _Jh=B(A1(_Is,_J0)),_Ji=B(_kj(_iU,_Jh.a,_Jh.b,_Jh.c));return new T3(0,E(_Ji.a),E(_Ji.b),E(_Ji.c));}),_Jj=new T(function(){var _Jk=B(A1(_Is,_J1)),_Jl=B(_kj(_iU,_Jk.a,_Jk.b,_Jk.c));return new T3(0,E(_Jl.a),E(_Jl.b),E(_Jl.c));}),_Jm=E(_J0.a)+ -E(_J1.a),_Jn=E(_J0.b)+ -E(_J1.b),_Jo=E(_J0.c)+ -E(_J1.c),_Jp=new T(function(){return Math.sqrt(B(_7n(_iU,_Jm,_Jn,_Jo,_Jm,_Jn,_Jo)));}),_Jq=new T(function(){var _Jr=1/E(_Jp);return new T3(0,_Jm*_Jr,_Jn*_Jr,_Jo*_Jr);}),_Js=new T(function(){if(!E(_IZ.g)){return E(_Jq);}else{var _Jt=E(_Jq);return new T3(0,-1*E(_Jt.a),-1*E(_Jt.b),-1*E(_Jt.c));}}),_Ju=new T(function(){if(!E(_IZ.h)){return E(_Jq);}else{var _Jv=E(_Jq);return new T3(0,-1*E(_Jv.a),-1*E(_Jv.b),-1*E(_Jv.c));}});return (!E(_IU))?new T2(1,new T(function(){var _Jw=E(_Js),_Jx=E(_Jw.b),_Jy=E(_Jw.c),_Jz=E(_Jw.a),_JA=E(_Jj),_JB=E(_JA.c),_JC=E(_JA.b),_JD=E(_JA.a),_JE=E(_Jd),_JF=E(_JE.c),_JG=E(_JE.b),_JH=E(_JE.a),_JI=_Jx*_JB-_JC*_Jy,_JJ=_Jy*_JD-_JB*_Jz,_JK=_Jz*_JC-_JD*_Jx,_JL=B(_7n(_iU,_JJ*_JF-_JG*_JK,_JK*_JH-_JF*_JI,_JI*_JG-_JH*_JJ,_JD,_JC,_JB));return new T6(0,_IC,_IG,E(new T2(0,E(new T3(0,E(_JI),E(_JJ),E(_JK))),E(_JL))),E(_Iq),_Jp,_I8);}),new T2(1,new T(function(){var _JM=E(_Ju),_JN=E(_JM.b),_JO=E(_JM.c),_JP=E(_JM.a),_JQ=E(_Jg),_JR=E(_JQ.c),_JS=E(_JQ.b),_JT=E(_JQ.a),_JU=E(_Ja),_JV=E(_JU.c),_JW=E(_JU.b),_JX=E(_JU.a),_JY=_JN*_JR-_JS*_JO,_JZ=_JO*_JT-_JR*_JP,_K0=_JP*_JS-_JT*_JN,_K1=B(_7n(_iU,_JZ*_JV-_JW*_K0,_K0*_JX-_JV*_JY,_JY*_JW-_JX*_JZ,_JT,_JS,_JR));return new T6(0,_IC,_IG,E(_Iq),E(new T2(0,E(new T3(0,E(_JY),E(_JZ),E(_K0))),E(_K1))),_Jp,_I8);}),new T(function(){return B(_IV(_IY));}))):new T2(1,new T(function(){var _K2=E(_Js),_K3=E(_K2.b),_K4=E(_K2.c),_K5=E(_K2.a),_K6=E(_Jj),_K7=_K6.a,_K8=_K6.b,_K9=_K6.c,_Ka=B(_l6(_iU,_K5,_K3,_K4,_K7,_K8,_K9)),_Kb=E(_Jd),_Kc=E(_Kb.c),_Kd=E(_Kb.b),_Ke=E(_Kb.a),_Kf=B(_7n(_iU,_K3*_Kc-_Kd*_K4,_K4*_Ke-_Kc*_K5,_K5*_Kd-_Ke*_K3,_K7,_K8,_K9)),_Kg=E(_Ju),_Kh=E(_Kg.b),_Ki=E(_Kg.c),_Kj=E(_Kg.a),_Kk=E(_Jg),_Kl=_Kk.a,_Km=_Kk.b,_Kn=_Kk.c,_Ko=B(_l6(_iU,_Kj,_Kh,_Ki,_Kl,_Km,_Kn)),_Kp=E(_Ja),_Kq=E(_Kp.c),_Kr=E(_Kp.b),_Ks=E(_Kp.a),_Kt=B(_7n(_iU,_Kh*_Kq-_Kr*_Ki,_Ki*_Ks-_Kq*_Kj,_Kj*_Kr-_Ks*_Kh,_Kl,_Km,_Kn));return new T6(0,_IC,_IG,E(new T2(0,E(new T3(0,E(_Ka.a),E(_Ka.b),E(_Ka.c))),E(_Kf))),E(new T2(0,E(new T3(0,E(_Ko.a),E(_Ko.b),E(_Ko.c))),E(_Kt))),_Jp,_I9);}),new T(function(){return B(_IV(_IY));}));}};return B(_IV(_IR));});return new T2(0,new T2(1,_IT,new T(function(){return E(E(_IS).a);})),new T(function(){return E(E(_IS).b);}));}else{var _Ku=new T(function(){var _Kv=new T(function(){return _IC!=_IG;}),_Kw=function(_Kx){var _Ky=E(_Kx);if(!_Ky._){return __Z;}else{var _Kz=_Ky.b,_KA=E(_Ky.a),_KB=E(_KA.b),_KC=E(_KA.a),_KD=E(_KA.c),_KE=_KD.a,_KF=_KD.b,_KG=E(_KA.e),_KH=E(_KA.d),_KI=_KH.a,_KJ=_KH.b,_KK=E(_KA.f),_KL=new T(function(){var _KM=B(_kj(_iU,_KK.a,_KK.b,_KK.c)),_KN=Math.sqrt(B(_HX(_iU,_KI,_KJ,_KI,_KJ)));return new T3(0,_KN*E(_KM.a),_KN*E(_KM.b),_KN*E(_KM.c));}),_KO=new T(function(){var _KP=B(_kj(_iU,_KG.a,_KG.b,_KG.c)),_KQ=Math.sqrt(B(_HX(_iU,_KE,_KF,_KE,_KF)));return new T3(0,_KQ*E(_KP.a),_KQ*E(_KP.b),_KQ*E(_KP.c));}),_KR=new T(function(){var _KS=B(A1(_Is,_KB)),_KT=B(_kj(_iU,_KS.a,_KS.b,_KS.c));return new T3(0,E(_KT.a),E(_KT.b),E(_KT.c));}),_KU=new T(function(){var _KV=B(A1(_Is,_KC)),_KW=B(_kj(_iU,_KV.a,_KV.b,_KV.c));return new T3(0,E(_KW.a),E(_KW.b),E(_KW.c));}),_KX=E(_KB.a)+ -E(_KC.a),_KY=E(_KB.b)+ -E(_KC.b),_KZ=E(_KB.c)+ -E(_KC.c),_L0=new T(function(){return Math.sqrt(B(_7n(_iU,_KX,_KY,_KZ,_KX,_KY,_KZ)));}),_L1=new T(function(){var _L2=1/E(_L0);return new T3(0,_KX*_L2,_KY*_L2,_KZ*_L2);}),_L3=new T(function(){if(!E(_KA.g)){return E(_L1);}else{var _L4=E(_L1);return new T3(0,-1*E(_L4.a),-1*E(_L4.b),-1*E(_L4.c));}}),_L5=new T(function(){if(!E(_KA.h)){return E(_L1);}else{var _L6=E(_L1);return new T3(0,-1*E(_L6.a),-1*E(_L6.b),-1*E(_L6.c));}});return (!E(_Kv))?new T2(1,new T(function(){var _L7=E(_L3),_L8=E(_L7.b),_L9=E(_L7.c),_La=E(_L7.a),_Lb=E(_KU),_Lc=E(_Lb.c),_Ld=E(_Lb.b),_Le=E(_Lb.a),_Lf=E(_KO),_Lg=E(_Lf.c),_Lh=E(_Lf.b),_Li=E(_Lf.a),_Lj=_L8*_Lc-_Ld*_L9,_Lk=_L9*_Le-_Lc*_La,_Ll=_La*_Ld-_Le*_L8,_Lm=B(_7n(_iU,_Lk*_Lg-_Lh*_Ll,_Ll*_Li-_Lg*_Lj,_Lj*_Lh-_Li*_Lk,_Le,_Ld,_Lc));return new T6(0,_IC,_IG,E(new T2(0,E(new T3(0,E(_Lj),E(_Lk),E(_Ll))),E(_Lm))),E(_Iq),_L0,_I8);}),new T2(1,new T(function(){var _Ln=E(_L5),_Lo=E(_Ln.b),_Lp=E(_Ln.c),_Lq=E(_Ln.a),_Lr=E(_KR),_Ls=E(_Lr.c),_Lt=E(_Lr.b),_Lu=E(_Lr.a),_Lv=E(_KL),_Lw=E(_Lv.c),_Lx=E(_Lv.b),_Ly=E(_Lv.a),_Lz=_Lo*_Ls-_Lt*_Lp,_LA=_Lp*_Lu-_Ls*_Lq,_LB=_Lq*_Lt-_Lu*_Lo,_LC=B(_7n(_iU,_LA*_Lw-_Lx*_LB,_LB*_Ly-_Lw*_Lz,_Lz*_Lx-_Ly*_LA,_Lu,_Lt,_Ls));return new T6(0,_IC,_IG,E(_Iq),E(new T2(0,E(new T3(0,E(_Lz),E(_LA),E(_LB))),E(_LC))),_L0,_I8);}),new T(function(){return B(_Kw(_Kz));}))):new T2(1,new T(function(){var _LD=E(_L3),_LE=E(_LD.b),_LF=E(_LD.c),_LG=E(_LD.a),_LH=E(_KU),_LI=_LH.a,_LJ=_LH.b,_LK=_LH.c,_LL=B(_l6(_iU,_LG,_LE,_LF,_LI,_LJ,_LK)),_LM=E(_KO),_LN=E(_LM.c),_LO=E(_LM.b),_LP=E(_LM.a),_LQ=B(_7n(_iU,_LE*_LN-_LO*_LF,_LF*_LP-_LN*_LG,_LG*_LO-_LP*_LE,_LI,_LJ,_LK)),_LR=E(_L5),_LS=E(_LR.b),_LT=E(_LR.c),_LU=E(_LR.a),_LV=E(_KR),_LW=_LV.a,_LX=_LV.b,_LY=_LV.c,_LZ=B(_l6(_iU,_LU,_LS,_LT,_LW,_LX,_LY)),_M0=E(_KL),_M1=E(_M0.c),_M2=E(_M0.b),_M3=E(_M0.a),_M4=B(_7n(_iU,_LS*_M1-_M2*_LT,_LT*_M3-_M1*_LU,_LU*_M2-_M3*_LS,_LW,_LX,_LY));return new T6(0,_IC,_IG,E(new T2(0,E(new T3(0,E(_LL.a),E(_LL.b),E(_LL.c))),E(_LQ))),E(new T2(0,E(new T3(0,E(_LZ.a),E(_LZ.b),E(_LZ.c))),E(_M4))),_L0,_I9);}),new T(function(){return B(_Kw(_Kz));}));}};return B(_Kw(_IR));});return new T2(0,new T2(1,_Ku,_o),new T4(0,E(_IH),E(_II),_IJ,_IK));}}}}}}}}}},_M5=B(_IF(_IC,E(_IE.a),E(_IE.b),_IE.c,_IE.d,_));if(_IC!=_IA){var _M6=B(_IB(_IC+1|0,new T(function(){return E(E(_M5).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Il(E(_M5).a));}),new T(function(){return E(E(_M6).a);})),new T(function(){return E(E(_M6).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Il(E(_M5).a));}),_o),new T(function(){return E(E(_M5).b);}));}}else{if(_IC!=_IA){var _M7=B(_IB(_IC+1|0,_ID,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_M7).a);})),new T(function(){return E(E(_M7).b);}));}else{return new T2(0,new T2(1,_o,_o),_ID);}}},_M8=function(_M9,_Ma,_Mb,_Mc,_Md,_){if(_M9<=_IA){var _Me=function(_Mf,_Mg,_Mh,_Mi,_Mj,_){if(_Mg>_M9){return new F(function(){return die(_Iv);});}else{if(_M9>_Mh){return new F(function(){return die(_Iv);});}else{if(_Mg>_Mf){return new F(function(){return _I7(_);});}else{if(_Mf>_Mh){return new F(function(){return _I7(_);});}else{var _Mk=_M9-_Mg|0;if(0>_Mk){return new F(function(){return _FS(_Mk,_Mi);});}else{if(_Mk>=_Mi){return new F(function(){return _FS(_Mk,_Mi);});}else{var _Ml=E(_Mj[_Mk]),_Mm=_Mf-_Mg|0;if(0>_Mm){return new F(function(){return _FS(_Mm,_Mi);});}else{if(_Mm>=_Mi){return new F(function(){return _FS(_Mm,_Mi);});}else{var _Mn=E(_Mj[_Mm]),_Mo=__app2(E(_Ik),B(_jG(new T2(1,new T2(0,_zH,_Ml.h),new T2(1,new T2(0,_zG,_Ml.i),_o)))),B(_jG(new T2(1,new T2(0,_zH,_Mn.h),new T2(1,new T2(0,_zG,_Mn.i),_o))))),_Mp=__arr2lst(0,_Mo),_Mq=B(_AV(_Mp,_));if(_Mf!=_IA){var _Mr=B(_Me(_Mf+1|0,_Mg,_Mh,_Mi,_Mj,_)),_Ms=new T(function(){var _Mt=new T(function(){return _M9!=_Mf;}),_Mu=function(_Mv){var _Mw=E(_Mv);if(!_Mw._){return __Z;}else{var _Mx=_Mw.b,_My=E(_Mw.a),_Mz=E(_My.b),_MA=E(_My.a),_MB=E(_My.c),_MC=_MB.a,_MD=_MB.b,_ME=E(_My.e),_MF=E(_My.d),_MG=_MF.a,_MH=_MF.b,_MI=E(_My.f),_MJ=new T(function(){var _MK=B(_kj(_iU,_MI.a,_MI.b,_MI.c)),_ML=Math.sqrt(B(_HX(_iU,_MG,_MH,_MG,_MH)));return new T3(0,_ML*E(_MK.a),_ML*E(_MK.b),_ML*E(_MK.c));}),_MM=new T(function(){var _MN=B(_kj(_iU,_ME.a,_ME.b,_ME.c)),_MO=Math.sqrt(B(_HX(_iU,_MC,_MD,_MC,_MD)));return new T3(0,_MO*E(_MN.a),_MO*E(_MN.b),_MO*E(_MN.c));}),_MP=new T(function(){var _MQ=B(A1(_Is,_Mz)),_MR=B(_kj(_iU,_MQ.a,_MQ.b,_MQ.c));return new T3(0,E(_MR.a),E(_MR.b),E(_MR.c));}),_MS=new T(function(){var _MT=B(A1(_Is,_MA)),_MU=B(_kj(_iU,_MT.a,_MT.b,_MT.c));return new T3(0,E(_MU.a),E(_MU.b),E(_MU.c));}),_MV=E(_Mz.a)+ -E(_MA.a),_MW=E(_Mz.b)+ -E(_MA.b),_MX=E(_Mz.c)+ -E(_MA.c),_MY=new T(function(){return Math.sqrt(B(_7n(_iU,_MV,_MW,_MX,_MV,_MW,_MX)));}),_MZ=new T(function(){var _N0=1/E(_MY);return new T3(0,_MV*_N0,_MW*_N0,_MX*_N0);}),_N1=new T(function(){if(!E(_My.g)){return E(_MZ);}else{var _N2=E(_MZ);return new T3(0,-1*E(_N2.a),-1*E(_N2.b),-1*E(_N2.c));}}),_N3=new T(function(){if(!E(_My.h)){return E(_MZ);}else{var _N4=E(_MZ);return new T3(0,-1*E(_N4.a),-1*E(_N4.b),-1*E(_N4.c));}});return (!E(_Mt))?new T2(1,new T(function(){var _N5=E(_N1),_N6=E(_N5.b),_N7=E(_N5.c),_N8=E(_N5.a),_N9=E(_MS),_Na=E(_N9.c),_Nb=E(_N9.b),_Nc=E(_N9.a),_Nd=E(_MM),_Ne=E(_Nd.c),_Nf=E(_Nd.b),_Ng=E(_Nd.a),_Nh=_N6*_Na-_Nb*_N7,_Ni=_N7*_Nc-_Na*_N8,_Nj=_N8*_Nb-_Nc*_N6,_Nk=B(_7n(_iU,_Ni*_Ne-_Nf*_Nj,_Nj*_Ng-_Ne*_Nh,_Nh*_Nf-_Ng*_Ni,_Nc,_Nb,_Na));return new T6(0,_M9,_Mf,E(new T2(0,E(new T3(0,E(_Nh),E(_Ni),E(_Nj))),E(_Nk))),E(_Iq),_MY,_I8);}),new T2(1,new T(function(){var _Nl=E(_N3),_Nm=E(_Nl.b),_Nn=E(_Nl.c),_No=E(_Nl.a),_Np=E(_MP),_Nq=E(_Np.c),_Nr=E(_Np.b),_Ns=E(_Np.a),_Nt=E(_MJ),_Nu=E(_Nt.c),_Nv=E(_Nt.b),_Nw=E(_Nt.a),_Nx=_Nm*_Nq-_Nr*_Nn,_Ny=_Nn*_Ns-_Nq*_No,_Nz=_No*_Nr-_Ns*_Nm,_NA=B(_7n(_iU,_Ny*_Nu-_Nv*_Nz,_Nz*_Nw-_Nu*_Nx,_Nx*_Nv-_Nw*_Ny,_Ns,_Nr,_Nq));return new T6(0,_M9,_Mf,E(_Iq),E(new T2(0,E(new T3(0,E(_Nx),E(_Ny),E(_Nz))),E(_NA))),_MY,_I8);}),new T(function(){return B(_Mu(_Mx));}))):new T2(1,new T(function(){var _NB=E(_N1),_NC=E(_NB.b),_ND=E(_NB.c),_NE=E(_NB.a),_NF=E(_MS),_NG=_NF.a,_NH=_NF.b,_NI=_NF.c,_NJ=B(_l6(_iU,_NE,_NC,_ND,_NG,_NH,_NI)),_NK=E(_MM),_NL=E(_NK.c),_NM=E(_NK.b),_NN=E(_NK.a),_NO=B(_7n(_iU,_NC*_NL-_NM*_ND,_ND*_NN-_NL*_NE,_NE*_NM-_NN*_NC,_NG,_NH,_NI)),_NP=E(_N3),_NQ=E(_NP.b),_NR=E(_NP.c),_NS=E(_NP.a),_NT=E(_MP),_NU=_NT.a,_NV=_NT.b,_NW=_NT.c,_NX=B(_l6(_iU,_NS,_NQ,_NR,_NU,_NV,_NW)),_NY=E(_MJ),_NZ=E(_NY.c),_O0=E(_NY.b),_O1=E(_NY.a),_O2=B(_7n(_iU,_NQ*_NZ-_O0*_NR,_NR*_O1-_NZ*_NS,_NS*_O0-_O1*_NQ,_NU,_NV,_NW));return new T6(0,_M9,_Mf,E(new T2(0,E(new T3(0,E(_NJ.a),E(_NJ.b),E(_NJ.c))),E(_NO))),E(new T2(0,E(new T3(0,E(_NX.a),E(_NX.b),E(_NX.c))),E(_O2))),_MY,_I9);}),new T(function(){return B(_Mu(_Mx));}));}};return B(_Mu(_Mq));});return new T2(0,new T2(1,_Ms,new T(function(){return E(E(_Mr).a);})),new T(function(){return E(E(_Mr).b);}));}else{var _O3=new T(function(){var _O4=new T(function(){return _M9!=_Mf;}),_O5=function(_O6){var _O7=E(_O6);if(!_O7._){return __Z;}else{var _O8=_O7.b,_O9=E(_O7.a),_Oa=E(_O9.b),_Ob=E(_O9.a),_Oc=E(_O9.c),_Od=_Oc.a,_Oe=_Oc.b,_Of=E(_O9.e),_Og=E(_O9.d),_Oh=_Og.a,_Oi=_Og.b,_Oj=E(_O9.f),_Ok=new T(function(){var _Ol=B(_kj(_iU,_Oj.a,_Oj.b,_Oj.c)),_Om=Math.sqrt(B(_HX(_iU,_Oh,_Oi,_Oh,_Oi)));return new T3(0,_Om*E(_Ol.a),_Om*E(_Ol.b),_Om*E(_Ol.c));}),_On=new T(function(){var _Oo=B(_kj(_iU,_Of.a,_Of.b,_Of.c)),_Op=Math.sqrt(B(_HX(_iU,_Od,_Oe,_Od,_Oe)));return new T3(0,_Op*E(_Oo.a),_Op*E(_Oo.b),_Op*E(_Oo.c));}),_Oq=new T(function(){var _Or=B(A1(_Is,_Oa)),_Os=B(_kj(_iU,_Or.a,_Or.b,_Or.c));return new T3(0,E(_Os.a),E(_Os.b),E(_Os.c));}),_Ot=new T(function(){var _Ou=B(A1(_Is,_Ob)),_Ov=B(_kj(_iU,_Ou.a,_Ou.b,_Ou.c));return new T3(0,E(_Ov.a),E(_Ov.b),E(_Ov.c));}),_Ow=E(_Oa.a)+ -E(_Ob.a),_Ox=E(_Oa.b)+ -E(_Ob.b),_Oy=E(_Oa.c)+ -E(_Ob.c),_Oz=new T(function(){return Math.sqrt(B(_7n(_iU,_Ow,_Ox,_Oy,_Ow,_Ox,_Oy)));}),_OA=new T(function(){var _OB=1/E(_Oz);return new T3(0,_Ow*_OB,_Ox*_OB,_Oy*_OB);}),_OC=new T(function(){if(!E(_O9.g)){return E(_OA);}else{var _OD=E(_OA);return new T3(0,-1*E(_OD.a),-1*E(_OD.b),-1*E(_OD.c));}}),_OE=new T(function(){if(!E(_O9.h)){return E(_OA);}else{var _OF=E(_OA);return new T3(0,-1*E(_OF.a),-1*E(_OF.b),-1*E(_OF.c));}});return (!E(_O4))?new T2(1,new T(function(){var _OG=E(_OC),_OH=E(_OG.b),_OI=E(_OG.c),_OJ=E(_OG.a),_OK=E(_Ot),_OL=E(_OK.c),_OM=E(_OK.b),_ON=E(_OK.a),_OO=E(_On),_OP=E(_OO.c),_OQ=E(_OO.b),_OR=E(_OO.a),_OS=_OH*_OL-_OM*_OI,_OT=_OI*_ON-_OL*_OJ,_OU=_OJ*_OM-_ON*_OH,_OV=B(_7n(_iU,_OT*_OP-_OQ*_OU,_OU*_OR-_OP*_OS,_OS*_OQ-_OR*_OT,_ON,_OM,_OL));return new T6(0,_M9,_Mf,E(new T2(0,E(new T3(0,E(_OS),E(_OT),E(_OU))),E(_OV))),E(_Iq),_Oz,_I8);}),new T2(1,new T(function(){var _OW=E(_OE),_OX=E(_OW.b),_OY=E(_OW.c),_OZ=E(_OW.a),_P0=E(_Oq),_P1=E(_P0.c),_P2=E(_P0.b),_P3=E(_P0.a),_P4=E(_Ok),_P5=E(_P4.c),_P6=E(_P4.b),_P7=E(_P4.a),_P8=_OX*_P1-_P2*_OY,_P9=_OY*_P3-_P1*_OZ,_Pa=_OZ*_P2-_P3*_OX,_Pb=B(_7n(_iU,_P9*_P5-_P6*_Pa,_Pa*_P7-_P5*_P8,_P8*_P6-_P7*_P9,_P3,_P2,_P1));return new T6(0,_M9,_Mf,E(_Iq),E(new T2(0,E(new T3(0,E(_P8),E(_P9),E(_Pa))),E(_Pb))),_Oz,_I8);}),new T(function(){return B(_O5(_O8));}))):new T2(1,new T(function(){var _Pc=E(_OC),_Pd=E(_Pc.b),_Pe=E(_Pc.c),_Pf=E(_Pc.a),_Pg=E(_Ot),_Ph=_Pg.a,_Pi=_Pg.b,_Pj=_Pg.c,_Pk=B(_l6(_iU,_Pf,_Pd,_Pe,_Ph,_Pi,_Pj)),_Pl=E(_On),_Pm=E(_Pl.c),_Pn=E(_Pl.b),_Po=E(_Pl.a),_Pp=B(_7n(_iU,_Pd*_Pm-_Pn*_Pe,_Pe*_Po-_Pm*_Pf,_Pf*_Pn-_Po*_Pd,_Ph,_Pi,_Pj)),_Pq=E(_OE),_Pr=E(_Pq.b),_Ps=E(_Pq.c),_Pt=E(_Pq.a),_Pu=E(_Oq),_Pv=_Pu.a,_Pw=_Pu.b,_Px=_Pu.c,_Py=B(_l6(_iU,_Pt,_Pr,_Ps,_Pv,_Pw,_Px)),_Pz=E(_Ok),_PA=E(_Pz.c),_PB=E(_Pz.b),_PC=E(_Pz.a),_PD=B(_7n(_iU,_Pr*_PA-_PB*_Ps,_Ps*_PC-_PA*_Pt,_Pt*_PB-_PC*_Pr,_Pv,_Pw,_Px));return new T6(0,_M9,_Mf,E(new T2(0,E(new T3(0,E(_Pk.a),E(_Pk.b),E(_Pk.c))),E(_Pp))),E(new T2(0,E(new T3(0,E(_Py.a),E(_Py.b),E(_Py.c))),E(_PD))),_Oz,_I9);}),new T(function(){return B(_O5(_O8));}));}};return B(_O5(_Mq));});return new T2(0,new T2(1,_O3,_o),new T4(0,E(_Mg),E(_Mh),_Mi,_Mj));}}}}}}}}}},_PE=B(_Me(_M9,_Ma,_Mb,_Mc,_Md,_));if(_M9!=_IA){var _PF=B(_IB(_M9+1|0,new T(function(){return E(E(_PE).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Il(E(_PE).a));}),new T(function(){return E(E(_PF).a);})),new T(function(){return E(E(_PF).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Il(E(_PE).a));}),_o),new T(function(){return E(E(_PE).b);}));}}else{if(_M9!=_IA){var _PG=B(_M8(_M9+1|0,_Ma,_Mb,_Mc,_Md,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_PG).a);})),new T(function(){return E(E(_PG).b);}));}else{return new T2(0,new T2(1,_o,_o),new T4(0,E(_Ma),E(_Mb),_Mc,_Md));}}},_PH=B(_M8(_Iz,_Iz,_IA,_Iy.c,_Iy.d,_));return new F(function(){return _HP(_,_PH);});}else{return new F(function(){return _HP(_,new T2(0,_o,_Iy));});}},_PI=new T(function(){return eval("__strict(passObject)");}),_PJ=new T(function(){return eval("__strict(refresh)");}),_PK=function(_PL,_){var _PM=__app0(E(_PJ)),_PN=__app0(E(_zL)),_PO=E(_PL),_PP=_PO.c,_PQ=_PO.d,_PR=E(_PO.a),_PS=E(_PO.b);if(_PR<=_PS){if(_PR>_PS){return E(_zJ);}else{if(0>=_PP){return new F(function(){return _zW(_PP,0);});}else{var _PT=E(_PQ[0]),_PU=E(_PI),_PV=__app2(_PU,_PR,B(_jG(new T2(1,new T2(0,_zH,_PT.h),new T2(1,new T2(0,_zG,_PT.i),_o)))));if(_PR!=_PS){var _PW=function(_PX,_){if(_PR>_PX){return E(_zJ);}else{if(_PX>_PS){return E(_zJ);}else{var _PY=_PX-_PR|0;if(0>_PY){return new F(function(){return _zW(_PP,_PY);});}else{if(_PY>=_PP){return new F(function(){return _zW(_PP,_PY);});}else{var _PZ=E(_PQ[_PY]),_Q0=__app2(_PU,_PX,B(_jG(new T2(1,new T2(0,_zH,_PZ.h),new T2(1,new T2(0,_zG,_PZ.i),_o)))));if(_PX!=_PS){var _Q1=B(_PW(_PX+1|0,_));return new T2(1,_jF,_Q1);}else{return _A1;}}}}}},_Q2=B(_PW(_PR+1|0,_)),_Q3=__app0(E(_zK)),_Q4=B(_Iw(_PO,_));return new T(function(){return E(E(_Q4).b);});}else{var _Q5=__app0(E(_zK)),_Q6=B(_Iw(_PO,_));return new T(function(){return E(E(_Q6).b);});}}}}else{var _Q7=__app0(E(_zK)),_Q8=B(_Iw(_PO,_));return new T(function(){return E(E(_Q8).b);});}},_Q9=function(_Qa,_){while(1){var _Qb=E(_Qa);if(!_Qb._){return _jF;}else{var _Qc=_Qb.b,_Qd=E(_Qb.a);switch(_Qd._){case 0:var _Qe=B(A1(_Qd.a,_));_Qa=B(_f(_Qc,new T2(1,_Qe,_o)));continue;case 1:_Qa=B(_f(_Qc,_Qd.a));continue;default:_Qa=_Qc;continue;}}}},_Qf=function(_Qg,_Qh,_){var _Qi=E(_Qg);switch(_Qi._){case 0:var _Qj=B(A1(_Qi.a,_));return new F(function(){return _Q9(B(_f(_Qh,new T2(1,_Qj,_o))),_);});break;case 1:return new F(function(){return _Q9(B(_f(_Qh,_Qi.a)),_);});break;default:return new F(function(){return _Q9(_Qh,_);});}},_Qk=new T0(2),_Ql=function(_Qm){return new T0(2);},_Qn=function(_Qo,_Qp,_Qq){return function(_){var _Qr=E(_Qo),_Qs=rMV(_Qr),_Qt=E(_Qs);if(!_Qt._){var _Qu=new T(function(){var _Qv=new T(function(){return B(A1(_Qq,_jF));});return B(_f(_Qt.b,new T2(1,new T2(0,_Qp,function(_Qw){return E(_Qv);}),_o)));}),_=wMV(_Qr,new T2(0,_Qt.a,_Qu));return _Qk;}else{var _Qx=E(_Qt.a);if(!_Qx._){var _=wMV(_Qr,new T2(0,_Qp,_o));return new T(function(){return B(A1(_Qq,_jF));});}else{var _=wMV(_Qr,new T1(1,_Qx.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Qq,_jF));}),new T2(1,new T(function(){return B(A2(_Qx.a,_Qp,_Ql));}),_o)));}}};},_Qy=new T(function(){return E(_p6);}),_Qz=new T(function(){return eval("window.requestAnimationFrame");}),_QA=new T1(1,_o),_QB=function(_QC,_QD){return function(_){var _QE=E(_QC),_QF=rMV(_QE),_QG=E(_QF);if(!_QG._){var _QH=_QG.a,_QI=E(_QG.b);if(!_QI._){var _=wMV(_QE,_QA);return new T(function(){return B(A1(_QD,_QH));});}else{var _QJ=E(_QI.a),_=wMV(_QE,new T2(0,_QJ.a,_QI.b));return new T1(1,new T2(1,new T(function(){return B(A1(_QD,_QH));}),new T2(1,new T(function(){return B(A1(_QJ.b,_Ql));}),_o)));}}else{var _QK=new T(function(){var _QL=function(_QM){var _QN=new T(function(){return B(A1(_QD,_QM));});return function(_QO){return E(_QN);};};return B(_f(_QG.a,new T2(1,_QL,_o)));}),_=wMV(_QE,new T1(1,_QK));return _Qk;}};},_QP=function(_QQ,_QR){return new T1(0,B(_QB(_QQ,_QR)));},_QS=function(_QT,_QU){var _QV=new T(function(){return new T1(0,B(_Qn(_QT,_jF,_Ql)));});return function(_){var _QW=__createJSFunc(2,function(_QX,_){var _QY=B(_Qf(_QV,_o,_));return _Qy;}),_QZ=__app1(E(_Qz),_QW);return new T(function(){return B(_QP(_QT,_QU));});};},_R0=new T1(1,_o),_R1=function(_R2,_R3,_){var _R4=function(_){var _R5=nMV(_R2),_R6=_R5;return new T(function(){var _R7=new T(function(){return B(_R8(_));}),_R9=function(_){var _Ra=rMV(_R6),_Rb=B(A2(_R3,_Ra,_)),_=wMV(_R6,_Rb),_Rc=function(_){var _Rd=nMV(_R0);return new T(function(){return new T1(0,B(_QS(_Rd,function(_Re){return E(_R7);})));});};return new T1(0,_Rc);},_Rf=new T(function(){return new T1(0,_R9);}),_R8=function(_Rg){return E(_Rf);};return B(_R8(_));});};return new F(function(){return _Qf(new T1(0,_R4),_o,_);});},_Rh=function(_){var _Ri=__app2(E(_0),E(_7W),E(_hg));return new F(function(){return _R1(_zF,_PK,_);});},_Rj=function(_){return new F(function(){return _Rh(_);});};
var hasteMain = function() {B(A(_Rj, [0]));};window.onload = hasteMain;