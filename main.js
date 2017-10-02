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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=function(_hP){var _hQ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(_hP).a);})));})));}),_hR=new T(function(){return B(_fR(_hQ));}),_hS=new T(function(){return B(A2(_8s,_hQ,_8r));}),_hT=new T(function(){return E(E(_hP).b);}),_hU=function(_hV){var _hW=new T(function(){var _hX=new T(function(){return B(A1(_hR,new T(function(){return E(E(_hV).c);})));}),_hY=new T(function(){return B(A1(_hR,new T(function(){return E(E(_hV).a);})));});return B(A3(_gN,_hT,_hY,_hX));});return new F(function(){return A3(_9p,_hQ,_hW,_hS);});};return E(_hU);},_hZ=function(_ef,_ee){return new T2(0,_ef,_ee);},_i0=function(_i1,_i2,_i3){var _i4=new T(function(){var _i5=E(_i1),_i6=_i5.a,_i7=new T(function(){return B(A1(_i5.b,new T(function(){return B(_8J(B(_8H(E(_i5.c).a))));})));});return B(A3(_8R,_i6,new T(function(){return B(A3(_8T,B(_8F(_i6)),_hZ,_i3));}),_i7));});return E(B(A1(_i2,_i4)).b);},_i8=function(_i9){var _ia=new T(function(){return E(E(_i9).a);}),_ib=new T(function(){return E(E(_i9).b);}),_ic=new T(function(){var _id=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_ia,_ib))));}),new T3(0,_8p,_8u,new T2(0,_ia,_ib))));}),_ie=new T(function(){var _if=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_ia,_ib))));}),new T3(0,_8p,_8u,new T2(0,_ia,_ib))));});return B(_eb(_if,new T3(0,_8p,_8u,new T2(0,_ia,_ib))));});return B(_hO(new T2(0,_ie,_id)));});return function(_ig){return new F(function(){return _i0(new T3(0,_8p,_8u,new T2(0,_ia,_ib)),_ic,_ig);});};},_ih=new T(function(){return B(_i8(_7V));}),_ii=new T(function(){return B(A1(_ih,_E));}),_ij=new T(function(){return E(E(_ii).a);}),_ik=new T(function(){return B(unCStr(",y:"));}),_il=new T1(0,_ik),_im=new T(function(){return E(E(_ii).b);}),_in=new T(function(){return B(unCStr(",z:"));}),_io=new T1(0,_in),_ip=new T(function(){return E(E(_ii).c);}),_iq=new T(function(){return B(unCStr("})"));}),_ir=new T1(0,_iq),_is=new T2(1,_ir,_w),_it=new T2(1,_ip,_is),_iu=new T2(1,_io,_it),_iv=new T2(1,_im,_iu),_iw=new T2(1,_il,_iv),_ix=new T2(1,_ij,_iw),_iy=new T(function(){return B(unCStr("({x:"));}),_iz=new T1(0,_iy),_iA=new T2(1,_iz,_ix),_iB=function(_iC){return E(_iC);},_iD=new T(function(){return toJSStr(B(_e(_x,_iB,_iA)));}),_iE=new T(function(){return B(_hO(_7V));}),_iF=new T(function(){return B(A1(_iE,_E));}),_iG=new T(function(){return toJSStr(B(_4(_x,_iB,_iF)));}),_iH=function(_iI,_iJ,_iK){var _iL=E(_iK);if(!_iL._){return new F(function(){return A1(_iJ,_iL.a);});}else{var _iM=new T(function(){return B(_0(_iI));}),_iN=new T(function(){return B(_2(_iI));}),_iO=function(_iP){var _iQ=E(_iP);if(!_iQ._){return E(_iN);}else{return new F(function(){return A2(_iM,new T(function(){return B(_iH(_iI,_iJ,_iQ.a));}),new T(function(){return B(_iO(_iQ.b));}));});}};return new F(function(){return _iO(_iL.a);});}},_iR=new T(function(){return B(unCStr("x"));}),_iS=new T1(0,_iR),_iT=new T(function(){return B(unCStr("y"));}),_iU=new T1(0,_iT),_iV=new T(function(){return B(unCStr("z"));}),_iW=new T1(0,_iV),_iX=new T3(0,E(_iS),E(_iU),E(_iW)),_iY=new T(function(){return B(unCStr(","));}),_iZ=new T1(0,_iY),_j0=new T(function(){return B(unCStr("pow("));}),_j1=new T1(0,_j0),_j2=new T(function(){return B(unCStr(")"));}),_j3=new T1(0,_j2),_j4=new T2(1,_j3,_w),_j5=function(_j6,_j7){return new T1(1,new T2(1,_j1,new T2(1,_j6,new T2(1,_iZ,new T2(1,_j7,_j4)))));},_j8=new T(function(){return B(unCStr("acos("));}),_j9=new T1(0,_j8),_ja=function(_jb){return new T1(1,new T2(1,_j9,new T2(1,_jb,_j4)));},_jc=new T(function(){return B(unCStr("acosh("));}),_jd=new T1(0,_jc),_je=function(_jf){return new T1(1,new T2(1,_jd,new T2(1,_jf,_j4)));},_jg=new T(function(){return B(unCStr("asin("));}),_jh=new T1(0,_jg),_ji=function(_jj){return new T1(1,new T2(1,_jh,new T2(1,_jj,_j4)));},_jk=new T(function(){return B(unCStr("asinh("));}),_jl=new T1(0,_jk),_jm=function(_jn){return new T1(1,new T2(1,_jl,new T2(1,_jn,_j4)));},_jo=new T(function(){return B(unCStr("atan("));}),_jp=new T1(0,_jo),_jq=function(_jr){return new T1(1,new T2(1,_jp,new T2(1,_jr,_j4)));},_js=new T(function(){return B(unCStr("atanh("));}),_jt=new T1(0,_js),_ju=function(_jv){return new T1(1,new T2(1,_jt,new T2(1,_jv,_j4)));},_jw=new T(function(){return B(unCStr("cos("));}),_jx=new T1(0,_jw),_jy=function(_jz){return new T1(1,new T2(1,_jx,new T2(1,_jz,_j4)));},_jA=new T(function(){return B(unCStr("cosh("));}),_jB=new T1(0,_jA),_jC=function(_jD){return new T1(1,new T2(1,_jB,new T2(1,_jD,_j4)));},_jE=new T(function(){return B(unCStr("exp("));}),_jF=new T1(0,_jE),_jG=function(_jH){return new T1(1,new T2(1,_jF,new T2(1,_jH,_j4)));},_jI=new T(function(){return B(unCStr("log("));}),_jJ=new T1(0,_jI),_jK=function(_jL){return new T1(1,new T2(1,_jJ,new T2(1,_jL,_j4)));},_jM=new T(function(){return B(unCStr(")/log("));}),_jN=new T1(0,_jM),_jO=function(_jP,_jQ){return new T1(1,new T2(1,_jJ,new T2(1,_jQ,new T2(1,_jN,new T2(1,_jP,_j4)))));},_jR=new T(function(){return B(unCStr("pi"));}),_jS=new T1(0,_jR),_jT=new T(function(){return B(unCStr("sin("));}),_jU=new T1(0,_jT),_jV=function(_jW){return new T1(1,new T2(1,_jU,new T2(1,_jW,_j4)));},_jX=new T(function(){return B(unCStr("sinh("));}),_jY=new T1(0,_jX),_jZ=function(_k0){return new T1(1,new T2(1,_jY,new T2(1,_k0,_j4)));},_k1=new T(function(){return B(unCStr("sqrt("));}),_k2=new T1(0,_k1),_k3=function(_k4){return new T1(1,new T2(1,_k2,new T2(1,_k4,_j4)));},_k5=new T(function(){return B(unCStr("tan("));}),_k6=new T1(0,_k5),_k7=function(_k8){return new T1(1,new T2(1,_k6,new T2(1,_k8,_j4)));},_k9=new T(function(){return B(unCStr("tanh("));}),_ka=new T1(0,_k9),_kb=function(_kc){return new T1(1,new T2(1,_ka,new T2(1,_kc,_j4)));},_kd=new T(function(){return B(unCStr("("));}),_ke=new T1(0,_kd),_kf=new T(function(){return B(unCStr(")/("));}),_kg=new T1(0,_kf),_kh=function(_ki,_kj){return new T1(1,new T2(1,_ke,new T2(1,_ki,new T2(1,_kg,new T2(1,_kj,_j4)))));},_kk=function(_kl){return new T1(0,new T(function(){var _km=E(_kl),_kn=jsShow(B(_6y(_km.a,_km.b)));return fromJSStr(_kn);}));},_ko=new T(function(){return B(unCStr("1./("));}),_kp=new T1(0,_ko),_kq=function(_kr){return new T1(1,new T2(1,_kp,new T2(1,_kr,_j4)));},_ks=new T(function(){return B(unCStr(")+("));}),_kt=new T1(0,_ks),_ku=function(_kv,_kw){return new T1(1,new T2(1,_ke,new T2(1,_kv,new T2(1,_kt,new T2(1,_kw,_j4)))));},_kx=new T(function(){return B(unCStr("-("));}),_ky=new T1(0,_kx),_kz=function(_kA){return new T1(1,new T2(1,_ky,new T2(1,_kA,_j4)));},_kB=new T(function(){return B(unCStr(")*("));}),_kC=new T1(0,_kB),_kD=function(_kE,_kF){return new T1(1,new T2(1,_ke,new T2(1,_kE,new T2(1,_kC,new T2(1,_kF,_j4)))));},_kG=function(_kH,_kI){return new F(function(){return A3(_6X,_kJ,_kH,new T(function(){return B(A2(_6Z,_kJ,_kI));}));});},_kK=new T(function(){return B(unCStr("abs("));}),_kL=new T1(0,_kK),_kM=function(_kN){return new T1(1,new T2(1,_kL,new T2(1,_kN,_j4)));},_kO=new T(function(){return B(unCStr("."));}),_kP=function(_kQ){return new T1(0,new T(function(){return B(_n(B(_7i(0,_kQ,_w)),_kO));}));},_kR=new T(function(){return B(unCStr("sign("));}),_kS=new T1(0,_kR),_kT=function(_kU){return new T1(1,new T2(1,_kS,new T2(1,_kU,_j4)));},_kJ=new T(function(){return {_:0,a:_ku,b:_kG,c:_kD,d:_kz,e:_kM,f:_kT,g:_kP};}),_kV=new T4(0,_kJ,_kh,_kq,_kk),_kW={_:0,a:_kV,b:_jS,c:_jG,d:_jK,e:_k3,f:_j5,g:_jO,h:_jV,i:_jy,j:_k7,k:_ji,l:_ja,m:_jq,n:_jZ,o:_jC,p:_kb,q:_jm,r:_je,s:_ju},_kX=new T(function(){return B(unCStr("(/=) is not defined"));}),_kY=new T(function(){return B(err(_kX));}),_kZ=new T(function(){return B(unCStr("(==) is not defined"));}),_l0=new T(function(){return B(err(_kZ));}),_l1=new T2(0,_l0,_kY),_l2=new T(function(){return B(unCStr("(<) is not defined"));}),_l3=new T(function(){return B(err(_l2));}),_l4=new T(function(){return B(unCStr("(<=) is not defined"));}),_l5=new T(function(){return B(err(_l4));}),_l6=new T(function(){return B(unCStr("(>) is not defined"));}),_l7=new T(function(){return B(err(_l6));}),_l8=new T(function(){return B(unCStr("(>=) is not defined"));}),_l9=new T(function(){return B(err(_l8));}),_la=new T(function(){return B(unCStr("compare is not defined"));}),_lb=new T(function(){return B(err(_la));}),_lc=new T(function(){return B(unCStr("max("));}),_ld=new T1(0,_lc),_le=function(_lf,_lg){return new T1(1,new T2(1,_ld,new T2(1,_lf,new T2(1,_iZ,new T2(1,_lg,_j4)))));},_lh=new T(function(){return B(unCStr("min("));}),_li=new T1(0,_lh),_lj=function(_lk,_ll){return new T1(1,new T2(1,_li,new T2(1,_lk,new T2(1,_iZ,new T2(1,_ll,_j4)))));},_lm={_:0,a:_l1,b:_lb,c:_l3,d:_l5,e:_l7,f:_l9,g:_le,h:_lj},_ln=new T2(0,_kW,_lm),_lo=new T(function(){return B(_hO(_ln));}),_lp=new T(function(){return B(A1(_lo,_iX));}),_lq=new T(function(){return toJSStr(B(_iH(_x,_iB,_lp)));}),_lr=new T(function(){return eval("__strict(compile)");}),_ls=new T(function(){return toJSStr(E(_iT));}),_lt=function(_lu,_lv,_lw){var _lx=new T(function(){return B(_0(_lu));}),_ly=new T(function(){return B(_2(_lu));}),_lz=function(_lA){var _lB=E(_lA);if(!_lB._){return E(_ly);}else{return new F(function(){return A2(_lx,new T(function(){return B(_iH(_lu,_lv,_lB.a));}),new T(function(){return B(_lz(_lB.b));}));});}};return new F(function(){return _lz(_lw);});},_lC=new T(function(){return B(unCStr("vec3("));}),_lD=new T1(0,_lC),_lE=new T(function(){return B(_7i(0,_8r,_w));}),_lF=new T(function(){return B(_n(_lE,_kO));}),_lG=new T1(0,_lF),_lH=new T(function(){return B(_7i(0,_8q,_w));}),_lI=new T(function(){return B(_n(_lH,_kO));}),_lJ=new T1(0,_lI),_lK=new T2(1,_lJ,_w),_lL=new T2(1,_lG,_lK),_lM=function(_lN,_lO){var _lP=E(_lO);return (_lP._==0)?__Z:new T2(1,_lN,new T2(1,_lP.a,new T(function(){return B(_lM(_lN,_lP.b));})));},_lQ=new T(function(){return B(_lM(_iZ,_lL));}),_lR=new T2(1,_lJ,_lQ),_lS=new T1(1,_lR),_lT=new T2(1,_lS,_j4),_lU=new T2(1,_lD,_lT),_lV=new T(function(){return toJSStr(B(_lt(_x,_iB,_lU)));}),_lW=function(_lX,_lY){while(1){var _lZ=E(_lX);if(!_lZ._){return E(_lY);}else{var _m0=_lY+1|0;_lX=_lZ.b;_lY=_m0;continue;}}},_m1=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_m2=new T(function(){return B(err(_m1));}),_m3=0,_m4=new T3(0,E(_m3),E(_m3),E(_m3)),_m5=new T(function(){return B(unCStr("Negative exponent"));}),_m6=new T(function(){return B(err(_m5));}),_m7=function(_m8,_m9,_ma){while(1){if(!(_m9%2)){var _mb=_m8*_m8,_mc=quot(_m9,2);_m8=_mb;_m9=_mc;continue;}else{var _md=E(_m9);if(_md==1){return _m8*_ma;}else{var _mb=_m8*_m8,_me=_m8*_ma;_m8=_mb;_m9=quot(_md-1|0,2);_ma=_me;continue;}}}},_mf=function(_mg,_mh){while(1){if(!(_mh%2)){var _mi=_mg*_mg,_mj=quot(_mh,2);_mg=_mi;_mh=_mj;continue;}else{var _mk=E(_mh);if(_mk==1){return E(_mg);}else{return new F(function(){return _m7(_mg*_mg,quot(_mk-1|0,2),_mg);});}}}},_ml=function(_mm){var _mn=E(_mm);return new F(function(){return Math.log(_mn+(_mn+1)*Math.sqrt((_mn-1)/(_mn+1)));});},_mo=function(_mp){var _mq=E(_mp);return new F(function(){return Math.log(_mq+Math.sqrt(1+_mq*_mq));});},_mr=function(_ms){var _mt=E(_ms);return 0.5*Math.log((1+_mt)/(1-_mt));},_mu=function(_mv,_mw){return Math.log(E(_mw))/Math.log(E(_mv));},_mx=3.141592653589793,_my=function(_mz){var _mA=E(_mz);return new F(function(){return _6y(_mA.a,_mA.b);});},_mB=function(_mC){return 1/E(_mC);},_mD=function(_mE){var _mF=E(_mE),_mG=E(_mF);return (_mG==0)?E(_6x):(_mG<=0)? -_mG:E(_mF);},_mH=function(_mI){var _mJ=E(_mI);if(!_mJ._){return _mJ.a;}else{return new F(function(){return I_toNumber(_mJ.a);});}},_mK=function(_mL){return new F(function(){return _mH(_mL);});},_mM=1,_mN=-1,_mO=function(_mP){var _mQ=E(_mP);return (_mQ<=0)?(_mQ>=0)?E(_mQ):E(_mN):E(_mM);},_mR=function(_mS,_mT){return E(_mS)-E(_mT);},_mU=function(_mV){return  -E(_mV);},_mW=function(_mX,_mY){return E(_mX)+E(_mY);},_mZ=function(_n0,_n1){return E(_n0)*E(_n1);},_n2={_:0,a:_mW,b:_mR,c:_mZ,d:_mU,e:_mD,f:_mO,g:_mK},_n3=function(_n4,_n5){return E(_n4)/E(_n5);},_n6=new T4(0,_n2,_n3,_mB,_my),_n7=function(_n8){return new F(function(){return Math.acos(E(_n8));});},_n9=function(_na){return new F(function(){return Math.asin(E(_na));});},_nb=function(_nc){return new F(function(){return Math.atan(E(_nc));});},_nd=function(_ne){return new F(function(){return Math.cos(E(_ne));});},_nf=function(_ng){return new F(function(){return cosh(E(_ng));});},_nh=function(_ni){return new F(function(){return Math.exp(E(_ni));});},_nj=function(_nk){return new F(function(){return Math.log(E(_nk));});},_nl=function(_nm,_nn){return new F(function(){return Math.pow(E(_nm),E(_nn));});},_no=function(_np){return new F(function(){return Math.sin(E(_np));});},_nq=function(_nr){return new F(function(){return sinh(E(_nr));});},_ns=function(_nt){return new F(function(){return Math.sqrt(E(_nt));});},_nu=function(_nv){return new F(function(){return Math.tan(E(_nv));});},_nw=function(_nx){return new F(function(){return tanh(E(_nx));});},_ny={_:0,a:_n6,b:_mx,c:_nh,d:_nj,e:_ns,f:_nl,g:_mu,h:_no,i:_nd,j:_nu,k:_n9,l:_n7,m:_nb,n:_nq,o:_nf,p:_nw,q:_mo,r:_ml,s:_mr},_nz=function(_nA,_nB){return (E(_nA)!=E(_nB))?true:false;},_nC=function(_nD,_nE){return E(_nD)==E(_nE);},_nF=new T2(0,_nC,_nz),_nG=function(_nH,_nI){return E(_nH)<E(_nI);},_nJ=function(_nK,_nL){return E(_nK)<=E(_nL);},_nM=function(_nN,_nO){return E(_nN)>E(_nO);},_nP=function(_nQ,_nR){return E(_nQ)>=E(_nR);},_nS=function(_nT,_nU){var _nV=E(_nT),_nW=E(_nU);return (_nV>=_nW)?(_nV!=_nW)?2:1:0;},_nX=function(_nY,_nZ){var _o0=E(_nY),_o1=E(_nZ);return (_o0>_o1)?E(_o0):E(_o1);},_o2=function(_o3,_o4){var _o5=E(_o3),_o6=E(_o4);return (_o5>_o6)?E(_o6):E(_o5);},_o7={_:0,a:_nF,b:_nS,c:_nG,d:_nJ,e:_nM,f:_nP,g:_nX,h:_o2},_o8="dz",_o9="wy",_oa="wx",_ob="dy",_oc="dx",_od="t",_oe="a",_of="r",_og="ly",_oh="lx",_oi="wz",_oj=0,_ok=function(_ol){var _om=__new(),_on=_om,_oo=function(_op,_){while(1){var _oq=E(_op);if(!_oq._){return _oj;}else{var _or=E(_oq.a),_os=__set(_on,E(_or.a),E(_or.b));_op=_oq.b;continue;}}},_ot=B(_oo(_ol,_));return E(_on);},_ou=function(_ov,_ow,_ox,_oy,_oz,_oA,_oB,_oC,_oD){return new F(function(){return _ok(new T2(1,new T2(0,_oa,_ov),new T2(1,new T2(0,_o9,_ow),new T2(1,new T2(0,_oi,_ox),new T2(1,new T2(0,_oh,_oy*_oz*Math.cos(_oA)),new T2(1,new T2(0,_og,_oy*_oz*Math.sin(_oA)),new T2(1,new T2(0,_of,_oy),new T2(1,new T2(0,_oe,_oz),new T2(1,new T2(0,_od,_oA),new T2(1,new T2(0,_oc,_oB),new T2(1,new T2(0,_ob,_oC),new T2(1,new T2(0,_o8,_oD),_w))))))))))));});},_oE=function(_oF){var _oG=E(_oF),_oH=E(_oG.a),_oI=E(_oG.b),_oJ=E(_oG.d);return new F(function(){return _ou(_oH.a,_oH.b,_oH.c,E(_oI.a),E(_oI.b),E(_oG.c),_oJ.a,_oJ.b,_oJ.c);});},_oK=function(_oL,_oM){var _oN=E(_oM);return (_oN._==0)?__Z:new T2(1,new T(function(){return B(A1(_oL,_oN.a));}),new T(function(){return B(_oK(_oL,_oN.b));}));},_oO=function(_oP,_oQ,_oR){var _oS=__lst2arr(B(_oK(_oE,new T2(1,_oP,new T2(1,_oQ,new T2(1,_oR,_w))))));return E(_oS);},_oT=function(_oU){var _oV=E(_oU);return new F(function(){return _oO(_oV.a,_oV.b,_oV.c);});},_oW=new T2(0,_ny,_o7),_oX=function(_oY,_oZ,_p0,_p1,_p2,_p3,_p4){var _p5=B(_8J(B(_8H(_oY)))),_p6=new T(function(){return B(A3(_6X,_p5,new T(function(){return B(A3(_8L,_p5,_oZ,_p2));}),new T(function(){return B(A3(_8L,_p5,_p0,_p3));})));});return new F(function(){return A3(_6X,_p5,_p6,new T(function(){return B(A3(_8L,_p5,_p1,_p4));}));});},_p7=function(_p8,_p9,_pa,_pb){var _pc=B(_8H(_p8)),_pd=new T(function(){return B(A2(_9t,_p8,new T(function(){return B(_oX(_p8,_p9,_pa,_pb,_p9,_pa,_pb));})));});return new T3(0,B(A3(_8P,_pc,_p9,_pd)),B(A3(_8P,_pc,_pa,_pd)),B(A3(_8P,_pc,_pb,_pd)));},_pe=function(_pf,_pg,_ph,_pi,_pj,_pk,_pl){var _pm=B(_8L(_pf));return new T3(0,B(A1(B(A1(_pm,_pg)),_pj)),B(A1(B(A1(_pm,_ph)),_pk)),B(A1(B(A1(_pm,_pi)),_pl)));},_pn=function(_po,_pp,_pq,_pr,_ps,_pt,_pu){var _pv=B(_6X(_po));return new T3(0,B(A1(B(A1(_pv,_pp)),_ps)),B(A1(B(A1(_pv,_pq)),_pt)),B(A1(B(A1(_pv,_pr)),_pu)));},_pw=function(_px,_py){var _pz=new T(function(){return E(E(_px).a);}),_pA=new T(function(){var _pB=E(_py),_pC=new T(function(){return B(_8J(new T(function(){return B(_8H(_pz));})));}),_pD=B(A2(_8s,_pC,_8q));return new T3(0,E(_pD),E(B(A2(_8s,_pC,_8r))),E(_pD));}),_pE=new T(function(){var _pF=E(_pA),_pG=B(_p7(_pz,_pF.a,_pF.b,_pF.c));return new T3(0,E(_pG.a),E(_pG.b),E(_pG.c));}),_pH=new T(function(){var _pI=E(_py),_pJ=_pI.b,_pK=E(_pE),_pL=B(_8H(_pz)),_pM=new T(function(){return B(A2(_9t,_pz,new T(function(){var _pN=E(_pA),_pO=_pN.a,_pP=_pN.b,_pQ=_pN.c;return B(_oX(_pz,_pO,_pP,_pQ,_pO,_pP,_pQ));})));}),_pR=B(A3(_8P,_pL,_pJ,_pM)),_pS=B(_8J(_pL)),_pT=B(_pe(_pS,_pK.a,_pK.b,_pK.c,_pR,_pR,_pR)),_pU=B(_6Z(_pS)),_pV=B(_pn(_pS,_pI.a,_pJ,_pI.c,B(A1(_pU,_pT.a)),B(A1(_pU,_pT.b)),B(A1(_pU,_pT.c))));return new T3(0,E(_pV.a),E(_pV.b),E(_pV.c));});return new T2(0,_pH,_pE);},_pW=function(_pX){return E(E(_pX).a);},_pY=function(_pZ,_q0,_q1,_q2,_q3,_q4,_q5){var _q6=B(_oX(_pZ,_q3,_q4,_q5,_q0,_q1,_q2)),_q7=B(_8J(B(_8H(_pZ)))),_q8=B(_pe(_q7,_q3,_q4,_q5,_q6,_q6,_q6)),_q9=B(_6Z(_q7));return new F(function(){return _pn(_q7,_q0,_q1,_q2,B(A1(_q9,_q8.a)),B(A1(_q9,_q8.b)),B(A1(_q9,_q8.c)));});},_qa=function(_qb){return E(E(_qb).a);},_qc=function(_qd,_qe,_qf,_qg){var _qh=new T(function(){var _qi=E(_qg),_qj=E(_qf),_qk=B(_pY(_qd,_qi.a,_qi.b,_qi.c,_qj.a,_qj.b,_qj.c));return new T3(0,E(_qk.a),E(_qk.b),E(_qk.c));}),_ql=new T(function(){return B(A2(_9t,_qd,new T(function(){var _qm=E(_qh),_qn=_qm.a,_qo=_qm.b,_qp=_qm.c;return B(_oX(_qd,_qn,_qo,_qp,_qn,_qo,_qp));})));});if(!B(A3(_qa,B(_pW(_qe)),_ql,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_qd)))),_8q));})))){var _qq=E(_qh),_qr=B(_p7(_qd,_qq.a,_qq.b,_qq.c)),_qs=B(A2(_9t,_qd,new T(function(){var _qt=E(_qg),_qu=_qt.a,_qv=_qt.b,_qw=_qt.c;return B(_oX(_qd,_qu,_qv,_qw,_qu,_qv,_qw));}))),_qx=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_qd));})));})));return new T3(0,B(A1(B(A1(_qx,_qr.a)),_qs)),B(A1(B(A1(_qx,_qr.b)),_qs)),B(A1(B(A1(_qx,_qr.c)),_qs)));}else{var _qy=B(A2(_8s,B(_8J(B(_8H(_qd)))),_8q));return new T3(0,_qy,_qy,_qy);}},_qz=function(_qA,_qB){while(1){var _qC=E(_qA);if(!_qC._){return E(_qB);}else{var _qD=_qC.b,_qE=E(_qC.a);if(_qB>_qE){_qA=_qD;continue;}else{_qA=_qD;_qB=_qE;continue;}}}},_qF=new T(function(){var _qG=eval("angleCount"),_qH=Number(_qG);return jsTrunc(_qH);}),_qI=new T(function(){return E(_qF);}),_qJ=new T(function(){return B(unCStr(": empty list"));}),_qK=new T(function(){return B(unCStr("Prelude."));}),_qL=function(_qM){return new F(function(){return err(B(_n(_qK,new T(function(){return B(_n(_qM,_qJ));},1))));});},_qN=new T(function(){return B(unCStr("head"));}),_qO=new T(function(){return B(_qL(_qN));}),_qP=function(_qQ,_qR,_qS){var _qT=E(_qQ);if(!_qT._){return __Z;}else{var _qU=E(_qR);if(!_qU._){return __Z;}else{var _qV=_qU.a,_qW=E(_qS);if(!_qW._){return __Z;}else{var _qX=E(_qW.a),_qY=_qX.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_qT.a),E(_qV),E(_qY));}),new T2(1,new T(function(){return new T3(0,E(_qV),E(_qY),E(_qX.b));}),_w)),new T(function(){return B(_qP(_qT.b,_qU.b,_qW.b));},1));});}}}},_qZ=new T(function(){return B(unCStr("tail"));}),_r0=new T(function(){return B(_qL(_qZ));}),_r1=function(_r2,_r3){var _r4=E(_r2);if(!_r4._){return __Z;}else{var _r5=E(_r3);return (_r5._==0)?__Z:new T2(1,new T2(0,_r4.a,_r5.a),new T(function(){return B(_r1(_r4.b,_r5.b));}));}},_r6=function(_r7,_r8){var _r9=E(_r7);if(!_r9._){return __Z;}else{var _ra=E(_r8);if(!_ra._){return __Z;}else{var _rb=E(_r9.a),_rc=_rb.b,_rd=E(_ra.a).b,_re=new T(function(){var _rf=new T(function(){return B(_r1(_rd,new T(function(){var _rg=E(_rd);if(!_rg._){return E(_r0);}else{return E(_rg.b);}},1)));},1);return B(_qP(_rc,new T(function(){var _rh=E(_rc);if(!_rh._){return E(_r0);}else{return E(_rh.b);}},1),_rf));});return new F(function(){return _n(new T2(1,new T(function(){var _ri=E(_rc);if(!_ri._){return E(_qO);}else{var _rj=E(_rd);if(!_rj._){return E(_qO);}else{return new T3(0,E(_rb.a),E(_ri.a),E(_rj.a));}}}),_re),new T(function(){return B(_r6(_r9.b,_ra.b));},1));});}}},_rk=new T(function(){return 6.283185307179586/E(_qI);}),_rl=new T(function(){return E(_qI)-1;}),_rm=new T1(0,1),_rn=function(_ro,_rp){var _rq=E(_rp),_rr=new T(function(){var _rs=B(_8J(_ro)),_rt=B(_rn(_ro,B(A3(_6X,_rs,_rq,new T(function(){return B(A2(_8s,_rs,_rm));})))));return new T2(1,_rt.a,_rt.b);});return new T2(0,_rq,_rr);},_ru=function(_rv){return E(E(_rv).d);},_rw=new T1(0,2),_rx=function(_ry,_rz){var _rA=E(_rz);if(!_rA._){return __Z;}else{var _rB=_rA.a;return (!B(A1(_ry,_rB)))?__Z:new T2(1,_rB,new T(function(){return B(_rx(_ry,_rA.b));}));}},_rC=function(_rD,_rE,_rF,_rG){var _rH=B(_rn(_rE,_rF)),_rI=new T(function(){var _rJ=B(_8J(_rE)),_rK=new T(function(){return B(A3(_8P,_rE,new T(function(){return B(A2(_8s,_rJ,_rm));}),new T(function(){return B(A2(_8s,_rJ,_rw));})));});return B(A3(_6X,_rJ,_rG,_rK));});return new F(function(){return _rx(function(_rL){return new F(function(){return A3(_ru,_rD,_rL,_rI);});},new T2(1,_rH.a,_rH.b));});},_rM=new T(function(){return B(_rC(_o7,_n6,_m3,_rl));}),_rN=function(_rO,_rP){while(1){var _rQ=E(_rO);if(!_rQ._){return E(_rP);}else{_rO=_rQ.b;_rP=_rQ.a;continue;}}},_rR=new T(function(){return B(unCStr("last"));}),_rS=new T(function(){return B(_qL(_rR));}),_rT=function(_rU){return new F(function(){return _rN(_rU,_rS);});},_rV=function(_rW){return new F(function(){return _rT(E(_rW).b);});},_rX=new T(function(){return B(unCStr("maximum"));}),_rY=new T(function(){return B(_qL(_rX));}),_rZ=new T(function(){var _s0=eval("proceedCount"),_s1=Number(_s0);return jsTrunc(_s1);}),_s2=new T(function(){return E(_rZ);}),_s3=1,_s4=new T(function(){return B(_rC(_o7,_n6,_s3,_s2));}),_s5=function(_s6,_s7,_s8,_s9,_sa,_sb,_sc,_sd,_se,_sf,_sg,_sh,_si,_sj){var _sk=new T(function(){var _sl=new T(function(){var _sm=E(_sf),_sn=E(_sj),_so=E(_si),_sp=E(_sg),_sq=E(_sh),_sr=E(_se);return new T3(0,_sm*_sn-_so*_sp,_sp*_sq-_sn*_sr,_sr*_so-_sq*_sm);}),_ss=function(_st){var _su=new T(function(){var _sv=E(_st)/E(_qI);return (_sv+_sv)*3.141592653589793;}),_sw=new T(function(){return B(A1(_s6,_su));}),_sx=new T(function(){var _sy=new T(function(){var _sz=E(_sw)/E(_s2);return new T3(0,E(_sz),E(_sz),E(_sz));}),_sA=function(_sB,_sC){var _sD=E(_sB);if(!_sD._){return new T2(0,_w,_sC);}else{var _sE=new T(function(){var _sF=B(_pw(_oW,new T(function(){var _sG=E(_sC),_sH=E(_sG.a),_sI=E(_sG.b),_sJ=E(_sy);return new T3(0,E(_sH.a)+E(_sI.a)*E(_sJ.a),E(_sH.b)+E(_sI.b)*E(_sJ.b),E(_sH.c)+E(_sI.c)*E(_sJ.c));}))),_sK=_sF.a,_sL=new T(function(){var _sM=E(_sF.b),_sN=E(E(_sC).b),_sO=B(_pY(_ny,_sN.a,_sN.b,_sN.c,_sM.a,_sM.b,_sM.c)),_sP=B(_p7(_ny,_sO.a,_sO.b,_sO.c));return new T3(0,E(_sP.a),E(_sP.b),E(_sP.c));});return new T2(0,new T(function(){var _sQ=E(_sw),_sR=E(_su);return new T4(0,E(_sK),E(new T2(0,E(_sD.a)/E(_s2),E(_sQ))),E(_sR),E(_sL));}),new T2(0,_sK,_sL));}),_sS=new T(function(){var _sT=B(_sA(_sD.b,new T(function(){return E(E(_sE).b);})));return new T2(0,_sT.a,_sT.b);});return new T2(0,new T2(1,new T(function(){return E(E(_sE).a);}),new T(function(){return E(E(_sS).a);})),new T(function(){return E(E(_sS).b);}));}},_sU=function(_sV,_sW,_sX,_sY,_sZ){var _t0=E(_sV);if(!_t0._){return new T2(0,_w,new T2(0,new T3(0,E(_sW),E(_sX),E(_sY)),_sZ));}else{var _t1=new T(function(){var _t2=B(_pw(_oW,new T(function(){var _t3=E(_sZ),_t4=E(_sy);return new T3(0,E(_sW)+E(_t3.a)*E(_t4.a),E(_sX)+E(_t3.b)*E(_t4.b),E(_sY)+E(_t3.c)*E(_t4.c));}))),_t5=_t2.a,_t6=new T(function(){var _t7=E(_t2.b),_t8=E(_sZ),_t9=B(_pY(_ny,_t8.a,_t8.b,_t8.c,_t7.a,_t7.b,_t7.c)),_ta=B(_p7(_ny,_t9.a,_t9.b,_t9.c));return new T3(0,E(_ta.a),E(_ta.b),E(_ta.c));});return new T2(0,new T(function(){var _tb=E(_sw),_tc=E(_su);return new T4(0,E(_t5),E(new T2(0,E(_t0.a)/E(_s2),E(_tb))),E(_tc),E(_t6));}),new T2(0,_t5,_t6));}),_td=new T(function(){var _te=B(_sA(_t0.b,new T(function(){return E(E(_t1).b);})));return new T2(0,_te.a,_te.b);});return new T2(0,new T2(1,new T(function(){return E(E(_t1).a);}),new T(function(){return E(E(_td).a);})),new T(function(){return E(E(_td).b);}));}};return E(B(_sU(_s4,_s9,_sa,_sb,new T(function(){var _tf=E(_sl),_tg=E(_su)+_sc,_th=Math.cos(_tg),_ti=Math.sin(_tg);return new T3(0,E(_se)*_th+E(_tf.a)*_ti,E(_sf)*_th+E(_tf.b)*_ti,E(_sg)*_th+E(_tf.c)*_ti);}))).a);});return new T2(0,new T(function(){var _tj=E(_sw),_tk=E(_su);return new T4(0,E(new T3(0,E(_s9),E(_sa),E(_sb))),E(new T2(0,E(_m3),E(_tj))),E(_tk),E(_m4));}),_sx);};return B(_oK(_ss,_rM));}),_tl=new T(function(){var _tm=function(_tn){return new F(function(){return A1(_s6,new T(function(){return B(_mZ(_tn,_rk));}));});},_to=B(_oK(_tm,_rM));if(!_to._){return E(_rY);}else{return B(_qz(_to.b,E(_to.a)));}}),_tp=new T(function(){var _tq=new T(function(){var _tr=B(_n(_sk,new T2(1,new T(function(){var _ts=E(_sk);if(!_ts._){return E(_qO);}else{return E(_ts.a);}}),_w)));if(!_tr._){return E(_r0);}else{return E(_tr.b);}},1);return B(_r6(_sk,_tq));});return new T3(0,_tp,new T(function(){return B(_oK(_rV,_sk));}),_tl);},_tt=function(_tu,_tv,_tw,_tx,_ty,_tz,_tA,_tB,_tC,_tD,_tE,_tF,_tG,_tH,_tI,_tJ,_tK,_tL){var _tM=B(_pw(_oW,new T3(0,E(_tx),E(_ty),E(_tz)))),_tN=_tM.b,_tO=E(_tM.a),_tP=B(_qc(_ny,_o7,_tN,new T3(0,E(_tB),E(_tC),E(_tD)))),_tQ=E(_tN),_tR=_tQ.a,_tS=_tQ.b,_tT=_tQ.c,_tU=B(_pY(_ny,_tF,_tG,_tH,_tR,_tS,_tT)),_tV=B(_p7(_ny,_tU.a,_tU.b,_tU.c)),_tW=_tV.a,_tX=_tV.b,_tY=_tV.c,_tZ=E(_tA),_u0=new T2(0,E(new T3(0,E(_tP.a),E(_tP.b),E(_tP.c))),E(_tE)),_u1=B(_s5(_tu,_tv,_tw,_tO.a,_tO.b,_tO.c,_tZ,_u0,_tW,_tX,_tY,_tR,_tS,_tT)),_u2=__lst2arr(B(_oK(_oT,_u1.a))),_u3=__lst2arr(B(_oK(_oE,_u1.b)));return {_:0,a:_tu,b:_tv,c:_tw,d:new T2(0,E(_tO),E(_tZ)),e:_u0,f:new T3(0,E(_tW),E(_tX),E(_tY)),g:_tQ,h:_u2,i:_u3,j:E(_u1.c)};},_u4=-4,_u5=new T3(0,E(_m3),E(_m3),E(_u4)),_u6=function(_u7){return E(_u5);},_u8=function(_){return new F(function(){return __jsNull();});},_u9=function(_ua){var _ub=B(A1(_ua,_));return E(_ub);},_uc=new T(function(){return B(_u9(_u8));}),_ud=function(_ue,_uf,_ug,_uh,_ui,_uj,_uk,_ul,_um,_un,_uo,_up,_uq){var _ur=function(_us){var _ut=E(_rk),_uu=2+_us|0,_uv=_uu-1|0,_uw=(2+_us)*(1+_us),_ux=E(_rM);if(!_ux._){return _ut*0;}else{var _uy=_ux.a,_uz=_ux.b,_uA=B(A1(_ue,new T(function(){return 6.283185307179586*E(_uy)/E(_qI);}))),_uB=B(A1(_ue,new T(function(){return 6.283185307179586*(E(_uy)+1)/E(_qI);})));if(_uA!=_uB){if(_uu>=0){var _uC=E(_uu);if(!_uC){var _uD=function(_uE,_uF){while(1){var _uG=B((function(_uH,_uI){var _uJ=E(_uH);if(!_uJ._){return E(_uI);}else{var _uK=_uJ.a,_uL=_uJ.b,_uM=B(A1(_ue,new T(function(){return 6.283185307179586*E(_uK)/E(_qI);}))),_uN=B(A1(_ue,new T(function(){return 6.283185307179586*(E(_uK)+1)/E(_qI);})));if(_uM!=_uN){var _uO=_uI+0/(_uM-_uN)/_uw;_uE=_uL;_uF=_uO;return __continue;}else{if(_uv>=0){var _uP=E(_uv);if(!_uP){var _uO=_uI+_uu/_uw;_uE=_uL;_uF=_uO;return __continue;}else{var _uO=_uI+_uu*B(_mf(_uM,_uP))/_uw;_uE=_uL;_uF=_uO;return __continue;}}else{return E(_m6);}}}})(_uE,_uF));if(_uG!=__continue){return _uG;}}};return _ut*B(_uD(_uz,0/(_uA-_uB)/_uw));}else{var _uQ=function(_uR,_uS){while(1){var _uT=B((function(_uU,_uV){var _uW=E(_uU);if(!_uW._){return E(_uV);}else{var _uX=_uW.a,_uY=_uW.b,_uZ=B(A1(_ue,new T(function(){return 6.283185307179586*E(_uX)/E(_qI);}))),_v0=B(A1(_ue,new T(function(){return 6.283185307179586*(E(_uX)+1)/E(_qI);})));if(_uZ!=_v0){if(_uC>=0){var _v1=_uV+(B(_mf(_uZ,_uC))-B(_mf(_v0,_uC)))/(_uZ-_v0)/_uw;_uR=_uY;_uS=_v1;return __continue;}else{return E(_m6);}}else{if(_uv>=0){var _v2=E(_uv);if(!_v2){var _v1=_uV+_uu/_uw;_uR=_uY;_uS=_v1;return __continue;}else{var _v1=_uV+_uu*B(_mf(_uZ,_v2))/_uw;_uR=_uY;_uS=_v1;return __continue;}}else{return E(_m6);}}}})(_uR,_uS));if(_uT!=__continue){return _uT;}}};return _ut*B(_uQ(_uz,(B(_mf(_uA,_uC))-B(_mf(_uB,_uC)))/(_uA-_uB)/_uw));}}else{return E(_m6);}}else{if(_uv>=0){var _v3=E(_uv);if(!_v3){var _v4=function(_v5,_v6){while(1){var _v7=B((function(_v8,_v9){var _va=E(_v8);if(!_va._){return E(_v9);}else{var _vb=_va.a,_vc=_va.b,_vd=B(A1(_ue,new T(function(){return 6.283185307179586*E(_vb)/E(_qI);}))),_ve=B(A1(_ue,new T(function(){return 6.283185307179586*(E(_vb)+1)/E(_qI);})));if(_vd!=_ve){if(_uu>=0){var _vf=E(_uu);if(!_vf){var _vg=_v9+0/(_vd-_ve)/_uw;_v5=_vc;_v6=_vg;return __continue;}else{var _vg=_v9+(B(_mf(_vd,_vf))-B(_mf(_ve,_vf)))/(_vd-_ve)/_uw;_v5=_vc;_v6=_vg;return __continue;}}else{return E(_m6);}}else{var _vg=_v9+_uu/_uw;_v5=_vc;_v6=_vg;return __continue;}}})(_v5,_v6));if(_v7!=__continue){return _v7;}}};return _ut*B(_v4(_uz,_uu/_uw));}else{var _vh=function(_vi,_vj){while(1){var _vk=B((function(_vl,_vm){var _vn=E(_vl);if(!_vn._){return E(_vm);}else{var _vo=_vn.a,_vp=_vn.b,_vq=B(A1(_ue,new T(function(){return 6.283185307179586*E(_vo)/E(_qI);}))),_vr=B(A1(_ue,new T(function(){return 6.283185307179586*(E(_vo)+1)/E(_qI);})));if(_vq!=_vr){if(_uu>=0){var _vs=E(_uu);if(!_vs){var _vt=_vm+0/(_vq-_vr)/_uw;_vi=_vp;_vj=_vt;return __continue;}else{var _vt=_vm+(B(_mf(_vq,_vs))-B(_mf(_vr,_vs)))/(_vq-_vr)/_uw;_vi=_vp;_vj=_vt;return __continue;}}else{return E(_m6);}}else{if(_v3>=0){var _vt=_vm+_uu*B(_mf(_vq,_v3))/_uw;_vi=_vp;_vj=_vt;return __continue;}else{return E(_m6);}}}})(_vi,_vj));if(_vk!=__continue){return _vk;}}};return _ut*B(_vh(_uz,_uu*B(_mf(_uA,_v3))/_uw));}}else{return E(_m6);}}}},_vu=E(_uc),_vv=1/(B(_ur(1))*_uf);return new F(function(){return _tt(_ue,_u6,new T2(0,E(new T3(0,E(_vv),E(_vv),E(_vv))),1/(B(_ur(3))*_uf)),_ug,_uh,_ui,_uj,_uk,_ul,_um,_un,_uo,_up,_uq,_m4,_vu,_vu,0);});},_vw=1,_vx=0,_vy=function(_vz){var _vA=I_decodeDouble(_vz);return new T2(0,new T1(1,_vA.b),_vA.a);},_vB=function(_vC){return new T1(0,_vC);},_vD=function(_vE){var _vF=hs_intToInt64(2147483647),_vG=hs_leInt64(_vE,_vF);if(!_vG){return new T1(1,I_fromInt64(_vE));}else{var _vH=hs_intToInt64(-2147483648),_vI=hs_geInt64(_vE,_vH);if(!_vI){return new T1(1,I_fromInt64(_vE));}else{var _vJ=hs_int64ToInt(_vE);return new F(function(){return _vB(_vJ);});}}},_vK=new T(function(){var _vL=newByteArr(256),_vM=_vL,_=_vM["v"]["i8"][0]=8,_vN=function(_vO,_vP,_vQ,_){while(1){if(_vQ>=256){if(_vO>=256){return E(_);}else{var _vR=imul(2,_vO)|0,_vS=_vP+1|0,_vT=_vO;_vO=_vR;_vP=_vS;_vQ=_vT;continue;}}else{var _=_vM["v"]["i8"][_vQ]=_vP,_vT=_vQ+_vO|0;_vQ=_vT;continue;}}},_=B(_vN(2,0,1,_));return _vM;}),_vU=function(_vV,_vW){var _vX=hs_int64ToInt(_vV),_vY=E(_vK),_vZ=_vY["v"]["i8"][(255&_vX>>>0)>>>0&4294967295];if(_vW>_vZ){if(_vZ>=8){var _w0=hs_uncheckedIShiftRA64(_vV,8),_w1=function(_w2,_w3){while(1){var _w4=B((function(_w5,_w6){var _w7=hs_int64ToInt(_w5),_w8=_vY["v"]["i8"][(255&_w7>>>0)>>>0&4294967295];if(_w6>_w8){if(_w8>=8){var _w9=hs_uncheckedIShiftRA64(_w5,8),_wa=_w6-8|0;_w2=_w9;_w3=_wa;return __continue;}else{return new T2(0,new T(function(){var _wb=hs_uncheckedIShiftRA64(_w5,_w8);return B(_vD(_wb));}),_w6-_w8|0);}}else{return new T2(0,new T(function(){var _wc=hs_uncheckedIShiftRA64(_w5,_w6);return B(_vD(_wc));}),0);}})(_w2,_w3));if(_w4!=__continue){return _w4;}}};return new F(function(){return _w1(_w0,_vW-8|0);});}else{return new T2(0,new T(function(){var _wd=hs_uncheckedIShiftRA64(_vV,_vZ);return B(_vD(_wd));}),_vW-_vZ|0);}}else{return new T2(0,new T(function(){var _we=hs_uncheckedIShiftRA64(_vV,_vW);return B(_vD(_we));}),0);}},_wf=function(_wg){var _wh=hs_intToInt64(_wg);return E(_wh);},_wi=function(_wj){var _wk=E(_wj);if(!_wk._){return new F(function(){return _wf(_wk.a);});}else{return new F(function(){return I_toInt64(_wk.a);});}},_wl=function(_wm){return I_toInt(_wm)>>>0;},_wn=function(_wo){var _wp=E(_wo);if(!_wp._){return _wp.a>>>0;}else{return new F(function(){return _wl(_wp.a);});}},_wq=function(_wr){var _ws=B(_vy(_wr)),_wt=_ws.a,_wu=_ws.b;if(_wu<0){var _wv=function(_ww){if(!_ww){return new T2(0,E(_wt),B(_3J(_21, -_wu)));}else{var _wx=B(_vU(B(_wi(_wt)), -_wu));return new T2(0,E(_wx.a),B(_3J(_21,_wx.b)));}};if(!((B(_wn(_wt))&1)>>>0)){return new F(function(){return _wv(1);});}else{return new F(function(){return _wv(0);});}}else{return new T2(0,B(_3J(_wt,_wu)),_21);}},_wy=function(_wz){var _wA=B(_wq(E(_wz)));return new T2(0,E(_wA.a),E(_wA.b));},_wB=new T3(0,_n2,_o7,_wy),_wC=function(_wD){return E(E(_wD).a);},_wE=function(_wF){return E(E(_wF).a);},_wG=function(_wH,_wI){if(_wH<=_wI){var _wJ=function(_wK){return new T2(1,_wK,new T(function(){if(_wK!=_wI){return B(_wJ(_wK+1|0));}else{return __Z;}}));};return new F(function(){return _wJ(_wH);});}else{return __Z;}},_wL=function(_wM){return new F(function(){return _wG(E(_wM),2147483647);});},_wN=function(_wO,_wP,_wQ){if(_wQ<=_wP){var _wR=new T(function(){var _wS=_wP-_wO|0,_wT=function(_wU){return (_wU>=(_wQ-_wS|0))?new T2(1,_wU,new T(function(){return B(_wT(_wU+_wS|0));})):new T2(1,_wU,_w);};return B(_wT(_wP));});return new T2(1,_wO,_wR);}else{return (_wQ<=_wO)?new T2(1,_wO,_w):__Z;}},_wV=function(_wW,_wX,_wY){if(_wY>=_wX){var _wZ=new T(function(){var _x0=_wX-_wW|0,_x1=function(_x2){return (_x2<=(_wY-_x0|0))?new T2(1,_x2,new T(function(){return B(_x1(_x2+_x0|0));})):new T2(1,_x2,_w);};return B(_x1(_wX));});return new T2(1,_wW,_wZ);}else{return (_wY>=_wW)?new T2(1,_wW,_w):__Z;}},_x3=function(_x4,_x5){if(_x5<_x4){return new F(function(){return _wN(_x4,_x5,-2147483648);});}else{return new F(function(){return _wV(_x4,_x5,2147483647);});}},_x6=function(_x7,_x8){return new F(function(){return _x3(E(_x7),E(_x8));});},_x9=function(_xa,_xb,_xc){if(_xb<_xa){return new F(function(){return _wN(_xa,_xb,_xc);});}else{return new F(function(){return _wV(_xa,_xb,_xc);});}},_xd=function(_xe,_xf,_xg){return new F(function(){return _x9(E(_xe),E(_xf),E(_xg));});},_xh=function(_xi,_xj){return new F(function(){return _wG(E(_xi),E(_xj));});},_xk=function(_xl){return E(_xl);},_xm=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_xn=new T(function(){return B(err(_xm));}),_xo=function(_xp){var _xq=E(_xp);return (_xq==(-2147483648))?E(_xn):_xq-1|0;},_xr=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_xs=new T(function(){return B(err(_xr));}),_xt=function(_xu){var _xv=E(_xu);return (_xv==2147483647)?E(_xs):_xv+1|0;},_xw={_:0,a:_xt,b:_xo,c:_xk,d:_xk,e:_wL,f:_x6,g:_xh,h:_xd},_xx=function(_xy,_xz){if(_xy<=0){if(_xy>=0){return new F(function(){return quot(_xy,_xz);});}else{if(_xz<=0){return new F(function(){return quot(_xy,_xz);});}else{return quot(_xy+1|0,_xz)-1|0;}}}else{if(_xz>=0){if(_xy>=0){return new F(function(){return quot(_xy,_xz);});}else{if(_xz<=0){return new F(function(){return quot(_xy,_xz);});}else{return quot(_xy+1|0,_xz)-1|0;}}}else{return quot(_xy-1|0,_xz)-1|0;}}},_xA=0,_xB=new T(function(){return B(_36(_xA));}),_xC=new T(function(){return die(_xB);}),_xD=function(_xE,_xF){var _xG=E(_xF);switch(_xG){case -1:var _xH=E(_xE);if(_xH==(-2147483648)){return E(_xC);}else{return new F(function(){return _xx(_xH,-1);});}break;case 0:return E(_3a);default:return new F(function(){return _xx(_xE,_xG);});}},_xI=function(_xJ,_xK){return new F(function(){return _xD(E(_xJ),E(_xK));});},_xL=0,_xM=new T2(0,_xC,_xL),_xN=function(_xO,_xP){var _xQ=E(_xO),_xR=E(_xP);switch(_xR){case -1:var _xS=E(_xQ);if(_xS==(-2147483648)){return E(_xM);}else{if(_xS<=0){if(_xS>=0){var _xT=quotRemI(_xS,-1);return new T2(0,_xT.a,_xT.b);}else{var _xU=quotRemI(_xS,-1);return new T2(0,_xU.a,_xU.b);}}else{var _xV=quotRemI(_xS-1|0,-1);return new T2(0,_xV.a-1|0,(_xV.b+(-1)|0)+1|0);}}break;case 0:return E(_3a);default:if(_xQ<=0){if(_xQ>=0){var _xW=quotRemI(_xQ,_xR);return new T2(0,_xW.a,_xW.b);}else{if(_xR<=0){var _xX=quotRemI(_xQ,_xR);return new T2(0,_xX.a,_xX.b);}else{var _xY=quotRemI(_xQ+1|0,_xR);return new T2(0,_xY.a-1|0,(_xY.b+_xR|0)-1|0);}}}else{if(_xR>=0){if(_xQ>=0){var _xZ=quotRemI(_xQ,_xR);return new T2(0,_xZ.a,_xZ.b);}else{if(_xR<=0){var _y0=quotRemI(_xQ,_xR);return new T2(0,_y0.a,_y0.b);}else{var _y1=quotRemI(_xQ+1|0,_xR);return new T2(0,_y1.a-1|0,(_y1.b+_xR|0)-1|0);}}}else{var _y2=quotRemI(_xQ-1|0,_xR);return new T2(0,_y2.a-1|0,(_y2.b+_xR|0)+1|0);}}}},_y3=function(_y4,_y5){var _y6=_y4%_y5;if(_y4<=0){if(_y4>=0){return E(_y6);}else{if(_y5<=0){return E(_y6);}else{var _y7=E(_y6);return (_y7==0)?0:_y7+_y5|0;}}}else{if(_y5>=0){if(_y4>=0){return E(_y6);}else{if(_y5<=0){return E(_y6);}else{var _y8=E(_y6);return (_y8==0)?0:_y8+_y5|0;}}}else{var _y9=E(_y6);return (_y9==0)?0:_y9+_y5|0;}}},_ya=function(_yb,_yc){var _yd=E(_yc);switch(_yd){case -1:return E(_xL);case 0:return E(_3a);default:return new F(function(){return _y3(E(_yb),_yd);});}},_ye=function(_yf,_yg){var _yh=E(_yf),_yi=E(_yg);switch(_yi){case -1:var _yj=E(_yh);if(_yj==(-2147483648)){return E(_xC);}else{return new F(function(){return quot(_yj,-1);});}break;case 0:return E(_3a);default:return new F(function(){return quot(_yh,_yi);});}},_yk=function(_yl,_ym){var _yn=E(_yl),_yo=E(_ym);switch(_yo){case -1:var _yp=E(_yn);if(_yp==(-2147483648)){return E(_xM);}else{var _yq=quotRemI(_yp,-1);return new T2(0,_yq.a,_yq.b);}break;case 0:return E(_3a);default:var _yr=quotRemI(_yn,_yo);return new T2(0,_yr.a,_yr.b);}},_ys=function(_yt,_yu){var _yv=E(_yu);switch(_yv){case -1:return E(_xL);case 0:return E(_3a);default:return E(_yt)%_yv;}},_yw=function(_yx){return new F(function(){return _vB(E(_yx));});},_yy=function(_yz){return new T2(0,E(B(_vB(E(_yz)))),E(_rm));},_yA=function(_yB,_yC){return imul(E(_yB),E(_yC))|0;},_yD=function(_yE,_yF){return E(_yE)+E(_yF)|0;},_yG=function(_yH,_yI){return E(_yH)-E(_yI)|0;},_yJ=function(_yK){var _yL=E(_yK);return (_yL<0)? -_yL:E(_yL);},_yM=function(_yN){return new F(function(){return _3n(_yN);});},_yO=function(_yP){return  -E(_yP);},_yQ=-1,_yR=0,_yS=1,_yT=function(_yU){var _yV=E(_yU);return (_yV>=0)?(E(_yV)==0)?E(_yR):E(_yS):E(_yQ);},_yW={_:0,a:_yD,b:_yG,c:_yA,d:_yO,e:_yJ,f:_yT,g:_yM},_yX=function(_yY,_yZ){return E(_yY)==E(_yZ);},_z0=function(_z1,_z2){return E(_z1)!=E(_z2);},_z3=new T2(0,_yX,_z0),_z4=function(_z5,_z6){var _z7=E(_z5),_z8=E(_z6);return (_z7>_z8)?E(_z7):E(_z8);},_z9=function(_za,_zb){var _zc=E(_za),_zd=E(_zb);return (_zc>_zd)?E(_zd):E(_zc);},_ze=function(_zf,_zg){return (_zf>=_zg)?(_zf!=_zg)?2:1:0;},_zh=function(_zi,_zj){return new F(function(){return _ze(E(_zi),E(_zj));});},_zk=function(_zl,_zm){return E(_zl)>=E(_zm);},_zn=function(_zo,_zp){return E(_zo)>E(_zp);},_zq=function(_zr,_zs){return E(_zr)<=E(_zs);},_zt=function(_zu,_zv){return E(_zu)<E(_zv);},_zw={_:0,a:_z3,b:_zh,c:_zt,d:_zq,e:_zn,f:_zk,g:_z4,h:_z9},_zx=new T3(0,_yW,_zw,_yy),_zy={_:0,a:_zx,b:_xw,c:_ye,d:_ys,e:_xI,f:_ya,g:_yk,h:_xN,i:_yw},_zz=new T1(0,2),_zA=function(_zB,_zC){while(1){var _zD=E(_zB);if(!_zD._){var _zE=_zD.a,_zF=E(_zC);if(!_zF._){var _zG=_zF.a;if(!(imul(_zE,_zG)|0)){return new T1(0,imul(_zE,_zG)|0);}else{_zB=new T1(1,I_fromInt(_zE));_zC=new T1(1,I_fromInt(_zG));continue;}}else{_zB=new T1(1,I_fromInt(_zE));_zC=_zF;continue;}}else{var _zH=E(_zC);if(!_zH._){_zB=_zD;_zC=new T1(1,I_fromInt(_zH.a));continue;}else{return new T1(1,I_mul(_zD.a,_zH.a));}}}},_zI=function(_zJ,_zK,_zL){while(1){if(!(_zK%2)){var _zM=B(_zA(_zJ,_zJ)),_zN=quot(_zK,2);_zJ=_zM;_zK=_zN;continue;}else{var _zO=E(_zK);if(_zO==1){return new F(function(){return _zA(_zJ,_zL);});}else{var _zM=B(_zA(_zJ,_zJ)),_zP=B(_zA(_zJ,_zL));_zJ=_zM;_zK=quot(_zO-1|0,2);_zL=_zP;continue;}}}},_zQ=function(_zR,_zS){while(1){if(!(_zS%2)){var _zT=B(_zA(_zR,_zR)),_zU=quot(_zS,2);_zR=_zT;_zS=_zU;continue;}else{var _zV=E(_zS);if(_zV==1){return E(_zR);}else{return new F(function(){return _zI(B(_zA(_zR,_zR)),quot(_zV-1|0,2),_zR);});}}}},_zW=function(_zX){return E(E(_zX).b);},_zY=function(_zZ){return E(E(_zZ).c);},_A0=new T1(0,0),_A1=function(_A2){return E(E(_A2).d);},_A3=function(_A4,_A5){var _A6=B(_wC(_A4)),_A7=new T(function(){return B(_wE(_A6));}),_A8=new T(function(){return B(A3(_A1,_A4,_A5,new T(function(){return B(A2(_8s,_A7,_rw));})));});return new F(function(){return A3(_qa,B(_pW(B(_zW(_A6)))),_A8,new T(function(){return B(A2(_8s,_A7,_A0));}));});},_A9=new T(function(){return B(unCStr("Negative exponent"));}),_Aa=new T(function(){return B(err(_A9));}),_Ab=function(_Ac){return E(E(_Ac).c);},_Ad=function(_Ae,_Af,_Ag,_Ah){var _Ai=B(_wC(_Af)),_Aj=new T(function(){return B(_wE(_Ai));}),_Ak=B(_zW(_Ai));if(!B(A3(_zY,_Ak,_Ah,new T(function(){return B(A2(_8s,_Aj,_A0));})))){if(!B(A3(_qa,B(_pW(_Ak)),_Ah,new T(function(){return B(A2(_8s,_Aj,_A0));})))){var _Al=new T(function(){return B(A2(_8s,_Aj,_rw));}),_Am=new T(function(){return B(A2(_8s,_Aj,_rm));}),_An=B(_pW(_Ak)),_Ao=function(_Ap,_Aq,_Ar){while(1){var _As=B((function(_At,_Au,_Av){if(!B(_A3(_Af,_Au))){if(!B(A3(_qa,_An,_Au,_Am))){var _Aw=new T(function(){return B(A3(_Ab,_Af,new T(function(){return B(A3(_9p,_Aj,_Au,_Am));}),_Al));});_Ap=new T(function(){return B(A3(_8L,_Ae,_At,_At));});_Aq=_Aw;_Ar=new T(function(){return B(A3(_8L,_Ae,_At,_Av));});return __continue;}else{return new F(function(){return A3(_8L,_Ae,_At,_Av);});}}else{var _Ax=_Av;_Ap=new T(function(){return B(A3(_8L,_Ae,_At,_At));});_Aq=new T(function(){return B(A3(_Ab,_Af,_Au,_Al));});_Ar=_Ax;return __continue;}})(_Ap,_Aq,_Ar));if(_As!=__continue){return _As;}}},_Ay=function(_Az,_AA){while(1){var _AB=B((function(_AC,_AD){if(!B(_A3(_Af,_AD))){if(!B(A3(_qa,_An,_AD,_Am))){var _AE=new T(function(){return B(A3(_Ab,_Af,new T(function(){return B(A3(_9p,_Aj,_AD,_Am));}),_Al));});return new F(function(){return _Ao(new T(function(){return B(A3(_8L,_Ae,_AC,_AC));}),_AE,_AC);});}else{return E(_AC);}}else{_Az=new T(function(){return B(A3(_8L,_Ae,_AC,_AC));});_AA=new T(function(){return B(A3(_Ab,_Af,_AD,_Al));});return __continue;}})(_Az,_AA));if(_AB!=__continue){return _AB;}}};return new F(function(){return _Ay(_Ag,_Ah);});}else{return new F(function(){return A2(_8s,_Ae,_rm);});}}else{return E(_Aa);}},_AF=new T(function(){return B(err(_A9));}),_AG=function(_AH,_AI){var _AJ=B(_vy(_AI)),_AK=_AJ.a,_AL=_AJ.b,_AM=new T(function(){return B(_wE(new T(function(){return B(_wC(_AH));})));});if(_AL<0){var _AN= -_AL;if(_AN>=0){var _AO=E(_AN);if(!_AO){var _AP=E(_rm);}else{var _AP=B(_zQ(_zz,_AO));}if(!B(_3f(_AP,_3I))){var _AQ=B(_3z(_AK,_AP));return new T2(0,new T(function(){return B(A2(_8s,_AM,_AQ.a));}),new T(function(){return B(_3b(_AQ.b,_AL));}));}else{return E(_3a);}}else{return E(_AF);}}else{var _AR=new T(function(){var _AS=new T(function(){return B(_Ad(_AM,_zy,new T(function(){return B(A2(_8s,_AM,_zz));}),_AL));});return B(A3(_8L,_AM,new T(function(){return B(A2(_8s,_AM,_AK));}),_AS));});return new T2(0,_AR,_6x);}},_AT=function(_AU,_AV){var _AW=B(_AG(_AU,E(_AV))),_AX=_AW.a;if(E(_AW.b)<=0){return E(_AX);}else{var _AY=B(_wE(B(_wC(_AU))));return new F(function(){return A3(_6X,_AY,_AX,new T(function(){return B(A2(_8s,_AY,_21));}));});}},_AZ=function(_B0,_B1){var _B2=B(_AG(_B0,E(_B1))),_B3=_B2.a;if(E(_B2.b)>=0){return E(_B3);}else{var _B4=B(_wE(B(_wC(_B0))));return new F(function(){return A3(_9p,_B4,_B3,new T(function(){return B(A2(_8s,_B4,_21));}));});}},_B5=function(_B6,_B7){var _B8=B(_AG(_B6,E(_B7)));return new T2(0,_B8.a,_B8.b);},_B9=function(_Ba,_Bb){var _Bc=B(_AG(_Ba,_Bb)),_Bd=_Bc.a,_Be=E(_Bc.b),_Bf=new T(function(){var _Bg=B(_wE(B(_wC(_Ba))));if(_Be>=0){return B(A3(_6X,_Bg,_Bd,new T(function(){return B(A2(_8s,_Bg,_21));})));}else{return B(A3(_9p,_Bg,_Bd,new T(function(){return B(A2(_8s,_Bg,_21));})));}}),_Bh=function(_Bi){var _Bj=_Bi-0.5;return (_Bj>=0)?(E(_Bj)==0)?(!B(_A3(_Ba,_Bd)))?E(_Bf):E(_Bd):E(_Bf):E(_Bd);},_Bk=E(_Be);if(!_Bk){return new F(function(){return _Bh(0);});}else{if(_Bk<=0){var _Bl= -_Bk-0.5;return (_Bl>=0)?(E(_Bl)==0)?(!B(_A3(_Ba,_Bd)))?E(_Bf):E(_Bd):E(_Bf):E(_Bd);}else{return new F(function(){return _Bh(_Bk);});}}},_Bm=function(_Bn,_Bo){return new F(function(){return _B9(_Bn,E(_Bo));});},_Bp=function(_Bq,_Br){return E(B(_AG(_Bq,E(_Br))).a);},_Bs={_:0,a:_wB,b:_n6,c:_B5,d:_Bp,e:_Bm,f:_AT,g:_AZ},_Bt=new T1(0,1),_Bu=function(_Bv,_Bw){var _Bx=E(_Bv);return new T2(0,_Bx,new T(function(){var _By=B(_Bu(B(_3q(_Bx,_Bw)),_Bw));return new T2(1,_By.a,_By.b);}));},_Bz=function(_BA){var _BB=B(_Bu(_BA,_Bt));return new T2(1,_BB.a,_BB.b);},_BC=function(_BD,_BE){var _BF=B(_Bu(_BD,new T(function(){return B(_5L(_BE,_BD));})));return new T2(1,_BF.a,_BF.b);},_BG=new T1(0,0),_BH=function(_BI,_BJ){var _BK=E(_BI);if(!_BK._){var _BL=_BK.a,_BM=E(_BJ);return (_BM._==0)?_BL>=_BM.a:I_compareInt(_BM.a,_BL)<=0;}else{var _BN=_BK.a,_BO=E(_BJ);return (_BO._==0)?I_compareInt(_BN,_BO.a)>=0:I_compare(_BN,_BO.a)>=0;}},_BP=function(_BQ,_BR,_BS){if(!B(_BH(_BR,_BG))){var _BT=function(_BU){return (!B(_42(_BU,_BS)))?new T2(1,_BU,new T(function(){return B(_BT(B(_3q(_BU,_BR))));})):__Z;};return new F(function(){return _BT(_BQ);});}else{var _BV=function(_BW){return (!B(_3T(_BW,_BS)))?new T2(1,_BW,new T(function(){return B(_BV(B(_3q(_BW,_BR))));})):__Z;};return new F(function(){return _BV(_BQ);});}},_BX=function(_BY,_BZ,_C0){return new F(function(){return _BP(_BY,B(_5L(_BZ,_BY)),_C0);});},_C1=function(_C2,_C3){return new F(function(){return _BP(_C2,_Bt,_C3);});},_C4=function(_C5){return new F(function(){return _3n(_C5);});},_C6=function(_C7){return new F(function(){return _5L(_C7,_Bt);});},_C8=function(_C9){return new F(function(){return _3q(_C9,_Bt);});},_Ca=function(_Cb){return new F(function(){return _vB(E(_Cb));});},_Cc={_:0,a:_C8,b:_C6,c:_Ca,d:_C4,e:_Bz,f:_BC,g:_C1,h:_BX},_Cd=function(_Ce,_Cf){while(1){var _Cg=E(_Ce);if(!_Cg._){var _Ch=E(_Cg.a);if(_Ch==(-2147483648)){_Ce=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ci=E(_Cf);if(!_Ci._){return new T1(0,B(_xx(_Ch,_Ci.a)));}else{_Ce=new T1(1,I_fromInt(_Ch));_Cf=_Ci;continue;}}}else{var _Cj=_Cg.a,_Ck=E(_Cf);return (_Ck._==0)?new T1(1,I_div(_Cj,I_fromInt(_Ck.a))):new T1(1,I_div(_Cj,_Ck.a));}}},_Cl=function(_Cm,_Cn){if(!B(_3f(_Cn,_A0))){return new F(function(){return _Cd(_Cm,_Cn);});}else{return E(_3a);}},_Co=function(_Cp,_Cq){while(1){var _Cr=E(_Cp);if(!_Cr._){var _Cs=E(_Cr.a);if(_Cs==(-2147483648)){_Cp=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ct=E(_Cq);if(!_Ct._){var _Cu=_Ct.a;return new T2(0,new T1(0,B(_xx(_Cs,_Cu))),new T1(0,B(_y3(_Cs,_Cu))));}else{_Cp=new T1(1,I_fromInt(_Cs));_Cq=_Ct;continue;}}}else{var _Cv=E(_Cq);if(!_Cv._){_Cp=_Cr;_Cq=new T1(1,I_fromInt(_Cv.a));continue;}else{var _Cw=I_divMod(_Cr.a,_Cv.a);return new T2(0,new T1(1,_Cw.a),new T1(1,_Cw.b));}}}},_Cx=function(_Cy,_Cz){if(!B(_3f(_Cz,_A0))){var _CA=B(_Co(_Cy,_Cz));return new T2(0,_CA.a,_CA.b);}else{return E(_3a);}},_CB=function(_CC,_CD){while(1){var _CE=E(_CC);if(!_CE._){var _CF=E(_CE.a);if(_CF==(-2147483648)){_CC=new T1(1,I_fromInt(-2147483648));continue;}else{var _CG=E(_CD);if(!_CG._){return new T1(0,B(_y3(_CF,_CG.a)));}else{_CC=new T1(1,I_fromInt(_CF));_CD=_CG;continue;}}}else{var _CH=_CE.a,_CI=E(_CD);return (_CI._==0)?new T1(1,I_mod(_CH,I_fromInt(_CI.a))):new T1(1,I_mod(_CH,_CI.a));}}},_CJ=function(_CK,_CL){if(!B(_3f(_CL,_A0))){return new F(function(){return _CB(_CK,_CL);});}else{return E(_3a);}},_CM=function(_CN,_CO){while(1){var _CP=E(_CN);if(!_CP._){var _CQ=E(_CP.a);if(_CQ==(-2147483648)){_CN=new T1(1,I_fromInt(-2147483648));continue;}else{var _CR=E(_CO);if(!_CR._){return new T1(0,quot(_CQ,_CR.a));}else{_CN=new T1(1,I_fromInt(_CQ));_CO=_CR;continue;}}}else{var _CS=_CP.a,_CT=E(_CO);return (_CT._==0)?new T1(0,I_toInt(I_quot(_CS,I_fromInt(_CT.a)))):new T1(1,I_quot(_CS,_CT.a));}}},_CU=function(_CV,_CW){if(!B(_3f(_CW,_A0))){return new F(function(){return _CM(_CV,_CW);});}else{return E(_3a);}},_CX=function(_CY,_CZ){if(!B(_3f(_CZ,_A0))){var _D0=B(_3z(_CY,_CZ));return new T2(0,_D0.a,_D0.b);}else{return E(_3a);}},_D1=function(_D2,_D3){while(1){var _D4=E(_D2);if(!_D4._){var _D5=E(_D4.a);if(_D5==(-2147483648)){_D2=new T1(1,I_fromInt(-2147483648));continue;}else{var _D6=E(_D3);if(!_D6._){return new T1(0,_D5%_D6.a);}else{_D2=new T1(1,I_fromInt(_D5));_D3=_D6;continue;}}}else{var _D7=_D4.a,_D8=E(_D3);return (_D8._==0)?new T1(1,I_rem(_D7,I_fromInt(_D8.a))):new T1(1,I_rem(_D7,_D8.a));}}},_D9=function(_Da,_Db){if(!B(_3f(_Db,_A0))){return new F(function(){return _D1(_Da,_Db);});}else{return E(_3a);}},_Dc=function(_Dd){return E(_Dd);},_De=function(_Df){return E(_Df);},_Dg=function(_Dh){var _Di=E(_Dh);if(!_Di._){var _Dj=E(_Di.a);return (_Dj==(-2147483648))?E(_6p):(_Dj<0)?new T1(0, -_Dj):E(_Di);}else{var _Dk=_Di.a;return (I_compareInt(_Dk,0)>=0)?E(_Di):new T1(1,I_negate(_Dk));}},_Dl=new T1(0,0),_Dm=new T1(0,-1),_Dn=function(_Do){var _Dp=E(_Do);if(!_Dp._){var _Dq=_Dp.a;return (_Dq>=0)?(E(_Dq)==0)?E(_Dl):E(_41):E(_Dm);}else{var _Dr=I_compareInt(_Dp.a,0);return (_Dr<=0)?(E(_Dr)==0)?E(_Dl):E(_Dm):E(_41);}},_Ds={_:0,a:_3q,b:_5L,c:_zA,d:_6q,e:_Dg,f:_Dn,g:_De},_Dt=function(_Du,_Dv){var _Dw=E(_Du);if(!_Dw._){var _Dx=_Dw.a,_Dy=E(_Dv);return (_Dy._==0)?_Dx!=_Dy.a:(I_compareInt(_Dy.a,_Dx)==0)?false:true;}else{var _Dz=_Dw.a,_DA=E(_Dv);return (_DA._==0)?(I_compareInt(_Dz,_DA.a)==0)?false:true:(I_compare(_Dz,_DA.a)==0)?false:true;}},_DB=new T2(0,_3f,_Dt),_DC=function(_DD,_DE){return (!B(_5w(_DD,_DE)))?E(_DD):E(_DE);},_DF=function(_DG,_DH){return (!B(_5w(_DG,_DH)))?E(_DH):E(_DG);},_DI={_:0,a:_DB,b:_22,c:_42,d:_5w,e:_3T,f:_BH,g:_DC,h:_DF},_DJ=function(_DK){return new T2(0,E(_DK),E(_rm));},_DL=new T3(0,_Ds,_DI,_DJ),_DM={_:0,a:_DL,b:_Cc,c:_CU,d:_D9,e:_Cl,f:_CJ,g:_CX,h:_Cx,i:_Dc},_DN=function(_DO){return E(E(_DO).b);},_DP=function(_DQ){return E(E(_DQ).g);},_DR=new T1(0,1),_DS=function(_DT,_DU,_DV){var _DW=B(_DN(_DT)),_DX=B(_8J(_DW)),_DY=new T(function(){var _DZ=new T(function(){var _E0=new T(function(){var _E1=new T(function(){return B(A3(_DP,_DT,_DM,new T(function(){return B(A3(_8P,_DW,_DU,_DV));})));});return B(A2(_8s,_DX,_E1));}),_E2=new T(function(){return B(A2(_6Z,_DX,new T(function(){return B(A2(_8s,_DX,_DR));})));});return B(A3(_8L,_DX,_E2,_E0));});return B(A3(_8L,_DX,_DZ,_DV));});return new F(function(){return A3(_6X,_DX,_DU,_DY);});},_E3=1.5707963267948966,_E4=function(_E5){return 0.2/Math.cos(B(_DS(_Bs,_E5,_E3))-0.7853981633974483);},_E6=new T(function(){var _E7=B(_ud(_E4,1.2,_vx,_vx,_vw,_vx,_vx,_vx,_vx,_vx,_vw,_vw,_vw));return {_:0,a:E(_E7.a),b:E(_E7.b),c:E(_E7.c),d:E(_E7.d),e:E(_E7.e),f:E(_E7.f),g:E(_E7.g),h:_E7.h,i:_E7.i,j:_E7.j};}),_E8=0,_E9=0.3,_Ea=function(_Eb){return E(_E9);},_Ec=new T(function(){var _Ed=B(_ud(_Ea,1.2,_vw,_vx,_vw,_vx,_vx,_vx,_vx,_vx,_vw,_vw,_vw));return {_:0,a:E(_Ed.a),b:E(_Ed.b),c:E(_Ed.c),d:E(_Ed.d),e:E(_Ed.e),f:E(_Ed.f),g:E(_Ed.g),h:_Ed.h,i:_Ed.i,j:_Ed.j};}),_Ee=new T(function(){var _Ef=B(_ud(_Ea,1.2,_vw,_vw,_vx,_vx,_vx,_vx,_vx,_vx,_vw,_vw,_vw));return {_:0,a:E(_Ef.a),b:E(_Ef.b),c:E(_Ef.c),d:E(_Ef.d),e:E(_Ef.e),f:E(_Ef.f),g:E(_Ef.g),h:_Ef.h,i:_Ef.i,j:_Ef.j};}),_Eg=2,_Eh=function(_Ei){return 0.3/Math.cos(B(_DS(_Bs,_Ei,_E3))-0.7853981633974483);},_Ej=new T(function(){var _Ek=B(_ud(_Eh,1.2,_Eg,_vw,_vw,_vx,_vx,_vx,_vx,_vx,_vw,_vw,_vw));return {_:0,a:E(_Ek.a),b:E(_Ek.b),c:E(_Ek.c),d:E(_Ek.d),e:E(_Ek.e),f:E(_Ek.f),g:E(_Ek.g),h:_Ek.h,i:_Ek.i,j:_Ek.j};}),_El=0.5,_Em=new T(function(){var _En=B(_ud(_Ea,1.2,_vx,_vw,_El,_vx,_vx,_vx,_vx,_vx,_vw,_vw,_vw));return {_:0,a:E(_En.a),b:E(_En.b),c:E(_En.c),d:E(_En.d),e:E(_En.e),f:E(_En.f),g:E(_En.g),h:_En.h,i:_En.i,j:_En.j};}),_Eo=new T2(1,_Em,_w),_Ep=new T2(1,_Ej,_Eo),_Eq=new T2(1,_Ee,_Ep),_Er=new T2(1,_Ec,_Eq),_Es=new T2(1,_E6,_Er),_Et=new T(function(){return B(unCStr("Negative range size"));}),_Eu=new T(function(){return B(err(_Et));}),_Ev=function(_){var _Ew=B(_lW(_Es,0))-1|0,_Ex=function(_Ey){if(_Ey>=0){var _Ez=newArr(_Ey,_m2),_EA=_Ez,_EB=E(_Ey);if(!_EB){return new T4(0,E(_E8),E(_Ew),0,_EA);}else{var _EC=function(_ED,_EE,_){while(1){var _EF=E(_ED);if(!_EF._){return E(_);}else{var _=_EA[_EE]=_EF.a;if(_EE!=(_EB-1|0)){var _EG=_EE+1|0;_ED=_EF.b;_EE=_EG;continue;}else{return E(_);}}}},_=B((function(_EH,_EI,_EJ,_){var _=_EA[_EJ]=_EH;if(_EJ!=(_EB-1|0)){return new F(function(){return _EC(_EI,_EJ+1|0,_);});}else{return E(_);}})(_E6,_Er,0,_));return new T4(0,E(_E8),E(_Ew),_EB,_EA);}}else{return E(_Eu);}};if(0>_Ew){return new F(function(){return _Ex(0);});}else{return new F(function(){return _Ex(_Ew+1|0);});}},_EK=function(_EL){var _EM=B(A1(_EL,_));return E(_EM);},_EN=new T(function(){return B(_EK(_Ev));}),_EO="enclose",_EP="outline",_EQ="polygon",_ER="z",_ES="y",_ET="x",_EU=function(_EV){return new F(function(){return _ok(new T2(1,new T2(0,_ET,new T(function(){return E(E(E(E(_EV).d).a).a);})),new T2(1,new T2(0,_ES,new T(function(){return E(E(E(E(_EV).d).a).b);})),new T2(1,new T2(0,_ER,new T(function(){return E(E(E(E(_EV).d).a).c);})),new T2(1,new T2(0,_EQ,new T(function(){return E(_EV).h;})),new T2(1,new T2(0,_EP,new T(function(){return E(_EV).i;})),new T2(1,new T2(0,_EO,new T(function(){return E(_EV).j;})),_w)))))));});},_EW=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_EX=new T(function(){return B(err(_EW));}),_EY=new T(function(){return eval("__strict(drawObjects)");}),_EZ=new T(function(){return eval("__strict(draw)");}),_F0=function(_F1,_F2){var _F3=jsShowI(_F1);return new F(function(){return _n(fromJSStr(_F3),_F2);});},_F4=function(_F5,_F6,_F7){if(_F6>=0){return new F(function(){return _F0(_F6,_F7);});}else{if(_F5<=6){return new F(function(){return _F0(_F6,_F7);});}else{return new T2(1,_7g,new T(function(){var _F8=jsShowI(_F6);return B(_n(fromJSStr(_F8),new T2(1,_7f,_F7)));}));}}},_F9=new T(function(){return B(unCStr(")"));}),_Fa=function(_Fb,_Fc){var _Fd=new T(function(){var _Fe=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_F4(0,_Fb,_w)),_F9));})));},1);return B(_n(B(_F4(0,_Fc,_w)),_Fe));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Fd)));});},_Ff=new T2(1,_oj,_w),_Fg=function(_Fh){return E(_Fh);},_Fi=function(_Fj){return E(_Fj);},_Fk=function(_Fl,_Fm){return E(_Fm);},_Fn=function(_Fo,_Fp){return E(_Fo);},_Fq=function(_Fr){return E(_Fr);},_Fs=new T2(0,_Fq,_Fn),_Ft=function(_Fu,_Fv){return E(_Fu);},_Fw=new T5(0,_Fs,_Fi,_Fg,_Fk,_Ft),_Fx="flipped2",_Fy="flipped1",_Fz="c1y",_FA="c1x",_FB="w2z",_FC="w2y",_FD="w2x",_FE="w1z",_FF="w1y",_FG="w1x",_FH="d2z",_FI="d2y",_FJ="d2x",_FK="d1z",_FL="d1y",_FM="d1x",_FN="c2y",_FO="c2x",_FP=function(_FQ,_){var _FR=__get(_FQ,E(_FG)),_FS=__get(_FQ,E(_FF)),_FT=__get(_FQ,E(_FE)),_FU=__get(_FQ,E(_FD)),_FV=__get(_FQ,E(_FC)),_FW=__get(_FQ,E(_FB)),_FX=__get(_FQ,E(_FA)),_FY=__get(_FQ,E(_Fz)),_FZ=__get(_FQ,E(_FO)),_G0=__get(_FQ,E(_FN)),_G1=__get(_FQ,E(_FM)),_G2=__get(_FQ,E(_FL)),_G3=__get(_FQ,E(_FK)),_G4=__get(_FQ,E(_FJ)),_G5=__get(_FQ,E(_FI)),_G6=__get(_FQ,E(_FH)),_G7=__get(_FQ,E(_Fy)),_G8=__get(_FQ,E(_Fx));return {_:0,a:E(new T3(0,E(_FR),E(_FS),E(_FT))),b:E(new T3(0,E(_FU),E(_FV),E(_FW))),c:E(new T2(0,E(_FX),E(_FY))),d:E(new T2(0,E(_FZ),E(_G0))),e:E(new T3(0,E(_G1),E(_G2),E(_G3))),f:E(new T3(0,E(_G4),E(_G5),E(_G6))),g:E(_G7),h:E(_G8)};},_G9=function(_Ga,_){var _Gb=E(_Ga);if(!_Gb._){return _w;}else{var _Gc=B(_FP(E(_Gb.a),_)),_Gd=B(_G9(_Gb.b,_));return new T2(1,_Gc,_Gd);}},_Ge=function(_Gf){var _Gg=E(_Gf);return (E(_Gg.b)-E(_Gg.a)|0)+1|0;},_Gh=function(_Gi,_Gj){var _Gk=E(_Gi),_Gl=E(_Gj);return (E(_Gk.a)>_Gl)?false:_Gl<=E(_Gk.b);},_Gm=function(_Gn){return new F(function(){return _F4(0,E(_Gn),_w);});},_Go=function(_Gp,_Gq,_Gr){return new F(function(){return _F4(E(_Gp),E(_Gq),_Gr);});},_Gs=function(_Gt,_Gu){return new F(function(){return _F4(0,E(_Gt),_Gu);});},_Gv=function(_Gw,_Gx){return new F(function(){return _2Q(_Gs,_Gw,_Gx);});},_Gy=new T3(0,_Go,_Gm,_Gv),_Gz=0,_GA=function(_GB,_GC,_GD){return new F(function(){return A1(_GB,new T2(1,_2N,new T(function(){return B(A1(_GC,_GD));})));});},_GE=new T(function(){return B(unCStr("foldr1"));}),_GF=new T(function(){return B(_qL(_GE));}),_GG=function(_GH,_GI){var _GJ=E(_GI);if(!_GJ._){return E(_GF);}else{var _GK=_GJ.a,_GL=E(_GJ.b);if(!_GL._){return E(_GK);}else{return new F(function(){return A2(_GH,_GK,new T(function(){return B(_GG(_GH,_GL));}));});}}},_GM=new T(function(){return B(unCStr(" out of range "));}),_GN=new T(function(){return B(unCStr("}.index: Index "));}),_GO=new T(function(){return B(unCStr("Ix{"));}),_GP=new T2(1,_7f,_w),_GQ=new T2(1,_7f,_GP),_GR=0,_GS=function(_GT){return E(E(_GT).a);},_GU=function(_GV,_GW,_GX,_GY,_GZ){var _H0=new T(function(){var _H1=new T(function(){var _H2=new T(function(){var _H3=new T(function(){var _H4=new T(function(){return B(A3(_GG,_GA,new T2(1,new T(function(){return B(A3(_GS,_GX,_GR,_GY));}),new T2(1,new T(function(){return B(A3(_GS,_GX,_GR,_GZ));}),_w)),_GQ));});return B(_n(_GM,new T2(1,_7g,new T2(1,_7g,_H4))));});return B(A(_GS,[_GX,_Gz,_GW,new T2(1,_7f,_H3)]));});return B(_n(_GN,new T2(1,_7g,_H2)));},1);return B(_n(_GV,_H1));},1);return new F(function(){return err(B(_n(_GO,_H0)));});},_H5=function(_H6,_H7,_H8,_H9,_Ha){return new F(function(){return _GU(_H6,_H7,_Ha,_H8,_H9);});},_Hb=function(_Hc,_Hd,_He,_Hf){var _Hg=E(_He);return new F(function(){return _H5(_Hc,_Hd,_Hg.a,_Hg.b,_Hf);});},_Hh=function(_Hi,_Hj,_Hk,_Hl){return new F(function(){return _Hb(_Hl,_Hk,_Hj,_Hi);});},_Hm=new T(function(){return B(unCStr("Int"));}),_Hn=function(_Ho,_Hp){return new F(function(){return _Hh(_Gy,_Hp,_Ho,_Hm);});},_Hq=function(_Hr,_Hs){var _Ht=E(_Hr),_Hu=E(_Ht.a),_Hv=E(_Hs);if(_Hu>_Hv){return new F(function(){return _Hn(_Hv,_Ht);});}else{if(_Hv>E(_Ht.b)){return new F(function(){return _Hn(_Hv,_Ht);});}else{return _Hv-_Hu|0;}}},_Hw=function(_Hx){var _Hy=E(_Hx);return new F(function(){return _xh(_Hy.a,_Hy.b);});},_Hz=function(_HA){var _HB=E(_HA),_HC=E(_HB.a),_HD=E(_HB.b);return (_HC>_HD)?E(_Gz):(_HD-_HC|0)+1|0;},_HE=function(_HF,_HG){return new F(function(){return _yG(_HG,E(_HF).a);});},_HH={_:0,a:_zw,b:_Hw,c:_Hq,d:_HE,e:_Gh,f:_Hz,g:_Ge},_HI=function(_HJ,_HK,_){while(1){var _HL=B((function(_HM,_HN,_){var _HO=E(_HM);if(!_HO._){return new T2(0,_oj,_HN);}else{var _HP=B(A2(_HO.a,_HN,_));_HJ=_HO.b;_HK=new T(function(){return E(E(_HP).b);});return __continue;}})(_HJ,_HK,_));if(_HL!=__continue){return _HL;}}},_HQ=function(_HR,_HS){return new T2(1,_HR,_HS);},_HT=function(_HU,_HV){var _HW=E(_HV);return new T2(0,_HW.a,_HW.b);},_HX=function(_HY){return E(E(_HY).f);},_HZ=function(_I0,_I1,_I2){var _I3=E(_I1),_I4=_I3.a,_I5=_I3.b,_I6=function(_){var _I7=B(A2(_HX,_I0,_I3));if(_I7>=0){var _I8=newArr(_I7,_m2),_I9=_I8,_Ia=E(_I7);if(!_Ia){return new T(function(){return new T4(0,E(_I4),E(_I5),0,_I9);});}else{var _Ib=function(_Ic,_Id,_){while(1){var _Ie=E(_Ic);if(!_Ie._){return E(_);}else{var _=_I9[_Id]=_Ie.a;if(_Id!=(_Ia-1|0)){var _If=_Id+1|0;_Ic=_Ie.b;_Id=_If;continue;}else{return E(_);}}}},_=B(_Ib(_I2,0,_));return new T(function(){return new T4(0,E(_I4),E(_I5),_Ia,_I9);});}}else{return E(_Eu);}};return new F(function(){return _EK(_I6);});},_Ig=function(_Ih,_Ii,_Ij,_Ik){var _Il=new T(function(){var _Im=E(_Ik),_In=_Im.c-1|0,_Io=new T(function(){return B(A2(_cF,_Ii,_w));});if(0<=_In){var _Ip=new T(function(){return B(_8F(_Ii));}),_Iq=function(_Ir){var _Is=new T(function(){var _It=new T(function(){return B(A1(_Ij,new T(function(){return E(_Im.d[_Ir]);})));});return B(A3(_8T,_Ip,_HQ,_It));});return new F(function(){return A3(_8R,_Ii,_Is,new T(function(){if(_Ir!=_In){return B(_Iq(_Ir+1|0));}else{return E(_Io);}}));});};return B(_Iq(0));}else{return E(_Io);}}),_Iu=new T(function(){return B(_HT(_Ih,_Ik));});return new F(function(){return A3(_8T,B(_8F(_Ii)),function(_Iv){return new F(function(){return _HZ(_Ih,_Iu,_Iv);});},_Il);});},_Iw=function(_Ix,_Iy,_Iz,_IA,_IB,_IC,_ID,_IE,_IF){var _IG=B(_8L(_Ix));return new T2(0,new T3(0,E(B(A1(B(A1(_IG,_Iy)),_IC))),E(B(A1(B(A1(_IG,_Iz)),_ID))),E(B(A1(B(A1(_IG,_IA)),_IE)))),B(A1(B(A1(_IG,_IB)),_IF)));},_IH=function(_II,_IJ,_IK,_IL,_IM,_IN,_IO,_IP,_IQ){var _IR=B(_6X(_II));return new T2(0,new T3(0,E(B(A1(B(A1(_IR,_IJ)),_IN))),E(B(A1(B(A1(_IR,_IK)),_IO))),E(B(A1(B(A1(_IR,_IL)),_IP)))),B(A1(B(A1(_IR,_IM)),_IQ)));},_IS=1.0e-2,_IT=function(_IU,_IV,_IW,_IX,_IY,_IZ,_J0,_J1,_J2,_J3,_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb){var _Jc=B(_Iw(_n2,_J1,_J2,_J3,_J4,_IS,_IS,_IS,_IS)),_Jd=E(_Jc.a),_Je=B(_IH(_n2,_IX,_IY,_IZ,_J0,_Jd.a,_Jd.b,_Jd.c,_Jc.b)),_Jf=E(_Je.a);return new F(function(){return _tt(_IU,_IV,_IW,_Jf.a,_Jf.b,_Jf.c,_Je.b,_J1,_J2,_J3,_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb);});},_Jg=function(_Jh){var _Ji=E(_Jh),_Jj=E(_Ji.d),_Jk=E(_Jj.a),_Jl=E(_Ji.e),_Jm=E(_Jl.a),_Jn=E(_Ji.f),_Jo=B(_IT(_Ji.a,_Ji.b,_Ji.c,_Jk.a,_Jk.b,_Jk.c,_Jj.b,_Jm.a,_Jm.b,_Jm.c,_Jl.b,_Jn.a,_Jn.b,_Jn.c,_Ji.g,_Ji.h,_Ji.i,_Ji.j));return {_:0,a:E(_Jo.a),b:E(_Jo.b),c:E(_Jo.c),d:E(_Jo.d),e:E(_Jo.e),f:E(_Jo.f),g:E(_Jo.g),h:_Jo.h,i:_Jo.i,j:_Jo.j};},_Jp=function(_Jq,_Jr,_Js,_Jt,_Ju,_Jv,_Jw,_Jx,_Jy){var _Jz=B(_8J(B(_8H(_Jq))));return new F(function(){return A3(_6X,_Jz,new T(function(){return B(_oX(_Jq,_Jr,_Js,_Jt,_Jv,_Jw,_Jx));}),new T(function(){return B(A3(_8L,_Jz,_Ju,_Jy));}));});},_JA=new T(function(){return B(unCStr("base"));}),_JB=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_JC=new T(function(){return B(unCStr("IOException"));}),_JD=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_JA,_JB,_JC),_JE=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_JD,_w,_w),_JF=function(_JG){return E(_JE);},_JH=function(_JI){var _JJ=E(_JI);return new F(function(){return _2n(B(_2l(_JJ.a)),_JF,_JJ.b);});},_JK=new T(function(){return B(unCStr(": "));}),_JL=new T(function(){return B(unCStr(")"));}),_JM=new T(function(){return B(unCStr(" ("));}),_JN=new T(function(){return B(unCStr("interrupted"));}),_JO=new T(function(){return B(unCStr("system error"));}),_JP=new T(function(){return B(unCStr("unsatisified constraints"));}),_JQ=new T(function(){return B(unCStr("user error"));}),_JR=new T(function(){return B(unCStr("permission denied"));}),_JS=new T(function(){return B(unCStr("illegal operation"));}),_JT=new T(function(){return B(unCStr("end of file"));}),_JU=new T(function(){return B(unCStr("resource exhausted"));}),_JV=new T(function(){return B(unCStr("resource busy"));}),_JW=new T(function(){return B(unCStr("does not exist"));}),_JX=new T(function(){return B(unCStr("already exists"));}),_JY=new T(function(){return B(unCStr("resource vanished"));}),_JZ=new T(function(){return B(unCStr("timeout"));}),_K0=new T(function(){return B(unCStr("unsupported operation"));}),_K1=new T(function(){return B(unCStr("hardware fault"));}),_K2=new T(function(){return B(unCStr("inappropriate type"));}),_K3=new T(function(){return B(unCStr("invalid argument"));}),_K4=new T(function(){return B(unCStr("failed"));}),_K5=new T(function(){return B(unCStr("protocol error"));}),_K6=function(_K7,_K8){switch(E(_K7)){case 0:return new F(function(){return _n(_JX,_K8);});break;case 1:return new F(function(){return _n(_JW,_K8);});break;case 2:return new F(function(){return _n(_JV,_K8);});break;case 3:return new F(function(){return _n(_JU,_K8);});break;case 4:return new F(function(){return _n(_JT,_K8);});break;case 5:return new F(function(){return _n(_JS,_K8);});break;case 6:return new F(function(){return _n(_JR,_K8);});break;case 7:return new F(function(){return _n(_JQ,_K8);});break;case 8:return new F(function(){return _n(_JP,_K8);});break;case 9:return new F(function(){return _n(_JO,_K8);});break;case 10:return new F(function(){return _n(_K5,_K8);});break;case 11:return new F(function(){return _n(_K4,_K8);});break;case 12:return new F(function(){return _n(_K3,_K8);});break;case 13:return new F(function(){return _n(_K2,_K8);});break;case 14:return new F(function(){return _n(_K1,_K8);});break;case 15:return new F(function(){return _n(_K0,_K8);});break;case 16:return new F(function(){return _n(_JZ,_K8);});break;case 17:return new F(function(){return _n(_JY,_K8);});break;default:return new F(function(){return _n(_JN,_K8);});}},_K9=new T(function(){return B(unCStr("}"));}),_Ka=new T(function(){return B(unCStr("{handle: "));}),_Kb=function(_Kc,_Kd,_Ke,_Kf,_Kg,_Kh){var _Ki=new T(function(){var _Kj=new T(function(){var _Kk=new T(function(){var _Kl=E(_Kf);if(!_Kl._){return E(_Kh);}else{var _Km=new T(function(){return B(_n(_Kl,new T(function(){return B(_n(_JL,_Kh));},1)));},1);return B(_n(_JM,_Km));}},1);return B(_K6(_Kd,_Kk));}),_Kn=E(_Ke);if(!_Kn._){return E(_Kj);}else{return B(_n(_Kn,new T(function(){return B(_n(_JK,_Kj));},1)));}}),_Ko=E(_Kg);if(!_Ko._){var _Kp=E(_Kc);if(!_Kp._){return E(_Ki);}else{var _Kq=E(_Kp.a);if(!_Kq._){var _Kr=new T(function(){var _Ks=new T(function(){return B(_n(_K9,new T(function(){return B(_n(_JK,_Ki));},1)));},1);return B(_n(_Kq.a,_Ks));},1);return new F(function(){return _n(_Ka,_Kr);});}else{var _Kt=new T(function(){var _Ku=new T(function(){return B(_n(_K9,new T(function(){return B(_n(_JK,_Ki));},1)));},1);return B(_n(_Kq.a,_Ku));},1);return new F(function(){return _n(_Ka,_Kt);});}}}else{return new F(function(){return _n(_Ko.a,new T(function(){return B(_n(_JK,_Ki));},1));});}},_Kv=function(_Kw){var _Kx=E(_Kw);return new F(function(){return _Kb(_Kx.a,_Kx.b,_Kx.c,_Kx.d,_Kx.f,_w);});},_Ky=function(_Kz,_KA,_KB){var _KC=E(_KA);return new F(function(){return _Kb(_KC.a,_KC.b,_KC.c,_KC.d,_KC.f,_KB);});},_KD=function(_KE,_KF){var _KG=E(_KE);return new F(function(){return _Kb(_KG.a,_KG.b,_KG.c,_KG.d,_KG.f,_KF);});},_KH=function(_KI,_KJ){return new F(function(){return _2Q(_KD,_KI,_KJ);});},_KK=new T3(0,_Ky,_Kv,_KH),_KL=new T(function(){return new T5(0,_JF,_KK,_KM,_JH,_Kv);}),_KM=function(_KN){return new T2(0,_KL,_KN);},_KO=__Z,_KP=7,_KQ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_KR=new T6(0,_KO,_KP,_w,_KQ,_KO,_KO),_KS=new T(function(){return B(_KM(_KR));}),_KT=function(_){return new F(function(){return die(_KS);});},_KU=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_KV=new T6(0,_KO,_KP,_w,_KU,_KO,_KO),_KW=new T(function(){return B(_KM(_KV));}),_KX=function(_){return new F(function(){return die(_KW);});},_KY=function(_KZ,_){return new T2(0,_w,_KZ);},_L0=0.6,_L1=1,_L2=new T(function(){return B(unCStr(")"));}),_L3=function(_L4,_L5){var _L6=new T(function(){var _L7=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_F4(0,_L4,_w)),_L2));})));},1);return B(_n(B(_F4(0,_L5,_w)),_L7));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_L6)));});},_L8=function(_L9,_La){var _Lb=new T(function(){var _Lc=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_F4(0,_La,_w)),_L2));})));},1);return B(_n(B(_F4(0,_L9,_w)),_Lc));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Lb)));});},_Ld=function(_Le){var _Lf=E(_Le);if(!_Lf._){return E(_KY);}else{var _Lg=new T(function(){return B(_Ld(_Lf.b));}),_Lh=function(_Li){var _Lj=E(_Li);if(!_Lj._){return E(_Lg);}else{var _Lk=_Lj.a,_Ll=new T(function(){return B(_Lh(_Lj.b));}),_Lm=new T(function(){return 0.1*E(E(_Lk).e)/1.0e-2;}),_Ln=new T(function(){var _Lo=E(_Lk);if(_Lo.a!=_Lo.b){return E(_L1);}else{return E(_L0);}}),_Lp=function(_Lq,_){var _Lr=E(_Lq),_Ls=_Lr.c,_Lt=_Lr.d,_Lu=E(_Lr.a),_Lv=E(_Lr.b),_Lw=E(_Lk),_Lx=_Lw.a,_Ly=_Lw.b,_Lz=E(_Lw.c),_LA=_Lz.b,_LB=E(_Lz.a),_LC=_LB.a,_LD=_LB.b,_LE=_LB.c,_LF=E(_Lw.d),_LG=_LF.b,_LH=E(_LF.a),_LI=_LH.a,_LJ=_LH.b,_LK=_LH.c;if(_Lu>_Lx){return new F(function(){return _KX(_);});}else{if(_Lx>_Lv){return new F(function(){return _KX(_);});}else{if(_Lu>_Ly){return new F(function(){return _KT(_);});}else{if(_Ly>_Lv){return new F(function(){return _KT(_);});}else{var _LL=_Lx-_Lu|0;if(0>_LL){return new F(function(){return _L3(_Ls,_LL);});}else{if(_LL>=_Ls){return new F(function(){return _L3(_Ls,_LL);});}else{var _LM=E(_Lt[_LL]),_LN=E(_LM.c),_LO=_LN.b,_LP=E(_LN.a),_LQ=_LP.a,_LR=_LP.b,_LS=_LP.c,_LT=E(_LM.e),_LU=E(_LT.a),_LV=B(_Iw(_n2,_LC,_LD,_LE,_LA,_LQ,_LR,_LS,_LO)),_LW=E(_LV.a),_LX=B(_Iw(_n2,_LW.a,_LW.b,_LW.c,_LV.b,_LC,_LD,_LE,_LA)),_LY=E(_LX.a),_LZ=_Ly-_Lu|0;if(0>_LZ){return new F(function(){return _L8(_LZ,_Ls);});}else{if(_LZ>=_Ls){return new F(function(){return _L8(_LZ,_Ls);});}else{var _M0=E(_Lt[_LZ]),_M1=E(_M0.c),_M2=_M1.b,_M3=E(_M1.a),_M4=_M3.a,_M5=_M3.b,_M6=_M3.c,_M7=E(_M0.e),_M8=E(_M7.a),_M9=B(_Iw(_n2,_LI,_LJ,_LK,_LG,_M4,_M5,_M6,_M2)),_Ma=E(_M9.a),_Mb=B(_Iw(_n2,_Ma.a,_Ma.b,_Ma.c,_M9.b,_LI,_LJ,_LK,_LG)),_Mc=E(_Mb.a),_Md=E(_LY.a)+E(_LY.b)+E(_LY.c)+E(_LX.b)+E(_Mc.a)+E(_Mc.b)+E(_Mc.c)+E(_Mb.b);if(!_Md){var _Me=B(A2(_Ll,_Lr,_));return new T2(0,new T2(1,_oj,new T(function(){return E(E(_Me).a);})),new T(function(){return E(E(_Me).b);}));}else{var _Mf=new T(function(){return  -((B(_Jp(_ny,_LU.a,_LU.b,_LU.c,_LT.b,_LC,_LD,_LE,_LA))-B(_Jp(_ny,_M8.a,_M8.b,_M8.c,_M7.b,_LI,_LJ,_LK,_LG))-E(_Lm))/_Md);}),_Mg=function(_Mh,_Mi,_Mj,_Mk,_){var _Ml=new T(function(){var _Mm=function(_Mn,_Mo,_Mp,_Mq,_Mr){if(_Mn>_Ly){return E(_Mr);}else{if(_Ly>_Mo){return E(_Mr);}else{var _Ms=function(_){var _Mt=newArr(_Mp,_m2),_Mu=_Mt,_Mv=function(_Mw,_){while(1){if(_Mw!=_Mp){var _=_Mu[_Mw]=_Mq[_Mw],_Mx=_Mw+1|0;_Mw=_Mx;continue;}else{return E(_);}}},_=B(_Mv(0,_)),_My=_Ly-_Mn|0;if(0>_My){return new F(function(){return _L8(_My,_Mp);});}else{if(_My>=_Mp){return new F(function(){return _L8(_My,_Mp);});}else{var _=_Mu[_My]=new T(function(){var _Mz=E(_Mq[_My]),_MA=E(_Mz.e),_MB=E(_MA.a),_MC=B(_Iw(_n2,_M4,_M5,_M6,_M2,_LI,_LJ,_LK,_LG)),_MD=E(_MC.a),_ME=E(_Mf)*E(_Ln),_MF=B(_Iw(_n2,_MD.a,_MD.b,_MD.c,_MC.b,_ME,_ME,_ME,_ME)),_MG=E(_MF.a),_MH=B(_IH(_n2,_MB.a,_MB.b,_MB.c,_MA.b, -E(_MG.a), -E(_MG.b), -E(_MG.c), -E(_MF.b)));return {_:0,a:E(_Mz.a),b:E(_Mz.b),c:E(_Mz.c),d:E(_Mz.d),e:E(new T2(0,E(_MH.a),E(_MH.b))),f:E(_Mz.f),g:E(_Mz.g),h:_Mz.h,i:_Mz.i,j:_Mz.j};});return new T4(0,E(_Mn),E(_Mo),_Mp,_Mu);}}};return new F(function(){return _EK(_Ms);});}}};if(_Mh>_Lx){return B(_Mm(_Mh,_Mi,_Mj,_Mk,new T4(0,E(_Mh),E(_Mi),_Mj,_Mk)));}else{if(_Lx>_Mi){return B(_Mm(_Mh,_Mi,_Mj,_Mk,new T4(0,E(_Mh),E(_Mi),_Mj,_Mk)));}else{var _MI=function(_){var _MJ=newArr(_Mj,_m2),_MK=_MJ,_ML=function(_MM,_){while(1){if(_MM!=_Mj){var _=_MK[_MM]=_Mk[_MM],_MN=_MM+1|0;_MM=_MN;continue;}else{return E(_);}}},_=B(_ML(0,_)),_MO=_Lx-_Mh|0;if(0>_MO){return new F(function(){return _L3(_Mj,_MO);});}else{if(_MO>=_Mj){return new F(function(){return _L3(_Mj,_MO);});}else{var _=_MK[_MO]=new T(function(){var _MP=E(_Mk[_MO]),_MQ=E(_MP.e),_MR=E(_MQ.a),_MS=B(_Iw(_n2,_LQ,_LR,_LS,_LO,_LC,_LD,_LE,_LA)),_MT=E(_MS.a),_MU=E(_Mf)*E(_Ln),_MV=B(_Iw(_n2,_MT.a,_MT.b,_MT.c,_MS.b,_MU,_MU,_MU,_MU)),_MW=E(_MV.a),_MX=B(_IH(_n2,_MR.a,_MR.b,_MR.c,_MQ.b,_MW.a,_MW.b,_MW.c,_MV.b));return {_:0,a:E(_MP.a),b:E(_MP.b),c:E(_MP.c),d:E(_MP.d),e:E(new T2(0,E(_MX.a),E(_MX.b))),f:E(_MP.f),g:E(_MP.g),h:_MP.h,i:_MP.i,j:_MP.j};});return new T4(0,E(_Mh),E(_Mi),_Mj,_MK);}}},_MY=B(_EK(_MI));return B(_Mm(E(_MY.a),E(_MY.b),_MY.c,_MY.d,_MY));}}});return new T2(0,_oj,_Ml);};if(!E(_Lw.f)){var _MZ=B(_Mg(_Lu,_Lv,_Ls,_Lt,_)),_N0=B(A2(_Ll,new T(function(){return E(E(_MZ).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_MZ).a);}),new T(function(){return E(E(_N0).a);})),new T(function(){return E(E(_N0).b);}));}else{if(E(_Mf)<0){var _N1=B(A2(_Ll,_Lr,_));return new T2(0,new T2(1,_oj,new T(function(){return E(E(_N1).a);})),new T(function(){return E(E(_N1).b);}));}else{var _N2=B(_Mg(_Lu,_Lv,_Ls,_Lt,_)),_N3=B(A2(_Ll,new T(function(){return E(E(_N2).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_N2).a);}),new T(function(){return E(E(_N3).a);})),new T(function(){return E(E(_N3).b);}));}}}}}}}}}}}};return E(_Lp);}};return new F(function(){return _Lh(_Lf.a);});}},_N4=function(_,_N5){var _N6=new T(function(){return B(_Ld(E(_N5).a));}),_N7=function(_N8){var _N9=E(_N8);return (_N9==1)?E(new T2(1,_N6,_w)):new T2(1,_N6,new T(function(){return B(_N7(_N9-1|0));}));},_Na=B(_HI(B(_N7(5)),new T(function(){return E(E(_N5).b);}),_)),_Nb=new T(function(){return B(_Ig(_HH,_Fw,_Jg,new T(function(){return E(E(_Na).b);})));});return new T2(0,_oj,_Nb);},_Nc=function(_Nd,_Ne,_Nf,_Ng,_Nh){var _Ni=B(_8J(B(_8H(_Nd))));return new F(function(){return A3(_6X,_Ni,new T(function(){return B(A3(_8L,_Ni,_Ne,_Ng));}),new T(function(){return B(A3(_8L,_Ni,_Nf,_Nh));}));});},_Nj=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Nk=new T6(0,_KO,_KP,_w,_Nj,_KO,_KO),_Nl=new T(function(){return B(_KM(_Nk));}),_Nm=function(_){return new F(function(){return die(_Nl);});},_Nn=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_No=new T6(0,_KO,_KP,_w,_Nn,_KO,_KO),_Np=new T(function(){return B(_KM(_No));}),_Nq=function(_){return new F(function(){return die(_Np);});},_Nr=function(_Ns,_Nt,_Nu,_Nv){var _Nw=new T(function(){return B(_8J(new T(function(){return B(_8H(_Ns));})));}),_Nx=B(A2(_8s,_Nw,_8q));return new F(function(){return _p7(_Ns,_Nx,B(A2(_8s,_Nw,_8r)),_Nx);});},_Ny=false,_Nz=true,_NA=function(_NB){var _NC=E(_NB),_ND=_NC.b,_NE=E(_NC.d),_NF=E(_NC.e),_NG=E(_NF.a),_NH=E(_NC.g),_NI=B(A1(_ND,_NE.a)),_NJ=B(_pY(_ny,_NI.a,_NI.b,_NI.c,_NH.a,_NH.b,_NH.c));return {_:0,a:E(_NC.a),b:E(_ND),c:E(_NC.c),d:E(_NE),e:E(new T2(0,E(new T3(0,E(_NG.a)+E(_NJ.a)*1.0e-2,E(_NG.b)+E(_NJ.b)*1.0e-2,E(_NG.c)+E(_NJ.c)*1.0e-2)),E(_NF.b))),f:E(_NC.f),g:E(_NH),h:_NC.h,i:_NC.i,j:_NC.j};},_NK=new T(function(){return eval("__strict(collideBound)");}),_NL=new T(function(){return eval("__strict(mouseContact)");}),_NM=new T(function(){return eval("__strict(collide)");}),_NN=function(_NO){var _NP=E(_NO);if(!_NP._){return __Z;}else{return new F(function(){return _n(_NP.a,new T(function(){return B(_NN(_NP.b));},1));});}},_NQ=0,_NR=new T3(0,E(_NQ),E(_NQ),E(_NQ)),_NS=new T2(0,E(_NR),E(_NQ)),_NT=function(_NU,_){var _NV=B(_Ig(_HH,_Fw,_NA,_NU)),_NW=E(_NV.a),_NX=E(_NV.b);if(_NW<=_NX){var _NY=function(_NZ,_O0,_O1,_O2,_O3,_){if(_O0>_NZ){return new F(function(){return _Nq(_);});}else{if(_NZ>_O1){return new F(function(){return _Nq(_);});}else{var _O4=new T(function(){var _O5=_NZ-_O0|0;if(0>_O5){return B(_L8(_O5,_O2));}else{if(_O5>=_O2){return B(_L8(_O5,_O2));}else{return E(_O3[_O5]);}}}),_O6=function(_O7,_O8,_O9,_Oa,_Ob,_){var _Oc=E(_O7);if(!_Oc._){return new T2(0,_w,new T4(0,E(_O8),E(_O9),_Oa,_Ob));}else{var _Od=E(_Oc.a);if(_O8>_Od){return new F(function(){return _Nm(_);});}else{if(_Od>_O9){return new F(function(){return _Nm(_);});}else{var _Oe=_Od-_O8|0;if(0>_Oe){return new F(function(){return _L3(_Oa,_Oe);});}else{if(_Oe>=_Oa){return new F(function(){return _L3(_Oa,_Oe);});}else{var _Of=__app2(E(_NM),B(_EU(E(_O4))),B(_EU(E(_Ob[_Oe])))),_Og=__arr2lst(0,_Of),_Oh=B(_G9(_Og,_)),_Oi=B(_O6(_Oc.b,_O8,_O9,_Oa,_Ob,_)),_Oj=new T(function(){var _Ok=new T(function(){return _NZ!=_Od;}),_Ol=function(_Om){var _On=E(_Om);if(!_On._){return __Z;}else{var _Oo=_On.b,_Op=E(_On.a),_Oq=E(_Op.b),_Or=E(_Op.a),_Os=E(_Or.a),_Ot=E(_Or.b),_Ou=E(_Or.c),_Ov=E(_Oq.a),_Ow=E(_Oq.b),_Ox=E(_Oq.c),_Oy=E(_Op.c),_Oz=_Oy.a,_OA=_Oy.b,_OB=E(_Op.e),_OC=E(_Op.d),_OD=_OC.a,_OE=_OC.b,_OF=E(_Op.f),_OG=new T(function(){var _OH=B(_p7(_ny,_OF.a,_OF.b,_OF.c)),_OI=Math.sqrt(B(_Nc(_ny,_OD,_OE,_OD,_OE)));return new T3(0,_OI*E(_OH.a),_OI*E(_OH.b),_OI*E(_OH.c));}),_OJ=new T(function(){var _OK=B(_p7(_ny,_OB.a,_OB.b,_OB.c)),_OL=Math.sqrt(B(_Nc(_ny,_Oz,_OA,_Oz,_OA)));return new T3(0,_OL*E(_OK.a),_OL*E(_OK.b),_OL*E(_OK.c));}),_OM=new T(function(){var _ON=B(_Nr(_ny,_Ov,_Ow,_Ox));return new T3(0,E(_ON.a),E(_ON.b),E(_ON.c));}),_OO=new T(function(){var _OP=B(_Nr(_ny,_Os,_Ot,_Ou));return new T3(0,E(_OP.a),E(_OP.b),E(_OP.c));}),_OQ=_Ov+ -_Os,_OR=_Ow+ -_Ot,_OS=_Ox+ -_Ou,_OT=new T(function(){return Math.sqrt(B(_oX(_ny,_OQ,_OR,_OS,_OQ,_OR,_OS)));}),_OU=new T(function(){var _OV=1/E(_OT);return new T3(0,_OQ*_OV,_OR*_OV,_OS*_OV);}),_OW=new T(function(){if(!E(_Op.g)){return E(_OU);}else{var _OX=E(_OU);return new T3(0,-1*E(_OX.a),-1*E(_OX.b),-1*E(_OX.c));}}),_OY=new T(function(){if(!E(_Op.h)){return E(_OU);}else{var _OZ=E(_OU);return new T3(0,-1*E(_OZ.a),-1*E(_OZ.b),-1*E(_OZ.c));}});return (!E(_Ok))?new T2(1,new T(function(){var _P0=E(_OW),_P1=E(_P0.b),_P2=E(_P0.c),_P3=E(_P0.a),_P4=E(_OO),_P5=E(_P4.c),_P6=E(_P4.b),_P7=E(_P4.a),_P8=E(_OJ),_P9=E(_P8.c),_Pa=E(_P8.b),_Pb=E(_P8.a),_Pc=_P1*_P5-_P6*_P2,_Pd=_P2*_P7-_P5*_P3,_Pe=_P3*_P6-_P7*_P1,_Pf=B(_oX(_ny,_Pd*_P9-_Pa*_Pe,_Pe*_Pb-_P9*_Pc,_Pc*_Pa-_Pb*_Pd,_P7,_P6,_P5));return new T6(0,_NZ,_Od,E(new T2(0,E(new T3(0,E(_Pc),E(_Pd),E(_Pe))),E(_Pf))),E(_NS),_OT,_Ny);}),new T2(1,new T(function(){var _Pg=E(_OY),_Ph=E(_Pg.b),_Pi=E(_Pg.c),_Pj=E(_Pg.a),_Pk=E(_OM),_Pl=E(_Pk.c),_Pm=E(_Pk.b),_Pn=E(_Pk.a),_Po=E(_OG),_Pp=E(_Po.c),_Pq=E(_Po.b),_Pr=E(_Po.a),_Ps=_Ph*_Pl-_Pm*_Pi,_Pt=_Pi*_Pn-_Pl*_Pj,_Pu=_Pj*_Pm-_Pn*_Ph,_Pv=B(_oX(_ny,_Pt*_Pp-_Pq*_Pu,_Pu*_Pr-_Pp*_Ps,_Ps*_Pq-_Pr*_Pt,_Pn,_Pm,_Pl));return new T6(0,_NZ,_Od,E(_NS),E(new T2(0,E(new T3(0,E(_Ps),E(_Pt),E(_Pu))),E(_Pv))),_OT,_Ny);}),new T(function(){return B(_Ol(_Oo));}))):new T2(1,new T(function(){var _Pw=E(_OW),_Px=E(_Pw.b),_Py=E(_Pw.c),_Pz=E(_Pw.a),_PA=E(_OO),_PB=_PA.a,_PC=_PA.b,_PD=_PA.c,_PE=B(_pY(_ny,_Pz,_Px,_Py,_PB,_PC,_PD)),_PF=E(_OJ),_PG=E(_PF.c),_PH=E(_PF.b),_PI=E(_PF.a),_PJ=B(_oX(_ny,_Px*_PG-_PH*_Py,_Py*_PI-_PG*_Pz,_Pz*_PH-_PI*_Px,_PB,_PC,_PD)),_PK=E(_OY),_PL=E(_PK.b),_PM=E(_PK.c),_PN=E(_PK.a),_PO=E(_OM),_PP=_PO.a,_PQ=_PO.b,_PR=_PO.c,_PS=B(_pY(_ny,_PN,_PL,_PM,_PP,_PQ,_PR)),_PT=E(_OG),_PU=E(_PT.c),_PV=E(_PT.b),_PW=E(_PT.a),_PX=B(_oX(_ny,_PL*_PU-_PV*_PM,_PM*_PW-_PU*_PN,_PN*_PV-_PW*_PL,_PP,_PQ,_PR));return new T6(0,_NZ,_Od,E(new T2(0,E(new T3(0,E(_PE.a),E(_PE.b),E(_PE.c))),E(_PJ))),E(new T2(0,E(new T3(0,E(_PS.a),E(_PS.b),E(_PS.c))),E(_PX))),_OT,_Nz);}),new T(function(){return B(_Ol(_Oo));}));}};return B(_Ol(_Oh));});return new T2(0,new T2(1,_Oj,new T(function(){return E(E(_Oi).a);})),new T(function(){return E(E(_Oi).b);}));}}}}}},_PY=B(_O6(B(_wG(_NZ,_NX)),_O0,_O1,_O2,_O3,_)),_PZ=E(_O4),_Q0=E(_PZ.d).a,_Q1=__app1(E(_NK),B(_EU(_PZ))),_Q2=__arr2lst(0,_Q1),_Q3=B(_G9(_Q2,_)),_Q4=__app1(E(_NL),_NZ),_Q5=__arr2lst(0,_Q4),_Q6=B(_G9(_Q5,_));if(_NZ!=_NX){var _Q7=E(_PY),_Q8=E(_Q7.b),_Q9=B(_NY(_NZ+1|0,E(_Q8.a),E(_Q8.b),_Q8.c,_Q8.d,_)),_Qa=new T(function(){var _Qb=new T(function(){var _Qc=E(_Q0),_Qd=B(_Nr(_ny,_Qc.a,_Qc.b,_Qc.c));return new T3(0,E(_Qd.a),E(_Qd.b),E(_Qd.c));}),_Qe=new T(function(){var _Qf=new T(function(){return B(_NN(_Q7.a));}),_Qg=function(_Qh){var _Qi=E(_Qh);if(!_Qi._){return E(_Qf);}else{var _Qj=E(_Qi.a),_Qk=E(_Qj.b),_Ql=E(_Qj.a),_Qm=E(_Ql.a),_Qn=E(_Ql.b),_Qo=E(_Ql.c),_Qp=E(_Qj.c),_Qq=_Qp.a,_Qr=_Qp.b,_Qs=E(_Qj.e);return new T2(1,new T(function(){var _Qt=E(_Qk.a)+ -_Qm,_Qu=E(_Qk.b)+ -_Qn,_Qv=E(_Qk.c)+ -_Qo,_Qw=B(_Nr(_ny,_Qm,_Qn,_Qo)),_Qx=_Qw.a,_Qy=_Qw.b,_Qz=_Qw.c,_QA=Math.sqrt(B(_oX(_ny,_Qt,_Qu,_Qv,_Qt,_Qu,_Qv))),_QB=1/_QA,_QC=_Qt*_QB,_QD=_Qu*_QB,_QE=_Qv*_QB,_QF=B(_pY(_ny,_QC,_QD,_QE,_Qx,_Qy,_Qz)),_QG=B(_p7(_ny,_Qs.a,_Qs.b,_Qs.c)),_QH=Math.sqrt(B(_Nc(_ny,_Qq,_Qr,_Qq,_Qr))),_QI=_QH*E(_QG.a),_QJ=_QH*E(_QG.b),_QK=_QH*E(_QG.c),_QL=B(_oX(_ny,_QD*_QK-_QJ*_QE,_QE*_QI-_QK*_QC,_QC*_QJ-_QI*_QD,_Qx,_Qy,_Qz));return new T6(0,_NZ,_NZ,E(new T2(0,E(new T3(0,E(_QF.a),E(_QF.b),E(_QF.c))),E(_QL))),E(_NS),_QA,_Nz);}),new T(function(){return B(_Qg(_Qi.b));}));}};return B(_Qg(_Q3));}),_QM=function(_QN){var _QO=E(_QN);if(!_QO._){return E(_Qe);}else{var _QP=E(_QO.a),_QQ=E(_QP.b),_QR=new T(function(){var _QS=E(_Q0),_QT=E(_QQ.c)+ -E(_QS.c),_QU=E(_QQ.b)+ -E(_QS.b),_QV=E(_QQ.a)+ -E(_QS.a),_QW=Math.sqrt(B(_oX(_ny,_QV,_QU,_QT,_QV,_QU,_QT))),_QX=function(_QY,_QZ,_R0){var _R1=E(_Qb),_R2=_R1.a,_R3=_R1.b,_R4=_R1.c,_R5=B(_pY(_ny,_QY,_QZ,_R0,_R2,_R3,_R4)),_R6=B(_oX(_ny,_QZ*0-0*_R0,_R0*0-0*_QY,_QY*0-0*_QZ,_R2,_R3,_R4));return new T6(0,_NZ,_NZ,new T2(0,E(new T3(0,E(_R5.a),E(_R5.b),E(_R5.c))),E(_R6)),_NS,_QW,_Nz);};if(!E(_QP.g)){var _R7=1/_QW,_R8=B(_QX(_QV*_R7,_QU*_R7,_QT*_R7));return new T6(0,_R8.a,_R8.b,E(_R8.c),E(_R8.d),_R8.e,_R8.f);}else{var _R9=1/_QW,_Ra=B(_QX(-1*_QV*_R9,-1*_QU*_R9,-1*_QT*_R9));return new T6(0,_Ra.a,_Ra.b,E(_Ra.c),E(_Ra.d),_Ra.e,_Ra.f);}});return new T2(1,_QR,new T(function(){return B(_QM(_QO.b));}));}};return B(_QM(_Q6));});return new T2(0,new T2(1,_Qa,new T(function(){return E(E(_Q9).a);})),new T(function(){return E(E(_Q9).b);}));}else{var _Rb=new T(function(){var _Rc=new T(function(){var _Rd=E(_Q0),_Re=B(_Nr(_ny,_Rd.a,_Rd.b,_Rd.c));return new T3(0,E(_Re.a),E(_Re.b),E(_Re.c));}),_Rf=new T(function(){var _Rg=new T(function(){return B(_NN(E(_PY).a));}),_Rh=function(_Ri){var _Rj=E(_Ri);if(!_Rj._){return E(_Rg);}else{var _Rk=E(_Rj.a),_Rl=E(_Rk.b),_Rm=E(_Rk.a),_Rn=E(_Rm.a),_Ro=E(_Rm.b),_Rp=E(_Rm.c),_Rq=E(_Rk.c),_Rr=_Rq.a,_Rs=_Rq.b,_Rt=E(_Rk.e);return new T2(1,new T(function(){var _Ru=E(_Rl.a)+ -_Rn,_Rv=E(_Rl.b)+ -_Ro,_Rw=E(_Rl.c)+ -_Rp,_Rx=B(_Nr(_ny,_Rn,_Ro,_Rp)),_Ry=_Rx.a,_Rz=_Rx.b,_RA=_Rx.c,_RB=Math.sqrt(B(_oX(_ny,_Ru,_Rv,_Rw,_Ru,_Rv,_Rw))),_RC=1/_RB,_RD=_Ru*_RC,_RE=_Rv*_RC,_RF=_Rw*_RC,_RG=B(_pY(_ny,_RD,_RE,_RF,_Ry,_Rz,_RA)),_RH=B(_p7(_ny,_Rt.a,_Rt.b,_Rt.c)),_RI=Math.sqrt(B(_Nc(_ny,_Rr,_Rs,_Rr,_Rs))),_RJ=_RI*E(_RH.a),_RK=_RI*E(_RH.b),_RL=_RI*E(_RH.c),_RM=B(_oX(_ny,_RE*_RL-_RK*_RF,_RF*_RJ-_RL*_RD,_RD*_RK-_RJ*_RE,_Ry,_Rz,_RA));return new T6(0,_NZ,_NZ,E(new T2(0,E(new T3(0,E(_RG.a),E(_RG.b),E(_RG.c))),E(_RM))),E(_NS),_RB,_Nz);}),new T(function(){return B(_Rh(_Rj.b));}));}};return B(_Rh(_Q3));}),_RN=function(_RO){var _RP=E(_RO);if(!_RP._){return E(_Rf);}else{var _RQ=E(_RP.a),_RR=E(_RQ.b),_RS=new T(function(){var _RT=E(_Q0),_RU=E(_RR.c)+ -E(_RT.c),_RV=E(_RR.b)+ -E(_RT.b),_RW=E(_RR.a)+ -E(_RT.a),_RX=Math.sqrt(B(_oX(_ny,_RW,_RV,_RU,_RW,_RV,_RU))),_RY=function(_RZ,_S0,_S1){var _S2=E(_Rc),_S3=_S2.a,_S4=_S2.b,_S5=_S2.c,_S6=B(_pY(_ny,_RZ,_S0,_S1,_S3,_S4,_S5)),_S7=B(_oX(_ny,_S0*0-0*_S1,_S1*0-0*_RZ,_RZ*0-0*_S0,_S3,_S4,_S5));return new T6(0,_NZ,_NZ,new T2(0,E(new T3(0,E(_S6.a),E(_S6.b),E(_S6.c))),E(_S7)),_NS,_RX,_Nz);};if(!E(_RQ.g)){var _S8=1/_RX,_S9=B(_RY(_RW*_S8,_RV*_S8,_RU*_S8));return new T6(0,_S9.a,_S9.b,E(_S9.c),E(_S9.d),_S9.e,_S9.f);}else{var _Sa=1/_RX,_Sb=B(_RY(-1*_RW*_Sa,-1*_RV*_Sa,-1*_RU*_Sa));return new T6(0,_Sb.a,_Sb.b,E(_Sb.c),E(_Sb.d),_Sb.e,_Sb.f);}});return new T2(1,_RS,new T(function(){return B(_RN(_RP.b));}));}};return B(_RN(_Q6));});return new T2(0,new T2(1,_Rb,_w),new T(function(){return E(E(_PY).b);}));}}}},_Sc=B(_NY(_NW,_NW,_NX,_NV.c,_NV.d,_));return new F(function(){return _N4(_,_Sc);});}else{return new F(function(){return _N4(_,new T2(0,_w,_NV));});}},_Sd=new T(function(){return eval("__strict(passObject)");}),_Se=new T(function(){return eval("__strict(refresh)");}),_Sf=function(_Sg,_){var _Sh=__app0(E(_Se)),_Si=__app0(E(_EZ)),_Sj=E(_Sg),_Sk=_Sj.c,_Sl=_Sj.d,_Sm=E(_Sj.a),_Sn=E(_Sj.b);if(_Sm<=_Sn){if(_Sm>_Sn){return E(_EX);}else{if(0>=_Sk){return new F(function(){return _Fa(_Sk,0);});}else{var _So=E(_Sd),_Sp=__app2(_So,_Sm,B(_EU(E(_Sl[0]))));if(_Sm!=_Sn){var _Sq=function(_Sr,_){if(_Sm>_Sr){return E(_EX);}else{if(_Sr>_Sn){return E(_EX);}else{var _Ss=_Sr-_Sm|0;if(0>_Ss){return new F(function(){return _Fa(_Sk,_Ss);});}else{if(_Ss>=_Sk){return new F(function(){return _Fa(_Sk,_Ss);});}else{var _St=__app2(_So,_Sr,B(_EU(E(_Sl[_Ss]))));if(_Sr!=_Sn){var _Su=B(_Sq(_Sr+1|0,_));return new T2(1,_oj,_Su);}else{return _Ff;}}}}}},_Sv=B(_Sq(_Sm+1|0,_)),_Sw=__app0(E(_EY)),_Sx=B(_NT(_Sj,_));return new T(function(){return E(E(_Sx).b);});}else{var _Sy=__app0(E(_EY)),_Sz=B(_NT(_Sj,_));return new T(function(){return E(E(_Sz).b);});}}}}else{var _SA=__app0(E(_EY)),_SB=B(_NT(_Sj,_));return new T(function(){return E(E(_SB).b);});}},_SC=function(_SD,_){while(1){var _SE=E(_SD);if(!_SE._){return _oj;}else{var _SF=_SE.b,_SG=E(_SE.a);switch(_SG._){case 0:var _SH=B(A1(_SG.a,_));_SD=B(_n(_SF,new T2(1,_SH,_w)));continue;case 1:_SD=B(_n(_SF,_SG.a));continue;default:_SD=_SF;continue;}}}},_SI=function(_SJ,_SK,_){var _SL=E(_SJ);switch(_SL._){case 0:var _SM=B(A1(_SL.a,_));return new F(function(){return _SC(B(_n(_SK,new T2(1,_SM,_w))),_);});break;case 1:return new F(function(){return _SC(B(_n(_SK,_SL.a)),_);});break;default:return new F(function(){return _SC(_SK,_);});}},_SN=new T0(2),_SO=function(_SP){return new T0(2);},_SQ=function(_SR,_SS,_ST){return function(_){var _SU=E(_SR),_SV=rMV(_SU),_SW=E(_SV);if(!_SW._){var _SX=new T(function(){var _SY=new T(function(){return B(A1(_ST,_oj));});return B(_n(_SW.b,new T2(1,new T2(0,_SS,function(_SZ){return E(_SY);}),_w)));}),_=wMV(_SU,new T2(0,_SW.a,_SX));return _SN;}else{var _T0=E(_SW.a);if(!_T0._){var _=wMV(_SU,new T2(0,_SS,_w));return new T(function(){return B(A1(_ST,_oj));});}else{var _=wMV(_SU,new T1(1,_T0.b));return new T1(1,new T2(1,new T(function(){return B(A1(_ST,_oj));}),new T2(1,new T(function(){return B(A2(_T0.a,_SS,_SO));}),_w)));}}};},_T1=new T(function(){return E(_uc);}),_T2=new T(function(){return eval("window.requestAnimationFrame");}),_T3=new T1(1,_w),_T4=function(_T5,_T6){return function(_){var _T7=E(_T5),_T8=rMV(_T7),_T9=E(_T8);if(!_T9._){var _Ta=_T9.a,_Tb=E(_T9.b);if(!_Tb._){var _=wMV(_T7,_T3);return new T(function(){return B(A1(_T6,_Ta));});}else{var _Tc=E(_Tb.a),_=wMV(_T7,new T2(0,_Tc.a,_Tb.b));return new T1(1,new T2(1,new T(function(){return B(A1(_T6,_Ta));}),new T2(1,new T(function(){return B(A1(_Tc.b,_SO));}),_w)));}}else{var _Td=new T(function(){var _Te=function(_Tf){var _Tg=new T(function(){return B(A1(_T6,_Tf));});return function(_Th){return E(_Tg);};};return B(_n(_T9.a,new T2(1,_Te,_w)));}),_=wMV(_T7,new T1(1,_Td));return _SN;}};},_Ti=function(_Tj,_Tk){return new T1(0,B(_T4(_Tj,_Tk)));},_Tl=function(_Tm,_Tn){var _To=new T(function(){return new T1(0,B(_SQ(_Tm,_oj,_SO)));});return function(_){var _Tp=__createJSFunc(2,function(_Tq,_){var _Tr=B(_SI(_To,_w,_));return _T1;}),_Ts=__app1(E(_T2),_Tp);return new T(function(){return B(_Ti(_Tm,_Tn));});};},_Tt=new T1(1,_w),_Tu=function(_Tv,_Tw,_){var _Tx=function(_){var _Ty=nMV(_Tv),_Tz=_Ty;return new T(function(){var _TA=new T(function(){return B(_TB(_));}),_TC=function(_){var _TD=rMV(_Tz),_TE=B(A2(_Tw,_TD,_)),_=wMV(_Tz,_TE),_TF=function(_){var _TG=nMV(_Tt);return new T(function(){return new T1(0,B(_Tl(_TG,function(_TH){return E(_TA);})));});};return new T1(0,_TF);},_TI=new T(function(){return new T1(0,_TC);}),_TB=function(_TJ){return E(_TI);};return B(_TB(_));});};return new F(function(){return _SI(new T1(0,_Tx),_w,_);});},_TK=new T(function(){return eval("__strict(setBounds)");}),_TL=function(_){var _TM=__app3(E(_lr),E(_ls),E(_lV),E(_lq)),_TN=__app2(E(_TK),E(_iG),E(_iD));return new F(function(){return _Tu(_EN,_Sf,_);});},_TO=function(_){return new F(function(){return _TL(_);});};
var hasteMain = function() {B(A(_TO, [0]));};window.onload = hasteMain;