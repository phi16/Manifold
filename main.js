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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(",y:"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr(",z:"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("})"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=new T(function(){return B(unCStr("-("));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr(")"));}),_I=new T1(0,_H),_J=new T2(1,_I,_w),_K=new T(function(){return B(unCStr("."));}),_L=new T1(0,0),_M=function(_N){while(1){var _O=E(_N);if(!_O._){_N=new T1(1,I_fromInt(_O.a));continue;}else{return new F(function(){return I_toString(_O.a);});}}},_P=function(_Q,_R){return new F(function(){return _n(fromJSStr(B(_M(_Q))),_R);});},_S=function(_T,_U){var _V=E(_T);if(!_V._){var _W=_V.a,_X=E(_U);return (_X._==0)?_W<_X.a:I_compareInt(_X.a,_W)>0;}else{var _Y=_V.a,_Z=E(_U);return (_Z._==0)?I_compareInt(_Y,_Z.a)<0:I_compare(_Y,_Z.a)<0;}},_10=41,_11=40,_12=new T1(0,0),_13=function(_14,_15,_16){if(_14<=6){return new F(function(){return _P(_15,_16);});}else{if(!B(_S(_15,_12))){return new F(function(){return _P(_15,_16);});}else{return new T2(1,_11,new T(function(){return B(_n(fromJSStr(B(_M(_15))),new T2(1,_10,_16)));}));}}},_17=new T(function(){return B(_13(0,_L,_w));}),_18=new T(function(){return B(_n(_17,_K));}),_19=new T1(0,_18),_1a=new T2(1,_19,_J),_1b=new T2(1,_G,_1a),_1c=new T1(1,_1b),_1d=new T2(1,_1c,_E),_1e=new T2(1,_B,_1d),_1f=new T2(1,_1c,_1e),_1g=new T2(1,_z,_1f),_1h=new T2(1,_1c,_1g),_1i=new T(function(){return B(unCStr("({x:"));}),_1j=new T1(0,_1i),_1k=new T2(1,_1j,_1h),_1l=function(_1m){return E(_1m);},_1n=new T(function(){return toJSStr(B(_e(_x,_1l,_1k)));}),_1o=new T1(0,1),_1p=new T(function(){return B(_13(0,_1o,_w));}),_1q=new T(function(){return B(_n(_1p,_K));}),_1r=new T1(0,_1q),_1s=new T2(1,_1r,_J),_1t=new T2(1,_G,_1s),_1u=new T(function(){return toJSStr(B(_e(_x,_1l,_1t)));}),_1v=function(_1w,_1x,_1y){var _1z=E(_1y);if(!_1z._){return new F(function(){return A1(_1x,_1z.a);});}else{var _1A=new T(function(){return B(_0(_1w));}),_1B=new T(function(){return B(_2(_1w));}),_1C=function(_1D){var _1E=E(_1D);if(!_1E._){return E(_1B);}else{return new F(function(){return A2(_1A,new T(function(){return B(_1v(_1w,_1x,_1E.a));}),new T(function(){return B(_1C(_1E.b));}));});}};return new F(function(){return _1C(_1z.a);});}},_1F=function(_1G,_1H,_1I){var _1J=new T(function(){return B(_0(_1G));}),_1K=new T(function(){return B(_2(_1G));}),_1L=function(_1M){var _1N=E(_1M);if(!_1N._){return E(_1K);}else{return new F(function(){return A2(_1J,new T(function(){return B(_1v(_1G,_1H,_1N.a));}),new T(function(){return B(_1L(_1N.b));}));});}};return new F(function(){return _1L(_1I);});},_1O=new T(function(){return B(unCStr("-("));}),_1P=new T1(0,_1O),_1Q=new T(function(){return B(unCStr(")"));}),_1R=new T1(0,_1Q),_1S=new T2(1,_1R,_w),_1T=new T(function(){return B(unCStr("."));}),_1U=new T(function(){return B(_13(0,_1o,_w));}),_1V=new T(function(){return B(_n(_1U,_1T));}),_1W=new T1(0,_1V),_1X=new T2(1,_1W,_1S),_1Y=new T2(1,_1P,_1X),_1Z=new T(function(){return toJSStr(B(_1F(_x,_1l,_1Y)));}),_20=new T(function(){return eval("__strict(compile)");}),_21=new T(function(){return B(unCStr(","));}),_22=new T1(0,_21),_23=new T(function(){return B(unCStr("pow("));}),_24=new T1(0,_23),_25=function(_26,_27){return new T1(1,new T2(1,_24,new T2(1,_26,new T2(1,_22,new T2(1,_27,_1S)))));},_28=new T(function(){return B(unCStr("acos("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1S)));},_2c=new T(function(){return B(unCStr("acosh("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1S)));},_2g=new T(function(){return B(unCStr("asin("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1S)));},_2k=new T(function(){return B(unCStr("asinh("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1S)));},_2o=new T(function(){return B(unCStr("atan("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1S)));},_2s=new T(function(){return B(unCStr("atanh("));}),_2t=new T1(0,_2s),_2u=function(_2v){return new T1(1,new T2(1,_2t,new T2(1,_2v,_1S)));},_2w=new T(function(){return B(unCStr("cos("));}),_2x=new T1(0,_2w),_2y=function(_2z){return new T1(1,new T2(1,_2x,new T2(1,_2z,_1S)));},_2A=new T(function(){return B(unCStr("cosh("));}),_2B=new T1(0,_2A),_2C=function(_2D){return new T1(1,new T2(1,_2B,new T2(1,_2D,_1S)));},_2E=new T(function(){return B(unCStr("exp("));}),_2F=new T1(0,_2E),_2G=function(_2H){return new T1(1,new T2(1,_2F,new T2(1,_2H,_1S)));},_2I=new T(function(){return B(unCStr("log("));}),_2J=new T1(0,_2I),_2K=function(_2L){return new T1(1,new T2(1,_2J,new T2(1,_2L,_1S)));},_2M=new T(function(){return B(unCStr(")/log("));}),_2N=new T1(0,_2M),_2O=function(_2P,_2Q){return new T1(1,new T2(1,_2J,new T2(1,_2Q,new T2(1,_2N,new T2(1,_2P,_1S)))));},_2R=new T(function(){return B(unCStr("pi"));}),_2S=new T1(0,_2R),_2T=new T(function(){return B(unCStr("sin("));}),_2U=new T1(0,_2T),_2V=function(_2W){return new T1(1,new T2(1,_2U,new T2(1,_2W,_1S)));},_2X=new T(function(){return B(unCStr("sinh("));}),_2Y=new T1(0,_2X),_2Z=function(_30){return new T1(1,new T2(1,_2Y,new T2(1,_30,_1S)));},_31=new T(function(){return B(unCStr("sqrt("));}),_32=new T1(0,_31),_33=function(_34){return new T1(1,new T2(1,_32,new T2(1,_34,_1S)));},_35=new T(function(){return B(unCStr("tan("));}),_36=new T1(0,_35),_37=function(_38){return new T1(1,new T2(1,_36,new T2(1,_38,_1S)));},_39=new T(function(){return B(unCStr("tanh("));}),_3a=new T1(0,_39),_3b=function(_3c){return new T1(1,new T2(1,_3a,new T2(1,_3c,_1S)));},_3d=new T(function(){return B(unCStr("("));}),_3e=new T1(0,_3d),_3f=new T(function(){return B(unCStr(")/("));}),_3g=new T1(0,_3f),_3h=function(_3i,_3j){return new T1(1,new T2(1,_3e,new T2(1,_3i,new T2(1,_3g,new T2(1,_3j,_1S)))));},_3k=new T1(0,1),_3l=function(_3m,_3n){var _3o=E(_3m);if(!_3o._){var _3p=_3o.a,_3q=E(_3n);if(!_3q._){var _3r=_3q.a;return (_3p!=_3r)?(_3p>_3r)?2:0:1;}else{var _3s=I_compareInt(_3q.a,_3p);return (_3s<=0)?(_3s>=0)?1:2:0;}}else{var _3t=_3o.a,_3u=E(_3n);if(!_3u._){var _3v=I_compareInt(_3t,_3u.a);return (_3v>=0)?(_3v<=0)?1:2:0;}else{var _3w=I_compare(_3t,_3u.a);return (_3w>=0)?(_3w<=0)?1:2:0;}}},_3x=new T(function(){return B(unCStr("base"));}),_3y=new T(function(){return B(unCStr("GHC.Exception"));}),_3z=new T(function(){return B(unCStr("ArithException"));}),_3A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3x,_3y,_3z),_3B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3A,_w,_w),_3C=function(_3D){return E(_3B);},_3E=function(_3F){return E(E(_3F).a);},_3G=function(_3H,_3I,_3J){var _3K=B(A1(_3H,_)),_3L=B(A1(_3I,_)),_3M=hs_eqWord64(_3K.a,_3L.a);if(!_3M){return __Z;}else{var _3N=hs_eqWord64(_3K.b,_3L.b);return (!_3N)?__Z:new T1(1,_3J);}},_3O=function(_3P){var _3Q=E(_3P);return new F(function(){return _3G(B(_3E(_3Q.a)),_3C,_3Q.b);});},_3R=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3S=new T(function(){return B(unCStr("denormal"));}),_3T=new T(function(){return B(unCStr("divide by zero"));}),_3U=new T(function(){return B(unCStr("loss of precision"));}),_3V=new T(function(){return B(unCStr("arithmetic underflow"));}),_3W=new T(function(){return B(unCStr("arithmetic overflow"));}),_3X=function(_3Y,_3Z){switch(E(_3Y)){case 0:return new F(function(){return _n(_3W,_3Z);});break;case 1:return new F(function(){return _n(_3V,_3Z);});break;case 2:return new F(function(){return _n(_3U,_3Z);});break;case 3:return new F(function(){return _n(_3T,_3Z);});break;case 4:return new F(function(){return _n(_3S,_3Z);});break;default:return new F(function(){return _n(_3R,_3Z);});}},_40=function(_41){return new F(function(){return _3X(_41,_w);});},_42=function(_43,_44,_45){return new F(function(){return _3X(_44,_45);});},_46=44,_47=93,_48=91,_49=function(_4a,_4b,_4c){var _4d=E(_4b);if(!_4d._){return new F(function(){return unAppCStr("[]",_4c);});}else{var _4e=new T(function(){var _4f=new T(function(){var _4g=function(_4h){var _4i=E(_4h);if(!_4i._){return E(new T2(1,_47,_4c));}else{var _4j=new T(function(){return B(A2(_4a,_4i.a,new T(function(){return B(_4g(_4i.b));})));});return new T2(1,_46,_4j);}};return B(_4g(_4d.b));});return B(A2(_4a,_4d.a,_4f));});return new T2(1,_48,_4e);}},_4k=function(_4l,_4m){return new F(function(){return _49(_3X,_4l,_4m);});},_4n=new T3(0,_42,_40,_4k),_4o=new T(function(){return new T5(0,_3C,_4n,_4p,_3O,_40);}),_4p=function(_4q){return new T2(0,_4o,_4q);},_4r=3,_4s=new T(function(){return B(_4p(_4r));}),_4t=new T(function(){return die(_4s);}),_4u=function(_4v,_4w){var _4x=E(_4v);return (_4x._==0)?_4x.a*Math.pow(2,_4w):I_toNumber(_4x.a)*Math.pow(2,_4w);},_4y=function(_4z,_4A){var _4B=E(_4z);if(!_4B._){var _4C=_4B.a,_4D=E(_4A);return (_4D._==0)?_4C==_4D.a:(I_compareInt(_4D.a,_4C)==0)?true:false;}else{var _4E=_4B.a,_4F=E(_4A);return (_4F._==0)?(I_compareInt(_4E,_4F.a)==0)?true:false:(I_compare(_4E,_4F.a)==0)?true:false;}},_4G=function(_4H){var _4I=E(_4H);if(!_4I._){return E(_4I.a);}else{return new F(function(){return I_toInt(_4I.a);});}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a,_4Q=addC(_4N,_4P);if(!E(_4Q.b)){return new T1(0,_4Q.a);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R._){_4K=_4M;_4L=new T1(1,I_fromInt(_4R.a));continue;}else{return new T1(1,I_add(_4M.a,_4R.a));}}}},_4S=function(_4T,_4U){while(1){var _4V=E(_4T);if(!_4V._){var _4W=E(_4V.a);if(_4W==(-2147483648)){_4T=new T1(1,I_fromInt(-2147483648));continue;}else{var _4X=E(_4U);if(!_4X._){var _4Y=_4X.a;return new T2(0,new T1(0,quot(_4W,_4Y)),new T1(0,_4W%_4Y));}else{_4T=new T1(1,I_fromInt(_4W));_4U=_4X;continue;}}}else{var _4Z=E(_4U);if(!_4Z._){_4T=_4V;_4U=new T1(1,I_fromInt(_4Z.a));continue;}else{var _50=I_quotRem(_4V.a,_4Z.a);return new T2(0,new T1(1,_50.a),new T1(1,_50.b));}}}},_51=new T1(0,0),_52=function(_53,_54){while(1){var _55=E(_53);if(!_55._){_53=new T1(1,I_fromInt(_55.a));continue;}else{return new T1(1,I_shiftLeft(_55.a,_54));}}},_56=function(_57,_58,_59){if(!B(_4y(_59,_51))){var _5a=B(_4S(_58,_59)),_5b=_5a.a;switch(B(_3l(B(_52(_5a.b,1)),_59))){case 0:return new F(function(){return _4u(_5b,_57);});break;case 1:if(!(B(_4G(_5b))&1)){return new F(function(){return _4u(_5b,_57);});}else{return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}break;default:return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}}else{return E(_4t);}},_5c=function(_5d,_5e){var _5f=E(_5d);if(!_5f._){var _5g=_5f.a,_5h=E(_5e);return (_5h._==0)?_5g>_5h.a:I_compareInt(_5h.a,_5g)<0;}else{var _5i=_5f.a,_5j=E(_5e);return (_5j._==0)?I_compareInt(_5i,_5j.a)>0:I_compare(_5i,_5j.a)>0;}},_5k=new T1(0,1),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5n=new T(function(){return B(unCStr("PatternMatchFail"));}),_5o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5l,_5m,_5n),_5p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5o,_w,_w),_5q=function(_5r){return E(_5p);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _3G(B(_3E(_5u.a)),_5q,_5u.b);});},_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return new T2(0,_5z,_5y);},_5A=function(_5B,_5C){return new F(function(){return _n(E(_5B).a,_5C);});},_5D=function(_5E,_5F){return new F(function(){return _49(_5A,_5E,_5F);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _n(E(_5I).a,_5J);});},_5K=new T3(0,_5G,_5v,_5D),_5z=new T(function(){return new T5(0,_5q,_5K,_5x,_5s,_5v);}),_5L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5M=function(_5N){return E(E(_5N).c);},_5O=function(_5P,_5Q){return new F(function(){return die(new T(function(){return B(A2(_5M,_5Q,_5P));}));});},_5R=function(_5S,_4q){return new F(function(){return _5O(_5S,_4q);});},_5T=function(_5U,_5V){var _5W=E(_5V);if(!_5W._){return new T2(0,_w,_w);}else{var _5X=_5W.a;if(!B(A1(_5U,_5X))){return new T2(0,_w,_5W);}else{var _5Y=new T(function(){var _5Z=B(_5T(_5U,_5W.b));return new T2(0,_5Z.a,_5Z.b);});return new T2(0,new T2(1,_5X,new T(function(){return E(E(_5Y).a);})),new T(function(){return E(E(_5Y).b);}));}}},_60=32,_61=new T(function(){return B(unCStr("\n"));}),_62=function(_63){return (E(_63)==124)?false:true;},_64=function(_65,_66){var _67=B(_5T(_62,B(unCStr(_65)))),_68=_67.a,_69=function(_6a,_6b){var _6c=new T(function(){var _6d=new T(function(){return B(_n(_66,new T(function(){return B(_n(_6b,_61));},1)));});return B(unAppCStr(": ",_6d));},1);return new F(function(){return _n(_6a,_6c);});},_6e=E(_67.b);if(!_6e._){return new F(function(){return _69(_68,_w);});}else{if(E(_6e.a)==124){return new F(function(){return _69(_68,new T2(1,_60,_6e.b));});}else{return new F(function(){return _69(_68,_w);});}}},_6f=function(_6g){return new F(function(){return _5R(new T1(0,new T(function(){return B(_64(_6g,_5L));})),_5z);});},_6h=function(_6i){var _6j=function(_6k,_6l){while(1){if(!B(_S(_6k,_6i))){if(!B(_5c(_6k,_6i))){if(!B(_4y(_6k,_6i))){return new F(function(){return _6f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_6l);}}else{return _6l-1|0;}}else{var _6m=B(_52(_6k,1)),_6n=_6l+1|0;_6k=_6m;_6l=_6n;continue;}}};return new F(function(){return _6j(_5k,0);});},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){var _6r=_6q.a>>>0;if(!_6r){return -1;}else{var _6s=function(_6t,_6u){while(1){if(_6t>=_6r){if(_6t<=_6r){if(_6t!=_6r){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6u);}}else{return _6u-1|0;}}else{var _6v=imul(_6t,2)>>>0,_6w=_6u+1|0;_6t=_6v;_6u=_6w;continue;}}};return new F(function(){return _6s(1,0);});}}else{return new F(function(){return _6h(_6q);});}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){var _6A=_6z.a>>>0;if(!_6A){return new T2(0,-1,0);}else{var _6B=function(_6C,_6D){while(1){if(_6C>=_6A){if(_6C<=_6A){if(_6C!=_6A){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6D);}}else{return _6D-1|0;}}else{var _6E=imul(_6C,2)>>>0,_6F=_6D+1|0;_6C=_6E;_6D=_6F;continue;}}};return new T2(0,B(_6B(1,0)),(_6A&_6A-1>>>0)>>>0&4294967295);}}else{var _6G=_6z.a;return new T2(0,B(_6o(_6z)),I_compareInt(I_and(_6G,I_sub(_6G,I_fromInt(1))),0));}},_6H=function(_6I,_6J){var _6K=E(_6I);if(!_6K._){var _6L=_6K.a,_6M=E(_6J);return (_6M._==0)?_6L<=_6M.a:I_compareInt(_6M.a,_6L)>=0;}else{var _6N=_6K.a,_6O=E(_6J);return (_6O._==0)?I_compareInt(_6N,_6O.a)<=0:I_compare(_6N,_6O.a)<=0;}},_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){var _6T=_6S.a,_6U=E(_6R);if(!_6U._){return new T1(0,(_6T>>>0&_6U.a>>>0)>>>0&4294967295);}else{_6Q=new T1(1,I_fromInt(_6T));_6R=_6U;continue;}}else{var _6V=E(_6R);if(!_6V._){_6Q=_6S;_6R=new T1(1,I_fromInt(_6V.a));continue;}else{return new T1(1,I_and(_6S.a,_6V.a));}}}},_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){var _70=_6Z.a,_71=E(_6Y);if(!_71._){var _72=_71.a,_73=subC(_70,_72);if(!E(_73.b)){return new T1(0,_73.a);}else{_6X=new T1(1,I_fromInt(_70));_6Y=new T1(1,I_fromInt(_72));continue;}}else{_6X=new T1(1,I_fromInt(_70));_6Y=_71;continue;}}else{var _74=E(_6Y);if(!_74._){_6X=_6Z;_6Y=new T1(1,I_fromInt(_74.a));continue;}else{return new T1(1,I_sub(_6Z.a,_74.a));}}}},_75=new T1(0,2),_76=function(_77,_78){var _79=E(_77);if(!_79._){var _7a=(_79.a>>>0&(2<<_78>>>0)-1>>>0)>>>0,_7b=1<<_78>>>0;return (_7b<=_7a)?(_7b>=_7a)?1:2:0;}else{var _7c=B(_6P(_79,B(_6W(B(_52(_75,_78)),_5k)))),_7d=B(_52(_5k,_78));return (!B(_5c(_7d,_7c)))?(!B(_S(_7d,_7c)))?1:2:0;}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){_7f=new T1(1,I_fromInt(_7h.a));continue;}else{return new T1(1,I_shiftRight(_7h.a,_7g));}}},_7i=function(_7j,_7k,_7l,_7m){var _7n=B(_6x(_7m)),_7o=_7n.a;if(!E(_7n.b)){var _7p=B(_6o(_7l));if(_7p<((_7o+_7j|0)-1|0)){var _7q=_7o+(_7j-_7k|0)|0;if(_7q>0){if(_7q>_7p){if(_7q<=(_7p+1|0)){if(!E(B(_6x(_7l)).b)){return 0;}else{return new F(function(){return _4u(_3k,_7j-_7k|0);});}}else{return 0;}}else{var _7r=B(_7e(_7l,_7q));switch(B(_76(_7l,_7q-1|0))){case 0:return new F(function(){return _4u(_7r,_7j-_7k|0);});break;case 1:if(!(B(_4G(_7r))&1)){return new F(function(){return _4u(_7r,_7j-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}break;default:return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}}}else{return new F(function(){return _4u(_7l,(_7j-_7k|0)-_7q|0);});}}else{if(_7p>=_7k){var _7s=B(_7e(_7l,(_7p+1|0)-_7k|0));switch(B(_76(_7l,_7p-_7k|0))){case 0:return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});break;case 2:return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});break;default:if(!(B(_4G(_7s))&1)){return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});}}}else{return new F(function(){return _4u(_7l, -_7o);});}}}else{var _7t=B(_6o(_7l))-_7o|0,_7u=function(_7v){var _7w=function(_7x,_7y){if(!B(_6H(B(_52(_7y,_7k)),_7x))){return new F(function(){return _56(_7v-_7k|0,_7x,_7y);});}else{return new F(function(){return _56((_7v-_7k|0)+1|0,_7x,B(_52(_7y,1)));});}};if(_7v>=_7k){if(_7v!=_7k){return new F(function(){return _7w(_7l,new T(function(){return B(_52(_7m,_7v-_7k|0));}));});}else{return new F(function(){return _7w(_7l,_7m);});}}else{return new F(function(){return _7w(new T(function(){return B(_52(_7l,_7k-_7v|0));}),_7m);});}};if(_7j>_7t){return new F(function(){return _7u(_7j);});}else{return new F(function(){return _7u(_7t);});}}},_7z=new T1(0,2147483647),_7A=new T(function(){return B(_4J(_7z,_5k));}),_7B=function(_7C){var _7D=E(_7C);if(!_7D._){var _7E=E(_7D.a);return (_7E==(-2147483648))?E(_7A):new T1(0, -_7E);}else{return new T1(1,I_negate(_7D.a));}},_7F=new T(function(){return 0/0;}),_7G=new T(function(){return -1/0;}),_7H=new T(function(){return 1/0;}),_7I=0,_7J=function(_7K,_7L){if(!B(_4y(_7L,_51))){if(!B(_4y(_7K,_51))){if(!B(_S(_7K,_51))){return new F(function(){return _7i(-1021,53,_7K,_7L);});}else{return  -B(_7i(-1021,53,B(_7B(_7K)),_7L));}}else{return E(_7I);}}else{return (!B(_4y(_7K,_51)))?(!B(_S(_7K,_51)))?E(_7H):E(_7G):E(_7F);}},_7M=function(_7N){return new T1(0,new T(function(){var _7O=E(_7N),_7P=jsShow(B(_7J(_7O.a,_7O.b)));return fromJSStr(_7P);}));},_7Q=new T(function(){return B(unCStr("1./("));}),_7R=new T1(0,_7Q),_7S=function(_7T){return new T1(1,new T2(1,_7R,new T2(1,_7T,_1S)));},_7U=new T(function(){return B(unCStr(")+("));}),_7V=new T1(0,_7U),_7W=function(_7X,_7Y){return new T1(1,new T2(1,_3e,new T2(1,_7X,new T2(1,_7V,new T2(1,_7Y,_1S)))));},_7Z=function(_80){return new T1(1,new T2(1,_1P,new T2(1,_80,_1S)));},_81=new T(function(){return B(unCStr(")*("));}),_82=new T1(0,_81),_83=function(_84,_85){return new T1(1,new T2(1,_3e,new T2(1,_84,new T2(1,_82,new T2(1,_85,_1S)))));},_86=function(_87){return E(E(_87).a);},_88=function(_89){return E(E(_89).d);},_8a=function(_8b,_8c){return new F(function(){return A3(_86,_8d,_8b,new T(function(){return B(A2(_88,_8d,_8c));}));});},_8e=new T(function(){return B(unCStr("abs("));}),_8f=new T1(0,_8e),_8g=function(_8h){return new T1(1,new T2(1,_8f,new T2(1,_8h,_1S)));},_8i=function(_8j){return new T1(0,new T(function(){return B(_n(B(_13(0,_8j,_w)),_1T));}));},_8k=new T(function(){return B(unCStr("sign("));}),_8l=new T1(0,_8k),_8m=function(_8n){return new T1(1,new T2(1,_8l,new T2(1,_8n,_1S)));},_8d=new T(function(){return {_:0,a:_7W,b:_8a,c:_83,d:_7Z,e:_8g,f:_8m,g:_8i};}),_8o=new T4(0,_8d,_3h,_7S,_7M),_8p={_:0,a:_8o,b:_2S,c:_2G,d:_2K,e:_33,f:_25,g:_2O,h:_2V,i:_2y,j:_37,k:_2i,l:_2a,m:_2q,n:_2Z,o:_2C,p:_3b,q:_2m,r:_2e,s:_2u},_8q=function(_8r){return E(E(_8r).a);},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v){return E(E(_8v).c);},_8w=function(_8x,_8y,_8z,_8A,_8B,_8C,_8D){var _8E=B(_8s(B(_8q(_8x)))),_8F=new T(function(){return B(A3(_86,_8E,new T(function(){return B(A3(_8u,_8E,_8y,_8B));}),new T(function(){return B(A3(_8u,_8E,_8z,_8C));})));});return new F(function(){return A3(_86,_8E,_8F,new T(function(){return B(A3(_8u,_8E,_8A,_8D));}));});},_8G=function(_8H){return E(E(_8H).b);},_8I=function(_8J){return E(E(_8J).g);},_8K=function(_8L){return E(E(_8L).e);},_8M=function(_8N,_8O){var _8P=B(_8s(B(_8q(_8N)))),_8Q=new T(function(){return B(A2(_8K,_8N,new T(function(){var _8R=E(_8O),_8S=_8R.a,_8T=_8R.b,_8U=_8R.c;return B(_8w(_8N,_8S,_8T,_8U,_8S,_8T,_8U));})));});return new F(function(){return A3(_8G,_8P,_8Q,new T(function(){return B(A2(_8I,_8P,_1o));}));});},_8V=new T(function(){return B(unCStr("x"));}),_8W=new T1(0,_8V),_8X=new T(function(){return B(unCStr("y"));}),_8Y=new T1(0,_8X),_8Z=new T(function(){return B(unCStr("z"));}),_90=new T1(0,_8Z),_91=new T3(0,E(_8W),E(_8Y),E(_90)),_92=new T(function(){return B(_8M(_8p,_91));}),_93=new T(function(){return toJSStr(B(_1v(_x,_1l,_92)));}),_94=new T(function(){return B(unCStr("(/=) is not defined"));}),_95=new T(function(){return B(err(_94));}),_96=new T(function(){return B(unCStr("(==) is not defined"));}),_97=new T(function(){return B(err(_96));}),_98=new T2(0,_97,_95),_99=new T(function(){return B(unCStr("(<) is not defined"));}),_9a=new T(function(){return B(err(_99));}),_9b=new T(function(){return B(unCStr("(<=) is not defined"));}),_9c=new T(function(){return B(err(_9b));}),_9d=new T(function(){return B(unCStr("(>) is not defined"));}),_9e=new T(function(){return B(err(_9d));}),_9f=new T(function(){return B(unCStr("(>=) is not defined"));}),_9g=new T(function(){return B(err(_9f));}),_9h=new T(function(){return B(unCStr("compare is not defined"));}),_9i=new T(function(){return B(err(_9h));}),_9j=new T(function(){return B(unCStr("max("));}),_9k=new T1(0,_9j),_9l=function(_9m,_9n){return new T1(1,new T2(1,_9k,new T2(1,_9m,new T2(1,_22,new T2(1,_9n,_1S)))));},_9o=new T(function(){return B(unCStr("min("));}),_9p=new T1(0,_9o),_9q=function(_9r,_9s){return new T1(1,new T2(1,_9p,new T2(1,_9r,new T2(1,_22,new T2(1,_9s,_1S)))));},_9t={_:0,a:_98,b:_9i,c:_9a,d:_9c,e:_9e,f:_9g,g:_9l,h:_9q},_9u=new T2(0,_8p,_9t),_9v=function(_9w,_9x){var _9y=E(_9w);return E(_9x);},_9z=function(_9A,_9B){var _9C=E(_9B);return E(_9A);},_9D=function(_9E,_9F){var _9G=E(_9E),_9H=E(_9F);return new T3(0,E(B(A1(_9G.a,_9H.a))),E(B(A1(_9G.b,_9H.b))),E(B(A1(_9G.c,_9H.c))));},_9I=function(_9J,_9K,_9L){return new T3(0,E(_9J),E(_9K),E(_9L));},_9M=function(_9N){return new F(function(){return _9I(_9N,_9N,_9N);});},_9O=function(_9P,_9Q){var _9R=E(_9Q),_9S=E(_9P);return new T3(0,E(_9S),E(_9S),E(_9S));},_9T=function(_9U,_9V){var _9W=E(_9V);return new T3(0,E(B(A1(_9U,_9W.a))),E(B(A1(_9U,_9W.b))),E(B(A1(_9U,_9W.c))));},_9X=new T2(0,_9T,_9O),_9Y=new T5(0,_9X,_9M,_9D,_9v,_9z),_9Z=new T1(0,0),_a0=function(_a1){var _a2=B(A2(_8I,_a1,_1o)),_a3=B(A2(_8I,_a1,_9Z));return new T3(0,E(new T3(0,E(_a2),E(_a3),E(_a3))),E(new T3(0,E(_a3),E(_a2),E(_a3))),E(new T3(0,E(_a3),E(_a3),E(_a2))));},_a4=function(_a5){return E(E(_a5).a);},_a6=function(_a7){return E(E(_a7).f);},_a8=function(_a9){return E(E(_a9).b);},_aa=function(_ab){return E(E(_ab).c);},_ac=function(_ad){return E(E(_ad).a);},_ae=function(_af){return E(E(_af).d);},_ag=function(_ah,_ai,_aj,_ak,_al){var _am=new T(function(){return E(E(E(_ah).c).a);}),_an=new T(function(){var _ao=E(_ah).a,_ap=new T(function(){var _aq=new T(function(){return B(_8q(_am));}),_ar=new T(function(){return B(_8s(_aq));}),_as=new T(function(){return B(A2(_ae,_am,_ai));}),_at=new T(function(){return B(A3(_a6,_am,_ai,_ak));}),_au=function(_av,_aw){var _ax=new T(function(){var _ay=new T(function(){return B(A3(_a8,_aq,new T(function(){return B(A3(_8u,_ar,_ak,_av));}),_ai));});return B(A3(_86,_ar,_ay,new T(function(){return B(A3(_8u,_ar,_aw,_as));})));});return new F(function(){return A3(_8u,_ar,_at,_ax);});};return B(A3(_ac,B(_a4(_ao)),_au,_aj));});return B(A3(_aa,_ao,_ap,_al));});return new T2(0,new T(function(){return B(A3(_a6,_am,_ai,_ak));}),_an);},_az=function(_aA,_aB,_aC,_aD){var _aE=E(_aC),_aF=E(_aD),_aG=B(_ag(_aB,_aE.a,_aE.b,_aF.a,_aF.b));return new T2(0,_aG.a,_aG.b);},_aH=new T1(0,1),_aI=function(_aJ){return E(E(_aJ).l);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8q(_aO));}),_aR=new T(function(){var _aS=B(_8s(_aQ)),_aT=new T(function(){var _aU=new T(function(){return B(A3(_8G,_aS,new T(function(){return B(A2(_8I,_aS,_aH));}),new T(function(){return B(A3(_8u,_aS,_aM,_aM));})));});return B(A2(_8K,_aO,_aU));});return B(A2(_88,_aS,_aT));});return B(A3(_ac,B(_a4(E(_aL).a)),function(_aV){return new F(function(){return A3(_a8,_aQ,_aV,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aW=function(_aX,_aY,_aZ){var _b0=E(_aZ),_b1=B(_aK(_aY,_b0.a,_b0.b));return new T2(0,_b1.a,_b1.b);},_b2=function(_b3){return E(E(_b3).r);},_b4=function(_b5,_b6,_b7){var _b8=new T(function(){return E(E(E(_b5).c).a);}),_b9=new T(function(){var _ba=new T(function(){return B(_8q(_b8));}),_bb=new T(function(){var _bc=new T(function(){var _bd=B(_8s(_ba));return B(A3(_8G,_bd,new T(function(){return B(A3(_8u,_bd,_b6,_b6));}),new T(function(){return B(A2(_8I,_bd,_aH));})));});return B(A2(_8K,_b8,_bc));});return B(A3(_ac,B(_a4(E(_b5).a)),function(_be){return new F(function(){return A3(_a8,_ba,_be,_bb);});},_b7));});return new T2(0,new T(function(){return B(A2(_b2,_b8,_b6));}),_b9);},_bf=function(_bg,_bh,_bi){var _bj=E(_bi),_bk=B(_b4(_bh,_bj.a,_bj.b));return new T2(0,_bk.a,_bk.b);},_bl=function(_bm){return E(E(_bm).k);},_bn=function(_bo,_bp,_bq){var _br=new T(function(){return E(E(E(_bo).c).a);}),_bs=new T(function(){var _bt=new T(function(){return B(_8q(_br));}),_bu=new T(function(){var _bv=new T(function(){var _bw=B(_8s(_bt));return B(A3(_8G,_bw,new T(function(){return B(A2(_8I,_bw,_aH));}),new T(function(){return B(A3(_8u,_bw,_bp,_bp));})));});return B(A2(_8K,_br,_bv));});return B(A3(_ac,B(_a4(E(_bo).a)),function(_bx){return new F(function(){return A3(_a8,_bt,_bx,_bu);});},_bq));});return new T2(0,new T(function(){return B(A2(_bl,_br,_bp));}),_bs);},_by=function(_bz,_bA,_bB){var _bC=E(_bB),_bD=B(_bn(_bA,_bC.a,_bC.b));return new T2(0,_bD.a,_bD.b);},_bE=function(_bF){return E(E(_bF).q);},_bG=function(_bH,_bI,_bJ){var _bK=new T(function(){return E(E(E(_bH).c).a);}),_bL=new T(function(){var _bM=new T(function(){return B(_8q(_bK));}),_bN=new T(function(){var _bO=new T(function(){var _bP=B(_8s(_bM));return B(A3(_86,_bP,new T(function(){return B(A3(_8u,_bP,_bI,_bI));}),new T(function(){return B(A2(_8I,_bP,_aH));})));});return B(A2(_8K,_bK,_bO));});return B(A3(_ac,B(_a4(E(_bH).a)),function(_bQ){return new F(function(){return A3(_a8,_bM,_bQ,_bN);});},_bJ));});return new T2(0,new T(function(){return B(A2(_bE,_bK,_bI));}),_bL);},_bR=function(_bS,_bT,_bU){var _bV=E(_bU),_bW=B(_bG(_bT,_bV.a,_bV.b));return new T2(0,_bW.a,_bW.b);},_bX=function(_bY){return E(E(_bY).m);},_bZ=function(_c0,_c1,_c2){var _c3=new T(function(){return E(E(E(_c0).c).a);}),_c4=new T(function(){var _c5=new T(function(){return B(_8q(_c3));}),_c6=new T(function(){var _c7=B(_8s(_c5));return B(A3(_86,_c7,new T(function(){return B(A2(_8I,_c7,_aH));}),new T(function(){return B(A3(_8u,_c7,_c1,_c1));})));});return B(A3(_ac,B(_a4(E(_c0).a)),function(_c8){return new F(function(){return A3(_a8,_c5,_c8,_c6);});},_c2));});return new T2(0,new T(function(){return B(A2(_bX,_c3,_c1));}),_c4);},_c9=function(_ca,_cb,_cc){var _cd=E(_cc),_ce=B(_bZ(_cb,_cd.a,_cd.b));return new T2(0,_ce.a,_ce.b);},_cf=function(_cg){return E(E(_cg).s);},_ch=function(_ci,_cj,_ck){var _cl=new T(function(){return E(E(E(_ci).c).a);}),_cm=new T(function(){var _cn=new T(function(){return B(_8q(_cl));}),_co=new T(function(){var _cp=B(_8s(_cn));return B(A3(_8G,_cp,new T(function(){return B(A2(_8I,_cp,_aH));}),new T(function(){return B(A3(_8u,_cp,_cj,_cj));})));});return B(A3(_ac,B(_a4(E(_ci).a)),function(_cq){return new F(function(){return A3(_a8,_cn,_cq,_co);});},_ck));});return new T2(0,new T(function(){return B(A2(_cf,_cl,_cj));}),_cm);},_cr=function(_cs,_ct,_cu){var _cv=E(_cu),_cw=B(_ch(_ct,_cv.a,_cv.b));return new T2(0,_cw.a,_cw.b);},_cx=function(_cy){return E(E(_cy).i);},_cz=function(_cA){return E(E(_cA).h);},_cB=function(_cC,_cD,_cE){var _cF=new T(function(){return E(E(E(_cC).c).a);}),_cG=new T(function(){var _cH=new T(function(){return B(_8s(new T(function(){return B(_8q(_cF));})));}),_cI=new T(function(){return B(A2(_88,_cH,new T(function(){return B(A2(_cz,_cF,_cD));})));});return B(A3(_ac,B(_a4(E(_cC).a)),function(_cJ){return new F(function(){return A3(_8u,_cH,_cJ,_cI);});},_cE));});return new T2(0,new T(function(){return B(A2(_cx,_cF,_cD));}),_cG);},_cK=function(_cL,_cM,_cN){var _cO=E(_cN),_cP=B(_cB(_cM,_cO.a,_cO.b));return new T2(0,_cP.a,_cP.b);},_cQ=function(_cR){return E(E(_cR).o);},_cS=function(_cT){return E(E(_cT).n);},_cU=function(_cV,_cW,_cX){var _cY=new T(function(){return E(E(E(_cV).c).a);}),_cZ=new T(function(){var _d0=new T(function(){return B(_8s(new T(function(){return B(_8q(_cY));})));}),_d1=new T(function(){return B(A2(_cS,_cY,_cW));});return B(A3(_ac,B(_a4(E(_cV).a)),function(_d2){return new F(function(){return A3(_8u,_d0,_d2,_d1);});},_cX));});return new T2(0,new T(function(){return B(A2(_cQ,_cY,_cW));}),_cZ);},_d3=function(_d4,_d5,_d6){var _d7=E(_d6),_d8=B(_cU(_d5,_d7.a,_d7.b));return new T2(0,_d8.a,_d8.b);},_d9=function(_da){return E(E(_da).c);},_db=function(_dc,_dd,_de){var _df=new T(function(){return E(E(E(_dc).c).a);}),_dg=new T(function(){var _dh=new T(function(){return B(_8s(new T(function(){return B(_8q(_df));})));}),_di=new T(function(){return B(A2(_d9,_df,_dd));});return B(A3(_ac,B(_a4(E(_dc).a)),function(_dj){return new F(function(){return A3(_8u,_dh,_dj,_di);});},_de));});return new T2(0,new T(function(){return B(A2(_d9,_df,_dd));}),_dg);},_dk=function(_dl,_dm,_dn){var _do=E(_dn),_dp=B(_db(_dm,_do.a,_do.b));return new T2(0,_dp.a,_dp.b);},_dq=function(_dr,_ds,_dt){var _du=new T(function(){return E(E(E(_dr).c).a);}),_dv=new T(function(){var _dw=new T(function(){return B(_8q(_du));}),_dx=new T(function(){return B(_8s(_dw));}),_dy=new T(function(){return B(A3(_a8,_dw,new T(function(){return B(A2(_8I,_dx,_aH));}),_ds));});return B(A3(_ac,B(_a4(E(_dr).a)),function(_dz){return new F(function(){return A3(_8u,_dx,_dz,_dy);});},_dt));});return new T2(0,new T(function(){return B(A2(_ae,_du,_ds));}),_dv);},_dA=function(_dB,_dC,_dD){var _dE=E(_dD),_dF=B(_dq(_dC,_dE.a,_dE.b));return new T2(0,_dF.a,_dF.b);},_dG=function(_dH,_dI,_dJ,_dK){var _dL=new T(function(){return E(E(_dI).c);}),_dM=new T3(0,new T(function(){return E(E(_dI).a);}),new T(function(){return E(E(_dI).b);}),new T2(0,new T(function(){return E(E(_dL).a);}),new T(function(){return E(E(_dL).b);})));return new F(function(){return A3(_a8,_dH,new T(function(){var _dN=E(_dK),_dO=B(_dq(_dM,_dN.a,_dN.b));return new T2(0,_dO.a,_dO.b);}),new T(function(){var _dP=E(_dJ),_dQ=B(_dq(_dM,_dP.a,_dP.b));return new T2(0,_dQ.a,_dQ.b);}));});},_dR=function(_dS){return E(E(_dS).b);},_dT=function(_dU){return E(E(_dU).b);},_dV=function(_dW){var _dX=new T(function(){return E(E(E(_dW).c).a);}),_dY=new T(function(){return B(A2(_dT,E(_dW).a,new T(function(){return B(A2(_8I,B(_8s(B(_8q(_dX)))),_L));})));});return new T2(0,new T(function(){return B(_dR(_dX));}),_dY);},_dZ=function(_e0,_e1){var _e2=B(_dV(_e1));return new T2(0,_e2.a,_e2.b);},_e3=function(_e4,_e5,_e6){var _e7=new T(function(){return E(E(E(_e4).c).a);}),_e8=new T(function(){var _e9=new T(function(){return B(_8s(new T(function(){return B(_8q(_e7));})));}),_ea=new T(function(){return B(A2(_cx,_e7,_e5));});return B(A3(_ac,B(_a4(E(_e4).a)),function(_eb){return new F(function(){return A3(_8u,_e9,_eb,_ea);});},_e6));});return new T2(0,new T(function(){return B(A2(_cz,_e7,_e5));}),_e8);},_ec=function(_ed,_ee,_ef){var _eg=E(_ef),_eh=B(_e3(_ee,_eg.a,_eg.b));return new T2(0,_eh.a,_eh.b);},_ei=function(_ej,_ek,_el){var _em=new T(function(){return E(E(E(_ej).c).a);}),_en=new T(function(){var _eo=new T(function(){return B(_8s(new T(function(){return B(_8q(_em));})));}),_ep=new T(function(){return B(A2(_cQ,_em,_ek));});return B(A3(_ac,B(_a4(E(_ej).a)),function(_eq){return new F(function(){return A3(_8u,_eo,_eq,_ep);});},_el));});return new T2(0,new T(function(){return B(A2(_cS,_em,_ek));}),_en);},_er=function(_es,_et,_eu){var _ev=E(_eu),_ew=B(_ei(_et,_ev.a,_ev.b));return new T2(0,_ew.a,_ew.b);},_ex=new T1(0,2),_ey=function(_ez,_eA,_eB){var _eC=new T(function(){return E(E(E(_ez).c).a);}),_eD=new T(function(){var _eE=new T(function(){return B(_8q(_eC));}),_eF=new T(function(){return B(_8s(_eE));}),_eG=new T(function(){var _eH=new T(function(){return B(A3(_a8,_eE,new T(function(){return B(A2(_8I,_eF,_aH));}),new T(function(){return B(A2(_8I,_eF,_ex));})));});return B(A3(_a8,_eE,_eH,new T(function(){return B(A2(_8K,_eC,_eA));})));});return B(A3(_ac,B(_a4(E(_ez).a)),function(_eI){return new F(function(){return A3(_8u,_eF,_eI,_eG);});},_eB));});return new T2(0,new T(function(){return B(A2(_8K,_eC,_eA));}),_eD);},_eJ=function(_eK,_eL,_eM){var _eN=E(_eM),_eO=B(_ey(_eL,_eN.a,_eN.b));return new T2(0,_eO.a,_eO.b);},_eP=function(_eQ){return E(E(_eQ).j);},_eR=function(_eS,_eT,_eU){var _eV=new T(function(){return E(E(E(_eS).c).a);}),_eW=new T(function(){var _eX=new T(function(){return B(_8q(_eV));}),_eY=new T(function(){var _eZ=new T(function(){return B(A2(_cx,_eV,_eT));});return B(A3(_8u,B(_8s(_eX)),_eZ,_eZ));});return B(A3(_ac,B(_a4(E(_eS).a)),function(_f0){return new F(function(){return A3(_a8,_eX,_f0,_eY);});},_eU));});return new T2(0,new T(function(){return B(A2(_eP,_eV,_eT));}),_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eR(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8){return E(E(_f8).p);},_f9=function(_fa,_fb,_fc){var _fd=new T(function(){return E(E(E(_fa).c).a);}),_fe=new T(function(){var _ff=new T(function(){return B(_8q(_fd));}),_fg=new T(function(){var _fh=new T(function(){return B(A2(_cQ,_fd,_fb));});return B(A3(_8u,B(_8s(_ff)),_fh,_fh));});return B(A3(_ac,B(_a4(E(_fa).a)),function(_fi){return new F(function(){return A3(_a8,_ff,_fi,_fg);});},_fc));});return new T2(0,new T(function(){return B(A2(_f7,_fd,_fb));}),_fe);},_fj=function(_fk,_fl,_fm){var _fn=E(_fm),_fo=B(_f9(_fl,_fn.a,_fn.b));return new T2(0,_fo.a,_fo.b);},_fp=function(_fq,_fr){return {_:0,a:_fq,b:new T(function(){return B(_dZ(_fq,_fr));}),c:function(_fs){return new F(function(){return _dk(_fq,_fr,_fs);});},d:function(_fs){return new F(function(){return _dA(_fq,_fr,_fs);});},e:function(_fs){return new F(function(){return _eJ(_fq,_fr,_fs);});},f:function(_ft,_fs){return new F(function(){return _az(_fq,_fr,_ft,_fs);});},g:function(_ft,_fs){return new F(function(){return _dG(_fq,_fr,_ft,_fs);});},h:function(_fs){return new F(function(){return _ec(_fq,_fr,_fs);});},i:function(_fs){return new F(function(){return _cK(_fq,_fr,_fs);});},j:function(_fs){return new F(function(){return _f1(_fq,_fr,_fs);});},k:function(_fs){return new F(function(){return _by(_fq,_fr,_fs);});},l:function(_fs){return new F(function(){return _aW(_fq,_fr,_fs);});},m:function(_fs){return new F(function(){return _c9(_fq,_fr,_fs);});},n:function(_fs){return new F(function(){return _er(_fq,_fr,_fs);});},o:function(_fs){return new F(function(){return _d3(_fq,_fr,_fs);});},p:function(_fs){return new F(function(){return _fj(_fq,_fr,_fs);});},q:function(_fs){return new F(function(){return _bR(_fq,_fr,_fs);});},r:function(_fs){return new F(function(){return _bf(_fq,_fr,_fs);});},s:function(_fs){return new F(function(){return _cr(_fq,_fr,_fs);});}};},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8q(new T(function(){return E(E(E(_fv).c).a);})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){var _fE=new T(function(){return B(_8s(_fA));}),_fF=new T(function(){return B(A3(_8u,_fE,_fy,_fy));}),_fG=function(_fH,_fI){var _fJ=new T(function(){return B(A3(_8G,_fE,new T(function(){return B(A3(_8u,_fE,_fH,_fy));}),new T(function(){return B(A3(_8u,_fE,_fw,_fI));})));});return new F(function(){return A3(_a8,_fA,_fJ,_fF);});};return B(A3(_ac,B(_a4(_fC)),_fG,_fx));});return B(A3(_aa,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_a8,_fA,_fw,_fy));}),_fB);},_fK=function(_fL,_fM,_fN,_fO){var _fP=E(_fN),_fQ=E(_fO),_fR=B(_fu(_fM,_fP.a,_fP.b,_fQ.a,_fQ.b));return new T2(0,_fR.a,_fR.b);},_fS=function(_fT){return E(E(_fT).d);},_fU=function(_fV,_fW){var _fX=new T(function(){return B(_8q(new T(function(){return E(E(E(_fV).c).a);})));}),_fY=new T(function(){return B(A2(_dT,E(_fV).a,new T(function(){return B(A2(_8I,B(_8s(_fX)),_L));})));});return new T2(0,new T(function(){return B(A2(_fS,_fX,_fW));}),_fY);},_fZ=function(_g0,_g1,_g2){var _g3=B(_fU(_g1,_g2));return new T2(0,_g3.a,_g3.b);},_g4=function(_g5,_g6,_g7){var _g8=new T(function(){return B(_8q(new T(function(){return E(E(E(_g5).c).a);})));}),_g9=new T(function(){return B(_8s(_g8));}),_ga=new T(function(){var _gb=new T(function(){var _gc=new T(function(){return B(A3(_a8,_g8,new T(function(){return B(A2(_8I,_g9,_aH));}),new T(function(){return B(A3(_8u,_g9,_g6,_g6));})));});return B(A2(_88,_g9,_gc));});return B(A3(_ac,B(_a4(E(_g5).a)),function(_gd){return new F(function(){return A3(_8u,_g9,_gd,_gb);});},_g7));}),_ge=new T(function(){return B(A3(_a8,_g8,new T(function(){return B(A2(_8I,_g9,_aH));}),_g6));});return new T2(0,_ge,_ga);},_gf=function(_gg,_gh,_gi){var _gj=E(_gi),_gk=B(_g4(_gh,_gj.a,_gj.b));return new T2(0,_gk.a,_gk.b);},_gl=function(_gm,_gn){return new T4(0,_gm,function(_ft,_fs){return new F(function(){return _fK(_gm,_gn,_ft,_fs);});},function(_fs){return new F(function(){return _gf(_gm,_gn,_fs);});},function(_fs){return new F(function(){return _fZ(_gm,_gn,_fs);});});},_go=function(_gp,_gq,_gr,_gs,_gt){var _gu=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gp).c).a);})));})));}),_gv=new T(function(){var _gw=E(_gp).a,_gx=new T(function(){var _gy=function(_gz,_gA){return new F(function(){return A3(_86,_gu,new T(function(){return B(A3(_8u,_gu,_gq,_gA));}),new T(function(){return B(A3(_8u,_gu,_gz,_gs));}));});};return B(A3(_ac,B(_a4(_gw)),_gy,_gr));});return B(A3(_aa,_gw,_gx,_gt));});return new T2(0,new T(function(){return B(A3(_8u,_gu,_gq,_gs));}),_gv);},_gB=function(_gC,_gD,_gE){var _gF=E(_gD),_gG=E(_gE),_gH=B(_go(_gC,_gF.a,_gF.b,_gG.a,_gG.b));return new T2(0,_gH.a,_gH.b);},_gI=function(_gJ,_gK,_gL,_gM,_gN){var _gO=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gJ).c).a);})));})));}),_gP=new T(function(){var _gQ=E(_gJ).a,_gR=new T(function(){return B(A3(_ac,B(_a4(_gQ)),new T(function(){return B(_86(_gO));}),_gL));});return B(A3(_aa,_gQ,_gR,_gN));});return new T2(0,new T(function(){return B(A3(_86,_gO,_gK,_gM));}),_gP);},_gS=function(_gT,_gU,_gV){var _gW=E(_gU),_gX=E(_gV),_gY=B(_gI(_gT,_gW.a,_gW.b,_gX.a,_gX.b));return new T2(0,_gY.a,_gY.b);},_gZ=function(_h0,_h1,_h2){var _h3=B(_h4(_h0));return new F(function(){return A3(_86,_h3,_h1,new T(function(){return B(A2(_88,_h3,_h2));}));});},_h5=function(_h6){return E(E(_h6).e);},_h7=function(_h8){return E(E(_h8).f);},_h9=function(_ha,_hb,_hc){var _hd=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_ha).c).a);})));})));}),_he=new T(function(){var _hf=new T(function(){return B(A2(_h7,_hd,_hb));});return B(A3(_ac,B(_a4(E(_ha).a)),function(_hg){return new F(function(){return A3(_8u,_hd,_hg,_hf);});},_hc));});return new T2(0,new T(function(){return B(A2(_h5,_hd,_hb));}),_he);},_hh=function(_hi,_hj){var _hk=E(_hj),_hl=B(_h9(_hi,_hk.a,_hk.b));return new T2(0,_hl.a,_hl.b);},_hm=function(_hn,_ho){var _hp=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hn).c).a);})));})));}),_hq=new T(function(){return B(A2(_dT,E(_hn).a,new T(function(){return B(A2(_8I,_hp,_L));})));});return new T2(0,new T(function(){return B(A2(_8I,_hp,_ho));}),_hq);},_hr=function(_hs,_ht){var _hu=B(_hm(_hs,_ht));return new T2(0,_hu.a,_hu.b);},_hv=function(_hw,_hx,_hy){var _hz=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hw).c).a);})));})));}),_hA=new T(function(){return B(A3(_ac,B(_a4(E(_hw).a)),new T(function(){return B(_88(_hz));}),_hy));});return new T2(0,new T(function(){return B(A2(_88,_hz,_hx));}),_hA);},_hB=function(_hC,_hD){var _hE=E(_hD),_hF=B(_hv(_hC,_hE.a,_hE.b));return new T2(0,_hF.a,_hF.b);},_hG=function(_hH,_hI){var _hJ=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hH).c).a);})));})));}),_hK=new T(function(){return B(A2(_dT,E(_hH).a,new T(function(){return B(A2(_8I,_hJ,_L));})));});return new T2(0,new T(function(){return B(A2(_h7,_hJ,_hI));}),_hK);},_hL=function(_hM,_hN){var _hO=B(_hG(_hM,E(_hN).a));return new T2(0,_hO.a,_hO.b);},_h4=function(_hP){return {_:0,a:function(_ft,_fs){return new F(function(){return _gS(_hP,_ft,_fs);});},b:function(_ft,_fs){return new F(function(){return _gZ(_hP,_ft,_fs);});},c:function(_ft,_fs){return new F(function(){return _gB(_hP,_ft,_fs);});},d:function(_fs){return new F(function(){return _hB(_hP,_fs);});},e:function(_fs){return new F(function(){return _hh(_hP,_fs);});},f:function(_fs){return new F(function(){return _hL(_hP,_fs);});},g:function(_fs){return new F(function(){return _hr(_hP,_fs);});}};},_hQ=function(_hR){var _hS=new T(function(){return E(E(_hR).a);}),_hT=new T3(0,_9Y,_a0,new T2(0,_hS,new T(function(){return E(E(_hR).b);}))),_hU=new T(function(){return B(_fp(new T(function(){return B(_gl(new T(function(){return B(_h4(_hT));}),_hT));}),_hT));}),_hV=new T(function(){return B(_8s(new T(function(){return B(_8q(_hS));})));}),_hW=function(_hX){return E(B(_8M(_hU,new T(function(){var _hY=E(_hX),_hZ=B(A2(_8I,_hV,_1o)),_i0=B(A2(_8I,_hV,_9Z));return new T3(0,E(new T2(0,_hY.a,new T3(0,E(_hZ),E(_i0),E(_i0)))),E(new T2(0,_hY.b,new T3(0,E(_i0),E(_hZ),E(_i0)))),E(new T2(0,_hY.c,new T3(0,E(_i0),E(_i0),E(_hZ)))));}))).b);};return E(_hW);},_i1=new T(function(){return B(_hQ(_9u));}),_i2=function(_i3,_i4){var _i5=E(_i4);return (_i5._==0)?__Z:new T2(1,_i3,new T2(1,_i5.a,new T(function(){return B(_i2(_i3,_i5.b));})));},_i6=new T(function(){var _i7=B(A1(_i1,_91));return new T2(1,_i7.a,new T(function(){return B(_i2(_22,new T2(1,_i7.b,new T2(1,_i7.c,_w))));}));}),_i8=new T1(1,_i6),_i9=new T2(1,_i8,_1S),_ia=new T(function(){return B(unCStr("vec3("));}),_ib=new T1(0,_ia),_ic=new T2(1,_ib,_i9),_id=new T(function(){return toJSStr(B(_1F(_x,_1l,_ic)));}),_ie="enclose",_if="outline",_ig="polygon",_ih="z",_ii="y",_ij="x",_ik=0,_il=function(_im){var _in=__new(),_io=_in,_ip=function(_iq,_){while(1){var _ir=E(_iq);if(!_ir._){return _ik;}else{var _is=E(_ir.a),_it=__set(_io,E(_is.a),E(_is.b));_iq=_ir.b;continue;}}},_iu=B(_ip(_im,_));return E(_io);},_iv=function(_iw){return new F(function(){return _il(new T2(1,new T2(0,_ij,new T(function(){return E(E(E(E(_iw).d).a).a);})),new T2(1,new T2(0,_ii,new T(function(){return E(E(E(E(_iw).d).a).b);})),new T2(1,new T2(0,_ih,new T(function(){return E(E(E(E(_iw).d).a).c);})),new T2(1,new T2(0,_ig,new T(function(){return E(_iw).h;})),new T2(1,new T2(0,_if,new T(function(){return E(_iw).i;})),new T2(1,new T2(0,_ie,new T(function(){return E(_iw).j;})),_w)))))));});},_ix=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_iy=new T(function(){return B(err(_ix));}),_iz=new T(function(){return eval("__strict(drawObjects)");}),_iA=new T(function(){return eval("__strict(draw)");}),_iB=function(_iC,_iD){var _iE=jsShowI(_iC);return new F(function(){return _n(fromJSStr(_iE),_iD);});},_iF=function(_iG,_iH,_iI){if(_iH>=0){return new F(function(){return _iB(_iH,_iI);});}else{if(_iG<=6){return new F(function(){return _iB(_iH,_iI);});}else{return new T2(1,_11,new T(function(){var _iJ=jsShowI(_iH);return B(_n(fromJSStr(_iJ),new T2(1,_10,_iI)));}));}}},_iK=new T(function(){return B(unCStr(")"));}),_iL=function(_iM,_iN){var _iO=new T(function(){var _iP=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_iF(0,_iM,_w)),_iK));})));},1);return B(_n(B(_iF(0,_iN,_w)),_iP));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_iO)));});},_iQ=new T2(1,_ik,_w),_iR=function(_iS){return E(_iS);},_iT=function(_iU){return E(_iU);},_iV=function(_iW,_iX){return E(_iX);},_iY=function(_iZ,_j0){return E(_iZ);},_j1=function(_j2){return E(_j2);},_j3=new T2(0,_j1,_iY),_j4=function(_j5,_j6){return E(_j5);},_j7=new T5(0,_j3,_iT,_iR,_iV,_j4),_j8=function(_j9){var _ja=E(_j9);return new F(function(){return Math.log(_ja+(_ja+1)*Math.sqrt((_ja-1)/(_ja+1)));});},_jb=function(_jc){var _jd=E(_jc);return new F(function(){return Math.log(_jd+Math.sqrt(1+_jd*_jd));});},_je=function(_jf){var _jg=E(_jf);return 0.5*Math.log((1+_jg)/(1-_jg));},_jh=function(_ji,_jj){return Math.log(E(_jj))/Math.log(E(_ji));},_jk=3.141592653589793,_jl=function(_jm){var _jn=E(_jm);return new F(function(){return _7J(_jn.a,_jn.b);});},_jo=function(_jp){return 1/E(_jp);},_jq=function(_jr){var _js=E(_jr),_jt=E(_js);return (_jt==0)?E(_7I):(_jt<=0)? -_jt:E(_js);},_ju=function(_jv){var _jw=E(_jv);if(!_jw._){return _jw.a;}else{return new F(function(){return I_toNumber(_jw.a);});}},_jx=function(_jy){return new F(function(){return _ju(_jy);});},_jz=1,_jA=-1,_jB=function(_jC){var _jD=E(_jC);return (_jD<=0)?(_jD>=0)?E(_jD):E(_jA):E(_jz);},_jE=function(_jF,_jG){return E(_jF)-E(_jG);},_jH=function(_jI){return  -E(_jI);},_jJ=function(_jK,_jL){return E(_jK)+E(_jL);},_jM=function(_jN,_jO){return E(_jN)*E(_jO);},_jP={_:0,a:_jJ,b:_jE,c:_jM,d:_jH,e:_jq,f:_jB,g:_jx},_jQ=function(_jR,_jS){return E(_jR)/E(_jS);},_jT=new T4(0,_jP,_jQ,_jo,_jl),_jU=function(_jV){return new F(function(){return Math.acos(E(_jV));});},_jW=function(_jX){return new F(function(){return Math.asin(E(_jX));});},_jY=function(_jZ){return new F(function(){return Math.atan(E(_jZ));});},_k0=function(_k1){return new F(function(){return Math.cos(E(_k1));});},_k2=function(_k3){return new F(function(){return cosh(E(_k3));});},_k4=function(_k5){return new F(function(){return Math.exp(E(_k5));});},_k6=function(_k7){return new F(function(){return Math.log(E(_k7));});},_k8=function(_k9,_ka){return new F(function(){return Math.pow(E(_k9),E(_ka));});},_kb=function(_kc){return new F(function(){return Math.sin(E(_kc));});},_kd=function(_ke){return new F(function(){return sinh(E(_ke));});},_kf=function(_kg){return new F(function(){return Math.sqrt(E(_kg));});},_kh=function(_ki){return new F(function(){return Math.tan(E(_ki));});},_kj=function(_kk){return new F(function(){return tanh(E(_kk));});},_kl={_:0,a:_jT,b:_jk,c:_k4,d:_k6,e:_kf,f:_k8,g:_jh,h:_kb,i:_k0,j:_kh,k:_jW,l:_jU,m:_jY,n:_kd,o:_k2,p:_kj,q:_jb,r:_j8,s:_je},_km="flipped2",_kn="flipped1",_ko="c1y",_kp="c1x",_kq="w2z",_kr="w2y",_ks="w2x",_kt="w1z",_ku="w1y",_kv="w1x",_kw="d2z",_kx="d2y",_ky="d2x",_kz="d1z",_kA="d1y",_kB="d1x",_kC="c2y",_kD="c2x",_kE=function(_kF,_){var _kG=__get(_kF,E(_kv)),_kH=__get(_kF,E(_ku)),_kI=__get(_kF,E(_kt)),_kJ=__get(_kF,E(_ks)),_kK=__get(_kF,E(_kr)),_kL=__get(_kF,E(_kq)),_kM=__get(_kF,E(_kp)),_kN=__get(_kF,E(_ko)),_kO=__get(_kF,E(_kD)),_kP=__get(_kF,E(_kC)),_kQ=__get(_kF,E(_kB)),_kR=__get(_kF,E(_kA)),_kS=__get(_kF,E(_kz)),_kT=__get(_kF,E(_ky)),_kU=__get(_kF,E(_kx)),_kV=__get(_kF,E(_kw)),_kW=__get(_kF,E(_kn)),_kX=__get(_kF,E(_km));return {_:0,a:E(new T3(0,E(_kG),E(_kH),E(_kI))),b:E(new T3(0,E(_kJ),E(_kK),E(_kL))),c:E(new T2(0,E(_kM),E(_kN))),d:E(new T2(0,E(_kO),E(_kP))),e:E(new T3(0,E(_kQ),E(_kR),E(_kS))),f:E(new T3(0,E(_kT),E(_kU),E(_kV))),g:E(_kW),h:E(_kX)};},_kY=function(_kZ,_){var _l0=E(_kZ);if(!_l0._){return _w;}else{var _l1=B(_kE(E(_l0.a),_)),_l2=B(_kY(_l0.b,_));return new T2(1,_l1,_l2);}},_l3=function(_l4){var _l5=E(_l4);return (E(_l5.b)-E(_l5.a)|0)+1|0;},_l6=function(_l7,_l8){var _l9=E(_l7),_la=E(_l8);return (E(_l9.a)>_la)?false:_la<=E(_l9.b);},_lb=function(_lc){return new F(function(){return _iF(0,E(_lc),_w);});},_ld=function(_le,_lf,_lg){return new F(function(){return _iF(E(_le),E(_lf),_lg);});},_lh=function(_li,_lj){return new F(function(){return _iF(0,E(_li),_lj);});},_lk=function(_ll,_lm){return new F(function(){return _49(_lh,_ll,_lm);});},_ln=new T3(0,_ld,_lb,_lk),_lo=0,_lp=function(_lq,_lr,_ls){return new F(function(){return A1(_lq,new T2(1,_46,new T(function(){return B(A1(_lr,_ls));})));});},_lt=new T(function(){return B(unCStr(": empty list"));}),_lu=new T(function(){return B(unCStr("Prelude."));}),_lv=function(_lw){return new F(function(){return err(B(_n(_lu,new T(function(){return B(_n(_lw,_lt));},1))));});},_lx=new T(function(){return B(unCStr("foldr1"));}),_ly=new T(function(){return B(_lv(_lx));}),_lz=function(_lA,_lB){var _lC=E(_lB);if(!_lC._){return E(_ly);}else{var _lD=_lC.a,_lE=E(_lC.b);if(!_lE._){return E(_lD);}else{return new F(function(){return A2(_lA,_lD,new T(function(){return B(_lz(_lA,_lE));}));});}}},_lF=new T(function(){return B(unCStr(" out of range "));}),_lG=new T(function(){return B(unCStr("}.index: Index "));}),_lH=new T(function(){return B(unCStr("Ix{"));}),_lI=new T2(1,_10,_w),_lJ=new T2(1,_10,_lI),_lK=0,_lL=function(_lM){return E(E(_lM).a);},_lN=function(_lO,_lP,_lQ,_lR,_lS){var _lT=new T(function(){var _lU=new T(function(){var _lV=new T(function(){var _lW=new T(function(){var _lX=new T(function(){return B(A3(_lz,_lp,new T2(1,new T(function(){return B(A3(_lL,_lQ,_lK,_lR));}),new T2(1,new T(function(){return B(A3(_lL,_lQ,_lK,_lS));}),_w)),_lJ));});return B(_n(_lF,new T2(1,_11,new T2(1,_11,_lX))));});return B(A(_lL,[_lQ,_lo,_lP,new T2(1,_10,_lW)]));});return B(_n(_lG,new T2(1,_11,_lV)));},1);return B(_n(_lO,_lU));},1);return new F(function(){return err(B(_n(_lH,_lT)));});},_lY=function(_lZ,_m0,_m1,_m2,_m3){return new F(function(){return _lN(_lZ,_m0,_m3,_m1,_m2);});},_m4=function(_m5,_m6,_m7,_m8){var _m9=E(_m7);return new F(function(){return _lY(_m5,_m6,_m9.a,_m9.b,_m8);});},_ma=function(_mb,_mc,_md,_me){return new F(function(){return _m4(_me,_md,_mc,_mb);});},_mf=new T(function(){return B(unCStr("Int"));}),_mg=function(_mh,_mi){return new F(function(){return _ma(_ln,_mi,_mh,_mf);});},_mj=function(_mk,_ml){var _mm=E(_mk),_mn=E(_mm.a),_mo=E(_ml);if(_mn>_mo){return new F(function(){return _mg(_mo,_mm);});}else{if(_mo>E(_mm.b)){return new F(function(){return _mg(_mo,_mm);});}else{return _mo-_mn|0;}}},_mp=function(_mq,_mr){if(_mq<=_mr){var _ms=function(_mt){return new T2(1,_mt,new T(function(){if(_mt!=_mr){return B(_ms(_mt+1|0));}else{return __Z;}}));};return new F(function(){return _ms(_mq);});}else{return __Z;}},_mu=function(_mv,_mw){return new F(function(){return _mp(E(_mv),E(_mw));});},_mx=function(_my){var _mz=E(_my);return new F(function(){return _mu(_mz.a,_mz.b);});},_mA=function(_mB){var _mC=E(_mB),_mD=E(_mC.a),_mE=E(_mC.b);return (_mD>_mE)?E(_lo):(_mE-_mD|0)+1|0;},_mF=function(_mG,_mH){return E(_mG)-E(_mH)|0;},_mI=function(_mJ,_mK){return new F(function(){return _mF(_mK,E(_mJ).a);});},_mL=function(_mM,_mN){return E(_mM)==E(_mN);},_mO=function(_mP,_mQ){return E(_mP)!=E(_mQ);},_mR=new T2(0,_mL,_mO),_mS=function(_mT,_mU){var _mV=E(_mT),_mW=E(_mU);return (_mV>_mW)?E(_mV):E(_mW);},_mX=function(_mY,_mZ){var _n0=E(_mY),_n1=E(_mZ);return (_n0>_n1)?E(_n1):E(_n0);},_n2=function(_n3,_n4){return (_n3>=_n4)?(_n3!=_n4)?2:1:0;},_n5=function(_n6,_n7){return new F(function(){return _n2(E(_n6),E(_n7));});},_n8=function(_n9,_na){return E(_n9)>=E(_na);},_nb=function(_nc,_nd){return E(_nc)>E(_nd);},_ne=function(_nf,_ng){return E(_nf)<=E(_ng);},_nh=function(_ni,_nj){return E(_ni)<E(_nj);},_nk={_:0,a:_mR,b:_n5,c:_nh,d:_ne,e:_nb,f:_n8,g:_mS,h:_mX},_nl={_:0,a:_nk,b:_mx,c:_mj,d:_mI,e:_l6,f:_mA,g:_l3},_nm=function(_nn,_no,_){while(1){var _np=B((function(_nq,_nr,_){var _ns=E(_nq);if(!_ns._){return new T2(0,_ik,_nr);}else{var _nt=B(A2(_ns.a,_nr,_));_nn=_ns.b;_no=new T(function(){return E(E(_nt).b);});return __continue;}})(_nn,_no,_));if(_np!=__continue){return _np;}}},_nu=function(_nv,_nw){return new T2(1,_nv,_nw);},_nx=function(_ny,_nz){var _nA=E(_nz);return new T2(0,_nA.a,_nA.b);},_nB=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_nC=new T(function(){return B(err(_nB));}),_nD=new T(function(){return B(unCStr("Negative range size"));}),_nE=new T(function(){return B(err(_nD));}),_nF=function(_nG){return E(E(_nG).f);},_nH=function(_nI){var _nJ=B(A1(_nI,_));return E(_nJ);},_nK=function(_nL,_nM,_nN){var _nO=E(_nM),_nP=_nO.a,_nQ=_nO.b,_nR=function(_){var _nS=B(A2(_nF,_nL,_nO));if(_nS>=0){var _nT=newArr(_nS,_nC),_nU=_nT,_nV=E(_nS);if(!_nV){return new T(function(){return new T4(0,E(_nP),E(_nQ),0,_nU);});}else{var _nW=function(_nX,_nY,_){while(1){var _nZ=E(_nX);if(!_nZ._){return E(_);}else{var _=_nU[_nY]=_nZ.a;if(_nY!=(_nV-1|0)){var _o0=_nY+1|0;_nX=_nZ.b;_nY=_o0;continue;}else{return E(_);}}}},_=B(_nW(_nN,0,_));return new T(function(){return new T4(0,E(_nP),E(_nQ),_nV,_nU);});}}else{return E(_nE);}};return new F(function(){return _nH(_nR);});},_o1=function(_o2,_o3,_o4,_o5){var _o6=new T(function(){var _o7=E(_o5),_o8=_o7.c-1|0,_o9=new T(function(){return B(A2(_dT,_o3,_w));});if(0<=_o8){var _oa=new T(function(){return B(_a4(_o3));}),_ob=function(_oc){var _od=new T(function(){var _oe=new T(function(){return B(A1(_o4,new T(function(){return E(_o7.d[_oc]);})));});return B(A3(_ac,_oa,_nu,_oe));});return new F(function(){return A3(_aa,_o3,_od,new T(function(){if(_oc!=_o8){return B(_ob(_oc+1|0));}else{return E(_o9);}}));});};return B(_ob(0));}else{return E(_o9);}}),_of=new T(function(){return B(_nx(_o2,_o5));});return new F(function(){return A3(_ac,B(_a4(_o3)),function(_og){return new F(function(){return _nK(_o2,_of,_og);});},_o6);});},_oh=function(_oi,_oj,_ok,_ol,_om,_on,_oo,_op,_oq){var _or=B(_8u(_oi));return new T2(0,new T3(0,E(B(A1(B(A1(_or,_oj)),_on))),E(B(A1(B(A1(_or,_ok)),_oo))),E(B(A1(B(A1(_or,_ol)),_op)))),B(A1(B(A1(_or,_om)),_oq)));},_os=function(_ot,_ou,_ov,_ow,_ox,_oy,_oz,_oA,_oB){var _oC=B(_86(_ot));return new T2(0,new T3(0,E(B(A1(B(A1(_oC,_ou)),_oy))),E(B(A1(B(A1(_oC,_ov)),_oz))),E(B(A1(B(A1(_oC,_ow)),_oA)))),B(A1(B(A1(_oC,_ox)),_oB)));},_oD=function(_oE,_oF){return (E(_oE)!=E(_oF))?true:false;},_oG=function(_oH,_oI){return E(_oH)==E(_oI);},_oJ=new T2(0,_oG,_oD),_oK=function(_oL,_oM){return E(_oL)<E(_oM);},_oN=function(_oO,_oP){return E(_oO)<=E(_oP);},_oQ=function(_oR,_oS){return E(_oR)>E(_oS);},_oT=function(_oU,_oV){return E(_oU)>=E(_oV);},_oW=function(_oX,_oY){var _oZ=E(_oX),_p0=E(_oY);return (_oZ>=_p0)?(_oZ!=_p0)?2:1:0;},_p1=function(_p2,_p3){var _p4=E(_p2),_p5=E(_p3);return (_p4>_p5)?E(_p4):E(_p5);},_p6=function(_p7,_p8){var _p9=E(_p7),_pa=E(_p8);return (_p9>_pa)?E(_pa):E(_p9);},_pb={_:0,a:_oJ,b:_oW,c:_oK,d:_oN,e:_oQ,f:_oT,g:_p1,h:_p6},_pc="dz",_pd="wy",_pe="wx",_pf="dy",_pg="dx",_ph="t",_pi="a",_pj="r",_pk="ly",_pl="lx",_pm="wz",_pn=function(_po,_pp,_pq,_pr,_ps,_pt,_pu,_pv,_pw){return new F(function(){return _il(new T2(1,new T2(0,_pe,_po),new T2(1,new T2(0,_pd,_pp),new T2(1,new T2(0,_pm,_pq),new T2(1,new T2(0,_pl,_pr*_ps*Math.cos(_pt)),new T2(1,new T2(0,_pk,_pr*_ps*Math.sin(_pt)),new T2(1,new T2(0,_pj,_pr),new T2(1,new T2(0,_pi,_ps),new T2(1,new T2(0,_ph,_pt),new T2(1,new T2(0,_pg,_pu),new T2(1,new T2(0,_pf,_pv),new T2(1,new T2(0,_pc,_pw),_w))))))))))));});},_px=function(_py){var _pz=E(_py),_pA=E(_pz.a),_pB=E(_pz.b),_pC=E(_pz.d);return new F(function(){return _pn(_pA.a,_pA.b,_pA.c,E(_pB.a),E(_pB.b),E(_pz.c),_pC.a,_pC.b,_pC.c);});},_pD=function(_pE,_pF){var _pG=E(_pF);return (_pG._==0)?__Z:new T2(1,new T(function(){return B(A1(_pE,_pG.a));}),new T(function(){return B(_pD(_pE,_pG.b));}));},_pH=function(_pI,_pJ,_pK){var _pL=__lst2arr(B(_pD(_px,new T2(1,_pI,new T2(1,_pJ,new T2(1,_pK,_w))))));return E(_pL);},_pM=function(_pN){var _pO=E(_pN);return new F(function(){return _pH(_pO.a,_pO.b,_pO.c);});},_pP=new T2(0,_kl,_pb),_pQ=function(_pR,_pS,_pT,_pU){var _pV=B(_8q(_pR)),_pW=new T(function(){return B(A2(_8K,_pR,new T(function(){return B(_8w(_pR,_pS,_pT,_pU,_pS,_pT,_pU));})));});return new T3(0,B(A3(_a8,_pV,_pS,_pW)),B(A3(_a8,_pV,_pT,_pW)),B(A3(_a8,_pV,_pU,_pW)));},_pX=function(_pY,_pZ,_q0,_q1,_q2,_q3,_q4){var _q5=B(_8u(_pY));return new T3(0,B(A1(B(A1(_q5,_pZ)),_q2)),B(A1(B(A1(_q5,_q0)),_q3)),B(A1(B(A1(_q5,_q1)),_q4)));},_q6=function(_q7,_q8,_q9,_qa,_qb,_qc,_qd){var _qe=B(_86(_q7));return new T3(0,B(A1(B(A1(_qe,_q8)),_qb)),B(A1(B(A1(_qe,_q9)),_qc)),B(A1(B(A1(_qe,_qa)),_qd)));},_qf=function(_qg,_qh){var _qi=new T(function(){return E(E(_qg).a);}),_qj=new T(function(){return B(A2(_hQ,new T2(0,_qi,new T(function(){return E(E(_qg).b);})),_qh));}),_qk=new T(function(){var _ql=E(_qj),_qm=B(_pQ(_qi,_ql.a,_ql.b,_ql.c));return new T3(0,E(_qm.a),E(_qm.b),E(_qm.c));}),_qn=new T(function(){var _qo=E(_qh),_qp=E(_qk),_qq=B(_8q(_qi)),_qr=new T(function(){return B(A2(_8K,_qi,new T(function(){var _qs=E(_qj),_qt=_qs.a,_qu=_qs.b,_qv=_qs.c;return B(_8w(_qi,_qt,_qu,_qv,_qt,_qu,_qv));})));}),_qw=B(A3(_a8,_qq,new T(function(){return B(_8M(_qi,_qo));}),_qr)),_qx=B(_8s(_qq)),_qy=B(_pX(_qx,_qp.a,_qp.b,_qp.c,_qw,_qw,_qw)),_qz=B(_88(_qx)),_qA=B(_q6(_qx,_qo.a,_qo.b,_qo.c,B(A1(_qz,_qy.a)),B(A1(_qz,_qy.b)),B(A1(_qz,_qy.c))));return new T3(0,E(_qA.a),E(_qA.b),E(_qA.c));});return new T2(0,_qn,_qk);},_qB=function(_qC){return E(E(_qC).a);},_qD=function(_qE,_qF,_qG,_qH,_qI,_qJ,_qK){var _qL=B(_8w(_qE,_qI,_qJ,_qK,_qF,_qG,_qH)),_qM=B(_8s(B(_8q(_qE)))),_qN=B(_pX(_qM,_qI,_qJ,_qK,_qL,_qL,_qL)),_qO=B(_88(_qM));return new F(function(){return _q6(_qM,_qF,_qG,_qH,B(A1(_qO,_qN.a)),B(A1(_qO,_qN.b)),B(A1(_qO,_qN.c)));});},_qP=function(_qQ){return E(E(_qQ).a);},_qR=function(_qS,_qT,_qU,_qV){var _qW=new T(function(){var _qX=E(_qV),_qY=E(_qU),_qZ=B(_qD(_qS,_qX.a,_qX.b,_qX.c,_qY.a,_qY.b,_qY.c));return new T3(0,E(_qZ.a),E(_qZ.b),E(_qZ.c));}),_r0=new T(function(){return B(A2(_8K,_qS,new T(function(){var _r1=E(_qW),_r2=_r1.a,_r3=_r1.b,_r4=_r1.c;return B(_8w(_qS,_r2,_r3,_r4,_r2,_r3,_r4));})));});if(!B(A3(_qP,B(_qB(_qT)),_r0,new T(function(){return B(A2(_8I,B(_8s(B(_8q(_qS)))),_9Z));})))){var _r5=E(_qW),_r6=B(_pQ(_qS,_r5.a,_r5.b,_r5.c)),_r7=B(A2(_8K,_qS,new T(function(){var _r8=E(_qV),_r9=_r8.a,_ra=_r8.b,_rb=_r8.c;return B(_8w(_qS,_r9,_ra,_rb,_r9,_ra,_rb));}))),_rc=B(_8u(new T(function(){return B(_8s(new T(function(){return B(_8q(_qS));})));})));return new T3(0,B(A1(B(A1(_rc,_r6.a)),_r7)),B(A1(B(A1(_rc,_r6.b)),_r7)),B(A1(B(A1(_rc,_r6.c)),_r7)));}else{var _rd=B(A2(_8I,B(_8s(B(_8q(_qS)))),_9Z));return new T3(0,_rd,_rd,_rd);}},_re=0,_rf=new T3(0,E(_re),E(_re),E(_re)),_rg=function(_rh,_ri){while(1){var _rj=E(_rh);if(!_rj._){return E(_ri);}else{var _rk=_rj.b,_rl=E(_rj.a);if(_ri>_rl){_rh=_rk;continue;}else{_rh=_rk;_ri=_rl;continue;}}}},_rm=new T(function(){var _rn=eval("angleCount"),_ro=Number(_rn);return jsTrunc(_ro);}),_rp=new T(function(){return E(_rm);}),_rq=new T(function(){return B(unCStr("head"));}),_rr=new T(function(){return B(_lv(_rq));}),_rs=function(_rt,_ru,_rv){var _rw=E(_rt);if(!_rw._){return __Z;}else{var _rx=E(_ru);if(!_rx._){return __Z;}else{var _ry=_rx.a,_rz=E(_rv);if(!_rz._){return __Z;}else{var _rA=E(_rz.a),_rB=_rA.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_rw.a),E(_ry),E(_rB));}),new T2(1,new T(function(){return new T3(0,E(_ry),E(_rB),E(_rA.b));}),_w)),new T(function(){return B(_rs(_rw.b,_rx.b,_rz.b));},1));});}}}},_rC=new T(function(){return B(unCStr("tail"));}),_rD=new T(function(){return B(_lv(_rC));}),_rE=function(_rF,_rG){var _rH=E(_rF);if(!_rH._){return __Z;}else{var _rI=E(_rG);return (_rI._==0)?__Z:new T2(1,new T2(0,_rH.a,_rI.a),new T(function(){return B(_rE(_rH.b,_rI.b));}));}},_rJ=function(_rK,_rL){var _rM=E(_rK);if(!_rM._){return __Z;}else{var _rN=E(_rL);if(!_rN._){return __Z;}else{var _rO=E(_rM.a),_rP=_rO.b,_rQ=E(_rN.a).b,_rR=new T(function(){var _rS=new T(function(){return B(_rE(_rQ,new T(function(){var _rT=E(_rQ);if(!_rT._){return E(_rD);}else{return E(_rT.b);}},1)));},1);return B(_rs(_rP,new T(function(){var _rU=E(_rP);if(!_rU._){return E(_rD);}else{return E(_rU.b);}},1),_rS));});return new F(function(){return _n(new T2(1,new T(function(){var _rV=E(_rP);if(!_rV._){return E(_rr);}else{var _rW=E(_rQ);if(!_rW._){return E(_rr);}else{return new T3(0,E(_rO.a),E(_rV.a),E(_rW.a));}}}),_rR),new T(function(){return B(_rJ(_rM.b,_rN.b));},1));});}}},_rX=new T(function(){return 6.283185307179586/E(_rp);}),_rY=new T(function(){return E(_rp)-1;}),_rZ=new T1(0,1),_s0=function(_s1,_s2){var _s3=E(_s2),_s4=new T(function(){var _s5=B(_8s(_s1)),_s6=B(_s0(_s1,B(A3(_86,_s5,_s3,new T(function(){return B(A2(_8I,_s5,_rZ));})))));return new T2(1,_s6.a,_s6.b);});return new T2(0,_s3,_s4);},_s7=function(_s8){return E(E(_s8).d);},_s9=new T1(0,2),_sa=function(_sb,_sc){var _sd=E(_sc);if(!_sd._){return __Z;}else{var _se=_sd.a;return (!B(A1(_sb,_se)))?__Z:new T2(1,_se,new T(function(){return B(_sa(_sb,_sd.b));}));}},_sf=function(_sg,_sh,_si,_sj){var _sk=B(_s0(_sh,_si)),_sl=new T(function(){var _sm=B(_8s(_sh)),_sn=new T(function(){return B(A3(_a8,_sh,new T(function(){return B(A2(_8I,_sm,_rZ));}),new T(function(){return B(A2(_8I,_sm,_s9));})));});return B(A3(_86,_sm,_sj,_sn));});return new F(function(){return _sa(function(_so){return new F(function(){return A3(_s7,_sg,_so,_sl);});},new T2(1,_sk.a,_sk.b));});},_sp=new T(function(){return B(_sf(_pb,_jT,_re,_rY));}),_sq=function(_sr,_ss){while(1){var _st=E(_sr);if(!_st._){return E(_ss);}else{_sr=_st.b;_ss=_st.a;continue;}}},_su=new T(function(){return B(unCStr("last"));}),_sv=new T(function(){return B(_lv(_su));}),_sw=function(_sx){return new F(function(){return _sq(_sx,_sv);});},_sy=function(_sz){return new F(function(){return _sw(E(_sz).b);});},_sA=new T(function(){return B(unCStr("maximum"));}),_sB=new T(function(){return B(_lv(_sA));}),_sC=new T(function(){var _sD=eval("proceedCount"),_sE=Number(_sD);return jsTrunc(_sE);}),_sF=new T(function(){return E(_sC);}),_sG=1,_sH=new T(function(){return B(_sf(_pb,_jT,_sG,_sF));}),_sI=function(_sJ,_sK,_sL,_sM,_sN,_sO,_sP,_sQ,_sR,_sS,_sT,_sU,_sV,_sW){var _sX=new T(function(){var _sY=new T(function(){var _sZ=E(_sS),_t0=E(_sW),_t1=E(_sV),_t2=E(_sT),_t3=E(_sU),_t4=E(_sR);return new T3(0,_sZ*_t0-_t1*_t2,_t2*_t3-_t0*_t4,_t4*_t1-_t3*_sZ);}),_t5=function(_t6){var _t7=new T(function(){var _t8=E(_t6)/E(_rp);return (_t8+_t8)*3.141592653589793;}),_t9=new T(function(){return B(A1(_sJ,_t7));}),_ta=new T(function(){var _tb=new T(function(){var _tc=E(_t9)/E(_sF);return new T3(0,E(_tc),E(_tc),E(_tc));}),_td=function(_te,_tf){var _tg=E(_te);if(!_tg._){return new T2(0,_w,_tf);}else{var _th=new T(function(){var _ti=B(_qf(_pP,new T(function(){var _tj=E(_tf),_tk=E(_tj.a),_tl=E(_tj.b),_tm=E(_tb);return new T3(0,E(_tk.a)+E(_tl.a)*E(_tm.a),E(_tk.b)+E(_tl.b)*E(_tm.b),E(_tk.c)+E(_tl.c)*E(_tm.c));}))),_tn=_ti.a,_to=new T(function(){var _tp=E(_ti.b),_tq=E(E(_tf).b),_tr=B(_qD(_kl,_tq.a,_tq.b,_tq.c,_tp.a,_tp.b,_tp.c)),_ts=B(_pQ(_kl,_tr.a,_tr.b,_tr.c));return new T3(0,E(_ts.a),E(_ts.b),E(_ts.c));});return new T2(0,new T(function(){var _tt=E(_t9),_tu=E(_t7);return new T4(0,E(_tn),E(new T2(0,E(_tg.a)/E(_sF),E(_tt))),E(_tu),E(_to));}),new T2(0,_tn,_to));}),_tv=new T(function(){var _tw=B(_td(_tg.b,new T(function(){return E(E(_th).b);})));return new T2(0,_tw.a,_tw.b);});return new T2(0,new T2(1,new T(function(){return E(E(_th).a);}),new T(function(){return E(E(_tv).a);})),new T(function(){return E(E(_tv).b);}));}},_tx=function(_ty,_tz,_tA,_tB,_tC){var _tD=E(_ty);if(!_tD._){return new T2(0,_w,new T2(0,new T3(0,E(_tz),E(_tA),E(_tB)),_tC));}else{var _tE=new T(function(){var _tF=B(_qf(_pP,new T(function(){var _tG=E(_tC),_tH=E(_tb);return new T3(0,E(_tz)+E(_tG.a)*E(_tH.a),E(_tA)+E(_tG.b)*E(_tH.b),E(_tB)+E(_tG.c)*E(_tH.c));}))),_tI=_tF.a,_tJ=new T(function(){var _tK=E(_tF.b),_tL=E(_tC),_tM=B(_qD(_kl,_tL.a,_tL.b,_tL.c,_tK.a,_tK.b,_tK.c)),_tN=B(_pQ(_kl,_tM.a,_tM.b,_tM.c));return new T3(0,E(_tN.a),E(_tN.b),E(_tN.c));});return new T2(0,new T(function(){var _tO=E(_t9),_tP=E(_t7);return new T4(0,E(_tI),E(new T2(0,E(_tD.a)/E(_sF),E(_tO))),E(_tP),E(_tJ));}),new T2(0,_tI,_tJ));}),_tQ=new T(function(){var _tR=B(_td(_tD.b,new T(function(){return E(E(_tE).b);})));return new T2(0,_tR.a,_tR.b);});return new T2(0,new T2(1,new T(function(){return E(E(_tE).a);}),new T(function(){return E(E(_tQ).a);})),new T(function(){return E(E(_tQ).b);}));}};return E(B(_tx(_sH,_sM,_sN,_sO,new T(function(){var _tS=E(_sY),_tT=E(_t7)+_sP,_tU=Math.cos(_tT),_tV=Math.sin(_tT);return new T3(0,E(_sR)*_tU+E(_tS.a)*_tV,E(_sS)*_tU+E(_tS.b)*_tV,E(_sT)*_tU+E(_tS.c)*_tV);}))).a);});return new T2(0,new T(function(){var _tW=E(_t9),_tX=E(_t7);return new T4(0,E(new T3(0,E(_sM),E(_sN),E(_sO))),E(new T2(0,E(_re),E(_tW))),E(_tX),E(_rf));}),_ta);};return B(_pD(_t5,_sp));}),_tY=new T(function(){var _tZ=function(_u0){return new F(function(){return A1(_sJ,new T(function(){return B(_jM(_u0,_rX));}));});},_u1=B(_pD(_tZ,_sp));if(!_u1._){return E(_sB);}else{return B(_rg(_u1.b,E(_u1.a)));}}),_u2=new T(function(){var _u3=new T(function(){var _u4=B(_n(_sX,new T2(1,new T(function(){var _u5=E(_sX);if(!_u5._){return E(_rr);}else{return E(_u5.a);}}),_w)));if(!_u4._){return E(_rD);}else{return E(_u4.b);}},1);return B(_rJ(_sX,_u3));});return new T3(0,_u2,new T(function(){return B(_pD(_sy,_sX));}),_tY);},_u6=function(_u7,_u8,_u9,_ua,_ub,_uc,_ud,_ue,_uf,_ug,_uh,_ui,_uj,_uk,_ul,_um,_un,_uo){var _up=B(_qf(_pP,new T3(0,E(_ua),E(_ub),E(_uc)))),_uq=_up.b,_ur=E(_up.a),_us=B(_qR(_kl,_pb,_uq,new T3(0,E(_ue),E(_uf),E(_ug)))),_ut=E(_uq),_uu=_ut.a,_uv=_ut.b,_uw=_ut.c,_ux=B(_qD(_kl,_ui,_uj,_uk,_uu,_uv,_uw)),_uy=B(_pQ(_kl,_ux.a,_ux.b,_ux.c)),_uz=_uy.a,_uA=_uy.b,_uB=_uy.c,_uC=E(_ud),_uD=new T2(0,E(new T3(0,E(_us.a),E(_us.b),E(_us.c))),E(_uh)),_uE=B(_sI(_u7,_u8,_u9,_ur.a,_ur.b,_ur.c,_uC,_uD,_uz,_uA,_uB,_uu,_uv,_uw)),_uF=__lst2arr(B(_pD(_pM,_uE.a))),_uG=__lst2arr(B(_pD(_px,_uE.b)));return {_:0,a:_u7,b:_u8,c:_u9,d:new T2(0,E(_ur),E(_uC)),e:_uD,f:new T3(0,E(_uz),E(_uA),E(_uB)),g:_ut,h:_uF,i:_uG,j:E(_uE.c)};},_uH=1.0e-2,_uI=function(_uJ,_uK,_uL,_uM,_uN,_uO,_uP,_uQ,_uR,_uS,_uT,_uU,_uV,_uW,_uX,_uY,_uZ,_v0){var _v1=B(_oh(_jP,_uQ,_uR,_uS,_uT,_uH,_uH,_uH,_uH)),_v2=E(_v1.a),_v3=B(_os(_jP,_uM,_uN,_uO,_uP,_v2.a,_v2.b,_v2.c,_v1.b)),_v4=E(_v3.a);return new F(function(){return _u6(_uJ,_uK,_uL,_v4.a,_v4.b,_v4.c,_v3.b,_uQ,_uR,_uS,_uT,_uU,_uV,_uW,_uX,_uY,_uZ,_v0);});},_v5=function(_v6){var _v7=E(_v6),_v8=E(_v7.d),_v9=E(_v8.a),_va=E(_v7.e),_vb=E(_va.a),_vc=E(_v7.f),_vd=B(_uI(_v7.a,_v7.b,_v7.c,_v9.a,_v9.b,_v9.c,_v8.b,_vb.a,_vb.b,_vb.c,_va.b,_vc.a,_vc.b,_vc.c,_v7.g,_v7.h,_v7.i,_v7.j));return {_:0,a:E(_vd.a),b:E(_vd.b),c:E(_vd.c),d:E(_vd.d),e:E(_vd.e),f:E(_vd.f),g:E(_vd.g),h:_vd.h,i:_vd.i,j:_vd.j};},_ve=function(_vf,_vg,_vh,_vi,_vj,_vk,_vl,_vm,_vn){var _vo=B(_8s(B(_8q(_vf))));return new F(function(){return A3(_86,_vo,new T(function(){return B(_8w(_vf,_vg,_vh,_vi,_vk,_vl,_vm));}),new T(function(){return B(A3(_8u,_vo,_vj,_vn));}));});},_vp=new T(function(){return B(unCStr("base"));}),_vq=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_vr=new T(function(){return B(unCStr("IOException"));}),_vs=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_vp,_vq,_vr),_vt=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_vs,_w,_w),_vu=function(_vv){return E(_vt);},_vw=function(_vx){var _vy=E(_vx);return new F(function(){return _3G(B(_3E(_vy.a)),_vu,_vy.b);});},_vz=new T(function(){return B(unCStr(": "));}),_vA=new T(function(){return B(unCStr(")"));}),_vB=new T(function(){return B(unCStr(" ("));}),_vC=new T(function(){return B(unCStr("interrupted"));}),_vD=new T(function(){return B(unCStr("system error"));}),_vE=new T(function(){return B(unCStr("unsatisified constraints"));}),_vF=new T(function(){return B(unCStr("user error"));}),_vG=new T(function(){return B(unCStr("permission denied"));}),_vH=new T(function(){return B(unCStr("illegal operation"));}),_vI=new T(function(){return B(unCStr("end of file"));}),_vJ=new T(function(){return B(unCStr("resource exhausted"));}),_vK=new T(function(){return B(unCStr("resource busy"));}),_vL=new T(function(){return B(unCStr("does not exist"));}),_vM=new T(function(){return B(unCStr("already exists"));}),_vN=new T(function(){return B(unCStr("resource vanished"));}),_vO=new T(function(){return B(unCStr("timeout"));}),_vP=new T(function(){return B(unCStr("unsupported operation"));}),_vQ=new T(function(){return B(unCStr("hardware fault"));}),_vR=new T(function(){return B(unCStr("inappropriate type"));}),_vS=new T(function(){return B(unCStr("invalid argument"));}),_vT=new T(function(){return B(unCStr("failed"));}),_vU=new T(function(){return B(unCStr("protocol error"));}),_vV=function(_vW,_vX){switch(E(_vW)){case 0:return new F(function(){return _n(_vM,_vX);});break;case 1:return new F(function(){return _n(_vL,_vX);});break;case 2:return new F(function(){return _n(_vK,_vX);});break;case 3:return new F(function(){return _n(_vJ,_vX);});break;case 4:return new F(function(){return _n(_vI,_vX);});break;case 5:return new F(function(){return _n(_vH,_vX);});break;case 6:return new F(function(){return _n(_vG,_vX);});break;case 7:return new F(function(){return _n(_vF,_vX);});break;case 8:return new F(function(){return _n(_vE,_vX);});break;case 9:return new F(function(){return _n(_vD,_vX);});break;case 10:return new F(function(){return _n(_vU,_vX);});break;case 11:return new F(function(){return _n(_vT,_vX);});break;case 12:return new F(function(){return _n(_vS,_vX);});break;case 13:return new F(function(){return _n(_vR,_vX);});break;case 14:return new F(function(){return _n(_vQ,_vX);});break;case 15:return new F(function(){return _n(_vP,_vX);});break;case 16:return new F(function(){return _n(_vO,_vX);});break;case 17:return new F(function(){return _n(_vN,_vX);});break;default:return new F(function(){return _n(_vC,_vX);});}},_vY=new T(function(){return B(unCStr("}"));}),_vZ=new T(function(){return B(unCStr("{handle: "));}),_w0=function(_w1,_w2,_w3,_w4,_w5,_w6){var _w7=new T(function(){var _w8=new T(function(){var _w9=new T(function(){var _wa=E(_w4);if(!_wa._){return E(_w6);}else{var _wb=new T(function(){return B(_n(_wa,new T(function(){return B(_n(_vA,_w6));},1)));},1);return B(_n(_vB,_wb));}},1);return B(_vV(_w2,_w9));}),_wc=E(_w3);if(!_wc._){return E(_w8);}else{return B(_n(_wc,new T(function(){return B(_n(_vz,_w8));},1)));}}),_wd=E(_w5);if(!_wd._){var _we=E(_w1);if(!_we._){return E(_w7);}else{var _wf=E(_we.a);if(!_wf._){var _wg=new T(function(){var _wh=new T(function(){return B(_n(_vY,new T(function(){return B(_n(_vz,_w7));},1)));},1);return B(_n(_wf.a,_wh));},1);return new F(function(){return _n(_vZ,_wg);});}else{var _wi=new T(function(){var _wj=new T(function(){return B(_n(_vY,new T(function(){return B(_n(_vz,_w7));},1)));},1);return B(_n(_wf.a,_wj));},1);return new F(function(){return _n(_vZ,_wi);});}}}else{return new F(function(){return _n(_wd.a,new T(function(){return B(_n(_vz,_w7));},1));});}},_wk=function(_wl){var _wm=E(_wl);return new F(function(){return _w0(_wm.a,_wm.b,_wm.c,_wm.d,_wm.f,_w);});},_wn=function(_wo,_wp,_wq){var _wr=E(_wp);return new F(function(){return _w0(_wr.a,_wr.b,_wr.c,_wr.d,_wr.f,_wq);});},_ws=function(_wt,_wu){var _wv=E(_wt);return new F(function(){return _w0(_wv.a,_wv.b,_wv.c,_wv.d,_wv.f,_wu);});},_ww=function(_wx,_wy){return new F(function(){return _49(_ws,_wx,_wy);});},_wz=new T3(0,_wn,_wk,_ww),_wA=new T(function(){return new T5(0,_vu,_wz,_wB,_vw,_wk);}),_wB=function(_wC){return new T2(0,_wA,_wC);},_wD=__Z,_wE=7,_wF=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_wG=new T6(0,_wD,_wE,_w,_wF,_wD,_wD),_wH=new T(function(){return B(_wB(_wG));}),_wI=function(_){return new F(function(){return die(_wH);});},_wJ=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_wK=new T6(0,_wD,_wE,_w,_wJ,_wD,_wD),_wL=new T(function(){return B(_wB(_wK));}),_wM=function(_){return new F(function(){return die(_wL);});},_wN=function(_wO,_){return new T2(0,_w,_wO);},_wP=0.6,_wQ=1,_wR=new T(function(){return B(unCStr(")"));}),_wS=function(_wT,_wU){var _wV=new T(function(){var _wW=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_iF(0,_wT,_w)),_wR));})));},1);return B(_n(B(_iF(0,_wU,_w)),_wW));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_wV)));});},_wX=function(_wY,_wZ){var _x0=new T(function(){var _x1=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_iF(0,_wZ,_w)),_wR));})));},1);return B(_n(B(_iF(0,_wY,_w)),_x1));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_x0)));});},_x2=function(_x3){var _x4=E(_x3);if(!_x4._){return E(_wN);}else{var _x5=new T(function(){return B(_x2(_x4.b));}),_x6=function(_x7){var _x8=E(_x7);if(!_x8._){return E(_x5);}else{var _x9=_x8.a,_xa=new T(function(){return B(_x6(_x8.b));}),_xb=new T(function(){return 0.1*E(E(_x9).e)/1.0e-2;}),_xc=new T(function(){var _xd=E(_x9);if(_xd.a!=_xd.b){return E(_wQ);}else{return E(_wP);}}),_xe=function(_xf,_){var _xg=E(_xf),_xh=_xg.c,_xi=_xg.d,_xj=E(_xg.a),_xk=E(_xg.b),_xl=E(_x9),_xm=_xl.a,_xn=_xl.b,_xo=E(_xl.c),_xp=_xo.b,_xq=E(_xo.a),_xr=_xq.a,_xs=_xq.b,_xt=_xq.c,_xu=E(_xl.d),_xv=_xu.b,_xw=E(_xu.a),_xx=_xw.a,_xy=_xw.b,_xz=_xw.c;if(_xj>_xm){return new F(function(){return _wM(_);});}else{if(_xm>_xk){return new F(function(){return _wM(_);});}else{if(_xj>_xn){return new F(function(){return _wI(_);});}else{if(_xn>_xk){return new F(function(){return _wI(_);});}else{var _xA=_xm-_xj|0;if(0>_xA){return new F(function(){return _wS(_xh,_xA);});}else{if(_xA>=_xh){return new F(function(){return _wS(_xh,_xA);});}else{var _xB=E(_xi[_xA]),_xC=E(_xB.c),_xD=_xC.b,_xE=E(_xC.a),_xF=_xE.a,_xG=_xE.b,_xH=_xE.c,_xI=E(_xB.e),_xJ=E(_xI.a),_xK=B(_oh(_jP,_xr,_xs,_xt,_xp,_xF,_xG,_xH,_xD)),_xL=E(_xK.a),_xM=B(_oh(_jP,_xL.a,_xL.b,_xL.c,_xK.b,_xr,_xs,_xt,_xp)),_xN=E(_xM.a),_xO=_xn-_xj|0;if(0>_xO){return new F(function(){return _wX(_xO,_xh);});}else{if(_xO>=_xh){return new F(function(){return _wX(_xO,_xh);});}else{var _xP=E(_xi[_xO]),_xQ=E(_xP.c),_xR=_xQ.b,_xS=E(_xQ.a),_xT=_xS.a,_xU=_xS.b,_xV=_xS.c,_xW=E(_xP.e),_xX=E(_xW.a),_xY=B(_oh(_jP,_xx,_xy,_xz,_xv,_xT,_xU,_xV,_xR)),_xZ=E(_xY.a),_y0=B(_oh(_jP,_xZ.a,_xZ.b,_xZ.c,_xY.b,_xx,_xy,_xz,_xv)),_y1=E(_y0.a),_y2=E(_xN.a)+E(_xN.b)+E(_xN.c)+E(_xM.b)+E(_y1.a)+E(_y1.b)+E(_y1.c)+E(_y0.b);if(!_y2){var _y3=B(A2(_xa,_xg,_));return new T2(0,new T2(1,_ik,new T(function(){return E(E(_y3).a);})),new T(function(){return E(E(_y3).b);}));}else{var _y4=new T(function(){return  -((B(_ve(_kl,_xJ.a,_xJ.b,_xJ.c,_xI.b,_xr,_xs,_xt,_xp))-B(_ve(_kl,_xX.a,_xX.b,_xX.c,_xW.b,_xx,_xy,_xz,_xv))-E(_xb))/_y2);}),_y5=function(_y6,_y7,_y8,_y9,_){var _ya=new T(function(){var _yb=function(_yc,_yd,_ye,_yf,_yg){if(_yc>_xn){return E(_yg);}else{if(_xn>_yd){return E(_yg);}else{var _yh=function(_){var _yi=newArr(_ye,_nC),_yj=_yi,_yk=function(_yl,_){while(1){if(_yl!=_ye){var _=_yj[_yl]=_yf[_yl],_ym=_yl+1|0;_yl=_ym;continue;}else{return E(_);}}},_=B(_yk(0,_)),_yn=_xn-_yc|0;if(0>_yn){return new F(function(){return _wX(_yn,_ye);});}else{if(_yn>=_ye){return new F(function(){return _wX(_yn,_ye);});}else{var _=_yj[_yn]=new T(function(){var _yo=E(_yf[_yn]),_yp=E(_yo.e),_yq=E(_yp.a),_yr=B(_oh(_jP,_xT,_xU,_xV,_xR,_xx,_xy,_xz,_xv)),_ys=E(_yr.a),_yt=E(_y4)*E(_xc),_yu=B(_oh(_jP,_ys.a,_ys.b,_ys.c,_yr.b,_yt,_yt,_yt,_yt)),_yv=E(_yu.a),_yw=B(_os(_jP,_yq.a,_yq.b,_yq.c,_yp.b, -E(_yv.a), -E(_yv.b), -E(_yv.c), -E(_yu.b)));return {_:0,a:E(_yo.a),b:E(_yo.b),c:E(_yo.c),d:E(_yo.d),e:E(new T2(0,E(_yw.a),E(_yw.b))),f:E(_yo.f),g:E(_yo.g),h:_yo.h,i:_yo.i,j:_yo.j};});return new T4(0,E(_yc),E(_yd),_ye,_yj);}}};return new F(function(){return _nH(_yh);});}}};if(_y6>_xm){return B(_yb(_y6,_y7,_y8,_y9,new T4(0,E(_y6),E(_y7),_y8,_y9)));}else{if(_xm>_y7){return B(_yb(_y6,_y7,_y8,_y9,new T4(0,E(_y6),E(_y7),_y8,_y9)));}else{var _yx=function(_){var _yy=newArr(_y8,_nC),_yz=_yy,_yA=function(_yB,_){while(1){if(_yB!=_y8){var _=_yz[_yB]=_y9[_yB],_yC=_yB+1|0;_yB=_yC;continue;}else{return E(_);}}},_=B(_yA(0,_)),_yD=_xm-_y6|0;if(0>_yD){return new F(function(){return _wS(_y8,_yD);});}else{if(_yD>=_y8){return new F(function(){return _wS(_y8,_yD);});}else{var _=_yz[_yD]=new T(function(){var _yE=E(_y9[_yD]),_yF=E(_yE.e),_yG=E(_yF.a),_yH=B(_oh(_jP,_xF,_xG,_xH,_xD,_xr,_xs,_xt,_xp)),_yI=E(_yH.a),_yJ=E(_y4)*E(_xc),_yK=B(_oh(_jP,_yI.a,_yI.b,_yI.c,_yH.b,_yJ,_yJ,_yJ,_yJ)),_yL=E(_yK.a),_yM=B(_os(_jP,_yG.a,_yG.b,_yG.c,_yF.b,_yL.a,_yL.b,_yL.c,_yK.b));return {_:0,a:E(_yE.a),b:E(_yE.b),c:E(_yE.c),d:E(_yE.d),e:E(new T2(0,E(_yM.a),E(_yM.b))),f:E(_yE.f),g:E(_yE.g),h:_yE.h,i:_yE.i,j:_yE.j};});return new T4(0,E(_y6),E(_y7),_y8,_yz);}}},_yN=B(_nH(_yx));return B(_yb(E(_yN.a),E(_yN.b),_yN.c,_yN.d,_yN));}}});return new T2(0,_ik,_ya);};if(!E(_xl.f)){var _yO=B(_y5(_xj,_xk,_xh,_xi,_)),_yP=B(A2(_xa,new T(function(){return E(E(_yO).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_yO).a);}),new T(function(){return E(E(_yP).a);})),new T(function(){return E(E(_yP).b);}));}else{if(E(_y4)<0){var _yQ=B(A2(_xa,_xg,_));return new T2(0,new T2(1,_ik,new T(function(){return E(E(_yQ).a);})),new T(function(){return E(E(_yQ).b);}));}else{var _yR=B(_y5(_xj,_xk,_xh,_xi,_)),_yS=B(A2(_xa,new T(function(){return E(E(_yR).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_yR).a);}),new T(function(){return E(E(_yS).a);})),new T(function(){return E(E(_yS).b);}));}}}}}}}}}}}};return E(_xe);}};return new F(function(){return _x6(_x4.a);});}},_yT=function(_,_yU){var _yV=new T(function(){return B(_x2(E(_yU).a));}),_yW=function(_yX){var _yY=E(_yX);return (_yY==1)?E(new T2(1,_yV,_w)):new T2(1,_yV,new T(function(){return B(_yW(_yY-1|0));}));},_yZ=B(_nm(B(_yW(5)),new T(function(){return E(E(_yU).b);}),_)),_z0=new T(function(){return B(_o1(_nl,_j7,_v5,new T(function(){return E(E(_yZ).b);})));});return new T2(0,_ik,_z0);},_z1=function(_z2,_z3,_z4,_z5,_z6){var _z7=B(_8s(B(_8q(_z2))));return new F(function(){return A3(_86,_z7,new T(function(){return B(A3(_8u,_z7,_z3,_z5));}),new T(function(){return B(A3(_8u,_z7,_z4,_z6));}));});},_z8=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_z9=new T6(0,_wD,_wE,_w,_z8,_wD,_wD),_za=new T(function(){return B(_wB(_z9));}),_zb=function(_){return new F(function(){return die(_za);});},_zc=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_zd=new T6(0,_wD,_wE,_w,_zc,_wD,_wD),_ze=new T(function(){return B(_wB(_zd));}),_zf=function(_){return new F(function(){return die(_ze);});},_zg=false,_zh=true,_zi=function(_zj){var _zk=E(_zj),_zl=_zk.b,_zm=E(_zk.d),_zn=E(_zk.e),_zo=E(_zn.a),_zp=E(_zk.g),_zq=B(A1(_zl,_zm.a)),_zr=B(_qD(_kl,_zq.a,_zq.b,_zq.c,_zp.a,_zp.b,_zp.c));return {_:0,a:E(_zk.a),b:E(_zl),c:E(_zk.c),d:E(_zm),e:E(new T2(0,E(new T3(0,E(_zo.a)+E(_zr.a)*1.0e-2,E(_zo.b)+E(_zr.b)*1.0e-2,E(_zo.c)+E(_zr.c)*1.0e-2)),E(_zn.b))),f:E(_zk.f),g:E(_zp),h:_zk.h,i:_zk.i,j:_zk.j};},_zs=new T(function(){return eval("__strict(collideBound)");}),_zt=new T(function(){return eval("__strict(mouseContact)");}),_zu=new T(function(){return eval("__strict(collide)");}),_zv=function(_zw){var _zx=E(_zw);if(!_zx._){return __Z;}else{return new F(function(){return _n(_zx.a,new T(function(){return B(_zv(_zx.b));},1));});}},_zy=0,_zz=new T3(0,E(_zy),E(_zy),E(_zy)),_zA=new T2(0,E(_zz),E(_zy)),_zB=new T2(0,_kl,_pb),_zC=new T(function(){return B(_hQ(_zB));}),_zD=function(_zE,_){var _zF=B(_o1(_nl,_j7,_zi,_zE)),_zG=E(_zF.a),_zH=E(_zF.b);if(_zG<=_zH){var _zI=function(_zJ,_zK,_zL,_zM,_zN,_){if(_zK>_zJ){return new F(function(){return _zf(_);});}else{if(_zJ>_zL){return new F(function(){return _zf(_);});}else{var _zO=new T(function(){var _zP=_zJ-_zK|0;if(0>_zP){return B(_wX(_zP,_zM));}else{if(_zP>=_zM){return B(_wX(_zP,_zM));}else{return E(_zN[_zP]);}}}),_zQ=function(_zR,_zS,_zT,_zU,_zV,_){var _zW=E(_zR);if(!_zW._){return new T2(0,_w,new T4(0,E(_zS),E(_zT),_zU,_zV));}else{var _zX=E(_zW.a);if(_zS>_zX){return new F(function(){return _zb(_);});}else{if(_zX>_zT){return new F(function(){return _zb(_);});}else{var _zY=_zX-_zS|0;if(0>_zY){return new F(function(){return _wS(_zU,_zY);});}else{if(_zY>=_zU){return new F(function(){return _wS(_zU,_zY);});}else{var _zZ=__app2(E(_zu),B(_iv(E(_zO))),B(_iv(E(_zV[_zY])))),_A0=__arr2lst(0,_zZ),_A1=B(_kY(_A0,_)),_A2=B(_zQ(_zW.b,_zS,_zT,_zU,_zV,_)),_A3=new T(function(){var _A4=new T(function(){return _zJ!=_zX;}),_A5=function(_A6){var _A7=E(_A6);if(!_A7._){return __Z;}else{var _A8=_A7.b,_A9=E(_A7.a),_Aa=E(_A9.b),_Ab=E(_A9.a),_Ac=E(_A9.c),_Ad=_Ac.a,_Ae=_Ac.b,_Af=E(_A9.e),_Ag=E(_A9.d),_Ah=_Ag.a,_Ai=_Ag.b,_Aj=E(_A9.f),_Ak=new T(function(){var _Al=B(_pQ(_kl,_Aj.a,_Aj.b,_Aj.c)),_Am=Math.sqrt(B(_z1(_kl,_Ah,_Ai,_Ah,_Ai)));return new T3(0,_Am*E(_Al.a),_Am*E(_Al.b),_Am*E(_Al.c));}),_An=new T(function(){var _Ao=B(_pQ(_kl,_Af.a,_Af.b,_Af.c)),_Ap=Math.sqrt(B(_z1(_kl,_Ad,_Ae,_Ad,_Ae)));return new T3(0,_Ap*E(_Ao.a),_Ap*E(_Ao.b),_Ap*E(_Ao.c));}),_Aq=new T(function(){var _Ar=B(A1(_zC,_Aa)),_As=B(_pQ(_kl,_Ar.a,_Ar.b,_Ar.c));return new T3(0,E(_As.a),E(_As.b),E(_As.c));}),_At=new T(function(){var _Au=B(A1(_zC,_Ab)),_Av=B(_pQ(_kl,_Au.a,_Au.b,_Au.c));return new T3(0,E(_Av.a),E(_Av.b),E(_Av.c));}),_Aw=E(_Aa.a)+ -E(_Ab.a),_Ax=E(_Aa.b)+ -E(_Ab.b),_Ay=E(_Aa.c)+ -E(_Ab.c),_Az=new T(function(){return Math.sqrt(B(_8w(_kl,_Aw,_Ax,_Ay,_Aw,_Ax,_Ay)));}),_AA=new T(function(){var _AB=1/E(_Az);return new T3(0,_Aw*_AB,_Ax*_AB,_Ay*_AB);}),_AC=new T(function(){if(!E(_A9.g)){return E(_AA);}else{var _AD=E(_AA);return new T3(0,-1*E(_AD.a),-1*E(_AD.b),-1*E(_AD.c));}}),_AE=new T(function(){if(!E(_A9.h)){return E(_AA);}else{var _AF=E(_AA);return new T3(0,-1*E(_AF.a),-1*E(_AF.b),-1*E(_AF.c));}});return (!E(_A4))?new T2(1,new T(function(){var _AG=E(_AC),_AH=E(_AG.b),_AI=E(_AG.c),_AJ=E(_AG.a),_AK=E(_At),_AL=E(_AK.c),_AM=E(_AK.b),_AN=E(_AK.a),_AO=E(_An),_AP=E(_AO.c),_AQ=E(_AO.b),_AR=E(_AO.a),_AS=_AH*_AL-_AM*_AI,_AT=_AI*_AN-_AL*_AJ,_AU=_AJ*_AM-_AN*_AH,_AV=B(_8w(_kl,_AT*_AP-_AQ*_AU,_AU*_AR-_AP*_AS,_AS*_AQ-_AR*_AT,_AN,_AM,_AL));return new T6(0,_zJ,_zX,E(new T2(0,E(new T3(0,E(_AS),E(_AT),E(_AU))),E(_AV))),E(_zA),_Az,_zg);}),new T2(1,new T(function(){var _AW=E(_AE),_AX=E(_AW.b),_AY=E(_AW.c),_AZ=E(_AW.a),_B0=E(_Aq),_B1=E(_B0.c),_B2=E(_B0.b),_B3=E(_B0.a),_B4=E(_Ak),_B5=E(_B4.c),_B6=E(_B4.b),_B7=E(_B4.a),_B8=_AX*_B1-_B2*_AY,_B9=_AY*_B3-_B1*_AZ,_Ba=_AZ*_B2-_B3*_AX,_Bb=B(_8w(_kl,_B9*_B5-_B6*_Ba,_Ba*_B7-_B5*_B8,_B8*_B6-_B7*_B9,_B3,_B2,_B1));return new T6(0,_zJ,_zX,E(_zA),E(new T2(0,E(new T3(0,E(_B8),E(_B9),E(_Ba))),E(_Bb))),_Az,_zg);}),new T(function(){return B(_A5(_A8));}))):new T2(1,new T(function(){var _Bc=E(_AC),_Bd=E(_Bc.b),_Be=E(_Bc.c),_Bf=E(_Bc.a),_Bg=E(_At),_Bh=_Bg.a,_Bi=_Bg.b,_Bj=_Bg.c,_Bk=B(_qD(_kl,_Bf,_Bd,_Be,_Bh,_Bi,_Bj)),_Bl=E(_An),_Bm=E(_Bl.c),_Bn=E(_Bl.b),_Bo=E(_Bl.a),_Bp=B(_8w(_kl,_Bd*_Bm-_Bn*_Be,_Be*_Bo-_Bm*_Bf,_Bf*_Bn-_Bo*_Bd,_Bh,_Bi,_Bj)),_Bq=E(_AE),_Br=E(_Bq.b),_Bs=E(_Bq.c),_Bt=E(_Bq.a),_Bu=E(_Aq),_Bv=_Bu.a,_Bw=_Bu.b,_Bx=_Bu.c,_By=B(_qD(_kl,_Bt,_Br,_Bs,_Bv,_Bw,_Bx)),_Bz=E(_Ak),_BA=E(_Bz.c),_BB=E(_Bz.b),_BC=E(_Bz.a),_BD=B(_8w(_kl,_Br*_BA-_BB*_Bs,_Bs*_BC-_BA*_Bt,_Bt*_BB-_BC*_Br,_Bv,_Bw,_Bx));return new T6(0,_zJ,_zX,E(new T2(0,E(new T3(0,E(_Bk.a),E(_Bk.b),E(_Bk.c))),E(_Bp))),E(new T2(0,E(new T3(0,E(_By.a),E(_By.b),E(_By.c))),E(_BD))),_Az,_zh);}),new T(function(){return B(_A5(_A8));}));}};return B(_A5(_A1));});return new T2(0,new T2(1,_A3,new T(function(){return E(E(_A2).a);})),new T(function(){return E(E(_A2).b);}));}}}}}},_BE=B(_zQ(B(_mp(_zJ,_zH)),_zK,_zL,_zM,_zN,_)),_BF=E(_zO),_BG=E(_BF.d).a,_BH=__app1(E(_zs),B(_iv(_BF))),_BI=__arr2lst(0,_BH),_BJ=B(_kY(_BI,_)),_BK=__app1(E(_zt),_zJ),_BL=__arr2lst(0,_BK),_BM=B(_kY(_BL,_));if(_zJ!=_zH){var _BN=E(_BE),_BO=E(_BN.b),_BP=B(_zI(_zJ+1|0,E(_BO.a),E(_BO.b),_BO.c,_BO.d,_)),_BQ=new T(function(){var _BR=new T(function(){var _BS=B(A1(_zC,_BG)),_BT=B(_pQ(_kl,_BS.a,_BS.b,_BS.c));return new T3(0,E(_BT.a),E(_BT.b),E(_BT.c));}),_BU=new T(function(){var _BV=new T(function(){return B(_zv(_BN.a));}),_BW=function(_BX){var _BY=E(_BX);if(!_BY._){return E(_BV);}else{var _BZ=E(_BY.a),_C0=E(_BZ.b),_C1=E(_BZ.a),_C2=E(_BZ.c),_C3=_C2.a,_C4=_C2.b,_C5=E(_BZ.e);return new T2(1,new T(function(){var _C6=E(_C0.a)+ -E(_C1.a),_C7=E(_C0.b)+ -E(_C1.b),_C8=E(_C0.c)+ -E(_C1.c),_C9=B(A1(_zC,_C1)),_Ca=B(_pQ(_kl,_C9.a,_C9.b,_C9.c)),_Cb=_Ca.a,_Cc=_Ca.b,_Cd=_Ca.c,_Ce=Math.sqrt(B(_8w(_kl,_C6,_C7,_C8,_C6,_C7,_C8))),_Cf=1/_Ce,_Cg=_C6*_Cf,_Ch=_C7*_Cf,_Ci=_C8*_Cf,_Cj=B(_qD(_kl,_Cg,_Ch,_Ci,_Cb,_Cc,_Cd)),_Ck=B(_pQ(_kl,_C5.a,_C5.b,_C5.c)),_Cl=Math.sqrt(B(_z1(_kl,_C3,_C4,_C3,_C4))),_Cm=_Cl*E(_Ck.a),_Cn=_Cl*E(_Ck.b),_Co=_Cl*E(_Ck.c),_Cp=B(_8w(_kl,_Ch*_Co-_Cn*_Ci,_Ci*_Cm-_Co*_Cg,_Cg*_Cn-_Cm*_Ch,_Cb,_Cc,_Cd));return new T6(0,_zJ,_zJ,E(new T2(0,E(new T3(0,E(_Cj.a),E(_Cj.b),E(_Cj.c))),E(_Cp))),E(_zA),_Ce,_zh);}),new T(function(){return B(_BW(_BY.b));}));}};return B(_BW(_BJ));}),_Cq=function(_Cr){var _Cs=E(_Cr);if(!_Cs._){return E(_BU);}else{var _Ct=E(_Cs.a),_Cu=E(_Ct.b),_Cv=new T(function(){var _Cw=E(_BG),_Cx=E(_Cu.c)+ -E(_Cw.c),_Cy=E(_Cu.b)+ -E(_Cw.b),_Cz=E(_Cu.a)+ -E(_Cw.a),_CA=Math.sqrt(B(_8w(_kl,_Cz,_Cy,_Cx,_Cz,_Cy,_Cx))),_CB=function(_CC,_CD,_CE){var _CF=E(_BR),_CG=_CF.a,_CH=_CF.b,_CI=_CF.c,_CJ=B(_qD(_kl,_CC,_CD,_CE,_CG,_CH,_CI)),_CK=B(_8w(_kl,_CD*0-0*_CE,_CE*0-0*_CC,_CC*0-0*_CD,_CG,_CH,_CI));return new T6(0,_zJ,_zJ,new T2(0,E(new T3(0,E(_CJ.a),E(_CJ.b),E(_CJ.c))),E(_CK)),_zA,_CA,_zh);};if(!E(_Ct.g)){var _CL=1/_CA,_CM=B(_CB(_Cz*_CL,_Cy*_CL,_Cx*_CL));return new T6(0,_CM.a,_CM.b,E(_CM.c),E(_CM.d),_CM.e,_CM.f);}else{var _CN=1/_CA,_CO=B(_CB(-1*_Cz*_CN,-1*_Cy*_CN,-1*_Cx*_CN));return new T6(0,_CO.a,_CO.b,E(_CO.c),E(_CO.d),_CO.e,_CO.f);}});return new T2(1,_Cv,new T(function(){return B(_Cq(_Cs.b));}));}};return B(_Cq(_BM));});return new T2(0,new T2(1,_BQ,new T(function(){return E(E(_BP).a);})),new T(function(){return E(E(_BP).b);}));}else{var _CP=new T(function(){var _CQ=new T(function(){var _CR=B(A1(_zC,_BG)),_CS=B(_pQ(_kl,_CR.a,_CR.b,_CR.c));return new T3(0,E(_CS.a),E(_CS.b),E(_CS.c));}),_CT=new T(function(){var _CU=new T(function(){return B(_zv(E(_BE).a));}),_CV=function(_CW){var _CX=E(_CW);if(!_CX._){return E(_CU);}else{var _CY=E(_CX.a),_CZ=E(_CY.b),_D0=E(_CY.a),_D1=E(_CY.c),_D2=_D1.a,_D3=_D1.b,_D4=E(_CY.e);return new T2(1,new T(function(){var _D5=E(_CZ.a)+ -E(_D0.a),_D6=E(_CZ.b)+ -E(_D0.b),_D7=E(_CZ.c)+ -E(_D0.c),_D8=B(A1(_zC,_D0)),_D9=B(_pQ(_kl,_D8.a,_D8.b,_D8.c)),_Da=_D9.a,_Db=_D9.b,_Dc=_D9.c,_Dd=Math.sqrt(B(_8w(_kl,_D5,_D6,_D7,_D5,_D6,_D7))),_De=1/_Dd,_Df=_D5*_De,_Dg=_D6*_De,_Dh=_D7*_De,_Di=B(_qD(_kl,_Df,_Dg,_Dh,_Da,_Db,_Dc)),_Dj=B(_pQ(_kl,_D4.a,_D4.b,_D4.c)),_Dk=Math.sqrt(B(_z1(_kl,_D2,_D3,_D2,_D3))),_Dl=_Dk*E(_Dj.a),_Dm=_Dk*E(_Dj.b),_Dn=_Dk*E(_Dj.c),_Do=B(_8w(_kl,_Dg*_Dn-_Dm*_Dh,_Dh*_Dl-_Dn*_Df,_Df*_Dm-_Dl*_Dg,_Da,_Db,_Dc));return new T6(0,_zJ,_zJ,E(new T2(0,E(new T3(0,E(_Di.a),E(_Di.b),E(_Di.c))),E(_Do))),E(_zA),_Dd,_zh);}),new T(function(){return B(_CV(_CX.b));}));}};return B(_CV(_BJ));}),_Dp=function(_Dq){var _Dr=E(_Dq);if(!_Dr._){return E(_CT);}else{var _Ds=E(_Dr.a),_Dt=E(_Ds.b),_Du=new T(function(){var _Dv=E(_BG),_Dw=E(_Dt.c)+ -E(_Dv.c),_Dx=E(_Dt.b)+ -E(_Dv.b),_Dy=E(_Dt.a)+ -E(_Dv.a),_Dz=Math.sqrt(B(_8w(_kl,_Dy,_Dx,_Dw,_Dy,_Dx,_Dw))),_DA=function(_DB,_DC,_DD){var _DE=E(_CQ),_DF=_DE.a,_DG=_DE.b,_DH=_DE.c,_DI=B(_qD(_kl,_DB,_DC,_DD,_DF,_DG,_DH)),_DJ=B(_8w(_kl,_DC*0-0*_DD,_DD*0-0*_DB,_DB*0-0*_DC,_DF,_DG,_DH));return new T6(0,_zJ,_zJ,new T2(0,E(new T3(0,E(_DI.a),E(_DI.b),E(_DI.c))),E(_DJ)),_zA,_Dz,_zh);};if(!E(_Ds.g)){var _DK=1/_Dz,_DL=B(_DA(_Dy*_DK,_Dx*_DK,_Dw*_DK));return new T6(0,_DL.a,_DL.b,E(_DL.c),E(_DL.d),_DL.e,_DL.f);}else{var _DM=1/_Dz,_DN=B(_DA(-1*_Dy*_DM,-1*_Dx*_DM,-1*_Dw*_DM));return new T6(0,_DN.a,_DN.b,E(_DN.c),E(_DN.d),_DN.e,_DN.f);}});return new T2(1,_Du,new T(function(){return B(_Dp(_Dr.b));}));}};return B(_Dp(_BM));});return new T2(0,new T2(1,_CP,_w),new T(function(){return E(E(_BE).b);}));}}}},_DO=B(_zI(_zG,_zG,_zH,_zF.c,_zF.d,_));return new F(function(){return _yT(_,_DO);});}else{return new F(function(){return _yT(_,new T2(0,_w,_zF));});}},_DP=new T(function(){return eval("__strict(passObject)");}),_DQ=new T(function(){return eval("__strict(refresh)");}),_DR=function(_DS,_){var _DT=__app0(E(_DQ)),_DU=__app0(E(_iA)),_DV=E(_DS),_DW=_DV.c,_DX=_DV.d,_DY=E(_DV.a),_DZ=E(_DV.b);if(_DY<=_DZ){if(_DY>_DZ){return E(_iy);}else{if(0>=_DW){return new F(function(){return _iL(_DW,0);});}else{var _E0=E(_DP),_E1=__app2(_E0,_DY,B(_iv(E(_DX[0]))));if(_DY!=_DZ){var _E2=function(_E3,_){if(_DY>_E3){return E(_iy);}else{if(_E3>_DZ){return E(_iy);}else{var _E4=_E3-_DY|0;if(0>_E4){return new F(function(){return _iL(_DW,_E4);});}else{if(_E4>=_DW){return new F(function(){return _iL(_DW,_E4);});}else{var _E5=__app2(_E0,_E3,B(_iv(E(_DX[_E4]))));if(_E3!=_DZ){var _E6=B(_E2(_E3+1|0,_));return new T2(1,_ik,_E6);}else{return _iQ;}}}}}},_E7=B(_E2(_DY+1|0,_)),_E8=__app0(E(_iz)),_E9=B(_zD(_DV,_));return new T(function(){return E(E(_E9).b);});}else{var _Ea=__app0(E(_iz)),_Eb=B(_zD(_DV,_));return new T(function(){return E(E(_Eb).b);});}}}}else{var _Ec=__app0(E(_iz)),_Ed=B(_zD(_DV,_));return new T(function(){return E(E(_Ed).b);});}},_Ee=new T(function(){return B(unCStr("Negative exponent"));}),_Ef=new T(function(){return B(err(_Ee));}),_Eg=function(_Eh,_Ei,_Ej){while(1){if(!(_Ei%2)){var _Ek=_Eh*_Eh,_El=quot(_Ei,2);_Eh=_Ek;_Ei=_El;continue;}else{var _Em=E(_Ei);if(_Em==1){return _Eh*_Ej;}else{var _Ek=_Eh*_Eh,_En=_Eh*_Ej;_Eh=_Ek;_Ei=quot(_Em-1|0,2);_Ej=_En;continue;}}}},_Eo=function(_Ep,_Eq){while(1){if(!(_Eq%2)){var _Er=_Ep*_Ep,_Es=quot(_Eq,2);_Ep=_Er;_Eq=_Es;continue;}else{var _Et=E(_Eq);if(_Et==1){return E(_Ep);}else{return new F(function(){return _Eg(_Ep*_Ep,quot(_Et-1|0,2),_Ep);});}}}},_Eu=-4,_Ev=new T3(0,E(_re),E(_Eu),E(_re)),_Ew=function(_Ex){return E(_Ev);},_Ey=function(_){return new F(function(){return __jsNull();});},_Ez=function(_EA){var _EB=B(A1(_EA,_));return E(_EB);},_EC=new T(function(){return B(_Ez(_Ey));}),_ED=function(_EE,_EF,_EG,_EH,_EI,_EJ,_EK,_EL,_EM,_EN,_EO,_EP,_EQ){var _ER=function(_ES){var _ET=E(_rX),_EU=2+_ES|0,_EV=_EU-1|0,_EW=(2+_ES)*(1+_ES),_EX=E(_sp);if(!_EX._){return _ET*0;}else{var _EY=_EX.a,_EZ=_EX.b,_F0=B(A1(_EE,new T(function(){return 6.283185307179586*E(_EY)/E(_rp);}))),_F1=B(A1(_EE,new T(function(){return 6.283185307179586*(E(_EY)+1)/E(_rp);})));if(_F0!=_F1){if(_EU>=0){var _F2=E(_EU);if(!_F2){var _F3=function(_F4,_F5){while(1){var _F6=B((function(_F7,_F8){var _F9=E(_F7);if(!_F9._){return E(_F8);}else{var _Fa=_F9.a,_Fb=_F9.b,_Fc=B(A1(_EE,new T(function(){return 6.283185307179586*E(_Fa)/E(_rp);}))),_Fd=B(A1(_EE,new T(function(){return 6.283185307179586*(E(_Fa)+1)/E(_rp);})));if(_Fc!=_Fd){var _Fe=_F8+0/(_Fc-_Fd)/_EW;_F4=_Fb;_F5=_Fe;return __continue;}else{if(_EV>=0){var _Ff=E(_EV);if(!_Ff){var _Fe=_F8+_EU/_EW;_F4=_Fb;_F5=_Fe;return __continue;}else{var _Fe=_F8+_EU*B(_Eo(_Fc,_Ff))/_EW;_F4=_Fb;_F5=_Fe;return __continue;}}else{return E(_Ef);}}}})(_F4,_F5));if(_F6!=__continue){return _F6;}}};return _ET*B(_F3(_EZ,0/(_F0-_F1)/_EW));}else{var _Fg=function(_Fh,_Fi){while(1){var _Fj=B((function(_Fk,_Fl){var _Fm=E(_Fk);if(!_Fm._){return E(_Fl);}else{var _Fn=_Fm.a,_Fo=_Fm.b,_Fp=B(A1(_EE,new T(function(){return 6.283185307179586*E(_Fn)/E(_rp);}))),_Fq=B(A1(_EE,new T(function(){return 6.283185307179586*(E(_Fn)+1)/E(_rp);})));if(_Fp!=_Fq){if(_F2>=0){var _Fr=_Fl+(B(_Eo(_Fp,_F2))-B(_Eo(_Fq,_F2)))/(_Fp-_Fq)/_EW;_Fh=_Fo;_Fi=_Fr;return __continue;}else{return E(_Ef);}}else{if(_EV>=0){var _Fs=E(_EV);if(!_Fs){var _Fr=_Fl+_EU/_EW;_Fh=_Fo;_Fi=_Fr;return __continue;}else{var _Fr=_Fl+_EU*B(_Eo(_Fp,_Fs))/_EW;_Fh=_Fo;_Fi=_Fr;return __continue;}}else{return E(_Ef);}}}})(_Fh,_Fi));if(_Fj!=__continue){return _Fj;}}};return _ET*B(_Fg(_EZ,(B(_Eo(_F0,_F2))-B(_Eo(_F1,_F2)))/(_F0-_F1)/_EW));}}else{return E(_Ef);}}else{if(_EV>=0){var _Ft=E(_EV);if(!_Ft){var _Fu=function(_Fv,_Fw){while(1){var _Fx=B((function(_Fy,_Fz){var _FA=E(_Fy);if(!_FA._){return E(_Fz);}else{var _FB=_FA.a,_FC=_FA.b,_FD=B(A1(_EE,new T(function(){return 6.283185307179586*E(_FB)/E(_rp);}))),_FE=B(A1(_EE,new T(function(){return 6.283185307179586*(E(_FB)+1)/E(_rp);})));if(_FD!=_FE){if(_EU>=0){var _FF=E(_EU);if(!_FF){var _FG=_Fz+0/(_FD-_FE)/_EW;_Fv=_FC;_Fw=_FG;return __continue;}else{var _FG=_Fz+(B(_Eo(_FD,_FF))-B(_Eo(_FE,_FF)))/(_FD-_FE)/_EW;_Fv=_FC;_Fw=_FG;return __continue;}}else{return E(_Ef);}}else{var _FG=_Fz+_EU/_EW;_Fv=_FC;_Fw=_FG;return __continue;}}})(_Fv,_Fw));if(_Fx!=__continue){return _Fx;}}};return _ET*B(_Fu(_EZ,_EU/_EW));}else{var _FH=function(_FI,_FJ){while(1){var _FK=B((function(_FL,_FM){var _FN=E(_FL);if(!_FN._){return E(_FM);}else{var _FO=_FN.a,_FP=_FN.b,_FQ=B(A1(_EE,new T(function(){return 6.283185307179586*E(_FO)/E(_rp);}))),_FR=B(A1(_EE,new T(function(){return 6.283185307179586*(E(_FO)+1)/E(_rp);})));if(_FQ!=_FR){if(_EU>=0){var _FS=E(_EU);if(!_FS){var _FT=_FM+0/(_FQ-_FR)/_EW;_FI=_FP;_FJ=_FT;return __continue;}else{var _FT=_FM+(B(_Eo(_FQ,_FS))-B(_Eo(_FR,_FS)))/(_FQ-_FR)/_EW;_FI=_FP;_FJ=_FT;return __continue;}}else{return E(_Ef);}}else{if(_Ft>=0){var _FT=_FM+_EU*B(_Eo(_FQ,_Ft))/_EW;_FI=_FP;_FJ=_FT;return __continue;}else{return E(_Ef);}}}})(_FI,_FJ));if(_FK!=__continue){return _FK;}}};return _ET*B(_FH(_EZ,_EU*B(_Eo(_F0,_Ft))/_EW));}}else{return E(_Ef);}}}},_FU=E(_EC),_FV=1/(B(_ER(1))*_EF);return new F(function(){return _u6(_EE,_Ew,new T2(0,E(new T3(0,E(_FV),E(_FV),E(_FV))),1/(B(_ER(3))*_EF)),_EG,_EH,_EI,_EJ,_EK,_EL,_EM,_EN,_EO,_EP,_EQ,_rf,_FU,_FU,0);});},_FW=0.5,_FX=1,_FY=0,_FZ=0.3,_G0=function(_G1){return E(_FZ);},_G2=new T(function(){var _G3=B(_ED(_G0,1.2,_FY,_FX,_FW,_FY,_FY,_FY,_FY,_FY,_FX,_FX,_FX));return {_:0,a:E(_G3.a),b:E(_G3.b),c:E(_G3.c),d:E(_G3.d),e:E(_G3.e),f:E(_G3.f),g:E(_G3.g),h:_G3.h,i:_G3.i,j:_G3.j};}),_G4=0,_G5=function(_){var _G6=newArr(1,_nC),_=_G6[0]=_G2;return new T4(0,E(_G4),E(_G4),1,_G6);},_G7=new T(function(){return B(_nH(_G5));}),_G8=function(_G9,_){while(1){var _Ga=E(_G9);if(!_Ga._){return _ik;}else{var _Gb=_Ga.b,_Gc=E(_Ga.a);switch(_Gc._){case 0:var _Gd=B(A1(_Gc.a,_));_G9=B(_n(_Gb,new T2(1,_Gd,_w)));continue;case 1:_G9=B(_n(_Gb,_Gc.a));continue;default:_G9=_Gb;continue;}}}},_Ge=function(_Gf,_Gg,_){var _Gh=E(_Gf);switch(_Gh._){case 0:var _Gi=B(A1(_Gh.a,_));return new F(function(){return _G8(B(_n(_Gg,new T2(1,_Gi,_w))),_);});break;case 1:return new F(function(){return _G8(B(_n(_Gg,_Gh.a)),_);});break;default:return new F(function(){return _G8(_Gg,_);});}},_Gj=new T0(2),_Gk=function(_Gl){return new T0(2);},_Gm=function(_Gn,_Go,_Gp){return function(_){var _Gq=E(_Gn),_Gr=rMV(_Gq),_Gs=E(_Gr);if(!_Gs._){var _Gt=new T(function(){var _Gu=new T(function(){return B(A1(_Gp,_ik));});return B(_n(_Gs.b,new T2(1,new T2(0,_Go,function(_Gv){return E(_Gu);}),_w)));}),_=wMV(_Gq,new T2(0,_Gs.a,_Gt));return _Gj;}else{var _Gw=E(_Gs.a);if(!_Gw._){var _=wMV(_Gq,new T2(0,_Go,_w));return new T(function(){return B(A1(_Gp,_ik));});}else{var _=wMV(_Gq,new T1(1,_Gw.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Gp,_ik));}),new T2(1,new T(function(){return B(A2(_Gw.a,_Go,_Gk));}),_w)));}}};},_Gx=new T(function(){return E(_EC);}),_Gy=new T(function(){return eval("window.requestAnimationFrame");}),_Gz=new T1(1,_w),_GA=function(_GB,_GC){return function(_){var _GD=E(_GB),_GE=rMV(_GD),_GF=E(_GE);if(!_GF._){var _GG=_GF.a,_GH=E(_GF.b);if(!_GH._){var _=wMV(_GD,_Gz);return new T(function(){return B(A1(_GC,_GG));});}else{var _GI=E(_GH.a),_=wMV(_GD,new T2(0,_GI.a,_GH.b));return new T1(1,new T2(1,new T(function(){return B(A1(_GC,_GG));}),new T2(1,new T(function(){return B(A1(_GI.b,_Gk));}),_w)));}}else{var _GJ=new T(function(){var _GK=function(_GL){var _GM=new T(function(){return B(A1(_GC,_GL));});return function(_GN){return E(_GM);};};return B(_n(_GF.a,new T2(1,_GK,_w)));}),_=wMV(_GD,new T1(1,_GJ));return _Gj;}};},_GO=function(_GP,_GQ){return new T1(0,B(_GA(_GP,_GQ)));},_GR=function(_GS,_GT){var _GU=new T(function(){return new T1(0,B(_Gm(_GS,_ik,_Gk)));});return function(_){var _GV=__createJSFunc(2,function(_GW,_){var _GX=B(_Ge(_GU,_w,_));return _Gx;}),_GY=__app1(E(_Gy),_GV);return new T(function(){return B(_GO(_GS,_GT));});};},_GZ=new T1(1,_w),_H0=function(_H1,_H2,_){var _H3=function(_){var _H4=nMV(_H1),_H5=_H4;return new T(function(){var _H6=new T(function(){return B(_H7(_));}),_H8=function(_){var _H9=rMV(_H5),_Ha=B(A2(_H2,_H9,_)),_=wMV(_H5,_Ha),_Hb=function(_){var _Hc=nMV(_GZ);return new T(function(){return new T1(0,B(_GR(_Hc,function(_Hd){return E(_H6);})));});};return new T1(0,_Hb);},_He=new T(function(){return new T1(0,_H8);}),_H7=function(_Hf){return E(_He);};return B(_H7(_));});};return new F(function(){return _Ge(new T1(0,_H3),_w,_);});},_Hg=new T(function(){return eval("__strict(setBounds)");}),_Hh=function(_){var _Hi=__app3(E(_20),E(_93),E(_id),E(_1Z)),_Hj=__app2(E(_Hg),E(_1u),E(_1n));return new F(function(){return _H0(_G7,_DR,_);});},_Hk=function(_){return new F(function(){return _Hh(_);});};
var hasteMain = function() {B(A(_Hk, [0]));};window.onload = hasteMain;