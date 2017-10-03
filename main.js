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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=function(_hP){var _hQ=new T(function(){return E(E(_hP).a);}),_hR=new T(function(){return B(_8J(new T(function(){return B(_8H(_hQ));})));}),_hS=new T(function(){return B(A2(_8s,_hR,_8r));}),_hT=function(_hU){var _hV=new T(function(){var _hW=new T(function(){var _hX=new T(function(){var _hY=new T(function(){return E(E(_hU).c);});return B(A3(_8L,_hR,_hY,_hY));}),_hZ=new T(function(){var _i0=new T(function(){return E(E(_hU).a);});return B(A3(_8L,_hR,_i0,_i0));});return B(A3(_6X,_hR,_hZ,_hX));});return B(A2(_9t,_hQ,_hW));});return new F(function(){return A3(_9p,_hR,_hV,_hS);});};return E(_hT);},_i1=function(_ef,_ee){return new T2(0,_ef,_ee);},_i2=function(_i3,_i4,_i5){var _i6=new T(function(){var _i7=E(_i3),_i8=_i7.a,_i9=new T(function(){return B(A1(_i7.b,new T(function(){return B(_8J(B(_8H(E(_i7.c).a))));})));});return B(A3(_8R,_i8,new T(function(){return B(A3(_8T,B(_8F(_i8)),_i1,_i5));}),_i9));});return E(B(A1(_i4,_i6)).b);},_ia=function(_ib){var _ic=new T(function(){return E(E(_ib).a);}),_id=new T(function(){return E(E(_ib).b);}),_ie=new T(function(){var _if=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),_ig=new T(function(){var _ih=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_eb(_ih,new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_hO(new T2(0,_ig,_if)));});return function(_ii){return new F(function(){return _i2(new T3(0,_8p,_8u,new T2(0,_ic,_id)),_ie,_ii);});};},_ij=new T(function(){return B(_ia(_7V));}),_ik=new T(function(){return B(A1(_ij,_E));}),_il=new T(function(){return E(E(_ik).a);}),_im=new T(function(){return B(unCStr(",y:"));}),_in=new T1(0,_im),_io=new T(function(){return E(E(_ik).b);}),_ip=new T(function(){return B(unCStr(",z:"));}),_iq=new T1(0,_ip),_ir=new T(function(){return E(E(_ik).c);}),_is=new T(function(){return B(unCStr("})"));}),_it=new T1(0,_is),_iu=new T2(1,_it,_w),_iv=new T2(1,_ir,_iu),_iw=new T2(1,_iq,_iv),_ix=new T2(1,_io,_iw),_iy=new T2(1,_in,_ix),_iz=new T2(1,_il,_iy),_iA=new T(function(){return B(unCStr("({x:"));}),_iB=new T1(0,_iA),_iC=new T2(1,_iB,_iz),_iD=function(_iE){return E(_iE);},_iF=new T(function(){return toJSStr(B(_e(_x,_iD,_iC)));}),_iG=new T(function(){return B(_hO(_7V));}),_iH=new T(function(){return B(A1(_iG,_E));}),_iI=new T(function(){return toJSStr(B(_4(_x,_iD,_iH)));}),_iJ=function(_iK,_iL,_iM){var _iN=E(_iM);if(!_iN._){return new F(function(){return A1(_iL,_iN.a);});}else{var _iO=new T(function(){return B(_0(_iK));}),_iP=new T(function(){return B(_2(_iK));}),_iQ=function(_iR){var _iS=E(_iR);if(!_iS._){return E(_iP);}else{return new F(function(){return A2(_iO,new T(function(){return B(_iJ(_iK,_iL,_iS.a));}),new T(function(){return B(_iQ(_iS.b));}));});}};return new F(function(){return _iQ(_iN.a);});}},_iT=new T(function(){return B(unCStr("x"));}),_iU=new T1(0,_iT),_iV=new T(function(){return B(unCStr("y"));}),_iW=new T1(0,_iV),_iX=new T(function(){return B(unCStr("z"));}),_iY=new T1(0,_iX),_iZ=new T3(0,E(_iU),E(_iW),E(_iY)),_j0=new T(function(){return B(unCStr(","));}),_j1=new T1(0,_j0),_j2=new T(function(){return B(unCStr("pow("));}),_j3=new T1(0,_j2),_j4=new T(function(){return B(unCStr(")"));}),_j5=new T1(0,_j4),_j6=new T2(1,_j5,_w),_j7=function(_j8,_j9){return new T1(1,new T2(1,_j3,new T2(1,_j8,new T2(1,_j1,new T2(1,_j9,_j6)))));},_ja=new T(function(){return B(unCStr("acos("));}),_jb=new T1(0,_ja),_jc=function(_jd){return new T1(1,new T2(1,_jb,new T2(1,_jd,_j6)));},_je=new T(function(){return B(unCStr("acosh("));}),_jf=new T1(0,_je),_jg=function(_jh){return new T1(1,new T2(1,_jf,new T2(1,_jh,_j6)));},_ji=new T(function(){return B(unCStr("asin("));}),_jj=new T1(0,_ji),_jk=function(_jl){return new T1(1,new T2(1,_jj,new T2(1,_jl,_j6)));},_jm=new T(function(){return B(unCStr("asinh("));}),_jn=new T1(0,_jm),_jo=function(_jp){return new T1(1,new T2(1,_jn,new T2(1,_jp,_j6)));},_jq=new T(function(){return B(unCStr("atan("));}),_jr=new T1(0,_jq),_js=function(_jt){return new T1(1,new T2(1,_jr,new T2(1,_jt,_j6)));},_ju=new T(function(){return B(unCStr("atanh("));}),_jv=new T1(0,_ju),_jw=function(_jx){return new T1(1,new T2(1,_jv,new T2(1,_jx,_j6)));},_jy=new T(function(){return B(unCStr("cos("));}),_jz=new T1(0,_jy),_jA=function(_jB){return new T1(1,new T2(1,_jz,new T2(1,_jB,_j6)));},_jC=new T(function(){return B(unCStr("cosh("));}),_jD=new T1(0,_jC),_jE=function(_jF){return new T1(1,new T2(1,_jD,new T2(1,_jF,_j6)));},_jG=new T(function(){return B(unCStr("exp("));}),_jH=new T1(0,_jG),_jI=function(_jJ){return new T1(1,new T2(1,_jH,new T2(1,_jJ,_j6)));},_jK=new T(function(){return B(unCStr("log("));}),_jL=new T1(0,_jK),_jM=function(_jN){return new T1(1,new T2(1,_jL,new T2(1,_jN,_j6)));},_jO=new T(function(){return B(unCStr(")/log("));}),_jP=new T1(0,_jO),_jQ=function(_jR,_jS){return new T1(1,new T2(1,_jL,new T2(1,_jS,new T2(1,_jP,new T2(1,_jR,_j6)))));},_jT=new T(function(){return B(unCStr("pi"));}),_jU=new T1(0,_jT),_jV=new T(function(){return B(unCStr("sin("));}),_jW=new T1(0,_jV),_jX=function(_jY){return new T1(1,new T2(1,_jW,new T2(1,_jY,_j6)));},_jZ=new T(function(){return B(unCStr("sinh("));}),_k0=new T1(0,_jZ),_k1=function(_k2){return new T1(1,new T2(1,_k0,new T2(1,_k2,_j6)));},_k3=new T(function(){return B(unCStr("sqrt("));}),_k4=new T1(0,_k3),_k5=function(_k6){return new T1(1,new T2(1,_k4,new T2(1,_k6,_j6)));},_k7=new T(function(){return B(unCStr("tan("));}),_k8=new T1(0,_k7),_k9=function(_ka){return new T1(1,new T2(1,_k8,new T2(1,_ka,_j6)));},_kb=new T(function(){return B(unCStr("tanh("));}),_kc=new T1(0,_kb),_kd=function(_ke){return new T1(1,new T2(1,_kc,new T2(1,_ke,_j6)));},_kf=new T(function(){return B(unCStr("("));}),_kg=new T1(0,_kf),_kh=new T(function(){return B(unCStr(")/("));}),_ki=new T1(0,_kh),_kj=function(_kk,_kl){return new T1(1,new T2(1,_kg,new T2(1,_kk,new T2(1,_ki,new T2(1,_kl,_j6)))));},_km=function(_kn){return new T1(0,new T(function(){var _ko=E(_kn),_kp=jsShow(B(_6y(_ko.a,_ko.b)));return fromJSStr(_kp);}));},_kq=new T(function(){return B(unCStr("1./("));}),_kr=new T1(0,_kq),_ks=function(_kt){return new T1(1,new T2(1,_kr,new T2(1,_kt,_j6)));},_ku=new T(function(){return B(unCStr(")+("));}),_kv=new T1(0,_ku),_kw=function(_kx,_ky){return new T1(1,new T2(1,_kg,new T2(1,_kx,new T2(1,_kv,new T2(1,_ky,_j6)))));},_kz=new T(function(){return B(unCStr("-("));}),_kA=new T1(0,_kz),_kB=function(_kC){return new T1(1,new T2(1,_kA,new T2(1,_kC,_j6)));},_kD=new T(function(){return B(unCStr(")*("));}),_kE=new T1(0,_kD),_kF=function(_kG,_kH){return new T1(1,new T2(1,_kg,new T2(1,_kG,new T2(1,_kE,new T2(1,_kH,_j6)))));},_kI=function(_kJ,_kK){return new F(function(){return A3(_6X,_kL,_kJ,new T(function(){return B(A2(_6Z,_kL,_kK));}));});},_kM=new T(function(){return B(unCStr("abs("));}),_kN=new T1(0,_kM),_kO=function(_kP){return new T1(1,new T2(1,_kN,new T2(1,_kP,_j6)));},_kQ=new T(function(){return B(unCStr("."));}),_kR=function(_kS){return new T1(0,new T(function(){return B(_n(B(_7i(0,_kS,_w)),_kQ));}));},_kT=new T(function(){return B(unCStr("sign("));}),_kU=new T1(0,_kT),_kV=function(_kW){return new T1(1,new T2(1,_kU,new T2(1,_kW,_j6)));},_kL=new T(function(){return {_:0,a:_kw,b:_kI,c:_kF,d:_kB,e:_kO,f:_kV,g:_kR};}),_kX=new T4(0,_kL,_kj,_ks,_km),_kY={_:0,a:_kX,b:_jU,c:_jI,d:_jM,e:_k5,f:_j7,g:_jQ,h:_jX,i:_jA,j:_k9,k:_jk,l:_jc,m:_js,n:_k1,o:_jE,p:_kd,q:_jo,r:_jg,s:_jw},_kZ=new T(function(){return B(unCStr("(/=) is not defined"));}),_l0=new T(function(){return B(err(_kZ));}),_l1=new T(function(){return B(unCStr("(==) is not defined"));}),_l2=new T(function(){return B(err(_l1));}),_l3=new T2(0,_l2,_l0),_l4=new T(function(){return B(unCStr("(<) is not defined"));}),_l5=new T(function(){return B(err(_l4));}),_l6=new T(function(){return B(unCStr("(<=) is not defined"));}),_l7=new T(function(){return B(err(_l6));}),_l8=new T(function(){return B(unCStr("(>) is not defined"));}),_l9=new T(function(){return B(err(_l8));}),_la=new T(function(){return B(unCStr("(>=) is not defined"));}),_lb=new T(function(){return B(err(_la));}),_lc=new T(function(){return B(unCStr("compare is not defined"));}),_ld=new T(function(){return B(err(_lc));}),_le=new T(function(){return B(unCStr("max("));}),_lf=new T1(0,_le),_lg=function(_lh,_li){return new T1(1,new T2(1,_lf,new T2(1,_lh,new T2(1,_j1,new T2(1,_li,_j6)))));},_lj=new T(function(){return B(unCStr("min("));}),_lk=new T1(0,_lj),_ll=function(_lm,_ln){return new T1(1,new T2(1,_lk,new T2(1,_lm,new T2(1,_j1,new T2(1,_ln,_j6)))));},_lo={_:0,a:_l3,b:_ld,c:_l5,d:_l7,e:_l9,f:_lb,g:_lg,h:_ll},_lp=new T2(0,_kY,_lo),_lq=new T(function(){return B(_hO(_lp));}),_lr=new T(function(){return B(A1(_lq,_iZ));}),_ls=new T(function(){return toJSStr(B(_iJ(_x,_iD,_lr)));}),_lt=new T(function(){return eval("__strict(compile)");}),_lu=function(_lv,_lw,_lx,_ly){var _lz=B(_8J(B(_8H(_lv)))),_lA=new T(function(){var _lB=new T(function(){return B(A3(_6X,_lz,new T(function(){return B(A3(_8L,_lz,_lw,_lw));}),new T(function(){return B(A3(_8L,_lz,_ly,_ly));})));});return B(A2(_9t,_lv,_lB));});return new F(function(){return A3(_9p,_lz,_lA,new T(function(){return B(A2(_bU,_lv,_lx));}));});},_lC=new T(function(){return B(_lu(_kY,_iU,_iW,_iY));}),_lD=new T(function(){return toJSStr(B(_iJ(_x,_iD,_lC)));}),_lE=function(_lF,_lG,_lH){var _lI=new T(function(){return B(_0(_lF));}),_lJ=new T(function(){return B(_2(_lF));}),_lK=function(_lL){var _lM=E(_lL);if(!_lM._){return E(_lJ);}else{return new F(function(){return A2(_lI,new T(function(){return B(_iJ(_lF,_lG,_lM.a));}),new T(function(){return B(_lK(_lM.b));}));});}};return new F(function(){return _lK(_lH);});},_lN=function(_lO){var _lP=new T(function(){return E(E(_lO).a);}),_lQ=new T3(0,_8p,_8u,new T2(0,_lP,new T(function(){return E(E(_lO).b);}))),_lR=new T(function(){return B(_eb(new T(function(){return B(_f7(new T(function(){return B(_fQ(_lQ));}),_lQ));}),_lQ));}),_lS=new T(function(){return B(_8J(new T(function(){return B(_8H(_lP));})));});return function(_lT){var _lU=E(_lT),_lV=B(A2(_8s,_lS,_8r)),_lW=B(A2(_8s,_lS,_8q));return E(B(_lu(_lR,new T2(0,_lU.a,new T3(0,E(_lV),E(_lW),E(_lW))),new T2(0,_lU.b,new T3(0,E(_lW),E(_lV),E(_lW))),new T2(0,_lU.c,new T3(0,E(_lW),E(_lW),E(_lV))))).b);};},_lX=new T(function(){return B(_lN(_lp));}),_lY=function(_lZ,_m0){var _m1=E(_m0);return (_m1._==0)?__Z:new T2(1,_lZ,new T2(1,_m1.a,new T(function(){return B(_lY(_lZ,_m1.b));})));},_m2=new T(function(){var _m3=B(A1(_lX,_iZ));return new T2(1,_m3.a,new T(function(){return B(_lY(_j1,new T2(1,_m3.b,new T2(1,_m3.c,_w))));}));}),_m4=new T1(1,_m2),_m5=new T2(1,_m4,_j6),_m6=new T(function(){return B(unCStr("vec3("));}),_m7=new T1(0,_m6),_m8=new T2(1,_m7,_m5),_m9=new T(function(){return toJSStr(B(_lE(_x,_iD,_m8)));}),_ma="enclose",_mb="outline",_mc="polygon",_md="z",_me="y",_mf="x",_mg=0,_mh=function(_mi){var _mj=__new(),_mk=_mj,_ml=function(_mm,_){while(1){var _mn=E(_mm);if(!_mn._){return _mg;}else{var _mo=E(_mn.a),_mp=__set(_mk,E(_mo.a),E(_mo.b));_mm=_mn.b;continue;}}},_mq=B(_ml(_mi,_));return E(_mk);},_mr=function(_ms){return new F(function(){return _mh(new T2(1,new T2(0,_mf,new T(function(){return E(E(E(E(_ms).d).a).a);})),new T2(1,new T2(0,_me,new T(function(){return E(E(E(E(_ms).d).a).b);})),new T2(1,new T2(0,_md,new T(function(){return E(E(E(E(_ms).d).a).c);})),new T2(1,new T2(0,_mc,new T(function(){return E(_ms).h;})),new T2(1,new T2(0,_mb,new T(function(){return E(_ms).i;})),new T2(1,new T2(0,_ma,new T(function(){return E(_ms).j;})),_w)))))));});},_mt=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_mu=new T(function(){return B(err(_mt));}),_mv=new T(function(){return eval("__strict(drawObjects)");}),_mw=new T(function(){return eval("__strict(draw)");}),_mx=function(_my,_mz){var _mA=jsShowI(_my);return new F(function(){return _n(fromJSStr(_mA),_mz);});},_mB=function(_mC,_mD,_mE){if(_mD>=0){return new F(function(){return _mx(_mD,_mE);});}else{if(_mC<=6){return new F(function(){return _mx(_mD,_mE);});}else{return new T2(1,_7g,new T(function(){var _mF=jsShowI(_mD);return B(_n(fromJSStr(_mF),new T2(1,_7f,_mE)));}));}}},_mG=new T(function(){return B(unCStr(")"));}),_mH=function(_mI,_mJ){var _mK=new T(function(){var _mL=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mB(0,_mI,_w)),_mG));})));},1);return B(_n(B(_mB(0,_mJ,_w)),_mL));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_mK)));});},_mM=new T2(1,_mg,_w),_mN=function(_mO){return E(_mO);},_mP=function(_mQ){return E(_mQ);},_mR=function(_mS,_mT){return E(_mT);},_mU=function(_mV,_mW){return E(_mV);},_mX=function(_mY){return E(_mY);},_mZ=new T2(0,_mX,_mU),_n0=function(_n1,_n2){return E(_n1);},_n3=new T5(0,_mZ,_mP,_mN,_mR,_n0),_n4=function(_n5){var _n6=E(_n5);return new F(function(){return Math.log(_n6+(_n6+1)*Math.sqrt((_n6-1)/(_n6+1)));});},_n7=function(_n8){var _n9=E(_n8);return new F(function(){return Math.log(_n9+Math.sqrt(1+_n9*_n9));});},_na=function(_nb){var _nc=E(_nb);return 0.5*Math.log((1+_nc)/(1-_nc));},_nd=function(_ne,_nf){return Math.log(E(_nf))/Math.log(E(_ne));},_ng=3.141592653589793,_nh=function(_ni){var _nj=E(_ni);return new F(function(){return _6y(_nj.a,_nj.b);});},_nk=function(_nl){return 1/E(_nl);},_nm=function(_nn){var _no=E(_nn),_np=E(_no);return (_np==0)?E(_6x):(_np<=0)? -_np:E(_no);},_nq=function(_nr){var _ns=E(_nr);if(!_ns._){return _ns.a;}else{return new F(function(){return I_toNumber(_ns.a);});}},_nt=function(_nu){return new F(function(){return _nq(_nu);});},_nv=1,_nw=-1,_nx=function(_ny){var _nz=E(_ny);return (_nz<=0)?(_nz>=0)?E(_nz):E(_nw):E(_nv);},_nA=function(_nB,_nC){return E(_nB)-E(_nC);},_nD=function(_nE){return  -E(_nE);},_nF=function(_nG,_nH){return E(_nG)+E(_nH);},_nI=function(_nJ,_nK){return E(_nJ)*E(_nK);},_nL={_:0,a:_nF,b:_nA,c:_nI,d:_nD,e:_nm,f:_nx,g:_nt},_nM=function(_nN,_nO){return E(_nN)/E(_nO);},_nP=new T4(0,_nL,_nM,_nk,_nh),_nQ=function(_nR){return new F(function(){return Math.acos(E(_nR));});},_nS=function(_nT){return new F(function(){return Math.asin(E(_nT));});},_nU=function(_nV){return new F(function(){return Math.atan(E(_nV));});},_nW=function(_nX){return new F(function(){return Math.cos(E(_nX));});},_nY=function(_nZ){return new F(function(){return cosh(E(_nZ));});},_o0=function(_o1){return new F(function(){return Math.exp(E(_o1));});},_o2=function(_o3){return new F(function(){return Math.log(E(_o3));});},_o4=function(_o5,_o6){return new F(function(){return Math.pow(E(_o5),E(_o6));});},_o7=function(_o8){return new F(function(){return Math.sin(E(_o8));});},_o9=function(_oa){return new F(function(){return sinh(E(_oa));});},_ob=function(_oc){return new F(function(){return Math.sqrt(E(_oc));});},_od=function(_oe){return new F(function(){return Math.tan(E(_oe));});},_of=function(_og){return new F(function(){return tanh(E(_og));});},_oh={_:0,a:_nP,b:_ng,c:_o0,d:_o2,e:_ob,f:_o4,g:_nd,h:_o7,i:_nW,j:_od,k:_nS,l:_nQ,m:_nU,n:_o9,o:_nY,p:_of,q:_n7,r:_n4,s:_na},_oi="flipped2",_oj="flipped1",_ok="c1y",_ol="c1x",_om="w2z",_on="w2y",_oo="w2x",_op="w1z",_oq="w1y",_or="w1x",_os="d2z",_ot="d2y",_ou="d2x",_ov="d1z",_ow="d1y",_ox="d1x",_oy="c2y",_oz="c2x",_oA=function(_oB,_){var _oC=__get(_oB,E(_or)),_oD=__get(_oB,E(_oq)),_oE=__get(_oB,E(_op)),_oF=__get(_oB,E(_oo)),_oG=__get(_oB,E(_on)),_oH=__get(_oB,E(_om)),_oI=__get(_oB,E(_ol)),_oJ=__get(_oB,E(_ok)),_oK=__get(_oB,E(_oz)),_oL=__get(_oB,E(_oy)),_oM=__get(_oB,E(_ox)),_oN=__get(_oB,E(_ow)),_oO=__get(_oB,E(_ov)),_oP=__get(_oB,E(_ou)),_oQ=__get(_oB,E(_ot)),_oR=__get(_oB,E(_os)),_oS=__get(_oB,E(_oj)),_oT=__get(_oB,E(_oi));return {_:0,a:E(new T3(0,E(_oC),E(_oD),E(_oE))),b:E(new T3(0,E(_oF),E(_oG),E(_oH))),c:E(new T2(0,E(_oI),E(_oJ))),d:E(new T2(0,E(_oK),E(_oL))),e:E(new T3(0,E(_oM),E(_oN),E(_oO))),f:E(new T3(0,E(_oP),E(_oQ),E(_oR))),g:E(_oS),h:E(_oT)};},_oU=function(_oV,_){var _oW=E(_oV);if(!_oW._){return _w;}else{var _oX=B(_oA(E(_oW.a),_)),_oY=B(_oU(_oW.b,_));return new T2(1,_oX,_oY);}},_oZ=function(_p0){var _p1=E(_p0);return (E(_p1.b)-E(_p1.a)|0)+1|0;},_p2=function(_p3,_p4){var _p5=E(_p3),_p6=E(_p4);return (E(_p5.a)>_p6)?false:_p6<=E(_p5.b);},_p7=function(_p8){return new F(function(){return _mB(0,E(_p8),_w);});},_p9=function(_pa,_pb,_pc){return new F(function(){return _mB(E(_pa),E(_pb),_pc);});},_pd=function(_pe,_pf){return new F(function(){return _mB(0,E(_pe),_pf);});},_pg=function(_ph,_pi){return new F(function(){return _2Q(_pd,_ph,_pi);});},_pj=new T3(0,_p9,_p7,_pg),_pk=0,_pl=function(_pm,_pn,_po){return new F(function(){return A1(_pm,new T2(1,_2N,new T(function(){return B(A1(_pn,_po));})));});},_pp=new T(function(){return B(unCStr(": empty list"));}),_pq=new T(function(){return B(unCStr("Prelude."));}),_pr=function(_ps){return new F(function(){return err(B(_n(_pq,new T(function(){return B(_n(_ps,_pp));},1))));});},_pt=new T(function(){return B(unCStr("foldr1"));}),_pu=new T(function(){return B(_pr(_pt));}),_pv=function(_pw,_px){var _py=E(_px);if(!_py._){return E(_pu);}else{var _pz=_py.a,_pA=E(_py.b);if(!_pA._){return E(_pz);}else{return new F(function(){return A2(_pw,_pz,new T(function(){return B(_pv(_pw,_pA));}));});}}},_pB=new T(function(){return B(unCStr(" out of range "));}),_pC=new T(function(){return B(unCStr("}.index: Index "));}),_pD=new T(function(){return B(unCStr("Ix{"));}),_pE=new T2(1,_7f,_w),_pF=new T2(1,_7f,_pE),_pG=0,_pH=function(_pI){return E(E(_pI).a);},_pJ=function(_pK,_pL,_pM,_pN,_pO){var _pP=new T(function(){var _pQ=new T(function(){var _pR=new T(function(){var _pS=new T(function(){var _pT=new T(function(){return B(A3(_pv,_pl,new T2(1,new T(function(){return B(A3(_pH,_pM,_pG,_pN));}),new T2(1,new T(function(){return B(A3(_pH,_pM,_pG,_pO));}),_w)),_pF));});return B(_n(_pB,new T2(1,_7g,new T2(1,_7g,_pT))));});return B(A(_pH,[_pM,_pk,_pL,new T2(1,_7f,_pS)]));});return B(_n(_pC,new T2(1,_7g,_pR)));},1);return B(_n(_pK,_pQ));},1);return new F(function(){return err(B(_n(_pD,_pP)));});},_pU=function(_pV,_pW,_pX,_pY,_pZ){return new F(function(){return _pJ(_pV,_pW,_pZ,_pX,_pY);});},_q0=function(_q1,_q2,_q3,_q4){var _q5=E(_q3);return new F(function(){return _pU(_q1,_q2,_q5.a,_q5.b,_q4);});},_q6=function(_q7,_q8,_q9,_qa){return new F(function(){return _q0(_qa,_q9,_q8,_q7);});},_qb=new T(function(){return B(unCStr("Int"));}),_qc=function(_qd,_qe){return new F(function(){return _q6(_pj,_qe,_qd,_qb);});},_qf=function(_qg,_qh){var _qi=E(_qg),_qj=E(_qi.a),_qk=E(_qh);if(_qj>_qk){return new F(function(){return _qc(_qk,_qi);});}else{if(_qk>E(_qi.b)){return new F(function(){return _qc(_qk,_qi);});}else{return _qk-_qj|0;}}},_ql=function(_qm,_qn){if(_qm<=_qn){var _qo=function(_qp){return new T2(1,_qp,new T(function(){if(_qp!=_qn){return B(_qo(_qp+1|0));}else{return __Z;}}));};return new F(function(){return _qo(_qm);});}else{return __Z;}},_qq=function(_qr,_qs){return new F(function(){return _ql(E(_qr),E(_qs));});},_qt=function(_qu){var _qv=E(_qu);return new F(function(){return _qq(_qv.a,_qv.b);});},_qw=function(_qx){var _qy=E(_qx),_qz=E(_qy.a),_qA=E(_qy.b);return (_qz>_qA)?E(_pk):(_qA-_qz|0)+1|0;},_qB=function(_qC,_qD){return E(_qC)-E(_qD)|0;},_qE=function(_qF,_qG){return new F(function(){return _qB(_qG,E(_qF).a);});},_qH=function(_qI,_qJ){return E(_qI)==E(_qJ);},_qK=function(_qL,_qM){return E(_qL)!=E(_qM);},_qN=new T2(0,_qH,_qK),_qO=function(_qP,_qQ){var _qR=E(_qP),_qS=E(_qQ);return (_qR>_qS)?E(_qR):E(_qS);},_qT=function(_qU,_qV){var _qW=E(_qU),_qX=E(_qV);return (_qW>_qX)?E(_qX):E(_qW);},_qY=function(_qZ,_r0){return (_qZ>=_r0)?(_qZ!=_r0)?2:1:0;},_r1=function(_r2,_r3){return new F(function(){return _qY(E(_r2),E(_r3));});},_r4=function(_r5,_r6){return E(_r5)>=E(_r6);},_r7=function(_r8,_r9){return E(_r8)>E(_r9);},_ra=function(_rb,_rc){return E(_rb)<=E(_rc);},_rd=function(_re,_rf){return E(_re)<E(_rf);},_rg={_:0,a:_qN,b:_r1,c:_rd,d:_ra,e:_r7,f:_r4,g:_qO,h:_qT},_rh={_:0,a:_rg,b:_qt,c:_qf,d:_qE,e:_p2,f:_qw,g:_oZ},_ri=function(_rj,_rk,_){while(1){var _rl=B((function(_rm,_rn,_){var _ro=E(_rm);if(!_ro._){return new T2(0,_mg,_rn);}else{var _rp=B(A2(_ro.a,_rn,_));_rj=_ro.b;_rk=new T(function(){return E(E(_rp).b);});return __continue;}})(_rj,_rk,_));if(_rl!=__continue){return _rl;}}},_rq=function(_rr,_rs){return new T2(1,_rr,_rs);},_rt=function(_ru,_rv){var _rw=E(_rv);return new T2(0,_rw.a,_rw.b);},_rx=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_ry=new T(function(){return B(err(_rx));}),_rz=new T(function(){return B(unCStr("Negative range size"));}),_rA=new T(function(){return B(err(_rz));}),_rB=function(_rC){return E(E(_rC).f);},_rD=function(_rE){var _rF=B(A1(_rE,_));return E(_rF);},_rG=function(_rH,_rI,_rJ){var _rK=E(_rI),_rL=_rK.a,_rM=_rK.b,_rN=function(_){var _rO=B(A2(_rB,_rH,_rK));if(_rO>=0){var _rP=newArr(_rO,_ry),_rQ=_rP,_rR=E(_rO);if(!_rR){return new T(function(){return new T4(0,E(_rL),E(_rM),0,_rQ);});}else{var _rS=function(_rT,_rU,_){while(1){var _rV=E(_rT);if(!_rV._){return E(_);}else{var _=_rQ[_rU]=_rV.a;if(_rU!=(_rR-1|0)){var _rW=_rU+1|0;_rT=_rV.b;_rU=_rW;continue;}else{return E(_);}}}},_=B(_rS(_rJ,0,_));return new T(function(){return new T4(0,E(_rL),E(_rM),_rR,_rQ);});}}else{return E(_rA);}};return new F(function(){return _rD(_rN);});},_rX=function(_rY,_rZ,_s0,_s1){var _s2=new T(function(){var _s3=E(_s1),_s4=_s3.c-1|0,_s5=new T(function(){return B(A2(_cF,_rZ,_w));});if(0<=_s4){var _s6=new T(function(){return B(_8F(_rZ));}),_s7=function(_s8){var _s9=new T(function(){var _sa=new T(function(){return B(A1(_s0,new T(function(){return E(_s3.d[_s8]);})));});return B(A3(_8T,_s6,_rq,_sa));});return new F(function(){return A3(_8R,_rZ,_s9,new T(function(){if(_s8!=_s4){return B(_s7(_s8+1|0));}else{return E(_s5);}}));});};return B(_s7(0));}else{return E(_s5);}}),_sb=new T(function(){return B(_rt(_rY,_s1));});return new F(function(){return A3(_8T,B(_8F(_rZ)),function(_sc){return new F(function(){return _rG(_rY,_sb,_sc);});},_s2);});},_sd=function(_se,_sf,_sg,_sh,_si,_sj,_sk,_sl,_sm){var _sn=B(_8L(_se));return new T2(0,new T3(0,E(B(A1(B(A1(_sn,_sf)),_sj))),E(B(A1(B(A1(_sn,_sg)),_sk))),E(B(A1(B(A1(_sn,_sh)),_sl)))),B(A1(B(A1(_sn,_si)),_sm)));},_so=function(_sp,_sq,_sr,_ss,_st,_su,_sv,_sw,_sx){var _sy=B(_6X(_sp));return new T2(0,new T3(0,E(B(A1(B(A1(_sy,_sq)),_su))),E(B(A1(B(A1(_sy,_sr)),_sv))),E(B(A1(B(A1(_sy,_ss)),_sw)))),B(A1(B(A1(_sy,_st)),_sx)));},_sz=function(_sA,_sB){return (E(_sA)!=E(_sB))?true:false;},_sC=function(_sD,_sE){return E(_sD)==E(_sE);},_sF=new T2(0,_sC,_sz),_sG=function(_sH,_sI){return E(_sH)<E(_sI);},_sJ=function(_sK,_sL){return E(_sK)<=E(_sL);},_sM=function(_sN,_sO){return E(_sN)>E(_sO);},_sP=function(_sQ,_sR){return E(_sQ)>=E(_sR);},_sS=function(_sT,_sU){var _sV=E(_sT),_sW=E(_sU);return (_sV>=_sW)?(_sV!=_sW)?2:1:0;},_sX=function(_sY,_sZ){var _t0=E(_sY),_t1=E(_sZ);return (_t0>_t1)?E(_t0):E(_t1);},_t2=function(_t3,_t4){var _t5=E(_t3),_t6=E(_t4);return (_t5>_t6)?E(_t6):E(_t5);},_t7={_:0,a:_sF,b:_sS,c:_sG,d:_sJ,e:_sM,f:_sP,g:_sX,h:_t2},_t8="dz",_t9="wy",_ta="wx",_tb="dy",_tc="dx",_td="t",_te="a",_tf="r",_tg="ly",_th="lx",_ti="wz",_tj=function(_tk,_tl,_tm,_tn,_to,_tp,_tq,_tr,_ts){return new F(function(){return _mh(new T2(1,new T2(0,_ta,_tk),new T2(1,new T2(0,_t9,_tl),new T2(1,new T2(0,_ti,_tm),new T2(1,new T2(0,_th,_tn*_to*Math.cos(_tp)),new T2(1,new T2(0,_tg,_tn*_to*Math.sin(_tp)),new T2(1,new T2(0,_tf,_tn),new T2(1,new T2(0,_te,_to),new T2(1,new T2(0,_td,_tp),new T2(1,new T2(0,_tc,_tq),new T2(1,new T2(0,_tb,_tr),new T2(1,new T2(0,_t8,_ts),_w))))))))))));});},_tt=function(_tu){var _tv=E(_tu),_tw=E(_tv.a),_tx=E(_tv.b),_ty=E(_tv.d);return new F(function(){return _tj(_tw.a,_tw.b,_tw.c,E(_tx.a),E(_tx.b),E(_tv.c),_ty.a,_ty.b,_ty.c);});},_tz=function(_tA,_tB){var _tC=E(_tB);return (_tC._==0)?__Z:new T2(1,new T(function(){return B(A1(_tA,_tC.a));}),new T(function(){return B(_tz(_tA,_tC.b));}));},_tD=function(_tE,_tF,_tG){var _tH=__lst2arr(B(_tz(_tt,new T2(1,_tE,new T2(1,_tF,new T2(1,_tG,_w))))));return E(_tH);},_tI=function(_tJ){var _tK=E(_tJ);return new F(function(){return _tD(_tK.a,_tK.b,_tK.c);});},_tL=new T2(0,_oh,_t7),_tM=function(_tN,_tO,_tP,_tQ,_tR,_tS,_tT){var _tU=B(_8J(B(_8H(_tN)))),_tV=new T(function(){return B(A3(_6X,_tU,new T(function(){return B(A3(_8L,_tU,_tO,_tR));}),new T(function(){return B(A3(_8L,_tU,_tP,_tS));})));});return new F(function(){return A3(_6X,_tU,_tV,new T(function(){return B(A3(_8L,_tU,_tQ,_tT));}));});},_tW=function(_tX,_tY,_tZ,_u0){var _u1=B(_8H(_tX)),_u2=new T(function(){return B(A2(_9t,_tX,new T(function(){return B(_tM(_tX,_tY,_tZ,_u0,_tY,_tZ,_u0));})));});return new T3(0,B(A3(_8P,_u1,_tY,_u2)),B(A3(_8P,_u1,_tZ,_u2)),B(A3(_8P,_u1,_u0,_u2)));},_u3=function(_u4,_u5,_u6,_u7,_u8,_u9,_ua){var _ub=B(_8L(_u4));return new T3(0,B(A1(B(A1(_ub,_u5)),_u8)),B(A1(B(A1(_ub,_u6)),_u9)),B(A1(B(A1(_ub,_u7)),_ua)));},_uc=function(_ud,_ue,_uf,_ug,_uh,_ui,_uj){var _uk=B(_6X(_ud));return new T3(0,B(A1(B(A1(_uk,_ue)),_uh)),B(A1(B(A1(_uk,_uf)),_ui)),B(A1(B(A1(_uk,_ug)),_uj)));},_ul=function(_um,_un){var _uo=new T(function(){return E(E(_um).a);}),_up=new T(function(){return B(A2(_lN,new T2(0,_uo,new T(function(){return E(E(_um).b);})),_un));}),_uq=new T(function(){var _ur=E(_up),_us=B(_tW(_uo,_ur.a,_ur.b,_ur.c));return new T3(0,E(_us.a),E(_us.b),E(_us.c));}),_ut=new T(function(){var _uu=E(_un),_uv=_uu.a,_uw=_uu.b,_ux=_uu.c,_uy=E(_uq),_uz=B(_8H(_uo)),_uA=new T(function(){return B(A2(_9t,_uo,new T(function(){var _uB=E(_up),_uC=_uB.a,_uD=_uB.b,_uE=_uB.c;return B(_tM(_uo,_uC,_uD,_uE,_uC,_uD,_uE));})));}),_uF=B(A3(_8P,_uz,new T(function(){return B(_lu(_uo,_uv,_uw,_ux));}),_uA)),_uG=B(_8J(_uz)),_uH=B(_u3(_uG,_uy.a,_uy.b,_uy.c,_uF,_uF,_uF)),_uI=B(_6Z(_uG)),_uJ=B(_uc(_uG,_uv,_uw,_ux,B(A1(_uI,_uH.a)),B(A1(_uI,_uH.b)),B(A1(_uI,_uH.c))));return new T3(0,E(_uJ.a),E(_uJ.b),E(_uJ.c));});return new T2(0,_ut,_uq);},_uK=function(_uL){return E(E(_uL).a);},_uM=function(_uN,_uO,_uP,_uQ,_uR,_uS,_uT){var _uU=B(_tM(_uN,_uR,_uS,_uT,_uO,_uP,_uQ)),_uV=B(_8J(B(_8H(_uN)))),_uW=B(_u3(_uV,_uR,_uS,_uT,_uU,_uU,_uU)),_uX=B(_6Z(_uV));return new F(function(){return _uc(_uV,_uO,_uP,_uQ,B(A1(_uX,_uW.a)),B(A1(_uX,_uW.b)),B(A1(_uX,_uW.c)));});},_uY=function(_uZ){return E(E(_uZ).a);},_v0=function(_v1,_v2,_v3,_v4){var _v5=new T(function(){var _v6=E(_v4),_v7=E(_v3),_v8=B(_uM(_v1,_v6.a,_v6.b,_v6.c,_v7.a,_v7.b,_v7.c));return new T3(0,E(_v8.a),E(_v8.b),E(_v8.c));}),_v9=new T(function(){return B(A2(_9t,_v1,new T(function(){var _va=E(_v5),_vb=_va.a,_vc=_va.b,_vd=_va.c;return B(_tM(_v1,_vb,_vc,_vd,_vb,_vc,_vd));})));});if(!B(A3(_uY,B(_uK(_v2)),_v9,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_v1)))),_8q));})))){var _ve=E(_v5),_vf=B(_tW(_v1,_ve.a,_ve.b,_ve.c)),_vg=B(A2(_9t,_v1,new T(function(){var _vh=E(_v4),_vi=_vh.a,_vj=_vh.b,_vk=_vh.c;return B(_tM(_v1,_vi,_vj,_vk,_vi,_vj,_vk));}))),_vl=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_v1));})));})));return new T3(0,B(A1(B(A1(_vl,_vf.a)),_vg)),B(A1(B(A1(_vl,_vf.b)),_vg)),B(A1(B(A1(_vl,_vf.c)),_vg)));}else{var _vm=B(A2(_8s,B(_8J(B(_8H(_v1)))),_8q));return new T3(0,_vm,_vm,_vm);}},_vn=0,_vo=new T3(0,E(_vn),E(_vn),E(_vn)),_vp=function(_vq,_vr){while(1){var _vs=E(_vq);if(!_vs._){return E(_vr);}else{var _vt=_vs.b,_vu=E(_vs.a);if(_vr>_vu){_vq=_vt;continue;}else{_vq=_vt;_vr=_vu;continue;}}}},_vv=new T(function(){var _vw=eval("angleCount"),_vx=Number(_vw);return jsTrunc(_vx);}),_vy=new T(function(){return E(_vv);}),_vz=new T(function(){return B(unCStr("head"));}),_vA=new T(function(){return B(_pr(_vz));}),_vB=function(_vC,_vD,_vE){var _vF=E(_vC);if(!_vF._){return __Z;}else{var _vG=E(_vD);if(!_vG._){return __Z;}else{var _vH=_vG.a,_vI=E(_vE);if(!_vI._){return __Z;}else{var _vJ=E(_vI.a),_vK=_vJ.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_vF.a),E(_vH),E(_vK));}),new T2(1,new T(function(){return new T3(0,E(_vH),E(_vK),E(_vJ.b));}),_w)),new T(function(){return B(_vB(_vF.b,_vG.b,_vI.b));},1));});}}}},_vL=new T(function(){return B(unCStr("tail"));}),_vM=new T(function(){return B(_pr(_vL));}),_vN=function(_vO,_vP){var _vQ=E(_vO);if(!_vQ._){return __Z;}else{var _vR=E(_vP);return (_vR._==0)?__Z:new T2(1,new T2(0,_vQ.a,_vR.a),new T(function(){return B(_vN(_vQ.b,_vR.b));}));}},_vS=function(_vT,_vU){var _vV=E(_vT);if(!_vV._){return __Z;}else{var _vW=E(_vU);if(!_vW._){return __Z;}else{var _vX=E(_vV.a),_vY=_vX.b,_vZ=E(_vW.a).b,_w0=new T(function(){var _w1=new T(function(){return B(_vN(_vZ,new T(function(){var _w2=E(_vZ);if(!_w2._){return E(_vM);}else{return E(_w2.b);}},1)));},1);return B(_vB(_vY,new T(function(){var _w3=E(_vY);if(!_w3._){return E(_vM);}else{return E(_w3.b);}},1),_w1));});return new F(function(){return _n(new T2(1,new T(function(){var _w4=E(_vY);if(!_w4._){return E(_vA);}else{var _w5=E(_vZ);if(!_w5._){return E(_vA);}else{return new T3(0,E(_vX.a),E(_w4.a),E(_w5.a));}}}),_w0),new T(function(){return B(_vS(_vV.b,_vW.b));},1));});}}},_w6=new T(function(){return 6.283185307179586/E(_vy);}),_w7=new T(function(){return E(_vy)-1;}),_w8=new T1(0,1),_w9=function(_wa,_wb){var _wc=E(_wb),_wd=new T(function(){var _we=B(_8J(_wa)),_wf=B(_w9(_wa,B(A3(_6X,_we,_wc,new T(function(){return B(A2(_8s,_we,_w8));})))));return new T2(1,_wf.a,_wf.b);});return new T2(0,_wc,_wd);},_wg=function(_wh){return E(E(_wh).d);},_wi=new T1(0,2),_wj=function(_wk,_wl){var _wm=E(_wl);if(!_wm._){return __Z;}else{var _wn=_wm.a;return (!B(A1(_wk,_wn)))?__Z:new T2(1,_wn,new T(function(){return B(_wj(_wk,_wm.b));}));}},_wo=function(_wp,_wq,_wr,_ws){var _wt=B(_w9(_wq,_wr)),_wu=new T(function(){var _wv=B(_8J(_wq)),_ww=new T(function(){return B(A3(_8P,_wq,new T(function(){return B(A2(_8s,_wv,_w8));}),new T(function(){return B(A2(_8s,_wv,_wi));})));});return B(A3(_6X,_wv,_ws,_ww));});return new F(function(){return _wj(function(_wx){return new F(function(){return A3(_wg,_wp,_wx,_wu);});},new T2(1,_wt.a,_wt.b));});},_wy=new T(function(){return B(_wo(_t7,_nP,_vn,_w7));}),_wz=function(_wA,_wB){while(1){var _wC=E(_wA);if(!_wC._){return E(_wB);}else{_wA=_wC.b;_wB=_wC.a;continue;}}},_wD=new T(function(){return B(unCStr("last"));}),_wE=new T(function(){return B(_pr(_wD));}),_wF=function(_wG){return new F(function(){return _wz(_wG,_wE);});},_wH=function(_wI){return new F(function(){return _wF(E(_wI).b);});},_wJ=new T(function(){return B(unCStr("maximum"));}),_wK=new T(function(){return B(_pr(_wJ));}),_wL=new T(function(){var _wM=eval("proceedCount"),_wN=Number(_wM);return jsTrunc(_wN);}),_wO=new T(function(){return E(_wL);}),_wP=1,_wQ=new T(function(){return B(_wo(_t7,_nP,_wP,_wO));}),_wR=function(_wS,_wT,_wU,_wV,_wW,_wX,_wY,_wZ,_x0,_x1,_x2,_x3,_x4,_x5){var _x6=new T(function(){var _x7=new T(function(){var _x8=E(_x1),_x9=E(_x5),_xa=E(_x4),_xb=E(_x2),_xc=E(_x3),_xd=E(_x0);return new T3(0,_x8*_x9-_xa*_xb,_xb*_xc-_x9*_xd,_xd*_xa-_xc*_x8);}),_xe=function(_xf){var _xg=new T(function(){var _xh=E(_xf)/E(_vy);return (_xh+_xh)*3.141592653589793;}),_xi=new T(function(){return B(A1(_wS,_xg));}),_xj=new T(function(){var _xk=new T(function(){var _xl=E(_xi)/E(_wO);return new T3(0,E(_xl),E(_xl),E(_xl));}),_xm=function(_xn,_xo){var _xp=E(_xn);if(!_xp._){return new T2(0,_w,_xo);}else{var _xq=new T(function(){var _xr=B(_ul(_tL,new T(function(){var _xs=E(_xo),_xt=E(_xs.a),_xu=E(_xs.b),_xv=E(_xk);return new T3(0,E(_xt.a)+E(_xu.a)*E(_xv.a),E(_xt.b)+E(_xu.b)*E(_xv.b),E(_xt.c)+E(_xu.c)*E(_xv.c));}))),_xw=_xr.a,_xx=new T(function(){var _xy=E(_xr.b),_xz=E(E(_xo).b),_xA=B(_uM(_oh,_xz.a,_xz.b,_xz.c,_xy.a,_xy.b,_xy.c)),_xB=B(_tW(_oh,_xA.a,_xA.b,_xA.c));return new T3(0,E(_xB.a),E(_xB.b),E(_xB.c));});return new T2(0,new T(function(){var _xC=E(_xi),_xD=E(_xg);return new T4(0,E(_xw),E(new T2(0,E(_xp.a)/E(_wO),E(_xC))),E(_xD),E(_xx));}),new T2(0,_xw,_xx));}),_xE=new T(function(){var _xF=B(_xm(_xp.b,new T(function(){return E(E(_xq).b);})));return new T2(0,_xF.a,_xF.b);});return new T2(0,new T2(1,new T(function(){return E(E(_xq).a);}),new T(function(){return E(E(_xE).a);})),new T(function(){return E(E(_xE).b);}));}},_xG=function(_xH,_xI,_xJ,_xK,_xL){var _xM=E(_xH);if(!_xM._){return new T2(0,_w,new T2(0,new T3(0,E(_xI),E(_xJ),E(_xK)),_xL));}else{var _xN=new T(function(){var _xO=B(_ul(_tL,new T(function(){var _xP=E(_xL),_xQ=E(_xk);return new T3(0,E(_xI)+E(_xP.a)*E(_xQ.a),E(_xJ)+E(_xP.b)*E(_xQ.b),E(_xK)+E(_xP.c)*E(_xQ.c));}))),_xR=_xO.a,_xS=new T(function(){var _xT=E(_xO.b),_xU=E(_xL),_xV=B(_uM(_oh,_xU.a,_xU.b,_xU.c,_xT.a,_xT.b,_xT.c)),_xW=B(_tW(_oh,_xV.a,_xV.b,_xV.c));return new T3(0,E(_xW.a),E(_xW.b),E(_xW.c));});return new T2(0,new T(function(){var _xX=E(_xi),_xY=E(_xg);return new T4(0,E(_xR),E(new T2(0,E(_xM.a)/E(_wO),E(_xX))),E(_xY),E(_xS));}),new T2(0,_xR,_xS));}),_xZ=new T(function(){var _y0=B(_xm(_xM.b,new T(function(){return E(E(_xN).b);})));return new T2(0,_y0.a,_y0.b);});return new T2(0,new T2(1,new T(function(){return E(E(_xN).a);}),new T(function(){return E(E(_xZ).a);})),new T(function(){return E(E(_xZ).b);}));}};return E(B(_xG(_wQ,_wV,_wW,_wX,new T(function(){var _y1=E(_x7),_y2=E(_xg)+_wY,_y3=Math.cos(_y2),_y4=Math.sin(_y2);return new T3(0,E(_x0)*_y3+E(_y1.a)*_y4,E(_x1)*_y3+E(_y1.b)*_y4,E(_x2)*_y3+E(_y1.c)*_y4);}))).a);});return new T2(0,new T(function(){var _y5=E(_xi),_y6=E(_xg);return new T4(0,E(new T3(0,E(_wV),E(_wW),E(_wX))),E(new T2(0,E(_vn),E(_y5))),E(_y6),E(_vo));}),_xj);};return B(_tz(_xe,_wy));}),_y7=new T(function(){var _y8=function(_y9){return new F(function(){return A1(_wS,new T(function(){return B(_nI(_y9,_w6));}));});},_ya=B(_tz(_y8,_wy));if(!_ya._){return E(_wK);}else{return B(_vp(_ya.b,E(_ya.a)));}}),_yb=new T(function(){var _yc=new T(function(){var _yd=B(_n(_x6,new T2(1,new T(function(){var _ye=E(_x6);if(!_ye._){return E(_vA);}else{return E(_ye.a);}}),_w)));if(!_yd._){return E(_vM);}else{return E(_yd.b);}},1);return B(_vS(_x6,_yc));});return new T3(0,_yb,new T(function(){return B(_tz(_wH,_x6));}),_y7);},_yf=function(_yg,_yh,_yi,_yj,_yk,_yl,_ym,_yn,_yo,_yp,_yq,_yr,_ys,_yt,_yu,_yv,_yw,_yx){var _yy=B(_ul(_tL,new T3(0,E(_yj),E(_yk),E(_yl)))),_yz=_yy.b,_yA=E(_yy.a),_yB=B(_v0(_oh,_t7,_yz,new T3(0,E(_yn),E(_yo),E(_yp)))),_yC=E(_yz),_yD=_yC.a,_yE=_yC.b,_yF=_yC.c,_yG=B(_uM(_oh,_yr,_ys,_yt,_yD,_yE,_yF)),_yH=B(_tW(_oh,_yG.a,_yG.b,_yG.c)),_yI=_yH.a,_yJ=_yH.b,_yK=_yH.c,_yL=E(_ym),_yM=new T2(0,E(new T3(0,E(_yB.a),E(_yB.b),E(_yB.c))),E(_yq)),_yN=B(_wR(_yg,_yh,_yi,_yA.a,_yA.b,_yA.c,_yL,_yM,_yI,_yJ,_yK,_yD,_yE,_yF)),_yO=__lst2arr(B(_tz(_tI,_yN.a))),_yP=__lst2arr(B(_tz(_tt,_yN.b)));return {_:0,a:_yg,b:_yh,c:_yi,d:new T2(0,E(_yA),E(_yL)),e:_yM,f:new T3(0,E(_yI),E(_yJ),E(_yK)),g:_yC,h:_yO,i:_yP,j:E(_yN.c)};},_yQ=1.0e-2,_yR=function(_yS,_yT,_yU,_yV,_yW,_yX,_yY,_yZ,_z0,_z1,_z2,_z3,_z4,_z5,_z6,_z7,_z8,_z9){var _za=B(_sd(_nL,_yZ,_z0,_z1,_z2,_yQ,_yQ,_yQ,_yQ)),_zb=E(_za.a),_zc=B(_so(_nL,_yV,_yW,_yX,_yY,_zb.a,_zb.b,_zb.c,_za.b)),_zd=E(_zc.a);return new F(function(){return _yf(_yS,_yT,_yU,_zd.a,_zd.b,_zd.c,_zc.b,_yZ,_z0,_z1,_z2,_z3,_z4,_z5,_z6,_z7,_z8,_z9);});},_ze=function(_zf){var _zg=E(_zf),_zh=E(_zg.d),_zi=E(_zh.a),_zj=E(_zg.e),_zk=E(_zj.a),_zl=E(_zg.f),_zm=B(_yR(_zg.a,_zg.b,_zg.c,_zi.a,_zi.b,_zi.c,_zh.b,_zk.a,_zk.b,_zk.c,_zj.b,_zl.a,_zl.b,_zl.c,_zg.g,_zg.h,_zg.i,_zg.j));return {_:0,a:E(_zm.a),b:E(_zm.b),c:E(_zm.c),d:E(_zm.d),e:E(_zm.e),f:E(_zm.f),g:E(_zm.g),h:_zm.h,i:_zm.i,j:_zm.j};},_zn=function(_zo,_zp,_zq,_zr,_zs,_zt,_zu,_zv,_zw){var _zx=B(_8J(B(_8H(_zo))));return new F(function(){return A3(_6X,_zx,new T(function(){return B(_tM(_zo,_zp,_zq,_zr,_zt,_zu,_zv));}),new T(function(){return B(A3(_8L,_zx,_zs,_zw));}));});},_zy=new T(function(){return B(unCStr("base"));}),_zz=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_zA=new T(function(){return B(unCStr("IOException"));}),_zB=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_zy,_zz,_zA),_zC=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_zB,_w,_w),_zD=function(_zE){return E(_zC);},_zF=function(_zG){var _zH=E(_zG);return new F(function(){return _2n(B(_2l(_zH.a)),_zD,_zH.b);});},_zI=new T(function(){return B(unCStr(": "));}),_zJ=new T(function(){return B(unCStr(")"));}),_zK=new T(function(){return B(unCStr(" ("));}),_zL=new T(function(){return B(unCStr("interrupted"));}),_zM=new T(function(){return B(unCStr("system error"));}),_zN=new T(function(){return B(unCStr("unsatisified constraints"));}),_zO=new T(function(){return B(unCStr("user error"));}),_zP=new T(function(){return B(unCStr("permission denied"));}),_zQ=new T(function(){return B(unCStr("illegal operation"));}),_zR=new T(function(){return B(unCStr("end of file"));}),_zS=new T(function(){return B(unCStr("resource exhausted"));}),_zT=new T(function(){return B(unCStr("resource busy"));}),_zU=new T(function(){return B(unCStr("does not exist"));}),_zV=new T(function(){return B(unCStr("already exists"));}),_zW=new T(function(){return B(unCStr("resource vanished"));}),_zX=new T(function(){return B(unCStr("timeout"));}),_zY=new T(function(){return B(unCStr("unsupported operation"));}),_zZ=new T(function(){return B(unCStr("hardware fault"));}),_A0=new T(function(){return B(unCStr("inappropriate type"));}),_A1=new T(function(){return B(unCStr("invalid argument"));}),_A2=new T(function(){return B(unCStr("failed"));}),_A3=new T(function(){return B(unCStr("protocol error"));}),_A4=function(_A5,_A6){switch(E(_A5)){case 0:return new F(function(){return _n(_zV,_A6);});break;case 1:return new F(function(){return _n(_zU,_A6);});break;case 2:return new F(function(){return _n(_zT,_A6);});break;case 3:return new F(function(){return _n(_zS,_A6);});break;case 4:return new F(function(){return _n(_zR,_A6);});break;case 5:return new F(function(){return _n(_zQ,_A6);});break;case 6:return new F(function(){return _n(_zP,_A6);});break;case 7:return new F(function(){return _n(_zO,_A6);});break;case 8:return new F(function(){return _n(_zN,_A6);});break;case 9:return new F(function(){return _n(_zM,_A6);});break;case 10:return new F(function(){return _n(_A3,_A6);});break;case 11:return new F(function(){return _n(_A2,_A6);});break;case 12:return new F(function(){return _n(_A1,_A6);});break;case 13:return new F(function(){return _n(_A0,_A6);});break;case 14:return new F(function(){return _n(_zZ,_A6);});break;case 15:return new F(function(){return _n(_zY,_A6);});break;case 16:return new F(function(){return _n(_zX,_A6);});break;case 17:return new F(function(){return _n(_zW,_A6);});break;default:return new F(function(){return _n(_zL,_A6);});}},_A7=new T(function(){return B(unCStr("}"));}),_A8=new T(function(){return B(unCStr("{handle: "));}),_A9=function(_Aa,_Ab,_Ac,_Ad,_Ae,_Af){var _Ag=new T(function(){var _Ah=new T(function(){var _Ai=new T(function(){var _Aj=E(_Ad);if(!_Aj._){return E(_Af);}else{var _Ak=new T(function(){return B(_n(_Aj,new T(function(){return B(_n(_zJ,_Af));},1)));},1);return B(_n(_zK,_Ak));}},1);return B(_A4(_Ab,_Ai));}),_Al=E(_Ac);if(!_Al._){return E(_Ah);}else{return B(_n(_Al,new T(function(){return B(_n(_zI,_Ah));},1)));}}),_Am=E(_Ae);if(!_Am._){var _An=E(_Aa);if(!_An._){return E(_Ag);}else{var _Ao=E(_An.a);if(!_Ao._){var _Ap=new T(function(){var _Aq=new T(function(){return B(_n(_A7,new T(function(){return B(_n(_zI,_Ag));},1)));},1);return B(_n(_Ao.a,_Aq));},1);return new F(function(){return _n(_A8,_Ap);});}else{var _Ar=new T(function(){var _As=new T(function(){return B(_n(_A7,new T(function(){return B(_n(_zI,_Ag));},1)));},1);return B(_n(_Ao.a,_As));},1);return new F(function(){return _n(_A8,_Ar);});}}}else{return new F(function(){return _n(_Am.a,new T(function(){return B(_n(_zI,_Ag));},1));});}},_At=function(_Au){var _Av=E(_Au);return new F(function(){return _A9(_Av.a,_Av.b,_Av.c,_Av.d,_Av.f,_w);});},_Aw=function(_Ax,_Ay,_Az){var _AA=E(_Ay);return new F(function(){return _A9(_AA.a,_AA.b,_AA.c,_AA.d,_AA.f,_Az);});},_AB=function(_AC,_AD){var _AE=E(_AC);return new F(function(){return _A9(_AE.a,_AE.b,_AE.c,_AE.d,_AE.f,_AD);});},_AF=function(_AG,_AH){return new F(function(){return _2Q(_AB,_AG,_AH);});},_AI=new T3(0,_Aw,_At,_AF),_AJ=new T(function(){return new T5(0,_zD,_AI,_AK,_zF,_At);}),_AK=function(_AL){return new T2(0,_AJ,_AL);},_AM=__Z,_AN=7,_AO=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_AP=new T6(0,_AM,_AN,_w,_AO,_AM,_AM),_AQ=new T(function(){return B(_AK(_AP));}),_AR=function(_){return new F(function(){return die(_AQ);});},_AS=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_AT=new T6(0,_AM,_AN,_w,_AS,_AM,_AM),_AU=new T(function(){return B(_AK(_AT));}),_AV=function(_){return new F(function(){return die(_AU);});},_AW=function(_AX,_){return new T2(0,_w,_AX);},_AY=0.6,_AZ=1,_B0=new T(function(){return B(unCStr(")"));}),_B1=function(_B2,_B3){var _B4=new T(function(){var _B5=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mB(0,_B2,_w)),_B0));})));},1);return B(_n(B(_mB(0,_B3,_w)),_B5));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_B4)));});},_B6=function(_B7,_B8){var _B9=new T(function(){var _Ba=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_mB(0,_B8,_w)),_B0));})));},1);return B(_n(B(_mB(0,_B7,_w)),_Ba));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_B9)));});},_Bb=function(_Bc){var _Bd=E(_Bc);if(!_Bd._){return E(_AW);}else{var _Be=new T(function(){return B(_Bb(_Bd.b));}),_Bf=function(_Bg){var _Bh=E(_Bg);if(!_Bh._){return E(_Be);}else{var _Bi=_Bh.a,_Bj=new T(function(){return B(_Bf(_Bh.b));}),_Bk=new T(function(){return 0.1*E(E(_Bi).e)/1.0e-2;}),_Bl=new T(function(){var _Bm=E(_Bi);if(_Bm.a!=_Bm.b){return E(_AZ);}else{return E(_AY);}}),_Bn=function(_Bo,_){var _Bp=E(_Bo),_Bq=_Bp.c,_Br=_Bp.d,_Bs=E(_Bp.a),_Bt=E(_Bp.b),_Bu=E(_Bi),_Bv=_Bu.a,_Bw=_Bu.b,_Bx=E(_Bu.c),_By=_Bx.b,_Bz=E(_Bx.a),_BA=_Bz.a,_BB=_Bz.b,_BC=_Bz.c,_BD=E(_Bu.d),_BE=_BD.b,_BF=E(_BD.a),_BG=_BF.a,_BH=_BF.b,_BI=_BF.c;if(_Bs>_Bv){return new F(function(){return _AV(_);});}else{if(_Bv>_Bt){return new F(function(){return _AV(_);});}else{if(_Bs>_Bw){return new F(function(){return _AR(_);});}else{if(_Bw>_Bt){return new F(function(){return _AR(_);});}else{var _BJ=_Bv-_Bs|0;if(0>_BJ){return new F(function(){return _B1(_Bq,_BJ);});}else{if(_BJ>=_Bq){return new F(function(){return _B1(_Bq,_BJ);});}else{var _BK=E(_Br[_BJ]),_BL=E(_BK.c),_BM=_BL.b,_BN=E(_BL.a),_BO=_BN.a,_BP=_BN.b,_BQ=_BN.c,_BR=E(_BK.e),_BS=E(_BR.a),_BT=B(_sd(_nL,_BA,_BB,_BC,_By,_BO,_BP,_BQ,_BM)),_BU=E(_BT.a),_BV=B(_sd(_nL,_BU.a,_BU.b,_BU.c,_BT.b,_BA,_BB,_BC,_By)),_BW=E(_BV.a),_BX=_Bw-_Bs|0;if(0>_BX){return new F(function(){return _B6(_BX,_Bq);});}else{if(_BX>=_Bq){return new F(function(){return _B6(_BX,_Bq);});}else{var _BY=E(_Br[_BX]),_BZ=E(_BY.c),_C0=_BZ.b,_C1=E(_BZ.a),_C2=_C1.a,_C3=_C1.b,_C4=_C1.c,_C5=E(_BY.e),_C6=E(_C5.a),_C7=B(_sd(_nL,_BG,_BH,_BI,_BE,_C2,_C3,_C4,_C0)),_C8=E(_C7.a),_C9=B(_sd(_nL,_C8.a,_C8.b,_C8.c,_C7.b,_BG,_BH,_BI,_BE)),_Ca=E(_C9.a),_Cb=E(_BW.a)+E(_BW.b)+E(_BW.c)+E(_BV.b)+E(_Ca.a)+E(_Ca.b)+E(_Ca.c)+E(_C9.b);if(!_Cb){var _Cc=B(A2(_Bj,_Bp,_));return new T2(0,new T2(1,_mg,new T(function(){return E(E(_Cc).a);})),new T(function(){return E(E(_Cc).b);}));}else{var _Cd=new T(function(){return  -((B(_zn(_oh,_BS.a,_BS.b,_BS.c,_BR.b,_BA,_BB,_BC,_By))-B(_zn(_oh,_C6.a,_C6.b,_C6.c,_C5.b,_BG,_BH,_BI,_BE))-E(_Bk))/_Cb);}),_Ce=function(_Cf,_Cg,_Ch,_Ci,_){var _Cj=new T(function(){var _Ck=function(_Cl,_Cm,_Cn,_Co,_Cp){if(_Cl>_Bw){return E(_Cp);}else{if(_Bw>_Cm){return E(_Cp);}else{var _Cq=function(_){var _Cr=newArr(_Cn,_ry),_Cs=_Cr,_Ct=function(_Cu,_){while(1){if(_Cu!=_Cn){var _=_Cs[_Cu]=_Co[_Cu],_Cv=_Cu+1|0;_Cu=_Cv;continue;}else{return E(_);}}},_=B(_Ct(0,_)),_Cw=_Bw-_Cl|0;if(0>_Cw){return new F(function(){return _B6(_Cw,_Cn);});}else{if(_Cw>=_Cn){return new F(function(){return _B6(_Cw,_Cn);});}else{var _=_Cs[_Cw]=new T(function(){var _Cx=E(_Co[_Cw]),_Cy=E(_Cx.e),_Cz=E(_Cy.a),_CA=B(_sd(_nL,_C2,_C3,_C4,_C0,_BG,_BH,_BI,_BE)),_CB=E(_CA.a),_CC=E(_Cd)*E(_Bl),_CD=B(_sd(_nL,_CB.a,_CB.b,_CB.c,_CA.b,_CC,_CC,_CC,_CC)),_CE=E(_CD.a),_CF=B(_so(_nL,_Cz.a,_Cz.b,_Cz.c,_Cy.b, -E(_CE.a), -E(_CE.b), -E(_CE.c), -E(_CD.b)));return {_:0,a:E(_Cx.a),b:E(_Cx.b),c:E(_Cx.c),d:E(_Cx.d),e:E(new T2(0,E(_CF.a),E(_CF.b))),f:E(_Cx.f),g:E(_Cx.g),h:_Cx.h,i:_Cx.i,j:_Cx.j};});return new T4(0,E(_Cl),E(_Cm),_Cn,_Cs);}}};return new F(function(){return _rD(_Cq);});}}};if(_Cf>_Bv){return B(_Ck(_Cf,_Cg,_Ch,_Ci,new T4(0,E(_Cf),E(_Cg),_Ch,_Ci)));}else{if(_Bv>_Cg){return B(_Ck(_Cf,_Cg,_Ch,_Ci,new T4(0,E(_Cf),E(_Cg),_Ch,_Ci)));}else{var _CG=function(_){var _CH=newArr(_Ch,_ry),_CI=_CH,_CJ=function(_CK,_){while(1){if(_CK!=_Ch){var _=_CI[_CK]=_Ci[_CK],_CL=_CK+1|0;_CK=_CL;continue;}else{return E(_);}}},_=B(_CJ(0,_)),_CM=_Bv-_Cf|0;if(0>_CM){return new F(function(){return _B1(_Ch,_CM);});}else{if(_CM>=_Ch){return new F(function(){return _B1(_Ch,_CM);});}else{var _=_CI[_CM]=new T(function(){var _CN=E(_Ci[_CM]),_CO=E(_CN.e),_CP=E(_CO.a),_CQ=B(_sd(_nL,_BO,_BP,_BQ,_BM,_BA,_BB,_BC,_By)),_CR=E(_CQ.a),_CS=E(_Cd)*E(_Bl),_CT=B(_sd(_nL,_CR.a,_CR.b,_CR.c,_CQ.b,_CS,_CS,_CS,_CS)),_CU=E(_CT.a),_CV=B(_so(_nL,_CP.a,_CP.b,_CP.c,_CO.b,_CU.a,_CU.b,_CU.c,_CT.b));return {_:0,a:E(_CN.a),b:E(_CN.b),c:E(_CN.c),d:E(_CN.d),e:E(new T2(0,E(_CV.a),E(_CV.b))),f:E(_CN.f),g:E(_CN.g),h:_CN.h,i:_CN.i,j:_CN.j};});return new T4(0,E(_Cf),E(_Cg),_Ch,_CI);}}},_CW=B(_rD(_CG));return B(_Ck(E(_CW.a),E(_CW.b),_CW.c,_CW.d,_CW));}}});return new T2(0,_mg,_Cj);};if(!E(_Bu.f)){var _CX=B(_Ce(_Bs,_Bt,_Bq,_Br,_)),_CY=B(A2(_Bj,new T(function(){return E(E(_CX).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_CX).a);}),new T(function(){return E(E(_CY).a);})),new T(function(){return E(E(_CY).b);}));}else{if(E(_Cd)<0){var _CZ=B(A2(_Bj,_Bp,_));return new T2(0,new T2(1,_mg,new T(function(){return E(E(_CZ).a);})),new T(function(){return E(E(_CZ).b);}));}else{var _D0=B(_Ce(_Bs,_Bt,_Bq,_Br,_)),_D1=B(A2(_Bj,new T(function(){return E(E(_D0).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_D0).a);}),new T(function(){return E(E(_D1).a);})),new T(function(){return E(E(_D1).b);}));}}}}}}}}}}}};return E(_Bn);}};return new F(function(){return _Bf(_Bd.a);});}},_D2=function(_,_D3){var _D4=new T(function(){return B(_Bb(E(_D3).a));}),_D5=function(_D6){var _D7=E(_D6);return (_D7==1)?E(new T2(1,_D4,_w)):new T2(1,_D4,new T(function(){return B(_D5(_D7-1|0));}));},_D8=B(_ri(B(_D5(5)),new T(function(){return E(E(_D3).b);}),_)),_D9=new T(function(){return B(_rX(_rh,_n3,_ze,new T(function(){return E(E(_D8).b);})));});return new T2(0,_mg,_D9);},_Da=function(_Db,_Dc,_Dd,_De,_Df){var _Dg=B(_8J(B(_8H(_Db))));return new F(function(){return A3(_6X,_Dg,new T(function(){return B(A3(_8L,_Dg,_Dc,_De));}),new T(function(){return B(A3(_8L,_Dg,_Dd,_Df));}));});},_Dh=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Di=new T6(0,_AM,_AN,_w,_Dh,_AM,_AM),_Dj=new T(function(){return B(_AK(_Di));}),_Dk=function(_){return new F(function(){return die(_Dj);});},_Dl=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Dm=new T6(0,_AM,_AN,_w,_Dl,_AM,_AM),_Dn=new T(function(){return B(_AK(_Dm));}),_Do=function(_){return new F(function(){return die(_Dn);});},_Dp=false,_Dq=true,_Dr=function(_Ds){var _Dt=E(_Ds),_Du=_Dt.b,_Dv=E(_Dt.d),_Dw=E(_Dt.e),_Dx=E(_Dw.a),_Dy=E(_Dt.g),_Dz=B(A1(_Du,_Dv.a)),_DA=B(_uM(_oh,_Dz.a,_Dz.b,_Dz.c,_Dy.a,_Dy.b,_Dy.c));return {_:0,a:E(_Dt.a),b:E(_Du),c:E(_Dt.c),d:E(_Dv),e:E(new T2(0,E(new T3(0,E(_Dx.a)+E(_DA.a)*1.0e-2,E(_Dx.b)+E(_DA.b)*1.0e-2,E(_Dx.c)+E(_DA.c)*1.0e-2)),E(_Dw.b))),f:E(_Dt.f),g:E(_Dy),h:_Dt.h,i:_Dt.i,j:_Dt.j};},_DB=new T(function(){return eval("__strict(collideBound)");}),_DC=new T(function(){return eval("__strict(mouseContact)");}),_DD=new T(function(){return eval("__strict(collide)");}),_DE=function(_DF){var _DG=E(_DF);if(!_DG._){return __Z;}else{return new F(function(){return _n(_DG.a,new T(function(){return B(_DE(_DG.b));},1));});}},_DH=0,_DI=new T3(0,E(_DH),E(_DH),E(_DH)),_DJ=new T2(0,E(_DI),E(_DH)),_DK=new T2(0,_oh,_t7),_DL=new T(function(){return B(_lN(_DK));}),_DM=function(_DN,_){var _DO=B(_rX(_rh,_n3,_Dr,_DN)),_DP=E(_DO.a),_DQ=E(_DO.b);if(_DP<=_DQ){var _DR=function(_DS,_DT,_DU,_DV,_DW,_){if(_DT>_DS){return new F(function(){return _Do(_);});}else{if(_DS>_DU){return new F(function(){return _Do(_);});}else{var _DX=new T(function(){var _DY=_DS-_DT|0;if(0>_DY){return B(_B6(_DY,_DV));}else{if(_DY>=_DV){return B(_B6(_DY,_DV));}else{return E(_DW[_DY]);}}}),_DZ=function(_E0,_E1,_E2,_E3,_E4,_){var _E5=E(_E0);if(!_E5._){return new T2(0,_w,new T4(0,E(_E1),E(_E2),_E3,_E4));}else{var _E6=E(_E5.a);if(_E1>_E6){return new F(function(){return _Dk(_);});}else{if(_E6>_E2){return new F(function(){return _Dk(_);});}else{var _E7=_E6-_E1|0;if(0>_E7){return new F(function(){return _B1(_E3,_E7);});}else{if(_E7>=_E3){return new F(function(){return _B1(_E3,_E7);});}else{var _E8=__app2(E(_DD),B(_mr(E(_DX))),B(_mr(E(_E4[_E7])))),_E9=__arr2lst(0,_E8),_Ea=B(_oU(_E9,_)),_Eb=B(_DZ(_E5.b,_E1,_E2,_E3,_E4,_)),_Ec=new T(function(){var _Ed=new T(function(){return _DS!=_E6;}),_Ee=function(_Ef){var _Eg=E(_Ef);if(!_Eg._){return __Z;}else{var _Eh=_Eg.b,_Ei=E(_Eg.a),_Ej=E(_Ei.b),_Ek=E(_Ei.a),_El=E(_Ei.c),_Em=_El.a,_En=_El.b,_Eo=E(_Ei.e),_Ep=E(_Ei.d),_Eq=_Ep.a,_Er=_Ep.b,_Es=E(_Ei.f),_Et=new T(function(){var _Eu=B(_tW(_oh,_Es.a,_Es.b,_Es.c)),_Ev=Math.sqrt(B(_Da(_oh,_Eq,_Er,_Eq,_Er)));return new T3(0,_Ev*E(_Eu.a),_Ev*E(_Eu.b),_Ev*E(_Eu.c));}),_Ew=new T(function(){var _Ex=B(_tW(_oh,_Eo.a,_Eo.b,_Eo.c)),_Ey=Math.sqrt(B(_Da(_oh,_Em,_En,_Em,_En)));return new T3(0,_Ey*E(_Ex.a),_Ey*E(_Ex.b),_Ey*E(_Ex.c));}),_Ez=new T(function(){var _EA=B(A1(_DL,_Ej)),_EB=B(_tW(_oh,_EA.a,_EA.b,_EA.c));return new T3(0,E(_EB.a),E(_EB.b),E(_EB.c));}),_EC=new T(function(){var _ED=B(A1(_DL,_Ek)),_EE=B(_tW(_oh,_ED.a,_ED.b,_ED.c));return new T3(0,E(_EE.a),E(_EE.b),E(_EE.c));}),_EF=E(_Ej.a)+ -E(_Ek.a),_EG=E(_Ej.b)+ -E(_Ek.b),_EH=E(_Ej.c)+ -E(_Ek.c),_EI=new T(function(){return Math.sqrt(B(_tM(_oh,_EF,_EG,_EH,_EF,_EG,_EH)));}),_EJ=new T(function(){var _EK=1/E(_EI);return new T3(0,_EF*_EK,_EG*_EK,_EH*_EK);}),_EL=new T(function(){if(!E(_Ei.g)){return E(_EJ);}else{var _EM=E(_EJ);return new T3(0,-1*E(_EM.a),-1*E(_EM.b),-1*E(_EM.c));}}),_EN=new T(function(){if(!E(_Ei.h)){return E(_EJ);}else{var _EO=E(_EJ);return new T3(0,-1*E(_EO.a),-1*E(_EO.b),-1*E(_EO.c));}});return (!E(_Ed))?new T2(1,new T(function(){var _EP=E(_EL),_EQ=E(_EP.b),_ER=E(_EP.c),_ES=E(_EP.a),_ET=E(_EC),_EU=E(_ET.c),_EV=E(_ET.b),_EW=E(_ET.a),_EX=E(_Ew),_EY=E(_EX.c),_EZ=E(_EX.b),_F0=E(_EX.a),_F1=_EQ*_EU-_EV*_ER,_F2=_ER*_EW-_EU*_ES,_F3=_ES*_EV-_EW*_EQ,_F4=B(_tM(_oh,_F2*_EY-_EZ*_F3,_F3*_F0-_EY*_F1,_F1*_EZ-_F0*_F2,_EW,_EV,_EU));return new T6(0,_DS,_E6,E(new T2(0,E(new T3(0,E(_F1),E(_F2),E(_F3))),E(_F4))),E(_DJ),_EI,_Dp);}),new T2(1,new T(function(){var _F5=E(_EN),_F6=E(_F5.b),_F7=E(_F5.c),_F8=E(_F5.a),_F9=E(_Ez),_Fa=E(_F9.c),_Fb=E(_F9.b),_Fc=E(_F9.a),_Fd=E(_Et),_Fe=E(_Fd.c),_Ff=E(_Fd.b),_Fg=E(_Fd.a),_Fh=_F6*_Fa-_Fb*_F7,_Fi=_F7*_Fc-_Fa*_F8,_Fj=_F8*_Fb-_Fc*_F6,_Fk=B(_tM(_oh,_Fi*_Fe-_Ff*_Fj,_Fj*_Fg-_Fe*_Fh,_Fh*_Ff-_Fg*_Fi,_Fc,_Fb,_Fa));return new T6(0,_DS,_E6,E(_DJ),E(new T2(0,E(new T3(0,E(_Fh),E(_Fi),E(_Fj))),E(_Fk))),_EI,_Dp);}),new T(function(){return B(_Ee(_Eh));}))):new T2(1,new T(function(){var _Fl=E(_EL),_Fm=E(_Fl.b),_Fn=E(_Fl.c),_Fo=E(_Fl.a),_Fp=E(_EC),_Fq=_Fp.a,_Fr=_Fp.b,_Fs=_Fp.c,_Ft=B(_uM(_oh,_Fo,_Fm,_Fn,_Fq,_Fr,_Fs)),_Fu=E(_Ew),_Fv=E(_Fu.c),_Fw=E(_Fu.b),_Fx=E(_Fu.a),_Fy=B(_tM(_oh,_Fm*_Fv-_Fw*_Fn,_Fn*_Fx-_Fv*_Fo,_Fo*_Fw-_Fx*_Fm,_Fq,_Fr,_Fs)),_Fz=E(_EN),_FA=E(_Fz.b),_FB=E(_Fz.c),_FC=E(_Fz.a),_FD=E(_Ez),_FE=_FD.a,_FF=_FD.b,_FG=_FD.c,_FH=B(_uM(_oh,_FC,_FA,_FB,_FE,_FF,_FG)),_FI=E(_Et),_FJ=E(_FI.c),_FK=E(_FI.b),_FL=E(_FI.a),_FM=B(_tM(_oh,_FA*_FJ-_FK*_FB,_FB*_FL-_FJ*_FC,_FC*_FK-_FL*_FA,_FE,_FF,_FG));return new T6(0,_DS,_E6,E(new T2(0,E(new T3(0,E(_Ft.a),E(_Ft.b),E(_Ft.c))),E(_Fy))),E(new T2(0,E(new T3(0,E(_FH.a),E(_FH.b),E(_FH.c))),E(_FM))),_EI,_Dq);}),new T(function(){return B(_Ee(_Eh));}));}};return B(_Ee(_Ea));});return new T2(0,new T2(1,_Ec,new T(function(){return E(E(_Eb).a);})),new T(function(){return E(E(_Eb).b);}));}}}}}},_FN=B(_DZ(B(_ql(_DS,_DQ)),_DT,_DU,_DV,_DW,_)),_FO=E(_DX),_FP=E(_FO.d).a,_FQ=__app1(E(_DB),B(_mr(_FO))),_FR=__arr2lst(0,_FQ),_FS=B(_oU(_FR,_)),_FT=__app1(E(_DC),_DS),_FU=__arr2lst(0,_FT),_FV=B(_oU(_FU,_));if(_DS!=_DQ){var _FW=E(_FN),_FX=E(_FW.b),_FY=B(_DR(_DS+1|0,E(_FX.a),E(_FX.b),_FX.c,_FX.d,_)),_FZ=new T(function(){var _G0=new T(function(){var _G1=B(A1(_DL,_FP)),_G2=B(_tW(_oh,_G1.a,_G1.b,_G1.c));return new T3(0,E(_G2.a),E(_G2.b),E(_G2.c));}),_G3=new T(function(){var _G4=new T(function(){return B(_DE(_FW.a));}),_G5=function(_G6){var _G7=E(_G6);if(!_G7._){return E(_G4);}else{var _G8=E(_G7.a),_G9=E(_G8.b),_Ga=E(_G8.a),_Gb=E(_G8.c),_Gc=_Gb.a,_Gd=_Gb.b,_Ge=E(_G8.e);return new T2(1,new T(function(){var _Gf=E(_G9.a)+ -E(_Ga.a),_Gg=E(_G9.b)+ -E(_Ga.b),_Gh=E(_G9.c)+ -E(_Ga.c),_Gi=B(A1(_DL,_Ga)),_Gj=B(_tW(_oh,_Gi.a,_Gi.b,_Gi.c)),_Gk=_Gj.a,_Gl=_Gj.b,_Gm=_Gj.c,_Gn=Math.sqrt(B(_tM(_oh,_Gf,_Gg,_Gh,_Gf,_Gg,_Gh))),_Go=1/_Gn,_Gp=_Gf*_Go,_Gq=_Gg*_Go,_Gr=_Gh*_Go,_Gs=B(_uM(_oh,_Gp,_Gq,_Gr,_Gk,_Gl,_Gm)),_Gt=B(_tW(_oh,_Ge.a,_Ge.b,_Ge.c)),_Gu=Math.sqrt(B(_Da(_oh,_Gc,_Gd,_Gc,_Gd))),_Gv=_Gu*E(_Gt.a),_Gw=_Gu*E(_Gt.b),_Gx=_Gu*E(_Gt.c),_Gy=B(_tM(_oh,_Gq*_Gx-_Gw*_Gr,_Gr*_Gv-_Gx*_Gp,_Gp*_Gw-_Gv*_Gq,_Gk,_Gl,_Gm));return new T6(0,_DS,_DS,E(new T2(0,E(new T3(0,E(_Gs.a),E(_Gs.b),E(_Gs.c))),E(_Gy))),E(_DJ),_Gn,_Dq);}),new T(function(){return B(_G5(_G7.b));}));}};return B(_G5(_FS));}),_Gz=function(_GA){var _GB=E(_GA);if(!_GB._){return E(_G3);}else{var _GC=E(_GB.a),_GD=E(_GC.b),_GE=new T(function(){var _GF=E(_FP),_GG=E(_GD.c)+ -E(_GF.c),_GH=E(_GD.b)+ -E(_GF.b),_GI=E(_GD.a)+ -E(_GF.a),_GJ=Math.sqrt(B(_tM(_oh,_GI,_GH,_GG,_GI,_GH,_GG))),_GK=function(_GL,_GM,_GN){var _GO=E(_G0),_GP=_GO.a,_GQ=_GO.b,_GR=_GO.c,_GS=B(_uM(_oh,_GL,_GM,_GN,_GP,_GQ,_GR)),_GT=B(_tM(_oh,_GM*0-0*_GN,_GN*0-0*_GL,_GL*0-0*_GM,_GP,_GQ,_GR));return new T6(0,_DS,_DS,new T2(0,E(new T3(0,E(_GS.a),E(_GS.b),E(_GS.c))),E(_GT)),_DJ,_GJ,_Dq);};if(!E(_GC.g)){var _GU=1/_GJ,_GV=B(_GK(_GI*_GU,_GH*_GU,_GG*_GU));return new T6(0,_GV.a,_GV.b,E(_GV.c),E(_GV.d),_GV.e,_GV.f);}else{var _GW=1/_GJ,_GX=B(_GK(-1*_GI*_GW,-1*_GH*_GW,-1*_GG*_GW));return new T6(0,_GX.a,_GX.b,E(_GX.c),E(_GX.d),_GX.e,_GX.f);}});return new T2(1,_GE,new T(function(){return B(_Gz(_GB.b));}));}};return B(_Gz(_FV));});return new T2(0,new T2(1,_FZ,new T(function(){return E(E(_FY).a);})),new T(function(){return E(E(_FY).b);}));}else{var _GY=new T(function(){var _GZ=new T(function(){var _H0=B(A1(_DL,_FP)),_H1=B(_tW(_oh,_H0.a,_H0.b,_H0.c));return new T3(0,E(_H1.a),E(_H1.b),E(_H1.c));}),_H2=new T(function(){var _H3=new T(function(){return B(_DE(E(_FN).a));}),_H4=function(_H5){var _H6=E(_H5);if(!_H6._){return E(_H3);}else{var _H7=E(_H6.a),_H8=E(_H7.b),_H9=E(_H7.a),_Ha=E(_H7.c),_Hb=_Ha.a,_Hc=_Ha.b,_Hd=E(_H7.e);return new T2(1,new T(function(){var _He=E(_H8.a)+ -E(_H9.a),_Hf=E(_H8.b)+ -E(_H9.b),_Hg=E(_H8.c)+ -E(_H9.c),_Hh=B(A1(_DL,_H9)),_Hi=B(_tW(_oh,_Hh.a,_Hh.b,_Hh.c)),_Hj=_Hi.a,_Hk=_Hi.b,_Hl=_Hi.c,_Hm=Math.sqrt(B(_tM(_oh,_He,_Hf,_Hg,_He,_Hf,_Hg))),_Hn=1/_Hm,_Ho=_He*_Hn,_Hp=_Hf*_Hn,_Hq=_Hg*_Hn,_Hr=B(_uM(_oh,_Ho,_Hp,_Hq,_Hj,_Hk,_Hl)),_Hs=B(_tW(_oh,_Hd.a,_Hd.b,_Hd.c)),_Ht=Math.sqrt(B(_Da(_oh,_Hb,_Hc,_Hb,_Hc))),_Hu=_Ht*E(_Hs.a),_Hv=_Ht*E(_Hs.b),_Hw=_Ht*E(_Hs.c),_Hx=B(_tM(_oh,_Hp*_Hw-_Hv*_Hq,_Hq*_Hu-_Hw*_Ho,_Ho*_Hv-_Hu*_Hp,_Hj,_Hk,_Hl));return new T6(0,_DS,_DS,E(new T2(0,E(new T3(0,E(_Hr.a),E(_Hr.b),E(_Hr.c))),E(_Hx))),E(_DJ),_Hm,_Dq);}),new T(function(){return B(_H4(_H6.b));}));}};return B(_H4(_FS));}),_Hy=function(_Hz){var _HA=E(_Hz);if(!_HA._){return E(_H2);}else{var _HB=E(_HA.a),_HC=E(_HB.b),_HD=new T(function(){var _HE=E(_FP),_HF=E(_HC.c)+ -E(_HE.c),_HG=E(_HC.b)+ -E(_HE.b),_HH=E(_HC.a)+ -E(_HE.a),_HI=Math.sqrt(B(_tM(_oh,_HH,_HG,_HF,_HH,_HG,_HF))),_HJ=function(_HK,_HL,_HM){var _HN=E(_GZ),_HO=_HN.a,_HP=_HN.b,_HQ=_HN.c,_HR=B(_uM(_oh,_HK,_HL,_HM,_HO,_HP,_HQ)),_HS=B(_tM(_oh,_HL*0-0*_HM,_HM*0-0*_HK,_HK*0-0*_HL,_HO,_HP,_HQ));return new T6(0,_DS,_DS,new T2(0,E(new T3(0,E(_HR.a),E(_HR.b),E(_HR.c))),E(_HS)),_DJ,_HI,_Dq);};if(!E(_HB.g)){var _HT=1/_HI,_HU=B(_HJ(_HH*_HT,_HG*_HT,_HF*_HT));return new T6(0,_HU.a,_HU.b,E(_HU.c),E(_HU.d),_HU.e,_HU.f);}else{var _HV=1/_HI,_HW=B(_HJ(-1*_HH*_HV,-1*_HG*_HV,-1*_HF*_HV));return new T6(0,_HW.a,_HW.b,E(_HW.c),E(_HW.d),_HW.e,_HW.f);}});return new T2(1,_HD,new T(function(){return B(_Hy(_HA.b));}));}};return B(_Hy(_FV));});return new T2(0,new T2(1,_GY,_w),new T(function(){return E(E(_FN).b);}));}}}},_HX=B(_DR(_DP,_DP,_DQ,_DO.c,_DO.d,_));return new F(function(){return _D2(_,_HX);});}else{return new F(function(){return _D2(_,new T2(0,_w,_DO));});}},_HY=new T(function(){return eval("__strict(passObject)");}),_HZ=new T(function(){return eval("__strict(refresh)");}),_I0=function(_I1,_){var _I2=__app0(E(_HZ)),_I3=__app0(E(_mw)),_I4=E(_I1),_I5=_I4.c,_I6=_I4.d,_I7=E(_I4.a),_I8=E(_I4.b);if(_I7<=_I8){if(_I7>_I8){return E(_mu);}else{if(0>=_I5){return new F(function(){return _mH(_I5,0);});}else{var _I9=E(_HY),_Ia=__app2(_I9,_I7,B(_mr(E(_I6[0]))));if(_I7!=_I8){var _Ib=function(_Ic,_){if(_I7>_Ic){return E(_mu);}else{if(_Ic>_I8){return E(_mu);}else{var _Id=_Ic-_I7|0;if(0>_Id){return new F(function(){return _mH(_I5,_Id);});}else{if(_Id>=_I5){return new F(function(){return _mH(_I5,_Id);});}else{var _Ie=__app2(_I9,_Ic,B(_mr(E(_I6[_Id]))));if(_Ic!=_I8){var _If=B(_Ib(_Ic+1|0,_));return new T2(1,_mg,_If);}else{return _mM;}}}}}},_Ig=B(_Ib(_I7+1|0,_)),_Ih=__app0(E(_mv)),_Ii=B(_DM(_I4,_));return new T(function(){return E(E(_Ii).b);});}else{var _Ij=__app0(E(_mv)),_Ik=B(_DM(_I4,_));return new T(function(){return E(E(_Ik).b);});}}}}else{var _Il=__app0(E(_mv)),_Im=B(_DM(_I4,_));return new T(function(){return E(E(_Im).b);});}},_In=new T(function(){return B(unCStr("Negative exponent"));}),_Io=new T(function(){return B(err(_In));}),_Ip=function(_Iq,_Ir,_Is){while(1){if(!(_Ir%2)){var _It=_Iq*_Iq,_Iu=quot(_Ir,2);_Iq=_It;_Ir=_Iu;continue;}else{var _Iv=E(_Ir);if(_Iv==1){return _Iq*_Is;}else{var _It=_Iq*_Iq,_Iw=_Iq*_Is;_Iq=_It;_Ir=quot(_Iv-1|0,2);_Is=_Iw;continue;}}}},_Ix=function(_Iy,_Iz){while(1){if(!(_Iz%2)){var _IA=_Iy*_Iy,_IB=quot(_Iz,2);_Iy=_IA;_Iz=_IB;continue;}else{var _IC=E(_Iz);if(_IC==1){return E(_Iy);}else{return new F(function(){return _Ip(_Iy*_Iy,quot(_IC-1|0,2),_Iy);});}}}},_ID=-0.6,_IE=new T3(0,E(_vn),E(_ID),E(_vn)),_IF=function(_IG){return E(_IE);},_IH=function(_){return new F(function(){return __jsNull();});},_II=function(_IJ){var _IK=B(A1(_IJ,_));return E(_IK);},_IL=new T(function(){return B(_II(_IH));}),_IM=function(_IN,_IO,_IP,_IQ,_IR,_IS,_IT,_IU,_IV,_IW,_IX,_IY,_IZ){var _J0=function(_J1){var _J2=E(_w6),_J3=2+_J1|0,_J4=_J3-1|0,_J5=(2+_J1)*(1+_J1),_J6=E(_wy);if(!_J6._){return _J2*0;}else{var _J7=_J6.a,_J8=_J6.b,_J9=B(A1(_IN,new T(function(){return 6.283185307179586*E(_J7)/E(_vy);}))),_Ja=B(A1(_IN,new T(function(){return 6.283185307179586*(E(_J7)+1)/E(_vy);})));if(_J9!=_Ja){if(_J3>=0){var _Jb=E(_J3);if(!_Jb){var _Jc=function(_Jd,_Je){while(1){var _Jf=B((function(_Jg,_Jh){var _Ji=E(_Jg);if(!_Ji._){return E(_Jh);}else{var _Jj=_Ji.a,_Jk=_Ji.b,_Jl=B(A1(_IN,new T(function(){return 6.283185307179586*E(_Jj)/E(_vy);}))),_Jm=B(A1(_IN,new T(function(){return 6.283185307179586*(E(_Jj)+1)/E(_vy);})));if(_Jl!=_Jm){var _Jn=_Jh+0/(_Jl-_Jm)/_J5;_Jd=_Jk;_Je=_Jn;return __continue;}else{if(_J4>=0){var _Jo=E(_J4);if(!_Jo){var _Jn=_Jh+_J3/_J5;_Jd=_Jk;_Je=_Jn;return __continue;}else{var _Jn=_Jh+_J3*B(_Ix(_Jl,_Jo))/_J5;_Jd=_Jk;_Je=_Jn;return __continue;}}else{return E(_Io);}}}})(_Jd,_Je));if(_Jf!=__continue){return _Jf;}}};return _J2*B(_Jc(_J8,0/(_J9-_Ja)/_J5));}else{var _Jp=function(_Jq,_Jr){while(1){var _Js=B((function(_Jt,_Ju){var _Jv=E(_Jt);if(!_Jv._){return E(_Ju);}else{var _Jw=_Jv.a,_Jx=_Jv.b,_Jy=B(A1(_IN,new T(function(){return 6.283185307179586*E(_Jw)/E(_vy);}))),_Jz=B(A1(_IN,new T(function(){return 6.283185307179586*(E(_Jw)+1)/E(_vy);})));if(_Jy!=_Jz){if(_Jb>=0){var _JA=_Ju+(B(_Ix(_Jy,_Jb))-B(_Ix(_Jz,_Jb)))/(_Jy-_Jz)/_J5;_Jq=_Jx;_Jr=_JA;return __continue;}else{return E(_Io);}}else{if(_J4>=0){var _JB=E(_J4);if(!_JB){var _JA=_Ju+_J3/_J5;_Jq=_Jx;_Jr=_JA;return __continue;}else{var _JA=_Ju+_J3*B(_Ix(_Jy,_JB))/_J5;_Jq=_Jx;_Jr=_JA;return __continue;}}else{return E(_Io);}}}})(_Jq,_Jr));if(_Js!=__continue){return _Js;}}};return _J2*B(_Jp(_J8,(B(_Ix(_J9,_Jb))-B(_Ix(_Ja,_Jb)))/(_J9-_Ja)/_J5));}}else{return E(_Io);}}else{if(_J4>=0){var _JC=E(_J4);if(!_JC){var _JD=function(_JE,_JF){while(1){var _JG=B((function(_JH,_JI){var _JJ=E(_JH);if(!_JJ._){return E(_JI);}else{var _JK=_JJ.a,_JL=_JJ.b,_JM=B(A1(_IN,new T(function(){return 6.283185307179586*E(_JK)/E(_vy);}))),_JN=B(A1(_IN,new T(function(){return 6.283185307179586*(E(_JK)+1)/E(_vy);})));if(_JM!=_JN){if(_J3>=0){var _JO=E(_J3);if(!_JO){var _JP=_JI+0/(_JM-_JN)/_J5;_JE=_JL;_JF=_JP;return __continue;}else{var _JP=_JI+(B(_Ix(_JM,_JO))-B(_Ix(_JN,_JO)))/(_JM-_JN)/_J5;_JE=_JL;_JF=_JP;return __continue;}}else{return E(_Io);}}else{var _JP=_JI+_J3/_J5;_JE=_JL;_JF=_JP;return __continue;}}})(_JE,_JF));if(_JG!=__continue){return _JG;}}};return _J2*B(_JD(_J8,_J3/_J5));}else{var _JQ=function(_JR,_JS){while(1){var _JT=B((function(_JU,_JV){var _JW=E(_JU);if(!_JW._){return E(_JV);}else{var _JX=_JW.a,_JY=_JW.b,_JZ=B(A1(_IN,new T(function(){return 6.283185307179586*E(_JX)/E(_vy);}))),_K0=B(A1(_IN,new T(function(){return 6.283185307179586*(E(_JX)+1)/E(_vy);})));if(_JZ!=_K0){if(_J3>=0){var _K1=E(_J3);if(!_K1){var _K2=_JV+0/(_JZ-_K0)/_J5;_JR=_JY;_JS=_K2;return __continue;}else{var _K2=_JV+(B(_Ix(_JZ,_K1))-B(_Ix(_K0,_K1)))/(_JZ-_K0)/_J5;_JR=_JY;_JS=_K2;return __continue;}}else{return E(_Io);}}else{if(_JC>=0){var _K2=_JV+_J3*B(_Ix(_JZ,_JC))/_J5;_JR=_JY;_JS=_K2;return __continue;}else{return E(_Io);}}}})(_JR,_JS));if(_JT!=__continue){return _JT;}}};return _J2*B(_JQ(_J8,_J3*B(_Ix(_J9,_JC))/_J5));}}else{return E(_Io);}}}},_K3=E(_IL),_K4=1/(B(_J0(1))*_IO);return new F(function(){return _yf(_IN,_IF,new T2(0,E(new T3(0,E(_K4),E(_K4),E(_K4))),1/(B(_J0(3))*_IO)),_IP,_IQ,_IR,_IS,_IT,_IU,_IV,_IW,_IX,_IY,_IZ,_vo,_K3,_K3,0);});},_K5=0.5,_K6=1,_K7=0,_K8=0.3,_K9=function(_Ka){return E(_K8);},_Kb=new T(function(){var _Kc=B(_IM(_K9,1.2,_K7,_K6,_K5,_K7,_K7,_K7,_K7,_K7,_K6,_K6,_K6));return {_:0,a:E(_Kc.a),b:E(_Kc.b),c:E(_Kc.c),d:E(_Kc.d),e:E(_Kc.e),f:E(_Kc.f),g:E(_Kc.g),h:_Kc.h,i:_Kc.i,j:_Kc.j};}),_Kd=0,_Ke=function(_){var _Kf=newArr(1,_ry),_=_Kf[0]=_Kb;return new T4(0,E(_Kd),E(_Kd),1,_Kf);},_Kg=new T(function(){return B(_rD(_Ke));}),_Kh=function(_Ki,_){while(1){var _Kj=E(_Ki);if(!_Kj._){return _mg;}else{var _Kk=_Kj.b,_Kl=E(_Kj.a);switch(_Kl._){case 0:var _Km=B(A1(_Kl.a,_));_Ki=B(_n(_Kk,new T2(1,_Km,_w)));continue;case 1:_Ki=B(_n(_Kk,_Kl.a));continue;default:_Ki=_Kk;continue;}}}},_Kn=function(_Ko,_Kp,_){var _Kq=E(_Ko);switch(_Kq._){case 0:var _Kr=B(A1(_Kq.a,_));return new F(function(){return _Kh(B(_n(_Kp,new T2(1,_Kr,_w))),_);});break;case 1:return new F(function(){return _Kh(B(_n(_Kp,_Kq.a)),_);});break;default:return new F(function(){return _Kh(_Kp,_);});}},_Ks=new T0(2),_Kt=function(_Ku){return new T0(2);},_Kv=function(_Kw,_Kx,_Ky){return function(_){var _Kz=E(_Kw),_KA=rMV(_Kz),_KB=E(_KA);if(!_KB._){var _KC=new T(function(){var _KD=new T(function(){return B(A1(_Ky,_mg));});return B(_n(_KB.b,new T2(1,new T2(0,_Kx,function(_KE){return E(_KD);}),_w)));}),_=wMV(_Kz,new T2(0,_KB.a,_KC));return _Ks;}else{var _KF=E(_KB.a);if(!_KF._){var _=wMV(_Kz,new T2(0,_Kx,_w));return new T(function(){return B(A1(_Ky,_mg));});}else{var _=wMV(_Kz,new T1(1,_KF.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Ky,_mg));}),new T2(1,new T(function(){return B(A2(_KF.a,_Kx,_Kt));}),_w)));}}};},_KG=new T(function(){return E(_IL);}),_KH=new T(function(){return eval("window.requestAnimationFrame");}),_KI=new T1(1,_w),_KJ=function(_KK,_KL){return function(_){var _KM=E(_KK),_KN=rMV(_KM),_KO=E(_KN);if(!_KO._){var _KP=_KO.a,_KQ=E(_KO.b);if(!_KQ._){var _=wMV(_KM,_KI);return new T(function(){return B(A1(_KL,_KP));});}else{var _KR=E(_KQ.a),_=wMV(_KM,new T2(0,_KR.a,_KQ.b));return new T1(1,new T2(1,new T(function(){return B(A1(_KL,_KP));}),new T2(1,new T(function(){return B(A1(_KR.b,_Kt));}),_w)));}}else{var _KS=new T(function(){var _KT=function(_KU){var _KV=new T(function(){return B(A1(_KL,_KU));});return function(_KW){return E(_KV);};};return B(_n(_KO.a,new T2(1,_KT,_w)));}),_=wMV(_KM,new T1(1,_KS));return _Ks;}};},_KX=function(_KY,_KZ){return new T1(0,B(_KJ(_KY,_KZ)));},_L0=function(_L1,_L2){var _L3=new T(function(){return new T1(0,B(_Kv(_L1,_mg,_Kt)));});return function(_){var _L4=__createJSFunc(2,function(_L5,_){var _L6=B(_Kn(_L3,_w,_));return _KG;}),_L7=__app1(E(_KH),_L4);return new T(function(){return B(_KX(_L1,_L2));});};},_L8=new T1(1,_w),_L9=function(_La,_Lb,_){var _Lc=function(_){var _Ld=nMV(_La),_Le=_Ld;return new T(function(){var _Lf=new T(function(){return B(_Lg(_));}),_Lh=function(_){var _Li=rMV(_Le),_Lj=B(A2(_Lb,_Li,_)),_=wMV(_Le,_Lj),_Lk=function(_){var _Ll=nMV(_L8);return new T(function(){return new T1(0,B(_L0(_Ll,function(_Lm){return E(_Lf);})));});};return new T1(0,_Lk);},_Ln=new T(function(){return new T1(0,_Lh);}),_Lg=function(_Lo){return E(_Ln);};return B(_Lg(_));});};return new F(function(){return _Kn(new T1(0,_Lc),_w,_);});},_Lp=new T(function(){return eval("__strict(setBounds)");}),_Lq=function(_){var _Lr=__app3(E(_lt),E(_lD),E(_m9),E(_ls)),_Ls=__app2(E(_Lp),E(_iI),E(_iF));return new F(function(){return _L9(_Kg,_I0,_);});},_Lt=function(_){return new F(function(){return _Lq(_);});};
var hasteMain = function() {B(A(_Lt, [0]));};window.onload = hasteMain;