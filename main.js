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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr("x"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr("y"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("z"));}),_D=new T1(0,_C),_E=new T3(0,E(_z),E(_B),E(_D)),_F=new T(function(){return B(unCStr(","));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr("Math.pow("));}),_I=new T1(0,_H),_J=new T(function(){return B(unCStr(")"));}),_K=new T1(0,_J),_L=new T2(1,_K,_w),_M=function(_N,_O){return new T1(1,new T2(1,_I,new T2(1,_N,new T2(1,_G,new T2(1,_O,_L)))));},_P=new T(function(){return B(unCStr("Math.acos("));}),_Q=new T1(0,_P),_R=function(_S){return new T1(1,new T2(1,_Q,new T2(1,_S,_L)));},_T=new T(function(){return B(unCStr("Math.acosh("));}),_U=new T1(0,_T),_V=function(_W){return new T1(1,new T2(1,_U,new T2(1,_W,_L)));},_X=new T(function(){return B(unCStr("Math.asin("));}),_Y=new T1(0,_X),_Z=function(_10){return new T1(1,new T2(1,_Y,new T2(1,_10,_L)));},_11=new T(function(){return B(unCStr("Math.asinh("));}),_12=new T1(0,_11),_13=function(_14){return new T1(1,new T2(1,_12,new T2(1,_14,_L)));},_15=new T(function(){return B(unCStr("Math.atan("));}),_16=new T1(0,_15),_17=function(_18){return new T1(1,new T2(1,_16,new T2(1,_18,_L)));},_19=new T(function(){return B(unCStr("Math.atanh("));}),_1a=new T1(0,_19),_1b=function(_1c){return new T1(1,new T2(1,_1a,new T2(1,_1c,_L)));},_1d=new T(function(){return B(unCStr("Math.cos("));}),_1e=new T1(0,_1d),_1f=function(_1g){return new T1(1,new T2(1,_1e,new T2(1,_1g,_L)));},_1h=new T(function(){return B(unCStr("Math.cosh("));}),_1i=new T1(0,_1h),_1j=function(_1k){return new T1(1,new T2(1,_1i,new T2(1,_1k,_L)));},_1l=new T(function(){return B(unCStr("Math.exp("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_L)));},_1p=new T(function(){return B(unCStr("Math.log("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_L)));},_1t=new T(function(){return B(unCStr(")/Math.log("));}),_1u=new T1(0,_1t),_1v=function(_1w,_1x){return new T1(1,new T2(1,_1q,new T2(1,_1x,new T2(1,_1u,new T2(1,_1w,_L)))));},_1y=new T(function(){return B(unCStr("Math.PI"));}),_1z=new T1(0,_1y),_1A=new T(function(){return B(unCStr("Math.sin("));}),_1B=new T1(0,_1A),_1C=function(_1D){return new T1(1,new T2(1,_1B,new T2(1,_1D,_L)));},_1E=new T(function(){return B(unCStr("Math.sinh("));}),_1F=new T1(0,_1E),_1G=function(_1H){return new T1(1,new T2(1,_1F,new T2(1,_1H,_L)));},_1I=new T(function(){return B(unCStr("Math.sqrt("));}),_1J=new T1(0,_1I),_1K=function(_1L){return new T1(1,new T2(1,_1J,new T2(1,_1L,_L)));},_1M=new T(function(){return B(unCStr("Math.tan("));}),_1N=new T1(0,_1M),_1O=function(_1P){return new T1(1,new T2(1,_1N,new T2(1,_1P,_L)));},_1Q=new T(function(){return B(unCStr("Math.tanh("));}),_1R=new T1(0,_1Q),_1S=function(_1T){return new T1(1,new T2(1,_1R,new T2(1,_1T,_L)));},_1U=new T(function(){return B(unCStr("("));}),_1V=new T1(0,_1U),_1W=new T(function(){return B(unCStr(")/("));}),_1X=new T1(0,_1W),_1Y=function(_1Z,_20){return new T1(1,new T2(1,_1V,new T2(1,_1Z,new T2(1,_1X,new T2(1,_20,_L)))));},_21=new T1(0,1),_22=function(_23,_24){var _25=E(_23);if(!_25._){var _26=_25.a,_27=E(_24);if(!_27._){var _28=_27.a;return (_26!=_28)?(_26>_28)?2:0:1;}else{var _29=I_compareInt(_27.a,_26);return (_29<=0)?(_29>=0)?1:2:0;}}else{var _2a=_25.a,_2b=E(_24);if(!_2b._){var _2c=I_compareInt(_2a,_2b.a);return (_2c>=0)?(_2c<=0)?1:2:0;}else{var _2d=I_compare(_2a,_2b.a);return (_2d>=0)?(_2d<=0)?1:2:0;}}},_2e=new T(function(){return B(unCStr("base"));}),_2f=new T(function(){return B(unCStr("GHC.Exception"));}),_2g=new T(function(){return B(unCStr("ArithException"));}),_2h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2e,_2f,_2g),_2i=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2h,_w,_w),_2j=function(_2k){return E(_2i);},_2l=function(_2m){return E(E(_2m).a);},_2n=function(_2o,_2p,_2q){var _2r=B(A1(_2o,_)),_2s=B(A1(_2p,_)),_2t=hs_eqWord64(_2r.a,_2s.a);if(!_2t){return __Z;}else{var _2u=hs_eqWord64(_2r.b,_2s.b);return (!_2u)?__Z:new T1(1,_2q);}},_2v=function(_2w){var _2x=E(_2w);return new F(function(){return _2n(B(_2l(_2x.a)),_2j,_2x.b);});},_2y=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2z=new T(function(){return B(unCStr("denormal"));}),_2A=new T(function(){return B(unCStr("divide by zero"));}),_2B=new T(function(){return B(unCStr("loss of precision"));}),_2C=new T(function(){return B(unCStr("arithmetic underflow"));}),_2D=new T(function(){return B(unCStr("arithmetic overflow"));}),_2E=function(_2F,_2G){switch(E(_2F)){case 0:return new F(function(){return _n(_2D,_2G);});break;case 1:return new F(function(){return _n(_2C,_2G);});break;case 2:return new F(function(){return _n(_2B,_2G);});break;case 3:return new F(function(){return _n(_2A,_2G);});break;case 4:return new F(function(){return _n(_2z,_2G);});break;default:return new F(function(){return _n(_2y,_2G);});}},_2H=function(_2I){return new F(function(){return _2E(_2I,_w);});},_2J=function(_2K,_2L,_2M){return new F(function(){return _2E(_2L,_2M);});},_2N=44,_2O=93,_2P=91,_2Q=function(_2R,_2S,_2T){var _2U=E(_2S);if(!_2U._){return new F(function(){return unAppCStr("[]",_2T);});}else{var _2V=new T(function(){var _2W=new T(function(){var _2X=function(_2Y){var _2Z=E(_2Y);if(!_2Z._){return E(new T2(1,_2O,_2T));}else{var _30=new T(function(){return B(A2(_2R,_2Z.a,new T(function(){return B(_2X(_2Z.b));})));});return new T2(1,_2N,_30);}};return B(_2X(_2U.b));});return B(A2(_2R,_2U.a,_2W));});return new T2(1,_2P,_2V);}},_31=function(_32,_33){return new F(function(){return _2Q(_2E,_32,_33);});},_34=new T3(0,_2J,_2H,_31),_35=new T(function(){return new T5(0,_2j,_34,_36,_2v,_2H);}),_36=function(_37){return new T2(0,_35,_37);},_38=3,_39=new T(function(){return B(_36(_38));}),_3a=new T(function(){return die(_39);}),_3b=function(_3c,_3d){var _3e=E(_3c);return (_3e._==0)?_3e.a*Math.pow(2,_3d):I_toNumber(_3e.a)*Math.pow(2,_3d);},_3f=function(_3g,_3h){var _3i=E(_3g);if(!_3i._){var _3j=_3i.a,_3k=E(_3h);return (_3k._==0)?_3j==_3k.a:(I_compareInt(_3k.a,_3j)==0)?true:false;}else{var _3l=_3i.a,_3m=E(_3h);return (_3m._==0)?(I_compareInt(_3l,_3m.a)==0)?true:false:(I_compare(_3l,_3m.a)==0)?true:false;}},_3n=function(_3o){var _3p=E(_3o);if(!_3p._){return E(_3p.a);}else{return new F(function(){return I_toInt(_3p.a);});}},_3q=function(_3r,_3s){while(1){var _3t=E(_3r);if(!_3t._){var _3u=_3t.a,_3v=E(_3s);if(!_3v._){var _3w=_3v.a,_3x=addC(_3u,_3w);if(!E(_3x.b)){return new T1(0,_3x.a);}else{_3r=new T1(1,I_fromInt(_3u));_3s=new T1(1,I_fromInt(_3w));continue;}}else{_3r=new T1(1,I_fromInt(_3u));_3s=_3v;continue;}}else{var _3y=E(_3s);if(!_3y._){_3r=_3t;_3s=new T1(1,I_fromInt(_3y.a));continue;}else{return new T1(1,I_add(_3t.a,_3y.a));}}}},_3z=function(_3A,_3B){while(1){var _3C=E(_3A);if(!_3C._){var _3D=E(_3C.a);if(_3D==(-2147483648)){_3A=new T1(1,I_fromInt(-2147483648));continue;}else{var _3E=E(_3B);if(!_3E._){var _3F=_3E.a;return new T2(0,new T1(0,quot(_3D,_3F)),new T1(0,_3D%_3F));}else{_3A=new T1(1,I_fromInt(_3D));_3B=_3E;continue;}}}else{var _3G=E(_3B);if(!_3G._){_3A=_3C;_3B=new T1(1,I_fromInt(_3G.a));continue;}else{var _3H=I_quotRem(_3C.a,_3G.a);return new T2(0,new T1(1,_3H.a),new T1(1,_3H.b));}}}},_3I=new T1(0,0),_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P,_3Q){if(!B(_3f(_3Q,_3I))){var _3R=B(_3z(_3P,_3Q)),_3S=_3R.a;switch(B(_22(B(_3J(_3R.b,1)),_3Q))){case 0:return new F(function(){return _3b(_3S,_3O);});break;case 1:if(!(B(_3n(_3S))&1)){return new F(function(){return _3b(_3S,_3O);});}else{return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}break;default:return new F(function(){return _3b(B(_3q(_3S,_21)),_3O);});}}else{return E(_3a);}},_3T=function(_3U,_3V){var _3W=E(_3U);if(!_3W._){var _3X=_3W.a,_3Y=E(_3V);return (_3Y._==0)?_3X>_3Y.a:I_compareInt(_3Y.a,_3X)<0;}else{var _3Z=_3W.a,_40=E(_3V);return (_40._==0)?I_compareInt(_3Z,_40.a)>0:I_compare(_3Z,_40.a)>0;}},_41=new T1(0,1),_42=function(_43,_44){var _45=E(_43);if(!_45._){var _46=_45.a,_47=E(_44);return (_47._==0)?_46<_47.a:I_compareInt(_47.a,_46)>0;}else{var _48=_45.a,_49=E(_44);return (_49._==0)?I_compareInt(_48,_49.a)<0:I_compare(_48,_49.a)<0;}},_4a=new T(function(){return B(unCStr("base"));}),_4b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4c=new T(function(){return B(unCStr("PatternMatchFail"));}),_4d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4a,_4b,_4c),_4e=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4d,_w,_w),_4f=function(_4g){return E(_4e);},_4h=function(_4i){var _4j=E(_4i);return new F(function(){return _2n(B(_2l(_4j.a)),_4f,_4j.b);});},_4k=function(_4l){return E(E(_4l).a);},_4m=function(_4n){return new T2(0,_4o,_4n);},_4p=function(_4q,_4r){return new F(function(){return _n(E(_4q).a,_4r);});},_4s=function(_4t,_4u){return new F(function(){return _2Q(_4p,_4t,_4u);});},_4v=function(_4w,_4x,_4y){return new F(function(){return _n(E(_4x).a,_4y);});},_4z=new T3(0,_4v,_4k,_4s),_4o=new T(function(){return new T5(0,_4f,_4z,_4m,_4h,_4k);}),_4A=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4B=function(_4C){return E(E(_4C).c);},_4D=function(_4E,_4F){return new F(function(){return die(new T(function(){return B(A2(_4B,_4F,_4E));}));});},_4G=function(_4H,_37){return new F(function(){return _4D(_4H,_37);});},_4I=function(_4J,_4K){var _4L=E(_4K);if(!_4L._){return new T2(0,_w,_w);}else{var _4M=_4L.a;if(!B(A1(_4J,_4M))){return new T2(0,_w,_4L);}else{var _4N=new T(function(){var _4O=B(_4I(_4J,_4L.b));return new T2(0,_4O.a,_4O.b);});return new T2(0,new T2(1,_4M,new T(function(){return E(E(_4N).a);})),new T(function(){return E(E(_4N).b);}));}}},_4P=32,_4Q=new T(function(){return B(unCStr("\n"));}),_4R=function(_4S){return (E(_4S)==124)?false:true;},_4T=function(_4U,_4V){var _4W=B(_4I(_4R,B(unCStr(_4U)))),_4X=_4W.a,_4Y=function(_4Z,_50){var _51=new T(function(){var _52=new T(function(){return B(_n(_4V,new T(function(){return B(_n(_50,_4Q));},1)));});return B(unAppCStr(": ",_52));},1);return new F(function(){return _n(_4Z,_51);});},_53=E(_4W.b);if(!_53._){return new F(function(){return _4Y(_4X,_w);});}else{if(E(_53.a)==124){return new F(function(){return _4Y(_4X,new T2(1,_4P,_53.b));});}else{return new F(function(){return _4Y(_4X,_w);});}}},_54=function(_55){return new F(function(){return _4G(new T1(0,new T(function(){return B(_4T(_55,_4A));})),_4o);});},_56=function(_57){var _58=function(_59,_5a){while(1){if(!B(_42(_59,_57))){if(!B(_3T(_59,_57))){if(!B(_3f(_59,_57))){return new F(function(){return _54("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_5a);}}else{return _5a-1|0;}}else{var _5b=B(_3J(_59,1)),_5c=_5a+1|0;_59=_5b;_5a=_5c;continue;}}};return new F(function(){return _58(_41,0);});},_5d=function(_5e){var _5f=E(_5e);if(!_5f._){var _5g=_5f.a>>>0;if(!_5g){return -1;}else{var _5h=function(_5i,_5j){while(1){if(_5i>=_5g){if(_5i<=_5g){if(_5i!=_5g){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5j);}}else{return _5j-1|0;}}else{var _5k=imul(_5i,2)>>>0,_5l=_5j+1|0;_5i=_5k;_5j=_5l;continue;}}};return new F(function(){return _5h(1,0);});}}else{return new F(function(){return _56(_5f);});}},_5m=function(_5n){var _5o=E(_5n);if(!_5o._){var _5p=_5o.a>>>0;if(!_5p){return new T2(0,-1,0);}else{var _5q=function(_5r,_5s){while(1){if(_5r>=_5p){if(_5r<=_5p){if(_5r!=_5p){return new F(function(){return _54("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5s);}}else{return _5s-1|0;}}else{var _5t=imul(_5r,2)>>>0,_5u=_5s+1|0;_5r=_5t;_5s=_5u;continue;}}};return new T2(0,B(_5q(1,0)),(_5p&_5p-1>>>0)>>>0&4294967295);}}else{var _5v=_5o.a;return new T2(0,B(_5d(_5o)),I_compareInt(I_and(_5v,I_sub(_5v,I_fromInt(1))),0));}},_5w=function(_5x,_5y){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);return (_5B._==0)?_5A<=_5B.a:I_compareInt(_5B.a,_5A)>=0;}else{var _5C=_5z.a,_5D=E(_5y);return (_5D._==0)?I_compareInt(_5C,_5D.a)<=0:I_compare(_5C,_5D.a)<=0;}},_5E=function(_5F,_5G){while(1){var _5H=E(_5F);if(!_5H._){var _5I=_5H.a,_5J=E(_5G);if(!_5J._){return new T1(0,(_5I>>>0&_5J.a>>>0)>>>0&4294967295);}else{_5F=new T1(1,I_fromInt(_5I));_5G=_5J;continue;}}else{var _5K=E(_5G);if(!_5K._){_5F=_5H;_5G=new T1(1,I_fromInt(_5K.a));continue;}else{return new T1(1,I_and(_5H.a,_5K.a));}}}},_5L=function(_5M,_5N){while(1){var _5O=E(_5M);if(!_5O._){var _5P=_5O.a,_5Q=E(_5N);if(!_5Q._){var _5R=_5Q.a,_5S=subC(_5P,_5R);if(!E(_5S.b)){return new T1(0,_5S.a);}else{_5M=new T1(1,I_fromInt(_5P));_5N=new T1(1,I_fromInt(_5R));continue;}}else{_5M=new T1(1,I_fromInt(_5P));_5N=_5Q;continue;}}else{var _5T=E(_5N);if(!_5T._){_5M=_5O;_5N=new T1(1,I_fromInt(_5T.a));continue;}else{return new T1(1,I_sub(_5O.a,_5T.a));}}}},_5U=new T1(0,2),_5V=function(_5W,_5X){var _5Y=E(_5W);if(!_5Y._){var _5Z=(_5Y.a>>>0&(2<<_5X>>>0)-1>>>0)>>>0,_60=1<<_5X>>>0;return (_60<=_5Z)?(_60>=_5Z)?1:2:0;}else{var _61=B(_5E(_5Y,B(_5L(B(_3J(_5U,_5X)),_41)))),_62=B(_3J(_41,_5X));return (!B(_3T(_62,_61)))?(!B(_42(_62,_61)))?1:2:0;}},_63=function(_64,_65){while(1){var _66=E(_64);if(!_66._){_64=new T1(1,I_fromInt(_66.a));continue;}else{return new T1(1,I_shiftRight(_66.a,_65));}}},_67=function(_68,_69,_6a,_6b){var _6c=B(_5m(_6b)),_6d=_6c.a;if(!E(_6c.b)){var _6e=B(_5d(_6a));if(_6e<((_6d+_68|0)-1|0)){var _6f=_6d+(_68-_69|0)|0;if(_6f>0){if(_6f>_6e){if(_6f<=(_6e+1|0)){if(!E(B(_5m(_6a)).b)){return 0;}else{return new F(function(){return _3b(_21,_68-_69|0);});}}else{return 0;}}else{var _6g=B(_63(_6a,_6f));switch(B(_5V(_6a,_6f-1|0))){case 0:return new F(function(){return _3b(_6g,_68-_69|0);});break;case 1:if(!(B(_3n(_6g))&1)){return new F(function(){return _3b(_6g,_68-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}break;default:return new F(function(){return _3b(B(_3q(_6g,_21)),_68-_69|0);});}}}else{return new F(function(){return _3b(_6a,(_68-_69|0)-_6f|0);});}}else{if(_6e>=_69){var _6h=B(_63(_6a,(_6e+1|0)-_69|0));switch(B(_5V(_6a,_6e-_69|0))){case 0:return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});break;case 2:return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});break;default:if(!(B(_3n(_6h))&1)){return new F(function(){return _3b(_6h,((_6e-_6d|0)+1|0)-_69|0);});}else{return new F(function(){return _3b(B(_3q(_6h,_21)),((_6e-_6d|0)+1|0)-_69|0);});}}}else{return new F(function(){return _3b(_6a, -_6d);});}}}else{var _6i=B(_5d(_6a))-_6d|0,_6j=function(_6k){var _6l=function(_6m,_6n){if(!B(_5w(B(_3J(_6n,_69)),_6m))){return new F(function(){return _3N(_6k-_69|0,_6m,_6n);});}else{return new F(function(){return _3N((_6k-_69|0)+1|0,_6m,B(_3J(_6n,1)));});}};if(_6k>=_69){if(_6k!=_69){return new F(function(){return _6l(_6a,new T(function(){return B(_3J(_6b,_6k-_69|0));}));});}else{return new F(function(){return _6l(_6a,_6b);});}}else{return new F(function(){return _6l(new T(function(){return B(_3J(_6a,_69-_6k|0));}),_6b);});}};if(_68>_6i){return new F(function(){return _6j(_68);});}else{return new F(function(){return _6j(_6i);});}}},_6o=new T1(0,2147483647),_6p=new T(function(){return B(_3q(_6o,_41));}),_6q=function(_6r){var _6s=E(_6r);if(!_6s._){var _6t=E(_6s.a);return (_6t==(-2147483648))?E(_6p):new T1(0, -_6t);}else{return new T1(1,I_negate(_6s.a));}},_6u=new T(function(){return 0/0;}),_6v=new T(function(){return -1/0;}),_6w=new T(function(){return 1/0;}),_6x=0,_6y=function(_6z,_6A){if(!B(_3f(_6A,_3I))){if(!B(_3f(_6z,_3I))){if(!B(_42(_6z,_3I))){return new F(function(){return _67(-1021,53,_6z,_6A);});}else{return  -B(_67(-1021,53,B(_6q(_6z)),_6A));}}else{return E(_6x);}}else{return (!B(_3f(_6z,_3I)))?(!B(_42(_6z,_3I)))?E(_6w):E(_6v):E(_6u);}},_6B=function(_6C){return new T1(0,new T(function(){var _6D=E(_6C),_6E=jsShow(B(_6y(_6D.a,_6D.b)));return fromJSStr(_6E);}));},_6F=new T(function(){return B(unCStr("1/("));}),_6G=new T1(0,_6F),_6H=function(_6I){return new T1(1,new T2(1,_6G,new T2(1,_6I,_L)));},_6J=new T(function(){return B(unCStr(")+("));}),_6K=new T1(0,_6J),_6L=function(_6M,_6N){return new T1(1,new T2(1,_1V,new T2(1,_6M,new T2(1,_6K,new T2(1,_6N,_L)))));},_6O=new T(function(){return B(unCStr("-("));}),_6P=new T1(0,_6O),_6Q=function(_6R){return new T1(1,new T2(1,_6P,new T2(1,_6R,_L)));},_6S=new T(function(){return B(unCStr(")*("));}),_6T=new T1(0,_6S),_6U=function(_6V,_6W){return new T1(1,new T2(1,_1V,new T2(1,_6V,new T2(1,_6T,new T2(1,_6W,_L)))));},_6X=function(_6Y){return E(E(_6Y).a);},_6Z=function(_70){return E(E(_70).d);},_71=function(_72,_73){return new F(function(){return A3(_6X,_74,_72,new T(function(){return B(A2(_6Z,_74,_73));}));});},_75=new T(function(){return B(unCStr("Math.abs("));}),_76=new T1(0,_75),_77=function(_78){return new T1(1,new T2(1,_76,new T2(1,_78,_L)));},_79=function(_7a){while(1){var _7b=E(_7a);if(!_7b._){_7a=new T1(1,I_fromInt(_7b.a));continue;}else{return new F(function(){return I_toString(_7b.a);});}}},_7c=function(_7d,_7e){return new F(function(){return _n(fromJSStr(B(_79(_7d))),_7e);});},_7f=41,_7g=40,_7h=new T1(0,0),_7i=function(_7j,_7k,_7l){if(_7j<=6){return new F(function(){return _7c(_7k,_7l);});}else{if(!B(_42(_7k,_7h))){return new F(function(){return _7c(_7k,_7l);});}else{return new T2(1,_7g,new T(function(){return B(_n(fromJSStr(B(_79(_7k))),new T2(1,_7f,_7l)));}));}}},_7m=new T(function(){return B(unCStr("."));}),_7n=function(_7o){return new T1(0,new T(function(){return B(_n(B(_7i(0,_7o,_w)),_7m));}));},_7p=new T(function(){return B(unCStr("Math.sign("));}),_7q=new T1(0,_7p),_7r=function(_7s){return new T1(1,new T2(1,_7q,new T2(1,_7s,_L)));},_74=new T(function(){return {_:0,a:_6L,b:_71,c:_6U,d:_6Q,e:_77,f:_7r,g:_7n};}),_7t=new T4(0,_74,_1Y,_6H,_6B),_7u={_:0,a:_7t,b:_1z,c:_1n,d:_1r,e:_1K,f:_M,g:_1v,h:_1C,i:_1f,j:_1O,k:_Z,l:_R,m:_17,n:_1G,o:_1j,p:_1S,q:_13,r:_V,s:_1b},_7v=new T(function(){return B(unCStr("(/=) is not defined"));}),_7w=new T(function(){return B(err(_7v));}),_7x=new T(function(){return B(unCStr("(==) is not defined"));}),_7y=new T(function(){return B(err(_7x));}),_7z=new T2(0,_7y,_7w),_7A=new T(function(){return B(unCStr("(<) is not defined"));}),_7B=new T(function(){return B(err(_7A));}),_7C=new T(function(){return B(unCStr("(<=) is not defined"));}),_7D=new T(function(){return B(err(_7C));}),_7E=new T(function(){return B(unCStr("(>) is not defined"));}),_7F=new T(function(){return B(err(_7E));}),_7G=new T(function(){return B(unCStr("(>=) is not defined"));}),_7H=new T(function(){return B(err(_7G));}),_7I=new T(function(){return B(unCStr("compare is not defined"));}),_7J=new T(function(){return B(err(_7I));}),_7K=new T(function(){return B(unCStr("Math.max("));}),_7L=new T1(0,_7K),_7M=function(_7N,_7O){return new T1(1,new T2(1,_7L,new T2(1,_7N,new T2(1,_G,new T2(1,_7O,_L)))));},_7P=new T(function(){return B(unCStr("Math.min("));}),_7Q=new T1(0,_7P),_7R=function(_7S,_7T){return new T1(1,new T2(1,_7Q,new T2(1,_7S,new T2(1,_G,new T2(1,_7T,_L)))));},_7U={_:0,a:_7z,b:_7J,c:_7B,d:_7D,e:_7F,f:_7H,g:_7M,h:_7R},_7V=new T2(0,_7u,_7U),_7W=function(_7X,_7Y){var _7Z=E(_7X);return E(_7Y);},_80=function(_81,_82){var _83=E(_82);return E(_81);},_84=function(_85,_86){var _87=E(_85),_88=E(_86);return new T3(0,E(B(A1(_87.a,_88.a))),E(B(A1(_87.b,_88.b))),E(B(A1(_87.c,_88.c))));},_89=function(_8a,_8b,_8c){return new T3(0,E(_8a),E(_8b),E(_8c));},_8d=function(_8e){return new F(function(){return _89(_8e,_8e,_8e);});},_8f=function(_8g,_8h){var _8i=E(_8h),_8j=E(_8g);return new T3(0,E(_8j),E(_8j),E(_8j));},_8k=function(_8l,_8m){var _8n=E(_8m);return new T3(0,E(B(A1(_8l,_8n.a))),E(B(A1(_8l,_8n.b))),E(B(A1(_8l,_8n.c))));},_8o=new T2(0,_8k,_8f),_8p=new T5(0,_8o,_8d,_84,_7W,_80),_8q=new T1(0,0),_8r=new T1(0,1),_8s=function(_8t){return E(E(_8t).g);},_8u=function(_8v){var _8w=B(A2(_8s,_8v,_8r)),_8x=B(A2(_8s,_8v,_8q));return new T3(0,E(new T3(0,E(_8w),E(_8x),E(_8x))),E(new T3(0,E(_8x),E(_8w),E(_8x))),E(new T3(0,E(_8x),E(_8x),E(_8w))));},_8y=new T(function(){return B(unCStr("(/=) is not defined"));}),_8z=new T(function(){return B(err(_8y));}),_8A=new T(function(){return B(unCStr("(==) is not defined"));}),_8B=new T(function(){return B(err(_8A));}),_8C=new T2(0,_8B,_8z),_8D=function(_8E){return E(_8C);},_8F=function(_8G){return E(E(_8G).a);},_8H=function(_8I){return E(E(_8I).a);},_8J=function(_8K){return E(E(_8K).a);},_8L=function(_8M){return E(E(_8M).c);},_8N=function(_8O){return E(E(_8O).f);},_8P=function(_8Q){return E(E(_8Q).b);},_8R=function(_8S){return E(E(_8S).c);},_8T=function(_8U){return E(E(_8U).a);},_8V=function(_8W){return E(E(_8W).d);},_8X=function(_8Y,_8Z,_90,_91,_92){var _93=new T(function(){return E(E(E(_8Y).c).a);}),_94=new T(function(){var _95=E(_8Y).a,_96=new T(function(){var _97=new T(function(){return B(_8H(_93));}),_98=new T(function(){return B(_8J(_97));}),_99=new T(function(){return B(A2(_8V,_93,_8Z));}),_9a=new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_9b=function(_9c,_9d){var _9e=new T(function(){var _9f=new T(function(){return B(A3(_8P,_97,new T(function(){return B(A3(_8L,_98,_91,_9c));}),_8Z));});return B(A3(_6X,_98,_9f,new T(function(){return B(A3(_8L,_98,_9d,_99));})));});return new F(function(){return A3(_8L,_98,_9a,_9e);});};return B(A3(_8T,B(_8F(_95)),_9b,_90));});return B(A3(_8R,_95,_96,_92));});return new T2(0,new T(function(){return B(A3(_8N,_93,_8Z,_91));}),_94);},_9g=function(_9h,_9i,_9j,_9k){var _9l=E(_9j),_9m=E(_9k),_9n=B(_8X(_9i,_9l.a,_9l.b,_9m.a,_9m.b));return new T2(0,_9n.a,_9n.b);},_9o=new T1(0,1),_9p=function(_9q){return E(E(_9q).b);},_9r=function(_9s){return E(E(_9s).l);},_9t=function(_9u){return E(E(_9u).e);},_9v=function(_9w,_9x,_9y){var _9z=new T(function(){return E(E(E(_9w).c).a);}),_9A=new T(function(){var _9B=new T(function(){return B(_8H(_9z));}),_9C=new T(function(){var _9D=B(_8J(_9B)),_9E=new T(function(){var _9F=new T(function(){return B(A3(_9p,_9D,new T(function(){return B(A2(_8s,_9D,_9o));}),new T(function(){return B(A3(_8L,_9D,_9x,_9x));})));});return B(A2(_9t,_9z,_9F));});return B(A2(_6Z,_9D,_9E));});return B(A3(_8T,B(_8F(E(_9w).a)),function(_9G){return new F(function(){return A3(_8P,_9B,_9G,_9C);});},_9y));});return new T2(0,new T(function(){return B(A2(_9r,_9z,_9x));}),_9A);},_9H=function(_9I,_9J,_9K){var _9L=E(_9K),_9M=B(_9v(_9J,_9L.a,_9L.b));return new T2(0,_9M.a,_9M.b);},_9N=function(_9O){return E(E(_9O).r);},_9P=function(_9Q,_9R,_9S){var _9T=new T(function(){return E(E(E(_9Q).c).a);}),_9U=new T(function(){var _9V=new T(function(){return B(_8H(_9T));}),_9W=new T(function(){var _9X=new T(function(){var _9Y=B(_8J(_9V));return B(A3(_9p,_9Y,new T(function(){return B(A3(_8L,_9Y,_9R,_9R));}),new T(function(){return B(A2(_8s,_9Y,_9o));})));});return B(A2(_9t,_9T,_9X));});return B(A3(_8T,B(_8F(E(_9Q).a)),function(_9Z){return new F(function(){return A3(_8P,_9V,_9Z,_9W);});},_9S));});return new T2(0,new T(function(){return B(A2(_9N,_9T,_9R));}),_9U);},_a0=function(_a1,_a2,_a3){var _a4=E(_a3),_a5=B(_9P(_a2,_a4.a,_a4.b));return new T2(0,_a5.a,_a5.b);},_a6=function(_a7){return E(E(_a7).k);},_a8=function(_a9,_aa,_ab){var _ac=new T(function(){return E(E(E(_a9).c).a);}),_ad=new T(function(){var _ae=new T(function(){return B(_8H(_ac));}),_af=new T(function(){var _ag=new T(function(){var _ah=B(_8J(_ae));return B(A3(_9p,_ah,new T(function(){return B(A2(_8s,_ah,_9o));}),new T(function(){return B(A3(_8L,_ah,_aa,_aa));})));});return B(A2(_9t,_ac,_ag));});return B(A3(_8T,B(_8F(E(_a9).a)),function(_ai){return new F(function(){return A3(_8P,_ae,_ai,_af);});},_ab));});return new T2(0,new T(function(){return B(A2(_a6,_ac,_aa));}),_ad);},_aj=function(_ak,_al,_am){var _an=E(_am),_ao=B(_a8(_al,_an.a,_an.b));return new T2(0,_ao.a,_ao.b);},_ap=function(_aq){return E(E(_aq).q);},_ar=function(_as,_at,_au){var _av=new T(function(){return E(E(E(_as).c).a);}),_aw=new T(function(){var _ax=new T(function(){return B(_8H(_av));}),_ay=new T(function(){var _az=new T(function(){var _aA=B(_8J(_ax));return B(A3(_6X,_aA,new T(function(){return B(A3(_8L,_aA,_at,_at));}),new T(function(){return B(A2(_8s,_aA,_9o));})));});return B(A2(_9t,_av,_az));});return B(A3(_8T,B(_8F(E(_as).a)),function(_aB){return new F(function(){return A3(_8P,_ax,_aB,_ay);});},_au));});return new T2(0,new T(function(){return B(A2(_ap,_av,_at));}),_aw);},_aC=function(_aD,_aE,_aF){var _aG=E(_aF),_aH=B(_ar(_aE,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=function(_aJ){return E(E(_aJ).m);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8H(_aO));}),_aR=new T(function(){var _aS=B(_8J(_aQ));return B(A3(_6X,_aS,new T(function(){return B(A2(_8s,_aS,_9o));}),new T(function(){return B(A3(_8L,_aS,_aM,_aM));})));});return B(A3(_8T,B(_8F(E(_aL).a)),function(_aT){return new F(function(){return A3(_8P,_aQ,_aT,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aU=function(_aV,_aW,_aX){var _aY=E(_aX),_aZ=B(_aK(_aW,_aY.a,_aY.b));return new T2(0,_aZ.a,_aZ.b);},_b0=function(_b1){return E(E(_b1).s);},_b2=function(_b3,_b4,_b5){var _b6=new T(function(){return E(E(E(_b3).c).a);}),_b7=new T(function(){var _b8=new T(function(){return B(_8H(_b6));}),_b9=new T(function(){var _ba=B(_8J(_b8));return B(A3(_9p,_ba,new T(function(){return B(A2(_8s,_ba,_9o));}),new T(function(){return B(A3(_8L,_ba,_b4,_b4));})));});return B(A3(_8T,B(_8F(E(_b3).a)),function(_bb){return new F(function(){return A3(_8P,_b8,_bb,_b9);});},_b5));});return new T2(0,new T(function(){return B(A2(_b0,_b6,_b4));}),_b7);},_bc=function(_bd,_be,_bf){var _bg=E(_bf),_bh=B(_b2(_be,_bg.a,_bg.b));return new T2(0,_bh.a,_bh.b);},_bi=function(_bj){return E(E(_bj).i);},_bk=function(_bl){return E(E(_bl).h);},_bm=function(_bn,_bo,_bp){var _bq=new T(function(){return E(E(E(_bn).c).a);}),_br=new T(function(){var _bs=new T(function(){return B(_8J(new T(function(){return B(_8H(_bq));})));}),_bt=new T(function(){return B(A2(_6Z,_bs,new T(function(){return B(A2(_bk,_bq,_bo));})));});return B(A3(_8T,B(_8F(E(_bn).a)),function(_bu){return new F(function(){return A3(_8L,_bs,_bu,_bt);});},_bp));});return new T2(0,new T(function(){return B(A2(_bi,_bq,_bo));}),_br);},_bv=function(_bw,_bx,_by){var _bz=E(_by),_bA=B(_bm(_bx,_bz.a,_bz.b));return new T2(0,_bA.a,_bA.b);},_bB=function(_bC){return E(E(_bC).o);},_bD=function(_bE){return E(E(_bE).n);},_bF=function(_bG,_bH,_bI){var _bJ=new T(function(){return E(E(E(_bG).c).a);}),_bK=new T(function(){var _bL=new T(function(){return B(_8J(new T(function(){return B(_8H(_bJ));})));}),_bM=new T(function(){return B(A2(_bD,_bJ,_bH));});return B(A3(_8T,B(_8F(E(_bG).a)),function(_bN){return new F(function(){return A3(_8L,_bL,_bN,_bM);});},_bI));});return new T2(0,new T(function(){return B(A2(_bB,_bJ,_bH));}),_bK);},_bO=function(_bP,_bQ,_bR){var _bS=E(_bR),_bT=B(_bF(_bQ,_bS.a,_bS.b));return new T2(0,_bT.a,_bT.b);},_bU=function(_bV){return E(E(_bV).c);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_8J(new T(function(){return B(_8H(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_8T,B(_8F(E(_bX).a)),function(_c4){return new F(function(){return A3(_8L,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bU,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8H(_cf));}),_ci=new T(function(){return B(_8J(_ch));}),_cj=new T(function(){return B(A3(_8P,_ch,new T(function(){return B(A2(_8s,_ci,_9o));}),_cd));});return B(A3(_8T,B(_8F(E(_cc).a)),function(_ck){return new F(function(){return A3(_8L,_ci,_ck,_cj);});},_ce));});return new T2(0,new T(function(){return B(A2(_8V,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs,_ct,_cu,_cv){var _cw=new T(function(){return E(E(_ct).c);}),_cx=new T3(0,new T(function(){return E(E(_ct).a);}),new T(function(){return E(E(_ct).b);}),new T2(0,new T(function(){return E(E(_cw).a);}),new T(function(){return E(E(_cw).b);})));return new F(function(){return A3(_8P,_cs,new T(function(){var _cy=E(_cv),_cz=B(_cb(_cx,_cy.a,_cy.b));return new T2(0,_cz.a,_cz.b);}),new T(function(){var _cA=E(_cu),_cB=B(_cb(_cx,_cA.a,_cA.b));return new T2(0,_cB.a,_cB.b);}));});},_cC=new T1(0,0),_cD=function(_cE){return E(E(_cE).b);},_cF=function(_cG){return E(E(_cG).b);},_cH=function(_cI){var _cJ=new T(function(){return E(E(E(_cI).c).a);}),_cK=new T(function(){return B(A2(_cF,E(_cI).a,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_cJ)))),_cC));})));});return new T2(0,new T(function(){return B(_cD(_cJ));}),_cK);},_cL=function(_cM,_cN){var _cO=B(_cH(_cN));return new T2(0,_cO.a,_cO.b);},_cP=function(_cQ,_cR,_cS){var _cT=new T(function(){return E(E(E(_cQ).c).a);}),_cU=new T(function(){var _cV=new T(function(){return B(_8J(new T(function(){return B(_8H(_cT));})));}),_cW=new T(function(){return B(A2(_bi,_cT,_cR));});return B(A3(_8T,B(_8F(E(_cQ).a)),function(_cX){return new F(function(){return A3(_8L,_cV,_cX,_cW);});},_cS));});return new T2(0,new T(function(){return B(A2(_bk,_cT,_cR));}),_cU);},_cY=function(_cZ,_d0,_d1){var _d2=E(_d1),_d3=B(_cP(_d0,_d2.a,_d2.b));return new T2(0,_d3.a,_d3.b);},_d4=function(_d5,_d6,_d7){var _d8=new T(function(){return E(E(E(_d5).c).a);}),_d9=new T(function(){var _da=new T(function(){return B(_8J(new T(function(){return B(_8H(_d8));})));}),_db=new T(function(){return B(A2(_bB,_d8,_d6));});return B(A3(_8T,B(_8F(E(_d5).a)),function(_dc){return new F(function(){return A3(_8L,_da,_dc,_db);});},_d7));});return new T2(0,new T(function(){return B(A2(_bD,_d8,_d6));}),_d9);},_dd=function(_de,_df,_dg){var _dh=E(_dg),_di=B(_d4(_df,_dh.a,_dh.b));return new T2(0,_di.a,_di.b);},_dj=new T1(0,2),_dk=function(_dl,_dm,_dn){var _do=new T(function(){return E(E(E(_dl).c).a);}),_dp=new T(function(){var _dq=new T(function(){return B(_8H(_do));}),_dr=new T(function(){return B(_8J(_dq));}),_ds=new T(function(){var _dt=new T(function(){return B(A3(_8P,_dq,new T(function(){return B(A2(_8s,_dr,_9o));}),new T(function(){return B(A2(_8s,_dr,_dj));})));});return B(A3(_8P,_dq,_dt,new T(function(){return B(A2(_9t,_do,_dm));})));});return B(A3(_8T,B(_8F(E(_dl).a)),function(_du){return new F(function(){return A3(_8L,_dr,_du,_ds);});},_dn));});return new T2(0,new T(function(){return B(A2(_9t,_do,_dm));}),_dp);},_dv=function(_dw,_dx,_dy){var _dz=E(_dy),_dA=B(_dk(_dx,_dz.a,_dz.b));return new T2(0,_dA.a,_dA.b);},_dB=function(_dC){return E(E(_dC).j);},_dD=function(_dE,_dF,_dG){var _dH=new T(function(){return E(E(E(_dE).c).a);}),_dI=new T(function(){var _dJ=new T(function(){return B(_8H(_dH));}),_dK=new T(function(){var _dL=new T(function(){return B(A2(_bi,_dH,_dF));});return B(A3(_8L,B(_8J(_dJ)),_dL,_dL));});return B(A3(_8T,B(_8F(E(_dE).a)),function(_dM){return new F(function(){return A3(_8P,_dJ,_dM,_dK);});},_dG));});return new T2(0,new T(function(){return B(A2(_dB,_dH,_dF));}),_dI);},_dN=function(_dO,_dP,_dQ){var _dR=E(_dQ),_dS=B(_dD(_dP,_dR.a,_dR.b));return new T2(0,_dS.a,_dS.b);},_dT=function(_dU){return E(E(_dU).p);},_dV=function(_dW,_dX,_dY){var _dZ=new T(function(){return E(E(E(_dW).c).a);}),_e0=new T(function(){var _e1=new T(function(){return B(_8H(_dZ));}),_e2=new T(function(){var _e3=new T(function(){return B(A2(_bB,_dZ,_dX));});return B(A3(_8L,B(_8J(_e1)),_e3,_e3));});return B(A3(_8T,B(_8F(E(_dW).a)),function(_e4){return new F(function(){return A3(_8P,_e1,_e4,_e2);});},_dY));});return new T2(0,new T(function(){return B(A2(_dT,_dZ,_dX));}),_e0);},_e5=function(_e6,_e7,_e8){var _e9=E(_e8),_ea=B(_dV(_e7,_e9.a,_e9.b));return new T2(0,_ea.a,_ea.b);},_eb=function(_ec,_ed){return {_:0,a:_ec,b:new T(function(){return B(_cL(_ec,_ed));}),c:function(_ee){return new F(function(){return _c5(_ec,_ed,_ee);});},d:function(_ee){return new F(function(){return _cl(_ec,_ed,_ee);});},e:function(_ee){return new F(function(){return _dv(_ec,_ed,_ee);});},f:function(_ef,_ee){return new F(function(){return _9g(_ec,_ed,_ef,_ee);});},g:function(_ef,_ee){return new F(function(){return _cr(_ec,_ed,_ef,_ee);});},h:function(_ee){return new F(function(){return _cY(_ec,_ed,_ee);});},i:function(_ee){return new F(function(){return _bv(_ec,_ed,_ee);});},j:function(_ee){return new F(function(){return _dN(_ec,_ed,_ee);});},k:function(_ee){return new F(function(){return _aj(_ec,_ed,_ee);});},l:function(_ee){return new F(function(){return _9H(_ec,_ed,_ee);});},m:function(_ee){return new F(function(){return _aU(_ec,_ed,_ee);});},n:function(_ee){return new F(function(){return _dd(_ec,_ed,_ee);});},o:function(_ee){return new F(function(){return _bO(_ec,_ed,_ee);});},p:function(_ee){return new F(function(){return _e5(_ec,_ed,_ee);});},q:function(_ee){return new F(function(){return _aC(_ec,_ed,_ee);});},r:function(_ee){return new F(function(){return _a0(_ec,_ed,_ee);});},s:function(_ee){return new F(function(){return _bc(_ec,_ed,_ee);});}};},_eg=function(_eh,_ei,_ej,_ek,_el){var _em=new T(function(){return B(_8H(new T(function(){return E(E(E(_eh).c).a);})));}),_en=new T(function(){var _eo=E(_eh).a,_ep=new T(function(){var _eq=new T(function(){return B(_8J(_em));}),_er=new T(function(){return B(A3(_8L,_eq,_ek,_ek));}),_es=function(_et,_eu){var _ev=new T(function(){return B(A3(_9p,_eq,new T(function(){return B(A3(_8L,_eq,_et,_ek));}),new T(function(){return B(A3(_8L,_eq,_ei,_eu));})));});return new F(function(){return A3(_8P,_em,_ev,_er);});};return B(A3(_8T,B(_8F(_eo)),_es,_ej));});return B(A3(_8R,_eo,_ep,_el));});return new T2(0,new T(function(){return B(A3(_8P,_em,_ei,_ek));}),_en);},_ew=function(_ex,_ey,_ez,_eA){var _eB=E(_ez),_eC=E(_eA),_eD=B(_eg(_ey,_eB.a,_eB.b,_eC.a,_eC.b));return new T2(0,_eD.a,_eD.b);},_eE=function(_eF){return E(E(_eF).d);},_eG=function(_eH,_eI){var _eJ=new T(function(){return B(_8H(new T(function(){return E(E(E(_eH).c).a);})));}),_eK=new T(function(){return B(A2(_cF,E(_eH).a,new T(function(){return B(A2(_8s,B(_8J(_eJ)),_cC));})));});return new T2(0,new T(function(){return B(A2(_eE,_eJ,_eI));}),_eK);},_eL=function(_eM,_eN,_eO){var _eP=B(_eG(_eN,_eO));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(_8H(new T(function(){return E(E(E(_eR).c).a);})));}),_eV=new T(function(){return B(_8J(_eU));}),_eW=new T(function(){var _eX=new T(function(){var _eY=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),new T(function(){return B(A3(_8L,_eV,_eS,_eS));})));});return B(A2(_6Z,_eV,_eY));});return B(A3(_8T,B(_8F(E(_eR).a)),function(_eZ){return new F(function(){return A3(_8L,_eV,_eZ,_eX);});},_eT));}),_f0=new T(function(){return B(A3(_8P,_eU,new T(function(){return B(A2(_8s,_eV,_9o));}),_eS));});return new T2(0,_f0,_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eQ(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9){return new T4(0,_f8,function(_ef,_ee){return new F(function(){return _ew(_f8,_f9,_ef,_ee);});},function(_ee){return new F(function(){return _f1(_f8,_f9,_ee);});},function(_ee){return new F(function(){return _eL(_f8,_f9,_ee);});});},_fa=function(_fb,_fc,_fd,_fe,_ff){var _fg=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fb).c).a);})));})));}),_fh=new T(function(){var _fi=E(_fb).a,_fj=new T(function(){var _fk=function(_fl,_fm){return new F(function(){return A3(_6X,_fg,new T(function(){return B(A3(_8L,_fg,_fc,_fm));}),new T(function(){return B(A3(_8L,_fg,_fl,_fe));}));});};return B(A3(_8T,B(_8F(_fi)),_fk,_fd));});return B(A3(_8R,_fi,_fj,_ff));});return new T2(0,new T(function(){return B(A3(_8L,_fg,_fc,_fe));}),_fh);},_fn=function(_fo,_fp,_fq){var _fr=E(_fp),_fs=E(_fq),_ft=B(_fa(_fo,_fr.a,_fr.b,_fs.a,_fs.b));return new T2(0,_ft.a,_ft.b);},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fv).c).a);})));})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){return B(A3(_8T,B(_8F(_fC)),new T(function(){return B(_6X(_fA));}),_fx));});return B(A3(_8R,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_6X,_fA,_fw,_fy));}),_fB);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fu(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO){var _fP=B(_fQ(_fM));return new F(function(){return A3(_6X,_fP,_fN,new T(function(){return B(A2(_6Z,_fP,_fO));}));});},_fR=function(_fS){return E(E(_fS).e);},_fT=function(_fU){return E(E(_fU).f);},_fV=function(_fW,_fX,_fY){var _fZ=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_fW).c).a);})));})));}),_g0=new T(function(){var _g1=new T(function(){return B(A2(_fT,_fZ,_fX));});return B(A3(_8T,B(_8F(E(_fW).a)),function(_g2){return new F(function(){return A3(_8L,_fZ,_g2,_g1);});},_fY));});return new T2(0,new T(function(){return B(A2(_fR,_fZ,_fX));}),_g0);},_g3=function(_g4,_g5){var _g6=E(_g5),_g7=B(_fV(_g4,_g6.a,_g6.b));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga){var _gb=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_g9).c).a);})));})));}),_gc=new T(function(){return B(A2(_cF,E(_g9).a,new T(function(){return B(A2(_8s,_gb,_cC));})));});return new T2(0,new T(function(){return B(A2(_8s,_gb,_ga));}),_gc);},_gd=function(_ge,_gf){var _gg=B(_g8(_ge,_gf));return new T2(0,_gg.a,_gg.b);},_gh=function(_gi,_gj,_gk){var _gl=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gi).c).a);})));})));}),_gm=new T(function(){return B(A3(_8T,B(_8F(E(_gi).a)),new T(function(){return B(_6Z(_gl));}),_gk));});return new T2(0,new T(function(){return B(A2(_6Z,_gl,_gj));}),_gm);},_gn=function(_go,_gp){var _gq=E(_gp),_gr=B(_gh(_go,_gq.a,_gq.b));return new T2(0,_gr.a,_gr.b);},_gs=function(_gt,_gu){var _gv=new T(function(){return B(_8J(new T(function(){return B(_8H(new T(function(){return E(E(E(_gt).c).a);})));})));}),_gw=new T(function(){return B(A2(_cF,E(_gt).a,new T(function(){return B(A2(_8s,_gv,_cC));})));});return new T2(0,new T(function(){return B(A2(_fT,_gv,_gu));}),_gw);},_gx=function(_gy,_gz){var _gA=B(_gs(_gy,E(_gz).a));return new T2(0,_gA.a,_gA.b);},_fQ=function(_gB){return {_:0,a:function(_ef,_ee){return new F(function(){return _fE(_gB,_ef,_ee);});},b:function(_ef,_ee){return new F(function(){return _fL(_gB,_ef,_ee);});},c:function(_ef,_ee){return new F(function(){return _fn(_gB,_ef,_ee);});},d:function(_ee){return new F(function(){return _gn(_gB,_ee);});},e:function(_ee){return new F(function(){return _g3(_gB,_ee);});},f:function(_ee){return new F(function(){return _gx(_gB,_ee);});},g:function(_ee){return new F(function(){return _gd(_gB,_ee);});}};},_gC=new T(function(){return B(unCStr("(>=) is not defined"));}),_gD=new T(function(){return B(err(_gC));}),_gE=new T(function(){return B(unCStr("(>) is not defined"));}),_gF=new T(function(){return B(err(_gE));}),_gG=new T(function(){return B(unCStr("(<=) is not defined"));}),_gH=new T(function(){return B(err(_gG));}),_gI=new T(function(){return B(unCStr("(<) is not defined"));}),_gJ=new T(function(){return B(err(_gI));}),_gK=new T(function(){return B(unCStr("compare is not defined"));}),_gL=new T(function(){return B(err(_gK));}),_gM=new T2(0,E(_9o),E(_dj)),_gN=function(_gO){return E(E(_gO).g);},_gP=function(_gQ,_gR,_gS,_gT){var _gU=new T(function(){return B(A3(_8L,_gQ,new T(function(){return B(A3(_9p,_gQ,_gS,_gR));}),_gT));});return new F(function(){return A3(_6X,_gQ,_gR,_gU);});},_gV=function(_gW,_gX,_gY,_gZ,_h0){var _h1=new T(function(){return E(E(_gW).c);}),_h2=new T(function(){var _h3=E(_gW).a,_h4=new T(function(){var _h5=new T(function(){return B(_8H(new T(function(){return E(E(_h1).a);})));}),_h6=new T(function(){return B(_8J(_h5));}),_h7=new T(function(){var _h8=new T(function(){var _h9=new T(function(){return B(A2(_fT,_h6,new T(function(){return B(A3(_9p,_h6,_gZ,_gX));})));});return B(A3(_8L,_h6,_h9,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_6X,_h6,_h8,new T(function(){return B(A2(_eE,_h5,_gM));})));});return B(A3(_8T,B(_8F(_h3)),function(_ha,_hb){return new F(function(){return _gP(_h6,_ha,_hb,_h7);});},_gY));});return B(A3(_8R,_h3,_h4,_h0));});return new T2(0,new T(function(){return B(A3(_gN,E(_h1).b,_gX,_gZ));}),_h2);},_hc=function(_hd,_he,_hf,_hg){var _hh=E(_hf),_hi=E(_hg),_hj=B(_gV(_he,_hh.a,_hh.b,_hi.a,_hi.b));return new T2(0,_hj.a,_hj.b);},_hk=function(_hl){return E(E(_hl).h);},_hm=function(_hn,_ho,_hp,_hq,_hr){var _hs=new T(function(){return E(E(_hn).c);}),_ht=new T(function(){var _hu=E(_hn).a,_hv=new T(function(){var _hw=new T(function(){return B(_8H(new T(function(){return E(E(_hs).a);})));}),_hx=new T(function(){return B(_8J(_hw));}),_hy=new T(function(){var _hz=new T(function(){var _hA=new T(function(){return B(A2(_fT,_hx,new T(function(){return B(A3(_9p,_hx,_hq,_ho));})));});return B(A3(_8L,_hx,_hA,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_6X,_hx,_hz,new T(function(){return B(A2(_eE,_hw,_gM));})));});return B(A3(_8T,B(_8F(_hu)),function(_hB,_hC){return new F(function(){return _gP(_hx,_hC,_hB,_hy);});},_hp));});return B(A3(_8R,_hu,_hv,_hr));});return new T2(0,new T(function(){return B(A3(_hk,E(_hs).b,_ho,_hq));}),_ht);},_hD=function(_hE,_hF,_hG,_hH){var _hI=E(_hG),_hJ=E(_hH),_hK=B(_hm(_hF,_hI.a,_hI.b,_hJ.a,_hJ.b));return new T2(0,_hK.a,_hK.b);},_hL=function(_hM,_hN){return {_:0,a:_hM,b:_gL,c:_gJ,d:_gH,e:_gF,f:_gD,g:function(_ef,_ee){return new F(function(){return _hc(_hM,_hN,_ef,_ee);});},h:function(_ef,_ee){return new F(function(){return _hD(_hM,_hN,_ef,_ee);});}};},_hO=function(_hP){var _hQ=new T(function(){return E(E(_hP).a);}),_hR=new T(function(){return B(_8J(new T(function(){return B(_8H(_hQ));})));}),_hS=new T(function(){return B(A2(_8s,_hR,_8r));}),_hT=function(_hU){var _hV=new T(function(){var _hW=new T(function(){var _hX=new T(function(){var _hY=new T(function(){return E(E(_hU).c);});return B(A3(_8L,_hR,_hY,_hY));}),_hZ=new T(function(){var _i0=new T(function(){return E(E(_hU).a);});return B(A3(_8L,_hR,_i0,_i0));});return B(A3(_6X,_hR,_hZ,_hX));});return B(A2(_9t,_hQ,_hW));});return new F(function(){return A3(_9p,_hR,_hV,_hS);});};return E(_hT);},_i1=function(_ef,_ee){return new T2(0,_ef,_ee);},_i2=function(_i3,_i4,_i5){var _i6=new T(function(){var _i7=E(_i3),_i8=_i7.a,_i9=new T(function(){return B(A1(_i7.b,new T(function(){return B(_8J(B(_8H(E(_i7.c).a))));})));});return B(A3(_8R,_i8,new T(function(){return B(A3(_8T,B(_8F(_i8)),_i1,_i5));}),_i9));});return E(B(A1(_i4,_i6)).b);},_ia=function(_ib){var _ic=new T(function(){return E(E(_ib).a);}),_id=new T(function(){return E(E(_ib).b);}),_ie=new T(function(){var _if=new T(function(){return B(_hL(new T(function(){return B(_8D(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),_ig=new T(function(){var _ih=new T(function(){return B(_f7(new T(function(){return B(_fQ(new T3(0,_8p,_8u,new T2(0,_ic,_id))));}),new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_eb(_ih,new T3(0,_8p,_8u,new T2(0,_ic,_id))));});return B(_hO(new T2(0,_ig,_if)));});return function(_ii){return new F(function(){return _i2(new T3(0,_8p,_8u,new T2(0,_ic,_id)),_ie,_ii);});};},_ij=new T(function(){return B(_ia(_7V));}),_ik=new T(function(){return B(A1(_ij,_E));}),_il=new T(function(){return E(E(_ik).a);}),_im=new T(function(){return B(unCStr(",y:"));}),_in=new T1(0,_im),_io=new T(function(){return E(E(_ik).b);}),_ip=new T(function(){return B(unCStr(",z:"));}),_iq=new T1(0,_ip),_ir=new T(function(){return E(E(_ik).c);}),_is=new T(function(){return B(unCStr("})"));}),_it=new T1(0,_is),_iu=new T2(1,_it,_w),_iv=new T2(1,_ir,_iu),_iw=new T2(1,_iq,_iv),_ix=new T2(1,_io,_iw),_iy=new T2(1,_in,_ix),_iz=new T2(1,_il,_iy),_iA=new T(function(){return B(unCStr("({x:"));}),_iB=new T1(0,_iA),_iC=new T2(1,_iB,_iz),_iD=function(_iE){return E(_iE);},_iF=new T(function(){return toJSStr(B(_e(_x,_iD,_iC)));}),_iG=new T(function(){return B(_hO(_7V));}),_iH=new T(function(){return B(A1(_iG,_E));}),_iI=new T(function(){return toJSStr(B(_4(_x,_iD,_iH)));}),_iJ=function(_iK,_iL,_iM){var _iN=E(_iM);if(!_iN._){return new F(function(){return A1(_iL,_iN.a);});}else{var _iO=new T(function(){return B(_0(_iK));}),_iP=new T(function(){return B(_2(_iK));}),_iQ=function(_iR){var _iS=E(_iR);if(!_iS._){return E(_iP);}else{return new F(function(){return A2(_iO,new T(function(){return B(_iJ(_iK,_iL,_iS.a));}),new T(function(){return B(_iQ(_iS.b));}));});}};return new F(function(){return _iQ(_iN.a);});}},_iT=new T(function(){return B(unCStr("x"));}),_iU=new T1(0,_iT),_iV=new T(function(){return B(unCStr("y"));}),_iW=new T1(0,_iV),_iX=new T(function(){return B(unCStr("z"));}),_iY=new T1(0,_iX),_iZ=new T3(0,E(_iU),E(_iW),E(_iY)),_j0=new T(function(){return B(unCStr(","));}),_j1=new T1(0,_j0),_j2=new T(function(){return B(unCStr("pow("));}),_j3=new T1(0,_j2),_j4=new T(function(){return B(unCStr(")"));}),_j5=new T1(0,_j4),_j6=new T2(1,_j5,_w),_j7=function(_j8,_j9){return new T1(1,new T2(1,_j3,new T2(1,_j8,new T2(1,_j1,new T2(1,_j9,_j6)))));},_ja=new T(function(){return B(unCStr("acos("));}),_jb=new T1(0,_ja),_jc=function(_jd){return new T1(1,new T2(1,_jb,new T2(1,_jd,_j6)));},_je=new T(function(){return B(unCStr("acosh("));}),_jf=new T1(0,_je),_jg=function(_jh){return new T1(1,new T2(1,_jf,new T2(1,_jh,_j6)));},_ji=new T(function(){return B(unCStr("asin("));}),_jj=new T1(0,_ji),_jk=function(_jl){return new T1(1,new T2(1,_jj,new T2(1,_jl,_j6)));},_jm=new T(function(){return B(unCStr("asinh("));}),_jn=new T1(0,_jm),_jo=function(_jp){return new T1(1,new T2(1,_jn,new T2(1,_jp,_j6)));},_jq=new T(function(){return B(unCStr("atan("));}),_jr=new T1(0,_jq),_js=function(_jt){return new T1(1,new T2(1,_jr,new T2(1,_jt,_j6)));},_ju=new T(function(){return B(unCStr("atanh("));}),_jv=new T1(0,_ju),_jw=function(_jx){return new T1(1,new T2(1,_jv,new T2(1,_jx,_j6)));},_jy=new T(function(){return B(unCStr("cos("));}),_jz=new T1(0,_jy),_jA=function(_jB){return new T1(1,new T2(1,_jz,new T2(1,_jB,_j6)));},_jC=new T(function(){return B(unCStr("cosh("));}),_jD=new T1(0,_jC),_jE=function(_jF){return new T1(1,new T2(1,_jD,new T2(1,_jF,_j6)));},_jG=new T(function(){return B(unCStr("exp("));}),_jH=new T1(0,_jG),_jI=function(_jJ){return new T1(1,new T2(1,_jH,new T2(1,_jJ,_j6)));},_jK=new T(function(){return B(unCStr("log("));}),_jL=new T1(0,_jK),_jM=function(_jN){return new T1(1,new T2(1,_jL,new T2(1,_jN,_j6)));},_jO=new T(function(){return B(unCStr(")/log("));}),_jP=new T1(0,_jO),_jQ=function(_jR,_jS){return new T1(1,new T2(1,_jL,new T2(1,_jS,new T2(1,_jP,new T2(1,_jR,_j6)))));},_jT=new T(function(){return B(unCStr("pi"));}),_jU=new T1(0,_jT),_jV=new T(function(){return B(unCStr("sin("));}),_jW=new T1(0,_jV),_jX=function(_jY){return new T1(1,new T2(1,_jW,new T2(1,_jY,_j6)));},_jZ=new T(function(){return B(unCStr("sinh("));}),_k0=new T1(0,_jZ),_k1=function(_k2){return new T1(1,new T2(1,_k0,new T2(1,_k2,_j6)));},_k3=new T(function(){return B(unCStr("sqrt("));}),_k4=new T1(0,_k3),_k5=function(_k6){return new T1(1,new T2(1,_k4,new T2(1,_k6,_j6)));},_k7=new T(function(){return B(unCStr("tan("));}),_k8=new T1(0,_k7),_k9=function(_ka){return new T1(1,new T2(1,_k8,new T2(1,_ka,_j6)));},_kb=new T(function(){return B(unCStr("tanh("));}),_kc=new T1(0,_kb),_kd=function(_ke){return new T1(1,new T2(1,_kc,new T2(1,_ke,_j6)));},_kf=new T(function(){return B(unCStr("("));}),_kg=new T1(0,_kf),_kh=new T(function(){return B(unCStr(")/("));}),_ki=new T1(0,_kh),_kj=function(_kk,_kl){return new T1(1,new T2(1,_kg,new T2(1,_kk,new T2(1,_ki,new T2(1,_kl,_j6)))));},_km=function(_kn){return new T1(0,new T(function(){var _ko=E(_kn),_kp=jsShow(B(_6y(_ko.a,_ko.b)));return fromJSStr(_kp);}));},_kq=new T(function(){return B(unCStr("1./("));}),_kr=new T1(0,_kq),_ks=function(_kt){return new T1(1,new T2(1,_kr,new T2(1,_kt,_j6)));},_ku=new T(function(){return B(unCStr(")+("));}),_kv=new T1(0,_ku),_kw=function(_kx,_ky){return new T1(1,new T2(1,_kg,new T2(1,_kx,new T2(1,_kv,new T2(1,_ky,_j6)))));},_kz=new T(function(){return B(unCStr("-("));}),_kA=new T1(0,_kz),_kB=function(_kC){return new T1(1,new T2(1,_kA,new T2(1,_kC,_j6)));},_kD=new T(function(){return B(unCStr(")*("));}),_kE=new T1(0,_kD),_kF=function(_kG,_kH){return new T1(1,new T2(1,_kg,new T2(1,_kG,new T2(1,_kE,new T2(1,_kH,_j6)))));},_kI=function(_kJ,_kK){return new F(function(){return A3(_6X,_kL,_kJ,new T(function(){return B(A2(_6Z,_kL,_kK));}));});},_kM=new T(function(){return B(unCStr("abs("));}),_kN=new T1(0,_kM),_kO=function(_kP){return new T1(1,new T2(1,_kN,new T2(1,_kP,_j6)));},_kQ=new T(function(){return B(unCStr("."));}),_kR=function(_kS){return new T1(0,new T(function(){return B(_n(B(_7i(0,_kS,_w)),_kQ));}));},_kT=new T(function(){return B(unCStr("sign("));}),_kU=new T1(0,_kT),_kV=function(_kW){return new T1(1,new T2(1,_kU,new T2(1,_kW,_j6)));},_kL=new T(function(){return {_:0,a:_kw,b:_kI,c:_kF,d:_kB,e:_kO,f:_kV,g:_kR};}),_kX=new T4(0,_kL,_kj,_ks,_km),_kY={_:0,a:_kX,b:_jU,c:_jI,d:_jM,e:_k5,f:_j7,g:_jQ,h:_jX,i:_jA,j:_k9,k:_jk,l:_jc,m:_js,n:_k1,o:_jE,p:_kd,q:_jo,r:_jg,s:_jw},_kZ=new T(function(){return B(unCStr("(/=) is not defined"));}),_l0=new T(function(){return B(err(_kZ));}),_l1=new T(function(){return B(unCStr("(==) is not defined"));}),_l2=new T(function(){return B(err(_l1));}),_l3=new T2(0,_l2,_l0),_l4=new T(function(){return B(unCStr("(<) is not defined"));}),_l5=new T(function(){return B(err(_l4));}),_l6=new T(function(){return B(unCStr("(<=) is not defined"));}),_l7=new T(function(){return B(err(_l6));}),_l8=new T(function(){return B(unCStr("(>) is not defined"));}),_l9=new T(function(){return B(err(_l8));}),_la=new T(function(){return B(unCStr("(>=) is not defined"));}),_lb=new T(function(){return B(err(_la));}),_lc=new T(function(){return B(unCStr("compare is not defined"));}),_ld=new T(function(){return B(err(_lc));}),_le=new T(function(){return B(unCStr("max("));}),_lf=new T1(0,_le),_lg=function(_lh,_li){return new T1(1,new T2(1,_lf,new T2(1,_lh,new T2(1,_j1,new T2(1,_li,_j6)))));},_lj=new T(function(){return B(unCStr("min("));}),_lk=new T1(0,_lj),_ll=function(_lm,_ln){return new T1(1,new T2(1,_lk,new T2(1,_lm,new T2(1,_j1,new T2(1,_ln,_j6)))));},_lo={_:0,a:_l3,b:_ld,c:_l5,d:_l7,e:_l9,f:_lb,g:_lg,h:_ll},_lp=new T2(0,_kY,_lo),_lq=new T(function(){return B(_hO(_lp));}),_lr=new T(function(){return B(A1(_lq,_iZ));}),_ls=new T(function(){return toJSStr(B(_iJ(_x,_iD,_lr)));}),_lt=new T(function(){return eval("__strict(compile)");}),_lu=new T(function(){return toJSStr(E(_iV));}),_lv=function(_lw,_lx,_ly){var _lz=new T(function(){return B(_0(_lw));}),_lA=new T(function(){return B(_2(_lw));}),_lB=function(_lC){var _lD=E(_lC);if(!_lD._){return E(_lA);}else{return new F(function(){return A2(_lz,new T(function(){return B(_iJ(_lw,_lx,_lD.a));}),new T(function(){return B(_lB(_lD.b));}));});}};return new F(function(){return _lB(_ly);});},_lE=new T(function(){return B(unCStr("vec3("));}),_lF=new T1(0,_lE),_lG=new T(function(){return B(_7i(0,_8r,_w));}),_lH=new T(function(){return B(_n(_lG,_kQ));}),_lI=new T1(0,_lH),_lJ=new T(function(){return B(_7i(0,_8q,_w));}),_lK=new T(function(){return B(_n(_lJ,_kQ));}),_lL=new T1(0,_lK),_lM=new T2(1,_lL,_w),_lN=new T2(1,_lI,_lM),_lO=function(_lP,_lQ){var _lR=E(_lQ);return (_lR._==0)?__Z:new T2(1,_lP,new T2(1,_lR.a,new T(function(){return B(_lO(_lP,_lR.b));})));},_lS=new T(function(){return B(_lO(_j1,_lN));}),_lT=new T2(1,_lL,_lS),_lU=new T1(1,_lT),_lV=new T2(1,_lU,_j6),_lW=new T2(1,_lF,_lV),_lX=new T(function(){return toJSStr(B(_lv(_x,_iD,_lW)));}),_lY=function(_lZ,_m0){while(1){var _m1=E(_lZ);if(!_m1._){return E(_m0);}else{var _m2=_m0+1|0;_lZ=_m1.b;_m0=_m2;continue;}}},_m3=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_m4=new T(function(){return B(err(_m3));}),_m5=0,_m6=new T3(0,E(_m5),E(_m5),E(_m5)),_m7=new T(function(){return B(unCStr("Negative exponent"));}),_m8=new T(function(){return B(err(_m7));}),_m9=function(_ma,_mb,_mc){while(1){if(!(_mb%2)){var _md=_ma*_ma,_me=quot(_mb,2);_ma=_md;_mb=_me;continue;}else{var _mf=E(_mb);if(_mf==1){return _ma*_mc;}else{var _md=_ma*_ma,_mg=_ma*_mc;_ma=_md;_mb=quot(_mf-1|0,2);_mc=_mg;continue;}}}},_mh=function(_mi,_mj){while(1){if(!(_mj%2)){var _mk=_mi*_mi,_ml=quot(_mj,2);_mi=_mk;_mj=_ml;continue;}else{var _mm=E(_mj);if(_mm==1){return E(_mi);}else{return new F(function(){return _m9(_mi*_mi,quot(_mm-1|0,2),_mi);});}}}},_mn=function(_mo){var _mp=E(_mo);return new F(function(){return Math.log(_mp+(_mp+1)*Math.sqrt((_mp-1)/(_mp+1)));});},_mq=function(_mr){var _ms=E(_mr);return new F(function(){return Math.log(_ms+Math.sqrt(1+_ms*_ms));});},_mt=function(_mu){var _mv=E(_mu);return 0.5*Math.log((1+_mv)/(1-_mv));},_mw=function(_mx,_my){return Math.log(E(_my))/Math.log(E(_mx));},_mz=3.141592653589793,_mA=function(_mB){var _mC=E(_mB);return new F(function(){return _6y(_mC.a,_mC.b);});},_mD=function(_mE){return 1/E(_mE);},_mF=function(_mG){var _mH=E(_mG),_mI=E(_mH);return (_mI==0)?E(_6x):(_mI<=0)? -_mI:E(_mH);},_mJ=function(_mK){var _mL=E(_mK);if(!_mL._){return _mL.a;}else{return new F(function(){return I_toNumber(_mL.a);});}},_mM=function(_mN){return new F(function(){return _mJ(_mN);});},_mO=1,_mP=-1,_mQ=function(_mR){var _mS=E(_mR);return (_mS<=0)?(_mS>=0)?E(_mS):E(_mP):E(_mO);},_mT=function(_mU,_mV){return E(_mU)-E(_mV);},_mW=function(_mX){return  -E(_mX);},_mY=function(_mZ,_n0){return E(_mZ)+E(_n0);},_n1=function(_n2,_n3){return E(_n2)*E(_n3);},_n4={_:0,a:_mY,b:_mT,c:_n1,d:_mW,e:_mF,f:_mQ,g:_mM},_n5=function(_n6,_n7){return E(_n6)/E(_n7);},_n8=new T4(0,_n4,_n5,_mD,_mA),_n9=function(_na){return new F(function(){return Math.acos(E(_na));});},_nb=function(_nc){return new F(function(){return Math.asin(E(_nc));});},_nd=function(_ne){return new F(function(){return Math.atan(E(_ne));});},_nf=function(_ng){return new F(function(){return Math.cos(E(_ng));});},_nh=function(_ni){return new F(function(){return cosh(E(_ni));});},_nj=function(_nk){return new F(function(){return Math.exp(E(_nk));});},_nl=function(_nm){return new F(function(){return Math.log(E(_nm));});},_nn=function(_no,_np){return new F(function(){return Math.pow(E(_no),E(_np));});},_nq=function(_nr){return new F(function(){return Math.sin(E(_nr));});},_ns=function(_nt){return new F(function(){return sinh(E(_nt));});},_nu=function(_nv){return new F(function(){return Math.sqrt(E(_nv));});},_nw=function(_nx){return new F(function(){return Math.tan(E(_nx));});},_ny=function(_nz){return new F(function(){return tanh(E(_nz));});},_nA={_:0,a:_n8,b:_mz,c:_nj,d:_nl,e:_nu,f:_nn,g:_mw,h:_nq,i:_nf,j:_nw,k:_nb,l:_n9,m:_nd,n:_ns,o:_nh,p:_ny,q:_mq,r:_mn,s:_mt},_nB=function(_nC,_nD){return (E(_nC)!=E(_nD))?true:false;},_nE=function(_nF,_nG){return E(_nF)==E(_nG);},_nH=new T2(0,_nE,_nB),_nI=function(_nJ,_nK){return E(_nJ)<E(_nK);},_nL=function(_nM,_nN){return E(_nM)<=E(_nN);},_nO=function(_nP,_nQ){return E(_nP)>E(_nQ);},_nR=function(_nS,_nT){return E(_nS)>=E(_nT);},_nU=function(_nV,_nW){var _nX=E(_nV),_nY=E(_nW);return (_nX>=_nY)?(_nX!=_nY)?2:1:0;},_nZ=function(_o0,_o1){var _o2=E(_o0),_o3=E(_o1);return (_o2>_o3)?E(_o2):E(_o3);},_o4=function(_o5,_o6){var _o7=E(_o5),_o8=E(_o6);return (_o7>_o8)?E(_o8):E(_o7);},_o9={_:0,a:_nH,b:_nU,c:_nI,d:_nL,e:_nO,f:_nR,g:_nZ,h:_o4},_oa="dz",_ob="wy",_oc="wx",_od="dy",_oe="dx",_of="t",_og="a",_oh="r",_oi="ly",_oj="lx",_ok="wz",_ol=0,_om=function(_on){var _oo=__new(),_op=_oo,_oq=function(_or,_){while(1){var _os=E(_or);if(!_os._){return _ol;}else{var _ot=E(_os.a),_ou=__set(_op,E(_ot.a),E(_ot.b));_or=_os.b;continue;}}},_ov=B(_oq(_on,_));return E(_op);},_ow=function(_ox,_oy,_oz,_oA,_oB,_oC,_oD,_oE,_oF){return new F(function(){return _om(new T2(1,new T2(0,_oc,_ox),new T2(1,new T2(0,_ob,_oy),new T2(1,new T2(0,_ok,_oz),new T2(1,new T2(0,_oj,_oA*_oB*Math.cos(_oC)),new T2(1,new T2(0,_oi,_oA*_oB*Math.sin(_oC)),new T2(1,new T2(0,_oh,_oA),new T2(1,new T2(0,_og,_oB),new T2(1,new T2(0,_of,_oC),new T2(1,new T2(0,_oe,_oD),new T2(1,new T2(0,_od,_oE),new T2(1,new T2(0,_oa,_oF),_w))))))))))));});},_oG=function(_oH){var _oI=E(_oH),_oJ=E(_oI.a),_oK=E(_oI.b),_oL=E(_oI.d);return new F(function(){return _ow(_oJ.a,_oJ.b,_oJ.c,E(_oK.a),E(_oK.b),E(_oI.c),_oL.a,_oL.b,_oL.c);});},_oM=function(_oN,_oO){var _oP=E(_oO);return (_oP._==0)?__Z:new T2(1,new T(function(){return B(A1(_oN,_oP.a));}),new T(function(){return B(_oM(_oN,_oP.b));}));},_oQ=function(_oR,_oS,_oT){var _oU=__lst2arr(B(_oM(_oG,new T2(1,_oR,new T2(1,_oS,new T2(1,_oT,_w))))));return E(_oU);},_oV=function(_oW){var _oX=E(_oW);return new F(function(){return _oQ(_oX.a,_oX.b,_oX.c);});},_oY=new T2(0,_nA,_o9),_oZ=function(_p0,_p1,_p2,_p3,_p4,_p5,_p6){var _p7=B(_8J(B(_8H(_p0)))),_p8=new T(function(){return B(A3(_6X,_p7,new T(function(){return B(A3(_8L,_p7,_p1,_p4));}),new T(function(){return B(A3(_8L,_p7,_p2,_p5));})));});return new F(function(){return A3(_6X,_p7,_p8,new T(function(){return B(A3(_8L,_p7,_p3,_p6));}));});},_p9=function(_pa,_pb,_pc,_pd){var _pe=B(_8H(_pa)),_pf=new T(function(){return B(A2(_9t,_pa,new T(function(){return B(_oZ(_pa,_pb,_pc,_pd,_pb,_pc,_pd));})));});return new T3(0,B(A3(_8P,_pe,_pb,_pf)),B(A3(_8P,_pe,_pc,_pf)),B(A3(_8P,_pe,_pd,_pf)));},_pg=function(_ph,_pi,_pj,_pk,_pl,_pm,_pn){var _po=B(_8L(_ph));return new T3(0,B(A1(B(A1(_po,_pi)),_pl)),B(A1(B(A1(_po,_pj)),_pm)),B(A1(B(A1(_po,_pk)),_pn)));},_pp=function(_pq,_pr,_ps,_pt,_pu,_pv,_pw){var _px=B(_6X(_pq));return new T3(0,B(A1(B(A1(_px,_pr)),_pu)),B(A1(B(A1(_px,_ps)),_pv)),B(A1(B(A1(_px,_pt)),_pw)));},_py=function(_pz,_pA){var _pB=new T(function(){return E(E(_pz).a);}),_pC=new T(function(){var _pD=E(_pA),_pE=new T(function(){return B(_8J(new T(function(){return B(_8H(_pB));})));}),_pF=B(A2(_8s,_pE,_8q));return new T3(0,E(_pF),E(B(A2(_8s,_pE,_8r))),E(_pF));}),_pG=new T(function(){var _pH=E(_pC),_pI=B(_p9(_pB,_pH.a,_pH.b,_pH.c));return new T3(0,E(_pI.a),E(_pI.b),E(_pI.c));}),_pJ=new T(function(){var _pK=E(_pA),_pL=_pK.b,_pM=E(_pG),_pN=B(_8H(_pB)),_pO=new T(function(){return B(A2(_9t,_pB,new T(function(){var _pP=E(_pC),_pQ=_pP.a,_pR=_pP.b,_pS=_pP.c;return B(_oZ(_pB,_pQ,_pR,_pS,_pQ,_pR,_pS));})));}),_pT=B(A3(_8P,_pN,_pL,_pO)),_pU=B(_8J(_pN)),_pV=B(_pg(_pU,_pM.a,_pM.b,_pM.c,_pT,_pT,_pT)),_pW=B(_6Z(_pU)),_pX=B(_pp(_pU,_pK.a,_pL,_pK.c,B(A1(_pW,_pV.a)),B(A1(_pW,_pV.b)),B(A1(_pW,_pV.c))));return new T3(0,E(_pX.a),E(_pX.b),E(_pX.c));});return new T2(0,_pJ,_pG);},_pY=function(_pZ){return E(E(_pZ).a);},_q0=function(_q1,_q2,_q3,_q4,_q5,_q6,_q7){var _q8=B(_oZ(_q1,_q5,_q6,_q7,_q2,_q3,_q4)),_q9=B(_8J(B(_8H(_q1)))),_qa=B(_pg(_q9,_q5,_q6,_q7,_q8,_q8,_q8)),_qb=B(_6Z(_q9));return new F(function(){return _pp(_q9,_q2,_q3,_q4,B(A1(_qb,_qa.a)),B(A1(_qb,_qa.b)),B(A1(_qb,_qa.c)));});},_qc=function(_qd){return E(E(_qd).a);},_qe=function(_qf,_qg,_qh,_qi){var _qj=new T(function(){var _qk=E(_qi),_ql=E(_qh),_qm=B(_q0(_qf,_qk.a,_qk.b,_qk.c,_ql.a,_ql.b,_ql.c));return new T3(0,E(_qm.a),E(_qm.b),E(_qm.c));}),_qn=new T(function(){return B(A2(_9t,_qf,new T(function(){var _qo=E(_qj),_qp=_qo.a,_qq=_qo.b,_qr=_qo.c;return B(_oZ(_qf,_qp,_qq,_qr,_qp,_qq,_qr));})));});if(!B(A3(_qc,B(_pY(_qg)),_qn,new T(function(){return B(A2(_8s,B(_8J(B(_8H(_qf)))),_8q));})))){var _qs=E(_qj),_qt=B(_p9(_qf,_qs.a,_qs.b,_qs.c)),_qu=B(A2(_9t,_qf,new T(function(){var _qv=E(_qi),_qw=_qv.a,_qx=_qv.b,_qy=_qv.c;return B(_oZ(_qf,_qw,_qx,_qy,_qw,_qx,_qy));}))),_qz=B(_8L(new T(function(){return B(_8J(new T(function(){return B(_8H(_qf));})));})));return new T3(0,B(A1(B(A1(_qz,_qt.a)),_qu)),B(A1(B(A1(_qz,_qt.b)),_qu)),B(A1(B(A1(_qz,_qt.c)),_qu)));}else{var _qA=B(A2(_8s,B(_8J(B(_8H(_qf)))),_8q));return new T3(0,_qA,_qA,_qA);}},_qB=new T(function(){var _qC=eval("angleCount"),_qD=Number(_qC);return jsTrunc(_qD);}),_qE=new T(function(){return E(_qB);}),_qF=new T(function(){return B(unCStr(": empty list"));}),_qG=new T(function(){return B(unCStr("Prelude."));}),_qH=function(_qI){return new F(function(){return err(B(_n(_qG,new T(function(){return B(_n(_qI,_qF));},1))));});},_qJ=new T(function(){return B(unCStr("head"));}),_qK=new T(function(){return B(_qH(_qJ));}),_qL=function(_qM,_qN,_qO){var _qP=E(_qM);if(!_qP._){return __Z;}else{var _qQ=E(_qN);if(!_qQ._){return __Z;}else{var _qR=_qQ.a,_qS=E(_qO);if(!_qS._){return __Z;}else{var _qT=E(_qS.a),_qU=_qT.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_qP.a),E(_qR),E(_qU));}),new T2(1,new T(function(){return new T3(0,E(_qR),E(_qU),E(_qT.b));}),_w)),new T(function(){return B(_qL(_qP.b,_qQ.b,_qS.b));},1));});}}}},_qV=new T(function(){return B(unCStr("tail"));}),_qW=new T(function(){return B(_qH(_qV));}),_qX=function(_qY,_qZ){var _r0=E(_qY);if(!_r0._){return __Z;}else{var _r1=E(_qZ);return (_r1._==0)?__Z:new T2(1,new T2(0,_r0.a,_r1.a),new T(function(){return B(_qX(_r0.b,_r1.b));}));}},_r2=function(_r3,_r4){var _r5=E(_r3);if(!_r5._){return __Z;}else{var _r6=E(_r4);if(!_r6._){return __Z;}else{var _r7=E(_r5.a),_r8=_r7.b,_r9=E(_r6.a).b,_ra=new T(function(){var _rb=new T(function(){return B(_qX(_r9,new T(function(){var _rc=E(_r9);if(!_rc._){return E(_qW);}else{return E(_rc.b);}},1)));},1);return B(_qL(_r8,new T(function(){var _rd=E(_r8);if(!_rd._){return E(_qW);}else{return E(_rd.b);}},1),_rb));});return new F(function(){return _n(new T2(1,new T(function(){var _re=E(_r8);if(!_re._){return E(_qK);}else{var _rf=E(_r9);if(!_rf._){return E(_qK);}else{return new T3(0,E(_r7.a),E(_re.a),E(_rf.a));}}}),_ra),new T(function(){return B(_r2(_r5.b,_r6.b));},1));});}}},_rg=new T(function(){return E(_qE)-1;}),_rh=new T1(0,1),_ri=function(_rj,_rk){var _rl=E(_rk),_rm=new T(function(){var _rn=B(_8J(_rj)),_ro=B(_ri(_rj,B(A3(_6X,_rn,_rl,new T(function(){return B(A2(_8s,_rn,_rh));})))));return new T2(1,_ro.a,_ro.b);});return new T2(0,_rl,_rm);},_rp=function(_rq){return E(E(_rq).d);},_rr=new T1(0,2),_rs=function(_rt,_ru){var _rv=E(_ru);if(!_rv._){return __Z;}else{var _rw=_rv.a;return (!B(A1(_rt,_rw)))?__Z:new T2(1,_rw,new T(function(){return B(_rs(_rt,_rv.b));}));}},_rx=function(_ry,_rz,_rA,_rB){var _rC=B(_ri(_rz,_rA)),_rD=new T(function(){var _rE=B(_8J(_rz)),_rF=new T(function(){return B(A3(_8P,_rz,new T(function(){return B(A2(_8s,_rE,_rh));}),new T(function(){return B(A2(_8s,_rE,_rr));})));});return B(A3(_6X,_rE,_rB,_rF));});return new F(function(){return _rs(function(_rG){return new F(function(){return A3(_rp,_ry,_rG,_rD);});},new T2(1,_rC.a,_rC.b));});},_rH=new T(function(){return B(_rx(_o9,_n8,_m5,_rg));}),_rI=function(_rJ,_rK){while(1){var _rL=E(_rJ);if(!_rL._){return E(_rK);}else{_rJ=_rL.b;_rK=_rL.a;continue;}}},_rM=new T(function(){return B(unCStr("last"));}),_rN=new T(function(){return B(_qH(_rM));}),_rO=function(_rP){return new F(function(){return _rI(_rP,_rN);});},_rQ=function(_rR){return new F(function(){return _rO(E(_rR).b);});},_rS=new T(function(){var _rT=eval("proceedCount"),_rU=Number(_rT);return jsTrunc(_rU);}),_rV=new T(function(){return E(_rS);}),_rW=1,_rX=new T(function(){return B(_rx(_o9,_n8,_rW,_rV));}),_rY=function(_rZ,_s0,_s1,_s2,_s3,_s4,_s5,_s6,_s7,_s8,_s9,_sa,_sb,_sc){var _sd=new T(function(){var _se=new T(function(){var _sf=E(_s8),_sg=E(_sc),_sh=E(_sb),_si=E(_s9),_sj=E(_sa),_sk=E(_s7);return new T3(0,_sf*_sg-_sh*_si,_si*_sj-_sg*_sk,_sk*_sh-_sj*_sf);}),_sl=function(_sm){var _sn=new T(function(){var _so=E(_sm)/E(_qE);return (_so+_so)*3.141592653589793;}),_sp=new T(function(){return B(A1(_rZ,_sn));}),_sq=new T(function(){var _sr=new T(function(){var _ss=E(_sp)/E(_rV);return new T3(0,E(_ss),E(_ss),E(_ss));}),_st=function(_su,_sv){var _sw=E(_su);if(!_sw._){return new T2(0,_w,_sv);}else{var _sx=new T(function(){var _sy=B(_py(_oY,new T(function(){var _sz=E(_sv),_sA=E(_sz.a),_sB=E(_sz.b),_sC=E(_sr);return new T3(0,E(_sA.a)+E(_sB.a)*E(_sC.a),E(_sA.b)+E(_sB.b)*E(_sC.b),E(_sA.c)+E(_sB.c)*E(_sC.c));}))),_sD=_sy.a,_sE=new T(function(){var _sF=E(_sy.b),_sG=E(E(_sv).b),_sH=B(_q0(_nA,_sG.a,_sG.b,_sG.c,_sF.a,_sF.b,_sF.c)),_sI=B(_p9(_nA,_sH.a,_sH.b,_sH.c));return new T3(0,E(_sI.a),E(_sI.b),E(_sI.c));});return new T2(0,new T(function(){var _sJ=E(_sp),_sK=E(_sn);return new T4(0,E(_sD),E(new T2(0,E(_sw.a)/E(_rV),E(_sJ))),E(_sK),E(_sE));}),new T2(0,_sD,_sE));}),_sL=new T(function(){var _sM=B(_st(_sw.b,new T(function(){return E(E(_sx).b);})));return new T2(0,_sM.a,_sM.b);});return new T2(0,new T2(1,new T(function(){return E(E(_sx).a);}),new T(function(){return E(E(_sL).a);})),new T(function(){return E(E(_sL).b);}));}},_sN=function(_sO,_sP,_sQ,_sR,_sS){var _sT=E(_sO);if(!_sT._){return new T2(0,_w,new T2(0,new T3(0,E(_sP),E(_sQ),E(_sR)),_sS));}else{var _sU=new T(function(){var _sV=B(_py(_oY,new T(function(){var _sW=E(_sS),_sX=E(_sr);return new T3(0,E(_sP)+E(_sW.a)*E(_sX.a),E(_sQ)+E(_sW.b)*E(_sX.b),E(_sR)+E(_sW.c)*E(_sX.c));}))),_sY=_sV.a,_sZ=new T(function(){var _t0=E(_sV.b),_t1=E(_sS),_t2=B(_q0(_nA,_t1.a,_t1.b,_t1.c,_t0.a,_t0.b,_t0.c)),_t3=B(_p9(_nA,_t2.a,_t2.b,_t2.c));return new T3(0,E(_t3.a),E(_t3.b),E(_t3.c));});return new T2(0,new T(function(){var _t4=E(_sp),_t5=E(_sn);return new T4(0,E(_sY),E(new T2(0,E(_sT.a)/E(_rV),E(_t4))),E(_t5),E(_sZ));}),new T2(0,_sY,_sZ));}),_t6=new T(function(){var _t7=B(_st(_sT.b,new T(function(){return E(E(_sU).b);})));return new T2(0,_t7.a,_t7.b);});return new T2(0,new T2(1,new T(function(){return E(E(_sU).a);}),new T(function(){return E(E(_t6).a);})),new T(function(){return E(E(_t6).b);}));}};return E(B(_sN(_rX,_s2,_s3,_s4,new T(function(){var _t8=E(_se),_t9=E(_sn)+_s5,_ta=Math.cos(_t9),_tb=Math.sin(_t9);return new T3(0,E(_s7)*_ta+E(_t8.a)*_tb,E(_s8)*_ta+E(_t8.b)*_tb,E(_s9)*_ta+E(_t8.c)*_tb);}))).a);});return new T2(0,new T(function(){var _tc=E(_sp),_td=E(_sn);return new T4(0,E(new T3(0,E(_s2),E(_s3),E(_s4))),E(new T2(0,E(_m5),E(_tc))),E(_td),E(_m6));}),_sq);};return B(_oM(_sl,_rH));}),_te=new T(function(){var _tf=new T(function(){var _tg=B(_n(_sd,new T2(1,new T(function(){var _th=E(_sd);if(!_th._){return E(_qK);}else{return E(_th.a);}}),_w)));if(!_tg._){return E(_qW);}else{return E(_tg.b);}},1);return B(_r2(_sd,_tf));});return new T2(0,_te,new T(function(){return B(_oM(_rQ,_sd));}));},_ti=function(_tj,_tk,_tl,_tm,_tn,_to,_tp,_tq,_tr,_ts,_tt,_tu,_tv,_tw,_tx,_ty,_tz){var _tA=B(_py(_oY,new T3(0,E(_tm),E(_tn),E(_to)))),_tB=_tA.b,_tC=E(_tA.a),_tD=B(_qe(_nA,_o9,_tB,new T3(0,E(_tq),E(_tr),E(_ts)))),_tE=E(_tB),_tF=_tE.a,_tG=_tE.b,_tH=_tE.c,_tI=B(_q0(_nA,_tu,_tv,_tw,_tF,_tG,_tH)),_tJ=B(_p9(_nA,_tI.a,_tI.b,_tI.c)),_tK=_tJ.a,_tL=_tJ.b,_tM=_tJ.c,_tN=E(_tp),_tO=new T2(0,E(new T3(0,E(_tD.a),E(_tD.b),E(_tD.c))),E(_tt)),_tP=B(_rY(_tj,_tk,_tl,_tC.a,_tC.b,_tC.c,_tN,_tO,_tK,_tL,_tM,_tF,_tG,_tH)),_tQ=__lst2arr(B(_oM(_oV,_tP.a))),_tR=__lst2arr(B(_oM(_oG,_tP.b)));return {_:0,a:_tj,b:_tk,c:_tl,d:new T2(0,E(_tC),E(_tN)),e:_tO,f:new T3(0,E(_tK),E(_tL),E(_tM)),g:_tE,h:_tQ,i:_tR};},_tS=-2,_tT=new T3(0,E(_m5),E(_m5),E(_tS)),_tU=function(_tV){return E(_tT);},_tW=new T(function(){return 6.283185307179586/E(_qE);}),_tX=function(_){return new F(function(){return __jsNull();});},_tY=function(_tZ){var _u0=B(A1(_tZ,_));return E(_u0);},_u1=new T(function(){return B(_tY(_tX));}),_u2=function(_u3,_u4,_u5,_u6,_u7,_u8,_u9,_ua,_ub,_uc,_ud,_ue,_uf){var _ug=function(_uh){var _ui=E(_tW),_uj=2+_uh|0,_uk=_uj-1|0,_ul=(2+_uh)*(1+_uh),_um=E(_rH);if(!_um._){return _ui*0;}else{var _un=_um.a,_uo=_um.b,_up=B(A1(_u3,new T(function(){return 6.283185307179586*E(_un)/E(_qE);}))),_uq=B(A1(_u3,new T(function(){return 6.283185307179586*(E(_un)+1)/E(_qE);})));if(_up!=_uq){if(_uj>=0){var _ur=E(_uj);if(!_ur){var _us=function(_ut,_uu){while(1){var _uv=B((function(_uw,_ux){var _uy=E(_uw);if(!_uy._){return E(_ux);}else{var _uz=_uy.a,_uA=_uy.b,_uB=B(A1(_u3,new T(function(){return 6.283185307179586*E(_uz)/E(_qE);}))),_uC=B(A1(_u3,new T(function(){return 6.283185307179586*(E(_uz)+1)/E(_qE);})));if(_uB!=_uC){var _uD=_ux+0/(_uB-_uC)/_ul;_ut=_uA;_uu=_uD;return __continue;}else{if(_uk>=0){var _uE=E(_uk);if(!_uE){var _uD=_ux+_uj/_ul;_ut=_uA;_uu=_uD;return __continue;}else{var _uD=_ux+_uj*B(_mh(_uB,_uE))/_ul;_ut=_uA;_uu=_uD;return __continue;}}else{return E(_m8);}}}})(_ut,_uu));if(_uv!=__continue){return _uv;}}};return _ui*B(_us(_uo,0/(_up-_uq)/_ul));}else{var _uF=function(_uG,_uH){while(1){var _uI=B((function(_uJ,_uK){var _uL=E(_uJ);if(!_uL._){return E(_uK);}else{var _uM=_uL.a,_uN=_uL.b,_uO=B(A1(_u3,new T(function(){return 6.283185307179586*E(_uM)/E(_qE);}))),_uP=B(A1(_u3,new T(function(){return 6.283185307179586*(E(_uM)+1)/E(_qE);})));if(_uO!=_uP){if(_ur>=0){var _uQ=_uK+(B(_mh(_uO,_ur))-B(_mh(_uP,_ur)))/(_uO-_uP)/_ul;_uG=_uN;_uH=_uQ;return __continue;}else{return E(_m8);}}else{if(_uk>=0){var _uR=E(_uk);if(!_uR){var _uQ=_uK+_uj/_ul;_uG=_uN;_uH=_uQ;return __continue;}else{var _uQ=_uK+_uj*B(_mh(_uO,_uR))/_ul;_uG=_uN;_uH=_uQ;return __continue;}}else{return E(_m8);}}}})(_uG,_uH));if(_uI!=__continue){return _uI;}}};return _ui*B(_uF(_uo,(B(_mh(_up,_ur))-B(_mh(_uq,_ur)))/(_up-_uq)/_ul));}}else{return E(_m8);}}else{if(_uk>=0){var _uS=E(_uk);if(!_uS){var _uT=function(_uU,_uV){while(1){var _uW=B((function(_uX,_uY){var _uZ=E(_uX);if(!_uZ._){return E(_uY);}else{var _v0=_uZ.a,_v1=_uZ.b,_v2=B(A1(_u3,new T(function(){return 6.283185307179586*E(_v0)/E(_qE);}))),_v3=B(A1(_u3,new T(function(){return 6.283185307179586*(E(_v0)+1)/E(_qE);})));if(_v2!=_v3){if(_uj>=0){var _v4=E(_uj);if(!_v4){var _v5=_uY+0/(_v2-_v3)/_ul;_uU=_v1;_uV=_v5;return __continue;}else{var _v5=_uY+(B(_mh(_v2,_v4))-B(_mh(_v3,_v4)))/(_v2-_v3)/_ul;_uU=_v1;_uV=_v5;return __continue;}}else{return E(_m8);}}else{var _v5=_uY+_uj/_ul;_uU=_v1;_uV=_v5;return __continue;}}})(_uU,_uV));if(_uW!=__continue){return _uW;}}};return _ui*B(_uT(_uo,_uj/_ul));}else{var _v6=function(_v7,_v8){while(1){var _v9=B((function(_va,_vb){var _vc=E(_va);if(!_vc._){return E(_vb);}else{var _vd=_vc.a,_ve=_vc.b,_vf=B(A1(_u3,new T(function(){return 6.283185307179586*E(_vd)/E(_qE);}))),_vg=B(A1(_u3,new T(function(){return 6.283185307179586*(E(_vd)+1)/E(_qE);})));if(_vf!=_vg){if(_uj>=0){var _vh=E(_uj);if(!_vh){var _vi=_vb+0/(_vf-_vg)/_ul;_v7=_ve;_v8=_vi;return __continue;}else{var _vi=_vb+(B(_mh(_vf,_vh))-B(_mh(_vg,_vh)))/(_vf-_vg)/_ul;_v7=_ve;_v8=_vi;return __continue;}}else{return E(_m8);}}else{if(_uS>=0){var _vi=_vb+_uj*B(_mh(_vf,_uS))/_ul;_v7=_ve;_v8=_vi;return __continue;}else{return E(_m8);}}}})(_v7,_v8));if(_v9!=__continue){return _v9;}}};return _ui*B(_v6(_uo,_uj*B(_mh(_up,_uS))/_ul));}}else{return E(_m8);}}}},_vj=E(_u1),_vk=1/(B(_ug(1))*_u4);return new F(function(){return _ti(_u3,_tU,new T2(0,E(new T3(0,E(_vk),E(_vk),E(_vk))),1/(B(_ug(3))*_u4)),_u5,_u6,_u7,_u8,_u9,_ua,_ub,_uc,_ud,_ue,_uf,_m6,_vj,_vj);});},_vl=1,_vm=function(_vn){var _vo=I_decodeDouble(_vn);return new T2(0,new T1(1,_vo.b),_vo.a);},_vp=function(_vq){return new T1(0,_vq);},_vr=function(_vs){var _vt=hs_intToInt64(2147483647),_vu=hs_leInt64(_vs,_vt);if(!_vu){return new T1(1,I_fromInt64(_vs));}else{var _vv=hs_intToInt64(-2147483648),_vw=hs_geInt64(_vs,_vv);if(!_vw){return new T1(1,I_fromInt64(_vs));}else{var _vx=hs_int64ToInt(_vs);return new F(function(){return _vp(_vx);});}}},_vy=new T(function(){var _vz=newByteArr(256),_vA=_vz,_=_vA["v"]["i8"][0]=8,_vB=function(_vC,_vD,_vE,_){while(1){if(_vE>=256){if(_vC>=256){return E(_);}else{var _vF=imul(2,_vC)|0,_vG=_vD+1|0,_vH=_vC;_vC=_vF;_vD=_vG;_vE=_vH;continue;}}else{var _=_vA["v"]["i8"][_vE]=_vD,_vH=_vE+_vC|0;_vE=_vH;continue;}}},_=B(_vB(2,0,1,_));return _vA;}),_vI=function(_vJ,_vK){var _vL=hs_int64ToInt(_vJ),_vM=E(_vy),_vN=_vM["v"]["i8"][(255&_vL>>>0)>>>0&4294967295];if(_vK>_vN){if(_vN>=8){var _vO=hs_uncheckedIShiftRA64(_vJ,8),_vP=function(_vQ,_vR){while(1){var _vS=B((function(_vT,_vU){var _vV=hs_int64ToInt(_vT),_vW=_vM["v"]["i8"][(255&_vV>>>0)>>>0&4294967295];if(_vU>_vW){if(_vW>=8){var _vX=hs_uncheckedIShiftRA64(_vT,8),_vY=_vU-8|0;_vQ=_vX;_vR=_vY;return __continue;}else{return new T2(0,new T(function(){var _vZ=hs_uncheckedIShiftRA64(_vT,_vW);return B(_vr(_vZ));}),_vU-_vW|0);}}else{return new T2(0,new T(function(){var _w0=hs_uncheckedIShiftRA64(_vT,_vU);return B(_vr(_w0));}),0);}})(_vQ,_vR));if(_vS!=__continue){return _vS;}}};return new F(function(){return _vP(_vO,_vK-8|0);});}else{return new T2(0,new T(function(){var _w1=hs_uncheckedIShiftRA64(_vJ,_vN);return B(_vr(_w1));}),_vK-_vN|0);}}else{return new T2(0,new T(function(){var _w2=hs_uncheckedIShiftRA64(_vJ,_vK);return B(_vr(_w2));}),0);}},_w3=function(_w4){var _w5=hs_intToInt64(_w4);return E(_w5);},_w6=function(_w7){var _w8=E(_w7);if(!_w8._){return new F(function(){return _w3(_w8.a);});}else{return new F(function(){return I_toInt64(_w8.a);});}},_w9=function(_wa){return I_toInt(_wa)>>>0;},_wb=function(_wc){var _wd=E(_wc);if(!_wd._){return _wd.a>>>0;}else{return new F(function(){return _w9(_wd.a);});}},_we=function(_wf){var _wg=B(_vm(_wf)),_wh=_wg.a,_wi=_wg.b;if(_wi<0){var _wj=function(_wk){if(!_wk){return new T2(0,E(_wh),B(_3J(_21, -_wi)));}else{var _wl=B(_vI(B(_w6(_wh)), -_wi));return new T2(0,E(_wl.a),B(_3J(_21,_wl.b)));}};if(!((B(_wb(_wh))&1)>>>0)){return new F(function(){return _wj(1);});}else{return new F(function(){return _wj(0);});}}else{return new T2(0,B(_3J(_wh,_wi)),_21);}},_wm=function(_wn){var _wo=B(_we(E(_wn)));return new T2(0,E(_wo.a),E(_wo.b));},_wp=new T3(0,_n4,_o9,_wm),_wq=function(_wr){return E(E(_wr).a);},_ws=function(_wt){return E(E(_wt).a);},_wu=function(_wv,_ww){if(_wv<=_ww){var _wx=function(_wy){return new T2(1,_wy,new T(function(){if(_wy!=_ww){return B(_wx(_wy+1|0));}else{return __Z;}}));};return new F(function(){return _wx(_wv);});}else{return __Z;}},_wz=function(_wA){return new F(function(){return _wu(E(_wA),2147483647);});},_wB=function(_wC,_wD,_wE){if(_wE<=_wD){var _wF=new T(function(){var _wG=_wD-_wC|0,_wH=function(_wI){return (_wI>=(_wE-_wG|0))?new T2(1,_wI,new T(function(){return B(_wH(_wI+_wG|0));})):new T2(1,_wI,_w);};return B(_wH(_wD));});return new T2(1,_wC,_wF);}else{return (_wE<=_wC)?new T2(1,_wC,_w):__Z;}},_wJ=function(_wK,_wL,_wM){if(_wM>=_wL){var _wN=new T(function(){var _wO=_wL-_wK|0,_wP=function(_wQ){return (_wQ<=(_wM-_wO|0))?new T2(1,_wQ,new T(function(){return B(_wP(_wQ+_wO|0));})):new T2(1,_wQ,_w);};return B(_wP(_wL));});return new T2(1,_wK,_wN);}else{return (_wM>=_wK)?new T2(1,_wK,_w):__Z;}},_wR=function(_wS,_wT){if(_wT<_wS){return new F(function(){return _wB(_wS,_wT,-2147483648);});}else{return new F(function(){return _wJ(_wS,_wT,2147483647);});}},_wU=function(_wV,_wW){return new F(function(){return _wR(E(_wV),E(_wW));});},_wX=function(_wY,_wZ,_x0){if(_wZ<_wY){return new F(function(){return _wB(_wY,_wZ,_x0);});}else{return new F(function(){return _wJ(_wY,_wZ,_x0);});}},_x1=function(_x2,_x3,_x4){return new F(function(){return _wX(E(_x2),E(_x3),E(_x4));});},_x5=function(_x6,_x7){return new F(function(){return _wu(E(_x6),E(_x7));});},_x8=function(_x9){return E(_x9);},_xa=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_xb=new T(function(){return B(err(_xa));}),_xc=function(_xd){var _xe=E(_xd);return (_xe==(-2147483648))?E(_xb):_xe-1|0;},_xf=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_xg=new T(function(){return B(err(_xf));}),_xh=function(_xi){var _xj=E(_xi);return (_xj==2147483647)?E(_xg):_xj+1|0;},_xk={_:0,a:_xh,b:_xc,c:_x8,d:_x8,e:_wz,f:_wU,g:_x5,h:_x1},_xl=function(_xm,_xn){if(_xm<=0){if(_xm>=0){return new F(function(){return quot(_xm,_xn);});}else{if(_xn<=0){return new F(function(){return quot(_xm,_xn);});}else{return quot(_xm+1|0,_xn)-1|0;}}}else{if(_xn>=0){if(_xm>=0){return new F(function(){return quot(_xm,_xn);});}else{if(_xn<=0){return new F(function(){return quot(_xm,_xn);});}else{return quot(_xm+1|0,_xn)-1|0;}}}else{return quot(_xm-1|0,_xn)-1|0;}}},_xo=0,_xp=new T(function(){return B(_36(_xo));}),_xq=new T(function(){return die(_xp);}),_xr=function(_xs,_xt){var _xu=E(_xt);switch(_xu){case -1:var _xv=E(_xs);if(_xv==(-2147483648)){return E(_xq);}else{return new F(function(){return _xl(_xv,-1);});}break;case 0:return E(_3a);default:return new F(function(){return _xl(_xs,_xu);});}},_xw=function(_xx,_xy){return new F(function(){return _xr(E(_xx),E(_xy));});},_xz=0,_xA=new T2(0,_xq,_xz),_xB=function(_xC,_xD){var _xE=E(_xC),_xF=E(_xD);switch(_xF){case -1:var _xG=E(_xE);if(_xG==(-2147483648)){return E(_xA);}else{if(_xG<=0){if(_xG>=0){var _xH=quotRemI(_xG,-1);return new T2(0,_xH.a,_xH.b);}else{var _xI=quotRemI(_xG,-1);return new T2(0,_xI.a,_xI.b);}}else{var _xJ=quotRemI(_xG-1|0,-1);return new T2(0,_xJ.a-1|0,(_xJ.b+(-1)|0)+1|0);}}break;case 0:return E(_3a);default:if(_xE<=0){if(_xE>=0){var _xK=quotRemI(_xE,_xF);return new T2(0,_xK.a,_xK.b);}else{if(_xF<=0){var _xL=quotRemI(_xE,_xF);return new T2(0,_xL.a,_xL.b);}else{var _xM=quotRemI(_xE+1|0,_xF);return new T2(0,_xM.a-1|0,(_xM.b+_xF|0)-1|0);}}}else{if(_xF>=0){if(_xE>=0){var _xN=quotRemI(_xE,_xF);return new T2(0,_xN.a,_xN.b);}else{if(_xF<=0){var _xO=quotRemI(_xE,_xF);return new T2(0,_xO.a,_xO.b);}else{var _xP=quotRemI(_xE+1|0,_xF);return new T2(0,_xP.a-1|0,(_xP.b+_xF|0)-1|0);}}}else{var _xQ=quotRemI(_xE-1|0,_xF);return new T2(0,_xQ.a-1|0,(_xQ.b+_xF|0)+1|0);}}}},_xR=function(_xS,_xT){var _xU=_xS%_xT;if(_xS<=0){if(_xS>=0){return E(_xU);}else{if(_xT<=0){return E(_xU);}else{var _xV=E(_xU);return (_xV==0)?0:_xV+_xT|0;}}}else{if(_xT>=0){if(_xS>=0){return E(_xU);}else{if(_xT<=0){return E(_xU);}else{var _xW=E(_xU);return (_xW==0)?0:_xW+_xT|0;}}}else{var _xX=E(_xU);return (_xX==0)?0:_xX+_xT|0;}}},_xY=function(_xZ,_y0){var _y1=E(_y0);switch(_y1){case -1:return E(_xz);case 0:return E(_3a);default:return new F(function(){return _xR(E(_xZ),_y1);});}},_y2=function(_y3,_y4){var _y5=E(_y3),_y6=E(_y4);switch(_y6){case -1:var _y7=E(_y5);if(_y7==(-2147483648)){return E(_xq);}else{return new F(function(){return quot(_y7,-1);});}break;case 0:return E(_3a);default:return new F(function(){return quot(_y5,_y6);});}},_y8=function(_y9,_ya){var _yb=E(_y9),_yc=E(_ya);switch(_yc){case -1:var _yd=E(_yb);if(_yd==(-2147483648)){return E(_xA);}else{var _ye=quotRemI(_yd,-1);return new T2(0,_ye.a,_ye.b);}break;case 0:return E(_3a);default:var _yf=quotRemI(_yb,_yc);return new T2(0,_yf.a,_yf.b);}},_yg=function(_yh,_yi){var _yj=E(_yi);switch(_yj){case -1:return E(_xz);case 0:return E(_3a);default:return E(_yh)%_yj;}},_yk=function(_yl){return new F(function(){return _vp(E(_yl));});},_ym=function(_yn){return new T2(0,E(B(_vp(E(_yn)))),E(_rh));},_yo=function(_yp,_yq){return imul(E(_yp),E(_yq))|0;},_yr=function(_ys,_yt){return E(_ys)+E(_yt)|0;},_yu=function(_yv,_yw){return E(_yv)-E(_yw)|0;},_yx=function(_yy){var _yz=E(_yy);return (_yz<0)? -_yz:E(_yz);},_yA=function(_yB){return new F(function(){return _3n(_yB);});},_yC=function(_yD){return  -E(_yD);},_yE=-1,_yF=0,_yG=1,_yH=function(_yI){var _yJ=E(_yI);return (_yJ>=0)?(E(_yJ)==0)?E(_yF):E(_yG):E(_yE);},_yK={_:0,a:_yr,b:_yu,c:_yo,d:_yC,e:_yx,f:_yH,g:_yA},_yL=function(_yM,_yN){return E(_yM)==E(_yN);},_yO=function(_yP,_yQ){return E(_yP)!=E(_yQ);},_yR=new T2(0,_yL,_yO),_yS=function(_yT,_yU){var _yV=E(_yT),_yW=E(_yU);return (_yV>_yW)?E(_yV):E(_yW);},_yX=function(_yY,_yZ){var _z0=E(_yY),_z1=E(_yZ);return (_z0>_z1)?E(_z1):E(_z0);},_z2=function(_z3,_z4){return (_z3>=_z4)?(_z3!=_z4)?2:1:0;},_z5=function(_z6,_z7){return new F(function(){return _z2(E(_z6),E(_z7));});},_z8=function(_z9,_za){return E(_z9)>=E(_za);},_zb=function(_zc,_zd){return E(_zc)>E(_zd);},_ze=function(_zf,_zg){return E(_zf)<=E(_zg);},_zh=function(_zi,_zj){return E(_zi)<E(_zj);},_zk={_:0,a:_yR,b:_z5,c:_zh,d:_ze,e:_zb,f:_z8,g:_yS,h:_yX},_zl=new T3(0,_yK,_zk,_ym),_zm={_:0,a:_zl,b:_xk,c:_y2,d:_yg,e:_xw,f:_xY,g:_y8,h:_xB,i:_yk},_zn=new T1(0,2),_zo=function(_zp,_zq){while(1){var _zr=E(_zp);if(!_zr._){var _zs=_zr.a,_zt=E(_zq);if(!_zt._){var _zu=_zt.a;if(!(imul(_zs,_zu)|0)){return new T1(0,imul(_zs,_zu)|0);}else{_zp=new T1(1,I_fromInt(_zs));_zq=new T1(1,I_fromInt(_zu));continue;}}else{_zp=new T1(1,I_fromInt(_zs));_zq=_zt;continue;}}else{var _zv=E(_zq);if(!_zv._){_zp=_zr;_zq=new T1(1,I_fromInt(_zv.a));continue;}else{return new T1(1,I_mul(_zr.a,_zv.a));}}}},_zw=function(_zx,_zy,_zz){while(1){if(!(_zy%2)){var _zA=B(_zo(_zx,_zx)),_zB=quot(_zy,2);_zx=_zA;_zy=_zB;continue;}else{var _zC=E(_zy);if(_zC==1){return new F(function(){return _zo(_zx,_zz);});}else{var _zA=B(_zo(_zx,_zx)),_zD=B(_zo(_zx,_zz));_zx=_zA;_zy=quot(_zC-1|0,2);_zz=_zD;continue;}}}},_zE=function(_zF,_zG){while(1){if(!(_zG%2)){var _zH=B(_zo(_zF,_zF)),_zI=quot(_zG,2);_zF=_zH;_zG=_zI;continue;}else{var _zJ=E(_zG);if(_zJ==1){return E(_zF);}else{return new F(function(){return _zw(B(_zo(_zF,_zF)),quot(_zJ-1|0,2),_zF);});}}}},_zK=function(_zL){return E(E(_zL).b);},_zM=function(_zN){return E(E(_zN).c);},_zO=new T1(0,0),_zP=function(_zQ){return E(E(_zQ).d);},_zR=function(_zS,_zT){var _zU=B(_wq(_zS)),_zV=new T(function(){return B(_ws(_zU));}),_zW=new T(function(){return B(A3(_zP,_zS,_zT,new T(function(){return B(A2(_8s,_zV,_rr));})));});return new F(function(){return A3(_qc,B(_pY(B(_zK(_zU)))),_zW,new T(function(){return B(A2(_8s,_zV,_zO));}));});},_zX=new T(function(){return B(unCStr("Negative exponent"));}),_zY=new T(function(){return B(err(_zX));}),_zZ=function(_A0){return E(E(_A0).c);},_A1=function(_A2,_A3,_A4,_A5){var _A6=B(_wq(_A3)),_A7=new T(function(){return B(_ws(_A6));}),_A8=B(_zK(_A6));if(!B(A3(_zM,_A8,_A5,new T(function(){return B(A2(_8s,_A7,_zO));})))){if(!B(A3(_qc,B(_pY(_A8)),_A5,new T(function(){return B(A2(_8s,_A7,_zO));})))){var _A9=new T(function(){return B(A2(_8s,_A7,_rr));}),_Aa=new T(function(){return B(A2(_8s,_A7,_rh));}),_Ab=B(_pY(_A8)),_Ac=function(_Ad,_Ae,_Af){while(1){var _Ag=B((function(_Ah,_Ai,_Aj){if(!B(_zR(_A3,_Ai))){if(!B(A3(_qc,_Ab,_Ai,_Aa))){var _Ak=new T(function(){return B(A3(_zZ,_A3,new T(function(){return B(A3(_9p,_A7,_Ai,_Aa));}),_A9));});_Ad=new T(function(){return B(A3(_8L,_A2,_Ah,_Ah));});_Ae=_Ak;_Af=new T(function(){return B(A3(_8L,_A2,_Ah,_Aj));});return __continue;}else{return new F(function(){return A3(_8L,_A2,_Ah,_Aj);});}}else{var _Al=_Aj;_Ad=new T(function(){return B(A3(_8L,_A2,_Ah,_Ah));});_Ae=new T(function(){return B(A3(_zZ,_A3,_Ai,_A9));});_Af=_Al;return __continue;}})(_Ad,_Ae,_Af));if(_Ag!=__continue){return _Ag;}}},_Am=function(_An,_Ao){while(1){var _Ap=B((function(_Aq,_Ar){if(!B(_zR(_A3,_Ar))){if(!B(A3(_qc,_Ab,_Ar,_Aa))){var _As=new T(function(){return B(A3(_zZ,_A3,new T(function(){return B(A3(_9p,_A7,_Ar,_Aa));}),_A9));});return new F(function(){return _Ac(new T(function(){return B(A3(_8L,_A2,_Aq,_Aq));}),_As,_Aq);});}else{return E(_Aq);}}else{_An=new T(function(){return B(A3(_8L,_A2,_Aq,_Aq));});_Ao=new T(function(){return B(A3(_zZ,_A3,_Ar,_A9));});return __continue;}})(_An,_Ao));if(_Ap!=__continue){return _Ap;}}};return new F(function(){return _Am(_A4,_A5);});}else{return new F(function(){return A2(_8s,_A2,_rh);});}}else{return E(_zY);}},_At=new T(function(){return B(err(_zX));}),_Au=function(_Av,_Aw){var _Ax=B(_vm(_Aw)),_Ay=_Ax.a,_Az=_Ax.b,_AA=new T(function(){return B(_ws(new T(function(){return B(_wq(_Av));})));});if(_Az<0){var _AB= -_Az;if(_AB>=0){var _AC=E(_AB);if(!_AC){var _AD=E(_rh);}else{var _AD=B(_zE(_zn,_AC));}if(!B(_3f(_AD,_3I))){var _AE=B(_3z(_Ay,_AD));return new T2(0,new T(function(){return B(A2(_8s,_AA,_AE.a));}),new T(function(){return B(_3b(_AE.b,_Az));}));}else{return E(_3a);}}else{return E(_At);}}else{var _AF=new T(function(){var _AG=new T(function(){return B(_A1(_AA,_zm,new T(function(){return B(A2(_8s,_AA,_zn));}),_Az));});return B(A3(_8L,_AA,new T(function(){return B(A2(_8s,_AA,_Ay));}),_AG));});return new T2(0,_AF,_6x);}},_AH=function(_AI,_AJ){var _AK=B(_Au(_AI,E(_AJ))),_AL=_AK.a;if(E(_AK.b)<=0){return E(_AL);}else{var _AM=B(_ws(B(_wq(_AI))));return new F(function(){return A3(_6X,_AM,_AL,new T(function(){return B(A2(_8s,_AM,_21));}));});}},_AN=function(_AO,_AP){var _AQ=B(_Au(_AO,E(_AP))),_AR=_AQ.a;if(E(_AQ.b)>=0){return E(_AR);}else{var _AS=B(_ws(B(_wq(_AO))));return new F(function(){return A3(_9p,_AS,_AR,new T(function(){return B(A2(_8s,_AS,_21));}));});}},_AT=function(_AU,_AV){var _AW=B(_Au(_AU,E(_AV)));return new T2(0,_AW.a,_AW.b);},_AX=function(_AY,_AZ){var _B0=B(_Au(_AY,_AZ)),_B1=_B0.a,_B2=E(_B0.b),_B3=new T(function(){var _B4=B(_ws(B(_wq(_AY))));if(_B2>=0){return B(A3(_6X,_B4,_B1,new T(function(){return B(A2(_8s,_B4,_21));})));}else{return B(A3(_9p,_B4,_B1,new T(function(){return B(A2(_8s,_B4,_21));})));}}),_B5=function(_B6){var _B7=_B6-0.5;return (_B7>=0)?(E(_B7)==0)?(!B(_zR(_AY,_B1)))?E(_B3):E(_B1):E(_B3):E(_B1);},_B8=E(_B2);if(!_B8){return new F(function(){return _B5(0);});}else{if(_B8<=0){var _B9= -_B8-0.5;return (_B9>=0)?(E(_B9)==0)?(!B(_zR(_AY,_B1)))?E(_B3):E(_B1):E(_B3):E(_B1);}else{return new F(function(){return _B5(_B8);});}}},_Ba=function(_Bb,_Bc){return new F(function(){return _AX(_Bb,E(_Bc));});},_Bd=function(_Be,_Bf){return E(B(_Au(_Be,E(_Bf))).a);},_Bg={_:0,a:_wp,b:_n8,c:_AT,d:_Bd,e:_Ba,f:_AH,g:_AN},_Bh=new T1(0,1),_Bi=function(_Bj,_Bk){var _Bl=E(_Bj);return new T2(0,_Bl,new T(function(){var _Bm=B(_Bi(B(_3q(_Bl,_Bk)),_Bk));return new T2(1,_Bm.a,_Bm.b);}));},_Bn=function(_Bo){var _Bp=B(_Bi(_Bo,_Bh));return new T2(1,_Bp.a,_Bp.b);},_Bq=function(_Br,_Bs){var _Bt=B(_Bi(_Br,new T(function(){return B(_5L(_Bs,_Br));})));return new T2(1,_Bt.a,_Bt.b);},_Bu=new T1(0,0),_Bv=function(_Bw,_Bx){var _By=E(_Bw);if(!_By._){var _Bz=_By.a,_BA=E(_Bx);return (_BA._==0)?_Bz>=_BA.a:I_compareInt(_BA.a,_Bz)<=0;}else{var _BB=_By.a,_BC=E(_Bx);return (_BC._==0)?I_compareInt(_BB,_BC.a)>=0:I_compare(_BB,_BC.a)>=0;}},_BD=function(_BE,_BF,_BG){if(!B(_Bv(_BF,_Bu))){var _BH=function(_BI){return (!B(_42(_BI,_BG)))?new T2(1,_BI,new T(function(){return B(_BH(B(_3q(_BI,_BF))));})):__Z;};return new F(function(){return _BH(_BE);});}else{var _BJ=function(_BK){return (!B(_3T(_BK,_BG)))?new T2(1,_BK,new T(function(){return B(_BJ(B(_3q(_BK,_BF))));})):__Z;};return new F(function(){return _BJ(_BE);});}},_BL=function(_BM,_BN,_BO){return new F(function(){return _BD(_BM,B(_5L(_BN,_BM)),_BO);});},_BP=function(_BQ,_BR){return new F(function(){return _BD(_BQ,_Bh,_BR);});},_BS=function(_BT){return new F(function(){return _3n(_BT);});},_BU=function(_BV){return new F(function(){return _5L(_BV,_Bh);});},_BW=function(_BX){return new F(function(){return _3q(_BX,_Bh);});},_BY=function(_BZ){return new F(function(){return _vp(E(_BZ));});},_C0={_:0,a:_BW,b:_BU,c:_BY,d:_BS,e:_Bn,f:_Bq,g:_BP,h:_BL},_C1=function(_C2,_C3){while(1){var _C4=E(_C2);if(!_C4._){var _C5=E(_C4.a);if(_C5==(-2147483648)){_C2=new T1(1,I_fromInt(-2147483648));continue;}else{var _C6=E(_C3);if(!_C6._){return new T1(0,B(_xl(_C5,_C6.a)));}else{_C2=new T1(1,I_fromInt(_C5));_C3=_C6;continue;}}}else{var _C7=_C4.a,_C8=E(_C3);return (_C8._==0)?new T1(1,I_div(_C7,I_fromInt(_C8.a))):new T1(1,I_div(_C7,_C8.a));}}},_C9=function(_Ca,_Cb){if(!B(_3f(_Cb,_zO))){return new F(function(){return _C1(_Ca,_Cb);});}else{return E(_3a);}},_Cc=function(_Cd,_Ce){while(1){var _Cf=E(_Cd);if(!_Cf._){var _Cg=E(_Cf.a);if(_Cg==(-2147483648)){_Cd=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ch=E(_Ce);if(!_Ch._){var _Ci=_Ch.a;return new T2(0,new T1(0,B(_xl(_Cg,_Ci))),new T1(0,B(_xR(_Cg,_Ci))));}else{_Cd=new T1(1,I_fromInt(_Cg));_Ce=_Ch;continue;}}}else{var _Cj=E(_Ce);if(!_Cj._){_Cd=_Cf;_Ce=new T1(1,I_fromInt(_Cj.a));continue;}else{var _Ck=I_divMod(_Cf.a,_Cj.a);return new T2(0,new T1(1,_Ck.a),new T1(1,_Ck.b));}}}},_Cl=function(_Cm,_Cn){if(!B(_3f(_Cn,_zO))){var _Co=B(_Cc(_Cm,_Cn));return new T2(0,_Co.a,_Co.b);}else{return E(_3a);}},_Cp=function(_Cq,_Cr){while(1){var _Cs=E(_Cq);if(!_Cs._){var _Ct=E(_Cs.a);if(_Ct==(-2147483648)){_Cq=new T1(1,I_fromInt(-2147483648));continue;}else{var _Cu=E(_Cr);if(!_Cu._){return new T1(0,B(_xR(_Ct,_Cu.a)));}else{_Cq=new T1(1,I_fromInt(_Ct));_Cr=_Cu;continue;}}}else{var _Cv=_Cs.a,_Cw=E(_Cr);return (_Cw._==0)?new T1(1,I_mod(_Cv,I_fromInt(_Cw.a))):new T1(1,I_mod(_Cv,_Cw.a));}}},_Cx=function(_Cy,_Cz){if(!B(_3f(_Cz,_zO))){return new F(function(){return _Cp(_Cy,_Cz);});}else{return E(_3a);}},_CA=function(_CB,_CC){while(1){var _CD=E(_CB);if(!_CD._){var _CE=E(_CD.a);if(_CE==(-2147483648)){_CB=new T1(1,I_fromInt(-2147483648));continue;}else{var _CF=E(_CC);if(!_CF._){return new T1(0,quot(_CE,_CF.a));}else{_CB=new T1(1,I_fromInt(_CE));_CC=_CF;continue;}}}else{var _CG=_CD.a,_CH=E(_CC);return (_CH._==0)?new T1(0,I_toInt(I_quot(_CG,I_fromInt(_CH.a)))):new T1(1,I_quot(_CG,_CH.a));}}},_CI=function(_CJ,_CK){if(!B(_3f(_CK,_zO))){return new F(function(){return _CA(_CJ,_CK);});}else{return E(_3a);}},_CL=function(_CM,_CN){if(!B(_3f(_CN,_zO))){var _CO=B(_3z(_CM,_CN));return new T2(0,_CO.a,_CO.b);}else{return E(_3a);}},_CP=function(_CQ,_CR){while(1){var _CS=E(_CQ);if(!_CS._){var _CT=E(_CS.a);if(_CT==(-2147483648)){_CQ=new T1(1,I_fromInt(-2147483648));continue;}else{var _CU=E(_CR);if(!_CU._){return new T1(0,_CT%_CU.a);}else{_CQ=new T1(1,I_fromInt(_CT));_CR=_CU;continue;}}}else{var _CV=_CS.a,_CW=E(_CR);return (_CW._==0)?new T1(1,I_rem(_CV,I_fromInt(_CW.a))):new T1(1,I_rem(_CV,_CW.a));}}},_CX=function(_CY,_CZ){if(!B(_3f(_CZ,_zO))){return new F(function(){return _CP(_CY,_CZ);});}else{return E(_3a);}},_D0=function(_D1){return E(_D1);},_D2=function(_D3){return E(_D3);},_D4=function(_D5){var _D6=E(_D5);if(!_D6._){var _D7=E(_D6.a);return (_D7==(-2147483648))?E(_6p):(_D7<0)?new T1(0, -_D7):E(_D6);}else{var _D8=_D6.a;return (I_compareInt(_D8,0)>=0)?E(_D6):new T1(1,I_negate(_D8));}},_D9=new T1(0,0),_Da=new T1(0,-1),_Db=function(_Dc){var _Dd=E(_Dc);if(!_Dd._){var _De=_Dd.a;return (_De>=0)?(E(_De)==0)?E(_D9):E(_41):E(_Da);}else{var _Df=I_compareInt(_Dd.a,0);return (_Df<=0)?(E(_Df)==0)?E(_D9):E(_Da):E(_41);}},_Dg={_:0,a:_3q,b:_5L,c:_zo,d:_6q,e:_D4,f:_Db,g:_D2},_Dh=function(_Di,_Dj){var _Dk=E(_Di);if(!_Dk._){var _Dl=_Dk.a,_Dm=E(_Dj);return (_Dm._==0)?_Dl!=_Dm.a:(I_compareInt(_Dm.a,_Dl)==0)?false:true;}else{var _Dn=_Dk.a,_Do=E(_Dj);return (_Do._==0)?(I_compareInt(_Dn,_Do.a)==0)?false:true:(I_compare(_Dn,_Do.a)==0)?false:true;}},_Dp=new T2(0,_3f,_Dh),_Dq=function(_Dr,_Ds){return (!B(_5w(_Dr,_Ds)))?E(_Dr):E(_Ds);},_Dt=function(_Du,_Dv){return (!B(_5w(_Du,_Dv)))?E(_Dv):E(_Du);},_Dw={_:0,a:_Dp,b:_22,c:_42,d:_5w,e:_3T,f:_Bv,g:_Dq,h:_Dt},_Dx=function(_Dy){return new T2(0,E(_Dy),E(_rh));},_Dz=new T3(0,_Dg,_Dw,_Dx),_DA={_:0,a:_Dz,b:_C0,c:_CI,d:_CX,e:_C9,f:_Cx,g:_CL,h:_Cl,i:_D0},_DB=function(_DC){return E(E(_DC).b);},_DD=function(_DE){return E(E(_DE).g);},_DF=new T1(0,1),_DG=function(_DH,_DI,_DJ){var _DK=B(_DB(_DH)),_DL=B(_8J(_DK)),_DM=new T(function(){var _DN=new T(function(){var _DO=new T(function(){var _DP=new T(function(){return B(A3(_DD,_DH,_DA,new T(function(){return B(A3(_8P,_DK,_DI,_DJ));})));});return B(A2(_8s,_DL,_DP));}),_DQ=new T(function(){return B(A2(_6Z,_DL,new T(function(){return B(A2(_8s,_DL,_DF));})));});return B(A3(_8L,_DL,_DQ,_DO));});return B(A3(_8L,_DL,_DN,_DJ));});return new F(function(){return A3(_6X,_DL,_DI,_DM);});},_DR=1.5707963267948966,_DS=function(_DT){return 0.2/Math.cos(B(_DG(_Bg,_DT,_DR))-0.7853981633974483);},_DU=0,_DV=new T(function(){var _DW=B(_u2(_DS,1.2,_DU,_DU,_vl,_DU,_DU,_DU,_DU,_DU,_vl,_vl,_vl));return {_:0,a:E(_DW.a),b:E(_DW.b),c:E(_DW.c),d:E(_DW.d),e:E(_DW.e),f:E(_DW.f),g:E(_DW.g),h:_DW.h,i:_DW.i};}),_DX=0,_DY=0.3,_DZ=function(_E0){return E(_DY);},_E1=new T(function(){var _E2=B(_u2(_DZ,1.2,_vl,_DU,_vl,_DU,_DU,_DU,_DU,_DU,_vl,_vl,_vl));return {_:0,a:E(_E2.a),b:E(_E2.b),c:E(_E2.c),d:E(_E2.d),e:E(_E2.e),f:E(_E2.f),g:E(_E2.g),h:_E2.h,i:_E2.i};}),_E3=new T(function(){var _E4=B(_u2(_DZ,1.2,_vl,_vl,_DU,_DU,_DU,_DU,_DU,_DU,_vl,_vl,_vl));return {_:0,a:E(_E4.a),b:E(_E4.b),c:E(_E4.c),d:E(_E4.d),e:E(_E4.e),f:E(_E4.f),g:E(_E4.g),h:_E4.h,i:_E4.i};}),_E5=2,_E6=function(_E7){return 0.3/Math.cos(B(_DG(_Bg,_E7,_DR))-0.7853981633974483);},_E8=new T(function(){var _E9=B(_u2(_E6,1.2,_E5,_vl,_vl,_DU,_DU,_DU,_DU,_DU,_vl,_vl,_vl));return {_:0,a:E(_E9.a),b:E(_E9.b),c:E(_E9.c),d:E(_E9.d),e:E(_E9.e),f:E(_E9.f),g:E(_E9.g),h:_E9.h,i:_E9.i};}),_Ea=new T2(1,_E8,_w),_Eb=new T2(1,_E3,_Ea),_Ec=new T2(1,_E1,_Eb),_Ed=new T2(1,_DV,_Ec),_Ee=new T(function(){return B(unCStr("Negative range size"));}),_Ef=new T(function(){return B(err(_Ee));}),_Eg=function(_){var _Eh=B(_lY(_Ed,0))-1|0,_Ei=function(_Ej){if(_Ej>=0){var _Ek=newArr(_Ej,_m4),_El=_Ek,_Em=E(_Ej);if(!_Em){return new T4(0,E(_DX),E(_Eh),0,_El);}else{var _En=function(_Eo,_Ep,_){while(1){var _Eq=E(_Eo);if(!_Eq._){return E(_);}else{var _=_El[_Ep]=_Eq.a;if(_Ep!=(_Em-1|0)){var _Er=_Ep+1|0;_Eo=_Eq.b;_Ep=_Er;continue;}else{return E(_);}}}},_=B((function(_Es,_Et,_Eu,_){var _=_El[_Eu]=_Es;if(_Eu!=(_Em-1|0)){return new F(function(){return _En(_Et,_Eu+1|0,_);});}else{return E(_);}})(_DV,_Ec,0,_));return new T4(0,E(_DX),E(_Eh),_Em,_El);}}else{return E(_Ef);}};if(0>_Eh){return new F(function(){return _Ei(0);});}else{return new F(function(){return _Ei(_Eh+1|0);});}},_Ev=function(_Ew){var _Ex=B(A1(_Ew,_));return E(_Ex);},_Ey=new T(function(){return B(_Ev(_Eg));}),_Ez="outline",_EA="polygon",_EB=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_EC=new T(function(){return B(err(_EB));}),_ED=new T(function(){return eval("__strict(drawObjects)");}),_EE=new T(function(){return eval("__strict(draw)");}),_EF=function(_EG,_EH){var _EI=jsShowI(_EG);return new F(function(){return _n(fromJSStr(_EI),_EH);});},_EJ=function(_EK,_EL,_EM){if(_EL>=0){return new F(function(){return _EF(_EL,_EM);});}else{if(_EK<=6){return new F(function(){return _EF(_EL,_EM);});}else{return new T2(1,_7g,new T(function(){var _EN=jsShowI(_EL);return B(_n(fromJSStr(_EN),new T2(1,_7f,_EM)));}));}}},_EO=new T(function(){return B(unCStr(")"));}),_EP=function(_EQ,_ER){var _ES=new T(function(){var _ET=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_EJ(0,_EQ,_w)),_EO));})));},1);return B(_n(B(_EJ(0,_ER,_w)),_ET));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_ES)));});},_EU=new T2(1,_ol,_w),_EV=function(_EW){return E(_EW);},_EX=function(_EY){return E(_EY);},_EZ=function(_F0,_F1){return E(_F1);},_F2=function(_F3,_F4){return E(_F3);},_F5=function(_F6){return E(_F6);},_F7=new T2(0,_F5,_F2),_F8=function(_F9,_Fa){return E(_F9);},_Fb=new T5(0,_F7,_EX,_EV,_EZ,_F8),_Fc="flipped2",_Fd="flipped1",_Fe="c1y",_Ff="c1x",_Fg="w2z",_Fh="w2y",_Fi="w2x",_Fj="w1z",_Fk="w1y",_Fl="w1x",_Fm="d2z",_Fn="d2y",_Fo="d2x",_Fp="d1z",_Fq="d1y",_Fr="d1x",_Fs="c2y",_Ft="c2x",_Fu=function(_Fv,_){var _Fw=__get(_Fv,E(_Fl)),_Fx=__get(_Fv,E(_Fk)),_Fy=__get(_Fv,E(_Fj)),_Fz=__get(_Fv,E(_Fi)),_FA=__get(_Fv,E(_Fh)),_FB=__get(_Fv,E(_Fg)),_FC=__get(_Fv,E(_Ff)),_FD=__get(_Fv,E(_Fe)),_FE=__get(_Fv,E(_Ft)),_FF=__get(_Fv,E(_Fs)),_FG=__get(_Fv,E(_Fr)),_FH=__get(_Fv,E(_Fq)),_FI=__get(_Fv,E(_Fp)),_FJ=__get(_Fv,E(_Fo)),_FK=__get(_Fv,E(_Fn)),_FL=__get(_Fv,E(_Fm)),_FM=__get(_Fv,E(_Fd)),_FN=__get(_Fv,E(_Fc));return {_:0,a:E(new T3(0,E(_Fw),E(_Fx),E(_Fy))),b:E(new T3(0,E(_Fz),E(_FA),E(_FB))),c:E(new T2(0,E(_FC),E(_FD))),d:E(new T2(0,E(_FE),E(_FF))),e:E(new T3(0,E(_FG),E(_FH),E(_FI))),f:E(new T3(0,E(_FJ),E(_FK),E(_FL))),g:E(_FM),h:E(_FN)};},_FO=function(_FP,_){var _FQ=E(_FP);if(!_FQ._){return _w;}else{var _FR=B(_Fu(E(_FQ.a),_)),_FS=B(_FO(_FQ.b,_));return new T2(1,_FR,_FS);}},_FT=function(_FU){var _FV=E(_FU);return (E(_FV.b)-E(_FV.a)|0)+1|0;},_FW=function(_FX,_FY){var _FZ=E(_FX),_G0=E(_FY);return (E(_FZ.a)>_G0)?false:_G0<=E(_FZ.b);},_G1=function(_G2){return new F(function(){return _EJ(0,E(_G2),_w);});},_G3=function(_G4,_G5,_G6){return new F(function(){return _EJ(E(_G4),E(_G5),_G6);});},_G7=function(_G8,_G9){return new F(function(){return _EJ(0,E(_G8),_G9);});},_Ga=function(_Gb,_Gc){return new F(function(){return _2Q(_G7,_Gb,_Gc);});},_Gd=new T3(0,_G3,_G1,_Ga),_Ge=0,_Gf=function(_Gg,_Gh,_Gi){return new F(function(){return A1(_Gg,new T2(1,_2N,new T(function(){return B(A1(_Gh,_Gi));})));});},_Gj=new T(function(){return B(unCStr("foldr1"));}),_Gk=new T(function(){return B(_qH(_Gj));}),_Gl=function(_Gm,_Gn){var _Go=E(_Gn);if(!_Go._){return E(_Gk);}else{var _Gp=_Go.a,_Gq=E(_Go.b);if(!_Gq._){return E(_Gp);}else{return new F(function(){return A2(_Gm,_Gp,new T(function(){return B(_Gl(_Gm,_Gq));}));});}}},_Gr=new T(function(){return B(unCStr(" out of range "));}),_Gs=new T(function(){return B(unCStr("}.index: Index "));}),_Gt=new T(function(){return B(unCStr("Ix{"));}),_Gu=new T2(1,_7f,_w),_Gv=new T2(1,_7f,_Gu),_Gw=0,_Gx=function(_Gy){return E(E(_Gy).a);},_Gz=function(_GA,_GB,_GC,_GD,_GE){var _GF=new T(function(){var _GG=new T(function(){var _GH=new T(function(){var _GI=new T(function(){var _GJ=new T(function(){return B(A3(_Gl,_Gf,new T2(1,new T(function(){return B(A3(_Gx,_GC,_Gw,_GD));}),new T2(1,new T(function(){return B(A3(_Gx,_GC,_Gw,_GE));}),_w)),_Gv));});return B(_n(_Gr,new T2(1,_7g,new T2(1,_7g,_GJ))));});return B(A(_Gx,[_GC,_Ge,_GB,new T2(1,_7f,_GI)]));});return B(_n(_Gs,new T2(1,_7g,_GH)));},1);return B(_n(_GA,_GG));},1);return new F(function(){return err(B(_n(_Gt,_GF)));});},_GK=function(_GL,_GM,_GN,_GO,_GP){return new F(function(){return _Gz(_GL,_GM,_GP,_GN,_GO);});},_GQ=function(_GR,_GS,_GT,_GU){var _GV=E(_GT);return new F(function(){return _GK(_GR,_GS,_GV.a,_GV.b,_GU);});},_GW=function(_GX,_GY,_GZ,_H0){return new F(function(){return _GQ(_H0,_GZ,_GY,_GX);});},_H1=new T(function(){return B(unCStr("Int"));}),_H2=function(_H3,_H4){return new F(function(){return _GW(_Gd,_H4,_H3,_H1);});},_H5=function(_H6,_H7){var _H8=E(_H6),_H9=E(_H8.a),_Ha=E(_H7);if(_H9>_Ha){return new F(function(){return _H2(_Ha,_H8);});}else{if(_Ha>E(_H8.b)){return new F(function(){return _H2(_Ha,_H8);});}else{return _Ha-_H9|0;}}},_Hb=function(_Hc){var _Hd=E(_Hc);return new F(function(){return _x5(_Hd.a,_Hd.b);});},_He=function(_Hf){var _Hg=E(_Hf),_Hh=E(_Hg.a),_Hi=E(_Hg.b);return (_Hh>_Hi)?E(_Ge):(_Hi-_Hh|0)+1|0;},_Hj=function(_Hk,_Hl){return new F(function(){return _yu(_Hl,E(_Hk).a);});},_Hm={_:0,a:_zk,b:_Hb,c:_H5,d:_Hj,e:_FW,f:_He,g:_FT},_Hn=function(_Ho,_Hp,_){while(1){var _Hq=B((function(_Hr,_Hs,_){var _Ht=E(_Hr);if(!_Ht._){return new T2(0,_ol,_Hs);}else{var _Hu=B(A2(_Ht.a,_Hs,_));_Ho=_Ht.b;_Hp=new T(function(){return E(E(_Hu).b);});return __continue;}})(_Ho,_Hp,_));if(_Hq!=__continue){return _Hq;}}},_Hv=function(_Hw,_Hx){return new T2(1,_Hw,_Hx);},_Hy=function(_Hz,_HA){var _HB=E(_HA);return new T2(0,_HB.a,_HB.b);},_HC=function(_HD){return E(E(_HD).f);},_HE=function(_HF,_HG,_HH){var _HI=E(_HG),_HJ=_HI.a,_HK=_HI.b,_HL=function(_){var _HM=B(A2(_HC,_HF,_HI));if(_HM>=0){var _HN=newArr(_HM,_m4),_HO=_HN,_HP=E(_HM);if(!_HP){return new T(function(){return new T4(0,E(_HJ),E(_HK),0,_HO);});}else{var _HQ=function(_HR,_HS,_){while(1){var _HT=E(_HR);if(!_HT._){return E(_);}else{var _=_HO[_HS]=_HT.a;if(_HS!=(_HP-1|0)){var _HU=_HS+1|0;_HR=_HT.b;_HS=_HU;continue;}else{return E(_);}}}},_=B(_HQ(_HH,0,_));return new T(function(){return new T4(0,E(_HJ),E(_HK),_HP,_HO);});}}else{return E(_Ef);}};return new F(function(){return _Ev(_HL);});},_HV=function(_HW,_HX,_HY,_HZ){var _I0=new T(function(){var _I1=E(_HZ),_I2=_I1.c-1|0,_I3=new T(function(){return B(A2(_cF,_HX,_w));});if(0<=_I2){var _I4=new T(function(){return B(_8F(_HX));}),_I5=function(_I6){var _I7=new T(function(){var _I8=new T(function(){return B(A1(_HY,new T(function(){return E(_I1.d[_I6]);})));});return B(A3(_8T,_I4,_Hv,_I8));});return new F(function(){return A3(_8R,_HX,_I7,new T(function(){if(_I6!=_I2){return B(_I5(_I6+1|0));}else{return E(_I3);}}));});};return B(_I5(0));}else{return E(_I3);}}),_I9=new T(function(){return B(_Hy(_HW,_HZ));});return new F(function(){return A3(_8T,B(_8F(_HX)),function(_Ia){return new F(function(){return _HE(_HW,_I9,_Ia);});},_I0);});},_Ib=function(_Ic,_Id,_Ie,_If,_Ig,_Ih,_Ii,_Ij,_Ik){var _Il=B(_8L(_Ic));return new T2(0,new T3(0,E(B(A1(B(A1(_Il,_Id)),_Ih))),E(B(A1(B(A1(_Il,_Ie)),_Ii))),E(B(A1(B(A1(_Il,_If)),_Ij)))),B(A1(B(A1(_Il,_Ig)),_Ik)));},_Im=function(_In,_Io,_Ip,_Iq,_Ir,_Is,_It,_Iu,_Iv){var _Iw=B(_6X(_In));return new T2(0,new T3(0,E(B(A1(B(A1(_Iw,_Io)),_Is))),E(B(A1(B(A1(_Iw,_Ip)),_It))),E(B(A1(B(A1(_Iw,_Iq)),_Iu)))),B(A1(B(A1(_Iw,_Ir)),_Iv)));},_Ix=1.0e-2,_Iy=function(_Iz,_IA,_IB,_IC,_ID,_IE,_IF,_IG,_IH,_II,_IJ,_IK,_IL,_IM,_IN,_IO,_IP){var _IQ=B(_Ib(_n4,_IG,_IH,_II,_IJ,_Ix,_Ix,_Ix,_Ix)),_IR=E(_IQ.a),_IS=B(_Im(_n4,_IC,_ID,_IE,_IF,_IR.a,_IR.b,_IR.c,_IQ.b)),_IT=E(_IS.a);return new F(function(){return _ti(_Iz,_IA,_IB,_IT.a,_IT.b,_IT.c,_IS.b,_IG,_IH,_II,_IJ,_IK,_IL,_IM,_IN,_IO,_IP);});},_IU=function(_IV){var _IW=E(_IV),_IX=E(_IW.d),_IY=E(_IX.a),_IZ=E(_IW.e),_J0=E(_IZ.a),_J1=E(_IW.f),_J2=B(_Iy(_IW.a,_IW.b,_IW.c,_IY.a,_IY.b,_IY.c,_IX.b,_J0.a,_J0.b,_J0.c,_IZ.b,_J1.a,_J1.b,_J1.c,_IW.g,_IW.h,_IW.i));return {_:0,a:E(_J2.a),b:E(_J2.b),c:E(_J2.c),d:E(_J2.d),e:E(_J2.e),f:E(_J2.f),g:E(_J2.g),h:_J2.h,i:_J2.i};},_J3=function(_J4,_J5,_J6,_J7,_J8,_J9,_Ja,_Jb,_Jc){var _Jd=B(_8J(B(_8H(_J4))));return new F(function(){return A3(_6X,_Jd,new T(function(){return B(_oZ(_J4,_J5,_J6,_J7,_J9,_Ja,_Jb));}),new T(function(){return B(A3(_8L,_Jd,_J8,_Jc));}));});},_Je=new T(function(){return B(unCStr("base"));}),_Jf=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Jg=new T(function(){return B(unCStr("IOException"));}),_Jh=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Je,_Jf,_Jg),_Ji=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Jh,_w,_w),_Jj=function(_Jk){return E(_Ji);},_Jl=function(_Jm){var _Jn=E(_Jm);return new F(function(){return _2n(B(_2l(_Jn.a)),_Jj,_Jn.b);});},_Jo=new T(function(){return B(unCStr(": "));}),_Jp=new T(function(){return B(unCStr(")"));}),_Jq=new T(function(){return B(unCStr(" ("));}),_Jr=new T(function(){return B(unCStr("interrupted"));}),_Js=new T(function(){return B(unCStr("system error"));}),_Jt=new T(function(){return B(unCStr("unsatisified constraints"));}),_Ju=new T(function(){return B(unCStr("user error"));}),_Jv=new T(function(){return B(unCStr("permission denied"));}),_Jw=new T(function(){return B(unCStr("illegal operation"));}),_Jx=new T(function(){return B(unCStr("end of file"));}),_Jy=new T(function(){return B(unCStr("resource exhausted"));}),_Jz=new T(function(){return B(unCStr("resource busy"));}),_JA=new T(function(){return B(unCStr("does not exist"));}),_JB=new T(function(){return B(unCStr("already exists"));}),_JC=new T(function(){return B(unCStr("resource vanished"));}),_JD=new T(function(){return B(unCStr("timeout"));}),_JE=new T(function(){return B(unCStr("unsupported operation"));}),_JF=new T(function(){return B(unCStr("hardware fault"));}),_JG=new T(function(){return B(unCStr("inappropriate type"));}),_JH=new T(function(){return B(unCStr("invalid argument"));}),_JI=new T(function(){return B(unCStr("failed"));}),_JJ=new T(function(){return B(unCStr("protocol error"));}),_JK=function(_JL,_JM){switch(E(_JL)){case 0:return new F(function(){return _n(_JB,_JM);});break;case 1:return new F(function(){return _n(_JA,_JM);});break;case 2:return new F(function(){return _n(_Jz,_JM);});break;case 3:return new F(function(){return _n(_Jy,_JM);});break;case 4:return new F(function(){return _n(_Jx,_JM);});break;case 5:return new F(function(){return _n(_Jw,_JM);});break;case 6:return new F(function(){return _n(_Jv,_JM);});break;case 7:return new F(function(){return _n(_Ju,_JM);});break;case 8:return new F(function(){return _n(_Jt,_JM);});break;case 9:return new F(function(){return _n(_Js,_JM);});break;case 10:return new F(function(){return _n(_JJ,_JM);});break;case 11:return new F(function(){return _n(_JI,_JM);});break;case 12:return new F(function(){return _n(_JH,_JM);});break;case 13:return new F(function(){return _n(_JG,_JM);});break;case 14:return new F(function(){return _n(_JF,_JM);});break;case 15:return new F(function(){return _n(_JE,_JM);});break;case 16:return new F(function(){return _n(_JD,_JM);});break;case 17:return new F(function(){return _n(_JC,_JM);});break;default:return new F(function(){return _n(_Jr,_JM);});}},_JN=new T(function(){return B(unCStr("}"));}),_JO=new T(function(){return B(unCStr("{handle: "));}),_JP=function(_JQ,_JR,_JS,_JT,_JU,_JV){var _JW=new T(function(){var _JX=new T(function(){var _JY=new T(function(){var _JZ=E(_JT);if(!_JZ._){return E(_JV);}else{var _K0=new T(function(){return B(_n(_JZ,new T(function(){return B(_n(_Jp,_JV));},1)));},1);return B(_n(_Jq,_K0));}},1);return B(_JK(_JR,_JY));}),_K1=E(_JS);if(!_K1._){return E(_JX);}else{return B(_n(_K1,new T(function(){return B(_n(_Jo,_JX));},1)));}}),_K2=E(_JU);if(!_K2._){var _K3=E(_JQ);if(!_K3._){return E(_JW);}else{var _K4=E(_K3.a);if(!_K4._){var _K5=new T(function(){var _K6=new T(function(){return B(_n(_JN,new T(function(){return B(_n(_Jo,_JW));},1)));},1);return B(_n(_K4.a,_K6));},1);return new F(function(){return _n(_JO,_K5);});}else{var _K7=new T(function(){var _K8=new T(function(){return B(_n(_JN,new T(function(){return B(_n(_Jo,_JW));},1)));},1);return B(_n(_K4.a,_K8));},1);return new F(function(){return _n(_JO,_K7);});}}}else{return new F(function(){return _n(_K2.a,new T(function(){return B(_n(_Jo,_JW));},1));});}},_K9=function(_Ka){var _Kb=E(_Ka);return new F(function(){return _JP(_Kb.a,_Kb.b,_Kb.c,_Kb.d,_Kb.f,_w);});},_Kc=function(_Kd,_Ke,_Kf){var _Kg=E(_Ke);return new F(function(){return _JP(_Kg.a,_Kg.b,_Kg.c,_Kg.d,_Kg.f,_Kf);});},_Kh=function(_Ki,_Kj){var _Kk=E(_Ki);return new F(function(){return _JP(_Kk.a,_Kk.b,_Kk.c,_Kk.d,_Kk.f,_Kj);});},_Kl=function(_Km,_Kn){return new F(function(){return _2Q(_Kh,_Km,_Kn);});},_Ko=new T3(0,_Kc,_K9,_Kl),_Kp=new T(function(){return new T5(0,_Jj,_Ko,_Kq,_Jl,_K9);}),_Kq=function(_Kr){return new T2(0,_Kp,_Kr);},_Ks=__Z,_Kt=7,_Ku=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:101:3-9"));}),_Kv=new T6(0,_Ks,_Kt,_w,_Ku,_Ks,_Ks),_Kw=new T(function(){return B(_Kq(_Kv));}),_Kx=function(_){return new F(function(){return die(_Kw);});},_Ky=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:100:3-9"));}),_Kz=new T6(0,_Ks,_Kt,_w,_Ky,_Ks,_Ks),_KA=new T(function(){return B(_Kq(_Kz));}),_KB=function(_){return new F(function(){return die(_KA);});},_KC=function(_KD,_){return new T2(0,_w,_KD);},_KE=0.6,_KF=1,_KG=new T(function(){return B(unCStr(")"));}),_KH=function(_KI,_KJ){var _KK=new T(function(){var _KL=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_EJ(0,_KI,_w)),_KG));})));},1);return B(_n(B(_EJ(0,_KJ,_w)),_KL));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_KK)));});},_KM=function(_KN,_KO){var _KP=new T(function(){var _KQ=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_EJ(0,_KO,_w)),_KG));})));},1);return B(_n(B(_EJ(0,_KN,_w)),_KQ));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_KP)));});},_KR=function(_KS){var _KT=E(_KS);if(!_KT._){return E(_KC);}else{var _KU=new T(function(){return B(_KR(_KT.b));}),_KV=function(_KW){var _KX=E(_KW);if(!_KX._){return E(_KU);}else{var _KY=_KX.a,_KZ=new T(function(){return B(_KV(_KX.b));}),_L0=new T(function(){return 0.1*E(E(_KY).e)/1.0e-2;}),_L1=new T(function(){var _L2=E(_KY);if(_L2.a!=_L2.b){return E(_KF);}else{return E(_KE);}}),_L3=function(_L4,_){var _L5=E(_L4),_L6=_L5.c,_L7=_L5.d,_L8=E(_L5.a),_L9=E(_L5.b),_La=E(_KY),_Lb=_La.a,_Lc=_La.b,_Ld=E(_La.c),_Le=_Ld.b,_Lf=E(_Ld.a),_Lg=_Lf.a,_Lh=_Lf.b,_Li=_Lf.c,_Lj=E(_La.d),_Lk=_Lj.b,_Ll=E(_Lj.a),_Lm=_Ll.a,_Ln=_Ll.b,_Lo=_Ll.c;if(_L8>_Lb){return new F(function(){return _KB(_);});}else{if(_Lb>_L9){return new F(function(){return _KB(_);});}else{if(_L8>_Lc){return new F(function(){return _Kx(_);});}else{if(_Lc>_L9){return new F(function(){return _Kx(_);});}else{var _Lp=_Lb-_L8|0;if(0>_Lp){return new F(function(){return _KH(_L6,_Lp);});}else{if(_Lp>=_L6){return new F(function(){return _KH(_L6,_Lp);});}else{var _Lq=E(_L7[_Lp]),_Lr=E(_Lq.c),_Ls=_Lr.b,_Lt=E(_Lr.a),_Lu=_Lt.a,_Lv=_Lt.b,_Lw=_Lt.c,_Lx=E(_Lq.e),_Ly=E(_Lx.a),_Lz=B(_Ib(_n4,_Lg,_Lh,_Li,_Le,_Lu,_Lv,_Lw,_Ls)),_LA=E(_Lz.a),_LB=B(_Ib(_n4,_LA.a,_LA.b,_LA.c,_Lz.b,_Lg,_Lh,_Li,_Le)),_LC=E(_LB.a),_LD=_Lc-_L8|0;if(0>_LD){return new F(function(){return _KM(_LD,_L6);});}else{if(_LD>=_L6){return new F(function(){return _KM(_LD,_L6);});}else{var _LE=E(_L7[_LD]),_LF=E(_LE.c),_LG=_LF.b,_LH=E(_LF.a),_LI=_LH.a,_LJ=_LH.b,_LK=_LH.c,_LL=E(_LE.e),_LM=E(_LL.a),_LN=B(_Ib(_n4,_Lm,_Ln,_Lo,_Lk,_LI,_LJ,_LK,_LG)),_LO=E(_LN.a),_LP=B(_Ib(_n4,_LO.a,_LO.b,_LO.c,_LN.b,_Lm,_Ln,_Lo,_Lk)),_LQ=E(_LP.a),_LR=E(_LC.a)+E(_LC.b)+E(_LC.c)+E(_LB.b)+E(_LQ.a)+E(_LQ.b)+E(_LQ.c)+E(_LP.b);if(!_LR){var _LS=B(A2(_KZ,_L5,_));return new T2(0,new T2(1,_ol,new T(function(){return E(E(_LS).a);})),new T(function(){return E(E(_LS).b);}));}else{var _LT=new T(function(){return  -((B(_J3(_nA,_Ly.a,_Ly.b,_Ly.c,_Lx.b,_Lg,_Lh,_Li,_Le))-B(_J3(_nA,_LM.a,_LM.b,_LM.c,_LL.b,_Lm,_Ln,_Lo,_Lk))-E(_L0))/_LR);}),_LU=function(_LV,_LW,_LX,_LY,_){var _LZ=new T(function(){var _M0=function(_M1,_M2,_M3,_M4,_M5){if(_M1>_Lc){return E(_M5);}else{if(_Lc>_M2){return E(_M5);}else{var _M6=function(_){var _M7=newArr(_M3,_m4),_M8=_M7,_M9=function(_Ma,_){while(1){if(_Ma!=_M3){var _=_M8[_Ma]=_M4[_Ma],_Mb=_Ma+1|0;_Ma=_Mb;continue;}else{return E(_);}}},_=B(_M9(0,_)),_Mc=_Lc-_M1|0;if(0>_Mc){return new F(function(){return _KM(_Mc,_M3);});}else{if(_Mc>=_M3){return new F(function(){return _KM(_Mc,_M3);});}else{var _=_M8[_Mc]=new T(function(){var _Md=E(_M4[_Mc]),_Me=E(_Md.e),_Mf=E(_Me.a),_Mg=B(_Ib(_n4,_LI,_LJ,_LK,_LG,_Lm,_Ln,_Lo,_Lk)),_Mh=E(_Mg.a),_Mi=E(_LT)*E(_L1),_Mj=B(_Ib(_n4,_Mh.a,_Mh.b,_Mh.c,_Mg.b,_Mi,_Mi,_Mi,_Mi)),_Mk=E(_Mj.a),_Ml=B(_Im(_n4,_Mf.a,_Mf.b,_Mf.c,_Me.b, -E(_Mk.a), -E(_Mk.b), -E(_Mk.c), -E(_Mj.b)));return {_:0,a:E(_Md.a),b:E(_Md.b),c:E(_Md.c),d:E(_Md.d),e:E(new T2(0,E(_Ml.a),E(_Ml.b))),f:E(_Md.f),g:E(_Md.g),h:_Md.h,i:_Md.i};});return new T4(0,E(_M1),E(_M2),_M3,_M8);}}};return new F(function(){return _Ev(_M6);});}}};if(_LV>_Lb){return B(_M0(_LV,_LW,_LX,_LY,new T4(0,E(_LV),E(_LW),_LX,_LY)));}else{if(_Lb>_LW){return B(_M0(_LV,_LW,_LX,_LY,new T4(0,E(_LV),E(_LW),_LX,_LY)));}else{var _Mm=function(_){var _Mn=newArr(_LX,_m4),_Mo=_Mn,_Mp=function(_Mq,_){while(1){if(_Mq!=_LX){var _=_Mo[_Mq]=_LY[_Mq],_Mr=_Mq+1|0;_Mq=_Mr;continue;}else{return E(_);}}},_=B(_Mp(0,_)),_Ms=_Lb-_LV|0;if(0>_Ms){return new F(function(){return _KH(_LX,_Ms);});}else{if(_Ms>=_LX){return new F(function(){return _KH(_LX,_Ms);});}else{var _=_Mo[_Ms]=new T(function(){var _Mt=E(_LY[_Ms]),_Mu=E(_Mt.e),_Mv=E(_Mu.a),_Mw=B(_Ib(_n4,_Lu,_Lv,_Lw,_Ls,_Lg,_Lh,_Li,_Le)),_Mx=E(_Mw.a),_My=E(_LT)*E(_L1),_Mz=B(_Ib(_n4,_Mx.a,_Mx.b,_Mx.c,_Mw.b,_My,_My,_My,_My)),_MA=E(_Mz.a),_MB=B(_Im(_n4,_Mv.a,_Mv.b,_Mv.c,_Mu.b,_MA.a,_MA.b,_MA.c,_Mz.b));return {_:0,a:E(_Mt.a),b:E(_Mt.b),c:E(_Mt.c),d:E(_Mt.d),e:E(new T2(0,E(_MB.a),E(_MB.b))),f:E(_Mt.f),g:E(_Mt.g),h:_Mt.h,i:_Mt.i};});return new T4(0,E(_LV),E(_LW),_LX,_Mo);}}},_MC=B(_Ev(_Mm));return B(_M0(E(_MC.a),E(_MC.b),_MC.c,_MC.d,_MC));}}});return new T2(0,_ol,_LZ);};if(!E(_La.f)){var _MD=B(_LU(_L8,_L9,_L6,_L7,_)),_ME=B(A2(_KZ,new T(function(){return E(E(_MD).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_MD).a);}),new T(function(){return E(E(_ME).a);})),new T(function(){return E(E(_ME).b);}));}else{if(E(_LT)<0){var _MF=B(A2(_KZ,_L5,_));return new T2(0,new T2(1,_ol,new T(function(){return E(E(_MF).a);})),new T(function(){return E(E(_MF).b);}));}else{var _MG=B(_LU(_L8,_L9,_L6,_L7,_)),_MH=B(A2(_KZ,new T(function(){return E(E(_MG).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_MG).a);}),new T(function(){return E(E(_MH).a);})),new T(function(){return E(E(_MH).b);}));}}}}}}}}}}}};return E(_L3);}};return new F(function(){return _KV(_KT.a);});}},_MI=function(_,_MJ){var _MK=new T(function(){return B(_KR(E(_MJ).a));}),_ML=function(_MM){var _MN=E(_MM);return (_MN==1)?E(new T2(1,_MK,_w)):new T2(1,_MK,new T(function(){return B(_ML(_MN-1|0));}));},_MO=B(_Hn(B(_ML(5)),new T(function(){return E(E(_MJ).b);}),_)),_MP=new T(function(){return B(_HV(_Hm,_Fb,_IU,new T(function(){return E(E(_MO).b);})));});return new T2(0,_ol,_MP);},_MQ=function(_MR,_MS,_MT,_MU,_MV){var _MW=B(_8J(B(_8H(_MR))));return new F(function(){return A3(_6X,_MW,new T(function(){return B(A3(_8L,_MW,_MS,_MU));}),new T(function(){return B(A3(_8L,_MW,_MT,_MV));}));});},_MX=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:58:7-13"));}),_MY=new T6(0,_Ks,_Kt,_w,_MX,_Ks,_Ks),_MZ=new T(function(){return B(_Kq(_MY));}),_N0=function(_){return new F(function(){return die(_MZ);});},_N1=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:56:5-11"));}),_N2=new T6(0,_Ks,_Kt,_w,_N1,_Ks,_Ks),_N3=new T(function(){return B(_Kq(_N2));}),_N4=function(_){return new F(function(){return die(_N3);});},_N5=function(_N6,_N7,_N8,_N9){var _Na=new T(function(){return B(_8J(new T(function(){return B(_8H(_N6));})));}),_Nb=B(A2(_8s,_Na,_8q));return new F(function(){return _p9(_N6,_Nb,B(A2(_8s,_Na,_8r)),_Nb);});},_Nc=false,_Nd=true,_Ne=function(_Nf){var _Ng=E(_Nf),_Nh=_Ng.b,_Ni=E(_Ng.d),_Nj=E(_Ng.e),_Nk=E(_Nj.a),_Nl=E(_Ng.g),_Nm=B(A1(_Nh,_Ni.a)),_Nn=B(_q0(_nA,_Nm.a,_Nm.b,_Nm.c,_Nl.a,_Nl.b,_Nl.c));return {_:0,a:E(_Ng.a),b:E(_Nh),c:E(_Ng.c),d:E(_Ni),e:E(new T2(0,E(new T3(0,E(_Nk.a)+E(_Nn.a)*1.0e-2,E(_Nk.b)+E(_Nn.b)*1.0e-2,E(_Nk.c)+E(_Nn.c)*1.0e-2)),E(_Nj.b))),f:E(_Ng.f),g:E(_Nl),h:_Ng.h,i:_Ng.i};},_No=new T(function(){return eval("collide");}),_Np=new T(function(){return eval("collideBound");}),_Nq=function(_Nr){var _Ns=E(_Nr);if(!_Ns._){return __Z;}else{return new F(function(){return _n(_Ns.a,new T(function(){return B(_Nq(_Ns.b));},1));});}},_Nt=0,_Nu=new T3(0,E(_Nt),E(_Nt),E(_Nt)),_Nv=new T2(0,E(_Nu),E(_Nt)),_Nw=function(_Nx,_){var _Ny=B(_HV(_Hm,_Fb,_Ne,_Nx)),_Nz=E(_Ny.a),_NA=E(_Ny.b);if(_Nz<=_NA){var _NB=function(_NC,_ND,_NE,_NF,_NG,_){if(_ND>_NC){return new F(function(){return _N4(_);});}else{if(_NC>_NE){return new F(function(){return _N4(_);});}else{var _NH=new T(function(){var _NI=_NC-_ND|0;if(0>_NI){return B(_KM(_NI,_NF));}else{if(_NI>=_NF){return B(_KM(_NI,_NF));}else{return E(_NG[_NI]);}}}),_NJ=function(_NK,_NL,_NM,_NN,_NO,_){var _NP=E(_NK);if(!_NP._){return new T2(0,_w,new T4(0,E(_NL),E(_NM),_NN,_NO));}else{var _NQ=E(_NP.a);if(_NL>_NQ){return new F(function(){return _N0(_);});}else{if(_NQ>_NM){return new F(function(){return _N0(_);});}else{var _NR=E(_NH),_NS=_NQ-_NL|0;if(0>_NS){return new F(function(){return _KH(_NN,_NS);});}else{if(_NS>=_NN){return new F(function(){return _KH(_NN,_NS);});}else{var _NT=E(_NO[_NS]),_NU=__app2(E(_No),B(_om(new T2(1,new T2(0,_EA,_NR.h),new T2(1,new T2(0,_Ez,_NR.i),_w)))),B(_om(new T2(1,new T2(0,_EA,_NT.h),new T2(1,new T2(0,_Ez,_NT.i),_w))))),_NV=__arr2lst(0,_NU),_NW=B(_FO(_NV,_)),_NX=B(_NJ(_NP.b,_NL,_NM,_NN,_NO,_)),_NY=new T(function(){var _NZ=new T(function(){return _NC!=_NQ;}),_O0=function(_O1){var _O2=E(_O1);if(!_O2._){return __Z;}else{var _O3=_O2.b,_O4=E(_O2.a),_O5=E(_O4.b),_O6=E(_O4.a),_O7=E(_O6.a),_O8=E(_O6.b),_O9=E(_O6.c),_Oa=E(_O5.a),_Ob=E(_O5.b),_Oc=E(_O5.c),_Od=E(_O4.c),_Oe=_Od.a,_Of=_Od.b,_Og=E(_O4.e),_Oh=E(_O4.d),_Oi=_Oh.a,_Oj=_Oh.b,_Ok=E(_O4.f),_Ol=new T(function(){var _Om=B(_p9(_nA,_Ok.a,_Ok.b,_Ok.c)),_On=Math.sqrt(B(_MQ(_nA,_Oi,_Oj,_Oi,_Oj)));return new T3(0,_On*E(_Om.a),_On*E(_Om.b),_On*E(_Om.c));}),_Oo=new T(function(){var _Op=B(_p9(_nA,_Og.a,_Og.b,_Og.c)),_Oq=Math.sqrt(B(_MQ(_nA,_Oe,_Of,_Oe,_Of)));return new T3(0,_Oq*E(_Op.a),_Oq*E(_Op.b),_Oq*E(_Op.c));}),_Or=new T(function(){var _Os=B(_N5(_nA,_Oa,_Ob,_Oc));return new T3(0,E(_Os.a),E(_Os.b),E(_Os.c));}),_Ot=new T(function(){var _Ou=B(_N5(_nA,_O7,_O8,_O9));return new T3(0,E(_Ou.a),E(_Ou.b),E(_Ou.c));}),_Ov=_Oa+ -_O7,_Ow=_Ob+ -_O8,_Ox=_Oc+ -_O9,_Oy=new T(function(){return Math.sqrt(B(_oZ(_nA,_Ov,_Ow,_Ox,_Ov,_Ow,_Ox)));}),_Oz=new T(function(){var _OA=1/E(_Oy);return new T3(0,_Ov*_OA,_Ow*_OA,_Ox*_OA);}),_OB=new T(function(){if(!E(_O4.g)){return E(_Oz);}else{var _OC=E(_Oz);return new T3(0,-1*E(_OC.a),-1*E(_OC.b),-1*E(_OC.c));}}),_OD=new T(function(){if(!E(_O4.h)){return E(_Oz);}else{var _OE=E(_Oz);return new T3(0,-1*E(_OE.a),-1*E(_OE.b),-1*E(_OE.c));}});return (!E(_NZ))?new T2(1,new T(function(){var _OF=E(_OB),_OG=E(_OF.b),_OH=E(_OF.c),_OI=E(_OF.a),_OJ=E(_Ot),_OK=E(_OJ.c),_OL=E(_OJ.b),_OM=E(_OJ.a),_ON=E(_Oo),_OO=E(_ON.c),_OP=E(_ON.b),_OQ=E(_ON.a),_OR=_OG*_OK-_OL*_OH,_OS=_OH*_OM-_OK*_OI,_OT=_OI*_OL-_OM*_OG,_OU=B(_oZ(_nA,_OS*_OO-_OP*_OT,_OT*_OQ-_OO*_OR,_OR*_OP-_OQ*_OS,_OM,_OL,_OK));return new T6(0,_NC,_NQ,E(new T2(0,E(new T3(0,E(_OR),E(_OS),E(_OT))),E(_OU))),E(_Nv),_Oy,_Nc);}),new T2(1,new T(function(){var _OV=E(_OD),_OW=E(_OV.b),_OX=E(_OV.c),_OY=E(_OV.a),_OZ=E(_Or),_P0=E(_OZ.c),_P1=E(_OZ.b),_P2=E(_OZ.a),_P3=E(_Ol),_P4=E(_P3.c),_P5=E(_P3.b),_P6=E(_P3.a),_P7=_OW*_P0-_P1*_OX,_P8=_OX*_P2-_P0*_OY,_P9=_OY*_P1-_P2*_OW,_Pa=B(_oZ(_nA,_P8*_P4-_P5*_P9,_P9*_P6-_P4*_P7,_P7*_P5-_P6*_P8,_P2,_P1,_P0));return new T6(0,_NC,_NQ,E(_Nv),E(new T2(0,E(new T3(0,E(_P7),E(_P8),E(_P9))),E(_Pa))),_Oy,_Nc);}),new T(function(){return B(_O0(_O3));}))):new T2(1,new T(function(){var _Pb=E(_OB),_Pc=E(_Pb.b),_Pd=E(_Pb.c),_Pe=E(_Pb.a),_Pf=E(_Ot),_Pg=_Pf.a,_Ph=_Pf.b,_Pi=_Pf.c,_Pj=B(_q0(_nA,_Pe,_Pc,_Pd,_Pg,_Ph,_Pi)),_Pk=E(_Oo),_Pl=E(_Pk.c),_Pm=E(_Pk.b),_Pn=E(_Pk.a),_Po=B(_oZ(_nA,_Pc*_Pl-_Pm*_Pd,_Pd*_Pn-_Pl*_Pe,_Pe*_Pm-_Pn*_Pc,_Pg,_Ph,_Pi)),_Pp=E(_OD),_Pq=E(_Pp.b),_Pr=E(_Pp.c),_Ps=E(_Pp.a),_Pt=E(_Or),_Pu=_Pt.a,_Pv=_Pt.b,_Pw=_Pt.c,_Px=B(_q0(_nA,_Ps,_Pq,_Pr,_Pu,_Pv,_Pw)),_Py=E(_Ol),_Pz=E(_Py.c),_PA=E(_Py.b),_PB=E(_Py.a),_PC=B(_oZ(_nA,_Pq*_Pz-_PA*_Pr,_Pr*_PB-_Pz*_Ps,_Ps*_PA-_PB*_Pq,_Pu,_Pv,_Pw));return new T6(0,_NC,_NQ,E(new T2(0,E(new T3(0,E(_Pj.a),E(_Pj.b),E(_Pj.c))),E(_Po))),E(new T2(0,E(new T3(0,E(_Px.a),E(_Px.b),E(_Px.c))),E(_PC))),_Oy,_Nd);}),new T(function(){return B(_O0(_O3));}));}};return B(_O0(_NW));});return new T2(0,new T2(1,_NY,new T(function(){return E(E(_NX).a);})),new T(function(){return E(E(_NX).b);}));}}}}}},_PD=B(_NJ(B(_wu(_NC,_NA)),_ND,_NE,_NF,_NG,_)),_PE=E(_NH),_PF=__app1(E(_Np),B(_om(new T2(1,new T2(0,_EA,_PE.h),new T2(1,new T2(0,_Ez,_PE.i),_w))))),_PG=__arr2lst(0,_PF),_PH=B(_FO(_PG,_));if(_NC!=_NA){var _PI=E(_PD),_PJ=E(_PI.b),_PK=B(_NB(_NC+1|0,E(_PJ.a),E(_PJ.b),_PJ.c,_PJ.d,_)),_PL=new T(function(){var _PM=new T(function(){return B(_Nq(_PI.a));}),_PN=function(_PO){var _PP=E(_PO);if(!_PP._){return E(_PM);}else{var _PQ=E(_PP.a),_PR=E(_PQ.b),_PS=E(_PQ.a),_PT=E(_PS.a),_PU=E(_PS.b),_PV=E(_PS.c),_PW=E(_PQ.c),_PX=_PW.a,_PY=_PW.b,_PZ=E(_PQ.e);return new T2(1,new T(function(){var _Q0=E(_PR.a)+ -_PT,_Q1=E(_PR.b)+ -_PU,_Q2=E(_PR.c)+ -_PV,_Q3=B(_N5(_nA,_PT,_PU,_PV)),_Q4=_Q3.a,_Q5=_Q3.b,_Q6=_Q3.c,_Q7=Math.sqrt(B(_oZ(_nA,_Q0,_Q1,_Q2,_Q0,_Q1,_Q2))),_Q8=1/_Q7,_Q9=_Q0*_Q8,_Qa=_Q1*_Q8,_Qb=_Q2*_Q8,_Qc=B(_q0(_nA,_Q9,_Qa,_Qb,_Q4,_Q5,_Q6)),_Qd=B(_p9(_nA,_PZ.a,_PZ.b,_PZ.c)),_Qe=Math.sqrt(B(_MQ(_nA,_PX,_PY,_PX,_PY))),_Qf=_Qe*E(_Qd.a),_Qg=_Qe*E(_Qd.b),_Qh=_Qe*E(_Qd.c),_Qi=B(_oZ(_nA,_Qa*_Qh-_Qg*_Qb,_Qb*_Qf-_Qh*_Q9,_Q9*_Qg-_Qf*_Qa,_Q4,_Q5,_Q6));return new T6(0,_NC,_NC,E(new T2(0,E(new T3(0,E(_Qc.a),E(_Qc.b),E(_Qc.c))),E(_Qi))),E(_Nv),_Q7,_Nd);}),new T(function(){return B(_PN(_PP.b));}));}};return B(_PN(_PH));});return new T2(0,new T2(1,_PL,new T(function(){return E(E(_PK).a);})),new T(function(){return E(E(_PK).b);}));}else{var _Qj=new T(function(){var _Qk=new T(function(){return B(_Nq(E(_PD).a));}),_Ql=function(_Qm){var _Qn=E(_Qm);if(!_Qn._){return E(_Qk);}else{var _Qo=E(_Qn.a),_Qp=E(_Qo.b),_Qq=E(_Qo.a),_Qr=E(_Qq.a),_Qs=E(_Qq.b),_Qt=E(_Qq.c),_Qu=E(_Qo.c),_Qv=_Qu.a,_Qw=_Qu.b,_Qx=E(_Qo.e);return new T2(1,new T(function(){var _Qy=E(_Qp.a)+ -_Qr,_Qz=E(_Qp.b)+ -_Qs,_QA=E(_Qp.c)+ -_Qt,_QB=B(_N5(_nA,_Qr,_Qs,_Qt)),_QC=_QB.a,_QD=_QB.b,_QE=_QB.c,_QF=Math.sqrt(B(_oZ(_nA,_Qy,_Qz,_QA,_Qy,_Qz,_QA))),_QG=1/_QF,_QH=_Qy*_QG,_QI=_Qz*_QG,_QJ=_QA*_QG,_QK=B(_q0(_nA,_QH,_QI,_QJ,_QC,_QD,_QE)),_QL=B(_p9(_nA,_Qx.a,_Qx.b,_Qx.c)),_QM=Math.sqrt(B(_MQ(_nA,_Qv,_Qw,_Qv,_Qw))),_QN=_QM*E(_QL.a),_QO=_QM*E(_QL.b),_QP=_QM*E(_QL.c),_QQ=B(_oZ(_nA,_QI*_QP-_QO*_QJ,_QJ*_QN-_QP*_QH,_QH*_QO-_QN*_QI,_QC,_QD,_QE));return new T6(0,_NC,_NC,E(new T2(0,E(new T3(0,E(_QK.a),E(_QK.b),E(_QK.c))),E(_QQ))),E(_Nv),_QF,_Nd);}),new T(function(){return B(_Ql(_Qn.b));}));}};return B(_Ql(_PH));});return new T2(0,new T2(1,_Qj,_w),new T(function(){return E(E(_PD).b);}));}}}},_QR=B(_NB(_Nz,_Nz,_NA,_Ny.c,_Ny.d,_));return new F(function(){return _MI(_,_QR);});}else{return new F(function(){return _MI(_,new T2(0,_w,_Ny));});}},_QS=new T(function(){return eval("__strict(passObject)");}),_QT=new T(function(){return eval("__strict(refresh)");}),_QU=function(_QV,_){var _QW=__app0(E(_QT)),_QX=__app0(E(_EE)),_QY=E(_QV),_QZ=_QY.c,_R0=_QY.d,_R1=E(_QY.a),_R2=E(_QY.b);if(_R1<=_R2){if(_R1>_R2){return E(_EC);}else{if(0>=_QZ){return new F(function(){return _EP(_QZ,0);});}else{var _R3=E(_R0[0]),_R4=E(_QS),_R5=__app2(_R4,_R1,B(_om(new T2(1,new T2(0,_EA,_R3.h),new T2(1,new T2(0,_Ez,_R3.i),_w)))));if(_R1!=_R2){var _R6=function(_R7,_){if(_R1>_R7){return E(_EC);}else{if(_R7>_R2){return E(_EC);}else{var _R8=_R7-_R1|0;if(0>_R8){return new F(function(){return _EP(_QZ,_R8);});}else{if(_R8>=_QZ){return new F(function(){return _EP(_QZ,_R8);});}else{var _R9=E(_R0[_R8]),_Ra=__app2(_R4,_R7,B(_om(new T2(1,new T2(0,_EA,_R9.h),new T2(1,new T2(0,_Ez,_R9.i),_w)))));if(_R7!=_R2){var _Rb=B(_R6(_R7+1|0,_));return new T2(1,_ol,_Rb);}else{return _EU;}}}}}},_Rc=B(_R6(_R1+1|0,_)),_Rd=__app0(E(_ED)),_Re=B(_Nw(_QY,_));return new T(function(){return E(E(_Re).b);});}else{var _Rf=__app0(E(_ED)),_Rg=B(_Nw(_QY,_));return new T(function(){return E(E(_Rg).b);});}}}}else{var _Rh=__app0(E(_ED)),_Ri=B(_Nw(_QY,_));return new T(function(){return E(E(_Ri).b);});}},_Rj=function(_Rk,_){while(1){var _Rl=E(_Rk);if(!_Rl._){return _ol;}else{var _Rm=_Rl.b,_Rn=E(_Rl.a);switch(_Rn._){case 0:var _Ro=B(A1(_Rn.a,_));_Rk=B(_n(_Rm,new T2(1,_Ro,_w)));continue;case 1:_Rk=B(_n(_Rm,_Rn.a));continue;default:_Rk=_Rm;continue;}}}},_Rp=function(_Rq,_Rr,_){var _Rs=E(_Rq);switch(_Rs._){case 0:var _Rt=B(A1(_Rs.a,_));return new F(function(){return _Rj(B(_n(_Rr,new T2(1,_Rt,_w))),_);});break;case 1:return new F(function(){return _Rj(B(_n(_Rr,_Rs.a)),_);});break;default:return new F(function(){return _Rj(_Rr,_);});}},_Ru=new T0(2),_Rv=function(_Rw){return new T0(2);},_Rx=function(_Ry,_Rz,_RA){return function(_){var _RB=E(_Ry),_RC=rMV(_RB),_RD=E(_RC);if(!_RD._){var _RE=new T(function(){var _RF=new T(function(){return B(A1(_RA,_ol));});return B(_n(_RD.b,new T2(1,new T2(0,_Rz,function(_RG){return E(_RF);}),_w)));}),_=wMV(_RB,new T2(0,_RD.a,_RE));return _Ru;}else{var _RH=E(_RD.a);if(!_RH._){var _=wMV(_RB,new T2(0,_Rz,_w));return new T(function(){return B(A1(_RA,_ol));});}else{var _=wMV(_RB,new T1(1,_RH.b));return new T1(1,new T2(1,new T(function(){return B(A1(_RA,_ol));}),new T2(1,new T(function(){return B(A2(_RH.a,_Rz,_Rv));}),_w)));}}};},_RI=new T(function(){return E(_u1);}),_RJ=new T(function(){return eval("window.requestAnimationFrame");}),_RK=new T1(1,_w),_RL=function(_RM,_RN){return function(_){var _RO=E(_RM),_RP=rMV(_RO),_RQ=E(_RP);if(!_RQ._){var _RR=_RQ.a,_RS=E(_RQ.b);if(!_RS._){var _=wMV(_RO,_RK);return new T(function(){return B(A1(_RN,_RR));});}else{var _RT=E(_RS.a),_=wMV(_RO,new T2(0,_RT.a,_RS.b));return new T1(1,new T2(1,new T(function(){return B(A1(_RN,_RR));}),new T2(1,new T(function(){return B(A1(_RT.b,_Rv));}),_w)));}}else{var _RU=new T(function(){var _RV=function(_RW){var _RX=new T(function(){return B(A1(_RN,_RW));});return function(_RY){return E(_RX);};};return B(_n(_RQ.a,new T2(1,_RV,_w)));}),_=wMV(_RO,new T1(1,_RU));return _Ru;}};},_RZ=function(_S0,_S1){return new T1(0,B(_RL(_S0,_S1)));},_S2=function(_S3,_S4){var _S5=new T(function(){return new T1(0,B(_Rx(_S3,_ol,_Rv)));});return function(_){var _S6=__createJSFunc(2,function(_S7,_){var _S8=B(_Rp(_S5,_w,_));return _RI;}),_S9=__app1(E(_RJ),_S6);return new T(function(){return B(_RZ(_S3,_S4));});};},_Sa=new T1(1,_w),_Sb=function(_Sc,_Sd,_){var _Se=function(_){var _Sf=nMV(_Sc),_Sg=_Sf;return new T(function(){var _Sh=new T(function(){return B(_Si(_));}),_Sj=function(_){var _Sk=rMV(_Sg),_Sl=B(A2(_Sd,_Sk,_)),_=wMV(_Sg,_Sl),_Sm=function(_){var _Sn=nMV(_Sa);return new T(function(){return new T1(0,B(_S2(_Sn,function(_So){return E(_Sh);})));});};return new T1(0,_Sm);},_Sp=new T(function(){return new T1(0,_Sj);}),_Si=function(_Sq){return E(_Sp);};return B(_Si(_));});};return new F(function(){return _Rp(new T1(0,_Se),_w,_);});},_Sr=new T(function(){return eval("__strict(setBounds)");}),_Ss=function(_){var _St=__app3(E(_lt),E(_lu),E(_lX),E(_ls)),_Su=__app2(E(_Sr),E(_iI),E(_iF));return new F(function(){return _Sb(_Ey,_QU,_);});},_Sv=function(_){return new F(function(){return _Ss(_);});};
var hasteMain = function() {B(A(_Sv, [0]));};window.onload = hasteMain;