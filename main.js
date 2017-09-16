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

var _0=function(_1,_2,_3){return new F(function(){return A1(_1,function(_4){return new F(function(){return A2(_2,_4,_3);});});});},_5=function(_6,_7,_8){var _9=function(_a){var _b=new T(function(){return B(A1(_8,_a));});return new F(function(){return A1(_7,function(_c){return E(_b);});});};return new F(function(){return A1(_6,_9);});},_d=function(_e,_f,_g){var _h=new T(function(){return B(A1(_f,function(_i){return new F(function(){return A1(_g,_i);});}));});return new F(function(){return A1(_e,function(_j){return E(_h);});});},_k=function(_l,_m,_n){var _o=function(_p){var _q=function(_r){return new F(function(){return A1(_n,new T(function(){return B(A1(_p,_r));}));});};return new F(function(){return A1(_m,_q);});};return new F(function(){return A1(_l,_o);});},_s=function(_t,_u){return new F(function(){return A1(_u,_t);});},_v=function(_w,_x,_y){var _z=new T(function(){return B(A1(_y,_w));});return new F(function(){return A1(_x,function(_A){return E(_z);});});},_B=function(_C,_D,_E){var _F=function(_G){return new F(function(){return A1(_E,new T(function(){return B(A1(_C,_G));}));});};return new F(function(){return A1(_D,_F);});},_H=new T2(0,_B,_v),_I=new T5(0,_H,_s,_k,_d,_5),_J=function(_K){return E(E(_K).b);},_L=function(_M,_N){return new F(function(){return A3(_J,_O,_M,function(_P){return E(_N);});});},_Q=function(_R){return new F(function(){return err(_R);});},_O=new T(function(){return new T5(0,_I,_0,_L,_s,_Q);}),_S=0,_T=__Z,_U=function(_V){return new T0(2);},_W=function(_X){var _Y=new T(function(){return B(A1(_X,_U));}),_Z=function(_10){return new T1(1,new T2(1,new T(function(){return B(A1(_10,_S));}),new T2(1,_Y,_T)));};return E(_Z);},_11=function(_12){return E(_12);},_13=new T3(0,_O,_11,_W),_14=function(_15,_16){var _17=E(_15);return (_17._==0)?E(_16):new T2(1,_17.a,new T(function(){return B(_14(_17.b,_16));}));},_18=function(_19,_){while(1){var _1a=E(_19);if(!_1a._){return _S;}else{var _1b=_1a.b,_1c=E(_1a.a);switch(_1c._){case 0:var _1d=B(A1(_1c.a,_));_19=B(_14(_1b,new T2(1,_1d,_T)));continue;case 1:_19=B(_14(_1b,_1c.a));continue;default:_19=_1b;continue;}}}},_1e=function(_1f,_1g,_){var _1h=E(_1f);switch(_1h._){case 0:var _1i=B(A1(_1h.a,_));return new F(function(){return _18(B(_14(_1g,new T2(1,_1i,_T))),_);});break;case 1:return new F(function(){return _18(B(_14(_1g,_1h.a)),_);});break;default:return new F(function(){return _18(_1g,_);});}},_1j=new T(function(){return eval("compile");}),_1k=function(_1l){return E(E(_1l).b);},_1m=function(_1n){return E(E(_1n).a);},_1o=function(_1p,_1q,_1r){var _1s=E(_1r);if(!_1s._){return new F(function(){return A1(_1q,_1s.a);});}else{var _1t=new T(function(){return B(_1k(_1p));}),_1u=new T(function(){return B(_1m(_1p));}),_1v=function(_1w){var _1x=E(_1w);if(!_1x._){return E(_1u);}else{return new F(function(){return A2(_1t,new T(function(){return B(_1o(_1p,_1q,_1x.a));}),new T(function(){return B(_1v(_1x.b));}));});}};return new F(function(){return _1v(_1s.a);});}},_1y=function(_1z){var _1A=E(_1z);if(!_1A._){return __Z;}else{return new F(function(){return _14(_1A.a,new T(function(){return B(_1y(_1A.b));},1));});}},_1B=function(_1C){return new F(function(){return _1y(_1C);});},_1D=new T3(0,_T,_14,_1B),_1E=new T(function(){return B(unCStr("z"));}),_1F=new T1(0,_1E),_1G=new T(function(){return B(unCStr("y"));}),_1H=new T1(0,_1G),_1I=new T(function(){return B(unCStr("x"));}),_1J=new T1(0,_1I),_1K=new T3(0,_1J,_1H,_1F),_1L=new T1(0,0),_1M=function(_1N){return E(E(_1N).a);},_1O=function(_1P){return E(E(_1P).a);},_1Q=function(_1R){return E(E(_1R).c);},_1S=function(_1T){return E(E(_1T).a);},_1U=function(_1V,_1W,_1X,_1Y,_1Z,_20,_21){var _22=B(_1O(B(_1M(_1V)))),_23=new T(function(){return B(A3(_1S,_22,new T(function(){return B(A3(_1Q,_22,_1W,_1Z));}),new T(function(){return B(A3(_1Q,_22,_1X,_20));})));});return new F(function(){return A3(_1S,_22,_23,new T(function(){return B(A3(_1Q,_22,_1Y,_21));}));});},_24=function(_25){return E(E(_25).b);},_26=function(_27){return E(E(_27).e);},_28=function(_29){return E(E(_29).g);},_2a=function(_2b){return E(E(_2b).d);},_2c=new T1(0,10),_2d=new T1(0,3),_2e=new T2(0,E(_2d),E(_2c)),_2f=new T1(0,5),_2g=new T2(0,E(_2d),E(_2f)),_2h=function(_2i){return E(E(_2i).g);},_2j=function(_2k){return E(E(_2k).h);},_2l=function(_2m){return E(E(_2m).d);},_2n=function(_2o){return E(E(_2o).e);},_2p=function(_2q){var _2r=new T(function(){return E(E(_2q).a);}),_2s=new T(function(){return B(_1M(_2r));}),_2t=new T(function(){return B(_1O(_2s));}),_2u=new T(function(){return B(A2(_28,_2t,_1L));}),_2v=new T(function(){return B(A2(_2l,_2t,new T(function(){return B(A2(_2a,_2s,_2g));})));}),_2w=new T(function(){return E(E(_2q).b);}),_2x=new T(function(){return B(_1S(_2t));}),_2y=new T(function(){return B(_26(_2t));}),_2z=new T(function(){return B(A2(_2a,_2s,_2e));}),_2A=function(_2B){var _2C=new T(function(){var _2D=new T(function(){var _2E=E(_2B),_2F=new T(function(){return B(A2(_2x,new T(function(){return B(A1(_2y,_2E.c));}),_2v));}),_2G=new T(function(){return B(A2(_2x,new T(function(){return B(A1(_2y,_2E.b));}),_2v));}),_2H=new T(function(){return B(A2(_2x,new T(function(){return B(A1(_2y,_2E.a));}),_2v));});return new T3(0,_2H,_2G,_2F);}),_2I=new T(function(){var _2J=new T(function(){var _2K=new T(function(){return B(A3(_2h,_2w,new T(function(){return E(E(_2D).a);}),_2u));}),_2L=new T(function(){return B(A3(_2h,_2w,new T(function(){return E(E(_2D).b);}),_2u));}),_2M=new T(function(){return B(A3(_2h,_2w,new T(function(){return E(E(_2D).c);}),_2u));});return B(_1U(_2r,_2K,_2L,_2M,_2K,_2L,_2M));});return B(A2(_2n,_2r,_2J));}),_2N=new T(function(){var _2O=new T(function(){var _2P=new T(function(){return B(A3(_2h,_2w,new T(function(){return E(E(_2D).a);}),new T(function(){return E(E(_2D).b);})));});return B(A3(_2h,_2w,_2P,new T(function(){return E(E(_2D).c);})));});return B(A3(_2j,_2w,_2u,_2O));});return B(A3(_1S,_2t,_2N,_2I));});return new F(function(){return A3(_24,_2t,_2C,_2z);});};return E(_2A);},_2Q=new T(function(){return B(unCStr(","));}),_2R=new T1(0,_2Q),_2S=new T(function(){return B(unCStr("pow("));}),_2T=new T1(0,_2S),_2U=new T(function(){return B(unCStr(")"));}),_2V=new T1(0,_2U),_2W=new T2(1,_2V,_T),_2X=function(_2Y,_2Z){return new T1(1,new T2(1,_2T,new T2(1,_2Y,new T2(1,_2R,new T2(1,_2Z,_2W)))));},_30=new T(function(){return B(unCStr("acos("));}),_31=new T1(0,_30),_32=function(_33){return new T1(1,new T2(1,_31,new T2(1,_33,_2W)));},_34=new T(function(){return B(unCStr("acosh("));}),_35=new T1(0,_34),_36=function(_37){return new T1(1,new T2(1,_35,new T2(1,_37,_2W)));},_38=new T(function(){return B(unCStr("asin("));}),_39=new T1(0,_38),_3a=function(_3b){return new T1(1,new T2(1,_39,new T2(1,_3b,_2W)));},_3c=new T(function(){return B(unCStr("asinh("));}),_3d=new T1(0,_3c),_3e=function(_3f){return new T1(1,new T2(1,_3d,new T2(1,_3f,_2W)));},_3g=new T(function(){return B(unCStr("atan("));}),_3h=new T1(0,_3g),_3i=function(_3j){return new T1(1,new T2(1,_3h,new T2(1,_3j,_2W)));},_3k=new T(function(){return B(unCStr("atanh("));}),_3l=new T1(0,_3k),_3m=function(_3n){return new T1(1,new T2(1,_3l,new T2(1,_3n,_2W)));},_3o=new T(function(){return B(unCStr("cos("));}),_3p=new T1(0,_3o),_3q=function(_3r){return new T1(1,new T2(1,_3p,new T2(1,_3r,_2W)));},_3s=new T(function(){return B(unCStr("cosh("));}),_3t=new T1(0,_3s),_3u=function(_3v){return new T1(1,new T2(1,_3t,new T2(1,_3v,_2W)));},_3w=new T(function(){return B(unCStr("exp("));}),_3x=new T1(0,_3w),_3y=function(_3z){return new T1(1,new T2(1,_3x,new T2(1,_3z,_2W)));},_3A=new T(function(){return B(unCStr("log("));}),_3B=new T1(0,_3A),_3C=function(_3D){return new T1(1,new T2(1,_3B,new T2(1,_3D,_2W)));},_3E=new T(function(){return B(unCStr(")/log("));}),_3F=new T1(0,_3E),_3G=function(_3H,_3I){return new T1(1,new T2(1,_3B,new T2(1,_3I,new T2(1,_3F,new T2(1,_3H,_2W)))));},_3J=new T(function(){return B(unCStr("pi"));}),_3K=new T1(0,_3J),_3L=new T(function(){return B(unCStr("sin("));}),_3M=new T1(0,_3L),_3N=function(_3O){return new T1(1,new T2(1,_3M,new T2(1,_3O,_2W)));},_3P=new T(function(){return B(unCStr("sinh("));}),_3Q=new T1(0,_3P),_3R=function(_3S){return new T1(1,new T2(1,_3Q,new T2(1,_3S,_2W)));},_3T=new T(function(){return B(unCStr("sqrt("));}),_3U=new T1(0,_3T),_3V=function(_3W){return new T1(1,new T2(1,_3U,new T2(1,_3W,_2W)));},_3X=new T(function(){return B(unCStr("tan("));}),_3Y=new T1(0,_3X),_3Z=function(_40){return new T1(1,new T2(1,_3Y,new T2(1,_40,_2W)));},_41=new T(function(){return B(unCStr("tanh("));}),_42=new T1(0,_41),_43=function(_44){return new T1(1,new T2(1,_42,new T2(1,_44,_2W)));},_45=new T(function(){return B(unCStr("("));}),_46=new T1(0,_45),_47=new T(function(){return B(unCStr(")/("));}),_48=new T1(0,_47),_49=function(_4a,_4b){return new T1(1,new T2(1,_46,new T2(1,_4a,new T2(1,_48,new T2(1,_4b,_2W)))));},_4c=new T1(0,1),_4d=function(_4e,_4f){var _4g=E(_4e);if(!_4g._){var _4h=_4g.a,_4i=E(_4f);if(!_4i._){var _4j=_4i.a;return (_4h!=_4j)?(_4h>_4j)?2:0:1;}else{var _4k=I_compareInt(_4i.a,_4h);return (_4k<=0)?(_4k>=0)?1:2:0;}}else{var _4l=_4g.a,_4m=E(_4f);if(!_4m._){var _4n=I_compareInt(_4l,_4m.a);return (_4n>=0)?(_4n<=0)?1:2:0;}else{var _4o=I_compare(_4l,_4m.a);return (_4o>=0)?(_4o<=0)?1:2:0;}}},_4p=new T(function(){return B(unCStr("base"));}),_4q=new T(function(){return B(unCStr("GHC.Exception"));}),_4r=new T(function(){return B(unCStr("ArithException"));}),_4s=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_4p,_4q,_4r),_4t=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_4s,_T,_T),_4u=function(_4v){return E(_4t);},_4w=function(_4x){return E(E(_4x).a);},_4y=function(_4z,_4A,_4B){var _4C=B(A1(_4z,_)),_4D=B(A1(_4A,_)),_4E=hs_eqWord64(_4C.a,_4D.a);if(!_4E){return __Z;}else{var _4F=hs_eqWord64(_4C.b,_4D.b);return (!_4F)?__Z:new T1(1,_4B);}},_4G=function(_4H){var _4I=E(_4H);return new F(function(){return _4y(B(_4w(_4I.a)),_4u,_4I.b);});},_4J=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_4K=new T(function(){return B(unCStr("denormal"));}),_4L=new T(function(){return B(unCStr("divide by zero"));}),_4M=new T(function(){return B(unCStr("loss of precision"));}),_4N=new T(function(){return B(unCStr("arithmetic underflow"));}),_4O=new T(function(){return B(unCStr("arithmetic overflow"));}),_4P=function(_4Q,_4R){switch(E(_4Q)){case 0:return new F(function(){return _14(_4O,_4R);});break;case 1:return new F(function(){return _14(_4N,_4R);});break;case 2:return new F(function(){return _14(_4M,_4R);});break;case 3:return new F(function(){return _14(_4L,_4R);});break;case 4:return new F(function(){return _14(_4K,_4R);});break;default:return new F(function(){return _14(_4J,_4R);});}},_4S=function(_4T){return new F(function(){return _4P(_4T,_T);});},_4U=function(_4V,_4W,_4X){return new F(function(){return _4P(_4W,_4X);});},_4Y=44,_4Z=93,_50=91,_51=function(_52,_53,_54){var _55=E(_53);if(!_55._){return new F(function(){return unAppCStr("[]",_54);});}else{var _56=new T(function(){var _57=new T(function(){var _58=function(_59){var _5a=E(_59);if(!_5a._){return E(new T2(1,_4Z,_54));}else{var _5b=new T(function(){return B(A2(_52,_5a.a,new T(function(){return B(_58(_5a.b));})));});return new T2(1,_4Y,_5b);}};return B(_58(_55.b));});return B(A2(_52,_55.a,_57));});return new T2(1,_50,_56);}},_5c=function(_5d,_5e){return new F(function(){return _51(_4P,_5d,_5e);});},_5f=new T3(0,_4U,_4S,_5c),_5g=new T(function(){return new T5(0,_4u,_5f,_5h,_4G,_4S);}),_5h=function(_5i){return new T2(0,_5g,_5i);},_5j=3,_5k=new T(function(){return B(_5h(_5j));}),_5l=new T(function(){return die(_5k);}),_5m=function(_5n,_5o){var _5p=E(_5n);return (_5p._==0)?_5p.a*Math.pow(2,_5o):I_toNumber(_5p.a)*Math.pow(2,_5o);},_5q=function(_5r,_5s){var _5t=E(_5r);if(!_5t._){var _5u=_5t.a,_5v=E(_5s);return (_5v._==0)?_5u==_5v.a:(I_compareInt(_5v.a,_5u)==0)?true:false;}else{var _5w=_5t.a,_5x=E(_5s);return (_5x._==0)?(I_compareInt(_5w,_5x.a)==0)?true:false:(I_compare(_5w,_5x.a)==0)?true:false;}},_5y=function(_5z){var _5A=E(_5z);if(!_5A._){return E(_5A.a);}else{return new F(function(){return I_toInt(_5A.a);});}},_5B=function(_5C,_5D){while(1){var _5E=E(_5C);if(!_5E._){var _5F=_5E.a,_5G=E(_5D);if(!_5G._){var _5H=_5G.a,_5I=addC(_5F,_5H);if(!E(_5I.b)){return new T1(0,_5I.a);}else{_5C=new T1(1,I_fromInt(_5F));_5D=new T1(1,I_fromInt(_5H));continue;}}else{_5C=new T1(1,I_fromInt(_5F));_5D=_5G;continue;}}else{var _5J=E(_5D);if(!_5J._){_5C=_5E;_5D=new T1(1,I_fromInt(_5J.a));continue;}else{return new T1(1,I_add(_5E.a,_5J.a));}}}},_5K=function(_5L,_5M){while(1){var _5N=E(_5L);if(!_5N._){var _5O=E(_5N.a);if(_5O==(-2147483648)){_5L=new T1(1,I_fromInt(-2147483648));continue;}else{var _5P=E(_5M);if(!_5P._){var _5Q=_5P.a;return new T2(0,new T1(0,quot(_5O,_5Q)),new T1(0,_5O%_5Q));}else{_5L=new T1(1,I_fromInt(_5O));_5M=_5P;continue;}}}else{var _5R=E(_5M);if(!_5R._){_5L=_5N;_5M=new T1(1,I_fromInt(_5R.a));continue;}else{var _5S=I_quotRem(_5N.a,_5R.a);return new T2(0,new T1(1,_5S.a),new T1(1,_5S.b));}}}},_5T=new T1(0,0),_5U=function(_5V,_5W){while(1){var _5X=E(_5V);if(!_5X._){_5V=new T1(1,I_fromInt(_5X.a));continue;}else{return new T1(1,I_shiftLeft(_5X.a,_5W));}}},_5Y=function(_5Z,_60,_61){if(!B(_5q(_61,_5T))){var _62=B(_5K(_60,_61)),_63=_62.a;switch(B(_4d(B(_5U(_62.b,1)),_61))){case 0:return new F(function(){return _5m(_63,_5Z);});break;case 1:if(!(B(_5y(_63))&1)){return new F(function(){return _5m(_63,_5Z);});}else{return new F(function(){return _5m(B(_5B(_63,_4c)),_5Z);});}break;default:return new F(function(){return _5m(B(_5B(_63,_4c)),_5Z);});}}else{return E(_5l);}},_64=function(_65,_66){var _67=E(_65);if(!_67._){var _68=_67.a,_69=E(_66);return (_69._==0)?_68>_69.a:I_compareInt(_69.a,_68)<0;}else{var _6a=_67.a,_6b=E(_66);return (_6b._==0)?I_compareInt(_6a,_6b.a)>0:I_compare(_6a,_6b.a)>0;}},_6c=new T1(0,1),_6d=function(_6e,_6f){var _6g=E(_6e);if(!_6g._){var _6h=_6g.a,_6i=E(_6f);return (_6i._==0)?_6h<_6i.a:I_compareInt(_6i.a,_6h)>0;}else{var _6j=_6g.a,_6k=E(_6f);return (_6k._==0)?I_compareInt(_6j,_6k.a)<0:I_compare(_6j,_6k.a)<0;}},_6l=new T(function(){return B(unCStr("base"));}),_6m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6n=new T(function(){return B(unCStr("PatternMatchFail"));}),_6o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6l,_6m,_6n),_6p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6o,_T,_T),_6q=function(_6r){return E(_6p);},_6s=function(_6t){var _6u=E(_6t);return new F(function(){return _4y(B(_4w(_6u.a)),_6q,_6u.b);});},_6v=function(_6w){return E(E(_6w).a);},_6x=function(_6y){return new T2(0,_6z,_6y);},_6A=function(_6B,_6C){return new F(function(){return _14(E(_6B).a,_6C);});},_6D=function(_6E,_6F){return new F(function(){return _51(_6A,_6E,_6F);});},_6G=function(_6H,_6I,_6J){return new F(function(){return _14(E(_6I).a,_6J);});},_6K=new T3(0,_6G,_6v,_6D),_6z=new T(function(){return new T5(0,_6q,_6K,_6x,_6s,_6v);}),_6L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6M=function(_6N){return E(E(_6N).c);},_6O=function(_6P,_6Q){return new F(function(){return die(new T(function(){return B(A2(_6M,_6Q,_6P));}));});},_6R=function(_6S,_5i){return new F(function(){return _6O(_6S,_5i);});},_6T=function(_6U,_6V){var _6W=E(_6V);if(!_6W._){return new T2(0,_T,_T);}else{var _6X=_6W.a;if(!B(A1(_6U,_6X))){return new T2(0,_T,_6W);}else{var _6Y=new T(function(){var _6Z=B(_6T(_6U,_6W.b));return new T2(0,_6Z.a,_6Z.b);});return new T2(0,new T2(1,_6X,new T(function(){return E(E(_6Y).a);})),new T(function(){return E(E(_6Y).b);}));}}},_70=32,_71=new T(function(){return B(unCStr("\n"));}),_72=function(_73){return (E(_73)==124)?false:true;},_74=function(_75,_76){var _77=B(_6T(_72,B(unCStr(_75)))),_78=_77.a,_79=function(_7a,_7b){var _7c=new T(function(){var _7d=new T(function(){return B(_14(_76,new T(function(){return B(_14(_7b,_71));},1)));});return B(unAppCStr(": ",_7d));},1);return new F(function(){return _14(_7a,_7c);});},_7e=E(_77.b);if(!_7e._){return new F(function(){return _79(_78,_T);});}else{if(E(_7e.a)==124){return new F(function(){return _79(_78,new T2(1,_70,_7e.b));});}else{return new F(function(){return _79(_78,_T);});}}},_7f=function(_7g){return new F(function(){return _6R(new T1(0,new T(function(){return B(_74(_7g,_6L));})),_6z);});},_7h=function(_7i){var _7j=function(_7k,_7l){while(1){if(!B(_6d(_7k,_7i))){if(!B(_64(_7k,_7i))){if(!B(_5q(_7k,_7i))){return new F(function(){return _7f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_7l);}}else{return _7l-1|0;}}else{var _7m=B(_5U(_7k,1)),_7n=_7l+1|0;_7k=_7m;_7l=_7n;continue;}}};return new F(function(){return _7j(_6c,0);});},_7o=function(_7p){var _7q=E(_7p);if(!_7q._){var _7r=_7q.a>>>0;if(!_7r){return -1;}else{var _7s=function(_7t,_7u){while(1){if(_7t>=_7r){if(_7t<=_7r){if(_7t!=_7r){return new F(function(){return _7f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_7u);}}else{return _7u-1|0;}}else{var _7v=imul(_7t,2)>>>0,_7w=_7u+1|0;_7t=_7v;_7u=_7w;continue;}}};return new F(function(){return _7s(1,0);});}}else{return new F(function(){return _7h(_7q);});}},_7x=function(_7y){var _7z=E(_7y);if(!_7z._){var _7A=_7z.a>>>0;if(!_7A){return new T2(0,-1,0);}else{var _7B=function(_7C,_7D){while(1){if(_7C>=_7A){if(_7C<=_7A){if(_7C!=_7A){return new F(function(){return _7f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_7D);}}else{return _7D-1|0;}}else{var _7E=imul(_7C,2)>>>0,_7F=_7D+1|0;_7C=_7E;_7D=_7F;continue;}}};return new T2(0,B(_7B(1,0)),(_7A&_7A-1>>>0)>>>0&4294967295);}}else{var _7G=_7z.a;return new T2(0,B(_7o(_7z)),I_compareInt(I_and(_7G,I_sub(_7G,I_fromInt(1))),0));}},_7H=function(_7I,_7J){var _7K=E(_7I);if(!_7K._){var _7L=_7K.a,_7M=E(_7J);return (_7M._==0)?_7L<=_7M.a:I_compareInt(_7M.a,_7L)>=0;}else{var _7N=_7K.a,_7O=E(_7J);return (_7O._==0)?I_compareInt(_7N,_7O.a)<=0:I_compare(_7N,_7O.a)<=0;}},_7P=function(_7Q,_7R){while(1){var _7S=E(_7Q);if(!_7S._){var _7T=_7S.a,_7U=E(_7R);if(!_7U._){return new T1(0,(_7T>>>0&_7U.a>>>0)>>>0&4294967295);}else{_7Q=new T1(1,I_fromInt(_7T));_7R=_7U;continue;}}else{var _7V=E(_7R);if(!_7V._){_7Q=_7S;_7R=new T1(1,I_fromInt(_7V.a));continue;}else{return new T1(1,I_and(_7S.a,_7V.a));}}}},_7W=function(_7X,_7Y){while(1){var _7Z=E(_7X);if(!_7Z._){var _80=_7Z.a,_81=E(_7Y);if(!_81._){var _82=_81.a,_83=subC(_80,_82);if(!E(_83.b)){return new T1(0,_83.a);}else{_7X=new T1(1,I_fromInt(_80));_7Y=new T1(1,I_fromInt(_82));continue;}}else{_7X=new T1(1,I_fromInt(_80));_7Y=_81;continue;}}else{var _84=E(_7Y);if(!_84._){_7X=_7Z;_7Y=new T1(1,I_fromInt(_84.a));continue;}else{return new T1(1,I_sub(_7Z.a,_84.a));}}}},_85=new T1(0,2),_86=function(_87,_88){var _89=E(_87);if(!_89._){var _8a=(_89.a>>>0&(2<<_88>>>0)-1>>>0)>>>0,_8b=1<<_88>>>0;return (_8b<=_8a)?(_8b>=_8a)?1:2:0;}else{var _8c=B(_7P(_89,B(_7W(B(_5U(_85,_88)),_6c)))),_8d=B(_5U(_6c,_88));return (!B(_64(_8d,_8c)))?(!B(_6d(_8d,_8c)))?1:2:0;}},_8e=function(_8f,_8g){while(1){var _8h=E(_8f);if(!_8h._){_8f=new T1(1,I_fromInt(_8h.a));continue;}else{return new T1(1,I_shiftRight(_8h.a,_8g));}}},_8i=function(_8j,_8k,_8l,_8m){var _8n=B(_7x(_8m)),_8o=_8n.a;if(!E(_8n.b)){var _8p=B(_7o(_8l));if(_8p<((_8o+_8j|0)-1|0)){var _8q=_8o+(_8j-_8k|0)|0;if(_8q>0){if(_8q>_8p){if(_8q<=(_8p+1|0)){if(!E(B(_7x(_8l)).b)){return 0;}else{return new F(function(){return _5m(_4c,_8j-_8k|0);});}}else{return 0;}}else{var _8r=B(_8e(_8l,_8q));switch(B(_86(_8l,_8q-1|0))){case 0:return new F(function(){return _5m(_8r,_8j-_8k|0);});break;case 1:if(!(B(_5y(_8r))&1)){return new F(function(){return _5m(_8r,_8j-_8k|0);});}else{return new F(function(){return _5m(B(_5B(_8r,_4c)),_8j-_8k|0);});}break;default:return new F(function(){return _5m(B(_5B(_8r,_4c)),_8j-_8k|0);});}}}else{return new F(function(){return _5m(_8l,(_8j-_8k|0)-_8q|0);});}}else{if(_8p>=_8k){var _8s=B(_8e(_8l,(_8p+1|0)-_8k|0));switch(B(_86(_8l,_8p-_8k|0))){case 0:return new F(function(){return _5m(_8s,((_8p-_8o|0)+1|0)-_8k|0);});break;case 2:return new F(function(){return _5m(B(_5B(_8s,_4c)),((_8p-_8o|0)+1|0)-_8k|0);});break;default:if(!(B(_5y(_8s))&1)){return new F(function(){return _5m(_8s,((_8p-_8o|0)+1|0)-_8k|0);});}else{return new F(function(){return _5m(B(_5B(_8s,_4c)),((_8p-_8o|0)+1|0)-_8k|0);});}}}else{return new F(function(){return _5m(_8l, -_8o);});}}}else{var _8t=B(_7o(_8l))-_8o|0,_8u=function(_8v){var _8w=function(_8x,_8y){if(!B(_7H(B(_5U(_8y,_8k)),_8x))){return new F(function(){return _5Y(_8v-_8k|0,_8x,_8y);});}else{return new F(function(){return _5Y((_8v-_8k|0)+1|0,_8x,B(_5U(_8y,1)));});}};if(_8v>=_8k){if(_8v!=_8k){return new F(function(){return _8w(_8l,new T(function(){return B(_5U(_8m,_8v-_8k|0));}));});}else{return new F(function(){return _8w(_8l,_8m);});}}else{return new F(function(){return _8w(new T(function(){return B(_5U(_8l,_8k-_8v|0));}),_8m);});}};if(_8j>_8t){return new F(function(){return _8u(_8j);});}else{return new F(function(){return _8u(_8t);});}}},_8z=new T1(0,2147483647),_8A=new T(function(){return B(_5B(_8z,_6c));}),_8B=function(_8C){var _8D=E(_8C);if(!_8D._){var _8E=E(_8D.a);return (_8E==(-2147483648))?E(_8A):new T1(0, -_8E);}else{return new T1(1,I_negate(_8D.a));}},_8F=new T(function(){return 0/0;}),_8G=new T(function(){return -1/0;}),_8H=new T(function(){return 1/0;}),_8I=0,_8J=function(_8K,_8L){if(!B(_5q(_8L,_5T))){if(!B(_5q(_8K,_5T))){if(!B(_6d(_8K,_5T))){return new F(function(){return _8i(-1021,53,_8K,_8L);});}else{return  -B(_8i(-1021,53,B(_8B(_8K)),_8L));}}else{return E(_8I);}}else{return (!B(_5q(_8K,_5T)))?(!B(_6d(_8K,_5T)))?E(_8H):E(_8G):E(_8F);}},_8M=function(_8N){return new T1(0,new T(function(){var _8O=E(_8N),_8P=jsShow(B(_8J(_8O.a,_8O.b)));return fromJSStr(_8P);}));},_8Q=new T(function(){return B(unCStr("1./("));}),_8R=new T1(0,_8Q),_8S=function(_8T){return new T1(1,new T2(1,_8R,new T2(1,_8T,_2W)));},_8U=new T(function(){return B(unCStr(")+("));}),_8V=new T1(0,_8U),_8W=function(_8X,_8Y){return new T1(1,new T2(1,_46,new T2(1,_8X,new T2(1,_8V,new T2(1,_8Y,_2W)))));},_8Z=new T(function(){return B(unCStr("-("));}),_90=new T1(0,_8Z),_91=function(_92){return new T1(1,new T2(1,_90,new T2(1,_92,_2W)));},_93=new T(function(){return B(unCStr(")*("));}),_94=new T1(0,_93),_95=function(_96,_97){return new T1(1,new T2(1,_46,new T2(1,_96,new T2(1,_94,new T2(1,_97,_2W)))));},_98=function(_99,_9a){return new F(function(){return A3(_1S,_9b,_99,new T(function(){return B(A2(_2l,_9b,_9a));}));});},_9c=new T(function(){return B(unCStr("abs("));}),_9d=new T1(0,_9c),_9e=function(_9f){return new T1(1,new T2(1,_9d,new T2(1,_9f,_2W)));},_9g=function(_9h){while(1){var _9i=E(_9h);if(!_9i._){_9h=new T1(1,I_fromInt(_9i.a));continue;}else{return new F(function(){return I_toString(_9i.a);});}}},_9j=function(_9k,_9l){return new F(function(){return _14(fromJSStr(B(_9g(_9k))),_9l);});},_9m=41,_9n=40,_9o=new T1(0,0),_9p=function(_9q,_9r,_9s){if(_9q<=6){return new F(function(){return _9j(_9r,_9s);});}else{if(!B(_6d(_9r,_9o))){return new F(function(){return _9j(_9r,_9s);});}else{return new T2(1,_9n,new T(function(){return B(_14(fromJSStr(B(_9g(_9r))),new T2(1,_9m,_9s)));}));}}},_9t=new T(function(){return B(unCStr("."));}),_9u=function(_9v){return new T1(0,new T(function(){return B(_14(B(_9p(0,_9v,_T)),_9t));}));},_9w=new T(function(){return B(unCStr("sign("));}),_9x=new T1(0,_9w),_9y=function(_9z){return new T1(1,new T2(1,_9x,new T2(1,_9z,_2W)));},_9b=new T(function(){return {_:0,a:_8W,b:_98,c:_95,d:_91,e:_9e,f:_9y,g:_9u};}),_9A=new T4(0,_9b,_49,_8S,_8M),_9B={_:0,a:_9A,b:_3K,c:_3y,d:_3C,e:_3V,f:_2X,g:_3G,h:_3N,i:_3q,j:_3Z,k:_3a,l:_32,m:_3i,n:_3R,o:_3u,p:_43,q:_3e,r:_36,s:_3m},_9C=new T(function(){return B(unCStr("(/=) is not defined"));}),_9D=new T(function(){return B(err(_9C));}),_9E=new T(function(){return B(unCStr("(==) is not defined"));}),_9F=new T(function(){return B(err(_9E));}),_9G=new T2(0,_9F,_9D),_9H=new T(function(){return B(unCStr("(<) is not defined"));}),_9I=new T(function(){return B(err(_9H));}),_9J=new T(function(){return B(unCStr("(<=) is not defined"));}),_9K=new T(function(){return B(err(_9J));}),_9L=new T(function(){return B(unCStr("(>) is not defined"));}),_9M=new T(function(){return B(err(_9L));}),_9N=new T(function(){return B(unCStr("(>=) is not defined"));}),_9O=new T(function(){return B(err(_9N));}),_9P=new T(function(){return B(unCStr("compare is not defined"));}),_9Q=new T(function(){return B(err(_9P));}),_9R=new T(function(){return B(unCStr("max("));}),_9S=new T1(0,_9R),_9T=function(_9U,_9V){return new T1(1,new T2(1,_9S,new T2(1,_9U,new T2(1,_2R,new T2(1,_9V,_2W)))));},_9W=new T(function(){return B(unCStr("min("));}),_9X=new T1(0,_9W),_9Y=function(_9Z,_a0){return new T1(1,new T2(1,_9X,new T2(1,_9Z,new T2(1,_2R,new T2(1,_a0,_2W)))));},_a1={_:0,a:_9G,b:_9Q,c:_9I,d:_9K,e:_9M,f:_9O,g:_9T,h:_9Y},_a2=new T2(0,_9B,_a1),_a3=new T(function(){return B(_2p(_a2));}),_a4=new T(function(){return B(A1(_a3,_1K));}),_a5=new T(function(){return toJSStr(B(_1o(_1D,_11,_a4)));}),_a6=function(_a7,_a8,_a9){var _aa=new T(function(){return B(_1k(_a7));}),_ab=new T(function(){return B(_1m(_a7));}),_ac=function(_ad){var _ae=E(_ad);if(!_ae._){return E(_ab);}else{return new F(function(){return A2(_aa,new T(function(){return B(_1o(_a7,_a8,_ae.a));}),new T(function(){return B(_ac(_ae.b));}));});}};return new F(function(){return _ac(_a9);});},_af=function(_ag,_ah){var _ai=E(_ag);return E(_ah);},_aj=function(_ak,_al){var _am=E(_ak),_an=E(_al);return new T3(0,new T(function(){return B(A1(_am.a,_an.a));}),new T(function(){return B(A1(_am.b,_an.b));}),new T(function(){return B(A1(_am.c,_an.c));}));},_ao=function(_ap){return new T3(0,_ap,_ap,_ap);},_aq=function(_ar,_as){var _at=E(_as);return new T3(0,_ar,_ar,_ar);},_au=function(_av,_aw){var _ax=E(_aw);return new T3(0,new T(function(){return B(A1(_av,_ax.a));}),new T(function(){return B(A1(_av,_ax.b));}),new T(function(){return B(A1(_av,_ax.c));}));},_ay=new T2(0,_au,_aq),_az=function(_aA,_aB){var _aC=E(_aA),_aD=E(_aB);return new T3(0,_aC.a,_aC.b,_aC.c);},_aE=new T5(0,_ay,_ao,_aj,_af,_az),_aF=new T1(0,1),_aG=function(_aH){return new T3(0,new T3(0,new T(function(){return B(A2(_28,_aH,_aF));}),new T(function(){return B(A2(_28,_aH,_1L));}),new T(function(){return B(A2(_28,_aH,_1L));})),new T3(0,new T(function(){return B(A2(_28,_aH,_1L));}),new T(function(){return B(A2(_28,_aH,_aF));}),new T(function(){return B(A2(_28,_aH,_1L));})),new T3(0,new T(function(){return B(A2(_28,_aH,_1L));}),new T(function(){return B(A2(_28,_aH,_1L));}),new T(function(){return B(A2(_28,_aH,_aF));})));},_aI=function(_aJ){var _aK=B(_aG(_aJ));return new T3(0,_aK.a,_aK.b,_aK.c);},_aL=new T(function(){return B(unCStr("(/=) is not defined"));}),_aM=new T(function(){return B(err(_aL));}),_aN=new T(function(){return B(unCStr("(==) is not defined"));}),_aO=new T(function(){return B(err(_aN));}),_aP=new T2(0,_aO,_aM),_aQ=function(_aR){return E(_aP);},_aS=function(_aT){return E(E(_aT).a);},_aU=function(_aV){return E(E(_aV).f);},_aW=function(_aX){return E(E(_aX).b);},_aY=function(_aZ){return E(E(_aZ).c);},_b0=function(_b1){return E(E(_b1).a);},_b2=function(_b3){return E(E(_b3).d);},_b4=function(_b5,_b6,_b7,_b8,_b9){var _ba=new T(function(){return E(E(E(_b5).c).a);}),_bb=new T(function(){var _bc=E(_b5).a,_bd=new T(function(){var _be=new T(function(){return B(_1M(_ba));}),_bf=new T(function(){return B(_1O(_be));}),_bg=new T(function(){return B(A2(_b2,_ba,_b6));}),_bh=new T(function(){return B(A3(_aU,_ba,_b6,_b8));}),_bi=function(_bj,_bk){var _bl=new T(function(){var _bm=new T(function(){return B(A3(_aW,_be,new T(function(){return B(A3(_1Q,_bf,_b8,_bj));}),_b6));});return B(A3(_1S,_bf,_bm,new T(function(){return B(A3(_1Q,_bf,_bk,_bg));})));});return new F(function(){return A3(_1Q,_bf,_bh,_bl);});};return B(A3(_b0,B(_aS(_bc)),_bi,_b7));});return B(A3(_aY,_bc,_bd,_b9));});return new T2(0,new T(function(){return B(A3(_aU,_ba,_b6,_b8));}),_bb);},_bn=function(_bo,_bp,_bq,_br){var _bs=E(_bq),_bt=E(_br),_bu=B(_b4(_bp,_bs.a,_bs.b,_bt.a,_bt.b));return new T2(0,_bu.a,_bu.b);},_bv=new T1(0,1),_bw=function(_bx){return E(E(_bx).l);},_by=function(_bz,_bA,_bB){var _bC=new T(function(){return E(E(E(_bz).c).a);}),_bD=new T(function(){var _bE=new T(function(){return B(_1M(_bC));}),_bF=new T(function(){var _bG=B(_1O(_bE)),_bH=new T(function(){var _bI=new T(function(){return B(A3(_24,_bG,new T(function(){return B(A2(_28,_bG,_bv));}),new T(function(){return B(A3(_1Q,_bG,_bA,_bA));})));});return B(A2(_2n,_bC,_bI));});return B(A2(_2l,_bG,_bH));});return B(A3(_b0,B(_aS(E(_bz).a)),function(_bJ){return new F(function(){return A3(_aW,_bE,_bJ,_bF);});},_bB));});return new T2(0,new T(function(){return B(A2(_bw,_bC,_bA));}),_bD);},_bK=function(_bL,_bM,_bN){var _bO=E(_bN),_bP=B(_by(_bM,_bO.a,_bO.b));return new T2(0,_bP.a,_bP.b);},_bQ=function(_bR){return E(E(_bR).r);},_bS=function(_bT,_bU,_bV){var _bW=new T(function(){return E(E(E(_bT).c).a);}),_bX=new T(function(){var _bY=new T(function(){return B(_1M(_bW));}),_bZ=new T(function(){var _c0=new T(function(){var _c1=B(_1O(_bY));return B(A3(_24,_c1,new T(function(){return B(A3(_1Q,_c1,_bU,_bU));}),new T(function(){return B(A2(_28,_c1,_bv));})));});return B(A2(_2n,_bW,_c0));});return B(A3(_b0,B(_aS(E(_bT).a)),function(_c2){return new F(function(){return A3(_aW,_bY,_c2,_bZ);});},_bV));});return new T2(0,new T(function(){return B(A2(_bQ,_bW,_bU));}),_bX);},_c3=function(_c4,_c5,_c6){var _c7=E(_c6),_c8=B(_bS(_c5,_c7.a,_c7.b));return new T2(0,_c8.a,_c8.b);},_c9=function(_ca){return E(E(_ca).k);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_1M(_cf));}),_ci=new T(function(){var _cj=new T(function(){var _ck=B(_1O(_ch));return B(A3(_24,_ck,new T(function(){return B(A2(_28,_ck,_bv));}),new T(function(){return B(A3(_1Q,_ck,_cd,_cd));})));});return B(A2(_2n,_cf,_cj));});return B(A3(_b0,B(_aS(E(_cc).a)),function(_cl){return new F(function(){return A3(_aW,_ch,_cl,_ci);});},_ce));});return new T2(0,new T(function(){return B(A2(_c9,_cf,_cd));}),_cg);},_cm=function(_cn,_co,_cp){var _cq=E(_cp),_cr=B(_cb(_co,_cq.a,_cq.b));return new T2(0,_cr.a,_cr.b);},_cs=function(_ct){return E(E(_ct).q);},_cu=function(_cv,_cw,_cx){var _cy=new T(function(){return E(E(E(_cv).c).a);}),_cz=new T(function(){var _cA=new T(function(){return B(_1M(_cy));}),_cB=new T(function(){var _cC=new T(function(){var _cD=B(_1O(_cA));return B(A3(_1S,_cD,new T(function(){return B(A3(_1Q,_cD,_cw,_cw));}),new T(function(){return B(A2(_28,_cD,_bv));})));});return B(A2(_2n,_cy,_cC));});return B(A3(_b0,B(_aS(E(_cv).a)),function(_cE){return new F(function(){return A3(_aW,_cA,_cE,_cB);});},_cx));});return new T2(0,new T(function(){return B(A2(_cs,_cy,_cw));}),_cz);},_cF=function(_cG,_cH,_cI){var _cJ=E(_cI),_cK=B(_cu(_cH,_cJ.a,_cJ.b));return new T2(0,_cK.a,_cK.b);},_cL=function(_cM){return E(E(_cM).m);},_cN=function(_cO,_cP,_cQ){var _cR=new T(function(){return E(E(E(_cO).c).a);}),_cS=new T(function(){var _cT=new T(function(){return B(_1M(_cR));}),_cU=new T(function(){var _cV=B(_1O(_cT));return B(A3(_1S,_cV,new T(function(){return B(A2(_28,_cV,_bv));}),new T(function(){return B(A3(_1Q,_cV,_cP,_cP));})));});return B(A3(_b0,B(_aS(E(_cO).a)),function(_cW){return new F(function(){return A3(_aW,_cT,_cW,_cU);});},_cQ));});return new T2(0,new T(function(){return B(A2(_cL,_cR,_cP));}),_cS);},_cX=function(_cY,_cZ,_d0){var _d1=E(_d0),_d2=B(_cN(_cZ,_d1.a,_d1.b));return new T2(0,_d2.a,_d2.b);},_d3=function(_d4){return E(E(_d4).s);},_d5=function(_d6,_d7,_d8){var _d9=new T(function(){return E(E(E(_d6).c).a);}),_da=new T(function(){var _db=new T(function(){return B(_1M(_d9));}),_dc=new T(function(){var _dd=B(_1O(_db));return B(A3(_24,_dd,new T(function(){return B(A2(_28,_dd,_bv));}),new T(function(){return B(A3(_1Q,_dd,_d7,_d7));})));});return B(A3(_b0,B(_aS(E(_d6).a)),function(_de){return new F(function(){return A3(_aW,_db,_de,_dc);});},_d8));});return new T2(0,new T(function(){return B(A2(_d3,_d9,_d7));}),_da);},_df=function(_dg,_dh,_di){var _dj=E(_di),_dk=B(_d5(_dh,_dj.a,_dj.b));return new T2(0,_dk.a,_dk.b);},_dl=function(_dm){return E(E(_dm).i);},_dn=function(_do){return E(E(_do).h);},_dp=function(_dq,_dr,_ds){var _dt=new T(function(){return E(E(E(_dq).c).a);}),_du=new T(function(){var _dv=new T(function(){return B(_1O(new T(function(){return B(_1M(_dt));})));}),_dw=new T(function(){return B(A2(_2l,_dv,new T(function(){return B(A2(_dn,_dt,_dr));})));});return B(A3(_b0,B(_aS(E(_dq).a)),function(_dx){return new F(function(){return A3(_1Q,_dv,_dx,_dw);});},_ds));});return new T2(0,new T(function(){return B(A2(_dl,_dt,_dr));}),_du);},_dy=function(_dz,_dA,_dB){var _dC=E(_dB),_dD=B(_dp(_dA,_dC.a,_dC.b));return new T2(0,_dD.a,_dD.b);},_dE=function(_dF){return E(E(_dF).o);},_dG=function(_dH){return E(E(_dH).n);},_dI=function(_dJ,_dK,_dL){var _dM=new T(function(){return E(E(E(_dJ).c).a);}),_dN=new T(function(){var _dO=new T(function(){return B(_1O(new T(function(){return B(_1M(_dM));})));}),_dP=new T(function(){return B(A2(_dG,_dM,_dK));});return B(A3(_b0,B(_aS(E(_dJ).a)),function(_dQ){return new F(function(){return A3(_1Q,_dO,_dQ,_dP);});},_dL));});return new T2(0,new T(function(){return B(A2(_dE,_dM,_dK));}),_dN);},_dR=function(_dS,_dT,_dU){var _dV=E(_dU),_dW=B(_dI(_dT,_dV.a,_dV.b));return new T2(0,_dW.a,_dW.b);},_dX=function(_dY){return E(E(_dY).c);},_dZ=function(_e0,_e1,_e2){var _e3=new T(function(){return E(E(E(_e0).c).a);}),_e4=new T(function(){var _e5=new T(function(){return B(_1O(new T(function(){return B(_1M(_e3));})));}),_e6=new T(function(){return B(A2(_dX,_e3,_e1));});return B(A3(_b0,B(_aS(E(_e0).a)),function(_e7){return new F(function(){return A3(_1Q,_e5,_e7,_e6);});},_e2));});return new T2(0,new T(function(){return B(A2(_dX,_e3,_e1));}),_e4);},_e8=function(_e9,_ea,_eb){var _ec=E(_eb),_ed=B(_dZ(_ea,_ec.a,_ec.b));return new T2(0,_ed.a,_ed.b);},_ee=function(_ef,_eg,_eh){var _ei=new T(function(){return E(E(E(_ef).c).a);}),_ej=new T(function(){var _ek=new T(function(){return B(_1M(_ei));}),_el=new T(function(){return B(_1O(_ek));}),_em=new T(function(){return B(A3(_aW,_ek,new T(function(){return B(A2(_28,_el,_bv));}),_eg));});return B(A3(_b0,B(_aS(E(_ef).a)),function(_en){return new F(function(){return A3(_1Q,_el,_en,_em);});},_eh));});return new T2(0,new T(function(){return B(A2(_b2,_ei,_eg));}),_ej);},_eo=function(_ep,_eq,_er){var _es=E(_er),_et=B(_ee(_eq,_es.a,_es.b));return new T2(0,_et.a,_et.b);},_eu=function(_ev,_ew,_ex,_ey){var _ez=new T(function(){return E(E(_ew).c);}),_eA=new T3(0,new T(function(){return E(E(_ew).a);}),new T(function(){return E(E(_ew).b);}),new T2(0,new T(function(){return E(E(_ez).a);}),new T(function(){return E(E(_ez).b);})));return new F(function(){return A3(_aW,_ev,new T(function(){var _eB=E(_ey),_eC=B(_ee(_eA,_eB.a,_eB.b));return new T2(0,_eC.a,_eC.b);}),new T(function(){var _eD=E(_ex),_eE=B(_ee(_eA,_eD.a,_eD.b));return new T2(0,_eE.a,_eE.b);}));});},_eF=new T1(0,0),_eG=function(_eH){return E(E(_eH).b);},_eI=function(_eJ){return E(E(_eJ).b);},_eK=function(_eL){var _eM=new T(function(){return E(E(E(_eL).c).a);}),_eN=new T(function(){return B(A2(_eI,E(_eL).a,new T(function(){return B(A2(_28,B(_1O(B(_1M(_eM)))),_eF));})));});return new T2(0,new T(function(){return B(_eG(_eM));}),_eN);},_eO=function(_eP,_eQ){var _eR=B(_eK(_eQ));return new T2(0,_eR.a,_eR.b);},_eS=function(_eT,_eU,_eV){var _eW=new T(function(){return E(E(E(_eT).c).a);}),_eX=new T(function(){var _eY=new T(function(){return B(_1O(new T(function(){return B(_1M(_eW));})));}),_eZ=new T(function(){return B(A2(_dl,_eW,_eU));});return B(A3(_b0,B(_aS(E(_eT).a)),function(_f0){return new F(function(){return A3(_1Q,_eY,_f0,_eZ);});},_eV));});return new T2(0,new T(function(){return B(A2(_dn,_eW,_eU));}),_eX);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eS(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9,_fa){var _fb=new T(function(){return E(E(E(_f8).c).a);}),_fc=new T(function(){var _fd=new T(function(){return B(_1O(new T(function(){return B(_1M(_fb));})));}),_fe=new T(function(){return B(A2(_dE,_fb,_f9));});return B(A3(_b0,B(_aS(E(_f8).a)),function(_ff){return new F(function(){return A3(_1Q,_fd,_ff,_fe);});},_fa));});return new T2(0,new T(function(){return B(A2(_dG,_fb,_f9));}),_fc);},_fg=function(_fh,_fi,_fj){var _fk=E(_fj),_fl=B(_f7(_fi,_fk.a,_fk.b));return new T2(0,_fl.a,_fl.b);},_fm=new T1(0,2),_fn=function(_fo,_fp,_fq){var _fr=new T(function(){return E(E(E(_fo).c).a);}),_fs=new T(function(){var _ft=new T(function(){return B(_1M(_fr));}),_fu=new T(function(){return B(_1O(_ft));}),_fv=new T(function(){var _fw=new T(function(){return B(A3(_aW,_ft,new T(function(){return B(A2(_28,_fu,_bv));}),new T(function(){return B(A2(_28,_fu,_fm));})));});return B(A3(_aW,_ft,_fw,new T(function(){return B(A2(_2n,_fr,_fp));})));});return B(A3(_b0,B(_aS(E(_fo).a)),function(_fx){return new F(function(){return A3(_1Q,_fu,_fx,_fv);});},_fq));});return new T2(0,new T(function(){return B(A2(_2n,_fr,_fp));}),_fs);},_fy=function(_fz,_fA,_fB){var _fC=E(_fB),_fD=B(_fn(_fA,_fC.a,_fC.b));return new T2(0,_fD.a,_fD.b);},_fE=function(_fF){return E(E(_fF).j);},_fG=function(_fH,_fI,_fJ){var _fK=new T(function(){return E(E(E(_fH).c).a);}),_fL=new T(function(){var _fM=new T(function(){return B(_1M(_fK));}),_fN=new T(function(){var _fO=new T(function(){return B(A2(_dl,_fK,_fI));});return B(A3(_1Q,B(_1O(_fM)),_fO,_fO));});return B(A3(_b0,B(_aS(E(_fH).a)),function(_fP){return new F(function(){return A3(_aW,_fM,_fP,_fN);});},_fJ));});return new T2(0,new T(function(){return B(A2(_fE,_fK,_fI));}),_fL);},_fQ=function(_fR,_fS,_fT){var _fU=E(_fT),_fV=B(_fG(_fS,_fU.a,_fU.b));return new T2(0,_fV.a,_fV.b);},_fW=function(_fX){return E(E(_fX).p);},_fY=function(_fZ,_g0,_g1){var _g2=new T(function(){return E(E(E(_fZ).c).a);}),_g3=new T(function(){var _g4=new T(function(){return B(_1M(_g2));}),_g5=new T(function(){var _g6=new T(function(){return B(A2(_dE,_g2,_g0));});return B(A3(_1Q,B(_1O(_g4)),_g6,_g6));});return B(A3(_b0,B(_aS(E(_fZ).a)),function(_g7){return new F(function(){return A3(_aW,_g4,_g7,_g5);});},_g1));});return new T2(0,new T(function(){return B(A2(_fW,_g2,_g0));}),_g3);},_g8=function(_g9,_ga,_gb){var _gc=E(_gb),_gd=B(_fY(_ga,_gc.a,_gc.b));return new T2(0,_gd.a,_gd.b);},_ge=function(_gf,_gg){return {_:0,a:_gf,b:new T(function(){return B(_eO(_gf,_gg));}),c:function(_gh){return new F(function(){return _e8(_gf,_gg,_gh);});},d:function(_gh){return new F(function(){return _eo(_gf,_gg,_gh);});},e:function(_gh){return new F(function(){return _fy(_gf,_gg,_gh);});},f:function(_gi,_gh){return new F(function(){return _bn(_gf,_gg,_gi,_gh);});},g:function(_gi,_gh){return new F(function(){return _eu(_gf,_gg,_gi,_gh);});},h:function(_gh){return new F(function(){return _f1(_gf,_gg,_gh);});},i:function(_gh){return new F(function(){return _dy(_gf,_gg,_gh);});},j:function(_gh){return new F(function(){return _fQ(_gf,_gg,_gh);});},k:function(_gh){return new F(function(){return _cm(_gf,_gg,_gh);});},l:function(_gh){return new F(function(){return _bK(_gf,_gg,_gh);});},m:function(_gh){return new F(function(){return _cX(_gf,_gg,_gh);});},n:function(_gh){return new F(function(){return _fg(_gf,_gg,_gh);});},o:function(_gh){return new F(function(){return _dR(_gf,_gg,_gh);});},p:function(_gh){return new F(function(){return _g8(_gf,_gg,_gh);});},q:function(_gh){return new F(function(){return _cF(_gf,_gg,_gh);});},r:function(_gh){return new F(function(){return _c3(_gf,_gg,_gh);});},s:function(_gh){return new F(function(){return _df(_gf,_gg,_gh);});}};},_gj=function(_gk,_gl,_gm,_gn,_go){var _gp=new T(function(){return B(_1M(new T(function(){return E(E(E(_gk).c).a);})));}),_gq=new T(function(){var _gr=E(_gk).a,_gs=new T(function(){var _gt=new T(function(){return B(_1O(_gp));}),_gu=new T(function(){return B(A3(_1Q,_gt,_gn,_gn));}),_gv=function(_gw,_gx){var _gy=new T(function(){return B(A3(_24,_gt,new T(function(){return B(A3(_1Q,_gt,_gw,_gn));}),new T(function(){return B(A3(_1Q,_gt,_gl,_gx));})));});return new F(function(){return A3(_aW,_gp,_gy,_gu);});};return B(A3(_b0,B(_aS(_gr)),_gv,_gm));});return B(A3(_aY,_gr,_gs,_go));});return new T2(0,new T(function(){return B(A3(_aW,_gp,_gl,_gn));}),_gq);},_gz=function(_gA,_gB,_gC,_gD){var _gE=E(_gC),_gF=E(_gD),_gG=B(_gj(_gB,_gE.a,_gE.b,_gF.a,_gF.b));return new T2(0,_gG.a,_gG.b);},_gH=function(_gI,_gJ){var _gK=new T(function(){return B(_1M(new T(function(){return E(E(E(_gI).c).a);})));}),_gL=new T(function(){return B(A2(_eI,E(_gI).a,new T(function(){return B(A2(_28,B(_1O(_gK)),_eF));})));});return new T2(0,new T(function(){return B(A2(_2a,_gK,_gJ));}),_gL);},_gM=function(_gN,_gO,_gP){var _gQ=B(_gH(_gO,_gP));return new T2(0,_gQ.a,_gQ.b);},_gR=function(_gS,_gT,_gU){var _gV=new T(function(){return B(_1M(new T(function(){return E(E(E(_gS).c).a);})));}),_gW=new T(function(){return B(_1O(_gV));}),_gX=new T(function(){var _gY=new T(function(){var _gZ=new T(function(){return B(A3(_aW,_gV,new T(function(){return B(A2(_28,_gW,_bv));}),new T(function(){return B(A3(_1Q,_gW,_gT,_gT));})));});return B(A2(_2l,_gW,_gZ));});return B(A3(_b0,B(_aS(E(_gS).a)),function(_h0){return new F(function(){return A3(_1Q,_gW,_h0,_gY);});},_gU));}),_h1=new T(function(){return B(A3(_aW,_gV,new T(function(){return B(A2(_28,_gW,_bv));}),_gT));});return new T2(0,_h1,_gX);},_h2=function(_h3,_h4,_h5){var _h6=E(_h5),_h7=B(_gR(_h4,_h6.a,_h6.b));return new T2(0,_h7.a,_h7.b);},_h8=function(_h9,_ha){return new T4(0,_h9,function(_gi,_gh){return new F(function(){return _gz(_h9,_ha,_gi,_gh);});},function(_gh){return new F(function(){return _h2(_h9,_ha,_gh);});},function(_gh){return new F(function(){return _gM(_h9,_ha,_gh);});});},_hb=function(_hc,_hd,_he,_hf,_hg){var _hh=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_hc).c).a);})));})));}),_hi=new T(function(){var _hj=E(_hc).a,_hk=new T(function(){var _hl=function(_hm,_hn){return new F(function(){return A3(_1S,_hh,new T(function(){return B(A3(_1Q,_hh,_hd,_hn));}),new T(function(){return B(A3(_1Q,_hh,_hm,_hf));}));});};return B(A3(_b0,B(_aS(_hj)),_hl,_he));});return B(A3(_aY,_hj,_hk,_hg));});return new T2(0,new T(function(){return B(A3(_1Q,_hh,_hd,_hf));}),_hi);},_ho=function(_hp,_hq,_hr){var _hs=E(_hq),_ht=E(_hr),_hu=B(_hb(_hp,_hs.a,_hs.b,_ht.a,_ht.b));return new T2(0,_hu.a,_hu.b);},_hv=function(_hw,_hx,_hy,_hz,_hA){var _hB=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_hw).c).a);})));})));}),_hC=new T(function(){var _hD=E(_hw).a,_hE=new T(function(){return B(A3(_b0,B(_aS(_hD)),new T(function(){return B(_1S(_hB));}),_hy));});return B(A3(_aY,_hD,_hE,_hA));});return new T2(0,new T(function(){return B(A3(_1S,_hB,_hx,_hz));}),_hC);},_hF=function(_hG,_hH,_hI){var _hJ=E(_hH),_hK=E(_hI),_hL=B(_hv(_hG,_hJ.a,_hJ.b,_hK.a,_hK.b));return new T2(0,_hL.a,_hL.b);},_hM=function(_hN,_hO,_hP){var _hQ=B(_hR(_hN));return new F(function(){return A3(_1S,_hQ,_hO,new T(function(){return B(A2(_2l,_hQ,_hP));}));});},_hS=function(_hT){return E(E(_hT).f);},_hU=function(_hV,_hW,_hX){var _hY=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_hV).c).a);})));})));}),_hZ=new T(function(){var _i0=new T(function(){return B(A2(_hS,_hY,_hW));});return B(A3(_b0,B(_aS(E(_hV).a)),function(_i1){return new F(function(){return A3(_1Q,_hY,_i1,_i0);});},_hX));});return new T2(0,new T(function(){return B(A2(_26,_hY,_hW));}),_hZ);},_i2=function(_i3,_i4){var _i5=E(_i4),_i6=B(_hU(_i3,_i5.a,_i5.b));return new T2(0,_i6.a,_i6.b);},_i7=function(_i8,_i9){var _ia=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_i8).c).a);})));})));}),_ib=new T(function(){return B(A2(_eI,E(_i8).a,new T(function(){return B(A2(_28,_ia,_eF));})));});return new T2(0,new T(function(){return B(A2(_28,_ia,_i9));}),_ib);},_ic=function(_id,_ie){var _if=B(_i7(_id,_ie));return new T2(0,_if.a,_if.b);},_ig=function(_ih,_ii,_ij){var _ik=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_ih).c).a);})));})));}),_il=new T(function(){return B(A3(_b0,B(_aS(E(_ih).a)),new T(function(){return B(_2l(_ik));}),_ij));});return new T2(0,new T(function(){return B(A2(_2l,_ik,_ii));}),_il);},_im=function(_in,_io){var _ip=E(_io),_iq=B(_ig(_in,_ip.a,_ip.b));return new T2(0,_iq.a,_iq.b);},_ir=function(_is,_it){var _iu=new T(function(){return B(_1O(new T(function(){return B(_1M(new T(function(){return E(E(E(_is).c).a);})));})));}),_iv=new T(function(){return B(A2(_eI,E(_is).a,new T(function(){return B(A2(_28,_iu,_eF));})));});return new T2(0,new T(function(){return B(A2(_hS,_iu,_it));}),_iv);},_iw=function(_ix,_iy){var _iz=B(_ir(_ix,E(_iy).a));return new T2(0,_iz.a,_iz.b);},_hR=function(_iA){return {_:0,a:function(_gi,_gh){return new F(function(){return _hF(_iA,_gi,_gh);});},b:function(_gi,_gh){return new F(function(){return _hM(_iA,_gi,_gh);});},c:function(_gi,_gh){return new F(function(){return _ho(_iA,_gi,_gh);});},d:function(_gh){return new F(function(){return _im(_iA,_gh);});},e:function(_gh){return new F(function(){return _i2(_iA,_gh);});},f:function(_gh){return new F(function(){return _iw(_iA,_gh);});},g:function(_gh){return new F(function(){return _ic(_iA,_gh);});}};},_iB=new T(function(){return B(unCStr("(>=) is not defined"));}),_iC=new T(function(){return B(err(_iB));}),_iD=new T(function(){return B(unCStr("(>) is not defined"));}),_iE=new T(function(){return B(err(_iD));}),_iF=new T(function(){return B(unCStr("(<=) is not defined"));}),_iG=new T(function(){return B(err(_iF));}),_iH=new T(function(){return B(unCStr("(<) is not defined"));}),_iI=new T(function(){return B(err(_iH));}),_iJ=new T(function(){return B(unCStr("compare is not defined"));}),_iK=new T(function(){return B(err(_iJ));}),_iL=new T2(0,E(_bv),E(_fm)),_iM=function(_iN,_iO,_iP,_iQ){var _iR=new T(function(){return B(A3(_1Q,_iN,new T(function(){return B(A3(_24,_iN,_iP,_iO));}),_iQ));});return new F(function(){return A3(_1S,_iN,_iO,_iR);});},_iS=function(_iT,_iU,_iV,_iW,_iX){var _iY=new T(function(){return E(E(_iT).c);}),_iZ=new T(function(){var _j0=E(_iT).a,_j1=new T(function(){var _j2=new T(function(){return B(_1M(new T(function(){return E(E(_iY).a);})));}),_j3=new T(function(){return B(_1O(_j2));}),_j4=new T(function(){var _j5=new T(function(){var _j6=new T(function(){return B(A2(_hS,_j3,new T(function(){return B(A3(_24,_j3,_iW,_iU));})));});return B(A3(_1Q,_j3,_j6,new T(function(){return B(A2(_2a,_j2,_iL));})));});return B(A3(_1S,_j3,_j5,new T(function(){return B(A2(_2a,_j2,_iL));})));});return B(A3(_b0,B(_aS(_j0)),function(_j7,_j8){return new F(function(){return _iM(_j3,_j7,_j8,_j4);});},_iV));});return B(A3(_aY,_j0,_j1,_iX));});return new T2(0,new T(function(){return B(A3(_2h,E(_iY).b,_iU,_iW));}),_iZ);},_j9=function(_ja,_jb,_jc,_jd){var _je=E(_jc),_jf=E(_jd),_jg=B(_iS(_jb,_je.a,_je.b,_jf.a,_jf.b));return new T2(0,_jg.a,_jg.b);},_jh=function(_ji,_jj,_jk,_jl,_jm){var _jn=new T(function(){return E(E(_ji).c);}),_jo=new T(function(){var _jp=E(_ji).a,_jq=new T(function(){var _jr=new T(function(){return B(_1M(new T(function(){return E(E(_jn).a);})));}),_js=new T(function(){return B(_1O(_jr));}),_jt=new T(function(){var _ju=new T(function(){var _jv=new T(function(){return B(A2(_hS,_js,new T(function(){return B(A3(_24,_js,_jl,_jj));})));});return B(A3(_1Q,_js,_jv,new T(function(){return B(A2(_2a,_jr,_iL));})));});return B(A3(_1S,_js,_ju,new T(function(){return B(A2(_2a,_jr,_iL));})));});return B(A3(_b0,B(_aS(_jp)),function(_jw,_jx){return new F(function(){return _iM(_js,_jx,_jw,_jt);});},_jk));});return B(A3(_aY,_jp,_jq,_jm));});return new T2(0,new T(function(){return B(A3(_2j,E(_jn).b,_jj,_jl));}),_jo);},_jy=function(_jz,_jA,_jB,_jC){var _jD=E(_jB),_jE=E(_jC),_jF=B(_jh(_jA,_jD.a,_jD.b,_jE.a,_jE.b));return new T2(0,_jF.a,_jF.b);},_jG=function(_jH,_jI){return {_:0,a:_jH,b:_iK,c:_iI,d:_iG,e:_iE,f:_iC,g:function(_gi,_gh){return new F(function(){return _j9(_jH,_jI,_gi,_gh);});},h:function(_gi,_gh){return new F(function(){return _jy(_jH,_jI,_gi,_gh);});}};},_jJ=function(_gi,_gh){return new T2(0,_gi,_gh);},_jK=function(_jL,_jM,_jN){var _jO=new T(function(){var _jP=E(_jL),_jQ=_jP.a,_jR=new T(function(){return B(A1(_jP.b,new T(function(){return B(_1O(B(_1M(E(_jP.c).a))));})));});return B(A3(_aY,_jQ,new T(function(){return B(A3(_b0,B(_aS(_jQ)),_jJ,_jN));}),_jR));});return E(B(A1(_jM,_jO)).b);},_jS=function(_jT){var _jU=new T(function(){return E(E(_jT).a);}),_jV=new T(function(){return E(E(_jT).b);}),_jW=new T(function(){var _jX=new T(function(){return B(_jG(new T(function(){return B(_aQ(new T3(0,_aE,_aI,new T2(0,_jU,_jV))));}),new T3(0,_aE,_aI,new T2(0,_jU,_jV))));}),_jY=new T(function(){var _jZ=new T(function(){return B(_h8(new T(function(){return B(_hR(new T3(0,_aE,_aI,new T2(0,_jU,_jV))));}),new T3(0,_aE,_aI,new T2(0,_jU,_jV))));});return B(_ge(_jZ,new T3(0,_aE,_aI,new T2(0,_jU,_jV))));});return B(_2p(new T2(0,_jY,_jX)));});return function(_k0){return new F(function(){return _jK(new T3(0,_aE,_aI,new T2(0,_jU,_jV)),_jW,_k0);});};},_k1=new T(function(){return B(_jS(_a2));}),_k2=function(_k3,_k4){var _k5=E(_k4);return (_k5._==0)?__Z:new T2(1,_k3,new T2(1,_k5.a,new T(function(){return B(_k2(_k3,_k5.b));})));},_k6=new T(function(){var _k7=B(A1(_k1,_1K));return new T2(1,_k7.a,new T(function(){return B(_k2(_2R,new T2(1,_k7.b,new T2(1,_k7.c,_T))));}));}),_k8=new T1(1,_k6),_k9=new T2(1,_k8,_2W),_ka=new T(function(){return B(unCStr("vec3("));}),_kb=new T1(0,_ka),_kc=new T2(1,_kb,_k9),_kd=new T(function(){return toJSStr(B(_a6(_1D,_11,_kc)));}),_ke=function(_kf,_kg){while(1){var _kh=E(_kf);if(!_kh._){return E(_kg);}else{var _ki=_kg+1|0;_kf=_kh.b;_kg=_ki;continue;}}},_kj=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_kk=new T(function(){return B(err(_kj));}),_kl=new T(function(){return B(unCStr("Negative exponent"));}),_km=new T(function(){return B(err(_kl));}),_kn=function(_ko,_kp,_kq){while(1){if(!(_kp%2)){var _kr=_ko*_ko,_ks=quot(_kp,2);_ko=_kr;_kp=_ks;continue;}else{var _kt=E(_kp);if(_kt==1){return _ko*_kq;}else{var _kr=_ko*_ko,_ku=_ko*_kq;_ko=_kr;_kp=quot(_kt-1|0,2);_kq=_ku;continue;}}}},_kv=function(_kw,_kx){while(1){if(!(_kx%2)){var _ky=_kw*_kw,_kz=quot(_kx,2);_kw=_ky;_kx=_kz;continue;}else{var _kA=E(_kx);if(_kA==1){return E(_kw);}else{return new F(function(){return _kn(_kw*_kw,quot(_kA-1|0,2),_kw);});}}}},_kB=function(_kC){var _kD=E(_kC);return new F(function(){return Math.log(_kD+(_kD+1)*Math.sqrt((_kD-1)/(_kD+1)));});},_kE=function(_kF){var _kG=E(_kF);return new F(function(){return Math.log(_kG+Math.sqrt(1+_kG*_kG));});},_kH=function(_kI){var _kJ=E(_kI);return 0.5*Math.log((1+_kJ)/(1-_kJ));},_kK=function(_kL,_kM){return Math.log(E(_kM))/Math.log(E(_kL));},_kN=3.141592653589793,_kO=function(_kP){var _kQ=E(_kP);return new F(function(){return _8J(_kQ.a,_kQ.b);});},_kR=function(_kS){return 1/E(_kS);},_kT=function(_kU){var _kV=E(_kU),_kW=E(_kV);return (_kW==0)?E(_8I):(_kW<=0)? -_kW:E(_kV);},_kX=function(_kY){var _kZ=E(_kY);if(!_kZ._){return _kZ.a;}else{return new F(function(){return I_toNumber(_kZ.a);});}},_l0=function(_l1){return new F(function(){return _kX(_l1);});},_l2=1,_l3=-1,_l4=function(_l5){var _l6=E(_l5);return (_l6<=0)?(_l6>=0)?E(_l6):E(_l3):E(_l2);},_l7=function(_l8,_l9){return E(_l8)-E(_l9);},_la=function(_lb){return  -E(_lb);},_lc=function(_ld,_le){return E(_ld)+E(_le);},_lf=function(_lg,_lh){return E(_lg)*E(_lh);},_li={_:0,a:_lc,b:_l7,c:_lf,d:_la,e:_kT,f:_l4,g:_l0},_lj=function(_lk,_ll){return E(_lk)/E(_ll);},_lm=new T4(0,_li,_lj,_kR,_kO),_ln=function(_lo){return new F(function(){return Math.acos(E(_lo));});},_lp=function(_lq){return new F(function(){return Math.asin(E(_lq));});},_lr=function(_ls){return new F(function(){return Math.atan(E(_ls));});},_lt=function(_lu){return new F(function(){return Math.cos(E(_lu));});},_lv=function(_lw){return new F(function(){return cosh(E(_lw));});},_lx=function(_ly){return new F(function(){return Math.exp(E(_ly));});},_lz=function(_lA){return new F(function(){return Math.log(E(_lA));});},_lB=function(_lC,_lD){return new F(function(){return Math.pow(E(_lC),E(_lD));});},_lE=function(_lF){return new F(function(){return Math.sin(E(_lF));});},_lG=function(_lH){return new F(function(){return sinh(E(_lH));});},_lI=function(_lJ){return new F(function(){return Math.sqrt(E(_lJ));});},_lK=function(_lL){return new F(function(){return Math.tan(E(_lL));});},_lM=function(_lN){return new F(function(){return tanh(E(_lN));});},_lO={_:0,a:_lm,b:_kN,c:_lx,d:_lz,e:_lI,f:_lB,g:_kK,h:_lE,i:_lt,j:_lK,k:_lp,l:_ln,m:_lr,n:_lG,o:_lv,p:_lM,q:_kE,r:_kB,s:_kH},_lP=function(_lQ,_lR){return (E(_lQ)!=E(_lR))?true:false;},_lS=function(_lT,_lU){return E(_lT)==E(_lU);},_lV=new T2(0,_lS,_lP),_lW=function(_lX,_lY){return E(_lX)<E(_lY);},_lZ=function(_m0,_m1){return E(_m0)<=E(_m1);},_m2=function(_m3,_m4){return E(_m3)>E(_m4);},_m5=function(_m6,_m7){return E(_m6)>=E(_m7);},_m8=function(_m9,_ma){var _mb=E(_m9),_mc=E(_ma);return (_mb>=_mc)?(_mb!=_mc)?2:1:0;},_md=function(_me,_mf){var _mg=E(_me),_mh=E(_mf);return (_mg>_mh)?E(_mg):E(_mh);},_mi=function(_mj,_mk){var _ml=E(_mj),_mm=E(_mk);return (_ml>_mm)?E(_mm):E(_ml);},_mn={_:0,a:_lV,b:_m8,c:_lW,d:_lZ,e:_m2,f:_m5,g:_md,h:_mi},_mo=new T2(0,_lO,_mn),_mp=function(_mq,_mr,_ms,_mt){var _mu=new T(function(){return E(E(_mq).a);}),_mv=new T(function(){return B(_1M(_mu));}),_mw=new T(function(){return B(A2(_2n,_mu,new T(function(){return B(_1U(_mu,_mr,_ms,_mt,_mr,_ms,_mt));})));});return new T3(0,new T(function(){return B(A3(_aW,_mv,_mr,_mw));}),new T(function(){return B(A3(_aW,_mv,_ms,_mw));}),new T(function(){return B(A3(_aW,_mv,_mt,_mw));}));},_mx=function(_my,_mz){var _mA=new T(function(){return E(E(_my).a);}),_mB=new T(function(){return E(E(_my).b);}),_mC=new T(function(){return B(A2(_jS,new T2(0,_mA,_mB),_mz));}),_mD=new T(function(){var _mE=E(_mC),_mF=B(_mp(new T2(0,_mA,_mB),_mE.a,_mE.b,_mE.c));return new T3(0,_mF.a,_mF.b,_mF.c);}),_mG=new T(function(){var _mH=E(_mz),_mI=E(_mD),_mJ=new T(function(){return B(_1M(_mA));}),_mK=new T(function(){return B(_1O(_mJ));}),_mL=new T(function(){return B(_1S(_mK));}),_mM=new T(function(){return B(_2l(_mK));}),_mN=new T(function(){return B(_1Q(_mK));}),_mO=new T(function(){var _mP=new T(function(){return B(A2(_2n,_mA,new T(function(){var _mQ=E(_mC),_mR=_mQ.a,_mS=_mQ.b,_mT=_mQ.c;return B(_1U(_mA,_mR,_mS,_mT,_mR,_mS,_mT));})));});return B(A3(_aW,_mJ,new T(function(){return B(A2(_2p,new T2(0,_mA,_mB),_mH));}),_mP));}),_mU=new T(function(){var _mV=new T(function(){return B(A1(_mM,new T(function(){return B(A2(_mN,_mI.c,_mO));})));});return B(A2(_mL,_mH.c,_mV));}),_mW=new T(function(){var _mX=new T(function(){return B(A1(_mM,new T(function(){return B(A2(_mN,_mI.b,_mO));})));});return B(A2(_mL,_mH.b,_mX));}),_mY=new T(function(){var _mZ=new T(function(){return B(A1(_mM,new T(function(){return B(A2(_mN,_mI.a,_mO));})));});return B(A2(_mL,_mH.a,_mZ));});return new T3(0,_mY,_mW,_mU);});return new T2(0,_mG,_mD);},_n0=function(_n1,_n2,_n3,_n4,_n5,_n6,_n7){var _n8=new T(function(){return E(E(_n1).a);}),_n9=new T(function(){return B(_1O(new T(function(){return B(_1M(_n8));})));}),_na=new T(function(){return B(_1S(_n9));}),_nb=new T(function(){return B(_2l(_n9));}),_nc=new T(function(){return B(_1Q(_n9));}),_nd=new T(function(){return B(_1U(_n8,_n5,_n6,_n7,_n2,_n3,_n4));}),_ne=new T(function(){var _nf=new T(function(){return B(A1(_nb,new T(function(){return B(A2(_nc,_n7,_nd));})));});return B(A2(_na,_n4,_nf));}),_ng=new T(function(){var _nh=new T(function(){return B(A1(_nb,new T(function(){return B(A2(_nc,_n6,_nd));})));});return B(A2(_na,_n3,_nh));}),_ni=new T(function(){var _nj=new T(function(){return B(A1(_nb,new T(function(){return B(A2(_nc,_n5,_nd));})));});return B(A2(_na,_n2,_nj));});return new T3(0,_ni,_ng,_ne);},_nk=function(_nl){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_nl));}))));});},_nm=new T(function(){return B(_nk("$dOrd_sd1k Ord a"));}),_nn=function(_no,_np,_nq,_nr,_ns,_nt,_nu){var _nv=new T(function(){return E(E(_no).a);}),_nw=B(_n0(new T2(0,_nv,_nm),_ns,_nt,_nu,_np,_nq,_nr));return new F(function(){return _mp(new T2(0,_nv,_nm),_nw.a,_nw.b,_nw.c);});},_nx=function(_ny){return E(E(_ny).a);},_nz=function(_nA){return E(E(_nA).a);},_nB=function(_nC,_nD,_nE,_nF){var _nG=new T(function(){var _nH=E(_nF),_nI=E(_nE),_nJ=B(_n0(new T2(0,_nC,_nD),_nH.a,_nH.b,_nH.c,_nI.a,_nI.b,_nI.c));return new T3(0,_nJ.a,_nJ.b,_nJ.c);}),_nK=new T(function(){return B(A2(_2n,_nC,new T(function(){var _nL=E(_nG),_nM=_nL.a,_nN=_nL.b,_nO=_nL.c;return B(_1U(_nC,_nM,_nN,_nO,_nM,_nN,_nO));})));});if(!B(A3(_nz,B(_nx(_nD)),_nK,new T(function(){return B(A2(_28,B(_1O(B(_1M(_nC)))),_1L));})))){var _nP=E(_nG),_nQ=B(_mp(new T2(0,_nC,_nD),_nP.a,_nP.b,_nP.c)),_nR=new T(function(){return B(_1Q(new T(function(){return B(_1O(new T(function(){return B(_1M(_nC));})));})));}),_nS=new T(function(){return B(A2(_2n,_nC,new T(function(){var _nT=E(_nF),_nU=_nT.a,_nV=_nT.b,_nW=_nT.c;return B(_1U(_nC,_nU,_nV,_nW,_nU,_nV,_nW));})));});return new T3(0,new T(function(){return B(A2(_nR,_nQ.a,_nS));}),new T(function(){return B(A2(_nR,_nQ.b,_nS));}),new T(function(){return B(A2(_nR,_nQ.c,_nS));}));}else{var _nX=new T(function(){return B(A2(_28,B(_1O(B(_1M(_nC)))),_1L));});return new T3(0,_nX,_nX,_nX);}},_nY=0,_nZ=new T(function(){var _o0=eval("angleCount"),_o1=Number(_o0);return jsTrunc(_o1);}),_o2=new T(function(){return E(_nZ);}),_o3=new T(function(){return B(unCStr(": empty list"));}),_o4=new T(function(){return B(unCStr("Prelude."));}),_o5=function(_o6){return new F(function(){return err(B(_14(_o4,new T(function(){return B(_14(_o6,_o3));},1))));});},_o7=new T(function(){return B(unCStr("head"));}),_o8=new T(function(){return B(_o5(_o7));}),_o9=function(_oa,_ob,_oc){var _od=E(_oa);if(!_od._){return __Z;}else{var _oe=E(_ob);if(!_oe._){return __Z;}else{var _of=_oe.a,_og=E(_oc);if(!_og._){return __Z;}else{var _oh=E(_og.a),_oi=_oh.a;return new F(function(){return _14(new T2(1,new T3(0,_od.a,_of,_oi),new T2(1,new T3(0,_of,_oi,_oh.b),_T)),new T(function(){return B(_o9(_od.b,_oe.b,_og.b));},1));});}}}},_oj=new T(function(){return B(unCStr("tail"));}),_ok=new T(function(){return B(_o5(_oj));}),_ol=function(_om,_on){var _oo=E(_om);if(!_oo._){return __Z;}else{var _op=E(_on);return (_op._==0)?__Z:new T2(1,new T2(0,_oo.a,_op.a),new T(function(){return B(_ol(_oo.b,_op.b));}));}},_oq=function(_or,_os){var _ot=E(_or);if(!_ot._){return __Z;}else{var _ou=E(_os);if(!_ou._){return __Z;}else{var _ov=E(_ot.a),_ow=_ov.b,_ox=E(_ou.a).b,_oy=new T(function(){var _oz=new T(function(){return B(_ol(_ox,new T(function(){var _oA=E(_ox);if(!_oA._){return E(_ok);}else{return E(_oA.b);}},1)));},1);return B(_o9(_ow,new T(function(){var _oB=E(_ow);if(!_oB._){return E(_ok);}else{return E(_oB.b);}},1),_oz));});return new F(function(){return _14(new T2(1,new T3(0,_ov.a,new T(function(){var _oC=E(_ow);if(!_oC._){return E(_o8);}else{return E(_oC.a);}}),new T(function(){var _oD=E(_ox);if(!_oD._){return E(_o8);}else{return E(_oD.a);}})),_oy),new T(function(){return B(_oq(_ot.b,_ou.b));},1));});}}},_oE=new T(function(){return E(_o2)-1;}),_oF=new T1(0,1),_oG=function(_oH,_oI){var _oJ=E(_oI),_oK=new T(function(){var _oL=B(_1O(_oH)),_oM=B(_oG(_oH,B(A3(_1S,_oL,_oJ,new T(function(){return B(A2(_28,_oL,_oF));})))));return new T2(1,_oM.a,_oM.b);});return new T2(0,_oJ,_oK);},_oN=function(_oO){return E(E(_oO).d);},_oP=new T1(0,2),_oQ=function(_oR,_oS){var _oT=E(_oS);if(!_oT._){return __Z;}else{var _oU=_oT.a;return (!B(A1(_oR,_oU)))?__Z:new T2(1,_oU,new T(function(){return B(_oQ(_oR,_oT.b));}));}},_oV=function(_oW,_oX,_oY,_oZ){var _p0=B(_oG(_oX,_oY)),_p1=new T(function(){var _p2=B(_1O(_oX)),_p3=new T(function(){return B(A3(_aW,_oX,new T(function(){return B(A2(_28,_p2,_oF));}),new T(function(){return B(A2(_28,_p2,_oP));})));});return B(A3(_1S,_p2,_oZ,_p3));});return new F(function(){return _oQ(function(_p4){return new F(function(){return A3(_oN,_oW,_p4,_p1);});},new T2(1,_p0.a,_p0.b));});},_p5=new T(function(){return B(_oV(_mn,_lm,_nY,_oE));}),_p6=function(_p7,_p8){var _p9=E(_p8);return (_p9._==0)?__Z:new T2(1,new T(function(){return B(A1(_p7,_p9.a));}),new T(function(){return B(_p6(_p7,_p9.b));}));},_pa=new T(function(){var _pb=eval("proceedCount"),_pc=Number(_pb);return jsTrunc(_pc);}),_pd=new T(function(){return E(_pa);}),_pe=1,_pf=new T(function(){return B(_oV(_mn,_lm,_pe,_pd));}),_pg=function(_ph,_pi,_pj,_pk,_pl){var _pm=new T(function(){var _pn=E(_pk),_po=_pn.a,_pp=_pn.b,_pq=_pn.c,_pr=E(_pl),_ps=_pr.a,_pt=_pr.b,_pu=_pr.c;return new T3(0,new T(function(){return E(_pp)*E(_pu)-E(_pt)*E(_pq);}),new T(function(){return E(_pq)*E(_ps)-E(_pu)*E(_po);}),new T(function(){return E(_po)*E(_pt)-E(_ps)*E(_pp);}));}),_pv=function(_pw){var _px=new T(function(){var _py=E(_pw)/E(_o2);return (_py+_py)*3.141592653589793;}),_pz=new T(function(){return B(A1(_ph,_px));}),_pA=new T(function(){return E(_px)+E(_pj);}),_pB=new T(function(){var _pC=new T(function(){return E(_pz)/E(_pd);}),_pD=function(_pE,_pF){var _pG=E(_pE);if(!_pG._){return new T2(0,_T,_pF);}else{var _pH=new T(function(){var _pI=new T(function(){var _pJ=E(_pF),_pK=E(_pJ.a),_pL=E(_pJ.b);return new T3(0,new T(function(){return E(_pK.a)+E(_pL.a)*E(_pC);}),new T(function(){return E(_pK.b)+E(_pL.b)*E(_pC);}),new T(function(){return E(_pK.c)+E(_pL.c)*E(_pC);}));}),_pM=B(_mx(_mo,_pI)),_pN=_pM.a;return new T2(0,new T3(0,_pN,new T2(0,new T(function(){return E(_pG.a)/E(_pd);}),_pz),_pA),new T2(0,_pN,new T(function(){var _pO=E(_pM.b),_pP=E(E(_pF).b),_pQ=B(_nn(_mo,_pO.a,_pO.b,_pO.c,_pP.a,_pP.b,_pP.c));return new T3(0,_pQ.a,_pQ.b,_pQ.c);})));}),_pR=new T(function(){var _pS=B(_pD(_pG.b,new T(function(){return E(E(_pH).b);})));return new T2(0,_pS.a,_pS.b);});return new T2(0,new T2(1,new T(function(){return E(E(_pH).a);}),new T(function(){return E(E(_pR).a);})),new T(function(){return E(E(_pR).b);}));}},_pT=function(_pU,_pV,_pW){var _pX=E(_pU);if(!_pX._){return new T2(0,_T,new T2(0,_pV,_pW));}else{var _pY=new T(function(){var _pZ=new T(function(){var _q0=E(_pV),_q1=E(_pW);return new T3(0,new T(function(){return E(_q0.a)+E(_q1.a)*E(_pC);}),new T(function(){return E(_q0.b)+E(_q1.b)*E(_pC);}),new T(function(){return E(_q0.c)+E(_q1.c)*E(_pC);}));}),_q2=B(_mx(_mo,_pZ)),_q3=_q2.a;return new T2(0,new T3(0,_q3,new T2(0,new T(function(){return E(_pX.a)/E(_pd);}),_pz),_pA),new T2(0,_q3,new T(function(){var _q4=E(_q2.b),_q5=E(_pW),_q6=B(_nn(_mo,_q4.a,_q4.b,_q4.c,_q5.a,_q5.b,_q5.c));return new T3(0,_q6.a,_q6.b,_q6.c);})));}),_q7=new T(function(){var _q8=B(_pD(_pX.b,new T(function(){return E(E(_pY).b);})));return new T2(0,_q8.a,_q8.b);});return new T2(0,new T2(1,new T(function(){return E(E(_pY).a);}),new T(function(){return E(E(_q7).a);})),new T(function(){return E(E(_q7).b);}));}},_q9=new T(function(){var _qa=E(_pk),_qb=E(_pm),_qc=new T(function(){return Math.cos(E(_pA));}),_qd=new T(function(){return Math.sin(E(_pA));});return new T3(0,new T(function(){return E(_qa.a)*E(_qc)+E(_qb.a)*E(_qd);}),new T(function(){return E(_qa.b)*E(_qc)+E(_qb.b)*E(_qd);}),new T(function(){return E(_qa.c)*E(_qc)+E(_qb.c)*E(_qd);}));});return E(B(_pT(_pf,_pi,_q9)).a);});return new T2(0,new T3(0,_pi,new T2(0,_nY,_pz),_pA),_pB);},_qe=B(_p6(_pv,_p5)),_qf=new T(function(){var _qg=B(_14(_qe,new T2(1,new T(function(){var _qh=E(_qe);if(!_qh._){return E(_o8);}else{return E(_qh.a);}}),_T)));if(!_qg._){return E(_ok);}else{return E(_qg.b);}},1);return new F(function(){return _oq(_qe,_qf);});},_qi=function(_qj,_qk,_ql,_qm,_qn,_qo){var _qp=new T(function(){var _qq=B(_mx(_mo,new T(function(){return E(E(_qm).a);})));return new T2(0,_qq.a,_qq.b);}),_qr=new T(function(){return new T2(0,new T(function(){return E(E(_qp).a);}),E(_qm).b);}),_qs=new T(function(){return E(E(_qp).b);}),_qt=new T(function(){var _qu=E(_qs),_qv=E(_qo),_qw=B(_nn(_mo,_qu.a,_qu.b,_qu.c,_qv.a,_qv.b,_qv.c));return new T3(0,_qw.a,_qw.b,_qw.c);}),_qx=new T(function(){var _qy=E(_qn);return new T2(0,new T(function(){var _qz=B(_nB(_lO,_mn,_qs,_qy.a));return new T3(0,_qz.a,_qz.b,_qz.c);}),_qy.b);});return {_:0,a:_qj,b:_qk,c:_ql,d:_qr,e:_qx,f:_qt,g:_qs,h:new T(function(){var _qA=E(_qr);return B(_pg(_qj,_qA.a,_qA.b,_qt,_qs));})};},_qB=-1,_qC=0.5,_qD=new T3(0,_nY,_qC,_qB),_qE=new T(function(){return 6.283185307179586/E(_o2);}),_qF=function(_qG,_qH,_qI,_qJ,_qK){var _qL=function(_qM){var _qN=E(_qE),_qO=2+_qM|0,_qP=_qO-1|0,_qQ=(2+_qM)*(1+_qM),_qR=E(_p5);if(!_qR._){return _qN*0;}else{var _qS=_qR.a,_qT=_qR.b,_qU=B(A1(_qG,new T(function(){return 6.283185307179586*E(_qS)/E(_o2);}))),_qV=B(A1(_qG,new T(function(){return 6.283185307179586*(E(_qS)+1)/E(_o2);})));if(_qU!=_qV){if(_qO>=0){var _qW=E(_qO);if(!_qW){var _qX=function(_qY,_qZ){while(1){var _r0=B((function(_r1,_r2){var _r3=E(_r1);if(!_r3._){return E(_r2);}else{var _r4=_r3.a,_r5=_r3.b,_r6=B(A1(_qG,new T(function(){return 6.283185307179586*E(_r4)/E(_o2);}))),_r7=B(A1(_qG,new T(function(){return 6.283185307179586*(E(_r4)+1)/E(_o2);})));if(_r6!=_r7){var _r8=_r2+0/(_r6-_r7)/_qQ;_qY=_r5;_qZ=_r8;return __continue;}else{if(_qP>=0){var _r9=E(_qP);if(!_r9){var _r8=_r2+_qO/_qQ;_qY=_r5;_qZ=_r8;return __continue;}else{var _r8=_r2+_qO*B(_kv(_r6,_r9))/_qQ;_qY=_r5;_qZ=_r8;return __continue;}}else{return E(_km);}}}})(_qY,_qZ));if(_r0!=__continue){return _r0;}}};return _qN*B(_qX(_qT,0/(_qU-_qV)/_qQ));}else{var _ra=function(_rb,_rc){while(1){var _rd=B((function(_re,_rf){var _rg=E(_re);if(!_rg._){return E(_rf);}else{var _rh=_rg.a,_ri=_rg.b,_rj=B(A1(_qG,new T(function(){return 6.283185307179586*E(_rh)/E(_o2);}))),_rk=B(A1(_qG,new T(function(){return 6.283185307179586*(E(_rh)+1)/E(_o2);})));if(_rj!=_rk){if(_qW>=0){var _rl=_rf+(B(_kv(_rj,_qW))-B(_kv(_rk,_qW)))/(_rj-_rk)/_qQ;_rb=_ri;_rc=_rl;return __continue;}else{return E(_km);}}else{if(_qP>=0){var _rm=E(_qP);if(!_rm){var _rl=_rf+_qO/_qQ;_rb=_ri;_rc=_rl;return __continue;}else{var _rl=_rf+_qO*B(_kv(_rj,_rm))/_qQ;_rb=_ri;_rc=_rl;return __continue;}}else{return E(_km);}}}})(_rb,_rc));if(_rd!=__continue){return _rd;}}};return _qN*B(_ra(_qT,(B(_kv(_qU,_qW))-B(_kv(_qV,_qW)))/(_qU-_qV)/_qQ));}}else{return E(_km);}}else{if(_qP>=0){var _rn=E(_qP);if(!_rn){var _ro=function(_rp,_rq){while(1){var _rr=B((function(_rs,_rt){var _ru=E(_rs);if(!_ru._){return E(_rt);}else{var _rv=_ru.a,_rw=_ru.b,_rx=B(A1(_qG,new T(function(){return 6.283185307179586*E(_rv)/E(_o2);}))),_ry=B(A1(_qG,new T(function(){return 6.283185307179586*(E(_rv)+1)/E(_o2);})));if(_rx!=_ry){if(_qO>=0){var _rz=E(_qO);if(!_rz){var _rA=_rt+0/(_rx-_ry)/_qQ;_rp=_rw;_rq=_rA;return __continue;}else{var _rA=_rt+(B(_kv(_rx,_rz))-B(_kv(_ry,_rz)))/(_rx-_ry)/_qQ;_rp=_rw;_rq=_rA;return __continue;}}else{return E(_km);}}else{var _rA=_rt+_qO/_qQ;_rp=_rw;_rq=_rA;return __continue;}}})(_rp,_rq));if(_rr!=__continue){return _rr;}}};return _qN*B(_ro(_qT,_qO/_qQ));}else{var _rB=function(_rC,_rD){while(1){var _rE=B((function(_rF,_rG){var _rH=E(_rF);if(!_rH._){return E(_rG);}else{var _rI=_rH.a,_rJ=_rH.b,_rK=B(A1(_qG,new T(function(){return 6.283185307179586*E(_rI)/E(_o2);}))),_rL=B(A1(_qG,new T(function(){return 6.283185307179586*(E(_rI)+1)/E(_o2);})));if(_rK!=_rL){if(_qO>=0){var _rM=E(_qO);if(!_rM){var _rN=_rG+0/(_rK-_rL)/_qQ;_rC=_rJ;_rD=_rN;return __continue;}else{var _rN=_rG+(B(_kv(_rK,_rM))-B(_kv(_rL,_rM)))/(_rK-_rL)/_qQ;_rC=_rJ;_rD=_rN;return __continue;}}else{return E(_km);}}else{if(_rn>=0){var _rN=_rG+_qO*B(_kv(_rK,_rn))/_qQ;_rC=_rJ;_rD=_rN;return __continue;}else{return E(_km);}}}})(_rC,_rD));if(_rE!=__continue){return _rE;}}};return _qN*B(_rB(_qT,_qO*B(_kv(_qU,_rn))/_qQ));}}else{return E(_km);}}}},_rO=new T(function(){return 1/(B(_qL(1))*E(_qH));});return new F(function(){return _qi(_qG,_qD,new T2(0,new T3(0,_rO,_rO,_rO),new T(function(){return 1/(B(_qL(3))*E(_qH));})),_qI,_qJ,_qK);});},_rP=1.2,_rQ=-0.2,_rR=1,_rS=0,_rT=new T3(0,_rQ,_rS,_rR),_rU=new T2(0,_rT,_rS),_rV=0.5,_rW=-0.8,_rX=new T3(0,_rW,_rV,_rS),_rY=new T2(0,_rX,_rS),_rZ=0.2,_s0=function(_s1){return E(_rZ);},_s2=new T3(0,_rS,_rS,_rR),_s3=new T(function(){var _s4=B(_qF(_s0,_rP,_rY,_rU,_s2));return {_:0,a:_s4.a,b:_s4.b,c:_s4.c,d:_s4.d,e:_s4.e,f:_s4.f,g:_s4.g,h:_s4.h};}),_s5=0,_s6=1.3,_s7=new T3(0,_s6,_rS,_rS),_s8=new T2(0,_s7,_rS),_s9=function(_sa){var _sb=I_decodeDouble(_sa);return new T2(0,new T1(1,_sb.b),_sb.a);},_sc=function(_sd){return new T1(0,_sd);},_se=function(_sf){var _sg=hs_intToInt64(2147483647),_sh=hs_leInt64(_sf,_sg);if(!_sh){return new T1(1,I_fromInt64(_sf));}else{var _si=hs_intToInt64(-2147483648),_sj=hs_geInt64(_sf,_si);if(!_sj){return new T1(1,I_fromInt64(_sf));}else{var _sk=hs_int64ToInt(_sf);return new F(function(){return _sc(_sk);});}}},_sl=new T(function(){var _sm=newByteArr(256),_sn=_sm,_=_sn["v"]["i8"][0]=8,_so=function(_sp,_sq,_sr,_){while(1){if(_sr>=256){if(_sp>=256){return E(_);}else{var _ss=imul(2,_sp)|0,_st=_sq+1|0,_su=_sp;_sp=_ss;_sq=_st;_sr=_su;continue;}}else{var _=_sn["v"]["i8"][_sr]=_sq,_su=_sr+_sp|0;_sr=_su;continue;}}},_=B(_so(2,0,1,_));return _sn;}),_sv=function(_sw,_sx){var _sy=hs_int64ToInt(_sw),_sz=E(_sl),_sA=_sz["v"]["i8"][(255&_sy>>>0)>>>0&4294967295];if(_sx>_sA){if(_sA>=8){var _sB=hs_uncheckedIShiftRA64(_sw,8),_sC=function(_sD,_sE){while(1){var _sF=B((function(_sG,_sH){var _sI=hs_int64ToInt(_sG),_sJ=_sz["v"]["i8"][(255&_sI>>>0)>>>0&4294967295];if(_sH>_sJ){if(_sJ>=8){var _sK=hs_uncheckedIShiftRA64(_sG,8),_sL=_sH-8|0;_sD=_sK;_sE=_sL;return __continue;}else{return new T2(0,new T(function(){var _sM=hs_uncheckedIShiftRA64(_sG,_sJ);return B(_se(_sM));}),_sH-_sJ|0);}}else{return new T2(0,new T(function(){var _sN=hs_uncheckedIShiftRA64(_sG,_sH);return B(_se(_sN));}),0);}})(_sD,_sE));if(_sF!=__continue){return _sF;}}};return new F(function(){return _sC(_sB,_sx-8|0);});}else{return new T2(0,new T(function(){var _sO=hs_uncheckedIShiftRA64(_sw,_sA);return B(_se(_sO));}),_sx-_sA|0);}}else{return new T2(0,new T(function(){var _sP=hs_uncheckedIShiftRA64(_sw,_sx);return B(_se(_sP));}),0);}},_sQ=function(_sR){var _sS=hs_intToInt64(_sR);return E(_sS);},_sT=function(_sU){var _sV=E(_sU);if(!_sV._){return new F(function(){return _sQ(_sV.a);});}else{return new F(function(){return I_toInt64(_sV.a);});}},_sW=function(_sX){return I_toInt(_sX)>>>0;},_sY=function(_sZ){var _t0=E(_sZ);if(!_t0._){return _t0.a>>>0;}else{return new F(function(){return _sW(_t0.a);});}},_t1=function(_t2){var _t3=B(_s9(_t2)),_t4=_t3.a,_t5=_t3.b;if(_t5<0){var _t6=function(_t7){if(!_t7){return new T2(0,E(_t4),B(_5U(_4c, -_t5)));}else{var _t8=B(_sv(B(_sT(_t4)), -_t5));return new T2(0,E(_t8.a),B(_5U(_4c,_t8.b)));}};if(!((B(_sY(_t4))&1)>>>0)){return new F(function(){return _t6(1);});}else{return new F(function(){return _t6(0);});}}else{return new T2(0,B(_5U(_t4,_t5)),_4c);}},_t9=function(_ta){var _tb=B(_t1(E(_ta)));return new T2(0,E(_tb.a),E(_tb.b));},_tc=new T3(0,_li,_mn,_t9),_td=function(_te){return E(E(_te).a);},_tf=function(_tg){return E(E(_tg).a);},_th=function(_ti,_tj){if(_ti<=_tj){var _tk=function(_tl){return new T2(1,_tl,new T(function(){if(_tl!=_tj){return B(_tk(_tl+1|0));}else{return __Z;}}));};return new F(function(){return _tk(_ti);});}else{return __Z;}},_tm=function(_tn){return new F(function(){return _th(E(_tn),2147483647);});},_to=function(_tp,_tq,_tr){if(_tr<=_tq){var _ts=new T(function(){var _tt=_tq-_tp|0,_tu=function(_tv){return (_tv>=(_tr-_tt|0))?new T2(1,_tv,new T(function(){return B(_tu(_tv+_tt|0));})):new T2(1,_tv,_T);};return B(_tu(_tq));});return new T2(1,_tp,_ts);}else{return (_tr<=_tp)?new T2(1,_tp,_T):__Z;}},_tw=function(_tx,_ty,_tz){if(_tz>=_ty){var _tA=new T(function(){var _tB=_ty-_tx|0,_tC=function(_tD){return (_tD<=(_tz-_tB|0))?new T2(1,_tD,new T(function(){return B(_tC(_tD+_tB|0));})):new T2(1,_tD,_T);};return B(_tC(_ty));});return new T2(1,_tx,_tA);}else{return (_tz>=_tx)?new T2(1,_tx,_T):__Z;}},_tE=function(_tF,_tG){if(_tG<_tF){return new F(function(){return _to(_tF,_tG,-2147483648);});}else{return new F(function(){return _tw(_tF,_tG,2147483647);});}},_tH=function(_tI,_tJ){return new F(function(){return _tE(E(_tI),E(_tJ));});},_tK=function(_tL,_tM,_tN){if(_tM<_tL){return new F(function(){return _to(_tL,_tM,_tN);});}else{return new F(function(){return _tw(_tL,_tM,_tN);});}},_tO=function(_tP,_tQ,_tR){return new F(function(){return _tK(E(_tP),E(_tQ),E(_tR));});},_tS=function(_tT,_tU){return new F(function(){return _th(E(_tT),E(_tU));});},_tV=function(_tW){return E(_tW);},_tX=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_tY=new T(function(){return B(err(_tX));}),_tZ=function(_u0){var _u1=E(_u0);return (_u1==(-2147483648))?E(_tY):_u1-1|0;},_u2=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_u3=new T(function(){return B(err(_u2));}),_u4=function(_u5){var _u6=E(_u5);return (_u6==2147483647)?E(_u3):_u6+1|0;},_u7={_:0,a:_u4,b:_tZ,c:_tV,d:_tV,e:_tm,f:_tH,g:_tS,h:_tO},_u8=function(_u9,_ua){if(_u9<=0){if(_u9>=0){return new F(function(){return quot(_u9,_ua);});}else{if(_ua<=0){return new F(function(){return quot(_u9,_ua);});}else{return quot(_u9+1|0,_ua)-1|0;}}}else{if(_ua>=0){if(_u9>=0){return new F(function(){return quot(_u9,_ua);});}else{if(_ua<=0){return new F(function(){return quot(_u9,_ua);});}else{return quot(_u9+1|0,_ua)-1|0;}}}else{return quot(_u9-1|0,_ua)-1|0;}}},_ub=0,_uc=new T(function(){return B(_5h(_ub));}),_ud=new T(function(){return die(_uc);}),_ue=function(_uf,_ug){var _uh=E(_ug);switch(_uh){case -1:var _ui=E(_uf);if(_ui==(-2147483648)){return E(_ud);}else{return new F(function(){return _u8(_ui,-1);});}break;case 0:return E(_5l);default:return new F(function(){return _u8(_uf,_uh);});}},_uj=function(_uk,_ul){return new F(function(){return _ue(E(_uk),E(_ul));});},_um=0,_un=new T2(0,_ud,_um),_uo=function(_up,_uq){var _ur=E(_up),_us=E(_uq);switch(_us){case -1:var _ut=E(_ur);if(_ut==(-2147483648)){return E(_un);}else{if(_ut<=0){if(_ut>=0){var _uu=quotRemI(_ut,-1);return new T2(0,_uu.a,_uu.b);}else{var _uv=quotRemI(_ut,-1);return new T2(0,_uv.a,_uv.b);}}else{var _uw=quotRemI(_ut-1|0,-1);return new T2(0,_uw.a-1|0,(_uw.b+(-1)|0)+1|0);}}break;case 0:return E(_5l);default:if(_ur<=0){if(_ur>=0){var _ux=quotRemI(_ur,_us);return new T2(0,_ux.a,_ux.b);}else{if(_us<=0){var _uy=quotRemI(_ur,_us);return new T2(0,_uy.a,_uy.b);}else{var _uz=quotRemI(_ur+1|0,_us);return new T2(0,_uz.a-1|0,(_uz.b+_us|0)-1|0);}}}else{if(_us>=0){if(_ur>=0){var _uA=quotRemI(_ur,_us);return new T2(0,_uA.a,_uA.b);}else{if(_us<=0){var _uB=quotRemI(_ur,_us);return new T2(0,_uB.a,_uB.b);}else{var _uC=quotRemI(_ur+1|0,_us);return new T2(0,_uC.a-1|0,(_uC.b+_us|0)-1|0);}}}else{var _uD=quotRemI(_ur-1|0,_us);return new T2(0,_uD.a-1|0,(_uD.b+_us|0)+1|0);}}}},_uE=function(_uF,_uG){var _uH=_uF%_uG;if(_uF<=0){if(_uF>=0){return E(_uH);}else{if(_uG<=0){return E(_uH);}else{var _uI=E(_uH);return (_uI==0)?0:_uI+_uG|0;}}}else{if(_uG>=0){if(_uF>=0){return E(_uH);}else{if(_uG<=0){return E(_uH);}else{var _uJ=E(_uH);return (_uJ==0)?0:_uJ+_uG|0;}}}else{var _uK=E(_uH);return (_uK==0)?0:_uK+_uG|0;}}},_uL=function(_uM,_uN){var _uO=E(_uN);switch(_uO){case -1:return E(_um);case 0:return E(_5l);default:return new F(function(){return _uE(E(_uM),_uO);});}},_uP=function(_uQ,_uR){var _uS=E(_uQ),_uT=E(_uR);switch(_uT){case -1:var _uU=E(_uS);if(_uU==(-2147483648)){return E(_ud);}else{return new F(function(){return quot(_uU,-1);});}break;case 0:return E(_5l);default:return new F(function(){return quot(_uS,_uT);});}},_uV=function(_uW,_uX){var _uY=E(_uW),_uZ=E(_uX);switch(_uZ){case -1:var _v0=E(_uY);if(_v0==(-2147483648)){return E(_un);}else{var _v1=quotRemI(_v0,-1);return new T2(0,_v1.a,_v1.b);}break;case 0:return E(_5l);default:var _v2=quotRemI(_uY,_uZ);return new T2(0,_v2.a,_v2.b);}},_v3=function(_v4,_v5){var _v6=E(_v5);switch(_v6){case -1:return E(_um);case 0:return E(_5l);default:return E(_v4)%_v6;}},_v7=function(_v8){return new F(function(){return _sc(E(_v8));});},_v9=function(_va){return new T2(0,E(B(_sc(E(_va)))),E(_oF));},_vb=function(_vc,_vd){return imul(E(_vc),E(_vd))|0;},_ve=function(_vf,_vg){return E(_vf)+E(_vg)|0;},_vh=function(_vi,_vj){return E(_vi)-E(_vj)|0;},_vk=function(_vl){var _vm=E(_vl);return (_vm<0)? -_vm:E(_vm);},_vn=function(_vo){return new F(function(){return _5y(_vo);});},_vp=function(_vq){return  -E(_vq);},_vr=-1,_vs=0,_vt=1,_vu=function(_vv){var _vw=E(_vv);return (_vw>=0)?(E(_vw)==0)?E(_vs):E(_vt):E(_vr);},_vx={_:0,a:_ve,b:_vh,c:_vb,d:_vp,e:_vk,f:_vu,g:_vn},_vy=function(_vz,_vA){return E(_vz)==E(_vA);},_vB=function(_vC,_vD){return E(_vC)!=E(_vD);},_vE=new T2(0,_vy,_vB),_vF=function(_vG,_vH){var _vI=E(_vG),_vJ=E(_vH);return (_vI>_vJ)?E(_vI):E(_vJ);},_vK=function(_vL,_vM){var _vN=E(_vL),_vO=E(_vM);return (_vN>_vO)?E(_vO):E(_vN);},_vP=function(_vQ,_vR){return (_vQ>=_vR)?(_vQ!=_vR)?2:1:0;},_vS=function(_vT,_vU){return new F(function(){return _vP(E(_vT),E(_vU));});},_vV=function(_vW,_vX){return E(_vW)>=E(_vX);},_vY=function(_vZ,_w0){return E(_vZ)>E(_w0);},_w1=function(_w2,_w3){return E(_w2)<=E(_w3);},_w4=function(_w5,_w6){return E(_w5)<E(_w6);},_w7={_:0,a:_vE,b:_vS,c:_w4,d:_w1,e:_vY,f:_vV,g:_vF,h:_vK},_w8=new T3(0,_vx,_w7,_v9),_w9={_:0,a:_w8,b:_u7,c:_uP,d:_v3,e:_uj,f:_uL,g:_uV,h:_uo,i:_v7},_wa=new T1(0,2),_wb=function(_wc,_wd){while(1){var _we=E(_wc);if(!_we._){var _wf=_we.a,_wg=E(_wd);if(!_wg._){var _wh=_wg.a;if(!(imul(_wf,_wh)|0)){return new T1(0,imul(_wf,_wh)|0);}else{_wc=new T1(1,I_fromInt(_wf));_wd=new T1(1,I_fromInt(_wh));continue;}}else{_wc=new T1(1,I_fromInt(_wf));_wd=_wg;continue;}}else{var _wi=E(_wd);if(!_wi._){_wc=_we;_wd=new T1(1,I_fromInt(_wi.a));continue;}else{return new T1(1,I_mul(_we.a,_wi.a));}}}},_wj=function(_wk,_wl,_wm){while(1){if(!(_wl%2)){var _wn=B(_wb(_wk,_wk)),_wo=quot(_wl,2);_wk=_wn;_wl=_wo;continue;}else{var _wp=E(_wl);if(_wp==1){return new F(function(){return _wb(_wk,_wm);});}else{var _wn=B(_wb(_wk,_wk)),_wq=B(_wb(_wk,_wm));_wk=_wn;_wl=quot(_wp-1|0,2);_wm=_wq;continue;}}}},_wr=function(_ws,_wt){while(1){if(!(_wt%2)){var _wu=B(_wb(_ws,_ws)),_wv=quot(_wt,2);_ws=_wu;_wt=_wv;continue;}else{var _ww=E(_wt);if(_ww==1){return E(_ws);}else{return new F(function(){return _wj(B(_wb(_ws,_ws)),quot(_ww-1|0,2),_ws);});}}}},_wx=function(_wy){return E(E(_wy).b);},_wz=function(_wA){return E(E(_wA).c);},_wB=new T1(0,0),_wC=function(_wD){return E(E(_wD).d);},_wE=function(_wF,_wG){var _wH=B(_td(_wF)),_wI=new T(function(){return B(_tf(_wH));}),_wJ=new T(function(){return B(A3(_wC,_wF,_wG,new T(function(){return B(A2(_28,_wI,_oP));})));});return new F(function(){return A3(_nz,B(_nx(B(_wx(_wH)))),_wJ,new T(function(){return B(A2(_28,_wI,_wB));}));});},_wK=new T(function(){return B(unCStr("Negative exponent"));}),_wL=new T(function(){return B(err(_wK));}),_wM=function(_wN){return E(E(_wN).c);},_wO=function(_wP,_wQ,_wR,_wS){var _wT=B(_td(_wQ)),_wU=new T(function(){return B(_tf(_wT));}),_wV=B(_wx(_wT));if(!B(A3(_wz,_wV,_wS,new T(function(){return B(A2(_28,_wU,_wB));})))){if(!B(A3(_nz,B(_nx(_wV)),_wS,new T(function(){return B(A2(_28,_wU,_wB));})))){var _wW=new T(function(){return B(A2(_28,_wU,_oP));}),_wX=new T(function(){return B(A2(_28,_wU,_oF));}),_wY=B(_nx(_wV)),_wZ=function(_x0,_x1,_x2){while(1){var _x3=B((function(_x4,_x5,_x6){if(!B(_wE(_wQ,_x5))){if(!B(A3(_nz,_wY,_x5,_wX))){var _x7=new T(function(){return B(A3(_wM,_wQ,new T(function(){return B(A3(_24,_wU,_x5,_wX));}),_wW));});_x0=new T(function(){return B(A3(_1Q,_wP,_x4,_x4));});_x1=_x7;_x2=new T(function(){return B(A3(_1Q,_wP,_x4,_x6));});return __continue;}else{return new F(function(){return A3(_1Q,_wP,_x4,_x6);});}}else{var _x8=_x6;_x0=new T(function(){return B(A3(_1Q,_wP,_x4,_x4));});_x1=new T(function(){return B(A3(_wM,_wQ,_x5,_wW));});_x2=_x8;return __continue;}})(_x0,_x1,_x2));if(_x3!=__continue){return _x3;}}},_x9=function(_xa,_xb){while(1){var _xc=B((function(_xd,_xe){if(!B(_wE(_wQ,_xe))){if(!B(A3(_nz,_wY,_xe,_wX))){var _xf=new T(function(){return B(A3(_wM,_wQ,new T(function(){return B(A3(_24,_wU,_xe,_wX));}),_wW));});return new F(function(){return _wZ(new T(function(){return B(A3(_1Q,_wP,_xd,_xd));}),_xf,_xd);});}else{return E(_xd);}}else{_xa=new T(function(){return B(A3(_1Q,_wP,_xd,_xd));});_xb=new T(function(){return B(A3(_wM,_wQ,_xe,_wW));});return __continue;}})(_xa,_xb));if(_xc!=__continue){return _xc;}}};return new F(function(){return _x9(_wR,_wS);});}else{return new F(function(){return A2(_28,_wP,_oF);});}}else{return E(_wL);}},_xg=new T(function(){return B(err(_wK));}),_xh=function(_xi,_xj){var _xk=B(_s9(_xj)),_xl=_xk.a,_xm=_xk.b,_xn=new T(function(){return B(_tf(new T(function(){return B(_td(_xi));})));});if(_xm<0){var _xo= -_xm;if(_xo>=0){var _xp=E(_xo);if(!_xp){var _xq=E(_oF);}else{var _xq=B(_wr(_wa,_xp));}if(!B(_5q(_xq,_5T))){var _xr=B(_5K(_xl,_xq));return new T2(0,new T(function(){return B(A2(_28,_xn,_xr.a));}),new T(function(){return B(_5m(_xr.b,_xm));}));}else{return E(_5l);}}else{return E(_xg);}}else{var _xs=new T(function(){var _xt=new T(function(){return B(_wO(_xn,_w9,new T(function(){return B(A2(_28,_xn,_wa));}),_xm));});return B(A3(_1Q,_xn,new T(function(){return B(A2(_28,_xn,_xl));}),_xt));});return new T2(0,_xs,_8I);}},_xu=function(_xv,_xw){var _xx=B(_xh(_xv,E(_xw))),_xy=_xx.a;if(E(_xx.b)<=0){return E(_xy);}else{var _xz=B(_tf(B(_td(_xv))));return new F(function(){return A3(_1S,_xz,_xy,new T(function(){return B(A2(_28,_xz,_4c));}));});}},_xA=function(_xB,_xC){var _xD=B(_xh(_xB,E(_xC))),_xE=_xD.a;if(E(_xD.b)>=0){return E(_xE);}else{var _xF=B(_tf(B(_td(_xB))));return new F(function(){return A3(_24,_xF,_xE,new T(function(){return B(A2(_28,_xF,_4c));}));});}},_xG=function(_xH,_xI){var _xJ=B(_xh(_xH,E(_xI)));return new T2(0,_xJ.a,_xJ.b);},_xK=function(_xL,_xM){var _xN=B(_xh(_xL,_xM)),_xO=_xN.a,_xP=E(_xN.b),_xQ=new T(function(){var _xR=B(_tf(B(_td(_xL))));if(_xP>=0){return B(A3(_1S,_xR,_xO,new T(function(){return B(A2(_28,_xR,_4c));})));}else{return B(A3(_24,_xR,_xO,new T(function(){return B(A2(_28,_xR,_4c));})));}}),_xS=function(_xT){var _xU=_xT-0.5;return (_xU>=0)?(E(_xU)==0)?(!B(_wE(_xL,_xO)))?E(_xQ):E(_xO):E(_xQ):E(_xO);},_xV=E(_xP);if(!_xV){return new F(function(){return _xS(0);});}else{if(_xV<=0){var _xW= -_xV-0.5;return (_xW>=0)?(E(_xW)==0)?(!B(_wE(_xL,_xO)))?E(_xQ):E(_xO):E(_xQ):E(_xO);}else{return new F(function(){return _xS(_xV);});}}},_xX=function(_xY,_xZ){return new F(function(){return _xK(_xY,E(_xZ));});},_y0=function(_y1,_y2){return E(B(_xh(_y1,E(_y2))).a);},_y3={_:0,a:_tc,b:_lm,c:_xG,d:_y0,e:_xX,f:_xu,g:_xA},_y4=new T1(0,1),_y5=function(_y6,_y7){var _y8=E(_y6);return new T2(0,_y8,new T(function(){var _y9=B(_y5(B(_5B(_y8,_y7)),_y7));return new T2(1,_y9.a,_y9.b);}));},_ya=function(_yb){var _yc=B(_y5(_yb,_y4));return new T2(1,_yc.a,_yc.b);},_yd=function(_ye,_yf){var _yg=B(_y5(_ye,new T(function(){return B(_7W(_yf,_ye));})));return new T2(1,_yg.a,_yg.b);},_yh=new T1(0,0),_yi=function(_yj,_yk){var _yl=E(_yj);if(!_yl._){var _ym=_yl.a,_yn=E(_yk);return (_yn._==0)?_ym>=_yn.a:I_compareInt(_yn.a,_ym)<=0;}else{var _yo=_yl.a,_yp=E(_yk);return (_yp._==0)?I_compareInt(_yo,_yp.a)>=0:I_compare(_yo,_yp.a)>=0;}},_yq=function(_yr,_ys,_yt){if(!B(_yi(_ys,_yh))){var _yu=function(_yv){return (!B(_6d(_yv,_yt)))?new T2(1,_yv,new T(function(){return B(_yu(B(_5B(_yv,_ys))));})):__Z;};return new F(function(){return _yu(_yr);});}else{var _yw=function(_yx){return (!B(_64(_yx,_yt)))?new T2(1,_yx,new T(function(){return B(_yw(B(_5B(_yx,_ys))));})):__Z;};return new F(function(){return _yw(_yr);});}},_yy=function(_yz,_yA,_yB){return new F(function(){return _yq(_yz,B(_7W(_yA,_yz)),_yB);});},_yC=function(_yD,_yE){return new F(function(){return _yq(_yD,_y4,_yE);});},_yF=function(_yG){return new F(function(){return _5y(_yG);});},_yH=function(_yI){return new F(function(){return _7W(_yI,_y4);});},_yJ=function(_yK){return new F(function(){return _5B(_yK,_y4);});},_yL=function(_yM){return new F(function(){return _sc(E(_yM));});},_yN={_:0,a:_yJ,b:_yH,c:_yL,d:_yF,e:_ya,f:_yd,g:_yC,h:_yy},_yO=function(_yP,_yQ){while(1){var _yR=E(_yP);if(!_yR._){var _yS=E(_yR.a);if(_yS==(-2147483648)){_yP=new T1(1,I_fromInt(-2147483648));continue;}else{var _yT=E(_yQ);if(!_yT._){return new T1(0,B(_u8(_yS,_yT.a)));}else{_yP=new T1(1,I_fromInt(_yS));_yQ=_yT;continue;}}}else{var _yU=_yR.a,_yV=E(_yQ);return (_yV._==0)?new T1(1,I_div(_yU,I_fromInt(_yV.a))):new T1(1,I_div(_yU,_yV.a));}}},_yW=function(_yX,_yY){if(!B(_5q(_yY,_wB))){return new F(function(){return _yO(_yX,_yY);});}else{return E(_5l);}},_yZ=function(_z0,_z1){while(1){var _z2=E(_z0);if(!_z2._){var _z3=E(_z2.a);if(_z3==(-2147483648)){_z0=new T1(1,I_fromInt(-2147483648));continue;}else{var _z4=E(_z1);if(!_z4._){var _z5=_z4.a;return new T2(0,new T1(0,B(_u8(_z3,_z5))),new T1(0,B(_uE(_z3,_z5))));}else{_z0=new T1(1,I_fromInt(_z3));_z1=_z4;continue;}}}else{var _z6=E(_z1);if(!_z6._){_z0=_z2;_z1=new T1(1,I_fromInt(_z6.a));continue;}else{var _z7=I_divMod(_z2.a,_z6.a);return new T2(0,new T1(1,_z7.a),new T1(1,_z7.b));}}}},_z8=function(_z9,_za){if(!B(_5q(_za,_wB))){var _zb=B(_yZ(_z9,_za));return new T2(0,_zb.a,_zb.b);}else{return E(_5l);}},_zc=function(_zd,_ze){while(1){var _zf=E(_zd);if(!_zf._){var _zg=E(_zf.a);if(_zg==(-2147483648)){_zd=new T1(1,I_fromInt(-2147483648));continue;}else{var _zh=E(_ze);if(!_zh._){return new T1(0,B(_uE(_zg,_zh.a)));}else{_zd=new T1(1,I_fromInt(_zg));_ze=_zh;continue;}}}else{var _zi=_zf.a,_zj=E(_ze);return (_zj._==0)?new T1(1,I_mod(_zi,I_fromInt(_zj.a))):new T1(1,I_mod(_zi,_zj.a));}}},_zk=function(_zl,_zm){if(!B(_5q(_zm,_wB))){return new F(function(){return _zc(_zl,_zm);});}else{return E(_5l);}},_zn=function(_zo,_zp){while(1){var _zq=E(_zo);if(!_zq._){var _zr=E(_zq.a);if(_zr==(-2147483648)){_zo=new T1(1,I_fromInt(-2147483648));continue;}else{var _zs=E(_zp);if(!_zs._){return new T1(0,quot(_zr,_zs.a));}else{_zo=new T1(1,I_fromInt(_zr));_zp=_zs;continue;}}}else{var _zt=_zq.a,_zu=E(_zp);return (_zu._==0)?new T1(0,I_toInt(I_quot(_zt,I_fromInt(_zu.a)))):new T1(1,I_quot(_zt,_zu.a));}}},_zv=function(_zw,_zx){if(!B(_5q(_zx,_wB))){return new F(function(){return _zn(_zw,_zx);});}else{return E(_5l);}},_zy=function(_zz,_zA){if(!B(_5q(_zA,_wB))){var _zB=B(_5K(_zz,_zA));return new T2(0,_zB.a,_zB.b);}else{return E(_5l);}},_zC=function(_zD,_zE){while(1){var _zF=E(_zD);if(!_zF._){var _zG=E(_zF.a);if(_zG==(-2147483648)){_zD=new T1(1,I_fromInt(-2147483648));continue;}else{var _zH=E(_zE);if(!_zH._){return new T1(0,_zG%_zH.a);}else{_zD=new T1(1,I_fromInt(_zG));_zE=_zH;continue;}}}else{var _zI=_zF.a,_zJ=E(_zE);return (_zJ._==0)?new T1(1,I_rem(_zI,I_fromInt(_zJ.a))):new T1(1,I_rem(_zI,_zJ.a));}}},_zK=function(_zL,_zM){if(!B(_5q(_zM,_wB))){return new F(function(){return _zC(_zL,_zM);});}else{return E(_5l);}},_zN=function(_zO){return E(_zO);},_zP=function(_zQ){return E(_zQ);},_zR=function(_zS){var _zT=E(_zS);if(!_zT._){var _zU=E(_zT.a);return (_zU==(-2147483648))?E(_8A):(_zU<0)?new T1(0, -_zU):E(_zT);}else{var _zV=_zT.a;return (I_compareInt(_zV,0)>=0)?E(_zT):new T1(1,I_negate(_zV));}},_zW=new T1(0,0),_zX=new T1(0,-1),_zY=function(_zZ){var _A0=E(_zZ);if(!_A0._){var _A1=_A0.a;return (_A1>=0)?(E(_A1)==0)?E(_zW):E(_6c):E(_zX);}else{var _A2=I_compareInt(_A0.a,0);return (_A2<=0)?(E(_A2)==0)?E(_zW):E(_zX):E(_6c);}},_A3={_:0,a:_5B,b:_7W,c:_wb,d:_8B,e:_zR,f:_zY,g:_zP},_A4=function(_A5,_A6){var _A7=E(_A5);if(!_A7._){var _A8=_A7.a,_A9=E(_A6);return (_A9._==0)?_A8!=_A9.a:(I_compareInt(_A9.a,_A8)==0)?false:true;}else{var _Aa=_A7.a,_Ab=E(_A6);return (_Ab._==0)?(I_compareInt(_Aa,_Ab.a)==0)?false:true:(I_compare(_Aa,_Ab.a)==0)?false:true;}},_Ac=new T2(0,_5q,_A4),_Ad=function(_Ae,_Af){return (!B(_7H(_Ae,_Af)))?E(_Ae):E(_Af);},_Ag=function(_Ah,_Ai){return (!B(_7H(_Ah,_Ai)))?E(_Ai):E(_Ah);},_Aj={_:0,a:_Ac,b:_4d,c:_6d,d:_7H,e:_64,f:_yi,g:_Ad,h:_Ag},_Ak=function(_Al){return new T2(0,E(_Al),E(_oF));},_Am=new T3(0,_A3,_Aj,_Ak),_An={_:0,a:_Am,b:_yN,c:_zv,d:_zK,e:_yW,f:_zk,g:_zy,h:_z8,i:_zN},_Ao=function(_Ap){return E(E(_Ap).b);},_Aq=function(_Ar){return E(E(_Ar).g);},_As=new T1(0,1),_At=function(_Au,_Av,_Aw){var _Ax=B(_Ao(_Au)),_Ay=B(_1O(_Ax)),_Az=new T(function(){var _AA=new T(function(){var _AB=new T(function(){var _AC=new T(function(){return B(A3(_Aq,_Au,_An,new T(function(){return B(A3(_aW,_Ax,_Av,_Aw));})));});return B(A2(_28,_Ay,_AC));}),_AD=new T(function(){return B(A2(_2l,_Ay,new T(function(){return B(A2(_28,_Ay,_As));})));});return B(A3(_1Q,_Ay,_AD,_AB));});return B(A3(_1Q,_Ay,_AA,_Aw));});return new F(function(){return A3(_1S,_Ay,_Av,_Az);});},_AE=1.5707963267948966,_AF=function(_AG){return 0.2/Math.cos(B(_At(_y3,_AG,_AE))-0.7853981633974483);},_AH=0.3,_AI=-0.1,_AJ=new T3(0,_rS,_AI,_AH),_AK=new T2(0,_AJ,_rS),_AL=new T(function(){var _AM=B(_qF(_AF,_rP,_s8,_AK,_s2));return {_:0,a:_AM.a,b:_AM.b,c:_AM.c,d:_AM.d,e:_AM.e,f:_AM.f,g:_AM.g,h:_AM.h};}),_AN=new T2(1,_AL,_T),_AO=new T2(1,_s3,_AN),_AP=new T(function(){return B(unCStr("Negative range size"));}),_AQ=new T(function(){return B(err(_AP));}),_AR=function(_){var _AS=B(_ke(_AO,0))-1|0,_AT=function(_AU){if(_AU>=0){var _AV=newArr(_AU,_kk),_AW=_AV,_AX=E(_AU);if(!_AX){return new T4(0,E(_s5),E(_AS),0,_AW);}else{var _AY=function(_AZ,_B0,_){while(1){var _B1=E(_AZ);if(!_B1._){return E(_);}else{var _=_AW[_B0]=_B1.a;if(_B0!=(_AX-1|0)){var _B2=_B0+1|0;_AZ=_B1.b;_B0=_B2;continue;}else{return E(_);}}}},_=B((function(_B3,_B4,_B5,_){var _=_AW[_B5]=_B3;if(_B5!=(_AX-1|0)){return new F(function(){return _AY(_B4,_B5+1|0,_);});}else{return E(_);}})(_s3,_AN,0,_));return new T4(0,E(_s5),E(_AS),_AX,_AW);}}else{return E(_AQ);}};if(0>_AS){return new F(function(){return _AT(0);});}else{return new F(function(){return _AT(_AS+1|0);});}},_B6=function(_B7){var _B8=B(A1(_B7,_));return E(_B8);},_B9=new T(function(){return B(_B6(_AR));}),_Ba=function(_Bb,_Bc,_){var _Bd=B(A1(_Bb,_)),_Be=B(A1(_Bc,_));return _Bd;},_Bf=function(_Bg,_Bh,_){var _Bi=B(A1(_Bg,_)),_Bj=B(A1(_Bh,_));return new T(function(){return B(A1(_Bi,_Bj));});},_Bk=function(_Bl,_Bm,_){var _Bn=B(A1(_Bm,_));return _Bl;},_Bo=function(_Bp,_Bq,_){var _Br=B(A1(_Bq,_));return new T(function(){return B(A1(_Bp,_Br));});},_Bs=new T2(0,_Bo,_Bk),_Bt=function(_Bu,_){return _Bu;},_Bv=function(_Bw,_Bx,_){var _By=B(A1(_Bw,_));return new F(function(){return A1(_Bx,_);});},_Bz=new T5(0,_Bs,_Bt,_Bf,_Bv,_Ba),_BA=function(_BB){var _BC=E(_BB);return (E(_BC.b)-E(_BC.a)|0)+1|0;},_BD=function(_BE,_BF){var _BG=E(_BE),_BH=E(_BF);return (E(_BG.a)>_BH)?false:_BH<=E(_BG.b);},_BI=function(_BJ,_BK){var _BL=jsShowI(_BJ);return new F(function(){return _14(fromJSStr(_BL),_BK);});},_BM=function(_BN,_BO,_BP){if(_BO>=0){return new F(function(){return _BI(_BO,_BP);});}else{if(_BN<=6){return new F(function(){return _BI(_BO,_BP);});}else{return new T2(1,_9n,new T(function(){var _BQ=jsShowI(_BO);return B(_14(fromJSStr(_BQ),new T2(1,_9m,_BP)));}));}}},_BR=function(_BS){return new F(function(){return _BM(0,E(_BS),_T);});},_BT=function(_BU,_BV,_BW){return new F(function(){return _BM(E(_BU),E(_BV),_BW);});},_BX=function(_BY,_BZ){return new F(function(){return _BM(0,E(_BY),_BZ);});},_C0=function(_C1,_C2){return new F(function(){return _51(_BX,_C1,_C2);});},_C3=new T3(0,_BT,_BR,_C0),_C4=0,_C5=function(_C6,_C7,_C8){return new F(function(){return A1(_C6,new T2(1,_4Y,new T(function(){return B(A1(_C7,_C8));})));});},_C9=new T(function(){return B(unCStr("foldr1"));}),_Ca=new T(function(){return B(_o5(_C9));}),_Cb=function(_Cc,_Cd){var _Ce=E(_Cd);if(!_Ce._){return E(_Ca);}else{var _Cf=_Ce.a,_Cg=E(_Ce.b);if(!_Cg._){return E(_Cf);}else{return new F(function(){return A2(_Cc,_Cf,new T(function(){return B(_Cb(_Cc,_Cg));}));});}}},_Ch=new T(function(){return B(unCStr(" out of range "));}),_Ci=new T(function(){return B(unCStr("}.index: Index "));}),_Cj=new T(function(){return B(unCStr("Ix{"));}),_Ck=new T2(1,_9m,_T),_Cl=new T2(1,_9m,_Ck),_Cm=0,_Cn=function(_Co){return E(E(_Co).a);},_Cp=function(_Cq,_Cr,_Cs,_Ct,_Cu){var _Cv=new T(function(){var _Cw=new T(function(){var _Cx=new T(function(){var _Cy=new T(function(){var _Cz=new T(function(){return B(A3(_Cb,_C5,new T2(1,new T(function(){return B(A3(_Cn,_Cs,_Cm,_Ct));}),new T2(1,new T(function(){return B(A3(_Cn,_Cs,_Cm,_Cu));}),_T)),_Cl));});return B(_14(_Ch,new T2(1,_9n,new T2(1,_9n,_Cz))));});return B(A(_Cn,[_Cs,_C4,_Cr,new T2(1,_9m,_Cy)]));});return B(_14(_Ci,new T2(1,_9n,_Cx)));},1);return B(_14(_Cq,_Cw));},1);return new F(function(){return err(B(_14(_Cj,_Cv)));});},_CA=function(_CB,_CC,_CD,_CE,_CF){return new F(function(){return _Cp(_CB,_CC,_CF,_CD,_CE);});},_CG=function(_CH,_CI,_CJ,_CK){var _CL=E(_CJ);return new F(function(){return _CA(_CH,_CI,_CL.a,_CL.b,_CK);});},_CM=function(_CN,_CO,_CP,_CQ){return new F(function(){return _CG(_CQ,_CP,_CO,_CN);});},_CR=new T(function(){return B(unCStr("Int"));}),_CS=function(_CT,_CU){return new F(function(){return _CM(_C3,_CU,_CT,_CR);});},_CV=function(_CW,_CX){var _CY=E(_CW),_CZ=E(_CY.a),_D0=E(_CX);if(_CZ>_D0){return new F(function(){return _CS(_D0,_CY);});}else{if(_D0>E(_CY.b)){return new F(function(){return _CS(_D0,_CY);});}else{return _D0-_CZ|0;}}},_D1=function(_D2){var _D3=E(_D2);return new F(function(){return _tS(_D3.a,_D3.b);});},_D4=function(_D5){var _D6=E(_D5),_D7=E(_D6.a),_D8=E(_D6.b);return (_D7>_D8)?E(_C4):(_D8-_D7|0)+1|0;},_D9=function(_Da,_Db){return new F(function(){return _vh(_Db,E(_Da).a);});},_Dc={_:0,a:_w7,b:_D1,c:_CV,d:_D9,e:_BD,f:_D4,g:_BA},_Dd=function(_De,_Df){return new T2(1,_De,_Df);},_Dg=function(_Dh,_Di){var _Dj=E(_Di);return new T2(0,_Dj.a,_Dj.b);},_Dk=function(_Dl){return E(E(_Dl).f);},_Dm=function(_Dn,_Do,_Dp){var _Dq=E(_Do),_Dr=_Dq.a,_Ds=_Dq.b,_Dt=function(_){var _Du=B(A2(_Dk,_Dn,_Dq));if(_Du>=0){var _Dv=newArr(_Du,_kk),_Dw=_Dv,_Dx=E(_Du);if(!_Dx){return new T(function(){return new T4(0,E(_Dr),E(_Ds),0,_Dw);});}else{var _Dy=function(_Dz,_DA,_){while(1){var _DB=E(_Dz);if(!_DB._){return E(_);}else{var _=_Dw[_DA]=_DB.a;if(_DA!=(_Dx-1|0)){var _DC=_DA+1|0;_Dz=_DB.b;_DA=_DC;continue;}else{return E(_);}}}},_=B(_Dy(_Dp,0,_));return new T(function(){return new T4(0,E(_Dr),E(_Ds),_Dx,_Dw);});}}else{return E(_AQ);}};return new F(function(){return _B6(_Dt);});},_DD=function(_DE,_DF,_DG,_DH){var _DI=new T(function(){var _DJ=E(_DH),_DK=_DJ.c-1|0,_DL=new T(function(){return B(A2(_eI,_DF,_T));});if(0<=_DK){var _DM=new T(function(){return B(_aS(_DF));}),_DN=function(_DO){var _DP=new T(function(){var _DQ=new T(function(){return B(A1(_DG,new T(function(){return E(_DJ.d[_DO]);})));});return B(A3(_b0,_DM,_Dd,_DQ));});return new F(function(){return A3(_aY,_DF,_DP,new T(function(){if(_DO!=_DK){return B(_DN(_DO+1|0));}else{return E(_DL);}}));});};return B(_DN(0));}else{return E(_DL);}}),_DR=new T(function(){return B(_Dg(_DE,_DH));});return new F(function(){return A3(_b0,B(_aS(_DF)),function(_DS){return new F(function(){return _Dm(_DE,_DR,_DS);});},_DI);});},_DT=function(_){return _S;},_DU=new T(function(){return eval("vertex");}),_DV=function(_DW,_DX,_DY,_DZ,_E0,_E1,_){var _E2=__apply(E(_DU),new T2(1,_E1,new T2(1,_E0,new T2(1,_DZ,new T2(1,_DY,new T2(1,_DX,new T2(1,_DW,_T)))))));return new F(function(){return _DT(_);});},_E3=function(_E4,_){while(1){var _E5=E(_E4);if(!_E5._){return _S;}else{var _E6=E(_E5.a),_E7=E(_E6.a),_E8=E(_E7.a),_E9=E(_E7.b),_Ea=B(_DV(E(_E8.a),E(_E8.b),E(_E8.c),E(_E9.a),E(_E9.b),E(_E7.c),_)),_Eb=E(_E6.b),_Ec=E(_Eb.a),_Ed=E(_Eb.b),_Ee=B(_DV(E(_Ec.a),E(_Ec.b),E(_Ec.c),E(_Ed.a),E(_Ed.b),E(_Eb.c),_)),_Ef=E(_E6.c),_Eg=E(_Ef.a),_Eh=E(_Ef.b),_Ei=B(_DV(E(_Eg.a),E(_Eg.b),E(_Eg.c),E(_Eh.a),E(_Eh.b),E(_Ef.c),_));_E4=_E5.b;continue;}}},_Ej=new T(function(){return eval("drawTriangles");}),_Ek=function(_){var _El=__app0(E(_Ej));return new F(function(){return _DT(_);});},_Em=function(_En,_){var _Eo=B(_E3(_En,_));return new F(function(){return _Ek(_);});},_Ep=function(_Eq,_){return new F(function(){return _Em(E(_Eq).h,_);});},_Er=new T(function(){return eval("draw");}),_Es=function(_Et){return E(_Et);},_Eu=function(_Ev){return E(_Ev);},_Ew=function(_Ex,_Ey){return E(_Ey);},_Ez=function(_EA,_EB){return E(_EA);},_EC=function(_ED){return E(_ED);},_EE=new T2(0,_EC,_Ez),_EF=function(_EG,_EH){return E(_EG);},_EI=new T5(0,_EE,_Eu,_Es,_Ew,_EF),_EJ=function(_EK,_EL,_EM,_EN,_EO,_EP){var _EQ=new T(function(){var _ER=E(_EN),_ES=E(_EO),_ET=new T(function(){var _EU=E(_ER.a),_EV=E(_ES.a);return new T3(0,new T(function(){return E(_EU.a)+E(_EV.a)*5.0e-2;}),new T(function(){return E(_EU.b)+E(_EV.b)*5.0e-2;}),new T(function(){return E(_EU.c)+E(_EV.c)*5.0e-2;}));});return new T2(0,_ET,new T(function(){return E(_ER.b)+E(_ES.b)*5.0e-2;}));});return new F(function(){return _qi(_EK,_EL,_EM,_EQ,_EO,_EP);});},_EW=new T2(0,_lO,_mn),_EX=function(_EY){var _EZ=E(_EY),_F0=_EZ.b,_F1=_EZ.g,_F2=new T(function(){var _F3=E(_EZ.e),_F4=new T(function(){var _F5=E(_F3.a),_F6=E(_F0),_F7=E(_F1),_F8=B(_n0(_EW,_F6.a,_F6.b,_F6.c,_F7.a,_F7.b,_F7.c));return new T3(0,new T(function(){return E(_F5.a)+E(_F8.a)*5.0e-2;}),new T(function(){return E(_F5.b)+E(_F8.b)*5.0e-2;}),new T(function(){return E(_F5.c)+E(_F8.c)*5.0e-2;}));});return new T2(0,_F4,_F3.b);});return {_:0,a:_EZ.a,b:_F0,c:_EZ.c,d:_EZ.d,e:_F2,f:_EZ.f,g:_F1,h:_EZ.h};},_F9=function(_Fa){var _Fb=E(_Fa),_Fc=B(_EJ(_Fb.a,_Fb.b,_Fb.c,_Fb.d,_Fb.e,_Fb.f));return {_:0,a:_Fc.a,b:_Fc.b,c:_Fc.c,d:_Fc.d,e:_Fc.e,f:_Fc.f,g:_Fc.g,h:_Fc.h};},_Fd=function(_Fe){var _Ff=E(_Fe);if(!_Ff._){return __Z;}else{return new F(function(){return _14(_Ff.a,new T(function(){return B(_Fd(_Ff.b));},1));});}},_Fg=new T(function(){return B(unCStr("base"));}),_Fh=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_Fi=new T(function(){return B(unCStr("IOException"));}),_Fj=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fg,_Fh,_Fi),_Fk=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Fj,_T,_T),_Fl=function(_Fm){return E(_Fk);},_Fn=function(_Fo){var _Fp=E(_Fo);return new F(function(){return _4y(B(_4w(_Fp.a)),_Fl,_Fp.b);});},_Fq=new T(function(){return B(unCStr(": "));}),_Fr=new T(function(){return B(unCStr(")"));}),_Fs=new T(function(){return B(unCStr(" ("));}),_Ft=new T(function(){return B(unCStr("interrupted"));}),_Fu=new T(function(){return B(unCStr("system error"));}),_Fv=new T(function(){return B(unCStr("unsatisified constraints"));}),_Fw=new T(function(){return B(unCStr("user error"));}),_Fx=new T(function(){return B(unCStr("permission denied"));}),_Fy=new T(function(){return B(unCStr("illegal operation"));}),_Fz=new T(function(){return B(unCStr("end of file"));}),_FA=new T(function(){return B(unCStr("resource exhausted"));}),_FB=new T(function(){return B(unCStr("resource busy"));}),_FC=new T(function(){return B(unCStr("does not exist"));}),_FD=new T(function(){return B(unCStr("already exists"));}),_FE=new T(function(){return B(unCStr("resource vanished"));}),_FF=new T(function(){return B(unCStr("timeout"));}),_FG=new T(function(){return B(unCStr("unsupported operation"));}),_FH=new T(function(){return B(unCStr("hardware fault"));}),_FI=new T(function(){return B(unCStr("inappropriate type"));}),_FJ=new T(function(){return B(unCStr("invalid argument"));}),_FK=new T(function(){return B(unCStr("failed"));}),_FL=new T(function(){return B(unCStr("protocol error"));}),_FM=function(_FN,_FO){switch(E(_FN)){case 0:return new F(function(){return _14(_FD,_FO);});break;case 1:return new F(function(){return _14(_FC,_FO);});break;case 2:return new F(function(){return _14(_FB,_FO);});break;case 3:return new F(function(){return _14(_FA,_FO);});break;case 4:return new F(function(){return _14(_Fz,_FO);});break;case 5:return new F(function(){return _14(_Fy,_FO);});break;case 6:return new F(function(){return _14(_Fx,_FO);});break;case 7:return new F(function(){return _14(_Fw,_FO);});break;case 8:return new F(function(){return _14(_Fv,_FO);});break;case 9:return new F(function(){return _14(_Fu,_FO);});break;case 10:return new F(function(){return _14(_FL,_FO);});break;case 11:return new F(function(){return _14(_FK,_FO);});break;case 12:return new F(function(){return _14(_FJ,_FO);});break;case 13:return new F(function(){return _14(_FI,_FO);});break;case 14:return new F(function(){return _14(_FH,_FO);});break;case 15:return new F(function(){return _14(_FG,_FO);});break;case 16:return new F(function(){return _14(_FF,_FO);});break;case 17:return new F(function(){return _14(_FE,_FO);});break;default:return new F(function(){return _14(_Ft,_FO);});}},_FP=new T(function(){return B(unCStr("}"));}),_FQ=new T(function(){return B(unCStr("{handle: "));}),_FR=function(_FS,_FT,_FU,_FV,_FW,_FX){var _FY=new T(function(){var _FZ=new T(function(){var _G0=new T(function(){var _G1=E(_FV);if(!_G1._){return E(_FX);}else{var _G2=new T(function(){return B(_14(_G1,new T(function(){return B(_14(_Fr,_FX));},1)));},1);return B(_14(_Fs,_G2));}},1);return B(_FM(_FT,_G0));}),_G3=E(_FU);if(!_G3._){return E(_FZ);}else{return B(_14(_G3,new T(function(){return B(_14(_Fq,_FZ));},1)));}}),_G4=E(_FW);if(!_G4._){var _G5=E(_FS);if(!_G5._){return E(_FY);}else{var _G6=E(_G5.a);if(!_G6._){var _G7=new T(function(){var _G8=new T(function(){return B(_14(_FP,new T(function(){return B(_14(_Fq,_FY));},1)));},1);return B(_14(_G6.a,_G8));},1);return new F(function(){return _14(_FQ,_G7);});}else{var _G9=new T(function(){var _Ga=new T(function(){return B(_14(_FP,new T(function(){return B(_14(_Fq,_FY));},1)));},1);return B(_14(_G6.a,_Ga));},1);return new F(function(){return _14(_FQ,_G9);});}}}else{return new F(function(){return _14(_G4.a,new T(function(){return B(_14(_Fq,_FY));},1));});}},_Gb=function(_Gc){var _Gd=E(_Gc);return new F(function(){return _FR(_Gd.a,_Gd.b,_Gd.c,_Gd.d,_Gd.f,_T);});},_Ge=function(_Gf,_Gg,_Gh){var _Gi=E(_Gg);return new F(function(){return _FR(_Gi.a,_Gi.b,_Gi.c,_Gi.d,_Gi.f,_Gh);});},_Gj=function(_Gk,_Gl){var _Gm=E(_Gk);return new F(function(){return _FR(_Gm.a,_Gm.b,_Gm.c,_Gm.d,_Gm.f,_Gl);});},_Gn=function(_Go,_Gp){return new F(function(){return _51(_Gj,_Go,_Gp);});},_Gq=new T3(0,_Ge,_Gb,_Gn),_Gr=new T(function(){return new T5(0,_Fl,_Gq,_Gs,_Fn,_Gb);}),_Gs=function(_Gt){return new T2(0,_Gr,_Gt);},_Gu=__Z,_Gv=7,_Gw=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:43:7-13"));}),_Gx=new T6(0,_Gu,_Gv,_T,_Gw,_Gu,_Gu),_Gy=new T(function(){return B(_Gs(_Gx));}),_Gz=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:44:7-13"));}),_GA=new T6(0,_Gu,_Gv,_T,_Gz,_Gu,_Gu),_GB=new T(function(){return B(_Gs(_GA));}),_GC=new T2(1,_T,_T),_GD=function(_GE,_){var _GF=B(_DD(_Dc,_EI,_EX,_GE)),_GG=_GF.c,_GH=_GF.d,_GI=E(_GF.a),_GJ=E(_GF.b);if(_GI<=_GJ){var _GK=function(_GL,_GM,_){if(_GL<=_GJ){var _GN=E(_GM),_GO=function(_GP,_GQ,_GR,_GS,_GT,_){if(_GQ>_GL){return new F(function(){return die(_Gy);});}else{if(_GL>_GR){return new F(function(){return die(_Gy);});}else{if(_GQ>_GP){return new F(function(){return die(_GB);});}else{if(_GP>_GR){return new F(function(){return die(_GB);});}else{if(_GP!=_GJ){var _GU=B(_GO(_GP+1|0,_GQ,_GR,_GS,_GT,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_GU).a);})),new T(function(){return E(E(_GU).b);}));}else{return new T2(0,_GC,new T4(0,E(_GQ),E(_GR),_GS,_GT));}}}}}},_GV=B(_GO(_GL,E(_GN.a),E(_GN.b),_GN.c,_GN.d,_));if(_GL!=_GJ){var _GW=B(_GK(_GL+1|0,new T(function(){return E(E(_GV).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Fd(E(_GV).a));}),new T(function(){return E(E(_GW).a);})),new T(function(){return E(E(_GW).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Fd(E(_GV).a));}),_T),new T(function(){return E(E(_GV).b);}));}}else{if(_GL!=_GJ){var _GX=B(_GK(_GL+1|0,_GM,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_GX).a);})),new T(function(){return E(E(_GX).b);}));}else{return new T2(0,new T2(1,_T,_T),_GM);}}},_GY=function(_GZ,_H0,_H1,_H2,_H3,_){if(_GZ<=_GJ){var _H4=function(_H5,_H6,_H7,_H8,_H9,_){if(_H6>_GZ){return new F(function(){return die(_Gy);});}else{if(_GZ>_H7){return new F(function(){return die(_Gy);});}else{if(_H6>_H5){return new F(function(){return die(_GB);});}else{if(_H5>_H7){return new F(function(){return die(_GB);});}else{if(_H5!=_GJ){var _Ha=B(_H4(_H5+1|0,_H6,_H7,_H8,_H9,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_Ha).a);})),new T(function(){return E(E(_Ha).b);}));}else{return new T2(0,_GC,new T4(0,E(_H6),E(_H7),_H8,_H9));}}}}}},_Hb=B(_H4(_GZ,_H0,_H1,_H2,_H3,_));if(_GZ!=_GJ){var _Hc=B(_GK(_GZ+1|0,new T(function(){return E(E(_Hb).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Fd(E(_Hb).a));}),new T(function(){return E(E(_Hc).a);})),new T(function(){return E(E(_Hc).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Fd(E(_Hb).a));}),_T),new T(function(){return E(E(_Hb).b);}));}}else{if(_GZ!=_GJ){var _Hd=B(_GY(_GZ+1|0,_H0,_H1,_H2,_H3,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_Hd).a);})),new T(function(){return E(E(_Hd).b);}));}else{return new T2(0,new T2(1,_T,_T),new T4(0,E(_H0),E(_H1),_H2,_H3));}}},_He=B(_GY(_GI,_GI,_GJ,_GG,_GH,_)),_Hf=new T(function(){return B(_DD(_Dc,_EI,_F9,new T(function(){return E(E(_He).b);})));});return new T2(0,_S,_Hf);}else{var _Hg=new T(function(){var _Hh=function(_){var _Hi=function(_Hj){if(_Hj>=0){var _Hk=newArr(_Hj,_kk),_Hl=_Hk,_Hm=E(_Hj);if(!_Hm){return new T4(0,E(_GI),E(_GJ),0,_Hl);}else{var _Hn=_GG-1|0,_Ho=function(_Hp,_Hq,_){while(1){var _Hr=E(_Hp);if(!_Hr._){return E(_);}else{var _=_Hl[_Hq]=_Hr.a;if(_Hq!=(_Hm-1|0)){var _Hs=_Hq+1|0;_Hp=_Hr.b;_Hq=_Hs;continue;}else{return E(_);}}}};if(0<=_Hn){var _Ht=function(_Hu){return new T2(1,new T(function(){var _Hv=E(_GH[_Hu]),_Hw=B(_EJ(_Hv.a,_Hv.b,_Hv.c,_Hv.d,_Hv.e,_Hv.f));return {_:0,a:_Hw.a,b:_Hw.b,c:_Hw.c,d:_Hw.d,e:_Hw.e,f:_Hw.f,g:_Hw.g,h:_Hw.h};}),new T(function(){if(_Hu!=_Hn){return B(_Ht(_Hu+1|0));}else{return __Z;}}));},_=B(_Ho(B(_Ht(0)),0,_));return new T4(0,E(_GI),E(_GJ),_Hm,_Hl);}else{return new T4(0,E(_GI),E(_GJ),_Hm,_Hl);}}}else{return E(_AQ);}};if(_GI>_GJ){return new F(function(){return _Hi(0);});}else{return new F(function(){return _Hi((_GJ-_GI|0)+1|0);});}};return B(_B6(_Hh));});return new T2(0,_S,_Hg);}},_Hx=new T(function(){return eval("refresh");}),_Hy=function(_Hz,_){var _HA=__app0(E(_Hx)),_HB=__app0(E(_Er)),_HC=B(A(_DD,[_Dc,_Bz,_Ep,_Hz,_])),_HD=B(_GD(_Hz,_));return new T(function(){return E(E(_HD).b);});},_HE=function(_HF,_HG,_HH){var _HI=function(_){var _HJ=B(_Hy(_HF,_));return new T(function(){return B(A1(_HH,new T1(1,_HJ)));});};return new T1(0,_HI);},_HK=new T0(2),_HL=function(_HM,_HN,_HO){return function(_){var _HP=E(_HM),_HQ=rMV(_HP),_HR=E(_HQ);if(!_HR._){var _HS=new T(function(){var _HT=new T(function(){return B(A1(_HO,_S));});return B(_14(_HR.b,new T2(1,new T2(0,_HN,function(_HU){return E(_HT);}),_T)));}),_=wMV(_HP,new T2(0,_HR.a,_HS));return _HK;}else{var _HV=E(_HR.a);if(!_HV._){var _=wMV(_HP,new T2(0,_HN,_T));return new T(function(){return B(A1(_HO,_S));});}else{var _=wMV(_HP,new T1(1,_HV.b));return new T1(1,new T2(1,new T(function(){return B(A1(_HO,_S));}),new T2(1,new T(function(){return B(A2(_HV.a,_HN,_U));}),_T)));}}};},_HW=function(_HX){return E(E(_HX).b);},_HY=function(_HZ,_I0,_I1){var _I2=new T(function(){return new T1(0,B(_HL(_I0,_I1,_U)));}),_I3=function(_I4){return new T1(1,new T2(1,new T(function(){return B(A1(_I4,_S));}),new T2(1,_I2,_T)));};return new F(function(){return A2(_HW,_HZ,_I3);});},_I5=function(_){return new F(function(){return __jsNull();});},_I6=function(_I7){var _I8=B(A1(_I7,_));return E(_I8);},_I9=new T(function(){return B(_I6(_I5));}),_Ia=new T(function(){return E(_I9);}),_Ib=new T(function(){return eval("window.requestAnimationFrame");}),_Ic=new T1(1,_T),_Id=function(_Ie,_If){return function(_){var _Ig=E(_Ie),_Ih=rMV(_Ig),_Ii=E(_Ih);if(!_Ii._){var _Ij=_Ii.a,_Ik=E(_Ii.b);if(!_Ik._){var _=wMV(_Ig,_Ic);return new T(function(){return B(A1(_If,_Ij));});}else{var _Il=E(_Ik.a),_=wMV(_Ig,new T2(0,_Il.a,_Ik.b));return new T1(1,new T2(1,new T(function(){return B(A1(_If,_Ij));}),new T2(1,new T(function(){return B(A1(_Il.b,_U));}),_T)));}}else{var _Im=new T(function(){var _In=function(_Io){var _Ip=new T(function(){return B(A1(_If,_Io));});return function(_Iq){return E(_Ip);};};return B(_14(_Ii.a,new T2(1,_In,_T)));}),_=wMV(_Ig,new T1(1,_Im));return _HK;}};},_Ir=function(_Is,_It){return new T1(0,B(_Id(_Is,_It)));},_Iu=function(_Iv,_Iw){var _Ix=new T(function(){return new T1(0,B(_HL(_Iv,_S,_U)));});return function(_){var _Iy=__createJSFunc(2,function(_Iz,_){var _IA=B(_1e(_Ix,_T,_));return _Ia;}),_IB=__app1(E(_Ib),_Iy);return new T(function(){return B(_Ir(_Iv,_Iw));});};},_IC=new T1(1,_T),_ID=function(_IE){var _IF=new T(function(){return B(_IG(_));}),_IH=new T(function(){var _II=function(_IJ){return E(_IF);},_IK=function(_){var _IL=nMV(_IC);return new T(function(){return new T1(0,B(_Iu(_IL,_II)));});};return B(A(_HY,[_13,_IE,_S,function(_IM){return E(new T1(0,_IK));}]));}),_IG=function(_IN){return E(_IH);};return new F(function(){return _IG(_);});},_IO=function(_IP){return E(E(_IP).a);},_IQ=function(_IR){return E(E(_IR).d);},_IS=function(_IT){return E(E(_IT).c);},_IU=function(_IV){return E(E(_IV).c);},_IW=new T1(1,_T),_IX=function(_IY){var _IZ=function(_){var _J0=nMV(_IW);return new T(function(){return B(A1(_IY,_J0));});};return new T1(0,_IZ);},_J1=function(_J2,_J3){var _J4=new T(function(){return B(_IU(_J2));}),_J5=B(_IO(_J2)),_J6=function(_J7){var _J8=new T(function(){return B(A1(_J4,new T(function(){return B(A1(_J3,_J7));})));});return new F(function(){return A3(_IS,_J5,_J8,new T(function(){return B(A2(_IQ,_J5,_J7));}));});};return new F(function(){return A3(_J,_J5,new T(function(){return B(A2(_HW,_J2,_IX));}),_J6);});},_J9=function(_Ja,_Jb,_Jc){var _Jd=new T(function(){return B(_IO(_Ja));}),_Je=new T(function(){return B(A2(_IQ,_Jd,_S));}),_Jf=function(_Jg,_Jh){var _Ji=new T(function(){var _Jj=new T(function(){return B(A2(_HW,_Ja,function(_Jk){return new F(function(){return _Ir(_Jh,_Jk);});}));});return B(A3(_J,_Jd,_Jj,new T(function(){return B(A1(_Jc,_Jg));})));});return new F(function(){return A3(_J,_Jd,_Ji,function(_Jl){var _Jm=E(_Jl);if(!_Jm._){return E(_Je);}else{return new F(function(){return _Jf(_Jm.a,_Jh);});}});});};return new F(function(){return _J1(_Ja,function(_Jk){return new F(function(){return _Jf(_Jb,_Jk);});});});},_Jn=function(_){var _Jo=__app2(E(_1j),E(_a5),E(_kd));return new F(function(){return _1e(new T(function(){return B(A(_J9,[_13,_B9,_HE,_ID]));}),_T,_);});},_Jp=function(_){return new F(function(){return _Jn(_);});};
var hasteMain = function() {B(A(_Jp, [0]));};window.onload = hasteMain;