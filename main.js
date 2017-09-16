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

var _0=function(_1,_2,_3){return new F(function(){return A1(_1,function(_4){return new F(function(){return A2(_2,_4,_3);});});});},_5=function(_6,_7,_8){var _9=function(_a){var _b=new T(function(){return B(A1(_8,_a));});return new F(function(){return A1(_7,function(_c){return E(_b);});});};return new F(function(){return A1(_6,_9);});},_d=function(_e,_f,_g){var _h=new T(function(){return B(A1(_f,function(_i){return new F(function(){return A1(_g,_i);});}));});return new F(function(){return A1(_e,function(_j){return E(_h);});});},_k=function(_l,_m,_n){var _o=function(_p){var _q=function(_r){return new F(function(){return A1(_n,new T(function(){return B(A1(_p,_r));}));});};return new F(function(){return A1(_m,_q);});};return new F(function(){return A1(_l,_o);});},_s=function(_t,_u){return new F(function(){return A1(_u,_t);});},_v=function(_w,_x,_y){var _z=new T(function(){return B(A1(_y,_w));});return new F(function(){return A1(_x,function(_A){return E(_z);});});},_B=function(_C,_D,_E){var _F=function(_G){return new F(function(){return A1(_E,new T(function(){return B(A1(_C,_G));}));});};return new F(function(){return A1(_D,_F);});},_H=new T2(0,_B,_v),_I=new T5(0,_H,_s,_k,_d,_5),_J=function(_K){return E(E(_K).b);},_L=function(_M,_N){return new F(function(){return A3(_J,_O,_M,function(_P){return E(_N);});});},_Q=function(_R){return new F(function(){return err(_R);});},_O=new T(function(){return new T5(0,_I,_0,_L,_s,_Q);}),_S=0,_T=__Z,_U=function(_V){return new T0(2);},_W=function(_X){var _Y=new T(function(){return B(A1(_X,_U));}),_Z=function(_10){return new T1(1,new T2(1,new T(function(){return B(A1(_10,_S));}),new T2(1,_Y,_T)));};return E(_Z);},_11=function(_12){return E(_12);},_13=new T3(0,_O,_11,_W),_14=function(_15,_16){var _17=E(_15);return (_17._==0)?E(_16):new T2(1,_17.a,new T(function(){return B(_14(_17.b,_16));}));},_18=function(_19,_){while(1){var _1a=E(_19);if(!_1a._){return _S;}else{var _1b=_1a.b,_1c=E(_1a.a);switch(_1c._){case 0:var _1d=B(A1(_1c.a,_));_19=B(_14(_1b,new T2(1,_1d,_T)));continue;case 1:_19=B(_14(_1b,_1c.a));continue;default:_19=_1b;continue;}}}},_1e=function(_1f,_1g,_){var _1h=E(_1f);switch(_1h._){case 0:var _1i=B(A1(_1h.a,_));return new F(function(){return _18(B(_14(_1g,new T2(1,_1i,_T))),_);});break;case 1:return new F(function(){return _18(B(_14(_1g,_1h.a)),_);});break;default:return new F(function(){return _18(_1g,_);});}},_1j=new T(function(){return eval("compile");}),_1k=function(_1l){return E(E(_1l).b);},_1m=function(_1n){return E(E(_1n).a);},_1o=function(_1p,_1q,_1r){var _1s=E(_1r);if(!_1s._){return new F(function(){return A1(_1q,_1s.a);});}else{var _1t=new T(function(){return B(_1k(_1p));}),_1u=new T(function(){return B(_1m(_1p));}),_1v=function(_1w){var _1x=E(_1w);if(!_1x._){return E(_1u);}else{return new F(function(){return A2(_1t,new T(function(){return B(_1o(_1p,_1q,_1x.a));}),new T(function(){return B(_1v(_1x.b));}));});}};return new F(function(){return _1v(_1s.a);});}},_1y=function(_1z){var _1A=E(_1z);if(!_1A._){return __Z;}else{return new F(function(){return _14(_1A.a,new T(function(){return B(_1y(_1A.b));},1));});}},_1B=function(_1C){return new F(function(){return _1y(_1C);});},_1D=new T3(0,_T,_14,_1B),_1E=new T(function(){return B(unCStr(","));}),_1F=new T1(0,_1E),_1G=new T(function(){return B(unCStr("pow("));}),_1H=new T1(0,_1G),_1I=new T(function(){return B(unCStr(")"));}),_1J=new T1(0,_1I),_1K=new T2(1,_1J,_T),_1L=function(_1M,_1N){return new T1(1,new T2(1,_1H,new T2(1,_1M,new T2(1,_1F,new T2(1,_1N,_1K)))));},_1O=new T(function(){return B(unCStr("acos("));}),_1P=new T1(0,_1O),_1Q=function(_1R){return new T1(1,new T2(1,_1P,new T2(1,_1R,_1K)));},_1S=new T(function(){return B(unCStr("acosh("));}),_1T=new T1(0,_1S),_1U=function(_1V){return new T1(1,new T2(1,_1T,new T2(1,_1V,_1K)));},_1W=new T(function(){return B(unCStr("asin("));}),_1X=new T1(0,_1W),_1Y=function(_1Z){return new T1(1,new T2(1,_1X,new T2(1,_1Z,_1K)));},_20=new T(function(){return B(unCStr("asinh("));}),_21=new T1(0,_20),_22=function(_23){return new T1(1,new T2(1,_21,new T2(1,_23,_1K)));},_24=new T(function(){return B(unCStr("atan("));}),_25=new T1(0,_24),_26=function(_27){return new T1(1,new T2(1,_25,new T2(1,_27,_1K)));},_28=new T(function(){return B(unCStr("atanh("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1K)));},_2c=new T(function(){return B(unCStr("cos("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1K)));},_2g=new T(function(){return B(unCStr("cosh("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1K)));},_2k=new T(function(){return B(unCStr("exp("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1K)));},_2o=new T(function(){return B(unCStr("log("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1K)));},_2s=new T(function(){return B(unCStr(")/log("));}),_2t=new T1(0,_2s),_2u=function(_2v,_2w){return new T1(1,new T2(1,_2p,new T2(1,_2w,new T2(1,_2t,new T2(1,_2v,_1K)))));},_2x=new T(function(){return B(unCStr("pi"));}),_2y=new T1(0,_2x),_2z=new T(function(){return B(unCStr("sin("));}),_2A=new T1(0,_2z),_2B=function(_2C){return new T1(1,new T2(1,_2A,new T2(1,_2C,_1K)));},_2D=new T(function(){return B(unCStr("sinh("));}),_2E=new T1(0,_2D),_2F=function(_2G){return new T1(1,new T2(1,_2E,new T2(1,_2G,_1K)));},_2H=new T(function(){return B(unCStr("sqrt("));}),_2I=new T1(0,_2H),_2J=function(_2K){return new T1(1,new T2(1,_2I,new T2(1,_2K,_1K)));},_2L=new T(function(){return B(unCStr("tan("));}),_2M=new T1(0,_2L),_2N=function(_2O){return new T1(1,new T2(1,_2M,new T2(1,_2O,_1K)));},_2P=new T(function(){return B(unCStr("tanh("));}),_2Q=new T1(0,_2P),_2R=function(_2S){return new T1(1,new T2(1,_2Q,new T2(1,_2S,_1K)));},_2T=new T(function(){return B(unCStr("("));}),_2U=new T1(0,_2T),_2V=new T(function(){return B(unCStr(")/("));}),_2W=new T1(0,_2V),_2X=function(_2Y,_2Z){return new T1(1,new T2(1,_2U,new T2(1,_2Y,new T2(1,_2W,new T2(1,_2Z,_1K)))));},_30=new T1(0,1),_31=function(_32,_33){var _34=E(_32);if(!_34._){var _35=_34.a,_36=E(_33);if(!_36._){var _37=_36.a;return (_35!=_37)?(_35>_37)?2:0:1;}else{var _38=I_compareInt(_36.a,_35);return (_38<=0)?(_38>=0)?1:2:0;}}else{var _39=_34.a,_3a=E(_33);if(!_3a._){var _3b=I_compareInt(_39,_3a.a);return (_3b>=0)?(_3b<=0)?1:2:0;}else{var _3c=I_compare(_39,_3a.a);return (_3c>=0)?(_3c<=0)?1:2:0;}}},_3d=new T(function(){return B(unCStr("base"));}),_3e=new T(function(){return B(unCStr("GHC.Exception"));}),_3f=new T(function(){return B(unCStr("ArithException"));}),_3g=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3d,_3e,_3f),_3h=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3g,_T,_T),_3i=function(_3j){return E(_3h);},_3k=function(_3l){return E(E(_3l).a);},_3m=function(_3n,_3o,_3p){var _3q=B(A1(_3n,_)),_3r=B(A1(_3o,_)),_3s=hs_eqWord64(_3q.a,_3r.a);if(!_3s){return __Z;}else{var _3t=hs_eqWord64(_3q.b,_3r.b);return (!_3t)?__Z:new T1(1,_3p);}},_3u=function(_3v){var _3w=E(_3v);return new F(function(){return _3m(B(_3k(_3w.a)),_3i,_3w.b);});},_3x=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3y=new T(function(){return B(unCStr("denormal"));}),_3z=new T(function(){return B(unCStr("divide by zero"));}),_3A=new T(function(){return B(unCStr("loss of precision"));}),_3B=new T(function(){return B(unCStr("arithmetic underflow"));}),_3C=new T(function(){return B(unCStr("arithmetic overflow"));}),_3D=function(_3E,_3F){switch(E(_3E)){case 0:return new F(function(){return _14(_3C,_3F);});break;case 1:return new F(function(){return _14(_3B,_3F);});break;case 2:return new F(function(){return _14(_3A,_3F);});break;case 3:return new F(function(){return _14(_3z,_3F);});break;case 4:return new F(function(){return _14(_3y,_3F);});break;default:return new F(function(){return _14(_3x,_3F);});}},_3G=function(_3H){return new F(function(){return _3D(_3H,_T);});},_3I=function(_3J,_3K,_3L){return new F(function(){return _3D(_3K,_3L);});},_3M=44,_3N=93,_3O=91,_3P=function(_3Q,_3R,_3S){var _3T=E(_3R);if(!_3T._){return new F(function(){return unAppCStr("[]",_3S);});}else{var _3U=new T(function(){var _3V=new T(function(){var _3W=function(_3X){var _3Y=E(_3X);if(!_3Y._){return E(new T2(1,_3N,_3S));}else{var _3Z=new T(function(){return B(A2(_3Q,_3Y.a,new T(function(){return B(_3W(_3Y.b));})));});return new T2(1,_3M,_3Z);}};return B(_3W(_3T.b));});return B(A2(_3Q,_3T.a,_3V));});return new T2(1,_3O,_3U);}},_40=function(_41,_42){return new F(function(){return _3P(_3D,_41,_42);});},_43=new T3(0,_3I,_3G,_40),_44=new T(function(){return new T5(0,_3i,_43,_45,_3u,_3G);}),_45=function(_46){return new T2(0,_44,_46);},_47=3,_48=new T(function(){return B(_45(_47));}),_49=new T(function(){return die(_48);}),_4a=function(_4b,_4c){var _4d=E(_4b);return (_4d._==0)?_4d.a*Math.pow(2,_4c):I_toNumber(_4d.a)*Math.pow(2,_4c);},_4e=function(_4f,_4g){var _4h=E(_4f);if(!_4h._){var _4i=_4h.a,_4j=E(_4g);return (_4j._==0)?_4i==_4j.a:(I_compareInt(_4j.a,_4i)==0)?true:false;}else{var _4k=_4h.a,_4l=E(_4g);return (_4l._==0)?(I_compareInt(_4k,_4l.a)==0)?true:false:(I_compare(_4k,_4l.a)==0)?true:false;}},_4m=function(_4n){var _4o=E(_4n);if(!_4o._){return E(_4o.a);}else{return new F(function(){return I_toInt(_4o.a);});}},_4p=function(_4q,_4r){while(1){var _4s=E(_4q);if(!_4s._){var _4t=_4s.a,_4u=E(_4r);if(!_4u._){var _4v=_4u.a,_4w=addC(_4t,_4v);if(!E(_4w.b)){return new T1(0,_4w.a);}else{_4q=new T1(1,I_fromInt(_4t));_4r=new T1(1,I_fromInt(_4v));continue;}}else{_4q=new T1(1,I_fromInt(_4t));_4r=_4u;continue;}}else{var _4x=E(_4r);if(!_4x._){_4q=_4s;_4r=new T1(1,I_fromInt(_4x.a));continue;}else{return new T1(1,I_add(_4s.a,_4x.a));}}}},_4y=function(_4z,_4A){while(1){var _4B=E(_4z);if(!_4B._){var _4C=E(_4B.a);if(_4C==(-2147483648)){_4z=new T1(1,I_fromInt(-2147483648));continue;}else{var _4D=E(_4A);if(!_4D._){var _4E=_4D.a;return new T2(0,new T1(0,quot(_4C,_4E)),new T1(0,_4C%_4E));}else{_4z=new T1(1,I_fromInt(_4C));_4A=_4D;continue;}}}else{var _4F=E(_4A);if(!_4F._){_4z=_4B;_4A=new T1(1,I_fromInt(_4F.a));continue;}else{var _4G=I_quotRem(_4B.a,_4F.a);return new T2(0,new T1(1,_4G.a),new T1(1,_4G.b));}}}},_4H=new T1(0,0),_4I=function(_4J,_4K){while(1){var _4L=E(_4J);if(!_4L._){_4J=new T1(1,I_fromInt(_4L.a));continue;}else{return new T1(1,I_shiftLeft(_4L.a,_4K));}}},_4M=function(_4N,_4O,_4P){if(!B(_4e(_4P,_4H))){var _4Q=B(_4y(_4O,_4P)),_4R=_4Q.a;switch(B(_31(B(_4I(_4Q.b,1)),_4P))){case 0:return new F(function(){return _4a(_4R,_4N);});break;case 1:if(!(B(_4m(_4R))&1)){return new F(function(){return _4a(_4R,_4N);});}else{return new F(function(){return _4a(B(_4p(_4R,_30)),_4N);});}break;default:return new F(function(){return _4a(B(_4p(_4R,_30)),_4N);});}}else{return E(_49);}},_4S=function(_4T,_4U){var _4V=E(_4T);if(!_4V._){var _4W=_4V.a,_4X=E(_4U);return (_4X._==0)?_4W>_4X.a:I_compareInt(_4X.a,_4W)<0;}else{var _4Y=_4V.a,_4Z=E(_4U);return (_4Z._==0)?I_compareInt(_4Y,_4Z.a)>0:I_compare(_4Y,_4Z.a)>0;}},_50=new T1(0,1),_51=function(_52,_53){var _54=E(_52);if(!_54._){var _55=_54.a,_56=E(_53);return (_56._==0)?_55<_56.a:I_compareInt(_56.a,_55)>0;}else{var _57=_54.a,_58=E(_53);return (_58._==0)?I_compareInt(_57,_58.a)<0:I_compare(_57,_58.a)<0;}},_59=new T(function(){return B(unCStr("base"));}),_5a=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5b=new T(function(){return B(unCStr("PatternMatchFail"));}),_5c=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_59,_5a,_5b),_5d=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5c,_T,_T),_5e=function(_5f){return E(_5d);},_5g=function(_5h){var _5i=E(_5h);return new F(function(){return _3m(B(_3k(_5i.a)),_5e,_5i.b);});},_5j=function(_5k){return E(E(_5k).a);},_5l=function(_5m){return new T2(0,_5n,_5m);},_5o=function(_5p,_5q){return new F(function(){return _14(E(_5p).a,_5q);});},_5r=function(_5s,_5t){return new F(function(){return _3P(_5o,_5s,_5t);});},_5u=function(_5v,_5w,_5x){return new F(function(){return _14(E(_5w).a,_5x);});},_5y=new T3(0,_5u,_5j,_5r),_5n=new T(function(){return new T5(0,_5e,_5y,_5l,_5g,_5j);}),_5z=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5A=function(_5B){return E(E(_5B).c);},_5C=function(_5D,_5E){return new F(function(){return die(new T(function(){return B(A2(_5A,_5E,_5D));}));});},_5F=function(_5G,_46){return new F(function(){return _5C(_5G,_46);});},_5H=function(_5I,_5J){var _5K=E(_5J);if(!_5K._){return new T2(0,_T,_T);}else{var _5L=_5K.a;if(!B(A1(_5I,_5L))){return new T2(0,_T,_5K);}else{var _5M=new T(function(){var _5N=B(_5H(_5I,_5K.b));return new T2(0,_5N.a,_5N.b);});return new T2(0,new T2(1,_5L,new T(function(){return E(E(_5M).a);})),new T(function(){return E(E(_5M).b);}));}}},_5O=32,_5P=new T(function(){return B(unCStr("\n"));}),_5Q=function(_5R){return (E(_5R)==124)?false:true;},_5S=function(_5T,_5U){var _5V=B(_5H(_5Q,B(unCStr(_5T)))),_5W=_5V.a,_5X=function(_5Y,_5Z){var _60=new T(function(){var _61=new T(function(){return B(_14(_5U,new T(function(){return B(_14(_5Z,_5P));},1)));});return B(unAppCStr(": ",_61));},1);return new F(function(){return _14(_5Y,_60);});},_62=E(_5V.b);if(!_62._){return new F(function(){return _5X(_5W,_T);});}else{if(E(_62.a)==124){return new F(function(){return _5X(_5W,new T2(1,_5O,_62.b));});}else{return new F(function(){return _5X(_5W,_T);});}}},_63=function(_64){return new F(function(){return _5F(new T1(0,new T(function(){return B(_5S(_64,_5z));})),_5n);});},_65=function(_66){var _67=function(_68,_69){while(1){if(!B(_51(_68,_66))){if(!B(_4S(_68,_66))){if(!B(_4e(_68,_66))){return new F(function(){return _63("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_69);}}else{return _69-1|0;}}else{var _6a=B(_4I(_68,1)),_6b=_69+1|0;_68=_6a;_69=_6b;continue;}}};return new F(function(){return _67(_50,0);});},_6c=function(_6d){var _6e=E(_6d);if(!_6e._){var _6f=_6e.a>>>0;if(!_6f){return -1;}else{var _6g=function(_6h,_6i){while(1){if(_6h>=_6f){if(_6h<=_6f){if(_6h!=_6f){return new F(function(){return _63("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6i);}}else{return _6i-1|0;}}else{var _6j=imul(_6h,2)>>>0,_6k=_6i+1|0;_6h=_6j;_6i=_6k;continue;}}};return new F(function(){return _6g(1,0);});}}else{return new F(function(){return _65(_6e);});}},_6l=function(_6m){var _6n=E(_6m);if(!_6n._){var _6o=_6n.a>>>0;if(!_6o){return new T2(0,-1,0);}else{var _6p=function(_6q,_6r){while(1){if(_6q>=_6o){if(_6q<=_6o){if(_6q!=_6o){return new F(function(){return _63("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6r);}}else{return _6r-1|0;}}else{var _6s=imul(_6q,2)>>>0,_6t=_6r+1|0;_6q=_6s;_6r=_6t;continue;}}};return new T2(0,B(_6p(1,0)),(_6o&_6o-1>>>0)>>>0&4294967295);}}else{var _6u=_6n.a;return new T2(0,B(_6c(_6n)),I_compareInt(I_and(_6u,I_sub(_6u,I_fromInt(1))),0));}},_6v=function(_6w,_6x){var _6y=E(_6w);if(!_6y._){var _6z=_6y.a,_6A=E(_6x);return (_6A._==0)?_6z<=_6A.a:I_compareInt(_6A.a,_6z)>=0;}else{var _6B=_6y.a,_6C=E(_6x);return (_6C._==0)?I_compareInt(_6B,_6C.a)<=0:I_compare(_6B,_6C.a)<=0;}},_6D=function(_6E,_6F){while(1){var _6G=E(_6E);if(!_6G._){var _6H=_6G.a,_6I=E(_6F);if(!_6I._){return new T1(0,(_6H>>>0&_6I.a>>>0)>>>0&4294967295);}else{_6E=new T1(1,I_fromInt(_6H));_6F=_6I;continue;}}else{var _6J=E(_6F);if(!_6J._){_6E=_6G;_6F=new T1(1,I_fromInt(_6J.a));continue;}else{return new T1(1,I_and(_6G.a,_6J.a));}}}},_6K=function(_6L,_6M){while(1){var _6N=E(_6L);if(!_6N._){var _6O=_6N.a,_6P=E(_6M);if(!_6P._){var _6Q=_6P.a,_6R=subC(_6O,_6Q);if(!E(_6R.b)){return new T1(0,_6R.a);}else{_6L=new T1(1,I_fromInt(_6O));_6M=new T1(1,I_fromInt(_6Q));continue;}}else{_6L=new T1(1,I_fromInt(_6O));_6M=_6P;continue;}}else{var _6S=E(_6M);if(!_6S._){_6L=_6N;_6M=new T1(1,I_fromInt(_6S.a));continue;}else{return new T1(1,I_sub(_6N.a,_6S.a));}}}},_6T=new T1(0,2),_6U=function(_6V,_6W){var _6X=E(_6V);if(!_6X._){var _6Y=(_6X.a>>>0&(2<<_6W>>>0)-1>>>0)>>>0,_6Z=1<<_6W>>>0;return (_6Z<=_6Y)?(_6Z>=_6Y)?1:2:0;}else{var _70=B(_6D(_6X,B(_6K(B(_4I(_6T,_6W)),_50)))),_71=B(_4I(_50,_6W));return (!B(_4S(_71,_70)))?(!B(_51(_71,_70)))?1:2:0;}},_72=function(_73,_74){while(1){var _75=E(_73);if(!_75._){_73=new T1(1,I_fromInt(_75.a));continue;}else{return new T1(1,I_shiftRight(_75.a,_74));}}},_76=function(_77,_78,_79,_7a){var _7b=B(_6l(_7a)),_7c=_7b.a;if(!E(_7b.b)){var _7d=B(_6c(_79));if(_7d<((_7c+_77|0)-1|0)){var _7e=_7c+(_77-_78|0)|0;if(_7e>0){if(_7e>_7d){if(_7e<=(_7d+1|0)){if(!E(B(_6l(_79)).b)){return 0;}else{return new F(function(){return _4a(_30,_77-_78|0);});}}else{return 0;}}else{var _7f=B(_72(_79,_7e));switch(B(_6U(_79,_7e-1|0))){case 0:return new F(function(){return _4a(_7f,_77-_78|0);});break;case 1:if(!(B(_4m(_7f))&1)){return new F(function(){return _4a(_7f,_77-_78|0);});}else{return new F(function(){return _4a(B(_4p(_7f,_30)),_77-_78|0);});}break;default:return new F(function(){return _4a(B(_4p(_7f,_30)),_77-_78|0);});}}}else{return new F(function(){return _4a(_79,(_77-_78|0)-_7e|0);});}}else{if(_7d>=_78){var _7g=B(_72(_79,(_7d+1|0)-_78|0));switch(B(_6U(_79,_7d-_78|0))){case 0:return new F(function(){return _4a(_7g,((_7d-_7c|0)+1|0)-_78|0);});break;case 2:return new F(function(){return _4a(B(_4p(_7g,_30)),((_7d-_7c|0)+1|0)-_78|0);});break;default:if(!(B(_4m(_7g))&1)){return new F(function(){return _4a(_7g,((_7d-_7c|0)+1|0)-_78|0);});}else{return new F(function(){return _4a(B(_4p(_7g,_30)),((_7d-_7c|0)+1|0)-_78|0);});}}}else{return new F(function(){return _4a(_79, -_7c);});}}}else{var _7h=B(_6c(_79))-_7c|0,_7i=function(_7j){var _7k=function(_7l,_7m){if(!B(_6v(B(_4I(_7m,_78)),_7l))){return new F(function(){return _4M(_7j-_78|0,_7l,_7m);});}else{return new F(function(){return _4M((_7j-_78|0)+1|0,_7l,B(_4I(_7m,1)));});}};if(_7j>=_78){if(_7j!=_78){return new F(function(){return _7k(_79,new T(function(){return B(_4I(_7a,_7j-_78|0));}));});}else{return new F(function(){return _7k(_79,_7a);});}}else{return new F(function(){return _7k(new T(function(){return B(_4I(_79,_78-_7j|0));}),_7a);});}};if(_77>_7h){return new F(function(){return _7i(_77);});}else{return new F(function(){return _7i(_7h);});}}},_7n=new T1(0,2147483647),_7o=new T(function(){return B(_4p(_7n,_50));}),_7p=function(_7q){var _7r=E(_7q);if(!_7r._){var _7s=E(_7r.a);return (_7s==(-2147483648))?E(_7o):new T1(0, -_7s);}else{return new T1(1,I_negate(_7r.a));}},_7t=new T(function(){return 0/0;}),_7u=new T(function(){return -1/0;}),_7v=new T(function(){return 1/0;}),_7w=0,_7x=function(_7y,_7z){if(!B(_4e(_7z,_4H))){if(!B(_4e(_7y,_4H))){if(!B(_51(_7y,_4H))){return new F(function(){return _76(-1021,53,_7y,_7z);});}else{return  -B(_76(-1021,53,B(_7p(_7y)),_7z));}}else{return E(_7w);}}else{return (!B(_4e(_7y,_4H)))?(!B(_51(_7y,_4H)))?E(_7v):E(_7u):E(_7t);}},_7A=function(_7B){return new T1(0,new T(function(){var _7C=E(_7B),_7D=jsShow(B(_7x(_7C.a,_7C.b)));return fromJSStr(_7D);}));},_7E=new T(function(){return B(unCStr("1./("));}),_7F=new T1(0,_7E),_7G=function(_7H){return new T1(1,new T2(1,_7F,new T2(1,_7H,_1K)));},_7I=new T(function(){return B(unCStr(")+("));}),_7J=new T1(0,_7I),_7K=function(_7L,_7M){return new T1(1,new T2(1,_2U,new T2(1,_7L,new T2(1,_7J,new T2(1,_7M,_1K)))));},_7N=new T(function(){return B(unCStr("-("));}),_7O=new T1(0,_7N),_7P=function(_7Q){return new T1(1,new T2(1,_7O,new T2(1,_7Q,_1K)));},_7R=new T(function(){return B(unCStr(")*("));}),_7S=new T1(0,_7R),_7T=function(_7U,_7V){return new T1(1,new T2(1,_2U,new T2(1,_7U,new T2(1,_7S,new T2(1,_7V,_1K)))));},_7W=function(_7X){return E(E(_7X).a);},_7Y=function(_7Z){return E(E(_7Z).d);},_80=function(_81,_82){return new F(function(){return A3(_7W,_83,_81,new T(function(){return B(A2(_7Y,_83,_82));}));});},_84=new T(function(){return B(unCStr("abs("));}),_85=new T1(0,_84),_86=function(_87){return new T1(1,new T2(1,_85,new T2(1,_87,_1K)));},_88=function(_89){while(1){var _8a=E(_89);if(!_8a._){_89=new T1(1,I_fromInt(_8a.a));continue;}else{return new F(function(){return I_toString(_8a.a);});}}},_8b=function(_8c,_8d){return new F(function(){return _14(fromJSStr(B(_88(_8c))),_8d);});},_8e=41,_8f=40,_8g=new T1(0,0),_8h=function(_8i,_8j,_8k){if(_8i<=6){return new F(function(){return _8b(_8j,_8k);});}else{if(!B(_51(_8j,_8g))){return new F(function(){return _8b(_8j,_8k);});}else{return new T2(1,_8f,new T(function(){return B(_14(fromJSStr(B(_88(_8j))),new T2(1,_8e,_8k)));}));}}},_8l=new T(function(){return B(unCStr("."));}),_8m=function(_8n){return new T1(0,new T(function(){return B(_14(B(_8h(0,_8n,_T)),_8l));}));},_8o=new T(function(){return B(unCStr("sign("));}),_8p=new T1(0,_8o),_8q=function(_8r){return new T1(1,new T2(1,_8p,new T2(1,_8r,_1K)));},_83=new T(function(){return {_:0,a:_7K,b:_80,c:_7T,d:_7P,e:_86,f:_8q,g:_8m};}),_8s=new T4(0,_83,_2X,_7G,_7A),_8t={_:0,a:_8s,b:_2y,c:_2m,d:_2q,e:_2J,f:_1L,g:_2u,h:_2B,i:_2e,j:_2N,k:_1Y,l:_1Q,m:_26,n:_2F,o:_2i,p:_2R,q:_22,r:_1U,s:_2a},_8u=function(_8v){return E(E(_8v).a);},_8w=function(_8x){return E(E(_8x).a);},_8y=function(_8z){return E(E(_8z).c);},_8A=function(_8B){return E(E(_8B).b);},_8C=function(_8D){return E(E(_8D).d);},_8E=new T1(0,1),_8F=new T1(0,2),_8G=new T2(0,E(_8E),E(_8F)),_8H=new T1(0,5),_8I=new T1(0,4),_8J=new T2(0,E(_8I),E(_8H)),_8K=function(_8L){return E(E(_8L).e);},_8M=function(_8N,_8O,_8P,_8Q){var _8R=B(_8u(_8N)),_8S=B(_8w(_8R)),_8T=new T(function(){var _8U=new T(function(){var _8V=new T(function(){var _8W=new T(function(){var _8X=new T(function(){var _8Y=new T(function(){return B(A3(_7W,_8S,new T(function(){return B(A3(_8y,_8S,_8O,_8O));}),new T(function(){return B(A3(_8y,_8S,_8Q,_8Q));})));});return B(A2(_8K,_8N,_8Y));});return B(A3(_8A,_8S,_8X,new T(function(){return B(A2(_8C,_8R,_8J));})));});return B(A3(_8y,_8S,_8W,_8W));});return B(A3(_7W,_8S,_8V,new T(function(){return B(A3(_8y,_8S,_8P,_8P));})));});return B(A2(_8K,_8N,_8U));});return new F(function(){return A3(_8A,_8S,_8T,new T(function(){return B(A2(_8C,_8R,_8G));}));});},_8Z=new T(function(){return B(unCStr("z"));}),_90=new T1(0,_8Z),_91=new T(function(){return B(unCStr("y"));}),_92=new T1(0,_91),_93=new T(function(){return B(unCStr("x"));}),_94=new T1(0,_93),_95=new T(function(){return B(_8M(_8t,_94,_92,_90));}),_96=new T(function(){return toJSStr(B(_1o(_1D,_11,_95)));}),_97=function(_98,_99,_9a){var _9b=new T(function(){return B(_1k(_98));}),_9c=new T(function(){return B(_1m(_98));}),_9d=function(_9e){var _9f=E(_9e);if(!_9f._){return E(_9c);}else{return new F(function(){return A2(_9b,new T(function(){return B(_1o(_98,_99,_9f.a));}),new T(function(){return B(_9d(_9f.b));}));});}};return new F(function(){return _9d(_9a);});},_9g=new T3(0,_94,_92,_90),_9h=new T(function(){return B(unCStr("(/=) is not defined"));}),_9i=new T(function(){return B(err(_9h));}),_9j=new T(function(){return B(unCStr("(==) is not defined"));}),_9k=new T(function(){return B(err(_9j));}),_9l=new T2(0,_9k,_9i),_9m=new T(function(){return B(unCStr("(<) is not defined"));}),_9n=new T(function(){return B(err(_9m));}),_9o=new T(function(){return B(unCStr("(<=) is not defined"));}),_9p=new T(function(){return B(err(_9o));}),_9q=new T(function(){return B(unCStr("(>) is not defined"));}),_9r=new T(function(){return B(err(_9q));}),_9s=new T(function(){return B(unCStr("(>=) is not defined"));}),_9t=new T(function(){return B(err(_9s));}),_9u=new T(function(){return B(unCStr("compare is not defined"));}),_9v=new T(function(){return B(err(_9u));}),_9w=new T(function(){return B(unCStr("max("));}),_9x=new T1(0,_9w),_9y=function(_9z,_9A){return new T1(1,new T2(1,_9x,new T2(1,_9z,new T2(1,_1F,new T2(1,_9A,_1K)))));},_9B=new T(function(){return B(unCStr("min("));}),_9C=new T1(0,_9B),_9D=function(_9E,_9F){return new T1(1,new T2(1,_9C,new T2(1,_9E,new T2(1,_1F,new T2(1,_9F,_1K)))));},_9G={_:0,a:_9l,b:_9v,c:_9n,d:_9p,e:_9r,f:_9t,g:_9y,h:_9D},_9H=new T2(0,_8t,_9G),_9I=function(_9J,_9K){var _9L=E(_9J);return E(_9K);},_9M=function(_9N,_9O){var _9P=E(_9N),_9Q=E(_9O);return new T3(0,new T(function(){return B(A1(_9P.a,_9Q.a));}),new T(function(){return B(A1(_9P.b,_9Q.b));}),new T(function(){return B(A1(_9P.c,_9Q.c));}));},_9R=function(_9S){return new T3(0,_9S,_9S,_9S);},_9T=function(_9U,_9V){var _9W=E(_9V);return new T3(0,_9U,_9U,_9U);},_9X=function(_9Y,_9Z){var _a0=E(_9Z);return new T3(0,new T(function(){return B(A1(_9Y,_a0.a));}),new T(function(){return B(A1(_9Y,_a0.b));}),new T(function(){return B(A1(_9Y,_a0.c));}));},_a1=new T2(0,_9X,_9T),_a2=function(_a3,_a4){var _a5=E(_a3),_a6=E(_a4);return new T3(0,_a5.a,_a5.b,_a5.c);},_a7=new T5(0,_a1,_9R,_9M,_9I,_a2),_a8=new T1(0,0),_a9=function(_aa){return E(E(_aa).g);},_ab=function(_ac){return new T3(0,new T3(0,new T(function(){return B(A2(_a9,_ac,_8E));}),new T(function(){return B(A2(_a9,_ac,_a8));}),new T(function(){return B(A2(_a9,_ac,_a8));})),new T3(0,new T(function(){return B(A2(_a9,_ac,_a8));}),new T(function(){return B(A2(_a9,_ac,_8E));}),new T(function(){return B(A2(_a9,_ac,_a8));})),new T3(0,new T(function(){return B(A2(_a9,_ac,_a8));}),new T(function(){return B(A2(_a9,_ac,_a8));}),new T(function(){return B(A2(_a9,_ac,_8E));})));},_ad=function(_ae){var _af=B(_ab(_ae));return new T3(0,_af.a,_af.b,_af.c);},_ag=function(_ah){return E(E(_ah).a);},_ai=function(_aj){return E(E(_aj).f);},_ak=function(_al){return E(E(_al).b);},_am=function(_an){return E(E(_an).c);},_ao=function(_ap){return E(E(_ap).a);},_aq=function(_ar){return E(E(_ar).d);},_as=function(_at,_au,_av,_aw,_ax){var _ay=new T(function(){return E(E(E(_at).c).a);}),_az=new T(function(){var _aA=E(_at).a,_aB=new T(function(){var _aC=new T(function(){return B(_8u(_ay));}),_aD=new T(function(){return B(_8w(_aC));}),_aE=new T(function(){return B(A2(_aq,_ay,_au));}),_aF=new T(function(){return B(A3(_ai,_ay,_au,_aw));}),_aG=function(_aH,_aI){var _aJ=new T(function(){var _aK=new T(function(){return B(A3(_ak,_aC,new T(function(){return B(A3(_8y,_aD,_aw,_aH));}),_au));});return B(A3(_7W,_aD,_aK,new T(function(){return B(A3(_8y,_aD,_aI,_aE));})));});return new F(function(){return A3(_8y,_aD,_aF,_aJ);});};return B(A3(_ao,B(_ag(_aA)),_aG,_av));});return B(A3(_am,_aA,_aB,_ax));});return new T2(0,new T(function(){return B(A3(_ai,_ay,_au,_aw));}),_az);},_aL=function(_aM,_aN,_aO,_aP){var _aQ=E(_aO),_aR=E(_aP),_aS=B(_as(_aN,_aQ.a,_aQ.b,_aR.a,_aR.b));return new T2(0,_aS.a,_aS.b);},_aT=new T1(0,1),_aU=function(_aV){return E(E(_aV).l);},_aW=function(_aX,_aY,_aZ){var _b0=new T(function(){return E(E(E(_aX).c).a);}),_b1=new T(function(){var _b2=new T(function(){return B(_8u(_b0));}),_b3=new T(function(){var _b4=B(_8w(_b2)),_b5=new T(function(){var _b6=new T(function(){return B(A3(_8A,_b4,new T(function(){return B(A2(_a9,_b4,_aT));}),new T(function(){return B(A3(_8y,_b4,_aY,_aY));})));});return B(A2(_8K,_b0,_b6));});return B(A2(_7Y,_b4,_b5));});return B(A3(_ao,B(_ag(E(_aX).a)),function(_b7){return new F(function(){return A3(_ak,_b2,_b7,_b3);});},_aZ));});return new T2(0,new T(function(){return B(A2(_aU,_b0,_aY));}),_b1);},_b8=function(_b9,_ba,_bb){var _bc=E(_bb),_bd=B(_aW(_ba,_bc.a,_bc.b));return new T2(0,_bd.a,_bd.b);},_be=function(_bf){return E(E(_bf).r);},_bg=function(_bh,_bi,_bj){var _bk=new T(function(){return E(E(E(_bh).c).a);}),_bl=new T(function(){var _bm=new T(function(){return B(_8u(_bk));}),_bn=new T(function(){var _bo=new T(function(){var _bp=B(_8w(_bm));return B(A3(_8A,_bp,new T(function(){return B(A3(_8y,_bp,_bi,_bi));}),new T(function(){return B(A2(_a9,_bp,_aT));})));});return B(A2(_8K,_bk,_bo));});return B(A3(_ao,B(_ag(E(_bh).a)),function(_bq){return new F(function(){return A3(_ak,_bm,_bq,_bn);});},_bj));});return new T2(0,new T(function(){return B(A2(_be,_bk,_bi));}),_bl);},_br=function(_bs,_bt,_bu){var _bv=E(_bu),_bw=B(_bg(_bt,_bv.a,_bv.b));return new T2(0,_bw.a,_bw.b);},_bx=function(_by){return E(E(_by).k);},_bz=function(_bA,_bB,_bC){var _bD=new T(function(){return E(E(E(_bA).c).a);}),_bE=new T(function(){var _bF=new T(function(){return B(_8u(_bD));}),_bG=new T(function(){var _bH=new T(function(){var _bI=B(_8w(_bF));return B(A3(_8A,_bI,new T(function(){return B(A2(_a9,_bI,_aT));}),new T(function(){return B(A3(_8y,_bI,_bB,_bB));})));});return B(A2(_8K,_bD,_bH));});return B(A3(_ao,B(_ag(E(_bA).a)),function(_bJ){return new F(function(){return A3(_ak,_bF,_bJ,_bG);});},_bC));});return new T2(0,new T(function(){return B(A2(_bx,_bD,_bB));}),_bE);},_bK=function(_bL,_bM,_bN){var _bO=E(_bN),_bP=B(_bz(_bM,_bO.a,_bO.b));return new T2(0,_bP.a,_bP.b);},_bQ=function(_bR){return E(E(_bR).q);},_bS=function(_bT,_bU,_bV){var _bW=new T(function(){return E(E(E(_bT).c).a);}),_bX=new T(function(){var _bY=new T(function(){return B(_8u(_bW));}),_bZ=new T(function(){var _c0=new T(function(){var _c1=B(_8w(_bY));return B(A3(_7W,_c1,new T(function(){return B(A3(_8y,_c1,_bU,_bU));}),new T(function(){return B(A2(_a9,_c1,_aT));})));});return B(A2(_8K,_bW,_c0));});return B(A3(_ao,B(_ag(E(_bT).a)),function(_c2){return new F(function(){return A3(_ak,_bY,_c2,_bZ);});},_bV));});return new T2(0,new T(function(){return B(A2(_bQ,_bW,_bU));}),_bX);},_c3=function(_c4,_c5,_c6){var _c7=E(_c6),_c8=B(_bS(_c5,_c7.a,_c7.b));return new T2(0,_c8.a,_c8.b);},_c9=function(_ca){return E(E(_ca).m);},_cb=function(_cc,_cd,_ce){var _cf=new T(function(){return E(E(E(_cc).c).a);}),_cg=new T(function(){var _ch=new T(function(){return B(_8u(_cf));}),_ci=new T(function(){var _cj=B(_8w(_ch));return B(A3(_7W,_cj,new T(function(){return B(A2(_a9,_cj,_aT));}),new T(function(){return B(A3(_8y,_cj,_cd,_cd));})));});return B(A3(_ao,B(_ag(E(_cc).a)),function(_ck){return new F(function(){return A3(_ak,_ch,_ck,_ci);});},_ce));});return new T2(0,new T(function(){return B(A2(_c9,_cf,_cd));}),_cg);},_cl=function(_cm,_cn,_co){var _cp=E(_co),_cq=B(_cb(_cn,_cp.a,_cp.b));return new T2(0,_cq.a,_cq.b);},_cr=function(_cs){return E(E(_cs).s);},_ct=function(_cu,_cv,_cw){var _cx=new T(function(){return E(E(E(_cu).c).a);}),_cy=new T(function(){var _cz=new T(function(){return B(_8u(_cx));}),_cA=new T(function(){var _cB=B(_8w(_cz));return B(A3(_8A,_cB,new T(function(){return B(A2(_a9,_cB,_aT));}),new T(function(){return B(A3(_8y,_cB,_cv,_cv));})));});return B(A3(_ao,B(_ag(E(_cu).a)),function(_cC){return new F(function(){return A3(_ak,_cz,_cC,_cA);});},_cw));});return new T2(0,new T(function(){return B(A2(_cr,_cx,_cv));}),_cy);},_cD=function(_cE,_cF,_cG){var _cH=E(_cG),_cI=B(_ct(_cF,_cH.a,_cH.b));return new T2(0,_cI.a,_cI.b);},_cJ=function(_cK){return E(E(_cK).i);},_cL=function(_cM){return E(E(_cM).h);},_cN=function(_cO,_cP,_cQ){var _cR=new T(function(){return E(E(E(_cO).c).a);}),_cS=new T(function(){var _cT=new T(function(){return B(_8w(new T(function(){return B(_8u(_cR));})));}),_cU=new T(function(){return B(A2(_7Y,_cT,new T(function(){return B(A2(_cL,_cR,_cP));})));});return B(A3(_ao,B(_ag(E(_cO).a)),function(_cV){return new F(function(){return A3(_8y,_cT,_cV,_cU);});},_cQ));});return new T2(0,new T(function(){return B(A2(_cJ,_cR,_cP));}),_cS);},_cW=function(_cX,_cY,_cZ){var _d0=E(_cZ),_d1=B(_cN(_cY,_d0.a,_d0.b));return new T2(0,_d1.a,_d1.b);},_d2=function(_d3){return E(E(_d3).o);},_d4=function(_d5){return E(E(_d5).n);},_d6=function(_d7,_d8,_d9){var _da=new T(function(){return E(E(E(_d7).c).a);}),_db=new T(function(){var _dc=new T(function(){return B(_8w(new T(function(){return B(_8u(_da));})));}),_dd=new T(function(){return B(A2(_d4,_da,_d8));});return B(A3(_ao,B(_ag(E(_d7).a)),function(_de){return new F(function(){return A3(_8y,_dc,_de,_dd);});},_d9));});return new T2(0,new T(function(){return B(A2(_d2,_da,_d8));}),_db);},_df=function(_dg,_dh,_di){var _dj=E(_di),_dk=B(_d6(_dh,_dj.a,_dj.b));return new T2(0,_dk.a,_dk.b);},_dl=function(_dm){return E(E(_dm).c);},_dn=function(_do,_dp,_dq){var _dr=new T(function(){return E(E(E(_do).c).a);}),_ds=new T(function(){var _dt=new T(function(){return B(_8w(new T(function(){return B(_8u(_dr));})));}),_du=new T(function(){return B(A2(_dl,_dr,_dp));});return B(A3(_ao,B(_ag(E(_do).a)),function(_dv){return new F(function(){return A3(_8y,_dt,_dv,_du);});},_dq));});return new T2(0,new T(function(){return B(A2(_dl,_dr,_dp));}),_ds);},_dw=function(_dx,_dy,_dz){var _dA=E(_dz),_dB=B(_dn(_dy,_dA.a,_dA.b));return new T2(0,_dB.a,_dB.b);},_dC=function(_dD,_dE,_dF){var _dG=new T(function(){return E(E(E(_dD).c).a);}),_dH=new T(function(){var _dI=new T(function(){return B(_8u(_dG));}),_dJ=new T(function(){return B(_8w(_dI));}),_dK=new T(function(){return B(A3(_ak,_dI,new T(function(){return B(A2(_a9,_dJ,_aT));}),_dE));});return B(A3(_ao,B(_ag(E(_dD).a)),function(_dL){return new F(function(){return A3(_8y,_dJ,_dL,_dK);});},_dF));});return new T2(0,new T(function(){return B(A2(_aq,_dG,_dE));}),_dH);},_dM=function(_dN,_dO,_dP){var _dQ=E(_dP),_dR=B(_dC(_dO,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);},_dS=function(_dT,_dU,_dV,_dW){var _dX=new T(function(){return E(E(_dU).c);}),_dY=new T3(0,new T(function(){return E(E(_dU).a);}),new T(function(){return E(E(_dU).b);}),new T2(0,new T(function(){return E(E(_dX).a);}),new T(function(){return E(E(_dX).b);})));return new F(function(){return A3(_ak,_dT,new T(function(){var _dZ=E(_dW),_e0=B(_dC(_dY,_dZ.a,_dZ.b));return new T2(0,_e0.a,_e0.b);}),new T(function(){var _e1=E(_dV),_e2=B(_dC(_dY,_e1.a,_e1.b));return new T2(0,_e2.a,_e2.b);}));});},_e3=new T1(0,0),_e4=function(_e5){return E(E(_e5).b);},_e6=function(_e7){return E(E(_e7).b);},_e8=function(_e9){var _ea=new T(function(){return E(E(E(_e9).c).a);}),_eb=new T(function(){return B(A2(_e6,E(_e9).a,new T(function(){return B(A2(_a9,B(_8w(B(_8u(_ea)))),_e3));})));});return new T2(0,new T(function(){return B(_e4(_ea));}),_eb);},_ec=function(_ed,_ee){var _ef=B(_e8(_ee));return new T2(0,_ef.a,_ef.b);},_eg=function(_eh,_ei,_ej){var _ek=new T(function(){return E(E(E(_eh).c).a);}),_el=new T(function(){var _em=new T(function(){return B(_8w(new T(function(){return B(_8u(_ek));})));}),_en=new T(function(){return B(A2(_cJ,_ek,_ei));});return B(A3(_ao,B(_ag(E(_eh).a)),function(_eo){return new F(function(){return A3(_8y,_em,_eo,_en);});},_ej));});return new T2(0,new T(function(){return B(A2(_cL,_ek,_ei));}),_el);},_ep=function(_eq,_er,_es){var _et=E(_es),_eu=B(_eg(_er,_et.a,_et.b));return new T2(0,_eu.a,_eu.b);},_ev=function(_ew,_ex,_ey){var _ez=new T(function(){return E(E(E(_ew).c).a);}),_eA=new T(function(){var _eB=new T(function(){return B(_8w(new T(function(){return B(_8u(_ez));})));}),_eC=new T(function(){return B(A2(_d2,_ez,_ex));});return B(A3(_ao,B(_ag(E(_ew).a)),function(_eD){return new F(function(){return A3(_8y,_eB,_eD,_eC);});},_ey));});return new T2(0,new T(function(){return B(A2(_d4,_ez,_ex));}),_eA);},_eE=function(_eF,_eG,_eH){var _eI=E(_eH),_eJ=B(_ev(_eG,_eI.a,_eI.b));return new T2(0,_eJ.a,_eJ.b);},_eK=new T1(0,2),_eL=function(_eM,_eN,_eO){var _eP=new T(function(){return E(E(E(_eM).c).a);}),_eQ=new T(function(){var _eR=new T(function(){return B(_8u(_eP));}),_eS=new T(function(){return B(_8w(_eR));}),_eT=new T(function(){var _eU=new T(function(){return B(A3(_ak,_eR,new T(function(){return B(A2(_a9,_eS,_aT));}),new T(function(){return B(A2(_a9,_eS,_eK));})));});return B(A3(_ak,_eR,_eU,new T(function(){return B(A2(_8K,_eP,_eN));})));});return B(A3(_ao,B(_ag(E(_eM).a)),function(_eV){return new F(function(){return A3(_8y,_eS,_eV,_eT);});},_eO));});return new T2(0,new T(function(){return B(A2(_8K,_eP,_eN));}),_eQ);},_eW=function(_eX,_eY,_eZ){var _f0=E(_eZ),_f1=B(_eL(_eY,_f0.a,_f0.b));return new T2(0,_f1.a,_f1.b);},_f2=function(_f3){return E(E(_f3).j);},_f4=function(_f5,_f6,_f7){var _f8=new T(function(){return E(E(E(_f5).c).a);}),_f9=new T(function(){var _fa=new T(function(){return B(_8u(_f8));}),_fb=new T(function(){var _fc=new T(function(){return B(A2(_cJ,_f8,_f6));});return B(A3(_8y,B(_8w(_fa)),_fc,_fc));});return B(A3(_ao,B(_ag(E(_f5).a)),function(_fd){return new F(function(){return A3(_ak,_fa,_fd,_fb);});},_f7));});return new T2(0,new T(function(){return B(A2(_f2,_f8,_f6));}),_f9);},_fe=function(_ff,_fg,_fh){var _fi=E(_fh),_fj=B(_f4(_fg,_fi.a,_fi.b));return new T2(0,_fj.a,_fj.b);},_fk=function(_fl){return E(E(_fl).p);},_fm=function(_fn,_fo,_fp){var _fq=new T(function(){return E(E(E(_fn).c).a);}),_fr=new T(function(){var _fs=new T(function(){return B(_8u(_fq));}),_ft=new T(function(){var _fu=new T(function(){return B(A2(_d2,_fq,_fo));});return B(A3(_8y,B(_8w(_fs)),_fu,_fu));});return B(A3(_ao,B(_ag(E(_fn).a)),function(_fv){return new F(function(){return A3(_ak,_fs,_fv,_ft);});},_fp));});return new T2(0,new T(function(){return B(A2(_fk,_fq,_fo));}),_fr);},_fw=function(_fx,_fy,_fz){var _fA=E(_fz),_fB=B(_fm(_fy,_fA.a,_fA.b));return new T2(0,_fB.a,_fB.b);},_fC=function(_fD,_fE){return {_:0,a:_fD,b:new T(function(){return B(_ec(_fD,_fE));}),c:function(_fF){return new F(function(){return _dw(_fD,_fE,_fF);});},d:function(_fF){return new F(function(){return _dM(_fD,_fE,_fF);});},e:function(_fF){return new F(function(){return _eW(_fD,_fE,_fF);});},f:function(_fG,_fF){return new F(function(){return _aL(_fD,_fE,_fG,_fF);});},g:function(_fG,_fF){return new F(function(){return _dS(_fD,_fE,_fG,_fF);});},h:function(_fF){return new F(function(){return _ep(_fD,_fE,_fF);});},i:function(_fF){return new F(function(){return _cW(_fD,_fE,_fF);});},j:function(_fF){return new F(function(){return _fe(_fD,_fE,_fF);});},k:function(_fF){return new F(function(){return _bK(_fD,_fE,_fF);});},l:function(_fF){return new F(function(){return _b8(_fD,_fE,_fF);});},m:function(_fF){return new F(function(){return _cl(_fD,_fE,_fF);});},n:function(_fF){return new F(function(){return _eE(_fD,_fE,_fF);});},o:function(_fF){return new F(function(){return _df(_fD,_fE,_fF);});},p:function(_fF){return new F(function(){return _fw(_fD,_fE,_fF);});},q:function(_fF){return new F(function(){return _c3(_fD,_fE,_fF);});},r:function(_fF){return new F(function(){return _br(_fD,_fE,_fF);});},s:function(_fF){return new F(function(){return _cD(_fD,_fE,_fF);});}};},_fH=function(_fI,_fJ,_fK,_fL,_fM){var _fN=new T(function(){return B(_8u(new T(function(){return E(E(E(_fI).c).a);})));}),_fO=new T(function(){var _fP=E(_fI).a,_fQ=new T(function(){var _fR=new T(function(){return B(_8w(_fN));}),_fS=new T(function(){return B(A3(_8y,_fR,_fL,_fL));}),_fT=function(_fU,_fV){var _fW=new T(function(){return B(A3(_8A,_fR,new T(function(){return B(A3(_8y,_fR,_fU,_fL));}),new T(function(){return B(A3(_8y,_fR,_fJ,_fV));})));});return new F(function(){return A3(_ak,_fN,_fW,_fS);});};return B(A3(_ao,B(_ag(_fP)),_fT,_fK));});return B(A3(_am,_fP,_fQ,_fM));});return new T2(0,new T(function(){return B(A3(_ak,_fN,_fJ,_fL));}),_fO);},_fX=function(_fY,_fZ,_g0,_g1){var _g2=E(_g0),_g3=E(_g1),_g4=B(_fH(_fZ,_g2.a,_g2.b,_g3.a,_g3.b));return new T2(0,_g4.a,_g4.b);},_g5=function(_g6,_g7){var _g8=new T(function(){return B(_8u(new T(function(){return E(E(E(_g6).c).a);})));}),_g9=new T(function(){return B(A2(_e6,E(_g6).a,new T(function(){return B(A2(_a9,B(_8w(_g8)),_e3));})));});return new T2(0,new T(function(){return B(A2(_8C,_g8,_g7));}),_g9);},_ga=function(_gb,_gc,_gd){var _ge=B(_g5(_gc,_gd));return new T2(0,_ge.a,_ge.b);},_gf=function(_gg,_gh,_gi){var _gj=new T(function(){return B(_8u(new T(function(){return E(E(E(_gg).c).a);})));}),_gk=new T(function(){return B(_8w(_gj));}),_gl=new T(function(){var _gm=new T(function(){var _gn=new T(function(){return B(A3(_ak,_gj,new T(function(){return B(A2(_a9,_gk,_aT));}),new T(function(){return B(A3(_8y,_gk,_gh,_gh));})));});return B(A2(_7Y,_gk,_gn));});return B(A3(_ao,B(_ag(E(_gg).a)),function(_go){return new F(function(){return A3(_8y,_gk,_go,_gm);});},_gi));}),_gp=new T(function(){return B(A3(_ak,_gj,new T(function(){return B(A2(_a9,_gk,_aT));}),_gh));});return new T2(0,_gp,_gl);},_gq=function(_gr,_gs,_gt){var _gu=E(_gt),_gv=B(_gf(_gs,_gu.a,_gu.b));return new T2(0,_gv.a,_gv.b);},_gw=function(_gx,_gy){return new T4(0,_gx,function(_fG,_fF){return new F(function(){return _fX(_gx,_gy,_fG,_fF);});},function(_fF){return new F(function(){return _gq(_gx,_gy,_fF);});},function(_fF){return new F(function(){return _ga(_gx,_gy,_fF);});});},_gz=function(_gA,_gB,_gC,_gD,_gE){var _gF=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_gA).c).a);})));})));}),_gG=new T(function(){var _gH=E(_gA).a,_gI=new T(function(){var _gJ=function(_gK,_gL){return new F(function(){return A3(_7W,_gF,new T(function(){return B(A3(_8y,_gF,_gB,_gL));}),new T(function(){return B(A3(_8y,_gF,_gK,_gD));}));});};return B(A3(_ao,B(_ag(_gH)),_gJ,_gC));});return B(A3(_am,_gH,_gI,_gE));});return new T2(0,new T(function(){return B(A3(_8y,_gF,_gB,_gD));}),_gG);},_gM=function(_gN,_gO,_gP){var _gQ=E(_gO),_gR=E(_gP),_gS=B(_gz(_gN,_gQ.a,_gQ.b,_gR.a,_gR.b));return new T2(0,_gS.a,_gS.b);},_gT=function(_gU,_gV,_gW,_gX,_gY){var _gZ=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_gU).c).a);})));})));}),_h0=new T(function(){var _h1=E(_gU).a,_h2=new T(function(){return B(A3(_ao,B(_ag(_h1)),new T(function(){return B(_7W(_gZ));}),_gW));});return B(A3(_am,_h1,_h2,_gY));});return new T2(0,new T(function(){return B(A3(_7W,_gZ,_gV,_gX));}),_h0);},_h3=function(_h4,_h5,_h6){var _h7=E(_h5),_h8=E(_h6),_h9=B(_gT(_h4,_h7.a,_h7.b,_h8.a,_h8.b));return new T2(0,_h9.a,_h9.b);},_ha=function(_hb,_hc,_hd){var _he=B(_hf(_hb));return new F(function(){return A3(_7W,_he,_hc,new T(function(){return B(A2(_7Y,_he,_hd));}));});},_hg=function(_hh){return E(E(_hh).e);},_hi=function(_hj){return E(E(_hj).f);},_hk=function(_hl,_hm,_hn){var _ho=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_hl).c).a);})));})));}),_hp=new T(function(){var _hq=new T(function(){return B(A2(_hi,_ho,_hm));});return B(A3(_ao,B(_ag(E(_hl).a)),function(_hr){return new F(function(){return A3(_8y,_ho,_hr,_hq);});},_hn));});return new T2(0,new T(function(){return B(A2(_hg,_ho,_hm));}),_hp);},_hs=function(_ht,_hu){var _hv=E(_hu),_hw=B(_hk(_ht,_hv.a,_hv.b));return new T2(0,_hw.a,_hw.b);},_hx=function(_hy,_hz){var _hA=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_hy).c).a);})));})));}),_hB=new T(function(){return B(A2(_e6,E(_hy).a,new T(function(){return B(A2(_a9,_hA,_e3));})));});return new T2(0,new T(function(){return B(A2(_a9,_hA,_hz));}),_hB);},_hC=function(_hD,_hE){var _hF=B(_hx(_hD,_hE));return new T2(0,_hF.a,_hF.b);},_hG=function(_hH,_hI,_hJ){var _hK=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_hH).c).a);})));})));}),_hL=new T(function(){return B(A3(_ao,B(_ag(E(_hH).a)),new T(function(){return B(_7Y(_hK));}),_hJ));});return new T2(0,new T(function(){return B(A2(_7Y,_hK,_hI));}),_hL);},_hM=function(_hN,_hO){var _hP=E(_hO),_hQ=B(_hG(_hN,_hP.a,_hP.b));return new T2(0,_hQ.a,_hQ.b);},_hR=function(_hS,_hT){var _hU=new T(function(){return B(_8w(new T(function(){return B(_8u(new T(function(){return E(E(E(_hS).c).a);})));})));}),_hV=new T(function(){return B(A2(_e6,E(_hS).a,new T(function(){return B(A2(_a9,_hU,_e3));})));});return new T2(0,new T(function(){return B(A2(_hi,_hU,_hT));}),_hV);},_hW=function(_hX,_hY){var _hZ=B(_hR(_hX,E(_hY).a));return new T2(0,_hZ.a,_hZ.b);},_hf=function(_i0){return {_:0,a:function(_fG,_fF){return new F(function(){return _h3(_i0,_fG,_fF);});},b:function(_fG,_fF){return new F(function(){return _ha(_i0,_fG,_fF);});},c:function(_fG,_fF){return new F(function(){return _gM(_i0,_fG,_fF);});},d:function(_fF){return new F(function(){return _hM(_i0,_fF);});},e:function(_fF){return new F(function(){return _hs(_i0,_fF);});},f:function(_fF){return new F(function(){return _hW(_i0,_fF);});},g:function(_fF){return new F(function(){return _hC(_i0,_fF);});}};},_i1=function(_i2){var _i3=new T(function(){return E(E(_i2).a);}),_i4=new T3(0,_a7,_ad,new T2(0,_i3,new T(function(){return E(E(_i2).b);}))),_i5=new T(function(){return B(_fC(new T(function(){return B(_gw(new T(function(){return B(_hf(_i4));}),_i4));}),_i4));}),_i6=new T(function(){return B(_8w(new T(function(){return B(_8u(_i3));})));});return function(_i7){var _i8=E(_i7),_i9=B(_ab(_i6));return E(B(_8M(_i5,new T2(0,_i8.a,_i9.a),new T2(0,_i8.b,_i9.b),new T2(0,_i8.c,_i9.c))).b);};},_ia=new T(function(){return B(_i1(_9H));}),_ib=function(_ic,_id){var _ie=E(_id);return (_ie._==0)?__Z:new T2(1,_ic,new T2(1,_ie.a,new T(function(){return B(_ib(_ic,_ie.b));})));},_if=new T(function(){var _ig=B(A1(_ia,_9g));return new T2(1,_ig.a,new T(function(){return B(_ib(_1F,new T2(1,_ig.b,new T2(1,_ig.c,_T))));}));}),_ih=new T1(1,_if),_ii=new T2(1,_ih,_1K),_ij=new T(function(){return B(unCStr("vec3("));}),_ik=new T1(0,_ij),_il=new T2(1,_ik,_ii),_im=new T(function(){return toJSStr(B(_97(_1D,_11,_il)));}),_in=function(_io,_ip){while(1){var _iq=E(_io);if(!_iq._){return E(_ip);}else{var _ir=_ip+1|0;_io=_iq.b;_ip=_ir;continue;}}},_is=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_it=new T(function(){return B(err(_is));}),_iu=new T(function(){return B(unCStr("Negative exponent"));}),_iv=new T(function(){return B(err(_iu));}),_iw=function(_ix,_iy,_iz){while(1){if(!(_iy%2)){var _iA=_ix*_ix,_iB=quot(_iy,2);_ix=_iA;_iy=_iB;continue;}else{var _iC=E(_iy);if(_iC==1){return _ix*_iz;}else{var _iA=_ix*_ix,_iD=_ix*_iz;_ix=_iA;_iy=quot(_iC-1|0,2);_iz=_iD;continue;}}}},_iE=function(_iF,_iG){while(1){if(!(_iG%2)){var _iH=_iF*_iF,_iI=quot(_iG,2);_iF=_iH;_iG=_iI;continue;}else{var _iJ=E(_iG);if(_iJ==1){return E(_iF);}else{return new F(function(){return _iw(_iF*_iF,quot(_iJ-1|0,2),_iF);});}}}},_iK=function(_iL){var _iM=E(_iL);return new F(function(){return Math.log(_iM+(_iM+1)*Math.sqrt((_iM-1)/(_iM+1)));});},_iN=function(_iO){var _iP=E(_iO);return new F(function(){return Math.log(_iP+Math.sqrt(1+_iP*_iP));});},_iQ=function(_iR){var _iS=E(_iR);return 0.5*Math.log((1+_iS)/(1-_iS));},_iT=function(_iU,_iV){return Math.log(E(_iV))/Math.log(E(_iU));},_iW=3.141592653589793,_iX=function(_iY){var _iZ=E(_iY);return new F(function(){return _7x(_iZ.a,_iZ.b);});},_j0=function(_j1){return 1/E(_j1);},_j2=function(_j3){var _j4=E(_j3),_j5=E(_j4);return (_j5==0)?E(_7w):(_j5<=0)? -_j5:E(_j4);},_j6=function(_j7){var _j8=E(_j7);if(!_j8._){return _j8.a;}else{return new F(function(){return I_toNumber(_j8.a);});}},_j9=function(_ja){return new F(function(){return _j6(_ja);});},_jb=1,_jc=-1,_jd=function(_je){var _jf=E(_je);return (_jf<=0)?(_jf>=0)?E(_jf):E(_jc):E(_jb);},_jg=function(_jh,_ji){return E(_jh)-E(_ji);},_jj=function(_jk){return  -E(_jk);},_jl=function(_jm,_jn){return E(_jm)+E(_jn);},_jo=function(_jp,_jq){return E(_jp)*E(_jq);},_jr={_:0,a:_jl,b:_jg,c:_jo,d:_jj,e:_j2,f:_jd,g:_j9},_js=function(_jt,_ju){return E(_jt)/E(_ju);},_jv=new T4(0,_jr,_js,_j0,_iX),_jw=function(_jx){return new F(function(){return Math.acos(E(_jx));});},_jy=function(_jz){return new F(function(){return Math.asin(E(_jz));});},_jA=function(_jB){return new F(function(){return Math.atan(E(_jB));});},_jC=function(_jD){return new F(function(){return Math.cos(E(_jD));});},_jE=function(_jF){return new F(function(){return cosh(E(_jF));});},_jG=function(_jH){return new F(function(){return Math.exp(E(_jH));});},_jI=function(_jJ){return new F(function(){return Math.log(E(_jJ));});},_jK=function(_jL,_jM){return new F(function(){return Math.pow(E(_jL),E(_jM));});},_jN=function(_jO){return new F(function(){return Math.sin(E(_jO));});},_jP=function(_jQ){return new F(function(){return sinh(E(_jQ));});},_jR=function(_jS){return new F(function(){return Math.sqrt(E(_jS));});},_jT=function(_jU){return new F(function(){return Math.tan(E(_jU));});},_jV=function(_jW){return new F(function(){return tanh(E(_jW));});},_jX={_:0,a:_jv,b:_iW,c:_jG,d:_jI,e:_jR,f:_jK,g:_iT,h:_jN,i:_jC,j:_jT,k:_jy,l:_jw,m:_jA,n:_jP,o:_jE,p:_jV,q:_iN,r:_iK,s:_iQ},_jY=function(_jZ,_k0){return (E(_jZ)!=E(_k0))?true:false;},_k1=function(_k2,_k3){return E(_k2)==E(_k3);},_k4=new T2(0,_k1,_jY),_k5=function(_k6,_k7){return E(_k6)<E(_k7);},_k8=function(_k9,_ka){return E(_k9)<=E(_ka);},_kb=function(_kc,_kd){return E(_kc)>E(_kd);},_ke=function(_kf,_kg){return E(_kf)>=E(_kg);},_kh=function(_ki,_kj){var _kk=E(_ki),_kl=E(_kj);return (_kk>=_kl)?(_kk!=_kl)?2:1:0;},_km=function(_kn,_ko){var _kp=E(_kn),_kq=E(_ko);return (_kp>_kq)?E(_kp):E(_kq);},_kr=function(_ks,_kt){var _ku=E(_ks),_kv=E(_kt);return (_ku>_kv)?E(_kv):E(_ku);},_kw={_:0,a:_k4,b:_kh,c:_k5,d:_k8,e:_kb,f:_ke,g:_km,h:_kr},_kx=new T2(0,_jX,_kw),_ky=function(_kz,_kA,_kB,_kC,_kD,_kE,_kF){var _kG=B(_8w(B(_8u(_kz)))),_kH=new T(function(){return B(A3(_7W,_kG,new T(function(){return B(A3(_8y,_kG,_kA,_kD));}),new T(function(){return B(A3(_8y,_kG,_kB,_kE));})));});return new F(function(){return A3(_7W,_kG,_kH,new T(function(){return B(A3(_8y,_kG,_kC,_kF));}));});},_kI=function(_kJ,_kK,_kL,_kM){var _kN=new T(function(){return E(E(_kJ).a);}),_kO=new T(function(){return B(_8u(_kN));}),_kP=new T(function(){return B(A2(_8K,_kN,new T(function(){return B(_ky(_kN,_kK,_kL,_kM,_kK,_kL,_kM));})));});return new T3(0,new T(function(){return B(A3(_ak,_kO,_kK,_kP));}),new T(function(){return B(A3(_ak,_kO,_kL,_kP));}),new T(function(){return B(A3(_ak,_kO,_kM,_kP));}));},_kQ=function(_kR,_kS){var _kT=new T(function(){return E(E(_kR).a);}),_kU=new T(function(){return E(E(_kR).b);}),_kV=new T(function(){return B(A2(_i1,new T2(0,_kT,_kU),_kS));}),_kW=new T(function(){var _kX=E(_kV),_kY=B(_kI(new T2(0,_kT,_kU),_kX.a,_kX.b,_kX.c));return new T3(0,_kY.a,_kY.b,_kY.c);}),_kZ=new T(function(){var _l0=E(_kS),_l1=_l0.a,_l2=_l0.b,_l3=_l0.c,_l4=E(_kW),_l5=new T(function(){return B(_8u(_kT));}),_l6=new T(function(){return B(_8w(_l5));}),_l7=new T(function(){return B(_7W(_l6));}),_l8=new T(function(){return B(_7Y(_l6));}),_l9=new T(function(){return B(_8y(_l6));}),_la=new T(function(){var _lb=new T(function(){return B(A2(_8K,_kT,new T(function(){var _lc=E(_kV),_ld=_lc.a,_le=_lc.b,_lf=_lc.c;return B(_ky(_kT,_ld,_le,_lf,_ld,_le,_lf));})));});return B(A3(_ak,_l5,new T(function(){return B(_8M(_kT,_l1,_l2,_l3));}),_lb));}),_lg=new T(function(){var _lh=new T(function(){return B(A1(_l8,new T(function(){return B(A2(_l9,_l4.c,_la));})));});return B(A2(_l7,_l3,_lh));}),_li=new T(function(){var _lj=new T(function(){return B(A1(_l8,new T(function(){return B(A2(_l9,_l4.b,_la));})));});return B(A2(_l7,_l2,_lj));}),_lk=new T(function(){var _ll=new T(function(){return B(A1(_l8,new T(function(){return B(A2(_l9,_l4.a,_la));})));});return B(A2(_l7,_l1,_ll));});return new T3(0,_lk,_li,_lg);});return new T2(0,_kZ,_kW);},_lm=function(_ln,_lo,_lp,_lq,_lr,_ls,_lt){var _lu=new T(function(){return E(E(_ln).a);}),_lv=new T(function(){return B(_8w(new T(function(){return B(_8u(_lu));})));}),_lw=new T(function(){return B(_7W(_lv));}),_lx=new T(function(){return B(_7Y(_lv));}),_ly=new T(function(){return B(_8y(_lv));}),_lz=new T(function(){return B(_ky(_lu,_lr,_ls,_lt,_lo,_lp,_lq));}),_lA=new T(function(){var _lB=new T(function(){return B(A1(_lx,new T(function(){return B(A2(_ly,_lt,_lz));})));});return B(A2(_lw,_lq,_lB));}),_lC=new T(function(){var _lD=new T(function(){return B(A1(_lx,new T(function(){return B(A2(_ly,_ls,_lz));})));});return B(A2(_lw,_lp,_lD));}),_lE=new T(function(){var _lF=new T(function(){return B(A1(_lx,new T(function(){return B(A2(_ly,_lr,_lz));})));});return B(A2(_lw,_lo,_lF));});return new T3(0,_lE,_lC,_lA);},_lG=function(_lH){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_lH));}))));});},_lI=new T(function(){return B(_lG("$dOrd_s3Pn Ord a"));}),_lJ=function(_lK,_lL,_lM,_lN,_lO,_lP,_lQ){var _lR=new T(function(){return E(E(_lK).a);}),_lS=B(_lm(new T2(0,_lR,_lI),_lO,_lP,_lQ,_lL,_lM,_lN));return new F(function(){return _kI(new T2(0,_lR,_lI),_lS.a,_lS.b,_lS.c);});},_lT=function(_lU){return E(E(_lU).a);},_lV=function(_lW){return E(E(_lW).a);},_lX=function(_lY,_lZ,_m0,_m1){var _m2=new T(function(){var _m3=E(_m1),_m4=E(_m0),_m5=B(_lm(new T2(0,_lY,_lZ),_m3.a,_m3.b,_m3.c,_m4.a,_m4.b,_m4.c));return new T3(0,_m5.a,_m5.b,_m5.c);}),_m6=new T(function(){return B(A2(_8K,_lY,new T(function(){var _m7=E(_m2),_m8=_m7.a,_m9=_m7.b,_ma=_m7.c;return B(_ky(_lY,_m8,_m9,_ma,_m8,_m9,_ma));})));});if(!B(A3(_lV,B(_lT(_lZ)),_m6,new T(function(){return B(A2(_a9,B(_8w(B(_8u(_lY)))),_a8));})))){var _mb=E(_m2),_mc=B(_kI(new T2(0,_lY,_lZ),_mb.a,_mb.b,_mb.c)),_md=new T(function(){return B(_8y(new T(function(){return B(_8w(new T(function(){return B(_8u(_lY));})));})));}),_me=new T(function(){return B(A2(_8K,_lY,new T(function(){var _mf=E(_m1),_mg=_mf.a,_mh=_mf.b,_mi=_mf.c;return B(_ky(_lY,_mg,_mh,_mi,_mg,_mh,_mi));})));});return new T3(0,new T(function(){return B(A2(_md,_mc.a,_me));}),new T(function(){return B(A2(_md,_mc.b,_me));}),new T(function(){return B(A2(_md,_mc.c,_me));}));}else{var _mj=new T(function(){return B(A2(_a9,B(_8w(B(_8u(_lY)))),_a8));});return new T3(0,_mj,_mj,_mj);}},_mk=0,_ml=new T(function(){var _mm=eval("angleCount"),_mn=Number(_mm);return jsTrunc(_mn);}),_mo=new T(function(){return E(_ml);}),_mp=new T(function(){return B(unCStr(": empty list"));}),_mq=new T(function(){return B(unCStr("Prelude."));}),_mr=function(_ms){return new F(function(){return err(B(_14(_mq,new T(function(){return B(_14(_ms,_mp));},1))));});},_mt=new T(function(){return B(unCStr("head"));}),_mu=new T(function(){return B(_mr(_mt));}),_mv=function(_mw,_mx,_my){var _mz=E(_mw);if(!_mz._){return __Z;}else{var _mA=E(_mx);if(!_mA._){return __Z;}else{var _mB=_mA.a,_mC=E(_my);if(!_mC._){return __Z;}else{var _mD=E(_mC.a),_mE=_mD.a;return new F(function(){return _14(new T2(1,new T3(0,_mz.a,_mB,_mE),new T2(1,new T3(0,_mB,_mE,_mD.b),_T)),new T(function(){return B(_mv(_mz.b,_mA.b,_mC.b));},1));});}}}},_mF=new T(function(){return B(unCStr("tail"));}),_mG=new T(function(){return B(_mr(_mF));}),_mH=function(_mI,_mJ){var _mK=E(_mI);if(!_mK._){return __Z;}else{var _mL=E(_mJ);return (_mL._==0)?__Z:new T2(1,new T2(0,_mK.a,_mL.a),new T(function(){return B(_mH(_mK.b,_mL.b));}));}},_mM=function(_mN,_mO){var _mP=E(_mN);if(!_mP._){return __Z;}else{var _mQ=E(_mO);if(!_mQ._){return __Z;}else{var _mR=E(_mP.a),_mS=_mR.b,_mT=E(_mQ.a).b,_mU=new T(function(){var _mV=new T(function(){return B(_mH(_mT,new T(function(){var _mW=E(_mT);if(!_mW._){return E(_mG);}else{return E(_mW.b);}},1)));},1);return B(_mv(_mS,new T(function(){var _mX=E(_mS);if(!_mX._){return E(_mG);}else{return E(_mX.b);}},1),_mV));});return new F(function(){return _14(new T2(1,new T3(0,_mR.a,new T(function(){var _mY=E(_mS);if(!_mY._){return E(_mu);}else{return E(_mY.a);}}),new T(function(){var _mZ=E(_mT);if(!_mZ._){return E(_mu);}else{return E(_mZ.a);}})),_mU),new T(function(){return B(_mM(_mP.b,_mQ.b));},1));});}}},_n0=new T(function(){return E(_mo)-1;}),_n1=new T1(0,1),_n2=function(_n3,_n4){var _n5=E(_n4),_n6=new T(function(){var _n7=B(_8w(_n3)),_n8=B(_n2(_n3,B(A3(_7W,_n7,_n5,new T(function(){return B(A2(_a9,_n7,_n1));})))));return new T2(1,_n8.a,_n8.b);});return new T2(0,_n5,_n6);},_n9=function(_na){return E(E(_na).d);},_nb=new T1(0,2),_nc=function(_nd,_ne){var _nf=E(_ne);if(!_nf._){return __Z;}else{var _ng=_nf.a;return (!B(A1(_nd,_ng)))?__Z:new T2(1,_ng,new T(function(){return B(_nc(_nd,_nf.b));}));}},_nh=function(_ni,_nj,_nk,_nl){var _nm=B(_n2(_nj,_nk)),_nn=new T(function(){var _no=B(_8w(_nj)),_np=new T(function(){return B(A3(_ak,_nj,new T(function(){return B(A2(_a9,_no,_n1));}),new T(function(){return B(A2(_a9,_no,_nb));})));});return B(A3(_7W,_no,_nl,_np));});return new F(function(){return _nc(function(_nq){return new F(function(){return A3(_n9,_ni,_nq,_nn);});},new T2(1,_nm.a,_nm.b));});},_nr=new T(function(){return B(_nh(_kw,_jv,_mk,_n0));}),_ns=function(_nt,_nu){while(1){var _nv=E(_nt);if(!_nv._){return E(_nu);}else{_nt=_nv.b;_nu=_nv.a;continue;}}},_nw=new T(function(){return B(unCStr("last"));}),_nx=new T(function(){return B(_mr(_nw));}),_ny=function(_nz){return new F(function(){return _ns(_nz,_nx);});},_nA=function(_nB){return new F(function(){return _ny(E(_nB).b);});},_nC=function(_nD,_nE){var _nF=E(_nE);return (_nF._==0)?__Z:new T2(1,new T(function(){return B(A1(_nD,_nF.a));}),new T(function(){return B(_nC(_nD,_nF.b));}));},_nG=new T(function(){var _nH=eval("proceedCount"),_nI=Number(_nH);return jsTrunc(_nI);}),_nJ=new T(function(){return E(_nG);}),_nK=1,_nL=new T(function(){return B(_nh(_kw,_jv,_nK,_nJ));}),_nM=function(_nN,_nO,_nP,_nQ,_nR){var _nS=new T(function(){var _nT=new T(function(){var _nU=E(_nQ),_nV=_nU.a,_nW=_nU.b,_nX=_nU.c,_nY=E(_nR),_nZ=_nY.a,_o0=_nY.b,_o1=_nY.c;return new T3(0,new T(function(){return E(_nW)*E(_o1)-E(_o0)*E(_nX);}),new T(function(){return E(_nX)*E(_nZ)-E(_o1)*E(_nV);}),new T(function(){return E(_nV)*E(_o0)-E(_nZ)*E(_nW);}));}),_o2=function(_o3){var _o4=new T(function(){var _o5=E(_o3)/E(_mo);return (_o5+_o5)*3.141592653589793;}),_o6=new T(function(){return B(A1(_nN,_o4));}),_o7=new T(function(){var _o8=new T(function(){return E(_o4)+E(_nP);}),_o9=new T(function(){return E(_o6)/E(_nJ);}),_oa=function(_ob,_oc){var _od=E(_ob);if(!_od._){return new T2(0,_T,_oc);}else{var _oe=new T(function(){var _of=new T(function(){var _og=E(_oc),_oh=E(_og.a),_oi=E(_og.b);return new T3(0,new T(function(){return E(_oh.a)+E(_oi.a)*E(_o9);}),new T(function(){return E(_oh.b)+E(_oi.b)*E(_o9);}),new T(function(){return E(_oh.c)+E(_oi.c)*E(_o9);}));}),_oj=B(_kQ(_kx,_of)),_ok=_oj.a;return new T2(0,new T3(0,_ok,new T2(0,new T(function(){return E(_od.a)/E(_nJ);}),_o6),_o4),new T2(0,_ok,new T(function(){var _ol=E(_oj.b),_om=E(E(_oc).b),_on=B(_lJ(_kx,_ol.a,_ol.b,_ol.c,_om.a,_om.b,_om.c));return new T3(0,_on.a,_on.b,_on.c);})));}),_oo=new T(function(){var _op=B(_oa(_od.b,new T(function(){return E(E(_oe).b);})));return new T2(0,_op.a,_op.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oe).a);}),new T(function(){return E(E(_oo).a);})),new T(function(){return E(E(_oo).b);}));}},_oq=function(_or,_os,_ot){var _ou=E(_or);if(!_ou._){return new T2(0,_T,new T2(0,_os,_ot));}else{var _ov=new T(function(){var _ow=new T(function(){var _ox=E(_os),_oy=E(_ot);return new T3(0,new T(function(){return E(_ox.a)+E(_oy.a)*E(_o9);}),new T(function(){return E(_ox.b)+E(_oy.b)*E(_o9);}),new T(function(){return E(_ox.c)+E(_oy.c)*E(_o9);}));}),_oz=B(_kQ(_kx,_ow)),_oA=_oz.a;return new T2(0,new T3(0,_oA,new T2(0,new T(function(){return E(_ou.a)/E(_nJ);}),_o6),_o4),new T2(0,_oA,new T(function(){var _oB=E(_oz.b),_oC=E(_ot),_oD=B(_lJ(_kx,_oB.a,_oB.b,_oB.c,_oC.a,_oC.b,_oC.c));return new T3(0,_oD.a,_oD.b,_oD.c);})));}),_oE=new T(function(){var _oF=B(_oa(_ou.b,new T(function(){return E(E(_ov).b);})));return new T2(0,_oF.a,_oF.b);});return new T2(0,new T2(1,new T(function(){return E(E(_ov).a);}),new T(function(){return E(E(_oE).a);})),new T(function(){return E(E(_oE).b);}));}},_oG=new T(function(){var _oH=E(_nQ),_oI=E(_nT),_oJ=new T(function(){return Math.cos(E(_o8));}),_oK=new T(function(){return Math.sin(E(_o8));});return new T3(0,new T(function(){return E(_oH.a)*E(_oJ)+E(_oI.a)*E(_oK);}),new T(function(){return E(_oH.b)*E(_oJ)+E(_oI.b)*E(_oK);}),new T(function(){return E(_oH.c)*E(_oJ)+E(_oI.c)*E(_oK);}));});return E(B(_oq(_nL,_nO,_oG)).a);});return new T2(0,new T3(0,_nO,new T2(0,_mk,_o6),_o4),_o7);};return B(_nC(_o2,_nr));}),_oL=new T(function(){var _oM=new T(function(){var _oN=B(_14(_nS,new T2(1,new T(function(){var _oO=E(_nS);if(!_oO._){return E(_mu);}else{return E(_oO.a);}}),_T)));if(!_oN._){return E(_mG);}else{return E(_oN.b);}},1);return B(_mM(_nS,_oM));});return new T2(0,_oL,new T(function(){return B(_nC(_nA,_nS));}));},_oP=function(_oQ,_oR,_oS,_oT,_oU,_oV){var _oW=new T(function(){var _oX=B(_kQ(_kx,new T(function(){return E(E(_oT).a);})));return new T2(0,_oX.a,_oX.b);}),_oY=new T(function(){return E(E(_oW).b);}),_oZ=new T(function(){var _p0=E(_oY),_p1=E(_oV),_p2=B(_lJ(_kx,_p0.a,_p0.b,_p0.c,_p1.a,_p1.b,_p1.c));return new T3(0,_p2.a,_p2.b,_p2.c);}),_p3=new T(function(){return new T2(0,new T(function(){return E(E(_oW).a);}),E(_oT).b);}),_p4=new T(function(){var _p5=E(_p3),_p6=B(_nM(_oQ,_p5.a,_p5.b,_oZ,_oY));return new T2(0,_p6.a,_p6.b);}),_p7=new T(function(){var _p8=E(_oU);return new T2(0,new T(function(){var _p9=B(_lX(_jX,_kw,_oY,_p8.a));return new T3(0,_p9.a,_p9.b,_p9.c);}),_p8.b);});return {_:0,a:_oQ,b:_oR,c:_oS,d:_p3,e:_p7,f:_oZ,g:_oY,h:new T(function(){return E(E(_p4).a);}),i:new T(function(){return E(E(_p4).b);})};},_pa=-1,_pb=0.5,_pc=new T3(0,_mk,_pb,_pa),_pd=new T(function(){return 6.283185307179586/E(_mo);}),_pe=function(_pf,_pg,_ph,_pi,_pj){var _pk=function(_pl){var _pm=E(_pd),_pn=2+_pl|0,_po=_pn-1|0,_pp=(2+_pl)*(1+_pl),_pq=E(_nr);if(!_pq._){return _pm*0;}else{var _pr=_pq.a,_ps=_pq.b,_pt=B(A1(_pf,new T(function(){return 6.283185307179586*E(_pr)/E(_mo);}))),_pu=B(A1(_pf,new T(function(){return 6.283185307179586*(E(_pr)+1)/E(_mo);})));if(_pt!=_pu){if(_pn>=0){var _pv=E(_pn);if(!_pv){var _pw=function(_px,_py){while(1){var _pz=B((function(_pA,_pB){var _pC=E(_pA);if(!_pC._){return E(_pB);}else{var _pD=_pC.a,_pE=_pC.b,_pF=B(A1(_pf,new T(function(){return 6.283185307179586*E(_pD)/E(_mo);}))),_pG=B(A1(_pf,new T(function(){return 6.283185307179586*(E(_pD)+1)/E(_mo);})));if(_pF!=_pG){var _pH=_pB+0/(_pF-_pG)/_pp;_px=_pE;_py=_pH;return __continue;}else{if(_po>=0){var _pI=E(_po);if(!_pI){var _pH=_pB+_pn/_pp;_px=_pE;_py=_pH;return __continue;}else{var _pH=_pB+_pn*B(_iE(_pF,_pI))/_pp;_px=_pE;_py=_pH;return __continue;}}else{return E(_iv);}}}})(_px,_py));if(_pz!=__continue){return _pz;}}};return _pm*B(_pw(_ps,0/(_pt-_pu)/_pp));}else{var _pJ=function(_pK,_pL){while(1){var _pM=B((function(_pN,_pO){var _pP=E(_pN);if(!_pP._){return E(_pO);}else{var _pQ=_pP.a,_pR=_pP.b,_pS=B(A1(_pf,new T(function(){return 6.283185307179586*E(_pQ)/E(_mo);}))),_pT=B(A1(_pf,new T(function(){return 6.283185307179586*(E(_pQ)+1)/E(_mo);})));if(_pS!=_pT){if(_pv>=0){var _pU=_pO+(B(_iE(_pS,_pv))-B(_iE(_pT,_pv)))/(_pS-_pT)/_pp;_pK=_pR;_pL=_pU;return __continue;}else{return E(_iv);}}else{if(_po>=0){var _pV=E(_po);if(!_pV){var _pU=_pO+_pn/_pp;_pK=_pR;_pL=_pU;return __continue;}else{var _pU=_pO+_pn*B(_iE(_pS,_pV))/_pp;_pK=_pR;_pL=_pU;return __continue;}}else{return E(_iv);}}}})(_pK,_pL));if(_pM!=__continue){return _pM;}}};return _pm*B(_pJ(_ps,(B(_iE(_pt,_pv))-B(_iE(_pu,_pv)))/(_pt-_pu)/_pp));}}else{return E(_iv);}}else{if(_po>=0){var _pW=E(_po);if(!_pW){var _pX=function(_pY,_pZ){while(1){var _q0=B((function(_q1,_q2){var _q3=E(_q1);if(!_q3._){return E(_q2);}else{var _q4=_q3.a,_q5=_q3.b,_q6=B(A1(_pf,new T(function(){return 6.283185307179586*E(_q4)/E(_mo);}))),_q7=B(A1(_pf,new T(function(){return 6.283185307179586*(E(_q4)+1)/E(_mo);})));if(_q6!=_q7){if(_pn>=0){var _q8=E(_pn);if(!_q8){var _q9=_q2+0/(_q6-_q7)/_pp;_pY=_q5;_pZ=_q9;return __continue;}else{var _q9=_q2+(B(_iE(_q6,_q8))-B(_iE(_q7,_q8)))/(_q6-_q7)/_pp;_pY=_q5;_pZ=_q9;return __continue;}}else{return E(_iv);}}else{var _q9=_q2+_pn/_pp;_pY=_q5;_pZ=_q9;return __continue;}}})(_pY,_pZ));if(_q0!=__continue){return _q0;}}};return _pm*B(_pX(_ps,_pn/_pp));}else{var _qa=function(_qb,_qc){while(1){var _qd=B((function(_qe,_qf){var _qg=E(_qe);if(!_qg._){return E(_qf);}else{var _qh=_qg.a,_qi=_qg.b,_qj=B(A1(_pf,new T(function(){return 6.283185307179586*E(_qh)/E(_mo);}))),_qk=B(A1(_pf,new T(function(){return 6.283185307179586*(E(_qh)+1)/E(_mo);})));if(_qj!=_qk){if(_pn>=0){var _ql=E(_pn);if(!_ql){var _qm=_qf+0/(_qj-_qk)/_pp;_qb=_qi;_qc=_qm;return __continue;}else{var _qm=_qf+(B(_iE(_qj,_ql))-B(_iE(_qk,_ql)))/(_qj-_qk)/_pp;_qb=_qi;_qc=_qm;return __continue;}}else{return E(_iv);}}else{if(_pW>=0){var _qm=_qf+_pn*B(_iE(_qj,_pW))/_pp;_qb=_qi;_qc=_qm;return __continue;}else{return E(_iv);}}}})(_qb,_qc));if(_qd!=__continue){return _qd;}}};return _pm*B(_qa(_ps,_pn*B(_iE(_pt,_pW))/_pp));}}else{return E(_iv);}}}},_qn=new T(function(){return 1/(B(_pk(1))*E(_pg));});return new F(function(){return _oP(_pf,_pc,new T2(0,new T3(0,_qn,_qn,_qn),new T(function(){return 1/(B(_pk(3))*E(_pg));})),_ph,_pi,_pj);});},_qo=1.2,_qp=-0.2,_qq=1,_qr=0,_qs=new T3(0,_qp,_qr,_qq),_qt=new T2(0,_qs,_qr),_qu=0.5,_qv=-0.8,_qw=new T3(0,_qv,_qu,_qr),_qx=new T2(0,_qw,_qr),_qy=0.2,_qz=function(_qA){return E(_qy);},_qB=new T3(0,_qr,_qr,_qq),_qC=new T(function(){var _qD=B(_pe(_qz,_qo,_qx,_qt,_qB));return {_:0,a:_qD.a,b:_qD.b,c:_qD.c,d:_qD.d,e:_qD.e,f:_qD.f,g:_qD.g,h:_qD.h,i:_qD.i};}),_qE=0,_qF=1.3,_qG=new T3(0,_qF,_qr,_qr),_qH=new T2(0,_qG,_qr),_qI=function(_qJ){var _qK=I_decodeDouble(_qJ);return new T2(0,new T1(1,_qK.b),_qK.a);},_qL=function(_qM){return new T1(0,_qM);},_qN=function(_qO){var _qP=hs_intToInt64(2147483647),_qQ=hs_leInt64(_qO,_qP);if(!_qQ){return new T1(1,I_fromInt64(_qO));}else{var _qR=hs_intToInt64(-2147483648),_qS=hs_geInt64(_qO,_qR);if(!_qS){return new T1(1,I_fromInt64(_qO));}else{var _qT=hs_int64ToInt(_qO);return new F(function(){return _qL(_qT);});}}},_qU=new T(function(){var _qV=newByteArr(256),_qW=_qV,_=_qW["v"]["i8"][0]=8,_qX=function(_qY,_qZ,_r0,_){while(1){if(_r0>=256){if(_qY>=256){return E(_);}else{var _r1=imul(2,_qY)|0,_r2=_qZ+1|0,_r3=_qY;_qY=_r1;_qZ=_r2;_r0=_r3;continue;}}else{var _=_qW["v"]["i8"][_r0]=_qZ,_r3=_r0+_qY|0;_r0=_r3;continue;}}},_=B(_qX(2,0,1,_));return _qW;}),_r4=function(_r5,_r6){var _r7=hs_int64ToInt(_r5),_r8=E(_qU),_r9=_r8["v"]["i8"][(255&_r7>>>0)>>>0&4294967295];if(_r6>_r9){if(_r9>=8){var _ra=hs_uncheckedIShiftRA64(_r5,8),_rb=function(_rc,_rd){while(1){var _re=B((function(_rf,_rg){var _rh=hs_int64ToInt(_rf),_ri=_r8["v"]["i8"][(255&_rh>>>0)>>>0&4294967295];if(_rg>_ri){if(_ri>=8){var _rj=hs_uncheckedIShiftRA64(_rf,8),_rk=_rg-8|0;_rc=_rj;_rd=_rk;return __continue;}else{return new T2(0,new T(function(){var _rl=hs_uncheckedIShiftRA64(_rf,_ri);return B(_qN(_rl));}),_rg-_ri|0);}}else{return new T2(0,new T(function(){var _rm=hs_uncheckedIShiftRA64(_rf,_rg);return B(_qN(_rm));}),0);}})(_rc,_rd));if(_re!=__continue){return _re;}}};return new F(function(){return _rb(_ra,_r6-8|0);});}else{return new T2(0,new T(function(){var _rn=hs_uncheckedIShiftRA64(_r5,_r9);return B(_qN(_rn));}),_r6-_r9|0);}}else{return new T2(0,new T(function(){var _ro=hs_uncheckedIShiftRA64(_r5,_r6);return B(_qN(_ro));}),0);}},_rp=function(_rq){var _rr=hs_intToInt64(_rq);return E(_rr);},_rs=function(_rt){var _ru=E(_rt);if(!_ru._){return new F(function(){return _rp(_ru.a);});}else{return new F(function(){return I_toInt64(_ru.a);});}},_rv=function(_rw){return I_toInt(_rw)>>>0;},_rx=function(_ry){var _rz=E(_ry);if(!_rz._){return _rz.a>>>0;}else{return new F(function(){return _rv(_rz.a);});}},_rA=function(_rB){var _rC=B(_qI(_rB)),_rD=_rC.a,_rE=_rC.b;if(_rE<0){var _rF=function(_rG){if(!_rG){return new T2(0,E(_rD),B(_4I(_30, -_rE)));}else{var _rH=B(_r4(B(_rs(_rD)), -_rE));return new T2(0,E(_rH.a),B(_4I(_30,_rH.b)));}};if(!((B(_rx(_rD))&1)>>>0)){return new F(function(){return _rF(1);});}else{return new F(function(){return _rF(0);});}}else{return new T2(0,B(_4I(_rD,_rE)),_30);}},_rI=function(_rJ){var _rK=B(_rA(E(_rJ)));return new T2(0,E(_rK.a),E(_rK.b));},_rL=new T3(0,_jr,_kw,_rI),_rM=function(_rN){return E(E(_rN).a);},_rO=function(_rP){return E(E(_rP).a);},_rQ=function(_rR,_rS){if(_rR<=_rS){var _rT=function(_rU){return new T2(1,_rU,new T(function(){if(_rU!=_rS){return B(_rT(_rU+1|0));}else{return __Z;}}));};return new F(function(){return _rT(_rR);});}else{return __Z;}},_rV=function(_rW){return new F(function(){return _rQ(E(_rW),2147483647);});},_rX=function(_rY,_rZ,_s0){if(_s0<=_rZ){var _s1=new T(function(){var _s2=_rZ-_rY|0,_s3=function(_s4){return (_s4>=(_s0-_s2|0))?new T2(1,_s4,new T(function(){return B(_s3(_s4+_s2|0));})):new T2(1,_s4,_T);};return B(_s3(_rZ));});return new T2(1,_rY,_s1);}else{return (_s0<=_rY)?new T2(1,_rY,_T):__Z;}},_s5=function(_s6,_s7,_s8){if(_s8>=_s7){var _s9=new T(function(){var _sa=_s7-_s6|0,_sb=function(_sc){return (_sc<=(_s8-_sa|0))?new T2(1,_sc,new T(function(){return B(_sb(_sc+_sa|0));})):new T2(1,_sc,_T);};return B(_sb(_s7));});return new T2(1,_s6,_s9);}else{return (_s8>=_s6)?new T2(1,_s6,_T):__Z;}},_sd=function(_se,_sf){if(_sf<_se){return new F(function(){return _rX(_se,_sf,-2147483648);});}else{return new F(function(){return _s5(_se,_sf,2147483647);});}},_sg=function(_sh,_si){return new F(function(){return _sd(E(_sh),E(_si));});},_sj=function(_sk,_sl,_sm){if(_sl<_sk){return new F(function(){return _rX(_sk,_sl,_sm);});}else{return new F(function(){return _s5(_sk,_sl,_sm);});}},_sn=function(_so,_sp,_sq){return new F(function(){return _sj(E(_so),E(_sp),E(_sq));});},_sr=function(_ss,_st){return new F(function(){return _rQ(E(_ss),E(_st));});},_su=function(_sv){return E(_sv);},_sw=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_sx=new T(function(){return B(err(_sw));}),_sy=function(_sz){var _sA=E(_sz);return (_sA==(-2147483648))?E(_sx):_sA-1|0;},_sB=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_sC=new T(function(){return B(err(_sB));}),_sD=function(_sE){var _sF=E(_sE);return (_sF==2147483647)?E(_sC):_sF+1|0;},_sG={_:0,a:_sD,b:_sy,c:_su,d:_su,e:_rV,f:_sg,g:_sr,h:_sn},_sH=function(_sI,_sJ){if(_sI<=0){if(_sI>=0){return new F(function(){return quot(_sI,_sJ);});}else{if(_sJ<=0){return new F(function(){return quot(_sI,_sJ);});}else{return quot(_sI+1|0,_sJ)-1|0;}}}else{if(_sJ>=0){if(_sI>=0){return new F(function(){return quot(_sI,_sJ);});}else{if(_sJ<=0){return new F(function(){return quot(_sI,_sJ);});}else{return quot(_sI+1|0,_sJ)-1|0;}}}else{return quot(_sI-1|0,_sJ)-1|0;}}},_sK=0,_sL=new T(function(){return B(_45(_sK));}),_sM=new T(function(){return die(_sL);}),_sN=function(_sO,_sP){var _sQ=E(_sP);switch(_sQ){case -1:var _sR=E(_sO);if(_sR==(-2147483648)){return E(_sM);}else{return new F(function(){return _sH(_sR,-1);});}break;case 0:return E(_49);default:return new F(function(){return _sH(_sO,_sQ);});}},_sS=function(_sT,_sU){return new F(function(){return _sN(E(_sT),E(_sU));});},_sV=0,_sW=new T2(0,_sM,_sV),_sX=function(_sY,_sZ){var _t0=E(_sY),_t1=E(_sZ);switch(_t1){case -1:var _t2=E(_t0);if(_t2==(-2147483648)){return E(_sW);}else{if(_t2<=0){if(_t2>=0){var _t3=quotRemI(_t2,-1);return new T2(0,_t3.a,_t3.b);}else{var _t4=quotRemI(_t2,-1);return new T2(0,_t4.a,_t4.b);}}else{var _t5=quotRemI(_t2-1|0,-1);return new T2(0,_t5.a-1|0,(_t5.b+(-1)|0)+1|0);}}break;case 0:return E(_49);default:if(_t0<=0){if(_t0>=0){var _t6=quotRemI(_t0,_t1);return new T2(0,_t6.a,_t6.b);}else{if(_t1<=0){var _t7=quotRemI(_t0,_t1);return new T2(0,_t7.a,_t7.b);}else{var _t8=quotRemI(_t0+1|0,_t1);return new T2(0,_t8.a-1|0,(_t8.b+_t1|0)-1|0);}}}else{if(_t1>=0){if(_t0>=0){var _t9=quotRemI(_t0,_t1);return new T2(0,_t9.a,_t9.b);}else{if(_t1<=0){var _ta=quotRemI(_t0,_t1);return new T2(0,_ta.a,_ta.b);}else{var _tb=quotRemI(_t0+1|0,_t1);return new T2(0,_tb.a-1|0,(_tb.b+_t1|0)-1|0);}}}else{var _tc=quotRemI(_t0-1|0,_t1);return new T2(0,_tc.a-1|0,(_tc.b+_t1|0)+1|0);}}}},_td=function(_te,_tf){var _tg=_te%_tf;if(_te<=0){if(_te>=0){return E(_tg);}else{if(_tf<=0){return E(_tg);}else{var _th=E(_tg);return (_th==0)?0:_th+_tf|0;}}}else{if(_tf>=0){if(_te>=0){return E(_tg);}else{if(_tf<=0){return E(_tg);}else{var _ti=E(_tg);return (_ti==0)?0:_ti+_tf|0;}}}else{var _tj=E(_tg);return (_tj==0)?0:_tj+_tf|0;}}},_tk=function(_tl,_tm){var _tn=E(_tm);switch(_tn){case -1:return E(_sV);case 0:return E(_49);default:return new F(function(){return _td(E(_tl),_tn);});}},_to=function(_tp,_tq){var _tr=E(_tp),_ts=E(_tq);switch(_ts){case -1:var _tt=E(_tr);if(_tt==(-2147483648)){return E(_sM);}else{return new F(function(){return quot(_tt,-1);});}break;case 0:return E(_49);default:return new F(function(){return quot(_tr,_ts);});}},_tu=function(_tv,_tw){var _tx=E(_tv),_ty=E(_tw);switch(_ty){case -1:var _tz=E(_tx);if(_tz==(-2147483648)){return E(_sW);}else{var _tA=quotRemI(_tz,-1);return new T2(0,_tA.a,_tA.b);}break;case 0:return E(_49);default:var _tB=quotRemI(_tx,_ty);return new T2(0,_tB.a,_tB.b);}},_tC=function(_tD,_tE){var _tF=E(_tE);switch(_tF){case -1:return E(_sV);case 0:return E(_49);default:return E(_tD)%_tF;}},_tG=function(_tH){return new F(function(){return _qL(E(_tH));});},_tI=function(_tJ){return new T2(0,E(B(_qL(E(_tJ)))),E(_n1));},_tK=function(_tL,_tM){return imul(E(_tL),E(_tM))|0;},_tN=function(_tO,_tP){return E(_tO)+E(_tP)|0;},_tQ=function(_tR,_tS){return E(_tR)-E(_tS)|0;},_tT=function(_tU){var _tV=E(_tU);return (_tV<0)? -_tV:E(_tV);},_tW=function(_tX){return new F(function(){return _4m(_tX);});},_tY=function(_tZ){return  -E(_tZ);},_u0=-1,_u1=0,_u2=1,_u3=function(_u4){var _u5=E(_u4);return (_u5>=0)?(E(_u5)==0)?E(_u1):E(_u2):E(_u0);},_u6={_:0,a:_tN,b:_tQ,c:_tK,d:_tY,e:_tT,f:_u3,g:_tW},_u7=function(_u8,_u9){return E(_u8)==E(_u9);},_ua=function(_ub,_uc){return E(_ub)!=E(_uc);},_ud=new T2(0,_u7,_ua),_ue=function(_uf,_ug){var _uh=E(_uf),_ui=E(_ug);return (_uh>_ui)?E(_uh):E(_ui);},_uj=function(_uk,_ul){var _um=E(_uk),_un=E(_ul);return (_um>_un)?E(_un):E(_um);},_uo=function(_up,_uq){return (_up>=_uq)?(_up!=_uq)?2:1:0;},_ur=function(_us,_ut){return new F(function(){return _uo(E(_us),E(_ut));});},_uu=function(_uv,_uw){return E(_uv)>=E(_uw);},_ux=function(_uy,_uz){return E(_uy)>E(_uz);},_uA=function(_uB,_uC){return E(_uB)<=E(_uC);},_uD=function(_uE,_uF){return E(_uE)<E(_uF);},_uG={_:0,a:_ud,b:_ur,c:_uD,d:_uA,e:_ux,f:_uu,g:_ue,h:_uj},_uH=new T3(0,_u6,_uG,_tI),_uI={_:0,a:_uH,b:_sG,c:_to,d:_tC,e:_sS,f:_tk,g:_tu,h:_sX,i:_tG},_uJ=new T1(0,2),_uK=function(_uL,_uM){while(1){var _uN=E(_uL);if(!_uN._){var _uO=_uN.a,_uP=E(_uM);if(!_uP._){var _uQ=_uP.a;if(!(imul(_uO,_uQ)|0)){return new T1(0,imul(_uO,_uQ)|0);}else{_uL=new T1(1,I_fromInt(_uO));_uM=new T1(1,I_fromInt(_uQ));continue;}}else{_uL=new T1(1,I_fromInt(_uO));_uM=_uP;continue;}}else{var _uR=E(_uM);if(!_uR._){_uL=_uN;_uM=new T1(1,I_fromInt(_uR.a));continue;}else{return new T1(1,I_mul(_uN.a,_uR.a));}}}},_uS=function(_uT,_uU,_uV){while(1){if(!(_uU%2)){var _uW=B(_uK(_uT,_uT)),_uX=quot(_uU,2);_uT=_uW;_uU=_uX;continue;}else{var _uY=E(_uU);if(_uY==1){return new F(function(){return _uK(_uT,_uV);});}else{var _uW=B(_uK(_uT,_uT)),_uZ=B(_uK(_uT,_uV));_uT=_uW;_uU=quot(_uY-1|0,2);_uV=_uZ;continue;}}}},_v0=function(_v1,_v2){while(1){if(!(_v2%2)){var _v3=B(_uK(_v1,_v1)),_v4=quot(_v2,2);_v1=_v3;_v2=_v4;continue;}else{var _v5=E(_v2);if(_v5==1){return E(_v1);}else{return new F(function(){return _uS(B(_uK(_v1,_v1)),quot(_v5-1|0,2),_v1);});}}}},_v6=function(_v7){return E(E(_v7).b);},_v8=function(_v9){return E(E(_v9).c);},_va=new T1(0,0),_vb=function(_vc){return E(E(_vc).d);},_vd=function(_ve,_vf){var _vg=B(_rM(_ve)),_vh=new T(function(){return B(_rO(_vg));}),_vi=new T(function(){return B(A3(_vb,_ve,_vf,new T(function(){return B(A2(_a9,_vh,_nb));})));});return new F(function(){return A3(_lV,B(_lT(B(_v6(_vg)))),_vi,new T(function(){return B(A2(_a9,_vh,_va));}));});},_vj=new T(function(){return B(unCStr("Negative exponent"));}),_vk=new T(function(){return B(err(_vj));}),_vl=function(_vm){return E(E(_vm).c);},_vn=function(_vo,_vp,_vq,_vr){var _vs=B(_rM(_vp)),_vt=new T(function(){return B(_rO(_vs));}),_vu=B(_v6(_vs));if(!B(A3(_v8,_vu,_vr,new T(function(){return B(A2(_a9,_vt,_va));})))){if(!B(A3(_lV,B(_lT(_vu)),_vr,new T(function(){return B(A2(_a9,_vt,_va));})))){var _vv=new T(function(){return B(A2(_a9,_vt,_nb));}),_vw=new T(function(){return B(A2(_a9,_vt,_n1));}),_vx=B(_lT(_vu)),_vy=function(_vz,_vA,_vB){while(1){var _vC=B((function(_vD,_vE,_vF){if(!B(_vd(_vp,_vE))){if(!B(A3(_lV,_vx,_vE,_vw))){var _vG=new T(function(){return B(A3(_vl,_vp,new T(function(){return B(A3(_8A,_vt,_vE,_vw));}),_vv));});_vz=new T(function(){return B(A3(_8y,_vo,_vD,_vD));});_vA=_vG;_vB=new T(function(){return B(A3(_8y,_vo,_vD,_vF));});return __continue;}else{return new F(function(){return A3(_8y,_vo,_vD,_vF);});}}else{var _vH=_vF;_vz=new T(function(){return B(A3(_8y,_vo,_vD,_vD));});_vA=new T(function(){return B(A3(_vl,_vp,_vE,_vv));});_vB=_vH;return __continue;}})(_vz,_vA,_vB));if(_vC!=__continue){return _vC;}}},_vI=function(_vJ,_vK){while(1){var _vL=B((function(_vM,_vN){if(!B(_vd(_vp,_vN))){if(!B(A3(_lV,_vx,_vN,_vw))){var _vO=new T(function(){return B(A3(_vl,_vp,new T(function(){return B(A3(_8A,_vt,_vN,_vw));}),_vv));});return new F(function(){return _vy(new T(function(){return B(A3(_8y,_vo,_vM,_vM));}),_vO,_vM);});}else{return E(_vM);}}else{_vJ=new T(function(){return B(A3(_8y,_vo,_vM,_vM));});_vK=new T(function(){return B(A3(_vl,_vp,_vN,_vv));});return __continue;}})(_vJ,_vK));if(_vL!=__continue){return _vL;}}};return new F(function(){return _vI(_vq,_vr);});}else{return new F(function(){return A2(_a9,_vo,_n1);});}}else{return E(_vk);}},_vP=new T(function(){return B(err(_vj));}),_vQ=function(_vR,_vS){var _vT=B(_qI(_vS)),_vU=_vT.a,_vV=_vT.b,_vW=new T(function(){return B(_rO(new T(function(){return B(_rM(_vR));})));});if(_vV<0){var _vX= -_vV;if(_vX>=0){var _vY=E(_vX);if(!_vY){var _vZ=E(_n1);}else{var _vZ=B(_v0(_uJ,_vY));}if(!B(_4e(_vZ,_4H))){var _w0=B(_4y(_vU,_vZ));return new T2(0,new T(function(){return B(A2(_a9,_vW,_w0.a));}),new T(function(){return B(_4a(_w0.b,_vV));}));}else{return E(_49);}}else{return E(_vP);}}else{var _w1=new T(function(){var _w2=new T(function(){return B(_vn(_vW,_uI,new T(function(){return B(A2(_a9,_vW,_uJ));}),_vV));});return B(A3(_8y,_vW,new T(function(){return B(A2(_a9,_vW,_vU));}),_w2));});return new T2(0,_w1,_7w);}},_w3=function(_w4,_w5){var _w6=B(_vQ(_w4,E(_w5))),_w7=_w6.a;if(E(_w6.b)<=0){return E(_w7);}else{var _w8=B(_rO(B(_rM(_w4))));return new F(function(){return A3(_7W,_w8,_w7,new T(function(){return B(A2(_a9,_w8,_30));}));});}},_w9=function(_wa,_wb){var _wc=B(_vQ(_wa,E(_wb))),_wd=_wc.a;if(E(_wc.b)>=0){return E(_wd);}else{var _we=B(_rO(B(_rM(_wa))));return new F(function(){return A3(_8A,_we,_wd,new T(function(){return B(A2(_a9,_we,_30));}));});}},_wf=function(_wg,_wh){var _wi=B(_vQ(_wg,E(_wh)));return new T2(0,_wi.a,_wi.b);},_wj=function(_wk,_wl){var _wm=B(_vQ(_wk,_wl)),_wn=_wm.a,_wo=E(_wm.b),_wp=new T(function(){var _wq=B(_rO(B(_rM(_wk))));if(_wo>=0){return B(A3(_7W,_wq,_wn,new T(function(){return B(A2(_a9,_wq,_30));})));}else{return B(A3(_8A,_wq,_wn,new T(function(){return B(A2(_a9,_wq,_30));})));}}),_wr=function(_ws){var _wt=_ws-0.5;return (_wt>=0)?(E(_wt)==0)?(!B(_vd(_wk,_wn)))?E(_wp):E(_wn):E(_wp):E(_wn);},_wu=E(_wo);if(!_wu){return new F(function(){return _wr(0);});}else{if(_wu<=0){var _wv= -_wu-0.5;return (_wv>=0)?(E(_wv)==0)?(!B(_vd(_wk,_wn)))?E(_wp):E(_wn):E(_wp):E(_wn);}else{return new F(function(){return _wr(_wu);});}}},_ww=function(_wx,_wy){return new F(function(){return _wj(_wx,E(_wy));});},_wz=function(_wA,_wB){return E(B(_vQ(_wA,E(_wB))).a);},_wC={_:0,a:_rL,b:_jv,c:_wf,d:_wz,e:_ww,f:_w3,g:_w9},_wD=new T1(0,1),_wE=function(_wF,_wG){var _wH=E(_wF);return new T2(0,_wH,new T(function(){var _wI=B(_wE(B(_4p(_wH,_wG)),_wG));return new T2(1,_wI.a,_wI.b);}));},_wJ=function(_wK){var _wL=B(_wE(_wK,_wD));return new T2(1,_wL.a,_wL.b);},_wM=function(_wN,_wO){var _wP=B(_wE(_wN,new T(function(){return B(_6K(_wO,_wN));})));return new T2(1,_wP.a,_wP.b);},_wQ=new T1(0,0),_wR=function(_wS,_wT){var _wU=E(_wS);if(!_wU._){var _wV=_wU.a,_wW=E(_wT);return (_wW._==0)?_wV>=_wW.a:I_compareInt(_wW.a,_wV)<=0;}else{var _wX=_wU.a,_wY=E(_wT);return (_wY._==0)?I_compareInt(_wX,_wY.a)>=0:I_compare(_wX,_wY.a)>=0;}},_wZ=function(_x0,_x1,_x2){if(!B(_wR(_x1,_wQ))){var _x3=function(_x4){return (!B(_51(_x4,_x2)))?new T2(1,_x4,new T(function(){return B(_x3(B(_4p(_x4,_x1))));})):__Z;};return new F(function(){return _x3(_x0);});}else{var _x5=function(_x6){return (!B(_4S(_x6,_x2)))?new T2(1,_x6,new T(function(){return B(_x5(B(_4p(_x6,_x1))));})):__Z;};return new F(function(){return _x5(_x0);});}},_x7=function(_x8,_x9,_xa){return new F(function(){return _wZ(_x8,B(_6K(_x9,_x8)),_xa);});},_xb=function(_xc,_xd){return new F(function(){return _wZ(_xc,_wD,_xd);});},_xe=function(_xf){return new F(function(){return _4m(_xf);});},_xg=function(_xh){return new F(function(){return _6K(_xh,_wD);});},_xi=function(_xj){return new F(function(){return _4p(_xj,_wD);});},_xk=function(_xl){return new F(function(){return _qL(E(_xl));});},_xm={_:0,a:_xi,b:_xg,c:_xk,d:_xe,e:_wJ,f:_wM,g:_xb,h:_x7},_xn=function(_xo,_xp){while(1){var _xq=E(_xo);if(!_xq._){var _xr=E(_xq.a);if(_xr==(-2147483648)){_xo=new T1(1,I_fromInt(-2147483648));continue;}else{var _xs=E(_xp);if(!_xs._){return new T1(0,B(_sH(_xr,_xs.a)));}else{_xo=new T1(1,I_fromInt(_xr));_xp=_xs;continue;}}}else{var _xt=_xq.a,_xu=E(_xp);return (_xu._==0)?new T1(1,I_div(_xt,I_fromInt(_xu.a))):new T1(1,I_div(_xt,_xu.a));}}},_xv=function(_xw,_xx){if(!B(_4e(_xx,_va))){return new F(function(){return _xn(_xw,_xx);});}else{return E(_49);}},_xy=function(_xz,_xA){while(1){var _xB=E(_xz);if(!_xB._){var _xC=E(_xB.a);if(_xC==(-2147483648)){_xz=new T1(1,I_fromInt(-2147483648));continue;}else{var _xD=E(_xA);if(!_xD._){var _xE=_xD.a;return new T2(0,new T1(0,B(_sH(_xC,_xE))),new T1(0,B(_td(_xC,_xE))));}else{_xz=new T1(1,I_fromInt(_xC));_xA=_xD;continue;}}}else{var _xF=E(_xA);if(!_xF._){_xz=_xB;_xA=new T1(1,I_fromInt(_xF.a));continue;}else{var _xG=I_divMod(_xB.a,_xF.a);return new T2(0,new T1(1,_xG.a),new T1(1,_xG.b));}}}},_xH=function(_xI,_xJ){if(!B(_4e(_xJ,_va))){var _xK=B(_xy(_xI,_xJ));return new T2(0,_xK.a,_xK.b);}else{return E(_49);}},_xL=function(_xM,_xN){while(1){var _xO=E(_xM);if(!_xO._){var _xP=E(_xO.a);if(_xP==(-2147483648)){_xM=new T1(1,I_fromInt(-2147483648));continue;}else{var _xQ=E(_xN);if(!_xQ._){return new T1(0,B(_td(_xP,_xQ.a)));}else{_xM=new T1(1,I_fromInt(_xP));_xN=_xQ;continue;}}}else{var _xR=_xO.a,_xS=E(_xN);return (_xS._==0)?new T1(1,I_mod(_xR,I_fromInt(_xS.a))):new T1(1,I_mod(_xR,_xS.a));}}},_xT=function(_xU,_xV){if(!B(_4e(_xV,_va))){return new F(function(){return _xL(_xU,_xV);});}else{return E(_49);}},_xW=function(_xX,_xY){while(1){var _xZ=E(_xX);if(!_xZ._){var _y0=E(_xZ.a);if(_y0==(-2147483648)){_xX=new T1(1,I_fromInt(-2147483648));continue;}else{var _y1=E(_xY);if(!_y1._){return new T1(0,quot(_y0,_y1.a));}else{_xX=new T1(1,I_fromInt(_y0));_xY=_y1;continue;}}}else{var _y2=_xZ.a,_y3=E(_xY);return (_y3._==0)?new T1(0,I_toInt(I_quot(_y2,I_fromInt(_y3.a)))):new T1(1,I_quot(_y2,_y3.a));}}},_y4=function(_y5,_y6){if(!B(_4e(_y6,_va))){return new F(function(){return _xW(_y5,_y6);});}else{return E(_49);}},_y7=function(_y8,_y9){if(!B(_4e(_y9,_va))){var _ya=B(_4y(_y8,_y9));return new T2(0,_ya.a,_ya.b);}else{return E(_49);}},_yb=function(_yc,_yd){while(1){var _ye=E(_yc);if(!_ye._){var _yf=E(_ye.a);if(_yf==(-2147483648)){_yc=new T1(1,I_fromInt(-2147483648));continue;}else{var _yg=E(_yd);if(!_yg._){return new T1(0,_yf%_yg.a);}else{_yc=new T1(1,I_fromInt(_yf));_yd=_yg;continue;}}}else{var _yh=_ye.a,_yi=E(_yd);return (_yi._==0)?new T1(1,I_rem(_yh,I_fromInt(_yi.a))):new T1(1,I_rem(_yh,_yi.a));}}},_yj=function(_yk,_yl){if(!B(_4e(_yl,_va))){return new F(function(){return _yb(_yk,_yl);});}else{return E(_49);}},_ym=function(_yn){return E(_yn);},_yo=function(_yp){return E(_yp);},_yq=function(_yr){var _ys=E(_yr);if(!_ys._){var _yt=E(_ys.a);return (_yt==(-2147483648))?E(_7o):(_yt<0)?new T1(0, -_yt):E(_ys);}else{var _yu=_ys.a;return (I_compareInt(_yu,0)>=0)?E(_ys):new T1(1,I_negate(_yu));}},_yv=new T1(0,0),_yw=new T1(0,-1),_yx=function(_yy){var _yz=E(_yy);if(!_yz._){var _yA=_yz.a;return (_yA>=0)?(E(_yA)==0)?E(_yv):E(_50):E(_yw);}else{var _yB=I_compareInt(_yz.a,0);return (_yB<=0)?(E(_yB)==0)?E(_yv):E(_yw):E(_50);}},_yC={_:0,a:_4p,b:_6K,c:_uK,d:_7p,e:_yq,f:_yx,g:_yo},_yD=function(_yE,_yF){var _yG=E(_yE);if(!_yG._){var _yH=_yG.a,_yI=E(_yF);return (_yI._==0)?_yH!=_yI.a:(I_compareInt(_yI.a,_yH)==0)?false:true;}else{var _yJ=_yG.a,_yK=E(_yF);return (_yK._==0)?(I_compareInt(_yJ,_yK.a)==0)?false:true:(I_compare(_yJ,_yK.a)==0)?false:true;}},_yL=new T2(0,_4e,_yD),_yM=function(_yN,_yO){return (!B(_6v(_yN,_yO)))?E(_yN):E(_yO);},_yP=function(_yQ,_yR){return (!B(_6v(_yQ,_yR)))?E(_yR):E(_yQ);},_yS={_:0,a:_yL,b:_31,c:_51,d:_6v,e:_4S,f:_wR,g:_yM,h:_yP},_yT=function(_yU){return new T2(0,E(_yU),E(_n1));},_yV=new T3(0,_yC,_yS,_yT),_yW={_:0,a:_yV,b:_xm,c:_y4,d:_yj,e:_xv,f:_xT,g:_y7,h:_xH,i:_ym},_yX=function(_yY){return E(E(_yY).b);},_yZ=function(_z0){return E(E(_z0).g);},_z1=new T1(0,1),_z2=function(_z3,_z4,_z5){var _z6=B(_yX(_z3)),_z7=B(_8w(_z6)),_z8=new T(function(){var _z9=new T(function(){var _za=new T(function(){var _zb=new T(function(){return B(A3(_yZ,_z3,_yW,new T(function(){return B(A3(_ak,_z6,_z4,_z5));})));});return B(A2(_a9,_z7,_zb));}),_zc=new T(function(){return B(A2(_7Y,_z7,new T(function(){return B(A2(_a9,_z7,_z1));})));});return B(A3(_8y,_z7,_zc,_za));});return B(A3(_8y,_z7,_z9,_z5));});return new F(function(){return A3(_7W,_z7,_z4,_z8);});},_zd=1.5707963267948966,_ze=function(_zf){return 0.2/Math.cos(B(_z2(_wC,_zf,_zd))-0.7853981633974483);},_zg=2,_zh=0.3,_zi=-0.1,_zj=new T3(0,_qr,_zi,_zh),_zk=new T2(0,_zj,_zg),_zl=new T(function(){var _zm=B(_pe(_ze,_qo,_qH,_zk,_qB));return {_:0,a:_zm.a,b:_zm.b,c:_zm.c,d:_zm.d,e:_zm.e,f:_zm.f,g:_zm.g,h:_zm.h,i:_zm.i};}),_zn=new T2(1,_zl,_T),_zo=new T2(1,_qC,_zn),_zp=new T(function(){return B(unCStr("Negative range size"));}),_zq=new T(function(){return B(err(_zp));}),_zr=function(_){var _zs=B(_in(_zo,0))-1|0,_zt=function(_zu){if(_zu>=0){var _zv=newArr(_zu,_it),_zw=_zv,_zx=E(_zu);if(!_zx){return new T4(0,E(_qE),E(_zs),0,_zw);}else{var _zy=function(_zz,_zA,_){while(1){var _zB=E(_zz);if(!_zB._){return E(_);}else{var _=_zw[_zA]=_zB.a;if(_zA!=(_zx-1|0)){var _zC=_zA+1|0;_zz=_zB.b;_zA=_zC;continue;}else{return E(_);}}}},_=B((function(_zD,_zE,_zF,_){var _=_zw[_zF]=_zD;if(_zF!=(_zx-1|0)){return new F(function(){return _zy(_zE,_zF+1|0,_);});}else{return E(_);}})(_qC,_zn,0,_));return new T4(0,E(_qE),E(_zs),_zx,_zw);}}else{return E(_zq);}};if(0>_zs){return new F(function(){return _zt(0);});}else{return new F(function(){return _zt(_zs+1|0);});}},_zG=function(_zH){var _zI=B(A1(_zH,_));return E(_zI);},_zJ=new T(function(){return B(_zG(_zr));}),_zK=function(_zL,_zM,_){var _zN=B(A1(_zL,_)),_zO=B(A1(_zM,_));return _zN;},_zP=function(_zQ,_zR,_){var _zS=B(A1(_zQ,_)),_zT=B(A1(_zR,_));return new T(function(){return B(A1(_zS,_zT));});},_zU=function(_zV,_zW,_){var _zX=B(A1(_zW,_));return _zV;},_zY=function(_zZ,_A0,_){var _A1=B(A1(_A0,_));return new T(function(){return B(A1(_zZ,_A1));});},_A2=new T2(0,_zY,_zU),_A3=function(_A4,_){return _A4;},_A5=function(_A6,_A7,_){var _A8=B(A1(_A6,_));return new F(function(){return A1(_A7,_);});},_A9=new T5(0,_A2,_A3,_zP,_A5,_zK),_Aa=function(_Ab){var _Ac=E(_Ab);return (E(_Ac.b)-E(_Ac.a)|0)+1|0;},_Ad=function(_Ae,_Af){var _Ag=E(_Ae),_Ah=E(_Af);return (E(_Ag.a)>_Ah)?false:_Ah<=E(_Ag.b);},_Ai=function(_Aj,_Ak){var _Al=jsShowI(_Aj);return new F(function(){return _14(fromJSStr(_Al),_Ak);});},_Am=function(_An,_Ao,_Ap){if(_Ao>=0){return new F(function(){return _Ai(_Ao,_Ap);});}else{if(_An<=6){return new F(function(){return _Ai(_Ao,_Ap);});}else{return new T2(1,_8f,new T(function(){var _Aq=jsShowI(_Ao);return B(_14(fromJSStr(_Aq),new T2(1,_8e,_Ap)));}));}}},_Ar=function(_As){return new F(function(){return _Am(0,E(_As),_T);});},_At=function(_Au,_Av,_Aw){return new F(function(){return _Am(E(_Au),E(_Av),_Aw);});},_Ax=function(_Ay,_Az){return new F(function(){return _Am(0,E(_Ay),_Az);});},_AA=function(_AB,_AC){return new F(function(){return _3P(_Ax,_AB,_AC);});},_AD=new T3(0,_At,_Ar,_AA),_AE=0,_AF=function(_AG,_AH,_AI){return new F(function(){return A1(_AG,new T2(1,_3M,new T(function(){return B(A1(_AH,_AI));})));});},_AJ=new T(function(){return B(unCStr("foldr1"));}),_AK=new T(function(){return B(_mr(_AJ));}),_AL=function(_AM,_AN){var _AO=E(_AN);if(!_AO._){return E(_AK);}else{var _AP=_AO.a,_AQ=E(_AO.b);if(!_AQ._){return E(_AP);}else{return new F(function(){return A2(_AM,_AP,new T(function(){return B(_AL(_AM,_AQ));}));});}}},_AR=new T(function(){return B(unCStr(" out of range "));}),_AS=new T(function(){return B(unCStr("}.index: Index "));}),_AT=new T(function(){return B(unCStr("Ix{"));}),_AU=new T2(1,_8e,_T),_AV=new T2(1,_8e,_AU),_AW=0,_AX=function(_AY){return E(E(_AY).a);},_AZ=function(_B0,_B1,_B2,_B3,_B4){var _B5=new T(function(){var _B6=new T(function(){var _B7=new T(function(){var _B8=new T(function(){var _B9=new T(function(){return B(A3(_AL,_AF,new T2(1,new T(function(){return B(A3(_AX,_B2,_AW,_B3));}),new T2(1,new T(function(){return B(A3(_AX,_B2,_AW,_B4));}),_T)),_AV));});return B(_14(_AR,new T2(1,_8f,new T2(1,_8f,_B9))));});return B(A(_AX,[_B2,_AE,_B1,new T2(1,_8e,_B8)]));});return B(_14(_AS,new T2(1,_8f,_B7)));},1);return B(_14(_B0,_B6));},1);return new F(function(){return err(B(_14(_AT,_B5)));});},_Ba=function(_Bb,_Bc,_Bd,_Be,_Bf){return new F(function(){return _AZ(_Bb,_Bc,_Bf,_Bd,_Be);});},_Bg=function(_Bh,_Bi,_Bj,_Bk){var _Bl=E(_Bj);return new F(function(){return _Ba(_Bh,_Bi,_Bl.a,_Bl.b,_Bk);});},_Bm=function(_Bn,_Bo,_Bp,_Bq){return new F(function(){return _Bg(_Bq,_Bp,_Bo,_Bn);});},_Br=new T(function(){return B(unCStr("Int"));}),_Bs=function(_Bt,_Bu){return new F(function(){return _Bm(_AD,_Bu,_Bt,_Br);});},_Bv=function(_Bw,_Bx){var _By=E(_Bw),_Bz=E(_By.a),_BA=E(_Bx);if(_Bz>_BA){return new F(function(){return _Bs(_BA,_By);});}else{if(_BA>E(_By.b)){return new F(function(){return _Bs(_BA,_By);});}else{return _BA-_Bz|0;}}},_BB=function(_BC){var _BD=E(_BC);return new F(function(){return _sr(_BD.a,_BD.b);});},_BE=function(_BF){var _BG=E(_BF),_BH=E(_BG.a),_BI=E(_BG.b);return (_BH>_BI)?E(_AE):(_BI-_BH|0)+1|0;},_BJ=function(_BK,_BL){return new F(function(){return _tQ(_BL,E(_BK).a);});},_BM={_:0,a:_uG,b:_BB,c:_Bv,d:_BJ,e:_Ad,f:_BE,g:_Aa},_BN=function(_BO,_BP){return new T2(1,_BO,_BP);},_BQ=function(_BR,_BS){var _BT=E(_BS);return new T2(0,_BT.a,_BT.b);},_BU=function(_BV){return E(E(_BV).f);},_BW=function(_BX,_BY,_BZ){var _C0=E(_BY),_C1=_C0.a,_C2=_C0.b,_C3=function(_){var _C4=B(A2(_BU,_BX,_C0));if(_C4>=0){var _C5=newArr(_C4,_it),_C6=_C5,_C7=E(_C4);if(!_C7){return new T(function(){return new T4(0,E(_C1),E(_C2),0,_C6);});}else{var _C8=function(_C9,_Ca,_){while(1){var _Cb=E(_C9);if(!_Cb._){return E(_);}else{var _=_C6[_Ca]=_Cb.a;if(_Ca!=(_C7-1|0)){var _Cc=_Ca+1|0;_C9=_Cb.b;_Ca=_Cc;continue;}else{return E(_);}}}},_=B(_C8(_BZ,0,_));return new T(function(){return new T4(0,E(_C1),E(_C2),_C7,_C6);});}}else{return E(_zq);}};return new F(function(){return _zG(_C3);});},_Cd=function(_Ce,_Cf,_Cg,_Ch){var _Ci=new T(function(){var _Cj=E(_Ch),_Ck=_Cj.c-1|0,_Cl=new T(function(){return B(A2(_e6,_Cf,_T));});if(0<=_Ck){var _Cm=new T(function(){return B(_ag(_Cf));}),_Cn=function(_Co){var _Cp=new T(function(){var _Cq=new T(function(){return B(A1(_Cg,new T(function(){return E(_Cj.d[_Co]);})));});return B(A3(_ao,_Cm,_BN,_Cq));});return new F(function(){return A3(_am,_Cf,_Cp,new T(function(){if(_Co!=_Ck){return B(_Cn(_Co+1|0));}else{return E(_Cl);}}));});};return B(_Cn(0));}else{return E(_Cl);}}),_Cr=new T(function(){return B(_BQ(_Ce,_Ch));});return new F(function(){return A3(_ao,B(_ag(_Cf)),function(_Cs){return new F(function(){return _BW(_Ce,_Cr,_Cs);});},_Ci);});},_Ct=function(_){return _S;},_Cu=new T(function(){return eval("vertex");}),_Cv=function(_Cw,_Cx,_Cy,_Cz,_CA,_CB,_){var _CC=__apply(E(_Cu),new T2(1,_CB,new T2(1,_CA,new T2(1,_Cz,new T2(1,_Cy,new T2(1,_Cx,new T2(1,_Cw,_T)))))));return new F(function(){return _Ct(_);});},_CD=function(_CE,_){while(1){var _CF=E(_CE);if(!_CF._){return _S;}else{var _CG=E(_CF.a),_CH=E(_CG.a),_CI=E(_CH.a),_CJ=E(_CH.b),_CK=B(_Cv(E(_CI.a),E(_CI.b),E(_CI.c),E(_CJ.a),E(_CJ.b),E(_CH.c),_)),_CL=E(_CG.b),_CM=E(_CL.a),_CN=E(_CL.b),_CO=B(_Cv(E(_CM.a),E(_CM.b),E(_CM.c),E(_CN.a),E(_CN.b),E(_CL.c),_)),_CP=E(_CG.c),_CQ=E(_CP.a),_CR=E(_CP.b),_CS=B(_Cv(E(_CQ.a),E(_CQ.b),E(_CQ.c),E(_CR.a),E(_CR.b),E(_CP.c),_));_CE=_CF.b;continue;}}},_CT=new T(function(){return eval("drawTriangles");}),_CU=function(_){var _CV=__app0(E(_CT));return new F(function(){return _Ct(_);});},_CW=function(_CX,_){var _CY=B(_CD(_CX,_));return new F(function(){return _CU(_);});},_CZ=function(_D0,_){return new F(function(){return _CW(E(_D0).h,_);});},_D1=new T(function(){return eval("draw");}),_D2=function(_D3){return E(_D3);},_D4=function(_D5){return E(_D5);},_D6=function(_D7,_D8){return E(_D8);},_D9=function(_Da,_Db){return E(_Da);},_Dc=function(_Dd){return E(_Dd);},_De=new T2(0,_Dc,_D9),_Df=function(_Dg,_Dh){return E(_Dg);},_Di=new T5(0,_De,_D4,_D2,_D6,_Df),_Dj=function(_Dk,_Dl,_Dm,_Dn,_Do,_Dp){var _Dq=new T(function(){var _Dr=E(_Dn),_Ds=E(_Do),_Dt=new T(function(){var _Du=E(_Dr.a),_Dv=E(_Ds.a);return new T3(0,new T(function(){return E(_Du.a)+E(_Dv.a)*5.0e-2;}),new T(function(){return E(_Du.b)+E(_Dv.b)*5.0e-2;}),new T(function(){return E(_Du.c)+E(_Dv.c)*5.0e-2;}));});return new T2(0,_Dt,new T(function(){return E(_Dr.b)+E(_Ds.b)*5.0e-2;}));});return new F(function(){return _oP(_Dk,_Dl,_Dm,_Dq,_Do,_Dp);});},_Dw=new T2(0,_jX,_kw),_Dx=function(_Dy){var _Dz=E(_Dy),_DA=_Dz.b,_DB=_Dz.g,_DC=new T(function(){var _DD=E(_Dz.e),_DE=new T(function(){var _DF=E(_DD.a),_DG=E(_DA),_DH=E(_DB),_DI=B(_lm(_Dw,_DG.a,_DG.b,_DG.c,_DH.a,_DH.b,_DH.c));return new T3(0,new T(function(){return E(_DF.a)+E(_DI.a)*5.0e-2;}),new T(function(){return E(_DF.b)+E(_DI.b)*5.0e-2;}),new T(function(){return E(_DF.c)+E(_DI.c)*5.0e-2;}));});return new T2(0,_DE,_DD.b);});return {_:0,a:_Dz.a,b:_DA,c:_Dz.c,d:_Dz.d,e:_DC,f:_Dz.f,g:_DB,h:_Dz.h,i:_Dz.i};},_DJ=function(_DK){var _DL=E(_DK),_DM=B(_Dj(_DL.a,_DL.b,_DL.c,_DL.d,_DL.e,_DL.f));return {_:0,a:_DM.a,b:_DM.b,c:_DM.c,d:_DM.d,e:_DM.e,f:_DM.f,g:_DM.g,h:_DM.h,i:_DM.i};},_DN=function(_DO){var _DP=E(_DO);if(!_DP._){return __Z;}else{return new F(function(){return _14(_DP.a,new T(function(){return B(_DN(_DP.b));},1));});}},_DQ=new T(function(){return B(unCStr("base"));}),_DR=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_DS=new T(function(){return B(unCStr("IOException"));}),_DT=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_DQ,_DR,_DS),_DU=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_DT,_T,_T),_DV=function(_DW){return E(_DU);},_DX=function(_DY){var _DZ=E(_DY);return new F(function(){return _3m(B(_3k(_DZ.a)),_DV,_DZ.b);});},_E0=new T(function(){return B(unCStr(": "));}),_E1=new T(function(){return B(unCStr(")"));}),_E2=new T(function(){return B(unCStr(" ("));}),_E3=new T(function(){return B(unCStr("interrupted"));}),_E4=new T(function(){return B(unCStr("system error"));}),_E5=new T(function(){return B(unCStr("unsatisified constraints"));}),_E6=new T(function(){return B(unCStr("user error"));}),_E7=new T(function(){return B(unCStr("permission denied"));}),_E8=new T(function(){return B(unCStr("illegal operation"));}),_E9=new T(function(){return B(unCStr("end of file"));}),_Ea=new T(function(){return B(unCStr("resource exhausted"));}),_Eb=new T(function(){return B(unCStr("resource busy"));}),_Ec=new T(function(){return B(unCStr("does not exist"));}),_Ed=new T(function(){return B(unCStr("already exists"));}),_Ee=new T(function(){return B(unCStr("resource vanished"));}),_Ef=new T(function(){return B(unCStr("timeout"));}),_Eg=new T(function(){return B(unCStr("unsupported operation"));}),_Eh=new T(function(){return B(unCStr("hardware fault"));}),_Ei=new T(function(){return B(unCStr("inappropriate type"));}),_Ej=new T(function(){return B(unCStr("invalid argument"));}),_Ek=new T(function(){return B(unCStr("failed"));}),_El=new T(function(){return B(unCStr("protocol error"));}),_Em=function(_En,_Eo){switch(E(_En)){case 0:return new F(function(){return _14(_Ed,_Eo);});break;case 1:return new F(function(){return _14(_Ec,_Eo);});break;case 2:return new F(function(){return _14(_Eb,_Eo);});break;case 3:return new F(function(){return _14(_Ea,_Eo);});break;case 4:return new F(function(){return _14(_E9,_Eo);});break;case 5:return new F(function(){return _14(_E8,_Eo);});break;case 6:return new F(function(){return _14(_E7,_Eo);});break;case 7:return new F(function(){return _14(_E6,_Eo);});break;case 8:return new F(function(){return _14(_E5,_Eo);});break;case 9:return new F(function(){return _14(_E4,_Eo);});break;case 10:return new F(function(){return _14(_El,_Eo);});break;case 11:return new F(function(){return _14(_Ek,_Eo);});break;case 12:return new F(function(){return _14(_Ej,_Eo);});break;case 13:return new F(function(){return _14(_Ei,_Eo);});break;case 14:return new F(function(){return _14(_Eh,_Eo);});break;case 15:return new F(function(){return _14(_Eg,_Eo);});break;case 16:return new F(function(){return _14(_Ef,_Eo);});break;case 17:return new F(function(){return _14(_Ee,_Eo);});break;default:return new F(function(){return _14(_E3,_Eo);});}},_Ep=new T(function(){return B(unCStr("}"));}),_Eq=new T(function(){return B(unCStr("{handle: "));}),_Er=function(_Es,_Et,_Eu,_Ev,_Ew,_Ex){var _Ey=new T(function(){var _Ez=new T(function(){var _EA=new T(function(){var _EB=E(_Ev);if(!_EB._){return E(_Ex);}else{var _EC=new T(function(){return B(_14(_EB,new T(function(){return B(_14(_E1,_Ex));},1)));},1);return B(_14(_E2,_EC));}},1);return B(_Em(_Et,_EA));}),_ED=E(_Eu);if(!_ED._){return E(_Ez);}else{return B(_14(_ED,new T(function(){return B(_14(_E0,_Ez));},1)));}}),_EE=E(_Ew);if(!_EE._){var _EF=E(_Es);if(!_EF._){return E(_Ey);}else{var _EG=E(_EF.a);if(!_EG._){var _EH=new T(function(){var _EI=new T(function(){return B(_14(_Ep,new T(function(){return B(_14(_E0,_Ey));},1)));},1);return B(_14(_EG.a,_EI));},1);return new F(function(){return _14(_Eq,_EH);});}else{var _EJ=new T(function(){var _EK=new T(function(){return B(_14(_Ep,new T(function(){return B(_14(_E0,_Ey));},1)));},1);return B(_14(_EG.a,_EK));},1);return new F(function(){return _14(_Eq,_EJ);});}}}else{return new F(function(){return _14(_EE.a,new T(function(){return B(_14(_E0,_Ey));},1));});}},_EL=function(_EM){var _EN=E(_EM);return new F(function(){return _Er(_EN.a,_EN.b,_EN.c,_EN.d,_EN.f,_T);});},_EO=function(_EP,_EQ,_ER){var _ES=E(_EQ);return new F(function(){return _Er(_ES.a,_ES.b,_ES.c,_ES.d,_ES.f,_ER);});},_ET=function(_EU,_EV){var _EW=E(_EU);return new F(function(){return _Er(_EW.a,_EW.b,_EW.c,_EW.d,_EW.f,_EV);});},_EX=function(_EY,_EZ){return new F(function(){return _3P(_ET,_EY,_EZ);});},_F0=new T3(0,_EO,_EL,_EX),_F1=new T(function(){return new T5(0,_DV,_F0,_F2,_DX,_EL);}),_F2=function(_F3){return new T2(0,_F1,_F3);},_F4=__Z,_F5=7,_F6=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:43:7-13"));}),_F7=new T6(0,_F4,_F5,_T,_F6,_F4,_F4),_F8=new T(function(){return B(_F2(_F7));}),_F9=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:44:7-13"));}),_Fa=new T6(0,_F4,_F5,_T,_F9,_F4,_F4),_Fb=new T(function(){return B(_F2(_Fa));}),_Fc=new T2(1,_T,_T),_Fd=function(_Fe,_){var _Ff=B(_Cd(_BM,_Di,_Dx,_Fe)),_Fg=_Ff.c,_Fh=_Ff.d,_Fi=E(_Ff.a),_Fj=E(_Ff.b);if(_Fi<=_Fj){var _Fk=function(_Fl,_Fm,_){if(_Fl<=_Fj){var _Fn=E(_Fm),_Fo=function(_Fp,_Fq,_Fr,_Fs,_Ft,_){if(_Fq>_Fl){return new F(function(){return die(_F8);});}else{if(_Fl>_Fr){return new F(function(){return die(_F8);});}else{if(_Fq>_Fp){return new F(function(){return die(_Fb);});}else{if(_Fp>_Fr){return new F(function(){return die(_Fb);});}else{if(_Fp!=_Fj){var _Fu=B(_Fo(_Fp+1|0,_Fq,_Fr,_Fs,_Ft,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_Fu).a);})),new T(function(){return E(E(_Fu).b);}));}else{return new T2(0,_Fc,new T4(0,E(_Fq),E(_Fr),_Fs,_Ft));}}}}}},_Fv=B(_Fo(_Fl,E(_Fn.a),E(_Fn.b),_Fn.c,_Fn.d,_));if(_Fl!=_Fj){var _Fw=B(_Fk(_Fl+1|0,new T(function(){return E(E(_Fv).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_DN(E(_Fv).a));}),new T(function(){return E(E(_Fw).a);})),new T(function(){return E(E(_Fw).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_DN(E(_Fv).a));}),_T),new T(function(){return E(E(_Fv).b);}));}}else{if(_Fl!=_Fj){var _Fx=B(_Fk(_Fl+1|0,_Fm,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_Fx).a);})),new T(function(){return E(E(_Fx).b);}));}else{return new T2(0,new T2(1,_T,_T),_Fm);}}},_Fy=function(_Fz,_FA,_FB,_FC,_FD,_){if(_Fz<=_Fj){var _FE=function(_FF,_FG,_FH,_FI,_FJ,_){if(_FG>_Fz){return new F(function(){return die(_F8);});}else{if(_Fz>_FH){return new F(function(){return die(_F8);});}else{if(_FG>_FF){return new F(function(){return die(_Fb);});}else{if(_FF>_FH){return new F(function(){return die(_Fb);});}else{if(_FF!=_Fj){var _FK=B(_FE(_FF+1|0,_FG,_FH,_FI,_FJ,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_FK).a);})),new T(function(){return E(E(_FK).b);}));}else{return new T2(0,_Fc,new T4(0,E(_FG),E(_FH),_FI,_FJ));}}}}}},_FL=B(_FE(_Fz,_FA,_FB,_FC,_FD,_));if(_Fz!=_Fj){var _FM=B(_Fk(_Fz+1|0,new T(function(){return E(E(_FL).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_DN(E(_FL).a));}),new T(function(){return E(E(_FM).a);})),new T(function(){return E(E(_FM).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_DN(E(_FL).a));}),_T),new T(function(){return E(E(_FL).b);}));}}else{if(_Fz!=_Fj){var _FN=B(_Fy(_Fz+1|0,_FA,_FB,_FC,_FD,_));return new T2(0,new T2(1,_T,new T(function(){return E(E(_FN).a);})),new T(function(){return E(E(_FN).b);}));}else{return new T2(0,new T2(1,_T,_T),new T4(0,E(_FA),E(_FB),_FC,_FD));}}},_FO=B(_Fy(_Fi,_Fi,_Fj,_Fg,_Fh,_)),_FP=new T(function(){return B(_Cd(_BM,_Di,_DJ,new T(function(){return E(E(_FO).b);})));});return new T2(0,_S,_FP);}else{var _FQ=new T(function(){var _FR=function(_){var _FS=function(_FT){if(_FT>=0){var _FU=newArr(_FT,_it),_FV=_FU,_FW=E(_FT);if(!_FW){return new T4(0,E(_Fi),E(_Fj),0,_FV);}else{var _FX=_Fg-1|0,_FY=function(_FZ,_G0,_){while(1){var _G1=E(_FZ);if(!_G1._){return E(_);}else{var _=_FV[_G0]=_G1.a;if(_G0!=(_FW-1|0)){var _G2=_G0+1|0;_FZ=_G1.b;_G0=_G2;continue;}else{return E(_);}}}};if(0<=_FX){var _G3=function(_G4){return new T2(1,new T(function(){var _G5=E(_Fh[_G4]),_G6=B(_Dj(_G5.a,_G5.b,_G5.c,_G5.d,_G5.e,_G5.f));return {_:0,a:_G6.a,b:_G6.b,c:_G6.c,d:_G6.d,e:_G6.e,f:_G6.f,g:_G6.g,h:_G6.h,i:_G6.i};}),new T(function(){if(_G4!=_FX){return B(_G3(_G4+1|0));}else{return __Z;}}));},_=B(_FY(B(_G3(0)),0,_));return new T4(0,E(_Fi),E(_Fj),_FW,_FV);}else{return new T4(0,E(_Fi),E(_Fj),_FW,_FV);}}}else{return E(_zq);}};if(_Fi>_Fj){return new F(function(){return _FS(0);});}else{return new F(function(){return _FS((_Fj-_Fi|0)+1|0);});}};return B(_zG(_FR));});return new T2(0,_S,_FQ);}},_G7=new T(function(){return eval("refresh");}),_G8=function(_G9,_){var _Ga=__app0(E(_G7)),_Gb=__app0(E(_D1)),_Gc=B(A(_Cd,[_BM,_A9,_CZ,_G9,_])),_Gd=B(_Fd(_G9,_));return new T(function(){return E(E(_Gd).b);});},_Ge=function(_Gf,_Gg,_Gh){var _Gi=function(_){var _Gj=B(_G8(_Gf,_));return new T(function(){return B(A1(_Gh,new T1(1,_Gj)));});};return new T1(0,_Gi);},_Gk=new T0(2),_Gl=function(_Gm,_Gn,_Go){return function(_){var _Gp=E(_Gm),_Gq=rMV(_Gp),_Gr=E(_Gq);if(!_Gr._){var _Gs=new T(function(){var _Gt=new T(function(){return B(A1(_Go,_S));});return B(_14(_Gr.b,new T2(1,new T2(0,_Gn,function(_Gu){return E(_Gt);}),_T)));}),_=wMV(_Gp,new T2(0,_Gr.a,_Gs));return _Gk;}else{var _Gv=E(_Gr.a);if(!_Gv._){var _=wMV(_Gp,new T2(0,_Gn,_T));return new T(function(){return B(A1(_Go,_S));});}else{var _=wMV(_Gp,new T1(1,_Gv.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Go,_S));}),new T2(1,new T(function(){return B(A2(_Gv.a,_Gn,_U));}),_T)));}}};},_Gw=function(_Gx){return E(E(_Gx).b);},_Gy=function(_Gz,_GA,_GB){var _GC=new T(function(){return new T1(0,B(_Gl(_GA,_GB,_U)));}),_GD=function(_GE){return new T1(1,new T2(1,new T(function(){return B(A1(_GE,_S));}),new T2(1,_GC,_T)));};return new F(function(){return A2(_Gw,_Gz,_GD);});},_GF=function(_){return new F(function(){return __jsNull();});},_GG=function(_GH){var _GI=B(A1(_GH,_));return E(_GI);},_GJ=new T(function(){return B(_GG(_GF));}),_GK=new T(function(){return E(_GJ);}),_GL=new T(function(){return eval("window.requestAnimationFrame");}),_GM=new T1(1,_T),_GN=function(_GO,_GP){return function(_){var _GQ=E(_GO),_GR=rMV(_GQ),_GS=E(_GR);if(!_GS._){var _GT=_GS.a,_GU=E(_GS.b);if(!_GU._){var _=wMV(_GQ,_GM);return new T(function(){return B(A1(_GP,_GT));});}else{var _GV=E(_GU.a),_=wMV(_GQ,new T2(0,_GV.a,_GU.b));return new T1(1,new T2(1,new T(function(){return B(A1(_GP,_GT));}),new T2(1,new T(function(){return B(A1(_GV.b,_U));}),_T)));}}else{var _GW=new T(function(){var _GX=function(_GY){var _GZ=new T(function(){return B(A1(_GP,_GY));});return function(_H0){return E(_GZ);};};return B(_14(_GS.a,new T2(1,_GX,_T)));}),_=wMV(_GQ,new T1(1,_GW));return _Gk;}};},_H1=function(_H2,_H3){return new T1(0,B(_GN(_H2,_H3)));},_H4=function(_H5,_H6){var _H7=new T(function(){return new T1(0,B(_Gl(_H5,_S,_U)));});return function(_){var _H8=__createJSFunc(2,function(_H9,_){var _Ha=B(_1e(_H7,_T,_));return _GK;}),_Hb=__app1(E(_GL),_H8);return new T(function(){return B(_H1(_H5,_H6));});};},_Hc=new T1(1,_T),_Hd=function(_He){var _Hf=new T(function(){return B(_Hg(_));}),_Hh=new T(function(){var _Hi=function(_Hj){return E(_Hf);},_Hk=function(_){var _Hl=nMV(_Hc);return new T(function(){return new T1(0,B(_H4(_Hl,_Hi)));});};return B(A(_Gy,[_13,_He,_S,function(_Hm){return E(new T1(0,_Hk));}]));}),_Hg=function(_Hn){return E(_Hh);};return new F(function(){return _Hg(_);});},_Ho=function(_Hp){return E(E(_Hp).a);},_Hq=function(_Hr){return E(E(_Hr).d);},_Hs=function(_Ht){return E(E(_Ht).c);},_Hu=function(_Hv){return E(E(_Hv).c);},_Hw=new T1(1,_T),_Hx=function(_Hy){var _Hz=function(_){var _HA=nMV(_Hw);return new T(function(){return B(A1(_Hy,_HA));});};return new T1(0,_Hz);},_HB=function(_HC,_HD){var _HE=new T(function(){return B(_Hu(_HC));}),_HF=B(_Ho(_HC)),_HG=function(_HH){var _HI=new T(function(){return B(A1(_HE,new T(function(){return B(A1(_HD,_HH));})));});return new F(function(){return A3(_Hs,_HF,_HI,new T(function(){return B(A2(_Hq,_HF,_HH));}));});};return new F(function(){return A3(_J,_HF,new T(function(){return B(A2(_Gw,_HC,_Hx));}),_HG);});},_HJ=function(_HK,_HL,_HM){var _HN=new T(function(){return B(_Ho(_HK));}),_HO=new T(function(){return B(A2(_Hq,_HN,_S));}),_HP=function(_HQ,_HR){var _HS=new T(function(){var _HT=new T(function(){return B(A2(_Gw,_HK,function(_HU){return new F(function(){return _H1(_HR,_HU);});}));});return B(A3(_J,_HN,_HT,new T(function(){return B(A1(_HM,_HQ));})));});return new F(function(){return A3(_J,_HN,_HS,function(_HV){var _HW=E(_HV);if(!_HW._){return E(_HO);}else{return new F(function(){return _HP(_HW.a,_HR);});}});});};return new F(function(){return _HB(_HK,function(_HU){return new F(function(){return _HP(_HL,_HU);});});});},_HX=function(_){var _HY=__app2(E(_1j),E(_96),E(_im));return new F(function(){return _1e(new T(function(){return B(A(_HJ,[_13,_zJ,_Ge,_Hd]));}),_T,_);});},_HZ=function(_){return new F(function(){return _HX(_);});};
var hasteMain = function() {B(A(_HZ, [0]));};window.onload = hasteMain;