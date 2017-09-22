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

var _0=new T(function(){return eval("__strict(compile)");}),_1=function(_2){return E(E(_2).b);},_3=function(_4){return E(E(_4).a);},_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){return new F(function(){return A1(_7,_9.a);});}else{var _a=new T(function(){return B(_1(_6));}),_b=new T(function(){return B(_3(_6));}),_c=function(_d){var _e=E(_d);if(!_e._){return E(_b);}else{return new F(function(){return A2(_a,new T(function(){return B(_5(_6,_7,_e.a));}),new T(function(){return B(_c(_e.b));}));});}};return new F(function(){return _c(_9.a);});}},_f=function(_g,_h){var _i=E(_g);return (_i._==0)?E(_h):new T2(1,_i.a,new T(function(){return B(_f(_i.b,_h));}));},_j=function(_k){var _l=E(_k);if(!_l._){return __Z;}else{return new F(function(){return _f(_l.a,new T(function(){return B(_j(_l.b));},1));});}},_m=function(_n){return new F(function(){return _j(_n);});},_o=__Z,_p=new T3(0,_o,_f,_m),_q=new T(function(){return B(unCStr(","));}),_r=new T1(0,_q),_s=new T(function(){return B(unCStr("pow("));}),_t=new T1(0,_s),_u=new T(function(){return B(unCStr(")"));}),_v=new T1(0,_u),_w=new T2(1,_v,_o),_x=function(_y,_z){return new T1(1,new T2(1,_t,new T2(1,_y,new T2(1,_r,new T2(1,_z,_w)))));},_A=new T(function(){return B(unCStr("acos("));}),_B=new T1(0,_A),_C=function(_D){return new T1(1,new T2(1,_B,new T2(1,_D,_w)));},_E=new T(function(){return B(unCStr("acosh("));}),_F=new T1(0,_E),_G=function(_H){return new T1(1,new T2(1,_F,new T2(1,_H,_w)));},_I=new T(function(){return B(unCStr("asin("));}),_J=new T1(0,_I),_K=function(_L){return new T1(1,new T2(1,_J,new T2(1,_L,_w)));},_M=new T(function(){return B(unCStr("asinh("));}),_N=new T1(0,_M),_O=function(_P){return new T1(1,new T2(1,_N,new T2(1,_P,_w)));},_Q=new T(function(){return B(unCStr("atan("));}),_R=new T1(0,_Q),_S=function(_T){return new T1(1,new T2(1,_R,new T2(1,_T,_w)));},_U=new T(function(){return B(unCStr("atanh("));}),_V=new T1(0,_U),_W=function(_X){return new T1(1,new T2(1,_V,new T2(1,_X,_w)));},_Y=new T(function(){return B(unCStr("cos("));}),_Z=new T1(0,_Y),_10=function(_11){return new T1(1,new T2(1,_Z,new T2(1,_11,_w)));},_12=new T(function(){return B(unCStr("cosh("));}),_13=new T1(0,_12),_14=function(_15){return new T1(1,new T2(1,_13,new T2(1,_15,_w)));},_16=new T(function(){return B(unCStr("exp("));}),_17=new T1(0,_16),_18=function(_19){return new T1(1,new T2(1,_17,new T2(1,_19,_w)));},_1a=new T(function(){return B(unCStr("log("));}),_1b=new T1(0,_1a),_1c=function(_1d){return new T1(1,new T2(1,_1b,new T2(1,_1d,_w)));},_1e=new T(function(){return B(unCStr(")/log("));}),_1f=new T1(0,_1e),_1g=function(_1h,_1i){return new T1(1,new T2(1,_1b,new T2(1,_1i,new T2(1,_1f,new T2(1,_1h,_w)))));},_1j=new T(function(){return B(unCStr("pi"));}),_1k=new T1(0,_1j),_1l=new T(function(){return B(unCStr("sin("));}),_1m=new T1(0,_1l),_1n=function(_1o){return new T1(1,new T2(1,_1m,new T2(1,_1o,_w)));},_1p=new T(function(){return B(unCStr("sinh("));}),_1q=new T1(0,_1p),_1r=function(_1s){return new T1(1,new T2(1,_1q,new T2(1,_1s,_w)));},_1t=new T(function(){return B(unCStr("sqrt("));}),_1u=new T1(0,_1t),_1v=function(_1w){return new T1(1,new T2(1,_1u,new T2(1,_1w,_w)));},_1x=new T(function(){return B(unCStr("tan("));}),_1y=new T1(0,_1x),_1z=function(_1A){return new T1(1,new T2(1,_1y,new T2(1,_1A,_w)));},_1B=new T(function(){return B(unCStr("tanh("));}),_1C=new T1(0,_1B),_1D=function(_1E){return new T1(1,new T2(1,_1C,new T2(1,_1E,_w)));},_1F=new T(function(){return B(unCStr("("));}),_1G=new T1(0,_1F),_1H=new T(function(){return B(unCStr(")/("));}),_1I=new T1(0,_1H),_1J=function(_1K,_1L){return new T1(1,new T2(1,_1G,new T2(1,_1K,new T2(1,_1I,new T2(1,_1L,_w)))));},_1M=new T1(0,1),_1N=function(_1O,_1P){var _1Q=E(_1O);if(!_1Q._){var _1R=_1Q.a,_1S=E(_1P);if(!_1S._){var _1T=_1S.a;return (_1R!=_1T)?(_1R>_1T)?2:0:1;}else{var _1U=I_compareInt(_1S.a,_1R);return (_1U<=0)?(_1U>=0)?1:2:0;}}else{var _1V=_1Q.a,_1W=E(_1P);if(!_1W._){var _1X=I_compareInt(_1V,_1W.a);return (_1X>=0)?(_1X<=0)?1:2:0;}else{var _1Y=I_compare(_1V,_1W.a);return (_1Y>=0)?(_1Y<=0)?1:2:0;}}},_1Z=new T(function(){return B(unCStr("base"));}),_20=new T(function(){return B(unCStr("GHC.Exception"));}),_21=new T(function(){return B(unCStr("ArithException"));}),_22=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_1Z,_20,_21),_23=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_22,_o,_o),_24=function(_25){return E(_23);},_26=function(_27){return E(E(_27).a);},_28=function(_29,_2a,_2b){var _2c=B(A1(_29,_)),_2d=B(A1(_2a,_)),_2e=hs_eqWord64(_2c.a,_2d.a);if(!_2e){return __Z;}else{var _2f=hs_eqWord64(_2c.b,_2d.b);return (!_2f)?__Z:new T1(1,_2b);}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _28(B(_26(_2i.a)),_24,_2i.b);});},_2j=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_2k=new T(function(){return B(unCStr("denormal"));}),_2l=new T(function(){return B(unCStr("divide by zero"));}),_2m=new T(function(){return B(unCStr("loss of precision"));}),_2n=new T(function(){return B(unCStr("arithmetic underflow"));}),_2o=new T(function(){return B(unCStr("arithmetic overflow"));}),_2p=function(_2q,_2r){switch(E(_2q)){case 0:return new F(function(){return _f(_2o,_2r);});break;case 1:return new F(function(){return _f(_2n,_2r);});break;case 2:return new F(function(){return _f(_2m,_2r);});break;case 3:return new F(function(){return _f(_2l,_2r);});break;case 4:return new F(function(){return _f(_2k,_2r);});break;default:return new F(function(){return _f(_2j,_2r);});}},_2s=function(_2t){return new F(function(){return _2p(_2t,_o);});},_2u=function(_2v,_2w,_2x){return new F(function(){return _2p(_2w,_2x);});},_2y=44,_2z=93,_2A=91,_2B=function(_2C,_2D,_2E){var _2F=E(_2D);if(!_2F._){return new F(function(){return unAppCStr("[]",_2E);});}else{var _2G=new T(function(){var _2H=new T(function(){var _2I=function(_2J){var _2K=E(_2J);if(!_2K._){return E(new T2(1,_2z,_2E));}else{var _2L=new T(function(){return B(A2(_2C,_2K.a,new T(function(){return B(_2I(_2K.b));})));});return new T2(1,_2y,_2L);}};return B(_2I(_2F.b));});return B(A2(_2C,_2F.a,_2H));});return new T2(1,_2A,_2G);}},_2M=function(_2N,_2O){return new F(function(){return _2B(_2p,_2N,_2O);});},_2P=new T3(0,_2u,_2s,_2M),_2Q=new T(function(){return new T5(0,_24,_2P,_2R,_2g,_2s);}),_2R=function(_2S){return new T2(0,_2Q,_2S);},_2T=3,_2U=new T(function(){return B(_2R(_2T));}),_2V=new T(function(){return die(_2U);}),_2W=function(_2X,_2Y){var _2Z=E(_2X);return (_2Z._==0)?_2Z.a*Math.pow(2,_2Y):I_toNumber(_2Z.a)*Math.pow(2,_2Y);},_30=function(_31,_32){var _33=E(_31);if(!_33._){var _34=_33.a,_35=E(_32);return (_35._==0)?_34==_35.a:(I_compareInt(_35.a,_34)==0)?true:false;}else{var _36=_33.a,_37=E(_32);return (_37._==0)?(I_compareInt(_36,_37.a)==0)?true:false:(I_compare(_36,_37.a)==0)?true:false;}},_38=function(_39){var _3a=E(_39);if(!_3a._){return E(_3a.a);}else{return new F(function(){return I_toInt(_3a.a);});}},_3b=function(_3c,_3d){while(1){var _3e=E(_3c);if(!_3e._){var _3f=_3e.a,_3g=E(_3d);if(!_3g._){var _3h=_3g.a,_3i=addC(_3f,_3h);if(!E(_3i.b)){return new T1(0,_3i.a);}else{_3c=new T1(1,I_fromInt(_3f));_3d=new T1(1,I_fromInt(_3h));continue;}}else{_3c=new T1(1,I_fromInt(_3f));_3d=_3g;continue;}}else{var _3j=E(_3d);if(!_3j._){_3c=_3e;_3d=new T1(1,I_fromInt(_3j.a));continue;}else{return new T1(1,I_add(_3e.a,_3j.a));}}}},_3k=function(_3l,_3m){while(1){var _3n=E(_3l);if(!_3n._){var _3o=E(_3n.a);if(_3o==(-2147483648)){_3l=new T1(1,I_fromInt(-2147483648));continue;}else{var _3p=E(_3m);if(!_3p._){var _3q=_3p.a;return new T2(0,new T1(0,quot(_3o,_3q)),new T1(0,_3o%_3q));}else{_3l=new T1(1,I_fromInt(_3o));_3m=_3p;continue;}}}else{var _3r=E(_3m);if(!_3r._){_3l=_3n;_3m=new T1(1,I_fromInt(_3r.a));continue;}else{var _3s=I_quotRem(_3n.a,_3r.a);return new T2(0,new T1(1,_3s.a),new T1(1,_3s.b));}}}},_3t=new T1(0,0),_3u=function(_3v,_3w){while(1){var _3x=E(_3v);if(!_3x._){_3v=new T1(1,I_fromInt(_3x.a));continue;}else{return new T1(1,I_shiftLeft(_3x.a,_3w));}}},_3y=function(_3z,_3A,_3B){if(!B(_30(_3B,_3t))){var _3C=B(_3k(_3A,_3B)),_3D=_3C.a;switch(B(_1N(B(_3u(_3C.b,1)),_3B))){case 0:return new F(function(){return _2W(_3D,_3z);});break;case 1:if(!(B(_38(_3D))&1)){return new F(function(){return _2W(_3D,_3z);});}else{return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}break;default:return new F(function(){return _2W(B(_3b(_3D,_1M)),_3z);});}}else{return E(_2V);}},_3E=function(_3F,_3G){var _3H=E(_3F);if(!_3H._){var _3I=_3H.a,_3J=E(_3G);return (_3J._==0)?_3I>_3J.a:I_compareInt(_3J.a,_3I)<0;}else{var _3K=_3H.a,_3L=E(_3G);return (_3L._==0)?I_compareInt(_3K,_3L.a)>0:I_compare(_3K,_3L.a)>0;}},_3M=new T1(0,1),_3N=function(_3O,_3P){var _3Q=E(_3O);if(!_3Q._){var _3R=_3Q.a,_3S=E(_3P);return (_3S._==0)?_3R<_3S.a:I_compareInt(_3S.a,_3R)>0;}else{var _3T=_3Q.a,_3U=E(_3P);return (_3U._==0)?I_compareInt(_3T,_3U.a)<0:I_compare(_3T,_3U.a)<0;}},_3V=new T(function(){return B(unCStr("base"));}),_3W=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3X=new T(function(){return B(unCStr("PatternMatchFail"));}),_3Y=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3V,_3W,_3X),_3Z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3Y,_o,_o),_40=function(_41){return E(_3Z);},_42=function(_43){var _44=E(_43);return new F(function(){return _28(B(_26(_44.a)),_40,_44.b);});},_45=function(_46){return E(E(_46).a);},_47=function(_48){return new T2(0,_49,_48);},_4a=function(_4b,_4c){return new F(function(){return _f(E(_4b).a,_4c);});},_4d=function(_4e,_4f){return new F(function(){return _2B(_4a,_4e,_4f);});},_4g=function(_4h,_4i,_4j){return new F(function(){return _f(E(_4i).a,_4j);});},_4k=new T3(0,_4g,_45,_4d),_49=new T(function(){return new T5(0,_40,_4k,_47,_42,_45);}),_4l=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4m=function(_4n){return E(E(_4n).c);},_4o=function(_4p,_4q){return new F(function(){return die(new T(function(){return B(A2(_4m,_4q,_4p));}));});},_4r=function(_4s,_2S){return new F(function(){return _4o(_4s,_2S);});},_4t=function(_4u,_4v){var _4w=E(_4v);if(!_4w._){return new T2(0,_o,_o);}else{var _4x=_4w.a;if(!B(A1(_4u,_4x))){return new T2(0,_o,_4w);}else{var _4y=new T(function(){var _4z=B(_4t(_4u,_4w.b));return new T2(0,_4z.a,_4z.b);});return new T2(0,new T2(1,_4x,new T(function(){return E(E(_4y).a);})),new T(function(){return E(E(_4y).b);}));}}},_4A=32,_4B=new T(function(){return B(unCStr("\n"));}),_4C=function(_4D){return (E(_4D)==124)?false:true;},_4E=function(_4F,_4G){var _4H=B(_4t(_4C,B(unCStr(_4F)))),_4I=_4H.a,_4J=function(_4K,_4L){var _4M=new T(function(){var _4N=new T(function(){return B(_f(_4G,new T(function(){return B(_f(_4L,_4B));},1)));});return B(unAppCStr(": ",_4N));},1);return new F(function(){return _f(_4K,_4M);});},_4O=E(_4H.b);if(!_4O._){return new F(function(){return _4J(_4I,_o);});}else{if(E(_4O.a)==124){return new F(function(){return _4J(_4I,new T2(1,_4A,_4O.b));});}else{return new F(function(){return _4J(_4I,_o);});}}},_4P=function(_4Q){return new F(function(){return _4r(new T1(0,new T(function(){return B(_4E(_4Q,_4l));})),_49);});},_4R=function(_4S){var _4T=function(_4U,_4V){while(1){if(!B(_3N(_4U,_4S))){if(!B(_3E(_4U,_4S))){if(!B(_30(_4U,_4S))){return new F(function(){return _4P("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_4V);}}else{return _4V-1|0;}}else{var _4W=B(_3u(_4U,1)),_4X=_4V+1|0;_4U=_4W;_4V=_4X;continue;}}};return new F(function(){return _4T(_3M,0);});},_4Y=function(_4Z){var _50=E(_4Z);if(!_50._){var _51=_50.a>>>0;if(!_51){return -1;}else{var _52=function(_53,_54){while(1){if(_53>=_51){if(_53<=_51){if(_53!=_51){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_54);}}else{return _54-1|0;}}else{var _55=imul(_53,2)>>>0,_56=_54+1|0;_53=_55;_54=_56;continue;}}};return new F(function(){return _52(1,0);});}}else{return new F(function(){return _4R(_50);});}},_57=function(_58){var _59=E(_58);if(!_59._){var _5a=_59.a>>>0;if(!_5a){return new T2(0,-1,0);}else{var _5b=function(_5c,_5d){while(1){if(_5c>=_5a){if(_5c<=_5a){if(_5c!=_5a){return new F(function(){return _4P("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_5d);}}else{return _5d-1|0;}}else{var _5e=imul(_5c,2)>>>0,_5f=_5d+1|0;_5c=_5e;_5d=_5f;continue;}}};return new T2(0,B(_5b(1,0)),(_5a&_5a-1>>>0)>>>0&4294967295);}}else{var _5g=_59.a;return new T2(0,B(_4Y(_59)),I_compareInt(I_and(_5g,I_sub(_5g,I_fromInt(1))),0));}},_5h=function(_5i,_5j){var _5k=E(_5i);if(!_5k._){var _5l=_5k.a,_5m=E(_5j);return (_5m._==0)?_5l<=_5m.a:I_compareInt(_5m.a,_5l)>=0;}else{var _5n=_5k.a,_5o=E(_5j);return (_5o._==0)?I_compareInt(_5n,_5o.a)<=0:I_compare(_5n,_5o.a)<=0;}},_5p=function(_5q,_5r){while(1){var _5s=E(_5q);if(!_5s._){var _5t=_5s.a,_5u=E(_5r);if(!_5u._){return new T1(0,(_5t>>>0&_5u.a>>>0)>>>0&4294967295);}else{_5q=new T1(1,I_fromInt(_5t));_5r=_5u;continue;}}else{var _5v=E(_5r);if(!_5v._){_5q=_5s;_5r=new T1(1,I_fromInt(_5v.a));continue;}else{return new T1(1,I_and(_5s.a,_5v.a));}}}},_5w=function(_5x,_5y){while(1){var _5z=E(_5x);if(!_5z._){var _5A=_5z.a,_5B=E(_5y);if(!_5B._){var _5C=_5B.a,_5D=subC(_5A,_5C);if(!E(_5D.b)){return new T1(0,_5D.a);}else{_5x=new T1(1,I_fromInt(_5A));_5y=new T1(1,I_fromInt(_5C));continue;}}else{_5x=new T1(1,I_fromInt(_5A));_5y=_5B;continue;}}else{var _5E=E(_5y);if(!_5E._){_5x=_5z;_5y=new T1(1,I_fromInt(_5E.a));continue;}else{return new T1(1,I_sub(_5z.a,_5E.a));}}}},_5F=new T1(0,2),_5G=function(_5H,_5I){var _5J=E(_5H);if(!_5J._){var _5K=(_5J.a>>>0&(2<<_5I>>>0)-1>>>0)>>>0,_5L=1<<_5I>>>0;return (_5L<=_5K)?(_5L>=_5K)?1:2:0;}else{var _5M=B(_5p(_5J,B(_5w(B(_3u(_5F,_5I)),_3M)))),_5N=B(_3u(_3M,_5I));return (!B(_3E(_5N,_5M)))?(!B(_3N(_5N,_5M)))?1:2:0;}},_5O=function(_5P,_5Q){while(1){var _5R=E(_5P);if(!_5R._){_5P=new T1(1,I_fromInt(_5R.a));continue;}else{return new T1(1,I_shiftRight(_5R.a,_5Q));}}},_5S=function(_5T,_5U,_5V,_5W){var _5X=B(_57(_5W)),_5Y=_5X.a;if(!E(_5X.b)){var _5Z=B(_4Y(_5V));if(_5Z<((_5Y+_5T|0)-1|0)){var _60=_5Y+(_5T-_5U|0)|0;if(_60>0){if(_60>_5Z){if(_60<=(_5Z+1|0)){if(!E(B(_57(_5V)).b)){return 0;}else{return new F(function(){return _2W(_1M,_5T-_5U|0);});}}else{return 0;}}else{var _61=B(_5O(_5V,_60));switch(B(_5G(_5V,_60-1|0))){case 0:return new F(function(){return _2W(_61,_5T-_5U|0);});break;case 1:if(!(B(_38(_61))&1)){return new F(function(){return _2W(_61,_5T-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}break;default:return new F(function(){return _2W(B(_3b(_61,_1M)),_5T-_5U|0);});}}}else{return new F(function(){return _2W(_5V,(_5T-_5U|0)-_60|0);});}}else{if(_5Z>=_5U){var _62=B(_5O(_5V,(_5Z+1|0)-_5U|0));switch(B(_5G(_5V,_5Z-_5U|0))){case 0:return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});break;case 2:return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});break;default:if(!(B(_38(_62))&1)){return new F(function(){return _2W(_62,((_5Z-_5Y|0)+1|0)-_5U|0);});}else{return new F(function(){return _2W(B(_3b(_62,_1M)),((_5Z-_5Y|0)+1|0)-_5U|0);});}}}else{return new F(function(){return _2W(_5V, -_5Y);});}}}else{var _63=B(_4Y(_5V))-_5Y|0,_64=function(_65){var _66=function(_67,_68){if(!B(_5h(B(_3u(_68,_5U)),_67))){return new F(function(){return _3y(_65-_5U|0,_67,_68);});}else{return new F(function(){return _3y((_65-_5U|0)+1|0,_67,B(_3u(_68,1)));});}};if(_65>=_5U){if(_65!=_5U){return new F(function(){return _66(_5V,new T(function(){return B(_3u(_5W,_65-_5U|0));}));});}else{return new F(function(){return _66(_5V,_5W);});}}else{return new F(function(){return _66(new T(function(){return B(_3u(_5V,_5U-_65|0));}),_5W);});}};if(_5T>_63){return new F(function(){return _64(_5T);});}else{return new F(function(){return _64(_63);});}}},_69=new T1(0,2147483647),_6a=new T(function(){return B(_3b(_69,_3M));}),_6b=function(_6c){var _6d=E(_6c);if(!_6d._){var _6e=E(_6d.a);return (_6e==(-2147483648))?E(_6a):new T1(0, -_6e);}else{return new T1(1,I_negate(_6d.a));}},_6f=new T(function(){return 0/0;}),_6g=new T(function(){return -1/0;}),_6h=new T(function(){return 1/0;}),_6i=0,_6j=function(_6k,_6l){if(!B(_30(_6l,_3t))){if(!B(_30(_6k,_3t))){if(!B(_3N(_6k,_3t))){return new F(function(){return _5S(-1021,53,_6k,_6l);});}else{return  -B(_5S(-1021,53,B(_6b(_6k)),_6l));}}else{return E(_6i);}}else{return (!B(_30(_6k,_3t)))?(!B(_3N(_6k,_3t)))?E(_6h):E(_6g):E(_6f);}},_6m=function(_6n){return new T1(0,new T(function(){var _6o=E(_6n),_6p=jsShow(B(_6j(_6o.a,_6o.b)));return fromJSStr(_6p);}));},_6q=new T(function(){return B(unCStr("1./("));}),_6r=new T1(0,_6q),_6s=function(_6t){return new T1(1,new T2(1,_6r,new T2(1,_6t,_w)));},_6u=new T(function(){return B(unCStr(")+("));}),_6v=new T1(0,_6u),_6w=function(_6x,_6y){return new T1(1,new T2(1,_1G,new T2(1,_6x,new T2(1,_6v,new T2(1,_6y,_w)))));},_6z=new T(function(){return B(unCStr("-("));}),_6A=new T1(0,_6z),_6B=function(_6C){return new T1(1,new T2(1,_6A,new T2(1,_6C,_w)));},_6D=new T(function(){return B(unCStr(")*("));}),_6E=new T1(0,_6D),_6F=function(_6G,_6H){return new T1(1,new T2(1,_1G,new T2(1,_6G,new T2(1,_6E,new T2(1,_6H,_w)))));},_6I=function(_6J){return E(E(_6J).a);},_6K=function(_6L){return E(E(_6L).d);},_6M=function(_6N,_6O){return new F(function(){return A3(_6I,_6P,_6N,new T(function(){return B(A2(_6K,_6P,_6O));}));});},_6Q=new T(function(){return B(unCStr("abs("));}),_6R=new T1(0,_6Q),_6S=function(_6T){return new T1(1,new T2(1,_6R,new T2(1,_6T,_w)));},_6U=function(_6V){while(1){var _6W=E(_6V);if(!_6W._){_6V=new T1(1,I_fromInt(_6W.a));continue;}else{return new F(function(){return I_toString(_6W.a);});}}},_6X=function(_6Y,_6Z){return new F(function(){return _f(fromJSStr(B(_6U(_6Y))),_6Z);});},_70=41,_71=40,_72=new T1(0,0),_73=function(_74,_75,_76){if(_74<=6){return new F(function(){return _6X(_75,_76);});}else{if(!B(_3N(_75,_72))){return new F(function(){return _6X(_75,_76);});}else{return new T2(1,_71,new T(function(){return B(_f(fromJSStr(B(_6U(_75))),new T2(1,_70,_76)));}));}}},_77=new T(function(){return B(unCStr("."));}),_78=function(_79){return new T1(0,new T(function(){return B(_f(B(_73(0,_79,_o)),_77));}));},_7a=new T(function(){return B(unCStr("sign("));}),_7b=new T1(0,_7a),_7c=function(_7d){return new T1(1,new T2(1,_7b,new T2(1,_7d,_w)));},_6P=new T(function(){return {_:0,a:_6w,b:_6M,c:_6F,d:_6B,e:_6S,f:_7c,g:_78};}),_7e=new T4(0,_6P,_1J,_6s,_6m),_7f={_:0,a:_7e,b:_1k,c:_18,d:_1c,e:_1v,f:_x,g:_1g,h:_1n,i:_10,j:_1z,k:_K,l:_C,m:_S,n:_1r,o:_14,p:_1D,q:_O,r:_G,s:_W},_7g=new T1(0,1),_7h=function(_7i){return E(E(_7i).a);},_7j=function(_7k){return E(E(_7k).a);},_7l=function(_7m){return E(E(_7m).c);},_7n=function(_7o,_7p,_7q,_7r,_7s,_7t,_7u){var _7v=B(_7j(B(_7h(_7o)))),_7w=new T(function(){return B(A3(_6I,_7v,new T(function(){return B(A3(_7l,_7v,_7p,_7s));}),new T(function(){return B(A3(_7l,_7v,_7q,_7t));})));});return new F(function(){return A3(_6I,_7v,_7w,new T(function(){return B(A3(_7l,_7v,_7r,_7u));}));});},_7x=function(_7y){return E(E(_7y).b);},_7z=function(_7A){return E(E(_7A).g);},_7B=function(_7C){return E(E(_7C).e);},_7D=function(_7E,_7F){var _7G=B(_7j(B(_7h(_7E)))),_7H=new T(function(){return B(A2(_7B,_7E,new T(function(){var _7I=E(_7F),_7J=_7I.a,_7K=_7I.b,_7L=_7I.c;return B(_7n(_7E,_7J,_7K,_7L,_7J,_7K,_7L));})));});return new F(function(){return A3(_7x,_7G,_7H,new T(function(){return B(A2(_7z,_7G,_7g));}));});},_7M=new T(function(){return B(unCStr("x"));}),_7N=new T1(0,_7M),_7O=new T(function(){return B(unCStr("y"));}),_7P=new T1(0,_7O),_7Q=new T(function(){return B(unCStr("z"));}),_7R=new T1(0,_7Q),_7S=new T3(0,E(_7N),E(_7P),E(_7R)),_7T=new T(function(){return B(_7D(_7f,_7S));}),_7U=function(_7V){return E(_7V);},_7W=new T(function(){return toJSStr(B(_5(_p,_7U,_7T)));}),_7X=function(_7Y,_7Z,_80){var _81=new T(function(){return B(_1(_7Y));}),_82=new T(function(){return B(_3(_7Y));}),_83=function(_84){var _85=E(_84);if(!_85._){return E(_82);}else{return new F(function(){return A2(_81,new T(function(){return B(_5(_7Y,_7Z,_85.a));}),new T(function(){return B(_83(_85.b));}));});}};return new F(function(){return _83(_80);});},_86=new T(function(){return B(unCStr("(/=) is not defined"));}),_87=new T(function(){return B(err(_86));}),_88=new T(function(){return B(unCStr("(==) is not defined"));}),_89=new T(function(){return B(err(_88));}),_8a=new T2(0,_89,_87),_8b=new T(function(){return B(unCStr("(<) is not defined"));}),_8c=new T(function(){return B(err(_8b));}),_8d=new T(function(){return B(unCStr("(<=) is not defined"));}),_8e=new T(function(){return B(err(_8d));}),_8f=new T(function(){return B(unCStr("(>) is not defined"));}),_8g=new T(function(){return B(err(_8f));}),_8h=new T(function(){return B(unCStr("(>=) is not defined"));}),_8i=new T(function(){return B(err(_8h));}),_8j=new T(function(){return B(unCStr("compare is not defined"));}),_8k=new T(function(){return B(err(_8j));}),_8l=new T(function(){return B(unCStr("max("));}),_8m=new T1(0,_8l),_8n=function(_8o,_8p){return new T1(1,new T2(1,_8m,new T2(1,_8o,new T2(1,_r,new T2(1,_8p,_w)))));},_8q=new T(function(){return B(unCStr("min("));}),_8r=new T1(0,_8q),_8s=function(_8t,_8u){return new T1(1,new T2(1,_8r,new T2(1,_8t,new T2(1,_r,new T2(1,_8u,_w)))));},_8v={_:0,a:_8a,b:_8k,c:_8c,d:_8e,e:_8g,f:_8i,g:_8n,h:_8s},_8w=new T2(0,_7f,_8v),_8x=function(_8y,_8z){var _8A=E(_8y);return E(_8z);},_8B=function(_8C,_8D){var _8E=E(_8D);return E(_8C);},_8F=function(_8G,_8H){var _8I=E(_8G),_8J=E(_8H);return new T3(0,E(B(A1(_8I.a,_8J.a))),E(B(A1(_8I.b,_8J.b))),E(B(A1(_8I.c,_8J.c))));},_8K=function(_8L,_8M,_8N){return new T3(0,E(_8L),E(_8M),E(_8N));},_8O=function(_8P){return new F(function(){return _8K(_8P,_8P,_8P);});},_8Q=function(_8R,_8S){var _8T=E(_8S),_8U=E(_8R);return new T3(0,E(_8U),E(_8U),E(_8U));},_8V=function(_8W,_8X){var _8Y=E(_8X);return new T3(0,E(B(A1(_8W,_8Y.a))),E(B(A1(_8W,_8Y.b))),E(B(A1(_8W,_8Y.c))));},_8Z=new T2(0,_8V,_8Q),_90=new T5(0,_8Z,_8O,_8F,_8x,_8B),_91=new T1(0,0),_92=function(_93){var _94=B(A2(_7z,_93,_7g)),_95=B(A2(_7z,_93,_91));return new T3(0,E(new T3(0,E(_94),E(_95),E(_95))),E(new T3(0,E(_95),E(_94),E(_95))),E(new T3(0,E(_95),E(_95),E(_94))));},_96=function(_97){return E(E(_97).a);},_98=function(_99){return E(E(_99).f);},_9a=function(_9b){return E(E(_9b).b);},_9c=function(_9d){return E(E(_9d).c);},_9e=function(_9f){return E(E(_9f).a);},_9g=function(_9h){return E(E(_9h).d);},_9i=function(_9j,_9k,_9l,_9m,_9n){var _9o=new T(function(){return E(E(E(_9j).c).a);}),_9p=new T(function(){var _9q=E(_9j).a,_9r=new T(function(){var _9s=new T(function(){return B(_7h(_9o));}),_9t=new T(function(){return B(_7j(_9s));}),_9u=new T(function(){return B(A2(_9g,_9o,_9k));}),_9v=new T(function(){return B(A3(_98,_9o,_9k,_9m));}),_9w=function(_9x,_9y){var _9z=new T(function(){var _9A=new T(function(){return B(A3(_9a,_9s,new T(function(){return B(A3(_7l,_9t,_9m,_9x));}),_9k));});return B(A3(_6I,_9t,_9A,new T(function(){return B(A3(_7l,_9t,_9y,_9u));})));});return new F(function(){return A3(_7l,_9t,_9v,_9z);});};return B(A3(_9e,B(_96(_9q)),_9w,_9l));});return B(A3(_9c,_9q,_9r,_9n));});return new T2(0,new T(function(){return B(A3(_98,_9o,_9k,_9m));}),_9p);},_9B=function(_9C,_9D,_9E,_9F){var _9G=E(_9E),_9H=E(_9F),_9I=B(_9i(_9D,_9G.a,_9G.b,_9H.a,_9H.b));return new T2(0,_9I.a,_9I.b);},_9J=new T1(0,1),_9K=function(_9L){return E(E(_9L).l);},_9M=function(_9N,_9O,_9P){var _9Q=new T(function(){return E(E(E(_9N).c).a);}),_9R=new T(function(){var _9S=new T(function(){return B(_7h(_9Q));}),_9T=new T(function(){var _9U=B(_7j(_9S)),_9V=new T(function(){var _9W=new T(function(){return B(A3(_7x,_9U,new T(function(){return B(A2(_7z,_9U,_9J));}),new T(function(){return B(A3(_7l,_9U,_9O,_9O));})));});return B(A2(_7B,_9Q,_9W));});return B(A2(_6K,_9U,_9V));});return B(A3(_9e,B(_96(E(_9N).a)),function(_9X){return new F(function(){return A3(_9a,_9S,_9X,_9T);});},_9P));});return new T2(0,new T(function(){return B(A2(_9K,_9Q,_9O));}),_9R);},_9Y=function(_9Z,_a0,_a1){var _a2=E(_a1),_a3=B(_9M(_a0,_a2.a,_a2.b));return new T2(0,_a3.a,_a3.b);},_a4=function(_a5){return E(E(_a5).r);},_a6=function(_a7,_a8,_a9){var _aa=new T(function(){return E(E(E(_a7).c).a);}),_ab=new T(function(){var _ac=new T(function(){return B(_7h(_aa));}),_ad=new T(function(){var _ae=new T(function(){var _af=B(_7j(_ac));return B(A3(_7x,_af,new T(function(){return B(A3(_7l,_af,_a8,_a8));}),new T(function(){return B(A2(_7z,_af,_9J));})));});return B(A2(_7B,_aa,_ae));});return B(A3(_9e,B(_96(E(_a7).a)),function(_ag){return new F(function(){return A3(_9a,_ac,_ag,_ad);});},_a9));});return new T2(0,new T(function(){return B(A2(_a4,_aa,_a8));}),_ab);},_ah=function(_ai,_aj,_ak){var _al=E(_ak),_am=B(_a6(_aj,_al.a,_al.b));return new T2(0,_am.a,_am.b);},_an=function(_ao){return E(E(_ao).k);},_ap=function(_aq,_ar,_as){var _at=new T(function(){return E(E(E(_aq).c).a);}),_au=new T(function(){var _av=new T(function(){return B(_7h(_at));}),_aw=new T(function(){var _ax=new T(function(){var _ay=B(_7j(_av));return B(A3(_7x,_ay,new T(function(){return B(A2(_7z,_ay,_9J));}),new T(function(){return B(A3(_7l,_ay,_ar,_ar));})));});return B(A2(_7B,_at,_ax));});return B(A3(_9e,B(_96(E(_aq).a)),function(_az){return new F(function(){return A3(_9a,_av,_az,_aw);});},_as));});return new T2(0,new T(function(){return B(A2(_an,_at,_ar));}),_au);},_aA=function(_aB,_aC,_aD){var _aE=E(_aD),_aF=B(_ap(_aC,_aE.a,_aE.b));return new T2(0,_aF.a,_aF.b);},_aG=function(_aH){return E(E(_aH).q);},_aI=function(_aJ,_aK,_aL){var _aM=new T(function(){return E(E(E(_aJ).c).a);}),_aN=new T(function(){var _aO=new T(function(){return B(_7h(_aM));}),_aP=new T(function(){var _aQ=new T(function(){var _aR=B(_7j(_aO));return B(A3(_6I,_aR,new T(function(){return B(A3(_7l,_aR,_aK,_aK));}),new T(function(){return B(A2(_7z,_aR,_9J));})));});return B(A2(_7B,_aM,_aQ));});return B(A3(_9e,B(_96(E(_aJ).a)),function(_aS){return new F(function(){return A3(_9a,_aO,_aS,_aP);});},_aL));});return new T2(0,new T(function(){return B(A2(_aG,_aM,_aK));}),_aN);},_aT=function(_aU,_aV,_aW){var _aX=E(_aW),_aY=B(_aI(_aV,_aX.a,_aX.b));return new T2(0,_aY.a,_aY.b);},_aZ=function(_b0){return E(E(_b0).m);},_b1=function(_b2,_b3,_b4){var _b5=new T(function(){return E(E(E(_b2).c).a);}),_b6=new T(function(){var _b7=new T(function(){return B(_7h(_b5));}),_b8=new T(function(){var _b9=B(_7j(_b7));return B(A3(_6I,_b9,new T(function(){return B(A2(_7z,_b9,_9J));}),new T(function(){return B(A3(_7l,_b9,_b3,_b3));})));});return B(A3(_9e,B(_96(E(_b2).a)),function(_ba){return new F(function(){return A3(_9a,_b7,_ba,_b8);});},_b4));});return new T2(0,new T(function(){return B(A2(_aZ,_b5,_b3));}),_b6);},_bb=function(_bc,_bd,_be){var _bf=E(_be),_bg=B(_b1(_bd,_bf.a,_bf.b));return new T2(0,_bg.a,_bg.b);},_bh=function(_bi){return E(E(_bi).s);},_bj=function(_bk,_bl,_bm){var _bn=new T(function(){return E(E(E(_bk).c).a);}),_bo=new T(function(){var _bp=new T(function(){return B(_7h(_bn));}),_bq=new T(function(){var _br=B(_7j(_bp));return B(A3(_7x,_br,new T(function(){return B(A2(_7z,_br,_9J));}),new T(function(){return B(A3(_7l,_br,_bl,_bl));})));});return B(A3(_9e,B(_96(E(_bk).a)),function(_bs){return new F(function(){return A3(_9a,_bp,_bs,_bq);});},_bm));});return new T2(0,new T(function(){return B(A2(_bh,_bn,_bl));}),_bo);},_bt=function(_bu,_bv,_bw){var _bx=E(_bw),_by=B(_bj(_bv,_bx.a,_bx.b));return new T2(0,_by.a,_by.b);},_bz=function(_bA){return E(E(_bA).i);},_bB=function(_bC){return E(E(_bC).h);},_bD=function(_bE,_bF,_bG){var _bH=new T(function(){return E(E(E(_bE).c).a);}),_bI=new T(function(){var _bJ=new T(function(){return B(_7j(new T(function(){return B(_7h(_bH));})));}),_bK=new T(function(){return B(A2(_6K,_bJ,new T(function(){return B(A2(_bB,_bH,_bF));})));});return B(A3(_9e,B(_96(E(_bE).a)),function(_bL){return new F(function(){return A3(_7l,_bJ,_bL,_bK);});},_bG));});return new T2(0,new T(function(){return B(A2(_bz,_bH,_bF));}),_bI);},_bM=function(_bN,_bO,_bP){var _bQ=E(_bP),_bR=B(_bD(_bO,_bQ.a,_bQ.b));return new T2(0,_bR.a,_bR.b);},_bS=function(_bT){return E(E(_bT).o);},_bU=function(_bV){return E(E(_bV).n);},_bW=function(_bX,_bY,_bZ){var _c0=new T(function(){return E(E(E(_bX).c).a);}),_c1=new T(function(){var _c2=new T(function(){return B(_7j(new T(function(){return B(_7h(_c0));})));}),_c3=new T(function(){return B(A2(_bU,_c0,_bY));});return B(A3(_9e,B(_96(E(_bX).a)),function(_c4){return new F(function(){return A3(_7l,_c2,_c4,_c3);});},_bZ));});return new T2(0,new T(function(){return B(A2(_bS,_c0,_bY));}),_c1);},_c5=function(_c6,_c7,_c8){var _c9=E(_c8),_ca=B(_bW(_c7,_c9.a,_c9.b));return new T2(0,_ca.a,_ca.b);},_cb=function(_cc){return E(E(_cc).c);},_cd=function(_ce,_cf,_cg){var _ch=new T(function(){return E(E(E(_ce).c).a);}),_ci=new T(function(){var _cj=new T(function(){return B(_7j(new T(function(){return B(_7h(_ch));})));}),_ck=new T(function(){return B(A2(_cb,_ch,_cf));});return B(A3(_9e,B(_96(E(_ce).a)),function(_cl){return new F(function(){return A3(_7l,_cj,_cl,_ck);});},_cg));});return new T2(0,new T(function(){return B(A2(_cb,_ch,_cf));}),_ci);},_cm=function(_cn,_co,_cp){var _cq=E(_cp),_cr=B(_cd(_co,_cq.a,_cq.b));return new T2(0,_cr.a,_cr.b);},_cs=function(_ct,_cu,_cv){var _cw=new T(function(){return E(E(E(_ct).c).a);}),_cx=new T(function(){var _cy=new T(function(){return B(_7h(_cw));}),_cz=new T(function(){return B(_7j(_cy));}),_cA=new T(function(){return B(A3(_9a,_cy,new T(function(){return B(A2(_7z,_cz,_9J));}),_cu));});return B(A3(_9e,B(_96(E(_ct).a)),function(_cB){return new F(function(){return A3(_7l,_cz,_cB,_cA);});},_cv));});return new T2(0,new T(function(){return B(A2(_9g,_cw,_cu));}),_cx);},_cC=function(_cD,_cE,_cF){var _cG=E(_cF),_cH=B(_cs(_cE,_cG.a,_cG.b));return new T2(0,_cH.a,_cH.b);},_cI=function(_cJ,_cK,_cL,_cM){var _cN=new T(function(){return E(E(_cK).c);}),_cO=new T3(0,new T(function(){return E(E(_cK).a);}),new T(function(){return E(E(_cK).b);}),new T2(0,new T(function(){return E(E(_cN).a);}),new T(function(){return E(E(_cN).b);})));return new F(function(){return A3(_9a,_cJ,new T(function(){var _cP=E(_cM),_cQ=B(_cs(_cO,_cP.a,_cP.b));return new T2(0,_cQ.a,_cQ.b);}),new T(function(){var _cR=E(_cL),_cS=B(_cs(_cO,_cR.a,_cR.b));return new T2(0,_cS.a,_cS.b);}));});},_cT=new T1(0,0),_cU=function(_cV){return E(E(_cV).b);},_cW=function(_cX){return E(E(_cX).b);},_cY=function(_cZ){var _d0=new T(function(){return E(E(E(_cZ).c).a);}),_d1=new T(function(){return B(A2(_cW,E(_cZ).a,new T(function(){return B(A2(_7z,B(_7j(B(_7h(_d0)))),_cT));})));});return new T2(0,new T(function(){return B(_cU(_d0));}),_d1);},_d2=function(_d3,_d4){var _d5=B(_cY(_d4));return new T2(0,_d5.a,_d5.b);},_d6=function(_d7,_d8,_d9){var _da=new T(function(){return E(E(E(_d7).c).a);}),_db=new T(function(){var _dc=new T(function(){return B(_7j(new T(function(){return B(_7h(_da));})));}),_dd=new T(function(){return B(A2(_bz,_da,_d8));});return B(A3(_9e,B(_96(E(_d7).a)),function(_de){return new F(function(){return A3(_7l,_dc,_de,_dd);});},_d9));});return new T2(0,new T(function(){return B(A2(_bB,_da,_d8));}),_db);},_df=function(_dg,_dh,_di){var _dj=E(_di),_dk=B(_d6(_dh,_dj.a,_dj.b));return new T2(0,_dk.a,_dk.b);},_dl=function(_dm,_dn,_do){var _dp=new T(function(){return E(E(E(_dm).c).a);}),_dq=new T(function(){var _dr=new T(function(){return B(_7j(new T(function(){return B(_7h(_dp));})));}),_ds=new T(function(){return B(A2(_bS,_dp,_dn));});return B(A3(_9e,B(_96(E(_dm).a)),function(_dt){return new F(function(){return A3(_7l,_dr,_dt,_ds);});},_do));});return new T2(0,new T(function(){return B(A2(_bU,_dp,_dn));}),_dq);},_du=function(_dv,_dw,_dx){var _dy=E(_dx),_dz=B(_dl(_dw,_dy.a,_dy.b));return new T2(0,_dz.a,_dz.b);},_dA=new T1(0,2),_dB=function(_dC,_dD,_dE){var _dF=new T(function(){return E(E(E(_dC).c).a);}),_dG=new T(function(){var _dH=new T(function(){return B(_7h(_dF));}),_dI=new T(function(){return B(_7j(_dH));}),_dJ=new T(function(){var _dK=new T(function(){return B(A3(_9a,_dH,new T(function(){return B(A2(_7z,_dI,_9J));}),new T(function(){return B(A2(_7z,_dI,_dA));})));});return B(A3(_9a,_dH,_dK,new T(function(){return B(A2(_7B,_dF,_dD));})));});return B(A3(_9e,B(_96(E(_dC).a)),function(_dL){return new F(function(){return A3(_7l,_dI,_dL,_dJ);});},_dE));});return new T2(0,new T(function(){return B(A2(_7B,_dF,_dD));}),_dG);},_dM=function(_dN,_dO,_dP){var _dQ=E(_dP),_dR=B(_dB(_dO,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);},_dS=function(_dT){return E(E(_dT).j);},_dU=function(_dV,_dW,_dX){var _dY=new T(function(){return E(E(E(_dV).c).a);}),_dZ=new T(function(){var _e0=new T(function(){return B(_7h(_dY));}),_e1=new T(function(){var _e2=new T(function(){return B(A2(_bz,_dY,_dW));});return B(A3(_7l,B(_7j(_e0)),_e2,_e2));});return B(A3(_9e,B(_96(E(_dV).a)),function(_e3){return new F(function(){return A3(_9a,_e0,_e3,_e1);});},_dX));});return new T2(0,new T(function(){return B(A2(_dS,_dY,_dW));}),_dZ);},_e4=function(_e5,_e6,_e7){var _e8=E(_e7),_e9=B(_dU(_e6,_e8.a,_e8.b));return new T2(0,_e9.a,_e9.b);},_ea=function(_eb){return E(E(_eb).p);},_ec=function(_ed,_ee,_ef){var _eg=new T(function(){return E(E(E(_ed).c).a);}),_eh=new T(function(){var _ei=new T(function(){return B(_7h(_eg));}),_ej=new T(function(){var _ek=new T(function(){return B(A2(_bS,_eg,_ee));});return B(A3(_7l,B(_7j(_ei)),_ek,_ek));});return B(A3(_9e,B(_96(E(_ed).a)),function(_el){return new F(function(){return A3(_9a,_ei,_el,_ej);});},_ef));});return new T2(0,new T(function(){return B(A2(_ea,_eg,_ee));}),_eh);},_em=function(_en,_eo,_ep){var _eq=E(_ep),_er=B(_ec(_eo,_eq.a,_eq.b));return new T2(0,_er.a,_er.b);},_es=function(_et,_eu){return {_:0,a:_et,b:new T(function(){return B(_d2(_et,_eu));}),c:function(_ev){return new F(function(){return _cm(_et,_eu,_ev);});},d:function(_ev){return new F(function(){return _cC(_et,_eu,_ev);});},e:function(_ev){return new F(function(){return _dM(_et,_eu,_ev);});},f:function(_ew,_ev){return new F(function(){return _9B(_et,_eu,_ew,_ev);});},g:function(_ew,_ev){return new F(function(){return _cI(_et,_eu,_ew,_ev);});},h:function(_ev){return new F(function(){return _df(_et,_eu,_ev);});},i:function(_ev){return new F(function(){return _bM(_et,_eu,_ev);});},j:function(_ev){return new F(function(){return _e4(_et,_eu,_ev);});},k:function(_ev){return new F(function(){return _aA(_et,_eu,_ev);});},l:function(_ev){return new F(function(){return _9Y(_et,_eu,_ev);});},m:function(_ev){return new F(function(){return _bb(_et,_eu,_ev);});},n:function(_ev){return new F(function(){return _du(_et,_eu,_ev);});},o:function(_ev){return new F(function(){return _c5(_et,_eu,_ev);});},p:function(_ev){return new F(function(){return _em(_et,_eu,_ev);});},q:function(_ev){return new F(function(){return _aT(_et,_eu,_ev);});},r:function(_ev){return new F(function(){return _ah(_et,_eu,_ev);});},s:function(_ev){return new F(function(){return _bt(_et,_eu,_ev);});}};},_ex=function(_ey,_ez,_eA,_eB,_eC){var _eD=new T(function(){return B(_7h(new T(function(){return E(E(E(_ey).c).a);})));}),_eE=new T(function(){var _eF=E(_ey).a,_eG=new T(function(){var _eH=new T(function(){return B(_7j(_eD));}),_eI=new T(function(){return B(A3(_7l,_eH,_eB,_eB));}),_eJ=function(_eK,_eL){var _eM=new T(function(){return B(A3(_7x,_eH,new T(function(){return B(A3(_7l,_eH,_eK,_eB));}),new T(function(){return B(A3(_7l,_eH,_ez,_eL));})));});return new F(function(){return A3(_9a,_eD,_eM,_eI);});};return B(A3(_9e,B(_96(_eF)),_eJ,_eA));});return B(A3(_9c,_eF,_eG,_eC));});return new T2(0,new T(function(){return B(A3(_9a,_eD,_ez,_eB));}),_eE);},_eN=function(_eO,_eP,_eQ,_eR){var _eS=E(_eQ),_eT=E(_eR),_eU=B(_ex(_eP,_eS.a,_eS.b,_eT.a,_eT.b));return new T2(0,_eU.a,_eU.b);},_eV=function(_eW){return E(E(_eW).d);},_eX=function(_eY,_eZ){var _f0=new T(function(){return B(_7h(new T(function(){return E(E(E(_eY).c).a);})));}),_f1=new T(function(){return B(A2(_cW,E(_eY).a,new T(function(){return B(A2(_7z,B(_7j(_f0)),_cT));})));});return new T2(0,new T(function(){return B(A2(_eV,_f0,_eZ));}),_f1);},_f2=function(_f3,_f4,_f5){var _f6=B(_eX(_f4,_f5));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8,_f9,_fa){var _fb=new T(function(){return B(_7h(new T(function(){return E(E(E(_f8).c).a);})));}),_fc=new T(function(){return B(_7j(_fb));}),_fd=new T(function(){var _fe=new T(function(){var _ff=new T(function(){return B(A3(_9a,_fb,new T(function(){return B(A2(_7z,_fc,_9J));}),new T(function(){return B(A3(_7l,_fc,_f9,_f9));})));});return B(A2(_6K,_fc,_ff));});return B(A3(_9e,B(_96(E(_f8).a)),function(_fg){return new F(function(){return A3(_7l,_fc,_fg,_fe);});},_fa));}),_fh=new T(function(){return B(A3(_9a,_fb,new T(function(){return B(A2(_7z,_fc,_9J));}),_f9));});return new T2(0,_fh,_fd);},_fi=function(_fj,_fk,_fl){var _fm=E(_fl),_fn=B(_f7(_fk,_fm.a,_fm.b));return new T2(0,_fn.a,_fn.b);},_fo=function(_fp,_fq){return new T4(0,_fp,function(_ew,_ev){return new F(function(){return _eN(_fp,_fq,_ew,_ev);});},function(_ev){return new F(function(){return _fi(_fp,_fq,_ev);});},function(_ev){return new F(function(){return _f2(_fp,_fq,_ev);});});},_fr=function(_fs,_ft,_fu,_fv,_fw){var _fx=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_fs).c).a);})));})));}),_fy=new T(function(){var _fz=E(_fs).a,_fA=new T(function(){var _fB=function(_fC,_fD){return new F(function(){return A3(_6I,_fx,new T(function(){return B(A3(_7l,_fx,_ft,_fD));}),new T(function(){return B(A3(_7l,_fx,_fC,_fv));}));});};return B(A3(_9e,B(_96(_fz)),_fB,_fu));});return B(A3(_9c,_fz,_fA,_fw));});return new T2(0,new T(function(){return B(A3(_7l,_fx,_ft,_fv));}),_fy);},_fE=function(_fF,_fG,_fH){var _fI=E(_fG),_fJ=E(_fH),_fK=B(_fr(_fF,_fI.a,_fI.b,_fJ.a,_fJ.b));return new T2(0,_fK.a,_fK.b);},_fL=function(_fM,_fN,_fO,_fP,_fQ){var _fR=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_fM).c).a);})));})));}),_fS=new T(function(){var _fT=E(_fM).a,_fU=new T(function(){return B(A3(_9e,B(_96(_fT)),new T(function(){return B(_6I(_fR));}),_fO));});return B(A3(_9c,_fT,_fU,_fQ));});return new T2(0,new T(function(){return B(A3(_6I,_fR,_fN,_fP));}),_fS);},_fV=function(_fW,_fX,_fY){var _fZ=E(_fX),_g0=E(_fY),_g1=B(_fL(_fW,_fZ.a,_fZ.b,_g0.a,_g0.b));return new T2(0,_g1.a,_g1.b);},_g2=function(_g3,_g4,_g5){var _g6=B(_g7(_g3));return new F(function(){return A3(_6I,_g6,_g4,new T(function(){return B(A2(_6K,_g6,_g5));}));});},_g8=function(_g9){return E(E(_g9).e);},_ga=function(_gb){return E(E(_gb).f);},_gc=function(_gd,_ge,_gf){var _gg=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gd).c).a);})));})));}),_gh=new T(function(){var _gi=new T(function(){return B(A2(_ga,_gg,_ge));});return B(A3(_9e,B(_96(E(_gd).a)),function(_gj){return new F(function(){return A3(_7l,_gg,_gj,_gi);});},_gf));});return new T2(0,new T(function(){return B(A2(_g8,_gg,_ge));}),_gh);},_gk=function(_gl,_gm){var _gn=E(_gm),_go=B(_gc(_gl,_gn.a,_gn.b));return new T2(0,_go.a,_go.b);},_gp=function(_gq,_gr){var _gs=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gq).c).a);})));})));}),_gt=new T(function(){return B(A2(_cW,E(_gq).a,new T(function(){return B(A2(_7z,_gs,_cT));})));});return new T2(0,new T(function(){return B(A2(_7z,_gs,_gr));}),_gt);},_gu=function(_gv,_gw){var _gx=B(_gp(_gv,_gw));return new T2(0,_gx.a,_gx.b);},_gy=function(_gz,_gA,_gB){var _gC=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gz).c).a);})));})));}),_gD=new T(function(){return B(A3(_9e,B(_96(E(_gz).a)),new T(function(){return B(_6K(_gC));}),_gB));});return new T2(0,new T(function(){return B(A2(_6K,_gC,_gA));}),_gD);},_gE=function(_gF,_gG){var _gH=E(_gG),_gI=B(_gy(_gF,_gH.a,_gH.b));return new T2(0,_gI.a,_gI.b);},_gJ=function(_gK,_gL){var _gM=new T(function(){return B(_7j(new T(function(){return B(_7h(new T(function(){return E(E(E(_gK).c).a);})));})));}),_gN=new T(function(){return B(A2(_cW,E(_gK).a,new T(function(){return B(A2(_7z,_gM,_cT));})));});return new T2(0,new T(function(){return B(A2(_ga,_gM,_gL));}),_gN);},_gO=function(_gP,_gQ){var _gR=B(_gJ(_gP,E(_gQ).a));return new T2(0,_gR.a,_gR.b);},_g7=function(_gS){return {_:0,a:function(_ew,_ev){return new F(function(){return _fV(_gS,_ew,_ev);});},b:function(_ew,_ev){return new F(function(){return _g2(_gS,_ew,_ev);});},c:function(_ew,_ev){return new F(function(){return _fE(_gS,_ew,_ev);});},d:function(_ev){return new F(function(){return _gE(_gS,_ev);});},e:function(_ev){return new F(function(){return _gk(_gS,_ev);});},f:function(_ev){return new F(function(){return _gO(_gS,_ev);});},g:function(_ev){return new F(function(){return _gu(_gS,_ev);});}};},_gT=function(_gU){var _gV=new T(function(){return E(E(_gU).a);}),_gW=new T3(0,_90,_92,new T2(0,_gV,new T(function(){return E(E(_gU).b);}))),_gX=new T(function(){return B(_es(new T(function(){return B(_fo(new T(function(){return B(_g7(_gW));}),_gW));}),_gW));}),_gY=new T(function(){return B(_7j(new T(function(){return B(_7h(_gV));})));}),_gZ=function(_h0){return E(B(_7D(_gX,new T(function(){var _h1=E(_h0),_h2=B(A2(_7z,_gY,_7g)),_h3=B(A2(_7z,_gY,_91));return new T3(0,E(new T2(0,_h1.a,new T3(0,E(_h2),E(_h3),E(_h3)))),E(new T2(0,_h1.b,new T3(0,E(_h3),E(_h2),E(_h3)))),E(new T2(0,_h1.c,new T3(0,E(_h3),E(_h3),E(_h2)))));}))).b);};return E(_gZ);},_h4=new T(function(){return B(_gT(_8w));}),_h5=function(_h6,_h7){var _h8=E(_h7);return (_h8._==0)?__Z:new T2(1,_h6,new T2(1,_h8.a,new T(function(){return B(_h5(_h6,_h8.b));})));},_h9=new T(function(){var _ha=B(A1(_h4,_7S));return new T2(1,_ha.a,new T(function(){return B(_h5(_r,new T2(1,_ha.b,new T2(1,_ha.c,_o))));}));}),_hb=new T1(1,_h9),_hc=new T2(1,_hb,_w),_hd=new T(function(){return B(unCStr("vec3("));}),_he=new T1(0,_hd),_hf=new T2(1,_he,_hc),_hg=new T(function(){return toJSStr(B(_7X(_p,_7U,_hf)));}),_hh=function(_hi,_hj){while(1){var _hk=E(_hi);if(!_hk._){return E(_hj);}else{var _hl=_hj+1|0;_hi=_hk.b;_hj=_hl;continue;}}},_hm=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_hn=new T(function(){return B(err(_hm));}),_ho=0,_hp=new T3(0,E(_ho),E(_ho),E(_ho)),_hq=new T(function(){return B(unCStr("Negative exponent"));}),_hr=new T(function(){return B(err(_hq));}),_hs=function(_ht,_hu,_hv){while(1){if(!(_hu%2)){var _hw=_ht*_ht,_hx=quot(_hu,2);_ht=_hw;_hu=_hx;continue;}else{var _hy=E(_hu);if(_hy==1){return _ht*_hv;}else{var _hw=_ht*_ht,_hz=_ht*_hv;_ht=_hw;_hu=quot(_hy-1|0,2);_hv=_hz;continue;}}}},_hA=function(_hB,_hC){while(1){if(!(_hC%2)){var _hD=_hB*_hB,_hE=quot(_hC,2);_hB=_hD;_hC=_hE;continue;}else{var _hF=E(_hC);if(_hF==1){return E(_hB);}else{return new F(function(){return _hs(_hB*_hB,quot(_hF-1|0,2),_hB);});}}}},_hG=function(_hH){var _hI=E(_hH);return new F(function(){return Math.log(_hI+(_hI+1)*Math.sqrt((_hI-1)/(_hI+1)));});},_hJ=function(_hK){var _hL=E(_hK);return new F(function(){return Math.log(_hL+Math.sqrt(1+_hL*_hL));});},_hM=function(_hN){var _hO=E(_hN);return 0.5*Math.log((1+_hO)/(1-_hO));},_hP=function(_hQ,_hR){return Math.log(E(_hR))/Math.log(E(_hQ));},_hS=3.141592653589793,_hT=function(_hU){var _hV=E(_hU);return new F(function(){return _6j(_hV.a,_hV.b);});},_hW=function(_hX){return 1/E(_hX);},_hY=function(_hZ){var _i0=E(_hZ),_i1=E(_i0);return (_i1==0)?E(_6i):(_i1<=0)? -_i1:E(_i0);},_i2=function(_i3){var _i4=E(_i3);if(!_i4._){return _i4.a;}else{return new F(function(){return I_toNumber(_i4.a);});}},_i5=function(_i6){return new F(function(){return _i2(_i6);});},_i7=1,_i8=-1,_i9=function(_ia){var _ib=E(_ia);return (_ib<=0)?(_ib>=0)?E(_ib):E(_i8):E(_i7);},_ic=function(_id,_ie){return E(_id)-E(_ie);},_if=function(_ig){return  -E(_ig);},_ih=function(_ii,_ij){return E(_ii)+E(_ij);},_ik=function(_il,_im){return E(_il)*E(_im);},_in={_:0,a:_ih,b:_ic,c:_ik,d:_if,e:_hY,f:_i9,g:_i5},_io=function(_ip,_iq){return E(_ip)/E(_iq);},_ir=new T4(0,_in,_io,_hW,_hT),_is=function(_it){return new F(function(){return Math.acos(E(_it));});},_iu=function(_iv){return new F(function(){return Math.asin(E(_iv));});},_iw=function(_ix){return new F(function(){return Math.atan(E(_ix));});},_iy=function(_iz){return new F(function(){return Math.cos(E(_iz));});},_iA=function(_iB){return new F(function(){return cosh(E(_iB));});},_iC=function(_iD){return new F(function(){return Math.exp(E(_iD));});},_iE=function(_iF){return new F(function(){return Math.log(E(_iF));});},_iG=function(_iH,_iI){return new F(function(){return Math.pow(E(_iH),E(_iI));});},_iJ=function(_iK){return new F(function(){return Math.sin(E(_iK));});},_iL=function(_iM){return new F(function(){return sinh(E(_iM));});},_iN=function(_iO){return new F(function(){return Math.sqrt(E(_iO));});},_iP=function(_iQ){return new F(function(){return Math.tan(E(_iQ));});},_iR=function(_iS){return new F(function(){return tanh(E(_iS));});},_iT={_:0,a:_ir,b:_hS,c:_iC,d:_iE,e:_iN,f:_iG,g:_hP,h:_iJ,i:_iy,j:_iP,k:_iu,l:_is,m:_iw,n:_iL,o:_iA,p:_iR,q:_hJ,r:_hG,s:_hM},_iU=function(_iV,_iW){return (E(_iV)!=E(_iW))?true:false;},_iX=function(_iY,_iZ){return E(_iY)==E(_iZ);},_j0=new T2(0,_iX,_iU),_j1=function(_j2,_j3){return E(_j2)<E(_j3);},_j4=function(_j5,_j6){return E(_j5)<=E(_j6);},_j7=function(_j8,_j9){return E(_j8)>E(_j9);},_ja=function(_jb,_jc){return E(_jb)>=E(_jc);},_jd=function(_je,_jf){var _jg=E(_je),_jh=E(_jf);return (_jg>=_jh)?(_jg!=_jh)?2:1:0;},_ji=function(_jj,_jk){var _jl=E(_jj),_jm=E(_jk);return (_jl>_jm)?E(_jl):E(_jm);},_jn=function(_jo,_jp){var _jq=E(_jo),_jr=E(_jp);return (_jq>_jr)?E(_jr):E(_jq);},_js={_:0,a:_j0,b:_jd,c:_j1,d:_j4,e:_j7,f:_ja,g:_ji,h:_jn},_jt="dz",_ju="wy",_jv="wx",_jw="dy",_jx="dx",_jy="t",_jz="a",_jA="r",_jB="ly",_jC="lx",_jD="wz",_jE=0,_jF=function(_jG){var _jH=__new(),_jI=_jH,_jJ=function(_jK,_){while(1){var _jL=E(_jK);if(!_jL._){return _jE;}else{var _jM=E(_jL.a),_jN=__set(_jI,E(_jM.a),E(_jM.b));_jK=_jL.b;continue;}}},_jO=B(_jJ(_jG,_));return E(_jI);},_jP=function(_jQ,_jR,_jS,_jT,_jU,_jV,_jW,_jX,_jY){return new F(function(){return _jF(new T2(1,new T2(0,_jv,_jQ),new T2(1,new T2(0,_ju,_jR),new T2(1,new T2(0,_jD,_jS),new T2(1,new T2(0,_jC,_jT*_jU*Math.cos(_jV)),new T2(1,new T2(0,_jB,_jT*_jU*Math.sin(_jV)),new T2(1,new T2(0,_jA,_jT),new T2(1,new T2(0,_jz,_jU),new T2(1,new T2(0,_jy,_jV),new T2(1,new T2(0,_jx,_jW),new T2(1,new T2(0,_jw,_jX),new T2(1,new T2(0,_jt,_jY),_o))))))))))));});},_jZ=function(_k0){var _k1=E(_k0),_k2=E(_k1.a),_k3=E(_k1.b),_k4=E(_k1.d);return new F(function(){return _jP(_k2.a,_k2.b,_k2.c,E(_k3.a),E(_k3.b),E(_k1.c),_k4.a,_k4.b,_k4.c);});},_k5=function(_k6,_k7){var _k8=E(_k7);return (_k8._==0)?__Z:new T2(1,new T(function(){return B(A1(_k6,_k8.a));}),new T(function(){return B(_k5(_k6,_k8.b));}));},_k9=function(_ka,_kb,_kc){var _kd=__lst2arr(B(_k5(_jZ,new T2(1,_ka,new T2(1,_kb,new T2(1,_kc,_o))))));return E(_kd);},_ke=function(_kf){var _kg=E(_kf);return new F(function(){return _k9(_kg.a,_kg.b,_kg.c);});},_kh=new T2(0,_iT,_js),_ki=function(_kj,_kk,_kl,_km){var _kn=B(_7h(_kj)),_ko=new T(function(){return B(A2(_7B,_kj,new T(function(){return B(_7n(_kj,_kk,_kl,_km,_kk,_kl,_km));})));});return new T3(0,B(A3(_9a,_kn,_kk,_ko)),B(A3(_9a,_kn,_kl,_ko)),B(A3(_9a,_kn,_km,_ko)));},_kp=function(_kq,_kr,_ks,_kt,_ku,_kv,_kw){var _kx=B(_7l(_kq));return new T3(0,B(A1(B(A1(_kx,_kr)),_ku)),B(A1(B(A1(_kx,_ks)),_kv)),B(A1(B(A1(_kx,_kt)),_kw)));},_ky=function(_kz,_kA,_kB,_kC,_kD,_kE,_kF){var _kG=B(_6I(_kz));return new T3(0,B(A1(B(A1(_kG,_kA)),_kD)),B(A1(B(A1(_kG,_kB)),_kE)),B(A1(B(A1(_kG,_kC)),_kF)));},_kH=function(_kI,_kJ){var _kK=new T(function(){return E(E(_kI).a);}),_kL=new T(function(){return B(A2(_gT,new T2(0,_kK,new T(function(){return E(E(_kI).b);})),_kJ));}),_kM=new T(function(){var _kN=E(_kL),_kO=B(_ki(_kK,_kN.a,_kN.b,_kN.c));return new T3(0,E(_kO.a),E(_kO.b),E(_kO.c));}),_kP=new T(function(){var _kQ=E(_kJ),_kR=E(_kM),_kS=B(_7h(_kK)),_kT=new T(function(){return B(A2(_7B,_kK,new T(function(){var _kU=E(_kL),_kV=_kU.a,_kW=_kU.b,_kX=_kU.c;return B(_7n(_kK,_kV,_kW,_kX,_kV,_kW,_kX));})));}),_kY=B(A3(_9a,_kS,new T(function(){return B(_7D(_kK,_kQ));}),_kT)),_kZ=B(_7j(_kS)),_l0=B(_kp(_kZ,_kR.a,_kR.b,_kR.c,_kY,_kY,_kY)),_l1=B(_6K(_kZ)),_l2=B(_ky(_kZ,_kQ.a,_kQ.b,_kQ.c,B(A1(_l1,_l0.a)),B(A1(_l1,_l0.b)),B(A1(_l1,_l0.c))));return new T3(0,E(_l2.a),E(_l2.b),E(_l2.c));});return new T2(0,_kP,_kM);},_l3=function(_l4){return E(E(_l4).a);},_l5=function(_l6,_l7,_l8,_l9,_la,_lb,_lc){var _ld=B(_7n(_l6,_la,_lb,_lc,_l7,_l8,_l9)),_le=B(_7j(B(_7h(_l6)))),_lf=B(_kp(_le,_la,_lb,_lc,_ld,_ld,_ld)),_lg=B(_6K(_le));return new F(function(){return _ky(_le,_l7,_l8,_l9,B(A1(_lg,_lf.a)),B(A1(_lg,_lf.b)),B(A1(_lg,_lf.c)));});},_lh=function(_li){return E(E(_li).a);},_lj=function(_lk,_ll,_lm,_ln){var _lo=new T(function(){var _lp=E(_ln),_lq=E(_lm),_lr=B(_l5(_lk,_lp.a,_lp.b,_lp.c,_lq.a,_lq.b,_lq.c));return new T3(0,E(_lr.a),E(_lr.b),E(_lr.c));}),_ls=new T(function(){return B(A2(_7B,_lk,new T(function(){var _lt=E(_lo),_lu=_lt.a,_lv=_lt.b,_lw=_lt.c;return B(_7n(_lk,_lu,_lv,_lw,_lu,_lv,_lw));})));});if(!B(A3(_lh,B(_l3(_ll)),_ls,new T(function(){return B(A2(_7z,B(_7j(B(_7h(_lk)))),_91));})))){var _lx=E(_lo),_ly=B(_ki(_lk,_lx.a,_lx.b,_lx.c)),_lz=B(A2(_7B,_lk,new T(function(){var _lA=E(_ln),_lB=_lA.a,_lC=_lA.b,_lD=_lA.c;return B(_7n(_lk,_lB,_lC,_lD,_lB,_lC,_lD));}))),_lE=B(_7l(new T(function(){return B(_7j(new T(function(){return B(_7h(_lk));})));})));return new T3(0,B(A1(B(A1(_lE,_ly.a)),_lz)),B(A1(B(A1(_lE,_ly.b)),_lz)),B(A1(B(A1(_lE,_ly.c)),_lz)));}else{var _lF=B(A2(_7z,B(_7j(B(_7h(_lk)))),_91));return new T3(0,_lF,_lF,_lF);}},_lG=new T(function(){var _lH=eval("angleCount"),_lI=Number(_lH);return jsTrunc(_lI);}),_lJ=new T(function(){return E(_lG);}),_lK=new T(function(){return B(unCStr(": empty list"));}),_lL=new T(function(){return B(unCStr("Prelude."));}),_lM=function(_lN){return new F(function(){return err(B(_f(_lL,new T(function(){return B(_f(_lN,_lK));},1))));});},_lO=new T(function(){return B(unCStr("head"));}),_lP=new T(function(){return B(_lM(_lO));}),_lQ=function(_lR,_lS,_lT){var _lU=E(_lR);if(!_lU._){return __Z;}else{var _lV=E(_lS);if(!_lV._){return __Z;}else{var _lW=_lV.a,_lX=E(_lT);if(!_lX._){return __Z;}else{var _lY=E(_lX.a),_lZ=_lY.a;return new F(function(){return _f(new T2(1,new T(function(){return new T3(0,E(_lU.a),E(_lW),E(_lZ));}),new T2(1,new T(function(){return new T3(0,E(_lW),E(_lZ),E(_lY.b));}),_o)),new T(function(){return B(_lQ(_lU.b,_lV.b,_lX.b));},1));});}}}},_m0=new T(function(){return B(unCStr("tail"));}),_m1=new T(function(){return B(_lM(_m0));}),_m2=function(_m3,_m4){var _m5=E(_m3);if(!_m5._){return __Z;}else{var _m6=E(_m4);return (_m6._==0)?__Z:new T2(1,new T2(0,_m5.a,_m6.a),new T(function(){return B(_m2(_m5.b,_m6.b));}));}},_m7=function(_m8,_m9){var _ma=E(_m8);if(!_ma._){return __Z;}else{var _mb=E(_m9);if(!_mb._){return __Z;}else{var _mc=E(_ma.a),_md=_mc.b,_me=E(_mb.a).b,_mf=new T(function(){var _mg=new T(function(){return B(_m2(_me,new T(function(){var _mh=E(_me);if(!_mh._){return E(_m1);}else{return E(_mh.b);}},1)));},1);return B(_lQ(_md,new T(function(){var _mi=E(_md);if(!_mi._){return E(_m1);}else{return E(_mi.b);}},1),_mg));});return new F(function(){return _f(new T2(1,new T(function(){var _mj=E(_md);if(!_mj._){return E(_lP);}else{var _mk=E(_me);if(!_mk._){return E(_lP);}else{return new T3(0,E(_mc.a),E(_mj.a),E(_mk.a));}}}),_mf),new T(function(){return B(_m7(_ma.b,_mb.b));},1));});}}},_ml=new T(function(){return E(_lJ)-1;}),_mm=new T1(0,1),_mn=function(_mo,_mp){var _mq=E(_mp),_mr=new T(function(){var _ms=B(_7j(_mo)),_mt=B(_mn(_mo,B(A3(_6I,_ms,_mq,new T(function(){return B(A2(_7z,_ms,_mm));})))));return new T2(1,_mt.a,_mt.b);});return new T2(0,_mq,_mr);},_mu=function(_mv){return E(E(_mv).d);},_mw=new T1(0,2),_mx=function(_my,_mz){var _mA=E(_mz);if(!_mA._){return __Z;}else{var _mB=_mA.a;return (!B(A1(_my,_mB)))?__Z:new T2(1,_mB,new T(function(){return B(_mx(_my,_mA.b));}));}},_mC=function(_mD,_mE,_mF,_mG){var _mH=B(_mn(_mE,_mF)),_mI=new T(function(){var _mJ=B(_7j(_mE)),_mK=new T(function(){return B(A3(_9a,_mE,new T(function(){return B(A2(_7z,_mJ,_mm));}),new T(function(){return B(A2(_7z,_mJ,_mw));})));});return B(A3(_6I,_mJ,_mG,_mK));});return new F(function(){return _mx(function(_mL){return new F(function(){return A3(_mu,_mD,_mL,_mI);});},new T2(1,_mH.a,_mH.b));});},_mM=new T(function(){return B(_mC(_js,_ir,_ho,_ml));}),_mN=function(_mO,_mP){while(1){var _mQ=E(_mO);if(!_mQ._){return E(_mP);}else{_mO=_mQ.b;_mP=_mQ.a;continue;}}},_mR=new T(function(){return B(unCStr("last"));}),_mS=new T(function(){return B(_lM(_mR));}),_mT=function(_mU){return new F(function(){return _mN(_mU,_mS);});},_mV=function(_mW){return new F(function(){return _mT(E(_mW).b);});},_mX=new T(function(){var _mY=eval("proceedCount"),_mZ=Number(_mY);return jsTrunc(_mZ);}),_n0=new T(function(){return E(_mX);}),_n1=1,_n2=new T(function(){return B(_mC(_js,_ir,_n1,_n0));}),_n3=function(_n4,_n5,_n6,_n7,_n8,_n9,_na,_nb,_nc,_nd,_ne,_nf,_ng,_nh){var _ni=new T(function(){var _nj=new T(function(){var _nk=E(_nd),_nl=E(_nh),_nm=E(_ng),_nn=E(_ne),_no=E(_nf),_np=E(_nc);return new T3(0,_nk*_nl-_nm*_nn,_nn*_no-_nl*_np,_np*_nm-_no*_nk);}),_nq=function(_nr){var _ns=new T(function(){var _nt=E(_nr)/E(_lJ);return (_nt+_nt)*3.141592653589793;}),_nu=new T(function(){return B(A1(_n4,_ns));}),_nv=new T(function(){var _nw=new T(function(){var _nx=E(_nu)/E(_n0);return new T3(0,E(_nx),E(_nx),E(_nx));}),_ny=function(_nz,_nA){var _nB=E(_nz);if(!_nB._){return new T2(0,_o,_nA);}else{var _nC=new T(function(){var _nD=B(_kH(_kh,new T(function(){var _nE=E(_nA),_nF=E(_nE.a),_nG=E(_nE.b),_nH=E(_nw);return new T3(0,E(_nF.a)+E(_nG.a)*E(_nH.a),E(_nF.b)+E(_nG.b)*E(_nH.b),E(_nF.c)+E(_nG.c)*E(_nH.c));}))),_nI=_nD.a,_nJ=new T(function(){var _nK=E(_nD.b),_nL=E(E(_nA).b),_nM=B(_l5(_iT,_nL.a,_nL.b,_nL.c,_nK.a,_nK.b,_nK.c)),_nN=B(_ki(_iT,_nM.a,_nM.b,_nM.c));return new T3(0,E(_nN.a),E(_nN.b),E(_nN.c));});return new T2(0,new T(function(){var _nO=E(_nu),_nP=E(_ns);return new T4(0,E(_nI),E(new T2(0,E(_nB.a)/E(_n0),E(_nO))),E(_nP),E(_nJ));}),new T2(0,_nI,_nJ));}),_nQ=new T(function(){var _nR=B(_ny(_nB.b,new T(function(){return E(E(_nC).b);})));return new T2(0,_nR.a,_nR.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nC).a);}),new T(function(){return E(E(_nQ).a);})),new T(function(){return E(E(_nQ).b);}));}},_nS=function(_nT,_nU,_nV,_nW,_nX){var _nY=E(_nT);if(!_nY._){return new T2(0,_o,new T2(0,new T3(0,E(_nU),E(_nV),E(_nW)),_nX));}else{var _nZ=new T(function(){var _o0=B(_kH(_kh,new T(function(){var _o1=E(_nX),_o2=E(_nw);return new T3(0,E(_nU)+E(_o1.a)*E(_o2.a),E(_nV)+E(_o1.b)*E(_o2.b),E(_nW)+E(_o1.c)*E(_o2.c));}))),_o3=_o0.a,_o4=new T(function(){var _o5=E(_o0.b),_o6=E(_nX),_o7=B(_l5(_iT,_o6.a,_o6.b,_o6.c,_o5.a,_o5.b,_o5.c)),_o8=B(_ki(_iT,_o7.a,_o7.b,_o7.c));return new T3(0,E(_o8.a),E(_o8.b),E(_o8.c));});return new T2(0,new T(function(){var _o9=E(_nu),_oa=E(_ns);return new T4(0,E(_o3),E(new T2(0,E(_nY.a)/E(_n0),E(_o9))),E(_oa),E(_o4));}),new T2(0,_o3,_o4));}),_ob=new T(function(){var _oc=B(_ny(_nY.b,new T(function(){return E(E(_nZ).b);})));return new T2(0,_oc.a,_oc.b);});return new T2(0,new T2(1,new T(function(){return E(E(_nZ).a);}),new T(function(){return E(E(_ob).a);})),new T(function(){return E(E(_ob).b);}));}};return E(B(_nS(_n2,_n7,_n8,_n9,new T(function(){var _od=E(_nj),_oe=E(_ns)+_na,_of=Math.cos(_oe),_og=Math.sin(_oe);return new T3(0,E(_nc)*_of+E(_od.a)*_og,E(_nd)*_of+E(_od.b)*_og,E(_ne)*_of+E(_od.c)*_og);}))).a);});return new T2(0,new T(function(){var _oh=E(_nu),_oi=E(_ns);return new T4(0,E(new T3(0,E(_n7),E(_n8),E(_n9))),E(new T2(0,E(_ho),E(_oh))),E(_oi),E(_hp));}),_nv);};return B(_k5(_nq,_mM));}),_oj=new T(function(){var _ok=new T(function(){var _ol=B(_f(_ni,new T2(1,new T(function(){var _om=E(_ni);if(!_om._){return E(_lP);}else{return E(_om.a);}}),_o)));if(!_ol._){return E(_m1);}else{return E(_ol.b);}},1);return B(_m7(_ni,_ok));});return new T2(0,_oj,new T(function(){return B(_k5(_mV,_ni));}));},_on=function(_oo,_op,_oq,_or,_os,_ot,_ou,_ov,_ow,_ox,_oy,_oz,_oA,_oB,_oC,_oD,_oE){var _oF=B(_kH(_kh,new T3(0,E(_or),E(_os),E(_ot)))),_oG=_oF.b,_oH=E(_oF.a),_oI=B(_lj(_iT,_js,_oG,new T3(0,E(_ov),E(_ow),E(_ox)))),_oJ=E(_oG),_oK=_oJ.a,_oL=_oJ.b,_oM=_oJ.c,_oN=B(_l5(_iT,_oz,_oA,_oB,_oK,_oL,_oM)),_oO=B(_ki(_iT,_oN.a,_oN.b,_oN.c)),_oP=_oO.a,_oQ=_oO.b,_oR=_oO.c,_oS=E(_ou),_oT=new T2(0,E(new T3(0,E(_oI.a),E(_oI.b),E(_oI.c))),E(_oy)),_oU=B(_n3(_oo,_op,_oq,_oH.a,_oH.b,_oH.c,_oS,_oT,_oP,_oQ,_oR,_oK,_oL,_oM)),_oV=__lst2arr(B(_k5(_ke,_oU.a))),_oW=__lst2arr(B(_k5(_jZ,_oU.b)));return {_:0,a:_oo,b:_op,c:_oq,d:new T2(0,E(_oH),E(_oS)),e:_oT,f:new T3(0,E(_oP),E(_oQ),E(_oR)),g:_oJ,h:_oV,i:_oW};},_oX=new T(function(){return 6.283185307179586/E(_lJ);}),_oY=0.4,_oZ=new T3(0,E(_oY),E(_oY),E(_oY)),_p0=function(_){return new F(function(){return __jsNull();});},_p1=function(_p2){var _p3=B(A1(_p2,_));return E(_p3);},_p4=new T(function(){return B(_p1(_p0));}),_p5=function(_p6,_p7,_p8,_p9,_pa,_pb,_pc,_pd,_pe,_pf,_pg,_ph,_pi){var _pj=function(_pk){var _pl=E(_oX),_pm=2+_pk|0,_pn=_pm-1|0,_po=(2+_pk)*(1+_pk),_pp=E(_mM);if(!_pp._){return _pl*0;}else{var _pq=_pp.a,_pr=_pp.b,_ps=B(A1(_p6,new T(function(){return 6.283185307179586*E(_pq)/E(_lJ);}))),_pt=B(A1(_p6,new T(function(){return 6.283185307179586*(E(_pq)+1)/E(_lJ);})));if(_ps!=_pt){if(_pm>=0){var _pu=E(_pm);if(!_pu){var _pv=function(_pw,_px){while(1){var _py=B((function(_pz,_pA){var _pB=E(_pz);if(!_pB._){return E(_pA);}else{var _pC=_pB.a,_pD=_pB.b,_pE=B(A1(_p6,new T(function(){return 6.283185307179586*E(_pC)/E(_lJ);}))),_pF=B(A1(_p6,new T(function(){return 6.283185307179586*(E(_pC)+1)/E(_lJ);})));if(_pE!=_pF){var _pG=_pA+0/(_pE-_pF)/_po;_pw=_pD;_px=_pG;return __continue;}else{if(_pn>=0){var _pH=E(_pn);if(!_pH){var _pG=_pA+_pm/_po;_pw=_pD;_px=_pG;return __continue;}else{var _pG=_pA+_pm*B(_hA(_pE,_pH))/_po;_pw=_pD;_px=_pG;return __continue;}}else{return E(_hr);}}}})(_pw,_px));if(_py!=__continue){return _py;}}};return _pl*B(_pv(_pr,0/(_ps-_pt)/_po));}else{var _pI=function(_pJ,_pK){while(1){var _pL=B((function(_pM,_pN){var _pO=E(_pM);if(!_pO._){return E(_pN);}else{var _pP=_pO.a,_pQ=_pO.b,_pR=B(A1(_p6,new T(function(){return 6.283185307179586*E(_pP)/E(_lJ);}))),_pS=B(A1(_p6,new T(function(){return 6.283185307179586*(E(_pP)+1)/E(_lJ);})));if(_pR!=_pS){if(_pu>=0){var _pT=_pN+(B(_hA(_pR,_pu))-B(_hA(_pS,_pu)))/(_pR-_pS)/_po;_pJ=_pQ;_pK=_pT;return __continue;}else{return E(_hr);}}else{if(_pn>=0){var _pU=E(_pn);if(!_pU){var _pT=_pN+_pm/_po;_pJ=_pQ;_pK=_pT;return __continue;}else{var _pT=_pN+_pm*B(_hA(_pR,_pU))/_po;_pJ=_pQ;_pK=_pT;return __continue;}}else{return E(_hr);}}}})(_pJ,_pK));if(_pL!=__continue){return _pL;}}};return _pl*B(_pI(_pr,(B(_hA(_ps,_pu))-B(_hA(_pt,_pu)))/(_ps-_pt)/_po));}}else{return E(_hr);}}else{if(_pn>=0){var _pV=E(_pn);if(!_pV){var _pW=function(_pX,_pY){while(1){var _pZ=B((function(_q0,_q1){var _q2=E(_q0);if(!_q2._){return E(_q1);}else{var _q3=_q2.a,_q4=_q2.b,_q5=B(A1(_p6,new T(function(){return 6.283185307179586*E(_q3)/E(_lJ);}))),_q6=B(A1(_p6,new T(function(){return 6.283185307179586*(E(_q3)+1)/E(_lJ);})));if(_q5!=_q6){if(_pm>=0){var _q7=E(_pm);if(!_q7){var _q8=_q1+0/(_q5-_q6)/_po;_pX=_q4;_pY=_q8;return __continue;}else{var _q8=_q1+(B(_hA(_q5,_q7))-B(_hA(_q6,_q7)))/(_q5-_q6)/_po;_pX=_q4;_pY=_q8;return __continue;}}else{return E(_hr);}}else{var _q8=_q1+_pm/_po;_pX=_q4;_pY=_q8;return __continue;}}})(_pX,_pY));if(_pZ!=__continue){return _pZ;}}};return _pl*B(_pW(_pr,_pm/_po));}else{var _q9=function(_qa,_qb){while(1){var _qc=B((function(_qd,_qe){var _qf=E(_qd);if(!_qf._){return E(_qe);}else{var _qg=_qf.a,_qh=_qf.b,_qi=B(A1(_p6,new T(function(){return 6.283185307179586*E(_qg)/E(_lJ);}))),_qj=B(A1(_p6,new T(function(){return 6.283185307179586*(E(_qg)+1)/E(_lJ);})));if(_qi!=_qj){if(_pm>=0){var _qk=E(_pm);if(!_qk){var _ql=_qe+0/(_qi-_qj)/_po;_qa=_qh;_qb=_ql;return __continue;}else{var _ql=_qe+(B(_hA(_qi,_qk))-B(_hA(_qj,_qk)))/(_qi-_qj)/_po;_qa=_qh;_qb=_ql;return __continue;}}else{return E(_hr);}}else{if(_pV>=0){var _ql=_qe+_pm*B(_hA(_qi,_pV))/_po;_qa=_qh;_qb=_ql;return __continue;}else{return E(_hr);}}}})(_qa,_qb));if(_qc!=__continue){return _qc;}}};return _pl*B(_q9(_pr,_pm*B(_hA(_ps,_pV))/_po));}}else{return E(_hr);}}}},_qm=E(_p4),_qn=1/(B(_pj(1))*_p7);return new F(function(){return _on(_p6,_oZ,new T2(0,E(new T3(0,E(_qn),E(_qn),E(_qn))),1/(B(_pj(3))*_p7)),_p8,_p9,_pa,_pb,_pc,_pd,_pe,_pf,_pg,_ph,_pi,_hp,_qm,_qm);});},_qo=1,_qp=0,_qq=0.4,_qr=function(_qs){var _qt=I_decodeDouble(_qs);return new T2(0,new T1(1,_qt.b),_qt.a);},_qu=function(_qv){return new T1(0,_qv);},_qw=function(_qx){var _qy=hs_intToInt64(2147483647),_qz=hs_leInt64(_qx,_qy);if(!_qz){return new T1(1,I_fromInt64(_qx));}else{var _qA=hs_intToInt64(-2147483648),_qB=hs_geInt64(_qx,_qA);if(!_qB){return new T1(1,I_fromInt64(_qx));}else{var _qC=hs_int64ToInt(_qx);return new F(function(){return _qu(_qC);});}}},_qD=new T(function(){var _qE=newByteArr(256),_qF=_qE,_=_qF["v"]["i8"][0]=8,_qG=function(_qH,_qI,_qJ,_){while(1){if(_qJ>=256){if(_qH>=256){return E(_);}else{var _qK=imul(2,_qH)|0,_qL=_qI+1|0,_qM=_qH;_qH=_qK;_qI=_qL;_qJ=_qM;continue;}}else{var _=_qF["v"]["i8"][_qJ]=_qI,_qM=_qJ+_qH|0;_qJ=_qM;continue;}}},_=B(_qG(2,0,1,_));return _qF;}),_qN=function(_qO,_qP){var _qQ=hs_int64ToInt(_qO),_qR=E(_qD),_qS=_qR["v"]["i8"][(255&_qQ>>>0)>>>0&4294967295];if(_qP>_qS){if(_qS>=8){var _qT=hs_uncheckedIShiftRA64(_qO,8),_qU=function(_qV,_qW){while(1){var _qX=B((function(_qY,_qZ){var _r0=hs_int64ToInt(_qY),_r1=_qR["v"]["i8"][(255&_r0>>>0)>>>0&4294967295];if(_qZ>_r1){if(_r1>=8){var _r2=hs_uncheckedIShiftRA64(_qY,8),_r3=_qZ-8|0;_qV=_r2;_qW=_r3;return __continue;}else{return new T2(0,new T(function(){var _r4=hs_uncheckedIShiftRA64(_qY,_r1);return B(_qw(_r4));}),_qZ-_r1|0);}}else{return new T2(0,new T(function(){var _r5=hs_uncheckedIShiftRA64(_qY,_qZ);return B(_qw(_r5));}),0);}})(_qV,_qW));if(_qX!=__continue){return _qX;}}};return new F(function(){return _qU(_qT,_qP-8|0);});}else{return new T2(0,new T(function(){var _r6=hs_uncheckedIShiftRA64(_qO,_qS);return B(_qw(_r6));}),_qP-_qS|0);}}else{return new T2(0,new T(function(){var _r7=hs_uncheckedIShiftRA64(_qO,_qP);return B(_qw(_r7));}),0);}},_r8=function(_r9){var _ra=hs_intToInt64(_r9);return E(_ra);},_rb=function(_rc){var _rd=E(_rc);if(!_rd._){return new F(function(){return _r8(_rd.a);});}else{return new F(function(){return I_toInt64(_rd.a);});}},_re=function(_rf){return I_toInt(_rf)>>>0;},_rg=function(_rh){var _ri=E(_rh);if(!_ri._){return _ri.a>>>0;}else{return new F(function(){return _re(_ri.a);});}},_rj=function(_rk){var _rl=B(_qr(_rk)),_rm=_rl.a,_rn=_rl.b;if(_rn<0){var _ro=function(_rp){if(!_rp){return new T2(0,E(_rm),B(_3u(_1M, -_rn)));}else{var _rq=B(_qN(B(_rb(_rm)), -_rn));return new T2(0,E(_rq.a),B(_3u(_1M,_rq.b)));}};if(!((B(_rg(_rm))&1)>>>0)){return new F(function(){return _ro(1);});}else{return new F(function(){return _ro(0);});}}else{return new T2(0,B(_3u(_rm,_rn)),_1M);}},_rr=function(_rs){var _rt=B(_rj(E(_rs)));return new T2(0,E(_rt.a),E(_rt.b));},_ru=new T3(0,_in,_js,_rr),_rv=function(_rw){return E(E(_rw).a);},_rx=function(_ry){return E(E(_ry).a);},_rz=function(_rA,_rB){if(_rA<=_rB){var _rC=function(_rD){return new T2(1,_rD,new T(function(){if(_rD!=_rB){return B(_rC(_rD+1|0));}else{return __Z;}}));};return new F(function(){return _rC(_rA);});}else{return __Z;}},_rE=function(_rF){return new F(function(){return _rz(E(_rF),2147483647);});},_rG=function(_rH,_rI,_rJ){if(_rJ<=_rI){var _rK=new T(function(){var _rL=_rI-_rH|0,_rM=function(_rN){return (_rN>=(_rJ-_rL|0))?new T2(1,_rN,new T(function(){return B(_rM(_rN+_rL|0));})):new T2(1,_rN,_o);};return B(_rM(_rI));});return new T2(1,_rH,_rK);}else{return (_rJ<=_rH)?new T2(1,_rH,_o):__Z;}},_rO=function(_rP,_rQ,_rR){if(_rR>=_rQ){var _rS=new T(function(){var _rT=_rQ-_rP|0,_rU=function(_rV){return (_rV<=(_rR-_rT|0))?new T2(1,_rV,new T(function(){return B(_rU(_rV+_rT|0));})):new T2(1,_rV,_o);};return B(_rU(_rQ));});return new T2(1,_rP,_rS);}else{return (_rR>=_rP)?new T2(1,_rP,_o):__Z;}},_rW=function(_rX,_rY){if(_rY<_rX){return new F(function(){return _rG(_rX,_rY,-2147483648);});}else{return new F(function(){return _rO(_rX,_rY,2147483647);});}},_rZ=function(_s0,_s1){return new F(function(){return _rW(E(_s0),E(_s1));});},_s2=function(_s3,_s4,_s5){if(_s4<_s3){return new F(function(){return _rG(_s3,_s4,_s5);});}else{return new F(function(){return _rO(_s3,_s4,_s5);});}},_s6=function(_s7,_s8,_s9){return new F(function(){return _s2(E(_s7),E(_s8),E(_s9));});},_sa=function(_sb,_sc){return new F(function(){return _rz(E(_sb),E(_sc));});},_sd=function(_se){return E(_se);},_sf=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_sg=new T(function(){return B(err(_sf));}),_sh=function(_si){var _sj=E(_si);return (_sj==(-2147483648))?E(_sg):_sj-1|0;},_sk=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_sl=new T(function(){return B(err(_sk));}),_sm=function(_sn){var _so=E(_sn);return (_so==2147483647)?E(_sl):_so+1|0;},_sp={_:0,a:_sm,b:_sh,c:_sd,d:_sd,e:_rE,f:_rZ,g:_sa,h:_s6},_sq=function(_sr,_ss){if(_sr<=0){if(_sr>=0){return new F(function(){return quot(_sr,_ss);});}else{if(_ss<=0){return new F(function(){return quot(_sr,_ss);});}else{return quot(_sr+1|0,_ss)-1|0;}}}else{if(_ss>=0){if(_sr>=0){return new F(function(){return quot(_sr,_ss);});}else{if(_ss<=0){return new F(function(){return quot(_sr,_ss);});}else{return quot(_sr+1|0,_ss)-1|0;}}}else{return quot(_sr-1|0,_ss)-1|0;}}},_st=0,_su=new T(function(){return B(_2R(_st));}),_sv=new T(function(){return die(_su);}),_sw=function(_sx,_sy){var _sz=E(_sy);switch(_sz){case -1:var _sA=E(_sx);if(_sA==(-2147483648)){return E(_sv);}else{return new F(function(){return _sq(_sA,-1);});}break;case 0:return E(_2V);default:return new F(function(){return _sq(_sx,_sz);});}},_sB=function(_sC,_sD){return new F(function(){return _sw(E(_sC),E(_sD));});},_sE=0,_sF=new T2(0,_sv,_sE),_sG=function(_sH,_sI){var _sJ=E(_sH),_sK=E(_sI);switch(_sK){case -1:var _sL=E(_sJ);if(_sL==(-2147483648)){return E(_sF);}else{if(_sL<=0){if(_sL>=0){var _sM=quotRemI(_sL,-1);return new T2(0,_sM.a,_sM.b);}else{var _sN=quotRemI(_sL,-1);return new T2(0,_sN.a,_sN.b);}}else{var _sO=quotRemI(_sL-1|0,-1);return new T2(0,_sO.a-1|0,(_sO.b+(-1)|0)+1|0);}}break;case 0:return E(_2V);default:if(_sJ<=0){if(_sJ>=0){var _sP=quotRemI(_sJ,_sK);return new T2(0,_sP.a,_sP.b);}else{if(_sK<=0){var _sQ=quotRemI(_sJ,_sK);return new T2(0,_sQ.a,_sQ.b);}else{var _sR=quotRemI(_sJ+1|0,_sK);return new T2(0,_sR.a-1|0,(_sR.b+_sK|0)-1|0);}}}else{if(_sK>=0){if(_sJ>=0){var _sS=quotRemI(_sJ,_sK);return new T2(0,_sS.a,_sS.b);}else{if(_sK<=0){var _sT=quotRemI(_sJ,_sK);return new T2(0,_sT.a,_sT.b);}else{var _sU=quotRemI(_sJ+1|0,_sK);return new T2(0,_sU.a-1|0,(_sU.b+_sK|0)-1|0);}}}else{var _sV=quotRemI(_sJ-1|0,_sK);return new T2(0,_sV.a-1|0,(_sV.b+_sK|0)+1|0);}}}},_sW=function(_sX,_sY){var _sZ=_sX%_sY;if(_sX<=0){if(_sX>=0){return E(_sZ);}else{if(_sY<=0){return E(_sZ);}else{var _t0=E(_sZ);return (_t0==0)?0:_t0+_sY|0;}}}else{if(_sY>=0){if(_sX>=0){return E(_sZ);}else{if(_sY<=0){return E(_sZ);}else{var _t1=E(_sZ);return (_t1==0)?0:_t1+_sY|0;}}}else{var _t2=E(_sZ);return (_t2==0)?0:_t2+_sY|0;}}},_t3=function(_t4,_t5){var _t6=E(_t5);switch(_t6){case -1:return E(_sE);case 0:return E(_2V);default:return new F(function(){return _sW(E(_t4),_t6);});}},_t7=function(_t8,_t9){var _ta=E(_t8),_tb=E(_t9);switch(_tb){case -1:var _tc=E(_ta);if(_tc==(-2147483648)){return E(_sv);}else{return new F(function(){return quot(_tc,-1);});}break;case 0:return E(_2V);default:return new F(function(){return quot(_ta,_tb);});}},_td=function(_te,_tf){var _tg=E(_te),_th=E(_tf);switch(_th){case -1:var _ti=E(_tg);if(_ti==(-2147483648)){return E(_sF);}else{var _tj=quotRemI(_ti,-1);return new T2(0,_tj.a,_tj.b);}break;case 0:return E(_2V);default:var _tk=quotRemI(_tg,_th);return new T2(0,_tk.a,_tk.b);}},_tl=function(_tm,_tn){var _to=E(_tn);switch(_to){case -1:return E(_sE);case 0:return E(_2V);default:return E(_tm)%_to;}},_tp=function(_tq){return new F(function(){return _qu(E(_tq));});},_tr=function(_ts){return new T2(0,E(B(_qu(E(_ts)))),E(_mm));},_tt=function(_tu,_tv){return imul(E(_tu),E(_tv))|0;},_tw=function(_tx,_ty){return E(_tx)+E(_ty)|0;},_tz=function(_tA,_tB){return E(_tA)-E(_tB)|0;},_tC=function(_tD){var _tE=E(_tD);return (_tE<0)? -_tE:E(_tE);},_tF=function(_tG){return new F(function(){return _38(_tG);});},_tH=function(_tI){return  -E(_tI);},_tJ=-1,_tK=0,_tL=1,_tM=function(_tN){var _tO=E(_tN);return (_tO>=0)?(E(_tO)==0)?E(_tK):E(_tL):E(_tJ);},_tP={_:0,a:_tw,b:_tz,c:_tt,d:_tH,e:_tC,f:_tM,g:_tF},_tQ=function(_tR,_tS){return E(_tR)==E(_tS);},_tT=function(_tU,_tV){return E(_tU)!=E(_tV);},_tW=new T2(0,_tQ,_tT),_tX=function(_tY,_tZ){var _u0=E(_tY),_u1=E(_tZ);return (_u0>_u1)?E(_u0):E(_u1);},_u2=function(_u3,_u4){var _u5=E(_u3),_u6=E(_u4);return (_u5>_u6)?E(_u6):E(_u5);},_u7=function(_u8,_u9){return (_u8>=_u9)?(_u8!=_u9)?2:1:0;},_ua=function(_ub,_uc){return new F(function(){return _u7(E(_ub),E(_uc));});},_ud=function(_ue,_uf){return E(_ue)>=E(_uf);},_ug=function(_uh,_ui){return E(_uh)>E(_ui);},_uj=function(_uk,_ul){return E(_uk)<=E(_ul);},_um=function(_un,_uo){return E(_un)<E(_uo);},_up={_:0,a:_tW,b:_ua,c:_um,d:_uj,e:_ug,f:_ud,g:_tX,h:_u2},_uq=new T3(0,_tP,_up,_tr),_ur={_:0,a:_uq,b:_sp,c:_t7,d:_tl,e:_sB,f:_t3,g:_td,h:_sG,i:_tp},_us=new T1(0,2),_ut=function(_uu,_uv){while(1){var _uw=E(_uu);if(!_uw._){var _ux=_uw.a,_uy=E(_uv);if(!_uy._){var _uz=_uy.a;if(!(imul(_ux,_uz)|0)){return new T1(0,imul(_ux,_uz)|0);}else{_uu=new T1(1,I_fromInt(_ux));_uv=new T1(1,I_fromInt(_uz));continue;}}else{_uu=new T1(1,I_fromInt(_ux));_uv=_uy;continue;}}else{var _uA=E(_uv);if(!_uA._){_uu=_uw;_uv=new T1(1,I_fromInt(_uA.a));continue;}else{return new T1(1,I_mul(_uw.a,_uA.a));}}}},_uB=function(_uC,_uD,_uE){while(1){if(!(_uD%2)){var _uF=B(_ut(_uC,_uC)),_uG=quot(_uD,2);_uC=_uF;_uD=_uG;continue;}else{var _uH=E(_uD);if(_uH==1){return new F(function(){return _ut(_uC,_uE);});}else{var _uF=B(_ut(_uC,_uC)),_uI=B(_ut(_uC,_uE));_uC=_uF;_uD=quot(_uH-1|0,2);_uE=_uI;continue;}}}},_uJ=function(_uK,_uL){while(1){if(!(_uL%2)){var _uM=B(_ut(_uK,_uK)),_uN=quot(_uL,2);_uK=_uM;_uL=_uN;continue;}else{var _uO=E(_uL);if(_uO==1){return E(_uK);}else{return new F(function(){return _uB(B(_ut(_uK,_uK)),quot(_uO-1|0,2),_uK);});}}}},_uP=function(_uQ){return E(E(_uQ).b);},_uR=function(_uS){return E(E(_uS).c);},_uT=new T1(0,0),_uU=function(_uV){return E(E(_uV).d);},_uW=function(_uX,_uY){var _uZ=B(_rv(_uX)),_v0=new T(function(){return B(_rx(_uZ));}),_v1=new T(function(){return B(A3(_uU,_uX,_uY,new T(function(){return B(A2(_7z,_v0,_mw));})));});return new F(function(){return A3(_lh,B(_l3(B(_uP(_uZ)))),_v1,new T(function(){return B(A2(_7z,_v0,_uT));}));});},_v2=new T(function(){return B(unCStr("Negative exponent"));}),_v3=new T(function(){return B(err(_v2));}),_v4=function(_v5){return E(E(_v5).c);},_v6=function(_v7,_v8,_v9,_va){var _vb=B(_rv(_v8)),_vc=new T(function(){return B(_rx(_vb));}),_vd=B(_uP(_vb));if(!B(A3(_uR,_vd,_va,new T(function(){return B(A2(_7z,_vc,_uT));})))){if(!B(A3(_lh,B(_l3(_vd)),_va,new T(function(){return B(A2(_7z,_vc,_uT));})))){var _ve=new T(function(){return B(A2(_7z,_vc,_mw));}),_vf=new T(function(){return B(A2(_7z,_vc,_mm));}),_vg=B(_l3(_vd)),_vh=function(_vi,_vj,_vk){while(1){var _vl=B((function(_vm,_vn,_vo){if(!B(_uW(_v8,_vn))){if(!B(A3(_lh,_vg,_vn,_vf))){var _vp=new T(function(){return B(A3(_v4,_v8,new T(function(){return B(A3(_7x,_vc,_vn,_vf));}),_ve));});_vi=new T(function(){return B(A3(_7l,_v7,_vm,_vm));});_vj=_vp;_vk=new T(function(){return B(A3(_7l,_v7,_vm,_vo));});return __continue;}else{return new F(function(){return A3(_7l,_v7,_vm,_vo);});}}else{var _vq=_vo;_vi=new T(function(){return B(A3(_7l,_v7,_vm,_vm));});_vj=new T(function(){return B(A3(_v4,_v8,_vn,_ve));});_vk=_vq;return __continue;}})(_vi,_vj,_vk));if(_vl!=__continue){return _vl;}}},_vr=function(_vs,_vt){while(1){var _vu=B((function(_vv,_vw){if(!B(_uW(_v8,_vw))){if(!B(A3(_lh,_vg,_vw,_vf))){var _vx=new T(function(){return B(A3(_v4,_v8,new T(function(){return B(A3(_7x,_vc,_vw,_vf));}),_ve));});return new F(function(){return _vh(new T(function(){return B(A3(_7l,_v7,_vv,_vv));}),_vx,_vv);});}else{return E(_vv);}}else{_vs=new T(function(){return B(A3(_7l,_v7,_vv,_vv));});_vt=new T(function(){return B(A3(_v4,_v8,_vw,_ve));});return __continue;}})(_vs,_vt));if(_vu!=__continue){return _vu;}}};return new F(function(){return _vr(_v9,_va);});}else{return new F(function(){return A2(_7z,_v7,_mm);});}}else{return E(_v3);}},_vy=new T(function(){return B(err(_v2));}),_vz=function(_vA,_vB){var _vC=B(_qr(_vB)),_vD=_vC.a,_vE=_vC.b,_vF=new T(function(){return B(_rx(new T(function(){return B(_rv(_vA));})));});if(_vE<0){var _vG= -_vE;if(_vG>=0){var _vH=E(_vG);if(!_vH){var _vI=E(_mm);}else{var _vI=B(_uJ(_us,_vH));}if(!B(_30(_vI,_3t))){var _vJ=B(_3k(_vD,_vI));return new T2(0,new T(function(){return B(A2(_7z,_vF,_vJ.a));}),new T(function(){return B(_2W(_vJ.b,_vE));}));}else{return E(_2V);}}else{return E(_vy);}}else{var _vK=new T(function(){var _vL=new T(function(){return B(_v6(_vF,_ur,new T(function(){return B(A2(_7z,_vF,_us));}),_vE));});return B(A3(_7l,_vF,new T(function(){return B(A2(_7z,_vF,_vD));}),_vL));});return new T2(0,_vK,_6i);}},_vM=function(_vN,_vO){var _vP=B(_vz(_vN,E(_vO))),_vQ=_vP.a;if(E(_vP.b)<=0){return E(_vQ);}else{var _vR=B(_rx(B(_rv(_vN))));return new F(function(){return A3(_6I,_vR,_vQ,new T(function(){return B(A2(_7z,_vR,_1M));}));});}},_vS=function(_vT,_vU){var _vV=B(_vz(_vT,E(_vU))),_vW=_vV.a;if(E(_vV.b)>=0){return E(_vW);}else{var _vX=B(_rx(B(_rv(_vT))));return new F(function(){return A3(_7x,_vX,_vW,new T(function(){return B(A2(_7z,_vX,_1M));}));});}},_vY=function(_vZ,_w0){var _w1=B(_vz(_vZ,E(_w0)));return new T2(0,_w1.a,_w1.b);},_w2=function(_w3,_w4){var _w5=B(_vz(_w3,_w4)),_w6=_w5.a,_w7=E(_w5.b),_w8=new T(function(){var _w9=B(_rx(B(_rv(_w3))));if(_w7>=0){return B(A3(_6I,_w9,_w6,new T(function(){return B(A2(_7z,_w9,_1M));})));}else{return B(A3(_7x,_w9,_w6,new T(function(){return B(A2(_7z,_w9,_1M));})));}}),_wa=function(_wb){var _wc=_wb-0.5;return (_wc>=0)?(E(_wc)==0)?(!B(_uW(_w3,_w6)))?E(_w8):E(_w6):E(_w8):E(_w6);},_wd=E(_w7);if(!_wd){return new F(function(){return _wa(0);});}else{if(_wd<=0){var _we= -_wd-0.5;return (_we>=0)?(E(_we)==0)?(!B(_uW(_w3,_w6)))?E(_w8):E(_w6):E(_w8):E(_w6);}else{return new F(function(){return _wa(_wd);});}}},_wf=function(_wg,_wh){return new F(function(){return _w2(_wg,E(_wh));});},_wi=function(_wj,_wk){return E(B(_vz(_wj,E(_wk))).a);},_wl={_:0,a:_ru,b:_ir,c:_vY,d:_wi,e:_wf,f:_vM,g:_vS},_wm=new T1(0,1),_wn=function(_wo,_wp){var _wq=E(_wo);return new T2(0,_wq,new T(function(){var _wr=B(_wn(B(_3b(_wq,_wp)),_wp));return new T2(1,_wr.a,_wr.b);}));},_ws=function(_wt){var _wu=B(_wn(_wt,_wm));return new T2(1,_wu.a,_wu.b);},_wv=function(_ww,_wx){var _wy=B(_wn(_ww,new T(function(){return B(_5w(_wx,_ww));})));return new T2(1,_wy.a,_wy.b);},_wz=new T1(0,0),_wA=function(_wB,_wC){var _wD=E(_wB);if(!_wD._){var _wE=_wD.a,_wF=E(_wC);return (_wF._==0)?_wE>=_wF.a:I_compareInt(_wF.a,_wE)<=0;}else{var _wG=_wD.a,_wH=E(_wC);return (_wH._==0)?I_compareInt(_wG,_wH.a)>=0:I_compare(_wG,_wH.a)>=0;}},_wI=function(_wJ,_wK,_wL){if(!B(_wA(_wK,_wz))){var _wM=function(_wN){return (!B(_3N(_wN,_wL)))?new T2(1,_wN,new T(function(){return B(_wM(B(_3b(_wN,_wK))));})):__Z;};return new F(function(){return _wM(_wJ);});}else{var _wO=function(_wP){return (!B(_3E(_wP,_wL)))?new T2(1,_wP,new T(function(){return B(_wO(B(_3b(_wP,_wK))));})):__Z;};return new F(function(){return _wO(_wJ);});}},_wQ=function(_wR,_wS,_wT){return new F(function(){return _wI(_wR,B(_5w(_wS,_wR)),_wT);});},_wU=function(_wV,_wW){return new F(function(){return _wI(_wV,_wm,_wW);});},_wX=function(_wY){return new F(function(){return _38(_wY);});},_wZ=function(_x0){return new F(function(){return _5w(_x0,_wm);});},_x1=function(_x2){return new F(function(){return _3b(_x2,_wm);});},_x3=function(_x4){return new F(function(){return _qu(E(_x4));});},_x5={_:0,a:_x1,b:_wZ,c:_x3,d:_wX,e:_ws,f:_wv,g:_wU,h:_wQ},_x6=function(_x7,_x8){while(1){var _x9=E(_x7);if(!_x9._){var _xa=E(_x9.a);if(_xa==(-2147483648)){_x7=new T1(1,I_fromInt(-2147483648));continue;}else{var _xb=E(_x8);if(!_xb._){return new T1(0,B(_sq(_xa,_xb.a)));}else{_x7=new T1(1,I_fromInt(_xa));_x8=_xb;continue;}}}else{var _xc=_x9.a,_xd=E(_x8);return (_xd._==0)?new T1(1,I_div(_xc,I_fromInt(_xd.a))):new T1(1,I_div(_xc,_xd.a));}}},_xe=function(_xf,_xg){if(!B(_30(_xg,_uT))){return new F(function(){return _x6(_xf,_xg);});}else{return E(_2V);}},_xh=function(_xi,_xj){while(1){var _xk=E(_xi);if(!_xk._){var _xl=E(_xk.a);if(_xl==(-2147483648)){_xi=new T1(1,I_fromInt(-2147483648));continue;}else{var _xm=E(_xj);if(!_xm._){var _xn=_xm.a;return new T2(0,new T1(0,B(_sq(_xl,_xn))),new T1(0,B(_sW(_xl,_xn))));}else{_xi=new T1(1,I_fromInt(_xl));_xj=_xm;continue;}}}else{var _xo=E(_xj);if(!_xo._){_xi=_xk;_xj=new T1(1,I_fromInt(_xo.a));continue;}else{var _xp=I_divMod(_xk.a,_xo.a);return new T2(0,new T1(1,_xp.a),new T1(1,_xp.b));}}}},_xq=function(_xr,_xs){if(!B(_30(_xs,_uT))){var _xt=B(_xh(_xr,_xs));return new T2(0,_xt.a,_xt.b);}else{return E(_2V);}},_xu=function(_xv,_xw){while(1){var _xx=E(_xv);if(!_xx._){var _xy=E(_xx.a);if(_xy==(-2147483648)){_xv=new T1(1,I_fromInt(-2147483648));continue;}else{var _xz=E(_xw);if(!_xz._){return new T1(0,B(_sW(_xy,_xz.a)));}else{_xv=new T1(1,I_fromInt(_xy));_xw=_xz;continue;}}}else{var _xA=_xx.a,_xB=E(_xw);return (_xB._==0)?new T1(1,I_mod(_xA,I_fromInt(_xB.a))):new T1(1,I_mod(_xA,_xB.a));}}},_xC=function(_xD,_xE){if(!B(_30(_xE,_uT))){return new F(function(){return _xu(_xD,_xE);});}else{return E(_2V);}},_xF=function(_xG,_xH){while(1){var _xI=E(_xG);if(!_xI._){var _xJ=E(_xI.a);if(_xJ==(-2147483648)){_xG=new T1(1,I_fromInt(-2147483648));continue;}else{var _xK=E(_xH);if(!_xK._){return new T1(0,quot(_xJ,_xK.a));}else{_xG=new T1(1,I_fromInt(_xJ));_xH=_xK;continue;}}}else{var _xL=_xI.a,_xM=E(_xH);return (_xM._==0)?new T1(0,I_toInt(I_quot(_xL,I_fromInt(_xM.a)))):new T1(1,I_quot(_xL,_xM.a));}}},_xN=function(_xO,_xP){if(!B(_30(_xP,_uT))){return new F(function(){return _xF(_xO,_xP);});}else{return E(_2V);}},_xQ=function(_xR,_xS){if(!B(_30(_xS,_uT))){var _xT=B(_3k(_xR,_xS));return new T2(0,_xT.a,_xT.b);}else{return E(_2V);}},_xU=function(_xV,_xW){while(1){var _xX=E(_xV);if(!_xX._){var _xY=E(_xX.a);if(_xY==(-2147483648)){_xV=new T1(1,I_fromInt(-2147483648));continue;}else{var _xZ=E(_xW);if(!_xZ._){return new T1(0,_xY%_xZ.a);}else{_xV=new T1(1,I_fromInt(_xY));_xW=_xZ;continue;}}}else{var _y0=_xX.a,_y1=E(_xW);return (_y1._==0)?new T1(1,I_rem(_y0,I_fromInt(_y1.a))):new T1(1,I_rem(_y0,_y1.a));}}},_y2=function(_y3,_y4){if(!B(_30(_y4,_uT))){return new F(function(){return _xU(_y3,_y4);});}else{return E(_2V);}},_y5=function(_y6){return E(_y6);},_y7=function(_y8){return E(_y8);},_y9=function(_ya){var _yb=E(_ya);if(!_yb._){var _yc=E(_yb.a);return (_yc==(-2147483648))?E(_6a):(_yc<0)?new T1(0, -_yc):E(_yb);}else{var _yd=_yb.a;return (I_compareInt(_yd,0)>=0)?E(_yb):new T1(1,I_negate(_yd));}},_ye=new T1(0,0),_yf=new T1(0,-1),_yg=function(_yh){var _yi=E(_yh);if(!_yi._){var _yj=_yi.a;return (_yj>=0)?(E(_yj)==0)?E(_ye):E(_3M):E(_yf);}else{var _yk=I_compareInt(_yi.a,0);return (_yk<=0)?(E(_yk)==0)?E(_ye):E(_yf):E(_3M);}},_yl={_:0,a:_3b,b:_5w,c:_ut,d:_6b,e:_y9,f:_yg,g:_y7},_ym=function(_yn,_yo){var _yp=E(_yn);if(!_yp._){var _yq=_yp.a,_yr=E(_yo);return (_yr._==0)?_yq!=_yr.a:(I_compareInt(_yr.a,_yq)==0)?false:true;}else{var _ys=_yp.a,_yt=E(_yo);return (_yt._==0)?(I_compareInt(_ys,_yt.a)==0)?false:true:(I_compare(_ys,_yt.a)==0)?false:true;}},_yu=new T2(0,_30,_ym),_yv=function(_yw,_yx){return (!B(_5h(_yw,_yx)))?E(_yw):E(_yx);},_yy=function(_yz,_yA){return (!B(_5h(_yz,_yA)))?E(_yA):E(_yz);},_yB={_:0,a:_yu,b:_1N,c:_3N,d:_5h,e:_3E,f:_wA,g:_yv,h:_yy},_yC=function(_yD){return new T2(0,E(_yD),E(_mm));},_yE=new T3(0,_yl,_yB,_yC),_yF={_:0,a:_yE,b:_x5,c:_xN,d:_y2,e:_xe,f:_xC,g:_xQ,h:_xq,i:_y5},_yG=function(_yH){return E(E(_yH).b);},_yI=function(_yJ){return E(E(_yJ).g);},_yK=new T1(0,1),_yL=function(_yM,_yN,_yO){var _yP=B(_yG(_yM)),_yQ=B(_7j(_yP)),_yR=new T(function(){var _yS=new T(function(){var _yT=new T(function(){var _yU=new T(function(){return B(A3(_yI,_yM,_yF,new T(function(){return B(A3(_9a,_yP,_yN,_yO));})));});return B(A2(_7z,_yQ,_yU));}),_yV=new T(function(){return B(A2(_6K,_yQ,new T(function(){return B(A2(_7z,_yQ,_yK));})));});return B(A3(_7l,_yQ,_yV,_yT));});return B(A3(_7l,_yQ,_yS,_yO));});return new F(function(){return A3(_6I,_yQ,_yN,_yR);});},_yW=1.5707963267948966,_yX=function(_yY){return 0.4/Math.cos(B(_yL(_wl,_yY,_yW))-0.7853981633974483);},_yZ=new T(function(){var _z0=B(_p5(_yX,1.2,_qq,_qq,_qq,_qp,_qp,_qp,_qp,_qp,_qp,_qp,_qo));return {_:0,a:E(_z0.a),b:E(_z0.b),c:E(_z0.c),d:E(_z0.d),e:E(_z0.e),f:E(_z0.f),g:E(_z0.g),h:_z0.h,i:_z0.i};}),_z1=0,_z2=function(_z3){return E(_qq);},_z4=1.3,_z5=new T(function(){var _z6=B(_p5(_z2,1.2,_z4,_qp,_qp,_qp,_qp,_qp,_qp,_qp,_qp,_qp,_qo));return {_:0,a:E(_z6.a),b:E(_z6.b),c:E(_z6.c),d:E(_z6.d),e:E(_z6.e),f:E(_z6.f),g:E(_z6.g),h:_z6.h,i:_z6.i};}),_z7=new T(function(){var _z8=B(_p5(_z2,1.2,_qo,_qo,_qp,_qp,_qp,_qp,_qp,_qp,_qp,_qp,_qo));return {_:0,a:E(_z8.a),b:E(_z8.b),c:E(_z8.c),d:E(_z8.d),e:E(_z8.e),f:E(_z8.f),g:E(_z8.g),h:_z8.h,i:_z8.i};}),_z9=new T(function(){var _za=B(_p5(_yX,1.2,_qp,_qo,_qo,_qp,_qp,_qp,_qp,_qp,_qp,_qp,_qo));return {_:0,a:E(_za.a),b:E(_za.b),c:E(_za.c),d:E(_za.d),e:E(_za.e),f:E(_za.f),g:E(_za.g),h:_za.h,i:_za.i};}),_zb=0.5,_zc=new T(function(){var _zd=B(_p5(_z2,1.2,_qp,_qo,_zb,_qp,_qp,_qp,_qp,_qp,_qp,_qp,_qo));return {_:0,a:E(_zd.a),b:E(_zd.b),c:E(_zd.c),d:E(_zd.d),e:E(_zd.e),f:E(_zd.f),g:E(_zd.g),h:_zd.h,i:_zd.i};}),_ze=new T2(1,_zc,_o),_zf=new T2(1,_z9,_ze),_zg=new T2(1,_z7,_zf),_zh=new T2(1,_z5,_zg),_zi=new T2(1,_yZ,_zh),_zj=new T(function(){return B(unCStr("Negative range size"));}),_zk=new T(function(){return B(err(_zj));}),_zl=function(_){var _zm=B(_hh(_zi,0))-1|0,_zn=function(_zo){if(_zo>=0){var _zp=newArr(_zo,_hn),_zq=_zp,_zr=E(_zo);if(!_zr){return new T4(0,E(_z1),E(_zm),0,_zq);}else{var _zs=function(_zt,_zu,_){while(1){var _zv=E(_zt);if(!_zv._){return E(_);}else{var _=_zq[_zu]=_zv.a;if(_zu!=(_zr-1|0)){var _zw=_zu+1|0;_zt=_zv.b;_zu=_zw;continue;}else{return E(_);}}}},_=B((function(_zx,_zy,_zz,_){var _=_zq[_zz]=_zx;if(_zz!=(_zr-1|0)){return new F(function(){return _zs(_zy,_zz+1|0,_);});}else{return E(_);}})(_yZ,_zh,0,_));return new T4(0,E(_z1),E(_zm),_zr,_zq);}}else{return E(_zk);}};if(0>_zm){return new F(function(){return _zn(0);});}else{return new F(function(){return _zn(_zm+1|0);});}},_zA=function(_zB){var _zC=B(A1(_zB,_));return E(_zC);},_zD=new T(function(){return B(_zA(_zl));}),_zE="outline",_zF="polygon",_zG=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_zH=new T(function(){return B(err(_zG));}),_zI=new T(function(){return eval("drawObjects");}),_zJ=new T(function(){return eval("__strict(draw)");}),_zK=function(_zL,_zM){var _zN=jsShowI(_zL);return new F(function(){return _f(fromJSStr(_zN),_zM);});},_zO=function(_zP,_zQ,_zR){if(_zQ>=0){return new F(function(){return _zK(_zQ,_zR);});}else{if(_zP<=6){return new F(function(){return _zK(_zQ,_zR);});}else{return new T2(1,_71,new T(function(){var _zS=jsShowI(_zQ);return B(_f(fromJSStr(_zS),new T2(1,_70,_zR)));}));}}},_zT=new T(function(){return B(unCStr(")"));}),_zU=function(_zV,_zW){var _zX=new T(function(){var _zY=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_zO(0,_zV,_o)),_zT));})));},1);return B(_f(B(_zO(0,_zW,_o)),_zY));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_zX)));});},_zZ=new T2(1,_jE,_o),_A0=function(_A1){return E(_A1);},_A2=function(_A3){return E(_A3);},_A4=function(_A5,_A6){return E(_A6);},_A7=function(_A8,_A9){return E(_A8);},_Aa=function(_Ab){return E(_Ab);},_Ac=new T2(0,_Aa,_A7),_Ad=function(_Ae,_Af){return E(_Ae);},_Ag=new T5(0,_Ac,_A2,_A0,_A4,_Ad),_Ah="flipped2",_Ai="flipped1",_Aj="c1y",_Ak="c1x",_Al="w2z",_Am="w2y",_An="w2x",_Ao="w1z",_Ap="w1y",_Aq="w1x",_Ar="d2z",_As="d2y",_At="d2x",_Au="d1z",_Av="d1y",_Aw="d1x",_Ax="c2y",_Ay="c2x",_Az=function(_AA,_){var _AB=__get(_AA,E(_Aq)),_AC=__get(_AA,E(_Ap)),_AD=__get(_AA,E(_Ao)),_AE=__get(_AA,E(_An)),_AF=__get(_AA,E(_Am)),_AG=__get(_AA,E(_Al)),_AH=__get(_AA,E(_Ak)),_AI=__get(_AA,E(_Aj)),_AJ=__get(_AA,E(_Ay)),_AK=__get(_AA,E(_Ax)),_AL=__get(_AA,E(_Aw)),_AM=__get(_AA,E(_Av)),_AN=__get(_AA,E(_Au)),_AO=__get(_AA,E(_At)),_AP=__get(_AA,E(_As)),_AQ=__get(_AA,E(_Ar)),_AR=__get(_AA,E(_Ai)),_AS=__get(_AA,E(_Ah));return {_:0,a:E(new T3(0,E(_AB),E(_AC),E(_AD))),b:E(new T3(0,E(_AE),E(_AF),E(_AG))),c:E(new T2(0,E(_AH),E(_AI))),d:E(new T2(0,E(_AJ),E(_AK))),e:E(new T3(0,E(_AL),E(_AM),E(_AN))),f:E(new T3(0,E(_AO),E(_AP),E(_AQ))),g:E(_AR),h:E(_AS)};},_AT=function(_AU,_){var _AV=E(_AU);if(!_AV._){return _o;}else{var _AW=B(_Az(E(_AV.a),_)),_AX=B(_AT(_AV.b,_));return new T2(1,_AW,_AX);}},_AY=function(_AZ){var _B0=E(_AZ);return (E(_B0.b)-E(_B0.a)|0)+1|0;},_B1=function(_B2,_B3){var _B4=E(_B2),_B5=E(_B3);return (E(_B4.a)>_B5)?false:_B5<=E(_B4.b);},_B6=function(_B7){return new F(function(){return _zO(0,E(_B7),_o);});},_B8=function(_B9,_Ba,_Bb){return new F(function(){return _zO(E(_B9),E(_Ba),_Bb);});},_Bc=function(_Bd,_Be){return new F(function(){return _zO(0,E(_Bd),_Be);});},_Bf=function(_Bg,_Bh){return new F(function(){return _2B(_Bc,_Bg,_Bh);});},_Bi=new T3(0,_B8,_B6,_Bf),_Bj=0,_Bk=function(_Bl,_Bm,_Bn){return new F(function(){return A1(_Bl,new T2(1,_2y,new T(function(){return B(A1(_Bm,_Bn));})));});},_Bo=new T(function(){return B(unCStr("foldr1"));}),_Bp=new T(function(){return B(_lM(_Bo));}),_Bq=function(_Br,_Bs){var _Bt=E(_Bs);if(!_Bt._){return E(_Bp);}else{var _Bu=_Bt.a,_Bv=E(_Bt.b);if(!_Bv._){return E(_Bu);}else{return new F(function(){return A2(_Br,_Bu,new T(function(){return B(_Bq(_Br,_Bv));}));});}}},_Bw=new T(function(){return B(unCStr(" out of range "));}),_Bx=new T(function(){return B(unCStr("}.index: Index "));}),_By=new T(function(){return B(unCStr("Ix{"));}),_Bz=new T2(1,_70,_o),_BA=new T2(1,_70,_Bz),_BB=0,_BC=function(_BD){return E(E(_BD).a);},_BE=function(_BF,_BG,_BH,_BI,_BJ){var _BK=new T(function(){var _BL=new T(function(){var _BM=new T(function(){var _BN=new T(function(){var _BO=new T(function(){return B(A3(_Bq,_Bk,new T2(1,new T(function(){return B(A3(_BC,_BH,_BB,_BI));}),new T2(1,new T(function(){return B(A3(_BC,_BH,_BB,_BJ));}),_o)),_BA));});return B(_f(_Bw,new T2(1,_71,new T2(1,_71,_BO))));});return B(A(_BC,[_BH,_Bj,_BG,new T2(1,_70,_BN)]));});return B(_f(_Bx,new T2(1,_71,_BM)));},1);return B(_f(_BF,_BL));},1);return new F(function(){return err(B(_f(_By,_BK)));});},_BP=function(_BQ,_BR,_BS,_BT,_BU){return new F(function(){return _BE(_BQ,_BR,_BU,_BS,_BT);});},_BV=function(_BW,_BX,_BY,_BZ){var _C0=E(_BY);return new F(function(){return _BP(_BW,_BX,_C0.a,_C0.b,_BZ);});},_C1=function(_C2,_C3,_C4,_C5){return new F(function(){return _BV(_C5,_C4,_C3,_C2);});},_C6=new T(function(){return B(unCStr("Int"));}),_C7=function(_C8,_C9){return new F(function(){return _C1(_Bi,_C9,_C8,_C6);});},_Ca=function(_Cb,_Cc){var _Cd=E(_Cb),_Ce=E(_Cd.a),_Cf=E(_Cc);if(_Ce>_Cf){return new F(function(){return _C7(_Cf,_Cd);});}else{if(_Cf>E(_Cd.b)){return new F(function(){return _C7(_Cf,_Cd);});}else{return _Cf-_Ce|0;}}},_Cg=function(_Ch){var _Ci=E(_Ch);return new F(function(){return _sa(_Ci.a,_Ci.b);});},_Cj=function(_Ck){var _Cl=E(_Ck),_Cm=E(_Cl.a),_Cn=E(_Cl.b);return (_Cm>_Cn)?E(_Bj):(_Cn-_Cm|0)+1|0;},_Co=function(_Cp,_Cq){return new F(function(){return _tz(_Cq,E(_Cp).a);});},_Cr={_:0,a:_up,b:_Cg,c:_Ca,d:_Co,e:_B1,f:_Cj,g:_AY},_Cs=function(_Ct,_Cu,_){while(1){var _Cv=B((function(_Cw,_Cx,_){var _Cy=E(_Cw);if(!_Cy._){return new T2(0,_jE,_Cx);}else{var _Cz=B(A2(_Cy.a,_Cx,_));_Ct=_Cy.b;_Cu=new T(function(){return E(E(_Cz).b);});return __continue;}})(_Ct,_Cu,_));if(_Cv!=__continue){return _Cv;}}},_CA=function(_CB,_CC){return new T2(1,_CB,_CC);},_CD=function(_CE,_CF){var _CG=E(_CF);return new T2(0,_CG.a,_CG.b);},_CH=function(_CI){return E(E(_CI).f);},_CJ=function(_CK,_CL,_CM){var _CN=E(_CL),_CO=_CN.a,_CP=_CN.b,_CQ=function(_){var _CR=B(A2(_CH,_CK,_CN));if(_CR>=0){var _CS=newArr(_CR,_hn),_CT=_CS,_CU=E(_CR);if(!_CU){return new T(function(){return new T4(0,E(_CO),E(_CP),0,_CT);});}else{var _CV=function(_CW,_CX,_){while(1){var _CY=E(_CW);if(!_CY._){return E(_);}else{var _=_CT[_CX]=_CY.a;if(_CX!=(_CU-1|0)){var _CZ=_CX+1|0;_CW=_CY.b;_CX=_CZ;continue;}else{return E(_);}}}},_=B(_CV(_CM,0,_));return new T(function(){return new T4(0,E(_CO),E(_CP),_CU,_CT);});}}else{return E(_zk);}};return new F(function(){return _zA(_CQ);});},_D0=function(_D1,_D2,_D3,_D4){var _D5=new T(function(){var _D6=E(_D4),_D7=_D6.c-1|0,_D8=new T(function(){return B(A2(_cW,_D2,_o));});if(0<=_D7){var _D9=new T(function(){return B(_96(_D2));}),_Da=function(_Db){var _Dc=new T(function(){var _Dd=new T(function(){return B(A1(_D3,new T(function(){return E(_D6.d[_Db]);})));});return B(A3(_9e,_D9,_CA,_Dd));});return new F(function(){return A3(_9c,_D2,_Dc,new T(function(){if(_Db!=_D7){return B(_Da(_Db+1|0));}else{return E(_D8);}}));});};return B(_Da(0));}else{return E(_D8);}}),_De=new T(function(){return B(_CD(_D1,_D4));});return new F(function(){return A3(_9e,B(_96(_D2)),function(_Df){return new F(function(){return _CJ(_D1,_De,_Df);});},_D5);});},_Dg=function(_Dh,_Di,_Dj,_Dk,_Dl,_Dm,_Dn,_Do,_Dp){var _Dq=B(_7l(_Dh));return new T2(0,new T3(0,E(B(A1(B(A1(_Dq,_Di)),_Dm))),E(B(A1(B(A1(_Dq,_Dj)),_Dn))),E(B(A1(B(A1(_Dq,_Dk)),_Do)))),B(A1(B(A1(_Dq,_Dl)),_Dp)));},_Dr=function(_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA){var _DB=B(_6I(_Ds));return new T2(0,new T3(0,E(B(A1(B(A1(_DB,_Dt)),_Dx))),E(B(A1(B(A1(_DB,_Du)),_Dy))),E(B(A1(B(A1(_DB,_Dv)),_Dz)))),B(A1(B(A1(_DB,_Dw)),_DA)));},_DC=1.0e-2,_DD=function(_DE,_DF,_DG,_DH,_DI,_DJ,_DK,_DL,_DM,_DN,_DO,_DP,_DQ,_DR,_DS,_DT,_DU){var _DV=B(_Dg(_in,_DL,_DM,_DN,_DO,_DC,_DC,_DC,_DC)),_DW=E(_DV.a),_DX=B(_Dr(_in,_DH,_DI,_DJ,_DK,_DW.a,_DW.b,_DW.c,_DV.b)),_DY=E(_DX.a);return new F(function(){return _on(_DE,_DF,_DG,_DY.a,_DY.b,_DY.c,_DX.b,_DL,_DM,_DN,_DO,_DP,_DQ,_DR,_DS,_DT,_DU);});},_DZ=function(_E0){var _E1=E(_E0),_E2=E(_E1.d),_E3=E(_E2.a),_E4=E(_E1.e),_E5=E(_E4.a),_E6=E(_E1.f),_E7=B(_DD(_E1.a,_E1.b,_E1.c,_E3.a,_E3.b,_E3.c,_E2.b,_E5.a,_E5.b,_E5.c,_E4.b,_E6.a,_E6.b,_E6.c,_E1.g,_E1.h,_E1.i));return {_:0,a:E(_E7.a),b:E(_E7.b),c:E(_E7.c),d:E(_E7.d),e:E(_E7.e),f:E(_E7.f),g:E(_E7.g),h:_E7.h,i:_E7.i};},_E8=function(_E9,_Ea,_Eb,_Ec,_Ed,_Ee,_Ef,_Eg,_Eh){var _Ei=B(_7j(B(_7h(_E9))));return new F(function(){return A3(_6I,_Ei,new T(function(){return B(_7n(_E9,_Ea,_Eb,_Ec,_Ee,_Ef,_Eg));}),new T(function(){return B(A3(_7l,_Ei,_Ed,_Eh));}));});},_Ej=new T(function(){return B(unCStr("base"));}),_Ek=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_El=new T(function(){return B(unCStr("IOException"));}),_Em=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Ej,_Ek,_El),_En=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_Em,_o,_o),_Eo=function(_Ep){return E(_En);},_Eq=function(_Er){var _Es=E(_Er);return new F(function(){return _28(B(_26(_Es.a)),_Eo,_Es.b);});},_Et=new T(function(){return B(unCStr(": "));}),_Eu=new T(function(){return B(unCStr(")"));}),_Ev=new T(function(){return B(unCStr(" ("));}),_Ew=new T(function(){return B(unCStr("interrupted"));}),_Ex=new T(function(){return B(unCStr("system error"));}),_Ey=new T(function(){return B(unCStr("unsatisified constraints"));}),_Ez=new T(function(){return B(unCStr("user error"));}),_EA=new T(function(){return B(unCStr("permission denied"));}),_EB=new T(function(){return B(unCStr("illegal operation"));}),_EC=new T(function(){return B(unCStr("end of file"));}),_ED=new T(function(){return B(unCStr("resource exhausted"));}),_EE=new T(function(){return B(unCStr("resource busy"));}),_EF=new T(function(){return B(unCStr("does not exist"));}),_EG=new T(function(){return B(unCStr("already exists"));}),_EH=new T(function(){return B(unCStr("resource vanished"));}),_EI=new T(function(){return B(unCStr("timeout"));}),_EJ=new T(function(){return B(unCStr("unsupported operation"));}),_EK=new T(function(){return B(unCStr("hardware fault"));}),_EL=new T(function(){return B(unCStr("inappropriate type"));}),_EM=new T(function(){return B(unCStr("invalid argument"));}),_EN=new T(function(){return B(unCStr("failed"));}),_EO=new T(function(){return B(unCStr("protocol error"));}),_EP=function(_EQ,_ER){switch(E(_EQ)){case 0:return new F(function(){return _f(_EG,_ER);});break;case 1:return new F(function(){return _f(_EF,_ER);});break;case 2:return new F(function(){return _f(_EE,_ER);});break;case 3:return new F(function(){return _f(_ED,_ER);});break;case 4:return new F(function(){return _f(_EC,_ER);});break;case 5:return new F(function(){return _f(_EB,_ER);});break;case 6:return new F(function(){return _f(_EA,_ER);});break;case 7:return new F(function(){return _f(_Ez,_ER);});break;case 8:return new F(function(){return _f(_Ey,_ER);});break;case 9:return new F(function(){return _f(_Ex,_ER);});break;case 10:return new F(function(){return _f(_EO,_ER);});break;case 11:return new F(function(){return _f(_EN,_ER);});break;case 12:return new F(function(){return _f(_EM,_ER);});break;case 13:return new F(function(){return _f(_EL,_ER);});break;case 14:return new F(function(){return _f(_EK,_ER);});break;case 15:return new F(function(){return _f(_EJ,_ER);});break;case 16:return new F(function(){return _f(_EI,_ER);});break;case 17:return new F(function(){return _f(_EH,_ER);});break;default:return new F(function(){return _f(_Ew,_ER);});}},_ES=new T(function(){return B(unCStr("}"));}),_ET=new T(function(){return B(unCStr("{handle: "));}),_EU=function(_EV,_EW,_EX,_EY,_EZ,_F0){var _F1=new T(function(){var _F2=new T(function(){var _F3=new T(function(){var _F4=E(_EY);if(!_F4._){return E(_F0);}else{var _F5=new T(function(){return B(_f(_F4,new T(function(){return B(_f(_Eu,_F0));},1)));},1);return B(_f(_Ev,_F5));}},1);return B(_EP(_EW,_F3));}),_F6=E(_EX);if(!_F6._){return E(_F2);}else{return B(_f(_F6,new T(function(){return B(_f(_Et,_F2));},1)));}}),_F7=E(_EZ);if(!_F7._){var _F8=E(_EV);if(!_F8._){return E(_F1);}else{var _F9=E(_F8.a);if(!_F9._){var _Fa=new T(function(){var _Fb=new T(function(){return B(_f(_ES,new T(function(){return B(_f(_Et,_F1));},1)));},1);return B(_f(_F9.a,_Fb));},1);return new F(function(){return _f(_ET,_Fa);});}else{var _Fc=new T(function(){var _Fd=new T(function(){return B(_f(_ES,new T(function(){return B(_f(_Et,_F1));},1)));},1);return B(_f(_F9.a,_Fd));},1);return new F(function(){return _f(_ET,_Fc);});}}}else{return new F(function(){return _f(_F7.a,new T(function(){return B(_f(_Et,_F1));},1));});}},_Fe=function(_Ff){var _Fg=E(_Ff);return new F(function(){return _EU(_Fg.a,_Fg.b,_Fg.c,_Fg.d,_Fg.f,_o);});},_Fh=function(_Fi,_Fj,_Fk){var _Fl=E(_Fj);return new F(function(){return _EU(_Fl.a,_Fl.b,_Fl.c,_Fl.d,_Fl.f,_Fk);});},_Fm=function(_Fn,_Fo){var _Fp=E(_Fn);return new F(function(){return _EU(_Fp.a,_Fp.b,_Fp.c,_Fp.d,_Fp.f,_Fo);});},_Fq=function(_Fr,_Fs){return new F(function(){return _2B(_Fm,_Fr,_Fs);});},_Ft=new T3(0,_Fh,_Fe,_Fq),_Fu=new T(function(){return new T5(0,_Eo,_Ft,_Fv,_Eq,_Fe);}),_Fv=function(_Fw){return new T2(0,_Fu,_Fw);},_Fx=__Z,_Fy=7,_Fz=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:85:3-9"));}),_FA=new T6(0,_Fx,_Fy,_o,_Fz,_Fx,_Fx),_FB=new T(function(){return B(_Fv(_FA));}),_FC=function(_){return new F(function(){return die(_FB);});},_FD=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:84:3-9"));}),_FE=new T6(0,_Fx,_Fy,_o,_FD,_Fx,_Fx),_FF=new T(function(){return B(_Fv(_FE));}),_FG=function(_){return new F(function(){return die(_FF);});},_FH=function(_FI,_){return new T2(0,_o,_FI);},_FJ=1,_FK=new T(function(){return B(unCStr(")"));}),_FL=function(_FM,_FN){var _FO=new T(function(){var _FP=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_zO(0,_FM,_o)),_FK));})));},1);return B(_f(B(_zO(0,_FN,_o)),_FP));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_FO)));});},_FQ=function(_FR,_FS){var _FT=new T(function(){var _FU=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_f(B(_zO(0,_FS,_o)),_FK));})));},1);return B(_f(B(_zO(0,_FR,_o)),_FU));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_FT)));});},_FV=0.6,_FW=function(_FX){var _FY=E(_FX);if(!_FY._){return E(_FH);}else{var _FZ=new T(function(){return B(_FW(_FY.b));}),_G0=function(_G1){var _G2=E(_G1);if(!_G2._){return E(_FZ);}else{var _G3=_G2.a,_G4=new T(function(){return B(_G0(_G2.b));}),_G5=new T(function(){return 0.1*E(E(_G3).e)/1.0e-2;}),_G6=new T(function(){var _G7=E(_G3);if(_G7.a!=_G7.b){return E(_FJ);}else{return E(_FV);}}),_G8=function(_G9,_){var _Ga=E(_G9),_Gb=_Ga.c,_Gc=_Ga.d,_Gd=E(_Ga.a),_Ge=E(_Ga.b),_Gf=E(_G3),_Gg=_Gf.a,_Gh=_Gf.b,_Gi=E(_Gf.c),_Gj=_Gi.b,_Gk=E(_Gi.a),_Gl=_Gk.a,_Gm=_Gk.b,_Gn=_Gk.c,_Go=E(_Gf.d),_Gp=_Go.b,_Gq=E(_Go.a),_Gr=_Gq.a,_Gs=_Gq.b,_Gt=_Gq.c;if(_Gd>_Gg){return new F(function(){return _FG(_);});}else{if(_Gg>_Ge){return new F(function(){return _FG(_);});}else{if(_Gd>_Gh){return new F(function(){return _FC(_);});}else{if(_Gh>_Ge){return new F(function(){return _FC(_);});}else{var _Gu=_Gg-_Gd|0;if(0>_Gu){return new F(function(){return _FL(_Gb,_Gu);});}else{if(_Gu>=_Gb){return new F(function(){return _FL(_Gb,_Gu);});}else{var _Gv=E(_Gc[_Gu]),_Gw=E(_Gv.c),_Gx=_Gw.b,_Gy=E(_Gw.a),_Gz=_Gy.a,_GA=_Gy.b,_GB=_Gy.c,_GC=E(_Gv.e),_GD=E(_GC.a),_GE=B(_Dg(_in,_Gl,_Gm,_Gn,_Gj,_Gz,_GA,_GB,_Gx)),_GF=E(_GE.a),_GG=B(_Dg(_in,_GF.a,_GF.b,_GF.c,_GE.b,_Gl,_Gm,_Gn,_Gj)),_GH=E(_GG.a),_GI=_Gh-_Gd|0;if(0>_GI){return new F(function(){return _FQ(_GI,_Gb);});}else{if(_GI>=_Gb){return new F(function(){return _FQ(_GI,_Gb);});}else{var _GJ=E(_Gc[_GI]),_GK=E(_GJ.c),_GL=_GK.b,_GM=E(_GK.a),_GN=_GM.a,_GO=_GM.b,_GP=_GM.c,_GQ=E(_GJ.e),_GR=E(_GQ.a),_GS=B(_Dg(_in,_Gr,_Gs,_Gt,_Gp,_GN,_GO,_GP,_GL)),_GT=E(_GS.a),_GU=B(_Dg(_in,_GT.a,_GT.b,_GT.c,_GS.b,_Gr,_Gs,_Gt,_Gp)),_GV=E(_GU.a),_GW=E(_GH.a)+E(_GH.b)+E(_GH.c)+E(_GG.b)+E(_GV.a)+E(_GV.b)+E(_GV.c)+E(_GU.b);if(!_GW){var _GX=B(A2(_G4,_Ga,_));return new T2(0,new T2(1,_jE,new T(function(){return E(E(_GX).a);})),new T(function(){return E(E(_GX).b);}));}else{var _GY=new T(function(){return  -((B(_E8(_iT,_GD.a,_GD.b,_GD.c,_GC.b,_Gl,_Gm,_Gn,_Gj))-B(_E8(_iT,_GR.a,_GR.b,_GR.c,_GQ.b,_Gr,_Gs,_Gt,_Gp))-E(_G5))/_GW);}),_GZ=function(_H0,_H1,_H2,_H3,_){var _H4=new T(function(){var _H5=function(_H6,_H7,_H8,_H9,_Ha){if(_H6>_Gh){return E(_Ha);}else{if(_Gh>_H7){return E(_Ha);}else{var _Hb=function(_){var _Hc=newArr(_H8,_hn),_Hd=_Hc,_He=function(_Hf,_){while(1){if(_Hf!=_H8){var _=_Hd[_Hf]=_H9[_Hf],_Hg=_Hf+1|0;_Hf=_Hg;continue;}else{return E(_);}}},_=B(_He(0,_)),_Hh=_Gh-_H6|0;if(0>_Hh){return new F(function(){return _FQ(_Hh,_H8);});}else{if(_Hh>=_H8){return new F(function(){return _FQ(_Hh,_H8);});}else{var _=_Hd[_Hh]=new T(function(){var _Hi=E(_H9[_Hh]),_Hj=E(_Hi.e),_Hk=E(_Hj.a),_Hl=B(_Dg(_in,_GN,_GO,_GP,_GL,_Gr,_Gs,_Gt,_Gp)),_Hm=E(_Hl.a),_Hn=E(_GY)*E(_G6),_Ho=B(_Dg(_in,_Hm.a,_Hm.b,_Hm.c,_Hl.b,_Hn,_Hn,_Hn,_Hn)),_Hp=E(_Ho.a),_Hq=B(_Dr(_in,_Hk.a,_Hk.b,_Hk.c,_Hj.b, -E(_Hp.a), -E(_Hp.b), -E(_Hp.c), -E(_Ho.b)));return {_:0,a:E(_Hi.a),b:E(_Hi.b),c:E(_Hi.c),d:E(_Hi.d),e:E(new T2(0,E(_Hq.a),E(_Hq.b))),f:E(_Hi.f),g:E(_Hi.g),h:_Hi.h,i:_Hi.i};});return new T4(0,E(_H6),E(_H7),_H8,_Hd);}}};return new F(function(){return _zA(_Hb);});}}};if(_H0>_Gg){return B(_H5(_H0,_H1,_H2,_H3,new T4(0,E(_H0),E(_H1),_H2,_H3)));}else{if(_Gg>_H1){return B(_H5(_H0,_H1,_H2,_H3,new T4(0,E(_H0),E(_H1),_H2,_H3)));}else{var _Hr=function(_){var _Hs=newArr(_H2,_hn),_Ht=_Hs,_Hu=function(_Hv,_){while(1){if(_Hv!=_H2){var _=_Ht[_Hv]=_H3[_Hv],_Hw=_Hv+1|0;_Hv=_Hw;continue;}else{return E(_);}}},_=B(_Hu(0,_)),_Hx=_Gg-_H0|0;if(0>_Hx){return new F(function(){return _FL(_H2,_Hx);});}else{if(_Hx>=_H2){return new F(function(){return _FL(_H2,_Hx);});}else{var _=_Ht[_Hx]=new T(function(){var _Hy=E(_H3[_Hx]),_Hz=E(_Hy.e),_HA=E(_Hz.a),_HB=B(_Dg(_in,_Gz,_GA,_GB,_Gx,_Gl,_Gm,_Gn,_Gj)),_HC=E(_HB.a),_HD=E(_GY)*E(_G6),_HE=B(_Dg(_in,_HC.a,_HC.b,_HC.c,_HB.b,_HD,_HD,_HD,_HD)),_HF=E(_HE.a),_HG=B(_Dr(_in,_HA.a,_HA.b,_HA.c,_Hz.b,_HF.a,_HF.b,_HF.c,_HE.b));return {_:0,a:E(_Hy.a),b:E(_Hy.b),c:E(_Hy.c),d:E(_Hy.d),e:E(new T2(0,E(_HG.a),E(_HG.b))),f:E(_Hy.f),g:E(_Hy.g),h:_Hy.h,i:_Hy.i};});return new T4(0,E(_H0),E(_H1),_H2,_Ht);}}},_HH=B(_zA(_Hr));return B(_H5(E(_HH.a),E(_HH.b),_HH.c,_HH.d,_HH));}}});return new T2(0,_jE,_H4);};if(!E(_Gf.f)){var _HI=B(_GZ(_Gd,_Ge,_Gb,_Gc,_)),_HJ=B(A2(_G4,new T(function(){return E(E(_HI).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_HI).a);}),new T(function(){return E(E(_HJ).a);})),new T(function(){return E(E(_HJ).b);}));}else{if(E(_GY)<0){var _HK=B(A2(_G4,_Ga,_));return new T2(0,new T2(1,_jE,new T(function(){return E(E(_HK).a);})),new T(function(){return E(E(_HK).b);}));}else{var _HL=B(_GZ(_Gd,_Ge,_Gb,_Gc,_)),_HM=B(A2(_G4,new T(function(){return E(E(_HL).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_HL).a);}),new T(function(){return E(E(_HM).a);})),new T(function(){return E(E(_HM).b);}));}}}}}}}}}}}};return E(_G8);}};return new F(function(){return _G0(_FY.a);});}},_HN=function(_,_HO){var _HP=new T(function(){return B(_FW(E(_HO).a));}),_HQ=function(_HR){var _HS=E(_HR);return (_HS==1)?E(new T2(1,_HP,_o)):new T2(1,_HP,new T(function(){return B(_HQ(_HS-1|0));}));},_HT=B(_Cs(B(_HQ(5)),new T(function(){return E(E(_HO).b);}),_)),_HU=new T(function(){return B(_D0(_Cr,_Ag,_DZ,new T(function(){return E(E(_HT).b);})));});return new T2(0,_jE,_HU);},_HV=function(_HW,_HX,_HY,_HZ,_I0){var _I1=B(_7j(B(_7h(_HW))));return new F(function(){return A3(_6I,_I1,new T(function(){return B(A3(_7l,_I1,_HX,_HZ));}),new T(function(){return B(A3(_7l,_I1,_HY,_I0));}));});},_I2=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:55:7-13"));}),_I3=new T6(0,_Fx,_Fy,_o,_I2,_Fx,_Fx),_I4=new T(function(){return B(_Fv(_I3));}),_I5=function(_){return new F(function(){return die(_I4);});},_I6=false,_I7=true,_I8=function(_I9){var _Ia=E(_I9),_Ib=E(_Ia.b),_Ic=E(_Ia.e),_Id=E(_Ic.a),_Ie=E(_Ia.g),_If=B(_l5(_iT,_Ib.a,_Ib.b,_Ib.c,_Ie.a,_Ie.b,_Ie.c));return {_:0,a:E(_Ia.a),b:E(_Ib),c:E(_Ia.c),d:E(_Ia.d),e:E(new T2(0,E(new T3(0,E(_Id.a)+E(_If.a)*1.0e-2,E(_Id.b)+E(_If.b)*1.0e-2,E(_Id.c)+E(_If.c)*1.0e-2)),E(_Ic.b))),f:E(_Ia.f),g:E(_Ie),h:_Ia.h,i:_Ia.i};},_Ig=new T(function(){return eval("collide");}),_Ih=function(_Ii){var _Ij=E(_Ii);if(!_Ij._){return __Z;}else{return new F(function(){return _f(_Ij.a,new T(function(){return B(_Ih(_Ij.b));},1));});}},_Ik=0,_Il=new T3(0,E(_Ik),E(_Ik),E(_Ik)),_Im=new T2(0,E(_Il),E(_Ik)),_In=new T2(0,_iT,_js),_Io=new T(function(){return B(_gT(_In));}),_Ip=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:54:7-13"));}),_Iq=new T6(0,_Fx,_Fy,_o,_Ip,_Fx,_Fx),_Ir=new T(function(){return B(_Fv(_Iq));}),_Is=function(_It,_){var _Iu=B(_D0(_Cr,_Ag,_I8,_It)),_Iv=E(_Iu.a),_Iw=E(_Iu.b);if(_Iv<=_Iw){var _Ix=function(_Iy,_Iz,_){if(_Iy<=_Iw){var _IA=E(_Iz),_IB=function(_IC,_ID,_IE,_IF,_IG,_){if(_ID>_Iy){return new F(function(){return die(_Ir);});}else{if(_Iy>_IE){return new F(function(){return die(_Ir);});}else{if(_ID>_IC){return new F(function(){return _I5(_);});}else{if(_IC>_IE){return new F(function(){return _I5(_);});}else{var _IH=_Iy-_ID|0;if(0>_IH){return new F(function(){return _FQ(_IH,_IF);});}else{if(_IH>=_IF){return new F(function(){return _FQ(_IH,_IF);});}else{var _II=E(_IG[_IH]),_IJ=_IC-_ID|0;if(0>_IJ){return new F(function(){return _FQ(_IJ,_IF);});}else{if(_IJ>=_IF){return new F(function(){return _FQ(_IJ,_IF);});}else{var _IK=E(_IG[_IJ]),_IL=__app2(E(_Ig),B(_jF(new T2(1,new T2(0,_zF,_II.h),new T2(1,new T2(0,_zE,_II.i),_o)))),B(_jF(new T2(1,new T2(0,_zF,_IK.h),new T2(1,new T2(0,_zE,_IK.i),_o))))),_IM=__arr2lst(0,_IL),_IN=B(_AT(_IM,_));if(_IC!=_Iw){var _IO=B(_IB(_IC+1|0,_ID,_IE,_IF,_IG,_)),_IP=new T(function(){var _IQ=new T(function(){return _Iy!=_IC;}),_IR=function(_IS){var _IT=E(_IS);if(!_IT._){return __Z;}else{var _IU=_IT.b,_IV=E(_IT.a),_IW=E(_IV.b),_IX=E(_IV.a),_IY=E(_IV.c),_IZ=_IY.a,_J0=_IY.b,_J1=E(_IV.e),_J2=E(_IV.d),_J3=_J2.a,_J4=_J2.b,_J5=E(_IV.f),_J6=new T(function(){var _J7=B(_ki(_iT,_J5.a,_J5.b,_J5.c)),_J8=Math.sqrt(B(_HV(_iT,_J3,_J4,_J3,_J4)));return new T3(0,_J8*E(_J7.a),_J8*E(_J7.b),_J8*E(_J7.c));}),_J9=new T(function(){var _Ja=B(_ki(_iT,_J1.a,_J1.b,_J1.c)),_Jb=Math.sqrt(B(_HV(_iT,_IZ,_J0,_IZ,_J0)));return new T3(0,_Jb*E(_Ja.a),_Jb*E(_Ja.b),_Jb*E(_Ja.c));}),_Jc=new T(function(){var _Jd=B(A1(_Io,_IW)),_Je=B(_ki(_iT,_Jd.a,_Jd.b,_Jd.c));return new T3(0,E(_Je.a),E(_Je.b),E(_Je.c));}),_Jf=new T(function(){var _Jg=B(A1(_Io,_IX)),_Jh=B(_ki(_iT,_Jg.a,_Jg.b,_Jg.c));return new T3(0,E(_Jh.a),E(_Jh.b),E(_Jh.c));}),_Ji=E(_IW.a)+ -E(_IX.a),_Jj=E(_IW.b)+ -E(_IX.b),_Jk=E(_IW.c)+ -E(_IX.c),_Jl=new T(function(){return Math.sqrt(B(_7n(_iT,_Ji,_Jj,_Jk,_Ji,_Jj,_Jk)));}),_Jm=new T(function(){var _Jn=1/E(_Jl);return new T3(0,_Ji*_Jn,_Jj*_Jn,_Jk*_Jn);}),_Jo=new T(function(){if(!E(_IV.g)){return E(_Jm);}else{var _Jp=E(_Jm);return new T3(0,-1*E(_Jp.a),-1*E(_Jp.b),-1*E(_Jp.c));}}),_Jq=new T(function(){if(!E(_IV.h)){return E(_Jm);}else{var _Jr=E(_Jm);return new T3(0,-1*E(_Jr.a),-1*E(_Jr.b),-1*E(_Jr.c));}});return (!E(_IQ))?new T2(1,new T(function(){var _Js=E(_Jo),_Jt=E(_Js.b),_Ju=E(_Js.c),_Jv=E(_Js.a),_Jw=E(_Jf),_Jx=E(_Jw.c),_Jy=E(_Jw.b),_Jz=E(_Jw.a),_JA=E(_J9),_JB=E(_JA.c),_JC=E(_JA.b),_JD=E(_JA.a),_JE=_Jt*_Jx-_Jy*_Ju,_JF=_Ju*_Jz-_Jx*_Jv,_JG=_Jv*_Jy-_Jz*_Jt,_JH=B(_7n(_iT,_JF*_JB-_JC*_JG,_JG*_JD-_JB*_JE,_JE*_JC-_JD*_JF,_Jz,_Jy,_Jx));return new T6(0,_Iy,_IC,E(new T2(0,E(new T3(0,E(_JE),E(_JF),E(_JG))),E(_JH))),E(_Im),_Jl,_I6);}),new T2(1,new T(function(){var _JI=E(_Jq),_JJ=E(_JI.b),_JK=E(_JI.c),_JL=E(_JI.a),_JM=E(_Jc),_JN=E(_JM.c),_JO=E(_JM.b),_JP=E(_JM.a),_JQ=E(_J6),_JR=E(_JQ.c),_JS=E(_JQ.b),_JT=E(_JQ.a),_JU=_JJ*_JN-_JO*_JK,_JV=_JK*_JP-_JN*_JL,_JW=_JL*_JO-_JP*_JJ,_JX=B(_7n(_iT,_JV*_JR-_JS*_JW,_JW*_JT-_JR*_JU,_JU*_JS-_JT*_JV,_JP,_JO,_JN));return new T6(0,_Iy,_IC,E(_Im),E(new T2(0,E(new T3(0,E(_JU),E(_JV),E(_JW))),E(_JX))),_Jl,_I6);}),new T(function(){return B(_IR(_IU));}))):new T2(1,new T(function(){var _JY=E(_Jo),_JZ=E(_JY.b),_K0=E(_JY.c),_K1=E(_JY.a),_K2=E(_Jf),_K3=_K2.a,_K4=_K2.b,_K5=_K2.c,_K6=B(_l5(_iT,_K1,_JZ,_K0,_K3,_K4,_K5)),_K7=E(_J9),_K8=E(_K7.c),_K9=E(_K7.b),_Ka=E(_K7.a),_Kb=B(_7n(_iT,_JZ*_K8-_K9*_K0,_K0*_Ka-_K8*_K1,_K1*_K9-_Ka*_JZ,_K3,_K4,_K5)),_Kc=E(_Jq),_Kd=E(_Kc.b),_Ke=E(_Kc.c),_Kf=E(_Kc.a),_Kg=E(_Jc),_Kh=_Kg.a,_Ki=_Kg.b,_Kj=_Kg.c,_Kk=B(_l5(_iT,_Kf,_Kd,_Ke,_Kh,_Ki,_Kj)),_Kl=E(_J6),_Km=E(_Kl.c),_Kn=E(_Kl.b),_Ko=E(_Kl.a),_Kp=B(_7n(_iT,_Kd*_Km-_Kn*_Ke,_Ke*_Ko-_Km*_Kf,_Kf*_Kn-_Ko*_Kd,_Kh,_Ki,_Kj));return new T6(0,_Iy,_IC,E(new T2(0,E(new T3(0,E(_K6.a),E(_K6.b),E(_K6.c))),E(_Kb))),E(new T2(0,E(new T3(0,E(_Kk.a),E(_Kk.b),E(_Kk.c))),E(_Kp))),_Jl,_I7);}),new T(function(){return B(_IR(_IU));}));}};return B(_IR(_IN));});return new T2(0,new T2(1,_IP,new T(function(){return E(E(_IO).a);})),new T(function(){return E(E(_IO).b);}));}else{var _Kq=new T(function(){var _Kr=new T(function(){return _Iy!=_IC;}),_Ks=function(_Kt){var _Ku=E(_Kt);if(!_Ku._){return __Z;}else{var _Kv=_Ku.b,_Kw=E(_Ku.a),_Kx=E(_Kw.b),_Ky=E(_Kw.a),_Kz=E(_Kw.c),_KA=_Kz.a,_KB=_Kz.b,_KC=E(_Kw.e),_KD=E(_Kw.d),_KE=_KD.a,_KF=_KD.b,_KG=E(_Kw.f),_KH=new T(function(){var _KI=B(_ki(_iT,_KG.a,_KG.b,_KG.c)),_KJ=Math.sqrt(B(_HV(_iT,_KE,_KF,_KE,_KF)));return new T3(0,_KJ*E(_KI.a),_KJ*E(_KI.b),_KJ*E(_KI.c));}),_KK=new T(function(){var _KL=B(_ki(_iT,_KC.a,_KC.b,_KC.c)),_KM=Math.sqrt(B(_HV(_iT,_KA,_KB,_KA,_KB)));return new T3(0,_KM*E(_KL.a),_KM*E(_KL.b),_KM*E(_KL.c));}),_KN=new T(function(){var _KO=B(A1(_Io,_Kx)),_KP=B(_ki(_iT,_KO.a,_KO.b,_KO.c));return new T3(0,E(_KP.a),E(_KP.b),E(_KP.c));}),_KQ=new T(function(){var _KR=B(A1(_Io,_Ky)),_KS=B(_ki(_iT,_KR.a,_KR.b,_KR.c));return new T3(0,E(_KS.a),E(_KS.b),E(_KS.c));}),_KT=E(_Kx.a)+ -E(_Ky.a),_KU=E(_Kx.b)+ -E(_Ky.b),_KV=E(_Kx.c)+ -E(_Ky.c),_KW=new T(function(){return Math.sqrt(B(_7n(_iT,_KT,_KU,_KV,_KT,_KU,_KV)));}),_KX=new T(function(){var _KY=1/E(_KW);return new T3(0,_KT*_KY,_KU*_KY,_KV*_KY);}),_KZ=new T(function(){if(!E(_Kw.g)){return E(_KX);}else{var _L0=E(_KX);return new T3(0,-1*E(_L0.a),-1*E(_L0.b),-1*E(_L0.c));}}),_L1=new T(function(){if(!E(_Kw.h)){return E(_KX);}else{var _L2=E(_KX);return new T3(0,-1*E(_L2.a),-1*E(_L2.b),-1*E(_L2.c));}});return (!E(_Kr))?new T2(1,new T(function(){var _L3=E(_KZ),_L4=E(_L3.b),_L5=E(_L3.c),_L6=E(_L3.a),_L7=E(_KQ),_L8=E(_L7.c),_L9=E(_L7.b),_La=E(_L7.a),_Lb=E(_KK),_Lc=E(_Lb.c),_Ld=E(_Lb.b),_Le=E(_Lb.a),_Lf=_L4*_L8-_L9*_L5,_Lg=_L5*_La-_L8*_L6,_Lh=_L6*_L9-_La*_L4,_Li=B(_7n(_iT,_Lg*_Lc-_Ld*_Lh,_Lh*_Le-_Lc*_Lf,_Lf*_Ld-_Le*_Lg,_La,_L9,_L8));return new T6(0,_Iy,_IC,E(new T2(0,E(new T3(0,E(_Lf),E(_Lg),E(_Lh))),E(_Li))),E(_Im),_KW,_I6);}),new T2(1,new T(function(){var _Lj=E(_L1),_Lk=E(_Lj.b),_Ll=E(_Lj.c),_Lm=E(_Lj.a),_Ln=E(_KN),_Lo=E(_Ln.c),_Lp=E(_Ln.b),_Lq=E(_Ln.a),_Lr=E(_KH),_Ls=E(_Lr.c),_Lt=E(_Lr.b),_Lu=E(_Lr.a),_Lv=_Lk*_Lo-_Lp*_Ll,_Lw=_Ll*_Lq-_Lo*_Lm,_Lx=_Lm*_Lp-_Lq*_Lk,_Ly=B(_7n(_iT,_Lw*_Ls-_Lt*_Lx,_Lx*_Lu-_Ls*_Lv,_Lv*_Lt-_Lu*_Lw,_Lq,_Lp,_Lo));return new T6(0,_Iy,_IC,E(_Im),E(new T2(0,E(new T3(0,E(_Lv),E(_Lw),E(_Lx))),E(_Ly))),_KW,_I6);}),new T(function(){return B(_Ks(_Kv));}))):new T2(1,new T(function(){var _Lz=E(_KZ),_LA=E(_Lz.b),_LB=E(_Lz.c),_LC=E(_Lz.a),_LD=E(_KQ),_LE=_LD.a,_LF=_LD.b,_LG=_LD.c,_LH=B(_l5(_iT,_LC,_LA,_LB,_LE,_LF,_LG)),_LI=E(_KK),_LJ=E(_LI.c),_LK=E(_LI.b),_LL=E(_LI.a),_LM=B(_7n(_iT,_LA*_LJ-_LK*_LB,_LB*_LL-_LJ*_LC,_LC*_LK-_LL*_LA,_LE,_LF,_LG)),_LN=E(_L1),_LO=E(_LN.b),_LP=E(_LN.c),_LQ=E(_LN.a),_LR=E(_KN),_LS=_LR.a,_LT=_LR.b,_LU=_LR.c,_LV=B(_l5(_iT,_LQ,_LO,_LP,_LS,_LT,_LU)),_LW=E(_KH),_LX=E(_LW.c),_LY=E(_LW.b),_LZ=E(_LW.a),_M0=B(_7n(_iT,_LO*_LX-_LY*_LP,_LP*_LZ-_LX*_LQ,_LQ*_LY-_LZ*_LO,_LS,_LT,_LU));return new T6(0,_Iy,_IC,E(new T2(0,E(new T3(0,E(_LH.a),E(_LH.b),E(_LH.c))),E(_LM))),E(new T2(0,E(new T3(0,E(_LV.a),E(_LV.b),E(_LV.c))),E(_M0))),_KW,_I7);}),new T(function(){return B(_Ks(_Kv));}));}};return B(_Ks(_IN));});return new T2(0,new T2(1,_Kq,_o),new T4(0,E(_ID),E(_IE),_IF,_IG));}}}}}}}}}},_M1=B(_IB(_Iy,E(_IA.a),E(_IA.b),_IA.c,_IA.d,_));if(_Iy!=_Iw){var _M2=B(_Ix(_Iy+1|0,new T(function(){return E(E(_M1).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Ih(E(_M1).a));}),new T(function(){return E(E(_M2).a);})),new T(function(){return E(E(_M2).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Ih(E(_M1).a));}),_o),new T(function(){return E(E(_M1).b);}));}}else{if(_Iy!=_Iw){var _M3=B(_Ix(_Iy+1|0,_Iz,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_M3).a);})),new T(function(){return E(E(_M3).b);}));}else{return new T2(0,new T2(1,_o,_o),_Iz);}}},_M4=function(_M5,_M6,_M7,_M8,_M9,_){if(_M5<=_Iw){var _Ma=function(_Mb,_Mc,_Md,_Me,_Mf,_){if(_Mc>_M5){return new F(function(){return die(_Ir);});}else{if(_M5>_Md){return new F(function(){return die(_Ir);});}else{if(_Mc>_Mb){return new F(function(){return _I5(_);});}else{if(_Mb>_Md){return new F(function(){return _I5(_);});}else{var _Mg=_M5-_Mc|0;if(0>_Mg){return new F(function(){return _FQ(_Mg,_Me);});}else{if(_Mg>=_Me){return new F(function(){return _FQ(_Mg,_Me);});}else{var _Mh=E(_Mf[_Mg]),_Mi=_Mb-_Mc|0;if(0>_Mi){return new F(function(){return _FQ(_Mi,_Me);});}else{if(_Mi>=_Me){return new F(function(){return _FQ(_Mi,_Me);});}else{var _Mj=E(_Mf[_Mi]),_Mk=__app2(E(_Ig),B(_jF(new T2(1,new T2(0,_zF,_Mh.h),new T2(1,new T2(0,_zE,_Mh.i),_o)))),B(_jF(new T2(1,new T2(0,_zF,_Mj.h),new T2(1,new T2(0,_zE,_Mj.i),_o))))),_Ml=__arr2lst(0,_Mk),_Mm=B(_AT(_Ml,_));if(_Mb!=_Iw){var _Mn=B(_Ma(_Mb+1|0,_Mc,_Md,_Me,_Mf,_)),_Mo=new T(function(){var _Mp=new T(function(){return _M5!=_Mb;}),_Mq=function(_Mr){var _Ms=E(_Mr);if(!_Ms._){return __Z;}else{var _Mt=_Ms.b,_Mu=E(_Ms.a),_Mv=E(_Mu.b),_Mw=E(_Mu.a),_Mx=E(_Mu.c),_My=_Mx.a,_Mz=_Mx.b,_MA=E(_Mu.e),_MB=E(_Mu.d),_MC=_MB.a,_MD=_MB.b,_ME=E(_Mu.f),_MF=new T(function(){var _MG=B(_ki(_iT,_ME.a,_ME.b,_ME.c)),_MH=Math.sqrt(B(_HV(_iT,_MC,_MD,_MC,_MD)));return new T3(0,_MH*E(_MG.a),_MH*E(_MG.b),_MH*E(_MG.c));}),_MI=new T(function(){var _MJ=B(_ki(_iT,_MA.a,_MA.b,_MA.c)),_MK=Math.sqrt(B(_HV(_iT,_My,_Mz,_My,_Mz)));return new T3(0,_MK*E(_MJ.a),_MK*E(_MJ.b),_MK*E(_MJ.c));}),_ML=new T(function(){var _MM=B(A1(_Io,_Mv)),_MN=B(_ki(_iT,_MM.a,_MM.b,_MM.c));return new T3(0,E(_MN.a),E(_MN.b),E(_MN.c));}),_MO=new T(function(){var _MP=B(A1(_Io,_Mw)),_MQ=B(_ki(_iT,_MP.a,_MP.b,_MP.c));return new T3(0,E(_MQ.a),E(_MQ.b),E(_MQ.c));}),_MR=E(_Mv.a)+ -E(_Mw.a),_MS=E(_Mv.b)+ -E(_Mw.b),_MT=E(_Mv.c)+ -E(_Mw.c),_MU=new T(function(){return Math.sqrt(B(_7n(_iT,_MR,_MS,_MT,_MR,_MS,_MT)));}),_MV=new T(function(){var _MW=1/E(_MU);return new T3(0,_MR*_MW,_MS*_MW,_MT*_MW);}),_MX=new T(function(){if(!E(_Mu.g)){return E(_MV);}else{var _MY=E(_MV);return new T3(0,-1*E(_MY.a),-1*E(_MY.b),-1*E(_MY.c));}}),_MZ=new T(function(){if(!E(_Mu.h)){return E(_MV);}else{var _N0=E(_MV);return new T3(0,-1*E(_N0.a),-1*E(_N0.b),-1*E(_N0.c));}});return (!E(_Mp))?new T2(1,new T(function(){var _N1=E(_MX),_N2=E(_N1.b),_N3=E(_N1.c),_N4=E(_N1.a),_N5=E(_MO),_N6=E(_N5.c),_N7=E(_N5.b),_N8=E(_N5.a),_N9=E(_MI),_Na=E(_N9.c),_Nb=E(_N9.b),_Nc=E(_N9.a),_Nd=_N2*_N6-_N7*_N3,_Ne=_N3*_N8-_N6*_N4,_Nf=_N4*_N7-_N8*_N2,_Ng=B(_7n(_iT,_Ne*_Na-_Nb*_Nf,_Nf*_Nc-_Na*_Nd,_Nd*_Nb-_Nc*_Ne,_N8,_N7,_N6));return new T6(0,_M5,_Mb,E(new T2(0,E(new T3(0,E(_Nd),E(_Ne),E(_Nf))),E(_Ng))),E(_Im),_MU,_I6);}),new T2(1,new T(function(){var _Nh=E(_MZ),_Ni=E(_Nh.b),_Nj=E(_Nh.c),_Nk=E(_Nh.a),_Nl=E(_ML),_Nm=E(_Nl.c),_Nn=E(_Nl.b),_No=E(_Nl.a),_Np=E(_MF),_Nq=E(_Np.c),_Nr=E(_Np.b),_Ns=E(_Np.a),_Nt=_Ni*_Nm-_Nn*_Nj,_Nu=_Nj*_No-_Nm*_Nk,_Nv=_Nk*_Nn-_No*_Ni,_Nw=B(_7n(_iT,_Nu*_Nq-_Nr*_Nv,_Nv*_Ns-_Nq*_Nt,_Nt*_Nr-_Ns*_Nu,_No,_Nn,_Nm));return new T6(0,_M5,_Mb,E(_Im),E(new T2(0,E(new T3(0,E(_Nt),E(_Nu),E(_Nv))),E(_Nw))),_MU,_I6);}),new T(function(){return B(_Mq(_Mt));}))):new T2(1,new T(function(){var _Nx=E(_MX),_Ny=E(_Nx.b),_Nz=E(_Nx.c),_NA=E(_Nx.a),_NB=E(_MO),_NC=_NB.a,_ND=_NB.b,_NE=_NB.c,_NF=B(_l5(_iT,_NA,_Ny,_Nz,_NC,_ND,_NE)),_NG=E(_MI),_NH=E(_NG.c),_NI=E(_NG.b),_NJ=E(_NG.a),_NK=B(_7n(_iT,_Ny*_NH-_NI*_Nz,_Nz*_NJ-_NH*_NA,_NA*_NI-_NJ*_Ny,_NC,_ND,_NE)),_NL=E(_MZ),_NM=E(_NL.b),_NN=E(_NL.c),_NO=E(_NL.a),_NP=E(_ML),_NQ=_NP.a,_NR=_NP.b,_NS=_NP.c,_NT=B(_l5(_iT,_NO,_NM,_NN,_NQ,_NR,_NS)),_NU=E(_MF),_NV=E(_NU.c),_NW=E(_NU.b),_NX=E(_NU.a),_NY=B(_7n(_iT,_NM*_NV-_NW*_NN,_NN*_NX-_NV*_NO,_NO*_NW-_NX*_NM,_NQ,_NR,_NS));return new T6(0,_M5,_Mb,E(new T2(0,E(new T3(0,E(_NF.a),E(_NF.b),E(_NF.c))),E(_NK))),E(new T2(0,E(new T3(0,E(_NT.a),E(_NT.b),E(_NT.c))),E(_NY))),_MU,_I7);}),new T(function(){return B(_Mq(_Mt));}));}};return B(_Mq(_Mm));});return new T2(0,new T2(1,_Mo,new T(function(){return E(E(_Mn).a);})),new T(function(){return E(E(_Mn).b);}));}else{var _NZ=new T(function(){var _O0=new T(function(){return _M5!=_Mb;}),_O1=function(_O2){var _O3=E(_O2);if(!_O3._){return __Z;}else{var _O4=_O3.b,_O5=E(_O3.a),_O6=E(_O5.b),_O7=E(_O5.a),_O8=E(_O5.c),_O9=_O8.a,_Oa=_O8.b,_Ob=E(_O5.e),_Oc=E(_O5.d),_Od=_Oc.a,_Oe=_Oc.b,_Of=E(_O5.f),_Og=new T(function(){var _Oh=B(_ki(_iT,_Of.a,_Of.b,_Of.c)),_Oi=Math.sqrt(B(_HV(_iT,_Od,_Oe,_Od,_Oe)));return new T3(0,_Oi*E(_Oh.a),_Oi*E(_Oh.b),_Oi*E(_Oh.c));}),_Oj=new T(function(){var _Ok=B(_ki(_iT,_Ob.a,_Ob.b,_Ob.c)),_Ol=Math.sqrt(B(_HV(_iT,_O9,_Oa,_O9,_Oa)));return new T3(0,_Ol*E(_Ok.a),_Ol*E(_Ok.b),_Ol*E(_Ok.c));}),_Om=new T(function(){var _On=B(A1(_Io,_O6)),_Oo=B(_ki(_iT,_On.a,_On.b,_On.c));return new T3(0,E(_Oo.a),E(_Oo.b),E(_Oo.c));}),_Op=new T(function(){var _Oq=B(A1(_Io,_O7)),_Or=B(_ki(_iT,_Oq.a,_Oq.b,_Oq.c));return new T3(0,E(_Or.a),E(_Or.b),E(_Or.c));}),_Os=E(_O6.a)+ -E(_O7.a),_Ot=E(_O6.b)+ -E(_O7.b),_Ou=E(_O6.c)+ -E(_O7.c),_Ov=new T(function(){return Math.sqrt(B(_7n(_iT,_Os,_Ot,_Ou,_Os,_Ot,_Ou)));}),_Ow=new T(function(){var _Ox=1/E(_Ov);return new T3(0,_Os*_Ox,_Ot*_Ox,_Ou*_Ox);}),_Oy=new T(function(){if(!E(_O5.g)){return E(_Ow);}else{var _Oz=E(_Ow);return new T3(0,-1*E(_Oz.a),-1*E(_Oz.b),-1*E(_Oz.c));}}),_OA=new T(function(){if(!E(_O5.h)){return E(_Ow);}else{var _OB=E(_Ow);return new T3(0,-1*E(_OB.a),-1*E(_OB.b),-1*E(_OB.c));}});return (!E(_O0))?new T2(1,new T(function(){var _OC=E(_Oy),_OD=E(_OC.b),_OE=E(_OC.c),_OF=E(_OC.a),_OG=E(_Op),_OH=E(_OG.c),_OI=E(_OG.b),_OJ=E(_OG.a),_OK=E(_Oj),_OL=E(_OK.c),_OM=E(_OK.b),_ON=E(_OK.a),_OO=_OD*_OH-_OI*_OE,_OP=_OE*_OJ-_OH*_OF,_OQ=_OF*_OI-_OJ*_OD,_OR=B(_7n(_iT,_OP*_OL-_OM*_OQ,_OQ*_ON-_OL*_OO,_OO*_OM-_ON*_OP,_OJ,_OI,_OH));return new T6(0,_M5,_Mb,E(new T2(0,E(new T3(0,E(_OO),E(_OP),E(_OQ))),E(_OR))),E(_Im),_Ov,_I6);}),new T2(1,new T(function(){var _OS=E(_OA),_OT=E(_OS.b),_OU=E(_OS.c),_OV=E(_OS.a),_OW=E(_Om),_OX=E(_OW.c),_OY=E(_OW.b),_OZ=E(_OW.a),_P0=E(_Og),_P1=E(_P0.c),_P2=E(_P0.b),_P3=E(_P0.a),_P4=_OT*_OX-_OY*_OU,_P5=_OU*_OZ-_OX*_OV,_P6=_OV*_OY-_OZ*_OT,_P7=B(_7n(_iT,_P5*_P1-_P2*_P6,_P6*_P3-_P1*_P4,_P4*_P2-_P3*_P5,_OZ,_OY,_OX));return new T6(0,_M5,_Mb,E(_Im),E(new T2(0,E(new T3(0,E(_P4),E(_P5),E(_P6))),E(_P7))),_Ov,_I6);}),new T(function(){return B(_O1(_O4));}))):new T2(1,new T(function(){var _P8=E(_Oy),_P9=E(_P8.b),_Pa=E(_P8.c),_Pb=E(_P8.a),_Pc=E(_Op),_Pd=_Pc.a,_Pe=_Pc.b,_Pf=_Pc.c,_Pg=B(_l5(_iT,_Pb,_P9,_Pa,_Pd,_Pe,_Pf)),_Ph=E(_Oj),_Pi=E(_Ph.c),_Pj=E(_Ph.b),_Pk=E(_Ph.a),_Pl=B(_7n(_iT,_P9*_Pi-_Pj*_Pa,_Pa*_Pk-_Pi*_Pb,_Pb*_Pj-_Pk*_P9,_Pd,_Pe,_Pf)),_Pm=E(_OA),_Pn=E(_Pm.b),_Po=E(_Pm.c),_Pp=E(_Pm.a),_Pq=E(_Om),_Pr=_Pq.a,_Ps=_Pq.b,_Pt=_Pq.c,_Pu=B(_l5(_iT,_Pp,_Pn,_Po,_Pr,_Ps,_Pt)),_Pv=E(_Og),_Pw=E(_Pv.c),_Px=E(_Pv.b),_Py=E(_Pv.a),_Pz=B(_7n(_iT,_Pn*_Pw-_Px*_Po,_Po*_Py-_Pw*_Pp,_Pp*_Px-_Py*_Pn,_Pr,_Ps,_Pt));return new T6(0,_M5,_Mb,E(new T2(0,E(new T3(0,E(_Pg.a),E(_Pg.b),E(_Pg.c))),E(_Pl))),E(new T2(0,E(new T3(0,E(_Pu.a),E(_Pu.b),E(_Pu.c))),E(_Pz))),_Ov,_I7);}),new T(function(){return B(_O1(_O4));}));}};return B(_O1(_Mm));});return new T2(0,new T2(1,_NZ,_o),new T4(0,E(_Mc),E(_Md),_Me,_Mf));}}}}}}}}}},_PA=B(_Ma(_M5,_M6,_M7,_M8,_M9,_));if(_M5!=_Iw){var _PB=B(_Ix(_M5+1|0,new T(function(){return E(E(_PA).b);},1),_));return new T2(0,new T2(1,new T(function(){return B(_Ih(E(_PA).a));}),new T(function(){return E(E(_PB).a);})),new T(function(){return E(E(_PB).b);}));}else{return new T2(0,new T2(1,new T(function(){return B(_Ih(E(_PA).a));}),_o),new T(function(){return E(E(_PA).b);}));}}else{if(_M5!=_Iw){var _PC=B(_M4(_M5+1|0,_M6,_M7,_M8,_M9,_));return new T2(0,new T2(1,_o,new T(function(){return E(E(_PC).a);})),new T(function(){return E(E(_PC).b);}));}else{return new T2(0,new T2(1,_o,_o),new T4(0,E(_M6),E(_M7),_M8,_M9));}}},_PD=B(_M4(_Iv,_Iv,_Iw,_Iu.c,_Iu.d,_));return new F(function(){return _HN(_,_PD);});}else{return new F(function(){return _HN(_,new T2(0,_o,_Iu));});}},_PE=new T(function(){return eval("passObject");}),_PF=new T(function(){return eval("__strict(refresh)");}),_PG=function(_PH,_){var _PI=__app0(E(_PF)),_PJ=__app0(E(_zJ)),_PK=E(_PH),_PL=_PK.c,_PM=_PK.d,_PN=E(_PK.a),_PO=E(_PK.b);if(_PN<=_PO){if(_PN>_PO){return E(_zH);}else{if(0>=_PL){return new F(function(){return _zU(_PL,0);});}else{var _PP=E(_PM[0]),_PQ=E(_PE),_PR=__app2(_PQ,_PN,B(_jF(new T2(1,new T2(0,_zF,_PP.h),new T2(1,new T2(0,_zE,_PP.i),_o)))));if(_PN!=_PO){var _PS=function(_PT,_){if(_PN>_PT){return E(_zH);}else{if(_PT>_PO){return E(_zH);}else{var _PU=_PT-_PN|0;if(0>_PU){return new F(function(){return _zU(_PL,_PU);});}else{if(_PU>=_PL){return new F(function(){return _zU(_PL,_PU);});}else{var _PV=E(_PM[_PU]),_PW=__app2(_PQ,_PT,B(_jF(new T2(1,new T2(0,_zF,_PV.h),new T2(1,new T2(0,_zE,_PV.i),_o)))));if(_PT!=_PO){var _PX=B(_PS(_PT+1|0,_));return new T2(1,_jE,_PX);}else{return _zZ;}}}}}},_PY=B(_PS(_PN+1|0,_)),_PZ=__app0(E(_zI)),_Q0=B(_Is(_PK,_));return new T(function(){return E(E(_Q0).b);});}else{var _Q1=__app0(E(_zI)),_Q2=B(_Is(_PK,_));return new T(function(){return E(E(_Q2).b);});}}}}else{var _Q3=__app0(E(_zI)),_Q4=B(_Is(_PK,_));return new T(function(){return E(E(_Q4).b);});}},_Q5=function(_Q6,_){while(1){var _Q7=E(_Q6);if(!_Q7._){return _jE;}else{var _Q8=_Q7.b,_Q9=E(_Q7.a);switch(_Q9._){case 0:var _Qa=B(A1(_Q9.a,_));_Q6=B(_f(_Q8,new T2(1,_Qa,_o)));continue;case 1:_Q6=B(_f(_Q8,_Q9.a));continue;default:_Q6=_Q8;continue;}}}},_Qb=function(_Qc,_Qd,_){var _Qe=E(_Qc);switch(_Qe._){case 0:var _Qf=B(A1(_Qe.a,_));return new F(function(){return _Q5(B(_f(_Qd,new T2(1,_Qf,_o))),_);});break;case 1:return new F(function(){return _Q5(B(_f(_Qd,_Qe.a)),_);});break;default:return new F(function(){return _Q5(_Qd,_);});}},_Qg=new T0(2),_Qh=function(_Qi){return new T0(2);},_Qj=function(_Qk,_Ql,_Qm){return function(_){var _Qn=E(_Qk),_Qo=rMV(_Qn),_Qp=E(_Qo);if(!_Qp._){var _Qq=new T(function(){var _Qr=new T(function(){return B(A1(_Qm,_jE));});return B(_f(_Qp.b,new T2(1,new T2(0,_Ql,function(_Qs){return E(_Qr);}),_o)));}),_=wMV(_Qn,new T2(0,_Qp.a,_Qq));return _Qg;}else{var _Qt=E(_Qp.a);if(!_Qt._){var _=wMV(_Qn,new T2(0,_Ql,_o));return new T(function(){return B(A1(_Qm,_jE));});}else{var _=wMV(_Qn,new T1(1,_Qt.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Qm,_jE));}),new T2(1,new T(function(){return B(A2(_Qt.a,_Ql,_Qh));}),_o)));}}};},_Qu=new T(function(){return E(_p4);}),_Qv=new T(function(){return eval("window.requestAnimationFrame");}),_Qw=new T1(1,_o),_Qx=function(_Qy,_Qz){return function(_){var _QA=E(_Qy),_QB=rMV(_QA),_QC=E(_QB);if(!_QC._){var _QD=_QC.a,_QE=E(_QC.b);if(!_QE._){var _=wMV(_QA,_Qw);return new T(function(){return B(A1(_Qz,_QD));});}else{var _QF=E(_QE.a),_=wMV(_QA,new T2(0,_QF.a,_QE.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Qz,_QD));}),new T2(1,new T(function(){return B(A1(_QF.b,_Qh));}),_o)));}}else{var _QG=new T(function(){var _QH=function(_QI){var _QJ=new T(function(){return B(A1(_Qz,_QI));});return function(_QK){return E(_QJ);};};return B(_f(_QC.a,new T2(1,_QH,_o)));}),_=wMV(_QA,new T1(1,_QG));return _Qg;}};},_QL=function(_QM,_QN){return new T1(0,B(_Qx(_QM,_QN)));},_QO=function(_QP,_QQ){var _QR=new T(function(){return new T1(0,B(_Qj(_QP,_jE,_Qh)));});return function(_){var _QS=__createJSFunc(2,function(_QT,_){var _QU=B(_Qb(_QR,_o,_));return _Qu;}),_QV=__app1(E(_Qv),_QS);return new T(function(){return B(_QL(_QP,_QQ));});};},_QW=new T1(1,_o),_QX=function(_QY,_QZ,_){var _R0=function(_){var _R1=nMV(_QY),_R2=_R1;return new T(function(){var _R3=new T(function(){return B(_R4(_));}),_R5=function(_){var _R6=rMV(_R2),_R7=B(A2(_QZ,_R6,_)),_=wMV(_R2,_R7),_R8=function(_){var _R9=nMV(_QW);return new T(function(){return new T1(0,B(_QO(_R9,function(_Ra){return E(_R3);})));});};return new T1(0,_R8);},_Rb=new T(function(){return new T1(0,_R5);}),_R4=function(_Rc){return E(_Rb);};return B(_R4(_));});};return new F(function(){return _Qb(new T1(0,_R0),_o,_);});},_Rd=function(_){var _Re=__app2(E(_0),E(_7W),E(_hg));return new F(function(){return _QX(_zD,_PG,_);});},_Rf=function(_){return new F(function(){return _Rd(_);});};
var hasteMain = function() {B(A(_Rf, [0]));};window.onload = hasteMain;