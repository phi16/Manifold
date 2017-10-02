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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(",y:"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr(",z:"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("})"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=new T(function(){return B(unCStr("-("));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr(")"));}),_I=new T1(0,_H),_J=new T2(1,_I,_w),_K=new T(function(){return B(unCStr("."));}),_L=new T1(0,0),_M=function(_N){while(1){var _O=E(_N);if(!_O._){_N=new T1(1,I_fromInt(_O.a));continue;}else{return new F(function(){return I_toString(_O.a);});}}},_P=function(_Q,_R){return new F(function(){return _n(fromJSStr(B(_M(_Q))),_R);});},_S=function(_T,_U){var _V=E(_T);if(!_V._){var _W=_V.a,_X=E(_U);return (_X._==0)?_W<_X.a:I_compareInt(_X.a,_W)>0;}else{var _Y=_V.a,_Z=E(_U);return (_Z._==0)?I_compareInt(_Y,_Z.a)<0:I_compare(_Y,_Z.a)<0;}},_10=41,_11=40,_12=new T1(0,0),_13=function(_14,_15,_16){if(_14<=6){return new F(function(){return _P(_15,_16);});}else{if(!B(_S(_15,_12))){return new F(function(){return _P(_15,_16);});}else{return new T2(1,_11,new T(function(){return B(_n(fromJSStr(B(_M(_15))),new T2(1,_10,_16)));}));}}},_17=new T(function(){return B(_13(0,_L,_w));}),_18=new T(function(){return B(_n(_17,_K));}),_19=new T1(0,_18),_1a=new T2(1,_19,_J),_1b=new T2(1,_G,_1a),_1c=new T1(1,_1b),_1d=new T2(1,_1c,_E),_1e=new T2(1,_B,_1d),_1f=new T2(1,_1c,_1e),_1g=new T2(1,_z,_1f),_1h=new T2(1,_1c,_1g),_1i=new T(function(){return B(unCStr("({x:"));}),_1j=new T1(0,_1i),_1k=new T2(1,_1j,_1h),_1l=function(_1m){return E(_1m);},_1n=new T(function(){return toJSStr(B(_e(_x,_1l,_1k)));}),_1o=new T1(0,1),_1p=new T(function(){return B(_13(0,_1o,_w));}),_1q=new T(function(){return B(_n(_1p,_K));}),_1r=new T1(0,_1q),_1s=new T2(1,_1r,_J),_1t=new T2(1,_G,_1s),_1u=new T(function(){return toJSStr(B(_e(_x,_1l,_1t)));}),_1v=function(_1w,_1x,_1y){var _1z=E(_1y);if(!_1z._){return new F(function(){return A1(_1x,_1z.a);});}else{var _1A=new T(function(){return B(_0(_1w));}),_1B=new T(function(){return B(_2(_1w));}),_1C=function(_1D){var _1E=E(_1D);if(!_1E._){return E(_1B);}else{return new F(function(){return A2(_1A,new T(function(){return B(_1v(_1w,_1x,_1E.a));}),new T(function(){return B(_1C(_1E.b));}));});}};return new F(function(){return _1C(_1z.a);});}},_1F=function(_1G,_1H,_1I){var _1J=new T(function(){return B(_0(_1G));}),_1K=new T(function(){return B(_2(_1G));}),_1L=function(_1M){var _1N=E(_1M);if(!_1N._){return E(_1K);}else{return new F(function(){return A2(_1J,new T(function(){return B(_1v(_1G,_1H,_1N.a));}),new T(function(){return B(_1L(_1N.b));}));});}};return new F(function(){return _1L(_1I);});},_1O=new T(function(){return B(unCStr("-("));}),_1P=new T1(0,_1O),_1Q=new T(function(){return B(unCStr(")"));}),_1R=new T1(0,_1Q),_1S=new T2(1,_1R,_w),_1T=new T(function(){return B(unCStr("."));}),_1U=new T(function(){return B(_13(0,_1o,_w));}),_1V=new T(function(){return B(_n(_1U,_1T));}),_1W=new T1(0,_1V),_1X=new T2(1,_1W,_1S),_1Y=new T2(1,_1P,_1X),_1Z=new T(function(){return toJSStr(B(_1F(_x,_1l,_1Y)));}),_20=new T(function(){return eval("__strict(compile)");}),_21=new T(function(){return B(unCStr(","));}),_22=new T1(0,_21),_23=new T(function(){return B(unCStr("pow("));}),_24=new T1(0,_23),_25=function(_26,_27){return new T1(1,new T2(1,_24,new T2(1,_26,new T2(1,_22,new T2(1,_27,_1S)))));},_28=new T(function(){return B(unCStr("acos("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1S)));},_2c=new T(function(){return B(unCStr("acosh("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1S)));},_2g=new T(function(){return B(unCStr("asin("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1S)));},_2k=new T(function(){return B(unCStr("asinh("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1S)));},_2o=new T(function(){return B(unCStr("atan("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1S)));},_2s=new T(function(){return B(unCStr("atanh("));}),_2t=new T1(0,_2s),_2u=function(_2v){return new T1(1,new T2(1,_2t,new T2(1,_2v,_1S)));},_2w=new T(function(){return B(unCStr("cos("));}),_2x=new T1(0,_2w),_2y=function(_2z){return new T1(1,new T2(1,_2x,new T2(1,_2z,_1S)));},_2A=new T(function(){return B(unCStr("cosh("));}),_2B=new T1(0,_2A),_2C=function(_2D){return new T1(1,new T2(1,_2B,new T2(1,_2D,_1S)));},_2E=new T(function(){return B(unCStr("exp("));}),_2F=new T1(0,_2E),_2G=function(_2H){return new T1(1,new T2(1,_2F,new T2(1,_2H,_1S)));},_2I=new T(function(){return B(unCStr("log("));}),_2J=new T1(0,_2I),_2K=function(_2L){return new T1(1,new T2(1,_2J,new T2(1,_2L,_1S)));},_2M=new T(function(){return B(unCStr(")/log("));}),_2N=new T1(0,_2M),_2O=function(_2P,_2Q){return new T1(1,new T2(1,_2J,new T2(1,_2Q,new T2(1,_2N,new T2(1,_2P,_1S)))));},_2R=new T(function(){return B(unCStr("pi"));}),_2S=new T1(0,_2R),_2T=new T(function(){return B(unCStr("sin("));}),_2U=new T1(0,_2T),_2V=function(_2W){return new T1(1,new T2(1,_2U,new T2(1,_2W,_1S)));},_2X=new T(function(){return B(unCStr("sinh("));}),_2Y=new T1(0,_2X),_2Z=function(_30){return new T1(1,new T2(1,_2Y,new T2(1,_30,_1S)));},_31=new T(function(){return B(unCStr("sqrt("));}),_32=new T1(0,_31),_33=function(_34){return new T1(1,new T2(1,_32,new T2(1,_34,_1S)));},_35=new T(function(){return B(unCStr("tan("));}),_36=new T1(0,_35),_37=function(_38){return new T1(1,new T2(1,_36,new T2(1,_38,_1S)));},_39=new T(function(){return B(unCStr("tanh("));}),_3a=new T1(0,_39),_3b=function(_3c){return new T1(1,new T2(1,_3a,new T2(1,_3c,_1S)));},_3d=new T(function(){return B(unCStr("("));}),_3e=new T1(0,_3d),_3f=new T(function(){return B(unCStr(")/("));}),_3g=new T1(0,_3f),_3h=function(_3i,_3j){return new T1(1,new T2(1,_3e,new T2(1,_3i,new T2(1,_3g,new T2(1,_3j,_1S)))));},_3k=new T1(0,1),_3l=function(_3m,_3n){var _3o=E(_3m);if(!_3o._){var _3p=_3o.a,_3q=E(_3n);if(!_3q._){var _3r=_3q.a;return (_3p!=_3r)?(_3p>_3r)?2:0:1;}else{var _3s=I_compareInt(_3q.a,_3p);return (_3s<=0)?(_3s>=0)?1:2:0;}}else{var _3t=_3o.a,_3u=E(_3n);if(!_3u._){var _3v=I_compareInt(_3t,_3u.a);return (_3v>=0)?(_3v<=0)?1:2:0;}else{var _3w=I_compare(_3t,_3u.a);return (_3w>=0)?(_3w<=0)?1:2:0;}}},_3x=new T(function(){return B(unCStr("base"));}),_3y=new T(function(){return B(unCStr("GHC.Exception"));}),_3z=new T(function(){return B(unCStr("ArithException"));}),_3A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3x,_3y,_3z),_3B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3A,_w,_w),_3C=function(_3D){return E(_3B);},_3E=function(_3F){return E(E(_3F).a);},_3G=function(_3H,_3I,_3J){var _3K=B(A1(_3H,_)),_3L=B(A1(_3I,_)),_3M=hs_eqWord64(_3K.a,_3L.a);if(!_3M){return __Z;}else{var _3N=hs_eqWord64(_3K.b,_3L.b);return (!_3N)?__Z:new T1(1,_3J);}},_3O=function(_3P){var _3Q=E(_3P);return new F(function(){return _3G(B(_3E(_3Q.a)),_3C,_3Q.b);});},_3R=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3S=new T(function(){return B(unCStr("denormal"));}),_3T=new T(function(){return B(unCStr("divide by zero"));}),_3U=new T(function(){return B(unCStr("loss of precision"));}),_3V=new T(function(){return B(unCStr("arithmetic underflow"));}),_3W=new T(function(){return B(unCStr("arithmetic overflow"));}),_3X=function(_3Y,_3Z){switch(E(_3Y)){case 0:return new F(function(){return _n(_3W,_3Z);});break;case 1:return new F(function(){return _n(_3V,_3Z);});break;case 2:return new F(function(){return _n(_3U,_3Z);});break;case 3:return new F(function(){return _n(_3T,_3Z);});break;case 4:return new F(function(){return _n(_3S,_3Z);});break;default:return new F(function(){return _n(_3R,_3Z);});}},_40=function(_41){return new F(function(){return _3X(_41,_w);});},_42=function(_43,_44,_45){return new F(function(){return _3X(_44,_45);});},_46=44,_47=93,_48=91,_49=function(_4a,_4b,_4c){var _4d=E(_4b);if(!_4d._){return new F(function(){return unAppCStr("[]",_4c);});}else{var _4e=new T(function(){var _4f=new T(function(){var _4g=function(_4h){var _4i=E(_4h);if(!_4i._){return E(new T2(1,_47,_4c));}else{var _4j=new T(function(){return B(A2(_4a,_4i.a,new T(function(){return B(_4g(_4i.b));})));});return new T2(1,_46,_4j);}};return B(_4g(_4d.b));});return B(A2(_4a,_4d.a,_4f));});return new T2(1,_48,_4e);}},_4k=function(_4l,_4m){return new F(function(){return _49(_3X,_4l,_4m);});},_4n=new T3(0,_42,_40,_4k),_4o=new T(function(){return new T5(0,_3C,_4n,_4p,_3O,_40);}),_4p=function(_4q){return new T2(0,_4o,_4q);},_4r=3,_4s=new T(function(){return B(_4p(_4r));}),_4t=new T(function(){return die(_4s);}),_4u=function(_4v,_4w){var _4x=E(_4v);return (_4x._==0)?_4x.a*Math.pow(2,_4w):I_toNumber(_4x.a)*Math.pow(2,_4w);},_4y=function(_4z,_4A){var _4B=E(_4z);if(!_4B._){var _4C=_4B.a,_4D=E(_4A);return (_4D._==0)?_4C==_4D.a:(I_compareInt(_4D.a,_4C)==0)?true:false;}else{var _4E=_4B.a,_4F=E(_4A);return (_4F._==0)?(I_compareInt(_4E,_4F.a)==0)?true:false:(I_compare(_4E,_4F.a)==0)?true:false;}},_4G=function(_4H){var _4I=E(_4H);if(!_4I._){return E(_4I.a);}else{return new F(function(){return I_toInt(_4I.a);});}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a,_4Q=addC(_4N,_4P);if(!E(_4Q.b)){return new T1(0,_4Q.a);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R._){_4K=_4M;_4L=new T1(1,I_fromInt(_4R.a));continue;}else{return new T1(1,I_add(_4M.a,_4R.a));}}}},_4S=function(_4T,_4U){while(1){var _4V=E(_4T);if(!_4V._){var _4W=E(_4V.a);if(_4W==(-2147483648)){_4T=new T1(1,I_fromInt(-2147483648));continue;}else{var _4X=E(_4U);if(!_4X._){var _4Y=_4X.a;return new T2(0,new T1(0,quot(_4W,_4Y)),new T1(0,_4W%_4Y));}else{_4T=new T1(1,I_fromInt(_4W));_4U=_4X;continue;}}}else{var _4Z=E(_4U);if(!_4Z._){_4T=_4V;_4U=new T1(1,I_fromInt(_4Z.a));continue;}else{var _50=I_quotRem(_4V.a,_4Z.a);return new T2(0,new T1(1,_50.a),new T1(1,_50.b));}}}},_51=new T1(0,0),_52=function(_53,_54){while(1){var _55=E(_53);if(!_55._){_53=new T1(1,I_fromInt(_55.a));continue;}else{return new T1(1,I_shiftLeft(_55.a,_54));}}},_56=function(_57,_58,_59){if(!B(_4y(_59,_51))){var _5a=B(_4S(_58,_59)),_5b=_5a.a;switch(B(_3l(B(_52(_5a.b,1)),_59))){case 0:return new F(function(){return _4u(_5b,_57);});break;case 1:if(!(B(_4G(_5b))&1)){return new F(function(){return _4u(_5b,_57);});}else{return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}break;default:return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}}else{return E(_4t);}},_5c=function(_5d,_5e){var _5f=E(_5d);if(!_5f._){var _5g=_5f.a,_5h=E(_5e);return (_5h._==0)?_5g>_5h.a:I_compareInt(_5h.a,_5g)<0;}else{var _5i=_5f.a,_5j=E(_5e);return (_5j._==0)?I_compareInt(_5i,_5j.a)>0:I_compare(_5i,_5j.a)>0;}},_5k=new T1(0,1),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5n=new T(function(){return B(unCStr("PatternMatchFail"));}),_5o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5l,_5m,_5n),_5p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5o,_w,_w),_5q=function(_5r){return E(_5p);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _3G(B(_3E(_5u.a)),_5q,_5u.b);});},_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return new T2(0,_5z,_5y);},_5A=function(_5B,_5C){return new F(function(){return _n(E(_5B).a,_5C);});},_5D=function(_5E,_5F){return new F(function(){return _49(_5A,_5E,_5F);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _n(E(_5I).a,_5J);});},_5K=new T3(0,_5G,_5v,_5D),_5z=new T(function(){return new T5(0,_5q,_5K,_5x,_5s,_5v);}),_5L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5M=function(_5N){return E(E(_5N).c);},_5O=function(_5P,_5Q){return new F(function(){return die(new T(function(){return B(A2(_5M,_5Q,_5P));}));});},_5R=function(_5S,_4q){return new F(function(){return _5O(_5S,_4q);});},_5T=function(_5U,_5V){var _5W=E(_5V);if(!_5W._){return new T2(0,_w,_w);}else{var _5X=_5W.a;if(!B(A1(_5U,_5X))){return new T2(0,_w,_5W);}else{var _5Y=new T(function(){var _5Z=B(_5T(_5U,_5W.b));return new T2(0,_5Z.a,_5Z.b);});return new T2(0,new T2(1,_5X,new T(function(){return E(E(_5Y).a);})),new T(function(){return E(E(_5Y).b);}));}}},_60=32,_61=new T(function(){return B(unCStr("\n"));}),_62=function(_63){return (E(_63)==124)?false:true;},_64=function(_65,_66){var _67=B(_5T(_62,B(unCStr(_65)))),_68=_67.a,_69=function(_6a,_6b){var _6c=new T(function(){var _6d=new T(function(){return B(_n(_66,new T(function(){return B(_n(_6b,_61));},1)));});return B(unAppCStr(": ",_6d));},1);return new F(function(){return _n(_6a,_6c);});},_6e=E(_67.b);if(!_6e._){return new F(function(){return _69(_68,_w);});}else{if(E(_6e.a)==124){return new F(function(){return _69(_68,new T2(1,_60,_6e.b));});}else{return new F(function(){return _69(_68,_w);});}}},_6f=function(_6g){return new F(function(){return _5R(new T1(0,new T(function(){return B(_64(_6g,_5L));})),_5z);});},_6h=function(_6i){var _6j=function(_6k,_6l){while(1){if(!B(_S(_6k,_6i))){if(!B(_5c(_6k,_6i))){if(!B(_4y(_6k,_6i))){return new F(function(){return _6f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_6l);}}else{return _6l-1|0;}}else{var _6m=B(_52(_6k,1)),_6n=_6l+1|0;_6k=_6m;_6l=_6n;continue;}}};return new F(function(){return _6j(_5k,0);});},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){var _6r=_6q.a>>>0;if(!_6r){return -1;}else{var _6s=function(_6t,_6u){while(1){if(_6t>=_6r){if(_6t<=_6r){if(_6t!=_6r){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6u);}}else{return _6u-1|0;}}else{var _6v=imul(_6t,2)>>>0,_6w=_6u+1|0;_6t=_6v;_6u=_6w;continue;}}};return new F(function(){return _6s(1,0);});}}else{return new F(function(){return _6h(_6q);});}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){var _6A=_6z.a>>>0;if(!_6A){return new T2(0,-1,0);}else{var _6B=function(_6C,_6D){while(1){if(_6C>=_6A){if(_6C<=_6A){if(_6C!=_6A){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6D);}}else{return _6D-1|0;}}else{var _6E=imul(_6C,2)>>>0,_6F=_6D+1|0;_6C=_6E;_6D=_6F;continue;}}};return new T2(0,B(_6B(1,0)),(_6A&_6A-1>>>0)>>>0&4294967295);}}else{var _6G=_6z.a;return new T2(0,B(_6o(_6z)),I_compareInt(I_and(_6G,I_sub(_6G,I_fromInt(1))),0));}},_6H=function(_6I,_6J){var _6K=E(_6I);if(!_6K._){var _6L=_6K.a,_6M=E(_6J);return (_6M._==0)?_6L<=_6M.a:I_compareInt(_6M.a,_6L)>=0;}else{var _6N=_6K.a,_6O=E(_6J);return (_6O._==0)?I_compareInt(_6N,_6O.a)<=0:I_compare(_6N,_6O.a)<=0;}},_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){var _6T=_6S.a,_6U=E(_6R);if(!_6U._){return new T1(0,(_6T>>>0&_6U.a>>>0)>>>0&4294967295);}else{_6Q=new T1(1,I_fromInt(_6T));_6R=_6U;continue;}}else{var _6V=E(_6R);if(!_6V._){_6Q=_6S;_6R=new T1(1,I_fromInt(_6V.a));continue;}else{return new T1(1,I_and(_6S.a,_6V.a));}}}},_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){var _70=_6Z.a,_71=E(_6Y);if(!_71._){var _72=_71.a,_73=subC(_70,_72);if(!E(_73.b)){return new T1(0,_73.a);}else{_6X=new T1(1,I_fromInt(_70));_6Y=new T1(1,I_fromInt(_72));continue;}}else{_6X=new T1(1,I_fromInt(_70));_6Y=_71;continue;}}else{var _74=E(_6Y);if(!_74._){_6X=_6Z;_6Y=new T1(1,I_fromInt(_74.a));continue;}else{return new T1(1,I_sub(_6Z.a,_74.a));}}}},_75=new T1(0,2),_76=function(_77,_78){var _79=E(_77);if(!_79._){var _7a=(_79.a>>>0&(2<<_78>>>0)-1>>>0)>>>0,_7b=1<<_78>>>0;return (_7b<=_7a)?(_7b>=_7a)?1:2:0;}else{var _7c=B(_6P(_79,B(_6W(B(_52(_75,_78)),_5k)))),_7d=B(_52(_5k,_78));return (!B(_5c(_7d,_7c)))?(!B(_S(_7d,_7c)))?1:2:0;}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){_7f=new T1(1,I_fromInt(_7h.a));continue;}else{return new T1(1,I_shiftRight(_7h.a,_7g));}}},_7i=function(_7j,_7k,_7l,_7m){var _7n=B(_6x(_7m)),_7o=_7n.a;if(!E(_7n.b)){var _7p=B(_6o(_7l));if(_7p<((_7o+_7j|0)-1|0)){var _7q=_7o+(_7j-_7k|0)|0;if(_7q>0){if(_7q>_7p){if(_7q<=(_7p+1|0)){if(!E(B(_6x(_7l)).b)){return 0;}else{return new F(function(){return _4u(_3k,_7j-_7k|0);});}}else{return 0;}}else{var _7r=B(_7e(_7l,_7q));switch(B(_76(_7l,_7q-1|0))){case 0:return new F(function(){return _4u(_7r,_7j-_7k|0);});break;case 1:if(!(B(_4G(_7r))&1)){return new F(function(){return _4u(_7r,_7j-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}break;default:return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}}}else{return new F(function(){return _4u(_7l,(_7j-_7k|0)-_7q|0);});}}else{if(_7p>=_7k){var _7s=B(_7e(_7l,(_7p+1|0)-_7k|0));switch(B(_76(_7l,_7p-_7k|0))){case 0:return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});break;case 2:return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});break;default:if(!(B(_4G(_7s))&1)){return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});}}}else{return new F(function(){return _4u(_7l, -_7o);});}}}else{var _7t=B(_6o(_7l))-_7o|0,_7u=function(_7v){var _7w=function(_7x,_7y){if(!B(_6H(B(_52(_7y,_7k)),_7x))){return new F(function(){return _56(_7v-_7k|0,_7x,_7y);});}else{return new F(function(){return _56((_7v-_7k|0)+1|0,_7x,B(_52(_7y,1)));});}};if(_7v>=_7k){if(_7v!=_7k){return new F(function(){return _7w(_7l,new T(function(){return B(_52(_7m,_7v-_7k|0));}));});}else{return new F(function(){return _7w(_7l,_7m);});}}else{return new F(function(){return _7w(new T(function(){return B(_52(_7l,_7k-_7v|0));}),_7m);});}};if(_7j>_7t){return new F(function(){return _7u(_7j);});}else{return new F(function(){return _7u(_7t);});}}},_7z=new T1(0,2147483647),_7A=new T(function(){return B(_4J(_7z,_5k));}),_7B=function(_7C){var _7D=E(_7C);if(!_7D._){var _7E=E(_7D.a);return (_7E==(-2147483648))?E(_7A):new T1(0, -_7E);}else{return new T1(1,I_negate(_7D.a));}},_7F=new T(function(){return 0/0;}),_7G=new T(function(){return -1/0;}),_7H=new T(function(){return 1/0;}),_7I=0,_7J=function(_7K,_7L){if(!B(_4y(_7L,_51))){if(!B(_4y(_7K,_51))){if(!B(_S(_7K,_51))){return new F(function(){return _7i(-1021,53,_7K,_7L);});}else{return  -B(_7i(-1021,53,B(_7B(_7K)),_7L));}}else{return E(_7I);}}else{return (!B(_4y(_7K,_51)))?(!B(_S(_7K,_51)))?E(_7H):E(_7G):E(_7F);}},_7M=function(_7N){return new T1(0,new T(function(){var _7O=E(_7N),_7P=jsShow(B(_7J(_7O.a,_7O.b)));return fromJSStr(_7P);}));},_7Q=new T(function(){return B(unCStr("1./("));}),_7R=new T1(0,_7Q),_7S=function(_7T){return new T1(1,new T2(1,_7R,new T2(1,_7T,_1S)));},_7U=new T(function(){return B(unCStr(")+("));}),_7V=new T1(0,_7U),_7W=function(_7X,_7Y){return new T1(1,new T2(1,_3e,new T2(1,_7X,new T2(1,_7V,new T2(1,_7Y,_1S)))));},_7Z=function(_80){return new T1(1,new T2(1,_1P,new T2(1,_80,_1S)));},_81=new T(function(){return B(unCStr(")*("));}),_82=new T1(0,_81),_83=function(_84,_85){return new T1(1,new T2(1,_3e,new T2(1,_84,new T2(1,_82,new T2(1,_85,_1S)))));},_86=function(_87){return E(E(_87).a);},_88=function(_89){return E(E(_89).d);},_8a=function(_8b,_8c){return new F(function(){return A3(_86,_8d,_8b,new T(function(){return B(A2(_88,_8d,_8c));}));});},_8e=new T(function(){return B(unCStr("abs("));}),_8f=new T1(0,_8e),_8g=function(_8h){return new T1(1,new T2(1,_8f,new T2(1,_8h,_1S)));},_8i=function(_8j){return new T1(0,new T(function(){return B(_n(B(_13(0,_8j,_w)),_1T));}));},_8k=new T(function(){return B(unCStr("sign("));}),_8l=new T1(0,_8k),_8m=function(_8n){return new T1(1,new T2(1,_8l,new T2(1,_8n,_1S)));},_8d=new T(function(){return {_:0,a:_7W,b:_8a,c:_83,d:_7Z,e:_8g,f:_8m,g:_8i};}),_8o=new T4(0,_8d,_3h,_7S,_7M),_8p={_:0,a:_8o,b:_2S,c:_2G,d:_2K,e:_33,f:_25,g:_2O,h:_2V,i:_2y,j:_37,k:_2i,l:_2a,m:_2q,n:_2Z,o:_2C,p:_3b,q:_2m,r:_2e,s:_2u},_8q=function(_8r){return E(E(_8r).a);},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v){return E(E(_8v).c);},_8w=function(_8x,_8y,_8z,_8A,_8B,_8C,_8D){var _8E=B(_8s(B(_8q(_8x)))),_8F=new T(function(){return B(A3(_86,_8E,new T(function(){return B(A3(_8u,_8E,_8y,_8B));}),new T(function(){return B(A3(_8u,_8E,_8z,_8C));})));});return new F(function(){return A3(_86,_8E,_8F,new T(function(){return B(A3(_8u,_8E,_8A,_8D));}));});},_8G=function(_8H){return E(E(_8H).b);},_8I=function(_8J){return E(E(_8J).g);},_8K=function(_8L){return E(E(_8L).e);},_8M=function(_8N,_8O){var _8P=B(_8s(B(_8q(_8N)))),_8Q=new T(function(){return B(A2(_8K,_8N,new T(function(){var _8R=E(_8O),_8S=_8R.a,_8T=_8R.b,_8U=_8R.c;return B(_8w(_8N,_8S,_8T,_8U,_8S,_8T,_8U));})));});return new F(function(){return A3(_8G,_8P,_8Q,new T(function(){return B(A2(_8I,_8P,_1o));}));});},_8V=new T(function(){return B(unCStr("x"));}),_8W=new T1(0,_8V),_8X=new T(function(){return B(unCStr("y"));}),_8Y=new T1(0,_8X),_8Z=new T(function(){return B(unCStr("z"));}),_90=new T1(0,_8Z),_91=new T3(0,E(_8W),E(_8Y),E(_90)),_92=new T(function(){return B(_8M(_8p,_91));}),_93=new T(function(){return toJSStr(B(_1v(_x,_1l,_92)));}),_94=new T(function(){return B(unCStr("(/=) is not defined"));}),_95=new T(function(){return B(err(_94));}),_96=new T(function(){return B(unCStr("(==) is not defined"));}),_97=new T(function(){return B(err(_96));}),_98=new T2(0,_97,_95),_99=new T(function(){return B(unCStr("(<) is not defined"));}),_9a=new T(function(){return B(err(_99));}),_9b=new T(function(){return B(unCStr("(<=) is not defined"));}),_9c=new T(function(){return B(err(_9b));}),_9d=new T(function(){return B(unCStr("(>) is not defined"));}),_9e=new T(function(){return B(err(_9d));}),_9f=new T(function(){return B(unCStr("(>=) is not defined"));}),_9g=new T(function(){return B(err(_9f));}),_9h=new T(function(){return B(unCStr("compare is not defined"));}),_9i=new T(function(){return B(err(_9h));}),_9j=new T(function(){return B(unCStr("max("));}),_9k=new T1(0,_9j),_9l=function(_9m,_9n){return new T1(1,new T2(1,_9k,new T2(1,_9m,new T2(1,_22,new T2(1,_9n,_1S)))));},_9o=new T(function(){return B(unCStr("min("));}),_9p=new T1(0,_9o),_9q=function(_9r,_9s){return new T1(1,new T2(1,_9p,new T2(1,_9r,new T2(1,_22,new T2(1,_9s,_1S)))));},_9t={_:0,a:_98,b:_9i,c:_9a,d:_9c,e:_9e,f:_9g,g:_9l,h:_9q},_9u=new T2(0,_8p,_9t),_9v=function(_9w,_9x){var _9y=E(_9w);return E(_9x);},_9z=function(_9A,_9B){var _9C=E(_9B);return E(_9A);},_9D=function(_9E,_9F){var _9G=E(_9E),_9H=E(_9F);return new T3(0,E(B(A1(_9G.a,_9H.a))),E(B(A1(_9G.b,_9H.b))),E(B(A1(_9G.c,_9H.c))));},_9I=function(_9J,_9K,_9L){return new T3(0,E(_9J),E(_9K),E(_9L));},_9M=function(_9N){return new F(function(){return _9I(_9N,_9N,_9N);});},_9O=function(_9P,_9Q){var _9R=E(_9Q),_9S=E(_9P);return new T3(0,E(_9S),E(_9S),E(_9S));},_9T=function(_9U,_9V){var _9W=E(_9V);return new T3(0,E(B(A1(_9U,_9W.a))),E(B(A1(_9U,_9W.b))),E(B(A1(_9U,_9W.c))));},_9X=new T2(0,_9T,_9O),_9Y=new T5(0,_9X,_9M,_9D,_9v,_9z),_9Z=new T1(0,0),_a0=function(_a1){var _a2=B(A2(_8I,_a1,_1o)),_a3=B(A2(_8I,_a1,_9Z));return new T3(0,E(new T3(0,E(_a2),E(_a3),E(_a3))),E(new T3(0,E(_a3),E(_a2),E(_a3))),E(new T3(0,E(_a3),E(_a3),E(_a2))));},_a4=function(_a5){return E(E(_a5).a);},_a6=function(_a7){return E(E(_a7).f);},_a8=function(_a9){return E(E(_a9).b);},_aa=function(_ab){return E(E(_ab).c);},_ac=function(_ad){return E(E(_ad).a);},_ae=function(_af){return E(E(_af).d);},_ag=function(_ah,_ai,_aj,_ak,_al){var _am=new T(function(){return E(E(E(_ah).c).a);}),_an=new T(function(){var _ao=E(_ah).a,_ap=new T(function(){var _aq=new T(function(){return B(_8q(_am));}),_ar=new T(function(){return B(_8s(_aq));}),_as=new T(function(){return B(A2(_ae,_am,_ai));}),_at=new T(function(){return B(A3(_a6,_am,_ai,_ak));}),_au=function(_av,_aw){var _ax=new T(function(){var _ay=new T(function(){return B(A3(_a8,_aq,new T(function(){return B(A3(_8u,_ar,_ak,_av));}),_ai));});return B(A3(_86,_ar,_ay,new T(function(){return B(A3(_8u,_ar,_aw,_as));})));});return new F(function(){return A3(_8u,_ar,_at,_ax);});};return B(A3(_ac,B(_a4(_ao)),_au,_aj));});return B(A3(_aa,_ao,_ap,_al));});return new T2(0,new T(function(){return B(A3(_a6,_am,_ai,_ak));}),_an);},_az=function(_aA,_aB,_aC,_aD){var _aE=E(_aC),_aF=E(_aD),_aG=B(_ag(_aB,_aE.a,_aE.b,_aF.a,_aF.b));return new T2(0,_aG.a,_aG.b);},_aH=new T1(0,1),_aI=function(_aJ){return E(E(_aJ).l);},_aK=function(_aL,_aM,_aN){var _aO=new T(function(){return E(E(E(_aL).c).a);}),_aP=new T(function(){var _aQ=new T(function(){return B(_8q(_aO));}),_aR=new T(function(){var _aS=B(_8s(_aQ)),_aT=new T(function(){var _aU=new T(function(){return B(A3(_8G,_aS,new T(function(){return B(A2(_8I,_aS,_aH));}),new T(function(){return B(A3(_8u,_aS,_aM,_aM));})));});return B(A2(_8K,_aO,_aU));});return B(A2(_88,_aS,_aT));});return B(A3(_ac,B(_a4(E(_aL).a)),function(_aV){return new F(function(){return A3(_a8,_aQ,_aV,_aR);});},_aN));});return new T2(0,new T(function(){return B(A2(_aI,_aO,_aM));}),_aP);},_aW=function(_aX,_aY,_aZ){var _b0=E(_aZ),_b1=B(_aK(_aY,_b0.a,_b0.b));return new T2(0,_b1.a,_b1.b);},_b2=function(_b3){return E(E(_b3).r);},_b4=function(_b5,_b6,_b7){var _b8=new T(function(){return E(E(E(_b5).c).a);}),_b9=new T(function(){var _ba=new T(function(){return B(_8q(_b8));}),_bb=new T(function(){var _bc=new T(function(){var _bd=B(_8s(_ba));return B(A3(_8G,_bd,new T(function(){return B(A3(_8u,_bd,_b6,_b6));}),new T(function(){return B(A2(_8I,_bd,_aH));})));});return B(A2(_8K,_b8,_bc));});return B(A3(_ac,B(_a4(E(_b5).a)),function(_be){return new F(function(){return A3(_a8,_ba,_be,_bb);});},_b7));});return new T2(0,new T(function(){return B(A2(_b2,_b8,_b6));}),_b9);},_bf=function(_bg,_bh,_bi){var _bj=E(_bi),_bk=B(_b4(_bh,_bj.a,_bj.b));return new T2(0,_bk.a,_bk.b);},_bl=function(_bm){return E(E(_bm).k);},_bn=function(_bo,_bp,_bq){var _br=new T(function(){return E(E(E(_bo).c).a);}),_bs=new T(function(){var _bt=new T(function(){return B(_8q(_br));}),_bu=new T(function(){var _bv=new T(function(){var _bw=B(_8s(_bt));return B(A3(_8G,_bw,new T(function(){return B(A2(_8I,_bw,_aH));}),new T(function(){return B(A3(_8u,_bw,_bp,_bp));})));});return B(A2(_8K,_br,_bv));});return B(A3(_ac,B(_a4(E(_bo).a)),function(_bx){return new F(function(){return A3(_a8,_bt,_bx,_bu);});},_bq));});return new T2(0,new T(function(){return B(A2(_bl,_br,_bp));}),_bs);},_by=function(_bz,_bA,_bB){var _bC=E(_bB),_bD=B(_bn(_bA,_bC.a,_bC.b));return new T2(0,_bD.a,_bD.b);},_bE=function(_bF){return E(E(_bF).q);},_bG=function(_bH,_bI,_bJ){var _bK=new T(function(){return E(E(E(_bH).c).a);}),_bL=new T(function(){var _bM=new T(function(){return B(_8q(_bK));}),_bN=new T(function(){var _bO=new T(function(){var _bP=B(_8s(_bM));return B(A3(_86,_bP,new T(function(){return B(A3(_8u,_bP,_bI,_bI));}),new T(function(){return B(A2(_8I,_bP,_aH));})));});return B(A2(_8K,_bK,_bO));});return B(A3(_ac,B(_a4(E(_bH).a)),function(_bQ){return new F(function(){return A3(_a8,_bM,_bQ,_bN);});},_bJ));});return new T2(0,new T(function(){return B(A2(_bE,_bK,_bI));}),_bL);},_bR=function(_bS,_bT,_bU){var _bV=E(_bU),_bW=B(_bG(_bT,_bV.a,_bV.b));return new T2(0,_bW.a,_bW.b);},_bX=function(_bY){return E(E(_bY).m);},_bZ=function(_c0,_c1,_c2){var _c3=new T(function(){return E(E(E(_c0).c).a);}),_c4=new T(function(){var _c5=new T(function(){return B(_8q(_c3));}),_c6=new T(function(){var _c7=B(_8s(_c5));return B(A3(_86,_c7,new T(function(){return B(A2(_8I,_c7,_aH));}),new T(function(){return B(A3(_8u,_c7,_c1,_c1));})));});return B(A3(_ac,B(_a4(E(_c0).a)),function(_c8){return new F(function(){return A3(_a8,_c5,_c8,_c6);});},_c2));});return new T2(0,new T(function(){return B(A2(_bX,_c3,_c1));}),_c4);},_c9=function(_ca,_cb,_cc){var _cd=E(_cc),_ce=B(_bZ(_cb,_cd.a,_cd.b));return new T2(0,_ce.a,_ce.b);},_cf=function(_cg){return E(E(_cg).s);},_ch=function(_ci,_cj,_ck){var _cl=new T(function(){return E(E(E(_ci).c).a);}),_cm=new T(function(){var _cn=new T(function(){return B(_8q(_cl));}),_co=new T(function(){var _cp=B(_8s(_cn));return B(A3(_8G,_cp,new T(function(){return B(A2(_8I,_cp,_aH));}),new T(function(){return B(A3(_8u,_cp,_cj,_cj));})));});return B(A3(_ac,B(_a4(E(_ci).a)),function(_cq){return new F(function(){return A3(_a8,_cn,_cq,_co);});},_ck));});return new T2(0,new T(function(){return B(A2(_cf,_cl,_cj));}),_cm);},_cr=function(_cs,_ct,_cu){var _cv=E(_cu),_cw=B(_ch(_ct,_cv.a,_cv.b));return new T2(0,_cw.a,_cw.b);},_cx=function(_cy){return E(E(_cy).i);},_cz=function(_cA){return E(E(_cA).h);},_cB=function(_cC,_cD,_cE){var _cF=new T(function(){return E(E(E(_cC).c).a);}),_cG=new T(function(){var _cH=new T(function(){return B(_8s(new T(function(){return B(_8q(_cF));})));}),_cI=new T(function(){return B(A2(_88,_cH,new T(function(){return B(A2(_cz,_cF,_cD));})));});return B(A3(_ac,B(_a4(E(_cC).a)),function(_cJ){return new F(function(){return A3(_8u,_cH,_cJ,_cI);});},_cE));});return new T2(0,new T(function(){return B(A2(_cx,_cF,_cD));}),_cG);},_cK=function(_cL,_cM,_cN){var _cO=E(_cN),_cP=B(_cB(_cM,_cO.a,_cO.b));return new T2(0,_cP.a,_cP.b);},_cQ=function(_cR){return E(E(_cR).o);},_cS=function(_cT){return E(E(_cT).n);},_cU=function(_cV,_cW,_cX){var _cY=new T(function(){return E(E(E(_cV).c).a);}),_cZ=new T(function(){var _d0=new T(function(){return B(_8s(new T(function(){return B(_8q(_cY));})));}),_d1=new T(function(){return B(A2(_cS,_cY,_cW));});return B(A3(_ac,B(_a4(E(_cV).a)),function(_d2){return new F(function(){return A3(_8u,_d0,_d2,_d1);});},_cX));});return new T2(0,new T(function(){return B(A2(_cQ,_cY,_cW));}),_cZ);},_d3=function(_d4,_d5,_d6){var _d7=E(_d6),_d8=B(_cU(_d5,_d7.a,_d7.b));return new T2(0,_d8.a,_d8.b);},_d9=function(_da){return E(E(_da).c);},_db=function(_dc,_dd,_de){var _df=new T(function(){return E(E(E(_dc).c).a);}),_dg=new T(function(){var _dh=new T(function(){return B(_8s(new T(function(){return B(_8q(_df));})));}),_di=new T(function(){return B(A2(_d9,_df,_dd));});return B(A3(_ac,B(_a4(E(_dc).a)),function(_dj){return new F(function(){return A3(_8u,_dh,_dj,_di);});},_de));});return new T2(0,new T(function(){return B(A2(_d9,_df,_dd));}),_dg);},_dk=function(_dl,_dm,_dn){var _do=E(_dn),_dp=B(_db(_dm,_do.a,_do.b));return new T2(0,_dp.a,_dp.b);},_dq=function(_dr,_ds,_dt){var _du=new T(function(){return E(E(E(_dr).c).a);}),_dv=new T(function(){var _dw=new T(function(){return B(_8q(_du));}),_dx=new T(function(){return B(_8s(_dw));}),_dy=new T(function(){return B(A3(_a8,_dw,new T(function(){return B(A2(_8I,_dx,_aH));}),_ds));});return B(A3(_ac,B(_a4(E(_dr).a)),function(_dz){return new F(function(){return A3(_8u,_dx,_dz,_dy);});},_dt));});return new T2(0,new T(function(){return B(A2(_ae,_du,_ds));}),_dv);},_dA=function(_dB,_dC,_dD){var _dE=E(_dD),_dF=B(_dq(_dC,_dE.a,_dE.b));return new T2(0,_dF.a,_dF.b);},_dG=function(_dH,_dI,_dJ,_dK){var _dL=new T(function(){return E(E(_dI).c);}),_dM=new T3(0,new T(function(){return E(E(_dI).a);}),new T(function(){return E(E(_dI).b);}),new T2(0,new T(function(){return E(E(_dL).a);}),new T(function(){return E(E(_dL).b);})));return new F(function(){return A3(_a8,_dH,new T(function(){var _dN=E(_dK),_dO=B(_dq(_dM,_dN.a,_dN.b));return new T2(0,_dO.a,_dO.b);}),new T(function(){var _dP=E(_dJ),_dQ=B(_dq(_dM,_dP.a,_dP.b));return new T2(0,_dQ.a,_dQ.b);}));});},_dR=function(_dS){return E(E(_dS).b);},_dT=function(_dU){return E(E(_dU).b);},_dV=function(_dW){var _dX=new T(function(){return E(E(E(_dW).c).a);}),_dY=new T(function(){return B(A2(_dT,E(_dW).a,new T(function(){return B(A2(_8I,B(_8s(B(_8q(_dX)))),_L));})));});return new T2(0,new T(function(){return B(_dR(_dX));}),_dY);},_dZ=function(_e0,_e1){var _e2=B(_dV(_e1));return new T2(0,_e2.a,_e2.b);},_e3=function(_e4,_e5,_e6){var _e7=new T(function(){return E(E(E(_e4).c).a);}),_e8=new T(function(){var _e9=new T(function(){return B(_8s(new T(function(){return B(_8q(_e7));})));}),_ea=new T(function(){return B(A2(_cx,_e7,_e5));});return B(A3(_ac,B(_a4(E(_e4).a)),function(_eb){return new F(function(){return A3(_8u,_e9,_eb,_ea);});},_e6));});return new T2(0,new T(function(){return B(A2(_cz,_e7,_e5));}),_e8);},_ec=function(_ed,_ee,_ef){var _eg=E(_ef),_eh=B(_e3(_ee,_eg.a,_eg.b));return new T2(0,_eh.a,_eh.b);},_ei=function(_ej,_ek,_el){var _em=new T(function(){return E(E(E(_ej).c).a);}),_en=new T(function(){var _eo=new T(function(){return B(_8s(new T(function(){return B(_8q(_em));})));}),_ep=new T(function(){return B(A2(_cQ,_em,_ek));});return B(A3(_ac,B(_a4(E(_ej).a)),function(_eq){return new F(function(){return A3(_8u,_eo,_eq,_ep);});},_el));});return new T2(0,new T(function(){return B(A2(_cS,_em,_ek));}),_en);},_er=function(_es,_et,_eu){var _ev=E(_eu),_ew=B(_ei(_et,_ev.a,_ev.b));return new T2(0,_ew.a,_ew.b);},_ex=new T1(0,2),_ey=function(_ez,_eA,_eB){var _eC=new T(function(){return E(E(E(_ez).c).a);}),_eD=new T(function(){var _eE=new T(function(){return B(_8q(_eC));}),_eF=new T(function(){return B(_8s(_eE));}),_eG=new T(function(){var _eH=new T(function(){return B(A3(_a8,_eE,new T(function(){return B(A2(_8I,_eF,_aH));}),new T(function(){return B(A2(_8I,_eF,_ex));})));});return B(A3(_a8,_eE,_eH,new T(function(){return B(A2(_8K,_eC,_eA));})));});return B(A3(_ac,B(_a4(E(_ez).a)),function(_eI){return new F(function(){return A3(_8u,_eF,_eI,_eG);});},_eB));});return new T2(0,new T(function(){return B(A2(_8K,_eC,_eA));}),_eD);},_eJ=function(_eK,_eL,_eM){var _eN=E(_eM),_eO=B(_ey(_eL,_eN.a,_eN.b));return new T2(0,_eO.a,_eO.b);},_eP=function(_eQ){return E(E(_eQ).j);},_eR=function(_eS,_eT,_eU){var _eV=new T(function(){return E(E(E(_eS).c).a);}),_eW=new T(function(){var _eX=new T(function(){return B(_8q(_eV));}),_eY=new T(function(){var _eZ=new T(function(){return B(A2(_cx,_eV,_eT));});return B(A3(_8u,B(_8s(_eX)),_eZ,_eZ));});return B(A3(_ac,B(_a4(E(_eS).a)),function(_f0){return new F(function(){return A3(_a8,_eX,_f0,_eY);});},_eU));});return new T2(0,new T(function(){return B(A2(_eP,_eV,_eT));}),_eW);},_f1=function(_f2,_f3,_f4){var _f5=E(_f4),_f6=B(_eR(_f3,_f5.a,_f5.b));return new T2(0,_f6.a,_f6.b);},_f7=function(_f8){return E(E(_f8).p);},_f9=function(_fa,_fb,_fc){var _fd=new T(function(){return E(E(E(_fa).c).a);}),_fe=new T(function(){var _ff=new T(function(){return B(_8q(_fd));}),_fg=new T(function(){var _fh=new T(function(){return B(A2(_cQ,_fd,_fb));});return B(A3(_8u,B(_8s(_ff)),_fh,_fh));});return B(A3(_ac,B(_a4(E(_fa).a)),function(_fi){return new F(function(){return A3(_a8,_ff,_fi,_fg);});},_fc));});return new T2(0,new T(function(){return B(A2(_f7,_fd,_fb));}),_fe);},_fj=function(_fk,_fl,_fm){var _fn=E(_fm),_fo=B(_f9(_fl,_fn.a,_fn.b));return new T2(0,_fo.a,_fo.b);},_fp=function(_fq,_fr){return {_:0,a:_fq,b:new T(function(){return B(_dZ(_fq,_fr));}),c:function(_fs){return new F(function(){return _dk(_fq,_fr,_fs);});},d:function(_fs){return new F(function(){return _dA(_fq,_fr,_fs);});},e:function(_fs){return new F(function(){return _eJ(_fq,_fr,_fs);});},f:function(_ft,_fs){return new F(function(){return _az(_fq,_fr,_ft,_fs);});},g:function(_ft,_fs){return new F(function(){return _dG(_fq,_fr,_ft,_fs);});},h:function(_fs){return new F(function(){return _ec(_fq,_fr,_fs);});},i:function(_fs){return new F(function(){return _cK(_fq,_fr,_fs);});},j:function(_fs){return new F(function(){return _f1(_fq,_fr,_fs);});},k:function(_fs){return new F(function(){return _by(_fq,_fr,_fs);});},l:function(_fs){return new F(function(){return _aW(_fq,_fr,_fs);});},m:function(_fs){return new F(function(){return _c9(_fq,_fr,_fs);});},n:function(_fs){return new F(function(){return _er(_fq,_fr,_fs);});},o:function(_fs){return new F(function(){return _d3(_fq,_fr,_fs);});},p:function(_fs){return new F(function(){return _fj(_fq,_fr,_fs);});},q:function(_fs){return new F(function(){return _bR(_fq,_fr,_fs);});},r:function(_fs){return new F(function(){return _bf(_fq,_fr,_fs);});},s:function(_fs){return new F(function(){return _cr(_fq,_fr,_fs);});}};},_fu=function(_fv,_fw,_fx,_fy,_fz){var _fA=new T(function(){return B(_8q(new T(function(){return E(E(E(_fv).c).a);})));}),_fB=new T(function(){var _fC=E(_fv).a,_fD=new T(function(){var _fE=new T(function(){return B(_8s(_fA));}),_fF=new T(function(){return B(A3(_8u,_fE,_fy,_fy));}),_fG=function(_fH,_fI){var _fJ=new T(function(){return B(A3(_8G,_fE,new T(function(){return B(A3(_8u,_fE,_fH,_fy));}),new T(function(){return B(A3(_8u,_fE,_fw,_fI));})));});return new F(function(){return A3(_a8,_fA,_fJ,_fF);});};return B(A3(_ac,B(_a4(_fC)),_fG,_fx));});return B(A3(_aa,_fC,_fD,_fz));});return new T2(0,new T(function(){return B(A3(_a8,_fA,_fw,_fy));}),_fB);},_fK=function(_fL,_fM,_fN,_fO){var _fP=E(_fN),_fQ=E(_fO),_fR=B(_fu(_fM,_fP.a,_fP.b,_fQ.a,_fQ.b));return new T2(0,_fR.a,_fR.b);},_fS=function(_fT){return E(E(_fT).d);},_fU=function(_fV,_fW){var _fX=new T(function(){return B(_8q(new T(function(){return E(E(E(_fV).c).a);})));}),_fY=new T(function(){return B(A2(_dT,E(_fV).a,new T(function(){return B(A2(_8I,B(_8s(_fX)),_L));})));});return new T2(0,new T(function(){return B(A2(_fS,_fX,_fW));}),_fY);},_fZ=function(_g0,_g1,_g2){var _g3=B(_fU(_g1,_g2));return new T2(0,_g3.a,_g3.b);},_g4=function(_g5,_g6,_g7){var _g8=new T(function(){return B(_8q(new T(function(){return E(E(E(_g5).c).a);})));}),_g9=new T(function(){return B(_8s(_g8));}),_ga=new T(function(){var _gb=new T(function(){var _gc=new T(function(){return B(A3(_a8,_g8,new T(function(){return B(A2(_8I,_g9,_aH));}),new T(function(){return B(A3(_8u,_g9,_g6,_g6));})));});return B(A2(_88,_g9,_gc));});return B(A3(_ac,B(_a4(E(_g5).a)),function(_gd){return new F(function(){return A3(_8u,_g9,_gd,_gb);});},_g7));}),_ge=new T(function(){return B(A3(_a8,_g8,new T(function(){return B(A2(_8I,_g9,_aH));}),_g6));});return new T2(0,_ge,_ga);},_gf=function(_gg,_gh,_gi){var _gj=E(_gi),_gk=B(_g4(_gh,_gj.a,_gj.b));return new T2(0,_gk.a,_gk.b);},_gl=function(_gm,_gn){return new T4(0,_gm,function(_ft,_fs){return new F(function(){return _fK(_gm,_gn,_ft,_fs);});},function(_fs){return new F(function(){return _gf(_gm,_gn,_fs);});},function(_fs){return new F(function(){return _fZ(_gm,_gn,_fs);});});},_go=function(_gp,_gq,_gr,_gs,_gt){var _gu=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gp).c).a);})));})));}),_gv=new T(function(){var _gw=E(_gp).a,_gx=new T(function(){var _gy=function(_gz,_gA){return new F(function(){return A3(_86,_gu,new T(function(){return B(A3(_8u,_gu,_gq,_gA));}),new T(function(){return B(A3(_8u,_gu,_gz,_gs));}));});};return B(A3(_ac,B(_a4(_gw)),_gy,_gr));});return B(A3(_aa,_gw,_gx,_gt));});return new T2(0,new T(function(){return B(A3(_8u,_gu,_gq,_gs));}),_gv);},_gB=function(_gC,_gD,_gE){var _gF=E(_gD),_gG=E(_gE),_gH=B(_go(_gC,_gF.a,_gF.b,_gG.a,_gG.b));return new T2(0,_gH.a,_gH.b);},_gI=function(_gJ,_gK,_gL,_gM,_gN){var _gO=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gJ).c).a);})));})));}),_gP=new T(function(){var _gQ=E(_gJ).a,_gR=new T(function(){return B(A3(_ac,B(_a4(_gQ)),new T(function(){return B(_86(_gO));}),_gL));});return B(A3(_aa,_gQ,_gR,_gN));});return new T2(0,new T(function(){return B(A3(_86,_gO,_gK,_gM));}),_gP);},_gS=function(_gT,_gU,_gV){var _gW=E(_gU),_gX=E(_gV),_gY=B(_gI(_gT,_gW.a,_gW.b,_gX.a,_gX.b));return new T2(0,_gY.a,_gY.b);},_gZ=function(_h0,_h1,_h2){var _h3=B(_h4(_h0));return new F(function(){return A3(_86,_h3,_h1,new T(function(){return B(A2(_88,_h3,_h2));}));});},_h5=function(_h6){return E(E(_h6).e);},_h7=function(_h8){return E(E(_h8).f);},_h9=function(_ha,_hb,_hc){var _hd=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_ha).c).a);})));})));}),_he=new T(function(){var _hf=new T(function(){return B(A2(_h7,_hd,_hb));});return B(A3(_ac,B(_a4(E(_ha).a)),function(_hg){return new F(function(){return A3(_8u,_hd,_hg,_hf);});},_hc));});return new T2(0,new T(function(){return B(A2(_h5,_hd,_hb));}),_he);},_hh=function(_hi,_hj){var _hk=E(_hj),_hl=B(_h9(_hi,_hk.a,_hk.b));return new T2(0,_hl.a,_hl.b);},_hm=function(_hn,_ho){var _hp=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hn).c).a);})));})));}),_hq=new T(function(){return B(A2(_dT,E(_hn).a,new T(function(){return B(A2(_8I,_hp,_L));})));});return new T2(0,new T(function(){return B(A2(_8I,_hp,_ho));}),_hq);},_hr=function(_hs,_ht){var _hu=B(_hm(_hs,_ht));return new T2(0,_hu.a,_hu.b);},_hv=function(_hw,_hx,_hy){var _hz=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hw).c).a);})));})));}),_hA=new T(function(){return B(A3(_ac,B(_a4(E(_hw).a)),new T(function(){return B(_88(_hz));}),_hy));});return new T2(0,new T(function(){return B(A2(_88,_hz,_hx));}),_hA);},_hB=function(_hC,_hD){var _hE=E(_hD),_hF=B(_hv(_hC,_hE.a,_hE.b));return new T2(0,_hF.a,_hF.b);},_hG=function(_hH,_hI){var _hJ=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hH).c).a);})));})));}),_hK=new T(function(){return B(A2(_dT,E(_hH).a,new T(function(){return B(A2(_8I,_hJ,_L));})));});return new T2(0,new T(function(){return B(A2(_h7,_hJ,_hI));}),_hK);},_hL=function(_hM,_hN){var _hO=B(_hG(_hM,E(_hN).a));return new T2(0,_hO.a,_hO.b);},_h4=function(_hP){return {_:0,a:function(_ft,_fs){return new F(function(){return _gS(_hP,_ft,_fs);});},b:function(_ft,_fs){return new F(function(){return _gZ(_hP,_ft,_fs);});},c:function(_ft,_fs){return new F(function(){return _gB(_hP,_ft,_fs);});},d:function(_fs){return new F(function(){return _hB(_hP,_fs);});},e:function(_fs){return new F(function(){return _hh(_hP,_fs);});},f:function(_fs){return new F(function(){return _hL(_hP,_fs);});},g:function(_fs){return new F(function(){return _hr(_hP,_fs);});}};},_hQ=function(_hR){var _hS=new T(function(){return E(E(_hR).a);}),_hT=new T3(0,_9Y,_a0,new T2(0,_hS,new T(function(){return E(E(_hR).b);}))),_hU=new T(function(){return B(_fp(new T(function(){return B(_gl(new T(function(){return B(_h4(_hT));}),_hT));}),_hT));}),_hV=new T(function(){return B(_8s(new T(function(){return B(_8q(_hS));})));}),_hW=function(_hX){return E(B(_8M(_hU,new T(function(){var _hY=E(_hX),_hZ=B(A2(_8I,_hV,_1o)),_i0=B(A2(_8I,_hV,_9Z));return new T3(0,E(new T2(0,_hY.a,new T3(0,E(_hZ),E(_i0),E(_i0)))),E(new T2(0,_hY.b,new T3(0,E(_i0),E(_hZ),E(_i0)))),E(new T2(0,_hY.c,new T3(0,E(_i0),E(_i0),E(_hZ)))));}))).b);};return E(_hW);},_i1=new T(function(){return B(_hQ(_9u));}),_i2=function(_i3,_i4){var _i5=E(_i4);return (_i5._==0)?__Z:new T2(1,_i3,new T2(1,_i5.a,new T(function(){return B(_i2(_i3,_i5.b));})));},_i6=new T(function(){var _i7=B(A1(_i1,_91));return new T2(1,_i7.a,new T(function(){return B(_i2(_22,new T2(1,_i7.b,new T2(1,_i7.c,_w))));}));}),_i8=new T1(1,_i6),_i9=new T2(1,_i8,_1S),_ia=new T(function(){return B(unCStr("vec3("));}),_ib=new T1(0,_ia),_ic=new T2(1,_ib,_i9),_id=new T(function(){return toJSStr(B(_1F(_x,_1l,_ic)));}),_ie=function(_if,_ig){while(1){var _ih=E(_if);if(!_ih._){return E(_ig);}else{var _ii=_ig+1|0;_if=_ih.b;_ig=_ii;continue;}}},_ij=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_ik=new T(function(){return B(err(_ij));}),_il=0,_im=new T3(0,E(_il),E(_il),E(_il)),_in=new T2(0,E(_im),E(_il)),_io=new T(function(){return B(unCStr("Negative exponent"));}),_ip=new T(function(){return B(err(_io));}),_iq=function(_ir,_is,_it){while(1){if(!(_is%2)){var _iu=_ir*_ir,_iv=quot(_is,2);_ir=_iu;_is=_iv;continue;}else{var _iw=E(_is);if(_iw==1){return _ir*_it;}else{var _iu=_ir*_ir,_ix=_ir*_it;_ir=_iu;_is=quot(_iw-1|0,2);_it=_ix;continue;}}}},_iy=function(_iz,_iA){while(1){if(!(_iA%2)){var _iB=_iz*_iz,_iC=quot(_iA,2);_iz=_iB;_iA=_iC;continue;}else{var _iD=E(_iA);if(_iD==1){return E(_iz);}else{return new F(function(){return _iq(_iz*_iz,quot(_iD-1|0,2),_iz);});}}}},_iE=function(_iF){var _iG=E(_iF);return new F(function(){return Math.log(_iG+(_iG+1)*Math.sqrt((_iG-1)/(_iG+1)));});},_iH=function(_iI){var _iJ=E(_iI);return new F(function(){return Math.log(_iJ+Math.sqrt(1+_iJ*_iJ));});},_iK=function(_iL){var _iM=E(_iL);return 0.5*Math.log((1+_iM)/(1-_iM));},_iN=function(_iO,_iP){return Math.log(E(_iP))/Math.log(E(_iO));},_iQ=3.141592653589793,_iR=function(_iS){var _iT=E(_iS);return new F(function(){return _7J(_iT.a,_iT.b);});},_iU=function(_iV){return 1/E(_iV);},_iW=function(_iX){var _iY=E(_iX),_iZ=E(_iY);return (_iZ==0)?E(_7I):(_iZ<=0)? -_iZ:E(_iY);},_j0=function(_j1){var _j2=E(_j1);if(!_j2._){return _j2.a;}else{return new F(function(){return I_toNumber(_j2.a);});}},_j3=function(_j4){return new F(function(){return _j0(_j4);});},_j5=1,_j6=-1,_j7=function(_j8){var _j9=E(_j8);return (_j9<=0)?(_j9>=0)?E(_j9):E(_j6):E(_j5);},_ja=function(_jb,_jc){return E(_jb)-E(_jc);},_jd=function(_je){return  -E(_je);},_jf=function(_jg,_jh){return E(_jg)+E(_jh);},_ji=function(_jj,_jk){return E(_jj)*E(_jk);},_jl={_:0,a:_jf,b:_ja,c:_ji,d:_jd,e:_iW,f:_j7,g:_j3},_jm=function(_jn,_jo){return E(_jn)/E(_jo);},_jp=new T4(0,_jl,_jm,_iU,_iR),_jq=function(_jr){return new F(function(){return Math.acos(E(_jr));});},_js=function(_jt){return new F(function(){return Math.asin(E(_jt));});},_ju=function(_jv){return new F(function(){return Math.atan(E(_jv));});},_jw=function(_jx){return new F(function(){return Math.cos(E(_jx));});},_jy=function(_jz){return new F(function(){return cosh(E(_jz));});},_jA=function(_jB){return new F(function(){return Math.exp(E(_jB));});},_jC=function(_jD){return new F(function(){return Math.log(E(_jD));});},_jE=function(_jF,_jG){return new F(function(){return Math.pow(E(_jF),E(_jG));});},_jH=function(_jI){return new F(function(){return Math.sin(E(_jI));});},_jJ=function(_jK){return new F(function(){return sinh(E(_jK));});},_jL=function(_jM){return new F(function(){return Math.sqrt(E(_jM));});},_jN=function(_jO){return new F(function(){return Math.tan(E(_jO));});},_jP=function(_jQ){return new F(function(){return tanh(E(_jQ));});},_jR={_:0,a:_jp,b:_iQ,c:_jA,d:_jC,e:_jL,f:_jE,g:_iN,h:_jH,i:_jw,j:_jN,k:_js,l:_jq,m:_ju,n:_jJ,o:_jy,p:_jP,q:_iH,r:_iE,s:_iK},_jS=function(_jT,_jU){return (E(_jT)!=E(_jU))?true:false;},_jV=function(_jW,_jX){return E(_jW)==E(_jX);},_jY=new T2(0,_jV,_jS),_jZ=function(_k0,_k1){return E(_k0)<E(_k1);},_k2=function(_k3,_k4){return E(_k3)<=E(_k4);},_k5=function(_k6,_k7){return E(_k6)>E(_k7);},_k8=function(_k9,_ka){return E(_k9)>=E(_ka);},_kb=function(_kc,_kd){var _ke=E(_kc),_kf=E(_kd);return (_ke>=_kf)?(_ke!=_kf)?2:1:0;},_kg=function(_kh,_ki){var _kj=E(_kh),_kk=E(_ki);return (_kj>_kk)?E(_kj):E(_kk);},_kl=function(_km,_kn){var _ko=E(_km),_kp=E(_kn);return (_ko>_kp)?E(_kp):E(_ko);},_kq={_:0,a:_jY,b:_kb,c:_jZ,d:_k2,e:_k5,f:_k8,g:_kg,h:_kl},_kr="dz",_ks="wy",_kt="wx",_ku="dy",_kv="dx",_kw="t",_kx="a",_ky="r",_kz="ly",_kA="lx",_kB="wz",_kC=0,_kD=function(_kE){var _kF=__new(),_kG=_kF,_kH=function(_kI,_){while(1){var _kJ=E(_kI);if(!_kJ._){return _kC;}else{var _kK=E(_kJ.a),_kL=__set(_kG,E(_kK.a),E(_kK.b));_kI=_kJ.b;continue;}}},_kM=B(_kH(_kE,_));return E(_kG);},_kN=function(_kO,_kP,_kQ,_kR,_kS,_kT,_kU,_kV,_kW){return new F(function(){return _kD(new T2(1,new T2(0,_kt,_kO),new T2(1,new T2(0,_ks,_kP),new T2(1,new T2(0,_kB,_kQ),new T2(1,new T2(0,_kA,_kR*_kS*Math.cos(_kT)),new T2(1,new T2(0,_kz,_kR*_kS*Math.sin(_kT)),new T2(1,new T2(0,_ky,_kR),new T2(1,new T2(0,_kx,_kS),new T2(1,new T2(0,_kw,_kT),new T2(1,new T2(0,_kv,_kU),new T2(1,new T2(0,_ku,_kV),new T2(1,new T2(0,_kr,_kW),_w))))))))))));});},_kX=function(_kY){var _kZ=E(_kY),_l0=E(_kZ.a),_l1=E(_kZ.b),_l2=E(_kZ.d);return new F(function(){return _kN(_l0.a,_l0.b,_l0.c,E(_l1.a),E(_l1.b),E(_kZ.c),_l2.a,_l2.b,_l2.c);});},_l3=function(_l4,_l5){var _l6=E(_l5);return (_l6._==0)?__Z:new T2(1,new T(function(){return B(A1(_l4,_l6.a));}),new T(function(){return B(_l3(_l4,_l6.b));}));},_l7=function(_l8,_l9,_la){var _lb=__lst2arr(B(_l3(_kX,new T2(1,_l8,new T2(1,_l9,new T2(1,_la,_w))))));return E(_lb);},_lc=function(_ld){var _le=E(_ld);return new F(function(){return _l7(_le.a,_le.b,_le.c);});},_lf=new T2(0,_jR,_kq),_lg=function(_lh,_li,_lj,_lk){var _ll=B(_8q(_lh)),_lm=new T(function(){return B(A2(_8K,_lh,new T(function(){return B(_8w(_lh,_li,_lj,_lk,_li,_lj,_lk));})));});return new T3(0,B(A3(_a8,_ll,_li,_lm)),B(A3(_a8,_ll,_lj,_lm)),B(A3(_a8,_ll,_lk,_lm)));},_ln=function(_lo,_lp,_lq,_lr,_ls,_lt,_lu){var _lv=B(_8u(_lo));return new T3(0,B(A1(B(A1(_lv,_lp)),_ls)),B(A1(B(A1(_lv,_lq)),_lt)),B(A1(B(A1(_lv,_lr)),_lu)));},_lw=function(_lx,_ly,_lz,_lA,_lB,_lC,_lD){var _lE=B(_86(_lx));return new T3(0,B(A1(B(A1(_lE,_ly)),_lB)),B(A1(B(A1(_lE,_lz)),_lC)),B(A1(B(A1(_lE,_lA)),_lD)));},_lF=function(_lG,_lH){var _lI=new T(function(){return E(E(_lG).a);}),_lJ=new T(function(){return B(A2(_hQ,new T2(0,_lI,new T(function(){return E(E(_lG).b);})),_lH));}),_lK=new T(function(){var _lL=E(_lJ),_lM=B(_lg(_lI,_lL.a,_lL.b,_lL.c));return new T3(0,E(_lM.a),E(_lM.b),E(_lM.c));}),_lN=new T(function(){var _lO=E(_lH),_lP=E(_lK),_lQ=B(_8q(_lI)),_lR=new T(function(){return B(A2(_8K,_lI,new T(function(){var _lS=E(_lJ),_lT=_lS.a,_lU=_lS.b,_lV=_lS.c;return B(_8w(_lI,_lT,_lU,_lV,_lT,_lU,_lV));})));}),_lW=B(A3(_a8,_lQ,new T(function(){return B(_8M(_lI,_lO));}),_lR)),_lX=B(_8s(_lQ)),_lY=B(_ln(_lX,_lP.a,_lP.b,_lP.c,_lW,_lW,_lW)),_lZ=B(_88(_lX)),_m0=B(_lw(_lX,_lO.a,_lO.b,_lO.c,B(A1(_lZ,_lY.a)),B(A1(_lZ,_lY.b)),B(A1(_lZ,_lY.c))));return new T3(0,E(_m0.a),E(_m0.b),E(_m0.c));});return new T2(0,_lN,_lK);},_m1=function(_m2){return E(E(_m2).a);},_m3=function(_m4,_m5,_m6,_m7,_m8,_m9,_ma){var _mb=B(_8w(_m4,_m8,_m9,_ma,_m5,_m6,_m7)),_mc=B(_8s(B(_8q(_m4)))),_md=B(_ln(_mc,_m8,_m9,_ma,_mb,_mb,_mb)),_me=B(_88(_mc));return new F(function(){return _lw(_mc,_m5,_m6,_m7,B(A1(_me,_md.a)),B(A1(_me,_md.b)),B(A1(_me,_md.c)));});},_mf=function(_mg){return E(E(_mg).a);},_mh=function(_mi,_mj,_mk,_ml){var _mm=new T(function(){var _mn=E(_ml),_mo=E(_mk),_mp=B(_m3(_mi,_mn.a,_mn.b,_mn.c,_mo.a,_mo.b,_mo.c));return new T3(0,E(_mp.a),E(_mp.b),E(_mp.c));}),_mq=new T(function(){return B(A2(_8K,_mi,new T(function(){var _mr=E(_mm),_ms=_mr.a,_mt=_mr.b,_mu=_mr.c;return B(_8w(_mi,_ms,_mt,_mu,_ms,_mt,_mu));})));});if(!B(A3(_mf,B(_m1(_mj)),_mq,new T(function(){return B(A2(_8I,B(_8s(B(_8q(_mi)))),_9Z));})))){var _mv=E(_mm),_mw=B(_lg(_mi,_mv.a,_mv.b,_mv.c)),_mx=B(A2(_8K,_mi,new T(function(){var _my=E(_ml),_mz=_my.a,_mA=_my.b,_mB=_my.c;return B(_8w(_mi,_mz,_mA,_mB,_mz,_mA,_mB));}))),_mC=B(_8u(new T(function(){return B(_8s(new T(function(){return B(_8q(_mi));})));})));return new T3(0,B(A1(B(A1(_mC,_mw.a)),_mx)),B(A1(B(A1(_mC,_mw.b)),_mx)),B(A1(B(A1(_mC,_mw.c)),_mx)));}else{var _mD=B(A2(_8I,B(_8s(B(_8q(_mi)))),_9Z));return new T3(0,_mD,_mD,_mD);}},_mE=function(_mF,_mG){while(1){var _mH=E(_mF);if(!_mH._){return E(_mG);}else{var _mI=_mH.b,_mJ=E(_mH.a);if(_mG>_mJ){_mF=_mI;continue;}else{_mF=_mI;_mG=_mJ;continue;}}}},_mK=new T(function(){var _mL=eval("angleCount"),_mM=Number(_mL);return jsTrunc(_mM);}),_mN=new T(function(){return E(_mK);}),_mO=new T(function(){return B(unCStr(": empty list"));}),_mP=new T(function(){return B(unCStr("Prelude."));}),_mQ=function(_mR){return new F(function(){return err(B(_n(_mP,new T(function(){return B(_n(_mR,_mO));},1))));});},_mS=new T(function(){return B(unCStr("head"));}),_mT=new T(function(){return B(_mQ(_mS));}),_mU=function(_mV,_mW,_mX){var _mY=E(_mV);if(!_mY._){return __Z;}else{var _mZ=E(_mW);if(!_mZ._){return __Z;}else{var _n0=_mZ.a,_n1=E(_mX);if(!_n1._){return __Z;}else{var _n2=E(_n1.a),_n3=_n2.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_mY.a),E(_n0),E(_n3));}),new T2(1,new T(function(){return new T3(0,E(_n0),E(_n3),E(_n2.b));}),_w)),new T(function(){return B(_mU(_mY.b,_mZ.b,_n1.b));},1));});}}}},_n4=new T(function(){return B(unCStr("tail"));}),_n5=new T(function(){return B(_mQ(_n4));}),_n6=function(_n7,_n8){var _n9=E(_n7);if(!_n9._){return __Z;}else{var _na=E(_n8);return (_na._==0)?__Z:new T2(1,new T2(0,_n9.a,_na.a),new T(function(){return B(_n6(_n9.b,_na.b));}));}},_nb=function(_nc,_nd){var _ne=E(_nc);if(!_ne._){return __Z;}else{var _nf=E(_nd);if(!_nf._){return __Z;}else{var _ng=E(_ne.a),_nh=_ng.b,_ni=E(_nf.a).b,_nj=new T(function(){var _nk=new T(function(){return B(_n6(_ni,new T(function(){var _nl=E(_ni);if(!_nl._){return E(_n5);}else{return E(_nl.b);}},1)));},1);return B(_mU(_nh,new T(function(){var _nm=E(_nh);if(!_nm._){return E(_n5);}else{return E(_nm.b);}},1),_nk));});return new F(function(){return _n(new T2(1,new T(function(){var _nn=E(_nh);if(!_nn._){return E(_mT);}else{var _no=E(_ni);if(!_no._){return E(_mT);}else{return new T3(0,E(_ng.a),E(_nn.a),E(_no.a));}}}),_nj),new T(function(){return B(_nb(_ne.b,_nf.b));},1));});}}},_np=new T(function(){return 6.283185307179586/E(_mN);}),_nq=new T(function(){return E(_mN)-1;}),_nr=new T1(0,1),_ns=function(_nt,_nu){var _nv=E(_nu),_nw=new T(function(){var _nx=B(_8s(_nt)),_ny=B(_ns(_nt,B(A3(_86,_nx,_nv,new T(function(){return B(A2(_8I,_nx,_nr));})))));return new T2(1,_ny.a,_ny.b);});return new T2(0,_nv,_nw);},_nz=function(_nA){return E(E(_nA).d);},_nB=new T1(0,2),_nC=function(_nD,_nE){var _nF=E(_nE);if(!_nF._){return __Z;}else{var _nG=_nF.a;return (!B(A1(_nD,_nG)))?__Z:new T2(1,_nG,new T(function(){return B(_nC(_nD,_nF.b));}));}},_nH=function(_nI,_nJ,_nK,_nL){var _nM=B(_ns(_nJ,_nK)),_nN=new T(function(){var _nO=B(_8s(_nJ)),_nP=new T(function(){return B(A3(_a8,_nJ,new T(function(){return B(A2(_8I,_nO,_nr));}),new T(function(){return B(A2(_8I,_nO,_nB));})));});return B(A3(_86,_nO,_nL,_nP));});return new F(function(){return _nC(function(_nQ){return new F(function(){return A3(_nz,_nI,_nQ,_nN);});},new T2(1,_nM.a,_nM.b));});},_nR=new T(function(){return B(_nH(_kq,_jp,_il,_nq));}),_nS=function(_nT,_nU){while(1){var _nV=E(_nT);if(!_nV._){return E(_nU);}else{_nT=_nV.b;_nU=_nV.a;continue;}}},_nW=new T(function(){return B(unCStr("last"));}),_nX=new T(function(){return B(_mQ(_nW));}),_nY=function(_nZ){return new F(function(){return _nS(_nZ,_nX);});},_o0=function(_o1){return new F(function(){return _nY(E(_o1).b);});},_o2=new T(function(){return B(unCStr("maximum"));}),_o3=new T(function(){return B(_mQ(_o2));}),_o4=new T(function(){var _o5=eval("proceedCount"),_o6=Number(_o5);return jsTrunc(_o6);}),_o7=new T(function(){return E(_o4);}),_o8=1,_o9=new T(function(){return B(_nH(_kq,_jp,_o8,_o7));}),_oa=function(_ob,_oc,_od,_oe,_of,_og,_oh,_oi,_oj,_ok,_ol,_om,_on,_oo){var _op=new T(function(){var _oq=new T(function(){var _or=E(_ok),_os=E(_oo),_ot=E(_on),_ou=E(_ol),_ov=E(_om),_ow=E(_oj);return new T3(0,_or*_os-_ot*_ou,_ou*_ov-_os*_ow,_ow*_ot-_ov*_or);}),_ox=function(_oy){var _oz=new T(function(){var _oA=E(_oy)/E(_mN);return (_oA+_oA)*3.141592653589793;}),_oB=new T(function(){return B(A1(_ob,_oz));}),_oC=new T(function(){var _oD=new T(function(){var _oE=E(_oB)/E(_o7);return new T3(0,E(_oE),E(_oE),E(_oE));}),_oF=function(_oG,_oH){var _oI=E(_oG);if(!_oI._){return new T2(0,_w,_oH);}else{var _oJ=new T(function(){var _oK=B(_lF(_lf,new T(function(){var _oL=E(_oH),_oM=E(_oL.a),_oN=E(_oL.b),_oO=E(_oD);return new T3(0,E(_oM.a)+E(_oN.a)*E(_oO.a),E(_oM.b)+E(_oN.b)*E(_oO.b),E(_oM.c)+E(_oN.c)*E(_oO.c));}))),_oP=_oK.a,_oQ=new T(function(){var _oR=E(_oK.b),_oS=E(E(_oH).b),_oT=B(_m3(_jR,_oS.a,_oS.b,_oS.c,_oR.a,_oR.b,_oR.c)),_oU=B(_lg(_jR,_oT.a,_oT.b,_oT.c));return new T3(0,E(_oU.a),E(_oU.b),E(_oU.c));});return new T2(0,new T(function(){var _oV=E(_oB),_oW=E(_oz);return new T4(0,E(_oP),E(new T2(0,E(_oI.a)/E(_o7),E(_oV))),E(_oW),E(_oQ));}),new T2(0,_oP,_oQ));}),_oX=new T(function(){var _oY=B(_oF(_oI.b,new T(function(){return E(E(_oJ).b);})));return new T2(0,_oY.a,_oY.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oJ).a);}),new T(function(){return E(E(_oX).a);})),new T(function(){return E(E(_oX).b);}));}},_oZ=function(_p0,_p1,_p2,_p3,_p4){var _p5=E(_p0);if(!_p5._){return new T2(0,_w,new T2(0,new T3(0,E(_p1),E(_p2),E(_p3)),_p4));}else{var _p6=new T(function(){var _p7=B(_lF(_lf,new T(function(){var _p8=E(_p4),_p9=E(_oD);return new T3(0,E(_p1)+E(_p8.a)*E(_p9.a),E(_p2)+E(_p8.b)*E(_p9.b),E(_p3)+E(_p8.c)*E(_p9.c));}))),_pa=_p7.a,_pb=new T(function(){var _pc=E(_p7.b),_pd=E(_p4),_pe=B(_m3(_jR,_pd.a,_pd.b,_pd.c,_pc.a,_pc.b,_pc.c)),_pf=B(_lg(_jR,_pe.a,_pe.b,_pe.c));return new T3(0,E(_pf.a),E(_pf.b),E(_pf.c));});return new T2(0,new T(function(){var _pg=E(_oB),_ph=E(_oz);return new T4(0,E(_pa),E(new T2(0,E(_p5.a)/E(_o7),E(_pg))),E(_ph),E(_pb));}),new T2(0,_pa,_pb));}),_pi=new T(function(){var _pj=B(_oF(_p5.b,new T(function(){return E(E(_p6).b);})));return new T2(0,_pj.a,_pj.b);});return new T2(0,new T2(1,new T(function(){return E(E(_p6).a);}),new T(function(){return E(E(_pi).a);})),new T(function(){return E(E(_pi).b);}));}};return E(B(_oZ(_o9,_oe,_of,_og,new T(function(){var _pk=E(_oq),_pl=E(_oz)+_oh,_pm=Math.cos(_pl),_pn=Math.sin(_pl);return new T3(0,E(_oj)*_pm+E(_pk.a)*_pn,E(_ok)*_pm+E(_pk.b)*_pn,E(_ol)*_pm+E(_pk.c)*_pn);}))).a);});return new T2(0,new T(function(){var _po=E(_oB),_pp=E(_oz);return new T4(0,E(new T3(0,E(_oe),E(_of),E(_og))),E(new T2(0,E(_il),E(_po))),E(_pp),E(_im));}),_oC);};return B(_l3(_ox,_nR));}),_pq=new T(function(){var _pr=function(_ps){return new F(function(){return A1(_ob,new T(function(){return B(_ji(_ps,_np));}));});},_pt=B(_l3(_pr,_nR));if(!_pt._){return E(_o3);}else{return B(_mE(_pt.b,E(_pt.a)));}}),_pu=new T(function(){var _pv=new T(function(){var _pw=B(_n(_op,new T2(1,new T(function(){var _px=E(_op);if(!_px._){return E(_mT);}else{return E(_px.a);}}),_w)));if(!_pw._){return E(_n5);}else{return E(_pw.b);}},1);return B(_nb(_op,_pv));});return new T3(0,_pu,new T(function(){return B(_l3(_o0,_op));}),_pq);},_py=function(_pz,_pA,_pB,_pC,_pD,_pE,_pF,_pG,_pH,_pI,_pJ,_pK,_pL,_pM,_pN,_pO,_pP,_pQ){var _pR=B(_lF(_lf,new T3(0,E(_pC),E(_pD),E(_pE)))),_pS=_pR.b,_pT=E(_pR.a),_pU=B(_mh(_jR,_kq,_pS,new T3(0,E(_pG),E(_pH),E(_pI)))),_pV=E(_pS),_pW=_pV.a,_pX=_pV.b,_pY=_pV.c,_pZ=B(_m3(_jR,_pK,_pL,_pM,_pW,_pX,_pY)),_q0=B(_lg(_jR,_pZ.a,_pZ.b,_pZ.c)),_q1=_q0.a,_q2=_q0.b,_q3=_q0.c,_q4=E(_pF),_q5=new T2(0,E(new T3(0,E(_pU.a),E(_pU.b),E(_pU.c))),E(_pJ)),_q6=B(_oa(_pz,_pA,_pB,_pT.a,_pT.b,_pT.c,_q4,_q5,_q1,_q2,_q3,_pW,_pX,_pY)),_q7=__lst2arr(B(_l3(_lc,_q6.a))),_q8=__lst2arr(B(_l3(_kX,_q6.b)));return {_:0,a:_pz,b:_pA,c:_pB,d:new T2(0,E(_pT),E(_q4)),e:_q5,f:new T3(0,E(_q1),E(_q2),E(_q3)),g:_pV,h:_q7,i:_q8,j:E(_q6.c)};},_q9=function(_qa){var _qb=E(_qa);return new T3(0, -E(_qb.a),E(_qb.c), -E(_qb.b));},_qc=function(_){return new F(function(){return __jsNull();});},_qd=function(_qe){var _qf=B(A1(_qe,_));return E(_qf);},_qg=new T(function(){return B(_qd(_qc));}),_qh=function(_qi,_qj,_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu){var _qv=function(_qw){var _qx=E(_np),_qy=2+_qw|0,_qz=_qy-1|0,_qA=(2+_qw)*(1+_qw),_qB=E(_nR);if(!_qB._){return _qx*0;}else{var _qC=_qB.a,_qD=_qB.b,_qE=B(A1(_qi,new T(function(){return 6.283185307179586*E(_qC)/E(_mN);}))),_qF=B(A1(_qi,new T(function(){return 6.283185307179586*(E(_qC)+1)/E(_mN);})));if(_qE!=_qF){if(_qy>=0){var _qG=E(_qy);if(!_qG){var _qH=function(_qI,_qJ){while(1){var _qK=B((function(_qL,_qM){var _qN=E(_qL);if(!_qN._){return E(_qM);}else{var _qO=_qN.a,_qP=_qN.b,_qQ=B(A1(_qi,new T(function(){return 6.283185307179586*E(_qO)/E(_mN);}))),_qR=B(A1(_qi,new T(function(){return 6.283185307179586*(E(_qO)+1)/E(_mN);})));if(_qQ!=_qR){var _qS=_qM+0/(_qQ-_qR)/_qA;_qI=_qP;_qJ=_qS;return __continue;}else{if(_qz>=0){var _qT=E(_qz);if(!_qT){var _qS=_qM+_qy/_qA;_qI=_qP;_qJ=_qS;return __continue;}else{var _qS=_qM+_qy*B(_iy(_qQ,_qT))/_qA;_qI=_qP;_qJ=_qS;return __continue;}}else{return E(_ip);}}}})(_qI,_qJ));if(_qK!=__continue){return _qK;}}};return _qx*B(_qH(_qD,0/(_qE-_qF)/_qA));}else{var _qU=function(_qV,_qW){while(1){var _qX=B((function(_qY,_qZ){var _r0=E(_qY);if(!_r0._){return E(_qZ);}else{var _r1=_r0.a,_r2=_r0.b,_r3=B(A1(_qi,new T(function(){return 6.283185307179586*E(_r1)/E(_mN);}))),_r4=B(A1(_qi,new T(function(){return 6.283185307179586*(E(_r1)+1)/E(_mN);})));if(_r3!=_r4){if(_qG>=0){var _r5=_qZ+(B(_iy(_r3,_qG))-B(_iy(_r4,_qG)))/(_r3-_r4)/_qA;_qV=_r2;_qW=_r5;return __continue;}else{return E(_ip);}}else{if(_qz>=0){var _r6=E(_qz);if(!_r6){var _r5=_qZ+_qy/_qA;_qV=_r2;_qW=_r5;return __continue;}else{var _r5=_qZ+_qy*B(_iy(_r3,_r6))/_qA;_qV=_r2;_qW=_r5;return __continue;}}else{return E(_ip);}}}})(_qV,_qW));if(_qX!=__continue){return _qX;}}};return _qx*B(_qU(_qD,(B(_iy(_qE,_qG))-B(_iy(_qF,_qG)))/(_qE-_qF)/_qA));}}else{return E(_ip);}}else{if(_qz>=0){var _r7=E(_qz);if(!_r7){var _r8=function(_r9,_ra){while(1){var _rb=B((function(_rc,_rd){var _re=E(_rc);if(!_re._){return E(_rd);}else{var _rf=_re.a,_rg=_re.b,_rh=B(A1(_qi,new T(function(){return 6.283185307179586*E(_rf)/E(_mN);}))),_ri=B(A1(_qi,new T(function(){return 6.283185307179586*(E(_rf)+1)/E(_mN);})));if(_rh!=_ri){if(_qy>=0){var _rj=E(_qy);if(!_rj){var _rk=_rd+0/(_rh-_ri)/_qA;_r9=_rg;_ra=_rk;return __continue;}else{var _rk=_rd+(B(_iy(_rh,_rj))-B(_iy(_ri,_rj)))/(_rh-_ri)/_qA;_r9=_rg;_ra=_rk;return __continue;}}else{return E(_ip);}}else{var _rk=_rd+_qy/_qA;_r9=_rg;_ra=_rk;return __continue;}}})(_r9,_ra));if(_rb!=__continue){return _rb;}}};return _qx*B(_r8(_qD,_qy/_qA));}else{var _rl=function(_rm,_rn){while(1){var _ro=B((function(_rp,_rq){var _rr=E(_rp);if(!_rr._){return E(_rq);}else{var _rs=_rr.a,_rt=_rr.b,_ru=B(A1(_qi,new T(function(){return 6.283185307179586*E(_rs)/E(_mN);}))),_rv=B(A1(_qi,new T(function(){return 6.283185307179586*(E(_rs)+1)/E(_mN);})));if(_ru!=_rv){if(_qy>=0){var _rw=E(_qy);if(!_rw){var _rx=_rq+0/(_ru-_rv)/_qA;_rm=_rt;_rn=_rx;return __continue;}else{var _rx=_rq+(B(_iy(_ru,_rw))-B(_iy(_rv,_rw)))/(_ru-_rv)/_qA;_rm=_rt;_rn=_rx;return __continue;}}else{return E(_ip);}}else{if(_r7>=0){var _rx=_rq+_qy*B(_iy(_ru,_r7))/_qA;_rm=_rt;_rn=_rx;return __continue;}else{return E(_ip);}}}})(_rm,_rn));if(_ro!=__continue){return _ro;}}};return _qx*B(_rl(_qD,_qy*B(_iy(_qE,_r7))/_qA));}}else{return E(_ip);}}}},_ry=E(_qg),_rz=1/(B(_qv(1))*_qj);return new F(function(){return _py(_qi,_q9,new T2(0,E(new T3(0,E(_rz),E(_rz),E(_rz))),1/(B(_qv(3))*_qj)),_qk,_ql,_qm,_qn,_qo,_qp,_qq,_qr,_qs,_qt,_qu,_im,_ry,_ry,0);});},_rA=1,_rB=0,_rC=function(_rD){return E(_im);},_rE=function(_rF){var _rG=I_decodeDouble(_rF);return new T2(0,new T1(1,_rG.b),_rG.a);},_rH=function(_rI){return new T1(0,_rI);},_rJ=function(_rK){var _rL=hs_intToInt64(2147483647),_rM=hs_leInt64(_rK,_rL);if(!_rM){return new T1(1,I_fromInt64(_rK));}else{var _rN=hs_intToInt64(-2147483648),_rO=hs_geInt64(_rK,_rN);if(!_rO){return new T1(1,I_fromInt64(_rK));}else{var _rP=hs_int64ToInt(_rK);return new F(function(){return _rH(_rP);});}}},_rQ=new T(function(){var _rR=newByteArr(256),_rS=_rR,_=_rS["v"]["i8"][0]=8,_rT=function(_rU,_rV,_rW,_){while(1){if(_rW>=256){if(_rU>=256){return E(_);}else{var _rX=imul(2,_rU)|0,_rY=_rV+1|0,_rZ=_rU;_rU=_rX;_rV=_rY;_rW=_rZ;continue;}}else{var _=_rS["v"]["i8"][_rW]=_rV,_rZ=_rW+_rU|0;_rW=_rZ;continue;}}},_=B(_rT(2,0,1,_));return _rS;}),_s0=function(_s1,_s2){var _s3=hs_int64ToInt(_s1),_s4=E(_rQ),_s5=_s4["v"]["i8"][(255&_s3>>>0)>>>0&4294967295];if(_s2>_s5){if(_s5>=8){var _s6=hs_uncheckedIShiftRA64(_s1,8),_s7=function(_s8,_s9){while(1){var _sa=B((function(_sb,_sc){var _sd=hs_int64ToInt(_sb),_se=_s4["v"]["i8"][(255&_sd>>>0)>>>0&4294967295];if(_sc>_se){if(_se>=8){var _sf=hs_uncheckedIShiftRA64(_sb,8),_sg=_sc-8|0;_s8=_sf;_s9=_sg;return __continue;}else{return new T2(0,new T(function(){var _sh=hs_uncheckedIShiftRA64(_sb,_se);return B(_rJ(_sh));}),_sc-_se|0);}}else{return new T2(0,new T(function(){var _si=hs_uncheckedIShiftRA64(_sb,_sc);return B(_rJ(_si));}),0);}})(_s8,_s9));if(_sa!=__continue){return _sa;}}};return new F(function(){return _s7(_s6,_s2-8|0);});}else{return new T2(0,new T(function(){var _sj=hs_uncheckedIShiftRA64(_s1,_s5);return B(_rJ(_sj));}),_s2-_s5|0);}}else{return new T2(0,new T(function(){var _sk=hs_uncheckedIShiftRA64(_s1,_s2);return B(_rJ(_sk));}),0);}},_sl=function(_sm){var _sn=hs_intToInt64(_sm);return E(_sn);},_so=function(_sp){var _sq=E(_sp);if(!_sq._){return new F(function(){return _sl(_sq.a);});}else{return new F(function(){return I_toInt64(_sq.a);});}},_sr=function(_ss){return I_toInt(_ss)>>>0;},_st=function(_su){var _sv=E(_su);if(!_sv._){return _sv.a>>>0;}else{return new F(function(){return _sr(_sv.a);});}},_sw=function(_sx){var _sy=B(_rE(_sx)),_sz=_sy.a,_sA=_sy.b;if(_sA<0){var _sB=function(_sC){if(!_sC){return new T2(0,E(_sz),B(_52(_3k, -_sA)));}else{var _sD=B(_s0(B(_so(_sz)), -_sA));return new T2(0,E(_sD.a),B(_52(_3k,_sD.b)));}};if(!((B(_st(_sz))&1)>>>0)){return new F(function(){return _sB(1);});}else{return new F(function(){return _sB(0);});}}else{return new T2(0,B(_52(_sz,_sA)),_3k);}},_sE=function(_sF){var _sG=B(_sw(E(_sF)));return new T2(0,E(_sG.a),E(_sG.b));},_sH=new T3(0,_jl,_kq,_sE),_sI=function(_sJ){return E(E(_sJ).a);},_sK=function(_sL){return E(E(_sL).a);},_sM=function(_sN,_sO){if(_sN<=_sO){var _sP=function(_sQ){return new T2(1,_sQ,new T(function(){if(_sQ!=_sO){return B(_sP(_sQ+1|0));}else{return __Z;}}));};return new F(function(){return _sP(_sN);});}else{return __Z;}},_sR=function(_sS){return new F(function(){return _sM(E(_sS),2147483647);});},_sT=function(_sU,_sV,_sW){if(_sW<=_sV){var _sX=new T(function(){var _sY=_sV-_sU|0,_sZ=function(_t0){return (_t0>=(_sW-_sY|0))?new T2(1,_t0,new T(function(){return B(_sZ(_t0+_sY|0));})):new T2(1,_t0,_w);};return B(_sZ(_sV));});return new T2(1,_sU,_sX);}else{return (_sW<=_sU)?new T2(1,_sU,_w):__Z;}},_t1=function(_t2,_t3,_t4){if(_t4>=_t3){var _t5=new T(function(){var _t6=_t3-_t2|0,_t7=function(_t8){return (_t8<=(_t4-_t6|0))?new T2(1,_t8,new T(function(){return B(_t7(_t8+_t6|0));})):new T2(1,_t8,_w);};return B(_t7(_t3));});return new T2(1,_t2,_t5);}else{return (_t4>=_t2)?new T2(1,_t2,_w):__Z;}},_t9=function(_ta,_tb){if(_tb<_ta){return new F(function(){return _sT(_ta,_tb,-2147483648);});}else{return new F(function(){return _t1(_ta,_tb,2147483647);});}},_tc=function(_td,_te){return new F(function(){return _t9(E(_td),E(_te));});},_tf=function(_tg,_th,_ti){if(_th<_tg){return new F(function(){return _sT(_tg,_th,_ti);});}else{return new F(function(){return _t1(_tg,_th,_ti);});}},_tj=function(_tk,_tl,_tm){return new F(function(){return _tf(E(_tk),E(_tl),E(_tm));});},_tn=function(_to,_tp){return new F(function(){return _sM(E(_to),E(_tp));});},_tq=function(_tr){return E(_tr);},_ts=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_tt=new T(function(){return B(err(_ts));}),_tu=function(_tv){var _tw=E(_tv);return (_tw==(-2147483648))?E(_tt):_tw-1|0;},_tx=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_ty=new T(function(){return B(err(_tx));}),_tz=function(_tA){var _tB=E(_tA);return (_tB==2147483647)?E(_ty):_tB+1|0;},_tC={_:0,a:_tz,b:_tu,c:_tq,d:_tq,e:_sR,f:_tc,g:_tn,h:_tj},_tD=function(_tE,_tF){if(_tE<=0){if(_tE>=0){return new F(function(){return quot(_tE,_tF);});}else{if(_tF<=0){return new F(function(){return quot(_tE,_tF);});}else{return quot(_tE+1|0,_tF)-1|0;}}}else{if(_tF>=0){if(_tE>=0){return new F(function(){return quot(_tE,_tF);});}else{if(_tF<=0){return new F(function(){return quot(_tE,_tF);});}else{return quot(_tE+1|0,_tF)-1|0;}}}else{return quot(_tE-1|0,_tF)-1|0;}}},_tG=0,_tH=new T(function(){return B(_4p(_tG));}),_tI=new T(function(){return die(_tH);}),_tJ=function(_tK,_tL){var _tM=E(_tL);switch(_tM){case -1:var _tN=E(_tK);if(_tN==(-2147483648)){return E(_tI);}else{return new F(function(){return _tD(_tN,-1);});}break;case 0:return E(_4t);default:return new F(function(){return _tD(_tK,_tM);});}},_tO=function(_tP,_tQ){return new F(function(){return _tJ(E(_tP),E(_tQ));});},_tR=0,_tS=new T2(0,_tI,_tR),_tT=function(_tU,_tV){var _tW=E(_tU),_tX=E(_tV);switch(_tX){case -1:var _tY=E(_tW);if(_tY==(-2147483648)){return E(_tS);}else{if(_tY<=0){if(_tY>=0){var _tZ=quotRemI(_tY,-1);return new T2(0,_tZ.a,_tZ.b);}else{var _u0=quotRemI(_tY,-1);return new T2(0,_u0.a,_u0.b);}}else{var _u1=quotRemI(_tY-1|0,-1);return new T2(0,_u1.a-1|0,(_u1.b+(-1)|0)+1|0);}}break;case 0:return E(_4t);default:if(_tW<=0){if(_tW>=0){var _u2=quotRemI(_tW,_tX);return new T2(0,_u2.a,_u2.b);}else{if(_tX<=0){var _u3=quotRemI(_tW,_tX);return new T2(0,_u3.a,_u3.b);}else{var _u4=quotRemI(_tW+1|0,_tX);return new T2(0,_u4.a-1|0,(_u4.b+_tX|0)-1|0);}}}else{if(_tX>=0){if(_tW>=0){var _u5=quotRemI(_tW,_tX);return new T2(0,_u5.a,_u5.b);}else{if(_tX<=0){var _u6=quotRemI(_tW,_tX);return new T2(0,_u6.a,_u6.b);}else{var _u7=quotRemI(_tW+1|0,_tX);return new T2(0,_u7.a-1|0,(_u7.b+_tX|0)-1|0);}}}else{var _u8=quotRemI(_tW-1|0,_tX);return new T2(0,_u8.a-1|0,(_u8.b+_tX|0)+1|0);}}}},_u9=function(_ua,_ub){var _uc=_ua%_ub;if(_ua<=0){if(_ua>=0){return E(_uc);}else{if(_ub<=0){return E(_uc);}else{var _ud=E(_uc);return (_ud==0)?0:_ud+_ub|0;}}}else{if(_ub>=0){if(_ua>=0){return E(_uc);}else{if(_ub<=0){return E(_uc);}else{var _ue=E(_uc);return (_ue==0)?0:_ue+_ub|0;}}}else{var _uf=E(_uc);return (_uf==0)?0:_uf+_ub|0;}}},_ug=function(_uh,_ui){var _uj=E(_ui);switch(_uj){case -1:return E(_tR);case 0:return E(_4t);default:return new F(function(){return _u9(E(_uh),_uj);});}},_uk=function(_ul,_um){var _un=E(_ul),_uo=E(_um);switch(_uo){case -1:var _up=E(_un);if(_up==(-2147483648)){return E(_tI);}else{return new F(function(){return quot(_up,-1);});}break;case 0:return E(_4t);default:return new F(function(){return quot(_un,_uo);});}},_uq=function(_ur,_us){var _ut=E(_ur),_uu=E(_us);switch(_uu){case -1:var _uv=E(_ut);if(_uv==(-2147483648)){return E(_tS);}else{var _uw=quotRemI(_uv,-1);return new T2(0,_uw.a,_uw.b);}break;case 0:return E(_4t);default:var _ux=quotRemI(_ut,_uu);return new T2(0,_ux.a,_ux.b);}},_uy=function(_uz,_uA){var _uB=E(_uA);switch(_uB){case -1:return E(_tR);case 0:return E(_4t);default:return E(_uz)%_uB;}},_uC=function(_uD){return new F(function(){return _rH(E(_uD));});},_uE=function(_uF){return new T2(0,E(B(_rH(E(_uF)))),E(_nr));},_uG=function(_uH,_uI){return imul(E(_uH),E(_uI))|0;},_uJ=function(_uK,_uL){return E(_uK)+E(_uL)|0;},_uM=function(_uN,_uO){return E(_uN)-E(_uO)|0;},_uP=function(_uQ){var _uR=E(_uQ);return (_uR<0)? -_uR:E(_uR);},_uS=function(_uT){return new F(function(){return _4G(_uT);});},_uU=function(_uV){return  -E(_uV);},_uW=-1,_uX=0,_uY=1,_uZ=function(_v0){var _v1=E(_v0);return (_v1>=0)?(E(_v1)==0)?E(_uX):E(_uY):E(_uW);},_v2={_:0,a:_uJ,b:_uM,c:_uG,d:_uU,e:_uP,f:_uZ,g:_uS},_v3=function(_v4,_v5){return E(_v4)==E(_v5);},_v6=function(_v7,_v8){return E(_v7)!=E(_v8);},_v9=new T2(0,_v3,_v6),_va=function(_vb,_vc){var _vd=E(_vb),_ve=E(_vc);return (_vd>_ve)?E(_vd):E(_ve);},_vf=function(_vg,_vh){var _vi=E(_vg),_vj=E(_vh);return (_vi>_vj)?E(_vj):E(_vi);},_vk=function(_vl,_vm){return (_vl>=_vm)?(_vl!=_vm)?2:1:0;},_vn=function(_vo,_vp){return new F(function(){return _vk(E(_vo),E(_vp));});},_vq=function(_vr,_vs){return E(_vr)>=E(_vs);},_vt=function(_vu,_vv){return E(_vu)>E(_vv);},_vw=function(_vx,_vy){return E(_vx)<=E(_vy);},_vz=function(_vA,_vB){return E(_vA)<E(_vB);},_vC={_:0,a:_v9,b:_vn,c:_vz,d:_vw,e:_vt,f:_vq,g:_va,h:_vf},_vD=new T3(0,_v2,_vC,_uE),_vE={_:0,a:_vD,b:_tC,c:_uk,d:_uy,e:_tO,f:_ug,g:_uq,h:_tT,i:_uC},_vF=new T1(0,2),_vG=function(_vH,_vI){while(1){var _vJ=E(_vH);if(!_vJ._){var _vK=_vJ.a,_vL=E(_vI);if(!_vL._){var _vM=_vL.a;if(!(imul(_vK,_vM)|0)){return new T1(0,imul(_vK,_vM)|0);}else{_vH=new T1(1,I_fromInt(_vK));_vI=new T1(1,I_fromInt(_vM));continue;}}else{_vH=new T1(1,I_fromInt(_vK));_vI=_vL;continue;}}else{var _vN=E(_vI);if(!_vN._){_vH=_vJ;_vI=new T1(1,I_fromInt(_vN.a));continue;}else{return new T1(1,I_mul(_vJ.a,_vN.a));}}}},_vO=function(_vP,_vQ,_vR){while(1){if(!(_vQ%2)){var _vS=B(_vG(_vP,_vP)),_vT=quot(_vQ,2);_vP=_vS;_vQ=_vT;continue;}else{var _vU=E(_vQ);if(_vU==1){return new F(function(){return _vG(_vP,_vR);});}else{var _vS=B(_vG(_vP,_vP)),_vV=B(_vG(_vP,_vR));_vP=_vS;_vQ=quot(_vU-1|0,2);_vR=_vV;continue;}}}},_vW=function(_vX,_vY){while(1){if(!(_vY%2)){var _vZ=B(_vG(_vX,_vX)),_w0=quot(_vY,2);_vX=_vZ;_vY=_w0;continue;}else{var _w1=E(_vY);if(_w1==1){return E(_vX);}else{return new F(function(){return _vO(B(_vG(_vX,_vX)),quot(_w1-1|0,2),_vX);});}}}},_w2=function(_w3){return E(E(_w3).b);},_w4=function(_w5){return E(E(_w5).c);},_w6=new T1(0,0),_w7=function(_w8){return E(E(_w8).d);},_w9=function(_wa,_wb){var _wc=B(_sI(_wa)),_wd=new T(function(){return B(_sK(_wc));}),_we=new T(function(){return B(A3(_w7,_wa,_wb,new T(function(){return B(A2(_8I,_wd,_nB));})));});return new F(function(){return A3(_mf,B(_m1(B(_w2(_wc)))),_we,new T(function(){return B(A2(_8I,_wd,_w6));}));});},_wf=new T(function(){return B(unCStr("Negative exponent"));}),_wg=new T(function(){return B(err(_wf));}),_wh=function(_wi){return E(E(_wi).c);},_wj=function(_wk,_wl,_wm,_wn){var _wo=B(_sI(_wl)),_wp=new T(function(){return B(_sK(_wo));}),_wq=B(_w2(_wo));if(!B(A3(_w4,_wq,_wn,new T(function(){return B(A2(_8I,_wp,_w6));})))){if(!B(A3(_mf,B(_m1(_wq)),_wn,new T(function(){return B(A2(_8I,_wp,_w6));})))){var _wr=new T(function(){return B(A2(_8I,_wp,_nB));}),_ws=new T(function(){return B(A2(_8I,_wp,_nr));}),_wt=B(_m1(_wq)),_wu=function(_wv,_ww,_wx){while(1){var _wy=B((function(_wz,_wA,_wB){if(!B(_w9(_wl,_wA))){if(!B(A3(_mf,_wt,_wA,_ws))){var _wC=new T(function(){return B(A3(_wh,_wl,new T(function(){return B(A3(_8G,_wp,_wA,_ws));}),_wr));});_wv=new T(function(){return B(A3(_8u,_wk,_wz,_wz));});_ww=_wC;_wx=new T(function(){return B(A3(_8u,_wk,_wz,_wB));});return __continue;}else{return new F(function(){return A3(_8u,_wk,_wz,_wB);});}}else{var _wD=_wB;_wv=new T(function(){return B(A3(_8u,_wk,_wz,_wz));});_ww=new T(function(){return B(A3(_wh,_wl,_wA,_wr));});_wx=_wD;return __continue;}})(_wv,_ww,_wx));if(_wy!=__continue){return _wy;}}},_wE=function(_wF,_wG){while(1){var _wH=B((function(_wI,_wJ){if(!B(_w9(_wl,_wJ))){if(!B(A3(_mf,_wt,_wJ,_ws))){var _wK=new T(function(){return B(A3(_wh,_wl,new T(function(){return B(A3(_8G,_wp,_wJ,_ws));}),_wr));});return new F(function(){return _wu(new T(function(){return B(A3(_8u,_wk,_wI,_wI));}),_wK,_wI);});}else{return E(_wI);}}else{_wF=new T(function(){return B(A3(_8u,_wk,_wI,_wI));});_wG=new T(function(){return B(A3(_wh,_wl,_wJ,_wr));});return __continue;}})(_wF,_wG));if(_wH!=__continue){return _wH;}}};return new F(function(){return _wE(_wm,_wn);});}else{return new F(function(){return A2(_8I,_wk,_nr);});}}else{return E(_wg);}},_wL=new T(function(){return B(err(_wf));}),_wM=function(_wN,_wO){var _wP=B(_rE(_wO)),_wQ=_wP.a,_wR=_wP.b,_wS=new T(function(){return B(_sK(new T(function(){return B(_sI(_wN));})));});if(_wR<0){var _wT= -_wR;if(_wT>=0){var _wU=E(_wT);if(!_wU){var _wV=E(_nr);}else{var _wV=B(_vW(_vF,_wU));}if(!B(_4y(_wV,_51))){var _wW=B(_4S(_wQ,_wV));return new T2(0,new T(function(){return B(A2(_8I,_wS,_wW.a));}),new T(function(){return B(_4u(_wW.b,_wR));}));}else{return E(_4t);}}else{return E(_wL);}}else{var _wX=new T(function(){var _wY=new T(function(){return B(_wj(_wS,_vE,new T(function(){return B(A2(_8I,_wS,_vF));}),_wR));});return B(A3(_8u,_wS,new T(function(){return B(A2(_8I,_wS,_wQ));}),_wY));});return new T2(0,_wX,_7I);}},_wZ=function(_x0,_x1){var _x2=B(_wM(_x0,E(_x1))),_x3=_x2.a;if(E(_x2.b)<=0){return E(_x3);}else{var _x4=B(_sK(B(_sI(_x0))));return new F(function(){return A3(_86,_x4,_x3,new T(function(){return B(A2(_8I,_x4,_3k));}));});}},_x5=function(_x6,_x7){var _x8=B(_wM(_x6,E(_x7))),_x9=_x8.a;if(E(_x8.b)>=0){return E(_x9);}else{var _xa=B(_sK(B(_sI(_x6))));return new F(function(){return A3(_8G,_xa,_x9,new T(function(){return B(A2(_8I,_xa,_3k));}));});}},_xb=function(_xc,_xd){var _xe=B(_wM(_xc,E(_xd)));return new T2(0,_xe.a,_xe.b);},_xf=function(_xg,_xh){var _xi=B(_wM(_xg,_xh)),_xj=_xi.a,_xk=E(_xi.b),_xl=new T(function(){var _xm=B(_sK(B(_sI(_xg))));if(_xk>=0){return B(A3(_86,_xm,_xj,new T(function(){return B(A2(_8I,_xm,_3k));})));}else{return B(A3(_8G,_xm,_xj,new T(function(){return B(A2(_8I,_xm,_3k));})));}}),_xn=function(_xo){var _xp=_xo-0.5;return (_xp>=0)?(E(_xp)==0)?(!B(_w9(_xg,_xj)))?E(_xl):E(_xj):E(_xl):E(_xj);},_xq=E(_xk);if(!_xq){return new F(function(){return _xn(0);});}else{if(_xq<=0){var _xr= -_xq-0.5;return (_xr>=0)?(E(_xr)==0)?(!B(_w9(_xg,_xj)))?E(_xl):E(_xj):E(_xl):E(_xj);}else{return new F(function(){return _xn(_xq);});}}},_xs=function(_xt,_xu){return new F(function(){return _xf(_xt,E(_xu));});},_xv=function(_xw,_xx){return E(B(_wM(_xw,E(_xx))).a);},_xy={_:0,a:_sH,b:_jp,c:_xb,d:_xv,e:_xs,f:_wZ,g:_x5},_xz=new T1(0,1),_xA=function(_xB,_xC){var _xD=E(_xB);return new T2(0,_xD,new T(function(){var _xE=B(_xA(B(_4J(_xD,_xC)),_xC));return new T2(1,_xE.a,_xE.b);}));},_xF=function(_xG){var _xH=B(_xA(_xG,_xz));return new T2(1,_xH.a,_xH.b);},_xI=function(_xJ,_xK){var _xL=B(_xA(_xJ,new T(function(){return B(_6W(_xK,_xJ));})));return new T2(1,_xL.a,_xL.b);},_xM=new T1(0,0),_xN=function(_xO,_xP){var _xQ=E(_xO);if(!_xQ._){var _xR=_xQ.a,_xS=E(_xP);return (_xS._==0)?_xR>=_xS.a:I_compareInt(_xS.a,_xR)<=0;}else{var _xT=_xQ.a,_xU=E(_xP);return (_xU._==0)?I_compareInt(_xT,_xU.a)>=0:I_compare(_xT,_xU.a)>=0;}},_xV=function(_xW,_xX,_xY){if(!B(_xN(_xX,_xM))){var _xZ=function(_y0){return (!B(_S(_y0,_xY)))?new T2(1,_y0,new T(function(){return B(_xZ(B(_4J(_y0,_xX))));})):__Z;};return new F(function(){return _xZ(_xW);});}else{var _y1=function(_y2){return (!B(_5c(_y2,_xY)))?new T2(1,_y2,new T(function(){return B(_y1(B(_4J(_y2,_xX))));})):__Z;};return new F(function(){return _y1(_xW);});}},_y3=function(_y4,_y5,_y6){return new F(function(){return _xV(_y4,B(_6W(_y5,_y4)),_y6);});},_y7=function(_y8,_y9){return new F(function(){return _xV(_y8,_xz,_y9);});},_ya=function(_yb){return new F(function(){return _4G(_yb);});},_yc=function(_yd){return new F(function(){return _6W(_yd,_xz);});},_ye=function(_yf){return new F(function(){return _4J(_yf,_xz);});},_yg=function(_yh){return new F(function(){return _rH(E(_yh));});},_yi={_:0,a:_ye,b:_yc,c:_yg,d:_ya,e:_xF,f:_xI,g:_y7,h:_y3},_yj=function(_yk,_yl){while(1){var _ym=E(_yk);if(!_ym._){var _yn=E(_ym.a);if(_yn==(-2147483648)){_yk=new T1(1,I_fromInt(-2147483648));continue;}else{var _yo=E(_yl);if(!_yo._){return new T1(0,B(_tD(_yn,_yo.a)));}else{_yk=new T1(1,I_fromInt(_yn));_yl=_yo;continue;}}}else{var _yp=_ym.a,_yq=E(_yl);return (_yq._==0)?new T1(1,I_div(_yp,I_fromInt(_yq.a))):new T1(1,I_div(_yp,_yq.a));}}},_yr=function(_ys,_yt){if(!B(_4y(_yt,_w6))){return new F(function(){return _yj(_ys,_yt);});}else{return E(_4t);}},_yu=function(_yv,_yw){while(1){var _yx=E(_yv);if(!_yx._){var _yy=E(_yx.a);if(_yy==(-2147483648)){_yv=new T1(1,I_fromInt(-2147483648));continue;}else{var _yz=E(_yw);if(!_yz._){var _yA=_yz.a;return new T2(0,new T1(0,B(_tD(_yy,_yA))),new T1(0,B(_u9(_yy,_yA))));}else{_yv=new T1(1,I_fromInt(_yy));_yw=_yz;continue;}}}else{var _yB=E(_yw);if(!_yB._){_yv=_yx;_yw=new T1(1,I_fromInt(_yB.a));continue;}else{var _yC=I_divMod(_yx.a,_yB.a);return new T2(0,new T1(1,_yC.a),new T1(1,_yC.b));}}}},_yD=function(_yE,_yF){if(!B(_4y(_yF,_w6))){var _yG=B(_yu(_yE,_yF));return new T2(0,_yG.a,_yG.b);}else{return E(_4t);}},_yH=function(_yI,_yJ){while(1){var _yK=E(_yI);if(!_yK._){var _yL=E(_yK.a);if(_yL==(-2147483648)){_yI=new T1(1,I_fromInt(-2147483648));continue;}else{var _yM=E(_yJ);if(!_yM._){return new T1(0,B(_u9(_yL,_yM.a)));}else{_yI=new T1(1,I_fromInt(_yL));_yJ=_yM;continue;}}}else{var _yN=_yK.a,_yO=E(_yJ);return (_yO._==0)?new T1(1,I_mod(_yN,I_fromInt(_yO.a))):new T1(1,I_mod(_yN,_yO.a));}}},_yP=function(_yQ,_yR){if(!B(_4y(_yR,_w6))){return new F(function(){return _yH(_yQ,_yR);});}else{return E(_4t);}},_yS=function(_yT,_yU){while(1){var _yV=E(_yT);if(!_yV._){var _yW=E(_yV.a);if(_yW==(-2147483648)){_yT=new T1(1,I_fromInt(-2147483648));continue;}else{var _yX=E(_yU);if(!_yX._){return new T1(0,quot(_yW,_yX.a));}else{_yT=new T1(1,I_fromInt(_yW));_yU=_yX;continue;}}}else{var _yY=_yV.a,_yZ=E(_yU);return (_yZ._==0)?new T1(0,I_toInt(I_quot(_yY,I_fromInt(_yZ.a)))):new T1(1,I_quot(_yY,_yZ.a));}}},_z0=function(_z1,_z2){if(!B(_4y(_z2,_w6))){return new F(function(){return _yS(_z1,_z2);});}else{return E(_4t);}},_z3=function(_z4,_z5){if(!B(_4y(_z5,_w6))){var _z6=B(_4S(_z4,_z5));return new T2(0,_z6.a,_z6.b);}else{return E(_4t);}},_z7=function(_z8,_z9){while(1){var _za=E(_z8);if(!_za._){var _zb=E(_za.a);if(_zb==(-2147483648)){_z8=new T1(1,I_fromInt(-2147483648));continue;}else{var _zc=E(_z9);if(!_zc._){return new T1(0,_zb%_zc.a);}else{_z8=new T1(1,I_fromInt(_zb));_z9=_zc;continue;}}}else{var _zd=_za.a,_ze=E(_z9);return (_ze._==0)?new T1(1,I_rem(_zd,I_fromInt(_ze.a))):new T1(1,I_rem(_zd,_ze.a));}}},_zf=function(_zg,_zh){if(!B(_4y(_zh,_w6))){return new F(function(){return _z7(_zg,_zh);});}else{return E(_4t);}},_zi=function(_zj){return E(_zj);},_zk=function(_zl){return E(_zl);},_zm=function(_zn){var _zo=E(_zn);if(!_zo._){var _zp=E(_zo.a);return (_zp==(-2147483648))?E(_7A):(_zp<0)?new T1(0, -_zp):E(_zo);}else{var _zq=_zo.a;return (I_compareInt(_zq,0)>=0)?E(_zo):new T1(1,I_negate(_zq));}},_zr=new T1(0,0),_zs=new T1(0,-1),_zt=function(_zu){var _zv=E(_zu);if(!_zv._){var _zw=_zv.a;return (_zw>=0)?(E(_zw)==0)?E(_zr):E(_5k):E(_zs);}else{var _zx=I_compareInt(_zv.a,0);return (_zx<=0)?(E(_zx)==0)?E(_zr):E(_zs):E(_5k);}},_zy={_:0,a:_4J,b:_6W,c:_vG,d:_7B,e:_zm,f:_zt,g:_zk},_zz=function(_zA,_zB){var _zC=E(_zA);if(!_zC._){var _zD=_zC.a,_zE=E(_zB);return (_zE._==0)?_zD!=_zE.a:(I_compareInt(_zE.a,_zD)==0)?false:true;}else{var _zF=_zC.a,_zG=E(_zB);return (_zG._==0)?(I_compareInt(_zF,_zG.a)==0)?false:true:(I_compare(_zF,_zG.a)==0)?false:true;}},_zH=new T2(0,_4y,_zz),_zI=function(_zJ,_zK){return (!B(_6H(_zJ,_zK)))?E(_zJ):E(_zK);},_zL=function(_zM,_zN){return (!B(_6H(_zM,_zN)))?E(_zN):E(_zM);},_zO={_:0,a:_zH,b:_3l,c:_S,d:_6H,e:_5c,f:_xN,g:_zI,h:_zL},_zP=function(_zQ){return new T2(0,E(_zQ),E(_nr));},_zR=new T3(0,_zy,_zO,_zP),_zS={_:0,a:_zR,b:_yi,c:_z0,d:_zf,e:_yr,f:_yP,g:_z3,h:_yD,i:_zi},_zT=function(_zU){return E(E(_zU).b);},_zV=function(_zW){return E(E(_zW).g);},_zX=new T1(0,1),_zY=function(_zZ,_A0,_A1){var _A2=B(_zT(_zZ)),_A3=B(_8s(_A2)),_A4=new T(function(){var _A5=new T(function(){var _A6=new T(function(){var _A7=new T(function(){return B(A3(_zV,_zZ,_zS,new T(function(){return B(A3(_a8,_A2,_A0,_A1));})));});return B(A2(_8I,_A3,_A7));}),_A8=new T(function(){return B(A2(_88,_A3,new T(function(){return B(A2(_8I,_A3,_zX));})));});return B(A3(_8u,_A3,_A8,_A6));});return B(A3(_8u,_A3,_A5,_A1));});return new F(function(){return A3(_86,_A3,_A0,_A4);});},_A9=1.5707963267948966,_Aa=function(_Ab){return 0.2/Math.cos(B(_zY(_xy,_Ab,_A9))-0.7853981633974483);},_Ac=new T(function(){var _Ad=B(_qh(_Aa,1.2,_rB,_rB,_rA,_rB,_rB,_rB,_rB,_rB,_rA,_rA,_rA));return {_:0,a:E(_Ad.a),b:E(_rC),c:E(_in),d:E(_Ad.d),e:E(_Ad.e),f:E(_Ad.f),g:E(_Ad.g),h:_Ad.h,i:_Ad.i,j:_Ad.j};}),_Ae=0,_Af=0.3,_Ag=function(_Ah){return E(_Af);},_Ai=new T(function(){var _Aj=B(_qh(_Ag,1.2,_rA,_rB,_rA,_rB,_rB,_rB,_rB,_rB,_rA,_rA,_rA));return {_:0,a:E(_Aj.a),b:E(_Aj.b),c:E(_Aj.c),d:E(_Aj.d),e:E(_Aj.e),f:E(_Aj.f),g:E(_Aj.g),h:_Aj.h,i:_Aj.i,j:_Aj.j};}),_Ak=new T(function(){var _Al=B(_qh(_Ag,1.2,_rA,_rA,_rB,_rB,_rB,_rB,_rB,_rB,_rA,_rA,_rA));return {_:0,a:E(_Al.a),b:E(_Al.b),c:E(_Al.c),d:E(_Al.d),e:E(_Al.e),f:E(_Al.f),g:E(_Al.g),h:_Al.h,i:_Al.i,j:_Al.j};}),_Am=2,_An=function(_Ao){return 0.3/Math.cos(B(_zY(_xy,_Ao,_A9))-0.7853981633974483);},_Ap=new T(function(){var _Aq=B(_qh(_An,1.2,_Am,_rA,_rA,_rB,_rB,_rB,_rB,_rB,_rA,_rA,_rA));return {_:0,a:E(_Aq.a),b:E(_Aq.b),c:E(_Aq.c),d:E(_Aq.d),e:E(_Aq.e),f:E(_Aq.f),g:E(_Aq.g),h:_Aq.h,i:_Aq.i,j:_Aq.j};}),_Ar=0.5,_As=new T(function(){var _At=B(_qh(_Ag,1.2,_rB,_rA,_Ar,_rB,_rB,_rB,_rB,_rB,_rA,_rA,_rA));return {_:0,a:E(_At.a),b:E(_At.b),c:E(_At.c),d:E(_At.d),e:E(_At.e),f:E(_At.f),g:E(_At.g),h:_At.h,i:_At.i,j:_At.j};}),_Au=new T2(1,_As,_w),_Av=new T2(1,_Ap,_Au),_Aw=new T2(1,_Ak,_Av),_Ax=new T2(1,_Ai,_Aw),_Ay=new T2(1,_Ac,_Ax),_Az=new T(function(){return B(unCStr("Negative range size"));}),_AA=new T(function(){return B(err(_Az));}),_AB=function(_){var _AC=B(_ie(_Ay,0))-1|0,_AD=function(_AE){if(_AE>=0){var _AF=newArr(_AE,_ik),_AG=_AF,_AH=E(_AE);if(!_AH){return new T4(0,E(_Ae),E(_AC),0,_AG);}else{var _AI=function(_AJ,_AK,_){while(1){var _AL=E(_AJ);if(!_AL._){return E(_);}else{var _=_AG[_AK]=_AL.a;if(_AK!=(_AH-1|0)){var _AM=_AK+1|0;_AJ=_AL.b;_AK=_AM;continue;}else{return E(_);}}}},_=B((function(_AN,_AO,_AP,_){var _=_AG[_AP]=_AN;if(_AP!=(_AH-1|0)){return new F(function(){return _AI(_AO,_AP+1|0,_);});}else{return E(_);}})(_Ac,_Ax,0,_));return new T4(0,E(_Ae),E(_AC),_AH,_AG);}}else{return E(_AA);}};if(0>_AC){return new F(function(){return _AD(0);});}else{return new F(function(){return _AD(_AC+1|0);});}},_AQ=function(_AR){var _AS=B(A1(_AR,_));return E(_AS);},_AT=new T(function(){return B(_AQ(_AB));}),_AU="enclose",_AV="outline",_AW="polygon",_AX="z",_AY="y",_AZ="x",_B0=function(_B1){return new F(function(){return _kD(new T2(1,new T2(0,_AZ,new T(function(){return E(E(E(E(_B1).d).a).a);})),new T2(1,new T2(0,_AY,new T(function(){return E(E(E(E(_B1).d).a).b);})),new T2(1,new T2(0,_AX,new T(function(){return E(E(E(E(_B1).d).a).c);})),new T2(1,new T2(0,_AW,new T(function(){return E(_B1).h;})),new T2(1,new T2(0,_AV,new T(function(){return E(_B1).i;})),new T2(1,new T2(0,_AU,new T(function(){return E(_B1).j;})),_w)))))));});},_B2=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_B3=new T(function(){return B(err(_B2));}),_B4=new T(function(){return eval("__strict(drawObjects)");}),_B5=new T(function(){return eval("__strict(draw)");}),_B6=function(_B7,_B8){var _B9=jsShowI(_B7);return new F(function(){return _n(fromJSStr(_B9),_B8);});},_Ba=function(_Bb,_Bc,_Bd){if(_Bc>=0){return new F(function(){return _B6(_Bc,_Bd);});}else{if(_Bb<=6){return new F(function(){return _B6(_Bc,_Bd);});}else{return new T2(1,_11,new T(function(){var _Be=jsShowI(_Bc);return B(_n(fromJSStr(_Be),new T2(1,_10,_Bd)));}));}}},_Bf=new T(function(){return B(unCStr(")"));}),_Bg=function(_Bh,_Bi){var _Bj=new T(function(){var _Bk=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Ba(0,_Bh,_w)),_Bf));})));},1);return B(_n(B(_Ba(0,_Bi,_w)),_Bk));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Bj)));});},_Bl=new T2(1,_kC,_w),_Bm=function(_Bn){return E(_Bn);},_Bo=function(_Bp){return E(_Bp);},_Bq=function(_Br,_Bs){return E(_Bs);},_Bt=function(_Bu,_Bv){return E(_Bu);},_Bw=function(_Bx){return E(_Bx);},_By=new T2(0,_Bw,_Bt),_Bz=function(_BA,_BB){return E(_BA);},_BC=new T5(0,_By,_Bo,_Bm,_Bq,_Bz),_BD="flipped2",_BE="flipped1",_BF="c1y",_BG="c1x",_BH="w2z",_BI="w2y",_BJ="w2x",_BK="w1z",_BL="w1y",_BM="w1x",_BN="d2z",_BO="d2y",_BP="d2x",_BQ="d1z",_BR="d1y",_BS="d1x",_BT="c2y",_BU="c2x",_BV=function(_BW,_){var _BX=__get(_BW,E(_BM)),_BY=__get(_BW,E(_BL)),_BZ=__get(_BW,E(_BK)),_C0=__get(_BW,E(_BJ)),_C1=__get(_BW,E(_BI)),_C2=__get(_BW,E(_BH)),_C3=__get(_BW,E(_BG)),_C4=__get(_BW,E(_BF)),_C5=__get(_BW,E(_BU)),_C6=__get(_BW,E(_BT)),_C7=__get(_BW,E(_BS)),_C8=__get(_BW,E(_BR)),_C9=__get(_BW,E(_BQ)),_Ca=__get(_BW,E(_BP)),_Cb=__get(_BW,E(_BO)),_Cc=__get(_BW,E(_BN)),_Cd=__get(_BW,E(_BE)),_Ce=__get(_BW,E(_BD));return {_:0,a:E(new T3(0,E(_BX),E(_BY),E(_BZ))),b:E(new T3(0,E(_C0),E(_C1),E(_C2))),c:E(new T2(0,E(_C3),E(_C4))),d:E(new T2(0,E(_C5),E(_C6))),e:E(new T3(0,E(_C7),E(_C8),E(_C9))),f:E(new T3(0,E(_Ca),E(_Cb),E(_Cc))),g:E(_Cd),h:E(_Ce)};},_Cf=function(_Cg,_){var _Ch=E(_Cg);if(!_Ch._){return _w;}else{var _Ci=B(_BV(E(_Ch.a),_)),_Cj=B(_Cf(_Ch.b,_));return new T2(1,_Ci,_Cj);}},_Ck=function(_Cl){var _Cm=E(_Cl);return (E(_Cm.b)-E(_Cm.a)|0)+1|0;},_Cn=function(_Co,_Cp){var _Cq=E(_Co),_Cr=E(_Cp);return (E(_Cq.a)>_Cr)?false:_Cr<=E(_Cq.b);},_Cs=function(_Ct){return new F(function(){return _Ba(0,E(_Ct),_w);});},_Cu=function(_Cv,_Cw,_Cx){return new F(function(){return _Ba(E(_Cv),E(_Cw),_Cx);});},_Cy=function(_Cz,_CA){return new F(function(){return _Ba(0,E(_Cz),_CA);});},_CB=function(_CC,_CD){return new F(function(){return _49(_Cy,_CC,_CD);});},_CE=new T3(0,_Cu,_Cs,_CB),_CF=0,_CG=function(_CH,_CI,_CJ){return new F(function(){return A1(_CH,new T2(1,_46,new T(function(){return B(A1(_CI,_CJ));})));});},_CK=new T(function(){return B(unCStr("foldr1"));}),_CL=new T(function(){return B(_mQ(_CK));}),_CM=function(_CN,_CO){var _CP=E(_CO);if(!_CP._){return E(_CL);}else{var _CQ=_CP.a,_CR=E(_CP.b);if(!_CR._){return E(_CQ);}else{return new F(function(){return A2(_CN,_CQ,new T(function(){return B(_CM(_CN,_CR));}));});}}},_CS=new T(function(){return B(unCStr(" out of range "));}),_CT=new T(function(){return B(unCStr("}.index: Index "));}),_CU=new T(function(){return B(unCStr("Ix{"));}),_CV=new T2(1,_10,_w),_CW=new T2(1,_10,_CV),_CX=0,_CY=function(_CZ){return E(E(_CZ).a);},_D0=function(_D1,_D2,_D3,_D4,_D5){var _D6=new T(function(){var _D7=new T(function(){var _D8=new T(function(){var _D9=new T(function(){var _Da=new T(function(){return B(A3(_CM,_CG,new T2(1,new T(function(){return B(A3(_CY,_D3,_CX,_D4));}),new T2(1,new T(function(){return B(A3(_CY,_D3,_CX,_D5));}),_w)),_CW));});return B(_n(_CS,new T2(1,_11,new T2(1,_11,_Da))));});return B(A(_CY,[_D3,_CF,_D2,new T2(1,_10,_D9)]));});return B(_n(_CT,new T2(1,_11,_D8)));},1);return B(_n(_D1,_D7));},1);return new F(function(){return err(B(_n(_CU,_D6)));});},_Db=function(_Dc,_Dd,_De,_Df,_Dg){return new F(function(){return _D0(_Dc,_Dd,_Dg,_De,_Df);});},_Dh=function(_Di,_Dj,_Dk,_Dl){var _Dm=E(_Dk);return new F(function(){return _Db(_Di,_Dj,_Dm.a,_Dm.b,_Dl);});},_Dn=function(_Do,_Dp,_Dq,_Dr){return new F(function(){return _Dh(_Dr,_Dq,_Dp,_Do);});},_Ds=new T(function(){return B(unCStr("Int"));}),_Dt=function(_Du,_Dv){return new F(function(){return _Dn(_CE,_Dv,_Du,_Ds);});},_Dw=function(_Dx,_Dy){var _Dz=E(_Dx),_DA=E(_Dz.a),_DB=E(_Dy);if(_DA>_DB){return new F(function(){return _Dt(_DB,_Dz);});}else{if(_DB>E(_Dz.b)){return new F(function(){return _Dt(_DB,_Dz);});}else{return _DB-_DA|0;}}},_DC=function(_DD){var _DE=E(_DD);return new F(function(){return _tn(_DE.a,_DE.b);});},_DF=function(_DG){var _DH=E(_DG),_DI=E(_DH.a),_DJ=E(_DH.b);return (_DI>_DJ)?E(_CF):(_DJ-_DI|0)+1|0;},_DK=function(_DL,_DM){return new F(function(){return _uM(_DM,E(_DL).a);});},_DN={_:0,a:_vC,b:_DC,c:_Dw,d:_DK,e:_Cn,f:_DF,g:_Ck},_DO=function(_DP,_DQ,_){while(1){var _DR=B((function(_DS,_DT,_){var _DU=E(_DS);if(!_DU._){return new T2(0,_kC,_DT);}else{var _DV=B(A2(_DU.a,_DT,_));_DP=_DU.b;_DQ=new T(function(){return E(E(_DV).b);});return __continue;}})(_DP,_DQ,_));if(_DR!=__continue){return _DR;}}},_DW=function(_DX,_DY){return new T2(1,_DX,_DY);},_DZ=function(_E0,_E1){var _E2=E(_E1);return new T2(0,_E2.a,_E2.b);},_E3=function(_E4){return E(E(_E4).f);},_E5=function(_E6,_E7,_E8){var _E9=E(_E7),_Ea=_E9.a,_Eb=_E9.b,_Ec=function(_){var _Ed=B(A2(_E3,_E6,_E9));if(_Ed>=0){var _Ee=newArr(_Ed,_ik),_Ef=_Ee,_Eg=E(_Ed);if(!_Eg){return new T(function(){return new T4(0,E(_Ea),E(_Eb),0,_Ef);});}else{var _Eh=function(_Ei,_Ej,_){while(1){var _Ek=E(_Ei);if(!_Ek._){return E(_);}else{var _=_Ef[_Ej]=_Ek.a;if(_Ej!=(_Eg-1|0)){var _El=_Ej+1|0;_Ei=_Ek.b;_Ej=_El;continue;}else{return E(_);}}}},_=B(_Eh(_E8,0,_));return new T(function(){return new T4(0,E(_Ea),E(_Eb),_Eg,_Ef);});}}else{return E(_AA);}};return new F(function(){return _AQ(_Ec);});},_Em=function(_En,_Eo,_Ep,_Eq){var _Er=new T(function(){var _Es=E(_Eq),_Et=_Es.c-1|0,_Eu=new T(function(){return B(A2(_dT,_Eo,_w));});if(0<=_Et){var _Ev=new T(function(){return B(_a4(_Eo));}),_Ew=function(_Ex){var _Ey=new T(function(){var _Ez=new T(function(){return B(A1(_Ep,new T(function(){return E(_Es.d[_Ex]);})));});return B(A3(_ac,_Ev,_DW,_Ez));});return new F(function(){return A3(_aa,_Eo,_Ey,new T(function(){if(_Ex!=_Et){return B(_Ew(_Ex+1|0));}else{return E(_Eu);}}));});};return B(_Ew(0));}else{return E(_Eu);}}),_EA=new T(function(){return B(_DZ(_En,_Eq));});return new F(function(){return A3(_ac,B(_a4(_Eo)),function(_EB){return new F(function(){return _E5(_En,_EA,_EB);});},_Er);});},_EC=function(_ED,_EE,_EF,_EG,_EH,_EI,_EJ,_EK,_EL){var _EM=B(_8u(_ED));return new T2(0,new T3(0,E(B(A1(B(A1(_EM,_EE)),_EI))),E(B(A1(B(A1(_EM,_EF)),_EJ))),E(B(A1(B(A1(_EM,_EG)),_EK)))),B(A1(B(A1(_EM,_EH)),_EL)));},_EN=function(_EO,_EP,_EQ,_ER,_ES,_ET,_EU,_EV,_EW){var _EX=B(_86(_EO));return new T2(0,new T3(0,E(B(A1(B(A1(_EX,_EP)),_ET))),E(B(A1(B(A1(_EX,_EQ)),_EU))),E(B(A1(B(A1(_EX,_ER)),_EV)))),B(A1(B(A1(_EX,_ES)),_EW)));},_EY=1.0e-2,_EZ=function(_F0,_F1,_F2,_F3,_F4,_F5,_F6,_F7,_F8,_F9,_Fa,_Fb,_Fc,_Fd,_Fe,_Ff,_Fg,_Fh){var _Fi=B(_EC(_jl,_F7,_F8,_F9,_Fa,_EY,_EY,_EY,_EY)),_Fj=E(_Fi.a),_Fk=B(_EN(_jl,_F3,_F4,_F5,_F6,_Fj.a,_Fj.b,_Fj.c,_Fi.b)),_Fl=E(_Fk.a);return new F(function(){return _py(_F0,_F1,_F2,_Fl.a,_Fl.b,_Fl.c,_Fk.b,_F7,_F8,_F9,_Fa,_Fb,_Fc,_Fd,_Fe,_Ff,_Fg,_Fh);});},_Fm=function(_Fn){var _Fo=E(_Fn),_Fp=E(_Fo.d),_Fq=E(_Fp.a),_Fr=E(_Fo.e),_Fs=E(_Fr.a),_Ft=E(_Fo.f),_Fu=B(_EZ(_Fo.a,_Fo.b,_Fo.c,_Fq.a,_Fq.b,_Fq.c,_Fp.b,_Fs.a,_Fs.b,_Fs.c,_Fr.b,_Ft.a,_Ft.b,_Ft.c,_Fo.g,_Fo.h,_Fo.i,_Fo.j));return {_:0,a:E(_Fu.a),b:E(_Fu.b),c:E(_Fu.c),d:E(_Fu.d),e:E(_Fu.e),f:E(_Fu.f),g:E(_Fu.g),h:_Fu.h,i:_Fu.i,j:_Fu.j};},_Fv=function(_Fw,_Fx,_Fy,_Fz,_FA,_FB,_FC,_FD,_FE){var _FF=B(_8s(B(_8q(_Fw))));return new F(function(){return A3(_86,_FF,new T(function(){return B(_8w(_Fw,_Fx,_Fy,_Fz,_FB,_FC,_FD));}),new T(function(){return B(A3(_8u,_FF,_FA,_FE));}));});},_FG=new T(function(){return B(unCStr("base"));}),_FH=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_FI=new T(function(){return B(unCStr("IOException"));}),_FJ=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_FG,_FH,_FI),_FK=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_FJ,_w,_w),_FL=function(_FM){return E(_FK);},_FN=function(_FO){var _FP=E(_FO);return new F(function(){return _3G(B(_3E(_FP.a)),_FL,_FP.b);});},_FQ=new T(function(){return B(unCStr(": "));}),_FR=new T(function(){return B(unCStr(")"));}),_FS=new T(function(){return B(unCStr(" ("));}),_FT=new T(function(){return B(unCStr("interrupted"));}),_FU=new T(function(){return B(unCStr("system error"));}),_FV=new T(function(){return B(unCStr("unsatisified constraints"));}),_FW=new T(function(){return B(unCStr("user error"));}),_FX=new T(function(){return B(unCStr("permission denied"));}),_FY=new T(function(){return B(unCStr("illegal operation"));}),_FZ=new T(function(){return B(unCStr("end of file"));}),_G0=new T(function(){return B(unCStr("resource exhausted"));}),_G1=new T(function(){return B(unCStr("resource busy"));}),_G2=new T(function(){return B(unCStr("does not exist"));}),_G3=new T(function(){return B(unCStr("already exists"));}),_G4=new T(function(){return B(unCStr("resource vanished"));}),_G5=new T(function(){return B(unCStr("timeout"));}),_G6=new T(function(){return B(unCStr("unsupported operation"));}),_G7=new T(function(){return B(unCStr("hardware fault"));}),_G8=new T(function(){return B(unCStr("inappropriate type"));}),_G9=new T(function(){return B(unCStr("invalid argument"));}),_Ga=new T(function(){return B(unCStr("failed"));}),_Gb=new T(function(){return B(unCStr("protocol error"));}),_Gc=function(_Gd,_Ge){switch(E(_Gd)){case 0:return new F(function(){return _n(_G3,_Ge);});break;case 1:return new F(function(){return _n(_G2,_Ge);});break;case 2:return new F(function(){return _n(_G1,_Ge);});break;case 3:return new F(function(){return _n(_G0,_Ge);});break;case 4:return new F(function(){return _n(_FZ,_Ge);});break;case 5:return new F(function(){return _n(_FY,_Ge);});break;case 6:return new F(function(){return _n(_FX,_Ge);});break;case 7:return new F(function(){return _n(_FW,_Ge);});break;case 8:return new F(function(){return _n(_FV,_Ge);});break;case 9:return new F(function(){return _n(_FU,_Ge);});break;case 10:return new F(function(){return _n(_Gb,_Ge);});break;case 11:return new F(function(){return _n(_Ga,_Ge);});break;case 12:return new F(function(){return _n(_G9,_Ge);});break;case 13:return new F(function(){return _n(_G8,_Ge);});break;case 14:return new F(function(){return _n(_G7,_Ge);});break;case 15:return new F(function(){return _n(_G6,_Ge);});break;case 16:return new F(function(){return _n(_G5,_Ge);});break;case 17:return new F(function(){return _n(_G4,_Ge);});break;default:return new F(function(){return _n(_FT,_Ge);});}},_Gf=new T(function(){return B(unCStr("}"));}),_Gg=new T(function(){return B(unCStr("{handle: "));}),_Gh=function(_Gi,_Gj,_Gk,_Gl,_Gm,_Gn){var _Go=new T(function(){var _Gp=new T(function(){var _Gq=new T(function(){var _Gr=E(_Gl);if(!_Gr._){return E(_Gn);}else{var _Gs=new T(function(){return B(_n(_Gr,new T(function(){return B(_n(_FR,_Gn));},1)));},1);return B(_n(_FS,_Gs));}},1);return B(_Gc(_Gj,_Gq));}),_Gt=E(_Gk);if(!_Gt._){return E(_Gp);}else{return B(_n(_Gt,new T(function(){return B(_n(_FQ,_Gp));},1)));}}),_Gu=E(_Gm);if(!_Gu._){var _Gv=E(_Gi);if(!_Gv._){return E(_Go);}else{var _Gw=E(_Gv.a);if(!_Gw._){var _Gx=new T(function(){var _Gy=new T(function(){return B(_n(_Gf,new T(function(){return B(_n(_FQ,_Go));},1)));},1);return B(_n(_Gw.a,_Gy));},1);return new F(function(){return _n(_Gg,_Gx);});}else{var _Gz=new T(function(){var _GA=new T(function(){return B(_n(_Gf,new T(function(){return B(_n(_FQ,_Go));},1)));},1);return B(_n(_Gw.a,_GA));},1);return new F(function(){return _n(_Gg,_Gz);});}}}else{return new F(function(){return _n(_Gu.a,new T(function(){return B(_n(_FQ,_Go));},1));});}},_GB=function(_GC){var _GD=E(_GC);return new F(function(){return _Gh(_GD.a,_GD.b,_GD.c,_GD.d,_GD.f,_w);});},_GE=function(_GF,_GG,_GH){var _GI=E(_GG);return new F(function(){return _Gh(_GI.a,_GI.b,_GI.c,_GI.d,_GI.f,_GH);});},_GJ=function(_GK,_GL){var _GM=E(_GK);return new F(function(){return _Gh(_GM.a,_GM.b,_GM.c,_GM.d,_GM.f,_GL);});},_GN=function(_GO,_GP){return new F(function(){return _49(_GJ,_GO,_GP);});},_GQ=new T3(0,_GE,_GB,_GN),_GR=new T(function(){return new T5(0,_FL,_GQ,_GS,_FN,_GB);}),_GS=function(_GT){return new T2(0,_GR,_GT);},_GU=__Z,_GV=7,_GW=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_GX=new T6(0,_GU,_GV,_w,_GW,_GU,_GU),_GY=new T(function(){return B(_GS(_GX));}),_GZ=function(_){return new F(function(){return die(_GY);});},_H0=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_H1=new T6(0,_GU,_GV,_w,_H0,_GU,_GU),_H2=new T(function(){return B(_GS(_H1));}),_H3=function(_){return new F(function(){return die(_H2);});},_H4=function(_H5,_){return new T2(0,_w,_H5);},_H6=0.6,_H7=1,_H8=new T(function(){return B(unCStr(")"));}),_H9=function(_Ha,_Hb){var _Hc=new T(function(){var _Hd=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Ba(0,_Ha,_w)),_H8));})));},1);return B(_n(B(_Ba(0,_Hb,_w)),_Hd));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Hc)));});},_He=function(_Hf,_Hg){var _Hh=new T(function(){var _Hi=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Ba(0,_Hg,_w)),_H8));})));},1);return B(_n(B(_Ba(0,_Hf,_w)),_Hi));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Hh)));});},_Hj=function(_Hk){var _Hl=E(_Hk);if(!_Hl._){return E(_H4);}else{var _Hm=new T(function(){return B(_Hj(_Hl.b));}),_Hn=function(_Ho){var _Hp=E(_Ho);if(!_Hp._){return E(_Hm);}else{var _Hq=_Hp.a,_Hr=new T(function(){return B(_Hn(_Hp.b));}),_Hs=new T(function(){return 0.1*E(E(_Hq).e)/1.0e-2;}),_Ht=new T(function(){var _Hu=E(_Hq);if(_Hu.a!=_Hu.b){return E(_H7);}else{return E(_H6);}}),_Hv=function(_Hw,_){var _Hx=E(_Hw),_Hy=_Hx.c,_Hz=_Hx.d,_HA=E(_Hx.a),_HB=E(_Hx.b),_HC=E(_Hq),_HD=_HC.a,_HE=_HC.b,_HF=E(_HC.c),_HG=_HF.b,_HH=E(_HF.a),_HI=_HH.a,_HJ=_HH.b,_HK=_HH.c,_HL=E(_HC.d),_HM=_HL.b,_HN=E(_HL.a),_HO=_HN.a,_HP=_HN.b,_HQ=_HN.c;if(_HA>_HD){return new F(function(){return _H3(_);});}else{if(_HD>_HB){return new F(function(){return _H3(_);});}else{if(_HA>_HE){return new F(function(){return _GZ(_);});}else{if(_HE>_HB){return new F(function(){return _GZ(_);});}else{var _HR=_HD-_HA|0;if(0>_HR){return new F(function(){return _H9(_Hy,_HR);});}else{if(_HR>=_Hy){return new F(function(){return _H9(_Hy,_HR);});}else{var _HS=E(_Hz[_HR]),_HT=E(_HS.c),_HU=_HT.b,_HV=E(_HT.a),_HW=_HV.a,_HX=_HV.b,_HY=_HV.c,_HZ=E(_HS.e),_I0=E(_HZ.a),_I1=B(_EC(_jl,_HI,_HJ,_HK,_HG,_HW,_HX,_HY,_HU)),_I2=E(_I1.a),_I3=B(_EC(_jl,_I2.a,_I2.b,_I2.c,_I1.b,_HI,_HJ,_HK,_HG)),_I4=E(_I3.a),_I5=_HE-_HA|0;if(0>_I5){return new F(function(){return _He(_I5,_Hy);});}else{if(_I5>=_Hy){return new F(function(){return _He(_I5,_Hy);});}else{var _I6=E(_Hz[_I5]),_I7=E(_I6.c),_I8=_I7.b,_I9=E(_I7.a),_Ia=_I9.a,_Ib=_I9.b,_Ic=_I9.c,_Id=E(_I6.e),_Ie=E(_Id.a),_If=B(_EC(_jl,_HO,_HP,_HQ,_HM,_Ia,_Ib,_Ic,_I8)),_Ig=E(_If.a),_Ih=B(_EC(_jl,_Ig.a,_Ig.b,_Ig.c,_If.b,_HO,_HP,_HQ,_HM)),_Ii=E(_Ih.a),_Ij=E(_I4.a)+E(_I4.b)+E(_I4.c)+E(_I3.b)+E(_Ii.a)+E(_Ii.b)+E(_Ii.c)+E(_Ih.b);if(!_Ij){var _Ik=B(A2(_Hr,_Hx,_));return new T2(0,new T2(1,_kC,new T(function(){return E(E(_Ik).a);})),new T(function(){return E(E(_Ik).b);}));}else{var _Il=new T(function(){return  -((B(_Fv(_jR,_I0.a,_I0.b,_I0.c,_HZ.b,_HI,_HJ,_HK,_HG))-B(_Fv(_jR,_Ie.a,_Ie.b,_Ie.c,_Id.b,_HO,_HP,_HQ,_HM))-E(_Hs))/_Ij);}),_Im=function(_In,_Io,_Ip,_Iq,_){var _Ir=new T(function(){var _Is=function(_It,_Iu,_Iv,_Iw,_Ix){if(_It>_HE){return E(_Ix);}else{if(_HE>_Iu){return E(_Ix);}else{var _Iy=function(_){var _Iz=newArr(_Iv,_ik),_IA=_Iz,_IB=function(_IC,_){while(1){if(_IC!=_Iv){var _=_IA[_IC]=_Iw[_IC],_ID=_IC+1|0;_IC=_ID;continue;}else{return E(_);}}},_=B(_IB(0,_)),_IE=_HE-_It|0;if(0>_IE){return new F(function(){return _He(_IE,_Iv);});}else{if(_IE>=_Iv){return new F(function(){return _He(_IE,_Iv);});}else{var _=_IA[_IE]=new T(function(){var _IF=E(_Iw[_IE]),_IG=E(_IF.e),_IH=E(_IG.a),_II=B(_EC(_jl,_Ia,_Ib,_Ic,_I8,_HO,_HP,_HQ,_HM)),_IJ=E(_II.a),_IK=E(_Il)*E(_Ht),_IL=B(_EC(_jl,_IJ.a,_IJ.b,_IJ.c,_II.b,_IK,_IK,_IK,_IK)),_IM=E(_IL.a),_IN=B(_EN(_jl,_IH.a,_IH.b,_IH.c,_IG.b, -E(_IM.a), -E(_IM.b), -E(_IM.c), -E(_IL.b)));return {_:0,a:E(_IF.a),b:E(_IF.b),c:E(_IF.c),d:E(_IF.d),e:E(new T2(0,E(_IN.a),E(_IN.b))),f:E(_IF.f),g:E(_IF.g),h:_IF.h,i:_IF.i,j:_IF.j};});return new T4(0,E(_It),E(_Iu),_Iv,_IA);}}};return new F(function(){return _AQ(_Iy);});}}};if(_In>_HD){return B(_Is(_In,_Io,_Ip,_Iq,new T4(0,E(_In),E(_Io),_Ip,_Iq)));}else{if(_HD>_Io){return B(_Is(_In,_Io,_Ip,_Iq,new T4(0,E(_In),E(_Io),_Ip,_Iq)));}else{var _IO=function(_){var _IP=newArr(_Ip,_ik),_IQ=_IP,_IR=function(_IS,_){while(1){if(_IS!=_Ip){var _=_IQ[_IS]=_Iq[_IS],_IT=_IS+1|0;_IS=_IT;continue;}else{return E(_);}}},_=B(_IR(0,_)),_IU=_HD-_In|0;if(0>_IU){return new F(function(){return _H9(_Ip,_IU);});}else{if(_IU>=_Ip){return new F(function(){return _H9(_Ip,_IU);});}else{var _=_IQ[_IU]=new T(function(){var _IV=E(_Iq[_IU]),_IW=E(_IV.e),_IX=E(_IW.a),_IY=B(_EC(_jl,_HW,_HX,_HY,_HU,_HI,_HJ,_HK,_HG)),_IZ=E(_IY.a),_J0=E(_Il)*E(_Ht),_J1=B(_EC(_jl,_IZ.a,_IZ.b,_IZ.c,_IY.b,_J0,_J0,_J0,_J0)),_J2=E(_J1.a),_J3=B(_EN(_jl,_IX.a,_IX.b,_IX.c,_IW.b,_J2.a,_J2.b,_J2.c,_J1.b));return {_:0,a:E(_IV.a),b:E(_IV.b),c:E(_IV.c),d:E(_IV.d),e:E(new T2(0,E(_J3.a),E(_J3.b))),f:E(_IV.f),g:E(_IV.g),h:_IV.h,i:_IV.i,j:_IV.j};});return new T4(0,E(_In),E(_Io),_Ip,_IQ);}}},_J4=B(_AQ(_IO));return B(_Is(E(_J4.a),E(_J4.b),_J4.c,_J4.d,_J4));}}});return new T2(0,_kC,_Ir);};if(!E(_HC.f)){var _J5=B(_Im(_HA,_HB,_Hy,_Hz,_)),_J6=B(A2(_Hr,new T(function(){return E(E(_J5).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_J5).a);}),new T(function(){return E(E(_J6).a);})),new T(function(){return E(E(_J6).b);}));}else{if(E(_Il)<0){var _J7=B(A2(_Hr,_Hx,_));return new T2(0,new T2(1,_kC,new T(function(){return E(E(_J7).a);})),new T(function(){return E(E(_J7).b);}));}else{var _J8=B(_Im(_HA,_HB,_Hy,_Hz,_)),_J9=B(A2(_Hr,new T(function(){return E(E(_J8).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_J8).a);}),new T(function(){return E(E(_J9).a);})),new T(function(){return E(E(_J9).b);}));}}}}}}}}}}}};return E(_Hv);}};return new F(function(){return _Hn(_Hl.a);});}},_Ja=function(_,_Jb){var _Jc=new T(function(){return B(_Hj(E(_Jb).a));}),_Jd=function(_Je){var _Jf=E(_Je);return (_Jf==1)?E(new T2(1,_Jc,_w)):new T2(1,_Jc,new T(function(){return B(_Jd(_Jf-1|0));}));},_Jg=B(_DO(B(_Jd(5)),new T(function(){return E(E(_Jb).b);}),_)),_Jh=new T(function(){return B(_Em(_DN,_BC,_Fm,new T(function(){return E(E(_Jg).b);})));});return new T2(0,_kC,_Jh);},_Ji=function(_Jj,_Jk,_Jl,_Jm,_Jn){var _Jo=B(_8s(B(_8q(_Jj))));return new F(function(){return A3(_86,_Jo,new T(function(){return B(A3(_8u,_Jo,_Jk,_Jm));}),new T(function(){return B(A3(_8u,_Jo,_Jl,_Jn));}));});},_Jp=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Jq=new T6(0,_GU,_GV,_w,_Jp,_GU,_GU),_Jr=new T(function(){return B(_GS(_Jq));}),_Js=function(_){return new F(function(){return die(_Jr);});},_Jt=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Ju=new T6(0,_GU,_GV,_w,_Jt,_GU,_GU),_Jv=new T(function(){return B(_GS(_Ju));}),_Jw=function(_){return new F(function(){return die(_Jv);});},_Jx=false,_Jy=true,_Jz=function(_JA){var _JB=E(_JA),_JC=_JB.b,_JD=E(_JB.d),_JE=E(_JB.e),_JF=E(_JE.a),_JG=E(_JB.g),_JH=B(A1(_JC,_JD.a)),_JI=B(_m3(_jR,_JH.a,_JH.b,_JH.c,_JG.a,_JG.b,_JG.c));return {_:0,a:E(_JB.a),b:E(_JC),c:E(_JB.c),d:E(_JD),e:E(new T2(0,E(new T3(0,E(_JF.a)+E(_JI.a)*1.0e-2,E(_JF.b)+E(_JI.b)*1.0e-2,E(_JF.c)+E(_JI.c)*1.0e-2)),E(_JE.b))),f:E(_JB.f),g:E(_JG),h:_JB.h,i:_JB.i,j:_JB.j};},_JJ=new T(function(){return eval("__strict(collideBound)");}),_JK=new T(function(){return eval("__strict(mouseContact)");}),_JL=new T(function(){return eval("__strict(collide)");}),_JM=function(_JN){var _JO=E(_JN);if(!_JO._){return __Z;}else{return new F(function(){return _n(_JO.a,new T(function(){return B(_JM(_JO.b));},1));});}},_JP=0,_JQ=new T3(0,E(_JP),E(_JP),E(_JP)),_JR=new T2(0,E(_JQ),E(_JP)),_JS=new T2(0,_jR,_kq),_JT=new T(function(){return B(_hQ(_JS));}),_JU=function(_JV,_){var _JW=B(_Em(_DN,_BC,_Jz,_JV)),_JX=E(_JW.a),_JY=E(_JW.b);if(_JX<=_JY){var _JZ=function(_K0,_K1,_K2,_K3,_K4,_){if(_K1>_K0){return new F(function(){return _Jw(_);});}else{if(_K0>_K2){return new F(function(){return _Jw(_);});}else{var _K5=new T(function(){var _K6=_K0-_K1|0;if(0>_K6){return B(_He(_K6,_K3));}else{if(_K6>=_K3){return B(_He(_K6,_K3));}else{return E(_K4[_K6]);}}}),_K7=function(_K8,_K9,_Ka,_Kb,_Kc,_){var _Kd=E(_K8);if(!_Kd._){return new T2(0,_w,new T4(0,E(_K9),E(_Ka),_Kb,_Kc));}else{var _Ke=E(_Kd.a);if(_K9>_Ke){return new F(function(){return _Js(_);});}else{if(_Ke>_Ka){return new F(function(){return _Js(_);});}else{var _Kf=_Ke-_K9|0;if(0>_Kf){return new F(function(){return _H9(_Kb,_Kf);});}else{if(_Kf>=_Kb){return new F(function(){return _H9(_Kb,_Kf);});}else{var _Kg=__app2(E(_JL),B(_B0(E(_K5))),B(_B0(E(_Kc[_Kf])))),_Kh=__arr2lst(0,_Kg),_Ki=B(_Cf(_Kh,_)),_Kj=B(_K7(_Kd.b,_K9,_Ka,_Kb,_Kc,_)),_Kk=new T(function(){var _Kl=new T(function(){return _K0!=_Ke;}),_Km=function(_Kn){var _Ko=E(_Kn);if(!_Ko._){return __Z;}else{var _Kp=_Ko.b,_Kq=E(_Ko.a),_Kr=E(_Kq.b),_Ks=E(_Kq.a),_Kt=E(_Kq.c),_Ku=_Kt.a,_Kv=_Kt.b,_Kw=E(_Kq.e),_Kx=E(_Kq.d),_Ky=_Kx.a,_Kz=_Kx.b,_KA=E(_Kq.f),_KB=new T(function(){var _KC=B(_lg(_jR,_KA.a,_KA.b,_KA.c)),_KD=Math.sqrt(B(_Ji(_jR,_Ky,_Kz,_Ky,_Kz)));return new T3(0,_KD*E(_KC.a),_KD*E(_KC.b),_KD*E(_KC.c));}),_KE=new T(function(){var _KF=B(_lg(_jR,_Kw.a,_Kw.b,_Kw.c)),_KG=Math.sqrt(B(_Ji(_jR,_Ku,_Kv,_Ku,_Kv)));return new T3(0,_KG*E(_KF.a),_KG*E(_KF.b),_KG*E(_KF.c));}),_KH=new T(function(){var _KI=B(A1(_JT,_Kr)),_KJ=B(_lg(_jR,_KI.a,_KI.b,_KI.c));return new T3(0,E(_KJ.a),E(_KJ.b),E(_KJ.c));}),_KK=new T(function(){var _KL=B(A1(_JT,_Ks)),_KM=B(_lg(_jR,_KL.a,_KL.b,_KL.c));return new T3(0,E(_KM.a),E(_KM.b),E(_KM.c));}),_KN=E(_Kr.a)+ -E(_Ks.a),_KO=E(_Kr.b)+ -E(_Ks.b),_KP=E(_Kr.c)+ -E(_Ks.c),_KQ=new T(function(){return Math.sqrt(B(_8w(_jR,_KN,_KO,_KP,_KN,_KO,_KP)));}),_KR=new T(function(){var _KS=1/E(_KQ);return new T3(0,_KN*_KS,_KO*_KS,_KP*_KS);}),_KT=new T(function(){if(!E(_Kq.g)){return E(_KR);}else{var _KU=E(_KR);return new T3(0,-1*E(_KU.a),-1*E(_KU.b),-1*E(_KU.c));}}),_KV=new T(function(){if(!E(_Kq.h)){return E(_KR);}else{var _KW=E(_KR);return new T3(0,-1*E(_KW.a),-1*E(_KW.b),-1*E(_KW.c));}});return (!E(_Kl))?new T2(1,new T(function(){var _KX=E(_KT),_KY=E(_KX.b),_KZ=E(_KX.c),_L0=E(_KX.a),_L1=E(_KK),_L2=E(_L1.c),_L3=E(_L1.b),_L4=E(_L1.a),_L5=E(_KE),_L6=E(_L5.c),_L7=E(_L5.b),_L8=E(_L5.a),_L9=_KY*_L2-_L3*_KZ,_La=_KZ*_L4-_L2*_L0,_Lb=_L0*_L3-_L4*_KY,_Lc=B(_8w(_jR,_La*_L6-_L7*_Lb,_Lb*_L8-_L6*_L9,_L9*_L7-_L8*_La,_L4,_L3,_L2));return new T6(0,_K0,_Ke,E(new T2(0,E(new T3(0,E(_L9),E(_La),E(_Lb))),E(_Lc))),E(_JR),_KQ,_Jx);}),new T2(1,new T(function(){var _Ld=E(_KV),_Le=E(_Ld.b),_Lf=E(_Ld.c),_Lg=E(_Ld.a),_Lh=E(_KH),_Li=E(_Lh.c),_Lj=E(_Lh.b),_Lk=E(_Lh.a),_Ll=E(_KB),_Lm=E(_Ll.c),_Ln=E(_Ll.b),_Lo=E(_Ll.a),_Lp=_Le*_Li-_Lj*_Lf,_Lq=_Lf*_Lk-_Li*_Lg,_Lr=_Lg*_Lj-_Lk*_Le,_Ls=B(_8w(_jR,_Lq*_Lm-_Ln*_Lr,_Lr*_Lo-_Lm*_Lp,_Lp*_Ln-_Lo*_Lq,_Lk,_Lj,_Li));return new T6(0,_K0,_Ke,E(_JR),E(new T2(0,E(new T3(0,E(_Lp),E(_Lq),E(_Lr))),E(_Ls))),_KQ,_Jx);}),new T(function(){return B(_Km(_Kp));}))):new T2(1,new T(function(){var _Lt=E(_KT),_Lu=E(_Lt.b),_Lv=E(_Lt.c),_Lw=E(_Lt.a),_Lx=E(_KK),_Ly=_Lx.a,_Lz=_Lx.b,_LA=_Lx.c,_LB=B(_m3(_jR,_Lw,_Lu,_Lv,_Ly,_Lz,_LA)),_LC=E(_KE),_LD=E(_LC.c),_LE=E(_LC.b),_LF=E(_LC.a),_LG=B(_8w(_jR,_Lu*_LD-_LE*_Lv,_Lv*_LF-_LD*_Lw,_Lw*_LE-_LF*_Lu,_Ly,_Lz,_LA)),_LH=E(_KV),_LI=E(_LH.b),_LJ=E(_LH.c),_LK=E(_LH.a),_LL=E(_KH),_LM=_LL.a,_LN=_LL.b,_LO=_LL.c,_LP=B(_m3(_jR,_LK,_LI,_LJ,_LM,_LN,_LO)),_LQ=E(_KB),_LR=E(_LQ.c),_LS=E(_LQ.b),_LT=E(_LQ.a),_LU=B(_8w(_jR,_LI*_LR-_LS*_LJ,_LJ*_LT-_LR*_LK,_LK*_LS-_LT*_LI,_LM,_LN,_LO));return new T6(0,_K0,_Ke,E(new T2(0,E(new T3(0,E(_LB.a),E(_LB.b),E(_LB.c))),E(_LG))),E(new T2(0,E(new T3(0,E(_LP.a),E(_LP.b),E(_LP.c))),E(_LU))),_KQ,_Jy);}),new T(function(){return B(_Km(_Kp));}));}};return B(_Km(_Ki));});return new T2(0,new T2(1,_Kk,new T(function(){return E(E(_Kj).a);})),new T(function(){return E(E(_Kj).b);}));}}}}}},_LV=B(_K7(B(_sM(_K0,_JY)),_K1,_K2,_K3,_K4,_)),_LW=E(_K5),_LX=E(_LW.d).a,_LY=__app1(E(_JJ),B(_B0(_LW))),_LZ=__arr2lst(0,_LY),_M0=B(_Cf(_LZ,_)),_M1=__app1(E(_JK),_K0),_M2=__arr2lst(0,_M1),_M3=B(_Cf(_M2,_));if(_K0!=_JY){var _M4=E(_LV),_M5=E(_M4.b),_M6=B(_JZ(_K0+1|0,E(_M5.a),E(_M5.b),_M5.c,_M5.d,_)),_M7=new T(function(){var _M8=new T(function(){var _M9=B(A1(_JT,_LX)),_Ma=B(_lg(_jR,_M9.a,_M9.b,_M9.c));return new T3(0,E(_Ma.a),E(_Ma.b),E(_Ma.c));}),_Mb=new T(function(){var _Mc=new T(function(){return B(_JM(_M4.a));}),_Md=function(_Me){var _Mf=E(_Me);if(!_Mf._){return E(_Mc);}else{var _Mg=E(_Mf.a),_Mh=E(_Mg.b),_Mi=E(_Mg.a),_Mj=E(_Mg.c),_Mk=_Mj.a,_Ml=_Mj.b,_Mm=E(_Mg.e);return new T2(1,new T(function(){var _Mn=E(_Mh.a)+ -E(_Mi.a),_Mo=E(_Mh.b)+ -E(_Mi.b),_Mp=E(_Mh.c)+ -E(_Mi.c),_Mq=B(A1(_JT,_Mi)),_Mr=B(_lg(_jR,_Mq.a,_Mq.b,_Mq.c)),_Ms=_Mr.a,_Mt=_Mr.b,_Mu=_Mr.c,_Mv=Math.sqrt(B(_8w(_jR,_Mn,_Mo,_Mp,_Mn,_Mo,_Mp))),_Mw=1/_Mv,_Mx=_Mn*_Mw,_My=_Mo*_Mw,_Mz=_Mp*_Mw,_MA=B(_m3(_jR,_Mx,_My,_Mz,_Ms,_Mt,_Mu)),_MB=B(_lg(_jR,_Mm.a,_Mm.b,_Mm.c)),_MC=Math.sqrt(B(_Ji(_jR,_Mk,_Ml,_Mk,_Ml))),_MD=_MC*E(_MB.a),_ME=_MC*E(_MB.b),_MF=_MC*E(_MB.c),_MG=B(_8w(_jR,_My*_MF-_ME*_Mz,_Mz*_MD-_MF*_Mx,_Mx*_ME-_MD*_My,_Ms,_Mt,_Mu));return new T6(0,_K0,_K0,E(new T2(0,E(new T3(0,E(_MA.a),E(_MA.b),E(_MA.c))),E(_MG))),E(_JR),_Mv,_Jy);}),new T(function(){return B(_Md(_Mf.b));}));}};return B(_Md(_M0));}),_MH=function(_MI){var _MJ=E(_MI);if(!_MJ._){return E(_Mb);}else{var _MK=E(_MJ.a),_ML=E(_MK.b),_MM=new T(function(){var _MN=E(_LX),_MO=E(_ML.c)+ -E(_MN.c),_MP=E(_ML.b)+ -E(_MN.b),_MQ=E(_ML.a)+ -E(_MN.a),_MR=Math.sqrt(B(_8w(_jR,_MQ,_MP,_MO,_MQ,_MP,_MO))),_MS=function(_MT,_MU,_MV){var _MW=E(_M8),_MX=_MW.a,_MY=_MW.b,_MZ=_MW.c,_N0=B(_m3(_jR,_MT,_MU,_MV,_MX,_MY,_MZ)),_N1=B(_8w(_jR,_MU*0-0*_MV,_MV*0-0*_MT,_MT*0-0*_MU,_MX,_MY,_MZ));return new T6(0,_K0,_K0,new T2(0,E(new T3(0,E(_N0.a),E(_N0.b),E(_N0.c))),E(_N1)),_JR,_MR,_Jy);};if(!E(_MK.g)){var _N2=1/_MR,_N3=B(_MS(_MQ*_N2,_MP*_N2,_MO*_N2));return new T6(0,_N3.a,_N3.b,E(_N3.c),E(_N3.d),_N3.e,_N3.f);}else{var _N4=1/_MR,_N5=B(_MS(-1*_MQ*_N4,-1*_MP*_N4,-1*_MO*_N4));return new T6(0,_N5.a,_N5.b,E(_N5.c),E(_N5.d),_N5.e,_N5.f);}});return new T2(1,_MM,new T(function(){return B(_MH(_MJ.b));}));}};return B(_MH(_M3));});return new T2(0,new T2(1,_M7,new T(function(){return E(E(_M6).a);})),new T(function(){return E(E(_M6).b);}));}else{var _N6=new T(function(){var _N7=new T(function(){var _N8=B(A1(_JT,_LX)),_N9=B(_lg(_jR,_N8.a,_N8.b,_N8.c));return new T3(0,E(_N9.a),E(_N9.b),E(_N9.c));}),_Na=new T(function(){var _Nb=new T(function(){return B(_JM(E(_LV).a));}),_Nc=function(_Nd){var _Ne=E(_Nd);if(!_Ne._){return E(_Nb);}else{var _Nf=E(_Ne.a),_Ng=E(_Nf.b),_Nh=E(_Nf.a),_Ni=E(_Nf.c),_Nj=_Ni.a,_Nk=_Ni.b,_Nl=E(_Nf.e);return new T2(1,new T(function(){var _Nm=E(_Ng.a)+ -E(_Nh.a),_Nn=E(_Ng.b)+ -E(_Nh.b),_No=E(_Ng.c)+ -E(_Nh.c),_Np=B(A1(_JT,_Nh)),_Nq=B(_lg(_jR,_Np.a,_Np.b,_Np.c)),_Nr=_Nq.a,_Ns=_Nq.b,_Nt=_Nq.c,_Nu=Math.sqrt(B(_8w(_jR,_Nm,_Nn,_No,_Nm,_Nn,_No))),_Nv=1/_Nu,_Nw=_Nm*_Nv,_Nx=_Nn*_Nv,_Ny=_No*_Nv,_Nz=B(_m3(_jR,_Nw,_Nx,_Ny,_Nr,_Ns,_Nt)),_NA=B(_lg(_jR,_Nl.a,_Nl.b,_Nl.c)),_NB=Math.sqrt(B(_Ji(_jR,_Nj,_Nk,_Nj,_Nk))),_NC=_NB*E(_NA.a),_ND=_NB*E(_NA.b),_NE=_NB*E(_NA.c),_NF=B(_8w(_jR,_Nx*_NE-_ND*_Ny,_Ny*_NC-_NE*_Nw,_Nw*_ND-_NC*_Nx,_Nr,_Ns,_Nt));return new T6(0,_K0,_K0,E(new T2(0,E(new T3(0,E(_Nz.a),E(_Nz.b),E(_Nz.c))),E(_NF))),E(_JR),_Nu,_Jy);}),new T(function(){return B(_Nc(_Ne.b));}));}};return B(_Nc(_M0));}),_NG=function(_NH){var _NI=E(_NH);if(!_NI._){return E(_Na);}else{var _NJ=E(_NI.a),_NK=E(_NJ.b),_NL=new T(function(){var _NM=E(_LX),_NN=E(_NK.c)+ -E(_NM.c),_NO=E(_NK.b)+ -E(_NM.b),_NP=E(_NK.a)+ -E(_NM.a),_NQ=Math.sqrt(B(_8w(_jR,_NP,_NO,_NN,_NP,_NO,_NN))),_NR=function(_NS,_NT,_NU){var _NV=E(_N7),_NW=_NV.a,_NX=_NV.b,_NY=_NV.c,_NZ=B(_m3(_jR,_NS,_NT,_NU,_NW,_NX,_NY)),_O0=B(_8w(_jR,_NT*0-0*_NU,_NU*0-0*_NS,_NS*0-0*_NT,_NW,_NX,_NY));return new T6(0,_K0,_K0,new T2(0,E(new T3(0,E(_NZ.a),E(_NZ.b),E(_NZ.c))),E(_O0)),_JR,_NQ,_Jy);};if(!E(_NJ.g)){var _O1=1/_NQ,_O2=B(_NR(_NP*_O1,_NO*_O1,_NN*_O1));return new T6(0,_O2.a,_O2.b,E(_O2.c),E(_O2.d),_O2.e,_O2.f);}else{var _O3=1/_NQ,_O4=B(_NR(-1*_NP*_O3,-1*_NO*_O3,-1*_NN*_O3));return new T6(0,_O4.a,_O4.b,E(_O4.c),E(_O4.d),_O4.e,_O4.f);}});return new T2(1,_NL,new T(function(){return B(_NG(_NI.b));}));}};return B(_NG(_M3));});return new T2(0,new T2(1,_N6,_w),new T(function(){return E(E(_LV).b);}));}}}},_O5=B(_JZ(_JX,_JX,_JY,_JW.c,_JW.d,_));return new F(function(){return _Ja(_,_O5);});}else{return new F(function(){return _Ja(_,new T2(0,_w,_JW));});}},_O6=new T(function(){return eval("__strict(passObject)");}),_O7=new T(function(){return eval("__strict(refresh)");}),_O8=function(_O9,_){var _Oa=__app0(E(_O7)),_Ob=__app0(E(_B5)),_Oc=E(_O9),_Od=_Oc.c,_Oe=_Oc.d,_Of=E(_Oc.a),_Og=E(_Oc.b);if(_Of<=_Og){if(_Of>_Og){return E(_B3);}else{if(0>=_Od){return new F(function(){return _Bg(_Od,0);});}else{var _Oh=E(_O6),_Oi=__app2(_Oh,_Of,B(_B0(E(_Oe[0]))));if(_Of!=_Og){var _Oj=function(_Ok,_){if(_Of>_Ok){return E(_B3);}else{if(_Ok>_Og){return E(_B3);}else{var _Ol=_Ok-_Of|0;if(0>_Ol){return new F(function(){return _Bg(_Od,_Ol);});}else{if(_Ol>=_Od){return new F(function(){return _Bg(_Od,_Ol);});}else{var _Om=__app2(_Oh,_Ok,B(_B0(E(_Oe[_Ol]))));if(_Ok!=_Og){var _On=B(_Oj(_Ok+1|0,_));return new T2(1,_kC,_On);}else{return _Bl;}}}}}},_Oo=B(_Oj(_Of+1|0,_)),_Op=__app0(E(_B4)),_Oq=B(_JU(_Oc,_));return new T(function(){return E(E(_Oq).b);});}else{var _Or=__app0(E(_B4)),_Os=B(_JU(_Oc,_));return new T(function(){return E(E(_Os).b);});}}}}else{var _Ot=__app0(E(_B4)),_Ou=B(_JU(_Oc,_));return new T(function(){return E(E(_Ou).b);});}},_Ov=function(_Ow,_){while(1){var _Ox=E(_Ow);if(!_Ox._){return _kC;}else{var _Oy=_Ox.b,_Oz=E(_Ox.a);switch(_Oz._){case 0:var _OA=B(A1(_Oz.a,_));_Ow=B(_n(_Oy,new T2(1,_OA,_w)));continue;case 1:_Ow=B(_n(_Oy,_Oz.a));continue;default:_Ow=_Oy;continue;}}}},_OB=function(_OC,_OD,_){var _OE=E(_OC);switch(_OE._){case 0:var _OF=B(A1(_OE.a,_));return new F(function(){return _Ov(B(_n(_OD,new T2(1,_OF,_w))),_);});break;case 1:return new F(function(){return _Ov(B(_n(_OD,_OE.a)),_);});break;default:return new F(function(){return _Ov(_OD,_);});}},_OG=new T0(2),_OH=function(_OI){return new T0(2);},_OJ=function(_OK,_OL,_OM){return function(_){var _ON=E(_OK),_OO=rMV(_ON),_OP=E(_OO);if(!_OP._){var _OQ=new T(function(){var _OR=new T(function(){return B(A1(_OM,_kC));});return B(_n(_OP.b,new T2(1,new T2(0,_OL,function(_OS){return E(_OR);}),_w)));}),_=wMV(_ON,new T2(0,_OP.a,_OQ));return _OG;}else{var _OT=E(_OP.a);if(!_OT._){var _=wMV(_ON,new T2(0,_OL,_w));return new T(function(){return B(A1(_OM,_kC));});}else{var _=wMV(_ON,new T1(1,_OT.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OM,_kC));}),new T2(1,new T(function(){return B(A2(_OT.a,_OL,_OH));}),_w)));}}};},_OU=new T(function(){return E(_qg);}),_OV=new T(function(){return eval("window.requestAnimationFrame");}),_OW=new T1(1,_w),_OX=function(_OY,_OZ){return function(_){var _P0=E(_OY),_P1=rMV(_P0),_P2=E(_P1);if(!_P2._){var _P3=_P2.a,_P4=E(_P2.b);if(!_P4._){var _=wMV(_P0,_OW);return new T(function(){return B(A1(_OZ,_P3));});}else{var _P5=E(_P4.a),_=wMV(_P0,new T2(0,_P5.a,_P4.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OZ,_P3));}),new T2(1,new T(function(){return B(A1(_P5.b,_OH));}),_w)));}}else{var _P6=new T(function(){var _P7=function(_P8){var _P9=new T(function(){return B(A1(_OZ,_P8));});return function(_Pa){return E(_P9);};};return B(_n(_P2.a,new T2(1,_P7,_w)));}),_=wMV(_P0,new T1(1,_P6));return _OG;}};},_Pb=function(_Pc,_Pd){return new T1(0,B(_OX(_Pc,_Pd)));},_Pe=function(_Pf,_Pg){var _Ph=new T(function(){return new T1(0,B(_OJ(_Pf,_kC,_OH)));});return function(_){var _Pi=__createJSFunc(2,function(_Pj,_){var _Pk=B(_OB(_Ph,_w,_));return _OU;}),_Pl=__app1(E(_OV),_Pi);return new T(function(){return B(_Pb(_Pf,_Pg));});};},_Pm=new T1(1,_w),_Pn=function(_Po,_Pp,_){var _Pq=function(_){var _Pr=nMV(_Po),_Ps=_Pr;return new T(function(){var _Pt=new T(function(){return B(_Pu(_));}),_Pv=function(_){var _Pw=rMV(_Ps),_Px=B(A2(_Pp,_Pw,_)),_=wMV(_Ps,_Px),_Py=function(_){var _Pz=nMV(_Pm);return new T(function(){return new T1(0,B(_Pe(_Pz,function(_PA){return E(_Pt);})));});};return new T1(0,_Py);},_PB=new T(function(){return new T1(0,_Pv);}),_Pu=function(_PC){return E(_PB);};return B(_Pu(_));});};return new F(function(){return _OB(new T1(0,_Pq),_w,_);});},_PD=new T(function(){return eval("__strict(setBounds)");}),_PE=function(_){var _PF=__app3(E(_20),E(_93),E(_id),E(_1Z)),_PG=__app2(E(_PD),E(_1u),E(_1n));return new F(function(){return _Pn(_AT,_O8,_);});},_PH=function(_){return new F(function(){return _PE(_);});};
var hasteMain = function() {B(A(_PH, [0]));};window.onload = hasteMain;