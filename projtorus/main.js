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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(",y:"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr(",z:"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("})"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=new T(function(){return B(unCStr("-("));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr(")"));}),_I=new T1(0,_H),_J=new T2(1,_I,_w),_K=new T(function(){return B(unCStr("."));}),_L=new T1(0,0),_M=function(_N){while(1){var _O=E(_N);if(!_O._){_N=new T1(1,I_fromInt(_O.a));continue;}else{return new F(function(){return I_toString(_O.a);});}}},_P=function(_Q,_R){return new F(function(){return _n(fromJSStr(B(_M(_Q))),_R);});},_S=function(_T,_U){var _V=E(_T);if(!_V._){var _W=_V.a,_X=E(_U);return (_X._==0)?_W<_X.a:I_compareInt(_X.a,_W)>0;}else{var _Y=_V.a,_Z=E(_U);return (_Z._==0)?I_compareInt(_Y,_Z.a)<0:I_compare(_Y,_Z.a)<0;}},_10=41,_11=40,_12=new T1(0,0),_13=function(_14,_15,_16){if(_14<=6){return new F(function(){return _P(_15,_16);});}else{if(!B(_S(_15,_12))){return new F(function(){return _P(_15,_16);});}else{return new T2(1,_11,new T(function(){return B(_n(fromJSStr(B(_M(_15))),new T2(1,_10,_16)));}));}}},_17=new T(function(){return B(_13(0,_L,_w));}),_18=new T(function(){return B(_n(_17,_K));}),_19=new T1(0,_18),_1a=new T2(1,_19,_J),_1b=new T2(1,_G,_1a),_1c=new T1(1,_1b),_1d=new T2(1,_1c,_E),_1e=new T2(1,_B,_1d),_1f=new T2(1,_1c,_1e),_1g=new T2(1,_z,_1f),_1h=new T2(1,_1c,_1g),_1i=new T(function(){return B(unCStr("({x:"));}),_1j=new T1(0,_1i),_1k=new T2(1,_1j,_1h),_1l=function(_1m){return E(_1m);},_1n=new T(function(){return toJSStr(B(_e(_x,_1l,_1k)));}),_1o=new T1(0,1),_1p=new T(function(){return B(_13(0,_1o,_w));}),_1q=new T(function(){return B(_n(_1p,_K));}),_1r=new T1(0,_1q),_1s=new T2(1,_1r,_J),_1t=new T2(1,_G,_1s),_1u=new T(function(){return toJSStr(B(_e(_x,_1l,_1t)));}),_1v=function(_1w,_1x,_1y){var _1z=E(_1y);if(!_1z._){return new F(function(){return A1(_1x,_1z.a);});}else{var _1A=new T(function(){return B(_0(_1w));}),_1B=new T(function(){return B(_2(_1w));}),_1C=function(_1D){var _1E=E(_1D);if(!_1E._){return E(_1B);}else{return new F(function(){return A2(_1A,new T(function(){return B(_1v(_1w,_1x,_1E.a));}),new T(function(){return B(_1C(_1E.b));}));});}};return new F(function(){return _1C(_1z.a);});}},_1F=function(_1G,_1H,_1I){var _1J=new T(function(){return B(_0(_1G));}),_1K=new T(function(){return B(_2(_1G));}),_1L=function(_1M){var _1N=E(_1M);if(!_1N._){return E(_1K);}else{return new F(function(){return A2(_1J,new T(function(){return B(_1v(_1G,_1H,_1N.a));}),new T(function(){return B(_1L(_1N.b));}));});}};return new F(function(){return _1L(_1I);});},_1O=new T(function(){return B(unCStr("-("));}),_1P=new T1(0,_1O),_1Q=new T(function(){return B(unCStr(")"));}),_1R=new T1(0,_1Q),_1S=new T2(1,_1R,_w),_1T=new T(function(){return B(unCStr("."));}),_1U=new T(function(){return B(_13(0,_1o,_w));}),_1V=new T(function(){return B(_n(_1U,_1T));}),_1W=new T1(0,_1V),_1X=new T2(1,_1W,_1S),_1Y=new T2(1,_1P,_1X),_1Z=new T(function(){return toJSStr(B(_1F(_x,_1l,_1Y)));}),_20=new T(function(){return eval("__strict(compile)");}),_21=new T(function(){return B(unCStr(","));}),_22=new T1(0,_21),_23=new T(function(){return B(unCStr("pow("));}),_24=new T1(0,_23),_25=function(_26,_27){return new T1(1,new T2(1,_24,new T2(1,_26,new T2(1,_22,new T2(1,_27,_1S)))));},_28=new T(function(){return B(unCStr("acos("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1S)));},_2c=new T(function(){return B(unCStr("acosh("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1S)));},_2g=new T(function(){return B(unCStr("asin("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1S)));},_2k=new T(function(){return B(unCStr("asinh("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1S)));},_2o=new T(function(){return B(unCStr("atan("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1S)));},_2s=new T(function(){return B(unCStr("atanh("));}),_2t=new T1(0,_2s),_2u=function(_2v){return new T1(1,new T2(1,_2t,new T2(1,_2v,_1S)));},_2w=new T(function(){return B(unCStr("cos("));}),_2x=new T1(0,_2w),_2y=function(_2z){return new T1(1,new T2(1,_2x,new T2(1,_2z,_1S)));},_2A=new T(function(){return B(unCStr("cosh("));}),_2B=new T1(0,_2A),_2C=function(_2D){return new T1(1,new T2(1,_2B,new T2(1,_2D,_1S)));},_2E=new T(function(){return B(unCStr("exp("));}),_2F=new T1(0,_2E),_2G=function(_2H){return new T1(1,new T2(1,_2F,new T2(1,_2H,_1S)));},_2I=new T(function(){return B(unCStr("log("));}),_2J=new T1(0,_2I),_2K=function(_2L){return new T1(1,new T2(1,_2J,new T2(1,_2L,_1S)));},_2M=new T(function(){return B(unCStr(")/log("));}),_2N=new T1(0,_2M),_2O=function(_2P,_2Q){return new T1(1,new T2(1,_2J,new T2(1,_2Q,new T2(1,_2N,new T2(1,_2P,_1S)))));},_2R=new T(function(){return B(unCStr("pi"));}),_2S=new T1(0,_2R),_2T=new T(function(){return B(unCStr("sin("));}),_2U=new T1(0,_2T),_2V=function(_2W){return new T1(1,new T2(1,_2U,new T2(1,_2W,_1S)));},_2X=new T(function(){return B(unCStr("sinh("));}),_2Y=new T1(0,_2X),_2Z=function(_30){return new T1(1,new T2(1,_2Y,new T2(1,_30,_1S)));},_31=new T(function(){return B(unCStr("sqrt("));}),_32=new T1(0,_31),_33=function(_34){return new T1(1,new T2(1,_32,new T2(1,_34,_1S)));},_35=new T(function(){return B(unCStr("tan("));}),_36=new T1(0,_35),_37=function(_38){return new T1(1,new T2(1,_36,new T2(1,_38,_1S)));},_39=new T(function(){return B(unCStr("tanh("));}),_3a=new T1(0,_39),_3b=function(_3c){return new T1(1,new T2(1,_3a,new T2(1,_3c,_1S)));},_3d=new T(function(){return B(unCStr("("));}),_3e=new T1(0,_3d),_3f=new T(function(){return B(unCStr(")/("));}),_3g=new T1(0,_3f),_3h=function(_3i,_3j){return new T1(1,new T2(1,_3e,new T2(1,_3i,new T2(1,_3g,new T2(1,_3j,_1S)))));},_3k=new T1(0,1),_3l=function(_3m,_3n){var _3o=E(_3m);if(!_3o._){var _3p=_3o.a,_3q=E(_3n);if(!_3q._){var _3r=_3q.a;return (_3p!=_3r)?(_3p>_3r)?2:0:1;}else{var _3s=I_compareInt(_3q.a,_3p);return (_3s<=0)?(_3s>=0)?1:2:0;}}else{var _3t=_3o.a,_3u=E(_3n);if(!_3u._){var _3v=I_compareInt(_3t,_3u.a);return (_3v>=0)?(_3v<=0)?1:2:0;}else{var _3w=I_compare(_3t,_3u.a);return (_3w>=0)?(_3w<=0)?1:2:0;}}},_3x=new T(function(){return B(unCStr("base"));}),_3y=new T(function(){return B(unCStr("GHC.Exception"));}),_3z=new T(function(){return B(unCStr("ArithException"));}),_3A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3x,_3y,_3z),_3B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3A,_w,_w),_3C=function(_3D){return E(_3B);},_3E=function(_3F){return E(E(_3F).a);},_3G=function(_3H,_3I,_3J){var _3K=B(A1(_3H,_)),_3L=B(A1(_3I,_)),_3M=hs_eqWord64(_3K.a,_3L.a);if(!_3M){return __Z;}else{var _3N=hs_eqWord64(_3K.b,_3L.b);return (!_3N)?__Z:new T1(1,_3J);}},_3O=function(_3P){var _3Q=E(_3P);return new F(function(){return _3G(B(_3E(_3Q.a)),_3C,_3Q.b);});},_3R=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3S=new T(function(){return B(unCStr("denormal"));}),_3T=new T(function(){return B(unCStr("divide by zero"));}),_3U=new T(function(){return B(unCStr("loss of precision"));}),_3V=new T(function(){return B(unCStr("arithmetic underflow"));}),_3W=new T(function(){return B(unCStr("arithmetic overflow"));}),_3X=function(_3Y,_3Z){switch(E(_3Y)){case 0:return new F(function(){return _n(_3W,_3Z);});break;case 1:return new F(function(){return _n(_3V,_3Z);});break;case 2:return new F(function(){return _n(_3U,_3Z);});break;case 3:return new F(function(){return _n(_3T,_3Z);});break;case 4:return new F(function(){return _n(_3S,_3Z);});break;default:return new F(function(){return _n(_3R,_3Z);});}},_40=function(_41){return new F(function(){return _3X(_41,_w);});},_42=function(_43,_44,_45){return new F(function(){return _3X(_44,_45);});},_46=44,_47=93,_48=91,_49=function(_4a,_4b,_4c){var _4d=E(_4b);if(!_4d._){return new F(function(){return unAppCStr("[]",_4c);});}else{var _4e=new T(function(){var _4f=new T(function(){var _4g=function(_4h){var _4i=E(_4h);if(!_4i._){return E(new T2(1,_47,_4c));}else{var _4j=new T(function(){return B(A2(_4a,_4i.a,new T(function(){return B(_4g(_4i.b));})));});return new T2(1,_46,_4j);}};return B(_4g(_4d.b));});return B(A2(_4a,_4d.a,_4f));});return new T2(1,_48,_4e);}},_4k=function(_4l,_4m){return new F(function(){return _49(_3X,_4l,_4m);});},_4n=new T3(0,_42,_40,_4k),_4o=new T(function(){return new T5(0,_3C,_4n,_4p,_3O,_40);}),_4p=function(_4q){return new T2(0,_4o,_4q);},_4r=3,_4s=new T(function(){return B(_4p(_4r));}),_4t=new T(function(){return die(_4s);}),_4u=function(_4v,_4w){var _4x=E(_4v);return (_4x._==0)?_4x.a*Math.pow(2,_4w):I_toNumber(_4x.a)*Math.pow(2,_4w);},_4y=function(_4z,_4A){var _4B=E(_4z);if(!_4B._){var _4C=_4B.a,_4D=E(_4A);return (_4D._==0)?_4C==_4D.a:(I_compareInt(_4D.a,_4C)==0)?true:false;}else{var _4E=_4B.a,_4F=E(_4A);return (_4F._==0)?(I_compareInt(_4E,_4F.a)==0)?true:false:(I_compare(_4E,_4F.a)==0)?true:false;}},_4G=function(_4H){var _4I=E(_4H);if(!_4I._){return E(_4I.a);}else{return new F(function(){return I_toInt(_4I.a);});}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a,_4Q=addC(_4N,_4P);if(!E(_4Q.b)){return new T1(0,_4Q.a);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R._){_4K=_4M;_4L=new T1(1,I_fromInt(_4R.a));continue;}else{return new T1(1,I_add(_4M.a,_4R.a));}}}},_4S=function(_4T,_4U){while(1){var _4V=E(_4T);if(!_4V._){var _4W=E(_4V.a);if(_4W==(-2147483648)){_4T=new T1(1,I_fromInt(-2147483648));continue;}else{var _4X=E(_4U);if(!_4X._){var _4Y=_4X.a;return new T2(0,new T1(0,quot(_4W,_4Y)),new T1(0,_4W%_4Y));}else{_4T=new T1(1,I_fromInt(_4W));_4U=_4X;continue;}}}else{var _4Z=E(_4U);if(!_4Z._){_4T=_4V;_4U=new T1(1,I_fromInt(_4Z.a));continue;}else{var _50=I_quotRem(_4V.a,_4Z.a);return new T2(0,new T1(1,_50.a),new T1(1,_50.b));}}}},_51=new T1(0,0),_52=function(_53,_54){while(1){var _55=E(_53);if(!_55._){_53=new T1(1,I_fromInt(_55.a));continue;}else{return new T1(1,I_shiftLeft(_55.a,_54));}}},_56=function(_57,_58,_59){if(!B(_4y(_59,_51))){var _5a=B(_4S(_58,_59)),_5b=_5a.a;switch(B(_3l(B(_52(_5a.b,1)),_59))){case 0:return new F(function(){return _4u(_5b,_57);});break;case 1:if(!(B(_4G(_5b))&1)){return new F(function(){return _4u(_5b,_57);});}else{return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}break;default:return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}}else{return E(_4t);}},_5c=function(_5d,_5e){var _5f=E(_5d);if(!_5f._){var _5g=_5f.a,_5h=E(_5e);return (_5h._==0)?_5g>_5h.a:I_compareInt(_5h.a,_5g)<0;}else{var _5i=_5f.a,_5j=E(_5e);return (_5j._==0)?I_compareInt(_5i,_5j.a)>0:I_compare(_5i,_5j.a)>0;}},_5k=new T1(0,1),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5n=new T(function(){return B(unCStr("PatternMatchFail"));}),_5o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5l,_5m,_5n),_5p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5o,_w,_w),_5q=function(_5r){return E(_5p);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _3G(B(_3E(_5u.a)),_5q,_5u.b);});},_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return new T2(0,_5z,_5y);},_5A=function(_5B,_5C){return new F(function(){return _n(E(_5B).a,_5C);});},_5D=function(_5E,_5F){return new F(function(){return _49(_5A,_5E,_5F);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _n(E(_5I).a,_5J);});},_5K=new T3(0,_5G,_5v,_5D),_5z=new T(function(){return new T5(0,_5q,_5K,_5x,_5s,_5v);}),_5L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5M=function(_5N){return E(E(_5N).c);},_5O=function(_5P,_5Q){return new F(function(){return die(new T(function(){return B(A2(_5M,_5Q,_5P));}));});},_5R=function(_5S,_4q){return new F(function(){return _5O(_5S,_4q);});},_5T=function(_5U,_5V){var _5W=E(_5V);if(!_5W._){return new T2(0,_w,_w);}else{var _5X=_5W.a;if(!B(A1(_5U,_5X))){return new T2(0,_w,_5W);}else{var _5Y=new T(function(){var _5Z=B(_5T(_5U,_5W.b));return new T2(0,_5Z.a,_5Z.b);});return new T2(0,new T2(1,_5X,new T(function(){return E(E(_5Y).a);})),new T(function(){return E(E(_5Y).b);}));}}},_60=32,_61=new T(function(){return B(unCStr("\n"));}),_62=function(_63){return (E(_63)==124)?false:true;},_64=function(_65,_66){var _67=B(_5T(_62,B(unCStr(_65)))),_68=_67.a,_69=function(_6a,_6b){var _6c=new T(function(){var _6d=new T(function(){return B(_n(_66,new T(function(){return B(_n(_6b,_61));},1)));});return B(unAppCStr(": ",_6d));},1);return new F(function(){return _n(_6a,_6c);});},_6e=E(_67.b);if(!_6e._){return new F(function(){return _69(_68,_w);});}else{if(E(_6e.a)==124){return new F(function(){return _69(_68,new T2(1,_60,_6e.b));});}else{return new F(function(){return _69(_68,_w);});}}},_6f=function(_6g){return new F(function(){return _5R(new T1(0,new T(function(){return B(_64(_6g,_5L));})),_5z);});},_6h=function(_6i){var _6j=function(_6k,_6l){while(1){if(!B(_S(_6k,_6i))){if(!B(_5c(_6k,_6i))){if(!B(_4y(_6k,_6i))){return new F(function(){return _6f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_6l);}}else{return _6l-1|0;}}else{var _6m=B(_52(_6k,1)),_6n=_6l+1|0;_6k=_6m;_6l=_6n;continue;}}};return new F(function(){return _6j(_5k,0);});},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){var _6r=_6q.a>>>0;if(!_6r){return -1;}else{var _6s=function(_6t,_6u){while(1){if(_6t>=_6r){if(_6t<=_6r){if(_6t!=_6r){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6u);}}else{return _6u-1|0;}}else{var _6v=imul(_6t,2)>>>0,_6w=_6u+1|0;_6t=_6v;_6u=_6w;continue;}}};return new F(function(){return _6s(1,0);});}}else{return new F(function(){return _6h(_6q);});}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){var _6A=_6z.a>>>0;if(!_6A){return new T2(0,-1,0);}else{var _6B=function(_6C,_6D){while(1){if(_6C>=_6A){if(_6C<=_6A){if(_6C!=_6A){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6D);}}else{return _6D-1|0;}}else{var _6E=imul(_6C,2)>>>0,_6F=_6D+1|0;_6C=_6E;_6D=_6F;continue;}}};return new T2(0,B(_6B(1,0)),(_6A&_6A-1>>>0)>>>0&4294967295);}}else{var _6G=_6z.a;return new T2(0,B(_6o(_6z)),I_compareInt(I_and(_6G,I_sub(_6G,I_fromInt(1))),0));}},_6H=function(_6I,_6J){var _6K=E(_6I);if(!_6K._){var _6L=_6K.a,_6M=E(_6J);return (_6M._==0)?_6L<=_6M.a:I_compareInt(_6M.a,_6L)>=0;}else{var _6N=_6K.a,_6O=E(_6J);return (_6O._==0)?I_compareInt(_6N,_6O.a)<=0:I_compare(_6N,_6O.a)<=0;}},_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){var _6T=_6S.a,_6U=E(_6R);if(!_6U._){return new T1(0,(_6T>>>0&_6U.a>>>0)>>>0&4294967295);}else{_6Q=new T1(1,I_fromInt(_6T));_6R=_6U;continue;}}else{var _6V=E(_6R);if(!_6V._){_6Q=_6S;_6R=new T1(1,I_fromInt(_6V.a));continue;}else{return new T1(1,I_and(_6S.a,_6V.a));}}}},_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){var _70=_6Z.a,_71=E(_6Y);if(!_71._){var _72=_71.a,_73=subC(_70,_72);if(!E(_73.b)){return new T1(0,_73.a);}else{_6X=new T1(1,I_fromInt(_70));_6Y=new T1(1,I_fromInt(_72));continue;}}else{_6X=new T1(1,I_fromInt(_70));_6Y=_71;continue;}}else{var _74=E(_6Y);if(!_74._){_6X=_6Z;_6Y=new T1(1,I_fromInt(_74.a));continue;}else{return new T1(1,I_sub(_6Z.a,_74.a));}}}},_75=new T1(0,2),_76=function(_77,_78){var _79=E(_77);if(!_79._){var _7a=(_79.a>>>0&(2<<_78>>>0)-1>>>0)>>>0,_7b=1<<_78>>>0;return (_7b<=_7a)?(_7b>=_7a)?1:2:0;}else{var _7c=B(_6P(_79,B(_6W(B(_52(_75,_78)),_5k)))),_7d=B(_52(_5k,_78));return (!B(_5c(_7d,_7c)))?(!B(_S(_7d,_7c)))?1:2:0;}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){_7f=new T1(1,I_fromInt(_7h.a));continue;}else{return new T1(1,I_shiftRight(_7h.a,_7g));}}},_7i=function(_7j,_7k,_7l,_7m){var _7n=B(_6x(_7m)),_7o=_7n.a;if(!E(_7n.b)){var _7p=B(_6o(_7l));if(_7p<((_7o+_7j|0)-1|0)){var _7q=_7o+(_7j-_7k|0)|0;if(_7q>0){if(_7q>_7p){if(_7q<=(_7p+1|0)){if(!E(B(_6x(_7l)).b)){return 0;}else{return new F(function(){return _4u(_3k,_7j-_7k|0);});}}else{return 0;}}else{var _7r=B(_7e(_7l,_7q));switch(B(_76(_7l,_7q-1|0))){case 0:return new F(function(){return _4u(_7r,_7j-_7k|0);});break;case 1:if(!(B(_4G(_7r))&1)){return new F(function(){return _4u(_7r,_7j-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}break;default:return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}}}else{return new F(function(){return _4u(_7l,(_7j-_7k|0)-_7q|0);});}}else{if(_7p>=_7k){var _7s=B(_7e(_7l,(_7p+1|0)-_7k|0));switch(B(_76(_7l,_7p-_7k|0))){case 0:return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});break;case 2:return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});break;default:if(!(B(_4G(_7s))&1)){return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});}}}else{return new F(function(){return _4u(_7l, -_7o);});}}}else{var _7t=B(_6o(_7l))-_7o|0,_7u=function(_7v){var _7w=function(_7x,_7y){if(!B(_6H(B(_52(_7y,_7k)),_7x))){return new F(function(){return _56(_7v-_7k|0,_7x,_7y);});}else{return new F(function(){return _56((_7v-_7k|0)+1|0,_7x,B(_52(_7y,1)));});}};if(_7v>=_7k){if(_7v!=_7k){return new F(function(){return _7w(_7l,new T(function(){return B(_52(_7m,_7v-_7k|0));}));});}else{return new F(function(){return _7w(_7l,_7m);});}}else{return new F(function(){return _7w(new T(function(){return B(_52(_7l,_7k-_7v|0));}),_7m);});}};if(_7j>_7t){return new F(function(){return _7u(_7j);});}else{return new F(function(){return _7u(_7t);});}}},_7z=new T1(0,2147483647),_7A=new T(function(){return B(_4J(_7z,_5k));}),_7B=function(_7C){var _7D=E(_7C);if(!_7D._){var _7E=E(_7D.a);return (_7E==(-2147483648))?E(_7A):new T1(0, -_7E);}else{return new T1(1,I_negate(_7D.a));}},_7F=new T(function(){return 0/0;}),_7G=new T(function(){return -1/0;}),_7H=new T(function(){return 1/0;}),_7I=0,_7J=function(_7K,_7L){if(!B(_4y(_7L,_51))){if(!B(_4y(_7K,_51))){if(!B(_S(_7K,_51))){return new F(function(){return _7i(-1021,53,_7K,_7L);});}else{return  -B(_7i(-1021,53,B(_7B(_7K)),_7L));}}else{return E(_7I);}}else{return (!B(_4y(_7K,_51)))?(!B(_S(_7K,_51)))?E(_7H):E(_7G):E(_7F);}},_7M=function(_7N){return new T1(0,new T(function(){var _7O=E(_7N),_7P=jsShow(B(_7J(_7O.a,_7O.b)));return fromJSStr(_7P);}));},_7Q=new T(function(){return B(unCStr("1./("));}),_7R=new T1(0,_7Q),_7S=function(_7T){return new T1(1,new T2(1,_7R,new T2(1,_7T,_1S)));},_7U=new T(function(){return B(unCStr(")+("));}),_7V=new T1(0,_7U),_7W=function(_7X,_7Y){return new T1(1,new T2(1,_3e,new T2(1,_7X,new T2(1,_7V,new T2(1,_7Y,_1S)))));},_7Z=function(_80){return new T1(1,new T2(1,_1P,new T2(1,_80,_1S)));},_81=new T(function(){return B(unCStr(")*("));}),_82=new T1(0,_81),_83=function(_84,_85){return new T1(1,new T2(1,_3e,new T2(1,_84,new T2(1,_82,new T2(1,_85,_1S)))));},_86=function(_87){return E(E(_87).a);},_88=function(_89){return E(E(_89).d);},_8a=function(_8b,_8c){return new F(function(){return A3(_86,_8d,_8b,new T(function(){return B(A2(_88,_8d,_8c));}));});},_8e=new T(function(){return B(unCStr("abs("));}),_8f=new T1(0,_8e),_8g=function(_8h){return new T1(1,new T2(1,_8f,new T2(1,_8h,_1S)));},_8i=function(_8j){return new T1(0,new T(function(){return B(_n(B(_13(0,_8j,_w)),_1T));}));},_8k=new T(function(){return B(unCStr("sign("));}),_8l=new T1(0,_8k),_8m=function(_8n){return new T1(1,new T2(1,_8l,new T2(1,_8n,_1S)));},_8d=new T(function(){return {_:0,a:_7W,b:_8a,c:_83,d:_7Z,e:_8g,f:_8m,g:_8i};}),_8o=new T4(0,_8d,_3h,_7S,_7M),_8p={_:0,a:_8o,b:_2S,c:_2G,d:_2K,e:_33,f:_25,g:_2O,h:_2V,i:_2y,j:_37,k:_2i,l:_2a,m:_2q,n:_2Z,o:_2C,p:_3b,q:_2m,r:_2e,s:_2u},_8q=function(_8r){return E(E(_8r).a);},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v){return E(E(_8v).c);},_8w=function(_8x){return E(E(_8x).b);},_8y=function(_8z){return E(E(_8z).d);},_8A=new T1(0,2),_8B=new T2(0,E(_1o),E(_8A)),_8C=new T1(0,5),_8D=new T1(0,4),_8E=new T2(0,E(_8D),E(_8C)),_8F=function(_8G){return E(E(_8G).e);},_8H=function(_8I,_8J,_8K,_8L){var _8M=B(_8q(_8I)),_8N=B(_8s(_8M)),_8O=new T(function(){var _8P=new T(function(){var _8Q=new T(function(){var _8R=new T(function(){var _8S=new T(function(){var _8T=new T(function(){return B(A3(_86,_8N,new T(function(){return B(A3(_8u,_8N,_8J,_8J));}),new T(function(){return B(A3(_8u,_8N,_8L,_8L));})));});return B(A2(_8F,_8I,_8T));});return B(A3(_8w,_8N,_8S,new T(function(){return B(A2(_8y,_8M,_8E));})));});return B(A3(_8u,_8N,_8R,_8R));});return B(A3(_86,_8N,_8Q,new T(function(){return B(A3(_8u,_8N,_8K,_8K));})));});return B(A2(_8F,_8I,_8P));});return new F(function(){return A3(_8w,_8N,_8O,new T(function(){return B(A2(_8y,_8M,_8B));}));});},_8U=new T(function(){return B(unCStr("x"));}),_8V=new T1(0,_8U),_8W=new T(function(){return B(unCStr("y"));}),_8X=new T1(0,_8W),_8Y=new T(function(){return B(unCStr("z"));}),_8Z=new T1(0,_8Y),_90=new T(function(){return B(_8H(_8p,_8V,_8X,_8Z));}),_91=new T(function(){return toJSStr(B(_1v(_x,_1l,_90)));}),_92=new T3(0,E(_8V),E(_8X),E(_8Z)),_93=new T(function(){return B(unCStr("(/=) is not defined"));}),_94=new T(function(){return B(err(_93));}),_95=new T(function(){return B(unCStr("(==) is not defined"));}),_96=new T(function(){return B(err(_95));}),_97=new T2(0,_96,_94),_98=new T(function(){return B(unCStr("(<) is not defined"));}),_99=new T(function(){return B(err(_98));}),_9a=new T(function(){return B(unCStr("(<=) is not defined"));}),_9b=new T(function(){return B(err(_9a));}),_9c=new T(function(){return B(unCStr("(>) is not defined"));}),_9d=new T(function(){return B(err(_9c));}),_9e=new T(function(){return B(unCStr("(>=) is not defined"));}),_9f=new T(function(){return B(err(_9e));}),_9g=new T(function(){return B(unCStr("compare is not defined"));}),_9h=new T(function(){return B(err(_9g));}),_9i=new T(function(){return B(unCStr("max("));}),_9j=new T1(0,_9i),_9k=function(_9l,_9m){return new T1(1,new T2(1,_9j,new T2(1,_9l,new T2(1,_22,new T2(1,_9m,_1S)))));},_9n=new T(function(){return B(unCStr("min("));}),_9o=new T1(0,_9n),_9p=function(_9q,_9r){return new T1(1,new T2(1,_9o,new T2(1,_9q,new T2(1,_22,new T2(1,_9r,_1S)))));},_9s={_:0,a:_97,b:_9h,c:_99,d:_9b,e:_9d,f:_9f,g:_9k,h:_9p},_9t=new T2(0,_8p,_9s),_9u=function(_9v,_9w){var _9x=E(_9v);return E(_9w);},_9y=function(_9z,_9A){var _9B=E(_9A);return E(_9z);},_9C=function(_9D,_9E){var _9F=E(_9D),_9G=E(_9E);return new T3(0,E(B(A1(_9F.a,_9G.a))),E(B(A1(_9F.b,_9G.b))),E(B(A1(_9F.c,_9G.c))));},_9H=function(_9I,_9J,_9K){return new T3(0,E(_9I),E(_9J),E(_9K));},_9L=function(_9M){return new F(function(){return _9H(_9M,_9M,_9M);});},_9N=function(_9O,_9P){var _9Q=E(_9P),_9R=E(_9O);return new T3(0,E(_9R),E(_9R),E(_9R));},_9S=function(_9T,_9U){var _9V=E(_9U);return new T3(0,E(B(A1(_9T,_9V.a))),E(B(A1(_9T,_9V.b))),E(B(A1(_9T,_9V.c))));},_9W=new T2(0,_9S,_9N),_9X=new T5(0,_9W,_9L,_9C,_9u,_9y),_9Y=new T1(0,0),_9Z=function(_a0){return E(E(_a0).g);},_a1=function(_a2){var _a3=B(A2(_9Z,_a2,_1o)),_a4=B(A2(_9Z,_a2,_9Y));return new T3(0,E(new T3(0,E(_a3),E(_a4),E(_a4))),E(new T3(0,E(_a4),E(_a3),E(_a4))),E(new T3(0,E(_a4),E(_a4),E(_a3))));},_a5=function(_a6){return E(E(_a6).a);},_a7=function(_a8){return E(E(_a8).f);},_a9=function(_aa){return E(E(_aa).b);},_ab=function(_ac){return E(E(_ac).c);},_ad=function(_ae){return E(E(_ae).a);},_af=function(_ag){return E(E(_ag).d);},_ah=function(_ai,_aj,_ak,_al,_am){var _an=new T(function(){return E(E(E(_ai).c).a);}),_ao=new T(function(){var _ap=E(_ai).a,_aq=new T(function(){var _ar=new T(function(){return B(_8q(_an));}),_as=new T(function(){return B(_8s(_ar));}),_at=new T(function(){return B(A2(_af,_an,_aj));}),_au=new T(function(){return B(A3(_a7,_an,_aj,_al));}),_av=function(_aw,_ax){var _ay=new T(function(){var _az=new T(function(){return B(A3(_a9,_ar,new T(function(){return B(A3(_8u,_as,_al,_aw));}),_aj));});return B(A3(_86,_as,_az,new T(function(){return B(A3(_8u,_as,_ax,_at));})));});return new F(function(){return A3(_8u,_as,_au,_ay);});};return B(A3(_ad,B(_a5(_ap)),_av,_ak));});return B(A3(_ab,_ap,_aq,_am));});return new T2(0,new T(function(){return B(A3(_a7,_an,_aj,_al));}),_ao);},_aA=function(_aB,_aC,_aD,_aE){var _aF=E(_aD),_aG=E(_aE),_aH=B(_ah(_aC,_aF.a,_aF.b,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=new T1(0,1),_aJ=function(_aK){return E(E(_aK).l);},_aL=function(_aM,_aN,_aO){var _aP=new T(function(){return E(E(E(_aM).c).a);}),_aQ=new T(function(){var _aR=new T(function(){return B(_8q(_aP));}),_aS=new T(function(){var _aT=B(_8s(_aR)),_aU=new T(function(){var _aV=new T(function(){return B(A3(_8w,_aT,new T(function(){return B(A2(_9Z,_aT,_aI));}),new T(function(){return B(A3(_8u,_aT,_aN,_aN));})));});return B(A2(_8F,_aP,_aV));});return B(A2(_88,_aT,_aU));});return B(A3(_ad,B(_a5(E(_aM).a)),function(_aW){return new F(function(){return A3(_a9,_aR,_aW,_aS);});},_aO));});return new T2(0,new T(function(){return B(A2(_aJ,_aP,_aN));}),_aQ);},_aX=function(_aY,_aZ,_b0){var _b1=E(_b0),_b2=B(_aL(_aZ,_b1.a,_b1.b));return new T2(0,_b2.a,_b2.b);},_b3=function(_b4){return E(E(_b4).r);},_b5=function(_b6,_b7,_b8){var _b9=new T(function(){return E(E(E(_b6).c).a);}),_ba=new T(function(){var _bb=new T(function(){return B(_8q(_b9));}),_bc=new T(function(){var _bd=new T(function(){var _be=B(_8s(_bb));return B(A3(_8w,_be,new T(function(){return B(A3(_8u,_be,_b7,_b7));}),new T(function(){return B(A2(_9Z,_be,_aI));})));});return B(A2(_8F,_b9,_bd));});return B(A3(_ad,B(_a5(E(_b6).a)),function(_bf){return new F(function(){return A3(_a9,_bb,_bf,_bc);});},_b8));});return new T2(0,new T(function(){return B(A2(_b3,_b9,_b7));}),_ba);},_bg=function(_bh,_bi,_bj){var _bk=E(_bj),_bl=B(_b5(_bi,_bk.a,_bk.b));return new T2(0,_bl.a,_bl.b);},_bm=function(_bn){return E(E(_bn).k);},_bo=function(_bp,_bq,_br){var _bs=new T(function(){return E(E(E(_bp).c).a);}),_bt=new T(function(){var _bu=new T(function(){return B(_8q(_bs));}),_bv=new T(function(){var _bw=new T(function(){var _bx=B(_8s(_bu));return B(A3(_8w,_bx,new T(function(){return B(A2(_9Z,_bx,_aI));}),new T(function(){return B(A3(_8u,_bx,_bq,_bq));})));});return B(A2(_8F,_bs,_bw));});return B(A3(_ad,B(_a5(E(_bp).a)),function(_by){return new F(function(){return A3(_a9,_bu,_by,_bv);});},_br));});return new T2(0,new T(function(){return B(A2(_bm,_bs,_bq));}),_bt);},_bz=function(_bA,_bB,_bC){var _bD=E(_bC),_bE=B(_bo(_bB,_bD.a,_bD.b));return new T2(0,_bE.a,_bE.b);},_bF=function(_bG){return E(E(_bG).q);},_bH=function(_bI,_bJ,_bK){var _bL=new T(function(){return E(E(E(_bI).c).a);}),_bM=new T(function(){var _bN=new T(function(){return B(_8q(_bL));}),_bO=new T(function(){var _bP=new T(function(){var _bQ=B(_8s(_bN));return B(A3(_86,_bQ,new T(function(){return B(A3(_8u,_bQ,_bJ,_bJ));}),new T(function(){return B(A2(_9Z,_bQ,_aI));})));});return B(A2(_8F,_bL,_bP));});return B(A3(_ad,B(_a5(E(_bI).a)),function(_bR){return new F(function(){return A3(_a9,_bN,_bR,_bO);});},_bK));});return new T2(0,new T(function(){return B(A2(_bF,_bL,_bJ));}),_bM);},_bS=function(_bT,_bU,_bV){var _bW=E(_bV),_bX=B(_bH(_bU,_bW.a,_bW.b));return new T2(0,_bX.a,_bX.b);},_bY=function(_bZ){return E(E(_bZ).m);},_c0=function(_c1,_c2,_c3){var _c4=new T(function(){return E(E(E(_c1).c).a);}),_c5=new T(function(){var _c6=new T(function(){return B(_8q(_c4));}),_c7=new T(function(){var _c8=B(_8s(_c6));return B(A3(_86,_c8,new T(function(){return B(A2(_9Z,_c8,_aI));}),new T(function(){return B(A3(_8u,_c8,_c2,_c2));})));});return B(A3(_ad,B(_a5(E(_c1).a)),function(_c9){return new F(function(){return A3(_a9,_c6,_c9,_c7);});},_c3));});return new T2(0,new T(function(){return B(A2(_bY,_c4,_c2));}),_c5);},_ca=function(_cb,_cc,_cd){var _ce=E(_cd),_cf=B(_c0(_cc,_ce.a,_ce.b));return new T2(0,_cf.a,_cf.b);},_cg=function(_ch){return E(E(_ch).s);},_ci=function(_cj,_ck,_cl){var _cm=new T(function(){return E(E(E(_cj).c).a);}),_cn=new T(function(){var _co=new T(function(){return B(_8q(_cm));}),_cp=new T(function(){var _cq=B(_8s(_co));return B(A3(_8w,_cq,new T(function(){return B(A2(_9Z,_cq,_aI));}),new T(function(){return B(A3(_8u,_cq,_ck,_ck));})));});return B(A3(_ad,B(_a5(E(_cj).a)),function(_cr){return new F(function(){return A3(_a9,_co,_cr,_cp);});},_cl));});return new T2(0,new T(function(){return B(A2(_cg,_cm,_ck));}),_cn);},_cs=function(_ct,_cu,_cv){var _cw=E(_cv),_cx=B(_ci(_cu,_cw.a,_cw.b));return new T2(0,_cx.a,_cx.b);},_cy=function(_cz){return E(E(_cz).i);},_cA=function(_cB){return E(E(_cB).h);},_cC=function(_cD,_cE,_cF){var _cG=new T(function(){return E(E(E(_cD).c).a);}),_cH=new T(function(){var _cI=new T(function(){return B(_8s(new T(function(){return B(_8q(_cG));})));}),_cJ=new T(function(){return B(A2(_88,_cI,new T(function(){return B(A2(_cA,_cG,_cE));})));});return B(A3(_ad,B(_a5(E(_cD).a)),function(_cK){return new F(function(){return A3(_8u,_cI,_cK,_cJ);});},_cF));});return new T2(0,new T(function(){return B(A2(_cy,_cG,_cE));}),_cH);},_cL=function(_cM,_cN,_cO){var _cP=E(_cO),_cQ=B(_cC(_cN,_cP.a,_cP.b));return new T2(0,_cQ.a,_cQ.b);},_cR=function(_cS){return E(E(_cS).o);},_cT=function(_cU){return E(E(_cU).n);},_cV=function(_cW,_cX,_cY){var _cZ=new T(function(){return E(E(E(_cW).c).a);}),_d0=new T(function(){var _d1=new T(function(){return B(_8s(new T(function(){return B(_8q(_cZ));})));}),_d2=new T(function(){return B(A2(_cT,_cZ,_cX));});return B(A3(_ad,B(_a5(E(_cW).a)),function(_d3){return new F(function(){return A3(_8u,_d1,_d3,_d2);});},_cY));});return new T2(0,new T(function(){return B(A2(_cR,_cZ,_cX));}),_d0);},_d4=function(_d5,_d6,_d7){var _d8=E(_d7),_d9=B(_cV(_d6,_d8.a,_d8.b));return new T2(0,_d9.a,_d9.b);},_da=function(_db){return E(E(_db).c);},_dc=function(_dd,_de,_df){var _dg=new T(function(){return E(E(E(_dd).c).a);}),_dh=new T(function(){var _di=new T(function(){return B(_8s(new T(function(){return B(_8q(_dg));})));}),_dj=new T(function(){return B(A2(_da,_dg,_de));});return B(A3(_ad,B(_a5(E(_dd).a)),function(_dk){return new F(function(){return A3(_8u,_di,_dk,_dj);});},_df));});return new T2(0,new T(function(){return B(A2(_da,_dg,_de));}),_dh);},_dl=function(_dm,_dn,_do){var _dp=E(_do),_dq=B(_dc(_dn,_dp.a,_dp.b));return new T2(0,_dq.a,_dq.b);},_dr=function(_ds,_dt,_du){var _dv=new T(function(){return E(E(E(_ds).c).a);}),_dw=new T(function(){var _dx=new T(function(){return B(_8q(_dv));}),_dy=new T(function(){return B(_8s(_dx));}),_dz=new T(function(){return B(A3(_a9,_dx,new T(function(){return B(A2(_9Z,_dy,_aI));}),_dt));});return B(A3(_ad,B(_a5(E(_ds).a)),function(_dA){return new F(function(){return A3(_8u,_dy,_dA,_dz);});},_du));});return new T2(0,new T(function(){return B(A2(_af,_dv,_dt));}),_dw);},_dB=function(_dC,_dD,_dE){var _dF=E(_dE),_dG=B(_dr(_dD,_dF.a,_dF.b));return new T2(0,_dG.a,_dG.b);},_dH=function(_dI,_dJ,_dK,_dL){var _dM=new T(function(){return E(E(_dJ).c);}),_dN=new T3(0,new T(function(){return E(E(_dJ).a);}),new T(function(){return E(E(_dJ).b);}),new T2(0,new T(function(){return E(E(_dM).a);}),new T(function(){return E(E(_dM).b);})));return new F(function(){return A3(_a9,_dI,new T(function(){var _dO=E(_dL),_dP=B(_dr(_dN,_dO.a,_dO.b));return new T2(0,_dP.a,_dP.b);}),new T(function(){var _dQ=E(_dK),_dR=B(_dr(_dN,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);}));});},_dS=function(_dT){return E(E(_dT).b);},_dU=function(_dV){return E(E(_dV).b);},_dW=function(_dX){var _dY=new T(function(){return E(E(E(_dX).c).a);}),_dZ=new T(function(){return B(A2(_dU,E(_dX).a,new T(function(){return B(A2(_9Z,B(_8s(B(_8q(_dY)))),_L));})));});return new T2(0,new T(function(){return B(_dS(_dY));}),_dZ);},_e0=function(_e1,_e2){var _e3=B(_dW(_e2));return new T2(0,_e3.a,_e3.b);},_e4=function(_e5,_e6,_e7){var _e8=new T(function(){return E(E(E(_e5).c).a);}),_e9=new T(function(){var _ea=new T(function(){return B(_8s(new T(function(){return B(_8q(_e8));})));}),_eb=new T(function(){return B(A2(_cy,_e8,_e6));});return B(A3(_ad,B(_a5(E(_e5).a)),function(_ec){return new F(function(){return A3(_8u,_ea,_ec,_eb);});},_e7));});return new T2(0,new T(function(){return B(A2(_cA,_e8,_e6));}),_e9);},_ed=function(_ee,_ef,_eg){var _eh=E(_eg),_ei=B(_e4(_ef,_eh.a,_eh.b));return new T2(0,_ei.a,_ei.b);},_ej=function(_ek,_el,_em){var _en=new T(function(){return E(E(E(_ek).c).a);}),_eo=new T(function(){var _ep=new T(function(){return B(_8s(new T(function(){return B(_8q(_en));})));}),_eq=new T(function(){return B(A2(_cR,_en,_el));});return B(A3(_ad,B(_a5(E(_ek).a)),function(_er){return new F(function(){return A3(_8u,_ep,_er,_eq);});},_em));});return new T2(0,new T(function(){return B(A2(_cT,_en,_el));}),_eo);},_es=function(_et,_eu,_ev){var _ew=E(_ev),_ex=B(_ej(_eu,_ew.a,_ew.b));return new T2(0,_ex.a,_ex.b);},_ey=new T1(0,2),_ez=function(_eA,_eB,_eC){var _eD=new T(function(){return E(E(E(_eA).c).a);}),_eE=new T(function(){var _eF=new T(function(){return B(_8q(_eD));}),_eG=new T(function(){return B(_8s(_eF));}),_eH=new T(function(){var _eI=new T(function(){return B(A3(_a9,_eF,new T(function(){return B(A2(_9Z,_eG,_aI));}),new T(function(){return B(A2(_9Z,_eG,_ey));})));});return B(A3(_a9,_eF,_eI,new T(function(){return B(A2(_8F,_eD,_eB));})));});return B(A3(_ad,B(_a5(E(_eA).a)),function(_eJ){return new F(function(){return A3(_8u,_eG,_eJ,_eH);});},_eC));});return new T2(0,new T(function(){return B(A2(_8F,_eD,_eB));}),_eE);},_eK=function(_eL,_eM,_eN){var _eO=E(_eN),_eP=B(_ez(_eM,_eO.a,_eO.b));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR){return E(E(_eR).j);},_eS=function(_eT,_eU,_eV){var _eW=new T(function(){return E(E(E(_eT).c).a);}),_eX=new T(function(){var _eY=new T(function(){return B(_8q(_eW));}),_eZ=new T(function(){var _f0=new T(function(){return B(A2(_cy,_eW,_eU));});return B(A3(_8u,B(_8s(_eY)),_f0,_f0));});return B(A3(_ad,B(_a5(E(_eT).a)),function(_f1){return new F(function(){return A3(_a9,_eY,_f1,_eZ);});},_eV));});return new T2(0,new T(function(){return B(A2(_eQ,_eW,_eU));}),_eX);},_f2=function(_f3,_f4,_f5){var _f6=E(_f5),_f7=B(_eS(_f4,_f6.a,_f6.b));return new T2(0,_f7.a,_f7.b);},_f8=function(_f9){return E(E(_f9).p);},_fa=function(_fb,_fc,_fd){var _fe=new T(function(){return E(E(E(_fb).c).a);}),_ff=new T(function(){var _fg=new T(function(){return B(_8q(_fe));}),_fh=new T(function(){var _fi=new T(function(){return B(A2(_cR,_fe,_fc));});return B(A3(_8u,B(_8s(_fg)),_fi,_fi));});return B(A3(_ad,B(_a5(E(_fb).a)),function(_fj){return new F(function(){return A3(_a9,_fg,_fj,_fh);});},_fd));});return new T2(0,new T(function(){return B(A2(_f8,_fe,_fc));}),_ff);},_fk=function(_fl,_fm,_fn){var _fo=E(_fn),_fp=B(_fa(_fm,_fo.a,_fo.b));return new T2(0,_fp.a,_fp.b);},_fq=function(_fr,_fs){return {_:0,a:_fr,b:new T(function(){return B(_e0(_fr,_fs));}),c:function(_ft){return new F(function(){return _dl(_fr,_fs,_ft);});},d:function(_ft){return new F(function(){return _dB(_fr,_fs,_ft);});},e:function(_ft){return new F(function(){return _eK(_fr,_fs,_ft);});},f:function(_fu,_ft){return new F(function(){return _aA(_fr,_fs,_fu,_ft);});},g:function(_fu,_ft){return new F(function(){return _dH(_fr,_fs,_fu,_ft);});},h:function(_ft){return new F(function(){return _ed(_fr,_fs,_ft);});},i:function(_ft){return new F(function(){return _cL(_fr,_fs,_ft);});},j:function(_ft){return new F(function(){return _f2(_fr,_fs,_ft);});},k:function(_ft){return new F(function(){return _bz(_fr,_fs,_ft);});},l:function(_ft){return new F(function(){return _aX(_fr,_fs,_ft);});},m:function(_ft){return new F(function(){return _ca(_fr,_fs,_ft);});},n:function(_ft){return new F(function(){return _es(_fr,_fs,_ft);});},o:function(_ft){return new F(function(){return _d4(_fr,_fs,_ft);});},p:function(_ft){return new F(function(){return _fk(_fr,_fs,_ft);});},q:function(_ft){return new F(function(){return _bS(_fr,_fs,_ft);});},r:function(_ft){return new F(function(){return _bg(_fr,_fs,_ft);});},s:function(_ft){return new F(function(){return _cs(_fr,_fs,_ft);});}};},_fv=function(_fw,_fx,_fy,_fz,_fA){var _fB=new T(function(){return B(_8q(new T(function(){return E(E(E(_fw).c).a);})));}),_fC=new T(function(){var _fD=E(_fw).a,_fE=new T(function(){var _fF=new T(function(){return B(_8s(_fB));}),_fG=new T(function(){return B(A3(_8u,_fF,_fz,_fz));}),_fH=function(_fI,_fJ){var _fK=new T(function(){return B(A3(_8w,_fF,new T(function(){return B(A3(_8u,_fF,_fI,_fz));}),new T(function(){return B(A3(_8u,_fF,_fx,_fJ));})));});return new F(function(){return A3(_a9,_fB,_fK,_fG);});};return B(A3(_ad,B(_a5(_fD)),_fH,_fy));});return B(A3(_ab,_fD,_fE,_fA));});return new T2(0,new T(function(){return B(A3(_a9,_fB,_fx,_fz));}),_fC);},_fL=function(_fM,_fN,_fO,_fP){var _fQ=E(_fO),_fR=E(_fP),_fS=B(_fv(_fN,_fQ.a,_fQ.b,_fR.a,_fR.b));return new T2(0,_fS.a,_fS.b);},_fT=function(_fU,_fV){var _fW=new T(function(){return B(_8q(new T(function(){return E(E(E(_fU).c).a);})));}),_fX=new T(function(){return B(A2(_dU,E(_fU).a,new T(function(){return B(A2(_9Z,B(_8s(_fW)),_L));})));});return new T2(0,new T(function(){return B(A2(_8y,_fW,_fV));}),_fX);},_fY=function(_fZ,_g0,_g1){var _g2=B(_fT(_g0,_g1));return new T2(0,_g2.a,_g2.b);},_g3=function(_g4,_g5,_g6){var _g7=new T(function(){return B(_8q(new T(function(){return E(E(E(_g4).c).a);})));}),_g8=new T(function(){return B(_8s(_g7));}),_g9=new T(function(){var _ga=new T(function(){var _gb=new T(function(){return B(A3(_a9,_g7,new T(function(){return B(A2(_9Z,_g8,_aI));}),new T(function(){return B(A3(_8u,_g8,_g5,_g5));})));});return B(A2(_88,_g8,_gb));});return B(A3(_ad,B(_a5(E(_g4).a)),function(_gc){return new F(function(){return A3(_8u,_g8,_gc,_ga);});},_g6));}),_gd=new T(function(){return B(A3(_a9,_g7,new T(function(){return B(A2(_9Z,_g8,_aI));}),_g5));});return new T2(0,_gd,_g9);},_ge=function(_gf,_gg,_gh){var _gi=E(_gh),_gj=B(_g3(_gg,_gi.a,_gi.b));return new T2(0,_gj.a,_gj.b);},_gk=function(_gl,_gm){return new T4(0,_gl,function(_fu,_ft){return new F(function(){return _fL(_gl,_gm,_fu,_ft);});},function(_ft){return new F(function(){return _ge(_gl,_gm,_ft);});},function(_ft){return new F(function(){return _fY(_gl,_gm,_ft);});});},_gn=function(_go,_gp,_gq,_gr,_gs){var _gt=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_go).c).a);})));})));}),_gu=new T(function(){var _gv=E(_go).a,_gw=new T(function(){var _gx=function(_gy,_gz){return new F(function(){return A3(_86,_gt,new T(function(){return B(A3(_8u,_gt,_gp,_gz));}),new T(function(){return B(A3(_8u,_gt,_gy,_gr));}));});};return B(A3(_ad,B(_a5(_gv)),_gx,_gq));});return B(A3(_ab,_gv,_gw,_gs));});return new T2(0,new T(function(){return B(A3(_8u,_gt,_gp,_gr));}),_gu);},_gA=function(_gB,_gC,_gD){var _gE=E(_gC),_gF=E(_gD),_gG=B(_gn(_gB,_gE.a,_gE.b,_gF.a,_gF.b));return new T2(0,_gG.a,_gG.b);},_gH=function(_gI,_gJ,_gK,_gL,_gM){var _gN=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gI).c).a);})));})));}),_gO=new T(function(){var _gP=E(_gI).a,_gQ=new T(function(){return B(A3(_ad,B(_a5(_gP)),new T(function(){return B(_86(_gN));}),_gK));});return B(A3(_ab,_gP,_gQ,_gM));});return new T2(0,new T(function(){return B(A3(_86,_gN,_gJ,_gL));}),_gO);},_gR=function(_gS,_gT,_gU){var _gV=E(_gT),_gW=E(_gU),_gX=B(_gH(_gS,_gV.a,_gV.b,_gW.a,_gW.b));return new T2(0,_gX.a,_gX.b);},_gY=function(_gZ,_h0,_h1){var _h2=B(_h3(_gZ));return new F(function(){return A3(_86,_h2,_h0,new T(function(){return B(A2(_88,_h2,_h1));}));});},_h4=function(_h5){return E(E(_h5).e);},_h6=function(_h7){return E(E(_h7).f);},_h8=function(_h9,_ha,_hb){var _hc=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_h9).c).a);})));})));}),_hd=new T(function(){var _he=new T(function(){return B(A2(_h6,_hc,_ha));});return B(A3(_ad,B(_a5(E(_h9).a)),function(_hf){return new F(function(){return A3(_8u,_hc,_hf,_he);});},_hb));});return new T2(0,new T(function(){return B(A2(_h4,_hc,_ha));}),_hd);},_hg=function(_hh,_hi){var _hj=E(_hi),_hk=B(_h8(_hh,_hj.a,_hj.b));return new T2(0,_hk.a,_hk.b);},_hl=function(_hm,_hn){var _ho=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hm).c).a);})));})));}),_hp=new T(function(){return B(A2(_dU,E(_hm).a,new T(function(){return B(A2(_9Z,_ho,_L));})));});return new T2(0,new T(function(){return B(A2(_9Z,_ho,_hn));}),_hp);},_hq=function(_hr,_hs){var _ht=B(_hl(_hr,_hs));return new T2(0,_ht.a,_ht.b);},_hu=function(_hv,_hw,_hx){var _hy=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hv).c).a);})));})));}),_hz=new T(function(){return B(A3(_ad,B(_a5(E(_hv).a)),new T(function(){return B(_88(_hy));}),_hx));});return new T2(0,new T(function(){return B(A2(_88,_hy,_hw));}),_hz);},_hA=function(_hB,_hC){var _hD=E(_hC),_hE=B(_hu(_hB,_hD.a,_hD.b));return new T2(0,_hE.a,_hE.b);},_hF=function(_hG,_hH){var _hI=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hG).c).a);})));})));}),_hJ=new T(function(){return B(A2(_dU,E(_hG).a,new T(function(){return B(A2(_9Z,_hI,_L));})));});return new T2(0,new T(function(){return B(A2(_h6,_hI,_hH));}),_hJ);},_hK=function(_hL,_hM){var _hN=B(_hF(_hL,E(_hM).a));return new T2(0,_hN.a,_hN.b);},_h3=function(_hO){return {_:0,a:function(_fu,_ft){return new F(function(){return _gR(_hO,_fu,_ft);});},b:function(_fu,_ft){return new F(function(){return _gY(_hO,_fu,_ft);});},c:function(_fu,_ft){return new F(function(){return _gA(_hO,_fu,_ft);});},d:function(_ft){return new F(function(){return _hA(_hO,_ft);});},e:function(_ft){return new F(function(){return _hg(_hO,_ft);});},f:function(_ft){return new F(function(){return _hK(_hO,_ft);});},g:function(_ft){return new F(function(){return _hq(_hO,_ft);});}};},_hP=function(_hQ){var _hR=new T(function(){return E(E(_hQ).a);}),_hS=new T3(0,_9X,_a1,new T2(0,_hR,new T(function(){return E(E(_hQ).b);}))),_hT=new T(function(){return B(_fq(new T(function(){return B(_gk(new T(function(){return B(_h3(_hS));}),_hS));}),_hS));}),_hU=new T(function(){return B(_8s(new T(function(){return B(_8q(_hR));})));});return function(_hV){var _hW=E(_hV),_hX=B(A2(_9Z,_hU,_1o)),_hY=B(A2(_9Z,_hU,_9Y));return E(B(_8H(_hT,new T2(0,_hW.a,new T3(0,E(_hX),E(_hY),E(_hY))),new T2(0,_hW.b,new T3(0,E(_hY),E(_hX),E(_hY))),new T2(0,_hW.c,new T3(0,E(_hY),E(_hY),E(_hX))))).b);};},_hZ=new T(function(){return B(_hP(_9t));}),_i0=function(_i1,_i2){var _i3=E(_i2);return (_i3._==0)?__Z:new T2(1,_i1,new T2(1,_i3.a,new T(function(){return B(_i0(_i1,_i3.b));})));},_i4=new T(function(){var _i5=B(A1(_hZ,_92));return new T2(1,_i5.a,new T(function(){return B(_i0(_22,new T2(1,_i5.b,new T2(1,_i5.c,_w))));}));}),_i6=new T1(1,_i4),_i7=new T2(1,_i6,_1S),_i8=new T(function(){return B(unCStr("vec3("));}),_i9=new T1(0,_i8),_ia=new T2(1,_i9,_i7),_ib=new T(function(){return toJSStr(B(_1F(_x,_1l,_ia)));}),_ic=function(_id,_ie){while(1){var _if=E(_id);if(!_if._){return E(_ie);}else{var _ig=_ie+1|0;_id=_if.b;_ie=_ig;continue;}}},_ih=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_ii=new T(function(){return B(err(_ih));}),_ij=0,_ik=new T3(0,E(_ij),E(_ij),E(_ij)),_il=new T2(0,E(_ik),E(_ij)),_im=new T(function(){return B(unCStr("Negative exponent"));}),_in=new T(function(){return B(err(_im));}),_io=function(_ip,_iq,_ir){while(1){if(!(_iq%2)){var _is=_ip*_ip,_it=quot(_iq,2);_ip=_is;_iq=_it;continue;}else{var _iu=E(_iq);if(_iu==1){return _ip*_ir;}else{var _is=_ip*_ip,_iv=_ip*_ir;_ip=_is;_iq=quot(_iu-1|0,2);_ir=_iv;continue;}}}},_iw=function(_ix,_iy){while(1){if(!(_iy%2)){var _iz=_ix*_ix,_iA=quot(_iy,2);_ix=_iz;_iy=_iA;continue;}else{var _iB=E(_iy);if(_iB==1){return E(_ix);}else{return new F(function(){return _io(_ix*_ix,quot(_iB-1|0,2),_ix);});}}}},_iC=function(_iD){var _iE=E(_iD);return new F(function(){return Math.log(_iE+(_iE+1)*Math.sqrt((_iE-1)/(_iE+1)));});},_iF=function(_iG){var _iH=E(_iG);return new F(function(){return Math.log(_iH+Math.sqrt(1+_iH*_iH));});},_iI=function(_iJ){var _iK=E(_iJ);return 0.5*Math.log((1+_iK)/(1-_iK));},_iL=function(_iM,_iN){return Math.log(E(_iN))/Math.log(E(_iM));},_iO=3.141592653589793,_iP=function(_iQ){var _iR=E(_iQ);return new F(function(){return _7J(_iR.a,_iR.b);});},_iS=function(_iT){return 1/E(_iT);},_iU=function(_iV){var _iW=E(_iV),_iX=E(_iW);return (_iX==0)?E(_7I):(_iX<=0)? -_iX:E(_iW);},_iY=function(_iZ){var _j0=E(_iZ);if(!_j0._){return _j0.a;}else{return new F(function(){return I_toNumber(_j0.a);});}},_j1=function(_j2){return new F(function(){return _iY(_j2);});},_j3=1,_j4=-1,_j5=function(_j6){var _j7=E(_j6);return (_j7<=0)?(_j7>=0)?E(_j7):E(_j4):E(_j3);},_j8=function(_j9,_ja){return E(_j9)-E(_ja);},_jb=function(_jc){return  -E(_jc);},_jd=function(_je,_jf){return E(_je)+E(_jf);},_jg=function(_jh,_ji){return E(_jh)*E(_ji);},_jj={_:0,a:_jd,b:_j8,c:_jg,d:_jb,e:_iU,f:_j5,g:_j1},_jk=function(_jl,_jm){return E(_jl)/E(_jm);},_jn=new T4(0,_jj,_jk,_iS,_iP),_jo=function(_jp){return new F(function(){return Math.acos(E(_jp));});},_jq=function(_jr){return new F(function(){return Math.asin(E(_jr));});},_js=function(_jt){return new F(function(){return Math.atan(E(_jt));});},_ju=function(_jv){return new F(function(){return Math.cos(E(_jv));});},_jw=function(_jx){return new F(function(){return cosh(E(_jx));});},_jy=function(_jz){return new F(function(){return Math.exp(E(_jz));});},_jA=function(_jB){return new F(function(){return Math.log(E(_jB));});},_jC=function(_jD,_jE){return new F(function(){return Math.pow(E(_jD),E(_jE));});},_jF=function(_jG){return new F(function(){return Math.sin(E(_jG));});},_jH=function(_jI){return new F(function(){return sinh(E(_jI));});},_jJ=function(_jK){return new F(function(){return Math.sqrt(E(_jK));});},_jL=function(_jM){return new F(function(){return Math.tan(E(_jM));});},_jN=function(_jO){return new F(function(){return tanh(E(_jO));});},_jP={_:0,a:_jn,b:_iO,c:_jy,d:_jA,e:_jJ,f:_jC,g:_iL,h:_jF,i:_ju,j:_jL,k:_jq,l:_jo,m:_js,n:_jH,o:_jw,p:_jN,q:_iF,r:_iC,s:_iI},_jQ=function(_jR,_jS){return (E(_jR)!=E(_jS))?true:false;},_jT=function(_jU,_jV){return E(_jU)==E(_jV);},_jW=new T2(0,_jT,_jQ),_jX=function(_jY,_jZ){return E(_jY)<E(_jZ);},_k0=function(_k1,_k2){return E(_k1)<=E(_k2);},_k3=function(_k4,_k5){return E(_k4)>E(_k5);},_k6=function(_k7,_k8){return E(_k7)>=E(_k8);},_k9=function(_ka,_kb){var _kc=E(_ka),_kd=E(_kb);return (_kc>=_kd)?(_kc!=_kd)?2:1:0;},_ke=function(_kf,_kg){var _kh=E(_kf),_ki=E(_kg);return (_kh>_ki)?E(_kh):E(_ki);},_kj=function(_kk,_kl){var _km=E(_kk),_kn=E(_kl);return (_km>_kn)?E(_kn):E(_km);},_ko={_:0,a:_jW,b:_k9,c:_jX,d:_k0,e:_k3,f:_k6,g:_ke,h:_kj},_kp="dz",_kq="wy",_kr="wx",_ks="dy",_kt="dx",_ku="t",_kv="a",_kw="r",_kx="ly",_ky="lx",_kz="wz",_kA=0,_kB=function(_kC){var _kD=__new(),_kE=_kD,_kF=function(_kG,_){while(1){var _kH=E(_kG);if(!_kH._){return _kA;}else{var _kI=E(_kH.a),_kJ=__set(_kE,E(_kI.a),E(_kI.b));_kG=_kH.b;continue;}}},_kK=B(_kF(_kC,_));return E(_kE);},_kL=function(_kM,_kN,_kO,_kP,_kQ,_kR,_kS,_kT,_kU){return new F(function(){return _kB(new T2(1,new T2(0,_kr,_kM),new T2(1,new T2(0,_kq,_kN),new T2(1,new T2(0,_kz,_kO),new T2(1,new T2(0,_ky,_kP*_kQ*Math.cos(_kR)),new T2(1,new T2(0,_kx,_kP*_kQ*Math.sin(_kR)),new T2(1,new T2(0,_kw,_kP),new T2(1,new T2(0,_kv,_kQ),new T2(1,new T2(0,_ku,_kR),new T2(1,new T2(0,_kt,_kS),new T2(1,new T2(0,_ks,_kT),new T2(1,new T2(0,_kp,_kU),_w))))))))))));});},_kV=function(_kW){var _kX=E(_kW),_kY=E(_kX.a),_kZ=E(_kX.b),_l0=E(_kX.d);return new F(function(){return _kL(_kY.a,_kY.b,_kY.c,E(_kZ.a),E(_kZ.b),E(_kX.c),_l0.a,_l0.b,_l0.c);});},_l1=function(_l2,_l3){var _l4=E(_l3);return (_l4._==0)?__Z:new T2(1,new T(function(){return B(A1(_l2,_l4.a));}),new T(function(){return B(_l1(_l2,_l4.b));}));},_l5=function(_l6,_l7,_l8){var _l9=__lst2arr(B(_l1(_kV,new T2(1,_l6,new T2(1,_l7,new T2(1,_l8,_w))))));return E(_l9);},_la=function(_lb){var _lc=E(_lb);return new F(function(){return _l5(_lc.a,_lc.b,_lc.c);});},_ld=new T2(0,_jP,_ko),_le=function(_lf,_lg,_lh,_li,_lj,_lk,_ll){var _lm=B(_8s(B(_8q(_lf)))),_ln=new T(function(){return B(A3(_86,_lm,new T(function(){return B(A3(_8u,_lm,_lg,_lj));}),new T(function(){return B(A3(_8u,_lm,_lh,_lk));})));});return new F(function(){return A3(_86,_lm,_ln,new T(function(){return B(A3(_8u,_lm,_li,_ll));}));});},_lo=function(_lp,_lq,_lr,_ls){var _lt=B(_8q(_lp)),_lu=new T(function(){return B(A2(_8F,_lp,new T(function(){return B(_le(_lp,_lq,_lr,_ls,_lq,_lr,_ls));})));});return new T3(0,B(A3(_a9,_lt,_lq,_lu)),B(A3(_a9,_lt,_lr,_lu)),B(A3(_a9,_lt,_ls,_lu)));},_lv=function(_lw,_lx,_ly,_lz,_lA,_lB,_lC){var _lD=B(_8u(_lw));return new T3(0,B(A1(B(A1(_lD,_lx)),_lA)),B(A1(B(A1(_lD,_ly)),_lB)),B(A1(B(A1(_lD,_lz)),_lC)));},_lE=function(_lF,_lG,_lH,_lI,_lJ,_lK,_lL){var _lM=B(_86(_lF));return new T3(0,B(A1(B(A1(_lM,_lG)),_lJ)),B(A1(B(A1(_lM,_lH)),_lK)),B(A1(B(A1(_lM,_lI)),_lL)));},_lN=function(_lO,_lP){var _lQ=new T(function(){return E(E(_lO).a);}),_lR=new T(function(){return B(A2(_hP,new T2(0,_lQ,new T(function(){return E(E(_lO).b);})),_lP));}),_lS=new T(function(){var _lT=E(_lR),_lU=B(_lo(_lQ,_lT.a,_lT.b,_lT.c));return new T3(0,E(_lU.a),E(_lU.b),E(_lU.c));}),_lV=new T(function(){var _lW=E(_lP),_lX=_lW.a,_lY=_lW.b,_lZ=_lW.c,_m0=E(_lS),_m1=B(_8q(_lQ)),_m2=new T(function(){return B(A2(_8F,_lQ,new T(function(){var _m3=E(_lR),_m4=_m3.a,_m5=_m3.b,_m6=_m3.c;return B(_le(_lQ,_m4,_m5,_m6,_m4,_m5,_m6));})));}),_m7=B(A3(_a9,_m1,new T(function(){return B(_8H(_lQ,_lX,_lY,_lZ));}),_m2)),_m8=B(_8s(_m1)),_m9=B(_lv(_m8,_m0.a,_m0.b,_m0.c,_m7,_m7,_m7)),_ma=B(_88(_m8)),_mb=B(_lE(_m8,_lX,_lY,_lZ,B(A1(_ma,_m9.a)),B(A1(_ma,_m9.b)),B(A1(_ma,_m9.c))));return new T3(0,E(_mb.a),E(_mb.b),E(_mb.c));});return new T2(0,_lV,_lS);},_mc=function(_md){return E(E(_md).a);},_me=function(_mf,_mg,_mh,_mi,_mj,_mk,_ml){var _mm=B(_le(_mf,_mj,_mk,_ml,_mg,_mh,_mi)),_mn=B(_8s(B(_8q(_mf)))),_mo=B(_lv(_mn,_mj,_mk,_ml,_mm,_mm,_mm)),_mp=B(_88(_mn));return new F(function(){return _lE(_mn,_mg,_mh,_mi,B(A1(_mp,_mo.a)),B(A1(_mp,_mo.b)),B(A1(_mp,_mo.c)));});},_mq=function(_mr){return E(E(_mr).a);},_ms=function(_mt,_mu,_mv,_mw){var _mx=new T(function(){var _my=E(_mw),_mz=E(_mv),_mA=B(_me(_mt,_my.a,_my.b,_my.c,_mz.a,_mz.b,_mz.c));return new T3(0,E(_mA.a),E(_mA.b),E(_mA.c));}),_mB=new T(function(){return B(A2(_8F,_mt,new T(function(){var _mC=E(_mx),_mD=_mC.a,_mE=_mC.b,_mF=_mC.c;return B(_le(_mt,_mD,_mE,_mF,_mD,_mE,_mF));})));});if(!B(A3(_mq,B(_mc(_mu)),_mB,new T(function(){return B(A2(_9Z,B(_8s(B(_8q(_mt)))),_9Y));})))){var _mG=E(_mx),_mH=B(_lo(_mt,_mG.a,_mG.b,_mG.c)),_mI=B(A2(_8F,_mt,new T(function(){var _mJ=E(_mw),_mK=_mJ.a,_mL=_mJ.b,_mM=_mJ.c;return B(_le(_mt,_mK,_mL,_mM,_mK,_mL,_mM));}))),_mN=B(_8u(new T(function(){return B(_8s(new T(function(){return B(_8q(_mt));})));})));return new T3(0,B(A1(B(A1(_mN,_mH.a)),_mI)),B(A1(B(A1(_mN,_mH.b)),_mI)),B(A1(B(A1(_mN,_mH.c)),_mI)));}else{var _mO=B(A2(_9Z,B(_8s(B(_8q(_mt)))),_9Y));return new T3(0,_mO,_mO,_mO);}},_mP=function(_mQ,_mR){while(1){var _mS=E(_mQ);if(!_mS._){return E(_mR);}else{var _mT=_mS.b,_mU=E(_mS.a);if(_mR>_mU){_mQ=_mT;continue;}else{_mQ=_mT;_mR=_mU;continue;}}}},_mV=new T(function(){var _mW=eval("angleCount"),_mX=Number(_mW);return jsTrunc(_mX);}),_mY=new T(function(){return E(_mV);}),_mZ=new T(function(){return B(unCStr(": empty list"));}),_n0=new T(function(){return B(unCStr("Prelude."));}),_n1=function(_n2){return new F(function(){return err(B(_n(_n0,new T(function(){return B(_n(_n2,_mZ));},1))));});},_n3=new T(function(){return B(unCStr("head"));}),_n4=new T(function(){return B(_n1(_n3));}),_n5=function(_n6,_n7,_n8){var _n9=E(_n6);if(!_n9._){return __Z;}else{var _na=E(_n7);if(!_na._){return __Z;}else{var _nb=_na.a,_nc=E(_n8);if(!_nc._){return __Z;}else{var _nd=E(_nc.a),_ne=_nd.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_n9.a),E(_nb),E(_ne));}),new T2(1,new T(function(){return new T3(0,E(_nb),E(_ne),E(_nd.b));}),_w)),new T(function(){return B(_n5(_n9.b,_na.b,_nc.b));},1));});}}}},_nf=new T(function(){return B(unCStr("tail"));}),_ng=new T(function(){return B(_n1(_nf));}),_nh=function(_ni,_nj){var _nk=E(_ni);if(!_nk._){return __Z;}else{var _nl=E(_nj);return (_nl._==0)?__Z:new T2(1,new T2(0,_nk.a,_nl.a),new T(function(){return B(_nh(_nk.b,_nl.b));}));}},_nm=function(_nn,_no){var _np=E(_nn);if(!_np._){return __Z;}else{var _nq=E(_no);if(!_nq._){return __Z;}else{var _nr=E(_np.a),_ns=_nr.b,_nt=E(_nq.a).b,_nu=new T(function(){var _nv=new T(function(){return B(_nh(_nt,new T(function(){var _nw=E(_nt);if(!_nw._){return E(_ng);}else{return E(_nw.b);}},1)));},1);return B(_n5(_ns,new T(function(){var _nx=E(_ns);if(!_nx._){return E(_ng);}else{return E(_nx.b);}},1),_nv));});return new F(function(){return _n(new T2(1,new T(function(){var _ny=E(_ns);if(!_ny._){return E(_n4);}else{var _nz=E(_nt);if(!_nz._){return E(_n4);}else{return new T3(0,E(_nr.a),E(_ny.a),E(_nz.a));}}}),_nu),new T(function(){return B(_nm(_np.b,_nq.b));},1));});}}},_nA=new T(function(){return 6.283185307179586/E(_mY);}),_nB=new T(function(){return E(_mY)-1;}),_nC=new T1(0,1),_nD=function(_nE,_nF){var _nG=E(_nF),_nH=new T(function(){var _nI=B(_8s(_nE)),_nJ=B(_nD(_nE,B(A3(_86,_nI,_nG,new T(function(){return B(A2(_9Z,_nI,_nC));})))));return new T2(1,_nJ.a,_nJ.b);});return new T2(0,_nG,_nH);},_nK=function(_nL){return E(E(_nL).d);},_nM=new T1(0,2),_nN=function(_nO,_nP){var _nQ=E(_nP);if(!_nQ._){return __Z;}else{var _nR=_nQ.a;return (!B(A1(_nO,_nR)))?__Z:new T2(1,_nR,new T(function(){return B(_nN(_nO,_nQ.b));}));}},_nS=function(_nT,_nU,_nV,_nW){var _nX=B(_nD(_nU,_nV)),_nY=new T(function(){var _nZ=B(_8s(_nU)),_o0=new T(function(){return B(A3(_a9,_nU,new T(function(){return B(A2(_9Z,_nZ,_nC));}),new T(function(){return B(A2(_9Z,_nZ,_nM));})));});return B(A3(_86,_nZ,_nW,_o0));});return new F(function(){return _nN(function(_o1){return new F(function(){return A3(_nK,_nT,_o1,_nY);});},new T2(1,_nX.a,_nX.b));});},_o2=new T(function(){return B(_nS(_ko,_jn,_ij,_nB));}),_o3=function(_o4,_o5){while(1){var _o6=E(_o4);if(!_o6._){return E(_o5);}else{_o4=_o6.b;_o5=_o6.a;continue;}}},_o7=new T(function(){return B(unCStr("last"));}),_o8=new T(function(){return B(_n1(_o7));}),_o9=function(_oa){return new F(function(){return _o3(_oa,_o8);});},_ob=function(_oc){return new F(function(){return _o9(E(_oc).b);});},_od=new T(function(){return B(unCStr("maximum"));}),_oe=new T(function(){return B(_n1(_od));}),_of=new T(function(){var _og=eval("proceedCount"),_oh=Number(_og);return jsTrunc(_oh);}),_oi=new T(function(){return E(_of);}),_oj=1,_ok=new T(function(){return B(_nS(_ko,_jn,_oj,_oi));}),_ol=function(_om,_on,_oo,_op,_oq,_or,_os,_ot,_ou,_ov,_ow,_ox,_oy,_oz){var _oA=new T(function(){var _oB=new T(function(){var _oC=E(_ov),_oD=E(_oz),_oE=E(_oy),_oF=E(_ow),_oG=E(_ox),_oH=E(_ou);return new T3(0,_oC*_oD-_oE*_oF,_oF*_oG-_oD*_oH,_oH*_oE-_oG*_oC);}),_oI=function(_oJ){var _oK=new T(function(){var _oL=E(_oJ)/E(_mY);return (_oL+_oL)*3.141592653589793;}),_oM=new T(function(){return B(A1(_om,_oK));}),_oN=new T(function(){var _oO=new T(function(){var _oP=E(_oM)/E(_oi);return new T3(0,E(_oP),E(_oP),E(_oP));}),_oQ=function(_oR,_oS){var _oT=E(_oR);if(!_oT._){return new T2(0,_w,_oS);}else{var _oU=new T(function(){var _oV=B(_lN(_ld,new T(function(){var _oW=E(_oS),_oX=E(_oW.a),_oY=E(_oW.b),_oZ=E(_oO);return new T3(0,E(_oX.a)+E(_oY.a)*E(_oZ.a),E(_oX.b)+E(_oY.b)*E(_oZ.b),E(_oX.c)+E(_oY.c)*E(_oZ.c));}))),_p0=_oV.a,_p1=new T(function(){var _p2=E(_oV.b),_p3=E(E(_oS).b),_p4=B(_me(_jP,_p3.a,_p3.b,_p3.c,_p2.a,_p2.b,_p2.c)),_p5=B(_lo(_jP,_p4.a,_p4.b,_p4.c));return new T3(0,E(_p5.a),E(_p5.b),E(_p5.c));});return new T2(0,new T(function(){var _p6=E(_oM),_p7=E(_oK);return new T4(0,E(_p0),E(new T2(0,E(_oT.a)/E(_oi),E(_p6))),E(_p7),E(_p1));}),new T2(0,_p0,_p1));}),_p8=new T(function(){var _p9=B(_oQ(_oT.b,new T(function(){return E(E(_oU).b);})));return new T2(0,_p9.a,_p9.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oU).a);}),new T(function(){return E(E(_p8).a);})),new T(function(){return E(E(_p8).b);}));}},_pa=function(_pb,_pc,_pd,_pe,_pf){var _pg=E(_pb);if(!_pg._){return new T2(0,_w,new T2(0,new T3(0,E(_pc),E(_pd),E(_pe)),_pf));}else{var _ph=new T(function(){var _pi=B(_lN(_ld,new T(function(){var _pj=E(_pf),_pk=E(_oO);return new T3(0,E(_pc)+E(_pj.a)*E(_pk.a),E(_pd)+E(_pj.b)*E(_pk.b),E(_pe)+E(_pj.c)*E(_pk.c));}))),_pl=_pi.a,_pm=new T(function(){var _pn=E(_pi.b),_po=E(_pf),_pp=B(_me(_jP,_po.a,_po.b,_po.c,_pn.a,_pn.b,_pn.c)),_pq=B(_lo(_jP,_pp.a,_pp.b,_pp.c));return new T3(0,E(_pq.a),E(_pq.b),E(_pq.c));});return new T2(0,new T(function(){var _pr=E(_oM),_ps=E(_oK);return new T4(0,E(_pl),E(new T2(0,E(_pg.a)/E(_oi),E(_pr))),E(_ps),E(_pm));}),new T2(0,_pl,_pm));}),_pt=new T(function(){var _pu=B(_oQ(_pg.b,new T(function(){return E(E(_ph).b);})));return new T2(0,_pu.a,_pu.b);});return new T2(0,new T2(1,new T(function(){return E(E(_ph).a);}),new T(function(){return E(E(_pt).a);})),new T(function(){return E(E(_pt).b);}));}};return E(B(_pa(_ok,_op,_oq,_or,new T(function(){var _pv=E(_oB),_pw=E(_oK)+_os,_px=Math.cos(_pw),_py=Math.sin(_pw);return new T3(0,E(_ou)*_px+E(_pv.a)*_py,E(_ov)*_px+E(_pv.b)*_py,E(_ow)*_px+E(_pv.c)*_py);}))).a);});return new T2(0,new T(function(){var _pz=E(_oM),_pA=E(_oK);return new T4(0,E(new T3(0,E(_op),E(_oq),E(_or))),E(new T2(0,E(_ij),E(_pz))),E(_pA),E(_ik));}),_oN);};return B(_l1(_oI,_o2));}),_pB=new T(function(){var _pC=function(_pD){return new F(function(){return A1(_om,new T(function(){return B(_jg(_pD,_nA));}));});},_pE=B(_l1(_pC,_o2));if(!_pE._){return E(_oe);}else{return B(_mP(_pE.b,E(_pE.a)));}}),_pF=new T(function(){var _pG=new T(function(){var _pH=B(_n(_oA,new T2(1,new T(function(){var _pI=E(_oA);if(!_pI._){return E(_n4);}else{return E(_pI.a);}}),_w)));if(!_pH._){return E(_ng);}else{return E(_pH.b);}},1);return B(_nm(_oA,_pG));});return new T3(0,_pF,new T(function(){return B(_l1(_ob,_oA));}),_pB);},_pJ=function(_pK,_pL,_pM,_pN,_pO,_pP,_pQ,_pR,_pS,_pT,_pU,_pV,_pW,_pX,_pY,_pZ,_q0,_q1){var _q2=B(_lN(_ld,new T3(0,E(_pN),E(_pO),E(_pP)))),_q3=_q2.b,_q4=E(_q2.a),_q5=B(_ms(_jP,_ko,_q3,new T3(0,E(_pR),E(_pS),E(_pT)))),_q6=E(_q3),_q7=_q6.a,_q8=_q6.b,_q9=_q6.c,_qa=B(_me(_jP,_pV,_pW,_pX,_q7,_q8,_q9)),_qb=B(_lo(_jP,_qa.a,_qa.b,_qa.c)),_qc=_qb.a,_qd=_qb.b,_qe=_qb.c,_qf=E(_pQ),_qg=new T2(0,E(new T3(0,E(_q5.a),E(_q5.b),E(_q5.c))),E(_pU)),_qh=B(_ol(_pK,_pL,_pM,_q4.a,_q4.b,_q4.c,_qf,_qg,_qc,_qd,_qe,_q7,_q8,_q9)),_qi=__lst2arr(B(_l1(_la,_qh.a))),_qj=__lst2arr(B(_l1(_kV,_qh.b)));return {_:0,a:_pK,b:_pL,c:_pM,d:new T2(0,E(_q4),E(_qf)),e:_qg,f:new T3(0,E(_qc),E(_qd),E(_qe)),g:_q6,h:_qi,i:_qj,j:E(_qh.c)};},_qk=function(_ql){var _qm=E(_ql);return new T3(0,E(_qm.c), -E(_qm.b), -E(_qm.a));},_qn=function(_){return new F(function(){return __jsNull();});},_qo=function(_qp){var _qq=B(A1(_qp,_));return E(_qq);},_qr=new T(function(){return B(_qo(_qn));}),_qs=function(_qt,_qu,_qv,_qw,_qx,_qy,_qz,_qA,_qB,_qC,_qD,_qE,_qF){var _qG=function(_qH){var _qI=E(_nA),_qJ=2+_qH|0,_qK=_qJ-1|0,_qL=(2+_qH)*(1+_qH),_qM=E(_o2);if(!_qM._){return _qI*0;}else{var _qN=_qM.a,_qO=_qM.b,_qP=B(A1(_qt,new T(function(){return 6.283185307179586*E(_qN)/E(_mY);}))),_qQ=B(A1(_qt,new T(function(){return 6.283185307179586*(E(_qN)+1)/E(_mY);})));if(_qP!=_qQ){if(_qJ>=0){var _qR=E(_qJ);if(!_qR){var _qS=function(_qT,_qU){while(1){var _qV=B((function(_qW,_qX){var _qY=E(_qW);if(!_qY._){return E(_qX);}else{var _qZ=_qY.a,_r0=_qY.b,_r1=B(A1(_qt,new T(function(){return 6.283185307179586*E(_qZ)/E(_mY);}))),_r2=B(A1(_qt,new T(function(){return 6.283185307179586*(E(_qZ)+1)/E(_mY);})));if(_r1!=_r2){var _r3=_qX+0/(_r1-_r2)/_qL;_qT=_r0;_qU=_r3;return __continue;}else{if(_qK>=0){var _r4=E(_qK);if(!_r4){var _r3=_qX+_qJ/_qL;_qT=_r0;_qU=_r3;return __continue;}else{var _r3=_qX+_qJ*B(_iw(_r1,_r4))/_qL;_qT=_r0;_qU=_r3;return __continue;}}else{return E(_in);}}}})(_qT,_qU));if(_qV!=__continue){return _qV;}}};return _qI*B(_qS(_qO,0/(_qP-_qQ)/_qL));}else{var _r5=function(_r6,_r7){while(1){var _r8=B((function(_r9,_ra){var _rb=E(_r9);if(!_rb._){return E(_ra);}else{var _rc=_rb.a,_rd=_rb.b,_re=B(A1(_qt,new T(function(){return 6.283185307179586*E(_rc)/E(_mY);}))),_rf=B(A1(_qt,new T(function(){return 6.283185307179586*(E(_rc)+1)/E(_mY);})));if(_re!=_rf){if(_qR>=0){var _rg=_ra+(B(_iw(_re,_qR))-B(_iw(_rf,_qR)))/(_re-_rf)/_qL;_r6=_rd;_r7=_rg;return __continue;}else{return E(_in);}}else{if(_qK>=0){var _rh=E(_qK);if(!_rh){var _rg=_ra+_qJ/_qL;_r6=_rd;_r7=_rg;return __continue;}else{var _rg=_ra+_qJ*B(_iw(_re,_rh))/_qL;_r6=_rd;_r7=_rg;return __continue;}}else{return E(_in);}}}})(_r6,_r7));if(_r8!=__continue){return _r8;}}};return _qI*B(_r5(_qO,(B(_iw(_qP,_qR))-B(_iw(_qQ,_qR)))/(_qP-_qQ)/_qL));}}else{return E(_in);}}else{if(_qK>=0){var _ri=E(_qK);if(!_ri){var _rj=function(_rk,_rl){while(1){var _rm=B((function(_rn,_ro){var _rp=E(_rn);if(!_rp._){return E(_ro);}else{var _rq=_rp.a,_rr=_rp.b,_rs=B(A1(_qt,new T(function(){return 6.283185307179586*E(_rq)/E(_mY);}))),_rt=B(A1(_qt,new T(function(){return 6.283185307179586*(E(_rq)+1)/E(_mY);})));if(_rs!=_rt){if(_qJ>=0){var _ru=E(_qJ);if(!_ru){var _rv=_ro+0/(_rs-_rt)/_qL;_rk=_rr;_rl=_rv;return __continue;}else{var _rv=_ro+(B(_iw(_rs,_ru))-B(_iw(_rt,_ru)))/(_rs-_rt)/_qL;_rk=_rr;_rl=_rv;return __continue;}}else{return E(_in);}}else{var _rv=_ro+_qJ/_qL;_rk=_rr;_rl=_rv;return __continue;}}})(_rk,_rl));if(_rm!=__continue){return _rm;}}};return _qI*B(_rj(_qO,_qJ/_qL));}else{var _rw=function(_rx,_ry){while(1){var _rz=B((function(_rA,_rB){var _rC=E(_rA);if(!_rC._){return E(_rB);}else{var _rD=_rC.a,_rE=_rC.b,_rF=B(A1(_qt,new T(function(){return 6.283185307179586*E(_rD)/E(_mY);}))),_rG=B(A1(_qt,new T(function(){return 6.283185307179586*(E(_rD)+1)/E(_mY);})));if(_rF!=_rG){if(_qJ>=0){var _rH=E(_qJ);if(!_rH){var _rI=_rB+0/(_rF-_rG)/_qL;_rx=_rE;_ry=_rI;return __continue;}else{var _rI=_rB+(B(_iw(_rF,_rH))-B(_iw(_rG,_rH)))/(_rF-_rG)/_qL;_rx=_rE;_ry=_rI;return __continue;}}else{return E(_in);}}else{if(_ri>=0){var _rI=_rB+_qJ*B(_iw(_rF,_ri))/_qL;_rx=_rE;_ry=_rI;return __continue;}else{return E(_in);}}}})(_rx,_ry));if(_rz!=__continue){return _rz;}}};return _qI*B(_rw(_qO,_qJ*B(_iw(_qP,_ri))/_qL));}}else{return E(_in);}}}},_rJ=E(_qr),_rK=1/(B(_qG(1))*_qu);return new F(function(){return _pJ(_qt,_qk,new T2(0,E(new T3(0,E(_rK),E(_rK),E(_rK))),1/(B(_qG(3))*_qu)),_qv,_qw,_qx,_qy,_qz,_qA,_qB,_qC,_qD,_qE,_qF,_ik,_rJ,_rJ,0);});},_rL=1,_rM=function(_rN){return E(_ik);},_rO=function(_rP){var _rQ=I_decodeDouble(_rP);return new T2(0,new T1(1,_rQ.b),_rQ.a);},_rR=function(_rS){return new T1(0,_rS);},_rT=function(_rU){var _rV=hs_intToInt64(2147483647),_rW=hs_leInt64(_rU,_rV);if(!_rW){return new T1(1,I_fromInt64(_rU));}else{var _rX=hs_intToInt64(-2147483648),_rY=hs_geInt64(_rU,_rX);if(!_rY){return new T1(1,I_fromInt64(_rU));}else{var _rZ=hs_int64ToInt(_rU);return new F(function(){return _rR(_rZ);});}}},_s0=new T(function(){var _s1=newByteArr(256),_s2=_s1,_=_s2["v"]["i8"][0]=8,_s3=function(_s4,_s5,_s6,_){while(1){if(_s6>=256){if(_s4>=256){return E(_);}else{var _s7=imul(2,_s4)|0,_s8=_s5+1|0,_s9=_s4;_s4=_s7;_s5=_s8;_s6=_s9;continue;}}else{var _=_s2["v"]["i8"][_s6]=_s5,_s9=_s6+_s4|0;_s6=_s9;continue;}}},_=B(_s3(2,0,1,_));return _s2;}),_sa=function(_sb,_sc){var _sd=hs_int64ToInt(_sb),_se=E(_s0),_sf=_se["v"]["i8"][(255&_sd>>>0)>>>0&4294967295];if(_sc>_sf){if(_sf>=8){var _sg=hs_uncheckedIShiftRA64(_sb,8),_sh=function(_si,_sj){while(1){var _sk=B((function(_sl,_sm){var _sn=hs_int64ToInt(_sl),_so=_se["v"]["i8"][(255&_sn>>>0)>>>0&4294967295];if(_sm>_so){if(_so>=8){var _sp=hs_uncheckedIShiftRA64(_sl,8),_sq=_sm-8|0;_si=_sp;_sj=_sq;return __continue;}else{return new T2(0,new T(function(){var _sr=hs_uncheckedIShiftRA64(_sl,_so);return B(_rT(_sr));}),_sm-_so|0);}}else{return new T2(0,new T(function(){var _ss=hs_uncheckedIShiftRA64(_sl,_sm);return B(_rT(_ss));}),0);}})(_si,_sj));if(_sk!=__continue){return _sk;}}};return new F(function(){return _sh(_sg,_sc-8|0);});}else{return new T2(0,new T(function(){var _st=hs_uncheckedIShiftRA64(_sb,_sf);return B(_rT(_st));}),_sc-_sf|0);}}else{return new T2(0,new T(function(){var _su=hs_uncheckedIShiftRA64(_sb,_sc);return B(_rT(_su));}),0);}},_sv=function(_sw){var _sx=hs_intToInt64(_sw);return E(_sx);},_sy=function(_sz){var _sA=E(_sz);if(!_sA._){return new F(function(){return _sv(_sA.a);});}else{return new F(function(){return I_toInt64(_sA.a);});}},_sB=function(_sC){return I_toInt(_sC)>>>0;},_sD=function(_sE){var _sF=E(_sE);if(!_sF._){return _sF.a>>>0;}else{return new F(function(){return _sB(_sF.a);});}},_sG=function(_sH){var _sI=B(_rO(_sH)),_sJ=_sI.a,_sK=_sI.b;if(_sK<0){var _sL=function(_sM){if(!_sM){return new T2(0,E(_sJ),B(_52(_3k, -_sK)));}else{var _sN=B(_sa(B(_sy(_sJ)), -_sK));return new T2(0,E(_sN.a),B(_52(_3k,_sN.b)));}};if(!((B(_sD(_sJ))&1)>>>0)){return new F(function(){return _sL(1);});}else{return new F(function(){return _sL(0);});}}else{return new T2(0,B(_52(_sJ,_sK)),_3k);}},_sO=function(_sP){var _sQ=B(_sG(E(_sP)));return new T2(0,E(_sQ.a),E(_sQ.b));},_sR=new T3(0,_jj,_ko,_sO),_sS=function(_sT){return E(E(_sT).a);},_sU=function(_sV){return E(E(_sV).a);},_sW=function(_sX,_sY){if(_sX<=_sY){var _sZ=function(_t0){return new T2(1,_t0,new T(function(){if(_t0!=_sY){return B(_sZ(_t0+1|0));}else{return __Z;}}));};return new F(function(){return _sZ(_sX);});}else{return __Z;}},_t1=function(_t2){return new F(function(){return _sW(E(_t2),2147483647);});},_t3=function(_t4,_t5,_t6){if(_t6<=_t5){var _t7=new T(function(){var _t8=_t5-_t4|0,_t9=function(_ta){return (_ta>=(_t6-_t8|0))?new T2(1,_ta,new T(function(){return B(_t9(_ta+_t8|0));})):new T2(1,_ta,_w);};return B(_t9(_t5));});return new T2(1,_t4,_t7);}else{return (_t6<=_t4)?new T2(1,_t4,_w):__Z;}},_tb=function(_tc,_td,_te){if(_te>=_td){var _tf=new T(function(){var _tg=_td-_tc|0,_th=function(_ti){return (_ti<=(_te-_tg|0))?new T2(1,_ti,new T(function(){return B(_th(_ti+_tg|0));})):new T2(1,_ti,_w);};return B(_th(_td));});return new T2(1,_tc,_tf);}else{return (_te>=_tc)?new T2(1,_tc,_w):__Z;}},_tj=function(_tk,_tl){if(_tl<_tk){return new F(function(){return _t3(_tk,_tl,-2147483648);});}else{return new F(function(){return _tb(_tk,_tl,2147483647);});}},_tm=function(_tn,_to){return new F(function(){return _tj(E(_tn),E(_to));});},_tp=function(_tq,_tr,_ts){if(_tr<_tq){return new F(function(){return _t3(_tq,_tr,_ts);});}else{return new F(function(){return _tb(_tq,_tr,_ts);});}},_tt=function(_tu,_tv,_tw){return new F(function(){return _tp(E(_tu),E(_tv),E(_tw));});},_tx=function(_ty,_tz){return new F(function(){return _sW(E(_ty),E(_tz));});},_tA=function(_tB){return E(_tB);},_tC=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_tD=new T(function(){return B(err(_tC));}),_tE=function(_tF){var _tG=E(_tF);return (_tG==(-2147483648))?E(_tD):_tG-1|0;},_tH=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_tI=new T(function(){return B(err(_tH));}),_tJ=function(_tK){var _tL=E(_tK);return (_tL==2147483647)?E(_tI):_tL+1|0;},_tM={_:0,a:_tJ,b:_tE,c:_tA,d:_tA,e:_t1,f:_tm,g:_tx,h:_tt},_tN=function(_tO,_tP){if(_tO<=0){if(_tO>=0){return new F(function(){return quot(_tO,_tP);});}else{if(_tP<=0){return new F(function(){return quot(_tO,_tP);});}else{return quot(_tO+1|0,_tP)-1|0;}}}else{if(_tP>=0){if(_tO>=0){return new F(function(){return quot(_tO,_tP);});}else{if(_tP<=0){return new F(function(){return quot(_tO,_tP);});}else{return quot(_tO+1|0,_tP)-1|0;}}}else{return quot(_tO-1|0,_tP)-1|0;}}},_tQ=0,_tR=new T(function(){return B(_4p(_tQ));}),_tS=new T(function(){return die(_tR);}),_tT=function(_tU,_tV){var _tW=E(_tV);switch(_tW){case -1:var _tX=E(_tU);if(_tX==(-2147483648)){return E(_tS);}else{return new F(function(){return _tN(_tX,-1);});}break;case 0:return E(_4t);default:return new F(function(){return _tN(_tU,_tW);});}},_tY=function(_tZ,_u0){return new F(function(){return _tT(E(_tZ),E(_u0));});},_u1=0,_u2=new T2(0,_tS,_u1),_u3=function(_u4,_u5){var _u6=E(_u4),_u7=E(_u5);switch(_u7){case -1:var _u8=E(_u6);if(_u8==(-2147483648)){return E(_u2);}else{if(_u8<=0){if(_u8>=0){var _u9=quotRemI(_u8,-1);return new T2(0,_u9.a,_u9.b);}else{var _ua=quotRemI(_u8,-1);return new T2(0,_ua.a,_ua.b);}}else{var _ub=quotRemI(_u8-1|0,-1);return new T2(0,_ub.a-1|0,(_ub.b+(-1)|0)+1|0);}}break;case 0:return E(_4t);default:if(_u6<=0){if(_u6>=0){var _uc=quotRemI(_u6,_u7);return new T2(0,_uc.a,_uc.b);}else{if(_u7<=0){var _ud=quotRemI(_u6,_u7);return new T2(0,_ud.a,_ud.b);}else{var _ue=quotRemI(_u6+1|0,_u7);return new T2(0,_ue.a-1|0,(_ue.b+_u7|0)-1|0);}}}else{if(_u7>=0){if(_u6>=0){var _uf=quotRemI(_u6,_u7);return new T2(0,_uf.a,_uf.b);}else{if(_u7<=0){var _ug=quotRemI(_u6,_u7);return new T2(0,_ug.a,_ug.b);}else{var _uh=quotRemI(_u6+1|0,_u7);return new T2(0,_uh.a-1|0,(_uh.b+_u7|0)-1|0);}}}else{var _ui=quotRemI(_u6-1|0,_u7);return new T2(0,_ui.a-1|0,(_ui.b+_u7|0)+1|0);}}}},_uj=function(_uk,_ul){var _um=_uk%_ul;if(_uk<=0){if(_uk>=0){return E(_um);}else{if(_ul<=0){return E(_um);}else{var _un=E(_um);return (_un==0)?0:_un+_ul|0;}}}else{if(_ul>=0){if(_uk>=0){return E(_um);}else{if(_ul<=0){return E(_um);}else{var _uo=E(_um);return (_uo==0)?0:_uo+_ul|0;}}}else{var _up=E(_um);return (_up==0)?0:_up+_ul|0;}}},_uq=function(_ur,_us){var _ut=E(_us);switch(_ut){case -1:return E(_u1);case 0:return E(_4t);default:return new F(function(){return _uj(E(_ur),_ut);});}},_uu=function(_uv,_uw){var _ux=E(_uv),_uy=E(_uw);switch(_uy){case -1:var _uz=E(_ux);if(_uz==(-2147483648)){return E(_tS);}else{return new F(function(){return quot(_uz,-1);});}break;case 0:return E(_4t);default:return new F(function(){return quot(_ux,_uy);});}},_uA=function(_uB,_uC){var _uD=E(_uB),_uE=E(_uC);switch(_uE){case -1:var _uF=E(_uD);if(_uF==(-2147483648)){return E(_u2);}else{var _uG=quotRemI(_uF,-1);return new T2(0,_uG.a,_uG.b);}break;case 0:return E(_4t);default:var _uH=quotRemI(_uD,_uE);return new T2(0,_uH.a,_uH.b);}},_uI=function(_uJ,_uK){var _uL=E(_uK);switch(_uL){case -1:return E(_u1);case 0:return E(_4t);default:return E(_uJ)%_uL;}},_uM=function(_uN){return new F(function(){return _rR(E(_uN));});},_uO=function(_uP){return new T2(0,E(B(_rR(E(_uP)))),E(_nC));},_uQ=function(_uR,_uS){return imul(E(_uR),E(_uS))|0;},_uT=function(_uU,_uV){return E(_uU)+E(_uV)|0;},_uW=function(_uX,_uY){return E(_uX)-E(_uY)|0;},_uZ=function(_v0){var _v1=E(_v0);return (_v1<0)? -_v1:E(_v1);},_v2=function(_v3){return new F(function(){return _4G(_v3);});},_v4=function(_v5){return  -E(_v5);},_v6=-1,_v7=0,_v8=1,_v9=function(_va){var _vb=E(_va);return (_vb>=0)?(E(_vb)==0)?E(_v7):E(_v8):E(_v6);},_vc={_:0,a:_uT,b:_uW,c:_uQ,d:_v4,e:_uZ,f:_v9,g:_v2},_vd=function(_ve,_vf){return E(_ve)==E(_vf);},_vg=function(_vh,_vi){return E(_vh)!=E(_vi);},_vj=new T2(0,_vd,_vg),_vk=function(_vl,_vm){var _vn=E(_vl),_vo=E(_vm);return (_vn>_vo)?E(_vn):E(_vo);},_vp=function(_vq,_vr){var _vs=E(_vq),_vt=E(_vr);return (_vs>_vt)?E(_vt):E(_vs);},_vu=function(_vv,_vw){return (_vv>=_vw)?(_vv!=_vw)?2:1:0;},_vx=function(_vy,_vz){return new F(function(){return _vu(E(_vy),E(_vz));});},_vA=function(_vB,_vC){return E(_vB)>=E(_vC);},_vD=function(_vE,_vF){return E(_vE)>E(_vF);},_vG=function(_vH,_vI){return E(_vH)<=E(_vI);},_vJ=function(_vK,_vL){return E(_vK)<E(_vL);},_vM={_:0,a:_vj,b:_vx,c:_vJ,d:_vG,e:_vD,f:_vA,g:_vk,h:_vp},_vN=new T3(0,_vc,_vM,_uO),_vO={_:0,a:_vN,b:_tM,c:_uu,d:_uI,e:_tY,f:_uq,g:_uA,h:_u3,i:_uM},_vP=new T1(0,2),_vQ=function(_vR,_vS){while(1){var _vT=E(_vR);if(!_vT._){var _vU=_vT.a,_vV=E(_vS);if(!_vV._){var _vW=_vV.a;if(!(imul(_vU,_vW)|0)){return new T1(0,imul(_vU,_vW)|0);}else{_vR=new T1(1,I_fromInt(_vU));_vS=new T1(1,I_fromInt(_vW));continue;}}else{_vR=new T1(1,I_fromInt(_vU));_vS=_vV;continue;}}else{var _vX=E(_vS);if(!_vX._){_vR=_vT;_vS=new T1(1,I_fromInt(_vX.a));continue;}else{return new T1(1,I_mul(_vT.a,_vX.a));}}}},_vY=function(_vZ,_w0,_w1){while(1){if(!(_w0%2)){var _w2=B(_vQ(_vZ,_vZ)),_w3=quot(_w0,2);_vZ=_w2;_w0=_w3;continue;}else{var _w4=E(_w0);if(_w4==1){return new F(function(){return _vQ(_vZ,_w1);});}else{var _w2=B(_vQ(_vZ,_vZ)),_w5=B(_vQ(_vZ,_w1));_vZ=_w2;_w0=quot(_w4-1|0,2);_w1=_w5;continue;}}}},_w6=function(_w7,_w8){while(1){if(!(_w8%2)){var _w9=B(_vQ(_w7,_w7)),_wa=quot(_w8,2);_w7=_w9;_w8=_wa;continue;}else{var _wb=E(_w8);if(_wb==1){return E(_w7);}else{return new F(function(){return _vY(B(_vQ(_w7,_w7)),quot(_wb-1|0,2),_w7);});}}}},_wc=function(_wd){return E(E(_wd).b);},_we=function(_wf){return E(E(_wf).c);},_wg=new T1(0,0),_wh=function(_wi){return E(E(_wi).d);},_wj=function(_wk,_wl){var _wm=B(_sS(_wk)),_wn=new T(function(){return B(_sU(_wm));}),_wo=new T(function(){return B(A3(_wh,_wk,_wl,new T(function(){return B(A2(_9Z,_wn,_nM));})));});return new F(function(){return A3(_mq,B(_mc(B(_wc(_wm)))),_wo,new T(function(){return B(A2(_9Z,_wn,_wg));}));});},_wp=new T(function(){return B(unCStr("Negative exponent"));}),_wq=new T(function(){return B(err(_wp));}),_wr=function(_ws){return E(E(_ws).c);},_wt=function(_wu,_wv,_ww,_wx){var _wy=B(_sS(_wv)),_wz=new T(function(){return B(_sU(_wy));}),_wA=B(_wc(_wy));if(!B(A3(_we,_wA,_wx,new T(function(){return B(A2(_9Z,_wz,_wg));})))){if(!B(A3(_mq,B(_mc(_wA)),_wx,new T(function(){return B(A2(_9Z,_wz,_wg));})))){var _wB=new T(function(){return B(A2(_9Z,_wz,_nM));}),_wC=new T(function(){return B(A2(_9Z,_wz,_nC));}),_wD=B(_mc(_wA)),_wE=function(_wF,_wG,_wH){while(1){var _wI=B((function(_wJ,_wK,_wL){if(!B(_wj(_wv,_wK))){if(!B(A3(_mq,_wD,_wK,_wC))){var _wM=new T(function(){return B(A3(_wr,_wv,new T(function(){return B(A3(_8w,_wz,_wK,_wC));}),_wB));});_wF=new T(function(){return B(A3(_8u,_wu,_wJ,_wJ));});_wG=_wM;_wH=new T(function(){return B(A3(_8u,_wu,_wJ,_wL));});return __continue;}else{return new F(function(){return A3(_8u,_wu,_wJ,_wL);});}}else{var _wN=_wL;_wF=new T(function(){return B(A3(_8u,_wu,_wJ,_wJ));});_wG=new T(function(){return B(A3(_wr,_wv,_wK,_wB));});_wH=_wN;return __continue;}})(_wF,_wG,_wH));if(_wI!=__continue){return _wI;}}},_wO=function(_wP,_wQ){while(1){var _wR=B((function(_wS,_wT){if(!B(_wj(_wv,_wT))){if(!B(A3(_mq,_wD,_wT,_wC))){var _wU=new T(function(){return B(A3(_wr,_wv,new T(function(){return B(A3(_8w,_wz,_wT,_wC));}),_wB));});return new F(function(){return _wE(new T(function(){return B(A3(_8u,_wu,_wS,_wS));}),_wU,_wS);});}else{return E(_wS);}}else{_wP=new T(function(){return B(A3(_8u,_wu,_wS,_wS));});_wQ=new T(function(){return B(A3(_wr,_wv,_wT,_wB));});return __continue;}})(_wP,_wQ));if(_wR!=__continue){return _wR;}}};return new F(function(){return _wO(_ww,_wx);});}else{return new F(function(){return A2(_9Z,_wu,_nC);});}}else{return E(_wq);}},_wV=new T(function(){return B(err(_wp));}),_wW=function(_wX,_wY){var _wZ=B(_rO(_wY)),_x0=_wZ.a,_x1=_wZ.b,_x2=new T(function(){return B(_sU(new T(function(){return B(_sS(_wX));})));});if(_x1<0){var _x3= -_x1;if(_x3>=0){var _x4=E(_x3);if(!_x4){var _x5=E(_nC);}else{var _x5=B(_w6(_vP,_x4));}if(!B(_4y(_x5,_51))){var _x6=B(_4S(_x0,_x5));return new T2(0,new T(function(){return B(A2(_9Z,_x2,_x6.a));}),new T(function(){return B(_4u(_x6.b,_x1));}));}else{return E(_4t);}}else{return E(_wV);}}else{var _x7=new T(function(){var _x8=new T(function(){return B(_wt(_x2,_vO,new T(function(){return B(A2(_9Z,_x2,_vP));}),_x1));});return B(A3(_8u,_x2,new T(function(){return B(A2(_9Z,_x2,_x0));}),_x8));});return new T2(0,_x7,_7I);}},_x9=function(_xa,_xb){var _xc=B(_wW(_xa,E(_xb))),_xd=_xc.a;if(E(_xc.b)<=0){return E(_xd);}else{var _xe=B(_sU(B(_sS(_xa))));return new F(function(){return A3(_86,_xe,_xd,new T(function(){return B(A2(_9Z,_xe,_3k));}));});}},_xf=function(_xg,_xh){var _xi=B(_wW(_xg,E(_xh))),_xj=_xi.a;if(E(_xi.b)>=0){return E(_xj);}else{var _xk=B(_sU(B(_sS(_xg))));return new F(function(){return A3(_8w,_xk,_xj,new T(function(){return B(A2(_9Z,_xk,_3k));}));});}},_xl=function(_xm,_xn){var _xo=B(_wW(_xm,E(_xn)));return new T2(0,_xo.a,_xo.b);},_xp=function(_xq,_xr){var _xs=B(_wW(_xq,_xr)),_xt=_xs.a,_xu=E(_xs.b),_xv=new T(function(){var _xw=B(_sU(B(_sS(_xq))));if(_xu>=0){return B(A3(_86,_xw,_xt,new T(function(){return B(A2(_9Z,_xw,_3k));})));}else{return B(A3(_8w,_xw,_xt,new T(function(){return B(A2(_9Z,_xw,_3k));})));}}),_xx=function(_xy){var _xz=_xy-0.5;return (_xz>=0)?(E(_xz)==0)?(!B(_wj(_xq,_xt)))?E(_xv):E(_xt):E(_xv):E(_xt);},_xA=E(_xu);if(!_xA){return new F(function(){return _xx(0);});}else{if(_xA<=0){var _xB= -_xA-0.5;return (_xB>=0)?(E(_xB)==0)?(!B(_wj(_xq,_xt)))?E(_xv):E(_xt):E(_xv):E(_xt);}else{return new F(function(){return _xx(_xA);});}}},_xC=function(_xD,_xE){return new F(function(){return _xp(_xD,E(_xE));});},_xF=function(_xG,_xH){return E(B(_wW(_xG,E(_xH))).a);},_xI={_:0,a:_sR,b:_jn,c:_xl,d:_xF,e:_xC,f:_x9,g:_xf},_xJ=new T1(0,1),_xK=function(_xL,_xM){var _xN=E(_xL);return new T2(0,_xN,new T(function(){var _xO=B(_xK(B(_4J(_xN,_xM)),_xM));return new T2(1,_xO.a,_xO.b);}));},_xP=function(_xQ){var _xR=B(_xK(_xQ,_xJ));return new T2(1,_xR.a,_xR.b);},_xS=function(_xT,_xU){var _xV=B(_xK(_xT,new T(function(){return B(_6W(_xU,_xT));})));return new T2(1,_xV.a,_xV.b);},_xW=new T1(0,0),_xX=function(_xY,_xZ){var _y0=E(_xY);if(!_y0._){var _y1=_y0.a,_y2=E(_xZ);return (_y2._==0)?_y1>=_y2.a:I_compareInt(_y2.a,_y1)<=0;}else{var _y3=_y0.a,_y4=E(_xZ);return (_y4._==0)?I_compareInt(_y3,_y4.a)>=0:I_compare(_y3,_y4.a)>=0;}},_y5=function(_y6,_y7,_y8){if(!B(_xX(_y7,_xW))){var _y9=function(_ya){return (!B(_S(_ya,_y8)))?new T2(1,_ya,new T(function(){return B(_y9(B(_4J(_ya,_y7))));})):__Z;};return new F(function(){return _y9(_y6);});}else{var _yb=function(_yc){return (!B(_5c(_yc,_y8)))?new T2(1,_yc,new T(function(){return B(_yb(B(_4J(_yc,_y7))));})):__Z;};return new F(function(){return _yb(_y6);});}},_yd=function(_ye,_yf,_yg){return new F(function(){return _y5(_ye,B(_6W(_yf,_ye)),_yg);});},_yh=function(_yi,_yj){return new F(function(){return _y5(_yi,_xJ,_yj);});},_yk=function(_yl){return new F(function(){return _4G(_yl);});},_ym=function(_yn){return new F(function(){return _6W(_yn,_xJ);});},_yo=function(_yp){return new F(function(){return _4J(_yp,_xJ);});},_yq=function(_yr){return new F(function(){return _rR(E(_yr));});},_ys={_:0,a:_yo,b:_ym,c:_yq,d:_yk,e:_xP,f:_xS,g:_yh,h:_yd},_yt=function(_yu,_yv){while(1){var _yw=E(_yu);if(!_yw._){var _yx=E(_yw.a);if(_yx==(-2147483648)){_yu=new T1(1,I_fromInt(-2147483648));continue;}else{var _yy=E(_yv);if(!_yy._){return new T1(0,B(_tN(_yx,_yy.a)));}else{_yu=new T1(1,I_fromInt(_yx));_yv=_yy;continue;}}}else{var _yz=_yw.a,_yA=E(_yv);return (_yA._==0)?new T1(1,I_div(_yz,I_fromInt(_yA.a))):new T1(1,I_div(_yz,_yA.a));}}},_yB=function(_yC,_yD){if(!B(_4y(_yD,_wg))){return new F(function(){return _yt(_yC,_yD);});}else{return E(_4t);}},_yE=function(_yF,_yG){while(1){var _yH=E(_yF);if(!_yH._){var _yI=E(_yH.a);if(_yI==(-2147483648)){_yF=new T1(1,I_fromInt(-2147483648));continue;}else{var _yJ=E(_yG);if(!_yJ._){var _yK=_yJ.a;return new T2(0,new T1(0,B(_tN(_yI,_yK))),new T1(0,B(_uj(_yI,_yK))));}else{_yF=new T1(1,I_fromInt(_yI));_yG=_yJ;continue;}}}else{var _yL=E(_yG);if(!_yL._){_yF=_yH;_yG=new T1(1,I_fromInt(_yL.a));continue;}else{var _yM=I_divMod(_yH.a,_yL.a);return new T2(0,new T1(1,_yM.a),new T1(1,_yM.b));}}}},_yN=function(_yO,_yP){if(!B(_4y(_yP,_wg))){var _yQ=B(_yE(_yO,_yP));return new T2(0,_yQ.a,_yQ.b);}else{return E(_4t);}},_yR=function(_yS,_yT){while(1){var _yU=E(_yS);if(!_yU._){var _yV=E(_yU.a);if(_yV==(-2147483648)){_yS=new T1(1,I_fromInt(-2147483648));continue;}else{var _yW=E(_yT);if(!_yW._){return new T1(0,B(_uj(_yV,_yW.a)));}else{_yS=new T1(1,I_fromInt(_yV));_yT=_yW;continue;}}}else{var _yX=_yU.a,_yY=E(_yT);return (_yY._==0)?new T1(1,I_mod(_yX,I_fromInt(_yY.a))):new T1(1,I_mod(_yX,_yY.a));}}},_yZ=function(_z0,_z1){if(!B(_4y(_z1,_wg))){return new F(function(){return _yR(_z0,_z1);});}else{return E(_4t);}},_z2=function(_z3,_z4){while(1){var _z5=E(_z3);if(!_z5._){var _z6=E(_z5.a);if(_z6==(-2147483648)){_z3=new T1(1,I_fromInt(-2147483648));continue;}else{var _z7=E(_z4);if(!_z7._){return new T1(0,quot(_z6,_z7.a));}else{_z3=new T1(1,I_fromInt(_z6));_z4=_z7;continue;}}}else{var _z8=_z5.a,_z9=E(_z4);return (_z9._==0)?new T1(0,I_toInt(I_quot(_z8,I_fromInt(_z9.a)))):new T1(1,I_quot(_z8,_z9.a));}}},_za=function(_zb,_zc){if(!B(_4y(_zc,_wg))){return new F(function(){return _z2(_zb,_zc);});}else{return E(_4t);}},_zd=function(_ze,_zf){if(!B(_4y(_zf,_wg))){var _zg=B(_4S(_ze,_zf));return new T2(0,_zg.a,_zg.b);}else{return E(_4t);}},_zh=function(_zi,_zj){while(1){var _zk=E(_zi);if(!_zk._){var _zl=E(_zk.a);if(_zl==(-2147483648)){_zi=new T1(1,I_fromInt(-2147483648));continue;}else{var _zm=E(_zj);if(!_zm._){return new T1(0,_zl%_zm.a);}else{_zi=new T1(1,I_fromInt(_zl));_zj=_zm;continue;}}}else{var _zn=_zk.a,_zo=E(_zj);return (_zo._==0)?new T1(1,I_rem(_zn,I_fromInt(_zo.a))):new T1(1,I_rem(_zn,_zo.a));}}},_zp=function(_zq,_zr){if(!B(_4y(_zr,_wg))){return new F(function(){return _zh(_zq,_zr);});}else{return E(_4t);}},_zs=function(_zt){return E(_zt);},_zu=function(_zv){return E(_zv);},_zw=function(_zx){var _zy=E(_zx);if(!_zy._){var _zz=E(_zy.a);return (_zz==(-2147483648))?E(_7A):(_zz<0)?new T1(0, -_zz):E(_zy);}else{var _zA=_zy.a;return (I_compareInt(_zA,0)>=0)?E(_zy):new T1(1,I_negate(_zA));}},_zB=new T1(0,0),_zC=new T1(0,-1),_zD=function(_zE){var _zF=E(_zE);if(!_zF._){var _zG=_zF.a;return (_zG>=0)?(E(_zG)==0)?E(_zB):E(_5k):E(_zC);}else{var _zH=I_compareInt(_zF.a,0);return (_zH<=0)?(E(_zH)==0)?E(_zB):E(_zC):E(_5k);}},_zI={_:0,a:_4J,b:_6W,c:_vQ,d:_7B,e:_zw,f:_zD,g:_zu},_zJ=function(_zK,_zL){var _zM=E(_zK);if(!_zM._){var _zN=_zM.a,_zO=E(_zL);return (_zO._==0)?_zN!=_zO.a:(I_compareInt(_zO.a,_zN)==0)?false:true;}else{var _zP=_zM.a,_zQ=E(_zL);return (_zQ._==0)?(I_compareInt(_zP,_zQ.a)==0)?false:true:(I_compare(_zP,_zQ.a)==0)?false:true;}},_zR=new T2(0,_4y,_zJ),_zS=function(_zT,_zU){return (!B(_6H(_zT,_zU)))?E(_zT):E(_zU);},_zV=function(_zW,_zX){return (!B(_6H(_zW,_zX)))?E(_zX):E(_zW);},_zY={_:0,a:_zR,b:_3l,c:_S,d:_6H,e:_5c,f:_xX,g:_zS,h:_zV},_zZ=function(_A0){return new T2(0,E(_A0),E(_nC));},_A1=new T3(0,_zI,_zY,_zZ),_A2={_:0,a:_A1,b:_ys,c:_za,d:_zp,e:_yB,f:_yZ,g:_zd,h:_yN,i:_zs},_A3=function(_A4){return E(E(_A4).b);},_A5=function(_A6){return E(E(_A6).g);},_A7=new T1(0,1),_A8=function(_A9,_Aa,_Ab){var _Ac=B(_A3(_A9)),_Ad=B(_8s(_Ac)),_Ae=new T(function(){var _Af=new T(function(){var _Ag=new T(function(){var _Ah=new T(function(){return B(A3(_A5,_A9,_A2,new T(function(){return B(A3(_a9,_Ac,_Aa,_Ab));})));});return B(A2(_9Z,_Ad,_Ah));}),_Ai=new T(function(){return B(A2(_88,_Ad,new T(function(){return B(A2(_9Z,_Ad,_A7));})));});return B(A3(_8u,_Ad,_Ai,_Ag));});return B(A3(_8u,_Ad,_Af,_Ab));});return new F(function(){return A3(_86,_Ad,_Aa,_Ae);});},_Aj=1.5707963267948966,_Ak=function(_Al){return 0.2/Math.cos(B(_A8(_xI,_Al,_Aj))-0.7853981633974483);},_Am=0,_An=new T(function(){var _Ao=B(_qs(_Ak,1.2,_Am,_Am,_rL,_Am,_Am,_Am,_Am,_Am,_rL,_rL,_rL));return {_:0,a:E(_Ao.a),b:E(_rM),c:E(_il),d:E(_Ao.d),e:E(_Ao.e),f:E(_Ao.f),g:E(_Ao.g),h:_Ao.h,i:_Ao.i,j:_Ao.j};}),_Ap=0,_Aq=0.3,_Ar=function(_As){return E(_Aq);},_At=new T(function(){var _Au=B(_qs(_Ar,1.2,_rL,_Am,_rL,_Am,_Am,_Am,_Am,_Am,_rL,_rL,_rL));return {_:0,a:E(_Au.a),b:E(_Au.b),c:E(_Au.c),d:E(_Au.d),e:E(_Au.e),f:E(_Au.f),g:E(_Au.g),h:_Au.h,i:_Au.i,j:_Au.j};}),_Av=new T(function(){var _Aw=B(_qs(_Ar,1.2,_rL,_rL,_Am,_Am,_Am,_Am,_Am,_Am,_rL,_rL,_rL));return {_:0,a:E(_Aw.a),b:E(_Aw.b),c:E(_Aw.c),d:E(_Aw.d),e:E(_Aw.e),f:E(_Aw.f),g:E(_Aw.g),h:_Aw.h,i:_Aw.i,j:_Aw.j};}),_Ax=2,_Ay=function(_Az){return 0.3/Math.cos(B(_A8(_xI,_Az,_Aj))-0.7853981633974483);},_AA=new T(function(){var _AB=B(_qs(_Ay,1.2,_Ax,_rL,_rL,_Am,_Am,_Am,_Am,_Am,_rL,_rL,_rL));return {_:0,a:E(_AB.a),b:E(_AB.b),c:E(_AB.c),d:E(_AB.d),e:E(_AB.e),f:E(_AB.f),g:E(_AB.g),h:_AB.h,i:_AB.i,j:_AB.j};}),_AC=new T2(1,_AA,_w),_AD=new T2(1,_Av,_AC),_AE=new T2(1,_At,_AD),_AF=new T2(1,_An,_AE),_AG=new T(function(){return B(unCStr("Negative range size"));}),_AH=new T(function(){return B(err(_AG));}),_AI=function(_){var _AJ=B(_ic(_AF,0))-1|0,_AK=function(_AL){if(_AL>=0){var _AM=newArr(_AL,_ii),_AN=_AM,_AO=E(_AL);if(!_AO){return new T4(0,E(_Ap),E(_AJ),0,_AN);}else{var _AP=function(_AQ,_AR,_){while(1){var _AS=E(_AQ);if(!_AS._){return E(_);}else{var _=_AN[_AR]=_AS.a;if(_AR!=(_AO-1|0)){var _AT=_AR+1|0;_AQ=_AS.b;_AR=_AT;continue;}else{return E(_);}}}},_=B((function(_AU,_AV,_AW,_){var _=_AN[_AW]=_AU;if(_AW!=(_AO-1|0)){return new F(function(){return _AP(_AV,_AW+1|0,_);});}else{return E(_);}})(_An,_AE,0,_));return new T4(0,E(_Ap),E(_AJ),_AO,_AN);}}else{return E(_AH);}};if(0>_AJ){return new F(function(){return _AK(0);});}else{return new F(function(){return _AK(_AJ+1|0);});}},_AX=function(_AY){var _AZ=B(A1(_AY,_));return E(_AZ);},_B0=new T(function(){return B(_AX(_AI));}),_B1="enclose",_B2="outline",_B3="polygon",_B4="z",_B5="y",_B6="x",_B7=function(_B8){return new F(function(){return _kB(new T2(1,new T2(0,_B6,new T(function(){return E(E(E(E(_B8).d).a).a);})),new T2(1,new T2(0,_B5,new T(function(){return E(E(E(E(_B8).d).a).b);})),new T2(1,new T2(0,_B4,new T(function(){return E(E(E(E(_B8).d).a).c);})),new T2(1,new T2(0,_B3,new T(function(){return E(_B8).h;})),new T2(1,new T2(0,_B2,new T(function(){return E(_B8).i;})),new T2(1,new T2(0,_B1,new T(function(){return E(_B8).j;})),_w)))))));});},_B9=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_Ba=new T(function(){return B(err(_B9));}),_Bb=new T(function(){return eval("__strict(drawObjects)");}),_Bc=new T(function(){return eval("__strict(draw)");}),_Bd=function(_Be,_Bf){var _Bg=jsShowI(_Be);return new F(function(){return _n(fromJSStr(_Bg),_Bf);});},_Bh=function(_Bi,_Bj,_Bk){if(_Bj>=0){return new F(function(){return _Bd(_Bj,_Bk);});}else{if(_Bi<=6){return new F(function(){return _Bd(_Bj,_Bk);});}else{return new T2(1,_11,new T(function(){var _Bl=jsShowI(_Bj);return B(_n(fromJSStr(_Bl),new T2(1,_10,_Bk)));}));}}},_Bm=new T(function(){return B(unCStr(")"));}),_Bn=function(_Bo,_Bp){var _Bq=new T(function(){var _Br=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Bh(0,_Bo,_w)),_Bm));})));},1);return B(_n(B(_Bh(0,_Bp,_w)),_Br));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Bq)));});},_Bs=new T2(1,_kA,_w),_Bt=function(_Bu){return E(_Bu);},_Bv=function(_Bw){return E(_Bw);},_Bx=function(_By,_Bz){return E(_Bz);},_BA=function(_BB,_BC){return E(_BB);},_BD=function(_BE){return E(_BE);},_BF=new T2(0,_BD,_BA),_BG=function(_BH,_BI){return E(_BH);},_BJ=new T5(0,_BF,_Bv,_Bt,_Bx,_BG),_BK="flipped2",_BL="flipped1",_BM="c1y",_BN="c1x",_BO="w2z",_BP="w2y",_BQ="w2x",_BR="w1z",_BS="w1y",_BT="w1x",_BU="d2z",_BV="d2y",_BW="d2x",_BX="d1z",_BY="d1y",_BZ="d1x",_C0="c2y",_C1="c2x",_C2=function(_C3,_){var _C4=__get(_C3,E(_BT)),_C5=__get(_C3,E(_BS)),_C6=__get(_C3,E(_BR)),_C7=__get(_C3,E(_BQ)),_C8=__get(_C3,E(_BP)),_C9=__get(_C3,E(_BO)),_Ca=__get(_C3,E(_BN)),_Cb=__get(_C3,E(_BM)),_Cc=__get(_C3,E(_C1)),_Cd=__get(_C3,E(_C0)),_Ce=__get(_C3,E(_BZ)),_Cf=__get(_C3,E(_BY)),_Cg=__get(_C3,E(_BX)),_Ch=__get(_C3,E(_BW)),_Ci=__get(_C3,E(_BV)),_Cj=__get(_C3,E(_BU)),_Ck=__get(_C3,E(_BL)),_Cl=__get(_C3,E(_BK));return {_:0,a:E(new T3(0,E(_C4),E(_C5),E(_C6))),b:E(new T3(0,E(_C7),E(_C8),E(_C9))),c:E(new T2(0,E(_Ca),E(_Cb))),d:E(new T2(0,E(_Cc),E(_Cd))),e:E(new T3(0,E(_Ce),E(_Cf),E(_Cg))),f:E(new T3(0,E(_Ch),E(_Ci),E(_Cj))),g:E(_Ck),h:E(_Cl)};},_Cm=function(_Cn,_){var _Co=E(_Cn);if(!_Co._){return _w;}else{var _Cp=B(_C2(E(_Co.a),_)),_Cq=B(_Cm(_Co.b,_));return new T2(1,_Cp,_Cq);}},_Cr=function(_Cs){var _Ct=E(_Cs);return (E(_Ct.b)-E(_Ct.a)|0)+1|0;},_Cu=function(_Cv,_Cw){var _Cx=E(_Cv),_Cy=E(_Cw);return (E(_Cx.a)>_Cy)?false:_Cy<=E(_Cx.b);},_Cz=function(_CA){return new F(function(){return _Bh(0,E(_CA),_w);});},_CB=function(_CC,_CD,_CE){return new F(function(){return _Bh(E(_CC),E(_CD),_CE);});},_CF=function(_CG,_CH){return new F(function(){return _Bh(0,E(_CG),_CH);});},_CI=function(_CJ,_CK){return new F(function(){return _49(_CF,_CJ,_CK);});},_CL=new T3(0,_CB,_Cz,_CI),_CM=0,_CN=function(_CO,_CP,_CQ){return new F(function(){return A1(_CO,new T2(1,_46,new T(function(){return B(A1(_CP,_CQ));})));});},_CR=new T(function(){return B(unCStr("foldr1"));}),_CS=new T(function(){return B(_n1(_CR));}),_CT=function(_CU,_CV){var _CW=E(_CV);if(!_CW._){return E(_CS);}else{var _CX=_CW.a,_CY=E(_CW.b);if(!_CY._){return E(_CX);}else{return new F(function(){return A2(_CU,_CX,new T(function(){return B(_CT(_CU,_CY));}));});}}},_CZ=new T(function(){return B(unCStr(" out of range "));}),_D0=new T(function(){return B(unCStr("}.index: Index "));}),_D1=new T(function(){return B(unCStr("Ix{"));}),_D2=new T2(1,_10,_w),_D3=new T2(1,_10,_D2),_D4=0,_D5=function(_D6){return E(E(_D6).a);},_D7=function(_D8,_D9,_Da,_Db,_Dc){var _Dd=new T(function(){var _De=new T(function(){var _Df=new T(function(){var _Dg=new T(function(){var _Dh=new T(function(){return B(A3(_CT,_CN,new T2(1,new T(function(){return B(A3(_D5,_Da,_D4,_Db));}),new T2(1,new T(function(){return B(A3(_D5,_Da,_D4,_Dc));}),_w)),_D3));});return B(_n(_CZ,new T2(1,_11,new T2(1,_11,_Dh))));});return B(A(_D5,[_Da,_CM,_D9,new T2(1,_10,_Dg)]));});return B(_n(_D0,new T2(1,_11,_Df)));},1);return B(_n(_D8,_De));},1);return new F(function(){return err(B(_n(_D1,_Dd)));});},_Di=function(_Dj,_Dk,_Dl,_Dm,_Dn){return new F(function(){return _D7(_Dj,_Dk,_Dn,_Dl,_Dm);});},_Do=function(_Dp,_Dq,_Dr,_Ds){var _Dt=E(_Dr);return new F(function(){return _Di(_Dp,_Dq,_Dt.a,_Dt.b,_Ds);});},_Du=function(_Dv,_Dw,_Dx,_Dy){return new F(function(){return _Do(_Dy,_Dx,_Dw,_Dv);});},_Dz=new T(function(){return B(unCStr("Int"));}),_DA=function(_DB,_DC){return new F(function(){return _Du(_CL,_DC,_DB,_Dz);});},_DD=function(_DE,_DF){var _DG=E(_DE),_DH=E(_DG.a),_DI=E(_DF);if(_DH>_DI){return new F(function(){return _DA(_DI,_DG);});}else{if(_DI>E(_DG.b)){return new F(function(){return _DA(_DI,_DG);});}else{return _DI-_DH|0;}}},_DJ=function(_DK){var _DL=E(_DK);return new F(function(){return _tx(_DL.a,_DL.b);});},_DM=function(_DN){var _DO=E(_DN),_DP=E(_DO.a),_DQ=E(_DO.b);return (_DP>_DQ)?E(_CM):(_DQ-_DP|0)+1|0;},_DR=function(_DS,_DT){return new F(function(){return _uW(_DT,E(_DS).a);});},_DU={_:0,a:_vM,b:_DJ,c:_DD,d:_DR,e:_Cu,f:_DM,g:_Cr},_DV=function(_DW,_DX,_){while(1){var _DY=B((function(_DZ,_E0,_){var _E1=E(_DZ);if(!_E1._){return new T2(0,_kA,_E0);}else{var _E2=B(A2(_E1.a,_E0,_));_DW=_E1.b;_DX=new T(function(){return E(E(_E2).b);});return __continue;}})(_DW,_DX,_));if(_DY!=__continue){return _DY;}}},_E3=function(_E4,_E5){return new T2(1,_E4,_E5);},_E6=function(_E7,_E8){var _E9=E(_E8);return new T2(0,_E9.a,_E9.b);},_Ea=function(_Eb){return E(E(_Eb).f);},_Ec=function(_Ed,_Ee,_Ef){var _Eg=E(_Ee),_Eh=_Eg.a,_Ei=_Eg.b,_Ej=function(_){var _Ek=B(A2(_Ea,_Ed,_Eg));if(_Ek>=0){var _El=newArr(_Ek,_ii),_Em=_El,_En=E(_Ek);if(!_En){return new T(function(){return new T4(0,E(_Eh),E(_Ei),0,_Em);});}else{var _Eo=function(_Ep,_Eq,_){while(1){var _Er=E(_Ep);if(!_Er._){return E(_);}else{var _=_Em[_Eq]=_Er.a;if(_Eq!=(_En-1|0)){var _Es=_Eq+1|0;_Ep=_Er.b;_Eq=_Es;continue;}else{return E(_);}}}},_=B(_Eo(_Ef,0,_));return new T(function(){return new T4(0,E(_Eh),E(_Ei),_En,_Em);});}}else{return E(_AH);}};return new F(function(){return _AX(_Ej);});},_Et=function(_Eu,_Ev,_Ew,_Ex){var _Ey=new T(function(){var _Ez=E(_Ex),_EA=_Ez.c-1|0,_EB=new T(function(){return B(A2(_dU,_Ev,_w));});if(0<=_EA){var _EC=new T(function(){return B(_a5(_Ev));}),_ED=function(_EE){var _EF=new T(function(){var _EG=new T(function(){return B(A1(_Ew,new T(function(){return E(_Ez.d[_EE]);})));});return B(A3(_ad,_EC,_E3,_EG));});return new F(function(){return A3(_ab,_Ev,_EF,new T(function(){if(_EE!=_EA){return B(_ED(_EE+1|0));}else{return E(_EB);}}));});};return B(_ED(0));}else{return E(_EB);}}),_EH=new T(function(){return B(_E6(_Eu,_Ex));});return new F(function(){return A3(_ad,B(_a5(_Ev)),function(_EI){return new F(function(){return _Ec(_Eu,_EH,_EI);});},_Ey);});},_EJ=function(_EK,_EL,_EM,_EN,_EO,_EP,_EQ,_ER,_ES){var _ET=B(_8u(_EK));return new T2(0,new T3(0,E(B(A1(B(A1(_ET,_EL)),_EP))),E(B(A1(B(A1(_ET,_EM)),_EQ))),E(B(A1(B(A1(_ET,_EN)),_ER)))),B(A1(B(A1(_ET,_EO)),_ES)));},_EU=function(_EV,_EW,_EX,_EY,_EZ,_F0,_F1,_F2,_F3){var _F4=B(_86(_EV));return new T2(0,new T3(0,E(B(A1(B(A1(_F4,_EW)),_F0))),E(B(A1(B(A1(_F4,_EX)),_F1))),E(B(A1(B(A1(_F4,_EY)),_F2)))),B(A1(B(A1(_F4,_EZ)),_F3)));},_F5=1.0e-2,_F6=function(_F7,_F8,_F9,_Fa,_Fb,_Fc,_Fd,_Fe,_Ff,_Fg,_Fh,_Fi,_Fj,_Fk,_Fl,_Fm,_Fn,_Fo){var _Fp=B(_EJ(_jj,_Fe,_Ff,_Fg,_Fh,_F5,_F5,_F5,_F5)),_Fq=E(_Fp.a),_Fr=B(_EU(_jj,_Fa,_Fb,_Fc,_Fd,_Fq.a,_Fq.b,_Fq.c,_Fp.b)),_Fs=E(_Fr.a);return new F(function(){return _pJ(_F7,_F8,_F9,_Fs.a,_Fs.b,_Fs.c,_Fr.b,_Fe,_Ff,_Fg,_Fh,_Fi,_Fj,_Fk,_Fl,_Fm,_Fn,_Fo);});},_Ft=function(_Fu){var _Fv=E(_Fu),_Fw=E(_Fv.d),_Fx=E(_Fw.a),_Fy=E(_Fv.e),_Fz=E(_Fy.a),_FA=E(_Fv.f),_FB=B(_F6(_Fv.a,_Fv.b,_Fv.c,_Fx.a,_Fx.b,_Fx.c,_Fw.b,_Fz.a,_Fz.b,_Fz.c,_Fy.b,_FA.a,_FA.b,_FA.c,_Fv.g,_Fv.h,_Fv.i,_Fv.j));return {_:0,a:E(_FB.a),b:E(_FB.b),c:E(_FB.c),d:E(_FB.d),e:E(_FB.e),f:E(_FB.f),g:E(_FB.g),h:_FB.h,i:_FB.i,j:_FB.j};},_FC=function(_FD,_FE,_FF,_FG,_FH,_FI,_FJ,_FK,_FL){var _FM=B(_8s(B(_8q(_FD))));return new F(function(){return A3(_86,_FM,new T(function(){return B(_le(_FD,_FE,_FF,_FG,_FI,_FJ,_FK));}),new T(function(){return B(A3(_8u,_FM,_FH,_FL));}));});},_FN=new T(function(){return B(unCStr("base"));}),_FO=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_FP=new T(function(){return B(unCStr("IOException"));}),_FQ=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_FN,_FO,_FP),_FR=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_FQ,_w,_w),_FS=function(_FT){return E(_FR);},_FU=function(_FV){var _FW=E(_FV);return new F(function(){return _3G(B(_3E(_FW.a)),_FS,_FW.b);});},_FX=new T(function(){return B(unCStr(": "));}),_FY=new T(function(){return B(unCStr(")"));}),_FZ=new T(function(){return B(unCStr(" ("));}),_G0=new T(function(){return B(unCStr("interrupted"));}),_G1=new T(function(){return B(unCStr("system error"));}),_G2=new T(function(){return B(unCStr("unsatisified constraints"));}),_G3=new T(function(){return B(unCStr("user error"));}),_G4=new T(function(){return B(unCStr("permission denied"));}),_G5=new T(function(){return B(unCStr("illegal operation"));}),_G6=new T(function(){return B(unCStr("end of file"));}),_G7=new T(function(){return B(unCStr("resource exhausted"));}),_G8=new T(function(){return B(unCStr("resource busy"));}),_G9=new T(function(){return B(unCStr("does not exist"));}),_Ga=new T(function(){return B(unCStr("already exists"));}),_Gb=new T(function(){return B(unCStr("resource vanished"));}),_Gc=new T(function(){return B(unCStr("timeout"));}),_Gd=new T(function(){return B(unCStr("unsupported operation"));}),_Ge=new T(function(){return B(unCStr("hardware fault"));}),_Gf=new T(function(){return B(unCStr("inappropriate type"));}),_Gg=new T(function(){return B(unCStr("invalid argument"));}),_Gh=new T(function(){return B(unCStr("failed"));}),_Gi=new T(function(){return B(unCStr("protocol error"));}),_Gj=function(_Gk,_Gl){switch(E(_Gk)){case 0:return new F(function(){return _n(_Ga,_Gl);});break;case 1:return new F(function(){return _n(_G9,_Gl);});break;case 2:return new F(function(){return _n(_G8,_Gl);});break;case 3:return new F(function(){return _n(_G7,_Gl);});break;case 4:return new F(function(){return _n(_G6,_Gl);});break;case 5:return new F(function(){return _n(_G5,_Gl);});break;case 6:return new F(function(){return _n(_G4,_Gl);});break;case 7:return new F(function(){return _n(_G3,_Gl);});break;case 8:return new F(function(){return _n(_G2,_Gl);});break;case 9:return new F(function(){return _n(_G1,_Gl);});break;case 10:return new F(function(){return _n(_Gi,_Gl);});break;case 11:return new F(function(){return _n(_Gh,_Gl);});break;case 12:return new F(function(){return _n(_Gg,_Gl);});break;case 13:return new F(function(){return _n(_Gf,_Gl);});break;case 14:return new F(function(){return _n(_Ge,_Gl);});break;case 15:return new F(function(){return _n(_Gd,_Gl);});break;case 16:return new F(function(){return _n(_Gc,_Gl);});break;case 17:return new F(function(){return _n(_Gb,_Gl);});break;default:return new F(function(){return _n(_G0,_Gl);});}},_Gm=new T(function(){return B(unCStr("}"));}),_Gn=new T(function(){return B(unCStr("{handle: "));}),_Go=function(_Gp,_Gq,_Gr,_Gs,_Gt,_Gu){var _Gv=new T(function(){var _Gw=new T(function(){var _Gx=new T(function(){var _Gy=E(_Gs);if(!_Gy._){return E(_Gu);}else{var _Gz=new T(function(){return B(_n(_Gy,new T(function(){return B(_n(_FY,_Gu));},1)));},1);return B(_n(_FZ,_Gz));}},1);return B(_Gj(_Gq,_Gx));}),_GA=E(_Gr);if(!_GA._){return E(_Gw);}else{return B(_n(_GA,new T(function(){return B(_n(_FX,_Gw));},1)));}}),_GB=E(_Gt);if(!_GB._){var _GC=E(_Gp);if(!_GC._){return E(_Gv);}else{var _GD=E(_GC.a);if(!_GD._){var _GE=new T(function(){var _GF=new T(function(){return B(_n(_Gm,new T(function(){return B(_n(_FX,_Gv));},1)));},1);return B(_n(_GD.a,_GF));},1);return new F(function(){return _n(_Gn,_GE);});}else{var _GG=new T(function(){var _GH=new T(function(){return B(_n(_Gm,new T(function(){return B(_n(_FX,_Gv));},1)));},1);return B(_n(_GD.a,_GH));},1);return new F(function(){return _n(_Gn,_GG);});}}}else{return new F(function(){return _n(_GB.a,new T(function(){return B(_n(_FX,_Gv));},1));});}},_GI=function(_GJ){var _GK=E(_GJ);return new F(function(){return _Go(_GK.a,_GK.b,_GK.c,_GK.d,_GK.f,_w);});},_GL=function(_GM,_GN,_GO){var _GP=E(_GN);return new F(function(){return _Go(_GP.a,_GP.b,_GP.c,_GP.d,_GP.f,_GO);});},_GQ=function(_GR,_GS){var _GT=E(_GR);return new F(function(){return _Go(_GT.a,_GT.b,_GT.c,_GT.d,_GT.f,_GS);});},_GU=function(_GV,_GW){return new F(function(){return _49(_GQ,_GV,_GW);});},_GX=new T3(0,_GL,_GI,_GU),_GY=new T(function(){return new T5(0,_FS,_GX,_GZ,_FU,_GI);}),_GZ=function(_H0){return new T2(0,_GY,_H0);},_H1=__Z,_H2=7,_H3=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_H4=new T6(0,_H1,_H2,_w,_H3,_H1,_H1),_H5=new T(function(){return B(_GZ(_H4));}),_H6=function(_){return new F(function(){return die(_H5);});},_H7=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_H8=new T6(0,_H1,_H2,_w,_H7,_H1,_H1),_H9=new T(function(){return B(_GZ(_H8));}),_Ha=function(_){return new F(function(){return die(_H9);});},_Hb=function(_Hc,_){return new T2(0,_w,_Hc);},_Hd=0.6,_He=1,_Hf=new T(function(){return B(unCStr(")"));}),_Hg=function(_Hh,_Hi){var _Hj=new T(function(){var _Hk=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Bh(0,_Hh,_w)),_Hf));})));},1);return B(_n(B(_Bh(0,_Hi,_w)),_Hk));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Hj)));});},_Hl=function(_Hm,_Hn){var _Ho=new T(function(){var _Hp=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Bh(0,_Hn,_w)),_Hf));})));},1);return B(_n(B(_Bh(0,_Hm,_w)),_Hp));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Ho)));});},_Hq=function(_Hr){var _Hs=E(_Hr);if(!_Hs._){return E(_Hb);}else{var _Ht=new T(function(){return B(_Hq(_Hs.b));}),_Hu=function(_Hv){var _Hw=E(_Hv);if(!_Hw._){return E(_Ht);}else{var _Hx=_Hw.a,_Hy=new T(function(){return B(_Hu(_Hw.b));}),_Hz=new T(function(){return 0.1*E(E(_Hx).e)/1.0e-2;}),_HA=new T(function(){var _HB=E(_Hx);if(_HB.a!=_HB.b){return E(_He);}else{return E(_Hd);}}),_HC=function(_HD,_){var _HE=E(_HD),_HF=_HE.c,_HG=_HE.d,_HH=E(_HE.a),_HI=E(_HE.b),_HJ=E(_Hx),_HK=_HJ.a,_HL=_HJ.b,_HM=E(_HJ.c),_HN=_HM.b,_HO=E(_HM.a),_HP=_HO.a,_HQ=_HO.b,_HR=_HO.c,_HS=E(_HJ.d),_HT=_HS.b,_HU=E(_HS.a),_HV=_HU.a,_HW=_HU.b,_HX=_HU.c;if(_HH>_HK){return new F(function(){return _Ha(_);});}else{if(_HK>_HI){return new F(function(){return _Ha(_);});}else{if(_HH>_HL){return new F(function(){return _H6(_);});}else{if(_HL>_HI){return new F(function(){return _H6(_);});}else{var _HY=_HK-_HH|0;if(0>_HY){return new F(function(){return _Hg(_HF,_HY);});}else{if(_HY>=_HF){return new F(function(){return _Hg(_HF,_HY);});}else{var _HZ=E(_HG[_HY]),_I0=E(_HZ.c),_I1=_I0.b,_I2=E(_I0.a),_I3=_I2.a,_I4=_I2.b,_I5=_I2.c,_I6=E(_HZ.e),_I7=E(_I6.a),_I8=B(_EJ(_jj,_HP,_HQ,_HR,_HN,_I3,_I4,_I5,_I1)),_I9=E(_I8.a),_Ia=B(_EJ(_jj,_I9.a,_I9.b,_I9.c,_I8.b,_HP,_HQ,_HR,_HN)),_Ib=E(_Ia.a),_Ic=_HL-_HH|0;if(0>_Ic){return new F(function(){return _Hl(_Ic,_HF);});}else{if(_Ic>=_HF){return new F(function(){return _Hl(_Ic,_HF);});}else{var _Id=E(_HG[_Ic]),_Ie=E(_Id.c),_If=_Ie.b,_Ig=E(_Ie.a),_Ih=_Ig.a,_Ii=_Ig.b,_Ij=_Ig.c,_Ik=E(_Id.e),_Il=E(_Ik.a),_Im=B(_EJ(_jj,_HV,_HW,_HX,_HT,_Ih,_Ii,_Ij,_If)),_In=E(_Im.a),_Io=B(_EJ(_jj,_In.a,_In.b,_In.c,_Im.b,_HV,_HW,_HX,_HT)),_Ip=E(_Io.a),_Iq=E(_Ib.a)+E(_Ib.b)+E(_Ib.c)+E(_Ia.b)+E(_Ip.a)+E(_Ip.b)+E(_Ip.c)+E(_Io.b);if(!_Iq){var _Ir=B(A2(_Hy,_HE,_));return new T2(0,new T2(1,_kA,new T(function(){return E(E(_Ir).a);})),new T(function(){return E(E(_Ir).b);}));}else{var _Is=new T(function(){return  -((B(_FC(_jP,_I7.a,_I7.b,_I7.c,_I6.b,_HP,_HQ,_HR,_HN))-B(_FC(_jP,_Il.a,_Il.b,_Il.c,_Ik.b,_HV,_HW,_HX,_HT))-E(_Hz))/_Iq);}),_It=function(_Iu,_Iv,_Iw,_Ix,_){var _Iy=new T(function(){var _Iz=function(_IA,_IB,_IC,_ID,_IE){if(_IA>_HL){return E(_IE);}else{if(_HL>_IB){return E(_IE);}else{var _IF=function(_){var _IG=newArr(_IC,_ii),_IH=_IG,_II=function(_IJ,_){while(1){if(_IJ!=_IC){var _=_IH[_IJ]=_ID[_IJ],_IK=_IJ+1|0;_IJ=_IK;continue;}else{return E(_);}}},_=B(_II(0,_)),_IL=_HL-_IA|0;if(0>_IL){return new F(function(){return _Hl(_IL,_IC);});}else{if(_IL>=_IC){return new F(function(){return _Hl(_IL,_IC);});}else{var _=_IH[_IL]=new T(function(){var _IM=E(_ID[_IL]),_IN=E(_IM.e),_IO=E(_IN.a),_IP=B(_EJ(_jj,_Ih,_Ii,_Ij,_If,_HV,_HW,_HX,_HT)),_IQ=E(_IP.a),_IR=E(_Is)*E(_HA),_IS=B(_EJ(_jj,_IQ.a,_IQ.b,_IQ.c,_IP.b,_IR,_IR,_IR,_IR)),_IT=E(_IS.a),_IU=B(_EU(_jj,_IO.a,_IO.b,_IO.c,_IN.b, -E(_IT.a), -E(_IT.b), -E(_IT.c), -E(_IS.b)));return {_:0,a:E(_IM.a),b:E(_IM.b),c:E(_IM.c),d:E(_IM.d),e:E(new T2(0,E(_IU.a),E(_IU.b))),f:E(_IM.f),g:E(_IM.g),h:_IM.h,i:_IM.i,j:_IM.j};});return new T4(0,E(_IA),E(_IB),_IC,_IH);}}};return new F(function(){return _AX(_IF);});}}};if(_Iu>_HK){return B(_Iz(_Iu,_Iv,_Iw,_Ix,new T4(0,E(_Iu),E(_Iv),_Iw,_Ix)));}else{if(_HK>_Iv){return B(_Iz(_Iu,_Iv,_Iw,_Ix,new T4(0,E(_Iu),E(_Iv),_Iw,_Ix)));}else{var _IV=function(_){var _IW=newArr(_Iw,_ii),_IX=_IW,_IY=function(_IZ,_){while(1){if(_IZ!=_Iw){var _=_IX[_IZ]=_Ix[_IZ],_J0=_IZ+1|0;_IZ=_J0;continue;}else{return E(_);}}},_=B(_IY(0,_)),_J1=_HK-_Iu|0;if(0>_J1){return new F(function(){return _Hg(_Iw,_J1);});}else{if(_J1>=_Iw){return new F(function(){return _Hg(_Iw,_J1);});}else{var _=_IX[_J1]=new T(function(){var _J2=E(_Ix[_J1]),_J3=E(_J2.e),_J4=E(_J3.a),_J5=B(_EJ(_jj,_I3,_I4,_I5,_I1,_HP,_HQ,_HR,_HN)),_J6=E(_J5.a),_J7=E(_Is)*E(_HA),_J8=B(_EJ(_jj,_J6.a,_J6.b,_J6.c,_J5.b,_J7,_J7,_J7,_J7)),_J9=E(_J8.a),_Ja=B(_EU(_jj,_J4.a,_J4.b,_J4.c,_J3.b,_J9.a,_J9.b,_J9.c,_J8.b));return {_:0,a:E(_J2.a),b:E(_J2.b),c:E(_J2.c),d:E(_J2.d),e:E(new T2(0,E(_Ja.a),E(_Ja.b))),f:E(_J2.f),g:E(_J2.g),h:_J2.h,i:_J2.i,j:_J2.j};});return new T4(0,E(_Iu),E(_Iv),_Iw,_IX);}}},_Jb=B(_AX(_IV));return B(_Iz(E(_Jb.a),E(_Jb.b),_Jb.c,_Jb.d,_Jb));}}});return new T2(0,_kA,_Iy);};if(!E(_HJ.f)){var _Jc=B(_It(_HH,_HI,_HF,_HG,_)),_Jd=B(A2(_Hy,new T(function(){return E(E(_Jc).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_Jc).a);}),new T(function(){return E(E(_Jd).a);})),new T(function(){return E(E(_Jd).b);}));}else{if(E(_Is)<0){var _Je=B(A2(_Hy,_HE,_));return new T2(0,new T2(1,_kA,new T(function(){return E(E(_Je).a);})),new T(function(){return E(E(_Je).b);}));}else{var _Jf=B(_It(_HH,_HI,_HF,_HG,_)),_Jg=B(A2(_Hy,new T(function(){return E(E(_Jf).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_Jf).a);}),new T(function(){return E(E(_Jg).a);})),new T(function(){return E(E(_Jg).b);}));}}}}}}}}}}}};return E(_HC);}};return new F(function(){return _Hu(_Hs.a);});}},_Jh=function(_,_Ji){var _Jj=new T(function(){return B(_Hq(E(_Ji).a));}),_Jk=function(_Jl){var _Jm=E(_Jl);return (_Jm==1)?E(new T2(1,_Jj,_w)):new T2(1,_Jj,new T(function(){return B(_Jk(_Jm-1|0));}));},_Jn=B(_DV(B(_Jk(5)),new T(function(){return E(E(_Ji).b);}),_)),_Jo=new T(function(){return B(_Et(_DU,_BJ,_Ft,new T(function(){return E(E(_Jn).b);})));});return new T2(0,_kA,_Jo);},_Jp=function(_Jq,_Jr,_Js,_Jt,_Ju){var _Jv=B(_8s(B(_8q(_Jq))));return new F(function(){return A3(_86,_Jv,new T(function(){return B(A3(_8u,_Jv,_Jr,_Jt));}),new T(function(){return B(A3(_8u,_Jv,_Js,_Ju));}));});},_Jw=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Jx=new T6(0,_H1,_H2,_w,_Jw,_H1,_H1),_Jy=new T(function(){return B(_GZ(_Jx));}),_Jz=function(_){return new F(function(){return die(_Jy);});},_JA=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_JB=new T6(0,_H1,_H2,_w,_JA,_H1,_H1),_JC=new T(function(){return B(_GZ(_JB));}),_JD=function(_){return new F(function(){return die(_JC);});},_JE=false,_JF=true,_JG=function(_JH){var _JI=E(_JH),_JJ=_JI.b,_JK=E(_JI.d),_JL=E(_JI.e),_JM=E(_JL.a),_JN=E(_JI.g),_JO=B(A1(_JJ,_JK.a)),_JP=B(_me(_jP,_JO.a,_JO.b,_JO.c,_JN.a,_JN.b,_JN.c));return {_:0,a:E(_JI.a),b:E(_JJ),c:E(_JI.c),d:E(_JK),e:E(new T2(0,E(new T3(0,E(_JM.a)+E(_JP.a)*1.0e-2,E(_JM.b)+E(_JP.b)*1.0e-2,E(_JM.c)+E(_JP.c)*1.0e-2)),E(_JL.b))),f:E(_JI.f),g:E(_JN),h:_JI.h,i:_JI.i,j:_JI.j};},_JQ=new T(function(){return eval("__strict(collideBound)");}),_JR=new T(function(){return eval("__strict(mouseContact)");}),_JS=new T(function(){return eval("__strict(collide)");}),_JT=function(_JU){var _JV=E(_JU);if(!_JV._){return __Z;}else{return new F(function(){return _n(_JV.a,new T(function(){return B(_JT(_JV.b));},1));});}},_JW=0,_JX=new T3(0,E(_JW),E(_JW),E(_JW)),_JY=new T2(0,E(_JX),E(_JW)),_JZ=new T2(0,_jP,_ko),_K0=new T(function(){return B(_hP(_JZ));}),_K1=function(_K2,_){var _K3=B(_Et(_DU,_BJ,_JG,_K2)),_K4=E(_K3.a),_K5=E(_K3.b);if(_K4<=_K5){var _K6=function(_K7,_K8,_K9,_Ka,_Kb,_){if(_K8>_K7){return new F(function(){return _JD(_);});}else{if(_K7>_K9){return new F(function(){return _JD(_);});}else{var _Kc=new T(function(){var _Kd=_K7-_K8|0;if(0>_Kd){return B(_Hl(_Kd,_Ka));}else{if(_Kd>=_Ka){return B(_Hl(_Kd,_Ka));}else{return E(_Kb[_Kd]);}}}),_Ke=function(_Kf,_Kg,_Kh,_Ki,_Kj,_){var _Kk=E(_Kf);if(!_Kk._){return new T2(0,_w,new T4(0,E(_Kg),E(_Kh),_Ki,_Kj));}else{var _Kl=E(_Kk.a);if(_Kg>_Kl){return new F(function(){return _Jz(_);});}else{if(_Kl>_Kh){return new F(function(){return _Jz(_);});}else{var _Km=_Kl-_Kg|0;if(0>_Km){return new F(function(){return _Hg(_Ki,_Km);});}else{if(_Km>=_Ki){return new F(function(){return _Hg(_Ki,_Km);});}else{var _Kn=__app2(E(_JS),B(_B7(E(_Kc))),B(_B7(E(_Kj[_Km])))),_Ko=__arr2lst(0,_Kn),_Kp=B(_Cm(_Ko,_)),_Kq=B(_Ke(_Kk.b,_Kg,_Kh,_Ki,_Kj,_)),_Kr=new T(function(){var _Ks=new T(function(){return _K7!=_Kl;}),_Kt=function(_Ku){var _Kv=E(_Ku);if(!_Kv._){return __Z;}else{var _Kw=_Kv.b,_Kx=E(_Kv.a),_Ky=E(_Kx.b),_Kz=E(_Kx.a),_KA=E(_Kx.c),_KB=_KA.a,_KC=_KA.b,_KD=E(_Kx.e),_KE=E(_Kx.d),_KF=_KE.a,_KG=_KE.b,_KH=E(_Kx.f),_KI=new T(function(){var _KJ=B(_lo(_jP,_KH.a,_KH.b,_KH.c)),_KK=Math.sqrt(B(_Jp(_jP,_KF,_KG,_KF,_KG)));return new T3(0,_KK*E(_KJ.a),_KK*E(_KJ.b),_KK*E(_KJ.c));}),_KL=new T(function(){var _KM=B(_lo(_jP,_KD.a,_KD.b,_KD.c)),_KN=Math.sqrt(B(_Jp(_jP,_KB,_KC,_KB,_KC)));return new T3(0,_KN*E(_KM.a),_KN*E(_KM.b),_KN*E(_KM.c));}),_KO=new T(function(){var _KP=B(A1(_K0,_Ky)),_KQ=B(_lo(_jP,_KP.a,_KP.b,_KP.c));return new T3(0,E(_KQ.a),E(_KQ.b),E(_KQ.c));}),_KR=new T(function(){var _KS=B(A1(_K0,_Kz)),_KT=B(_lo(_jP,_KS.a,_KS.b,_KS.c));return new T3(0,E(_KT.a),E(_KT.b),E(_KT.c));}),_KU=E(_Ky.a)+ -E(_Kz.a),_KV=E(_Ky.b)+ -E(_Kz.b),_KW=E(_Ky.c)+ -E(_Kz.c),_KX=new T(function(){return Math.sqrt(B(_le(_jP,_KU,_KV,_KW,_KU,_KV,_KW)));}),_KY=new T(function(){var _KZ=1/E(_KX);return new T3(0,_KU*_KZ,_KV*_KZ,_KW*_KZ);}),_L0=new T(function(){if(!E(_Kx.g)){return E(_KY);}else{var _L1=E(_KY);return new T3(0,-1*E(_L1.a),-1*E(_L1.b),-1*E(_L1.c));}}),_L2=new T(function(){if(!E(_Kx.h)){return E(_KY);}else{var _L3=E(_KY);return new T3(0,-1*E(_L3.a),-1*E(_L3.b),-1*E(_L3.c));}});return (!E(_Ks))?new T2(1,new T(function(){var _L4=E(_L0),_L5=E(_L4.b),_L6=E(_L4.c),_L7=E(_L4.a),_L8=E(_KR),_L9=E(_L8.c),_La=E(_L8.b),_Lb=E(_L8.a),_Lc=E(_KL),_Ld=E(_Lc.c),_Le=E(_Lc.b),_Lf=E(_Lc.a),_Lg=_L5*_L9-_La*_L6,_Lh=_L6*_Lb-_L9*_L7,_Li=_L7*_La-_Lb*_L5,_Lj=B(_le(_jP,_Lh*_Ld-_Le*_Li,_Li*_Lf-_Ld*_Lg,_Lg*_Le-_Lf*_Lh,_Lb,_La,_L9));return new T6(0,_K7,_Kl,E(new T2(0,E(new T3(0,E(_Lg),E(_Lh),E(_Li))),E(_Lj))),E(_JY),_KX,_JE);}),new T2(1,new T(function(){var _Lk=E(_L2),_Ll=E(_Lk.b),_Lm=E(_Lk.c),_Ln=E(_Lk.a),_Lo=E(_KO),_Lp=E(_Lo.c),_Lq=E(_Lo.b),_Lr=E(_Lo.a),_Ls=E(_KI),_Lt=E(_Ls.c),_Lu=E(_Ls.b),_Lv=E(_Ls.a),_Lw=_Ll*_Lp-_Lq*_Lm,_Lx=_Lm*_Lr-_Lp*_Ln,_Ly=_Ln*_Lq-_Lr*_Ll,_Lz=B(_le(_jP,_Lx*_Lt-_Lu*_Ly,_Ly*_Lv-_Lt*_Lw,_Lw*_Lu-_Lv*_Lx,_Lr,_Lq,_Lp));return new T6(0,_K7,_Kl,E(_JY),E(new T2(0,E(new T3(0,E(_Lw),E(_Lx),E(_Ly))),E(_Lz))),_KX,_JE);}),new T(function(){return B(_Kt(_Kw));}))):new T2(1,new T(function(){var _LA=E(_L0),_LB=E(_LA.b),_LC=E(_LA.c),_LD=E(_LA.a),_LE=E(_KR),_LF=_LE.a,_LG=_LE.b,_LH=_LE.c,_LI=B(_me(_jP,_LD,_LB,_LC,_LF,_LG,_LH)),_LJ=E(_KL),_LK=E(_LJ.c),_LL=E(_LJ.b),_LM=E(_LJ.a),_LN=B(_le(_jP,_LB*_LK-_LL*_LC,_LC*_LM-_LK*_LD,_LD*_LL-_LM*_LB,_LF,_LG,_LH)),_LO=E(_L2),_LP=E(_LO.b),_LQ=E(_LO.c),_LR=E(_LO.a),_LS=E(_KO),_LT=_LS.a,_LU=_LS.b,_LV=_LS.c,_LW=B(_me(_jP,_LR,_LP,_LQ,_LT,_LU,_LV)),_LX=E(_KI),_LY=E(_LX.c),_LZ=E(_LX.b),_M0=E(_LX.a),_M1=B(_le(_jP,_LP*_LY-_LZ*_LQ,_LQ*_M0-_LY*_LR,_LR*_LZ-_M0*_LP,_LT,_LU,_LV));return new T6(0,_K7,_Kl,E(new T2(0,E(new T3(0,E(_LI.a),E(_LI.b),E(_LI.c))),E(_LN))),E(new T2(0,E(new T3(0,E(_LW.a),E(_LW.b),E(_LW.c))),E(_M1))),_KX,_JF);}),new T(function(){return B(_Kt(_Kw));}));}};return B(_Kt(_Kp));});return new T2(0,new T2(1,_Kr,new T(function(){return E(E(_Kq).a);})),new T(function(){return E(E(_Kq).b);}));}}}}}},_M2=B(_Ke(B(_sW(_K7,_K5)),_K8,_K9,_Ka,_Kb,_)),_M3=E(_Kc),_M4=E(_M3.d).a,_M5=__app1(E(_JQ),B(_B7(_M3))),_M6=__arr2lst(0,_M5),_M7=B(_Cm(_M6,_)),_M8=__app1(E(_JR),_K7),_M9=__arr2lst(0,_M8),_Ma=B(_Cm(_M9,_));if(_K7!=_K5){var _Mb=E(_M2),_Mc=E(_Mb.b),_Md=B(_K6(_K7+1|0,E(_Mc.a),E(_Mc.b),_Mc.c,_Mc.d,_)),_Me=new T(function(){var _Mf=new T(function(){var _Mg=B(A1(_K0,_M4)),_Mh=B(_lo(_jP,_Mg.a,_Mg.b,_Mg.c));return new T3(0,E(_Mh.a),E(_Mh.b),E(_Mh.c));}),_Mi=new T(function(){var _Mj=new T(function(){return B(_JT(_Mb.a));}),_Mk=function(_Ml){var _Mm=E(_Ml);if(!_Mm._){return E(_Mj);}else{var _Mn=E(_Mm.a),_Mo=E(_Mn.b),_Mp=E(_Mn.a),_Mq=E(_Mn.c),_Mr=_Mq.a,_Ms=_Mq.b,_Mt=E(_Mn.e);return new T2(1,new T(function(){var _Mu=E(_Mo.a)+ -E(_Mp.a),_Mv=E(_Mo.b)+ -E(_Mp.b),_Mw=E(_Mo.c)+ -E(_Mp.c),_Mx=B(A1(_K0,_Mp)),_My=B(_lo(_jP,_Mx.a,_Mx.b,_Mx.c)),_Mz=_My.a,_MA=_My.b,_MB=_My.c,_MC=Math.sqrt(B(_le(_jP,_Mu,_Mv,_Mw,_Mu,_Mv,_Mw))),_MD=1/_MC,_ME=_Mu*_MD,_MF=_Mv*_MD,_MG=_Mw*_MD,_MH=B(_me(_jP,_ME,_MF,_MG,_Mz,_MA,_MB)),_MI=B(_lo(_jP,_Mt.a,_Mt.b,_Mt.c)),_MJ=Math.sqrt(B(_Jp(_jP,_Mr,_Ms,_Mr,_Ms))),_MK=_MJ*E(_MI.a),_ML=_MJ*E(_MI.b),_MM=_MJ*E(_MI.c),_MN=B(_le(_jP,_MF*_MM-_ML*_MG,_MG*_MK-_MM*_ME,_ME*_ML-_MK*_MF,_Mz,_MA,_MB));return new T6(0,_K7,_K7,E(new T2(0,E(new T3(0,E(_MH.a),E(_MH.b),E(_MH.c))),E(_MN))),E(_JY),_MC,_JF);}),new T(function(){return B(_Mk(_Mm.b));}));}};return B(_Mk(_M7));}),_MO=function(_MP){var _MQ=E(_MP);if(!_MQ._){return E(_Mi);}else{var _MR=E(_MQ.a),_MS=E(_MR.b),_MT=new T(function(){var _MU=E(_M4),_MV=E(_MS.c)+ -E(_MU.c),_MW=E(_MS.b)+ -E(_MU.b),_MX=E(_MS.a)+ -E(_MU.a),_MY=Math.sqrt(B(_le(_jP,_MX,_MW,_MV,_MX,_MW,_MV))),_MZ=function(_N0,_N1,_N2){var _N3=E(_Mf),_N4=_N3.a,_N5=_N3.b,_N6=_N3.c,_N7=B(_me(_jP,_N0,_N1,_N2,_N4,_N5,_N6)),_N8=B(_le(_jP,_N1*0-0*_N2,_N2*0-0*_N0,_N0*0-0*_N1,_N4,_N5,_N6));return new T6(0,_K7,_K7,new T2(0,E(new T3(0,E(_N7.a),E(_N7.b),E(_N7.c))),E(_N8)),_JY,_MY,_JF);};if(!E(_MR.g)){var _N9=1/_MY,_Na=B(_MZ(_MX*_N9,_MW*_N9,_MV*_N9));return new T6(0,_Na.a,_Na.b,E(_Na.c),E(_Na.d),_Na.e,_Na.f);}else{var _Nb=1/_MY,_Nc=B(_MZ(-1*_MX*_Nb,-1*_MW*_Nb,-1*_MV*_Nb));return new T6(0,_Nc.a,_Nc.b,E(_Nc.c),E(_Nc.d),_Nc.e,_Nc.f);}});return new T2(1,_MT,new T(function(){return B(_MO(_MQ.b));}));}};return B(_MO(_Ma));});return new T2(0,new T2(1,_Me,new T(function(){return E(E(_Md).a);})),new T(function(){return E(E(_Md).b);}));}else{var _Nd=new T(function(){var _Ne=new T(function(){var _Nf=B(A1(_K0,_M4)),_Ng=B(_lo(_jP,_Nf.a,_Nf.b,_Nf.c));return new T3(0,E(_Ng.a),E(_Ng.b),E(_Ng.c));}),_Nh=new T(function(){var _Ni=new T(function(){return B(_JT(E(_M2).a));}),_Nj=function(_Nk){var _Nl=E(_Nk);if(!_Nl._){return E(_Ni);}else{var _Nm=E(_Nl.a),_Nn=E(_Nm.b),_No=E(_Nm.a),_Np=E(_Nm.c),_Nq=_Np.a,_Nr=_Np.b,_Ns=E(_Nm.e);return new T2(1,new T(function(){var _Nt=E(_Nn.a)+ -E(_No.a),_Nu=E(_Nn.b)+ -E(_No.b),_Nv=E(_Nn.c)+ -E(_No.c),_Nw=B(A1(_K0,_No)),_Nx=B(_lo(_jP,_Nw.a,_Nw.b,_Nw.c)),_Ny=_Nx.a,_Nz=_Nx.b,_NA=_Nx.c,_NB=Math.sqrt(B(_le(_jP,_Nt,_Nu,_Nv,_Nt,_Nu,_Nv))),_NC=1/_NB,_ND=_Nt*_NC,_NE=_Nu*_NC,_NF=_Nv*_NC,_NG=B(_me(_jP,_ND,_NE,_NF,_Ny,_Nz,_NA)),_NH=B(_lo(_jP,_Ns.a,_Ns.b,_Ns.c)),_NI=Math.sqrt(B(_Jp(_jP,_Nq,_Nr,_Nq,_Nr))),_NJ=_NI*E(_NH.a),_NK=_NI*E(_NH.b),_NL=_NI*E(_NH.c),_NM=B(_le(_jP,_NE*_NL-_NK*_NF,_NF*_NJ-_NL*_ND,_ND*_NK-_NJ*_NE,_Ny,_Nz,_NA));return new T6(0,_K7,_K7,E(new T2(0,E(new T3(0,E(_NG.a),E(_NG.b),E(_NG.c))),E(_NM))),E(_JY),_NB,_JF);}),new T(function(){return B(_Nj(_Nl.b));}));}};return B(_Nj(_M7));}),_NN=function(_NO){var _NP=E(_NO);if(!_NP._){return E(_Nh);}else{var _NQ=E(_NP.a),_NR=E(_NQ.b),_NS=new T(function(){var _NT=E(_M4),_NU=E(_NR.c)+ -E(_NT.c),_NV=E(_NR.b)+ -E(_NT.b),_NW=E(_NR.a)+ -E(_NT.a),_NX=Math.sqrt(B(_le(_jP,_NW,_NV,_NU,_NW,_NV,_NU))),_NY=function(_NZ,_O0,_O1){var _O2=E(_Ne),_O3=_O2.a,_O4=_O2.b,_O5=_O2.c,_O6=B(_me(_jP,_NZ,_O0,_O1,_O3,_O4,_O5)),_O7=B(_le(_jP,_O0*0-0*_O1,_O1*0-0*_NZ,_NZ*0-0*_O0,_O3,_O4,_O5));return new T6(0,_K7,_K7,new T2(0,E(new T3(0,E(_O6.a),E(_O6.b),E(_O6.c))),E(_O7)),_JY,_NX,_JF);};if(!E(_NQ.g)){var _O8=1/_NX,_O9=B(_NY(_NW*_O8,_NV*_O8,_NU*_O8));return new T6(0,_O9.a,_O9.b,E(_O9.c),E(_O9.d),_O9.e,_O9.f);}else{var _Oa=1/_NX,_Ob=B(_NY(-1*_NW*_Oa,-1*_NV*_Oa,-1*_NU*_Oa));return new T6(0,_Ob.a,_Ob.b,E(_Ob.c),E(_Ob.d),_Ob.e,_Ob.f);}});return new T2(1,_NS,new T(function(){return B(_NN(_NP.b));}));}};return B(_NN(_Ma));});return new T2(0,new T2(1,_Nd,_w),new T(function(){return E(E(_M2).b);}));}}}},_Oc=B(_K6(_K4,_K4,_K5,_K3.c,_K3.d,_));return new F(function(){return _Jh(_,_Oc);});}else{return new F(function(){return _Jh(_,new T2(0,_w,_K3));});}},_Od=new T(function(){return eval("__strict(passObject)");}),_Oe=new T(function(){return eval("__strict(refresh)");}),_Of=function(_Og,_){var _Oh=__app0(E(_Oe)),_Oi=__app0(E(_Bc)),_Oj=E(_Og),_Ok=_Oj.c,_Ol=_Oj.d,_Om=E(_Oj.a),_On=E(_Oj.b);if(_Om<=_On){if(_Om>_On){return E(_Ba);}else{if(0>=_Ok){return new F(function(){return _Bn(_Ok,0);});}else{var _Oo=E(_Od),_Op=__app2(_Oo,_Om,B(_B7(E(_Ol[0]))));if(_Om!=_On){var _Oq=function(_Or,_){if(_Om>_Or){return E(_Ba);}else{if(_Or>_On){return E(_Ba);}else{var _Os=_Or-_Om|0;if(0>_Os){return new F(function(){return _Bn(_Ok,_Os);});}else{if(_Os>=_Ok){return new F(function(){return _Bn(_Ok,_Os);});}else{var _Ot=__app2(_Oo,_Or,B(_B7(E(_Ol[_Os]))));if(_Or!=_On){var _Ou=B(_Oq(_Or+1|0,_));return new T2(1,_kA,_Ou);}else{return _Bs;}}}}}},_Ov=B(_Oq(_Om+1|0,_)),_Ow=__app0(E(_Bb)),_Ox=B(_K1(_Oj,_));return new T(function(){return E(E(_Ox).b);});}else{var _Oy=__app0(E(_Bb)),_Oz=B(_K1(_Oj,_));return new T(function(){return E(E(_Oz).b);});}}}}else{var _OA=__app0(E(_Bb)),_OB=B(_K1(_Oj,_));return new T(function(){return E(E(_OB).b);});}},_OC=function(_OD,_){while(1){var _OE=E(_OD);if(!_OE._){return _kA;}else{var _OF=_OE.b,_OG=E(_OE.a);switch(_OG._){case 0:var _OH=B(A1(_OG.a,_));_OD=B(_n(_OF,new T2(1,_OH,_w)));continue;case 1:_OD=B(_n(_OF,_OG.a));continue;default:_OD=_OF;continue;}}}},_OI=function(_OJ,_OK,_){var _OL=E(_OJ);switch(_OL._){case 0:var _OM=B(A1(_OL.a,_));return new F(function(){return _OC(B(_n(_OK,new T2(1,_OM,_w))),_);});break;case 1:return new F(function(){return _OC(B(_n(_OK,_OL.a)),_);});break;default:return new F(function(){return _OC(_OK,_);});}},_ON=new T0(2),_OO=function(_OP){return new T0(2);},_OQ=function(_OR,_OS,_OT){return function(_){var _OU=E(_OR),_OV=rMV(_OU),_OW=E(_OV);if(!_OW._){var _OX=new T(function(){var _OY=new T(function(){return B(A1(_OT,_kA));});return B(_n(_OW.b,new T2(1,new T2(0,_OS,function(_OZ){return E(_OY);}),_w)));}),_=wMV(_OU,new T2(0,_OW.a,_OX));return _ON;}else{var _P0=E(_OW.a);if(!_P0._){var _=wMV(_OU,new T2(0,_OS,_w));return new T(function(){return B(A1(_OT,_kA));});}else{var _=wMV(_OU,new T1(1,_P0.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OT,_kA));}),new T2(1,new T(function(){return B(A2(_P0.a,_OS,_OO));}),_w)));}}};},_P1=new T(function(){return E(_qr);}),_P2=new T(function(){return eval("window.requestAnimationFrame");}),_P3=new T1(1,_w),_P4=function(_P5,_P6){return function(_){var _P7=E(_P5),_P8=rMV(_P7),_P9=E(_P8);if(!_P9._){var _Pa=_P9.a,_Pb=E(_P9.b);if(!_Pb._){var _=wMV(_P7,_P3);return new T(function(){return B(A1(_P6,_Pa));});}else{var _Pc=E(_Pb.a),_=wMV(_P7,new T2(0,_Pc.a,_Pb.b));return new T1(1,new T2(1,new T(function(){return B(A1(_P6,_Pa));}),new T2(1,new T(function(){return B(A1(_Pc.b,_OO));}),_w)));}}else{var _Pd=new T(function(){var _Pe=function(_Pf){var _Pg=new T(function(){return B(A1(_P6,_Pf));});return function(_Ph){return E(_Pg);};};return B(_n(_P9.a,new T2(1,_Pe,_w)));}),_=wMV(_P7,new T1(1,_Pd));return _ON;}};},_Pi=function(_Pj,_Pk){return new T1(0,B(_P4(_Pj,_Pk)));},_Pl=function(_Pm,_Pn){var _Po=new T(function(){return new T1(0,B(_OQ(_Pm,_kA,_OO)));});return function(_){var _Pp=__createJSFunc(2,function(_Pq,_){var _Pr=B(_OI(_Po,_w,_));return _P1;}),_Ps=__app1(E(_P2),_Pp);return new T(function(){return B(_Pi(_Pm,_Pn));});};},_Pt=new T1(1,_w),_Pu=function(_Pv,_Pw,_){var _Px=function(_){var _Py=nMV(_Pv),_Pz=_Py;return new T(function(){var _PA=new T(function(){return B(_PB(_));}),_PC=function(_){var _PD=rMV(_Pz),_PE=B(A2(_Pw,_PD,_)),_=wMV(_Pz,_PE),_PF=function(_){var _PG=nMV(_Pt);return new T(function(){return new T1(0,B(_Pl(_PG,function(_PH){return E(_PA);})));});};return new T1(0,_PF);},_PI=new T(function(){return new T1(0,_PC);}),_PB=function(_PJ){return E(_PI);};return B(_PB(_));});};return new F(function(){return _OI(new T1(0,_Px),_w,_);});},_PK=new T(function(){return eval("__strict(setBounds)");}),_PL=function(_){var _PM=__app3(E(_20),E(_91),E(_ib),E(_1Z)),_PN=__app2(E(_PK),E(_1u),E(_1n));return new F(function(){return _Pu(_B0,_Of,_);});},_PO=function(_){return new F(function(){return _PL(_);});};
var hasteMain = function() {B(A(_PO, [0]));};window.onload = hasteMain;