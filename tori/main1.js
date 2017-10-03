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

var _0=function(_1){return E(E(_1).b);},_2=function(_3){return E(E(_3).a);},_4=function(_5,_6,_7){var _8=E(_7);if(!_8._){return new F(function(){return A1(_6,_8.a);});}else{var _9=new T(function(){return B(_0(_5));}),_a=new T(function(){return B(_2(_5));}),_b=function(_c){var _d=E(_c);if(!_d._){return E(_a);}else{return new F(function(){return A2(_9,new T(function(){return B(_4(_5,_6,_d.a));}),new T(function(){return B(_b(_d.b));}));});}};return new F(function(){return _b(_8.a);});}},_e=function(_f,_g,_h){var _i=new T(function(){return B(_0(_f));}),_j=new T(function(){return B(_2(_f));}),_k=function(_l){var _m=E(_l);if(!_m._){return E(_j);}else{return new F(function(){return A2(_i,new T(function(){return B(_4(_f,_g,_m.a));}),new T(function(){return B(_k(_m.b));}));});}};return new F(function(){return _k(_h);});},_n=function(_o,_p){var _q=E(_o);return (_q._==0)?E(_p):new T2(1,_q.a,new T(function(){return B(_n(_q.b,_p));}));},_r=function(_s){var _t=E(_s);if(!_t._){return __Z;}else{return new F(function(){return _n(_t.a,new T(function(){return B(_r(_t.b));},1));});}},_u=function(_v){return new F(function(){return _r(_v);});},_w=__Z,_x=new T3(0,_w,_n,_u),_y=new T(function(){return B(unCStr(",y:"));}),_z=new T1(0,_y),_A=new T(function(){return B(unCStr(",z:"));}),_B=new T1(0,_A),_C=new T(function(){return B(unCStr("})"));}),_D=new T1(0,_C),_E=new T2(1,_D,_w),_F=new T(function(){return B(unCStr("-("));}),_G=new T1(0,_F),_H=new T(function(){return B(unCStr(")"));}),_I=new T1(0,_H),_J=new T2(1,_I,_w),_K=new T(function(){return B(unCStr("."));}),_L=new T1(0,0),_M=function(_N){while(1){var _O=E(_N);if(!_O._){_N=new T1(1,I_fromInt(_O.a));continue;}else{return new F(function(){return I_toString(_O.a);});}}},_P=function(_Q,_R){return new F(function(){return _n(fromJSStr(B(_M(_Q))),_R);});},_S=function(_T,_U){var _V=E(_T);if(!_V._){var _W=_V.a,_X=E(_U);return (_X._==0)?_W<_X.a:I_compareInt(_X.a,_W)>0;}else{var _Y=_V.a,_Z=E(_U);return (_Z._==0)?I_compareInt(_Y,_Z.a)<0:I_compare(_Y,_Z.a)<0;}},_10=41,_11=40,_12=new T1(0,0),_13=function(_14,_15,_16){if(_14<=6){return new F(function(){return _P(_15,_16);});}else{if(!B(_S(_15,_12))){return new F(function(){return _P(_15,_16);});}else{return new T2(1,_11,new T(function(){return B(_n(fromJSStr(B(_M(_15))),new T2(1,_10,_16)));}));}}},_17=new T(function(){return B(_13(0,_L,_w));}),_18=new T(function(){return B(_n(_17,_K));}),_19=new T1(0,_18),_1a=new T2(1,_19,_J),_1b=new T2(1,_G,_1a),_1c=new T1(1,_1b),_1d=new T2(1,_1c,_E),_1e=new T2(1,_B,_1d),_1f=new T2(1,_1c,_1e),_1g=new T2(1,_z,_1f),_1h=new T2(1,_1c,_1g),_1i=new T(function(){return B(unCStr("({x:"));}),_1j=new T1(0,_1i),_1k=new T2(1,_1j,_1h),_1l=function(_1m){return E(_1m);},_1n=new T(function(){return toJSStr(B(_e(_x,_1l,_1k)));}),_1o=new T1(0,1),_1p=new T(function(){return B(_13(0,_1o,_w));}),_1q=new T(function(){return B(_n(_1p,_K));}),_1r=new T1(0,_1q),_1s=new T2(1,_1r,_J),_1t=new T2(1,_G,_1s),_1u=new T(function(){return toJSStr(B(_e(_x,_1l,_1t)));}),_1v=function(_1w,_1x,_1y){var _1z=E(_1y);if(!_1z._){return new F(function(){return A1(_1x,_1z.a);});}else{var _1A=new T(function(){return B(_0(_1w));}),_1B=new T(function(){return B(_2(_1w));}),_1C=function(_1D){var _1E=E(_1D);if(!_1E._){return E(_1B);}else{return new F(function(){return A2(_1A,new T(function(){return B(_1v(_1w,_1x,_1E.a));}),new T(function(){return B(_1C(_1E.b));}));});}};return new F(function(){return _1C(_1z.a);});}},_1F=function(_1G,_1H,_1I){var _1J=new T(function(){return B(_0(_1G));}),_1K=new T(function(){return B(_2(_1G));}),_1L=function(_1M){var _1N=E(_1M);if(!_1N._){return E(_1K);}else{return new F(function(){return A2(_1J,new T(function(){return B(_1v(_1G,_1H,_1N.a));}),new T(function(){return B(_1L(_1N.b));}));});}};return new F(function(){return _1L(_1I);});},_1O=new T(function(){return B(unCStr("-("));}),_1P=new T1(0,_1O),_1Q=new T(function(){return B(unCStr(")"));}),_1R=new T1(0,_1Q),_1S=new T2(1,_1R,_w),_1T=new T(function(){return B(unCStr("."));}),_1U=new T(function(){return B(_13(0,_1o,_w));}),_1V=new T(function(){return B(_n(_1U,_1T));}),_1W=new T1(0,_1V),_1X=new T2(1,_1W,_1S),_1Y=new T2(1,_1P,_1X),_1Z=new T(function(){return toJSStr(B(_1F(_x,_1l,_1Y)));}),_20=new T(function(){return eval("__strict(compile)");}),_21=new T(function(){return B(unCStr(","));}),_22=new T1(0,_21),_23=new T(function(){return B(unCStr("pow("));}),_24=new T1(0,_23),_25=function(_26,_27){return new T1(1,new T2(1,_24,new T2(1,_26,new T2(1,_22,new T2(1,_27,_1S)))));},_28=new T(function(){return B(unCStr("acos("));}),_29=new T1(0,_28),_2a=function(_2b){return new T1(1,new T2(1,_29,new T2(1,_2b,_1S)));},_2c=new T(function(){return B(unCStr("acosh("));}),_2d=new T1(0,_2c),_2e=function(_2f){return new T1(1,new T2(1,_2d,new T2(1,_2f,_1S)));},_2g=new T(function(){return B(unCStr("asin("));}),_2h=new T1(0,_2g),_2i=function(_2j){return new T1(1,new T2(1,_2h,new T2(1,_2j,_1S)));},_2k=new T(function(){return B(unCStr("asinh("));}),_2l=new T1(0,_2k),_2m=function(_2n){return new T1(1,new T2(1,_2l,new T2(1,_2n,_1S)));},_2o=new T(function(){return B(unCStr("atan("));}),_2p=new T1(0,_2o),_2q=function(_2r){return new T1(1,new T2(1,_2p,new T2(1,_2r,_1S)));},_2s=new T(function(){return B(unCStr("atanh("));}),_2t=new T1(0,_2s),_2u=function(_2v){return new T1(1,new T2(1,_2t,new T2(1,_2v,_1S)));},_2w=new T(function(){return B(unCStr("cos("));}),_2x=new T1(0,_2w),_2y=function(_2z){return new T1(1,new T2(1,_2x,new T2(1,_2z,_1S)));},_2A=new T(function(){return B(unCStr("cosh("));}),_2B=new T1(0,_2A),_2C=function(_2D){return new T1(1,new T2(1,_2B,new T2(1,_2D,_1S)));},_2E=new T(function(){return B(unCStr("exp("));}),_2F=new T1(0,_2E),_2G=function(_2H){return new T1(1,new T2(1,_2F,new T2(1,_2H,_1S)));},_2I=new T(function(){return B(unCStr("log("));}),_2J=new T1(0,_2I),_2K=function(_2L){return new T1(1,new T2(1,_2J,new T2(1,_2L,_1S)));},_2M=new T(function(){return B(unCStr(")/log("));}),_2N=new T1(0,_2M),_2O=function(_2P,_2Q){return new T1(1,new T2(1,_2J,new T2(1,_2Q,new T2(1,_2N,new T2(1,_2P,_1S)))));},_2R=new T(function(){return B(unCStr("pi"));}),_2S=new T1(0,_2R),_2T=new T(function(){return B(unCStr("sin("));}),_2U=new T1(0,_2T),_2V=function(_2W){return new T1(1,new T2(1,_2U,new T2(1,_2W,_1S)));},_2X=new T(function(){return B(unCStr("sinh("));}),_2Y=new T1(0,_2X),_2Z=function(_30){return new T1(1,new T2(1,_2Y,new T2(1,_30,_1S)));},_31=new T(function(){return B(unCStr("sqrt("));}),_32=new T1(0,_31),_33=function(_34){return new T1(1,new T2(1,_32,new T2(1,_34,_1S)));},_35=new T(function(){return B(unCStr("tan("));}),_36=new T1(0,_35),_37=function(_38){return new T1(1,new T2(1,_36,new T2(1,_38,_1S)));},_39=new T(function(){return B(unCStr("tanh("));}),_3a=new T1(0,_39),_3b=function(_3c){return new T1(1,new T2(1,_3a,new T2(1,_3c,_1S)));},_3d=new T(function(){return B(unCStr("("));}),_3e=new T1(0,_3d),_3f=new T(function(){return B(unCStr(")/("));}),_3g=new T1(0,_3f),_3h=function(_3i,_3j){return new T1(1,new T2(1,_3e,new T2(1,_3i,new T2(1,_3g,new T2(1,_3j,_1S)))));},_3k=new T1(0,1),_3l=function(_3m,_3n){var _3o=E(_3m);if(!_3o._){var _3p=_3o.a,_3q=E(_3n);if(!_3q._){var _3r=_3q.a;return (_3p!=_3r)?(_3p>_3r)?2:0:1;}else{var _3s=I_compareInt(_3q.a,_3p);return (_3s<=0)?(_3s>=0)?1:2:0;}}else{var _3t=_3o.a,_3u=E(_3n);if(!_3u._){var _3v=I_compareInt(_3t,_3u.a);return (_3v>=0)?(_3v<=0)?1:2:0;}else{var _3w=I_compare(_3t,_3u.a);return (_3w>=0)?(_3w<=0)?1:2:0;}}},_3x=new T(function(){return B(unCStr("base"));}),_3y=new T(function(){return B(unCStr("GHC.Exception"));}),_3z=new T(function(){return B(unCStr("ArithException"));}),_3A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3x,_3y,_3z),_3B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_3A,_w,_w),_3C=function(_3D){return E(_3B);},_3E=function(_3F){return E(E(_3F).a);},_3G=function(_3H,_3I,_3J){var _3K=B(A1(_3H,_)),_3L=B(A1(_3I,_)),_3M=hs_eqWord64(_3K.a,_3L.a);if(!_3M){return __Z;}else{var _3N=hs_eqWord64(_3K.b,_3L.b);return (!_3N)?__Z:new T1(1,_3J);}},_3O=function(_3P){var _3Q=E(_3P);return new F(function(){return _3G(B(_3E(_3Q.a)),_3C,_3Q.b);});},_3R=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_3S=new T(function(){return B(unCStr("denormal"));}),_3T=new T(function(){return B(unCStr("divide by zero"));}),_3U=new T(function(){return B(unCStr("loss of precision"));}),_3V=new T(function(){return B(unCStr("arithmetic underflow"));}),_3W=new T(function(){return B(unCStr("arithmetic overflow"));}),_3X=function(_3Y,_3Z){switch(E(_3Y)){case 0:return new F(function(){return _n(_3W,_3Z);});break;case 1:return new F(function(){return _n(_3V,_3Z);});break;case 2:return new F(function(){return _n(_3U,_3Z);});break;case 3:return new F(function(){return _n(_3T,_3Z);});break;case 4:return new F(function(){return _n(_3S,_3Z);});break;default:return new F(function(){return _n(_3R,_3Z);});}},_40=function(_41){return new F(function(){return _3X(_41,_w);});},_42=function(_43,_44,_45){return new F(function(){return _3X(_44,_45);});},_46=44,_47=93,_48=91,_49=function(_4a,_4b,_4c){var _4d=E(_4b);if(!_4d._){return new F(function(){return unAppCStr("[]",_4c);});}else{var _4e=new T(function(){var _4f=new T(function(){var _4g=function(_4h){var _4i=E(_4h);if(!_4i._){return E(new T2(1,_47,_4c));}else{var _4j=new T(function(){return B(A2(_4a,_4i.a,new T(function(){return B(_4g(_4i.b));})));});return new T2(1,_46,_4j);}};return B(_4g(_4d.b));});return B(A2(_4a,_4d.a,_4f));});return new T2(1,_48,_4e);}},_4k=function(_4l,_4m){return new F(function(){return _49(_3X,_4l,_4m);});},_4n=new T3(0,_42,_40,_4k),_4o=new T(function(){return new T5(0,_3C,_4n,_4p,_3O,_40);}),_4p=function(_4q){return new T2(0,_4o,_4q);},_4r=3,_4s=new T(function(){return B(_4p(_4r));}),_4t=new T(function(){return die(_4s);}),_4u=function(_4v,_4w){var _4x=E(_4v);return (_4x._==0)?_4x.a*Math.pow(2,_4w):I_toNumber(_4x.a)*Math.pow(2,_4w);},_4y=function(_4z,_4A){var _4B=E(_4z);if(!_4B._){var _4C=_4B.a,_4D=E(_4A);return (_4D._==0)?_4C==_4D.a:(I_compareInt(_4D.a,_4C)==0)?true:false;}else{var _4E=_4B.a,_4F=E(_4A);return (_4F._==0)?(I_compareInt(_4E,_4F.a)==0)?true:false:(I_compare(_4E,_4F.a)==0)?true:false;}},_4G=function(_4H){var _4I=E(_4H);if(!_4I._){return E(_4I.a);}else{return new F(function(){return I_toInt(_4I.a);});}},_4J=function(_4K,_4L){while(1){var _4M=E(_4K);if(!_4M._){var _4N=_4M.a,_4O=E(_4L);if(!_4O._){var _4P=_4O.a,_4Q=addC(_4N,_4P);if(!E(_4Q.b)){return new T1(0,_4Q.a);}else{_4K=new T1(1,I_fromInt(_4N));_4L=new T1(1,I_fromInt(_4P));continue;}}else{_4K=new T1(1,I_fromInt(_4N));_4L=_4O;continue;}}else{var _4R=E(_4L);if(!_4R._){_4K=_4M;_4L=new T1(1,I_fromInt(_4R.a));continue;}else{return new T1(1,I_add(_4M.a,_4R.a));}}}},_4S=function(_4T,_4U){while(1){var _4V=E(_4T);if(!_4V._){var _4W=E(_4V.a);if(_4W==(-2147483648)){_4T=new T1(1,I_fromInt(-2147483648));continue;}else{var _4X=E(_4U);if(!_4X._){var _4Y=_4X.a;return new T2(0,new T1(0,quot(_4W,_4Y)),new T1(0,_4W%_4Y));}else{_4T=new T1(1,I_fromInt(_4W));_4U=_4X;continue;}}}else{var _4Z=E(_4U);if(!_4Z._){_4T=_4V;_4U=new T1(1,I_fromInt(_4Z.a));continue;}else{var _50=I_quotRem(_4V.a,_4Z.a);return new T2(0,new T1(1,_50.a),new T1(1,_50.b));}}}},_51=new T1(0,0),_52=function(_53,_54){while(1){var _55=E(_53);if(!_55._){_53=new T1(1,I_fromInt(_55.a));continue;}else{return new T1(1,I_shiftLeft(_55.a,_54));}}},_56=function(_57,_58,_59){if(!B(_4y(_59,_51))){var _5a=B(_4S(_58,_59)),_5b=_5a.a;switch(B(_3l(B(_52(_5a.b,1)),_59))){case 0:return new F(function(){return _4u(_5b,_57);});break;case 1:if(!(B(_4G(_5b))&1)){return new F(function(){return _4u(_5b,_57);});}else{return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}break;default:return new F(function(){return _4u(B(_4J(_5b,_3k)),_57);});}}else{return E(_4t);}},_5c=function(_5d,_5e){var _5f=E(_5d);if(!_5f._){var _5g=_5f.a,_5h=E(_5e);return (_5h._==0)?_5g>_5h.a:I_compareInt(_5h.a,_5g)<0;}else{var _5i=_5f.a,_5j=E(_5e);return (_5j._==0)?I_compareInt(_5i,_5j.a)>0:I_compare(_5i,_5j.a)>0;}},_5k=new T1(0,1),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_5n=new T(function(){return B(unCStr("PatternMatchFail"));}),_5o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5l,_5m,_5n),_5p=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_5o,_w,_w),_5q=function(_5r){return E(_5p);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _3G(B(_3E(_5u.a)),_5q,_5u.b);});},_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return new T2(0,_5z,_5y);},_5A=function(_5B,_5C){return new F(function(){return _n(E(_5B).a,_5C);});},_5D=function(_5E,_5F){return new F(function(){return _49(_5A,_5E,_5F);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _n(E(_5I).a,_5J);});},_5K=new T3(0,_5G,_5v,_5D),_5z=new T(function(){return new T5(0,_5q,_5K,_5x,_5s,_5v);}),_5L=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5M=function(_5N){return E(E(_5N).c);},_5O=function(_5P,_5Q){return new F(function(){return die(new T(function(){return B(A2(_5M,_5Q,_5P));}));});},_5R=function(_5S,_4q){return new F(function(){return _5O(_5S,_4q);});},_5T=function(_5U,_5V){var _5W=E(_5V);if(!_5W._){return new T2(0,_w,_w);}else{var _5X=_5W.a;if(!B(A1(_5U,_5X))){return new T2(0,_w,_5W);}else{var _5Y=new T(function(){var _5Z=B(_5T(_5U,_5W.b));return new T2(0,_5Z.a,_5Z.b);});return new T2(0,new T2(1,_5X,new T(function(){return E(E(_5Y).a);})),new T(function(){return E(E(_5Y).b);}));}}},_60=32,_61=new T(function(){return B(unCStr("\n"));}),_62=function(_63){return (E(_63)==124)?false:true;},_64=function(_65,_66){var _67=B(_5T(_62,B(unCStr(_65)))),_68=_67.a,_69=function(_6a,_6b){var _6c=new T(function(){var _6d=new T(function(){return B(_n(_66,new T(function(){return B(_n(_6b,_61));},1)));});return B(unAppCStr(": ",_6d));},1);return new F(function(){return _n(_6a,_6c);});},_6e=E(_67.b);if(!_6e._){return new F(function(){return _69(_68,_w);});}else{if(E(_6e.a)==124){return new F(function(){return _69(_68,new T2(1,_60,_6e.b));});}else{return new F(function(){return _69(_68,_w);});}}},_6f=function(_6g){return new F(function(){return _5R(new T1(0,new T(function(){return B(_64(_6g,_5L));})),_5z);});},_6h=function(_6i){var _6j=function(_6k,_6l){while(1){if(!B(_S(_6k,_6i))){if(!B(_5c(_6k,_6i))){if(!B(_4y(_6k,_6i))){return new F(function(){return _6f("GHCIntegerType.lhs:(553,5)-(555,32)|function l2");});}else{return E(_6l);}}else{return _6l-1|0;}}else{var _6m=B(_52(_6k,1)),_6n=_6l+1|0;_6k=_6m;_6l=_6n;continue;}}};return new F(function(){return _6j(_5k,0);});},_6o=function(_6p){var _6q=E(_6p);if(!_6q._){var _6r=_6q.a>>>0;if(!_6r){return -1;}else{var _6s=function(_6t,_6u){while(1){if(_6t>=_6r){if(_6t<=_6r){if(_6t!=_6r){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6u);}}else{return _6u-1|0;}}else{var _6v=imul(_6t,2)>>>0,_6w=_6u+1|0;_6t=_6v;_6u=_6w;continue;}}};return new F(function(){return _6s(1,0);});}}else{return new F(function(){return _6h(_6q);});}},_6x=function(_6y){var _6z=E(_6y);if(!_6z._){var _6A=_6z.a>>>0;if(!_6A){return new T2(0,-1,0);}else{var _6B=function(_6C,_6D){while(1){if(_6C>=_6A){if(_6C<=_6A){if(_6C!=_6A){return new F(function(){return _6f("GHCIntegerType.lhs:(609,5)-(611,40)|function l2");});}else{return E(_6D);}}else{return _6D-1|0;}}else{var _6E=imul(_6C,2)>>>0,_6F=_6D+1|0;_6C=_6E;_6D=_6F;continue;}}};return new T2(0,B(_6B(1,0)),(_6A&_6A-1>>>0)>>>0&4294967295);}}else{var _6G=_6z.a;return new T2(0,B(_6o(_6z)),I_compareInt(I_and(_6G,I_sub(_6G,I_fromInt(1))),0));}},_6H=function(_6I,_6J){var _6K=E(_6I);if(!_6K._){var _6L=_6K.a,_6M=E(_6J);return (_6M._==0)?_6L<=_6M.a:I_compareInt(_6M.a,_6L)>=0;}else{var _6N=_6K.a,_6O=E(_6J);return (_6O._==0)?I_compareInt(_6N,_6O.a)<=0:I_compare(_6N,_6O.a)<=0;}},_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){var _6T=_6S.a,_6U=E(_6R);if(!_6U._){return new T1(0,(_6T>>>0&_6U.a>>>0)>>>0&4294967295);}else{_6Q=new T1(1,I_fromInt(_6T));_6R=_6U;continue;}}else{var _6V=E(_6R);if(!_6V._){_6Q=_6S;_6R=new T1(1,I_fromInt(_6V.a));continue;}else{return new T1(1,I_and(_6S.a,_6V.a));}}}},_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){var _70=_6Z.a,_71=E(_6Y);if(!_71._){var _72=_71.a,_73=subC(_70,_72);if(!E(_73.b)){return new T1(0,_73.a);}else{_6X=new T1(1,I_fromInt(_70));_6Y=new T1(1,I_fromInt(_72));continue;}}else{_6X=new T1(1,I_fromInt(_70));_6Y=_71;continue;}}else{var _74=E(_6Y);if(!_74._){_6X=_6Z;_6Y=new T1(1,I_fromInt(_74.a));continue;}else{return new T1(1,I_sub(_6Z.a,_74.a));}}}},_75=new T1(0,2),_76=function(_77,_78){var _79=E(_77);if(!_79._){var _7a=(_79.a>>>0&(2<<_78>>>0)-1>>>0)>>>0,_7b=1<<_78>>>0;return (_7b<=_7a)?(_7b>=_7a)?1:2:0;}else{var _7c=B(_6P(_79,B(_6W(B(_52(_75,_78)),_5k)))),_7d=B(_52(_5k,_78));return (!B(_5c(_7d,_7c)))?(!B(_S(_7d,_7c)))?1:2:0;}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){_7f=new T1(1,I_fromInt(_7h.a));continue;}else{return new T1(1,I_shiftRight(_7h.a,_7g));}}},_7i=function(_7j,_7k,_7l,_7m){var _7n=B(_6x(_7m)),_7o=_7n.a;if(!E(_7n.b)){var _7p=B(_6o(_7l));if(_7p<((_7o+_7j|0)-1|0)){var _7q=_7o+(_7j-_7k|0)|0;if(_7q>0){if(_7q>_7p){if(_7q<=(_7p+1|0)){if(!E(B(_6x(_7l)).b)){return 0;}else{return new F(function(){return _4u(_3k,_7j-_7k|0);});}}else{return 0;}}else{var _7r=B(_7e(_7l,_7q));switch(B(_76(_7l,_7q-1|0))){case 0:return new F(function(){return _4u(_7r,_7j-_7k|0);});break;case 1:if(!(B(_4G(_7r))&1)){return new F(function(){return _4u(_7r,_7j-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}break;default:return new F(function(){return _4u(B(_4J(_7r,_3k)),_7j-_7k|0);});}}}else{return new F(function(){return _4u(_7l,(_7j-_7k|0)-_7q|0);});}}else{if(_7p>=_7k){var _7s=B(_7e(_7l,(_7p+1|0)-_7k|0));switch(B(_76(_7l,_7p-_7k|0))){case 0:return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});break;case 2:return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});break;default:if(!(B(_4G(_7s))&1)){return new F(function(){return _4u(_7s,((_7p-_7o|0)+1|0)-_7k|0);});}else{return new F(function(){return _4u(B(_4J(_7s,_3k)),((_7p-_7o|0)+1|0)-_7k|0);});}}}else{return new F(function(){return _4u(_7l, -_7o);});}}}else{var _7t=B(_6o(_7l))-_7o|0,_7u=function(_7v){var _7w=function(_7x,_7y){if(!B(_6H(B(_52(_7y,_7k)),_7x))){return new F(function(){return _56(_7v-_7k|0,_7x,_7y);});}else{return new F(function(){return _56((_7v-_7k|0)+1|0,_7x,B(_52(_7y,1)));});}};if(_7v>=_7k){if(_7v!=_7k){return new F(function(){return _7w(_7l,new T(function(){return B(_52(_7m,_7v-_7k|0));}));});}else{return new F(function(){return _7w(_7l,_7m);});}}else{return new F(function(){return _7w(new T(function(){return B(_52(_7l,_7k-_7v|0));}),_7m);});}};if(_7j>_7t){return new F(function(){return _7u(_7j);});}else{return new F(function(){return _7u(_7t);});}}},_7z=new T1(0,2147483647),_7A=new T(function(){return B(_4J(_7z,_5k));}),_7B=function(_7C){var _7D=E(_7C);if(!_7D._){var _7E=E(_7D.a);return (_7E==(-2147483648))?E(_7A):new T1(0, -_7E);}else{return new T1(1,I_negate(_7D.a));}},_7F=new T(function(){return 0/0;}),_7G=new T(function(){return -1/0;}),_7H=new T(function(){return 1/0;}),_7I=0,_7J=function(_7K,_7L){if(!B(_4y(_7L,_51))){if(!B(_4y(_7K,_51))){if(!B(_S(_7K,_51))){return new F(function(){return _7i(-1021,53,_7K,_7L);});}else{return  -B(_7i(-1021,53,B(_7B(_7K)),_7L));}}else{return E(_7I);}}else{return (!B(_4y(_7K,_51)))?(!B(_S(_7K,_51)))?E(_7H):E(_7G):E(_7F);}},_7M=function(_7N){return new T1(0,new T(function(){var _7O=E(_7N),_7P=jsShow(B(_7J(_7O.a,_7O.b)));return fromJSStr(_7P);}));},_7Q=new T(function(){return B(unCStr("1./("));}),_7R=new T1(0,_7Q),_7S=function(_7T){return new T1(1,new T2(1,_7R,new T2(1,_7T,_1S)));},_7U=new T(function(){return B(unCStr(")+("));}),_7V=new T1(0,_7U),_7W=function(_7X,_7Y){return new T1(1,new T2(1,_3e,new T2(1,_7X,new T2(1,_7V,new T2(1,_7Y,_1S)))));},_7Z=function(_80){return new T1(1,new T2(1,_1P,new T2(1,_80,_1S)));},_81=new T(function(){return B(unCStr(")*("));}),_82=new T1(0,_81),_83=function(_84,_85){return new T1(1,new T2(1,_3e,new T2(1,_84,new T2(1,_82,new T2(1,_85,_1S)))));},_86=function(_87){return E(E(_87).a);},_88=function(_89){return E(E(_89).d);},_8a=function(_8b,_8c){return new F(function(){return A3(_86,_8d,_8b,new T(function(){return B(A2(_88,_8d,_8c));}));});},_8e=new T(function(){return B(unCStr("abs("));}),_8f=new T1(0,_8e),_8g=function(_8h){return new T1(1,new T2(1,_8f,new T2(1,_8h,_1S)));},_8i=function(_8j){return new T1(0,new T(function(){return B(_n(B(_13(0,_8j,_w)),_1T));}));},_8k=new T(function(){return B(unCStr("sign("));}),_8l=new T1(0,_8k),_8m=function(_8n){return new T1(1,new T2(1,_8l,new T2(1,_8n,_1S)));},_8d=new T(function(){return {_:0,a:_7W,b:_8a,c:_83,d:_7Z,e:_8g,f:_8m,g:_8i};}),_8o=new T4(0,_8d,_3h,_7S,_7M),_8p={_:0,a:_8o,b:_2S,c:_2G,d:_2K,e:_33,f:_25,g:_2O,h:_2V,i:_2y,j:_37,k:_2i,l:_2a,m:_2q,n:_2Z,o:_2C,p:_3b,q:_2m,r:_2e,s:_2u},_8q=function(_8r){return E(E(_8r).a);},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v){return E(E(_8v).c);},_8w=function(_8x){return E(E(_8x).b);},_8y=function(_8z){return E(E(_8z).d);},_8A=new T1(0,2),_8B=new T2(0,E(_1o),E(_8A)),_8C=new T1(0,5),_8D=new T1(0,4),_8E=new T2(0,E(_8D),E(_8C)),_8F=function(_8G){return E(E(_8G).e);},_8H=function(_8I,_8J,_8K,_8L){var _8M=B(_8q(_8I)),_8N=B(_8s(_8M)),_8O=new T(function(){var _8P=new T(function(){var _8Q=new T(function(){var _8R=new T(function(){var _8S=new T(function(){var _8T=new T(function(){return B(A3(_86,_8N,new T(function(){return B(A3(_8u,_8N,_8J,_8J));}),new T(function(){return B(A3(_8u,_8N,_8L,_8L));})));});return B(A2(_8F,_8I,_8T));});return B(A3(_8w,_8N,_8S,new T(function(){return B(A2(_8y,_8M,_8E));})));});return B(A3(_8u,_8N,_8R,_8R));});return B(A3(_86,_8N,_8Q,new T(function(){return B(A3(_8u,_8N,_8K,_8K));})));});return B(A2(_8F,_8I,_8P));});return new F(function(){return A3(_8w,_8N,_8O,new T(function(){return B(A2(_8y,_8M,_8B));}));});},_8U=new T(function(){return B(unCStr("x"));}),_8V=new T1(0,_8U),_8W=new T(function(){return B(unCStr("y"));}),_8X=new T1(0,_8W),_8Y=new T(function(){return B(unCStr("z"));}),_8Z=new T1(0,_8Y),_90=new T(function(){return B(_8H(_8p,_8V,_8X,_8Z));}),_91=new T(function(){return toJSStr(B(_1v(_x,_1l,_90)));}),_92=new T3(0,E(_8V),E(_8X),E(_8Z)),_93=new T(function(){return B(unCStr("(/=) is not defined"));}),_94=new T(function(){return B(err(_93));}),_95=new T(function(){return B(unCStr("(==) is not defined"));}),_96=new T(function(){return B(err(_95));}),_97=new T2(0,_96,_94),_98=new T(function(){return B(unCStr("(<) is not defined"));}),_99=new T(function(){return B(err(_98));}),_9a=new T(function(){return B(unCStr("(<=) is not defined"));}),_9b=new T(function(){return B(err(_9a));}),_9c=new T(function(){return B(unCStr("(>) is not defined"));}),_9d=new T(function(){return B(err(_9c));}),_9e=new T(function(){return B(unCStr("(>=) is not defined"));}),_9f=new T(function(){return B(err(_9e));}),_9g=new T(function(){return B(unCStr("compare is not defined"));}),_9h=new T(function(){return B(err(_9g));}),_9i=new T(function(){return B(unCStr("max("));}),_9j=new T1(0,_9i),_9k=function(_9l,_9m){return new T1(1,new T2(1,_9j,new T2(1,_9l,new T2(1,_22,new T2(1,_9m,_1S)))));},_9n=new T(function(){return B(unCStr("min("));}),_9o=new T1(0,_9n),_9p=function(_9q,_9r){return new T1(1,new T2(1,_9o,new T2(1,_9q,new T2(1,_22,new T2(1,_9r,_1S)))));},_9s={_:0,a:_97,b:_9h,c:_99,d:_9b,e:_9d,f:_9f,g:_9k,h:_9p},_9t=new T2(0,_8p,_9s),_9u=function(_9v,_9w){var _9x=E(_9v);return E(_9w);},_9y=function(_9z,_9A){var _9B=E(_9A);return E(_9z);},_9C=function(_9D,_9E){var _9F=E(_9D),_9G=E(_9E);return new T3(0,E(B(A1(_9F.a,_9G.a))),E(B(A1(_9F.b,_9G.b))),E(B(A1(_9F.c,_9G.c))));},_9H=function(_9I,_9J,_9K){return new T3(0,E(_9I),E(_9J),E(_9K));},_9L=function(_9M){return new F(function(){return _9H(_9M,_9M,_9M);});},_9N=function(_9O,_9P){var _9Q=E(_9P),_9R=E(_9O);return new T3(0,E(_9R),E(_9R),E(_9R));},_9S=function(_9T,_9U){var _9V=E(_9U);return new T3(0,E(B(A1(_9T,_9V.a))),E(B(A1(_9T,_9V.b))),E(B(A1(_9T,_9V.c))));},_9W=new T2(0,_9S,_9N),_9X=new T5(0,_9W,_9L,_9C,_9u,_9y),_9Y=new T1(0,0),_9Z=function(_a0){return E(E(_a0).g);},_a1=function(_a2){var _a3=B(A2(_9Z,_a2,_1o)),_a4=B(A2(_9Z,_a2,_9Y));return new T3(0,E(new T3(0,E(_a3),E(_a4),E(_a4))),E(new T3(0,E(_a4),E(_a3),E(_a4))),E(new T3(0,E(_a4),E(_a4),E(_a3))));},_a5=function(_a6){return E(E(_a6).a);},_a7=function(_a8){return E(E(_a8).f);},_a9=function(_aa){return E(E(_aa).b);},_ab=function(_ac){return E(E(_ac).c);},_ad=function(_ae){return E(E(_ae).a);},_af=function(_ag){return E(E(_ag).d);},_ah=function(_ai,_aj,_ak,_al,_am){var _an=new T(function(){return E(E(E(_ai).c).a);}),_ao=new T(function(){var _ap=E(_ai).a,_aq=new T(function(){var _ar=new T(function(){return B(_8q(_an));}),_as=new T(function(){return B(_8s(_ar));}),_at=new T(function(){return B(A2(_af,_an,_aj));}),_au=new T(function(){return B(A3(_a7,_an,_aj,_al));}),_av=function(_aw,_ax){var _ay=new T(function(){var _az=new T(function(){return B(A3(_a9,_ar,new T(function(){return B(A3(_8u,_as,_al,_aw));}),_aj));});return B(A3(_86,_as,_az,new T(function(){return B(A3(_8u,_as,_ax,_at));})));});return new F(function(){return A3(_8u,_as,_au,_ay);});};return B(A3(_ad,B(_a5(_ap)),_av,_ak));});return B(A3(_ab,_ap,_aq,_am));});return new T2(0,new T(function(){return B(A3(_a7,_an,_aj,_al));}),_ao);},_aA=function(_aB,_aC,_aD,_aE){var _aF=E(_aD),_aG=E(_aE),_aH=B(_ah(_aC,_aF.a,_aF.b,_aG.a,_aG.b));return new T2(0,_aH.a,_aH.b);},_aI=new T1(0,1),_aJ=function(_aK){return E(E(_aK).l);},_aL=function(_aM,_aN,_aO){var _aP=new T(function(){return E(E(E(_aM).c).a);}),_aQ=new T(function(){var _aR=new T(function(){return B(_8q(_aP));}),_aS=new T(function(){var _aT=B(_8s(_aR)),_aU=new T(function(){var _aV=new T(function(){return B(A3(_8w,_aT,new T(function(){return B(A2(_9Z,_aT,_aI));}),new T(function(){return B(A3(_8u,_aT,_aN,_aN));})));});return B(A2(_8F,_aP,_aV));});return B(A2(_88,_aT,_aU));});return B(A3(_ad,B(_a5(E(_aM).a)),function(_aW){return new F(function(){return A3(_a9,_aR,_aW,_aS);});},_aO));});return new T2(0,new T(function(){return B(A2(_aJ,_aP,_aN));}),_aQ);},_aX=function(_aY,_aZ,_b0){var _b1=E(_b0),_b2=B(_aL(_aZ,_b1.a,_b1.b));return new T2(0,_b2.a,_b2.b);},_b3=function(_b4){return E(E(_b4).r);},_b5=function(_b6,_b7,_b8){var _b9=new T(function(){return E(E(E(_b6).c).a);}),_ba=new T(function(){var _bb=new T(function(){return B(_8q(_b9));}),_bc=new T(function(){var _bd=new T(function(){var _be=B(_8s(_bb));return B(A3(_8w,_be,new T(function(){return B(A3(_8u,_be,_b7,_b7));}),new T(function(){return B(A2(_9Z,_be,_aI));})));});return B(A2(_8F,_b9,_bd));});return B(A3(_ad,B(_a5(E(_b6).a)),function(_bf){return new F(function(){return A3(_a9,_bb,_bf,_bc);});},_b8));});return new T2(0,new T(function(){return B(A2(_b3,_b9,_b7));}),_ba);},_bg=function(_bh,_bi,_bj){var _bk=E(_bj),_bl=B(_b5(_bi,_bk.a,_bk.b));return new T2(0,_bl.a,_bl.b);},_bm=function(_bn){return E(E(_bn).k);},_bo=function(_bp,_bq,_br){var _bs=new T(function(){return E(E(E(_bp).c).a);}),_bt=new T(function(){var _bu=new T(function(){return B(_8q(_bs));}),_bv=new T(function(){var _bw=new T(function(){var _bx=B(_8s(_bu));return B(A3(_8w,_bx,new T(function(){return B(A2(_9Z,_bx,_aI));}),new T(function(){return B(A3(_8u,_bx,_bq,_bq));})));});return B(A2(_8F,_bs,_bw));});return B(A3(_ad,B(_a5(E(_bp).a)),function(_by){return new F(function(){return A3(_a9,_bu,_by,_bv);});},_br));});return new T2(0,new T(function(){return B(A2(_bm,_bs,_bq));}),_bt);},_bz=function(_bA,_bB,_bC){var _bD=E(_bC),_bE=B(_bo(_bB,_bD.a,_bD.b));return new T2(0,_bE.a,_bE.b);},_bF=function(_bG){return E(E(_bG).q);},_bH=function(_bI,_bJ,_bK){var _bL=new T(function(){return E(E(E(_bI).c).a);}),_bM=new T(function(){var _bN=new T(function(){return B(_8q(_bL));}),_bO=new T(function(){var _bP=new T(function(){var _bQ=B(_8s(_bN));return B(A3(_86,_bQ,new T(function(){return B(A3(_8u,_bQ,_bJ,_bJ));}),new T(function(){return B(A2(_9Z,_bQ,_aI));})));});return B(A2(_8F,_bL,_bP));});return B(A3(_ad,B(_a5(E(_bI).a)),function(_bR){return new F(function(){return A3(_a9,_bN,_bR,_bO);});},_bK));});return new T2(0,new T(function(){return B(A2(_bF,_bL,_bJ));}),_bM);},_bS=function(_bT,_bU,_bV){var _bW=E(_bV),_bX=B(_bH(_bU,_bW.a,_bW.b));return new T2(0,_bX.a,_bX.b);},_bY=function(_bZ){return E(E(_bZ).m);},_c0=function(_c1,_c2,_c3){var _c4=new T(function(){return E(E(E(_c1).c).a);}),_c5=new T(function(){var _c6=new T(function(){return B(_8q(_c4));}),_c7=new T(function(){var _c8=B(_8s(_c6));return B(A3(_86,_c8,new T(function(){return B(A2(_9Z,_c8,_aI));}),new T(function(){return B(A3(_8u,_c8,_c2,_c2));})));});return B(A3(_ad,B(_a5(E(_c1).a)),function(_c9){return new F(function(){return A3(_a9,_c6,_c9,_c7);});},_c3));});return new T2(0,new T(function(){return B(A2(_bY,_c4,_c2));}),_c5);},_ca=function(_cb,_cc,_cd){var _ce=E(_cd),_cf=B(_c0(_cc,_ce.a,_ce.b));return new T2(0,_cf.a,_cf.b);},_cg=function(_ch){return E(E(_ch).s);},_ci=function(_cj,_ck,_cl){var _cm=new T(function(){return E(E(E(_cj).c).a);}),_cn=new T(function(){var _co=new T(function(){return B(_8q(_cm));}),_cp=new T(function(){var _cq=B(_8s(_co));return B(A3(_8w,_cq,new T(function(){return B(A2(_9Z,_cq,_aI));}),new T(function(){return B(A3(_8u,_cq,_ck,_ck));})));});return B(A3(_ad,B(_a5(E(_cj).a)),function(_cr){return new F(function(){return A3(_a9,_co,_cr,_cp);});},_cl));});return new T2(0,new T(function(){return B(A2(_cg,_cm,_ck));}),_cn);},_cs=function(_ct,_cu,_cv){var _cw=E(_cv),_cx=B(_ci(_cu,_cw.a,_cw.b));return new T2(0,_cx.a,_cx.b);},_cy=function(_cz){return E(E(_cz).i);},_cA=function(_cB){return E(E(_cB).h);},_cC=function(_cD,_cE,_cF){var _cG=new T(function(){return E(E(E(_cD).c).a);}),_cH=new T(function(){var _cI=new T(function(){return B(_8s(new T(function(){return B(_8q(_cG));})));}),_cJ=new T(function(){return B(A2(_88,_cI,new T(function(){return B(A2(_cA,_cG,_cE));})));});return B(A3(_ad,B(_a5(E(_cD).a)),function(_cK){return new F(function(){return A3(_8u,_cI,_cK,_cJ);});},_cF));});return new T2(0,new T(function(){return B(A2(_cy,_cG,_cE));}),_cH);},_cL=function(_cM,_cN,_cO){var _cP=E(_cO),_cQ=B(_cC(_cN,_cP.a,_cP.b));return new T2(0,_cQ.a,_cQ.b);},_cR=function(_cS){return E(E(_cS).o);},_cT=function(_cU){return E(E(_cU).n);},_cV=function(_cW,_cX,_cY){var _cZ=new T(function(){return E(E(E(_cW).c).a);}),_d0=new T(function(){var _d1=new T(function(){return B(_8s(new T(function(){return B(_8q(_cZ));})));}),_d2=new T(function(){return B(A2(_cT,_cZ,_cX));});return B(A3(_ad,B(_a5(E(_cW).a)),function(_d3){return new F(function(){return A3(_8u,_d1,_d3,_d2);});},_cY));});return new T2(0,new T(function(){return B(A2(_cR,_cZ,_cX));}),_d0);},_d4=function(_d5,_d6,_d7){var _d8=E(_d7),_d9=B(_cV(_d6,_d8.a,_d8.b));return new T2(0,_d9.a,_d9.b);},_da=function(_db){return E(E(_db).c);},_dc=function(_dd,_de,_df){var _dg=new T(function(){return E(E(E(_dd).c).a);}),_dh=new T(function(){var _di=new T(function(){return B(_8s(new T(function(){return B(_8q(_dg));})));}),_dj=new T(function(){return B(A2(_da,_dg,_de));});return B(A3(_ad,B(_a5(E(_dd).a)),function(_dk){return new F(function(){return A3(_8u,_di,_dk,_dj);});},_df));});return new T2(0,new T(function(){return B(A2(_da,_dg,_de));}),_dh);},_dl=function(_dm,_dn,_do){var _dp=E(_do),_dq=B(_dc(_dn,_dp.a,_dp.b));return new T2(0,_dq.a,_dq.b);},_dr=function(_ds,_dt,_du){var _dv=new T(function(){return E(E(E(_ds).c).a);}),_dw=new T(function(){var _dx=new T(function(){return B(_8q(_dv));}),_dy=new T(function(){return B(_8s(_dx));}),_dz=new T(function(){return B(A3(_a9,_dx,new T(function(){return B(A2(_9Z,_dy,_aI));}),_dt));});return B(A3(_ad,B(_a5(E(_ds).a)),function(_dA){return new F(function(){return A3(_8u,_dy,_dA,_dz);});},_du));});return new T2(0,new T(function(){return B(A2(_af,_dv,_dt));}),_dw);},_dB=function(_dC,_dD,_dE){var _dF=E(_dE),_dG=B(_dr(_dD,_dF.a,_dF.b));return new T2(0,_dG.a,_dG.b);},_dH=function(_dI,_dJ,_dK,_dL){var _dM=new T(function(){return E(E(_dJ).c);}),_dN=new T3(0,new T(function(){return E(E(_dJ).a);}),new T(function(){return E(E(_dJ).b);}),new T2(0,new T(function(){return E(E(_dM).a);}),new T(function(){return E(E(_dM).b);})));return new F(function(){return A3(_a9,_dI,new T(function(){var _dO=E(_dL),_dP=B(_dr(_dN,_dO.a,_dO.b));return new T2(0,_dP.a,_dP.b);}),new T(function(){var _dQ=E(_dK),_dR=B(_dr(_dN,_dQ.a,_dQ.b));return new T2(0,_dR.a,_dR.b);}));});},_dS=function(_dT){return E(E(_dT).b);},_dU=function(_dV){return E(E(_dV).b);},_dW=function(_dX){var _dY=new T(function(){return E(E(E(_dX).c).a);}),_dZ=new T(function(){return B(A2(_dU,E(_dX).a,new T(function(){return B(A2(_9Z,B(_8s(B(_8q(_dY)))),_L));})));});return new T2(0,new T(function(){return B(_dS(_dY));}),_dZ);},_e0=function(_e1,_e2){var _e3=B(_dW(_e2));return new T2(0,_e3.a,_e3.b);},_e4=function(_e5,_e6,_e7){var _e8=new T(function(){return E(E(E(_e5).c).a);}),_e9=new T(function(){var _ea=new T(function(){return B(_8s(new T(function(){return B(_8q(_e8));})));}),_eb=new T(function(){return B(A2(_cy,_e8,_e6));});return B(A3(_ad,B(_a5(E(_e5).a)),function(_ec){return new F(function(){return A3(_8u,_ea,_ec,_eb);});},_e7));});return new T2(0,new T(function(){return B(A2(_cA,_e8,_e6));}),_e9);},_ed=function(_ee,_ef,_eg){var _eh=E(_eg),_ei=B(_e4(_ef,_eh.a,_eh.b));return new T2(0,_ei.a,_ei.b);},_ej=function(_ek,_el,_em){var _en=new T(function(){return E(E(E(_ek).c).a);}),_eo=new T(function(){var _ep=new T(function(){return B(_8s(new T(function(){return B(_8q(_en));})));}),_eq=new T(function(){return B(A2(_cR,_en,_el));});return B(A3(_ad,B(_a5(E(_ek).a)),function(_er){return new F(function(){return A3(_8u,_ep,_er,_eq);});},_em));});return new T2(0,new T(function(){return B(A2(_cT,_en,_el));}),_eo);},_es=function(_et,_eu,_ev){var _ew=E(_ev),_ex=B(_ej(_eu,_ew.a,_ew.b));return new T2(0,_ex.a,_ex.b);},_ey=new T1(0,2),_ez=function(_eA,_eB,_eC){var _eD=new T(function(){return E(E(E(_eA).c).a);}),_eE=new T(function(){var _eF=new T(function(){return B(_8q(_eD));}),_eG=new T(function(){return B(_8s(_eF));}),_eH=new T(function(){var _eI=new T(function(){return B(A3(_a9,_eF,new T(function(){return B(A2(_9Z,_eG,_aI));}),new T(function(){return B(A2(_9Z,_eG,_ey));})));});return B(A3(_a9,_eF,_eI,new T(function(){return B(A2(_8F,_eD,_eB));})));});return B(A3(_ad,B(_a5(E(_eA).a)),function(_eJ){return new F(function(){return A3(_8u,_eG,_eJ,_eH);});},_eC));});return new T2(0,new T(function(){return B(A2(_8F,_eD,_eB));}),_eE);},_eK=function(_eL,_eM,_eN){var _eO=E(_eN),_eP=B(_ez(_eM,_eO.a,_eO.b));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR){return E(E(_eR).j);},_eS=function(_eT,_eU,_eV){var _eW=new T(function(){return E(E(E(_eT).c).a);}),_eX=new T(function(){var _eY=new T(function(){return B(_8q(_eW));}),_eZ=new T(function(){var _f0=new T(function(){return B(A2(_cy,_eW,_eU));});return B(A3(_8u,B(_8s(_eY)),_f0,_f0));});return B(A3(_ad,B(_a5(E(_eT).a)),function(_f1){return new F(function(){return A3(_a9,_eY,_f1,_eZ);});},_eV));});return new T2(0,new T(function(){return B(A2(_eQ,_eW,_eU));}),_eX);},_f2=function(_f3,_f4,_f5){var _f6=E(_f5),_f7=B(_eS(_f4,_f6.a,_f6.b));return new T2(0,_f7.a,_f7.b);},_f8=function(_f9){return E(E(_f9).p);},_fa=function(_fb,_fc,_fd){var _fe=new T(function(){return E(E(E(_fb).c).a);}),_ff=new T(function(){var _fg=new T(function(){return B(_8q(_fe));}),_fh=new T(function(){var _fi=new T(function(){return B(A2(_cR,_fe,_fc));});return B(A3(_8u,B(_8s(_fg)),_fi,_fi));});return B(A3(_ad,B(_a5(E(_fb).a)),function(_fj){return new F(function(){return A3(_a9,_fg,_fj,_fh);});},_fd));});return new T2(0,new T(function(){return B(A2(_f8,_fe,_fc));}),_ff);},_fk=function(_fl,_fm,_fn){var _fo=E(_fn),_fp=B(_fa(_fm,_fo.a,_fo.b));return new T2(0,_fp.a,_fp.b);},_fq=function(_fr,_fs){return {_:0,a:_fr,b:new T(function(){return B(_e0(_fr,_fs));}),c:function(_ft){return new F(function(){return _dl(_fr,_fs,_ft);});},d:function(_ft){return new F(function(){return _dB(_fr,_fs,_ft);});},e:function(_ft){return new F(function(){return _eK(_fr,_fs,_ft);});},f:function(_fu,_ft){return new F(function(){return _aA(_fr,_fs,_fu,_ft);});},g:function(_fu,_ft){return new F(function(){return _dH(_fr,_fs,_fu,_ft);});},h:function(_ft){return new F(function(){return _ed(_fr,_fs,_ft);});},i:function(_ft){return new F(function(){return _cL(_fr,_fs,_ft);});},j:function(_ft){return new F(function(){return _f2(_fr,_fs,_ft);});},k:function(_ft){return new F(function(){return _bz(_fr,_fs,_ft);});},l:function(_ft){return new F(function(){return _aX(_fr,_fs,_ft);});},m:function(_ft){return new F(function(){return _ca(_fr,_fs,_ft);});},n:function(_ft){return new F(function(){return _es(_fr,_fs,_ft);});},o:function(_ft){return new F(function(){return _d4(_fr,_fs,_ft);});},p:function(_ft){return new F(function(){return _fk(_fr,_fs,_ft);});},q:function(_ft){return new F(function(){return _bS(_fr,_fs,_ft);});},r:function(_ft){return new F(function(){return _bg(_fr,_fs,_ft);});},s:function(_ft){return new F(function(){return _cs(_fr,_fs,_ft);});}};},_fv=function(_fw,_fx,_fy,_fz,_fA){var _fB=new T(function(){return B(_8q(new T(function(){return E(E(E(_fw).c).a);})));}),_fC=new T(function(){var _fD=E(_fw).a,_fE=new T(function(){var _fF=new T(function(){return B(_8s(_fB));}),_fG=new T(function(){return B(A3(_8u,_fF,_fz,_fz));}),_fH=function(_fI,_fJ){var _fK=new T(function(){return B(A3(_8w,_fF,new T(function(){return B(A3(_8u,_fF,_fI,_fz));}),new T(function(){return B(A3(_8u,_fF,_fx,_fJ));})));});return new F(function(){return A3(_a9,_fB,_fK,_fG);});};return B(A3(_ad,B(_a5(_fD)),_fH,_fy));});return B(A3(_ab,_fD,_fE,_fA));});return new T2(0,new T(function(){return B(A3(_a9,_fB,_fx,_fz));}),_fC);},_fL=function(_fM,_fN,_fO,_fP){var _fQ=E(_fO),_fR=E(_fP),_fS=B(_fv(_fN,_fQ.a,_fQ.b,_fR.a,_fR.b));return new T2(0,_fS.a,_fS.b);},_fT=function(_fU,_fV){var _fW=new T(function(){return B(_8q(new T(function(){return E(E(E(_fU).c).a);})));}),_fX=new T(function(){return B(A2(_dU,E(_fU).a,new T(function(){return B(A2(_9Z,B(_8s(_fW)),_L));})));});return new T2(0,new T(function(){return B(A2(_8y,_fW,_fV));}),_fX);},_fY=function(_fZ,_g0,_g1){var _g2=B(_fT(_g0,_g1));return new T2(0,_g2.a,_g2.b);},_g3=function(_g4,_g5,_g6){var _g7=new T(function(){return B(_8q(new T(function(){return E(E(E(_g4).c).a);})));}),_g8=new T(function(){return B(_8s(_g7));}),_g9=new T(function(){var _ga=new T(function(){var _gb=new T(function(){return B(A3(_a9,_g7,new T(function(){return B(A2(_9Z,_g8,_aI));}),new T(function(){return B(A3(_8u,_g8,_g5,_g5));})));});return B(A2(_88,_g8,_gb));});return B(A3(_ad,B(_a5(E(_g4).a)),function(_gc){return new F(function(){return A3(_8u,_g8,_gc,_ga);});},_g6));}),_gd=new T(function(){return B(A3(_a9,_g7,new T(function(){return B(A2(_9Z,_g8,_aI));}),_g5));});return new T2(0,_gd,_g9);},_ge=function(_gf,_gg,_gh){var _gi=E(_gh),_gj=B(_g3(_gg,_gi.a,_gi.b));return new T2(0,_gj.a,_gj.b);},_gk=function(_gl,_gm){return new T4(0,_gl,function(_fu,_ft){return new F(function(){return _fL(_gl,_gm,_fu,_ft);});},function(_ft){return new F(function(){return _ge(_gl,_gm,_ft);});},function(_ft){return new F(function(){return _fY(_gl,_gm,_ft);});});},_gn=function(_go,_gp,_gq,_gr,_gs){var _gt=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_go).c).a);})));})));}),_gu=new T(function(){var _gv=E(_go).a,_gw=new T(function(){var _gx=function(_gy,_gz){return new F(function(){return A3(_86,_gt,new T(function(){return B(A3(_8u,_gt,_gp,_gz));}),new T(function(){return B(A3(_8u,_gt,_gy,_gr));}));});};return B(A3(_ad,B(_a5(_gv)),_gx,_gq));});return B(A3(_ab,_gv,_gw,_gs));});return new T2(0,new T(function(){return B(A3(_8u,_gt,_gp,_gr));}),_gu);},_gA=function(_gB,_gC,_gD){var _gE=E(_gC),_gF=E(_gD),_gG=B(_gn(_gB,_gE.a,_gE.b,_gF.a,_gF.b));return new T2(0,_gG.a,_gG.b);},_gH=function(_gI,_gJ,_gK,_gL,_gM){var _gN=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_gI).c).a);})));})));}),_gO=new T(function(){var _gP=E(_gI).a,_gQ=new T(function(){return B(A3(_ad,B(_a5(_gP)),new T(function(){return B(_86(_gN));}),_gK));});return B(A3(_ab,_gP,_gQ,_gM));});return new T2(0,new T(function(){return B(A3(_86,_gN,_gJ,_gL));}),_gO);},_gR=function(_gS,_gT,_gU){var _gV=E(_gT),_gW=E(_gU),_gX=B(_gH(_gS,_gV.a,_gV.b,_gW.a,_gW.b));return new T2(0,_gX.a,_gX.b);},_gY=function(_gZ,_h0,_h1){var _h2=B(_h3(_gZ));return new F(function(){return A3(_86,_h2,_h0,new T(function(){return B(A2(_88,_h2,_h1));}));});},_h4=function(_h5){return E(E(_h5).e);},_h6=function(_h7){return E(E(_h7).f);},_h8=function(_h9,_ha,_hb){var _hc=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_h9).c).a);})));})));}),_hd=new T(function(){var _he=new T(function(){return B(A2(_h6,_hc,_ha));});return B(A3(_ad,B(_a5(E(_h9).a)),function(_hf){return new F(function(){return A3(_8u,_hc,_hf,_he);});},_hb));});return new T2(0,new T(function(){return B(A2(_h4,_hc,_ha));}),_hd);},_hg=function(_hh,_hi){var _hj=E(_hi),_hk=B(_h8(_hh,_hj.a,_hj.b));return new T2(0,_hk.a,_hk.b);},_hl=function(_hm,_hn){var _ho=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hm).c).a);})));})));}),_hp=new T(function(){return B(A2(_dU,E(_hm).a,new T(function(){return B(A2(_9Z,_ho,_L));})));});return new T2(0,new T(function(){return B(A2(_9Z,_ho,_hn));}),_hp);},_hq=function(_hr,_hs){var _ht=B(_hl(_hr,_hs));return new T2(0,_ht.a,_ht.b);},_hu=function(_hv,_hw,_hx){var _hy=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hv).c).a);})));})));}),_hz=new T(function(){return B(A3(_ad,B(_a5(E(_hv).a)),new T(function(){return B(_88(_hy));}),_hx));});return new T2(0,new T(function(){return B(A2(_88,_hy,_hw));}),_hz);},_hA=function(_hB,_hC){var _hD=E(_hC),_hE=B(_hu(_hB,_hD.a,_hD.b));return new T2(0,_hE.a,_hE.b);},_hF=function(_hG,_hH){var _hI=new T(function(){return B(_8s(new T(function(){return B(_8q(new T(function(){return E(E(E(_hG).c).a);})));})));}),_hJ=new T(function(){return B(A2(_dU,E(_hG).a,new T(function(){return B(A2(_9Z,_hI,_L));})));});return new T2(0,new T(function(){return B(A2(_h6,_hI,_hH));}),_hJ);},_hK=function(_hL,_hM){var _hN=B(_hF(_hL,E(_hM).a));return new T2(0,_hN.a,_hN.b);},_h3=function(_hO){return {_:0,a:function(_fu,_ft){return new F(function(){return _gR(_hO,_fu,_ft);});},b:function(_fu,_ft){return new F(function(){return _gY(_hO,_fu,_ft);});},c:function(_fu,_ft){return new F(function(){return _gA(_hO,_fu,_ft);});},d:function(_ft){return new F(function(){return _hA(_hO,_ft);});},e:function(_ft){return new F(function(){return _hg(_hO,_ft);});},f:function(_ft){return new F(function(){return _hK(_hO,_ft);});},g:function(_ft){return new F(function(){return _hq(_hO,_ft);});}};},_hP=function(_hQ){var _hR=new T(function(){return E(E(_hQ).a);}),_hS=new T3(0,_9X,_a1,new T2(0,_hR,new T(function(){return E(E(_hQ).b);}))),_hT=new T(function(){return B(_fq(new T(function(){return B(_gk(new T(function(){return B(_h3(_hS));}),_hS));}),_hS));}),_hU=new T(function(){return B(_8s(new T(function(){return B(_8q(_hR));})));});return function(_hV){var _hW=E(_hV),_hX=B(A2(_9Z,_hU,_1o)),_hY=B(A2(_9Z,_hU,_9Y));return E(B(_8H(_hT,new T2(0,_hW.a,new T3(0,E(_hX),E(_hY),E(_hY))),new T2(0,_hW.b,new T3(0,E(_hY),E(_hX),E(_hY))),new T2(0,_hW.c,new T3(0,E(_hY),E(_hY),E(_hX))))).b);};},_hZ=new T(function(){return B(_hP(_9t));}),_i0=function(_i1,_i2){var _i3=E(_i2);return (_i3._==0)?__Z:new T2(1,_i1,new T2(1,_i3.a,new T(function(){return B(_i0(_i1,_i3.b));})));},_i4=new T(function(){var _i5=B(A1(_hZ,_92));return new T2(1,_i5.a,new T(function(){return B(_i0(_22,new T2(1,_i5.b,new T2(1,_i5.c,_w))));}));}),_i6=new T1(1,_i4),_i7=new T2(1,_i6,_1S),_i8=new T(function(){return B(unCStr("vec3("));}),_i9=new T1(0,_i8),_ia=new T2(1,_i9,_i7),_ib=new T(function(){return toJSStr(B(_1F(_x,_1l,_ia)));}),_ic=function(_id,_ie){while(1){var _if=E(_id);if(!_if._){return E(_ie);}else{var _ig=_ie+1|0;_id=_if.b;_ie=_ig;continue;}}},_ih=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_ii=new T(function(){return B(err(_ih));}),_ij=0,_ik=new T3(0,E(_ij),E(_ij),E(_ij)),_il=new T(function(){return B(unCStr("Negative exponent"));}),_im=new T(function(){return B(err(_il));}),_in=function(_io,_ip,_iq){while(1){if(!(_ip%2)){var _ir=_io*_io,_is=quot(_ip,2);_io=_ir;_ip=_is;continue;}else{var _it=E(_ip);if(_it==1){return _io*_iq;}else{var _ir=_io*_io,_iu=_io*_iq;_io=_ir;_ip=quot(_it-1|0,2);_iq=_iu;continue;}}}},_iv=function(_iw,_ix){while(1){if(!(_ix%2)){var _iy=_iw*_iw,_iz=quot(_ix,2);_iw=_iy;_ix=_iz;continue;}else{var _iA=E(_ix);if(_iA==1){return E(_iw);}else{return new F(function(){return _in(_iw*_iw,quot(_iA-1|0,2),_iw);});}}}},_iB=function(_iC){var _iD=E(_iC);return new F(function(){return Math.log(_iD+(_iD+1)*Math.sqrt((_iD-1)/(_iD+1)));});},_iE=function(_iF){var _iG=E(_iF);return new F(function(){return Math.log(_iG+Math.sqrt(1+_iG*_iG));});},_iH=function(_iI){var _iJ=E(_iI);return 0.5*Math.log((1+_iJ)/(1-_iJ));},_iK=function(_iL,_iM){return Math.log(E(_iM))/Math.log(E(_iL));},_iN=3.141592653589793,_iO=function(_iP){var _iQ=E(_iP);return new F(function(){return _7J(_iQ.a,_iQ.b);});},_iR=function(_iS){return 1/E(_iS);},_iT=function(_iU){var _iV=E(_iU),_iW=E(_iV);return (_iW==0)?E(_7I):(_iW<=0)? -_iW:E(_iV);},_iX=function(_iY){var _iZ=E(_iY);if(!_iZ._){return _iZ.a;}else{return new F(function(){return I_toNumber(_iZ.a);});}},_j0=function(_j1){return new F(function(){return _iX(_j1);});},_j2=1,_j3=-1,_j4=function(_j5){var _j6=E(_j5);return (_j6<=0)?(_j6>=0)?E(_j6):E(_j3):E(_j2);},_j7=function(_j8,_j9){return E(_j8)-E(_j9);},_ja=function(_jb){return  -E(_jb);},_jc=function(_jd,_je){return E(_jd)+E(_je);},_jf=function(_jg,_jh){return E(_jg)*E(_jh);},_ji={_:0,a:_jc,b:_j7,c:_jf,d:_ja,e:_iT,f:_j4,g:_j0},_jj=function(_jk,_jl){return E(_jk)/E(_jl);},_jm=new T4(0,_ji,_jj,_iR,_iO),_jn=function(_jo){return new F(function(){return Math.acos(E(_jo));});},_jp=function(_jq){return new F(function(){return Math.asin(E(_jq));});},_jr=function(_js){return new F(function(){return Math.atan(E(_js));});},_jt=function(_ju){return new F(function(){return Math.cos(E(_ju));});},_jv=function(_jw){return new F(function(){return cosh(E(_jw));});},_jx=function(_jy){return new F(function(){return Math.exp(E(_jy));});},_jz=function(_jA){return new F(function(){return Math.log(E(_jA));});},_jB=function(_jC,_jD){return new F(function(){return Math.pow(E(_jC),E(_jD));});},_jE=function(_jF){return new F(function(){return Math.sin(E(_jF));});},_jG=function(_jH){return new F(function(){return sinh(E(_jH));});},_jI=function(_jJ){return new F(function(){return Math.sqrt(E(_jJ));});},_jK=function(_jL){return new F(function(){return Math.tan(E(_jL));});},_jM=function(_jN){return new F(function(){return tanh(E(_jN));});},_jO={_:0,a:_jm,b:_iN,c:_jx,d:_jz,e:_jI,f:_jB,g:_iK,h:_jE,i:_jt,j:_jK,k:_jp,l:_jn,m:_jr,n:_jG,o:_jv,p:_jM,q:_iE,r:_iB,s:_iH},_jP=function(_jQ,_jR){return (E(_jQ)!=E(_jR))?true:false;},_jS=function(_jT,_jU){return E(_jT)==E(_jU);},_jV=new T2(0,_jS,_jP),_jW=function(_jX,_jY){return E(_jX)<E(_jY);},_jZ=function(_k0,_k1){return E(_k0)<=E(_k1);},_k2=function(_k3,_k4){return E(_k3)>E(_k4);},_k5=function(_k6,_k7){return E(_k6)>=E(_k7);},_k8=function(_k9,_ka){var _kb=E(_k9),_kc=E(_ka);return (_kb>=_kc)?(_kb!=_kc)?2:1:0;},_kd=function(_ke,_kf){var _kg=E(_ke),_kh=E(_kf);return (_kg>_kh)?E(_kg):E(_kh);},_ki=function(_kj,_kk){var _kl=E(_kj),_km=E(_kk);return (_kl>_km)?E(_km):E(_kl);},_kn={_:0,a:_jV,b:_k8,c:_jW,d:_jZ,e:_k2,f:_k5,g:_kd,h:_ki},_ko="dz",_kp="wy",_kq="wx",_kr="dy",_ks="dx",_kt="t",_ku="a",_kv="r",_kw="ly",_kx="lx",_ky="wz",_kz=0,_kA=function(_kB){var _kC=__new(),_kD=_kC,_kE=function(_kF,_){while(1){var _kG=E(_kF);if(!_kG._){return _kz;}else{var _kH=E(_kG.a),_kI=__set(_kD,E(_kH.a),E(_kH.b));_kF=_kG.b;continue;}}},_kJ=B(_kE(_kB,_));return E(_kD);},_kK=function(_kL,_kM,_kN,_kO,_kP,_kQ,_kR,_kS,_kT){return new F(function(){return _kA(new T2(1,new T2(0,_kq,_kL),new T2(1,new T2(0,_kp,_kM),new T2(1,new T2(0,_ky,_kN),new T2(1,new T2(0,_kx,_kO*_kP*Math.cos(_kQ)),new T2(1,new T2(0,_kw,_kO*_kP*Math.sin(_kQ)),new T2(1,new T2(0,_kv,_kO),new T2(1,new T2(0,_ku,_kP),new T2(1,new T2(0,_kt,_kQ),new T2(1,new T2(0,_ks,_kR),new T2(1,new T2(0,_kr,_kS),new T2(1,new T2(0,_ko,_kT),_w))))))))))));});},_kU=function(_kV){var _kW=E(_kV),_kX=E(_kW.a),_kY=E(_kW.b),_kZ=E(_kW.d);return new F(function(){return _kK(_kX.a,_kX.b,_kX.c,E(_kY.a),E(_kY.b),E(_kW.c),_kZ.a,_kZ.b,_kZ.c);});},_l0=function(_l1,_l2){var _l3=E(_l2);return (_l3._==0)?__Z:new T2(1,new T(function(){return B(A1(_l1,_l3.a));}),new T(function(){return B(_l0(_l1,_l3.b));}));},_l4=function(_l5,_l6,_l7){var _l8=__lst2arr(B(_l0(_kU,new T2(1,_l5,new T2(1,_l6,new T2(1,_l7,_w))))));return E(_l8);},_l9=function(_la){var _lb=E(_la);return new F(function(){return _l4(_lb.a,_lb.b,_lb.c);});},_lc=new T2(0,_jO,_kn),_ld=function(_le,_lf,_lg,_lh,_li,_lj,_lk){var _ll=B(_8s(B(_8q(_le)))),_lm=new T(function(){return B(A3(_86,_ll,new T(function(){return B(A3(_8u,_ll,_lf,_li));}),new T(function(){return B(A3(_8u,_ll,_lg,_lj));})));});return new F(function(){return A3(_86,_ll,_lm,new T(function(){return B(A3(_8u,_ll,_lh,_lk));}));});},_ln=function(_lo,_lp,_lq,_lr){var _ls=B(_8q(_lo)),_lt=new T(function(){return B(A2(_8F,_lo,new T(function(){return B(_ld(_lo,_lp,_lq,_lr,_lp,_lq,_lr));})));});return new T3(0,B(A3(_a9,_ls,_lp,_lt)),B(A3(_a9,_ls,_lq,_lt)),B(A3(_a9,_ls,_lr,_lt)));},_lu=function(_lv,_lw,_lx,_ly,_lz,_lA,_lB){var _lC=B(_8u(_lv));return new T3(0,B(A1(B(A1(_lC,_lw)),_lz)),B(A1(B(A1(_lC,_lx)),_lA)),B(A1(B(A1(_lC,_ly)),_lB)));},_lD=function(_lE,_lF,_lG,_lH,_lI,_lJ,_lK){var _lL=B(_86(_lE));return new T3(0,B(A1(B(A1(_lL,_lF)),_lI)),B(A1(B(A1(_lL,_lG)),_lJ)),B(A1(B(A1(_lL,_lH)),_lK)));},_lM=function(_lN,_lO){var _lP=new T(function(){return E(E(_lN).a);}),_lQ=new T(function(){return B(A2(_hP,new T2(0,_lP,new T(function(){return E(E(_lN).b);})),_lO));}),_lR=new T(function(){var _lS=E(_lQ),_lT=B(_ln(_lP,_lS.a,_lS.b,_lS.c));return new T3(0,E(_lT.a),E(_lT.b),E(_lT.c));}),_lU=new T(function(){var _lV=E(_lO),_lW=_lV.a,_lX=_lV.b,_lY=_lV.c,_lZ=E(_lR),_m0=B(_8q(_lP)),_m1=new T(function(){return B(A2(_8F,_lP,new T(function(){var _m2=E(_lQ),_m3=_m2.a,_m4=_m2.b,_m5=_m2.c;return B(_ld(_lP,_m3,_m4,_m5,_m3,_m4,_m5));})));}),_m6=B(A3(_a9,_m0,new T(function(){return B(_8H(_lP,_lW,_lX,_lY));}),_m1)),_m7=B(_8s(_m0)),_m8=B(_lu(_m7,_lZ.a,_lZ.b,_lZ.c,_m6,_m6,_m6)),_m9=B(_88(_m7)),_ma=B(_lD(_m7,_lW,_lX,_lY,B(A1(_m9,_m8.a)),B(A1(_m9,_m8.b)),B(A1(_m9,_m8.c))));return new T3(0,E(_ma.a),E(_ma.b),E(_ma.c));});return new T2(0,_lU,_lR);},_mb=function(_mc){return E(E(_mc).a);},_md=function(_me,_mf,_mg,_mh,_mi,_mj,_mk){var _ml=B(_ld(_me,_mi,_mj,_mk,_mf,_mg,_mh)),_mm=B(_8s(B(_8q(_me)))),_mn=B(_lu(_mm,_mi,_mj,_mk,_ml,_ml,_ml)),_mo=B(_88(_mm));return new F(function(){return _lD(_mm,_mf,_mg,_mh,B(A1(_mo,_mn.a)),B(A1(_mo,_mn.b)),B(A1(_mo,_mn.c)));});},_mp=function(_mq){return E(E(_mq).a);},_mr=function(_ms,_mt,_mu,_mv){var _mw=new T(function(){var _mx=E(_mv),_my=E(_mu),_mz=B(_md(_ms,_mx.a,_mx.b,_mx.c,_my.a,_my.b,_my.c));return new T3(0,E(_mz.a),E(_mz.b),E(_mz.c));}),_mA=new T(function(){return B(A2(_8F,_ms,new T(function(){var _mB=E(_mw),_mC=_mB.a,_mD=_mB.b,_mE=_mB.c;return B(_ld(_ms,_mC,_mD,_mE,_mC,_mD,_mE));})));});if(!B(A3(_mp,B(_mb(_mt)),_mA,new T(function(){return B(A2(_9Z,B(_8s(B(_8q(_ms)))),_9Y));})))){var _mF=E(_mw),_mG=B(_ln(_ms,_mF.a,_mF.b,_mF.c)),_mH=B(A2(_8F,_ms,new T(function(){var _mI=E(_mv),_mJ=_mI.a,_mK=_mI.b,_mL=_mI.c;return B(_ld(_ms,_mJ,_mK,_mL,_mJ,_mK,_mL));}))),_mM=B(_8u(new T(function(){return B(_8s(new T(function(){return B(_8q(_ms));})));})));return new T3(0,B(A1(B(A1(_mM,_mG.a)),_mH)),B(A1(B(A1(_mM,_mG.b)),_mH)),B(A1(B(A1(_mM,_mG.c)),_mH)));}else{var _mN=B(A2(_9Z,B(_8s(B(_8q(_ms)))),_9Y));return new T3(0,_mN,_mN,_mN);}},_mO=function(_mP,_mQ){while(1){var _mR=E(_mP);if(!_mR._){return E(_mQ);}else{var _mS=_mR.b,_mT=E(_mR.a);if(_mQ>_mT){_mP=_mS;continue;}else{_mP=_mS;_mQ=_mT;continue;}}}},_mU=new T(function(){var _mV=eval("angleCount"),_mW=Number(_mV);return jsTrunc(_mW);}),_mX=new T(function(){return E(_mU);}),_mY=new T(function(){return B(unCStr(": empty list"));}),_mZ=new T(function(){return B(unCStr("Prelude."));}),_n0=function(_n1){return new F(function(){return err(B(_n(_mZ,new T(function(){return B(_n(_n1,_mY));},1))));});},_n2=new T(function(){return B(unCStr("head"));}),_n3=new T(function(){return B(_n0(_n2));}),_n4=function(_n5,_n6,_n7){var _n8=E(_n5);if(!_n8._){return __Z;}else{var _n9=E(_n6);if(!_n9._){return __Z;}else{var _na=_n9.a,_nb=E(_n7);if(!_nb._){return __Z;}else{var _nc=E(_nb.a),_nd=_nc.a;return new F(function(){return _n(new T2(1,new T(function(){return new T3(0,E(_n8.a),E(_na),E(_nd));}),new T2(1,new T(function(){return new T3(0,E(_na),E(_nd),E(_nc.b));}),_w)),new T(function(){return B(_n4(_n8.b,_n9.b,_nb.b));},1));});}}}},_ne=new T(function(){return B(unCStr("tail"));}),_nf=new T(function(){return B(_n0(_ne));}),_ng=function(_nh,_ni){var _nj=E(_nh);if(!_nj._){return __Z;}else{var _nk=E(_ni);return (_nk._==0)?__Z:new T2(1,new T2(0,_nj.a,_nk.a),new T(function(){return B(_ng(_nj.b,_nk.b));}));}},_nl=function(_nm,_nn){var _no=E(_nm);if(!_no._){return __Z;}else{var _np=E(_nn);if(!_np._){return __Z;}else{var _nq=E(_no.a),_nr=_nq.b,_ns=E(_np.a).b,_nt=new T(function(){var _nu=new T(function(){return B(_ng(_ns,new T(function(){var _nv=E(_ns);if(!_nv._){return E(_nf);}else{return E(_nv.b);}},1)));},1);return B(_n4(_nr,new T(function(){var _nw=E(_nr);if(!_nw._){return E(_nf);}else{return E(_nw.b);}},1),_nu));});return new F(function(){return _n(new T2(1,new T(function(){var _nx=E(_nr);if(!_nx._){return E(_n3);}else{var _ny=E(_ns);if(!_ny._){return E(_n3);}else{return new T3(0,E(_nq.a),E(_nx.a),E(_ny.a));}}}),_nt),new T(function(){return B(_nl(_no.b,_np.b));},1));});}}},_nz=new T(function(){return 6.283185307179586/E(_mX);}),_nA=new T(function(){return E(_mX)-1;}),_nB=new T1(0,1),_nC=function(_nD,_nE){var _nF=E(_nE),_nG=new T(function(){var _nH=B(_8s(_nD)),_nI=B(_nC(_nD,B(A3(_86,_nH,_nF,new T(function(){return B(A2(_9Z,_nH,_nB));})))));return new T2(1,_nI.a,_nI.b);});return new T2(0,_nF,_nG);},_nJ=function(_nK){return E(E(_nK).d);},_nL=new T1(0,2),_nM=function(_nN,_nO){var _nP=E(_nO);if(!_nP._){return __Z;}else{var _nQ=_nP.a;return (!B(A1(_nN,_nQ)))?__Z:new T2(1,_nQ,new T(function(){return B(_nM(_nN,_nP.b));}));}},_nR=function(_nS,_nT,_nU,_nV){var _nW=B(_nC(_nT,_nU)),_nX=new T(function(){var _nY=B(_8s(_nT)),_nZ=new T(function(){return B(A3(_a9,_nT,new T(function(){return B(A2(_9Z,_nY,_nB));}),new T(function(){return B(A2(_9Z,_nY,_nL));})));});return B(A3(_86,_nY,_nV,_nZ));});return new F(function(){return _nM(function(_o0){return new F(function(){return A3(_nJ,_nS,_o0,_nX);});},new T2(1,_nW.a,_nW.b));});},_o1=new T(function(){return B(_nR(_kn,_jm,_ij,_nA));}),_o2=function(_o3,_o4){while(1){var _o5=E(_o3);if(!_o5._){return E(_o4);}else{_o3=_o5.b;_o4=_o5.a;continue;}}},_o6=new T(function(){return B(unCStr("last"));}),_o7=new T(function(){return B(_n0(_o6));}),_o8=function(_o9){return new F(function(){return _o2(_o9,_o7);});},_oa=function(_ob){return new F(function(){return _o8(E(_ob).b);});},_oc=new T(function(){return B(unCStr("maximum"));}),_od=new T(function(){return B(_n0(_oc));}),_oe=new T(function(){var _of=eval("proceedCount"),_og=Number(_of);return jsTrunc(_og);}),_oh=new T(function(){return E(_oe);}),_oi=1,_oj=new T(function(){return B(_nR(_kn,_jm,_oi,_oh));}),_ok=function(_ol,_om,_on,_oo,_op,_oq,_or,_os,_ot,_ou,_ov,_ow,_ox,_oy){var _oz=new T(function(){var _oA=new T(function(){var _oB=E(_ou),_oC=E(_oy),_oD=E(_ox),_oE=E(_ov),_oF=E(_ow),_oG=E(_ot);return new T3(0,_oB*_oC-_oD*_oE,_oE*_oF-_oC*_oG,_oG*_oD-_oF*_oB);}),_oH=function(_oI){var _oJ=new T(function(){var _oK=E(_oI)/E(_mX);return (_oK+_oK)*3.141592653589793;}),_oL=new T(function(){return B(A1(_ol,_oJ));}),_oM=new T(function(){var _oN=new T(function(){var _oO=E(_oL)/E(_oh);return new T3(0,E(_oO),E(_oO),E(_oO));}),_oP=function(_oQ,_oR){var _oS=E(_oQ);if(!_oS._){return new T2(0,_w,_oR);}else{var _oT=new T(function(){var _oU=B(_lM(_lc,new T(function(){var _oV=E(_oR),_oW=E(_oV.a),_oX=E(_oV.b),_oY=E(_oN);return new T3(0,E(_oW.a)+E(_oX.a)*E(_oY.a),E(_oW.b)+E(_oX.b)*E(_oY.b),E(_oW.c)+E(_oX.c)*E(_oY.c));}))),_oZ=_oU.a,_p0=new T(function(){var _p1=E(_oU.b),_p2=E(E(_oR).b),_p3=B(_md(_jO,_p2.a,_p2.b,_p2.c,_p1.a,_p1.b,_p1.c)),_p4=B(_ln(_jO,_p3.a,_p3.b,_p3.c));return new T3(0,E(_p4.a),E(_p4.b),E(_p4.c));});return new T2(0,new T(function(){var _p5=E(_oL),_p6=E(_oJ);return new T4(0,E(_oZ),E(new T2(0,E(_oS.a)/E(_oh),E(_p5))),E(_p6),E(_p0));}),new T2(0,_oZ,_p0));}),_p7=new T(function(){var _p8=B(_oP(_oS.b,new T(function(){return E(E(_oT).b);})));return new T2(0,_p8.a,_p8.b);});return new T2(0,new T2(1,new T(function(){return E(E(_oT).a);}),new T(function(){return E(E(_p7).a);})),new T(function(){return E(E(_p7).b);}));}},_p9=function(_pa,_pb,_pc,_pd,_pe){var _pf=E(_pa);if(!_pf._){return new T2(0,_w,new T2(0,new T3(0,E(_pb),E(_pc),E(_pd)),_pe));}else{var _pg=new T(function(){var _ph=B(_lM(_lc,new T(function(){var _pi=E(_pe),_pj=E(_oN);return new T3(0,E(_pb)+E(_pi.a)*E(_pj.a),E(_pc)+E(_pi.b)*E(_pj.b),E(_pd)+E(_pi.c)*E(_pj.c));}))),_pk=_ph.a,_pl=new T(function(){var _pm=E(_ph.b),_pn=E(_pe),_po=B(_md(_jO,_pn.a,_pn.b,_pn.c,_pm.a,_pm.b,_pm.c)),_pp=B(_ln(_jO,_po.a,_po.b,_po.c));return new T3(0,E(_pp.a),E(_pp.b),E(_pp.c));});return new T2(0,new T(function(){var _pq=E(_oL),_pr=E(_oJ);return new T4(0,E(_pk),E(new T2(0,E(_pf.a)/E(_oh),E(_pq))),E(_pr),E(_pl));}),new T2(0,_pk,_pl));}),_ps=new T(function(){var _pt=B(_oP(_pf.b,new T(function(){return E(E(_pg).b);})));return new T2(0,_pt.a,_pt.b);});return new T2(0,new T2(1,new T(function(){return E(E(_pg).a);}),new T(function(){return E(E(_ps).a);})),new T(function(){return E(E(_ps).b);}));}};return E(B(_p9(_oj,_oo,_op,_oq,new T(function(){var _pu=E(_oA),_pv=E(_oJ)+_or,_pw=Math.cos(_pv),_px=Math.sin(_pv);return new T3(0,E(_ot)*_pw+E(_pu.a)*_px,E(_ou)*_pw+E(_pu.b)*_px,E(_ov)*_pw+E(_pu.c)*_px);}))).a);});return new T2(0,new T(function(){var _py=E(_oL),_pz=E(_oJ);return new T4(0,E(new T3(0,E(_oo),E(_op),E(_oq))),E(new T2(0,E(_ij),E(_py))),E(_pz),E(_ik));}),_oM);};return B(_l0(_oH,_o1));}),_pA=new T(function(){var _pB=function(_pC){return new F(function(){return A1(_ol,new T(function(){return B(_jf(_pC,_nz));}));});},_pD=B(_l0(_pB,_o1));if(!_pD._){return E(_od);}else{return B(_mO(_pD.b,E(_pD.a)));}}),_pE=new T(function(){var _pF=new T(function(){var _pG=B(_n(_oz,new T2(1,new T(function(){var _pH=E(_oz);if(!_pH._){return E(_n3);}else{return E(_pH.a);}}),_w)));if(!_pG._){return E(_nf);}else{return E(_pG.b);}},1);return B(_nl(_oz,_pF));});return new T3(0,_pE,new T(function(){return B(_l0(_oa,_oz));}),_pA);},_pI=function(_pJ,_pK,_pL,_pM,_pN,_pO,_pP,_pQ,_pR,_pS,_pT,_pU,_pV,_pW,_pX,_pY,_pZ,_q0){var _q1=B(_lM(_lc,new T3(0,E(_pM),E(_pN),E(_pO)))),_q2=_q1.b,_q3=E(_q1.a),_q4=B(_mr(_jO,_kn,_q2,new T3(0,E(_pQ),E(_pR),E(_pS)))),_q5=E(_q2),_q6=_q5.a,_q7=_q5.b,_q8=_q5.c,_q9=B(_md(_jO,_pU,_pV,_pW,_q6,_q7,_q8)),_qa=B(_ln(_jO,_q9.a,_q9.b,_q9.c)),_qb=_qa.a,_qc=_qa.b,_qd=_qa.c,_qe=E(_pP),_qf=new T2(0,E(new T3(0,E(_q4.a),E(_q4.b),E(_q4.c))),E(_pT)),_qg=B(_ok(_pJ,_pK,_pL,_q3.a,_q3.b,_q3.c,_qe,_qf,_qb,_qc,_qd,_q6,_q7,_q8)),_qh=__lst2arr(B(_l0(_l9,_qg.a))),_qi=__lst2arr(B(_l0(_kU,_qg.b)));return {_:0,a:_pJ,b:_pK,c:_pL,d:new T2(0,E(_q3),E(_qe)),e:_qf,f:new T3(0,E(_qb),E(_qc),E(_qd)),g:_q5,h:_qh,i:_qi,j:E(_qg.c)};},_qj=-4,_qk=new T3(0,E(_ij),E(_ij),E(_qj)),_ql=function(_qm){return E(_qk);},_qn=function(_){return new F(function(){return __jsNull();});},_qo=function(_qp){var _qq=B(A1(_qp,_));return E(_qq);},_qr=new T(function(){return B(_qo(_qn));}),_qs=function(_qt,_qu,_qv,_qw,_qx,_qy,_qz,_qA,_qB,_qC,_qD,_qE,_qF){var _qG=function(_qH){var _qI=E(_nz),_qJ=2+_qH|0,_qK=_qJ-1|0,_qL=(2+_qH)*(1+_qH),_qM=E(_o1);if(!_qM._){return _qI*0;}else{var _qN=_qM.a,_qO=_qM.b,_qP=B(A1(_qt,new T(function(){return 6.283185307179586*E(_qN)/E(_mX);}))),_qQ=B(A1(_qt,new T(function(){return 6.283185307179586*(E(_qN)+1)/E(_mX);})));if(_qP!=_qQ){if(_qJ>=0){var _qR=E(_qJ);if(!_qR){var _qS=function(_qT,_qU){while(1){var _qV=B((function(_qW,_qX){var _qY=E(_qW);if(!_qY._){return E(_qX);}else{var _qZ=_qY.a,_r0=_qY.b,_r1=B(A1(_qt,new T(function(){return 6.283185307179586*E(_qZ)/E(_mX);}))),_r2=B(A1(_qt,new T(function(){return 6.283185307179586*(E(_qZ)+1)/E(_mX);})));if(_r1!=_r2){var _r3=_qX+0/(_r1-_r2)/_qL;_qT=_r0;_qU=_r3;return __continue;}else{if(_qK>=0){var _r4=E(_qK);if(!_r4){var _r3=_qX+_qJ/_qL;_qT=_r0;_qU=_r3;return __continue;}else{var _r3=_qX+_qJ*B(_iv(_r1,_r4))/_qL;_qT=_r0;_qU=_r3;return __continue;}}else{return E(_im);}}}})(_qT,_qU));if(_qV!=__continue){return _qV;}}};return _qI*B(_qS(_qO,0/(_qP-_qQ)/_qL));}else{var _r5=function(_r6,_r7){while(1){var _r8=B((function(_r9,_ra){var _rb=E(_r9);if(!_rb._){return E(_ra);}else{var _rc=_rb.a,_rd=_rb.b,_re=B(A1(_qt,new T(function(){return 6.283185307179586*E(_rc)/E(_mX);}))),_rf=B(A1(_qt,new T(function(){return 6.283185307179586*(E(_rc)+1)/E(_mX);})));if(_re!=_rf){if(_qR>=0){var _rg=_ra+(B(_iv(_re,_qR))-B(_iv(_rf,_qR)))/(_re-_rf)/_qL;_r6=_rd;_r7=_rg;return __continue;}else{return E(_im);}}else{if(_qK>=0){var _rh=E(_qK);if(!_rh){var _rg=_ra+_qJ/_qL;_r6=_rd;_r7=_rg;return __continue;}else{var _rg=_ra+_qJ*B(_iv(_re,_rh))/_qL;_r6=_rd;_r7=_rg;return __continue;}}else{return E(_im);}}}})(_r6,_r7));if(_r8!=__continue){return _r8;}}};return _qI*B(_r5(_qO,(B(_iv(_qP,_qR))-B(_iv(_qQ,_qR)))/(_qP-_qQ)/_qL));}}else{return E(_im);}}else{if(_qK>=0){var _ri=E(_qK);if(!_ri){var _rj=function(_rk,_rl){while(1){var _rm=B((function(_rn,_ro){var _rp=E(_rn);if(!_rp._){return E(_ro);}else{var _rq=_rp.a,_rr=_rp.b,_rs=B(A1(_qt,new T(function(){return 6.283185307179586*E(_rq)/E(_mX);}))),_rt=B(A1(_qt,new T(function(){return 6.283185307179586*(E(_rq)+1)/E(_mX);})));if(_rs!=_rt){if(_qJ>=0){var _ru=E(_qJ);if(!_ru){var _rv=_ro+0/(_rs-_rt)/_qL;_rk=_rr;_rl=_rv;return __continue;}else{var _rv=_ro+(B(_iv(_rs,_ru))-B(_iv(_rt,_ru)))/(_rs-_rt)/_qL;_rk=_rr;_rl=_rv;return __continue;}}else{return E(_im);}}else{var _rv=_ro+_qJ/_qL;_rk=_rr;_rl=_rv;return __continue;}}})(_rk,_rl));if(_rm!=__continue){return _rm;}}};return _qI*B(_rj(_qO,_qJ/_qL));}else{var _rw=function(_rx,_ry){while(1){var _rz=B((function(_rA,_rB){var _rC=E(_rA);if(!_rC._){return E(_rB);}else{var _rD=_rC.a,_rE=_rC.b,_rF=B(A1(_qt,new T(function(){return 6.283185307179586*E(_rD)/E(_mX);}))),_rG=B(A1(_qt,new T(function(){return 6.283185307179586*(E(_rD)+1)/E(_mX);})));if(_rF!=_rG){if(_qJ>=0){var _rH=E(_qJ);if(!_rH){var _rI=_rB+0/(_rF-_rG)/_qL;_rx=_rE;_ry=_rI;return __continue;}else{var _rI=_rB+(B(_iv(_rF,_rH))-B(_iv(_rG,_rH)))/(_rF-_rG)/_qL;_rx=_rE;_ry=_rI;return __continue;}}else{return E(_im);}}else{if(_ri>=0){var _rI=_rB+_qJ*B(_iv(_rF,_ri))/_qL;_rx=_rE;_ry=_rI;return __continue;}else{return E(_im);}}}})(_rx,_ry));if(_rz!=__continue){return _rz;}}};return _qI*B(_rw(_qO,_qJ*B(_iv(_qP,_ri))/_qL));}}else{return E(_im);}}}},_rJ=E(_qr),_rK=1/(B(_qG(1))*_qu);return new F(function(){return _pI(_qt,_ql,new T2(0,E(new T3(0,E(_rK),E(_rK),E(_rK))),1/(B(_qG(3))*_qu)),_qv,_qw,_qx,_qy,_qz,_qA,_qB,_qC,_qD,_qE,_qF,_ik,_rJ,_rJ,0);});},_rL=1,_rM=function(_rN){var _rO=I_decodeDouble(_rN);return new T2(0,new T1(1,_rO.b),_rO.a);},_rP=function(_rQ){return new T1(0,_rQ);},_rR=function(_rS){var _rT=hs_intToInt64(2147483647),_rU=hs_leInt64(_rS,_rT);if(!_rU){return new T1(1,I_fromInt64(_rS));}else{var _rV=hs_intToInt64(-2147483648),_rW=hs_geInt64(_rS,_rV);if(!_rW){return new T1(1,I_fromInt64(_rS));}else{var _rX=hs_int64ToInt(_rS);return new F(function(){return _rP(_rX);});}}},_rY=new T(function(){var _rZ=newByteArr(256),_s0=_rZ,_=_s0["v"]["i8"][0]=8,_s1=function(_s2,_s3,_s4,_){while(1){if(_s4>=256){if(_s2>=256){return E(_);}else{var _s5=imul(2,_s2)|0,_s6=_s3+1|0,_s7=_s2;_s2=_s5;_s3=_s6;_s4=_s7;continue;}}else{var _=_s0["v"]["i8"][_s4]=_s3,_s7=_s4+_s2|0;_s4=_s7;continue;}}},_=B(_s1(2,0,1,_));return _s0;}),_s8=function(_s9,_sa){var _sb=hs_int64ToInt(_s9),_sc=E(_rY),_sd=_sc["v"]["i8"][(255&_sb>>>0)>>>0&4294967295];if(_sa>_sd){if(_sd>=8){var _se=hs_uncheckedIShiftRA64(_s9,8),_sf=function(_sg,_sh){while(1){var _si=B((function(_sj,_sk){var _sl=hs_int64ToInt(_sj),_sm=_sc["v"]["i8"][(255&_sl>>>0)>>>0&4294967295];if(_sk>_sm){if(_sm>=8){var _sn=hs_uncheckedIShiftRA64(_sj,8),_so=_sk-8|0;_sg=_sn;_sh=_so;return __continue;}else{return new T2(0,new T(function(){var _sp=hs_uncheckedIShiftRA64(_sj,_sm);return B(_rR(_sp));}),_sk-_sm|0);}}else{return new T2(0,new T(function(){var _sq=hs_uncheckedIShiftRA64(_sj,_sk);return B(_rR(_sq));}),0);}})(_sg,_sh));if(_si!=__continue){return _si;}}};return new F(function(){return _sf(_se,_sa-8|0);});}else{return new T2(0,new T(function(){var _sr=hs_uncheckedIShiftRA64(_s9,_sd);return B(_rR(_sr));}),_sa-_sd|0);}}else{return new T2(0,new T(function(){var _ss=hs_uncheckedIShiftRA64(_s9,_sa);return B(_rR(_ss));}),0);}},_st=function(_su){var _sv=hs_intToInt64(_su);return E(_sv);},_sw=function(_sx){var _sy=E(_sx);if(!_sy._){return new F(function(){return _st(_sy.a);});}else{return new F(function(){return I_toInt64(_sy.a);});}},_sz=function(_sA){return I_toInt(_sA)>>>0;},_sB=function(_sC){var _sD=E(_sC);if(!_sD._){return _sD.a>>>0;}else{return new F(function(){return _sz(_sD.a);});}},_sE=function(_sF){var _sG=B(_rM(_sF)),_sH=_sG.a,_sI=_sG.b;if(_sI<0){var _sJ=function(_sK){if(!_sK){return new T2(0,E(_sH),B(_52(_3k, -_sI)));}else{var _sL=B(_s8(B(_sw(_sH)), -_sI));return new T2(0,E(_sL.a),B(_52(_3k,_sL.b)));}};if(!((B(_sB(_sH))&1)>>>0)){return new F(function(){return _sJ(1);});}else{return new F(function(){return _sJ(0);});}}else{return new T2(0,B(_52(_sH,_sI)),_3k);}},_sM=function(_sN){var _sO=B(_sE(E(_sN)));return new T2(0,E(_sO.a),E(_sO.b));},_sP=new T3(0,_ji,_kn,_sM),_sQ=function(_sR){return E(E(_sR).a);},_sS=function(_sT){return E(E(_sT).a);},_sU=function(_sV,_sW){if(_sV<=_sW){var _sX=function(_sY){return new T2(1,_sY,new T(function(){if(_sY!=_sW){return B(_sX(_sY+1|0));}else{return __Z;}}));};return new F(function(){return _sX(_sV);});}else{return __Z;}},_sZ=function(_t0){return new F(function(){return _sU(E(_t0),2147483647);});},_t1=function(_t2,_t3,_t4){if(_t4<=_t3){var _t5=new T(function(){var _t6=_t3-_t2|0,_t7=function(_t8){return (_t8>=(_t4-_t6|0))?new T2(1,_t8,new T(function(){return B(_t7(_t8+_t6|0));})):new T2(1,_t8,_w);};return B(_t7(_t3));});return new T2(1,_t2,_t5);}else{return (_t4<=_t2)?new T2(1,_t2,_w):__Z;}},_t9=function(_ta,_tb,_tc){if(_tc>=_tb){var _td=new T(function(){var _te=_tb-_ta|0,_tf=function(_tg){return (_tg<=(_tc-_te|0))?new T2(1,_tg,new T(function(){return B(_tf(_tg+_te|0));})):new T2(1,_tg,_w);};return B(_tf(_tb));});return new T2(1,_ta,_td);}else{return (_tc>=_ta)?new T2(1,_ta,_w):__Z;}},_th=function(_ti,_tj){if(_tj<_ti){return new F(function(){return _t1(_ti,_tj,-2147483648);});}else{return new F(function(){return _t9(_ti,_tj,2147483647);});}},_tk=function(_tl,_tm){return new F(function(){return _th(E(_tl),E(_tm));});},_tn=function(_to,_tp,_tq){if(_tp<_to){return new F(function(){return _t1(_to,_tp,_tq);});}else{return new F(function(){return _t9(_to,_tp,_tq);});}},_tr=function(_ts,_tt,_tu){return new F(function(){return _tn(E(_ts),E(_tt),E(_tu));});},_tv=function(_tw,_tx){return new F(function(){return _sU(E(_tw),E(_tx));});},_ty=function(_tz){return E(_tz);},_tA=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_tB=new T(function(){return B(err(_tA));}),_tC=function(_tD){var _tE=E(_tD);return (_tE==(-2147483648))?E(_tB):_tE-1|0;},_tF=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_tG=new T(function(){return B(err(_tF));}),_tH=function(_tI){var _tJ=E(_tI);return (_tJ==2147483647)?E(_tG):_tJ+1|0;},_tK={_:0,a:_tH,b:_tC,c:_ty,d:_ty,e:_sZ,f:_tk,g:_tv,h:_tr},_tL=function(_tM,_tN){if(_tM<=0){if(_tM>=0){return new F(function(){return quot(_tM,_tN);});}else{if(_tN<=0){return new F(function(){return quot(_tM,_tN);});}else{return quot(_tM+1|0,_tN)-1|0;}}}else{if(_tN>=0){if(_tM>=0){return new F(function(){return quot(_tM,_tN);});}else{if(_tN<=0){return new F(function(){return quot(_tM,_tN);});}else{return quot(_tM+1|0,_tN)-1|0;}}}else{return quot(_tM-1|0,_tN)-1|0;}}},_tO=0,_tP=new T(function(){return B(_4p(_tO));}),_tQ=new T(function(){return die(_tP);}),_tR=function(_tS,_tT){var _tU=E(_tT);switch(_tU){case -1:var _tV=E(_tS);if(_tV==(-2147483648)){return E(_tQ);}else{return new F(function(){return _tL(_tV,-1);});}break;case 0:return E(_4t);default:return new F(function(){return _tL(_tS,_tU);});}},_tW=function(_tX,_tY){return new F(function(){return _tR(E(_tX),E(_tY));});},_tZ=0,_u0=new T2(0,_tQ,_tZ),_u1=function(_u2,_u3){var _u4=E(_u2),_u5=E(_u3);switch(_u5){case -1:var _u6=E(_u4);if(_u6==(-2147483648)){return E(_u0);}else{if(_u6<=0){if(_u6>=0){var _u7=quotRemI(_u6,-1);return new T2(0,_u7.a,_u7.b);}else{var _u8=quotRemI(_u6,-1);return new T2(0,_u8.a,_u8.b);}}else{var _u9=quotRemI(_u6-1|0,-1);return new T2(0,_u9.a-1|0,(_u9.b+(-1)|0)+1|0);}}break;case 0:return E(_4t);default:if(_u4<=0){if(_u4>=0){var _ua=quotRemI(_u4,_u5);return new T2(0,_ua.a,_ua.b);}else{if(_u5<=0){var _ub=quotRemI(_u4,_u5);return new T2(0,_ub.a,_ub.b);}else{var _uc=quotRemI(_u4+1|0,_u5);return new T2(0,_uc.a-1|0,(_uc.b+_u5|0)-1|0);}}}else{if(_u5>=0){if(_u4>=0){var _ud=quotRemI(_u4,_u5);return new T2(0,_ud.a,_ud.b);}else{if(_u5<=0){var _ue=quotRemI(_u4,_u5);return new T2(0,_ue.a,_ue.b);}else{var _uf=quotRemI(_u4+1|0,_u5);return new T2(0,_uf.a-1|0,(_uf.b+_u5|0)-1|0);}}}else{var _ug=quotRemI(_u4-1|0,_u5);return new T2(0,_ug.a-1|0,(_ug.b+_u5|0)+1|0);}}}},_uh=function(_ui,_uj){var _uk=_ui%_uj;if(_ui<=0){if(_ui>=0){return E(_uk);}else{if(_uj<=0){return E(_uk);}else{var _ul=E(_uk);return (_ul==0)?0:_ul+_uj|0;}}}else{if(_uj>=0){if(_ui>=0){return E(_uk);}else{if(_uj<=0){return E(_uk);}else{var _um=E(_uk);return (_um==0)?0:_um+_uj|0;}}}else{var _un=E(_uk);return (_un==0)?0:_un+_uj|0;}}},_uo=function(_up,_uq){var _ur=E(_uq);switch(_ur){case -1:return E(_tZ);case 0:return E(_4t);default:return new F(function(){return _uh(E(_up),_ur);});}},_us=function(_ut,_uu){var _uv=E(_ut),_uw=E(_uu);switch(_uw){case -1:var _ux=E(_uv);if(_ux==(-2147483648)){return E(_tQ);}else{return new F(function(){return quot(_ux,-1);});}break;case 0:return E(_4t);default:return new F(function(){return quot(_uv,_uw);});}},_uy=function(_uz,_uA){var _uB=E(_uz),_uC=E(_uA);switch(_uC){case -1:var _uD=E(_uB);if(_uD==(-2147483648)){return E(_u0);}else{var _uE=quotRemI(_uD,-1);return new T2(0,_uE.a,_uE.b);}break;case 0:return E(_4t);default:var _uF=quotRemI(_uB,_uC);return new T2(0,_uF.a,_uF.b);}},_uG=function(_uH,_uI){var _uJ=E(_uI);switch(_uJ){case -1:return E(_tZ);case 0:return E(_4t);default:return E(_uH)%_uJ;}},_uK=function(_uL){return new F(function(){return _rP(E(_uL));});},_uM=function(_uN){return new T2(0,E(B(_rP(E(_uN)))),E(_nB));},_uO=function(_uP,_uQ){return imul(E(_uP),E(_uQ))|0;},_uR=function(_uS,_uT){return E(_uS)+E(_uT)|0;},_uU=function(_uV,_uW){return E(_uV)-E(_uW)|0;},_uX=function(_uY){var _uZ=E(_uY);return (_uZ<0)? -_uZ:E(_uZ);},_v0=function(_v1){return new F(function(){return _4G(_v1);});},_v2=function(_v3){return  -E(_v3);},_v4=-1,_v5=0,_v6=1,_v7=function(_v8){var _v9=E(_v8);return (_v9>=0)?(E(_v9)==0)?E(_v5):E(_v6):E(_v4);},_va={_:0,a:_uR,b:_uU,c:_uO,d:_v2,e:_uX,f:_v7,g:_v0},_vb=function(_vc,_vd){return E(_vc)==E(_vd);},_ve=function(_vf,_vg){return E(_vf)!=E(_vg);},_vh=new T2(0,_vb,_ve),_vi=function(_vj,_vk){var _vl=E(_vj),_vm=E(_vk);return (_vl>_vm)?E(_vl):E(_vm);},_vn=function(_vo,_vp){var _vq=E(_vo),_vr=E(_vp);return (_vq>_vr)?E(_vr):E(_vq);},_vs=function(_vt,_vu){return (_vt>=_vu)?(_vt!=_vu)?2:1:0;},_vv=function(_vw,_vx){return new F(function(){return _vs(E(_vw),E(_vx));});},_vy=function(_vz,_vA){return E(_vz)>=E(_vA);},_vB=function(_vC,_vD){return E(_vC)>E(_vD);},_vE=function(_vF,_vG){return E(_vF)<=E(_vG);},_vH=function(_vI,_vJ){return E(_vI)<E(_vJ);},_vK={_:0,a:_vh,b:_vv,c:_vH,d:_vE,e:_vB,f:_vy,g:_vi,h:_vn},_vL=new T3(0,_va,_vK,_uM),_vM={_:0,a:_vL,b:_tK,c:_us,d:_uG,e:_tW,f:_uo,g:_uy,h:_u1,i:_uK},_vN=new T1(0,2),_vO=function(_vP,_vQ){while(1){var _vR=E(_vP);if(!_vR._){var _vS=_vR.a,_vT=E(_vQ);if(!_vT._){var _vU=_vT.a;if(!(imul(_vS,_vU)|0)){return new T1(0,imul(_vS,_vU)|0);}else{_vP=new T1(1,I_fromInt(_vS));_vQ=new T1(1,I_fromInt(_vU));continue;}}else{_vP=new T1(1,I_fromInt(_vS));_vQ=_vT;continue;}}else{var _vV=E(_vQ);if(!_vV._){_vP=_vR;_vQ=new T1(1,I_fromInt(_vV.a));continue;}else{return new T1(1,I_mul(_vR.a,_vV.a));}}}},_vW=function(_vX,_vY,_vZ){while(1){if(!(_vY%2)){var _w0=B(_vO(_vX,_vX)),_w1=quot(_vY,2);_vX=_w0;_vY=_w1;continue;}else{var _w2=E(_vY);if(_w2==1){return new F(function(){return _vO(_vX,_vZ);});}else{var _w0=B(_vO(_vX,_vX)),_w3=B(_vO(_vX,_vZ));_vX=_w0;_vY=quot(_w2-1|0,2);_vZ=_w3;continue;}}}},_w4=function(_w5,_w6){while(1){if(!(_w6%2)){var _w7=B(_vO(_w5,_w5)),_w8=quot(_w6,2);_w5=_w7;_w6=_w8;continue;}else{var _w9=E(_w6);if(_w9==1){return E(_w5);}else{return new F(function(){return _vW(B(_vO(_w5,_w5)),quot(_w9-1|0,2),_w5);});}}}},_wa=function(_wb){return E(E(_wb).b);},_wc=function(_wd){return E(E(_wd).c);},_we=new T1(0,0),_wf=function(_wg){return E(E(_wg).d);},_wh=function(_wi,_wj){var _wk=B(_sQ(_wi)),_wl=new T(function(){return B(_sS(_wk));}),_wm=new T(function(){return B(A3(_wf,_wi,_wj,new T(function(){return B(A2(_9Z,_wl,_nL));})));});return new F(function(){return A3(_mp,B(_mb(B(_wa(_wk)))),_wm,new T(function(){return B(A2(_9Z,_wl,_we));}));});},_wn=new T(function(){return B(unCStr("Negative exponent"));}),_wo=new T(function(){return B(err(_wn));}),_wp=function(_wq){return E(E(_wq).c);},_wr=function(_ws,_wt,_wu,_wv){var _ww=B(_sQ(_wt)),_wx=new T(function(){return B(_sS(_ww));}),_wy=B(_wa(_ww));if(!B(A3(_wc,_wy,_wv,new T(function(){return B(A2(_9Z,_wx,_we));})))){if(!B(A3(_mp,B(_mb(_wy)),_wv,new T(function(){return B(A2(_9Z,_wx,_we));})))){var _wz=new T(function(){return B(A2(_9Z,_wx,_nL));}),_wA=new T(function(){return B(A2(_9Z,_wx,_nB));}),_wB=B(_mb(_wy)),_wC=function(_wD,_wE,_wF){while(1){var _wG=B((function(_wH,_wI,_wJ){if(!B(_wh(_wt,_wI))){if(!B(A3(_mp,_wB,_wI,_wA))){var _wK=new T(function(){return B(A3(_wp,_wt,new T(function(){return B(A3(_8w,_wx,_wI,_wA));}),_wz));});_wD=new T(function(){return B(A3(_8u,_ws,_wH,_wH));});_wE=_wK;_wF=new T(function(){return B(A3(_8u,_ws,_wH,_wJ));});return __continue;}else{return new F(function(){return A3(_8u,_ws,_wH,_wJ);});}}else{var _wL=_wJ;_wD=new T(function(){return B(A3(_8u,_ws,_wH,_wH));});_wE=new T(function(){return B(A3(_wp,_wt,_wI,_wz));});_wF=_wL;return __continue;}})(_wD,_wE,_wF));if(_wG!=__continue){return _wG;}}},_wM=function(_wN,_wO){while(1){var _wP=B((function(_wQ,_wR){if(!B(_wh(_wt,_wR))){if(!B(A3(_mp,_wB,_wR,_wA))){var _wS=new T(function(){return B(A3(_wp,_wt,new T(function(){return B(A3(_8w,_wx,_wR,_wA));}),_wz));});return new F(function(){return _wC(new T(function(){return B(A3(_8u,_ws,_wQ,_wQ));}),_wS,_wQ);});}else{return E(_wQ);}}else{_wN=new T(function(){return B(A3(_8u,_ws,_wQ,_wQ));});_wO=new T(function(){return B(A3(_wp,_wt,_wR,_wz));});return __continue;}})(_wN,_wO));if(_wP!=__continue){return _wP;}}};return new F(function(){return _wM(_wu,_wv);});}else{return new F(function(){return A2(_9Z,_ws,_nB);});}}else{return E(_wo);}},_wT=new T(function(){return B(err(_wn));}),_wU=function(_wV,_wW){var _wX=B(_rM(_wW)),_wY=_wX.a,_wZ=_wX.b,_x0=new T(function(){return B(_sS(new T(function(){return B(_sQ(_wV));})));});if(_wZ<0){var _x1= -_wZ;if(_x1>=0){var _x2=E(_x1);if(!_x2){var _x3=E(_nB);}else{var _x3=B(_w4(_vN,_x2));}if(!B(_4y(_x3,_51))){var _x4=B(_4S(_wY,_x3));return new T2(0,new T(function(){return B(A2(_9Z,_x0,_x4.a));}),new T(function(){return B(_4u(_x4.b,_wZ));}));}else{return E(_4t);}}else{return E(_wT);}}else{var _x5=new T(function(){var _x6=new T(function(){return B(_wr(_x0,_vM,new T(function(){return B(A2(_9Z,_x0,_vN));}),_wZ));});return B(A3(_8u,_x0,new T(function(){return B(A2(_9Z,_x0,_wY));}),_x6));});return new T2(0,_x5,_7I);}},_x7=function(_x8,_x9){var _xa=B(_wU(_x8,E(_x9))),_xb=_xa.a;if(E(_xa.b)<=0){return E(_xb);}else{var _xc=B(_sS(B(_sQ(_x8))));return new F(function(){return A3(_86,_xc,_xb,new T(function(){return B(A2(_9Z,_xc,_3k));}));});}},_xd=function(_xe,_xf){var _xg=B(_wU(_xe,E(_xf))),_xh=_xg.a;if(E(_xg.b)>=0){return E(_xh);}else{var _xi=B(_sS(B(_sQ(_xe))));return new F(function(){return A3(_8w,_xi,_xh,new T(function(){return B(A2(_9Z,_xi,_3k));}));});}},_xj=function(_xk,_xl){var _xm=B(_wU(_xk,E(_xl)));return new T2(0,_xm.a,_xm.b);},_xn=function(_xo,_xp){var _xq=B(_wU(_xo,_xp)),_xr=_xq.a,_xs=E(_xq.b),_xt=new T(function(){var _xu=B(_sS(B(_sQ(_xo))));if(_xs>=0){return B(A3(_86,_xu,_xr,new T(function(){return B(A2(_9Z,_xu,_3k));})));}else{return B(A3(_8w,_xu,_xr,new T(function(){return B(A2(_9Z,_xu,_3k));})));}}),_xv=function(_xw){var _xx=_xw-0.5;return (_xx>=0)?(E(_xx)==0)?(!B(_wh(_xo,_xr)))?E(_xt):E(_xr):E(_xt):E(_xr);},_xy=E(_xs);if(!_xy){return new F(function(){return _xv(0);});}else{if(_xy<=0){var _xz= -_xy-0.5;return (_xz>=0)?(E(_xz)==0)?(!B(_wh(_xo,_xr)))?E(_xt):E(_xr):E(_xt):E(_xr);}else{return new F(function(){return _xv(_xy);});}}},_xA=function(_xB,_xC){return new F(function(){return _xn(_xB,E(_xC));});},_xD=function(_xE,_xF){return E(B(_wU(_xE,E(_xF))).a);},_xG={_:0,a:_sP,b:_jm,c:_xj,d:_xD,e:_xA,f:_x7,g:_xd},_xH=new T1(0,1),_xI=function(_xJ,_xK){var _xL=E(_xJ);return new T2(0,_xL,new T(function(){var _xM=B(_xI(B(_4J(_xL,_xK)),_xK));return new T2(1,_xM.a,_xM.b);}));},_xN=function(_xO){var _xP=B(_xI(_xO,_xH));return new T2(1,_xP.a,_xP.b);},_xQ=function(_xR,_xS){var _xT=B(_xI(_xR,new T(function(){return B(_6W(_xS,_xR));})));return new T2(1,_xT.a,_xT.b);},_xU=new T1(0,0),_xV=function(_xW,_xX){var _xY=E(_xW);if(!_xY._){var _xZ=_xY.a,_y0=E(_xX);return (_y0._==0)?_xZ>=_y0.a:I_compareInt(_y0.a,_xZ)<=0;}else{var _y1=_xY.a,_y2=E(_xX);return (_y2._==0)?I_compareInt(_y1,_y2.a)>=0:I_compare(_y1,_y2.a)>=0;}},_y3=function(_y4,_y5,_y6){if(!B(_xV(_y5,_xU))){var _y7=function(_y8){return (!B(_S(_y8,_y6)))?new T2(1,_y8,new T(function(){return B(_y7(B(_4J(_y8,_y5))));})):__Z;};return new F(function(){return _y7(_y4);});}else{var _y9=function(_ya){return (!B(_5c(_ya,_y6)))?new T2(1,_ya,new T(function(){return B(_y9(B(_4J(_ya,_y5))));})):__Z;};return new F(function(){return _y9(_y4);});}},_yb=function(_yc,_yd,_ye){return new F(function(){return _y3(_yc,B(_6W(_yd,_yc)),_ye);});},_yf=function(_yg,_yh){return new F(function(){return _y3(_yg,_xH,_yh);});},_yi=function(_yj){return new F(function(){return _4G(_yj);});},_yk=function(_yl){return new F(function(){return _6W(_yl,_xH);});},_ym=function(_yn){return new F(function(){return _4J(_yn,_xH);});},_yo=function(_yp){return new F(function(){return _rP(E(_yp));});},_yq={_:0,a:_ym,b:_yk,c:_yo,d:_yi,e:_xN,f:_xQ,g:_yf,h:_yb},_yr=function(_ys,_yt){while(1){var _yu=E(_ys);if(!_yu._){var _yv=E(_yu.a);if(_yv==(-2147483648)){_ys=new T1(1,I_fromInt(-2147483648));continue;}else{var _yw=E(_yt);if(!_yw._){return new T1(0,B(_tL(_yv,_yw.a)));}else{_ys=new T1(1,I_fromInt(_yv));_yt=_yw;continue;}}}else{var _yx=_yu.a,_yy=E(_yt);return (_yy._==0)?new T1(1,I_div(_yx,I_fromInt(_yy.a))):new T1(1,I_div(_yx,_yy.a));}}},_yz=function(_yA,_yB){if(!B(_4y(_yB,_we))){return new F(function(){return _yr(_yA,_yB);});}else{return E(_4t);}},_yC=function(_yD,_yE){while(1){var _yF=E(_yD);if(!_yF._){var _yG=E(_yF.a);if(_yG==(-2147483648)){_yD=new T1(1,I_fromInt(-2147483648));continue;}else{var _yH=E(_yE);if(!_yH._){var _yI=_yH.a;return new T2(0,new T1(0,B(_tL(_yG,_yI))),new T1(0,B(_uh(_yG,_yI))));}else{_yD=new T1(1,I_fromInt(_yG));_yE=_yH;continue;}}}else{var _yJ=E(_yE);if(!_yJ._){_yD=_yF;_yE=new T1(1,I_fromInt(_yJ.a));continue;}else{var _yK=I_divMod(_yF.a,_yJ.a);return new T2(0,new T1(1,_yK.a),new T1(1,_yK.b));}}}},_yL=function(_yM,_yN){if(!B(_4y(_yN,_we))){var _yO=B(_yC(_yM,_yN));return new T2(0,_yO.a,_yO.b);}else{return E(_4t);}},_yP=function(_yQ,_yR){while(1){var _yS=E(_yQ);if(!_yS._){var _yT=E(_yS.a);if(_yT==(-2147483648)){_yQ=new T1(1,I_fromInt(-2147483648));continue;}else{var _yU=E(_yR);if(!_yU._){return new T1(0,B(_uh(_yT,_yU.a)));}else{_yQ=new T1(1,I_fromInt(_yT));_yR=_yU;continue;}}}else{var _yV=_yS.a,_yW=E(_yR);return (_yW._==0)?new T1(1,I_mod(_yV,I_fromInt(_yW.a))):new T1(1,I_mod(_yV,_yW.a));}}},_yX=function(_yY,_yZ){if(!B(_4y(_yZ,_we))){return new F(function(){return _yP(_yY,_yZ);});}else{return E(_4t);}},_z0=function(_z1,_z2){while(1){var _z3=E(_z1);if(!_z3._){var _z4=E(_z3.a);if(_z4==(-2147483648)){_z1=new T1(1,I_fromInt(-2147483648));continue;}else{var _z5=E(_z2);if(!_z5._){return new T1(0,quot(_z4,_z5.a));}else{_z1=new T1(1,I_fromInt(_z4));_z2=_z5;continue;}}}else{var _z6=_z3.a,_z7=E(_z2);return (_z7._==0)?new T1(0,I_toInt(I_quot(_z6,I_fromInt(_z7.a)))):new T1(1,I_quot(_z6,_z7.a));}}},_z8=function(_z9,_za){if(!B(_4y(_za,_we))){return new F(function(){return _z0(_z9,_za);});}else{return E(_4t);}},_zb=function(_zc,_zd){if(!B(_4y(_zd,_we))){var _ze=B(_4S(_zc,_zd));return new T2(0,_ze.a,_ze.b);}else{return E(_4t);}},_zf=function(_zg,_zh){while(1){var _zi=E(_zg);if(!_zi._){var _zj=E(_zi.a);if(_zj==(-2147483648)){_zg=new T1(1,I_fromInt(-2147483648));continue;}else{var _zk=E(_zh);if(!_zk._){return new T1(0,_zj%_zk.a);}else{_zg=new T1(1,I_fromInt(_zj));_zh=_zk;continue;}}}else{var _zl=_zi.a,_zm=E(_zh);return (_zm._==0)?new T1(1,I_rem(_zl,I_fromInt(_zm.a))):new T1(1,I_rem(_zl,_zm.a));}}},_zn=function(_zo,_zp){if(!B(_4y(_zp,_we))){return new F(function(){return _zf(_zo,_zp);});}else{return E(_4t);}},_zq=function(_zr){return E(_zr);},_zs=function(_zt){return E(_zt);},_zu=function(_zv){var _zw=E(_zv);if(!_zw._){var _zx=E(_zw.a);return (_zx==(-2147483648))?E(_7A):(_zx<0)?new T1(0, -_zx):E(_zw);}else{var _zy=_zw.a;return (I_compareInt(_zy,0)>=0)?E(_zw):new T1(1,I_negate(_zy));}},_zz=new T1(0,0),_zA=new T1(0,-1),_zB=function(_zC){var _zD=E(_zC);if(!_zD._){var _zE=_zD.a;return (_zE>=0)?(E(_zE)==0)?E(_zz):E(_5k):E(_zA);}else{var _zF=I_compareInt(_zD.a,0);return (_zF<=0)?(E(_zF)==0)?E(_zz):E(_zA):E(_5k);}},_zG={_:0,a:_4J,b:_6W,c:_vO,d:_7B,e:_zu,f:_zB,g:_zs},_zH=function(_zI,_zJ){var _zK=E(_zI);if(!_zK._){var _zL=_zK.a,_zM=E(_zJ);return (_zM._==0)?_zL!=_zM.a:(I_compareInt(_zM.a,_zL)==0)?false:true;}else{var _zN=_zK.a,_zO=E(_zJ);return (_zO._==0)?(I_compareInt(_zN,_zO.a)==0)?false:true:(I_compare(_zN,_zO.a)==0)?false:true;}},_zP=new T2(0,_4y,_zH),_zQ=function(_zR,_zS){return (!B(_6H(_zR,_zS)))?E(_zR):E(_zS);},_zT=function(_zU,_zV){return (!B(_6H(_zU,_zV)))?E(_zV):E(_zU);},_zW={_:0,a:_zP,b:_3l,c:_S,d:_6H,e:_5c,f:_xV,g:_zQ,h:_zT},_zX=function(_zY){return new T2(0,E(_zY),E(_nB));},_zZ=new T3(0,_zG,_zW,_zX),_A0={_:0,a:_zZ,b:_yq,c:_z8,d:_zn,e:_yz,f:_yX,g:_zb,h:_yL,i:_zq},_A1=function(_A2){return E(E(_A2).b);},_A3=function(_A4){return E(E(_A4).g);},_A5=new T1(0,1),_A6=function(_A7,_A8,_A9){var _Aa=B(_A1(_A7)),_Ab=B(_8s(_Aa)),_Ac=new T(function(){var _Ad=new T(function(){var _Ae=new T(function(){var _Af=new T(function(){return B(A3(_A3,_A7,_A0,new T(function(){return B(A3(_a9,_Aa,_A8,_A9));})));});return B(A2(_9Z,_Ab,_Af));}),_Ag=new T(function(){return B(A2(_88,_Ab,new T(function(){return B(A2(_9Z,_Ab,_A5));})));});return B(A3(_8u,_Ab,_Ag,_Ae));});return B(A3(_8u,_Ab,_Ad,_A9));});return new F(function(){return A3(_86,_Ab,_A8,_Ac);});},_Ah=1.5707963267948966,_Ai=function(_Aj){return 0.2/Math.cos(B(_A6(_xG,_Aj,_Ah))-0.7853981633974483);},_Ak=0,_Al=new T(function(){var _Am=B(_qs(_Ai,1.2,_Ak,_Ak,_rL,_Ak,_Ak,_Ak,_Ak,_Ak,_rL,_rL,_rL));return {_:0,a:E(_Am.a),b:E(_Am.b),c:E(_Am.c),d:E(_Am.d),e:E(_Am.e),f:E(_Am.f),g:E(_Am.g),h:_Am.h,i:_Am.i,j:_Am.j};}),_An=0,_Ao=0.3,_Ap=function(_Aq){return E(_Ao);},_Ar=new T(function(){var _As=B(_qs(_Ap,1.2,_rL,_Ak,_rL,_Ak,_Ak,_Ak,_Ak,_Ak,_rL,_rL,_rL));return {_:0,a:E(_As.a),b:E(_As.b),c:E(_As.c),d:E(_As.d),e:E(_As.e),f:E(_As.f),g:E(_As.g),h:_As.h,i:_As.i,j:_As.j};}),_At=new T(function(){var _Au=B(_qs(_Ap,1.2,_rL,_rL,_Ak,_Ak,_Ak,_Ak,_Ak,_Ak,_rL,_rL,_rL));return {_:0,a:E(_Au.a),b:E(_Au.b),c:E(_Au.c),d:E(_Au.d),e:E(_Au.e),f:E(_Au.f),g:E(_Au.g),h:_Au.h,i:_Au.i,j:_Au.j};}),_Av=2,_Aw=function(_Ax){return 0.3/Math.cos(B(_A6(_xG,_Ax,_Ah))-0.7853981633974483);},_Ay=new T(function(){var _Az=B(_qs(_Aw,1.2,_Av,_rL,_rL,_Ak,_Ak,_Ak,_Ak,_Ak,_rL,_rL,_rL));return {_:0,a:E(_Az.a),b:E(_Az.b),c:E(_Az.c),d:E(_Az.d),e:E(_Az.e),f:E(_Az.f),g:E(_Az.g),h:_Az.h,i:_Az.i,j:_Az.j};}),_AA=new T2(1,_Ay,_w),_AB=new T2(1,_At,_AA),_AC=new T2(1,_Ar,_AB),_AD=new T2(1,_Al,_AC),_AE=new T(function(){return B(unCStr("Negative range size"));}),_AF=new T(function(){return B(err(_AE));}),_AG=function(_){var _AH=B(_ic(_AD,0))-1|0,_AI=function(_AJ){if(_AJ>=0){var _AK=newArr(_AJ,_ii),_AL=_AK,_AM=E(_AJ);if(!_AM){return new T4(0,E(_An),E(_AH),0,_AL);}else{var _AN=function(_AO,_AP,_){while(1){var _AQ=E(_AO);if(!_AQ._){return E(_);}else{var _=_AL[_AP]=_AQ.a;if(_AP!=(_AM-1|0)){var _AR=_AP+1|0;_AO=_AQ.b;_AP=_AR;continue;}else{return E(_);}}}},_=B((function(_AS,_AT,_AU,_){var _=_AL[_AU]=_AS;if(_AU!=(_AM-1|0)){return new F(function(){return _AN(_AT,_AU+1|0,_);});}else{return E(_);}})(_Al,_AC,0,_));return new T4(0,E(_An),E(_AH),_AM,_AL);}}else{return E(_AF);}};if(0>_AH){return new F(function(){return _AI(0);});}else{return new F(function(){return _AI(_AH+1|0);});}},_AV=function(_AW){var _AX=B(A1(_AW,_));return E(_AX);},_AY=new T(function(){return B(_AV(_AG));}),_AZ="enclose",_B0="outline",_B1="polygon",_B2="z",_B3="y",_B4="x",_B5=function(_B6){return new F(function(){return _kA(new T2(1,new T2(0,_B4,new T(function(){return E(E(E(E(_B6).d).a).a);})),new T2(1,new T2(0,_B3,new T(function(){return E(E(E(E(_B6).d).a).b);})),new T2(1,new T2(0,_B2,new T(function(){return E(E(E(E(_B6).d).a).c);})),new T2(1,new T2(0,_B1,new T(function(){return E(_B6).h;})),new T2(1,new T2(0,_B0,new T(function(){return E(_B6).i;})),new T2(1,new T2(0,_AZ,new T(function(){return E(_B6).j;})),_w)))))));});},_B7=new T(function(){return B(unCStr("(^?!): empty Fold"));}),_B8=new T(function(){return B(err(_B7));}),_B9=new T(function(){return eval("__strict(drawObjects)");}),_Ba=new T(function(){return eval("__strict(draw)");}),_Bb=function(_Bc,_Bd){var _Be=jsShowI(_Bc);return new F(function(){return _n(fromJSStr(_Be),_Bd);});},_Bf=function(_Bg,_Bh,_Bi){if(_Bh>=0){return new F(function(){return _Bb(_Bh,_Bi);});}else{if(_Bg<=6){return new F(function(){return _Bb(_Bh,_Bi);});}else{return new T2(1,_11,new T(function(){var _Bj=jsShowI(_Bh);return B(_n(fromJSStr(_Bj),new T2(1,_10,_Bi)));}));}}},_Bk=new T(function(){return B(unCStr(")"));}),_Bl=function(_Bm,_Bn){var _Bo=new T(function(){var _Bp=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Bf(0,_Bm,_w)),_Bk));})));},1);return B(_n(B(_Bf(0,_Bn,_w)),_Bp));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Bo)));});},_Bq=new T2(1,_kz,_w),_Br=function(_Bs){return E(_Bs);},_Bt=function(_Bu){return E(_Bu);},_Bv=function(_Bw,_Bx){return E(_Bx);},_By=function(_Bz,_BA){return E(_Bz);},_BB=function(_BC){return E(_BC);},_BD=new T2(0,_BB,_By),_BE=function(_BF,_BG){return E(_BF);},_BH=new T5(0,_BD,_Bt,_Br,_Bv,_BE),_BI="flipped2",_BJ="flipped1",_BK="c1y",_BL="c1x",_BM="w2z",_BN="w2y",_BO="w2x",_BP="w1z",_BQ="w1y",_BR="w1x",_BS="d2z",_BT="d2y",_BU="d2x",_BV="d1z",_BW="d1y",_BX="d1x",_BY="c2y",_BZ="c2x",_C0=function(_C1,_){var _C2=__get(_C1,E(_BR)),_C3=__get(_C1,E(_BQ)),_C4=__get(_C1,E(_BP)),_C5=__get(_C1,E(_BO)),_C6=__get(_C1,E(_BN)),_C7=__get(_C1,E(_BM)),_C8=__get(_C1,E(_BL)),_C9=__get(_C1,E(_BK)),_Ca=__get(_C1,E(_BZ)),_Cb=__get(_C1,E(_BY)),_Cc=__get(_C1,E(_BX)),_Cd=__get(_C1,E(_BW)),_Ce=__get(_C1,E(_BV)),_Cf=__get(_C1,E(_BU)),_Cg=__get(_C1,E(_BT)),_Ch=__get(_C1,E(_BS)),_Ci=__get(_C1,E(_BJ)),_Cj=__get(_C1,E(_BI));return {_:0,a:E(new T3(0,E(_C2),E(_C3),E(_C4))),b:E(new T3(0,E(_C5),E(_C6),E(_C7))),c:E(new T2(0,E(_C8),E(_C9))),d:E(new T2(0,E(_Ca),E(_Cb))),e:E(new T3(0,E(_Cc),E(_Cd),E(_Ce))),f:E(new T3(0,E(_Cf),E(_Cg),E(_Ch))),g:E(_Ci),h:E(_Cj)};},_Ck=function(_Cl,_){var _Cm=E(_Cl);if(!_Cm._){return _w;}else{var _Cn=B(_C0(E(_Cm.a),_)),_Co=B(_Ck(_Cm.b,_));return new T2(1,_Cn,_Co);}},_Cp=function(_Cq){var _Cr=E(_Cq);return (E(_Cr.b)-E(_Cr.a)|0)+1|0;},_Cs=function(_Ct,_Cu){var _Cv=E(_Ct),_Cw=E(_Cu);return (E(_Cv.a)>_Cw)?false:_Cw<=E(_Cv.b);},_Cx=function(_Cy){return new F(function(){return _Bf(0,E(_Cy),_w);});},_Cz=function(_CA,_CB,_CC){return new F(function(){return _Bf(E(_CA),E(_CB),_CC);});},_CD=function(_CE,_CF){return new F(function(){return _Bf(0,E(_CE),_CF);});},_CG=function(_CH,_CI){return new F(function(){return _49(_CD,_CH,_CI);});},_CJ=new T3(0,_Cz,_Cx,_CG),_CK=0,_CL=function(_CM,_CN,_CO){return new F(function(){return A1(_CM,new T2(1,_46,new T(function(){return B(A1(_CN,_CO));})));});},_CP=new T(function(){return B(unCStr("foldr1"));}),_CQ=new T(function(){return B(_n0(_CP));}),_CR=function(_CS,_CT){var _CU=E(_CT);if(!_CU._){return E(_CQ);}else{var _CV=_CU.a,_CW=E(_CU.b);if(!_CW._){return E(_CV);}else{return new F(function(){return A2(_CS,_CV,new T(function(){return B(_CR(_CS,_CW));}));});}}},_CX=new T(function(){return B(unCStr(" out of range "));}),_CY=new T(function(){return B(unCStr("}.index: Index "));}),_CZ=new T(function(){return B(unCStr("Ix{"));}),_D0=new T2(1,_10,_w),_D1=new T2(1,_10,_D0),_D2=0,_D3=function(_D4){return E(E(_D4).a);},_D5=function(_D6,_D7,_D8,_D9,_Da){var _Db=new T(function(){var _Dc=new T(function(){var _Dd=new T(function(){var _De=new T(function(){var _Df=new T(function(){return B(A3(_CR,_CL,new T2(1,new T(function(){return B(A3(_D3,_D8,_D2,_D9));}),new T2(1,new T(function(){return B(A3(_D3,_D8,_D2,_Da));}),_w)),_D1));});return B(_n(_CX,new T2(1,_11,new T2(1,_11,_Df))));});return B(A(_D3,[_D8,_CK,_D7,new T2(1,_10,_De)]));});return B(_n(_CY,new T2(1,_11,_Dd)));},1);return B(_n(_D6,_Dc));},1);return new F(function(){return err(B(_n(_CZ,_Db)));});},_Dg=function(_Dh,_Di,_Dj,_Dk,_Dl){return new F(function(){return _D5(_Dh,_Di,_Dl,_Dj,_Dk);});},_Dm=function(_Dn,_Do,_Dp,_Dq){var _Dr=E(_Dp);return new F(function(){return _Dg(_Dn,_Do,_Dr.a,_Dr.b,_Dq);});},_Ds=function(_Dt,_Du,_Dv,_Dw){return new F(function(){return _Dm(_Dw,_Dv,_Du,_Dt);});},_Dx=new T(function(){return B(unCStr("Int"));}),_Dy=function(_Dz,_DA){return new F(function(){return _Ds(_CJ,_DA,_Dz,_Dx);});},_DB=function(_DC,_DD){var _DE=E(_DC),_DF=E(_DE.a),_DG=E(_DD);if(_DF>_DG){return new F(function(){return _Dy(_DG,_DE);});}else{if(_DG>E(_DE.b)){return new F(function(){return _Dy(_DG,_DE);});}else{return _DG-_DF|0;}}},_DH=function(_DI){var _DJ=E(_DI);return new F(function(){return _tv(_DJ.a,_DJ.b);});},_DK=function(_DL){var _DM=E(_DL),_DN=E(_DM.a),_DO=E(_DM.b);return (_DN>_DO)?E(_CK):(_DO-_DN|0)+1|0;},_DP=function(_DQ,_DR){return new F(function(){return _uU(_DR,E(_DQ).a);});},_DS={_:0,a:_vK,b:_DH,c:_DB,d:_DP,e:_Cs,f:_DK,g:_Cp},_DT=function(_DU,_DV,_){while(1){var _DW=B((function(_DX,_DY,_){var _DZ=E(_DX);if(!_DZ._){return new T2(0,_kz,_DY);}else{var _E0=B(A2(_DZ.a,_DY,_));_DU=_DZ.b;_DV=new T(function(){return E(E(_E0).b);});return __continue;}})(_DU,_DV,_));if(_DW!=__continue){return _DW;}}},_E1=function(_E2,_E3){return new T2(1,_E2,_E3);},_E4=function(_E5,_E6){var _E7=E(_E6);return new T2(0,_E7.a,_E7.b);},_E8=function(_E9){return E(E(_E9).f);},_Ea=function(_Eb,_Ec,_Ed){var _Ee=E(_Ec),_Ef=_Ee.a,_Eg=_Ee.b,_Eh=function(_){var _Ei=B(A2(_E8,_Eb,_Ee));if(_Ei>=0){var _Ej=newArr(_Ei,_ii),_Ek=_Ej,_El=E(_Ei);if(!_El){return new T(function(){return new T4(0,E(_Ef),E(_Eg),0,_Ek);});}else{var _Em=function(_En,_Eo,_){while(1){var _Ep=E(_En);if(!_Ep._){return E(_);}else{var _=_Ek[_Eo]=_Ep.a;if(_Eo!=(_El-1|0)){var _Eq=_Eo+1|0;_En=_Ep.b;_Eo=_Eq;continue;}else{return E(_);}}}},_=B(_Em(_Ed,0,_));return new T(function(){return new T4(0,E(_Ef),E(_Eg),_El,_Ek);});}}else{return E(_AF);}};return new F(function(){return _AV(_Eh);});},_Er=function(_Es,_Et,_Eu,_Ev){var _Ew=new T(function(){var _Ex=E(_Ev),_Ey=_Ex.c-1|0,_Ez=new T(function(){return B(A2(_dU,_Et,_w));});if(0<=_Ey){var _EA=new T(function(){return B(_a5(_Et));}),_EB=function(_EC){var _ED=new T(function(){var _EE=new T(function(){return B(A1(_Eu,new T(function(){return E(_Ex.d[_EC]);})));});return B(A3(_ad,_EA,_E1,_EE));});return new F(function(){return A3(_ab,_Et,_ED,new T(function(){if(_EC!=_Ey){return B(_EB(_EC+1|0));}else{return E(_Ez);}}));});};return B(_EB(0));}else{return E(_Ez);}}),_EF=new T(function(){return B(_E4(_Es,_Ev));});return new F(function(){return A3(_ad,B(_a5(_Et)),function(_EG){return new F(function(){return _Ea(_Es,_EF,_EG);});},_Ew);});},_EH=function(_EI,_EJ,_EK,_EL,_EM,_EN,_EO,_EP,_EQ){var _ER=B(_8u(_EI));return new T2(0,new T3(0,E(B(A1(B(A1(_ER,_EJ)),_EN))),E(B(A1(B(A1(_ER,_EK)),_EO))),E(B(A1(B(A1(_ER,_EL)),_EP)))),B(A1(B(A1(_ER,_EM)),_EQ)));},_ES=function(_ET,_EU,_EV,_EW,_EX,_EY,_EZ,_F0,_F1){var _F2=B(_86(_ET));return new T2(0,new T3(0,E(B(A1(B(A1(_F2,_EU)),_EY))),E(B(A1(B(A1(_F2,_EV)),_EZ))),E(B(A1(B(A1(_F2,_EW)),_F0)))),B(A1(B(A1(_F2,_EX)),_F1)));},_F3=1.0e-2,_F4=function(_F5,_F6,_F7,_F8,_F9,_Fa,_Fb,_Fc,_Fd,_Fe,_Ff,_Fg,_Fh,_Fi,_Fj,_Fk,_Fl,_Fm){var _Fn=B(_EH(_ji,_Fc,_Fd,_Fe,_Ff,_F3,_F3,_F3,_F3)),_Fo=E(_Fn.a),_Fp=B(_ES(_ji,_F8,_F9,_Fa,_Fb,_Fo.a,_Fo.b,_Fo.c,_Fn.b)),_Fq=E(_Fp.a);return new F(function(){return _pI(_F5,_F6,_F7,_Fq.a,_Fq.b,_Fq.c,_Fp.b,_Fc,_Fd,_Fe,_Ff,_Fg,_Fh,_Fi,_Fj,_Fk,_Fl,_Fm);});},_Fr=function(_Fs){var _Ft=E(_Fs),_Fu=E(_Ft.d),_Fv=E(_Fu.a),_Fw=E(_Ft.e),_Fx=E(_Fw.a),_Fy=E(_Ft.f),_Fz=B(_F4(_Ft.a,_Ft.b,_Ft.c,_Fv.a,_Fv.b,_Fv.c,_Fu.b,_Fx.a,_Fx.b,_Fx.c,_Fw.b,_Fy.a,_Fy.b,_Fy.c,_Ft.g,_Ft.h,_Ft.i,_Ft.j));return {_:0,a:E(_Fz.a),b:E(_Fz.b),c:E(_Fz.c),d:E(_Fz.d),e:E(_Fz.e),f:E(_Fz.f),g:E(_Fz.g),h:_Fz.h,i:_Fz.i,j:_Fz.j};},_FA=function(_FB,_FC,_FD,_FE,_FF,_FG,_FH,_FI,_FJ){var _FK=B(_8s(B(_8q(_FB))));return new F(function(){return A3(_86,_FK,new T(function(){return B(_ld(_FB,_FC,_FD,_FE,_FG,_FH,_FI));}),new T(function(){return B(A3(_8u,_FK,_FF,_FJ));}));});},_FL=new T(function(){return B(unCStr("base"));}),_FM=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_FN=new T(function(){return B(unCStr("IOException"));}),_FO=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_FL,_FM,_FN),_FP=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_FO,_w,_w),_FQ=function(_FR){return E(_FP);},_FS=function(_FT){var _FU=E(_FT);return new F(function(){return _3G(B(_3E(_FU.a)),_FQ,_FU.b);});},_FV=new T(function(){return B(unCStr(": "));}),_FW=new T(function(){return B(unCStr(")"));}),_FX=new T(function(){return B(unCStr(" ("));}),_FY=new T(function(){return B(unCStr("interrupted"));}),_FZ=new T(function(){return B(unCStr("system error"));}),_G0=new T(function(){return B(unCStr("unsatisified constraints"));}),_G1=new T(function(){return B(unCStr("user error"));}),_G2=new T(function(){return B(unCStr("permission denied"));}),_G3=new T(function(){return B(unCStr("illegal operation"));}),_G4=new T(function(){return B(unCStr("end of file"));}),_G5=new T(function(){return B(unCStr("resource exhausted"));}),_G6=new T(function(){return B(unCStr("resource busy"));}),_G7=new T(function(){return B(unCStr("does not exist"));}),_G8=new T(function(){return B(unCStr("already exists"));}),_G9=new T(function(){return B(unCStr("resource vanished"));}),_Ga=new T(function(){return B(unCStr("timeout"));}),_Gb=new T(function(){return B(unCStr("unsupported operation"));}),_Gc=new T(function(){return B(unCStr("hardware fault"));}),_Gd=new T(function(){return B(unCStr("inappropriate type"));}),_Ge=new T(function(){return B(unCStr("invalid argument"));}),_Gf=new T(function(){return B(unCStr("failed"));}),_Gg=new T(function(){return B(unCStr("protocol error"));}),_Gh=function(_Gi,_Gj){switch(E(_Gi)){case 0:return new F(function(){return _n(_G8,_Gj);});break;case 1:return new F(function(){return _n(_G7,_Gj);});break;case 2:return new F(function(){return _n(_G6,_Gj);});break;case 3:return new F(function(){return _n(_G5,_Gj);});break;case 4:return new F(function(){return _n(_G4,_Gj);});break;case 5:return new F(function(){return _n(_G3,_Gj);});break;case 6:return new F(function(){return _n(_G2,_Gj);});break;case 7:return new F(function(){return _n(_G1,_Gj);});break;case 8:return new F(function(){return _n(_G0,_Gj);});break;case 9:return new F(function(){return _n(_FZ,_Gj);});break;case 10:return new F(function(){return _n(_Gg,_Gj);});break;case 11:return new F(function(){return _n(_Gf,_Gj);});break;case 12:return new F(function(){return _n(_Ge,_Gj);});break;case 13:return new F(function(){return _n(_Gd,_Gj);});break;case 14:return new F(function(){return _n(_Gc,_Gj);});break;case 15:return new F(function(){return _n(_Gb,_Gj);});break;case 16:return new F(function(){return _n(_Ga,_Gj);});break;case 17:return new F(function(){return _n(_G9,_Gj);});break;default:return new F(function(){return _n(_FY,_Gj);});}},_Gk=new T(function(){return B(unCStr("}"));}),_Gl=new T(function(){return B(unCStr("{handle: "));}),_Gm=function(_Gn,_Go,_Gp,_Gq,_Gr,_Gs){var _Gt=new T(function(){var _Gu=new T(function(){var _Gv=new T(function(){var _Gw=E(_Gq);if(!_Gw._){return E(_Gs);}else{var _Gx=new T(function(){return B(_n(_Gw,new T(function(){return B(_n(_FW,_Gs));},1)));},1);return B(_n(_FX,_Gx));}},1);return B(_Gh(_Go,_Gv));}),_Gy=E(_Gp);if(!_Gy._){return E(_Gu);}else{return B(_n(_Gy,new T(function(){return B(_n(_FV,_Gu));},1)));}}),_Gz=E(_Gr);if(!_Gz._){var _GA=E(_Gn);if(!_GA._){return E(_Gt);}else{var _GB=E(_GA.a);if(!_GB._){var _GC=new T(function(){var _GD=new T(function(){return B(_n(_Gk,new T(function(){return B(_n(_FV,_Gt));},1)));},1);return B(_n(_GB.a,_GD));},1);return new F(function(){return _n(_Gl,_GC);});}else{var _GE=new T(function(){var _GF=new T(function(){return B(_n(_Gk,new T(function(){return B(_n(_FV,_Gt));},1)));},1);return B(_n(_GB.a,_GF));},1);return new F(function(){return _n(_Gl,_GE);});}}}else{return new F(function(){return _n(_Gz.a,new T(function(){return B(_n(_FV,_Gt));},1));});}},_GG=function(_GH){var _GI=E(_GH);return new F(function(){return _Gm(_GI.a,_GI.b,_GI.c,_GI.d,_GI.f,_w);});},_GJ=function(_GK,_GL,_GM){var _GN=E(_GL);return new F(function(){return _Gm(_GN.a,_GN.b,_GN.c,_GN.d,_GN.f,_GM);});},_GO=function(_GP,_GQ){var _GR=E(_GP);return new F(function(){return _Gm(_GR.a,_GR.b,_GR.c,_GR.d,_GR.f,_GQ);});},_GS=function(_GT,_GU){return new F(function(){return _49(_GO,_GT,_GU);});},_GV=new T3(0,_GJ,_GG,_GS),_GW=new T(function(){return new T5(0,_FQ,_GV,_GX,_FS,_GG);}),_GX=function(_GY){return new T2(0,_GW,_GY);},_GZ=__Z,_H0=7,_H1=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:118:3-9"));}),_H2=new T6(0,_GZ,_H0,_w,_H1,_GZ,_GZ),_H3=new T(function(){return B(_GX(_H2));}),_H4=function(_){return new F(function(){return die(_H3);});},_H5=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:117:3-9"));}),_H6=new T6(0,_GZ,_H0,_w,_H5,_GZ,_GZ),_H7=new T(function(){return B(_GX(_H6));}),_H8=function(_){return new F(function(){return die(_H7);});},_H9=function(_Ha,_){return new T2(0,_w,_Ha);},_Hb=0.6,_Hc=1,_Hd=new T(function(){return B(unCStr(")"));}),_He=function(_Hf,_Hg){var _Hh=new T(function(){var _Hi=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Bf(0,_Hf,_w)),_Hd));})));},1);return B(_n(B(_Bf(0,_Hg,_w)),_Hi));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Hh)));});},_Hj=function(_Hk,_Hl){var _Hm=new T(function(){var _Hn=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_n(B(_Bf(0,_Hl,_w)),_Hd));})));},1);return B(_n(B(_Bf(0,_Hk,_w)),_Hn));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_Hm)));});},_Ho=function(_Hp){var _Hq=E(_Hp);if(!_Hq._){return E(_H9);}else{var _Hr=new T(function(){return B(_Ho(_Hq.b));}),_Hs=function(_Ht){var _Hu=E(_Ht);if(!_Hu._){return E(_Hr);}else{var _Hv=_Hu.a,_Hw=new T(function(){return B(_Hs(_Hu.b));}),_Hx=new T(function(){return 0.1*E(E(_Hv).e)/1.0e-2;}),_Hy=new T(function(){var _Hz=E(_Hv);if(_Hz.a!=_Hz.b){return E(_Hc);}else{return E(_Hb);}}),_HA=function(_HB,_){var _HC=E(_HB),_HD=_HC.c,_HE=_HC.d,_HF=E(_HC.a),_HG=E(_HC.b),_HH=E(_Hv),_HI=_HH.a,_HJ=_HH.b,_HK=E(_HH.c),_HL=_HK.b,_HM=E(_HK.a),_HN=_HM.a,_HO=_HM.b,_HP=_HM.c,_HQ=E(_HH.d),_HR=_HQ.b,_HS=E(_HQ.a),_HT=_HS.a,_HU=_HS.b,_HV=_HS.c;if(_HF>_HI){return new F(function(){return _H8(_);});}else{if(_HI>_HG){return new F(function(){return _H8(_);});}else{if(_HF>_HJ){return new F(function(){return _H4(_);});}else{if(_HJ>_HG){return new F(function(){return _H4(_);});}else{var _HW=_HI-_HF|0;if(0>_HW){return new F(function(){return _He(_HD,_HW);});}else{if(_HW>=_HD){return new F(function(){return _He(_HD,_HW);});}else{var _HX=E(_HE[_HW]),_HY=E(_HX.c),_HZ=_HY.b,_I0=E(_HY.a),_I1=_I0.a,_I2=_I0.b,_I3=_I0.c,_I4=E(_HX.e),_I5=E(_I4.a),_I6=B(_EH(_ji,_HN,_HO,_HP,_HL,_I1,_I2,_I3,_HZ)),_I7=E(_I6.a),_I8=B(_EH(_ji,_I7.a,_I7.b,_I7.c,_I6.b,_HN,_HO,_HP,_HL)),_I9=E(_I8.a),_Ia=_HJ-_HF|0;if(0>_Ia){return new F(function(){return _Hj(_Ia,_HD);});}else{if(_Ia>=_HD){return new F(function(){return _Hj(_Ia,_HD);});}else{var _Ib=E(_HE[_Ia]),_Ic=E(_Ib.c),_Id=_Ic.b,_Ie=E(_Ic.a),_If=_Ie.a,_Ig=_Ie.b,_Ih=_Ie.c,_Ii=E(_Ib.e),_Ij=E(_Ii.a),_Ik=B(_EH(_ji,_HT,_HU,_HV,_HR,_If,_Ig,_Ih,_Id)),_Il=E(_Ik.a),_Im=B(_EH(_ji,_Il.a,_Il.b,_Il.c,_Ik.b,_HT,_HU,_HV,_HR)),_In=E(_Im.a),_Io=E(_I9.a)+E(_I9.b)+E(_I9.c)+E(_I8.b)+E(_In.a)+E(_In.b)+E(_In.c)+E(_Im.b);if(!_Io){var _Ip=B(A2(_Hw,_HC,_));return new T2(0,new T2(1,_kz,new T(function(){return E(E(_Ip).a);})),new T(function(){return E(E(_Ip).b);}));}else{var _Iq=new T(function(){return  -((B(_FA(_jO,_I5.a,_I5.b,_I5.c,_I4.b,_HN,_HO,_HP,_HL))-B(_FA(_jO,_Ij.a,_Ij.b,_Ij.c,_Ii.b,_HT,_HU,_HV,_HR))-E(_Hx))/_Io);}),_Ir=function(_Is,_It,_Iu,_Iv,_){var _Iw=new T(function(){var _Ix=function(_Iy,_Iz,_IA,_IB,_IC){if(_Iy>_HJ){return E(_IC);}else{if(_HJ>_Iz){return E(_IC);}else{var _ID=function(_){var _IE=newArr(_IA,_ii),_IF=_IE,_IG=function(_IH,_){while(1){if(_IH!=_IA){var _=_IF[_IH]=_IB[_IH],_II=_IH+1|0;_IH=_II;continue;}else{return E(_);}}},_=B(_IG(0,_)),_IJ=_HJ-_Iy|0;if(0>_IJ){return new F(function(){return _Hj(_IJ,_IA);});}else{if(_IJ>=_IA){return new F(function(){return _Hj(_IJ,_IA);});}else{var _=_IF[_IJ]=new T(function(){var _IK=E(_IB[_IJ]),_IL=E(_IK.e),_IM=E(_IL.a),_IN=B(_EH(_ji,_If,_Ig,_Ih,_Id,_HT,_HU,_HV,_HR)),_IO=E(_IN.a),_IP=E(_Iq)*E(_Hy),_IQ=B(_EH(_ji,_IO.a,_IO.b,_IO.c,_IN.b,_IP,_IP,_IP,_IP)),_IR=E(_IQ.a),_IS=B(_ES(_ji,_IM.a,_IM.b,_IM.c,_IL.b, -E(_IR.a), -E(_IR.b), -E(_IR.c), -E(_IQ.b)));return {_:0,a:E(_IK.a),b:E(_IK.b),c:E(_IK.c),d:E(_IK.d),e:E(new T2(0,E(_IS.a),E(_IS.b))),f:E(_IK.f),g:E(_IK.g),h:_IK.h,i:_IK.i,j:_IK.j};});return new T4(0,E(_Iy),E(_Iz),_IA,_IF);}}};return new F(function(){return _AV(_ID);});}}};if(_Is>_HI){return B(_Ix(_Is,_It,_Iu,_Iv,new T4(0,E(_Is),E(_It),_Iu,_Iv)));}else{if(_HI>_It){return B(_Ix(_Is,_It,_Iu,_Iv,new T4(0,E(_Is),E(_It),_Iu,_Iv)));}else{var _IT=function(_){var _IU=newArr(_Iu,_ii),_IV=_IU,_IW=function(_IX,_){while(1){if(_IX!=_Iu){var _=_IV[_IX]=_Iv[_IX],_IY=_IX+1|0;_IX=_IY;continue;}else{return E(_);}}},_=B(_IW(0,_)),_IZ=_HI-_Is|0;if(0>_IZ){return new F(function(){return _He(_Iu,_IZ);});}else{if(_IZ>=_Iu){return new F(function(){return _He(_Iu,_IZ);});}else{var _=_IV[_IZ]=new T(function(){var _J0=E(_Iv[_IZ]),_J1=E(_J0.e),_J2=E(_J1.a),_J3=B(_EH(_ji,_I1,_I2,_I3,_HZ,_HN,_HO,_HP,_HL)),_J4=E(_J3.a),_J5=E(_Iq)*E(_Hy),_J6=B(_EH(_ji,_J4.a,_J4.b,_J4.c,_J3.b,_J5,_J5,_J5,_J5)),_J7=E(_J6.a),_J8=B(_ES(_ji,_J2.a,_J2.b,_J2.c,_J1.b,_J7.a,_J7.b,_J7.c,_J6.b));return {_:0,a:E(_J0.a),b:E(_J0.b),c:E(_J0.c),d:E(_J0.d),e:E(new T2(0,E(_J8.a),E(_J8.b))),f:E(_J0.f),g:E(_J0.g),h:_J0.h,i:_J0.i,j:_J0.j};});return new T4(0,E(_Is),E(_It),_Iu,_IV);}}},_J9=B(_AV(_IT));return B(_Ix(E(_J9.a),E(_J9.b),_J9.c,_J9.d,_J9));}}});return new T2(0,_kz,_Iw);};if(!E(_HH.f)){var _Ja=B(_Ir(_HF,_HG,_HD,_HE,_)),_Jb=B(A2(_Hw,new T(function(){return E(E(_Ja).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_Ja).a);}),new T(function(){return E(E(_Jb).a);})),new T(function(){return E(E(_Jb).b);}));}else{if(E(_Iq)<0){var _Jc=B(A2(_Hw,_HC,_));return new T2(0,new T2(1,_kz,new T(function(){return E(E(_Jc).a);})),new T(function(){return E(E(_Jc).b);}));}else{var _Jd=B(_Ir(_HF,_HG,_HD,_HE,_)),_Je=B(A2(_Hw,new T(function(){return E(E(_Jd).b);}),_));return new T2(0,new T2(1,new T(function(){return E(E(_Jd).a);}),new T(function(){return E(E(_Je).a);})),new T(function(){return E(E(_Je).b);}));}}}}}}}}}}}};return E(_HA);}};return new F(function(){return _Hs(_Hq.a);});}},_Jf=function(_,_Jg){var _Jh=new T(function(){return B(_Ho(E(_Jg).a));}),_Ji=function(_Jj){var _Jk=E(_Jj);return (_Jk==1)?E(new T2(1,_Jh,_w)):new T2(1,_Jh,new T(function(){return B(_Ji(_Jk-1|0));}));},_Jl=B(_DT(B(_Ji(5)),new T(function(){return E(E(_Jg).b);}),_)),_Jm=new T(function(){return B(_Er(_DS,_BH,_Fr,new T(function(){return E(E(_Jl).b);})));});return new T2(0,_kz,_Jm);},_Jn=function(_Jo,_Jp,_Jq,_Jr,_Js){var _Jt=B(_8s(B(_8q(_Jo))));return new F(function(){return A3(_86,_Jt,new T(function(){return B(A3(_8u,_Jt,_Jp,_Jr));}),new T(function(){return B(A3(_8u,_Jt,_Jq,_Js));}));});},_Ju=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:61:7-13"));}),_Jv=new T6(0,_GZ,_H0,_w,_Ju,_GZ,_GZ),_Jw=new T(function(){return B(_GX(_Jv));}),_Jx=function(_){return new F(function(){return die(_Jw);});},_Jy=new T(function(){return B(unCStr("Pattern match failure in do expression at Lib\\Physics.hs:59:5-11"));}),_Jz=new T6(0,_GZ,_H0,_w,_Jy,_GZ,_GZ),_JA=new T(function(){return B(_GX(_Jz));}),_JB=function(_){return new F(function(){return die(_JA);});},_JC=false,_JD=true,_JE=function(_JF){var _JG=E(_JF),_JH=_JG.b,_JI=E(_JG.d),_JJ=E(_JG.e),_JK=E(_JJ.a),_JL=E(_JG.g),_JM=B(A1(_JH,_JI.a)),_JN=B(_md(_jO,_JM.a,_JM.b,_JM.c,_JL.a,_JL.b,_JL.c));return {_:0,a:E(_JG.a),b:E(_JH),c:E(_JG.c),d:E(_JI),e:E(new T2(0,E(new T3(0,E(_JK.a)+E(_JN.a)*1.0e-2,E(_JK.b)+E(_JN.b)*1.0e-2,E(_JK.c)+E(_JN.c)*1.0e-2)),E(_JJ.b))),f:E(_JG.f),g:E(_JL),h:_JG.h,i:_JG.i,j:_JG.j};},_JO=new T(function(){return eval("__strict(collideBound)");}),_JP=new T(function(){return eval("__strict(mouseContact)");}),_JQ=new T(function(){return eval("__strict(collide)");}),_JR=function(_JS){var _JT=E(_JS);if(!_JT._){return __Z;}else{return new F(function(){return _n(_JT.a,new T(function(){return B(_JR(_JT.b));},1));});}},_JU=0,_JV=new T3(0,E(_JU),E(_JU),E(_JU)),_JW=new T2(0,E(_JV),E(_JU)),_JX=new T2(0,_jO,_kn),_JY=new T(function(){return B(_hP(_JX));}),_JZ=function(_K0,_){var _K1=B(_Er(_DS,_BH,_JE,_K0)),_K2=E(_K1.a),_K3=E(_K1.b);if(_K2<=_K3){var _K4=function(_K5,_K6,_K7,_K8,_K9,_){if(_K6>_K5){return new F(function(){return _JB(_);});}else{if(_K5>_K7){return new F(function(){return _JB(_);});}else{var _Ka=new T(function(){var _Kb=_K5-_K6|0;if(0>_Kb){return B(_Hj(_Kb,_K8));}else{if(_Kb>=_K8){return B(_Hj(_Kb,_K8));}else{return E(_K9[_Kb]);}}}),_Kc=function(_Kd,_Ke,_Kf,_Kg,_Kh,_){var _Ki=E(_Kd);if(!_Ki._){return new T2(0,_w,new T4(0,E(_Ke),E(_Kf),_Kg,_Kh));}else{var _Kj=E(_Ki.a);if(_Ke>_Kj){return new F(function(){return _Jx(_);});}else{if(_Kj>_Kf){return new F(function(){return _Jx(_);});}else{var _Kk=_Kj-_Ke|0;if(0>_Kk){return new F(function(){return _He(_Kg,_Kk);});}else{if(_Kk>=_Kg){return new F(function(){return _He(_Kg,_Kk);});}else{var _Kl=__app2(E(_JQ),B(_B5(E(_Ka))),B(_B5(E(_Kh[_Kk])))),_Km=__arr2lst(0,_Kl),_Kn=B(_Ck(_Km,_)),_Ko=B(_Kc(_Ki.b,_Ke,_Kf,_Kg,_Kh,_)),_Kp=new T(function(){var _Kq=new T(function(){return _K5!=_Kj;}),_Kr=function(_Ks){var _Kt=E(_Ks);if(!_Kt._){return __Z;}else{var _Ku=_Kt.b,_Kv=E(_Kt.a),_Kw=E(_Kv.b),_Kx=E(_Kv.a),_Ky=E(_Kv.c),_Kz=_Ky.a,_KA=_Ky.b,_KB=E(_Kv.e),_KC=E(_Kv.d),_KD=_KC.a,_KE=_KC.b,_KF=E(_Kv.f),_KG=new T(function(){var _KH=B(_ln(_jO,_KF.a,_KF.b,_KF.c)),_KI=Math.sqrt(B(_Jn(_jO,_KD,_KE,_KD,_KE)));return new T3(0,_KI*E(_KH.a),_KI*E(_KH.b),_KI*E(_KH.c));}),_KJ=new T(function(){var _KK=B(_ln(_jO,_KB.a,_KB.b,_KB.c)),_KL=Math.sqrt(B(_Jn(_jO,_Kz,_KA,_Kz,_KA)));return new T3(0,_KL*E(_KK.a),_KL*E(_KK.b),_KL*E(_KK.c));}),_KM=new T(function(){var _KN=B(A1(_JY,_Kw)),_KO=B(_ln(_jO,_KN.a,_KN.b,_KN.c));return new T3(0,E(_KO.a),E(_KO.b),E(_KO.c));}),_KP=new T(function(){var _KQ=B(A1(_JY,_Kx)),_KR=B(_ln(_jO,_KQ.a,_KQ.b,_KQ.c));return new T3(0,E(_KR.a),E(_KR.b),E(_KR.c));}),_KS=E(_Kw.a)+ -E(_Kx.a),_KT=E(_Kw.b)+ -E(_Kx.b),_KU=E(_Kw.c)+ -E(_Kx.c),_KV=new T(function(){return Math.sqrt(B(_ld(_jO,_KS,_KT,_KU,_KS,_KT,_KU)));}),_KW=new T(function(){var _KX=1/E(_KV);return new T3(0,_KS*_KX,_KT*_KX,_KU*_KX);}),_KY=new T(function(){if(!E(_Kv.g)){return E(_KW);}else{var _KZ=E(_KW);return new T3(0,-1*E(_KZ.a),-1*E(_KZ.b),-1*E(_KZ.c));}}),_L0=new T(function(){if(!E(_Kv.h)){return E(_KW);}else{var _L1=E(_KW);return new T3(0,-1*E(_L1.a),-1*E(_L1.b),-1*E(_L1.c));}});return (!E(_Kq))?new T2(1,new T(function(){var _L2=E(_KY),_L3=E(_L2.b),_L4=E(_L2.c),_L5=E(_L2.a),_L6=E(_KP),_L7=E(_L6.c),_L8=E(_L6.b),_L9=E(_L6.a),_La=E(_KJ),_Lb=E(_La.c),_Lc=E(_La.b),_Ld=E(_La.a),_Le=_L3*_L7-_L8*_L4,_Lf=_L4*_L9-_L7*_L5,_Lg=_L5*_L8-_L9*_L3,_Lh=B(_ld(_jO,_Lf*_Lb-_Lc*_Lg,_Lg*_Ld-_Lb*_Le,_Le*_Lc-_Ld*_Lf,_L9,_L8,_L7));return new T6(0,_K5,_Kj,E(new T2(0,E(new T3(0,E(_Le),E(_Lf),E(_Lg))),E(_Lh))),E(_JW),_KV,_JC);}),new T2(1,new T(function(){var _Li=E(_L0),_Lj=E(_Li.b),_Lk=E(_Li.c),_Ll=E(_Li.a),_Lm=E(_KM),_Ln=E(_Lm.c),_Lo=E(_Lm.b),_Lp=E(_Lm.a),_Lq=E(_KG),_Lr=E(_Lq.c),_Ls=E(_Lq.b),_Lt=E(_Lq.a),_Lu=_Lj*_Ln-_Lo*_Lk,_Lv=_Lk*_Lp-_Ln*_Ll,_Lw=_Ll*_Lo-_Lp*_Lj,_Lx=B(_ld(_jO,_Lv*_Lr-_Ls*_Lw,_Lw*_Lt-_Lr*_Lu,_Lu*_Ls-_Lt*_Lv,_Lp,_Lo,_Ln));return new T6(0,_K5,_Kj,E(_JW),E(new T2(0,E(new T3(0,E(_Lu),E(_Lv),E(_Lw))),E(_Lx))),_KV,_JC);}),new T(function(){return B(_Kr(_Ku));}))):new T2(1,new T(function(){var _Ly=E(_KY),_Lz=E(_Ly.b),_LA=E(_Ly.c),_LB=E(_Ly.a),_LC=E(_KP),_LD=_LC.a,_LE=_LC.b,_LF=_LC.c,_LG=B(_md(_jO,_LB,_Lz,_LA,_LD,_LE,_LF)),_LH=E(_KJ),_LI=E(_LH.c),_LJ=E(_LH.b),_LK=E(_LH.a),_LL=B(_ld(_jO,_Lz*_LI-_LJ*_LA,_LA*_LK-_LI*_LB,_LB*_LJ-_LK*_Lz,_LD,_LE,_LF)),_LM=E(_L0),_LN=E(_LM.b),_LO=E(_LM.c),_LP=E(_LM.a),_LQ=E(_KM),_LR=_LQ.a,_LS=_LQ.b,_LT=_LQ.c,_LU=B(_md(_jO,_LP,_LN,_LO,_LR,_LS,_LT)),_LV=E(_KG),_LW=E(_LV.c),_LX=E(_LV.b),_LY=E(_LV.a),_LZ=B(_ld(_jO,_LN*_LW-_LX*_LO,_LO*_LY-_LW*_LP,_LP*_LX-_LY*_LN,_LR,_LS,_LT));return new T6(0,_K5,_Kj,E(new T2(0,E(new T3(0,E(_LG.a),E(_LG.b),E(_LG.c))),E(_LL))),E(new T2(0,E(new T3(0,E(_LU.a),E(_LU.b),E(_LU.c))),E(_LZ))),_KV,_JD);}),new T(function(){return B(_Kr(_Ku));}));}};return B(_Kr(_Kn));});return new T2(0,new T2(1,_Kp,new T(function(){return E(E(_Ko).a);})),new T(function(){return E(E(_Ko).b);}));}}}}}},_M0=B(_Kc(B(_sU(_K5,_K3)),_K6,_K7,_K8,_K9,_)),_M1=E(_Ka),_M2=E(_M1.d).a,_M3=__app1(E(_JO),B(_B5(_M1))),_M4=__arr2lst(0,_M3),_M5=B(_Ck(_M4,_)),_M6=__app1(E(_JP),_K5),_M7=__arr2lst(0,_M6),_M8=B(_Ck(_M7,_));if(_K5!=_K3){var _M9=E(_M0),_Ma=E(_M9.b),_Mb=B(_K4(_K5+1|0,E(_Ma.a),E(_Ma.b),_Ma.c,_Ma.d,_)),_Mc=new T(function(){var _Md=new T(function(){var _Me=B(A1(_JY,_M2)),_Mf=B(_ln(_jO,_Me.a,_Me.b,_Me.c));return new T3(0,E(_Mf.a),E(_Mf.b),E(_Mf.c));}),_Mg=new T(function(){var _Mh=new T(function(){return B(_JR(_M9.a));}),_Mi=function(_Mj){var _Mk=E(_Mj);if(!_Mk._){return E(_Mh);}else{var _Ml=E(_Mk.a),_Mm=E(_Ml.b),_Mn=E(_Ml.a),_Mo=E(_Ml.c),_Mp=_Mo.a,_Mq=_Mo.b,_Mr=E(_Ml.e);return new T2(1,new T(function(){var _Ms=E(_Mm.a)+ -E(_Mn.a),_Mt=E(_Mm.b)+ -E(_Mn.b),_Mu=E(_Mm.c)+ -E(_Mn.c),_Mv=B(A1(_JY,_Mn)),_Mw=B(_ln(_jO,_Mv.a,_Mv.b,_Mv.c)),_Mx=_Mw.a,_My=_Mw.b,_Mz=_Mw.c,_MA=Math.sqrt(B(_ld(_jO,_Ms,_Mt,_Mu,_Ms,_Mt,_Mu))),_MB=1/_MA,_MC=_Ms*_MB,_MD=_Mt*_MB,_ME=_Mu*_MB,_MF=B(_md(_jO,_MC,_MD,_ME,_Mx,_My,_Mz)),_MG=B(_ln(_jO,_Mr.a,_Mr.b,_Mr.c)),_MH=Math.sqrt(B(_Jn(_jO,_Mp,_Mq,_Mp,_Mq))),_MI=_MH*E(_MG.a),_MJ=_MH*E(_MG.b),_MK=_MH*E(_MG.c),_ML=B(_ld(_jO,_MD*_MK-_MJ*_ME,_ME*_MI-_MK*_MC,_MC*_MJ-_MI*_MD,_Mx,_My,_Mz));return new T6(0,_K5,_K5,E(new T2(0,E(new T3(0,E(_MF.a),E(_MF.b),E(_MF.c))),E(_ML))),E(_JW),_MA,_JD);}),new T(function(){return B(_Mi(_Mk.b));}));}};return B(_Mi(_M5));}),_MM=function(_MN){var _MO=E(_MN);if(!_MO._){return E(_Mg);}else{var _MP=E(_MO.a),_MQ=E(_MP.b),_MR=new T(function(){var _MS=E(_M2),_MT=E(_MQ.c)+ -E(_MS.c),_MU=E(_MQ.b)+ -E(_MS.b),_MV=E(_MQ.a)+ -E(_MS.a),_MW=Math.sqrt(B(_ld(_jO,_MV,_MU,_MT,_MV,_MU,_MT))),_MX=function(_MY,_MZ,_N0){var _N1=E(_Md),_N2=_N1.a,_N3=_N1.b,_N4=_N1.c,_N5=B(_md(_jO,_MY,_MZ,_N0,_N2,_N3,_N4)),_N6=B(_ld(_jO,_MZ*0-0*_N0,_N0*0-0*_MY,_MY*0-0*_MZ,_N2,_N3,_N4));return new T6(0,_K5,_K5,new T2(0,E(new T3(0,E(_N5.a),E(_N5.b),E(_N5.c))),E(_N6)),_JW,_MW,_JD);};if(!E(_MP.g)){var _N7=1/_MW,_N8=B(_MX(_MV*_N7,_MU*_N7,_MT*_N7));return new T6(0,_N8.a,_N8.b,E(_N8.c),E(_N8.d),_N8.e,_N8.f);}else{var _N9=1/_MW,_Na=B(_MX(-1*_MV*_N9,-1*_MU*_N9,-1*_MT*_N9));return new T6(0,_Na.a,_Na.b,E(_Na.c),E(_Na.d),_Na.e,_Na.f);}});return new T2(1,_MR,new T(function(){return B(_MM(_MO.b));}));}};return B(_MM(_M8));});return new T2(0,new T2(1,_Mc,new T(function(){return E(E(_Mb).a);})),new T(function(){return E(E(_Mb).b);}));}else{var _Nb=new T(function(){var _Nc=new T(function(){var _Nd=B(A1(_JY,_M2)),_Ne=B(_ln(_jO,_Nd.a,_Nd.b,_Nd.c));return new T3(0,E(_Ne.a),E(_Ne.b),E(_Ne.c));}),_Nf=new T(function(){var _Ng=new T(function(){return B(_JR(E(_M0).a));}),_Nh=function(_Ni){var _Nj=E(_Ni);if(!_Nj._){return E(_Ng);}else{var _Nk=E(_Nj.a),_Nl=E(_Nk.b),_Nm=E(_Nk.a),_Nn=E(_Nk.c),_No=_Nn.a,_Np=_Nn.b,_Nq=E(_Nk.e);return new T2(1,new T(function(){var _Nr=E(_Nl.a)+ -E(_Nm.a),_Ns=E(_Nl.b)+ -E(_Nm.b),_Nt=E(_Nl.c)+ -E(_Nm.c),_Nu=B(A1(_JY,_Nm)),_Nv=B(_ln(_jO,_Nu.a,_Nu.b,_Nu.c)),_Nw=_Nv.a,_Nx=_Nv.b,_Ny=_Nv.c,_Nz=Math.sqrt(B(_ld(_jO,_Nr,_Ns,_Nt,_Nr,_Ns,_Nt))),_NA=1/_Nz,_NB=_Nr*_NA,_NC=_Ns*_NA,_ND=_Nt*_NA,_NE=B(_md(_jO,_NB,_NC,_ND,_Nw,_Nx,_Ny)),_NF=B(_ln(_jO,_Nq.a,_Nq.b,_Nq.c)),_NG=Math.sqrt(B(_Jn(_jO,_No,_Np,_No,_Np))),_NH=_NG*E(_NF.a),_NI=_NG*E(_NF.b),_NJ=_NG*E(_NF.c),_NK=B(_ld(_jO,_NC*_NJ-_NI*_ND,_ND*_NH-_NJ*_NB,_NB*_NI-_NH*_NC,_Nw,_Nx,_Ny));return new T6(0,_K5,_K5,E(new T2(0,E(new T3(0,E(_NE.a),E(_NE.b),E(_NE.c))),E(_NK))),E(_JW),_Nz,_JD);}),new T(function(){return B(_Nh(_Nj.b));}));}};return B(_Nh(_M5));}),_NL=function(_NM){var _NN=E(_NM);if(!_NN._){return E(_Nf);}else{var _NO=E(_NN.a),_NP=E(_NO.b),_NQ=new T(function(){var _NR=E(_M2),_NS=E(_NP.c)+ -E(_NR.c),_NT=E(_NP.b)+ -E(_NR.b),_NU=E(_NP.a)+ -E(_NR.a),_NV=Math.sqrt(B(_ld(_jO,_NU,_NT,_NS,_NU,_NT,_NS))),_NW=function(_NX,_NY,_NZ){var _O0=E(_Nc),_O1=_O0.a,_O2=_O0.b,_O3=_O0.c,_O4=B(_md(_jO,_NX,_NY,_NZ,_O1,_O2,_O3)),_O5=B(_ld(_jO,_NY*0-0*_NZ,_NZ*0-0*_NX,_NX*0-0*_NY,_O1,_O2,_O3));return new T6(0,_K5,_K5,new T2(0,E(new T3(0,E(_O4.a),E(_O4.b),E(_O4.c))),E(_O5)),_JW,_NV,_JD);};if(!E(_NO.g)){var _O6=1/_NV,_O7=B(_NW(_NU*_O6,_NT*_O6,_NS*_O6));return new T6(0,_O7.a,_O7.b,E(_O7.c),E(_O7.d),_O7.e,_O7.f);}else{var _O8=1/_NV,_O9=B(_NW(-1*_NU*_O8,-1*_NT*_O8,-1*_NS*_O8));return new T6(0,_O9.a,_O9.b,E(_O9.c),E(_O9.d),_O9.e,_O9.f);}});return new T2(1,_NQ,new T(function(){return B(_NL(_NN.b));}));}};return B(_NL(_M8));});return new T2(0,new T2(1,_Nb,_w),new T(function(){return E(E(_M0).b);}));}}}},_Oa=B(_K4(_K2,_K2,_K3,_K1.c,_K1.d,_));return new F(function(){return _Jf(_,_Oa);});}else{return new F(function(){return _Jf(_,new T2(0,_w,_K1));});}},_Ob=new T(function(){return eval("__strict(passObject)");}),_Oc=new T(function(){return eval("__strict(refresh)");}),_Od=function(_Oe,_){var _Of=__app0(E(_Oc)),_Og=__app0(E(_Ba)),_Oh=E(_Oe),_Oi=_Oh.c,_Oj=_Oh.d,_Ok=E(_Oh.a),_Ol=E(_Oh.b);if(_Ok<=_Ol){if(_Ok>_Ol){return E(_B8);}else{if(0>=_Oi){return new F(function(){return _Bl(_Oi,0);});}else{var _Om=E(_Ob),_On=__app2(_Om,_Ok,B(_B5(E(_Oj[0]))));if(_Ok!=_Ol){var _Oo=function(_Op,_){if(_Ok>_Op){return E(_B8);}else{if(_Op>_Ol){return E(_B8);}else{var _Oq=_Op-_Ok|0;if(0>_Oq){return new F(function(){return _Bl(_Oi,_Oq);});}else{if(_Oq>=_Oi){return new F(function(){return _Bl(_Oi,_Oq);});}else{var _Or=__app2(_Om,_Op,B(_B5(E(_Oj[_Oq]))));if(_Op!=_Ol){var _Os=B(_Oo(_Op+1|0,_));return new T2(1,_kz,_Os);}else{return _Bq;}}}}}},_Ot=B(_Oo(_Ok+1|0,_)),_Ou=__app0(E(_B9)),_Ov=B(_JZ(_Oh,_));return new T(function(){return E(E(_Ov).b);});}else{var _Ow=__app0(E(_B9)),_Ox=B(_JZ(_Oh,_));return new T(function(){return E(E(_Ox).b);});}}}}else{var _Oy=__app0(E(_B9)),_Oz=B(_JZ(_Oh,_));return new T(function(){return E(E(_Oz).b);});}},_OA=function(_OB,_){while(1){var _OC=E(_OB);if(!_OC._){return _kz;}else{var _OD=_OC.b,_OE=E(_OC.a);switch(_OE._){case 0:var _OF=B(A1(_OE.a,_));_OB=B(_n(_OD,new T2(1,_OF,_w)));continue;case 1:_OB=B(_n(_OD,_OE.a));continue;default:_OB=_OD;continue;}}}},_OG=function(_OH,_OI,_){var _OJ=E(_OH);switch(_OJ._){case 0:var _OK=B(A1(_OJ.a,_));return new F(function(){return _OA(B(_n(_OI,new T2(1,_OK,_w))),_);});break;case 1:return new F(function(){return _OA(B(_n(_OI,_OJ.a)),_);});break;default:return new F(function(){return _OA(_OI,_);});}},_OL=new T0(2),_OM=function(_ON){return new T0(2);},_OO=function(_OP,_OQ,_OR){return function(_){var _OS=E(_OP),_OT=rMV(_OS),_OU=E(_OT);if(!_OU._){var _OV=new T(function(){var _OW=new T(function(){return B(A1(_OR,_kz));});return B(_n(_OU.b,new T2(1,new T2(0,_OQ,function(_OX){return E(_OW);}),_w)));}),_=wMV(_OS,new T2(0,_OU.a,_OV));return _OL;}else{var _OY=E(_OU.a);if(!_OY._){var _=wMV(_OS,new T2(0,_OQ,_w));return new T(function(){return B(A1(_OR,_kz));});}else{var _=wMV(_OS,new T1(1,_OY.b));return new T1(1,new T2(1,new T(function(){return B(A1(_OR,_kz));}),new T2(1,new T(function(){return B(A2(_OY.a,_OQ,_OM));}),_w)));}}};},_OZ=new T(function(){return E(_qr);}),_P0=new T(function(){return eval("window.requestAnimationFrame");}),_P1=new T1(1,_w),_P2=function(_P3,_P4){return function(_){var _P5=E(_P3),_P6=rMV(_P5),_P7=E(_P6);if(!_P7._){var _P8=_P7.a,_P9=E(_P7.b);if(!_P9._){var _=wMV(_P5,_P1);return new T(function(){return B(A1(_P4,_P8));});}else{var _Pa=E(_P9.a),_=wMV(_P5,new T2(0,_Pa.a,_P9.b));return new T1(1,new T2(1,new T(function(){return B(A1(_P4,_P8));}),new T2(1,new T(function(){return B(A1(_Pa.b,_OM));}),_w)));}}else{var _Pb=new T(function(){var _Pc=function(_Pd){var _Pe=new T(function(){return B(A1(_P4,_Pd));});return function(_Pf){return E(_Pe);};};return B(_n(_P7.a,new T2(1,_Pc,_w)));}),_=wMV(_P5,new T1(1,_Pb));return _OL;}};},_Pg=function(_Ph,_Pi){return new T1(0,B(_P2(_Ph,_Pi)));},_Pj=function(_Pk,_Pl){var _Pm=new T(function(){return new T1(0,B(_OO(_Pk,_kz,_OM)));});return function(_){var _Pn=__createJSFunc(2,function(_Po,_){var _Pp=B(_OG(_Pm,_w,_));return _OZ;}),_Pq=__app1(E(_P0),_Pn);return new T(function(){return B(_Pg(_Pk,_Pl));});};},_Pr=new T1(1,_w),_Ps=function(_Pt,_Pu,_){var _Pv=function(_){var _Pw=nMV(_Pt),_Px=_Pw;return new T(function(){var _Py=new T(function(){return B(_Pz(_));}),_PA=function(_){var _PB=rMV(_Px),_PC=B(A2(_Pu,_PB,_)),_=wMV(_Px,_PC),_PD=function(_){var _PE=nMV(_Pr);return new T(function(){return new T1(0,B(_Pj(_PE,function(_PF){return E(_Py);})));});};return new T1(0,_PD);},_PG=new T(function(){return new T1(0,_PA);}),_Pz=function(_PH){return E(_PG);};return B(_Pz(_));});};return new F(function(){return _OG(new T1(0,_Pv),_w,_);});},_PI=new T(function(){return eval("__strict(setBounds)");}),_PJ=function(_){var _PK=__app3(E(_20),E(_91),E(_ib),E(_1Z)),_PL=__app2(E(_PI),E(_1u),E(_1n));return new F(function(){return _Ps(_AY,_Od,_);});},_PM=function(_){return new F(function(){return _PJ(_);});};
var hasteMain = function() {B(A(_PM, [0]));};window.onload = hasteMain;