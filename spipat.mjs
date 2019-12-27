// -*-javascript-*-
// SPITBOL Patterns in JavaScript
// Based on GNAT (GNU Ada Translator) GNAT.SPITBOL.PATTERNS
////////////////////////////////////////////////////////////////
//          Copyright (C) 1998-2013, AdaCore
//          Copyright (C) 2007-2019, Philip L. Budne
// GNAT is free software;  you can  redistribute it  and/or modify it under
// terms of the  GNU General Public License as published  by the Free Soft-
// ware  Foundation;  either version 3,  or (at your option) any later ver-
// sion.  GNAT is distributed in the hope that it will be useful, but WITH-
// OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.
//
// As a special exception under Section 7 of GPL version 3, you are granted
// additional permissions described in the GCC Runtime Library Exception,
// version 3.1, as published by the Free Software Foundation.
//
// You should have received a copy of the GNU General Public License and
// a copy of the GCC Runtime Library Exception along with this program;
// see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
// <http://www.gnu.org/licenses/>.
//
// GNAT was originally developed  by the GNAT team at  New York University.
// Extensive contributions were provided by Ada Core Technologies Inc.
// The C and JavaScript translations were done by Philip L. Budne
////////////////////////////////////////////////////////////////

// This is a native JavaScript implementation of SNOBOL/SPITBOL pattern
// matching.  It's a translation of the C translation of the GNAT
// (GNU Ada Translator) gnat.spitbol.patterns library.

// Written as ES6 (2015) under nodejs 13.5.0
// I hope I won't regret that choice as much as I did
// using C99 for the C port!!

// Different node types implemented as subclasses of PE.  Probably not
// as efficient as a big switch, but keeps different aspects of each
// node (construction, booleans, match operation, display) in one place.

//let STRING_LENGTHS = new Array(10).fill(0);

// XXX for testing under nodejs, set from command line???
//	look at process.argv or process.env
const DEBUG_STACK = false;
const DEBUG_IMAGE = false;
const TEST_IMAGE = false;
const PARANOIA = true;

// uni-chars for display of strings:
export const LQ = '«';	// string left quote
export const RQ = '»';	// string right quote
const CURSOR = '❱';		// display before cursor location
const EOP_INDEX = 0;
const EOP_SYMBOL = '∎';		// "end of proof" (QED)

//////////////// helpers

function is_func(x) {
    return (typeof x === 'function');
}

function is_str(x) {
    return (typeof x === 'string');
}

function is_int(x) {
    return (typeof x === 'number') && (x % 1 === 0);
}

function is_bool(x) {
    return (typeof x === 'boolean');
}

function is_set(x) {
    return x instanceof Set;
}

export function is_pat(x) {
    return x instanceof Pattern;
}

function is_var(x) {
    return x instanceof Var;
}

// explode string into unicode "runes" which may be JS strings of
// length one or two :-( (Where two-character sequences are UTF-16
// "surrogate pairs" (and include all emoji)).

// EXPLODE was a function in MacLISP that took an atom/symbol
// and expanded it to a list with one symbol per character, see:
// http://www.maclisp.info/pitmanual/charac.html#EXPLODE

// "Rune" was the name the datatype used to hold unicode characters
// (code points) on "Plan9 from Bell Labs", where UTF-8 was invented
// by Brian Kernighan and implement by Kernighan and Pike.

// http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.45.1638&rep=rep1&type=pdf
// https://www.researchgate.net/scientific-contributions/3228095_Ken_Thompson
// https://www.unix.com/man-page/plan9/6/utf/
// https://9fans.github.io/plan9port/man/man3/rune.html
// https://www.cl.cam.ac.uk/~mgk25/ucs/utf-8-history.txt

// Ironically the Plan9 rune type was ORIGINALLY only 16 bits, much as
// "characters" in JavaScript are now, but I can't imagine Plan9 ever
// resorted to "surrogate pairs" madness, and probably moved to 32-bit
// runes at some point by just recompiling all their code.

function explode(str) {
    return Array.from(str);
}

// return str as a JS quoted string.
function stringify(str) {
    // maybe use single quotes
    // if string contains double quote (and no singles)??
    return JSON.stringify(str);
}

//////////////// errors

class SpipatError extends Error {}

function error(msg) {
    throw new SpipatError(msg);
}

class SpipatUserError extends SpipatError {}

function uerror(msg) {
    throw new SpipatUserError(msg);
}

function need_ssfv(who) {
    throw new SpipatUserError(`'${who}' needs String, Set, Function or Var`);
}

// from "ssf" matching functions
function need_sf(who, got, func) {
    throw new SpipatUserError(`'${who}' needs String or Set, got ${got} from ${func}`);
}

// from _Var matching functions
function need_s(who, got, v) {
    throw new SpipatUserError(`'${who}' needs String got ${got} from ${v.toString()}`);
}

function need_nnifv(who, n) {
    throw new SpipatUserError(`'${who}' needs non-negative integer, Function, or Var, got ${n}`);
}

function need_nni_func(who, n, func) {
    throw new SpipatUserError(`'${who}' needs non-negative integer from function ${func} got ${n}`);
}

function need_nni_var(who, n, v) {
    throw new SpipatUserError(`'${who}' needs non-negative integer from var ${v.name} got ${n}`);
}

// onmatch/imm/cursor need function or Var
function need_fv(who) {
    throw new SpipatUserError(`'${who}' needs Function or Var`);
}

////////////////////////////////////////////////////////////////
// Pattern Element class

// return values for PE.match method (want enum or class constants):
const M_Pattern_Success = 0;	// entire pattern succeeded
const M_Pattern_Fail = 1;	// entire pattern failed
const M_Succeed = 2;		// node match succeeded
const M_Fail = 3;		// node match failed
const M_Continue = 4;		// node changed, continue

// super-base class.  The only instance of a class directly derived
// from _PE is the singleton PE_EOP instance, EOP, so that the const
// EOP can be used in the constructor for the "PE" class used as the
// base for all other pattern element node types.
class _PE {			// Pattern Element
    constructor(index, pthen, ok_for_simple_arbno, has_alt) {
	this.index = index;
	this.pthen = pthen;
	// want (const) class members:
	this.ok_for_simple_arbno = ok_for_simple_arbno;
	this.has_alt = has_alt;
	this.assign = false;	// imm/onmatch wrappers
	this.need_pat = false;	// image needs pat(x)
    }

    // methods for image (conversion to string):
    name() {
	return this.constructor.name;
    }

    data() {			// return string for additional data
	return null;
    }

    inext(ic) {			// return subsequent pattern (for image)
	return this.pthen;
    }

    image(ic) {
	error(this.name() + " image not defined!");
    }

    match(m) {
	error(this.name() + " match not defined!");
    }

    // return an array of pointers to elements of pattern
    // rooted at this element.
    ref_array() {
	// XXX cache in this.ra???
	let ra = new Array(this.index);

	// Record given pattern element if not already recorded in ra,
	// and also record any referenced pattern elements recursively.
	function record(pe) {
	    if (pe === EOP || ra[pe.index-1])
		return;
	    ra[pe.index-1] = pe;
	    record(pe.pthen);
	    if (pe.has_alt)
		record(pe.alt);
	}

	record(this);		// walk the tree

	Object.freeze(ra);
	return ra;
    } // ref_array

    copy() {			// copy pattern rooted at this node
	let refs = this.ref_array();

	// Holds copies of elements, indexed by index-1
	let copies = new Array(this.index);

	// Now copy all nodes
	for (let j = 0; j < this.index; j++)
	    copies[j] = refs[j].clone();

	// Adjust all internal references
	for (let j = 0; j < this.index; j++) {
	    let e = copies[j];

	    // Adjust successor pointer to point to copy
	    if (e.pthen !== EOP)
		e.pthen = copies[e.pthen.index-1];

	    // Adjust Alt pointer if there is one to point to copy
	    if (e.has_alt && e.alt !== EOP)
		e.alt = copies[e.alt.index-1];
	} // for j
	return copies[this.index-1];
    } // copy

    clone() {			// clone this element, for copy()
	let copy = Object.assign({}, this);

	// is this REALLY the best/right way?
	// do we need to make a copy of the prototype?????
	copy.__proto__ = Object.assign(Object.create(Object.getPrototypeOf(this)),
				       this);
	return copy;
    }

    // Note: this procedure is not used by the normal concatenation circuit,
    // since other fixups are required on the left operand in this case, and
    // they might as well be done all together.
    set_successor(succ) {
	for (let p of this.ref_array()) {
	    if (p.pthen === EOP) {
		p.pthen = succ;
		//console.log(`set node ${p.index} pthen to ${succ.index}`);
	    }
	    if (p.has_alt && p.alt === EOP) {
		p.alt = succ;
		//console.log(`set node ${p.index} alt to ${succ.index}`);
	    }
	}
    }

    seal() {
	Object.seal(this);
    }
}

//////////////// end of pattern (internal)

class PE_EOP extends _PE {	// End Of Pattern
    constructor() {
	super(EOP_INDEX, null, false, false, false);
	this.seal();
    }

    match(m) {
	if (m.stack.base === m.stack.init) {
	    m.trace("  === end of pattern ==="); // no node addr
	    return M_Pattern_Success;
	}
	else {
	    // End of recursive inner match. See separate section on
	    // handing of recursive pattern matches for details.
	    m.trace("  terminating recursive match"); // no node addr
	    let elt = m.stack.peek(m.stack.base - 1);
	    m.node = elt.node;
	    m.pop_region();
	    return M_Continue;
	}
    }

    name() {
	return "EOP";
    }

    clone() {			// single instance
	error("EOP.clone");
    }
}

const EOP = new PE_EOP();	// single instance, never copied

//////////////// PE base class

// base class for all Pattern Element nodes OTHER than EOP.
// UnsealedPE is NOT for direct use!
// All classes that inherit from it should call this.seal
// in the constructor!
export class UnsealedPE extends _PE {
    constructor(index, pthen, ok_for_simple_arbno, has_alt) {
	super(index || 1,
	      pthen || EOP,
	      ok_for_simple_arbno || false,
	      has_alt || false);
    }
}

// base for classes that don't require private data/constructor
class PE extends UnsealedPE {
    constructor(index, pthen, ok_for_simple_arbno, has_alt) {
	super(index, pthen, ok_for_simple_arbno, has_alt);
	this.seal();
    }
}

class VarPE extends UnsealedPE {
    constructor(index, v, ok_for_simple_arbno) {
	super(index, EOP, ok_for_simple_arbno);
	this.assign = true;	// want class member
	this.v = v;
	this.seal();
    }

    data() {
	return this.v.toString();
    }

    image(ic) {
	ic.append(`${this.name()}(${this.data()})`);
    }
}

//////////////// string

// Note, the following is not just an optimization, it is needed
// to ensure that arbno(len(0)) and arbno('') do not generate infinite
// matching loops (PE_Null is *NOT* safe_for_simple_arbno)!

class PE_Null extends PE { // match zero length string
    match(m) {
	m.petrace(this, "matching null string");
	return M_Succeed;
    }

    image(ic) {
	ic.pappend('""');
    }
}

class RunesPE extends UnsealedPE {
    constructor(runes) {
	super(1, EOP, true);	// ok_for_simple_arbno
	this.runes = runes;
	this.length = runes.length; // for general case
	this.need_pat = true;
	this.str = runes.join('');
	this.seal();
    }

    data() {
	return stringify(this.str);
    }

    image(ic) {
	ic.pappend(stringify(this.str));
    }
}

// special case to match single unicode character (rune)
// (which may be one or two javascript "characters" long due to UTF-16)
class PE_String_1 extends RunesPE {
    match(m) {
	m.petrace(this, `matching ${LQ}${this.str}${RQ}`);
	if ((m.length - m.cursor) >= 1 &&
	    m.subject[m.cursor+0] === this.runes[0]) {
	    m.cursor++;
	    return M_Succeed;
	}
	return M_Fail;
    }
}

class PE_String_2 extends RunesPE {
    match(m) {
	m.petrace(this, `matching ${LQ}${this.str}${RQ}`);
	if ((m.length - m.cursor) >= 2 &&
	    m.subject[m.cursor+0] === this.runes[0] &&
	    m.subject[m.cursor+1] === this.runes[1]) {
	    m.cursor += 2;
	    return M_Succeed;
	}
	return M_Fail;
    }
}

class PE_String_3 extends RunesPE {
    match(m) {
	m.petrace(this, `matching ${LQ}${this.str}${RQ}`);
	if ((m.length - m.cursor) >= 3 &&
	    m.subject[m.cursor+0] === this.runes[0] &&
	    m.subject[m.cursor+1] === this.runes[1] &&
	    m.subject[m.cursor+2] === this.runes[2]) {
	    m.cursor += 3;
	    return M_Succeed;
	}
	return M_Fail;
    }
}

class PE_String_4 extends RunesPE {
    match(m) {
	m.petrace(this, `matching ${LQ}${this.str}${RQ}`);
	if ((m.length - m.cursor) >= 4 &&
	    m.subject[m.cursor+0] === this.runes[0] &&
	    m.subject[m.cursor+1] === this.runes[1] &&
	    m.subject[m.cursor+2] === this.runes[2] &&
	    m.subject[m.cursor+3] === this.runes[3]) {
	    m.cursor += 4;
	    return M_Succeed;
	}
	return M_Fail;
    }
}

class PE_String_5 extends RunesPE {
    match(m) {
	m.petrace(this, `matching ${LQ}${this.str}${RQ}`);
	if ((m.length - m.cursor) >= 5 &&
	    m.subject[m.cursor+0] === this.runes[0] &&
	    m.subject[m.cursor+1] === this.runes[1] &&
	    m.subject[m.cursor+2] === this.runes[2] &&
	    m.subject[m.cursor+3] === this.runes[3] &&
	    m.subject[m.cursor+4] === this.runes[4]) {
	    m.cursor += 5;
	    return M_Succeed;
	}
	return M_Fail;
    }
}

class PE_String_6 extends RunesPE {
    match(m) {
	m.petrace(this, `matching ${LQ}${this.str}${RQ}`);
	if ((m.length - m.cursor) >= 6 &&
	    m.subject[m.cursor+0] === this.runes[0] &&
	    m.subject[m.cursor+1] === this.runes[1] &&
	    m.subject[m.cursor+2] === this.runes[2] &&
	    m.subject[m.cursor+3] === this.runes[3] &&
	    m.subject[m.cursor+4] === this.runes[4] &&
	    m.subject[m.cursor+5] === this.runes[5]) {
	    m.cursor += 6;
	    return M_Succeed;
	}
	return M_Fail;
    }
}

class PE_String extends RunesPE {
    match(m) {
	m.petrace(this, `matching ${LQ}${this.str}${RQ}`);
	if ((m.length - m.cursor) >= this.length) {
	    for (let i = 0; i < this.length; i++)
		if (m.subject[m.cursor + i] !== this.runes[i])
		    return M_Fail;
	    m.cursor += this.runes.length;
	    return M_Succeed;
	}
	return M_Fail;
    }
}

class PE_Var extends VarPE {
    constructor(v) {		// XXX Var1PE?
	super(1, v);
	this.need_pat = true;
    }

    match(m) {
	let str = this.v.get();
	m.petrace(this, `matching ${LQ}${str}${RQ}`);
	if (!is_str(str))
	    need_s('pat', str, this.v);
	let runes = explode(str);
	if ((m.length - m.cursor) >= runes.length) {
	    for (let i = 0; i < runes.length; i++)
		if (m.subject[m.cursor + i] !== runes[i])
		    return M_Fail;
	    m.cursor += runes.length;
	    return M_Succeed;
	}
	return M_Fail;
    }

    image(ic) {
	ic.append(this.v.toString());
    }
}

class FuncPE extends UnsealedPE {
    constructor(index, func, ok_for_simple_arbno, need_pat) {
	super(index, EOP, ok_for_simple_arbno);
	this.func = func;
	// true if node needs to be wrapped in pat() for image:
	this.need_pat = need_pat || false;
	this.seal();
    }

    data() {
	if (this.func.name)
	    return this.func.name;
	else
	    return this.func.toString(); // anonymous: return defn
    }

    image(ic) {
	ic.append(`${this.name()}(${this.data()})`);
    }
}

// call func at match time, handles:
// string, pattern, boolean
class PE_Func extends FuncPE {
    constructor(func) {		     // XXX Func1PE?
	super(1, func, false, true); // need_pat
    }

    match(m) {
	let x = this.func();
	if (is_str(x)) {
	    m.petrace(this, `function ${this.data()} matching ${LQ}${x}${RQ}`);
	    let runes = explode(x);
	    let length = runes.length;
	    if ((m.length - m.cursor) >= length) {
		for (let i = 0; i < length; i++) {
		    if (m.subject[m.cursor + i] !== runes[i]) {
			return M_Fail;
		    }
		}
		m.cursor += length;
		return M_Succeed;
	    }
	    return M_Fail;
	}
	else if (is_pat(x)) {
	    m.petrace(this, `function ${this.data()} starting recursive match`);
	    if (!m.stack.room(x.stk))
		error("pattern stack overflow");
	    m.stack.put_node(m.stack.ptr + 1, this.pthen);
	    m.push_region()
	    m.node = x.p;
	    return M_Continue;
	}
	else if (is_bool(x) || is_int(x)) {
	    m.petrace(this, `function ${this.data()} returned ${x}`);
	    if (x)
		return M_Succeed;
	    else
		return M_Fail;
	}
	else {
	    uerror(`need String, Pattern, integer, or Boolean from ${this.data()}`);
	}
    }

    image(ic) {
	ic.pappend(`${this.data()}`); // function name or defn
    }
} // PE_Func

// String, Function or Var to PE
function sfv_to_pe(who, x) {
    if (is_str(x)) {
	let runes = explode(x);
// gather stats:
//	if (STRING_LENGTHS) {
//	    let sl = runes.length < STRING_LENGTHS.length ? runes.length : STRING_LENGTHS.length-1;
//	    STRING_LENGTHS[sl] += 1;
//	}
	switch (runes.length) {
	case 0: return new PE_Null(); // not ok_for_simple_arbno!
	case 1: return new PE_String_1(runes);
	case 2: return new PE_String_2(runes);
	case 3: return new PE_String_3(runes);
	case 4: return new PE_String_4(runes);
	case 5: return new PE_String_5(runes);
	case 6: return new PE_String_6(runes);
	default: return new PE_String(runes);
	}
    }
    else if (is_func(x))
	return new PE_Func(x);
    else if (is_var(x))
	return new PE_Var(x);
    else
	uerror(`'${who}' needs String, Function, or Var`);
}

// NOTE: _COULD_ rename Pattern class to PPattern (primative pattern)
// and construct new patterns thru a Pattern subclass constructor.
// But this requires fewer keystrokes:
export function pat(x) { // string or function to Pattern
    return new Pattern(0, sfv_to_pe('pat', x));
}

////////////////
// Abort Node (internal)

// Abort on backtrack of anchored match, fence; abort primative
class PE_Abort extends PE {
    match(m) {
	m.petrace(this, "matching abort");
	return M_Pattern_Fail;
    }

    image(ic) {
	ic.append("abort");
    }
}

const CP_Abort = new PE_Abort(); // for anchored match, fence

////////////////
// Assign Node (internal)

class PE_Assign extends PE { // Assignment on match
    match(m) {
	// If this node is executed, it means the assign-on-match
	// (call-on-match) operation will not happen after all, so we
	// propagate the failure, removing the PE_Assign node.
	m.petrace(this, "deferred assign/call cancelled");
	return M_Fail;
    }

    clone() {			// single instance, stacked only
	error("PE_Assign.clone");
    }
}

const CP_Assign = new PE_Assign();

////////////////
// Region Enter node (internal)

// Region Enter. Initiate new pattern history stack region
// used by immediate and "on match" assignment
class PE_R_Enter extends PE {
    constructor() {
	super();
	this.assign = true;
    }

    match(m) {
	m.petrace(this, "starting match of nested pattern");
	m.stack.put_cursor(m.stack.ptr + 1, m.cursor);
	m.push_region();
	return M_Succeed;
    }

    image(ic) {
	const action = ic.refs[this.index-2];
	action.image(ic); // Imm/OnMatch node
    }

    inext(ic) {
	return ic.refs[this.index-2].pthen; // pick up after Imm/OnMatch
    }
}

////////////////
// Region Remove node (internal).

// This is the node stacked by an R_Enter.
// It removes the special format stack entry right underneath, and
// then restores the outer level stack base and signals failure.

class PE_R_Remove extends PE {
    match(m) {
	// Note: the cursor value at this stage is actually the (negative)
	// stack base value for the outer level.
	m.petrace(this, "failure, match of nested pattern terminated");
	m.stack.set_base(m.cursor);
	m.region_level--;	// XXX check?
	m.stack.ptr--;		// XXX check? HIDE??
	return M_Fail;
    }

    clone() {			// single instance: stacked only
	error("PE_R_Remove.clone");
    }
}

const CP_R_Remove = new PE_R_Remove();

////////////////
// Region restore node. (internal)

// This is the node stacked at the end of an
// inner level match. Its function is to restore the inner level
// region, so that alternatives in this region can be sought.

class PE_R_Restore extends PE {
    match(m) {
	// Note: the Cursor at this stage is actually the negative of the
	// inner stack base value, which we use to restore the inner region.
	m.petrace(this, "failure, search for alternatives in nested pattern");
	m.region_level++;
	m.stack.set_base(m.cursor);
	return M_Fail;
    }

    clone() {			// single instance: stacked only
	error("PE_R_Restore.clone");
    }
}

const CP_R_Restore = new PE_R_Restore();

////////////////
// Unanchored match helper

class PE_Unanchored extends PE { // Unanchored movement
    constructor(node) {
	super(0, node, false);
    }

    match(m) {
	m.trace("  attempting to move anchor point"); // no node addr
	if (m.cursor > m.length) {
	    return M_Pattern_Fail; // All done if we tried every position
	}

	// Otherwise extend the anchor point, and restack ourself
	m.cursor++;
	m.push(this);
	return M_Succeed;
    }
}

////////////////
// Concat

// Concat needs to traverse the left operand performing the following
// set of fixups:

// a) Any successor pointers (Pthen fields) that are set to EOP are
// reset to point to the second operand.

// b) Any PC_Arbno_Y node has its stack count field incremented
// by the parameter Incr provided for this purpose.

// d) Num fields of all pattern elements in the left operand are
// adjusted to include the elements of the right operand.

// Note: we do not use Set_Successor in the processing for Concat, since
// there is no point in doing two traversals, we may as well do everything
// at the same time.

function pe_conc(l, r, incr) {
    if (l === EOP)
	return r;

    if (r === EOP)
	return l;

    // XXX optimize two strings with no alts?

    // loop for all nodes in left
    for (let p of l.ref_array()) {
	p.index += r.index;

	if (p instanceof PE_Arbno_Y) // OOF!
	    p.n += incr;

	if (p.pthen === EOP)
	    p.pthen = r;

	if (p.has_alt && p.alt === EOP)
	   p.alt = r;
    } // for
    return l;
}

////////////////

const STACK_SIZE = 2000;	// XXX

class Match {
    constructor(anchored) {
	this.anchored = anchored;
	this.region_level = 0;
	this.cursor = 0;

	this.subject = null;	// set by match()
	this.length = 0;	// set by match()
	this.node = null;	// set by match()
	this.stack = null;	// set by match()

	// Set true when assign-on-match (call-on-match) operations may be
	// present in the history stack, which must then be scanned on a
	// successful match.
	this.assign_on_match = false;

	this.debug = false;

	// output:
	this.start = 0;
	this.stop = 0;
	this.matched = null;

	Object.seal(this);
    }

    match(subject, pat, stack_size)  {
	if (TEST_IMAGE)
	    console.log("match", pat.toString()); // XXX this.trace?
	// XXX call this.trace w/ pat.trace??

	this.subject = explode(subject); // Array of runes
	this.length = this.subject.length;

	this.node = pat.p;
	if (!stack_size)
	    stack_size = STACK_SIZE;
	if (stack_size < pat.stk*2)
	    stack_size = pat.stk*2;
	this.stack = new Stack(stack_size);

	// push initial stack entry based on anchored mode
	if (this.anchored) {
	    // anchored: abort on backtrack.
	    this.stack.put(this.stack.init, 0, CP_Abort);
	}
	else {
	    // In unanchored mode, the bottom entry on the stack references
	    // the special pattern element PE_Unanchored, whose Pthen field
	    // points to the initial pattern element. The cursor value in this
	    // entry is the number of anchor moves so far.
	    this.stack.put(this.stack.init, 0, new PE_Unanchored(this.node));
	}

	this.trace(`======== match ${LQ}${subject}${RQ} anchored=${this.anchored}`);
	while (this.node) {
	    let n = this.node;
	    this.trace_match(n)
	    switch (n.match(this)) {
	    case M_Succeed:
		this.node = this.node.pthen;
		this.trace("    success");
		break;
	    case M_Fail: {
		let stk = this.stack;
		let top = stk.peek(stk.ptr);
		if (DEBUG_STACK)
		    console.log(`ptr ${stk.ptr} top ${top.cursor} node ${top.node}`)
		stk.ptr--;	// XXX check? HIDE??

		this.cursor = top.cursor;
		this.node   = top.node;

		this.trace(`    failed, cursor reset to ${this.cursor}`);
		break;
	    }
	    case M_Continue:	// node changed, continue
		this.trace("    continue");
		break;
	    case M_Pattern_Success:
		this.trace("match succeeded");
		this.start = this.stack.peek(this.stack.init).cursor + 1;
		this.stop = this.cursor;
		this.matched = this.slice(this.start, this.stop);
		this.trace(` matched positions ${this.start} .. ${this.stop}`);
		this.trace(` matched substring ${LQ}${this.matched}${RQ}`);
		if (this.assign_on_match) {
		    let stk = this.stack;
		    for (let s = stk.first; s <= stk.ptr; s++) {
			let stkent = stk.peek(s);
			if (stkent.node === CP_Assign) {
			    let inner_base = stk.peek(s + 1).cursor; // stack ptr
			    let special_entry = stk.peek(inner_base - 1);
			    let start = special_entry.cursor + 1;
			    let stop = stkent.cursor; // from a CP_Assign stack entry
			    let str = this.slice(start, stop);
			    let on_match = special_entry.node;
			    on_match.onmatch(this, str);
			} // CP_Assign
		    } // for each stack entry
		} // assign_on_match
		return true;
	    case M_Pattern_Fail:
		this.trace("match failed");
		return false;
	    }
	} // while this.node
	error("null PE node");
    } // match

    replace(repl) {
	let before = this.subject.slice(0, this.start-1).join('');
	let after  = this.subject.slice(this.stop, this.length).join('');
	return before + repl + after;
    }

    // Internal:

    slice(start, stop) {
	return this.subject.slice(start-1, stop).join('');
    }

    trace_match(n) {		// overridden in DMatch
    }

    trace(msg) {		// overridden in DMatch
    }

    petrace(pe, msg) {		// overridden in DMatch
    }

    push(node) {
	let stack = this.stack;
	if (DEBUG_STACK)
	    console.log(`stack.push ${this.cursor} ${node.index}`);
	stack.ptr++;		// XXX check? HIDE??
	stack.put(stack.ptr, this.cursor, node);
    }

    push_region() {
	this.region_level++;
	let stack = this.stack;
	stack.ptr += 2;		// XXX check? HIDE??
	if (DEBUG_STACK) console.log("push_region", stack.base);
	stack.put(stack.ptr, stack.base, CP_R_Remove);
	stack.set_base(stack.ptr);
    }

    pop_region() {
	this.region_level--;	// XXX check?
	let stack = this.stack;
	if (stack.ptr === stack.base) {
	    stack.ptr -= 2;	// XXX check? HIDE??
	    stack.set_base(stack.peek(stack.ptr + 2).cursor);
	}
	else {
	    stack.ptr++;	// XXX check? HIDE??
	    stack.put(stack.ptr, stack.base, CP_R_Restore);
	    stack.set_base(stack.peek(stack.base).cursor);
	}
    }
} // Match

class DMatch extends Match {	// debug match
    constructor(anchored, stack_size) {
	super(anchored, stack_size);
	this.debug = true;
    }

    trace_match(n) {
	// XXX if this.cursor < 0, display as stack pointer!!
	// XXX need to handle negative (SP) values??
	let before = this.slice(1, this.cursor);
	let after = this.slice(this.cursor+1, this.length);
	let str =  LQ + before + CURSOR + after + RQ;
	let nname = n.constructor.name;
	this.trace(`cursor @${this.cursor} node #${n.index} ${nname} ${str}`);
    }

    trace(msg) {
	console.log(msg);
    }

    petrace(pe, msg) {		// PE trace
	console.log(`  node ${pe.index} ${msg}`);
    }
}

////////////////

export function print_nodes(refs) {
    for (let r of refs) {
	// EOP will display as EOP_SYMBOL
	let line = `${r.index} ${r.constructor.name}`;
	let d = r.data();
	if (d !== null)
	    line += ` ${d}`;
	if (r.pthen === EOP)
	    line += ' ' + EOP_SYMBOL;
	else
	    line += ` then ${r.pthen.index}`;
	if (r.has_alt)
	    line += ` alt ${r.alt.index}`; // XXX check for EOP?
	console.log(line);
    }
}

// graphviz "dot" format
export function print_dot(refs) {
    console.log('strict digraph foo {');
    console.log('    node [shape=box];');
    // XXX try to force samerank on previously unplaced nodes by following pthen?
    for (let r of refs)
	console.log(`    n${r.index} [label="${r.index}: ${r.constructor.name}"]`)
    
    for (let r of refs)
	if (r.pthen !== EOP)
	    console.log(`    n${r.index}:e -> n${r.pthen.index}:w;`);

    console.log('    edge [style=dashed];');
    for (let r of refs)
	if (r.has_alt && r.alt !== EOP)
	    console.log(`    n${r.index}:s -> n${r.alt.index}:n;`);
    console.log('}');
}

class ImageContext {
    constructor(pat) {
	this.pe = pat.p;
	this.refs = this.pe.ref_array();
	this.result = "";

	// these two probably don't belong!
	this.first = true;

	if (DEBUG_IMAGE) {
	    console.log("****************");
	    print_nodes(this);
	}
	Object.seal(this);
    }

    append(str) {
	this.result += str;
	this.first = false;
    }

    // append a pattern that needs to be wrapped in pat() if first
    pappend(str) {
	if (this.first)
	    this.append(`pat(${str})`);
	else
	    this.append(str);
    }

    // e refers to a pattern structure whose successor is given by succ.
    // This procedure appends a representation of this pattern.
    // "bare_ok" means a bare "need_pat" node is OK (argument to a function)
    sequence(e, succ, bare_ok) {
	if (e === EOP) {
	    this.pappend('""'); // The image of EOP is "" (the null string)
	    return;
	}

	// else generate appropriate concatenation sequence

	// collect list of elements
	let elts = [];
	for(let e1 = e; e1 !== succ && e1 !== EOP; e1 = e1.inext(this))
	    elts.push(e1);

	if (DEBUG_IMAGE) console.log("sequence", elts.map((x) => x.index));

	if (elts.length == 1) {
	    if (bare_ok && elts[0].need_pat) {
		this.first = false;
		elts[0].image(this);
	    }
	    else {
		this.first = true;
		elts[0].image(this);
	    }
	    return;
	}
	this.append('and(');
	this.first = false;
	let n = 0;
	for (let e1 of elts) {
	    if (n > 0)
		this.append(", ");
	    let lenb4 = this.result.length;
	    e1.image(this);
	    // don't count elements (eg; R_Enter) that are invisible
	    if (this.result.length > lenb4)
		n++;
	}
	this.append(')');	// end "and("
    } // sequence

} // ImageContext

////////////////

export class Pattern {	// primative pattern
    constructor (stk, pe) {
	this.stk = stk;
	this.p = pe;
	this.trace = new Error().stack;
	Object.freeze(this);
	// make pattern elements immutable: worth the cost??
	pe.ref_array().map(Object.freeze);
    }

    amatch(subject, debug) {	// anchored match
	let m;
	if (debug) 
	    m = new DMatch(true);
	else
	    m = new Match(true);
	if (m.match(subject, this)) {
	    Object.freeze(m);	// make immutable
	    return m;
	}
	else
	    return null;
    }

    umatch(subject, debug) {	// unanchored match
	let m;
	if (debug)
	    m = new DMatch(false);
	else
	    m = new Match(false);
	if (m.match(subject, this)) {
	    Object.freeze(m);	// make immutable
	    return m;
	}
	else
	    return null;
    }

    and() {
	let lp = this.p;
	let lstk = this.stk;
	for (let i = 0; i < arguments.length; i++) {
	    let r = arguments[i];
	    if (is_str(r) || is_func(r) || is_var(r)) {
		lp = pe_conc(lp.copy(), sfv_to_pe('and', r), 0);
		// no chnge to lstk?? what about func???
	    }
	    else if (is_pat(r)) {
		let rc = r.p.copy();
		lp = pe_conc(lp.copy(), r.p.copy(), r.index);
		lstk += r.stk;
	    }
	    else
		uerror("'and' needs Pattern, String, Var, or Function");
	} // for arguments
	return new Pattern(lstk, lp);
    } // and

    or() {
	let lstk = this.stk;
	let lp = this.p;
	for (let i = 0; i < arguments.length; i++) {
	    let r = arguments[i];
	    if (is_str(r) || is_func(r) || is_var(r)) {
		lstk++;
		lp = pe_alt(lp.copy(), sfv_to_pe('or', r));
	    }
	    else if (is_pat(r)) {
		lstk = Math.max(lstk, r.stk) + 1;
		lp = pe_alt(lp.copy(), r.p.copy());
	    }
	    else
		uerror("'or' needs Pattern, String, Var, or Function");
	} // for arguments
	return new Pattern(lstk, lp);
    } // or

    imm(x) {			// assign/call immediately
	// +---+     +---+     +---+
	// | E |---->| P |---->| A |---->
	// +---+     +---+     +---+

	// The node numbering of the constituent pattern P is not affected.
	// Where N is the number of nodes in P,
	// the A node is N + 1,
	// the E node is N + 2.
	const e   = new PE_R_Enter();
	const pat = this.p.copy();
	let a;
	if (is_func(x))
	    a = new PE_Call_Imm(x);
	else if (is_var(x))
	    a = new PE_Var_Imm(x);
	else
	    need_fv('imm');
	return new Pattern(this.stk + 3, bracket(e, pat, a));
    } // imm

    onmatch(x) {		// assign/call on pattern match
	// +---+     +---+     +---+
	// | E |---->| P |---->| C |---->
	// +---+     +---+     +---+

	// The node numbering of the constituent pattern P is not affected.
	// Where N is the number of nodes in P,
	// the C node is N + 1,
	// the E node is N + 2.

	const e   = new PE_R_Enter();
	const pat = this.p.copy();
	let a;
	if (is_func(x))
	    a = new PE_Call_OnM(x);
	else if (is_var(x))
	    a = new PE_Var_OnM(x);
	else
	    need_fv('onmatch');
	return new Pattern(this.stk + 3, bracket(e, pat, a));
    } // onmatch

    toString() {
	let ic = new ImageContext(this);
	ic.sequence(this.p, EOP, false);
	return ic.result;
    }
}

////////////////////////////////////////////////////////////////

class Stack {
    // XXX for now... make dynamic!!! make -1 the first element!!!
    // stack pointer values are negative!
    constructor(size) {
	this.size  = size;
	this.first = -size;
	this.last  = -1;

	// This is the initial value of the Stack_Ptr and Stack_Base. The
	// initial (Stack_First) element of the stack is not used so that
	// when we pop the last element off, Stack_Ptr is still in range.
	this.init = this.first + 1;

	// Current stack pointer. This points to the top element of the stack
	// that is currently in use. At the outer level this is the special
	// entry placed on the stack according to the anchor mode.
	this.ptr  = this.init;

	// This value is the stack base value, i.e. the stack pointer for the
	// first history stack entry in the current stack region. See separate
	// section on handling of recursive pattern matches.
	this.base = this.init;

	this._arr = [];
	for (let i = 0; i < size; i++) {
	    this._arr.push(new Stack_Entry(0, null));
	}
	Object.seal(this);
    }

    empty() {
	return this.base === this.init;
    }

    peek(n) {			// hide representation!
	//if (n > this.ptr) console.log(`peek @ ${n} ptr ${this.ptr}`);
	let elt = this._arr[this.size + n];
	if (DEBUG_STACK) console.log(`stack.peek ${n} elt ${elt}`);
	return elt;
    }

    put(n, cursor, node) {
	if (DEBUG_STACK)
	    console.log(`stack.put ${n} cursor ${cursor} node ${node.name()}`);
	this._arr[this.size + n].cursor = cursor;
	this._arr[this.size + n].node = node;
    }

    put_cursor(n, cursor) {
	if (DEBUG_STACK)
	    console.log(`stack.put_cursor ${n} cursor ${cursor}`);
	this._arr[this.size + n].cursor = cursor;
    }

    put_node(n, node) {
	if (DEBUG_STACK)
	    console.log(`stack.put_node ${n} node ${node.name()}`);
	this._arr[this.size + n].node = node;
    }

    // return true if room left for n entries on stack
    room(n) {
	//console.log(`room ${n} ptr ${this.ptr} size ${this.size}`)
    	return this.ptr + n < this.size;
    }

    set_base(n) {
	if (DEBUG_STACK) console.log(`stack.set_base ${n}`);
	if (PARANOIA && !is_int(n)) error('bad base');
	this.base = n;
    }
}

class Stack_Entry {
    constructor(cursor, node) {
	this.cursor = cursor;	// or stack ptr if negative
	this.node = node;
	Object.seal(this);
    }
}

////////////////////////////////////////////////////////////////

// make a character set
export function cset(str) {
    if (!is_str(str))
	uerror("'cset' needs String");

    return new Set(explode(str));
}

// utility
function set2str(cset) {
    return Array.from(cset).join('');
}

////////////////////////////////////////////////////////////////

// class for match-time variable.
// pass to .and/.or, .imm/.onmatch, (not)any, break(p|x), (n)span
//	cursor, (r)(tab|pos), len)
let vnum = 1;

export class Var {
    constructor(name, value) {
	if (!name)
	    name = `var${vnum++}`;
	this.name = name
	this.value = value
    }

    get() {
	return this.value;
    }

    set(value) {
	this.value = value;
    }

    toString() {
	return `new Var(${stringify(this.name)})`;
    }
}

////////////////////////////////////////////////////////////////
// Pattern implementation

//////////////// abort

export const abort = new Pattern(0, new PE_Abort());

//////////////// alternate (or)

class AltPE extends UnsealedPE {
    constructor(index, pthen, alt) {
	super(index, pthen, false, true); // has_alt
	this.alt = alt;
	this.seal();
    }
}

class PE_Alt extends AltPE {
    match(m) {
	m.petrace(this, `setting up alternative ${this.alt.index}`);
	m.push(this.alt);
	m.node = this.pthen;
	return M_Continue;
    }

    inext(ic) {
        // Number of elements in left pattern of alternation
	const elmts_in_l = this.pthen.index - this.alt.index;

	// Number of lowest index in elements of left pattern
	const lowest_in_l = this.index - elmts_in_l;

	// The successor of the alternation node must have a lower
	// index than any node that is in the left pattern or a
	// higher index than the alternation node itself.
	let er = this.pthen;
	while (er !== EOP &&
	       er.index >= lowest_in_l &&
	       er.index < this.index) {
	    er = er.pthen;
	}
	return er;
    }

    image(ic) {
	let er = this.inext(ic);
	//console.log("er", er.index, er.constructor.name)

	// render or(or(a, b), c) as or(a, b, c)
	var elts = [];
	let e1 = this;
	//console.log('---- alt.image');
	for (;;) {
	    //console.log("e1", e1.index, e1.constructor.name, "then", e1.pthen.index, e1.pthen.constructor.name, e1.pthen.data());
	    elts.unshift(e1.alt);
	    e1 = e1.pthen;
	    if (!(e1 instanceof PE_Alt)) {
		elts.unshift(e1);
		break;
	    }
	}
	ic.append("or(");
	let first = true
	for (e1 of elts) {
	    if (first)
		first = false;
	    else
		ic.append(', ');
	    ic.sequence(e1, er, true); // allow bare string
	}
	ic.append(")");
    }
} // PE_Alt

// helper for Pattern.or
function pe_alt(l, r) {
    // If the left pattern is null, then we just add the alternation
    // node with an index one greater than the right hand pattern.
    if (l === EOP)
	return new PE_Alt(r.index + 1, EOP, r);

    // If the left pattern is non-null, then build a reference vector
    // for its elements, and adjust their index values to acccomodate
    // the right hand elements. Then add the alternation node.
    for (let ref of l.ref_array())
	ref.index += r.index;
    return new PE_Alt(l.index + 1, l, r);
}

//////////////// any

class SetPE extends UnsealedPE {
    // NOTE: BreakX nodes are constructed with index > 1
    constructor(index, cset, ok_for_simple_arbno) {
	super(index, EOP, ok_for_simple_arbno || false);
	this.cset = cset;
	this.str = set2str(cset);
	this.seal();
    }

    data() {
	return stringify(this.str);
    }

    image(ic) {
	ic.append(`${this.name()}(${stringify(this.str)})`);
    }
}

class PE_Any_Set extends SetPE {
    constructor(cset) {		// XXX Set1PE?
	super(1, cset, true);	// ok_for_simple_arbno
    }

    match(m) {
	m.petrace(this, `matching any ${LQ}${this.str}${RQ}`);
	if (m.cursor < m.length && this.cset.has(m.subject[m.cursor])) {
	    m.cursor++;
	    return M_Succeed;
	}
	else
	    return M_Fail;
    }

    name() {
	return "any";
    }
}

class PE_Any_Var extends VarPE {
    constructor(v) {		// XXX Var1PE?
	super(1, v, true);	// ok_for_simple_arbno
    }

    match(m) {
	const str = this.v.get();
	if (!is_str(str))
	    need_s('any', str, this.v);
	m.petrace(this, `matching any (var) ${LQ}${str}${RQ}`);
	const cs = cset(str);
	if (m.cursor < m.length && cs.has(m.subject[m.cursor])) {
	    m.cursor++;
	    return M_Succeed;
	}
	else
	    return M_Fail;
    }

    name() {
	return "any";
    }
}

class PE_Any_Func extends FuncPE {
    constructor(func) {		// XXX Func1PE?
	super(1, func, true);	// ok_for_simple_arbno
    }

    match(m) {
	let cs = this.func();
	m.petrace(this, "matching any (func) ${LQ}${cs}${RQ}");
	if (is_str(cs))
	    cs = cset(cs)
	else if (!is_set(cs))
	    need_sf('any', cs, this.func);

	if (m.cursor < m.length && cs.has(m.subject[m.cursor])) {
	    m.cursor++;
	    return M_Succeed;
	}
	else
	    return M_Fail;
    }

    name() {
	return "any";
    }
}

export function any(x) {
    if (is_str(x))
	return new Pattern(1, new PE_Any_Set(cset(x)));
    else if (is_set(x))
	return new Pattern(1, new PE_Any_Set(x));
    else if (is_var(x))
	return new Pattern(1, new PE_Any_Var(x));
    else if (is_func(x))
	return new Pattern(1, new PE_Any_Func(x));
    else
	need_ssfv('any');
}

//////////////// arb

// +---+
// | X |---->
// +---+
//   .
//   .
// +---+
// | Y |---->
// +---+

// The PC_Arb_X element is 2,
// the PC_Arb_Y element is 1

class PE_Arb_X extends AltPE {	// arb (initial match)
    match(m) {
	m.petrace(this, "matching arb");
	m.push(this.alt);
	m.node = this.pthen;
	return M_Continue;
    }

    image(ic) {
	ic.append("arb");
    }
}

class PE_Arb_Y extends PE {	// arb (extension)
    constructor(index, pthen) {
	super(index, pthen);
    }

    match(m) {
	m.petrace(this, "extending arb");
	if (m.cursor < m.length) {
	    m.cursor++;
	    m.push(this);
	    return M_Succeed;
	}
	return M_Fail;
    }
}

export const arb = new Pattern(1,
				    new PE_Arb_X(2, EOP,
						 new PE_Arb_Y()));

//////////////// arbno (simple case)

// The simple form of Arbno can be used where the pattern always
// matches at least one character if it succeeds, and it is known
// not to make any history stack entries. In this case, arbno(P)
// can construct the following structure:

//   +-------------+
//   |             ^
//   V             |
// +---+           |
// | S |---->      |
// +---+           |
//   .             |
//   .             |
// +---+           |
// | P |---------->+
// +---+

// The S (PC_Arbno_S) node matches null stacking a pointer to the
// pattern P. If a subsequent failure causes P to be matched and
// this match succeeds, then node A gets restacked to try another
// instance if needed by a subsequent failure.

// The node numbering of the constituent pattern P is not affected.
// The S node has a node number of p.index + 1.

//////////////////////////
// Arbno (complex case) //
//////////////////////////

// A call to arbno(P), where P can match null (or at least is not
// known to require a non-null string) and/or P requires pattern stack
// entries, constructs the following structure:

//   +--------------------------+
//   |                          ^
//   V                          |
// +---+                        |
// | X |---->                   |
// +---+                        |
//   .                          |
//   .                          |
// +---+     +---+     +---+    |
// | E |---->| P |---->| Y |--->+
// +---+     +---+     +---+

// The node X (PC_Arbno_X) matches null, stacking a pointer to the
// E-P-X structure used to match one Arbno instance.

// Here E is the PC_R_Enter node which matches null and creates two
// stack entries. The first is a special entry whose node field is
// not used at all, and whose cursor field has the initial cursor.

// The second entry corresponds to a standard new region action. A
// PC_R_Remove node is stacked, whose cursor field is used to store
// the outer stack base, and the stack base is reset to point to
// this PC_R_Remove node. Then the pattern P is matched, and it can
// make history stack entries in the normal manner, so now the stack
// looks like:

// (stack entries made before assign pattern)

// (Special entry, node field not used,
// used only to save initial cursor)

// (PC_R_Remove entry, "cursor" value is (negative)  <-- Stack Base
// saved base value for the enclosing region)

// (stack entries made by matching P)

// If the match of P fails, then the PC_R_Remove entry is popped and
// it removes both itself and the special entry underneath it,
// restores the outer stack base, and signals failure.

// If the match of P succeeds, then node Y, the PC_Arbno_Y node, pops
// the inner region. There are two possibilities. If matching P left
// no stack entries, then all traces of the inner region can be removed.
// If there are stack entries, then we push an PC_Region_Replace stack
// entry whose "cursor" value is the inner stack base value, and then
// restore the outer stack base value, so the stack looks like:

// (stack entries made before assign pattern)

// (Special entry, node field not used,
// used only to save initial cursor)

// (PC_R_Remove entry, "cursor" value is (negative)
// saved base value for the enclosing region)

// (stack entries made by matching P)

// (PC_Region_Replace entry, "cursor" value is (negative)
// stack pointer value referencing the PC_R_Remove entry).

// Now that we have matched another instance of the Arbno pattern,
// we need to move to the successor. There are two cases. If the
// Arbno pattern matched null, then there is no point in seeking
// alternatives, since we would just match a whole bunch of nulls.
// In this case we look through the alternative node, and move
// directly to its successor (i.e. the successor of the Arbno
// pattern). If on the other hand a non-null string was matched,
// we simply follow the successor to the alternative node, which
// sets up for another possible match of the Arbno pattern.

// As noted in the section on stack checking, the stack count (and
// hence the stack check) for a pattern includes only one iteration
// of the Arbno pattern. To make sure that multiple iterations do not
// overflow the stack, the Arbno node saves the stack count required
// by a single iteration, and the Concat function increments this to
// include stack entries required by any successor. The PC_Arbno_Y
// node uses this count to ensure that sufficient stack remains
// before proceeding after matching each new instance.

// The node numbering of the constituent pattern P is not affected.
// Where N is the number of nodes in P,
// the Y node is N + 1,
// the E node is N + 2,
// the X node is N + 3.


// This is the node that initiates
// the match of a simple Arbno structure
class PE_Arbno_S extends AltPE { // Arbno_S (simple Arbno initialize)
    match(m) {
	m.petrace(this, `setting up arbno alternative ${this.alt.index}`);
	m.push(this.alt);
	m.node = this.pthen;
	return M_Continue;
    }

    image(ic) {
	ic.append('arbno(');
	ic.sequence(this.alt, this, true);
	ic.append(')');
    }
} // PE_Arbno_S

// helper for arbno()
function _arbno_simple(p) {
    let s = new PE_Arbno_S(p.index + 1, EOP, p);
    p.set_successor(s);
    return s;
}

// This is the node that initiates
// the match of a complex Arbno structure.
class PE_Arbno_X extends AltPE {	// Arbno_X (Arbno initialize)
    match(m) {
	m.petrace(this, `setting up arbno alternative ${this.alt.index}`);
	m.push(this.alt);
	m.node = this.pthen;
	return M_Continue;
    }

    image(ic) {
	ic.append('arbno(');
	ic.sequence(this.alt.pthen, ic.refs[this.index-3], true);
	ic.append(')');
    }
} // PE_Arbno_X

// This is the node that is executed following successful
// matching of one instance of a complex Arbno pattern.
class PE_Arbno_Y extends UnsealedPE {	// Arbno_Y (Arbno rematch)
    constructor(index, pthen, n) {
	super(index, pthen);
	this.n = n;
	this.seal();
    }

    match(m) {
	let stk = m.stack;
	let null_match = (m.cursor === stk.peek(stk.base - 1).cursor);

	m.petrace(this, "extending arbno");
	m.pop_region();

	// If (arbno extension matched null, then immediately fail
	if (null_match) {
	    m.trace("arbno extension matched null, so fails");
	    return M_Fail;
	}

	// Here we must do a stack check to make sure enough stack
	// is left. This check will happen once for each instance of
	// the Arbno pattern that is matched. The Nat field of a
	// PC_Arbno pattern contains the maximum stack entries needed
	// for the Arbno with one instance and the successor pattern
	if ((stk.ptr + this.n) >= stk.last)
	    error("pattern stack overflow");
	return M_Succeed;
    }

    image(ic) {
	ic.append("PE_Arbno_Y");
    }
} // PE_Arbno_Y

// used by arbno and assignment
function bracket(e, p, a) {
    // e is always PE_R_Enter?
    if (p === EOP) {
	e.pthen = a;
	e.index = 2;
	a.index = 1;
    }
    else {
	e.pthen = p;
	p.set_successor(a);
	e.index = p.index + 2;
	a.index = p.index + 1;
    }
    return e;
} // bracket

export function arbno(p) {
    let pe;
    let patstk;
    if (is_pat(p)) {
	pe = p.p.copy();
	patstk = p.stk;
    }
    else {
	pe = sfv_to_pe('arbno', p); // XXX error won't mention Pattern!
	patstk = 0;
    }
    
    if (patstk === 0 && pe.ok_for_simple_arbno)
	return new Pattern(0, _arbno_simple(pe));

    // This is the complex case, either the pattern makes stack entries
    // or it is possible for the pattern to match the null string (more
    // accurately, we don't know that this is not the case).

    //   +--------------------------+
    //   |                          ^
    //   V                          |
    // +---+                        |
    // | X |---->                   |
    // +---+                        |
    //   .                          |
    //   .                          |
    // +---+     +---+     +---+    |
    // | E |---->| P |---->| Y |--->+
    // +---+     +---+     +---+

    // The node numbering of the constituent pattern P is not affected.
    // Where N is the number of nodes in P,
    // the Y node is N + 1,
    // the E node is N + 2,
    // the X node is N + 3.
    const e = new PE_R_Enter();
    const x = new PE_Arbno_X(0, EOP, e);
    const y = new PE_Arbno_Y(0, x, patstk + 3);
    const epy = bracket(e, pe, y);

    x.alt = epy;
    x.index = epy.index + 1;
    return new Pattern(p.stk + 3, x);
} // arbno

//////////////// assign immediate

// no mixins (MI), so need a function
// would prefer "pattern.imm/onmatch(data)", but it's hard!
function image_match(e, ic) {
    // assert(!first)?

    //ic.append(`.${e.name()}(${e.data()})`);

    const p = ic.refs[e.index-2];
    ic.append(`${e.name()}(`);
    ic.sequence(p, e, true);
    ic.append(`, ${e.data()})`);
}

class PE_Call_Imm extends FuncPE {
    constructor(func) {		// XXX Func1PE?
	super(1, func);
	this.assign = true;	// want class member
    }

    match(m) {
	let stk = m.stack;
	const s = m.slice(stk.peek(stk.base - 1).cursor + 1, m.cursor);
	m.petrace(this, `imm calling ${this.data()} with ${LQ}${s}${RQ}`);
	this.func(s);
	m.pop_region();
	return M_Succeed;
    }

    name() {
	return 'imm';
    }

    image(ic) {
	image_match(this, ic);
    }
}

class PE_Var_Imm extends VarPE {
    constructor(v) {		// XXX Var1PE??
	super(1, v);
    }

    match(m) {
	let stk = m.stack;
	let s = m.slice(stk.peek(stk.base - 1).cursor + 1, m.cursor);
	m.petrace(this, `imm setting var ${this.data()} to ${LQ}${s}${RQ}`);
	// XXX register by name in m.vars object?
	this.v.set(s);
	m.pop_region();
	return M_Succeed;
    }

    name() {
	return 'imm';
    }

    image(ic) {
	image_match(this, ic);
    }
}

//////////////// call/var on match

// This node sets up for the eventual assignment
class PE_Call_OnM extends FuncPE {
    constructor(func) {
	super(1, func);		// XXX Func1PE?
	this.assign = true;	// want class member
    }

    match(m) {
	m.petrace(this, "  registering deferred call");
	m.stack.put_node(m.stack.base - 1, m.node);
	m.push(CP_Assign);
	m.pop_region();
	m.assign_on_match = true;
	return M_Succeed;
    }	

    onmatch(m, str) {
	m.trace(` calling ${this.data()} with ${LQ}${str}${RQ}`);
	this.func(str);
    }

    name() {
	return 'onmatch';
    }

    image(ic) {
	image_match(this, ic);
    }
}

// This node sets up for the eventual assignment
class PE_Var_OnM extends VarPE {
    constructor(v) {		// XXX Var1PE??
	super(1, v);
    }

    match(m) {
	m.petrace(this, "registering deferred assign");
	m.stack.put_node(m.stack.base - 1, m.node);
	m.push(CP_Assign);
	m.pop_region();
	m.assign_on_match = true;
	return M_Succeed;
    }	

    onmatch(m, str) {
	// XXX register by name in m.vars object?
	this.v.set(str);
    }

    name() {
	return 'onmatch';
    }

    image(ic) {
	image_match(this, ic);
    }
}

//////////////// bal

// XXX take open/close arguments, so can be used with other chars?
class PE_Bal extends PE {	// Bal
    match(m) {
	m.petrace(this, "matching or extending bal");
	if (m.cursor >= m.length || m.subject[m.cursor] === ')')
	    return M_Fail;

	if (m.subject[m.cursor] === '(') {
	    let paren_count = 1;
	    for (;;) {
		if (++m.cursor >= m.length)
		    return M_Fail;
		else if (m.subject[m.cursor] === '(')
		    paren_count++;
		else if (m.subject[m.cursor] === ')') {
		    if (--paren_count === 0)
			break;
		}
	    } // forever
	} // open paren
	m.cursor++;		// advance over close paren
	m.push(this);
	return M_Succeed;
    }

    image(ic) {
	ic.append("bal");
    }
}

export const bal = new Pattern(1, new PE_Bal());

//////////////// break

class PE_Break_Set extends SetPE {
    constructor(cset) {		// XXX Set1PE?
	super(1, cset);
    }

    match(m) {
	m.petrace(this, `matching break ${LQ}${this.str}${RQ}`);
	while (m.cursor < m.length && !this.cset.has(m.subject[m.cursor])) {
	    m.cursor++;
	}
	return M_Succeed;
    }

    name() {
	return "breakp";
    }
}

class PE_Break_Var extends VarPE {
    constructor(v) {		// XXX Var1PE?
	super(1, v);
    }

    match(m) {
	const str = this.v.get();
	if (!is_str(str))
	    need_s('breakp', str, this.v);
	m.petrace(this, `matching break (var) ${LQ}${str}${RQ}`);
	const cs = cset(str);
	while (m.cursor < m.length && !cs.has(m.subject[m.cursor])) {
	    m.cursor++;
	}
	return M_Succeed;
    }

    name() {
	return "breakp";
    }
}

class PE_Break_Func extends FuncPE {
    constructor(func) {		// XXX Func1PE?
	super(1, func);
    }

    match(m) {
	let cs = this.func();
	m.petrace(this, `matching break (func) ${LQ}${str}${RQ}`);
	if (is_str(cs))
	    cs = cset(cs)
	else if (!is_set(cs))
	    need_sf('break', cs, this.func);

	// XXX missing trace("matching....")
	while (m.cursor < m.length && !cs.has(m.subject[m.cursor])) {
	    m.cursor++;
	}
	return M_Succeed;
    }

    name() {
	return "breakp";
    }
}

export function breakp(x) {	// Break Pattern
    if (is_str(x))
	return new Pattern(1, new PE_Break_Set(cset(x)));
    else if (is_set(x))
	return new Pattern(1, new PE_Break_Set(x));
    else if (is_var(x))
	return new Pattern(1, new PE_Break_Var(x));
    else if (is_func(x))
	return new Pattern(1, new PE_Break_Func(x));
    else
	need_ssfv('breakp');
}

//////////////// breakx

class PE_BreakX_Set extends SetPE { // breakx (character set case)
    match(m) {
	m.petrace(this, `matching breakx ${LQ}${this.str}${RQ}`);
	while (m.cursor < m.length) {
	    if (this.cset.has(m.subject[m.cursor]))
		return M_Succeed;
	    m.cursor++;
	}
	return M_Fail;
    }

    name() {
	return "breakx";
    }

    inext(ic) {
	return super.inext(ic).pthen; // skip PE_Alt
    }
}

class PE_BreakX_Var extends VarPE { // breakx(var)
    match(m) {
	const str = this.v.get();
	if (!is_str(str))
	    need_s('breakx', str, this.v);
	m.petrace(this, `matching breakx (var) ${LQ}${str}${RQ}`);
	const cs = cset(str);
	while (m.cursor < m.length) {
	    if (cs.has(m.subject[m.cursor]))
		return M_Succeed;
	    m.cursor++;
	}
	return M_Fail;
    }

    name() {
	return "breakx";
    }

    inext(ic) {
	return super.inext(ic).pthen; // skip PE_Alt
    }
}

class PE_BreakX_Func extends FuncPE { // breakx (function case)
    match(m) {
	let cs = this.func();
	m.petrace(this, `matching breakx (func) ${LQ}${cs}${RQ}`);
	if (is_str(cs))
	    cs = cset(cs)
	else if (!is_set(cs))
	    need_sf('breakx', cs, this.func);

	while (m.cursor < m.length) {
	    if (cs.has(m.subject[m.cursor]))
		return M_Succeed;
	    m.cursor++;
	}
	return M_Fail;
    }

    name() {
	return "breakx";
    }
}

// BreakX_X (BreakX extension). See section on "Compound Pattern
// Structures". This node is the alternative that is stacked
// to skip past the break character and extend the break.
class PE_BreakX_X extends PE {
    match(m) {
	m.petrace(this, "extending breakx");
	m.cursor++;
	return M_Succeed;
    }
}


// +---+     +---+
// | B |---->| A |---->
// +---+     +---+
//   ^         .
//   |         .
//   |       +---+
//   +<------| X |
//           +---+

// The B node is numbered 3,
// the alternative node is 1,
// the X node is 2.

export function breakx(arg) { // Breakx Pattern
    let b = null;
    if (is_str(arg))
	b = new PE_BreakX_Set(3, cset(arg));
    else if (is_set(arg))
	b = new PE_BreakX_Set(3, arg);
    else if (is_var(x))
	b = new PE_BreakX_Var(3, arg);
    else if (is_func(arg))
	b = new PE_BreakX_Func(3, arg);
    else
	need_ssfv('breakx');

    let x = new PE_BreakX_X(2, b);
    let a = new PE_Alt(1, EOP, x);
    b.pthen = a;
    return new Pattern(2, b);
}

//////////////// cursor

class PE_Cursor_Func extends FuncPE {    // Cursor assignment
    constructor(func) {		// XXX Func1PE?
	super(1, func);
    }

    match(m) {
	m.petrace(this, `calling ${this.data()} with cursor`);
	this.func(m.cursor);
	return M_Succeed;
    }

    name() {
	return "cursor";
    }
}

class PE_Cursor_Var extends VarPE {    // Cursor assignment (var)
    constructor(v) {		       // XXX Var1PE?
	super(1, v);
    }

    match(m) {
	m.petrace(this, `setting ${this.data()} to ${m.cursor}`);
	this.v.set(m.cursor);
	return M_Succeed;
    }

    name() {
	return "cursor";
    }
}

export function cursor(x) {
    if (is_func(x))
	return new Pattern(0, new PE_Cursor_Func(x));
    if (is_var(x))
	return new Pattern(0, new PE_Cursor_Var(x));
    need_fv('cursor');
}

//////////////// fail

class PE_Fail extends PE {	// Fail
    match(m) {
	m.petrace(this, "matching fail");
	return M_Fail;
    }

    image(ic) {
	ic.append("fail");
    }
}

export const fail = new Pattern(1, new PE_Fail());

//////////////// fence (pattern)

class PE_Fence extends PE {	// fence (built in pattern)
    constructor() {
    	super(1, EOP);
    }

    match(m) {
	m.petrace(this, "matching fence");
	m.push(CP_Abort);
	return M_Succeed;
    }

    image(ic) {
	ic.append("fence");
    }
}

export const fence = new Pattern(1, new PE_Fence());

//////////////// fencef (function)

// Fence function node X. This is the node that gets control
// after a successful match of the fenced pattern.
class PE_Fence_X extends PE {
    match(m) {
	m.petrace(this, "matching fence function");
	let stk = m.stack;
	stk.ptr++;		// XXX check?  HIDE??
	stk.put(stk.ptr, stk.base, CP_Fence_Y);
	stk.set_base(stk.peek(stk.base).cursor);
	m.region_level--;
	return M_Succeed;
    }

    image(ic) {
	// Fixes thanks to Robin Haberkorn
	ic.append('fence(');
	// PC_R_Enter at refs[this.index]
	ic.sequence(ic.refs[this.index].pthen, this, true);
	ic.append(')');
    }
}

// Fence function node Y. This is the node that gets control on
// a failure that occurs after the fenced pattern has matched.
class PE_Fence_Y extends PE {
    match(m) {
	// Note: the Cursor at this stage is actually the inner stack
	// base value. We don't reset this, but we do use it to strip
	// off all the entries made by the fenced pattern.
	m.petrace(this, "pattern matched by fence caused failure");
	m.stack.ptr = m.cursor - 2; // XXX check! HIDE?
	return M_Fail;
    }
}

const CP_Fence_Y = new PE_Fence_Y();

// +---+     +---+     +---+
// | E |---->| P |---->| X |---->
// +---+     +---+     +---+

// The node numbering of the constituent pattern P is not affected.
// Where N is the number of nodes in P,
// the X node is N + 1,
// the E node is N + 2.

export function fencef(pat) {
    const e = new PE_R_Enter();
    const p = pat.p.copy();
    const x = new PE_Fence_X();
    return new Pattern(pat.stk + 1, bracket(e, p, x));
}

//////////////// len

class IntPE extends UnsealedPE {
    constructor(n) {
	super();
	this.n = n;
	this.seal();
    }

    data() {
	return this.n
    }

    image(ic) {
	ic.append(`${this.name()}(${this.n})`);
    }
}

class PE_Len extends UnsealedPE { // len (integer case)
    constructor(n) {
	super(1, EOP, n > 0);	// ok_for_simple_arbno if non-null
	this.n = n;
	this.seal();
    }

    match(m) {
	m.petrace(this, `matching len ${this.n}`);
	if (m.cursor + this.n > m.length)
	    return M_Fail;
	m.cursor += this.n;
	return M_Succeed;
    }

    // not using IntPE because of constructor args
    image(ic) {
	ic.append(`len(${this.n})`);
    }
}

class PE_Len_Func extends FuncPE { // len (function case)
    constructor(func) {		// XXX Func1PE?
	super(1, func);
    }

    match(m) {
	let len = this.func();
	m.petrace(this, `matching len (func) ${len}`);
	if (!is_int(len) || len < 0)
	    need_nni_func('len', len, this.func);
	if (m.cursor + len > m.length)
	    return M_Fail;
	m.cursor += len;
	return M_Succeed;
    }

    name() {
	return "len";
    }
}

class PE_Len_Var extends VarPE { // len (var)
    constructor(v) {		 // XXX Var1PE?
	super(1, v);
    }

    match(m) {
	let len = parseInt(this.v.get()); // XXX .get_int()?
	m.petrace(this, `matching len (var) ${len}`);
	if (len < 0)
	    need_nni_var('len', len, this.v);
	if (m.cursor + len > m.length)
	    return M_Fail;
	m.cursor += len;
	return M_Succeed;
    }

    name() {
	return "len";
    }
}

export function len(x) {
    if (is_int(x)) {
	// Note, the following is not just an optimization, it is needed
	// to ensure that Arbno (Len (0)) does not generate an infinite
	// matching loop (since PC_Len is ok_for_simple_arbno).
	if (x === 0)
	    return new Pattern(0, new PE_Null()); // not ok_for_simple_arbno
	else if (x > 0)
	    return new Pattern(0, new PE_Len(x));
    }
    else if (is_func(x))
	return new Pattern(0, new PE_Len_Func(x));
    else if (is_var(x))
	return new Pattern(0, new PE_Len_Var(x));
    uerror("'len' takes non-negative Number or Function");
}


//////////////// notany

class PE_NotAny_Set extends SetPE {
    constructor(cset) {		// XXX Set1PE
	super(1, cset, true);	// ok_for_simple_arbno
    }

    match(m) {
	m.petrace(this, `matching notany ${LQ}${this.str}${RQ}`);
	if (m.cursor < m.length && !this.cset.has(m.subject[m.cursor])) {
	    m.cursor++;
	    return M_Succeed;
	}
	else
	    return M_Fail;
    }

    name() {
	return "notany";
    }
}

class PE_NotAny_Var extends VarPE {
    constructor(v) {		// XXX Var1PE?
	super(1, v, true);	// ok_for_simple_arbno
    }

    match(m) {
	const str = this.v.get();
	if (!is_str(str))
	    need_s('notany', str, this.v);
	m.petrace(this, `matching notany (var) ${LQ}${str}${RQ}`);
	const cs = cset(str);
	if (m.cursor < m.length && !cs.has(m.subject[m.cursor])) {
	    m.cursor++;
	    return M_Succeed;
	}
	else
	    return M_Fail;
    }

    name() {
	return "notany";
    }
}

class PE_NotAny_Func extends FuncPE {
    constructor(func) {		// XXX Func1PE?
	super(1, func, true);	// ok_for_simple_arbno
    }

    match(m) {
	let cs = this.func();
	m.petrace(this, `matching notany (func) ${LQ}${cs}${RQ}`);
	if (is_str(cs))
	    cs = cset(cs)
	else if (!is_set(cs))
	    need_sf('notany', cs, this.func);

	if (m.cursor < m.length && !cs.has(m.subject[m.cursor])) {
	    m.cursor++;
	    return M_Succeed;
	}
	else
	    return M_Fail;
    }

    name() {
	return "notany";
    }
}

export function notany(x) {
    if (is_str(x))
	return new Pattern(1, new PE_NotAny_Set(cset(x)));
    else if (is_set(x))
	return new Pattern(1, new PE_NotAny_Set(x));
    else if (is_var(x))
	return new Pattern(1, new PE_NotAny_Var(x));
    else if (is_func(x))
	return new Pattern(1, new PE_NotAny_Func(x));
    else
	need_ssd('any');
}

//////////////// nspan (possibly null)

class PE_NSpan_Set extends SetPE {
    constructor(cset) {		// XXX Set1PE
	super(1, cset);
    }

    match(m) {
	m.petrace(this, `matching nspan ${LQ}${this.str}${RQ}`);
	while (m.cursor < m.length && this.cset.has(m.subject[m.cursor])) {
	    m.cursor++;
	}
	return M_Succeed;
    }

    name() {
	return "nspan";
    }
}

class PE_NSpan_Var extends VarPE {
    constructor(v) {		// XXX Var1PE?
	super(1, v);
    }

    match(m) {
	const str = this.v.get();
	if (!is_str(str))
	    need_s('nspan', str, this.v);
	m.petrace(this, `matching nspan (var) ${LQ}${str}${RQ}`);
	const cs = cset(str);
	while (m.cursor < m.length && cs.has(m.subject[m.cursor])) {
	    m.cursor++;
	}
	return M_Succeed;
    }

    name() {
	return "nspan";
    }
}

class PE_NSpan_Func extends FuncPE {
    constructor(func) {		// XXX Func1PE?
	super(1, func);
    }

    match(m) {
	let cs = this.func();
	m.petrace(this, `matching nspan (func) ${LQ}${cs}${RQ}`);
	if (is_str(cs))
	    cs = cset(cs)
	else if (!is_set(cs))
	    need_sf('nspan', cs, this.func);

	while (m.cursor < m.length && cs.has(m.subject[m.cursor])) {
	    m.cursor++;
	}
	return M_Succeed;
    }

    name() {
	return "nspan";
    }
}

export function nspan(x) {
    if (is_str(x))
	return new Pattern(1, new PE_NSpan_Set(cset(x)));
    else if (is_set(x))
	return new Pattern(1, new PE_NSpan_Set(x));
    else if (is_var(x))
	return new Pattern(1, new PE_NSpan_Var(x));
    else if (is_func(x))
	return new Pattern(1, new PE_NSpan_Func(x));
    else
	need_ssfv('nspan');
}

//////////////// pos

class PE_Pos_Int extends IntPE { // rpos(n)
    match(m) {
	m.petrace(this, `matching rpos ${this.n}`);
	if (m.cursor === this.n)
	    return M_Succeed;
	return M_Fail;
    }

    name() {
	return "pos";
    }
}

class PE_Pos_Func extends FuncPE { // pos(func)
    constructor(func) {		// XXX Func1PE?
	super(1, func);
    }

    match(m) {
	let n = this.func();
	m.petrace(this, `matching rpos (func) ${n}`);
	if (n < 0)
	    uerror(`rpos function ${this.func} returned ${n}`);
	if (m.cursor === n)
	    return M_Succeed;
	return M_Fail;
    }

    name() {
	return "pos";
    }
}

class PE_Pos_Var extends VarPE { // pos(var)
    constructor(v) {		 // XXX Var1PE?
	super(1, v);
    }

    match(m) {
	let n = parseInt(this.v.get()); // XXX .get_int()?
	m.petrace(this, `matching rpos (var) ${n}`);
	if (n < 0)
	    uerror(`rpos function ${this.func} returned ${n}`);
	if (m.cursor === n)
	    return M_Succeed;
	return M_Fail;
    }

    name() {
	return "pos";
    }
}

export function pos(n) {
    if (is_func(n))
	return new Pattern(0, new PE_Pos_Func(n));
    if (is_var(n))
	return new Pattern(0, new PE_Pos_Var(n));
    if (is_int(n) && n >= 0)
	return new Pattern(0, new PE_Pos_Int(n));
    need_nnifv('pos', n);
}

//////////////// rpos

class PE_RPos_Int extends IntPE { // pos(n)
    match(m) {
	m.petrace(this, `matching pos ${this.n}`);
	if (m.cursor === m.length - this.n)
	    return M_Succeed;
	return M_Fail;
    }

    name() {
	return "rpos";
    }
}

class PE_RPos_Func extends FuncPE { // pos(func)
    constructor(func) {		// XXX Func1PE?
	super(1, func);
    }

    match(m) {
	let n = this.func();
	m.petrace(this, `matching pos (func) ${n}`);
	if (n < 0)
	    uerror(`pos function ${this.func} returned ${n}`);
	if (m.cursor === m.length - n)
	    return M_Succeed;
	return M_Fail;
    }

    name() {
	return "rpos";
    }
}

class PE_RPos_Var extends VarPE { // pos(var)
    constructor(v) {		  // XXX Var1PE?
	super(1, v);
    }

    match(m) {
	let n = parseInt(this.v.get()); // XXX .get_int()?
	m.petrace(this, `matching pos (var) ${n}`);
	if (n < 0)
	    uerror(`pos function ${this.func} returned ${n}`);
	if (m.cursor === m.length - n)
	    return M_Succeed;
	return M_Fail;
    }

    name() {
	return "rpos";
    }
}

export function rpos(n) {
    if (is_func(n))
	return new Pattern(0, new PE_RPos_Func(n));
    if (is_var(n))
	return new Pattern(0, new PE_RPos_Var(n));
    if (is_int(n) && n >= 0)
	return new Pattern(0, new PE_RPos_Int(n));
    need_nnifv('rpos', n);
}

//////////////// rtab

class PE_RTab_Int extends IntPE { // rtab(n)
    match(m) {
	m.petrace(this, `matching rtab ${this.n}`);
	if (m.cursor <= m.length - this.n) {
	    m.cursor = m.length - this.n;
	    return M_Succeed;
	}
	return M_Fail;
    }

    name() {
	return "rtab";
    }
}

class PE_RTab_Func extends FuncPE { // rtab(func)
    constructor(func) {		// XXX Func1PE?
	super(1, func);
    }

    match(m) {
	let n = this.func();
	m.petrace(this, `matching rtab (func) ${n}`);
	if (n < 0)
	    need_nni_func('rtab', n, this.func);
	if (m.cursor <= m.length - n) {
	    m.cursor = m.length - n;
	    return M_Succeed;
	}
	return M_Fail;
    }

    name() {
	return "rtab";
    }
}

class PE_RTab_Var extends VarPE { // rtab(var)
    constructor(v) {		  // XXX Var1PE?
	super(1, v);
    }

    match(m) {
	let n = parseInt(this.v.get()); // XXX .get_int()?
	m.petrace(this, `matching rtab (var) ${n}`);
	if (n < 0)
	    need_nni_var('rtab', n, this.v);
	if (m.cursor <= m.length - n) {
	    m.cursor = m.length - n;
	    return M_Succeed;
	}
	return M_Fail;
    }

    name() {
	return "rtab";
    }
}

export function rtab(n) {
    if (is_func(n))
	return new Pattern(0, new PE_RTab_Func(n));
    if (is_var(n))
	return new Pattern(0, new PE_RTab_Var(n));
    if (is_int(n) && n >= 0)
	return new Pattern(0, new PE_RTab_Int(n));
    need_nnifv('rtab', n);
}

//////////////// rem

class PE_Rem extends PE {	// Rem
    match(m) {
	m.pe(this, "matching rem");
	m.cursor = m.length;
	return M_Succeed;
    }

    image(ic) {
	ic.append("rem");
    }
}

export const rem = new Pattern(0, new PE_Rem());

//////////////// span

class PE_Span_Set extends SetPE { // XXX Set1PE?
    constructor(cset) {
	super(1, cset, true); // ok_for_simple_arbno
    }

    match(m) {
	let c = m.cursor;
	m.petrace(this, `matching span ${LQ}${this.str}${RQ}`);
	while (c < m.length && this.cset.has(m.subject[c]))
	    c++;
	if (m.cursor !== c) {
	    m.cursor = c;
	    return M_Succeed;
	}
	else
	    return M_Fail;
    }

    name() {
	return "span";
    }
}

class PE_Span_Var extends VarPE {
    constructor(v) {		// XXX Var1PE?
	super(1, v, true);	// ok_for_simple_arbno
    }

    match(m) {
	const str = this.v.get();
	m.petrace(this, "matching span (var) ${LQ}${str}${RQ}");
	if (!is_str(str))
	    need_s('span', str, this.v);
	const cs = cset(str);
	let c = m.cursor;
	while (c < m.length && cs.has(m.subject[c]))
	    c++;
	if (m.cursor !== c) {	// non-empty match?
	    m.cursor = c;	// move cursor
	    return M_Succeed;
	}
	else
	    return M_Fail;
    }

    name() {
	return "span";
    }
}

class PE_Span_Func extends FuncPE {
    constructor(func) {		// XXX Func1PE?
	super(1, func, true);	// ok_for_simple_arbno
    }

    match(m) {
	let cs = this.func();
	m.petrace(this, `matching span (func) ${LQ}${cs}${RQ}`);
	if (is_str(cs))
	    cs = cset(cs)
	else if (!is_set(cs))
	    need_sf('span', cs, this.func);

	let c = m.cursor;
	while (c < m.length && set.has(m.subject[c]))
	    c++;
	if (m.cursor !== c) {	// non-empty match?
	    m.cursor = c;	// move cursor
	    return M_Succeed;
	}
	else
	    return M_Fail;
    }

    name() {
	return "span";
    }
}

export function span(x) {
    if (is_str(x))
	return new Pattern(1, new PE_Span_Set(cset(x)));
    else if (is_set(x))
	return new Pattern(1, new PE_Span_Set(x));
    else if (is_var(x))
	return new Pattern(1, new PE_Span_Var(x));
    else if (is_func(x))
	return new Pattern(1, new PE_Span_Func(x));
    else
	need_ssfv('span');
}

//////////////// succeed

class PE_Succeed extends PE {	// succeed
    match(m) {
	m.petrace(this, "matching 'succeed'");
	m.push(this);
	return M_Succeed;
    }

    name() {
	return "succeed"
    }
}

export const succeed = new Pattern(1, new PE_Succeed());

//////////////// tab

class PE_Tab_Int extends IntPE { // tab(n)
    match(m) {
	m.petrace(this, `matching tab ${this.n}`);
	if (m.cursor <= this.n) {
	    m.cursor = this.n;
	    return M_Succeed;
	}
	return M_Fail;
    }

    name() {
	return "tab";
    }
}

class PE_Tab_Func extends FuncPE { // tab(func)
    constructor(func) {		// XXX Func1PE?
	super(1, func);
    }

    match(m) {
	let n = this.func();
	m.petrace(this, `matching tab (func) ${n}`);
	if (n < 0)
	    need_nni_func('tab', n, this.func);
	if (m.cursor <= n) {
	    m.cursor = n;
	    return M_Succeed;
	}
	return M_Fail;
    }

    name() {
	return "tab";
    }
}

class PE_Tab_Var extends VarPE { // tab(var)
    constructor(v) {		// XXX Var1PE?
	super(1, v);
    }

    match(m) {
	let n = parseInt(this.v.get()); // XXX .get_int()?
	m.petrace(this, `matching tab (var) ${n}`);
	if (n < 0)
	    need_nni_func('tab', n, this.v);
	if (m.cursor <= n) {
	    m.cursor = n;
	    return M_Succeed;
	}
	return M_Fail;
    }

    name() {
	return "tab";
    }
}

export function tab(n) {
    if (is_func(n))
	return new Pattern(0, new PE_Tab_Func(n));
    if (is_var(n))
	return new Pattern(0, new PE_Tab_Var(n));
    if (is_int(n) && n >= 0)
	return new Pattern(0, new PE_Tab_Int(n));
    need_nnifv('tab', n);
}

//////////////// top level and/or

export function and(first, ...rest) {
    if (!is_pat(first))
	first = pat(first);
    return first.and(...rest);
}

export function or(first, ...rest) {
    if (!is_pat(first))
	first = pat(first);
    return first.or(...rest);
}

//////////////// top level onmatch/imm

export function imm(p, arg) {
    if (!is_pat(p))
	p = pat(p);
    return p.imm(arg);
}

export function onmatch(p, arg) {
    if (!is_pat(p))
	p = pat(p);
    return p.onmatch(arg);
}

////////////////////////////////////////////////////////////////

//console.log(STRING_LENGTHS);
