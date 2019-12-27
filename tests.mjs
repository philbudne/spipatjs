// -*-javascript-*-

// XXX test rem, pos, fence pat(Var)
// XXX test backtrack w/ fail, abort, breakx -- split.js
// XXX test functions, Vars as arguments to and/or
// XXX test (not)any, (n)span, break(p|x) w/ Var
// XXX test (r)pos, (r)tab, len w/ Function, Var
// XXX test arbno with string, function, variable

import {
    abort,
    and,
    any,
    arb,
    arbno,
    bal,
    breakp,
    breakx,
    cursor,
    fail,
    len,
    notany,
    nspan,
    or,
    pat,
    rpos,
    span,
    tab,
    rtab,

    Var,
    LQ,
    RQ
} from "./spipat.mjs";

////////////////////////////////////////////////////////////////
// tests

const deb = false;

let tests = 0;
let ok = 0;
let err = 0;

// return file:line:char from n'th line in Error().stack output
function get_caller(err, n) {
    const trace = err.stack.split("\n");
    let str = trace[n];

    const op = str.lastIndexOf("(");
    // want breakx('(').and('(', break(')').onmatch(vx))!!
    if (op > 0)
	str = str.substring(op + 1,
			    str.lastIndexOf(")"));

    str = str.replace('\s+at ');
    return str;
}

function stderr_putc(c) {
    if (process && process.stdout)
	process.stderr.write(c);
}

// this MUST be called (directly) by a "check" function
function test_err(msg) {
    stderr_putc('X');
    console.log(msg);
    console.log(get_caller(new Error(), 3));
}

function passed() {
    ok++;
    stderr_putc('.');
}

function check(m, expect) {
    tests++;
    if (expect && m === null) {
	test_err(`expecting ${LQ}${expect}${RQ}, but failed`);
    }
    else if (expect === null) {
	if (m !== null) {
	    test_err(`expecting failure, but matched ${LQ}${m.matched}${RQ}`);
	}
	else
	    passed();
    }
    else if (m.matched !== expect) {
	test_err(`expecting ${LQ}${expect}${RQ}, but matched ${LQ}${m.matched}${RQ}`);
    }
    else
	passed();
}

function checkval(v, expect) {
    tests++;
    if (v === expect)
	passed();
    else
	test_err(`expecting ${LQ}${expect}${RQ} got ${LQ}${v}${RQ}`);
}

function imgcheck(p, expect) {
    tests++;
    //spipat.print_nodes(p.p.ref_array())
    let v = p.toString();
    if (v === expect)
	passed();
    else {
	test_err('imgcheck failed');
	console.log(`expecting ${LQ}${expect}${RQ}`);
        console.log(`      got ${LQ}${v}${RQ}`);
	//spipat.print_nodes(p.p.ref_array())
	//spipat.print_dot(p.p.ref_array())
    }
}

const apat = any('123' +  "😀😀😀");
imgcheck(apat, 'any("123😀")');
check(apat.amatch('123', deb), '1');
check(apat.amatch("😀😀😀", deb), '😀');

const bpat = breakp('123' +  "😀😀😀");
imgcheck(bpat, 'breakp("123😀")')
check(bpat.amatch('hello🌎1', deb), 'hello🌎');
check(bpat.amatch('hello🌎😀', deb), 'hello🌎');

const nspat = nspan('123' +  "😀😀😀");
imgcheck(nspat, 'nspan("123😀")')
check(nspat.amatch('321xyz', deb), '321');
check(nspat.amatch("😀😀😀zzz", deb), '😀😀😀');

// test concatenation:
const cpat = and(any('123'), any('456'));
imgcheck(cpat, 'and(any("123"), any("456"))')
check(cpat.amatch('167', deb), '16');

const cpat2 = and('1', '2', '3');
imgcheck(cpat2, 'and("1", "2", "3")')
check(cpat2.amatch('123', deb), '123');

// test strings, concatenation:
const strpat = pat("hello");
imgcheck(strpat, 'pat("hello")')
check(strpat.amatch("hello world", deb), 'hello')

const strpat2 = and("hello", " world");
imgcheck(strpat2, 'and("hello", " world")')
check(strpat2.amatch("hello world", deb), 'hello world');
// test match failure
checkval(strpat2.amatch("hello moon", deb), null);

const strpat3 = and("hello", " world");
imgcheck(strpat3, 'and("hello", " world")')
check(strpat3.amatch("hello world", deb), 'hello world');

const strpat4 = pat("hello world"); // too long for special case
imgcheck(strpat4, 'pat("hello world")')
check(strpat4.amatch("hello world", deb), 'hello world');

//// function
const fpat = pat(function () { return "foo"; });
imgcheck(fpat, 'pat(function () { return "foo"; })')
check(fpat.amatch("foo", deb), 'foo');

//// test unanchored match:
check(strpat.umatch('      hello world     ', deb), 'hello');
check(strpat2.umatch('      hello world     ', deb), 'hello world');
check(strpat3.umatch('      hello world     ', deb), 'hello world');

//// call on match
let v;
function set_v(x) {
    v = x;
}

const aspat = strpat.onmatch(set_v);
//imgcheck(aspat, 'pat("hello").onmatch(set_v)')
imgcheck(aspat, 'onmatch("hello", set_v)')
check(aspat.umatch('   hello world   ', deb), 'hello');
checkval(v, 'hello')

const aspat2 = aspat.and(" world");
//imgcheck(aspat2, 'pat("hello").onmatch(set_v).and(" world")')
imgcheck(aspat2, 'and(onmatch("hello", set_v), " world")');
check(aspat2.umatch('   hello world   ', deb), 'hello world');
checkval(v, 'hello')

// full pattern will not match, so assign on match should not occur
const aspat3 = aspat.and(" goodbye");
//imgcheck(aspat3, 'pat("hello").onmatch(set_v).and(" goodbye")')
imgcheck(aspat3, 'and(onmatch("hello", set_v), " goodbye")');
v = null;
checkval(aspat3.umatch('   hello world   ', false), null);
checkval(v, null);

//// set vars on match

let vv = new Var('vv');
const asvpat = strpat.onmatch(vv);
//imgcheck(asvpat, 'pat("hello").onmatch(Var("vv"))')
imgcheck(asvpat, 'onmatch("hello", Var("vv"))');
var m = asvpat.umatch('   hello world   ', deb);
check(m, 'hello');
checkval(vv.get(), 'hello')

vv.set(null);
checkval(vv.get(), null)
const asvpat2 = asvpat.and(" world");
//imgcheck(asvpat2, 'pat("hello").onmatch(Var("vv")).and(" world")')
imgcheck(asvpat2, 'and(onmatch("hello", Var("vv")), " world")');
m = asvpat2.umatch('   hello world   ', deb);
check(m, 'hello world');
checkval(vv.get(), 'hello')

//// immediate call

const iaspat = strpat.imm(set_v);
//imgcheck(iaspat, 'pat("hello").imm(set_v)')
imgcheck(iaspat, 'imm("hello", set_v)');
check(iaspat.umatch('   hello world   ', deb), 'hello');
checkval(v, 'hello')

// larger full match
const iaspat2 = iaspat.and(" world");
//imgcheck(iaspat2, 'pat("hello").imm(set_v).and(" world")')
imgcheck(iaspat2, 'and(imm("hello", set_v), " world")');
v = null;
check(iaspat2.umatch('   hello world   ', deb), 'hello world');
checkval(v, 'hello')

// full pattern will not match, but immediate assign should occur
const iaspat3 = iaspat.and(" goodbye");
//imgcheck(iaspat3, 'pat("hello").imm(set_v).and(" goodbye")')
imgcheck(iaspat3, 'and(imm("hello", set_v), " goodbye")');
v = null;
checkval(iaspat3.umatch('   hello world   ', deb), null);
checkval(v, 'hello');

// immediate var set
const iasvpat = strpat.imm(vv);
//imgcheck(iasvpat, 'pat("hello").imm(Var("vv"))')
imgcheck(iasvpat, 'imm("hello", Var("vv"))');
check(iasvpat.umatch('   hello world   ', deb), 'hello');
checkval(vv.get(), 'hello')

// full pattern will not match, but immediate assign should occur
vv.set(null);
checkval(vv.get(), null)
const iasvpat3 = iasvpat.and(" goodbye");
//imgcheck(iasvpat3, 'pat("hello").imm(Var("vv")).and(" goodbye")')
imgcheck(iasvpat3, 'and(imm("hello", Var("vv")), " goodbye")');
checkval(iasvpat3.umatch('   hello world   ', deb), null);
checkval(vv.get(), 'hello');

//// alternation
const alpat1 = pat('day').or('night');
//imgcheck(alpat1, 'pat("day").or("night")')
imgcheck(alpat1, 'or("day", "night")');
check(alpat1.amatch('day', deb), 'day');
check(alpat1.amatch('night', deb), 'night');

const alpat2 = pat('good ').and(alpat1);
//imgcheck(alpat2, 'pat("good ").and(pat("day").or("night"))')
imgcheck(alpat2, 'and("good ", or("day", "night"))');
check(alpat2.amatch('good day', deb), 'good day');
check(alpat2.amatch('good night', deb), 'good night');

const alpat3 = alpat1.and(' job');
//imgcheck(alpat3, 'pat("day").or("night").and(" job")')
imgcheck(alpat3, 'and(or("day", "night"), " job")');
check(alpat3.amatch('day job', deb), 'day job');
check(alpat3.amatch('night job', deb), 'night job');

const alpat4 = pat('1').or('2', '3');
//imgcheck(alpat4, 'pat("1").or("2", "3")')
//imgcheck(alpat4, 'pat("1").or("2").or("3")')
imgcheck(alpat4, 'or(or("1", "2"), "3")');
check(alpat4.amatch('1', deb), '1');
check(alpat4.amatch('2', deb), '2');
check(alpat4.amatch('3', deb), '3');

const alpat5 = pat('1').or('2').or('3');
//imgcheck(alpat5, 'pat("1").or("2", "3")') // !!
//imgcheck(alpat5, 'pat("1").or("2").or("3")')
imgcheck(alpat5, 'or(or("1", "2"), "3")');
check(alpat5.amatch('1', deb), '1');
check(alpat5.amatch('2', deb), '2');
check(alpat5.amatch('3', deb), '3');

const alpat6 = alpat1.and(alpat5);
//imgcheck(alpat6, 'pat("day").or("night").and(pat("1").or("2", "3"))')
//imgcheck(alpat6, 'pat("day").or("night").and(pat("1").or("2").or("3"))')
imgcheck(alpat6, 'and(or("day", "night"), or(or("1", "2"), "3"))')

// replacement
const rpat = pat('🌎');
imgcheck(rpat, 'pat("🌎")')
const rmatch = rpat.umatch('hello 🌎!', deb);
checkval(rmatch.replace('world'), 'hello world!');

// arb
const arbpat1 = pat('a').and(arb, pat('z'));
//imgcheck(arbpat1, 'pat("a").and(arb, "z")')
imgcheck(arbpat1, 'and("a", arb, "z")');
check(arbpat1.amatch('abcedfghijklmnopqrstuvwxyz', deb),
      'abcedfghijklmnopqrstuvwxyz');

const arbpat2 = arb.and('z');
//imgcheck(arbpat2, 'arb.and("z")')
imgcheck(arbpat2, 'and(arb, "z")')
check(arbpat2.amatch('z', deb), 'z')
check(arbpat2.amatch('az', deb), 'az')
check(arbpat2.amatch('abcz', deb), 'abcz')
checkval(arbpat2.amatch('abc', deb), null)

// arbno
const arbnpat1 = arbno('z').and('y');
//imgcheck(arbnpat1, 'arbno("z").and("y")')
imgcheck(arbnpat1, 'and(arbno("z"), "y")');
check(arbnpat1.amatch('zzzy', false), 'zzzy');

const arbnpat2 = pat('xy').and(arbno(pat('z')), 'y');
//imgcheck(arbnpat2, 'pat("xy").and(arbno("z"), "y")')
imgcheck(arbnpat2, 'and("xy", arbno("z"), "y")');
check(arbnpat2.amatch('xyzzy', deb), 'xyzzy');

const arbnpat3 = pat('b').and(arbno(any('an')), '!');
//imgcheck(arbnpat3, 'pat("b").and(arbno(any("an")), "!")')
imgcheck(arbnpat3, 'and("b", arbno(any("an")), "!")')
check(arbnpat3.amatch('b!', deb), 'b!');
check(arbnpat3.amatch('banana!', deb), 'banana!');
check(arbnpat3.amatch('bananana!', deb), 'bananana!');

// non-simple argument
const arbnpat4 = pat('b').and(arbno(pat('a').or('n')), '!');
//imgcheck(arbnpat4, 'pat("b").and(arbno(pat("a").or("n")), "!")')
imgcheck(arbnpat4, 'and("b", arbno(or("a", "n")), "!")')
check(arbnpat4.amatch('b!', deb), 'b!');
check(arbnpat4.amatch('banana!', deb), 'banana!');
check(arbnpat4.amatch('bananana!', deb), 'bananana!');

// must not loop!
const arbnpat5 = pat('xy').and(arbno(''), 'z');
//imgcheck(arbnpat5, 'pat("xy").and(arbno(pat("")), "z")')
imgcheck(arbnpat5, 'and("xy", arbno(pat("")), "z")')
check(arbnpat5.amatch('xyz', false), 'xyz');

// must not loop!
const arbnpat6 = pat('xy').and(len(0), 'z');
//imgcheck(arbnpat6, 'pat("xy").and("", "z")')
imgcheck(arbnpat6, 'and("xy", "", "z")')
check(arbnpat6.amatch('xyz', false), 'xyz');

// notany
const nanpat = any('abc').and(notany('abc'));
//imgcheck(nanpat, 'any("abc").and(notany("abc"))')
imgcheck(nanpat, 'and(any("abc"), notany("abc"))')
check(nanpat.amatch('ax', deb), 'ax');

const orpat = pat('yes').or('no').or('maybe');
//imgcheck(orpat, 'pat("yes").or("no", "maybe")')
//imgcheck(orpat, 'pat("yes").or("no").or("maybe")')
imgcheck(orpat, 'or(or("yes", "no"), "maybe")')
check(orpat.amatch('yes', deb), 'yes');
check(orpat.amatch('no', deb), 'no');
check(orpat.amatch('maybe', deb), 'maybe');
checkval(orpat.amatch('foo', deb), null);

const orpat2 = pat('yes').or('no', 'maybe');
//imgcheck(orpat2, 'pat("yes").or("no", "maybe")')
//imgcheck(orpat2, 'pat("yes").or("no").or("maybe")')
imgcheck(orpat2, 'or(or("yes", "no"), "maybe")')
check(orpat2.amatch('yes', deb), 'yes');
check(orpat2.amatch('no', deb), 'no');
check(orpat2.amatch('maybe', deb), 'maybe');
checkval(orpat2.amatch('foo', deb), null);

// abort
const abpat = pat('yes').or(pat('no').and(abort));
//imgcheck(abpat, 'pat("yes").or(pat("no").and(abort))')
imgcheck(abpat, 'or("yes", and("no", abort))');
check(abpat.amatch('yes', deb), 'yes');
checkval(abpat.amatch('no', deb), null);

// span
const sppat1 = pat('b').and(span('an'));
//imgcheck(sppat1, 'pat("b").and(span("an"))')
imgcheck(sppat1, 'and("b", span("an"))')
check(sppat1.amatch('banana', deb), 'banana');
checkval(sppat1.amatch('b', deb), null);

// nspan
const nsppat1 = pat('b').and(nspan('an'));
//imgcheck(nsppat1, 'pat("b").and(nspan("an"))')
imgcheck(nsppat1, 'and("b", nspan("an"))')
check(nsppat1.amatch('banana', deb), 'banana');
check(nsppat1.amatch('b', deb), 'b');

// pattern returned by function
const pfpat = pat('hello ').and(() => pat('world'));
//imgcheck(pfpat, 'pat("hello ").and(() => pat(\'world\'))')
imgcheck(pfpat, 'and("hello ", () => pat(\'world\'))')
check(pfpat.amatch('hello world', deb), 'hello world');

const pfpat2 = pat(() => 'hello ').and(() => pat('world'));
//imgcheck(pfpat2, 'pat(() => \'hello \').and(() => pat(\'world\'))')
imgcheck(pfpat2, 'and(() => \'hello \', () => pat(\'world\'))')
check(pfpat2.amatch('hello world', deb), 'hello world');

// bool returned by function
const pbpat1 = pat('hello ').and(() => true);
//imgcheck(pbpat1, 'pat("hello ").and(() => true)')
imgcheck(pbpat1, 'and("hello ", () => true)')
check(pbpat1.amatch('hello world', deb), 'hello ');

const pbpat2 = pat('hello ').and(() => false);
//imgcheck(pbpat2, 'pat("hello ").and(() => false)')
imgcheck(pbpat2, 'and("hello ", () => false)')
checkval(pbpat2.amatch('hello world', deb), null);

const pbpat3 = pat(() => true).and('hello ');
//imgcheck(pbpat3, 'pat(() => true).and("hello ")')
imgcheck(pbpat3, 'and(() => true, "hello ")')
check(pbpat3.amatch('hello world', deb), 'hello ');

// bal:
check(bal.amatch("()", deb), "()");
imgcheck(bal, 'bal')
checkval(bal.amatch(")()", deb), null);
checkval(bal.amatch(")(", deb), null);
checkval(bal.amatch("(", deb), null);
checkval(bal.amatch("(()", deb), null);
check(bal.amatch("(foo + bar)", deb), "(foo + bar)");
check(bal.amatch("(1 / (x + 2))", deb), "(1 / (x + 2))");

// fail
const failpat = pat('yes').or(pat('no').and(fail));
//imgcheck(failpat, 'pat("yes").or(pat("no").and(fail))')
imgcheck(failpat, 'or("yes", and("no", fail))')
check(failpat.amatch('yes', deb), 'yes');
checkval(failpat.amatch('no', deb), null);

// breakx
const bxpat = breakx('z')
imgcheck(bxpat, 'breakx("z")');
check(bxpat.amatch('z', deb), '')
check(bxpat.amatch('abcz', deb), 'abc')

// cursor
const ccc = []
const curpat = arb.and(cursor((x) => ccc.push(x)), 'z');
check(curpat.amatch('abcxyz', deb), 'abcxyz');
//imgcheck(curpat, 'arb.and(cursor((x) => ccc.push(x)), "z")');
imgcheck(curpat, 'and(arb, cursor((x) => ccc.push(x)), "z")');
checkval(ccc.join(','), '0,1,2,3,4,5');

// len
imgcheck(len(123), 'len(123)');
check(len(5).amatch("hello world", deb), "hello");
// NOTE!! tests proper "explode" of pairs!!
check(len(3).amatch("😀😀😀", deb), "😀😀😀");

// rpos
const rpospat = len(3).and(rpos(0));
//imgcheck(rpospat, 'len(3).and(rpos(0))')
imgcheck(rpospat, 'and(len(3), rpos(0))')
check(rpospat.amatch("😀😀😀", deb), "😀😀😀");

// image tests
imgcheck(arbno("x"), 'arbno("x")')
imgcheck(pat("x"), 'pat("x")')
imgcheck(pat("x").imm((x) => {}),
	 'imm("x", (x) => {})')
imgcheck(pat("x").or("y").imm((x) => {}),
	 'imm(or("x", "y"), (x) => {})');
imgcheck(pat("x").or("y", "z").imm((x) => {}),
	 'imm(or(or("x", "y"), "z"), (x) => {})')
imgcheck(pat("x").or("y", "z").imm((x) => {}),
	 'imm(or(or("x", "y"), "z"), (x) => {})');
imgcheck(pat("x").and("y", "z").imm((x) => {}),
	 'imm(and("x", "y", "z"), (x) => {})');

const imgpat1 = pat("x").and("y", "z").or("a").and("b");
//imgcheck(imgpat1, 'pat("x").and("y", "z").or("a").and("b")')
imgcheck(imgpat1, 'and(or(and("x", "y", "z"), "a"), "b")');
check(imgpat1.amatch("ab", deb), "ab")
check(imgpat1.amatch("xyzb", deb), "xyzb")

const imgpat2 = pat("1").and("23", "456").or(pat("7890").and("abcde"));
//imgcheck(imgpat2, 'pat("1").and("23", "456").or(pat("7890").and("abcde"))'); // XXX reversed
imgcheck(imgpat2, 'or(and("1", "23", "456"), and("7890", "abcde"))');
check(imgpat2.amatch("123456", deb), "123456")
check(imgpat2.amatch("7890abcde", deb), "7890abcde")

const imgpat3 = pat("1").and("23", "456").or(pat("7890").and("abcde"), arb);
//imgcheck(imgpat3, 'pat("1").and("23", "456").or(pat("7890").and("abcde"), arb)');
//imgcheck(imgpat3, 'pat("1").and("23", "456").or(pat("7890").and("abcde")).or(arb)');
imgcheck(imgpat3, 'or(or(and("1", "23", "456"), and("7890", "abcde")), arb)');

const imgpat4 = pat("7890").and("abcde").or(arb);
//imgcheck(imgpat4, 'pat("7890").and("abcde").or(arb)'); // XXX reversed
imgcheck(imgpat4, 'or(and("7890", "abcde"), arb)');

// recursive pattern
const recurse1 = pat('a').or(pat('b').and(() => recurse1));
//imgcheck(recurse1, 'pat("a").or(pat("b").and(() => recurse1))');
imgcheck(recurse1, 'or("a", and("b", () => recurse1))');
check(recurse1.amatch('a', deb), 'a');
check(recurse1.amatch('ba', deb), 'ba');
check(recurse1.amatch('bbbba', deb), 'bbbba');

const qvar = new Var('quote');
const qstr1v = any('"' + "'").imm(qvar).and(breakp(qvar), pat(qvar)); // XXX direct var!!!
imgcheck(qstr1v, 'and(imm(any("\\"\'"), Var("quote")), breakp(Var("quote")), PE_Var(Var("quote")))');
check(qstr1v.amatch("'abc'", deb), "'abc'");
checkval(qvar.get(), "'");
qvar.set('');
checkval(qvar.get(), "");
check(qstr1v.amatch('"abc"', deb), '"abc"');
checkval(qvar.get(), '"');

const tvar = new Var('t');
const tabpat1 = tab(1).and(rtab(5).onmatch(tvar));
//imgcheck(tabpat1, 'tab(1).and(rtab(5).onmatch(Var("t")))');
imgcheck(tabpat1, 'and(tab(1), onmatch(rtab(5), Var("t")))');
check(tabpat1.amatch("0123456789"), "01234");
checkval(tvar.get(), "1234");
tvar.set('');

const tabpat2 = tab(1).and(rtab(1).onmatch(tvar));
//imgcheck(tabpat2, 'tab(1).and(rtab(1).onmatch(Var("t")))');
imgcheck(tabpat2, 'and(tab(1), onmatch(rtab(1), Var("t")))');
check(tabpat2.amatch("0123456789"), "012345678");
checkval(tvar.get(), "12345678");

/* XXX TODO:
let m = and('a', 'b', 'c').amatch('abc');
console.log(m.matched);

m = and(or('a', 'b', 'c'), 'x').amatch('cx');
console.log(m.matched);
*/

//================
stderr_putc('\n');
console.log(`${tests} tests: ${ok} ok`);
if (ok == tests)
    process.exit(0);
else
    process.exit(1);
