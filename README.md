# spipatjs

This is a native (re)implementation of SNOBOL4/SPITBOL pattern
matching for ES6 (JavaScript) which is fully Unicode compatible.

In SNOBOL4, PATTERN is a fundamental data type that can be composed.
Matching is non-greedy, backtracking is used to progressively match
larger prefixes.

## Primative Patterns

The following primative Patterns are available as const variables:

### abort

Immediately aborts the entire pattern match, signalling
failure. This is a specialized pattern element, which is
useful in conjunction with some of the special pattern
elements that have side effects.

### arb

Matches any string. First it matches the null string, and
then on a subsequent failure, matches one character, and
then two characters, and so on. It only fails if the
entire remaining string is matched.

### bal

Matches a non-empty string that is parentheses balanced
with respect to ordinary () characters. Examples of
balanced strings are "ABC", "A((B)C)", and "A(B)C(D)E".
Bal matches the shortest possible balanced string on the
first attempt, and if there is a subsequent failure,
attempts to extend the string.

### fail

The null alternation. Matches no possible strings, so it
always signals failure. This is a specialized pattern
element, which is useful in conjunction with some of the
special pattern elements that have side effects.

### fence

Matches the null string at first, and then if a failure
causes alternatives to be sought, aborts the match (like
abort). Note that using fence at the start of a pattern
has the same effect as matching in anchored mode.

### rem

Matches from the current point to the last character in
the string. This is a specialized pattern element, which
is useful in conjunction with some of the special pattern
elements that have side effects.

### succeed

Repeatedly matches the null string (it is equivalent to
the alternation null.or(null, .....))
pattern element, which is useful in conjunction with some
of the special pattern elements that have side effects.

## Pattern contruction functions

### pat(SF)

Takes a String to match, or a function taking no arguments
that returns a string or pattern (to match) or a boolean
(which, if true matches the null string, and if false fails)
and returns a Pattern.

### cset(S)

Takes a String and returns a (possibly optimized) character set
representing the Unicode characters in the string.

### any(SSF)

Takes a String, cset, or Function (returning a String or cset).  Matches
a single character that is any one of the characters in the String or
Set.  Fails if the current character is not one of the given set of
characters.

### arbno(P)

Where P is any pattern, matches any number of instances
of the pattern, starting with zero occurrences. It is
thus equivalent to
```
null = pat('')
null.or(P.and(null.or(P.and(null.or( ....)))))
```

The pattern P may contain any number of pattern elements
including the use of alternation and concatenation.

### breakp(SSF)

Where SSF is a String, cset, or Function returning a String or cset,
matches a string of zero or more characters up to but not including a
break character that is one of the characters given in the string S.
Can match the null string, but cannot match the last character in the
string, since a break character is required to be present.

### breakx(SSF)

Where SSF is a String, cset, or Function behaves exactly like breakp(SSF)
when it first matches, but if a string is successfully matched, then a
subsequent failure causes an attempt to extend the matched string.

### cursor(F)

Calls function F with a one-based integer cursor position, defined as
the count of characters that have been matched so far (including any
start point moves).

### fencef(P)

Where P is a pattern, attempts to match the pattern P including trying
all possible alternatives of P. If none of these alternatives
succeeds, then the fencef pattern fails. If one alternative succeeds,
then the pattern match proceeds, but on a subsequent failure, no
attempt is made to search for alternative matches of P. The pattern P
may contain any number of pattern elements including the use of
alternation and concatenation.

### len(NF)

Where N is a positive integer (or Function returning one), matches the
given number of characters. For example, Len(10) matches any string
that is exactly ten characters long.

### notany(SSF)

Where S is a String, cset, or Function returning a String or cset,
matches a single character that is not one of the characters.
Fails if the current character is one of the given set of
characters.

### nspan(SSF)

Where SSF is a String, yadda, yadda, matches a string of zero or more
characters that is among the characters given in the string. Always
matches the longest possible such string.  Always succeeds, since it
can match the null string.

### pos(NF)

Where NF is a positive integer (or Function), matches the null string
if exactly N characters have been matched so far, and otherwise fails.

### rpos(NF)

Where NF is a positive integer (or Function yadda yadda), matches the null
string matches the null string if exactly N characters remain to be
matched, and otherwise fails.


### rtab(NF)

Where NF is a positive integer (or Function), matches
characters from the current position until exactly N characters remain
to be matched in the string. Fails if fewer than N unmatched
characters remain in the string.

### tab(NF)

Where NF is a positive integer (or Function), matches from
the current position until exactly N characters have
been matched in all. Fails if more than N characters
have already been matched.

### span(SSF)

Where SSF is a String, cset, or Function, matches a string of one or more
characters that is among the characters given.
Always matches the longest possible such string.
Fails if the current character is not one of the given
set of characters.

## Pattern object

### Pattern object methods:

#### amatch(SUBJECT[, DEBUG])

Attempts an "anchored" match against the String SUBJECT.
If DEBUG is true, uses console.log to trace the match.
Returns a Match object on success,
or null on failure.

#### and(...)

Takes any number of Pattern, String or Function arguments
and returns a new Pattern which is a concatenation of
all of the arguments.

#### imm(F)

Takes a Function with one argument, and returns a new Pattern.
Each time the original Pattern matches, the Function will
be called with the matching string.

#### onmatch(F)

Takes a Function with one argument, and returns a new Pattern.
If the entire Pattern match succeeds, 
the Function will be called with each matching string.

#### or(...)

Takes any number of Pattern, String or Function arguments
and returns a Pattern which matches any of the Patterns

#### umatch(SUBJECT[, DEBUG])

Attempts an "unanchored" match against the String SUBJECT.  If DEBUG
is true, uses console.log to trace the match.  If the match fails,
successive attempts are made to match the given pattern each character
of the subject string until a match succeeds, or until all
possibilities have failed.  Returns a Match object on success,
or null on failure.

## Match object

### Match object members

#### matched

The String matched by the Pattern.

#### start

The number of characters before the matched string

#### stop

The total number of characters from the start
of the SUBJECT string to the end of the match.

### Match object methods

#### replace(REPL)

Returns the SUBJECT String with the matched
string replaced by the REPL String.

## Recursive Patterns

A Function returning a Pattern can be used to create
a recursive Pattern:

```
var P = pat('A').or(pat('B').and(() => P));
```

On the first attempt, this pattern attempts to match the string "A".
If this fails, then the alternative matches a "B", followed by an
attempt to match P again. This second attempt first attempts to
match "A", and so on. The result is a pattern that will match a
string of B's followed by a single A.

This particular example could simply be written as nspan('B').and('A')
but the use of recursive patterns in the general case can construct
complex patterns which could not otherwise be built.
