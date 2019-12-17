// TEMP:
import { pat, is_pat } from "./spipat.mjs";

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
/*
let m = and('a', 'b', 'c').amatch('abc');
console.log(m.matched);

m = and(or('a', 'b', 'c'), 'x').amatch('cx');
console.log(m.matched);
*/