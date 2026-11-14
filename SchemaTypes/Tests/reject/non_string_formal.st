// Parse error: the string section of a predicate sort only admits string sorts.
union (Q : (a : str) -> prop) =>
union (R : (a : prf Q(b)) -> prop) =>
in { d : str }
