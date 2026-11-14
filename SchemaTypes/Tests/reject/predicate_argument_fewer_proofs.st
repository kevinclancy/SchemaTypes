// Kind error: Keyed expects a predicate requiring a proof of A(x), but Q requires none.
union (A : (a : str) -> prop) =>
union (Q : (a : str) -> prop) =>
type Keyed = (P : (x : str | A(x)) -> prop) => { [k : str] A(k) : { [j : str] P(k) : str } }
in { d : (Keyed Q) }
