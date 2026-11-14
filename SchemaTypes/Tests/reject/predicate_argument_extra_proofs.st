// Kind error: Q requires a proof that the predicate Keyed expects does not.
union (A : (a : str) -> prop) =>
union (Q : (a : str | A(a)) -> prop) =>
type Keyed = (P : (x : str) -> prop) => { [k : str] P(k) : str }
in { d : (Keyed Q) }
