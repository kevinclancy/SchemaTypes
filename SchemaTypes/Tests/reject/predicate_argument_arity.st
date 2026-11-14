// Kind error: Keyed expects a unary predicate, but Q is binary.
union (Q : (a : str, b : str) -> prop) =>
type Keyed = (P : (x : str) -> prop) => { [k : str] P(k) : str }
in { d : (Keyed Q) }
