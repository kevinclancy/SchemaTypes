// A predicate passed as the argument of an index-to-type function.
union (Q : (a : str) -> prop) =>
type Keyed = (P : (x : str) -> prop) => { [k : str] P(k) : { other : { o : str | P(o) } } }
in { d : (Keyed Q) }
