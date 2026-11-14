// Type-to-type functions applied with !.
union (Q : (a : str) -> prop) =>
type Keyed = (V :: *) => { [k : str] Q(k) : V }
in { d : (Keyed !{ name : str }), e : (Keyed !{ o : str | Q(o) }) }
