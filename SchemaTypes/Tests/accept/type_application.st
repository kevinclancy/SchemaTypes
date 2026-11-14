// Type-to-type functions applied with !.
predicates
    Q(a : str)
end
type Keyed = (V :: *) => { [k : str] Q(k) : V }
in { d : (Keyed !{ name : str }), e : (Keyed !{ o : str | Q(o) }) }
