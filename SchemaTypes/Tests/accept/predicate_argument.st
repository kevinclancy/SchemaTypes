// A predicate passed as the argument of an index-to-type function.
predicates
    Q(a : str)
end
type Keyed = (P : pred (x : str)) => { [k : str] P(k) : { other : { o : str | P(o) } } }
in { d : (Keyed Q) }
