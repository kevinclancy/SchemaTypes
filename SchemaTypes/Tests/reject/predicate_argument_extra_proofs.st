// Kind error: Q requires a proof that the predicate Keyed expects does not.
predicates
    A(a : str)
    Q(a : str | A(a))
end
type Keyed = (P : pred (x : str)) => { [k : str] P(k) : str }
in { d : (Keyed Q) }
