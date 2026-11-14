// Kind error: Keyed expects a predicate requiring a proof of A(x), but Q requires none.
predicates
    A(a : str)
    Q(a : str)
end
type Keyed = (P : pred (x : str | A(x))) => { [k : str] A(k) : { [j : str] P(k) : str } }
in { d : (Keyed Q) }
