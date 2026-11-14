// Kind error: Keyed expects a unary predicate, but Q is binary.
predicates
    Q(a : str, b : str)
end
type Keyed = (P : pred (x : str)) => { [k : str] P(k) : str }
in { d : (Keyed Q) }
