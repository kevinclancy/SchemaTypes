// Parse error: the string section of a predicate sort only admits string sorts.
predicates
    Q(a : str)
    R(a : prf Q(b))
end
in { d : str }
