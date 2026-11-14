// A dictionary with two guards, which together supply the proofs that R requires.
predicates
    P(a : str)
    Q(a : str)
    R(a : str | P(a), Q(a))
end
in { ps : { [x : str] P(x) : "*" }, qs : { [x : str] Q(x) : "*" }, d : { [x : str] P(x), Q(x) : { [y : str] R(x) : { p : { z : str | P(z) } } } } }
