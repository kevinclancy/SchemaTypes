// Kind error: the proof of P(x) is about the outer x, but R is applied to the inner x.
predicates
    P(a : str)
    Q(a : str)
    R(a : str | P(a))
end
in { d : { [x : str] P(x) : { [x : str] Q(x) : { r : { y : str | R(x) } } } } }
