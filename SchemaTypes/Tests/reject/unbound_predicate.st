// Kind error: Q is not bound.
predicates
    P(a : str)
end
in { d : { [x : str] Q(x) : str }, e : { [y : str] P(z) : str } }
