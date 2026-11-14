// Code generation error: no dictionary is keyed by P, so nothing decides P(z).
predicates
    P(a : str)
end
in { d : { p : { z : str | P(z) } } }
