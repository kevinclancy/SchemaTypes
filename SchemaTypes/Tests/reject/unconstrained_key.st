// Code generation error: the only dictionary keyed by R has a key x that no proof
// constrains, so we cannot tell where to look R(z) up.
predicates
    Q(a : str)
    R(a : str)
end
in {
  d : { [c : str] Q(c) : { [x : str] Q(c) : { [y : str] R(y) : "*" } } },
  e : { [c : str] Q(c) : { r : { z : str | R(z) } } }
}
