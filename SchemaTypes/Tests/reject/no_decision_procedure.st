// Code generation error: no dictionary is keyed by P, so nothing decides P(z).
union (P : (a : str) -> prop) =>
in { d : { p : { z : str | P(z) } } }
