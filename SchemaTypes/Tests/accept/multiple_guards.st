// A dictionary with two guards, which together supply the proofs that R requires.
union (P : (a : str) -> prop) =>
union (Q : (a : str) -> prop) =>
union (R : (a : str | P(a), Q(a)) -> prop) =>
in { ps : { [x : str] P(x) : "*" }, qs : { [x : str] Q(x) : "*" }, d : { [x : str] P(x), Q(x) : { [y : str] R(x) : { p : { z : str | P(z) } } } } }
