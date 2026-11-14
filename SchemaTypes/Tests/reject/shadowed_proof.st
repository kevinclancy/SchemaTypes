// Kind error: the proof of P(x) is about the outer x, but R is applied to the inner x.
union (P : (a : str) -> prop) =>
union (Q : (a : str) -> prop) =>
union (R : (a : str | P(a)) -> prop) =>
in { d : { [x : str] P(x) : { [x : str] Q(x) : { r : { y : str | R(x) } } } } }
