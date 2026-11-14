// Kind error: Q is not bound.
union (P : (a : str) -> prop) =>
in { d : { [x : str] Q(x) : str }, e : { [y : str] P(z) : str } }
