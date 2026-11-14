// Applying T to y must not let T's bound y capture the argument.
union (P : (a : str, b : str) -> prop) =>
type T = (x : str) => { [y : str] P(x, y) : { z : { y : str | P(x, y) } } }
in { d : { [y : str] : (T y) } }
