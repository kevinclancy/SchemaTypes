// Applying T to y must not let T's bound y capture the argument.
predicates
    P(a : str, b : str)
end
type T = (x : str) => { [y : str] P(x, y) : { z : { y : str | P(x, y) } } }
in { d : { [y : str] : (T y) } }
