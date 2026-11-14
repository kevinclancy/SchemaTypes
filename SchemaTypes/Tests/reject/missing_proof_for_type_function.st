// Kind error: T requires a proof of A(k), which is not in context.
predicates
    A(a : str)
end
type T = (x : str) => prf A(x) => { r : { y : str | A(y) } }
in { d : { [k : str] : (T k) } }
