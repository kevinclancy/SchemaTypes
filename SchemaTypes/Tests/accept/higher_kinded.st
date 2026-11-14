// A type function whose parameter is itself an index-to-type function with a proof parameter.
predicates
    Q(a : str)
end
type Apply = (F :: (x : str) -> (pf : prf Q(x)) -> *) => { [k : str] Q(k) : (F k) }
type Leaf = (c : str) => prf Q(c) => { self : { s : str | Q(s) }, name : str }
in { d : (Apply !Leaf) }
