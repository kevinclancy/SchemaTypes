// A type function that takes a string and a proof about it.
predicates
    Kind(k : str)
    Tagged(k : str, x : str | Kind(k))
end
type Ref = (k : str) => prf Kind(k) => { x : str | Tagged(k, x) }
in {
  kinds : { [k : str] Kind(k) : { [x : str] Tagged(k, x) : "*" } },
  favorites : { [k : str] Kind(k) : { best : (Ref k) } }
}
