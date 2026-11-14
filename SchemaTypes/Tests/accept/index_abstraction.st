// A type function that takes a string and a proof about it.
union (Kind : (k : str) -> prop) =>
union (Tagged : (k : str, x : str | Kind(k)) -> prop) =>
type Ref = (k : str) => prf Kind(k) => { x : str | Tagged(k, x) }
in {
  kinds : { [k : str] Kind(k) : { [x : str] Tagged(k, x) : "*" } },
  favorites : { [k : str] Kind(k) : { best : (Ref k) } }
}
