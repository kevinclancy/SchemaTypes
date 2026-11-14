// A string literal as a predicate argument. The validator should look up ^tagged("gold",@loc).
union (A : (k : str) -> prop) =>
union (P : (k : str, x : str | A(k)) -> prop) =>
in {
  tagged : { [k : str] A(k) : { [x : str] P(k, x) : "*" } },
  gold : union (pf : prf A("gold")) => { best : { z : str | P("gold", z) } }
}
