// A string literal as a predicate argument. The validator should look up ^tagged("gold",@loc).
predicates
    P(k : str, x : str)
end
in {
  tagged : { [k, x : str] P(k, x) : "*" },
  best : { z : str | P("gold", z) }
}
