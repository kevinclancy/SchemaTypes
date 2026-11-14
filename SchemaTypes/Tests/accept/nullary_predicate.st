// A predicate with no string arguments.
union (Flag : () -> prop) =>
in { d : { [k : str] Flag() : str } }
