// Kind error: P takes two strings but is applied to one.
union (P : (a : str, b : str) -> prop) =>
in { d : { [x : str] P(x) : str } }
