// Kind error: P takes two strings but is applied to one.
predicates
    P(a : str, b : str)
end
in { d : { [x : str] P(x) : str } }
