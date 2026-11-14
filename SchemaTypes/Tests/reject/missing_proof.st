// Kind error: CardId(c, k) requires a proof of CustId(c), which is not in context.
predicates
    CustId(cust : str)
    CardId(cust : str, card : str | CustId(cust))
end
in { cards : { [c : str] : { [k : str] CardId(c, k) : str } } }
