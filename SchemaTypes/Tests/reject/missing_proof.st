// Kind error: CardId(c, k) requires a proof of CustId(c), which is not in context.
union (CustId : (cust : str) -> prop) =>
union (CardId : (cust : str, card : str | CustId(cust)) -> prop) =>
in { cards : { [c : str] : { [k : str] CardId(c, k) : str } } }
