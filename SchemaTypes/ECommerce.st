union (ItemId : str -> prop) =>
union (CustId : str -> prop) =>
union (PurchaseId : str -> prop) =>
union (CardType : str -> prop) =>
union (CardId : (x : str) -> prf (CustId x) -> str -> prop) =>

type Card = {
    billingAddr : str,
    cardType : { x : str | (CardType x) }
}

type Purchase = (cust : str) => prf (CustId cust) => {
    itemId : { x : str | (ItemId x) },
    cardId : { x : str | (CardId cust x) }
}

type Customer = (cust : str) => prf (CustId cust) => {
    purchases : {
        // note that p is not related to cust.... we should
        // generate an error for such cases maybe
        [p : str] (PurchaseId p) : (Purchase cust)
    },
    card : {
        // we need to mark this as a source, maybe using an asterisk
        // [card : str] (CardId cust card) * : Card
        // even without this it could still serve as a source
        [card : str] (CardId cust card) : Card
    }
}

in

{
    items : { [x : str] (ItemId x) : { name : str, description : str } },
    cardTypes : { [x : str] (CardType x) : "*"  },
    customers : { [x : str] (CustId x) : (Customer x) }
}