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
        [p : str] (PurchaseId p) : (Purchase cust)
    },
    card : {
        [card : str] (CardId cust card) : Card
    }
}

in

{
    cardTypes : { [x : str] (CardType x) : "*"  },
    customers : { [x : str] (CustId x) : (Customer x) }
}