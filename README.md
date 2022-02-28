# SchemaTypes

A dependently typed schema language for MUMPS.
STATUS: Highly experimental.

Modern database systems, and also crusty old ones such as MUMPS, advertise the fact that they are "schemaless" as if it is a feature. However, I believe that when someone creates 
data, they should pair the data with its intended meaning; this saves anyone who stumbles upon the data a world of trouble trying to infer its full meaning 
from reading the field names, concrete data instances, code accessing it.

Developers sometimes write informal schemas, which is better than neglecting to write a schema entirely. But *foreign keys*, data elements that refer to other locations in the database,
are a typical weakpoint for these informal schemas.

For this reason, I've created an experimental schema language for MUMPS databases which aims to provide expressive support for foreign keys. Here is an example schema:

```
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
    items : { [x : str] (ItemId x) : { name : str, description : str } },
    cardTypes : { [x : str] (CardType x) : "*"  },
    customers : { [x : str] (CustId x) : (Customer x) }
}
```

In this language, schemas are expressed as types, and types are layered over another language called the *subject language*, which is used to express keys (strings), sets of keys, and 
relations on keys. Above, *ItemId*, *PurchasId*, *CardType*, and *CardId* are subject variables. ItemId, for example, represents a set of strings, and if x is a string then the proposition 
(ItemId x) is true whenever x is an element of this set. 

Near the bottom, the field items is given type ```{ [x : str] (ItemId x) : { name : str, description : str } }```. This is a dictionary type, but unlike a typical dictionary 
type, its key set is not an arbitrary set of strings; instead, it is the set of all strings that satisfy the *ItemId* predicate.

Saving the above schema in a file called "ECommerce.st" and then executing the command "dotnet run ECommerce.st" will generate an ugly chunk of MUMPS code under a tag called 
*validate*. This tag can be used to validate that a database conforms to a schema. For example, we could paste validate in a routine containing the following code:

```
MyRoutine
	n x
	s ^items("1", "name")="Slinky"
	s ^items("1", "description")="A spring-based toy"
	
	s ^cardTypes("visa")="*"
	s ^cardTypes("mastercard")="*"
	
	s ^customers("kevin", "purchases", "1", "itemId")="1"
	s ^customers("kevin", "purchases", "1", "cardId")="1"
	
	s ^customers("kevin", "card", "1", "billingAddr")="308 Muffin Road"
	s ^customers("kevin", "card", "1", "cardType")="pisa"
	
	d validate
	
    q

validate
  ...
```

Running this routine would produce the output ```Expected ^cardTypes("pisa") to be populated when validating ^customers("kevin","card",1,"cardType")```.

