# SchemaTypes

An experimental dependently typed schema language for MUMPS.

schema_kindcheck.pdf contains an incomplete formalization of this prototype. It is only recommended for readers with knowledge of operational and categorical semantics. If you read it, keep in mind that it's a work in progress, and becomes a bit disjointed and incoherent in later pages. Please contact me if you're interested in helping.

## Introduction

Modern database systems, and also crusty old ones such as MUMPS, advertise the fact that they are "schemaless" as if it is a feature. However, I believe that when someone creates data, they should pair the data with its intended meaning; this saves anyone who stumbles upon the data a world of trouble trying to infer its full meaning from reading the field names, examining concrete data instances, and poring through the code accessing it.

The distinction between the logical and physical layers is a central theme in the study of databases. The logical layer describes real-world entities and relations between them. The physical layer describes how these logical entities and relations are stored in memory. SQL hides the physical layer from the programmer. However, many alternative database systems require the programmer to manipulate the physical layer directly. In particular, consider MUMPS (a modern implementation of which is [Intersystems IRIS](https://www.intersystems.com/products/intersystems-iris/)), whose databases can be considered as partial functions from lists of strings to strings. Here is an example of a MUMPS database:

```
["items", "1", "name"] -> "Slinky"ƒ
["items", "1", "description"] -> "A spring-based toy"
["customers", "kevin", "purchases", "1", "itemId"] -> "1"
```

The above hierarchical structure is formal, and it is physical rather than logical. Because the `name` and `description` fields are both children of `["items", "1"]` the programmer understands that these two fields are physically "close together", and that it's therefore inexpensive to retrieve their values in sequence. On the other hand, a physical database implies the existence of a logical database, and unfortunately MUMPS does not give us the tools to describe the logical database formally. Above, our logical database includes a set of entities called "items". The value at `["customers", "kevin", "purchases", "1", "itemId"]` is an identifier for such an entity (a *foreign key*). Identifers for all items should occur as children of `["items"]`, but a MUMPS developer must often *guess* this fact. Instead, we should have a formal schema that lists all logical sets of entities, the relations between them, and how these entities and relations are stored in memory (i.e. the relation between the logical and physical layers). That is the purpose of SchemaTypes.

Schema Types is a schema language for MUMPS in which both logical and physical layers are given first class treatment. The logical layer is described using a self-contained language which we call the *subject language*. The language describing the physical layer is called the *type language*, and contains fragments of the subject language embedded inside of it, reflecting the one-way dependence of a database's physical layer on its logical layer. (Side note: In the study of programming languages, such a layered language structure is called an *indexed type system*. Mathematically, such a layered structure is called a *fibration*.)  

## Example

Here is an example schema:
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
        [p : str] in (PurchaseId p) : (Purchase cust)
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

In this language, schemas are expressed as types, in which we find embedded expressions of the subject language, which are used to express keys (strings), sets of keys, and relations on keys. Above, ```ItemId```, ```PurchaseId```, ```CardType```, and ```CardId``` are subject variables. ```ItemId```, for example, represents the set of strings ```x``` such that ```(ItemId x)``` is true. 

Near the bottom, the field ```items``` is given type ```{ [x : str] (ItemId x) : { name : str, description : str } }```. This is a dictionary type, but unlike a typical dictionary type, its key set is not an arbitrary set of strings; instead, it is the set of all strings that satisfy the ```ItemId``` predicate.

Saving the above schema in a file called "ECommerce.st" and then executing the command "dotnet run ECommerce.st" will generate an ugly chunk of MUMPS code under a tag called *validate*. This tag can be used to semi- validate that a database conforms to a schema. For example, we could paste validate in a routine containing the following code:

```
MyRoutine
	n x
	s ^items("1", "name")="Slinky"
	s ^items("1", "description")="A spring-based toy"

	s ^cardTypes("visa")="*"
	s ^cardTypes("mastercard")="*"

	s ^customers("kevin", "purchases", "1", "itemId")="1"
	s ^customers("kevin", "purchases", "1", "cardId")="1"

	s ^customers("kevin", "card", "1", "billingAddr")="308 Drury Ln"
	s ^customers("kevin", "card", "1", "cardType")="pisa"

	d validate
	
	q

validate
  ...
```

Running this routine would produce the output ```Expected ^cardTypes("pisa") to be populated when validating ^customers("kevin","card",1,"cardType")```.

In general, if the database does conform to the schema, the partial validator will not generate an error; however, if the database does not conform to the schema then the semi-validator will generate zero or more errors. Under the stipulation that all predicates are finite, I think it would be possible to generate a full validator, but that is beyond the scope of this prototype. Keep in mind that semi-validators have a practical niche: they may be applied to massive, real world data without requiring excessive computation.

## Existing Schema Languages for Hierarchical Database Systems

Note that the ideas underlying this tool are applicable to other database systems besides MUMPS. Most generally, they apply to a class of database systems that I call "hierarchical"; this class includes document databases, key-value stores, and systems such as DynamoDB, which combine elements of both. Attempts to develop schema languages for these database systems have neglected the logical layer. For example, consider [Amazon NoSQL Workbench](https://docs.aws.amazon.com/amazondynamodb/latest/developerguide/workbench.html) for DynamoDB. It uses types to describe the structure of data but contains no types to describe foreign keys. Instead, foreign keys are given the type `string`.

## Why not use SQL?

SQL schemas adequately formalize the logical database layer, so why not use SQL instead of bothering with SchemaTypes? I'm not knowledgable enough on the advantages and disadvantages of SQL over hierarchical database systems to discuss this. However, developers are actively engaged in developing new hierarchical databases systems, and many enormous legacy systems already use hierarchical databases. As a developer, I want these databases to have formalized schemas so that they are easier for me to work with.  

