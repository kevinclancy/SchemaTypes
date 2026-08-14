-- Core language syntax definitions
namespace SchemaTypesLean.Core

inductive PreIndex : Nat → Type where
  | var : Fin n → PreIndex n
  | str : String → PreIndex n
  | tru : PreIndex n
  | app : (fn : PreIndex n) → (arg : PreIndex n) → PreIndex n
  deriving DecidableEq

/-- A sort with free variables drawn from `{0 .. n-1}` -/
inductive PreSort : (n : Nat) → Type where
  | str : PreSort n
  | prop : PreSort n
  | prf : PreIndex n → PreSort n
  | fn : (dom : PreSort n) → (cod : PreSort (n+1)) → PreSort n

inductive PreSortContext : (n : Nat) → Type where
  | ext : (rest : PreSortContext n) → (pre_sort : PreSort n) → PreSortContext (n + 1)
  | empty : PreSortContext 0

/-- Weaken an index by adding `k` variables to the context, starting at position `m`.
    Variables below `m` are unchanged, variables at or above `m` are shifted up by `k`. -/
def PreIndex.weakenBy (m : Nat) (k : Nat) : PreIndex n → PreIndex (n + k)
  | .var i =>
      if i.val < m then
        .var ⟨i.val, by omega⟩
      else
        .var (Fin.addNat i k)
  | .str s => .str s
  | .tru => .tru
  | .app fn arg => .app (weakenBy m k fn) (weakenBy m k arg)

def PreIndex.weaken : PreIndex n → PreIndex (n + 1) :=
  PreIndex.weakenBy 0 1

/-- Weaken a sort by adding `k` variables to the context, starting at position `m`.
    When going under a binder, `m` is incremented. -/
def PreSort.weakenBy (m : Nat) (k : Nat) : PreSort n → PreSort (n + k)
  | .str => .str
  | .prop => .prop
  | .prf i => .prf (i.weakenBy m k)
  | .fn dom cod =>
      have h : n + 1 + k = n + k + 1 := by omega
      .fn (weakenBy m k dom) (h ▸ weakenBy (m + 1) k cod)

def PreSort.weaken : PreSort n → PreSort (n + 1) :=
  PreSort.weakenBy 0 1

def PreIndex.substAt (i : PreIndex (n + 1)) (k : Fin (n + 1)) (j : PreIndex n) : PreIndex n :=
  match i with
  | .var v =>
      if h : v = k then
        j
      else if h2 : v < k then
        .var ⟨v.val, by omega⟩
      else
        .var ⟨v.val - 1, by omega⟩
  | .str s => .str s
  | .tru => .tru
  | .app fn arg => .app (fn.substAt k j) (arg.substAt k j)

def PreIndex.subst (i : PreIndex (n + 1)) (j : PreIndex n) : PreIndex n :=
  i.substAt 0 j

/-- Substitute index `j` for variable `k` in a sort, shifting variables above `k` down. -/
def PreSort.substAt (k : Fin (n + 1)) (j : PreIndex n) : PreSort (n + 1) → PreSort n
  | .str => .str
  | .prop => .prop
  | .prf i => .prf (i.substAt k j)
  | .fn dom cod => .fn (dom.substAt k j) (cod.substAt (Fin.succ k) j.weaken)

/-- Substitute index `j` for variable 0 in a sort, shifting other variables down -/
def PreSort.subst (q : PreIndex n) : PreSort (n + 1) → PreSort n :=
  PreSort.substAt 0 q

/-- The `k`th (0 indexed) element of `Ω` from the right is the sort `p` -/
inductive LookupContext :
  {n : Nat} → (Ω : PreSortContext n) → (k : Fin n) → (p : PreSort n) → Type
where
  | here :
      (Ω : PreSortContext n) →
      (s : PreSort n) →
      LookupContext (PreSortContext.ext Ω s) 0 s.weaken
  | there :
      (Ω : PreSortContext n) →
      (s : PreSort n) →
      (i : Fin n) →
      (t : PreSort n) →
      LookupContext Ω i t →
      LookupContext (PreSortContext.ext Ω s) (Fin.succ i) t.weaken

/-- List of PreIndex values, where

* `n` - the number of index variables in context
-/
inductive PreKind : (n : Nat) → Type where
  | proper_ty : PreKind n
  | ty_fn : (dom : PreKind n) → (cod : PreKind n) → PreKind n
  | ind_fn : (dom : PreSort n) → (cod : PreKind (n+1)) → PreKind n

/-- Weaken a kind by adding `k` index variables to the context, starting at position `m`. -/
def PreKind.weakenBy (m : Nat) (k : Nat) : PreKind n → PreKind (n + k)
  | .proper_ty => .proper_ty
  | .ty_fn dom cod => .ty_fn (weakenBy m k dom) (weakenBy m k cod)
  | .ind_fn dom cod =>
      have h : n + 1 + k = n + k + 1 := by omega
      .ind_fn (dom.weakenBy m k) (h ▸ weakenBy (m + 1) k cod)

/-- Weaken a kind by adding one index variable to the context at position 0 -/
def PreKind.weaken : PreKind n → PreKind (n + 1) :=
  PreKind.weakenBy 0 1

/-- Substitute index `j` for variable `k` in a kind, shifting variables above `k` down. -/
def PreKind.substAt (k : Fin (n + 1)) (j : PreIndex n) : PreKind (n + 1) → PreKind n
  | .proper_ty => .proper_ty
  | .ty_fn dom cod => .ty_fn (dom.substAt k j) (cod.substAt k j)
  | .ind_fn dom cod => .ind_fn (dom.substAt k j) (cod.substAt (Fin.succ k) j.weaken)

def PreKind.subst (j : PreIndex n) (κ : PreKind (n + 1)) : PreKind n :=
  κ.substAt 0 j

/-- List of PreIndex values, where

* `n` - the number of index variables in context
* `m` - length of pre-kind context
-/
inductive PreKindContext : (n : Nat) → (m : Nat) → Type where
  | empty : PreKindContext n 0
  | ext : PreKindContext n m → PreKind n → PreKindContext n (m + 1)

/-- Weaken a kind context by adding `k` index variables to the context, starting at position `m`.
    Each kind in the context is weakened with the same `m` and `k` parameters. -/
def PreKindContext.weakenBy (m : Nat) (k : Nat) : PreKindContext n p → PreKindContext (n + k) p
  | .empty => .empty
  | .ext Γ κ => .ext (weakenBy m k Γ) (κ.weakenBy m k)

/-- Weaken a kind context by adding one index variable to the context at position 0 -/
def PreKindContext.weaken : PreKindContext n m → PreKindContext (n + 1) m :=
  PreKindContext.weakenBy 0 1

mutual

/-- List of PreIndex values, where

* `n` - the number of index variables in context
* `m` - the length of the list
-/
inductive PreIndexList : (n : Nat) → (m : Nat) → Type where
  | nil : PreIndexList n 0
  | cons :
    PreIndex (n + m) → PreIndexList n m → PreIndexList n (m + 1)

/-- List of PreTypeFieldList values, where

* `n` - the number of index variables in context
* `m` - the number of type variables in context
-/
inductive PreTypeFieldList : (n : Nat) → (m : Nat) → Type where
  | nil : PreTypeFieldList n m
  | cons : String → PreType n m → PreTypeFieldList n m → PreTypeFieldList n m

/--
* `n` - the number of index variables in context
* `m` - the number of type variables in context
-/
inductive PreType : (n : Nat) → (m : Nat) → Type where
  | var : Fin m → PreType n m
  | dict :
    (guards : PreIndexList (n + 1) k) →
    (val_ty : PreType (n + k + 1) m) → PreType n m
  | record : (fields : PreTypeFieldList n m) → PreType n m
  | refinement : PreIndex (n+1) → PreType n m
  | ind_to_ty_fun : (q : PreSort n) → (τ : PreType (n + 1) m) → PreType n m
  | ty_to_ty_fun : (κ : PreKind n) → (τ : PreType n (m + 1)) → PreType n m
  -- do I still want to keep this in its current form? It's only used for top-level predicates
  | union : PreType n m → PreType n m
  | ty_app : PreType n m → PreType n m → PreType n m
  | ind_app : PreType n m → PreIndex n → PreType n m
end

def PreSortContext.prependTo (Ω : PreSortContext n) (indices : PreIndexList n m) : PreSortContext (n + m) :=
  match indices with
  | .nil => Ω
  | .cons i rest => PreSortContext.ext (Ω.prependTo rest) (PreSort.prf i)

def PreTypeFieldList.toList : PreTypeFieldList n m → List (String × PreType n m)
  | .nil => []
  | .cons name ty tl => (name, ty) :: tl.toList

def PreTypeFieldList.ofList : List (String × PreType n m) → PreTypeFieldList n m
  | [] => .nil
  | (name, ty) :: tl => .cons name ty (ofList tl)

end SchemaTypesLean.Core
