-- Core language typing rules
import «SchemaTypesLean».Core.Syntax

namespace SchemaTypesLean.Core

/--
* `Ω` - The sorting context the index is well-sorted under
* `i` - The index
* `p` - The sort of the index `i` under context `Ω`
-/
inductive WfIndex :
  {n : Nat} → (Ω : PreSortContext n) → (i : PreIndex n) → (p : PreSort n) → Type
where
  | str : (Ω : PreSortContext n) → (s : String) → WfIndex Ω (PreIndex.str s) PreSort.str
  | var :
    {Ω : PreSortContext n} → {k : Fin n} → {p : PreSort n} →
    (LookupContext Ω k p) → WfIndex Ω (PreIndex.var k) p
  | tru : (Ω : PreSortContext n) → WfIndex Ω PreIndex.tru PreSort.prop
  | app :
    {Ω : PreSortContext n} → {q : PreSort n} → {r : PreSort (n+1)} →
    {j : PreIndex n} → {k : PreIndex n} →
    (WfIndex Ω j (PreSort.fn q r)) → (WfIndex Ω k q) →
    WfIndex Ω (PreIndex.app j k) (r.subst k)

inductive WfSort : {n : Nat} → (Ω : PreSortContext n) → (p : PreSort n) → Type where
  | str : (Ω : PreSortContext n) → WfSort Ω PreSort.str
  | fn :
    {Ω : PreSortContext n} → {q : PreSort n} → {r : PreSort (n+1)} →
    (h : WfSort (PreSortContext.ext Ω q) r) → (WfSort Ω (PreSort.fn q r))
  | prf :
    {Ω : PreSortContext n} → {j : PreIndex n} → (WfIndex Ω j PreSort.prop) →
    WfSort Ω (PreSort.prf j)

inductive WfSortContext : {n : Nat} → (Ω : PreSortContext n) → Type where
  | empty : WfSortContext PreSortContext.empty
  | ext :
    (Ω : PreSortContext n) → (q : PreSort n) → WfSort Ω q →
    WfSortContext (PreSortContext.ext Ω q)

inductive WfKind : {n : Nat} → (Ω : PreSortContext n) → (κ : PreKind n) → Type where
  | proper_ty : WfKind Ω PreKind.proper_ty
  | ind_fn :
    WfSort Ω q → WfKind (PreSortContext.ext Ω q) κ → WfKind Ω (PreKind.ind_fn q κ)
  | ty_fn : WfKind Ω κ → WfKind Ω ρ → WfKind Ω (PreKind.ty_fn κ ρ)

inductive WfKindContext :
  {n m : Nat} → (Ω : PreSortContext n) → (Γ : PreKindContext n m) → Type
where
  | empty : {Ω : PreSortContext n} → WfKindContext Ω (PreKindContext.empty)
  | ext :
    {Ω : PreSortContext n} → {Γ : PreKindContext n m} → {κ : PreKind n} →
    (WfKindContext Ω Γ) → (WfKind Ω κ) →
    WfKindContext Ω (PreKindContext.ext Γ κ)

mutual

inductive WfFieldList
  : {n m : Nat} → (Ω : PreSortContext n) → (Γ : PreKindContext n m) →
    (PreTypeFieldList n m) → Type
where
  | nil : WfFieldList Ω Γ (PreTypeFieldList.nil)
  | cons :
    (wf_rest : WfFieldList Ω Γ rest) → (WfType Ω Γ τ (PreKind.proper_ty)) →
    WfFieldList Ω Γ (PreTypeFieldList.cons s τ rest)

inductive WfType
  : {n m : Nat} → (Ω : PreSortContext n) → (Γ : PreKindContext n m) →
    (τ : PreType n m) → (κ : PreKind n) → Type
where
  | refinement :
    (WfIndex (PreSortContext.ext Ω PreSort.str) i PreSort.prop) →
    WfType Ω Γ (PreType.refinement i) PreKind.proper_ty
  | ind_to_ty_fn :
     (WfSort Ω q) → (WfType (PreSortContext.ext Ω q) Γ.weaken τ κ) →
     WfType Ω Γ (PreType.ind_to_ty_fun q τ) (PreKind.ind_fn q κ)
  | ty_to_ty_fun :
    (WfKind Ω κ) → (WfType Ω (PreKindContext.ext Γ κ) τ ρ) →
    WfType Ω Γ (PreType.ty_to_ty_fun κ τ) (PreKind.ty_fn κ ρ)
  | ty_app :
    (WfType Ω Γ τ (PreKind.ty_fn κ ρ)) → (WfType Ω Γ σ κ) →
    (WfType Ω Γ (PreType.ty_app τ σ) ρ)
  | ind_app :
    (WfType Ω Γ τ (PreKind.ind_fn q ρ)) → (WfIndex Ω j q) →
    (WfType Ω Γ (PreType.ind_app τ j) (ρ.subst j))
  | record :
    (fields : (PreTypeFieldList n m)) → (WfFieldList Ω Γ fields) →
    WfType Ω Γ (PreType.record fields) PreKind.proper_ty
  | union :
    (WfType Ω Γ τ (PreKind.ind_fn q PreKind.proper_ty)) →
    WfType Ω Γ (PreType.union τ) PreKind.proper_ty
  | dict :
    {Γ : PreKindContext n m} →
    (guards : PreIndexList (n + 1) k) →
    (have h : n + 1 + k = n + k + 1 := by omega
     WfType ((PreSortContext.ext Ω PreSort.str).prependTo guards)
            (h ▸ Γ.weakenBy 0 (k + 1))
            (h ▸ τ)
            PreKind.proper_ty) →
    WfType Ω Γ (PreType.dict guards τ) PreKind.proper_ty

  -- | dict :
  --   (guards : PreIndexList (n + 1) k) →
  --   (val_ty : PreType (n + k + 1) m) → PreType n m
end

end SchemaTypesLean.Core
