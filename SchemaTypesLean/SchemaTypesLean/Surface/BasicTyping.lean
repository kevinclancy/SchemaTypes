-- Surface language typing rules
import «SchemaTypesLean».Surface.Syntax
import Mathlib.Data.Finset.Image
import Mathlib.Data.Vector.Basic

namespace SchemaTypesLean.Surface

mutual

/-- Predicate Context well-formedness -/
inductive PredicateContextWf : {n : Nat} → PrePredicateContext 0 n → Type where
  | empty : PredicateContextWf .empty
  | ext :
    (Ω₀ : PrePredicateContext 0 n) →
    (P : PrePredicate n) →
    (PredicateContextWf Ω₀) →
    (ordering : List (PrePredApp n P.num_string_args)) →
    (ordering.toFinset = P.proof_formals) →
    (∀ (i : Fin ordering.length),
      let prev_proofs := (ordering.take i).toFinset
      AppWf ⟨Ω₀, cast (by simp) prev_proofs⟩ (ordering.get i)) →
    PredicateContextWf (.ext Ω₀ (cast (by simp) P))

/-- Context well-formedness.
    Requires that there exists a linearization of the proofs where each proof
    is well-formed with respect to the proofs that come before it. -/
inductive SortContextWf : {n m : Nat} → PreSortContext 0 n 0 m → Type where
  | mk :
    (Ω : PreSortContext 0 n 0 m) →
    PredicateContextWf Ω.pred_context →
    (ordering : List (PrePredApp n m)) →
    -- Converting: Finset (PrePredApp (0 + n) (0 + m)) → Finset (PrePredApp n m)
    (hproofs : Finset (PrePredApp (0 + n) (0 + m)) = Finset (PrePredApp n m) := by simp) →
    (ordering.toFinset = cast hproofs Ω.proofs) →
    (∀ (i : Fin ordering.length),
      -- Converting: Finset (PrePredApp n m) → Finset (PrePredApp (0 + n) (0 + m))
      (hprev : Finset (PrePredApp n m) = Finset (PrePredApp (0 + n) (0 + m)) := by simp) →
      let prev_proofs := (ordering.take i).toFinset
      AppWf ⟨Ω.pred_context, cast hprev prev_proofs⟩ (ordering.get i)) →
    SortContextWf Ω

/-- Predicate application well-formedness -/
inductive AppWf : {n m : Nat} → PreSortContext 0 n 0 m → PrePredApp n m → Type where
  | mk :
    (Ω : PreSortContext 0 n 0 m) →
    (j : PrePredApp n m) →
    (Ωwf : SortContextWf Ω) →
    (arity_match : (lookupPredicate Ω.pred_context j.pred).num_string_args = j.str_args.length) →
    (proofs_present :
      let P := lookupPredicate Ω.pred_context j.pred
      let casted_formals : Finset (PrePredApp n j.str_args.length) :=
        arity_match ▸ P.proof_formals
      let substituted := Finset.image (substStringArgs j.str_args) casted_formals
      substituted ⊆ (cast (by simp) Ω.proofs)) →
    AppWf Ω j
end

inductive KindWf : (Ω : PreSortContext 0 n 0 m) → (κ : PreKind n m) → Type where
  | proper_ty : (SortContextWf Ω) → KindWf Ω (PreKind.proper_ty)
  | ty_fn :
    (SortContextWf Ω) →
    (KindWf Ω τ) →
    (KindWf Ω σ) →
    (KindWf Ω (PreKind.ty_fn τ σ))
  | ind_fn :
    {Ω : PreSortContext 0 n 0 m} →
    (Ω_args : PreSortContext n n' m m') →
    (h : n = 0 + n ∧ m = 0 + m := by simp) →
    (SortContextWf (Ω.append (h.1 ▸ h.2 ▸ Ω_args))) →
    (κ : PreKind (n + n') (m + m')) →
    (KindWf (Ω.append (h.1 ▸ h.2 ▸ Ω_args)) κ) →
    (KindWf Ω (PreKind.ind_fn Ω_args κ))

def KindContextWf (Ω : PreSortContext 0 n 0 m) (Γ : PreKindContext n m k) : Type :=
  SortContextWf Ω × (∀ (i : Fin k), KindWf Ω (Γ.get i))

mutual

inductive TypeFieldListWf :
  (Ω : PreSortContext 0 n 0 m) →
  (Γ : PreKindContext n m k) →
  (used_labels : Finset String) →
  (fields : PreTypeFieldList n m k) →
  Type
where
  | nil : TypeFieldListWf Ω Γ ∅ .nil
  | cons :
    (label : String) →
    (label ∉ rest_labels) →
    (TypeWf Ω Γ field_ty PreKind.proper_ty) →
    (TypeFieldListWf Ω Γ rest_labels rest) →
    TypeFieldListWf Ω Γ (rest_labels ∪ {label}) (.cons label field_ty rest)

inductive TypeWf :
  (Ω : PreSortContext 0 n 0 m) →
  (Γ : PreKindContext n m k) →
  (τ : PreType n m k) →
  (κ : PreKind n m) →
  Type
where
  | var :
    (SortContextWf Ω) →
    (KindContextWf Ω Γ) →
    (TypeWf Ω Γ (PreType.var ℓ) (Γ.get ℓ))
  | dict :
    {Ω : PreSortContext 0 n 0 m} →
    {Γ : PreKindContext n m k} →
    (SortContextWf Ω) →
    (KindContextWf Ω Γ) →
    (guards : Finset (PrePredApp n m)) →
    (ordering : List (PrePredApp n m)) →
    (ordering.toFinset = guards) →
    (∀ (i : Fin ordering.length),
      let prev_guards := (ordering.take i).toFinset
      AppWf ⟨Ω.pred_context, cast (by simp) prev_guards⟩ (ordering.get i)) →
    (val_ty : PreType n (m + 1) k) →
    (TypeWf Ω.extendString (Γ.weaken 0 0 0 1) val_ty PreKind.proper_ty) →
    (TypeWf Ω Γ (PreType.dict guards val_ty) PreKind.proper_ty)
  | record :
    (fields : PreTypeFieldList n m k) →
    (TypeFieldListWf Ω Γ ∅ fields) →
    TypeWf Ω Γ (PreType.record fields) PreKind.proper_ty
  | refinement :
    {Ω : PreSortContext 0 n 0 m} →
    {Γ : PreKindContext n m k} →
    (SortContextWf Ω) →
    (KindContextWf Ω Γ) →
    (j : PrePredApp n (m + 1)) →
    (AppWf Ω.extendString j) →
    TypeWf Ω Γ (PreType.refinement j) PreKind.proper_ty
  | ind_to_ty_fun :
    {Ω : PreSortContext 0 n 0 m} →
    {Γ : PreKindContext n m k} →
    (SortContextWf Ω) →
    (KindContextWf Ω Γ) →
    (Ω_args : PreSortContext n n' m m') →
    (τ : PreType (n + n') (m + m') k) →
    (h : n = 0 + n ∧ m = 0 + m := by simp) →
    (SortContextWf (Ω.append (h.1 ▸ h.2 ▸ Ω_args))) →
    (κ : PreKind (n + n') (m + m')) →
    (TypeWf (Ω.append (h.1 ▸ h.2 ▸ Ω_args)) (Γ.weaken 0 n' 0 m') τ κ) →
    TypeWf Ω Γ (PreType.ind_to_ty_fun Ω_args τ) (PreKind.ind_fn Ω_args κ)
  | ty_to_ty_fun :
    {Ω : PreSortContext 0 n 0 m} →
    {Γ : PreKindContext n m k} →
    (SortContextWf Ω) →
    (KindContextWf Ω Γ) →
    (κ : PreKind n m) →
    (KindWf Ω κ) →
    (τ : PreType n m (k + 1)) →
    (TypeWf Ω (κ ::ᵥ Γ) τ κ') →
    TypeWf Ω Γ (PreType.ty_to_ty_fun κ τ) (PreKind.ty_fn κ κ')
  | ty_app :
    (TypeWf Ω Γ τ (PreKind.ty_fn κ ρ)) →
    (TypeWf Ω Γ σ κ) →
    (TypeWf Ω Γ (PreType.ty_app τ σ) ρ)
  | ind_app :
    {Ω : PreSortContext 0 n 0 m} →
    {Γ : PreKindContext n m k} →
    (Ω' : PreSortContext n n' m m') →
    (TypeWf Ω Γ τ (PreKind.ind_fn Ω' κ)) →
    (pred_args : Fin n' → Fin n) →
    (str_args : Fin m' → Fin m) →
    (TypeWf Ω Γ (PreType.ind_app Ω' τ) κ)


end

end SchemaTypesLean.Surface
