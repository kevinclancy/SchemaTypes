-- Surface language syntax definitions (with n-ary functions)
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Vector.Basic

namespace SchemaTypesLean.Surface

-- /-- A possibly ill-formed index term

--     * `m` - number of string variables in scope
-- -/
-- inductive PreAtom : (m : Nat) → Type where
--   | var : Fin m → PreAtom m
--   | str : String → PreAtom m
--   deriving DecidableEq

-- /-- A possibly ill-formed index term

--     * `n` - number of predicate variables in scope
--     * `m` - number of string variables in scope
-- -/
-- inductive PreIndex : (n : Nat) → (m : Nat) → Type where
--   | pred_var : Fin n → PreIndex n m
--   | str_var : Fin m → PreIndex n m
--   | str : String → PreIndex n m
--   | tru : PreIndex n m
--   | app : (pred : Fin n) → (args : List (PreAtom n)) → PreIndex n
--   deriving DecidableEq

-- inductive PreSortContext : Nat → Type where
--   | ext : (pre_sort : PreSort n) → (rest : PreSortContext n) → PreSortContext (n + 1)
--   | empty : PreSortContext 0

/-- A (possibly ill-formed) partial predicate application.
    Proof arguments elided due to proof irrelevance.

    * `n` is the number of predicate variables in scope.
    * `m` is the number of string variables in scope. -/
structure PrePredApp (n : Nat) (m : Nat) where
  pred : Fin n
  str_args : List (Fin m)
  deriving DecidableEq

/-- Weaken a single Fin by adding m_inc if it's >= m_lo -/
def weakenFin (m_lo m_inc : Nat) (s : Fin m) : Fin (m + m_inc) :=
  if s.val < m_lo then
    ⟨s.val, by omega⟩
  else
    ⟨s.val + m_inc, by omega⟩

/-- Embedding for weakening Fin -/
def weakenFinEmbedding (m_lo m_inc : Nat) : Fin m ↪ Fin (m + m_inc) where
  toFun := weakenFin m_lo m_inc
  inj' := by
    intro s1 s2 h
    simp only [weakenFin] at h
    by_cases h1 : s1.val < m_lo <;> by_cases h2 : s2.val < m_lo
    all_goals simp [h1, h2] at h
    · exact Fin.ext (by omega)
    · omega
    · omega
    · exact Fin.ext (by omega)

/-- Weaken a PrePredApp by adding `n_inc` to predicate variable occurrences whose indices are greater
    than or equal to `n_lo`

    Also add `m_inc` to string variable occurrences whose indices are greater than or equal to `m_lo`
 -/
def PrePredApp.weaken (n_lo n_inc m_lo m_inc : Nat) (app : PrePredApp n m) : PrePredApp (n + n_inc) (m + m_inc) :=
  match app with
  | ⟨pred, str_args⟩ =>
      let pred' : Fin (n + n_inc) := weakenFin n_lo n_inc pred
      let str_args' := str_args.map (weakenFin m_lo m_inc)
      ⟨pred', str_args'⟩

/-- Embedding for weakening predicate applications -/
def PrePredApp.weakenEmbedding (n_lo n_inc m_lo m_inc : Nat) :
  PrePredApp n m ↪ PrePredApp (n + n_inc) (m + m_inc)
where
  toFun := weaken n_lo n_inc m_lo m_inc
  inj' := by
    intro ⟨p1, args1⟩ ⟨p2, args2⟩ h
    simp only [weaken, PrePredApp.mk.injEq] at h
    have hp : p1 = p2 := (weakenFinEmbedding n_lo n_inc).inj' h.left
    have hargs : args1 = args2 := (weakenFinEmbedding m_lo m_inc).inj'.list_map h.right
    simp [hp, hargs]

/-- A (possibly ill-formed) predicate signature

    * `n` is the number of predicate variables in scope
-/
structure PrePredicate (n : Nat) where
  num_string_args : Nat
  proof_formals : Finset (PrePredApp n num_string_args)

/-- Weaken a predicate by adding n_inc predicates starting at n_lo -/
def PrePredicate.weaken (n_lo n_inc : Nat) : PrePredicate n → PrePredicate (n + n_inc)
  | ⟨num_string_args, proof_formals⟩ =>
    ⟨num_string_args, Finset.map (PrePredApp.weakenEmbedding n_lo n_inc 0 0) proof_formals⟩

/-- A (possibly ill-formed) predicate context segment

    * `n₀` - the number of predicates to the left of the first element of the segment
    * `n₁` - the number of predicates in the segment
-/
inductive PrePredicateContext : (n₀ : Nat) → (n₁ : Nat) → Type where
  | empty : PrePredicateContext n₀ 0
  | ext : PrePredicateContext n₀ n₁ → PrePredicate (n₀ + n₁) → PrePredicateContext n₀ (n₁ + 1)

/-- Weaken a predicate context by adding n_inc predicates starting at n_lo -/
def PrePredicateContext.weaken (n_lo n_inc : Nat) :
    PrePredicateContext n₀ n₁ → PrePredicateContext (n₀ + n_inc) n₁
  | .empty => .empty
  | .ext rest pred =>
    .ext (weaken n_lo n_inc rest)
         (cast (by simp [Nat.add_comm, Nat.add_left_comm]) (PrePredicate.weaken n_lo n_inc pred))

def PrePredicateContext.append
  (Ω₀ : PrePredicateContext n₀ n₁)
  (Ω₁ : PrePredicateContext (n₀ + n₁) n₂)
  : PrePredicateContext n₀ (n₁ + n₂) :=

  match n₂, Ω₁ with
  | 0, empty =>
    Ω₀
  | n₂' + 1, ext Ω₁' P =>
    have h : n₀ + n₁ + n₂' = n₀ + (n₁ + n₂') := by omega
    PrePredicateContext.ext (PrePredicateContext.append Ω₀ Ω₁') (h ▸ P)

/-- A context split into predicates, strings, and proofs

    * `n₀` - number of predicate variables to the left of context
    * `n₁` - number of predicate variables in context
    * `m₀` - number of string variables left of context
    * `m₁` - number of string variables in context
-/
structure PreSortContext (n₀ : Nat) (n₁ : Nat) (m₀ : Nat) (m₁ : Nat) where
  /-- List of predicates signatures for predicate variables in context -/
  pred_context : PrePredicateContext n₀ n₁

  /-- Set of proven predicate applications in context -/
  proofs : Finset (PrePredApp (n₀ + n₁) (m₀ + m₁))

def PreSortContext.append
  (Ω₀ : PreSortContext n₀ n₁ m₀ m₁)
  (Ω₁ : PreSortContext (n₀ + n₁) n₂ (m₀ + m₁) m₂)
  : PreSortContext n₀ (n₁ + n₂) m₀ (m₁ + m₂) :=
  have ha1 : n₀ + n₁ + n₂ = n₀ + (n₁ + n₂) := by omega
  have ha2 : m₀ + m₁ + m₂ = m₀ + (m₁ + m₂) := by omega
  let w := cast (by rw [ha1, ha2]) (PrePredApp.weaken (n := n₀ + n₁) (m := m₀ + m₁) 0 n₂ 0 m₂)
  let proofs₁ := cast (by rw [ha1, ha2]) Ω₁.proofs
  ⟨Ω₀.pred_context.append Ω₁.pred_context,
   (Finset.image w Ω₀.proofs) ∪ proofs₁⟩

/-- Extend a sort context with a single string variable by weakening all proofs -/
def PreSortContext.extendString (Ω : PreSortContext n₀ n₁ m₀ m₁) : PreSortContext n₀ n₁ m₀ (m₁ + 1) :=
  have h : m₀ + m₁ + 1 = m₀ + (m₁ + 1) := by omega
  let w := PrePredApp.weaken (n := n₀ + n₁) (m := m₀ + m₁) 0 0 0 1
  ⟨Ω.pred_context, cast (by rw [h]; simp) (Finset.image w Ω.proofs)⟩

/-- PreSorts classify PreIndices

  * n - The number of predicates in context
  * m - The number of strings in context
-/
inductive PreSort : (n : Nat) → (m : Nat) → Type where
  | str : PreSort n m
  | prop : PreSort n m
  | pred : (num_string_args : Nat) → (Finset (PrePredApp n (m + num_string_args))) → PreSort n m
  deriving DecidableEq

/-- Look up the k-th predicate in a predicate context.
    Returns the predicate weakened to have n free variables. -/
def lookupPredicate {n₁ : Nat} (ctx : PrePredicateContext 0 n₁) (k : Fin n₁) : PrePredicate n₁ :=
  match n₁, ctx with
  | 0, .empty => Fin.elim0 k
  | n + 1, .ext rest pred =>
    if h : k.val = 0 then
      Nat.zero_add n ▸ pred.weaken 0 1
    else
      have : k.val - 1 < n := by omega
      (lookupPredicate rest ⟨k.val - 1, this⟩).weaken 0 1

/-- Substitute a list of string arguments into string variable positions.
    Given k string arguments and a string variable index in m+k variables,
    if the index is < k, replace it with the corresponding argument,
    otherwise shift it down by k. -/
def substStringVar (args : List (Fin m)) : Fin args.length → Fin m
  | ⟨i, h⟩ =>
    if hi : i < args.length then
      args.get ⟨i, hi⟩
    else
      ⟨i - args.length, by omega⟩

/-- Substitute string arguments into a predicate application -/
def substStringArgs (args : List (Fin m)) (target : PrePredApp n args.length) : PrePredApp n m :=
  let ⟨pred, str_args⟩ := target
  ⟨pred, str_args.map (substStringVar args)⟩

/--
* `n` - the number of predicate variables in context
* `m` - the number of string variables in scope
-/
inductive PreKind : (n : Nat) → (m : Nat) → Type where
  | proper_ty : PreKind n m
  | ty_fn : (dom : PreKind n m) → (cod : PreKind n m) → PreKind n m
  | ind_fn :
    (PreSortContext n num_pred_formals m num_str_formals) →
    (cod : PreKind (n + num_pred_formals) (m + num_str_formals)) →
    PreKind n m

/-- Weaken a kind by adding `m_inc` string variables starting at position `m_lo`
    and adding `n_inc` predicate variables, starting at `n_lo`
-/
def PreKind.weaken (n_lo n_inc m_lo m_inc : Nat) : PreKind n m → PreKind (n + n_inc) (m + m_inc)
  | .proper_ty => .proper_ty
  | .ty_fn dom cod =>
    .ty_fn (weaken n_lo n_inc m_lo m_inc dom) (weaken n_lo n_inc m_lo m_inc cod)
  | @PreKind.ind_fn _ num_preds _ num_strs Ω κ =>
      -- Ω has type PreSortContext n num_preds m num_strs
      -- Need PreSortContext (n + n_inc) num_preds (m + m_inc) num_strs
      have h2 : m + m_inc + num_strs = m + num_strs + m_inc := by omega
      have h3 : (n + n_inc + num_preds) = (n + num_preds + n_inc) := by omega
      let w := PrePredApp.weaken n_lo n_inc m_lo m_inc
      let weakened_proofs := Finset.image w Ω.proofs
      let Ω' : PreSortContext (n + n_inc) num_preds (m + m_inc) num_strs :=
        ⟨PrePredicateContext.weaken n_lo n_inc Ω.pred_context, cast (by rw [h2, h3]) weakened_proofs⟩
      -- κ has type PreKind (n + num_preds) (m + num_strs)
      -- Need PreKind (n + num_preds + n_inc) (m + num_strs + m_inc)
      let κ' : PreKind (n + num_preds + n_inc) (m + num_strs + m_inc) :=
        weaken n_lo n_inc m_lo m_inc κ
      PreKind.ind_fn Ω' (cast (by rw [h2, h3]) κ')

/--
* `n` - number of predicate variables in scope
* `m` - number of string variables in scope
* `k` - length of kind context
-/
def PreKindContext n m k := List.Vector (PreKind n m) k

/-- Weaken a kind context by adding `n_inc` predicate variables starting at `n_lo`
    and adding `m_inc` string variables starting at `m_lo` -/
def PreKindContext.weaken (n_lo n_inc m_lo m_inc : Nat) :
    PreKindContext n m k → PreKindContext (n + n_inc) (m + m_inc) k :=
  fun Γ => Γ.map (PreKind.weaken n_lo n_inc m_lo m_inc)

mutual

/--
* `n` - the number of predicate variables in context
* `m` - the number of string variables in context
* `k` - the number of type variables in context
-/
inductive PreTypeFieldList : (n : Nat) → (m : Nat) → (k : Nat) → Type where
  | nil : PreTypeFieldList n m k
  | cons : String → PreType n m k → PreTypeFieldList n m k → PreTypeFieldList n m k

/--
* `n` - the number of predicate variables in context
* `m` - the number of string variables in context
* `k` - the number of type variables in context
-/
inductive PreType : (n : Nat) → (m : Nat) → (k : Nat) → Type where
  | var : Fin k → PreType n m k
  | dict :
    (guards : Finset (PrePredApp n m)) →
    (val_ty : PreType n (m + 1) k) →
    PreType n m k
  | record : (fields : PreTypeFieldList n m k) → PreType n m k
  | refinement : PrePredApp n (m + 1) → PreType n m k
  | ind_to_ty_fun :
    (Ω : PreSortContext n n₁ m m₁) →
    (τ : PreType (n + n₁) (m + m₁) k) →
    PreType n m k
  | ty_to_ty_fun : (κ : PreKind n m) → (τ : PreType n m (k + 1)) → PreType n m k
  | ty_app : PreType n m k → PreType n m k → PreType n m k
  | ind_app :
    (ind_to_ty_fn : PreType n m k) →
    (n₁ m₁ : Nat) →
    (pred_args : Fin n₁ → Fin n) →
    (str_args : Fin m₁ → Fin m) →
    PreType n m k

structure PreSchema where
  num_predicates : Nat
  predicate_defs : PrePredicateContext 0 num_predicates
  body : PreType num_predicates 0 0

end -- mutual

end SchemaTypesLean.Surface
