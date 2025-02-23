-- http://euclid.trentu.ca/math/sb/pcml/pcml-16.pdf

open Classical

structure Set.{u} (α : Sort u) where
  predicate : α → Prop

instance {α : Sort u} : CoeSort (Set α) (Sort max u 1) where
  coe s := { x : α // s.predicate x}

instance {α : Type u} : EmptyCollection (Set α) where
  emptyCollection := Set.mk (fun _ => False)

instance {α : Type u} : Singleton α (Set α) where
  singleton x := Set.mk (fun y => y = x)

instance {α : Type u} : Insert α (Set α) where
  insert x s := Set.mk (fun y => y = x ∨ s.predicate y)

instance {α : Type u} : Membership α (Set α) where
  mem s x := s.predicate x

instance {α : Type u} : HasSubset (Set α) where
  Subset a b := ∀ x : a, x.val ∈ b

instance {α : Type u} : Union (Set α) where
  union S T := Set.mk (fun x => S.predicate x ∨ T.predicate x)

instance {α : Type u} : Inter (Set α) where
  inter S T := Set.mk (fun x => S.predicate x ∧ T.predicate x)

namespace Set
variable {α : Type u}

theorem setext (a b : Set α) : (∀ x : α, x ∈ a ↔ x ∈ b) → a = b := by
    intro h
    calc a
      _ = Set.mk (a.predicate) := rfl
      _ = Set.mk (b.predicate) := ?_
      _ = b := rfl
    apply congrArg Set.mk
    apply funext
    intro x
    apply propext
    exact h x

def All (α : Type u) : Set α := Set.mk (fun _ => True)

theorem empty_insert (x : α) : insert x (∅ : Set α) = {x} := by
    apply setext
    intro y
    apply Iff.intro
    . intro h
      apply Or.elim h
      . intro h₁; exact h₁
      . intro; contradiction
    . intro h; exact Or.inl h

theorem for_all (s : Set α) (p : α → Prop) : (∀ x : s, p x) ↔ (∀ x : α, x ∈ s → p x) := by
    apply Iff.intro
    . intro h₁
      intro x
      intro h₂
      show (p ∘ Subtype.val) (⟨x, h₂⟩ : Subtype _)
      apply Subtype.forall.mp
      intro x₁
      show p x₁.val
      exact h₁ x₁
    . intro h₁
      intro x
      exact h₁ x.val x.property

theorem forall_insert (A : Set α) (b : α) (p : α → Prop) : (∀ x : (insert b A : Set α), p x) ↔ (p b ∧ ∀ x : A, p x) := by
    apply Iff.intro
    . intro h
      constructor
      . exact h ⟨b, Or.inl rfl⟩
      . intro x
        exact h ⟨x, Or.inr x.property⟩
    . intro h₀
      intro x
      apply Or.elim x.property
      . intro h; exact Eq.subst h.symm h₀.left
      . intro h₁; exact h₀.right ⟨x.val,  h₁⟩

theorem insert_subset (b : α) (A : Set α) : A ⊆ (insert b A) := by
    intro x
    show x.val = b ∨ x.val ∈ A
    exact Or.inr x.property

theorem member_subset (A : Set α) (x : α) (h : x ∈ A) : {x} ⊆ A := by
    intro y
    rw [y.property]
    exact h

theorem empty_subset {A : Set α} : ∅ ⊆ A := by
    intro x
    exact False.elim x.property

theorem insert_member {A : Set α} {x : A} : insert x.val A = A := by
    apply setext
    intro y
    apply Iff.intro
    . intro h
      apply Or.elim h
      . intro h; exact Eq.subst h.symm x.property
      . intro; assumption
    . exact Or.inr

theorem subset_union_left {S T : Set α} : S ⊆ (S ∪ T) := fun x => Or.inl x.property
theorem subset_union_right {S T : Set α} : T ⊆ (S ∪ T) := fun x => Or.inr x.property

theorem insert_as_union (S : Set α) (x : α) : insert x S = {x} ∪ S := rfl

theorem union_subset (S T U : Set α) (h₁ : S ⊆ U) (h₂ : T ⊆ U) : (S ∪ T) ⊆ U := by
    intro x
    apply Or.elim x.property
    . intro h; exact h₁ ⟨x.val, h⟩
    . intro h; exact h₂ ⟨x.val, h⟩

theorem intersection_subset_left (S T : Set α) : (S ∩ T) ⊆ S := fun x => x.property.left
theorem intersection_subset_right (S T : Set α) : (S ∩ T) ⊆ T := fun x => x.property.right

inductive Finite.{u} : Set α → Type u where
    | Empty : Finite ∅
    | Singleton (x : α) : Finite {x}
    | Union {S T : Set α} : Finite S → Finite T → Finite (S ∪ T)
    | Intersection {S T : Set α} : Finite S → Finite T → Finite (S ∩ T)

def FiniteProp (S : Set α) := ∃ _ : Finite S, True

namespace FiniteProp
def Empty : FiniteProp (∅ : Set α) := ⟨Finite.Empty, trivial⟩
def Singleton (x : α) : FiniteProp {x} := ⟨Finite.Singleton x, trivial⟩
def Union {S T : Set α} : FiniteProp S → FiniteProp T → FiniteProp (S ∪ T) := (⟨Finite.Union ·.choose ·.choose, trivial⟩)
def Intersection {S T : Set α} : FiniteProp S → FiniteProp T → FiniteProp (S ∩ T) := (⟨Finite.Intersection ·.choose ·.choose, trivial⟩)
end FiniteProp

def equalCardinality {α : Type u} {β : Type v} (S : Set α) (T : Set β) : Prop :=   ∃ f : S → T, (∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂) ∧ (∀ y, ∃ x, f x = y)

theorem equal_cardinality_refl {S : Set α} : equalCardinality S S := ⟨id, fun _ _ h => h, fun x => ⟨x, rfl⟩⟩
theorem equal_cardinality_symm {S : Set α} {T : Set β} (h : equalCardinality S T) : equalCardinality T S := by
  have ⟨f, h₁, h₂⟩ := h
  let g : T → S := fun y => (h₂ y).choose
  have h₃ : ∀ y : T, f (g y) = y := fun y => (h₂ y).choose_spec
  apply Exists.intro g
  constructor
  . intro y₁ y₂ h₄
    rw [←h₃ y₁, ←h₃ y₂]
    exact congrArg f h₄
  . intro x
    apply Exists.intro (f x)
    have h₅ : f (g (f x)) = f x := h₃ (f x)
    exact h₁ (g (f x)) x h₅

theorem equal_cardinality_trans {S : Set α} {T : Set β} {U : Set γ} (h'₁ : equalCardinality S T) (h'₂ : equalCardinality T U) : equalCardinality S U := by
  have ⟨f, h₁₁, h₁₂⟩ := h'₁
  have ⟨g, h₂₁, h₂₂⟩ := h'₂
  let h := g ∘ f
  apply Exists.intro h
  constructor
  . intro x₁ x₂ h₃
    have h₄ : f x₁ = f x₂ := h₂₁ (f x₁) (f x₂) h₃
    exact h₁₁ x₁ x₂ h₄
  . intro z
    have ⟨y, h₅⟩ : ∃ y : T, g y = z := h₂₂ z
    have ⟨x, h₆⟩ : ∃ x : S, f x = y := h₁₂ y
    have h₇ : g (f x) = z := Eq.subst (motive := fun a => g a = z) h₆.symm h₅
    exact ⟨x, h₇⟩

def Countable (S : Set α) : Prop := ∃ f : S → Nat, ∀ x₁ x₂ : S, f x₁ = f x₂ → x₁ = x₂

theorem any_natural_numbers_countable (S : Set Nat) : Countable S := by
  let f : S → Nat := fun x => x.val
  apply Exists.intro f
  intro x₁ x₂
  unfold f
  intro h
  exact Subtype.eq h

def max_of_finite_nats {S : Set Nat} (f : Finite S) : Nat := match f with
  | Finite.Empty => 0
  | Finite.Singleton x => x
  | Finite.Union A B => max (max_of_finite_nats A) (max_of_finite_nats B)
  | Finite.Intersection A B => max (max_of_finite_nats A) (max_of_finite_nats B)


theorem max_of_finite_nats_ge_all {S : Set Nat} (f : Finite S) : ∀ n : S, max_of_finite_nats f ≥ n := match f with
  | Finite.Empty => fun x => False.elim x.property
  | Finite.Singleton x => fun y => Eq.subst y.property.symm (Nat.le_refl x)
  | Finite.Union A B => fun x =>
  have h₁ : max_of_finite_nats A ≥ x ∨ max_of_finite_nats B ≥ x := Or.elim x.property (fun h => Or.inl (max_of_finite_nats_ge_all A ⟨x, h⟩)) (fun h => Or.inr (max_of_finite_nats_ge_all B ⟨x, h⟩))
  have h₂ : max_of_finite_nats (Finite.Union A B) ≥ max_of_finite_nats A := Nat.le_max_left (max_of_finite_nats A) (max_of_finite_nats B)
  have h₃ : max_of_finite_nats (Finite.Union A B) ≥ max_of_finite_nats B := Nat.le_max_right (max_of_finite_nats A) (max_of_finite_nats B)
  Or.elim h₁ (fun h => Nat.le_trans h h₂) (fun h => Nat.le_trans h h₃)
  | Finite.Intersection A B => fun x =>
  have h₁ : max_of_finite_nats A ≥ x := max_of_finite_nats_ge_all A ⟨x, x.property.left⟩
  have h₂ : max_of_finite_nats (Finite.Intersection A B) ≥ max_of_finite_nats A := Nat.le_max_left (max_of_finite_nats A) (max_of_finite_nats B)
  Nat.le_trans h₁ h₂

theorem natural_numbers_infinite : ¬FiniteProp (All Nat) := by
    intro finite
    let max_nat := max_of_finite_nats finite.choose
    have h₀ : ∀n : (All Nat), max_nat ≥ n := max_of_finite_nats_ge_all finite.choose
    let not_present := max_nat + 1
    have h₁ : ∀ n : (All Nat), not_present > n := fun n => Nat.lt_succ_of_le (h₀ n)
    have h₂ : ∀ n : (All Nat), not_present ≠ n := fun n => Nat.ne_iff_lt_or_gt.mpr (Or.inr (h₁ n))
    have h₃ : not_present ∉ All Nat := fun h => h₂ ⟨not_present, h⟩ rfl
    exact h₃ trivial
end Set

namespace propositional
inductive Proposition where
    | Atomic : Nat → Proposition
    | Not : Proposition → Proposition
    | Implies : Proposition → Proposition → Proposition
deriving Repr

namespace Proposition
def atomic_count (p : Proposition) : Nat := match p with
    | Atomic _ => 1
    | Not p => atomic_count p
    | Implies p q => atomic_count p + atomic_count q

theorem atomic_count_atomic {n : Nat} : atomic_count (Atomic n) = 1 := rfl
theorem atomic_count_not {p : Proposition} : atomic_count (Not p) = atomic_count p := rfl
theorem atomic_count_implies {p q : Proposition} : atomic_count (Implies p q) = atomic_count p + atomic_count q := rfl

def implies_count (p : Proposition) : Nat := match p with
    | Atomic _ => 0
    | Not p => implies_count p
    |Implies p q => implies_count p + implies_count q + 1

theorem implies_count_atomic {n : Nat} : implies_count (Atomic n) = 0 := rfl
theorem implies_count_not {p : Proposition} : implies_count (Not p) = implies_count p := rfl
theorem implies_count_implies {p q : Proposition} : implies_count (Implies p q) = implies_count p + implies_count q + 1 := rfl

theorem p1_4 : ∀ p : Proposition, atomic_count p = implies_count p + 1 := by
    intro p
    induction p with
    | Atomic _ => rfl
    | Not p ih => calc atomic_count (Not p)
        _ = atomic_count p := rfl
        _ = implies_count p + 1 := ih
        _ = implies_count (Not p) + 1 := rfl
    | Implies p q ih₁ ih₂ => calc atomic_count (Implies p q)
        _ = atomic_count p + atomic_count q := rfl
        _ = (implies_count p + 1) + (implies_count q + 1) := by rw [ih₁, ih₂]
        _ = implies_count p + 1 + implies_count q + 1 := by rw [←Nat.add_assoc]
        _ = implies_count p + (1 + implies_count q) + 1 := by simp [Nat.add_assoc]
        _ = implies_count p + (implies_count q + 1) + 1 := by simp [Nat.add_comm]
        _ = implies_count (Implies p q) + 1 := by rfl

def And (p q : Proposition) : Proposition := Not (Implies p (Not q))
def Or (p q : Proposition) : Proposition := Implies (Not p) q
def Iff (p q : Proposition) : Proposition := And (Implies p q) (Implies q p)

def is_subformula (a b : Proposition) : Prop := a = b ∨ match b with
    | Atomic _ => False
    | Not c => a.is_subformula c
    | Implies c d => a.is_subformula c ∨ a.is_subformula d

--theorem propositions_countable : Set.countable (Set.all Proposition) :=
end Proposition

inductive TruthValue where
    | True
    | False

namespace TruthValue
def Not (v : TruthValue) : TruthValue := match v with
    | True => False
    | False => True

theorem double_negation (v : TruthValue) : v.Not.Not = v := match v with
    | True => rfl
    | False => rfl

def Implies (u v : TruthValue) : TruthValue := match u, v with
    | True, False => False
    | _, _ => True

theorem not_true_and_false (v : TruthValue) : ¬(v = True ∧ v = False) := by
    intro ⟨ht, hf⟩
    have : True = False := Eq.trans ht.symm hf
    injection this

theorem not_implies (u v : TruthValue) : u.Implies v = False → u = True ∧ v = False := by
    intro h
    match u with
    | True => match v with
      | True => exact False.elim (not_true_and_false (True.Implies True) ⟨rfl, h⟩)
      | False => exact ⟨rfl, rfl⟩
    | False => match v with
      | True => exact False.elim (not_true_and_false (True.Implies True) ⟨rfl, h⟩)
      | False => exact False.elim (not_true_and_false (True.Implies True) ⟨rfl, h⟩)

theorem implies (u v : TruthValue) : u.Implies v = True → u = False ∨ v = True := by
    intro h
    match u, v with
    | True, True => exact Or.inr rfl
    | True, False => exact False.elim (not_true_and_false (True.Implies False) ⟨h, rfl⟩)
    | False, True => exact Or.inl rfl
    | False, False => exact Or.inl rfl

theorem not_true (v : TruthValue) : ¬(v = TruthValue.True) ↔ v = TruthValue.False := by
  apply Iff.intro
  . intro h
    match v with
    | TruthValue.False => rfl
    | TruthValue.True => exact absurd rfl h
  . intro h_false
    intro h_true
    have : TruthValue.False = TruthValue.True := Eq.trans h_false.symm h_true
    injection this

def And (u v : TruthValue) : TruthValue := match u, v with
| True, True => True
| _, _ => False

def Or (u v : TruthValue) : TruthValue := match u, v with
| False, False => False
| _, _ => True

def Iff (u v : TruthValue) : TruthValue := match u, v with
| True, True => True
| False, False => True
| _, _ => False

theorem implies_true (v : TruthValue) : v.Implies True = True := match v with
    | True => rfl
    | False => rfl
end TruthValue

structure Valuation where
    function : Proposition → TruthValue
    negation (p : Proposition) : function (p.Not) = (function p).Not
    implication (p q : Proposition) : function (p.Implies q) = (function p).Implies (function q)

instance : CoeFun Valuation (fun _ => Proposition → TruthValue) where
  coe u := u.function

namespace Valuation
theorem atomically_identical (u v : Valuation) (p : Proposition) : (∀ n : Nat, (Proposition.Atomic n).is_subformula p → u (Proposition.Atomic n) = v (Proposition.Atomic n)) → u p = v p := by
    intro h
    induction p with
    | Atomic n => exact h n (Or.inl rfl)
    | Not q ih =>
      have h₁ : ∀ n : Nat, (Proposition.Atomic n).is_subformula q → u (Proposition.Atomic n) = v (Proposition.Atomic n) := by
        intro n
        intro h_inner
        exact h n (Or.inr h_inner)
      calc u q.Not
        _ = (u q).Not := u.negation q
        _ = (v q).Not := by rw [ih h₁]
        _ = v (q.Not) := (v.negation q).symm
    | Implies q r ih₁ ih₂ =>
      have h₁ : ∀ n : Nat, (Proposition.Atomic n).is_subformula q → u (Proposition.Atomic n) = v (Proposition.Atomic n) := by
        intro n
        intro h_inner
        exact h n (Or.inr (Or.inl h_inner))
      have h₂ : ∀ n : Nat, (Proposition.Atomic n).is_subformula r → u (Proposition.Atomic n) = v (Proposition.Atomic n) := by
        intro n
        intro h_inner
        exact h n (Or.inr (Or.inr h_inner))
      calc u (q.Implies r)
        _ = (u q).Implies (u r) := u.implication q r
        _ = (v q).Implies (v r) := by rw [ih₁ h₁, ih₂ h₂]
        _ = v (q.Implies r) := (v.implication q r).symm

variable {u : Valuation}

theorem not_definition (p : Proposition) : u p.Not = TruthValue.True ↔ u p = TruthValue.False := by
    apply Iff.intro
    . intro h
      have : (u p).Not = TruthValue.False.Not := Eq.trans (u.negation p).symm h
      have : (u p).Not.Not = TruthValue.False.Not.Not := congrArg TruthValue.Not this
      exact Eq.trans (TruthValue.double_negation (u p)).symm (Eq.trans this (TruthValue.double_negation TruthValue.False))
    . intro h
      calc u p.Not
      _ = (u p).Not := u.negation p
      _ = TruthValue.False.Not := by rw [h]

theorem implies_definition (p q : Proposition) : u (p.Implies q) = TruthValue.True ↔ (u p = TruthValue.True → u q = TruthValue.True) := by
    apply Iff.intro
    . intro h
      intro hpt
      have h₁ : (u p).Implies (u q) = TruthValue.True := Eq.trans (u.implication p q).symm h
      apply byContradiction
      intro hnq
      have hqf : u q = TruthValue.False := (TruthValue.not_true (u q)).mp hnq
      apply absurd h₁
      intro h_implies
      have : (u p).Implies (u q) = TruthValue.False := by (calc
        _ = TruthValue.True.Implies TruthValue.False := by rw [hpt, hqf])
      have : TruthValue.True = TruthValue.False := Eq.trans (h_implies).symm this
      injection this
    . intro h
      apply byContradiction
      intro hnvt
      have hvf : u (p.Implies q) = TruthValue.False := (TruthValue.not_true (u (p.Implies q))).mp hnvt
      have hf_implies : (u p).Implies (u q) = TruthValue.False := Eq.trans (u.implication p q).symm hvf
      have hpnq : u p = TruthValue.True ∧ u q = TruthValue.False := TruthValue.not_implies (u p) (u q) hf_implies
      exact TruthValue.not_true_and_false (u q) ⟨h hpnq.left, hpnq.right⟩

theorem and_definition (p q : Proposition) : u (p.And q) = TruthValue.True ↔ u p = TruthValue.True ∧ u q = TruthValue.True := by
    apply Iff.intro
    . intro h
      let vp := u p
      let vq := u q
      have : u (p.And q) = (vp.Implies vq.Not).Not := (calc u (p.And q)
        _ = u (p.Implies q.Not).Not := rfl
        _ = (u (p.Implies q.Not)).Not := u.negation (p.Implies q.Not)
        _ = ((u p).Implies (u q.Not)).Not := by rw [u.implication p q.Not]
        _ = ((u p).Implies (u q).Not).Not := by rw [u.negation q]
      )
      have : (vp.Implies vq.Not).Not = TruthValue.True := Eq.trans this.symm h
      have : (vp.Implies vq.Not).Not.Not = TruthValue.False := congrArg TruthValue.Not this
      have : vp.Implies vq.Not = TruthValue.False := Eq.trans (TruthValue.double_negation (vp.Implies vq.Not)).symm this
      have hptnqf : vp = TruthValue.True ∧ vq.Not = TruthValue.False := TruthValue.not_implies vp vq.Not this
      have : vq.Not.Not = TruthValue.True := congrArg TruthValue.Not hptnqf.right
      have hqt : vq = TruthValue.True := Eq.trans (TruthValue.double_negation vq).symm this
      exact ⟨hptnqf.left, hqt⟩
    . intro h
      calc u (p.And q)
      _ = u (p.Implies q.Not).Not := rfl
      _ = (u (p.Implies q.Not)).Not := u.negation (p.Implies q.Not)
      _ = ((u p).Implies (u q.Not)).Not := by rw [u.implication p q.Not]
      _ = ((u p).Implies (u q).Not).Not := by rw [u.negation q]
      _ = (TruthValue.True.Implies TruthValue.True.Not).Not := by rw [h.left, h.right]

theorem or_definition (p q : Proposition) : u (p.Or q) = TruthValue.True ↔ u p = TruthValue.True ∨ u q = TruthValue.True := by
    apply Iff.intro
    . intro h
      have : (u p).Not.Implies (u q) = TruthValue.True := Eq.trans (calc u (p.Or q)
        _ = u (p.Not.Implies q) := rfl
        _ = (u p.Not).Implies (u q) := u.implication p.Not q
        _ = (u p).Not.Implies (u q) := by rw [u.negation p]
      ).symm h
      have hnpfqt : (u p).Not = TruthValue.False ∨ u q = TruthValue.True := TruthValue.implies (u p).Not (u q) this
      apply Or.elim hnpfqt
      . intro hnpf
        apply Or.inl
        have hnnpt : (u p).Not.Not = TruthValue.True := congrArg TruthValue.Not hnpf
        exact Eq.trans (TruthValue.double_negation (u p)).symm hnnpt
      . exact Or.inr
    . intro h_either
      apply Or.elim h_either
      . intro h
        calc u (p.Or q)
        _ = u (p.Not.Implies q) := rfl
        _ = (u p.Not).Implies (u q) := u.implication p.Not q
        _ = (u p).Not.Implies (u q) := by rw [u.negation p]
        _ = TruthValue.True.Not.Implies (u q) := by rw [h]
        _ = TruthValue.True := rfl
      . intro h
        calc u (p.Or q)
        _ = u (p.Not.Implies q) := rfl
        _ = (u p.Not).Implies (u q) := u.implication p.Not q
        _ = (u p).Not.Implies (u q) := by rw [u.negation p]
        _ = (u p).Not.Implies TruthValue.True := by rw [h]
        _ = TruthValue.True := match u p with
          | TruthValue.True => rfl
          | TruthValue.False => rfl

theorem iff_definition (p q : Proposition) : u (p.Iff q) = TruthValue.True ↔ u p = u q := by
  let vp := u p
  let vq := u q
  apply Iff.intro
  . intro h
    have ⟨h_forward_valuation, h_backward_valuation⟩ := (and_definition (p.Implies q) (q.Implies p)).mp h
    have h_forward_implication : vp = TruthValue.True → vq = TruthValue.True := (implies_definition p q).mp h_forward_valuation
    have h_backward_implication : vq = TruthValue.True → vp = TruthValue.True := (implies_definition q p).mp h_backward_valuation
    show vp = vq
    match vp, vq with
    | TruthValue.True, TruthValue.True => rfl
    | TruthValue.False, TruthValue.False => rfl
    | TruthValue.True, TruthValue.False => injection h_forward_implication rfl
    | TruthValue.False, TruthValue.True => injection h_backward_implication rfl
  . intro h
    have h_forward_implication : u p = TruthValue.True → u q = TruthValue.True := fun hpt => Eq.trans h.symm hpt
    have h_backward_implication : u q = TruthValue.True → u p = TruthValue.True := fun hqt => Eq.trans h hqt
    have h_forward_valuation : u (p.Implies q) = TruthValue.True := (implies_definition p q).mpr h_forward_implication
    have h_backward_valuation : u (q.Implies p) = TruthValue.True := (implies_definition q p).mpr h_backward_implication
    show u ((p.Implies q).And (q.Implies p)) = TruthValue.True
    exact (and_definition (p.Implies q) (q.Implies p)).mpr ⟨h_forward_valuation, h_backward_valuation⟩

theorem conjunction (p q : Proposition) : u (p.And q) = (u p).And (u q) := by
    calc u (p.And q)
    _ = u (p.Implies q.Not).Not := rfl
    _ = ((u p).Implies (u q).Not).Not := by rw [u.negation (p.Implies q.Not), u.implication p q.Not, u.negation q]
    _ = (u p).And (u q) := match u p, u q with
    | TruthValue.True, TruthValue.True => rfl
    | TruthValue.True, TruthValue.False => rfl
    | TruthValue.False, TruthValue.True => rfl
    | TruthValue.False, TruthValue.False => rfl

theorem disjunction (p q : Proposition) : u (p.Or q) = (u p).Or (u q) := by
    calc u (p.Or q)
    _ = u (p.Not.Implies q) := rfl
    _ = (u p).Not.Implies (u q) := by rw [u.implication p.Not q, u.negation p]
    _ = (u p).Or (u q) := match u p, u q with
    | TruthValue.True, TruthValue.True => rfl
    | TruthValue.True, TruthValue.False => rfl
    | TruthValue.False, TruthValue.True => rfl
    | TruthValue.False, TruthValue.False => rfl

theorem equivalence (p q : Proposition) : u (p.Iff q) = (u p).Iff (u q) := by
    calc u (p.Iff q)
    _ = u ((p.Implies q).And (q.Implies p)) := rfl
    _ = ((u p).Implies (u q)).And ((u q).Implies (u p)) := by simp [u.implication, u.conjunction]
    _ = (u p).Iff (u q) := match u p, u q with
    | TruthValue.True, TruthValue.True => rfl
    | TruthValue.True, TruthValue.False => rfl
    | TruthValue.False, TruthValue.True => rfl
    | TruthValue.False, TruthValue.False => rfl

theorem double_negation (p : Proposition) : u p.Not.Not = u p := calc u p.Not.Not
    _ = (u p).Not.Not := by rw [u.negation p.Not, u.negation p]
    _ = u p := TruthValue.double_negation (u p)

def satisfies (u : Valuation) (p : Proposition) : Prop := u p = TruthValue.True
def Satisfiable (p : Proposition) : Prop := ∃ u : Valuation, u.satisfies p
def Tautology (p : Proposition) : Prop := ∀ u : Valuation, u.satisfies p
def Contradiction (p : Proposition) : Prop := ∀ u : Valuation, ¬(u.satisfies p)

def satisfies_set (u : Valuation) (P : Set Proposition) := ∀ p : P, u.satisfies p
def satisfiable_set (A : Set Proposition) : Prop := ∃ u : Valuation, ∀ p : A, u.satisfies p

theorem satisfies_empty (u : Valuation) : u.satisfies_set ∅ := by
    intro (p : (∅ : Set Proposition))
    have : False := p.property
    contradiction

theorem p2_5_tautology (p : Proposition) : Tautology (p.Or p.Not) := by
    intro u
    calc u (p.Or p.Not)
    _ = (u p).Or (u p).Not := by rw [u.disjunction p p.Not, u.negation p]
    _ = TruthValue.True := match u p with
    | TruthValue.True => rfl
    | TruthValue.False => rfl

theorem p2_5_contradiction (p : Proposition) : Contradiction (p.Not.And p) := by
    intro u
    intro ht
    apply TruthValue.not_true_and_false (u (p.Not.And p))
    apply And.intro ht
    calc u (p.Not.And p)
    _ = (u p).Not.And (u p) := by rw [u.conjunction p.Not p, u.negation p]
    _ = TruthValue.False := match u p with
    | TruthValue.True => rfl
    | TruthValue.False => rfl

theorem tautology_contradiction (p : Proposition) : Tautology p ↔ Contradiction p.Not := by
    apply Iff.intro
    . intro h₀
      intro u
      have h₁ : u p = TruthValue.True := h₀ u
      have h₂ : (u p).Not = TruthValue.False := congrArg TruthValue.Not h₁
      have h₃ : u p.Not = TruthValue.False := Eq.trans (u.negation p) h₂
      intro h_false
      injection Eq.trans h_false.symm h₃
    . intro h₀
      intro u
      have h₁ : u p.Not ≠ TruthValue.True := h₀ u
      have h₂ : u p.Not = TruthValue.False := (TruthValue.not_true (u p.Not)).mp h₁
      have h₃ : (u p).Not = TruthValue.False := Eq.trans (u.negation p).symm h₂
      have h₄ : (u p).Not.Not = TruthValue.True := congrArg TruthValue.Not h₃
      show u p = TruthValue.True
      exact Eq.trans (TruthValue.double_negation (u p)).symm h₄

def entails (S : Set Proposition) (p : Proposition) : Prop := ∀ u : Valuation, u.satisfies_set S → u.satisfies p
infix:50 " ⊧ " => entails

theorem entails_tautology {p : Proposition} : ∅ ⊧ p ↔ Tautology p := by
apply Iff.intro
. intro h
  intro u
  exact h u (satisfies_empty u)
. intro h
  intro u
  intro _
  exact h u

theorem entails_contradiction (p : Proposition) : ∅ ⊧ p.Not ↔ Contradiction p := by
    apply Iff.intro
    . intro h
      have h_tautology : Tautology p.Not := entails_tautology.mp h
      have h_contradiction : Contradiction p.Not.Not := (tautology_contradiction p.Not).mp h_tautology
      intro u
      have h_rewritten_contradiction : ¬(u.function p.Not.Not = TruthValue.True) := h_contradiction u
      exact Eq.subst (motive := fun x => ¬(x = TruthValue.True)) (double_negation p) h_rewritten_contradiction
    . intro h_contradiction
      have h_rewritten_contradiction : ∀ u : Valuation, ¬ (u p = TruthValue.True) := h_contradiction
      have h_contradiction_double_negation : ∀ u : Valuation, ¬ (u p.Not.Not = TruthValue.True) := fun u => Eq.subst (motive := fun x => ¬ (x = TruthValue.True)) (double_negation p).symm (h_rewritten_contradiction u)
      have h_tautology : Tautology p.Not := (tautology_contradiction p.Not).mpr h_contradiction_double_negation
      exact entails_tautology.mpr h_tautology

theorem entails_subset (A B : Set Proposition) (h : A ⊆ B) : ∀ a : A, B ⊧ a := by
    intro ⟨a, ha⟩
    intro u
    intro h₁
    have h₂ : a ∈ B := (Set.for_all A (fun p => p ∈ B)).mp h a ha
    exact h₁ ⟨a, h₂⟩

theorem entails_member (A : Set Proposition) (p : Proposition) (h : p ∈ A) : A ⊧ p := entails_subset {p} A (Set.member_subset A p h) ⟨p, rfl⟩

theorem subset_entails {p : Proposition} (A B : Set Proposition) (h : A ⊆ B) : A ⊧ p → B ⊧ p := by
    intro h₀
    intro u
    have h₁ : u.satisfies_set A → u.satisfies p := h₀ u
    intro h₂
    apply h₁
    intro a
    exact h₂ ⟨a.val, h a⟩

theorem entails_additional (A : Set Proposition) (p q : Proposition) : (insert p A) ⊧ q ↔ A ⊧ (p.Implies q) := by
    apply Iff.intro
    . intro h₀
      intro u
      have h₁ : (∀ r : (insert p A : Set Proposition), u r = TruthValue.True) → u q = TruthValue.True := h₀ u
      let vp := u p
      let vq := u q
      have h₂ : (vp = TruthValue.True ∧ ∀ r : A, u r = TruthValue.True) → vq = TruthValue.True := fun h => h₁ ((Set.forall_insert A p (u · = TruthValue.True)).mpr h)
      intro (h₃ : ∀ p : A, u p = TruthValue.True)
      suffices vq = TruthValue.True ∨ vp.Implies vq = TruthValue.True by
        apply Or.elim this
        . intro h
          calc u (p.Implies q)
          _ = vp.Implies vq := u.implication p q
          _ = vp.Implies TruthValue.True := by rw [h]
          _ = TruthValue.True := TruthValue.implies_true vp
        . intro h
          calc u (p.Implies q)
          _ = vp.Implies vq := u.implication p q
          _ = TruthValue.True := h
      match vp, vq with
      | TruthValue.True, _ => exact Or.inl (h₂ ⟨rfl, h₃⟩)
      | TruthValue.False, TruthValue.True => exact Or.inl rfl
      | TruthValue.False, TruthValue.False => exact Or.inr rfl
    . intro h₀
      intro u
      have h₁ : (∀ r : A, u r = TruthValue.True) → u (p.Implies q) = TruthValue.True := h₀ u
      intro (h₂ : ∀ r : (insert p A : Set Proposition), u r = TruthValue.True)
      have h₃ : u p = TruthValue.True ∧ ∀ r : A, u r = TruthValue.True := (Set.forall_insert A p (u · = TruthValue.True)).mp h₂
      have h₄ : u (p.Implies q) = TruthValue.True := h₁ h₃.right
      exact (implies_definition p q).mp h₄ h₃.left

theorem satisfiable_entails_contradiction (A : Set Proposition) : satisfiable_set A ↔ ¬ ∃ p : Proposition, Contradiction p ∧ A ⊧ p := by
    apply Iff.intro
    . intro ⟨u, h₀⟩
      intro ⟨p, h₁⟩
      have h₂ : u.satisfies p := h₁.right u h₀
      have h₃ : ¬ (u.satisfies p) := h₁.left u
      contradiction
    . intro h₀
      have h₁ : ∀ p : Proposition, ¬ (Contradiction p ∧ A ⊧ p) := fun p h => h₀ ⟨p, h⟩
      let p₁ : Proposition := (Proposition.Atomic 0).Not.And (Proposition.Atomic 0)
      have h₂ : Contradiction p₁ := p2_5_contradiction (Proposition.Atomic 0)
      have h₃ : ¬ (Contradiction p₁ ∧ A ⊧ p₁) := h₁ p₁
      have h₄ : ¬ A ⊧ p₁ := fun h => h₃ ⟨h₂, h⟩
      have ⟨u, h₅⟩ : ∃ u : Valuation, ¬ (u.satisfies_set A → u.satisfies p₁) := by
        apply byContradiction
        intro h'₀
        have h'₁ : ∀ u : Valuation, u.satisfies_set A → u.satisfies p₁ := fun u => byContradiction fun h => h'₀ ⟨u, h⟩
        have h'₂ : A ⊧ p₁ := h'₁
        contradiction
      have h₆ : u.satisfies_set A := byContradiction fun h'₀ => h₅ (fun h'₁ => absurd h'₁ h'₀)
      exact ⟨u, h₆⟩

theorem p_implies_p_tautology (p : Proposition) : Tautology (p.Implies p) := by
      show Tautology (p.Implies p)
      intro u
      let vp := u p
      calc u (p.Implies p)
        _ = vp.Implies vp := u.implication p p
        _ = TruthValue.True := match vp with
        | TruthValue.True => rfl
        | TruthValue.False => rfl
end Valuation

-- I would make this a Prop (see Deduction.proves), but you apparently can't do structural recursion on a Prop
inductive Deduction (A : Set Proposition) : Proposition → Type where
    | Premiss {p : Proposition} (h : p ∈ A) : Deduction A p
    | A1 {p q : Proposition} : Deduction A (p.Implies (q.Implies p))
    | A2 {p q r : Proposition} : Deduction A ((p.Implies (q.Implies r)).Implies ((p.Implies q).Implies (p.Implies r)))
    | A3 {p q : Proposition} : Deduction A ((q.Not.Implies p.Not).Implies ((q.Not.Implies p).Implies q))
    | Mp {p q : Proposition} (d₁ : Deduction A p) (d₂ : Deduction A (p.Implies q)) :  Deduction A q

namespace Deduction
open Proposition
open Valuation

theorem a1_tautology {p q : Proposition} : Tautology (p.Implies (q.Implies p)) := by
    intro u
    apply (implies_definition p (q.Implies p)).mpr
    intro h
    calc u (q.Implies p)
    _ = (u q).Implies (u p) := u.implication q p
    _ = (u q).Implies TruthValue.True := by rw [h]
    _ = TruthValue.True := TruthValue.implies_true (u q)

theorem a2_tautology {p q r : Proposition} : Tautology ((p.Implies (q.Implies r)).Implies ((p.Implies q).Implies (p.Implies r))) := by
    intro u
    apply (implies_definition (p.Implies (q.Implies r)) ((p.Implies q).Implies (p.Implies r))).mpr
    intro h₁
    apply (implies_definition (p.Implies q) (p.Implies r)).mpr
    intro h₂
    apply (implies_definition p r).mpr
    intro h₃
    have h₄ : u q = TruthValue.True := (implies_definition p q).mp h₂ h₃
    have h₅ : u (q.Implies r) = TruthValue.True := ((implies_definition p (q.Implies r)).mp h₁ h₃)
    exact (implies_definition q r).mp h₅ h₄

theorem a3_tautology {p q : Proposition} : Tautology ((q.Not.Implies p.Not).Implies ((q.Not.Implies p).Implies q)) := by
    intro u
    apply (implies_definition (q.Not.Implies p.Not) ((q.Not.Implies p).Implies q)).mpr
    intro h₁
    apply (implies_definition (q.Not.Implies p) q).mpr
    intro h₂
    apply byContradiction
    intro h₃
    have h₄ : u q = TruthValue.False := (TruthValue.not_true (u q)).mp h₃
    have h₅ : u (q.Not) = TruthValue.True := by calc u (q.Not)
      _ = (u q).Not := u.negation q
      _ = TruthValue.False.Not := by rw [h₄]
    have h₆ : u p = TruthValue.True := (implies_definition q.Not p).mp h₂ h₅
    have h₇ : u p.Not = TruthValue.True := (implies_definition q.Not p.Not).mp h₁ h₅
    injection Eq.trans h₆.symm ((not_definition p).mp h₇)

theorem mp_valid (p q : Proposition) : {p, p.Implies q} ⊧ q := by
    intro u
    intro h₁
    have h₂ : u.satisfies p := h₁ ⟨p, Or.inl rfl⟩
    have h₃ : u.satisfies (p.Implies q) := h₁ ⟨p.Implies q, Or.inr rfl⟩
    exact (implies_definition p q).mp h₃ h₂

-- This is incredibly annoying to deal with, but sometimes you just need a Prop
def proves (A : Set Proposition) (p : Proposition) := ∃ _ : Deduction A p, True
infix:50 " ⊢ " => proves

theorem Premiss_proves {A : Set Proposition} {p : Proposition} (h : p ∈ A) : A ⊢ p := ⟨Premiss h, trivial⟩
theorem A1_proves {A : Set Proposition} {p q : Proposition} : A ⊢ (p.Implies (q.Implies p)) := ⟨A1, trivial⟩
theorem A2_proves {A : Set Proposition} {p q r : Proposition} : A ⊢ ((p.Implies (q.Implies r)).Implies ((p.Implies q).Implies (p.Implies r))) := ⟨A2, trivial⟩
theorem A3_proves {A : Set Proposition} {p q : Proposition} : A ⊢ ((q.Not.Implies p.Not).Implies ((q.Not.Implies p).Implies q)) := ⟨A3, trivial⟩
theorem Mp_proves {A : Set Proposition} {p q : Proposition} (p₁ : A ⊢ p) (p₂ : A ⊢ p.Implies q) :  A ⊢ q := ⟨Mp p₁.choose p₂.choose, trivial⟩

theorem subset_proves {p : Proposition} {A B : Set Proposition} : A ⊆ B → Deduction A p → B ⊢ p := by
    intro h₁
    intro d₁
    match d₁ with
    | Premiss h => exact Premiss_proves (h₁ ⟨p, h⟩)
    | A1 => exact A1_proves
    | A2 => exact A2_proves
    | A3 => exact A3_proves
    | @Mp A p q d'₁ d'₂ => exact Mp_proves (subset_proves h₁ d'₁) (subset_proves h₁ d'₂)

theorem deduction_trans (p : Proposition) (A B : Set Proposition) : (∀ b : B, A ⊢ b) → Deduction B p → A ⊢ p := by
    intro h₁
    intro d₁
    match d₁ with
    | Premiss h => exact h₁ ⟨p, h⟩
    | A1 => exact A1_proves
    | A2 => exact A2_proves
    | A3 => exact A3_proves
    | @Mp B p q d'₁ d'₂ => exact Mp_proves (deduction_trans p A B h₁ d'₁) (deduction_trans (p.Implies q) A B h₁ d'₂)

theorem p_implies_p {A : Set Proposition} {p : Proposition} : A ⊢ p.Implies p :=
    have h₁ : A ⊢ (p.Implies ((p.Implies p).Implies p)).Implies ((p.Implies (p.Implies p)).Implies (p.Implies p)) := A2_proves
    have h₂ : A ⊢ p.Implies ((p.Implies p).Implies p) := A1_proves
    have h₃ : A ⊢ (p.Implies (p.Implies p)).Implies (p.Implies p) := Mp_proves h₂ h₁
    have h₄ : A ⊢ p.Implies (p.Implies p) := A1_proves
    Mp_proves h₄ h₃

theorem p_implies_provable {A : Set Proposition} {p q : Proposition} (h : A ⊢ q) : A ⊢ p.Implies q := Mp_proves h A1_proves

theorem _deduction_theorem_reverse {A : Set Proposition} {p q : Proposition} (d : Deduction (insert p A) q) : A ⊢ p.Implies q := match d with
    | Premiss h => Or.elim h
      (fun h => Eq.subst (motive := fun x => A ⊢ p.Implies x) h.symm p_implies_p)
      (fun h => p_implies_provable (Premiss_proves h))
    | A1 => p_implies_provable A1_proves
    | A2 => p_implies_provable A2_proves
    | A3 => p_implies_provable A3_proves
    | @ Mp (insert p A) q r d₁ d₂ =>
      have h₁ : A ⊢ (p.Implies (q.Implies r)).Implies ((p.Implies q).Implies (p.Implies r)) := A2_proves
      have h₂ : A ⊢ (p.Implies q).Implies (p.Implies r) := Mp_proves (_deduction_theorem_reverse d₂) h₁
      show A ⊢ p.Implies r from Mp_proves (_deduction_theorem_reverse d₁) h₂

theorem deduction_theorem {A : Set Proposition} {p q : Proposition} : A ⊢ p.Implies q ↔ (insert p A) ⊢ q := by
    apply Iff.intro
    . intro h₁
      have h₂ : (insert p A) ⊢ p.Implies q := subset_proves (Set.insert_subset p A) h₁.choose
      have h₃ : (insert p A) ⊢ p := Premiss_proves (Or.inl rfl)
      exact Mp_proves h₃ h₂
    . intro d₁
      exact _deduction_theorem_reverse d₁.choose

theorem double_negation_elimination {A : Set Proposition} {p : Proposition} (h : A ⊢ p.Not.Not) : A ⊢ p :=
    have h₁ : A ⊢ (p.Not.Implies p.Not.Not).Implies ((p.Not.Implies p.Not).Implies p) := A3_proves
    have h₂ : A ⊢ p.Not.Implies p.Not.Not := p_implies_provable h
    have h₃ : A ⊢ (p.Not.Implies p.Not).Implies p := Mp_proves h₂ h₁
    Mp_proves p_implies_p h₃

theorem double_negation_elimination_implication {A : Set Proposition} {p : Proposition} : A ⊢ p.Not.Not.Implies p := deduction_theorem.mpr (double_negation_elimination (Premiss_proves (Or.inl rfl)))

theorem implication_trans {A : Set Proposition} {p q r : Proposition} (h₁ : A ⊢ p.Implies q) (h₂ : A ⊢ q.Implies r) : A ⊢ p.Implies r :=
    have h₃ : (insert p A) ⊢ q := deduction_theorem.mp h₁
    have h₄ : (insert p A) ⊢ q.Implies r := subset_proves (Set.insert_subset p A) h₂.choose
    have h₅ : (insert p A) ⊢ r := Mp_proves h₃ h₄
    deduction_theorem.mpr h₅
end Deduction

namespace SoundAndComplete
open Set
open Proposition
open Valuation
open Deduction

theorem sound {A : Set Proposition} {p : Proposition} : Deduction A p → A ⊧ p := by
    intro d
    match d with
    | Premiss h => exact entails_member A p h
    | A1 => exact subset_entails ∅ A Set.empty_subset (entails_tautology.mpr a1_tautology)
    | A2 => exact subset_entails ∅ A Set.empty_subset (entails_tautology.mpr a2_tautology)
    | A3 => exact subset_entails ∅ A Set.empty_subset (entails_tautology.mpr a3_tautology)
    | @Mp A q r d₁ d₂ =>
      intro u
      intro h₀
      show u.satisfies r
      have h₁ : u.satisfies q := sound d₁ u h₀
      have h₂ : u.satisfies (q.Implies r) := sound d₂ u h₀
      exact (implies_definition q r).mp h₂ h₁

def inconsistent (A : Set Proposition) : Prop := ∃ p : Proposition, A ⊢ (p.Implies p).Not
def consistent (A : Set Proposition) : Prop := ¬ inconsistent A

theorem satisfiable_consistent {A : Set Proposition} : satisfiable_set A → consistent A := by
    intro h₁
    intro ⟨p, h₂⟩
    have h₃ : A ⊧ (p.Implies p).Not := sound h₂.choose
    have h₄ : ¬ ∃ q : Proposition, Contradiction q ∧ A ⊧ q := (satisfiable_entails_contradiction A).mp h₁
    apply h₄
    apply Exists.intro (p.Implies p).Not
    constructor
    . exact (tautology_contradiction (p.Implies p)).mp (Valuation.p_implies_p_tautology p)
    . exact h₃

theorem generalised_explosion {A : Set Proposition} {p q : Proposition} (h₁ : A ⊢ p) (h₂ : A ⊢ p.Not) : A ⊢ q :=
    have h₃ : A ⊢ q.Not.Implies p.Not := p_implies_provable h₂
    have h₄ : A ⊢ q.Not.Implies p := p_implies_provable h₁
    have h₅ : A ⊢ (q.Not.Implies p.Not).Implies ((q.Not.Implies p).Implies q) := A3_proves
    have h₆ : A ⊢ (q.Not.Implies p).Implies q := Mp_proves h₃ h₅
    Mp_proves h₄ h₆

theorem explosion {A : Set Proposition} {p : Proposition} : inconsistent A → A ⊢ p := by
    intro ⟨a, h₀⟩
    have h₁ : A ⊢ (p.Not.Implies (a.Implies a).Not).Implies ((p.Not.Implies (a.Implies a)).Implies p) := A3_proves
    have h₂ : A ⊢ p.Not.Implies (a.Implies a).Not := p_implies_provable h₀
    have h₃ : A ⊢ (p.Not.Implies (a.Implies a)).Implies p := Mp_proves h₂ h₁
    exact Mp_proves (p_implies_provable p_implies_p) h₃

theorem inconsistent_finite_subset {A : Set Proposition} : inconsistent A → ∃ B : Set Proposition, B ⊆ A ∧ FiniteProp B ∧ inconsistent B := by
    intro ⟨p, h₀⟩
    have ⟨B, h₁⟩ : ∃ B : Set Proposition, B ⊆ A ∧ FiniteProp B ∧ B ⊢ (p.Implies p).Not := recursive (p.Implies p).Not h₀.choose
    apply Exists.intro B
    constructor
    . exact h₁.left
    . constructor
      . exact h₁.right.left
      . exact ⟨p, h₁.right.right⟩
  where
    recursive (p : Proposition) (d₀ : Deduction A p) : ∃ B : Set Proposition, B ⊆ A ∧ FiniteProp B ∧ B ⊢ p := match d₀ with
    | Premiss h => ⟨{p}, fun x => Eq.subst x.property.symm h, FiniteProp.Singleton p, Premiss_proves rfl⟩
    | A1 => ⟨∅, empty_subset, FiniteProp.Empty, A1_proves⟩
    | A2 => ⟨∅, empty_subset, FiniteProp.Empty, A2_proves⟩
    | A3 => ⟨∅, empty_subset, FiniteProp.Empty, A3_proves⟩
    | @Mp A p q d₁ d₂ =>
      have ⟨B₁, h₁⟩ : ∃ B₁ : Set Proposition, B₁ ⊆ A ∧ FiniteProp B₁ ∧ B₁ ⊢ p := recursive p d₁
      have ⟨B₂, h₂⟩ : ∃ B₂ : Set Proposition, B₂ ⊆ A ∧ FiniteProp B₂ ∧ B₂ ⊢ p.Implies q := recursive (p.Implies q) d₂
      let B := B₁ ∪ B₂
      have h₃ : B ⊆ A := union_subset B₁ B₂ A h₁.left h₂.left
      have h₄ : FiniteProp B := FiniteProp.Union h₁.right.left h₂.right.left
      have h₅ : B ⊢ p := subset_proves subset_union_left h₁.right.right.choose
      have h₆ : B ⊢ p.Implies q := subset_proves subset_union_right h₂.right.right.choose
      have h₇ : B ⊢ q := Mp_proves h₅ h₆
      ⟨B, h₃, h₄, h₇⟩

theorem finite_subsets_consistent {A : Set Proposition} : consistent A ↔ ∀ B : Set Proposition, B ⊆ A → FiniteProp B → consistent B := by
    apply Iff.intro
    . intro h₀
      intro B
      intro h₁ _h₂ ⟨p, h₃⟩
      apply h₀
      apply Exists.intro p
      show A ⊢ (p.Implies p).Not
      exact subset_proves h₁ h₃.choose
    . intro h₀
      intro h₁
      have ⟨B, h₂, h₃, h₄⟩ : ∃ B : Set Proposition, B ⊆ A ∧ FiniteProp B ∧ inconsistent B := inconsistent_finite_subset h₁
      exact h₀ B h₂ h₃ h₄

theorem inconsistent_subset {A B : Set Proposition} (h₀ : A ⊆ B) : inconsistent A → inconsistent B := by
    intro ⟨p, h₁⟩
    exact ⟨p, subset_proves h₀ h₁.choose⟩

theorem proves_assumption {A : Set Proposition} {p : Proposition} (h₀ : A ⊢ p) : ∀ q : Proposition, insert p A ⊢ q ↔ A ⊢ q := by
    intro q
    apply Iff.intro
    . intro h₁
      exact mp_recursion h₀.choose h₁.choose
    . intro h₁
      exact subset_proves (insert_subset p A) h₁.choose
  where
    mp_recursion {p q : Proposition} (d₁ : Deduction A p) (d₂ : Deduction (insert p A) q) : A ⊢ q := match d₂ with
    | Premiss h => match h with
      | Or.inl h => Eq.subst (motive := fun a => A ⊢ a) h.symm ⟨d₁, trivial⟩
      | Or.inr h => Premiss_proves h
    | A1 => A1_proves
    | A2 => A2_proves
    | A3 => A3_proves
    | Mp d'₁ d'₂ => Mp_proves (mp_recursion d₁ d'₁) (mp_recursion d₁ d'₂)

def maximallyConsistent (A : Set Proposition) : Prop := consistent A ∧ ∀ p : Proposition, p ∉ A → inconsistent (insert p A)

theorem maximally_consistent_from_valuation {v : Valuation} : maximallyConsistent (Set.mk (fun p => v.satisfies p)) := by
    let A := Set.mk (fun p => v.satisfies p)
    constructor
    . exact satisfiable_consistent ⟨v, fun x => x.property⟩
    . intro p
      intro (h₀ : ¬ v.satisfies p)
      apply Exists.intro p
      have h₁ : v.satisfies p.Not := (not_definition p).mpr ((TruthValue.not_true (v p)).mp h₀)
      have h₂ : A ⊢ p.Not := Premiss_proves h₁
      have h₃ : (insert p A) ⊢ p.Not := subset_proves (insert_subset p A) h₂.choose
      have h₄ : (insert p A) ⊢ p := Premiss_proves (Or.inl rfl)
      exact generalised_explosion h₄ h₃

theorem maximally_consistent_proves {A : Set Proposition} {p : Proposition} (h₁ : maximallyConsistent A) (h₂ : A ⊢ p) : p ∈ A := by
    apply byContradiction
    intro h₃
    have ⟨q, h₄⟩ : inconsistent (insert p A) := h₁.right p h₃
    have h₅ : inconsistent A := ⟨q, (proves_assumption h₂ (q.Implies q).Not).mp h₄⟩
    exact h₁.left h₅

theorem maximally_consistent_proves_negation {A : Set Proposition} {p : Proposition} (h₀ : maximallyConsistent A) : A ⊢ p.Not ↔ p ∉ A := by
    apply Iff.intro
    . intro h₁
      intro h₂
      have h₃ : A ⊢ p := Premiss_proves h₂
      apply h₀.left
      apply Exists.intro p
      exact generalised_explosion h₃ h₁
    . intro h₁
      have h₂ : inconsistent (insert p A) := h₀.right p h₁
      have h₃ : (insert p A) ⊢ p.Not := explosion h₂
      have h₄ : A ⊢ p.Implies p.Not := deduction_theorem.mpr h₃
      have h₅ : A ⊢ p.Implies p := p_implies_p
      have h₆ : A ⊢ p.Not.Not.Implies p.Not := implication_trans double_negation_elimination_implication h₄
      have h₇ : A ⊢ p.Not.Not.Implies p := implication_trans double_negation_elimination_implication h₅
      have h₈ : A ⊢ (p.Not.Not.Implies p.Not).Implies ((p.Not.Not.Implies p).Implies p.Not) := A3_proves
      exact Mp_proves h₇ (Mp_proves h₆ h₈)

theorem maximally_consistent_includes_implication {A : Set Proposition} {p q : Proposition} (h : maximallyConsistent A) : p.Implies q ∈ A ↔ p ∉ A ∨ q ∈ A := by
    apply Iff.intro
    . intro h₀
      apply byContradiction
      intro h₁
      have h₂ : p ∈ A := not_not.mp (fun h => h₁ (Or.inl h))
      have h₃ : q ∉ A := fun h => h₁ (Or.inr h)
      have h₄ : A ⊢ q := Mp_proves (Premiss_proves h₂) (Premiss_proves h₀)
      exact h₃ (maximally_consistent_proves h h₄)
    . intro h₀
      apply Or.elim h₀
      . intro h₀
        apply maximally_consistent_proves h
        have h₁ : A ⊢ p.Not := (maximally_consistent_proves_negation h).mpr h₀
        have h₂ : (insert p A) ⊢ p := Premiss_proves (Or.inl rfl)
        have h₃ : (insert p A) ⊢ p.Not := subset_proves (insert_subset p A) h₁.choose
        have h₄ : (insert p A) ⊢ q := generalised_explosion h₂ h₃
        exact deduction_theorem.mpr h₄
      . intro h₀; exact maximally_consistent_proves h (p_implies_provable (Premiss_proves h₀))

--theorem maximally_consistent_superset {A : Set Proposition} (h : consistent A) : ∃ B : Set Proposition, A ⊆ B ∧ maximallyConsistent B := sorry
end SoundAndComplete
end propositional
