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

instance {α : Type u} : HasSSubset (Set α) where
  SSubset a b := a ≠ b ∧ ∀ x : a, x.val ∈ b

instance {α : Type u} : Union (Set α) where
  union S T := Set.mk (fun x => S.predicate x ∨ T.predicate x)

instance {α : Type u} : Inter (Set α) where
  inter S T := Set.mk (fun x => S.predicate x ∧ T.predicate x)

instance {α : Type u} : Sub (Set α) where
  sub S T := Set.mk fun x => x ∈ S ∧ x ∉ T

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

theorem subset_self (S : Set α) : S ⊆ S := fun x => x.property

theorem subset_trans {S T U : Set α} (h₁ : S ⊆ T) (h₂ : T ⊆ U) : S ⊆ U := fun x => h₂ ⟨x.val, h₁ x⟩

theorem subset_union_left {S T : Set α} : S ⊆ (S ∪ T) := fun x => Or.inl x.property
theorem subset_union_right {S T : Set α} : T ⊆ (S ∪ T) := fun x => Or.inr x.property

theorem ssubset_subset {S T : Set α} : S ⊂ T → S ⊆ T := And.right

theorem ssubset_trans_subset {S T U : Set α} (h₁ : S ⊂ T) (h₂ : T ⊆ U) : S ⊂ U := by
  constructor
  . intro h
    apply h₁.left
    apply setext
    intro y
    apply Iff.intro
    . intro h; exact h₁.right ⟨y, h⟩
    . intro h'; rw [h]; exact h₂ ⟨y, h'⟩
  . exact subset_trans h₁.right h₂

theorem ssubset_trans {S T U : Set α} (h₁ : S ⊂ T) (h₂ : T ⊂ U) : S ⊂ U := ssubset_trans_subset h₁ h₂.right

theorem union_symm {S T : Set α} : S ∪ T = T ∪ S := setext (S ∪ T) (T ∪ S) (fun _ => ⟨Or.symm, Or.symm⟩)

theorem insert_as_union (S : Set α) (x : α) : insert x S = {x} ∪ S := rfl

theorem union_subset (S T U : Set α) (h₁ : S ⊆ U) (h₂ : T ⊆ U) : (S ∪ T) ⊆ U := by
    intro x
    apply Or.elim x.property
    . intro h; exact h₁ ⟨x.val, h⟩
    . intro h; exact h₂ ⟨x.val, h⟩

theorem intersection_subset_left (S T : Set α) : (S ∩ T) ⊆ S := fun x => x.property.left
theorem intersection_subset_right (S T : Set α) : (S ∩ T) ⊆ T := fun x => x.property.right

theorem union_empty (S : Set α) : S = (S ∪ ∅) := by
  apply setext
  intro x
  apply Iff.intro
  . intro h; exact Or.inl h
  . intro h
    apply Or.elim h
    . intro h; exact h
    . exact False.elim

theorem intersection_empty (S : Set α) : ∅ = (S ∩ ∅) := by
  apply setext
  intro x
  apply Iff.intro
  . exact False.elim
  . exact And.right

theorem insert_into_union_right (x : α) (S T : Set α) : (insert x (S ∪ T)) = (S ∪ (insert x T)) := by
  apply setext
  intro y
  apply Iff.intro
  . intro h₀
    match h₀ with
    | Or.inl h₁ => exact Or.inr (Or.inl h₁)
    | Or.inr h₁ => match h₁ with
      | Or.inl h₂ => exact Or.inl h₂
      | Or.inr h₂ => exact Or.inr (Or.inr h₂)
  . intro h₀
    match h₀ with
    | Or.inl h₁ => exact Or.inr (Or.inl h₁)
    | Or.inr h₁ => match h₁ with
      | Or.inl h₂ => exact Or.inl h₂
      | Or.inr h₂ => exact Or.inr (Or.inr h₂)

theorem sub_subset (S T : Set α) : S - T ⊆ S := fun x => x.property.left
theorem sub_disjoint (S T : Set α) : ∀ x : S - T, x.val ∉ T := fun x => x.property.right

inductive Finite.{u} : Set α → Type u where
    | Empty : Finite ∅
    | Insert : {S : Set α} → (x : α) → Finite S → Finite (insert x S)

namespace Finite
def Singleton (x : α) : Finite {x} := by
  rw [←empty_insert x]
  exact Finite.Empty.Insert x

def Union {S T : Set α} (f₁ : Finite S) (f₂ : Finite T) : Finite (S ∪ T) := match f₂ with
  | Empty => by
    rw [←union_empty S]
    exact f₁
  | Insert x f₃ => by
    rw [←insert_into_union_right]
    apply Finite.Insert
    exact Union f₁ f₃

def Intersection {T : Set α} (S : Set α) [∀ x : α, Decidable (S.predicate x)] (f : Finite T) : Finite (S ∩ T) := match f with
  | Empty => by
    rw [←intersection_empty]
    exact Finite.Empty
  | @Insert _ T' x f₁ => by
    apply @Decidable.byCases (x ∈ S)
    . intro h₀
      have h₁ : S ∩ (insert x T') = insert x (S ∩ T') := by
        apply setext
        intro y
        apply Iff.intro
        . intro h
          match h.right with
          | Or.inl h => exact Or.inl h
          | Or.inr h' => exact Or.inr ⟨h.left, h'⟩
        . intro h
          apply And.intro
          . match h with
            | Or.inl h_eq => rw [h_eq]; exact h₀
            | Or.inr h' => exact h'.left
          . match h with
            | Or.inl h => exact Or.inl h
            | Or.inr h => exact Or.inr h.right
      rw [h₁]
      apply Finite.Insert
      exact Intersection S f₁
    . intro h₀
      have h₁ : S ∩ (insert x T') = S ∩ T' := by
        apply setext
        intro y
        apply Iff.intro
        . intro h
          apply And.intro
          . exact h.left
          . apply Or.resolve_left h.right
            intro h'
            rw [←h'] at h₀
            exact h₀ h.left
        . intro h
          apply And.intro
          . exact h.left
          . exact Or.inr h.right
      rw [h₁]
      exact Intersection S f₁
end Finite

def FiniteProp (S : Set α) := ∃ _ : Finite S, True

namespace FiniteProp
theorem Empty : FiniteProp (∅ : Set α) := ⟨Finite.Empty, trivial⟩
theorem Insert {S : Set α} : (x : α) → FiniteProp S → FiniteProp (insert x S) := (⟨Finite.Insert · ·.choose, trivial⟩)
theorem Singleton (x : α) : FiniteProp {x} := ⟨Finite.Singleton x, trivial⟩
theorem Union {S T : Set α} : FiniteProp S → FiniteProp T → FiniteProp (S ∪ T) := (⟨Finite.Union ·.choose ·.choose, trivial⟩)
theorem Intersection {T : Set α} : (S : Set α) → FiniteProp T → FiniteProp (S ∩ T) := (⟨Finite.Intersection · ·.choose, trivial⟩)

theorem Subset (S T : Set α) (h : S ⊆ T) (f : FiniteProp T) : FiniteProp S := by
  have h₁ : S = (S ∩ T) := by
    apply setext
    intro x
    apply Iff.intro
    . intro h₂
      exact ⟨h₂, h ⟨x, h₂⟩⟩
    . exact And.left
  rw [h₁]
  exact Intersection S f
end FiniteProp

def max_rank_of_finite {S : Set α} (rank : α → Nat) (f : Finite S) : Nat := match f with
  | Finite.Empty => 0
  | Finite.Insert x f' => max (rank x) (max_rank_of_finite rank f')

theorem max_rank_of_finite_ge_all {S : Set α} (rank : α → Nat) (f : Finite S) : ∀ x : S, max_rank_of_finite rank f ≥ rank x := match f with
  | Finite.Empty => fun x => False.elim x.property
  | Finite.Insert x f' => fun y =>
    match y.property with
    | Or.inl h => Eq.subst (congrArg rank h).symm (Nat.le_max_left (rank x) (max_rank_of_finite rank f'))
    | Or.inr h =>
    have h₁ : max_rank_of_finite rank (Finite.Insert x f') ≥ max_rank_of_finite rank f' := Nat.le_max_right (rank x) (max_rank_of_finite rank f')
    have h₂ : max_rank_of_finite rank f' ≥ rank y := max_rank_of_finite_ge_all rank f' ⟨y.val, h⟩
    Nat.le_trans h₂ h₁

theorem all_of_unbounded_infinite {S : Set α} (rank : α → Nat) (of_at_least_rank : Nat → S) (h : ∀ n : Nat, rank (of_at_least_rank n) ≥ n) : ¬FiniteProp S := by
    intro finite
    let max_rank := max_rank_of_finite rank finite.choose
    have h₀ : ∀x : S, max_rank ≥ rank x := max_rank_of_finite_ge_all rank finite.choose
    let not_present := of_at_least_rank (max_rank + 1)
    have h_not_present : rank not_present ≥ max_rank + 1 := h (max_rank + 1)
    have h₂ : ∀ x : S, rank not_present > rank x := fun n => by
      apply Nat.le_trans
      exact Nat.lt_succ_of_le (h₀ n)
      exact h_not_present
    have h₃ : ∀ x : S, rank not_present ≠ rank x := fun n => Nat.ne_iff_lt_or_gt.mpr (Or.inr (h₂ n))
    have h₄ : ∀ x : S, not_present ≠ x := fun x h => h₃ x (congrArg rank (Subtype.eq_iff.mp h))
    have h₅ : not_present.val ∉ S := fun h => h₄ ⟨not_present, h⟩ rfl
    exact h₅ not_present.property

theorem all_of_inductive_infinite (rank : α → Nat) (of_rank : Nat → α) (h : ∀ n : Nat, rank (of_rank n) = n) : ¬FiniteProp (All α) :=
all_of_unbounded_infinite rank (fun rank => ⟨of_rank rank, trivial⟩) (fun x => Nat.le_of_eq (h x).symm)

theorem all_nats_infinite : ¬FiniteProp (All Nat) := all_of_inductive_infinite id id (fun _ => rfl)

theorem infinite_sets_contain_element (S : Set α) (h : ¬ FiniteProp S) : ∃ _x : S, True := by
  apply byContradiction
  intro h₁'
  have h₁ : ∀ x : α, x ∉ S := fun x h => h₁' ⟨⟨x, h⟩, trivial⟩
  have h₂ : ∀ x : α, x ∈ S ↔ False := fun x => ⟨h₁ x, False.elim⟩
  have h₃ : S = ∅ := setext S ∅ h₂
  apply h
  rw [h₃]
  exact FiniteProp.Empty

theorem infinite_minus_singleton_infinite {S : Set α} (i : ¬ FiniteProp S) (x : S) : ¬ FiniteProp (S - {x.val}) := by
  intro finite
  have h₁ : S = (S - {x.val}) ∪ {x.val} := by
    apply setext
    intro y
    apply Iff.intro
    . intro h
      cases em (y = x.val) with
      | inl h_eq => exact Or.inr h_eq
      | inr h_neq => exact Or.inl ⟨h, h_neq⟩
    . intro h
      cases h with
      | inl h => exact h.left
      | inr h => rw [h]; exact x.property
  rw [h₁] at i
  apply i
  apply FiniteProp.Union
  . exact finite
  . rw [union_empty {x.val}]
    exact FiniteProp.Insert x.val FiniteProp.Empty

theorem infinite_of_infinite_subset {S : Set α} (i : ¬ FiniteProp S) (T : Set α) (h : S ⊆ T) : ¬ FiniteProp T := by
  intro finite
  have h₁ : FiniteProp S := FiniteProp.Subset S T h finite
  exact i h₁

def InfiniteSet (α : Type u) := {x : Set α // ¬ FiniteProp x}

namespace _of_nat
noncomputable def of_nat_with_remaining (S : InfiniteSet α) (n : Nat) : S.val × {T : InfiniteSet α // T.val ⊆ S.val} :=
  let previous_remaining : {T : InfiniteSet α // T.val ⊆ S.val} := match n with
    | 0 => ⟨S, subset_self S.val⟩
    | k+1 => (of_nat_with_remaining S k).snd
  let val : previous_remaining.val.val := (infinite_sets_contain_element previous_remaining.val.val previous_remaining.val.property).choose
  have h₁ : val.val ∈ S.val := previous_remaining.property val
  have h₂ : previous_remaining.val.val - {val.val} ⊆ S.val := subset_trans (sub_subset previous_remaining.val.val {val.val}) previous_remaining.property
  have h₃ : ¬ FiniteProp (previous_remaining.val.val - {val.val}) := infinite_minus_singleton_infinite previous_remaining.val.property val
  ⟨⟨val.val, h₁⟩, ⟨⟨previous_remaining.val.val - {val.val}, h₃⟩, h₂⟩⟩

theorem of_nat_val_nin_remaining (S : InfiniteSet α) (n : Nat) : (of_nat_with_remaining S n).fst.val ∉ (of_nat_with_remaining S n).snd.val.val := by
  let previous_remaining : {T : InfiniteSet α // T.val ⊆ S.val} := match n with
    | 0 => ⟨S, subset_self S.val⟩
    | k+1 => (of_nat_with_remaining S k).snd
  let val : previous_remaining.val.val := (infinite_sets_contain_element previous_remaining.val.val previous_remaining.val.property).choose
  unfold of_nat_with_remaining
  show val.val ∉ previous_remaining.val.val - {val.val}
  intro h
  exact h.right rfl

theorem of_nat_val_in_previous_remaining (S : InfiniteSet α) (n : Nat) : (of_nat_with_remaining S n.succ).fst.val ∈ (of_nat_with_remaining S n).snd.val.val := by
  let previous_remaining := (of_nat_with_remaining S n).snd
  show (infinite_sets_contain_element previous_remaining.val.val previous_remaining.val.property).choose.val ∈ previous_remaining.val.val
  exact (infinite_sets_contain_element previous_remaining.val.val previous_remaining.val.property).choose.property

theorem of_nat_remaining_subset_succ (S : InfiniteSet α) (n : Nat) : (of_nat_with_remaining S n.succ).snd.val.val ⊆ (of_nat_with_remaining S n).snd.val.val := by
  let nth := of_nat_with_remaining S n
  let succ_nth := of_nat_with_remaining S n.succ
  show (nth.snd.val.val - {succ_nth.fst.val}) ⊆ nth.snd.val.val
  exact sub_subset nth.snd.val.val {succ_nth.fst.val}

theorem of_nat_remaining_ne_succ (S : InfiniteSet α) (n : Nat) : (of_nat_with_remaining S n).snd.val.val ≠ (of_nat_with_remaining S n.succ).snd.val.val := by
  let previous_remaining := (of_nat_with_remaining S n).snd
  intro h₁
  have h₂ : (of_nat_with_remaining S n.succ).fst.val ∈ previous_remaining.val.val := of_nat_val_in_previous_remaining S n
  have h₃ : (of_nat_with_remaining S n.succ).fst.val ∈ (of_nat_with_remaining S n.succ).snd.val.val := Eq.subst (motive := ((of_nat_with_remaining S n.succ).fst.val ∈ ·)) h₁ h₂
  exact of_nat_val_nin_remaining S n.succ h₃

theorem of_nat_remaining_ssubset_succ (S : InfiniteSet α) (n : Nat) : (of_nat_with_remaining S n.succ).snd.val.val ⊂ (of_nat_with_remaining S n).snd.val.val := ⟨(of_nat_remaining_ne_succ S n).symm, of_nat_remaining_subset_succ S n⟩

theorem of_nat_remaining_ssubset_add (S : InfiniteSet α) (n k : Nat) : (of_nat_with_remaining S (n+k.succ)).snd.val.val ⊂ (of_nat_with_remaining S n).snd.val.val := match k with
  | 0 => of_nat_remaining_ssubset_succ S n
  | j+1 => by
    have ih : (of_nat_with_remaining S (n+j.succ)).snd.val.val ⊂ (of_nat_with_remaining S n).snd.val.val := of_nat_remaining_ssubset_add S n j
    have h₁ : (of_nat_with_remaining S (n+j.succ.succ)).snd.val.val ⊂ (of_nat_with_remaining S (n+j.succ)).snd.val.val := of_nat_remaining_ssubset_succ S (n+j.succ)
    exact ssubset_trans h₁ ih

theorem of_nat_remaining_ssubset_lt (S : InfiniteSet α) (a b : Nat) (h : a < b) : (of_nat_with_remaining S b).snd.val.val ⊂ (of_nat_with_remaining S a).snd.val.val := by
  have ⟨k, h₁⟩ : ∃ k : Nat, b = a+k.succ := Nat.exists_eq_add_of_lt h
  rw [h₁]
  exact of_nat_remaining_ssubset_add S a k

theorem of_nat_remaining_subset_le (S : InfiniteSet α) (a b : Nat) (h : a ≤ b) : (of_nat_with_remaining S b).snd.val.val ⊆ (of_nat_with_remaining S a).snd.val.val := by
  match Nat.le_iff_lt_or_eq.mp h with
  | Or.inr h_eq => rw [h_eq]; exact subset_self (of_nat_with_remaining S b).snd.val.val
  | Or.inl h_lt => exact (of_nat_remaining_ssubset_lt S a b h_lt).right

theorem of_nat_val_nin_remaining_le (S : InfiniteSet α) (a b : Nat) (h : a ≤ b) : (of_nat_with_remaining S a).fst.val ∉ (of_nat_with_remaining S b).snd.val.val := by
  intro h'
  have h₁ : (of_nat_with_remaining S b).snd.val.val ⊆ (of_nat_with_remaining S a).snd.val.val := of_nat_remaining_subset_le S a b h
  have h₂ : (of_nat_with_remaining S a).fst.val ∈ (of_nat_with_remaining S a).snd.val.val := h₁ ⟨(of_nat_with_remaining S a).fst.val, h'⟩
  exact of_nat_val_nin_remaining S a h₂

theorem of_nat_val_in_remaining_gt (S : InfiniteSet α) (a b : Nat) (h :a > b) : (of_nat_with_remaining S a).fst.val ∈ (of_nat_with_remaining S b).snd.val.val := by
  have ⟨k, h₁⟩ : ∃ k : Nat, a = k.succ := match a with
    | 0 => False.elim (Nat.not_lt_zero b h)
    | k+1 => ⟨k, rfl⟩
  rw [h₁] at h
  rw [h₁]
  have h₂ : k ≥ b := Nat.le_of_lt_succ h
  have h₃ : (of_nat_with_remaining S k).snd.val.val ⊆ (of_nat_with_remaining S b).snd.val.val := of_nat_remaining_subset_le S b k h₂
  have h₄ : (of_nat_with_remaining S k.succ).fst.val ∈ (of_nat_with_remaining S k).snd.val.val := of_nat_val_in_previous_remaining S k
  exact h₃ ⟨(of_nat_with_remaining S k.succ).fst.val, h₄⟩

theorem of_nat_val_ne_lt (S : InfiniteSet α) (a b : Nat) (h : a < b) : (of_nat_with_remaining S a).fst.val ≠ (of_nat_with_remaining S b).fst.val := by
  intro h'
  apply of_nat_val_nin_remaining S a
  rw [h']
  exact of_nat_val_in_remaining_gt S b a h

theorem of_nat_val_injective (S : InfiniteSet α) (a b : Nat) : (of_nat_with_remaining S a).fst.val = (of_nat_with_remaining S b).fst.val → a = b := by
  intro h
  apply byContradiction
  intro h₁'
  match Nat.ne_iff_lt_or_gt.mp h₁' with
  | Or.inl h_lt => exact of_nat_val_ne_lt S a b h_lt h
  | Or.inr h_gt => exact of_nat_val_ne_lt S b a h_gt h.symm

noncomputable def of_rank (S : InfiniteSet α) (n : Nat) : S.val := (of_nat_with_remaining S n).fst

theorem of_rank_injective (S : InfiniteSet α) (a b : Nat) : of_rank S a = of_rank S b → a = b := by
  intro h
  have h₁ : (of_nat_with_remaining S a).fst.val = (of_nat_with_remaining S b).fst.val := congrArg Subtype.val h
  exact of_nat_val_injective S a b h₁

noncomputable def rank (S : InfiniteSet α) (x : S.val) : Nat :=
  if h : ∃ n : Nat, x = of_rank S n then
    h.choose
  else
    0

theorem rank_of_rank (S : InfiniteSet α) (n : Nat) : rank S (of_rank S n) = n := by
  unfold rank
  have h₁ : ∃ m : Nat, of_rank S n = of_rank S m := ⟨n, rfl⟩
  split
  . show h₁.choose = n
    exact of_rank_injective S h₁.choose n h₁.choose_spec.symm
  . contradiction
end _of_nat

theorem infinite_iff_surjective_to_nat (S : Set α) : ¬ FiniteProp S ↔ ∃ f : S → Nat, ∀ n : Nat, ∃ x : S, n = f x := by
  apply Iff.intro
  . intro h
    let f := _of_nat.rank ⟨S, h⟩
    apply Exists.intro f
    intro n
    let x := _of_nat.of_rank ⟨S, h⟩ n
    apply Exists.intro x
    exact (_of_nat.rank_of_rank ⟨S, h⟩ n).symm
  . intro h
    let rank : α → Nat := fun x => if h' : x ∈ S then h.choose ⟨x, h'⟩ else 0
    let of_rank : Nat → S := fun n => (h.choose_spec n).choose
    apply all_of_unbounded_infinite rank of_rank
    intro n
    apply Nat.le_of_eq
    have h₁ : (of_rank n).val ∈ S := (of_rank n).property
    unfold rank
    split
    . exact (h.choose_spec n).choose_spec
    . contradiction

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

theorem infinite_equal_cardonality_infinite {S : Set α} {T : Set β} (h : equalCardinality S T) : ¬ FiniteProp S → ¬ FiniteProp T := by
  have h' : equalCardinality T S := equal_cardinality_symm h
  intro h₁
  have ⟨f₁, h₂⟩ : ∃ f : S → Nat, ∀ n : Nat, ∃ x : S, n = f x := (infinite_iff_surjective_to_nat S).mp h₁
  have ⟨f₂, h₃⟩ : ∃ f : T → S, ∀ y : S, ∃ x : T, f x = y := ⟨h'.choose, h'.choose_spec.right⟩
  let f₃ : T → Nat := f₁ ∘ f₂
  apply (infinite_iff_surjective_to_nat T).mpr
  apply Exists.intro f₃
  intro n
  let x : T := (h₃ (h₂ n).choose).choose
  apply Exists.intro x
  show n = f₁ (f₂ x)
  rw [(h₃ (h₂ n).choose).choose_spec]
  exact (h₂ n).choose_spec

def Countable (S : Set α) : Prop := ∃ f : S → Nat, ∀ x₁ x₂ : S, f x₁ = f x₂ → x₁ = x₂

namespace Countable
theorem any_natural_numbers_countable (S : Set Nat) : Countable S := by
  let f : S → Nat := fun x => x.val
  apply Exists.intro f
  intro x₁ x₂
  unfold f
  intro h
  exact Subtype.eq h

def pair (a b : Nat) : Nat := 2^a*3^b

theorem pair_not_zero (a b : Nat) : pair a b ≠ 0 := by
  intro h'
  have h₁ : 2^a = 0 ∨ 3^b = 0 := Nat.mul_eq_zero.mp h'
  apply Or.elim h₁
  . intro h₁'
    have h₂ : 1 < 2 := by decide
    have h₃ : 1 ≤ 2^a := (Nat.pow_le_pow_iff_right h₂).mpr (Nat.zero_le a)
    have h₄ : 1 ≤ 0 := Eq.subst h₁' h₃
    contradiction
  . intro h₁'
    have h₂ : 1 < 3 := by decide
    have h₃ : 1 ≤ 3^b := (Nat.pow_le_pow_iff_right h₂).mpr (Nat.zero_le b)
    have h₄ : 1 ≤ 0 := Eq.subst h₁' h₃
    contradiction

def unpair_left (p : Nat) : Nat :=
  if p = 0 then
    0
  else if h₁ : 2 ∣ p then
    unpair_left (p/2) + 1
  else
    0
def unpair_right (p : Nat) : Nat :=
  if p = 0 then
    0
  else if 3 ∣ p then
    unpair_right (p/3) + 1
  else
    0

theorem euclids_lemma_2_3 (k : Nat) : 2 ∣ 3*k → 2 ∣ k := match k with
  |0 => by decide
  | 1 => by decide
  | j+2 => by
    intro (h : 2 ∣ 3*(j+2))
    have h₁ : 3*(j+2) = 3*j+6 := Nat.left_distrib 3 j 2
    have h₂ : 2 ∣ 3*j+6 := Eq.subst h₁ h
    have h₃ : 2 ∣ 3*j :=(Nat.dvd_add_iff_left (by decide : 2 ∣ 6)).mpr h₂
    have ih : 2 ∣ j := euclids_lemma_2_3 j h₃
    exact (Nat.dvd_add_iff_left (by decide : 2 ∣ 2)).mp ih

theorem euclids_lemma_3_2 (k : Nat) : 3 ∣ 2*k → 3 ∣ k := match k with
  |0 => by decide
  | 1 => by decide
  | 2 => by decide
  | j+3 => by
    intro (h : 3 ∣ 2*(j+3))
    have h₁ : 2*(j+3) = 2*j+6 := Nat.left_distrib 2 j 3
    have h₂ : 3 ∣ 2*j+6 := Eq.subst h₁ h
    have h₃ : 3 ∣ 2*j := (Nat.dvd_add_iff_left (by decide : 3 ∣ 6)).mpr h₂
    have ih : 3 ∣ j := euclids_lemma_3_2 j h₃
    exact (Nat.dvd_add_iff_left (by decide : 3 ∣ 3)).mp ih

theorem power_of_3_not_even (k : Nat) : ¬ 2 ∣ 3^k := match k with
  | 0 => by decide
  | j+1 => by
    intro (h : 2 ∣ 3^(j+1))
    have h₁ : 2 ∣ 3*3^j := Eq.subst (Nat.mul_comm (3^j) 3) h
    have h₂ : 2 ∣ 3^j := euclids_lemma_2_3 (3^j) h₁
    exact (power_of_3_not_even j) h₂

theorem power_of_2_not_multiple_of_3 (k : Nat) : ¬ 3 ∣ 2^k := match k with
  | 0 => by decide
  | j+1 => by
    intro (h : 3 ∣ 2^(j+1))
    have h₁ : 3 ∣ 2*2^j := Eq.subst (Nat.mul_comm (2^j) 2) h
    have h₂ : 3 ∣ 2^j := euclids_lemma_3_2 (2^j) h₁
    exact (power_of_2_not_multiple_of_3 j) h₂

theorem cancel_unpair_left (a b : Nat) : unpair_left (pair a b) = a := match a with
  | 0 => by
    have h₁ : ¬ 2 ∣ 3^b := power_of_3_not_even b
    unfold unpair_left
    split
    . rfl
    . split
      . apply False.elim
        apply h₁
        have h₄ : 2 ∣ 1*3^b := by assumption
        exact Eq.subst (Nat.one_mul (3^b)) h₄
      . rfl
  | k+1 => by
    have ih :  unpair_left (pair k b) = k := cancel_unpair_left k b
    have h₁ : pair (k+1) b = 2*(pair k b) := calc pair (k+1) b
      _ = 2^k*2*3^b := rfl
      _ = 2*2^k*3^b := by rw [Nat.mul_comm (2^k) 2]
      _ = 2*(2^k*3^b) := Nat.mul_assoc 2 (2^k) (3^b)
    rw [h₁]
    unfold unpair_left
    split
    . have : pair (k+1) b ≠ 0 := pair_not_zero (k+1) b
      have : 2*pair k b ≠ 0 := Eq.subst (motive := fun x => x ≠ 0) h₁ this
      contradiction
    . split
      . have h₂ : (2*pair k b)/2 = pair k b := by simp
        have h₃ : (unpair_left (pair k b)) + 1 = k + 1 := congrArg (·+1) ih
        exact Eq.subst  (motive := fun x => (unpair_left x)+1 = k+1) h₂.symm h₃
      . have : 2 ∣ 2*pair k b := ⟨pair k b, rfl⟩
        contradiction

theorem cancel_unpair_right (a b : Nat) : unpair_right (pair a b) = b := match b with
  | 0 => by
    have h₁ : ¬ 3 ∣ 2^a := power_of_2_not_multiple_of_3 a
    unfold unpair_right
    split
    . rfl
    . split
      . apply False.elim
        apply h₁
        have h₄ : 3 ∣ 2^a*1 := by assumption
        exact Eq.subst (Nat.mul_one (2^a)) h₄
      . rfl
  | k+1 => by
    have ih :  unpair_right (pair a k) = k := cancel_unpair_right a k
    have h₁ : pair a (k+1) = 3*(pair a k) := calc pair a (k+1)
      _ = 2^a*(3^k*3) := rfl
      _ = 2^a*3^k*3 := by rw [Nat.mul_assoc (2^a) (3^k) 3]
      _ = 3*(2^a*3^k) := Nat.mul_comm (2^a*3^k) 3
    rw [h₁]
    unfold unpair_right
    split
    . have : pair a (k+1) ≠ 0 := pair_not_zero a (k+1)
      have : 3*pair a k ≠ 0 := Eq.subst (motive := fun x => x ≠ 0) h₁ this
      contradiction
    . split
      . have h₂ : (3*pair a k)/3 = pair a k := by simp
        have h₃ : (unpair_right (pair a k)) + 1 = k + 1 := congrArg (·+1) ih
        exact Eq.subst  (motive := fun x => (unpair_right x)+1 = k+1) h₂.symm h₃
      . have : 3 ∣ 3*pair a k := ⟨pair a k, rfl⟩
        contradiction

theorem nat_pairs_countable : Countable (All (Nat × Nat)) := by
  let f : All (Nat × Nat) → Nat := fun ⟨⟨a,b⟩,_⟩ => pair a b
  let f_cancel_left : ∀ a b : Nat, unpair_left (f ⟨⟨a,b⟩,trivial⟩) = a := fun a b => cancel_unpair_left a b
  let f_cancel_right : ∀ a b : Nat, unpair_right (f ⟨⟨a,b⟩,trivial⟩) = b := fun a b => cancel_unpair_right a b
  apply Exists.intro f
  intro ⟨⟨x₁,y₁⟩,_⟩ ⟨⟨x₂,y₂⟩,_⟩ h
  have h₁' : unpair_left (f ⟨⟨x₁,y₁⟩,trivial⟩) = unpair_left (f ⟨⟨x₂,y₂⟩,trivial⟩) := congrArg unpair_left h
  have h₁ : x₁ = x₂ := Eq.trans (Eq.trans (f_cancel_left x₁ y₁).symm h₁') (f_cancel_left x₂ y₂)
  have h₂' : unpair_right (f ⟨⟨x₁,y₁⟩,trivial⟩) = unpair_right (f ⟨⟨x₂,y₂⟩,trivial⟩) := congrArg unpair_right h
  have h₂ : y₁ = y₂ := Eq.trans (Eq.trans (f_cancel_right x₁ y₁).symm h₂') (f_cancel_right x₂ y₂)
  rw [h₁, h₂]

structure CountableSet where
  type : Type u
  val : Set type
  property : Countable val

namespace CountableSet
def All (type : Type u) (property : Countable (All type)) : CountableSet := mk type (Set.All type) property
end CountableSet

theorem countable_pairs_countable (S : CountableSet) (T : CountableSet) : Countable (All (S.val × T.val)) := by
  have ⟨nat_countable_function, h_nat_countable_function⟩ := nat_pairs_countable
  have ⟨s_countable_function, h_s_countable_function⟩ := S.property
  have ⟨t_countable_function, h_t_countable_function⟩ := T.property
  let f : All (S.val × T.val) → Nat := fun ⟨⟨a,b⟩,_⟩ => nat_countable_function ⟨⟨s_countable_function a, t_countable_function b⟩, trivial⟩
  apply Exists.intro f
  intro ⟨⟨a₁, b₁⟩, _⟩ ⟨⟨a₂, b₂⟩, _⟩ h₁
  have h₂' : (⟨⟨s_countable_function a₁, t_countable_function b₁⟩, trivial⟩ : All (Nat × Nat)) = ⟨⟨s_countable_function a₂, t_countable_function b₂⟩,_⟩ := h_nat_countable_function ⟨⟨s_countable_function a₁, t_countable_function b₁⟩,trivial⟩ ⟨⟨s_countable_function a₂, t_countable_function b₂⟩,trivial⟩ h₁
  have h₂ : (⟨s_countable_function a₁, t_countable_function b₁⟩ : Nat × Nat) = ⟨s_countable_function a₂, t_countable_function b₂⟩ := Subtype.eq_iff.mp h₂'
  have ⟨h₂₁, h₂₂⟩ : s_countable_function a₁ = s_countable_function a₂ ∧ t_countable_function b₁ = t_countable_function b₂ := Prod.ext_iff.mp h₂
  have h₃₁ : a₁ = a₂ := h_s_countable_function a₁ a₂ h₂₁
  have h₃₂ : b₁ = b₂ := h_t_countable_function b₁ b₂ h₂₂
  exact Subtype.eq (Prod.ext h₃₁ h₃₂)

theorem nats_bounded_below (S : Set Nat) (sample_value : Nat) (h : S.predicate sample_value) : ¬ ∀ n : S, ∃ m : S, n.val > m.val := by
  intro h'
  have ⟨m, _⟩ : ∃ m : S, m < sample_value := h' ⟨sample_value, h⟩
  exact nats_bounded_below S m.val m.property h'

theorem all_nats_below_n_finite (n : Nat) : FiniteProp (Set.mk fun m => m < n) :=
  match n with
  | 0 => by
    let S := Set.mk fun m => m < 0
    show FiniteProp S
    have h₁ : ∀ m : Nat, m ∉ S := fun m h => Nat.not_lt_zero m (h : S.predicate m)
    have h₂ : ∀ m : Nat, m ∈ S ↔ False := fun m => ⟨h₁ m, False.elim⟩
    have h₃ : S = ∅ := setext S ∅ h₂
    rw [h₃]
    exact FiniteProp.Empty
  | k+1 => by
    let S := Set.mk fun m => m < k+1
    let T := Set.mk fun m => m < k
    show FiniteProp S
    have ih : FiniteProp T := all_nats_below_n_finite k
    have h₁ : ∀ m : Nat, m < k+1 ↔ m < k ∨ m = k := fun m => Iff.trans Nat.lt_succ Nat.le_iff_lt_or_eq
    have h₂ : S = T ∪ {k} := setext S (T ∪ {k}) h₁
    rw [h₂, union_symm]
    exact FiniteProp.Insert k ih

theorem nats_bounded_above_finite (S : Set Nat) (n : Nat) (h : ∀ m : S, m < n) : FiniteProp S := by
  have h₁ : S ⊆ (Set.mk fun m => m < n) := h
  apply FiniteProp.Subset
  apply h₁
  exact all_nats_below_n_finite n

theorem infinite_nats_unbounded_above (S : Set Nat) (h : ¬ FiniteProp S) : ∀ n : Nat, ∃ m : S, m > n := by
  intro n
  apply byContradiction
  intro h₁'
  have h₁ : ∀ m : S, ¬ m > n := fun m h => h₁' ⟨m, h⟩
  have h₂ : ∀ m : S, m ≤ n := fun m => Nat.not_lt.mp (h₁ m)
  have h₃ : ∀ m : S, m < n+1 := fun m => Nat.lt_add_one_iff_lt_or_eq.mpr (Nat.le_iff_lt_or_eq.mp (h₂ m))
  apply h
  exact nats_bounded_above_finite S (n+1) h₃

theorem infinite_bounded_below_still_infinite (S : Set Nat) (h : ¬ FiniteProp S) (minimum : Nat) : ¬ FiniteProp (Set.mk (fun n => n ∈ S ∧ n  ≥ minimum)) :=
  let T := Set.mk (fun n => n ∈ S ∧ n ≥ minimum)
  let of_at_least_rank : Nat → T := fun rank =>
    let val : S := (infinite_nats_unbounded_above S h (minimum + rank)).choose
    have property : val.val ∈ S ∧ val.val ≥ minimum := ⟨val.property, Nat.le_trans (Nat.le_add_right minimum rank) (Nat.le_of_lt (infinite_nats_unbounded_above S h (minimum + rank)).choose_spec)⟩
    ⟨val.val, property⟩
  all_of_unbounded_infinite
  id
  of_at_least_rank
  (fun rank => Nat.le_trans (Nat.le_add_left rank minimum) (Nat.le_of_lt (infinite_nats_unbounded_above S h (minimum + rank)).choose_spec))

theorem has_minimum (S : Set Nat) (h : ∃ _n : S, True) : ∃ n : S, ∀ m : S, n.val ≤ m.val := by
  apply byContradiction
  intro h'
  have h₁ : ∀ n : S, ¬ ∀ m : S, n.val ≤ m.val := fun n h => h' ⟨n, h⟩
  have h₂ : ∀ n : S, ∃ m : S, n.val > m.val := by
    intro n
    apply byContradiction
    intro h₂'
    apply h₁ n
    intro m
    rw [←Nat.not_lt]
    intro h₂''
    exact h₂' ⟨m, h₂''⟩
  exact nats_bounded_below S h.choose.val h.choose.property h₂

noncomputable def nth_of_infinite {S : Set Nat} (h : ¬ FiniteProp S) (n : Nat) : S := match n with
  | 0 => (has_minimum S (infinite_sets_contain_element S h)).choose
  | k+1 =>
    let minimum := (nth_of_infinite h k).val + 1
    let T := Set.mk fun r => r ∈ S ∧ r ≥ minimum
    let val : T := (has_minimum T (infinite_sets_contain_element T (infinite_bounded_below_still_infinite S h minimum))).choose
    ⟨val.val, val.property.left⟩

theorem nth_lt_n_plus_oneth {S : Set Nat} (h : ¬ FiniteProp S) (n : Nat) : (nth_of_infinite h n).val < (nth_of_infinite h (n+1)).val := by
  let minimum := (nth_of_infinite h n).val + 1
  let T : Set Nat := { predicate := fun r => r ∈ S ∧ r ≥ minimum }
  let rhs_val := (has_minimum T (infinite_sets_contain_element T (infinite_bounded_below_still_infinite S h minimum))).choose
  let val_for_rhs := rhs_val.val
  have h_val_for_rhs : val_for_rhs ∈ S ∧ val_for_rhs ≥ minimum := rhs_val.property
  show nth_of_infinite h n < val_for_rhs
  have h₁ : val_for_rhs > (nth_of_infinite h n) := Nat.lt_of_add_one_le h_val_for_rhs.right
  exact h₁

theorem nth_lt_add {S : Set Nat} (h_f : ¬ FiniteProp S) (n m : Nat) (h : m > 0) : (nth_of_infinite h_f n).val < (nth_of_infinite h_f (n+m)).val := match m with
  | 0 => by contradiction
  | 1 => nth_lt_n_plus_oneth h_f n
  | k+2 => calc (nth_of_infinite h_f n).val
    _ < (nth_of_infinite h_f (n+(k+1))).val := nth_lt_add h_f n (k+1) (Nat.zero_lt_of_ne_zero (Nat.succ_ne_zero k))
    _ < (nth_of_infinite h_f (n+(k+1)+1)).val := nth_lt_n_plus_oneth h_f (n+(k+1))

theorem nth_increasing {S : Set Nat} (h_f : ¬ FiniteProp S) (m n : Nat) (h : m < n) : (nth_of_infinite h_f m).val < (nth_of_infinite h_f n).val := by
  let ⟨k, h_k⟩ := Nat.exists_eq_add_of_lt h
  rw [h_k]
  exact nth_lt_add h_f m (k+1) (Nat.zero_lt_of_ne_zero (Nat.succ_ne_zero k))

theorem nth_of_infinite_injective {S : Set Nat} (h_f : ¬ FiniteProp S) (n₁ n₂ : Nat) : nth_of_infinite h_f n₁ = nth_of_infinite h_f n₂ → n₁ = n₂ := by
  intro h₁
  apply byContradiction
  intro h₂
  cases Nat.lt_or_gt.mp h₂ with
  | inl h =>
    have h₃ : (nth_of_infinite h_f n₁).val < (nth_of_infinite h_f n₂) := nth_increasing h_f n₁ n₂ h
    exact Nat.ne_of_lt h₃ (Subtype.eq_iff.mp h₁)
  | inr h =>
    have h₃ : (nth_of_infinite h_f n₂).val < (nth_of_infinite h_f n₁) := nth_increasing h_f n₂ n₁ h
    exact Nat.ne_of_lt h₃ (Subtype.eq_iff.mp h₁.symm)

theorem no_nats_between_nths {S : Set Nat} (h_f : ¬ FiniteProp S) (n : Nat) : ∀ m : S, m.val ≤ nth_of_infinite h_f n ∨ m.val ≥ nth_of_infinite h_f (n+1) := by
  intro m
  cases em (m.val ≤ nth_of_infinite h_f n) with
  | inl h => exact Or.inl h
  | inr h =>
    have h : m.val > nth_of_infinite h_f n := Nat.gt_of_not_le h
    apply Or.inr
    let minimum := (nth_of_infinite h_f n).val + 1
    let T : Set Nat := { predicate := fun r => r ∈ S ∧ r ≥ minimum }
    let rhs_val := (has_minimum T (infinite_sets_contain_element T (infinite_bounded_below_still_infinite S h_f minimum))).choose
    show m ≥ rhs_val.val
    have h₁ : ∀ k : T, k ≥ rhs_val.val := (has_minimum T (infinite_sets_contain_element T (infinite_bounded_below_still_infinite S h_f minimum))).choose_spec
    have h₂ : m.val ≥ minimum := Nat.succ_le.mpr h
    exact h₁ ⟨m.val, ⟨m.property, h₂⟩⟩

theorem zeroth_le_all {S : Set Nat} (h_f : ¬ FiniteProp S) : ∀ n : S, n.val ≥ nth_of_infinite h_f 0 := by
  intro n
  have h₁ : ∀ m : S, (nth_of_infinite h_f 0).val ≤ m.val := (has_minimum S (infinite_sets_contain_element S h_f)).choose_spec
  exact h₁ n

theorem n_le_nth {S : Set Nat} (h_f : ¬ FiniteProp S) : ∀ n : Nat, n ≤ nth_of_infinite h_f n := by
  intro n
  match n with
  | 0 => exact Nat.zero_le (nth_of_infinite h_f 0)
  | k+1 =>
    have ih : k ≤ nth_of_infinite h_f k := n_le_nth h_f k
    have h₁ : k < nth_of_infinite h_f (k+1) := Nat.lt_of_le_of_lt ih (nth_lt_n_plus_oneth h_f k)
    exact Nat.succ_le_of_lt h₁

theorem nth_image_infinite {S : Set Nat} (h_f : ¬ FiniteProp S) : ¬ FiniteProp (Set.mk fun (y : Nat) => y ∈ S ∧ ∃ n : Nat, nth_of_infinite h_f n = y) :=
  all_of_unbounded_infinite
  (fun x => x)
  (fun n => ⟨nth_of_infinite h_f n, ⟨(nth_of_infinite h_f n).property, ⟨n, rfl⟩⟩⟩ : Nat → (Set.mk fun y => y ∈ S ∧ ∃ n : Nat, nth_of_infinite h_f n = y))
  (n_le_nth h_f)

theorem nth_of_infinite_surjective {S : Set Nat} (h_f : ¬ FiniteProp S) : ∀ y : S, ∃ n : Nat, nth_of_infinite h_f n = y := by
  intro y
  let image_of_nth : Set Nat := Set.mk fun y => y ∈ S ∧ ∃ n : Nat, nth_of_infinite h_f n = y
  let T : Set Nat := Set.mk fun n => n ∈ image_of_nth ∧ n ≥ y
  have h₁ : ∃ _ : T, True := infinite_sets_contain_element T (infinite_bounded_below_still_infinite image_of_nth (nth_image_infinite h_f) y)
  let ⟨next_lowest_nth, h₂⟩ : ∃ x : T, ∀ y : T, x.val ≤ y.val := has_minimum T h₁
  let n : Nat := next_lowest_nth.property.left.right.choose
  have h₃ : nth_of_infinite h_f n = next_lowest_nth.val := next_lowest_nth.property.left.right.choose_spec
  have h₄ : y.val ≤ next_lowest_nth.val := next_lowest_nth.property.right
  cases Nat.le_iff_lt_or_eq.mp h₄ with
  | inr h => exact ⟨n, Subtype.eq (Eq.trans h₃ h.symm)⟩
  | inl h =>
    apply False.elim
    match n with
    | 0 => exact Nat.not_lt_of_le (zeroth_le_all h_f y) (Eq.subst h₃.symm h)
    | k+1 =>
      have h₅ : nth_of_infinite h_f k < y.val := by
        apply byContradiction
        intro h₅'
        have h₆ : nth_of_infinite h_f k ≥ y.val := Nat.le_of_not_gt h₅'
        have h₇ : (nth_of_infinite h_f k).val ∈ T := ⟨⟨(nth_of_infinite h_f k).property, ⟨k, rfl⟩⟩, h₆⟩
        have h₈ : (nth_of_infinite h_f k).val ≥ nth_of_infinite h_f (k+1) := (by rw [h₃]; exact h₂ ⟨nth_of_infinite h_f k, h₇⟩)
        exact Nat.not_lt_of_ge h₈ (nth_lt_n_plus_oneth h_f k)
      have h₉ : y.val ≤ nth_of_infinite h_f k ∨ nth_of_infinite h_f (k+1) ≤ y.val := no_nats_between_nths h_f k y
      have h₁₀ : nth_of_infinite h_f (k+1) ≤ y.val := Or.resolve_left h₉ (Nat.not_le_of_gt h₅)
      apply Nat.not_lt_of_ge h₁₀
      rw [h₃]
      exact h

theorem infinite_nats_equal_cardonality_all_nats {S : Set Nat} (h_f : ¬ FiniteProp S) : equalCardinality (All Nat) S := ⟨fun x => nth_of_infinite h_f x.val, fun x₁ x₂ h => Subtype.eq (nth_of_infinite_injective h_f x₁.val x₂.val h), fun y => ⟨⟨(nth_of_infinite_surjective h_f y).choose, trivial⟩, (nth_of_infinite_surjective h_f y).choose_spec⟩⟩

theorem countable_equal_cardinality_image (S : CountableSet) : equalCardinality S.val (Set.mk fun n => ∃ x : S.val, n = S.property.choose x) := by
  let T := Set.mk fun n => ∃ x : S.val, n = S.property.choose x
  show equalCardinality S.val T
  let f : S.val → T := fun x => ⟨S.property.choose x, ⟨x, rfl⟩⟩
  apply Exists.intro f
  constructor
  . intro x₁ x₂ h₁
    have h₁' : (f x₁).val = (f x₂).val := congrArg Subtype.val h₁
    exact S.property.choose_spec x₁ x₂ h₁'
  . intro y
    apply Exists.intro y.property.choose
    apply Subtype.eq
    exact y.property.choose_spec.symm

theorem image_of_infinite_countable_infinite {S : CountableSet} (h_f : ¬ FiniteProp S.val) : ¬ FiniteProp (Set.mk fun n => ∃ x : S.val, n = S.property.choose x) := by
  apply infinite_equal_cardonality_infinite
  . exact countable_equal_cardinality_image S
  . exact h_f

theorem infinite_countable_equal_cardinality_all_nats {S : CountableSet} (h_f : ¬ FiniteProp S.val) : equalCardinality S.val (All Nat) := by
  let T : Set Nat := Set.mk fun n => ∃ x : S.val, n = S.property.choose x
  apply equal_cardinality_trans
  . show equalCardinality S.val T
    exact countable_equal_cardinality_image S
  . have h₁ : ¬ FiniteProp T := image_of_infinite_countable_infinite h_f
    apply equal_cardinality_symm
    exact infinite_nats_equal_cardonality_all_nats h₁
end Countable
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

theorem propositions_infinite : ¬Set.FiniteProp (Set.All Proposition) := by
  let rank : Proposition → Nat
  | Atomic n => n
  | Not _ => 0
  | Implies _ _ => 0
  exact Set.all_of_inductive_infinite rank Atomic (fun _ => rfl)

namespace countable
inductive PropositionType where
  | Atomic
  | Negation
  | Implication

theorem proposition_type_countable : Set.Countable (Set.All PropositionType) := by
  let f : Set.All PropositionType → Nat := fun t => match t.val with
    | PropositionType.Atomic => 0
    | PropositionType.Negation => 1
    | PropositionType.Implication => 2
  apply Exists.intro f
  intro t₁ t₂ h
  suffices t₁.val = t₂.val from Subtype.eq this
  have h₁₁ : t₁ = ⟨t₁.val, trivial⟩ := Subtype.eq rfl
  have h₁₂ : t₂ = ⟨t₂.val, trivial⟩ := Subtype.eq rfl
  let t₁_val := t₁.val
  let t₂_val := t₂.val
  have h₁ : f ⟨t₁_val, trivial⟩ = f ⟨t₂_val, trivial⟩ := by rw [←h₁₁, ←h₁₂, h]
  show t₁_val = t₂_val
  match t₁_val, t₂_val with
  | PropositionType.Atomic, PropositionType.Atomic => rfl
  | PropositionType.Negation, PropositionType.Negation => rfl
  | PropositionType.Implication, PropositionType.Implication => rfl

theorem type_body_pair_countable : Set.Countable (Set.All (Set.All PropositionType × Set.All Nat)) := Set.Countable.countable_pairs_countable (Set.Countable.CountableSet.All PropositionType proposition_type_countable) (Set.Countable.CountableSet.All Nat (Set.Countable.any_natural_numbers_countable (Set.All Nat)))

noncomputable def nat_pair_encoder : Set.All (Nat × Nat) → Nat := Set.Countable.nat_pairs_countable.choose
theorem nat_pair_encoder_injective (p₁ p₂ : Set.All (Nat × Nat)) : nat_pair_encoder p₁ = nat_pair_encoder p₂ → p₁ = p₂ := Set.Countable.nat_pairs_countable.choose_spec p₁ p₂

noncomputable def convert_to_nat (p : Proposition) : Nat := match p with
  | Atomic n => type_body_pair_countable.choose ⟨⟨⟨PropositionType.Atomic, trivial⟩, ⟨n, trivial⟩⟩, trivial⟩
  | Not p => type_body_pair_countable.choose ⟨⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat p, trivial⟩⟩, trivial⟩
  | Implies p q =>
    let p_encoded : Nat := convert_to_nat p
    let q_encoded : Nat := convert_to_nat q
    let encoded_pair := nat_pair_encoder ⟨⟨p_encoded, q_encoded⟩, trivial⟩
    type_body_pair_countable.choose ⟨⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair, trivial⟩⟩, trivial⟩

theorem converted_atomic_not_negation (n : Nat) (q : Proposition) : convert_to_nat (Atomic n) ≠ convert_to_nat (Not q) := by
  intro h₀
  have h₁ : (⟨⟨⟨PropositionType.Atomic, trivial⟩, ⟨n, trivial⟩⟩, trivial⟩ : Set.All ((Set.All PropositionType) × (Set.All Nat))) = ⟨⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q, trivial⟩⟩, trivial⟩ := type_body_pair_countable.choose_spec ⟨⟨⟨PropositionType.Atomic, trivial⟩, ⟨n, trivial⟩⟩, trivial⟩ ⟨⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q, trivial⟩⟩, trivial⟩ h₀
  have h₂ : (⟨⟨PropositionType.Atomic, trivial⟩, ⟨n, trivial⟩⟩ : (Set.All PropositionType) × (Set.All Nat)) = ⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q, trivial⟩⟩ := Subtype.eq_iff.mp h₁
  have h₃ : (⟨PropositionType.Atomic, trivial⟩ : Set.All PropositionType) = ⟨PropositionType.Negation, trivial⟩ := (Prod.ext_iff.mp h₂).left
  have h₄ : PropositionType.Atomic = PropositionType.Negation := Subtype.eq_iff.mp h₃
  contradiction

theorem converted_atomic_not_implication (n : Nat) (q r : Proposition) : convert_to_nat (Atomic n) ≠ convert_to_nat (Implies q r) := by
  intro h₀
  let q_encoded : Nat := convert_to_nat q
  let r_encoded : Nat := convert_to_nat r
  let encoded_pair := nat_pair_encoder ⟨⟨q_encoded, r_encoded⟩, trivial⟩
  have h₁ : (⟨⟨⟨PropositionType.Atomic, trivial⟩, ⟨n, trivial⟩⟩, trivial⟩ : Set.All ((Set.All PropositionType) × (Set.All Nat))) = ⟨⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair, trivial⟩⟩, trivial⟩ := type_body_pair_countable.choose_spec ⟨⟨⟨PropositionType.Atomic, trivial⟩, ⟨n, trivial⟩⟩, trivial⟩ ⟨⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair, trivial⟩⟩, trivial⟩ h₀
  have h₂ : (⟨⟨PropositionType.Atomic, trivial⟩, ⟨n, trivial⟩⟩ : (Set.All PropositionType) × (Set.All Nat)) = ⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair, trivial⟩⟩ := Subtype.eq_iff.mp h₁
  have h₃ : (⟨PropositionType.Atomic, trivial⟩ : Set.All PropositionType) = ⟨PropositionType.Implication, trivial⟩ := (Prod.ext_iff.mp h₂).left
  have h₄ : PropositionType.Atomic = PropositionType.Implication := Subtype.eq_iff.mp h₃
  contradiction

theorem converted_negation_not_implication (q₁ : Proposition) (q₂ r : Proposition) : convert_to_nat (Not q₁) ≠ convert_to_nat (Implies q₂ r) := by
  intro h₀
  let q₂_encoded : Nat := convert_to_nat q₂
  let r_encoded : Nat := convert_to_nat r
  let encoded_pair := nat_pair_encoder ⟨⟨q₂_encoded, r_encoded⟩, trivial⟩
  have h₁ : (⟨⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q₁, trivial⟩⟩, trivial⟩ : Set.All ((Set.All PropositionType) × (Set.All Nat))) = ⟨⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair, trivial⟩⟩, trivial⟩ := type_body_pair_countable.choose_spec ⟨⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q₁, trivial⟩⟩, trivial⟩ ⟨⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair, trivial⟩⟩, trivial⟩ h₀
  have h₂ : (⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q₁, trivial⟩⟩ : (Set.All PropositionType) × (Set.All Nat)) = ⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair, trivial⟩⟩ := Subtype.eq_iff.mp h₁
  have h₃ : (⟨PropositionType.Negation, trivial⟩ : Set.All PropositionType) = ⟨PropositionType.Implication, trivial⟩ := (Prod.ext_iff.mp h₂).left
  have h₄ : PropositionType.Negation = PropositionType.Implication := Subtype.eq_iff.mp h₃
  contradiction

theorem convert_to_nat_injective (p₁ p₂ : Proposition) : convert_to_nat p₁ = convert_to_nat p₂ → p₁ = p₂ := by
  intro h₀
  match p₁, p₂ with
  | Atomic n₁, Atomic n₂ =>
    have h₁ : (⟨⟨⟨PropositionType.Atomic, trivial⟩, ⟨n₁, trivial⟩⟩, trivial⟩ : Set.All ((Set.All PropositionType) × (Set.All Nat))) = ⟨⟨⟨PropositionType.Atomic, trivial⟩, ⟨n₂, trivial⟩⟩, trivial⟩ := type_body_pair_countable.choose_spec ⟨⟨⟨PropositionType.Atomic, trivial⟩, ⟨n₁, trivial⟩⟩, trivial⟩ ⟨⟨⟨PropositionType.Atomic, trivial⟩, ⟨n₂, trivial⟩⟩, trivial⟩ h₀
    have h₂ : (⟨⟨PropositionType.Atomic, trivial⟩, ⟨n₁, trivial⟩⟩ : (Set.All PropositionType) × (Set.All Nat)) = ⟨⟨PropositionType.Atomic, trivial⟩, ⟨n₂, trivial⟩⟩ := Subtype.eq_iff.mp h₁
    have h₃ : (⟨n₁, trivial⟩ : Set.All Nat) = ⟨n₂, trivial⟩ := (Prod.ext_iff.mp h₂).right
    have h₄ : n₁ = n₂ := Subtype.eq_iff.mp h₃
    congr
  | Not q₁, Not q₂ =>
    have h₁ : (⟨⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q₁, trivial⟩⟩, trivial⟩ : Set.All ((Set.All PropositionType) × (Set.All Nat))) = ⟨⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q₂, trivial⟩⟩, trivial⟩ := type_body_pair_countable.choose_spec ⟨⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q₁, trivial⟩⟩, trivial⟩ ⟨⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q₂, trivial⟩⟩, trivial⟩ h₀
    have h₂ : (⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q₁, trivial⟩⟩ : (Set.All PropositionType) × (Set.All Nat)) = ⟨⟨PropositionType.Negation, trivial⟩, ⟨convert_to_nat q₂, trivial⟩⟩ := Subtype.eq_iff.mp h₁
    have h₃ : (⟨convert_to_nat q₁, trivial⟩ : Set.All Nat) = ⟨convert_to_nat q₂, trivial⟩ := (Prod.ext_iff.mp h₂).right
    have h₄ : convert_to_nat q₁ = convert_to_nat q₂ := Subtype.eq_iff.mp h₃
    have h₅ : q₁ = q₂ := convert_to_nat_injective q₁ q₂ h₄
    congr
  | Implies q₁ r₁, Implies q₂ r₂ =>
    let q₁_encoded := convert_to_nat q₁
    let q₂_encoded := convert_to_nat q₂
    let r₁_encoded := convert_to_nat r₁
    let r₂_encoded := convert_to_nat r₂
    let encoded_pair₁ := nat_pair_encoder ⟨⟨q₁_encoded, r₁_encoded⟩, trivial⟩
    let encoded_pair₂ := nat_pair_encoder ⟨⟨q₂_encoded, r₂_encoded⟩, trivial⟩
    have h₁ : (⟨⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair₁, trivial⟩⟩, trivial⟩ : Set.All ((Set.All PropositionType) × (Set.All Nat))) = ⟨⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair₂, trivial⟩⟩, trivial⟩ := type_body_pair_countable.choose_spec ⟨⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair₁, trivial⟩⟩, trivial⟩ ⟨⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair₂, trivial⟩⟩, trivial⟩ h₀
    have h₂ : (⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair₁, trivial⟩⟩ : (Set.All PropositionType) × (Set.All Nat)) = ⟨⟨PropositionType.Implication, trivial⟩, ⟨encoded_pair₂, trivial⟩⟩ := Subtype.eq_iff.mp h₁
    have h₃ : (⟨encoded_pair₁, trivial⟩ : Set.All Nat) = ⟨encoded_pair₂, trivial⟩ := (Prod.ext_iff.mp h₂).right
    have h₄ : encoded_pair₁ = encoded_pair₂ := Subtype.eq_iff.mp h₃
    have h₅ : (⟨⟨convert_to_nat q₁, convert_to_nat r₁⟩, trivial⟩ : Set.All (Nat × Nat)) = ⟨⟨convert_to_nat q₂, convert_to_nat r₂⟩, trivial⟩ := nat_pair_encoder_injective ⟨⟨convert_to_nat q₁, convert_to_nat r₁⟩, trivial⟩ ⟨⟨convert_to_nat q₂, convert_to_nat r₂⟩, trivial⟩ h₄
    have h₆ : (⟨convert_to_nat q₁, convert_to_nat r₁⟩ : Nat × Nat) = ⟨convert_to_nat q₂, convert_to_nat r₂⟩ := Subtype.eq_iff.mp h₅
    have h₇ : q₁ = q₂ := convert_to_nat_injective q₁ q₂ (Prod.ext_iff.mp h₆).left
    have h₈ : r₁ = r₂ := convert_to_nat_injective r₁ r₂ (Prod.ext_iff.mp h₆).right
    congr
  | Atomic n, Not q => exact False.elim (converted_atomic_not_negation n q h₀)
  | Not q, Atomic n=> exact False.elim (converted_atomic_not_negation n q h₀.symm)
  | Atomic n, Implies q r => exact False.elim (converted_atomic_not_implication n q r h₀)
  | Implies q r, Atomic n => exact False.elim (converted_atomic_not_implication n q r h₀.symm)
  | Not q₁, Implies q₂ r => exact False.elim (converted_negation_not_implication q₁ q₂ r h₀)
  | Implies q₂ r, Not q₁ => exact False.elim (converted_negation_not_implication q₁ q₂ r h₀.symm)
end countable

theorem propositions_countable : Set.Countable (Set.All Proposition) := by
  apply Exists.intro fun ⟨p, _⟩ => countable.convert_to_nat p
  exact fun ⟨p₁, _⟩ ⟨p₂, _⟩ h => Subtype.eq (countable.convert_to_nat_injective p₁ p₂ h)
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
