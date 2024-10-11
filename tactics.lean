variable (p q r : Prop)

example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h_left
    exact And.intro h_left.right h_left.left
  . intro h_right
    exact And.intro h_right.right h_right.left

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro h_left
    apply Or.elim h_left
    . exact Or.inr
    . exact Or.inl
  . intro h_right
    apply Or.elim h_right
    . exact Or.inr
    . exact Or.inl

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro h_left
    exact ⟨h_left.left.left, ⟨h_left.left.right, h_left.right⟩⟩
  . intro h_right
    exact ⟨⟨h_right.left, h_right.right.left⟩, h_right.right.right⟩

theorem t1 : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h_left
    apply Or.elim h_left
    . intro hpq
      apply Or.elim hpq
      . exact Or.inl
      . exact Or.inr ∘ Or.inl
    . exact Or.inr ∘ Or.inr
  . intro h_right
    apply Or.elim h_right
    . exact Or.inl ∘ Or.inl
    . intro hqr
      apply Or.elim hqr
      . exact Or.inl ∘ Or.inr
      . exact Or.inr

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro ⟨hp, hqr⟩
    cases hqr with
    | inl hq => apply Or.inl; exact And.intro hp hq
    | inr hr => apply Or.inr; exact And.intro hp hr
  . intro h_right
    cases h_right with
    | inl hpq => constructor; exact hpq.left; exact Or.inl hpq.right
    | inr hpr => constructor; exact hpr.left; exact Or.inr hpr.right

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h_left
    cases h_left with
    | inl hp => constructor; exact Or.inl hp; exact Or.inl hp
    | inr hqr => constructor; exact Or.inr hqr.left; exact Or.inr hqr.right
  . intro ⟨hpq, hpr⟩
    cases hpq with
    | inl hp => exact Or.inl hp
    | inr hq =>
      cases hpr with
      |inl hp => exact Or.inl hp
      | inr hr => apply Or.inr; constructor; exact hq; exact hr

example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h_left
    intro ⟨hp, hq⟩
    exact h_left hp hq
  . intro h_right
    intro hp hq
    apply h_right ⟨hp, hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h_left
    constructor
    . intro hp
      exact h_left (Or.inl hp)
    . intro hq
      exact h_left (Or.inr hq)
  . intro ⟨hpr, hqr⟩
    intro hpq
    cases hpq with
    | inl hp => apply hpr hp
    | inr hq => apply hqr hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h_left
    constructor
    . intro hp
      exact h_left (Or.inl hp)
    . intro hq
      exact h_left (Or.inr hq)
  . intro ⟨hnp, hnq⟩
    intro hpq
    cases hpq with
    |inl hp => contradiction
    |inr hq => contradiction

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro hnpnq
  intro ⟨hp, hq⟩
  cases hnpnq
  repeat contradiction

example : ¬(p ∧ ¬p) := by
  intro ⟨hp, hnp⟩
  contradiction

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩
  intro hpq
  have := hpq hp
  contradiction

example : ¬p → (p → q) := by
  intro hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  cases h with
  | inl hnp => contradiction
  | inr hq => exact hq

example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro h_left
    cases h_left with
    | inl hp => exact hp
    | inr false => contradiction
  . exact Or.inl

example : p ∧ False ↔ False := by
  apply Iff.intro
  . exact And.right
  . intro hf
    contradiction

example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  have := hpq hp
  contradiction

open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  cases em p with
  |inl hp =>
    cases h hp with
    | inl hq => apply Or.inl; intro; exact hq
    |inr hr => apply Or.inr; intro; exact hr
  | inr hnp =>
    apply Or.inl
    intro hp
    contradiction

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h1
  apply byContradiction
  intro h2
  apply h1
  constructor
  . apply byContradiction
    intro h3
    apply h2
    exact Or.inl h3
  . apply byContradiction
    intro h4
    apply h2
    exact Or.inr h4

example : ¬(p → q) → p ∧ ¬q := by
  intro h1
  apply byContradiction
  intro h2
  apply h1
  intro h3
  apply byContradiction
  intro h4
  apply h2 ⟨h3, h4⟩

example : (p → q) → (¬p ∨ q) := by
  intro h1
  cases em p with
  | inl h2 => apply Or.inr; exact h1 h2
  | inr h3 => exact Or.inl h3

example : (¬q → ¬p) → (p → q) := by
  intro h1
  intro h2
  apply byContradiction
  intro h3
  exact h1 h3 h2

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := by
  intro h1
  apply byContradiction
  intro h2
  apply h2
  apply h1
  exact False.elim ∘ h2

example : ¬(p ↔ ¬p) := by
  intro h1
  have : ¬p := by
    intro h2
    exact h1.mp h2 h2
  have : ¬¬p := by
    intro h3
    exact h3 (h1.mpr h3)
  contradiction

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h_left
    constructor
    . intro x
      exact (h_left x).left
    . intro x
      exact (h_left x).right
  . intro h_right
    intro x
    constructor
    . exact h_right.left x
    . exact h_right.right x

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h1 h2 x
  exact h1 x (h2 x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h1 x
  cases h1 with
  | inl h2 => exact Or.inl (h2 x)
  | inr h3 => exact Or.inr (h3 x)

example : α → ((∀ _x : α, r) ↔ r) := by
  intro x
  apply Iff.intro
  . intro h1
    exact h1 x
  . intro h2
    intro _x
    exact h2

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . intro h1
    cases em r with
    | inl hr => exact Or.inr hr
    | inr h2 =>
      apply Or.inl
      intro x
      cases h1 x with
      | inl h3 => exact h3
      | inr h4 => contradiction
  . intro h5 x
    cases h5 with
    |inl h6 => exact Or.inl (h6 x)
    | inr h7 => exact Or.inr h7

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro h1 h2 x
    exact h1 x h2
  . intro h3 x h4
    exact h3 h4 x

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have h1 : shaves barber barber ↔ ¬ shaves barber barber := h barber
  have : ¬ shaves barber barber := by
    intro h2
    apply h1.mp h2
    exact h2
  have : ¬ ¬ shaves barber barber := by
    intro h3
    apply h3
    exact h1.mpr h3
  contradiction

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | apply And.intro | assumption)
