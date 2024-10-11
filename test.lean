variable {p : Prop}
variable {q : Prop}
variable {r : Prop}

theorem t1 : p -> q -> p := fun (hp : p) (_ : q) => hp

theorem t2 (hpq : p -> q) (hqr : q -> r) : (p -> r) := fun (hp : p) => hqr (hpq hp)

theorem t3 (h : p ∧ q) : (q ∧ p) := ⟨h.right, h.left⟩

theorem t4 (hp : p) (hnp : ¬p) : q := absurd hp hnp

theorem t5 : (p ∧ q) ↔ (q ∧ p) := ⟨t3, t3⟩

theorem t6 (h: p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from ⟨hq, hp⟩

namespace with_em
  open Classical

  theorem dne (h : ¬¬p) : p :=
    suffices hnpp : ¬p → p from Or.elim (em p) id hnpp
    fun hnp : ¬p => absurd hnp h
end with_em

theorem demorgan1 (h_and : p ∧ q) : ¬(¬p ∨ ¬q) :=
  have hp : p := h_and.left
  have hq : q := h_and.right
  fun h_or : ¬p ∨ ¬q =>
    show False from Or.elim h_or (absurd hp) (absurd hq)

theorem demorgan2 (h_or : p ∨ q) : ¬(¬p ∧ ¬q) :=
  fun h_and : ¬p ∧ ¬q =>
    have hnp : ¬p := h_and.left
    have hnq : ¬q := h_and.right
    show False from Or.elim h_or (fun hp => absurd hp hnp) (fun hq => absurd hq hnq)

theorem demorgan1r (h_nor : ¬(p ∨ q)) : ¬p ∧ ¬q :=
  have hnp : ¬p := fun hp : p => h_nor (Or.inl hp)
  have hnq : ¬q := fun hq : q => h_nor (Or.inr hq)
  ⟨hnp, hnq⟩

namespace with_dne
  axiom dne : ¬¬p → p

  theorem em : p ∨ ¬p :=
  dne fun h_neither : ¬(p ∨ ¬p) =>
    have both : ¬p ∧ ¬¬p := demorgan1r h_neither
    show False from absurd both.left both.right
end with_dne

example : p ∧ q ↔ q ∧ p := Iff.intro
  (fun hpq : p ∧ q => show q ∧ p from ⟨hpq.right, hpq.left⟩)
  (fun hqp : q ∧ p => show p ∧ q from ⟨hqp.right, hqp.left⟩)

example : p ∨ q ↔ q ∨ p := Iff.intro
  (fun hpq : p ∨ q => Or.elim hpq Or.inr Or.inl)
  (fun hqp : q ∨ p => Or.elim hqp Or.inr Or.inl)

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := Iff.intro
  (fun h_left : (p ∧ q) ∧ r => show p ∧ (q ∧ r) from ⟨h_left.left.left, ⟨h_left.left.right, h_left.right⟩⟩)
  (fun h_right : p ∧ (q ∧ r) => show (p ∧ q) ∧ r from ⟨⟨h_right.left, h_right.right.left⟩, h_right.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := Iff.intro
  (fun h_left : (p ∨ q) ∨ r => show p ∨ (q ∨ r) from Or.elim h_left
    (fun hpq => Or.elim hpq Or.inl (Or.inr ∘ Or.inl))
    (Or.inr ∘ Or.inr)
  )
  (fun h_right : p ∨ (q ∨ r) => show (p ∨ q) ∨ r from Or.elim h_right
    (Or.inl ∘ Or.inl)
    (fun hqr => Or.elim hqr (Or.inl ∘ Or.inr) Or.inr)
  )

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := Iff.intro
  (fun h_left: p ∧ (q ∨ r) =>
    have hp : p := h_left.left
    show (p ∧ q) ∨ (p ∧ r) from Or.elim h_left.right (Or.inl ∘ And.intro hp) (Or.inr ∘ And.intro hp)
  )
  (fun h_right: (p ∧ q) ∨ (p ∧ r) =>
    have hp : p := Or.elim h_right And.left And.left
    have hqr : q ∨ r := Or.elim h_right (Or.inl ∘ And.right) (Or.inr ∘ And.right)
    show p ∧ (q ∨ r) from ⟨hp, hqr⟩
  )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := Iff.intro
  (fun h_left: p ∨ (q ∧ r) =>
    have hpq : p ∨ q := Or.elim h_left Or.inl (Or.inr ∘ And.left)
    have hpr : p ∨ r := Or.elim h_left Or.inl (Or.inr ∘ And.right)
    show (p ∨ q) ∧ (p ∨ r) from ⟨hpq, hpr⟩
  )
  (fun h_right : (p ∨ q) ∧ (p ∨ r) =>
    have hpq : p ∨ q := h_right.left
    have hpr : p ∨ r := h_right.right
    show p ∨ (q ∧ r) from Or.elim hpq
      Or.inl
      (fun hq : q => Or.elim hpr
        Or.inl
        (Or.inr ∘ (And.intro hq))
      )
  )

example : (p → (q → r)) ↔ (p ∧ q → r) := Iff.intro
  (fun h_left: p → (q → r) =>
    (fun hpq : p ∧ q => show r from h_left hpq.left hpq.right
  ))
  (fun h_right : p ∧ q → r =>
    (fun p : p => fun q : q => h_right ⟨p, q⟩)
  )

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := Iff.intro
  (fun h_left: (p ∨ q) → r =>
    have hpr : p → r := h_left ∘ Or.inl
    have hqr : q → r := h_left ∘ Or.inr
    ⟨hpr, hqr⟩
  )
  (fun h_right : (p → r) ∧ (q → r) =>
    have hpr := h_right.left
    have hqr : q → r := h_right.right
    (fun hpq : p ∨ q => Or.elim hpq hpr hqr)
  )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := Iff.intro
  (fun h_left: ¬(p ∨ q) =>
    have hnp : ¬p := h_left ∘ Or.inl
    have hnq : ¬q := h_left ∘ Or.inr
    ⟨hnp, hnq⟩
  )
  (fun h_right: ¬p ∧ ¬q =>
    have hnp : ¬p := h_right.left
    have hnq : ¬q := h_right.right
    (fun h_or: p ∨ q => Or.elim h_or hnp hnq)
  )

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h : ¬p ∨ ¬q =>
    fun h_both : p ∧ q =>
      have hp : p := h_both.left
        have hq : q := h_both.right
        Or.elim h (fun hnp => hnp hp) (fun hnq => hnq hq)

example : ¬(p ∧ ¬p) := fun h_both : p ∧ ¬p => h_both.right h_both.left

example : p ∧ ¬q → ¬(p → q) := fun h : p ∧ ¬q =>
  fun h_implies : p → q => h.right (h_implies h.left)

example : ¬p → (p → q) := fun hnp : ¬p =>
  fun hp : p => absurd hp hnp

example : (¬p ∨ q) → (p → q) := fun h : ¬p ∨ q =>
  Or.elim h
    (fun hnp : ¬p => fun hp : p => absurd hp hnp)
    (fun hq : q => fun _ : p => hq)

example : p ∨ False ↔ p := Iff.intro
  (fun h_left : p ∨ False => Or.elim h_left id False.elim)
  Or.inl

example : p ∧ False ↔ False := Iff.intro
  (fun h_left: p ∧ False => False.elim h_left.right)
  False.elim

example : (p → q) → (¬q → ¬p) := fun h : p → q =>
  fun hnq : ¬q => fun hp : p => hnq (h hp)

namespace classical
  open Classical

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := fun h : p → q ∨ r => Or.elim (em q)
    (fun hq : q => Or.inl (fun _ : p => hq))
    (fun hnq : ¬q => Or.inr fun hp : p =>
      have hqr : q ∨ r := h hp
      show r from Or.elim hqr (fun hq : q => absurd hq hnq) id
    )

  example : ¬(p ∧ q) → ¬p ∨ ¬q := fun h : ¬(p ∧ q) => Or.elim (em p)
    (fun hp : p => Or.inr fun hq : q => h ⟨hp, hq⟩)
    Or.inl

  example : ¬(p → q) → p ∧ ¬q := fun h : ¬(p → q) =>
    have hp : p := byContradiction
      fun hnp : ¬p =>
        suffices p → q from absurd this h
        fun hp : p => absurd hp hnp
    have hnq : ¬q := byContradiction
      fun hnnq : ¬¬q => have hq := not_not.mp hnnq
        suffices p → q from absurd this h
        fun _ : p => hq
    ⟨hp, hnq⟩

  example : (p → q) → (¬p ∨ q) := fun h : p → q =>
    Or.elim (em p)
      (fun hp : p => Or.inr (h hp))
      Or.inl

  example : (¬q → ¬p) → (p → q) := fun h : ¬q → ¬p =>
    fun hp : p => byContradiction
      fun hnq : ¬q => absurd hp (h hnq)

  example : p ∨ ¬p := em p

  example : (((p → q) → p) → p) := fun h : (p → q) → p => byContradiction
    (fun hnp : ¬p =>
      have h_implies : p → q := fun hp : p => absurd hp hnp
      absurd (h h_implies) hnp
    )
end classical

example : ¬(p ↔ ¬p) := fun h : p ↔ ¬p =>
  have hnp := fun hp : p => absurd hp (h.mp hp)
  have hnnp : ¬¬p := fun hnp : ¬p => absurd (h.mpr hnp) hnp
  absurd hnp hnnp
