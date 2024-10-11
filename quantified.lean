variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := Iff.intro
  (fun h_left : ∀ x, p x ∧ q x =>
    have hpx : ∀x, p x := fun x => (h_left x).left
    have hqx : ∀x, q x := fun x => (h_left x).right
    ⟨hpx, hqx⟩
  )
  (fun h_right : (∀x, p x) ∧ (∀x, q x) =>
    have px : ∀x, p x := h_right.left
    have qx : ∀x, q x := h_right.right
    fun x =>
      ⟨px x, qx x⟩
  )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := fun h : ∀x, p x → q x =>
  fun hpx : ∀x, p x =>
    fun x =>
      show q x from (h x) (hpx x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := fun h : (∀x, p x) ∨ (∀x, q x) =>
  fun x =>
    Or.elim h
      (fun hpx : ∀x, p x => Or.inl (hpx x))
      (fun hqx : ∀x, q x => Or.inr (hqx x))

variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := fun x => Iff.intro
  (fun har : ∀ _ : α, r => har x)
  (fun hr : r => fun _ : α => hr)

open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := Iff.intro
  (fun h_left : ∀ x, p x ∨ r => Or.elim (em r)
    Or.inr
    (fun hnr : ¬r => Or.inl fun x =>
      show p x from Or.elim (h_left x) id (fun hr : r => absurd hr hnr)
    )
  )
  (fun h_right: (∀ x, p x) ∨ r => Or.elim h_right
    (fun hpx : ∀ x, p x => fun x => Or.inl (hpx x))
    (fun hr : r => fun _ => Or.inr hr)
  )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := Iff.intro
  (fun h_left : ∀ x, r → p x => fun hr : r =>
    fun x => h_left x hr
  )
  (fun h_right : r → ∀ x, p x => fun x =>
    fun hr : r => h_right hr x
  )

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h_barber : shaves barber barber ↔ ¬shaves barber barber := h barber
  have hn_barber_self : ¬shaves barber barber :=
    fun h_barber_self : shaves barber barber => absurd h_barber_self (h_barber.mp h_barber_self)
  have hnn_barber_self : ¬¬shaves barber barber :=
    fun hn_barber_self : ¬shaves barber barber => absurd (h_barber.mpr hn_barber_self) hn_barber_self
  show False from absurd hn_barber_self hnn_barber_self

def divides (a b : Nat) : Prop := ∃ c : Nat, a*c = b

def even (n : Nat) : Prop := ∃m : Nat, 2*m = n

def prime (n : Nat) : Prop := n ≠ 1 ∧ ∀ m : Nat, divides m n ↔ m = 1 ∨ m = n

def infinitely_many_primes : Prop := ∀ a : Nat, ∃ b : Nat, a > b ∧ prime b

def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃k : Nat, n = 2^2^k+1

def infinitely_many_Fermat_primes : Prop := ∀ a : Nat, ∃ b : Nat, a > b ∧ Fermat_prime b

def goldbach_conjecture : Prop := ∀ n : Nat, even n ∧ n > 2 → ∃ a b : Nat, prime a ∧ prime b ∧ a+b=n

def Goldbach's_weak_conjecture : Prop := ∀ n : Nat, ¬even n ∧ n > 5 → ∃ a b c : Nat, prime a ∧ prime b ∧ prime c ∧ n = a+b+c

def Fermat's_last_theorem : Prop := ∀ n : Nat, n > 2 → ¬∃ a b c : Nat, a^n+b^n = c^n

example : (∃ _ : α, r) → r := fun h : ∃ _ : α, r =>
  let ⟨_, hr⟩ := h
  hr

example (a : α) : r → (∃ _ : α, r) := fun hr : r =>
  ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := Iff.intro
  (fun h_left : ∃ x, p x ∧ r =>
    let ⟨x, hpx, hr⟩ := h_left
    ⟨⟨x, hpx⟩, hr⟩
  )
  (fun h_right : (∃ x, p x) ∧ r =>
    let ⟨⟨x, hpx⟩, hr⟩ := h_right
    ⟨x, hpx, hr⟩
  )

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := Iff.intro
  (fun h_left : ∃ x, p x ∨ q x =>
    let ⟨x, hpq⟩ := h_left
    show (∃ x, p x) ∨ (∃ x, q x) from Or.elim hpq (Or.inl ∘ (Exists.intro x)) (Or.inr ∘ (Exists.intro x))
  )
  (fun h_right : (∃ x, p x) ∨ (∃ x, q x) =>
    Or.elim h_right
      (fun hpx : ∃ x, p x =>
        let ⟨x, hpx⟩ := hpx
        show ∃x, p x ∨ q x from ⟨x, Or.inl hpx⟩
      )
      (fun hqx : ∃ x, q x =>
        let ⟨x, hqx⟩ := hqx
        show ∃x, p x ∨ q x from ⟨x, Or.inr hqx⟩
      )
  )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro
  (fun h_left : ∀ x, p x =>
    show ¬∃ x, ¬p x from fun hnpx : ∃ x, ¬p x =>
      let ⟨x, hnpx⟩ := hnpx
      show False from absurd (h_left x) hnpx
  )
  (fun h_right : ¬∃ x, ¬p x =>
    fun x => show p x from byContradiction
      fun hnpx : ¬p x =>
        show False from absurd (Exists.intro x hnpx) h_right
  )

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := Iff.intro
  (fun h_left : ∃ x, p x =>
    let ⟨x, hpx⟩ := h_left
    show ¬∀ x, ¬p x from fun hnpx : ∀ x, ¬p x =>
      show False from absurd hpx (hnpx x)
  )
  (fun h_right : ¬∀ x, ¬p x =>
    show ∃ x, p x from byContradiction
      fun hnpx : ¬∃ x, p x =>
        suffices ∀ x, ¬p x from absurd this h_right
        fun x => fun hpx : p x =>
          show False from absurd ⟨x, hpx⟩ hnpx
  )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := Iff.intro
  (fun h_left : ¬∃ x, p x => fun x =>
      show ¬p x from
        fun hpx : p x => absurd ⟨x, hpx⟩ h_left
  )
  (fun h_right : ∀ x, ¬p x =>
    show ¬∃ x, p x from fun hpx : ∃ x, p x =>
      let ⟨x, hpx⟩ := hpx
      absurd hpx (h_right x)
  )

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := Iff.intro
  (fun h_left : ¬ ∀ x, p x =>
    show ∃ x, ¬ p x from byContradiction
      fun hnnp : ¬ ∃ x, ¬ p x =>
        suffices ∀ x, p x from absurd this h_left
          show ∀ x, p x from fun x =>  show p x from byContradiction
            fun hnpx : ¬ p x =>
              show False from absurd ⟨x, hnpx⟩ hnnp
  )
  (fun h_right : ∃ x, ¬ p x =>
    let ⟨x, hnpx⟩ := h_right
    show ¬ ∀ x, p x from fun hpx : ∀ x, p x =>
      absurd (hpx x) hnpx
  )

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := Iff.intro
  (fun h_left : ∀ x, p x → r =>
    show (∃ x, p x) → r from fun hpx : ∃ x, p x =>
      let ⟨x, hpx⟩ := hpx
      show r from h_left x hpx
  )
  (fun h_right : (∃ x, p x) → r =>
    show ∀ x, p x → r from fun x =>
      show p x → r from fun hpx : p x =>
        show r from h_right (Exists.intro x hpx)
  )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := Iff.intro
  (fun h_left : ∃ x, p x → r =>
    let ⟨x, hpxr⟩ := h_left
    show (∀ x, p x) → r from fun hpx : ∀ x, p x =>
      show r from hpxr (hpx x)
  )
  (fun h_right : (∀ x, p x) → r =>
    show ∃ x, p x → r from byContradiction
      fun hnpxr : ¬ ∃ x, p x → r =>
        have hnr : ¬ r := fun hr : r =>
          suffices p a → r from absurd ⟨a, this⟩ hnpxr
            show p a → r from fun _ : p a => hr
        have hpx : ∀ x, p x := fun x =>
          show p x from byContradiction
            fun hnpx : ¬ p x =>
              suffices p x → r from absurd ⟨x, this⟩ hnpxr
                show p x → r from fun hpx : p x => absurd hpx hnpx
        show False from absurd (h_right hpx) hnr
  )

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := Iff.intro
  (fun h_left : ∃ x, r → p x =>
    let ⟨x, hrpx⟩ := h_left
    show r → ∃ x, p x from fun hr : r =>
      ⟨x, hrpx hr⟩
  )
  (fun h_right : r → ∃ x, p x =>
    show ∃ x, r → p x from byCases
      (fun hr : r =>
        let ⟨x, hpx⟩ := h_right hr
        have hrpx := fun _ : r => hpx
        ⟨x, hrpx⟩
      )
      (fun hnr : ¬ r =>
        have hrpa := fun hr : r => absurd hr hnr
        ⟨a, hrpa⟩
      )
  )
