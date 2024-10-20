inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving Repr

open MyNat

def add (m n : MyNat) : MyNat :=
  match n with
  | zero => m
  | succ k => succ (add m k)

instance : Add MyNat := ⟨add⟩

theorem add_zero (m : MyNat) : m+zero = m := rfl
theorem add_succ (m n : MyNat) : m+succ n = succ (m+n) := rfl

theorem zero_add : ∀ m : MyNat, add zero m = m := @MyNat.rec
  (fun k => add zero k = k)
  (show add zero zero = zero from rfl)
  (fun (k : MyNat) (ih : add zero k = k) =>
    have h1 : add zero k.succ = (add zero k).succ := add_succ zero k
    have h2 : (add zero k).succ = k.succ := congrArg succ ih
    show add zero k.succ = k.succ from Eq.subst h2 h1
  )

theorem succ_add (m : MyNat) : ∀ n : MyNat, (m+n).succ = m.succ+n := @MyNat.rec
  (fun k => (m+k).succ = m.succ+k)
  (show (m+zero).succ = m.succ+zero from rfl)
  (fun (k : MyNat) (ih : (m+k).succ = m.succ+k) =>
    have : m+k.succ = m.succ+k := by rw [add_succ, ih]
    have : (m+k.succ).succ = (m.succ+k).succ := congrArg succ this
    this
  )

theorem succ_switch (m n : MyNat) : m+n.succ = m.succ+n := calc m+n.succ
  _ = (m+n).succ := add_succ m n
  _ = m.succ+n := succ_add m n

theorem add_comm (m : MyNat) : ∀ n : MyNat, m+n = n+m := @MyNat.rec
  (fun k => m+k = k+m)
  (show m+zero = zero+m from Eq.trans (add_zero m) (zero_add m).symm)
  (fun (k : MyNat) (ih : m+k = k+m) =>
    have h₁ : (m+k).succ = m+k.succ := calc (m+k).succ
      _ = m+k.succ := add_succ m k
    have h₂ : (m+k).succ = k.succ+m := calc (m+k).succ
      _ = (k+m).succ := by rw [ih]
      _ = k.succ+m := succ_add k m
    show m+k.succ = k.succ+m from Eq.trans h₁ h₂
  )

theorem add_assoc (a b : MyNat) : ∀ c : MyNat, a+b+c = a+(b+c) := @MyNat.rec
  (fun k => a+b+k = a+(b+k))
  (show a+b+zero = a+(b+zero) from rfl)
  (fun (k : MyNat) (ih : a+b+k = a+(b+k)) =>
    have h₁ : (a+b+k).succ = a+b+k.succ := add_succ (a+b) k
    have h₂ : (a+b+k).succ = a+(b+k.succ) := calc (a+b+k).succ
      _ = (a+(b+k)).succ := by rw [ih]
      _ = a+(b+k).succ := by rw [add_succ]
      _ = a+(b+k.succ) := by rw [add_succ b k]
    Eq.trans h₁ h₂
  )

def mul (m n : MyNat) : MyNat :=
  match n with
  | zero => zero
  | succ k => m + (mul m k)

instance : Mul MyNat := ⟨mul⟩

theorem mul_zero (m : MyNat) : m*zero = zero := rfl
theorem mul_succ (m n : MyNat) : m*succ n = m+m*n := rfl

theorem zero_mul : ∀ m, zero*m = zero := @MyNat.rec
  (fun k => zero*k = zero)
  (show zero*zero = zero from rfl)
  (fun (k : MyNat) (ih : zero*k = zero) =>
    calc zero*k.succ
      _ = zero+zero*k := mul_succ zero k
      _ = zero+zero := by rw [ih]
  )

theorem succ_mul (m : MyNat) : ∀ n : MyNat, m.succ*n = m*n+n := @MyNat.rec
  (fun k => m.succ*k = m*k+k)
  (show m.succ*zero = m*zero+zero from rfl)
  (fun (k : MyNat) (ih : m.succ*k = m*k+k) =>
    calc m.succ*k.succ
      _ = m.succ+m.succ*k := mul_succ m.succ k
      _ = m.succ+(m*k+k) := by rw [ih]
      _ = m.succ+k+m*k := by rw [add_comm (m*k) k, add_assoc]
      _ = m+k.succ+m*k := by rw [succ_switch m k]
      _ = k.succ+(m+m*k) := by rw [add_comm m k.succ, add_assoc]
      _ = m*k.succ+k.succ := by rw [mul_succ, add_comm]
  )

theorem mul_comm (m : MyNat) : ∀ n : MyNat, m*n = n*m := @MyNat.rec
  (fun k => m*k = k*m)
  (show m*zero = zero*m from Eq.trans (mul_zero m) (zero_mul m).symm)
  (fun (k : MyNat) (ih : m*k = k*m) =>
    calc m*k.succ
      _ = m+m*k := mul_succ m k
      _ = k*m+m := by rw [ih, add_comm]
      _ = k.succ*m := (succ_mul k m).symm
  )

theorem mul_right_distrib (a b : MyNat) : ∀ m : MyNat, (a+b)*m = a*m+b*m := @MyNat.rec
  (fun k => (a+b)*k = a*k+b*k)
  (show (a+b)*zero = a*zero+b*zero from rfl)
  (fun (k : MyNat) (ih : (a+b)*k = a*k+b*k) =>
    calc (a+b)*k.succ
      _ = a+b+(a+b)*k := mul_succ (a+b) k
      _ = a+b+(a*k+b*k) := by rw [ih]
      _ = a+b+a*k+b*k := by rw [add_assoc (a+b) (a*k) (b*k)]
      _ = a+(a*k+b)+b*k := by rw [add_assoc a b (a*k), add_comm b (a*k)]
      _ = (a+a*k)+(b+b*k) := by rw [(add_assoc a (a*k) b).symm, add_assoc (a+a*k)]
  )

theorem mul_left_distrib (a b m : MyNat) : m*(a+b) = m*a+m*b :=
  by rw [mul_comm, mul_right_distrib, mul_comm m a, mul_comm m b]

theorem mul_assoc (a b : MyNat) : ∀ c : MyNat, a*b*c = a*(b*c) := @MyNat.rec
  (fun k => a*b*k = a*(b*k))
  (show a*b*zero = a*(b*zero) from rfl)
  (fun (k : MyNat) (ih : a*b*k = a*(b*k)) =>
    show a*b*k.succ = a*(b*k.succ) from Eq.symm (calc a*(b*k.succ)
      _ = a*(b+b*k) := by rw [mul_succ]
      _ = a*b+a*(b*k) := mul_left_distrib b (b*k) a
      _ = a*b+a*b*k := by rw [ih]
      _ = a*b*k.succ := mul_succ (a*b) k
    )
  )

namespace MyNat
  def fromNat (n : Nat) : MyNat := match n with
    | 0 => zero
    | Nat.succ k => succ (fromNat k)
end MyNat

instance : OfNat MyNat (n : Nat) where
  ofNat := fromNat n

theorem mul_one (n : MyNat) : n*1 = n := mul_succ n 0
theorem one_mul (n : MyNat) : 1*n = n := calc 1*n
  _ = n*1 := mul_comm 1 n

theorem add_one (m : MyNat) : m+1 = m.succ := rfl
theorem one_add (m : MyNat) : 1+m = m.succ := calc 1+m
  _ = m+1 := add_comm 1 m

theorem add_inj {a b c : MyNat} : a+c = b+c → a = b := by
  intro h
  induction c with
  | zero => exact h
  | succ k ih =>
    have : (a+k).succ = (b+k).succ := calc (a+k).succ
      _ = a+k.succ := add_succ a k
      _ = b+k.succ := h
    injection this with h'
    exact ih h'

theorem add_to_zero {m n : MyNat} : m+n = 0 → m = 0 ∧ n = 0 := by
  intro h
  induction n with
  | zero => exact And.intro h rfl
  | succ k _ => injection h

namespace MyNat
def pred (n : MyNat) := match n with
  | 0 => 0
  | succ k => k
end MyNat

theorem pred_succ (n : MyNat) : pred (succ n) = n := rfl
theorem succ_pred (n : MyNat) (non_zero : n ≠ 0) : succ (pred n) = n :=
  match n with
    | 0 => absurd rfl non_zero
    | succ _ => rfl

def add_pred (m n : MyNat) (hnz : n ≠ 0) : m+n.pred = (m+n).pred := match n with
  | 0 => absurd rfl hnz
  | succ _ => rfl

def lt (m n : MyNat) : Prop := ∃ k : MyNat, k ≠ 0 ∧ m+k = n

instance : LT MyNat := ⟨lt⟩

theorem lt_def (m n : MyNat) : m < n ↔ ∃ k : MyNat, k ≠ 0 ∧ m+k = n := by
  apply Iff.intro
  repeat (intro h; exact h)

def le (m n : MyNat) : Prop := m < n ∨ m = n

instance : LE MyNat := ⟨le⟩

theorem le_def (m n : MyNat) : m ≤ n ↔ m < n ∨ m = n := by
  apply Iff.intro
  repeat (intro h; exact h)

theorem lt_succ_self (m : MyNat) : m<m.succ := by
  apply Exists.intro 1
  constructor
  . intro h; injection h
  . rfl

theorem lt_self {m : MyNat} : ¬ m < m := by
  intro ⟨k, ⟨hnz, h⟩⟩
  apply hnz ∘ add_inj
  calc k+m
    _ = m+k := add_comm k m
    _ = m := h
    _ = 0+m := (zero_add m).symm

theorem le_self (m : MyNat) : m ≤ m := Or.inr rfl

theorem lt_zero {m : MyNat} : ¬ m < 0 := by
  intro ⟨k, ⟨hnz, h⟩⟩
  cases k with
  | zero => contradiction
  | succ a => injection h

theorem le_zero (m : MyNat) : m ≤ 0 ↔ m = 0 := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hlt => exact absurd hlt lt_zero
    | inr h => exact h
  . intro h; exact Or.inr h

theorem lt_trans (a b c : MyNat) : a<b → b<c → a<c := by
  intro ⟨k₁, ⟨_hnz₁, h₁⟩⟩ ⟨k₂, ⟨hnz₂, h₂⟩⟩
  apply Exists.intro (k₁+k₂)
  constructor
  . intro h; cases k₂ with
      | zero => exact hnz₂ rfl
      | succ a => injection h
  . calc a+(k₁+k₂)
      _ = a+k₁+k₂ := by rw [add_assoc]
      _ = b+k₂ := by rw [h₁]
      _ = c := by rw [h₂]

theorem le_trans (a b c : MyNat) : a ≤ b → b ≤ c → a ≤ c := by
  intro h₁ h₂
  cases h₁ with
  | inl lt₁ => cases h₂ with
    | inl lt₂ => exact Or.inl (lt_trans a b c lt₁ lt₂)
    |inr eq₂ => exact Or.inl (Eq.subst eq₂ lt₁)
  | inr eq₁ => cases h₂ with
    | inl lt₂ => exact Or.inl (Eq.subst (motive := fun k => k < c) eq₁.symm lt₂)
    | inr eq₂ => exact Or.inr (Eq.trans eq₁ eq₂)

theorem lt_le_trans (a b c : MyNat) : a < b → b ≤ c → a < c := by
  intro lt₁ h₂
  cases h₂ with
  | inl lt₂ => exact lt_trans a b c lt₁ lt₂
  | inr eq₂ => exact Eq.subst eq₂ lt₁

instance : Trans ((·<·) : MyNat → MyNat → Prop) (·<·) (·<·) where
  trans {a b c : MyNat} := lt_trans a b c

instance : Trans ((·≤·) : MyNat → MyNat → Prop) (·≤·) (·≤·) where
  trans {a b c : MyNat} := le_trans a b c

instance : Trans ((·<·) : MyNat → MyNat → Prop) (·≤·) (·<·) where
  trans {a b c : MyNat} := lt_le_trans a b c

theorem lt_succ (m n : MyNat) : m < n → m < n.succ := by
  intro ⟨k, ⟨_, h⟩⟩
  apply Exists.intro k.succ
  constructor
  . intro hz; injection hz
  . calc m+k.succ
      _ = (m+k).succ := by rw [add_succ]
      _ = n.succ := by rw [h]

theorem le_succ (m n : MyNat) : m ≤ n → m ≤ n.succ := by
  intro h
  cases h with
  | inl hlt => exact Or.inl (lt_succ m n hlt)
  | inr heq => exact Or.inl (Eq.subst (motive := fun k => m < k.succ) heq (lt_succ_self m))

theorem pred_lt (m n : MyNat) (h₁ : m < n) : m.pred < n := match m with
| zero => h₁
| succ k => by
  let ⟨a, ⟨_, h₂⟩⟩ := h₁
  apply Exists.intro a.succ
  constructor
  . intro h; injection h
  . calc k+a.succ
      _ = k.succ+a := by rw [succ_switch]
      _ = n := h₂

theorem pred_le (m n : MyNat) (h₁ : m ≤ n) : m.pred ≤ n := match h₁ with
  | Or.inl hlt => Or.inl (pred_lt m n hlt)
  | Or.inr heq => match m with
    | zero => Or.inr (Eq.subst rfl heq)
    | succ k => Or.inl (Eq.subst heq (lt_succ_self k))

theorem lt_add (m n : MyNat) : m < n → ∀ k : MyNat, m < n+k := by
  intro h
  intro k
  induction k with
  | zero => exact h
  | succ l ih => exact lt_succ _ _ ih

theorem le_add (m n : MyNat) : m ≤ n → ∀ k : MyNat, m ≤ n+k := by
  intro h
  intro k
  induction k with
  | zero => exact h
  | succ l ih => exact le_succ _ _ ih

theorem lt_add_self (m n : MyNat) (hnz : n ≠ 0) : m < m+n := by
  apply Exists.intro n
  constructor
  . exact hnz
  . rfl

theorem le_add_self (m n : MyNat) : m ≤ m+n := le_add m m (le_self m) n

theorem lt_mul (m n : MyNat) : m < n → ∀ k : MyNat, k ≠ 0 → m < n*k := by
  intro h
  intro k
  intro hnz
  induction k with
  | zero => contradiction
  | succ l ih => cases l with
    | zero => rw [←mul_one n]; exact h
    | succ a =>
      have hnz : a.succ ≠ 0 := fun h => by injection h
      have ih : m < n*a.succ := ih hnz
      calc m
        _ < n*a.succ := ih
        _ ≤ n*a.succ+n := le_add_self (n*a.succ) n
        _ = n*a.succ.succ := by rw [add_comm, ←mul_succ]

theorem le_mul (m n : MyNat) (h : m ≤ n) (k : MyNat) (hk : k ≠ 0) : m ≤ n*k := match h with
  | Or.inl hlt => Or.inl (lt_mul m n hlt k hk)
  | Or.inr _ => by
    induction k with
    | zero => exact absurd rfl hk
    | succ l ih => cases l with
      | zero => rw [←mul_one n]; exact h
      | succ a =>
        have hnz : a.succ ≠ 0 := fun h => by injection h
        have ih : m ≤ n*a.succ := ih hnz
        calc m
          _ ≤ n*a.succ := ih
          _ ≤ n*a.succ+n := le_add_self (n*a.succ) n
          _ = n*a.succ.succ := by rw [add_comm, ←mul_succ]

theorem lt_gt {m n : MyNat} : m < n → ¬ n < m := by
  intro ⟨k₁, ⟨hnz₁, h₁⟩⟩ ⟨k₂, ⟨_, h₂⟩⟩
  have : k₁+k₂+m = 0+m := calc k₁+k₂+m
    _ = k₂+n := by rw [add_comm k₁ k₂, add_assoc, add_comm k₁ m, h₁]
    _ = m := by rw [add_comm, h₂]
    _ = 0+m := (zero_add m).symm
  have : k₁+k₂ = 0 := add_inj this
  exact hnz₁ (add_to_zero this).left

theorem lt_eq (m n : MyNat) (h₁ : m < n) : m ≠ n := by
  intro h₂
  let ⟨k, ⟨hnz, h₃⟩⟩ := h₁
  apply hnz
  apply add_inj
  calc k+m
  _ = m+k := add_comm k m
  _ = n := h₃
  _ = m := h₂.symm
  _ = 0+m := (zero_add m).symm

theorem zero_lt {m : MyNat} : m ≠ 0 → 0 < m := by
  intro h
  induction m with
  | zero => contradiction
  | succ k ih => match k with
    | zero => exact Exists.intro 1 ⟨fun h => by injection h, rfl⟩
    | succ a => exact lt_succ 0 a.succ (ih (fun h => by injection h))

theorem lt_eq_gt {m n : MyNat} : m < n ∨ m = n ∨ m > n := by
  induction n with
  | zero => match m with
    | zero => exact Or.inr (Or.inl rfl)
    | succ k => exact Or.inr (Or.inr (zero_lt (fun h => by injection h)))
  | succ k ih => cases ih with
    | inl hlt => exact Or.inl (lt_succ m k hlt)
    |inr hge => cases hge with
      | inl heq =>
        apply fun leq => Or.elim leq (fun hlt => Or.inl hlt) (fun heq => Or.inr (Or.inl heq))
        exact le_succ m k  (Or.inr heq)
      | inr hgt =>
        let ⟨a, ⟨hnz, h₁⟩⟩ := hgt
        let b := a.pred -- why?
        have h₂ : m = k.succ+b := calc m
          _ = k+a := h₁.symm
          _ = (k+a).succ.pred := rfl
          _ = k.succ+a.pred := by rw [succ_add, add_pred k.succ a hnz]
        match b with
        | zero => exact Or.inr (Or.inl h₂)
        | succ c => exact Or.inr (Or.inr ⟨c.succ, ⟨fun h => by injection h, h₂.symm⟩⟩)

theorem lt_as_le (m n : MyNat) : m < n ↔ ¬ (n ≤ m) := by
  apply Iff.intro
  . intro h₁
    intro h₂
    cases h₂ with
    | inl hlt => exact lt_gt h₁ hlt
    | inr heq => exact lt_self (Eq.subst heq h₁)
  . intro h₃
    have hneq : m ≠ n := fun h => h₃ (Or.inr h.symm)
    have hngt : ¬ n < m := fun h => h₃ (Or.inl h)
    cases lt_eq_gt with
    | inl h => exact h
    | inr h => cases h with
      | inl heq => contradiction
      | inr hgt => contradiction

theorem lt_succ_both (m n : MyNat) (h₁ : m < n) : m.succ < n.succ := by
  let ⟨k, ⟨hnz, h₂⟩⟩ := h₁
  apply Exists.intro k
  apply And.intro hnz
  calc m.succ+k
  _ = (m+k).succ := (succ_add m k).symm
  _ = n.succ := by rw [h₂]

theorem le_succ_both (m n : MyNat) (h₁ : m ≤ n) : m.succ ≤ n.succ := match h₁ with
  | Or.inl hlt => Or.inl (lt_succ_both m n hlt)
  | Or.inr heq => Or.inr (congrArg succ heq)

theorem lt_pred (m n : MyNat) (h₁ : m < n) : m ≤ n.pred := by
  let ⟨k, ⟨hnz, h₂⟩⟩ := h₁
  let k₁ := k.pred -- why?
  have : k₁.succ = k := succ_pred k hnz
  have h₃ : m+k₁.succ = n := by rw [this, h₂]
  match k₁ with
  | zero =>
    have heq : m = n.pred := calc m+0
      _ = (m+0).succ.pred := rfl
      _ = (m+zero.succ).pred := rfl
      _ = n.pred := by rw [h₃]
    exact Or.inr heq
  | succ a =>
    apply Or.inl
    apply Exists.intro a.succ
    constructor
    . intro h; injection h
    . calc m+a.succ
      _ = (m+a.succ).succ.pred := rfl
      _ = n.pred := by rw [←add_succ, h₃]

theorem succ_lt (m n : MyNat) (h₁ : m < n) : m.succ ≤ n := lt_pred m.succ n.succ (lt_succ_both m n h₁)

def sub (m n : MyNat) : MyNat := match n with
  | 0 => m
  | succ k => pred (sub m k)

instance : Sub MyNat := ⟨sub⟩

theorem sub_zero (m : MyNat) : m - 0 = m := rfl
theorem sub_succ (m n : MyNat) : m-n.succ = pred (m-n) := rfl

theorem zero_sub (m : MyNat) : 0-m = 0 := by
  induction m with
  | zero => rfl
  | succ k ih => exact show 0-k.succ = pred 0 by rw [sub_succ, ih]

theorem sub_one (m : MyNat) : m-1 = m.pred := rfl

theorem sub_lt (a b c : MyNat) (h : a < b) : a-c < b := match c with
  | zero => h
  | succ k =>
    have ih : a-k < b := sub_lt a b k h
    pred_lt (a-k) b ih

theorem sub_le (a b c : MyNat) (h : a ≤ b) : a-c ≤ b := match c with
  | zero => h
  | succ k =>
    have ih : a-k ≤ b := sub_le a b k h
    pred_le (a-k) b ih

theorem sub_not_zero (m n : MyNat) (h₁ : m > n) : m-n ≠ 0 :=
  have h₂ : m ≠ n := (lt_eq n m h₁).symm
  match n with
  | zero => h₂
  | succ k =>
    have h₃ : m > k := pred_lt k.succ m h₁
    have ih : m-k ≠ 0 := sub_not_zero m k h₃
    sorry
