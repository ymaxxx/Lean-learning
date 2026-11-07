#check Prop

#check (1 + 1 = 3 : Prop)

#check (fun n => n + 3 = 39 : Nat→ Prop)

#check True
#check False

example : True := by
  trivial

example (P : Prop) (h : P) : P := by
  exact h
--or use assumption

example (h :False) : ∀ x y z n : Nat,
    n ≥ 3 → x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
  trivial

example (P Q R : Prop) : (P→ Q→ R) = (P→ (Q→ R)) := by
  rfl

example (P : Prop) : (¬ P) = (P→ False) := by
 rfl

example (P : Prop) (hnp :¬ P) (hp : P) : False := by
  apply hnp
  exact hp

example (P Q : Prop) (h : P→¬ Q) : Q→¬ P := by
  intro hq
  intro hp
  exact h hp hq

example (P : Prop) (hnp :¬ P) (hp : P) : False := by
  contradiction

example (P Q : Prop) (hnp :¬ P) (hp : P) : Q := by
  exfalso
  contradiction

example (P Q : Prop) (h1 : P→ Q) (h2 : Q→ P) : P↔ Q := by
 constructor
 ·apply h1
 ·apply h2

example (P Q : Prop) (hq : Q) : (Q→ P)↔ P := by

constructor
case mp =>
 intro h
 exact h hq

case mpr =>
  intro hp hq
  exact hp

example (P Q : Prop) (hq : Q) : (Q→ P)↔ P := by
  constructor <;> intro h
  case mp =>
    exact h hq
  case mpr =>
    intro hq
    exact h

example (P Q : Prop) (h : P↔ Q) (hq : Q) : P := by
  rw [h]
  exact hq

example (P Q : Prop) (h : P↔ Q) (hp : P) : Q := by
 rw [← h]
 exact hp

example (P Q : Prop) (h : P↔ Q) : P = Q := by
 rw [h]

example (P Q : Prop) (h : P∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P∧ Q) : Q := by
  exact h.right

example (P Q : Prop) (h : P∨ Q) : Q∨ P := by
  cases h with
 | inl hp =>
   right
   exact hp
 | inr hq =>
   left
   exact hq

--練習問題3.1.8
example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h hp
  cases h with
  | inl hnp => contradiction
  | inr hq => exact hq
example (P Q : Prop) :¬ (P∨ Q)↔¬ P∧¬ Q := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro h hp
    cases hp with
    | inl hp => exact h.left hp
    | inr hq => exact h.right hq
