-- P ↔ Q は「P → Q かつ Q → P」を表す。

-- 同値 P ↔ Q と P から Q を導く。
example (P Q : Prop) (h : P ↔ Q) : P → Q := by
  intro hp
  exact h.mp hp

-- 同値 P ↔ Q と Q から P を導く。
example (P Q : Prop) (h : P ↔ Q) : Q → P := by
  intro hq
  exact h.mpr hq

-- 二つの含意を証明して、同値 P ↔ Q を示す。
example (P Q : Prop) (hpq : P → Q) (hqp : Q → P) : P ↔ Q := by
  constructor
  · exact hpq
  · exact hqp

-- 同値の仮定と P の証明から Q を示す。
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  exact h.mp hp

example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  intro h
  apply h
  exact Or.inr (fun hp => h (Or.inl hp))
