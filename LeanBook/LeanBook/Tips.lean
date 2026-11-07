/-- 3重否定の簡略化 -/
example (P : Prop) : ¬¬¬ P → ¬ P := by
  -- ¬¬¬ P と P を仮定する
  intro hn3p hp
  -- ここで ¬¬ P が成り立つ
  have hn2p : ¬¬ P := by
    -- ¬ P と仮定すると、P と矛盾する
    intro hnp
    contradiction
  -- ¬¬¬ P と ¬¬ P は矛盾する
  contradiction

example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp
  have : ¬¬ P := by
    intro hnp
    contradiction
  guard_hyp this : ¬¬ P
  contradiction

/-- 排中律の二重否定 -/
example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  -- ¬ (P ∨ ¬ P) と仮定する
  intro h
  -- ここで ¬ P を示せば十分である
  suffices hyp : ¬ P from by
    -- ¬ P ならば P ∨ ¬ P が成り立つため、
    -- 最初の仮定と矛盾する
    have : P ∨ ¬ P := by
      right
      exact hyp
    contradiction
  -- 以下、¬ P を示す
  guard_target =ₛ ¬ P
  -- P と仮定すると P ∨ ¬ P が成り立ち、矛盾する
  intro hp
  have : P ∨ ¬ P := by
    left
    exact hp
  contradiction

example (P : Prop) : (P → True) ↔ True := by
  exact?

example (P : Prop) : (True → P) ↔ P := by
  exact?

example (P Q : Prop) (h : ¬ P ↔ Q) : (P → False) ↔ Q := by
  rw [show (P → False) ↔ ¬ P from by rfl]
  rw [h]


--練習問題3.2.5
example (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h
  have hnp : ¬ P := by
    intro hp
    exact (h.mp hp) hp
  exact hnp (h.mpr hnp)
