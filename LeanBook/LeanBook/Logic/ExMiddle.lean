/-- 二重否定の除去 -/
example (P : Prop) : ¬¬ P → P := by
  -- ¬¬ P だと仮定する
  intro hn2p
  -- 排中律より、P ∨ ¬ P が成り立つ
  by_cases h : P
  · -- P が成り立つ場合は即座に証明が終了する
    exact h
  · -- P が成り立たない場合、¬¬ P という仮定と矛盾する
    contradiction


--以下は練習問題
/-- 二重否定の除去 -/
example (P : Prop) : ¬¬ P → P := by
  intro hn2p
  by_cases h : P
  · exact h
  · exact False.elim (hn2p h)

/-- ドモルガンの法則 -/
example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  · intro h
    by_cases hp : P
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · exact Or.inl hp
  · intro h hpq
    cases h with
    | inl hnp => exact hnp hpq.left
    | inr hnq => exact hnq hpq.right

/-- 対偶が元の命題と同値であること -/
example (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor
  · intro hpq hnq hp
    exact hnq (hpq hp)
  · intro h hp
    by_cases hq : Q
    · exact hq
    · exact False.elim ((h hq) hp)
