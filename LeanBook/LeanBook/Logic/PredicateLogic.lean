/-- （Lean の標準の）自然数上の述語 -/
def P (n : Nat) : Prop := n = n

example : ∀ a : Nat, P a := by
  -- 任意の x : Nat が与えられたとする
  intro x
  -- P を展開すれば明らか
  dsimp [P]

/-- すべての自然数 x について P x が成り立つなら、P 0 も成り立つ -/
example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  -- h を 0 に適用すればよい
  exact h 0

/-- 偶数であることを表す述語 -/
def even (n : Nat) : Prop := ∃ m : Nat, n = m + m

/-- 4 : Nat は偶数 -/
example : even 4 := by
  exists 2

example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x) :
    ∃ x : α, Q x := by
  -- 仮定 h が存在を主張している y を取り出す
  obtain ⟨y, hy⟩ := h
  -- この y が求めるものである
  exists y
  -- P y ∧ Q y が成り立つ
  exact hy.right

/-- 人間たちの集合 -/
opaque Human : Type

/-- 愛の関係 -/
opaque Love : Human → Human → Prop

-- 専用の中置記法を用意する
@[inherit_doc] infix:50 " -♥→ " => Love

/-- すべての人に愛されているアイドルが存在する -/
def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -♥→ idol

/-- 誰にでも好きな人の 1 人くらいいる -/
def EveryoneLovesSomeone : Prop := ∀ h : Human, ∃ tgt : Human, h -♥→ tgt

#check ∃ philan : Human, ∀ h : Human, philan -♥→ h

def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -♥→ h

#check ∀ h : Human, ∃ lover : Human, lover -♥→ h

def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -♥→ h

example : PhilanExists → EveryoneLoved := by
  -- 博愛主義者の存在を仮定する
  intro h
  -- 存在が主張されている博愛主義者 philan を取り出す
  obtain ⟨philan, h⟩ := h
  -- EveryoneLoved を示す
  dsimp [EveryoneLoved]
  -- 任意の human : Human が与えられたとする
  intro human
  -- lover = philan とすればよい
  exists philan
  -- philan -♥→ human が成り立つ
  exact h human

-- 練習問題 3.3.4
example : IdolExists → EveryoneLovesSomeone := by
  intro hIdol
  obtain ⟨idol, hLovedByEveryone⟩ := hIdol
  intro person
  exists idol
  exact hLovedByEveryone person
