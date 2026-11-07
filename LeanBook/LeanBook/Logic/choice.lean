#check Classical.em

#print axioms Classical.em

#check Classical.choice

/-- 関数の全射性 -/
def Surjective {X Y : Type} (f : X → Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y

/-- Surjective を使用する例：恒等関数は全射 -/
example : Surjective (fun x : Nat => x) := by
  intro y
  exists y

variable {X Y : Type}

/-- 全射であるような関数 f : X → Y に対して、
その右逆関数 g : Y → X を返す高階関数 -/
noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
  -- y : Y が与えられたとする
  intro y
  -- f は全射なので {x // f x = y} は空ではない
  have hNonempty : Nonempty {x // f x = y} := by
    obtain ⟨x, hx⟩ := hf y
    exact ⟨⟨x, hx⟩⟩
  -- 選択原理を用いて、f x = y となる x : X を構成する
  have x := Classical.choice hNonempty
  exact x.val

-- 練習問題 3.5.4
/-- 対偶が元の命題と同値であることを認めれば、二重否定の除去が導ける -/
theorem double_negation_of_contra_equiv (P : Prop)
    (contra_equiv : ∀ (P Q : Prop), (¬ P → ¬ Q) ↔ (Q → P)) :
    ¬¬ P → P := by
  intro hNotNotP
  have hNotPImpliesNotTrue : ¬ P → ¬ True := by
    intro hNotP
    exact False.elim (hNotNotP hNotP)
  have hTrueImpliesP : True → P :=
    (contra_equiv P True).mp hNotPImpliesNotTrue
  exact hTrueImpliesP True.intro

-- Classical.choice に依存していないことを確認する
#print axioms double_negation_of_contra_equiv
