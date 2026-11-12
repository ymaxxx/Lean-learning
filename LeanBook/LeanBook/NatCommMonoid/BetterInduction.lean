import LeanBook.NatCommMonoid.AcRfl

example (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    -- MyNat.zero が表示される形を確認する
    guard_target =ₛ m + MyNat.zero = MyNat.zero + m
    simp [MyNat.ctor_eq_zero]
  | succ n ih =>
    -- MyNat.succ が表示される形を確認する
    guard_target =ₛ m + MyNat.succ n = MyNat.succ n + m
    simp [ih]

#check MyNat.rec

/-- MyNat 用の帰納法の原理を書き直したもの -/
def MyNat.recAux.{u} {motive : MyNat → Sort u}
    (zero : motive 0)
    (succ : (n : MyNat) → motive n → motive (n + 1))
    (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

attribute [induction_eliminator] MyNat.recAux


--要確認
example (m n : Nat) : m + n = n + m := by
  induction n with
  | zero =>
    -- ゼロになっている
    guard_target =ₛ m + 0 = 0 + m
    simp
  | succ n ih =>
    -- (· + 1) と表記されている
    guard_target =ₛ m + (n + 1) = (n + 1) + m
    ac_rfl

/-- 「1 つ前」の自然数を返す関数。ゼロに対してはゼロを返す -/
private def MyNat.pred (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => n

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  rfl
