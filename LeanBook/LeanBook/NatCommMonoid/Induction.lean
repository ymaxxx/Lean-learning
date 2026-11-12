import LeanBook.NatCommMonoid.TypeClass

example (n : MyNat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change MyNat.succ (0 + n) = MyNat.succ n
    rw [ih]

example (n : MyNat) : n + 0 = n := by
  rfl

#reduce fun (n : MyNat) => n + 0

#reduce fun (n : MyNat) => 0 + n

-- Infoview における表示の仕方を制御するための設定
set_option pp.fieldNotation.generalized false in
example (n : MyNat) : 0 + n = n := by
  -- n についての帰納法で証明する
  induction n with
  -- n = 0 のケース
  | zero =>
    -- ゴールは 0 + MyNat.zero = MyNat.zero
    guard_target =ₛ 0 + MyNat.zero = MyNat.zero
    rfl
  -- n = succ n' のケース
  | succ n' ih =>
    -- ゴールは 0 + MyNat.succ n' = MyNat.succ n'
    guard_target =ₛ 0 + MyNat.succ n' = MyNat.succ n'
    -- 帰納法の仮定 ih : 0 + n' = n'
    guard_hyp ih : 0 + n' = n'
    change MyNat.succ (0 + n') = MyNat.succ n'
    rw [ih]

example (n : MyNat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    change MyNat.succ (0 + n') = MyNat.succ n'
    rw [ih]

/-- 0 を右から足しても変わらない -/
theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by
  rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [MyNat.add_zero]

/-- add_zero の等式の順序が逆のバージョン -/
theorem MyNat.add_zero_rev (n : MyNat) : n = n + 0 := by
  rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [← MyNat.add_zero_rev]

example (m n : MyNat) (h : m + 0 = n) : n + m = m + n := by
  -- 仮定 h を簡略化して m = n を得る
  rw [MyNat.add_zero] at h
  rw [h]

/-- 右のオペランドに付いた .succ は外側に出せる -/
theorem MyNat.add_succ (m n : MyNat) :
    m + .succ n = .succ (m + n) := by
  rfl

/-- 0 を左から足しても変わらない -/
theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  -- n = 0 のケース
  | zero => rfl
  -- n = succ n' のケース
  | succ n' ih =>
    rw [MyNat.add_succ, ih]

example (n : MyNat) : 1 + n = .succ n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [MyNat.add_succ, ih]
