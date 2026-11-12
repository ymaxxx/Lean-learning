import LeanBook.NatCommMonoid.Induction

example (n : MyNat) : 0 + (n + 0) = n := by
  -- 最初は simp で証明できない
  fail_if_success simp
  -- 明示的に rw で証明する
  rw [MyNat.add_zero, MyNat.zero_add]

attribute [simp] MyNat.add_zero MyNat.zero_add

example (n : MyNat) : 0 + (n + 0) = n := by
  -- simp で証明できるようになった!
  simp

/-- MyNat において 0 は zero だと解釈される -/
theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := by
  rfl

example : MyNat.zero = 0 := by
  -- 手動で命題を渡すことで証明できる
  simp [MyNat.ctor_eq_zero]

attribute [simp] MyNat.add_succ

example (m n : MyNat) (h : m + n + 0 = n + m) : m + n = n + m := by
  simp at h
  -- 仮定 h の形が変わった
  guard_hyp h : m + n = n + m
  rw [h]

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp at *
  -- 仮定とゴールの形が変わった
  guard_hyp h : m = n
  guard_target =ₛ m = n
  rw [h]

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  -- 一発で終了する
  simp_all

/-- 左のオペランドに付いた .succ は外側に出せる -/
@[simp] theorem MyNat.succ_add (m n : MyNat) :
    .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [ih]

example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [ih]

example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  -- n = n' のケースまで示せていたと仮定して、n = n'.succ のケースを示す
  | succ n' ih =>
    calc
      .succ m + .succ n' = (.succ m + n').succ := by rw [MyNat.add_succ]
      _ = (m + n').succ.succ := by rw [MyNat.succ_add]
      _ = (m + .succ n').succ := by rw [MyNat.add_succ]

example (n : MyNat) : 1 + n = n + 1 := calc
  1 + n = .succ 0 + n := by rfl
  _ = .succ (0 + n) := by rw [MyNat.succ_add]
  _ = .succ n := by rw [MyNat.zero_add]
  _ = n + 1 := by rfl

example (n : MyNat) : 2 + n = n + 2 := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [ih]
