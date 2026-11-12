import LeanBook.NatSemiring.Mult

example (m n : MyNat) :
    m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  rw [MyNat.mul_add]
  -- 掛け算のオペランドに足し算が残ってしまっている
  guard_target =ₛ m * n + m * 1 + 2 * (m + n) = m * n + 3 * m + 2 * n
  rw [show 2 = 1 + 1 from rfl, show 3 = 1 + 1 + 1 from rfl]
  simp only [MyNat.add_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl

example (m n : MyNat) :
    m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  -- 引数部分が異なるので同じ補題でも 2 回必要だった
  rw [MyNat.mul_add m n 1, MyNat.mul_add 2 m n]
  -- 足し算が外側に来た
  guard_target =ₛ m * n + m * 1 + (2 * m + 2 * n) = m * n + 3 * m + 2 * n
  rw [show 2 = 1 + 1 from rfl, show 3 = 1 + 1 + 1 from rfl]
  simp only [MyNat.add_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl

example (m n : MyNat) :
    m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  -- 引数部分を変えながら繰り返し適用してくれる
  simp only [MyNat.mul_add]
  -- 足し算が外側に来た
  guard_target =ₛ m * n + m * 1 + (2 * m + 2 * n) = m * n + 3 * m + 2 * n
  rw [show 2 = 1 + 1 from rfl, show 3 = 1 + 1 + 1 from rfl]
  simp only [MyNat.add_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl

example (m n : MyNat) :
    m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  simp only [MyNat.mul_add, MyNat.add_mul]
  -- 足し算が外側に来る
  guard_target =ₛ m * n + m * 1 + (2 * m + m * m) = m * n + 3 * m + m * m
  rw [show 2 = 1 + 1 from rfl, show 3 = 1 + 1 + 1 from rfl]
  simp only [MyNat.add_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl

/-- 分配法則を適用して足し算を式の外側に持ってくるタクティク -/
macro "distrib" : tactic =>
  `(tactic| simp only [MyNat.mul_add, MyNat.add_mul])

example (m n : MyNat) :
    m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  distrib
  -- 足し算が外側に来る
  guard_target =ₛ m * n + m * 1 + (2 * m + m * m) = m * n + 3 * m + m * m
  rw [show 2 = 1 + 1 from rfl, show 3 = 1 + 1 + 1 from rfl]
  simp only [MyNat.add_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl

/-- 分配法則を適用して足し算を式の外側に持ってくるタクティク -/
macro "distrib" : tactic =>
  `(tactic| focus
    simp only [MyNat.mul_add, MyNat.add_mul]
    simp only [MyNat.mul_one]
    all_goals ac_rfl)

example (m n : MyNat) :
    m * (n + 1) + (2 + n) * n = m * n + m + 2 * n + n * n := by
  distrib

example (m n : MyNat) :
    m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_one]
  -- ac_rfl だけでは証明できない
  fail_if_success ac_rfl
  -- 同類項の 2 * m と m をまとめる必要がある
  guard_target =ₛ m * n + m + (2 * m + m * m) = m * n + 3 * m + m * m
  rw [show 2 = 1 + 1 from rfl, show 3 = 1 + 1 + 1 from rfl]
  simp only [MyNat.add_mul, MyNat.one_mul]
  ac_rfl

example (m n : MyNat) :
    m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  rw [show 3 = 1 + 2 from rfl]
  rw [show 2 = 1 + 1 from rfl]
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_one, MyNat.one_mul]
  -- ac_rfl が通るようになった
  ac_rfl

/-- 分配法則を適用して足し算を式の外側に持ってくる -/
macro "distrib" : tactic =>
  `(tactic| focus
    rw [show 3 = 1 + 1 + 1 from rfl]
    rw [show 2 = 1 + 1 from rfl]
    simp only [MyNat.mul_add, MyNat.add_mul]
    simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
    ac_rfl)

example (m n : MyNat) :
    m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  distrib

/-- 数値リテラルを 1 + 1 + ⋯ + 1 に分解するための補題 -/
theorem unfoldNatLit (x : Nat) :
    (OfNat.ofNat (x + 2) : MyNat) = (OfNat.ofNat (x + 1) : MyNat) + 1 :=
  rfl

/-- 自然数を 1 + 1 + ⋯ + 1 に分解する -/
macro "expand_num" : tactic =>
  `(tactic| focus
    simp only [unfoldNatLit]
    -- 標準の Nat の和を簡単な形にする
    simp only [Nat.reduceAdd]
    -- OfNat.ofNat を消す
    dsimp only [OfNat.ofNat]
    simp only [
      show MyNat.ofNat 1 = 1 from rfl,
      show MyNat.ofNat 0 = 0 from rfl
    ])

/-- expand_num タクティクのテスト -/
example (n : MyNat) : 3 * n = 2 * n + 1 * n := by
  expand_num
  -- 数値が 1 + 1 + ⋯ + 1 に分解された
  guard_target =ₛ (1 + 1 + 1) * n = (1 + 1) * n + 1 * n
  simp only [MyNat.add_mul]

/-- 分配法則を適用して足し算を式の外側に持ってくる -/
macro "distrib" : tactic =>
  `(tactic| focus
    try expand_num
    try simp only [
      MyNat.mul_add,
      MyNat.add_mul,
      MyNat.mul_zero,
      MyNat.zero_mul,
      MyNat.mul_one,
      MyNat.one_mul
    ]
    all_goals ac_rfl)

/-- distrib タクティクのテスト -/
example (m n : MyNat) : (m + 4) * n + n = m * n + 5 * n := by
  distrib

example (m n : MyNat) : m * n + n * n = (m + n) * n := by
  distrib

/-- 自然数を 1 + 1 + ⋯ + 1 に分解する -/
macro "expand_num" : tactic =>
  `(tactic| focus
    try simp only [unfoldNatLit, Nat.reduceAdd]
    try dsimp only [OfNat.ofNat]
    try simp only [
      show MyNat.ofNat 1 = 1 from rfl,
      show MyNat.ofNat 0 = 0 from rfl
    ])

/-- 分配法則を適用して足し算を式の外側に持ってくる -/
macro "distrib" : tactic =>
  `(tactic| focus
    expand_num
    try simp only [
      MyNat.mul_add,
      MyNat.add_mul,
      MyNat.mul_zero,
      MyNat.zero_mul,
      MyNat.mul_one,
      MyNat.one_mul
    ]
    try ac_rfl)

-- エラーで落ちなくなった！
example (m n : MyNat) : m * n + n * n = (m + n) * n := by
  distrib

example (n : MyNat) : ∃ s t : MyNat, s * t = n * n + 8 * n + 16 := by
  sorry
