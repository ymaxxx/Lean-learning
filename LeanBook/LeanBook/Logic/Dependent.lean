#check Nat.add_zero
#check Nat.add_zero 0
#check Nat.add_zero 42
#check (Nat.add_zero : (n : Nat) → n + 0 = n)

example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by
  rfl

set_option pp.foralls false in
  #check (∀ n : Nat, n + 0 = n)

example : List Nat := [0, 1, 2, 3]
example : List Nat := [0, 1]

inductive Vect (α : Type) : Nat → Type where
  /-- 空ベクトルは長さ 0 のベクトル -/
  | nil : Vect α 0
  /-- ベクトル v : Vect α n の先頭に a : α を追加して新しいベクトルを得る -/
  | cons {n : Nat} (a : α) (v : Vect α n) : Vect α (n + 1)

example : Vect Nat 0 := Vect.nil
example : Vect Nat 1 := Vect.cons 42 Vect.nil

example : (α : Type) × α := ⟨Nat, 1⟩
example : (α : Type) × α := ⟨Bool, true⟩
example : (α : Type) × α := ⟨Prop, True⟩

example : List ((α : Type) × α) :=
  [⟨Nat, 1⟩, ⟨Bool, true⟩, ⟨Prop, True⟩]

-- 練習問題 3.7.4
example : List ((α : Type) × α) :=
  [⟨Nat, 42⟩, ⟨Bool, false⟩]

example : {α : Type} → {n : Nat} → (a : α) → (v : Vect α n) →
    Vect α (n + 1) := Vect.cons

example : Vect Nat 3 :=
  Vect.cons 1 (Vect.cons 2 (Vect.cons 3 Vect.nil))
