
inductive MyNat where
  | zero
  | succ (n : MyNat)

#check MyNat.zero
#check MyNat.succ

#check MyNat.succ MyNat.zero

def MyNat.one := MyNat.succ .zero

def MyNat.two := MyNat.succ .one

/--足し算-/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n => MyNat.succ (MyNat.add m n)


set_option pp.fieldNotation.generalized false

#check MyNat.add .one .one = .two


set_option pp.fieldNotation.generalized true in

#check MyNat.add .one .one = .two


#reduce MyNat.add .one .one
#reduce MyNat.two

example : MyNat.add .one .one = .two := by
 rfl

example (n : MyNat) : MyNat.add n .zero = n := by
 rfl

#check Prop

#check ( 1 + 1 = 3 : Prop )

#check (fun n => n + 3 = 39 : Nat -> Prop)

#check True
#check False

example : True := by trivial
example (P : Prop) (h : P) : P := by
 exact h

example (P : Prop) (h : P) : P := by
 assumption

example (h : False) : ∀ x y z n : Nat,
 n ≥ 3 -> x ^ n + y ^ n = z ^ n -> x * y * z = 0 := by
 trivial


example ( P Q R : Prop) : (P -> Q -> R) = (P -> (Q -> R)) := by
 rfl

#eval True -> True
#eval True -> False
#eval False -> True
#eval False -> False



example (P Q : Prop) (h : P -> Q) (hp : P) : Q := by
 apply h
 apply hp


example (P Q : Prop) (h : P -> Q) (hp : P) : Q := by
 exact h hp


example ( P Q : Prop ) (hq : Q ) : P -> Q := by
 intro hp
 exact hq



#eval ¬ True
#eval ¬ False

example (P : Prop) : (¬ P) = (P -> False) := by
 rfl



example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
 apply hnp
 exact hp


example ( P Q : Prop) (h : P -> ¬ Q) : Q -> ¬ P := by
 intro hq
 intro hp
 exact h hp hq


example ( P : Prop) (hnp : ¬ P) (hp : P) : False := by
 contradiction


example ( P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
 exfalso
 contradiction

#eval True <-> True
#eval True <-> False
#eval False <-> True
#eval False <-> False


example ( P Q : Prop) (h1 : P -> Q) (h2 : Q -> P) : P <-> Q := by
 constructor
 · exact h1
 · exact h2


example ( P Q : Prop) (hq : Q) : (Q -> P) <-> P := by
 constructor

 case mp =>
  intro h
  exact h hq

 case mpr =>
  intro hp hq
  exact hp



example ( P Q : Prop) (hq : Q ) : ( Q -> P ) <-> P := by
 constructor <;> intro h

 case mp =>
  exact h hq

 case mpr =>
  intro hq
  exact h


example (P Q : Prop) (h : P <-> Q) (hq : Q) : P := by
 rw[h]
 exact hq



example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
 rw[← h]
 exact hp


example (P Q : Prop) (h : P ↔ Q) : P = Q := by
 rw [h]




/- 3.16　論理積 -/

#eval True ∧ True
#eval True ∧ False
#eval False ∧ True
#eval False ∧ False



example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
 constructor
 · exact hp
 · exact hq




example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
 exact ⟨hp,hq⟩


example (P Q : Prop) (h : P ∧ Q ) := by
 exact h.left
example (P Q : Prop) (h : P ∧ Q ) := by
 exact h.right



/- 3.16　論理和 -/

#eval True ∨  True
#eval True ∨  False
#eval False ∨  True
#eval False ∨  False

example (P Q : Prop ) (hp : P) : P ∨ Q := by
 left
 exact hp

example (P Q : Prop ) (hq : Q) : P ∨ Q := by
 right
 exact hq


example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
 cases h with
 | inl hp =>
   right
   exact hp
 | inr hq =>
   left
   exact hq


example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
 cases h
 case inl hp =>
  right
  exact hp
 case inr hq =>
  left
  exact hq



/- 3.1.8　練習問題-/
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
 constructor

 case mp =>
  intro h
  constructor
  · intro hp
    apply h
    left
    exact hp
  · intro hq
    apply h
    right
    exact hq
 case mpr =>
  intro h
  intro h2
  cases h2 with
  | inl hp =>
    exact h.left hp
  | inr hq =>
    exact h.right hq



/-解答-/
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor <;> intro h1
  · constructor <;> intro h2
    · apply h1
      left
      assumption
    · apply h1
      right
      assumption
  · intro hpq
    cases hpq with
    | inl hp =>
      apply h1.left
      assumption
    | inr hq =>
      apply h1.right
      assumption



/-haveタクティク、補題-/
example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp

  have hn2p : ¬¬ P := by
   intro hnp
   contradiction

  contradiction


example (P : Prop) : ¬¬¬ P → ¬P := by
  intro hn3p hp

  have : ¬¬ P := by
   intro hnp
   contradiction

  guard_hyp this : ¬¬ P

  contradiction



example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  intro h

  suffices hyp : ¬ P from by
   have : P ∨ ¬ P := by
     right
     exact hyp

   contradiction


  guard_target =ₛ ¬ P

  /-Pを仮定して矛盾を導く-/
  intro hq

  have : P ∨ ¬ P := by
    left
    exact hq

  contradiction





example (P : Prop) : (P → True) ↔ True := by
 exact?

example (P : Prop) : (True → P) ↔ P := by
 exact?


example (P Q : Prop) (h : ¬P ↔ Q) : (P →  False) ↔ Q := by
 rw [show (P → False) ↔ ¬P from by rfl]
 rw [h]


/-練習問題-/
example (P : Prop) : ¬ (P ↔ ¬ P) := by
 intro h

 have hpnp : P → ¬ P := by
  exact h.mp
 have hnp : ¬ P := by
  intro hp
  exact hpnp hp hp

 have hp : P := by
  exact h.mpr hnp
 contradiction



/-述語論理-/

def P (n : Nat) : Prop := n = n

example : ∀ a : Nat , P a := by
 intro x
 dsimp[P]

example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
 exact h 0


def even (n : Nat) : Prop := ∃ m : Nat, n = m + m

example : even 4 := by
 exists 2


example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x) : ∃ x : α, Q x := by
 obtain ⟨y, hy⟩ := h
 exists y
 exact hy.right


opaque Human : Type
opaque Love : Human → Human → Prop

@[inherit_doc] infix:50 " -♥→ " => Love

def IdolExists : Prop := ∃ idol : Human , ∀ h : Human, h -♥→ idol

def EveryoneLovesSomeone : Prop := ∀ h : Human , ∃ tgt : Human, h -♥→ tgt

#check ∃ philan : Human, ∀ h : Human, philan -♥→ h
def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -♥→ h

#check ∀ h : Human, ∃ lover : Human, lover -♥→ h
def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -♥→ h

example : PhilanExists → EveryoneLoved := by
 intro h
 obtain ⟨philan, h⟩ := h
 dsimp [EveryoneLoved]
 intro human
 exists philan
 exact h human


/-練習問題-/
example : IdolExists → EveryoneLovesSomeone := by
 intro h
 obtain ⟨idol1, h1⟩ := h
 dsimp [EveryoneLovesSomeone]
 intro human
 exists idol1
 exact h1 human


/-直観主義-/
example (P : Prop) : ¬¬ P →  P := by
 intro hn2p
 by_cases h : P
 · exact h
 · contradiction

/-練習問題-/
example (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) := by
 constructor

 case mp =>
  intro h
  by_cases h1 : P
  · right
    exact h h1
  · left
    exact h1
 case mpr =>
  intro h
  intro hp
  cases h with
  | inl hnp =>
    exfalso
    contradiction
  | inr hq =>
    exact hq


example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
 constructor

 case mp =>
  intro h
  by_cases h1 : P
  · right
    intro hq
    apply h
    constructor
    · exact h1
    · exact hq
  · left
    exact h1

 case mpr =>
   intro hnpq
   intro hpq
   cases hnpq with
   | inl hnpq1 =>
     apply hnpq1
     exact hpq.left
   | inr hnpq2 =>
     apply hnpq2
     exact hpq.right



example (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
 constructor

 case mp =>
  intro h hnq hp
  apply hnq
  apply h
  exact hp

 case mpr =>
  intro h hp
  by_cases hq : Q
  · exact hq
  · exfalso
    have hnp : ¬ P := by
     exact h hq
    contradiction



/-選択原理-/
#check Classical.em
#print axioms Classical.em


#check Classical.choice



def Surjective {X Y : Type} (f : X → Y) : Prop :=
 ∀ y : Y , ∃ x : X, f x = y

example : Surjective (fun x : Nat => x) := by
 intro y
 exists y


variable {X Y : Type}

noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
 intro y
 have : Nonempty {x // f x = y} := by
  let ⟨x, hx⟩ := hf y
  exact ⟨⟨x, hx⟩⟩

 have x := Classical.choice this
 exact x.val



 /-練習問題-/

theorem double_negation_elim' (P : Prop) : ¬¬ (¬ ¬ P → P) := by
 intro h
 have hnp : ¬ P := by
  intro hp
  apply h
  intro hnnp
  exact hp
 apply h
 intro hnnp
 exfalso
 contradiction

#print axioms double_negation_elim'


/-カリーハワード同型対応-/
theorem one_add_one_eq_two : 1+1 = 2 := by
 rfl

#check one_add_one_eq_two
#check (by rfl : 1 + 1 = 2)

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
 exact h hp

def idOnNat : Nat → Nat := by?
 intro n
 exact n

#eval idOnNat 42



/-練習問題-/
example (P Q : Prop) (hp : P) : Q → P :=
 fun hq => hp



#check Nat.add_zero

#check Nat.add_zero 0
#check Nat.add_zero 42

#check (Nat.add_zero : (n : Nat) → n + 0 = n)


example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by
 rfl


set_option pp.foralls false in

#check (∀ n : Nat, n + 0 = n)


inductive Listo (α : Type) : Type where
  | nil
  | cons (a : α) (l : Listo α)


example : List Nat := [0, 1, 2, 3]
example : List Nat := [0, 1]

inductive Vect (α : Type) : Nat → Type where
 | nil : Vect α 0
 | cons {n : Nat} (a : α) (v : Vect α n) : Vect α (n + 1)


example : Vect Nat 0 := Vect.nil
example : Vect Nat 1 := Vect.cons 42 Vect.nil


example :(α : Type) × α := ⟨Nat, 1⟩
example :(α : Type) × α := ⟨Bool, True⟩
example :(α : Type) × α := ⟨Prop, True⟩

example : List ((α : Type) × α) := [⟨Nat, 1⟩,⟨Bool, True⟩,⟨Prop, True⟩]


/-練習問題-/
example :  List ((α : Type) × α) := [⟨Nat, 42⟩, ⟨Bool, False⟩]
example : {α : Type} → {n : Nat} → (a : α) → (v : Vect α n) → Vect α (n+1) := Vect.cons
