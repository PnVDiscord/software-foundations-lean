-- # Data and Functions

-- ## Days of the Week
inductive Day : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

def next_working_day (day : Day) : Day :=
  match day with
  | Day.monday => Day.tuesday
  | Day.tuesday => Day.wednesday
  | Day.wednesday => Day.thursday
  | Day.thursday => Day.friday
  | Day.friday => Day.monday
  | Day.saturday => Day.monday
  | Day.sunday => Day.monday

#eval next_working_day Day.friday -- Day.monday
#eval next_working_day (next_working_day Day.saturday) -- Day.tuesday

example : next_working_day (next_working_day Day.saturday) = Day.tuesday := rfl

-- ## Booleans
-- NOTE: Unlike in Coq, Lean4 does have a built-in `Bool` type. So we will
-- define `MyBool` instead of `Bool` to avoid confusion with the built-in type.
inductive MyBool : Type where
  | true
  | false

def negb (b : MyBool) : MyBool :=
  match b with
  | MyBool.true => MyBool.false
  | MyBool.false => MyBool.true

def andb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | MyBool.true => b2
  | MyBool.false => MyBool.false

def orb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | MyBool.true => MyBool.true
  | MyBool.false => b2

example : orb MyBool.true MyBool.false = MyBool.true := rfl
example : orb MyBool.false MyBool.false = MyBool.false := rfl
example : orb MyBool.false MyBool.true = MyBool.true := rfl
example : orb MyBool.true MyBool.true = MyBool.true := rfl

infixl:60 " my&& " => andb
infixl:55 " my|| " => orb

example : MyBool.false my|| MyBool.false my|| MyBool.true = MyBool.true := rfl

-- Unlike in Coq, Lean4 does not treat first clause constructors as a truthy
-- value. So we need to define our own coercion from `MyBool` to `Bool` to
-- allow using `if` statements with `MyBool` values.
@[coe]
def MyBool.toBool (b : MyBool) : Bool :=
  match b with
  | MyBool.true => True
  | MyBool.false => False
-- Typeclass for coercion from `MyBool` to `Bool`. If you don't know what a type
-- class is, just skip it for now.
instance : Coe MyBool Bool where coe := MyBool.toBool

def negb' (b : MyBool) : MyBool :=
  if b
  then MyBool.false
  else MyBool.true

def andb' (b1 : MyBool) (b2 : MyBool) : MyBool :=
  if b1 then b2
  else MyBool.false

def orb' (b1 : MyBool) (b2 : MyBool) : MyBool :=
  if b1 then MyBool.true
  else b2

inductive BW : Type where
  | black
  | white

-- Unlike the original software foundations book,
-- let's not abuse the `if` statement as a binary pattern matching.
def invert (x: BW) : BW :=
  match x with
  | BW.black => BW.white
  | BW.white => BW.black

#eval invert BW.black -- BW.white
#eval invert BW.white -- BW.black

-- ### Exercise: 1 star, standard (nandb)
-- TODO: Replace `sorry` with your definition.
def nandb (b1 b2 : MyBool) : MyBool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry
example : (nandb MyBool.true MyBool.false) = true :=
  /- FILL IN HERE -/ sorry
example : (nandb MyBool.false MyBool.false) = true :=
  /- FILL IN HERE -/ sorry
example : (nandb MyBool.false MyBool.true) = true :=
  /- FILL IN HERE -/ sorry
example : (nandb MyBool.true MyBool.true) = false :=
  /- FILL IN HERE -/ sorry

-- ### Exercise: 1 star, standard (andb3)
def andb3 (b1 b2 b3 : MyBool) : MyBool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry
example : andb3 MyBool.true MyBool.true MyBool.true = MyBool.true :=
  /- FILL IN HERE -/ sorry
example : andb3 MyBool.false MyBool.true MyBool.true = MyBool.false :=
  /- FILL IN HERE -/ sorry
example : andb3 MyBool.true MyBool.false MyBool.true = MyBool.false :=
  /- FILL IN HERE -/ sorry
example : andb3 MyBool.true MyBool.true MyBool.false = MyBool.false :=
  /- FILL IN HERE -/ sorry

-- NOTE: We'll use lean's built-in `Bool` instead of `MyBool`
-- for the rest of the file.

-- ## Types
#check true -- Bool.true : Bool

#check (true : Bool)
#check (not true : Bool)
#check (not : Bool → Bool)

-- ## New Types from Old
inductive RGB : Type where
  | red
  | green
  | blue
inductive Color : Type where
  | black
  | white
  | primary (p : RGB)

def monochrome (c : Color) : Bool :=
  match c with
  | Color.black => true
  | Color.white => true
  | Color.primary _ => false

def isred (c : Color) : Bool :=
  match c with
  | Color.black => false
  | Color.white => false
  | Color.primary RGB.red => true
  | Color.primary _ => false

-- ## Modules
-- In Lean, we use `namespace` to achieve a similar effect to Coq's `Module`.
namespace Playground
  def foo : RGB := RGB.blue
end Playground

def foo : Bool := true

#check (Playground.foo : RGB)
#check (foo : Bool)

-- ## Tuples
namespace TuplePlayground
  inductive Bit : Type where
    | b1
    | b0
  inductive Nybble : Type where
    | bits (b0 b1 b2 b3 : Bit)

  #check (Nybble.bits Bit.b1 Bit.b0 Bit.b1 Bit.b0 : Nybble)

  def all_zero (nb : Nybble) : Bool :=
    match nb with
    | Nybble.bits Bit.b0 Bit.b0 Bit.b0 Bit.b0 => true
    | Nybble.bits _ _ _ _ => false

  #eval all_zero (Nybble.bits Bit.b1 Bit.b0 Bit.b1 Bit.b0) -- false
  #eval all_zero (Nybble.bits Bit.b0 Bit.b0 Bit.b0 Bit.b0) -- true
end TuplePlayground

-- ## Numbers
-- NOTE: Lean has a built-in `Nat` type. We will define `NatPlayground.Nat` to
-- follow the book's spirit of building everything from scratch.
namespace NatPlayground
  inductive Nat : Type where
    | zero
    | succ (n : Nat)

  inductive OtherNat : Type where
    | stop
    | tick (n : OtherNat)

  def pred (n : Nat) : Nat :=
    match n with
    | Nat.zero => Nat.zero
    | Nat.succ n' => n'
end NatPlayground

#check Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))) -- Nat.zero.succ.succ.succ.succ : Nat
-- NOTE: Lean treats `n.succ` as a `Nat.succ n`
#check Nat.zero.succ.succ.succ.succ -- Nat.zero.succ.succ.succ.succ : Nat

def minustwo (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ Nat.zero => Nat.zero
  | Nat.succ (Nat.succ n') => n'

#eval minustwo 4 -- 2

#check (Nat.succ : Nat → Nat)
#check (Nat.pred : Nat → Nat)
#check (minustwo : Nat → Nat)

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ Nat.zero => false
  | Nat.succ (Nat.succ n') => even n'

def odd (n : Nat) : Bool :=
  not (even n)

example : odd 1 = true := rfl
example : odd 4 = false := rfl

namespace NatPlayground2
  def plus (n : Nat) (m : Nat) : Nat :=
    match n with
    | Nat.zero => m
    | Nat.succ n' => Nat.succ (plus n' m)

  #eval plus 3 2 -- 5

  def mult (n m : Nat) : Nat :=
    match n with
    | Nat.zero => Nat.zero
    | Nat.succ n' => plus m (mult n' m)

  example : mult 3 3 = 9 := rfl

  def minus (n m : Nat) : Nat :=
    match n, m with
    | Nat.zero, _ => Nat.zero
    | Nat.succ _, Nat.zero => n
    | Nat.succ n', Nat.succ m' => minus n' m'
end NatPlayground2

def exp (base power : Nat) : Nat :=
  match power with
  | Nat.zero => Nat.succ Nat.zero
  | Nat.succ p => Nat.mul base (exp base p)

-- ### Exercise: 1 star, standard (factorial)
def factorial (n : Nat) : Nat :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry
example : factorial 3 = 6 :=
  /- FILL IN HERE -/ sorry
example : factorial 5 = Nat.mul 10 12 :=
  /- FILL IN HERE -/ sorry

infixl:65 " my+ " => Nat.add
infixl:65 " my- " => Nat.sub
infixl:70 " my* " => Nat.mul

#check (((0 my+ 1) my+ 1) : Nat)

def eqb (n m : Nat) : Bool :=
  match n with
  | Nat.zero =>
    match m with
    | Nat.zero => true
    | Nat.succ _ => false
  | Nat.succ n' =>
    match m with
    | Nat.zero => false
    | Nat.succ m' => eqb n' m'

def leb (n m : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ n' =>
    match m with
    | Nat.zero => false
    | Nat.succ m' => leb n' m'

example : leb 2 2 = true := rfl
example : leb 2 4 = true := rfl
example : leb 4 2 = false := rfl

infix:50 " =? " => eqb
infix:50 " <=? " => leb

example : (4 <=? 2) = false := rfl

-- ### Exercise: 1 star, standard (ltb)
def ltb (n m : Nat) : Bool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

infix:50 " <? " => ltb

example : ltb 2 2 = false :=
  /- FILL IN HERE -/ sorry
example : ltb 2 4 = true :=
  /- FILL IN HERE -/ sorry
example : ltb 4 2 = false :=
  /- FILL IN HERE -/ sorry

-- # Proof by Simplification
theorem zero_add : ∀ n : Nat, 0 + n = n := by
  intro n
  simp

theorem zero_add'': ∀ n : Nat, 0 + n = n := by
  intro m
  simp

theorem add_one : ∀ n : Nat, n + 1 = Nat.succ n := by
  intro n
  simp

theorem zero_mul : ∀ n : Nat, 0 * n = 0 := by
  intros n
  simp

-- # Proof by Rewriting
theorem plus_id_example : ∀ n m : Nat, n = m → n + n = m + m := by
  -- move both quantifiers into the context
  intro n m
  -- move the hypothesis into the context
  intro h
  -- rewrite the goal using the hypothesis
  rewrite [h]
  rfl

-- ### Exercise: 1 star, standard (plus_id_exercise)
theorem plus_id_exercise : ∀ n m o : Nat, n = m → m = o → n + m = m + o := by
  /- FILL IN HERE -/ sorry

#check Nat.mul_zero -- Nat.mul_zero (n : Nat) : n * 0 = 0
#check Nat.mul_succ -- Nat.mul_succ (n m : Nat) : n * m.succ = n * m + n

theorem mul_zero_add_mul_zero_eq_zero : ∀ p q : Nat, (p * 0) + (q * 0) = 0 := by
  intro p q
  rewrite [Nat.mul_zero]
  rewrite [Nat.mul_zero]
  rfl

-- ### Exercise: 1 star, standard (mult_n_1)
theorem mul_one : ∀ p : Nat, p * 1 = p := by
  /- FILL IN HERE -/ sorry

-- # Proof by Case Analysis
theorem add_one_neq_zero_firsttry : ∀ n : Nat, (n + 1 =? 0) = false := by
  intro n
  -- simp: does nothing!
  sorry

theorem add_one_neq_zero : ∀ n : Nat, (n + 1 =? 0) = false := by
  intro n
  cases n
  rfl
  rfl

theorem not_involutive : ∀ b : Bool, not (not b) = b := by
  intro b
  cases b
  . rfl
  . rfl

theorem and_commutative : ∀ b c : Bool, and b c = and c b := by
  intro b c
  cases b
  . cases c
    . rfl
    . rfl
  . cases c
    . rfl
    . rfl

theorem and_commutative' : ∀ b c : Bool, and b c = and c b := by
  intro b c
  cases b with
  | true => cases c with
    | true => rfl
    | false => rfl
  | false => cases c with
    | true => rfl
    | false => rfl

theorem and_commutative''' : ∀ b c : Bool, and b c = and c b := by
  intro b c
  cases b <;> cases c <;> rfl

theorem and3_exchange : ∀ b c d : Bool, and (and b c) d = and (and b d) c := by
  intro b c d
  cases b
  . cases c
    . cases d
      . rfl
      . rfl
    . cases d
      . rfl
      . rfl
  . cases c
    . cases d
      . rfl
      . rfl
    . cases d
      . rfl
      . rfl

theorem and3_exchange' : ∀ b c d : Bool, and (and b c) d = and (and b d) c := by
  intro b c d
  cases b <;> cases c <;> cases d <;> rfl

-- ### Exercise: 2 stars, standard (andb_true_elim2)
theorem and_true_elim2 : ∀ b c : Bool, and b c = true → c = true := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 1 star, standard (zero_nbeq_plus_1)
theorem zero_nbeq_add_one : ∀ n : Nat, 0 =? n + 1 = false := by
  /- FILL IN HERE -/ sorry

-- # More Exercises
