-- Basics: Functional Programming in Coq
--
-- https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html

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
  | Day.monday    => Day.tuesday
  | Day.tuesday   => Day.wednesday
  | Day.wednesday => Day.thursday
  | Day.thursday  => Day.friday
  | Day.friday    => Day.monday
  | Day.saturday  => Day.monday
  | Day.sunday    => Day.monday

-- NOTE: You can skip the name of the type before the constructors
-- when lean can infer it.
def next_working_day' (day : Day) : Day :=
  match day with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday

#eval next_working_day .friday -- Day.monday
#eval next_working_day (next_working_day .saturday) -- Day.tuesday

example : next_working_day (next_working_day .saturday) = .tuesday := rfl

-- ## Booleans
-- NOTE: Unlike in Coq, Lean4 does have a built-in `Bool` type. So we will
-- define `MyBool` instead of `Bool` to avoid confusion with the built-in type.
inductive MyBool : Type where
  | true
  | false

def negb (b : MyBool) : MyBool :=
  match b with
  | .true => .false
  | .false => .true

def andb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | .true => b2
  | .false => .false

def orb (b1 : MyBool) (b2 : MyBool) : MyBool :=
  match b1 with
  | .true => .true
  | .false => b2

example : orb .true  .false = .true := rfl
example : orb .false .false = .false := rfl
example : orb .false .true  = .true := rfl
example : orb .true  .true  = .true := rfl

infixl:60 " my&& " => andb
infixl:55 " my|| " => orb

example : .false my|| .false my|| .true = .true := rfl

-- Unlike in Coq, Lean4 does not treat first clause constructors as a truthy
-- value. So we need to define our own coercion from `MyBool` to `Bool` to
-- allow using `if` expressions with `MyBool` values.
@[coe]
def MyBool.toBool (b : MyBool) : Bool :=
  match b with
  | .true => True
  | .false => False
-- Typeclass for coercion from `MyBool` to `Bool`. If you don't know what a type
-- class is, just skip it for now.
instance : Coe MyBool Bool where coe := MyBool.toBool

def negb' (b : MyBool) : MyBool :=
  if b then .false
  else .true

def andb' (b1 : MyBool) (b2 : MyBool) : MyBool :=
  if b1 then b2
  else .false

def orb' (b1 : MyBool) (b2 : MyBool) : MyBool :=
  if b1 then .true
  else b2

inductive BW : Type where
  | black
  | white

-- Unlike the original software foundations book,
-- let's not abuse the `if` expression as a binary pattern match construct.
def invert (x: BW) : BW :=
  match x with
  | .black => .white
  | .white => .black

#eval invert .black -- BW.white
#eval invert .white -- BW.black

-- ### Exercise: 1 star, standard (nandb)
-- TODO: Replace `sorry` with your definitions.
def nandb (b1 b2 : MyBool) : MyBool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry
example : (nandb .true .false) = true :=
  /- FILL IN HERE -/ sorry
example : (nandb .false .false) = true :=
  /- FILL IN HERE -/ sorry
example : (nandb .false .true) = true :=
  /- FILL IN HERE -/ sorry
example : (nandb .true .true) = false :=
  /- FILL IN HERE -/ sorry

-- ### Exercise: 1 star, standard (andb3)
def andb3 (b1 b2 b3 : MyBool) : MyBool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry
example : andb3 .true .true .true = .true :=
  /- FILL IN HERE -/ sorry
example : andb3 .false .true .true = .false :=
  /- FILL IN HERE -/ sorry
example : andb3 .true .false .true = .false :=
  /- FILL IN HERE -/ sorry
example : andb3 .true .true .false = .false :=
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
  | .black => true
  | .white => true
  | .primary _ => false

def isred (c : Color) : Bool :=
  match c with
  | .black => false
  | .white => false
  | .primary .red => true
  | .primary _ => false

-- ## Modules
-- In Lean, we use `namespace` to achieve a similar effect to Coq's `Module`.
namespace Playground
  def foo : RGB := .blue
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
    | bits (d0 d1 d2 d3 : Bit)

  #check (Nybble.bits .b1 .b0 .b1 .b0 : Nybble)

  def all_zero (nb : Nybble) : Bool :=
    match nb with
    | .bits .b0 .b0 .b0 .b0 => true
    | .bits _ _ _ _ => false

  #eval all_zero (Nybble.bits .b1 .b0 .b1 .b0) -- false
  #eval all_zero (Nybble.bits .b0 .b0 .b0 .b0) -- true
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
    | .zero => .zero
    | .succ n' => n'
end NatPlayground

#check Nat.succ (.succ (.succ (.succ .zero))) -- Nat.zero.succ.succ.succ.succ : Nat
-- NOTE: Lean treats `n.succ` as a `Nat.succ n`
#check Nat.zero.succ.succ.succ.succ -- Nat.zero.succ.succ.succ.succ : Nat

def minustwo (n : Nat) : Nat :=
  match n with
  | .zero => .zero
  | .succ .zero => .zero
  | .succ (.succ n') => n'

#eval minustwo 4 -- 2

#check (Nat.succ : Nat → Nat)
#check (Nat.pred : Nat → Nat)
#check (minustwo : Nat → Nat)

def even (n : Nat) : Bool :=
  match n with
  | .zero => true
  | .succ .zero => false
  | .succ (.succ n') => even n'

def odd (n : Nat) : Bool :=
  not (even n)

example : odd 1 = true := rfl
example : odd 4 = false := rfl

namespace NatPlayground2
  def plus (n : Nat) (m : Nat) : Nat :=
    match n with
    | .zero => m
    | .succ n' => .succ (plus n' m)

  #eval plus 3 2 -- 5

  def mult (n m : Nat) : Nat :=
    match n with
    | .zero => .zero
    | .succ n' => plus m (mult n' m)

  example : mult 3 3 = 9 := rfl

  def minus (n m : Nat) : Nat :=
    match n, m with
    | .zero, _ => .zero
    | .succ _, .zero => n
    | .succ n', .succ m' => minus n' m'
end NatPlayground2

def exp (base power : Nat) : Nat :=
  match power with
  | .zero => .succ .zero
  | .succ p => Nat.mul base (exp base p)

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
  | .zero =>
    match m with
    | .zero => true
    | .succ _ => false
  | .succ n' =>
    match m with
    | .zero => false
    | .succ m' => eqb n' m'

def leb (n m : Nat) : Bool :=
  match n with
  | .zero => true
  | .succ n' =>
    match m with
    | .zero => false
    | .succ m' => leb n' m'

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
theorem zero_nbeq_add_one : ∀ n : Nat, (0 =? n + 1) = false := by
  /- FILL IN HERE -/ sorry

-- ## More on Notation (Optional)
-- NOTE: We'll skip `Exercise: 2 stars, standard, optional (decreasing)`,
-- as lean fails to show termination for the intended solution (like in Coq).

-- # More Exercises

-- ## Warmups

-- ### Exercise: 1 star, standard (identity_fn_applied_twice)
theorem identity_fn_applied_twice :
  ∀ (f : Bool → Bool),
  (∀ (x : Bool), f x = x) →
  ∀ (b : Bool), f (f b) = b := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 1 star, standard (negation_fn_applied_twice)
/- FILL IN HERE -/

-- ### Exercise: 3 stars, standard, optional (and_eq_or)
theorem and_eq_or :
  ∀ (b c : Bool),
  (and b c = or b c) →
  b = c := by
  /- FILL IN HERE -/ sorry

-- ## Course Late Policies, Formalized
namespace LateDays
  inductive Letter : Type where
    | a | b | c | d | f

  inductive Modifier : Type where
    | plus | natural | minus

  inductive Grade : Type where
    | grade (l : Letter) (m : Modifier)

  inductive Comparison : Type where
    | eq -- equal
    | lt -- less than
    | gt -- greater than

  def letter_comparison (l1 l2 : Letter) : Comparison :=
    match l1, l2 with
    | .a, .a                            => .eq
    | .a, _                             => .gt
    | .b, .a                            => .lt
    | .b, .b                            => .eq
    | .b, _                             => .gt
    | .c, .a | .c, .b                   => .lt
    | .c, .c                            => .eq
    | .c, _                             => .gt
    | .d, .a | .d, .b | .d, .c          => .lt
    | .d, .d                            => .eq
    | .d, _                             => .gt
    | .f, .a | .f, .b | .f, .c | .f, .d => .lt
    | .f, .f                            => .eq

  #eval letter_comparison .b .a -- .lt
  #eval letter_comparison .d .d -- .eq
  #eval letter_comparison .b .f -- .gt

  -- ### Exercise: 1 star, standard (letter_comparison)
  def letter_comparison_eq :
    ∀ l, letter_comparison l l = .eq := by
    /- FILL IN HERE -/ sorry

  def modifier_comparison (m1 m2 : Modifier) : Comparison :=
    match m1, m2 with
    | .plus, .plus                     => .eq
    | .plus, _                         => .gt
    | .natural, .plus                  => .lt
    | .natural, .natural               => .eq
    | .natural, _                      => .gt
    | .minus, .plus | .minus, .natural => .lt
    | .minus, _                        => .eq

  -- ### Exercise: 2 stars, standard (grade_comparison)
  def grade_comparison (g1 g2 : Grade) : Comparison :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : grade_comparison (.grade .a .minus) (.grade .b .plus) = .gt :=
    /- FILL IN HERE -/ sorry

  example : grade_comparison (.grade .a .minus) (.grade .a .plus) = .lt :=
    /- FILL IN HERE -/ sorry

  example : grade_comparison (.grade .f .plus) (.grade .f .plus) = .eq :=
    /- FILL IN HERE -/ sorry

  example : grade_comparison (.grade .b .minus) (.grade .c .plus) = .gt :=
    /- FILL IN HERE -/ sorry

  def lower_letter (l : Letter) : Letter :=
    match l with
    | .a => .b
    | .b => .c
    | .c => .d
    | .d => .f
    | .f => .f -- Can't go lower than F!

  theorem lower_letter_lowers_wrong :
    ∀ (l : Letter), letter_comparison (lower_letter l) l = .lt := by
    intro l
    cases l
    . rfl -- a -> b
    . rfl -- b -> c
    . rfl -- c -> d
    . rfl -- d -> f
    . sorry -- We get stuck here

  theorem lower_letter_f_is_f : lower_letter .f = .f := by
    rfl

  -- ### Exercise: 2 stars, standard (lower_letter_lowers)
  theorem lower_letter_lowers :
    ∀ (l : Letter),
    letter_comparison .f l = .lt →
    letter_comparison (lower_letter l) l = .lt := by
    /- FILL IN HERE -/ sorry

  -- ### Exercise: 2 stars, standard (lower_grade)
  def lower_grade (g : Grade) : Grade :=
    /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

  example : lower_grade (.grade .a .plus) = (.grade .a .natural) :=
    /- FILL IN HERE -/ sorry

  example : lower_grade (.grade .a .natural) = (.grade .a .minus) :=
    /- FILL IN HERE -/ sorry

  example : lower_grade (.grade .a .minus) = (.grade .b .plus) :=
    /- FILL IN HERE -/ sorry

  example : lower_grade (.grade .b .plus) = (.grade .b .natural) :=
    /- FILL IN HERE -/ sorry

  example : lower_grade (.grade .f .natural) = (.grade .f .minus) :=
    /- FILL IN HERE -/ sorry

  example : lower_grade (lower_grade (.grade .b .minus)) = (.grade .c .natural) :=
    /- FILL IN HERE -/ sorry

  example : lower_grade (lower_grade (lower_grade (.grade .b .minus))) = (.grade .c .minus) :=
    /- FILL IN HERE -/ sorry

  theorem lower_grade_f_minus : lower_grade (.grade .f .minus) = (.grade .f .minus) := by
    /- FILL IN HERE -/ sorry

  -- ### Exercise: 3 stars, standard (lower_grade_lowers)
  theorem lower_grade_lowers :
    ∀ (g : Grade),
    grade_comparison (.grade .f .minus) g = .lt →
    grade_comparison (lower_grade g) g = .lt := by
    /- FILL IN HERE -/ sorry

  def apply_late_policy (late_days : Nat) (g : Grade) : Grade :=
    if late_days <? 9 then g
    else if late_days <? 17 then lower_grade g
    else if late_days <? 21 then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g))

  theorem apply_late_policy_unfold :
    ∀ (late_days : Nat) (g : Grade), apply_late_policy late_days g
    =
    if late_days <? 9 then g
    else if late_days <? 17 then lower_grade g
    else if late_days <? 21 then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g))
  := by
    intros
    rfl

  -- ### Exercise: 2 stars, standard (no_penalty_for_mostly_on_time)
  theorem no_penalty_for_mostly_on_time :
    ∀ (late_days : Nat) (g : Grade),
    (late_days <? 9) = true →
    apply_late_policy late_days g = g
  := by
    /- FILL IN HERE -/ sorry

  -- ### Exercise: 2 stars, standard (graded_lowered_once)
  theorem grade_lowered_once :
    ∀ (late_days : Nat) (g : Grade),
      (late_days <? 9) = false →
      (late_days <? 17) = true →
      apply_late_policy late_days g = lower_grade g
  := by
    /- FILL IN HERE -/ sorry
end LateDays

-- ## Binary Numerals

-- ### Exercise: 3 stars, standard (binary)
inductive Bin : Type where
  | z
  | b0 (n : Bin)
  | b1 (n : Bin)

def incr (m : Bin) : Bin :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

def bin_to_nat (m : Bin) : Nat :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : (incr (.b1 .z)) = .b0 (.b1 .z) :=
  /- FILL IN HERE -/ sorry

example : (incr (.b0 (.b1 .z))) = .b1 (.b1 .z) :=
  /- FILL IN HERE -/ sorry

example : (incr (.b1 (.b1 .z))) = .b0 (.b0 (.b1 .z)) :=
  /- FILL IN HERE -/ sorry

example : bin_to_nat (.b0 (.b1 .z)) = 2 :=
  /- FILL IN HERE -/ sorry

example : bin_to_nat (incr (.b1 .z)) = 1 + bin_to_nat (.b1 .z) :=
  /- FILL IN HERE -/ sorry

example : bin_to_nat (incr (incr (.b1 .z))) = 2 + bin_to_nat (.b1 .z) :=
  /- FILL IN HERE -/ sorry
