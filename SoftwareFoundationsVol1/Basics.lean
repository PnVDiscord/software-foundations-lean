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

example : next_working_day (next_working_day Day.saturday) = Day.tuesday := by rfl

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

def andb (b1 b2 : MyBool) : MyBool :=
  match b1 with
  | MyBool.true => b2
  | MyBool.false => MyBool.false

def orb (b1 b2 : MyBool) : MyBool :=
  match b1 with
  | MyBool.true => MyBool.true
  | MyBool.false => b2

example : orb MyBool.true MyBool.false = MyBool.true := by rfl
example : orb MyBool.false MyBool.false = MyBool.false := by rfl
example : orb MyBool.false MyBool.true = MyBool.true := by rfl
example : orb MyBool.true MyBool.true = MyBool.true := by rfl

infixl:60 " my&& " => andb
infixl:55 " my|| " => orb

example : MyBool.false my|| MyBool.false my|| MyBool.true = MyBool.true := by rfl

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

def andb' (b1 b2 : MyBool) : MyBool :=
  if b1 then b2
  else MyBool.false

def orb' (b1 b2 : MyBool) : MyBool :=
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
  /- REPLACE THIS LINE WITH YOUR DEFINITION " -/ by sorry
example : (nandb MyBool.true MyBool.false) = true :=
  /- FILL IN HERE -/ by sorry
example : (nandb MyBool.false MyBool.false) = true :=
  /- FILL IN HERE -/ by sorry
example : (nandb MyBool.false MyBool.true) = true :=
  /- FILL IN HERE -/ by sorry
example : (nandb MyBool.true MyBool.true) = false :=
  /- FILL IN HERE -/ by sorry

-- ### Exercise: 1 star, standard (andb3)
def andb3 (b1 b2 b3 : MyBool) : MyBool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION " -/ by sorry
example : andb3 MyBool.true MyBool.true MyBool.true = MyBool.true :=
  /- FILL IN HERE -/ by sorry
example : andb3 MyBool.false MyBool.true MyBool.true = MyBool.false :=
  /- FILL IN HERE -/ by sorry
example : andb3 MyBool.true MyBool.false MyBool.true = MyBool.false :=
  /- FILL IN HERE -/ by sorry
example : andb3 MyBool.true MyBool.true MyBool.false = MyBool.false :=
  /- FILL IN HERE -/ by sorry

-- ## Types
#check MyBool.true -- MyBool.true : MyBool
#check negb MyBool.true -- negb MyBool.true : MyBool
#check negb -- negb (b : MyBool) : MyBool

-- ## New Types from Old
inductive rgb : Type where
  | red
  | green
  | blue
inductive color : Type where
  | black
  | white
  | primary (p : rgb)
