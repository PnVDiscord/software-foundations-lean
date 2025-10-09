-- Lists: Working with Structured Data
--
-- https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html

import SoftwareFoundations.Induction

namespace NatList
-- # Pairs of Numbers
inductive NatProd where
  | pair (n1 n2 : Nat)

#check (.pair 3 5 : NatProd)

def fst (p : NatProd) : Nat :=
  match p with
  | .pair x _ => x

def snd (p : NatProd) : Nat :=
  match p with
  | .pair _ y => y

#eval (fst (.pair 3 5))

@[coe]
def toNatProd (t : Nat × Nat) : NatProd := .pair t.1 t.2
instance : Coe (Nat × Nat) NatProd where coe := toNatProd

#eval (fst (3, 5))

def swap_pair (p : NatProd) : NatProd :=
  match p with
  | .pair x y => .pair y x

theorem surjective_pairing' : ∀ n m : Nat, (n,m) = (fst (n,m), snd (n,m)) := by
  intro n m
  rfl

theorem surjective_pairing_stuck : ∀ p : NatProd, p = (fst p, snd p) := by
  -- simp: doesn't reduce anything!
  sorry

theorem surjective_pairing : ∀ p : NatProd, p = (fst p, snd p) := by
  intro p
  cases p with
  | pair n m => rfl

-- ### Exercise: 1 star, standard (snd_fst_is_swap)
theorem snd_fst_is_swap : ∀ p : NatProd, (snd p, fst p) = swap_pair p := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 1 star, standard, optional (fst_swap_is_snd)
theorem fst_swap_is_snd : ∀ p : NatProd, fst (swap_pair p) = snd p := by
  /- FILL IN HERE -/ sorry

-- # Lists of Numbers
inductive NatList where
  | nil
  | cons (n : Nat) (l : NatList)

def myList : NatList := .cons 1 (.cons 2 (.cons 3 .nil))

infixr:60 " :: " => NatList.cons
notation "[]" => NatList.nil
-- NOTE: We'll use ',' as the separator instead of ';' in the list`
macro_rules
  | `([$hd:term , $tl:term,*]) => `(NatList.cons $(Lean.quote hd) ([$tl,*]))
  | `([$hd:term])    => `(NatList.cons $(Lean.quote hd) NatList.nil)
  | `([])      => `(NatList.nil)


def myList1 : NatList := 1 :: (2 :: (3 :: .nil))
def myList2 : NatList := 1 :: 2 :: 3 :: .nil
def myList3 : NatList := [1, 2, 3]

-- As `repeat` is keyword in Lean, we use `repeatN` instead.
def repeatN (n count : Nat) : NatList :=
  match count with
  | .zero => .nil
  | .succ count' => n :: (repeatN n count')

def length (l : NatList) : Nat :=
  match l with
  | [] => 0
  | _ :: t => 1 + length t

def app (l1 l2 : NatList) : NatList :=
  match l1 with
  | [] => l2
  | h :: t => h :: (app t l2)

infixr:60 " ++ " => app

example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] := rfl
example : [] ++ [4, 5] = [4, 5] := rfl
example : [1, 2, 3] ++ [] = [1, 2, 3] := rfl

def hd (default : Nat) (l : NatList) : Nat :=
  match l with
  | [] => default
  | h :: _ => h

def tl (l : NatList) : NatList :=
  match l with
  | [] => []
  | _ :: t => t

example : hd 0 [1, 2, 3] = 1 := rfl
example : hd 0 [] = 0 := rfl
example : tl [1, 2, 3] = [2, 3] := rfl

-- ### Exercise: 2 stars, standard, especially useful (list_funs)
def nonzeros (l : NatList) : NatList :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3] := by
  /- FILL IN HERE -/ sorry

def oddmembers (l : NatList) : NatList :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3] := by
  /- FILL IN HERE -/ sorry

def countoddmembers (l : NatList) : Nat :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : countoddmembers [1, 0, 3, 1, 4, 5] = 4 := by
  /- FILL IN HERE -/ sorry

example : countoddmembers [0, 2, 4] = 0 := by
  /- FILL IN HERE -/ sorry

example : countoddmembers [] = 0 := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 3 stars, advanced (alternate)
def alternate (l1 l2 : NatList) : NatList :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6] := by
  /- FILL IN HERE -/ sorry

example : alternate [1] [4, 5, 6] = [1, 4, 5, 6] := by
  /- FILL IN HERE -/ sorry

example : alternate [1, 2, 3] [4] = [1, 4, 2, 3] := by
  /- FILL IN HERE -/ sorry

example : alternate [] [20, 30] = [20, 30] := by
  /- FILL IN HERE -/ sorry

-- ## Bags via Lists
def Bag := NatList

-- ### Exercise: 3 stars, standard, especially useful (bag_functions)
def count (v : Nat) (s : Bag) : Nat :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : count 1 [1, 2, 3, 1, 4, 1] = 3 := by
  /- FILL IN HERE -/ sorry

example : count 6 [1, 2, 3, 1, 4, 1] = 0 := by
  /- FILL IN HERE -/ sorry

def sum: Bag → Bag → Bag :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3 := by
  /- FILL IN HERE -/ sorry

def add (v : Nat) (s : Bag) : Bag :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : count 1 (add 1 [1, 4, 1]) = 3 := by
  /- FILL IN HERE -/ sorry

example : count 5 (add 1 [1, 4, 1]) = 0 := by
  /- FILL IN HERE -/ sorry

def member (v : Nat) (s : Bag) : Bool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : member 1 [1, 4, 1] = true := by
  /- FILL IN HERE -/ sorry

example : member 2 [1, 4, 1] = false := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 3 stars, standard, optional (bag_more_functions)
def remove_one (v : Nat) (s : Bag) : Bag :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : count 5 (remove_one 5 [2, 1, 5, 4, 1]) = 0 := by
  /- FILL IN HERE -/ sorry

example : count 5 (remove_one 5 [2, 1, 4, 1]) = 0 := by
  /- FILL IN HERE -/ sorry

example : count 4 (remove_one 5 [2, 1, 4, 5, 1, 4]) = 2 := by
  /- FILL IN HERE -/ sorry

example : count 5 (remove_one 5 [2, 1, 5, 4, 5, 1, 4]) = 1 := by
  /- FILL IN HERE -/ sorry

def remove_all (v : Nat) (s : Bag) : Bag :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : count 5 (remove_all 5 [2, 1, 5, 4, 1]) = 0 := by
  /- FILL IN HERE -/ sorry

example : count 5 (remove_all 5 [2, 1, 4, 1]) = 0 := by
  /- FILL IN HERE -/ sorry

example : count 4 (remove_all 5 [2, 1, 4, 5, 1, 4]) = 2 := by
  /- FILL IN HERE -/ sorry

example : count 5 (remove_all 5 [2, 1, 5, 4, 5, 1, 4, 5, 1, 4]) = 0 := by
  /- FILL IN HERE -/ sorry

def included (s1 : Bag) (s2 : Bag) : Bool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : included [1, 2] [2, 1, 4, 1] = true := by
  /- FILL IN HERE -/ sorry

example : included [1, 2, 2] [2, 1, 4, 1] = false := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 2 stars, standard, especially useful (add_inc_count)
-- NOTE: Adding a value to a bag should increase the value's count by one.
-- State this as a theorem and prove it in Lean.

-- theorem add_inc_count : ...

-- # Reasoning About Lists
-- TODO

-- # Options
-- TODO

end NatList
-- # Partial Maps
-- TODO
