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
theorem nil_app : ∀ l : NatList, [] ++ l = l := by
  intro l
  rfl

theorem tl_length_pred : ∀ l : NatList, Nat.pred (length l) = length (tl l) := by
  intro l
  cases l with
  | nil => rfl
  | cons h t => simp [length, tl]

theorem app_assoc : ∀ l1 l2 l3 : NatList, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  intros l1 l2 l3
  induction l1 with
  | nil => rfl
  | cons h t ih => simp [app] <;> rewrite [ih] <;> rfl

theorem repeat_double_firsttry : ∀ c n : Nat, repeatN n c ++ repeatN n c = repeatN n (c + c) := by
  intros c
  induction c with
  | zero => intro n <;> rfl
  | succ c' ih =>
    intro n
    -- simp: seems to do nothing!
    sorry

theorem repeat_plus : ∀ c1 c2 n : Nat, repeatN n c1 ++ repeatN n c2 = repeatN n (c1 + c2) := by
  intros c1 c2 n
  induction c1 with
  | zero => simp <;> rfl
  | succ c1' ih =>
    simp [repeatN, app]
    rewrite [ih, <- repeatN]
    simp [Nat.succ_add]

def rev (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => rev t ++ [h]

example : rev [1, 2, 3] = [3, 2, 1] := rfl
example : rev [] = [] := rfl

theorem rev_length_firsttry : ∀ l : NatList, length (rev l) = length l := by
  intro l
  induction l with
  | nil => rfl
  | cons h t ih =>
    -- simp: seems to do nothing!
    sorry

theorem app_rev_length_succ_firsttry : ∀ l n, length (rev l ++ [n]) = Nat.succ (length l) := by
  intro l
  induction l with
  | nil => intro n <;> rfl
  | cons h t ih =>
    intro n
    -- simp: seems to do nothing!
    sorry

theorem app_length_succ : ∀ l n, length (l ++ [n]) = Nat.succ (length l) := by
  intro l
  induction l with
  | nil => intro n <;> rfl
  | cons h t ih => intro n <;> simp [app, length] <;> rewrite [ih] <;> rfl

theorem rev_length : ∀ l : NatList, length (rev l) = length l := by
  intro l
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp [rev, length]
    rewrite [app_length_succ, ih]
    simp [Nat.one_add]

theorem app_length : ∀ l1 l2 : NatList, length (l1 ++ l2) = length l1 + length l2 := by
  intros l1 l2
  induction l1 with
  | nil => simp [app, length]
  | cons h t ih =>
    simp [app, length]
    rewrite [ih]
    simp [Nat.succ_add]

-- NOTE: Lean does not have an exact equivalent of Coq’s `search`

-- ## List Exercises, Part 1
-- ### Exercise: 3 stars, standard (list_exercises)
theorem app_nil_r : ∀ l : NatList, l ++ [] = l := by
  /- FILL IN HERE -/ sorry

theorem rev_app_distr : ∀ l1 l2 : NatList, rev (l1 ++ l2) = rev l2 ++ rev l1 := by
  /- FILL IN HERE -/ sorry

theorem rev_involutive : ∀ l : NatList, rev (rev l) = l := by
  /- FILL IN HERE -/ sorry

theorem app_assoc4:
  ∀ l1 l2 l3 l4 : NatList,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4
:= by
  /- FILL IN HERE -/ sorry

theorem nonzeros_app :
  ∀ l1 l2 : NatList,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2)
:= by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 2 stars, standard (eqblist)
def eqblist (l1 l2 : NatList) : Bool :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : eqblist [] [] = true := by
  /- FILL IN HERE -/ sorry

example : eqblist [1, 2, 3] [1, 2, 3] = true := by
  /- FILL IN HERE -/ sorry

example : eqblist [1, 2, 3] [1, 2, 4] = false := by
  /- FILL IN HERE -/ sorry

theorem eqblist_refl : ∀ l : NatList, true = eqblist l l := by
  /- FILL IN HERE -/ sorry

-- ## List Exercises, Part 2
-- ### Exercise: 1 star, standard (count_member_nonzero)
theorem count_member_nonzero : ∀ (s : Bag), (1 <=? (count 1 (1 :: s))) = true := by
  /- FILL IN HERE -/ sorry

theorem leb_n_succ : ∀ n, (n <=? Nat.succ n) = true := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [leb] <;> rewrite [ih] <;> rfl

-- ### Exercise: 3 stars, advanced (remove_does_not_increase_count)
theorem remove_does_not_increase_count :
  ∀ (s : Bag),
  ((count 0 (remove_one 0 s)) <=? (count 0 s)) = true := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 3 stars, standard, optional (bag_count_sum)
-- theorem bag_count_sum : ...

-- ### Exercise: 3 stars, advanced (involution_injective)
theorem involution_injective :
  ∀ (f : Nat → Nat),
  (∀ n : Nat, n = f (f n)) → (∀ n1 n2 : Nat, f n1 = f n2 → n1 = n2)
:= by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 2 stars, advanced (rev_injective)
theorem rev_injective : ∀ (l1 l2 : NatList), rev l1 = rev l2 → l1 = l2 := by
  /- FILL IN HERE -/ sorry

-- # Options
def nth_bad (l: NatList) (n: Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' =>
    match n with
    | .zero => a
    | .succ n' => nth_bad l' n'

inductive NatOption : Type where
  | Some (n : Nat)
  | None

def nth_error (l: NatList) (n: Nat) : NatOption :=
  match l with
  | [] => .None
  | a :: l' =>
    match n with
    | .zero => .Some a
    | .succ n' => nth_error l' n'

example : nth_error [4, 5, 6, 7] 0 = .Some 4 := rfl
example : nth_error [4, 5, 6, 7] 3 = .Some 7 := rfl
example : nth_error [4, 5, 6, 7] 9 = .None := rfl

def option_elim (d: Nat) (o: NatOption) : Nat :=
  match o with
  | .Some n' => n'
  | .None => d

-- ### Exercise: 2 stars, standard (hd_error)
def hd_error (l : NatList) : NatOption :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : hd_error [] = .None := by
  /- FILL IN HERE -/ sorry

example : hd_error [1] = .Some 1 := by
  /- FILL IN HERE -/ sorry

example : hd_error [5, 6] = .Some 5 := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 1 star, standard, optional (option_elim_hd)
theorem option_elim_hd :
  ∀ (l: NatList) (default: Nat),
  hd default l = option_elim default (hd_error l)
:= by
  /- FILL IN HERE -/ sorry

end NatList

-- # Partial Maps
-- As `id` is already defined in Lean, we use `MyId` instead.
inductive MyId : Type where
  | Id (n : Nat)

def eqb_id (x1 x2 : MyId) :=
  match x1, x2 with
  | .Id n1, .Id n2 => n1 =? n2

-- ### Exercise: 1 star, standard (eqb_id_refl)
theorem eqb_id_refl : ∀ x, eqb_id x x = true := by
  /- FILL IN HERE -/ sorry

namespace PartialMap
export NatList (NatOption)

inductive partial_map : Type where
  | empty
  | record (i : MyId) (v : Nat) (m : partial_map)

def update (d : partial_map) (x : MyId) (value : Nat) : partial_map :=
  .record x value d

def find (x : MyId) (d : partial_map) : NatOption :=
  match d with
  | .empty => .None
  | .record y v d' =>
    if eqb_id x y then .Some v else find x d'

-- ### Exercise: 1 star, standard (update_eq)
theorem update_eq :
  ∀ (d : partial_map) (x : MyId) (v : Nat),
  find x (update d x v) = .Some v
:= by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 1 star, standard (update_neq)
theorem update_neq :
  ∀ (d : partial_map) (x y : MyId) (o : Nat),
  eqb_id x y = false → find x (update d y o) = find x d
:= by
  /- FILL IN HERE -/ sorry

end PartialMap
