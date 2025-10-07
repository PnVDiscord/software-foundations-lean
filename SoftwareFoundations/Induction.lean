-- Induction: Proof by Induction
--
-- https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html

-- # Seperate Compilation
import SoftwareFoundations.Basics

-- # Proof by Induction
theorem add_zero_r_firsttry : ∀ n : Nat, n + 0 = n := by
  intro n
  -- simp: does nothing!
  sorry

theorem add_zero_r_secondtry : ∀ n : Nat, n + 0 = n := by
  intro n
  match n with
  | .zero => rfl
  | .succ n' =>
    -- simp: does nothing!
    sorry -- We get stuck here

theorem add_zero_r : ∀ n : Nat, n + 0 = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => simp <;> rewrite [ih] <;> rfl

theorem sub_self : ∀ n : Nat, n - n = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih => simp <;> rewrite [ih] <;> rfl

-- ### Exercise: 2 stars, standard, especially useful (basic_induction)
theorem mul_zero_r : ∀ n : Nat, n * 0 = 0 := by
  /- FILL IN HERE -/ sorry

theorem add_succ : ∀ n m : Nat, Nat.succ (n + m) = n + Nat.succ m := by
  /- FILL IN HERE -/ sorry

theorem add_comm : ∀ n m : Nat, n + m = m + n := by
  /- FILL IN HERE -/ sorry

theorem add_assoc : ∀ n m p : Nat, n + (m + p) = (n + m) + p := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 2 stars, standard (double_plus)
def double (n : Nat) : Nat :=
  match n with
  | .zero => 0
  | .succ n' => .succ (.succ (double n'))

theorem double_plus : ∀ n : Nat, double n = n + n := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 2 stars, standard (eqb_refl)
theorem eqb_refl : ∀ n : Nat, (n =? n) = true := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 2 stars, standard, optional (even_S)
theorem even_succ : ∀ n : Nat, even (.succ n) = not (even n) := by
  /- FILL IN HERE -/ sorry

-- # Proofs Within Proofs
-- In Lean, we use `have` to achieve similar effect to Coq's `assert`.
theorem mul_zero_plus' : ∀ n m : Nat, (n + 0 + 0) * m = n * m := by
  intro n m
  have h : n + 0 + 0 = n := by
    rewrite [add_comm] <;> simp <;> rewrite [add_comm] <;> rfl
  rewrite [h]
  rfl

theorem plus_rearrange_firsttry :
  ∀ n m p q : Nat,
  (n + m) + (p + q) = (m + n) + (p + q)
:= by
  intro n m p q
  rewrite [add_comm] -- Lean rewrites the wrong plus!
  sorry

theorem plus_rearrange :
  ∀ n m p q : Nat,
  (n + m) + (p + q) = (m + n) + (p + q)
:= by
  intro n m p q
  have h : n + m = m + n := by
    rewrite [add_comm] <;> rfl
  rewrite [h]
  rfl

-- # Formal vs. Informal Proofs
-- NOTE: We'll skip `Exercise: 2 stars, advanced, especially useful (add_comm_informal)`
-- and `Exercise: 2 stars, standard, optional (eqb_refl_informal)` as they are
-- about writing informal proofs.

-- # More Exercises

-- ### Exercise: 3 stars, standard, especially useful (mul_comm)
theorem add_shuffle3 : ∀ n m p : Nat, n + (m + p) = m + (n + p) := by
  /- FILL IN HERE -/ sorry

theorem mul_comm : ∀ m n : Nat, m * n = n * m := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 3 stars, standard, optional (more_exercises)
theorem leb_refl : ∀ n : Nat, (n <=? n) = MyBool.true := by
  /- FILL IN HERE -/ sorry

theorem zero_neq_succ : ∀ n : Nat, (0 =? .succ n) = MyBool.false := by
  /- FILL IN HERE -/ sorry

theorem andb_false_r : ∀ b : MyBool, b my&& .false = .false := by
  /- FILL IN HERE -/ sorry

theorem succ_neqb_zero : ∀ n : Nat, (.succ n =? 0) = MyBool.false := by
  /- FILL IN HERE -/ sorry

theorem one_mul : ∀ n : Nat, 1 * n = n := by
  /- FILL IN HERE -/ sorry

theorem all3_spec : ∀ b c : MyBool,
  orb (andb b c) (orb (negb b) (negb c)) = .true
:= by
  /- FILL IN HERE -/ sorry

theorem mul_plus_distr_r : ∀ n m p : Nat, (n + m) * p = (n * p) + (m * p) := by
  /- FILL IN HERE -/ sorry

theorem mul_assoc : ∀ n m p : Nat, (n * m) * p = n * (m * p) := by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 2 stars, standard, optional (add_shuffle3')
theorem add_shuffle3' : ∀ n m p : Nat, n + (m + p) = m + (n + p) := by
  /- FILL IN HERE -/ sorry

-- # Nat to Bin and Back to Nat

-- ### Exercise: 3 stars, standard, especially useful (binary_commute)
theorem bin_to_nat_pres_incr : ∀ b : Bin,
  bin_to_nat (incr b) = 1 + (bin_to_nat b)
:= by
  /- FILL IN HERE -/ sorry

-- ### Exercise: 3 stars, standard (nat_bin_nat)
def nat_to_bin (n : Nat) : Bin := by
  /- FILL IN HERE -/ sorry

theorem nat_bin_nat : ∀ n : Nat, bin_to_nat (nat_to_bin n) = n := by
  /- FILL IN HERE -/ sorry

-- # Bin to Nat and Back to Bin (Advanced)
theorem bin_nat_bin_fails : ∀ b, nat_to_bin (bin_to_nat b) = b := by
  sorry -- does not hold

-- ### Exercise: 2 stars, advanced (double_bin)
theorem double_incr : ∀ n : Nat, double (.succ n) = .succ (.succ (double n)) := by
  /- FILL IN HERE -/ sorry

def double_bin (b : Bin) : Bin :=
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

example : double_bin z = z := by
  /- FILL IN HERE -/ sorry

theorem double_incr_bin :
  ∀ b : Bin,
  double_bin (incr b) = incr (incr (double_bin b))
:= by
  /- FILL IN HERE -/ sorry

-- NOTE: Explain why failure of `bin_nat_bin_fails` occurs. Your explanation
-- will not be graded, but it's important that you get it clear in your mind.

-- NOTE: To solve that problem, we can introduce a normalization function that
-- selects the simplest bin out of all the equivalent bin. Then we can prove
-- that the conversion from bin to nat and back again produces that normalized,
-- simplest bin.
-- ### Exercise: 4 stars, advanced (bin_nat_bin)
def normalize (b : Bin) : Bin := by
  /- REPLACE THIS LINE WITH YOUR DEFINITION -/ sorry

theorem bin_nat_bin : ∀ b : Bin, nat_to_bin (bin_to_nat b) = normalize b := by
  /- FILL IN HERE -/ sorry
