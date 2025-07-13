-- Imp: Simple Imperative Programs
--
-- https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html

-- # Arithmetic and Boolean Expressions

-- ## Syntax
-- TODO

-- ## Evaluation
-- TODO

-- ## Optimization
-- TODO

-- # Coq Automation

-- ## Tacticals
-- TODO

-- ## Defining New Tactics
-- TODO

-- ## The `lia` Tactic
-- TODO

-- ## A Few More Handy Tactics

-- # Evaluation as a Relation
-- TODO

-- ## Inference Rule Notation
-- TODO

-- ## Equivalence of the Definitions
-- TODO

-- ## Computational vs. Relational Definitions
-- TODO

-- # Expressions With Variables

-- ## States
-- TODO

-- ## Syntax
inductive AExp : Type
  | ANum (n : Nat)
  | AId (x : String) -- NEW
  | APlus (a1 a2 : AExp)
  | AMinus (a1 a2 : AExp)
  | AMult (a1 a2 : AExp)

def w : String := "W"
def x : String := "X"
def y : String := "Y"
def z : String := "Z"
