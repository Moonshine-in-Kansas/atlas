import Mathlib.Tactic

/-! Finite relative root data. These checks do not assume or establish a Bruhat
normal form for the matrix group; that remains a separate structural theorem. -/
namespace Atlas.Triality

/-- Coordinates in the ordered simple-root basis (short, long). -/
def positiveRootVector : Fin 6 → ℤ × ℤ :=
  ![(1,0), (0,1), (1,1), (2,1), (3,1), (3,2)]

/-- `true` denotes the short reflection. -/
def rootReflection (s : Bool) (r : ℤ × ℤ) : ℤ × ℤ :=
  if s then (-r.1 + 3*r.2, r.2) else (r.1, r.1-r.2)

def weylWord : Fin 12 → List Bool :=
  ![[], [true], [false], [true,false], [false,true],
    [true,false,true], [false,true,false], [true,false,true,false],
    [false,true,false,true], [true,false,true,false,true],
    [false,true,false,true,false], [true,false,true,false,true,false]]

def rootWordAction (w : List Bool) (r : ℤ × ℤ) : ℤ × ℤ :=
  w.foldr rootReflection r

def rootDimension : Fin 6 → ℕ := ![3,1,3,3,1,1]

def rootInversions (w : Fin 12) : Finset (Fin 6) :=
  Finset.univ.filter fun i =>
    let r := rootWordAction (weylWord w) (positiveRootVector i)
    r.1 ≤ 0 ∧ r.2 ≤ 0

def weightedLength (w : Fin 12) : ℕ :=
  ∑ i ∈ rootInversions w, rootDimension i

theorem rootReflection_involutive (s : Bool) : Function.Involutive (rootReflection s) := by
  intro r
  cases s <;> ext <;> simp [rootReflection] <;> omega

theorem weyl_root_actions_distinct :
    Function.Injective (fun w : Fin 12 =>
      (rootWordAction (weylWord w) (1,0), rootWordAction (weylWord w) (0,1))) := by
  decide

theorem weyl_positive_root_images : ∀ w : Fin 12, ∀ i : Fin 6,
    ∃ j : Fin 6, rootWordAction (weylWord w) (positiveRootVector i) = positiveRootVector j ∨
      rootWordAction (weylWord w) (positiveRootVector i) = -positiveRootVector j := by
  decide

theorem weyl_root_actions_closed : ∀ s : Bool, ∀ w : Fin 12, ∃ v : Fin 12,
    rootWordAction (s :: weylWord w) (1,0) = rootWordAction (weylWord v) (1,0) ∧
    rootWordAction (s :: weylWord w) (0,1) = rootWordAction (weylWord v) (0,1) := by
  decide

theorem weightedLength_table :
    weightedLength = ![0,3,1,4,4,7,5,8,8,11,9,12] := by
  decide

theorem weyl_weighted_sum (q : ℕ) :
    ∑ w : Fin 12, q ^ weightedLength w = (q+1)*(q^3+1)*(q^8+q^4+1) := by
  rw [weightedLength_table]
  simp [Fin.sum_univ_succ]
  ring

end Atlas.Triality
