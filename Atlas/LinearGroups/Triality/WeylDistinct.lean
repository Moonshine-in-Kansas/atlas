import Atlas.LinearGroups.Triality.WeylTorus

/-! Distinct right torus cosets of the twelve literal Weyl words, proved from
coordinate supports, including characteristic two where signs disappear. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal

def coordinateReflection (s : Bool) : Index 4 → Index 4 :=
  if s then Sum.elim ![.inl 1, .inl 0, .inr 2, .inr 3]
    ![.inr 1, .inr 0, .inl 2, .inl 3]
  else Sum.elim ![.inl 0, .inl 2, .inl 1, .inl 3]
    ![.inr 0, .inr 2, .inr 1, .inr 3]

def coordinateWord : List Bool → Index 4 → Index 4
  | [], i => i
  | s::w, i => coordinateWord w (coordinateReflection s i)

theorem coordinateWord_distinct :
    Function.Injective (fun w : Fin 12 =>
      (coordinateWord (weylWord w) (.inl 0), coordinateWord (weylWord w) (.inl 1))) := by
  decide

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem weylGenerator_row (s : Bool) (i : Index 4) :
    ∃ u : Kˣ, ∀ x : VectorD 4 K,
      (if s then shortWeyl F K else longWeyl F K).val x i =
        (u : K) * x (coordinateReflection s i) := by
  refine ⟨(if s then Sum.elim ![1,-1,-1,-1] ![1,-1,-1,-1]
    else Sum.elim ![1,1,-1,1] ![1,1,-1,1]) i, ?_⟩
  intro x
  cases s <;> rcases i with i|i <;> fin_cases i <;>
    simp [coordinateReflection, shortWeyl_apply, longWeyl_apply]

theorem weylWord_row (w : List Bool) (i : Index 4) :
    ∃ u : Kˣ, ∀ x : VectorD 4 K,
      ((w.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod).val x i =
        (u : K) * x (coordinateWord w i) := by
  induction w generalizing i with
  | nil => exact ⟨1, by intro x; simp [coordinateWord]⟩
  | cons s w ih =>
    obtain ⟨u, hu⟩ := weylGenerator_row F K s i
    obtain ⟨v, hv⟩ := ih (coordinateReflection s i)
    refine ⟨u*v, ?_⟩
    intro x
    simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [hu, hv]
    simp [coordinateWord, mul_assoc]

def torusCoordinateUnit (h : Kˣ × Fˣ) : Index 4 → Kˣ :=
  Sum.elim (torusWeights F K h) (fun i => (torusWeights F K h i)⁻¹)

theorem torus_row (h : Kˣ × Fˣ) (x : VectorD 4 K) (i : Index 4) :
    (torusMap F K h).val x i = (torusCoordinateUnit F K h i : K)*x i := by
  cases i <;> simp [torusMap, diagonalEmbedding, diagonalLinear, torusCoordinateUnit]

theorem weylLift_torus_row (w : Fin 12) (h : Kˣ × Fˣ) (i : Index 4) :
    ∃ u : Kˣ, ∀ x : VectorD 4 K,
      (weylLift F K w * torusMap F K h).val x i =
        (u : K)*x (coordinateWord (weylWord w) i) := by
  obtain ⟨u, hu⟩ := weylWord_row F K (weylWord w) i
  refine ⟨u * torusCoordinateUnit F K h (coordinateWord (weylWord w) i), ?_⟩
  intro x
  change (weylLift F K w).val ((torusMap F K h).val x) i = _
  simp only [weylLift]
  rw [hu, torus_row]
  simp [mul_assoc]

theorem weylLift_torus_disjoint (w v : Fin 12) (h k : Kˣ × Fˣ)
    (he : weylLift F K w * torusMap F K h = weylLift F K v * torusMap F K k) : w = v := by
  have hp : ∀ i : Index 4, coordinateWord (weylWord w) i = coordinateWord (weylWord v) i := by
    intro i
    by_contra hne
    obtain ⟨a, ha⟩ := weylLift_torus_row F K w h i
    obtain ⟨b, hb⟩ := weylLift_torus_row F K v k i
    have hh := congrArg (fun g : O_DPlus 4 K =>
      g.val (Pi.single (coordinateWord (weylWord w) i) 1) i) he
    rw [ha, hb] at hh
    simp [Pi.single_apply, hne, Ne.symm hne] at hh
  exact coordinateWord_distinct (Prod.ext (hp (.inl 0)) (hp (.inl 1)))

end Atlas.Triality
