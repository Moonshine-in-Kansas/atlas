import Atlas.LinearGroups.Triality.ParabolicFlags
import Atlas.LinearGroups.Triality.WeylDistinct

/-! The concrete Borel has invertible diagonal and is upper triangular in the
 ordered hyperbolic basis e₀,e₁,e₂,e₃,f₃,f₂,f₁,f₀. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal

def coordinateHeight : Index 4 → ℕ := Sum.elim (fun i => i.val) (fun i => 7-i.val)

theorem coordinateWord_injective (w : Fin 12) :
    Function.Injective (coordinateWord (weylWord w)) := by
  revert w
  decide

theorem coordinateWord_height_separates : ∀ w v : Fin 12, w ≠ v →
    ∃ i : Index 4, coordinateHeight (coordinateWord (weylWord w) i) <
      coordinateHeight (coordinateWord (weylWord v) i) := by decide

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

set_option maxHeartbeats 2000000 in
theorem positiveMatrix_diagonal (p : PositiveParameters F K) (i : Index 4) :
    (positiveMatrix F K p).val (Pi.single i 1) i = 1 := by
  change (positiveWord F K p.a p.b p.c p.d p.u p.v).val _ _ = _
  rw [positiveWord_apply]
  rcases i with i|i <;> fin_cases i <;> simp [positiveAction, Pi.single_apply]

set_option maxHeartbeats 4000000 in
theorem positiveMatrix_below (p : PositiveParameters F K) (i j : Index 4)
    (h : coordinateHeight j < coordinateHeight i) :
    (positiveMatrix F K p).val (Pi.single j 1) i = 0 := by
  change (positiveWord F K p.a p.b p.c p.d p.u p.v).val _ _ = _
  rw [positiveWord_apply]
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp_all [positiveAction, Pi.single_apply, coordinateHeight]

theorem torus_single (h : Kˣ × Fˣ) (i : Index 4) :
    (torusMap F K h).val (Pi.single i 1) =
      (torusCoordinateUnit F K h i : K) • Pi.single i 1 := by
  ext j
  rw [torus_row]
  by_cases hj : j=i
  · subst j; simp
  · simp [Pi.single_apply, hj, Ne.symm hj]

theorem borel_diagonal_ne_zero (hdeg : Module.finrank F K = 3)
    (b : borel F K hdeg) (i : Index 4) : b.val.val (Pi.single i 1) i ≠ 0 := by
  obtain ⟨⟨p,h⟩,hp⟩ := b.property
  change positiveMatrix F K p * torusMap F K h = b.val at hp
  rw [← hp]
  change (positiveMatrix F K p).val ((torusMap F K h).val (Pi.single i 1)) i ≠ 0
  rw [torus_single, map_smul]
  simp [positiveMatrix_diagonal]

theorem borel_below (hdeg : Module.finrank F K = 3)
    (b : borel F K hdeg) (i j : Index 4) (hij : coordinateHeight j < coordinateHeight i) :
    b.val.val (Pi.single j 1) i = 0 := by
  obtain ⟨⟨p,h⟩,hp⟩ := b.property
  change positiveMatrix F K p * torusMap F K h = b.val at hp
  rw [← hp]
  change (positiveMatrix F K p).val ((torusMap F K h).val (Pi.single j 1)) i = 0
  rw [torus_single, map_smul]
  simp [positiveMatrix_below F K p i j hij]

theorem weylLift_single (w : Fin 12) (i : Index 4) :
    ∃ u : Kˣ, (weylLift F K w).val (Pi.single (coordinateWord (weylWord w) i) 1) =
      (u : K) • Pi.single i 1 := by
  obtain ⟨u,hu⟩ := weylWord_row F K (weylWord w) i
  refine ⟨u,?_⟩
  ext j
  obtain ⟨v,hv⟩ := weylWord_row F K (weylWord w) j
  by_cases hj : j=i
  · subst j
    change (weylLift F K w).val _ _ = _
    rw [show (weylLift F K w).val _ i = _ from hu _]
    simp
  · have hji := (coordinateWord_injective w).ne hj
    change (weylLift F K w).val _ j = _
    rw [show (weylLift F K w).val _ j = _ from hv _]
    simp [Pi.single_apply, hj, Ne.symm hj, hji, Ne.symm hji]

end Atlas.Triality
