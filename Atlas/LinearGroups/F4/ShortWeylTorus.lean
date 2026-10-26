import Atlas.LinearGroups.F4.ShortWeyl
import Atlas.LinearGroups.F4.TorusNorm

noncomputable section
namespace Atlas.F4

def albertWeightCoefficients : Atlas.Albert.Coordinate → RootData.Vector :=
  Sum.elim (fun _ => 0) (fun p => RootData.simpleCoefficients (Weights.slotRoot p))

/-- Images of the four simple roots under each axial reflection, in simple-root coordinates. -/
def axialReflectionCoefficients : Fin 4 → Fin 4 → RootData.Vector :=
  ![![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![-1,-2,-3,-1]],
    ![![-1,-2,-2,0], ![0,1,0,0], ![0,0,1,0], ![1,1,1,1]],
    ![![1,2,2,0], ![0,-1,-2,0], ![0,0,1,0], ![0,1,1,1]],
    ![![1,0,0,0], ![0,1,2,0], ![0,0,-1,0], ![0,0,1,1]]]

theorem shortWeyl_coefficients : ∀ (i : Fin 8) (j : Fin 27),
    (∑ k : Fin 4, albertWeightCoefficients
      (albertCoordinateOfFin (shortWeylDestination i j)) k •
        axialReflectionCoefficients (shortWeylAxis i) k) =
          albertWeightCoefficients (albertCoordinateOfFin j) := by decide +kernel

section Characters
variable {F : Type*} [CommRing F]

theorem weightCharacter_zero (t : TorusParameters F) : weightCharacter 0 t = 1 := by
  simp [weightCharacter]

theorem weightCharacter_add (u v : RootData.Vector) (t : TorusParameters F) :
    weightCharacter (u+v) t = weightCharacter u t * weightCharacter v t := by
  simp [weightCharacter, zpow_add, Finset.prod_mul_distrib]

theorem weightCharacter_zsmul (n : ℤ) (v : RootData.Vector) (t : TorusParameters F) :
    weightCharacter (n • v) t = weightCharacter v t ^ n := by
  change (∏ j : Fin 4, t j ^ ((n • v) j)) = (∏ j : Fin 4, t j ^ v j) ^ n
  simp only [Pi.smul_apply, zsmul_eq_mul]
  rw [← Finset.prod_zpow]
  apply Finset.prod_congr rfl
  intro j _
  rw [← zpow_mul, mul_comm]
  simp

theorem weightCharacter_sum (v : Fin 4 → RootData.Vector) (t : TorusParameters F) :
    weightCharacter (∑ j : Fin 4, v j) t = ∏ j : Fin 4, weightCharacter (v j) t := by
  have h : ∀ s : Finset (Fin 4), weightCharacter (∑ j ∈ s, v j) t =
      ∏ j ∈ s, weightCharacter (v j) t := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [weightCharacter_zero]
    | @insert a s ha ih => simp [ha, weightCharacter_add, ih]
  exact h Finset.univ

def shortWeylTorusParameters (i : Fin 8) (t : TorusParameters F) : TorusParameters F :=
  fun k => weightCharacter (axialReflectionCoefficients (shortWeylAxis i) k) t

theorem weightCharacter_reflection (i : Fin 8) (t : TorusParameters F) (v : RootData.Vector) :
    weightCharacter v (shortWeylTorusParameters i t) =
      weightCharacter (∑ k : Fin 4, v k • axialReflectionCoefficients (shortWeylAxis i) k) t := by
  rw [weightCharacter_sum]
  simp only [weightCharacter_zsmul]
  rfl

theorem shortWeyl_character (i : Fin 8) (t : TorusParameters F) (j : Fin 27) :
    weightCharacter (albertWeightCoefficients (albertCoordinateOfFin
      (shortWeylDestination i j))) (shortWeylTorusParameters i t) =
        weightCharacter (albertWeightCoefficients (albertCoordinateOfFin j)) t := by
  rw [weightCharacter_reflection, shortWeyl_coefficients]

theorem torusEquiv_basis (t : TorusParameters F) (c : Atlas.Albert.Coordinate) :
    torusEquiv t (Atlas.Albert.basisVector c) =
      (weightCharacter (albertWeightCoefficients c) t : F) • Atlas.Albert.basisVector c := by
  cases c with
  | inl i =>
    apply Prod.ext
    · funext j
      simp [torusEquiv, torusApply, Atlas.Albert.basisVector, Pi.single_apply, albertWeightCoefficients,
        weightCharacter_zero]
    · funext j k
      simp [torusEquiv, torusApply, Atlas.Albert.basisVector, Pi.single_apply, albertWeightCoefficients,
        weightCharacter_zero]
  | inr p =>
    rcases p with ⟨i,j⟩
    apply Prod.ext
    · funext k
      simp [torusEquiv, torusApply, Atlas.Albert.basisVector, Pi.single_apply]
    · funext k l
      by_cases hk : k = i <;> by_cases hl : l = j <;>
        simp [torusEquiv, torusApply, Atlas.Albert.basisVector, Pi.single_apply,
          albertWeightCoefficients, torusScale, hk, hl]

end Characters

variable {F : Type*} [Field F]

theorem shortWeyl_torus_commute (i : Fin 8) (t : TorusParameters F) :
    shortWeylFirstPair i * diagonalTorus t =
      diagonalTorus (shortWeylTorusParameters i t) * shortWeylFirstPair i := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply Atlas.Albert.linearMap_ext_basis
  intro c
  obtain ⟨j,hj⟩ := albertCoordinateFinEquiv.symm.surjective c
  change albertCoordinateOfFin j = c at hj
  rw [← hj]
  change (shortWeylFirstPair i).val (torusEquiv t
    (Atlas.Albert.basisVector (albertCoordinateOfFin j))) =
    torusEquiv (shortWeylTorusParameters i t) ((shortWeylFirstPair i).val
      (Atlas.Albert.basisVector (albertCoordinateOfFin j)))
  rw [torusEquiv_basis, map_smul, shortWeylFirstPair_basis, map_smul, torusEquiv_basis,
    shortWeyl_character, smul_smul, smul_smul, mul_comm]

theorem shortWeyl_torus_conjugate (i : Fin 8) (t : TorusParameters F) :
    shortWeylFirstPair i * diagonalTorus t * (shortWeylFirstPair i)⁻¹ =
      diagonalTorus (shortWeylTorusParameters i t) := by
  rw [shortWeyl_torus_commute]
  simp [mul_assoc]

end Atlas.F4
