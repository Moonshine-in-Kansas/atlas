import Atlas.Rudvalis.SecondFrame

namespace Atlas.Rudvalis
open scoped BigOperators

theorem rationalDot_finset_sum_smul {ι : Type*} (s : Finset ι) (a : ι→ℚ)
    (v : ι→RationalSpace) (w : RationalSpace) :
    rationalDot (∑ i∈s,a i • v i) w=∑ i∈s,a i*rationalDot (v i) w := by
  simp only [rationalDot,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem secondFrame_linearIndependent : LinearIndependent ℚ secondFrame := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha i hi
  have h := congrArg (fun v : RationalSpace => rationalDot v (secondFrame i)) ha
  rw [rationalDot_finset_sum_smul] at h
  simp only [secondFrame_pairing] at h
  have hz : rationalDot 0 (secondFrame i)=0 := by simp [rationalDot]
  rw [hz] at h
  simp [mul_ite,hi] at h
  linarith

noncomputable def secondFrameBasis : Module.Basis SeedCoordinate ℚ RationalSpace :=
  basisOfLinearIndependentOfCardEqFinrank secondFrame_linearIndependent (by
    simp [RationalSpace,Module.finrank_pi_fintype,SeedCoordinate])

theorem secondFrameBasis_apply (z : SeedCoordinate) : secondFrameBasis z=secondFrame z := by simp [secondFrameBasis]

end Atlas.Rudvalis
