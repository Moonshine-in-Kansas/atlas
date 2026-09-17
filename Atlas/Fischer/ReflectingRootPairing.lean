import Atlas.Fischer.ReflectingRootPairingExpansion
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

noncomputable section
namespace Atlas.Fischer

/-- Distinct normalized cubic-root rays are linearly independent. Proportionality
is ruled out using the actual root equations, not a chosen root family. -/
theorem roots_distinct_phases_linearIndependent (r s : Coordinates)
    (hr : IsRoot r) (hs : IsRoot s)
    (hd : ¬ ∃ a : Scalar, a^3=1 ∧ s=a • r) :
    LinearIndependent Scalar ![s,r] := by
  rw [linearIndependent_fin2]
  constructor
  · exact root_ne_zero hr
  · intro a ha
    change a • r=s at ha
    apply hd
    refine ⟨a,?_,ha.symm⟩
    apply (root_scalar_iff r hr a).mp
    simpa only [ha] using hs

/-- The Hermitian pairing of independently defined reflecting roots on distinct
normalized rays has conjugate equal to its square. -/
theorem reflectingRoot_pairing_square (r s : Coordinates)
    (hr : IsReflectingRoot r) (hs : IsReflectingRoot s)
    (hd : ¬ ∃ a : Scalar, a^3=1 ∧ s=a • r) :
    hermitian r s^2 = star (hermitian r s) := by
  have hli := roots_distinct_phases_linearIndependent r s hr.1 hs.1 hd
  have hp := reflectingRoot_pairing_polynomial r s hr hs
  have he := (Fintype.linearIndependent_iff.mp hli)
    ![star (hermitian r s) - hermitian r s^2,
      star (hermitian r s)^2 - hermitian r s]
    (by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, add_comm] using hp) 0
  change star (hermitian r s) - hermitian r s^2 = 0 at he
  exact (sub_eq_zero.mp he).symm

/-- Intrinsic reflecting-root pairing: distinct normalized rays have pairing
zero or a cube root of unity, without any displayed-family hypothesis. -/
theorem reflectingRoot_pairing_zero_or_cube (r s : Coordinates)
    (hr : IsReflectingRoot r) (hs : IsReflectingRoot s)
    (hd : ¬ ∃ a : Scalar, a^3=1 ∧ s=a • r) :
    hermitian r s=0 ∨ hermitian r s^3=1 := by
  have hc := reflectingRoot_pairing_square r s hr hs hd
  have hb := congrArg star hc
  simp only [star_pow,star_star] at hb
  by_cases hz : hermitian r s=0
  · exact Or.inl hz
  · right
    have he : hermitian r s * (hermitian r s^3-1)=0 := by
      linear_combination (hermitian r s^2 + star (hermitian r s))*hc + hb
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hz)

/-- The same intrinsic pairing theorem stated with the actual subgroup Mu3. -/
theorem reflectingRoot_pairing_zero_or_mu3 (r s : Coordinates)
    (hr : IsReflectingRoot r) (hs : IsReflectingRoot s)
    (hd : ¬ ∃ a : Mu3, s=(a.val.val : Scalar) • r) :
    hermitian r s=0 ∨ ∃ a : Mu3, hermitian r s=(a.val.val : Scalar) := by
  have hdC : ¬ ∃ a : Scalar, a^3=1 ∧ s=a • r := by
    rintro ⟨a,ha,h⟩
    exact hd ⟨rootsOfUnity.mkOfPowEq a ha,h⟩
  rcases reflectingRoot_pairing_zero_or_cube r s hr hs hdC with h | h
  · exact Or.inl h
  · exact Or.inr ⟨rootsOfUnity.mkOfPowEq (hermitian r s) h,rfl⟩

end Atlas.Fischer
