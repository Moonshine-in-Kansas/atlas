import Atlas.Lattices.EisensteinThetaClassResidue
import Atlas.Lattices.EisensteinNormPatterns
import Atlas.Codes.TernaryConstantShifts

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

/-- Dividing an actual norm-six vector by theta gives scalar norm sum nine. -/
theorem eisenstein_six_normalized_norm_sum (x : EisensteinShell 6)
    (u : EisensteinCoordinates) (hu : x.val.val=eisensteinTheta • u) :
    ∑ i,(u i).norm=9 := by
  have he := eisenstein_six_sum_norms x
  rw [hu] at he
  simp only [Pi.smul_apply,smul_eq_mul,map_mul,
    show eisensteinTheta.norm=3 by decide +kernel,← Finset.mul_sum] at he
  omega

theorem eisenstein_six_normalized_weight (x : EisensteinShell 6)
    (u : EisensteinCoordinates) (hu : x.val.val=eisensteinTheta • u) :
    ternaryWeight (eisensteinWordResidue u) ≤ 9 := by
  have hs := eisenstein_six_normalized_norm_sum x u hu
  have he (i : Fin 12) : (if eisensteinResidue (u i)≠0 then (1 : ℤ) else 0) ≤ (u i).norm := by
    have hn := eisenstein_norm_nonneg (u i)
    by_cases hi : eisensteinResidue (u i)=0
    · simp [hi,hn]
    · have hd := (eisensteinResidue_zero_iff_norm (u i)).not.mp hi
      rw [if_pos hi]
      omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 12))) => he i)
  rw [hs] at hsum
  have hw : (ternaryWeight (eisensteinWordResidue u) : ℤ) =
      ∑ i,if eisensteinResidue (u i)≠0 then (1 : ℤ) else 0 := by
    simp only [ternaryWeight,eisensteinWordResidue,Finset.card_eq_sum_ones,Finset.sum_filter,
      Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [← hw] at hsum
  exact_mod_cast hsum

/-- A short class containing a normalized constant hexad can only retain that
hexad codeword or the negative complementary codeword. -/
theorem eisenstein_constant_hexad_class_normalized (s : Finset (Fin 12))
    (x y : EisensteinShell 6) (u v : EisensteinCoordinates)
    (hu : x.val.val=eisensteinTheta • u) (hv : y.val.val=eisensteinTheta • v)
    (hcode : eisensteinWordResidue u=ternaryTriadWord s)
    (hc : eisensteinClass x.val=eisensteinClass y.val) :
    eisensteinWordResidue v=ternaryTriadWord s ∨
      eisensteinWordResidue v= -ternaryTriadWord sᶜ := by
  have huL : eisensteinTheta • u ∈ eisensteinLeechModule := hu ▸ x.val.property
  have hvL : eisensteinTheta • v ∈ eisensteinLeechModule := hv ▸ y.val.property
  have hclass : eisensteinClass ⟨eisensteinTheta • u,huL⟩ =
      eisensteinClass ⟨eisensteinTheta • v,hvL⟩ := by
    have hx : (⟨eisensteinTheta • u,huL⟩ : EisensteinLattice)=x.val := Subtype.ext hu.symm
    have hy : (⟨eisensteinTheta • v,hvL⟩ : EisensteinLattice)=y.val := Subtype.ext hv.symm
    rw [hx,hy]
    exact hc
  obtain ⟨a,ha⟩ := eisensteinTheta_class_residue u v huL hvL hclass
  apply ternaryConstant_shift_short s (eisensteinWordResidue v)
    (by have h := eisenstein_six_normalized_weight y v hv; omega) a
  intro i
  have hh := congrFun hcode i
  change eisensteinResidue (u i)=ternaryTriadWord s i at hh
  rw [← hh]
  exact ha i

end Atlas.Lattices
