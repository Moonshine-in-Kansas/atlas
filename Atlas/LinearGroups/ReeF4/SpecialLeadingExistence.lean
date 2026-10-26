import Atlas.LinearGroups.ReeF4.SpecialLeadingClassification
import Mathlib.Data.Finset.Max

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- On the nonpositive part of the actual grading, the three diagonal adjoint
coordinates force both marked diagonal coefficients to vanish. -/
theorem IsSpecialVector.diagonal_zero_of_no_positive {m : ℕ} {u : TraceZero F}
    (hu : IsSpecialVector m u)
    (hp : ∀ j, 0 < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    isotropyCoordinates u 0=0 ∧ isotropyCoordinates u 1=0 := by
  have h0 : fullAdjointDiag0 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointDiag0_actual,hu.adjoint_zero]; rfl
  have h1 : fullAdjointDiag1 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointDiag1_actual,hu.adjoint_zero]; rfl
  have h2 : fullAdjointDiag2 (isotropyCoordinates u)=0 := by
    rw [←fullAdjointDiag2_actual,hu.adjoint_zero]; rfl
  have hz6 := hp 6 (by decide)
  have hz7 := hp 7 (by decide)
  have hz8 := hp 8 (by decide)
  have hz9 := hp 9 (by decide)
  have hz14 := hp 14 (by decide)
  have hz15 := hp 15 (by decide)
  have hz16 := hp 16 (by decide)
  have hz17 := hp 17 (by decide)
  have hz21 := hp 21 (by decide)
  have hz23 := hp 23 (by decide)
  have hz24 := hp 24 (by decide)
  have hz25 := hp 25 (by decide)
  simp only [fullAdjointDiag0,fullAdjointDiag1,fullAdjointDiag2,hz6,hz7,hz8,hz9,
    hz14,hz15,hz16,hz17,hz21,hz23,hz24,hz25,mul_zero,zero_mul,add_zero] at h0 h1 h2
  rw [h2,add_zero] at h0 h1
  exact ⟨sq_eq_zero_iff.mp h0,sq_eq_zero_iff.mp h1⟩

/-- Every intrinsic special vector has one of exactly the eight allowed
leading root labels, with every higher coordinate zero. -/
theorem IsSpecialVector.exists_allowed_leading_root {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) :
    ∃ r : Fin 26, allowedSpecialLeadingRoot r ∧ isotropyCoordinates u r≠0 ∧
      ∀ j, specialAbsoluteGrade r < specialAbsoluteGrade j → isotropyCoordinates u j=0 := by
  classical
  let s : Finset (Fin 26) := Finset.univ.filter (fun i => isotropyCoordinates u i≠0)
  have hs : s.Nonempty := by
    by_contra he
    have hz : isotropyCoordinates u = 0 := by
      funext i
      by_contra hi
      exact he ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
    apply hu.ne_zero
    calc
      u = isotropyPoint (isotropyCoordinates u) := (isotropyPoint_coordinates u).symm
      _ = isotropyPoint (isotropyCoordinates (0 : TraceZero F)) := by
        rw [hz,_root_.map_zero]
      _ = 0 := isotropyPoint_coordinates 0
  obtain ⟨r,hr,hmax⟩ := Finset.exists_max_image s specialAbsoluteGrade hs
  have hn : isotropyCoordinates u r≠0 := (Finset.mem_filter.mp hr).2
  have hz : ∀ j, specialAbsoluteGrade r < specialAbsoluteGrade j → isotropyCoordinates u j=0 := by
    intro j hj
    by_contra hne
    exact (not_lt_of_ge (hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hne⟩))) hj
  have hrroot : 2 ≤ r.val := by
    by_contra h
    have hi : r=0 ∨ r=1 := by
      have hv : r.val=0 ∨ r.val=1 := by omega
      rcases hv with hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Fin.ext hv)
    have hg : specialAbsoluteGrade r=0 := by
      rcases hi with rfl | rfl <;> rfl
    have hd := hu.diagonal_zero_of_no_positive (by simpa only [hg] using hz)
    rcases hi with rfl | rfl
    · exact hn hd.1
    · exact hn hd.2
  exact ⟨r,hu.leading_root_allowed hcard r hrroot hn hz,hn,hz⟩
end Atlas.ReeF4
