import Atlas.Lattices.EisensteinShortLines
import Atlas.Lattices.EisensteinMonomial

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

/-- The scalar norm possibilities below the norm-six shell's coordinate bound. -/
theorem eisenstein_scalar_norm_le27 (z : Eisenstein) (hz : z.norm ≤ 27) :
    z.norm ∈ ([0,1,3,4,7,9,12,13,16,19,21,25,27] : List ℤ) := by
  have hn := eisenstein_norm z
  have hr : -6 ≤ z.re ∧ z.re ≤ 6 := by
    have h1 : 3*z.re^2 ≤ 4*z.norm := by nlinarith [sq_nonneg (z.re-2*z.im)]
    constructor <;> nlinarith
  have hi : -6 ≤ z.im ∧ z.im ≤ 6 := by
    have h1 : 3*z.im^2 ≤ 4*z.norm := by nlinarith [sq_nonneg (z.im-2*z.re)]
    constructor <;> nlinarith
  have hfinite : ∀ a b : Fin 13,
      let n := ((a.val : ℤ)-6)^2-((a.val : ℤ)-6)*((b.val : ℤ)-6)+((b.val : ℤ)-6)^2
      n ≤ 27 → n ∈ ([0,1,3,4,7,9,12,13,16,19,21,25,27] : List ℤ) := by decide +kernel
  let a : Fin 13 := ⟨(z.re+6).toNat,by omega⟩
  let b : Fin 13 := ⟨(z.im+6).toNat,by omega⟩
  have ha : (a.val : ℤ)-6 = z.re := by dsimp [a]; omega
  have hb : (b.val : ℤ)-6 = z.im := by dsimp [b]; omega
  have h := hfinite a b
  simp only [ha,hb,← hn] at h
  exact h hz

/-- Scalar residue detects norm divisibility by three. -/
theorem eisensteinResidue_norm (z : Eisenstein) :
    (z.norm : ZMod 3) = (eisensteinResidue z)^2 := by
  rw [eisenstein_norm]
  change ((z.re^2-z.re*z.im+z.im^2 : ℤ) : ZMod 3) =
    ((z.re : ZMod 3)+(z.im : ZMod 3))^2
  push_cast
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination -(z.re : ZMod 3)*(z.im : ZMod 3)*h3

theorem eisensteinResidue_zero_iff_norm (z : Eisenstein) :
    eisensteinResidue z = 0 ↔ 3 ∣ z.norm := by
  change eisensteinResidue z = 0 ↔ ((3 : ℕ) : ℤ) ∣ z.norm
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, eisensteinResidue_norm]
  exact (sq_eq_zero_iff).symm

theorem eisenstein_six_sum_norms (x : EisensteinShell 6) :
    ∑ i, (x.val.val i).norm = 27 := by
  have h := x.property
  unfold eisensteinNorm at h
  rw [eisensteinBilinear_self_sum_norm] at h
  have he : ∑ i, (eisensteinCoordinateEmbedding x.val.val i).norm =
      ((∑ i, (x.val.val i).norm : ℤ) : ℚ) := by
    simp only [eisensteinCoordinateEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
      eisensteinToRational_norm, Int.cast_sum]
  rw [he] at h
  have hq : ((∑ i, (x.val.val i).norm : ℤ) : ℚ) = 27 := by linarith
  exact_mod_cast hq

theorem eisenstein_six_coordinate_norm_le (x : EisensteinShell 6) (i : Fin 12) :
    (x.val.val i).norm ≤ 27 := by
  rw [← eisenstein_six_sum_norms x]
  exact Finset.single_le_sum (fun j _ => eisenstein_norm_nonneg _) (Finset.mem_univ i)


def eisensteinNormCount (x : EisensteinShell 6) (n : ℤ) : ℕ :=
  (Finset.univ.filter (fun i => (x.val.val i).norm=n)).card

/-- Histogram identity used only on the thirteen possible scalar norms. -/
theorem eisensteinNormCount_sum (x : EisensteinShell 6) (s : Finset ℤ)
    (hs : ∀ i, (x.val.val i).norm ∈ s) :
    ∑ n ∈ s, n*(eisensteinNormCount x n : ℤ) = 27 := by
  rw [← eisenstein_six_sum_norms x]
  simp only [eisensteinNormCount,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (x.val.val i).norm]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · exact fun h => (h (hs i)).elim

theorem eisensteinNormCount_card (x : EisensteinShell 6) (s : Finset ℤ)
    (hs : ∀ i, (x.val.val i).norm ∈ s) :
    ∑ n ∈ s, eisensteinNormCount x n = 12 := by
  simp only [eisensteinNormCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  have he (i : Fin 12) : (∑ n ∈ s, if (x.val.val i).norm=n then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single (x.val.val i).norm]
    · simp
    · intro b hb hbi; simp [Ne.symm hbi]
    · exact fun h => (h (hs i)).elim
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

/-- Every coordinate in a zero-residue lattice vector has one of six norms. -/
theorem eisenstein_six_zeroResidue_values (x : EisensteinShell 6)
    (hx : ∀ i, eisensteinResidue (x.val.val i)=0) (i : Fin 12) :
    (x.val.val i).norm ∈ ({0,3,9,12,21,27} : Finset ℤ) := by
  have hn := eisenstein_scalar_norm_le27 _ (eisenstein_six_coordinate_norm_le x i)
  have hd := (eisensteinResidue_zero_iff_norm _).mp (hx i)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp_all

/-- Every coordinate in a nonzero-residue lattice vector has one of five norms:
the other eleven nonzero coordinates leave a bound sixteen. -/
theorem eisenstein_six_nonzeroResidue_values (x : EisensteinShell 6)
    (hx : ∀ i, eisensteinResidue (x.val.val i)≠0) (i : Fin 12) :
    (x.val.val i).norm ∈ ({1,4,7,13,16} : Finset ℤ) := by
  have hp (j : Fin 12) : 1 ≤ (x.val.val j).norm := by
    have hn := eisenstein_norm_nonneg (x.val.val j)
    have hd := (eisensteinResidue_zero_iff_norm _).not.mp (hx j)
    by_contra h
    have hz : (x.val.val j).norm=0 := by omega
    exact hd (hz ▸ dvd_zero _)
  have hb : (x.val.val i).norm ≤ 16 := by
    have hsum := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => hp j)
    have he := Finset.sum_erase_add (s := Finset.univ) (f := fun j => (x.val.val j).norm) (Finset.mem_univ i)
    rw [eisenstein_six_sum_norms] at he
    norm_num [Finset.card_erase_of_mem (Finset.mem_univ i)] at hsum
    rw [eisenstein_six_sum_norms] at hsum
    linarith
  have hn := eisenstein_scalar_norm_le27 _ (eisenstein_six_coordinate_norm_le x i)
  have hd := (eisensteinResidue_zero_iff_norm _).not.mp (hx i)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp_all


theorem eisenstein_six_zeroResidue_weight (x : EisensteinShell 6)
    (hx : ∀ i, eisensteinResidue (x.val.val i)=0) :
    eisensteinNormCount x 3 + eisensteinNormCount x 12 + eisensteinNormCount x 21 = 0 ∨
      6 ≤ eisensteinNormCount x 3 + eisensteinNormCount x 12 + eisensteinNormCount x 21 := by
  have hd (i : Fin 12) := (eisensteinResidue_eq_zero _).mp (hx i)
  choose a ha using hd
  have he : x.val.val = fun i => eisensteinTheta*a i := funext ha
  have hc : eisensteinWordResidue a ∈ ternaryGolay :=
    eisensteinLeechModule_theta_code a (by change (fun i => eisensteinTheta*a i) ∈ _; rw [← he]; exact x.val.property)
  have hn (i : Fin 12) : (x.val.val i).norm = 3*(a i).norm := by
    rw [ha i,map_mul,show eisensteinTheta.norm=3 by decide +kernel]
  have hr (i : Fin 12) : eisensteinResidue (a i) ≠ 0 ↔
      (x.val.val i).norm=3 ∨ (x.val.val i).norm=12 ∨ (x.val.val i).norm=21 := by
    have hi := eisenstein_six_zeroResidue_values x hx i
    rw [ne_eq,eisensteinResidue_zero_iff_norm]
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with hi|hi|hi|hi|hi|hi <;> rw [hi] <;> have hni := hn i <;> rw [hi] at hni <;> omega
  have hw : ternaryWeight (eisensteinWordResidue a) =
      eisensteinNormCount x 3 + eisensteinNormCount x 12 + eisensteinNormCount x 21 := by
    simp only [ternaryWeight,eisensteinNormCount,Finset.card_eq_sum_ones,Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    change (if eisensteinResidue (a i)≠0 then 1 else 0) = _
    simp only [hr]
    by_cases h3 : (x.val.val i).norm=3 <;> by_cases h12 : (x.val.val i).norm=12 <;>
      by_cases h21 : (x.val.val i).norm=21 <;> simp [h3,h12,h21] <;> omega
  by_cases hz : eisensteinWordResidue a = 0
  · left
    rw [← hw,(ternaryWeight_eq_zero _).mpr hz]
  · right
    rw [← hw]
    exact ternaryGolay_minimum _ hc hz

/-- Zero-residue norm-six vectors have precisely the five indicated histograms,
ordered by scalar norms 0,3,9,12,21,27. -/
theorem eisenstein_six_zeroResidue_patterns (x : EisensteinShell 6)
    (hx : ∀ i, eisensteinResidue (x.val.val i)=0) :
    [eisensteinNormCount x 0,eisensteinNormCount x 3,eisensteinNormCount x 9,
      eisensteinNormCount x 12,eisensteinNormCount x 21,eisensteinNormCount x 27] ∈
      ([[11,0,0,0,0,1],[9,0,3,0,0,0],[6,5,0,1,0,0],
        [5,6,1,0,0,0],[3,9,0,0,0,0]] : List (List ℕ)) := by
  have hs := eisensteinNormCount_sum x {0,3,9,12,21,27} (eisenstein_six_zeroResidue_values x hx)
  have hc := eisensteinNormCount_card x {0,3,9,12,21,27} (eisenstein_six_zeroResidue_values x hx)
  have hw := eisenstein_six_zeroResidue_weight x hx
  norm_num at hs hc
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true]
  have h27 : eisensteinNormCount x 27 ≤ 1 := by omega
  have h21 : eisensteinNormCount x 21 ≤ 1 := by omega
  have h12 : eisensteinNormCount x 12 ≤ 2 := by omega
  have h9 : eisensteinNormCount x 9 ≤ 3 := by omega
  interval_cases eisensteinNormCount x 27 <;>
    interval_cases eisensteinNormCount x 21 <;>
    interval_cases eisensteinNormCount x 12 <;>
    interval_cases eisensteinNormCount x 9 <;> omega

/-- Nonzero-residue norm-six vectors have precisely the five indicated histograms,
ordered by scalar norms 1,4,7,13,16. -/
theorem eisenstein_six_nonzeroResidue_patterns (x : EisensteinShell 6)
    (hx : ∀ i, eisensteinResidue (x.val.val i)≠0) :
    [eisensteinNormCount x 1,eisensteinNormCount x 4,eisensteinNormCount x 7,
      eisensteinNormCount x 13,eisensteinNormCount x 16] ∈
      ([[11,0,0,0,1],[10,1,0,1,0],[9,1,2,0,0],
        [8,3,1,0,0],[7,5,0,0,0]] : List (List ℕ)) := by
  have hs := eisensteinNormCount_sum x {1,4,7,13,16} (eisenstein_six_nonzeroResidue_values x hx)
  have hc := eisensteinNormCount_card x {1,4,7,13,16} (eisenstein_six_nonzeroResidue_values x hx)
  norm_num at hs hc
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true]
  have h16 : eisensteinNormCount x 16 ≤ 1 := by omega
  have h13 : eisensteinNormCount x 13 ≤ 1 := by omega
  have h7 : eisensteinNormCount x 7 ≤ 2 := by omega
  interval_cases eisensteinNormCount x 16 <;>
    interval_cases eisensteinNormCount x 13 <;>
    interval_cases eisensteinNormCount x 7 <;> omega


/-- The common lattice congruence ensures that the two histogram cases cover
every actual norm-six vector. -/
theorem eisenstein_six_residue_dichotomy (x : EisensteinShell 6) :
    (∀ i, eisensteinResidue (x.val.val i)=0) ∨
      (∀ i, eisensteinResidue (x.val.val i)≠0) := by
  obtain ⟨m,hm⟩ := x.val.property
  by_cases hz : eisensteinResidue m=0
  · exact Or.inl (fun i => (eisensteinCongruence_residue _ m hm i).trans hz)
  · exact Or.inr (fun i h => hz ((eisensteinCongruence_residue _ m hm i).symm.trans h))

end Atlas.Lattices
