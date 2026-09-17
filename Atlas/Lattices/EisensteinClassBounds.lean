import Atlas.Lattices.EisensteinShortClasses
import Atlas.Lattices.EisensteinShortGeometry
import Atlas.Lattices.EisensteinPhaseBound

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

/-- Integral and rational scalar rotations agree under the actual embedding. -/
theorem eisensteinLatticeRotation_embedding (x : EisensteinLattice) :
    eisensteinCoordinateEmbedding (eisensteinLatticeRotation x).val =
      eisensteinRotation (eisensteinCoordinateEmbedding x.val) := by
  exact eisensteinCoordinateEmbedding_omega x.val

theorem eisensteinNorm_rotation (x : EisensteinLattice) :
    eisensteinNorm (eisensteinLatticeRotation x) = eisensteinNorm x := by
  unfold eisensteinNorm
  rw [eisensteinLatticeRotation_embedding, eisensteinBilinear_rotation_self]

theorem eisensteinNorm_zero : eisensteinNorm 0 = 0 := by
  simp [eisensteinNorm, eisensteinCoordinateEmbedding, eisensteinBilinear,
    eisensteinHermitian, eisensteinReal]

theorem eisensteinNorm_sub (x y : EisensteinLattice) :
    eisensteinNorm (x-y) =
      eisensteinBilinear (eisensteinCoordinateEmbedding x.val - eisensteinCoordinateEmbedding y.val)
        (eisensteinCoordinateEmbedding x.val - eisensteinCoordinateEmbedding y.val) := by
  unfold eisensteinNorm
  rw [Submodule.coe_sub, map_sub]

theorem eisensteinLatticeRotation_cube (x : EisensteinLattice) :
    eisensteinLatticeRotation (eisensteinLatticeRotation (eisensteinLatticeRotation x)) = x := by
  apply Subtype.ext
  apply eisensteinCoordinateEmbedding_injective
  simp only [eisensteinLatticeRotation_embedding, eisensteinRotation_cube]

theorem eisensteinLatticeRotation_injective : Function.Injective eisensteinLatticeRotation := by
  intro x y h
  have hh := congrArg (fun z => eisensteinLatticeRotation (eisensteinLatticeRotation z)) h
  simpa only [eisensteinLatticeRotation_cube] using hh

theorem eisensteinLatticeRotation_fixed_iff (x : EisensteinLattice) :
    eisensteinLatticeRotation x = x ↔ x = 0 := by
  constructor
  · intro h
    have he := congrArg (fun z : EisensteinLattice => eisensteinCoordinateEmbedding z.val) h
    rw [eisensteinLatticeRotation_embedding] at he
    have hz := (eisensteinRotation_fixed_iff _).mp he
    apply Subtype.ext
    apply eisensteinCoordinateEmbedding_injective
    simpa only [Submodule.coe_zero, map_zero] using hz
  · rintro rfl; exact smul_zero _

theorem eisensteinClass_sub_mem {x y : EisensteinLattice}
    (h : eisensteinClass x = eisensteinClass y) : x-y ∈ eisensteinThetaEnd.range :=
  (Submodule.Quotient.eq _).mp h

/-- If three phase differences in one class are nonzero, each has norm at least twelve. -/
theorem eisenstein_sameClass_norm_sum_ge
    (x y : EisensteinLattice) (hc : eisensteinClass x = eisensteinClass y)
    (h0 : x ≠ y) (h1 : x ≠ eisensteinLatticeRotation y)
    (h2 : x ≠ eisensteinLatticeRotation (eisensteinLatticeRotation y)) :
    12 ≤ eisensteinNorm x + eisensteinNorm y := by
  have hA := eisensteinNorm_theta_minimum (x-y) (eisensteinClass_sub_mem hc) (sub_ne_zero.mpr h0)
  have hB := eisensteinNorm_theta_minimum (x-eisensteinLatticeRotation y)
    (eisensteinClass_sub_mem (hc.trans (eisensteinLatticeRotation_class y).symm))
    (sub_ne_zero.mpr h1)
  have hC := eisensteinNorm_theta_minimum (x-eisensteinLatticeRotation (eisensteinLatticeRotation y))
    (eisensteinClass_sub_mem (hc.trans
      ((eisensteinLatticeRotation_class (eisensteinLatticeRotation y)).trans
        (eisensteinLatticeRotation_class y)).symm)) (sub_ne_zero.mpr h2)
  rw [eisensteinNorm_sub] at hA hB hC
  rw [eisensteinLatticeRotation_embedding] at hB
  rw [eisensteinLatticeRotation_embedding, eisensteinLatticeRotation_embedding] at hC
  exact eisenstein_norm_sum_ge_of_three_differences _ _ 12 hA hB hC

/-- Two norm-four vectors in one theta-class differ by a scalar phase. -/
theorem eisenstein_four_sameClass_phases
    (x y : EisensteinLattice) (hx : eisensteinNorm x = 4) (hy : eisensteinNorm y = 4)
    (hc : eisensteinClass x = eisensteinClass y) :
    x = y ∨ x = eisensteinLatticeRotation y ∨
      x = eisensteinLatticeRotation (eisensteinLatticeRotation y) := by
  by_contra! h
  have hb := eisenstein_sameClass_norm_sum_ge x y hc h.1 h.2.1 h.2.2
  rw [hx, hy] at hb
  norm_num at hb

/-- Norm-four and norm-six shells occupy disjoint theta-classes. -/
theorem eisenstein_four_six_differentClass
    (x y : EisensteinLattice) (hx : eisensteinNorm x = 4) (hy : eisensteinNorm y = 6) :
    eisensteinClass x ≠ eisensteinClass y := by
  intro hc
  have h0 : x ≠ y := by intro h; rw [h, hy] at hx; norm_num at hx
  have h1 : x ≠ eisensteinLatticeRotation y := by
    intro h; rw [h, eisensteinNorm_rotation, hy] at hx; norm_num at hx
  have h2 : x ≠ eisensteinLatticeRotation (eisensteinLatticeRotation y) := by
    intro h; rw [h, eisensteinNorm_rotation, eisensteinNorm_rotation, hy] at hx; norm_num at hx
  have hb := eisenstein_sameClass_norm_sum_ge x y hc h0 h1 h2
  rw [hx, hy] at hb
  norm_num at hb

/-- Norm-six vectors in one class are scalar-phase partners or Hermitian orthogonal. -/
theorem eisenstein_six_sameClass_phases_or_orthogonal
    (x y : EisensteinLattice) (hx : eisensteinNorm x = 6) (hy : eisensteinNorm y = 6)
    (hc : eisensteinClass x = eisensteinClass y) :
    x = y ∨ x = eisensteinLatticeRotation y ∨
      x = eisensteinLatticeRotation (eisensteinLatticeRotation y) ∨
      eisensteinHermitian (eisensteinCoordinateEmbedding x.val) (eisensteinCoordinateEmbedding y.val) = 0 := by
  by_cases h0 : x = y
  · exact Or.inl h0
  by_cases h1 : x = eisensteinLatticeRotation y
  · exact Or.inr (Or.inl h1)
  by_cases h2 : x = eisensteinLatticeRotation (eisensteinLatticeRotation y)
  · exact Or.inr (Or.inr (Or.inl h2))
  refine Or.inr (Or.inr (Or.inr ?_))
  have hA := eisensteinNorm_theta_minimum (x-y) (eisensteinClass_sub_mem hc) (sub_ne_zero.mpr h0)
  have hB := eisensteinNorm_theta_minimum (x-eisensteinLatticeRotation y)
    (eisensteinClass_sub_mem (hc.trans (eisensteinLatticeRotation_class y).symm))
    (sub_ne_zero.mpr h1)
  have hC := eisensteinNorm_theta_minimum (x-eisensteinLatticeRotation (eisensteinLatticeRotation y))
    (eisensteinClass_sub_mem (hc.trans
      ((eisensteinLatticeRotation_class (eisensteinLatticeRotation y)).trans
        (eisensteinLatticeRotation_class y)).symm)) (sub_ne_zero.mpr h2)
  rw [eisensteinNorm_sub] at hA hB hC
  rw [eisensteinLatticeRotation_embedding] at hB
  rw [eisensteinLatticeRotation_embedding, eisensteinLatticeRotation_embedding] at hC
  apply eisenstein_hermitian_zero_of_three_differences _ _ 12 hA hB hC
  change eisensteinNorm x + eisensteinNorm y ≤ 12
  rw [hx, hy]
  norm_num

/-- The fiber of a shell over one actual theta-class. -/
def EisensteinClassFiber (r : ℤ) (c : EisensteinClasses) :=
  {x : EisensteinShell r // eisensteinClass x.val = c}

/-- Every positive vector shorter than twelve occupies a nonzero theta-class. -/
theorem eisenstein_short_class_ne_zero (x : EisensteinLattice)
    (hpos : 0 < eisensteinNorm x) (hsmall : eisensteinNorm x < 12) : eisensteinClass x ≠ 0 := by
  intro hc
  have hx : x ≠ 0 := by intro hx; rw [hx, eisensteinNorm_zero] at hpos; exact lt_irrefl _ hpos
  have hm : x ∈ eisensteinThetaEnd.range := (Submodule.Quotient.mk_eq_zero _).mp hc
  have hh := eisensteinNorm_theta_minimum x hm hx
  linarith

def eisensteinLatticePhase (x : EisensteinLattice) (k : Fin 3) : EisensteinLattice :=
  if k = 0 then x else if k = 1 then eisensteinLatticeRotation x
  else eisensteinLatticeRotation (eisensteinLatticeRotation x)

theorem eisensteinLatticePhase_norm (x : EisensteinLattice) (k : Fin 3) :
    eisensteinNorm (eisensteinLatticePhase x k) = eisensteinNorm x := by
  fin_cases k <;> simp [eisensteinLatticePhase, eisensteinNorm_rotation]

theorem eisensteinLatticePhase_class (x : EisensteinLattice) (k : Fin 3) :
    eisensteinClass (eisensteinLatticePhase x k) = eisensteinClass x := by
  fin_cases k <;> simp [eisensteinLatticePhase, eisensteinLatticeRotation_class]

theorem eisensteinLatticePhase_injective (x : EisensteinLattice) (hx : x ≠ 0) :
    Function.Injective (eisensteinLatticePhase x) := by
  have h1 : eisensteinLatticeRotation x ≠ x := fun h => hx ((eisensteinLatticeRotation_fixed_iff x).mp h)
  have h2 : eisensteinLatticeRotation (eisensteinLatticeRotation x) ≠ x := by
    intro h
    have he := congrArg eisensteinLatticeRotation h
    rw [eisensteinLatticeRotation_cube] at he
    exact h1 he.symm
  have h12 : eisensteinLatticeRotation x ≠ eisensteinLatticeRotation (eisensteinLatticeRotation x) :=
    fun h => h1 (eisensteinLatticeRotation_injective h).symm
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact (h1 h.symm).elim
  · exact (h2 h.symm).elim
  · exact (h1 h).elim
  · rfl
  · exact (h12 h).elim
  · exact (h2 h).elim
  · exact (h12 h.symm).elim
  · rfl

/-- Each occupied norm-four class contains exactly its three scalar phases. -/
theorem eisenstein_four_class_card (x : EisensteinShell 4) :
    Nat.card (EisensteinClassFiber 4 (eisensteinClass x.val)) = 3 := by
  have hx : x.val ≠ 0 := by
    intro hx
    have h := x.property
    rw [hx, eisensteinNorm_zero] at h
    norm_num at h
  let f : Fin 3 → EisensteinClassFiber 4 (eisensteinClass x.val) := fun k =>
    ⟨⟨eisensteinLatticePhase x.val k, (eisensteinLatticePhase_norm x.val k).trans x.property⟩,
      eisensteinLatticePhase_class x.val k⟩
  have hi : Function.Injective f := by
    intro a b h
    apply eisensteinLatticePhase_injective x.val hx
    exact congrArg (fun y : EisensteinClassFiber 4 (eisensteinClass x.val) => y.val.val) h
  have hs : Function.Surjective f := by
    intro y
    have h := eisenstein_four_sameClass_phases y.val.val x.val y.val.property x.property y.property
    rcases h with h | h | h
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact h.symm
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact h.symm
    · refine ⟨2, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact h.symm
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)]
  simp

theorem eisenstein_four_class_card_le (c : EisensteinClasses) :
    Nat.card (EisensteinClassFiber 4 c) ≤ 3 := by
  classical
  by_cases h : Nonempty (EisensteinClassFiber 4 c)
  · obtain ⟨x⟩ := h
    rw [← x.property, eisenstein_four_class_card x.val]
  · letI : IsEmpty (EisensteinClassFiber 4 c) := not_nonempty_iff.mp h
    simp

theorem eisenstein_six_class_card_le (c : EisensteinClasses) :
    Nat.card (EisensteinClassFiber 6 c) ≤ 36 := by
  letI : Finite (EisensteinShell 6) := Nat.finite_of_card_ne_zero (by rw [eisensteinShell_six_card]; decide)
  letI : Finite (EisensteinClassFiber 6 c) := by unfold EisensteinClassFiber; infer_instance
  letI : Fintype (EisensteinClassFiber 6 c) := Fintype.ofFinite _
  let v : EisensteinClassFiber 6 c → EisensteinRationalCoordinates :=
    fun x => eisensteinCoordinateEmbedding x.val.val.val
  have hinj : Function.Injective v := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact eisensteinCoordinateEmbedding_injective h
  have hne : ∀ x, v x ≠ 0 := by
    intro x h
    have hx : x.val.val = 0 := by
      apply Subtype.ext
      apply eisensteinCoordinateEmbedding_injective
      simpa only [Submodule.coe_zero, map_zero] using h
    have hn := x.val.property
    rw [hx, eisensteinNorm_zero] at hn
    norm_num at hn
  have hclass : ∀ x y, v x = v y ∨ v x = eisensteinRotation (v y) ∨
      v x = eisensteinRotation (eisensteinRotation (v y)) ∨ eisensteinHermitian (v x) (v y) = 0 := by
    intro x y
    have h := eisenstein_six_sameClass_phases_or_orthogonal x.val.val y.val.val
      x.val.property y.val.property (x.property.trans y.property.symm)
    rcases h with h | h | h | h
    · exact Or.inl (congrArg (fun z : EisensteinLattice => eisensteinCoordinateEmbedding z.val) h)
    · apply Or.inr ∘ Or.inl
      have he := congrArg (fun z : EisensteinLattice => eisensteinCoordinateEmbedding z.val) h
      simpa only [eisensteinLatticeRotation_embedding] using he
    · apply Or.inr ∘ Or.inr ∘ Or.inl
      have he := congrArg (fun z : EisensteinLattice => eisensteinCoordinateEmbedding z.val) h
      simpa only [eisensteinLatticeRotation_embedding] using he
    · exact Or.inr (Or.inr (Or.inr h))
  simpa only [Nat.card_eq_fintype_card] using eisenstein_phase_or_orthogonal_card_le v hinj hne hclass

end Atlas.Lattices
