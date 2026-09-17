import Atlas.Lattices.EisensteinHexadFrames

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped QuadraticAlgebra

/-- The unique heavy coordinate distinguishes the twelve lines without enumeration. -/
theorem eisensteinHexadVector_coordinate_norm (s : Finset (Fin 12))
    (i : Fin 12) (hi : i ∈ s) (k : Fin 12) :
    (eisensteinHexadVector s i k).norm =
      if k=i then 12 else if k ∈ s then 3 else 0 := by
  by_cases hki : k=i
  · subst k
    norm_num [eisensteinHexadVector,eisensteinHexadLift,Pi.smul_apply,smul_eq_mul,hi,
      eisensteinTheta,eisensteinOmega,QuadraticAlgebra.omega,QuadraticAlgebra.norm_def]
  · by_cases hk : k ∈ s <;>
      norm_num [eisensteinHexadVector,eisensteinHexadLift,Pi.smul_apply,smul_eq_mul,hki,hk,
        eisensteinTheta,eisensteinOmega,QuadraticAlgebra.omega,QuadraticAlgebra.norm_def]

theorem eisensteinHexadVector_line_heavy (s t : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (ht : t ∈ ternaryConstantHexads)
    (i j : Fin 12) (hi : i ∈ s) (hj : j ∈ t)
    (he : eisensteinScalarLine (eisensteinHexadShellVector s hs i hi) =
      eisensteinScalarLine (eisensteinHexadShellVector t ht j hj)) : i=j := by
  obtain ⟨u,hu⟩ := eisenstein_six_sameLine_unit _ _
    (eisensteinHexadVector_norm t ht j hj) (eisensteinHexadVector_norm s hs i hi)
    ((eisensteinScalarLine_eq_iff _ _).mp he)
  have hh := congrArg (fun x : EisensteinLattice => (x.val i).norm) hu
  change (eisensteinHexadVector s i i).norm =
    ((u : Eisenstein)*eisensteinHexadVector t j i).norm at hh
  rw [map_mul,(eisenstein_isUnit_iff (u : Eisenstein)).mp u.isUnit,one_mul,
    eisensteinHexadVector_coordinate_norm s i hi i,
    eisensteinHexadVector_coordinate_norm t j hj i] at hh
  by_contra hij
  simp only [ite_true, hij, ite_false] at hh
  split_ifs at hh <;> norm_num at hh

/-- Choose the member of the complementary pair that contains a given coordinate. -/
def eisensteinHexadSideVector (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (j : Fin 12) : EisensteinShell 6 :=
  if h : j ∈ s then eisensteinHexadShellVector s hs j h else
    eisensteinHexadShellVector sᶜ (ternaryConstantHexads_compl s hs) j
      (Finset.mem_compl.mpr h)

theorem eisensteinHexadSideVector_mem (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s) (j : Fin 12) :
    eisensteinHexadSideVector s hs j ∈
      eisensteinFrameVectors (eisensteinHexadFrame s hs i hi) := by
  unfold eisensteinHexadSideVector
  split_ifs with hj
  · exact eisensteinHexadFrame_contains s hs i j hi hj
  · exact eisensteinHexadFrame_contains_compl s hs i j hi (Finset.mem_compl.mpr hj)

theorem eisensteinHexadSideLines_injective (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) :
    Function.Injective (fun j => eisensteinScalarLine (eisensteinHexadSideVector s hs j)) := by
  intro i j he
  unfold eisensteinHexadSideVector at he
  dsimp only at he
  split_ifs at he <;> exact eisensteinHexadVector_line_heavy _ _ _ _ _ _ _ _ he

/-- These twelve explicit heavy-hexad lines exhaust the intrinsic frame. -/
theorem eisensteinHexadFrame_lines (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s) :
    eisensteinFrameLines (eisensteinHexadFrame s hs i hi) =
      Finset.univ.image (fun j => eisensteinScalarLine (eisensteinHexadSideVector s hs j)) := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro L hL
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    exact (eisensteinFrameLines_recovers_vectors _ _).mpr
      (eisensteinHexadSideVector_mem s hs i hi j)
  · rw [eisensteinFrameLines_card,Finset.card_image_of_injective _
      (eisensteinHexadSideLines_injective s hs)]
    simp

end Atlas.Lattices
