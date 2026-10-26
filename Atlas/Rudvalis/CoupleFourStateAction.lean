import Atlas.Rudvalis.CoupleFourStates

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem coupleFourForm_ne_zero (a : Fin 3) : coupleFourForm a≠0 := by decide +kernel +revert

theorem coupleFourSupport_admissible (a : Fin 3) (m : E) : admissibleFourSupport (coupleFourSupport a m) :=
  ⟨⟨coupleFourForm a,coupleFourForm_ne_zero a⟩,coupleFourConstants a m,rfl,coupleFourConstants_valid a m⟩

theorem coupleFourRowConstants_exhaustive (a : Fin 3) (f : Fin 7→Bit)
    (hz : ∀r,dot (coupleFourForm a) (rowLabel r).val=0 → f r=0)
    (hs : (∑r,f r)=1) : ∃m : E,∀r,f r=coupleFourRowConstants a m r := by
  decide +kernel +revert

theorem coupleFourConstants_exhaustive (a : Fin 3) (ε : Point→Bit)
    (hz : ∀p,dot (coupleFourForm a) p.val=0 → ε p=0)
    (hs : (∑p,ε p)=1) : ∃m : E,ε=coupleFourConstants a m := by
  have hsum : (∑r,ε (rowLabel r))=1 := (Equiv.sum_comp rowEquiv ε).trans hs
  obtain ⟨m,hm⟩ := coupleFourRowConstants_exhaustive a (fun r=>ε (rowLabel r))
    (fun r=>hz (rowLabel r)) hsum
  refine ⟨m,?_⟩
  funext p
  obtain ⟨r,rfl⟩ := rowLabel_bijective.2 p
  rw [coupleFourConstants_rows]
  exact hm r

theorem coupleCodeGenerator_transport (b : Fin 2) :
    (coupleCodeGenerator b).val=seedConjugateHom (coupleOriginalGenerator b) := by
  unfold coupleCodeGenerator coupleOriginalGenerator
  split_ifs
  · rfl
  · exact coupleCodeBeta_transport

theorem original_congr_symm_apply (p : Equiv.Perm SeedCoordinate) (z : SeedCoordinate) :
    (originalCoordinateEquiv.permCongrHom p).symm (originalCoordinateEquiv z)=
      originalCoordinateEquiv (p.symm z) := by
  apply (originalCoordinateEquiv.permCongrHom p).injective
  rw [Equiv.apply_symm_apply,original_congr_apply,Equiv.apply_symm_apply]

theorem coupleCodeGenerator_inverse_coordinate (b : Fin 2) (z : SeedCoordinate) :
    (coupleCodeGenerator b).val.right.symm (originalCoordinateEquiv z)=
      originalCoordinateEquiv ((coupleOriginalGenerator b).right.symm z) := by
  rw [coupleCodeGenerator_transport]
  change (seedConjugateMonomial (coupleOriginalGenerator b)).right.symm (originalCoordinateEquiv z)=_
  rw [seedConjugateMonomial_right,original_congr_symm_apply]

/-- Exact action on actual normal-form binary supports, not merely on formal state labels. -/
theorem coupleFourSupport_action (b : Fin 2) (a : Fin 3) (m : E) :
    coupleFourSupport a m ∘ (coupleCodeGenerator b).val.right.symm=
      coupleFourSupport (coupleFourTransportForm a) (coupleFourTransportParameters b a m) := by
  funext z
  obtain ⟨z,rfl⟩ := originalCoordinateEquiv.surjective z
  simp only [Function.comp_apply,coupleCodeGenerator_inverse_coordinate,coupleFourSupport_original,
    coupleFour_original_transport]

theorem coupleSixState_fibre_card (s : Fin 6) :
    Nat.card {z : Fin 3×E // coupleFourState z.1 z.2=s}=4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel +revert

theorem coupleSixState_permutation_bijective (b : Fin 2) :
    Function.Bijective (coupleSixStatePermutation b) := by decide +kernel +revert

/-- The displayed beta permutation alone connects each of the two state blocks. -/
theorem coupleSixState_beta_connected (s t : Fin 6)
    (h : (s.val<2 ↔ t.val<2)) :
    ∃n : Fin 4,((coupleSixStatePermutation 1)^[n.val]) s=t := by
  decide +kernel +revert

end Atlas.Rudvalis
