import Atlas.Conway.EisensteinUnitResidueSeparation

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem eisensteinResidueOneForms_correction (n : ℤ) (z : Eisenstein)
    (hz : z ∈ eisensteinResidueOneForms n) : ∃ a : Eisenstein, z=1+3*a := by
  have h : z=1 ∨ z= -2 ∨ z=1+3*eisensteinOmega ∨ z= -2-3*eisensteinOmega ∨
      z=1-3*eisensteinOmega ∨ z=4+3*eisensteinOmega ∨ z=4 := by
    unfold eisensteinResidueOneForms at hz
    split_ifs at hz <;> simp_all <;> tauto
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨0,by ring⟩
  · exact ⟨-1,by ring⟩
  · exact ⟨eisensteinOmega,rfl⟩
  · exact ⟨-1-eisensteinOmega,by ring⟩
  · exact ⟨-eisensteinOmega,by ring⟩
  · exact ⟨1+eisensteinOmega,by ring⟩
  · exact ⟨1,by ring⟩

/-- Every residue-one norm-six lattice vector admits normalization using the
actual ternary code phases, not arbitrary independent coordinate units. -/
theorem eisensteinUnitResidue_normalize (x : EisensteinShell 6)
    (hr : ∀ j, eisensteinResidue (x.val.val j)=1) :
    ∃ (t : ternaryGolay) (y : EisensteinShell 6) (a : EisensteinCoordinates),
      x=eisensteinCodePhaseShell t y ∧ ∀ j, y.val.val j=1+3*a j := by
  have hp (j : Fin 12) : ∃ (a : Eisenstein) (t : ZMod 3),
      x.val.val j=eisensteinPhase t*(1+3*a) := by
    have hn := eisenstein_six_nonzeroResidue_values x (by intro i; rw [hr i]; decide) j
    have hle : (x.val.val j).norm≤16 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hn; omega
    obtain ⟨z,hz,t,ht⟩ := eisensteinResidueOne_normalize _ hle (hr j)
    obtain ⟨a,rfl⟩ := eisensteinResidueOneForms_correction _ _ hz
    exact ⟨a,t,ht⟩
  choose a t ht using hp
  let z : EisensteinCoordinates := fun j => 1+3*a j
  have he : x.val.val=eisensteinDiagonal t z := funext ht
  have htc : t ∈ ternaryGolay :=
    eisensteinOneModThree_phase_necessary z a (fun _ => rfl) t (he ▸ x.val.property)
  let T : ternaryGolay := ⟨t,htc⟩
  let y := eisensteinCodePhaseShell (-T) x
  refine ⟨T,y,a,?_,?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    funext j
    change x.val.val j=(eisensteinCodePhaseShell T (eisensteinCodePhaseShell (-T) x)).val.val j
    rw [eisensteinCodePhaseShell_apply,eisensteinCodePhaseShell_apply,← mul_assoc,← eisensteinPhase_add]
    simp [T]
  · intro j
    change (eisensteinCodePhaseShell (-T) x).val.val j=1+3*a j
    rw [eisensteinCodePhaseShell_apply,ht j,← mul_assoc,← eisensteinPhase_add]
    simp [T]

end Atlas.Conway
