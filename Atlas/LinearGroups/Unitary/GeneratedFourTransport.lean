import Atlas.LinearGroups.Unitary.SupportFourReduction

/-! Norm-one transitivity of the actual transvection-generated subgroup, obtained
by decreasing support with actual four-coordinate blocks. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {k : ℕ}

/-- A sparse norm-one vector is carried to the first coordinate by a single
actual SU₄ block containing its support and that coordinate. -/
theorem exists_generated_map_sparse_to_first_four (hdeg : Module.finrank F K = 2)
    (hfour : transvectionGenerated hdeg (n := 4) = ⊤) (v : Fin (4+k) → K)
    (hv : hermitian F K v v = 1) (hsparse : (vectorSupport v).card ≤ 3) :
    ∃ g : SU F K (4+k) hdeg, g ∈ transvectionGenerated hdeg ∧ g.val *ᵥ v = Pi.single 0 1 := by
  classical
  obtain ⟨s,hsub,_,hs⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (insert (0 : Fin (4+k)) (vectorSupport v)))
    (show (insert (0 : Fin (4+k)) (vectorSupport v)).card ≤ 4 from
      le_trans (Finset.card_insert_le _ _) (by omega)) (by simp)
  let e : s ≃ Fin 4 := s.equivFinOfCardEq hs
  let I : Fin 4 ↪ Fin (4+k) := e.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have hrange (i : Fin (4+k)) : i ∈ Set.range I ↔ i ∈ s := by
    constructor
    · rintro ⟨j,rfl⟩
      exact (e.symm j).property
    · intro hi
      refine ⟨e ⟨i,hi⟩, ?_⟩
      simp [I]
  have hzero (i : Fin (4+k)) (hi : i ∉ Set.range I) : v i = 0 := by
    by_contra h
    apply hi
    apply (hrange i).mpr
    exact hsub (Finset.mem_insert_of_mem ((mem_vectorSupport v i).mpr h))
  have hs0 : (0 : Fin (4+k)) ∈ s := hsub (Finset.mem_insert_self _ _)
  let i0 := e ⟨0,hs0⟩
  have hI0 : I i0 = 0 := by simp [I, i0]
  have hlocal : hermitian F K (v ∘ I) (v ∘ I) = 1 := by
    have he := Fintype.sum_of_injective I I.injective
      (fun i => v (I i) * conjugation F K (v (I i)))
      (fun i => v i * conjugation F K (v i))
      (fun i hi => by rw [hzero i hi, zero_mul]) (fun _ => rfl)
    exact he.trans hv
  obtain ⟨g,hg⟩ := exists_special_unitary_map hdeg (by decide : 2 ≤ 4)
    (v ∘ I) (Pi.single i0 1) hlocal (by simp)
  have hggen : g ∈ transvectionGenerated hdeg := by
    rw [hfour]; trivial
  refine ⟨coordinateBlockHom hdeg I g, coordinateBlockHom_generated hdeg I g hggen, ?_⟩
  ext i
  by_cases hi : i ∈ Set.range I
  · obtain ⟨j,rfl⟩ := hi
    rw [coordinateBlockHom_apply_inside, hg]
    have he : I j = 0 ↔ j = i0 := by rw [← hI0]; exact I.injective.eq_iff
    simp [Pi.single_apply, he]
  · rw [coordinateBlockHom_apply_outside hdeg I g v i hi, hzero i hi]
    have hi0 : i ≠ 0 := by rintro rfl; exact hi ((hrange 0).mpr hs0)
    simp [hi0]

/-- Given generation in dimension four, in every dimension at least four, the actual generated subgroup is
transitive on norm-one vectors; isotropic restrictions were handled in support descent. -/
theorem exists_generated_map_to_first_four (hdeg : Module.finrank F K = 2)
    (hfour : transvectionGenerated hdeg (n := 4) = ⊤) (v : Fin (4+k) → K) (hv : hermitian F K v v = 1) :
    ∃ g : SU F K (4+k) hdeg, g ∈ transvectionGenerated hdeg ∧ g.val *ᵥ v = Pi.single 0 1 := by
  obtain ⟨g,hg,hsparse⟩ := exists_generated_sparse_four hdeg hfour v
  have hv' : hermitian F K (g.val *ᵥ v) (g.val *ᵥ v) = 1 :=
    (u_preserves_hermitian hdeg (⟨g.val,g.prop.1⟩ : U F K (4+k) hdeg) v v).trans hv
  obtain ⟨h,hh,he⟩ := exists_generated_map_sparse_to_first_four hdeg hfour (g.val *ᵥ v) hv' hsparse
  refine ⟨h*g, (transvectionGenerated hdeg).mul_mem hh hg, ?_⟩
  change (h.val*g.val) *ᵥ v = _
  rwa [← mulVec_mulVec]
end Atlas.Unitary
