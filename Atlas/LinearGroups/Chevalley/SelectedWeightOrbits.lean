import Atlas.LinearGroups.Chevalley.Models
import Atlas.LinearGroups.Chevalley.Integral.MinusculeABCRepresentations
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDAction
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDSpan
import Atlas.LinearGroups.Chevalley.Integral.E6Minuscule.Spanning
import Atlas.LinearGroups.Chevalley.Integral.E6Minuscule.Strings
import Atlas.LinearGroups.Chevalley.Integral.E7Minuscule.Spanning
import Atlas.LinearGroups.Chevalley.Integral.E7Minuscule.Strings
import Atlas.LinearGroups.Chevalley.RootData.ExceptionalWeightLattices

/-! Concrete deterministic weight selection for §4.4.
No center, kernel order,
simply-connected group identification, group order or simplicity is claimed. -/
noncomputable section
namespace Atlas.Chevalley
open Integral.Minuscule
open Classical

/-- One orbit except two half-spin orbits in D and none in E8/F4/G2. -/
def SelectedOrbitIndex : RootType → Type
  | .D _ _ => Bool
  | .E8 | .F4 | .G2 => Empty
  | _ => Unit

instance selectedOrbitIndexFintype (Φ : RootType) : Fintype (SelectedOrbitIndex Φ) := by
  cases Φ <;> dsimp [SelectedOrbitIndex] <;> infer_instance
instance selectedOrbitIndexDecidableEq (Φ : RootType) : DecidableEq (SelectedOrbitIndex Φ) := by
  cases Φ <;> dsimp [SelectedOrbitIndex] <;> infer_instance

def selectedWeightOrbits (Φ : RootType) :
    SelectedOrbitIndex Φ → Finset (WeightLattice (rootDatum Φ).pairing) := by
  cases Φ with
  | A r hr => exact fun _ => TypeA.naturalOrbit r
  | B r hr => exact fun _ => TypeB.spinOrbit (r-1)
  | C r hr => exact fun _ => TypeC.orbit (r-1+1)
  | D r hr => exact TypeD.halfSpinOrbit (r-2)
  | E6 => exact fun _ => E6Minuscule.weights
  | E7 => exact fun _ => E7Minuscule.weights
  | E8 => exact fun a => nomatch a
  | F4 => exact fun a => nomatch a
  | G2 => exact fun a => nomatch a

theorem selectedWeightOrbits_closed (Φ : RootType) :
    ∀ a i μ, μ ∈ selectedWeightOrbits Φ a →
      weightReflection (rootDatum Φ).pairing i μ ∈ selectedWeightOrbits Φ a := by
  cases Φ with
  | A r hr => exact fun _ => TypeA.naturalOrbit_closed r
  | B r hr => exact fun _ => TypeB.spinOrbit_closed (r-1)
  | C r hr => exact fun _ => TypeC.orbit_closed
  | D r hr => exact TypeD.halfSpinOrbit_closed (r-2)
  | E6 => exact fun _ => E6Minuscule.weights_closed
  | E7 => exact fun _ => E7Minuscule.weights_closed
  | E8 => exact fun a => nomatch a
  | F4 => exact fun a => nomatch a
  | G2 => exact fun a => nomatch a

theorem selectedWeightOrbits_minuscule (Φ : RootType) :
    ∀ a μ, μ ∈ selectedWeightOrbits Φ a → ∀ i,
      μ (corootElement (rootDatum Φ).pairing i) = -1 ∨
      μ (corootElement (rootDatum Φ).pairing i) = 0 ∨
      μ (corootElement (rootDatum Φ).pairing i) = 1 := by
  cases Φ with
  | A r hr =>
    intro a μ hμ i
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hμ
    exact TypeA.naturalWeight_minuscule k i
  | B r hr =>
    intro a μ hμ i
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hμ
    exact TypeB.spinWeight_minuscule (r-1) σ i
  | C r hr =>
    intro a μ hμ i
    obtain ⟨⟨k,s⟩, _, rfl⟩ := Finset.mem_image.mp hμ
    exact TypeC.naturalWeight_minuscule k (TypeC.sign s)
      (by cases s <;> simp [TypeC.sign]) i
  | D r hr =>
    intro a μ hμ i
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hμ
    exact TypeD.spinWeight_minuscule (r-2) σ.val i
  | E6 =>
    intro a μ hμ i
    obtain ⟨k, rfl⟩ := (E6Minuscule.mem_weights μ).mp hμ
    exact E6Minuscule.all_root_grades k i
  | E7 =>
    intro a μ hμ i
    obtain ⟨k, rfl⟩ := (E7Minuscule.mem_weights μ).mp hμ
    exact E7Minuscule.all_root_grades k i
  | E8 => exact fun a => nomatch a
  | F4 => exact fun a => nomatch a
  | G2 => exact fun a => nomatch a

def selectedWeightSet (Φ : RootType) : Set (WeightLattice (rootDatum Φ).pairing) :=
  {μ | ∃ a, μ ∈ selectedWeightOrbits Φ a}

private theorem span_union_top_of_subset {V : Type*} [AddCommGroup V] [Module ℤ V]
    (q s t : Set V) (h : Submodule.span ℤ (q ∪ s) = ⊤) (hst : s ⊆ t) :
    Submodule.span ℤ (q ∪ t) = ⊤ := by
  apply top_unique
  rw [← h]
  apply Submodule.span_mono
  intro v hv
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr (hst hv)

private theorem spinWeight_mem_some_halfSpinOrbit (n : ℕ) (σ : Fin (n+2) → Bool) :
    ∃ ε, TypeD.spinWeight n σ ∈ TypeD.halfSpinOrbit n ε := by
  rcases DParity.product_cases σ with h | h
  · refine ⟨true, Finset.mem_image.mpr ⟨⟨σ, ?_⟩, Finset.mem_univ _, rfl⟩⟩
    simpa [DParity.sign] using h
  · refine ⟨false, Finset.mem_image.mpr ⟨⟨σ, ?_⟩, Finset.mem_univ _, rfl⟩⟩
    simpa [DParity.sign] using h

/-- The selected actual orbits and actual root weights span the entire weight lattice. -/
theorem selectedWeightSet_spans (Φ : RootType) :
    Submodule.span ℤ (Set.range (rootWeight (rootDatum Φ).pairing) ∪
      selectedWeightSet Φ) = ⊤ := by
  cases Φ with
  | A r hr =>
    apply span_union_top_of_subset _ _ _ (TypeA.root_and_one_weight_span r)
    rintro μ rfl
    exact ⟨(), Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  | B r hr =>
    apply span_union_top_of_subset _ _ _ (TypeB.root_and_spin_weight_span (r-1))
    rintro μ rfl
    exact ⟨(), Finset.mem_image.mpr ⟨fun _ => true, Finset.mem_univ _, rfl⟩⟩
  | C r hr =>
    apply span_union_top_of_subset _ _ _ (TypeC.root_and_one_weight_span (r-1))
    rintro μ rfl
    exact ⟨(), TypeC.naturalWeight_mem_orbit 0 1 (Or.inl rfl)⟩
  | D r hr =>
    apply span_union_top_of_subset _ _ _ (TypeD.root_and_two_spin_weights_span (r-2))
    intro μ hμ
    rcases hμ with hμ | hμ <;> subst μ
    · exact spinWeight_mem_some_halfSpinOrbit (r-2) (fun _ => true)
    · exact spinWeight_mem_some_halfSpinOrbit (r-2) (TypeD.lastNegative (r-2))
  | E6 =>
    have h : Submodule.span ℤ (Set.range (rootWeight E6Data.pairing) ∪
        {E6Minuscule.selectedWeight}) = ⊤ := by
      simpa only [Submodule.span_union, rootLattice] using E6Minuscule.rootLattice_sup_selected
    apply span_union_top_of_subset _ _ _ h
    rintro μ rfl
    exact ⟨(), (E6Minuscule.mem_weights _).mpr ⟨0, E6Minuscule.weight_zero⟩⟩
  | E7 =>
    have h : Submodule.span ℤ (Set.range (rootWeight E7Data.pairing) ∪
        {E7Minuscule.selectedWeight}) = ⊤ := by
      simpa only [Submodule.span_union, rootLattice] using E7Minuscule.rootLattice_sup_selected
    apply span_union_top_of_subset _ _ _ h
    rintro μ rfl
    exact ⟨(), (E7Minuscule.mem_weights _).mpr ⟨0, E7Minuscule.weight_zero⟩⟩
  | E8 =>
    change Submodule.span ℤ (Set.range (rootWeight E8Data.pairing) ∪ _) = ⊤
    apply top_unique
    rw [← E8Data.rootLattice_eq_top]
    exact Submodule.span_mono Set.subset_union_left
  | F4 =>
    change Submodule.span ℤ (Set.range (rootWeight F4Data.pairing) ∪ _) = ⊤
    apply top_unique
    rw [← F4Data.rootLattice_eq_top]
    exact Submodule.span_mono Set.subset_union_left
  | G2 =>
    change Submodule.span ℤ (Set.range (rootWeight G2Data.pairing) ∪ _) = ⊤
    apply top_unique
    rw [← G2Data.rootLattice_eq_top]
    exact Submodule.span_mono Set.subset_union_left

end Atlas.Chevalley
