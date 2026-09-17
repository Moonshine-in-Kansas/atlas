import Atlas.Conway.HSDecompositionComparison

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Sporadic.HigmanSims
open Atlas.Codes Atlas.Lattices Atlas.Conway
attribute [local instance] Classical.propDecidable

def decompositionMap : Points → Conway3.Points := hsGraphDecomposition

theorem decompositionMap_injective : Function.Injective decompositionMap := hsGraphDecomposition_injective

def decompositionSubset : Set Conway3.Points := Set.range decompositionMap

def decompositionComplement : Set Conway3.Points := decompositionSubsetᶜ

def decompositionSubsetEquiv : Points ≃ decompositionSubset := Equiv.ofInjective decompositionMap decompositionMap_injective

theorem decomposition_subset_card : Nat.card decompositionSubset = 100 := by
  rw [← Nat.card_congr decompositionSubsetEquiv,degree]

theorem decomposition_complement_card : Nat.card decompositionComplement = 176 := by
  letI := Conway3.finite_points
  have he := Set.ncard_add_ncard_compl decompositionSubset
  change Nat.card decompositionSubset + Nat.card decompositionComplement = Nat.card Conway3.Points at he
  rw [decomposition_subset_card,Conway3.degree] at he
  omega

theorem decomposition_equivariant (g : Model) (y : Points) :
    decompositionMap (g • y) = toConway3 g • decompositionMap y := hsGraphDecomposition_equivariant g y

theorem decomposition_subset_invariant (g : Model) (D : Conway3.Points) :
    toConway3 g • D ∈ decompositionSubset ↔ D ∈ decompositionSubset := by
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨g⁻¹ • y,?_⟩
    rw [decomposition_equivariant,hy,map_inv,inv_smul_smul]
  · rintro ⟨y,rfl⟩
    exact ⟨g • y,decomposition_equivariant g y⟩

theorem decomposition_complement_invariant (g : Model) (D : Conway3.Points) :
    toConway3 g • D ∈ decompositionComplement ↔ D ∈ decompositionComplement :=
  not_congr (decomposition_subset_invariant g D)

theorem decomposition_subset_pairings (D : Conway3.Points) :
    D ∈ decompositionSubset ↔ ∃ v ∈ D.val, integerDot endpoint.val v.val = 16 :=
  hs_decomposition_range_iff D

theorem decomposition_complement_pairings (D : Conway3.Points) :
    D ∈ decompositionComplement ↔ ∀ v ∈ D.val, integerDot endpoint.val v.val = 8 :=
  hs_decomposition_complement_iff D

theorem decomposition_selected_endpoint_unique (D : Conway3.Points) (hD : D ∈ decompositionSubset) :
    ∃! v : leech, v ∈ D.val ∧ integerDot endpoint.val v.val = 16 := by
  obtain ⟨y,rfl⟩ := hD
  refine ⟨y.val,⟨Finset.mem_insert_self _ _,y.prop.2.2⟩,?_⟩
  intro v hv
  have hm : v = y.val ∨ v = normSixVector co3MarkedCoordinate-y.val := by
    exact Finset.mem_insert.mp hv.1 |>.imp_right Finset.mem_singleton.mp
  rcases hm with hm | hm
  · exact hm
  · have hd := hv.2
    change integerDot hsEndpoint.val v.val = 16 at hd
    rw [hm,hs_complement_dot,y.prop.2.2] at hd
    omega

end Atlas.Sporadic.HigmanSims
