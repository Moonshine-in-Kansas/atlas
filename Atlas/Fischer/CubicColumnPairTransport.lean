import Atlas.Fischer.CountingCanonicalTriangles
import Atlas.Mathieu.SextetColumnPairTransport
import Atlas.Mathieu.OctadExteriorTransitivity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Every permutation of the six actual sextet columns lifts through the
retained hexacode automorphism group to an actual Mathieu symmetry. -/
theorem cubicSextet_column_permutation (σ : Equiv.Perm HexIndex) :
    ∃ g : Mathieu24CodeModel, ∀ i, permuteBlock g.val (tetrad i) = tetrad (σ i) := by
  obtain ⟨h,hh⟩ := hexCoordinateHom_surjective σ
  let s : SextetStabilizer := sextetAffineEquiv ⟨Multiplicative.ofAdd 0,h⟩
  have hs (i : HexIndex) (k : Fin 4) : (s.val.val (i,k)).1 = σ i := by
    rw [sextetAffineEquiv_coordinates]
    exact DFunLike.congr_fun hh i
  exact ⟨s.val,fun i => sextet_tetrad_transport s σ hs i⟩

 theorem cubicColumnPair_permute (g : Mathieu24CodeModel) (σ : Equiv.Perm HexIndex)
    (hg : ∀ i, permuteBlock g.val (tetrad i) = tetrad (σ i)) (i j : HexIndex) :
    permuteBlock g.val (tetrad i ∪ tetrad j) = tetrad (σ i) ∪ tetrad (σ j) := by
  change (tetrad i ∪ tetrad j).image g.val = _
  rw [Finset.image_union]
  change permuteBlock g.val (tetrad i) ∪ permuteBlock g.val (tetrad j) = _
  rw [hg,hg]

 theorem cubicHexTriple_injective (i j k : HexIndex) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (![i,j,k] : Fin 3 → HexIndex) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

 theorem cubicColumnSextetPair_canonical (i j k : HexIndex)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ g : Mathieu24CodeModel,
      permuteBlock g.val (tetrad i ∪ tetrad j) = countingCanonicalD.val ∧
      permuteBlock g.val (tetrad i ∪ tetrad k) = countingCanonicalSextetE.val := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair
    (![i,j,k] : Fin 3 → HexIndex) (![hexPos 0,hexPos 1,hexPos 2] : Fin 3 → HexIndex)
    (cubicHexTriple_injective i j k hij hik hjk) (by decide)
  obtain ⟨g,hg⟩ := cubicSextet_column_permutation σ
  have hi : σ i = hexPos 0 := hσ 0
  have hj : σ j = hexPos 1 := hσ 1
  have hk : σ k = hexPos 2 := hσ 2
  refine ⟨g,?_,?_⟩ <;> rw [cubicColumnPair_permute g σ hg]
  · rw [hi,hj,countingCanonicalD,countingColumnPairOctad_val]
  · rw [hi,hk,countingCanonicalSextetE,countingColumnPairOctad_val]

 theorem cubicColumnTrioPair_canonical (i j k l : HexIndex)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) (hkl : k ≠ l) :
    ∃ g : Mathieu24CodeModel,
      permuteBlock g.val (tetrad i ∪ tetrad j) = countingCanonicalD.val ∧
      permuteBlock g.val (tetrad k ∪ tetrad l) = countingCanonicalTrioE.val := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair
    (![i,j,k,l] : Fin 4 → HexIndex)
    (![hexPos 0,hexPos 1,hexPos 2,hexPos 3] : Fin 4 → HexIndex)
    (hexQuad_injective i j k l hij hki hkj hli hlj hkl) (by decide)
  obtain ⟨g,hg⟩ := cubicSextet_column_permutation σ
  have hi : σ i = hexPos 0 := hσ 0
  have hj : σ j = hexPos 1 := hσ 1
  have hk : σ k = hexPos 2 := hσ 2
  have hl : σ l = hexPos 3 := hσ 3
  refine ⟨g,?_,?_⟩ <;> rw [cubicColumnPair_permute g σ hg]
  · rw [hi,hj,countingCanonicalD,countingColumnPairOctad_val]
  · rw [hk,hl,countingCanonicalTrioE,countingColumnPairOctad_val]

end Atlas.Fischer
