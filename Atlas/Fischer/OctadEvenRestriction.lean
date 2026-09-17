import Atlas.Fischer.OctadShortenedCode
import Atlas.Conway.GolayOctadRestriction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Conway Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def octadWordParity (O : Octad) : (O.val → Bit) →ₗ[Bit] Bit where
  toFun w := ∑ i, w i
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' r w := by simp [Finset.mul_sum]

/-- All even functions on the actual eight retained octad coordinates. -/
def octadEvenCode (O : Octad) : Submodule Bit (O.val → Bit) := (octadWordParity O).ker

theorem octadWord_eq_supportWord (O : Octad) : (octadWord O).val=supportWord O.val := by
  funext i
  simp [octadWord_apply,supportWord]

theorem golayRestriction_even (O : Octad) (c : golay) :
    golayRestriction O.val c ∈ octadEvenCode O := by
  have hp := golay_selfOrthogonal (octadWord O).property c.val c.property
  change binaryDot c.val (octadWord O).val=0 at hp
  rw [octadWord_eq_supportWord,tetradSignParity_dot] at hp
  exact hp

/-- Restriction onto the full even code, preserving its actual coordinate values. -/
def octadEvenRestriction (O : Octad) : golay →ₗ[Bit] octadEvenCode O :=
  (golayRestriction O.val).codRestrict (octadEvenCode O) (golayRestriction_even O)

theorem octadEvenRestriction_surjective (O : Octad) :
    Function.Surjective (octadEvenRestriction O) := by
  intro x
  let w : BinaryWord := fun i => if hi : i ∈ O.val then x.val ⟨i,hi⟩ else 0
  have hw : ∑ i ∈ O.val, w i=0 := by
    rw [← Finset.sum_coe_sort]
    change (∑ i : O.val, w i.val)=0
    calc
      _ = ∑ i : O.val, x.val i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [w,dif_pos i.property]
      _ = 0 := x.property
  have hC : supportWord O.val ∈ golay := octadWord_eq_supportWord O ▸ (octadWord O).property
  obtain ⟨c,hc⟩ := golay_octad_restriction O.val (octad_size O.val O.property) hC w hw
  refine ⟨c,?_⟩
  apply Subtype.ext
  funext i
  change c.val i.val=x.val i
  have h := hc i.val i.property
  simpa only [w,dif_pos i.property] using h

theorem octadEvenRestriction_kernel (O : Octad) :
    (octadEvenRestriction O).ker=octadShortenedCode O := by
  ext c
  change (octadEvenRestriction O c=0) ↔ golayRestriction O.val c=0
  exact Subtype.ext_iff

theorem octadEvenCode_finrank (O : Octad) : Module.finrank Bit (octadEvenCode O)=7 := by
  have h := (octadEvenRestriction O).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (octadEvenRestriction_surjective O),finrank_top,
    octadEvenRestriction_kernel,octadShortenedCode_finrank,golay_finrank] at h
  omega

/-- The first quotient comparison retains the full actual octad restriction. -/
def octadShortenedQuotientEquiv (O : Octad) :
    (golay ⧸ octadShortenedCode O) ≃ₗ[Bit] octadEvenCode O :=
  (Submodule.quotEquivOfEq _ _ (octadEvenRestriction_kernel O).symm).trans
    (LinearMap.quotKerEquivOfSurjective (octadEvenRestriction O)
      (octadEvenRestriction_surjective O))

end Atlas.Fischer
