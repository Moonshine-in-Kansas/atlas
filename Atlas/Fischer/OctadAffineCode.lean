import Atlas.Fischer.OctadAffineEvaluations
import Mathlib.LinearAlgebra.Dimension.Free

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

abbrev OctadTranslationSpace (O : Octad) := (octadDualConstant O).ker

def octadAffineOrigin (O : Octad) : OctadAffineHyperplane O :=
  octadAffineEvaluation O (Classical.arbitrary _)

/-- The affine hyperplane is a torsor over its actual four-dimensional direction space. -/
def octadHyperplaneCoordinates (O : Octad) : OctadTranslationSpace O ≃ OctadAffineHyperplane O where
  toFun v := ⟨(octadAffineOrigin O).val + v.val, by
    rw [map_add, (octadAffineOrigin O).prop, v.prop, add_zero]⟩
  invFun l := ⟨l.val - (octadAffineOrigin O).val, by
    change octadDualConstant O (l.val - (octadAffineOrigin O).val) = 0
    rw [map_sub, l.prop, (octadAffineOrigin O).prop, sub_self]⟩
  left_inv v := by apply Subtype.ext; dsimp; abel
  right_inv l := by apply Subtype.ext; dsimp; abel

/-- A basis labels the actual affine direction space by four binary coordinates. -/
def octadDirectionCoordinates (O : Octad) : OctadTranslationSpace O ≃ₗ[Bit] (Fin 4 → Bit) :=
  (Module.finBasisOfFinrankEq Bit (OctadTranslationSpace O)
    (octadDualConstant_kernel_finrank O)).equivFun

/-- A concrete coordinate labelling of the retained octad complement. -/
def octadExteriorCoordinates (O : Octad) : OctadExterior O ≃ (Fin 4 → Bit) :=
  (octadAffineEvaluationEquiv O).trans
    ((octadHyperplaneCoordinates O).symm.trans (octadDirectionCoordinates O).toEquiv)

/-- Actual shortened words, read in the constructed affine coordinates. -/
def octadAffineWord (O : Octad) : octadShortenedCode O →ₗ[Bit] ((Fin 4 → Bit) → Bit) where
  toFun c v := c.val.val ((octadExteriorCoordinates O).symm v).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- First-order Reed--Muller code as all affine functions on four binary coordinates. -/
def binaryAffineCodeFour : Submodule Bit ((Fin 4 → Bit) → Bit) where
  carrier := {w | ∃ a : Bit, ∃ l : (Fin 4 → Bit) →ₗ[Bit] Bit, ∀ v, w v = a + l v}
  zero_mem' := ⟨0, 0, fun _ => (add_zero _).symm⟩
  add_mem' := by
    rintro w z ⟨a,l,hl⟩ ⟨b,m,hm⟩
    refine ⟨a+b,l+m,?_⟩
    intro v
    change w v + z v = _
    rw [hl,hm]
    change a + l v + (b + m v) = a+b+(l v+m v)
    abel
  smul_mem' := by
    rintro r w ⟨a,l,hl⟩
    refine ⟨r*a,r • l,?_⟩
    intro v
    change r * w v = r*a+r*l v
    rw [hl,mul_add]

theorem octadAffineWord_formula (O : Octad) (c : octadShortenedCode O) (v : Fin 4 → Bit) :
    octadAffineWord O c v = (octadAffineOrigin O).val c +
      ((octadDirectionCoordinates O).symm v).val c := by
  have h := octadAffineEvaluation_word O c ((octadExteriorCoordinates O).symm v)
  change c.val.val ((octadExteriorCoordinates O).symm v).val = _
  rw [← h]
  simp [octadExteriorCoordinates, octadHyperplaneCoordinates]

theorem octadAffineWord_mem (O : Octad) (c : octadShortenedCode O) :
    octadAffineWord O c ∈ binaryAffineCodeFour := by
  refine ⟨(octadAffineOrigin O).val c,
    (LinearMap.applyₗ' Bit c).comp
      ((octadDualConstant O).ker.subtype.comp (octadDirectionCoordinates O).symm.toLinearMap), ?_⟩
  exact octadAffineWord_formula O c

/-- Every affine function arises from an actual shortened Golay word.
The extension uses linear duality; no code recognition by numerical parameters is used. -/
theorem octadAffineWord_range (O : Octad) : (octadAffineWord O).range = binaryAffineCodeFour := by
  apply le_antisymm
  · rintro w ⟨c,rfl⟩
    exact octadAffineWord_mem O c
  · rintro w ⟨a,l,hl⟩
    let m : Module.Dual Bit (OctadTranslationSpace O) := l.comp (octadDirectionCoordinates O).toLinearMap
    obtain ⟨L,hL⟩ := LinearMap.dualMap_surjective_of_injective
      (octadDualConstant O).ker.injective_subtype m
    let c : octadShortenedCode O := (Module.evalEquiv Bit (octadShortenedCode O)).symm L
    let b : Bit := a - (octadAffineOrigin O).val c
    let d : octadShortenedCode O := c + b • octadShortenedOne O
    refine ⟨d,?_⟩
    funext v
    rw [octadAffineWord_formula]
    have hv : ((octadDirectionCoordinates O).symm v).val (octadShortenedOne O) = 0 :=
      ((octadDirectionCoordinates O).symm v).prop
    have ho : (octadAffineOrigin O).val (octadShortenedOne O) = 1 :=
      (octadAffineOrigin O).prop
    have hm : ((octadDirectionCoordinates O).symm v).val c = l v := by
      have hh := LinearMap.congr_fun hL ((octadDirectionCoordinates O).symm v)
      simpa [c,m] using hh
    change (octadAffineOrigin O).val (c + b • octadShortenedOne O) +
      ((octadDirectionCoordinates O).symm v).val (c + b • octadShortenedOne O) = w v
    rw [map_add,map_smul,map_add,map_smul,ho,hv,hm,hl]
    dsimp [b]
    simp only [smul_eq_mul,mul_one,mul_zero,add_zero]
    ring

end Atlas.Fischer
