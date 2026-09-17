/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Codes.TetradCodeMinimum
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def tetradGluingParity (E : Submodule Bit BinaryWord) : tetradEvenSubcode E →ₗ[Bit] Bit where
  toFun w := ∑ i, tetradRemainder E w i
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum]

theorem tetradGluingParity_kernel (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    (tetradDecode E).ker ≤ (tetradGluingParity E).ker := by
  rw [tetradDecode_kernel E hE]
  rintro _ ⟨r,rfl⟩
  change ∑ i, rho r.val (hexPos i,0) = 0
  simpa [rho] using (parityCode_mem 5 r.val).mp r.prop

/-- The gluing functional descends through the precisely computed repetition kernel. -/
def tetradGluing (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    tetradHexacode E →ₗ[Bit] Bit :=
  ((tetradDecode E).ker.liftQ (tetradGluingParity E) (tetradGluingParity_kernel E hE)).comp
    (tetradQuotientEquiv E).symm.toLinearMap

theorem tetradGluing_apply (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (w : tetradEvenSubcode E) :
    tetradGluing E hE ⟨tetradDecode E w,⟨w,rfl⟩⟩ = ∑ i, tetradRemainder E w i := by
  have he := (tetradDecode E).quotKerEquivRange_symm_apply_image w
    (show tetradDecode E w ∈ (tetradDecode E).range from ⟨w,rfl⟩)
  exact congrArg ((tetradDecode E).ker.liftQ (tetradGluingParity E)
    (tetradGluingParity_kernel E hE)) he

theorem tetradGluing_mem_iff (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (h : tetradHexacode E) (r : Fin 6 → Bit) :
    jWord h.val + rho r ∈ E ↔ ∑ i, r i = tetradGluing E hE h := by
  constructor
  · intro he
    let w : tetradEvenSubcode E := ⟨⟨jWord h.val + rho r,he⟩,by
      change blockParity (jWord h.val + rho r) (0,0) = 0
      simp [blockParity,jWord,rho,Finset.sum_add_distrib]⟩
    have hd : tetradDecode E w = h.val := by
      funext i
      change blockDecode (j (h.val i) + fun _ => r (hexIndexEquiv i)) = _
      simp
    have hr : tetradRemainder E w = r := by
      funext i
      simp [tetradRemainder,w,jWord,rho]
    have hh : (⟨tetradDecode E w,⟨w,rfl⟩⟩ : tetradHexacode E) = h := Subtype.ext hd
    rw [← hh,tetradGluing_apply,hr]
  · intro hr
    obtain ⟨h,⟨w,rfl⟩⟩ := h
    rw [tetradGluing_apply] at hr
    exact tetradEven_change_constants E hE w r hr

theorem tetradGluing_represented (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    ∃ t : HexWord, ∀ h : tetradHexacode E, tetradGluing E hE h = wordPolar h.val t := by
  obtain ⟨f,hf⟩ := (tetradGluing E hE).exists_extend
  refine ⟨(wordPolar.toDual wordPolar_nondegenerate).symm f,?_⟩
  intro h
  rw [wordPolar_symmetric,LinearMap.BilinForm.apply_toDual_symm_apply]
  exact (DFunLike.congr_fun hf h).symm

end Atlas.Codes
