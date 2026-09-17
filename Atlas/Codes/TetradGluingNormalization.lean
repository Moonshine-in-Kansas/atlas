/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Codes.TetradCodeTransport

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def polarConstants (h t : HexWord) : Fin 6 → Bit :=
  fun i => polar (h (hexPos i)) (t (hexPos i))

theorem polarConstants_sum (h t : HexWord) : ∑ i, polarConstants h t i = wordPolar h t := by
  rw [wordPolar_apply]
  exact Equiv.sum_comp hexIndexEquiv.symm (fun i => polar (h i) (t i))

theorem affineTranslation_normalizes (h t : HexWord) :
    coordinatePermutation (affinePermutation t 1) (jWord h+rho (polarConstants h t)) = jWord h := by
  have he : rowEncoder h (fun i => polar (h i) (t i)) 0 = jWord h+rho (polarConstants h t) := by
    simpa [polarConstants] using rowEncoder_lift h (polarConstants h t) 0
  rw [← he,affine_encoder_transform]
  simp only [Monomial.act_one,zero_smul,add_zero]
  have hr : affineRepetition t 1 h (fun i => polar (h i) (t i)) 0 = 0 := by
    funext i
    simp only [affineRepetition,Monomial.act_one,zero_mul,add_zero]
    change polar (h i) (t i)+polar (h i) (t i) = 0
    exact bit_self_add _
  rw [hr]
  funext p
  simp [rowEncoder,jWord,j_row_polar]

/-- Local translations eliminate the gluing functional by an ambient polar representative. -/
theorem tetradGluing_normalization (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    ∃ t : HexWord, ∀ h ∈ tetradHexacode E,
      jWord h ∈ permutedBinaryCode E (affinePermutation t 1) := by
  obtain ⟨t,ht⟩ := tetradGluing_represented E hE
  refine ⟨t,?_⟩
  intro h hh
  have hm : jWord h+rho (polarConstants h t) ∈ E :=
    (tetradGluing_mem_iff E hE ⟨h,hh⟩ _).mpr (by rw [ht,polarConstants_sum])
  exact ⟨_,hm,affineTranslation_normalizes h t⟩

/-- A full code normal form is obtained by changing only the origins in its six tetrads. -/
theorem tetradCode_normalized (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    ∃ t : HexWord, ∀ w : BinaryWord,
      w ∈ permutedBinaryCode E (affinePermutation t 1) ↔
        ∃ (h : tetradHexacode E) (r : P6) (ε : Bit),
          w = jWord h.val+rho r.val+ε • eta := by
  obtain ⟨t,ht⟩ := tetradGluing_normalization E hE
  exact ⟨t,normalizedTetradCode_mem _ (permutedTetradCode E hE t 1)
    (tetradHexacode E) (tetradHexacode_selfDual E hE) ht⟩

end Atlas.Codes
