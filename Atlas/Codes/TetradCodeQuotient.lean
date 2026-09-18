/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Codes.TetradCodeParity

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

/-- Simultaneous quotient maps of the six even tetrads. -/
def tetradDecode (E : Submodule Bit BinaryWord) : tetradEvenSubcode E →ₗ[Bit] HexWord where
  toFun w i := blockDecode (fun k => w.val.val (i,k))
  map_add' := by intros; funext i; exact map_add blockDecode _ _
  map_smul' := by intros; funext i; exact map_smul blockDecode _ _

def tetradHexacode (E : Submodule Bit BinaryWord) : Submodule Bit HexWord := (tetradDecode E).range

def tetradConstants (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    P6 →ₗ[Bit] tetradEvenSubcode E where
  toFun r := ⟨⟨rho r.val,hE.repetitions ⟨r.val,r.prop,rfl⟩⟩,by
    change blockParity (rho r.val) (0,0) = 0
    simp [blockParity,rho]⟩
  map_add' := by intros; apply Subtype.ext; apply Subtype.ext; exact map_add rho _ _
  map_smul' := by intros; apply Subtype.ext; apply Subtype.ext; exact map_smul rho _ _

theorem tetradConstants_injective (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    Function.Injective (tetradConstants E hE) := by
  intro r s he
  apply Subtype.ext
  funext i
  simpa [tetradConstants,rho] using congrArg (fun w : tetradEvenSubcode E => w.val.val (hexPos i,0)) he

theorem tetradDecode_kernel (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    (tetradDecode E).ker = (tetradConstants E hE).range := by
  ext w
  constructor
  · intro hw
    let r : Fin 6 → Bit := fun i => w.val.val (hexPos i,0)
    have he : w.val.val = rho r := by
      funext p
      obtain ⟨i,k⟩ := p
      have hb := even_block_decomposition (fun k => w.val.val (i,k))
        ((tetradEvenSubcode_mem E hE w.val).mp w.prop i)
      have hz : blockDecode (fun k => w.val.val (i,k)) = 0 := congrFun hw i
      rw [hz,map_zero,zero_add] at hb
      simpa [rho,r] using congrFun hb k
    have hr : r ∈ P6 := (tetradCode_repetition_mem E hE r).mp (he ▸ w.val.prop)
    exact ⟨⟨r,hr⟩,Subtype.ext (Subtype.ext he.symm)⟩
  · rintro ⟨r,rfl⟩
    apply funext
    intro i
    exact blockDecode_constant _

def tetradQuotientEquiv (E : Submodule Bit BinaryWord) :
    (tetradEvenSubcode E ⧸ (tetradDecode E).ker) ≃ₗ[Bit] tetradHexacode E :=
  (tetradDecode E).quotKerEquivRange

theorem tetradDecode_kernel_finrank (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    Module.finrank Bit (tetradDecode E).ker = 5 := by
  rw [tetradDecode_kernel E hE,LinearMap.finrank_range_of_inj (tetradConstants_injective E hE)]
  exact parityCode_finrank 5

theorem tetradHexacode_finrank (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    Module.finrank Bit (tetradHexacode E) = 6 := by
  have hd := (tetradDecode E).finrank_range_add_finrank_ker
  rw [tetradDecode_kernel_finrank E hE,tetradEvenSubcode_finrank E hE] at hd
  have hd' : Module.finrank Bit (tetradHexacode E) + 5 = 11 := hd
  omega

theorem tetradDecode_polar (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (w z : tetradEvenSubcode E) :
    wordPolar (tetradDecode E w) (tetradDecode E z) = binaryDot w.val.val z.val.val := by
  rw [wordPolar_apply,binaryDot_apply]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact (evenBlock_polar _ _ ((tetradEvenSubcode_mem E hE w.val).mp w.prop i)
    ((tetradEvenSubcode_mem E hE z.val).mp z.prop i)).symm

theorem tetradHexacode_selfDual (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    tetradHexacode E = dual (tetradHexacode E) := by
  apply selfDual_of_half_dimension wordPolar wordPolar_nondegenerate
  · rintro _ ⟨w,rfl⟩ _ ⟨z,rfl⟩
    rw [tetradDecode_polar E hE]
    exact tetradCode_orthogonal E hE z.val w.val
  · rw [tetradHexacode_finrank E hE]
    change 2 * 6 = Module.finrank Bit (HexIndex → Bit × Bit)
    rw [Module.finrank_pi_fintype]
    simp [HexIndex,Module.finrank_prod]

end Atlas.Codes
