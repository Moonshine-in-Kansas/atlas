import Atlas.Rudvalis.BinaryGroupOrder
import Mathlib.Algebra.Module.ZMod

/-! Nine displayed translation matrices form a basis of the block kernel. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def nineTranslationMatrix (k : Fin 9) : BinaryMatrix :=
  fun j i => binaryLabel (![![1,2,4],![2,5,1],![5,3,2],![6,0,0],![0,0,1],
    ![5,5,5],![0,7,7],![0,4,0],![2,0,2]] k i) j

def nineTranslationInverseCode : Fin 9 → ℕ := ![273,121,106,336,108,378,363,232,289]

def nineTranslationCoefficient (k : Fin 9) (j i : Fin 3) : Bit :=
  ((nineTranslationInverseCode k / 2^(3*j.val+i.val) : ℕ) : Bit)

theorem nineTranslation_basis_certificate (j i r s : Fin 3) :
    (∑ k : Fin 9, nineTranslationCoefficient k j i * nineTranslationMatrix k r s)=
      if r=j then if s=i then 1 else 0 else 0 := by
  decide +kernel +revert

theorem nineTranslation_single (j i : Fin 3) :
    (∑ k : Fin 9, nineTranslationCoefficient k j i • nineTranslationMatrix k)=
      (Pi.single j (Pi.single i 1) : BinaryMatrix) := by
  ext r s
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  have h := nineTranslation_basis_certificate j i r s
  simpa [Pi.single_apply,ite_apply] using h

theorem binaryMatrix_single_expansion (M : BinaryMatrix) :
    (∑ j : Fin 3, ∑ i : Fin 3, M j i • (Pi.single j (Pi.single i 1) : BinaryMatrix))=M := by
  ext r s
  change (∑ j : Fin 3, ∑ i : Fin 3, M j i *
    (Pi.single j (Pi.single i 1) : BinaryMatrix) r s)=M r s
  simp [Pi.single_apply,ite_apply,mul_ite]

theorem nineTranslation_span :
    Submodule.span Bit (Set.range nineTranslationMatrix)=⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro M
  rw [← binaryMatrix_single_expansion M]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  rw [← nineTranslation_single]
  apply Submodule.sum_mem
  intro k _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩)

theorem translation_mem_of_nine (S : Subgroup binaryPermutationGroup)
    (hn : ∀ k : Fin 9,
      coordinateTranslationHom (Multiplicative.ofAdd (nineTranslationMatrix k))∈S)
    (M : BinaryMatrix) : coordinateTranslationHom (Multiplicative.ofAdd M)∈S := by
  let H : AddSubgroup BinaryMatrix := (S.comap coordinateTranslationHom).toAddSubgroup
  let V : Submodule Bit BinaryMatrix := AddSubgroup.toZModSubmodule 2 H
  have hle : Submodule.span Bit (Set.range nineTranslationMatrix)≤V := by
    apply Submodule.span_le.mpr
    rintro M ⟨k,rfl⟩
    exact hn k
  have ht : V=⊤ := top_unique (nineTranslation_span ▸ hle)
  have hm : M∈V := by rw [ht]; trivial
  exact hm

theorem binaryTranslationSubgroup_le_of_nine (S : Subgroup binaryPermutationGroup)
    (hn : ∀ k : Fin 9,
      coordinateTranslationHom (Multiplicative.ofAdd (nineTranslationMatrix k))∈S) :
    binaryTranslationSubgroup≤S := by
  rintro g ⟨M,rfl⟩
  exact translation_mem_of_nine S hn M.toAdd

theorem nineTranslation_closure :
    Subgroup.closure (Set.range (fun k : Fin 9 =>
      coordinateTranslationHom (Multiplicative.ofAdd (nineTranslationMatrix k))))=
      binaryTranslationSubgroup := by
  apply le_antisymm
  · apply (Subgroup.closure_le binaryTranslationSubgroup).mpr
    rintro g ⟨k,rfl⟩
    exact ⟨Multiplicative.ofAdd (nineTranslationMatrix k),rfl⟩
  · apply binaryTranslationSubgroup_le_of_nine
    intro k
    exact Subgroup.subset_closure ⟨k,rfl⟩

end Atlas.Rudvalis

