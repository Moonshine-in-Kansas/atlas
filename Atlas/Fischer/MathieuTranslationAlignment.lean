import Atlas.Fischer.OctadAvoidance
import Atlas.GroupTheory.FinitePartialTransport
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Actual octad translations containing S, inside the retained Mathieu group. -/
def octadTranslationGenerators (S : Finset Omega) : Set Mathieu24CodeModel :=
  {g | ∃ O : Octad, S ⊆ O.val ∧ ∃ t : mathieuOctadPointwise O, octadPointwiseEmbedding O t=g}

def mathieuTranslationGenerated (S : Finset Omega) : Subgroup Mathieu24CodeModel :=
  Subgroup.closure (octadTranslationGenerators S)

theorem mathieuTranslationGenerated_le_fixing (S : Finset Omega) :
    mathieuTranslationGenerated S ≤ fixingSubgroup Mathieu24CodeModel (S : Set Omega) := by
  rw [mathieuTranslationGenerated,Subgroup.closure_le]
  rintro g ⟨O,hSO,t,rfl⟩ i
  exact octadPointwiseEmbedding_fixes O t i.val (hSO i.prop)

theorem mathieuTranslationGenerated_local (S T : Finset Omega) (hST : S ⊆ T) (hT : T.card ≤ 4)
    (x y : Omega) (hx : x ∉ T) (hy : y ∉ T) :
    ∃ r : mathieuTranslationGenerated S, r.val.val x=y ∧ ∀ i ∈ T, r.val.val i=i := by
  obtain ⟨O,g,hTO,hg,hfix⟩ := octad_translation_align T hT x y hx hy
  have hm : octadPointwiseEmbedding O g ∈ mathieuTranslationGenerated S :=
    Subgroup.subset_closure ⟨O,hST.trans hTO,g,rfl⟩
  exact ⟨⟨octadPointwiseEmbedding O g,hm⟩,hg,hfix⟩

/-- The generated translations match any ambient pointwise-S permutation on
any at most five points containing S. -/
theorem mathieuTranslationGenerated_match (S P : Finset Omega) (hSP : S ⊆ P) (hP : P.card ≤ 5)
    (g : Mathieu24CodeModel) (hg : ∀ i ∈ S, g.val i=i) :
    ∃ r : mathieuTranslationGenerated S, ∀ i ∈ P, r.val.val i=g.val i := by
  have he : S ∪ (P \ S)=P := Finset.union_sdiff_of_subset hSP
  have hd : Disjoint S (P \ S) := Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)
  obtain ⟨r,hr⟩ := Atlas.GroupTheory.finite_partial_match (mathieuTranslationGenerated S) S 4
    (fun T hST hT x y hx hy => mathieuTranslationGenerated_local S T hST hT x y hx hy)
    g hg (P \ S) hd (by rw [he]; exact hP)
  refine ⟨r,?_⟩
  intro i hi
  exact hr i (he.symm ▸ hi)

/-- The source factorization M=R M_(P), with actual coordinate permutations. -/
theorem mathieuTranslationGenerated_factorization (S P : Finset Omega)
    (hSP : S ⊆ P) (hP : P.card ≤ 5) (g : Mathieu24CodeModel)
    (hg : ∀ i ∈ S, g.val i=i) :
    ∃ r : mathieuTranslationGenerated S,
      ∃ k : fixingSubgroup Mathieu24CodeModel (P : Set Omega), g=r.val*k.val := by
  obtain ⟨r,hr⟩ := mathieuTranslationGenerated_match S P hSP hP g hg
  have hk : r.val⁻¹*g ∈ fixingSubgroup Mathieu24CodeModel (P : Set Omega) := by
    intro i
    change r.val.val⁻¹ (g.val i.val)=i.val
    rw [← hr i.val i.prop,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
  refine ⟨r,⟨r.val⁻¹*g,hk⟩,?_⟩
  simp

abbrev MathieuTranslationPoints (S : Finset Omega) :=
  SubMulAction.ofFixingSubgroup Mathieu24CodeModel (S : Set Omega)

def mathieuTranslationFixerHom (S : Finset Omega) : mathieuTranslationGenerated S →*
    fixingSubgroup Mathieu24CodeModel (S : Set Omega) :=
  Subgroup.inclusion (mathieuTranslationGenerated_le_fixing S)

instance mathieuTranslationPointsAction (S : Finset Omega) :
    MulAction (mathieuTranslationGenerated S) (MathieuTranslationPoints S) :=
  MulAction.compHom _ (mathieuTranslationFixerHom S)

/-- The source's full ordered-tuple transitivity, on the actual complement. -/
theorem mathieuTranslationGenerated_multipleTransitive (S : Finset Omega) (hS : S.card ≤ 5) :
    MulAction.IsMultiplyPretransitive (mathieuTranslationGenerated S)
      (MathieuTranslationPoints S) (5-S.card) := by
  classical
  letI := mathieu24_five_transitive
  letI : MulAction.IsMultiplyPretransitive
      (fixingSubgroup Mathieu24CodeModel (S : Set Omega))
      (MathieuTranslationPoints S) (5-S.card) :=
    SubMulAction.ofFixingSubgroup.isMultiplyPretransitive Mathieu24CodeModel (n := 5) (S : Set Omega)
      (by simp only [Set.ncard_coe_finset]; omega)
  constructor
  intro e f
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq
    (fixingSubgroup Mathieu24CodeModel (S : Set Omega)) e f
  let P := S ∪ Finset.univ.image (fun k => (e k).val)
  have hP : P.card ≤ 5 := by
    have h := Finset.card_union_le S (Finset.univ.image (fun k => (e k).val))
    have hh := Finset.card_image_le (s := Finset.univ) (f := fun k => (e k).val)
    simp only [Finset.card_univ,Fintype.card_fin] at hh
    change P.card ≤ _ at h
    omega
  obtain ⟨r,hr⟩ := mathieuTranslationGenerated_match S P Finset.subset_union_left hP g.val
    (fun i hi => g.prop ⟨i,hi⟩)
  refine ⟨r,?_⟩
  apply Function.Embedding.ext
  intro k
  apply Subtype.ext
  change r.val.val (e k).val=(f k).val
  have hk := congrArg (fun t => (t k).val) hg
  change g.val.val (e k).val=(f k).val at hk
  exact (hr _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,by simp,rfl⟩))).trans hk

end Atlas.Fischer
