import Atlas.Fischer.ResiduePointCount
import Atlas.Fischer.ResidueAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Actual conjugation is transitive on original residue points by small-clique homogeneity. -/
theorem residuePoint_transitive (S : Finset Omega) (hS : S.card ≤ 4) :
    MulAction.IsPretransitive (residueCentralizer S) (ResiduePoint S) := by
  classical
  constructor
  intro x y
  let a := residueCoordinateEmbedding S
  let t := basicOrderedCommutingTuple a
  let u := orderedCommutingSnoc t (residuePointExtensionEquiv S x)
  let v := orderedCommutingSnoc t (residuePointExtensionEquiv S y)
  obtain ⟨g,hg⟩ := commutingTuples_homogeneous (by omega : S.card+1 ≤ 5)
    u.val v.val u.property.1 v.property.1 u.property.2 v.property.2
  have hfix : g ∈ residueCentralizer S := by
    apply (mem_markedPentadPointwise_iff S g).mpr
    intro i hi
    rw [← residueCoordinateEmbedding_image S] at hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    have hk := hg k.castSucc
    dsimp only [u,v,orderedCommutingSnoc,Function.Embedding.coeFn_mk] at hk
    simp only [Fin.snoc_castSucc] at hk
    change g * distinguishedRootElement (.inl (residueCoordinateEmbedding S k)) * g⁻¹ =
      distinguishedRootElement (.inl (residueCoordinateEmbedding S k)) at hk
    exact hk
  refine ⟨⟨g,hfix⟩,?_⟩
  apply Subtype.ext
  have hk := hg (Fin.last S.card)
  dsimp only [u,v,orderedCommutingSnoc,Function.Embedding.coeFn_mk] at hk
  simp only [Fin.snoc_last] at hk
  change g*x.val*g⁻¹=y.val at hk
  exact hk

end Atlas.Fischer
