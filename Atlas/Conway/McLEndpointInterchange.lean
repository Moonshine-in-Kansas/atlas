import Atlas.Conway.McLModel
import Atlas.GroupTheory.OrbitSection
import Atlas.LinearAlgebra.ConstantGramBound

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open Atlas.Sporadic.Conway3
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The full unordered decomposition stabilizer must move an endpoint.
Otherwise an equivariant section would give 276 doubly transitive distinct
vectors in a 24-dimensional rational space, contradicting the Gram bound. -/
theorem mcl_endpoint_not_fixed :
    ¬ ∀ g : McLPairStabilizer, g.val.val.val mclEndpoint = mclEndpoint := by
  intro hfix
  letI := finite_points
  letI := Fintype.ofFinite Points
  letI := transitive
  letI := two_transitive
  have hs : ∀ g : Model, g • basePoint = basePoint → g • mclEndpoint = mclEndpoint := by
    intro g hg
    exact hfix ⟨g,hg⟩
  obtain ⟨v,_,he,hv⟩ := Atlas.GroupTheory.exists_equivariant_map_of_stabilizer
    basePoint mclEndpoint hs
  have hp (p : Points) : p.val = {v p,vector.val-v p} := by
    obtain ⟨g,hg,hvg⟩ := hv p
    rw [hvg,← hg]
    change ({mclEndpoint,mclOtherEndpoint} : Finset leech).image g.val.val =
      {g.val.val mclEndpoint,normSixVector co3MarkedCoordinate-g.val.val mclEndpoint}
    have hx : g.val.val (normSixVector co3MarkedCoordinate) = normSixVector co3MarkedCoordinate := g.prop
    simp [mclOtherEndpoint,Finset.image_insert,Finset.image_singleton,map_sub,hx]
  have hinj : Function.Injective v := by
    intro p q h
    apply Subtype.ext
    rw [hp,hp,h]
  have hn (p : Points) : integerDot (v p).val (v p).val = 32 := by
    obtain ⟨g,_,hg⟩ := hv p
    rw [hg]
    exact (g.val.prop _ _).trans mcl_endpoint_norm
  have hcard : Fintype.card Points = 276 := by
    rw [← Nat.card_eq_fintype_card,degree]
  letI : Nontrivial Points := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨p,q,hpq⟩ := exists_pair_ne Points
  let b : ℤ := integerDot (v p).val (v q).val
  have hoff (i j : Points) (hij : i ≠ j) : integerDot (v i).val (v j).val = b := by
    obtain ⟨g,hi,hj⟩ := (MulAction.is_two_pretransitive_iff.mp
      (inferInstance : MulAction.IsMultiplyPretransitive Model Points 2)) hpq hij
    rw [← hi,← hj,he,he]
    exact g.val.prop _ _
  have hne : (32 : ℤ) ≠ b := by
    intro hb
    have hz : integerDot ((v p).val-(v q).val) ((v p).val-(v q).val) = 0 := by
      have hid : integerDot ((v p).val-(v q).val) ((v p).val-(v q).val) =
          integerDot (v p).val (v p).val + integerDot (v q).val (v q).val -
            2*integerDot (v p).val (v q).val := by
        simp only [integerDot,Pi.sub_apply,Finset.sum_add_distrib,
          Finset.sum_sub_distrib,Finset.mul_sum]
        rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring
      rw [hid,hn,hn]
      change 32+32-2*b = 0
      omega
    have hh := sub_eq_zero.mp ((integerDot_self_zero _).mp hz)
    exact hpq (hinj (Subtype.ext hh))
  have hbq : (32 : ℚ) ≠ (b : ℚ) := by exact_mod_cast hne
  have hgr (i j : Points) :
      (∑ k : Omega, ((v i).val k : ℚ) * ((v j).val k : ℚ)) =
        if i = j then 32 else (b : ℚ) := by
    have hi : integerDot (v i).val (v j).val = if i = j then 32 else b := by
      split_ifs with hij
      · subst j; exact hn i
      · exact hoff i j hij
    unfold integerDot at hi
    exact_mod_cast hi
  have hbound := Atlas.LinearAlgebra.constant_gram_card_bound
    (fun i k => ((v i).val k : ℚ)) 32 (b : ℚ) hbq hgr
  rw [hcard] at hbound
  have hd : Fintype.card Omega = 24 := by decide
  rw [hd] at hbound
  omega

end Atlas.Conway
