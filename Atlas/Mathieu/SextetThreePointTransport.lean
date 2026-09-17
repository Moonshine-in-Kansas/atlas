import Atlas.Mathieu.SextetTwoPointTransport
import Atlas.Codes.HexacodeUniqueness

noncomputable section
namespace Atlas.Codes

theorem sextet_three_point_transport (σ : Equiv.Perm HexIndex) (a b : Fin 3 → Omega)
    (hb : Function.Injective (fun j => (b j).1))
    (ha : ∀ j, σ (a j).1 = (b j).1) :
    ∃ s : SextetStabilizer, (∀ i k, (s.val.val (i,k)).1 = σ i) ∧
      ∀ j, s.val.val (a j) = b j := by
  obtain ⟨g,hg⟩ := hexCoordinateHom_surjective σ
  have hp : ∀ i, g.val.perm i = σ i := fun i => DFunLike.congr_fun hg i
  let e : Fin 3 ↪ HexIndex := ⟨fun j => (b j).1,hb⟩
  obtain ⟨t,ht⟩ := (codeTripleProjection_bijective hexacode hexacode_isHexMDS e).2
    (fun j => rowLabel (b j).2-g.val.localMap (b j).1 (rowLabel (a j).2))
  have htj (j : Fin 3) : t.val (b j).1 =
      rowLabel (b j).2-g.val.localMap (b j).1 (rowLabel (a j).2) := congrFun ht j
  refine ⟨sextetAffineEquiv ⟨Multiplicative.ofAdd t,g⟩,?_,?_⟩
  · intro i k
    rw [sextetAffineEquiv_coordinates]
    exact hp i
  · intro j
    change (g.val.perm (a j).1,rowLabel.symm
      (g.val.localMap (g.val.perm (a j).1) (rowLabel (a j).2)+t.val (g.val.perm (a j).1))) = b j
    rw [hp,ha,htj,add_sub_cancel,rowLabel.symm_apply_apply]

end Atlas.Codes
