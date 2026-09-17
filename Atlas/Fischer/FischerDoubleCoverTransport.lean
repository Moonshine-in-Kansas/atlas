import Atlas.Fischer.FischerDoubleCoverCenter
import Atlas.Fischer.ResidueTransport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

private theorem residueBasicSet_pair (i j : Omega) :
    residueBasicSet {i,j}={distinguishedRootElement (.inl i),distinguishedRootElement (.inl j)} := by
  ext x
  simp [residueBasicSet]

private theorem residueBasicSet_single (i : Omega) :
    residueBasicSet {i}={distinguishedRootElement (.inl i)} := by
  ext x
  simp [residueBasicSet]

theorem doubleCover_pair_transport (i j k l : Omega) (g : rootGeneratedRayGroup)
    (hi : g*distinguishedRootElement (.inl i)*g⁻¹=distinguishedRootElement (.inl k))
    (hj : g*distinguishedRootElement (.inl j)*g⁻¹=distinguishedRootElement (.inl l)) :
    (MulAut.conj g) '' residueBasicSet {i,j}=residueBasicSet {k,l} := by
  rw [residueBasicSet_pair,residueBasicSet_pair]
  simp only [Set.image_insert_eq,Set.image_singleton,MulAut.conj_apply,hi,hj]

theorem doubleCoverFirstKernel_transport (i j k l : Omega) (g : rootGeneratedRayGroup)
    (hi : g*distinguishedRootElement (.inl i)*g⁻¹=distinguishedRootElement (.inl k))
    (hj : g*distinguishedRootElement (.inl j)*g⁻¹=distinguishedRootElement (.inl l)) :
    (doubleCentralizerFirstKernel i j).map
      (residueCentralizerTransport {i,j} {k,l} g (doubleCover_pair_transport i j k l g hi hj)).toMonoidHom =
        doubleCentralizerFirstKernel k l := by
  let e := residueCentralizerTransport {i,j} {k,l} g (doubleCover_pair_transport i j k l g hi hj)
  have hsingle : (MulAut.conj g) '' residueBasicSet {i}=residueBasicSet {k} := by
    rw [residueBasicSet_single,residueBasicSet_single]
    simpa only [Set.image_singleton,MulAut.conj_apply] using congrArg (fun x => ({x}:Set rootGeneratedRayGroup)) hi
  apply Subgroup.eq_of_le_of_card_ge
  · rintro y ⟨x,hx,rfl⟩
    change g*x.val*g⁻¹ ∈ residueElementary {k}
    rw [← residueElementary_transport {i} {k} g hsingle]
    exact ⟨x.val,hx,rfl⟩
  · rw [Nat.card_congr ((doubleCentralizerFirstKernel i j).equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm,
      doubleCentralizerFirstKernel_card,doubleCentralizerFirstKernel_card]

/-- Choice transport preserves the ordered first factor being killed. -/
def doubleCoverTransport (i j k l : Omega) (g : rootGeneratedRayGroup)
    (hi : g*distinguishedRootElement (.inl i)*g⁻¹=distinguishedRootElement (.inl k))
    (hj : g*distinguishedRootElement (.inl j)*g⁻¹=distinguishedRootElement (.inl l)) :
    FischerDoubleCover i j ≃* FischerDoubleCover k l :=
  QuotientGroup.congr _ _
    (residueCentralizerTransport {i,j} {k,l} g (doubleCover_pair_transport i j k l g hi hj))
    (doubleCoverFirstKernel_transport i j k l g hi hj)

theorem doubleCoverTransport_projection (i j k l : Omega) (g : rootGeneratedRayGroup)
    (hi : g*distinguishedRootElement (.inl i)*g⁻¹=distinguishedRootElement (.inl k))
    (hj : g*distinguishedRootElement (.inl j)*g⁻¹=distinguishedRootElement (.inl l))
    (x : FischerDoubleCover i j) :
    doubleCoverProjection k l (doubleCoverTransport i j k l g hi hj x)=
      residueQuotientTransport {i,j} {k,l} g (doubleCover_pair_transport i j k l g hi hj)
        (doubleCoverProjection i j x) := by
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (doubleCentralizerFirstKernel i j) x
  rfl

/-- Ordered transport carries the surviving central involution to the surviving one. -/
theorem doubleCoverTransport_second (i j k l : Omega) (g : rootGeneratedRayGroup)
    (hi : g*distinguishedRootElement (.inl i)*g⁻¹=distinguishedRootElement (.inl k))
    (hj : g*distinguishedRootElement (.inl j)*g⁻¹=distinguishedRootElement (.inl l)) :
    doubleCoverTransport i j k l g hi hj (doubleCoverMarkedElement i j j)=
      doubleCoverMarkedElement k l l := by
  change QuotientGroup.mk' (doubleCentralizerFirstKernel k l)
    (residueCentralizerTransport {i,j} {k,l} g (doubleCover_pair_transport i j k l g hi hj)
      (residueCocodeCentralizer {i,j} (cocodeInvolution j))) = _
  apply congrArg (QuotientGroup.mk' (doubleCentralizerFirstKernel k l))
  apply Subtype.ext
  change g*generatedCocodeRayHom (cocodeInvolution j)*g⁻¹=
    generatedCocodeRayHom (cocodeInvolution l)
  simpa only [cocodeInvolution,generatedCocodeRayHom_coordinate] using hj

/-- The double-cover action is the restriction of the original singleton-residue action. -/
def doubleCoverOriginalAction (i j : Omega) (hij : i≠j) :
    FischerDoubleCover i j →* Equiv.Perm (ResiduePoint {i}) :=
  (MulAction.toPermHom (ResidueGroup {i}) (ResiduePoint {i})).comp
    ((doubleCoverCentralizerTarget i j hij).subtype.comp
      (doubleCoverCentralizerEquiv i j hij).toMonoidHom)

theorem doubleCoverOriginalAction_mk (i j : Omega) (hij : i≠j)
    (a : residueCentralizer {i,j}) (x : ResiduePoint {i}) :
    (doubleCoverOriginalAction i j hij (QuotientGroup.mk' (doubleCentralizerFirstKernel i j) a) x).val=
      a.val*x.val*a.val⁻¹ :=
  residueGroup_mk_smul_val {i} (doubleCentralizerInclusion i j a) x

theorem doubleCoverOriginalAction_faithful (i j : Omega) (hij : i≠j) :
    Function.Injective (doubleCoverOriginalAction i j hij) := by
  letI := residueGroup_faithful {i} (by simp)
  exact (MulAction.toPerm_injective).comp
    (Subtype.val_injective.comp (doubleCoverCentralizerEquiv i j hij).injective)

end Atlas.Fischer
