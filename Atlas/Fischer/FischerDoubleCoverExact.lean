import Atlas.Fischer.DoubleCentralizerLifting

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def doubleCoverMarkedElement (i j k : Omega) : FischerDoubleCover i j :=
  QuotientGroup.mk' (doubleCentralizerFirstKernel i j)
    (residueCocodeCentralizer {i,j} (cocodeInvolution k))

theorem doubleCoverMarkedElement_first (i j : Omega) : doubleCoverMarkedElement i j i=1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change generatedCocodeRayHom (cocodeInvolution i) ∈ residueElementary {i}
  change generatedCocodeRayHom (Multiplicative.ofAdd (coordinateCocode i)) ∈ _
  rw [generatedCocodeRayHom_coordinate]
  exact Subgroup.subset_closure ⟨i,by simp,rfl⟩

theorem doubleCoverMarkedElement_square (i j k : Omega) : doubleCoverMarkedElement i j k ^ 2=1 := by
  change (QuotientGroup.mk' (doubleCentralizerFirstKernel i j)
    (residueCocodeCentralizer {i,j} (cocodeInvolution k)))^2=1
  rw [← map_pow,← map_pow,cocodeInvolution_square,map_one,map_one]

theorem doubleCoverMarkedElement_second_order (i j : Omega) (hij : i≠j) :
    orderOf (doubleCoverMarkedElement i j j)=2 := by
  apply orderOf_eq_prime (doubleCoverMarkedElement_square i j j)
  intro h
  have hm : residueCocodeCentralizer {i,j} (cocodeInvolution j) ∈ doubleCentralizerFirstKernel i j :=
    (QuotientGroup.eq_one_iff _).mp h
  have hq : residueCocodeQuotient {i} (cocodeInvolution j)=1 :=
    (QuotientGroup.eq_one_iff _).mpr hm
  rw [residueCocodeQuotient_basic {i} j (by simpa using hij.symm)] at hq
  have he : residueDistinguishedElement {i} (doubleCoverSecondPoint i j hij)=1 := hq
  have ho := residueDistinguished_order {i} (by simp) (doubleCoverSecondPoint i j hij)
  rw [he,orderOf_one] at ho
  omega

theorem doubleCover_order (i j : Omega) (hij : i≠j) :
    Nat.card (FischerDoubleCover i j)=129123503308800 := by
  have h := (doubleCentralizerFirstKernel i j).index_mul_card
  rw [doubleCentralizerFirstKernel_card,
    markedCentralizer_pair_order {i,j} (by simp [hij])] at h
  change Nat.card (FischerDoubleCover i j)*2=258247006617600 at h
  omega

theorem doubleCoverProjection_kernel_card (i j : Omega) (hij : i≠j) :
    Nat.card (doubleCoverProjection i j).ker=2 := by
  have h := (doubleCoverProjection i j).ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr (doubleCoverProjection_surjective i j),
    Subgroup.card_top,
    residueGroup_pair_order {i,j} (by simp [hij]),doubleCover_order i j hij] at h
  omega

theorem doubleCoverProjection_second (i j : Omega) :
    doubleCoverProjection i j (doubleCoverMarkedElement i j j)=1 :=
  residueCocodeQuotient_marked {i,j} j (by simp)

/-- The kernel is the specified second involution, not merely an unspecified group of order two. -/
theorem doubleCoverProjection_kernel (i j : Omega) (hij : i≠j) :
    (doubleCoverProjection i j).ker=Subgroup.zpowers (doubleCoverMarkedElement i j j) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le.mpr (doubleCoverProjection_second i j)
  · rw [Nat.card_zpowers,doubleCoverMarkedElement_second_order i j hij,
      doubleCoverProjection_kernel_card i j hij]

theorem doubleCoverProjection_kernel_central (i j : Omega) :
    (doubleCoverProjection i j).ker ≤ Subgroup.center (FischerDoubleCover i j) := by
  intro x hx
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (doubleCentralizerFirstKernel i j) x
  have ha : a ∈ residueCentralElementary {i,j} := (QuotientGroup.eq_one_iff a).mp hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (doubleCentralizerFirstKernel i j) y
  exact congrArg (QuotientGroup.mk' (doubleCentralizerFirstKernel i j))
    (Subgroup.mem_center_iff.mp (residueCentralElementary_le_center {i,j} ha) b)

end Atlas.Fischer
