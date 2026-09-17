import Atlas.Fischer.ResidueOctadRelation
import Atlas.Fischer.ResidueClasses

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Inclusion of the actual double centralizer in the first centralizer. -/
def doubleCentralizerInclusion (i j : Omega) :
    residueCentralizer {i,j} →* residueCentralizer {i} :=
  Subgroup.inclusion (by
    intro x hx
    rintro y ⟨k,hk,rfl⟩
    exact hx _ ⟨k,Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hk)),rfl⟩)

theorem firstElementary_le_doubleCentralizer (i j : Omega) :
    residueElementary {i} ≤ residueCentralizer {i,j} := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨k,hk,rfl⟩
  rintro y ⟨l,hl,rfl⟩
  exact (standardCommutingFrame_isFrame.2.1 _ ⟨l,rfl⟩ _ ⟨k,rfl⟩).eq

/-- The first marked involution only, inside the actual double centralizer. -/
def doubleCentralizerFirstKernel (i j : Omega) : Subgroup (residueCentralizer {i,j}) :=
  (residueElementary {i}).subgroupOf (residueCentralizer {i,j})

theorem doubleCentralizerFirstKernel_central (i j : Omega) :
    doubleCentralizerFirstKernel i j ≤ Subgroup.center (residueCentralizer {i,j}) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  exact (residueElementary_commutes_centralizer {i} x.val hx
    (doubleCentralizerInclusion i j g)).eq.symm

instance doubleCentralizerFirstKernel_normal (i j : Omega) :
    (doubleCentralizerFirstKernel i j).Normal where
  conj_mem x hx g := by
    have hc := Subgroup.mem_center_iff.mp (doubleCentralizerFirstKernel_central i j hx) g
    have he : g*x*g⁻¹=x := by rw [hc]; group
    rw [he]
    exact hx

/-- The actual double cover kills the first marked involution, not both. -/
abbrev FischerDoubleCover (i j : Omega) :=
  residueCentralizer {i,j} ⧸ doubleCentralizerFirstKernel i j

theorem doubleCentralizerFirstKernel_le (i j : Omega) :
    doubleCentralizerFirstKernel i j ≤ residueCentralElementary {i,j} := by
  intro x hx
  change x.val ∈ residueElementary {i,j}
  apply Subgroup.closure_mono ?_ hx
  rintro y ⟨k,hk,rfl⟩
  exact ⟨k,Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hk)),rfl⟩

/-- The canonical map from the double cover onto the two-point residue. -/
def doubleCoverProjection (i j : Omega) : FischerDoubleCover i j →* ResidueGroup {i,j} :=
  QuotientGroup.lift _ (QuotientGroup.mk' (residueCentralElementary {i,j}))
    (fun x hx => (QuotientGroup.eq_one_iff x).mpr (doubleCentralizerFirstKernel_le i j hx))

theorem doubleCoverProjection_surjective (i j : Omega) :
    Function.Surjective (doubleCoverProjection i j) := by
  intro y
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (residueCentralElementary {i,j}) y
  exact ⟨QuotientGroup.mk x,rfl⟩

theorem doubleCentralizerFirstKernel_card (i j : Omega) :
    Nat.card (doubleCentralizerFirstKernel i j)=2 := by
  rw [show doubleCentralizerFirstKernel i j =
    (residueElementary {i}).subgroupOf (residueCentralizer {i,j}) from rfl,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (firstElementary_le_doubleCentralizer i j)).toEquiv,
    residueElementary_card {i} (by simp)]
  simp

end Atlas.Fischer
