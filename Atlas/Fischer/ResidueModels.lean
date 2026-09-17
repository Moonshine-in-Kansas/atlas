import Atlas.Fischer.MarkedPentadFrameAction
import Atlas.Fischer.BasicFramePointwiseKernel

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The specified actual basic distinguished elements. -/
def residueBasicSet (S : Finset Omega) : Set rootGeneratedRayGroup :=
  (fun i : Omega => distinguishedRootElement (.inl i)) '' (S : Set Omega)

abbrev residueCentralizer (S : Finset Omega) := markedPentadPointwise S

def residueElementary (S : Finset Omega) : Subgroup rootGeneratedRayGroup :=
  Subgroup.closure (residueBasicSet S)

def residueCentralElementary (S : Finset Omega) : Subgroup (residueCentralizer S) :=
  (residueElementary S).subgroupOf (residueCentralizer S)

/-- Original distinguished elements; no quotient images enter the point model. -/
def ResiduePoint (S : Finset Omega) :=
  {x : rootGeneratedRayGroup // x ∈ Set.range distinguishedRootElement ∧
    x ∉ residueBasicSet S ∧ ∀ i ∈ S, Commute (distinguishedRootElement (.inl i)) x}

theorem residueElementary_le_centralizer (S : Finset Omega) :
    residueElementary S ≤ residueCentralizer S := by
  change Subgroup.closure (residueBasicSet S) ≤ residueCentralizer S
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i,hi,rfl⟩
  rintro y ⟨j,hj,rfl⟩
  exact (standardCommutingFrame_isFrame.2.1 _ ⟨j,rfl⟩ _ ⟨i,rfl⟩).eq

theorem residueElementary_commutes_centralizer (S : Finset Omega)
    (x : rootGeneratedRayGroup) (hx : x ∈ residueElementary S)
    (g : residueCentralizer S) : Commute x g.val := by
  have h : residueElementary S ≤ Subgroup.centralizer (residueCentralizer S : Set rootGeneratedRayGroup) :=
    Subgroup.closure_le_centralizer_centralizer (residueBasicSet S)
  exact (h hx g.val g.property).symm

theorem residueCentralElementary_le_center (S : Finset Omega) :
    residueCentralElementary S ≤ Subgroup.center (residueCentralizer S) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact (residueElementary_commutes_centralizer S x.val hx g).eq.symm

instance residueCentralElementary_normal (S : Finset Omega) :
    (residueCentralElementary S).Normal := by
  constructor
  intro n hn g
  have hc := (Subgroup.mem_center_iff.mp (residueCentralElementary_le_center S hn)) g
  have he : g*n*g⁻¹=n := by rw [hc]; group
  rw [he]
  exact hn

end Atlas.Fischer
