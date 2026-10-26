import Atlas.LinearGroups.F4.CoordinateCycleGenerated
import Atlas.LinearGroups.F4.ParabolicMarkedPoint
import Atlas.LinearGroups.F4.OppositeCrossMarked
import Atlas.GroupTheory.PrimitivePointChains

/-! Two explicit stabilizer moves escape the canonical near pair (C₀,A₀).
The first fixes C₀ and sends A₀ to B₄; the second fixes A₀ and sends B₄ to C₇.
Only four actual signed basis columns are checked. This does not assert a
reduction of arbitrary near pairs to this marked pair. -/
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
noncomputable section
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

def canonicalNearFirst : Model F := shortWeylFirstPair 3*shortWeylFirstPair 2*shortWeylFirstPair 1
def canonicalNearSecond : Model F := coordinateCycle^2*canonicalNearFirst*coordinateCycle

private def nearFirstDestination (j : Fin 27) : Fin 27 :=
  shortWeylDestination 3 (shortWeylDestination 2 (shortWeylDestination 1 j))
private def nearFirstSign (j : Fin 27) : ℤ :=
  shortWeylSign 1 j*shortWeylSign 2 (shortWeylDestination 1 j)*
    shortWeylSign 3 (shortWeylDestination 2 (shortWeylDestination 1 j))

attribute [local irreducible] shortWeylFirstPair coordinateCycle

private theorem canonicalNearFirst_basis (j : Fin 27) :
    (canonicalNearFirst (F:=F)).val (basisVector (albertCoordinateOfFin j))=
      (nearFirstSign j:F) • basisVector (albertCoordinateOfFin (nearFirstDestination j)) := by
  change (shortWeylFirstPair 3).val ((shortWeylFirstPair 2).val
    ((shortWeylFirstPair 1).val (basisVector (albertCoordinateOfFin j))))=_
  simp only [shortWeylFirstPair_basis,map_smul]
  simp only [nearFirstSign,nearFirstDestination,Int.cast_mul,smul_smul,mul_assoc]

attribute [local irreducible] canonicalNearFirst

private theorem nearCycle_basis (j : Fin 27) :
    (coordinateCycle (F:=F)).val (basisVector (albertCoordinateOfFin j))=
      basisVector (albertCoordinateOfFin (coordinateCycleDestination j)) :=
by
  rw [coordinateCycle_apply]
  exact coordinateCycle_basis j

private theorem canonicalNearSecond_basis (j : Fin 27) :
    (canonicalNearSecond (F:=F)).val (basisVector (albertCoordinateOfFin j))=
      (nearFirstSign (coordinateCycleDestination j):F) • basisVector (albertCoordinateOfFin
        (coordinateCycleDestination (coordinateCycleDestination
          (nearFirstDestination (coordinateCycleDestination j))))) := by
  change (coordinateCycle (F:=F)).val ((coordinateCycle (F:=F)).val
    ((canonicalNearFirst (F:=F)).val ((coordinateCycle (F:=F)).val (basisVector (albertCoordinateOfFin j)))))=_
  simp only [nearCycle_basis,canonicalNearFirst_basis,map_smul]

private theorem nearFirst_C0_column :
    (canonicalNearFirst (F:=F)).val (basisVector (albertCoordinateOfFin 19))=
      basisVector (albertCoordinateOfFin 19) := by
  rw [canonicalNearFirst_basis]
  have hs : nearFirstSign 19=1 := by decide +kernel
  have hd : nearFirstDestination 19=19 := by decide +kernel
  rw [hs,hd]
  simp

private theorem nearFirst_A0_column :
    (canonicalNearFirst (F:=F)).val (basisVector (albertCoordinateOfFin 3))=
      basisVector (albertCoordinateOfFin 15) := by
  rw [canonicalNearFirst_basis]
  have hs : nearFirstSign 3=1 := by decide +kernel
  have hd : nearFirstDestination 3=15 := by decide +kernel
  rw [hs,hd]
  simp

private theorem nearSecond_A0_column :
    (canonicalNearSecond (F:=F)).val (basisVector (albertCoordinateOfFin 3))=
      basisVector (albertCoordinateOfFin 3) := by
  rw [canonicalNearSecond_basis]
  have hs : nearFirstSign (coordinateCycleDestination 3)=1 := by decide +kernel
  have hd : coordinateCycleDestination (coordinateCycleDestination
      (nearFirstDestination (coordinateCycleDestination 3)))=3 := by decide +kernel
  rw [hs,hd]
  simp

private theorem nearSecond_B4_column :
    (canonicalNearSecond (F:=F)).val (basisVector (albertCoordinateOfFin 15))=
      basisVector (albertCoordinateOfFin 26) := by
  rw [canonicalNearSecond_basis]
  have hs : nearFirstSign (coordinateCycleDestination 15)=1 := by decide +kernel
  have hd : coordinateCycleDestination (coordinateCycleDestination
      (nearFirstDestination (coordinateCycleDestination 15)))=26 := by decide +kernel
  rw [hs,hd]
  simp

theorem canonicalNearFirst_fixes_C0 : (canonicalNearFirst (F:=F)).val parabolicVector=parabolicVector := by
  have hb : (basisVector (albertCoordinateOfFin 19) : Carrier F)=parabolicVector := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [basisVector,albertCoordinateOfFin,parabolicVector,Pi.single_apply]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [basisVector,albertCoordinateOfFin,parabolicVector,Pi.single_apply]
  simpa only [hb] using nearFirst_C0_column (F:=F)

theorem canonicalNearFirst_A0 : (canonicalNearFirst (F:=F)).val (basisVector (.inr (0,0)))=
    basisVector (.inr (1,4)) := by
  exact nearFirst_A0_column (F:=F)

theorem canonicalNearSecond_fixes_A0 :
    (canonicalNearSecond (F:=F)).val (basisVector (.inr (0,0)))=basisVector (.inr (0,0)) := by
  exact nearSecond_A0_column (F:=F)

theorem canonicalNearSecond_B4 : (canonicalNearSecond (F:=F)).val (basisVector (.inr (1,4)))=
    basisVector (.inr (2,7)) := by
  exact nearSecond_B4_column (F:=F)

theorem canonicalNearFirst_mem_rootGenerated : canonicalNearFirst (F:=F)∈rootGenerated := by
  unfold canonicalNearFirst
  exact (rootGenerated (F:=F)).mul_mem ((rootGenerated (F:=F)).mul_mem
    (shortWeylFirstPair_mem_rootGenerated 3) (shortWeylFirstPair_mem_rootGenerated 2))
    (shortWeylFirstPair_mem_rootGenerated 1)

theorem canonicalNearSecond_mem_rootGenerated : canonicalNearSecond (F:=F)∈rootGenerated :=
  (rootGenerated (F:=F)).mul_mem ((rootGenerated (F:=F)).mul_mem
    ((rootGenerated (F:=F)).pow_mem coordinateCycle_mem_rootGenerated 2)
    canonicalNearFirst_mem_rootGenerated) coordinateCycle_mem_rootGenerated

private theorem nearBase_eq_basis : (baseVector : Carrier F)=basisVector (.inr (0,0)) := by
  apply Prod.ext
  · ext i; fin_cases i <;> simp [baseVector,basisVector,Pi.single_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [baseVector,basisVector,SplitOctonion.basisVector,Pi.single_apply]

theorem canonicalNearFirst_fixes_point :
    (canonicalNearFirst (F:=F)) • (parabolicPoint (F:=F))=parabolicPoint (F:=F) := by
  apply Subtype.ext
  change (canonicalNearFirst (F:=F)).val • Projectivization.mk F parabolicVector _=
    Projectivization.mk F parabolicVector _
  simp only [Projectivization.smul_mk,LinearEquiv.smul_def,canonicalNearFirst_fixes_C0]

theorem canonicalNearSecond_fixes_point :
    (canonicalNearSecond (F:=F)) • basePoint F=basePoint F := by
  apply Subtype.ext
  change (canonicalNearSecond (F:=F)).val • Projectivization.mk F baseVector _=
    Projectivization.mk F baseVector _
  simp only [Projectivization.smul_mk,LinearEquiv.smul_def,nearBase_eq_basis,
    canonicalNearSecond_fixes_A0]

def canonicalNearIntermediate : WhiteZeroPoints F := canonicalNearFirst (F:=F) • basePoint F
def canonicalNearOpposite : WhiteZeroPoints F := canonicalNearSecond (F:=F) • canonicalNearIntermediate (F:=F)

private theorem nearOpposite_basis_ne_zero : (basisVector (.inr (2,7)) : Carrier F)≠0 := by
  intro h
  have hh := congrArg (fun x : Carrier F=>x.2 2 7) h
  simpa [basisVector,Pi.single_apply] using hh

theorem canonicalNearOpposite_projective :
    (canonicalNearOpposite (F:=F)).val=
      Projectivization.mk F (basisVector (.inr (2,7))) nearOpposite_basis_ne_zero := by
  change (canonicalNearSecond (F:=F)).val • ((canonicalNearFirst (F:=F)).val • Projectivization.mk F (baseVector (F:=F)) _)=_
  simp only [Projectivization.smul_mk,LinearEquiv.smul_def,nearBase_eq_basis,
    canonicalNearFirst_A0,canonicalNearSecond_B4]

theorem canonicalNearOpposite_chain :
    Atlas.GroupTheory.StabilizerMoveChain (Model F) parabolicPoint (basePoint F)
      (canonicalNearOpposite (F:=F)) := by
  have hi : Atlas.GroupTheory.StabilizerMoveChain (Model F) parabolicPoint (basePoint F)
      (canonicalNearIntermediate (F:=F)) := by
    exact .move parabolicPoint (basePoint F) .left .right
      ⟨canonicalNearFirst,canonicalNearFirst_fixes_point⟩
  change Atlas.GroupTheory.StabilizerMoveChain (Model F) parabolicPoint (basePoint F)
    (canonicalNearSecond (F:=F) • canonicalNearIntermediate (F:=F))
  exact .move (basePoint F) (canonicalNearIntermediate (F:=F)) .right hi
    ⟨canonicalNearSecond,canonicalNearSecond_fixes_point⟩

theorem canonicalNearOpposite_pairing :
    tracePairing (parabolicVector (F:=F)) (canonicalNearOpposite (F:=F)).val.rep≠0 := by
  rw [canonicalNearOpposite_projective]
  obtain ⟨s,hs⟩ := Projectivization.exists_smul_eq_mk_rep F
    (basisVector (.inr (2,7)) : Carrier F) nearOpposite_basis_ne_zero
  rw [←hs]
  change tracePairing (parabolicVector (F:=F)) ((s:F) • (basisVector (.inr (2,7)) : Carrier F))≠0
  rw [tracePairing_comm,tracePairing_smul_left,tracePairing_comm,
    tracePairing_octonion_basis]
  simpa [parabolicVector] using s.ne_zero

/-- A concrete two-step escape for the marked near pair. -/
theorem canonical_near_stabilizer_chain_escape :
    ∃z : WhiteZeroPoints F,
      Atlas.GroupTheory.StabilizerMoveChain (Model F) parabolicPoint (basePoint F) z ∧
      tracePairing parabolicVector z.val.rep≠0 :=
  ⟨canonicalNearOpposite,canonicalNearOpposite_chain,canonicalNearOpposite_pairing⟩

end Atlas.F4

