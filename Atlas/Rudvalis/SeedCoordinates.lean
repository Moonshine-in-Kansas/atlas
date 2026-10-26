import Atlas.Rudvalis.BinaryLinearLifts

/-! Literal Version 33 signed Hamming coordinates and integer seed arrays.
The label table uses (e₁,-e₀,e₂,…,e₇), whereas the integer arrays use (e₀,…,e₇). -/
namespace Atlas.Rudvalis
open scoped BigOperators

abbrev SeedCoordinate := Fin 7 × Fin 8

def seedInnerLabel (r : Fin 7) (k : Fin 8) : E := binaryLabel
  (![![0,6,2,4,7,1,3,5],![0,1,3,2,4,5,6,7],![0,5,6,3,2,7,1,4],
    ![0,7,1,6,3,4,5,2],![0,4,5,1,6,2,7,3],![0,2,7,5,1,3,4,6],
    ![0,3,4,7,5,6,2,1]] r k)

theorem seedInnerLabel_bijective (r : Fin 7) : Function.Bijective (seedInnerLabel r) := by
  decide +kernel +revert

noncomputable def seedInnerEquiv (r : Fin 7) : Fin 8 ≃ E :=
  Equiv.ofBijective (seedInnerLabel r) (seedInnerLabel_bijective r)

noncomputable def seedCoordinateEquiv : SeedCoordinate ≃ Coordinate where
  toFun z := (rowEquiv z.1,seedInnerEquiv z.1 z.2)
  invFun z := (rowEquiv.symm z.1,(seedInnerEquiv (rowEquiv.symm z.1)).symm z.2)
  left_inv z := by simp
  right_inv z := by simp

def signedPositionIndex (k : Fin 8) : Fin 8 := if k=0 then 1 else if k=1 then 0 else k

def signedPositionSign (k : Fin 8) : ℤ := if k=1 then -1 else 1

noncomputable def signedSeedTransport (v : SeedCoordinate → ℤ) : Coordinate → ℤ := fun z =>
  let q := seedCoordinateEquiv.symm z
  signedPositionSign q.2 * v (q.1,signedPositionIndex q.2)

theorem signedSeedTransport_apply (v : SeedCoordinate → ℤ) (r : Fin 7) (k : Fin 8) :
    signedSeedTransport v (seedCoordinateEquiv (r,k)) =
      signedPositionSign k * v (r,signedPositionIndex k) := by
  simp [signedSeedTransport]

def seedAArray (z : SeedCoordinate) : ℤ :=
  (![![1,0,1,0,1,0,1,0],![0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0],
    ![0,1,1,0,0,1,-1,0],![0,0,0,0,0,0,0,0],![0,1,0,1,-1,0,1,0],
    ![0,1,-1,0,1,0,0,1]] z.1 z.2)

def seedBArray (z : SeedCoordinate) : ℤ :=
  (![![0,1,1,0,1,0,1,0],![0,1,0,0,0,0,-1,0],![0,1,-1,0,0,0,0,0],
    ![0,0,0,0,-1,0,1,0],![0,1,0,0,-1,0,0,0],![0,0,-1,0,1,0,0,0],
    ![0,0,1,0,0,0,-1,0]] z.1 z.2)

noncomputable def seedAWord : Coordinate → ℤ := signedSeedTransport seedAArray
noncomputable def seedBWord : Coordinate → ℤ := signedSeedTransport seedBArray

def seedAParameters : BinaryParameters :=
  ((fun p => (if p.val=binaryLabel 6 then 1 else 0)+dot (binaryLabel 2) p.val),
    outerMatrix (binaryLabel 2) (binaryLabel 2),0)

def seedBParameters : BinaryParameters :=
  ((fun p => if p.val=binaryLabel 1 ∨ p.val=binaryLabel 4 ∨
    p.val=binaryLabel 5 ∨ p.val=binaryLabel 6 then 1 else 0),0,binaryLabel 6)

theorem seedA_residue : (fun z : Coordinate => (seedAWord z : Bit)) =
    binaryNormalMap seedAParameters := by
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change (signedSeedTransport seedAArray (seedCoordinateEquiv (r,k)) : Bit)=_
  rw [signedSeedTransport_apply]
  change ((signedPositionSign k * seedAArray (r,signedPositionIndex k) : ℤ) : Bit)=
    binaryNormalMap seedAParameters (rowLabel r,seedInnerLabel r k)
  decide +kernel +revert


theorem seedB_residue : (fun z : Coordinate => (seedBWord z : Bit)) =
    binaryNormalMap seedBParameters := by
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change (signedSeedTransport seedBArray (seedCoordinateEquiv (r,k)) : Bit)=_
  rw [signedSeedTransport_apply]
  change ((signedPositionSign k * seedBArray (r,signedPositionIndex k) : ℤ) : Bit)=
    binaryNormalMap seedBParameters (rowLabel r,seedInnerLabel r k)
  decide +kernel +revert

theorem seedA_residue_mem : (fun z : Coordinate => (seedAWord z : Bit)) ∈ binaryResidue := by
  rw [seedA_residue]
  exact ⟨seedAParameters,rfl⟩

theorem seedB_residue_mem : (fun z : Coordinate => (seedBWord z : Bit)) ∈ binaryResidue := by
  rw [seedB_residue]
  exact ⟨seedBParameters,rfl⟩

theorem seedA_norm_sq : (∑ z : Coordinate, seedAWord z ^ 2)=16 := by
  rw [← Equiv.sum_comp seedCoordinateEquiv]
  change (∑ z : SeedCoordinate, signedSeedTransport seedAArray (seedCoordinateEquiv z)^2)=16
  simp_rw [show ∀ z : SeedCoordinate, signedSeedTransport seedAArray (seedCoordinateEquiv z) =
    signedPositionSign z.2 * seedAArray (z.1,signedPositionIndex z.2) from
    fun z => signedSeedTransport_apply seedAArray z.1 z.2]
  decide +kernel

theorem seedB_norm_sq : (∑ z : Coordinate, seedBWord z ^ 2)=16 := by
  rw [← Equiv.sum_comp seedCoordinateEquiv]
  change (∑ z : SeedCoordinate, signedSeedTransport seedBArray (seedCoordinateEquiv z)^2)=16
  simp_rw [show ∀ z : SeedCoordinate, signedSeedTransport seedBArray (seedCoordinateEquiv z) =
    signedPositionSign z.2 * seedBArray (z.1,signedPositionIndex z.2) from
    fun z => signedSeedTransport_apply seedBArray z.1 z.2]
  decide +kernel

end Atlas.Rudvalis

