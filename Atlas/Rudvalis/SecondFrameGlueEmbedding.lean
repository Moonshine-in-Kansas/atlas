import Atlas.Rudvalis.FrameGlueOrbit
import Atlas.Rudvalis.SecondFrameGlueProjection
import Atlas.Rudvalis.HexadEmbedding
import Atlas.Rudvalis.SecondFrameUnitAction
import Atlas.Rudvalis.SecondFrameFrobenius
import Atlas.Lattices.BinaryGlueSymmetry

/-! From the actual hexad embedding and its signed frame orbit to the full local glue. -/
namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Lattices
open Atlas.Codes.Quaternary

noncomputable def frameGlueBasis (i : FrameGlueCoordinate) : RationalSpace :=
  secondFrame (frameGlueSeedCoordinate i)

noncomputable def frameGlueHalfLift (w : FrameGlueWord) : RationalSpace :=
  binaryHalfLift frameGlueBasis w

theorem frameGlueSeedCoordinate_marking (z : FrameGlueRealCoordinate) :
    frameGlueSeedCoordinate (frameGlueRealMarking z)=(frameGlueRow z.1,z.2) := by
  apply originalCoordinateEquiv.injective
  change originalCoordinateEquiv (originalCoordinateEquiv.symm
    (frameGluePoint z.1,(frameGlueRealMarking z).2))=_
  rw [Equiv.apply_symm_apply,originalCoordinateEquiv_apply,frameGluePoint_row]
  rfl

theorem frameGlueHalfLift_hexad : frameGlueHalfLift frameGlueHexad=hexadUnsignedVector := by
  unfold frameGlueHalfLift binaryHalfLift
  rw [← Equiv.sum_comp frameGlueRealMarking]
  have hh (z : FrameGlueRealCoordinate) : frameGlueHexad (frameGlueRealMarking z)=
      if z.2=(![5,1,3] z.1) ∨ z.2=(![6,3,5] z.1) then 1 else 0 :=
    frameGlueHexad_real_positions _ _
  simp_rw [hh]
  have hb (z : FrameGlueRealCoordinate) : frameGlueBasis (frameGlueRealMarking z)=
      secondFrame (frameGlueRow z.1,z.2) := congrArg secondFrame (frameGlueSeedCoordinate_marking z)
  simp_rw [hb]
  ext i
  simp [Fintype.sum_prod_type,Fin.sum_univ_succ,frameGlueRow,hexadUnsignedVector]
  have h1 : (ZMod.cast (1 : Bit) : ℚ)=1 := rfl
  rw [h1]
  ring

theorem frameGlueHalfLift_hexad_mem : frameGlueHalfLift frameGlueHexad∈rudvalisLattice := by
  rw [frameGlueHalfLift_hexad]
  exact hexadUnsignedVector_mem

/-- The signed discrepancy is absorbed by the actual integer frame. -/
theorem frameGlueHalfLift_transport (g : codeGroup) (p : Equiv.Perm FrameGlueCoordinate)
    (hp : ∀ i,rationalMonomialHom g.val (frameGlueBasis i)=frameGlueBasis (p.symm i) ∨
      rationalMonomialHom g.val (frameGlueBasis i)= -frameGlueBasis (p.symm i))
    (w : FrameGlueWord) (hw : frameGlueHalfLift w∈rudvalisLattice) :
    frameGlueHalfLift (w ∘ p)∈rudvalisLattice := by
  classical
  let s : FrameGlueCoordinate→Bit := fun i =>
    if rationalMonomialHom g.val (frameGlueBasis i)=frameGlueBasis (p.symm i) then 0 else 1
  have hs (i : FrameGlueCoordinate) : rationalMonomialHom g.val (frameGlueBasis i)=
      if s i=0 then frameGlueBasis (p.symm i) else -frameGlueBasis (p.symm i) := by
    by_cases h : rationalMonomialHom g.val (frameGlueBasis i)=frameGlueBasis (p.symm i)
    · simp [s,h]
    · simpa [s,h] using (hp i).resolve_left h
  exact binaryHalfLift_permute_mem rudvalisLattice frameGlueBasis (fun i => secondFrame_mem _)
    p.symm s (rationalMonomialHom g.val).toLinearMap hs (codeGroup_lattice_preserves g) w hw

/-- Geometric transport of an actual permutation of the three original rows. -/
noncomputable def frameGlueLocalPerm (p : Equiv.Perm FrameGlueRealCoordinate) :
    Equiv.Perm FrameGlueCoordinate :=
  (frameGlueRealMarking.symm.trans p).trans frameGlueRealMarking

theorem frameGlueLocalPerm_trans (p q : Equiv.Perm FrameGlueRealCoordinate) :
    frameGlueLocalPerm (p.trans q)=(frameGlueLocalPerm p).trans (frameGlueLocalPerm q) := by
  apply Equiv.ext
  intro i
  simp [frameGlueLocalPerm]

theorem frameGlueLocalPerm_pow_succ (p : Equiv.Perm FrameGlueRealCoordinate) (n : ℕ) :
    frameGlueLocalPerm (p^(n+1))=(frameGlueLocalPerm p).trans (frameGlueLocalPerm (p^n)) := by
  apply Equiv.ext
  intro i
  simp [frameGlueLocalPerm,pow_succ,Equiv.Perm.mul_apply]

theorem frameGlueHalfLift_real_transport (g : codeGroup) (p : Equiv.Perm FrameGlueRealCoordinate)
    (hp : ∀z,rationalMonomialHom g.val (secondFrame (frameGlueRow z.1,z.2))=
      secondFrame (frameGlueRow (p.symm z).1,(p.symm z).2) ∨
      rationalMonomialHom g.val (secondFrame (frameGlueRow z.1,z.2))=
      -secondFrame (frameGlueRow (p.symm z).1,(p.symm z).2))
    (w : FrameGlueWord) (hw : frameGlueHalfLift w∈rudvalisLattice) :
    frameGlueHalfLift (w ∘ frameGlueLocalPerm p)∈rudvalisLattice := by
  apply frameGlueHalfLift_transport g _ ?_ w hw
  intro i
  obtain ⟨z,rfl⟩ := frameGlueRealMarking.surjective i
  have he : (frameGlueLocalPerm p).symm (frameGlueRealMarking z)=frameGlueRealMarking (p.symm z) := by
    simp [frameGlueLocalPerm]
  rw [he]
  change _=secondFrame (frameGlueSeedCoordinate (frameGlueRealMarking (p.symm z))) ∨
    _= -secondFrame (frameGlueSeedCoordinate (frameGlueRealMarking (p.symm z)))
  rw [frameGlueSeedCoordinate_marking]
  have hb : frameGlueBasis (frameGlueRealMarking z)=secondFrame (frameGlueRow z.1,z.2) :=
    congrArg secondFrame (frameGlueSeedCoordinate_marking z)
  rw [hb]
  exact hp z

theorem frameGlueHalfLift_unit (u : Fin 8) (w : FrameGlueWord)
    (hw : frameGlueHalfLift w∈rudvalisLattice) :
    frameGlueHalfLift (w ∘ frameGlueLocalPerm (frameGlueRealUnit u))∈rudvalisLattice := by
  apply frameGlueHalfLift_transport (codeUnit u) _ ?_ w hw
  intro i
  obtain ⟨z,rfl⟩ := frameGlueRealMarking.surjective i
  have hb : frameGlueBasis (frameGlueRealMarking z)=secondFrame (frameGlueRow z.1,z.2) :=
    congrArg secondFrame (frameGlueSeedCoordinate_marking z)
  have hp : (frameGlueLocalPerm (frameGlueRealUnit u)).symm (frameGlueRealMarking z)=
      frameGlueRealMarking (frameGlueRealUnit u z) := by
    simp [frameGlueLocalPerm,frameGlueRealUnit]
  rw [hb,hp]
  change _=secondFrame (frameGlueSeedCoordinate (frameGlueRealMarking (frameGlueRealUnit u z))) ∨
    _= -secondFrame (frameGlueSeedCoordinate (frameGlueRealMarking (frameGlueRealUnit u z)))
  rw [frameGlueSeedCoordinate_marking,secondFrame_unit]
  split <;> simp_all [frameGlueRealUnit]

/-- A finite orbit is obtained from just the unit and Frobenius actions. -/
theorem frameGlueHalfLift_orbit_of_generators
    (hu : ∀u : Fin 8,∀w : FrameGlueWord,frameGlueHalfLift w∈rudvalisLattice →
      frameGlueHalfLift (w ∘ frameGlueLocalPerm (frameGlueRealUnit u))∈rudvalisLattice)
    (ht : ∀w : FrameGlueWord,frameGlueHalfLift w∈rudvalisLattice →
      frameGlueHalfLift (w ∘ frameGlueLocalPerm frameGlueRealT)∈rudvalisLattice)
    (o : Fin 24) : frameGlueHalfLift (frameGlueOrbitWord o)∈rudvalisLattice := by
  have hp (n : ℕ) (w : FrameGlueWord) (hw : frameGlueHalfLift w∈rudvalisLattice) :
      frameGlueHalfLift (w ∘ frameGlueLocalPerm (frameGlueRealT^n))∈rudvalisLattice := by
    induction n with
    | zero => simpa [frameGlueLocalPerm] using hw
    | succ n ih =>
      simpa only [frameGlueLocalPerm_pow_succ,Equiv.trans_apply,Function.comp_def] using ht _ ih
  change frameGlueHalfLift (frameGlueHexad ∘ frameGlueLocalPerm
    ((frameGlueRealT^(o.val/8)).trans (frameGlueRealUnit ⟨o.val%8,Nat.mod_lt _ (by decide)⟩)))∈_
  rw [frameGlueLocalPerm_trans]
  exact hp (o.val/8) (frameGlueHexad ∘ frameGlueLocalPerm (frameGlueRealUnit ⟨o.val%8,Nat.mod_lt _ (by decide)⟩)) (hu ⟨o.val%8,Nat.mod_lt _ (by decide)⟩ frameGlueHexad frameGlueHalfLift_hexad_mem)

theorem frameGlueHalfLift_mem_of_orbit
    (horbit : ∀ o : Fin 24,frameGlueHalfLift (frameGlueOrbitWord o)∈rudvalisLattice)
    (w : FrameGlueWord) (hw : w∈frameGlueCode) : frameGlueHalfLift w∈rudvalisLattice := by
  apply binaryHalfLift_mem_of_span rudvalisLattice frameGlueBasis (fun i => secondFrame_mem _)
    (Set.range frameGlueOrbitWord)
  · rintro w ⟨o,rfl⟩
    exact horbit o
  · rwa [frameGlueHexad_orbit_spans]

theorem secondFrameGlue_embedding_of_orbit
    (horbit : ∀ o : Fin 24,frameGlueHalfLift (frameGlueOrbitWord o)∈rudvalisLattice)
    (v : RationalSpace) (hv : MemSecondFrameGlue v) : v∈rudvalisLattice := by
  obtain ⟨z,hz,rfl⟩ := hv
  exact integerHalfLift_mem rudvalisLattice frameGlueBasis (fun i => secondFrame_mem _) z
    (frameGlueHalfLift_mem_of_orbit horbit _ hz)

theorem frameGlueHalfLift_T (w : FrameGlueWord) (hw : frameGlueHalfLift w∈rudvalisLattice) :
    frameGlueHalfLift (w ∘ frameGlueLocalPerm frameGlueRealT)∈rudvalisLattice := by
  apply frameGlueHalfLift_real_transport codeT frameGlueRealT ?_ w hw
  intro z
  left
  have he : (frameGlueRow (frameGlueRealT.symm z).1,(frameGlueRealT.symm z).2)=
      (seedDoubleRow (frameGlueRow z.1),seedTIndexEquiv.symm z.2) := by
    decide +kernel +revert
  rw [he]
  exact secondFrame_T _ _

theorem frameGlueOrbit_halfLift_mem (o : Fin 24) :
    frameGlueHalfLift (frameGlueOrbitWord o)∈rudvalisLattice :=
  frameGlueHalfLift_orbit_of_generators frameGlueHalfLift_unit frameGlueHalfLift_T o

/-- The literal local binary glue embeds in the actual Construction-A lattice. -/
theorem secondFrameGlue_embedding (v : RationalSpace) (hv : MemSecondFrameGlue v) :
    v∈rudvalisLattice := secondFrameGlue_embedding_of_orbit frameGlueOrbit_halfLift_mem v hv

theorem frameGlueReflection_lattice_iff (v : RationalSpace) :
    frameGlueReflection v∈rudvalisLattice ↔ v∈rudvalisLattice :=
  secondFrameGlue_reflection_lattice_iff secondFrameGlue_embedding v

end Atlas.Rudvalis
