import Atlas.LinearGroups.Chevalley.RootData.F4ShortOrbit
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBTailWords

/-! Genuine B3 word transport into the first three marked F4 nodes. The
doubled Cartesian root coordinates turn their action into the actual integral
B3 linear action on the final three coordinates. Equality and faithfulness
are proved on integer vectors, without any order or presentation theorem. -/
noncomputable section
namespace Atlas.Chevalley.F4B3
open Classical ClassicalData RootData F4Data

def markedSimple (i : (baseB 2).support) : base.support :=
  baseIndexEquiv (((baseBIndexEquiv 2).symm i).castSucc)

def markedWord (l : List (baseB 2).support) : F4ShortOrbit.W :=
  rootWeylWord pairing base (l.map markedSimple)

private theorem simple_cartesian (i : Fin 3) (β : F4Data.Root) :
    Atlas.F4.RootData.coordinates
      (pairing.reflectionPerm (baseIndexEquiv i.castSucc).val β) =
      Fin.cons (Atlas.F4.RootData.coordinates β 0)
        (reflect (simpleB 2 i) (Fin.tail (Atlas.F4.RootData.coordinates β))) := by
  change Atlas.F4.RootData.coordinates
    (F4Table.reflectionIndex (F4Table.simpleIndex i.castSucc) β) = _
  exact (show ∀ i : Fin 3, ∀ β : F4Data.Root,
    Atlas.F4.RootData.coordinates
      (F4Table.reflectionIndex (F4Table.simpleIndex i.castSucc) β) =
        Fin.cons (Atlas.F4.RootData.coordinates β 0)
          (reflect (simpleB 2 i) (Fin.tail (Atlas.F4.RootData.coordinates β))) by
      decide +kernel) i β

theorem markedSimple_cartesian (i : (baseB 2).support) (β : F4Data.Root) :
    Atlas.F4.RootData.coordinates (pairing.reflectionPerm (markedSimple i).val β) =
      Fin.cons (Atlas.F4.RootData.coordinates β 0)
        (reflect i.val (Fin.tail (Atlas.F4.RootData.coordinates β))) := by
  obtain ⟨k, rfl⟩ := (baseBIndexEquiv 2).surjective i
  have hk : ((baseBIndexEquiv 2) k).val = simpleB 2 k := rfl
  simpa only [markedSimple, Equiv.symm_apply_apply, hk] using simple_cartesian k β

/-- The entire Cartesian tail, including half-root doubled coordinates,
is transported; this is stronger than agreement on the embedded B3 roots. -/
theorem markedWord_cartesian (l : List (baseB 2).support) (β : F4Data.Root) :
    Atlas.F4.RootData.coordinates ((markedWord l).val β) =
      Fin.cons (Atlas.F4.RootData.coordinates β 0)
        (ClassicalBParabolic.latticeWord 2 l
          (Fin.tail (Atlas.F4.RootData.coordinates β))) := by
  induction l with
  | nil =>
    change Atlas.F4.RootData.coordinates β =
      Fin.cons (Atlas.F4.RootData.coordinates β 0)
        (Fin.tail (Atlas.F4.RootData.coordinates β))
    exact (Fin.cons_self_tail _).symm
  | cons i l ih =>
    change Atlas.F4.RootData.coordinates
      (pairing.reflectionPerm (markedSimple i).val ((markedWord l).val β)) = _
    rw [markedSimple_cartesian, ih]
    simp only [Fin.cons_zero, Fin.tail_cons]
    rfl

/-- B3 root permutations determine the full integer linear action, hence
also the F4 action on all48 original labels. -/
theorem markedWord_eq_of_rootWord_eq (l r : List (baseB 2).support)
    (h : rootWeylWord (pairingB 3) (baseB 2) l =
      rootWeylWord (pairingB 3) (baseB 2) r) : markedWord l = markedWord r := by
  apply Subtype.ext
  apply Equiv.ext
  intro β
  apply Atlas.F4.RootData.coordinates_injective
  rw [markedWord_cartesian, markedWord_cartesian,
    ClassicalBParabolic.latticeWord_eq_of_rootWord_eq 2 l r h]

private def axis (k : Fin 3) : F4Data.Root := ![26,28,30] k

private theorem axis_tail : ∀ k : Fin 3,
    Fin.tail (Atlas.F4.RootData.coordinates (axis k)) =
      (2 : ℤ) • (Pi.single k (1 : ℤ) : ClassicalData.Lattice 3) := by
  decide +kernel

/-- The three axial F4 roots detect the B3 linear action. Cancellation of2
occurs exclusively in the integer lattice, before any coefficient field. -/
theorem rootWord_eq_of_markedWord_eq (l r : List (baseB 2).support)
    (h : markedWord l = markedWord r) :
    rootWeylWord (pairingB 3) (baseB 2) l =
      rootWeylWord (pairingB 3) (baseB 2) r := by
  have hlinear : ClassicalBParabolic.latticeWord 2 l =
      ClassicalBParabolic.latticeWord 2 r := by
    apply (Pi.basisFun ℤ (Fin 3)).ext
    intro k
    rw [Pi.basisFun_apply]
    have he := congrArg (fun w : F4ShortOrbit.W =>
      Atlas.F4.RootData.coordinates (w.val (axis k))) h
    rw [markedWord_cartesian, markedWord_cartesian] at he
    have ht := congrArg (fun x : Fin 4 → ℤ => Fin.tail x) he
    simp only [Fin.tail_cons, axis_tail, map_smul] at ht
    exact (smul_right_injective (ClassicalData.Lattice 3)
      (show (2 : ℤ) ≠ 0 by decide)) ht
  apply Subtype.ext
  apply Equiv.ext
  intro β
  apply Subtype.ext
  have hβ := congrArg (fun f : Module.End ℤ (ClassicalData.Lattice 3) => f β.val) hlinear
  rw [ClassicalBParabolic.latticeWord_root, ClassicalBParabolic.latticeWord_root] at hβ
  simpa only [rootWeylWord_val] using hβ

end Atlas.Chevalley.F4B3
