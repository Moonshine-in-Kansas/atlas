import Atlas.Lattices.LeechCrossGeometry
import Atlas.Lattices.LeechVisibleSymmetries
import Atlas.Lattices.LeechSextetSigns
import Atlas.Lattices.LeechSextetPermutations

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

/-- Job 12 on the retained Golay lattice, including explicit sextet crosses. -/
structure LeechConstruction : Prop where
  lattice : LatticeConstruction
  symmetries : VisibleSymmetryConstruction
  shells : SmallShellConstruction
  intrinsic : IntrinsicCrossConstruction
  sextet_vectors : ∀ S b, crossIntegerVectors (sextetCross S b) = sextetIntegerVectors S b
  sextet_injective : Function.Injective (fun p : UnorderedSextet × Bit => sextetCross p.1 p.2)
  sextet_count : sextetCrosses.card = 3542
  sign_parity_independent : ∀ (S : UnorderedSextet) (c : golay) (T U : {T // T ∈ S.val}),
    tetradSignParity c.val T.val = tetradSignParity c.val U.val
  permutation_action : ∀ S b g,
    crossAction (permutationIsometry g) (sextetCross S b) = sextetCross (sextetAction g S) b
  sign_action : ∀ S b c (T : {T // T ∈ S.val}),
    crossAction (signIsometry c) (sextetCross S b) =
      sextetCross S (b + tetradSignParity c.val T.val)

theorem leech_constructed : LeechConstruction where
  lattice := leech_lattice_constructed
  symmetries := leech_visible_symmetries_constructed
  shells := leech_small_shells_constructed
  intrinsic := leech_intrinsic_crosses_constructed
  sextet_vectors := sextetCross_vectors
  sextet_injective := sextetCross_injective
  sextet_count := sextetCrosses_card
  sign_parity_independent := sextetSignParity_independent
  permutation_action := sextetCross_permutation_action
  sign_action := sextetCross_sign_action

end Atlas.Lattices
