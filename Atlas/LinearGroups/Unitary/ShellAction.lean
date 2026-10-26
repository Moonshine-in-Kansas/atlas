import Atlas.LinearGroups.Unitary.VectorAction
import Atlas.LinearGroups.Unitary.NormOneTransport
import Atlas.LinearGroups.Unitary.NormCounts

/-! # The actual transitive norm-one shell action and its independent count -/
noncomputable section
namespace Atlas.Unitary
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

instance normOne_pretransitive (hdeg : Module.finrank F K = 2) :
    MulAction.IsPretransitive (U F K n hdeg) (NormOneVectors F K n) where
  exists_smul_eq v w := by
    obtain ⟨g, hg⟩ := exists_unitary_map hdeg v.val w.val v.prop w.prop
    exact ⟨g, Subtype.ext hg⟩

theorem card_normOneVectors (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Nat.card (NormOneVectors F K (n + 1)) =
      Nat.card F ^ n * orderFactor (Nat.card F) (n + 1) :=
  card_hermitian_norm_one hdeg n

/-- The orbit is the entire actual norm-one shell, not an abstract set of its size. -/
def normOneOrbitEquiv (hdeg : Module.finrank F K = 2) (v : NormOneVectors F K n) :
    MulAction.orbit (U F K n hdeg) v ≃ NormOneVectors F K n :=
  Equiv.ofBijective (fun p => p.val) ⟨Subtype.val_injective, fun w => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (U F K n hdeg) v w
    exact ⟨⟨w, ⟨g, hg⟩⟩, rfl⟩⟩
end Atlas.Unitary
