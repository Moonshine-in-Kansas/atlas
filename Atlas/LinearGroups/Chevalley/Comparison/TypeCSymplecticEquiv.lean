import Atlas.LinearGroups.Chevalley.Comparison.TypeCSymplecticSurjective
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionBCOrder
import Atlas.LinearGroups.Symplectic.Order

/-! The concrete type-C weight-block map is bijective over a finite field.
Surjectivity is obtained from actual transvections; injectivity then follows
from the independently proved orders of its source and target. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeC

private theorem adjacent_ne {n : ℕ} (i : Fin n) : i.castSucc ≠ i.succ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

theorem companion_card_eq_Sp (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion (.C (n + 1) hn) K) =
      Nat.card (Atlas.Symplectic.Sp (n + 1) K) := by
  rw [selectedWeightCompanion_C_card, Atlas.Symplectic.card_sp,
    Atlas.Symplectic.orderNumerator]
  simp only [pow_two]

/-- The marked isomorphism induced by the actual defining-weight matrix map. -/
def symplecticEquiv (n : ℕ) (hn : 2 ≤ n + 1) (K : Type*) [Field K] [Finite K] :
    SelectedWeightCompanion (.C (n + 1) hn) K ≃* Atlas.Symplectic.Sp (n + 1) K :=
  MulEquiv.ofBijective (symplecticHom n hn K)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨symplecticHom_surjective n hn K, companion_card_eq_Sp n hn K⟩)

theorem symplecticEquiv_X_short (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] [Finite K] (i : Fin n) (t : K) :
    symplecticEquiv n hn K (selectedWeightCompanionX (.C (n + 1) hn) K i.castSucc t) =
      ⟨shortMatrix (n + 1) K i.castSucc i.succ t,
        shortMatrix_mem (n + 1) K i.castSucc i.succ (adjacent_ne i) t⟩ :=
  Subtype.ext (symplecticHom_X_short n hn K i t)

theorem symplecticEquiv_Y_short (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] [Finite K] (i : Fin n) (t : K) :
    symplecticEquiv n hn K (selectedWeightCompanionY (.C (n + 1) hn) K i.castSucc t) =
      ⟨shortMatrix (n + 1) K i.succ i.castSucc t,
        shortMatrix_mem (n + 1) K i.succ i.castSucc (Ne.symm (adjacent_ne i)) t⟩ :=
  Subtype.ext (symplecticHom_Y_short n hn K i t)

theorem symplecticEquiv_X_long (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] [Finite K] (t : K) :
    symplecticEquiv n hn K (selectedWeightCompanionX (.C (n + 1) hn) K (Fin.last n) t) =
      ⟨longMatrix (n + 1) K (Fin.last n) t,
        longMatrix_mem (n + 1) K (Fin.last n) t⟩ :=
  Subtype.ext (symplecticHom_X_long n hn K t)

theorem symplecticEquiv_Y_long (n : ℕ) (hn : 2 ≤ n + 1)
    (K : Type*) [Field K] [Finite K] (t : K) :
    symplecticEquiv n hn K (selectedWeightCompanionY (.C (n + 1) hn) K (Fin.last n) t) =
      ⟨(longMatrix (n + 1) K (Fin.last n) t).transpose,
        longMatrix_transpose_mem (n + 1) K (Fin.last n) t⟩ :=
  Subtype.ext (symplecticHom_Y_long n hn K t)

end Atlas.Chevalley.Comparison.TypeC
