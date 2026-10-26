import Atlas.LinearGroups.ReeF4.WeylSL2Scalar
import Atlas.LinearGroups.ReeF4.WeylSL2Model
import Atlas.LinearGroups.ReeF4.TorusDerived
import Mathlib.GroupTheory.NoncommCoprod

/-! A faithful actual SL₂×F× subgroup; no full line-stabilizer claim is made. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def modelLongSL2ScalarHom {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) : Fˣ →* Model F m where
  toFun c := torusModelHom hcard (c,c)
  map_one' := (torusModelHom hcard).map_one
  map_mul' c d := (torusModelHom hcard).map_mul (c,c) (d,d)

theorem modelLongSL2ScalarHom_injective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) : Function.Injective (modelLongSL2ScalarHom hcard) := by
  intro c d h
  have hh := congrArg (fun g : Model F m => g.val) h
  have hp := torusHom_injective (F := F) m hh
  exact congrArg Prod.fst hp

theorem modelLongSL2_commutes_scalar {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (A : LongSL2 (F := F)) (c : Fˣ) :
    Commute (modelLongSL2Hom hcard A) (modelLongSL2ScalarHom hcard c) := by
  apply Subtype.ext
  exact (torusEquiv_scalar_commutes m c (theta F m).toRingHom A).symm

theorem modelLongSL2_disjoint_scalar {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Disjoint (modelLongSL2Hom hcard).range (modelLongSL2ScalarHom hcard).range := by
  rw [disjoint_iff_inf_le]
  rintro g ⟨⟨A,hA⟩,⟨c,hc⟩⟩
  have h := congrArg (fun z : Model F m => z.val) (hA.trans hc.symm)
  have htriv := longSL2_scalar_intersection m (theta F m).toRingHom A c h
  have hg : g = 1 := by rw [← hA,htriv.1,map_one]
  exact hg

def modelLongSL2ProductHom {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    LongSL2 (F := F) × Fˣ →* Model F m :=
  (modelLongSL2Hom hcard).noncommCoprod (modelLongSL2ScalarHom hcard)
    (modelLongSL2_commutes_scalar hcard)

theorem modelLongSL2ProductHom_injective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) : Function.Injective (modelLongSL2ProductHom hcard) := by
  exact (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨modelLongSL2Hom_injective hcard, modelLongSL2ScalarHom_injective hcard,
      modelLongSL2_disjoint_scalar hcard⟩

def modelLongSL2ProductSubgroup {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Subgroup (Model F m) := (modelLongSL2ProductHom hcard).range

def modelLongSL2ProductEquiv {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    LongSL2 (F := F) × Fˣ ≃* modelLongSL2ProductSubgroup hcard :=
  MonoidHom.ofInjective (modelLongSL2ProductHom_injective hcard)

end Atlas.ReeF4
