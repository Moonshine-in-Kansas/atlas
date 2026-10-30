import Atlas.LinearGroups.ReeF4.SpecialAdjacency
import Atlas.LinearGroups.ReeF4.SpecialMarkedPoints
import Atlas.LinearGroups.ReeF4.SpecialPointCount

/-! Actual opposition and the opposite-point chart. Scalar representative
independence is proved before using the projective relation. No group order enters. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem polar_nonzero_units_smul_iff (a b : Fˣ) (u v : TraceZero F) :
    traceZeroPolar (a • u) (b • v) ≠ 0 ↔ traceZeroPolar u v ≠ 0 := by
  simp only [Units.smul_def]
  rw [traceZeroPolar_smul_left,traceZeroPolar_comm u ((b:F) • v),
    traceZeroPolar_smul_left,traceZeroPolar_comm v u]
  simp only [mul_ne_zero_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨a.ne_zero, b.ne_zero, h⟩⟩

theorem polar_nonzero_mk_reps_iff (u v : TraceZero F) (hu : u ≠ 0) (hv : v ≠ 0) :
    traceZeroPolar (Projectivization.mk F u hu).rep (Projectivization.mk F v hv).rep ≠ 0 ↔
      traceZeroPolar u v ≠ 0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F u hu
  obtain ⟨b,hb⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  rw [←ha,←hb]
  exact polar_nonzero_units_smul_iff a b u v

def SpecialOpposite (m : ℕ) (p q : SpecialPoints (F := F) m) : Prop :=
  traceZeroPolar p.val.rep q.val.rep ≠ 0

theorem specialOpposite_symm (m : ℕ) (p q : SpecialPoints (F := F) m) :
    SpecialOpposite m p q ↔ SpecialOpposite m q p := by
  unfold SpecialOpposite
  rw [traceZeroPolar_comm]

theorem specialOpposite_irrefl (m : ℕ) (p : SpecialPoints (F := F) m) :
    ¬SpecialOpposite m p p := by
  simp [SpecialOpposite,traceZeroPolar_self]

theorem specialOpposite_mk_iff (m : ℕ) (u v : TraceZero F)
    (hu : IsSpecialVector m u) (hv : IsSpecialVector m v) :
    SpecialOpposite m (specialPointMk m u hu) (specialPointMk m v hv) ↔
      traceZeroPolar u v ≠ 0 :=
  polar_nonzero_mk_reps_iff u v hu.ne_zero hv.ne_zero

theorem firstRoot_polar_coordinate (u : TraceZero F) :
    traceZeroPolar (rootVector (F := F) (0,0)) u = isotropyCoordinates u 9 := by
  simp [traceZeroPolar,tracePairing,quadraticTrace,trace,rootVector,
    isotropyCoordinates,SplitOctonion.norm,Pi.single_apply]
  ring

theorem specialOpposite_first_iff (m : ℕ) (p : SpecialPoints (F := F) m) :
    SpecialOpposite m (firstSpecialPoint m) p ↔ isotropyCoordinates p.val.rep 9≠0 := by
  have h := specialOpposite_mk_iff m (rootVector (F := F) (0,0)) p.val.rep
    (isSpecialVector_firstRoot m) p.property
  rw [specialPointMk_rep,firstRoot_polar_coordinate] at h
  exact h

abbrev OppositeSpecialPoints (m : ℕ) :=
  {p : SpecialPoints (F := F) m // SpecialOpposite m (firstSpecialPoint m) p}

def chart9ToOpposite (m : ℕ) (u : NormalizedSpecialChart (F := F) m 9) :
    OppositeSpecialPoints (F := F) m :=
  ⟨specialPointMk m u.val u.property.1,
    (specialOpposite_mk_iff m _ _ (isSpecialVector_firstRoot m) u.property.1).mpr (by
      rw [firstRoot_polar_coordinate,u.property.2.1]
      exact one_ne_zero)⟩

theorem chart9ToOpposite_injective (m : ℕ) : Function.Injective (chart9ToOpposite (F := F) m) := by
  intro u v h
  have hp := congrArg Subtype.val h
  obtain ⟨a,ha⟩ := (specialPointMk_eq_iff m u.val v.val u.property.1 v.property.1).mp hp
  have hc := congrArg (fun w : TraceZero F => isotropyCoordinates w 9) ha
  have hs : isotropyCoordinates (a • v.val) 9 = (a:F) * isotropyCoordinates v.val 9 := by
    change isotropyCoordinates ((a:F) • v.val) 9 = _
    rw [_root_.map_smul]
    rfl
  rw [hs,v.property.2.1,u.property.2.1,mul_one] at hc
  have ha1 : a=1 := Units.ext hc
  apply Subtype.ext
  simpa only [ha1,one_smul] using ha.symm

theorem chart9ToOpposite_surjective (m : ℕ) : Function.Surjective (chart9ToOpposite (F := F) m) := by
  intro p
  have hn := (specialOpposite_first_iff m p.val).mp p.property
  let a : Fˣ := (Units.mk0 (isotropyCoordinates p.val.val.rep 9) hn)⁻¹
  let u : TraceZero F := a • p.val.val.rep
  have hu : IsSpecialVector m u := (isSpecialVector_units_smul_iff m a _).mpr p.val.property
  have hone : isotropyCoordinates u 9=1 := by
    change isotropyCoordinates ((a:F) • p.val.val.rep) 9=1
    rw [_root_.map_smul]
    change (isotropyCoordinates p.val.val.rep 9)⁻¹ * isotropyCoordinates p.val.val.rep 9=1
    exact inv_mul_cancel₀ hn
  have hmax : ∀ j : Fin 26, specialAbsoluteGrade j≤specialAbsoluteGrade 9 := by decide
  let z : NormalizedSpecialChart (F := F) m 9 :=
    ⟨u,hu,hone,fun j hj => False.elim ((not_lt_of_ge (hmax j)) hj)⟩
  refine ⟨z,?_⟩
  apply Subtype.ext
  change specialPointMk m (a • p.val.val.rep) hu=p.val
  rw [specialPointMk_units_smul m p.val.val.rep p.val.property a,specialPointMk_rep]

/-- Opposite points to A−4 are precisely the actual normalized A4 chart. -/
def oppositeSpecialPointsEquivChart9 (m : ℕ) :
    OppositeSpecialPoints (F := F) m ≃ NormalizedSpecialChart (F := F) m 9 :=
  (Equiv.ofBijective (chart9ToOpposite m)
    ⟨chart9ToOpposite_injective m,chart9ToOpposite_surjective m⟩).symm

theorem card_oppositeSpecialPoints {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (OppositeSpecialPoints (F := F) m)=(Nat.card F)^10 := by
  rw [Nat.card_congr (oppositeSpecialPointsEquivChart9 m),card_normalizedChart9 hcard]

end Atlas.ReeF4
