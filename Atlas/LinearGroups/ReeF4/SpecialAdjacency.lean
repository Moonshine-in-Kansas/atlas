import Atlas.LinearGroups.ReeF4.SpecialPoints

/-! The actual symmetric zero-product adjacency relation on special projective
points. No assertion about lines, incidence counts or transitivity is made. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The partial product is defined and zero. -/
def StarOrthogonal (m : ℕ) (u v : TraceZero F) : Prop :=
  ∃ h : StarDomain u v, proposedPartialProduct (thetaInv F m).toRingHom u v h = 0

theorem StarOrthogonal.symm {m : ℕ} {u v : TraceZero F}
    (h : StarOrthogonal m u v) : StarOrthogonal m v u := by
  rcases h with ⟨h,he⟩
  refine ⟨(starDomain_comm u v).mp h,?_⟩
  rw [←proposedPartialProduct_comm (thetaInv F m).toRingHom u v h]
  exact he

theorem starOrthogonal_comm (m : ℕ) (u v : TraceZero F) :
    StarOrthogonal m u v ↔ StarOrthogonal m v u := ⟨fun h => h.symm,fun h => h.symm⟩

theorem StarOrthogonal.smul {m : ℕ} {u v : TraceZero F}
    (h : StarOrthogonal m u v) (a b : F) : StarOrthogonal m (a • u) (b • v) := by
  rcases h with ⟨h,he⟩
  refine ⟨starDomain_smul_right b (starDomain_smul_left a h),?_⟩
  rw [proposedPartialProduct_smul (thetaInv F m).toRingHom a b u v h,he,smul_zero]

theorem starOrthogonal_units_smul_iff (m : ℕ) (a b : Fˣ) (u v : TraceZero F) :
    StarOrthogonal m (a • u) (b • v) ↔ StarOrthogonal m u v := by
  simp only [Units.smul_def]
  constructor
  · intro h
    have hi := h.smul (a : F)⁻¹ (b : F)⁻¹
    simpa only [smul_smul,inv_mul_cancel₀ a.ne_zero,inv_mul_cancel₀ b.ne_zero,one_smul] using hi
  · intro h
    exact h.smul (a : F) (b : F)

theorem StarOrthogonal.map_model {m : ℕ} {u v : TraceZero F}
    (h : StarOrthogonal m u v) (g : Model F m) : StarOrthogonal m (g.val u) (g.val v) := by
  rcases h with ⟨h,he⟩
  obtain ⟨hp,hg⟩ := (mem_modelSubgroup_iff m g.val).mp g.property
  refine ⟨(starDomain_polynomialStabilizer_iff ⟨g.val,hp⟩ u v).mpr h,?_⟩
  rw [hg u v h,he,map_zero]

theorem starOrthogonal_model_iff {m : ℕ} (g : Model F m) (u v : TraceZero F) :
    StarOrthogonal m (g.val u) (g.val v) ↔ StarOrthogonal m u v := by
  constructor
  · intro h
    have hi := h.map_model g⁻¹
    change StarOrthogonal m (g.val.symm (g.val u)) (g.val.symm (g.val v)) at hi
    simpa only [LinearEquiv.symm_apply_apply] using hi
  · intro h
    exact h.map_model g

theorem starOrthogonal_mk_reps_iff (m : ℕ) (u v : TraceZero F) (hu : u ≠ 0) (hv : v ≠ 0) :
    StarOrthogonal m (Projectivization.mk F u hu).rep (Projectivization.mk F v hv).rep ↔
      StarOrthogonal m u v := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F u hu
  obtain ⟨b,hb⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  rw [←ha,←hb]
  exact starOrthogonal_units_smul_iff m a b u v

/-- Distinct intrinsic special points joined by zero partial product. -/
def SpecialAdjacent (m : ℕ) (p q : SpecialPoints (F := F) m) : Prop :=
  p ≠ q ∧ StarOrthogonal m p.val.rep q.val.rep

theorem specialAdjacent_symm (m : ℕ) (p q : SpecialPoints (F := F) m)
    (h : SpecialAdjacent m p q) : SpecialAdjacent m q p := ⟨Ne.symm h.1,h.2.symm⟩

theorem specialAdjacent_irrefl (m : ℕ) (p : SpecialPoints (F := F) m) :
    ¬SpecialAdjacent m p p := fun h => h.1 rfl

theorem specialAdjacent_mk_iff (m : ℕ) (u v : TraceZero F)
    (hu : IsSpecialVector m u) (hv : IsSpecialVector m v) :
    SpecialAdjacent m (specialPointMk m u hu) (specialPointMk m v hv) ↔
      (specialPointMk m u hu ≠ specialPointMk m v hv ∧ StarOrthogonal m u v) := by
  exact and_congr Iff.rfl (starOrthogonal_mk_reps_iff m u v hu.ne_zero hv.ne_zero)

theorem specialAdjacent_model_iff (m : ℕ) (g : Model F m)
    (p q : SpecialPoints (F := F) m) :
    SpecialAdjacent m (g • p) (g • q) ↔ SpecialAdjacent m p q := by
  have hrep (r : SpecialPoints (F := F) m) :
      (g • r).val = Projectivization.mk F (g.val r.val.rep)
        (fun h => r.val.rep_nonzero (g.val.injective (h.trans (map_zero g.val).symm))) := by
    calc
      (g • r).val = g.val • r.val := rfl
      _ = g.val • Projectivization.mk F r.val.rep r.val.rep_nonzero :=
        congrArg (fun z => g.val • z) (Projectivization.mk_rep r.val).symm
      _ = _ := rfl
  have hs : StarOrthogonal m (g • p).val.rep (g • q).val.rep ↔
      StarOrthogonal m p.val.rep q.val.rep := by
    rw [hrep p,hrep q,starOrthogonal_mk_reps_iff]
    exact starOrthogonal_model_iff g _ _
  exact and_congr (not_congr (smul_left_cancel_iff g)) hs

end Atlas.ReeF4
