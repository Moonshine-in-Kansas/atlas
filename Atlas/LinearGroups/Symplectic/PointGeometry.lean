import Atlas.LinearGroups.Symplectic.OrthogonalFrame
import Atlas.LinearGroups.Symplectic.ProjectiveGeneration

noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

/-- Orthogonality of actual projective lines in the retained alternating form. -/
def Orthogonal (p q : Points n F) : Prop := form p.rep q.rep = 0

theorem orthogonal_mk {x y : Vector n F} (hx : x ≠ 0) (hy : y ≠ 0) :
    Orthogonal (Projectivization.mk F x hx) (Projectivization.mk F y hy) ↔ form x y = 0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F x hx
  obtain ⟨b,hb⟩ := Projectivization.exists_smul_eq_mk_rep F y hy
  unfold Orthogonal
  rw [← ha,← hb]
  simp [Units.smul_def,map_smul]

@[simp] theorem orthogonal_self (p : Points n F) : Orthogonal p p := form_self _

theorem orthogonal_symm {p q : Points n F} (h : Orthogonal p q) : Orthogonal q p := by
  unfold Orthogonal at *
  rw [form_swap,h,neg_zero]

theorem orthogonal_smul (g : Sp n F) (p q : Points n F) :
    Orthogonal (g • p) (g • q) ↔ Orthogonal p q := by
  rw [← Projectivization.mk_rep p,← Projectivization.mk_rep q,
    Projectivization.smul_mk,Projectivization.smul_mk,orthogonal_mk,orthogonal_mk]
  simp only [smul_eq_mulVec,preserves]

theorem projective_orthogonal_smul (g : PSp n F) (p q : Points n F) :
    Orthogonal (g • p) (g • q) ↔ Orthogonal p q := by
  obtain ⟨g,rfl⟩ := projection_surjective g
  exact orthogonal_smul g p q

theorem e_nonzero (i : Fin n) : e (F := F) i ≠ 0 := by
  intro h
  have := congrFun h (.inl i)
  simp [e] at this

theorem f_nonzero (i : Fin n) : f (F := F) i ≠ 0 := by
  intro h
  have := congrFun h (.inr i)
  simp [f] at this

def ePoint (i : Fin n) : Points n F := Projectivization.mk F (e i) (e_nonzero i)
def fPoint (i : Fin n) : Points n F := Projectivization.mk F (f i) (f_nonzero i)

/-- Normalize two distinct orthogonal lines using actual partial-frame extension. -/
theorem normalize_orthogonal_pair (n : ℕ) (p q : Points (n+2) F)
    (hpq : p ≠ q) (ho : Orthogonal p q) :
    ∃ g : Sp (n+2) F, g • p = ePoint 0 ∧ g • q = ePoint 1 := by
  have hq : q.rep ∉ Submodule.span F {p.rep} := by
    intro h
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp h
    apply hpq
    rw [← Projectivization.mk_rep p,← Projectivization.mk_rep q]
    apply Eq.symm
    exact (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨a,ha⟩
  obtain ⟨k,hkp,hkq⟩ := exists_isometry_orthogonal_pair n (form (n := n+2) (F := F)) form_alternating
    form_nondegenerate (by simp [Vector,Index,Module.finrank_pi,two_mul])
    p.rep q.rep p.rep_nonzero hq ho
  refine ⟨ofLinear k.toLinearEquiv k.map_app',?_,?_⟩
  · rw [← Projectivization.mk_rep p,Projectivization.smul_mk]
    simp only [ofLinear_apply,ePoint]
    change Projectivization.mk F (k p.rep) _ = _
    simp only [hkp]
  · rw [← Projectivization.mk_rep q,Projectivization.smul_mk]
    simp only [ofLinear_apply,ePoint]
    change Projectivization.mk F (k q.rep) _ = _
    simp only [hkq]

/-- Normalize a nonorthogonal pair without using a group order or generation premise. -/
theorem normalize_nonorthogonal_pair (n : ℕ) (p q : Points (n+1) F)
    (ho : ¬ Orthogonal p q) :
    ∃ g : Sp (n+1) F, g • p = ePoint 0 ∧ g • q = fPoint 0 := by
  have hc : form p.rep q.rep ≠ 0 := ho
  let v := (form p.rep q.rep)⁻¹ • q.rep
  have hv : v ≠ 0 := smul_ne_zero (inv_ne_zero hc) q.rep_nonzero
  have hpv : form p.rep v = 1 := by simp [v,map_smul,hc]
  have hqv : q = Projectivization.mk F v hv := by
    rw [← Projectivization.mk_rep q]
    apply Eq.symm
    exact (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨_,rfl⟩
  obtain ⟨k,hkp,hkv⟩ := exists_isometry_pair n form form_alternating
    form_nondegenerate (by simp [Vector,Index,Module.finrank_pi,two_mul]) p.rep v hpv
  refine ⟨ofLinear k.toLinearEquiv k.map_app',?_,?_⟩
  · rw [← Projectivization.mk_rep p,Projectivization.smul_mk]
    simp only [ofLinear_apply,ePoint]
    change Projectivization.mk F (k p.rep) _ = _
    simp only [hkp]
  · rw [hqv,Projectivization.smul_mk]
    simp only [ofLinear_apply,fPoint]
    change Projectivization.mk F (k v) _ = _
    simp only [hkv]

end Atlas.Symplectic
