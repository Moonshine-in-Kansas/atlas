import Atlas.LinearGroups.SuzukiFamily.GroupRelations
import Atlas.LinearGroups.Symplectic.FieldTransport

/-! Entrywise transport of the actual Suzuki subgroup along a field isomorphism. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F K : Type*} [Field F] [Finite F] [CharP F 2]
  [Field K] [Finite K] [CharP K 2]

@[simp] theorem matrix_fieldEquiv (e : F ≃+* K) (g : Atlas.Symplectic.Sp 2 F) :
    matrix (Atlas.Symplectic.fieldEquivSp e g)=(matrix g).map e := by
  rfl

theorem transport_root (e : F ≃+* K) (m : ℕ) (a b : F) :
    Atlas.Symplectic.fieldEquivSp e (rootElement m a b)=rootElement m (e a) (e b) := by
  apply matrix_injective
  simp only [matrix_fieldEquiv,matrix_root]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u,norm,-theta_apply,map_theta]

theorem transport_torus (e : F ≃+* K) (m : ℕ) (t : Fˣ) :
    Atlas.Symplectic.fieldEquivSp e (torusElement m t)=
      torusElement m (Units.mapEquiv e.toMulEquiv t) := by
  apply matrix_injective
  simp only [matrix_fieldEquiv,matrix_torus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h,Matrix.diagonal_apply,-theta_apply,map_theta]

theorem transport_weyl (e : F ≃+* K) :
    Atlas.Symplectic.fieldEquivSp e (weylElement : Atlas.Symplectic.Sp 2 F)=weylElement := by
  apply matrix_injective
  simp only [matrix_fieldEquiv,matrix_weyl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w]

theorem transport_mem_generated (e : F ≃+* K) (m : ℕ) {g : Atlas.Symplectic.Sp 2 F}
    (hg : g ∈ generated m) : Atlas.Symplectic.fieldEquivSp e g ∈ generated m := by
  have hle : generated (F := F) m ≤
      (generated (F := K) m).comap (Atlas.Symplectic.fieldEquivSp e).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change Atlas.Symplectic.fieldEquivSp e g ∈ generated m
    rcases hg with ((⟨⟨a,b⟩,rfl⟩ | ⟨t,rfl⟩) | hw)
    · rw [transport_root]
      exact rootElement_mem m (e a) (e b)
    · rw [transport_torus]
      exact torusElement_mem m _
    · have he : g=weylElement := Set.mem_singleton_iff.mp hw
      subst g
      rw [transport_weyl]
      exact weylElement_mem m
  exact hle hg

def fieldEquiv (e : F ≃+* K) (m : ℕ) : Group F m ≃* Group K m where
  toFun g := ⟨Atlas.Symplectic.fieldEquivSp e g.val,transport_mem_generated e m g.property⟩
  invFun g := ⟨Atlas.Symplectic.fieldEquivSp e.symm g.val,transport_mem_generated e.symm m g.property⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    exact e.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply _
  map_mul' g h := Subtype.ext ((Atlas.Symplectic.fieldEquivSp e).map_mul g.val h.val)

@[simp] theorem fieldEquiv_embedding (e : F ≃+* K) (m : ℕ) (g : Group F m) :
    embedding m (fieldEquiv e m g)=Atlas.Symplectic.fieldEquivSp e (embedding m g) := rfl
end Atlas.SuzukiFamily
