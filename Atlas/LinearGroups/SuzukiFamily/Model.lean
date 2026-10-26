import Atlas.LinearGroups.SuzukiFamily.SymplecticEmbedding
import Atlas.LinearGroups.SuzukiFamily.Unipotent
import Atlas.LinearGroups.SuzukiFamily.Torus

/-! The primary Suzuki group is the generated subgroup of the retained Sp4 model. -/
noncomputable section
namespace Atlas.SuzukiFamily
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem h_symplectic (m : ℕ) (t : Fˣ) :
    toStandard (h m t) ∈ Matrix.symplecticGroup (Fin 2) F := by
  have ht : (t:F) ≠ 0 := Units.ne_zero t
  have hθ : theta F m (t:F) ≠ 0 := (map_ne_zero (theta F m)).mpr ht
  rw [SymplecticGroup.mem_iff']
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_succ,Matrix.J,
      Matrix.fromBlocks,Matrix.one_apply,coordinateIndex,h,Matrix.diagonal_apply,-theta_apply] <;>
    norm_num [Finset.filter_singleton] <;> field_simp
  all_goals change (1:F)=1; rfl

def rootElement (m : ℕ) (a b : F) : Atlas.Symplectic.Sp 2 F :=
  ⟨toStandard (u m a b),u_symplectic m a b⟩
def torusElement (m : ℕ) (t : Fˣ) : Atlas.Symplectic.Sp 2 F :=
  ⟨toStandard (h m t),h_symplectic m t⟩
def weylElement : Atlas.Symplectic.Sp 2 F := ⟨toStandard w,w_symplectic⟩

def generated (m : ℕ) : Subgroup (Atlas.Symplectic.Sp 2 F) :=
  Subgroup.closure (Set.range (fun p : F × F => rootElement m p.1 p.2) ∪
    Set.range (torusElement (F := F) m) ∪ {weylElement})

/-- Actual generated matrix subgroup; cardinality hypotheses are required by its theorems. -/
abbrev Group (F : Type*) [Field F] [Finite F] [CharP F 2] (m : ℕ) :=
  ↥(generated (F := F) m)

theorem rootElement_mem (m : ℕ) (a b : F) : rootElement m a b ∈ generated m :=
  Subgroup.subset_closure (Or.inl (Or.inl ⟨(a,b),rfl⟩))
theorem torusElement_mem (m : ℕ) (t : Fˣ) : torusElement m t ∈ generated m :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨t,rfl⟩))
theorem weylElement_mem (m : ℕ) : (weylElement : Atlas.Symplectic.Sp 2 F) ∈ generated m :=
  Subgroup.subset_closure (Or.inr rfl)

def embedding (m : ℕ) : Group F m →* Atlas.Symplectic.Sp 2 F := (generated m).subtype

theorem embedding_injective (m : ℕ) : Function.Injective (embedding (F := F) m) :=
  Subtype.val_injective

theorem finite_group (m : ℕ) : Finite (Group F m) := inferInstance
end Atlas.SuzukiFamily
