import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic

noncomputable section
namespace Atlas.LinearGroups.UnitriangularFour
open Matrix
open scoped MatrixGroups
variable (F : Type*) [Field F]

def mat (v : Fin 6 → F) : Matrix (Fin 4) (Fin 4) F :=
  !![1,v 0,v 1,v 2;0,1,v 3,v 4;0,0,1,v 5;0,0,0,1]

def element (v : Fin 6 → F) : SL(4,F) := ⟨mat F v, by
  have ht : (mat F v).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [mat]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [mat,Fin.prod_univ_succ]⟩

def product (v w : Fin 6 → F) : Fin 6 → F :=
  ![v 0+w 0, v 1+w 1+v 0*w 3, v 2+w 2+v 0*w 4+v 1*w 5,
    v 3+w 3, v 4+w 4+v 3*w 5, v 5+w 5]
def inverse (v : Fin 6 → F) : Fin 6 → F :=
  ![-v 0, v 0*v 3-v 1, -v 2+v 0*v 4+v 1*v 5-v 0*v 3*v 5,
    -v 3, v 3*v 5-v 4, -v 5]

theorem element_injective : Function.Injective (element F) := by
  intro v w h
  have h0 := congrArg (fun g : SL(4,F) => g.val 0 1) h
  have h1 := congrArg (fun g : SL(4,F) => g.val 0 2) h
  have h2 := congrArg (fun g : SL(4,F) => g.val 0 3) h
  have h3 := congrArg (fun g : SL(4,F) => g.val 1 2) h
  have h4 := congrArg (fun g : SL(4,F) => g.val 1 3) h
  have h5 := congrArg (fun g : SL(4,F) => g.val 2 3) h
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem element_zero : element F 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [element,mat]

theorem element_mul (v w : Fin 6 → F) : element F v * element F w = element F (product F v w) := by
  apply Subtype.ext
  change mat F v * mat F w = mat F (product F v w)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat,product,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

theorem element_inv (v : Fin 6 → F) : (element F v)⁻¹ = element F (inverse F v) := by
  apply inv_eq_of_mul_eq_one_right
  rw [element_mul, ← element_zero F]
  congr 1
  funext i
  fin_cases i <;> simp [product,inverse] <;> ring

def subgroup : Subgroup SL(4,F) where
  carrier := Set.range (element F)
  one_mem' := ⟨0,element_zero F⟩
  mul_mem' := by rintro a b ⟨v,rfl⟩ ⟨w,rfl⟩; exact ⟨product F v w,(element_mul F v w).symm⟩
  inv_mem' := by rintro a ⟨v,rfl⟩; exact ⟨inverse F v,(element_inv F v).symm⟩

def member (v : Fin 6 → F) : subgroup F := ⟨element F v,⟨v,rfl⟩⟩
theorem member_injective : Function.Injective (member F) := fun _ _ h =>
  element_injective F (congrArg Subtype.val h)
theorem member_surjective : Function.Surjective (member F) := by
  rintro ⟨g,v,hv⟩
  exact ⟨v,Subtype.ext hv⟩

def parameterEquiv : (Fin 6 → F) ≃ subgroup F :=
  Equiv.ofBijective (member F) ⟨member_injective F,member_surjective F⟩

theorem card [Finite F] : Nat.card (subgroup F) = Nat.card F ^ 6 := by
  rw [← Nat.card_congr (parameterEquiv F),Nat.card_fun,Nat.card_fin]

theorem member_mul (v w : Fin 6 → F) : member F v * member F w = member F (product F v w) :=
  Subtype.ext (element_mul F v w)

theorem member_center_iff (v : Fin 6 → F) : member F v ∈ Subgroup.center (subgroup F) ↔
    v 0 = 0 ∧ v 1 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := by
  constructor
  · intro h
    have hc := Subgroup.mem_center_iff.mp h
    have h0 := congrArg (fun g : subgroup F => g.val.val 0 2) (hc (member F ![0,0,0,1,0,0]))
    have h1 := congrArg (fun g : subgroup F => g.val.val 0 3) (hc (member F ![0,0,0,0,0,1]))
    have h3 := congrArg (fun g : subgroup F => g.val.val 0 2) (hc (member F ![1,0,0,0,0,0]))
    have h4 := congrArg (fun g : subgroup F => g.val.val 0 3) (hc (member F ![1,0,0,0,0,0]))
    have h5 := congrArg (fun g : subgroup F => g.val.val 1 3) (hc (member F ![0,0,0,1,0,0]))
    rw [member_mul,member_mul] at h0 h1 h3 h4 h5
    simp [member,element,mat,product] at h0 h1 h3 h4 h5
    exact ⟨h0,h1,h3,h4,h5⟩
  · rintro ⟨h0,h1,h3,h4,h5⟩
    apply Subgroup.mem_center_iff.mpr
    intro g
    obtain ⟨w,rfl⟩ := member_surjective F g
    rw [member_mul,member_mul]
    congr 1
    funext i
    fin_cases i <;> simp [product,h0,h1,h3,h4,h5] <;> ring

def central (c : F) : Subgroup.center (subgroup F) :=
  ⟨member F ![0,0,c,0,0,0], (member_center_iff F _).mpr ⟨rfl,rfl,rfl,rfl,rfl⟩⟩

def centerEquiv : F ≃ Subgroup.center (subgroup F) := Equiv.ofBijective (central F) (by
  constructor
  · intro c d h
    exact congrArg (fun g : Subgroup.center (subgroup F) => g.val.val.val 0 3) h
  · intro g
    obtain ⟨v,hv⟩ := member_surjective F g.val
    have hp := (member_center_iff F v).mp (hv.symm ▸ g.property)
    refine ⟨v 2,?_⟩
    apply Subtype.ext
    rw [←hv]
    apply congrArg (member F)
    funext i
    fin_cases i <;> simp [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2])

theorem center_card : Nat.card (Subgroup.center (subgroup F)) = Nat.card F :=
  (Nat.card_congr (centerEquiv F)).symm

end Atlas.LinearGroups.UnitriangularFour
