import Atlas.LinearGroups.Triality.WeylSubgroup
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-! The actual torus–Weyl quotient is the dihedral group I₂(6). -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal

def weylListIndex (l : List Bool) : Fin 12 := l.foldr weylLeftIndex 0
def weylProductIndex (w v : Fin 12) : Fin 12 := weylListIndex (weylWord w ++ weylWord v)

def indexDihedral (w : Fin 12) : DihedralGroup 6 :=
  ((weylWord w).map fun s => if s then DihedralGroup.sr 0 else DihedralGroup.sr 1).prod

theorem indexDihedral_injective : Function.Injective indexDihedral := by decide

theorem indexDihedral_mul : ∀ w v : Fin 12,
    indexDihedral (weylProductIndex w v)=indexDihedral w*indexDihedral v := by decide

def indexDihedralEquiv : Fin 12 ≃ DihedralGroup 6 := Equiv.ofBijective indexDihedral
  ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨indexDihedral_injective,by rw [Nat.card_fin,DihedralGroup.nat_card]⟩)

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem weylList_torus_index (l : List Bool) : ∃ h : Kˣ × Fˣ,
    (l.map fun s => if s then shortWeyl F K else longWeyl F K).prod =
      weylLift F K (weylListIndex l)*torusMap F K h := by
  induction l with
  | nil => exact ⟨1,by simp [weylListIndex,weylLift,weylWord]⟩
  | cons s l ih =>
    obtain ⟨h,hh⟩ := ih
    refine ⟨weylLeftTorus F K s (weylListIndex l)*h,?_⟩
    rw [List.map_cons,List.prod_cons,hh,← mul_assoc,weylLeft_mul,map_mul]
    simp [weylListIndex,mul_assoc]

theorem weylLift_mul_index (w v : Fin 12) : ∃ h : Kˣ × Fˣ,
    weylLift F K w*weylLift F K v = weylLift F K (weylProductIndex w v)*torusMap F K h := by
  simpa [weylLift,weylProductIndex,List.map_append,List.prod_append] using
    weylList_torus_index F K (weylWord w ++ weylWord v)

abbrev WeylQuotient := weylSubgroup F K hdeg ⧸ (torus F K).subgroupOf (weylSubgroup F K hdeg)

def weylRepresentative (w : Fin 12) : weylSubgroup F K hdeg :=
  ⟨weylLift F K w,⟨(w,1),by simp [weylTorusWord]⟩⟩

def weylClass (w : Fin 12) : WeylQuotient F K hdeg := QuotientGroup.mk (weylRepresentative F K hdeg w)

theorem weylClass_mul (w v : Fin 12) :
    weylClass F K hdeg w * weylClass F K hdeg v = weylClass F K hdeg (weylProductIndex w v) := by
  obtain ⟨h,hh⟩ := weylLift_mul_index F K w v
  change QuotientGroup.mk (weylRepresentative F K hdeg w * weylRepresentative F K hdeg v) =
    QuotientGroup.mk (weylRepresentative F K hdeg (weylProductIndex w v))
  apply QuotientGroup.eq.mpr
  change (weylLift F K w * weylLift F K v)⁻¹ * weylLift F K (weylProductIndex w v) ∈ torus F K
  rw [hh]
  simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one] using (torus F K).inv_mem ⟨h,rfl⟩

theorem weylClass_injective : Function.Injective (weylClass F K hdeg) := by
  intro w v he
  have hh := QuotientGroup.eq.mp he
  change (weylLift F K w)⁻¹ * weylLift F K v ∈ torus F K at hh
  obtain ⟨h,hh⟩ := hh
  have hv : weylLift F K v * torusMap F K 1 = weylLift F K w * torusMap F K h := by
    rw [map_one,mul_one,hh]
    group
  exact (weylLift_torus_disjoint F K v w 1 h hv).symm

def dihedralToWeyl : DihedralGroup 6 →* WeylQuotient F K hdeg where
  toFun d := weylClass F K hdeg (indexDihedralEquiv.symm d)
  map_one' := by
    have h0 : indexDihedralEquiv.symm 1=0 := by
      apply indexDihedralEquiv.injective
      rw [indexDihedralEquiv.apply_symm_apply]
      rfl
    rw [h0]
    change QuotientGroup.mk (weylRepresentative F K hdeg 0)=1
    have hh : weylRepresentative F K hdeg 0=1 := by
      apply Subtype.ext
      simp [weylRepresentative,weylLift,weylWord]
    rw [hh]
    rfl
  map_mul' a b := by
    rw [weylClass_mul]
    congr 1
    apply indexDihedralEquiv.injective
    rw [indexDihedralEquiv.apply_symm_apply]
    change a*b=indexDihedral (weylProductIndex (indexDihedralEquiv.symm a) (indexDihedralEquiv.symm b))
    rw [indexDihedral_mul]
    exact (congrArg₂ (· * ·) (indexDihedralEquiv.apply_symm_apply a)
      (indexDihedralEquiv.apply_symm_apply b)).symm

def dihedralWeylEquiv : DihedralGroup 6 ≃* WeylQuotient F K hdeg :=
  MulEquiv.ofBijective (dihedralToWeyl F K hdeg)
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨
      (weylClass_injective F K hdeg).comp indexDihedralEquiv.symm.injective,
      by rw [DihedralGroup.nat_card,card_weylQuotient F K hdeg]⟩)

end Atlas.Triality
