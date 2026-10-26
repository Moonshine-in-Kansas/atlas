import Atlas.LinearGroups.F4.ScalarTorusActions
import Atlas.LinearGroups.Orthogonal.Basic

/-! Exact coordinates on the intrinsic nine-space at the marked C₀ point.
Its rank-one equation is a split eight-dimensional quadratic equation with a
free C₀ coordinate. No orbit or transitivity of a Spin group is assumed. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def nearVector (c : F) (v : Fin 8 → F) : Carrier F :=
  upperSpinEmbed v+c • parabolicVector

def nearSpinCoordinates (x : Carrier F) : Fin 8 → F :=
  ![x.2 0 0,x.2 0 1,x.2 0 2,x.2 0 3,x.2 1 0,x.2 1 1,x.2 1 2,x.2 1 4]

def nearQuadratic (v : Fin 8 → F) : F := v 0*v 7-v 1*v 6+v 2*v 5+v 3*v 4

@[simp] theorem nearVector_C0 (c : F) (v : Fin 8 → F) : (nearVector c v).2 2 0=c := by
  simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector]

@[simp] theorem nearVector_spin (c : F) (v : Fin 8 → F) :
    nearSpinCoordinates (nearVector c v)=v := by
  ext i; fin_cases i <;> simp [nearSpinCoordinates,nearVector,upperSpinEmbed,parabolicVector]

theorem nearVector_trace (c : F) (v : Fin 8 → F) : trace (nearVector c v)=0 := by
  simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector,trace]

theorem nearVector_mem_imageZero (c : F) (v : Fin 8 → F) :
    nearVector c v∈parabolicImageZero (F:=F) := by
  refine ⟨?_,nearVector_trace c v⟩
  refine ⟨(![0,0,-c],
    ![![0,0,0,0,-v 4,-v 5,v 6,-v 7],![0,0,0,-v 0,0,v 1,-v 2,-v 3],0]),?_⟩
  rw [parabolicCross_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector]

theorem nearVector_reconstruction (x : Carrier F) (hx : x∈parabolicImageZero (F:=F)) :
    nearVector (x.2 2 0) (nearSpinCoordinates x)=x := by
  obtain ⟨⟨y,rfl⟩,ht⟩ := hx
  have hy : y.2 2 7=0 := by
    change trace (parabolicCross y)=0 at ht
    rw [parabolicCross_coordinates] at ht
    simpa [trace] using ht
  rw [parabolicCross_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector,hy]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead,Matrix.vecTail,nearVector,nearSpinCoordinates,upperSpinEmbed,parabolicVector]

def nearImageChart : (F × (Fin 8 → F)) ≃ₗ[F] parabolicImageZero (F:=F) where
  toFun w := ⟨nearVector w.1 w.2,nearVector_mem_imageZero w.1 w.2⟩
  invFun x := (x.val.2 2 0,nearSpinCoordinates x.val)
  left_inv w := by simp
  right_inv x := Subtype.ext (nearVector_reconstruction x.val x.prop)
  map_add' v w := by
    apply Subtype.ext
    apply Prod.ext
    · ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector]
  map_smul' t w := by
    apply Subtype.ext
    apply Prod.ext
    · ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector,mul_assoc]

set_option maxHeartbeats 900000 in
theorem nearVector_adjoint (c : F) (v : Fin 8 → F) :
    adjoint (nearVector c v)= -nearQuadratic v • parabolicVector := by
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector,adjoint,SplitOctonion.norm]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecHead,Matrix.vecTail,nearVector,upperSpinEmbed,parabolicVector,nearQuadratic,adjoint,
        SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit] <;> ring

theorem nearVector_rankOne_iff (c : F) (v : Fin 8 → F) :
    adjoint (nearVector c v)=0 ↔ nearQuadratic v=0 := by
  rw [nearVector_adjoint]
  constructor
  · intro h
    have hc := congrArg (fun x : Carrier F=>x.2 2 0) h
    simpa [parabolicVector] using hc
  · intro h
    rw [h,neg_zero,zero_smul]

theorem imageZero_rankOne_iff (x : Carrier F) (hx : x∈parabolicImageZero (F:=F)) :
    adjoint x=0 ↔ nearQuadratic (nearSpinCoordinates x)=0 := by
  conv_lhs => rw [←nearVector_reconstruction x hx]
  exact nearVector_rankOne_iff _ _

def nearHyperbolicEquiv : (Fin 8 → F) ≃ₗ[F] Atlas.Orthogonal.VectorD 4 F where
  toFun v := Sum.elim ![v 0,v 1,v 2,v 3] ![v 7,-v 6,v 5,v 4]
  invFun v := ![v (.inl 0),v (.inl 1),v (.inl 2),v (.inl 3),
    v (.inr 3),v (.inr 2),-v (.inr 1),v (.inr 0)]
  left_inv v := by ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail]
  right_inv v := by
    ext i; cases i with
    | inl i => fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail]
    | inr i => fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail]
  map_add' v w := by
    ext i; cases i with
    | inl i => fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail]
    | inr i => fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail] <;> ring
  map_smul' t v := by
    ext i; cases i with
    | inl i => fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail]
    | inr i => fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail]

theorem nearQuadratic_hyperbolic (v : Fin 8 → F) :
    nearQuadratic v=Atlas.Orthogonal.formD 4 F (nearHyperbolicEquiv v) := by
  simp [nearQuadratic,Atlas.Orthogonal.formD_apply,nearHyperbolicEquiv,Fin.sum_univ_succ]
  ring

end Atlas.F4
