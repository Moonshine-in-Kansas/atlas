import Atlas.LinearGroups.F4.PointFiltration

/-! The intrinsic nine-dimensional middle image and its eight-dimensional quotient
at the marked C₀ point. These are linear spaces, not asserted Spin representations. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def parabolicTrace : Carrier F →ₗ[F] F where
  toFun := trace
  map_add' x y := by simp [trace]; ring
  map_smul' t x := by simp [trace,_root_.mul_add]

def parabolicImageZero : Submodule F (Carrier F) :=
  (parabolicCross (F:=F)).range ⊓ (parabolicTrace (F:=F)).ker

def parabolicTraceOnImage : (parabolicCross (F:=F)).range →ₗ[F] F :=
  parabolicTrace.comp (parabolicCross (F:=F)).range.subtype

def traceImageKernelEquiv : (parabolicTraceOnImage (F:=F)).ker ≃ₗ[F] parabolicImageZero (F:=F) where
  toFun x := ⟨x.val.val,x.val.prop,x.prop⟩
  invFun x := ⟨⟨x.val,x.prop.1⟩,x.prop.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem parabolicTraceOnImage_surjective : Function.Surjective (parabolicTraceOnImage (F:=F)) := by
  intro t
  let x : Carrier F := (0,![0,0,![0,0,0,0,0,0,0,-t]])
  refine ⟨⟨parabolicCross x,⟨x,rfl⟩⟩,?_⟩
  change trace (parabolicCross x)=t
  rw [parabolicCross_coordinates]
  simp [trace,x]

theorem parabolicImageZero_finrank : Module.finrank F (parabolicImageZero (F:=F))=9 := by
  have h := (parabolicTraceOnImage (F:=F)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr parabolicTraceOnImage_surjective,finrank_top,
    Module.finrank_self,parabolicCross_range_finrank] at h
  rw [←traceImageKernelEquiv.finrank_eq]
  omega

theorem parabolicVector_mem_imageZero : parabolicVector (F:=F)∈parabolicImageZero := by
  refine ⟨?_,?_⟩
  · refine ⟨(![0,0,-1],0),?_⟩
    rw [parabolicCross_coordinates]
    apply Prod.ext
    · ext i; fin_cases i <;> simp [parabolicVector]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [parabolicVector]
  · change trace parabolicVector=0
    simp [parabolicVector,trace]

theorem parabolicVector_ne_zero : parabolicVector (F:=F)≠0 := by
  intro h
  have := congrArg (fun x : Carrier F=>x.2 2 0) h
  exact one_ne_zero this

def parabolicImageLine : Submodule F (parabolicImageZero (F:=F)) :=
  Submodule.span F {⟨parabolicVector,parabolicVector_mem_imageZero⟩}

theorem parabolicImageLine_finrank : Module.finrank F (parabolicImageLine (F:=F))=1 := by
  apply finrank_span_singleton
  intro h
  exact parabolicVector_ne_zero (congrArg Subtype.val h)

theorem parabolicImageQuotient_finrank :
    Module.finrank F ((parabolicImageZero (F:=F)) ⧸ (parabolicImageLine (F:=F)))=8 := by
  have h := (parabolicImageLine (F:=F)).finrank_quotient_add_finrank
  rw [parabolicImageLine_finrank,parabolicImageZero_finrank] at h
  omega

end Atlas.F4
