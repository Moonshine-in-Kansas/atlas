import Atlas.LinearGroups.ReeF4.RootVectors

/-! A genuine basis for the 26-space, with two independent diagonal labels and
all 24 short-root vectors. The third diagonal label remains dependent. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def markedIndexSwap : TraceZeroCoordinate ≃ TraceZeroCoordinate :=
  Equiv.sumCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl _)

def markedBasis : Module.Basis TraceZeroCoordinate F (TraceZero F) :=
  ((Pi.basisFun F TraceZeroCoordinate).map traceZeroCoordinateEquiv.symm).reindex markedIndexSwap

private theorem coordinate_inl (w : TraceZero F) (i : Fin 2) :
    traceZeroCoordinateEquiv w (.inl i) = w.val.1 (Fin.castLE (by decide) i) := rfl

private theorem coordinate_inr (w : TraceZero F) (i : ShortRootLabel) :
    traceZeroCoordinateEquiv w (.inr i) = w.val.2 i.1 i.2 := rfl

theorem markedBasis_root (r : ShortRootLabel) : markedBasis (F:=F) (.inr r) = rootVector r := by
  apply traceZeroCoordinateEquiv.injective
  simp only [markedBasis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    Pi.basisFun_apply, LinearEquiv.apply_symm_apply]
  change Pi.single (.inr r) (1 : F) = traceZeroCoordinateEquiv (rootVector r)
  funext i
  cases i with
  | inl i => rw [coordinate_inl]; simp [rootVector, Pi.single_apply]
  | inr i =>
    rw [coordinate_inr]
    by_cases h0 : i.1 = r.1 <;> by_cases h1 : i.2 = r.2 <;>
      simp [rootVector, Pi.single_apply, Prod.ext_iff, h0, h1]

theorem markedBasis_diagonal (i : Fin 2) :
    markedBasis (F:=F) (.inl i) = diagonalVector (Fin.castLE (by decide) i) := by
  apply traceZeroCoordinateEquiv.injective
  simp only [markedBasis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    Pi.basisFun_apply, LinearEquiv.apply_symm_apply]
  funext j
  fin_cases i <;> cases j with
  | inl j =>
      rw [coordinate_inl]
      fin_cases j <;>
        simp [markedIndexSwap, Equiv.swap_apply_def, diagonalVector,
          traceZeroProjection, unit, trace, Pi.single_apply, CharTwo.neg_eq]
  | inr j =>
      rw [coordinate_inr]
      simp [markedIndexSwap, Equiv.swap_apply_def, diagonalVector,
        traceZeroProjection, unit, trace, Pi.single_apply]

end Atlas.ReeF4
