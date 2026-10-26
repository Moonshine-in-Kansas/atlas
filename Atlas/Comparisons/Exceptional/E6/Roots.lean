import Atlas.Comparisons.Exceptional.E6.RootBounds

/-! Exhaustion of the actual integral roots by a proved finite coordinate box. -/
namespace Atlas.Comparisons.E6Lattice

abbrev Root := {x : Fin 6 → ℤ // norm x = 1}

def RootBox := (i : Fin 6) → Fin (2 * (rootBound i).toNat + 1)
  deriving Fintype, DecidableEq

def boxVector (b : RootBox) : Fin 6 → ℤ := fun i => (b i).val - rootBound i

theorem rootBound_nonneg (i : Fin 6) : 0 ≤ rootBound i := by
  fin_cases i <;> decide

def rootBoxEncode (x : Root) : RootBox := fun i =>
  ⟨(x.val i + rootBound i).toNat, by
    have h := root_coordinate_bounds x.val x.property i
    have hb := rootBound_nonneg i
    omega⟩

@[simp] theorem boxVector_encode (x : Root) : boxVector (rootBoxEncode x) = x.val := by
  funext i
  have h := root_coordinate_bounds x.val x.property i
  simp only [boxVector,rootBoxEncode]
  omega

def rootEquivBox : Root ≃ {b : RootBox // norm (boxVector b) = 1} where
  toFun x := ⟨rootBoxEncode x,by rw [boxVector_encode]; exact x.property⟩
  invFun b := ⟨boxVector b.val,b.property⟩
  left_inv x := Subtype.ext (boxVector_encode x)
  right_inv b := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    simp only [rootBoxEncode,boxVector]
    have hi := (b.val i).isLt
    have hb := rootBound_nonneg i
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaust the proved 7875-element coordinate box using ordinary kernel reduction.
theorem card_box_roots :
    Fintype.card {b : RootBox // norm (boxVector b) = 1} = 72 := by decide

instance : Finite Root := Finite.of_equiv _ rootEquivBox.symm

theorem card_roots : Nat.card Root = 72 := by
  rw [Nat.card_congr rootEquivBox, Nat.card_eq_fintype_card]
  exact card_box_roots

end Atlas.Comparisons.E6Lattice
