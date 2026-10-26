import Atlas.LinearGroups.ReeF4.RootGroupSubgroup
import Atlas.LinearGroups.ReeF4.Weyl
import Atlas.LinearGroups.ReeF4.TorusDiagonal

/-! Explicit decomposition of the actual 26-space for the local Suzuki action:
four natural four-spaces, one six-space, and four fixed coordinates. The source
orders are reversed to retain the existing column-action matrix convention. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

/-- Four disjoint ordered natural blocks in the retained root labels. -/
def suzukiLeviBlockLabel (k i : Fin 4) : ShortRootLabel :=
  (![![(2,7),(1,7),(1,6),(2,6)], ![(2,1),(1,1),(1,0),(2,0)],
      ![(1,5),(2,5),(2,3),(1,4)], ![(1,3),(2,4),(2,2),(1,2)]]) k i

abbrev SuzukiLeviCoordinates (F : Type*) :=
  (Fin 4 → Fin 4 → F) × ((Fin 6 → F) × (Fin 4 → F))

variable {F : Type*} [CommRing F] [CharP F 2]

def suzukiLeviBlockProject (k : Fin 4) : TraceZero F →ₗ[F] (Fin 4 → F) where
  toFun w i := w.val.2 (suzukiLeviBlockLabel k i).1 (suzukiLeviBlockLabel k i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def suzukiLeviBlockEmbed (k : Fin 4) : (Fin 4 → F) →ₗ[F] TraceZero F where
  toFun v := ∑ i : Fin 4, v i • rootVector (suzukiLeviBlockLabel k i)
  map_add' u v := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem suzukiLeviBlockProject_embed (k : Fin 4) (v : Fin 4 → F) :
    suzukiLeviBlockProject k (suzukiLeviBlockEmbed k v) = v := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [suzukiLeviBlockProject, suzukiLeviBlockEmbed, suzukiLeviBlockLabel,
      Fin.sum_univ_succ, rootVector, Pi.single_apply, smul_eq_mul, Fin.ext_iff]

theorem suzukiLeviBlockEmbed_injective (k : Fin 4) :
    Function.Injective (suzukiLeviBlockEmbed (F := F) k) :=
  Function.LeftInverse.injective (suzukiLeviBlockProject_embed k)

/-- Six coordinates are in exterior basis order 01,02,03,12,13,23.
The two middle entries correspond to diagonal vectors d1,d2. -/
def suzukiLeviCoordinates (w : TraceZero F) : SuzukiLeviCoordinates F :=
  (fun k => suzukiLeviBlockProject k w,
    (![w.val.2 0 5,w.val.2 0 4,w.val.1 2,w.val.1 1,w.val.2 0 3,w.val.2 0 2],
      ![w.val.2 0 0,w.val.2 0 1,w.val.2 0 6,w.val.2 0 7]))

def suzukiLeviCoordinatesInverse (x : SuzukiLeviCoordinates F) : TraceZero F :=
  ⟨(![x.2.1 2+x.2.1 3,x.2.1 3,x.2.1 2],
    ![![x.2.2 0,x.2.2 1,x.2.1 5,x.2.1 4,x.2.1 1,x.2.1 0,x.2.2 2,x.2.2 3],
      ![x.1 1 2,x.1 1 1,x.1 3 3,x.1 3 0,x.1 2 3,x.1 2 0,x.1 0 2,x.1 0 1],
      ![x.1 1 3,x.1 1 0,x.1 3 2,x.1 2 2,x.1 3 1,x.1 2 1,x.1 0 3,x.1 0 0]]), by
    change (x.2.1 2+x.2.1 3)+x.2.1 3+x.2.1 2=0
    linear_combination (CharTwo.add_self_eq_zero (x.2.1 2)) +
      (CharTwo.add_self_eq_zero (x.2.1 3))⟩

private theorem suzukiLeviCoordinates_left_inverse (w : TraceZero F) :
    suzukiLeviCoordinatesInverse (suzukiLeviCoordinates w) = w := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i
    · change w.val.1 2+w.val.1 1=w.val.1 0
      have ht := w.property
      change w.val.1 0+w.val.1 1+w.val.1 2=0 at ht
      linear_combination -ht + (w.val.1 1+w.val.1 2)*(CharTwo.two_eq_zero (R := F))
    · rfl
    · rfl
  · funext k j
    fin_cases k <;> fin_cases j <;> rfl

private theorem suzukiLeviCoordinates_right_inverse (x : SuzukiLeviCoordinates F) :
    suzukiLeviCoordinates (suzukiLeviCoordinatesInverse x) = x := by
  apply Prod.ext
  · funext k i
    fin_cases k <;> fin_cases i <;> rfl
  · apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl

/-- An explicit linear decomposition of W, with a proved coordinate inverse. -/
def suzukiLeviCoordinatesEquiv : TraceZero F ≃ₗ[F] SuzukiLeviCoordinates F where
  toFun := suzukiLeviCoordinates
  invFun := suzukiLeviCoordinatesInverse
  left_inv := suzukiLeviCoordinates_left_inverse
  right_inv := suzukiLeviCoordinates_right_inverse
  map_add' u v := by
    apply Prod.ext
    · funext k i
      rfl
    · apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' a v := by
    apply Prod.ext
    · funext k i
      rfl
    · apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

end Atlas.ReeF4
