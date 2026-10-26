import Atlas.Rudvalis.LatticeShellClassification

/-! The norm-four shell has 112 coordinate vectors and 16128 code lifts. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def coordinateShellLift (a : Coordinate × Bool) : MinimalShell :=
  if a.2 then ⟨⟨coordinateMinimum a.1,coordinateMinimum_mem _⟩,coordinateMinimum_norm _⟩
  else ⟨⟨-coordinateMinimum a.1,rudvalisLattice.neg_mem (coordinateMinimum_mem _)⟩,by
    simpa [rationalDot] using coordinateMinimum_norm a.1⟩

theorem coordinateShellLift_injective : Function.Injective coordinateShellLift := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  have hv := congrArg (fun v : MinimalShell => v.val.val) h
  have hij : i=j := by
    by_contra hn
    have he := congrFun hv i
    cases b <;> cases c <;> norm_num [coordinateShellLift,coordinateMinimum,hn] at he
  subst j
  have he := congrFun hv i
  cases b <;> cases c <;> try rfl
  all_goals norm_num [coordinateShellLift,coordinateMinimum] at he

def coordinateShellInteger (a : Coordinate × Bool) : IntegerCoordinates :=
  Pi.single a.1 (if a.2 then 4 else -4)

theorem coordinateShellLift_half (a : Coordinate × Bool) :
    (coordinateShellLift a).val.val=halfCoordinates (coordinateShellInteger a) := by
  rcases a with ⟨i,b⟩
  funext j
  cases b <;> by_cases hj : j=i <;>
    norm_num [coordinateShellLift,coordinateShellInteger,halfCoordinates,coordinateMinimum,hj]

theorem coordinateShellInteger_reduce (a : Coordinate × Bool) : reduceModFour (coordinateShellInteger a)=0 := by
  rcases a with ⟨i,b⟩
  funext j
  cases b <;> by_cases hj : j=i <;> norm_num [coordinateShellInteger,reduceModFour,hj] <;> decide +kernel

theorem coordinateShellLift_ne_minimumWordShellLift (a : Coordinate × Bool) (w : MinimumWords) :
    coordinateShellLift a≠minimumWordShellLift w := by
  intro h
  have hv := congrArg (fun v : MinimalShell => v.val.val) h
  rw [coordinateShellLift_half] at hv
  have he := halfCoordinates_injective hv
  have hr := congrArg reduceModFour he
  rw [coordinateShellInteger_reduce,integerLift_reduce] at hr
  have hw := w.prop
  rw [← hr] at hw
  have hz := (euclideanWeight_eq_zero (0 : QuaternaryWord)).mpr rfl
  omega

noncomputable def minimalShellEquiv : MinimalShell ≃ (Coordinate × Bool) ⊕ MinimumWords :=
  (Equiv.ofBijective (Sum.elim coordinateShellLift minimumWordShellLift) (by
    constructor
    · intro a b h
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (coordinateShellLift_injective h)
        | inr b => exact False.elim (coordinateShellLift_ne_minimumWordShellLift a b h)
      | inr a =>
        cases b with
        | inl b => exact False.elim (coordinateShellLift_ne_minimumWordShellLift b a h.symm)
        | inr b => exact congrArg Sum.inr (minimumWordShellLift_injective h)
    · intro v
      rcases rudvalisLattice_shell_cases v.val.val v.val.prop v.prop with h|⟨w,hw⟩
      · obtain ⟨i,hi|hi⟩ := h
        · refine ⟨Sum.inl (i,true),?_⟩
          exact Subtype.ext (Subtype.ext hi.symm)
        · refine ⟨Sum.inl (i,false),?_⟩
          exact Subtype.ext (Subtype.ext hi.symm)
      · refine ⟨Sum.inr w,?_⟩
        exact Subtype.ext (Subtype.ext hw.symm))).symm

theorem rudvalisLattice_minimal_shell_card : Nat.card MinimalShell=16240 := by
  rw [Nat.card_congr minimalShellEquiv,Nat.card_sum,Nat.card_prod,quaternary_minimum_words_card]
  norm_num [Nat.card_eq_fintype_card]

end Atlas.Rudvalis
