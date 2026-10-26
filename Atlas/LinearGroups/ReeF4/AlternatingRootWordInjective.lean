import Atlas.LinearGroups.ReeF4.AlternatingWordPivotA0
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotB0
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotU0
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotA1
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotU1
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotA2
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotU2
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotA3
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotU3
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotB3
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotB1
import Atlas.LinearGroups.ReeF4.AlternatingWordPivotB2

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem alternatingRootWord_parameters_injective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u u' : Fin 4 → F) (v v' : Fin 4 → F × F)
    (h : alternatingRootWord hcard u v = alternatingRootWord hcard u' v') :
    u = u' ∧ v = v' := by
  have ha0 : (v 0).1 = (v' 0).1 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (0,4))).val.1 1) h
    simp only [alternatingRootWord_pivot_a0] at he
    exact he
  have hb0 : (v 0).2 = (v' 0).2 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (2,1))).val.2 1 0) h
    simp only [alternatingRootWord_pivot_b0] at he
    exact he
  have hu0 : u 0 = u' 0 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (1,5))).val.1 0) h
    simp only [alternatingRootWord_pivot_u0] at he
    exact he
  have ha1 : (v 1).1 = (v' 1).1 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (2,5))).val.1 0) h
    simp only [alternatingRootWord_pivot_a1] at he
    exact he
  have hu1 : u 1 = u' 1 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (0,5))).val.2 2 1) h
    simp only [alternatingRootWord_pivot_u1] at he
    exact he
  have ha2 : (v 2).1 = (v' 2).1 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (2,7))).val.2 1 5) h
    simp only [alternatingRootWord_pivot_a2] at he
    exact he
  have hu2 : u 2 = u' 2 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (2,7))).val.2 0 5) h
    simp only [alternatingRootWord_pivot_u2] at he
    exact he
  have ha3 : (v 3).1 = (v' 3).1 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (2,3))).val.1 0) h
    simp only [alternatingRootWord_pivot_a3] at he
    exact he
  have hu3 : u 3 = u' 3 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (1,4))).val.1 0) h
    simp only [alternatingRootWord_pivot_u3] at he
    exact he
  have hb3 : (v 3).2 = (v' 3).2 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (1,7))).val.2 0 5) h
    simp only [alternatingRootWord_pivot_b3] at he
    rw [ha3] at he
    exact add_left_cancel he
  have hb1 : (v 1).2 = (v' 1).2 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (1,5))).val.2 0 1) h
    simp only [alternatingRootWord_pivot_b1] at he
    rw [ha3, hu0] at he
    exact add_left_cancel he
  have hb2 : (v 2).2 = (v' 2).2 := by
    have he := congrArg (fun g : Model F m => (g.val (rootVector (2,7))).val.2 1 3) h
    simp only [alternatingRootWord_pivot_b2] at he
    rw [ha1, hu2] at he
    exact add_left_cancel he
  constructor
  · funext k
    fin_cases k
    · exact hu0
    · exact hu1
    · exact hu2
    · exact hu3
  · funext k
    fin_cases k
    · exact Prod.ext ha0 hb0
    · exact Prod.ext ha1 hb1
    · exact Prod.ext ha2 hb2
    · exact Prod.ext ha3 hb3

theorem alternatingRootWord_injective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Injective (fun p : (Fin 4 → F) × (Fin 4 → F × F) =>
      alternatingRootWord hcard p.1 p.2) := by
  intro p q h
  exact Prod.ext
    (alternatingRootWord_parameters_injective hcard p.1 q.1 p.2 q.2 h).1
    (alternatingRootWord_parameters_injective hcard p.1 q.1 p.2 q.2 h).2

/-- Cardinality of the ordered-product image only, not a subgroup-order assertion. -/
theorem card_alternatingRootWord_range {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (Set.range (fun p : (Fin 4 → F) × (Fin 4 → F × F) =>
      alternatingRootWord hcard p.1 p.2)) = (Nat.card F)^12 := by
  rw [← Nat.card_congr (Equiv.ofInjective _ (alternatingRootWord_injective hcard))]
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin]
  ring

end Atlas.ReeF4
