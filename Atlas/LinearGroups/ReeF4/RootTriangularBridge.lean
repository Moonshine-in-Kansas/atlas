import Atlas.LinearGroups.ReeF4.AlternatingRootFactors
import Atlas.LinearGroups.ReeF4.RootTriangularClosure
import Atlas.LinearGroups.ReeF4.RootTriangularShortParameter0
import Atlas.LinearGroups.ReeF4.RootTriangularShortParameter1
import Atlas.LinearGroups.ReeF4.RootTriangularShortParameter2
import Atlas.LinearGroups.ReeF4.RootTriangularShortParameter3
import Atlas.LinearGroups.ReeF4.RootTriangularShortCenter0
import Atlas.LinearGroups.ReeF4.RootTriangularShortCenter1
import Atlas.LinearGroups.ReeF4.RootTriangularShortCenter2
import Atlas.LinearGroups.ReeF4.RootTriangularShortCenter3
import Atlas.LinearGroups.ReeF4.RootTriangularLong0
import Atlas.LinearGroups.ReeF4.RootTriangularLong1
import Atlas.LinearGroups.ReeF4.RootTriangularLong2
import Atlas.LinearGroups.ReeF4.RootTriangularLong3

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem alternating_short_parameter_strictlyLowering (k : Fin 4) (τ : F →+* F) (a : F) :
    StrictlyLoweringFormula (alternatingShortPermutation k) (shortRootParameterFormula τ a) := by
  fin_cases k
  · exact alternating_short_parameter_strictlyLowering_0 τ a
  · exact alternating_short_parameter_strictlyLowering_1 τ a
  · exact alternating_short_parameter_strictlyLowering_2 τ a
  · exact alternating_short_parameter_strictlyLowering_3 τ a
theorem alternating_short_center_strictlyLowering (k : Fin 4) (τ : F →+* F) (a : F) :
    StrictlyLoweringFormula (alternatingShortPermutation k) (shortRootCenterFormula τ a) := by
  fin_cases k
  · exact alternating_short_center_strictlyLowering_0 τ a
  · exact alternating_short_center_strictlyLowering_1 τ a
  · exact alternating_short_center_strictlyLowering_2 τ a
  · exact alternating_short_center_strictlyLowering_3 τ a
theorem alternating_long_strictlyLowering (k : Fin 4) (u z : F) :
    StrictlyLoweringFormula (alternatingLongPermutation k) (longSL2Formula u z) := by
  fin_cases k
  · exact alternating_long_strictlyLowering_0 u z
  · exact alternating_long_strictlyLowering_1 u z
  · exact alternating_long_strictlyLowering_2 u z
  · exact alternating_long_strictlyLowering_3 u z

 theorem strictlyLoweringFormula_comp {p : Equiv.Perm WeylCoordinate}
    {f g : Carrier F → Carrier F} (hf : StrictlyLoweringFormula p f)
    (hg : StrictlyLoweringFormula p g) : StrictlyLoweringFormula p (f ∘ g) := by
  intro w c hzero
  have hz : ∀ d, absoluteCoordinateGrade (p c) < absoluteCoordinateGrade (p d) →
      wilsonCoordinatesEquiv (g w) d.1 d.2 = 0 := by
    intro d hd
    rw [hg w d (by intro t ht; exact hzero t (lt_trans hd ht))]
    exact hzero d hd
  exact (hf (g w) c hz).trans (hg w c hzero)

theorem alternatingShortPrefix_compatible (m : ℕ) (k : Fin 4) :
    WeylCoordinateCompatible (alternatingShortPrefix (F := F) m k).val
      (alternatingShortPermutation k) := by
  fin_cases k
  · exact weylCoordinateCompatible_pow
      (weylCoordinateCompatible_mul weylRho_coordinateCompatible weylSigma_coordinateCompatible) 0
  · exact weylCoordinateCompatible_pow
      (weylCoordinateCompatible_mul weylRho_coordinateCompatible weylSigma_coordinateCompatible) 1
  · exact weylCoordinateCompatible_pow
      (weylCoordinateCompatible_mul weylRho_coordinateCompatible weylSigma_coordinateCompatible) 2
  · exact weylCoordinateCompatible_pow
      (weylCoordinateCompatible_mul weylRho_coordinateCompatible weylSigma_coordinateCompatible) 3

theorem alternatingLongPrefix_compatible (m : ℕ) (k : Fin 4) :
    WeylCoordinateCompatible (alternatingLongPrefix (F := F) m k).val
      (alternatingLongPermutation k) := by
  exact weylCoordinateCompatible_mul (alternatingShortPrefix_compatible m k)
    weylRho_coordinateCompatible

theorem alternatingShortRoot_unitriangular {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) (g : shortRootSubgroup m hcard) :
    AbsoluteUnitriangular (alternatingShortRootHom hcard k g).val := by
  obtain ⟨⟨a,b⟩,hab⟩ := (shortRootParameters m hcard).surjective g
  subst g
  apply absoluteUnitriangular_conj_of_formula (alternatingShortPrefix_compatible m k)
    (shortRootParameterFormula (theta F m).toRingHom a ∘
      shortRootCenterFormula (theta F m).toRingHom b)
  · intro w
    rfl
  · exact strictlyLoweringFormula_comp
      (alternating_short_parameter_strictlyLowering k _ a)
      (alternating_short_center_strictlyLowering k _ b)

theorem alternatingLongRoot_unitriangular {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (k : Fin 4) (u : Multiplicative F) :
    AbsoluteUnitriangular (alternatingLongRootHom hcard k u).val := by
  apply absoluteUnitriangular_conj_of_formula (alternatingLongPrefix_compatible m k)
    (longSL2Formula u.toAdd (theta F m u.toAdd))
  · intro w
    rfl
  · exact alternating_long_strictlyLowering k _ _

theorem absoluteUnitriangular_model_list_prod {m : ℕ} (l : List (Model F m))
    (h : ∀ g ∈ l, AbsoluteUnitriangular g.val) : AbsoluteUnitriangular l.prod.val := by
  induction l with
  | nil => exact absoluteUnitriangular_one
  | cons a l ih =>
    exact absoluteUnitriangular_mul (h a (by simp)) (ih (by
      intro g hg
      exact h g (by simp [hg])))

theorem alternatingRootWord_unitriangular {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (u : Fin 4 → F) (v : Fin 4 → F × F) :
    AbsoluteUnitriangular (alternatingRootWord hcard u v).val := by
  apply absoluteUnitriangular_model_list_prod
  intro g hg
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hg
  exact absoluteUnitriangular_mul
    (alternatingShortRoot_unitriangular hcard k _)
    (alternatingLongRoot_unitriangular hcard k _)

end Atlas.ReeF4
