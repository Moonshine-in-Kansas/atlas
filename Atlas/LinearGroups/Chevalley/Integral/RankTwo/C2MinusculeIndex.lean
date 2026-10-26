import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2Index
import Atlas.LinearGroups.Chevalley.Integral.MinusculeABCRepresentations

/-! The four coordinates are the literal selected type-C
weights, not an assumed symplectic representation or a quotient argument. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo.C2Minuscule
open Classical ClassicalData Integral.Minuscule
open scoped Matrix
set_option maxRecDepth 8192

def parameters (j : Fin 4) : Fin 2 × Bool :=
  ![(0,true), (1,true), (0,false), (1,false)] j

theorem parameters_bijective : Function.Bijective parameters := by decide

/-- Ordered weights e1,e2,-e1,-e2 in the already constructed literal orbit. -/
def weightLabel (j : Fin 4) : WeightOrbit (pairingC 2) (TypeC.orbit 2) :=
  ⟨TypeC.naturalWeight (parameters j).1 (TypeC.sign (parameters j).2),
    Finset.mem_image.mpr ⟨parameters j, Finset.mem_univ _, rfl⟩⟩

theorem weightLabel_injective : Function.Injective weightLabel := by
  intro i j h
  exact parameters_bijective.1
    (TypeC.orbit_parameter_injective 2 (congrArg Subtype.val h))

theorem weightLabel_surjective : Function.Surjective weightLabel := by
  intro μ
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp μ.property
  obtain ⟨j, rfl⟩ := parameters_bijective.2 p
  exact ⟨j, Subtype.ext hp⟩

def indexEquiv : Fin 4 ≃ WeightOrbit (pairingC 2) (TypeC.orbit 2) :=
  Equiv.ofBijective weightLabel ⟨weightLabel_injective, weightLabel_surjective⟩

def grades (k : Fin 2) (j : Fin 4) : ℤ :=
  ![![1,-1,-1,1], ![0,1,0,-1]] k j

def reflected (k : Fin 2) (j : Fin 4) : Fin 4 :=
  ![![1,0,3,2], ![0,3,2,1]] k j

theorem weightLabel_grade (k : Fin 2) (j : Fin 4) :
    (weightLabel j).val (corootElement (pairingC 2) (baseCIndexEquiv 1 k).val) =
      grades k j := by
  rw [c_simple_label]
  fin_cases k <;> fin_cases j <;> rfl

theorem simple_coroot (k : Fin 2) :
    coroot (baseCIndexEquiv 1 k).val = functional (cCoordinates (simpleLabelIndex k)) := by
  rw [c_simple_label]
  exact c_root_label _

theorem weightLabel_reflection (k : Fin 2) (j : Fin 4) :
    weightReflection (pairingC 2) (baseCIndexEquiv 1 k).val (weightLabel j).val =
      (weightLabel (reflected k j)).val := by
  have hshort : (baseCIndexEquiv 1 (0 : Fin 2)).val =
      longRoot true 0 1 (by decide) 1 (-1) (Or.inl rfl) (Or.inr rfl) := by
    change simpleB 1 0 = _
    rfl
  have hlong : (baseCIndexEquiv 1 (1 : Fin 2)).val =
      shortRoot 1 1 (Or.inl rfl) := by
    change simpleB 1 1 = _
    rfl
  fin_cases k
  · change weightReflection (pairingC 2) (baseCIndexEquiv 1 (0 : Fin 2)).val
        (TypeC.naturalWeight (parameters j).1 (TypeC.sign (parameters j).2)) =
        (weightLabel (reflected 0 j)).val
    rw [hshort, TypeC.reflection_long_label]
    fin_cases j <;> rfl
  · change weightReflection (pairingC 2) (baseCIndexEquiv 1 (1 : Fin 2)).val
        (TypeC.naturalWeight (parameters j).1 (TypeC.sign (parameters j).2)) =
        (weightLabel (reflected 1 j)).val
    rw [hlong, TypeC.reflection_short_label]
    fin_cases j <;> rfl

theorem actualStrings_grade (k : Fin 2) (j : Fin 4) :
    (TypeC.actualStrings 2).pairing (baseCIndexEquiv 1 k).val (weightLabel j) =
      grades k j := weightLabel_grade k j

theorem actualStrings_reflection (k : Fin 2) (j : Fin 4) :
    (TypeC.actualStrings 2).reflection (baseCIndexEquiv 1 k).val (weightLabel j) =
      weightLabel (reflected k j) :=
  Subtype.ext (weightLabel_reflection k j)

theorem actual_step_entry (R : Type*) [CommRing R]
    (k : Fin 2) (ε : ℤ) (i j : Fin 4) :
    (TypeC.actualStrings 2).stepMatrix R (baseCIndexEquiv 1 k).val ε
      (weightLabel i) (weightLabel j) =
      if grades k j = ε ∧ reflected k j = i then 1 else 0 := by
  rw [Minuscule.Strings.stepMatrix_entry, actualStrings_grade, actualStrings_reflection]
  simp only [weightLabel_injective.eq_iff]

end Atlas.Chevalley.Integral.RankTwo.C2Minuscule
