import Atlas.LinearGroups.ReeF4.SpecialLowestCharts
import Atlas.LinearGroups.ReeF4.SpecialLeadingExistence

/-! Actual projective decomposition into the eight normalized special charts.
No cardinality or orbit-size assumptions occur. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

abbrev SpecialLeadingRoot := {r : Fin 26 // allowedSpecialLeadingRoot r}
abbrev SpecialChartSum (m : ℕ) :=
  (r : SpecialLeadingRoot) × NormalizedSpecialChart (F := F) m r.val

private theorem allowedSpecialLeadingRoot_grade_injective :
    ∀ r s : Fin 26, allowedSpecialLeadingRoot r → allowedSpecialLeadingRoot s →
      specialAbsoluteGrade r = specialAbsoluteGrade s → r = s := by
  unfold allowedSpecialLeadingRoot
  decide

private theorem isotropyCoordinates_units_smul (a : Fˣ) (u : TraceZero F) (j : Fin 26) :
    isotropyCoordinates (a • u) j = (a:F) * isotropyCoordinates u j := by
  change isotropyCoordinates ((a:F) • u) j = _
  rw [_root_.map_smul]
  rfl

def specialChartToPoint (m : ℕ) (x : SpecialChartSum (F := F) m) : SpecialPoints (F := F) m :=
  specialPointMk m x.2.val x.2.property.1

theorem specialChartToPoint_injective (m : ℕ) :
    Function.Injective (specialChartToPoint (F := F) m) := by
  rintro ⟨⟨r,hr⟩,u⟩ ⟨⟨s,hs⟩,v⟩ h
  obtain ⟨a,ha⟩ := (specialPointMk_eq_iff m u.val v.val u.property.1 v.property.1).mp h
  have hc (j : Fin 26) : (a:F) * isotropyCoordinates v.val j = isotropyCoordinates u.val j := by
    have hh := congrArg (fun z : TraceZero F => isotropyCoordinates z j) ha
    simpa only [isotropyCoordinates_units_smul] using hh
  have hgrade : specialAbsoluteGrade r = specialAbsoluteGrade s := by
    rcases lt_trichotomy (specialAbsoluteGrade r) (specialAbsoluteGrade s) with hlt | heq | hlt
    · have hh := hc s
      rw [v.property.2.1, u.property.2.2 s hlt, mul_one] at hh
      exact False.elim (a.ne_zero hh)
    · exact heq
    · have hh := hc r
      rw [v.property.2.2 r hlt, u.property.2.1, mul_zero] at hh
      exact False.elim (zero_ne_one hh)
  have hrs := allowedSpecialLeadingRoot_grade_injective r s hr hs hgrade
  subst s
  have ha1 : a = 1 := by
    apply Units.ext
    have hh := hc r
    simpa only [u.property.2.1,v.property.2.1,mul_one,Units.val_one] using hh
  have huv : u = v := by
    apply Subtype.ext
    simpa only [ha1, one_smul] using ha.symm
  cases huv
  rfl

theorem specialChartToPoint_surjective {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) : Function.Surjective (specialChartToPoint (F := F) m) := by
  intro p
  obtain ⟨r,hr,hn,hz⟩ := p.property.exists_allowed_leading_root hcard
  let a : Fˣ := (Units.mk0 (isotropyCoordinates p.val.rep r) hn)⁻¹
  let u : TraceZero F := a • p.val.rep
  have hu : IsSpecialVector m u := (isSpecialVector_units_smul_iff m a p.val.rep).mpr p.property
  have hone : isotropyCoordinates u r = 1 := by
    rw [isotropyCoordinates_units_smul]
    change (isotropyCoordinates p.val.rep r)⁻¹ * isotropyCoordinates p.val.rep r = 1
    exact inv_mul_cancel₀ hn
  have habove : ∀ j, specialAbsoluteGrade r < specialAbsoluteGrade j → isotropyCoordinates u j = 0 := by
    intro j hj
    rw [isotropyCoordinates_units_smul, hz j hj, mul_zero]
  refine ⟨⟨⟨r,hr⟩,⟨u,hu,hone,habove⟩⟩,?_⟩
  change specialPointMk m (a • p.val.rep) hu = p
  rw [specialPointMk_units_smul m p.val.rep p.property a, specialPointMk_rep]

/-- A point is uniquely its leading-root chart and its normalized vector. -/
def specialPointsEquivCharts {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    SpecialPoints (F := F) m ≃ SpecialChartSum (F := F) m :=
  (Equiv.ofBijective (specialChartToPoint m)
    ⟨specialChartToPoint_injective m,specialChartToPoint_surjective hcard⟩).symm

end Atlas.ReeF4
