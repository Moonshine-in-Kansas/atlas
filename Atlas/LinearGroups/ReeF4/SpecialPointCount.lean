import Atlas.LinearGroups.ReeF4.SpecialPointChartDecomposition
import Atlas.LinearGroups.ReeF4.SpecialA2Chart
import Atlas.LinearGroups.ReeF4.SpecialPositiveC3Chart
import Atlas.LinearGroups.ReeF4.SpecialA4Chart

/-! Intrinsic special-point count from eight actual normalized affine charts.
Independent of group order, parabolic orders, or an E=Model theorem. -/
noncomputable section
namespace Atlas.ReeF4
open scoped BigOperators
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def specialLeadingIndex (i : Fin 8) : SpecialLeadingRoot :=
  ⟨(![2,18,19,4,7,24,25,9] : Fin 8 → Fin 26) i, by fin_cases i <;> unfold allowedSpecialLeadingRoot <;> decide⟩

private theorem specialLeadingIndex_bijective : Function.Bijective specialLeadingIndex := by
  let f : Fin 8 → Fin 26 := ![2,18,19,4,7,24,25,9]
  have hi : ∀ i j : Fin 8, f i=f j → i=j := by decide
  have hs : ∀ r : Fin 26, r ∈ ({2,4,7,9,18,19,24,25} : Finset (Fin 26)) →
      ∃ i : Fin 8, f i=r := by decide
  constructor
  · intro i j h
    exact hi i j (congrArg Subtype.val h)
  · rintro ⟨r,hr⟩
    obtain ⟨i,he⟩ := hs r hr
    exact ⟨i,Subtype.ext he⟩

private def specialLeadingEquiv : Fin 8 ≃ SpecialLeadingRoot :=
  Equiv.ofBijective specialLeadingIndex specialLeadingIndex_bijective

theorem card_normalizedChart24 {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 24)=(Nat.card F)^7 := by
  rw [card_normalizedChart24_step hcard,card_normalizedChart7 hcard]
  ring

private theorem chart25_count {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 25)=(Nat.card F)^9 := by
  rw [Nat.card_congr (normalizedChart25Equiv hcard),Nat.card_prod,Nat.card_prod,card_normalizedChart24 hcard]
  ring

theorem card_normalizedChart9 {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (NormalizedSpecialChart (F := F) m 9)=(Nat.card F)^10 := by
  rw [card_normalizedChart9_recurrence hcard,chart25_count hcard]
  ring

theorem card_specialPoints_sum {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (SpecialPoints (F := F) m)=
      1+Nat.card F+(Nat.card F)^3+(Nat.card F)^4+(Nat.card F)^6+
        (Nat.card F)^7+(Nat.card F)^9+(Nat.card F)^10 := by
  classical
  letI : Fintype SpecialLeadingRoot := Fintype.ofFinite _
  letI : ∀ r : SpecialLeadingRoot, Finite (NormalizedSpecialChart (F := F) m r.val) :=
    fun r => by unfold NormalizedSpecialChart; infer_instance
  rw [Nat.card_congr (specialPointsEquivCharts hcard)]
  change Nat.card ((r : SpecialLeadingRoot) × NormalizedSpecialChart (F := F) m r.val)=_
  rw [Nat.card_sigma,← Equiv.sum_comp specialLeadingEquiv]
  change (∑ i : Fin 8, Nat.card (NormalizedSpecialChart (F := F) m
    ((![(2 : Fin 26),18,19,4,7,24,25,9]) i)))=_
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp only [Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_succ,
    card_normalizedChart2,card_normalizedChart18 hcard,card_normalizedChart19 hcard,
    card_normalizedChart4 hcard,card_normalizedChart7 hcard,card_normalizedChart24 hcard,
    chart25_count hcard,card_normalizedChart9 hcard]
  ring

theorem card_specialPoints {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (SpecialPoints (F := F) m)=
      ((Nat.card F)^6+1)*((Nat.card F)^3+1)*(Nat.card F+1) := by
  rw [card_specialPoints_sum hcard]
  ring

/-- The actual binary special-point set, without using a group-order theorem. -/
theorem card_specialPoints_binary (hcard : Nat.card F = 2) :
    Nat.card (SpecialPoints (F := F) 0) = 1755 := by
  rw [card_specialPoints (by simpa using hcard),hcard]
  norm_num

end Atlas.ReeF4

