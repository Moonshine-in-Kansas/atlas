import Atlas.Fischer.QuinticCocodeSupport
import Atlas.Fischer.ProductTraceOffDiagonal

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The point may occupy any of the three ordered tensor positions. -/
def IsPointRepeatedOctad (p q r : CoordinateIndex) (i : Omega) (O : Octad) : Prop :=
  (p=Sum.inl i ∧ q=Sum.inr O ∧ r=Sum.inr O) ∨
  (q=Sum.inl i ∧ p=Sum.inr O ∧ r=Sum.inr O) ∨
  (r=Sum.inl i ∧ p=Sum.inr O ∧ q=Sum.inr O)

def IsPointTriple (p q r : CoordinateIndex) : Prop :=
  ∃ i j k : Omega, p=Sum.inl i ∧ q=Sum.inl j ∧ r=Sum.inl k

/-- Seven support families, uniformly in the actual ordered coordinates. -/
def IsSevenTypeSupport (p q r : CoordinateIndex) : Prop :=
  (IsPointTriple p q r ∧ p=q ∧ q=r) ∨
  (IsPointTriple p q r ∧ (p=q ∨ q=r ∨ p=r) ∧ ¬ (p=q ∧ q=r)) ∨
  (IsPointTriple p q r ∧ p≠q ∧ q≠r ∧ p≠r) ∨
  (∃ i O, IsPointRepeatedOctad p q r i O ∧ i ∈ O.val) ∨
  (∃ i O, IsPointRepeatedOctad p q r i O ∧ i ∉ O.val) ∨
  (∃ A B C : Octad, p=Sum.inr A ∧ q=Sum.inr B ∧ r=Sum.inr C ∧
    A≠B ∧ B≠C ∧ A≠C ∧ octadWord A+octadWord B+octadWord C=0) ∨
  (∃ A B C : Octad, p=Sum.inr A ∧ q=Sum.inr B ∧ r=Sum.inr C ∧
    A≠B ∧ B≠C ∧ A≠C ∧ octadWord A+octadWord B+octadWord C=golayOne)

private theorem pointTriple_seven {p q r : CoordinateIndex} (h : IsPointTriple p q r) :
    IsSevenTypeSupport p q r := by
  by_cases hpq : p=q <;> by_cases hqr : q=r <;> by_cases hpr : p=r <;>
    simp_all [IsSevenTypeSupport]

private theorem pointRepeated_seven {p q r : CoordinateIndex} {i : Omega} {O : Octad}
    (h : IsPointRepeatedOctad p q r i O) : IsSevenTypeSupport p q r := by
  by_cases hi : i ∈ O.val
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,O,h,hi⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,O,h,hi⟩))))

private theorem octadWord_not_line (O : Octad) : octadWord O ∉ allOneCodeLine := by
  intro h
  rcases (mem_allOneCodeLine _).mp h with hz | ho
  · have hw := congrArg (fun c : golay => hammingNorm c.val) hz
    rw [octadWord_weight] at hw
    change 8=hammingNorm (0 : BinaryWord) at hw
    rw [hammingNorm_zero] at hw
    omega
  · have hw := congrArg (fun c : golay => hammingNorm c.val) ho
    rw [octadWord_weight] at hw
    have hone : hammingNorm golayOne.val=24 := (weight_twentyfour_iff _).mpr rfl
    rw [hone] at hw
    omega

private theorem twoOctads_line_eq (A B : Octad)
    (h : octadWord A+octadWord B ∈ allOneCodeLine) : A=B := by
  rcases (mem_allOneCodeLine _).mp h with hz | ho
  · apply octadWord_injective
    have he := congrArg (fun c : golay => c+octadWord B) hz
    simpa only [add_assoc,parkerGolay_add_self,add_zero,zero_add] using he
  · exact (productTraceCoordinateWord_sum_ne_one (Sum.inr A) (Sum.inr B) ho).elim

/-- Cocode support gives the seven source families without choosing representatives
or assuming transitivity on any tensor index type. -/
theorem coordinateTripleWord_seven_types (p q r : CoordinateIndex)
    (h : coordinateTripleWord p q r ∈ allOneCodeLine) : IsSevenTypeSupport p q r := by
  cases p with
  | inl i =>
    cases q with
    | inl j =>
      cases r with
      | inl k => exact pointTriple_seven ⟨i,j,k,rfl,rfl,rfl⟩
      | inr C => exact (octadWord_not_line C (by simpa [coordinateTripleWord,productTraceCoordinateWord] using h)).elim
    | inr B =>
      cases r with
      | inl k => exact (octadWord_not_line B (by simpa [coordinateTripleWord,productTraceCoordinateWord] using h)).elim
      | inr C =>
        have he := twoOctads_line_eq B C (by simpa [coordinateTripleWord,productTraceCoordinateWord] using h)
        subst C
        exact pointRepeated_seven (Or.inl ⟨rfl,rfl,rfl⟩)
  | inr A =>
    cases q with
    | inl j =>
      cases r with
      | inl k => exact (octadWord_not_line A (by simpa [coordinateTripleWord,productTraceCoordinateWord] using h)).elim
      | inr C =>
        have he := twoOctads_line_eq A C (by simpa [coordinateTripleWord,productTraceCoordinateWord] using h)
        subst C
        exact pointRepeated_seven (Or.inr (Or.inl ⟨rfl,rfl,rfl⟩))
    | inr B =>
      cases r with
      | inl k =>
        have he := twoOctads_line_eq A B (by simpa [coordinateTripleWord,productTraceCoordinateWord] using h)
        subst B
        exact pointRepeated_seven (Or.inr (Or.inr ⟨rfl,rfl,rfl⟩))
      | inr C =>
        change octadWord A+octadWord B+octadWord C ∈ allOneCodeLine at h
        have hAB : A≠B := by intro he; subst B; exact octadWord_not_line C (by simpa only [parkerGolay_add_self,zero_add] using h)
        have hBC : B≠C := by intro he; subst C; exact octadWord_not_line A (by simpa only [add_assoc,parkerGolay_add_self,add_zero] using h)
        have hAC : A≠C := by
          intro he
          subst C
          have hh : octadWord A+octadWord B+octadWord A=octadWord B := by
            rw [add_comm (octadWord A) (octadWord B),add_assoc,parkerGolay_add_self,add_zero]
          exact octadWord_not_line B (hh ▸ h)
        rcases (mem_allOneCodeLine _).mp h with hz | ho
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨A,B,C,rfl,rfl,rfl,hAB,hBC,hAC,hz⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨A,B,C,rfl,rfl,rfl,hAB,hBC,hAC,ho⟩)))))

theorem coordinateCubic_nonzero_seven_types (p q r : CoordinateIndex)
    (h : coordinateCubic p q r ≠ 0) : IsSevenTypeSupport p q r :=
  coordinateTripleWord_seven_types p q r (coordinateCubic_nonzero_support p q r h)

theorem coordinateQuintic_nonzero_seven_types (p q r : CoordinateIndex)
    (h : coordinateQuintic p q r ≠ 0) : IsSevenTypeSupport p q r :=
  coordinateTripleWord_seven_types p q r (coordinateQuintic_nonzero_support p q r h)

end Atlas.Fischer
