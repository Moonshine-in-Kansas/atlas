import Atlas.Fischer.OctadHyperplanePairs

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance (O : Octad) : Fintype (OctadShortenedHyperplane O) := Fintype.ofFinite _

private theorem twice_shortened (O : Octad) (a : octadShortenedCode O) : a+a=0 := by
  rw [← two_smul Bit,show (2 : Bit)=0 from rfl,zero_smul]

abbrev OctadHyperplaneSumPair (O : Octad) :=
  {p : OctadShortenedHyperplane O × OctadShortenedHyperplane O //
    p.1.val+p.2.val ≠ 0 ∧ p.1.val+p.2.val ≠ octadShortenedOne O}

def octadHyperplaneSum (O : Octad) (p : OctadHyperplaneSumPair O) :
    OctadShortenedHyperplane O := ⟨p.val.1.val+p.val.2.val,p.prop⟩

def octadHyperplaneSumFiberEquiv (O : Octad) (d : OctadShortenedHyperplane O) :
    {p : OctadHyperplaneSumPair O // octadHyperplaneSum O p=d} ≃
      {b : OctadShortenedHyperplane O //
        b.val+d.val ≠ 0 ∧ b.val+d.val ≠ octadShortenedOne O} where
  toFun p := ⟨p.val.val.1,by
    have he : p.val.val.1.val+d.val=p.val.val.2.val := by
      have hd : p.val.val.1.val+p.val.val.2.val=d.val := congrArg Subtype.val p.prop
      rw [←hd]
      change p.val.val.1.val+(p.val.val.1.val+p.val.val.2.val)=p.val.val.2.val
      rw [←add_assoc,twice_shortened,zero_add]
    rw [he]
    exact p.val.val.2.prop⟩
  invFun b := ⟨⟨(b.val,⟨b.val.val+d.val,b.prop⟩),by
    change b.val.val+(b.val.val+d.val) ≠ 0 ∧
      b.val.val+(b.val.val+d.val) ≠ octadShortenedOne O
    rw [←add_assoc,twice_shortened,zero_add]
    exact d.prop⟩,by
    apply Subtype.ext
    change b.val.val+(b.val.val+d.val)=d.val
    rw [←add_assoc,twice_shortened,zero_add]⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change p.val.val.1.val+d.val=p.val.val.2.val
      have hd : p.val.val.1.val+p.val.val.2.val=d.val := congrArg Subtype.val p.prop
      rw [←hd]
      change p.val.val.1.val+(p.val.val.1.val+p.val.val.2.val)=p.val.val.2.val
      rw [←add_assoc,twice_shortened,zero_add]
  right_inv b := rfl

theorem octadHyperplaneSum_fiber_card (O : Octad) (d : OctadShortenedHyperplane O) :
    Nat.card {p : OctadHyperplaneSumPair O // octadHyperplaneSum O p=d} = 28 := by
  rw [Nat.card_congr (octadHyperplaneSumFiberEquiv O d)]
  have h := octadShortenedHyperplane_sum_card O d
  rw [←Nat.card_eq_fintype_card] at h
  exact h

/-- The actual hyperplane convolution, with no scalar or sign assumption on F. -/
theorem octadHyperplane_convolution (O : Octad) {M : Type*} [AddCommMonoid M]
    (F : OctadShortenedHyperplane O → M) :
    (∑ p : OctadHyperplaneSumPair O, F (octadHyperplaneSum O p)) =
      28 • ∑ d : OctadShortenedHyperplane O, F d := by
  classical
  letI (d : OctadShortenedHyperplane O) :
      Fintype {p : OctadHyperplaneSumPair O // octadHyperplaneSum O p=d} :=
    Subtype.fintype (fun p : OctadHyperplaneSumPair O => octadHyperplaneSum O p=d)
  rw [←Fintype.sum_fiberwise' (octadHyperplaneSum O) F]
  simp only [Finset.sum_const,Finset.card_univ,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  exact (@Nat.card_eq_fintype_card _ _).symm.trans (octadHyperplaneSum_fiber_card O d)

end Atlas.Fischer
