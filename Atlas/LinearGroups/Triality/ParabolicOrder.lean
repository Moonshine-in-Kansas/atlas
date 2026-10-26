import Atlas.LinearGroups.Triality.ParabolicCellUniqueness

/-! Exact cardinalities of the actual parabolics from unique cell coordinates. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def shortParabolicCellMap :
    borel F K hdeg ⊕ (K × borel F K hdeg) → shortParabolic F K hdeg
  | .inl b => ⟨b.val,(le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg) b.property⟩
  | .inr p => ⟨shortRoot F K p.1 * shortWeyl F K * p.2.val,
      (shortParabolic_mem_iff F K hdeg _).mpr (Or.inr
        ⟨shortRoot F K p.1,shortRoot_mem_borel F K hdeg p.1,p.2.val,p.2.property,rfl⟩)⟩

theorem shortParabolicCellMap_bijective : Function.Bijective (shortParabolicCellMap F K hdeg) := by
  constructor
  · intro x y h
    have hh := congrArg Subtype.val h
    cases x with
    | inl b =>
      cases y with
      | inl c => exact congrArg Sum.inl (Subtype.ext hh)
      | inr p =>
        simp only [shortParabolicCellMap] at hh
        have hm : shortRoot F K p.1 * shortWeyl F K * p.2.val ∈ borel F K hdeg := hh ▸ b.property
        exact False.elim (shortParabolic_cells_disjoint F K hdeg
          ⟨shortRoot F K p.1,shortRoot_mem_borel F K hdeg p.1⟩ p.2 hm)
    | inr p =>
      cases y with
      | inl b =>
        simp only [shortParabolicCellMap] at hh
        have hm : shortRoot F K p.1 * shortWeyl F K * p.2.val ∈ borel F K hdeg := hh.symm ▸ b.property
        exact False.elim (shortParabolic_cells_disjoint F K hdeg
          ⟨shortRoot F K p.1,shortRoot_mem_borel F K hdeg p.1⟩ p.2 hm)
      | inr q => exact congrArg Sum.inr (shortCell_injective F K hdeg hh)
  · intro g
    rcases shortParabolic_root_cell F K hdeg g.val g.property with hb | ⟨t,b,he⟩
    · exact ⟨.inl ⟨g.val,hb⟩,rfl⟩
    · exact ⟨.inr (t,b),Subtype.ext he.symm⟩

def shortParabolicCoordinates :
    (borel F K hdeg ⊕ (K × borel F K hdeg)) ≃ shortParabolic F K hdeg :=
  Equiv.ofBijective _ (shortParabolicCellMap_bijective F K hdeg)

theorem card_shortParabolic_factored :
    Nat.card (shortParabolic F K hdeg) = Nat.card (borel F K hdeg) * (Nat.card F ^ 3 + 1) := by
  rw [← Nat.card_congr (shortParabolicCoordinates F K hdeg),Nat.card_sum,Nat.card_prod]
  rw [FiniteCubic.card_extension hdeg]
  ring

def longParabolicCellMap :
    borel F K hdeg ⊕ (F × borel F K hdeg) → longParabolic F K hdeg
  | .inl b => ⟨b.val,(le_sup_left : borel F K hdeg ≤ longParabolic F K hdeg) b.property⟩
  | .inr p => ⟨longRoot F K p.1 * longWeyl F K * p.2.val,
      (longParabolic_mem_iff F K hdeg _).mpr (Or.inr
        ⟨longRoot F K p.1,longRoot_mem_borel F K hdeg p.1,p.2.val,p.2.property,rfl⟩)⟩

theorem longParabolicCellMap_bijective : Function.Bijective (longParabolicCellMap F K hdeg) := by
  constructor
  · intro x y h
    have hh := congrArg Subtype.val h
    cases x with
    | inl b =>
      cases y with
      | inl c => exact congrArg Sum.inl (Subtype.ext hh)
      | inr p =>
        simp only [longParabolicCellMap] at hh
        have hm : longRoot F K p.1 * longWeyl F K * p.2.val ∈ borel F K hdeg := hh ▸ b.property
        exact False.elim (longParabolic_cells_disjoint F K hdeg
          ⟨longRoot F K p.1,longRoot_mem_borel F K hdeg p.1⟩ p.2 hm)
    | inr p =>
      cases y with
      | inl b =>
        simp only [longParabolicCellMap] at hh
        have hm : longRoot F K p.1 * longWeyl F K * p.2.val ∈ borel F K hdeg := hh.symm ▸ b.property
        exact False.elim (longParabolic_cells_disjoint F K hdeg
          ⟨longRoot F K p.1,longRoot_mem_borel F K hdeg p.1⟩ p.2 hm)
      | inr q => exact congrArg Sum.inr (longCell_injective F K hdeg hh)
  · intro g
    rcases longParabolic_root_cell F K hdeg g.val g.property with hb | ⟨t,b,he⟩
    · exact ⟨.inl ⟨g.val,hb⟩,rfl⟩
    · exact ⟨.inr (t,b),Subtype.ext he.symm⟩

def longParabolicCoordinates :
    (borel F K hdeg ⊕ (F × borel F K hdeg)) ≃ longParabolic F K hdeg :=
  Equiv.ofBijective _ (longParabolicCellMap_bijective F K hdeg)

theorem card_longParabolic_factored :
    Nat.card (longParabolic F K hdeg) = Nat.card (borel F K hdeg) * (Nat.card F + 1) := by
  rw [← Nat.card_congr (longParabolicCoordinates F K hdeg),Nat.card_sum,Nat.card_prod]
  ring

private theorem sub_one_mul_add_one (n : ℕ) (hn : 1 ≤ n) :
    (n-1)*(n+1) = n^2-1 := by
  have he : (n-1)*(n+1)+1=n^2 := by nlinarith [Nat.sub_add_cancel hn]
  omega

theorem card_shortParabolic :
    Nat.card (shortParabolic F K hdeg) = Nat.card F^12 * (Nat.card F^6-1) * (Nat.card F-1) := by
  rw [card_shortParabolic_factored,card_borel]
  calc
    _ = Nat.card F^12 * ((Nat.card F^3-1)*(Nat.card F^3+1)) * (Nat.card F-1) := by ring
    _ = _ := by
      rw [sub_one_mul_add_one _ (one_le_pow₀ (show 1 ≤ Nat.card F from Nat.card_pos)),← pow_mul]

theorem card_longParabolic :
    Nat.card (longParabolic F K hdeg) = Nat.card F^12 * (Nat.card F^3-1) * (Nat.card F^2-1) := by
  rw [card_longParabolic_factored,card_borel]
  calc
    _ = Nat.card F^12 * (Nat.card F^3-1) * ((Nat.card F-1)*(Nat.card F+1)) := by ring
    _ = _ := by rw [sub_one_mul_add_one _ (show 1 ≤ Nat.card F from Nat.card_pos)]

end Atlas.Triality
