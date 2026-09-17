import Atlas.LinearGroups.Orthogonal.CoordinateRootSubgroups
import Atlas.LinearGroups.Orthogonal.RootLineElimination
import Atlas.LinearGroups.Orthogonal.RootGenerationFromLineTransport

noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F : Type*} [Field F]

private theorem fin_nontrivial (n : ℕ) (hn : 2≤n) : Nontrivial (Fin n) := by
  refine ⟨⟨⟨0,by omega⟩,⟨1,by omega⟩,?_⟩⟩
  intro he
  have hh := congrArg Fin.val he
  simp at hh

theorem coordinateD_line_transport (n : ℕ) (hn : 2≤n) (x : VectorD n F)
    (hx : formD n F x=0) (hxn : x≠0) :
    ∃g : O_DPlus n F, g ∈ coordinateRootSubgroupD n ∧ ∃c : F, c≠0 ∧
      g.val (e ⟨0,by omega⟩)=c • x := by
  letI := fin_nontrivial n hn
  refine coordinate_frame_line_transport (formD n F) (coordinateRootSubgroupD n)
    e f ⟨0,by omega⟩ (formD_e) (formD_f) (polarD_ef) ?_
    (rootD_e_le_coordinate n) (rootD_f_le_coordinate n) x hx ?_
  · intro i j hij
    refine ⟨?_,?_,?_⟩
    · rw [polarD_e]; simp [e]
    · rw [polarD_f]; simp [e,Pi.single_apply,hij]
    · rw [polarD_f]; simp [f]
  · by_contra hh
    push_neg at hh
    apply hxn
    funext k
    cases k with
    | inl i =>
      have he := (hh i).2
      rw [polar_swap,polarD_f] at he
      exact he
    | inr i =>
      have he := (hh i).1
      rw [polar_swap,polarD_e] at he
      exact he

theorem coordinateB_line_transport (n : ℕ) (hn : 2≤n) (x : VectorB n F)
    (hx : formB n F x=0) (hxn : x≠0) :
    ∃g : O_B n F, g ∈ coordinateRootSubgroupB n ∧ ∃c : F, c≠0 ∧
      g.val (e ⟨0,by omega⟩,0)=c • x := by
  letI := fin_nontrivial n hn
  refine coordinate_frame_line_transport (formB n F) (coordinateRootSubgroupB n)
    (fun i => (e i,0)) (fun i => (f i,0)) ⟨0,by omega⟩
    (fun i => by simp [e]) (fun i => by simp [f])
    (fun i => by rw [polarB_apply,polarD_ef]; simp) ?_
    (rootB_e_le_coordinate n) (rootB_f_le_coordinate n) x hx ?_
  · intro i j hij
    refine ⟨?_,?_,?_⟩
    · rw [polarB_apply,polarD_e]; simp [e]
    · rw [polarB_apply,polarD_f]; simp [e,Pi.single_apply,hij]
    · rw [polarB_apply,polarD_f]; simp [f]
  · by_contra hh
    push_neg at hh
    have hz : x.1=0 := by
      funext k
      cases k with
      | inl i =>
        have he := (hh i).2
        rw [polar_swap,polarB_apply,polarD_f] at he
        simpa using he
      | inr i =>
        have he := (hh i).1
        rw [polar_swap,polarB_apply,polarD_e] at he
        simpa using he
    have hz' : x.2=0 := by
      have hh : x.2^2=0 := by simpa [formB_apply,hz] using hx
      exact (sq_eq_zero_iff).mp hh
    exact hxn (Prod.ext hz hz')

/-- The actual coordinate long-root transformations generate the full split elementary group. -/
theorem coordinateRootSubgroupD_eq_elementary (n : ℕ) (hn : 2≤n) :
    coordinateRootSubgroupD (F := F) n = elementarySubgroup (formD n F) := by
  apply le_antisymm (coordinateRootSubgroupD_le_elementary n)
  apply elementary_le_of_root_and_line_transport (formD n F) (coordinateRootSubgroupD n)
    (e ⟨0,by omega⟩) (formD_e _) (rootD_e_le_coordinate n _)
  intro u hun hu
  exact coordinateD_line_transport n hn u hu hun

/-- The actual coordinate long and short roots generate the full odd-dimensional elementary group. -/
theorem coordinateRootSubgroupB_eq_elementary (n : ℕ) (hn : 2≤n) :
    coordinateRootSubgroupB (F := F) n = elementarySubgroup (formB n F) := by
  apply le_antisymm (coordinateRootSubgroupB_le_elementary n)
  apply elementary_le_of_root_and_line_transport (formB n F) (coordinateRootSubgroupB n)
    (e ⟨0,by omega⟩,0) (by simp [e]) (rootB_e_le_coordinate n _)
  intro u hun hu
  exact coordinateB_line_transport n hn u hu hun

end Atlas.Orthogonal
