import Atlas.LinearGroups.Orthogonal.BInvolutionDimension
import Atlas.LinearGroups.Orthogonal.BInvolutionRepresentatives
import Atlas.GroupTheory.InvolutionClassEnumeration

/-! # Exact involution-class count in the actual odd-characteristic B family -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.LinearInvolution
variable {F : Type*} [Field F] [Finite F]

theorem B_elementary_k2 (n : ℕ) (hn : 1 ≤ n) (h2 : (2 : F) ≠ 0) :
    Atlas.k2 (elementarySubgroup (formB n F)) = n := by
  choose r hr using fun i : Fin n => exists_B_involution_of_half_minus_dim
    (F := F) n (i.val+1) hn (by omega) (by omega) h2
  have hi : ∀ i j, IsConj (r i) (r j) → i=j := by
    intro i j hc
    have hd := B_involutions_minus_dimension_of_isConj n (r i) (r j) hc
    rw [(hr i).2,(hr j).2] at hd
    apply Fin.ext
    omega
  have hs : ∀ g : elementarySubgroup (formB n F), orderOf g=2 → ∃ i, IsConj g (r i) := by
    intro g ho
    obtain ⟨m,hm,hmn,hd⟩ := B_involution_half_minus_dimension n hn h2 g ho
    let i : Fin n := ⟨m-1,by omega⟩
    refine ⟨i,B_involutions_isConj_of_minus_dimension n hn h2 g (r i) ho (hr i).1 ?_⟩
    rw [hd,(hr i).2]
    dsimp [i]
    omega
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
    Atlas.k2_eq_card_representatives r (fun i => (hr i).1) hi hs

/-- The public projective B model has exactly n involution conjugacy classes. -/
theorem B_k2 (n : ℕ) (hn : 1 ≤ n) (h2 : (2 : F) ≠ 0) : Atlas.k2 (B n F) = n := by
  rw [Atlas.k2_mulEquiv (B_elementaryEquiv_all_rank n hn)]
  exact B_elementary_k2 n hn h2

end Atlas.Orthogonal
