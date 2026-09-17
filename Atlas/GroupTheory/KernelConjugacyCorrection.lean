import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # Correcting an ambient conjugator into a kernel

The centralizer-surjectivity hypothesis is explicit. Applications must establish it
from their own geometry; normality alone does not prevent conjugacy-class splitting.
-/
namespace Atlas
variable {G H : Type*} [Group G] [Group H]

theorem kernel_conjugator_of_centralizer_image (φ : G →* H) (a b g : G)
    (hg : g * a * g⁻¹ = b)
    (hc : ∃ c : G, c * a = a * c ∧ φ c = φ g) :
    ∃ k : G, φ k = 1 ∧ k * a * k⁻¹ = b := by
  obtain ⟨c,hcomm,hmap⟩ := hc
  refine ⟨g*c⁻¹,?_,?_⟩
  · simp [hmap]
  · have hca : c⁻¹ * a * c = a := by
      have h := congrArg (fun z : G => c⁻¹*z) hcomm
      simpa only [← mul_assoc,inv_mul_cancel,one_mul] using h.symm
    calc
      (g*c⁻¹)*a*(g*c⁻¹)⁻¹ = g*(c⁻¹*a*c)*g⁻¹ := by group
      _ = b := by rw [hca,hg]

theorem isConj_in_kernel_iff (φ : G →* H) (a b : φ.ker)
    (hc : ∀ g : G, ∃ c : G, c * a.val = a.val * c ∧ φ c = φ g) :
    IsConj a b ↔ IsConj a.val b.val := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := isConj_iff.mp h
    exact isConj_iff.mpr ⟨k.val,congrArg Subtype.val hk⟩
  · intro h
    obtain ⟨g,hg⟩ := isConj_iff.mp h
    obtain ⟨k,hk,hconj⟩ := kernel_conjugator_of_centralizer_image φ a.val b.val g hg (hc g)
    exact isConj_iff.mpr ⟨⟨k,hk⟩,Subtype.ext hconj⟩
end Atlas
