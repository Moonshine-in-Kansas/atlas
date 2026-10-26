import Atlas.LinearGroups.Triality.SignedConjugation

/-! Surjectivity of the signed-root parameter maps under Weyl conjugation. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem shortSignedWord_conjugate_onto (l : List Bool) (i : Fin 6) (u : K) :
    ∃ t : K,
      ((l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod)⁻¹ *
        shortSignedRoot F K i t *
        (l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod =
          shortSignedRoot F K (shortSignedWord l i) u := by
  induction l generalizing i u with
  | nil => exact ⟨u,by simp [shortSignedWord]⟩
  | cons s l ih =>
    obtain ⟨v,hv⟩ := ih (shortSignedReflection s i) u
    let t := if shortSignedNegate s (shortSignedReflection s i) then -v else v
    have ht : (if shortSignedNegate s (shortSignedReflection s i) then -t else t)=v := by
      dsimp [t]
      split_ifs <;> simp
    refine ⟨t,?_⟩
    simp only [List.map_cons,List.prod_cons,mul_inv_rev]
    calc
      _ = ((l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod)⁻¹ *
        ((if s then shortWeyl F K else longWeyl F K)⁻¹ * shortSignedRoot F K i t *
          (if s then shortWeyl F K else longWeyl F K)) *
        (l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod := by group
      _ = _ := by rw [shortSignedRoot_inv_conjugate,ht]; exact hv

theorem shortSignedRoot_mem_of_weyl (hdeg : Module.finrank F K = 3)
    (H : Subgroup (O_DPlus 4 K)) (hB : borel F K hdeg ≤ H)
    (w : Fin 12) (hw : weylLift F K w ∈ H) (i : Fin 6) (hi : i.val<3) (u : K) :
    shortSignedRoot F K (shortSignedWord (weylWord w) i) u ∈ H := by
  obtain ⟨t,ht⟩ := shortSignedWord_conjugate_onto F K (weylWord w) i u
  change (weylLift F K w)⁻¹ * shortSignedRoot F K i t * weylLift F K w = _ at ht
  rw [← ht]
  exact H.mul_mem (H.mul_mem (H.inv_mem hw)
    (hB (unipotent_le_borel F K hdeg (shortSignedRoot_positive F K hdeg i hi t)))) hw

theorem longSignedWord_conjugate_onto (l : List Bool) (i : Fin 6) (u : F) :
    ∃ t : F,
      ((l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod)⁻¹ *
        longSignedRoot F K i t *
        (l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod =
          longSignedRoot F K (longSignedWord l i) u := by
  induction l generalizing i u with
  | nil => exact ⟨u,by simp [longSignedWord]⟩
  | cons s l ih =>
    obtain ⟨v,hv⟩ := ih (longSignedReflection s i) u
    let t := if longSignedNegate s (longSignedReflection s i) then -v else v
    have ht : (if longSignedNegate s (longSignedReflection s i) then -t else t)=v := by
      dsimp [t]
      split_ifs <;> simp
    refine ⟨t,?_⟩
    simp only [List.map_cons,List.prod_cons,mul_inv_rev]
    calc
      _ = ((l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod)⁻¹ *
        ((if s then shortWeyl F K else longWeyl F K)⁻¹ * longSignedRoot F K i t *
          (if s then shortWeyl F K else longWeyl F K)) *
        (l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod := by group
      _ = _ := by rw [longSignedRoot_inv_conjugate,ht]; exact hv

theorem longSignedRoot_mem_of_weyl (hdeg : Module.finrank F K = 3)
    (H : Subgroup (O_DPlus 4 K)) (hB : borel F K hdeg ≤ H)
    (w : Fin 12) (hw : weylLift F K w ∈ H) (i : Fin 6) (hi : i.val<3) (u : F) :
    longSignedRoot F K (longSignedWord (weylWord w) i) u ∈ H := by
  obtain ⟨t,ht⟩ := longSignedWord_conjugate_onto F K (weylWord w) i u
  change (weylLift F K w)⁻¹ * longSignedRoot F K i t * weylLift F K w = _ at ht
  rw [← ht]
  exact H.mul_mem (H.mul_mem (H.inv_mem hw)
    (hB (unipotent_le_borel F K hdeg (longSignedRoot_positive F K hdeg i hi t)))) hw

theorem longSignedWord_outside_short : ∀ w : Fin 12, w ≠ 0 → w ≠ 1 →
    ∃ i : Fin 6, i.val<3 ∧
      (longSignedWord (weylWord w) i=3 ∨ longSignedWord (weylWord w) i=4) := by decide

theorem shortSignedWord_outside_long : ∀ w : Fin 12, w ≠ 0 → w ≠ 2 →
    ∃ i : Fin 6, i.val<3 ∧
      (shortSignedWord (weylWord w) i=3 ∨ shortSignedWord (weylWord w) i=4) := by decide

end Atlas.Triality
