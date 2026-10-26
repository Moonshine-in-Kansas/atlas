import Atlas.LinearGroups.Triality.SignedRoots
import Atlas.LinearGroups.Triality.BorelStructure

/-! Root sign alternatives for each actual Weyl word, used in global cell closure. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem shortSignedReflection_involutive : ∀ s : Bool, ∀ i : Fin 6,
    shortSignedReflection s (shortSignedReflection s i) = i := by decide

def shortSignedWord (l : List Bool) (i : Fin 6) : Fin 6 :=
  l.foldl (fun j s => shortSignedReflection s j) i

theorem shortSignedRoot_inv_conjugate (s : Bool) (i : Fin 6) (t : K) :
    (if s then shortWeyl F K else longWeyl F K)⁻¹ * shortSignedRoot F K i t *
      (if s then shortWeyl F K else longWeyl F K) =
        shortSignedRoot F K (shortSignedReflection s i)
          (if shortSignedNegate s (shortSignedReflection s i) then -t else t) := by
  have hh := shortSignedRoot_intertwine F K s (shortSignedReflection s i)
    (if shortSignedNegate s (shortSignedReflection s i) then -t else t)
  rw [shortSignedReflection_involutive] at hh
  have ht : (if shortSignedNegate s (shortSignedReflection s i) then
      -(if shortSignedNegate s (shortSignedReflection s i) then -t else t)
    else (if shortSignedNegate s (shortSignedReflection s i) then -t else t)) = t := by
    split_ifs <;> simp
  rw [ht] at hh
  calc
    _ = (if s then shortWeyl F K else longWeyl F K)⁻¹ *
      (shortSignedRoot F K i t * (if s then shortWeyl F K else longWeyl F K)) := by group
    _ = _ := by rw [← hh]; group

theorem shortSignedWord_conjugate (l : List Bool) (i : Fin 6) (t : K) :
    ∃ u : K,
      ((l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod)⁻¹ *
        shortSignedRoot F K i t *
        (l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod =
          shortSignedRoot F K (shortSignedWord l i) u := by
  induction l generalizing i t with
  | nil => exact ⟨t,by simp [shortSignedWord]⟩
  | cons s l ih =>
    obtain ⟨u,hu⟩ := ih (shortSignedReflection s i)
      (if shortSignedNegate s (shortSignedReflection s i) then -t else t)
    refine ⟨u,?_⟩
    simp only [List.map_cons,List.prod_cons,mul_inv_rev]
    calc
      _ = ((l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod)⁻¹ *
        ((if s then shortWeyl F K else longWeyl F K)⁻¹ * shortSignedRoot F K i t *
          (if s then shortWeyl F K else longWeyl F K)) *
        (l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod := by group
      _ = _ := by rw [shortSignedRoot_inv_conjugate]; exact hu

theorem shortSignedWord_sign : ∀ w : Fin 12,
    (shortSignedWord (weylWord w) 0).val < 3 ∨ (shortSignedWord (weylWord w) 3).val < 3 := by
  decide

theorem shortSignedRoot_positive (hdeg : Module.finrank F K = 3)
    (i : Fin 6) (hi : i.val < 3) (t : K) : shortSignedRoot F K i t ∈ unipotent F K hdeg := by
  fin_cases i <;> try { norm_num at hi }
  · exact ⟨⟨t,0,0,0,0,0⟩,by simpa [shortSignedRoot] using positiveMatrix_short F K t⟩
  · exact ⟨⟨0,0,t,0,0,0⟩,by simpa [shortSignedRoot] using positiveMatrix_next F K t⟩
  · exact ⟨⟨0,0,0,t,0,0⟩,by simpa [shortSignedRoot] using positiveMatrix_middle F K t⟩

theorem shortWeyl_root_sign (hdeg : Module.finrank F K = 3) (w : Fin 12) :
    (∀ t : K, (weylLift F K w)⁻¹ * shortRoot F K t * weylLift F K w ∈ borel F K hdeg) ∨
    (∀ t : K, (weylLift F K w)⁻¹ * shortNegativeRoot F K t * weylLift F K w ∈ borel F K hdeg) := by
  rcases shortSignedWord_sign w with hp | hn
  · left
    intro t
    obtain ⟨u,hu⟩ := shortSignedWord_conjugate F K (weylWord w) 0 t
    apply unipotent_le_borel F K hdeg
    change (weylLift F K w)⁻¹ * shortRoot F K t * weylLift F K w = _ at hu
    rw [hu]
    exact shortSignedRoot_positive F K hdeg _ hp u
  · right
    intro t
    obtain ⟨u,hu⟩ := shortSignedWord_conjugate F K (weylWord w) 3 t
    apply unipotent_le_borel F K hdeg
    change (weylLift F K w)⁻¹ * shortNegativeRoot F K t * weylLift F K w = _ at hu
    rw [hu]
    exact shortSignedRoot_positive F K hdeg _ hn u

theorem longSignedReflection_involutive : ∀ s : Bool, ∀ i : Fin 6,
    longSignedReflection s (longSignedReflection s i) = i := by decide

def longSignedWord (l : List Bool) (i : Fin 6) : Fin 6 :=
  l.foldl (fun j s => longSignedReflection s j) i

theorem longSignedRoot_inv_conjugate (s : Bool) (i : Fin 6) (t : F) :
    (if s then shortWeyl F K else longWeyl F K)⁻¹ * longSignedRoot F K i t *
      (if s then shortWeyl F K else longWeyl F K) =
        longSignedRoot F K (longSignedReflection s i)
          (if longSignedNegate s (longSignedReflection s i) then -t else t) := by
  have hh := longSignedRoot_intertwine F K s (longSignedReflection s i)
    (if longSignedNegate s (longSignedReflection s i) then -t else t)
  rw [longSignedReflection_involutive] at hh
  have ht : (if longSignedNegate s (longSignedReflection s i) then
      -(if longSignedNegate s (longSignedReflection s i) then -t else t)
    else (if longSignedNegate s (longSignedReflection s i) then -t else t)) = t := by
    split_ifs <;> simp
  rw [ht] at hh
  calc
    _ = (if s then shortWeyl F K else longWeyl F K)⁻¹ *
      (longSignedRoot F K i t * (if s then shortWeyl F K else longWeyl F K)) := by group
    _ = _ := by rw [← hh]; group

theorem longSignedWord_conjugate (l : List Bool) (i : Fin 6) (t : F) :
    ∃ u : F,
      ((l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod)⁻¹ *
        longSignedRoot F K i t *
        (l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod =
          longSignedRoot F K (longSignedWord l i) u := by
  induction l generalizing i t with
  | nil => exact ⟨t,by simp [longSignedWord]⟩
  | cons s l ih =>
    obtain ⟨u,hu⟩ := ih (longSignedReflection s i)
      (if longSignedNegate s (longSignedReflection s i) then -t else t)
    refine ⟨u,?_⟩
    simp only [List.map_cons,List.prod_cons,mul_inv_rev]
    calc
      _ = ((l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod)⁻¹ *
        ((if s then shortWeyl F K else longWeyl F K)⁻¹ * longSignedRoot F K i t *
          (if s then shortWeyl F K else longWeyl F K)) *
        (l.map fun (s : Bool) => if s then shortWeyl F K else longWeyl F K).prod := by group
      _ = _ := by rw [longSignedRoot_inv_conjugate]; exact hu

theorem longSignedWord_sign : ∀ w : Fin 12,
    (longSignedWord (weylWord w) 0).val < 3 ∨ (longSignedWord (weylWord w) 3).val < 3 := by
  decide

theorem longSignedRoot_positive (hdeg : Module.finrank F K = 3)
    (i : Fin 6) (hi : i.val < 3) (t : F) : longSignedRoot F K i t ∈ unipotent F K hdeg := by
  fin_cases i <;> try { norm_num at hi }
  · exact ⟨⟨0,t,0,0,0,0⟩,by simpa [longSignedRoot] using positiveMatrix_long F K t⟩
  · exact ⟨⟨0,0,0,0,t,0⟩,by simpa [longSignedRoot] using positiveMatrix_high F K t⟩
  · exact ⟨⟨0,0,0,0,0,t⟩,by simpa [longSignedRoot] using positiveMatrix_highest F K t⟩

theorem longWeyl_root_sign (hdeg : Module.finrank F K = 3) (w : Fin 12) :
    (∀ t : F, (weylLift F K w)⁻¹ * longRoot F K t * weylLift F K w ∈ borel F K hdeg) ∨
    (∀ t : F, (weylLift F K w)⁻¹ * longNegativeRoot F K t * weylLift F K w ∈ borel F K hdeg) := by
  rcases longSignedWord_sign w with hp | hn
  · left
    intro t
    obtain ⟨u,hu⟩ := longSignedWord_conjugate F K (weylWord w) 0 t
    apply unipotent_le_borel F K hdeg
    change (weylLift F K w)⁻¹ * longRoot F K t * weylLift F K w = _ at hu
    rw [hu]
    exact longSignedRoot_positive F K hdeg _ hp u
  · right
    intro t
    obtain ⟨u,hu⟩ := longSignedWord_conjugate F K (weylWord w) 3 t
    apply unipotent_le_borel F K hdeg
    change (weylLift F K w)⁻¹ * longNegativeRoot F K t * weylLift F K w = _ at hu
    rw [hu]
    exact longSignedRoot_positive F K hdeg _ hn u

end Atlas.Triality
