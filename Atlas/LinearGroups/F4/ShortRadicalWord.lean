import Atlas.LinearGroups.F4.ShortRadicalLayer

noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def halfWordList (t : Fin 8→F) (l : List (Fin 8)) : Model F :=
  (l.map (fun i=>halfRoot i (t i))).prod

theorem halfWordList_lower (t : Fin 8→F) (l : List (Fin 8)) (x : Carrier F) :
    ((halfWordList t l).val x).2 2 7=x.2 2 7 ∧
    oppositeLowerCoordinates ((halfWordList t l).val x)=oppositeLowerCoordinates x+
      (l.map (fun i=>Pi.single i (t i*x.2 2 7))).sum := by
  induction l generalizing x with
  | nil => simp [halfWordList]
  | cons i l ih =>
    have h := halfRoot_lower i (t i) ((halfWordList t l).val x)
    have hi := ih x
    change ((halfRoot i (t i)).val ((halfWordList t l).val x)).2 2 7=_ ∧ _
    constructor
    · exact h.1.trans hi.1
    · change oppositeLowerCoordinates ((halfRoot i (t i)).val ((halfWordList t l).val x))=_
      rw [h.2,hi.2,hi.1]
      simp only [List.map_cons,List.sum_cons]
      abel

def halfWord (t : Fin 8→F) : Model F := halfWordList t (List.finRange 8)

theorem halfWord_lower (t : Fin 8→F) (x : Carrier F) :
    ((halfWord t).val x).2 2 7=x.2 2 7 ∧
      oppositeLowerCoordinates ((halfWord t).val x)=
        oppositeLowerCoordinates x+(fun i=>t i*x.2 2 7) := by
  have h := halfWordList_lower t (List.finRange 8) x
  refine ⟨h.1,?_⟩
  rw [halfWord,h.2]
  congr 1
  ext i
  fin_cases i <;> simp [List.finRange, List.ofFn_succ,Pi.single_apply]

theorem halfWord_mem_parabolic (t : Fin 8→F) : halfWord t∈parabolicPointStabilizer := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
  exact halfRoot_parabolic i (t i)

end Atlas.F4
