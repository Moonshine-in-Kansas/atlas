import Atlas.LinearGroups.F4.RootGroups
import Atlas.LinearGroups.F4.CentralSeven
import Atlas.LinearGroups.F4.ShortRadicalWord

/-! Membership of the constructed elementary pieces in the actual 48-root subgroup.
No assertion that it equals the full Albert automorphism group is made here. -/
noncomputable section
namespace Atlas.F4

private theorem shortRootLabelIndex_surjective : Function.Surjective shortRootLabelIndex := by
  unfold Function.Surjective
  decide +kernel

variable {F : Type*} [Field F]

theorem root_longRootLabel (r : Fin 24) (t : F) : root (longRootLabel r) t=longRoot r t := by
  simp [root,longRootLabel,r.isLt]

theorem root_shortLabel (r : Fin 24) (t : F) :
    root (⟨r.val+24,by omega⟩ : RootData.Root) t=
      shortRoot (shortRootPosition (shortRootLabelIndex r)).1
        (shortRootPosition (shortRootLabelIndex r)).2 t := by
  have h : ¬r.val+24<24 := by omega
  simp [root,h]

theorem longRoot_mem_rootGenerated (r : Fin 24) (t : F) : longRoot r t∈rootGenerated := by
  rw [←root_longRootLabel]
  exact root_mem_rootGenerated _ _

theorem shortRoot_mem_rootGenerated (p : Fin 3) (i : Fin 8) (t : F) :
    shortRoot p i t∈rootGenerated := by
  let r : Fin 24 := ⟨8*p.val+i.val,by omega⟩
  have hp : shortRootPosition r=(p,i) := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [shortRootPosition,r] <;> omega
  obtain ⟨k,hk⟩ := shortRootLabelIndex_surjective r
  have h := root_mem_rootGenerated (F := F) (⟨k.val+24,by omega⟩ : RootData.Root) t
  rw [root_shortLabel,hk,hp] at h
  exact h

theorem shortRootFirstPair_mem_rootGenerated (i : Fin 8) (t : F) :
    shortRootFirstPair i t∈rootGenerated := by
  simpa only [shortRoot,Fin.val_zero,pow_zero,one_mul,inv_one,mul_one] using
    shortRoot_mem_rootGenerated (F := F) 0 i t

theorem shortWeylFirstPair_mem_rootGenerated (i : Fin 8) :
    shortWeylFirstPair (F := F) i∈rootGenerated :=
  (rootGenerated (F := F)).mul_mem
    ((rootGenerated (F := F)).mul_mem (shortRootFirstPair_mem_rootGenerated i 1)
      (shortRootFirstPair_mem_rootGenerated (7-i) 1))
    (shortRootFirstPair_mem_rootGenerated i 1)

theorem halfRoot_mem_rootGenerated (i : Fin 8) (t : F) : halfRoot i t∈rootGenerated :=
  shortRoot_mem_rootGenerated _ _ _

theorem halfWordList_mem_rootGenerated (t : Fin 8 → F) (l : List (Fin 8)) :
    halfWordList t l∈rootGenerated := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
  exact halfRoot_mem_rootGenerated i (t i)

theorem halfWord_mem_rootGenerated (t : Fin 8 → F) : halfWord t∈rootGenerated :=
  halfWordList_mem_rootGenerated t (List.finRange 8)

theorem centralSeven_mem_rootGenerated (p : Fin 7 → F) : centralSeven p∈rootGenerated := by
  apply centralSeven_mem_of_singletons
  intro k t
  unfold centralSevenSingleton
  split_ifs
  · exact longRoot_mem_rootGenerated _ _
  · exact shortRoot_mem_rootGenerated _ _ _

end Atlas.F4
