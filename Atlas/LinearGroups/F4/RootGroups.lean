import Atlas.LinearGroups.F4.LongRoots
import Atlas.LinearGroups.F4.ShortRootDerived
import Atlas.LinearGroups.F4.ParameterSubgroups

/-! Uniform 48-root interface inside the full Albert group. The generated
subgroup is retained separately; equality with the full group is not assumed. -/
noncomputable section
namespace Atlas.F4

def shortRootLabelIndex : Fin 24 → Fin 24 :=
  ![0,7,1,6,2,5,3,4,8,16,17,9,18,10,12,19,20,11,13,21,14,22,23,15]

theorem shortRootLabelIndex_correct : ∀ r : Fin 24,
    Weights.slotRoot (2-(shortRootPosition (shortRootLabelIndex r)).1,
      (shortRootPosition (shortRootLabelIndex r)).2) =
      (⟨r.val+24,by omega⟩ : RootData.Root) := by
  decide +kernel

variable {F : Type*} [Field F]

def root (r : RootData.Root) (t : F) : Model F :=
  if h : r.val<24 then longRoot ⟨r.val,h⟩ t
  else
    let k := shortRootPosition (shortRootLabelIndex ⟨r.val-24,by omega⟩)
    shortRoot k.1 k.2 t

theorem root_add (r : RootData.Root) (s t : F) :
    root r (s+t)=root r s*root r t := by
  unfold root
  split_ifs
  · exact (longRoot_add _ s t).symm
  · exact shortRoot_add _ _ s t

theorem root_zero (r : RootData.Root) : root (F:=F) r 0=1 := by
  have h := root_add (F:=F) r 0 0
  have hh : root (F:=F) r 0*root r 0=root r 0*1 := by simpa using h.symm
  exact mul_left_cancel hh

theorem root_injective (r : RootData.Root) : Function.Injective (root (F:=F) r) := by
  unfold root
  split_ifs
  · exact longRoot_injective _
  · exact shortRoot_injective _ _

def rootHom (r : RootData.Root) : Multiplicative F →* Model F where
  toFun t := root r t.toAdd
  map_one' := root_zero r
  map_mul' s t := root_add r s.toAdd t.toAdd

def rootSubgroup (r : RootData.Root) : Subgroup (Model F) := (rootHom r).range

theorem card_rootSubgroup (r : RootData.Root) : Nat.card (rootSubgroup (F:=F) r)=Nat.card F := by
  change Nat.card (Set.range (root (F:=F) r))=Nat.card F
  exact Nat.card_range_of_injective (root_injective r)

theorem root_mem_commutator (r : RootData.Root) (t : F) :
    root r t∈commutator (Model F) := by
  unfold root
  split_ifs
  · exact longRoot_mem_commutator _ t
  · exact shortRoot_mem_commutator _ _ t

def rootGenerated : Subgroup (Model F) :=
  Subgroup.closure {g | ∃ r t, g=root r t}

theorem root_mem_rootGenerated (r : RootData.Root) (t : F) :
    root r t∈rootGenerated := Subgroup.subset_closure ⟨r,t,rfl⟩

theorem rootGenerated_le_commutator : rootGenerated (F:=F) ≤ commutator (Model F) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨r,t,rfl⟩
  exact root_mem_commutator r t

end Atlas.F4
