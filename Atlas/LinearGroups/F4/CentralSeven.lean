import Atlas.LinearGroups.F4.CentralSevenRoots
import Atlas.LinearGroups.F4.ShortRootDerived
import Atlas.LinearGroups.F4.ParabolicMarkedPoint
import Mathlib.FieldTheory.Finite.Basic

/-! An actual abelian seven-parameter subgroup of the C₀ stabilizer.
Its order is q⁷. Full radical and full stabilizer identifications remain separate. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

theorem centralSevenEquiv_zero : centralSevenEquiv (0 : Fin 7 → F)=1 := by
  apply LinearEquiv.ext
  exact centralSevenApply_zero

theorem centralSevenEquiv_add (p q : Fin 7 → F) :
    centralSevenEquiv (p+q)=centralSevenEquiv p*centralSevenEquiv q := by
  apply LinearEquiv.ext
  intro x
  exact (centralSevenApply_add p q x).symm

def centralSevenSingleton (k : Fin 7) (t : F) : Model F :=
  if h : k.val<6 then longRoot (centralSevenLongLabel ⟨k.val,h⟩) t else shortRoot 0 0 t

theorem centralSevenSingleton_val (k : Fin 7) (t : F) :
    (centralSevenSingleton k t).val=centralSevenEquiv (Pi.single k t) := by
  fin_cases k
  · exact centralSeven_single_long 0 t
  · exact centralSeven_single_long 1 t
  · exact centralSeven_single_long 2 t
  · exact centralSeven_single_long 3 t
  · exact centralSeven_single_long 4 t
  · exact centralSeven_single_long 5 t
  · exact centralSeven_single_short t

private theorem centralSeven_parameter_sum (p : Fin 7 → F) :
    (∑ k : Fin 7,Pi.single k (p k))=p := by
  ext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem centralSevenEquiv_mem (p : Fin 7 → F) : centralSevenEquiv p ∈ Model F := by
  have hm : ∀ s : Finset (Fin 7), centralSevenEquiv (∑ k∈s,Pi.single k (p k)) ∈ Model F := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty,centralSevenEquiv_zero] using (Model F).one_mem
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk,centralSevenEquiv_add]
      exact (Model F).mul_mem (by rw [←centralSevenSingleton_val]; exact (centralSevenSingleton k (p k)).prop) ih
  simpa only [centralSeven_parameter_sum] using hm Finset.univ

def centralSeven (p : Fin 7 → F) : Model F := ⟨centralSevenEquiv p,centralSevenEquiv_mem p⟩

theorem centralSeven_apply (p : Fin 7 → F) (x : Atlas.Albert.Carrier F) :
    (centralSeven p).val x=centralSevenApply p x := rfl

theorem centralSeven_zero : centralSeven (0 : Fin 7 → F)=1 :=
  Subtype.ext centralSevenEquiv_zero

theorem centralSeven_add (p q : Fin 7 → F) :
    centralSeven p*centralSeven q=centralSeven (p+q) :=
  Subtype.ext (centralSevenEquiv_add p q).symm

theorem centralSeven_commute (p q : Fin 7 → F) : Commute (centralSeven p) (centralSeven q) := by
  change centralSeven p*centralSeven q=centralSeven q*centralSeven p
  rw [centralSeven_add,centralSeven_add,add_comm]

theorem centralSeven_injective : Function.Injective (centralSeven (F := F)) := by
  intro p q h
  exact centralSevenEquiv_injective (congrArg Subtype.val h)

def centralSevenHom : Multiplicative (Fin 7 → F) →* Model F where
  toFun p := centralSeven p.toAdd
  map_one' := centralSeven_zero
  map_mul' p q := (centralSeven_add p.toAdd q.toAdd).symm

def centralSevenSubgroup : Subgroup (Model F) := (centralSevenHom (F := F)).range

theorem card_centralSevenSubgroup [Finite F] :
    Nat.card (centralSevenSubgroup (F := F))=(Nat.card F)^7 := by
  change Nat.card (Set.range (centralSeven (F := F)))=_
  rw [Nat.card_range_of_injective centralSeven_injective]
  simp [Nat.card_fun]

theorem centralSeven_singleton (k : Fin 7) (t : F) :
    centralSeven (Pi.single k t)=centralSevenSingleton k t :=
  Subtype.ext (centralSevenSingleton_val k t).symm

theorem centralSeven_mem_of_singletons (H : Subgroup (Model F))
    (h : ∀ (k : Fin 7) (t : F),centralSevenSingleton k t∈H) (p : Fin 7 → F) :
    centralSeven p∈H := by
  have hm : ∀ s : Finset (Fin 7),centralSeven (∑ k∈s,Pi.single k (p k))∈H := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty,centralSeven_zero] using H.one_mem
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk,←centralSeven_add,centralSeven_singleton]
      exact H.mul_mem (h k (p k)) ih
  simpa only [centralSeven_parameter_sum] using hm Finset.univ

theorem centralSeven_mem_commutator (p : Fin 7 → F) : centralSeven p∈commutator (Model F) := by
  apply centralSeven_mem_of_singletons
  intro k t
  unfold centralSevenSingleton
  split_ifs
  · exact longRoot_mem_commutator _ _
  · exact shortRoot_mem_commutator _ _ _

theorem centralSeven_parabolicVector (p : Fin 7 → F) :
    (centralSeven p).val parabolicVector=parabolicVector := by
  rw [centralSeven_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [centralSevenApply,parabolicVector,Atlas.SplitOctonion.basisVector]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [centralSevenApply,parabolicVector,Atlas.SplitOctonion.basisVector]

theorem centralSeven_mem_parabolicPointStabilizer (p : Fin 7 → F) :
    centralSeven p∈parabolicPointStabilizer := by
  apply (mem_parabolicPointStabilizer_iff _).mpr
  exact ⟨1,by simpa using centralSeven_parabolicVector p⟩

end Atlas.F4
