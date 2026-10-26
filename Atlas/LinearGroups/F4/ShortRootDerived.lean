import Atlas.LinearGroups.F4.ShortWeylRootConjugation
import Atlas.LinearGroups.F4.ShortRootA2Commutator
import Mathlib.GroupTheory.Commutator.Basic

/-! Every constructed short root lies in the derived subgroup of the actual
Albert group. This is independent of, and does not assert, full generation. -/
noncomputable section
namespace Atlas.F4
open scoped commutatorElement

/-- Rotation to the next one of the three diagonal pairs. -/
def shortRootNextPair (p : Fin 3) : Fin 3 := ⟨(p.val+1)%3,by omega⟩

def shortRootCycleLabel (r : Fin 24) : Fin 24 :=
  ⟨((r.val/8+1)%3)*8+r.val%8,by omega⟩

theorem shortRootCycleLabel_position : ∀ r : Fin 24,
    shortRootPosition (shortRootCycleLabel r) =
      (shortRootNextPair (shortRootPosition r).1,(shortRootPosition r).2) := by
  decide +kernel

variable {F : Type*} [Field F]

theorem coordinateCycle_shortRoot_conjugate (p : Fin 3) (i : Fin 8) (t : F) :
    coordinateCycle * shortRoot p i t * (coordinateCycle (F := F))⁻¹ =
      shortRoot (shortRootNextPair p) i t := by
  have hc : (coordinateCycle (F := F)) * coordinateCycle ^ p.val =
      coordinateCycle ^ (shortRootNextPair p).val := by
    fin_cases p
    · simp [shortRootNextPair]
    · simp [shortRootNextPair,pow_two]
    · norm_num [shortRootNextPair]
      rw [←pow_succ',coordinateCycle_cube]
  unfold shortRoot
  calc
    _ = (coordinateCycle * coordinateCycle ^ p.val) * shortRootFirstPair i t *
        (coordinateCycle * coordinateCycle ^ p.val)⁻¹ := by group
    _ = _ := by rw [hc]

private def ShortRootDerivedAt (F : Type*) [Field F] (r : Fin 24) : Prop :=
  ∀ t : F, shortRoot (shortRootPosition r).1 (shortRootPosition r).2 t ∈
    commutator (Model F)

private theorem shortRootDerivedAt_seed : ShortRootDerivedAt F 3 := by
  intro t
  change shortRoot 0 3 t ∈ commutator (Model F)
  have hc : ⁅shortRoot 1 0 t,shortRoot 2 7 (1 : F)⁆ = shortRoot 0 3 t := by
    simpa only [commutatorElement_def,mul_one] using shortRoot_A2_commutator t (1 : F)
  rw [←hc]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem shortRootDerivedAt_weyl (i : Fin 8) (r : Fin 24)
    (hr : ShortRootDerivedAt F r) : ShortRootDerivedAt F (shortWeylRootDestination i r) := by
  intro t
  have hs : (shortWeylRootSign i r : F)^2 = 1 := by
    have h := congrArg (fun n : ℤ => (n : F)) (shortWeylRootSign_sq i r)
    simpa only [Int.cast_pow,Int.cast_one] using h
  have hc := (inferInstance : (commutator (Model F)).Normal).conj_mem _
    (hr ((shortWeylRootSign i r : F)*t)) (shortWeylFirstPair i)
  rw [shortWeyl_shortRoot_conjugate] at hc
  simpa only [←mul_assoc,←pow_two,hs,one_mul] using hc

private theorem shortRootDerivedAt_cycle (r : Fin 24)
    (hr : ShortRootDerivedAt F r) : ShortRootDerivedAt F (shortRootCycleLabel r) := by
  intro t
  have hc := (inferInstance : (commutator (Model F)).Normal).conj_mem _ (hr t) coordinateCycle
  rw [coordinateCycle_shortRoot_conjugate] at hc
  change shortRoot (shortRootPosition (shortRootCycleLabel r)).1
    (shortRootPosition (shortRootCycleLabel r)).2 t ∈ _
  rw [shortRootCycleLabel_position]
  exact hc

/-- Four axial Weyl reflections and the coordinate cycle, on actual root labels. -/
def shortRootStepLabel (g : Fin 5) (r : Fin 24) : Fin 24 :=
  ![shortWeylRootDestination 0,shortWeylRootDestination 1,
    shortWeylRootDestination 2,shortWeylRootDestination 3,shortRootCycleLabel] g r

private theorem shortRootDerivedAt_step (g : Fin 5) (r : Fin 24)
    (hr : ShortRootDerivedAt F r) : ShortRootDerivedAt F (shortRootStepLabel g r) := by
  fin_cases g
  · exact shortRootDerivedAt_weyl 0 r hr
  · exact shortRootDerivedAt_weyl 1 r hr
  · exact shortRootDerivedAt_weyl 2 r hr
  · exact shortRootDerivedAt_weyl 3 r hr
  · exact shortRootDerivedAt_cycle r hr

/-- Words are applied in chronological order. -/
def shortRootWordLabel : List (Fin 5) → Fin 24 → Fin 24
  | [],r => r
  | g::w,r => shortRootWordLabel w (shortRootStepLabel g r)

def shortRootDerivedWitness : Fin 24 → List (Fin 5) :=
  ![[4,0,4],[3,4,1,4],[3,4,2,4],[],[3],[4,2,4],[4,1,4],[3,4,0,4],
    [4,0,3],[4,0,2],[4,0,1],[4],[3,4],[4,2,3],[4,1,3],[4,1,2],
    [4,0],[3,4,1],[3,4,2],[4,4],[4,3],[4,2],[4,1],[3,4,0]]

theorem shortRootDerivedWitness_correct : ∀ r : Fin 24,
    shortRootWordLabel (shortRootDerivedWitness r) 3 = r := by
  decide +kernel

private theorem shortRootDerivedAt_word (w : List (Fin 5)) (r : Fin 24)
    (hr : ShortRootDerivedAt F r) : ShortRootDerivedAt F (shortRootWordLabel w r) := by
  induction w generalizing r with
  | nil => exact hr
  | cons g w ih => exact ih _ (shortRootDerivedAt_step g r hr)

theorem shortRoot_flat_mem_commutator (r : Fin 24) (t : F) :
    shortRoot (shortRootPosition r).1 (shortRootPosition r).2 t ∈ commutator (Model F) := by
  have h := shortRootDerivedAt_word (shortRootDerivedWitness r) 3
    (shortRootDerivedAt_seed (F := F))
  rw [shortRootDerivedWitness_correct] at h
  exact h t

theorem shortRoot_mem_commutator (p : Fin 3) (i : Fin 8) (t : F) :
    shortRoot p i t ∈ commutator (Model F) := by
  let r : Fin 24 := ⟨8*p.val+i.val,by omega⟩
  have hp : shortRootPosition r = (p,i) := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [shortRootPosition,r] <;> omega
  have h := shortRoot_flat_mem_commutator r t
  simpa only [hp] using h

end Atlas.F4
