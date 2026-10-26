import Atlas.LinearGroups.Triality.PositiveSpecializations
import Atlas.LinearGroups.Triality.WeylDistinct

/-! All twelve signed relative roots, as literal orthogonal transformations. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def nextNegativeRoot (t : K) : O_DPlus 4 K :=
  differenceRoot 2 0 (by decide) (-t) *
    differenceRoot 3 1 (by decide) (FiniteCubic.sigma F K t) *
    negativeSumRoot 1 3 (FiniteCubic.sigma F K (FiniteCubic.sigma F K t))

def middleNegativeRoot (t : K) : O_DPlus 4 K :=
  differenceRoot 3 0 (by decide) (FiniteCubic.sigma F K (FiniteCubic.sigma F K t)) *
    negativeSumRoot 0 3 (FiniteCubic.sigma F K t) * negativeSumRoot 1 2 t

def highNegativeRoot (t : F) : O_DPlus 4 K := negativeSumRoot 0 2 (algebraMap F K t)
def highestNegativeRoot (t : F) : O_DPlus 4 K := negativeSumRoot 0 1 (algebraMap F K t)

def shortSignedRoot (i : Fin 6) (t : K) : O_DPlus 4 K :=
  ![shortRoot F K t,nextShortRoot F K t,middleRoot F K t,
    shortNegativeRoot F K t,nextNegativeRoot F K t,middleNegativeRoot F K t] i

def longSignedRoot (i : Fin 6) (t : F) : O_DPlus 4 K :=
  ![longRoot F K t,highLongRoot F K t,highestRoot F K t,
    longNegativeRoot F K t,highNegativeRoot F K t,highestNegativeRoot F K t] i

def shortSignedReflection (s : Bool) : Fin 6 → Fin 6 :=
  if s then ![3,2,1,0,5,4] else ![1,0,2,4,3,5]
def longSignedReflection (s : Bool) : Fin 6 → Fin 6 :=
  if s then ![1,0,2,4,3,5] else ![3,2,1,0,5,4]

def shortSignedNegate (s : Bool) : Fin 6 → Bool :=
  if s then ![true,true,false,true,true,false] else ![false,true,false,false,true,false]
def longSignedNegate (s : Bool) : Fin 6 → Bool :=
  if s then ![true,false,false,true,false,false] else ![true,false,true,true,false,true]

set_option maxHeartbeats 8000000 in
-- Twelve short-root identities, each verified on all eight coordinates.
theorem shortSignedRoot_intertwine (s : Bool) (i : Fin 6) (t : K) :
    (if s then shortWeyl F K else longWeyl F K) * shortSignedRoot F K i t =
      shortSignedRoot F K (shortSignedReflection s i) (if shortSignedNegate s i then -t else t) *
        (if s then shortWeyl F K else longWeyl F K) := by
  cases s <;> fin_cases i
  all_goals
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    ext j
    rcases j with j|j <;> fin_cases j <;>
      simp [shortSignedRoot, shortSignedReflection, shortSignedNegate,
        shortWeyl_apply, longWeyl_apply, shortRoot, nextShortRoot, middleRoot,
        shortNegativeRoot, nextNegativeRoot, middleNegativeRoot, pinnedRoot, pinnedNegativeRoot,
        Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply,
        negativeSumRoot_apply, e, f] <;> ring

set_option maxHeartbeats 8000000 in
-- Twelve long-root identities, valid also in characteristics two and three.
theorem longSignedRoot_intertwine (s : Bool) (i : Fin 6) (t : F) :
    (if s then shortWeyl F K else longWeyl F K) * longSignedRoot F K i t =
      longSignedRoot F K (longSignedReflection s i) (if longSignedNegate s i then -t else t) *
        (if s then shortWeyl F K else longWeyl F K) := by
  cases s <;> fin_cases i
  all_goals
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    ext j
    rcases j with j|j <;> fin_cases j <;>
      simp [longSignedRoot, longSignedReflection, longSignedNegate,
        shortWeyl_apply, longWeyl_apply, longRoot, highLongRoot, highestRoot,
        longNegativeRoot, highNegativeRoot, highestNegativeRoot, pinnedRoot, pinnedNegativeRoot,
        Subgroup.coe_mul, LinearEquiv.mul_apply, differenceRoot_apply, sumRoot_apply,
        negativeSumRoot_apply, e, f, Algebra.smul_def] <;> ring

end Atlas.Triality
