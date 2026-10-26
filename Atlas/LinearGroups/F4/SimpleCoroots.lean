import Atlas.LinearGroups.F4.SimpleCorootActions
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]
attribute [local irreducible] longRoot

theorem simplePositive_mem_rootGenerated (j : Fin 4) (t : F) :
    simplePositive j t∈rootGenerated := by
  fin_cases j
  · exact longRoot_mem_rootGenerated (torusLongLabel 0) t
  · exact longRoot_mem_rootGenerated (torusLongLabel 2) t
  · exact shortRoot_mem_rootGenerated 0 3 t
  · exact shortRoot_mem_rootGenerated 2 3 t

theorem simpleNegative_mem_rootGenerated (j : Fin 4) (t : F) :
    simpleNegative j t∈rootGenerated := by
  fin_cases j
  · exact longRoot_mem_rootGenerated (torusLongLabel 1) t
  · exact longRoot_mem_rootGenerated (torusLongLabel 3) t
  · exact shortRoot_mem_rootGenerated 0 4 t
  · exact shortRoot_mem_rootGenerated 2 4 t

theorem simpleCorootWord_mem_rootGenerated (j : Fin 4) (a : Fˣ) :
    simpleCorootWord j a∈rootGenerated := by
  unfold simpleCorootWord
  repeat first | apply Subgroup.mul_mem | apply simplePositive_mem_rootGenerated |
    apply simpleNegative_mem_rootGenerated

theorem simplePositive_add (j : Fin 4) (s t : F) :
    simplePositive j s*simplePositive j t=simplePositive j (s+t) := by
  fin_cases j
  · exact longRoot_add (torusLongLabel 0) s t
  · exact longRoot_add (torusLongLabel 2) s t
  · exact (shortRoot_add 0 3 s t).symm
  · exact (shortRoot_add 2 3 s t).symm

theorem simpleNegative_add (j : Fin 4) (s t : F) :
    simpleNegative j s*simpleNegative j t=simpleNegative j (s+t) := by
  fin_cases j
  · exact longRoot_add (torusLongLabel 1) s t
  · exact longRoot_add (torusLongLabel 3) s t
  · exact (shortRoot_add 0 4 s t).symm
  · exact (shortRoot_add 2 4 s t).symm

theorem simplePositive_zero (j : Fin 4) : simplePositive (F:=F) j 0=1 := by
  have h := simplePositive_add (F:=F) j 0 0
  simp only [zero_add] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

theorem simpleNegative_zero (j : Fin 4) : simpleNegative (F:=F) j 0=1 := by
  have h := simpleNegative_add (F:=F) j 0 0
  simp only [zero_add] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)


end Atlas.F4
