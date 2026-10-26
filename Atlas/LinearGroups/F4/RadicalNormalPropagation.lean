import Atlas.LinearGroups.F4.RadicalRootMembership
import Atlas.LinearGroups.F4.RootGroups

/-! Normal root propagation from actual local root subgroups. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def NormalShortRootAt (N : Subgroup (Model F)) (r : Fin 24) : Prop :=
  ∀t : F, shortRoot (shortRootPosition r).1 (shortRootPosition r).2 t∈N

variable (N : Subgroup (Model F)) [N.Normal]

theorem normalShortRootAt_weyl (i : Fin 8) (r : Fin 24)
    (hr : NormalShortRootAt N r) : NormalShortRootAt N (shortWeylRootDestination i r) := by
  intro t
  have hs : (shortWeylRootSign i r : F)^2 = 1 := by
    have h := congrArg (fun n : ℤ => (n : F)) (shortWeylRootSign_sq i r)
    simpa only [Int.cast_pow,Int.cast_one] using h
  have hc := (inferInstance : N.Normal).conj_mem _
    (hr ((shortWeylRootSign i r : F)*t)) (shortWeylFirstPair i)
  rw [shortWeyl_shortRoot_conjugate] at hc
  simpa only [←mul_assoc,←pow_two,hs,one_mul] using hc

theorem normalShortRootAt_cycle (r : Fin 24)
    (hr : NormalShortRootAt N r) : NormalShortRootAt N (shortRootCycleLabel r) := by
  intro t
  have hc := (inferInstance : N.Normal).conj_mem _ (hr t) coordinateCycle
  rw [coordinateCycle_shortRoot_conjugate] at hc
  change shortRoot (shortRootPosition (shortRootCycleLabel r)).1
    (shortRootPosition (shortRootCycleLabel r)).2 t ∈ _
  rw [shortRootCycleLabel_position]
  exact hc

theorem normalShortRootAt_step (g : Fin 5) (r : Fin 24)
    (hr : NormalShortRootAt N r) : NormalShortRootAt N (shortRootStepLabel g r) := by
  fin_cases g
  · exact normalShortRootAt_weyl N 0 r hr
  · exact normalShortRootAt_weyl N 1 r hr
  · exact normalShortRootAt_weyl N 2 r hr
  · exact normalShortRootAt_weyl N 3 r hr
  · exact normalShortRootAt_cycle N r hr

theorem normalShortRootAt_word (w : List (Fin 5)) (r : Fin 24)
    (hr : NormalShortRootAt N r) : NormalShortRootAt N (shortRootWordLabel w r) := by
  induction w generalizing r with
  | nil => exact hr
  | cons g w ih => exact ih _ (normalShortRootAt_step N g r hr)

theorem normalShortRootAt_all (h3 : NormalShortRootAt N 3) (r : Fin 24) :
    NormalShortRootAt N r := by
  have h := normalShortRootAt_word N (shortRootDerivedWitness r) 3 h3
  rw [shortRootDerivedWitness_correct] at h
  exact h

theorem normal_contains_radical_short_seed (hR : radicalSubgroup (F:=F) ≤ N) :
    NormalShortRootAt N 3 := by
  intro t
  have hs : shortRoot 2 3 t∈N := by
    have h := hR (halfRoot_mem_radical (F:=F) 7 (-t))
    simpa [halfRoot,halfRootIndex,halfRootSign,shortRootPosition] using h
  have h := (inferInstance : N.Normal).conj_mem _ hs coordinateCycle
  rw [coordinateCycle_shortRoot_conjugate] at h
  exact h

theorem normal_contains_radical_long (hR : radicalSubgroup (F:=F) ≤ N)
    (r : Fin 24) (t : F) : longRoot r t∈N := by
  have hz (k : Fin 6) (u : F) : longRoot (centralSevenLongLabel k) u∈N := by
    have h := hR (centralSeven_mem_radical (Pi.single k.castSucc u))
    rw [centralSeven_singleton] at h
    simpa [centralSevenSingleton,k.isLt] using h
  have hs (k : Fin 3) (u : F) : longRootSeeds k u∈N := by
    fin_cases k
    · have h := hz 0 u
      simpa [centralSevenLongLabel,longRoot,longRootWitness,longRootSeedFor,longRootWordElement] using h
    · have h := hz 2 u
      simpa [centralSevenLongLabel,longRoot,longRootWitness,longRootSeedFor,longRootWordElement] using h
    · let w : Model F := longRootWordElement (longRootWitness 8)
      have h0 : longRoot 8 u∈N := hz 4 u
      have h := (inferInstance : N.Normal).conj_mem _ h0 w⁻¹
      have he : longRoot 8 u=w*longRootSeeds 2 u*w⁻¹ := rfl
      rw [he] at h
      have hh : w⁻¹*(w*longRootSeeds 2 u*w⁻¹)*(w⁻¹)⁻¹=longRootSeeds 2 u := by group
      rwa [hh] at h
  exact (inferInstance : N.Normal).conj_mem _ (hs (longRootSeedFor r) t)
    (longRootWordElement (longRootWitness r))

theorem rootGenerated_le_of_normal_contains_radical (hR : radicalSubgroup (F:=F) ≤ N) :
    rootGenerated (F:=F) ≤ N := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨r,t,rfl⟩
  unfold root
  split_ifs
  · exact normal_contains_radical_long N hR _ t
  · exact normalShortRootAt_all N (normal_contains_radical_short_seed N hR) _ t

end Atlas.F4
