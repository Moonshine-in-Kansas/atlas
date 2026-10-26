import Atlas.LinearGroups.Triality.BruhatDisjoint

/-! Matrix-entry restrictions on the intersection of two actual Borels. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal

def rootSurvives (w : Fin 12) : Fin 6 → Bool :=
  ![decide ((shortSignedWord (weylWord w) 0).val < 3),
    decide ((longSignedWord (weylWord w) 0).val < 3),
    decide ((shortSignedWord (weylWord w) 1).val < 3),
    decide ((shortSignedWord (weylWord w) 2).val < 3),
    decide ((longSignedWord (weylWord w) 1).val < 3),
    decide ((longSignedWord (weylWord w) 2).val < 3)]

def rootEntry : Fin 6 → Index 4 × Index 4 :=
  ![(.inl 0,.inl 1),(.inl 1,.inl 2),(.inr 2,.inr 0),
    (.inl 1,.inr 2),(.inl 0,.inr 2),(.inl 0,.inr 1)]

theorem rootSurvives_entry : ∀ w : Fin 12, ∀ r : Fin 6, rootSurvives w r = false →
    coordinateHeight (coordinateWord (weylWord w) (rootEntry r).2) <
      coordinateHeight (coordinateWord (weylWord w) (rootEntry r).1) := by decide

theorem rootSurvives_u : ∀ w : Fin 12, rootSurvives w 4 = false →
    rootSurvives w 0 = false ∨ rootSurvives w 3 = false := by decide

theorem rootSurvives_v : ∀ w : Fin 12, rootSurvives w 5 = false →
    (rootSurvives w 2 = false ∨ rootSurvives w 3 = false) ∧
    (rootSurvives w 0 = false ∨ rootSurvives w 1 = false ∨ rootSurvives w 3 = false) ∧
    (rootSurvives w 0 = false ∨ rootSurvives w 2 = false) := by decide

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem weyl_conjugate_below (w : Fin 12) (g : O_DPlus 4 K)
    (hg : (weylLift F K w)⁻¹ * g * weylLift F K w ∈ borel F K hdeg)
    (i j : Index 4)
    (hij : coordinateHeight (coordinateWord (weylWord w) j) <
      coordinateHeight (coordinateWord (weylWord w) i)) :
    g.val (Pi.single j 1) i = 0 := by
  let b : borel F K hdeg := ⟨_,hg⟩
  have he : g*weylLift F K w=weylLift F K w*b.val := by dsimp [b]; group
  obtain ⟨u,hu⟩ := weylLift_single F K w j
  obtain ⟨z,hz⟩ := weylWord_row F K (weylWord w) i
  have hentry := congrArg (fun a : O_DPlus 4 K =>
    a.val (Pi.single (coordinateWord (weylWord w) j) 1) i) he
  change g.val ((weylLift F K w).val _) i = (weylLift F K w).val (b.val.val _) i at hentry
  rw [hu,map_smul] at hentry
  rw [show (weylLift F K w).val _ i = _ from hz _] at hentry
  rw [borel_below F K hdeg b _ _ hij,mul_zero] at hentry
  exact (mul_eq_zero.mp hentry).resolve_left u.ne_zero

def SurvivingParameters (w : Fin 12) (p : PositiveParameters F K) : Prop :=
  (rootSurvives w 0 = false → p.a=0) ∧
  (rootSurvives w 1 = false → p.b=0) ∧
  (rootSurvives w 2 = false → p.c=0) ∧
  (rootSurvives w 3 = false → p.d=0) ∧
  (rootSurvives w 4 = false → p.u=0) ∧
  (rootSurvives w 5 = false → p.v=0)

theorem survivingParameters_of_conjugate (w : Fin 12) (p : PositiveParameters F K)
    (hp : (weylLift F K w)⁻¹ * positiveMatrix F K p * weylLift F K w ∈ borel F K hdeg) :
    SurvivingParameters F K w p := by
  have he (r : Fin 6) (hr : rootSurvives w r = false) :=
    weyl_conjugate_below F K hdeg w (positiveMatrix F K p) hp
      (rootEntry r).1 (rootEntry r).2 (rootSurvives_entry w r hr)
  have ha (hr : rootSurvives w 0 = false) : p.a=0 := by
    have hh := he 0 hr
    simpa [positiveMatrix,positiveWord_apply,positiveAction,rootEntry,Pi.single_apply] using hh
  have hb (hr : rootSurvives w 1 = false) : p.b=0 := by
    have hh := he 1 hr
    have hh' : algebraMap F K p.b=0 := by
      simpa [positiveMatrix,positiveWord_apply,positiveAction,rootEntry,Pi.single_apply] using hh
    exact (algebraMap F K).injective (by simpa using hh')
  have hc (hr : rootSurvives w 2 = false) : p.c=0 := by
    have hh := he 2 hr
    simpa [positiveMatrix,positiveWord_apply,positiveAction,rootEntry,Pi.single_apply] using hh
  have hd (hr : rootSurvives w 3 = false) : p.d=0 := by
    have hh := he 3 hr
    simpa [positiveMatrix,positiveWord_apply,positiveAction,rootEntry,Pi.single_apply] using hh
  have hu (hr : rootSurvives w 4 = false) : p.u=0 := by
    have hh := he 4 hr
    have hz : p.a*p.d=0 := by
      rcases rootSurvives_u w hr with h|h
      · simp [ha h]
      · simp [hd h]
    have hh' : algebraMap F K p.u=0 := by
      simpa [positiveMatrix,positiveWord_apply,positiveAction,rootEntry,Pi.single_apply,hz] using hh
    exact (algebraMap F K).injective (by simpa using hh')
  refine ⟨ha,hb,hc,hd,hu,?_⟩
  intro hr
  have hh := he 5 hr
  obtain ⟨hcd,habd,hac⟩ := rootSurvives_v w hr
  have hcd' : p.c*p.d=0 := by
    rcases hcd with h|h
    · simp [hc h]
    · simp [hd h]
  have habd' : p.a*algebraMap F K p.b*p.d=0 := by
    rcases habd with h|h|h
    · simp [ha h]
    · simp [hb h]
    · simp [hd h]
  have hac' : p.a*FiniteCubic.sigma F K p.c*FiniteCubic.sigma F K (FiniteCubic.sigma F K p.c)=0 := by
    rcases hac with h|h
    · simp [ha h]
    · simp [hc h]
  have hh' : algebraMap F K p.v=0 := by
    simpa [positiveMatrix,positiveWord_apply,positiveAction,rootEntry,Pi.single_apply,hcd',habd',hac'] using hh
  exact (algebraMap F K).injective (by simpa using hh')

end Atlas.Triality
