import Atlas.LinearGroups.F4.FieldPointTransport
import Atlas.LinearGroups.F4.RootGroups

/-! Field isomorphisms carry the actual 48 root groups, with their parameters,
to the corresponding root groups in the transported Albert model. -/
noncomputable section
namespace Atlas.F4
variable {F K : Type*} [Field F] [Field K]

private theorem fieldTransport_eq_of_natural (f : F ≃+* K) (g : Model F) (h : Model K)
    (hn : ∀ x, h.val (Atlas.Albert.map f.toRingHom x) = Atlas.Albert.map f.toRingHom (g.val x)) :
    fieldTransport f g = h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro y
  let x := Atlas.Albert.map f.symm.toRingHom y
  have hx : Atlas.Albert.map f.toRingHom x = y := coefficient_inverse f.symm y
  rw [←hx,fieldTransport_apply]
  exact (hn x).symm

theorem fieldTransport_shortRootFirstPair (f : F ≃+* K) (i : Fin 8) (t : F) :
    fieldTransport f (shortRootFirstPair i t) = shortRootFirstPair i (f t) := by
  apply fieldTransport_eq_of_natural
  intro x
  exact Atlas.Albert.shortRootLinear_map f.toRingHom i t x

theorem fieldTransport_coordinateCycle (f : F ≃+* K) :
    fieldTransport f coordinateCycle = coordinateCycle := by
  apply fieldTransport_eq_of_natural
  intro x
  exact Atlas.Albert.coordinateCycle_map f.toRingHom x

theorem fieldTransport_shortRoot (f : F ≃+* K) (p : Fin 3) (i : Fin 8) (t : F) :
    fieldTransport f (shortRoot p i t) = shortRoot p i (f t) := by
  simp only [shortRoot,map_mul,map_inv,map_pow,fieldTransport_coordinateCycle,
    fieldTransport_shortRootFirstPair]

theorem fieldTransport_shortWeylFirstPair (f : F ≃+* K) (i : Fin 8) :
    fieldTransport f (shortWeylFirstPair i) = shortWeylFirstPair i := by
  simp only [shortWeylFirstPair,map_mul,fieldTransport_shortRootFirstPair,map_one]

theorem fieldTransport_longRootStep (f : F ≃+* K) (g : Fin 5) :
    fieldTransport f (longRootStepElement g) = longRootStepElement g := by
  fin_cases g <;> simp [longRootStepElement,fieldTransport_shortWeylFirstPair,
    fieldTransport_coordinateCycle]

theorem fieldTransport_longRootWord (f : F ≃+* K) (w : List (Fin 5)) :
    fieldTransport f (longRootWordElement w) = longRootWordElement w := by
  induction w with
  | nil => simp [longRootWordElement]
  | cons g w ih => simp only [longRootWordElement,map_mul,ih,fieldTransport_longRootStep]

theorem fieldTransport_longRootSeeds (f : F ≃+* K) (s : Fin 3) (t : F) :
    fieldTransport f (longRootSeeds s t) = longRootSeeds s (f t) := by
  apply fieldTransport_eq_of_natural
  intro x
  rw [longRootSeeds_apply,longRootSeeds_apply]
  fin_cases s
  all_goals
    apply Prod.ext
    · rfl
    · ext j i; fin_cases i <;>
        simp [Atlas.Albert.map,Atlas.G2.Explicit.rootAApply,
          Atlas.G2.Explicit.rootBApply,Atlas.G2.Explicit.rootEApply]

theorem fieldTransport_longRoot (f : F ≃+* K) (r : Fin 24) (t : F) :
    fieldTransport f (longRoot r t) = longRoot r (f t) := by
  simp only [longRoot,map_mul,map_inv,fieldTransport_longRootWord,fieldTransport_longRootSeeds]

theorem fieldTransport_root (f : F ≃+* K) (r : RootData.Root) (t : F) :
    fieldTransport f (root r t) = root r (f t) := by
  unfold root
  split_ifs
  · exact fieldTransport_longRoot f _ t
  · exact fieldTransport_shortRoot f _ _ t

end Atlas.F4
