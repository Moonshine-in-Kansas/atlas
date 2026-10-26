import Atlas.LinearGroups.Chevalley.RootData.TypeAMinimalRepresentatives
import Mathlib.Algebra.Group.Subgroup.Ker

/-! The coordinate-zero parabolic is the actual lower-rank type-A Weyl group,
with the ambient shortest word length equal to its intrinsic shortest length. -/
noncomputable section
namespace Atlas.Chevalley.TypeAData
open Classical RootData

def coordinateTailHom (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) where
  toFun e := Equiv.Perm.decomposeFin.symm (0, e)
  map_one' := by simp; rfl
  map_mul' e f := by
    apply Equiv.ext
    intro i
    cases i using Fin.cases with
    | zero => simp [Equiv.Perm.mul_apply]
    | succ i => simp [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.Perm.mul_apply]

@[simp] theorem coordinateTailHom_zero (n : ℕ) (e : Equiv.Perm (Fin n)) :
    coordinateTailHom n e 0 = 0 := by
  exact Equiv.Perm.decomposeFin_symm_apply_zero 0 e

@[simp] theorem coordinateTailHom_succ (n : ℕ) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    coordinateTailHom n e i.succ = (e i).succ := by
  change Equiv.Perm.decomposeFin.symm (0, e) i.succ = _
  simp [Equiv.Perm.decomposeFin_symm_apply_succ]

theorem coordinateTailHom_injective (n : ℕ) : Function.Injective (coordinateTailHom n) := by
  intro e f h
  apply Equiv.ext
  intro i
  have hi := congrArg (fun p : Equiv.Perm (Fin (n + 1)) => p i.succ) h
  simpa only [coordinateTailHom_succ, Fin.succ_inj] using hi

theorem mem_coordinateTailHom_range (n : ℕ) (e : Equiv.Perm (Fin (n + 1))) :
    e ∈ (coordinateTailHom n).range ↔ e 0 = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact coordinateTailHom_zero n f
  · intro he
    obtain ⟨⟨k, f⟩, h⟩ := Equiv.Perm.decomposeFin.symm.surjective e
    have hk : k = 0 := by
      have h0 := congrArg (fun p : Equiv.Perm (Fin (n + 1)) => p 0) h
      simpa only [Equiv.Perm.decomposeFin_symm_apply_zero, he] using h0
    subst k
    exact ⟨f, h⟩

def tailWeylHom (r : ℕ) : (pairing (r + 1)).weylGroupToPerm.range →*
    (pairing (r + 2)).weylGroupToPerm.range :=
  (coordinateWeylEquiv (r + 2)).toMonoidHom.comp
    ((coordinateTailHom (r + 1)).comp (coordinateWeylEquiv (r + 1)).symm.toMonoidHom)

@[simp] theorem tailWeylHom_coordinate (r : ℕ) (e : Equiv.Perm (Fin (r + 1))) :
    tailWeylHom r (coordinateWeylEquiv (r + 1) e) =
      coordinateWeylEquiv (r + 2) (coordinateTailHom (r + 1) e) := by
  simp only [tailWeylHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

theorem tailWeylHom_injective (r : ℕ) : Function.Injective (tailWeylHom r) :=
  (coordinateWeylEquiv (r + 2)).injective.comp
    ((coordinateTailHom_injective (r + 1)).comp (coordinateWeylEquiv (r + 1)).symm.injective)

theorem tailWeylHom_range (r : ℕ) :
    (tailWeylHom r).range = rootParabolicSubgroup (pairing (r + 2))
      (base (r + 1)) (firstZeroWalls r) := by
  ext w
  obtain ⟨e, rfl⟩ := (coordinateWeylEquiv (r + 2)).surjective w
  rw [coordinateWeyl_mem_zero_parabolic_iff]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨f, rfl⟩ := (coordinateWeylEquiv (r + 1)).surjective v
    rw [tailWeylHom_coordinate] at hv
    have he := (coordinateWeylEquiv (r + 2)).injective hv
    rw [← he]
    exact coordinateTailHom_zero (r + 1) f
  · intro he
    obtain ⟨f, hf⟩ := (mem_coordinateTailHom_range (r + 1) e).mpr he
    refine ⟨coordinateWeylEquiv (r + 1) f, ?_⟩
    rw [tailWeylHom_coordinate, hf]

def lowerRankParabolicEquiv (r : ℕ) :
    (pairing (r + 1)).weylGroupToPerm.range ≃*
      rootParabolicSubgroup (pairing (r + 2)) (base (r + 1)) (firstZeroWalls r) :=
  (MonoidHom.ofInjective (tailWeylHom_injective r)).trans
    (MulEquiv.subgroupCongr (tailWeylHom_range r))

private def tailRoot {n : ℕ} (a : Root n) : Root (n + 1) :=
  ⟨(a.val.1.succ, a.val.2.succ), fun h => a.property (Fin.succ_injective _ h)⟩

private theorem tail_inversion_count (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun a : Root n =>
      a.val.1 < a.val.2 ∧ e a.val.2 < e a.val.1)).card =
    (Finset.univ.filter (fun a : Root (n + 1) =>
      a.val.1 < a.val.2 ∧ coordinateTailHom n e a.val.2 <
        coordinateTailHom n e a.val.1)).card := by
  apply Finset.card_bij (fun a _ => tailRoot a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    change a.val.1.succ < a.val.2.succ ∧
      coordinateTailHom n e a.val.2.succ < coordinateTailHom n e a.val.1.succ
    simpa only [coordinateTailHom_succ, Fin.succ_lt_succ_iff] using ha
  · intro a ha b hb h
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.succ_injective _ (congrArg (fun x : Root (n + 1) => x.val.1) h)
    · exact Fin.succ_injective _ (congrArg (fun x : Root (n + 1) => x.val.2) h)
  · intro a ha
    have h := (Finset.mem_filter.mp ha).2
    have hfirst : a.val.1 ≠ 0 := by
      intro hz
      have hh := h.2
      rw [hz, coordinateTailHom_zero] at hh
      exact (Fin.not_lt_zero _) hh
    have hsecond : a.val.2 ≠ 0 := by
      intro hz
      have hh := h.1
      rw [hz] at hh
      exact (Fin.not_lt_zero _) hh
    let b : Root n := ⟨(a.val.1.pred hfirst, a.val.2.pred hsecond), by
      intro he
      have hs := congrArg Fin.succ he
      simp only [Fin.succ_pred] at hs
      exact a.property hs⟩
    have hb : tailRoot b = a := by
      apply Subtype.ext
      apply Prod.ext
      · exact Fin.succ_pred _ hfirst
      · exact Fin.succ_pred _ hsecond
    refine ⟨b, ?_, hb⟩
    rw [← hb] at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change b.val.1.succ < b.val.2.succ ∧
      coordinateTailHom n e b.val.2.succ < coordinateTailHom n e b.val.1.succ at h
    simpa only [coordinateTailHom_succ, Fin.succ_lt_succ_iff] using h

/-- The lower-rank length is exactly the ambient length, including the rank-zero base. -/
theorem lowerRankParabolicEquiv_length (r : ℕ)
    (w : (pairing (r + 1)).weylGroupToPerm.range) :
    rootWeylLength (pairing (r + 2)) (base (r + 1))
      (lowerRankParabolicEquiv r w).val =
        rootWeylLength (pairing (r + 1)) (base r) w := by
  obtain ⟨e, rfl⟩ := (coordinateWeylEquiv (r + 1)).surjective w
  change rootWeylLength (pairing (r + 2)) (base (r + 1))
    (tailWeylHom r (coordinateWeylEquiv (r + 1) e)) = _
  rw [tailWeylHom_coordinate, coordinateWeylEquiv_length, coordinateWeylEquiv_length]
  exact (tail_inversion_count (r + 1) e).symm

end Atlas.Chevalley.TypeAData
