import Atlas.Comparisons.Exceptional.G2Binary.QuadraticAction
import Atlas.Algebra.SplitOctonion.TraceKernelIsometry

namespace Atlas.Comparisons.G2Binary
open Atlas.SplitOctonion

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem traceZero_root_difference : ∀ x : V, trace x = 0 →
    ∃ a : V, IsQuadraticRoot a ∧ IsQuadraticRoot (x + a) := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem traceZero_partner_norm : ∀ x : V, trace x = 0 → norm (partner x) ≠ norm x := by decide

theorem partner_add_left (x y : V) : partner x + y = partner (x + y) := by
  simp only [partner, add_assoc]

theorem partner_add_right (x y : V) : x + partner y = partner (x + y) := by
  simp only [partner]; abel

theorem partner_add_both (x y : V) : partner x + partner y = x + y := by
  have hu : (unit : V) + unit = 0 := by decide
  calc
    _ = (unit + unit) + (x + y) := by simp only [partner]; abel
    _ = _ := by rw [hu, zero_add]

theorem pointKernel_root (g : Automorphism K) (hg : ∀ p : QuadraticPoint, g • p = p)
    (x : V) (hx : IsQuadraticRoot x) : g.val x = x ∨ g.val x = partner x := by
  have h := congrArg Subtype.val (hg (pointOfRoot ⟨x,hx⟩))
  change normalize (g.val (normalize x)) = normalize x at h
  rw [normalize_automorphism_normalize] at h
  exact (normalize_eq_iff _ _).mp h

theorem pointKernel_traceZero (g : Automorphism K) (hg : ∀ p : QuadraticPoint, g • p = p)
    (x : V) (hx : trace x = 0) : g.val x = x := by
  obtain ⟨a, ha, hxa⟩ := traceZero_root_difference x hx
  have hsum : a + (x + a) = x := by
    have haa : a + a = 0 := by ext i; exact CharTwo.add_self_eq_zero (a i)
    calc
      _ = x + (a + a) := by abel
      _ = x := by rw [haa,add_zero]
  have he : g.val x = x ∨ g.val x = partner x := by
    have hmap := map_add g.val a (x+a)
    rw [hsum] at hmap
    rcases pointKernel_root g hg a ha with h | h <;>
      rcases pointKernel_root g hg (x+a) hxa with h' | h'
    · exact Or.inl (by simpa [h,h',hsum] using hmap)
    · exact Or.inr (by simpa [h,h',partner_add_right,hsum] using hmap)
    · exact Or.inr (by simpa [h,h',partner_add_left,hsum] using hmap)
    · exact Or.inl (by simpa [h,h',partner_add_both,hsum] using hmap)
  rcases he with he | he
  · exact he
  · exact False.elim (traceZero_partner_norm x hx (he ▸ automorphism_norm g x))

/-- Faithfulness follows from multiplication and norm, not group order. -/
instance quadraticPoint_faithful : FaithfulSMul (Automorphism K) QuadraticPoint := by
  apply faithfulSMul_iff.mpr
  intro g hg
  rcases normIsometry_unit_traceKernel g.val (automorphism_norm g)
      (automorphism_unit g) (pointKernel_traceZero g hg) with h | h
  · apply Subtype.ext
    exact LinearEquiv.ext h
  · have hm := automorphism_mul g (basisVector 0) (basisVector 7)
    simp only [h.2] at hm
    have hfalse : conjugate (mul (basisVector (F := K) 0) (basisVector 7)) ≠
        mul (conjugate (basisVector 0)) (conjugate (basisVector 7)) := by decide
    exact False.elim (hfalse hm)

end Atlas.Comparisons.G2Binary
