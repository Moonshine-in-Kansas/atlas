import Atlas.LinearGroups.Symplectic.PairedMatrices
import Atlas.LinearGroups.Symplectic.Generation

/-! Elementary generation by paired short roots and coordinate long roots.
The only division is by a chosen nonzero vector coordinate. -/
noncomputable section
namespace Atlas.Symplectic
open Matrix
variable {r : ℕ} {K : Type*} [Field K]

private theorem f_transvection_inl (i k : Fin r) (a : K) (x : Vector r K) :
    (transvection (f i) a • x) (.inl k) = x (.inl k) := by
  simp [transvection_apply, f, Pi.single_apply]

private theorem f_transvection_inr (i k : Fin r) (a : K) (x : Vector r K) :
    (transvection (f i) a • x) (.inr k) =
      x (.inr k) + if k = i then a * x (.inl i) else 0 := by
  rw [transvection_apply, form_f_right]
  by_cases hk : k = i <;> simp_all [f, Pi.single_apply]

private theorem ff_transvection_inl (i j k : Fin r) (a : K) (x : Vector r K) :
    (transvection (f i + f j) a • x) (.inl k) = x (.inl k) := by
  simp [transvection_apply, f, Pi.single_apply]

private theorem ff_transvection_inr (i j k : Fin r) (hij : i ≠ j)
    (a c : K) (x : Vector r K) (hi : x (.inl i) = c) (hj : x (.inl j) = 0) :
    (transvection (f i + f j) a • x) (.inr k) =
      x (.inr k) + if k = i ∨ k = j then a * c else 0 := by
  rw [transvection_apply, map_add, form_f_right, form_f_right, hi, hj, add_zero]
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [f, Pi.single_apply]

private theorem reduce_upper (H : Subgroup (Sp r K))
    (hp : ∀ (i j : Fin r) (hij : i ≠ j) (a : K), pairedTransvection r K hij a ∈ H)
    (v : Vector r K) (i : Fin r) (hc : v (.inl i) ≠ 0) :
    ∃ g ∈ H, ∀ k : Fin r,
      (g • v) (.inl k) = if k = i then v (.inl i) else 0 := by
  have haux (S : Finset (Fin r)) : ∃ g ∈ H,
      (g • v) (.inl i) = v (.inl i) ∧
      ∀ k ∈ S, k ≠ i → (g • v) (.inl k) = 0 := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, H.one_mem, by simp⟩
    | @insert j S hj ih =>
      obtain ⟨g, hg, hi, hz⟩ := ih
      by_cases hji : j = i
      · refine ⟨g, hg, hi, ?_⟩
        intro k hk hki
        rcases Finset.mem_insert.mp hk with hkj | hk
        · exact (hki (hkj.trans hji)).elim
        · exact hz k hk hki
      · let a : K := -(g • v) (.inl j) / v (.inl i)
        let p := pairedTransvection r K hji a
        refine ⟨p * g, H.mul_mem (hp j i hji a) hg, ?_, ?_⟩
        · simpa only [mul_smul, p, pairedTransvection_inl, Ne.symm hji,
            if_false, add_zero] using hi
        · intro k hk hki
          rcases Finset.mem_insert.mp hk with hkj | hk
          · subst k
            rw [mul_smul, show p = pairedTransvection r K hji a from rfl,
              pairedTransvection_inl, if_pos rfl, hi]
            dsimp [a]
            rw [div_mul_cancel₀ _ hc, add_neg_cancel]
          · by_cases hkj : k = j
            · subst k
              rw [mul_smul, show p = pairedTransvection r K hji a from rfl,
                pairedTransvection_inl, if_pos rfl, hi]
              dsimp [a]
              rw [div_mul_cancel₀ _ hc, add_neg_cancel]
            · rw [mul_smul, show p = pairedTransvection r K hji a from rfl,
                pairedTransvection_inl, if_neg hkj, add_zero]
              exact hz k hk hki
  obtain ⟨g,hg,hi,hz⟩ := haux Finset.univ
  refine ⟨g,hg,fun k => ?_⟩
  by_cases hk : k = i
  · subst k; simpa using hi
  · simpa only [if_neg hk] using hz k (Finset.mem_univ k) hk

private theorem reduce_lower (H : Subgroup (Sp r K))
    (hp : ∀ (i j : Fin r) (hij : i ≠ j) (a : K), pairedTransvection r K hij a ∈ H)
    (hf : ∀ (i : Fin r) (a : K), transvection (f i) a ∈ H)
    (v : Vector r K) (i : Fin r) (c : K) (hc : c ≠ 0)
    (hu : ∀ k, v (.inl k) = if k = i then c else 0) :
    ∃ g ∈ H, g • v = c • e i := by
  have hff (j : Fin r) (hij : i ≠ j) (a : K) : transvection (f i + f j) a ∈ H := by
    rw [← pairedTransvection_f_add r K hij, ← transvection_conjugate]
    exact H.mul_mem (H.mul_mem (hp i j hij (-1)) (hf i a))
      (H.inv_mem (hp i j hij (-1)))
  have haux (S : Finset (Fin r)) : ∃ g ∈ H,
      (∀ k, (g • v) (.inl k) = if k = i then c else 0) ∧
      ∀ k ∈ S, k ≠ i → (g • v) (.inr k) = 0 := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, H.one_mem, by simpa using hu, by simp⟩
    | @insert j S hj ih =>
      obtain ⟨g,hg,hupper,hzero⟩ := ih
      by_cases hji : j = i
      · refine ⟨g,hg,hupper,?_⟩
        intro k hk hki
        rcases Finset.mem_insert.mp hk with hkj | hk
        · exact (hki (hkj.trans hji)).elim
        · exact hzero k hk hki
      · let a : K := -(g • v) (.inr j) / c
        let p : Sp r K := transvection (f i + f j) a
        have hi : (g • v) (.inl i) = c := by simpa using hupper i
        have hj' : (g • v) (.inl j) = 0 := by simpa [hji] using hupper j
        refine ⟨p * g, H.mul_mem (hff j (Ne.symm hji) a) hg, ?_, ?_⟩
        · intro k
          simpa only [mul_smul, p, ff_transvection_inl] using hupper k
        · intro k hk hki
          by_cases hkj : k = j
          · subst k
            rw [mul_smul, show p = transvection (f i + f j) a from rfl,
              ff_transvection_inr i j j (Ne.symm hji) a c (g • v) hi hj',
              if_pos (Or.inr rfl)]
            dsimp [a]
            rw [div_mul_cancel₀ _ hc, add_neg_cancel]
          · have hkS : k ∈ S := (Finset.mem_insert.mp hk).resolve_left hkj
            rw [mul_smul, show p = transvection (f i + f j) a from rfl,
              ff_transvection_inr i j k (Ne.symm hji) a c (g • v) hi hj',
              if_neg (not_or.mpr ⟨hki,hkj⟩), add_zero]
            exact hzero k hkS hki
  obtain ⟨g,hg,hupper,hzero⟩ := haux Finset.univ
  let a : K := -(g • v) (.inr i) / c
  let p : Sp r K := transvection (f i) a
  refine ⟨p * g, H.mul_mem (hf i a) hg, ?_⟩
  funext k
  cases k with
  | inl k =>
    rw [mul_smul, show p = transvection (f i) a from rfl, f_transvection_inl, hupper]
    by_cases hk : k = i <;> simp_all [e, Pi.single_apply]
  | inr k =>
    rw [mul_smul, show p = transvection (f i) a from rfl, f_transvection_inr]
    by_cases hk : k = i
    · subst k
      have hi : (g • v) (.inl i) = c := by simpa using hupper i
      rw [if_pos rfl, hi]
      dsimp [a]
      rw [div_mul_cancel₀ _ hc, add_neg_cancel]
      simp [e, Pi.single_apply]
    · rw [if_neg hk, add_zero, hzero k (Finset.mem_univ k) hk]
      simp [e, Pi.single_apply]

/-- Coordinate root elements generate the full symplectic group over any field.
No group cardinality, simplicity or characteristic bound enters the proof. -/
theorem eq_top_of_paired_and_axis (H : Subgroup (Sp r K))
    (hp : ∀ (i j : Fin r) (hij : i ≠ j) (a : K), pairedTransvection r K hij a ∈ H)
    (he : ∀ (i : Fin r) (a : K), transvection (e i) a ∈ H)
    (hf : ∀ (i : Fin r) (a : K), transvection (f i) a ∈ H) : H = ⊤ := by
  have hreduce (v : Vector r K) (hv : v ≠ 0) :
      ∃ g ∈ H, ∃ i : Fin r, ∃ c : K, c ≠ 0 ∧ g • v = c • e i := by
    have hstart : ∃ g ∈ H, ∃ i : Fin r, (g • v) (.inl i) ≠ 0 := by
      by_cases hu : ∃ i : Fin r, v (.inl i) ≠ 0
      · obtain ⟨i,hi⟩ := hu
        exact ⟨1,H.one_mem,i,by simpa using hi⟩
      · have hz : ∀ i : Fin r, v (.inl i) = 0 := by simpa using hu
        have hex : ∃ k, v k ≠ 0 := by
          by_contra! h
          exact hv (funext h)
        obtain ⟨k,hk⟩ := hex
        cases k with
        | inl i => exact (hk (hz i)).elim
        | inr i =>
          refine ⟨transvection (e i) 1, he i 1, i, ?_⟩
          rw [transvection_apply, form_e_right]
          simpa [e, Pi.single_apply, hz i] using neg_ne_zero.mpr hk
    obtain ⟨g,hg,i,hi⟩ := hstart
    obtain ⟨a,ha,hupper⟩ := reduce_upper H hp (g • v) i hi
    obtain ⟨b,hb,hresult⟩ := reduce_lower H hp hf (a • (g • v)) i
      ((g • v) (.inl i)) hi hupper
    exact ⟨b * (a * g), H.mul_mem hb (H.mul_mem ha hg), i,
      (g • v) (.inl i), hi, by simpa only [mul_smul] using hresult⟩
  have ht (v : Vector r K) (a : K) : transvection v a ∈ H := by
    by_cases hv : v = 0
    · subst v
      simpa only [transvection_zero_vector] using H.one_mem
    · obtain ⟨g,hg,i,c,hc,hgv⟩ := hreduce v hv
      have hm := H.mul_mem (H.mul_mem (H.inv_mem hg) (he i (c^2*a))) hg
      have heq : g⁻¹ * transvection (e i) (c^2*a) * g = transvection v a := by
        rw [← transvection_scale, ← hgv, ← transvection_conjugate]
        simp [mul_assoc]
      rwa [heq] at hm
  have hle : transvectionGroup r K ≤ H := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨v,a,rfl⟩
    exact ht v a
  exact top_unique (fun g _ => hle (mem_transvectionGroup r g))

end Atlas.Symplectic
