import Atlas.LinearGroups.Unitary.TransvectionConjugation
import Atlas.LinearGroups.Unitary.CenterLines

/-! # Abelian transvection groups attached to actual isotropic vectors -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

/-- Trace-zero parameters with multiplicative notation for their additive law. -/
def lineTransvectionHom (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0) :
    Multiplicative (trace F K).ker →* SU F K n hdeg where
  toFun a := transvection hdeg v a.toAdd.val hv ((trace_zero_iff hdeg _).mp a.toAdd.prop)
  map_one' := by
    apply Subtype.ext
    exact transvectionMatrix_zero v
  map_mul' a b := by
    apply Subtype.ext
    exact (transvectionMatrix_mul v hv a.toAdd.val b.toAdd.val).symm

theorem lineTransvectionHom_injective (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0) (hv0 : v ≠ 0) :
    Function.Injective (lineTransvectionHom hdeg v hv) := by
  intro a b hab
  obtain ⟨x, hx⟩ := hermitian_left_surjective (F := F) v hv0 1
  change hermitian F K x v = 1 at hx
  have h := congrArg (fun g : SU F K n hdeg => g.val *ᵥ x) hab
  change transvectionMatrix (F := F) v a.toAdd.val *ᵥ x =
    transvectionMatrix (F := F) v b.toAdd.val *ᵥ x at h
  rw [transvectionMatrix_apply, transvectionMatrix_apply, hx, mul_one, mul_one] at h
  change a.toAdd = b.toAdd
  apply Subtype.ext
  exact smul_left_injective K hv0 (add_left_cancel h)

/-- The actual image subgroup, not an abstract group of the expected order. -/
def lineTransvections (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0) : Subgroup (SU F K n hdeg) :=
  (lineTransvectionHom hdeg v hv).range

theorem card_lineTransvections (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0) (hv0 : v ≠ 0) :
    Nat.card (lineTransvections hdeg v hv) = Nat.card F := by
  rw [lineTransvections, ← Nat.card_congr
    (MonoidHom.ofInjective (f := lineTransvectionHom hdeg v hv)
      (lineTransvectionHom_injective hdeg v hv hv0)).toEquiv]
  exact trace_kernel_card hdeg

theorem lineTransvections_commute (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0)
    (a b : lineTransvections hdeg v hv) : a * b = b * a := by
  apply Subtype.ext
  obtain ⟨x, hx⟩ := a.prop
  obtain ⟨y, hy⟩ := b.prop
  change a.val * b.val = b.val * a.val
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

instance lineTransvections_commutative (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0) :
    IsMulCommutative (lineTransvections hdeg v hv) :=
  ⟨⟨lineTransvections_commute hdeg v hv⟩⟩

/-- Rescaling the representative does not enlarge the transvection subgroup. -/
theorem lineTransvections_smul_le (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0) (c : K)
    (hcv : hermitian F K (c • v) (c • v) = 0) :
    lineTransvections hdeg (c • v) hcv ≤ lineTransvections hdeg v hv := by
  rintro _ ⟨a, rfl⟩
  refine ⟨Multiplicative.ofAdd (norm F K c • a.toAdd), ?_⟩
  apply Subtype.ext
  change transvectionMatrix (F := F) v _ = transvectionMatrix (F := F) (c • v) _
  rw [transvectionMatrix_smul]
  congr 1
  change norm F K c • a.toAdd.val =
    a.toAdd.val * (c * conjugation F K c)
  rw [Algebra.smul_def, norm_formula hdeg, mul_comm]

/-- The image subgroup depends only on the actual isotropic line. -/
theorem lineTransvections_smul (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0) (c : K) (hc : c ≠ 0)
    (hcv : hermitian F K (c • v) (c • v) = 0) :
    lineTransvections hdeg (c • v) hcv = lineTransvections hdeg v hv := by
  apply le_antisymm (lineTransvections_smul_le hdeg v hv c hcv)
  have he : c⁻¹ • (c • v) = v := by simp [smul_smul, hc]
  have h := lineTransvections_smul_le hdeg (c • v) hcv c⁻¹ (by rw [he]; exact hv)
  simpa only [he] using h

/-- Conjugation by any matrix preserving the isotropic line preserves its
abelian transvection group. This is the normality input for the line stabilizer. -/
theorem conjugate_mem_lineTransvections (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0)
    (g : SU F K n hdeg) (c : K) (hg : g.val *ᵥ v = c • v)
    (x : SU F K n hdeg) (hx : x ∈ lineTransvections hdeg v hv) :
    g * x * g⁻¹ ∈ lineTransvections hdeg v hv := by
  obtain ⟨a, rfl⟩ := hx
  change g * transvection hdeg v a.toAdd.val hv
    ((trace_zero_iff hdeg _).mp a.toAdd.prop) * g⁻¹ ∈ _
  rw [transvection_conjugate]
  have hiso := su_image_isotropic hdeg g v hv
  rw [hg] at hiso
  have he : transvection hdeg (g.val *ᵥ v) a.toAdd.val
      (su_image_isotropic hdeg g v hv) ((trace_zero_iff hdeg _).mp a.toAdd.prop) =
      lineTransvectionHom hdeg (c • v) hiso a := by
    apply Subtype.ext
    change transvectionMatrix (F := F) (g.val *ᵥ v) a.toAdd.val =
      transvectionMatrix (F := F) (c • v) a.toAdd.val
    rw [hg]
  rw [he]
  apply lineTransvections_smul_le hdeg v hv c hiso
  exact ⟨a, rfl⟩

/-- The entire actual line stabilizer normalizes its transvection subgroup. -/
theorem line_preserver_mem_normalizer (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (hv : hermitian F K v v = 0)
    (g : SU F K n hdeg) (c : K) (hc : c ≠ 0) (hg : g.val *ᵥ v = c • v) :
    g ∈ Subgroup.normalizer (lineTransvections hdeg v hv : Set (SU F K n hdeg)) := by
  have hi : (g⁻¹).val *ᵥ v = c⁻¹ • v := by
    have he := congrArg (fun w : Fin n → K => (g⁻¹).val *ᵥ w) hg
    have hm : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
    rw [mulVec_mulVec, hm, one_mulVec, mulVec_smul] at he
    simpa [smul_smul, hc] using congrArg (fun w : Fin n → K => c⁻¹ • w) he.symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conjugate_mem_lineTransvections hdeg v hv g c hg x
  · intro hx
    have h := conjugate_mem_lineTransvections hdeg v hv g⁻¹ c⁻¹ hi
      (g * x * g⁻¹) hx
    simpa [mul_assoc] using h

end Atlas.Unitary


