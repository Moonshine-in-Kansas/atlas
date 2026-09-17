import Atlas.Lattices.GolayInteger

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def evenCoordinateSum : AddSubgroup IntegerCoordinates where
  carrier := {z | (∑ i, z i) % 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (∑ i, (x i + y i)) % 2 = 0
    rw [Finset.sum_add_distrib, Int.add_emod]
    change ((∑ i, x i) % 2 + (∑ i, y i) % 2) % 2 = 0
    rw [hx,hy]
    rfl
  neg_mem' := by
    intro x hx
    change (∑ i, -x i) % 2 = 0
    rw [Finset.sum_neg_distrib]
    change (∑ i, x i) % 2 = 0 at hx
    omega

theorem evenHalfLattice_gluing (y : IntegerCoordinates) :
    y ∈ evenHalfLattice ↔ ∃ c : golay, ∃ z : evenCoordinateSum,
      ∀ i, y i = golayIntegerLift c.val i + 2 * z.val i := by
  constructor
  · intro hy
    let c : golay := ⟨integerReduction y,hy.1⟩
    have hp (i : Omega) : 2 ∣ y i - golayIntegerLift c.val i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
      have h := congrFun (integerReduction_lift c.val) i
      change ((golayIntegerLift c.val i : ℤ) : Bit) = (y i : Bit) at h
      change ((y i - golayIntegerLift c.val i : ℤ) : Bit) = 0
      simp [h]
    let z : IntegerCoordinates := fun i => (y i - golayIntegerLift c.val i) / 2
    have he (i : Omega) : y i = golayIntegerLift c.val i + 2 * z i := by
      have h := Int.mul_ediv_cancel' (hp i)
      dsimp [z]
      omega
    have hs : (∑ i, y i) = (hammingNorm c.val : ℤ) + 2 * ∑ i, z i := by
      simp_rw [he]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_golayIntegerLift]
    have hz : z ∈ evenCoordinateSum := by
      change (∑ i, z i) % 2 = 0
      obtain ⟨k,hk⟩ := golay_doublyEven c.val c.prop
      have hw : (hammingNorm c.val : ℤ) = 4 * (k : ℤ) := by exact_mod_cast hk
      have hys := hy.2
      rw [hs,hw] at hys
      omega
    exact ⟨c,⟨z,hz⟩,he⟩
  · rintro ⟨c,z,he⟩
    constructor
    · have hc : integerReduction y = c.val := by
        ext i
        have h := congrFun (integerReduction_lift c.val) i
        change ((y i : ℤ) : Bit) = c.val i
        rw [he i]
        simpa [integerReduction] using h
      rw [hc]
      exact c.prop
    · change (∑ i, y i) % 4 = 0
      simp_rw [he]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_golayIntegerLift]
      obtain ⟨k,hk⟩ := golay_doublyEven c.val c.prop
      have hw : (hammingNorm c.val : ℤ) = 4 * (k : ℤ) := by exact_mod_cast hk
      have hz := z.prop
      change (∑ i, z.val i) % 2 = 0 at hz
      rw [hw]
      omega

theorem evenGolayLattice_gluing (x : IntegerCoordinates) :
    x ∈ evenGolayLattice ↔ ∃ c : golay, ∃ z : evenCoordinateSum,
      ∀ i, x i = 2 * golayIntegerLift c.val i + 4 * z.val i := by
  rw [mem_evenGolayLattice]
  constructor
  · rintro ⟨y,hc,hs,he⟩
    obtain ⟨c,z,hz⟩ := (evenHalfLattice_gluing y).mp ⟨hc,hs⟩
    exact ⟨c,z,fun i => by rw [he i,hz i]; ring⟩
  · rintro ⟨c,z,he⟩
    let y : IntegerCoordinates := fun i => golayIntegerLift c.val i + 2 * z.val i
    have hy := (evenHalfLattice_gluing y).mpr ⟨c,z,fun _ => rfl⟩
    exact ⟨y,hy.1,hy.2,fun i => by rw [he i]; dsimp [y]; ring⟩

end Atlas.Lattices
