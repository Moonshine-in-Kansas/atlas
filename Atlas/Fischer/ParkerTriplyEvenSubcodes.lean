import Atlas.Fischer.ParkerElementarySubcodes

namespace Atlas.Fischer
open Atlas.Codes

/-- Polarizing the actual quarter-weight invariant proves the other two
obstructions vanish on any triply even subcode. -/
def ParkerElementarySubcode.ofQuarterWeightZero (K : Submodule Bit golay)
    (hw : ∀ a : K, golayQuarterWeight a.val = 0) : ParkerElementarySubcode := by
  have hc (a b : K) : golayHalfOverlap a.val b.val = 0 := by
    have h := golayQuarterWeight_add a.val b.val
    rw [hw a,hw b,show golayQuarterWeight (a.val+b.val)=0 from hw (a+b)] at h
    simpa only [zero_add] using h.symm
  refine ⟨K,hw,hc,?_⟩
  intro a b c
  have h := golayHalfOverlap_add_left a.val b.val c.val
  rw [hc a c,hc b c,show golayHalfOverlap (a.val+b.val) c.val=0 from hc (a+b) c] at h
  simpa only [zero_add] using h.symm

/-- The source's weight condition already implies the overlap and triple
conditions by polarization. No affine model is assumed in this generic fact. -/
def ParkerElementarySubcode.ofWeightDivisibility (K : Submodule Bit golay)
    (hw : ∀ a : K, 8 ∣ hammingNorm a.val.val) : ParkerElementarySubcode :=
  .ofQuarterWeightZero K (fun a => by
    obtain ⟨k,hk⟩ := hw a
    change ((hammingNorm a.val.val / 4 : ℕ) : Bit)=0
    have he : hammingNorm a.val.val / 4 = 2*k := by omega
    rw [he,Nat.cast_mul]
    simp)

end Atlas.Fischer
