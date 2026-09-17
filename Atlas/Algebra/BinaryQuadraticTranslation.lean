import Atlas.Algebra.BinaryQuadraticWordRank

noncomputable section
namespace Atlas.Algebra
open Atlas.Codes

/-- Full polar rank makes the actual polar linear map injective. -/
theorem binaryQuadraticWordForm_polar_injective (w : binaryQuadraticCode)
    (hr : binaryWalshPolarRank (binaryQuadraticWordForm w)=4) :
    Function.Injective (binaryQuadraticWordForm w).polarBilin := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have h := (binaryQuadraticWordForm w).polarBilin.finrank_range_add_finrank_ker
  have hd : Module.finrank Bit BinaryFour=4 := by simp [BinaryFour]
  change binaryWalshPolarRank (binaryQuadraticWordForm w) +
    Module.finrank Bit (binaryQuadraticWordForm w).polarBilin.ker = _ at h
  rw [hr,hd] at h
  omega

/-- The sixteen literal translates of a full-rank four-variable quadratic word
are distinct; no arbitrary labels or Hadamard matrix are supplied. -/
theorem binaryQuadraticWord_translation_injective (w : binaryQuadraticCode)
    (hr : binaryWalshPolarRank (binaryQuadraticWordForm w)=4) :
    Function.Injective (fun t : BinaryFour => fun v : BinaryFour => w.val (v+t)) := by
  intro s t h
  have hz : w.val s=w.val t := by simpa only [zero_add] using congrFun h 0
  apply binaryQuadraticWordForm_polar_injective w hr
  apply LinearMap.ext
  intro v
  have hv := congrFun h v
  change w.val (v+s)=w.val (v+t) at hv
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    binaryQuadraticWordForm_apply]
  rw [add_comm s v,add_comm t v,hv,hz]

end Atlas.Algebra
