import Atlas.Algebra.Albert.CrossProduct
import Atlas.Algebra.Albert.RankOne

namespace Atlas.Albert
variable {F : Type*} [Field F]

theorem norm_eq_zero_of_adjoint_eq_zero (x : Carrier F) (hx : adjoint x=0) : norm x=0 := by
  by_cases hz : x=0
  · subst x; simp [norm,SplitOctonion.norm,SplitOctonion.trace,SplitOctonion.mul]
  have h := adjoint_adjoint x
  rw [hx] at h
  have ha : adjoint (0 : Carrier F)=0 := by
    apply Prod.ext
    · funext i; fin_cases i <;> simp [adjoint,SplitOctonion.norm]
    · funext i j; fin_cases i <;> fin_cases j <;> simp [adjoint,SplitOctonion.mul,
        SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit]
  rw [ha] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hz

theorem quadraticTrace_eq_zero_of_adjoint_eq_zero (x : Carrier F) (hx : adjoint x=0) :
    quadraticTrace x=0 := by
  rw [←trace_adjoint,hx]
  simp [trace]

end Atlas.Albert
