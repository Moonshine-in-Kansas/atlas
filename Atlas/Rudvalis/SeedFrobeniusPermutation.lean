import Atlas.Rudvalis.SeedOperatorProducts

/-! The literal unsigned permutation underlying (Tv)_(2r)=psi(v_r). -/
namespace Atlas.Rudvalis

def seedTIndex (k : Fin 8) : Fin 8 := ![0,1,6,7,2,3,4,5] k

def seedTIndexEquiv : Equiv.Perm (Fin 8) :=
  ⟨seedTIndex,(fun k => ![0,1,4,5,6,7,2,3] k),by decide +kernel,by decide +kernel⟩

def seedTRowEquiv : Equiv.Perm (Fin 7) :=
  ⟨(fun r => ![0,4,1,5,2,6,3] r),(fun r => ![0,2,4,6,1,3,5] r),
    by decide +kernel,by decide +kernel⟩

def seedTCoord : Equiv.Perm SeedCoordinate := Equiv.prodCongr seedTRowEquiv seedTIndexEquiv

theorem seedTCoord_row_doubling (r : Fin 7) (k : Fin 8) :
    seedTCoord (⟨(2*r.val)%7,Nat.mod_lt _ (by decide)⟩,k)=(r,seedTIndex k) := by
  decide +kernel +revert

theorem seedTCoord_cube : seedTCoord^3=1 := by
  apply Equiv.ext
  decide +kernel

end Atlas.Rudvalis
