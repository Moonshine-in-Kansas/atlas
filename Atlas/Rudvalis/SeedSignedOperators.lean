import Atlas.Rudvalis.SeedCoordinates

/-! The original-coordinate signed operators of Version 33 and the 112 seed translates. -/
namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def signedCoordinateOperator {R : Type*} [CommRing R]
    (e : Equiv.Perm SeedCoordinate) (s : SeedCoordinate → Bool) :
    (SeedCoordinate → R) ≃ₗ[R] (SeedCoordinate → R) where
  toFun v z := if s z then -v (e z) else v (e z)
  invFun v z := if s (e.symm z) then -v (e.symm z) else v (e.symm z)
  left_inv v := by funext z; simp; split <;> simp_all
  right_inv v := by funext z; simp; split <;> simp_all
  map_add' v w := by funext z; split <;> simp_all [add_comm]
  map_smul' a v := by funext z; split <;> simp_all

theorem signedCoordinateOperator_norm_sq {R : Type*} [CommRing R]
    (e : Equiv.Perm SeedCoordinate) (s : SeedCoordinate → Bool) (v : SeedCoordinate → R) :
    (∑ z, signedCoordinateOperator e s v z ^ 2)=∑ z, v z ^ 2 := by
  have he (z : SeedCoordinate) : signedCoordinateOperator e s v z ^2=v (e z)^2 := by
    change (if s z then -v (e z) else v (e z))^2=_
    split <;> simp
  simp_rw [he]
  exact Equiv.sum_comp e (fun z => v z^2)

def seedIIndex (k : Fin 8) : Fin 8 := ![1,0,3,2,5,4,7,6] k
def seedRhoIndex (k : Fin 8) : Fin 8 := ![2,3,0,1,6,7,4,5] k
def seedSigmaIndex (k : Fin 8) : Fin 8 := ![4,5,6,7,0,1,2,3] k

def seedIIndexEquiv : Equiv.Perm (Fin 8) :=
  ⟨seedIIndex,seedIIndex,by decide +kernel,by decide +kernel⟩
def seedRhoIndexEquiv : Equiv.Perm (Fin 8) :=
  ⟨seedRhoIndex,seedRhoIndex,by decide +kernel,by decide +kernel⟩
def seedSigmaIndexEquiv : Equiv.Perm (Fin 8) :=
  ⟨seedSigmaIndex,seedSigmaIndex,by decide +kernel,by decide +kernel⟩

def seedRowCycle : Equiv.Perm (Fin 7) :=
  ⟨(fun r => ![6,0,1,2,3,4,5] r),(fun r => ![1,2,3,4,5,6,0] r),
    by decide +kernel,by decide +kernel⟩

noncomputable def seedIOperator {R : Type*} [CommRing R] :
    (SeedCoordinate → R) ≃ₗ[R] (SeedCoordinate → R) :=
  signedCoordinateOperator (Equiv.prodCongr (Equiv.refl _) seedIIndexEquiv)
    (fun z => ![true,false,true,false,true,false,true,false] z.2)

noncomputable def seedRhoOperator {R : Type*} [CommRing R] :
    (SeedCoordinate → R) ≃ₗ[R] (SeedCoordinate → R) :=
  signedCoordinateOperator (Equiv.prodCongr (Equiv.refl _) seedRhoIndexEquiv)
    (fun z => ![true,true,false,false,false,false,true,true] z.2)

noncomputable def seedSigmaOperator {R : Type*} [CommRing R] :
    (SeedCoordinate → R) ≃ₗ[R] (SeedCoordinate → R) :=
  signedCoordinateOperator (Equiv.prodCongr (Equiv.refl _) seedSigmaIndexEquiv)
    (fun z => ![true,true,true,true,false,false,false,false] z.2)

noncomputable def seedPOperator {R : Type*} [CommRing R] :
    (SeedCoordinate → R) ≃ₗ[R] (SeedCoordinate → R) :=
  signedCoordinateOperator (Equiv.prodCongr seedRowCycle (Equiv.refl _)) (fun _ => false)

variable {R : Type*} [CommRing R]

theorem seedI_square (v : SeedCoordinate → R) : seedIOperator (seedIOperator v) = -v := by
  funext z
  rcases z with ⟨r,k⟩
  fin_cases k <;> simp [seedIOperator,signedCoordinateOperator,seedIIndexEquiv,seedIIndex]

theorem seedRho_square (v : SeedCoordinate → R) : seedRhoOperator (seedRhoOperator v) = -v := by
  funext z
  rcases z with ⟨r,k⟩
  fin_cases k <;> simp [seedRhoOperator,signedCoordinateOperator,seedRhoIndexEquiv,seedRhoIndex]

theorem seedSigma_square (v : SeedCoordinate → R) : seedSigmaOperator (seedSigmaOperator v) = -v := by
  funext z
  rcases z with ⟨r,k⟩
  fin_cases k <;> simp [seedSigmaOperator,signedCoordinateOperator,seedSigmaIndexEquiv,seedSigmaIndex]

theorem seedI_rho_comm (v : SeedCoordinate → R) :
    seedIOperator (seedRhoOperator v)=seedRhoOperator (seedIOperator v) := by
  funext z
  rcases z with ⟨r,k⟩
  fin_cases k <;> simp [seedIOperator,seedRhoOperator,signedCoordinateOperator,
    seedIIndexEquiv,seedRhoIndexEquiv,seedIIndex,seedRhoIndex]

theorem seedI_sigma_comm (v : SeedCoordinate → R) :
    seedIOperator (seedSigmaOperator v)=seedSigmaOperator (seedIOperator v) := by
  funext z
  rcases z with ⟨r,k⟩
  fin_cases k <;> simp [seedIOperator,seedSigmaOperator,signedCoordinateOperator,
    seedIIndexEquiv,seedSigmaIndexEquiv,seedIIndex,seedSigmaIndex]

theorem seedRho_sigma_anticomm (v : SeedCoordinate → R) :
    seedRhoOperator (seedSigmaOperator v)= -seedSigmaOperator (seedRhoOperator v) := by
  funext z
  rcases z with ⟨r,k⟩
  fin_cases k <;> simp [seedRhoOperator,seedSigmaOperator,signedCoordinateOperator,
    seedRhoIndexEquiv,seedSigmaIndexEquiv,seedRhoIndex,seedSigmaIndex]


theorem seedP_I_comm (v : SeedCoordinate → R) :
    seedPOperator (seedIOperator v)=seedIOperator (seedPOperator v) := rfl

theorem seedP_rho_comm (v : SeedCoordinate → R) :
    seedPOperator (seedRhoOperator v)=seedRhoOperator (seedPOperator v) := rfl

theorem seedP_sigma_comm (v : SeedCoordinate → R) :
    seedPOperator (seedSigmaOperator v)=seedSigmaOperator (seedPOperator v) := rfl

theorem seedP_seventh (v : SeedCoordinate → R) : (seedPOperator^7) v=v := by
  funext z
  rcases z with ⟨r,k⟩
  fin_cases r <;> rfl

theorem seedI_norm_sq (v : SeedCoordinate → R) : (∑ z, seedIOperator v z ^2)=∑ z,v z^2 :=
  signedCoordinateOperator_norm_sq _ _ v

theorem seedRho_norm_sq (v : SeedCoordinate → R) : (∑ z, seedRhoOperator v z ^2)=∑ z,v z^2 :=
  signedCoordinateOperator_norm_sq _ _ v

theorem seedSigma_norm_sq (v : SeedCoordinate → R) : (∑ z, seedSigmaOperator v z ^2)=∑ z,v z^2 :=
  signedCoordinateOperator_norm_sq _ _ v

theorem seedP_norm_sq (v : SeedCoordinate → R) : (∑ z, seedPOperator v z ^2)=∑ z,v z^2 :=
  signedCoordinateOperator_norm_sq _ _ v

noncomputable def seedJOperator (s : Fin 4) : (SeedCoordinate → R) ≃ₗ[R] (SeedCoordinate → R) :=
  ![1,seedRhoOperator,seedSigmaOperator,seedSigmaOperator*seedRhoOperator] s

theorem seedJ_norm_sq (s : Fin 4) (v : SeedCoordinate → R) :
    (∑ z, seedJOperator s v z ^2)=∑ z,v z^2 := by
  fin_cases s
  · rfl
  · exact seedRho_norm_sq v
  · exact seedSigma_norm_sq v
  · change (∑ z, seedSigmaOperator (seedRhoOperator v) z ^2)=_
    rw [seedSigma_norm_sq,seedRho_norm_sq]

theorem operator_pow_norm_sq (L : (SeedCoordinate → R) ≃ₗ[R] (SeedCoordinate → R))
    (hL : ∀ v, (∑ z, L v z ^2)=∑ z,v z^2) (n : ℕ) (v : SeedCoordinate → R) :
    (∑ z, (L^n) v z ^2)=∑ z,v z^2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change (∑ z,L ((L^n) v) z ^2)=_
    rw [hL,ih]

abbrev SeedOrbitIndex := Fin 7 × Fin 2 × Fin 4 × Fin 2

noncomputable def seedOrbitOriginal (z : SeedOrbitIndex) : SeedCoordinate → ℤ :=
  (seedPOperator^z.1.val) ((seedIOperator^z.2.1.val)
    (seedJOperator z.2.2.1 (if z.2.2.2=0 then seedAArray else seedBArray)))

noncomputable def seedOrbitWord (z : SeedOrbitIndex) : Coordinate → ℤ :=
  signedSeedTransport (seedOrbitOriginal z)

theorem seedOrbitIndex_card : Fintype.card SeedOrbitIndex=112 := by decide

def signedPositionIndexEquiv : Equiv.Perm (Fin 8) :=
  ⟨signedPositionIndex,signedPositionIndex,by decide +kernel,by decide +kernel⟩

theorem signedSeedTransport_norm_sq (v : SeedCoordinate → ℤ) :
    (∑ z : Coordinate, signedSeedTransport v z ^2)=∑ z,v z^2 := by
  rw [← Equiv.sum_comp seedCoordinateEquiv]
  have he (z : SeedCoordinate) : signedSeedTransport v (seedCoordinateEquiv z)^2 =
      v (z.1,signedPositionIndex z.2)^2 := by
    rw [show z=(z.1,z.2) from rfl,signedSeedTransport_apply]
    simp [signedPositionSign]
  simp_rw [he]
  exact Equiv.sum_comp (Equiv.prodCongr (Equiv.refl _) signedPositionIndexEquiv) (fun z=>v z^2)

theorem seedOrbitOriginal_norm_sq (z : SeedOrbitIndex) :
    (∑ q,seedOrbitOriginal z q ^2)=16 := by
  unfold seedOrbitOriginal
  rw [operator_pow_norm_sq _ seedP_norm_sq,operator_pow_norm_sq _ seedI_norm_sq,seedJ_norm_sq]
  split_ifs
  · have h := seedA_norm_sq
    change (∑ q,signedSeedTransport seedAArray q^2)=16 at h
    rwa [signedSeedTransport_norm_sq] at h
  · have h := seedB_norm_sq
    change (∑ q,signedSeedTransport seedBArray q^2)=16 at h
    rwa [signedSeedTransport_norm_sq] at h

theorem seedOrbitWord_norm_sq (z : SeedOrbitIndex) : (∑ q,seedOrbitWord z q ^2)=16 := by
  rw [seedOrbitWord,signedSeedTransport_norm_sq,seedOrbitOriginal_norm_sq]

end Atlas.Rudvalis

