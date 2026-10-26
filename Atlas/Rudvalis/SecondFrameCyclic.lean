import Atlas.Rudvalis.SecondFrameProjection
import Atlas.Rudvalis.SeedIntegralTransport

namespace Atlas.Rudvalis

def secondFramePreviousRow (r : Fin 7) : Fin 7 := ⟨(r.val+6)%7,Nat.mod_lt _ (by decide)⟩

theorem integerMonomial_P_seed (t : SeedOrbitIndex) :
    integerMonomial codeP.val (seedOrbitWord t)=seedOrbitWord (seedNextRow t.1,t.2) := by
  change liftedCoordinateHom (seedConjugateMonomial seedPMonomial)
    (signedSeedTransport (seedOrbitOriginal t))=signedSeedTransport (seedOrbitOriginal _)
  rw [signedSeedTransport_eq_linear,signedSeedTransport_eq_linear,
    seedConjugate_lifted_transport,seedP_lifted,seedOrbitOriginal_P]

theorem secondFrameInteger_P (z : SeedCoordinate) :
    integerMonomial codeP.val (secondFrameInteger z)=secondFrameInteger (secondFramePreviousRow z.1,z.2) := by
  change liftedCoordinateHom codeP.val (secondFrameSign z.2 • seedOrbitWord (secondFrameOrbitIndex z))=_
  rw [map_smul]
  change secondFrameSign z.2 • integerMonomial codeP.val (seedOrbitWord (secondFrameOrbitIndex z))=_
  rw [integerMonomial_P_seed]
  have he : (seedNextRow (secondFrameOrbitIndex z).1,(secondFrameOrbitIndex z).2)=
      secondFrameOrbitIndex (secondFramePreviousRow z.1,z.2) := by
    change (seedNextRow (secondFrameRow z.1),_)=(secondFrameRow (secondFramePreviousRow z.1),_)
    congr 1
    have h : ∀r : Fin 7,seedNextRow (secondFrameRow r)=secondFrameRow (secondFramePreviousRow r) := by decide +kernel
    exact h z.1
  rw [he]
  rfl

theorem secondFrame_P (z : SeedCoordinate) :
    rationalMonomialHom codeP.val (secondFrame z)=secondFrame (secondFramePreviousRow z.1,z.2) := by
  rw [secondFrame,rationalMonomial_half,secondFrameInteger_P]
  rfl

def secondFrameCyclicPerm : Equiv.Perm SeedCoordinate where
  toFun z := (secondFramePreviousRow z.1,z.2)
  invFun z := (seedNextRow z.1,z.2)
  left_inv z := by
    have h : ∀r : Fin 7,seedNextRow (secondFramePreviousRow r)=r := by decide +kernel
    exact Prod.ext (h z.1) rfl
  right_inv z := by
    have h : ∀r : Fin 7,secondFramePreviousRow (seedNextRow r)=r := by decide +kernel
    exact Prod.ext (h z.1) rfl

theorem secondFrame_P_power (n : ℕ) (z : SeedCoordinate) :
    rationalMonomialHom (codeP^n).val (secondFrame z)=secondFrame ((secondFrameCyclicPerm^n) z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',Subgroup.coe_mul,map_mul]
    change rationalMonomialHom codeP.val (rationalMonomialHom (codeP^n).val (secondFrame z))=_
    rw [ih,secondFrame_P,pow_succ']
    rfl

theorem secondFrameProjection_cyclic (n : ℕ) (s : Finset SeedCoordinate) (v : RationalSpace) :
    rationalMonomialHom (codeP^n).val (secondFrameProjection s v)=
      secondFrameProjection (s.map (secondFrameCyclicPerm^n).toEmbedding)
        (rationalMonomialHom (codeP^n).val v) := by
  classical
  have h : (rationalMonomialHom (codeP^n).val).toLinearMap.comp (secondFrameProjection s)=
      (secondFrameProjection (s.map (secondFrameCyclicPerm^n).toEmbedding)).comp
        (rationalMonomialHom (codeP^n).val).toLinearMap := by
    apply secondFrameBasis.ext
    intro i
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,secondFrameProjection_basis]
    have ha := secondFrame_P_power n i
    rw [←secondFrameBasis_apply,←secondFrameBasis_apply] at ha
    rw [ha,secondFrameProjection_basis]
    by_cases hi : i∈s <;> simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply,hi,ite_true,ite_false,map_zero]
    exact ha
  exact congrArg (fun f : RationalSpace →ₗ[ℚ] RationalSpace => f v) h

theorem secondFrameReflection_cyclic (n : ℕ) (s : Finset SeedCoordinate) (v : RationalSpace) :
    rationalMonomialHom (codeP^n).val (secondFrameReflection s v)=
      secondFrameReflection (s.map (secondFrameCyclicPerm^n).toEmbedding)
        (rationalMonomialHom (codeP^n).val v) := by
  change rationalMonomialHom (codeP^n).val ((2 : ℚ) • secondFrameProjection s v-v)=
    (2 : ℚ) • secondFrameProjection (s.map (secondFrameCyclicPerm^n).toEmbedding)
      (rationalMonomialHom (codeP^n).val v)-rationalMonomialHom (codeP^n).val v
  rw [map_sub,map_smul,secondFrameProjection_cyclic]

end Atlas.Rudvalis


