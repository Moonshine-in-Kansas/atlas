import Atlas.Rudvalis.LatticeMonomial
import Atlas.Rudvalis.LatticeShellLifts
import Atlas.Rudvalis.CodeRowExact
import Atlas.GroupTheory.FreeOrbitCount

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

instance : MulAction codeGroup MinimalShell where
  smul g v := ⟨⟨rationalMonomialHom g.val v.val.val,codeGroup_lattice_preserves g _ v.val.prop⟩,
    (rationalMonomial_pairing g.val _ _).trans v.prop⟩
  one_smul v := by apply Subtype.ext; apply Subtype.ext; change rationalMonomialHom 1 v.val.val=v.val.val; simp
  mul_smul g h v := by
    apply Subtype.ext; apply Subtype.ext
    change rationalMonomialHom (g.val*h.val) v.val.val=_
    rw [map_mul]; rfl

noncomputable abbrev GaussianUnits := Subgroup.zpowers codeI
noncomputable abbrev MinimalCross := Quotient (MulAction.orbitRel GaussianUnits MinimalShell)

noncomputable def minimalCross (v : MinimalShell) : MinimalCross := Quotient.mk _ v

theorem gaussianUnits_card : Nat.card GaussianUnits=4 := by
  rw [Nat.card_zpowers,codeI_order]

theorem minimalShell_nonzero (v : MinimalShell) : v.val.val≠0 := by
  intro h
  have hn := v.prop
  rw [h] at hn
  norm_num [rationalDot] at hn

private theorem codeI_square_no_fixed (v : MinimalShell) : (codeI^2) • v≠v := by
  intro h
  have hh := congrArg (fun w : MinimalShell => w.val.val) h
  change rationalMonomialHom (codeI.val^2) v.val.val=v.val.val at hh
  rw [map_pow,pow_two] at hh
  change rationalI (rationalI v.val.val)=v.val.val at hh
  rw [rationalI_square] at hh
  apply minimalShell_nonzero v
  funext i
  have hi := congrFun hh i
  change -v.val.val i=v.val.val i at hi
  change v.val.val i=0
  linarith

theorem gaussianUnits_free (g : GaussianUnits) (v : MinimalShell) (h : g • v=v) : g=1 := by
  classical
  have hg := (mem_zpowers_iff_mem_range_orderOf).mp g.prop
  rw [codeI_order] at hg
  obtain ⟨n,hn,hg⟩ := Finset.mem_image.mp hg
  have hn4 : n<4 := Finset.mem_range.mp hn
  have hv : (codeI^n) • v=v := by
    rw [hg]
    exact h
  apply Subtype.ext
  change g.val=1
  rw [←hg]
  interval_cases n
  · exact pow_zero _
  · exfalso
    apply codeI_square_no_fixed v
    simp only [pow_one] at hv
    rw [pow_two,mul_smul,hv,hv]
  · exact False.elim (codeI_square_no_fixed v hv)
  · exfalso
    apply codeI_square_no_fixed v
    have he : (codeI^3)^2=codeI^2 := by
      rw [←pow_mul,show 3*2=4+2 from rfl,pow_add,codeI_pow_four,one_mul]
    rw [←he,pow_two,mul_smul,hv,hv]

theorem minimalCross_card_mul_four [Finite MinimalShell] :
    Nat.card MinimalShell=Nat.card MinimalCross*4 := by
  simpa only [gaussianUnits_card] using Atlas.free_action_card GaussianUnits MinimalShell gaussianUnits_free

theorem codeGroup_commute_gaussianUnits (g : codeGroup) (u : GaussianUnits) : g*u.val=u.val*g := by
  obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp u.prop
  rw [←hk]
  exact (show Commute g codeI from codeGroup_commute_I g).zpow_right k

noncomputable instance : MulAction codeGroup MinimalCross where
  smul g := Quotient.map (fun v : MinimalShell => g • v) (by
    intro v w hvw
    obtain ⟨u,hu⟩ := MulAction.mem_orbit_iff.mp hvw
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨u,?_⟩
    change u.val • (g • w)=g • v
    rw [←mul_smul,←codeGroup_commute_gaussianUnits, mul_smul]
    exact congrArg (fun x : MinimalShell => g • x) hu)
  one_smul v := Quotient.inductionOn v (fun w => congrArg (Quotient.mk _) (one_smul codeGroup w))
  mul_smul g h v := Quotient.inductionOn v (fun w => congrArg (Quotient.mk _) (mul_smul g h w))

theorem minimalCross_smul (g : codeGroup) (v : MinimalShell) :
    minimalCross (g • v)=g • minimalCross v := rfl

theorem minimalCross_eq_iff (v w : MinimalShell) :
    minimalCross v=minimalCross w ↔ ∃u : GaussianUnits,u • w=v := by
  exact Quotient.eq.trans MulAction.mem_orbit_iff

end Atlas.Rudvalis

