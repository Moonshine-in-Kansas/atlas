import Atlas.Rudvalis.GaussianLatticeFinite

namespace Atlas.Rudvalis

theorem codeGaussianHom_shell (g : codeGroup) (v : MinimalShell) :
    codeGaussianHom g • v=g • v := rfl

theorem gaussianGroup_commute_units (f : gaussianLatticeGroup) (u : GaussianUnits) :
    f*codeGaussianHom u.val=codeGaussianHom u.val*f := by
  have hc : Commute f (codeGaussianHom codeI) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact f.prop.2.2 v
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp u.prop
  rw [←hn,map_zpow]
  exact hc.zpow_right n

theorem gaussian_units_shell_commute (f : gaussianLatticeGroup) (u : GaussianUnits) (v : MinimalShell) :
    u • (f • v)=f • (u • v) := by
  change u.val • (f • v)=f • (u.val • v)
  rw [←codeGaussianHom_shell,←codeGaussianHom_shell,←mul_smul,←mul_smul,
    gaussianGroup_commute_units]

noncomputable instance : MulAction gaussianLatticeGroup MinimalCross where
  smul f := Quotient.map (fun v : MinimalShell => f • v) (by
    intro v w h
    obtain ⟨u,hu⟩ := MulAction.mem_orbit_iff.mp h
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨u,by rw [gaussian_units_shell_commute,hu]⟩)
  one_smul v := Quotient.inductionOn v (fun w => congrArg (Quotient.mk _) (one_smul gaussianLatticeGroup w))
  mul_smul f g v := Quotient.inductionOn v (fun w => congrArg (Quotient.mk _) (mul_smul f g w))

theorem gaussian_minimalCross_smul (f : gaussianLatticeGroup) (v : MinimalShell) :
    minimalCross (f • v)=f • minimalCross v := rfl

theorem codeGaussianHom_cross (g : codeGroup) (v : MinimalCross) :
    codeGaussianHom g • v=g • v := by
  induction v using Quotient.inductionOn
  rfl

end Atlas.Rudvalis
