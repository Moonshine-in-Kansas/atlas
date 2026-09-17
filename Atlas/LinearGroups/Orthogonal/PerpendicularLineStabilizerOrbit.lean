import Atlas.LinearGroups.Orthogonal.PerpendicularStabilizerOrbit

noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem elementary_perpendicular_stabilizer_line_transport
    (Q : QuadraticForm F V) (e f : V) (he : Q e=0) (hf : Q f=0) (hef : Q.polarBilin e f=1)
    (hC : (complementForm Q e f).polarBilin.Nondegenerate)
    (htrans : ∀u v : complement Q e f,u≠0 → v≠0 →
      (complementForm Q e f) u=0 → (complementForm Q e f) v=0 →
      ∃g : isometrySubgroup (complementForm Q e f),g∈elementarySubgroup (complementForm Q e f) ∧
        ∃c : F,c≠0 ∧ g.val u=c • v)
    (x y : V) (hx : Q x=0) (hy : Q y=0)
    (hex : Q.polarBilin e x=0) (hey : Q.polarBilin e y=0)
    (hxl : x∉Submodule.span F {e}) (hyl : y∉Submodule.span F {e}) :
    ∃g : isometrySubgroup Q,g∈elementarySubgroup Q ∧ g.val e=e ∧
      ∃c : F,c≠0 ∧ g.val x=c • y := by
  obtain ⟨a,w,hw,hqw,hax⟩ := perpendicular_singular_decomposition Q e f he hf hef x hx hex hxl
  obtain ⟨b,v,hv,hqv,hby⟩ := perpendicular_singular_decomposition Q e f he hf hef y hy hey hyl
  obtain ⟨k,hk,c,hc,hkw⟩ := htrans w v hw hv hqw hqv
  let t := complementLift Q e f he hf hef k
  have hte : t.val e=e := complementLift_fix_e Q e f he hf hef k
  have htw : t.val w.val=(c • v).val :=
    (complementLift_apply Q e f he hf hef k w).trans (congrArg Subtype.val hkw)
  obtain ⟨r,hr,hrx⟩ := root_transport_perpendicular_coordinate Q e f he hC (c • v)
    (smul_ne_zero hc hv) a (c*b)
  refine ⟨r*t,(elementarySubgroup Q).mul_mem (rootSubgroup_le_elementary Q e he hr)
    (complementLift_mem_elementary Q e f he hf hef k hk),?_,c,hc,?_⟩
  · change r.val (t.val e)=e
    rw [hte,rootSubgroup_fixes_direction Q e he r hr]
  · change r.val (t.val x)=c • y
    rw [←hax,map_add,map_smul,hte,htw,hrx,←hby]
    simp only [Submodule.coe_smul,smul_add,smul_smul]

theorem elementary_singular_line_transport_of_isometry {W : Type*} [AddCommGroup W] [Module F W]
    (Q : QuadraticForm F V) (R : QuadraticForm F W) (i : Q.IsometryEquiv R)
    (htrans : ∀u v : W,u≠0 → v≠0 → R u=0 → R v=0 →
      ∃g : isometrySubgroup R,g∈elementarySubgroup R ∧ ∃c : F,c≠0 ∧ g.val u=c • v)
    (u v : V) (hu : u≠0) (hv : v≠0) (hqu : Q u=0) (hqv : Q v=0) :
    ∃g : isometrySubgroup Q,g∈elementarySubgroup Q ∧ ∃c : F,c≠0 ∧ g.val u=c • v := by
  let T := semilinearElementaryEquiv (RingEquiv.refl F) i.toLinearEquiv Q R i.map_app
  obtain ⟨k,hk,c,hc,hku⟩ := htrans (i u) (i v)
    (fun h => hu (i.injective (h.trans (map_zero i).symm)))
    (fun h => hv (i.injective (h.trans (map_zero i).symm)))
    ((i.map_app u).trans hqu) ((i.map_app v).trans hqv)
  let g := T.symm ⟨k,hk⟩
  refine ⟨g.val,g.prop,c,hc,?_⟩
  apply i.injective
  have h := T.apply_symm_apply ⟨k,hk⟩
  have ha := congrArg (fun s : elementarySubgroup R => s.val.val (i u)) h
  change i (g.val.val (i.symm (i u)))=k.val (i u) at ha
  rw [i.symm_apply_apply,hku] at ha
  simpa using ha

end Atlas.Orthogonal
