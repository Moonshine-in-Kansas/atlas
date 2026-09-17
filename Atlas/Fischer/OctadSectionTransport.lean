import Atlas.Fischer.OctadShortenedTransport

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

/-- Recover the section coordinates from an actual normalized multiplicative
lift with the prescribed projection. -/
def ParkerSection.ofLift {K : ParkerElementarySubcode} (f : K.code → ParkerLoop)
    (hz : f 0 = (0,0)) (hc : ∀ a, (f a).1=a.val)
    (hm : ∀ a b, f (a+b)=parkerLoopMultiply (f a) (f b)) : ParkerSection K where
  sign a := (f a).2
  zero := congrArg Prod.snd hz
  correction a b := by
    have h := congrArg Prod.snd (hm a b)
    change (f (a+b)).2 = (f a).2+(f b).2+parkerGolayFactorSet (f a).1 (f b).1 at h
    rw [hc a,hc b] at h
    rw [h]
    calc
      _ = parkerGolayFactorSet a.val b.val+
        (((f a).2+(f b).2)+((f a).2+(f b).2)) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

 theorem ParkerSection.ofLift_lift {K : ParkerElementarySubcode} (f : K.code → ParkerLoop)
    (hz : f 0 = (0,0)) (hc : ∀ a, (f a).1=a.val)
    (hm : ∀ a b, f (a+b)=parkerLoopMultiply (f a) (f b)) (a : K.code) :
    (ParkerSection.ofLift f hz hc hm).lift a=f a := Prod.ext (hc a).symm rfl

/-- Transport an actual Parker section by the actual loop automorphism. -/
noncomputable def octadSectionTransport (e : ParkerStandardGroup) (O : Octad)
    (q : OctadParkerSection O) : OctadParkerSection (parkerOctadAction e O) :=
  ParkerSection.ofLift (fun a => e.val (q.lift ((octadShortenedTransport e O).symm a)))
    (by rw [map_zero,q.lift_zero]; exact e.property.2.1 0)
    (by
      intro a
      rw [parkerStandardProjection_spec]
      change parkerCodeEquiv (parkerStandardProjection e)
        ((octadShortenedTransport e O).symm a).val = a.val
      exact congrArg Subtype.val ((octadShortenedTransport e O).apply_symm_apply a))
    (by
      intro a b
      rw [map_add,q.lift_multiply,e.property.1])

theorem octadSectionTransport_lift (e : ParkerStandardGroup) (O : Octad)
    (q : OctadParkerSection O) (a : octadShortenedCode (parkerOctadAction e O)) :
    (octadSectionTransport e O q).lift a =
      e.val (q.lift ((octadShortenedTransport e O).symm a)) :=
  ParkerSection.ofLift_lift (K := octadElementarySubcode (parkerOctadAction e O)) _ _ _ _ a

theorem octadSectionTransport_lift_image (e : ParkerStandardGroup) (O : Octad)
    (q : OctadParkerSection O) (a : octadShortenedCode O) :
    (octadSectionTransport e O q).lift (octadShortenedTransport e O a) = e.val (q.lift a) := by
  rw [octadSectionTransport_lift,LinearEquiv.symm_apply_apply]

theorem octadSectionTransport_translate (e : ParkerStandardGroup) (O : Octad)
    (q : OctadParkerSection O) (χ : Module.Dual Bit (octadShortenedCode O)) :
    octadSectionTransport e O (q.translate χ) =
      (octadSectionTransport e O q).translate ((octadCharacterPullback e O).symm χ) := by
  apply ParkerSection.ext
  funext a
  have h : (octadSectionTransport e O (q.translate χ)).lift a =
      ((octadSectionTransport e O q).translate
        ((octadCharacterPullback e O).symm χ)).lift a := by
    rw [octadSectionTransport_lift,ParkerSection.translate_lift,
      parkerStandard_preserves_sign,ParkerSection.translate_lift,octadSectionTransport_lift]
    rfl
  exact congrArg Prod.snd h

/-- The transported calibration has the necessary parity correction on the
actual octad lift: e(Ωo)=Ω((-1)^ε(e)e(o)). -/
theorem octadSectionTransport_calibration (e : ParkerStandardGroup) (O : Octad)
    (q : OctadParkerSection O) (o : ParkerLoop)
    (hq : q.lift (octadShortenedOne O)=parkerLoopMultiply parkerOmega o) :
    (octadSectionTransport e O q).lift (octadShortenedOne (parkerOctadAction e O)) =
      parkerLoopMultiply parkerOmega (parkerSign (e.val parkerOmega).2 (e.val o)) := by
  rw [← octadShortenedTransport_one e O,octadSectionTransport_lift_image,hq,e.property.1,
    parkerStandard_omega,parkerLoopMultiply_sign_left,parkerLoopMultiply_sign_right]
  simp [parkerSign,parkerOmega]

end Atlas.Fischer
