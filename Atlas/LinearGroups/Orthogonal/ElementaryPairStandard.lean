import Atlas.LinearGroups.Orthogonal.ElementaryPairTransport
import Atlas.LinearGroups.Orthogonal.WittTwoStandard
import Atlas.LinearGroups.Orthogonal.SpinorStandard

/-! # Elementary transitivity on actual B/D hyperbolic pairs and singular vectors -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F : Type*} [Field F]

theorem complementB_represents (n : ℕ) (e f : VectorB (n+2) F)
    (he : formB (n+2) F e = 0) (hf : formB (n+2) F f = 0)
    (hef : (formB (n+2) F).polarBilin e f = 1) (c : F) :
    ∃ a : complement (formB (n+2) F) e f, formB (n+2) F a.val = c := by
  obtain ⟨g⟩ := complement_isometryB e f he hf hef
  obtain ⟨a, ha⟩ := formB_represents n c
  exact ⟨g.symm a, (g.symm.map_app a).trans ha⟩

theorem complementD_represents (n : ℕ) (e f : VectorD (n+2) F)
    (he : formD (n+2) F e = 0) (hf : formD (n+2) F f = 0)
    (hef : (formD (n+2) F).polarBilin e f = 1) (c : F) :
    ∃ a : complement (formD (n+2) F) e f, formD (n+2) F a.val = c := by
  obtain ⟨g⟩ := complement_isometryD e f he hf hef
  obtain ⟨a, ha⟩ := formD_represents n c
  exact ⟨g.symm a, (g.symm.map_app a).trans ha⟩

theorem elementaryB_pair_transport (n : ℕ) (h2 : (2 : F) ≠ 0)
    (e f u v : VectorB (n+2) F)
    (he : formB (n+2) F e = 0) (hf : formB (n+2) F f = 0)
    (hu : formB (n+2) F u = 0) (hv : formB (n+2) F v = 0)
    (hef : (formB (n+2) F).polarBilin e f = 1)
    (huv : (formB (n+2) F).polarBilin u v = 1) :
    ∃ g : isometrySubgroup (formB (n+2) F), g ∈ elementarySubgroup (formB (n+2) F) ∧
      g.val e = u ∧ g.val f = v :=
  elementary_transport_hyperbolic_pair _ (wittTwoFrameB n) (polarB_nondegenerate h2) h2
    radicalB_eq_bot e f u v he hf hu hv hef huv (fun c _ => complementB_represents n e f he hf hef c)

theorem elementaryD_pair_transport (n : ℕ) (h2 : (2 : F) ≠ 0)
    (e f u v : VectorD (n+2) F)
    (he : formD (n+2) F e = 0) (hf : formD (n+2) F f = 0)
    (hu : formD (n+2) F u = 0) (hv : formD (n+2) F v = 0)
    (hef : (formD (n+2) F).polarBilin e f = 1)
    (huv : (formD (n+2) F).polarBilin u v = 1) :
    ∃ g : isometrySubgroup (formD (n+2) F), g ∈ elementarySubgroup (formD (n+2) F) ∧
      g.val e = u ∧ g.val f = v :=
  elementary_transport_hyperbolic_pair _ (wittTwoFrameD n) polarD_nondegenerate h2
    radicalD_eq_bot e f u v he hf hu hv hef huv (fun c _ => complementD_represents n e f he hf hef c)

theorem elementaryB_singular_transport (n : ℕ) (h2 : (2 : F) ≠ 0)
    (u v : VectorB (n+2) F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : formB (n+2) F u = 0) (hqv : formB (n+2) F v = 0) :
    ∃ g : isometrySubgroup (formB (n+2) F), g ∈ elementarySubgroup (formB (n+2) F) ∧ g.val u = v := by
  obtain ⟨f, hf, huf⟩ := exists_hyperbolic_partnerB u hu hqu
  obtain ⟨w, hw, hvw⟩ := exists_hyperbolic_partnerB v hv hqv
  obtain ⟨g, hg, hgu, _⟩ := elementaryB_pair_transport n h2 u f v w hqu hf hqv hw huf hvw
  exact ⟨g, hg, hgu⟩

theorem elementaryD_singular_transport (n : ℕ) (h2 : (2 : F) ≠ 0)
    (u v : VectorD (n+2) F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : formD (n+2) F u = 0) (hqv : formD (n+2) F v = 0) :
    ∃ g : isometrySubgroup (formD (n+2) F), g ∈ elementarySubgroup (formD (n+2) F) ∧ g.val u = v := by
  obtain ⟨f, hf, huf⟩ := exists_hyperbolic_partnerD u hu hqu
  obtain ⟨w, hw, hvw⟩ := exists_hyperbolic_partnerD v hv hqv
  obtain ⟨g, hg, hgu, _⟩ := elementaryD_pair_transport n h2 u f v w hqu hf hqv hw huf hvw
  exact ⟨g, hg, hgu⟩
end Atlas.Orthogonal
