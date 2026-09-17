import Atlas.LinearGroups.Orthogonal.CoordinateCrossTransport
import Atlas.LinearGroups.Orthogonal.RootPartnerAction

noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- The root subgroup at u sends its chosen partner onto every singular line not perpendicular to u. -/
theorem root_line_transport_of_pairing (Q : QuadraticForm F V) (u f : V)
    (hu : Q u=0) (hf : Q f=0) (huf : Q.polarBilin u f=1)
    (x : V) (hx : Q x=0) (hux : Q.polarBilin u x ≠ 0) :
    ∃g : rootSubgroup Q u hu, ∃c : F, c ≠ 0 ∧ g.val.val f=c • x := by
  let c := (Q.polarBilin u x)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hux
  have hy : Q (c • x)=0 := by rw [QuadraticMap.map_smul,hx,smul_zero]
  have huy : Q.polarBilin u (c • x)=1 := by
    rw [map_smul,smul_eq_mul]
    exact inv_mul_cancel₀ hux
  obtain ⟨g,hg,_⟩ := root_unique_partner_transport Q u f hu hf huf (c • x) hy huy
  exact ⟨g,c,hc,hg⟩

/-- Membership is retained in an actual ambient subgroup containing the coordinate root subgroup. -/
theorem subgroup_line_transport_of_pairing (Q : QuadraticForm F V) (H : Subgroup (isometrySubgroup Q))
    (u f : V) (hu : Q u=0) (hf : Q f=0) (huf : Q.polarBilin u f=1)
    (hr : rootSubgroup Q u hu ≤ H) (x : V) (hx : Q x=0) (hux : Q.polarBilin u x ≠ 0) :
    ∃g : isometrySubgroup Q, g ∈ H ∧ ∃c : F, c ≠ 0 ∧ g.val f=c • x := by
  obtain ⟨g,c,hc,hg⟩ := root_line_transport_of_pairing Q u f hu hf huf x hx hux
  exact ⟨g.val,hr g.prop,c,hc,hg⟩

end Atlas.Orthogonal

namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]

private def lineReachable (Q : QuadraticForm F V) (H : Subgroup (isometrySubgroup Q)) (e x : V) : Prop :=
  ∃g : isometrySubgroup Q, g ∈ H ∧ ∃c : F, c ≠ 0 ∧ g.val e=c • x

private theorem lineReachable_comp (Q : QuadraticForm F V) (H : Subgroup (isometrySubgroup Q))
    (e x y : V) (hx : lineReachable Q H e x) (g : isometrySubgroup Q) (hg : g∈H)
    (c : F) (hc : c≠0) (hy : g.val x=c • y) : lineReachable Q H e y := by
  obtain ⟨k,hk,d,hd,hke⟩ := hx
  refine ⟨g*k,H.mul_mem hg hk,d*c,mul_ne_zero hd hc,?_⟩
  change g.val (k.val e)=(d*c) • y
  rw [hke,map_smul,hy,smul_smul]

/-- Coordinate root subgroups act transitively on all singular lines detected by a hyperbolic frame. -/
theorem coordinate_frame_line_transport [Nontrivial ι]
    (Q : QuadraticForm F V) (H : Subgroup (isometrySubgroup Q)) (a b : ι → V) (i₀ : ι)
    (ha : ∀i,Q (a i)=0) (hb : ∀i,Q (b i)=0) (hab : ∀i,Q.polarBilin (a i) (b i)=1)
    (horth : ∀i j,i≠j → Q.polarBilin (a i) (a j)=0 ∧
      Q.polarBilin (a i) (b j)=0 ∧ Q.polarBilin (b i) (b j)=0)
    (hra : ∀i,rootSubgroup Q (a i) (ha i) ≤ H)
    (hrb : ∀i,rootSubgroup Q (b i) (hb i) ≤ H)
    (x : V) (hx : Q x=0) (hxp : ∃i,Q.polarBilin (a i) x≠0 ∨ Q.polarBilin (b i) x≠0) :
    ∃g : isometrySubgroup Q, g ∈ H ∧ ∃c : F, c≠0 ∧ g.val (a i₀)=c • x := by
  have hea (i : ι) : lineReachable Q H (a i₀) (a i) := by
    by_cases hi : i₀=i
    · subst i
      exact ⟨1,H.one_mem,1,one_ne_zero,by simp⟩
    · have hh := horth i₀ i hi
      have hba : Q.polarBilin (b i₀) (a i)=0 := by
        rw [polar_swap]; exact (horth i i₀ (Ne.symm hi)).2.1
      obtain ⟨g,hg,he⟩ := two_root_cross_transport Q H (a i₀) (b i₀) (a i) (b i)
        (ha i₀) (hb i₀) (ha i) (hb i) (hab i₀) (hab i) hh.1 hh.2.1 hba (hrb i₀) (hrb i)
      exact ⟨g,hg,-1,neg_ne_zero.mpr one_ne_zero,by simpa using he⟩
  have heb (i : ι) : lineReachable Q H (a i₀) (b i) := by
    obtain ⟨j,hji⟩ := exists_ne i
    have hh := horth j i hji
    have hba : Q.polarBilin (b i) (a i)=1 := by rw [polar_swap]; exact hab i
    obtain ⟨g,hg,he⟩ := two_root_cross_transport Q H (a j) (b j) (b i) (a i)
      (ha j) (hb j) (hb i) (ha i) (hab j) hba hh.2.1 hh.1 hh.2.2 (hrb j) (hra i)
    exact lineReachable_comp Q H (a i₀) (a j) (b i) (hea j) g hg (-1)
      (neg_ne_zero.mpr one_ne_zero) (by simpa using he)
  obtain ⟨i,hi|hi⟩ := hxp
  · obtain ⟨g,hg,c,hc,he⟩ := subgroup_line_transport_of_pairing Q H (a i) (b i)
      (ha i) (hb i) (hab i) (hra i) x hx hi
    exact lineReachable_comp Q H (a i₀) (b i) x (heb i) g hg c hc he
  · have hba : Q.polarBilin (b i) (a i)=1 := by rw [polar_swap]; exact hab i
    obtain ⟨g,hg,c,hc,he⟩ := subgroup_line_transport_of_pairing Q H (b i) (a i)
      (hb i) (ha i) hba (hrb i) x hx hi
    exact lineReachable_comp Q H (a i₀) (a i) x (hea i) g hg c hc he

end Atlas.Orthogonal
