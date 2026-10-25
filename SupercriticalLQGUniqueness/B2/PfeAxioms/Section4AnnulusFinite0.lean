import SupercriticalLQGUniqueness.B2.PfeAxioms.Section4AcrossFixed
import SupercriticalLQGUniqueness.B2.PfeAxioms.Section4AroundFinite
import SupercriticalLQGUniqueness.B2.PfeAxioms.GeometrySubsequence

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_annulus_costs_pos_finite_of_section4
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (A : EuclideanAnnulus) :
    ∀ᵐ ω ∂P, 0 < acrossDist (D (h ω)) A ∧
      acrossDist (D (h ω)) A < ∞ ∧
      0 < aroundDist (D (h ω)) A ∧
      aroundDist (D (h ω)) A < ∞ := by
  have hsmall : ∀ᶠ n in atTop, (ε n : ℝ) < 1 :=
    hε.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  let e : ℕ → Ioo (0 : ℝ) 1 := fun n =>
    ⟨(ε (n + N) : ℝ), ⟨(ε (n + N)).property, hN (n + N) (by omega)⟩⟩
  have htail : SubseqLimit ξ m
      (fun n => ⟨(e n : ℝ), (e n).property.1⟩) D := by
    change SubseqLimit ξ m (fun n => ε (n + N)) D
    exact subseqLimit_comp_strictMono ξ m ε D hD (fun n => n + N)
      (strictMono_nat_of_lt_succ (fun n => by omega))
  have ha := ae_acrossDist_lt_top_of_section4 hS ξ Q hQ m hm e D htail
    P h hh X hX A
  have hb := ae_aroundDist_lt_top_of_section4 hS ξ Q hQ m hm e D htail
    P h hh X hX A
  filter_upwards [ha, hb] with ω haω hbω
  exact ⟨B2.Strong.acrossDist_pos _ A, haω,
    B2.Strong.aroundDist_pos _ A, hbω⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
