import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedLFPPPointUpper
import SupercriticalLQGUniqueness.B2.PfeAxioms.TightLiminfFinite
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteLimit
import LQGMetric.Papers.DFGPS.L2_8GffSq

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_internal_lt_top_of_section4_buffered
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioo (0 : ℝ) 1)
    (D : DistC → LSCMetric)
    (hD : SubseqLimit ξ m
      (fun n => ⟨(ε n : ℝ), (ε n).property.1⟩) D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (V : TopologicalSpace.Opens ℂ) (hVc : IsConnected (V : Set ℂ))
    {K U : Set ℂ} (hVK : (V : Set ℂ) ⊆ K) (hK : IsCompact K) (hKU : K ⊆ U)
    (x y : V) (hxy : (x : ℂ) ≠ (y : ℂ)) :
    ∀ᵐ ω ∂P,
      (D (h ω)).internal U
        (⟨(x : ℂ), hKU (hVK x.property)⟩,
          ⟨(y : ℂ), hKU (hVK y.property)⟩) < ∞ := by
  let e : ℕ → Ioi (0 : ℝ) := fun n => ⟨(ε n : ℝ), (ε n).property.1⟩
  let Y (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ENNReal.ofReal ((m (e n) : ℝ)⁻¹) *
      crossLenIn (ξ : ℝ) (X (e n) ω) V {(x : ℂ)} {(y : ℂ)}
  have hSec := hS ξ Q hQ m hm
  have hT : IsTwoSidedTight P Y := by
    have ht := hSec.1 P h hh X hX V hVc (x : ℂ) (y : ℂ)
      x.property y.property hxy
    refine ⟨fun n => ht.1 (ε n), ?_⟩
    intro δ hδ
    obtain ⟨M, hM, htail⟩ := ht.2 δ hδ
    exact ⟨M, hM, fun n => htail (ε n)⟩
  have hFin := ae_liminf_lt_top_of_twoSidedTight P Y hT
  have hConv := ae_normalizedLFPPMetric_tendsto ξ m e D hD P h hh X hX
  filter_upwards [hConv, hFin] with ω hC hF
  have hB := buffered_internal_le_liminf_lfppDOn (ξ : ℝ)
    (fun n => m (e n)) (fun n => X (e n) ω) (D (h ω)) hC hVK hK hKU x y
  have hEq : (fun n => ENNReal.ofReal ((m (e n) : ℝ)⁻¹) *
        lfppDOn (ξ : ℝ) (X (e n) ω) V x y) = fun n => Y n ω := by
    funext n
    simp only [Y, LQGMetric.DFGPS.crossLenIn_singleton]
  rw [hEq] at hB
  exact lt_of_le_of_lt hB hF

end SupercriticalLQGUniqueness.B2.PfeAxioms
