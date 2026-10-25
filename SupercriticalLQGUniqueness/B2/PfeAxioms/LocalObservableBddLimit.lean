import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionBdd
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLiminfLocalized
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLowerLocalized

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_normalizedLFPPMetric_tendsto_bdd
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusBddCont h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n =>
        PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n))
          (X (ε n) ω)) atTop (𝓝 (D (h ω))) := by
  filter_upwards [(hD P h hh X hX).1] with ω hω
  rw [LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff]
  apply LSCFun.tendsto_of_lscTendsto
  convert hω using 1
  funext n
  funext p
  exact PfeWeyl.normalizedLFPPMetric_toLSCFun
    (ξ : ℝ) (m (ε n)) (X (ε n) ω) p

 

theorem ae_internal_eq_countable_localized_bdd_of_geometry
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusBddCont h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hGeom : ∀ᵐ ω ∂P,
      ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    {U : Set ℂ} (H : CompactExhaustion U) (x y : U)
    (W V : ℕ → Set ℂ)
    (hgeo : ∀ n,
      IsOpen (W n) ∧ IsCompact (closure (W n)) ∧
      closure (W n) ⊆ U ∧
      (H n).image Subtype.val ⊆ W n ∧
      (x : ℂ) ∈ W n ∧ (y : ℂ) ∈ W n ∧
      IsOpen (V n) ∧ IsCompact (closure (V n)) ∧
      closure (V n) ⊆ U ∧ closure (W n) ⊆ V n ∧
      IsCompact (frontier (V n)) ∧
      (frontier (V n)).Nonempty ∧
      Disjoint (closure (W n)) (frontier (V n)))
    (hsmall : ∀ᵐ ω ∂P, ∀ n,
      PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω))
        (D (h ω)) (closure (W n)) (V n)) :
    ∀ᵐ ω ∂P,
      (D (h ω)).internal U (x, y) =
        ⨅ n : ℕ, lowerLocalizedNeighborhoodObservable ξ
          ε (fun k => m (ε k))
          ⟨(x : ℂ),
            (hgeo n).2.2.2.2.2.2.2.2.2.1
              (subset_closure (hgeo n).2.2.2.2.1)⟩
          ⟨(y : ℂ),
            (hgeo n).2.2.2.2.2.2.2.2.2.1
              (subset_closure (hgeo n).2.2.2.2.2.1)⟩
          (h ω) := by
  have hConv := ae_normalizedLFPPMetric_tendsto_bdd ξ m ε D hD P h hh X hX
  have hXeq : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ z : ℂ,
      X (ε n) ω z = heatMollify (ε n : ℝ) (h ω) z :=
    ae_all_iff.mpr fun n => ae_heatVersion_eq_heatMollify_bdd hh (ε n)
      (X (ε n)) (hX (ε n))
  have hLoc : ∀ᵐ ω ∂P, ∀ n, ∀ x y : V n,
      lowerNeighborhoodObservable
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω)) (V n) x y =
      lowerLocalizedNeighborhoodObservable ξ
        ε (fun k => m (ε k)) x y (h ω) := by
    apply ae_all_iff.mpr
    intro n
    have hVb : Bornology.IsBounded (V n) :=
      (hgeo n).2.2.2.2.2.2.2.1.isBounded.subset subset_closure
    exact (ae_lowerNeighborhoodObservable_localized_eq_heat
      hh ξ (hgeo n).2.2.2.2.2.2.1 hVb
      ε hε (fun k => m (ε k)) (fun k => X (ε k)) hXeq).mono
        fun ω hω x y => (hω x y).symm
  filter_upwards [hGeom, hConv, hsmall, hLoc] with ω hGω hCω hSω hLω
  have hfinite := normalizedLFPPMetric_finite_geometry
    (ξ : ℝ) (fun k => m (ε k)) (fun k => X (ε k) ω)
  have hforget : Continuous (PfeWeyl.euclidForget (D (h ω))) :=
    B2.PfeLocal.continuous_euclidForget_of_small_metric (D (h ω)) hGω
  rw [internal_eq_iInf_lowerNeighborhoodObservable_of_smallAnnulusCosts
    hCω hfinite.1 hfinite.2.1 hfinite.2.2 hforget
    H x y W V hgeo hSω]
  apply iInf_congr
  intro n
  exact hLω n _ _

end SupercriticalLQGUniqueness.B2.PfeAxioms
