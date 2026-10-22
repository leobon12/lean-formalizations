import HigherDimLQGMetric.LfppTight.UnitCrossDirect
import HigherDimLQGMetric.LfppTight.CrossLaw
import HigherDimLQGMetric.LfppTight.ScaleCenter

/-! A8 for a normalized LGF from the DGZ adapter, at every centre and scale. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_cross_normalized_direct (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {p C : ℝ} (hp : p < 1) (hC : 0 < C) :
    ∃ R ε₀ : ℝ, 1 < R ∧ 0 < ε₀ ∧
      ∀ r : ℝ, 0 < r → ∀ x : Rd d, ∀ ε ∈ Ioo (0 : ℝ) (ε₀ * r),
        ENNReal.ofReal p ≤ P {ω |
          supPairs (lfppDist κ ξ ε (h ω)) (ball x r) ≤
            ENNReal.ofReal C⁻¹ * infPairs (lfppDist κ ξ ε (h ω))
              (sphere x r) (sphere x (R * r))} := by
  obtain ⟨b, εs, hb, hb4, hεs, hεhalf, hU⟩ :=
    l6a_unitCross_normalized_direct hL1e hDGZ hAdapter P h hh hp hC
  let R : ℝ := b⁻¹
  have hR0 : 0 < R := inv_pos.mpr hb
  have hR : 1 < R := by
    exact (one_lt_inv_iff₀).2 ⟨hb, by linarith⟩
  let ε₀ : ℝ := R * εs
  have hε₀ : 0 < ε₀ := mul_pos hR0 hεs
  refine ⟨R, ε₀, hR, hε₀, ?_⟩
  intro r hr x ε hε
  let ρ : ℝ := R * r
  have hρ : 0 < ρ := mul_pos hR0 hr
  let η : ℝ := ε / ρ
  have hη0 : 0 < η := div_pos hε.1 hρ
  have hηs : η < εs := by
    apply (div_lt_iff₀ hρ).2
    simpa only [ρ, ε₀, mul_assoc, mul_comm, mul_left_comm] using hε.2
  have hη1 : η < 1 := (hηs.trans_le hεhalf).trans (by norm_num)
  have hη : η ∈ Ioo (0 : ℝ) 1 := ⟨hη0, hη1⟩
  let k : Ω → DistRd d := fun ω => affineComp ρ x (h ω)
  have hk : IsWholeSpaceLGF k P := hh.1.affineComp hρ x
  have hconv : ∀ᵐ ω ∂P, k ω ∈ convSet d :=
    hk.ae_exists_tendsto_sphereAvgSeq hDGZ.dim one_pos 0
  let g : Ω → DistRd d := fun ω =>
    addConst (k ω) (-sphereAvg (k ω) 1 0)
  have hg : IsNormalizedLGF g P :=
    hk.isNormalizedLGF_normalize (by have := hDGZ.dim; omega) hconv
  have hlaw : P.map g = P.map h :=
    l6a_map_normalizedAffine_center_eq hDGZ.dim P h hh hρ x
  let U : Set Ω := {ω | supPairs
      (toCMapRd ((aEps κ ξ η)⁻¹ • lfppDist κ ξ η (g ω)))
      (ball (0 : Rd d) b) ≤
      ENNReal.ofReal C⁻¹ * infPairs
        (toCMapRd ((aEps κ ξ η)⁻¹ • lfppDist κ ξ η (g ω)))
        (sphere 0 b) (sphere 0 1)}
  have hUP : ENNReal.ofReal p ≤ P U := by
    rw [l6a_cross_normalized_law_eq hDGZ.dim κ hDGZ.kernel ξ hη0
      P h g hh hg hlaw b C⁻¹]
    have hc := l10a_ae_continuous_convMollify hDGZ.dim κ hDGZ.kernel P h hh hη0
    have hevent : P {ω |
        supPairs (toCMapRd ((aEps κ ξ η)⁻¹ • lfppDist κ ξ η (h ω)))
          (ball (0 : Rd d) b) ≤
          ENNReal.ofReal C⁻¹ * infPairs
            (toCMapRd ((aEps κ ξ η)⁻¹ • lfppDist κ ξ η (h ω)))
            (sphere 0 b) (sphere 0 1)} =
        P {ω | supPairs (lfppDist κ ξ η (h ω)) (ball 0 b) ≤
          ENNReal.ofReal C⁻¹ * infPairs (lfppDist κ ξ η (h ω))
            (sphere 0 b) (sphere 0 1)} := by
      apply measure_congr
      filter_upwards [hc] with ω hfield
      exact propext (l6a_cross_norm_iff_raw hDGZ.dim κ hDGZ.kernel ξ hη0
        (h ω) hfield b C⁻¹)
    rw [hevent]
    exact hU η ⟨hη0, hηs⟩
  have hscale := l6a_ae_lfppDist_scale_center hDGZ.dim κ hDGZ.kernel ξ P h hh hρ x
  have hcont := l10a_ae_continuous_convMollify hDGZ.dim κ hDGZ.kernel P g hg hη0
  have hρb : ρ * b = r := by
    dsimp [ρ, R]
    field_simp [hb.ne']
  have hsub : ∀ᵐ ω ∂P, ω ∈ U →
      supPairs (lfppDist κ ξ ε (h ω)) (ball x r) ≤
        ENNReal.ofReal C⁻¹ * infPairs (lfppDist κ ξ ε (h ω))
          (sphere x r) (sphere x (R * r)) := by
    filter_upwards [hscale, hcont] with ω hs hc hgood
    have hraw := (l6a_cross_norm_iff_raw hDGZ.dim κ hDGZ.kernel ξ hη0
      (g ω) hc b C⁻¹).1 hgood
    let a : ℝ := ρ * Real.exp (ξ * sphereAvg (h ω) ρ x)
    have ha : 0 < a := mul_pos hρ (Real.exp_pos _)
    have hD (u v : Rd d) :
        lfppDist κ ξ ε (h ω) (ρ • u + x, ρ • v + x) =
          a * lfppDist κ ξ η (g ω) (u, v) := by
      simpa only [a, η, add_comm] using hs ε hε.1 u v
    have hdet := l6a_cross_affine_of_field_eq
      (lfppDist κ ξ ε (h ω)) (lfppDist κ ξ η (g ω))
      (fun z => ρ • z + x) (ball 0 b) (sphere 0 b) (sphere 0 1)
      ha hD hraw
    rw [l6a_image_ball_affine hρ x b,
      image_sphere_affine hρ x b,
      image_sphere_affine hρ x 1] at hdet
    simpa only [hρb, mul_one, ρ] using hdet
  exact hUP.trans (measure_mono_ae hsub)

end HigherDimLQGMetric
