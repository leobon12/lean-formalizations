import QuantumZipper.Proofs.Thm18.G1SideScaleFree
import QuantumZipper.Proofs.Thm18.G1SideExact
import QuantumZipper.Proofs.Section5.Prop17RawRep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (8): deterministic continuum limit of the wedge field against a carried measure

For a good free sample `x` (witness `F`), a continuous radial path `A`, a regular wedge field
`w = wedgeField (lateralPart x) A Q`, and a probability measure `μ` carried by a compact
`Kc ⊆ ℍ̄` at distance `≥ c₀ > 0` from `0`: the pairings `σ ↦ ∫ evalReg w (fc(v,σ)) dμ(v)` are
integrable for every `σ > 0`, and they converge as `σ → 0⁺` whenever the free pairings
`σ ↦ ∫ F(v,σ) dμ(v)` do (`wedge_continuum_of_free`). For `σ < c₀/2`,
`evalReg w (fc(v,σ)) = F(v,σ) + ∫ profCut d fc(v,σ)` (the wedge field is the free field plus the
profile away from `0`, Duplantier–Sheffield 2011 (5.1)), and the profile part converges by the
deterministic smoothing limit `tendsto_integral_smooth_aff`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

theorem wedge_continuum_of_free {x : FieldSample} {F : ℂ × ℝ → ℝ} (hgood : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    {A : ℝ → ℝ} (hA : Continuous A) (Q : ℝ)
    (hW : IsRegularSample (wedgeField (lateralPart x) A Q))
    {μ : Measure ℂ} [IsProbabilityMeasure μ] {Kc : Set ℂ} (hKc : IsCompact Kc)
    (hKH : Kc ⊆ Hbar) (hμK : ∀ᵐ v ∂μ, v ∈ Kc) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hsepK : ∀ v ∈ Kc, c₀ ≤ ‖v‖) {Y : ℝ}
    (hY : Tendsto (fun σ => ∫ v, F (v, σ) ∂μ) (𝓝[>] 0) (𝓝 Y)) :
    (∀ σ : ℝ, 0 < σ →
      Integrable (fun v => evalReg (wedgeField (lateralPart x) A Q) (foldedCircle v σ)) μ) ∧
    ∃ L : ℝ, Tendsto (fun σ => ∫ v, evalReg (wedgeField (lateralPart x) A Q)
      (foldedCircle v σ) ∂μ) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨Fw, hFw⟩ := hW
  set w := wedgeField (lateralPart x) A Q with hwdef
  have hslice : ∀ {Φ : ℂ × ℝ → ℝ}, ContinuousOn Φ (Hbar ×ˢ Ioi 0) → ∀ σ : ℝ, 0 < σ →
      Integrable (fun v => Φ (v, σ)) μ := fun {Φ} hΦ σ hσ =>
    integrable_of_continuousOn_carrier hKc hμK
      (hΦ.comp (continuousOn_id.prodMk continuousOn_const) fun v hv => ⟨hKH hv, hσ⟩)
  refine ⟨fun σ hσ => (hslice hFw.1 σ hσ).congr
    (hμK.mono fun v hv => (hFw.evalReg_fc_of_mem (hKH hv) hσ).symm), ?_⟩
  set g := profCut x A Q (c₀ / 2 / 2) with hgdef
  have hgc : Continuous g := continuous_profCut hgood hA Q (by positivity)
  have hreg' := GoodSample.gs_add_ofFun hgood.1 hgc.continuousOn
  have hkey : ∀ σ ∈ Ioo 0 (c₀ / 2), ∀ v ∈ Kc,
      evalReg w (foldedCircle v σ) = F (v, σ) + ∫ z, g z ∂foldedCircle v σ := by
    intro σ hσ v hv
    have e1 : evalReg w (foldedCircle v σ) = evalReg (x + ofFun g) (foldedCircle v σ) := by
      unfold evalReg
      refine limUnder_congr_side ?_
      have hj : ∀ᶠ j in atTop, radius j < c₀ / 2 / 4 :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num)).eventually (gt_mem_nhds (show (0 : ℝ) < c₀ / 2 / 4 by positivity)) |>.mono fun j hj => by
            simpa [radius, one_div, inv_pow] using hj
      filter_upwards [hj] with j hj
      refine integral_congr_ae ?_
      filter_upwards [WedgeCan.ae_fc_abs_le_norm (w := v) hσ.1,
        RegClosure.fc_ae_mem_Hbar v σ] with z hz1 hz2
      have hvz : c₀ / 2 ≤ ‖z‖ := by
        have := hsepK v hv
        have h2 := le_abs_self (‖v‖ - σ)
        linarith [hσ.2]
      exact avgReg_wedge_eq_profCut hgood hraw hA (by positivity) j z hz2 hvz hj
    rw [e1, hreg'.evalReg_fc_of_mem (hKH hv) hσ.1]
  have hsm := S5.FieldLaw.Raw.tendsto_integral_smooth_aff hgc hKc (fun u hu => hKH hu) hμK 0
    one_pos
  have haff : ∀ u, PairLim.aff 0 1 u = u := fun u => by
    simp [PairLim.aff]
  simp only [haff] at hsm
  refine ⟨Y + ∫ u, g u ∂μ, (hY.add hsm).congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < c₀ / 2 by positivity)] with σ hσ
  have hint2 : Integrable (fun v => ∫ z, g z ∂foldedCircle v σ) μ :=
    integrable_of_continuousOn_carrier hKc hμK
      (GoodSample.continuous_smoothFun hgc.continuousOn σ).continuousOn
  rw [← integral_add (hslice hgood.1.1 σ hσ.1) hint2]
  exact integral_congr_ae (hμK.mono fun v hv => (hkey σ hσ v hv).symm)

end G1Side
end QuantumZipper
