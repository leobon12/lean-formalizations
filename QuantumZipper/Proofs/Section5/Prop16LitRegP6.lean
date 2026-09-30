import QuantumZipper.Proofs.Section5.Prop16LitRegP5
import QuantumZipper.Proofs.LQG.CoordChangeAreaOffset

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: chart-regular free samples, almost surely (D98)

`Prop16Lit.ae_chartY`: for the free-boundary GFF `X` and a deterministic conformal `ψ : ℍ → ℍ`,
a.s. `ChartY γ ψ (X ω) ν_ω` with `ν_ω = pullMu μ_{X ω} ψ`: regular sample, regular pushed
averages, convergent RC3 uniformly on compacts, continuous pushed averages at all small radii
(the finite-parameter primed core with radius factors, `ae_pushed_regular_alpha`), offset-uniform
area limit (`ae_hasAreaLimit_coordChange_free`, DS11 Prop. 2.1). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open CoordChangeArea GoodSample SWCore G1Side

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem ae_chartY [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψi : InjOn ψ H) (hψH : MapsTo ψ H H) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) :
    ∀ᵐ ω ∂P, ChartY γ ψ (X ω) (pullMu (qAreaMeasure γ (X ω)) ψ) := by
  have h : ∀ n : ℕ, ∃ k₀ : ℕ, ∀ᵐ ω ∂P, ∀ k ≥ k₀,
      TendstoUniformlyOn (fun j (p : ℂ × ℝ) =>
          ∫ u, avgReg (X ω) j u ∂((foldedCircle p.1 (p.2 * radius k)).map ψ))
        (fun p => evalReg (X ω) ((foldedCircle p.1 (p.2 * radius k)).map ψ)) atTop
        (recR (n + 1) ×ˢ Icc 1 2) ∧
      ContinuousOn (fun p : ℂ × ℝ => evalReg (X ω) ((foldedCircle p.1 (p.2 * radius k)).map ψ))
        (recR (n + 1) ×ˢ Icc 1 2) := by
    intro n
    have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    obtain ⟨ρ, M, m, hρ, hm, hcl⟩ := exists_areaClass hψd hψi hψH hψ0
      (a := -((n + 1 : ℕ) : ℝ)) (b := ((n + 1 : ℕ) : ℝ)) (d := ((n + 1 : ℕ) : ℝ))
      (c := 1 / (((n + 1 : ℕ) : ℝ) + 1)) (by positivity)
    have hy : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact ae_pushed_regular_alpha hX (by linarith) (by positivity) hy hρ hm hcl
  choose k₀ hk₀ using h
  have hall := ae_all_iff.2 hk₀
  filter_upwards [hall, RegSample.ae_isRegularSample hX, ae_pushRegular hX hψd hψi hψH hψ0,
    ae_hasAreaLimit_coordChange_free hX hγ hγ2 hψm hψd hψi hψH hψ0] with ω hω hreg hpush hlim
  obtain ⟨F, hF⟩ := hreg
  -- a compact of `ℍ` sits well inside some `R_{n+1}`
  have hbox : ∀ K, IsCompact K → K ⊆ H → ∃ n : ℕ, ∃ δ > 0,
      cthickening δ K ⊆ interior (recR (n + 1)) := by
    intro K hK hKH
    obtain ⟨n, hn⟩ := exists_recR hK hKH
    obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open isOpen_interior
      (hn.trans (interior_mono (recR_subset_succ n)))
    exact ⟨n, δ, hδ, hδK⟩
  refine ⟨⟨F, hF⟩, hpush, fun K hK hKH => ?_, fun K hK hKH => ?_, hlim⟩
  · obtain ⟨n, δ, hδ, hδK⟩ := hbox K hK hKH
    refine ⟨min (δ / 2) (radius (k₀ n)), lt_min (by linarith) (radius_pos _),
      fun w hw ρ hρ hρ₀ => ?_⟩
    obtain ⟨k, hk, α, hα, hρk⟩ := exists_offset hρ (lt_of_lt_of_le hρ₀ (min_le_right _ _))
    have hball : closedBall w (ρ + δ / 4) ⊆ recR (n + 1) := by
      refine (closedBall_subset_cthickening hw _).trans ((cthickening_mono ?_ K).trans
        (hδK.trans interior_subset))
      linarith [min_le_left (δ / 2) (radius (k₀ n))]
    exact tendsto_coordChange_fc hF hψm hψd hψ0 hψH (recR_subset_H (n + 1))
      (fun k' hk' => (hω n k' hk').1) (fun k' hk' => (hω n k' hk').2) (Qc γ) hρ (by linarith)
      hball hk hα hρk
  · obtain ⟨n, δ, hδ, hδK⟩ := hbox K hK hKH
    refine ⟨radius (k₀ n), radius_pos _, fun ρ hρ hρ₀ => ?_⟩
    obtain ⟨k, hk, α, hα, rfl⟩ := exists_offset hρ hρ₀
    have hKR : K ⊆ recR (n + 1) :=
      (self_subset_cthickening K).trans (hδK.trans interior_subset)
    have hc := (hω n k hk).2.comp (continuousOn_id.prodMk (continuousOn_const (c := α)))
      (fun w hw => ⟨hKR hw, hα⟩)
    exact hc.congr fun w _ => rfl

end Prop16Lit
end QuantumZipper
