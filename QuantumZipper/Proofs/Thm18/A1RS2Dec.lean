import QuantumZipper.Proofs.Thm18.A1RS2Log

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (12): splitting `evalReg Z` into the free part and the wedge profile

For `Z` with the circle values of `X + α₀(−log|·|) + G` (`X` regular, `G` continuous) and a
Frostman probability measure `ν` carried by a bounded part of `ℍ̄`:

**`evalReg_Z_split`**: if the dyadic pairings of `X` against `ν` converge to `A`, then
`evalReg Z ν = A + α₀ ∫ −log‖w‖ dν + ∫ G dν`.

Together with `continuousOn_integral_log_smearFam` and `continuousOn_integral_smearFam` (the
profile is continuous along the smeared family, including `ρ = 0`), this reduces the rational
Cauchy estimate for `Z` to the one for `X`. Own bookkeeping (dominated convergence:
`CoordReg.tendsto_integral_log_max_frostman`, `FrostmanReg.tendsto_integral_smoothFun_frostman`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- **The regularized evaluation of the unscaled wedge field splits.** -/
theorem evalReg_Z_split {κ : ℝ} {X Z : FieldSample} {FX : ℂ × ℝ → ℝ} {G : ℂ → ℝ}
    (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    {ν : Measure ℂ} [IsProbabilityMeasure ν] {Rs α CF : ℝ}
    (hsupp : ν (closedBall (0 : ℂ) Rs ∩ Hbar)ᶜ = 0) (hF : IsFrostman ν α CF) (hα : 0 < α)
    {A : ℝ} (hA : Tendsto (fun k : ℕ => ∫ w, avgReg X k w ∂ν) atTop (𝓝 A)) :
    evalReg Z ν = A + (Real.sqrt κ - 2 / Real.sqrt κ) * (-∫ w, Real.log ‖w‖ ∂ν) +
      ∫ w, G w ∂ν := by
  set α₀ : ℝ := Real.sqrt κ - 2 / Real.sqrt κ with hα₀
  have hZc := isRegularWith_Z hFX hGc hZfc
  have hFl := LogSingGood.regular_add_Lf hFX α₀
  have hmem : ∀ᵐ w ∂ν, w ∈ closedBall (0 : ℂ) Rs ∩ Hbar := ae_iff.2 hsupp
  have hcar : ∀ᵐ w ∂ν, w ∈ Hbar ∧ ‖w‖ ≤ Rs :=
    hmem.mono fun w hw => ⟨hw.2, by simpa using hw.1⟩
  have hdec : ∀ k : ℕ, ∀ v ∈ Hbar, avgReg Z k v =
      avgReg X k v + α₀ * -Real.log (max (radius k) ‖v‖) +
        GoodSample.smoothFun G v (radius k) := by
    intro k v hv
    have hσ := radius_pos k
    have hreg := S5.FieldShift.regEq_of_fc hZfc
    rw [A1RF.avgReg_eq_of_regular hZc k hv]
    show evalReg Z (foldedCircle v (radius k)) = _
    rw [WedgeUnzip.evalReg_congr_avgReg (fun k z => hreg k z),
      show X + F2.logSingField κ = X + ofFun (LogSingGood.Lf α₀) from rfl,
      GoodSample.evalReg_add_ofFun_fc hFl hGc.continuousOn hv hσ,
      LogSingGood.evalReg_add_Lf_fc hFX α₀ hv hσ, hFX.evalReg_fc_of_mem hv hσ,
      A1RF.avgReg_eq_of_regular hFX k hv]
  -- integrability of the three parts
  have hiX : ∀ k : ℕ, Integrable (avgReg X k) ν := by
    intro k
    have hg : ContinuousOn (fun v : ℂ => FX (v, radius k)) Hbar :=
      hFX.1.comp (continuous_id.prodMk continuous_const).continuousOn fun v hv =>
        ⟨hv, radius_pos k⟩
    refine (WedgeUnzip.integrable_of_continuousOn_of_carried hg hcar).congr ?_
    filter_upwards [hcar] with v hv
    exact (A1RF.avgReg_eq_of_regular hFX k hv.1).symm
  have hil : ∀ k : ℕ, Integrable (fun v : ℂ => Real.log (max (radius k) ‖v‖)) ν := fun k =>
    WedgeUnzip.integrable_of_continuousOn_of_carried
      (Continuous.log (continuous_const.max continuous_norm) fun v =>
        ((radius_pos k).trans_le (le_max_left _ _)).ne').continuousOn hcar
  have hig : ∀ k : ℕ, Integrable (fun v => GoodSample.smoothFun G v (radius k)) ν := fun k =>
    WedgeUnzip.integrable_of_continuousOn_of_carried
      (GoodSample.continuous_smoothFun hGc.continuousOn _).continuousOn hcar
  have hsplit : ∀ k : ℕ, ∫ w, avgReg Z k w ∂ν = (∫ w, avgReg X k w ∂ν) +
      α₀ * -(∫ w, Real.log (max (radius k) ‖w‖) ∂ν) +
        ∫ w, GoodSample.smoothFun G w (radius k) ∂ν := by
    intro k
    have i2 : Integrable (fun a : ℂ => α₀ * -Real.log (max (radius k) ‖a‖)) ν :=
      ((hil k).neg).const_mul α₀
    have i1 : Integrable (fun a : ℂ => avgReg X k a + α₀ * -Real.log (max (radius k) ‖a‖)) ν :=
      (hiX k).add i2
    rw [integral_congr_ae (hcar.mono fun w hw => hdec k w hw.1), integral_add i1 (hig k),
      integral_add (hiX k) i2, integral_const_mul, integral_neg]
  have hK : IsCompact (closedBall (0 : ℂ) Rs ∩ Hbar) :=
    (isCompact_closedBall (0 : ℂ) Rs).inter_right isClosed_Hbar
  have hlim : Tendsto (fun k : ℕ => ∫ w, avgReg Z k w ∂ν) atTop
      (𝓝 (A + α₀ * (-∫ w, Real.log ‖w‖ ∂ν) + ∫ w, G w ∂ν)) := by
    refine ((hA.add (((CoordReg.tendsto_integral_log_max_frostman hsupp hF hα).neg).const_mul
      α₀)).add (FrostmanReg.tendsto_integral_smoothFun_frostman hGc.continuousOn hK
      inter_subset_right hsupp)).congr fun k => (hsplit k).symm
  exact hlim.limUnder_eq

end A1RS
end R18
end QuantumZipper
