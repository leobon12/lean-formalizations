/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MeanIdUniq
import InteractingSLE.Spec.Supplement.BHMean
import InteractingSLE.WangWu.Singular

/-!
# Aux. lemma 61, second half: finite-exception uniqueness in the restart chart

Packet PROVE-AUX61-MEAN. Astra's follow-up 4 §1.2 (`source/external/AstraIG1/ig1_followup4_audited.txt` L166–L176,
ruling R71): "The proposed expression `M⁰_u − M₀ − H_u q` has exactly those data … Aux. 61 uses the subpower and
derivative-argument bounds, followed by the already established finite-exception uniqueness, to exclude a residual
term supported at the seed or tip." In the restart chart the explored set at fibre time `t` is the slit hull
`K_t = fwdHull w t`; its complement is parametrized by the disc through `ζ ↦ F_t(cayleyInv ζ)` (`F_t = fwdMapInv w t`),
and the prime ends of `ℍ ∖ K_t` are the real points of the `F_t`-chart together with `∞`.

* **`eqOn_of_tendsto_slit`** (deterministic, Aux. lemmas 27–28 on the slit domain): two harmonic functions on
  `ℍ ∖ K_t` whose difference has logarithmic growth in the disc chart and tends to zero at every real point of the
  `F_t`-chart outside a finite set agree on `ℍ ∖ K_t`;
* **`isChartMeanAt_of_slit`** — (K-b) reduced to boundary data: if one conditional Gaussian decomposition of the chart
  field given `𝒢` has a harmonic part whose representative differs from the candidate mean `M` (harmonic off the
  chart hull) by a function with logarithmic growth and vanishing boundary limits at all but finitely many real
  points of the `F_t`-chart, then `IsChartMeanAt μ Z B Y q 𝒢 M` (every decomposition has the mean `M`). With
  `M = canonMean`, the boundary data are Aux. lemma 61's: zero relative boundary values on the old real boundary
  (`ae_tendsto_sub_of_condLaw`), the canonical germs on the two sides of the new slit, and the explicit boundary values
  of the canonical mean.

Conditional helpers with distinct names; they replace no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function Metric
open QuantumZipper (H fwdHull fwdMapInv)
open QuantumZipper.CA (cayley cayleyInv)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61MeanId

open Aux61Fib (FibCode)
open Aux61ChLoc (IsChartGaussAt IsChartMeanAt)
open Aux61UnionK (chartHull)

universe u

/-! ### Finite-exception uniqueness on the slit domain -/

/-- **Aux. lemmas 27–28 on the slit domain `ℍ ∖ K_t`** (deterministic): if `v` and `M` are harmonic on `ℍ ∖ K_t`, the
difference `(v − M)(F_t(cayleyInv ζ))` is bounded by `C (1 + log (1/(1 − |ζ|)))` on the disc, and
`(v − M)(F_t(y)) → 0` as `y → x` in `ℍ` for every real `x` outside a finite set, then `v = M` on `ℍ ∖ K_t`. -/
theorem eqOn_of_tendsto_slit {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {v M : ℂ → ℝ} (hv : InnerProductSpace.HarmonicOnNhd v (H \ fwdHull w t))
    (hM : InnerProductSpace.HarmonicOnNhd M (H \ fwdHull w t)) {C : ℝ}
    (hgrowth : ∀ ζ ∈ ball (0 : ℂ) 1, |v (fwdMapInv w t (cayleyInv ζ)) - M (fwdMapInv w t (cayleyInv ζ))| ≤
      C * (1 + Real.log (1 / (1 - ‖ζ‖))))
    {X : Set ℝ} (hX : X.Finite)
    (hbd : ∀ x : ℝ, x ∉ X →
      Tendsto (fun y => v (fwdMapInv w t y) - M (fwdMapInv w t y)) (𝓝[H] (x : ℂ)) (𝓝 0)) :
    EqOn v M (H \ fwdHull w t) := by
  have hf : SupercriticalConformalCovariance.IsConformalBijection (fun ζ => fwdMapInv w t (cayleyInv ζ))
      (ball 0 1) (H \ fwdHull w t) :=
    isConformalBijection_comp (isConformalBijection_fwdMapInv hw hw0 ht) isConformalBijection_cayleyInv
  have hu := WangWu.harmonicOnNhd_comp_sub hf hv hM
  set E : Set ℂ := insert (1 : ℂ) ((fun x : ℝ => cayley (x : ℂ)) '' X) with hEdef
  have hE : E.Finite := (hX.image _).insert _
  have h0 := WangWu.eqOn_zero_of_log_growth hu hE (C := C) (fun z hz _ => hgrowth z hz) (fun q hq hqE => by
    have hq1 : q ≠ 1 := fun h => hqE (h ▸ mem_insert _ _)
    obtain ⟨hre, hcay⟩ := Supp8.BHMean.tendsto_cayleyInv_sphere hq hq1
    have hxX : (cayleyInv q).re ∉ X := fun hx => hqE (mem_insert_of_mem _ ⟨(cayleyInv q).re, hx, by
      simp only
      rw [← hre, QuantumZipper.CA.cayley_cayleyInv hq1]⟩)
    exact (hbd _ hxX).comp hcay)
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := hf.2.surjOn hz
  exact sub_eq_zero.1 (h0 ζ hζ)

/-! ### (K-b) reduced to the boundary data of one decomposition -/

section Reduce

variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]
  {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
  {h₁ : X → DistOn upperHalfPlaneOpens}

/-- The chart hull's driver, read on `ℝ`. -/
theorem continuous_chartDriver (s : FibCode) : Continuous fun r : ℝ => FibCode.driver r.toNNReal s :=
  (FibCode.continuous_driver s).comp continuous_real_toNNReal

theorem chartDriver_zero (s : FibCode) : (fun r : ℝ => FibCode.driver r.toNNReal s) 0 = 0 := by
  simp only [Real.toNNReal_zero, FibCode.driver_zero]

/-- **(K-b) from the boundary data of one decomposition.** Let `h₁` be one conditional Gaussian decomposition of the
chart field given `𝒢` (e.g. `Aux61ChLoc.exists_isChartGaussAt_exit`), and `M` a candidate mean, harmonic off the chart
hull on the live event. Suppose that, almost surely on the live event, every harmonic representative `v` of `h₁` off
the chart hull `K_q` differs from `M` by a function with logarithmic growth in the disc chart of `ℍ ∖ K_q` and with
vanishing limits at all but finitely many real points of the `F_q`-chart. Then every decomposition given `𝒢` has the
mean `M` (`IsChartMeanAt`). -/
theorem isChartMeanAt_of_slit [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B) {M : X → ℂ → ℝ}
    (hG₀ : IsChartGaussAt μ Z B Y q 𝒢 h₁)
    (hMh : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      InnerProductSpace.HarmonicOnNhd (M x) (H \ chartHull Y q x))
    (hbd : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      (∃ C : ℝ, ∀ ζ ∈ ball (0 : ℂ) 1,
        |v (fwdMapInv (fun r : ℝ => FibCode.driver r.toNNReal (Y x)) q (cayleyInv ζ)) -
          M x (fwdMapInv (fun r : ℝ => FibCode.driver r.toNNReal (Y x)) q (cayleyInv ζ))| ≤
        C * (1 + Real.log (1 / (1 - ‖ζ‖)))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ x' : ℝ, x' ∉ S →
        Tendsto (fun y => v (fwdMapInv (fun r : ℝ => FibCode.driver r.toNNReal (Y x)) q y) -
          M x (fwdMapInv (fun r : ℝ => FibCode.driver r.toNNReal (Y x)) q y)) (𝓝[H] (x' : ℂ)) (𝓝 0)) :
    @IsChartMeanAt X mX β mβ μ Z B Y q 𝒢 M := by
  refine isChartMeanAt_of_isChartGaussAt hY hB hG₀ ?_
  filter_upwards [hG₀.harmonic, hMh, hbd] with x hharm hMx hbx hxB hlt ψ hψ
  obtain ⟨v, hv, hrep⟩ := hharm hxB hlt
  have hψs : tsupport ψ ⊆ H \ chartHull Y q x := fun z hz => ⟨ψ.tsupport_subset hz, Set.disjoint_left.1 hψ hz⟩
  obtain ⟨⟨C, hC⟩, S, hS, hlim⟩ := hbx hxB hlt v hv hrep
  have heq : EqOn v (M x) (H \ chartHull Y q x) :=
    eqOn_of_tendsto_slit (continuous_chartDriver (Y x)) (chartDriver_zero (Y x)) q.coe_nonneg hv (hMx hxB hlt)
      hC hS hlim
  rw [hrep ψ hψs]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ tsupport ψ
  · simp only [heq (hψs hz)]
  · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp only [h0, mul_zero]

end Reduce

end InteractingSLE.Sec5.Aux61MeanId
