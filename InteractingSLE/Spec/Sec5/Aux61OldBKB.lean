/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61OldBRel
import InteractingSLE.Spec.Sec5.Aux61OldBWord

/-!
# Aux. 61's old boundary, V: MEAN's (b) and (c1) and (K-b) at fibre time `q` from (K-b) at time `0`

Packet PROVE-AUX61-OLDB. The two boundary inputs `hgrowth` (MEAN's (b)) and `hold` (MEAN's (c1)) of CONFIG's
`Aux61Conf2.isChartMeanAt_canonMean_of_glued` are PROVED from the time-`0` data:

* **`ae_rep_fibMean0`**: (K-b) at fibre time `0` (`IsChartMeanAt … 0 𝒢₀ (canonMean … 0)`, the definition of the data's
  correction `d.q`: `canonMean d F s 0 = fibMean0 d` on `ℍ`, GLUEINST's `canonMean_zero`) makes `fibMean0 d` a harmonic
  representative of every time-`0` decomposition;
* **`ae_growth_canonMean`** (`hgrowth`): `v − canonMean = (v − fibMean0) + (fibMean0 − canonMean)`; the first term has
  the global Gaussian bound (`ae_abs_sub_le_log`), transported to the disc chart of `ℍ ∖ K_q`
  (`WangWu.growth_of_global`, `Sec6.exists_abs_comp_le_log_of_log_norm_growth`); the second is GLUEINST's
  `exists_abs_canonMean_sub_le_log`;
* **`ae_old_canonMean`** (`hold`): off the finite set `oldExc`, at a real `x′` with real `F_q`-boundary value `p`, the
  first term tends to `0` (`ae_tendsto_sub_real` at `p`, composed with `F_q → p` inside `ℍ ∖ K_q`) and so does the
  second (`tendsto_fibMean0_sub_canonMean_old`);
* **`isChartMeanAt_canonMean_of_glued_of_zero`** — **(K-b) at fibre time `q`** from CONFIG's glued data, SLIT's
  comparison, a time-`0` decomposition given `𝒢₀ ≤ 𝒢`, and (K-b) at fibre time `0`.

Conditional helpers with distinct names; no source statement is replaced. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param`, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open QuantumZipper.CA (cayleyInv)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61OldB

open Aux61Fib (FibCode FibData)
open Aux61ChLoc (IsChartGaussAt IsChartMeanAt liveEv)
open Aux61UnionK (chartHull canonMean isOpen_H_diff_chartHull)
open Aux61Conf2 (IsGluedSlit IsGluedSlitSample chartDrv)
open Aux61GlueK (refMean0 fibMean0)
open Aux61Win (IsCutoffOn)
open Restart.FlowStopIdentCMI (CMCut)

universe u v

/-- The time-`0` mean `fibMean0 d = refMean0 d + d.q` is harmonic on `ℍ`. -/
theorem harmonicOnNhd_fibMean0 (d : FibData) : InnerProductSpace.HarmonicOnNhd (fibMean0 d) H :=
  fun z hz => ((Aux61GlueK.refMean0_ext d).1 z hz).add (d.q_harm z hz)

section KB

variable {X : Type u} {𝒢₀ 𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]
  {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
  {h₁ h₀ : X → DistOn upperHalfPlaneOpens}

/-- **(K-b) at fibre time `0` identifies the time-`0` representative**: almost surely on the time-`0` live event,
`fibMean0 d` represents every time-`0` decomposition on all of `ℍ`. -/
theorem ae_rep_fibMean0 {d : X → FibData} {F₀ : X → CMCut} (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀)
    (hKb0 : @IsChartMeanAt X mX β mβ μ Z B Y 0 𝒢₀ fun x => canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) 0) :
    ∀ᵐ x ∂μ, Z x ∈ B → ((0 : ℝ≥0) : ℝ≥0∞) < (Y x).life →
      ∀ ψ : TestOn upperHalfPlaneOpens, h₀ x ψ = ∫ z, fibMean0 (d x) z * ψ z := by
  filter_upwards [hKb0 h₀ hG0] with x hx hxB hlt ψ
  rw [hx hxB hlt ψ (by rw [chartHull_zero]; exact disjoint_empty _)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ H
  · simp only [Aux61GInst.canonMean_zero.{v} (d x) (F₀ x) (ULift.up (Y x)) hz]
  · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (ψ.tsupport_subset h)
    simp only [h0, mul_zero]

/-- **(K-b) at fibre time `0` from one decomposition** (the definition of the data's correction): if `fibMean0 d`
represents one time-`0` decomposition on `ℍ`, then every time-`0` decomposition has the canonical mean
`canonMean d F s 0` (`= fibMean0 d` on `ℍ`, GLUEINST's `canonMean_zero`; uniqueness of the harmonic part, MEAN's
`isChartMeanAt_of_isChartGaussAt`). -/
theorem isChartMeanAt_zero_of_fibMean0 [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) {d : X → FibData} {F₀ : X → CMCut}
    (hrep : ∀ᵐ x ∂μ, Z x ∈ B → ((0 : ℝ≥0) : ℝ≥0∞) < (Y x).life →
      ∀ ψ : TestOn upperHalfPlaneOpens, h₀ x ψ = ∫ z, fibMean0 (d x) z * ψ z) :
    @IsChartMeanAt X mX β mβ μ Z B Y 0 𝒢₀ fun x => canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) 0 := by
  refine Aux61MeanId.isChartMeanAt_of_isChartGaussAt hY hB hG0 ?_
  filter_upwards [hrep] with x hx hxB hlt ψ _
  rw [hx hxB hlt ψ]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ H
  · simp only [Aux61GInst.canonMean_zero.{v} (d x) (F₀ x) (ULift.up (Y x)) hz]
  · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (ψ.tsupport_subset h)
    simp only [h0, mul_zero]

/-- **MEAN's (b): the logarithmic growth of `v − canonMean` in the disc chart** (the input `hgrowth` of
`Aux61Conf2.isChartMeanAt_canonMean_of_glued`), from a time-`0` decomposition given `𝒢₀ ≤ 𝒢`, (K-b) at time `0`, and the
cutoff of the data's correction near the closed chart hull. -/
theorem ae_growth_canonMean [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) (h𝒢 : 𝒢₀ ≤ 𝒢)
    {d : X → FibData} {F₀ : X → CMCut} {N : X → Set ℂ}
    (hKb0 : @IsChartMeanAt X mX β mβ μ Z B Y 0 𝒢₀ fun x => canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) 0)
    (hcut : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      IsCutoffOn (F₀ x) (d x).q (N x) (d x).O₀ ∧ closure (fwdHull (chartDrv Y x) q) ⊆ N x) :
    ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∃ C : ℝ, ∀ ζ ∈ ball (0 : ℂ) 1,
        |v (fwdMapInv (chartDrv Y x) q (cayleyInv ζ)) -
          canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) q (fwdMapInv (chartDrv Y x) q (cayleyInv ζ))| ≤
        C * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
  filter_upwards [ae_abs_sub_le_log hY hB hG0 hG h𝒢, ae_rep_fibMean0 hG0 hKb0, hcut] with x hlog hrep0 hcx hxB hlt v
    hv hrep
  obtain ⟨C₁, hC₁⟩ := hlog hxB hlt
  have hlt0 : ((0 : ℝ≥0) : ℝ≥0∞) < (Y x).life := lt_of_le_of_lt (by simp) hlt
  have hb := hC₁ v hv hrep (fibMean0 (d x)) (harmonicOnNhd_fibMean0 _) (hrep0 hxB hlt0)
  have hCo := isOpen_H_diff_chartHull Y hlt
  have hf : SupercriticalConformalCovariance.IsConformalBijection
      (fun ζ => fwdMapInv (chartDrv Y x) q (cayleyInv ζ)) (ball 0 1) (H \ chartHull Y q x) :=
    isConformalBijection_comp (isConformalBijection_fwdMapInv (Aux61MeanId.continuous_chartDriver (Y x))
      (Aux61MeanId.chartDriver_zero (Y x)) q.coe_nonneg) isConformalBijection_cayleyInv
  obtain ⟨K₁, hK₁⟩ := Sec6.exists_abs_comp_le_log_of_log_norm_growth hCo hf
    (WangWu.growth_of_global hCo sdiff_subset hCo subset_rfl hb)
  obtain ⟨hF, hKN⟩ := hcx hxB hlt
  obtain ⟨C₂, hC₂⟩ := Aux61GInst.exists_abs_canonMean_sub_le_log hF (ULift.up (Y x)) q hKN
  refine ⟨K₁ + C₂, fun ζ hζ => ?_⟩
  have h1 := hK₁ ζ hζ
  have h2 := hC₂ ζ hζ
  set z := fwdMapInv (chartDrv Y x) q (cayleyInv ζ) with hz
  change |canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) q z - fibMean0 (d x) z| ≤ _ at h2
  have h3 := abs_sub_le (v z) (fibMean0 (d x) z) (canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) q z)
  rw [abs_sub_comm (fibMean0 (d x) z)] at h3
  have h1' : |v z - fibMean0 (d x) z| ≤ K₁ * (1 + Real.log (1 / (1 - ‖ζ‖))) := h1
  rw [add_mul]
  linarith

/-- **MEAN's (c1): the old real boundary** (the input `hold` of `Aux61Conf2.isChartMeanAt_canonMean_of_glued`): almost
surely on the live event, every harmonic representative `v` satisfies `v ∘ F_q − canonMean ∘ F_q → 0` at every real
`x′` off the finite set `oldExc` whose `F_q`-boundary value is real. -/
theorem ae_old_canonMean [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) (h𝒢 : 𝒢₀ ≤ 𝒢)
    {d : X → FibData} {F₀ : X → CMCut} {N : X → Set ℂ} {Wph : X → ℝ → ℝ} {η : X → ℝ → ℂ} {r τ Tc : X → ℝ}
    {c : X → Chart} {D : X → Set ℂ} {γ : X → ℝ → ℂ}
    (hKb0 : @IsChartMeanAt X mX β mβ μ Z B Y 0 𝒢₀ fun x => canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) 0)
    (hglued : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      IsGluedSlit (Wph x) (η x) (r x) (τ x) (c x) (D x) (chartDrv Y x) (γ x) (Tc x) q ∧
        IsCutoffOn (F₀ x) (d x).q (N x) (d x).O₀ ∧ closure (fwdHull (chartDrv Y x) q) ⊆ N x) :
    ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∃ S : Set ℝ, S.Finite ∧ ∀ x' : ℝ, x' ∉ S → extendFrom H (fwdMapInv (chartDrv Y x) q) x' ∉ H →
        Tendsto (fun y => v (fwdMapInv (chartDrv Y x) q y) -
          canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) q (fwdMapInv (chartDrv Y x) q y)) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_sub_real hY hB hG0 hG h𝒢, ae_rep_fibMean0 hG0 hKb0, hglued] with x hrel hrep0 hgx hxB
    hlt v hv hrep
  obtain ⟨hg, hF, hKN⟩ := hgx hxB hlt
  have hlt0 : ((0 : ℝ≥0) : ℝ≥0∞) < (Y x).life := lt_of_le_of_lt (by simp) hlt
  refine ⟨oldExc (d x) (Y x) q, oldExc_finite _ _ _, fun x' hx' hx'H => ?_⟩
  obtain ⟨p, hpcl, hFt, hdet⟩ := tendsto_fibMean0_sub_canonMean_old.{v} (d x) hg hF hKN hx' hx'H
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl (p : ℂ) hpcl
  have hball : ∃ ρ > 0, Disjoint (ball (p : ℂ) ρ) (chartHull Y q x) :=
    ⟨ρ, hρ, Set.disjoint_left.2 fun z hz hzK => hsub hz (subset_closure hzK)⟩
  have h1 := hrel hxB hlt v hv hrep (fibMean0 (d x)) (harmonicOnNhd_fibMean0 _) (hrep0 hxB hlt0) p hball
  have hFK : Tendsto (fwdMapInv (chartDrv Y x) q) (𝓝[H] (x' : ℂ)) (𝓝[H \ chartHull Y q x] (p : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hFt, eventually_nhdsWithin_of_forall fun y hy =>
      (isConformalBijection_fwdMapInv (Aux61MeanId.continuous_chartDriver (Y x))
        (Aux61MeanId.chartDriver_zero (Y x)) q.coe_nonneg).2.mapsTo hy⟩
  have h := (h1.comp hFK).add hdet
  rw [add_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply]
  ring

/-- **(K-b) at fibre time `q` from (K-b) at fibre time `0`** (Theorem 1.2's Prop 5.1 (E1), Aux. 61's mean at the glued
stop): CONFIG's assembly `Aux61Conf2.isChartMeanAt_canonMean_of_glued` with its two remaining inputs supplied —
`hgrowth` by `ae_growth_canonMean` and `hold` by `ae_old_canonMean`. Inputs: one decomposition `h₁` at time `q`
given `𝒢`, the glued data and SLIT's comparison (as in CONFIG), one decomposition `h₀` at time `0` given `𝒢₀ ≤ 𝒢`,
and (K-b) at fibre time `0` (the data's correction is the time-`0` mean). -/
theorem isChartMeanAt_canonMean_of_glued_of_zero [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG₀ : IsChartGaussAt μ Z B Y q 𝒢 h₁) (κ : ℝ) {d : X → FibData} {F₀ : X → CMCut} {N : X → Set ℂ}
    {Wph : X → ℝ → ℝ} {η : X → ℝ → ℂ} {r τ Tc : X → ℝ} {c : X → Chart} {D : X → Set ℂ} {γ : X → ℝ → ℂ}
    {ι : Type*} {ρ : ι → X → ℝ} {L : ι → X → Set ℂ} {A : X → Set ℂ} {M₂ uph : ι → X → ℂ → ℝ}
    {S' : ι → Set X}
    (hglued : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      IsGluedSlitSample κ (d x) (F₀ x) (N x) (Y x) q (Wph x) (η x) (r x) (τ x) (c x) (D x) (γ x) (Tc x)
        (fun i => ρ i x) (fun i => L i x) (A x) (fun i => M₂ i x) (fun i => uph i x))
    (hS' : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ i, ρ i x < r x + τ x → x ∈ S' i)
    (hconv : ∀ᵐ x ∂μ, ∀ i, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → x ∈ S' i →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∀ z₀ ∈ L i x ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A x ∩ ball z₀ r ⊆ L i x) →
      ∀ l : Filter ℂ, l ≤ 𝓟 (H \ chartHull Y q x) → Tendsto (c x).2.1 l (𝓝 z₀) →
        Tendsto (fun ζ => v ζ - (M₂ i x ((c x).2.1 ζ) + 0 + QuantumZipper.chiC κ * (c x).2.2 ((c x).2.1 ζ))) l
          (𝓝 0))
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) (h𝒢 : 𝒢₀ ≤ 𝒢)
    (hKb0 : @IsChartMeanAt X mX β mβ μ Z B Y 0 𝒢₀ fun x => canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) 0) :
    @IsChartMeanAt X mX β mβ μ Z B Y q 𝒢 fun x => canonMean.{v} (d x) (F₀ x) (ULift.up (Y x)) q := by
  have hcut : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      IsCutoffOn (F₀ x) (d x).q (N x) (d x).O₀ ∧ closure (fwdHull (chartDrv Y x) q) ⊆ N x := by
    filter_upwards [hglued] with x hx hxB hlt
    have hs := hx hxB hlt
    exact ⟨hs.cutoff, hs.hullN⟩
  have hgl : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      IsGluedSlit (Wph x) (η x) (r x) (τ x) (c x) (D x) (chartDrv Y x) (γ x) (Tc x) q ∧
        IsCutoffOn (F₀ x) (d x).q (N x) (d x).O₀ ∧ closure (fwdHull (chartDrv Y x) q) ⊆ N x := by
    filter_upwards [hglued] with x hx hxB hlt
    have hs := hx hxB hlt
    exact ⟨hs.glued, hs.cutoff, hs.hullN⟩
  exact Aux61Conf2.isChartMeanAt_canonMean_of_glued hY hB hG₀ κ hglued hS' hconv
    (ae_growth_canonMean hY hB hG0 hG₀ h𝒢 hKb0 hcut) (ae_old_canonMean hY hB hG0 hG₀ h𝒢 hKb0 hgl)

end KB

end InteractingSLE.Sec5.Aux61OldB
