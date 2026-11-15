/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61OldBCond
import InteractingSLE.Spec.Sec5.Aux61MeanIdNested
import InteractingSLE.WangWu.UnboundedComponent

/-!
# Aux. 61's old boundary, III: the relative chart mean (growth and old real boundary)

Packet PROVE-AUX61-OLDB. In the restart chart, with `h₀` a chart decomposition at fibre time `0` given `𝒢₀` and `h₁` one
at time `q` given `𝒢 ⊇ 𝒢₀` (both `IsChartGaussAt`), almost surely on the live event at `q`, for every harmonic
representative `v` of `h₁` off the chart hull `K_q` and every harmonic representative `v₀` of `h₀` on `ℍ`:

* **`ae_tendsto_sub_real`** (MEAN's (c1), probabilistic half, Astra's follow-up 4 L166–L169): `v − v₀ → 0` at every
  real point at positive distance from `K_q` — the marked nested Proposition 3.8
  (`Aux61MeanId.ae_tendsto_sub_of_condLaw`) under the time-`0` conditional measure, with the empty reference set (its
  germ is trivial, `measure_eq_zero_or_compl_of_germSigma_empty`) and the extended decomposition of `Aux61OldBCond`;
* **`ae_abs_sub_le_log`** (MEAN's (b), probabilistic half): `|v − v₀|(z) ≤ C (1 + log(1 + |z|) + log(1 + 1/d(z)))`
  on `ℍ ∖ K_q`, `d(z)` the distance to the complement — the landed global Gaussian bound for conditional means
  (`WangWu.ae_abs_le_log_global_of_condMean`) applied to the relative field.

No determination and no conditional independence are used. Conditional helpers with distinct names; no source
statement is replaced. R48/R77: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any
`*_of_param`, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex Metric
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61OldB

open Aux61Fib (FibCode)
open Aux61FibK (codeFiltration)
open Aux61ChLoc (IsChartGaussAt liveEv measurableSet_live)
open Aux61UnionK (chartHull isOpen_H_diff_chartHull)

universe u

/-! ### Representatives of the relative mean -/

section Rep

/-- **The difference of two representatives represents the difference.** If `v` represents `T₁` off `K` and `v₀`
represents `T₀` on `ℍ` (both harmonic), then `v − v₀` is harmonic off `K` and represents `T₁ − T₀` there. -/
theorem rep_sub {K : Set ℂ} {T₁ T₀ : DistOn upperHalfPlaneOpens} {v v₀ : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v (H \ K))
    (hrep : ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ K → T₁ ψ = ∫ z, v z * ψ z)
    (hv₀ : InnerProductSpace.HarmonicOnNhd v₀ H) (hrep₀ : ∀ ψ : TestOn upperHalfPlaneOpens, T₀ ψ = ∫ z, v₀ z * ψ z) :
    InnerProductSpace.HarmonicOnNhd (fun z => v z - v₀ z) (H \ K) ∧
      ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ K → (T₁ - T₀) ψ = ∫ z, (v z - v₀ z) * ψ z := by
  have hv₀' : InnerProductSpace.HarmonicOnNhd v₀ (H \ K) := fun z hz => hv₀ z hz.1
  refine ⟨fun z hz => (hv z hz).sub (hv₀' z hz), fun ψ hψ => ?_⟩
  have hvc : ContinuousOn v (H \ K) := fun z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hv₀c : ContinuousOn v₀ (H \ K) := fun z hz => (hv₀' z hz).1.continuousAt.continuousWithinAt
  have i₁ := WholeField.integrable_mul_testOn hvc ψ hψ
  have i₂ := WholeField.integrable_mul_testOn hv₀c ψ hψ
  rw [sub_apply, hrep ψ hψ, hrep₀ ψ, ← integral_sub i₁ i₂]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [sub_mul]

end Rep

/-! ### Under the time-`0` conditional measure -/

section Main

variable {X : Type u} {𝒢₀ 𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]
  {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
  {h₁ h₀ : X → DistOn upperHalfPlaneOpens}

/-- **The marked nested Proposition 3.8 for the relative chart mean** (under `μ[· | S₀]`): almost surely the relative
mean has a harmonic representative off the relative hull tending to `0` at every real point near which the hull is
empty. The empty reference set has mean `0`; its germ is trivial, so it can be joined to the old-boundary marks. -/
theorem ae_cond_tendsto_relMean_real [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) (h𝒢 : 𝒢₀ ≤ 𝒢)
    (hS : μ (liveEv Z B Y 0) ≠ 0) :
    ∀ᵐ x ∂μ[|liveEv Z B Y 0], ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ relHull Z B Y q x) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ relHull Z B Y q x →
        relMean (liveEv Z B Y q) h₁ h₀ (relField Y h₀) x φ = ∫ z, u z * φ z) ∧
      ∀ p : ℝ, (∃ r > 0, relHull Z B Y q x ∩ ball (p : ℂ) r ⊆ ∅) →
        Tendsto u (𝓝[H \ relHull Z B Y q x] (p : ℂ)) (𝓝 0) := by
  have := cond_isProbabilityMeasure (μ := μ) hS
  set S := liveEv Z B Y q with hSdef
  have hh₀ : Measurable h₀ := hG0.measurable.mono hG0.le le_rfl
  have hh' : Measurable (relField Y h₀) := measurable_relField hY hh₀
  have hh := isZeroBoundaryGFF_relField hY hB hG0 hS
  have hS𝒢 : MeasurableSet[𝒢] S := measurableSet_live hG.marksZ hG.marksY hB
  have hSm : MeasurableSet S := hG.le _ hS𝒢
  have h𝒥₁ : oldMarks 𝒢 S (relField Y h₀) ≤ mX := sup_le hG.le (hh'.indicator hSm.compl).comap_le
  have hgerm : LocalSets.germSigma (fun _ : X => (∅ : Set ℂ)) (relField Y h₀) ≤ mX :=
    LocalSets.germSigma_le measurable_const hh'
  have hA₁ : Measurable[𝒢, hittingSigma] (relHull Z B Y q) := measurable_relHull hG.marksZ hG.marksY hB
  have hgm := measurable_relMean hB hG0 hG h𝒢
  have hc := isCondZeroBoundaryGFF_sup_of_trivial h𝒥₁ hgerm
    (fun K hK => measure_eq_zero_or_compl_of_germSigma_empty hh hK)
    (measurable_distOn_sub hh' (hgm.mono h𝒥₁ le_rfl)) (isCondZeroBoundaryGFF_relMean hY hB hG0 hG h𝒢)
  have eU : (fun ω => H \ (relHull Z B Y q ω ∪ (fun _ : X => (∅ : Set ℂ)) ω)) = fun ω => H \ relHull Z B Y q ω := by
    funext ω; rw [union_empty]
  have hc' : IsCondZeroBoundaryGFF (μ[|liveEv Z B Y 0])
      (oldMarks 𝒢 S (relField Y h₀) ⊔ LocalSets.germSigma (fun _ : X => (∅ : Set ℂ)) (relField Y h₀))
      (fun ω => H \ (relHull Z B Y q ω ∪ (fun _ : X => (∅ : Set ℂ)) ω))
      (fun x => relField Y h₀ x - relMean S h₁ h₀ (relField Y h₀) x) := by
    rw [eU]; exact hc
  obtain ⟨g₂, hg₂⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh measurable_const (WangWu.isLocalSet_empty hh)
  have hunb : ∀ᵐ ω ∂μ[|liveEv Z B Y 0], ∀ z ∈ LocalSets.lowerUnion ((fun _ : X => (∅ : Set ℂ)) ω),
      ¬ Bornology.IsBounded (connectedComponentIn (LocalSets.lowerUnion ((fun _ : X => (∅ : Set ℂ)) ω)) z) := by
    refine Eventually.of_forall fun ω => LocalSets.not_isBounded_of_isPreconnected_union_real ?_
    rw [empty_union]
    have e : {w : ℂ | w.im = 0} = range ((↑) : ℝ → ℂ) := by
      ext w
      simp only [mem_ofPred_eq, mem_range]
      exact ⟨fun hw => ⟨w.re, Complex.ext (by simp) (by simp [hw])⟩, fun ⟨t, ht⟩ => by rw [← ht]; simp⟩
    rw [e]
    exact isPreconnected_range Complex.continuous_ofReal
  have h₁₂ : MeasurableSpace.comap (relHull Z B Y q) hittingSigma ⊔
      MeasurableSpace.comap (fun _ : X => (∅ : Set ℂ)) hittingSigma ≤
        oldMarks 𝒢 S (relField Y h₀) ⊔ LocalSets.germSigma (fun _ : X => (∅ : Set ℂ)) (relField Y h₀) := by
    refine sup_le (hA₁.comap_le.trans (le_sup_left.trans le_sup_left)) ?_
    rw [MeasurableSpace.comap_const]; exact bot_le
  have hharm : ∀ᵐ ω ∂μ[|liveEv Z B Y 0],
      IsHarmonicDistOn (relMean S h₁ h₀ (relField Y h₀) ω)
        (H \ (relHull Z B Y q ω ∪ (fun _ : X => (∅ : Set ℂ)) ω)) := by
    have h1 : ∀ᵐ ω ∂μ[|liveEv Z B Y 0], IsHarmonicDistOn (relMean S h₁ h₀ (relField Y h₀) ω) (H \ relHull Z B Y q ω) :=
      (cond_absolutelyContinuous (s := liveEv Z B Y 0)).ae_le (ae_isHarmonicDistOn_relMean hG0 hG)
    filter_upwards [h1] with ω hω
    rw [union_empty]; exact hω
  have h38 := Aux61MeanId.ae_tendsto_sub_of_condLaw hh (hA₁.mono hG.le le_rfl) measurable_const
    (Eventually.of_forall fun x => relHull_props x)
    (Eventually.of_forall fun _ => ⟨empty_subset _, by rw [sdiff_empty]; exact QuantumZipper.isOpen_H⟩)
    hunb (sup_le h𝒥₁ hgerm) le_sup_right h₁₂ (hgm.mono le_sup_left le_rfl) hharm hc' hg₂
  have hzero : ∀ᵐ ω ∂μ[|liveEv Z B Y 0], ∀ φ : TestOn upperHalfPlaneOpens, g₂ ω φ = 0 := by
    have hall := LocalSets.ae_forall_apply_eq_of_bump (T₁ := g₂) (T₂ := fun _ => 0) (O := fun _ => H)
      (Eventually.of_forall fun _ => ⟨QuantumZipper.isOpen_H, subset_rfl⟩)
      (hg₂.2.1.mono fun ω hω => by simpa only [sdiff_empty] using hω)
      (Eventually.of_forall fun _ => ?_)
      (fun x δ hδ hB => (Sec7.IsLocalSetMean.ae_apply_eq_zero_of_empty hh hg₂ _).mono fun ω hω _ => by
        rw [hω, zero_apply])
    · filter_upwards [hall] with ω hω φ
      exact hω φ (φ.tsupport_subset)
    · exact ⟨fun _ => 0, fun z _ => InnerProductSpace.harmonicAt_const 0, fun φ _ => by simp⟩
  filter_upwards [h38, hzero] with x ⟨u, hu, hrep, hlim⟩ hz
  simp only [union_empty] at hu hrep hlim
  refine ⟨u, hu, fun φ hφ => ?_, fun p hp => hlim p (Or.inr (by simp)) hp⟩
  rw [← hrep φ hφ, hz φ, sub_zero]

/-- **(c1), probabilistic half: the relative chart mean vanishes on the old real boundary.** Almost surely on the live
event at fibre time `q`, for every harmonic representative `v` of `h₁` off the chart hull `K_q` and every harmonic
representative `v₀` of `h₀` on `ℍ`, `v − v₀ → 0` at every real point at positive distance from `K_q`. -/
theorem ae_tendsto_sub_real [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) (h𝒢 : 𝒢₀ ≤ 𝒢) :
    ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∀ v₀ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v₀ H →
      (∀ ψ : TestOn upperHalfPlaneOpens, h₀ x ψ = ∫ z, v₀ z * ψ z) →
      ∀ p : ℝ, (∃ r > 0, Disjoint (ball (p : ℂ) r) (chartHull Y q x)) →
        Tendsto (fun z => v z - v₀ z) (𝓝[H \ chartHull Y q x] (p : ℂ)) (𝓝 0) := by
  classical
  by_cases hS : μ (liveEv Z B Y 0) = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS] with x hx hxB hlt
    exact absurd (liveEv_subset_zero (show x ∈ liveEv Z B Y q from ⟨hxB, hlt⟩)) hx
  have hS0m : MeasurableSet (liveEv Z B Y 0) := hG0.le _ (measurableSet_live hG0.marksZ hG0.marksY hB)
  filter_upwards [ae_mem_of_ae_cond hS0m (ae_cond_tendsto_relMean_real hY hB hG0 hG h𝒢 hS)] with x hx hxB hlt v hv
    hrep v₀ hv₀ hrep₀ p ⟨r, hr, hdis⟩
  have hxS : x ∈ liveEv Z B Y q := ⟨hxB, hlt⟩
  obtain ⟨u, hu, hurep, hulim⟩ := hx (liveEv_subset_zero hxS)
  rw [relHull_of_mem hxS] at hu hurep hulim
  have hrel := rep_sub hv hrep hv₀ hrep₀
  have heq : EqOn u (fun z => v z - v₀ z) (H \ chartHull Y q x) :=
    Sec6.eqOn_of_integral_mul_eq (isOpen_H_diff_chartHull Y hlt) sdiff_subset hu hrel.1 fun φ hφ => by
      rw [← hurep φ hφ, ← hrel.2 φ hφ, relMean, piecewise_eq_of_mem _ _ _ hxS]
  refine (hulim p ⟨r, hr, fun z hz => (Set.disjoint_left.1 hdis hz.2 hz.1).elim⟩).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz using heq hz

/-- **(b), probabilistic half: logarithmic growth of the relative chart mean.** Almost surely on the live event at
fibre time `q` there is `C` such that for every harmonic representative `v` of `h₁` off `K_q` and every harmonic
representative `v₀` of `h₀` on `ℍ`, `|v − v₀|(z) ≤ C (1 + log(1 + |z|) + log(1 + 1/d(z, (ℍ ∖ K_q)ᶜ)))` on `ℍ ∖ K_q`. -/
theorem ae_abs_sub_le_log [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) (h𝒢 : 𝒢₀ ≤ 𝒢) :
    ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∃ C : ℝ,
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∀ v₀ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v₀ H →
      (∀ ψ : TestOn upperHalfPlaneOpens, h₀ x ψ = ∫ z, v₀ z * ψ z) →
      ∀ z ∈ H \ chartHull Y q x, |v z - v₀ z| ≤
        C * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z (H \ chartHull Y q x)ᶜ)) := by
  classical
  by_cases hS : μ (liveEv Z B Y 0) = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS] with x hx hxB hlt
    exact absurd (liveEv_subset_zero (show x ∈ liveEv Z B Y q from ⟨hxB, hlt⟩)) hx
  have := cond_isProbabilityMeasure (μ := μ) hS
  have hS0m : MeasurableSet (liveEv Z B Y 0) := hG0.le _ (measurableSet_live hG0.marksZ hG0.marksY hB)
  set S := liveEv Z B Y q with hSdef
  have hh₀ : Measurable h₀ := hG0.measurable.mono hG0.le le_rfl
  have hh' : Measurable (relField Y h₀) := measurable_relField hY hh₀
  have hh := isZeroBoundaryGFF_relField hY hB hG0 hS
  have hS𝒢 : MeasurableSet[𝒢] S := measurableSet_live hG.marksZ hG.marksY hB
  have hSm : MeasurableSet S := hG.le _ hS𝒢
  have h𝒥₁ : oldMarks 𝒢 S (relField Y h₀) ≤ mX := sup_le hG.le (hh'.indicator hSm.compl).comap_le
  have hmean : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun x => relMean S h₁ h₀ (relField Y h₀) x φ) =ᵐ[μ[|liveEv Z B Y 0]]
        (μ[|liveEv Z B Y 0])[fun x => relField Y h₀ x φ | oldMarks 𝒢 S (relField Y h₀)] := fun φ =>
    ae_eq_condExp_of_isCondZeroBoundaryGFF h𝒥₁
      (Eventually.of_forall fun x => ⟨(relHull_props x).2, sdiff_subset⟩) hh'
      (measurable_relMean hB hG0 hG h𝒢) (isCondZeroBoundaryGFF_relMean hY hB hG0 hG h𝒢) φ
      ((hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two)
  have hlog := WangWu.ae_abs_le_log_global_of_condMean hh hmean
    (Eventually.of_forall fun x => (relHull_props (Z := Z) (B := B) (Y := Y) (q := q) x).2)
  filter_upwards [ae_mem_of_ae_cond hS0m hlog] with x hx hxB hlt
  have hxS : x ∈ liveEv Z B Y q := ⟨hxB, hlt⟩
  obtain ⟨C, hC⟩ := hx (liveEv_subset_zero hxS)
  refine ⟨C, fun v hv hrep v₀ hv₀ hrep₀ z hz => ?_⟩
  rw [relHull_of_mem hxS] at hC
  have hrel := rep_sub hv hrep hv₀ hrep₀
  exact hC (fun z => v z - v₀ z) hrel.1 (fun φ hφ => by
    rw [relMean, piecewise_eq_of_mem _ _ _ hxS]; exact hrel.2 φ hφ) z hz

end Main

end InteractingSLE.Sec5.Aux61OldB
