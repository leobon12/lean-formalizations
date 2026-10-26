import SupercriticalConformalCovariance.Lemma31.Random
import SupercriticalConformalCovariance.Lemma31.LscMeas

/-!
# Lemma 3.1: measurable `LSCFun`-valued confined metrics and convergence in measure

* `confinedLSC`: the confined metric of `x + f` on `K = closedBall c R` (`f ∈ C(K′)`), as an element
  of `LSCFun`: the closed-disk path infimum of `D_{x + F}`, `F` the radial extension of `f|_K`. It is a
  **measurable** function of `(x, f) ∈ 𝒟'(ℂ) × C(K′)` (`measurable_confinedLSC`), and for a whole-plane
  GFF plus a continuous function `h`, a.s. simultaneously for all `f` it is the confined metric
  `SupercriticalConformalCovariance.Domain.confined` (`ae_confinedLSC_eq`). This handles the measurability of the confined metrics
  as random variables in the lsc space, values `∞` included.
* `confinedConvergence_tendstoInMeasure`: under the hypotheses of `confinedConvergence_subseq` (and
  measurability of every `f n`), the confined metrics converge in probability for **every**
  pseudo-emetric inducing the topology of DG Definition 1.2 (paper l. 159–161).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Lemma31

open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont addFun ofCont)
open SupercriticalLQGUniqueness (LSCMetric LSCFun IsStrongLQGMetric LSCTendsto)
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints (closedBallPathInf
  closedBallPathInf_joint_lsc)
open SupercriticalConformalCovariance.Domain (confined resC ae_weylScaleOn_eq_internal)

/-- The closed-disk path infimum, as a kernel on `LSCMetric × (ℂ × ℂ)` with values in `EReal`. -/
def diskKernel (c : ℂ) (R : ℝ) (D₀ : LSCMetric) (q : ℂ × ℂ) : EReal :=
  ((closedBallPathInf D₀ c R q.1 q.2 : ℝ≥0∞) : EReal)

theorem diskKernel_lsc (c : ℂ) (R : ℝ) :
    LowerSemicontinuous fun p : LSCMetric × (ℂ × ℂ) => diskKernel c R p.1 p.2 := by
  have hc : Continuous fun p : LSCMetric × (ℂ × ℂ) => (p.1, (c, (R, p.2))) :=
    continuous_fst.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_snd))
  have h2 : LowerSemicontinuous fun p : LSCMetric × (ℂ × ℂ) =>
      closedBallPathInf p.1 c R p.2.1 p.2.2 := by
    change LowerSemicontinuous
      ((fun p : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) =>
        closedBallPathInf p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∘
        fun p : LSCMetric × (ℂ × ℂ) => (p.1, (c, (R, p.2))))
    exact closedBallPathInf_joint_lsc.comp hc
  exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous h2
    EReal.coe_ennreal_strictMono.monotone

/-- The confined metric on `closedBall c R` of `x + f` (`f ∈ C(K′)`), as an element of `LSCFun`. -/
def confinedLSC (D : DistC → LSCMetric) (c : ℂ) {R : ℝ} (hR : 0 < R) {K' : Set ℂ}
    (hKK' : closedBall c R ⊆ K') (x : DistC) (f : C(K', ℝ)) : LSCFun :=
  lscSection (diskKernel c R) (diskKernel_lsc c R) (D (addFun x (diskExt c hR (resC hKK' f))))

/-- **Measurability.** The `LSCFun`-valued confined metric is a Borel function of
`(x, f) ∈ 𝒟'(ℂ) × C(K′)`. -/
theorem measurable_confinedLSC {D : DistC → LSCMetric} (hDm : Measurable D) (c : ℂ) {R : ℝ}
    (hR : 0 < R) {K' : Set ℂ} (hKK' : closedBall c R ⊆ K') [MeasurableSpace LSCFun]
    [BorelSpace LSCFun] :
    Measurable fun p : DistC × C(K', ℝ) => confinedLSC D c hR hKK' p.1 p.2 := by
  have := SupercriticalLQGUniqueness.B2.LscTop.borelSpace_LSCMetric
  have hF : Measurable fun p : DistC × C(K', ℝ) => diskExt c hR (resC hKK' p.2) :=
    (measurable_diskExt c hR).comp ((ContinuousMap.continuous_precomp _).measurable.comp
      measurable_snd)
  exact (measurable_lscSection _ (diskKernel_lsc c R)).comp
    (hDm.comp (LQGMetric.measurable_addFun.comp (measurable_fst.prodMk hF)))

/-- **Identification.** For a whole-plane GFF plus a continuous function `h`, a.s. simultaneously for
all `f ∈ C(K′)`, `confinedLSC` is the confined metric `SupercriticalConformalCovariance.Domain.confined` (coerced to `EReal`). -/
theorem ae_confinedLSC_eq {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (c : ℂ) {R : ℝ} (hR : 0 < R) {K' : Set ℂ}
    (hKK' : closedBall c R ⊆ K') {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ f : C(K', ℝ), (confinedLSC D c hR hKK' (h ω) f).1 =
      fun q => ((confined (ξ : ℝ) (D (h ω)) hKK' f q : ℝ≥0∞) : EReal) := by
  filter_upwards [ae_weylScaleOn_eq_internal hD P hh] with ω hω f
  rw [confined_eq_closedBallPathInf hω c hR hKK' f]
  rfl

/-- **Lemma 3.1 (repaired, `lem-3.1#repaired`), convergence in probability for a metric.** Under the
hypotheses of `confinedConvergence_subseq`, with every `f n` measurable, the `LSCFun`-valued confined
metrics of `g n + f n` converge in `P`-probability to that of `g∞ + f∞`, for every pseudo-emetric `d`
inducing the topology of DG Definition 1.2. (Jointly with the fields: `P[g_n|_U ≠ g∞|_U] → 0` is the
hypothesis itself; along subsequences, a.s. eventual equality holds by `confinedConvergence_subseq`.) -/
theorem confinedConvergence_tendstoInMeasure {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {K' : Set ℂ} (hKK' : closedBall c R ⊆ K') (U : Opens ℂ) (hKU : closedBall c R ⊆ U)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℕ → Ω → DistC) (gL : Ω → DistC) (hg : ∀ n, IsGFFPlusCont (g n) P)
    (hgL : IsGFFPlusCont gL P) (f : ℕ → Ω → C(K', ℝ)) (fL : Ω → C(K', ℝ))
    (hf : ∀ n, Measurable (f n)) (hfL : Measurable fL)
    (hcoup : Tendsto (fun n => P {ω | restrictTo U (g n ω) ≠ restrictTo U (gL ω)}) atTop (𝓝 0))
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P {ω | ∃ x : K', ε < |f n ω x - fL ω x|}) atTop (𝓝 0))
    (d : PseudoEMetricSpace LSCFun)
    (hd : d.toUniformSpace.toTopologicalSpace = LSCFun.instTopologicalSpace) :
    @TendstoInMeasure _ _ _ d.toEDist _ P
      (fun n ω => confinedLSC D c hR hKK' (g n ω) (f n ω)) atTop
      (fun ω => confinedLSC D c hR hKK' (gL ω) (fL ω)) := by
  let _ : MeasurableSpace LSCFun := borel LSCFun
  have _ : BorelSpace LSCFun := ⟨rfl⟩
  have hmeas : ∀ n, @AEStronglyMeasurable _ _ d.toUniformSpace.toTopologicalSpace _ _
      (fun ω => confinedLSC D c hR hKK' (g n ω) (f n ω)) P := by
    intro n
    have hm0 := measurable_confinedLSC hD.1 c hR hKK'
    have hm := hm0.comp ((hg n).1.prodMk (hf n))
    have h := hm.aestronglyMeasurable (μ := P)
    rw [← hd] at h
    exact h
  refine (@exists_seq_tendstoInMeasure_atTop_iff _ _ _ P d _ _ hmeas _).2 fun ns hns => ?_
  obtain ⟨ms, hms, hae⟩ := confinedConvergence_subseq hD c hR hKK' U hKU P g gL hg hgL f fL hfL
    hcoup hconv ns hns
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae, ae_all_iff.2 fun n => ae_confinedLSC_eq hD c hR hKK' P (hg n),
    ae_confinedLSC_eq hD c hR hKK' P hgL] with ω hω hn hL
  rw [hd]
  refine SupercriticalLQGUniqueness.LSCFun.tendsto_iff_lscTendsto.2 ?_
  simp only [hn, hL]
  exact hω.1

end SupercriticalConformalCovariance.Lemma31
