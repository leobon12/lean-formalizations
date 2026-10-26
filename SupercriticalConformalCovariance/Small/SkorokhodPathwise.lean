import SupercriticalConformalCovariance.Small.FlagContradiction

set_option autoImplicit false
noncomputable section
open Filter Topology Set
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.PfeAxioms

/-- A pathwise contradiction for a Skorokhod sample carrying both metric
coordinates, selected endpoints and a continuous Boolean failure flag. -/
theorem no_flagged_skorokhod_sample
    {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    (Y : ℕ → (X × (LSCFun × LSCFun)) × T)
    (Ylim : (X × (LSCFun × LSCFun)) × T)
    (hY : Tendsto Y atTop (𝓝 Ylim))
    (d : LSCMetric)
    (hlimD : Ylim.1.2.1 = d.toLSCFun)
    (hlimE : Ylim.1.2.2 = d.toLSCFun)
    (c : NNReal) (hc : 0 < c)
    (hFm : ∀ n, IsMetricLSCFun (Y n).1.2.1)
    (hGm : ∀ n, IsMetricLSCFun (Y n).1.2.2)
    (hFlen : ∀ n, (ambientMetricLift (Y n).1.2.1).IsLengthSpace)
    (hGlen : ∀ n, (ambientMetricLift (Y n).1.2.2).IsLengthSpace)
    (hFreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (ambientMetricLift (Y n).1.2.1).IsCurve P a b →
      (ambientMetricLift (Y n).1.2.1).len P a b < ⊤ →
      ContinuousOn P (Icc a b))
    (hGreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (ambientMetricLift (Y n).1.2.2).IsCurve P a b →
      (ambientMetricLift (Y n).1.2.2).len P a b < ⊤ →
      ContinuousOn P (Icc a b))
    (hcomp : ∀ n : ℕ, ∀ x y : ℂ,
      ambientMetricLift (Y n).1.2.1 (x,y) ≤
          (c : ℝ≥0∞) * ambientMetricLift (Y n).1.2.2 (x,y) ∧
      ambientMetricLift (Y n).1.2.2 (x,y) ≤
          (c : ℝ≥0∞) * ambientMetricLift (Y n).1.2.1 (x,y))
    (u v : T → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hKend : ∀ t, u t ∈ K ∧ v t ∈ K)
    (flag : T → Bool) (hflag : Continuous flag)
    (hflaglim : flag Ylim.2 = true)
    (α θ m : ℝ) (hα : α < 1) (hθ : 0 < θ)
    (M : NNReal) (η : ℝ) (hη : 0 < η)
    (hbad : ∀ n, flag (Y n).2 = true →
      SupercriticalConformalCovariance.Regular.SourceFailure
        (ambientMetricLift (Y n).1.2.1)
        (ambientMetricLift (Y n).1.2.2)
        0 (u (Y n).2) (v (Y n).2) 1 α θ m (M : ℝ) (1 - α) η) : False := by
  have hF : Tendsto (fun n => (Y n).1.2.1) atTop (𝓝 d.toLSCFun) := by
    have hp : Continuous
        (fun y : (X × (LSCFun × LSCFun)) × T => y.1.2.1) :=
      (continuous_fst.comp continuous_snd).comp continuous_fst
    have ht := (hp.tendsto Ylim).comp hY
    simpa only [Function.comp_def, hlimD] using ht
  have hG : Tendsto (fun n => (Y n).1.2.2) atTop (𝓝 d.toLSCFun) := by
    have hp : Continuous
        (fun y : (X × (LSCFun × LSCFun)) × T => y.1.2.2) :=
      (continuous_snd.comp continuous_snd).comp continuous_fst
    have ht := (hp.tendsto Ylim).comp hY
    simpa only [Function.comp_def, hlimE] using ht
  have hflagEventually : ∀ᶠ n in atTop, flag (Y n).2 = true := by
    have ht : Tendsto (fun n => flag (Y n).2) atTop (𝓝 true) := by
      have h := ((hflag.comp continuous_snd).tendsto Ylim).comp hY
      simpa only [Function.comp_def, hflaglim] using h
    exact ht.eventually (IsOpen.mem_nhds (isOpen_discrete {true}) rfl)
  exact no_eventual_ambient_failure
    (fun n => (Y n).1.2.1) (fun n => (Y n).1.2.2)
    d hF hG c hc hFm hGm hFlen hGlen hFreg hGreg hcomp
    (fun n => u (Y n).2) (fun n => v (Y n).2) K hK
    (fun n => hKend (Y n).2)
    α θ m hα hθ M η hη
    (hflagEventually.mono (fun n hn => hbad n hn))

end SupercriticalConformalCovariance.Small
