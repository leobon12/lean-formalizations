import SupercriticalConformalCovariance.Small.ConfinedVarying
import SupercriticalConformalCovariance.Small.CommonRealization
import SupercriticalConformalCovariance.Small.TangentBridge
import SupercriticalConformalCovariance.Small.ConfinedMeasurable
import SupercriticalConformalCovariance.Small.TargetConfinedMeasurable

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric TopologicalSpace

namespace SupercriticalConformalCovariance.Small
open LQGMetric (DistC IsWholePlaneGFF restrictTo addFun ofCont CoordJ pairJ)
open SupercriticalLQGUniqueness (LSCMetric LSCFun IsStrongLQGMetric IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)
open SupercriticalConformalCovariance.GM24 (isConformalBijection_invFunOn)
open SupercriticalConformalCovariance.Tangent
open SupercriticalConformalCovariance.Domain (exW cutF measurable_cutExt)

/-- Lemma 3.3 in law on the diagonal-corrected confined metric coordinates,
for a triangular array of normalized fields with one common field law. -/
theorem tangent_limit_conf_law_varying
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ}
    (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop)
    (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Y Ω : Type} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → DistC) (mark : ℕ → Ω → Y)
    (hHm : ∀ n, Measurable (H n)) (hmarkm : ∀ n, Measurable (mark n))
    (μ : Measure DistC) [IsProbabilityMeasure μ] (y₀ : Y)
    (hlaw : ∀ n, P.map (H n) = μ)
    (hwpH : IsWholePlaneGFF (H 0) P)
    (J : ∀ n, DistC × Y → SupercriticalConformalCovariance.Transport.RealizationData (V n))
    (hJ : ∀ n, Measurable (J n))
    (hfield : ∀ n p, (J n p).1 =
      confPullbackField Q (isConformalBijection_invFunOn (hψ n))
        (restrictTo (U n) p.1))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => (J n (H n ω, mark n ω)).1)
      (fun ω => (J n (H n ω, mark n ω)).2.1)
      (fun ω => (J n (H n ω, mark n ω)).2.2.1))
    (hwpJ : ∀ n, IsWholePlaneGFF
      (fun ω => (J n (H n ω, mark n ω)).2.1 -
        ofCont (J n (H n ω, mark n ω)).2.2.2) P)
    [MeasurableSpace LSCFun] [BorelSpace LSCFun] :
    ∃ m : ℕ → ℕ,
      (∀ n, ψ n '' closedBall (0 : ℂ) (R n) ⊆ exW (V n) (m n)) ∧
      ∀ F : BoundedContinuousFunction ((CoordJ → ℝ) × LSCFun × LSCFun) ℝ,
        Tendsto (fun n => ∫ ω,
          F (pairJ ⊤ (H n ω),
            (conf (D (H n ω)) 0 (R n)).toLSCFun,
            (confPullCompact
              (D (addFun (J n (H n ω, mark n ω)).2.1
                (cutF (V n) (m n) (J n (H n ω, mark n ω)).2.2.1)))
              (ψ n '' closedBall 0 (R n)) (closedBall 0 (R n))
              (isCompact_closedBall _ _)
              ((isCompact_closedBall _ _).image_of_continuousOn
                ((hψ n).1.continuousOn.mono
                  ((closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2)))
              (imageMapK (ψ n) _
                ((hψ n).1.continuousOn.mono
                  ((closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2)))
              (imageMapK_injective _ ((hψ n).2.injOn.mono
                ((closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2)))).toLSCFun) ∂P)
          atTop (𝓝 (∫ ω, F (pairJ ⊤ (H 0 ω),
            (D (H 0 ω)).toLSCFun, (D (H 0 ω)).toLSCFun) ∂P)) := by
  classical
  let Pstar := commonFixedMeasure P H mark μ y₀
  haveI : IsProbabilityMeasure Pstar := by dsimp [Pstar, commonFixedMeasure]; infer_instance
  let hstar : (ℕ → DistC × Y) → DistC := fun path => (path 0).1
  let pairStar : ℕ → (ℕ → DistC × Y) → DistC × Y :=
    fun n path => (hstar path, (path (n+1)).2)
  let Jstar : ∀ n, (ℕ → DistC × Y) → SupercriticalConformalCovariance.Transport.RealizationData (V n) :=
    fun n path => J n (pairStar n path)
  have hrealstar : ∀ n, IsDomainRealization (V n) Pstar
      (fun path => confPullbackField Q (isConformalBijection_invFunOn (hψ n))
        (restrictTo (U n) (hstar path)))
      (fun path => (Jstar n path).2.1)
      (fun path => (Jstar n path).2.2.1) := by
    intro n
    have ht := commonFixedMeasure_realization P H mark μ y₀ n (hHm n) (hmarkm n)
      (hlaw n) (V n) (J n) (hJ n) (hreal n) (hwpJ n)
    convert ht using 1
    funext path
    exact (hfield n (pairStar n path)).symm
  have hwpstar : IsWholePlaneGFF hstar Pstar :=
    commonFixedMeasure_wholePlaneGFF P H mark μ y₀ hwpH (hlaw 0)
  obtain ⟨m, hm, hDcvg, hEcvg⟩ := tangent_limit_confined_for_prop43 hQ hD hψ
    hexhaust hzero ha0 ha hR hRU Pstar hwpstar
      (fun n path => (Jstar n path).2.1)
      (fun n path => (Jstar n path).2.2.1) hrealstar
  let Dpair (n : ℕ) (p : DistC × Y) : LSCMetric := conf (D p.1) 0 (R n)
  let Epair (n : ℕ) (p : DistC × Y) : LSCMetric :=
    confPullCompact
      (D (addFun (J n p).2.1 (cutF (V n) (m n) (J n p).2.2.1)))
      (ψ n '' closedBall 0 (R n)) (closedBall 0 (R n))
      (isCompact_closedBall _ _)
      ((isCompact_closedBall _ _).image_of_continuousOn
        ((hψ n).1.continuousOn.mono
          ((closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2)))
      (imageMapK (ψ n) _
        ((hψ n).1.continuousOn.mono
          ((closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2)))
      (imageMapK_injective _ ((hψ n).2.injOn.mono
        ((closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2)))
  have hDpair : ∀ n, Measurable (Dpair n) := by
    intro n
    rw [SupercriticalLQGUniqueness.B2.LscTop.measurable_iff_toLSCFun]
    exact (measurable_conf 0 (R n)).comp (hD.1.comp measurable_fst)
  have hEpair : ∀ n, Measurable (Epair n) := by
    intro n
    rw [SupercriticalLQGUniqueness.B2.LscTop.measurable_iff_toLSCFun]
    have hbarM : Measurable fun p : DistC × Y => (J n p).2.1 :=
      (measurable_fst.comp measurable_snd).comp (hJ n)
    have hfrM : Measurable fun p : DistC × Y => (J n p).2.2.1 :=
      ((measurable_fst.comp measurable_snd).comp measurable_snd).comp (hJ n)
    have hF : Measurable fun p : DistC × Y =>
        addFun (J n p).2.1 (cutF (V n) (m n) (J n p).2.2.1) :=
      LQGMetric.measurable_addFun.comp
        (hbarM.prodMk (measurable_cutExt (V n).isOpen
          (SupercriticalConformalCovariance.Domain.tsupport_cutoff_subset (V n : Set ℂ) (m n)) hfrM))
    exact (measurable_confPullCompact _ _ _ _ _ _).comp (hD.1.comp hF)
  have hdc : SubseqLSC Pstar
      (fun n path q => (Dpair n (pairStar n path) q : EReal))
      (fun path q => (D (hstar path) q : EReal)) := by
    simpa only [Dpair, pairStar, hstar, SupercriticalConformalCovariance.Conf.confDisk_eq_small] using hDcvg
  have hec : SubseqLSC Pstar
      (fun n path q => (Epair n (pairStar n path) q : EReal))
      (fun path q => (D (hstar path) q : EReal)) := by
    simpa only [Epair, pairStar, Jstar, hstar] using hEcvg
  refine ⟨m, hm, fun F => ?_⟩
  exact confined_joint_law_varying P H mark (hHm) (hmarkm) μ y₀ hlaw
    Dpair Epair D hDpair hEpair hD.1 hdc hec F

end SupercriticalConformalCovariance.Small
