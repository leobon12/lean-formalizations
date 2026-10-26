import SupercriticalConformalCovariance.Tangent.Final
import SupercriticalConformalCovariance.Conf

/-!
# Lemma 3.3 in the confined metric coordinates used by Proposition 4.3

The cutoff index is chosen from compactness of each transformed disk. Both
metric families use the constructors of the Proposition 4.3 proof. This is the joint convergence
input that proof consumes.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory Metric TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection IsDomainRealization confPullbackField)
open LQGMetric (DistC restrictTo IsWholePlaneGFF IsGFFPlusCont addFun)
open SupercriticalConformalCovariance.Tangent
open SupercriticalConformalCovariance.GM24 (isConformalBijection_invFunOn)
open SupercriticalConformalCovariance.Domain (exW cutF exists_subset_exW)

theorem tangent_limit_confined_for_prop43 {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    (hQ : IsLFPPExponent ξ Q) {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop)
    (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n)) :
    ∃ m : ℕ → ℕ,
      (∀ n, ψ n '' closedBall (0 : ℂ) (R n) ⊆ exW (V n) (m n)) ∧
      SubseqLSC P (fun n ω q => (SupercriticalConformalCovariance.Small.conf (D (h ω)) 0 (R n) q : EReal))
        (fun ω q => (D (h ω) q : EReal)) ∧
      SubseqLSC P (fun n ω q =>
        (SupercriticalConformalCovariance.Small.confPullCompact
          (D (addFun (hbar n ω) (cutF (V n) (m n) (fr n ω))))
          (ψ n '' closedBall 0 (R n)) (closedBall 0 (R n))
          (isCompact_closedBall _ _)
          ((isCompact_closedBall _ _).image_of_continuousOn
            ((hψ n).1.continuousOn.mono
              ((closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2)))
          (imageMapK (ψ n) _
            ((hψ n).1.continuousOn.mono
              ((closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2)))
          (imageMapK_injective _ ((hψ n).2.injOn.mono
              ((closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2))) q : EReal))
        (fun ω q => (D (h ω) q : EReal)) := by
  classical
  have hcl : ∀ n, closedBall (0 : ℂ) (R n) ⊆ (U n : Set ℂ) := fun n =>
    (closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2
  have hc : ∀ n, ContinuousOn (ψ n) (closedBall 0 (R n)) := fun n =>
    (hψ n).1.continuousOn.mono (hcl n)
  have hK : ∀ n, IsCompact (closedBall (0 : ℂ) (R n)) := fun n => isCompact_closedBall _ _
  have hYc : ∀ n, IsCompact (ψ n '' closedBall (0 : ℂ) (R n)) := fun n =>
    (hK n).image_of_continuousOn (hc n)
  have hinj : ∀ n, Function.Injective (imageMapK (ψ n) _ (hc n)) := fun n =>
    imageMapK_injective (hc n) ((hψ n).2.injOn.mono (hcl n))
  have hmex : ∀ n, ∃ m, ψ n '' closedBall (0 : ℂ) (R n) ⊆ exW (V n) m := fun n =>
    exists_subset_exW (V n).isOpen (hYc n) (tangentImage_subset hψ hRU n)
  choose m hm using hmex
  let Dd : ℕ → Ω → LSCMetric := fun n ω => SupercriticalConformalCovariance.Small.conf (D (h ω)) 0 (R n)
  let De : ℕ → Ω → LSCMetric := fun n ω =>
    SupercriticalConformalCovariance.Small.confPullCompact (D (addFun (hbar n ω) (cutF (V n) (m n) (fr n ω))))
      (ψ n '' closedBall 0 (R n)) (closedBall 0 (R n)) (hK n) (hYc n)
      (imageMapK (ψ n) _ (hc n)) (hinj n)
  have hDd : ∀ n, ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ y →
      Dd n ω (x, y) = extInternal (D (h ω)) (closedBall 0 (R n)) (x, y) := by
    intro n
    exact Filter.Eventually.of_forall fun ω x y hxy => by
      rw [show Dd n ω = confDisk (D (h ω)) (R n) from
        (SupercriticalConformalCovariance.Conf.confDisk_eq_small _ _).symm, confDisk_apply, if_neg hxy]
  have hDe : ∀ n, ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ y →
      De n ω (x, y) = tangentEval (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr n ω (x, y) := by
    intro n
    filter_upwards [ae_compactPullFun_eq_tangentEval hD hψ hRU P hbar fr
      (fun k => (hreal k).2.1) n (hc n) (hK n) (hYc n) (m n) (hm n)] with ω hω x y hxy
    have h1 := hω (x, y)
    change SupercriticalConformalCovariance.Small.confPullCompact _ _ _ _ _ _ _ (x, y) = _
    rw [← SupercriticalConformalCovariance.Conf.confPull_eq_small]
    change SupercriticalConformalCovariance.Tangent.extendMetric _ (SupercriticalConformalCovariance.Tangent.pullInner _ _ _ _) (x, y) = _
    rw [extendMetric_pullInner_eq _ _ _ (hK n) (hYc n), if_neg hxy, h1, EReal.toENNReal_coe]
  have hcvg := tangent_limit_conf hQ hD hψ hexhaust hzero ha0 ha hR hRU P hh hbar fr hreal
    Dd De hDd hDe
  refine ⟨m, hm, ?_, ?_⟩
  · exact hcvg.1
  · exact hcvg.2

end SupercriticalConformalCovariance.Small
