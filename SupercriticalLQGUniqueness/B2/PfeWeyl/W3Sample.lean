import SupercriticalLQGUniqueness.B2.PfeWeyl.W3WeylMetric
import SupercriticalLQGUniqueness.B2.PfeWeyl.NormalizedLFPP
import SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPLength
import SupercriticalLQGUniqueness.B2.PfeWeyl.Mollification
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteGeometry
import LQGMetric.LFPP.WeylBounds

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem mollCont_fixed_tendsto_compact {ε : ℕ → ℝ} (hε : ∀ n, ε n ≠ 0)
    (hε0 : Tendsto ε atTop (𝓝 0)) (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (K : Set ℂ) (hK : IsCompact K) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ x ∈ K,
      |LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM x - f x| < η := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hunif := mollCont_fixed_tendsto hε hε0 f M hM R hR
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  filter_upwards [hunif η hη] with n hn x hx
  have := hn x (hKR hx)
  rwa [Real.dist_eq, abs_sub_comm] at this

 
theorem abs_mollCont_le {ε : ℝ} (hε : ε ≠ 0) (f : C(ℂ, ℝ)) (M : ℝ)
    (hM : ∀ z, |f z| ≤ M) (z : ℂ) :
    |LQGMetric.LFPP.mollCont ε hε f M hM z| ≤ M :=
  LQGMetric.LFPP.abs_heatMollify_ofCont_le f hM hε z

 

theorem weyl_scaling_sample (ξ : ℝ) (hξ : 0 ≤ ξ)
    (a : ℕ → Set.Ioi (0 : ℝ)) (φ : ℕ → C(ℂ, ℝ)) (D : LSCMetric)
    (hG : Tendsto (fun n => normalizedLFPPMetric ξ (a n) (φ n)) atTop (𝓝 D))
    (hDlen : D.IsLengthSpace) (hDforget : Continuous (euclidForget D))
    (hacross : AcrossUnbounded D)
    (hsmall : ∀ k : ℕ, SmallAnnulusCosts (fun n => normalizedLFPPMetric ξ (a n) (φ n)) D
      (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ≠ 0) (hε0 : Tendsto ε atTop (𝓝 0))
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M) :
    ∃ E : LSCMetric, (∀ p, E p = weylScale ξ f D p) ∧
      Tendsto (fun n => normalizedLFPPMetric ξ (a n)
        (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM)) atTop (𝓝 E) := by
  exact weyl_tendsto_lscMetric hG
    (fun n => isLengthSpace_normalizedLFPPMetric ξ (a n) (φ n))
    (fun n => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric ξ (a n) (φ n))
    ξ hξ f (fun n => LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM)
    (fun K hK η hη => mollCont_fixed_tendsto_compact hε hε0 f M hM K hK η hη)
    M hM (fun n z => abs_mollCont_le (hε n) f M hM z) hDlen hDforget hacross
    (fun n => normalizedLFPPMetric ξ (a n)
      (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM))
    (fun n x y => normalizedLFPPMetric_add_eq_weylScale ξ (a n) (φ n) _ (x, y))
    (fun n => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric ξ (a n) _)
    hsmall

end SupercriticalLQGUniqueness.B2.PfeWeyl
