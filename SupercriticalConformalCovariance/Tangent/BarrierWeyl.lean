import SupercriticalConformalCovariance.Tangent.BarrierDet
import SupercriticalConformalCovariance.Tangent.LocalFunctional
import SupercriticalConformalCovariance.Domain.Sample
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylBridge
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.Localize
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection

/-!
# Lemma 3.3, step 6: the barrier event, Weyl stability and locality

* `aroundDist_weyl_le`, `le_aroundDist_weyl`, `acrossDist_weyl_le`, `le_acrossDist_weyl`:
  around and across distances under a globally bounded Weyl shift `m ≤ g ≤ M`.
* `around_lt_across_of_weyl`: the margin event `around(A) < θ · across(B)` for `D` gives the strict
  barrier `around(A) < across(B)` for `E = e^{ξ g} · D` when `θ e^{ξ(M − m)} ≤ 1`.
* `isPathwiseLocal_margin`: the margin event is a pathwise local observable of the field on any
  open `W` containing `A` and the closed disk of `B` (Axiom II plus SLU's locality of `around`
  (`aroundDist_eq_of_internal_eq`) and of `across` (`setDist_transfer`, first-visit truncation)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open SupercriticalLQGUniqueness (LSCMetric EuclideanAnnulus aroundDist acrossDist weylScale
  IsStrongLQGMetric)
open LQGMetric (DistC IsGFFPlusCont)
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift (length_bounds distance_lower
  distance_upper curve_forward curve_back)

variable (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (g : C(ℂ, ℝ)) (m M : ℝ)
  (hforget : Continuous (SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget D))
  (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p) (hg : ∀ x : ℂ, m ≤ g x ∧ g x ≤ M)

include hξ hforget hWeyl hg in
theorem aroundDist_weyl_le (hL : D.IsLengthSpace) (A : EuclideanAnnulus) :
    aroundDist E A ≤ ENNReal.ofReal (Real.exp (ξ * M)) * aroundDist D A := by
  have hc0 : ENNReal.ofReal (Real.exp (ξ * M)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  unfold aroundDist
  simp only [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP => le_iInf fun hA =>
    le_iInf fun hsep => ?_
  have hPE := curve_forward D E ξ hξ g m M hforget hWeyl hg hL hP
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hPE <|
    iInf_le_of_le hA <| iInf_le_of_le hsep (length_bounds D E ξ hξ g m M hforget hWeyl hg hP).2

include hξ hforget hWeyl hg in
theorem le_aroundDist_weyl (A : EuclideanAnnulus) :
    ENNReal.ofReal (Real.exp (ξ * m)) * aroundDist D A ≤ aroundDist E A := by
  have hc0 : ENNReal.ofReal (Real.exp (ξ * m)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  unfold aroundDist
  simp only [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP => le_iInf fun hA =>
    le_iInf fun hsep => ?_
  have hPD := curve_back D E ξ hξ g m hforget hWeyl (fun x => (hg x).1) hP
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hPD <|
    iInf_le_of_le hA <| iInf_le_of_le hsep (length_bounds D E ξ hξ g m M hforget hWeyl hg hPD).1

include hξ hforget hWeyl hg in
theorem acrossDist_weyl_le (hL : D.IsLengthSpace) (B : EuclideanAnnulus) :
    acrossDist E B ≤ ENNReal.ofReal (Real.exp (ξ * M)) * acrossDist D B := by
  have hc0 : ENNReal.ofReal (Real.exp (ξ * M)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  unfold acrossDist
  simp only [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  exact iInf₂_mono fun x _ => iInf₂_mono fun y _ =>
    distance_upper D E ξ hξ g m M hforget hWeyl hg hL x y

include hξ hforget hWeyl hg in
theorem le_acrossDist_weyl (B : EuclideanAnnulus) :
    ENNReal.ofReal (Real.exp (ξ * m)) * acrossDist D B ≤ acrossDist E B := by
  have hc0 : ENNReal.ofReal (Real.exp (ξ * m)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  unfold acrossDist
  simp only [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  exact iInf₂_mono fun x _ => iInf₂_mono fun y _ =>
    distance_lower D E ξ g m hforget hWeyl (fun x => (hg x).1) hξ x y

include hξ hforget hWeyl hg in
/-- **Weyl stability of the barrier with a margin.** -/
theorem around_lt_across_of_weyl (hL : D.IsLengthSpace) (A B : EuclideanAnnulus) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ * Real.exp (ξ * (M - m)) ≤ 1)
    (hlt : aroundDist D A < ENNReal.ofReal θ * acrossDist D B) :
    aroundDist E A < acrossDist E B := by
  set eM := ENNReal.ofReal (Real.exp (ξ * M)) with heM
  set em := ENNReal.ofReal (Real.exp (ξ * m)) with hem
  have heM0 : eM ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hem0 : em ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have h1 := aroundDist_weyl_le D E ξ hξ g m M hforget hWeyl hg hL A
  have h2 := le_acrossDist_weyl D E ξ hξ g m M hforget hWeyl hg B
  -- `eM * θ ≤ em`
  have hfac : eM * ENNReal.ofReal θ ≤ em := by
    rw [heM, hem, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : Real.exp (ξ * M) * θ = Real.exp (ξ * m) * (θ * Real.exp (ξ * (M - m))) := by
      rw [mul_sub, Real.exp_sub]
      field_simp
    rw [this]
    calc Real.exp (ξ * m) * (θ * Real.exp (ξ * (M - m))) ≤ Real.exp (ξ * m) * 1 := by
          gcongr
      _ = Real.exp (ξ * m) := mul_one _
  calc aroundDist E A ≤ eM * aroundDist D A := h1
    _ < eM * (ENNReal.ofReal θ * acrossDist D B) := by
        rw [mul_comm eM, mul_comm eM]
        exact ENNReal.mul_lt_mul_left heM0 ENNReal.ofReal_ne_top hlt
    _ = (eM * ENNReal.ofReal θ) * acrossDist D B := (mul_assoc _ _ _).symm
    _ ≤ em * acrossDist D B := by gcongr
    _ ≤ acrossDist E B := h2

/-- The margin event, as a `Bool`-valued observable of the field. -/
def marginEvent (D : DistC → LSCMetric) (A B : EuclideanAnnulus) (θ : ℝ) (g : DistC) : Bool :=
  open Classical in decide (aroundDist (D g) A < ENNReal.ofReal θ * acrossDist (D g) B)

theorem marginEvent_eq_true {D : DistC → LSCMetric} {A B : EuclideanAnnulus} {θ : ℝ} {g : DistC} :
    marginEvent D A B θ g = true ↔ aroundDist (D g) A < ENNReal.ofReal θ * acrossDist (D g) B := by
  unfold marginEvent
  exact decide_eq_true_iff

theorem measurable_marginEvent {D : DistC → LSCMetric} (hDm : Measurable D) (A B : EuclideanAnnulus)
    (θ : ℝ) : Measurable (marginEvent D A B θ) := by
  have hset : MeasurableSet {g : DistC | aroundDist (D g) A < ENNReal.ofReal θ * acrossDist (D g) B} :=
    measurableSet_lt ((SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.measurable_aroundDist_fixed
      A).comp hDm) (((SupercriticalLQGUniqueness.measurable_acrossDist B).comp hDm).const_mul _)
  refine measurable_to_countable' fun b => ?_
  cases b
  · have : marginEvent D A B θ ⁻¹' {false} = {g | aroundDist (D g) A <
        ENNReal.ofReal θ * acrossDist (D g) B}ᶜ := by
      ext g
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_ofPred_eq]
      rw [← marginEvent_eq_true, Bool.not_eq_true]
    rw [this]; exact hset.compl
  · have : marginEvent D A B θ ⁻¹' {true} = {g | aroundDist (D g) A <
        ENNReal.ofReal θ * acrossDist (D g) B} := by
      ext g
      simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
      exact marginEvent_eq_true
    rw [this]; exact hset

/-- `around` and `across` agree for two metrics with the same internal metric on an open `W`
containing `A` and the closed disk of `B`, when both are length spaces with Euclidean-continuous
curves. -/
theorem around_across_eq_of_internal_eq {D₁ D₂ : LSCMetric}
    (hf₁ : Continuous (SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget D₁))
    (hf₂ : Continuous (SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget D₂))
    (hL₁ : D₁.IsLengthSpace) (hL₂ : D₂.IsLengthSpace) {W : Set ℂ}
    (hint : D₁.internal W = D₂.internal W) (A B : EuclideanAnnulus) (hA : A.toSet ⊆ W)
    (hB : closedBall B.center B.outerRadius ⊆ W) :
    aroundDist D₁ A = aroundDist D₂ A ∧ acrossDist D₁ B = acrossDist D₂ B := by
  refine ⟨SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq
    D₁ D₂ W hint A hA, ?_⟩
  have hB0 : 0 < B.outerRadius := B.2.1.trans B.2.2
  have hcl : closure (ball B.center B.outerRadius) ⊆
      ball B.center B.outerRadius ∪ sphere B.center B.outerRadius := by
    rw [closure_ball _ hB0.ne']
    intro z hz
    rcases eq_or_lt_of_le (mem_closedBall.1 hz) with h | h
    · exact Or.inr (mem_sphere.2 h)
    · exact Or.inl (mem_ball.2 h)
  have hVSU : ball B.center B.outerRadius ∪ sphere B.center B.outerRadius ⊆ W := by
    rintro z (hz | hz)
    · exact hB (ball_subset_closedBall hz)
    · exact hB (sphere_subset_closedBall hz)
  have hMV : B.innerBoundary ⊆ ball B.center B.outerRadius := fun z hz => by
    have := mem_sphere.1 hz
    exact mem_ball.2 (by rw [this]; exact B.2.2)
  exact SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.setDist_transfer
    (fun γ a b hγ => hf₁.comp_continuousOn hγ.2) (fun γ a b hγ => hf₂.comp_continuousOn hγ.2)
    hL₁ hL₂ isOpen_ball hcl isClosed_sphere hVSU hMV
    (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.intExt_eq_of_internal_eq hint)

/-- **Pathwise locality of the margin event.** -/
theorem isPathwiseLocal_margin {ξ' : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ' Q D) (W : TopologicalSpace.Opens ℂ) (A B : EuclideanAnnulus)
    (hA : A.toSet ⊆ W) (hB : closedBall B.center B.outerRadius ⊆ W) (θ : ℝ) :
    IsPathwiseLocal W (marginEvent D A B θ) := by
  intro Ω _ P _ g₁ g₂ h₁ h₂ hU
  filter_upwards [SupercriticalConformalCovariance.Domain.ae_internal_eq_of_ae_restrictTo_eq_lsc hD h₁ h₂ W hU,
    SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P g₁ h₁,
    SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P g₂ h₂] with ω hint s₁ s₂
  obtain ⟨ha, hc⟩ := around_across_eq_of_internal_eq s₁.1 s₂.1 s₁.2.1 s₂.2.1 hint A B hA hB
  unfold marginEvent
  rw [ha, hc]

end SupercriticalConformalCovariance.Tangent
