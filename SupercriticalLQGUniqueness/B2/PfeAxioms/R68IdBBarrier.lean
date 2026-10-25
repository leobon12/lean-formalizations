import SupercriticalLQGUniqueness.B2.PfeAxioms.S2SampleIdentify
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1Crossing
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1LocalBounds
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3CSqueeze
import SupercriticalLQGUniqueness.B2.PfeLocal.Length

 



















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem lfppDOn_le_of_sub_le {ξ : ℝ} (hξ : 0 ≤ ξ) {φ φ' : ℂ → ℝ} {S : Set ℂ} {δ : ℝ}
    (hδ : ∀ x ∈ S, φ' x - φ x ≤ δ) (z w : ℂ) :
    LQGMetric.LFPP.lfppDOn ξ φ' S z w ≤
      ENNReal.ofReal (Real.exp (ξ * δ)) * LQGMetric.LFPP.lfppDOn ξ φ S z w := by
  unfold LQGMetric.LFPP.lfppDOn
  rw [ENNReal.mul_iInf_of_ne (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top]
  refine iInf_mono fun P => ?_
  rw [LQGMetric.LFPP.lfppLen_eq, LQGMetric.LFPP.lfppLen_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
  have e : LQGMetric.LFPP.lenDens ξ φ' P.1 s =
      LQGMetric.LFPP.lenDens ξ (fun x => φ x + (φ' x - φ x)) P.1 s := by
    simp only [add_sub_cancel]
  rw [e, LQGMetric.LFPP.lenDens_add]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
  exact mul_le_mul_of_nonneg_left (hδ _ (P.2.2 s hs)) hξ

 
theorem internal_le_of_weight_le (ξ : Set.Ioi (0 : ℝ)) (a : Set.Ioi (0 : ℝ))
    (φ ψ : C(ℂ, ℝ)) {V : Set ℂ} (hV : IsOpen V) {θ : ℝ}
    (hθ : ∀ z ∈ V, φ z ≤ ψ z + θ) (u v : V) :
    (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a φ).internal V (u, v) ≤
      ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ)) *
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a ψ).internal V (u, v) := by
  rw [normalizedLFPPMetric_internal_eq_lfppDOn _ _ _ hV,
    normalizedLFPPMetric_internal_eq_lfppDOn _ _ _ hV]
  have h := lfppDOn_le_of_sub_le (ξ := (ξ : ℝ)) (φ := ψ) (φ' := φ) (S := V) (δ := θ)
    ξ.property.le (fun z hz => by linarith [hθ z hz]) u v
  calc ENNReal.ofReal ((a : ℝ)⁻¹) * LQGMetric.LFPP.lfppDOn (ξ : ℝ) φ V u v
      ≤ ENNReal.ofReal ((a : ℝ)⁻¹) *
          (ENNReal.ofReal (Real.exp ((ξ : ℝ) * θ)) *
            LQGMetric.LFPP.lfppDOn (ξ : ℝ) ψ V u v) := by gcongr
    _ = _ := by ring

 

theorem le_acrossDist_weylScale (D E : LSCMetric)
    (hforget : Continuous (PfeWeyl.euclidForget D)) {ξ : ℝ} (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hE : ∀ p, E p = weylScale ξ f D p) (A : EuclideanAnnulus) (c : ℝ)
    (hc : ∀ z, A.innerRadius ≤ dist z A.center → dist z A.center ≤ A.outerRadius → c ≤ f z) :
    ENNReal.ofReal (Real.exp (ξ * c)) * acrossDist D A ≤ acrossDist E A := by
  show _ ≤ ⨅ (x ∈ A.innerBoundary) (y ∈ A.outerBoundary), E (x, y)
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  rw [hE (x, y)]
  unfold weylScale
  refine le_iInf fun P => le_iInf fun L => le_iInf fun hP => le_iInf fun hu =>
    le_iInf fun h0 => le_iInf fun h1 => ?_
  have hPc : ContinuousOn P (Icc 0 L) := hforget.comp_continuousOn hP.2
  have hf : ContinuousOn (fun u => dist (P u) A.center) (Icc 0 L) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  have hx' : dist x A.center = A.innerRadius := hx
  have hy' : dist y A.center = A.outerRadius := hy
  have ha : dist (P 0) A.center ≤ A.innerRadius := by rw [h0]; exact hx'.le
  have hb : A.outerRadius ≤ dist (P L) A.center := by rw [h1]; exact hy'.ge
  obtain ⟨s, t, h0s, hst, htL, hs, ht, hin⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hP.1 hf A.innerRadius_lt_outerRadius.le ha hb
  have hcross : acrossDist D A ≤ D (P s, P t) := by
    unfold acrossDist
    exact iInf_le_of_le (P s) (iInf_le_of_le hs (iInf_le_of_le (P t) (iInf_le_of_le ht le_rfl)))
  have hd : D (P s, P t) ≤ ENNReal.ofReal (t - s) := by
    have hunit := (LQGMetric.MetricGeometry.lipschitzOnWith_of_hasUnitSpeedOn hu)
      ⟨h0s, hst.trans htL⟩ ⟨h0s.trans hst, htL⟩
    change D (P s, P t) ≤ (1 : ℝ≥0∞) * edist s t at hunit
    rwa [one_mul, edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hst)]
      at hunit
  calc ENNReal.ofReal (Real.exp (ξ * c)) * acrossDist D A
      ≤ ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (t - s) :=
        mul_le_mul_of_nonneg_left (hcross.trans hd) zero_le
    _ = ∫⁻ _ in Icc s t, ENNReal.ofReal (Real.exp (ξ * c)) := by
        rw [setLIntegral_const, Real.volume_Icc]
    _ ≤ ∫⁻ u in Icc s t, ENNReal.ofReal (Real.exp (ξ * f (P u))) :=
        setLIntegral_mono' measurableSet_Icc fun u hu' =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left (hc _ (hin u hu').1 (hin u hu').2) hξ))
    _ ≤ ∫⁻ u in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P u))) :=
        lintegral_mono_set (Icc_subset_Icc h0s htL)

 
def barrierBump (R B : ℝ) : C(ℂ, ℝ) :=
  ⟨fun z => B * min 1 (max 0 (2 * (‖z‖ - R) - 1)), by fun_prop⟩

theorem barrierBump_apply (R B : ℝ) (z : ℂ) :
    barrierBump R B z = B * min 1 (max 0 (2 * (‖z‖ - R) - 1)) := rfl

theorem barrierBump_nonneg {R B : ℝ} (hB : 0 ≤ B) (z : ℂ) : 0 ≤ barrierBump R B z := by
  rw [barrierBump_apply]
  exact mul_nonneg hB (le_min zero_le_one (le_max_left _ _))

theorem barrierBump_le {R B : ℝ} (hB : 0 ≤ B) (z : ℂ) : barrierBump R B z ≤ B := by
  rw [barrierBump_apply]
  calc B * min 1 (max 0 (2 * (‖z‖ - R) - 1)) ≤ B * 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hB
    _ = B := mul_one B

theorem barrierBump_eq_zero {R B : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R + 1 / 2) :
    barrierBump R B z = 0 := by
  rw [barrierBump_apply, max_eq_left (by linarith), min_eq_right zero_le_one, mul_zero]

theorem barrierBump_eq {R B : ℝ} {z : ℂ} (hz : R + 1 ≤ ‖z‖) : barrierBump R B z = B := by
  rw [barrierBump_apply, max_eq_right (by linarith), min_eq_left (by linarith), mul_one]

 
theorem exists_barrier_height {ξ : ℝ} (hξ : 0 < ξ) (M : ℝ) {α T : ℝ≥0∞} (hα : 0 < α)
    (hT : T ≠ ⊤) :
    ∃ B : ℝ, 0 ≤ B ∧ T < ENNReal.ofReal (Real.exp (ξ * (B - M))) * α := by
  by_cases hαt : α = ⊤
  · refine ⟨0, le_rfl, ?_⟩
    rw [hαt, ENNReal.mul_top (by simpa using Real.exp_pos _)]
    exact lt_top_iff_ne_top.2 hT
  set q : ℝ := (T / α).toReal + 1 with hq
  have hq0 : 0 < q := by positivity
  refine ⟨max 0 (M + Real.log q / ξ), le_max_left _ _, ?_⟩
  have hexp : q ≤ Real.exp (ξ * (max 0 (M + Real.log q / ξ) - M)) := by
    have h1 : Real.log q ≤ ξ * (max 0 (M + Real.log q / ξ) - M) := by
      have h2 : M + Real.log q / ξ ≤ max 0 (M + Real.log q / ξ) := le_max_right _ _
      have h3 : Real.log q / ξ ≤ max 0 (M + Real.log q / ξ) - M := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hξ.le
      rwa [mul_div_cancel₀ _ hξ.ne'] at h4
    calc q = Real.exp (Real.log q) := (Real.exp_log hq0).symm
      _ ≤ _ := Real.exp_le_exp.2 h1
  have hdiv : T / α ≠ ⊤ := ENNReal.div_ne_top hT hα.ne'
  have hlt : T / α < ENNReal.ofReal (Real.exp (ξ * (max 0 (M + Real.log q / ξ) - M))) := by
    calc T / α = ENNReal.ofReal (T / α).toReal := (ENNReal.ofReal_toReal hdiv).symm
      _ < ENNReal.ofReal q := by
          rw [ENNReal.ofReal_lt_ofReal_iff hq0]
          linarith
      _ ≤ _ := ENNReal.ofReal_le_ofReal hexp
  exact (ENNReal.div_lt_iff (Or.inl hα.ne') (Or.inl hαt)).1 hlt

end SupercriticalLQGUniqueness.B2.PfeAxioms
