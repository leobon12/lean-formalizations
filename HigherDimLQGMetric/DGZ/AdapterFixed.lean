import HigherDimLQGMetric.DGZ.AdapterHolder

/-! Uniform field bounds and metric estimates away from the zero cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}

/-- The supremum of a field with cutoff bounded below is tight uniformly in the cutoff. -/
theorem adapter_fixed_band_sup (hd : 0 < d) (hκ : IsLFPPKernel κ)
    {a₀ R θ : ℝ} (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1)
    (hR : 0 ≤ R) (hθ : 0 < θ) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
        IsWhiteNoise P W → ∀ {a : ℝ}, a₀ ≤ a → a ≤ 1 →
        ∀ {G : Rd d → Ω → ℝ}, IsBandVersion P W κ a 1 G →
          P {ω | ∃ z ∈ cbox (0 : Rd d) R, L < |G z ω|} ≤
            ENNReal.ofReal θ := by
  have hdz : NeZero d := ⟨hd.ne'⟩
  obtain ⟨L₀, hL₀, htail⟩ := @HigherDimLFPP.exists_bandSup_bounds d hdz κ hκ
  let V : ℝ := Real.log (1 / a₀) + 1
  have hV : 0 < V := by
    have hlog : 0 ≤ Real.log (1 / a₀) :=
      Real.log_nonneg ((one_le_div ha₀).2 ha₀1)
    dsimp [V]
    linarith
  let M : ℝ := HigherDimLFPP.SupB.supMean d L₀ V (d * Real.log (2 * R / a₀ + 1))
  let u : ℝ := 2 * Real.sqrt (V / θ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu2 : u ^ 2 = 4 * (V / θ) := by
    dsimp [u]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have htailθ : 2 * Real.exp (-u ^ 2 / (2 * V)) ≤ θ := by
    have hx : 0 < u ^ 2 / (2 * V) := by rw [hu2]; positivity
    have he : Real.exp (-(u ^ 2 / (2 * V))) ≤ 1 / (u ^ 2 / (2 * V)) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hx (by linarith [Real.add_one_le_exp (u ^ 2 / (2 * V))])
    calc
      2 * Real.exp (-u ^ 2 / (2 * V)) ≤ 2 * (1 / (u ^ 2 / (2 * V))) := by
        simpa only [neg_div] using mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)
      _ = θ := by rw [hu2]; field_simp; ring
  refine ⟨max 0 (M + u), le_max_left _ _, ?_⟩
  intro Ω _ P W hW a ha₀a ha1 G hG
  have ha : 0 < a := ha₀.trans_le ha₀a
  have hVbound : Real.log (1 / a) ≤ V := by
    have hfrac : 1 / a ≤ 1 / a₀ := one_div_le_one_div_of_le ha₀ ha₀a
    have hlog := Real.log_le_log (by positivity : 0 < 1 / a) hfrac
    dsimp [V]
    linarith
  have hℓ : d * Real.log (2 * R / a + 1) ≤
      d * Real.log (2 * R / a₀ + 1) := by
    have hfrac : 2 * R / a ≤ 2 * R / a₀ := by
      apply (div_le_div_iff₀ ha ha₀).2
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * R) (sub_nonneg.2 ha₀a)]
    have hlog : Real.log (2 * R / a + 1) ≤ Real.log (2 * R / a₀ + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
  have h := (htail hW ha ha1 hG hV (by simpa only [one_div] using hVbound)
    0 hR).2.2.2 hu
  have hsub : {ω | ∃ z ∈ cbox (0 : Rd d) R,
      max 0 (M + u) < |G z ω|} ⊆
      {ω | ∃ z ∈ HigherDimLFPP.Osc.box (0 : Rd d) R,
        HigherDimLFPP.SupB.supMean d L₀ V
          (d * Real.log (2 * R / a + 1)) + u < |G z ω|} := by
    rintro ω ⟨z, hz, hzt⟩
    refine ⟨z, hz, lt_of_le_of_lt ?_ hzt⟩
    calc
      _ ≤ M + u := by
        dsimp [M]
        gcongr
        exact HigherDimLFPP.SupB.supMean_mono d le_rfl hℓ
      _ ≤ max 0 (M + u) := le_max_right _ _
  exact (measure_mono hsub).trans (h.trans (ENNReal.ofReal_le_ofReal htailθ))

/-- A bounded Euclidean distance is at most a fixed multiple of its `β` power. -/
private theorem adapter_norm_le_power {R β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {x y : Rd d} (hx : x ∈ Metric.closedBall (0 : Rd d) R)
    (hy : y ∈ Metric.closedBall (0 : Rd d) R) :
    ‖x - y‖ ≤ max 1 (2 * R) * ‖x - y‖ ^ β := by
  have hxn : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hyn : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hdist : ‖x - y‖ ≤ 2 * R := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ 2 * R := by linarith
  by_cases ht : ‖x - y‖ ≤ 1
  · have hh := Real.self_le_rpow_of_le_one (norm_nonneg (x - y)) ht hβ1
    exact hh.trans (le_mul_of_one_le_left (Real.rpow_nonneg (norm_nonneg _) _) (le_max_left _ _))
  · have ht1 : 1 ≤ ‖x - y‖ := le_of_not_ge ht
    have hpow : 1 ≤ ‖x - y‖ ^ β := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le ht1 hβ0.le
    calc
      ‖x - y‖ ≤ max 1 (2 * R) := hdist.trans (le_max_right _ _)
      _ ≤ max 1 (2 * R) * ‖x - y‖ ^ β :=
        le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _)) hpow

/-- On a fixed box field-supremum event, the unit-point distance is bounded below and all
distances inside the smaller Euclidean ball satisfy a deterministic Hölder estimate. -/
theorem adapter_fixed_good_metric {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {G : ℝ → Rd d → Ω → ℝ}
    {ε R β L : ℝ} (hd : 0 < d) (hξ : 0 < ξ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hR : 0 < R)
    (hG : IsBandVersion P W κ ε 1 (G ε)) (ω : Ω)
    (hgood : ¬ ∃ z ∈ cbox (0 : Rd d) (R + 2), L < |G ε z ω|) :
    Real.exp (-(ξ * L)) ≤ lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) ∧
      ∀ x ∈ Metric.closedBall (0 : Rd d) R,
        ∀ y ∈ Metric.closedBall (0 : Rd d) R,
          lfppMetric ξ (fun z => G ε z ω) x y ≤
            Real.exp (ξ * L) * max 1 (2 * R) * ‖x - y‖ ^ β := by
  have hfield : ∀ z ∈ cbox (0 : Rd d) (R + 2), |G ε z ω| ≤ L := by
    intro z hz
    exact le_of_not_gt (fun ht => hgood ⟨z, hz, ht⟩)
  constructor
  · have h0 : (0 : Rd d) ∈ cbox (0 : Rd d) 0 := by
      intro i
      simp only [PiLp.zero_apply, sub_self, abs_zero]
      exact le_rfl
    have he : e₁ d ∉ obox (0 : Rd d) 1 := by
      intro he
      have hh := he ⟨0, hd⟩
      simp [PiLp.zero_apply, e₁_ofLp] at hh
    have hshell : ∀ z ∈ cbox (0 : Rd d) 1 \ obox 0 0,
        -(ξ * L) ≤ ξ * G ε z ω := by
      intro z hz
      have hzS : z ∈ cbox (0 : Rd d) (R + 2) :=
        fun i => (hz.1 i).trans (by linarith)
      have hf := hfield z hzS
      have hlow := neg_abs_le (G ε z ω)
      nlinarith [mul_nonneg (sub_nonneg.2 (by linarith : 0 ≤ G ε z ω + L)) hξ.le]
    have hcross := exp_mul_le_acrossDist hd (hG.continuous ω)
      (c := (0 : Rd d)) (r₁ := 1) (r₂ := 0) (by norm_num) (by norm_num) hshell
    have hle := acrossDist_le_lfppMetric_of_mem (ξ := ξ) (hG.continuous ω)
      (c := (0 : Rd d)) (r₁ := 1) (r₂ := 0) (by norm_num) h0 he
    simpa only [sub_zero, mul_one] using hcross.trans hle
  · intro x hx y hy
    have hxU : x ∈ obox (0 : Rd d) (R + 1) :=
      adapter_closedBall_subset_obox (by linarith : R < R + 1) hx
    have hyU : y ∈ obox (0 : Rd d) (R + 1) :=
      adapter_closedBall_subset_obox (by linarith : R < R + 1) hy
    have hM : ∀ z ∈ obox (0 : Rd d) (R + 1), ξ * G ε z ω ≤ ξ * L := by
      intro z hz
      have hzS : z ∈ cbox (0 : Rd d) (R + 2) :=
        fun i => (HigherDimLFPP.DGZ.obox_subset_cbox 0 (R + 1) hz i).trans (by linarith)
      have hf := hfield z hzS
      have hh := le_abs_self (G ε z ω)
      nlinarith [mul_nonneg (sub_nonneg.2 (by linarith : 0 ≤ L - G ε z ω)) hξ.le]
    have hbound := lfppDistOn_le_exp_mul_norm_of_convex (hG.continuous ω)
      (HigherDimLFPP.DGZ.convex_obox 0 (R + 1)) hxU hyU hM
    have hjoin : PcwJoined (obox (0 : Rd d) (R + 1)) x y :=
      PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 (R + 1)) hxU hyU
    calc
      lfppMetric ξ (fun z => G ε z ω) x y
          ≤ lfppDistOn ξ (fun z => G ε z ω) (obox 0 (R + 1)) x y :=
            lfppMetric_le_lfppDistOn hjoin
      _ ≤ Real.exp (ξ * L) * ‖y - x‖ := hbound
      _ ≤ Real.exp (ξ * L) * (max 1 (2 * R) * ‖x - y‖ ^ β) := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_left (adapter_norm_le_power hβ0 hβ1 hx hy)
          (Real.exp_pos _).le
      _ = _ := by ring

/-- Hölder tightness on a compact range of real cutoffs. -/
theorem adapter_holder_fixed (h : DGZHyp d κ ξ Q)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {G : ℝ → Rd d → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (G ε))
    {a₀ R θ : ℝ} (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1)
    (hR : 0 < R) (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ ε ∈ Ico a₀ 1,
      P {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) R,
        ∃ y ∈ Metric.closedBall (0 : Rd d) R,
          M * aHat P G ξ ε * ‖x - y‖ ^ β <
            lfppMetric ξ (fun z => G ε z ω) x y} ≤ ENNReal.ofReal θ := by
  have hd : 0 < d := by have hh := h.dim; omega
  have hθ' : 0 < min θ (1 / 4) := lt_min hθ (by norm_num)
  obtain ⟨L, hL, hbad⟩ := adapter_fixed_band_sup hd h.kernel ha₀ ha₀1
    (R := R + 2) (θ := min θ (1 / 4)) (by linarith) hθ'
  let t : ℝ := Real.exp (-(ξ * L)) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  let M : ℝ := Real.exp (ξ * L) * max 1 (2 * R) / t
  refine ⟨M, ?_⟩
  intro ε hε
  have hε0 : 0 < ε := ha₀.trans_le hε.1
  have hGε := hG ε ⟨hε0, hε.2⟩
  have hP := hW.isProbabilityMeasure
  have hbadε : P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 2), L < |G ε z ω|} ≤
      ENNReal.ofReal (min θ (1 / 4)) := hbad hW hε.1 hε.2.le hGε
  let X : Ω → ℝ := fun ω => lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d)
  have hX : AEMeasurable X P :=
    (measurable_lfppMetric hGε.continuous hGε.measurable ξ 0 (e₁ d)).aemeasurable
  have hlow : t < aHat P G ξ ε := by
    have hsub : {ω | X ω ≤ t} ⊆
        {ω | ∃ z ∈ cbox (0 : Rd d) (R + 2), L < |G ε z ω|} := by
      intro ω hω
      by_contra hg
      have hh := (adapter_fixed_good_metric hd h.xi_pos hβ0 hβ1 hR hGε ω hg).1
      have htlt : t < Real.exp (-(ξ * L)) := by dsimp [t]; linarith [Real.exp_pos (-(ξ * L))]
      exact (not_le_of_gt (htlt.trans_le hh)) hω
    have hmeasure : P {ω | X ω ≤ t} < (2⁻¹ : ℝ≥0∞) := by
      calc
        P {ω | X ω ≤ t} ≤
            P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 2), L < |G ε z ω|} :=
          measure_mono hsub
        _ ≤ ENNReal.ofReal (min θ (1 / 4)) := hbadε
        _ ≤ (4⁻¹ : ℝ≥0∞) := by
          have hquart : ENNReal.ofReal (1 / 4 : ℝ) = (4⁻¹ : ℝ≥0∞) := by
            simp only [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
              ENNReal.ofReal_ofNat]
          exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans_eq hquart
        _ < 2⁻¹ := by norm_num
    exact adapter_lt_lowerMedian_of_measure_lt hX hmeasure
  have hsub : {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) R,
      ∃ y ∈ Metric.closedBall (0 : Rd d) R,
        M * aHat P G ξ ε * ‖x - y‖ ^ β <
          lfppMetric ξ (fun z => G ε z ω) x y} ⊆
      {ω | ∃ z ∈ cbox (0 : Rd d) (R + 2), L < |G ε z ω|} := by
    intro ω hω
    by_contra hg
    obtain ⟨x, hx, y, hy, hxy⟩ := hω
    have hupper := (adapter_fixed_good_metric hd h.xi_pos hβ0 hβ1 hR hGε ω hg).2
      x hx y hy
    have hcoef : Real.exp (ξ * L) * max 1 (2 * R) ≤ M * aHat P G ξ ε := by
      have hh : t ≤ aHat P G ξ ε := hlow.le
      have hc : 0 ≤ Real.exp (ξ * L) * max 1 (2 * R) := by positivity
      dsimp [M]
      calc
        Real.exp (ξ * L) * max 1 (2 * R)
            = (Real.exp (ξ * L) * max 1 (2 * R) / t) * t := by field_simp
        _ ≤ (Real.exp (ξ * L) * max 1 (2 * R) / t) * aHat P G ξ ε :=
          mul_le_mul_of_nonneg_left hh (div_nonneg hc ht.le)
    have hle : Real.exp (ξ * L) * max 1 (2 * R) * ‖x - y‖ ^ β ≤
        M * aHat P G ξ ε * ‖x - y‖ ^ β :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg _) _)
    exact (not_le_of_gt hxy) (hupper.trans hle)
  exact (measure_mono hsub).trans
    (hbadε.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))

/-- The first clause of `RealEpsAdapterShape`, uniformly for every `0 < ε < 1/2`. -/
theorem adapter_holder_real (h : DGZHyp d κ ξ Q)
    (hHolder : HolderTightShape d κ ξ Q) (hNondeg : NondegShape d κ ξ Q)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {G : ℝ → Rd d → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (G ε))
    (R θ : ℝ) (hR : 0 < R) (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹,
      P {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) R,
        ∃ y ∈ Metric.closedBall (0 : Rd d) R,
          M * aHat P G ξ ε * ‖x - y‖ ^ β <
            lfppMetric ξ (fun z => G ε z ω) x y} ≤ ENNReal.ofReal θ := by
  have hd : 0 < d := by have hh := h.dim; omega
  have hβ1 : β ≤ 1 := (hβ.trans_le (xi_mul_sub_sqrt_le_one h)).le
  obtain ⟨M₁, ε₀, hε₀, hε₀1, hsmall⟩ :=
    adapter_holder_small h hHolder hNondeg hβ0 hβ hW hG R θ hR hθ
  obtain ⟨M₂, hfixed⟩ := adapter_holder_fixed h hβ0 hβ1 hW hG
    hε₀ hε₀1 hR hθ
  refine ⟨max M₁ M₂, ?_⟩
  intro ε hε
  have hGε := hG ε ⟨hε.1, hε.2.trans (by norm_num : (2⁻¹ : ℝ) < 1)⟩
  have hmed0 : 0 ≤ aHat P G ξ ε := (aHat_pos hd hW hGε ξ).le
  have hsub : ∀ {m m' : ℝ}, m ≤ m' →
      {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) R,
        ∃ y ∈ Metric.closedBall (0 : Rd d) R,
          m' * aHat P G ξ ε * ‖x - y‖ ^ β <
            lfppMetric ξ (fun z => G ε z ω) x y} ⊆
      {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) R,
        ∃ y ∈ Metric.closedBall (0 : Rd d) R,
          m * aHat P G ξ ε * ‖x - y‖ ^ β <
            lfppMetric ξ (fun z => G ε z ω) x y} := by
    intro m m' hmm ω hω
    obtain ⟨x, hx, y, hy, hxy⟩ := hω
    refine ⟨x, hx, y, hy, lt_of_le_of_lt ?_ hxy⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmm hmed0)
      (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hεsmall : ε < ε₀
  · exact (measure_mono (hsub (le_max_left _ _))).trans
      (hsmall ε ⟨hε.1, hεsmall⟩)
  · have hεfixed : ε ∈ Ico ε₀ 1 :=
      ⟨le_of_not_gt hεsmall, hε.2.trans (by norm_num : (2⁻¹ : ℝ) < 1)⟩
    exact (measure_mono (hsub (le_max_right _ _))).trans (hfixed ε hεfixed)

end HigherDimLQGMetric.DGZ
