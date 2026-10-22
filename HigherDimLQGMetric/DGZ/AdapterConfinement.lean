import HigherDimLQGMetric.DGZ.AdapterConfinementTools
import HigherDimLQGMetric.DGZ.TightDistInf
import HigherDimLQGMetric.DGZ.CompareCor52

/-! The confinement clause of the real-cutoff adapter. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}

/-- The Euclidean confinement clause of `RealEpsAdapterShape`. -/
theorem adapter_confinement_real (h : DGZHyp d κ ξ Q)
    (hHolder : HolderTightShape d κ ξ Q) (hNondeg : NondegShape d κ ξ Q)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {G : ℝ → Rd d → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (G ε))
    (r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ) :
    ∃ R : ℝ, r < R ∧ ∃ ε₀ > 0, ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      P {ω | lfppSetDist ξ (fun z => G ε z ω) univ
          (Metric.sphere 0 r) (Metric.sphere 0 R) ≤
        ⨆ p : Metric.ball (0 : Rd d) r × Metric.ball (0 : Rd d) r,
          lfppMetric ξ (fun z => G ε z ω) p.1 p.2} ≤ ENNReal.ofReal θ := by
  have hd : 0 < d := by have hh := h.dim; omega
  obtain ⟨M₀, hholder⟩ := adapter_holder_real h hHolder hNondeg hβ0 hβ
    hW hG r (θ / 2) hr (by positivity)
  let M : ℝ := max 1 M₀
  have hM : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  obtain ⟨L₀, hL₀, M₁, hM₁, δ₀, hδ₀, N₀, hmed⟩ :=
    adapter_median_bounds_coupled h hHolder hNondeg hβ0 hβ
  let C : ℝ := Real.exp (ξ * L₀) * M₁ * (2 : ℝ) ^ β
  have hC : 0 < C := by
    dsimp [C]
    have : 0 < M₁ := by linarith
    positivity
  let T : ℝ := M * C * (2 * r) ^ β
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨q₂, hq₂0, hq₂1, hpert⟩ := distInf_aq_pert (cor52Shape d κ ξ Q) h
  let q : ℝ≥0∞ := max q₂ 2⁻¹
  have hq₂q : q₂ ≤ q := le_max_left _ _
  have hqhalf : (2⁻¹ : ℝ≥0∞) ≤ q := le_max_right _ _
  have hq1 : q < 1 := max_lt hq₂1 (by norm_num)
  have hq0 : 0 < q := hq₂0.trans_le hq₂q
  obtain ⟨R', hR', hpertR⟩ := hpert q hq₂q hq1 (2 * r) (2 * T) (θ / 2)
    (by linarith) (by positivity)
  let R : ℝ := (Real.sqrt d + 1) * R'
  have hR : r < R := by
    have hR'0 : 0 < R' := by linarith
    have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    dsimp [R]
    nlinarith [mul_nonneg hsqrt hR'0.le]
  let ε₀ : ℝ := min ((2 : ℝ)⁻¹ ^ N₀) (1 / 4)
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by norm_num)
  refine ⟨R, hR, ε₀, hε₀, ?_⟩
  intro ε hε
  have hεhalf : ε < (2⁻¹ : ℝ) :=
    hε.2.trans_le ((min_le_right _ _).trans (by norm_num : (1 / 4 : ℝ) ≤ 2⁻¹))
  have hε1 : ε < 1 := hεhalf.trans (by norm_num)
  obtain ⟨N, s, hs, hs1, hεeq⟩ := adapter_exists_dyadic_scale hε.1 hε1.le
  have hs0 : 0 < s := by linarith
  have hN : N₀ ≤ N := adapter_index_ge_of_eps_lt hs hεeq
    (hε.2.trans_le (min_le_left _ _))
  obtain ⟨H, hH, B, hB, heq⟩ := adapter_realScale_coupling h.kernel hW hε.1
    (hG ε ⟨hε.1, hε1⟩) N hs0 hs1 hεeq
  have hb1 : 1 ≤ 1 / s := (one_le_div hs0).2 hs1
  have hb2 : 1 / s ≤ 2 := (div_le_iff₀ hs0).2 (by linarith)
  have hmedup : aHat P G ξ ε ≤ C * aQ P H ξ N 2⁻¹ :=
    (hmed hW (hG ε ⟨hε.1, hε1⟩) hH hB hs hs1 hN heq).2
  have haQ : 0 ≤ aQ P H ξ N 2⁻¹ := by
    unfold aQ
    exact ((hH.band N).lowerQuantile_lfppDistance_pos hd hH.whiteNoise ξ
      (by norm_num) (by norm_num)).le
  have hqmono : aQ P H ξ N 2⁻¹ ≤ aQ P H ξ N q :=
    tight_aQ_mono hH ξ N (by norm_num) hqhalf hq1
  have haqpos : 0 < aQ P H ξ N q :=
    tight_aQ_pos hd hH ξ N hq0 hq1
  have hholderBad : P {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) r,
      ∃ y ∈ Metric.closedBall (0 : Rd d) r,
        M₀ * aHat P G ξ ε * ‖x - y‖ ^ β <
          lfppMetric ξ (fun z => G ε z ω) x y} ≤ ENNReal.ofReal (θ / 2) :=
    hholder ε ⟨hε.1, hεhalf⟩
  have hpertBad : P {ω | acrossDist ξ (fun z => H N z ω + B z ω)
      0 R' (2 * r) ≤ 2 * T * aQ P H ξ N q} ≤ ENNReal.ofReal (θ / 2) :=
    hpertR Ω P _ H hH (1 / s) hb1 hb2 B hB N
  have hsub : {ω | lfppSetDist ξ (fun z => G ε z ω) univ
      (Metric.sphere 0 r) (Metric.sphere 0 R) ≤
        ⨆ p : Metric.ball (0 : Rd d) r × Metric.ball (0 : Rd d) r,
          lfppMetric ξ (fun z => G ε z ω) p.1 p.2} ⊆
      {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) r,
        ∃ y ∈ Metric.closedBall (0 : Rd d) r,
          M₀ * aHat P G ξ ε * ‖x - y‖ ^ β <
            lfppMetric ξ (fun z => G ε z ω) x y} ∪
      {ω | acrossDist ξ (fun z => H N z ω + B z ω)
        0 R' (2 * r) ≤ 2 * T * aQ P H ξ N q} := by
    intro ω hω
    by_cases hHg : ∃ x ∈ Metric.closedBall (0 : Rd d) r,
        ∃ y ∈ Metric.closedBall (0 : Rd d) r,
          M₀ * aHat P G ξ ε * ‖x - y‖ ^ β <
            lfppMetric ξ (fun z => G ε z ω) x y
    · exact Or.inl hHg
    · right
      by_contra hCg
      have hholderGood : ∀ x ∈ Metric.closedBall (0 : Rd d) r,
          ∀ y ∈ Metric.closedBall (0 : Rd d) r,
            lfppMetric ξ (fun z => G ε z ω) x y ≤
              M * aHat P G ξ ε * ‖x - y‖ ^ β := by
        intro x hx y hy
        have hmedpos : 0 ≤ aHat P G ξ ε :=
          (aHat_pos hd hW (hG ε ⟨hε.1, hε1⟩) ξ).le
        have hh := le_of_not_gt (fun ht => hHg ⟨x, hx, y, hy, ht⟩)
        exact hh.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right 1 M₀) hmedpos)
          (Real.rpow_nonneg (norm_nonneg _) _))
      have hdiam : (⨆ p : Metric.ball (0 : Rd d) r × Metric.ball (0 : Rd d) r,
          lfppMetric ξ (fun z => G ε z ω) p.1 p.2) ≤ T * aQ P H ξ N q := by
        have hh := adapter_ball_diam_le hβ0.le hr hM.le hC.le haQ
          hmedup ω hholderGood
        exact hh.trans (mul_le_mul_of_nonneg_left hqmono hT.le)
      have hfun : (fun z => G ε (s • z) ω) =
          (fun z => H N z ω + B z ω) := funext fun z => heq z ω
      have hcross : 2 * T * aQ P H ξ N q <
          acrossDist ξ (fun z => G ε (s • z) ω) 0 R' (2 * r) := by
        rw [hfun]
        exact lt_of_not_ge hCg
      have hsphere : s * acrossDist ξ (fun z => G ε (s • z) ω) 0 R' (2 * r) ≤
          lfppSetDist ξ (fun z => G ε z ω) univ
            (Metric.sphere 0 r) (Metric.sphere 0 R) :=
        adapter_sphere_distance_ge_cross (φ := fun z => G ε z ω) (ξ := ξ)
          (r := r) (R' := R') (s := s) hd ((hG ε ⟨hε.1, hε1⟩).continuous ω)
          hr hR' hs hs1
      have hmargin : T * aQ P H ξ N q <
          s * (2 * T * aQ P H ξ N q) := by
        have hpos : 0 < T * aQ P H ξ N q := mul_pos hT haqpos
        nlinarith [mul_pos (by linarith : 0 < 2 * s - 1) hpos]
      have hstrict : (⨆ p : Metric.ball (0 : Rd d) r × Metric.ball (0 : Rd d) r,
          lfppMetric ξ (fun z => G ε z ω) p.1 p.2) <
          lfppSetDist ξ (fun z => G ε z ω) univ
            (Metric.sphere 0 r) (Metric.sphere 0 R) := by
        calc
          _ ≤ T * aQ P H ξ N q := hdiam
          _ < s * (2 * T * aQ P H ξ N q) := hmargin
          _ < s * acrossDist ξ (fun z => G ε (s • z) ω) 0 R' (2 * r) :=
            mul_lt_mul_of_pos_left hcross hs0
          _ ≤ _ := hsphere
      exact (not_le_of_gt hstrict) hω
  calc
    P {ω | lfppSetDist ξ (fun z => G ε z ω) univ
        (Metric.sphere 0 r) (Metric.sphere 0 R) ≤
          ⨆ p : Metric.ball (0 : Rd d) r × Metric.ball (0 : Rd d) r,
            lfppMetric ξ (fun z => G ε z ω) p.1 p.2}
        ≤ P ({ω | ∃ x ∈ Metric.closedBall (0 : Rd d) r,
            ∃ y ∈ Metric.closedBall (0 : Rd d) r,
              M₀ * aHat P G ξ ε * ‖x - y‖ ^ β <
                lfppMetric ξ (fun z => G ε z ω) x y} ∪
          {ω | acrossDist ξ (fun z => H N z ω + B z ω)
            0 R' (2 * r) ≤ 2 * T * aQ P H ξ N q}) := measure_mono hsub
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
      (measure_union_le _ _).trans (add_le_add hholderBad hpertBad)
    _ = ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end HigherDimLQGMetric.DGZ
