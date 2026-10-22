import HigherDimLQGMetric.DGZ.AdapterExponent
import HigherDimLQGMetric.DGZ.TightBasics

/-! Hölder part of the real-cutoff adapter. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (obox cbox)

variable {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}

/-- Specialize dyadic Hölder tightness to two concentric boxes, enlarging its constant
to make it positive. -/
theorem adapter_holder_box (h : DGZHyp d κ ξ Q)
    (hHolder : HolderTightShape d κ ξ Q) {β R θ : ℝ}
    (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    (hR : 0 < R) (hθ : 0 < θ) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ N : ℕ,
          P {ω | ∃ x ∈ obox (0 : Rd d) R, ∃ y ∈ obox (0 : Rd d) R,
              M * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
                lfppDistOn ξ (fun z => H N z ω) (obox 0 (R + 1)) x y} ≤
            ENNReal.ofReal θ := by
  obtain ⟨M₀, hM₀⟩ := hHolder h β hβ0 hβ (obox 0 (R + 1)) (obox 0 R)
    (HigherDimLFPP.DGZ.isOpen_obox 0 (R + 1))
    (HigherDimLFPP.DGZ.isOpen_obox 0 R)
    ((HigherDimLFPP.DGZ.convex_obox 0 R).isConnected
      ⟨0, fun i => by simp only [PiLp.zero_apply, sub_self, abs_zero]; linarith⟩)
    (isBounded_obox 0 R)
    (adapter_closure_obox_subset (by linarith : R < R + 1)) θ hθ
  refine ⟨max 1 M₀, le_max_left _ _, ?_⟩
  intro Ω _ P W H hH N
  have hd0 : 0 < d := by have := h.dim; omega
  have hq : 0 ≤ aQ P H ξ N 2⁻¹ := by
    unfold aQ
    exact ((hH.band N).lowerQuantile_lfppDistance_pos hd0
      hH.whiteNoise ξ (by norm_num) (by norm_num)).le
  have hsub : {ω | ∃ x ∈ obox (0 : Rd d) R, ∃ y ∈ obox (0 : Rd d) R,
      max 1 M₀ * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
        lfppDistOn ξ (fun z => H N z ω) (obox 0 (R + 1)) x y} ⊆
      {ω | ∃ x ∈ obox (0 : Rd d) R, ∃ y ∈ obox (0 : Rd d) R,
        M₀ * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
          lfppDistOn ξ (fun z => H N z ω) (obox 0 (R + 1)) x y} := by
    rintro ω ⟨x, hx, y, hy, hxy⟩
    refine ⟨x, hx, y, hy, lt_of_le_of_lt ?_ hxy⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 M₀) hq)
      (Real.rpow_nonneg (norm_nonneg _) _)
  exact (measure_mono hsub).trans (hM₀ (Ω := Ω) P W H hH N)

/-- Scaling a pair in a Euclidean ball by `s⁻¹`, with `s > 1/2`, puts it in a fixed box. -/
private theorem adapter_scaled_ball_mem {R s : ℝ} (hs : 1 / 2 < s)
    {x : Rd d} (hx : x ∈ Metric.closedBall 0 R) :
    s⁻¹ • x ∈ obox (0 : Rd d) (2 * R + 1) := by
  have hs0 : 0 < s := by linarith
  have hsi : s⁻¹ < 2 := by
    rw [← one_div]
    exact (div_lt_iff₀ hs0).2 (by linarith)
  have hxn : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hp : ‖s⁻¹ • x‖ < 2 * R + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
    have hmul : s⁻¹ * ‖x‖ ≤ 2 * R :=
      mul_le_mul hsi.le hxn (norm_nonneg _) (by norm_num)
    linarith
  intro i
  simpa only [PiLp.zero_apply, sub_zero] using
    (HigherDimLFPP.DGZ.abs_apply_le_norm (s⁻¹ • x) i).trans_lt hp

/-- The Hölder factor loses at most `2^β` under the rescaling `s ∈ (1/2,1]`. -/
private theorem adapter_scaled_power {s β : ℝ} (hs : 1 / 2 < s) (hs1 : s ≤ 1)
    (hβ : 0 ≤ β) (x y : Rd d) :
    s * ‖s⁻¹ • x - s⁻¹ • y‖ ^ β ≤ (2 : ℝ) ^ β * ‖x - y‖ ^ β := by
  have hs0 : 0 < s := by linarith
  have hsi : s⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hs0).2 (by linarith)
  have hnorm : ‖s⁻¹ • x - s⁻¹ • y‖ ≤ 2 * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
    exact mul_le_mul_of_nonneg_right hsi (norm_nonneg _)
  have hpow := Real.rpow_le_rpow (norm_nonneg _) hnorm hβ
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)] at hpow
  calc
    s * ‖s⁻¹ • x - s⁻¹ • y‖ ^ β ≤ ‖s⁻¹ • x - s⁻¹ • y‖ ^ β :=
      mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg _) _) hs1
    _ ≤ (2 : ℝ) ^ β * ‖x - y‖ ^ β := hpow

/-- Deterministic transfer of a dyadic box Hölder estimate through the real-scale coupling. -/
theorem adapter_holder_coupled_aux {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W W' : WN d → Ω → ℝ} {G : ℝ → Rd d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} {B : Rd d → Ω → ℝ}
    {ε s β R c M₀ L : ℝ} {N : ℕ}
    (hG : IsBandVersion P W κ ε 1 (G ε))
    (hH : IsDyadicRealization κ P W' H)
    (hd : 0 < d) (hs : 1 / 2 < s) (hs1 : s ≤ 1) (hβ : 0 < β)
    (hc : 0 < c) (hξ : 0 < ξ) (hM₀ : 0 ≤ M₀)
    (heq : ∀ z ω, G ε (s • z) ω = H N z ω + B z ω)
    (hmed : c * aQ P H ξ N 2⁻¹ ≤ aHat P G ξ ε)
    (ω : Ω)
    (hBg : ¬ ∃ z ∈ cbox (0 : Rd d) (2 * R + 2), L < |B z ω|)
    (hHg : ¬ ∃ x ∈ obox (0 : Rd d) (2 * R + 1),
      ∃ y ∈ obox (0 : Rd d) (2 * R + 1),
        M₀ * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
          lfppDistOn ξ (fun z => H N z ω) (obox 0 (2 * R + 2)) x y) :
    ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      ∀ y ∈ Metric.closedBall (0 : Rd d) R,
      lfppMetric ξ (fun z => G ε z ω) x y ≤
        (Real.exp (ξ * L) * M₀ * (2 : ℝ) ^ β / c) *
          aHat P G ξ ε * ‖x - y‖ ^ β := by
  intro x hx y hy
  have hs0 : 0 < s := by linarith
  let p : Rd d := s⁻¹ • x
  let q : Rd d := s⁻¹ • y
  have hp : p ∈ obox (0 : Rd d) (2 * R + 1) := adapter_scaled_ball_mem hs hx
  have hq : q ∈ obox (0 : Rd d) (2 * R + 1) := adapter_scaled_ball_mem hs hy
  have hpU : p ∈ obox (0 : Rd d) (2 * R + 2) :=
    (cbox_subset_obox (by linarith : 2 * R + 1 < 2 * R + 2))
      (HigherDimLFPP.DGZ.obox_subset_cbox 0 (2 * R + 1) hp)
  have hqU : q ∈ obox (0 : Rd d) (2 * R + 2) :=
    (cbox_subset_obox (by linarith : 2 * R + 1 < 2 * R + 2))
      (HigherDimLFPP.DGZ.obox_subset_cbox 0 (2 * R + 1) hq)
  have hBc : ∀ z ∈ obox (0 : Rd d) (2 * R + 2),
      |G ε (s • z) ω - H N z ω| ≤ L := by
    intro z hz
    rw [heq]
    simpa only [add_sub_cancel_left] using
      le_of_not_gt (fun ht => hBg ⟨z, HigherDimLFPP.DGZ.obox_subset_cbox _ _ hz, ht⟩)
  have hXc : Continuous (fun z => G ε (s • z) ω) :=
    (hG.continuous ω).comp (continuous_id.const_smul s)
  have hcomp := lfppDistOn_le_exp_mul (ζ := ξ) (V := obox 0 (2 * R + 2))
    (x := p) (y := q) hXc ((hH.band N).continuous ω) hBc
  have hjoin : PcwJoined (obox (0 : Rd d) (2 * R + 2)) p q :=
    PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 _) hpU hqU
  have hHbound : lfppDistOn ξ (fun z => H N z ω) (obox 0 (2 * R + 2)) p q ≤
      M₀ * aQ P H ξ N 2⁻¹ * ‖p - q‖ ^ β :=
    le_of_not_gt (fun ht => hHg ⟨p, hp, q, hq, ht⟩)
  have hscale : lfppMetric ξ (fun z => G ε z ω) x y =
      s * lfppMetric ξ (fun z => G ε (s • z) ω) p q := by
    have hh := lfppMetric_sim (LinearIsometryEquiv.refl ℝ (Rd d)) 0 ξ
      (fun z => G ε z ω) hs0 p q
    have hsp : s • p = x := by simp only [p, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
    have hsq : s • q = y := by simp only [q, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
    simpa only [zero_add, LinearIsometryEquiv.coe_refl, id, hsp, hsq] using hh
  have hD : lfppMetric ξ (fun z => G ε (s • z) ω) p q ≤
      Real.exp (ξ * L) * (M₀ * aQ P H ξ N 2⁻¹ * ‖p - q‖ ^ β) := by
    calc
      _ ≤ lfppDistOn ξ (fun z => G ε (s • z) ω) (obox 0 (2 * R + 2)) p q :=
        lfppMetric_le_lfppDistOn hjoin
      _ ≤ Real.exp (|ξ| * L) * lfppDistOn ξ (fun z => H N z ω)
        (obox 0 (2 * R + 2)) p q := hcomp
      _ ≤ Real.exp (ξ * L) * (M₀ * aQ P H ξ N 2⁻¹ * ‖p - q‖ ^ β) := by
        rw [abs_of_pos hξ]
        exact mul_le_mul_of_nonneg_left hHbound (Real.exp_pos _).le
  have hpow : s * ‖p - q‖ ^ β ≤ (2 : ℝ) ^ β * ‖x - y‖ ^ β :=
    adapter_scaled_power hs hs1 hβ.le x y
  have hq0 : 0 ≤ aQ P H ξ N 2⁻¹ := by
    unfold aQ
    exact ((hH.band N).lowerQuantile_lfppDistance_pos hd
      hH.whiteNoise ξ (by norm_num) (by norm_num)).le
  rw [hscale]
  calc
    s * lfppMetric ξ (fun z => G ε (s • z) ω) p q
        ≤ s * (Real.exp (ξ * L) * (M₀ * aQ P H ξ N 2⁻¹ * ‖p - q‖ ^ β)) :=
          mul_le_mul_of_nonneg_left hD hs0.le
    _ = (Real.exp (ξ * L) * M₀ * aQ P H ξ N 2⁻¹) *
          (s * ‖p - q‖ ^ β) := by ring
    _ ≤ (Real.exp (ξ * L) * M₀ * aQ P H ξ N 2⁻¹) *
          ((2 : ℝ) ^ β * ‖x - y‖ ^ β) := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ (Real.exp (ξ * L) * M₀ * (2 : ℝ) ^ β / c) *
          aHat P G ξ ε * ‖x - y‖ ^ β := by
        have hqmed : aQ P H ξ N 2⁻¹ ≤ c⁻¹ * aHat P G ξ ε := by
          have hh : aQ P H ξ N 2⁻¹ ≤ aHat P G ξ ε / c :=
            (le_div_iff₀ hc).2 (by nlinarith [hmed])
          simpa only [div_eq_mul_inv, mul_comm] using hh
        calc
          _ = (Real.exp (ξ * L) * M₀ * (2 : ℝ) ^ β) *
              aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β := by ring
          _ ≤ (Real.exp (ξ * L) * M₀ * (2 : ℝ) ^ β) *
              (c⁻¹ * aHat P G ξ ε) * ‖x - y‖ ^ β := by gcongr
          _ = _ := by field_simp

/-- Hölder tightness for sufficiently small real cutoffs. -/
theorem adapter_holder_small (h : DGZHyp d κ ξ Q)
    (hHolder : HolderTightShape d κ ξ Q) (hNondeg : NondegShape d κ ξ Q)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {G : ℝ → Rd d → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (G ε))
    (R θ : ℝ) (hR : 0 < R) (hθ : 0 < θ) :
    ∃ M ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        P {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) R,
            ∃ y ∈ Metric.closedBall (0 : Rd d) R,
              M * aHat P G ξ ε * ‖x - y‖ ^ β <
                lfppMetric ξ (fun z => G ε z ω) x y} ≤ ENNReal.ofReal θ := by
  have hd : 0 < d := by have hh := h.dim; omega
  obtain ⟨L₀, hL₀, M₀, hM₀, δ, hδ, N₀, hmedian⟩ :=
    adapter_median_bounds_coupled h hHolder hNondeg hβ0 hβ
  let c : ℝ := (1 / 2 : ℝ) * Real.exp (-(ξ * L₀)) * δ
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨M₁, hM₁, hHbound⟩ := adapter_holder_box h hHolder hβ0 hβ
    (R := 2 * R + 1) (θ := θ / 2) (by linarith) (by positivity)
  obtain ⟨L, hL, hBbound⟩ := adapter_exists_upperBand_sup_bound hd h.kernel
    (R := 2 * R + 2) (θ := θ / 2) (by linarith) (by positivity)
  let M : ℝ := Real.exp (ξ * L) * M₁ * (2 : ℝ) ^ β / c
  let ε₀ : ℝ := (2 : ℝ)⁻¹ ^ N₀
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hε₀1 : ε₀ ≤ 1 := by
    dsimp [ε₀]
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹ : ℝ) ≤ 1)
  refine ⟨M, ε₀, hε₀, hε₀1, ?_⟩
  intro ε hε
  have hε1 : ε < 1 := hε.2.trans_le hε₀1
  obtain ⟨N, s, hs, hs1, hεeq⟩ :=
    adapter_exists_dyadic_scale hε.1 hε1.le
  have hs0 : 0 < s := by linarith
  have hN : N₀ ≤ N := adapter_index_ge_of_eps_lt hs hεeq hε.2
  obtain ⟨H, hH, B, hB, heq⟩ := adapter_realScale_coupling h.kernel hW hε.1
    (hG ε ⟨hε.1, hε1⟩) N hs0 hs1 hεeq
  have hb1 : 1 ≤ 1 / s := (one_le_div hs0).2 hs1
  have hb2 : 1 / s ≤ 2 := (div_le_iff₀ hs0).2 (by linarith)
  have hmed : c * aQ P H ξ N 2⁻¹ ≤ aHat P G ξ ε := by
    have hh := (hmedian hW (hG ε ⟨hε.1, hε1⟩) hH hB hs hs1 hN heq).1
    exact hh.le
  have hBbad : P {ω | ∃ z ∈ cbox (0 : Rd d) (2 * R + 2), L < |B z ω|} ≤
      ENNReal.ofReal (θ / 2) := hBbound hH.whiteNoise hb1 hb2 hB
  have hHbad : P {ω | ∃ x ∈ obox (0 : Rd d) (2 * R + 1),
      ∃ y ∈ obox (0 : Rd d) (2 * R + 1),
        M₁ * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
          lfppDistOn ξ (fun z => H N z ω) (obox 0 (2 * R + 2)) x y} ≤
        ENNReal.ofReal (θ / 2) := by
    convert hHbound hH N using 1
    ring_nf
  have hsub : {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) R,
      ∃ y ∈ Metric.closedBall (0 : Rd d) R,
        M * aHat P G ξ ε * ‖x - y‖ ^ β <
          lfppMetric ξ (fun z => G ε z ω) x y} ⊆
      {ω | ∃ z ∈ cbox (0 : Rd d) (2 * R + 2), L < |B z ω|} ∪
      {ω | ∃ x ∈ obox (0 : Rd d) (2 * R + 1),
        ∃ y ∈ obox (0 : Rd d) (2 * R + 1),
          M₁ * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
            lfppDistOn ξ (fun z => H N z ω) (obox 0 (2 * R + 2)) x y} := by
    intro ω hω
    by_cases hBg : ∃ z ∈ cbox (0 : Rd d) (2 * R + 2), L < |B z ω|
    · exact Or.inl hBg
    · right
      by_contra hHg
      obtain ⟨x, hx, y, hy, hxy⟩ := hω
      exact (not_le_of_gt hxy) (adapter_holder_coupled_aux
        (hG ε ⟨hε.1, hε1⟩) hH hd hs hs1 hβ0 hc h.xi_pos (by linarith)
        heq hmed ω hBg hHg x hx y hy)
  calc
    P {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) R,
        ∃ y ∈ Metric.closedBall (0 : Rd d) R,
          M * aHat P G ξ ε * ‖x - y‖ ^ β <
            lfppMetric ξ (fun z => G ε z ω) x y}
        ≤ P ({ω | ∃ z ∈ cbox (0 : Rd d) (2 * R + 2), L < |B z ω|} ∪
          {ω | ∃ x ∈ obox (0 : Rd d) (2 * R + 1),
            ∃ y ∈ obox (0 : Rd d) (2 * R + 1),
              M₁ * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
                lfppDistOn ξ (fun z => H N z ω) (obox 0 (2 * R + 2)) x y}) :=
          measure_mono hsub
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
          (measure_union_le _ _).trans (add_le_add hBbad hHbad)
    _ = ENNReal.ofReal θ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

end HigherDimLQGMetric.DGZ
