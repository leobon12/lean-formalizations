import HigherDimLQGMetric.DGZ.TightNondegCross
import HigherDimLQGMetric.DGZ.TightDistInfTools
import HigherDimLQGMetric.DGZ.NiceBoxShell

/-!
# DGZ Lemma 6.7: distance to infinity, for perturbed fields (packet L5a)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 6.7 (TeX l. 3054–3106, p. 60);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-6.5–6.7; blueprint Part C,
Lemma `r2:lem:67` (authoritative: the perturbed form, ruling M23 (v)).

* `distInf_shell_growth` (Step 1): there are `c₁, p₁ > 0` and `k₀` with
  `P[D_n(across B_{2^{k+1}}(0) \ B_{2^k}(0)) > c₁ 2^{(g/2)k} a^{(q)}_n] ≥ p₁` for `k ≥ k₀` and all
  `n`, where `g = ξ(Q - √(2d))` (the factor `2^{(g/2)k}` is the growth `e^{c'k}` of the blueprint).
* **`distInf_aq_pert`** (Lemma 6.7 for perturbed fields): for `q ∈ [q₂, 1)`, `r > 0`, `T` and
  `θ > 0` there is `R > r` such that for every dyadic realization, every `b ∈ [1, 2]`, every version
  `G` of `H_{1,b}` over the same white noise and every `n`:
  `P[D(h_n + G)(across B_R(0) \ B_r(0)) ≤ T a^{(q)}_n] ≤ θ`.
* **`distInf_aq`** (DGZ Lemma 6.7, `b = 1`, `G = 0`).

**Proof** (blueprint `r2:lem:67`). *Step 1.* Rescale by `2^k`: `h_n(2^k ·) = Y` is a version of
`H_{2^{-(n+k)}, 2^{-k}}` over a transformed white noise `W'`; with a version `X` of
`H_{2^{-k}, 1}` over `W'`, `X + Y` is a version of `h_{n+k}` (it is the level `n + k` of a dyadic
realization over `W'`). Lemma 6.6 (extension, `nondeg_cross_unit`) at level `q' ∈ (q, 1)` gives
`P[D(X + Y)(across B₂ \ B₁) > A a^{(q')}_{n+k}] ≥ A`; on `{sup_{B̄₂} |X| ≤ (√(2d) + ε) k log 2}`
(probability `≥ 1 - C e^{-k log 2/C}`, L3b2's `exists_sup_cbox_tail`)
`D(Y)(across) ≥ 2^{-ξ(√(2d)+ε)k} D(X + Y)(across)`; and
`a^{(q)}_n ≤ C₅ 2^{(1-ξQ+ε)k} a^{(q')}_{n+k}`
(`Cor52Shape`). With `ε = g/(2(ξ+1))` the product is `2^{(g/2)k}`.
*Step 2.* `D(h_n + G)(across shell_k) ≥ 2^{-(g/4)k} D_n(across shell_k)` outside
`{sup_{B̄_{2^{k+1}}(0)} |G| > (g/4) k log 2/ξ}`, whose probability is at most
`(2^{k+2} + 1)^d · 2 exp(-(…)²/(2 log 2)) → 0` (`exists_sup_tail_growing`).
*Step 3.* `h_n + G` is a version of `H_{2^{-n}, b}` (range `2 ρ_κ b ≤ 4 ρ_κ`), so the across
distances of the shells `k₃ + 2i` are independent (`iIndepFun_restrict_of_far`,
`measurable_acrossDist_comap_shell`). A crossing of `B_R \ B_r` crosses every shell in between
(`acrossDist_ge_sum_shells`). Grouping the `J = K L` shells into `K` groups of `L`, every group
contains a success (`D > c₁ a`) outside probability `K (1 - p₁/2)^L ≤ θ`, and then
`D(across B_R \ B_r) ≥ K c₁ a > T a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-! ### Step 1: one shell, with growth -/

/-- The growth exponent identity of Step 1: with `ε (ξ + 1) = g/2`,
`2^k e^{-ξ(√(2d)+ε) k log 2} 2^{-(1-ξQ+ε)k} = 2^{(g/2)k}`, `g = ξ(Q - √(2d))`. -/
lemma tdi_growth_identity {ξ Q ε : ℝ} (s : ℝ) (k : ℕ) (hε : ε * (ξ + 1) = ξ * (Q - s) / 2) :
    (2 : ℝ) ^ k * Real.exp (-(ξ * ((s + ε) * (k * Real.log 2)))) *
      (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) = (2 : ℝ) ^ (ξ * (Q - s) / 2 * k) := by
  rw [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos two_pos, ← Real.rpow_natCast,
    Real.rpow_def_of_pos two_pos, ← Real.exp_add, ← Real.exp_add]
  congr 1
  linear_combination (-(Real.log 2) * (k : ℝ)) * hε

/-- **DGZ Lemma 6.7, Step 1** (blueprint `r2:lem:67`): one shell, with growth. -/
theorem distInf_shell_growth {κ : Rd d → ℝ} {ξ Q : ℝ} (hC52 : Cor52Shape d κ ξ Q)
    (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ p₁ : ℝ, 0 < p₁ ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
            ENNReal.ofReal p₁ ≤ P {ω | c₁ * (2 : ℝ) ^ (ξ * (Q - Real.sqrt (2 * d)) / 2 * k) *
              aQ P H ξ n q < acrossDist ξ (fun z => H n z ω) 0 (2 ^ (k + 1)) (2 ^ k)} := by
  have hd := h.dim
  have hd0 : 0 < d := by omega
  have hξ := h.xi_pos
  have hκ := h.kernel
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hg : 0 < ξ * (Q - Real.sqrt (2 * d)) := mul_pos hξ (by linarith [h.subcritical])
  set g := ξ * (Q - Real.sqrt (2 * d)) with hgdef
  set ε : ℝ := g / (2 * (ξ + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hεξ : ε * (ξ + 1) = ξ * (Q - Real.sqrt (2 * d)) / 2 := by
    rw [hεdef, ← hgdef]; field_simp
  obtain ⟨q₂, hq₂0, hq₂1, hunit⟩ := nondeg_cross_unit hC52 h
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 => ?_⟩
  have hq0 : 0 < q := hq₂0.trans_le hq₂q
  obtain ⟨q', hqq', hq'1⟩ := exists_between hq1
  obtain ⟨A, hA, hAb⟩ := hunit q' (hq₂q.trans hqq'.le) hq'1
  obtain ⟨C₅, hC₅, hcor⟩ := hC52 h ε hε q q' hq0 hqq' hq'1
  obtain ⟨Ct, hCt, hCtb⟩ := exists_sup_cbox_tail hκ (A := Real.sqrt (2 * d) + ε)
    (by linarith) (R := 2) (by norm_num)
  have hev : ∀ᶠ k : ℕ in atTop, Ct * Real.exp (-((k : ℝ) * Real.log 2) / Ct) < A / 2 := by
    have ht : Tendsto (fun k : ℕ => Ct * Real.exp (-((k : ℝ) * Real.log 2) / Ct)) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => (k : ℝ) * Real.log 2 / Ct) atTop atTop :=
        (tendsto_natCast_atTop_atTop.atTop_mul_const hlog2).atTop_div_const hCt
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul Ct
      simp only [mul_zero] at h2
      refine h2.congr fun k => ?_
      simp only [Function.comp_apply, neg_div]
    exact ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hev
  refine ⟨A / C₅, by positivity, A / 2, by positivity, k₀,
    fun k hk Ω _ P W H hH n => ?_⟩
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  have hr : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  set W' : WN d → Ω → ℝ := fun f => W (simL2 (LinearIsometryEquiv.refl ℝ (Rd d)) 0 hr f)
    with hW'def
  have hW' : IsWhiteNoise P W' := hW.comp_simL2 _ 0 hr
  -- the rescaled field `Y = h_n(2^k ·)`
  set Y : Rd d → Ω → ℝ := fun z ω => H n ((2 : ℝ) ^ k • z) ω with hYdef
  have hY : IsBandVersion P W' κ ((2 : ℝ)⁻¹ ^ (n + k)) ((2 : ℝ)⁻¹ ^ k) Y := by
    have h1 := (hH.band n).comp_smul hκ hr (tb_inv_two_pow_pos n)
    refine h1.congr_band ?_ ?_
    · rw [pow_add, div_eq_mul_inv, inv_pow (2 : ℝ) k]
    · rw [one_div, inv_pow]
  obtain ⟨X, hX⟩ := exists_isBandVersion hκ hW' (tb_inv_two_pow_pos k) 1
  have hXY : IsBandVersion P W' κ ((2 : ℝ)⁻¹ ^ (n + k)) 1 (fun z ω => X z ω + Y z ω) :=
    isBandVersion_add hκ hW' (tb_inv_two_pow_pos (n + k))
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left k n))
      (pow_le_one₀ (by norm_num) (by norm_num)) hX hY
  obtain ⟨H', hH', hH'eq⟩ := exists_isDyadicRealization_eq_tight hκ hW' (n + k) hXY
  have hb := hAb Ω P W' H' hH' (n + k)
  rw [hH'eq, aQ_eq_of_isDyadicRealization hH' hH] at hb
  -- the supremum of `X` on `B̄₂(0)`
  have hTb := hCtb hW' (a := (2 : ℝ)⁻¹ ^ k) (b := 1) (tb_inv_two_pow_pos k)
    (pow_le_one₀ (by norm_num) (by norm_num)) hX 0
  simp only [log_one_div_inv_two_pow, mul_one] at hTb
  set S : ℝ := (Real.sqrt (2 * d) + ε) * (k * Real.log 2) with hS
  -- quantile comparison
  have hcomp : aQ P H ξ n q ≤ C₅ * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * aQ P H ξ (n + k) q' := by
    have := hcor Ω P W H hH (n + k) k (Nat.le_add_left k n)
    rwa [Nat.add_sub_cancel] at this
  have ha : 0 < aQ P H ξ n q := tight_aQ_pos hd0 hH ξ n hq0 hq1
  -- the inclusion
  have hincl : {ω | A * aQ P H ξ (n + k) q' <
      acrossDist ξ (fun z => X z ω + Y z ω) 0 2 1} ⊆
      {ω | A / C₅ * (2 : ℝ) ^ (ξ * (Q - Real.sqrt (2 * d)) / 2 * k) * aQ P H ξ n q <
        acrossDist ξ (fun z => H n z ω) 0 (2 ^ (k + 1)) (2 ^ k)} ∪
      {ω | ∃ z ∈ cbox (0 : Rd d) 2, S < |X z ω|} := by
    intro ω hω
    by_cases hbad : ω ∈ {ω | ∃ z ∈ cbox (0 : Rd d) 2, S < |X z ω|}
    · exact Or.inr hbad
    left
    simp only [mem_ofPred_eq, not_exists, not_and, not_lt] at hω hbad ⊢
    -- scaling
    have hscale : acrossDist ξ (fun z => H n z ω) 0 (2 ^ (k + 1)) (2 ^ k) =
        (2 : ℝ) ^ k * acrossDist ξ (fun z => Y z ω) 0 2 1 := by
      have := acrossDist_smul_add (0 : Rd d) ξ (fun z => H n z ω) hr 0 2 1
      simp only [smul_zero, add_zero, zero_add, mul_one] at this
      rw [← this, pow_succ]
    -- field comparison
    have hcmp : acrossDist ξ (fun z => X z ω + Y z ω) 0 2 1 ≤
        Real.exp (ξ * S) * acrossDist ξ (fun z => Y z ω) 0 2 1 := by
      refine acrossDist_le_mul_of_exp_le ((hX.continuous ω).add (hY.continuous ω))
        (hY.continuous ω) one_lt_two (Real.exp_pos _).le fun z hz => ?_
      have hXz : X z ω ≤ S := (le_abs_self _).trans (hbad z hz.1)
      show Real.exp (ξ * (X z ω + Y z ω)) ≤ Real.exp (ξ * S) * Real.exp (ξ * Y z ω)
      rw [← Real.exp_add]
      have := mul_le_mul_of_nonneg_left hXz hξ.le
      exact Real.exp_le_exp.2 (by linarith)
    have hpos : 0 < (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) := Real.rpow_pos_of_pos two_pos _
    have hid := tdi_growth_identity (ξ := ξ) (Q := Q) (ε := ε) (Real.sqrt (2 * d)) k hεξ
    -- combine
    have h1 : A * aQ P H ξ n q ≤ A * C₅ * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) *
        aQ P H ξ (n + k) q' := by
      calc A * aQ P H ξ n q ≤ A * (C₅ * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * aQ P H ξ (n + k) q') :=
            mul_le_mul_of_nonneg_left hcomp hA.le
        _ = _ := by ring
    have e2 : (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) = 1 := by
      rw [← Real.rpow_add two_pos,
        show -(1 - ξ * Q + ε) * (k : ℝ) + (1 - ξ * Q + ε) * k = 0 by ring, Real.rpow_zero]
    rw [hscale]
    calc A / C₅ * (2 : ℝ) ^ (ξ * (Q - Real.sqrt (2 * d)) / 2 * k) * aQ P H ξ n q
        = (2 : ℝ) ^ k * Real.exp (-(ξ * S)) * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) *
            (A / C₅ * aQ P H ξ n q) := by rw [← hid, hS]; ring
      _ ≤ (2 : ℝ) ^ k * Real.exp (-(ξ * S)) * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) *
            (A / C₅ * (C₅ * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * aQ P H ξ (n + k) q')) := by
          gcongr
      _ = (2 : ℝ) ^ k * Real.exp (-(ξ * S)) * (A * aQ P H ξ (n + k) q') *
            ((2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k)) := by
          field_simp
      _ = (2 : ℝ) ^ k * (Real.exp (-(ξ * S)) * (A * aQ P H ξ (n + k) q')) := by rw [e2]; ring
      _ < (2 : ℝ) ^ k * (Real.exp (-(ξ * S)) *
            (Real.exp (ξ * S) * acrossDist ξ (fun z => Y z ω) 0 2 1)) :=
          mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (hω.trans_le hcmp) (Real.exp_pos _))
            (by positivity)
      _ = (2 : ℝ) ^ k * acrossDist ξ (fun z => Y z ω) 0 2 1 := by
          rw [show Real.exp (-(ξ * S)) * (Real.exp (ξ * S) * acrossDist ξ (fun z => Y z ω) 0 2 1)
            = acrossDist ξ (fun z => Y z ω) 0 2 1 by
            rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]]
  have hk' := (hk₀ k hk).le
  calc ENNReal.ofReal (A / 2) = ENNReal.ofReal A - ENNReal.ofReal (A / 2) := by
        rw [← ENNReal.ofReal_sub _ (by positivity)]; congr 1; ring
    _ ≤ P {ω | A / C₅ * (2 : ℝ) ^ (ξ * (Q - Real.sqrt (2 * d)) / 2 * k) * aQ P H ξ n q <
          acrossDist ξ (fun z => H n z ω) 0 (2 ^ (k + 1)) (2 ^ k)} := by
        rw [tsub_le_iff_right]
        refine hb.trans ((measure_mono hincl).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl (hTb.trans (ENNReal.ofReal_le_ofReal ?_)))))
        rw [neg_div] at hk' ⊢
        simpa only [mul_comm] using hk'

/-! ### Step 2: the asymptotics of the perturbation tail -/

/-- For `α > 0`, `p > 0` and `D ∈ ℕ` there is `k₁` such that for all `k ≥ k₁`: `C₀ ≤ αk` and
`(2·2^{k+1} + 1)^D · 2 exp(-(αk - C₀)²/(2 log 2)) ≤ p` (Gaussian decay beats the exponential
number of boxes). -/
lemma tdi_exists_growing_small {α C₀ p : ℝ} (hα : 0 < α) (hp : 0 < p) (D : ℕ) :
    ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k → C₀ ≤ α * k ∧
      (2 * (2 : ℝ) ^ (k + 1) + 1) ^ D * (2 * Real.exp (-(α * k - C₀) ^ 2 / (2 * Real.log 2))) ≤
        p := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K₀ : ℝ := max 0 (Real.log (2 * 8 ^ D / p)) with hK₀
  have hK₀0 : 0 ≤ K₀ := le_max_left _ _
  set B : ℝ := max (2 * (|C₀| + 1) / α) (max 1 (8 * Real.log 2 / α ^ 2 * (D * Real.log 2 + K₀)))
    with hB
  refine ⟨⌈B⌉₊, fun k hk => ?_⟩
  have hkB : B ≤ k := (Nat.le_ceil B).trans (by exact_mod_cast hk)
  have hk1 : 2 * (|C₀| + 1) / α ≤ k := (le_max_left _ _).trans hkB
  have hk2 : (1 : ℝ) ≤ k := ((le_max_left _ _).trans (le_max_right _ _)).trans hkB
  have hk3 : 8 * Real.log 2 / α ^ 2 * (D * Real.log 2 + K₀) ≤ k :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hkB
  have hαk : 2 * (|C₀| + 1) ≤ α * k := by
    rw [div_le_iff₀ hα] at hk1; linarith
  have hC₀ := le_abs_self C₀
  have hC₀' := abs_nonneg C₀
  refine ⟨by linarith, ?_⟩
  have hsq : (α * k / 2) ^ 2 ≤ (α * k - C₀) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hbase : 2 * (2 : ℝ) ^ (k + 1) + 1 ≤ 8 * 2 ^ k := by
    rw [pow_succ]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    linarith
  have hpow : (2 * (2 : ℝ) ^ (k + 1) + 1) ^ D ≤ 8 ^ D * Real.exp (D * k * Real.log 2) := by
    calc (2 * (2 : ℝ) ^ (k + 1) + 1) ^ D ≤ (8 * 2 ^ k) ^ D :=
          pow_le_pow_left₀ (by positivity) hbase D
      _ = 8 ^ D * ((2 : ℝ) ^ k) ^ D := mul_pow _ _ _
      _ = 8 ^ D * Real.exp (D * k * Real.log 2) := by
          congr 1
          rw [← pow_mul, ← Real.exp_log (pow_pos two_pos (k * D)), Real.log_pow]
          push_cast
          ring_nf
  have hquad : D * k * Real.log 2 + K₀ ≤ α ^ 2 * k ^ 2 / (8 * Real.log 2) := by
    have h1 : D * Real.log 2 + K₀ ≤ α ^ 2 * k / (8 * Real.log 2) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hk3
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : (D * Real.log 2 + K₀) * 1 ≤ (D * Real.log 2 + K₀) * k :=
      mul_le_mul_of_nonneg_left hk2 (by positivity)
    have h3 : α ^ 2 * k ^ 2 / (8 * Real.log 2) = k * (α ^ 2 * k / (8 * Real.log 2)) := by ring
    rw [h3]
    have h4 : (D * Real.log 2 + K₀) * k ≤ k * (α ^ 2 * k / (8 * Real.log 2)) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  have hexp1 : -(α * k - C₀) ^ 2 / (2 * Real.log 2) ≤ -(α ^ 2 * k ^ 2 / (8 * Real.log 2)) := by
    rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hK₀p : Real.exp (-K₀) ≤ p / (2 * 8 ^ D) := by
    have h1 : Real.log (2 * 8 ^ D / p) ≤ K₀ := le_max_right _ _
    rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity), one_mul]
    calc 2 * 8 ^ D = Real.exp (Real.log (2 * 8 ^ D / p)) * p := by
          rw [Real.exp_log (by positivity)]; field_simp
      _ ≤ Real.exp K₀ * p := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h1) hp.le
      _ = p * Real.exp K₀ := mul_comm _ _
  calc (2 * (2 : ℝ) ^ (k + 1) + 1) ^ D * (2 * Real.exp (-(α * k - C₀) ^ 2 / (2 * Real.log 2)))
      ≤ 8 ^ D * Real.exp (D * k * Real.log 2) *
          (2 * Real.exp (-(α ^ 2 * k ^ 2 / (8 * Real.log 2)))) := by
        gcongr
    _ = 2 * 8 ^ D * Real.exp (D * k * Real.log 2 - α ^ 2 * k ^ 2 / (8 * Real.log 2)) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ 2 * 8 ^ D * Real.exp (-K₀) := by
        gcongr
        linarith
    _ ≤ 2 * 8 ^ D * (p / (2 * 8 ^ D)) := by gcongr
    _ = p := by field_simp

/-! ### Step 3: counting successes over independent shells -/

/-- Blocks of a sum of nonnegative terms: `Σ_{g<K} Σ_{gL ≤ i < gL+L} f i ≤ Σ_{i < KL} f i`. -/
lemma tdi_sum_blocks (f : ℕ → ℝ) (L : ℕ) :
    ∀ K : ℕ, ∑ g ∈ Finset.range K, ∑ i ∈ Finset.Ico (g * L) (g * L + L), f i =
      ∑ i ∈ Finset.range (K * L), f i := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, show (K + 1) * L = K * L + L by ring]
    exact Finset.sum_range_add_sum_Ico f (Nat.le_add_right _ _)

/-- Far shells: for `i < j` with `k_j ≥ k_i + 2`, a point of `B̄_{2^{k_i+1}}(0)` and a point outside
`B_{2^{k_j}}(0)` are at distance `≥ 2^{k_i+1}`. -/
lemma tdi_far {k k' : ℕ} (hkk' : k + 2 ≤ k') {z w : Rd d}
    (hz : z ∈ cbox (0 : Rd d) ((2 : ℝ) ^ (k + 1))) (hw : w ∉ obox (0 : Rd d) ((2 : ℝ) ^ k')) :
    (2 : ℝ) ^ (k + 1) ≤ ‖z - w‖ := by
  simp only [HigherDimLFPP.DGZ.obox, mem_ofPred_eq, not_forall, not_lt] at hw
  obtain ⟨m, hm⟩ := hw
  have h1 := hz m
  simp only [PiLp.zero_apply, sub_zero] at hm h1
  have h2 : (2 : ℝ) ^ (k + 2) ≤ (2 : ℝ) ^ k' := pow_le_pow_right₀ (by norm_num) hkk'
  have h3 : (2 : ℝ) ^ (k + 2) = 2 * (2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
  have h4 : |w m| - |z m| ≤ |z m - w m| := by
    rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
  have h5 := HigherDimLFPP.DGZ.abs_apply_le_norm (z - w) m
  rw [PiLp.sub_apply] at h5
  linarith

/-- **DGZ Lemma 6.7 for perturbed fields** (blueprint `r2:lem:67`, ruling M23 (v); [2] Lemma 6.7
for `b = 1`). Under `Cor52Shape` and `DGZHyp` there is `q₂ ∈ (0, 1)` such that for every
`q ∈ [q₂, 1)`, `r > 0`, `T` and `θ > 0` there is `R > r` with
`P[D(h_n + G)(across B_R(0) \ B_r(0)) ≤ T a^{(q)}_n] ≤ θ` for every dyadic realization `(P, W, H)`,
every `b ∈ [1, 2]`, every continuous version `G` of `H_{1,b}` over the same white noise `W`, and
every `n` (the blueprint's `n ≥ N` holds with `N = 0`). -/
theorem distInf_aq_pert {κ : Rd d → ℝ} {ξ Q : ℝ} (hC52 : Cor52Shape d κ ξ Q)
    (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∀ r T θ : ℝ, 0 < r → 0 < θ → ∃ R : ℝ, r < R ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
          ∀ b : ℝ, 1 ≤ b → b ≤ 2 → ∀ G : Rd d → Ω → ℝ, IsBandVersion P W κ 1 b G → ∀ n : ℕ,
            P {ω | acrossDist ξ (fun z => H n z ω + G z ω) 0 R r ≤ T * aQ P H ξ n q} ≤
              ENNReal.ofReal θ := by
  have hd := h.dim
  have hd0 : 0 < d := by omega
  have hξ := h.xi_pos
  have hκ := h.kernel
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hg : 0 < ξ * (Q - Real.sqrt (2 * d)) := mul_pos hξ (by linarith [h.subcritical])
  set g := ξ * (Q - Real.sqrt (2 * d)) with hgdef
  obtain ⟨q₂, hq₂0, hq₂1, hgrow⟩ := distInf_shell_growth hC52 h
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 r T θ hr hθ => ?_⟩
  have hq0 : 0 < q := hq₂0.trans_le hq₂q
  obtain ⟨c₁, hc₁, p₁, hp₁, k₀, hk₀⟩ := hgrow q hq₂q hq1
  obtain ⟨C₀, -, hCtail⟩ := exists_sup_tail_growing hκ
  set α : ℝ := g / 4 * Real.log 2 / ξ with hα
  have hα0 : 0 < α := by positivity
  obtain ⟨k₁, hk₁⟩ := tdi_exists_growing_small (C₀ := C₀) hα0 (by positivity : 0 < p₁ / 2) d
  obtain ⟨ρκ, hρκ0, hρκ⟩ := hκ.exists_radius
  obtain ⟨k₂, hk₂⟩ := pow_unbounded_of_one_lt (max r (2 * ρκ)) (by norm_num : (1 : ℝ) < 2)
  set p₂ : ℝ := min (p₁ / 2) (1 / 2) with hp₂
  have hp₂0 : 0 < p₂ := lt_min (by positivity) (by norm_num)
  have hp₂1 : p₂ ≤ 1 / 2 := min_le_right _ _
  set K : ℕ := ⌈max T 0 / c₁⌉₊ + 1 with hK
  have hKpos : (0 : ℝ) < K := by positivity
  have hKc : max T 0 < K * c₁ := by
    have h1 : max T 0 / c₁ < K := by
      rw [hK]; push_cast; exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
    rwa [div_lt_iff₀ hc₁] at h1
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (div_pos hθ hKpos) (by linarith : 1 - p₂ < 1)
  set J : ℕ := K * L with hJ
  set k₃ : ℕ := max (max k₀ k₁) k₂ with hk₃
  have hk₀₃ : k₀ ≤ k₃ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hk₁₃ : k₁ ≤ k₃ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hk₂₃ : k₂ ≤ k₃ := le_max_right _ _
  set R : ℝ := (2 : ℝ) ^ (k₃ + 2 * J) with hR
  have h2k₂ : (2 : ℝ) ^ k₂ ≤ (2 : ℝ) ^ k₃ := pow_le_pow_right₀ (by norm_num) hk₂₃
  have hrR : r < R := by
    have : (2 : ℝ) ^ k₃ ≤ R := pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)
    linarith [le_max_left r (2 * ρκ)]
  refine ⟨R, hrR, fun Ω _ P W H hH b hb1 hb2 G hG n => ?_⟩
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  set a := aQ P H ξ n q with ha
  have ha0 : 0 < a := tight_aQ_pos hd0 hH ξ n hq0 hq1
  -- the field `F = h_n + G`, a version of `H_{2^{-n}, b}`
  have hF : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) b (fun z ω => H n z ω + G z ω) := by
    have h1 := isBandVersion_add hκ hW (tb_inv_two_pow_pos n)
      (pow_le_one₀ (by norm_num) (by norm_num)) hb1 hG (hH.band n)
    have e : (fun z ω => G z ω + H n z ω) = (fun z ω => H n z ω + G z ω) := by
      funext z ω; ring
    rwa [e] at h1
  have hFc : ∀ ω, Continuous fun z => H n z ω + G z ω := hF.continuous
  -- the shells `k₃ + 2i`
  set ks : ℕ → ℕ := fun i => k₃ + 2 * i with hks
  set A : ℕ → Set (Rd d) := fun i =>
    cbox (0 : Rd d) ((2 : ℝ) ^ (ks i + 1)) \ obox (0 : Rd d) ((2 : ℝ) ^ ks i) with hAdef
  set E : ℕ → Set Ω := fun i => {ω | c₁ * a <
    acrossDist ξ (fun z => H n z ω + G z ω) 0 ((2 : ℝ) ^ (ks i + 1)) ((2 : ℝ) ^ ks i)} with hEdef
  -- one shell: `P[E i] ≥ p₂`
  have hEprob : ∀ i, ENNReal.ofReal p₂ ≤ P (E i) := by
    intro i
    set k := ks i with hk
    have hkk₀ : k₀ ≤ k := hk₀₃.trans (Nat.le_add_right _ _)
    have hkk₁ : k₁ ≤ k := hk₁₃.trans (Nat.le_add_right _ _)
    have hstep1 := hk₀ k hkk₀ Ω P W H hH n
    obtain ⟨hαC, hsmall⟩ := hk₁ k hkk₁
    have htail := hCtail hW hb1 hb2 hG (2 ^ (k + 1)) (u := α * k - C₀) (by linarith)
    have hcast : (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
    rw [hcast, add_sub_cancel] at htail
    have hincl : {ω | c₁ * (2 : ℝ) ^ (g / 2 * k) * a <
        acrossDist ξ (fun z => H n z ω) 0 (2 ^ (k + 1)) (2 ^ k)} ⊆
        E i ∪ {ω | ∃ z ∈ cbox (0 : Rd d) ((2 : ℝ) ^ (k + 1)), α * k < |G z ω|} := by
      intro ω hω
      by_cases hbad : ω ∈ {ω | ∃ z ∈ cbox (0 : Rd d) ((2 : ℝ) ^ (k + 1)), α * k < |G z ω|}
      · exact Or.inr hbad
      left
      simp only [mem_ofPred_eq, not_exists, not_and, not_lt] at hω hbad
      have hcmp : acrossDist ξ (fun z => H n z ω) 0 (2 ^ (k + 1)) (2 ^ k) ≤
          Real.exp (ξ * (α * k)) *
            acrossDist ξ (fun z => H n z ω + G z ω) 0 (2 ^ (k + 1)) (2 ^ k) := by
        refine acrossDist_le_mul_of_exp_le ((hH.band n).continuous ω) (hFc ω)
          (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self k)) (Real.exp_pos _).le
          fun z hz => ?_
        have hGz := hbad z hz.1
        have hGz' : -G z ω ≤ α * k := (neg_le_abs _).trans hGz
        show Real.exp (ξ * H n z ω) ≤ Real.exp (ξ * (α * k)) * Real.exp (ξ * (H n z ω + G z ω))
        rw [← Real.exp_add]
        have := mul_le_mul_of_nonneg_left hGz' hξ.le
        exact Real.exp_le_exp.2 (by linarith)
      have hexp : Real.exp (ξ * (α * k)) = (2 : ℝ) ^ (g / 4 * k) := by
        rw [Real.rpow_def_of_pos two_pos, hα]
        congr 1
        field_simp
      have hsplit : (2 : ℝ) ^ (g / 2 * k) = (2 : ℝ) ^ (g / 4 * k) * (2 : ℝ) ^ (g / 4 * k) := by
        rw [← Real.rpow_add two_pos]; congr 1; ring
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (g / 4 * k) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have h2pos : 0 < (2 : ℝ) ^ (g / 4 * k) := Real.rpow_pos_of_pos two_pos _
      show c₁ * a < acrossDist ξ (fun z => H n z ω + G z ω) 0 ((2 : ℝ) ^ (k + 1)) ((2 : ℝ) ^ k)
      rw [hsplit] at hω
      rw [hexp] at hcmp
      have h3 : (2 : ℝ) ^ (g / 4 * k) * (c₁ * (2 : ℝ) ^ (g / 4 * k) * a) <
          (2 : ℝ) ^ (g / 4 * k) *
            acrossDist ξ (fun z => H n z ω + G z ω) 0 (2 ^ (k + 1)) (2 ^ k) := by
        calc (2 : ℝ) ^ (g / 4 * k) * (c₁ * (2 : ℝ) ^ (g / 4 * k) * a)
            = c₁ * ((2 : ℝ) ^ (g / 4 * k) * (2 : ℝ) ^ (g / 4 * k)) * a := by ring
          _ < _ := hω.trans_le hcmp
      have h4 := lt_of_mul_lt_mul_left h3 h2pos.le
      have h5 : c₁ * a ≤ c₁ * (2 : ℝ) ^ (g / 4 * k) * a := by
        have := mul_le_mul_of_nonneg_left h1 hc₁.le
        nlinarith
      linarith
    have hP := (measure_mono (μ := P) hincl).trans (measure_union_le _ _)
    have hPbad : P {ω | ∃ z ∈ cbox (0 : Rd d) ((2 : ℝ) ^ (k + 1)), α * k < |G z ω|} ≤
        ENNReal.ofReal (p₁ / 2) := by
      refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
      calc ((2 * (2 : ℝ) ^ (k + 1) + 1) ^ d *
            (2 * Real.exp (-(α * k - C₀) ^ 2 / (2 * Real.log 2)))) ≤ p₁ / 2 := hsmall
        _ = p₁ / 2 := rfl
    have h1 := hstep1.trans (hP.trans (add_le_add le_rfl hPbad))
    have h2 : ENNReal.ofReal p₂ + ENNReal.ofReal (p₁ / 2) ≤ ENNReal.ofReal p₁ := by
      rw [← ENNReal.ofReal_add hp₂0.le (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith [min_le_left (p₁ / 2) (1 / 2)])
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 (h2.trans h1)
  -- measurability of the events
  have hEmeas : ∀ i, MeasurableSet (E i) := fun i =>
    measurableSet_lt measurable_const (measurable_acrossDist hFc hF.measurable ξ 0 _ _)
  have hEc : ∀ i, P (E i)ᶜ ≤ ENNReal.ofReal (1 - p₂) := by
    intro i
    rw [prob_compl_eq_one_sub (hEmeas i), ENNReal.ofReal_sub _ hp₂0.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left (hEprob i) 1
  -- independence of the shells (finite range of `h_n + G`, a version of `H_{2^{-n}, b}`)
  have hfar : ∀ i j, i ≠ j → ∀ z ∈ A i, ∀ w ∈ A j, 2 * ρκ * b ≤ ‖z - w‖ := by
    have key : ∀ i j, i < j → ∀ z ∈ A i, ∀ w ∈ A j, 2 * ρκ * b ≤ ‖z - w‖ := by
      intro i j hij z hz w hw
      have h1 := tdi_far (k := ks i) (k' := ks j) (by simp only [hks]; omega) hz.1 hw.2
      have h2 : (2 : ℝ) ^ (k₂ + 1) ≤ (2 : ℝ) ^ (ks i + 1) :=
        pow_le_pow_right₀ (by norm_num) (by simp only [hks]; omega)
      have h3 : 2 * ρκ < (2 : ℝ) ^ k₂ := lt_of_le_of_lt (le_max_right _ _) hk₂
      have h4 : (2 : ℝ) ^ (k₂ + 1) = 2 * (2 : ℝ) ^ k₂ := by rw [pow_succ]; ring
      have h5 : 2 * ρκ * b ≤ 2 * ρκ * 2 := mul_le_mul_of_nonneg_left hb2 (by positivity)
      linarith
    intro i j hij z hz w hw
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact key i j hlt z hz w hw
    · rw [norm_sub_rev]; exact key j i hlt w hw z hz
  have hind := HigherDimLFPP.IsBandVersion.iIndepFun_restrict_of_far hW hκ hρκ hF
    (tb_inv_two_pow_pos n) A hfar
  have hEcmeas : ∀ i, MeasurableSet[MeasurableSpace.comap
      (fun ω (z : A i) => H n z ω + G z ω) MeasurableSpace.pi] (E i)ᶜ := by
    intro i
    have hm := measurable_acrossDist_comap_shell hFc ξ (0 : Rd d)
      (r₁ := (2 : ℝ) ^ (ks i + 1)) (r₂ := (2 : ℝ) ^ ks i) (by positivity)
      (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self _))
    have e : (E i)ᶜ = (fun ω => acrossDist ξ (fun z => H n z ω + G z ω) 0
        ((2 : ℝ) ^ (ks i + 1)) ((2 : ℝ) ^ ks i)) ⁻¹' Iic (c₁ * a) := by
      ext ω
      simp only [hEdef, mem_compl_iff, mem_ofPred_eq, not_lt, mem_preimage, mem_Iic]
    rw [e]
    exact hm measurableSet_Iic
  -- groups of `L` consecutive shells
  set Bad : ℕ → Set Ω := fun gr => ⋂ i ∈ Finset.Ico (gr * L) (gr * L + L), (E i)ᶜ with hBad
  have hBadP : ∀ gr, P (Bad gr) ≤ ENNReal.ofReal ((1 - p₂) ^ L) := by
    intro gr
    rw [hBad, hind.meas_biInter (fun i _ => hEcmeas i)]
    calc ∏ i ∈ Finset.Ico (gr * L) (gr * L + L), P (E i)ᶜ ≤
          ∏ _i ∈ Finset.Ico (gr * L) (gr * L + L), ENNReal.ofReal (1 - p₂) :=
          Finset.prod_le_prod fun i _ => hEc i
      _ = ENNReal.ofReal ((1 - p₂) ^ L) := by
          rw [Finset.prod_const, Nat.card_Ico, Nat.add_sub_cancel_left,
            ENNReal.ofReal_pow (by linarith)]
  -- on the complement of the bad groups, the crossing is long
  have hsub : {ω | acrossDist ξ (fun z => H n z ω + G z ω) 0 R r ≤ T * a} ⊆
      ⋃ gr ∈ Finset.range K, Bad gr := by
    intro ω hω
    by_contra hno
    simp only [mem_iUnion, not_exists] at hno
    have hsucc : ∀ gr ∈ Finset.range K, ∃ i ∈ Finset.Ico (gr * L) (gr * L + L), ω ∈ E i := by
      intro gr hgr
      by_contra hc
      push Not at hc
      exact hno gr hgr (mem_iInter₂.2 fun i hi => hc i hi)
    set f : ℕ → ℝ := fun i => acrossDist ξ (fun z => H n z ω + G z ω) 0
      ((2 : ℝ) ^ (ks i + 1)) ((2 : ℝ) ^ ks i) with hf
    have hf0 : ∀ i, 0 ≤ f i := fun i => acrossDist_nonneg _ _ _ _ _
    have hblock : ∀ gr ∈ Finset.range K, c₁ * a ≤ ∑ i ∈ Finset.Ico (gr * L) (gr * L + L), f i := by
      intro gr hgr
      obtain ⟨i, hi, hiE⟩ := hsucc gr hgr
      exact hiE.le.trans (Finset.single_le_sum (f := f) (fun j _ => hf0 j) hi)
    have hsum1 : K * (c₁ * a) ≤ ∑ i ∈ Finset.range J, f i := by
      rw [hJ, ← tdi_sum_blocks f L K]
      calc (K : ℝ) * (c₁ * a) = ∑ _gr ∈ Finset.range K, c₁ * a := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hblock
    have h2k₃ : ∀ i, (2 : ℝ) ^ k₃ ≤ (2 : ℝ) ^ ks i := fun i =>
      pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)
    have hsum2 := acrossDist_ge_sum_shells hd0 (ξ := ξ) (R := R) (hFc ω) hr.le J
      (fun i => (2 : ℝ) ^ ks i) (fun i => (2 : ℝ) ^ (ks i + 1))
      (fun i _ => pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self _))
      (fun i _ => by linarith [le_max_left r (2 * ρκ), h2k₃ i])
      (fun i hi => by rw [hR]; exact pow_le_pow_right₀ (by norm_num) (by simp only [hks]; omega))
      (fun i j hij _ => pow_le_pow_right₀ (by norm_num) (by simp only [hks]; omega))
    have hTa : T * a < K * (c₁ * a) := by
      have h1 : T * a ≤ max T 0 * a := mul_le_mul_of_nonneg_right (le_max_left _ _) ha0.le
      have h2 : max T 0 * a < K * c₁ * a := mul_lt_mul_of_pos_right hKc ha0
      linarith
    simp only [mem_ofPred_eq] at hω
    have hsum2' : ∑ i ∈ Finset.range J, f i ≤
        acrossDist ξ (fun z => H n z ω + G z ω) 0 R r := hsum2
    linarith
  calc P {ω | acrossDist ξ (fun z => H n z ω + G z ω) 0 R r ≤ T * a}
      ≤ P (⋃ gr ∈ Finset.range K, Bad gr) := measure_mono hsub
    _ ≤ ∑ gr ∈ Finset.range K, P (Bad gr) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _gr ∈ Finset.range K, ENNReal.ofReal ((1 - p₂) ^ L) :=
        Finset.sum_le_sum fun gr _ => hBadP gr
    _ = ENNReal.ofReal (K * (1 - p₂) ^ L) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal θ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [lt_div_iff₀ hKpos] at hL
        linarith

end DGZ

end HigherDimLQGMetric
