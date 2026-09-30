import QuantumZipper.Proofs.RS.OnePointWeightedCore
import QuantumZipper.Proofs.RS.MartingaleBound
import QuantumZipper.Proofs.Thm11.MainMart

/-!
# RS S1-Q / S1-3 (via the Girsanov-free route S1-3P): the sharp `Υ`-estimate

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §5, nodes S1-Q, S1-3 and S1-3P.

`RS.prob_logCR_lt` (node S1-3, Lawler–Zhou, *SLE curves and natural parametrization*,
arXiv:1006.4936, Prop. 2.3, p. 16, upper bound; Beffara, *The dimension of the SLE curves*,
Ann. Probab. 36 (2008), Prop. 4, upper half): for `κ ∈ (0,8)` there is `C` such that for
`z ∈ ℍ` and `0 < r ≤ Im z / 2`,
`P(∃ t ≥ 0, z ∉ K_t, Υ_t(z) < r) ≤ C (r / Im z)^{1−κ/8} (Im z/|z|)^{8/κ−1}`.

**Route (S1-3P instead of S1-Q).** The blueprint's S1-Q bounds
`∫⁻_{ρ_r ≤ T} M_{ρ_r} S_{ρ_r}^{−β} dP`; since `M S^{−β} = Υ^{d−2} = r^{d−2}` at `ρ_r`, that
integral is exactly `r^{d−2} P(ρ_r ≤ T)`, so S1-Q *is* the finite-horizon form of S1-3 (a
`P`-statement). The Girsanov weighting of LZ only rewrites the same inequality under `Q`:
`V = barrier/φ_M` is a `Q`-supersolution iff the barrier is a `P`-supersolution (GIR-0), and Bayes'
rule (GIR-1) maps `E^Q[V_σ] ≤ E^Q[V_ρ]` to `E^P[barrier_σ] ≤ E^P[barrier_ρ]`. We therefore prove
the `P`-inequality directly with GIR-D (`OnePointWeightedCore.lean`, `opw_core`), which is the
documented fallback S1-3P; GIR-4/GIR-5 are not needed. The terminal ("horizon") limit `δ ↓ 0`
and the localization `c ↓ 0`, `T ↑ ∞` are done here by continuity of measure along monotone
unions (valid for arbitrary, possibly non-measurable, sets).

The proof of the weighted-diffusion bound is **own** (the barrier S1-W replaces LZ Lemma 2.2
(26), see `DEVIATIONS.md` L-S1).
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace RS

open FrozenMart FwdHolo FwdClock

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The core estimate without the horizon slack: the limit `δ ↓ 0` of `opw_core`. -/
theorem opw_bound_c (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ ξ > 0, -K * barW (8 / κ - 1) ξ + ξ * deriv (barW (8 / κ - 1)) ξ * (ξ ^ 2 - 1) / 2 ≤ 0)
    {CW : ℝ} (hCW : ∀ ξ ≥ 0, barW (8 / κ - 1) ξ ≤ CW * ξ ^ (8 / κ - 1))
    {c : ℝ} (hc : 0 < c) (T : ℝ≥0) {z : ℂ} (hcz : c ≤ z.im) {r : ℝ} (hr : 0 < r)
    (hrz : r ≤ z.im / 2) :
    P {ω | (opProc κ B c z (opTau κ B c z (Real.log r) T ω) ω).2 ≤ Real.log r
        ∧ c < (opProc κ B c z (opTau κ B c z (Real.log r) T ω) ω).1.im}
      ≤ ENNReal.ofReal (Real.exp (2 * K) * CW
          * (1 / Real.sqrt (min (κ / 4 * Real.log 2) 1)) ^ (8 / κ - 1)
          * Real.exp ((1 - κ / 8) * min (Real.log z.im) (Real.log r + 4 / κ))
          * phiMF κ (z, Real.log z.im) / barW (8 / κ - 1) 1) := by
  have hPm : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hp : 0 < 8 / κ - 1 := by rw [sub_pos, lt_div_iff₀ hκ]; linarith
  have hW1 : 0 < barW (8 / κ - 1) 1 := by
    rw [barW_eq]; exact div_pos (barNum_pos hp one_pos) (barDen_pos hp)
  set s : ℕ → Set Ω := fun n => opEvt κ B c z r T (1 / ((n : ℝ) + 1)) with hs
  have hmono : Monotone s := by
    intro n k hnk ω hω
    obtain ⟨h1, h2, h3⟩ := hω
    refine ⟨h1, h2, le_trans (Real.sqrt_le_sqrt ?_) h3⟩
    have : (n : ℝ) ≤ k := by exact_mod_cast hnk
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hunion : {ω | (opProc κ B c z (opTau κ B c z (Real.log r) T ω) ω).2 ≤ Real.log r
        ∧ c < (opProc κ B c z (opTau κ B c z (Real.log r) T ω) ω).1.im} ⊆ ⋃ n, s n := by
    rintro ω ⟨h1, h2⟩
    set S := Real.sin (Complex.arg (opProc κ B c z (opTau κ B c z (Real.log r) T ω) ω).1)
    have hS : 0 < S := sin_arg_pos (hc.trans h2)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / S ^ 2)
    refine mem_iUnion.2 ⟨n, h1, h2, ?_⟩
    rw [Real.sqrt_le_left hS.le]
    have h' : 1 / S ^ 2 < (n : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ (by positivity)] at h'
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hbd : ∀ n, P (s n) ≤ ENNReal.ofReal (Real.exp (2 * K) * CW
          * (1 / Real.sqrt (min (κ / 4 * Real.log 2) 1)) ^ (8 / κ - 1)
          * Real.exp ((1 - κ / 8) * min (Real.log z.im) (Real.log r + 4 / κ))
          * phiMF κ (z, Real.log z.im) / barW (8 / κ - 1) 1) := by
    intro n
    have h := opw_core hB hBc hBm hB0 hκ hκ8 hK0 hK hCW hc T hcz hr hrz
      (δ := 1 / ((n : ℝ) + 1)) (by positivity)
      (by rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    rw [← ofReal_measureReal (μ := P) (s := s n)]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hW1).2 h)
  calc _ ≤ P (⋃ n, s n) := measure_mono hunion
    _ ≤ _ := le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hbd

/-- **Localization.** If `z` is not swallowed by time `t ≤ T`, `Υ_t(z) < r` and
`Im f_s(z) ≥ 2c` on `[0,t]`, then the tamed state (taming level `c`) meets `{L ≤ log r}` before `T`
while `Im Z > c` (so it lies in the event of `opw_bound_c`). -/
theorem opw_mem_of_sle (hBc : ∀ ω, Continuous (B · ω)) {κ c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : 0 < z.im) {r : ℝ} (hr : 0 < r) {T : ℝ≥0} {ω : Ω} {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hlog : Real.exp (fwdLogCR (drive κ B ω) t z) < r)
    (him : ∀ s ∈ Icc (0 : ℝ) t, 2 * c ≤ (fwdMap (drive κ B ω) s z).im) :
    (opProc κ B c z (opTau κ B c z (Real.log r) T ω) ω).2 ≤ Real.log r
      ∧ c < (opProc κ B c z (opTau κ B c z (Real.log r) T ω) ω).1.im := by
  set W := drive κ B ω with hWdef
  have hW : Continuous W := NonSwallow.continuous_drive_ns hBc κ ω
  have hst : ∀ s ∈ Icc (0 : ℝ) t, tamedZ W c z s = fwdMap W s z ∧
      tamedLogCR W c z s = fwdLogCR W s z := fun s hs =>
    opState_eq_tamed hW hc hz hs.1 fun s' hs' => by
      have := him s' ⟨hs'.1, hs'.2.trans hs.2⟩; linarith
  set U := opProc κ B c z with hU
  have hUc : ∀ ω, Continuous (U · ω) := continuous_opProc hBc hc κ z
  set t' : ℝ≥0 := t.toNNReal with ht'
  have ht'e : (t' : ℝ) = t := Real.coe_toNNReal t ht
  have ht'T : t' ≤ T := by rw [← NNReal.coe_le_coe, ht'e]; exact htT
  have hmem : U t' ω ∈ opCl c (Real.log r) := by
    refine Or.inr ?_
    show tamedLogCR W c z t' ≤ Real.log r
    rw [ht'e, (hst t ⟨ht, le_rfl⟩).2]
    exact (Real.lt_log_iff_exp_lt hr).2 hlog |>.le
  have hτt : opTau κ B c z (Real.log r) T ω ≤ t' :=
    hittingBtwn_le_of_mem zero_le ht'T hmem
  have hτmem : U (opTau κ B c z (Real.log r) T ω) ω ∈ opCl c (Real.log r) :=
    opw_mem_hit hUc (isClosed_opCl c (Real.log r)) ⟨t', ⟨zero_le, ht'T⟩, hmem⟩
  have hτim : c < (U (opTau κ B c z (Real.log r) T ω) ω).1.im := by
    set τ := opTau κ B c z (Real.log r) T ω
    have hτ1 : (τ : ℝ) ∈ Icc (0 : ℝ) t :=
      ⟨τ.coe_nonneg, by rw [← ht'e]; exact_mod_cast hτt⟩
    show c < (tamedZ W c z τ).im
    rw [(hst τ hτ1).1]
    have := him τ hτ1
    linarith
  refine ⟨?_, hτim⟩
  rcases hτmem with h | h
  · exact absurd h (not_le.2 hτim)
  · exact h

/-- `e^{(1−κ/8) L₁} φ_M(z, log Im z) ≤ e^{(1−κ/8)(4/κ)} (r/Im z)^{1−κ/8} (Im z/|z|)^{8/κ−1}`. -/
theorem opw_rhs_le {κ : ℝ} (hκ8 : κ < 8) {z : ℂ} (hz : 0 < z.im) {r : ℝ} (hr : 0 < r) :
    Real.exp ((1 - κ / 8) * min (Real.log z.im) (Real.log r + 4 / κ))
        * phiMF κ (z, Real.log z.im)
      ≤ Real.exp ((1 - κ / 8) * (4 / κ)) * ((r / z.im) ^ (1 - κ / 8)
        * (z.im / ‖z‖) ^ (8 / κ - 1)) := by
  have h1 : Real.exp ((1 - κ / 8) * min (Real.log z.im) (Real.log r + 4 / κ))
      ≤ Real.exp ((1 - κ / 8) * (Real.log r + 4 / κ)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith))
  refine (mul_le_mul_of_nonneg_right h1 (phiMF_nonneg (x := (z, Real.log z.im)) hz)).trans
    (le_of_eq ?_)
  show Real.exp ((1 - κ / 8) * (Real.log r + 4 / κ))
      * (Real.exp ((κ / 8 - 1) * Real.log z.im) * Real.sin (Complex.arg z) ^ (8 / κ - 1)) = _
  rw [Complex.sin_arg, Real.rpow_def_of_pos (div_pos hr hz), Real.log_div hr.ne' hz.ne',
    ← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **S1-3 for a nice version of the Brownian motion** (continuous paths, `B 0 = 0`). -/
theorem opw_prob_good (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ ξ > 0, -K * barW (8 / κ - 1) ξ + ξ * deriv (barW (8 / κ - 1)) ξ * (ξ ^ 2 - 1) / 2 ≤ 0)
    {CW : ℝ} (hCW : ∀ ξ ≥ 0, barW (8 / κ - 1) ξ ≤ CW * ξ ^ (8 / κ - 1))
    {z : ℂ} (hz : 0 < z.im) {r : ℝ} (hr : 0 < r) (hrz : r ≤ z.im / 2) :
    P {ω | ∃ t ≥ (0 : ℝ), z ∉ fwdHull (drive κ B ω) t ∧
        Real.exp (fwdLogCR (drive κ B ω) t z) < r}
      ≤ ENNReal.ofReal (Real.exp (2 * K) * CW
          * (1 / Real.sqrt (min (κ / 4 * Real.log 2) 1)) ^ (8 / κ - 1)
          * Real.exp ((1 - κ / 8) * min (Real.log z.im) (Real.log r + 4 / κ))
          * phiMF κ (z, Real.log z.im) / barW (8 / κ - 1) 1) := by
  set G : ℕ → Set Ω := fun N => {ω | 1 / ((N : ℝ) + 1) ≤ z.im ∧ ∃ t ∈ Icc (0 : ℝ) N,
      Real.exp (fwdLogCR (drive κ B ω) t z) < r ∧
      ∀ s ∈ Icc (0 : ℝ) t, 2 * (1 / ((N : ℝ) + 1)) ≤ (fwdMap (drive κ B ω) s z).im} with hG
  have hanti : ∀ {N N' : ℕ}, N ≤ N' → 1 / ((N' : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    intro N N' h
    have : (N : ℝ) ≤ N' := by exact_mod_cast h
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hmono : Monotone G := by
    intro N N' h ω ⟨h1, t, ht, hlog, him⟩
    refine ⟨(hanti h).trans h1, t, ⟨ht.1, ht.2.trans (by exact_mod_cast h)⟩, hlog,
      fun s hs => le_trans ?_ (him s hs)⟩
    have := hanti h
    linarith
  have hcover : {ω | ∃ t ≥ (0 : ℝ), z ∉ fwdHull (drive κ B ω) t ∧
      Real.exp (fwdLogCR (drive κ B ω) t z) < r} ⊆ ⋃ N, G N := by
    rintro ω ⟨t, ht, hnot, hlog⟩
    set W := drive κ B ω
    have hW : Continuous W := NonSwallow.continuous_drive_ns hBc κ ω
    have hzH : z ∈ H \ fwdHull W t := ⟨hz, hnot⟩
    have hcont := continuousOn_fwdMap_time hW ht hzH
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 ht)
      (Complex.continuous_im.comp_continuousOn hcont)
    have hnot₀ : z ∉ fwdHull W s₀ := fun h =>
      hnot ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal hs₀.2)⟩
    have hv : 0 < (fwdMap W s₀ z).im :=
      (MainMart.im_fwdMap_pos_and_clock hW hs₀.1 ⟨hz, hnot₀⟩).1
    obtain ⟨N, hN⟩ := exists_nat_gt (max (max t (2 / (fwdMap W s₀ z).im)) (1 / z.im))
    have hN1 : t < N := lt_of_le_of_lt (le_max_left _ _ |>.trans (le_max_left _ _)) hN
    have hN2 : 2 / (fwdMap W s₀ z).im < N :=
      lt_of_le_of_lt (le_max_right _ _ |>.trans (le_max_left _ _)) hN
    have hN3 : 1 / z.im < N := lt_of_le_of_lt (le_max_right _ _) hN
    have hNp : (0 : ℝ) < N + 1 := by positivity
    refine mem_iUnion.2 ⟨N, ?_, t, ⟨ht, hN1.le⟩, hlog, fun s hs => ?_⟩
    · rw [div_le_iff₀ hNp]
      rw [div_lt_iff₀ hz] at hN3
      linarith
    · have h1 : (fwdMap W s₀ z).im ≤ (fwdMap W s z).im := hmin hs
      have h2 : 2 * (1 / ((N : ℝ) + 1)) ≤ (fwdMap W s₀ z).im := by
        rw [div_lt_iff₀ hv] at hN2
        rw [mul_one_div, div_le_iff₀ hNp]
        linarith
      linarith
  have hbd : ∀ N, P (G N) ≤ ENNReal.ofReal (Real.exp (2 * K) * CW
          * (1 / Real.sqrt (min (κ / 4 * Real.log 2) 1)) ^ (8 / κ - 1)
          * Real.exp ((1 - κ / 8) * min (Real.log z.im) (Real.log r + 4 / κ))
          * phiMF κ (z, Real.log z.im) / barW (8 / κ - 1) 1) := by
    intro N
    by_cases hcz : 1 / ((N : ℝ) + 1) ≤ z.im
    · have hc : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      refine le_trans (measure_mono ?_) (opw_bound_c hB hBc hBm hB0 hκ hκ8 hK0 hK hCW hc
        (N : ℝ≥0) hcz hr hrz)
      rintro ω ⟨-, t, ht, hlog, him⟩
      exact opw_mem_of_sle hBc hc hz hr ht.1 (by exact_mod_cast ht.2) hlog him
    · have : G N = ∅ := by
        ext ω; simp only [hG, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hcz
      rw [this, measure_empty]
      exact zero_le
  calc _ ≤ P (⋃ N, G N) := measure_mono hcover
    _ ≤ _ := le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hbd

end RS
end QuantumZipper
