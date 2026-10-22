import HigherDimLQGMetric.DGZ.AdapterMedian
import HigherDimLQGMetric.DGZ.SelfDiam

/-!
# Exponent of the real-cutoff whole-space median

The dyadic exponent survives a bounded multiplicative change of the median and a cutoff
between consecutive dyadic scales.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP

/-- Numerical estimate used to pass from dyadic to real cutoffs. -/
private theorem adapter_ratio_numerical {n x y z α l K δ : ℝ}
    (hn : 0 < n) (hl : 0 < l) (hδ : 0 < δ)
    (happrox : |x / n + α * l| ≤ δ * l / 4)
    (hmed : |y - x| ≤ K) (hz : z ≤ -(n * l))
    (hscale : |z + n * l| ≤ l)
    (hbig : K + |α| * l ≤ δ * n * l / 4) :
    |y / z - α| ≤ δ := by
  have hnl : 0 < n * l := mul_pos hn hl
  have hzneg : z < 0 := lt_of_le_of_lt hz (neg_neg_of_pos hnl)
  have hzabs : n * l ≤ |z| := by rw [abs_of_neg hzneg]; linarith
  have hzabs0 : 0 < |z| := lt_of_lt_of_le hnl hzabs
  have happrox' : |x + α * n * l| ≤ δ * l / 4 * n := by
    have heq : x + α * n * l = n * (x / n + α * l) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hn]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left happrox hn.le
  have htriangle : |y - α * z| ≤ |y - x| + |x + α * n * l| + |α| * |z + n * l| := by
    have heq : y - α * z = (y - x) + (x + α * n * l) - α * (z + n * l) := by ring
    rw [heq]
    calc
      |(y - x) + (x + α * n * l) - α * (z + n * l)|
          ≤ |(y - x) + (x + α * n * l)| + |α * (z + n * l)| := abs_sub _ _
      _ ≤ |y - x| + |x + α * n * l| + |α| * |z + n * l| := by
            rw [abs_mul]
            gcongr
            exact abs_add_le _ _
  have hαl : |α| * |z + n * l| ≤ |α| * l :=
    mul_le_mul_of_nonneg_left hscale (abs_nonneg α)
  have hnum : |y - α * z| ≤ δ * n * l / 2 := by
    have hη : δ * l / 4 * n = δ * n * l / 4 := by ring
    rw [hη] at happrox'
    linarith [htriangle, happrox', hmed, hαl, hbig]
  have hrat : |y / z - α| = |y - α * z| / |z| := by
    have heq : y / z - α = (y - α * z) / z := by
      field_simp [ne_of_lt hzneg]
    rw [heq, abs_div]
  rw [hrat]
  apply (div_le_iff₀ hzabs0).2
  have hδnl : δ * n * l / 2 ≤ δ * |z| := by
    have hδ2 : 0 ≤ δ / 2 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.2 hzabs) hδ2]
  exact hnum.trans hδnl

/-- A two-sided multiplicative bound is an additive bounded logarithmic error. -/
private theorem adapter_log_error {a b c C : ℝ} (ha : 0 < a) (hc : 0 < c) (hC : 0 < C)
    (hlow : c * a ≤ b) (hupp : b ≤ C * a) :
    |Real.log b - Real.log a| ≤ max |Real.log c| |Real.log C| := by
  have hla : Real.log c + Real.log a ≤ Real.log b := by
    have h := Real.log_le_log (mul_pos hc ha) hlow
    rwa [Real.log_mul hc.ne' ha.ne'] at h
  have hua : Real.log b ≤ Real.log C + Real.log a := by
    have hb : 0 < b := (mul_pos hc ha).trans_le hlow
    have h := Real.log_le_log hb hupp
    rwa [Real.log_mul hC.ne' ha.ne'] at h
  rw [abs_le]
  constructor
  · have hcabs : -|Real.log c| ≤ Real.log c := neg_abs_le _
    have hmax : |Real.log c| ≤ max |Real.log c| |Real.log C| := le_max_left _ _
    linarith
  · have hCabs : Real.log C ≤ |Real.log C| := le_abs_self _
    have hmax : |Real.log C| ≤ max |Real.log c| |Real.log C| := le_max_right _ _
    linarith

/-- Exact logarithmic scale relation, including the endpoint `s = 1`. -/
private theorem adapter_log_scale {ε s : ℝ} {N : ℕ} (hs : 1 / 2 < s) (hs1 : s ≤ 1)
    (hεeq : ε = ((2 : ℝ)⁻¹ ^ N) * s) :
    Real.log ε ≤ -((N : ℝ) * Real.log 2) ∧
      |Real.log ε + (N : ℝ) * Real.log 2| ≤ Real.log 2 := by
  have hs0 : 0 < s := by linarith
  have hslog0 : Real.log s ≤ 0 := Real.log_nonpos hs0.le hs1
  have hsloglow : -(Real.log 2) < Real.log s := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 2) hs
    have he : Real.log (1 / 2 : ℝ) = -(Real.log 2) := by
      simpa only [one_div] using Real.log_inv (2 : ℝ)
    rwa [he] at h
  have hlogε : Real.log ε = -((N : ℝ) * Real.log 2) + Real.log s := by
    rw [hεeq, Real.log_mul (pow_ne_zero _ (by norm_num : (2⁻¹ : ℝ) ≠ 0)) hs0.ne',
      Real.log_pow, Real.log_inv]
    ring
  constructor
  · rw [hlogε]
    linarith
  · have hsabs : |Real.log s| ≤ Real.log 2 := by
      rw [abs_of_nonpos hslog0]
      linarith
    rw [hlogε]
    have heq : -((N : ℝ) * Real.log 2) + Real.log s + N * Real.log 2 = Real.log s := by
      ring
    rw [heq]
    exact hsabs

/-- A dyadic logarithmic exponent transfers through a uniformly comparable real-scale
normalizer. This lemma is deterministic. -/
theorem adapter_exponent_of_bounds (α : ℝ) (a : ℕ → ℝ) (b : ℝ → ℝ)
    (ha : ∀ N, 0 < a N)
    (hexp : Tendsto (fun N : ℕ => Real.log (a N) / N) atTop
      (𝓝 (-(α * Real.log 2))))
    (hbound : ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        ∃ N : ℕ, ∃ s : ℝ, 1 / 2 < s ∧ s ≤ 1 ∧
          ε = ((2 : ℝ)⁻¹ ^ N) * s ∧ c * a N ≤ b ε ∧ b ε ≤ C * a N) :
    Tendsto (fun ε : ℝ => Real.log (b ε) / Real.log ε) (𝓝[>] 0) (𝓝 α) := by
  obtain ⟨c, C, ε₀, hc, hC, hε₀, hb⟩ := hbound
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K : ℝ := max |Real.log c| |Real.log C| with hK
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (le_max_left _ _)
  refine Metric.tendsto_nhds.2 ?_
  intro δ hδ
  set e : ℝ := δ / 2 with he
  have he0 : 0 < e := by dsimp [e]; positivity
  have heta : 0 < e * Real.log 2 / 4 := by positivity
  have hev : ∀ᶠ N : ℕ in atTop,
      dist (Real.log (a N) / N) (-(α * Real.log 2)) < e * Real.log 2 / 4 :=
    hexp.eventually (Metric.ball_mem_nhds _ heta)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  have hden : 0 < e * Real.log 2 := mul_pos he0 hl
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt
    (4 * (K + |α| * Real.log 2) / (e * Real.log 2) + 1)
  have hnum0 : 0 ≤ K + |α| * Real.log 2 := add_nonneg hK0 (mul_nonneg (abs_nonneg _) hl.le)
  have hN₂pos : 0 < (N₂ : ℝ) := by
    have hq : 0 ≤ 4 * (K + |α| * Real.log 2) / (e * Real.log 2) := by positivity
    linarith
  set N₀ : ℕ := max N₁ N₂ with hN₀
  set ε₁ : ℝ := min ε₀ ((2 : ℝ)⁻¹ ^ N₀) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε₀ (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hε₁0] with ε hε
  obtain ⟨N, s, hs, hs1, hεeq, hlow, hupp⟩ := hb ε
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hN : N₀ ≤ N := adapter_index_ge_of_eps_lt hs hεeq
    (hε.2.trans_le (min_le_right _ _))
  have hN₁_le : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂_le : N₂ ≤ N := (le_max_right _ _).trans hN
  have hn : 0 < (N : ℝ) := lt_of_lt_of_le hN₂pos (by exact_mod_cast hN₂_le)
  have happrox : |Real.log (a N) / (N : ℝ) + α * Real.log 2| ≤
      e * Real.log 2 / 4 := by
    have ht := (hN₁ N hN₁_le).le
    simpa only [Real.dist_eq, sub_neg_eq_add] using ht
  have hmed : |Real.log (b ε) - Real.log (a N)| ≤ K :=
    adapter_log_error (ha N) hc hC hlow hupp
  obtain ⟨hz, hscale⟩ := adapter_log_scale hs hs1 hεeq
  have hNreal : (N₂ : ℝ) ≤ N := by exact_mod_cast hN₂_le
  have hq : 4 * (K + |α| * Real.log 2) < (N₂ : ℝ) * (e * Real.log 2) := by
    have h' : 4 * (K + |α| * Real.log 2) / (e * Real.log 2) < (N₂ : ℝ) := by
      linarith [hN₂]
    exact (div_lt_iff₀ hden).1 h'
  have hmul := mul_le_mul_of_nonneg_right hNreal hden.le
  have hbig : K + |α| * Real.log 2 ≤ e * (N : ℝ) * Real.log 2 / 4 := by
    nlinarith [hq, hmul]
  have hratio := adapter_ratio_numerical hn hl he0 happrox hmed hz hscale hbig
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hratio (by dsimp [e]; linarith)

/-- The fourth conjunct of `RealEpsAdapterShape`: the whole-space real-cutoff median has the
same exponent as the dyadic internal median. -/
theorem adapter_aHat_exponent {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) (hHolder : HolderTightShape d κ ξ Q)
    (hNondeg : NondegShape d κ ξ Q) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ} {G : ℝ → Rd d → Ω → ℝ}
    (hW : IsWhiteNoise P W)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (G ε)) :
    Tendsto (fun ε => Real.log (aHat P G ξ ε) / Real.log ε)
      (𝓝[>] 0) (𝓝 (1 - ξ * Q)) := by
  let β : ℝ := ξ * (Q - Real.sqrt (2 * d)) / 2
  have hβ0 : 0 < β := by
    dsimp [β]
    exact div_pos (mul_pos h.xi_pos (sub_pos.mpr h.subcritical)) (by norm_num)
  have hβ : β < ξ * (Q - Real.sqrt (2 * d)) := by
    dsimp [β]
    have hg0 : 0 < ξ * (Q - Real.sqrt (2 * d)) :=
      mul_pos h.xi_pos (sub_pos.mpr h.subcritical)
    linarith
  obtain ⟨c, C, ε₀, hc, hC, hε₀, -, hbounds⟩ :=
    adapter_median_bounds_real h hHolder hNondeg hβ0 hβ
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise d
  obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization h.kernel hW₀
  let a : ℕ → ℝ := fun N => aQ LQGDimension.ExistAsm.stdP H₀ ξ N 2⁻¹
  have ha : ∀ N, 0 < a N := by
    intro N
    dsimp [a, aQ]
    have hd0 : 0 < d := by have := h.dim; omega
    exact (hH₀.band N).lowerQuantile_lfppDistance_pos hd0 hW₀ ξ
      (by norm_num) (by norm_num)
  have hexp : Tendsto (fun N : ℕ => Real.log (a N) / N) atTop
      (𝓝 (-((1 - ξ * Q) * Real.log 2))) := by
    simpa only [a, neg_mul] using
      (h.exponent (ℕ → ℝ) LQGDimension.ExistAsm.stdP W₀ H₀ hH₀)
  apply adapter_exponent_of_bounds (1 - ξ * Q) a (aHat P G ξ) ha hexp
  refine ⟨c, C, ε₀, hc, hC, hε₀, ?_⟩
  intro ε hε
  obtain ⟨N, s, hs, hs1, hεeq, H, W', hH, hlow, hupp⟩ := hbounds hW hG ε hε
  have heq : aQ P H ξ N 2⁻¹ = a N :=
    aQ_eq_of_isDyadicRealization hH hH₀ ξ N 2⁻¹
  refine ⟨N, s, hs, hs1, hεeq, ?_, ?_⟩
  · simpa only [heq] using hlow.le
  · simpa only [heq] using hupp

end HigherDimLQGMetric.DGZ
