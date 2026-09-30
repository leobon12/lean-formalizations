import QuantumZipper.Proofs.Thm18.LWFarDefs
import QuantumZipper.Proofs.RS.OnePointFinal
import QuantumZipper.Proofs.RS.NoRealHit
import QuantumZipper.Proofs.RS.TraceGen
import QuantumZipper.Proofs.Thm11.AddendumArea

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node LWF-2: the boundary hitting estimate

Main result: `bdryHitStmt_holds : BdryHitStmt κ` for `0 < κ < 4`: for a real
`x` and `0 < r ≤ |x|/2`, `P(dist(x, η[0,∞)) < r) ≤ C (r/|x|)^{8/κ−1}`.

Source: G. Lawler, B. Werness, *Multi-point Green's functions for SLE and an estimate of
Beffara*, Ann. Probab. 41 (2013), Prop 2.6 (p. 10), which cites Alberts–Kozdron. We do not follow
their proof (it uses a boundary martingale); instead this is an **own elementary argument**
deducing it from the proved one-point estimate `RS.sleOnePointBound` (Beffara 2008, Prop 4) by a
Whitney cover, exactly as in the project's S1-5 argument `RS.prob_infDist_lt_im`
(`OnePointFinal.lean`):
* layer `k` of `B(x, r) ∩ ℍ` (heights in `(h_k/2, h_k]`, `h_k = r/2^k`) is covered by the
  `2^{k+2}+1` points `z = x + m h_k/2 + i h_k`, `|m| ≤ 2^{k+1}`, with `dist(y, z) < Im z`;
* each point has `|z| ≥ |x|/2`, so `P(dist(z, η) < Im z) ≤ C₁ (2 r/|x|)^β 2^{-kβ}`, `β = 8/κ − 1`;
* the union bound gives the geometric series `Σ_k 5·2^k 2^{-kβ} < ∞` since `β > 1`;
* a.s. the trace meets `ℝ` only at `η(0) = 0` (`RS.ae_sleTrace_real_eq_zero`, Rohde–Schramm
  Lemma 6.2), which lies outside `B(x, r)`, and it stays in `closure ℍ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- Height of layer `k`. -/
def bhH (r : ℝ) (k : ℕ) : ℝ := r / 2 ^ k

/-- Cover points of layer `k`. -/
def bhPt (x r : ℝ) (k : ℕ) (m : ℤ) : ℂ := ⟨x + m * (bhH r k / 2), bhH r k⟩

theorem bhH_pos {r : ℝ} (hr : 0 < r) (k : ℕ) : 0 < bhH r k := by unfold bhH; positivity

/-- Whitney cover of `B(x, r) ∩ ℍ`. -/
theorem bh_cover {x r : ℝ} (hr : 0 < r) {y : ℂ} (hy : 0 < y.im) (hyx : ‖y - x‖ < r) :
    ∃ k : ℕ, ∃ m ∈ Finset.Icc (-(2 ^ (k + 1) : ℤ)) (2 ^ (k + 1)),
      dist y (bhPt x r k m) < bhH r k := by
  classical
  have hre : |y.re - x| < r := by
    have := Complex.abs_re_le_norm (y - x); simp at this; linarith
  have him : y.im < r := by
    have := Complex.abs_im_le_norm (y - x); simp at this
    exact lt_of_le_of_lt (le_abs_self _) (by linarith)
  have hex : ∃ k : ℕ, bhH r k / 2 < y.im := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hy hr) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    have h1 : bhH r n = r * (1 / 2) ^ n := by unfold bhH; rw [one_div_pow]; ring
    rw [h1]
    have := (lt_div_iff₀ hr).1 hn
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
  set k := Nat.find hex with hk
  have hlo : bhH r k / 2 < y.im := Nat.find_spec hex
  have hup : y.im ≤ bhH r k := by
    rcases Nat.eq_zero_or_pos k with h0 | hs
    · rw [h0]; unfold bhH; simp; exact him.le
    · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hmin := Nat.find_min hex (show j < k by omega)
      rw [not_lt] at hmin
      have e : bhH r k = bhH r j / 2 := by
        unfold bhH; rw [hj, pow_succ]; field_simp
      rw [e]; exact hmin
  set h := bhH r k with hh
  have h0 : 0 < h := bhH_pos hr k
  set u := (y.re - x) / (h / 2) with hu
  refine ⟨k, round u, ?_, ?_⟩
  · have hu2 : |u| < 2 ^ (k + 1) := by
      rw [hu, abs_div, abs_of_pos (by positivity : (0 : ℝ) < h / 2), div_lt_iff₀ (by positivity)]
      have : (2 : ℝ) ^ (k + 1) * (h / 2) = r := by
        rw [hh]; unfold bhH; rw [pow_succ]; field_simp
      rw [this]; exact hre
    have hr1 := abs_sub_round u
    have hm : |((round u : ℤ) : ℝ)| < 2 ^ (k + 1) + 1 := by
      have h3 : |((round u : ℤ) : ℝ)| - |u| ≤ |u - round u| := by
        rw [abs_sub_comm u]; exact abs_sub_abs_le_abs_sub _ _
      linarith
    rw [abs_lt] at hm
    have h1 : ((round u : ℤ) : ℝ) < ((2 ^ (k + 1) + 1 : ℤ) : ℝ) := by push_cast; linarith
    have h2 : ((-(2 ^ (k + 1) : ℤ) - 1 : ℤ) : ℝ) < ((round u : ℤ) : ℝ) := by push_cast; linarith
    have h1' := Int.cast_lt.1 h1
    have h2' := Int.cast_lt.1 h2
    rw [Finset.mem_Icc]; constructor <;> omega
  · rw [dist_eq_norm]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    have ere : (y - bhPt x r k (round u)).re = h / 2 * (u - round u) := by
      simp only [Complex.sub_re, bhPt, hu]; rw [← hh]; field_simp; ring
    have eim : (y - bhPt x r k (round u)).im = y.im - h := by
      simp only [Complex.sub_im, bhPt]; rw [← hh]
    rw [ere, eim, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < h / 2),
      abs_of_nonpos (show y.im - h ≤ 0 by linarith)]
    have := mul_le_mul_of_nonneg_left (abs_sub_round u) (by positivity : (0 : ℝ) ≤ h / 2)
    rw [← hh]; linarith

/-- Cover points are far from the origin. -/
theorem bh_norm_ge {x r : ℝ} (hr : 0 < r) (hrx : 2 * r ≤ |x|) {k : ℕ} {m : ℤ}
    (hm : m ∈ Finset.Icc (-(2 ^ (k + 1) : ℤ)) (2 ^ (k + 1))) :
    |x| / 2 ≤ ‖bhPt x r k m‖ := by
  rw [Finset.mem_Icc] at hm
  have hm' : |(m : ℝ)| ≤ 2 ^ (k + 1) := by
    rw [abs_le]; constructor
    · have := Int.cast_le (R := ℝ).2 hm.1; push_cast at this; linarith
    · have := Int.cast_le (R := ℝ).2 hm.2; push_cast at this; linarith
  have hh : (2 : ℝ) ^ (k + 1) * (bhH r k / 2) = r := by
    unfold bhH; rw [pow_succ]; field_simp
  have h0 := bhH_pos hr k
  have hre : |(bhPt x r k m).re| ≤ ‖bhPt x r k m‖ := Complex.abs_re_le_norm _
  have e : (bhPt x r k m).re = x + m * (bhH r k / 2) := rfl
  rw [e] at hre
  have h1 : |(m : ℝ) * (bhH r k / 2)| ≤ r := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < bhH r k / 2)]
    exact (mul_le_mul_of_nonneg_right hm' (by positivity)).trans hh.le
  have h2 := abs_sub_abs_le_abs_sub x (-((m : ℝ) * (bhH r k / 2)))
  rw [abs_neg, sub_neg_eq_add] at h2
  linarith

/-- **LWF-2 (LW Prop 2.6, p. 10).** The boundary hitting estimate, `0 < κ < 4`. -/
theorem bdryHitStmt_holds {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) : BdryHitStmt κ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Blueprint.sleOnePointBound_pos_const RS.sleOnePointBound κ hκ hκ4
  set β := 8 / κ - 1 with hβdef
  have hβ : 1 < β := by rw [hβdef, lt_sub_iff_add_lt, lt_div_iff₀ hκ]; linarith
  set q : ℝ := 2 * (1 / 2) ^ β with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    have := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hβ
    rw [Real.rpow_one] at this; rw [hqdef]; linarith
  refine ⟨5 * C₁ * 2 ^ β / (1 - q), by
    have : 0 ≤ (2 : ℝ) ^ β := by positivity
    exact div_nonneg (by positivity) (by linarith), ?_⟩
  intro Ω _ P _ B hB x r hr hrx
  have hx : 0 < |x| := by linarith
  set E : ℕ → ℤ → Set Ω := fun k m => {ω | infDist (bhPt x r k m)
    (sleTrace κ B ω '' Ici 0) < bhH r k} with hEdef
  set I : ℕ → Finset ℤ := fun k => Finset.Icc (-(2 ^ (k + 1) : ℤ)) (2 ^ (k + 1)) with hIdef
  set s : ℝ := 2 * r / |x| with hsdef
  have hs : 0 ≤ s := by positivity
  set A : ℝ := C₁ * s ^ β with hAdef
  have hA : 0 ≤ A := mul_nonneg hC₁0.le (Real.rpow_nonneg hs _)
  -- the covering, almost surely
  have hcov : ∀ᵐ ω ∂P, ω ∈ {ω | ∃ t : ℝ, 0 ≤ t ∧ ‖sleTrace κ B ω t - x‖ < r} →
      ω ∈ ⋃ k, ⋃ m ∈ I k, E k m := by
    filter_upwards [RS.ae_sleTrace_real_eq_zero hB hκ hκ4.le,
      Thm11Area.ae_im_sleTrace_nonneg hB hκ (by linarith),
      Blueprint.RohdeSchrammTraceGen.ae_trace_zero
        (RS.rohdeSchrammTraceGen_of_lt_eight hκ (by linarith)) P B hB] with ω hNR hIm h0
    rintro ⟨t, ht, hd⟩
    have hpos : 0 < (sleTrace κ B ω t).im := by
      refine lt_of_le_of_ne (hIm t ht) (fun hz => ?_)
      have hz0 : sleTrace κ B ω t = 0 := by
        rcases ht.lt_or_eq with htp | ht0
        · exact hNR t htp hz.symm
        · rw [← ht0]; exact h0
      rw [hz0, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hd
      linarith
    obtain ⟨k, m, hm, hdist⟩ := bh_cover hr hpos hd
    refine mem_iUnion.2 ⟨k, mem_iUnion₂.2 ⟨m, hm, ?_⟩⟩
    show infDist _ _ < _
    refine lt_of_le_of_lt (infDist_le_dist_of_mem (mem_image_of_mem _ (mem_Ici.2 ht))) ?_
    rwa [dist_comm]
  -- one point
  have hpt : ∀ k : ℕ, ∀ m ∈ I k, P (E k m) ≤ ENNReal.ofReal (A * ((1 / 2) ^ β) ^ k) := by
    intro k m hm
    have h0 := bhH_pos hr k
    have hz : bhPt x r k m ∈ H := h0
    refine (hC₁ P B hB _ hz _ h0 le_rfl).trans (ENNReal.ofReal_le_ofReal ?_)
    have hwim : (bhPt x r k m).im = bhH r k := rfl
    rw [hwim, div_self h0.ne', Real.one_rpow, mul_one]
    have hwn := bh_norm_ge hr hrx hm
    set w := bhPt x r k m
    have hwn0 : 0 < ‖w‖ := by linarith
    have hq' : bhH r k / ‖w‖ ≤ s * (1 / 2) ^ k := by
      calc bhH r k / ‖w‖ ≤ bhH r k / (|x| / 2) :=
            div_le_div_of_nonneg_left h0.le (by positivity) hwn
        _ = s * (1 / 2) ^ k := by rw [hsdef]; unfold bhH; rw [one_div_pow]; field_simp
    have hpow : (bhH r k / ‖w‖) ^ β ≤ s ^ β * ((1 / 2) ^ β) ^ k := by
      have e : ((1 / 2 : ℝ) ^ β) ^ k = ((1 / 2 : ℝ) ^ k) ^ β := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast ((1 / 2 : ℝ)) k, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]
      rw [e, ← Real.mul_rpow hs (by positivity)]
      exact Real.rpow_le_rpow (div_nonneg h0.le hwn0.le) hq' (by linarith)
    rw [hAdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow hC₁0.le
  -- one layer
  have hlayer : ∀ k : ℕ, P (⋃ m ∈ I k, E k m) ≤ ENNReal.ofReal (5 * A * q ^ k) := by
    intro k
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum (hpt k)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hc : ((I k).card : ℝ) ≤ 5 * 2 ^ k := by
      have : (I k).card = 2 * 2 ^ (k + 1) + 1 := by
        rw [hIdef]; simp only [Int.card_Icc]
        rw [show ((2 : ℤ) ^ (k + 1)) = ((2 ^ (k + 1) : ℕ) : ℤ) by push_cast; ring]
        generalize 2 ^ (k + 1) = N; omega
      rw [this]; push_cast; rw [pow_succ]
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      linarith
    have hX : 0 ≤ A * ((1 / 2) ^ β) ^ k := by positivity
    calc ((I k).card : ℝ) * (A * ((1 / 2) ^ β) ^ k) ≤ 5 * 2 ^ k * (A * ((1 / 2) ^ β) ^ k) :=
          mul_le_mul_of_nonneg_right hc hX
      _ = 5 * A * q ^ k := by rw [hqdef, mul_pow]; ring
  calc P {ω | ∃ t : ℝ, 0 ≤ t ∧ ‖sleTrace κ B ω t - x‖ < r}
      ≤ P (⋃ k, ⋃ m ∈ I k, E k m) := measure_mono_ae hcov
    _ ≤ ∑' k, P (⋃ m ∈ I k, E k m) := measure_iUnion_le _
    _ ≤ ∑' k, ENNReal.ofReal (5 * A * q ^ k) := ENNReal.tsum_le_tsum hlayer
    _ = ENNReal.ofReal (∑' k, 5 * A * q ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          ((summable_geometric_of_lt_one hq0 hq1).mul_left _)).symm
    _ = ENNReal.ofReal (5 * C₁ * 2 ^ β / (1 - q) * (r / |x|) ^ (8 / κ - 1)) := by
        congr 1
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, hAdef, hsdef, ← hβdef,
          mul_div_assoc, Real.mul_rpow (by norm_num) (by positivity)]
        ring

end LWFar
end Thm18Asm
end QuantumZipper
