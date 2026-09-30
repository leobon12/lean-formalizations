import QuantumZipper.Proofs.RS.OnePointFinalKoebe

/-!
# EXT-RS S1-5, geometric part: a Whitney-type cover of the disc `B(z, Im z)`

`blueprint/EXT_RS_BLUEPRINT.md` §5, node S1-5. **Own elementary argument** (DEVIATIONS L-S1,
row S1-5 of the proof-route table): the published range `ε ≤ Im z` (Lawler, *Conformally
Invariant Processes in the Plane*, Thm 7.9, p. 159; Lawler–Zhou arXiv:1006.4936, Prop 2.3) is
obtained there with the sharp Koebe constant; ours (`koebeCovConst = 1/48`) is not sharp, so S1-4
covers only `ε ≤ c₁ Im z`, and the rest is covered by a union bound over countably many small
discs `B(w, c₁ Im w)`.

With `σ = 1 − c₁/4`, `δ = c₁/2`, layer `k` has height `h_k = 2 y σ^{2k}` and points
`w_{k,m} = x + m δ h_k + i h_k`, `|m| ≤ M_k = ⌈σ^{−k}/δ + 1/2⌉`. Every `q ∈ B(z, y)` (`z = x + iy`)
satisfies `dist(q, w_{k,m}) < c₁ Im w_{k,m}` for some `(k, m)` (`whitney_cover`), and if
`8y ≤ |z|` then `|w_{k,m}| ≥ |z|/2` (`norm_wPt_ge`).
-/

noncomputable section

open Set Filter Topology Metric

namespace QuantumZipper.RS

/-- Vertical ratio of the layers: `σ = 1 − c₁/4`. -/
def wSig : ℝ := 1 - onePointC1 / 4

/-- Horizontal spacing factor `δ = c₁/2`. -/
def wDel : ℝ := onePointC1 / 2

/-- Height of layer `k`. -/
def wHeight (y : ℝ) (k : ℕ) : ℝ := 2 * y * wSig ^ (2 * k)

/-- The points of the cover. -/
def wPt (x y : ℝ) (k : ℕ) (m : ℤ) : ℂ := ⟨x + m * wDel * wHeight y k, wHeight y k⟩

/-- Number of points on each side in layer `k`. -/
def wM (k : ℕ) : ℕ := ⌈(wSig ^ k)⁻¹ / wDel + 1 / 2⌉₊

theorem wSig_pos : 0 < wSig := by
  unfold wSig; linarith [onePointC1_le_half]

theorem wSig_lt_one : wSig < 1 := by
  unfold wSig; linarith [onePointC1_pos]

theorem wDel_pos : 0 < wDel := by unfold wDel; linarith [onePointC1_pos]

theorem wDel_le : wDel ≤ 1 / 4 := by unfold wDel; linarith [onePointC1_le_half]

theorem wHeight_pos {y : ℝ} (hy : 0 < y) (k : ℕ) : 0 < wHeight y k := by
  unfold wHeight; have := wSig_pos; positivity

theorem wHeight_eq {y : ℝ} (k : ℕ) : wHeight y k = 2 * y * (wSig ^ k) ^ 2 := by
  unfold wHeight; rw [← pow_mul, mul_comm k 2]

theorem wM_le (k : ℕ) : (wM k : ℝ) ≤ (wSig ^ k)⁻¹ / wDel + 3 / 2 := by
  have h0 : 0 ≤ (wSig ^ k)⁻¹ / wDel + 1 / 2 := by
    have := wSig_pos; have := wDel_pos; positivity
  have := Nat.ceil_lt_add_one h0
  unfold wM; linarith

/-- **Whitney cover.** Every point of `B(z, Im z)` lies within `c₁ Im w` of some cover point `w`. -/
theorem whitney_cover {z q : ℂ} (hy : 0 < z.im) (hq : dist q z < z.im) :
    ∃ k : ℕ, ∃ m ∈ Finset.Icc (-(wM k : ℤ)) (wM k),
      dist q (wPt z.re z.im k m) < onePointC1 * (wPt z.re z.im k m).im := by
  set x := z.re
  set y := z.im
  have hc := onePointC1_pos
  have hσ0 := wSig_pos
  have hσ1 := wSig_lt_one
  have hδ := wDel_pos
  have hρ : 1 - onePointC1 / 2 ≤ wSig ^ 2 := by unfold wSig; nlinarith
  have hdq : (q.re - x) ^ 2 + (q.im - y) ^ 2 < y ^ 2 := by
    rw [Complex.dist_eq] at hq
    have h2 : ‖q - z‖ ^ 2 < y ^ 2 := pow_lt_pow_left₀ hq (norm_nonneg _) two_ne_zero
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at h2
    nlinarith
  have him0 : 0 < q.im := by nlinarith [sq_nonneg (q.re - x)]
  have him2 : q.im < 2 * y := by nlinarith [sq_nonneg (q.re - x)]
  have hσ2 : wSig ^ 2 < 1 := by nlinarith
  have hex : ∃ n : ℕ, 2 * y * (wSig ^ 2) ^ n < q.im := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos him0 (by positivity : (0 : ℝ) < 2 * y)) hσ2
    exact ⟨n, by rwa [lt_div_iff₀ (by positivity), mul_comm] at hn⟩
  classical
  have hn := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0; rw [h0, pow_zero, mul_one] at hn; linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hk1 : ¬ 2 * y * (wSig ^ 2) ^ k < q.im := Nat.find_min hex (by omega)
  rw [hk] at hn
  set h := wHeight y k with hhdef
  have hh : h = 2 * y * (wSig ^ 2) ^ k := by rw [hhdef, wHeight, pow_mul]
  have hh0 : 0 < h := wHeight_pos hy k
  have hup : q.im ≤ h := by rw [hh]; exact not_lt.1 hk1
  have hlow : wSig ^ 2 * h < q.im := by
    rw [hh]
    calc wSig ^ 2 * (2 * y * (wSig ^ 2) ^ k) = 2 * y * (wSig ^ 2) ^ (k + 1) := by ring
      _ < q.im := hn
  have himd : |q.im - h| ≤ onePointC1 / 2 * h := by
    rw [abs_le]; constructor <;> nlinarith
  set u := (q.re - x) / (wDel * h) with hudef
  set m := round u with hmdef
  have hu := abs_sub_round u
  have hwh : 0 < wDel * h := mul_pos hδ hh0
  have hred : |q.re - (x + m * wDel * h)| ≤ onePointC1 / 4 * h := by
    have e : q.re - (x + m * wDel * h) = (wDel * h) * (u - m) := by
      rw [hudef]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hwh]
    calc wDel * h * |u - m| ≤ wDel * h * (1 / 2) := mul_le_mul_of_nonneg_left hu hwh.le
      _ = onePointC1 / 4 * h := by unfold wDel; ring
  refine ⟨k, m, ?_, ?_⟩
  · have hσk : 0 < wSig ^ k := pow_pos hσ0 k
    have hre2 : (q.re - x) ^ 2 < (2 * y * wSig ^ k) ^ 2 := by
      have e : (2 * y * wSig ^ k) ^ 2 = 2 * y * h := by rw [wHeight_eq] at hhdef; rw [hhdef]; ring
      rw [e]; nlinarith
    have hre : |q.re - x| < 2 * y * wSig ^ k := abs_lt_of_sq_lt_sq hre2 (by positivity)
    have huabs : |u| < (wSig ^ k)⁻¹ / wDel := by
      rw [hudef, abs_div, abs_of_pos hwh, div_lt_iff₀ hwh]
      have e : (wSig ^ k)⁻¹ / wDel * (wDel * h) = 2 * y * wSig ^ k := by
        rw [wHeight_eq] at hhdef; rw [hhdef]; field_simp
      rw [e]; exact hre
    have hmu : |(m : ℝ)| ≤ |u| + 1 / 2 := by
      have := abs_sub u (u - m)
      rw [sub_sub_cancel] at this
      linarith [abs_sub_comm u (m : ℝ)]
    have hM : ((|m| : ℤ) : ℝ) ≤ ((wM k : ℤ) : ℝ) := by
      push_cast
      have := Nat.le_ceil ((wSig ^ k)⁻¹ / wDel + 1 / 2)
      unfold wM; linarith
    have hM' : |m| ≤ (wM k : ℤ) := by exact_mod_cast hM
    rw [Finset.mem_Icc]; exact abs_le.1 hM'
  · rw [Complex.dist_eq]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    have e1 : (q - wPt x y k m).re = q.re - (x + m * wDel * h) := by
      simp only [Complex.sub_re, wPt, hhdef]
    have e2 : (q - wPt x y k m).im = q.im - h := by
      simp only [Complex.sub_im, wPt, hhdef]
    have e3 : (wPt x y k m).im = h := rfl
    rw [e1, e2, e3]
    nlinarith

/-- Cover points stay far from `0` when `8 Im z ≤ |z|`. -/
theorem norm_wPt_ge {z : ℂ} (hy : 0 < z.im) (h8 : 8 * z.im ≤ ‖z‖) {k : ℕ} {m : ℤ}
    (hm : m ∈ Finset.Icc (-(wM k : ℤ)) (wM k)) : ‖z‖ / 2 ≤ ‖wPt z.re z.im k m‖ := by
  have hσ0 := wSig_pos
  have hδ := wDel_pos
  have hσk : 0 < wSig ^ k := pow_pos hσ0 k
  have hσk1 : wSig ^ k ≤ 1 := pow_le_one₀ hσ0.le wSig_lt_one.le
  have hm' : |(m : ℝ)| ≤ (wM k : ℝ) := by
    rw [Finset.mem_Icc] at hm
    have : |m| ≤ (wM k : ℤ) := abs_le.2 hm
    exact_mod_cast this
  have hh := wHeight_eq (y := z.im) k
  have hh0 := wHeight_pos hy k
  -- `|m| δ h ≤ 3y`
  have hmd : |(m : ℝ)| * wDel * wHeight z.im k ≤ 3 * z.im := by
    have h1 : |(m : ℝ)| * wDel * wHeight z.im k
        ≤ ((wSig ^ k)⁻¹ / wDel + 3 / 2) * wDel * wHeight z.im k := by
      gcongr; exact hm'.trans (wM_le k)
    have e : ((wSig ^ k)⁻¹ / wDel + 3 / 2) * wDel * wHeight z.im k
        = 2 * z.im * wSig ^ k + 3 * wDel * z.im * (wSig ^ k) ^ 2 := by
      rw [hh]; field_simp
    have h2 : (wSig ^ k) ^ 2 ≤ 1 := pow_le_one₀ hσk.le hσk1
    have h3 := wDel_le
    rw [e] at h1
    have : 3 * wDel * z.im * (wSig ^ k) ^ 2 ≤ z.im := by
      calc 3 * wDel * z.im * (wSig ^ k) ^ 2 ≤ 3 * (1 / 4) * z.im * 1 := by gcongr
        _ ≤ z.im := by linarith
    nlinarith
  have hre := Complex.abs_re_le_norm (wPt z.re z.im k m)
  have hwre : (wPt z.re z.im k m).re = z.re + m * wDel * wHeight z.im k := rfl
  have hz := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos hy] at hz
  have habs : |z.re| - 3 * z.im ≤ |z.re + m * wDel * wHeight z.im k| := by
    have := abs_add_le (z.re + m * wDel * wHeight z.im k) (-(m * wDel * wHeight z.im k))
    rw [add_neg_cancel_right, abs_neg, abs_mul, abs_mul, abs_of_pos hδ, abs_of_pos hh0] at this
    linarith
  rw [hwre] at hre
  linarith

end QuantumZipper.RS
