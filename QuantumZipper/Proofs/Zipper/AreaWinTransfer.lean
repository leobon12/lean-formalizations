import QuantumZipper.Proofs.Zipper.AreaVarSand
import QuantumZipper.Proofs.LQG.LocalRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINDOW-WEDGE (1): deterministic transfer of the window limits under `+ ofFun g`

Target display: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 1.1, p. 9 (window
measures). SW prove it for the free field; the transfer to a field whose circle averages are those
of the free field plus the circle averages of a continuous function `g` is **own elementary
bookkeeping** (no source needed; AGENT_GUIDE cost rule):

* `windowLimits_transfer`: if `qAreaMeasure γ y = e^{γ g} qAreaMeasure γ x`, `g` is continuous on
  `ℍ`, and for every `w ∈ ℍ` and every `0 < ρ < Im w`,
  `evalReg y (fc w ρ) = evalReg x (fc w ρ) + ∫ g d fc(w, ρ)`, then `WindowLimits γ x c c'` implies
  `WindowLimits γ y c c'`.

Route: test `x` against `ψ = φ e^{γ g}`; on `K = tsupport φ` and for window radii below some
`r₀(δ)`, `|∫ g d fc(w, ρ) − g(w)| ≤ δ` (cutoff `LocalRule.exists_cutoff` +
`GoodSample.smooth_unif`), so the window densities of `y` lie between `e^{∓|γ|δ} e^{γ g(w)}` times
those of `x`; then squeeze and let `δ → 0` (`awt_squeeze`).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

/-! ## 1. Window suprema and infima under pointwise comparison -/

theorem awt_biSup_le_mul {S : Set ℝ} {f g : ℝ → ℝ≥0∞} {C : ℝ≥0∞}
    (h : ∀ ρ ∈ S, f ρ ≤ C * g ρ) : ⨆ ρ ∈ S, f ρ ≤ C * ⨆ ρ ∈ S, g ρ :=
  iSup₂_le fun ρ hρ => (h ρ hρ).trans (by gcongr; exact le_iSup₂ (f := fun ρ _ => g ρ) ρ hρ)

theorem awt_mul_biSup_le {S : Set ℝ} {f g : ℝ → ℝ≥0∞} {C : ℝ≥0∞}
    (h : ∀ ρ ∈ S, C * g ρ ≤ f ρ) : C * ⨆ ρ ∈ S, g ρ ≤ ⨆ ρ ∈ S, f ρ := by
  rw [ENNReal.mul_iSup]
  refine iSup_mono fun ρ => ?_
  rw [ENNReal.mul_iSup]
  exact iSup_mono fun hρ => h ρ hρ

theorem awt_mul_biInf_le {S : Set ℝ} {f g : ℝ → ℝ≥0∞} {C : ℝ≥0∞}
    (h : ∀ ρ ∈ S, C * g ρ ≤ f ρ) : C * ⨅ ρ ∈ S, g ρ ≤ ⨅ ρ ∈ S, f ρ :=
  le_iInf₂ fun ρ hρ => (by gcongr; exact iInf₂_le ρ hρ : C * ⨅ ρ ∈ S, g ρ ≤ C * g ρ).trans (h ρ hρ)

theorem awt_biInf_le_mul {S : Set ℝ} {f g : ℝ → ℝ≥0∞} {C : ℝ≥0∞} (hC0 : C ≠ 0) (hC : C ≠ ⊤)
    (h : ∀ ρ ∈ S, f ρ ≤ C * g ρ) : ⨅ ρ ∈ S, f ρ ≤ C * ⨅ ρ ∈ S, g ρ := by
  rw [ENNReal.mul_iInf_of_ne hC0 hC]
  refine iInf_mono fun ρ => ?_
  rw [ENNReal.mul_iInf_of_ne hC0 hC]
  exact iInf_mono fun hρ => h ρ hρ

/-! ## 2. The density comparison at one radius -/

theorem awt_dens_upper {γ : ℝ} {x y : FieldSample} {ρ : ℝ} {w : ℂ} {S g0 δ : ℝ}
    (hρ : 0 < ρ) (he : evalReg y (foldedCircle w ρ) = evalReg x (foldedCircle w ρ) + S)
    (hS : |S - g0| ≤ δ) :
    ENNReal.ofReal (areaDens γ y ρ w) ≤
      ENNReal.ofReal (Real.exp (|γ| * δ) * Real.exp (γ * g0)) *
        ENNReal.ofReal (areaDens γ x ρ w) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : γ * S ≤ |γ| * δ + γ * g0 := by
    have := mul_le_mul_of_nonneg_left hS (abs_nonneg γ)
    linarith [le_abs_self (γ * (S - g0)), abs_mul γ (S - g0)]
  have h3 : 0 ≤ ρ ^ (γ ^ 2 / 2) * Real.exp (γ * evalReg x (foldedCircle w ρ)) :=
    mul_nonneg (Real.rpow_nonneg hρ.le _) (Real.exp_pos _).le
  unfold areaDens
  rw [he]
  calc ρ ^ (γ ^ 2 / 2) * Real.exp (γ * (evalReg x (foldedCircle w ρ) + S))
      = (ρ ^ (γ ^ 2 / 2) * Real.exp (γ * evalReg x (foldedCircle w ρ))) * Real.exp (γ * S) := by
        rw [mul_add, Real.exp_add]; ring
    _ ≤ (ρ ^ (γ ^ 2 / 2) * Real.exp (γ * evalReg x (foldedCircle w ρ))) *
          Real.exp (|γ| * δ + γ * g0) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) h3
    _ = Real.exp (|γ| * δ) * Real.exp (γ * g0) *
          (ρ ^ (γ ^ 2 / 2) * Real.exp (γ * evalReg x (foldedCircle w ρ))) := by
        rw [Real.exp_add]; ring

theorem awt_dens_lower {γ : ℝ} {x y : FieldSample} {ρ : ℝ} {w : ℂ} {S g0 δ : ℝ}
    (hρ : 0 < ρ) (he : evalReg y (foldedCircle w ρ) = evalReg x (foldedCircle w ρ) + S)
    (hS : |S - g0| ≤ δ) :
    ENNReal.ofReal (Real.exp (-(|γ| * δ)) * Real.exp (γ * g0)) *
        ENNReal.ofReal (areaDens γ x ρ w) ≤ ENNReal.ofReal (areaDens γ y ρ w) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : -(|γ| * δ) + γ * g0 ≤ γ * S := by
    have := mul_le_mul_of_nonneg_left hS (abs_nonneg γ)
    linarith [neg_abs_le (γ * (S - g0)), abs_mul γ (S - g0)]
  have h3 : 0 ≤ ρ ^ (γ ^ 2 / 2) * Real.exp (γ * evalReg x (foldedCircle w ρ)) :=
    mul_nonneg (Real.rpow_nonneg hρ.le _) (Real.exp_pos _).le
  unfold areaDens
  rw [he]
  calc Real.exp (-(|γ| * δ)) * Real.exp (γ * g0) *
          (ρ ^ (γ ^ 2 / 2) * Real.exp (γ * evalReg x (foldedCircle w ρ)))
      = (ρ ^ (γ ^ 2 / 2) * Real.exp (γ * evalReg x (foldedCircle w ρ))) *
          Real.exp (-(|γ| * δ) + γ * g0) := by
        rw [Real.exp_add]; ring
    _ ≤ (ρ ^ (γ ^ 2 / 2) * Real.exp (γ * evalReg x (foldedCircle w ρ))) * Real.exp (γ * S) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) h3
    _ = ρ ^ (γ ^ 2 / 2) * Real.exp (γ * (evalReg x (foldedCircle w ρ) + S)) := by
        rw [mul_add, Real.exp_add]; ring

/-! ## 3. Uniform approximation by circle averages on compacts of `ℍ` -/

theorem awt_unif {g : ℂ → ℝ} (hg : ContinuousOn g H) {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ H) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ w ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < r0 →
      ρ < w.im ∧ |∫ u, g u ∂foldedCircle w ρ - g w| ≤ δ := by
  obtain ⟨δ₁, hδ₁, φ', hφ', heq⟩ :=
    LocalRule.exists_cutoff isOpen_H (hg.mono inter_subset_left) hK hKH
  have hs := GoodSample.smooth_unif hφ' hK (hKH.trans H_subset_Hbar) δ hδ
  obtain ⟨r1, hr1, hr1'⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hs
  obtain ⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ w ∈ K, m ≤ w.im := by
    rcases K.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨w0, hw0, hmin⟩ := hK.exists_isMinOn h Complex.continuous_im.continuousOn
      exact ⟨w0.im, hKH hw0, fun w hw => hmin hw⟩
  refine ⟨min r1 (min m δ₁), by positivity, fun w hw ρ hρ hρr => ⟨?_, ?_⟩⟩
  · exact lt_of_lt_of_le (hρr.trans_le ((min_le_right _ _).trans (min_le_left _ _))) (hmK w hw)
  · have hρδ : ρ ≤ δ₁ := (hρr.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
    have hc : ofFun g (foldedCircle w ρ) = ofFun φ' (foldedCircle w ρ) :=
      LocalRule.ofFun_fc_congr (H_subset_Hbar (hKH hw)) hρ (fun u hu =>
        (heq (Metric.mem_cthickening_of_dist_le u w δ₁ K hw
          ((Metric.mem_closedBall.1 hu).trans hρδ))).symm)
    have hc' : ∫ u, g u ∂foldedCircle w ρ = ∫ u, φ' u ∂foldedCircle w ρ := hc
    rw [hc', ← heq (Metric.self_subset_cthickening K hw)]
    exact (hr1' ⟨hρ, hρr.trans_le (min_le_left _ _)⟩ w hw).le

/-! ## 4. Small helpers -/

theorem awt_winHi_lt {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ j in atTop, winHi N j < r := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : Tendsto (fun j : ℕ => -(j : ℝ) / N) atTop atBot :=
    (tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const hNpos)).congr fun j => by
        simp [neg_div]
  exact ((tendsto_rpow_atBot_of_base_gt_one 2 one_lt_two).comp h1).eventually (gt_mem_nhds hr)

theorem awt_winLo_pos (N j : ℕ) : 0 < winLo N j := Real.rpow_pos_of_pos two_pos _

theorem awt_qAreaMeasure_compl_H (γ : ℝ) (x : FieldSample) : qAreaMeasure γ x Hᶜ = 0 := by
  unfold qAreaMeasure
  split_ifs with h
  · exact h.choose_spec.1
  · simp

/-- The squeeze: `e^{-kδ} b_j ≤ a_j ≤ e^{kδ} b_j` eventually, for every `δ > 0`, and `b_j → L < ∞`
give `a_j → L`. -/
theorem awt_squeeze {a b : ℕ → ℝ≥0∞} {L : ℝ≥0∞} {k : ℝ} (hL : L ≠ ⊤)
    (hb : Tendsto b atTop (𝓝 L))
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, ENNReal.ofReal (Real.exp (-(k * δ))) * b j ≤ a j ∧
      a j ≤ ENNReal.ofReal (Real.exp (k * δ)) * b j) :
    Tendsto a atTop (𝓝 L) := by
  have hlim : ∀ s : ℝ, Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.exp (s * δ)) * L) (𝓝 0)
      (𝓝 L) := by
    intro s
    have hc : Continuous fun δ : ℝ => ENNReal.ofReal (Real.exp (s * δ)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    have h1 : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.exp (s * δ))) (𝓝 0) (𝓝 1) := by
      simpa using hc.tendsto 0
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hL)
  have hpick : ∀ s : ℝ, ∀ V ∈ 𝓝 L, ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal (Real.exp (s * δ)) * L ∈ V := by
    intro s V hV
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 ((hlim s).eventually hV)
    refine ⟨ε / 2, by positivity, hball ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  rw [tendsto_order]
  constructor
  · intro u hu
    obtain ⟨δ, hδ, hδu⟩ := hpick (-k) _ (lt_mem_nhds hu)
    have hbl : Tendsto (fun j => ENNReal.ofReal (Real.exp (-k * δ)) * b j) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-k * δ)) * L)) :=
      ENNReal.Tendsto.const_mul hb (Or.inr ENNReal.ofReal_ne_top)
    filter_upwards [hbl.eventually (lt_mem_nhds hδu), h δ hδ] with j h1 h2
    refine h1.trans_le ?_
    simpa [neg_mul] using h2.1
  · intro u hu
    obtain ⟨δ, hδ, hδu⟩ := hpick k _ (gt_mem_nhds hu)
    have hbl : Tendsto (fun j => ENNReal.ofReal (Real.exp (k * δ)) * b j) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (k * δ)) * L)) :=
      ENNReal.Tendsto.const_mul hb (Or.inr ENNReal.ofReal_ne_top)
    filter_upwards [hbl.eventually (gt_mem_nhds hδu), h δ hδ] with j h1 h2
    exact h2.2.trans_lt h1

/-! ## 5. The transfer -/

theorem awt_test {φ g : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφH : tsupport φ ⊆ H) (hg : ContinuousOn g H) (γ : ℝ) :
    Continuous (fun z => φ z * Real.exp (γ * g z)) ∧
      HasCompactSupport (fun z => φ z * Real.exp (γ * g z)) ∧
      tsupport (fun z => φ z * Real.exp (γ * g z)) ⊆ H := by
  have hts : tsupport (fun z => φ z * Real.exp (γ * g z)) ⊆ tsupport φ :=
    tsupport_mul_subset_left
  exact ⟨ContinuousOn.continuous_of_tsupport_subset
    (hφ.continuousOn.mul (continuousOn_const.mul hg).rexp) isOpen_H (hts.trans hφH),
    hφc.mul_right, hts.trans hφH⟩

/-- The four window bounds at one point, from the density comparison on the whole window. -/
theorem awt_win_bounds {γ δ g0 : ℝ} {x y : FieldSample} {N j : ℕ} {w : ℂ} {S : ℝ → ℝ}
    (hS : ∀ ρ ∈ Icc (winLo N j) (winHi N j),
      evalReg y (foldedCircle w ρ) = evalReg x (foldedCircle w ρ) + S ρ ∧ |S ρ - g0| ≤ δ) :
    supWin γ y N j w ≤
        ENNReal.ofReal (Real.exp (|γ| * δ) * Real.exp (γ * g0)) * supWin γ x N j w ∧
      ENNReal.ofReal (Real.exp (-(|γ| * δ)) * Real.exp (γ * g0)) * supWin γ x N j w ≤
        supWin γ y N j w ∧
      infWin γ y N j w ≤
        ENNReal.ofReal (Real.exp (|γ| * δ) * Real.exp (γ * g0)) * infWin γ x N j w ∧
      ENNReal.ofReal (Real.exp (-(|γ| * δ)) * Real.exp (γ * g0)) * infWin γ x N j w ≤
        infWin γ y N j w := by
  have hp : ∀ ρ ∈ Icc (winLo N j) (winHi N j), 0 < ρ := fun ρ hρ =>
    (awt_winLo_pos N j).trans_le hρ.1
  have hC0 : ENNReal.ofReal (Real.exp (|γ| * δ) * Real.exp (γ * g0)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  unfold supWin infWin
  exact ⟨awt_biSup_le_mul fun ρ hρ => awt_dens_upper (hp ρ hρ) (hS ρ hρ).1 (hS ρ hρ).2,
    awt_mul_biSup_le fun ρ hρ => awt_dens_lower (hp ρ hρ) (hS ρ hρ).1 (hS ρ hρ).2,
    awt_biInf_le_mul hC0 ENNReal.ofReal_ne_top fun ρ hρ =>
      awt_dens_upper (hp ρ hρ) (hS ρ hρ).1 (hS ρ hρ).2,
    awt_mul_biInf_le fun ρ hρ => awt_dens_lower (hp ρ hρ) (hS ρ hρ).1 (hS ρ hρ).2⟩

/-- Pointwise window-integrand bounds, eventually in `j`, for a fixed test function. -/
theorem awt_key {γ : ℝ} {x y : FieldSample} {g φ : ℂ → ℝ} (hg : ContinuousOn g H)
    (hev : ∀ w ∈ H, ∀ ρ : ℝ, 0 < ρ → ρ < w.im →
      evalReg y (foldedCircle w ρ) = evalReg x (foldedCircle w ρ) + ∫ u, g u ∂foldedCircle w ρ)
    (hφc : HasCompactSupport φ) (hφH : tsupport φ ⊆ H) (hφ0 : ∀ w, 0 ≤ φ w)
    {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ w : ℂ,
      supWin γ y N j w * ENNReal.ofReal (φ w) ≤ ENNReal.ofReal (Real.exp (|γ| * δ)) *
          (supWin γ x N j w * ENNReal.ofReal (φ w * Real.exp (γ * g w))) ∧
      ENNReal.ofReal (Real.exp (-(|γ| * δ))) *
          (supWin γ x N j w * ENNReal.ofReal (φ w * Real.exp (γ * g w))) ≤
        supWin γ y N j w * ENNReal.ofReal (φ w) ∧
      infWin γ y N j w * ENNReal.ofReal (φ w) ≤ ENNReal.ofReal (Real.exp (|γ| * δ)) *
          (infWin γ x N j w * ENNReal.ofReal (φ w * Real.exp (γ * g w))) ∧
      ENNReal.ofReal (Real.exp (-(|γ| * δ))) *
          (infWin γ x N j w * ENNReal.ofReal (φ w * Real.exp (γ * g w))) ≤
        infWin γ y N j w * ENNReal.ofReal (φ w) := by
  obtain ⟨r0, hr0, hr0'⟩ := awt_unif hg hφc hφH hδ
  filter_upwards [awt_winHi_lt hN hr0] with j hj w
  by_cases hw : w ∈ tsupport φ
  · have hS : ∀ ρ ∈ Icc (winLo N j) (winHi N j),
        evalReg y (foldedCircle w ρ) = evalReg x (foldedCircle w ρ) +
          ∫ u, g u ∂foldedCircle w ρ ∧ |∫ u, g u ∂foldedCircle w ρ - g w| ≤ δ := by
      intro ρ hρ
      have hρ0 : 0 < ρ := (awt_winLo_pos N j).trans_le hρ.1
      obtain ⟨h1, h2⟩ := hr0' w hw ρ hρ0 (hρ.2.trans_lt hj)
      exact ⟨hev w (hφH hw) ρ hρ0 h1, h2⟩
    obtain ⟨b1, b2, b3, b4⟩ := awt_win_bounds (γ := γ) hS
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le] at b1 b2 b3 b4
    rw [ENNReal.ofReal_mul (hφ0 w)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc supWin γ y N j w * ENNReal.ofReal (φ w)
          ≤ ENNReal.ofReal (Real.exp (|γ| * δ)) * ENNReal.ofReal (Real.exp (γ * g w)) *
              supWin γ x N j w * ENNReal.ofReal (φ w) := by gcongr
        _ = _ := by ring
    · calc _ = ENNReal.ofReal (Real.exp (-(|γ| * δ))) * ENNReal.ofReal (Real.exp (γ * g w)) *
              supWin γ x N j w * ENNReal.ofReal (φ w) := by ring
        _ ≤ _ := by gcongr
    · calc infWin γ y N j w * ENNReal.ofReal (φ w)
          ≤ ENNReal.ofReal (Real.exp (|γ| * δ)) * ENNReal.ofReal (Real.exp (γ * g w)) *
              infWin γ x N j w * ENNReal.ofReal (φ w) := by gcongr
        _ = _ := by ring
    · calc _ = ENNReal.ofReal (Real.exp (-(|γ| * δ))) * ENNReal.ofReal (Real.exp (γ * g w)) *
              infWin γ x N j w * ENNReal.ofReal (φ w) := by ring
        _ ≤ _ := by gcongr
  · have h0 : φ w = 0 := image_eq_zero_of_notMem_tsupport hw
    simp [h0]

/-- Integrated form of the bounds. -/
theorem awt_int_bounds {μ : Measure ℂ} {c : ℝ} {E E' : ℝ≥0∞} (hE : E ≠ ⊤) (hE' : E' ≠ ⊤)
    {F G : ℂ → ℝ≥0∞} (h1 : ∀ w, F w ≤ E * G w) (h2 : ∀ w, E' * G w ≤ F w) :
    E' * (ENNReal.ofReal c * ∫⁻ w, G w ∂μ) ≤ ENNReal.ofReal c * ∫⁻ w, F w ∂μ ∧
      ENNReal.ofReal c * ∫⁻ w, F w ∂μ ≤ E * (ENNReal.ofReal c * ∫⁻ w, G w ∂μ) := by
  constructor
  · rw [mul_left_comm, ← lintegral_const_mul' _ _ hE']
    exact mul_le_mul_of_nonneg_left (lintegral_mono h2) (zero_le)
  · rw [mul_left_comm E, ← lintegral_const_mul' _ _ hE]
    exact mul_le_mul_of_nonneg_left (lintegral_mono h1) (zero_le)

/-- **Transfer of the window limits** (own elementary bookkeeping; the limits themselves are SW,
arXiv:1605.06171, proof of Thm 1.1, p. 9). -/
theorem windowLimits_transfer {γ : ℝ} {x y : FieldSample} {c c' : ℕ → ℝ} {g : ℂ → ℝ}
    (hg : ContinuousOn g H)
    (hμ : qAreaMeasure γ y =
      (qAreaMeasure γ x).withDensity fun z => ENNReal.ofReal (Real.exp (γ * g z)))
    (hev : ∀ w ∈ H, ∀ ρ : ℝ, 0 < ρ → ρ < w.im →
      evalReg y (foldedCircle w ρ) = evalReg x (foldedCircle w ρ) + ∫ u, g u ∂foldedCircle w ρ)
    (hx : WindowLimits γ x c c') : WindowLimits γ y c c' := by
  intro N hN φ hφ hφc hφH hφ0
  obtain ⟨hψ, hψc, hψH⟩ := awt_test hφ hφc hφH hg γ
  have hψ0 : ∀ z, 0 ≤ φ z * Real.exp (γ * g z) := fun z =>
    mul_nonneg (hφ0 z) (Real.exp_pos _).le
  have hint : ∫ z, φ z ∂qAreaMeasure γ y =
      ∫ z, φ z * Real.exp (γ * g z) ∂qAreaMeasure γ x := by
    rw [hμ, LocalRule.integral_withDensity_exp_of_continuousOn (w := fun z => γ * g z) isOpen_H
      (awt_qAreaMeasure_compl_H γ x) (continuousOn_const.mul hg)]
    congr 1
    funext z
    ring
  obtain ⟨hs, hi⟩ := hx N hN _ hψ hψc hψH hψ0
  rw [hint]
  constructor
  · refine awt_squeeze (k := |γ|) ENNReal.ofReal_ne_top hs fun δ hδ => ?_
    filter_upwards [awt_key (γ := γ) (x := x) (y := y) hg hev hφc hφH hφ0 hN hδ] with j hj
    exact awt_int_bounds ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (fun w => (hj w).1)
      (fun w => (hj w).2.1)
  · refine awt_squeeze (k := |γ|) ENNReal.ofReal_ne_top hi fun δ hδ => ?_
    filter_upwards [awt_key (γ := γ) (x := x) (y := y) hg hev hφc hφH hφ0 hN hδ] with j hj
    exact awt_int_bounds ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (fun w => (hj w).2.2.1)
      (fun w => (hj w).2.2.2)

end QuantumZipper.E6
