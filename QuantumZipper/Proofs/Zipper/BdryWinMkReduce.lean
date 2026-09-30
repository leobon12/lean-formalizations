import QuantumZipper.Proofs.Zipper.BdryWinMkCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-W1 (2): the boundary window split from the boundary window Markov structure

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 4.2, pp. 18–19 (the boundary
measure "as in the proof of Theorem 1.1", p. 9), via the proof of Lemma 3.1, (3.1)–(3.2) and the
one-point estimates on pp. 7–8.

Boundary copy of `E6.winSplit_of_markovData` (`AreaWinSWReduce.lean`) with index set `ℝ`
(Lebesgue measure), boundary densities `bdryDens` and no exceptional set. The estimate is the
core bound `winB_core_bound` with the `TwoRadius` truncation (`trl_exponent_identities`:
`α = (2+γ)/2`, `θg = max 0 ((3γ-2)/4)`, `θb = (2-γ)/4`), `L = 2 Lw = log 2^{j/N}`, and
near-diagonal measure `≤ 2 δ |S|` with `δ = 2 · 2^{-j/N} = 2 e^{-L}`: the good part is
`O(e^{(γ²/2 - θg² - 1) L})`, the bad part `O(e^{-((2-γ)²/16) L})`, both geometric in `j`.

The pathwise comparison `bwin_path_le` is own elementary bookkeeping (cost rule).

Main result: `bdryWinSplit_of_markovData`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.F1

open E6 TwoRadius

/-- **Pathwise boundary window comparison** (no exceptional set): if `c W = d (1 + g)` on
`S ⊇ supp φ`, then `c ∫ W φ` and `∫ d φ` differ by at most `|∫_S φ d g|`. -/
theorem bwin_path_le {S : Set ℝ} (hS : MeasurableSet S) {φ d g : ℝ → ℝ} {W : ℝ → ℝ≥0∞} {c : ℝ}
    (hφ0 : ∀ u, 0 ≤ φ u) (hφS : ∀ u, u ∉ S → φ u = 0)
    (hid : ∀ u ∈ S, 0 ≤ d u ∧ 0 ≤ 1 + g u ∧
      ENNReal.ofReal c * W u = ENNReal.ofReal (d u * (1 + g u)))
    (hi1 : IntegrableOn (fun u => φ u * d u) S)
    (hi2 : IntegrableOn (fun u => φ u * (d u * g u)) S) :
    ENNReal.ofReal c * (∫⁻ u, W u * ENNReal.ofReal (φ u))
        ≤ (∫⁻ u, ENNReal.ofReal (d u * φ u)) + ENNReal.ofReal |∫ u in S, φ u * (d u * g u)| ∧
      (∫⁻ u, ENNReal.ofReal (d u * φ u))
        ≤ ENNReal.ofReal c * (∫⁻ u, W u * ENNReal.ofReal (φ u)) +
          ENNReal.ofReal |∫ u in S, φ u * (d u * g u)| := by
  set F : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal c * (W u * ENNReal.ofReal (φ u)) with hF
  set Fb : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (d u * φ u) with hFb
  have hsuppF : Function.support F ⊆ S := by
    intro u hu
    by_contra huS
    exact hu (by simp [hF, hφS u huS])
  have hsuppFb : Function.support Fb ⊆ S := by
    intro u hu
    by_contra huS
    exact hu (by simp [hFb, hφS u huS])
  have eA : ENNReal.ofReal c * ∫⁻ u, W u * ENNReal.ofReal (φ u) = ENNReal.ofReal
      ((∫ u in S, φ u * d u) + ∫ u in S, φ u * (d u * g u)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    change ∫⁻ u, F u = _
    rw [← setLIntegral_eq_of_support_subset hsuppF]
    have hFS : ∀ u ∈ S, F u = ENNReal.ofReal (φ u * d u + φ u * (d u * g u)) := by
      intro u hu
      obtain ⟨hd, hg, hW⟩ := hid u hu
      simp only [hF]
      rw [← mul_assoc, hW, ← ENNReal.ofReal_mul (mul_nonneg hd hg)]
      congr 1; ring
    rw [setLIntegral_congr_fun hS (fun u hu => hFS u hu), ← integral_add hi1 hi2]
    refine (ofReal_integral_eq_lintegral_ofReal (hi1.add hi2) ?_).symm
    refine (ae_restrict_iff' hS).2 (ae_of_all _ fun u hu => ?_)
    obtain ⟨hd, hg, -⟩ := hid u hu
    have : φ u * d u + φ u * (d u * g u) = φ u * (d u * (1 + g u)) := by ring
    show 0 ≤ φ u * d u + φ u * (d u * g u)
    rw [this]; exact mul_nonneg (hφ0 u) (mul_nonneg hd hg)
  have eB : ∫⁻ u, ENNReal.ofReal (d u * φ u) = ENNReal.ofReal (∫ u in S, φ u * d u) := by
    change ∫⁻ u, Fb u = _
    rw [← setLIntegral_eq_of_support_subset hsuppFb,
      setLIntegral_congr_fun hS (fun u _ => show Fb u = ENNReal.ofReal (φ u * d u) by
        simp only [hFb]; rw [mul_comm])]
    refine (ofReal_integral_eq_lintegral_ofReal hi1 ?_).symm
    exact (ae_restrict_iff' hS).2 (ae_of_all _ fun u hu => mul_nonneg (hφ0 u) (hid u hu).1)
  rw [eA, eB]
  set b := ∫ u in S, φ u * (d u * g u)
  exact ⟨(ENNReal.ofReal_le_ofReal (by linarith [le_abs_self b])).trans ENNReal.ofReal_add_le,
    (ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le b])).trans ENNReal.ofReal_add_le⟩

/-- `2^{-j/N} = e^{-2 j (log 2 / (2N))}`. -/
theorem winHi_eq_exp_Lw {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    winHi N j = rexp (-2 * ((j : ℝ) * (Real.log 2 / (2 * N)))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [winHi, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp

/-- `1 - (γ²/2 - θg²) > 0` for `θg = max 0 ((3γ-2)/4)`, `0 < γ < 2`. -/
theorem bwinExp_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    0 < 1 - (γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2) := by
  rcases le_total ((3 * γ - 2) / 4) 0 with h | h
  · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right h]; nlinarith

/-- A.s. integrability of the coarse densities `e^{-(γ²/4) L + (γ/2) U}` on a finite-measure
`S ⊆ ℝ` (first moment `≤ e^{γ² K/8}`); boundary copy of `E6.ae_integrableOn_coarse`. -/
theorem ae_integrableOn_coarseB {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : Set ℝ} {δ K Q L : ℝ} {v : ℝ → ℝ≥0} {U G : ℝ → Ω → ℝ}
    (h : WinHypB P S δ K Q (fun _ => L) v U G) (hS : MeasurableSet S) (hSf : volume S < ∞)
    (γ : ℝ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun t => rexp (-(γ ^ 2 / 4) * L + γ / 2 * U t ω)) S := by
  set b := -(γ ^ 2 / 4) * L
  have hmeas : Measurable (fun p : ℝ × Ω => ENNReal.ofReal (rexp (b + γ / 2 * U p.1 p.2))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (measurable_const.add (measurable_const.mul h.measU)))
  have hpt : ∀ t ∈ S, ∫⁻ ω, ENNReal.ofReal (rexp (b + γ / 2 * U t ω)) ∂P
      ≤ ENNReal.ofReal (rexp (γ ^ 2 * K / 8)) := by
    intro t ht
    rw [(h.lawU t ht).lintegral_comp (f := fun x => ENNReal.ofReal (rexp (b + γ / 2 * x)))
      (by fun_prop),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_add_gaussianReal _ _ _)
        (ae_of_all _ fun _ => (exp_pos _).le),
      integral_exp_mul_add_gaussianReal]
    apply ENNReal.ofReal_le_ofReal
    apply exp_le_exp.2
    have hv := h.varU t ht
    simp only [b]
    nlinarith [sq_nonneg γ]
  have htot : ∫⁻ ω, (∫⁻ t in S, ENNReal.ofReal (rexp (b + γ / 2 * U t ω))) ∂P ≠ ∞ := by
    rw [lintegral_lintegral_swap (f := fun ω t => ENNReal.ofReal (rexp (b + γ / 2 * U t ω)))
      (hmeas.comp measurable_swap).aemeasurable]
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (rexp (γ ^ 2 * K / 8)) * volume S)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf.ne)
      ((setLIntegral_mono_ae' hS (ae_of_all _ fun t ht => hpt t ht)).trans_eq ?_)
    rw [setLIntegral_const]
  have hm2 : Measurable (fun ω => ∫⁻ t in S, ENNReal.ofReal (rexp (b + γ / 2 * U t ω))) :=
    hmeas.lintegral_prod_left'
  filter_upwards [ae_lt_top hm2 htot] with ω hω
  refine ⟨((Real.continuous_exp.measurable.comp (measurable_const.add
    (measurable_const.mul (h.measU.comp (measurable_id.prodMk measurable_const)))))).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (exp_pos _).le)]
  exact hω

/-- **SW's boundary window estimate for one test function** (proof of Thm 4.2, pp. 18–19, as in
the proof of Thm 1.1, p. 9, with (3.1)–(3.2) and p. 8) from the boundary window Markov structure
on `tsupport φ`. -/
theorem bdryWinSplit_of_markovData {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {γ c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {N : ℕ} (hN : 1 ≤ N) {win : FieldSample → ℕ → ℝ → ℝ≥0∞} {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hD : BdryWinMarkovData P X γ c N win (tsupport φ)) :
    E6.WinSplit P (fun j ω => bWinInt c (win (X ω) j) φ) (fun j ω => bWinRef γ (X ω) N j φ) := by
  obtain ⟨K, Q, j₀, U, G, v, hQ, hW, hid⟩ := hD
  set S := tsupport φ with hSdef
  have hSc : IsCompact S := hφs
  have hSm : MeasurableSet S := (isClosed_tsupport φ).measurableSet
  have hSf : volume S < ∞ := hSc.measure_lt_top
  have hφm : Measurable φ := hφc.measurable
  obtain ⟨M, hM⟩ := hφc.bounded_above_of_compact_support hφs
  have hMabs : ∀ t, |φ t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMabs 0)
  have hφS : ∀ u, u ∉ S → φ u = 0 := fun u hu => image_eq_zero_of_notMem_tsupport hu
  obtain ⟨e1, e2, e3⟩ := trl_exponent_identities hγ hγ2
  set θg := max 0 ((3 * γ - 2) / 4) with hθg
  set κ := Real.log 2 / (2 * N) with hκdef
  have hκ : 0 < κ := div_pos (Real.log_pos one_lt_two) (by positivity)
  have hδ : ∀ j : ℕ, (0 : ℝ) ≤ 2 * winHi N j := fun j => by unfold winHi; positivity
  have hcore := fun j (hj : j₀ ≤ j) =>
    winB_core_bound (γ := γ) (α := (2 + γ) / 2) (θg := θg) (θb := (2 - γ) / 4)
      (Lmin := 2 * Lw N j) (Lmax := 2 * Lw N j) (M := M)
      (D := 2 * (2 * winHi N j) * volume.real S) (f := φ)
      hγ.le (le_max_left 0 _) (by linarith) hQ (by rw [e1]; exact e2)
      (by rw [e3]; nlinarith) hSm hSf hφm hMabs (hW j hj)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl) (measureReal_near_diag_le hSf (hδ j))
  set Zr : ℕ → Ω → ℝ := fun j ω =>
    |∫ t in S, bwG γ ((2 + γ) / 2) φ (fun _ => 2 * Lw N j) (U j) (G j) t ω| with hZr
  set Yr : ℕ → Ω → ℝ := fun j ω =>
    ∫ t in S, |bwB γ ((2 + γ) / 2) φ (fun _ => 2 * Lw N j) (U j) (G j) t ω| with hYr
  have hmZ : ∀ j, j₀ ≤ j → Measurable (Zr j) := fun j hj =>
    continuous_abs.measurable.comp
      ((measurable_bwG hφm (hW j hj)).stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict S)).measurable
  have hmY : ∀ j, j₀ ≤ j → Measurable (Yr j) := fun j hj =>
    ((continuous_abs.measurable.comp (measurable_bwB hφm (hW j hj))).stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict S)).measurable
  refine ⟨fun j ω => if j₀ ≤ j then ENNReal.ofReal (Yr j ω) else 0,
    fun j ω => if j₀ ≤ j then ENNReal.ofReal (Zr j ω) else 0, ?_, ?_, ?_, ?_, j₀, ?_⟩
  · intro j
    by_cases hj : j₀ ≤ j
    · simp only [hj, ite_true]
      exact (ENNReal.measurable_ofReal.comp (hmY j hj)).aemeasurable
    · simp only [hj, ite_false]; exact aemeasurable_const
  · intro j
    by_cases hj : j₀ ≤ j
    · simp only [hj, ite_true]
      exact (ENNReal.measurable_ofReal.comp (hmZ j hj)).aemeasurable
    · simp only [hj, ite_false]; exact aemeasurable_const
  · -- `Σ E Y_j < ∞`
    set Cb := M * ((1 + Q) / 2 * rexp ((γ / 2 + (2 - γ) / 4) ^ 2 * K / 2)) * volume.real S
    have hb : ∀ j, ∫⁻ ω, (if j₀ ≤ j then ENNReal.ofReal (Yr j ω) else 0) ∂P
        ≤ ENNReal.ofReal (Cb * rexp (-((2 - γ) ^ 2 / 8) * ((j : ℝ) * κ))) := by
      intro j
      by_cases hj : j₀ ≤ j
      · simp only [hj, ite_true]
        obtain ⟨-, hY1, -, -, hYint, -⟩ := hcore j hj
        rw [← ofReal_integral_eq_lintegral_ofReal hYint
            (ae_of_all _ fun ω => integral_nonneg fun _ => abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (hY1.trans (le_of_eq ?_))
        rw [e3]
        simp only [Cb, Lw, κ]
        rw [show -((2 - γ) ^ 2 / 16) * (2 * ((j : ℝ) * (Real.log 2 / (2 * N))))
          = -((2 - γ) ^ 2 / 8) * ((j : ℝ) * (Real.log 2 / (2 * N))) by ring]
        ring
      · simp only [hj, ite_false, lintegral_zero]; exact bot_le
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
    exact tsum_ofReal_exp_ne_top (by positivity) (by nlinarith) hκ
  · -- `Σ E Z_j² < ∞`
    set eg := 2 * (1 - (γ ^ 2 / 2 - θg ^ 2))
    have heg : 0 < eg := by have := bwinExp_pos hγ hγ2; simp only [eg]; linarith
    set Cg := M ^ 2 * (Q * rexp ((γ - θg) ^ 2 * K / 2)) * (4 * volume.real S)
    have hb : ∀ j, ∫⁻ ω, (if j₀ ≤ j then ENNReal.ofReal (Zr j ω) else 0) ^ 2 ∂P
        ≤ ENNReal.ofReal (Cg * rexp (-eg * ((j : ℝ) * κ))) := by
      intro j
      by_cases hj : j₀ ≤ j
      · simp only [hj, ite_true]
        obtain ⟨hZ2, -, -, hZint, -, -⟩ := hcore j hj
        have e : ∀ ω, ENNReal.ofReal (Zr j ω) ^ 2 = ENNReal.ofReal
            ((∫ t in S, bwG γ ((2 + γ) / 2) φ (fun _ => 2 * Lw N j) (U j) (G j) t ω) ^ 2) := by
          intro ω
          rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
        simp_rw [e]
        rw [← ofReal_integral_eq_lintegral_ofReal hZint (ae_of_all _ fun _ => sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (hZ2.trans (le_of_eq ?_))
        rw [e1, winHi_eq_exp_Lw hN j]
        have hx : rexp ((γ ^ 2 / 2 - θg ^ 2) * (2 * Lw N j)) * rexp (-2 * ((j : ℝ) * κ))
            = rexp (-eg * ((j : ℝ) * κ)) := by
          rw [← Real.exp_add]; congr 1; simp only [eg, Lw, κ]; ring
        calc M ^ 2 * (Q * (rexp ((γ - θg) ^ 2 * K / 2) *
              rexp ((γ ^ 2 / 2 - θg ^ 2) * (2 * Lw N j)))) *
              (2 * (2 * rexp (-2 * ((j : ℝ) * (Real.log 2 / (2 * N))))) * volume.real S)
            = Cg * (rexp ((γ ^ 2 / 2 - θg ^ 2) * (2 * Lw N j)) * rexp (-2 * ((j : ℝ) * κ))) := by
              simp only [Cg, κ]; ring
          _ = _ := by rw [hx]
      · simp only [hj, ite_false]
        rw [show (0 : ℝ≥0∞) ^ 2 = 0 by norm_num, lintegral_zero]; exact bot_le
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
    exact tsum_ofReal_exp_ne_top (by positivity) heg hκ
  · -- the pathwise split
    have hper : ∀ j, j₀ ≤ j → ∀ᵐ ω ∂P,
        bWinInt c (win (X ω) j) φ
            ≤ bWinRef γ (X ω) N j φ + (ENNReal.ofReal (Yr j ω) + ENNReal.ofReal (Zr j ω)) ∧
          bWinRef γ (X ω) N j φ
            ≤ bWinInt c (win (X ω) j) φ + (ENNReal.ofReal (Yr j ω) + ENNReal.ofReal (Zr j ω)) := by
      intro j hj
      obtain ⟨-, -, hpath, -, -, hae⟩ := hcore j hj
      have hW' := hW j hj
      filter_upwards [hid j hj, hpath, hae, ae_integrableOn_coarseB hW' hSm hSf γ]
        with ω hid' hp hae' hco
      set E : ℝ → ℝ := fun u => rexp (-(γ ^ 2 / 4) * (2 * Lw N j) + γ / 2 * U j u ω) with hE
      have hEm : Measurable E := Real.continuous_exp.measurable.comp
        (measurable_const.add (measurable_const.mul
          (hW'.measU.comp (measurable_id.prodMk measurable_const))))
      have hi1 : IntegrableOn (fun u => φ u * bdryDens γ (X ω) (winHi N j) u) S := by
        have h0 : IntegrableOn (fun u => φ u * E u) S :=
          Integrable.mono' (hco.const_mul M) (hφm.mul hEm).aestronglyMeasurable
            (ae_of_all _ fun u => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
              exact mul_le_mul_of_nonneg_right (hMabs u) (exp_pos _).le)
        exact h0.congr_fun (fun u hu => by simp only [E]; rw [(hid' u hu).1]) hSm
      have hi2 : IntegrableOn (fun u => φ u * (bdryDens γ (X ω) (winHi N j) u * G j u ω)) S := by
        refine IntegrableOn.congr_fun (hae'.1.add hae'.2) (fun u hu => ?_) hSm
        show bwG γ ((2 + γ) / 2) φ (fun _ => 2 * Lw N j) (U j) (G j) u ω +
            bwB γ ((2 + γ) / 2) φ (fun _ => 2 * Lw N j) (U j) (G j) u ω = _
        rw [← bwD_eq, bwD, (hid' u hu).1]
      have hmain := bwin_path_le (W := win (X ω) j) (c := c) hSm hφ0 hφS
        (fun u hu => ⟨by rw [(hid' u hu).1]; exact (exp_pos _).le,
          (hid' u hu).2.1, (hid' u hu).2.2⟩) hi1 hi2
      have hEq : ∫ u in S, φ u * (bdryDens γ (X ω) (winHi N j) u * G j u ω)
          = ∫ t in S, bwD γ φ (fun _ => 2 * Lw N j) (U j) (G j) t ω :=
        setIntegral_congr_fun hSm (fun u hu => by simp only [bwD]; rw [(hid' u hu).1])
      have he : ENNReal.ofReal |∫ u in S, φ u * (bdryDens γ (X ω) (winHi N j) u * G j u ω)|
          ≤ ENNReal.ofReal (Yr j ω) + ENNReal.ofReal (Zr j ω) := by
        rw [hEq, add_comm]
        exact (ENNReal.ofReal_le_ofReal hp).trans ENNReal.ofReal_add_le
      exact ⟨hmain.1.trans (add_le_add le_rfl he), hmain.2.trans (add_le_add le_rfl he)⟩
    have hall : ∀ᵐ ω ∂P, ∀ j, j₀ ≤ j →
        bWinInt c (win (X ω) j) φ
            ≤ bWinRef γ (X ω) N j φ + (ENNReal.ofReal (Yr j ω) + ENNReal.ofReal (Zr j ω)) ∧
          bWinRef γ (X ω) N j φ
            ≤ bWinInt c (win (X ω) j) φ + (ENNReal.ofReal (Yr j ω) + ENNReal.ofReal (Zr j ω)) := by
      rw [ae_all_iff]
      intro j
      by_cases hj : j₀ ≤ j
      · filter_upwards [hper j hj] with ω hω using fun _ => hω
      · exact ae_of_all _ fun ω h => absurd h hj
    filter_upwards [hall] with ω hω j hj
    simp only [hj, ite_true]
    exact hω j hj

end QuantumZipper.F1
