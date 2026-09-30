import QuantumZipper.Proofs.Zipper.AreaWinSWPath
import QuantumZipper.Proofs.Zipper.AreaWinDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINSPLIT (3): `SWWindowSplitStmt` from the window Markov structure

Source: S. Sheffield, M. Wang, arXiv:1605.06171, §3.1, proof of Lemma 3.1 (pp. 7–8) and proof of
Theorem 1.1 (p. 9). SW's argument has two parts:

1. **The Markov/Brownian structure of the window** (p. 7, "By the Markov property of the GFF and
   Proposition 2.4 …", and the display on p. 9): at a point `z` with `B_{2^{-k/N}}(z)` inside the
   domain, `C(N) sup_{ε ∈ window} e^{h̄_ε(z)} = e^{h̄_{2^{-k/N}}(z)} · (1 + G)` where `G` is centred,
   has a bounded second moment, is independent of `h_{2^{-k/N}}(z)`, and is independent of
   everything at points `2 · 2^{-k/N}` away. This is recorded, for a compact `S ⊆ ℍ`, as
   `WinMarkovData` (the Gaussian coarse value `U`, the centred factor `G`, their hypotheses
   `WinHypC` off an exceptional set `T_j`, and a summable first-moment bound on `S ∩ T_j`).
   `SWWinMarkovStmt` asks for it for the normalized free field, for the sup and inf windows.
2. **The estimate** (3.1)–(3.2) and p. 8 with the tower property: proved here from part 1 via the
   window core bound `winC_core_bound` (area parameters of `TwoRadiusC.trlC_bound_area`:
   `γ ↦ 2γ`, `α = 2 + γ`), the pathwise comparison `win_path_le` and geometric sums.

The exceptional sets `T_j` are needed because the normalization `X(fc(0,1)) = 0` of
`SWWindowSplitStmt` breaks the independence of the window increments at points whose window disc
meets the unit semicircle (the circle average `h_1(0)` is not harmonic there); SW's
zero-boundary field on `D` has no such set. On `T_j` (area `O(2^{-j/N})`) a first-moment bound is
enough.

Main result: `swWindowSplitStmt_of_markov`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open TwoRadius TwoRadiusC VagueH

/-- The log-scale of the `j`-th window in the `γ/2`-normalization of `TwoRadius`:
`½ log (1/2^{-j/N})`. -/
def Lw (N j : ℕ) : ℝ := (j : ℝ) * (Real.log 2 / (2 * N))

/-- **The window Markov structure on a compact `S ⊆ ℍ`** (SW p. 7 and the display on p. 9): for
`j ≥ j₀`, a.s. on `S`: `c · win = areaDens_{2^{-j/N}} · (1 + G_j)`, `1 + G_j ≥ 0` and
`areaDens_{2^{-j/N}} = e^{-γ² · 2 Lw + γ U_j}` (`2 Lw = log 2^{j/N}`); `WinHypC` for `(U_j, G_j)` on
`S ∖ T_j` at decorrelation distance `2 · 2^{-j/N}`; and a summable first moment of
`areaDens · (2 + G_j)` over `S ∩ T_j`. Intended instance: `U_j(w) = h_{2^{-j/N}}(w)`,
`G_j = c · sup_{window} e^{γ(h_ρ − h_{2^{-j/N}}) − (γ²/2) log(2^{-j/N}/ρ)} − 1`,
`T_j = {w : |‖w‖ − 1| ≤ 2 · 2^{-j/N}}`. -/
def WinMarkovData {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample)
    (γ c : ℝ) (N : ℕ) (win : FieldSample → ℕ → ℂ → ℝ≥0∞) (S : Set ℂ) : Prop :=
  ∃ (K Q : ℝ) (j₀ : ℕ) (T : ℕ → Set ℂ) (U G : ℕ → ℂ → Ω → ℝ) (v : ℕ → ℂ → ℝ≥0),
    0 ≤ Q ∧ (∀ j, MeasurableSet (T j)) ∧
    (∀ j, j₀ ≤ j →
      WinHypC P (S \ T j) (2 * winHi N j) K Q (fun _ => Lw N j) (v j) (U j) (G j)) ∧
    (∀ j, j₀ ≤ j → ∀ᵐ ω ∂P, ∀ w ∈ S,
      areaDens γ (X ω) (winHi N j) w
          = rexp (-((2 * γ) ^ 2 / 4) * Lw N j + 2 * γ / 2 * U j w ω) ∧
        0 ≤ 1 + G j w ω ∧
        ENNReal.ofReal c * win (X ω) j w
          = ENNReal.ofReal (areaDens γ (X ω) (winHi N j) w * (1 + G j w ω))) ∧
    (∑' j, ∫⁻ ω, (∫⁻ w in S ∩ T j,
      ENNReal.ofReal (rexp (-((2 * γ) ^ 2 / 4) * Lw N j + 2 * γ / 2 * U j w ω) *
        (2 + G j w ω))) ∂P) ≠ ∞

/-! ## Two computations -/

/-- `(2 · 2^{-j/N})² = 4 e^{-4 Lw}`. -/
theorem two_winHi_sq {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    (2 * winHi N j) ^ 2 = 4 * rexp (-4 * ((j : ℝ) * (Real.log 2 / (2 * N)))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mul_pow, winHi, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
  congr 2
  · norm_num
  · rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    push_cast
    ring

/-- A.s. integrability of the coarse densities `e^{-(γ²/4) L + (γ/2) U}` on a finite-measure set
(first moment `≤ e^{γ² K/8}`). -/
theorem ae_integrableOn_coarse {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : Set ℂ} {δ K Q L : ℝ} {v : ℂ → ℝ≥0} {U G : ℂ → Ω → ℝ}
    (h : WinHypC P S δ K Q (fun _ => L) v U G) (hS : MeasurableSet S) (hSf : volume S < ∞)
    (γ : ℝ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun t => rexp (-(γ ^ 2 / 4) * L + γ / 2 * U t ω)) S := by
  set b := -(γ ^ 2 / 4) * L
  have hmeas : Measurable (fun p : ℂ × Ω => ENNReal.ofReal (rexp (b + γ / 2 * U p.1 p.2))) :=
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

/-- `4 − (2γ² − θ²) > 0` for the area truncation `θ = max 0 ((3γ−2)/2)`, `γ < 2`. -/
theorem winExp_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    0 < 4 - (2 * γ ^ 2 - (max 0 ((3 * γ - 2) / 2)) ^ 2) := by
  rcases le_total ((3 * γ - 2) / 2) 0 with h | h
  · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right h]; nlinarith

/-- **SW's window estimate for one test function** (proof of Thm 1.1, p. 9, with (3.1)–(3.2) and
p. 8) from the window Markov structure on `tsupport φ`. -/
theorem winSplit_of_markovData {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {γ c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {N : ℕ} (hN : 1 ≤ N) {win : FieldSample → ℕ → ℂ → ℝ≥0∞} {φ : ℂ → ℝ} (hφ : IsTestH φ)
    (hφ0 : ∀ w, 0 ≤ φ w) (hD : WinMarkovData P X γ c N win (tsupport φ)) :
    WinSplit P (fun j ω => ENNReal.ofReal c * ∫⁻ w in H, win (X ω) j w * ENNReal.ofReal (φ w))
      (fun j ω => winRef γ (X ω) N j φ) := by
  obtain ⟨K, Q, j₀, T, U, G, v, hQ, hT, hW, hid, hstrip⟩ := hD
  set S := tsupport φ with hSdef
  have hSc : IsCompact S := hφ.2.1
  have hSm : MeasurableSet S := (isClosed_tsupport φ).measurableSet
  have hSf : volume S < ∞ := hSc.measure_lt_top
  have hSH : S ⊆ H := hφ.2.2
  have hφm : Measurable φ := hφ.1.measurable
  obtain ⟨M, hM⟩ := hφ.1.bounded_above_of_compact_support hφ.2.1
  have hMabs : ∀ t, |φ t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
  have hφM : ∀ t, φ t ≤ M := fun t => (le_abs_self _).trans (hMabs t)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMabs 0)
  have hφS : ∀ w, w ∉ S → φ w = 0 := fun w hw => image_eq_zero_of_notMem_tsupport hw
  obtain ⟨e1, e2, e3⟩ := trlC_area_exponent_identities hγ hγ2
  set θg := max 0 ((3 * γ - 2) / 2) with hθg
  set κ := Real.log 2 / (2 * N) with hκdef
  have hκ : 0 < κ := div_pos (Real.log_pos one_lt_two) (by positivity)
  have hSTf : ∀ j, volume (S \ T j) < ∞ := fun j => (measure_mono diff_subset).trans_lt hSf
  have hSTr : ∀ j, volume.real (S \ T j) ≤ volume.real S := fun j =>
    measureReal_mono diff_subset hSf.ne
  have hcore := fun j (hj : j₀ ≤ j) =>
    winC_core_bound (γ := 2 * γ) (α := 2 + γ) (θg := θg) (θb := (2 - γ) / 2)
      (Lmin := Lw N j) (Lmax := Lw N j) (M := M)
      (D := π * (2 * winHi N j) ^ 2 * volume.real S) (f := φ)
      (by positivity) (le_max_left 0 _) (by linarith) hQ (by rw [e1]; exact e2)
      (by rw [e3]; nlinarith) (hSm.diff (hT j)) (hSTf j) hφm hMabs (hW j hj)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl)
      ((measureReal_near_diag_le_C (hSTf j) (by unfold winHi; positivity : (0 : ℝ) ≤ 2 * winHi N j)).trans
        (mul_le_mul_of_nonneg_left (hSTr j) (by positivity)))
  set Zr : ℕ → Ω → ℝ := fun j ω =>
    |∫ t in S \ T j, wG (2 * γ) (2 + γ) φ (fun _ => Lw N j) (U j) (G j) t ω| with hZr
  set Yr : ℕ → Ω → ℝ := fun j ω =>
    ∫ t in S \ T j, |wB (2 * γ) (2 + γ) φ (fun _ => Lw N j) (U j) (G j) t ω| with hYr
  set nn : ℕ → Ω → ℝ≥0∞ := fun j ω => ENNReal.ofReal M * ∫⁻ w in S ∩ T j,
    ENNReal.ofReal (rexp (-((2 * γ) ^ 2 / 4) * Lw N j + 2 * γ / 2 * U j w ω) * (2 + G j w ω))
    with hnn
  have hmZ : ∀ j, j₀ ≤ j → Measurable (Zr j) := fun j hj =>
    continuous_abs.measurable.comp
      ((measurable_wG hφm (hW j hj)).stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (S \ T j))).measurable
  have hmY : ∀ j, j₀ ≤ j → Measurable (Yr j) := fun j hj =>
    ((continuous_abs.measurable.comp (measurable_wB hφm (hW j hj))).stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict (S \ T j))).measurable
  have hmn : ∀ j, j₀ ≤ j → Measurable (nn j) := fun j hj =>
    (Measurable.lintegral_prod_left' (μ := volume.restrict (S ∩ T j))
      (ENNReal.measurable_ofReal.comp ((Real.continuous_exp.measurable.comp
        (measurable_const.add (measurable_const.mul (hW j hj).measU))).mul
        (measurable_const.add (hW j hj).measG)))).const_mul _
  refine ⟨fun j ω => if j₀ ≤ j then ENNReal.ofReal (Yr j ω) + nn j ω else 0,
    fun j ω => if j₀ ≤ j then ENNReal.ofReal (Zr j ω) else 0, ?_, ?_, ?_, ?_, j₀, ?_⟩
  · intro j
    by_cases hj : j₀ ≤ j
    · simp only [hj, ite_true]
      exact ((ENNReal.measurable_ofReal.comp (hmY j hj)).add (hmn j hj)).aemeasurable
    · simp only [hj, ite_false]; exact aemeasurable_const
  · intro j
    by_cases hj : j₀ ≤ j
    · simp only [hj, ite_true]
      exact (ENNReal.measurable_ofReal.comp (hmZ j hj)).aemeasurable
    · simp only [hj, ite_false]; exact aemeasurable_const
  · -- `Σ E Y_j < ∞`
    set Cb := M * ((1 + Q) / 2 * rexp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2)) * volume.real S
    have hb : ∀ j, ∫⁻ ω, (if j₀ ≤ j then ENNReal.ofReal (Yr j ω) + nn j ω else 0) ∂P
        ≤ ENNReal.ofReal (Cb * rexp (-((2 - γ) ^ 2 / 4) * ((j : ℝ) * κ))) +
          ENNReal.ofReal M * ∫⁻ ω, (∫⁻ w in S ∩ T j, ENNReal.ofReal
            (rexp (-((2 * γ) ^ 2 / 4) * Lw N j + 2 * γ / 2 * U j w ω) * (2 + G j w ω))) ∂P := by
      intro j
      by_cases hj : j₀ ≤ j
      · simp only [hj, ite_true]
        obtain ⟨-, hY1, -, -, hYint, -⟩ := hcore j hj
        rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (Yr j ω))
          (ENNReal.measurable_ofReal.comp (hmY j hj)),
          ← ofReal_integral_eq_lintegral_ofReal hYint
            (ae_of_all _ fun ω => integral_nonneg fun _ => abs_nonneg _),
          hnn, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine add_le_add (ENNReal.ofReal_le_ofReal (hY1.trans ?_)) le_rfl
        rw [e3]
        have hB0 : 0 ≤ M * ((1 + Q) / 2 * (rexp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2) *
            rexp (-((2 - γ) ^ 2 / 4) * Lw N j))) := by positivity
        calc M * ((1 + Q) / 2 * (rexp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2) *
              rexp (-((2 - γ) ^ 2 / 4) * Lw N j))) * volume.real (S \ T j)
            ≤ M * ((1 + Q) / 2 * (rexp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2) *
              rexp (-((2 - γ) ^ 2 / 4) * Lw N j))) * volume.real S :=
              mul_le_mul_of_nonneg_left (hSTr j) hB0
          _ = _ := by simp only [Cb, Lw, κ]; ring
      · simp only [hj, ite_false, lintegral_zero]; exact bot_le
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine ENNReal.add_ne_top.2 ⟨tsum_ofReal_exp_ne_top (by positivity)
      (by nlinarith) hκ, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hstrip⟩
  · -- `Σ E Z_j² < ∞`
    set eg := 4 - (2 * γ ^ 2 - θg ^ 2)
    have heg : 0 < eg := winExp_pos hγ hγ2
    set Cg := M ^ 2 * (Q * rexp ((2 * γ - θg) ^ 2 * K / 2)) * (π * 4 * volume.real S)
    have hb : ∀ j, ∫⁻ ω, (if j₀ ≤ j then ENNReal.ofReal (Zr j ω) else 0) ^ 2 ∂P
        ≤ ENNReal.ofReal (Cg * rexp (-eg * ((j : ℝ) * κ))) := by
      intro j
      by_cases hj : j₀ ≤ j
      · simp only [hj, ite_true]
        obtain ⟨hZ2, -, -, hZint, -, -⟩ := hcore j hj
        have e : ∀ ω, ENNReal.ofReal (Zr j ω) ^ 2 = ENNReal.ofReal
            ((∫ t in S \ T j, wG (2 * γ) (2 + γ) φ (fun _ => Lw N j) (U j) (G j) t ω) ^ 2) := by
          intro ω
          rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
        simp_rw [e]
        rw [← ofReal_integral_eq_lintegral_ofReal hZint (ae_of_all _ fun _ => sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (hZ2.trans (le_of_eq ?_))
        rw [e1, two_winHi_sq hN j]
        have hx : rexp ((2 * γ ^ 2 - θg ^ 2) * Lw N j) * rexp (-4 * ((j : ℝ) * κ))
            = rexp (-eg * ((j : ℝ) * κ)) := by
          rw [← Real.exp_add]; congr 1; simp only [eg, Lw, κ]; ring
        calc M ^ 2 * (Q * (rexp ((2 * γ - θg) ^ 2 * K / 2) *
              rexp ((2 * γ ^ 2 - θg ^ 2) * Lw N j))) *
              (π * (4 * rexp (-4 * ((j : ℝ) * (Real.log 2 / (2 * N))))) * volume.real S)
            = Cg * (rexp ((2 * γ ^ 2 - θg ^ 2) * Lw N j) * rexp (-4 * ((j : ℝ) * κ))) := by
              simp only [Cg, κ]; ring
          _ = _ := by rw [hx]
      · simp only [hj, ite_false]
        rw [show (0 : ℝ≥0∞) ^ 2 = 0 by norm_num, lintegral_zero]; exact bot_le
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
    exact tsum_ofReal_exp_ne_top (by positivity) heg hκ
  · -- the pathwise split
    have hper : ∀ j, j₀ ≤ j → ∀ᵐ ω ∂P,
        ENNReal.ofReal c * (∫⁻ w in H, win (X ω) j w * ENNReal.ofReal (φ w))
            ≤ winRef γ (X ω) N j φ + ((ENNReal.ofReal (Yr j ω) + nn j ω) + ENNReal.ofReal (Zr j ω)) ∧
          winRef γ (X ω) N j φ ≤ ENNReal.ofReal c * (∫⁻ w in H, win (X ω) j w * ENNReal.ofReal (φ w))
            + ((ENNReal.ofReal (Yr j ω) + nn j ω) + ENNReal.ofReal (Zr j ω)) := by
      intro j hj
      obtain ⟨-, -, hpath, -, -, hae⟩ := hcore j hj
      have hW' := hW j hj
      filter_upwards [hid j hj, hpath, hae,
        ae_integrableOn_coarse hW' (hSm.diff (hT j)) (hSTf j) (2 * γ)] with ω hid' hp hae' hco
      set E : ℂ → ℝ := fun w => rexp (-((2 * γ) ^ 2 / 4) * Lw N j + 2 * γ / 2 * U j w ω) with hE
      have hEm : Measurable E := Real.continuous_exp.measurable.comp
        (measurable_const.add (measurable_const.mul
          (hW'.measU.comp (measurable_id.prodMk measurable_const))))
      have hi1 : IntegrableOn (fun w => φ w * areaDens γ (X ω) (winHi N j) w) (S \ T j) := by
        have h0 : IntegrableOn (fun w => φ w * E w) (S \ T j) :=
          Integrable.mono' (hco.const_mul M) (hφm.mul hEm).aestronglyMeasurable
            (ae_of_all _ fun w => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
              exact mul_le_mul_of_nonneg_right (hMabs w) (exp_pos _).le)
        exact h0.congr_fun (fun w hw => by simp only [E]; rw [(hid' w hw.1).1])
          (hSm.diff (hT j))
      have hi2 : IntegrableOn (fun w => φ w * (areaDens γ (X ω) (winHi N j) w * G j w ω))
          (S \ T j) := by
        refine IntegrableOn.congr_fun (hae'.1.add hae'.2) (fun w hw => ?_) (hSm.diff (hT j))
        show wG (2 * γ) (2 + γ) φ (fun _ => Lw N j) (U j) (G j) w ω +
            wB (2 * γ) (2 + γ) φ (fun _ => Lw N j) (U j) (G j) w ω = _
        rw [← wD_eq, wD, (hid' w hw.1).1]
      have hmain := win_path_le (Hs := H) (W := win (X ω) j) (c := c) (M := M) hSm (hT j) hSH
        hφ0 hφM hφS (fun w hw => ⟨by rw [(hid' w hw).1]; exact (exp_pos _).le,
          (hid' w hw).2.1, (hid' w hw).2.2⟩) hi1 hi2
      have hEq : ∫ w in S \ T j, φ w * (areaDens γ (X ω) (winHi N j) w * G j w ω)
          = ∫ t in S \ T j, wD (2 * γ) φ (fun _ => Lw N j) (U j) (G j) t ω :=
        setIntegral_congr_fun (hSm.diff (hT j)) (fun w hw => by
          simp only [wD]; rw [(hid' w hw.1).1])
      have hn : ENNReal.ofReal M * ∫⁻ w in S ∩ T j,
          ENNReal.ofReal (areaDens γ (X ω) (winHi N j) w * (2 + G j w ω)) = nn j ω := by
        simp only [hnn]
        congr 1
        exact setLIntegral_congr_fun (hSm.inter (hT j)) (fun w hw => by rw [(hid' w hw.1).1])
      have he : ENNReal.ofReal |∫ w in S \ T j, φ w * (areaDens γ (X ω) (winHi N j) w * G j w ω)|
          ≤ ENNReal.ofReal (Yr j ω) + ENNReal.ofReal (Zr j ω) := by
        rw [hEq, add_comm]
        exact (ENNReal.ofReal_le_ofReal hp).trans ENNReal.ofReal_add_le
      have hle : ENNReal.ofReal |∫ w in S \ T j, φ w * (areaDens γ (X ω) (winHi N j) w * G j w ω)|
          + ENNReal.ofReal M * ∫⁻ w in S ∩ T j,
            ENNReal.ofReal (areaDens γ (X ω) (winHi N j) w * (2 + G j w ω))
          ≤ (ENNReal.ofReal (Yr j ω) + nn j ω) + ENNReal.ofReal (Zr j ω) := by
        rw [hn]
        calc _ ≤ (ENNReal.ofReal (Yr j ω) + ENNReal.ofReal (Zr j ω)) + nn j ω :=
              add_le_add he le_rfl
          _ = _ := by ring
      exact ⟨hmain.1.trans (add_le_add le_rfl hle), hmain.2.trans (add_le_add le_rfl hle)⟩
    have hall : ∀ᵐ ω ∂P, ∀ j, j₀ ≤ j →
        ENNReal.ofReal c * (∫⁻ w in H, win (X ω) j w * ENNReal.ofReal (φ w))
            ≤ winRef γ (X ω) N j φ + ((ENNReal.ofReal (Yr j ω) + nn j ω) + ENNReal.ofReal (Zr j ω)) ∧
          winRef γ (X ω) N j φ ≤ ENNReal.ofReal c * (∫⁻ w in H, win (X ω) j w * ENNReal.ofReal (φ w))
            + ((ENNReal.ofReal (Yr j ω) + nn j ω) + ENNReal.ofReal (Zr j ω)) := by
      rw [ae_all_iff]
      intro j
      by_cases hj : j₀ ≤ j
      · filter_upwards [hper j hj] with ω hω using fun _ => hω
      · exact ae_of_all _ fun ω h => absurd h hj
    filter_upwards [hall] with ω hω j hj
    simp only [hj, ite_true]
    exact hω j hj

end QuantumZipper.E6
