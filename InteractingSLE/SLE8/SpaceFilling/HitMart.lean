import InteractingSLE.Foundations.SLE.SpaceFilling.Density

/-!
# Space filling of SLE₈, §2: the one-point martingales at `κ = 8`

Source: `source/external/SLE8SF/sle8_space_filling_formalization.pdf`
("Space filling of a continuous SLE₈ trace"), §2, proof of Lemma 2.
Packet `planning/packets/PROVE-SF8-A.md`.

Fix `a ∈ ℍ` and write `Z_t = f_t(a) = g_t(a) − W_t = X_t + i Y_t`, `θ_t = arg Z_t`, and
`L_t = log Υ_t = log (Y_t / |g_t'(a)|)` (QuantumZipper's `fwdLogCR`), with `W = √8 B`.
The note proves Lemma 2 with the clock `u(t) = log (Im a / Y_t)` and the Brownian time change of
`Q_t = arsinh (X_t / Y_t)`. We replace the time change by two optional-stopping estimates for
local martingales of the one-point state `(Z, L)` (QuantumZipper's `opProc`), each a bounded
martingale up to an exit time (`FrozenMart.martingale_localDynkin_stopped`):

* **the log-radius martingale** `L − log sin θ` (its radial generator vanishes exactly at `κ = 8`;
  in the note's notation it is `log Υ + log cosh Q`): while `sin θ ≥ ε`, part D of
  `Foundations/SLE/SpaceFilling/Density.lean` makes `L` decrease linearly, and `sin θ` reaches `ε`
  before `L` reaches a fixed level with probability at most `C / |log ε|`. Hence
  `inf_{t < τ} Υ_t = 0` almost surely (`ae_exists_fwdLogCR_lt_eight`): the note's "the integral
  `∫ sech² q_v dv` diverges almost surely".
* **the swallowing martingales** `(|Z| ± X)^{1/4} Y^{-1/8}` (in the note's notation
  `e^{± Q/4} (Y/Im a)^{1/8}` up to constants: the exponential martingales of `Q = q + 2β_u`): while
  both stay below `A`, `|Z|² ≤ A⁸ Y`, so `Y` decreases at rate at least `2/A⁸` and `a` is swallowed
  before time `A⁸ Im a / 2`. Hence `τ_a < ∞` almost surely (`ae_exists_mem_fwdHull_eight`): the
  note's (2.4).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.SLE8

open QuantumZipper QuantumZipper.RS QuantumZipper.FwdClock

/-! ### The log-radius martingale `L − log sin θ` -/

/-- The profile `φ(L, θ) = L − log sin θ` of the log-radius martingale. -/
def logRadProfile (L θ : ℝ) : ℝ := L - Real.log (Real.sin θ)

theorem contDiffOn_uncurry_logRadProfile :
    ContDiffOn ℝ 3 (Function.uncurry logRadProfile) (univ ×ˢ Ioo 0 Real.pi) := by
  have hfun : Function.uncurry logRadProfile =
      fun p : ℝ × ℝ => p.1 - Real.log (Real.sin p.2) := rfl
  rw [hfun]
  refine contDiffOn_fst.sub (ContDiffOn.log (by fun_prop) fun p hp => ?_)
  exact (Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2).ne'

/-- **The radial generator of `L − log sin θ` vanishes at `κ = 8`**:
`−½ ∂_L φ + ½ ∂²_θ φ + ½ cot θ ∂_θ φ = −½ + 1/(2 sin² θ) − cos² θ/(2 sin² θ) = 0`. -/
theorem radGen_logRadProfile (L : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    radGen 8 logRadProfile L θ = 0 := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h1 : deriv (fun L' => logRadProfile L' θ) L = 1 :=
    ((hasDerivAt_id L).sub_const (Real.log (Real.sin θ))).deriv
  have hd : ∀ θ' ∈ Ioo 0 Real.pi,
      HasDerivAt (logRadProfile L) (-(Real.cos θ' / Real.sin θ')) θ' := by
    intro θ' hθ'
    have hs' := Real.sin_pos_of_pos_of_lt_pi hθ'.1 hθ'.2
    have h := ((Real.hasDerivAt_sin θ').log hs'.ne').const_sub L
    exact h.congr_deriv (by ring)
  have h2 : deriv (logRadProfile L) θ = -(Real.cos θ / Real.sin θ) := (hd θ hθ).deriv
  have hev : deriv (logRadProfile L) =ᶠ[𝓝 θ] fun θ' => -(Real.cos θ' / Real.sin θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact (hd θ' hθ').deriv
  have h3 : deriv (deriv (logRadProfile L)) θ =
      -((-Real.sin θ * Real.sin θ - Real.cos θ * Real.cos θ) / Real.sin θ ^ 2) := by
    rw [hev.deriv_eq]
    exact ((Real.hasDerivAt_cos θ).div (Real.hasDerivAt_sin θ) hs.ne').neg.deriv
  unfold radGen
  rw [h1, h2, h3]
  field_simp
  ring

/-- **Generator form at the one-point state.** While `Im Z ≥ c > 0`, the Dynkin generator of
`(Z, L) ↦ L − log sin arg Z` for the one-point state at `κ = 8` vanishes. -/
theorem dynkinGen_logRadProfile {c : ℝ} (hc : 0 < c) {Z : ℂ} {L : ℝ} (hZ : c ≤ Z.im) :
    dynkinGen (opDrift c) (opNoise 8)
      (fun x : ℂ × ℝ => logRadProfile x.2 (Complex.arg x.1)) (Z, L) = 0 := by
  rw [dynkinGen_opDrift_angle (by norm_num) hc contDiffOn_uncurry_logRadProfile hZ,
    radGen_logRadProfile L (arg_mem_Ioo_of_im_pos (hc.trans_le hZ)), mul_zero]

/-- `sin arg` is continuous on `{x : ℂ × ℝ | 0 < Im x.1}`. -/
theorem continuousOn_sin_arg_fst :
    ContinuousOn (fun x : ℂ × ℝ => Real.sin (Complex.arg x.1)) {x : ℂ × ℝ | 0 < x.1.im} := by
  intro x hx
  have h : ContinuousAt Complex.arg x.1 :=
    Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2 (Or.inr (ne_of_gt hx)))
  exact (Real.continuous_sin.continuousAt.comp (h.comp continuousAt_fst)).continuousWithinAt

section LogRad

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The log-radius martingale read in the one-point state `(Z, L)`: `L − log sin arg Z`. -/
def opLogRad (x : ℂ × ℝ) : ℝ := logRadProfile x.2 (Complex.arg x.1)

theorem contDiffOn_opLogRad : ContDiffOn ℝ 3 opLogRad {x : ℂ × ℝ | 0 < x.1.im} := by
  have hin : ContDiffOn ℝ 3 (fun x : ℂ × ℝ => (x.2, Complex.arg x.1)) {x : ℂ × ℝ | 0 < x.1.im} :=
    fun x hx => (contDiffAt_snd.prodMk ((contDiffAt_arg hx).comp x contDiffAt_fst)).contDiffWithinAt
  exact contDiffOn_uncurry_logRadProfile.comp hin fun x hx =>
    ⟨mem_univ _, arg_mem_Ioo_of_im_pos hx⟩

/-- **The log-radius estimate** (`κ = 8`). For `a ∈ ℍ`, `0 < η < Im a` and `0 < ε < 1` with
`ε ≤ sin arg a`, the event "`log Υ_t(a) ≥ log η` at every time `t` at which `a` is not swallowed"
has probability at most `(log Im a − log sin arg a − log η + 1) / |log ε|`. The martingale
`L − log sin θ` is stopped when `sin θ` reaches `ε`, `Im Z` reaches a level `δ`, or `L` leaves
`[log η − 1, log Im a + 1]`; on the event, part D of `Density.lean` shows that `Im Z` stays above
`2δ`, that `L` would drop below `log η` before the horizon, and that `L` never reaches the upper
level, so the stopped value of `L − log sin θ − (log η − 1)` is at least `|log ε|`; Markov's
inequality concludes. -/
theorem mul_measureReal_le_logRad (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {a : ℂ} (ha : 0 < a.im) {η : ℝ}
    (hη : 0 < η) (hηa : η < a.im) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hεa : ε ≤ Real.sin (Complex.arg a)) :
    -Real.log ε * P.real {ω | ∀ t : ℝ, 0 ≤ t → a ∉ fwdHull (drive 8 B ω) t →
      Real.log η ≤ fwdLogCR (drive 8 B ω) t a} ≤
      opLogRad (a, Real.log a.im) - (Real.log η - 1) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set Llo := Real.log η - 1 with hLlo
  set Lhi := Real.log a.im + 1 with hLhi
  set F₀ := opLogRad (a, Real.log a.im) with hF₀
  have hlogε : 0 < -Real.log ε := neg_pos.2 (Real.log_neg hε hε1)
  have hηa' : Real.log η < Real.log a.im := Real.log_lt_log hη hηa
  -- constants
  set D := Real.log a.im - Real.log η with hD
  have hD0 : 0 < D := sub_pos.2 hηa'
  set ymin := a.im * Real.exp (-(D / (2 * ε ^ 2))) with hymin
  have hymin0 : 0 < ymin := mul_pos ha (Real.exp_pos _)
  have hymina : ymin < a.im := by
    have h1 : Real.exp (-(D / (2 * ε ^ 2))) < 1 :=
      (Real.exp_lt_exp.2 (neg_neg_of_pos (by positivity))).trans_eq Real.exp_zero
    have := mul_lt_mul_of_pos_left h1 ha
    rwa [mul_one] at this
  set δ := ymin / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set T₀ := D * a.im ^ 2 / (4 * ε ^ 4) + 1 with hT₀
  have hT₀0 : 0 < T₀ := by positivity
  set T : ℝ≥0 := ⟨T₀ + 1, by positivity⟩ with hT
  set U := opProc 8 B δ a with hU
  set F := opLogRad with hF
  set sA : ℂ × ℝ → ℝ := fun x => Real.sin (Complex.arg x.1) with hsA
  set Dδ : Set (ℂ × ℝ) := {x | δ ≤ x.1.im} with hDδ
  set Cl : Set (ℂ × ℝ) := {x | x.1.im ≤ δ} ∪ (Dδ ∩ sA ⁻¹' Iic ε) ∪ {x | x.2 ≤ Llo} ∪
    {x | Lhi ≤ x.2} with hCl
  set K : Set (ℂ × ℝ) := Dδ ∩ sA ⁻¹' Ici ε ∩ {x | Llo ≤ x.2} ∩ {x | x.2 ≤ Lhi} with hK
  have hsAc : ContinuousOn sA Dδ := continuousOn_sin_arg_fst.mono fun x hx => hδ0.trans_le hx
  have hDc : IsClosed Dδ :=
    isClosed_le continuous_const (Complex.continuous_im.comp continuous_fst)
  have hL1 : IsClosed {x : ℂ × ℝ | x.2 ≤ Llo} := isClosed_le continuous_snd continuous_const
  have hL2 : IsClosed {x : ℂ × ℝ | Lhi ≤ x.2} := isClosed_le continuous_const continuous_snd
  have hL3 : IsClosed {x : ℂ × ℝ | Llo ≤ x.2} := isClosed_le continuous_const continuous_snd
  have hL4 : IsClosed {x : ℂ × ℝ | x.2 ≤ Lhi} := isClosed_le continuous_snd continuous_const
  have hClc : IsClosed Cl :=
    (((FrozenMart.isClosed_fzCl δ).union
      (hsAc.preimage_isClosed_of_isClosed hDc isClosed_Iic)).union hL1).union hL2
  have hKc : IsClosed K :=
    ((hsAc.preimage_isClosed_of_isClosed hDc isClosed_Ici).inter hL3).inter hL4
  have hKO : K ⊆ {x : ℂ × ℝ | 0 < x.1.im} := fun x hx => hδ0.trans_le hx.1.1.1
  have hU0 : ∀ ω, U 0 ω = (a, Real.log a.im) := fun ω => by
    rw [hU, opProc_integralEq hBc hδ0 8 a ω 0]
    simp [hB0 ω]
  have hK_of : ∀ x, x ∉ Cl → x ∈ K := fun x hx => by
    have h1 : δ < x.1.im := not_le.1 fun h => hx (Or.inl (Or.inl (Or.inl h)))
    have h2 : ε < sA x := not_le.1 fun h => hx (Or.inl (Or.inl (Or.inr ⟨h1.le, h⟩)))
    have h3 : Llo < x.2 := not_le.1 fun h => hx (Or.inl (Or.inr h))
    have h4 : x.2 < Lhi := not_le.1 fun h => hx (Or.inr h)
    exact ⟨⟨⟨h1.le, h2.le⟩, h3.le⟩, h4.le⟩
  have hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl) → U t ω ∈ K := by
    intro ω t _ h
    refine FrozenMart.mem_of_forall_lt_of_isClosed (continuous_opProc hBc hδ0 8 a ω) hKc ?_
      fun s hs => hK_of _ (h s hs)
    rw [show opProc 8 B δ a 0 ω = (a, Real.log a.im) from hU0 ω]
    refine ⟨⟨⟨?_, hεa⟩, ?_⟩, ?_⟩
    · show δ ≤ a.im
      linarith
    · show Llo ≤ Real.log a.im
      linarith
    · show Real.log a.im ≤ Lhi
      linarith
  have hFM : ∀ x ∈ K, |F x| ≤ |Llo| + |Lhi| + -Real.log ε := fun x hx => by
    obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := hx
    have h2' : ε ≤ Real.sin (Complex.arg x.1) := h2
    have h3' : Llo ≤ x.2 := h3
    have h4' : x.2 ≤ Lhi := h4
    have hs0 : 0 < Real.sin (Complex.arg x.1) := hε.trans_le h2'
    have hlog1 : Real.log (Real.sin (Complex.arg x.1)) ≤ 0 :=
      Real.log_nonpos hs0.le (Real.sin_le_one _)
    have hlog2 : Real.log ε ≤ Real.log (Real.sin (Complex.arg x.1)) := Real.log_le_log hε h2'
    show |x.2 - Real.log (Real.sin (Complex.arg x.1))| ≤ _
    rw [abs_le]
    constructor
    · linarith [neg_abs_le Llo, abs_nonneg Lhi]
    · linarith [le_abs_self Lhi, abs_nonneg Llo]
  have hM := FrozenMart.martingale_localDynkin_stopped hB hBc (NonSwallow.bmFilt hBm)
    (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm) (lipschitzWith_opDrift hδ0)
    (norm_opDrift_le hδ0) (opProc_integralEq hBc hδ0 8 a) FrozenMart.isOpen_fzO hClc hKc hKO
    contDiffOn_opLogRad (fun x hx _ => dynkinGen_logRadProfile hδ0 hx.1.1.1) T hUK hFM
  set σ : Ω → ℝ≥0 := hittingBtwn U Cl 0 T with hσ
  have hσT : ∀ ω, σ ω ≤ T := fun ω => hittingBtwn_le ω
  have hmin : ∀ ω, min T (σ ω) = σ ω := fun ω => min_eq_right (hσT ω)
  have hMT := hM.integrable T
  simp only [hmin] at hMT
  have hsi := hM.setIntegral_eq (show (0 : ℝ≥0) ≤ T from zero_le) MeasurableSet.univ
  simp only [Measure.restrict_univ, hmin, min_eq_left (zero_le : (0 : ℝ≥0) ≤ _)] at hsi
  have h0int : ∫ ω, opLogRad (opProc 8 B δ a 0 ω) ∂P = F₀ := by
    simp_rw [show ∀ ω, opProc 8 B δ a 0 ω = (a, Real.log a.im) from hU0]
    rw [integral_const]
    simp [hF₀, hF]
  rw [h0int] at hsi
  have hKσ : ∀ ω, U (σ ω) ω ∈ K := fun ω =>
    hUK ω (σ ω) (hσT ω) fun s hs => notMem_of_lt_hittingBtwn hs zero_le
  have hnn : ∀ ω, 0 ≤ F (U (σ ω) ω) - Llo := fun ω => by
    obtain ⟨⟨⟨-, h2⟩, h3⟩, -⟩ := hKσ ω
    have h2' : ε ≤ Real.sin (Complex.arg (U (σ ω) ω).1) := h2
    have h3' : Llo ≤ (U (σ ω) ω).2 := h3
    have hs0 : 0 < Real.sin (Complex.arg (U (σ ω) ω).1) := hε.trans_le h2'
    have hlog1 := Real.log_nonpos hs0.le (Real.sin_le_one _)
    show 0 ≤ (U (σ ω) ω).2 - Real.log (Real.sin (Complex.arg (U (σ ω) ω).1)) - Llo
    linarith
  have hGint : Integrable (fun ω => F (U (σ ω) ω) - Llo) P := hMT.sub (integrable_const _)
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hnn) hGint (-Real.log ε)
  have hEG : ∫ ω, (F (U (σ ω) ω) - Llo) ∂P = F₀ - Llo := by
    rw [integral_sub hMT (integrable_const _), integral_const, ← hsi]
    simp
  rw [hEG] at hmk
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_ (measure_ne_top P _))
    hlogε.le) hmk
  -- the inclusion
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hlt
  push Not at hlt
  set W := drive 8 B ω with hWdef
  have hW : Continuous W := drive_continuous (hBc ω)
  have hK_le : ∀ s : ℝ≥0, s ≤ σ ω → U s ω ∈ K := fun s hs =>
    hUK ω s (hs.trans (hσT ω)) fun r hr => notMem_of_lt_hittingBtwn (hr.trans_le hs) zero_le
  have hKr : ∀ r ∈ Icc (0 : ℝ) (σ ω), U r.toNNReal ω ∈ K := fun r hr =>
    hK_le r.toNNReal (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)
  have him : ∀ r ∈ Icc (0 : ℝ) (σ ω), δ ≤ (tamedZ W δ a r).im := fun r hr => by
    have h : δ ≤ (U r.toNNReal ω).1.im := (hKr r hr).1.1.1
    simpa [hU, opProc, Real.coe_toNNReal _ hr.1] using h
  have hsol := isForwardSol_tamedZ hW hδ0 (σ ω).coe_nonneg him
  have hfeq : ∀ r ∈ Icc (0 : ℝ) (σ ω), fwdMap W r a = tamedZ W δ a r := fun r hr =>
    fwdMap_eq hW ha hsol hr
  have hLeq : ∀ r ∈ Icc (0 : ℝ) (σ ω), fwdLogCR W r a = tamedLogCR W δ a r := fun r hr =>
    ((opState_eq_tamed hW hδ0 ha hr.1 fun q hq => by
      rw [hfeq q ⟨hq.1, hq.2.trans hr.2⟩]; exact him q ⟨hq.1, hq.2.trans hr.2⟩).2).symm
  have hL : ∀ r : ℝ, 0 ≤ r → r < σ ω → Real.log η ≤ fwdLogCR W r a := fun r hr0 hrσ =>
    hω r hr0 (LoewnerAlgebra.not_mem_fwdHull_of_sol hr0 hrσ ⟨_, hsol⟩)
  have hsin : ∀ r ∈ Icc (0 : ℝ) (σ ω), ε ≤ (fwdMap W r a).im / ‖fwdMap W r a‖ := by
    intro r hr
    have h : ε ≤ Real.sin (Complex.arg (tamedZ W δ a r)) := by
      have h0 : ε ≤ Real.sin (Complex.arg (U r.toNNReal ω).1) := (hKr r hr).1.1.2
      simpa [hU, opProc, Real.coe_toNNReal _ hr.1] using h0
    rwa [← hfeq r hr, Complex.sin_arg] at h
  have hdet : ∀ r ∈ Icc (0 : ℝ) (σ ω),
      fwdLogCR W r a ≤ Real.log a.im - 4 * ε ^ 2 * fwdClock W r a ∧
        ε ^ 2 / a.im ^ 2 * r ≤ fwdClock W r a := fun r hr =>
    ⟨fwdLogCR_le_of_sin_ge hW ha hr.1 hε.le (isForwardSol_restrict hsol hr.1 hr.2)
        fun q hq => hsin q ⟨hq.1, hq.2.trans hr.2⟩,
      fwdClock_ge_of_sin_ge hW ha hr.1 hε (isForwardSol_restrict hsol hr.1 hr.2)
        fun q hq => hsin q ⟨hq.1, hq.2.trans hr.2⟩⟩
  have himr : ∀ r : ℝ, 0 ≤ r → r < σ ω → ymin ≤ (fwdMap W r a).im := by
    intro r hr0 hrσ
    rw [im_fwdMap_eq_clock hW ha ⟨_, isForwardSol_restrict hsol hr0 hrσ.le⟩ ⟨hr0, le_rfl⟩]
    have h1 := (hdet r ⟨hr0, hrσ.le⟩).1
    have h2 := hL r hr0 hrσ
    have hS : 4 * ε ^ 2 * fwdClock W r a ≤ D := by linarith
    have hS' : 2 * fwdClock W r a ≤ D / (2 * ε ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [hymin]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) ha.le
  have hU0ω : U 0 ω = (a, Real.log a.im) := hU0 ω
  have hLσ : Real.log η ≤ (U (σ ω) ω).2 := by
    have h := FrozenMart.mem_of_forall_lt_of_isClosed (continuous_opProc hBc hδ0 8 a ω)
      (isClosed_le continuous_const continuous_snd : IsClosed {x : ℂ × ℝ | Real.log η ≤ x.2})
      (t := σ ω) (by rw [show opProc 8 B δ a 0 ω = (a, Real.log a.im) from hU0 ω]; exact hηa'.le)
      fun s hs => by
        show Real.log η ≤ tamedLogCR W δ a s
        rw [← hLeq s ⟨s.coe_nonneg, hs.le⟩]
        exact hL s s.coe_nonneg hs
    exact h
  obtain ⟨⟨⟨-, hKσ2⟩, hKσ3⟩, -⟩ := hKσ ω
  have hKσ2' : ε ≤ Real.sin (Complex.arg (U (σ ω) ω).1) := hKσ2
  have hKσ3' : Llo ≤ (U (σ ω) ω).2 := hKσ3
  rcases (hσT ω).lt_or_eq with hlt' | heq
  · have hex : ∃ j ∈ Icc 0 T, U j ω ∈ Cl := by
      by_contra hex
      have h := hlt'
      rw [hσ, hittingBtwn_def] at h
      simp only [hex, ↓reduceIte, lt_self_iff_false] at h
    have hmemCl := hittingBtwn_mem_of_isClosed' hClc (continuous_opProc hBc hδ0 8 a ω) hex
    rcases hmemCl with ((h | h) | h) | h
    · have hge : U (σ ω) ω ∈ {x : ℂ × ℝ | ymin ≤ x.1.im} := by
        refine FrozenMart.mem_of_forall_lt_of_isClosed (continuous_opProc hBc hδ0 8 a ω)
          (isClosed_le continuous_const (Complex.continuous_im.comp continuous_fst)) ?_ ?_
        · rw [show opProc 8 B δ a 0 ω = (a, Real.log a.im) from hU0 ω]
          exact hymina.le
        · intro s hs
          show ymin ≤ (tamedZ W δ a s).im
          rw [← hfeq s ⟨s.coe_nonneg, hs.le⟩]
          exact himr s s.coe_nonneg hs
      have h1 : ymin ≤ (U (σ ω) ω).1.im := hge
      have h2 : (U (σ ω) ω).1.im ≤ δ := h
      linarith
    · have h2 : Real.sin (Complex.arg (U (σ ω) ω).1) ≤ ε := h.2
      have hs0 : 0 < Real.sin (Complex.arg (U (σ ω) ω).1) := hε.trans_le hKσ2'
      have hlog : Real.log (Real.sin (Complex.arg (U (σ ω) ω).1)) ≤ Real.log ε :=
        Real.log_le_log hs0 h2
      have : -Real.log ε ≤ F (U (σ ω) ω) - Llo := by
        show -Real.log ε ≤ (U (σ ω) ω).2 - Real.log (Real.sin (Complex.arg (U (σ ω) ω).1)) - Llo
        linarith
      linarith
    · have h' : (U (σ ω) ω).2 ≤ Llo := h
      linarith
    · have h' : Lhi ≤ (U (σ ω) ω).2 := h
      have hσ' : (U (σ ω) ω).2 = fwdLogCR W (σ ω) a :=
        (hLeq (σ ω) ⟨(σ ω).coe_nonneg, le_rfl⟩).symm
      have h1 := hdet (σ ω) ⟨(σ ω).coe_nonneg, le_rfl⟩
      have hS0 : 0 ≤ fwdClock W (σ ω) a :=
        le_trans (mul_nonneg (by positivity) (σ ω).coe_nonneg) h1.2
      have h4 : 0 ≤ 4 * ε ^ 2 * fwdClock W (σ ω) a := mul_nonneg (by positivity) hS0
      linarith [h1.1]
  · have hrσ : T₀ < σ ω := by
      rw [heq]
      show T₀ < T₀ + 1
      linarith
    have h1 := hdet T₀ ⟨hT₀0.le, hrσ.le⟩
    have h2 := hL T₀ hT₀0.le hrσ
    have hkey : D < 4 * ε ^ 2 * (ε ^ 2 / a.im ^ 2 * T₀) := by
      have e : 4 * ε ^ 2 * (ε ^ 2 / a.im ^ 2 * T₀) = D + 4 * ε ^ 4 / a.im ^ 2 := by
        rw [hT₀]
        field_simp
      rw [e]
      have : 0 < 4 * ε ^ 4 / a.im ^ 2 := by positivity
      linarith
    have h3 : 4 * ε ^ 2 * (ε ^ 2 / a.im ^ 2 * T₀) ≤ 4 * ε ^ 2 * fwdClock W T₀ a :=
      mul_le_mul_of_nonneg_left h1.2 (by positivity)
    linarith [h1.1]

/-- The event "`log Υ_t(a) ≥ log η` whenever `a ∉ K_t`" has probability zero (`κ = 8`). -/
theorem measure_forall_le_fwdLogCR_eight_eq_zero (hB : IsPreBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {a : ℂ} (ha : 0 < a.im) {η : ℝ} (hη : 0 < η) (hηa : η < a.im) :
    P {ω | ∀ t : ℝ, 0 ≤ t → a ∉ fwdHull (drive 8 B ω) t →
      Real.log η ≤ fwdLogCR (drive 8 B ω) t a} = 0 := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set S := {ω | ∀ t : ℝ, 0 ≤ t → a ∉ fwdHull (drive 8 B ω) t →
      Real.log η ≤ fwdLogCR (drive 8 B ω) t a} with hS
  set c₀ := opLogRad (a, Real.log a.im) - (Real.log η - 1) with hc₀
  rw [← measureReal_eq_zero_iff (measure_ne_top P S)]
  by_contra hne
  have hp : 0 < P.real S := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  have hsa : 0 < Real.sin (Complex.arg a) := by
    rw [Complex.sin_arg]
    exact div_pos ha (norm_pos_iff.2 fun h => by simp [h] at ha)
  set s₀ := min (Real.sin (Complex.arg a)) (1 / 2) with hs₀
  have hs₀0 : 0 < s₀ := lt_min hsa (by norm_num)
  have hs₀1 : s₀ ≤ 1 / 2 := min_le_right _ _
  set ε := s₀ * Real.exp (-(c₀ / P.real S + 1)) with hεdef
  have hε0 : 0 < ε := mul_pos hs₀0 (Real.exp_pos _)
  have hexp : Real.exp (-(c₀ / P.real S + 1)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    have hc0 : 0 ≤ c₀ := by
      have hs1 : Real.log (Real.sin (Complex.arg a)) ≤ 0 :=
        Real.log_nonpos hsa.le (Real.sin_le_one _)
      have := Real.log_lt_log hη hηa
      simp only [hc₀, opLogRad, logRadProfile]
      linarith
    positivity
  have hεs : ε ≤ s₀ := by
    have := mul_le_mul_of_nonneg_left hexp hs₀0.le
    rwa [mul_one] at this
  have hε1 : ε < 1 := by linarith
  have hεa : ε ≤ Real.sin (Complex.arg a) := hεs.trans (min_le_left _ _)
  have h := mul_measureReal_le_logRad hB hBm hBc hB0 ha hη hηa hε0 hε1 hεa
  rw [← hS, ← hc₀] at h
  have hlog : -Real.log ε = -Real.log s₀ + (c₀ / P.real S + 1) := by
    rw [hεdef, Real.log_mul hs₀0.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hls : 0 ≤ -Real.log s₀ := neg_nonneg.2 (Real.log_nonpos hs₀0.le (by linarith))
  rw [hlog] at h
  have e : (-Real.log s₀ + (c₀ / P.real S + 1)) * P.real S =
      -Real.log s₀ * P.real S + c₀ + P.real S := by
    field_simp
    ring
  rw [e] at h
  have := mul_nonneg hls hp.le
  linarith

/-- **`inf_{t < τ} Υ_t(a) = 0` almost surely, `κ = 8`** (for a Brownian motion with continuous paths
started at `0`): the log conformal radius of `a` becomes arbitrarily negative before `a` is
swallowed. -/
theorem ae_exists_fwdLogCR_lt_eight_of_good (hB : IsPreBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {a : ℂ} (ha : 0 < a.im) :
    ∀ᵐ ω ∂P, ∀ η > (0 : ℝ), ∃ t ≥ (0 : ℝ), a ∉ fwdHull (drive 8 B ω) t ∧
      fwdLogCR (drive 8 B ω) t a < Real.log η := by
  have hηn : ∀ n : ℕ, 0 < a.im / ((n : ℝ) + 2) ∧ a.im / ((n : ℝ) + 2) < a.im := fun n =>
    ⟨by positivity, div_lt_self ha (by linarith [n.cast_nonneg (α := ℝ)])⟩
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ω ∉ {ω | ∀ t : ℝ, 0 ≤ t → a ∉ fwdHull (drive 8 B ω) t →
      Real.log (a.im / ((n : ℝ) + 2)) ≤ fwdLogCR (drive 8 B ω) t a} :=
    ae_all_iff.2 fun n => measure_eq_zero_iff_ae_notMem.1
      (measure_forall_le_fwdLogCR_eight_eq_zero hB hBm hBc hB0 ha (hηn n).1 (hηn n).2)
  filter_upwards [hall] with ω hω η hη
  obtain ⟨n, hn⟩ := exists_nat_gt (a.im / η)
  have hlt : a.im / ((n : ℝ) + 2) < η := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hη] at hn
    nlinarith
  have h := hω n
  simp only [not_forall, not_le, exists_prop] at h
  obtain ⟨t, ht, haK, hL⟩ := h
  exact ⟨t, ht, haK, hL.trans (Real.log_lt_log (hηn n).1 hlt)⟩

/-- **`inf_{t < τ} Υ_t(a) = 0` almost surely, `κ = 8`**, for any Brownian motion (the note's "the
integral `∫₀^u sech² q_v dv` diverges almost surely … Hence `Υ_t → 0` as `t ↑ τ`"). -/
theorem ae_exists_fwdLogCR_lt_eight (hB : IsBrownianReal B P) {a : ℂ} (ha : 0 < a.im) :
    ∀ᵐ ω ∂P, ∀ η > (0 : ℝ), ∃ t ≥ (0 : ℝ), a ∉ fwdHull (drive 8 B ω) t ∧
      fwdLogCR (drive 8 B ω) t a < Real.log η := by
  obtain ⟨G, hGm, hGc, hG0, hGbr, hGeq⟩ := exists_good_version0 hB
  filter_upwards [ae_exists_fwdLogCR_lt_eight_of_good hGbr.toIsPreBrownianReal hGm hGc hG0 ha,
    hGeq] with ω hω heq
  have hdr : drive 8 G ω = drive 8 B ω := funext fun s => by simp [drive, heq]
  rwa [hdr] at hω

end LogRad

/-! ### The swallowing martingales `(|Z| ± Re Z)^{1/4} (Im Z)^{-1/8}` -/


/-- The profile of the **swallowing martingales** (`s = ±1`): `(|Z| + s Re Z)^{1/4} (Im Z)^{-1/8}`,
that is `e^{s Q/4} (Im Z)^{1/8}` with `Q = arsinh (Re Z / Im Z)`. -/
def swallowProfile (s : ℝ) (Z : ℂ) : ℝ := (‖Z‖ + s * Z.re) ^ (1 / 4 : ℝ) * Z.im ^ (-(1 / 8) : ℝ)

theorem norm_add_smul_eq (Z w : ℂ) (r : ℝ) :
    ‖Z + r • w‖ = √((Z.re + r * w.re) ^ 2 + (Z.im + r * w.im) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

theorem swallow_base_pos {s : ℝ} (hs : s = 1 ∨ s = -1) {Z : ℂ} (hZ : Z.im ≠ 0) :
    0 < ‖Z‖ + s * Z.re := by
  have h : |Z.re| < ‖Z‖ := Complex.abs_re_lt_norm.2 hZ
  rcases hs with rfl | rfl
  · linarith [neg_abs_le Z.re]
  · linarith [le_abs_self Z.re]

/-- The norm along a line. -/
theorem hasDerivAt_norm_line (Z w : ℂ) (r : ℝ) (h : Z + r • w ≠ 0) :
    HasDerivAt (fun r' : ℝ => ‖Z + r' • w‖)
      (((Z + r • w).re * w.re + (Z + r • w).im * w.im) / ‖Z + r • w‖) r := by
  have hre : ∀ r' : ℝ, (Z + r' • w).re = Z.re + r' * w.re := fun r' => by simp
  have him : ∀ r' : ℝ, (Z + r' • w).im = Z.im + r' * w.im := fun r' => by simp
  have hlin : ∀ c d : ℝ, HasDerivAt (fun r' : ℝ => c + r' * d) d r := fun c d => by
    simpa using ((hasDerivAt_id r).mul_const d).const_add c
  have hq : HasDerivAt (fun r' : ℝ => (Z.re + r' * w.re) ^ 2 + (Z.im + r' * w.im) ^ 2)
      (2 * (Z.re + r * w.re) * w.re + 2 * (Z.im + r * w.im) * w.im) r := by
    refine (((hlin Z.re w.re).pow 2).add ((hlin Z.im w.im).pow 2)).congr_deriv ?_
    norm_num
  have hqpos : (Z.re + r * w.re) ^ 2 + (Z.im + r * w.im) ^ 2 ≠ 0 := by
    have e : (Z.re + r * w.re) ^ 2 + (Z.im + r * w.im) ^ 2 = ‖Z + r • w‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
      ring
    rw [e]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 h)
  have hN := hq.sqrt hqpos
  have hNeq : (fun r' : ℝ => √((Z.re + r' * w.re) ^ 2 + (Z.im + r' * w.im) ^ 2)) =
      fun r' => ‖Z + r' • w‖ := funext fun r' => (norm_add_smul_eq Z w r').symm
  rw [hNeq, ← norm_add_smul_eq Z w r] at hN
  refine hN.congr_deriv ?_
  rw [hre, him]
  field_simp

/-- Derivative of `r ↦ Ψ(Z + r w)` along a line, for `Im (Z + r w) > 0`. -/
theorem hasDerivAt_swallowProfile_line {s : ℝ} (hs : s = 1 ∨ s = -1) (Z w : ℂ) (r : ℝ)
    (hZ : 0 < (Z + r • w).im) :
    HasDerivAt (fun r : ℝ => swallowProfile s (Z + r • w))
      (swallowProfile s (Z + r • w) *
        ((((Z + r • w).re * w.re + (Z + r • w).im * w.im) / ‖Z + r • w‖ + s * w.re) /
            (4 * (‖Z + r • w‖ + s * (Z + r • w).re)) - w.im / (8 * (Z + r • w).im))) r := by
  have hS := swallow_base_pos hs hZ.ne'
  have hR0 : 0 < ‖Z + r • w‖ :=
    lt_of_le_of_lt (abs_nonneg _) (Complex.abs_re_lt_norm.2 hZ.ne')
  have hre : ∀ r' : ℝ, (Z + r' • w).re = Z.re + r' * w.re := fun r' => by simp
  have him : ∀ r' : ℝ, (Z + r' • w).im = Z.im + r' * w.im := fun r' => by simp
  have hlin : ∀ c d : ℝ, HasDerivAt (fun r' : ℝ => c + r' * d) d r := fun c d => by
    simpa using ((hasDerivAt_id r).mul_const d).const_add c
  -- the norm
  have hq : HasDerivAt (fun r' : ℝ => (Z.re + r' * w.re) ^ 2 + (Z.im + r' * w.im) ^ 2)
      (2 * (Z.re + r * w.re) * w.re + 2 * (Z.im + r * w.im) * w.im) r := by
    refine (((hlin Z.re w.re).pow 2).add ((hlin Z.im w.im).pow 2)).congr_deriv ?_
    norm_num
  have hqpos : (Z.re + r * w.re) ^ 2 + (Z.im + r * w.im) ^ 2 ≠ 0 := by
    have : 0 < (Z.im + r * w.im) ^ 2 := by rw [← him]; positivity
    positivity
  have hN := hq.sqrt hqpos
  have hNeq : (fun r' : ℝ => √((Z.re + r' * w.re) ^ 2 + (Z.im + r' * w.im) ^ 2)) =
      fun r' => ‖Z + r' • w‖ := funext fun r' => (norm_add_smul_eq Z w r').symm
  rw [hNeq, ← norm_add_smul_eq Z w r] at hN
  have hre' : (fun r' : ℝ => s * (Z + r' • w).re) = fun r' => s * (Z.re + r' * w.re) :=
    funext fun r' => by rw [hre]
  have h1 : HasDerivAt (fun r' : ℝ => s * (Z + r' • w).re) (s * w.re) r := by
    rw [hre']
    exact (hlin Z.re w.re).const_mul s
  have hSd : HasDerivAt (fun r' : ℝ => ‖Z + r' • w‖ + s * (Z + r' • w).re)
      ((2 * (Z.re + r * w.re) * w.re + 2 * (Z.im + r * w.im) * w.im) / (2 * ‖Z + r • w‖) +
        s * w.re) r := hN.add h1
  have hP1 := hSd.rpow_const (p := (1 / 4 : ℝ)) (Or.inl hS.ne')
  have him' : (fun r' : ℝ => (Z + r' • w).im) = fun r' => Z.im + r' * w.im :=
    funext fun r' => by rw [him]
  have hYd : HasDerivAt (fun r' : ℝ => (Z + r' • w).im) w.im r := by
    rw [him']
    exact hlin Z.im w.im
  have hP2 := hYd.rpow_const (p := (-(1 / 8) : ℝ)) (Or.inl hZ.ne')
  have hprod : HasDerivAt (fun r' : ℝ => (‖Z + r' • w‖ + s * (Z + r' • w).re) ^ (1 / 4 : ℝ) *
      (Z + r' • w).im ^ (-(1 / 8) : ℝ)) _ r := hP1.mul hP2
  refine hprod.congr_deriv ?_
  simp only [swallowProfile]
  rw [Real.rpow_sub_one hS.ne', Real.rpow_sub_one hZ.ne', ← hre r, ← him r]
  field_simp
  ring

/-- The complex noise direction `−√8` of the one-point state at `κ = 8`. -/
theorem deriv_swallowProfile_noise {s : ℝ} (hs : s = 1 ∨ s = -1) {Z : ℂ} (hZ : 0 < Z.im) :
    deriv (fun r : ℝ => swallowProfile s (Z + r • ((-√8 : ℝ) : ℂ))) =
      fun r => swallowProfile s (Z + r • ((-√8 : ℝ) : ℂ)) *
        (-√8 * s / (4 * ‖Z + r • ((-√8 : ℝ) : ℂ)‖)) := by
  funext r
  have hZr : 0 < (Z + r • ((-√8 : ℝ) : ℂ)).im := by simpa using hZ
  rw [(hasDerivAt_swallowProfile_line hs Z _ r hZr).deriv]
  congr 1
  have hS := swallow_base_pos hs hZr.ne'
  have hR0 : 0 < ‖Z + r • ((-√8 : ℝ) : ℂ)‖ :=
    lt_of_le_of_lt (abs_nonneg _) (Complex.abs_re_lt_norm.2 hZr.ne')
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, zero_div, sub_zero]
  generalize (Z + r • ((-√8 : ℝ) : ℂ)).re = X at hS ⊢
  generalize ‖Z + r • ((-√8 : ℝ) : ℂ)‖ = R at hS hR0 ⊢
  rcases hs with rfl | rfl
  · have h1 : R + X ≠ 0 := by linarith
    field_simp
    ring
  · have h1 : -X + R ≠ 0 := by linarith
    have h2 := mul_inv_cancel₀ h1
    field_simp
    linear_combination h2

theorem contDiffAt_swallowProfile_fst {s : ℝ} (hs : s = 1 ∨ s = -1) {n : WithTop ℕ∞}
    {x : ℂ × ℝ} (hx : 0 < x.1.im) :
    ContDiffAt ℝ n (fun x : ℂ × ℝ => swallowProfile s x.1) x := by
  have hx0 : x.1 ≠ 0 := fun h => by rw [h] at hx; simp at hx
  have h1 : ContDiffAt ℝ n (fun x : ℂ × ℝ => ‖x.1‖ + s * x.1.re) x :=
    ((contDiffAt_norm ℝ hx0).comp x contDiffAt_fst).add
      (contDiffAt_const.mul ((Complex.reCLM.contDiff.contDiffAt).comp x contDiffAt_fst))
  have h2 : ContDiffAt ℝ n (fun x : ℂ × ℝ => x.1.im) x :=
    (Complex.imCLM.contDiff.contDiffAt).comp x contDiffAt_fst
  exact (h1.rpow_const_of_ne (swallow_base_pos hs hx.ne').ne').mul (h2.rpow_const_of_ne hx.ne')

/-- **The swallowing martingales have zero generator at `κ = 8`.** -/
theorem dynkinGen_swallowProfile {s : ℝ} (hs : s = 1 ∨ s = -1) {c : ℝ} (hc : 0 < c) {Z : ℂ}
    {L : ℝ} (hZ : c ≤ Z.im) :
    dynkinGen (opDrift c) (opNoise 8) (fun x : ℂ × ℝ => swallowProfile s x.1) (Z, L) = 0 := by
  have hZi : 0 < Z.im := hc.trans_le hZ
  have hZ0 : Z ≠ 0 := fun h => by rw [h] at hZi; simp at hZi
  have hF : ContDiffAt ℝ 2 (fun x : ℂ × ℝ => swallowProfile s x.1) (Z, L) :=
    contDiffAt_swallowProfile_fst hs (x := (Z, L)) hZi
  unfold dynkinGen
  rw [FrozenMart.fderiv_apply_eq_deriv_line (hF.differentiableAt (by norm_num)),
    FrozenMart.iteratedFDeriv_two_eq_deriv_deriv_line hF]
  have e1 : (fun r : ℝ => (fun x : ℂ × ℝ => swallowProfile s x.1) ((Z, L) + r • opDrift c (Z, L)))
      = fun r => swallowProfile s (Z + r • (2 / Z)) := by
    funext r
    simp only [opDrift, FwdHolo.proj_of_le hZ, Prod.fst_add, Prod.smul_fst]
  have e2 : (fun r : ℝ => (fun x : ℂ × ℝ => swallowProfile s x.1) ((Z, L) + r • opNoise 8))
      = fun r => swallowProfile s (Z + r • ((-√8 : ℝ) : ℂ)) := by
    funext r
    simp only [opNoise, Prod.fst_add, Prod.smul_fst]
  rw [e1, e2, deriv_swallowProfile_noise hs hZi]
  have hd1 := hasDerivAt_swallowProfile_line hs Z (2 / Z) 0 (by simpa using hZi)
  rw [hd1.deriv]
  have hΨ := hasDerivAt_swallowProfile_line hs Z ((-√8 : ℝ) : ℂ) 0 (by simpa using hZi)
  have hN := hasDerivAt_norm_line Z ((-√8 : ℝ) : ℂ) 0 (by simpa using hZ0)
  have hN0 : (4 : ℝ) * ‖Z + (0 : ℝ) • ((-√8 : ℝ) : ℂ)‖ ≠ 0 := by
    simpa using norm_ne_zero_iff.2 hZ0
  have hk := (hasDerivAt_const (0 : ℝ) (-√8 * s)).div (hN.const_mul 4) hN0
  have hprod : HasDerivAt (fun r : ℝ => swallowProfile s (Z + r • ((-√8 : ℝ) : ℂ)) *
      (-√8 * s / (4 * ‖Z + r • ((-√8 : ℝ) : ℂ)‖))) _ 0 := hΨ.mul hk
  rw [hprod.deriv]
  simp only [zero_smul, add_zero]
  rw [Complex.div_re, Complex.div_im, Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    add_zero, mul_zero, sub_zero, zero_div, zero_sub]
  have hR2 : ‖Z‖ ^ 2 = Z.re ^ 2 + Z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h8 : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hS := swallow_base_pos hs hZi.ne'
  have hR0 : 0 < ‖Z‖ := norm_pos_iff.2 hZ0
  generalize swallowProfile s Z = Ψ
  generalize Z.re = X at hR2 hS ⊢
  generalize Z.im = Y at hR2 hZi ⊢
  generalize ‖Z‖ = R at hR2 hS hR0 ⊢
  generalize √8 = q at h8 ⊢
  generalize hSd : R + s * X = S at hS ⊢
  have hS0 : S ≠ 0 := hS.ne'
  have hY0 : Y ≠ 0 := hZi.ne'
  have hR0' : R ≠ 0 := hR0.ne'
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  field_simp
  linear_combination Ψ * (8 * X * R * s - 32 * X * s * S + 8 * R ^ 2 * s ^ 2) * h8 +
    Ψ * (64 * R ^ 2 - 256 * X ^ 2) * hs2 + Ψ * (256 * X * s - 64 * R) * hSd + 128 * Ψ * hR2

/-- **Deterministic swallowing bound.** If `|f_r(a)|² ≤ C · Im f_r(a)` along a forward solution on
`[0, t]`, then `Im f_r(a)` decreases at rate at least `2/C`, so `t < C · Im a / 2`. -/
theorem lt_of_norm_sq_le_mul_im {W : ℝ → ℝ} (hW : Continuous W) {a : ℂ} (ha : 0 < a.im) {t C : ℝ}
    (ht : 0 ≤ t) (hC : 0 < C) {u : ℝ → ℂ} (hu : IsForwardSol W a t u)
    (hb : ∀ r ∈ Icc (0 : ℝ) t, ‖fwdMap W r a‖ ^ 2 ≤ C * (fwdMap W r a).im) :
    t < C * a.im / 2 := by
  have hf := isForwardSol_fwdMap hW ha hu
  set φ : ℝ → ℝ := fun r => (fwdMap W r a).im + 2 / C * r with hφ
  have hder : ∀ r ∈ Icc (0 : ℝ) t,
      HasDerivWithinAt φ ((2 / fwdMap W r a).im + 2 / C * 1) (Icc 0 t) r := fun r hr =>
    (sol_hasDerivWithinAt_im hf hr).add ((hasDerivWithinAt_id r _).const_mul (2 / C))
  have hanti := antitoneOn_Icc_of_hasDerivWithinAt hder fun r hr => by
    have hr' : r ∈ Icc (0 : ℝ) t := Ioo_subset_Icc_self hr
    have hne : fwdMap W r a ≠ 0 := (hf.2 r hr').1
    have hn : 0 < ‖fwdMap W r a‖ := norm_pos_iff.2 hne
    have him : 0 < (fwdMap W r a).im := sol_im_pos hW ha hf hr'
    have h1 := hb r hr'
    rw [Complex.div_im, Complex.normSq_eq_norm_sq]
    simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, zero_div, zero_sub, mul_one]
    have h2 : 2 / C ≤ 2 * (fwdMap W r a).im / ‖fwdMap W r a‖ ^ 2 := by
      rw [div_le_div_iff₀ hC (by positivity)]
      nlinarith
    linarith
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have hle := hanti h0 ⟨ht, le_rfl⟩ ht
  have hf0 : fwdMap W 0 a = a - (W 0 : ℂ) := FwdHolo.sol_zero hf ht
  simp only [hφ, hf0, Complex.sub_im, Complex.ofReal_im, sub_zero, mul_zero, add_zero] at hle
  have hpos : 0 < (fwdMap W t a).im := sol_im_pos hW ha hf ⟨ht, le_rfl⟩
  have h2 : 2 / C * t < a.im := by linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hC] at h2
  linarith

theorem swallowProfile_pos {s : ℝ} (hs : s = 1 ∨ s = -1) {Z : ℂ} (hZ : 0 < Z.im) :
    0 < swallowProfile s Z :=
  mul_pos (Real.rpow_pos_of_pos (swallow_base_pos hs hZ.ne') _) (Real.rpow_pos_of_pos hZ _)

theorem swallowProfile_pow_four {s : ℝ} (hs : s = 1 ∨ s = -1) {Z : ℂ} (hZ : 0 < Z.im) :
    swallowProfile s Z ^ 4 = (‖Z‖ + s * Z.re) / √Z.im := by
  have hS := swallow_base_pos hs hZ.ne'
  rw [swallowProfile, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hS.le, ← Real.rpow_mul hZ.le]
  have e1 : (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 := by norm_num
  have e2 : -(1 / 8 : ℝ) * ((4 : ℕ) : ℝ) = -(1 / 2) := by norm_num
  rw [e1, e2, Real.rpow_one, Real.rpow_neg hZ.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- **The swallowing martingales control `|Z|² / Im Z`**: if both are at most `A`, then
`|Z|² ≤ A⁸ Im Z`. -/
theorem norm_sq_le_of_swallowProfile_le {Z : ℂ} (hZ : 0 < Z.im) {A : ℝ}
    (h1 : swallowProfile 1 Z ≤ A) (h2 : swallowProfile (-1) Z ≤ A) :
    ‖Z‖ ^ 2 ≤ A ^ 8 * Z.im := by
  have p1 := pow_le_pow_left₀ (swallowProfile_pos (Or.inl rfl) hZ).le h1 4
  have p2 := pow_le_pow_left₀ (swallowProfile_pos (Or.inr rfl) hZ).le h2 4
  rw [swallowProfile_pow_four (Or.inl rfl) hZ] at p1
  rw [swallowProfile_pow_four (Or.inr rfl) hZ] at p2
  have hsq : 0 < √Z.im := Real.sqrt_pos.2 hZ
  rw [div_le_iff₀ hsq] at p1 p2
  have h3 : ‖Z‖ ≤ A ^ 4 * √Z.im := by linarith
  have h4 := pow_le_pow_left₀ (norm_nonneg Z) h3 2
  rw [mul_pow, Real.sq_sqrt hZ.le, ← pow_mul] at h4
  exact h4

section SwallowEstimate

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The swallowing martingale read in the one-point state `(Z, L)`. -/
def opSwallow (s : ℝ) (x : ℂ × ℝ) : ℝ := swallowProfile s x.1

theorem contDiffOn_opSwallow {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ContDiffOn ℝ 3 (opSwallow s) {x : ℂ × ℝ | 0 < x.1.im} := fun _ hx =>
  (contDiffAt_swallowProfile_fst hs hx).contDiffWithinAt

/-- **The swallowing estimate** (`κ = 8`). For `a ∈ ℍ`, `0 < δ ≤ Im a` and `A ≥ Ψ_±(a)`, the event
"the `δ`-tamed flow stays above `δ` on `[0, A⁸ Im a / 2]`" has probability at most
`(Ψ_+(a) + Ψ_-(a)) / A`. Both swallowing martingales are stopped when one of them reaches `A` or
`Im Z` reaches `δ`; before that time `|Z|² ≤ A⁸ Im Z`, so (`lt_of_norm_sq_le_mul_im`) the stopping
time comes before `A⁸ Im a / 2`, and on the event it can only be caused by a martingale reaching
`A`; Markov's inequality concludes. -/
theorem mul_measureReal_le_swallow (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {a : ℂ} (ha : 0 < a.im) {δ : ℝ}
    (hδ0 : 0 < δ) (hδa : δ ≤ a.im) {A : ℝ} (hA1 : swallowProfile 1 a ≤ A)
    (hA2 : swallowProfile (-1) a ≤ A) :
    A * P.real {ω | ∀ r ∈ Icc (0 : ℝ) (A ^ 8 * a.im / 2), δ < (tamedZ (drive 8 B ω) δ a r).im} ≤
      swallowProfile 1 a + swallowProfile (-1) a := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hs1 : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have hs2 : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  have hA0 : 0 < A := (swallowProfile_pos hs1 ha).trans_le hA1
  set T₀ := A ^ 8 * a.im / 2 with hT₀
  have hT₀0 : 0 < T₀ := by positivity
  set T : ℝ≥0 := ⟨T₀ + 1, by positivity⟩ with hT
  set U := opProc 8 B δ a with hU
  set Dδ : Set (ℂ × ℝ) := {x | δ ≤ x.1.im} with hDδ
  have hDc : IsClosed Dδ :=
    isClosed_le continuous_const (Complex.continuous_im.comp continuous_fst)
  have hFc : ∀ s : ℝ, (s = 1 ∨ s = -1) → ContinuousOn (opSwallow s) Dδ := fun s hs =>
    (contDiffOn_opSwallow hs).continuousOn.mono fun x hx => hδ0.trans_le hx
  set Cl : Set (ℂ × ℝ) := {x | x.1.im ≤ δ} ∪ (Dδ ∩ opSwallow 1 ⁻¹' Ici A) ∪
    (Dδ ∩ opSwallow (-1) ⁻¹' Ici A) with hCl
  set K : Set (ℂ × ℝ) := (Dδ ∩ opSwallow 1 ⁻¹' Iic A) ∩ (Dδ ∩ opSwallow (-1) ⁻¹' Iic A) with hK
  have hClc : IsClosed Cl :=
    ((FrozenMart.isClosed_fzCl δ).union
      ((hFc 1 hs1).preimage_isClosed_of_isClosed hDc isClosed_Ici)).union
      ((hFc (-1) hs2).preimage_isClosed_of_isClosed hDc isClosed_Ici)
  have hKc : IsClosed K :=
    ((hFc 1 hs1).preimage_isClosed_of_isClosed hDc isClosed_Iic).inter
      ((hFc (-1) hs2).preimage_isClosed_of_isClosed hDc isClosed_Iic)
  have hKO : K ⊆ {x : ℂ × ℝ | 0 < x.1.im} := fun x hx => hδ0.trans_le hx.1.1
  have hU0 : ∀ ω, U 0 ω = (a, Real.log a.im) := fun ω => by
    rw [hU, opProc_integralEq hBc hδ0 8 a ω 0]
    simp [hB0 ω]
  have hK_of : ∀ x, x ∉ Cl → x ∈ K := fun x hx => by
    have h1 : δ < x.1.im := not_le.1 fun h => hx (Or.inl (Or.inl h))
    have h2 : opSwallow 1 x < A := not_le.1 fun h => hx (Or.inl (Or.inr ⟨h1.le, h⟩))
    have h3 : opSwallow (-1) x < A := not_le.1 fun h => hx (Or.inr ⟨h1.le, h⟩)
    exact ⟨⟨h1.le, h2.le⟩, ⟨h1.le, h3.le⟩⟩
  have hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl) → U t ω ∈ K := by
    intro ω t _ h
    refine FrozenMart.mem_of_forall_lt_of_isClosed (continuous_opProc hBc hδ0 8 a ω) hKc ?_
      fun s hs => hK_of _ (h s hs)
    rw [show opProc 8 B δ a 0 ω = (a, Real.log a.im) from hU0 ω]
    exact ⟨⟨hδa, hA1⟩, ⟨hδa, hA2⟩⟩
  have hFM : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ x ∈ K, |opSwallow s x| ≤ A := by
    intro s hs x hx
    have hpos := swallowProfile_pos hs (hKO hx)
    show |swallowProfile s x.1| ≤ A
    rw [abs_of_pos hpos]
    rcases hs with rfl | rfl
    · exact hx.1.2
    · exact hx.2.2
  set σ : Ω → ℝ≥0 := hittingBtwn U Cl 0 T with hσ
  have hσT : ∀ ω, σ ω ≤ T := fun ω => hittingBtwn_le ω
  have hmin : ∀ ω, min T (σ ω) = σ ω := fun ω => min_eq_right (hσT ω)
  -- optional stopping and Markov for each of the two martingales
  have hmark : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      A * P.real {ω | A ≤ opSwallow s (U (σ ω) ω)} ≤ swallowProfile s a := by
    intro s hs
    have hM : Martingale (fun t ω => opSwallow s (U (min t (σ ω)) ω)) (NonSwallow.bmFilt hBm) P :=
      FrozenMart.martingale_localDynkin_stopped hB hBc (NonSwallow.bmFilt hBm)
      (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm)
      (lipschitzWith_opDrift hδ0) (norm_opDrift_le hδ0) (opProc_integralEq hBc hδ0 8 a)
      FrozenMart.isOpen_fzO hClc hKc hKO (contDiffOn_opSwallow hs)
      (fun x hx _ => dynkinGen_swallowProfile hs hδ0 hx.1.1) T hUK
      (hFM s hs)
    have hMT := hM.integrable T
    simp only [hmin] at hMT
    have hsi := hM.setIntegral_eq (show (0 : ℝ≥0) ≤ T from zero_le) MeasurableSet.univ
    simp only [Measure.restrict_univ, hmin, min_eq_left (zero_le : (0 : ℝ≥0) ≤ _)] at hsi
    have h0int : ∫ ω, opSwallow s (opProc 8 B δ a 0 ω) ∂P = swallowProfile s a := by
      simp_rw [show ∀ ω, opProc 8 B δ a 0 ω = (a, Real.log a.im) from hU0]
      rw [integral_const]
      simp [opSwallow]
    rw [h0int] at hsi
    have hnn : ∀ ω, 0 ≤ opSwallow s (U (σ ω) ω) := fun ω =>
      (swallowProfile_pos hs (hKO (hUK ω (σ ω) (hσT ω)
        fun r hr => notMem_of_lt_hittingBtwn hr zero_le))).le
    have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hnn) hMT A
    rwa [← hsi] at hmk
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono (s₂ :=
      {ω | A ≤ opSwallow 1 (U (σ ω) ω)} ∪ {ω | A ≤ opSwallow (-1) (U (σ ω) ω)}) ?_
      (measure_ne_top P _)) hA0.le) ?_
  swap
  · refine le_trans (mul_le_mul_of_nonneg_left (measureReal_union_le _ _) hA0.le) ?_
    rw [mul_add]
    exact add_le_add (hmark 1 hs1) (hmark (-1) hs2)
  -- the inclusion
  intro ω hω
  simp only [mem_ofPred_eq, mem_union] at hω ⊢
  by_contra hlt
  push Not at hlt
  set W := drive 8 B ω with hWdef
  have hW : Continuous W := drive_continuous (hBc ω)
  have hK_le : ∀ s : ℝ≥0, s ≤ σ ω → U s ω ∈ K := fun s hs =>
    hUK ω s (hs.trans (hσT ω)) fun r hr => notMem_of_lt_hittingBtwn (hr.trans_le hs) zero_le
  have hKr : ∀ r ∈ Icc (0 : ℝ) (σ ω), U r.toNNReal ω ∈ K := fun r hr =>
    hK_le r.toNNReal (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)
  have hUr : ∀ r ∈ Icc (0 : ℝ) (σ ω), (U r.toNNReal ω).1 = tamedZ W δ a r := fun r hr => by
    show tamedZ (drive 8 B ω) δ a ((r.toNNReal : ℝ)) = _
    rw [Real.coe_toNNReal _ hr.1]
  have him : ∀ r ∈ Icc (0 : ℝ) (σ ω), δ ≤ (tamedZ W δ a r).im := fun r hr => by
    rw [← hUr r hr]
    exact (hKr r hr).1.1
  have hsol := isForwardSol_tamedZ hW hδ0 (σ ω).coe_nonneg him
  have hfeq : ∀ r ∈ Icc (0 : ℝ) (σ ω), fwdMap W r a = tamedZ W δ a r := fun r hr =>
    fwdMap_eq hW ha hsol hr
  have hb : ∀ r ∈ Icc (0 : ℝ) (σ ω), ‖fwdMap W r a‖ ^ 2 ≤ A ^ 8 * (fwdMap W r a).im := by
    intro r hr
    have h1 : swallowProfile 1 (U r.toNNReal ω).1 ≤ A := (hKr r hr).1.2
    have h2 : swallowProfile (-1) (U r.toNNReal ω).1 ≤ A := (hKr r hr).2.2
    rw [hUr r hr, ← hfeq r hr] at h1 h2
    have hpos : 0 < (fwdMap W r a).im := by
      rw [hfeq r hr]
      exact hδ0.trans_le (him r hr)
    exact norm_sq_le_of_swallowProfile_le hpos h1 h2
  have hσlt : (σ ω : ℝ) < T₀ :=
    lt_of_norm_sq_le_mul_im hW ha (σ ω).coe_nonneg (by positivity) hsol hb
  have hlt' : σ ω < T := by
    rw [← NNReal.coe_lt_coe]
    show (σ ω : ℝ) < T₀ + 1
    linarith
  have hex : ∃ j ∈ Icc 0 T, U j ω ∈ Cl := by
    by_contra hex
    have h := hlt'
    rw [hσ, hittingBtwn_def] at h
    simp only [hex, ↓reduceIte, lt_self_iff_false] at h
  have hmemCl := hittingBtwn_mem_of_isClosed' hClc (continuous_opProc hBc hδ0 8 a ω) hex
  rcases hmemCl with (h | h) | h
  · have h1 : (U (σ ω) ω).1.im ≤ δ := h
    have h2 := hω (σ ω) ⟨(σ ω).coe_nonneg, hσlt.le⟩
    have h3 : (U (σ ω) ω).1 = tamedZ W δ a (σ ω) := rfl
    rw [h3] at h1
    linarith
  · exact absurd h.2 (not_le.2 hlt.1)
  · exact absurd h.2 (not_le.2 hlt.2)

/-- **A swallowing bound** (`κ = 8`): for `A > 0` with `A ≥ Ψ_±(a)`, the point `a` is not swallowed
by time `A⁸ Im a / 2` with probability at most `(Ψ_+(a) + Ψ_-(a)) / A`. The levels
`δ_k = Im a / (2 (k + 1))` decrease to `0`; if `a` survives up to `T₀`, the forward flow stays
above some `2 δ_k` on `[0, T₀]` (compactness), so the `δ_k`-tamed flow equals it and stays above
`δ_k`; the events increase with `k`. -/
theorem measure_not_mem_fwdHull_le_swallow (hB : IsPreBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {a : ℂ} (ha : 0 < a.im) {A : ℝ} (hA1 : swallowProfile 1 a ≤ A)
    (hA2 : swallowProfile (-1) a ≤ A) :
    P {ω | a ∉ fwdHull (drive 8 B ω) (A ^ 8 * a.im / 2)} ≤
      ENNReal.ofReal ((swallowProfile 1 a + swallowProfile (-1) a) / A) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hA0 : 0 < A := (swallowProfile_pos (Or.inl rfl) ha).trans_le hA1
  set T₀ := A ^ 8 * a.im / 2 with hT₀
  have hT₀0 : 0 ≤ T₀ := by positivity
  set δ : ℕ → ℝ := fun k => a.im / (2 * ((k : ℝ) + 1)) with hδ
  have hδ0 : ∀ k, 0 < δ k := fun k => by positivity
  have hδa : ∀ k, δ k ≤ a.im := fun k => by
    show a.im / (2 * ((k : ℝ) + 1)) ≤ a.im
    rw [div_le_iff₀ (by positivity)]
    nlinarith [k.cast_nonneg (α := ℝ)]
  have hδanti : Antitone δ := fun j k hjk => by
    show a.im / (2 * ((k : ℝ) + 1)) ≤ a.im / (2 * ((j : ℝ) + 1))
    gcongr
  set E : ℕ → Set Ω := fun k => {ω | a ∉ fwdHull (drive 8 B ω) T₀ ∧
    ∀ r ∈ Icc (0 : ℝ) T₀, 2 * δ k ≤ (fwdMap (drive 8 B ω) r a).im} with hE
  have hEmono : Monotone E := fun j k hjk ω hω =>
    ⟨hω.1, fun r hr => le_trans (by linarith [hδanti hjk]) (hω.2 r hr)⟩
  have hsub : {ω | a ∉ fwdHull (drive 8 B ω) T₀} ⊆ ⋃ k, E k := by
    intro ω hω
    have hW : Continuous (drive 8 B ω) := drive_continuous (hBc ω)
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT₀0 (show a ∈ H from ha) hω
    have hf := isForwardSol_fwdMap hW ha hu
    have hc : ContinuousOn (fun r => (fwdMap (drive 8 B ω) r a).im) (Icc 0 T₀) :=
      Complex.continuous_im.comp_continuousOn hf.1
    obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, hT₀0⟩ hc
    have hm : 0 < (fwdMap (drive 8 B ω) r₀ a).im := sol_im_pos hW ha hf hr₀
    obtain ⟨k, hk⟩ := exists_nat_ge (a.im / (fwdMap (drive 8 B ω) r₀ a).im)
    refine mem_iUnion.2 ⟨k, hω, fun r hr => le_trans ?_ (hmin hr)⟩
    show 2 * (a.im / (2 * ((k : ℝ) + 1))) ≤ (fwdMap (drive 8 B ω) r₀ a).im
    rw [div_le_iff₀ hm] at hk
    rw [show 2 * (a.im / (2 * ((k : ℝ) + 1))) = a.im / ((k : ℝ) + 1) by field_simp,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hEk : ∀ k, P (E k) ≤ ENNReal.ofReal ((swallowProfile 1 a + swallowProfile (-1) a) / A) := by
    intro k
    set G := {ω | ∀ r ∈ Icc (0 : ℝ) (A ^ 8 * a.im / 2),
      δ k < (tamedZ (drive 8 B ω) (δ k) a r).im} with hG
    have hEG : E k ⊆ G := by
      intro ω hω
      have hW : Continuous (drive 8 B ω) := drive_continuous (hBc ω)
      have hsol := exists_isForwardSol_of_not_mem_fwdHull hT₀0 (show a ∈ H from ha) hω.1
      have heq := tamedZ_eq_fwdMap hW (hδ0 k) hT₀0 ha hsol fun r hr =>
        le_trans (by linarith [hδ0 k]) (hω.2 r hr)
      intro r hr
      rw [heq r hr]
      linarith [hω.2 r hr, hδ0 k]
    have h := mul_measureReal_le_swallow hB hBm hBc hB0 ha (hδ0 k) (hδa k) hA1 hA2
    rw [← hG] at h
    have h' : P.real G ≤ (swallowProfile 1 a + swallowProfile (-1) a) / A := by
      rw [le_div_iff₀ hA0, mul_comm]
      exact h
    calc P (E k) ≤ P G := measure_mono hEG
      _ = ENNReal.ofReal (P.real G) := (ofReal_measureReal (measure_ne_top P G)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h'
  calc P {ω | a ∉ fwdHull (drive 8 B ω) T₀} ≤ P (⋃ k, E k) := measure_mono hsub
    _ = ⨆ k, P (E k) := hEmono.directed_le.measure_iUnion
    _ ≤ _ := iSup_le hEk

/-- **Swallowing in finite time** (`κ = 8`; the note's (2.4), `τ_a < ∞` almost surely), for a
Brownian motion with continuous paths started at `0`. -/
theorem ae_exists_mem_fwdHull_eight_of_good (hB : IsPreBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {a : ℂ} (ha : 0 < a.im) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, a ∈ fwdHull (drive 8 B ω) n := by
  set c := swallowProfile 1 a + swallowProfile (-1) a with hc
  set A₀ := max (swallowProfile 1 a) (swallowProfile (-1) a) with hA₀
  have hA₀0 : 0 < A₀ := lt_max_of_lt_left (swallowProfile_pos (Or.inl rfl) ha)
  rw [ae_iff]
  have hbound : ∀ n : ℕ, P {ω | ¬∃ n : ℕ, a ∈ fwdHull (drive 8 B ω) n} ≤
      ENNReal.ofReal (c / (A₀ + n)) := by
    intro n
    have hA1 : swallowProfile 1 a ≤ A₀ + n :=
      (le_max_left _ _).trans (le_add_of_nonneg_right n.cast_nonneg)
    have hA2 : swallowProfile (-1) a ≤ A₀ + n :=
      (le_max_right _ _).trans (le_add_of_nonneg_right n.cast_nonneg)
    refine le_trans (measure_mono fun ω hω => ?_)
      (measure_not_mem_fwdHull_le_swallow hB hBm hBc hB0 ha hA1 hA2)
    simp only [mem_ofPred_eq, not_exists] at hω ⊢
    intro hmem
    obtain ⟨m, hm⟩ := exists_nat_ge ((A₀ + n) ^ 8 * a.im / 2)
    exact hω m ((QuantumZipper.fwdHull_mono (W := drive 8 B ω)).1 hm hmem)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (c / (A₀ + n))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
    exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  exact le_antisymm (ge_of_tendsto' hlim hbound) bot_le

/-- **Swallowing in finite time** (`κ = 8`): for every Brownian motion and `a ∈ ℍ`, almost surely
`a ∈ K_n` for some `n`. -/
theorem ae_exists_mem_fwdHull_eight (hB : IsBrownianReal B P) {a : ℂ} (ha : 0 < a.im) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, a ∈ fwdHull (drive 8 B ω) n := by
  obtain ⟨G, hGm, hGc, hG0, hGbr, hGeq⟩ := exists_good_version0 hB
  filter_upwards [ae_exists_mem_fwdHull_eight_of_good hGbr.toIsPreBrownianReal hGm hGc hG0 ha,
    hGeq] with ω hω heq
  have hdr : drive 8 G ω = drive 8 B ω := funext fun s => by simp [drive, heq]
  rwa [hdr] at hω

end SwallowEstimate

end InteractingSLE.SLE8
