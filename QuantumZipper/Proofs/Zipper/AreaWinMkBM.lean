import QuantumZipper.Proofs.Zipper.AreaWinMkDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINMARKOV (1): the window increments are Brownian motions

Source: B. Duplantier, S. Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185
(2011), §3.1 (the circle average `t ↦ h_{r e^{-t}}(w) − h_r(w)` is a standard Brownian motion);
S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 1.1, p. 9 (the window constants are
Brownian quantities, hence do not depend on the window).

* (H1) `isPreBrownianReal_mkIncr`: centred Gaussian process with covariance
  `log r − log (max ρ_s ρ_t) = min s t` (DS11 §3.1), via mathlib's
  `IsGaussianProcess.isPreBrownianReal_of_covariance`.
* (H2) `lintegral_comp_preBM_eq`: the law of a pre-Brownian motion on a countable time set is
  determined (finite marginals + uniqueness of projective limits).
* (H3) `lintegral_sup_preBM_eq`, `lintegral_inf_preBM_eq`: the window sup/inf means equal
  `swWinMean`, `swWinMeanInf`.
* (H4) `lintegral_sup_pow_preBM_le`: `n`-th moments of the window supremum (own elementary
  reduction to the Doob bound `lintegral_iSup_expMart_le` with `nγ`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

theorem mkRad_anti (N j : ℕ) {s t : ℝ≥0} (h : s ≤ t) : mkRad N j t ≤ mkRad N j s := by
  unfold mkRad
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg (by exact_mod_cast h)))
    (winHi_pos N j).le

theorem log_mkRad (N j : ℕ) (t : ℝ≥0) : Real.log (mkRad N j t) = Real.log (winHi N j) - t := by
  unfold mkRad
  rw [Real.log_mul (winHi_pos N j).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- (H1) The raw window increment is a pre-Brownian motion (DS11 §3.1). -/
theorem isPreBrownianReal_mkIncr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {N j : ℕ} {w : ℂ}
    (hw : winHi N j ≤ w.im) : IsPreBrownianReal (mkIncr X N j w) P := by
  have hr := winHi_pos N j
  have hwH : w ∈ Hbar := AreaExist.mem_Hbar_of_le_im hr hw
  have hgood : ∀ t : ℝ≥0, GaussTK.FcIdx.Good (w, mkRad N j t, w, winHi N j) :=
    fun t => ⟨hwH, mkRad_pos N j t, hwH, hr⟩
  let f : ℝ≥0 → {p : GaussTK.FcIdx // p.Good} := fun t => ⟨_, hgood t⟩
  have hG := (GaussTK.isGaussianProcess_fcPair hX).comp_right f
  refine IsGaussianProcess.isPreBrownianReal_of_covariance hG (fun t => ?_) (fun s t hst => ?_)
  · exact GaussTK.integral_fcPairVal hX (hgood t)
  · show cov[GaussTK.fcPairVal X (w, mkRad N j s, w, winHi N j),
      GaussTK.fcPairVal X (w, mkRad N j t, w, winHi N j); P] = s
    rw [GaussTK.covariance_fcPairVal hX (hgood s) (hgood t)]
    have hs := mkRad_pos N j s
    have ht := mkRad_pos N j t
    have hsw : mkRad N j s ≤ w.im := (mkRad_le N j s).trans hw
    have htw : mkRad N j t ≤ w.im := (mkRad_le N j t).trans hw
    simp only [GaussTK.fcPairCov, kernelCov2]
    rw [kernelCov_fc_interior_sameCenter hs ht hsw htw,
      kernelCov_fc_interior_sameCenter hs hr hsw hw,
      kernelCov_fc_interior_sameCenter hr ht hw htw,
      kernelCov_fc_interior_sameCenter hr hr hw hw]
    rw [max_eq_left (mkRad_anti N j hst), max_eq_right (mkRad_le N j s),
      max_eq_left (mkRad_le N j t), max_self, log_mkRad]
    ring

/-- The law of the path `(B t)_{t ∈ D}` of a pre-Brownian motion on a finite subset. -/
theorem map_restrict_path_preBM {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {D : Set ℝ≥0} (I : Finset D) :
    P.map (fun ω (i : I) => B i.1.1 ω) =
      (BrownianReal.projectiveFamily (I.map (Embedding.subtype _))).map
        (fun (g : (I.map (Embedding.subtype _)) → ℝ) (i : I) =>
          g ⟨i.1.1, Finset.mem_map_of_mem _ i.2⟩) := by
  set J := I.map (Embedding.subtype _)
  have hL := hB.hasLaw J
  have he : Measurable (fun (g : J → ℝ) (i : I) => g ⟨i.1.1, Finset.mem_map_of_mem _ i.2⟩) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [← hL.map_eq, AEMeasurable.map_map_of_aemeasurable he.aemeasurable hL.aemeasurable]
  rfl

/-- (H2) Functionals of a pre-Brownian path on a countable time set have the same mean for any
two pre-Brownian motions. -/
theorem lintegral_comp_preBM_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {B : ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω' → ℝ} (hB : IsPreBrownianReal B P)
    (hB' : IsPreBrownianReal B' P') {D : Set ℝ≥0} (hD : D.Countable)
    {Φ : (D → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (fun t : D => B t ω) ∂P = ∫⁻ ω, Φ (fun t : D => B' t ω) ∂P' := by
  have : Countable D := hD.to_subtype
  have hF : AEMeasurable (fun ω (t : D) => B t ω) P :=
    AEMeasurable.of_eval fun t => hB.aemeasurable t
  have hF' : AEMeasurable (fun ω (t : D) => B' t ω) P' :=
    AEMeasurable.of_eval fun t => hB'.aemeasurable t
  have hmaps : P.map (fun ω (t : D) => B t ω) = P'.map (fun ω (t : D) => B' t ω) := by
    have h1 : IsProjectiveLimit (P.map (fun ω (t : D) => B t ω))
        (fun I : Finset D => (P'.map (fun ω (t : D) => B' t ω)).map I.restrict) := by
      intro I
      show _ = (P'.map (fun ω (t : D) => B' t ω)).map I.restrict
      rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable hF,
        AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable hF']
      exact (map_restrict_path_preBM hB I).trans (map_restrict_path_preBM hB' I).symm
    have h2 : IsProjectiveLimit (P'.map (fun ω (t : D) => B' t ω))
        (fun I : Finset D => (P'.map (fun ω (t : D) => B' t ω)).map I.restrict) :=
      fun _ => rfl
    exact h1.unique h2
  rw [← lintegral_map' hΦ.aemeasurable hF, ← lintegral_map' hΦ.aemeasurable hF', hmaps]

theorem measurable_winExpSup (γ : ℝ) {D : Set ℝ≥0} (hD : D.Countable) :
    Measurable (fun g : D → ℝ => ⨆ t : D, ENNReal.ofReal (rexp (γ * g t - γ ^ 2 / 2 * t))) := by
  have : Countable D := hD.to_subtype
  exact Measurable.iSup fun t => by fun_prop

theorem measurable_winExpInf (γ : ℝ) {D : Set ℝ≥0} (hD : D.Countable) :
    Measurable (fun g : D → ℝ => ⨅ t : D, ENNReal.ofReal (rexp (γ * g t - γ ^ 2 / 2 * t))) := by
  have : Countable D := hD.to_subtype
  exact Measurable.iInf fun t => by fun_prop

/-- Pointwise: `(e^{a})^n ≤ e^{n²γ²s/2} e^{(nγ)B − (nγ)² t/2}` for `a = γB − γ²t/2`, `t ≤ s`. -/
theorem ofReal_exp_pow_le (γ b : ℝ) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (n : ℕ) :
    ENNReal.ofReal (rexp (γ * b - γ ^ 2 / 2 * t)) ^ n ≤
      ENNReal.ofReal (rexp ((n:ℝ) ^ 2 * γ ^ 2 / 2 * s)) *
        ENNReal.ofReal (rexp ((n * γ) * b - (n * γ) ^ 2 / 2 * t)) := by
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have h1 : (n:ℝ) ^ 2 * (γ ^ 2 * t) ≤ (n:ℝ) ^ 2 * (γ ^ 2 * s) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hts (sq_nonneg γ)) (sq_nonneg _)
  have h2 : 0 ≤ (n:ℝ) * (γ ^ 2 * t) := mul_nonneg hn (mul_nonneg (sq_nonneg γ) ht)
  nlinarith

/-- (H4) Moments of the window supremum of a pre-Brownian motion. -/
theorem lintegral_sup_pow_preBM_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (γ : ℝ) (s : ℝ≥0)
    {D : Set ℝ≥0} (hD : D.Countable) (hDs : ∀ t ∈ D, t ≤ s) (n : ℕ) :
    ∫⁻ ω, (⨆ t ∈ D, ENNReal.ofReal (rexp (γ * B t ω - γ ^ 2 / 2 * t))) ^ n ∂P ≤
      ENNReal.ofReal (rexp ((n:ℝ) ^ 2 * γ ^ 2 / 2 * s)) *
        (1 + 2 * ENNReal.ofReal (√(rexp (((n:ℝ) * γ) ^ 2 * s) - 1))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hpt : ∀ ω, (⨆ t ∈ D, ENNReal.ofReal (rexp (γ * B t ω - γ ^ 2 / 2 * t))) ^ n ≤
      ENNReal.ofReal (rexp ((n:ℝ) ^ 2 * γ ^ 2 / 2 * s)) *
        ⨆ t ∈ D, ENNReal.ofReal (rexp ((n * γ) * B t ω - (n * γ) ^ 2 / 2 * t)) := by
    intro ω
    rw [ENNReal.iSup_pow_of_ne_zero hn.ne']
    simp only [ENNReal.iSup_pow_of_ne_zero hn.ne', ENNReal.mul_iSup]
    refine iSup₂_mono fun t ht => ofReal_exp_pow_le γ (B t ω) t.2 ?_ n
    exact_mod_cast hDs t ht
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (rexp ((n:ℝ) ^ 2 * γ ^ 2 / 2 * s)) *
        ⨆ t ∈ D, ENNReal.ofReal (rexp ((n * γ) * B t ω - (n * γ) ^ 2 / 2 * t)) ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (rexp ((n:ℝ) ^ 2 * γ ^ 2 / 2 * s)) *
        ∫⁻ ω, ⨆ t ∈ D, ENNReal.ofReal (rexp ((n * γ) * B t ω - (n * γ) ^ 2 / 2 * t)) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr; exact lintegral_iSup_expMart_le hB (n * γ) s hD hDs

end QuantumZipper.E6
