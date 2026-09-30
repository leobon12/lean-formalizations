import QuantumZipper.Proofs.Thm11.AddendumMartL1
import QuantumZipper.Proofs.Thm11.AddendumMartV
import QuantumZipper.Proofs.Thm11.AddendumAssemblyStmt

/-!
# Theorem 1.1 addendum, AD-4: the frozen field converges to `(𝔥^ext_T, ρ)` in L¹

Blueprint `blueprint/THM11_BLUEPRINT.md` §9, AD-4 (first half).  For a good version `B` of the
Brownian motion (every `B t` measurable, every path continuous) and levels `δ_n ↓ 0`:

* for each `a`, `𝔥^{δ_n}_T(a) → 𝔥^ext_T(a)` a.s. (R19 `Thm11Add.ae_tendsto_hTfwd_swallow` and the
  pathwise `tendsto_frozenField_ext`);
* `E 𝔥^{δ_n}_T(a)² ≤ C₀ = (2π/√κ)² + 2 sup|g|` uniformly (AD-3 energy identity
  `Thm11Add.integral_frozenField_sq`, bounded FD-8 function `g`, κ < 8);
* hence `E|𝔥^{δ_n}_T(a) − 𝔥^ext_T(a)| → 0` (`tendsto_lintegral_enorm_sub_of_sq_le`) and, by
  Tonelli and dominated convergence in `a`, `E|X^{δ_n}_T − (𝔥^ext_T, ρ)| → 0`;
* `E ∫|ρ||𝔥^ext_T| < ∞`, so `ρ 𝔥^ext_T` is a.s. integrable (`ExtIntStmt`).

The blueprint's domination "E sup_t |𝔥_{t∧τ}(a)|² ≤ 4 E 𝔥²" (Doob) is replaced by the
uniform L² bound plus Vitali-type L¹ convergence, which suffices since the characteristic
function is bounded (own route; no Doob inequality needed).  The joint measurability of
`(ω, z) ↦ 𝔥^ext_T(z)` is the hypothesis `hMeas : ExtMeasStmt` (a separate node).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm11Asm

open FwdHolo FwdClock FrozenMart FieldMart NonSwallow MainMart Thm11Add Thm11Lyap

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The uniform second-moment bound `C₀`. -/
def momC (κ Cg : ℝ) : ℝ := (2 / Real.sqrt κ * Real.pi) ^ 2 + 2 * Cg

/-- **AD-3 energy bound.** `E 𝔥^δ_T(a)² ≤ (2π/√κ)² + 2 sup|g|`. -/
theorem lintegral_frozenField_sq_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {Cg : ℝ}
    (hCg : ∀ θ ∈ Ioo 0 Real.pi, |gFun κ θ| ≤ Cg) {c δ : ℝ} (hc : 0 < c) (hcδ : c ≤ δ) {a : ℂ}
    (hδa : δ ≤ a.im) (T : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (frozenField κ c δ T B a T ω ^ 2) ∂P ≤ ENNReal.ofReal (momC κ Cg) := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨hg, hF2, heq⟩ := integral_frozenField_sq hB hBc (bmFilt hBm) (bmFilt_adapted hBm)
    (bmFilt_le_past hBm) hκ4 hκ8 hc hcδ hδa T
  rw [← ofReal_integral_eq_lintegral_ofReal hF2 (ae_of_all _ fun ω => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [heq]
  have ha : 0 < a.im := (hc.trans_le hcδ).trans_le hδa
  have h1 : |fzPhi κ (a, 0)| ≤ 2 / Real.sqrt κ * Real.pi := by
    simp only [fzPhi, mul_zero, sub_zero, h0fwd, abs_mul, abs_neg]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.sqrt κ)]
    exact mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi _) (by positivity)
  have h2 : |gFun κ (Complex.arg a)| ≤ Cg := hCg _ (arg_mem_Ioo_of_im_pos ha)
  have h3 : -Cg ≤ ∫ ω, gFun κ (Complex.arg (fzZ κ c B a (frozenTime κ c δ T B a ω) ω)) ∂P := by
    have := integral_mono (integrable_const (-Cg)) hg fun ω => by
      have hz := fzZ_im_ge hBc hc hδa (T := T) ω (le_refl (frozenTime κ c δ T B a ω)) (κ := κ)
      exact (abs_le.1 (hCg _ (arg_mem_Ioo_of_im_pos ((hc.trans_le hcδ).trans_le hz)))).1
    simpa using this
  have h4 : fzPhi κ (a, 0) ^ 2 ≤ (2 / Real.sqrt κ * Real.pi) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  unfold momC
  linarith [(abs_le.1 h2).2]

variable {B' : ℝ≥0 → Ω → ℝ} {δn : ℕ → ℝ}

/-- **AD-4, a.s. pointwise limit.** For a good version `B'` of `B` and a fixed `a`,
`𝔥^{δ_n}_T(a) → 𝔥^ext_T(a)` a.s. (R19 + `tendsto_frozenField_ext`). -/
theorem ae_tendsto_frozenField_ext (hB : IsBrownianReal B P) (hB'c : ∀ ω, Continuous (B' · ω))
    {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω)
    (hδpos : ∀ n, 0 < δn n) (hδlim : Tendsto δn atTop (𝓝 0)) {a : ℂ} (ha : a ∈ H)
    (hδa : ∀ n, δn n ≤ a.im) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => frozenField κ (δn n / 2) (δn n) T B' a T ω) atTop
      (𝓝 (hTfwdExt κ (drive κ B' ω) T a)) := by
  filter_upwards [ae_tendsto_hTfwd_swallow hB hκ4 hκ8 ha, hdrive] with ω h hd
  have h' : swallowTime (drive κ B' ω) a < ⊤ → ∃ ℓ : ℝ, Tendsto (fieldAt κ (drive κ B' ω) a)
      (𝓝[<] (swallowTime (drive κ B' ω) a).toReal) (𝓝 ℓ) := by
    rw [hd]; exact h
  exact tendsto_frozenField_ext hB'c hδpos hδlim ha hδa T ω h'

theorem measurable_frozenField_sec (hB'm : ∀ r, Measurable (B' r))
    (hB'c : ∀ ω, Continuous (B' · ω)) {κ c δ : ℝ} (hc : 0 < c) (T : ℝ≥0) (a : ℂ) :
    Measurable fun ω => frozenField κ c δ T B' a T ω := by
  have h := measurable_frozenField_amb (κ := κ) (c := c) (δ := δ) (B := B') hB'c (bmFilt hB'm)
    (bmFilt_adapted hB'm) hc T T
  have h2 : Measurable fun ω : Ω => ((a, ω) : ℂ × Ω) := measurable_const.prodMk measurable_id
  have h3 := h.comp h2
  simp only [Function.comp_def] at h3
  exact h3

/-- **AD-4, L¹ limit for fixed `a`.** -/
theorem tendsto_lintegral_frozenField_ext (hB : IsBrownianReal B P)
    (hB'm : ∀ r, Measurable (B' r)) (hB'c : ∀ ω, Continuous (B' · ω))
    (hB' : IsPreBrownianReal B' P) (hMeas : ExtMeasStmt) {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8)
    {Cg : ℝ} (hCg : ∀ θ ∈ Ioo 0 Real.pi, |gFun κ θ| ≤ Cg)
    (hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω)
    (hδpos : ∀ n, 0 < δn n) (hδlim : Tendsto δn atTop (𝓝 0)) {a : ℂ} (ha : a ∈ H)
    (hδa : ∀ n, δn n ≤ a.im) (T : ℝ≥0) (hT : 0 < (T : ℝ)) :
    Tendsto (fun n => ∫⁻ ω, ‖frozenField κ (δn n / 2) (δn n) T B' a T ω -
        hTfwdExt κ (drive κ B' ω) T a‖ₑ ∂P) atTop (𝓝 0) ∧
      ∫⁻ ω, ‖hTfwdExt κ (drive κ B' ω) T a‖ₑ ∂P ≤ ENNReal.ofReal (momC κ Cg) + 1 := by
  have : IsProbabilityMeasure P := hB'.isGaussianProcess.isProbabilityMeasure
  have hf : ∀ n, AEMeasurable (fun ω => frozenField κ (δn n / 2) (δn n) T B' a T ω) P :=
    fun n => (measurable_frozenField_sec hB'm hB'c (by linarith [hδpos n]) T a).aemeasurable
  have hg : AEMeasurable (fun ω => hTfwdExt κ (drive κ B' ω) T a) P :=
    ((hMeas κ T hκ4 hκ8 hT B' hB'm hB'c).comp
      (measurable_id.prodMk measurable_const)).aemeasurable
  have hsq : ∀ n, ∫⁻ ω, ENNReal.ofReal (frozenField κ (δn n / 2) (δn n) T B' a T ω ^ 2) ∂P ≤
      ENNReal.ofReal (momC κ Cg) := fun n =>
    lintegral_frozenField_sq_le hB' hB'm hB'c hκ4 hκ8 hCg (by linarith [hδpos n])
      (by linarith [hδpos n]) (hδa n) T
  have hlim := ae_tendsto_frozenField_ext hB hB'c hκ4 hκ8 hdrive hδpos hδlim ha hδa T
  exact ⟨tendsto_lintegral_enorm_sub_of_sq_le ENNReal.ofReal_ne_top hf hg hsq hlim,
    (lintegral_enorm_le_sq_add_one _).trans (add_le_add (lintegral_sq_lim_le hf hsq hlim) le_rfl)⟩

/-- Joint measurability of `‖𝔥^δ_T(a) − 𝔥^ext_T(a)‖`, on `Ω × ℂ`. -/
theorem measurable_diff_ext (hB'm : ∀ r, Measurable (B' r)) (hB'c : ∀ ω, Continuous (B' · ω))
    (hMeas : ExtMeasStmt) {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8)
    {c δ : ℝ} (hc : 0 < c) (T : ℝ≥0) (hT : 0 < (T : ℝ)) :
    Measurable fun p : Ω × ℂ =>
      ‖frozenField κ c δ T B' p.2 T p.1 - hTfwdExt κ (drive κ B' p.1) T p.2‖ₑ := by
  have h := measurable_frozenField_amb (κ := κ) (c := c) (δ := δ) (B := B') hB'c (bmFilt hB'm)
    (bmFilt_adapted hB'm) hc T T
  have h1 := h.comp measurable_swap
  simp only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] at h1
  exact (h1.sub (hMeas κ T hκ4 hκ8 hT B' hB'm hB'c)).enorm

/-- **AD-4, L¹ convergence of the paired field** (integrated against `|ρ|`), and a.s.
integrability of `ρ 𝔥^ext_T` (the content of `ExtIntStmt`). -/
theorem tendsto_lintegral_rho_ext (hB : IsBrownianReal B P)
    (hB'm : ∀ r, Measurable (B' r)) (hB'c : ∀ ω, Continuous (B' · ω))
    (hB' : IsPreBrownianReal B' P) (hMeas : ExtMeasStmt) {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8)
    (hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω) {ρ : ℂ → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hρδ₀ : ∀ a : ℂ, a.im < δ₀ → ρ a = 0)
    (hδpos : ∀ n, 0 < δn n) (hδle : ∀ n, δn n ≤ δ₀) (hδlim : Tendsto δn atTop (𝓝 0))
    (T : ℝ≥0) (hT : 0 < (T : ℝ)) :
    Tendsto (fun n => ∫⁻ ω, (∫⁻ a, ‖ρ a‖ₑ *
      ‖frozenField κ (δn n / 2) (δn n) T B' a T ω - hTfwdExt κ (drive κ B' ω) T a‖ₑ) ∂P)
      atTop (𝓝 0) ∧
    ∀ᵐ ω ∂P, Integrable fun a => ρ a * hTfwdExt κ (drive κ B' ω) T a := by
  have : IsProbabilityMeasure P := hB'.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Cg, hCg⟩ := exists_abs_gFun_le hκ4 hκ8
  set M : ℝ≥0∞ := ENNReal.ofReal (momC κ Cg) + 1 with hM
  have hMt : M ≠ ⊤ := by simp [hM]
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hρfin : ∫⁻ a, ‖ρ a‖ₑ ≠ ⊤ := hρi.2.ne
  have hgood : ∀ a, ρ a ≠ 0 → a ∈ H ∧ ∀ n, δn n ≤ a.im := fun a h => by
    have : δ₀ ≤ a.im := not_lt.1 fun h' => h (hρδ₀ a h')
    exact ⟨hδ₀.trans_le this, fun n => (hδle n).trans this⟩
  have hL := fun a (h : ρ a ≠ 0) => tendsto_lintegral_frozenField_ext hB hB'm hB'c hB' hMeas
    hκ4 hκ8 hCg hdrive hδpos hδlim (hgood a h).1 (hgood a h).2 T hT
  have hmeasD := fun n => measurable_diff_ext (B' := B') hB'm hB'c hMeas hκ4 hκ8
    (δ := δn n) (by linarith [hδpos n] : 0 < δn n / 2) T hT
  have hℓ : Measurable fun p : Ω × ℂ => hTfwdExt κ (drive κ B' p.1) T p.2 :=
    hMeas κ T hκ4 hκ8 hT B' hB'm hB'c
  have hswap : ∀ (G : Ω × ℂ → ℝ≥0∞), Measurable G →
      ∫⁻ ω, (∫⁻ a, ‖ρ a‖ₑ * G (ω, a)) ∂P = ∫⁻ a, ‖ρ a‖ₑ * ∫⁻ ω, G (ω, a) ∂P := fun G hG => by
    rw [lintegral_lintegral_swap
      ((hρc.measurable.comp measurable_snd).enorm.mul hG).aemeasurable]
    exact lintegral_congr fun a => lintegral_const_mul' _ _ enorm_ne_top
  refine ⟨?_, ?_⟩
  · simp only [hswap _ (hmeasD _)]
    have h := tendsto_lintegral_of_dominated_convergence (μ := (volume : Measure ℂ))
      (f := fun _ => 0) (fun a => ‖ρ a‖ₑ * (2 * M))
      (fun n => hρc.measurable.enorm.mul ((hmeasD n).lintegral_prod_left' (μ := P))) (fun n => ?_) ?_ ?_
    · simpa using h
    · refine Eventually.of_forall fun a => ?_
      by_cases h0 : ρ a = 0
      · simp [h0]
      simp only [Pi.mul_apply]
      gcongr
      calc ∫⁻ ω, ‖frozenField κ (δn n / 2) (δn n) T B' a T ω -
            hTfwdExt κ (drive κ B' ω) T a‖ₑ ∂P
          ≤ ∫⁻ ω, (‖frozenField κ (δn n / 2) (δn n) T B' a T ω‖ₑ +
            ‖hTfwdExt κ (drive κ B' ω) T a‖ₑ) ∂P := lintegral_mono fun ω => enorm_sub_le
        _ = ∫⁻ ω, ‖frozenField κ (δn n / 2) (δn n) T B' a T ω‖ₑ ∂P +
            ∫⁻ ω, ‖hTfwdExt κ (drive κ B' ω) T a‖ₑ ∂P :=
          lintegral_add_left
            (measurable_frozenField_sec hB'm hB'c (by linarith [hδpos n]) T a).enorm _
        _ ≤ M + M := by
          gcongr
          · exact (lintegral_enorm_le_sq_add_one _).trans (add_le_add
              (lintegral_frozenField_sq_le hB' hB'm hB'c hκ4 hκ8 hCg (by linarith [hδpos n])
                (by linarith [hδpos n]) ((hgood a h0).2 n) T) le_rfl)
          · exact (hL a h0).2
        _ = 2 * M := by ring
    · rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top (by norm_num) hMt)]
      exact ENNReal.mul_ne_top hρfin (ENNReal.mul_ne_top (by norm_num) hMt)
    · refine ae_of_all _ fun a => ?_
      by_cases h0 : ρ a = 0
      · simp [h0]
      simpa using ENNReal.Tendsto.const_mul (hL a h0).1 (Or.inr enorm_ne_top)
  · have hmeasℓ : Measurable fun p : Ω × ℂ => ‖hTfwdExt κ (drive κ B' p.1) T p.2‖ₑ := hℓ.enorm
    have hfin : ∫⁻ ω, (∫⁻ a, ‖ρ a‖ₑ * ‖hTfwdExt κ (drive κ B' ω) T a‖ₑ) ∂P ≠ ⊤ := by
      rw [hswap _ hmeasℓ]
      refine ne_top_of_le_ne_top (b := ∫⁻ a, ‖ρ a‖ₑ * M) ?_ (lintegral_mono fun a => ?_)
      · rw [lintegral_mul_const' _ _ hMt]; exact ENNReal.mul_ne_top hρfin hMt
      · by_cases h0 : ρ a = 0
        · simp [h0]
        gcongr; exact (hL a h0).2
    have hm : Measurable fun ω => ∫⁻ a, ‖ρ a‖ₑ * ‖hTfwdExt κ (drive κ B' ω) T a‖ₑ :=
      ((hρc.measurable.comp measurable_snd).enorm.mul hmeasℓ).lintegral_prod_right'
    filter_upwards [ae_lt_top hm hfin] with ω hω
    refine ⟨(hρc.measurable.mul (hℓ.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable,
      ?_⟩
    simpa [HasFiniteIntegral, enorm_mul] using hω

end Thm11Asm
end QuantumZipper
