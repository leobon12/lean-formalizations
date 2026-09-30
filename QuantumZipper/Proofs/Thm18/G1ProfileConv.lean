import QuantumZipper.Proofs.Thm18.G1ProfileConvBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PROFILE-CONV (2): `G1ProfileConvStmt`, `G1ProfileContStmt`, hence `G1ProfileStmt`

For a continuous path whose trace is a simple chord, `ψ = Ψ left a` is the inverse of a normalized
uniformizer of the side component: holomorphic and injective on `ℍ`, `ψ(ℍ) ⊆ ℍ`, bounded on
bounded sets (`PsiGood`, `psiGood_of_sel`). Then, for a good sample:

* the profile part along `ψ_* fc(d, r)` converges, for **every** `d ∈ Hbar`, `r > 0` (circles
  through `0` included), to `∫ p(S ψ z) d fc(d, r)(z)` (`tendsto_profile_psi`): dominated
  convergence with the majorant `B + 8C |log ‖S ψ‖|`, integrable on every folded circle by the
  Koebe bound `|log ‖ψ z‖| ≤ K + (1 + C₂) |log Im z|` (`abs_log_norm_le_of_injOn`);
* hence `dPart = ∫ (p ∘ Sψ) dfc + Q log S + Q ∫ log ‖ψ'‖ dfc`, and both integrands are bounded by
  `A + B |log Im|` on bounded parts of `ℍ` (`LogBd`), so continuity on `Hbar × (0, ∞)` and the
  smoothing symmetry follow from `CoordReg.LogBounded.continuousOn` and
  `CoordReg.LogBounded.integral_swap` (commuting folded-circle means).

No weakening of the statements was needed: circles through `0` are handled by the same bound.
Main results: `g1ProfileConvStmt`, `g1ProfileContStmt`, `g1ProfileStmt_holds`,
`g1RegRepRC2Stmt_of_psiExt`. Own elementary assembly (sources for the analytic inputs in
`G1ProfileConvBasic.lean`).
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open F1.RC3Two CA.Koebe WedgeTK CircleFubini

/-! ## Integrands with a logarithmic bound in `Im` -/

/-- `G` is measurable, continuous on `ℍ` and `|G u| ≤ A_R + B |log Im u|` on `ℍ ∩ B̄(0, R)`. -/
def LogBd (G : ℂ → ℝ) (B : ℝ) : Prop :=
  Measurable G ∧ ContinuousOn G H ∧ 0 ≤ B ∧
    ∀ R : ℝ, ∃ A : ℝ, ∀ u ∈ H, ‖u‖ ≤ R → |G u| ≤ A + B * |Real.log u.im|

namespace LogBd

variable {G : ℂ → ℝ} {B : ℝ}

theorem logBounded (h : LogBd G B) : CoordReg.LogBounded fun u => G u / (B + 1) := by
  obtain ⟨hm, hc, hB, hbd⟩ := h
  have hB1 : 0 < B + 1 := by linarith
  refine ⟨hm.div_const _, hc.div_const _, fun R => ?_⟩
  obtain ⟨A, hA⟩ := hbd R
  refine ⟨|A| / (B + 1), by positivity, fun u hu huR => ?_⟩
  rw [abs_div, abs_of_pos hB1, div_le_iff₀ hB1, add_mul, div_mul_cancel₀ _ hB1.ne']
  have := hA u hu huR
  have h1 := le_abs_self A
  have h2 := abs_nonneg (Real.log u.im)
  nlinarith

theorem integral_eq (h : LogBd G B) (w : ℂ) (r : ℝ) :
    ∫ u, G u ∂foldedCircle w r = (B + 1) * ∫ u, G u / (B + 1) ∂foldedCircle w r := by
  have hB1 : B + 1 ≠ 0 := by linarith [h.2.2.1]
  rw [integral_div]
  field_simp

theorem integrable (h : LogBd G B) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable G (foldedCircle w r) := by
  have hB1 : B + 1 ≠ 0 := by linarith [h.2.2.1]
  refine ((h.logBounded.integrable w hr).const_mul (B + 1)).congr (ae_of_all _ fun u => ?_)
  show (B + 1) * (G u / (B + 1)) = G u
  field_simp

theorem continuousOn (h : LogBd G B) :
    ContinuousOn (fun p : ℂ × ℝ => ∫ u, G u ∂foldedCircle p.1 p.2) {p | 0 < p.2} :=
  (continuousOn_const.mul h.logBounded.continuousOn).congr fun p _ => h.integral_eq p.1 p.2

theorem integrable_smooth (h : LogBd G B) {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (w : ℂ) :
    Integrable (fun u => ∫ x, G x ∂foldedCircle u s) (foldedCircle w t) :=
  RegClosure.integrable_fc (h.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn
      fun u _ => (show (0 : ℝ) < s from hs)) w ht

theorem integral_swap (h : LogBd G B) (w : ℂ) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    ∫ u, (∫ x, G x ∂foldedCircle u ρ) ∂foldedCircle w r =
      ∫ v, (∫ x, G x ∂foldedCircle v r) ∂foldedCircle w ρ := by
  simp_rw [h.integral_eq]
  rw [integral_const_mul, integral_const_mul, h.logBounded.integral_swap w hr hρ]

end LogBd

/-! ## The selected maps -/

/-- The properties of `ψ = Ψ left a` used below. -/
def PsiGood (ψ : ℂ → ℂ) : Prop :=
  Measurable ψ ∧ DifferentiableOn ℂ ψ H ∧ InjOn ψ H ∧ MapsTo ψ H H ∧
    ∀ R : ℝ, ∃ M : ℝ, ∀ z ∈ H, ‖z‖ ≤ R → ‖ψ z‖ ≤ M

theorem psiGood_of_sel {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (hc : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool) :
    PsiGood (Ψ left a) := by
  obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 a hc hs left
  have hopen : IsOpen (sideDom (pathTrace (γ ^ 2) a) left) := by
    cases left
    · exact CA.Kernel.isOpen_rightComponent_qz hs
    · exact CA.Uniformizer.isOpen_leftComponent hs
  have hDH : sideDom (pathTrace (γ ^ 2) a) left ⊆ H := by
    cases left
    · exact rightComponent_subset_H _
    · exact leftComponent_subset_H _
  have hp := G1.invFunOn_props hopen hφ
  refine ⟨(hΨ.1 left).comp (measurable_const.prodMk measurable_id), ?_, ?_, ?_, fun R => ?_⟩
  · rw [hΨa]; exact hp.1
  · rw [hΨa]; exact G1.injOn_invFunOn_of_uniformizer hφ
  · rw [hΨa]; exact fun z hz => hDH (hp.2.2.2 hz)
  · obtain ⟨M, hM⟩ := bdd_invFunOn_of_normalized hφ R
    exact ⟨M, fun z hz hzR => by rw [hΨa]; exact hM z hz hzR⟩

variable {ψ : ℂ → ℂ}

theorem logBd_log_norm_deriv (hψ : PsiGood ψ) :
    LogBd (fun z => Real.log ‖deriv ψ z‖) koebeDistExp := by
  obtain ⟨-, hd, hinj, -, -⟩ := hψ
  refine ⟨Real.measurable_log.comp (measurable_deriv _).norm,
    ContinuousOn.log ((hd.deriv isOpen_H).continuousOn.norm) fun z hz =>
      norm_ne_zero_iff.2 (deriv_ne_zero_of_injOn isOpen_H hd hinj hz),
    koebeDistExp_pos.le, fun R => ?_⟩
  obtain ⟨K, hK⟩ := G1.abs_log_norm_deriv_le_of_injOn hd hinj
    (R := max R 1) (lt_of_lt_of_le one_pos (le_max_right _ _))
  exact ⟨K, fun u hu huR => hK u hu (huR.trans (le_max_left _ _))⟩

theorem logBd_log_norm (hψ : PsiGood ψ) {S : ℝ} (hS : 0 < S) :
    LogBd (fun z => Real.log ‖(S : ℂ) * ψ z‖) (1 + koebeDistExp) := by
  obtain ⟨hψm, hd, hinj, hmaps, hbdd⟩ := hψ
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  refine ⟨Real.measurable_log.comp (measurable_const.mul hψm).norm,
    ContinuousOn.log ((continuousOn_const.mul hd.continuousOn).norm) fun z hz =>
      norm_ne_zero_iff.2 (mul_ne_zero hS' (ne_zero_of_mem_H' (hmaps hz))),
    by linarith [koebeDistExp_pos], fun R => ?_⟩
  obtain ⟨M, hM⟩ := hbdd (max R 1)
  obtain ⟨K, hK⟩ := abs_log_norm_le_of_injOn hd hinj hmaps
    (lt_of_lt_of_le one_pos (le_max_right R 1)) hM
  refine ⟨|Real.log S| + K, fun u hu huR => ?_⟩
  have huR' : ‖u‖ ≤ max R 1 := huR.trans (le_max_left _ _)
  have hψ0 : ‖ψ u‖ ≠ 0 := norm_ne_zero_iff.2 (ne_zero_of_mem_H' (hmaps hu))
  show |Real.log ‖(S : ℂ) * ψ u‖| ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS,
    Real.log_mul hS.ne' hψ0]
  have := hK u hu huR'
  have := abs_add_le (Real.log S) (Real.log ‖ψ u‖)
  linarith

theorem norm_mul_psi_le (hψ : PsiGood ψ) {S : ℝ} (hS : 0 < S) (R : ℝ) :
    ∃ M : ℝ, ∀ z ∈ H, ‖z‖ ≤ R → ‖(S : ℂ) * ψ z‖ ≤ M := by
  obtain ⟨M, hM⟩ := hψ.2.2.2.2 R
  refine ⟨S * M, fun z hz hzR => ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  exact mul_le_mul_of_nonneg_left (hM z hz hzR) hS.le

theorem mul_psi_mem_H (hψ : PsiGood ψ) {S : ℝ} (hS : 0 < S) {z : ℂ} (hz : z ∈ H) :
    (S : ℂ) * ψ z ∈ H := by
  show 0 < ((S : ℂ) * ψ z).im
  rw [Complex.im_ofReal_mul]
  exact mul_pos hS (hψ.2.2.2.1 hz)

variable {g : ℝ → ℝ} {C : ℝ}

theorem logBd_profile (hψ : PsiGood ψ) {S : ℝ} (hS : 0 < S) (hgm : Measurable g)
    (hgc : ContinuousOn g (Ioi 0)) (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) :
    LogBd (fun z => rp g ((S : ℂ) * ψ z)) (C * (1 + koebeDistExp)) := by
  have hC := nonneg_of_bd hbd
  have hL := logBd_log_norm hψ hS
  refine ⟨hgm.comp (measurable_const.mul hψ.1).norm, fun z hz => ?_,
    mul_nonneg hC (by linarith [koebeDistExp_pos]), fun R => ?_⟩
  · refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun z => ‖(S : ℂ) * ψ z‖) z :=
      (continuousAt_const.mul (hψ.2.1.differentiableAt (isOpen_H.mem_nhds hz)).continuousAt).norm
    have hpos : 0 < ‖(S : ℂ) * ψ z‖ := norm_pos_iff.2 (ne_zero_of_mem_H' (mul_psi_mem_H hψ hS hz))
    exact ContinuousAt.comp (g := g) (hgc.continuousAt (Ioi_mem_nhds hpos)) h1
  · obtain ⟨A₁, hA₁⟩ := hL.2.2.2 R
    obtain ⟨M, hM⟩ := norm_mul_psi_le hψ hS R
    obtain ⟨B, -, hB⟩ := abs_le_log_of_bd hgc hbd M
    refine ⟨B + C * A₁, fun u hu huR => ?_⟩
    have hpos : 0 < ‖(S : ℂ) * ψ u‖ := norm_pos_iff.2 (ne_zero_of_mem_H' (mul_psi_mem_H hψ hS hu))
    have h1 := hB _ hpos (hM u hu huR)
    have h2 := mul_le_mul_of_nonneg_left (hA₁ u hu huR) hC
    show |g ‖(S : ℂ) * ψ u‖| ≤ _
    nlinarith

/-- **Convergence of the profile part** along `ψ_* fc(d, r)`, for every `d` and `r > 0`. -/
theorem tendsto_profile_psi (hψ : PsiGood ψ) {S : ℝ} (hS : 0 < S) (hgm : Measurable g)
    (hgc : ContinuousOn g (Ioi 0)) (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t))
    (d : ℂ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun k : ℕ => ∫ w, GoodSample.smoothFun (rp g) ((S : ℂ) * w) (S * radius k)
        ∂((foldedCircle d r).map ψ)) atTop
      (𝓝 (∫ z, rp g ((S : ℂ) * ψ z) ∂foldedCircle d r)) := by
  have e : ∀ k : ℕ, ∫ w, GoodSample.smoothFun (rp g) ((S : ℂ) * w) (S * radius k)
      ∂((foldedCircle d r).map ψ) =
      ∫ z, GoodSample.smoothFun (rp g) ((S : ℂ) * ψ z) (S * radius k) ∂foldedCircle d r :=
    fun k => integral_map hψ.1.aemeasurable
      ((continuous_smoothFun_rp hgm hgc hbd (mul_pos hS (radius_pos k))).comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable
  obtain ⟨M, hM⟩ := norm_mul_psi_le hψ hS (‖d‖ + r)
  have hρ : Tendsto (fun k : ℕ => S * radius k) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hS (radius_pos k)⟩
    simpa using (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul S
  refine (tendsto_integral_smoothFun_comp hgm hgc hbd (f := fun z => (S : ℂ) * ψ z)
    (measurable_const.mul hψ.1) ?_ (R₀ := M) ?_ ((logBd_log_norm hψ hS).integrable d hr)
    hρ).congr fun k => (e k).symm
  · filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with z hz
    exact mul_psi_mem_H hψ hS hz
  · filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr,
      TwoPoint.foldedCircle_ae_norm_le d hr.le] with z hz hzn
    exact hM z hz hzn

/-- The profile part of the canonical wedge field along `ψ_* fc(d, r)`. -/
theorem profPart_psi_eq {x : FieldSample} {A : ℝ → ℝ} {Q : ℝ} (hψ : PsiGood ψ) {S : ℝ}
    (hS : 0 < S) (hgm : Measurable (wg x A Q)) (hgc : ContinuousOn (wg x A Q) (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |wg x A Q t| ≤ C * (1 - Real.log t)) (d : ℂ) {r : ℝ}
    (hr : 0 < r) :
    profPart x A Q S ((foldedCircle d r).map ψ) =
      ∫ z, WedgeCan.wedgeProfile x A Q ((S : ℂ) * ψ z) ∂foldedCircle d r :=
  (tendsto_profile_psi hψ hS hgm hgc hbd d hr).limUnder_eq

theorem integral_add_const_add_mul {F₁ F₂ : ℂ → ℝ} {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (h₁ : Integrable F₁ μ) (h₂ : Integrable F₂ μ) (c q : ℝ) :
    ∫ u, (F₁ u + c + q * F₂ u) ∂μ = ∫ u, F₁ u ∂μ + c + q * ∫ u, F₂ u ∂μ := by
  rw [integral_add (f := fun u => F₁ u + c) (g := fun u => q * F₂ u)
    (h₁.add (integrable_const c)) (h₂.const_mul q),
    integral_add (f := F₁) (g := fun _ => c) h₁ (integrable_const c), integral_const_mul]
  simp

/-! ## The two statements -/

/-- **`G1ProfileConvStmt` holds.** -/
theorem g1ProfileConvStmt : G1ProfileConvStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ a hc hs left G hG
  have hψ := psiGood_of_sel hΨ hc hs left
  filter_upwards [ae_wedgeGood hX hA hXA hG, ae_scale_pos hγ hγ2 hX hA hXA,
    F1.ae_growth_radAvgReg hX, F1.ae_growth_wedge hA] with ω' hW hS hr hw
  obtain ⟨K₁, M₁, hM₁, h₁⟩ := hr
  obtain ⟨K₂, M₂, hM₂, h₂⟩ := hw
  intro d _ r hr
  exact ⟨_, tendsto_profile_psi hψ hS (measurable_wg hW.cont)
    (continuousOn_wg hW.good hW.cont)
    (bd_wg (Q := Qc γ) (A := fun t => A t ω') hM₁ hM₂ h₁ h₂) d hr⟩

/-- **`G1ProfileContStmt` holds.** -/
theorem g1ProfileContStmt : G1ProfileContStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ a hc hs left G hG
  have hψ := psiGood_of_sel hΨ hc hs left
  filter_upwards [ae_wedgeGood hX hA hXA hG, ae_scale_pos hγ hγ2 hX hA hXA,
    F1.ae_growth_radAvgReg hX, F1.ae_growth_wedge hA] with ω' hW hS hr hw
  obtain ⟨K₁, M₁, hM₁, h₁⟩ := hr
  obtain ⟨K₂, M₂, hM₂, h₂⟩ := hw
  have hgm := measurable_wg (x := X ω') (Q := Qc γ) hW.cont
  have hgc := continuousOn_wg (Q := Qc γ) hW.good hW.cont
  have hbd := bd_wg (Q := Qc γ) (A := fun t => A t ω') hM₁ hM₂ h₁ h₂
  set S := scaleParam γ (wedge0 γ X A ω') with hSdef
  have L1 := logBd_profile hψ hS hgm hgc hbd
  have L2 := logBd_log_norm_deriv hψ
  have hform : ∀ (u : ℂ) (s : ℝ), 0 < s → dPart γ X A (Ψ left a) ω' (u, s) =
      ∫ z, rp (wg (X ω') (fun t => A t ω') (Qc γ)) ((S : ℂ) * Ψ left a z) ∂foldedCircle u s +
        Qc γ * Real.log S + Qc γ * ∫ z, Real.log ‖deriv (Ψ left a) z‖ ∂foldedCircle u s := by
    intro u s hs
    show profPart _ _ _ S _ + _ + _ = _
    rw [profPart_psi_eq hψ hS hgm hgc hbd u hs]
    rfl
  refine ⟨?_, fun w _ r ρ hr hρ => ?_⟩
  · have hcont := (L1.continuousOn.add (continuousOn_const (c := Qc γ * Real.log S))).add
      ((continuousOn_const (c := Qc γ)).mul L2.continuousOn)
    refine (hcont.mono ?_).congr ?_
    · exact fun p hp => (show (0 : ℝ) < p.2 from hp.2)
    · exact fun p hp => hform p.1 p.2 hp.2
  · rw [integral_congr_ae (ae_of_all _ fun u => hform u ρ hρ),
      integral_congr_ae (ae_of_all _ fun v => hform v r hr)]
    rw [integral_add_const_add_mul (L1.integrable_smooth hρ hr.le w)
        (L2.integrable_smooth hρ hr.le w),
      integral_add_const_add_mul (L1.integrable_smooth hr hρ.le w)
        (L2.integrable_smooth hr hρ.le w),
      L1.integral_swap w hr hρ, L2.integral_swap w hr hρ]

/-- **`G1ProfileStmt` holds** (gap, integrability, convergence and continuity parts). -/
theorem g1ProfileStmt_holds : G1ProfileStmt :=
  g1ProfileStmt_of_conv_cont g1ProfileConvStmt g1ProfileContStmt

/-- **`G1RegRepRC2Stmt` from the analytic map input alone.** -/
theorem g1RegRepRC2Stmt_of_psiExt (h : G1PsiExtStmt) : G1RegRepRC2Stmt :=
  g1RegRepRC2Stmt_of_psi_profile h g1ProfileStmt_holds

end G1RC
end Thm18Asm
end QuantumZipper
