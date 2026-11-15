/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseLaw
import InteractingSLE.Spec.Sec6.Prop65Gauss
import QuantumZipper.Proofs.Loewner.CoreArc1

/-!
# Reading the phase from the retained Gaussian kernel

Packet PROVE-PHASECLAUSE. Astra's follow-up 5 §3.2 (R73, `source/external/AstraIG1/ig1_followup5.txt` L456–L483):
"Let `M⁰_t` be the canonical mean with exposed heights `−Λ, +Λ`. In the fixed initial pocket coordinate, the
derivative corrections cancel and `M_t(z) − M⁰_t(z) = δ_t ω_t(z)`, `ω_t(z) = (Arg(g_t(z) − V^R_t) − Arg(g_t(z) −
V^L_t))/π`. For every positive time, `V^L_t < V^R_t` and `ω_t(z) > 0` at an interior active point. […] Right
continuity of the retained filtration makes this constant measurable at time zero."

At a fixed capacity time `q > 0`, the retained kernel σ-algebra `𝓜_q` determines the conditional mean of the field,
hence the phase: on the safe event of a far bump `ψ` (supported where the hull cannot reach by time `q`), the
conditional characteristic function of `X(tψ)` given `𝓜_q` is Gaussian with mean `t (𝔥_A + δ_q J)`
(`ae_condExp_cexp_chartTransport_eq_energy` and the phase mean identification), the mean is `𝓜_q`-measurable up to
null sets (`Sec6.Prop65.exists_measurable_ae_eq_of_condCharFun`, localized), and the tested window
`J = ∫ ω_q ψ > 0` (`phaseGap_pos`). So `δ_q = (E[X(ψ) | 𝓜_q] − 𝔥_A)/J`.

## Main results

* `arg_sub_lt_arg_sub`, `meanCan_shift_one_sub_add_one_pos`: `ω_q > 0` on `ℍ` when `V^L_q < V^R_q`;
* `phaseGap`, `phaseInt_eq_add_mul`, **`phaseGap_pos`**: the tested window is positive on a safe time;
* `exists_isForwardSol_rpath_of_im_ge`: points of height `≥ y` are alive up to capacity `y²/8`;
* `exists_measurable_eq_on_of_condCharFun`: the localized measurable version of a conditional Gaussian mean;
* **`exists_measurableSet_iff_phase`**: at every `q > 0` each event `{c₀ ∈ B}` agrees almost surely on the live
  event with an event of `𝓜_q`.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper Complex
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PhaseClause

open Restart.DomainMarkov Restart.DomainMarkov.Mean Restart.DomainMarkov.Aux79 Coupling Ito PhaseSel PhaseMart
  PocketTraversal Lemma71C

/-! ### The harmonic measure of the exposed interval is positive -/

section Window

theorem mul_sqrt_lt_mul_sqrt {u v y : ℝ} (hy : 0 < y) (huv : u < v) :
    u * Real.sqrt (v ^ 2 + y ^ 2) < v * Real.sqrt (u ^ 2 + y ^ 2) := by
  have hsu : 0 < Real.sqrt (u ^ 2 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsv : 0 < Real.sqrt (v ^ 2 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hy2 : 0 < y ^ 2 := by positivity
  rcases lt_or_ge u 0 with hu | hu
  · rcases lt_or_ge v 0 with hv | hv
    · have hA : 0 ≤ -v * Real.sqrt (u ^ 2 + y ^ 2) := mul_nonneg (by linarith) hsu.le
      have hB : 0 ≤ -u * Real.sqrt (v ^ 2 + y ^ 2) := mul_nonneg (by linarith) hsv.le
      have h1 : -v * Real.sqrt (u ^ 2 + y ^ 2) < -u * Real.sqrt (v ^ 2 + y ^ 2) := by
        refine (sq_lt_sq₀ hA hB).1 ?_
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        have h2 : 0 < (u ^ 2 - v ^ 2) * y ^ 2 := mul_pos (by nlinarith) hy2
        nlinarith [h2]
      linarith
    · have h1 : u * Real.sqrt (v ^ 2 + y ^ 2) < 0 := mul_neg_of_neg_of_pos hu hsv
      have h2 : 0 ≤ v * Real.sqrt (u ^ 2 + y ^ 2) := mul_nonneg hv hsu.le
      linarith
  · have hA : 0 ≤ u * Real.sqrt (v ^ 2 + y ^ 2) := mul_nonneg hu hsv.le
    have hB : 0 ≤ v * Real.sqrt (u ^ 2 + y ^ 2) := mul_nonneg (hu.trans huv.le) hsu.le
    refine (sq_lt_sq₀ hA hB).1 ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have h2 : 0 < (v ^ 2 - u ^ 2) * y ^ 2 := mul_pos (by nlinarith) hy2
    nlinarith [h2]

/-- **Moving the base point to the right increases the argument** in `ℍ`: `arg (ξ − a) < arg (ξ − b)` for `a < b`. -/
theorem arg_sub_lt_arg_sub {ξ : ℂ} (hξ : 0 < ξ.im) {a b : ℝ} (hab : a < b) :
    arg (ξ - a) < arg (ξ - b) := by
  have h1 : 0 < (ξ - a).im := by simpa using hξ
  have h2 : 0 < (ξ - b).im := by simpa using hξ
  rw [arg_of_im_pos h1, arg_of_im_pos h2]
  have hnorm : ∀ c : ℝ, ‖ξ - c‖ = Real.sqrt ((ξ.re - c) ^ 2 + ξ.im ^ 2) := fun c => by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
    ring
  refine Real.arccos_lt_arccos (abs_le.1 (abs_re_div_norm_le_one _)).1 ?_
    (abs_le.1 (abs_re_div_norm_le_one _)).2
  have hsa : 0 < ‖ξ - a‖ := norm_pos_iff.2 fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hsb : 0 < ‖ξ - b‖ := norm_pos_iff.2 fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  rw [div_lt_div_iff₀ hsb hsa, hnorm a, hnorm b]
  simp only [sub_re, ofReal_re]
  exact mul_sqrt_lt_mul_sqrt hξ (by linarith)

variable {nL nR : ℕ} {κ : ℝ}

/-- **The window `ω_q = (arg(ξ − V^R) − arg(ξ − V^L))/π` is positive**: the explicit mean of the word with seed
weights shifted by `1`, minus the explicit mean, plus `1`, is `ω_q(f_q(y)) > 0` when the seeds are separated. -/
theorem meanCan_shift_one_sub_add_one_pos (hκ : 0 < κ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ} {s : ℝ≥0} {y : ℂ}
    (hsep : vL 0 s < vR 0 s) (hy : 0 < (fwdMap (rpath w) s y).im) :
    0 < meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s y - meanCan κ ρL ρR w vL vR s y + 1 := by
  rw [meanCan_shift κ ρL ρR w vL vR s y 1]
  have harg := arg_sub_lt_arg_sub hy (a := vL 0 s - w s) (b := vR 0 s - w s) (by linarith)
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  set A := arg (fwdMap (rpath w) s y - ((vR 0 s - w s : ℝ) : ℂ))
  set B := arg (fwdMap (rpath w) s y - ((vL 0 s - w s : ℝ) : ℂ))
  have e : meanCan κ ρL ρR w vL vR s y + 1 / (π / Real.sqrt κ) *
      phaseWin κ (vL 0 s - w s) (vR 0 s - w s) (fwdMap (rpath w) s y) - meanCan κ ρL ρR w vL vR s y + 1 =
      (A - B) / π := by
    simp only [phaseWin]
    field_simp
    ring
  rw [e]
  exact div_pos (by linarith) Real.pi_pos

end Window

/-! ### The tested window is positive on a safe time -/

section Gap

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞}
  {δ N : ℝ} {σ₀ r s : ℝ≥0}

/-- **The tested window** `J = 𝔥_B − 𝔥_A + ∫ψ = ∫ ω_s ψ`. -/
def phaseGap (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ≥0) (ψ : ℂ → ℝ) : ℝ :=
  (∫ z, meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s z * ψ z) -
    (∫ z, meanCan κ ρL ρR w vL vR s z * ψ z) + (∫ z, ψ z)

theorem phaseInt_eq_add_mul (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ≥0) (ψ : ℂ → ℝ) (c : ℝ) :
    phaseInt κ ρL ρR w vL vR s ψ c =
      (∫ z, meanCan κ ρL ρR w vL vR s z * ψ z) + c * phaseGap κ ρL ρR w vL vR s ψ := by
  unfold phaseInt phaseGap
  ring

/-- **The tested window is positive on a safe time when the seeds are separated**, for a nonnegative test function
of positive mass. -/
theorem phaseGap_pos (hκ : 0 < κ) {ψ : ℂ → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hψ0 : ∀ z, 0 ≤ ψ z) (hψpos : 0 < ∫ z, ψ z) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ₀})
    (hKH : tsupport ψ ⊆ H) (h : IsSafeAt (tsupport ψ) δ N σ₀ ζ₀ w r) (hδ : 0 < δ) (hs : s ≤ r)
    (hsep : vL 0 s < vR 0 s) : 0 < phaseGap κ ρL ρR w vL vR s ψ := by
  have hA := integrable_meanCan_mul (κ := κ) hψc hψs hw hKH h hδ hs ρL ρR vL vR
  have hB := integrable_meanCan_mul (κ := κ) hψc hψs hw hKH h hδ hs (shiftL κ ρL 1) (shiftR κ ρR 1) vL vR
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  set g : ℂ → ℝ := fun z => (meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s z -
    meanCan κ ρL ρR w vL vR s z + 1) * ψ z with hg
  have hfac : ∀ z ∈ tsupport ψ, 0 < meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s z -
      meanCan κ ρL ρR w vL vR s z + 1 := fun z hz =>
    meanCan_shift_one_sub_add_one_pos hκ ρL ρR hsep (hδ.trans_le (h.le_im_fwdMap hw hKH hs hz))
  have hgi : Integrable g := by
    have e : g = fun z => (meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s z * ψ z -
        meanCan κ ρL ρR w vL vR s z * ψ z) + ψ z := by
      funext z; simp only [hg]; ring
    rw [e]
    exact (hB.sub hA).add hψi
  have hg0 : 0 ≤ g := fun z => by
    by_cases hz : z ∈ tsupport ψ
    · exact mul_nonneg (hfac z hz).le (hψ0 z)
    · simp [hg, image_eq_zero_of_notMem_tsupport hz]
  have hsupp : Function.support g = Function.support ψ := by
    ext z
    simp only [Function.mem_support, ne_eq]
    constructor
    · intro hgz hψz
      exact hgz (by simp [hg, hψz])
    · intro hψz
      exact mul_ne_zero (hfac z (subset_tsupport _ hψz)).ne' hψz
  have hψm : 0 < volume (Function.support ψ) :=
    (integral_pos_iff_support_of_nonneg hψ0 hψi).1 hψpos
  have hgpos : 0 < ∫ z, g z := (integral_pos_iff_support_of_nonneg hg0 hgi).2 (hsupp ▸ hψm)
  have e : phaseGap κ ρL ρR w vL vR s ψ = ∫ z, g z := by
    have hi : Integrable (fun z => meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s z * ψ z -
        meanCan κ ρL ρR w vL vR s z * ψ z) := hB.sub hA
    have e3 : ∫ z, g z = ∫ z, ((meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s z * ψ z -
        meanCan κ ρL ρR w vL vR s z * ψ z) + ψ z) :=
      integral_congr_ae (ae_of_all _ fun z => by simp only [hg]; ring)
    rw [e3, integral_add hi hψi, integral_sub hB hA, phaseGap]
  rw [e]
  exact hgpos

end Gap

/-! ### Points of large height are alive -/

section Alive

variable {w : ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞}

/-- **Points of height at least `y` are alive up to capacity `y²/8`** (`QuantumZipper.CoreArc.
exists_isForwardSol_of_im_ge` for the clamped driver). -/
theorem exists_isForwardSol_rpath_of_im_ge (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ₀}) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < ζ₀) {z : ℂ} {y : ℝ} (hy : 0 < y) (hyz : y ≤ z.im) (hqy : (q : ℝ) ≤ y ^ 2 / 8) :
    ∃ u, IsForwardSol (rpath w) z q u := by
  have hB : Continuous (clampDrv (rpath w) q) := continuous_clampDrv q.coe_nonneg (continuousOn_rpath hw hq)
  obtain ⟨u, hu⟩ := CoreArc.exists_isForwardSol_of_im_ge hB hy hyz
  have hu' : IsForwardSol (clampDrv (rpath w) q) z q u := isForwardSol_of_le hu q.coe_nonneg hqy
  refine ⟨u, ?_⟩
  have heq : ∀ r ∈ Icc (0 : ℝ) q, clampDrv (rpath w) q r = rpath w r := fun r hr => clampDrv_eqOn hr
  unfold IsForwardSol at hu' ⊢
  refine ⟨hu'.1, fun t ht => ?_⟩
  rw [← heq t ht]
  exact hu'.2 t ht

end Alive

/-! ### A localized measurable version of a conditional Gaussian mean -/

section Extract

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **A conditional Gaussian mean on an event of `𝒢` has a `𝒢`-measurable version there**
(`Sec6.Prop65.exists_measurable_ae_eq_of_condCharFun` applied to the variables restricted to the event). -/
theorem exists_measurable_eq_on_of_condCharFun [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {X μ V : Ω → ℝ}
    (hX : Measurable X) {E : Set Ω} (hE : MeasurableSet[𝒢] E) (hV : Measurable[𝒢] (E.indicator V))
    (hc : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ E → P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒢] ω =
      cexp (I * ((t * μ ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ)) :
    ∃ μ' : Ω → ℝ, Measurable[𝒢] μ' ∧ ∀ᵐ ω ∂P, ω ∈ E → μ' ω = μ ω := by
  have hEm : MeasurableSet E := h𝒢 _ hE
  have hc' : ∀ t : ℝ, P[fun ω => cexp (I * ((t * E.indicator X ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cexp (I * ((t * E.indicator μ ω : ℝ) : ℂ)) *
        ((Real.exp (-(1 / 2) * (t ^ 2 * E.indicator V ω)) : ℝ) : ℂ) := by
    intro t
    have e : (fun ω => cexp (I * ((t * E.indicator X ω : ℝ) : ℂ))) =
        E.indicator (fun ω => cexp (I * ((t * X ω : ℝ) : ℂ))) + Eᶜ.indicator (fun _ => (1 : ℂ)) := by
      funext ω
      by_cases hω : ω ∈ E <;> simp [hω]
    have hint1 : Integrable (fun ω => cexp (I * ((t * X ω : ℝ) : ℂ))) P :=
      Integrable.of_bound ((by fun_prop : Continuous fun x : ℝ => cexp (I * ((t * x : ℝ) : ℂ))).measurable.comp
        hX).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
          rw [mul_comm I]; exact (norm_exp_ofReal_mul_I _).le)
    have hint2 : Integrable (Eᶜ.indicator fun _ => (1 : ℂ)) P := (integrable_const 1).indicator hEm.compl
    rw [e]
    have h1 := condExp_add (m := 𝒢) (hint1.indicator hEm) hint2
    have h2 := condExp_indicator (m := 𝒢) hint1 hE
    have h3 : P[Eᶜ.indicator (fun _ => (1 : ℂ)) | 𝒢] = Eᶜ.indicator (fun _ => 1) :=
      condExp_of_stronglyMeasurable h𝒢 (stronglyMeasurable_const.indicator hE.compl) hint2
    filter_upwards [h1, h2, hc t] with ω e1 e2 e3
    rw [e1, Pi.add_apply, e2, h3]
    by_cases hω : ω ∈ E
    · simp only [indicator_of_mem hω, indicator_of_notMem (show ω ∉ Eᶜ from fun h => h hω), add_zero]
      exact e3 hω
    · simp [hω]
  obtain ⟨μ', hμ'm, hμ'e⟩ := Sec6.Prop65.exists_measurable_ae_eq_of_condCharFun hV hc'
  refine ⟨μ', hμ'm, ?_⟩
  filter_upwards [hμ'e] with ω h hω
  rw [h, indicator_of_mem hω]

end Extract

/-! ### Seed separation along a driver continuous before its lifetime -/

section Sep

variable {Ω : Type*} {nL nR : ℕ} {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}

/-- **The seeds are separated at positive times before the lifetime** (`PocketTraversal.geom_sep` for the driver
frozen at `t`, `PocketPhaseMeans.geomLW_eq_frz`). -/
theorem geomLW_lt_geomRW_of_pos (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (i : Fin nL) (j : Fin nR) {t : ℝ≥0} (ht : 0 < t) {ω : Ω}
    (htT : (t : ℝ≥0∞) < T ω) : geomLW W xL i t ω < geomRW W xR j t ω := by
  rw [PocketPhaseMeans.geomLW_eq_frz hc xL i htT le_rfl, PocketPhaseMeans.geomRW_eq_frz hc xR j htT le_rfl]
  have hc' : ∀ ω, Continuous fun s => Lemma71C.frz W T t s ω := Lemma71C.continuous_frz hc t
  have h1 := geomLW_le hc' xL ω t i
  have h2 := le_geomRW hc' xR ω t j
  rcases lt_or_ge (geomLW (Lemma71C.frz W T t) xL i t ω) (geomRW (Lemma71C.frz W T t) xR j t ω) with h | h
  · exact h
  · exact absurd (le_antisymm h2 (h.trans h1)).symm (geom_sep hc' xL xR ω t ht i j (le_antisymm h1 (h2.trans h)))

end Sep

/-! ### The far bumps -/

section Far

/-- The point `(n + 1) i`. -/
def farPt (n : ℕ) : ℂ := ⟨0, (n : ℝ) + 1⟩

theorem farPt_im_pos (n : ℕ) : 0 < (farPt n).im := by
  show (0 : ℝ) < (n : ℝ) + 1
  positivity

/-- **The far bump probes**: the bump of radius `(n + 1)/4` at `(n + 1) i`. -/
def farBump (n : ℕ) : TestOn upperHalfPlaneOpens := Coupling.MartMeans.bumpTestAt (farPt n) (farPt_im_pos n) 0

theorem farBump_nonneg (n : ℕ) (z : ℂ) : 0 ≤ farBump n z := GFF.bumpFun_nonneg _ _ _

theorem integral_farBump_pos (n : ℕ) : 0 < ∫ z, farBump n z := by
  show 0 < ∫ z, GFF.bumpFun (farPt n) (Coupling.MartMeans.bumpRadius (farPt n) 0) z
  rw [GFF.integral_bumpFun (Coupling.MartMeans.bumpRadius_pos (farPt_im_pos n) 0)]
  have := Coupling.MartMeans.bumpRadius_pos (farPt_im_pos n) 0
  have := GFF.bumpMass_pos
  positivity

/-- The far bump is supported at height at least `(n + 1)/2`. -/
theorem le_im_of_mem_tsupport_farBump {n : ℕ} {z : ℂ} (hz : z ∈ tsupport (farBump n)) :
    ((n : ℝ) + 1) / 2 ≤ z.im := by
  have h := Coupling.MartMeans.tsupport_bumpFun_subset_locBall (farPt_im_pos n) 0 hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at h
  have h2 := (Complex.abs_im_le_norm (z - farPt n)).trans h
  rw [Complex.sub_im, abs_le] at h2
  have e : Coupling.MartMeans.locRad (farPt n) 0 = ((n : ℝ) + 1) / 2 := by
    simp only [Coupling.MartMeans.locRad, farPt]
    norm_num
  have e2 : (farPt n).im = (n : ℝ) + 1 := rfl
  rw [e, e2] at h2
  linarith [h2.1]

end Far

/-! ### The phase is measurable for the retained σ-algebra on the live event -/

section Read

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ}
  {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}

/-- **Every live point is safe for some far bump at some level** at a time before the lifetime. -/
theorem exists_mem_safeSet_farBump {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) {q : ℝ≥0} {ω : Ω}
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) :
    ∃ n m : ℕ, ω ∈ safeSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) univ (farBump n)
      (1 / ((m : ℝ) + 1)) q := by
  have hw : ContinuousOn (fun t => segDriver (γ ω) t) {t : ℝ≥0 | (t : ℝ≥0∞) < capLife (γ ω)} :=
    (hγ ω).segDriver_spec.2.1
  obtain ⟨n, hn⟩ := exists_nat_ge (8 * ((q : ℝ) + 1))
  have hy : 0 < ((n : ℝ) + 1) / 2 := by positivity
  have hq8 : (q : ℝ) ≤ (((n : ℝ) + 1) / 2) ^ 2 / 8 := by
    have h0 : (0 : ℝ) ≤ q := q.coe_nonneg
    nlinarith
  have halive : ∀ z ∈ tsupport (farBump n), ∃ u, IsForwardSol (rpath fun t => segDriver (γ ω) t) z q u :=
    fun z hz => exists_isForwardSol_rpath_of_im_ge hw hq hy (le_im_of_mem_tsupport_farBump hz) hq8
  obtain ⟨δ, hδ, hsafe⟩ := exists_isSafeAt_self hw (hγ ω).segDriver_spec.1 (farBump n).hasCompactSupport.isCompact
    (tsupport_subset_H _) hq halive
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  exact ⟨n, m, mem_univ ω, hsafe.mono hm.le le_rfl le_rfl⟩

/-- **The phase is measurable for the retained σ-algebra on the live event** (follow-up 5 (3.2) at one positive time
`q`). Let `γ` be driven with prefixes adapted to `𝓗`, the marks `𝓗₀`-measurable, the chart measurable for `𝒢 ≤ 𝓜`,
the physical field Gaussian given `𝓜 ≥ 𝓗_q` on the chart preimage of the active domain with mean `M` (`hcond`), and
the chart transport of `M` the coupling mean of the phase-`d` word (`hmean`), with `d = c₀` almost surely on the live
event. Then for every Borel set `B` there is an event `S ∈ 𝓜` with `{c₀ ∈ B} = S` almost surely on the live event:
on the safe event of each far bump `ψ`, `c₀ = (E[X(ψ) | 𝓜] − 𝔥_A)/J` with `J > 0`. -/
theorem exists_measurableSet_iff_phase [IsProbabilityMeasure P] (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ}
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hpre : IsPrefixAdapted 𝓗 γ)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxL : Measurable[𝓗 0] xL)
    (hxR : Measurable[𝓗 0] xR) {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ) {q : ℝ≥0} (hq : 0 < q) (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓜 : 𝓜 q ≤ mΩ) (h𝒢𝓜 : 𝒢 ≤ 𝓜 q)
    (h𝓗𝓜 : 𝓗 q ≤ 𝓜 q)
    (M : Ω → DistOn upperHalfPlaneOpens)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (q : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q))
            φ φ : ℝ) : ℂ)))
    {d : Ω → ℝ}
    (hmean : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ω ∈ Restart.DomainMarkov.avoidSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) ψ q →
      Chart.chartTransport (hc ω) 1 a k (M ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
          (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
            (geomRW (fun t ω => segDriver (γ ω) t) xR) d ω q) z * ψ z)
    {c₀ : Ω → ℝ} (hdc : ∀ᵐ ω ∂P, (q : ℝ≥0∞) < capLife (γ ω) → d ω = c₀ ω) {B : Set ℝ} (hB : MeasurableSet B) :
    ∃ S : Set Ω, MeasurableSet[𝓜 q] S ∧ ∀ᵐ ω ∂P, (q : ℝ≥0∞) < capLife (γ ω) → (c₀ ω ∈ B ↔ ω ∈ S) := by
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  set VL := geomLW W xL with hVLdef
  set VR := geomRW W xR with hVRdef
  set ζ : Ω → ℝ≥0∞ := fun ω => capLife (γ ω) with hζdef
  have hWa : AdaptedBefore 𝓗 ζ W := adaptedBefore_segDriver_of_isDrivenCurve hγ hpre
  have hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω => (hγ ω).segDriver_spec.2.1
  have hVLa : ∀ i, AdaptedBefore 𝓗 ζ (VL i) := fun i => PocketPhaseMeans.adaptedBefore_geomLW hWc hWa hxL i
  have hVRa : ∀ j, AdaptedBefore 𝓗 ζ (VR j) := fun j => PocketPhaseMeans.adaptedBefore_geomRW hWc hWa hxR j
  have hreg : ∀ ω, IsForceReg W VL VR ζ ω := PocketCoupling.isForceReg_segDriver hγ xL xR
  have hG0 : MeasurableSet[𝓗 0] (univ : Set Ω) := MeasurableSet.univ
  have hGc : ∀ ω ∈ (univ : Set Ω), ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω _ => hWc ω
  have h𝒢 : 𝒢 ≤ mΩ := h𝒢𝓜.trans h𝓜
  have hX : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => h𝒢 _ (hdom z))
      (fun z => (hfwd z).mono h𝒢 le_rfl) (fun z => (hliftm z).mono h𝒢 le_rfl) hliftc hh 1 a k
  have hδ : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := fun m => by positivity
  set E : ℕ → ℕ → Set Ω := fun n m => safeSet W ζ univ (farBump n) (1 / ((m : ℝ) + 1)) q with hEdef
  have hEm : ∀ n m, MeasurableSet[𝓜 q] (E n m) := fun n m =>
    h𝓗𝓜 _ (measurableSet_safeSet hWa hGc hG0 (tsupport_subset_H _) (hδ m) q)
  set IA : ℕ → ℕ → Ω → ℝ := fun n m => meanK κ ρL ρR W VL VR ζ univ (farBump n) (1 / ((m : ℝ) + 1)) q
    with hIAdef
  set IB : ℕ → ℕ → Ω → ℝ := fun n m =>
    meanK κ (shiftL κ ρL 1) (shiftR κ ρR 1) W VL VR ζ univ (farBump n) (1 / ((m : ℝ) + 1)) q with hIBdef
  have hIA : ∀ n m, Measurable[𝓜 q] (IA n m) := fun n m =>
    (measurable_meanK hWa hGc hG0 (tsupport_subset_H _) (hδ m) κ ρL ρR hVLa hVRa
      (farBump n).continuous.measurable q).mono h𝓗𝓜 le_rfl
  have hIB : ∀ n m, Measurable[𝓜 q] (IB n m) := fun n m =>
    (measurable_meanK hWa hGc hG0 (tsupport_subset_H _) (hδ m) κ (shiftL κ ρL 1) (shiftR κ ρR 1) hVLa hVRa
      (farBump n).continuous.measurable q).mono h𝓗𝓜 le_rfl
  -- the conditional characteristic function of the tested field on the safe events
  have hker : ∀ n m (t : ℝ), ∀ᵐ ω ∂P, ω ∈ E n m →
      P[fun ω => Complex.exp (Complex.I * ((t * Chart.chartTransport (hc ω) 1 a k (h ω) (farBump n) : ℝ) : ℂ)) |
        𝓜 q] ω = Complex.exp (Complex.I * ((t * Chart.chartTransport (hc ω) 1 a k (M ω) (farBump n) : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (t ^ 2 * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) q (farBump n))) : ℝ) :
            ℂ) := by
    intro n m t
    have hcl := ae_condExp_cexp_chartTransport_eq_energy (P := P) (ζ := ζ) (W := W) (𝒢 := 𝓜 q) h𝓜 hc
      (fun z => h𝒢𝓜 _ (hdom z)) (fun z => (hfwd z).mono h𝒢𝓜 le_rfl) (fun z => (hliftm z).mono h𝒢𝓜 le_rfl)
      hliftc hh a k q (Mset := univ) (fun φ => by filter_upwards [hcond φ] with ω hω _ using hω) (t • farBump n)
      (hEm n m) (ae_of_all _ fun ω hω => by
        have hs := hω.2
        have hdis := disjoint_fwdHull_of_isSafeAt (hWc ω) (tsupport_subset_H _) hs
        refine ⟨mem_univ ω, ⟨hs.1, ?_⟩, hWc ω, (hreg ω).1⟩
        exact Disjoint.mono_left (tsupport_smul_subset_right (fun _ : ℂ => t) _) hdis)
    filter_upwards [hcl] with ω hω hωE
    have hcoe : (⇑(t • farBump n) : ℂ → ℝ) = t • ⇑(farBump n) := by
      funext y
      simp
    have e1 : (fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hc ω') 1 a k (h ω') (t • farBump n) : ℂ))) =
        fun ω' => Complex.exp (Complex.I * ((t * Chart.chartTransport (hc ω') 1 a k (h ω') (farBump n) : ℝ) : ℂ)) := by
      funext ω'
      rw [map_smul, smul_eq_mul]
    rw [e1] at hω
    rw [hω hωE, map_smul, smul_eq_mul, hcoe, Coupling.MartMeans.loewnerGreenEnergy_smul, Complex.ofReal_exp,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- a measurable version of the tested mean on each safe event
  have hext : ∀ n m, ∃ μ' : Ω → ℝ, Measurable[𝓜 q] μ' ∧ ∀ᵐ ω ∂P, ω ∈ E n m →
      μ' ω = Chart.chartTransport (hc ω) 1 a k (M ω) (farBump n) := by
    intro n m
    have hV : (E n m).indicator (fun ω => loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) q (farBump n)) =
        energyK W ζ univ (farBump n) (1 / ((m : ℝ) + 1)) q := by
      funext ω
      by_cases hω : ω ∈ E n m
      · rw [indicator_of_mem hω]
        simp only [energyK, show ω ∈ safeSet W ζ univ (farBump n) (1 / ((m : ℝ) + 1)) q from hω, ↓reduceIte]
        rfl
      · rw [indicator_of_notMem hω]
        simp only [energyK, show ω ∉ safeSet W ζ univ (farBump n) (1 / ((m : ℝ) + 1)) q from hω, ↓reduceIte]
    refine exists_measurable_eq_on_of_condCharFun h𝓜
      ((LQGMetric.measurable_distOn_apply (farBump n)).comp hX) (hEm n m) ?_ (hker n m)
    rw [hV]
    exact (measurable_energyK hWa hGc hG0 (tsupport_subset_H _) (hδ m) (farBump n).continuous.measurable q).mono
      h𝓗𝓜 le_rfl
  choose μ' hμ'm hμ'e using hext
  -- the explicit form of the tested mean on each safe event
  have hform : ∀ n m, ∀ᵐ ω ∂P, ω ∈ E n m →
      0 < IB n m ω - IA n m ω + (∫ z, farBump n z) ∧
        c₀ ω = (μ' n m ω - IA n m ω) / (IB n m ω - IA n m ω + (∫ z, farBump n z)) := by
    intro n m
    filter_upwards [hμ'e n m, hmean (farBump n), hdc] with ω h1 h2 h3 hω
    have hs : IsSafeAt (tsupport (farBump n)) (1 / ((m : ℝ) + 1)) q q (ζ ω) (W · ω) q := hω.2
    have hlive : (q : ℝ≥0∞) < ζ ω := hs.1
    have hord := (hreg ω).2.2.2.2 q hlive
    have hA : IA n m ω = ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) q z *
        farBump n z := by
      simp only [hIAdef, meanK, show ω ∈ safeSet W ζ univ (farBump n) (1 / ((m : ℝ) + 1)) q from hω, ↓reduceIte]
    have hB' : IB n m ω = ∫ z, meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) q z * farBump n z := by
      simp only [hIBdef, meanK, show ω ∈ safeSet W ζ univ (farBump n) (1 / ((m : ℝ) + 1)) q from hω, ↓reduceIte]
    have hgap : IB n m ω - IA n m ω + (∫ z, farBump n z) =
        phaseGap κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) q (farBump n) := by
      rw [hA, hB', phaseGap]
    have hsep : VL 0 q ω < VR 0 q ω := geomLW_lt_geomRW_of_pos hWc xL xR 0 0 hq hlive
    have hJ : 0 < IB n m ω - IA n m ω + (∫ z, farBump n z) := by
      rw [hgap]
      exact phaseGap_pos hκ (farBump n).continuous (farBump n).hasCompactSupport (farBump_nonneg n)
        (integral_farBump_pos n) (hWc ω) (tsupport_subset_H _) hs (hδ m) le_rfl hsep
    have hdis : Disjoint (tsupport (farBump n)) (fwdHull (rpath (W · ω)) q) :=
      disjoint_fwdHull_of_isSafeAt (hWc ω) (tsupport_subset_H _) hs
    have hav : ω ∈ Restart.DomainMarkov.avoidSet W ζ (farBump n) q := ⟨hlive, hdis⟩
    have hint := integral_couplingMean_phase (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hκ
      (farBump n).continuous (farBump n).hasCompactSupport (hWc ω) (tsupport_subset_H _) hs (hδ m) le_rfl
      hord.1 hord.2 (isBoundedHarmonicExtension_phaseProc (ρL := ρL) (ρR := ρR) hκ d (hord.1 0) (hord.2 0))
    have hval : μ' n m ω = IA n m ω + c₀ ω * (IB n m ω - IA n m ω + (∫ z, farBump n z)) := by
      rw [h1 hω, h2 hav, ← h3 hlive, hgap, hA]
      rw [← phaseInt_eq_add_mul]
      exact hint
    refine ⟨hJ, ?_⟩
    rw [hval]
    field_simp
    ring
  -- the event
  set S : Set Ω := ⋃ n, ⋃ m, E n m ∩
    {ω | (μ' n m ω - IA n m ω) / (IB n m ω - IA n m ω + (∫ z, farBump n z)) ∈ B} with hSdef
  refine ⟨S, ?_, ?_⟩
  · refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m => (hEm n m).inter ?_
    exact (((hμ'm n m).sub (hIA n m)).div (((hIB n m).sub (hIA n m)).add_const _)) hB
  · filter_upwards [ae_all_iff.2 fun n => ae_all_iff.2 fun m => hform n m] with ω hω hlive
    constructor
    · intro hcB
      obtain ⟨n, m, hnm⟩ := exists_mem_safeSet_farBump hγ hlive
      refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨m, hnm, ?_⟩⟩
      show _ ∈ B
      rw [← (hω n m hnm).2]
      exact hcB
    · intro hS
      obtain ⟨n, hn⟩ := mem_iUnion.1 hS
      obtain ⟨m, hnm, hmB⟩ := mem_iUnion.1 hn
      rw [(hω n m hnm).2]
      exact hmB

end Read

/-! ### From the phase read at positive times to the retained filtration -/

section Transfer

variable {Ω : Type*} {𝓐 𝓑 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The events that agree almost surely on `L` with an event of `𝓑` (a σ-algebra). -/
@[instance_reducible]
def aeTraceSigma (𝓑 : MeasurableSpace Ω) (P : @Measure Ω mΩ) (L : Set Ω) : MeasurableSpace Ω where
  MeasurableSet' D := ∃ D' : Set Ω, MeasurableSet[𝓑] D' ∧ ∀ᵐ ω ∂P, ω ∈ L → (ω ∈ D ↔ ω ∈ D')
  measurableSet_empty := ⟨∅, @MeasurableSet.empty Ω 𝓑, ae_of_all _ fun _ _ => Iff.rfl⟩
  measurableSet_compl := fun _ ⟨D', hD', h⟩ =>
    ⟨D'ᶜ, hD'.compl, h.mono fun _ h hL => not_congr (h hL)⟩
  measurableSet_iUnion := fun f hf => by
    choose g hg h using hf
    refine ⟨⋃ i, g i, MeasurableSet.iUnion hg, ?_⟩
    filter_upwards [ae_all_iff.2 h] with ω hω hL
    simp only [mem_iUnion]
    exact exists_congr fun i => hω i hL

/-- **Adding the phase to a smaller σ-algebra**: if every event `{c₀ ∈ B}` agrees almost surely on `L` with an event of
`𝓑 ⊇ 𝓐`, then so does every event of `𝓐 ∨ σ(c₀)`. -/
theorem exists_ae_iff_of_sup_comap (h𝓐𝓑 : 𝓐 ≤ 𝓑) {L : Set Ω} {c₀ : Ω → ℝ}
    (hc : ∀ B : Set ℝ, MeasurableSet B → ∃ S : Set Ω, MeasurableSet[𝓑] S ∧
      ∀ᵐ ω ∂P, ω ∈ L → (c₀ ω ∈ B ↔ ω ∈ S))
    {D : Set Ω} (hD : MeasurableSet[𝓐 ⊔ MeasurableSpace.comap c₀ inferInstance] D) :
    ∃ D' : Set Ω, MeasurableSet[𝓑] D' ∧ ∀ᵐ ω ∂P, ω ∈ L → (ω ∈ D ↔ ω ∈ D') := by
  have hle : 𝓐 ⊔ MeasurableSpace.comap c₀ inferInstance ≤ aeTraceSigma 𝓑 P L := by
    refine sup_le (fun D hD => ⟨D, h𝓐𝓑 _ hD, ae_of_all _ fun _ _ => Iff.rfl⟩) ?_
    rintro _ ⟨B, hB, rfl⟩
    obtain ⟨S, hS, h⟩ := hc B hB
    exact ⟨S, hS, h⟩
  exact hle D hD

/-- **The transfer hypothesis of `hasPhaseSafeLaw_chartTransport`** for `𝓐 ∨ σ(c₀)`: an event of `𝓐 ∨ σ(c₀)` almost
surely inside the live event `L ∈ 𝓐` is almost surely an event of `𝓑`. -/
theorem exists_ae_eq_of_sup_comap (h𝓐𝓑 : 𝓐 ≤ 𝓑) {L : Set Ω} (hL : MeasurableSet[𝓐] L) {c₀ : Ω → ℝ}
    (hc : ∀ B : Set ℝ, MeasurableSet B → ∃ S : Set Ω, MeasurableSet[𝓑] S ∧
      ∀ᵐ ω ∂P, ω ∈ L → (c₀ ω ∈ B ↔ ω ∈ S))
    {D : Set Ω} (hD : MeasurableSet[𝓐 ⊔ MeasurableSpace.comap c₀ inferInstance] D)
    (hDL : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ L) : ∃ D' : Set Ω, MeasurableSet[𝓑] D' ∧ D =ᵐ[P] D' := by
  obtain ⟨D'', hD'', h⟩ := exists_ae_iff_of_sup_comap h𝓐𝓑 hc hD
  refine ⟨D'' ∩ L, hD''.inter (h𝓐𝓑 _ hL), ?_⟩
  filter_upwards [h, hDL] with ω h1 h2
  show (ω ∈ D) = (ω ∈ D'' ∩ L)
  exact propext ⟨fun hω => ⟨(h1 (h2 hω)).1 hω, h2 hω⟩, fun hω => (h1 hω.2).2 hω.1⟩

/-- **The phase read at positive times is almost everywhere measurable** (the live events at the times `1/(n + 1)`
exhaust the sample space, the relative lifetime being positive). -/
theorem aemeasurable_of_forall_pos_iff {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    {𝓗 : Filtration ℝ≥0 mΩ} (hpre : IsPrefixAdapted 𝓗 γ) (𝓜 : ℝ≥0 → MeasurableSpace Ω)
    (h𝓜 : ∀ q, 𝓜 q ≤ mΩ) {c₀ : Ω → ℝ}
    (hc : ∀ q : ℝ≥0, 0 < q → ∀ B : Set ℝ, MeasurableSet B → ∃ S : Set Ω, MeasurableSet[𝓜 q] S ∧
      ∀ᵐ ω ∂P, (q : ℝ≥0∞) < capLife (γ ω) → (c₀ ω ∈ B ↔ ω ∈ S)) :
    AEMeasurable c₀ P := by
  refine NullMeasurable.aemeasurable fun B hB => ?_
  set qn : ℕ → ℝ≥0 := fun n => (1 / ((n : ℝ) + 1)).toNNReal with hqn
  have hqpos : ∀ n, 0 < qn n := fun n => Real.toNNReal_pos.2 (by positivity)
  choose S hSm hS using fun n => hc (qn n) (hqpos n) B hB
  have hL : ∀ n, MeasurableSet {ω | ((qn n : ℝ≥0) : ℝ≥0∞) < capLife (γ ω)} := fun n =>
    𝓗.le _ _ (measurableSet_lt_capLife hpre (fun ω => (hγ ω).zero) (qn n))
  refine (MeasurableSet.iUnion fun n => (h𝓜 _ _ (hSm n)).inter (hL n)).nullMeasurableSet.congr ?_
  filter_upwards [ae_all_iff.2 hS] with ω hω
  show (ω ∈ ⋃ n, S n ∩ {ω | ((qn n : ℝ≥0) : ℝ≥0∞) < capLife (γ ω)}) = (ω ∈ c₀ ⁻¹' B)
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨n, hn⟩ := mem_iUnion.1 h
    exact (hω n hn.2).2 hn.1
  · obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (PocketPhaseMeans.capLife_pos (hγ ω))
    have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr0'
    have hlt : ((qn n : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) := by
      refine lt_trans (ENNReal.coe_lt_coe.2 ?_) hr
      exact (Real.toNNReal_lt_iff_lt_coe (by positivity)).2 hn
    exact mem_iUnion.2 ⟨n, (hω n hlt).1 h, hlt⟩

end Transfer

end InteractingSLE.Sec7.PhaseClause
