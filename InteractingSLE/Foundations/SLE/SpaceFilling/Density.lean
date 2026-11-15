import QuantumZipper.Proofs.Thm11.AddendumAreaMart
import QuantumZipper.Proofs.RS.OnePointMart
import QuantumZipper.Proofs.RS.OnePointWeightedCore
import QuantumZipper.Proofs.RS.TransienceCanon
import InteractingSLE.Foundations.SLE.TraceGtEight
import QuantumZipper.Proofs.Thm11.MainMart
import Mathlib.Analysis.Complex.Schwarz

/-!
# Density of the SLE_κ trace for `κ > 8` ([RS05, Lemma 6.3 and (6.4)])

Packet `planning/packets/PROVE-RS05-74.md` (input of [RS05, Corollary 7.4]). Source:
S. Rohde, O. Schramm, *Basic properties of SLE*, `source/external/RS05/arxiv-latex/SLEcont.tex`,
Lemma 6.3 (`howclose`, lines 1749–1772: `Z(z) = ∞` a.s. for `κ ≥ 8`) and (6.4) (`dtz`, lines
1773–1800: `dist(z, γ[0,∞) ∪ ℝ) ≤ 2 Z(z)^{-1} Im z`); [Law] G. F. Lawler, *Conformally
Invariant Processes in the Plane*, Theorem 7.9 (p. 159).

For `a ∈ ℍ` write `Z_t = f_t(a)`, `Υ_t = Im Z_t / |f_t'(a)|` (QuantumZipper's `fwdLogCR = log Υ`)
and `S_t = sin arg Z_t`. The one-point local martingale `M_t = Υ_t^{κ/8-1} S_t^{8/κ-1}`
(QuantumZipper `RS.phiM`, zero generator `RS.dynkinGen_opDrift_phiM`, valid for every `κ`) is used
for `κ > 8`, where both exponents have opposite signs:

* if `Υ` stayed `≥ η` while `M` stayed `≤ λ`, then `S ≥ s₀ > 0`, hence
  `dlog Υ ≤ 4 s₀² dlog Im Z / 2`, so `Im Z` stays bounded below and `|Z| ≤ Im a/s₀`, and then
  `log Υ` decreases at least linearly in time — impossible (`fwdLogCR_le_of_sin_ge`, part D);
* by optional stopping and Markov's inequality, `ℙ[M reaches λ] ≤ M₀/λ` (part P).

Hence `inf_t Υ_t = 0` almost surely, and by the Schwarz lemma `dist(a, ∂H_t) ≤ 2 Υ_t` (part G);
the boundary of `H_t` in `ℍ` lies on the trace, so `a ∈ \overline{γ[0,∞)}` (this is the proof of
[RS05] (6.4) with Lemma 6.3; our martingale argument replaces the radial-time computation of
`E[Z(z)^a]`, which RS do not spell out).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS QuantumZipper.FwdClock

/-! ### Part D: deterministic decay of the log conformal radius -/

section Deterministic

variable {W : ℝ → ℝ}

/-- The log conformal radius at time `0` is `log Im a`. -/
theorem fwdLogCR_zero (hW : Continuous W) {a : ℂ} (ha : 0 < a.im) :
    fwdLogCR W 0 a = Real.log a.im := by
  have hsol0 : ∃ u, IsForwardSol W a 0 u := by
    refine exists_isForwardSol_of_not_mem_fwdHull (le_refl 0) (show a ∈ H from ha) ?_
    intro hmem
    have hpos := swallowTime_pos hW ha
    rw [fwdHull] at hmem
    exact absurd hmem.2 (by rw [ENNReal.ofReal_zero]; exact not_le.mpr hpos)
  obtain ⟨u0, hu0⟩ := hsol0
  have hf0 : fwdMap W 0 a = a - (W 0 : ℂ) := by
    rw [fwdMap_eq hW ha hu0 ⟨le_rfl, le_rfl⟩, FwdHolo.sol_zero hu0 le_rfl]
  have h := (opState_eq_tamed hW ha ha (le_refl (0 : ℝ)) fun s hs => by
    rw [show s = 0 from le_antisymm hs.2 hs.1, hf0]; simp).2
  rw [← h, tamedLogCR, intervalIntegral.integral_same, add_zero]

/-- **Part D.** While `sin arg f_s(a) ≥ s₀ ≥ 0` on `[0,t]`, the log conformal radius drops at least
by `4 s₀²` times the clock `S_t = ∫₀ᵗ |f_s(a)|⁻² ds`. -/
theorem fwdLogCR_le_of_sin_ge (hW : Continuous W) {a : ℂ} (ha : 0 < a.im) {t s₀ : ℝ}
    (ht : 0 ≤ t) (hs₀ : 0 ≤ s₀) {u : ℝ → ℂ} (hu : IsForwardSol W a t u)
    (hsin : ∀ s ∈ Icc 0 t, s₀ ≤ (fwdMap W s a).im / ‖fwdMap W s a‖) :
    fwdLogCR W t a ≤ Real.log a.im - 4 * s₀ ^ 2 * fwdClock W t a := by
  have hf := isForwardSol_fwdMap hW ha hu
  set φ : ℝ → ℝ := fun s => fwdLogCR W s a + 4 * s₀ ^ 2 * fwdClock W s a with hφ
  have hder : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt φ
      (-4 * (fwdMap W s a).im ^ 2 / ‖fwdMap W s a‖ ^ 4 +
        4 * s₀ ^ 2 * (1 / ‖fwdMap W s a‖ ^ 2)) (Icc 0 t) s := fun s hs =>
    (hasDerivWithinAt_fwdLogCR hW ha ⟨u, hu⟩ hs).add
      ((hasDerivWithinAt_integral_Icc (sol_contOn_inv_sq hf) hs).const_mul _)
  have hanti := antitoneOn_Icc_of_hasDerivWithinAt hder fun s hs => by
    have hs' : s ∈ Icc (0 : ℝ) t := Ioo_subset_Icc_self hs
    have hne : fwdMap W s a ≠ 0 := (hf.2 s hs').1
    have hn : 0 < ‖fwdMap W s a‖ := norm_pos_iff.2 hne
    have h1 := hsin s hs'
    have h2 : s₀ ^ 2 ≤ ((fwdMap W s a).im / ‖fwdMap W s a‖) ^ 2 :=
      pow_le_pow_left₀ hs₀ h1 2
    rw [div_pow] at h2
    have h3 : s₀ ^ 2 * ‖fwdMap W s a‖ ^ 2 ≤ (fwdMap W s a).im ^ 2 := by
      rwa [le_div_iff₀ (by positivity)] at h2
    have e : -4 * (fwdMap W s a).im ^ 2 / ‖fwdMap W s a‖ ^ 4 +
        4 * s₀ ^ 2 * (1 / ‖fwdMap W s a‖ ^ 2) =
        4 * (s₀ ^ 2 * ‖fwdMap W s a‖ ^ 2 - (fwdMap W s a).im ^ 2) / ‖fwdMap W s a‖ ^ 4 := by
      field_simp
      ring
    rw [e]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have hle := hanti h0 ⟨ht, le_rfl⟩ ht
  simp only [hφ, fwdLogCR_zero hW ha, fwdClock, intervalIntegral.integral_same, mul_zero,
    add_zero] at hle
  simp only [fwdClock] at hle ⊢
  linarith

/-- While `sin arg f_s(a) ≥ s₀ > 0` on `[0,t]`, `|f_s(a)| ≤ Im a / s₀`, so the clock grows at least
linearly: `S_t ≥ s₀² t / (Im a)²`. -/
theorem fwdClock_ge_of_sin_ge (hW : Continuous W) {a : ℂ} (ha : 0 < a.im) {t s₀ : ℝ}
    (ht : 0 ≤ t) (hs₀ : 0 < s₀) {u : ℝ → ℂ} (hu : IsForwardSol W a t u)
    (hsin : ∀ s ∈ Icc 0 t, s₀ ≤ (fwdMap W s a).im / ‖fwdMap W s a‖) :
    s₀ ^ 2 / a.im ^ 2 * t ≤ fwdClock W t a := by
  have hf := isForwardSol_fwdMap hW ha hu
  have hmono := intervalIntegral.integral_mono_on (μ := volume) ht intervalIntegrable_const
    ((sol_contOn_inv_sq hf).intervalIntegrable_of_Icc ht) fun s hs => by
      show s₀ ^ 2 / a.im ^ 2 ≤ 1 / ‖fwdMap W s a‖ ^ 2
      have hne : fwdMap W s a ≠ 0 := (hf.2 s hs).1
      have hn : 0 < ‖fwdMap W s a‖ := norm_pos_iff.2 hne
      have him : (fwdMap W s a).im ≤ a.im := by
        have h := (im_isForwardSol_le hW ha hf).1 ⟨le_rfl, ht⟩ hs hs.1
        have h0 : fwdMap W 0 a = a - (W 0 : ℂ) := FwdHolo.sol_zero hf ht
        simp only [h0, Complex.sub_im, Complex.ofReal_im, sub_zero] at h
        exact h
      have h1 := hsin s hs
      rw [le_div_iff₀ hn] at h1
      have h2 : s₀ * ‖fwdMap W s a‖ ≤ a.im := h1.trans him
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have h3 := pow_le_pow_left₀ (by positivity) h2 2
      rw [mul_pow] at h3
      exact h3
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  simp only [fwdClock]
  linarith

end Deterministic


/-! ### Part G: the Schwarz lemma and the boundary of `H_t` -/

section Geometry

variable {W : ℝ → ℝ}

/-- The Cayley-type map `w ↦ (w − p)/(w − conj p)` has derivative `1/(p − conj p)` at `p`. -/
theorem hasDerivAt_cayley {p : ℂ} (hp : 0 < p.im) :
    HasDerivAt (fun w : ℂ => (w - p) / (w - (starRingEnd ℂ) p)) (1 / (p - (starRingEnd ℂ) p)) p := by
  have hne : p - (starRingEnd ℂ) p ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have h1 : HasDerivAt (fun w : ℂ => w - p) 1 p := (hasDerivAt_id' p).sub_const p
  have h2 : HasDerivAt (fun w : ℂ => w - (starRingEnd ℂ) p) 1 p := (hasDerivAt_id' p).sub_const _
  refine (h1.div h2 hne).congr_deriv ?_
  rw [sub_self, zero_mul, sub_zero, one_mul, pow_two]
  field_simp

/-- For `w, p ∈ ℍ`, `|w − p| < |w − conj p|`. -/
theorem norm_sub_lt_norm_sub_conj {w p : ℂ} (hw : 0 < w.im) (hp : 0 < p.im) :
    ‖w - p‖ < ‖w - (starRingEnd ℂ) p‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  nlinarith

/-- **The Schwarz lemma for the Loewner map** ([RS05], before (6.4): `r_t |g_t'(z)| ≤ 2 Im g_t(z)`).
If the disc `B(a, r)` lies in `ℍ \ K_t`, then `r ≤ 2 Υ_t(a) = 2 exp (fwdLogCR W t a)`. -/
theorem le_two_mul_exp_fwdLogCR (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : ball a r ⊆ H \ fwdHull W t) :
    r ≤ 2 * Real.exp (fwdLogCR W t a) := by
  have ha : a ∈ H \ fwdHull W t := hball (mem_ball_self hr)
  set f := fwdMap W t with hf_def
  set p := f a with hp_def
  have hp : 0 < p.im := (MainMart.im_fwdMap_pos_and_clock hW ht ha).1
  set g : ℂ → ℂ := fun w => (f w - p) / (f w - (starRingEnd ℂ) p) with hg_def
  have hfH : ∀ w ∈ ball a r, 0 < (f w).im := fun w hw =>
    (MainMart.im_fwdMap_pos_and_clock hW ht (hball hw)).1
  have hden : ∀ w ∈ ball a r, f w - (starRingEnd ℂ) p ≠ 0 := fun w hw h => by
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith [hfH w hw]
  have hgd : DifferentiableOn ℂ g (ball a r) := by
    have hfd := (FwdHolo.differentiableOn_fwdMap hW ht).mono hball
    exact (hfd.sub_const p).div (hfd.sub_const _) hden
  have hga : g a = 0 := by simp [hg_def, hp_def]
  have hmaps : MapsTo g (ball a r) (closedBall (g a) 1) := by
    intro w hw
    rw [hga, mem_closedBall, dist_zero_right, hg_def]
    simp only
    rw [norm_div, div_le_one (norm_pos_iff.2 (hden w hw))]
    exact (norm_sub_lt_norm_sub_conj (hfH w hw) hp).le
  have hS := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hmaps hr
  have hfa := FwdHolo.hasDerivAt_fwdMap hW ht ha
  have h1 := (hasDerivAt_cayley hp).comp a hfa
  have hgder : HasDerivAt g (1 / (p - (starRingEnd ℂ) p) * Complex.exp (logDerivFwd W t a)) a :=
    h1
  rw [hgder.deriv, norm_mul, norm_div, norm_one, Complex.norm_exp] at hS
  have hnp : ‖p - (starRingEnd ℂ) p‖ = 2 * p.im := by
    have e : p - (starRingEnd ℂ) p = ((2 * p.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [two_mul]
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg (by positivity)]
  rw [hnp] at hS
  have hexp : Real.exp (fwdLogCR W t a) = p.im / Real.exp (logDerivFwd W t a).re := by
    rw [fwdLogCR, Real.exp_sub, Real.exp_log hp]
  rw [hexp]
  have hE : 0 < Real.exp (logDerivFwd W t a).re := Real.exp_pos _
  rw [mul_div_assoc', le_div_iff₀ hE]
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hr] at hS
  linarith

/-- **A boundary point of `ℍ \ K_t` close to `a` lies on the trace.** If `ℍ \ K_t` is a connected
component of `ℍ \ γ[0,t]` and the disc `B(a, ρ) ⊆ ℍ` is not contained in `ℍ \ K_t`, then
`γ[0,t]` meets `B(a, ρ)`. -/
theorem exists_mem_image_ball_of_not_subset {γ : ℝ → ℂ} {t : ℝ} (hγc : ContinuousOn γ (Icc 0 t))
    (hgen : ∃ z ∈ H \ fwdHull W t, connectedComponentIn (H \ γ '' Icc 0 t) z = H \ fwdHull W t)
    (hW : Continuous W) (ht : 0 ≤ t) {a : ℂ} (ha : a ∈ H \ fwdHull W t) {ρ : ℝ}
    (hρH : ball a ρ ⊆ H) (hnot : ¬ ball a ρ ⊆ H \ fwdHull W t) :
    ∃ s ∈ Icc 0 t, γ s ∈ ball a ρ := by
  obtain ⟨z₀, -, hcomp⟩ := hgen
  set C := H \ fwdHull W t with hC
  set V := H \ γ '' Icc 0 t with hV
  have hCo : IsOpen C := FwdHolo.isOpen_compl_fwdHull hW ht
  have hVo : IsOpen V := isOpen_H.sdiff ((isCompact_Icc.image_of_continuousOn hγc).isClosed)
  have hρ : 0 < ρ := by
    by_contra h
    exact hnot (by rw [ball_eq_empty.2 (not_lt.1 h)]; exact empty_subset _)
  obtain ⟨w, hwB, hwC⟩ := not_subset.1 hnot
  -- a point of the ball in `closure C \ C`
  obtain ⟨b, hbB, hbcl, hbC⟩ : ∃ b ∈ ball a ρ, b ∈ closure C ∧ b ∉ C := by
    by_cases hw : w ∈ closure C
    · exact ⟨w, hwB, hw, hwC⟩
    · by_contra hcon
      push Not at hcon
      have hpre := (convex_ball a ρ).isPreconnected
      obtain ⟨x, -, hxC, hxcl⟩ := hpre C (closure C)ᶜ hCo isClosed_closure.isOpen_compl
        (fun x hx => by
          by_cases hxC : x ∈ C
          · exact Or.inl hxC
          · exact Or.inr fun hcl => hxC (hcon x hx hcl))
        ⟨a, mem_ball_self hρ, ha⟩ ⟨w, hwB, hw⟩
      exact hxcl (subset_closure hxC)
  refine by_contra fun hno => hbC ?_
  push Not at hno
  have hbV : b ∈ V := ⟨hρH hbB, fun ⟨s, hs, hsb⟩ => hno s hs (hsb ▸ hbB)⟩
  have hC' : IsOpen (connectedComponentIn V b) := hVo.connectedComponentIn
  obtain ⟨c, hcC', hcC⟩ := mem_closure_iff.1 hbcl _ hC' (mem_connectedComponentIn hbV)
  have e1 : connectedComponentIn V b = connectedComponentIn V c := connectedComponentIn_eq hcC'
  have e2 : C = connectedComponentIn V c := by
    rw [← hcomp] at hcC ⊢
    exact connectedComponentIn_eq hcC
  rw [e2, ← e1]
  exact mem_connectedComponentIn hbV

/-- **Density from a small conformal radius** ([RS05] (6.4), right inequality). If `ℍ \ K_t` is
a connected component of `ℍ \ γ[0,t]` for every `t ≥ 0`, and the conformal radius `Υ_t(a)` of
`a ∈ ℍ` becomes arbitrarily small while `a ∉ K_t`, then `a` lies in the closure of `γ[0,∞)`. -/
theorem mem_closure_image_of_fwdLogCR {γ : ℝ → ℂ} (hW : Continuous W) (hγc : ContinuousOn γ (Ici 0))
    (hgen : ∀ t : ℝ, 0 ≤ t →
      ∃ z ∈ H \ fwdHull W t, connectedComponentIn (H \ γ '' Icc 0 t) z = H \ fwdHull W t)
    {a : ℂ} (ha : 0 < a.im)
    (hsmall : ∀ η > (0 : ℝ), ∃ t ≥ (0 : ℝ), a ∉ fwdHull W t ∧ fwdLogCR W t a < Real.log η) :
    a ∈ closure (γ '' Ici 0) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set ρ := min ε a.im with hρ
  have hρ0 : 0 < ρ := lt_min hε ha
  obtain ⟨t, ht, haK, hL⟩ := hsmall (ρ / 2) (by positivity)
  have hρH : ball a ρ ⊆ H := fun w hw => by
    rw [mem_ball, Complex.dist_eq] at hw
    have h1 : |(w - a).im| ≤ ‖w - a‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h1
    have : ρ ≤ a.im := min_le_right _ _
    show 0 < w.im
    linarith [neg_abs_le (w.im - a.im)]
  have hnot : ¬ ball a ρ ⊆ H \ fwdHull W t := fun hsub => by
    have h1 := le_two_mul_exp_fwdLogCR hW ht hρ0 hsub
    have h2 : Real.exp (fwdLogCR W t a) < ρ / 2 := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < ρ / 2)]
      exact Real.exp_lt_exp.2 hL
    linarith
  obtain ⟨s, hs, hsB⟩ := exists_mem_image_ball_of_not_subset (hγc.mono Icc_subset_Ici_self)
    (hgen t ht) hW ht ⟨ha, haK⟩ hρH hnot
  refine ⟨γ s, ⟨s, hs.1, rfl⟩, ?_⟩
  rw [mem_ball] at hsB
  rw [dist_comm]
  exact hsB.trans_le (min_le_left _ _)

end Geometry


/-! ### Part P: the one-point martingale for `κ > 8` -/

section Probabilistic

/-- **The sine bound.** If `e^{pL} S^β ≤ λ` with `p = κ/8 − 1 > 0 > β = 8/κ − 1`, `L ≥ log η` and
`S > 0`, then `S ≥ (λ e^{−p log η})^{1/β}`. -/
theorem le_sin_of_phiM_le {κ : ℝ} (hκ : 8 < κ) {L S lam η : ℝ} (hS : 0 < S)
    (hL : Real.log η ≤ L) (h : Real.exp ((κ / 8 - 1) * L) * S ^ (8 / κ - 1) ≤ lam) :
    (lam * Real.exp (-(κ / 8 - 1) * Real.log η)) ^ (8 / κ - 1)⁻¹ ≤ S := by
  have hp : 0 < κ / 8 - 1 := by linarith
  have hβ : 8 / κ - 1 < 0 := by
    rw [sub_neg, div_lt_one (by linarith)]
    exact hκ
  have hSβ : 0 < S ^ (8 / κ - 1) := Real.rpow_pos_of_pos hS _
  have hE : 0 < Real.exp ((κ / 8 - 1) * L) := Real.exp_pos _
  have h1 : S ^ (8 / κ - 1) ≤ lam * Real.exp (-(κ / 8 - 1) * Real.log η) := by
    have h2 : S ^ (8 / κ - 1) ≤ lam * Real.exp (-((κ / 8 - 1) * L)) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hE, mul_comm]
      exact h
    refine h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) ?_)
    exact le_trans (mul_nonneg hE.le hSβ.le) h
  have h3 := Real.rpow_le_rpow_of_nonpos hSβ h1 (inv_nonpos.2 hβ.le)
  rwa [Real.rpow_rpow_inv hS.le hβ.ne] at h3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit mΩ in
/-- A continuous path reaching a closed set before time `T` is in it at the hitting time. -/
theorem hittingBtwn_mem_of_isClosed' {E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}
    {S : Set E} (hS : IsClosed S) {ω : Ω} (hc : Continuous (X · ω)) {T : ℝ≥0}
    (hex : ∃ j ∈ Icc 0 T, X j ω ∈ S) : X (hittingBtwn X S 0 T ω) ω ∈ S := by
  classical
  rw [hittingBtwn_def]
  simp only [hex, ↓reduceIte]
  obtain ⟨j, hj, hjS⟩ := hex
  have hcl : IsClosed (Icc 0 T ∩ {i : ℝ≥0 | X i ω ∈ S}) :=
    isClosed_Icc.inter (hS.preimage hc)
  exact (hcl.csInf_mem ⟨j, hj, hjS⟩ ⟨0, fun _ h => h.1.1⟩).2

/-- The one-point martingale profile read in the state `(Z, L)`. -/
def opPhiM (κ : ℝ) (x : ℂ × ℝ) : ℝ := phiM κ x.2 (Complex.arg x.1)

theorem contDiffOn_opPhiM (κ : ℝ) : ContDiffOn ℝ 3 (opPhiM κ) {x : ℂ × ℝ | 0 < x.1.im} := by
  have hin : ContDiffOn ℝ 3 (fun x : ℂ × ℝ => (x.2, Complex.arg x.1)) {x : ℂ × ℝ | 0 < x.1.im} :=
    fun x hx => (contDiffAt_snd.prodMk ((contDiffAt_arg hx).comp x contDiffAt_fst)).contDiffWithinAt
  exact (contDiffOn_uncurry_phiM κ).comp hin fun x hx =>
    ⟨mem_univ _, arg_mem_Ioo_of_im_pos hx⟩

theorem opPhiM_nonneg (κ : ℝ) {x : ℂ × ℝ} (hx : 0 < x.1.im) : 0 ≤ opPhiM κ x :=
  phiM_nonneg (arg_mem_Ioo_of_im_pos hx)


/-- **Part P (main estimate).** For `κ > 8`, `a ∈ ℍ`, `0 < η < Im a` and `λ > M₀ = φ_M(a)`, the
event "`log Υ_t(a) ≥ log η` at every time `t` at which `a` is not swallowed" has probability at
most `M₀ / λ`. The one-point martingale is stopped when it reaches `λ` or when `Im Z` reaches a
level `δ`; on the event, the sine bound (`le_sin_of_phiM_le`) and part D show that `Im Z` stays
above `2δ` and that `log Υ` would drop below `log η` before the horizon, so the martingale must
reach `λ`; Markov's inequality concludes. -/
theorem mul_measureReal_le_of_eight_lt (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 8 < κ) {a : ℂ}
    (ha : 0 < a.im) {η : ℝ} (hη : 0 < η) (hηa : η < a.im) {lam : ℝ}
    (hlam : opPhiM κ (a, Real.log a.im) < lam) :
    lam * P.real {ω | ∀ t : ℝ, 0 ≤ t → a ∉ fwdHull (drive κ B ω) t →
      Real.log η ≤ fwdLogCR (drive κ B ω) t a} ≤ opPhiM κ (a, Real.log a.im) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hκ0 : 0 < κ := by linarith
  set M₀ := opPhiM κ (a, Real.log a.im) with hM₀
  have hM₀0 : 0 ≤ M₀ := opPhiM_nonneg κ ha
  have hlam0 : 0 < lam := hM₀0.trans_lt hlam
  -- constants
  set A := lam * Real.exp (-(κ / 8 - 1) * Real.log η) with hA
  have hA0 : 0 < A := mul_pos hlam0 (Real.exp_pos _)
  set s₀ := A ^ (8 / κ - 1)⁻¹ with hs₀
  have hs₀0 : 0 < s₀ := Real.rpow_pos_of_pos hA0 _
  set D := Real.log a.im - Real.log η with hD
  have hD0 : 0 < D := sub_pos.2 (Real.log_lt_log hη hηa)
  set ymin := a.im * Real.exp (-(D / (2 * s₀ ^ 2))) with hymin
  have hymin0 : 0 < ymin := mul_pos ha (Real.exp_pos _)
  have hymina : ymin < a.im := by
    have h1 : Real.exp (-(D / (2 * s₀ ^ 2))) < 1 :=
      (Real.exp_lt_exp.2 (neg_neg_of_pos (by positivity))).trans_eq Real.exp_zero
    have := mul_lt_mul_of_pos_left h1 ha
    rwa [mul_one] at this
  set δ := ymin / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set T₀ := D * a.im ^ 2 / (4 * s₀ ^ 4) + 1 with hT₀
  have hT₀0 : 0 < T₀ := by positivity
  set T : ℝ≥0 := ⟨T₀ + 1, by positivity⟩ with hT
  set U := opProc κ B δ a with hU
  set F := opPhiM κ with hF
  set Cl : Set (ℂ × ℝ) := {x | x.1.im ≤ δ} ∪ ({x | δ ≤ x.1.im} ∩ F ⁻¹' Ici lam) with hCl
  set K : Set (ℂ × ℝ) := {x | δ ≤ x.1.im} ∩ F ⁻¹' Iic lam with hK
  have hFd := contDiffOn_opPhiM κ
  have hFc : ContinuousOn F {x : ℂ × ℝ | δ ≤ x.1.im} :=
    hFd.continuousOn.mono fun x hx => hδ0.trans_le hx
  have hDc : IsClosed {x : ℂ × ℝ | δ ≤ x.1.im} :=
    isClosed_le continuous_const (Complex.continuous_im.comp continuous_fst)
  have hClc : IsClosed Cl :=
    (FrozenMart.isClosed_fzCl δ).union (hFc.preimage_isClosed_of_isClosed hDc isClosed_Ici)
  have hKc : IsClosed K := hFc.preimage_isClosed_of_isClosed hDc isClosed_Iic
  have hKO : K ⊆ {x : ℂ × ℝ | 0 < x.1.im} := fun x hx => hδ0.trans_le hx.1
  have hU0 : ∀ ω, U 0 ω = (a, Real.log a.im) := fun ω => by
    rw [hU, opProc_integralEq hBc hδ0 κ a ω 0]
    simp [hB0 ω]
  have hK_of : ∀ x, x ∉ Cl → x ∈ K := fun x hx => by
    simp only [hCl, mem_union, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Ici, not_or,
      not_and, not_le] at hx
    exact ⟨hx.1.le, (hx.2 hx.1.le).le⟩
  have hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl) → U t ω ∈ K := by
    intro ω t _ h
    refine FrozenMart.mem_of_forall_lt_of_isClosed (continuous_opProc hBc hδ0 κ a ω) hKc ?_
      fun s hs => hK_of _ (h s hs)
    rw [show opProc κ B δ a 0 ω = (a, Real.log a.im) from hU0 ω]
    exact ⟨show δ ≤ a.im by linarith, hlam.le⟩
  have hFM : ∀ x ∈ K, |F x| ≤ lam := fun x hx => by
    rw [abs_of_nonneg (opPhiM_nonneg κ (hδ0.trans_le hx.1))]
    exact hx.2
  have hM := FrozenMart.martingale_localDynkin_stopped hB hBc (NonSwallow.bmFilt hBm)
    (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm) (lipschitzWith_opDrift hδ0)
    (norm_opDrift_le hδ0) (opProc_integralEq hBc hδ0 κ a) FrozenMart.isOpen_fzO hClc hKc hKO
    hFd (fun x hx _ => dynkinGen_opDrift_phiM hκ0 hδ0 hx.1) T hUK hFM
  set σ : Ω → ℝ≥0 := hittingBtwn U Cl 0 T with hσ
  have hσT : ∀ ω, σ ω ≤ T := fun ω => hittingBtwn_le ω
  have hmin : ∀ ω, min T (σ ω) = σ ω := fun ω => min_eq_right (hσT ω)
  have hMT := hM.integrable T
  simp only [hmin] at hMT
  have hsi := hM.setIntegral_eq (show (0 : ℝ≥0) ≤ T from zero_le) MeasurableSet.univ
  simp only [Measure.restrict_univ, hmin, min_eq_left (zero_le : (0 : ℝ≥0) ≤ _)] at hsi
  have h0int : ∫ ω, opPhiM κ (opProc κ B δ a 0 ω) ∂P = M₀ := by
    simp_rw [show ∀ ω, opProc κ B δ a 0 ω = (a, Real.log a.im) from hU0]
    rw [integral_const]
    simp [hM₀, hF]
  rw [h0int] at hsi
  have hKσ : ∀ ω, U (σ ω) ω ∈ K := fun ω =>
    hUK ω (σ ω) (hσT ω) fun s hs => notMem_of_lt_hittingBtwn hs zero_le
  have hnn : ∀ ω, 0 ≤ F (U (σ ω) ω) := fun ω => opPhiM_nonneg κ (hδ0.trans_le (hKσ ω).1)
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hnn) hMT lam
  rw [← hsi] at hmk
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_ (measure_ne_top P _)) hlam0.le) hmk
  -- the inclusion
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hlt
  push Not at hlt
  set W := drive κ B ω with hWdef
  have hW : Continuous W := drive_continuous (hBc ω)
  have hK_le : ∀ s : ℝ≥0, s ≤ σ ω → U s ω ∈ K := fun s hs =>
    hUK ω s (hs.trans (hσT ω)) fun r hr => notMem_of_lt_hittingBtwn (hr.trans_le hs) zero_le
  have him : ∀ r ∈ Icc (0 : ℝ) (σ ω), δ ≤ (tamedZ W δ a r).im := fun r hr => by
    have h := (hK_le r.toNNReal (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)).1
    simpa [hU, opProc, Real.coe_toNNReal _ hr.1] using h
  have hsol := isForwardSol_tamedZ hW hδ0 (σ ω).coe_nonneg him
  have hfeq : ∀ r ∈ Icc (0 : ℝ) (σ ω), fwdMap W r a = tamedZ W δ a r := fun r hr =>
    fwdMap_eq hW ha hsol hr
  have hLeq : ∀ r ∈ Icc (0 : ℝ) (σ ω), fwdLogCR W r a = tamedLogCR W δ a r := fun r hr =>
    ((opState_eq_tamed hW hδ0 ha hr.1 fun q hq => by
      rw [hfeq q ⟨hq.1, hq.2.trans hr.2⟩]; exact him q ⟨hq.1, hq.2.trans hr.2⟩).2).symm
  have hL : ∀ r : ℝ, 0 ≤ r → r < σ ω → Real.log η ≤ fwdLogCR W r a := fun r hr0 hrσ =>
    hω r hr0 (LoewnerAlgebra.not_mem_fwdHull_of_sol hr0 hrσ ⟨_, hsol⟩)
  have hsin : ∀ r : ℝ, 0 ≤ r → r < σ ω → s₀ ≤ (fwdMap W r a).im / ‖fwdMap W r a‖ := by
    intro r hr0 hrσ
    have hKr := hK_le r.toNNReal (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; exact hrσ.le)
    have hFr : Real.exp ((κ / 8 - 1) * fwdLogCR W r a) *
        Real.sin (Complex.arg (fwdMap W r a)) ^ (8 / κ - 1) ≤ lam := by
      rw [hfeq r ⟨hr0, hrσ.le⟩, hLeq r ⟨hr0, hrσ.le⟩]
      have h := hKr.2
      simpa [hU, opProc, hF, opPhiM, phiM, Real.coe_toNNReal _ hr0] using h
    have hpos : 0 < (fwdMap W r a).im := by
      rw [hfeq r ⟨hr0, hrσ.le⟩]; exact hδ0.trans_le (him r ⟨hr0, hrσ.le⟩)
    have hS : 0 < Real.sin (Complex.arg (fwdMap W r a)) :=
      Real.sin_pos_of_pos_of_lt_pi (arg_mem_Ioo_of_im_pos hpos).1 (arg_mem_Ioo_of_im_pos hpos).2
    have := le_sin_of_phiM_le hκ hS (hL r hr0 hrσ) hFr
    rwa [Complex.sin_arg] at this
  have hdet : ∀ r : ℝ, 0 ≤ r → r < σ ω →
      fwdLogCR W r a ≤ Real.log a.im - 4 * s₀ ^ 2 * fwdClock W r a ∧
        s₀ ^ 2 / a.im ^ 2 * r ≤ fwdClock W r a := fun r hr0 hrσ =>
    ⟨fwdLogCR_le_of_sin_ge hW ha hr0 hs₀0.le (isForwardSol_restrict hsol hr0 hrσ.le)
        fun q hq => hsin q hq.1 (hq.2.trans_lt hrσ),
      fwdClock_ge_of_sin_ge hW ha hr0 hs₀0 (isForwardSol_restrict hsol hr0 hrσ.le)
        fun q hq => hsin q hq.1 (hq.2.trans_lt hrσ)⟩
  have himr : ∀ r : ℝ, 0 ≤ r → r < σ ω → ymin ≤ (fwdMap W r a).im := by
    intro r hr0 hrσ
    rw [im_fwdMap_eq_clock hW ha ⟨_, isForwardSol_restrict hsol hr0 hrσ.le⟩ ⟨hr0, le_rfl⟩]
    have h1 := (hdet r hr0 hrσ).1
    have h2 := hL r hr0 hrσ
    have hS : 4 * s₀ ^ 2 * fwdClock W r a ≤ D := by linarith
    have hS' : 2 * fwdClock W r a ≤ D / (2 * s₀ ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [hymin]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) ha.le
  rcases (hσT ω).lt_or_eq with hlt' | heq
  · have hex : ∃ j ∈ Icc 0 T, U j ω ∈ Cl := by
      by_contra hex
      have h := hlt'
      rw [hσ, hittingBtwn_def] at h
      simp only [hex, ↓reduceIte, lt_self_iff_false] at h
    have hmemCl := hittingBtwn_mem_of_isClosed' hClc (continuous_opProc hBc hδ0 κ a ω) hex
    have him_le : (U (σ ω) ω).1.im ≤ δ := by
      rcases hmemCl with h | h
      · exact h
      · exact absurd h.2 (not_le.2 hlt)
    have hge : U (σ ω) ω ∈ {x : ℂ × ℝ | ymin ≤ x.1.im} := by
      refine FrozenMart.mem_of_forall_lt_of_isClosed (continuous_opProc hBc hδ0 κ a ω)
        (isClosed_le continuous_const (Complex.continuous_im.comp continuous_fst)) ?_ ?_
      · rw [show opProc κ B δ a 0 ω = (a, Real.log a.im) from hU0 ω]
        exact hymina.le
      · intro s hs
        show ymin ≤ (tamedZ W δ a s).im
        rw [← hfeq s ⟨s.coe_nonneg, hs.le⟩]
        exact himr s s.coe_nonneg hs
    have : ymin ≤ (U (σ ω) ω).1.im := hge
    linarith
  · have hrσ : T₀ < σ ω := by
      rw [heq]
      show T₀ < T₀ + 1
      linarith
    have h1 := hdet T₀ hT₀0.le hrσ
    have h2 := hL T₀ hT₀0.le hrσ
    have hkey : D < 4 * s₀ ^ 2 * (s₀ ^ 2 / a.im ^ 2 * T₀) := by
      have e : 4 * s₀ ^ 2 * (s₀ ^ 2 / a.im ^ 2 * T₀) =
          D + 4 * s₀ ^ 4 / a.im ^ 2 := by
        rw [hT₀]
        field_simp
      rw [e]
      have : 0 < 4 * s₀ ^ 4 / a.im ^ 2 := by positivity
      linarith
    have h3 : 4 * s₀ ^ 2 * (s₀ ^ 2 / a.im ^ 2 * T₀) ≤ 4 * s₀ ^ 2 * fwdClock W T₀ a :=
      mul_le_mul_of_nonneg_left h1.2 (by positivity)
    linarith [h1.1]


/-- The event "`log Υ_t(a) ≥ log η` whenever `a ∉ K_t`" has probability zero (`κ > 8`). -/
theorem measure_forall_le_fwdLogCR_eq_zero (hB : IsPreBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 8 < κ) {a : ℂ} (ha : 0 < a.im) {η : ℝ} (hη : 0 < η) (hηa : η < a.im) :
    P {ω | ∀ t : ℝ, 0 ≤ t → a ∉ fwdHull (drive κ B ω) t →
      Real.log η ≤ fwdLogCR (drive κ B ω) t a} = 0 := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set S := {ω | ∀ t : ℝ, 0 ≤ t → a ∉ fwdHull (drive κ B ω) t →
      Real.log η ≤ fwdLogCR (drive κ B ω) t a} with hS
  set M₀ := opPhiM κ (a, Real.log a.im) with hM₀
  have hM₀0 : 0 ≤ M₀ := opPhiM_nonneg κ ha
  rw [← measureReal_eq_zero_iff (measure_ne_top P S)]
  by_contra hne
  have hp : 0 < P.real S := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  have h := mul_measureReal_le_of_eight_lt hB hBm hBc hB0 hκ ha hη hηa
    (lam := M₀ / P.real S + M₀ + 1) (by have := div_nonneg hM₀0 hp.le; linarith)
  rw [← hS, ← hM₀, add_mul, add_mul, div_mul_cancel₀ _ hp.ne'] at h
  nlinarith

/-- **`inf_t Υ_t(a) = 0` almost surely, `κ > 8`** (for a Brownian motion with continuous paths
started at `0`): the log conformal radius of `a` becomes arbitrarily negative before `a` is
swallowed. -/
theorem ae_exists_fwdLogCR_lt_of_good (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 8 < κ) {a : ℂ}
    (ha : 0 < a.im) :
    ∀ᵐ ω ∂P, ∀ η > (0 : ℝ), ∃ t ≥ (0 : ℝ), a ∉ fwdHull (drive κ B ω) t ∧
      fwdLogCR (drive κ B ω) t a < Real.log η := by
  have hηn : ∀ n : ℕ, 0 < a.im / ((n : ℝ) + 2) ∧ a.im / ((n : ℝ) + 2) < a.im := fun n =>
    ⟨by positivity, div_lt_self ha (by linarith [n.cast_nonneg (α := ℝ)])⟩
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ω ∉ {ω | ∀ t : ℝ, 0 ≤ t → a ∉ fwdHull (drive κ B ω) t →
      Real.log (a.im / ((n : ℝ) + 2)) ≤ fwdLogCR (drive κ B ω) t a} :=
    ae_all_iff.2 fun n => measure_eq_zero_iff_ae_notMem.1
      (measure_forall_le_fwdLogCR_eq_zero hB hBm hBc hB0 hκ ha (hηn n).1 (hηn n).2)
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

/-- **`inf_t Υ_t(a) = 0` almost surely, `κ > 8`**, for any Brownian motion. -/
theorem ae_exists_fwdLogCR_lt_of_eight_lt (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ)
    {a : ℂ} (ha : 0 < a.im) :
    ∀ᵐ ω ∂P, ∀ η > (0 : ℝ), ∃ t ≥ (0 : ℝ), a ∉ fwdHull (drive κ B ω) t ∧
      fwdLogCR (drive κ B ω) t a < Real.log η := by
  obtain ⟨G, hGm, hGc, hG0, hGbr, hGeq⟩ := exists_good_version0 hB
  filter_upwards [ae_exists_fwdLogCR_lt_of_good hGbr.toIsPreBrownianReal hGm hGc hG0 hκ ha,
    hGeq] with ω hω heq
  have hdr : drive κ G ω = drive κ B ω := funext fun s => by simp [drive, heq]
  rwa [hdr] at hω

end Probabilistic

end InteractingSLE
