import QuantumZipper.Proofs.Thm11.AddendumAreaMart
import QuantumZipper.Proofs.Thm11.AddendumLeftLimit2Sub

/-!
# THM11 AD-2, probabilistic part (continued): an almost sure lower bound for the conformal radius

For κ ∈ (4,8), a fixed `a ∈ ℍ` and a horizon `T`, almost surely there is `M(ω)` with
`fwdLogCR W t a ≥ log Im a − M` for all `t ≤ T` before the swallowing time of `a`
(`ae_logCR_lower_bound`). Proof: `E[log Im a − L_{σ_n}] ≤ 2C` at the freezing times `σ_n` of the
levels `δ_n = Im a / 2^{n+1}` (`integral_logCR_drop_le`), Fatou's lemma, and the fact that
`t ≤ σ_n` for all large `n` when `a` is alive at `t` (FD-2 through `im_fwdMap_frozenTime_le`),
while `L` is nonincreasing in time (FD-1 (c), `hasDerivWithinAt_fwdLogCR`).

Source: blueprint `THM11_BLUEPRINT.md` §9 AD-2 (own argument around FD-8; cf. Rohde–Schramm,
*Basic properties of SLE*, Lemma 6.3 and Thm 6.4, pp. 25–31).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm11Area

open FrozenMart Thm11Lyap Thm11Add RS FwdClock FwdHolo

/-- FD-1 (c): the log conformral radius is nonincreasing while the point is alive. -/
theorem antitoneOn_fwdLogCR {W : ℝ → ℝ} (hW : Continuous W) {a : ℂ} (ha : 0 < a.im) {t : ℝ}
    (hsol : ∃ u, IsForwardSol W a t u) : AntitoneOn (fun s => fwdLogCR W s a) (Icc 0 t) := by
  have hd := fun s (hs : s ∈ Icc (0 : ℝ) t) => hasDerivWithinAt_fwdLogCR hW ha hsol hs
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
    (fun s hs => (hd s hs).continuousWithinAt) (fun s hs => (hd s (interior_subset hs)).mono
      interior_subset) (fun s _ => ?_)
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (fwdMap W s a).im])
    (by positivity)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- At the freezing time the tamed `L`-coordinate is the true log conformal radius. -/
theorem opProc_frozenTime_snd (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) (T : ℝ≥0) (ω : Ω) :
    (opProc κ B c a (frozenTime κ c δ T B a ω) ω).2
      = fwdLogCR (drive κ B ω) (frozenTime κ c δ T B a ω) a := by
  have hW := continuous_drive_path (κ := κ) hBc ω
  have ha : 0 < a.im := (hc.trans_le hcδ).trans_le hδa
  have hal := (alive_of_le_frozenTime (κ := κ) hBc hc hcδ hδa (T := T) ω le_rfl).2
  exact (opState_eq_tamed hW hc ha (NNReal.coe_nonneg _)
    fun s hs => hcδ.trans (hal s hs).2.2).2

/-- **AD-2, probabilistic input.** For κ ∈ (4,8), `a ∈ ℍ` and `T ≥ 0`, almost surely the log
conformal radius of `H \ K_t` at `a` is bounded below on the alive times `t ≤ T`. -/
theorem ae_logCR_lower_bound (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {a : ℂ}
    (ha : 0 < a.im) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ T → a ∉ fwdHull (drive κ B ω) t →
      Real.log a.im - M ≤ fwdLogCR (drive κ B ω) t a := by
  obtain ⟨C, hC⟩ := exists_abs_gFun_le hκ4 hκ8
  set D : ℕ → Ω → ℝ := fun n ω => Real.log a.im -
    (opProc κ B (lev a n) a (frozenTime κ (lev a n) (lev a n) T B a ω) ω).2 with hDdef
  have hD : ∀ n, Integrable (D n) P ∧ ∫ ω, D n ω ∂P ≤ 2 * C := fun n =>
    integral_logCR_drop_le hB hBc (NonSwallow.bmFilt hBm) (NonSwallow.bmFilt_adapted hBm)
      (NonSwallow.bmFilt_le_past hBm) hκ4 hκ8 (lev_pos ha n) le_rfl (lev_le ha n) T hC
  have hDnn : ∀ n ω, 0 ≤ D n ω := fun n ω =>
    sub_nonneg.2 (tamedLogCR_le (lev_pos ha n) a (NNReal.coe_nonneg _))
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (D n ω) with hfdef
  have hlin : ∀ n, ∫⁻ ω, f n ω ∂P ≤ ENNReal.ofReal (2 * C) := fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hD n).1 (Eventually.of_forall (hDnn n))]
    exact ENNReal.ofReal_le_ofReal (hD n).2
  have hfm : ∀ n, AEMeasurable (f n) P := fun n => (hD n).1.aemeasurable.ennreal_ofReal
  set g : ℕ → Ω → ℝ≥0∞ := fun n => (hfm n).mk (f n) with hgdef
  have hgm : ∀ n, Measurable (g n) := fun n => (hfm n).measurable_mk
  have hfg : ∀ᵐ ω ∂P, ∀ n, f n ω = g n ω := ae_all_iff.2 fun n => (hfm n).ae_eq_mk
  have hlim : ∫⁻ ω, liminf (fun n => g n ω) atTop ∂P ≤ ENNReal.ofReal (2 * C) := by
    refine (lintegral_liminf_le' fun n => (hgm n).aemeasurable).trans ?_
    refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
    rw [← lintegral_congr_ae (hfm n).ae_eq_mk]
    exact hlin n
  have hfin : ∀ᵐ ω ∂P, liminf (fun n => g n ω) atTop < ⊤ :=
    ae_lt_top (Measurable.liminf hgm) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim)
  filter_upwards [hfin, hfg] with ω hω hfgω
  have hfω : liminf (fun n => f n ω) atTop < ⊤ := by
    simpa only [hfgω] using hω
  refine ⟨(liminf (fun n => f n ω) atTop).toReal, fun t ht0 htT hK => ?_⟩
  set W := drive κ B ω with hWdef
  have hW : Continuous W := continuous_drive_path hBc ω
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull ht0 (show a ∈ H from ha) hK
  have hsol := isForwardSol_fwdMap hW ha hu
  -- the minimum of `Im f_s(a)` on `[0,t]`
  obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_isMinOn
    (nonempty_Icc.2 ht0) (Complex.continuous_im.comp_continuousOn hsol.1)
  have hm : 0 < (fwdMap W s₀ a).im := sol_im_pos hW ha hsol hs₀
  obtain ⟨N, hN⟩ := exists_lev_lt ha hm
  have hev : ∀ᶠ n in atTop, ENNReal.ofReal (Real.log a.im - fwdLogCR W t a) ≤ f n ω := by
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    set σ := frozenTime κ (lev a n) (lev a n) T B a ω with hσdef
    have htσ : t ≤ σ := by
      by_contra hcon
      push Not at hcon
      have hσT : σ < T := by
        have : (σ : ℝ) < T := hcon.trans_le htT
        exact_mod_cast this
      have h1 := im_fwdMap_frozenTime_le hBc (lev_pos ha n) le_rfl (lev_le ha n) ω hσT
      have h2 : (fwdMap W s₀ a).im ≤ (fwdMap W σ a).im :=
        hmin ⟨NNReal.coe_nonneg _, hcon.le⟩
      have h3 := lev_anti ha hn
      rw [← hWdef] at h1
      linarith
    have hsolσ := (alive_of_le_frozenTime (κ := κ) hBc (lev_pos ha n) le_rfl (lev_le ha n) (T := T) ω
      le_rfl).1
    have hanti := antitoneOn_fwdLogCR hW ha hsolσ ⟨ht0, htσ⟩
      ⟨NNReal.coe_nonneg _, le_rfl⟩ htσ
    have hDn : D n ω = Real.log a.im - fwdLogCR W σ a := by
      simp only [hDdef]
      rw [opProc_frozenTime_snd hBc (lev_pos ha n) le_rfl (lev_le ha n) T ω]
    exact ENNReal.ofReal_le_ofReal (by rw [hDn]; simp only at hanti; linarith)
  have hle : ENNReal.ofReal (Real.log a.im - fwdLogCR W t a) ≤ liminf (fun n => f n ω) atTop :=
    le_liminf_of_le (by isBoundedDefault) hev
  have := (ENNReal.ofReal_le_iff_le_toReal hfω.ne).1 hle
  linarith

end Thm11Area
end QuantumZipper
