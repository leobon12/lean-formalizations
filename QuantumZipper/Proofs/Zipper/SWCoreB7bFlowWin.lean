import QuantumZipper.Proofs.Zipper.SWCoreB7bFlowClass

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b-FLOW (4): the live window of the carrier and good solutions of the family

With `V = vrev W T` and a window `[u,v]` live up to time `T - q`:

* `b7bf_exists_sol`: each window point has a real `V`-solution beyond `T - q`;
* `b7bf_continuousOn_time`, `b7bf_strictMonoOn`, `b7bf_continuousOn_space`: the carrier
  `F_σ x = realRevMap V σ x` is continuous in `σ`, strictly increasing and continuous in `x`;
* `b7bf_good`: for `s ∈ [q,T]`, every `y` within the explicit radius
  `R₀ = (c₀/4) e^{-8T/c₀²}` of a moving-window point `F_{T-s} x` has a complex solution of the
  `vrev W s`-equation on `[0, s - q]` with clearance `c₀/2` (`c₀` a clearance of the window).

Own bookkeeping on top of `UnifACFlowDetFam` (restart transfer) and the quantitative ball lemma
`exists_ball_isCRevSol_quant`.
-/

noncomputable section

open Complex Filter MeasureTheory Set Metric
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace SWCore

open RevMapExtension B2

variable {W : ℝ → ℝ}

theorem b7bf_exists_sol {V : ℝ → ℝ} {τ x : ℝ} (hx : ENNReal.ofReal τ < realHitTime V x) :
    ∃ T', τ < T' ∧ 0 ≤ T' ∧ ∃ u₀, IsRealRevSol V x T' u₀ := by
  obtain ⟨T', h1⟩ := lt_iSup_iff.1 hx
  obtain ⟨hT'0, h2⟩ := lt_iSup_iff.1 h1
  obtain ⟨hex, h3⟩ := lt_iSup_iff.1 h2
  exact ⟨T', (ENNReal.ofReal_lt_ofReal_iff'.1 h3).1, hT'0, hex⟩

theorem b7bf_continuousOn_time {V : ℝ → ℝ} (hV : Continuous V) {τ x : ℝ}
    (hx : ENNReal.ofReal τ < realHitTime V x) :
    ContinuousOn (fun σ => realRevMap V σ x) (Icc 0 τ) := by
  obtain ⟨T', hT', -, u₀, hu₀⟩ := b7bf_exists_sol hx
  refine (hu₀.1.mono (Icc_subset_Icc_right hT'.le)).congr fun σ hσ => ?_
  exact RealLine.realRevMap_eq hV hu₀ hσ.1 (by linarith [hσ.2])

theorem b7bf_strictMonoOn {V : ℝ → ℝ} (hV : Continuous V) {τ u v : ℝ}
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal τ < realHitTime V x) {σ : ℝ} (hσ : σ ∈ Icc 0 τ) :
    StrictMonoOn (fun x => realRevMap V σ x) (Icc u v) := by
  refine (RealLine.strictMonoOn_realRevMap hV hσ.1).mono fun x hx => ?_
  obtain ⟨T', hT', -, u₀, hu₀⟩ := b7bf_exists_sol (hLive x hx)
  exact ⟨u₀, RealLine.isRealRevSol_restrict hu₀ (by linarith [hσ.2])⟩

theorem b7bf_continuousOn_space {V : ℝ → ℝ} (hV : Continuous V) {τ u v : ℝ} (hτ : 0 ≤ τ)
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal τ < realHitTime V x) {σ : ℝ} (hσ : σ ∈ Icc 0 τ) :
    ContinuousOn (fun x => realRevMap V σ x) (Icc u v) := by
  obtain ⟨U, hUo, hJU, -, hdiff, -, hval⟩ :=
    RegUnif.exists_unif_revMapExt_extension hV hτ isCompact_Icc hLive
  have hc : ContinuousOn (fun x : ℝ => (revMapExt V σ (x : ℂ)).re) (Icc u v) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    exact (hdiff σ hσ).continuousOn.comp Complex.continuous_ofReal.continuousOn
      fun x hx => hJU x hx
  refine hc.congr fun x hx => ?_
  simp only [(hval σ hσ x hx).1, Complex.ofReal_re]

/-- Intermediate values of the carrier on the window. -/
theorem b7bf_ivt {V : ℝ → ℝ} (hV : Continuous V) {τ u v : ℝ} (hτ : 0 ≤ τ) (huv : u ≤ v)
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal τ < realHitTime V x) {σ : ℝ} (hσ : σ ∈ Icc 0 τ)
    {t : ℝ} (ht : t ∈ Icc (realRevMap V σ u) (realRevMap V σ v)) :
    ∃ x ∈ Icc u v, realRevMap V σ x = t :=
  intermediate_value_Icc huv (b7bf_continuousOn_space hV hτ hLive hσ) ht

/-- **Good solutions of the family near the moving window.** -/
theorem b7bf_good (hW : Continuous W) {T q u v : ℝ} (hq0 : 0 < q)
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) {c₀ : ℝ}
    (hc₀ : 0 < c₀)
    (hcl : ∀ x ∈ Icc u v, ∀ σ ∈ Icc (0 : ℝ) (T - q), c₀ ≤ |realRevMap (vrev W T) σ x|)
    {s : ℝ} (hs : s ∈ Icc q T) {x : ℝ} (hx : x ∈ Icc u v) :
    ∀ y ∈ ball ((realRevMap (vrev W T) (T - s) x : ℝ) : ℂ)
        ((c₀ / 4) / Real.exp ((2 / (c₀ / 2) ^ 2) * T)),
      ∃ w, IsCRevSol (vrev W s) y (s - q) w ∧ ∀ r ∈ Icc (0 : ℝ) (s - q), c₀ / 2 ≤ ‖w r‖ := by
  intro y hy
  obtain ⟨ε, hε, -, w, hw, hweq⟩ :=
    RegUnif.exists_isRealRevSol_shift_vrev hW hq0 hs.1 hs.2 (hLive x hx)
  have hw' := RealLine.isRealRevSol_restrict hw (show s - q ≤ s - q + ε by linarith)
  have hcw : ∀ r ∈ Icc (0 : ℝ) (s - q), c₀ ≤ |w r| := by
    intro r hr
    rw [hweq r hr]
    exact hcl x hx _ ⟨by linarith [hr.1, hs.2], by linarith [hr.2]⟩
  refine exists_ball_isCRevSol_quant (continuous_vrev hW s) (by linarith [hs.1]) hw' hc₀ hcw y
    (ball_subset_ball ?_ hy)
  apply div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _)
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by positivity))

end SWCore
end QuantumZipper
