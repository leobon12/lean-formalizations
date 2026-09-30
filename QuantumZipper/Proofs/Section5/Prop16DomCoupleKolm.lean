import QuantumZipper.Proofs.Section5.Prop16DomCoupleFubini
import QuantumZipper.Proofs.LQG.RegularSample

/-!
# Proposition 1.6, node DOM-COUPLE (part 5): continuous versions for globally Lipschitz curves

`isoW_contVersion_global`: for an isonormal process `W` on `E` and a globally Lipschitz curve
`H : ℂ → E`, the process `z ↦ W(H z)` has a version `Y` with `Y ω` continuous on `ℂ` for
**every** `ω` and measurable coordinates. This is the global half of the continuous-version
sub-node `GaussContVersionStmt` (`Prop16DomCoupleVersion.lean`).

Source: Kolmogorov's continuity criterion (Revuz–Yor, *Continuous martingales and Brownian
motion*, Ch. I, Thm (2.1)), in the repository's dyadic form
`KolmD.exists_continuous_modification_D` (sixteenth moments, `d = 2`); the Gaussian sixteenth
moment is `RegSample.lintegral_pow16_of_map_eq`. The measurable modification (restriction to a
measurable full-measure subset of the convergence event) is an own elementary step.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Filter Topology
open scoped RealInnerProductSpace NNReal ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-- Coordinates `(Fin 2 → ℝ) → ℂ`. -/
def toCdom (q : Fin 2 → ℝ) : ℂ := ⟨q 0, q 1⟩

/-- Coordinates `ℂ → (Fin 2 → ℝ)`. -/
def fromCdom (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

theorem toCdom_fromCdom (z : ℂ) : toCdom (fromCdom z) = z := by
  simp [toCdom, fromCdom]

theorem continuous_fromCdom : Continuous fromCdom := by
  unfold fromCdom
  exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop

theorem norm_toCdom_sub_le (q q' : Fin 2 → ℝ) : ‖toCdom q - toCdom q'‖ ≤ 2 * ‖q - q'‖ := by
  have h0 : |q 0 - q' 0| ≤ ‖q - q'‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (q - q') 0
  have h1 : |q 1 - q' 1| ≤ ‖q - q'‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (q - q') 1
  have h := Complex.norm_le_abs_re_add_abs_im (toCdom q - toCdom q')
  simp only [toCdom, Complex.sub_re, Complex.sub_im] at h
  unfold toCdom
  linarith

theorem norm_sub_le_of_boxD {R : ℕ} {q q' : Fin 2 → ℝ} (hq : q ∈ KolmD.boxD R)
    (hq' : q' ∈ KolmD.boxD R) : ‖q - q'‖ ≤ 2 * R := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have := hq i
  have := hq' i
  calc |q i - q' i| ≤ |q i| + |q' i| := abs_sub _ _
    _ ≤ 2 * R := by linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : E → Ω → ℝ}
  (hW : ∀ {ι : Type} [Fintype ι] (τ : ι → E) (a : ι → ℝ),
    HasLaw (fun ω => ∑ i, a i * W (τ i) ω) (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) P)

omit [IsProbabilityMeasure P] in
include hW in
/-- Increments of an isonormal process: `W x − W y = W (x − y)` a.s. -/
theorem isoW_sub_ae (x y : E) : ∀ᵐ ω ∂P, W x ω - W y ω = W (x - y) ω := by
  have hlaw := hW ![x, y, x - y] ![1, -1, -1]
  have h0 : ∑ i, (![1, -1, -1] : Fin 3 → ℝ) i • (![x, y, x - y] : Fin 3 → E) i = 0 := by
    simp [Fin.sum_univ_three]; abel
  rw [h0] at hlaw
  have h0' : (‖(0 : E)‖ ^ 2).toNNReal = 0 := by simp
  have hae : ∀ᵐ ω ∂P, ∑ i, (![1, -1, -1] : Fin 3 → ℝ) i * W ((![x, y, x - y] : Fin 3 → E) i) ω
      = 0 := by
    refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
    rw [hlaw.map_eq, h0', gaussianReal_zero_var, ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl
  filter_upwards [hae] with ω hω
  simp [Fin.sum_univ_three] at hω
  linarith

include hW in
/-- **Continuous version for a globally Lipschitz curve** (Kolmogorov). -/
theorem isoW_contVersion_global (hWm : ∀ x, Measurable (W x)) {H : ℂ → E} {L : ℝ≥0}
    (hH : LipschitzWith L H) :
    ∃ Y : Ω → ℂ → ℝ, (∀ ω, Continuous (Y ω)) ∧ (∀ z, Measurable fun ω => Y ω z) ∧
      ∀ z, (fun ω => Y ω z) =ᵐ[P] W (H z) := by
  classical
  set Z : (Fin 2 → ℝ) → Ω → ℝ := fun q => W (H (toCdom q)) with hZdef
  have hZm : ∀ q, Measurable (Z q) := fun q => hWm _
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ KolmD.MomentBoundD Z P K R := by
    intro R
    have hc0 : 0 ≤ gaussianAbsMoment 16 := gaussianAbsMoment_nonneg _
    refine ⟨(2 * L) ^ 16 * (2 * R) ^ 8 * gaussianAbsMoment 16, by positivity, ?_⟩
    intro q hq q' hq'
    set x := H (toCdom q) - H (toCdom q') with hx
    have hae := isoW_sub_ae hW (H (toCdom q)) (H (toCdom q'))
    have hlaw := (isoW_law hW x).map_eq
    have hl : ∫⁻ ω, ENNReal.ofReal (|Z q ω - Z q' ω| ^ 16) ∂P =
        ∫⁻ ω, ENNReal.ofReal (|W x ω| ^ 16) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      simp only [hZdef, hω, hx]
    rw [hl, RegSample.lintegral_pow16_of_map_eq (hWm x) hlaw]
    refine ENNReal.ofReal_le_ofReal ?_
    have hv : (((‖x‖ ^ 2).toNNReal : ℝ≥0) : ℝ) = ‖x‖ ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)
    rw [hv]
    have hΔ := norm_sub_le_of_boxD hq hq'
    have hxL : ‖x‖ ≤ 2 * L * ‖q - q'‖ := by
      calc ‖x‖ ≤ L * ‖toCdom q - toCdom q'‖ := by
            rw [hx, ← dist_eq_norm, ← dist_eq_norm]; exact hH.dist_le_mul _ _
        _ ≤ L * (2 * ‖q - q'‖) := by gcongr; exact norm_toCdom_sub_le q q'
        _ = 2 * L * ‖q - q'‖ := by ring
    have hn0 : 0 ≤ ‖q - q'‖ := norm_nonneg _
    have h16 : (‖x‖ ^ 2) ^ 8 ≤ (2 * L) ^ 16 * (2 * R) ^ 8 * ‖q - q'‖ ^ 8 := by
      have e1 : (‖x‖ ^ 2) ^ 8 = ‖x‖ ^ 16 := by ring
      have e2 : ‖x‖ ^ 16 ≤ (2 * L * ‖q - q'‖) ^ 16 :=
        pow_le_pow_left₀ (norm_nonneg _) hxL 16
      have e3 : ‖q - q'‖ ^ 8 ≤ (2 * R) ^ 8 := pow_le_pow_left₀ hn0 hΔ 8
      have e4 : (2 * L * ‖q - q'‖) ^ 16 = (2 * L) ^ 16 * ‖q - q'‖ ^ 8 * ‖q - q'‖ ^ 8 := by ring
      rw [e1]
      refine e2.trans (le_of_eq_of_le e4 ?_)
      have : 0 ≤ (2 * (L : ℝ)) ^ 16 * ‖q - q'‖ ^ 8 := by positivity
      calc (2 * (L : ℝ)) ^ 16 * ‖q - q'‖ ^ 8 * ‖q - q'‖ ^ 8
          ≤ (2 * L) ^ 16 * ‖q - q'‖ ^ 8 * (2 * R) ^ 8 := mul_le_mul_of_nonneg_left e3 this
        _ = (2 * L) ^ 16 * (2 * R) ^ 8 * ‖q - q'‖ ^ 8 := by ring
    calc (‖x‖ ^ 2) ^ 8 * gaussianAbsMoment 16
        ≤ (2 * L) ^ 16 * (2 * R) ^ 8 * ‖q - q'‖ ^ 8 * gaussianAbsMoment 16 :=
          mul_le_mul_of_nonneg_right h16 hc0
      _ = (2 * L) ^ 16 * (2 * R) ^ 8 * gaussianAbsMoment 16 * ‖q - q'‖ ^ 8 := by ring
  obtain ⟨Y', hY'c, hY'ae, hconv⟩ := KolmD.exists_continuous_modification_D (d := 2)
    (by norm_num) (fun q => (hZm q).aemeasurable) hmom
  set B := {ω | ¬ ∀ q, Tendsto (fun n => Z (KolmD.rndD n q) ω) atTop (𝓝 (Y' q ω))} with hB
  have hB0 : P B = 0 := by
    rw [hB]; exact ae_iff.1 hconv
  set T := (toMeasurable P B)ᶜ with hT
  have hTm : MeasurableSet T := (measurableSet_toMeasurable P B).compl
  have hTgood : ∀ ω ∈ T, ∀ q, Tendsto (fun n => Z (KolmD.rndD n q) ω) atTop (𝓝 (Y' q ω)) := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P B h)
  have hTae : ∀ᵐ ω ∂P, ω ∈ T := by
    rw [ae_iff]
    simp only [hT, Set.mem_compl_iff, not_not]
    rw [show {a | a ∈ toMeasurable P B} = toMeasurable P B from rfl, measure_toMeasurable, hB0]
  set Yh : (Fin 2 → ℝ) → Ω → ℝ := fun q ω => T.indicator (fun ω => Y' q ω) ω with hYh
  have hYhm : ∀ q, Measurable (Yh q) := by
    intro q
    refine measurable_of_tendsto_metrizable
      (f := fun n => T.indicator (Z (KolmD.rndD n q))) (fun n => (hZm _).indicator hTm) ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ T
    · simp only [Set.indicator_of_mem hω, hYh]
      exact hTgood ω hω q
    · simp only [Set.indicator_of_notMem hω, hYh]
      exact tendsto_const_nhds
  refine ⟨fun ω z => Yh (fromCdom z) ω, fun ω => ?_, fun z => hYhm _, fun z => ?_⟩
  · by_cases hω : ω ∈ T
    · simp only [hYh, Set.indicator_of_mem hω]
      exact (hY'c ω).comp continuous_fromCdom
    · simp only [hYh, Set.indicator_of_notMem hω]
      exact continuous_const
  · filter_upwards [hTae, hY'ae (fromCdom z)] with ω hω h2
    simp only [hYh, Set.indicator_of_mem hω]
    rw [h2]
    simp only [hZdef, toCdom_fromCdom]

end Prop16Asm

end QuantumZipper
