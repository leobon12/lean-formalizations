import QuantumZipper.Proofs.Thm18.G1RCEval

/-!
# G1-RC, part 3: the GFF part of RC2 at a random scale (pushed folded circles `(s ψ)_* fc(d, r)`)

Specialization of `G1RC.exists_smoothing_limit` (G1RCEval.lean) to the four-parameter family of
pushed folded circles `(s ψ)_* fc(d, r)`, `d ∈ ℂ`, `r, s > 0`, parametrized by
`q = (Re d, Im d, log r, log s) ∈ ℝ⁴` (`G1RC.qOf`) and the circle angle `θ ∈ [0, 2π)`
(`G1RC.pushPhi`). Here `ψ` is a map continuous on `Hbar` with `ψ(Hbar) ⊆ Hbar` (for the G1 core:
the continuous extension to `Hbar` of an inverse normalized uniformizer of a side domain).

`G1RC.exists_pushed_limit`: if the smoothed family has the Kolmogorov bounds
(`G1RC.PushFamBounds ψ β`, the analytic input: support, logarithmic potential and variance
modulus, uniformly on compact parameter sets), then there is a process `V(d, r, s)`, continuous
on `ℂ × (0,∞) × (0,∞)` for every `ω`, a modification of `X((s ψ)_* fc(d, r))`, such that almost
surely, for **all** `d`, `r > 0`, `s > 0` at once,
`∫ G(u, t) d((s ψ)_* fc(d, r))(u) → V(d, r, s)` as `t → 0⁺`.
This is the step that makes the random canonical scale `s = scaleParam γ w₀` harmless (D32).

Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (arXiv:0808.1560, p. 18) and
Revuz–Yor, Ch. I, Thm (2.1), through G1RC{Kolm,Eval}; the parametrization is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open WedgeTK CircleFubini

/-- Normalized Lebesgue measure on `[0, 2π)`. -/
def circM : Measure ℝ := (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ico 0 (2 * π))

instance : IsProbabilityMeasure circM := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  constructor
  show (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ico 0 (2 * π)) univ = 1
  rw [smul_eq_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ico,
    sub_zero]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr h2π).ne' ENNReal.ofReal_ne_top

theorem circM_compl : circM (Icc 0 (2 * π))ᶜ = 0 := by
  show (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ico 0 (2 * π)) (Icc 0 (2 * π))ᶜ = 0
  rw [smul_eq_mul, Measure.restrict_apply measurableSet_Icc.compl]
  have : (Icc 0 (2 * π))ᶜ ∩ Ico 0 (2 * π) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro θ ⟨h1, h2⟩
    exact h1 (Ico_subset_Icc_self h2)
  rw [this, measure_empty, mul_zero]

theorem circleUnif_eq_map (z : ℂ) (ε : ℝ) : circleUnif z ε = circM.map (circleMap z ε) := by
  unfold circleUnif circM
  rw [Measure.map_smul]
  exact (continuous_circleMap z ε).measurable.aemeasurable

/-- Centre of the parameter `q`. -/
def cenQ (q : Fin 4 → ℝ) : ℂ := (q 0 : ℂ) + (q 1 : ℂ) * Complex.I

/-- The parametrized pushed circle: `θ ↦ e^{q₃} ψ(fold(cenQ q + e^{q₂} e^{iθ}))`. -/
def pushPhi (ψ : ℂ → ℂ) (q : Fin 4 → ℝ) (θ : ℝ) : ℂ :=
  (Real.exp (q 3) : ℂ) * ψ (foldH (circleMap (cenQ q) (Real.exp (q 2)) θ))

/-- The parameter of `(d, r, s)`. -/
def qOf (d : ℂ) (r s : ℝ) : Fin 4 → ℝ := ![d.re, d.im, Real.log r, Real.log s]

theorem pushPhi_qOf (ψ : ℂ → ℂ) (d : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    pushPhi ψ (qOf d r s) = fun θ => (s : ℂ) * ψ (foldH (circleMap d r θ)) := by
  funext θ
  simp [pushPhi, qOf, cenQ, Real.exp_log hr, Real.exp_log hs, Complex.re_add_im]

theorem map_foldedCircle_eq (ψ : ℂ → ℂ) (hψm : Measurable ψ) (d : ℂ) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) :
    (foldedCircle d r).map (fun z => (s : ℂ) * ψ z) = circM.map (pushPhi ψ (qOf d r s)) := by
  rw [pushPhi_qOf ψ d hr hs]
  unfold foldedCircle
  rw [circleUnif_eq_map, Measure.map_map continuous_foldH'.measurable
      (continuous_circleMap d r).measurable,
    Measure.map_map (show Measurable fun z => (s : ℂ) * ψ z from measurable_const.mul hψm) (continuous_foldH'.measurable.comp
      (continuous_circleMap d r).measurable)]
  rfl

theorem continuous_pushPhi {ψ : ℂ → ℂ} (hψc : ContinuousOn ψ Hbar) :
    Continuous (uncurry (pushPhi ψ)) := by
  have hc : Continuous fun x : (Fin 4 → ℝ) × ℝ =>
      foldH (circleMap (cenQ x.1) (Real.exp (x.1 2)) x.2) := by
    refine continuous_foldH'.comp ?_
    unfold circleMap cenQ
    fun_prop
  have h2 := hψc.comp_continuous hc fun x => foldH_mem_Hbar' _
  show Continuous fun x : (Fin 4 → ℝ) × ℝ =>
    (Real.exp (x.1 3) : ℂ) * ψ (foldH (circleMap (cenQ x.1) (Real.exp (x.1 2)) x.2))
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    ((continuous_apply 3).comp continuous_fst))).mul h2

theorem pushPhi_mem_Hbar {ψ : ℂ → ℂ} (hψH : MapsTo ψ Hbar Hbar) (q : Fin 4 → ℝ) (θ : ℝ) :
    pushPhi ψ q θ ∈ Hbar := by
  have h := hψH (foldH_mem_Hbar' (circleMap (cenQ q) (Real.exp (q 2)) θ))
  show 0 ≤ ((Real.exp (q 3) : ℂ) * ψ (foldH (circleMap (cenQ q) (Real.exp (q 2)) θ))).im
  rw [Complex.im_ofReal_mul]
  exact mul_nonneg (Real.exp_pos _).le h

/-- **Analytic input** for RC2 at a random scale: the Kolmogorov bounds of the smoothed
five-parameter family `(d, r, s, t) ↦ (s ψ)_* fc(d, r) * fc(·, t)`. -/
def PushFamBounds (ψ : ℂ → ℂ) (β : ℝ) : Prop := FamilyBounds (smoothFam circM (pushPhi ψ)) β

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

/-- **GFF part of RC2 at a random scale.** -/
theorem exists_pushed_limit {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψc : ContinuousOn ψ Hbar)
    (hψH : MapsTo ψ Hbar Hbar) {β : ℝ} (hβ : 0 < β) (hB : PushFamBounds ψ β)
    (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G) :
    ∃ V : ℂ × ℝ × ℝ → Ω → ℝ,
      (∀ ω, ContinuousOn (fun p => V p ω) (univ ×ˢ Ioi 0 ×ˢ Ioi 0)) ∧
      (∀ (d : ℂ) (r s : ℝ), 0 < r → 0 < s → (fun ω => V (d, r, s) ω) =ᵐ[P]
        fun ω => X ω ((foldedCircle d r).map fun z => (s : ℂ) * ψ z)) ∧
      ∀ᵐ ω ∂P, ∀ (d : ℂ) (r s : ℝ), 0 < r → 0 < s →
        Tendsto (fun t => ∫ u, G ω (u, t) ∂((foldedCircle d r).map fun z => (s : ℂ) * ψ z))
          (𝓝[>] 0) (𝓝 (V (d, r, s) ω)) := by
  obtain ⟨Y₀, hYc, hYV, hlim⟩ := exists_smoothing_limit (continuous_pushPhi hψc)
    (pushPhi_mem_Hbar hψH) isCompact_Icc circM_compl hβ hB hX hG
  refine ⟨fun p ω => Y₀ (qOf p.1 p.2.1 p.2.2) ω, fun ω => ?_, fun d r s hr hs => ?_, ?_⟩
  · refine (hYc ω).comp_continuousOn ?_
    have hl : ContinuousOn (fun p : ℂ × ℝ × ℝ => Real.log p.2.1) (univ ×ˢ Ioi 0 ×ˢ Ioi 0) :=
      (Real.continuousOn_log.comp continuous_fst.continuousOn fun x hx => ?_).comp
        continuous_snd.continuousOn fun p hp => hp.2
    · have hl' : ContinuousOn (fun p : ℂ × ℝ × ℝ => Real.log p.2.2)
          (univ ×ˢ Ioi 0 ×ˢ Ioi 0) :=
        (Real.continuousOn_log.comp continuous_snd.continuousOn fun x hx => ?_).comp
          continuous_snd.continuousOn fun p hp => hp.2
      · refine continuousOn_pi.2 fun i => ?_
        fin_cases i
        · exact (Complex.continuous_re.comp continuous_fst).continuousOn
        · exact (Complex.continuous_im.comp continuous_fst).continuousOn
        · exact hl
        · exact hl'
      · exact (ne_of_gt (show (0 : ℝ) < x.2 from hx.2))
    · exact (ne_of_gt (show (0 : ℝ) < x.1 from hx.1))
  · filter_upwards [hYV (qOf d r s)] with ω h
    rw [h, map_foldedCircle_eq ψ hψm d hr hs]
  · filter_upwards [hlim] with ω h d r s hr hs
    rw [map_foldedCircle_eq ψ hψm d hr hs]
    exact h _

end G1RC
end Thm18Asm
end QuantumZipper
