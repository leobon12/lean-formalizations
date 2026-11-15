/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.LiteralCounterflowDef
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.GFF.Pushforward
import InteractingSLE.Spec.Sec4.Heights
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The centred and the literal counterflow line: the exact frame bridge (FD11.1)

Packet PROVE-AF-CFLIT. For a fixed field representative `h` (no equality in law is used anywhere), the frozen centred
counterflow `IsCenteredCounterflowDriver κ P h W ζ` and the paper's literal counterflow
`IsLiteralCounterflowDriver κ P ĥ W ζ` of the shifted field `ĥ = h + πχ` (frozen `IsTranslateAddConst 0 (πχ) h ĥ`)
have literally the same parameter field, hence the same boundary data `b'`, the same induced force word on each side,
the same driver `W` and the same lifetime `ζ`.

* Chart calculus for the frozen `IsChartTransport`: the sign rule FD11.2 (`isChartTransport_neg_iff`), a constant
  field moves into the offset (`isChartTransport_shift_iff`, any conformal chart), a change of branch moves the offset
  by `2πnk` (`isChartTransport_infinitySourceChartAt_iff`);
* the explicit parameter fields: the literal one `−h ∘ R + 2π(1 − n)χ − 2χ arg w` (`literalAt_paramField_apply`) and
  the centred one `−h ∘ R + πχ − 2χ arg w` (`centred_paramField_apply`, FD12.5);
* **the bridge**: `centred_iff_literalAt`, `centred_iff_literal` (fields), `centredWitness_iff_literalWitness` (the
  same `b'`, hence the same force word), **`isCenteredCounterflowDriver_iff_literal`** (FD11.1, branch FD12.1) and
  `isCenteredCounterflowDriver_iff_literalAt` (branch `n`, shift `(1 − 2n)πχ`);
* the half-turn is a genuine frame convention: for `0 < κ < 4`, every branch `n` and every field `h`, the literal
  parameter field of `h` differs from the centred one by the nonzero constant `(1 − 2n)πχ`
  (`literalAt_paramField_ne_centred`); the paper's Remark normalization selects `n = 1` (`remarkBranch_iff`);
* the shifted field: existence, uniqueness and measurability (`shiftDist`), and its boundary data
  (`isPiecewiseConstantBoundaryData_add_const_iff`, `isGFFWithBoundaryData_shift_iff`): `h` has data `b` iff `h + s`
  has data `b + s`, with the same finite set `jumps`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.AuditFix.CFLit

/-! ### Test functions -/

/-- A test function on `ℍ` is integrable. -/
theorem integrable_testOn (φ : TestOn upperHalfPlaneOpens) : Integrable (fun z => φ z) :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-- A function continuous on `ℍ`, times a test function on `ℍ`, is integrable. -/
theorem integrable_mul_testOn {f : ℂ → ℝ} (hf : ContinuousOn f H) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun z => f z * φ z) := by
  have hS : tsupport φ ⊆ H := φ.tsupport_subset
  have hI : IntegrableOn (fun z => f z * φ z) (tsupport φ) :=
    ((hf.mono hS).mul φ.continuous.continuousOn).integrableOn_compact φ.hasCompactSupport.isCompact
  refine (integrableOn_iff_integrable_of_support_subset fun z hz => ?_).1 hI
  by_contra hns
  exact hz (by simp only [image_eq_zero_of_notMem_tsupport hns, mul_zero])

/-- A test function on `ℍ` vanishes off `ℍ`. -/
theorem testOn_eq_zero_of_notMem {φ : TestOn upperHalfPlaneOpens} {z : ℂ} (hz : z ∉ H) : φ z = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hz (φ.tsupport_subset h)

/-- **Change of variables for a transport pair**: if `φ = (φ' ∘ fwd) |fwd′|²` on the chart domain and `φ` is supported
there (the test pairs of the frozen `IsChartTransport`), then `∫ φ = ∫ φ'`. -/
theorem integral_eq_of_transportPair {c : Chart} (hc : c.IsConformal) {φ φ' : TestOn upperHalfPlaneOpens}
    (hsupp : tsupport φ ⊆ c.2.1 '' H) (hφ : ∀ z ∈ c.2.1 '' H, φ z = φ' (c.1 z) * ‖deriv c.1 z‖ ^ 2) :
    ∫ z, φ z = ∫ w, φ' w := by
  rw [Chart.eq_pushTest hc hsupp hφ]
  have h := Chart.integral_mul_pushTest hc φ' fun _ => (1 : ℝ)
  simp only [one_mul] at h
  exact h

/-- A test function on `ℍ` with nonzero integral (a smooth cutoff equal to `1` on the closed disc of radius `1/2`
about `i`). -/
theorem exists_testOn_integral_ne_zero : ∃ φ : TestOn upperHalfPlaneOpens, ∫ w, φ w ≠ 0 := by
  have hK : IsCompact (Metric.closedBall Complex.I (1 / 2)) := isCompact_closedBall _ _
  have hKH : Metric.closedBall Complex.I (1 / 2) ⊆ (upperHalfPlaneOpens : Set ℂ) := fun z hz => by
    have h1 : |z.im - 1| ≤ 1 / 2 := by
      have := Complex.abs_im_le_norm (z - Complex.I)
      rw [Complex.sub_im, Complex.I_im] at this
      exact this.trans (mem_closedBall_iff_norm.1 hz)
    show (0 : ℝ) < z.im
    linarith [(abs_le.1 h1).1]
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_cthickening_subset_open upperHalfPlaneOpens.isOpen hKH
  obtain ⟨ψ, hψ, hrange, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (Metric.isOpen_thickening (δ := δ) (E := Metric.closedBall Complex.I (1 / 2)))
    hK.isClosed (Metric.self_subset_thickening hδ _)
  have hts : tsupport ψ ⊆ Metric.cthickening δ (Metric.closedBall Complex.I (1 / 2)) := by
    rw [tsupport, hsupp]
    exact Metric.closure_thickening_subset_cthickening δ _
  let φ : TestOn upperHalfPlaneOpens :=
    ⟨ψ, hψ, (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hδD⟩
  have hφ01 : ∀ x, 0 ≤ φ x := fun x => (hrange (mem_range_self x)).1
  have hφ1 : ∀ x ∈ Metric.closedBall Complex.I (1 / 2), φ x = 1 := fun x hx => (h1 x).1 hx
  refine ⟨φ, (ne_of_lt ?_).symm⟩
  rw [integral_pos_iff_support_of_nonneg (fun x => hφ01 x) (integrable_testOn φ)]
  refine lt_of_lt_of_le (Metric.measure_closedBall_pos volume Complex.I (by norm_num : (0 : ℝ) < 1 / 2))
    (measure_mono fun z hz => ?_)
  rw [Function.mem_support, hφ1 z hz]
  exact one_ne_zero

/-! ### The shifted field `h + s` (frozen `IsTranslateAddConst 0 s`) -/

/-- `ĥ = h + s` in pairing form: `⟨ĥ, φ⟩ = ⟨h, φ⟩ + s ∫ φ`. -/
theorem translateAddConst_zero_apply {s : ℝ} {h ĥ : DistOn upperHalfPlaneOpens}
    (hĥ : IsTranslateAddConst 0 s h ĥ) (φ : TestOn upperHalfPlaneOpens) : ĥ φ = h φ + s * ∫ z, φ z :=
  hĥ φ φ fun z => by rw [Complex.ofReal_zero, add_zero]

/-- The shifted field `h + s`: the distribution `φ ↦ ⟨h, φ⟩ + s ∫ φ`. -/
def shiftDist (s : ℝ) (h : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  h + s • Chart.oneDist

theorem shiftDist_apply (s : ℝ) (h : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    shiftDist s h φ = h φ + s * ∫ z, φ z := by
  rw [shiftDist, add_apply, smul_apply, Chart.oneDist_apply, smul_eq_mul]

/-- `shiftDist s h` is the frozen `h + s`. -/
theorem isTranslateAddConst_shiftDist (s : ℝ) (h : DistOn upperHalfPlaneOpens) :
    IsTranslateAddConst 0 s h (shiftDist s h) := by
  intro φ φ' hφ
  have e : φ' = φ := by
    ext z
    rw [hφ z, Complex.ofReal_zero, add_zero]
  subst e
  exact shiftDist_apply s h φ'

/-- The shifted field is unique. -/
theorem eq_shiftDist_of_isTranslateAddConst {s : ℝ} {h ĥ : DistOn upperHalfPlaneOpens}
    (hĥ : IsTranslateAddConst 0 s h ĥ) : ĥ = shiftDist s h := by
  ext φ
  rw [translateAddConst_zero_apply hĥ, shiftDist_apply]

theorem measurable_shiftDist (s : ℝ) : Measurable (shiftDist s) :=
  LQGMetric.measurable_distOn_iff.2 fun φ => by
    simp only [shiftDist_apply]
    exact (LQGMetric.measurable_distOn_apply φ).add_const _

/-- Shifting back: if `ĥ = h + s` then `h = ĥ − s`. -/
theorem isTranslateAddConst_symm {s : ℝ} {h ĥ : DistOn upperHalfPlaneOpens}
    (hĥ : IsTranslateAddConst 0 s h ĥ) : IsTranslateAddConst 0 (-s) ĥ h := by
  intro φ φ' hφ
  have e : φ' = φ := by
    ext z
    rw [hφ z, Complex.ofReal_zero, add_zero]
  subst e
  rw [translateAddConst_zero_apply hĥ]
  ring

/-! ### Chart calculus for the frozen `IsChartTransport` -/

/-- **The sign rule FD11.2**: `σ h + a` transported with coefficient `k` is `g` iff `−(σ h + a)` transported with
coefficient `−k` is `−g`. -/
theorem isChartTransport_neg_iff {c : Chart} {σ a k : ℝ} {h g : DistOn upperHalfPlaneOpens} :
    IsChartTransport c σ a k h g ↔ IsChartTransport c (-σ) (-a) (-k) h (-g) := by
  constructor
  · intro ht φ φ' hs hφ
    rw [neg_apply, ht φ φ' hs hφ]
    ring
  · intro ht φ φ' hs hφ
    have e := ht φ φ' hs hφ
    rw [neg_apply] at e
    linear_combination -e

/-- **A constant field moves into the offset**: for a conformal chart and `ĥ = h + s`, transporting `σ ĥ + a` is
transporting `σ h + (a + σ s)` (change of variables `∫ φ = ∫ φ'`). -/
theorem isChartTransport_shift_iff {c : Chart} (hc : c.IsConformal) {s σ a k : ℝ}
    {h ĥ g : DistOn upperHalfPlaneOpens} (hĥ : IsTranslateAddConst 0 s h ĥ) :
    IsChartTransport c σ a k ĥ g ↔ IsChartTransport c σ (a + σ * s) k h g := by
  have key : ∀ φ φ' : TestOn upperHalfPlaneOpens, tsupport φ ⊆ c.2.1 '' H →
      (∀ z ∈ c.2.1 '' H, φ z = φ' (c.1 z) * ‖deriv c.1 z‖ ^ 2) →
      σ * ĥ φ + a * (∫ w, φ' w) = σ * h φ + (a + σ * s) * (∫ w, φ' w) := by
    intro φ φ' hs hφ
    rw [translateAddConst_zero_apply hĥ, integral_eq_of_transportPair hc hs hφ]
    ring
  constructor
  · intro ht φ φ' hs hφ
    rw [ht φ φ' hs hφ]
    linear_combination key φ φ' hs hφ
  · intro ht φ φ' hs hφ
    rw [ht φ φ' hs hφ]
    linear_combination -(key φ φ' hs hφ)

/-- The chart `infinitySourceChartAt n` is conformal (it has the maps of `infinitySourceChart`). -/
theorem isConformal_infinitySourceChartAt (n : ℤ) : (infinitySourceChartAt n).IsConformal :=
  Chart.isConformal_infinitySourceChart

/-- **A change of branch moves the offset by `2πnk`**: the lift of `infinitySourceChartAt n` is the FD12.1 lift plus
`2πn`. -/
theorem isChartTransport_infinitySourceChartAt_iff (n : ℤ) {σ a k : ℝ} {h g : DistOn upperHalfPlaneOpens} :
    IsChartTransport (infinitySourceChartAt n) σ a k h g ↔
      IsChartTransport infinitySourceChart σ (a + 2 * Real.pi * n * k) k h g := by
  have hint : ∀ φ' : TestOn upperHalfPlaneOpens,
      ∫ w, (infinitySourceChartAt n).2.2 ((infinitySourceChartAt n).2.1 w) * φ' w =
        (∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w) + 2 * Real.pi * n * ∫ w, φ' w := by
    intro φ'
    have h1 := integrable_mul_testOn Chart.continuousOn_infinitySourceChart_lift φ'
    have h2 := (integrable_testOn φ').const_mul (2 * Real.pi * n)
    have e : (fun w => (infinitySourceChartAt n).2.2 ((infinitySourceChartAt n).2.1 w) * φ' w) =
        fun w => infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w + 2 * Real.pi * n * φ' w := by
      funext w
      show ((-2 * Complex.log (-w⁻¹)).im + 2 * Real.pi * n) * φ' w =
        (-2 * Complex.log (-w⁻¹)).im * φ' w + 2 * Real.pi * n * φ' w
      ring
    rw [e, integral_add h1 h2, integral_const_mul]
  constructor
  · intro ht φ φ' hs hφ
    have e := ht φ φ' hs hφ
    rw [hint] at e
    rw [e]
    ring
  · intro ht φ φ' hs hφ
    have e := ht φ φ' hs hφ
    rw [hint, e]
    ring

theorem isChartTransport_infinitySourceChartAt_zero_iff {σ a k : ℝ} {h g : DistOn upperHalfPlaneOpens} :
    IsChartTransport (infinitySourceChartAt 0) σ a k h g ↔ IsChartTransport infinitySourceChart σ a k h g := by
  rw [isChartTransport_infinitySourceChartAt_iff]
  simp only [Int.cast_zero, mul_zero, zero_mul, add_zero]

/-! ### The explicit parameter fields -/

/-- `arg` is continuous on `ℍ`. -/
theorem continuousOn_arg_H : ContinuousOn (fun w : ℂ => Complex.arg w) H := fun _ hw =>
  (Complex.continuousAt_arg (Or.inr (ne_of_gt hw))).continuousWithinAt

/-- `∫ (a − b arg w) φ'(w) dw = a ∫ φ' − b ∫ arg · φ'`. -/
theorem integral_sub_arg_mul (a b : ℝ) (φ' : TestOn upperHalfPlaneOpens) :
    ∫ w, (a - b * Complex.arg w) * φ' w = a * (∫ w, φ' w) - b * ∫ w, Complex.arg w * φ' w := by
  have hi := integrable_mul_testOn continuousOn_arg_H φ'
  have e : (fun w => (a - b * Complex.arg w) * φ' w) = fun w => a * φ' w - b * (Complex.arg w * φ' w) := by
    funext w
    ring
  rw [e, integral_sub ((integrable_testOn φ').const_mul a) (hi.const_mul b), integral_const_mul,
    integral_const_mul]

/-- `arg(−1/w) = π − arg w` on `ℍ`. -/
theorem arg_neg_inv {w : ℂ} (hw : 0 < w.im) : Complex.arg (-w⁻¹) = Real.pi - Complex.arg w := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at hw; exact lt_irrefl _ hw
  have hinv : (w⁻¹).im < 0 := by
    rw [Complex.inv_im]
    exact div_neg_of_neg_of_pos (neg_lt_zero.2 hw) (Complex.normSq_pos.2 hw0)
  have hpi : Complex.arg w ≠ Real.pi := fun h => by
    have := (Complex.arg_eq_pi_iff.1 h).2
    rw [this] at hw
    exact lt_irrefl _ hw
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hinv, Complex.arg_inv, ite_eq_right hpi]
  ring

/-- **The FD12.1 lift read at `R(w)`**: `Im(−2 Log(−1/w)) = 2 arg w − 2π` on `ℍ`; equivalently the compatible inverse
lift is `arg (R⁻¹)′(w) = 2π − 2 arg w` (FD12.2). -/
theorem infinitySourceChart_lift_inv {w : ℂ} (hw : 0 < w.im) :
    infinitySourceChart.2.2 (infinitySourceChart.2.1 w) = 2 * Complex.arg w - 2 * Real.pi := by
  change (-2 * Complex.log (-w⁻¹)).im = _
  have e : (-2 * Complex.log (-w⁻¹)).im = -2 * (Complex.log (-w⁻¹)).im := by
    rw [Complex.mul_im]
    simp
  rw [e, Complex.log_im, arg_neg_inv hw]
  ring

/-- `∫ ℓ(R w) φ'(w) dw = 2 ∫ arg · φ' − 2π ∫ φ'` for the FD12.1 lift `ℓ`. -/
theorem integral_lift_inv_mul (φ' : TestOn upperHalfPlaneOpens) :
    ∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w =
      2 * (∫ w, Complex.arg w * φ' w) - 2 * Real.pi * ∫ w, φ' w := by
  have hi := integrable_mul_testOn continuousOn_arg_H φ'
  have e : ∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w =
      ∫ w, (2 * (Complex.arg w * φ' w) - 2 * Real.pi * φ' w) := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ H
    · show infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w =
        2 * (Complex.arg w * φ' w) - 2 * Real.pi * φ' w
      rw [infinitySourceChart_lift_inv hw]
      ring
    · show infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w =
        2 * (Complex.arg w * φ' w) - 2 * Real.pi * φ' w
      rw [testOn_eq_zero_of_notMem hw]
      ring
  rw [e, integral_sub (hi.const_mul 2) ((integrable_testOn φ').const_mul _), integral_const_mul,
    integral_const_mul]

/-- **The literal parameter field, branch `n`**: if `hR = h ∘ R + χ (arg R′) ∘ R` with the lift of branch `n`, then for
every transport pair `(φ, φ')`, `⟨−hR, φ'⟩ = −⟨h, φ⟩ + ∫ (2π(1 − n)χ − 2χ arg w) φ'(w) dw`: the parameter field is
`−h ∘ R + 2π(1 − n)χ − 2χ arg w` (for `n = 0`: `−h ∘ R + 2πχ − 2χ arg w`, the audit's computation). -/
theorem literalAt_paramField_apply {κ : ℝ} (n : ℤ) {h hR : DistOn upperHalfPlaneOpens}
    (hR' : IsChartTransport (infinitySourceChartAt n) 1 0 (chiC κ) h hR) {φ φ' : TestOn upperHalfPlaneOpens}
    (hs : tsupport φ ⊆ infinitySourceChart.2.1 '' H)
    (hφ : ∀ z ∈ infinitySourceChart.2.1 '' H,
      φ z = φ' (infinitySourceChart.1 z) * ‖deriv infinitySourceChart.1 z‖ ^ 2) :
    (-hR) φ' = -h φ + ∫ w, (2 * Real.pi * (1 - n) * chiC κ - 2 * chiC κ * Complex.arg w) * φ' w := by
  have e := (isChartTransport_infinitySourceChartAt_iff n).1 hR' φ φ' hs hφ
  rw [neg_apply, e, integral_lift_inv_mul, integral_sub_arg_mul]
  ring

/-- **The centred parameter field (FD12.5)**: if `g` is the frozen centred transport of `h`, then for every transport
pair `(φ, φ')`, `⟨g, φ'⟩ = −⟨h, φ⟩ + ∫ (πχ − 2χ arg w) φ'(w) dw`: the parameter field is `−h ∘ R + πχ − 2χ arg w`. -/
theorem centred_paramField_apply {κ : ℝ} (hκ : 0 < κ) {h g : DistOn upperHalfPlaneOpens}
    (hg : IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h g)
    {φ φ' : TestOn upperHalfPlaneOpens} (hs : tsupport φ ⊆ infinitySourceChart.2.1 '' H)
    (hφ : ∀ z ∈ infinitySourceChart.2.1 '' H,
      φ z = φ' (infinitySourceChart.1 z) * ‖deriv infinitySourceChart.1 z‖ ^ 2) :
    g φ' = -h φ + ∫ w, (Real.pi * chiC κ - 2 * chiC κ * Complex.arg w) * φ' w := by
  rw [hg φ φ' hs hφ, integral_lift_inv_mul, integral_sub_arg_mul, Sec4.chiC_sixteen_div hκ]
  ring

/-! ### The bridge -/

/-- **The frame bridge for fields, branch `n`**: for `ĥ = h + (1 − 2n)πχ`, `g` is the centred parameter field of `h`
iff `−g` is the literal transport (branch `n`) of `ĥ`. -/
theorem centred_iff_literalAt {κ : ℝ} (hκ : 0 < κ) (n : ℤ) {h ĥ g : DistOn upperHalfPlaneOpens}
    (hĥ : IsTranslateAddConst 0 ((1 - 2 * n) * (Real.pi * chiC κ)) h ĥ) :
    IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h g ↔
      IsChartTransport (infinitySourceChartAt n) 1 0 (chiC κ) ĥ (-g) := by
  calc IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h g
      ↔ IsChartTransport infinitySourceChart (-(-1)) (-(-(Real.pi * chiC κ))) (-(chiC (16 / κ))) h (-g) :=
        isChartTransport_neg_iff
    _ ↔ IsChartTransport infinitySourceChart 1
          (0 + 2 * Real.pi * n * chiC κ + 1 * ((1 - 2 * n) * (Real.pi * chiC κ))) (chiC κ) h (-g) := by
        have e : (0 + 2 * Real.pi * n * chiC κ + 1 * ((1 - 2 * n) * (Real.pi * chiC κ))) =
            -(-(Real.pi * chiC κ)) := by ring
        rw [e, Sec4.chiC_sixteen_div hκ, neg_neg (chiC κ), neg_neg (1 : ℝ)]
    _ ↔ IsChartTransport infinitySourceChart 1 (0 + 2 * Real.pi * n * chiC κ) (chiC κ) ĥ (-g) :=
        (isChartTransport_shift_iff Chart.isConformal_infinitySourceChart hĥ).symm
    _ ↔ IsChartTransport (infinitySourceChartAt n) 1 0 (chiC κ) ĥ (-g) :=
        (isChartTransport_infinitySourceChartAt_iff n).symm

/-- **The frame bridge for fields (FD11.1)**: for `ĥ = h + πχ`, `g` is the centred parameter field of `h` iff `−g` is
the literal transport `ĥ ∘ R + χ (arg R′) ∘ R` of `ĥ` (FD12.1 branch). -/
theorem centred_iff_literal {κ : ℝ} (hκ : 0 < κ) {h ĥ g : DistOn upperHalfPlaneOpens}
    (hĥ : IsTranslateAddConst 0 (Real.pi * chiC κ) h ĥ) :
    IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h g ↔
      IsChartTransport infinitySourceChart 1 0 (chiC κ) ĥ (-g) := by
  have e : (1 - 2 * ((0 : ℤ) : ℝ)) * (Real.pi * chiC κ) = Real.pi * chiC κ := by
    rw [Int.cast_zero]
    ring
  have hĥ0 : IsTranslateAddConst 0 ((1 - 2 * ((0 : ℤ) : ℝ)) * (Real.pi * chiC κ)) h ĥ := by
    rw [e]
    exact hĥ
  rw [centred_iff_literalAt hκ 0 hĥ0, isChartTransport_infinitySourceChartAt_zero_iff]

/-- **The parameter fields coincide**: the centred parameter field `g` of `h` is minus the literal transport `hR` of
`ĥ = h + πχ`. -/
theorem centred_eq_neg_literal {κ : ℝ} (hκ : 0 < κ) {h ĥ g hR : DistOn upperHalfPlaneOpens}
    (hĥ : IsTranslateAddConst 0 (Real.pi * chiC κ) h ĥ)
    (hg : IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h g)
    (hR' : IsChartTransport infinitySourceChart 1 0 (chiC κ) ĥ hR) : g = -hR := by
  have h1 : IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h (-hR) :=
    (centred_iff_literal hκ hĥ).2 (by rw [neg_neg]; exact hR')
  exact hg.unique Chart.isConformal_infinitySourceChart h1

/-- **The bridge with the same boundary data and the same induced force word**: for every boundary word `b'` (locally
constant off `jumps'`), `W` drives the angle-`0` parameter-`κ′` flow line of the centred parameter field of `h` with
the word induced by `b'` iff it drives that of the literal parameter field `−hR` of `ĥ = h + πχ` with the same word. -/
theorem centredWitness_iff_literalWitness {κ : ℝ} (hκ : 0 < κ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    {h ĥ : Ω → DistOn upperHalfPlaneOpens} (hĥ : ∀ ω, IsTranslateAddConst 0 (Real.pi * chiC κ) (h ω) (ĥ ω))
    (b' : ℝ → ℝ) (jumps' : Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    (∃ g : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (g ω)) ∧
          IsFlowLineDriver (16 / κ) b' jumps' 0 P g W ζ) ↔
      ∃ hR : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport infinitySourceChart 1 0 (chiC κ) (ĥ ω) (hR ω)) ∧
          IsFlowLineDriver (16 / κ) b' jumps' 0 P (fun ω => -hR ω) W ζ := by
  constructor
  · rintro ⟨g, hg, hfl⟩
    refine ⟨fun ω => -g ω, fun ω => (centred_iff_literal hκ (hĥ ω)).1 (hg ω), ?_⟩
    simpa only [neg_neg] using hfl
  · rintro ⟨hR, hR', hfl⟩
    refine ⟨fun ω => -hR ω, fun ω => (centred_iff_literal hκ (hĥ ω)).2 ?_, hfl⟩
    simpa only [neg_neg] using hR' ω

/-- **FD11.1, `CF_d(h) = CF_lit(h + πχ)`, for the same driver and lifetime**: `W` (lifetime `ζ`) drives the frozen
centred counterflow of `h` iff it drives the paper's literal counterflow (FD12.1 branch) of `ĥ = h + πχ`. -/
theorem isCenteredCounterflowDriver_iff_literal {κ : ℝ} (hκ : 0 < κ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) {h ĥ : Ω → DistOn upperHalfPlaneOpens}
    (hĥ : ∀ ω, IsTranslateAddConst 0 (Real.pi * chiC κ) (h ω) (ĥ ω)) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    IsCenteredCounterflowDriver κ P h W ζ ↔ IsLiteralCounterflowDriver κ P ĥ W ζ := by
  constructor
  · rintro ⟨b', jumps', g, hb', hg, hfl⟩
    obtain ⟨hR, hR', hfl'⟩ := (centredWitness_iff_literalWitness hκ P hĥ b' jumps' W ζ).1 ⟨g, hg, hfl⟩
    exact ⟨b', jumps', hR, hb', hR', hfl'⟩
  · rintro ⟨b', jumps', hR, hb', hR', hfl⟩
    obtain ⟨g, hg, hfl'⟩ := (centredWitness_iff_literalWitness hκ P hĥ b' jumps' W ζ).2 ⟨hR, hR', hfl⟩
    exact ⟨b', jumps', g, hb', hg, hfl'⟩

/-- **The bridge for the branch `n`**: `W` drives the centred counterflow of `h` iff it drives the literal
counterflow (branch `n`) of `ĥ = h + (1 − 2n)πχ`. For `n = 1` (the Remark's normalization): `CF_d(h) = CF_lit(h − πχ)`. -/
theorem isCenteredCounterflowDriver_iff_literalAt {κ : ℝ} (hκ : 0 < κ) (n : ℤ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) {h ĥ : Ω → DistOn upperHalfPlaneOpens}
    (hĥ : ∀ ω, IsTranslateAddConst 0 ((1 - 2 * n) * (Real.pi * chiC κ)) (h ω) (ĥ ω))
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    IsCenteredCounterflowDriver κ P h W ζ ↔ IsLiteralCounterflowDriverAt n κ P ĥ W ζ := by
  constructor
  · rintro ⟨b', jumps', g, hb', hg, hfl⟩
    refine ⟨b', jumps', fun ω => -g ω, hb', fun ω => (centred_iff_literalAt hκ n (hĥ ω)).1 (hg ω), ?_⟩
    simpa only [neg_neg] using hfl
  · rintro ⟨b', jumps', hR, hb', hR', hfl⟩
    refine ⟨b', jumps', fun ω => -hR ω, hb', fun ω => (centred_iff_literalAt hκ n (hĥ ω)).2 ?_, hfl⟩
    simpa only [neg_neg] using hR' ω

/-- `IsLiteralCounterflowDriver` is `IsLiteralCounterflowDriverAt 0` (FD12.1 is the branch `n = 0`). -/
theorem isLiteralCounterflowDriver_iff_at_zero {κ : ℝ} {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    IsLiteralCounterflowDriver κ P h W ζ ↔ IsLiteralCounterflowDriverAt 0 κ P h W ζ := by
  unfold IsLiteralCounterflowDriver IsLiteralCounterflowDriverAt
  simp only [isChartTransport_infinitySourceChartAt_zero_iff]

/-! ### The half-turn is a frame convention, not a branch choice -/

/-- **No branch removes the half-turn**: for `0 < κ < 4`, every branch `n` and every field `h`, the literal parameter
field `−hR` of `h` (branch `n`) and the centred parameter field `g` of the same `h` differ by the constant
`(1 − 2n)πχ`, which is nonzero; in particular `−hR ≠ g`. -/
theorem literalAt_paramField_ne_centred {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (n : ℤ)
    {h g hR : DistOn upperHalfPlaneOpens}
    (hg : IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h g)
    (hR' : IsChartTransport (infinitySourceChartAt n) 1 0 (chiC κ) h hR) :
    (∀ φ' : TestOn upperHalfPlaneOpens, (-hR) φ' = g φ' + (1 - 2 * n) * (Real.pi * chiC κ) * ∫ w, φ' w) ∧
      (1 - 2 * (n : ℝ)) * (Real.pi * chiC κ) ≠ 0 ∧ -hR ≠ g := by
  have hc := Chart.isConformal_infinitySourceChart
  have hdiff : ∀ φ' : TestOn upperHalfPlaneOpens,
      (-hR) φ' = g φ' + (1 - 2 * n) * (Real.pi * chiC κ) * ∫ w, φ' w := by
    intro φ'
    have e1 := hg.apply_eq hc φ'
    have e2 := ((isChartTransport_infinitySourceChartAt_iff n).1 hR').apply_eq hc φ'
    rw [neg_apply, e2, e1, Sec4.chiC_sixteen_div hκ]
    ring
  have hne : (1 - 2 * (n : ℝ)) * (Real.pi * chiC κ) ≠ 0 := by
    refine mul_ne_zero ?_ (mul_ne_zero Real.pi_ne_zero (Sec4.chiC_pos hκ hκ4).ne')
    intro h0
    have h1 : ((1 : ℤ) : ℝ) = ((2 * n : ℤ) : ℝ) := by
      push_cast
      linarith
    have h2 : (1 : ℤ) = 2 * n := Int.cast_injective h1
    omega
  refine ⟨hdiff, hne, fun heq => ?_⟩
  obtain ⟨φ, hφ⟩ := exists_testOn_integral_ne_zero
  have h3 := hdiff φ
  rw [heq] at h3
  have h0 : (1 - 2 * (n : ℝ)) * (Real.pi * chiC κ) * ∫ w, φ w = 0 := by linarith
  exact mul_ne_zero hne hφ h0

/-- The value of the branch-`n` lift at `R⁻¹(i) = i`: `arg R′(i) = −π + 2πn`. -/
theorem infinitySourceChartAt_lift_I (n : ℤ) :
    (infinitySourceChartAt n).2.2 ((infinitySourceChartAt n).2.1 Complex.I) = -Real.pi + 2 * Real.pi * n := by
  show (-2 * Complex.log (-Complex.I⁻¹)).im + 2 * Real.pi * n = -Real.pi + 2 * Real.pi * n
  rw [Complex.inv_I, neg_neg, Complex.log_I]
  have e : (-2 * ((Real.pi : ℂ) / 2 * Complex.I)).im = -Real.pi := by
    have e' : (-2 * ((Real.pi : ℂ) / 2 * Complex.I)) = ((-Real.pi : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e', Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [e]

/-- **The paper's Remark normalization selects the branch `n = 1`** (p. 19: "fix the branch of `arg ψ′` … so that
`arg ψ′(ψ⁻¹(i)) ∈ (−π, π]`"): with `ψ = R`, `ψ⁻¹(i) = i` and `arg R′(i) = −π + 2πn`, which lies in `(−π, π]` exactly
for `n = 1`. With it, `CF_d(h) = CF_lit(h − πχ)` (`isCenteredCounterflowDriver_iff_literalAt`). -/
theorem remarkBranch_iff (n : ℤ) :
    (infinitySourceChartAt n).2.2 ((infinitySourceChartAt n).2.1 Complex.I) ∈ Set.Ioc (-Real.pi) Real.pi ↔
      n = 1 := by
  rw [infinitySourceChartAt_lift_I, Set.mem_Ioc]
  have hπ := Real.pi_pos
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (0 : ℝ) < n := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith
    have h2' : (n : ℝ) ≤ 1 := by
      by_contra hc
      have hc' := not_le.1 hc
      nlinarith
    have h3 : (0 : ℤ) < n := by exact_mod_cast h1'
    have h4 : n ≤ 1 := by exact_mod_cast h2'
    omega
  · rintro rfl
    push_cast
    constructor <;> linarith

/-! ### The boundary data of the shifted field -/

/-- `b + s` is finite piecewise-constant data (with the same finite set `jumps`) iff `b` is. -/
theorem isPiecewiseConstantBoundaryData_add_const_iff (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ℝ) :
    IsPiecewiseConstantBoundaryData (fun x => b x + s) jumps ↔ IsPiecewiseConstantBoundaryData b jumps := by
  constructor
  · intro hb y hy
    exact (hb y hy).mono fun z hz => add_right_cancel hz
  · intro hb y hy
    exact (hb y hy).mono fun z hz => by simp only [hz]

/-- Adding a constant to a bounded harmonic extension of `g` gives one of `g + s`. -/
theorem isBoundedHarmonicExtension_add_const {g : ℝ → ℝ} {S : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (s : ℝ) :
    IsBoundedHarmonicExtension (fun x => g x + s) S (fun z => u z + s) := by
  obtain ⟨hharm, ⟨C, hC⟩, hlim⟩ := hu
  refine ⟨fun z hz => (hharm z hz).add (InnerProductSpace.harmonicAt_const _), ⟨C + |s|, fun z hz => ?_⟩,
    fun x hx => (hlim x hx).add_const s⟩
  exact (abs_add_le _ _).trans (by linarith [hC z hz])

/-- **The boundary data of the shifted field**: for `ĥ = h + s` (frozen `IsTranslateAddConst 0 s`), `ĥ` is a GFF with
boundary data `b + s` (off `S`) iff `h` is a GFF with boundary data `b` (off `S`). The shift acts on the GFF and on its
boundary data together; the zero-boundary part `ĥ − 𝔥_{b+s} = h − 𝔥_b` is unchanged. -/
theorem isGFFWithBoundaryData_shift_iff {s : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h ĥ : Ω → DistOn upperHalfPlaneOpens} (hĥ : ∀ ω, IsTranslateAddConst 0 s (h ω) (ĥ ω)) (b : ℝ → ℝ)
    (S : Set ℝ) :
    IsGFFWithBoundaryData P ĥ (fun x => b x + s) S ↔ IsGFFWithBoundaryData P h b S := by
  have happ : ∀ ω φ, ĥ ω φ = h ω φ + s * ∫ z, φ z := fun ω φ => translateAddConst_zero_apply (hĥ ω) φ
  have hproc : ∀ u : ℂ → ℝ, ContinuousOn u H →
      (fun (φ : TestOn upperHalfPlaneOpens) (ω : Ω) => ĥ ω φ - ∫ z, (u z + s) * φ z) =
        fun φ ω => h ω φ - ∫ z, u z * φ z := by
    intro u hu
    funext φ ω
    have e1 : (fun z => (u z + s) * φ z) = fun z => u z * φ z + s * φ z := by
      funext z
      ring
    rw [happ, e1, integral_add (integrable_mul_testOn hu φ) ((integrable_testOn φ).const_mul s),
      integral_const_mul]
    ring
  have hmeas : Measurable ĥ ↔ Measurable h := by
    rw [LQGMetric.measurable_distOn_iff, LQGMetric.measurable_distOn_iff]
    refine forall_congr' fun φ => ?_
    have e : (fun ω => ĥ ω φ) = fun ω => h ω φ + s * ∫ z, φ z := funext fun ω => happ ω φ
    rw [e]
    refine ⟨fun hm => ?_, fun hm => hm.add_const _⟩
    have := hm.add_const (-(s * ∫ z, φ z))
    simpa only [add_neg_cancel_right] using this
  constructor
  · rintro ⟨hm, hz⟩
    refine ⟨hmeas.1 hm, fun u₀ hu₀ => ?_⟩
    rw [← hproc u₀ hu₀.1.continuousOn]
    exact hz _ (isBoundedHarmonicExtension_add_const hu₀ s)
  · rintro ⟨hm, hz⟩
    refine ⟨hmeas.2 hm, fun u hu => ?_⟩
    have hu' : IsBoundedHarmonicExtension b S (fun z => u z - s) := by
      have h1 := isBoundedHarmonicExtension_add_const hu (-s)
      convert h1 using 1
      all_goals
        funext x
        simp [sub_eq_add_neg]
    have h2 := hproc (fun z => u z - s) hu'.1.continuousOn
    simp only [sub_add_cancel] at h2
    rw [h2]
    exact hz _ hu'

end InteractingSLE.AuditFix.CFLit
