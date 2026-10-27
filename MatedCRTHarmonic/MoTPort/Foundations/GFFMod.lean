/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import MatedCRTHarmonic.MoTPort.Foundations.GFF
import Mathlib.MeasureTheory.Function.Floor
import QuantumZipper.Proofs.Thm18.LWHarmPoisson
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import LQGMetric.Field.HeatMollifyPoint

/-!
# Bounded boundary data; fields modulo `cℤ`; lateral part

* `exists_isGFFBoundary_of_bounded`: `exists_isGFFBoundary` for bounded harmonic data (the case of
  IG1's piecewise-constant boundary data).
* `φ₀` and `normMod c h`: the normalized
  representative of `h` modulo `cℤ`, `(h, φ₀) ∈ [0,c)`, with `φ₀` a fixed bump of mass one
  (IG4 = arXiv:1302.4738, L1103: "fix φ₀ ∈ C_c^∞ with ∫ φ₀ = 1"; `φ₀ := LQGMetric.refTest`).
  Lemmas, all **exact for every field**: measurability, `normMod c (h + c k) = normMod c h`,
  `(normMod c h, φ₀) ∈ [0,c)`, `normMod c h = h` on the transversal, idempotence; the a.s.
  versions for a whole-plane GFF are kept as corollaries. The whole-plane GFF modulo `rℤ`
  (independent uniform constant, IG4 L1103–1108) is `IsWPGFFMod` in `GFFWP.lean`.
* `lateralPartC h := h − (z ↦ h_{|z|}(0))` (DMS Lemma 4.2–4.4, L1996, L2029, L2187: the
  lateral part of a whole-plane field); junk: the radial function is replaced by `0` when it is
  not locally integrable (mathlib `Distribution.ofFun`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions

namespace MatedCRTHarmonic.MoTPort

open LQGMetric GFFBdry

/-- the zero extension of a bounded function harmonic on `U` is locally integrable -/
lemma locallyIntegrable_indicator_of_bounded {U : Opens ℂ} {𝔥 : ℂ → ℝ}
    (h𝔥 : InnerProductSpace.HarmonicOnNhd 𝔥 (U : Set ℂ)) {M : ℝ}
    (hM : ∀ z ∈ (U : Set ℂ), |𝔥 z| ≤ M) :
    LocallyIntegrable ((U : Set ℂ).indicator 𝔥) volume := by
  have hmeas : AEStronglyMeasurable ((U : Set ℂ).indicator 𝔥) volume :=
    (aestronglyMeasurable_indicator_iff U.isOpen.measurableSet).2
      (h𝔥.contDiffOn.continuousOn.aestronglyMeasurable U.isOpen.measurableSet)
  refine locallyIntegrable_iff.2 fun k hk => Measure.integrableOn_of_bounded
    hk.measure_lt_top.ne hmeas (M := max M 0) (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ (U : Set ℂ)
  · rw [indicator_of_mem hz, Real.norm_eq_abs]; exact (hM z hz).trans (le_max_left _ _)
  · rw [indicator_of_notMem hz, norm_zero]; exact le_max_right _ _

/-- **Existence of a GFF with bounded deterministic harmonic boundary data** -/
theorem exists_isGFFBoundary_of_bounded (U : Opens ℂ) {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : Disjoint (U : Set ℂ) (sphere z₀ ρ)) (𝔥 : ℂ → ℝ)
    (h𝔥 : InnerProductSpace.HarmonicOnNhd 𝔥 (U : Set ℂ)) {M : ℝ}
    (hM : ∀ z ∈ (U : Set ℂ), |𝔥 z| ≤ M) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Field),
      IsProbabilityMeasure P ∧ IsGFFBoundary U (fun _ => 𝔥) X P :=
  exists_isGFFBoundary U hρ hU 𝔥 h𝔥 (locallyIntegrable_indicator_of_bounded h𝔥 hM)

/-- the upper half-plane `ℍ` (QuantumZipper's `H`) as an open set -/
def opensH : Opens ℂ := ⟨QuantumZipper.H, isOpen_lt continuous_const Complex.continuous_im⟩

lemma disjoint_opensH_sphere : Disjoint (opensH : Set ℂ) (sphere (-2 * Complex.I) 1) := by
  refine Set.disjoint_left.2 fun z hz hs => ?_
  have hz' : 0 < z.im := hz
  rw [mem_sphere, dist_eq_norm] at hs
  have := Complex.abs_im_le_norm (z - -2 * Complex.I)
  simp only [Complex.sub_im, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im] at this
  norm_num at this
  rw [sub_eq_add_neg, neg_mul, neg_neg] at hs
  rw [hs] at this
  linarith [le_abs_self (z.im + 2)]

/-! ## Fields modulo `cℤ` -/

/-- the fixed bump `φ₀ ∈ C_c^∞(ℂ)` with `∫ φ₀ = 1` used to normalize fields modulo constants
(IG4 L1103: "fix φ₀ ∈ C_c^∞ with ∫ φ₀ = 1"); it is LQGMetric's reference test function
`refTest` (the standard mollifier supported in `B₁(0)`). -/
def φ₀ : TestC := refTest

lemma integral_φ₀ : ∫ x, φ₀ x = 1 := integral_refTest

/-- the normalized representative of `h` modulo `cℤ`: `h − c⌊(h, φ₀)/c⌋`, so that
`(h, φ₀) ∈ [0,c)` -/
def normMod (c : ℝ) (h : Field) : Field :=
  addConst h (-c * ⌊h φ₀ / c⌋)

namespace NormMod

lemma addConst_addConst (h : Field) (a b : ℝ) :
    addConst (addConst h a) b = addConst h (a + b) := by
  ext φ
  simp only [GFFInv.addConst_apply]
  ring

lemma addConst_zero (h : Field) : addConst h 0 = h := by
  ext φ
  simp only [GFFInv.addConst_apply, mul_zero, add_zero]

lemma addConst_apply_φ₀ (h : Field) (a : ℝ) : addConst h a φ₀ = h φ₀ + a := by
  rw [GFFInv.addConst_apply, integral_φ₀, one_mul]

lemma measurable_addConst_prod : Measurable fun p : Field × ℝ => addConst p.1 p.2 :=
  GFFInv.measurable_distC_iff.2 fun φ => by
    simp only [GFFInv.addConst_apply]
    exact ((measurable_distOn_apply φ).comp measurable_fst).add (measurable_snd.const_mul _)

theorem measurable_normMod (c : ℝ) : Measurable (normMod c) := by
  have hf : Measurable fun h : Field => -c * (⌊h φ₀ / c⌋ : ℝ) :=
    ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      ((measurable_distOn_apply φ₀).div_const c).floor).const_mul _
  refine GFFInv.measurable_distC_iff.2 fun φ => ?_
  simp only [normMod, GFFInv.addConst_apply]
  exact (measurable_distOn_apply φ).add (hf.const_mul _)

/-- the normalized representative differs from `h` by an integer multiple of `c` -/
theorem exists_normMod_eq (c : ℝ) (h : Field) : ∃ k : ℤ, normMod c h = addConst h (c * k) :=
  ⟨-⌊h φ₀ / c⌋, by rw [normMod]; push_cast; ring_nf⟩

/-- adding an integer multiple of `c` does not change the normalized representative
(exact, for every field) -/
theorem normMod_addConst_intMul {c : ℝ} (hc : c ≠ 0) (h : Field) (k : ℤ) :
    normMod c (addConst h (c * k)) = normMod c h := by
  unfold normMod
  rw [addConst_apply_φ₀, addConst_addConst,
    show (h φ₀ + c * k) / c = h φ₀ / c + k by field_simp,
    Int.floor_add_intCast]
  congr 1
  push_cast
  ring

/-- the normalized representative has `(h, φ₀) ∈ [0,c)` (exact, for every field) -/
theorem normMod_apply_φ₀_mem {c : ℝ} (hc : 0 < c) (h : Field) :
    normMod c h φ₀ ∈ Ico 0 c := by
  unfold normMod
  rw [addConst_apply_φ₀]
  set A := h φ₀
  have h1 : (⌊A / c⌋ : ℝ) ≤ A / c := Int.floor_le _
  have h2 : A / c < ⌊A / c⌋ + 1 := Int.lt_floor_add_one _
  have e : A = c * (A / c) := by field_simp
  constructor
  · nlinarith
  · nlinarith

/-- a field already in the transversal `(h, φ₀) ∈ [0,c)` is its own normalized representative -/
theorem normMod_eq_self {c : ℝ} (hc : 0 < c) {h : Field} (hh : h φ₀ ∈ Ico 0 c) :
    normMod c h = h := by
  have : ⌊h φ₀ / c⌋ = 0 := by
    rw [Int.floor_eq_iff]
    refine ⟨by simpa using div_nonneg hh.1 hc.le, ?_⟩
    rw [Int.cast_zero, zero_add, div_lt_one hc]
    exact hh.2
  rw [normMod, this, Int.cast_zero, mul_zero, addConst_zero]

theorem normMod_normMod {c : ℝ} (hc : 0 < c) (h : Field) :
    normMod c (normMod c h) = normMod c h :=
  normMod_eq_self hc (normMod_apply_φ₀_mem hc h)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- a.s. version for a whole-plane GFF (now a corollary of the exact lemma) -/
theorem ae_normMod_addConst_intMul {X : Ω → Field} (_hX : IsWholePlaneGFF X P) {c : ℝ}
    (hc : c ≠ 0) : ∀ᵐ ω ∂P, ∀ k : ℤ, normMod c (addConst (X ω) (c * k)) = normMod c (X ω) :=
  ae_of_all _ fun ω k => normMod_addConst_intMul hc (X ω) k

/-- a.s. version for a whole-plane GFF: the representative lies in the transversal -/
theorem ae_normMod_apply_φ₀_mem {X : Ω → Field} (_hX : IsWholePlaneGFF X P) {c : ℝ}
    (hc : 0 < c) : ∀ᵐ ω ∂P, normMod c (X ω) φ₀ ∈ Ico 0 c :=
  ae_of_all _ fun ω => normMod_apply_φ₀_mem hc (X ω)

end NormMod

/-! ## Lateral part of a whole-plane field -/

/-- the radial part `z ↦ h_{|z|}(0)` of a field, as a function -/
def radialFun (h : Field) : ℂ → ℝ := fun z => circleAvg h ‖z‖ 0

/-- the lateral part `h − h_{|·|}(0)` (DMS Lemmas 4.2–4.4); the radial part is replaced by the
junk value `0` when `radialFun h` is not locally integrable -/
def lateralPartC (h : Field) : Field := h - ofFunC (radialFun h)

lemma lateralPartC_apply {h : Field} (hr : LocallyIntegrable (radialFun h) volume) (φ : TestC) :
    lateralPartC h φ = h φ - ∫ x, φ x * radialFun h x := by
  show h φ - ofFunC (radialFun h) φ = _
  rw [ofFunC, Distribution.ofFun_apply (hr.locallyIntegrableOn _)]
  rfl

end MatedCRTHarmonic.MoTPort
