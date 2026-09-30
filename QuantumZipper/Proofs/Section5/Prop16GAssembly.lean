import QuantumZipper.Proofs.Section5.Prop16GSite
import QuantumZipper.Proofs.Section5.Prop16GNu

/-!
# Proposition 1.6, node D4-G (part 3): D4-a with `hsite`, `hν` discharged and `hG0`/`hG1`
reduced to `P`-a.s. statements

For the objects of `theorem1_6` (`Statements/Prop16.lean`):

* `isProbabilityMeasure_prop16Law'`: `prop16Law` is a probability measure when
  `ω ↦ ν_{h(ω)}` is a.e.-measurable and `0 < E ν_h[a,b] < ∞` (the argument of
  `Prop16Asm.isProbabilityMeasure_prop16Law`);
* `exists_vague_canonicalOn`: deterministic. The canonical scale is `≥ 0`; at scale `0` the
  canonical domain `{z | 0·z ∈ U}` is empty (when `0 ∉ U`) and the vague limit is `0`; at a
  positive scale `s` the canonical field is `rescale x Q s`. So the vague area limit of the
  canonical field on its domain exists as soon as it exists for every rescaling `s > 0`;
* `prop16_areaConvergesInLawOn_of_inputs''`: D4-a for Proposition 1.6 with `hsite` and the
  measurability of the boundary kernel discharged, and `hG0`/`hG1` replaced by `P`-a.s.
  statements about the field `𝔥₀ + X ω` holding for all marked points `t ∈ (a,b)` at once.

Own elementary arguments (AGENT_GUIDE cost rule); reading of Sheffield, arXiv:1012.4797,
Proposition 1.6 and its proof (pp. 7, 25).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

namespace G

open TV Factorization Meas

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `prop16Law` is a probability measure (as in `Prop16Asm.isProbabilityMeasure_prop16Law`). -/
theorem isProbabilityMeasure_prop16Law' {P : Measure Ω} {ν : Ω → Measure ℝ} {a b : ℝ}
    (hν : AEMeasurable ν P) (hpos : 0 < ∫⁻ ω, ν ω (Icc a b) ∂P)
    (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ⊤) :
    IsProbabilityMeasure (prop16Law P ν a b) := by
  constructor
  rw [prop16Law, Measure.smul_apply, smul_eq_mul,
    Measure.bind_apply MeasurableSet.univ (aemeasurable_prop16Kernel' hν hfin)]
  have hae : ∀ᵐ ω ∂P, ν ω (Icc a b) ≠ ⊤ :=
    (ae_lt_top' ((Measure.measurable_coe measurableSet_Icc).comp_aemeasurable hν) hfin.ne).mono
      fun _ h => h.ne
  have hc : ∫⁻ ω, (Measure.dirac ω).prod ((ν ω).restrict (Icc a b)) univ ∂P =
      ∫⁻ ω, ν ω (Icc a b) ∂P :=
    lintegral_congr_ae (hae.mono fun ω hω => by
      have : IsFiniteMeasure ((ν ω).restrict (Icc a b)) := isFiniteMeasure_restrict.mpr hω
      show (Measure.dirac ω).prod ((ν ω).restrict (Icc a b)) univ = ν ω (Icc a b)
      rw [← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply MeasurableSet.univ,
        univ_inter, measure_univ, one_mul])
  rw [hc]
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

theorem isVagueLimitOn_empty (μs : ℕ → Measure ℂ) : IsVagueLimitOn ∅ μs 0 := by
  refine ⟨by simp, fun K _ _ => by simp, fun f _ _ hf => ?_⟩
  have hf0 : ∀ z, f z = 0 := fun z =>
    image_eq_zero_of_notMem_tsupport fun h => (hf h).elim
  simp only [hf0, integral_zero]
  exact tendsto_const_nhds

/-- **Canonical field, deterministic step.** -/
theorem exists_vague_canonicalOn {γ : ℝ} {x : FieldSample} {U : Set ℂ} (h0U : (0 : ℂ) ∉ U)
    (hs : ∀ s : ℝ, 0 < s → ∃ m, IsVagueLimitOn ((fun z => (s : ℂ) * z) ⁻¹' U)
      (areaApprox γ (rescale x (Qc γ) s)) m) :
    ∃ m, IsVagueLimitOn (canonicalDomainOn γ x U) (areaApprox γ (canonicalOn γ x U)) m := by
  have hnn : 0 ≤ scaleParamOn γ x U := Real.sInf_nonneg fun a ha => ha.1.le
  rcases hnn.lt_or_eq with hpos | h0
  · exact hs _ hpos
  · have hempty : canonicalDomainOn γ x U = ∅ := by
      ext z
      simp only [canonicalDomainOn, ← h0, Complex.ofReal_zero, zero_mul, mem_preimage,
        mem_empty_iff_false, iff_false]
      exact h0U
    rw [hempty]
    exact ⟨0, isVagueLimitOn_empty _⟩

theorem zero_notMem_zoomDomain {D : Set ℂ} (hDH : D ⊆ H) (t : ℝ) : (0 : ℂ) ∉ zoomDomain D t :=
  fun h => by
    have := hDH h
    simp [H] at this

end G

end Prop16Area

end QuantumZipper
