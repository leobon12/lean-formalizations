import QuantumZipper.Proofs.Section5.Prop16MeasGood
import QuantumZipper.Proofs.LQG.WedgeMeasND
import QuantumZipper.Proofs.LQG.WedgeFinZeroCoupling
import QuantumZipper.Proofs.LQG.WedgeInfTotal
import QuantumZipper.Proofs.LQG.PalmFormula
import QuantumZipper.Statements.Prop16

/-!
# Proposition 1.6, top-level assembly (PROP16-ASM), part 1: the elementary inputs

The inputs of D4-a (`Prop16Area.Meas.prop16_areaConvergesInLawOn_of_inputs'`) that follow from
proved nodes or from elementary facts, for the objects of `theorem1_6`:

* `isProbabilityMeasure_prop16Law`: the weighted law `prop16Law` is a probability measure once
  the random boundary measure `ω ↦ ν_{h(ω)}` is a.e.-measurable (the kernel of the `bind` is then
  a.e.-measurable: `aemeasurable_prop16Kernel`, via the s-finite kernel `Palm.kerI` of D1);
* `ae_snd_mem_Ioo`: under `prop16Law`, a.s. the marked point lies in `(a,b)` (the local
  boundary measure `qBoundaryMeasureOn _ _ (Ioo a b)` gives no mass outside `(a,b)`); hence
  (`ae_halfDisc`) a.s. it carries a half-disc inside `D` (geometry hypothesis of `theorem1_6`);
* `wedge_coords_aemeasurable`, `wedge_ae_exists_vague`: every `γ`-quantum wedge has a.e.-measurable
  coordinates and a.s. a quantum area measure (R23 via `WedgeMeasND`, with the proved
  `wedgeFiniteNearZero_holds`, `wedgeInfiniteTotal`).

Own elementary arguments (AGENT_GUIDE cost rule); the reading follows Sheffield,
*Conformal weldings of random surfaces*, arXiv:1012.4797, Proposition 1.6 and its proof
(pp. 19–25): `x` is sampled from `ν_h|_{[a,b]}` normalized, `h` from `ν_h[a,b] dh` normalized.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-! ## 1. Good samples have a vague area limit along the dyadic radii -/

/-- A good sample (`IsLQGGood`) has a vague limit of `areaApprox γ x` on `ℍ`: restrict the
uniform limit along `goodFilter` to the offsets `a = 1`. -/
theorem exists_isVagueLimitOn_of_isLQGGood {γ : ℝ} {x : FieldSample} (h : IsLQGGood γ x) :
    ∃ μ, IsVagueLimitOn H (areaApprox γ x) μ := by
  obtain ⟨⟨F, hF⟩, _, μ, hμ1, hμ2, hμ3⟩ := h
  refine ⟨μ, hμ1, hμ2, fun f hf hfs hft => ?_⟩
  have ht : Tendsto (fun k : ℕ => ((k, (1 : ℝ)) : ℕ × ℝ)) atTop goodFilter :=
    tendsto_id.prodMk (tendsto_principal.2
      (Eventually.of_forall fun _ => ⟨le_rfl, one_le_two⟩))
  refine ((hμ3 f hf hfs hft).comp ht).congr fun k => ?_
  simp only [Function.comp, goodRad]
  rw [GoodSample.areaR_radius γ hF k]

/-! ## 2. The quantum wedge side -/

theorem gamma_lt_Qc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < Qc γ := by
  unfold Qc
  have h1 : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ two_pos hγ]; nlinarith
  linarith

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : Ω' → FieldSample}

/-- The dyadic coordinates of a `γ`-quantum wedge are a.e.-measurable. -/
theorem wedge_coords_aemeasurable {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hW : IsQuantumWedge γ γ W P') :
    AEMeasurable (fun ω => Factorization.coords (W ω)) P' := by
  have hα := gamma_lt_Qc hγ hγ2
  have hd := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hα)
    hγ hγ2 hW
  have := (WedgeCan4.measurable_piC.comp measurable_fst).comp_aemeasurable hd
  refine this.congr (Eventually.of_forall fun ω => ?_)
  exact WedgeCan4.piC_coordsFull (W ω)

/-- A `γ`-quantum wedge has a.s. a quantum area measure on `ℍ`. -/
theorem wedge_ae_exists_vague {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hW : IsQuantumWedge γ γ W P') :
    ∀ᵐ ω ∂P', ∃ μ, IsVagueLimitOn H (areaApprox γ (W ω)) μ := by
  have hα := gamma_lt_Qc hγ hγ2
  exact (WedgeMeasND.IsQuantumWedge.ae_unitArea
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hα)
    hγ hγ2 hW).mono fun ω hω => exists_isVagueLimitOn_of_isLQGGood hω.1

/-! ## 3. The weighted law `prop16Law` -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Ω → Measure ℝ} {a b : ℝ}

/-- The kernel `ω ↦ δ_ω ⊗ ν_ω|_{[a,b]}` of `prop16Law` is a.e.-measurable. -/
theorem aemeasurable_prop16Kernel (hν : AEMeasurable ν P)
    (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ⊤) :
    AEMeasurable (fun ω => (Measure.dirac ω).prod ((ν ω).restrict (Icc a b))) P := by
  let κ : Kernel Ω (Ω × ℝ) :=
    (Kernel.deterministic id measurable_id) ×ₖ Palm.kerI hν (measurableSet_Icc (a := a) (b := b))
  refine ⟨fun ω => κ ω, κ.measurable, ?_⟩
  filter_upwards [Palm.nuMod_ae_eq hν (measurableSet_Icc (a := a) (b := b)) hfin] with ω hω
  simp only [κ]
  rw [Kernel.prod_apply, Kernel.deterministic_apply, Palm.kerI_apply, hω]
  rfl

theorem prop16Kernel_apply_prod (ω : Ω) (hω : ν ω (Icc a b) ≠ ⊤) {s : Set Ω} {t : Set ℝ}
    (ht : MeasurableSet t) :
    (Measure.dirac ω).prod ((ν ω).restrict (Icc a b)) (s ×ˢ t) =
      (Measure.dirac ω) s * ν ω (t ∩ Icc a b) := by
  have : IsFiniteMeasure ((ν ω).restrict (Icc a b)) := isFiniteMeasure_restrict.mpr hω
  rw [Measure.prod_prod, Measure.restrict_apply ht]

theorem ae_nu_ne_top (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ⊤) :
    ∀ᵐ ω ∂P, ν ω (Icc a b) ≠ ⊤ :=
  (ae_lt_top' ((Measure.measurable_coe measurableSet_Icc).comp_aemeasurable hν) hfin.ne).mono
    fun _ h => h.ne

/-- `prop16Law` is a probability measure when `0 < E ν[a,b] < ∞` and `ν` is a.e.-measurable. -/
theorem isProbabilityMeasure_prop16Law (hν : AEMeasurable ν P)
    (hpos : 0 < ∫⁻ ω, ν ω (Icc a b) ∂P) (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ⊤) :
    IsProbabilityMeasure (prop16Law P ν a b) := by
  constructor
  rw [prop16Law, Measure.smul_apply, smul_eq_mul,
    Measure.bind_apply MeasurableSet.univ (aemeasurable_prop16Kernel hν hfin)]
  have hc : ∫⁻ ω, (Measure.dirac ω).prod ((ν ω).restrict (Icc a b)) univ ∂P =
      ∫⁻ ω, ν ω (Icc a b) ∂P :=
    lintegral_congr_ae ((ae_nu_ne_top hν hfin).mono fun ω hω => by
      beta_reduce
      rw [← univ_prod_univ, prop16Kernel_apply_prod ω hω MeasurableSet.univ, univ_inter,
        measure_univ, one_mul])
  rw [hc]
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

/-- The local boundary measure on `(a,b)` gives no mass outside `(a,b)`. -/
theorem prop16Nu_compl (γ : ℝ) (h0 : ℂ → ℝ) (x : FieldSample) :
    prop16Nu γ h0 a b x (Ioo a b)ᶜ = 0 := by
  unfold prop16Nu qBoundaryMeasureOn
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

end Prop16Asm

end QuantumZipper
