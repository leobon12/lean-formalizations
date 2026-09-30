import QuantumZipper.Proofs.Zipper.D3PlusN1Local
import QuantumZipper.Proofs.Zipper.D3PlusIMarkov
import QuantumZipper.Proofs.Zipper.D3PlusIII
import QuantumZipper.Proofs.GFF.CircleMeanValue
import QuantumZipper.Proofs.GFF.CoordRegHarm
import QuantumZipper.Proofs.GFF.CoordRegLog
import QuantumZipper.Proofs.GFF.K3.HalfDiscPoisson

/-!
# D3⁺(i), node N1 (part 2): the model field through `(localZ, F)`

The zoomed data of D3⁺ only read the raw values of the model field
`Y_L = zoomModel γ α L ρ₀ (X ω) (g ω)` at the dyadic folded circles inside `ball 0 r`
(`circSet r`, a countable family; `AgreeNear`). At such a circle `μ`,
`Y_L(μ) = Z(μ) + [X(bal μ) − X(ρ₀) + ∫ (α(−log‖·‖) + g) dμ] + L/γ` with `Z = markovZ X 0 r` the
local part (node L2); the bracket `circVal` is `condSigma`-measurable:

* `X(bal μ) − X(ρ₀)` is an outside increment (`K3.measurable_outsideSigma`);
* `∫ g dμ = g(foldH d)` by the mean value property of the harmonic `g ∘ foldH` on the circle
  (`integral_foldedCircle_of_harm`; mathlib `HarmonicOnNhd.circleAverage_eq`), and `g(·)(z)` is
  `condSigma`-measurable (`Setup.gmeas`).

Definitions: `macroF ω : FieldSample` (the values `circVal` on `circSet r`, `0` elsewhere) and
`locModel γ L r (s, f) : FieldSample` (`s μ + f μ + L/γ` on `circSet r`, `0` elsewhere).
Results: `agreeNear_zoomModel_locModel` (for **every** `ω`), `measurable_macroF`
(`condSigma`), `measurable_locModel`.

Own elementary arguments (AGENT_GUIDE cost rule); the decomposition is the half-disc Markov
property (Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), Thm. 2.17;
node L2, `K3.markov_decomposition`) read on circles.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace D3Plus

/-- The dyadic folded circles inside `ball 0 r` (those read by `AgreeNear`). -/
def circSet (r : ℝ) : Set (Measure ℂ) :=
  {μ | ∃ (n k : ℕ) (z : ℂ), ‖dyadicRoundC n z‖ + radius k < r ∧
    μ = foldedCircle (dyadicRoundC n z) (radius k)}

theorem exists_of_mem_circSet {r : ℝ} {μ : Measure ℂ} (h : μ ∈ circSet r) :
    ∃ (d : ℂ) (ρ : ℝ), 0 < ρ ∧ ‖d‖ + ρ < r ∧ μ = foldedCircle d ρ := by
  obtain ⟨n, k, z, hz, rfl⟩ := h
  exact ⟨_, _, radius_pos k, hz, rfl⟩

/-- `isAdmissibleH_foldedCircle` without its (unused) hypothesis on the centre (same proof). -/
theorem isAdmissibleH_foldedCircle' (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IsAdmissibleH (foldedCircle z r) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · set K := Metric.closedBall (0 : ℂ) (‖z‖ + r) ∩ Hbar
    have hK : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
    refine ⟨K, hK, Set.inter_subset_right, ?_⟩
    have := CircleFubini.foldedCircle_support hr.le (z := z) (R := ‖z‖ + r) le_rfl
    exact this
  · exact ⟨_, ENNReal.mul_lt_top ENNReal.ofNat_lt_top ENNReal.ofReal_lt_top,
      lintegral_negLog_foldedCircle_le z hr⟩

theorem foldedCircle_compl_closedBall {d : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    foldedCircle d ρ (Metric.closedBall ((0 : ℝ) : ℂ) (‖d‖ + ρ))ᶜ = 0 := by
  rw [Complex.ofReal_zero]
  exact measure_mono_null (compl_subset_compl.2 inter_subset_left)
    (CircleFubini.foldedCircle_support hρ.le le_rfl)

theorem isLocalH_of_mem_circSet {r : ℝ} {μ : Measure ℂ} (h : μ ∈ circSet r) :
    K3.IsLocalH 0 r μ := by
  obtain ⟨d, ρ, hρ, hdr, rfl⟩ := exists_of_mem_circSet h
  exact ⟨isAdmissibleH_foldedCircle' d hρ, _, hdr, foldedCircle_compl_closedBall hρ⟩

/-- **Mean value property on folded circles**: for `g ∘ foldH` harmonic on `ball 0 r` and a
circle `closedBall d ρ ⊆ ball 0 r`, `g` is integrable on the folded circle and its average is
`g (foldH d)`. -/
theorem integral_foldedCircle_of_harm {g : ℂ → ℝ} {r : ℝ}
    (harm : InnerProductSpace.HarmonicOnNhd (fun z => g (foldH z)) (Metric.ball (0 : ℂ) r))
    {d : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hdr : ‖d‖ + ρ < r) :
    Integrable g (foldedCircle d ρ) ∧ ∫ z, g z ∂foldedCircle d ρ = g (foldH d) := by
  have hcl : Metric.closedBall d ρ ⊆ Metric.ball (0 : ℂ) r := fun w hw => by
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖w‖ = ‖(w - d) + d‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - d‖ + ‖d‖ := norm_add_le _ _
      _ < r := by linarith
  -- integrability on the folded circle
  have hK : CircleFubini.ballH (‖d‖ + ρ) ⊆ Metric.ball (0 : ℂ) r ∩ Hbar := fun w hw =>
    ⟨Metric.closedBall_subset_ball (by linarith) hw.1, hw.2⟩
  have hgc : ContinuousOn g (CircleFubini.ballH (‖d‖ + ρ)) :=
    (continuousOn_g_of_harm harm).mono hK
  have hae : ∀ᵐ w ∂foldedCircle d ρ, w ∈ CircleFubini.ballH (‖d‖ + ρ) :=
    measure_eq_zero_iff_ae_notMem.1 (CircleFubini.foldedCircle_support hρ.le le_rfl) |>.mono
      fun w hw => by simpa using hw
  have hgi : Integrable g (foldedCircle d ρ) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hgc.integrableOn_compact (CircleFubini.isCompact_ballH _)
  refine ⟨hgi, ?_⟩
  -- the circle average
  have hGc : ContinuousOn (fun z => g (foldH z)) (Metric.closedBall d ρ) :=
    harm.continuousOn.mono hcl
  have hGi : Integrable (fun z => g (foldH z)) (circleUnif d ρ) := by
    rw [← Measure.restrict_eq_self_of_ae_mem (CoordReg.ae_mem_closedBall_circleUnif d hρ.le)]
    exact hGc.integrableOn_compact (isCompact_closedBall d ρ)
  rw [foldedCircle, integral_map measurable_foldH.aemeasurable (by
    rw [← foldedCircle]; exact hgi.aestronglyMeasurable)]
  have hG' := hGi.aestronglyMeasurable
  rw [K3.circleUnif_eq_circMeas_k3] at hG' ⊢
  rw [LQGDimension.Coupling.integral_circMeas_eq_circleAverage hG']
  exact (harm.mono (by rwa [abs_of_pos hρ])).circleAverage_eq

section Model

variable {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → FieldSample} {E' : Type*} [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ}

/-- The macroscopic part of the model field at a circle `μ`:
`X(bal μ) − X(ρ₀) + ∫ (α(−log‖·‖) + g) dμ`. -/
def circVal (α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type*} (X : Ω → FieldSample) (g : Ω → ℂ → ℝ)
    (ω : Ω) (μ : Measure ℂ) : ℝ :=
  X ω (K3.bal 0 r μ) - X ω ρ₀ + ∫ z, (α * -Real.log ‖z‖ + g ω z) ∂μ

open Classical in
/-- **The macroscopic data `F`**: `circVal` on the dyadic circles inside `ball 0 r`, `0`
elsewhere. -/
def macroF (α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type*} (X : Ω → FieldSample) (g : Ω → ℂ → ℝ)
    (ω : Ω) : FieldSample :=
  fun μ => if μ ∈ circSet r then circVal α r ρ₀ X g ω μ else 0

/-- Measurability into `FieldSample` (product σ-algebra), coordinatewise. -/
theorem measurable_fieldSample_of {β : Type*} [MeasurableSpace β] {f : β → FieldSample}
    (h : ∀ μ, Measurable fun b => f b μ) : Measurable f :=
  measurable_pi_iff.2 h

open Classical in
/-- **The local model field** built from local values `s` and macroscopic data `f`. -/
def locModel (γ L r : ℝ) (p : (LocIdx r → ℝ) × FieldSample) : FieldSample :=
  fun μ => if h : μ ∈ circSet r then p.1 ⟨μ, isLocalH_of_mem_circSet h⟩ + p.2 μ + L / γ else 0

theorem measurable_locModel (γ L r : ℝ) : Measurable (locModel γ L r) := by
  classical
  refine measurable_fieldSample_of fun μ => ?_
  unfold locModel
  by_cases h : μ ∈ circSet r
  · simp only [h, dite_true]
    exact (((measurable_pi_apply (⟨μ, isLocalH_of_mem_circSet h⟩ : LocIdx r)).comp
      measurable_fst).add
      ((measurable_pi_apply μ).comp measurable_snd)).add_const _
  · simp only [h, dite_false]
    exact measurable_const

theorem integrable_zoomPot_circ (hS : Setup γ α r ρ₀ P X Ξ g) (ω : Ω) {d : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hdr : ‖d‖ + ρ < r) :
    Integrable (fun z => α * -Real.log ‖z‖ + g ω z) (foldedCircle d ρ) :=
  ((CoordReg.integrable_log_norm_foldedCircle d ρ).neg.const_mul α).add
    (integral_foldedCircle_of_harm (hS.harm ω) hρ hdr).1

/-- **The model field agrees with the local model near `0`, for every `ω`.** -/
theorem agreeNear_zoomModel_locModel (hS : Setup γ α r ρ₀ P X Ξ g) (L : ℝ) (ω : Ω) :
    AgreeNear (zoomModel γ α L ρ₀ (X ω) (g ω))
      (locModel γ L r (localZ X r ω, macroF α r ρ₀ X g ω)) r := by
  classical
  intro n k z hz
  have hmem : foldedCircle (dyadicRoundC n z) (radius k) ∈ circSet r := ⟨n, k, z, hz, rfl⟩
  have hint := integrable_zoomPot_circ hS ω (radius_pos k) hz
  simp only [locModel, macroF, dif_pos hmem, if_pos hmem, localZ, K3.markovZ, circVal, zoomModel,
    ofFun, Pi.add_apply]
  rw [integral_add hint (integrable_const _), integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul]
  ring

theorem measurable_circVal (hS : Setup γ α r ρ₀ P X Ξ g) {μ : Measure ℂ} (hμ : μ ∈ circSet r) :
    Measurable[condSigma Ξ X r] fun ω => circVal α r ρ₀ X g ω μ := by
  obtain ⟨d, ρ, hρ, hdr, rfl⟩ := exists_of_mem_circSet hμ
  have hr := hS.hr
  have hnull := foldedCircle_compl_closedBall (d := d) hρ
  have hm : K3.bal 0 r (foldedCircle d ρ) Set.univ = ρ₀ Set.univ := by
    rw [K3.bal_univ hr hdr hnull, measure_univ, hS.hρ1]
  have hρB : ρ₀ (Metric.ball ((0 : ℝ) : ℂ) r) = 0 := by simpa using hS.hρB
  have hout : Measurable[K3.outsideSigma X 0 r]
      fun ω => X ω (K3.bal 0 r (foldedCircle d ρ)) - X ω ρ₀ :=
    K3.measurable_outsideSigma (K3.isAdmissibleH_bal hr hdr hnull) hS.hρ hm (K3.bal_ball hr) hρB
  have e : (fun ω => circVal α r ρ₀ X g ω (foldedCircle d ρ)) = fun ω =>
      (X ω (K3.bal 0 r (foldedCircle d ρ)) - X ω ρ₀) +
        (∫ z, α * -Real.log ‖z‖ ∂foldedCircle d ρ + g ω (foldH d)) := by
    funext ω
    have h2 := integral_foldedCircle_of_harm (hS.harm ω) hρ hdr
    have hl : Integrable (fun z => α * -Real.log ‖z‖) (foldedCircle d ρ) :=
      (CoordReg.integrable_log_norm_foldedCircle d ρ).neg.const_mul α
    simp only [circVal]
    rw [integral_add hl h2.1, h2.2]
  rw [e]
  have h1 : Measurable[condSigma Ξ X r]
      fun ω => X ω (K3.bal 0 r (foldedCircle d ρ)) - X ω ρ₀ := hout.mono le_sup_right le_rfl
  have h2 : Measurable[condSigma Ξ X r] fun ω => g ω (foldH d) := hS.gmeas _
  exact h1.add (measurable_const.add h2)

/-- **`F = macroF` is `condSigma`-measurable.** -/
theorem measurable_macroF (hS : Setup γ α r ρ₀ P X Ξ g) :
    Measurable[condSigma Ξ X r] (macroF α r ρ₀ X g) := by
  classical
  refine @measurable_fieldSample_of Ω (condSigma Ξ X r) _ fun μ => ?_
  unfold macroF
  by_cases h : μ ∈ circSet r
  · simp only [h, if_true]
    exact measurable_circVal hS h
  · simp only [h, if_false]
    exact measurable_const

end Model

end D3Plus
end QuantumZipper
