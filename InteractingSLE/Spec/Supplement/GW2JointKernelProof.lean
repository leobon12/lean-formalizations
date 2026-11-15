/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JointKernelProofWord
import InteractingSLE.Spec.Supplement.GW2JointKernelProofChart
import InteractingSLE.Spec.Exist.StagedLaw3Adm
import InteractingSLE.Spec.Exist.StagedLaw3Path
import InteractingSLE.Spec.Exist.StagedLaw4
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Restart.ChartMeasFlow
import InteractingSLE.Spec.Sec2.AssemblyTheorem

/-!
# GW2's pre-contact kernel at a counterflow stop: the (R1) half, with the explicit joint-chart word

Packet PROVE-T14-TIP10. Supplement GB9 (p. 524): "the conditional field has a finite-piece mean" in the joint chart of
the counterflow stopped at own time `s`. The conditioning is the counterflow's own: given the counterflow history up
to `s`, its parameter field `h′` read in its own Loewner chart is the GFF of the counterflow's stop word
(`Exist.StagedLaw.ae_condExp_recField_of_admissible`, the single-stage law at `16/κ`), and the flow field `h` read in
the joint chart is that field returned through `R(z) = −1/z` (`GW2JointKernelProofChart`). So the conditional word is
the counterflow's stop word, returned (`GW2JointKernelProofWord`):

`jointWord κ c′ s w = retWord (−πχ(κ) + 2πχ(16/κ)) χ(16/κ) (stopWord (16/κ) (c′, 0, recOf s (w, ⊤)))`.

## Main results

* `jointWordOfRec`, **`jointWord`**: the explicit word of the field in the joint chart;
* **`exists_jointKernel_r1`**: in the setting of `GW2JointKernelStatement`, with `𝒢` the σ-algebra of the
  counterflow record at `s`, the event `M` of an interior counterflow tip read from the record, and
  `β = jointWordOfRec ∘ record`: `β` is sorted, (R1) holds on `M`, and almost surely `M = {γ(s) ∈ ℍ}` and
  `β = jointWord κ c′ s W`;
* **`GW2JointDetStatement`** (named): the (Det) clause of the pre-contact kernel for this explicit word, the part of
  GB9's kernel that needs the two-curve conditioning and flow-line locality;
* **`gw2JointKernelStatement_of_det`**: `GW2JointDetStatement → GW2JointKernelStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2JointKernel

open Restart Exist.StagedLaw Sec7.StripSysField Supp8.GB6

/-! ### The joint-chart word -/

section Word

/-- The constant of the return: `−πχ(κ) + 2πχ(16/κ)`. -/
def retA (κ : ℝ) : ℝ := -(Real.pi * QuantumZipper.chiC κ) + 2 * Real.pi * QuantumZipper.chiC (16 / κ)

/-- The lift coefficient of the return: `χ(16/κ)`. -/
def retL (κ : ℝ) : ℝ := QuantumZipper.chiC (16 / κ)

/-- **The joint-chart word of a counterflow record** for the field read in the joint chart with offset `a₀`: the
counterflow's stop word (parameter `16/κ`, angle `0`, data word `c′`), returned through `R`. -/
def jointWordOfRec (a₀ κ : ℝ) (c' : BoundaryWord) (r : RecData) : BoundaryWord :=
  retWord (retA κ + a₀) (retL κ) (stopWord (16 / κ) (c', 0, r))

/-- **The joint-chart word of a counterflow driver `w` stopped at own time `s`** (offset `a₀`). -/
def jointWord (a₀ κ : ℝ) (c' : BoundaryWord) (s : ℝ≥0) (w : ℝ≥0 → ℝ) : BoundaryWord :=
  jointWordOfRec a₀ κ c' (recOf (s : ℝ≥0∞) (w, ⊤))

theorem measurable_jointWordOfRec (a₀ κ : ℝ) (c' : BoundaryWord) : Measurable (jointWordOfRec a₀ κ c') :=
  (measurable_retWord _ _).comp ((measurable_stopWord (16 / κ)).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id)))

theorem isSorted_jointWordOfRec (a₀ κ : ℝ) (c' : BoundaryWord) (r : RecData) :
    (jointWordOfRec a₀ κ c' r).IsSorted :=
  isSorted_retWord (isSorted_stopWord _ _) _ _

end Word

/-! ### Conditional expectations agreeing on an event -/

section CondExp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- If two integrable functions agree almost surely on an `m`-event `M`, so do their conditional expectations. -/
theorem ae_condExp_eq_of_ae_eq_on {m : MeasurableSpace Ω} {M : Set Ω} (hM : MeasurableSet[m] M)
    {f g : Ω → ℂ} (hf : Integrable f P) (hg : Integrable g P) (hfg : ∀ᵐ ω ∂P, ω ∈ M → f ω = g ω) :
    ∀ᵐ ω ∂P, ω ∈ M → P[f | m] ω = P[g | m] ω := by
  have h1 := condExp_indicator (m := m) hf hM
  have h2 := condExp_indicator (m := m) hg hM
  have h3 : P[M.indicator f | m] =ᵐ[P] P[M.indicator g | m] := by
    refine condExp_congr_ae (hfg.mono fun ω h => ?_)
    by_cases hω : ω ∈ M
    · rw [indicator_of_mem hω, indicator_of_mem hω, h hω]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]
  filter_upwards [h1, h2, h3] with ω e1 e2 e3 hω
  have := e1.symm.trans (e3.trans e2)
  rwa [indicator_of_mem hω, indicator_of_mem hω] at this

end CondExp

/-! ### The regularized counterflow driver -/

section Drv

variable {Ω : Type*}

/-- The counterflow driver killed at its lifetime. -/
def cfKW (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ := if (t : ℝ≥0∞) < ζ ω then W t ω else 0

/-- The regularized counterflow driver (`StagedReg.regularize` for the own time `s`): regular at every sample. -/
def cfE (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  StagedReg.regularize (s : ℝ≥0∞) (fun t => cfKW W ζ t ω, ζ ω)

theorem cfE_snd (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : (cfE s W ζ ω).2 = ζ ω :=
  StagedReg.regularize_snd _ _

/-- On a sample with infinite lifetime and a continuous driver from `0`, the regularized driver is the driver. -/
theorem cfE_eq (s : ℝ≥0) {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ ω = ⊤) (hW0 : W 0 ω = 0)
    (hWc : Continuous fun t => W t ω) : cfE s W ζ ω = (fun t => W t ω, ⊤) := by
  have hK : (fun t => cfKW W ζ t ω) = fun t => W t ω := by
    funext t
    simp only [cfKW, hζ, ENNReal.coe_lt_top, ↓reduceIte]
  refine Prod.ext (funext fun t => ?_) ?_
  · change (StagedReg.regularize (s : ℝ≥0∞) (fun t => cfKW W ζ t ω, ζ ω)).1 t = W t ω
    rw [hK, hζ, StagedReg.regularize_eq_of_lt _ hW0 hWc.continuousOn (ENNReal.coe_lt_top)]
  · rw [cfE_snd, hζ]

end Drv

/-! ### (R1) of the pre-contact kernel -/

section R1

/-- **(R1) of GB9's pre-contact kernel at a counterflow stop, with the explicit word.** In the setting of
`GW2JointKernelStatement` (the counterflow part of its binders: the field `h`, its counterflow parameter field `h′`
with data `(b′, J′)` represented by the word `c′`, the centred counterflow driver `W` with infinite lifetime and
generating trace `γ`; the own time `s`; any measurable version `Hc` of `h` read in the joint chart on `{γ(s) ∈ ℍ}`):
with `𝒢` the σ-algebra of the regularized counterflow record at `s`, `M` the event "the tip read from the record is
interior" and `β = jointWordOfRec κ c′ ∘ record`,

* `M ∈ 𝒢`, `β` is `𝒢`-measurable and sorted;
* **(R1)**: for every test function `φ`, almost surely on `M`, `E[exp(i (Hc, φ)) | 𝒢] = gaussCF β φ`;
* almost surely, `M` is the interior-tip event `{γ(s) ∈ ℍ}` and `β = jointWord κ c′ s W`. -/
theorem exists_jointKernel_r1 {κ : ℝ} (hκ : 0 < κ) (a₀ : ℝ) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {h h' : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {γ : Ω → ℝ≥0 → ℂ} (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (s : ℝ≥0) {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 a₀ (QuantumZipper.chiC κ) (h ω) (Hc ω))
    {c' : BoundaryWord} (hc'b : ∀ y ∉ J', c'.fn y = b' y) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧ (∀ ω, (β ω).IsSorted) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ) ∧
      ∀ᵐ ω ∂P, (γ ω s ∈ H ↔ ω ∈ M) ∧ β ω = jointWord a₀ κ c' s (fun t => W t ω) := by
  classical
  have hκ' : 0 < 16 / κ := by positivity
  -- the counterflow driver: measurability and the good event
  have hcf' := hcf
  obtain ⟨h'', 𝓕, VL, VR, B, htr', hC⟩ := hcf'
  have hWa : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hζm : Measurable ζ := Sec2.Assembly.measurable_lifetime hWa
  have hKm : ∀ t, Measurable (cfKW W ζ t) := fun t => Restart.measurable_ite_of_adaptedBefore hWa t
  set E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := cfE s W ζ with hEdef
  have hEm : Measurable E :=
    (StagedReg.measurable_regularize _).comp ((measurable_pi_iff.2 hKm).prodMk hζm)
  have hEreg : ∀ ω, Exist.Staged.IsRegularDriver (E ω) := fun ω => StagedReg.isRegularDriver_regularize _ _
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hcf
  have hgood : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous (fun t => W t ω) ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [hζ, hdrv, hγ] with ω hζω hdω hγω
    refine ⟨hζω, hdω.1, ?_, hγω⟩
    have hc := hdω.2
    rw [hζω] at hc
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  -- the flow-line driver of the word `c'`, with the regularized driver
  have hfl₁ : IsFlowLineDriver (16 / κ) c'.fn c'.jumps 0 P h' W ζ := by
    have h := (isFlowLineDriver_congr_of_eqOn hb' c'.isPiecewiseConstantBoundaryData J' hc'b
      (θ := 0) (P := P) (h := h') (W := W) (ζ := ζ)).2 hcf
    exact h
  have hfl₂ : IsFlowLineDriver (16 / κ) c'.fn c'.jumps 0 P h' (fun t ω => (E ω).1 t) (fun ω => (E ω).2) := by
    have e : (fun ω => (E ω).2) = ζ := funext fun ω => cfE_snd s W ζ ω
    rw [e]
    refine StagedReg.isFlowLineDriver_congr_ae hfl₁
      (fun t => (measurable_pi_apply t).comp (measurable_fst.comp hEm)) ?_
    filter_upwards [hgood] with ω hω
    have hEω : E ω = (fun t => W t ω, ⊤) := cfE_eq s hω.1 hω.2.1 hω.2.2.1
    rw [hEω]
    exact ⟨rfl, fun t _ => rfl⟩
  -- the seed of the counterflow word is admissible (its lifetime is infinite)
  have hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0)
      (flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0) 0 (flowLineXL c'.fn c'.jumps 0) (flowLineXR c'.fn c'.jumps 0) := by
    intro hthr
    obtain ⟨_h₀, _𝓕₀, _VL₀, _VR₀, _B₀, _ht₀, hC'⟩ := hfl₁
    have h0 := IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC'.1 hthr
    have hF : ∀ᵐ _ω ∂P, False := by
      filter_upwards [h0, hζ] with ω h1 h2
      rw [h1] at h2
      exact ENNReal.zero_ne_top h2
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hF
    exact IsProbabilityMeasure.ne_zero P hF
  -- the record, the σ-algebra, the event and the word
  set rec : Ω → RecData := fun ω => recOf (s : ℝ≥0∞) (E ω) with hrecdef
  have hrecm : Measurable rec := measurable_recOf hEm hEreg _
  let 𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ} := ⟨MeasurableSpace.comap rec inferInstance, hrecm.comap_le⟩
  set TS : Set RecData := {r | LP.traceAt s (fun t : ℝ≥0 => rdrv r t) ∈ H} with hTS
  have hTSm : MeasurableSet TS :=
    ((LP.measurable_traceAt s).comp (measurable_pi_iff.2 fun t => measurable_rdrv_apply (t : ℝ)))
      QuantumZipper.isOpen_H.measurableSet
  set M : Set Ω := rec ⁻¹' TS with hMdef
  set β : Ω → BoundaryWord := fun ω => jointWordOfRec a₀ κ c' (rec ω) with hβdef
  have hM : MeasurableSet[𝒢.1] M := ⟨TS, hTSm, rfl⟩
  have hβ : Measurable[𝒢.1] β := (measurable_jointWordOfRec a₀ κ c').comp (comap_measurable rec)
  -- the record on a good sample
  have hptw : ∀ ω, ζ ω = ⊤ → W 0 ω = 0 → Continuous (fun t => W t ω) →
      rec ω = recOf (s : ℝ≥0∞) (fun t => W t ω, ⊤) ∧
      recChart (rec ω) = Chart.id.loewner (fun r : ℝ => W r.toNNReal ω) s ∧
      LP.traceAt s (fun t : ℝ≥0 => rdrv (rec ω) t) = LP.traceAt s (fun t => W t ω) := by
    intro ω hζω hW0 hWc
    have hEω : E ω = (fun t => W t ω, ⊤) := cfE_eq s hζω hW0 hWc
    have hrec : rec ω = recOf (s : ℝ≥0∞) (fun t => W t ω, ⊤) := by
      change recOf (s : ℝ≥0∞) (E ω) = _
      rw [hEω]
    have hreg : Exist.Staged.IsRegularDriver ((fun t => W t ω, ⊤) : (ℝ≥0 → ℝ) × ℝ≥0∞) := hEω ▸ hEreg ω
    have hfin : min (s : ℝ≥0∞) ⊤ ≠ ⊤ := by simp
    have hg := isDrvGood_of_continuousOn_le hreg hfin hWc.continuousOn
    have hrt : rtime (recOf (s : ℝ≥0∞) (fun t => W t ω, ⊤)) = s := by
      rw [rtime_recOf_coe]
      simp
    have hrd : ∀ x : ℝ, x ≤ s → rdrv (recOf (s : ℝ≥0∞) (fun t => W t ω, ⊤)) x = W x.toNNReal ω := by
      intro x hx
      exact rdrv_recOf_eq hreg hg hfin (by rw [hrt]; exact hx)
    refine ⟨hrec, ?_, ?_⟩
    · rw [hrec, recChart_eq, hrt]
      refine LocalExt.id_loewner_congr (t' := (s : ℝ) + 1) (continuous_rdrv _).continuousOn
        (hWc.comp continuous_real_toNNReal).continuousOn s.coe_nonneg (by linarith) fun x hx => ?_
      exact hrd x hx.2
    · rw [hrec]
      refine LP.traceAt_congr fun r hr => ?_
      rw [hrd r (by exact_mod_cast hr), Real.toNNReal_coe]
  -- the counterflow parameter field is measurable; the record field
  have hh'm : Measurable h' := by
    have hℓ := Chart.locallyIntegrableOn_of_continuousOn Chart.continuousOn_infinitySourceChart_lift
    have e : h' = fun ω => Chart.chartTransport Chart.isConformal_infinitySourceChart (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) :=
      funext fun ω => (hT ω).eq_chartTransport Chart.isConformal_infinitySourceChart hℓ
    rw [e]
    exact (Chart.measurable_chartTransport _ _ _ _).comp hhm
  obtain ⟨Y, hYdef⟩ : ∃ Y : Ω → DistOn upperHalfPlaneOpens, Y = fun ω => recField (16 / κ) (rec ω) (h' ω) :=
    ⟨_, rfl⟩
  have hYm : Measurable Y := by
    have h := (measurable_recField (16 / κ)).comp (hrecm.prodMk hh'm)
    rw [hYdef]
    exact h
  -- on a good sample with an interior tip, the joint-chart field is the returned record field
  have hident : ∀ᵐ ω ∂P, γ ω s ∈ H → Hc ω = returnField (retA κ + a₀) (retL κ) (Y ω) := by
    filter_upwards [hgood, hHc] with ω hω hHcω hsH
    obtain ⟨hζω, hW0, hWc, -⟩ := hω
    obtain ⟨-, hchart, -⟩ := hptw ω hζω hW0 hWc
    have h₂ : IsChartTransport (Chart.id.loewner (fun r : ℝ => W r.toNNReal ω) s) 1 0
        (QuantumZipper.chiC (16 / κ)) (h' ω) (Y ω) := by
      have h := isChartTransport_recField (16 / κ) (rec ω) (h' ω)
      rw [hchart] at h
      rw [hYdef]
      exact h
    have hw0 : (fun r : ℝ => W r.toNNReal ω) 0 = 0 := by simp only [Real.toNNReal_zero, hW0]
    exact eq_returnField_of_isChartTransport hκ (hWc.comp continuous_real_toNNReal) hw0 s.coe_nonneg a₀
      (hT ω) h₂ (hHcω hsH)
  -- the event `M` is the interior-tip event, and `β` the intrinsic word
  have hev : ∀ᵐ ω ∂P, (γ ω s ∈ H ↔ ω ∈ M) ∧ β ω = jointWord a₀ κ c' s (fun t => W t ω) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hζω, hW0, hWc, hγω⟩ := hω
    obtain ⟨hrec, -, htr⟩ := hptw ω hζω hW0 hWc
    have htip : LP.traceAt s (fun t => W t ω) = γ ω s :=
      LP.traceAt_eq_of_isGeneratingTrace hγω hWc.continuousOn hW0 ENNReal.coe_lt_top
    refine ⟨?_, ?_⟩
    · change γ ω s ∈ H ↔ LP.traceAt s (fun t : ℝ≥0 => rdrv (rec ω) t) ∈ H
      rw [htr, htip]
    · change jointWordOfRec a₀ κ c' (rec ω) = jointWordOfRec a₀ κ c' (recOf (s : ℝ≥0∞) (fun t => W t ω, ⊤))
      rw [hrec]
  refine ⟨𝒢, M, β, hM, hβ, fun ω => isSorted_jointWordOfRec a₀ κ c' (rec ω), fun φ => ?_, hev⟩
  -- (R1)
  set φ' : TestOn upperHalfPlaneOpens := Chart.pushTest isConformal_infinityReturnChart φ with hφ'
  set C : ℂ := Complex.exp (Complex.I *
    (((retA κ + a₀) * (∫ w, φ w) + retL κ * ∫ w, infinitySourceChart.2.2 w * φ w : ℝ) : ℂ)) with hC
  have hX : ∀ ω, Complex.exp (Complex.I * (returnField (retA κ + a₀) (retL κ) (Y ω) φ : ℂ)) =
      C * Complex.exp (Complex.I * (Y ω (-φ') : ℂ)) := by
    intro ω
    rw [hC, returnField_apply, map_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hint₁ : Integrable (fun ω => Complex.exp (Complex.I * (Hc ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hHcm)
  have hint₂ : Integrable (fun ω => Complex.exp (Complex.I * (returnField (retA κ + a₀) (retL κ) (Y ω) φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp
      ((measurable_returnField (retA κ + a₀) (retL κ)).comp hYm))
  have h1 := ae_condExp_eq_of_ae_eq_on (P := P) hM hint₁ hint₂ (by
    filter_upwards [hident, hev] with ω hid hevω hωM
    rw [hid (hevω.1.2 hωM)])
  have h2 : P[fun ω => Complex.exp (Complex.I * (returnField (retA κ + a₀) (retL κ) (Y ω) φ : ℂ)) | 𝒢.1] =ᵐ[P]
      C • P[fun ω => Complex.exp (Complex.I * (Y ω (-φ') : ℂ)) | 𝒢.1] := by
    have e : (fun ω => Complex.exp (Complex.I * (returnField (retA κ + a₀) (retL κ) (Y ω) φ : ℂ))) =
        C • fun ω => Complex.exp (Complex.I * (Y ω (-φ') : ℂ)) := by
      funext ω
      rw [hX ω, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact condExp_smul C _ _
  have h3 := ae_condExp_recField_of_admissible hκ' c' 0 (s : ℝ≥0∞) P h' E hEm hEreg hfl₂ hseed (-φ')
  filter_upwards [h1, h2, h3] with ω e1 e2 e3 hωM
  rw [e1 hωM, e2, Pi.smul_apply, smul_eq_mul]
  have hne : min (s : ℝ≥0∞) (E ω).2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  rw [hYdef]
  change C * P[fun ω' => Complex.exp (Complex.I * (recField (16 / κ) (recOf (s : ℝ≥0∞) (E ω')) (h' ω') (-φ') : ℂ)) |
    MeasurableSpace.comap (fun ω' => recOf (s : ℝ≥0∞) (E ω')) inferInstance] ω = _
  rw [e3 hne]
  exact (gaussCF_retWord (isSorted_stopWord _ _) (retA κ + a₀) (retL κ) φ).symm

end R1

/-! ### The (Det) clause and the reduction -/

/-- **Named input: the (Det) clause of GB9's pre-contact kernel at a counterflow stop, for the explicit joint-chart
word** (supplement p. 525: "Before a new flow prefix first meets the retained counterflow, the conditional exploration
has its full canonical word in this joint chart … This identifies the full field–path kernel"). Binders of
`GW2JointKernelStatement` verbatim, and a word `c′` representing the counterflow data `(b′, J′)`. Almost surely on the
interior-tip event `γ(s) ∈ ℍ`, with `β = jointWord κ c′ s W` (the word of the conditional field in the joint chart,
`exists_jointKernel_r1`):

* the canonical driver code `F (β, Hc)` of the joint-chart field is good, and
* **before the flow's first contact** with the physical counterflow prefix `−1/γ([0, s])`, the canonical flow line
  of the joint-chart field generates the joint-chart images `ψ(K^α_t)` of the physical flow hulls in the relative
  clock.

This is the part of `GW2JointKernelStatement` that is not proved here: it needs the conditional law of the field given
**both** the counterflow history and the flow prefix in the joint chart at a general angle `θ` (the cross-conditioning
law `Sec5.CrossCond.ae_condExp_cfGlue` and its image-word martingale clause `CrossCond.Word49.imageWord49FiltCStatement`
are proved for the flow line of angle `π/2` relative to the counterflow only, i.e. `cfField κ h = h − (π/2)χ`), and the
identification of the field-determined flow line with the flow line of the conditional field up to first contact
(flow-line locality, `RLC.FlowLocalityStatement`), through the stopped K2 (`Restart.StoppedK2`).

**Warning (normalization defect, PROVE-T14-TIP10).** `GW2JointKernelStatement` reads `h` in `jointChart` with the
coefficients `1, 0, χ`, but the chain-rule lift of `jointChart = R ∘ f_s ∘ R` is `arg ψ′ − 2π` (it is the constant
`−2π` at `s = 0`, `jointChart_zero_lift`), so its `Hc` is the specification's joint-chart field minus `2πχ`. The
canonical flow line of angle `θ` of `Hc` is then the specification's flow line of angle `θ − 2π`, whose seed weights
differ by `±(4 − κ)` from those of `α`; so this clause (and `GW2JointKernelStatement`) is believed false. The corrected
forms are `GW2JointDetCStatement` and `GW2JointKernelCStatement` (`GW2JointKernelProofC`, offset `a₀ = 2πχ`). -/
def GW2JointDetStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 0 (QuantumZipper.chiC κ) (h ω) (Hc ω)) →
    ∀ F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞,
      IsCanonicalDriverCode κ θ F →
    ∀ c' : BoundaryWord, c'.jumps = J' → (∀ y ∉ J', c'.fn y = b' y) →
      ∀ᵐ ω ∂P, γ ω s ∈ H →
        IsGoodDrvCode (F (jointWord 0 κ c' s (fun t => W t ω), Hc ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => (α ω t : OnePoint ℂ))
            ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (jointWord 0 κ c' s (fun t => W t ω), Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t) =
            relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t

/-- **The pre-contact kernel from its (Det) clause**: `exists_jointKernel_r1` supplies `𝒢`, `M`, `β` and (R1); the
named (Det) clause, for the explicit word `β = jointWord κ c′ s W`, supplies the rest. -/
theorem gw2JointKernelStatement_of_det (hD : GW2JointDetStatement.{u}) : GW2JointKernelStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα s Hc
    hHcm hHc F hF
  obtain ⟨c', hc'J, hc'b⟩ := BoundaryWord.exists_fn_eq hb'
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hreg.mono fun ω hω => hω.1
  have hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := hreg.mono fun ω hω => hω.2.1
  obtain ⟨𝒢, M, β, hM, hβ, hsort, hR1, hev⟩ :=
    exists_jointKernel_r1 hκ 0 hh.1 hb' hT hcf hζ hγ s hHcm hHc hc'b
  have hDω := hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα
    s Hc hHcm hHc F hF c' hc'J hc'b
  refine ⟨𝒢, M, β, hM, hβ, ?_, hR1, ?_⟩
  · filter_upwards [hev, hDω] with ω hevω hDω hωM
    refine ⟨hsort ω, ?_⟩
    rw [hevω.2]
    exact (hDω (hevω.1.2 hωM)).1
  · filter_upwards [hev, hDω] with ω hevω hDω hsH
    refine ⟨hevω.1.1 hsH, ?_⟩
    rw [hevω.2]
    exact (hDω hsH).2

end GW2JointKernel

end Theorem14

end InteractingSLE
