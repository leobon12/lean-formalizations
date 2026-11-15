/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JointKernelProof

/-!
# GW2's (R1) with the conditioning σ-algebra exposed

Packet PROVE-GW2-KMODELS. `GW2JointKernel.exists_jointKernel_r1` (PROVE-T14-TIP10) proves (R1) — the field `Hc` read
in the joint chart of the counterflow stopped at own time `s` has, given the counterflow record at `s`, the Gaussian
characteristic functional of the joint word — with the conditioning σ-algebra `𝒢` quantified existentially, although
its proof uses `𝒢 = σ(recOf s (cfE s W ζ))`, the σ-algebra of the regularized counterflow record. The retained-kernel
transfer (`GW2KModRetained`) needs that exact σ-algebra (it is the first factor of GW2's stage-start σ-algebra
`rootSigma`). **`exists_jointKernel_r1_rec`** is the same theorem with that σ-algebra in the statement; its proof is
the landed proof of `exists_jointKernel_r1` with only the final packaging changed (the landed file is not ours to
edit; replacing the landed statement by this one would make this copy unnecessary).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2JointKernel

open Restart Exist.StagedLaw Sec7.StripSysField Supp8.GB6

/-- **(R1) at a counterflow stop, with the record σ-algebra exposed.** `exists_jointKernel_r1` with
`𝒢 = σ(recOf s (cfE s W ζ))`. -/
theorem exists_jointKernel_r1_rec {κ : ℝ} (hκ : 0 < κ) (a₀ : ℝ) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
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
    ∃ (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[MeasurableSpace.comap (fun ω => recOf (s : ℝ≥0∞) (cfE s W ζ ω)) inferInstance] M ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (s : ℝ≥0∞) (cfE s W ζ ω)) inferInstance] β ∧
      (∀ ω, (β ω).IsSorted) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) |
          MeasurableSpace.comap (fun ω => recOf (s : ℝ≥0∞) (cfE s W ζ ω)) inferInstance] ω = gaussCF (β ω) φ) ∧
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
  refine ⟨M, β, hM, hβ, fun ω => isSorted_jointWordOfRec a₀ κ c' (rec ω), fun φ => ?_, hev⟩
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

end InteractingSLE.Theorem14.GW2JointKernel
