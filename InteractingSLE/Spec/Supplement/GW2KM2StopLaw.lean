/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Adm
import InteractingSLE.Spec.Supplement.GW2ScheduleCanon
import InteractingSLE.Spec.Exist.StagedLaw3Main

/-!
# The single-stage law at a stopping time

Packet PROVE-GW2-KMODELS2, part (II) (`planning/handoffs/PROVE-GW2-KMODELS.md` §4, "Design point for (II)"). In GW2's
retained stage experiment the canonical pieces switch at deterministic **physical** own times; read in the joint
chart of the counterflow they switch at **random** relative times, stopping times of the relative pieces (the physical
capacity clock is an adapted continuous increasing functional of the relative path). The canonical-space stage law
therefore needs the single-stage law (`Exist.StagedLaw.ae_condExp_recField_of_admissible`, deterministic stop `t`) at
a stopping time `T`, with the explicit word `stopWord` (computed pathwise from the record, so meaningful at records
taken at random times).

This file proves it, by the deterministic-time proof with `t` replaced by `T ω` (the announcing stops
`ρₙ = min T σₙ` are again stopping times of the driving filtration, and `{σₙ < T} ∈ 𝓓_{min T σₙ}` makes the record's
kill flag measurable for the announced history):

* `stopSeqR`, `isStoppingTime_stopSeqR`, `annSigmaR`, `measurableSet_forall_stopSeqR_lt`: the stops `min T σₙ` and
  their announced history;
* `ae_isGoodStopPath_all`: almost every path is good at every finite stop simultaneously;
* `ae_condExp_cexp_stopR`: the announced kernel at the stop `min T ζ`;
* `recVersionR`, `measurable_recVersionR`: an announced-history-measurable version of the record;
* **`ae_condExp_recField_of_admissible_stop`** (admissible seed), **`ae_condExp_recField_of_inadmissible_stop`**
  (inadmissible seed: the record is almost surely the zero record), **`ae_condExp_recField_stop`** (every seed): for an
  angle-`θ` flow-line coupling and a measurable stopping time `T` of its driving filtration, almost surely on
  `{min T ζ < ∞}` the conditional characteristic functional of the field read in the record chart, given the record
  `recOf T E`, is that of the Gaussian law of the stop word `stopWord κ (c, θ, recOf T E)`;
* `killedDriverSigma`, `isStoppingTime_of_killedDriverSigma`, **`ae_condExp_recField_stop_of_driver`**: the same for a
  flow-line driver (`IsFlowLineDriver`, coupling existential) and a random time decided by the killed driver alone —
  the form of `IsStopLaw` with the deterministic stop replaced by such a time.

R48: canonical-space probability for Theorem 1.4; no Theorem 1.2/1.3 input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2KM2

open QuantumZipper Exist Exist.StagedLaw Staged Restart LQGMetric

/-! ### The stops `min T σₙ` at a random time -/

/-- The stops `ρₙ = min T σₙ` at a random time `T`. -/
def stopSeqR {Ω : Type*} (T : Ω → ℝ≥0∞) (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 := stopSeq (T ω) σ n ω

theorem coe_stopSeqR {Ω : Type*} (T : Ω → ℝ≥0∞) (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    ((stopSeqR T σ n ω : ℝ≥0) : ℝ≥0∞) = min (T ω) (σ n ω : ℝ≥0∞) :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))

theorem isStoppingTime_stopSeqR {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {T : Ω → ℝ≥0∞}
    (hT : IsStoppingTime 𝓖 (T : Ω → WithTop ℝ≥0)) {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) (n : ℕ) :
    IsStoppingTime 𝓖 fun ω => (stopSeqR T σ n ω : WithTop ℝ≥0) := by
  have e : (fun ω => (stopSeqR T σ n ω : WithTop ℝ≥0)) =
      fun ω => min ((T : Ω → WithTop ℝ≥0) ω) (σ n ω : WithTop ℝ≥0) := by
    funext ω
    exact coe_stopSeqR T σ n ω
  rw [e]
  exact hT.min (hσ n)

theorem measurable_stopSeqR {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {T : Ω → ℝ≥0∞}
    (hT : IsStoppingTime 𝓖 (T : Ω → WithTop ℝ≥0)) {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) (n : ℕ) :
    Measurable[(isStoppingTime_stopSeqR hT hσ n).measurableSpace] (stopSeqR T σ n) := by
  have h : Measurable[(isStoppingTime_stopSeqR hT hσ n).measurableSpace]
      ((fun x : WithTop ℝ≥0 => x.untopD 0) ∘ (fun ω => (stopSeqR T σ n ω : WithTop ℝ≥0))) :=
    (WithTop.measurable_untopD (0 : ℝ≥0)).comp (isStoppingTime_stopSeqR hT hσ n).measurable
  have e : (fun x : WithTop ℝ≥0 => x.untopD 0) ∘ (fun ω => (stopSeqR T σ n ω : WithTop ℝ≥0)) =
      stopSeqR T σ n := by
    funext ω
    simp only [Function.comp_apply, WithTop.untopD_coe]
  rw [e] at h
  exact h

/-- The announced history `⋁ₙ 𝓓_{ρₙ}` of the stops `ρₙ = min T σₙ`. -/
abbrev annSigmaR {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {T : Ω → ℝ≥0∞}
    (hT : IsStoppingTime 𝓖 (T : Ω → WithTop ℝ≥0)) {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) : MeasurableSpace Ω :=
  ⨆ n, (isStoppingTime_stopSeqR hT hσ n).measurableSpace

theorem annSigmaR_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {T : Ω → ℝ≥0∞}
    (hT : IsStoppingTime 𝓖 (T : Ω → WithTop ℝ≥0)) {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) : annSigmaR hT hσ ≤ mΩ :=
  iSup_le fun n => (isStoppingTime_stopSeqR hT hσ n).measurableSpace_le

theorem le_annSigmaR {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {T : Ω → ℝ≥0∞}
    (hT : IsStoppingTime 𝓖 (T : Ω → WithTop ℝ≥0)) {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) (n : ℕ) :
    (isStoppingTime_stopSeqR hT hσ n).measurableSpace ≤ annSigmaR hT hσ :=
  le_iSup (fun n => (isStoppingTime_stopSeqR hT hσ n).measurableSpace) n

/-- **The event "every stop is before `T`" is in the announced history** (it is `⋂ₙ {σₙ < T}`, and
`{σₙ < T} ∈ 𝓓_{min T σₙ}`). -/
theorem measurableSet_forall_stopSeqR_lt {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {T : Ω → ℝ≥0∞} (hT : IsStoppingTime 𝓖 (T : Ω → WithTop ℝ≥0)) {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) :
    MeasurableSet[annSigmaR hT hσ] {ω | ∀ n, (stopSeqR T σ n ω : ℝ≥0∞) < T ω} := by
  have e : {ω | ∀ n, (stopSeqR T σ n ω : ℝ≥0∞) < T ω} =
      ⋂ n, {ω | (T : Ω → WithTop ℝ≥0) ω ≤ (σ n ω : WithTop ℝ≥0)}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, coe_stopSeqR]
    refine forall_congr' fun n => ?_
    rw [min_lt_iff, lt_self_iff_false, false_or]
    exact Iff.symm not_le
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.compl ?_
  have h := IsStoppingTime.measurableSet_stopping_time_le_min hT (hσ n)
  have hle : (hT.min (hσ n)).measurableSpace ≤ (isStoppingTime_stopSeqR hT hσ n).measurableSpace :=
    (hT.min (hσ n)).measurableSpace_mono (isStoppingTime_stopSeqR hT hσ n) fun ω =>
      (coe_stopSeqR T σ n ω).symm.le
  exact le_annSigmaR hT hσ n _ (hle _ h)

/-! ### Good paths at every finite stop -/

section Good

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
  {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}

/-- **Almost every path is good at every finite stop** (`ae_isGoodStopPath` with the stop inside the event). -/
theorem ae_isGoodStopPath_all (hκ : 0 < κ) (hreg : ∀ ω, IsRegularDriver (E ω))
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR Q 𝓕 (fun s ω => (E ω).1 s) VL VR B fun ω => (E ω).2)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0∞, min t (E ω).2 ≠ ⊤ →
      IsGoodStopPath κ xL xR ρL ρR t (E ω) (fun i s => VL i s ω) (fun j s => VR j s ω) (fun s => B s ω) := by
  filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ] with ω hp hthr t hfin
  have hgood : LocalExt.IsDrvGood (recHist (recOf t (E ω))) := by
    refine isDrvGood_recOf_of_leftLim (hreg ω) hfin fun T hT hζ => ?_
    obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthr T hT hζ
    exact ⟨w₀, (continuous_fst.tendsto _).comp hlim⟩
  have hpos : 0 < (E ω).2 := by
    refine pos_iff_ne_zero.2 fun h0 => hseed ?_
    exact hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0
  refine ⟨hp, fun T hT hζ => ?_, hreg ω, hgood, hfin, hpos⟩
  obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthr T hT hζ
  exact ⟨w₀, vL₀, vR₀, hlim⟩

end Good

/-! ### The kernel at the stop `min T ζ` -/

section Kernel

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
  {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {h' : Ω → DistOn upperHalfPlaneOpens}

/-- **The conditional law at the stop `min T ζ`, at a fixed test function** (`ae_condExp_cexp_stop` at a stopping
time `T`). Given the announced history `⋁ₙ 𝓓_{min T σₙ}`, on `{min T ζ < ∞}` every test function supported off the hull
at the stop has the Gaussian characteristic functional with the tested mean at the stop and the Green energy of the
remaining domain. -/
theorem ae_condExp_cexp_stopR (hκ : 0 < κ) (hreg : ∀ ω, IsRegularDriver (E ω))
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR Q 𝓕 (fun s ω => (E ω).1 s) VL VR B (fun ω => (E ω).2) h')
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hX : IsMeasurableKilledDriving (fun s ω => (E ω).1 s) VL VR fun ω => (E ω).2)
    {σ : ℕ → Ω → ℝ≥0} (hσ : Coupling.IsAnnouncingSeq (drivingFiltration Q hX) Q (fun ω => (E ω).2) σ)
    {T : Ω → ℝ≥0∞} (hT : IsStoppingTime (drivingFiltration Q hX) (T : Ω → WithTop ℝ≥0))
    {ρLp ρRp xLp xRp : ℕ → ℝ} (hρL : ∀ i : Fin nL, ρLp i = ρL i) (hρR : ∀ j : Fin nR, ρRp j = ρR j)
    (hxL : ∀ i : Fin nL, xLp i = xL i) (hxR : ∀ j : Fin nR, xRp j = xR j) (θc : ℝ)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂Q, min (T ω) (E ω).2 ≠ ⊤ → tsupport ψ ⊆ H \ stopHull (recOf (T ω) (E ω)) →
      Q[fun ω' => Complex.exp (Complex.I * (h' ω' ψ : ℂ)) | annSigmaR hT hσ.1] ω =
        Complex.exp (Complex.I * ((∫ z, stopMean κ nL nR xLp xRp ρLp ρRp θc (recOf (T ω) (E ω)) z * ψ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (H \ stopHull (recOf (T ω) (E ω))) ψ ψ : ℝ) : ℂ)) := by
  obtain ⟨u₀, hu₀⟩ := WholeField.exists_bhe κ ρL ρR xL xR
  have hρ := isStoppingTime_stopSeqR hT hσ.1
  have hρm : ∀ ω, Monotone fun n => stopSeqR T σ n ω := fun ω => monotone_stopSeq (T ω) hσ.2.1 ω
  have hρζ : ∀ n, ∀ᵐ ω ∂Q, (stopSeqR T σ n ω : ℝ≥0∞) < (E ω).2 := fun n =>
    (hσ.2.2.1 n).mono fun ω hω => lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le (T ω) σ n ω)) hω
  obtain ⟨A, 𝒢, -, hAK, -, hker⟩ := WholeField.exists_announced_kernel_history hC hκ hu₀ hX hρ hρm hρζ
  filter_upwards [hker ψ, ae_all_iff.2 hAK, ae_isGoodStopPath_all hκ hreg hC.1 hseed, hσ.2.2.2,
    ae_all_iff.2 hσ.2.2.1] with ω hk hA hgood hann hlt hfin hsupp
  have hg := hgood (T ω) hfin
  obtain ⟨hle, hlim⟩ := tendsto_stopSeq (σ := fun n => σ n ω) (hσ.2.1 ω) hlt hann hfin
  have hsζ : ∀ n, (stopSeqR T σ n ω : ℝ≥0∞) < (E ω).2 := fun n =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le (T ω) σ n ω)) (hlt n)
  have hdisjK : Disjoint (tsupport ψ) (stopHull (recOf (T ω) (E ω))) :=
    Set.disjoint_left.2 fun z hz hK => (hsupp hz).2 hK
  have hdisj : ∀ n, Disjoint (tsupport ψ) (A n ω) := by
    intro n
    rw [hA n, hg.fwdHull_eq (s := stopSeqR T σ n ω) (hle n) (hsζ n)]
    refine hdisjK.mono_right (fwdHull_subset_of_le ?_)
    rw [rtime_recOf_coe]
    exact_mod_cast hle n
  obtain ⟨h1, h2, -, h4⟩ := hk hdisj
  have hmean := hg.tendsto_integral_couplingMean (s := fun n => stopSeqR T σ n ω) hρL hρR hxL hxR θc hsζ hle hlim
    ψ hsupp
  have hm : (Q[fun ω' => WholeField.centredField h' u₀ ω' ψ | ⨆ n, 𝒢 n]) ω + ∫ z, u₀ z * ψ z =
      ∫ z, stopMean κ nL nR xLp xRp ρLp ρRp θc (recOf (T ω) (E ω)) z * ψ z := by
    refine tendsto_nhds_unique ((h1.add_const (∫ z, u₀ z * ψ z)).congr fun n => ?_) hmean
    simp only [WholeField.testedFrozenMean, sub_add_cancel]
  have hvar := hg.tendsto_zeroGFFTestCov (s := fun n => stopSeqR T σ n ω) hsζ hle hlim ψ hdisjK
  have hv : (⨅ n, zeroGFFTestCov (H \ A n ω) ψ ψ) =
      zeroGFFTestCov (H \ stopHull (recOf (T ω) (E ω))) ψ ψ := by
    refine tendsto_nhds_unique h2 (hvar.congr fun n => ?_)
    rw [hA n]
  rw [h4, hm, hv]

end Kernel

/-! ### The version of the record read from the announced history -/

section Version

variable {Ω : Type*} {nL nR : ℕ}

/-- **The version of the record at the random stop**, read from the announced history. -/
def recVersionR (T : Ω → ℝ≥0∞) (ρ : ℕ → Ω → ℝ≥0) (K : ℕ → Ω → LocalExt.DrivingHist nL nR) (ω : Ω) : RecData :=
  recVersion (T ω) ρ K ω

theorem measurable_recVersionR [MeasurableSpace Ω] {T : Ω → ℝ≥0∞} {ρ : ℕ → Ω → ℝ≥0}
    {K : ℕ → Ω → LocalExt.DrivingHist nL nR} (hρ : ∀ n, Measurable (ρ n)) (hK : ∀ n, Measurable (K n))
    (hS : MeasurableSet {ω | ∀ n, (ρ n ω : ℝ≥0∞) < T ω}) :
    Measurable (recVersionR T ρ K) := by
  classical
  have hρ' : ∀ n, Measurable fun ω => (ρ n ω : ℝ≥0∞) := fun n => measurable_coe_nnreal_ennreal.comp (hρ n)
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => ?_) (Measurable.prodMk ?_ ?_)
  · exact Measurable.limsup fun n =>
      measurable_fst.comp ((measurable_pi_apply q.toNNRat).comp (measurable_snd.comp (hK n)))
  · exact Measurable.iSup hρ'
  · refine measurable_to_countable' fun b => ?_
    cases b
    · convert hS.compl using 1
      ext ω
      simp
    · convert hS using 1
      ext ω
      simp

end Version

/-! ### The single-stage law at a stopping time -/

section Main

/-- **The single-stage law at a stopping time, admissible seed.** Let `E` be the (regular) driver of an angle-`θ`
flow-line coupling of the field `g` with datum `c` (`h′ = g + θχ`, the coupling `hC`), with an admissible seed, and let
`T` be a measurable stopping time of the coupling's driving filtration. Then almost surely on `{min T ζ < ∞}`, the
conditional characteristic functional of the field read in the record chart, given the record `recOf T E`, is that of
the Gaussian law of the stop word `stopWord κ (c, θ, recOf T E)`. (`ae_condExp_recField_of_admissible` is the case of
a deterministic `T`.) -/
theorem ae_condExp_recField_of_admissible_stop {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (g : Ω → DistOn upperHalfPlaneOpens) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hE : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω)) {h' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (g ω) (h' ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) Q 𝓕 (fun s ω => (E ω).1 s) VL VR B
      (fun ω => (E ω).2) h')
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))
    (hX : IsMeasurableKilledDriving (fun s ω => (E ω).1 s) VL VR fun ω => (E ω).2)
    {T : Ω → ℝ≥0∞} (hTm : Measurable T) (hT : IsStoppingTime (drivingFiltration Q hX) (T : Ω → WithTop ℝ≥0))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂Q, min (T ω) (E ω).2 ≠ ⊤ →
      Q[fun ω' => Complex.exp (Complex.I * (recField κ (recOf (T ω') (E ω')) (g ω') φ : ℂ)) |
          MeasurableSpace.comap (fun ω' => recOf (T ω') (E ω')) inferInstance] ω =
        gaussCF (stopWord κ (c, θ, recOf (T ω) (E ω))) φ := by
  classical
  set R : Ω → RecData := fun ω => recOf (T ω) (E ω) with hRdef
  have hRm : Measurable R := GW2Schedule.measurable_recOf_joint hE hreg hTm
  -- the announcing sequence and the stops
  have : (drivingFiltration Q hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := WholeField.exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration Q hX) (B := B)
    (κ := κ) (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0)
    (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hC.1.2.2.2.2 (hC.1.ae_tendsto_threshold hκ) hseed
  have hρ := isStoppingTime_stopSeqR hT hσ.1
  have h𝓗 : annSigmaR hT hσ.1 ≤ mΩ := annSigmaR_le hT hσ.1
  -- the version of the record
  have hKex : ∀ n, ∃ K : Ω → LocalExt.DrivingHist (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0),
      Measurable[(hρ n).measurableSpace] K ∧
      ∀ ω, IsIntegratedSLEPath κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
          (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) (fun s => (E ω).1 s)
          (fun i s => VL i s ω) (fun j s => VR j s ω) (fun s => B s ω) (E ω).2 →
        (stopSeqR T σ n ω : ℝ≥0∞) < (E ω).2 →
        K ω = Sec7.stoppedHistory (Sec7.completedState (fun s ω => (E ω).1 s) VL VR fun ω => (E ω).2)
          (fun ω => (stopSeqR T σ n ω : WithTop ℝ≥0)) ω := fun n =>
    LocalExt.exists_measurable_stoppedHistory_version hX (hρ n)
  choose K hKm hKeq using hKex
  set R' : Ω → RecData := recVersionR T (stopSeqR T σ) K with hR'def
  have hR' : Measurable[annSigmaR hT hσ.1] R' :=
    @measurable_recVersionR Ω _ _ (annSigmaR hT hσ.1) T _ _
      (fun n => (measurable_stopSeqR hT hσ.1 n).mono (le_annSigmaR hT hσ.1 n) le_rfl)
      (fun n => (hKm n).mono (le_annSigmaR hT hσ.1 n) le_rfl) (measurableSet_forall_stopSeqR_lt hT hσ.1)
  set F : Set Ω := {ω | min (T ω) (E ω).2 ≠ ⊤} with hFdef
  set F' : Set Ω := {ω | (⨆ n, (stopSeqR T σ n ω : ℝ≥0∞)) ≠ ⊤} with hF'def
  have hF' : MeasurableSet[annSigmaR hT hσ.1] F' := by
    have hm : Measurable[annSigmaR hT hσ.1] fun ω => (⨆ n, (stopSeqR T σ n ω : ℝ≥0∞)) :=
      Measurable.iSup fun n => measurable_coe_nnreal_ennreal.comp
        ((measurable_stopSeqR hT hσ.1 n).mono (le_annSigmaR hT hσ.1 n) le_rfl)
    exact (hm (measurableSet_singleton ⊤)).compl
  have hFF' : ∀ᵐ ω ∂Q, ω ∈ F' ↔ ω ∈ F := by
    filter_upwards [hσ.2.2.2, ae_all_iff.2 hσ.2.2.1] with ω hann hlt
    have := iSup_coe_stopSeq (t := T ω) (σ := fun n => σ n ω) hlt hann
    change (⨆ n, ((min (T ω) (σ n ω : ℝ≥0∞)).toNNReal : ℝ≥0∞)) ≠ ⊤ ↔ min (T ω) (E ω).2 ≠ ⊤
    rw [this]
  have hRR' : ∀ᵐ ω ∂Q, ω ∈ F → R' ω = R ω := by
    filter_upwards [ae_isGoodStopPath_all hκ hreg hC.1 hseed, hσ.2.2.2, ae_all_iff.2 hσ.2.2.1, hC.1.2.2.2.2]
      with ω hgood hann hlt hp hωF
    exact recVersion_eq (T ω) (hgood (T ω) hωF) (hσ.2.1 ω) hlt hann fun n => hKeq n ω hp
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le (T ω) σ n ω)) (hlt n))
  -- the kernel at the stop, at fixed and at pushed test functions
  set xLp := (padFL 0 0 c.fn c.jumps).1.1
  set xRp := (padFL 0 0 c.fn c.jumps).1.2
  set ρLp := (padFL κ θ c.fn c.jumps).2.1
  set ρRp := (padFL κ θ c.fn c.jumps).2.2
  set nL := flowLineNL c.fn c.jumps 0
  set nR := flowLineNR c.fn c.jumps 0
  have hker := fun ψ => ae_condExp_cexp_stopR hκ hreg hC hseed hX hσ hT (padFL_snd_fst_fin κ θ c.fn c.jumps)
    (padFL_snd_snd_fin κ θ c.fn c.jumps) (padFL_fst_fst_fin c.fn c.jumps) (padFL_fst_snd_fin c.fn c.jumps)
    (θ * chiC κ) ψ
  have hM : ∀ r, ContinuousOn (stopMean κ nL nR xLp xRp ρLp ρRp (θ * chiC κ) r) (H \ stopHull r) := by
    intro r
    refine LocalExt.continuousOn_couplingMean_alive (continuous_rdrv r) (rtime_nonneg r) ?_
    exact (LocalExt.continuousOn_of_isBoundedHarmonicExtension
      (BoundaryWord.isBoundedHarmonicExtension_mean _ (isSorted_forceWord _ _ _ _ _ _ _ _))).add continuousOn_const
  have hpush := ae_condExp_cexp_pushTest (Q := Q) h𝓗 hC.2.1 hR' hFF' hRR' hM (fun ψ => hker ψ) φ
  -- the field read in the record chart, through the version
  set X : Ω → ℂ := fun ω => Complex.exp (Complex.I * (recField κ (R ω) (g ω) φ : ℂ)) with hXdef
  set Y : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h' ω (Chart.pushTest (isConformal_recChart (R' ω)) φ) : ℂ))
    with hYdef
  set S : Ω → ℂ := fun ω => Complex.exp (Complex.I * (chartShift κ θ (R' ω) φ : ℂ)) with hSdef
  have hYi : Integrable Y Q := GFF.integrable_exp_I_mul
    (RandomTest.measurable_apply_of_forall_measurable hC.2.1 fun z =>
      ((measurable_pushTest_recChart φ z).comp hR').mono h𝓗 le_rfl)
  have hSm : StronglyMeasurable[annSigmaR hT hσ.1] S :=
    (@GFF.measurable_exp_I_mul Ω (annSigmaR hT hσ.1) _ ((measurable_chartShift κ θ φ).comp hR')).stronglyMeasurable
  have hSY : Integrable (fun ω => S ω * Y ω) Q :=
    hYi.bdd_mul (hSm.mono h𝓗).aestronglyMeasurable
      (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have hpull : Q[fun ω => S ω * Y ω | annSigmaR hT hσ.1] =ᵐ[Q]
      fun ω => S ω * Q[Y | annSigmaR hT hσ.1] ω := by
    have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hSm
      (by simpa [ContinuousLinearMap.mul_apply'] using hSY) hYi
    simpa [ContinuousLinearMap.mul_apply'] using hp
  have hg : Measurable g := by
    refine LQGMetric.measurable_distOn_iff.2 fun ψ => ?_
    have e : (fun ω => g ω ψ) = fun ω => h' ω ψ - θ * chiC κ * ∫ z, ψ z := by
      funext ω
      have := htr ω ψ ψ (fun z => by rw [Complex.ofReal_zero, add_zero])
      linarith
    rw [e]
    exact ((measurable_distOn_apply ψ).comp hC.2.1).sub_const _
  have hXr : Measurable fun ω => recField κ (R ω) (g ω) φ := by
    have h1 := (measurable_recField κ).comp (hRm.prodMk hg)
    have h2 := (measurable_distOn_apply φ).comp h1
    exact h2
  have hXi : Integrable X Q := by
    have h3 := GFF.integrable_exp_I_mul (P := Q) hXr
    exact h3
  have hXSY : ∀ᵐ ω ∂Q, ω ∈ F → X ω = S ω * Y ω := by
    filter_upwards [hRR'] with ω hR hωF
    show Complex.exp (Complex.I * (recField κ (R ω) (g ω) φ : ℂ)) =
      Complex.exp (Complex.I * (chartShift κ θ (R' ω) φ : ℂ)) *
        Complex.exp (Complex.I * (h' ω (Chart.pushTest (isConformal_recChart (R' ω)) φ) : ℂ))
    rw [hR hωF, recField_apply_eq (htr ω) (R ω) φ, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the conditional law given the announced history
  have hcond : ∀ᵐ ω ∂Q, ω ∈ F → Q[X|annSigmaR hT hσ.1] ω = gaussCF (stopWord κ (c, θ, R ω)) φ := by
    have hind : F'.indicator X =ᵐ[Q] F'.indicator (fun ω => S ω * Y ω) := by
      filter_upwards [hXSY, hFF'] with ω h1 h2
      by_cases hω : ω ∈ F'
      · rw [indicator_of_mem hω, indicator_of_mem hω, h1 (h2.1 hω)]
      · rw [indicator_of_notMem hω, indicator_of_notMem hω]
    have hc1 : Q[F'.indicator X|annSigmaR hT hσ.1] =ᵐ[Q] F'.indicator (Q[X|annSigmaR hT hσ.1]) :=
      condExp_indicator hXi hF'
    have hc2 : Q[F'.indicator (fun ω => S ω * Y ω)|annSigmaR hT hσ.1] =ᵐ[Q]
        F'.indicator (Q[fun ω => S ω * Y ω|annSigmaR hT hσ.1]) :=
      condExp_indicator hSY hF'
    have hc3 : Q[F'.indicator X|annSigmaR hT hσ.1] =ᵐ[Q]
        Q[F'.indicator (fun ω => S ω * Y ω)|annSigmaR hT hσ.1] := condExp_congr_ae hind
    filter_upwards [hc1, hc2, hc3, hpull, hpush, hFF', hRR'] with ω h1 h2 h3 h4 h5 h6 h7 hωF
    have hω : ω ∈ F' := h6.2 hωF
    have e1 : Q[X|annSigmaR hT hσ.1] ω = Q[fun ω => S ω * Y ω|annSigmaR hT hσ.1] ω := by
      have := h1.symm.trans (h3.trans h2)
      simpa only [indicator_of_mem hω] using this
    rw [e1, h4, h5 hωF]
    simp only [hSdef, h7 hωF]
    exact cexp_chartShift_mul_eq_gaussCF κ θ nL nR xLp xRp ρLp ρRp (R ω) φ
  -- the tower property to the record σ-algebra
  have hRle : MeasurableSpace.comap R inferInstance ≤ mΩ := hRm.comap_le
  have hYgm : Measurable[MeasurableSpace.comap R inferInstance]
      fun ω => gaussCF (stopWord κ (c, θ, R ω)) φ :=
    ((measurable_gaussCF φ).comp ((measurable_stopWord κ).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).comp (comap_measurable R)
  have hYgi : Integrable (fun ω => gaussCF (stopWord κ (c, θ, R ω)) φ) Q :=
    Integrable.of_bound (C := 1) (hYgm.mono hRle le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => norm_gaussCF_le _ φ)
  have hFm : MeasurableSet[MeasurableSpace.comap R inferInstance] F := by
    refine ⟨{r : RecData | r.2.1 ≠ ⊤}, ?_, rfl⟩
    exact ((measurable_fst.comp measurable_snd) (measurableSet_singleton ⊤)).compl
  refine ae_condExp_eq_of_setIntegral_eq hRle hFm hXi hYgm.stronglyMeasurable hYgi ?_
  rintro A ⟨S0, hS0, rfl⟩
  set Bset : Set Ω := R' ⁻¹' S0 ∩ F' with hBdef
  have hB : MeasurableSet[annSigmaR hT hσ.1] Bset := (hR' hS0).inter hF'
  have hAB : (R ⁻¹' S0 ∩ F : Set Ω) =ᵐ[Q] Bset := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hFF', hRR'] with ω h1 h2
    simp only [hBdef, mem_inter_iff, mem_preimage]
    by_cases hωF : ω ∈ F
    · rw [h2 hωF]
      exact ⟨fun h => ⟨h.1, h1.2 h.2⟩, fun h => ⟨h.1, hωF⟩⟩
    · exact ⟨fun h => absurd h.2 hωF, fun h => absurd (h1.1 h.2) hωF⟩
  calc ∫ ω in R ⁻¹' S0 ∩ F, X ω ∂Q = ∫ ω in Bset, X ω ∂Q := setIntegral_congr_set hAB
    _ = ∫ ω in Bset, (Q[X|annSigmaR hT hσ.1]) ω ∂Q := (setIntegral_condExp h𝓗 hXi hB).symm
    _ = ∫ ω in Bset, gaussCF (stopWord κ (c, θ, R ω)) φ ∂Q := by
        refine setIntegral_congr_ae (h𝓗 _ hB) ?_
        filter_upwards [hcond, hFF'] with ω h1 h2 hωB using h1 (h2.1 hωB.2)
    _ = ∫ ω in R ⁻¹' S0 ∩ F, gaussCF (stopWord κ (c, θ, R ω)) φ ∂Q := (setIntegral_congr_set hAB).symm

end Main

/-! ### An inadmissible seed, and every seed -/

section Inadm

/-- Conditioning on an almost surely constant map gives the expectation. -/
theorem condExp_comap_ae_const {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {R : Ω → β} (hR : Measurable R) {r₀ : β} (hR0 : ∀ᵐ ω ∂Q, R ω = r₀) {X : Ω → ℂ}
    (hX : Integrable X Q) : Q[X|MeasurableSpace.comap R inferInstance] =ᵐ[Q] fun _ => ∫ ω, X ω ∂Q := by
  have hRle : MeasurableSpace.comap R inferInstance ≤ mΩ := hR.comap_le
  refine (ae_eq_condExp_of_forall_setIntegral_eq hRle hX (fun s _ _ => integrableOn_const (measure_ne_top _ _))
    (fun s hs _ => ?_) stronglyMeasurable_const.aestronglyMeasurable).symm
  obtain ⟨S0, -, rfl⟩ := hs
  by_cases h0 : r₀ ∈ S0
  · have hset : (R ⁻¹' S0 : Set Ω) =ᵐ[Q] (univ : Set Ω) := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hR0] with ω hω
      simp only [mem_preimage, hω, h0, mem_univ]
    rw [setIntegral_congr_set hset, setIntegral_congr_set hset]
    simp only [Measure.restrict_univ]
    rw [integral_const, probReal_univ, one_smul]
  · have hset : (R ⁻¹' S0 : Set Ω) =ᵐ[Q] (∅ : Set Ω) := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hR0] with ω hω
      simp only [mem_preimage, hω, h0, mem_empty_iff_false]
    rw [setIntegral_congr_set hset, setIntegral_congr_set hset]
    simp only [Measure.restrict_empty, integral_zero_measure]

/-- **The single-stage law at a random time, inadmissible seed** (the lifetime vanishes almost surely, so the record is
almost surely the zero record whatever the stop; deduced from the deterministic case
`ae_condExp_recField_of_inadmissible` at `t = 0`). Only measurability of `T` is used. -/
theorem ae_condExp_recField_of_inadmissible_stop {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (g : Ω → DistOn upperHalfPlaneOpens) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hE : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω))
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ Q g (fun s ω => (E ω).1 s) (fun ω => (E ω).2))
    (hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))
    {T : Ω → ℝ≥0∞} (hTm : Measurable T) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂Q,
      Q[fun ω' => Complex.exp (Complex.I * (recField κ (recOf (T ω') (E ω')) (g ω') φ : ℂ)) |
          MeasurableSpace.comap (fun ω' => recOf (T ω') (E ω')) inferInstance] ω =
        gaussCF (stopWord κ (c, θ, recOf (T ω) (E ω))) φ := by
  have hdet := ae_condExp_recField_of_inadmissible hκ c θ 0 Q g E hE hreg hfl hseed φ
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := hfl
  have hζ0 := LocalExt.ae_zeta_eq_zero_of_thresholdCondition hC.1 hκ hseed
  have hRT : ∀ᵐ ω ∂Q, recOf (T ω) (E ω) = zeroRec := by
    filter_upwards [hζ0] with ω hω
    exact recOf_of_zero (hreg ω) hω
  have hR0 : ∀ᵐ ω ∂Q, recOf 0 (E ω) = zeroRec := by
    filter_upwards [hζ0] with ω hω
    exact recOf_of_zero (hreg ω) hω
  have hg : Measurable g := by
    refine LQGMetric.measurable_distOn_iff.2 fun ψ => ?_
    have e : (fun ω => g ω ψ) = fun ω => h' ω ψ - θ * chiC κ * ∫ z, ψ z := by
      funext ω
      have := htr ω ψ ψ (fun z => by rw [Complex.ofReal_zero, add_zero])
      linarith
    rw [e]
    exact ((measurable_distOn_apply ψ).comp hC.2.1).sub_const _
  have hRTm : Measurable fun ω => recOf (T ω) (E ω) := GW2Schedule.measurable_recOf_joint hE hreg hTm
  have hR0m : Measurable fun ω => recOf 0 (E ω) := measurable_recOf hE hreg 0
  have hXT : Integrable (fun ω => Complex.exp (Complex.I * (recField κ (recOf (T ω) (E ω)) (g ω) φ : ℂ))) Q := by
    have h1 := (measurable_recField κ).comp (hRTm.prodMk hg)
    have h2 := (measurable_distOn_apply φ).comp h1
    have h3 := GFF.integrable_exp_I_mul (P := Q) h2
    exact h3
  have hX0 : Integrable (fun ω => Complex.exp (Complex.I * (recField κ (recOf 0 (E ω)) (g ω) φ : ℂ))) Q := by
    have h1 := (measurable_recField κ).comp (hR0m.prodMk hg)
    have h2 := (measurable_distOn_apply φ).comp h1
    have h3 := GFF.integrable_exp_I_mul (P := Q) h2
    exact h3
  have hcT := condExp_comap_ae_const hRTm hRT hXT
  have hc0 := condExp_comap_ae_const hR0m hR0 hX0
  have hint : (∫ ω, Complex.exp (Complex.I * (recField κ (recOf (T ω) (E ω)) (g ω) φ : ℂ)) ∂Q) =
      ∫ ω, Complex.exp (Complex.I * (recField κ (recOf 0 (E ω)) (g ω) φ : ℂ)) ∂Q := by
    refine integral_congr_ae ?_
    filter_upwards [hRT, hR0] with ω h1 h2
    simp only [h1, h2]
  obtain ⟨ω₁, hω₁⟩ := (hdet.and (hc0.and hR0)).exists
  have hval : (∫ ω, Complex.exp (Complex.I * (recField κ (recOf 0 (E ω)) (g ω) φ : ℂ)) ∂Q) =
      gaussCF (stopWord κ (c, θ, zeroRec)) φ := by
    rw [← hω₁.2.2, ← hω₁.1, hω₁.2.1]
  filter_upwards [hcT, hRT] with ω h1 h2
  rw [h1, hint, hval, h2]

/-- **The single-stage law at a stopping time, every seed.** For an angle-`θ` flow-line coupling `hC` of `g` (datum
`c`) with regular driver `E` and a measurable stopping time `T` of its driving filtration, almost surely on
`{min T ζ < ∞}` the field read in the record chart has, given the record `recOf T E`, the Gaussian characteristic
functional of the stop word `stopWord κ (c, θ, recOf T E)`. -/
theorem ae_condExp_recField_stop {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (g : Ω → DistOn upperHalfPlaneOpens) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hE : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω)) {h' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (g ω) (h' ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) Q 𝓕 (fun s ω => (E ω).1 s) VL VR B
      (fun ω => (E ω).2) h')
    (hX : IsMeasurableKilledDriving (fun s ω => (E ω).1 s) VL VR fun ω => (E ω).2)
    {T : Ω → ℝ≥0∞} (hTm : Measurable T) (hT : IsStoppingTime (drivingFiltration Q hX) (T : Ω → WithTop ℝ≥0))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂Q, min (T ω) (E ω).2 ≠ ⊤ →
      Q[fun ω' => Complex.exp (Complex.I * (recField κ (recOf (T ω') (E ω')) (g ω') φ : ℂ)) |
          MeasurableSpace.comap (fun ω' => recOf (T ω') (E ω')) inferInstance] ω =
        gaussCF (stopWord κ (c, θ, recOf (T ω) (E ω))) φ := by
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  · filter_upwards [ae_condExp_recField_of_inadmissible_stop hκ c θ Q g E hE hreg ⟨h', 𝓕, VL, VR, B, htr, hC⟩
      hseed hTm φ] with ω h _ using h
  · exact ae_condExp_recField_of_admissible_stop hκ c θ Q g E hE hreg htr hC hseed hX hTm hT φ

end Inadm

/-! ### Times read from the killed driver are stopping times of the driving filtration -/

section DriverTimes

/-- The σ-algebra of the killed driver alone up to time `t` (no force points): generated by the events
`{r < ζ, W_r ∈ A}`, `r ≤ t`. -/
@[instance_reducible]
def killedDriverSigma {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {S | ∃ r ≤ t, ∃ A : Set ℝ, MeasurableSet A ∧ S = {ω | (r : ℝ≥0∞) < ζ ω ∧ W r ω ∈ A}}

/-- The killed driver's σ-algebra is contained in the driving filtration (whatever the force points). -/
theorem killedDriverSigma_le_drivingFiltration {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    killedDriverSigma W ζ t ≤ drivingFiltration P hX t := by
  refine (MeasurableSpace.generateFrom_le fun S hS => ?_).trans (Ito.le_usualAugmentation _ P t)
  obtain ⟨r, hr, A, hA, rfl⟩ := hS
  refine MeasurableSpace.measurableSet_generateFrom ⟨r, hr, A ×ˢ univ, hA.prod MeasurableSet.univ, ?_⟩
  ext ω
  simp only [mem_ofPred_eq, mem_prod, mem_univ, and_true]

/-- **A random time decided by the killed driver is a stopping time of the driving filtration**: if `{T ≤ t}` is in
the σ-algebra of the killed driver up to `t` for every `t`, then `T` is a stopping time of `drivingFiltration P hX`. -/
theorem isStoppingTime_of_killedDriverSigma {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0∞}
    (hT : ∀ t : ℝ≥0, MeasurableSet[killedDriverSigma W ζ t] {ω | T ω ≤ (t : ℝ≥0∞)}) :
    IsStoppingTime (drivingFiltration P hX) (T : Ω → WithTop ℝ≥0) := fun t =>
  killedDriverSigma_le_drivingFiltration P hX t _ (hT t)

/-- **The single-stage law at a random time read from the driver** (the form of `IsStopLaw` with the deterministic stop
replaced by a random time): for a flow-line driver `E` of `g` (datum `c`, angle `θ`) and a measurable random time `T`
such that `{T ≤ t}` is decided by the killed driver up to `t`, almost surely on `{min T ζ < ∞}` the field read in the
record chart has, given the record `recOf T E`, the Gaussian characteristic functional of
`stopWord κ (c, θ, recOf T E)`. -/
theorem ae_condExp_recField_stop_of_driver {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (g : Ω → DistOn upperHalfPlaneOpens) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hE : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω))
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ Q g (fun s ω => (E ω).1 s) (fun ω => (E ω).2))
    {T : Ω → ℝ≥0∞} (hTm : Measurable T)
    (hT : ∀ t : ℝ≥0, MeasurableSet[killedDriverSigma (fun s ω => (E ω).1 s) (fun ω => (E ω).2) t]
      {ω | T ω ≤ (t : ℝ≥0∞)})
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂Q, min (T ω) (E ω).2 ≠ ⊤ →
      Q[fun ω' => Complex.exp (Complex.I * (recField κ (recOf (T ω') (E ω')) (g ω') φ : ℂ)) |
          MeasurableSpace.comap (fun ω' => recOf (T ω') (E ω')) inferInstance] ω =
        gaussCF (stopWord κ (c, θ, recOf (T ω) (E ω))) φ := by
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := hfl
  obtain ⟨hX, -⟩ := hC.2.2.2
  exact ae_condExp_recField_stop hκ c θ Q g E hE hreg htr hC hX hTm (isStoppingTime_of_killedDriverSigma Q hX hT) φ

end DriverTimes

end InteractingSLE.Theorem14.GW2KM2
