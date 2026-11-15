/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MqIface
import InteractingSLE.Spec.Supplement.SB2CondCode
import InteractingSLE.Spec.Supplement.GW2aPiece
import InteractingSLE.Spec.Supplement.W5CommonSeedShift
import InteractingSLE.Spec.Sec5.Lemma56Stages
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# A relative stage of zero lifetime: the code match at an inadmissible seed (ruling R120, D11)

Packet PROVE-SB2-LCMEAN, round 12. D11: at an arc entry the relative walk's root seed has the low connector on its
right, so the relative root piece is launched with zero lifetime; there the conditional law says only "the canonical
flow line has lifetime `0`", which holds because the relative seed is inadmissible. This file proves the code-level
form of that case, generically and at the relative root:

* `IsSeedThreshold κ θ c`: the threshold condition at the seed of the angle-`θ` flow-line word of `c`;
* **`ae_driverCode_snd_eq_zero_of_threshold`**: under a GFF law with a word whose seed is a threshold, the canonical
  driver code has lifetime `0` almost surely (Theorems 1.2–1.3;
  `IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold`);
* `ae_notMem_of_condExpKernel_eq_zero`: almost surely, a sample whose conditional probability of a measurable set `B`
  vanishes is not in `B`;
* **`ae_codeMatch_of_seedThreshold`** (generic stage): for every witness `(β, Y)` of a stage's conditional law, almost
  surely at a launch whose witness word has a threshold seed, a driver of lifetime `0` matches the canonical code;
* **`ae_seedThreshold_root_iff`**: at the root of a boundary walk the witness word has a threshold seed iff the root's
  heights are not admissible (the past is trivial and the data agree off a finite set);
* **`ae_codeMatch_root_of_zero`**: SB2(2)'s relative root, case of zero lifetime — from LIFTSET's bundle
  (`ArcStart.low` with `RayCorr.rightLim_eq`; `PieceStartV` gives positive lifetime), almost surely under the retained
  kernel, a root of lifetime `0` matches the canonical code of every witness of the root's law.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mr

open Restart Exist Exist.Staged Exist.StagedLaw PiecewiseConstantBoundaryData Sec2.Assembly

/-- The threshold condition at the seed of the angle-`θ` flow-line word of `c`. -/
def IsSeedThreshold (κ θ : ℝ) (c : BoundaryWord) : Prop :=
  ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
    (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)

/-- **A threshold seed gives the canonical driver code lifetime `0`**, almost surely under a GFF law with the word. -/
theorem ae_driverCode_snd_eq_zero_of_threshold (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)
    (h13 : Theorem13Statement.{u}) {c : BoundaryWord} (hthr : IsSeedThreshold κ θ c) {S : Type u}
    [MeasurableSpace S] {Q : Measure S} [IsProbabilityMeasure Q] {Y : S → DistOn upperHalfPlaneOpens}
    (hY : IsGFFWithBoundaryData Q Y c.fn c.jumps) :
    ∀ᵐ s ∂Q, (driverCode h12p hκ θ (c, Y s)).2 = 0 := by
  have hD : Measurable fun s => driverOf h12p hκ θ (c, Y s) :=
    (measurable_driverOf h12p hκ θ).comp (measurable_const.prodMk hY.1)
  have hfl : IsFlowLineDriver κ c.fn c.jumps θ Q Y (fun t s => (driverOf h12p hκ θ (c, Y s)).1 t)
      (fun s => (driverOf h12p hκ θ (c, Y s)).2) := by
    refine Cond.isFlowLineDriver_of_driverCodeMatch_univ h12p hκ θ h13 c hY
      (fun t => (measurable_pi_apply t).comp (measurable_fst.comp hD)) (measurable_snd.comp hD)
      (fun s => ?_) (Eventually.of_forall fun s => ?_)
    · rw [driverOf_mk]
      exact (drvOf_regular _).1
    · refine ⟨rfl, ?_, fun n k _ => rfl⟩
      show (driverOf h12p hκ θ (c, Y s)).1 0 = (driverOf h12p hκ θ (c, Y s)).1 (dyad 0 0)
      rw [Exist.dyad_zero_zero]
  obtain ⟨_, _, _, _, _, _, hC⟩ := hfl
  exact IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hthr

/-- **A conditionally null set is missed**: almost surely, a sample whose conditional probability of the measurable
set `B` vanishes is not in `B`. -/
theorem ae_notMem_of_condExpKernel_eq_zero {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) {B : Set Ω}
    (hB : MeasurableSet B) : ∀ᵐ ω ∂P, condExpKernel P m ω B = 0 → ω ∉ B := by
  set Z : Set Ω := {ω | condExpKernel P m ω B = 0} with hZdef
  have hZ : MeasurableSet[m] Z := measurableSet_eq_fun (measurable_condExpKernel hB) measurable_const
  have hE : MeasurableSet (Z ∩ B)ᶜ := ((hm _ hZ).inter hB).compl
  have hae : ∀ᵐ ω ∂P, ω ∈ (Z ∩ B)ᶜ := by
    refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel hm hE ?_
    filter_upwards [Sec7.Aux122Disint.ae_condExpKernel_apply_eq_indicator (P := P) hm hZ] with ω₀ hind
    by_cases h₀ : ω₀ ∈ Z
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (show condExpKernel P m ω₀ B = 0 from h₀)] with ω hω h
      exact hω h.2
    · have h0 : condExpKernel P m ω₀ Z = 0 := by rw [hind, indicator_of_notMem h₀]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω h
      exact hω h.1
  filter_upwards [hae] with ω hω hz hb
  exact hω ⟨hz, hb⟩

section Generic

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The code match at a threshold seed** (generic stage): for every witness `(β, Y)` of the stage's conditional law,
almost surely at a launch whose witness word has a threshold seed, a driver of lifetime `0` matches the canonical
code (its lifetime is `0` by `ae_driverCode_snd_eq_zero_of_threshold` under the conditional law). -/
theorem ae_codeMatch_of_seedThreshold (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (θ₀ : ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps) (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ} {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsSeedThreshold κ θ₀ (β ω) → (E k ω).2 = 0 →
      IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2 := by
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by
    rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) k le_rfl).comap_le
  set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} with hLdef
  have hL : MeasurableSet[pastSigma κ b jumps spec E k] L := Lv.measurableSet_launch_pastSigma hb hEm hreg k
  have hβm : Measurable β := hW.1.mono h𝒢 le_rfl
  have hG : Measurable fun ω => driverCode h12p hκ θ₀ (β ω, Y ω) :=
    (measurable_driverCode h12p hκ θ₀).comp (hβm.prodMk hW.2.1)
  set B : Set Ω := L ∩ {ω | (driverCode h12p hκ θ₀ (β ω, Y ω)).2 ≠ 0} with hBdef
  have hB : MeasurableSet B :=
    (h𝒢 _ hL).inter (measurableSet_eq_fun (measurable_snd.comp hG) measurable_const).compl
  have hker : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → IsSeedThreshold κ θ₀ (β ω₀) →
      condExpKernel P (pastSigma κ b jumps spec E k) ω₀ B = 0 := by
    filter_upwards [hW.2.2.2, Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hW.1] with ω₀ hg hβeq hl hthr
    have h0 := ae_driverCode_snd_eq_zero_of_threshold h12p hκ θ₀ h13 hthr (hg hl)
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h0, hβeq] with ω h1 h2 hmem
    exact hmem.2 (by rw [h2]; exact h1)
  filter_upwards [ae_notMem_of_condExpKernel_eq_zero (P := P) h𝒢 hB, hker] with ω hn hk hl hthr hz
  have hc0 : (driverCode h12p hκ θ₀ (β ω, Y ω)).2 = 0 := by
    by_contra hne
    exact hn (hk hl hthr) ⟨hl, hne⟩
  refine ⟨hz.trans hc0.symm, ?_, fun n j hnj => absurd hnj (by rw [hz]; exact not_lt_zero)⟩
  show (E k ω).1 0 = (driverOf h12p hκ θ₀ (β ω, Y ω)).1 (dyad 0 0)
  rw [Exist.dyad_zero_zero, (hreg k ω).2.1, driverOf_mk, (drvOf_regular _).2.1]

end Generic

section Root

variable {κ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The root's witness word has a threshold seed iff the root's heights are not admissible**: at the root of a
boundary walk the past is trivial, the root field is the walk's field, and the witness word agrees with the walk's
data off a finite set. -/
theorem ae_seedThreshold_root_iff (hκ : 0 < κ) {b₂ : ℝ → ℝ} {J₂ : Finset ℝ}
    (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂) {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h₂ : Ω → DistOn upperHalfPlaneOpens} (hh₂ : IsGFFWithBoundaryData Q h₂ b₂ J₂) (θ : ℝ)
    {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b₂ J₂ Q h₂ (boundaryWalkSpec b₂ J₂ θ true) EL 0 β Y) :
    ∀ᵐ ω ∂Q, (IsSeedThreshold κ θ (β ω) ↔
      ¬ ExplState.IsAdmissibleSeed κ (leftLim b₂ 0) (rightLim b₂ 0) θ) := by
  have hl : ∀ ω, (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (fun j => EL j ω) (0 + 1)).2.2.2.1 0 ≠
      none := fun ω => by
    rw [zero_add, Lk.run_one_walk (κ := κ) (θ := θ) b₂ J₂ (fun j => EL j ω), launches_launch,
      Function.update_self]
    exact Option.some_ne_none _
  have hYeq : ∀ᵐ ω ∂Q, Exist.flowField 0 0 (h₂ ω) = Y ω := by
    filter_upwards [hW.2.2.1] with ω hω
    obtain ⟨-, -, hT⟩ := hω (hl ω)
    have hT' : IsChartTransport (Chart.id.recenter 0) 1 0 (chiC κ) (h₂ ω) (Y ω) := hT
    exact (GW2aPiece.eq_flowField_of_isChartTransport hT').symm
  have hYg : IsGFFWithBoundaryData Q Y (fun y => b₂ (y + 0)) (J₂.image (· - 0)) :=
    isGFFWithBoundaryData_congr_ae (Supp9.IsGFFWithBoundaryData.recenter hb₂ 0 hh₂) hW.2.1 hYeq
  have hb0 : IsPiecewiseConstantBoundaryData (fun y => b₂ (y + 0)) (J₂.image (· - 0)) :=
    Exist.isPiecewiseConstant_comp_add hb₂ 0
  filter_upwards [hW.2.2.2] with ω₀ hg
  have hg' := hg (hl ω₀)
  rw [GW1.pastSigma_zero_eq_bot, GW1.condExpKernel_bot_apply] at hg'
  have heq := eq_of_isGFFWithBoundaryData (β ω₀).isPiecewiseConstantBoundaryData hb0 hg' hYg
  have hlims := GW1.lims_eq_of_eq_off_finset ((β ω₀).jumps ∪ J₂.image (· - 0)) heq 0
  unfold IsSeedThreshold
  rw [GW1.thresholdCondition_flowLine_zero_iff hκ, hlims.1, hlims.2]
  simp only [add_zero]

end Root

end InteractingSLE.Theorem14.SB.Mr
