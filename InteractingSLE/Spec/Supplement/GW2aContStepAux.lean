/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContPass

/-!
# Lemma GW2a for every program: the ingredients of GW1's inductive step

Packet PROVE-GW2AC.

* `flowStep_uniform`, **`run_succ_cases`**: one step of the run keeps the state, kills it, launches the instruction's
  piece in the current chart, or (a boundary continuation) appends a connector; the branch does not depend on the
  driver of the instruction.
* `lastRec`, `lastRec_of_launch`, `lastRec_of_noLaunch`: the record of instruction `j` in the retained past.
* **`ae_ae_condExpKernel_succ_eq`**: under the regular conditional law given the retained past before `j`, the regular
  conditional law given the retained past before `j + 1` is the conditional law given the last record (the kernel of a
  kernel, PROVE-T14-BR7, for an arbitrary program).
* `ae_condExpKernel_comap_eq_self`: conditioning on an almost surely constant record does nothing.
* `ae_lifetime_eq_zero_or_ne`: a flow line has zero lifetime almost surely or almost never (the seed threshold
  condition is deterministic, Lemma GW0's first sentence).
* `loewner_zero_inv`, `isChartTransport_loewner_zero_iff`, `tipAt_loewner_zero_iff`: a stage of zero capacity does not
  change the chart.
* **`isConformal_runChart`**: the chart of a run whose launched pieces are regular is conformal with a continuous lift.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aCont

open Exist.Staged Exist.StagedLaw GW2Later CounterflowRange GW2aMulti

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-! ### The kinds of steps, uniformly in the driver -/

/-- **A flow step takes the same branch for every driver.** -/
theorem flowStep_uniform (gw2 : Bool) (s : ExplState) (k : ℕ) (θ : ℝ) (t : ℝ≥0∞) :
    (∀ D, ExplState.flowStep κ b gw2 s k D θ t = s) ∨ (∀ D, ExplState.flowStep κ b gw2 s k D θ t = setDead s) ∨
      ∀ D, ExplState.flowStep κ b gw2 s k D θ t = ExplState.launch s k D θ t := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.flowStep
  dsimp only
  rcases status with u | u | o | bb | u | u
  · exact Or.inr (Or.inr fun D => rfl)
  · exact Or.inr (Or.inr fun D => rfl)
  · split_ifs
    · exact Or.inr (Or.inl fun D => rfl)
    · exact Or.inr (Or.inr fun D => rfl)
    · exact Or.inl fun D => rfl
  · split_ifs
    · exact Or.inr (Or.inl fun D => rfl)
    · exact Or.inr (Or.inr fun D => rfl)
    · exact Or.inl fun D => rfl
  · exact Or.inl fun D => rfl
  · exact Or.inl fun D => rfl

/-- The boundary-continuation case of `run_succ_cases`. -/
theorem run_succ_cases_cont {spec : ExplSpec} {j : ℕ} (s : ExplState) (vStop : Option ℝ) (pref : Bool)
    (hD' : ∀ D, ExplState.run κ b jumps spec D j = s →
      ExplState.run κ b jumps spec D (j + 1) = ExplState.contStep κ b jumps s vStop pref) :
    (∀ D, ExplState.run κ b jumps spec D j = s → ExplState.run κ b jumps spec D (j + 1) = s) ∨
    (∀ D, ExplState.run κ b jumps spec D j = s → ExplState.run κ b jumps spec D (j + 1) = setDead s) ∨
    ∃ s' : ExplState, s'.2.1 ≠ s.2.1 ∧
      ∀ D, ExplState.run κ b jumps spec D j = s → ExplState.run κ b jumps spec D (j + 1) = s' := by
  by_cases ha : (ExplState.contStep κ b jumps s vStop pref).2.1 = s.2.1
  · rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s vStop pref with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩
    · exact Or.inl fun D hD => (hD' D hD).trans e
    · exact Or.inr (Or.inl fun D hD => (hD' D hD).trans e)
    · rw [e] at ha
      exact absurd (congrArg List.length ha) (by simp [ExplState.moveAlong])
    · rw [e] at ha
      exact absurd (congrArg List.length ha) (by simp [ExplState.moveToEnd])
  · exact Or.inr (Or.inr ⟨_, ha, hD'⟩)

/-- **The step after `j` instructions, uniformly in the driver of instruction `j`.** For the state `s` after `j`
instructions, the next step keeps `s`, kills it, launches the instruction's piece in the chart of `s`, or appends a
connector (a step that does not read the driver). -/
theorem run_succ_cases (spec : ExplSpec) (s : ExplState) (j : ℕ) :
    (∀ D, ExplState.run κ b jumps spec D j = s → ExplState.run κ b jumps spec D (j + 1) = s) ∨
    (∀ D, ExplState.run κ b jumps spec D j = s → ExplState.run κ b jumps spec D (j + 1) = setDead s) ∨
    (∃ (θ : ℝ) (t : ℝ≥0∞), spec.2.2[j]? = some (Sum.inl (θ, t)) ∧ ∀ D, ExplState.run κ b jumps spec D j = s →
      ExplState.run κ b jumps spec D (j + 1) = ExplState.launch s j (D j) θ t) ∨
    ∃ s' : ExplState, s'.2.1 ≠ s.2.1 ∧
      ∀ D, ExplState.run κ b jumps spec D j = s → ExplState.run κ b jumps spec D (j + 1) = s' := by
  cases hk : spec.2.2[j]? with
  | none => exact Or.inl fun D hD => by rw [run_succ, hk]; exact hD
  | some ins =>
    rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
    · rcases flowStep_uniform (κ := κ) (b := b) spec.2.1 s j θ t with h | h | h
      · exact Or.inl fun D hD => by rw [run_succ, hk, hD]; exact h (D j)
      · exact Or.inr (Or.inl fun D hD => by rw [run_succ, hk, hD]; exact h (D j))
      · exact Or.inr (Or.inr (Or.inl ⟨θ, t, rfl, fun D hD => by rw [run_succ, hk, hD]; exact h (D j)⟩))
    · rcases run_succ_cases_cont (κ := κ) (b := b) (jumps := jumps) s none pref fun D hD => by
          rw [run_succ, hk, hD]; rfl with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
    · rcases run_succ_cases_cont (κ := κ) (b := b) (jumps := jumps) s (some v) pref fun D hD => by
          rw [run_succ, hk, hD]; rfl with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

/-! ### The last record -/

/-- The record of instruction `j` in the retained past before `j + 1`. -/
def lastRec (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (ω : Ω) : RecData :=
  pastMap κ b jumps spec E (j + 1) ω (Fin.last j)

theorem lastRec_eq {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (ω : Ω) :
    lastRec κ b jumps spec E j ω = readRec ((ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.1 j) :=
  rfl

theorem lastRec_of_launch {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) {ω : Ω}
    (hl : (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none) :
    lastRec κ b jumps spec E j ω = recOf (instrTime spec j) (E j ω) := by
  rw [lastRec_eq, retained_run_succ_self]
  simp only [hl, ↓reduceIte]
  rfl

theorem lastRec_of_noLaunch {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) {ω : Ω}
    (hl : (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none) :
    lastRec κ b jumps spec E j ω = readRec (fun _ => 0, 0, false) := by
  rw [lastRec_eq, retained_run_succ_self]
  simp only [hl, ↓reduceIte]

/-! ### Kernels after one more instruction -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
theorem measurable_pastMap_of_le {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hle : ∀ k, pastSigma κ b jumps spec E k ≤ mΩ) (k : ℕ) : Measurable (pastMap κ b jumps spec E k) := by
  have : Measurable[pastSigma κ b jumps spec E k] (pastMap κ b jumps spec E k) := fun s hs => by
    rw [pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  exact this.mono (hle k) le_rfl

omit [StandardBorelSpace Ω] in
theorem measurable_lastRec {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hle : ∀ k, pastSigma κ b jumps spec E k ≤ mΩ) (j : ℕ) : Measurable (lastRec κ b jumps spec E j) :=
  (measurable_pi_apply _).comp (measurable_pastMap_of_le hle (j + 1))

/-- **The retained past one instruction later, under the conditional law given the retained past**: for almost every
`ω₀`, under `ν = condExpKernel P (pastSigma j) ω₀`, almost surely the conditional law given the last record is the
conditional law given the retained past before `j + 1` (PROVE-T14-BR7's kernel of a kernel and null-equivalence, for
an arbitrary program). -/
theorem ae_ae_condExpKernel_succ_eq {P : Measure Ω} [IsProbabilityMeasure P] {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hle : ∀ k, pastSigma κ b jumps spec E k ≤ mΩ) (j : ℕ) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
      condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
          (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω =
        condExpKernel P (pastSigma κ b jumps spec E (j + 1)) ω := by
  have hpm : ∀ k, Measurable[pastSigma κ b jumps spec E k] (pastMap κ b jumps spec E k) := fun k s hs => by
    rw [pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  have hpmΩ := measurable_pastMap_of_le hle (j + 1)
  have hcg : @MeasurableSpace.CountablyGenerated Ω (pastSigma κ b jumps spec E (j + 1)) := by
    rw [pastSigma_eq_comap]
    exact MeasurableSpace.CountablyGenerated.comap _
  have hgm := measurable_lastRec hle j
  filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel_eq (hle j) (hpm j),
    KernelTower.ae_ae_condExpKernel_condExpKernel_eq (P := P) (pastSigma_mono spec E (Nat.le_succ j))
      (hle (j + 1)) hcg] with ω₀ hpmω hkk
  have hfg : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
      pastMap κ b jumps spec E (j + 1) ω =
        Fin.snoc (α := fun _ => RecData) (pastMap κ b jumps spec E j ω₀) (lastRec κ b jumps spec E j ω) := by
    filter_upwards [hpmω] with ω hω
    rw [pastMap_succ_eq_snoc spec E j ω, hω]
    rfl
  have hker2 := KernelTower.ae_condExpKernel_comap_eq (P := condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
    hpmΩ hgm (measurable_snoc_const _) (ψ := fun u : PastData (j + 1) => u (Fin.last j))
    (measurable_pi_apply _) hfg (Eventually.of_forall fun ω => rfl)
  filter_upwards [hker2, hkk] with ω h1 h2
  rw [← h1]
  exact h2

/-- **Conditioning on an almost surely constant map does nothing.** -/
theorem ae_condExpKernel_comap_eq_self {ν : Measure Ω} [IsProbabilityMeasure ν] {X : Type*} [MeasurableSpace X]
    {g : Ω → X} (hg : Measurable g) {x₀ : X} (hx : ∀ᵐ ω ∂ν, g ω = x₀) :
    ∀ᵐ ω ∂ν, condExpKernel ν (MeasurableSpace.comap g inferInstance) ω = ν := by
  have h := KernelTower.ae_condExpKernel_comap_eq (P := ν) (f := g) (g := fun _ : Ω => ())
    hg measurable_const (φ := fun _ : Unit => x₀) measurable_const (ψ := fun _ : X => ()) measurable_const hx
    (Eventually.of_forall fun _ => rfl)
  have hbot : MeasurableSpace.comap (fun _ : Ω => ()) (inferInstance : MeasurableSpace Unit) = ⊥ :=
    MeasurableSpace.comap_const _
  filter_upwards [h] with ω hω
  rw [hω, hbot]
  exact GW1.condExpKernel_bot_apply ν ω

/-! ### Zero lifetime is almost sure or almost impossible -/

omit [StandardBorelSpace Ω] in
/-- **A flow line has zero lifetime almost surely or almost never**: the lifetime is zero exactly when the seed is a
threshold state of its force word (Lemma GW0's first sentence), a deterministic condition. -/
theorem ae_lifetime_eq_zero_or_ne {θ : ℝ} {Q : Measure Ω} {g : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b jumps θ Q g W ζ) :
    (∀ᵐ ω ∂Q, ζ ω = 0) ∨ ∀ᵐ ω ∂Q, ζ ω ≠ 0 := by
  obtain ⟨g', 𝓕, VL, VR, B, -, hC⟩ := hfl
  by_cases hthr : ForceWord.ThresholdCondition (flowLineRhoL κ b jumps 0 θ) (flowLineRhoR κ b jumps 0 θ) 0
      (flowLineXL b jumps 0) (flowLineXR b jumps 0)
  · exact Or.inl (hC.1.ae_lifetime_eq_zero_of_threshold hthr)
  · refine Or.inr ?_
    filter_upwards [hC.1.2.2.2.2] with ω hp h0
    exact hthr ((GW0.lifetime_eq_zero_iff hp).1 h0)

/-! ### A stage of zero capacity -/

omit mΩ [StandardBorelSpace Ω] in
theorem fwdMap_zero_driver_zero {W : ℝ → ℝ} (hW0 : W 0 = 0) : fwdMap W 0 = id :=
  funext fun y => Exist.StagedLaw.fwdMap_zero_time hW0 y

omit mΩ [StandardBorelSpace Ω] in
theorem loewner_zero_inv {c : Chart} {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {w : ℂ} (hw : w ∈ H) :
    (c.loewner W 0).2.1 w = c.2.1 w := by
  change c.2.1 (fwdMapInv W 0 w) = c.2.1 w
  rw [fwdMapInv_zero_time hW hW0 hw]

omit mΩ [StandardBorelSpace Ω] in
theorem loewner_zero_fwd {c : Chart} {W : ℝ → ℝ} (hW0 : W 0 = 0) : (c.loewner W 0).1 = c.1 := by
  funext z
  change fwdMap W 0 (c.1 z) = c.1 z
  rw [fwdMap_zero_driver_zero hW0]
  rfl

omit mΩ [StandardBorelSpace Ω] in
theorem loewner_zero_lift {c : Chart} {W : ℝ → ℝ} : (c.loewner W 0).2.2 = c.2.2 := by
  funext z
  change (QuantumZipper.logDerivFwd W 0 (c.1 z)).im + c.2.2 z = c.2.2 z
  simp only [QuantumZipper.logDerivFwd, intervalIntegral.integral_same, neg_zero, Complex.zero_im, zero_add]

omit mΩ [StandardBorelSpace Ω] in
theorem image_loewner_zero_inv {c : Chart} {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) :
    (c.loewner W 0).2.1 '' H = c.2.1 '' H :=
  image_congr fun _ hw => loewner_zero_inv hW hW0 hw

omit mΩ [StandardBorelSpace Ω] in
/-- **A stage of zero capacity does not change the transported field.** -/
theorem isChartTransport_loewner_zero_iff {c : Chart} {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {σ a k : ℝ} {g g' : DistOn upperHalfPlaneOpens} :
    IsChartTransport (c.loewner W 0) σ a k g g' ↔ IsChartTransport c σ a k g g' := by
  have hφ : ∀ φ' : LQGMetric.TestOn upperHalfPlaneOpens,
      (∫ w, (c.loewner W 0).2.2 ((c.loewner W 0).2.1 w) * φ' w) = ∫ w, c.2.2 (c.2.1 w) * φ' w := fun φ' => by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ H
    · simp only [loewner_zero_lift, loewner_zero_inv hW hW0 hw]
    · have : φ' w = 0 := image_eq_zero_of_notMem_tsupport (fun h => hw (φ'.tsupport_subset h))
      simp [this]
  unfold IsChartTransport
  simp only [image_loewner_zero_inv hW hW0, loewner_zero_fwd hW0, hφ]

omit mΩ [StandardBorelSpace Ω] in
theorem fwdMapInv_eq_zero_or_mem_H (W : ℝ → ℝ) (T : ℝ) (w : ℂ) : fwdMapInv W T w = 0 ∨ fwdMapInv W T w ∈ H := by
  unfold fwdMapInv
  split_ifs with h
  · exact Or.inr h.choose_spec.1.1.1
  · exact Or.inl rfl

omit mΩ [StandardBorelSpace Ω] in
theorem fwdMapInv_zero_driver_zero_at_zero {W : ℝ → ℝ} (hW0 : W 0 = 0) : fwdMapInv W 0 0 = 0 := by
  unfold fwdMapInv
  split_ifs with h
  · obtain ⟨⟨hz, -⟩, hz0⟩ := h.choose_spec.1
    have hid : fwdMap W 0 h.choose = h.choose := Exist.StagedLaw.fwdMap_zero_time hW0 _
    rw [hid] at hz0
    have hz' : (0 : ℂ).im > 0 := by
      have : h.choose.im > 0 := hz
      rwa [hz0] at this
    exact absurd hz' (by simp)
  · rfl

omit mΩ [StandardBorelSpace Ω] in
/-- **A stage of zero capacity does not change the physical tips read through the chart and the inversion.** -/
theorem tipAt_loewner_zero_iff {c : Chart} {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {V : ℝ≥0 → ℝ}
    {r : ℝ≥0} {z : ℂ} :
    ((c.loewner W 0).trans infinitySourceChart).tipAt V r z ↔ (c.trans infinitySourceChart).tipAt V r z := by
  have e : ∀ u : ℂ, u = 0 ∨ u ∈ H → (c.loewner W 0).2.1 (-u⁻¹) = c.2.1 (-u⁻¹) := by
    rintro u (rfl | hu)
    · simp only [inv_zero, neg_zero]
      change c.2.1 (fwdMapInv W 0 0) = c.2.1 0
      rw [fwdMapInv_zero_driver_zero_at_zero hW0]
    · exact loewner_zero_inv hW hW0 (GW2aPiece.neg_inv_mem_H hu)
  unfold Chart.tipAt
  have hf : (fun y : ℝ => ((c.loewner W 0).trans infinitySourceChart).2.1
      (fwdMapInv (fun x : ℝ => V x.toNNReal) (r : ℝ) ((y : ℂ) * Complex.I))) =
      fun y : ℝ => (c.trans infinitySourceChart).2.1
        (fwdMapInv (fun x : ℝ => V x.toNNReal) (r : ℝ) ((y : ℂ) * Complex.I)) := by
    funext y
    exact e _ (fwdMapInv_eq_zero_or_mem_H _ _ _)
  rw [hf]

/-! ### The charts of a run are conformal -/

omit mΩ [StandardBorelSpace Ω] in
/-- A launch whose stop is `⊤` keeps the chart. -/
theorem chart_launch_of_top (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (h : min t D.2 = ⊤) : (ExplState.launch s k D θ t).2.2.2.2.1 = s.2.2.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  simp only [h, ↓reduceIte]

omit mΩ [StandardBorelSpace Ω] in
/-- **The chart of a run whose launched pieces are regular is conformal, with a continuous lift.** -/
theorem isConformal_runChart (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ k, (∀ j < k, ∀ (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2)) →
      (ExplState.run κ b jumps spec D k).2.2.2.2.1.IsConformal ∧
        ContinuousOn (fun w => (ExplState.run κ b jumps spec D k).2.2.2.2.1.2.2
          ((ExplState.run κ b jumps spec D k).2.2.2.2.1.2.1 w)) H
  | 0, _ => ⟨Chart.isConformal_id.recenter spec.1, Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift⟩
  | k + 1, hreg => by
    obtain ⟨hc, hℓ⟩ := isConformal_runChart spec D k fun j hj => hreg j (Nat.lt_succ_of_lt hj)
    rcases hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k with _ | ⟨c, θ⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [ha]
      exact ⟨hc.recenter a, Chart.continuousOn_recenter_lift hℓ⟩
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [he]
      by_cases htop : min (instrTime spec k) (D k).2 = ⊤
      · rw [chart_launch_of_top _ _ _ _ _ htop]
        exact ⟨hc, hℓ⟩
      rw [chart_launch _ _ _ _ _ htop]
      obtain ⟨hU, hU0⟩ := (hreg k (Nat.lt_succ_self k) c θ hl).continuous_stoppedReal
      have hT : 0 ≤ ((min (instrTime spec k) (D k).2).toNNReal : ℝ) := NNReal.coe_nonneg _
      have hc₂ := Chart.isConformal_id.loewner hU hU0 hT
      have hℓ₂ := hc₂.continuousOn_lift_inv (Chart.continuousOn_lift_loewner hU hU0 hT)
      refine ⟨hc.loewner hU hU0 hT, ?_⟩
      rw [Chart.loewner_eq_trans]
      have hcomp := hℓ₂.add (hℓ.comp hc₂.1.continuousOn hc₂.2.1)
      refine hcomp.congr fun w hw => ?_
      exact IsChartTransport.trans_lift_inv hc (hc₂.2.1 hw)

end GW2aCont

end Theorem14

end InteractingSLE
