/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StagedEntranceChart
import InteractingSLE.Spec.Supplement.CondDriverBridge
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Supplement.KernelTower
import InteractingSLE.Impl.PiecewiseConstant

/-!
# The restart step for a launched piece of any staged history

Packet PROVE-STAGEDLOC2, staged-history instance (Theorem 1.4; PROVE-T14-SB8 §5 (a)). For a staged history `E` of any
program and a launched instruction `k` (angle `θ`, launch chart `c`), the entrance-history locality of a concatenated
own-history path `α` passes from the path frozen at the restart time `q₀` to the path frozen at `q₀ + m`, when after
`q₀` the path is the launch chart's inverse image of the piece's trace capped at own time `m`
(**`isEntranceHistoryLocal_frozenPath_staged`**). This is `StagedEntrance.isEntranceHistoryLocal_frozenPath_of_restart`
with:

* the chart data from the staged clause (`IsStagedHistory.exists_isCondFlowLineDriverOn`: under the staged conditional
  law the piece is a flow-line driver of the chart field, with chosen data `bc jc`), moved to Lemma 6.2's past by the
  kernel identity `hK`;
* the continuation hypothesis from Aux. lemma 56 for the capped piece under the conditional law
  (`measurable_entranceHist_of_isFlowLine_capped`) and the reading of the restarted path
  (`measurable_entranceHist_restart`), the launch chart being kernel-almost surely constant
  (`CondDriverBridge.ae_ae_launchChart_eq_of_le`).

**`isEntranceHistoryLocal_frozenPath_of_steps`** iterates the step over finitely many restart times (induction over
pieces).

The remaining inputs are per-piece path facts, stated as hypotheses: the kernel identity `hK` between the staged past
and the stopped path history (proved for the strip system in `StagedEntranceStripPast`), the frontier of the launch
chart's domain on the old path, a continuous version `ηc` of the capped chart trace staying in `ℍ` and its field
determination under the conditional law, and the concatenation identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Restart

namespace StagedEntrance

namespace Staged

open Sec6 Exist.Staged

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The restart step for a launched piece of a staged history** (Theorem 1.4's staged paths, one piece at a time).
Let `E` be a staged history of a GFF `h` with data `b` (harmonic extension `u₀`), and `k` an instruction almost surely
launched at angle `θ` in the conformal chart `c` (with locally integrable lift). Let `α` be a continuous path from
`x ∉ ℍ` such that

* (past) `α` frozen at the rational restart time `q₀` is field-determined and entrance-history local, Lemma 6.2's past
  of `α` at `q₀` has the same regular conditional laws as the staged past before `k` (`hK`), and the frontier of each
  chart domain in `ℍ` lies on the old path `α([0, q₀])`;
* (piece) `ηc` is a continuous version, from `0`, of the piece's trace `β` capped at own time `m` (and at its lifetime),
  determined under the conditional law by the chart field, staying in `ℍ` at positive times, and after `q₀` the path
  frozen at `q₀ + m` is `inv ∘ ηc`.

Then `α` frozen at `q₀ + m` is entrance-history local for the centred field. -/
theorem isEntranceHistoryLocal_frozenPath_staged (hκ : 0 < κ) (hκ4 : κ < 4) (hh : IsGFFWithBoundaryData P h b jumps)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) (θ : ℝ)
    {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hxH : x ∉ H) (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = x)
    (hαm : ∀ t, Measurable fun ω => α ω t) {q₀ : ℚ≥0} (m : ℝ≥0)
    (hdet₀ : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => frozenPath (α ω) q₀ t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hloc₀ : IsEntranceHistoryLocal (fun ω => frozenPath (α ω) q₀) (WholeField.centredField h u₀) P)
    (hK : ∀ᵐ ω₀ ∂P, condExpKernel P (_root_.InteractingSLE.pastSigma κ b jumps spec E k) ω₀ =
      condExpKernel P (StagedEntrance.pastSigma α q₀) ω₀)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hℓ : ∀ ω, LocallyIntegrableOn (fun w => (c ω).2.2 ((c ω).2.1 w)) H)
    (hlaunch : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c ω, θ))
    (hfr : ∀ ω, ∀ z ∈ H, z ∈ closure ((c ω).dom : Set ℂ) → z ∉ (c ω).dom → z ∈ α ω '' Icc 0 q₀)
    {β ηc : Ω → ℝ≥0 → ℂ} (hηc : ∀ ω, Continuous (ηc ω)) (hηm : ∀ t, Measurable fun ω => ηc ω t)
    (hη0 : ∀ ω, ηc ω 0 = 0) (htrβ : ∀ᵐ ω ∂P, IsGeneratingTrace (E k ω).1 (E k ω).2 (β ω))
    (hηβ : ∀ᵐ ω ∂P, ∀ t, ηc ω t = β ω (capTime m (E k ω).2 t))
    (hdetη : ∀ᵐ ω₀ ∂P, ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => ηc ω t) =ᵐ[condExpKernel P (StagedEntrance.pastSigma α q₀) ω₀]
        fun ω => f (Chart.chartTransport (hc ω₀) 1 0 (chiC κ) (h ω)))
    (hcat : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → ηc ω s ∈ H ∧
      frozenPath (α ω) ((q₀ : ℝ≥0) + m) ((q₀ : ℝ≥0) + s) = (c ω).2.1 (ηc ω s)) :
    IsEntranceHistoryLocal (fun ω => frozenPath (α ω) ((q₀ : ℝ≥0) + m)) (WholeField.centredField h u₀) P := by
  classical
  have hpast : StagedEntrance.pastSigma α (q₀ : ℝ≥0) ≤ mΩ := pastSigma_le hαm
  obtain ⟨bc, jc, hcond⟩ := hE.exists_isCondFlowLineDriverOn k θ
  -- the chart field and the harmonic extension of its data
  let h'' : Ω → Ω → DistOn upperHalfPlaneOpens := fun ω₀ ω => Chart.chartTransport (hc ω₀) 1 0 (chiC κ) (h ω)
  let u' : Ω → ℂ → ℝ := fun ω₀ => Classical.epsilon fun u : ℂ → ℝ => IsBoundedHarmonicExtension (bc ω₀) (jc ω₀) u
  have hu' : ∀ ω₀, IsPiecewiseConstantBoundaryData (bc ω₀) (jc ω₀) →
      IsBoundedHarmonicExtension (bc ω₀) (jc ω₀) (u' ω₀) := fun ω₀ hp => by
    obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hp
    exact Classical.epsilon_spec (p := fun u : ℂ → ℝ => IsBoundedHarmonicExtension (bc ω₀) (jc ω₀) u) ⟨u, hu⟩
  -- the staged clause under Lemma 6.2's conditional laws
  have hst : ∀ᵐ ω₀ ∂P, IsPiecewiseConstantBoundaryData (bc ω₀) (jc ω₀) ∧
      IsFlowLineDriver κ (bc ω₀) (jc ω₀) θ (condExpKernel P (StagedEntrance.pastSigma α q₀) ω₀) (h'' ω₀)
        (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) := by
    filter_upwards [hcond, hlaunch, hK] with ω₀ h1 hl h2
    have hlc : Theorem14.SB.launchChart κ b jumps spec (fun j => E j ω₀) k = c ω₀ := by
      simp only [Theorem14.SB.launchChart, hl, Option.elim]
    obtain ⟨hbp, h', ht, hfl⟩ := h1 ⟨c ω₀, hl⟩
    rw [hlc] at ht
    have e : h' = h'' ω₀ := funext fun ω => (ht ω).eq_chartTransport (hc ω₀) (hℓ ω₀)
    rw [e, h2] at hfl
    exact ⟨hbp, hfl⟩
  -- the a.s. facts under Lemma 6.2's conditional laws
  have hT1 := KernelTower.ae_ae_condExpKernel_of_ae hpast htrβ
  have hT2 := KernelTower.ae_ae_condExpKernel_of_ae hpast hηβ
  have hT3 := KernelTower.ae_ae_condExpKernel_of_ae hpast hcat
  have hT4 := KernelTower.ae_ae_condExpKernel_of_ae hpast hlaunch
  have hT5 : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (StagedEntrance.pastSigma α q₀) ω₀),
      Theorem14.SB.launchChart κ b jumps spec (fun j => E j ω) k =
        Theorem14.SB.launchChart κ b jumps spec (fun j => E j ω₀) k := by
    filter_upwards [Theorem14.CondDriverBridge.ae_ae_launchChart_eq_of_le (P := P) spec (fun j _ => hreg j)
      (hE.2.1 k) le_rfl, hK] with ω₀ h1 h2
    rw [← h2]
    exact h1
  have hcc : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (StagedEntrance.pastSigma α q₀) ω₀), c ω = c ω₀ := by
    filter_upwards [hT4, hT5, hlaunch] with ω₀ h4 h5 hl₀
    filter_upwards [h4, h5] with ω hl he
    have e₁ : Theorem14.SB.launchChart κ b jumps spec (fun j => E j ω) k = c ω := by
      simp only [Theorem14.SB.launchChart, hl, Option.elim]
    have e₀ : Theorem14.SB.launchChart κ b jumps spec (fun j => E j ω₀) k = c ω₀ := by
      simp only [Theorem14.SB.launchChart, hl₀, Option.elim]
    rw [← e₁, ← e₀, he]
  -- the restart step
  refine isEntranceHistoryLocal_frozenPath_of_restart (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀)
    hxH hαc hα0 hαm (t₀ := (q₀ : ℝ≥0)) le_self_add hdet₀ hloc₀ hc hfr
    (h' := fun ω₀ => WholeField.centredField (h'' ω₀) (u' ω₀))
    (m := fun ω₀ φ => SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀
      (Chart.pushTest (hc ω₀) φ) + chiC κ * Chart.liftDist (c ω₀) φ -
        SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (u' ω₀) φ) ?_ ?_ ?_
  · refine Eventually.of_forall fun ω₀ φ => Eventually.of_forall fun ω => ?_
    have e1 : h'' ω₀ ω φ = 1 * h ω (Chart.pushTest (hc ω₀) φ) + 0 * Chart.oneDist φ +
        chiC κ * Chart.liftDist (c ω₀) φ := Chart.chartTransport_apply' _ _ _ _ _ _
    simp only [WholeField.centredField, sub_apply, e1]
    ring
  · filter_upwards [hst] with ω₀ hω₀
    exact isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData
      (Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hω₀.1 hω₀.2) (hu' ω₀ hω₀.1)
  · filter_upwards [hst, hdetη, hT1, hT2, hT3, hcc, ae_ae_past_eq hαc hαm (q₀ : ℝ≥0)] with ω₀ hω₀ hd h1 h2 h3 h4 h5
      U hUH hdisj G' hG' hd'
    obtain ⟨hbp, hfl⟩ := hω₀
    have hgff := Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hbp hfl
    have hfl' : IsFlowLine κ (bc ω₀) (jc ω₀) 0 θ (condExpKernel P (StagedEntrance.pastSigma α q₀) ω₀) (h'' ω₀) β
        (fun ω => (E k ω).2) := by
      obtain ⟨h₃, 𝓕, VL, VR, B, ht, hC⟩ := hfl
      refine ⟨h₃, 𝓕, fun t ω => (E k ω).1 t, VL, VR, B, ht, hC, ?_⟩
      filter_upwards [h1] with ω hω
      simpa only [Complex.ofReal_zero, sub_zero] using hω
    have hdet' : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => ηc ω t) =ᵐ[condExpKernel P (StagedEntrance.pastSigma α q₀) ω₀]
          fun ω => f (WholeField.centredField (h'' ω₀) (u' ω₀) ω) := fun t => by
      obtain ⟨f, hf, hfe⟩ := hd t
      refine ⟨fun X => f (X + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (u' ω₀)),
        hf.comp (Coupling.measurable_add_distOnConst _), ?_⟩
      filter_upwards [hfe] with ω hω
      simp only [hω, WholeField.centredField, sub_add_cancel, h'']
    have hη0' : ∀ ω, ηc ω 0 ∉ H := fun ω hH => by
      have h0 : (0 : ℝ) < (ηc ω 0).im := hH
      rw [hη0, Complex.zero_im] at h0
      exact lt_irrefl _ h0
    have hβ := measurable_entranceHist_of_isFlowLine_capped hκ hκ4 hbp hgff hfl' (hu' ω₀ hbp) m hηc hηm hη0' h2
      hdet' (MarkovChart.chartPreOpens (hc ω₀) U) (MarkovChart.chartPre_subset_H (c ω₀) U) G' hG' hd'
    refine measurable_entranceHist_restart (hc ω₀) (a := α ω₀) hdisj ?_ hβ
    filter_upwards [h3, h4, h5] with ω hω hcω hpω
    refine ⟨fun s hs => ?_, hη0' ω, fun s hs => ?_⟩
    · rw [frozenPath_of_le (hs.trans le_self_add)]
      exact hpω s hs
    · obtain ⟨hH, he⟩ := hω s hs
      rw [← hcω]
      exact ⟨hH, he⟩

/-! ### The base case: the empty past at time `0` -/

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **A path that does not depend on the sample is entrance-history local** (its marked history is deterministic). -/
theorem isEntranceHistoryLocal_of_const [IsFiniteMeasure P] {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    {η : Ω → ℝ≥0 → ℂ} (γ : ℝ≥0 → ℂ) (hη : ∀ ω, η ω = γ) : IsEntranceHistoryLocal η X P := by
  intro U G _ hG _
  refine condIndepEv_of_le_aeSigma ((LocalSets.measurable_markovCompl hG).comp hXm).comap_le
    (hG.comp hXm).comap_le (MeasurableSpace.generateFrom_le fun s hs => ?_)
  obtain ⟨B, -, rfl⟩ := hs
  have e : {ω | AvoidsUpTo (η ω) (firstEntrance U (pathCoord (η ω))) U} ∩
      (fun ω => histOf (pathCoord (η ω)) (firstEntrance U (pathCoord (η ω)))) ⁻¹' B =
      {_ω | AvoidsUpTo γ (firstEntrance U (pathCoord γ)) U ∧
        histOf (pathCoord γ) (firstEntrance U (pathCoord γ)) ∈ B} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, hη]
    rfl
  rw [e]
  by_cases hp : AvoidsUpTo γ (firstEntrance U (pathCoord γ)) U ∧
      histOf (pathCoord γ) (firstEntrance U (pathCoord γ)) ∈ B
  · rw [eq_univ_of_forall fun _ => hp, ← compl_empty]
    exact MeasurableSpace.measurableSet_compl _ _ (MeasurableSpace.measurableSet_empty _)
  · rw [eq_empty_of_forall_notMem fun _ h => hp h]
    exact MeasurableSpace.measurableSet_empty _

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem frozenPath_zero_eq {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hα0 : ∀ ω, α ω 0 = x) (ω : Ω) :
    frozenPath (α ω) 0 = fun _ => x :=
  funext fun t => by simp only [frozenPath, min_eq_right zero_le, hα0]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- `hloc₀` at the restart time `0`. -/
theorem isEntranceHistoryLocal_frozenPath_zero [IsFiniteMeasure P] {X : Ω → DistOn upperHalfPlaneOpens}
    (hXm : Measurable X) {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hα0 : ∀ ω, α ω 0 = x) :
    IsEntranceHistoryLocal (fun ω => frozenPath (α ω) 0) X P :=
  isEntranceHistoryLocal_of_const hXm _ (frozenPath_zero_eq hα0)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- `hdet₀` at the restart time `0`. -/
theorem frozenPath_zero_det {X : Ω → DistOn upperHalfPlaneOpens} {α : Ω → ℝ≥0 → ℂ} {x : ℂ}
    (hα0 : ∀ ω, α ω 0 = x) (t : ℝ≥0) :
    ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => frozenPath (α ω) 0 t) =ᵐ[P] fun ω => f (X ω) :=
  ⟨fun _ => x, measurable_const, Eventually.of_forall fun ω => by
    show frozenPath (α ω) 0 t = x
    rw [frozenPath_zero_eq hα0]⟩

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- Lemma 6.2's past of a path at time `0` is trivial. -/
theorem pastSigma_zero_eq_bot {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hα0 : ∀ ω, α ω 0 = x) :
    StagedEntrance.pastSigma α 0 = ⊥ := by
  have e : (fun ω (_ : Fin 1) => histOf (pathCoord (frozenPath (α ω) 0)) ((0 : ℝ≥0) : ℝ≥0∞)) =
      fun _ _ => histOf (pathCoord fun _ => x) ((0 : ℝ≥0) : ℝ≥0∞) := by
    funext ω _
    rw [frozenPath_zero_eq hα0]
  change MeasurableSpace.comap _ _ = ⊥
  rw [e]
  exact MeasurableSpace.comap_const _

/-- `hK` at the first instruction and the restart time `0`: both pasts are trivial. -/
theorem ae_condExpKernel_pastSigma_zero_eq {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hα0 : ∀ ω, α ω 0 = x) :
    ∀ᵐ ω₀ ∂P, condExpKernel P (_root_.InteractingSLE.pastSigma κ b jumps spec E 0) ω₀ =
      condExpKernel P (StagedEntrance.pastSigma α ((0 : ℚ≥0) : ℝ≥0)) ω₀ := by
  refine Eventually.of_forall fun ω₀ => ?_
  rw [Theorem14.GW1.pastSigma_zero_eq_bot, NNRat.cast_zero, pastSigma_zero_eq_bot hα0]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Finitely many pieces** (induction over the restart times). If the path frozen at the first restart time `T 0` is
entrance-history local, the path is field-determined at every time, and each restart step from `T n` to `T (n + 1)`
preserves locality (e.g. by `isEntranceHistoryLocal_frozenPath_staged` for the piece launched at `T n`), then the path
frozen at every `T n` is entrance-history local. -/
theorem isEntranceHistoryLocal_frozenPath_of_steps {X : Ω → DistOn upperHalfPlaneOpens} {α : Ω → ℝ≥0 → ℂ}
    (T : ℕ → ℝ≥0) (h0 : IsEntranceHistoryLocal (fun ω => frozenPath (α ω) (T 0)) X P)
    (hstep : ∀ n, IsEntranceHistoryLocal (fun ω => frozenPath (α ω) (T n)) X P →
      IsEntranceHistoryLocal (fun ω => frozenPath (α ω) (T (n + 1))) X P) (n : ℕ) :
    IsEntranceHistoryLocal (fun ω => frozenPath (α ω) (T n)) X P := by
  induction n with
  | zero => exact h0
  | succ n ih => exact hstep n ih

end Staged

end StagedEntrance

end Restart

end InteractingSLE
