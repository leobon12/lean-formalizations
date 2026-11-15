/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VmSafe
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVmAd
import InteractingSLE.Spec.Supplement.SB2VmAd
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeAsm
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife
import InteractingSLE.Spec.Supplement.SBS3DwViAbs
import InteractingSLE.Spec.Supplement.SBS3DwViRed
import InteractingSLE.Spec.Supplement.SBS3DwVjEnt
import InteractingSLE.Spec.Supplement.SBS3DwVjJoint
import InteractingSLE.Spec.Supplement.SBS3DwVjRel
import InteractingSLE.Spec.Supplement.SBS3DwVkAsm
import InteractingSLE.Spec.Supplement.SBS3DwVkEnd
import InteractingSLE.Spec.Supplement.SBS3DwVkFam
import InteractingSLE.Spec.Supplement.SBS3DwVkFrz
import InteractingSLE.Spec.Supplement.SBS3DwVkLife
import InteractingSLE.Spec.Supplement.SBS3DwVkLink

/-!
# Successor of `SB2VmSafe` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VmSafe` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `measurableSet_safeLe`;
* `sb2DriverAdaptLeStatement`;
* `sb2LineVersionRStatement_of_endpointLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vm

open Lv Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw Supp8.Q3Stop
  Sec7.PocketTraversal Sec7.Lemma71C

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The safe event of the frozen driver for a closed set is an event of the completed line filtration.** -/
theorem measurableSet_safeLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) {a : ℝ≥0 → Ω → ℝ≥0∞}
    (ha : ∀ t, Measurable[D.lineFiltC HP t] (a t)) (hac : ∀ ω, Continuous fun t => a t ω)
    (ham : ∀ ω, Monotone fun t => a t ω)
    (hae : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal
        (ζ ω) t)
    {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0)))
    {W : ℝ≥0 → Ω → ℝ} {G : Set Ω} (hGm : MeasurableSet G) (hGnull : P Gᶜ = 0) (hWm : ∀ q, Measurable (W q))
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun q => W q ω)
    (hWoff : ∀ q ω, ω ∉ G ∩ D.event → W q ω = 0)
    (hWon : ∀ ω ∈ G ∩ D.event, ω ∈ launchSet κ b jumps E (k + 1) ∧ Ve.entT κ b jumps E k u η ζ ω < ζ ω ∧
      IsDrivenCurve (ρ ω) ∧ Sec7.Lemma71C.capLife (ρ ω) = Vk.relLife κ b jumps E k u η ζ ω ∧
      ∀ q : ℝ≥0, (q : ℝ≥0∞) < Vk.relLife κ b jumps E k u η ζ ω → W q ω = segDriver (ρ ω) q)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : ∀ t, Measurable[D.lineFiltC HP t] xL) (hxR : ∀ t, Measurable[D.lineFiltC HP t] xR)
    {K : Set ℂ} (hK : IsClosed K) (t : ℝ≥0) :
    MeasurableSet[D.lineFiltC HP t] {ω | a t ω < FCDet.thr ρL ρR W xL xR ω ∧
      Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)} := by
  classical
  obtain ⟨Eg, -, hEgsub, hEgae, hY⟩ := exists_goodReadingLe h13 hS3 HP I D ha hac ham hae hρ hGm hGnull hWm hW0
    hWc hWoff hWon
  set τ : Ω → ℝ≥0 := fun ω => (a t ω).toNNReal with hτdef
  have hτm : Measurable[D.lineFiltC HP t] τ := ENNReal.measurable_toNNReal.comp (ha t)
  set B : ℝ≥0 → Ω → ℝ := fun s ω => if ω ∈ Eg then W (min s (τ ω)) ω else 0 with hBdef
  have hBm : ∀ s, Measurable[D.lineFiltC HP t] (B s) := fun s =>
    measurable_stopped hWc hτm (Y := fun v => (Eg ∩ {ω | (v : ℝ≥0∞) ≤ a t ω}).indicator (W v))
      (fun v => hY v t)
      (fun v ω hω hv => by
        have hva : (v : ℝ≥0∞) ≤ a t ω := by
          by_cases htop : a t ω = ⊤
          · rw [htop]; exact le_top
          · rw [← ENNReal.coe_toNNReal htop]; exact ENNReal.coe_le_coe.2 hv
        exact indicator_of_mem (show ω ∈ Eg ∩ {ω | (v : ℝ≥0∞) ≤ a t ω} from ⟨hω, hva⟩) _)
      (fun v ω hω => indicator_of_notMem (fun h' => hω h'.1) _) s
  have hBc : ∀ ω, Continuous fun s => B s ω := fun ω => by
    by_cases hω : ω ∈ Eg
    · simp only [hBdef, hω, ↓reduceIte]
      exact (hWc ω).comp (continuous_id.min continuous_const)
    · simp only [hBdef, hω, ↓reduceIte]
      exact continuous_const
  -- the stopped driver's event
  have hSB : MeasurableSet[D.lineFiltC HP t] {ω | a t ω < FCDet.thr ρL ρR B xL xR ω ∧
      Disjoint K (fwdHull (QuantumZipper.drive 1 B ω) (τ ω : ℝ))} :=
    (measurableSet_lt (ha t) (measurable_thr_of_le ((D.lineFiltC HP).le t) ρL ρR hBc hBm (hxL t) (hxR t))).inter
      (Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand hBc hBm (measurable_coe_nnreal_real.comp hτm)
        (fun ω => (τ ω).2) hK)
  -- the event itself is ambient-measurable
  have hxL0 : Measurable xL := (hxL 0).mono ((D.lineFiltC HP).le 0) le_rfl
  have hxR0 : Measurable xR := (hxR 0).mono ((D.lineFiltC HP).le 0) le_rfl
  have hS : MeasurableSet {ω | a t ω < FCDet.thr ρL ρR W xL xR ω ∧
      Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)} := by
    have h1 := Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand (m := mΩ) hWc hWm
      (measurable_coe_nnreal_real.comp (ENNReal.measurable_toNNReal.comp ((ha t).mono ((D.lineFiltC HP).le t) le_rfl)))
      (fun ω => ((a t ω).toNNReal).2) hK
    simp only [drive_one] at h1
    exact (measurableSet_lt ((ha t).mono ((D.lineFiltC HP).le t) le_rfl)
      (measurable_thr_of_le le_rfl ρL ρR hWc hWm hxL0 hxR0)).inter h1
  refine Vf.lineFiltC_closed D HP t hS hSB ?_
  filter_upwards [hEgae] with ω hω
  apply propext
  show (a t ω < _ ∧ _) ↔ (a t ω < _ ∧ _)
  by_cases hev : ω ∈ D.event
  · have hωE := hω hev
    have hBW : ∀ s ≤ τ ω, W s ω = B s ω := fun s hs => by
      simp only [hBdef, hωE, ↓reduceIte, min_eq_left hs]
    have hhull : fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω : ℝ) =
        fwdHull (QuantumZipper.drive 1 B ω) (τ ω : ℝ) := by
      rw [drive_one]
      refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc ((hWc ω).comp continuous_real_toNNReal)
        ((hBc ω).comp continuous_real_toNNReal) (τ ω).2 fun r hr => hBW _ ?_
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
      exact hr.2
    have hthr : a t ω < FCDet.thr ρL ρR W xL xR ω ↔ a t ω < FCDet.thr ρL ρR B xL xR ω := by
      by_cases htop : a t ω = ⊤
      · rw [htop]; simp only [not_top_lt]
      · rw [← ENNReal.coe_toNNReal htop, ← not_le, ← not_le]
        exact not_congr (thr_le_iff_of_eqOn hWc hBc xL xR hBW)
    rw [hthr]
    show _ ∧ Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω : ℝ)) ↔ _
    rw [hhull]
  · have hW0' : ∀ s, W s ω = 0 := fun s => hWoff s ω fun h' => hev h'.2
    have hB0 : ∀ s, B s ω = 0 := fun s => by
      simp only [hBdef, show ω ∉ Eg from fun h' => hev (hEgsub h').2, ↓reduceIte]
    have hthr : FCDet.thr ρL ρR W xL xR ω = FCDet.thr ρL ρR B xL xR ω :=
      FCDet.thr_congr (fun s => by rw [hW0' s, hB0 s]) rfl rfl
    have hdr : QuantumZipper.drive 1 B ω = fun s : ℝ => W s.toNNReal ω := by
      rw [drive_one]; funext s; rw [hW0', hB0]
    rw [hthr, hdr]

/-- **`Vk.SB2DriverAdaptLeStatement` from Theorem 1.3 and S3.** -/
theorem sb2DriverAdaptLeStatement (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) : Vk.SB2DriverAdaptLeStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP _ I u₀ D a ha hac ham ha0 hae ρ W G hρm hρ hGm hGnull hWm hW0 hWc
    hWoff hWon
  have hword : ∀ t, Measurable[D.lineFiltC HP t] I.word := fun t =>
    (I.word_measurable.mono D.past_le_marks le_rfl).mono (D.marks_le_lineFiltC HP t) le_rfl
  refine ⟨stronglyAdapted_frozenLe h13 hS3 HP I D ha hac ham hae hρ hGm hGnull hWm hW0 hWc hWoff hWon,
    fun w _ φ t => ?_, fun w _ Fb t => ?_⟩
  · exact measurableSet_safeLe h13 hS3 HP I D ha hac ham hae hρ hGm hGnull hWm hW0 hWc hWoff hWon
      (typedRhoL w) (typedRhoR w) (fun t => measurable_cellXL (hword t) w) (fun t => measurable_cellXR (hword t) w)
      (isClosed_tsupport _) t
  · exact measurableSet_safeLe h13 hS3 HP I D ha hac ham hae hρ hGm hGnull hWm hW0 hWc hWoff hWon
      (typedRhoL w) (typedRhoR w) (fun t => measurable_cellXL (hword t) w) (fun t => measurable_cellXR (hword t) w)
      (Set.Finite.isClosed_biUnion Fb.finite_toSet fun _ _ => isClosed_closedBall) t

end

/-- **SB2(1)'s line version** (`Lv.SB2LineVersionRLeStatement`) from Theorem 1.3, S3, E7 and the relative endpoint
(`Vk.SB2DriverAdaptLeStatement` discharged). -/
theorem sb2LineVersionRStatement_of_endpointLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (hE7 : Vh.SB2RemainderLifeLeStatement.{u})
    (hEnd : Vk.SB2RelEndpointLeStatement.{u}) : Lv.SB2LineVersionRLeStatement.{u} :=
  Vk.sb2LineVersionRStatement_of_adaptLe h13 hS3 hE7 hEnd (sb2DriverAdaptLeStatement h13 hS3)


end InteractingSLE.Theorem14.SB.Vm
