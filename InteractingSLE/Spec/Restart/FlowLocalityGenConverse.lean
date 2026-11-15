/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowLocalityGenClock

/-!
# Flow locality with a general agreement set: the converse assembly

Packet PROVE-G7A-LOC. The explicit-shift (L1) with a general agreement set, from

* **`ShiftKernelGenStatement`** (named input): the per-stop Cameron–Martin identification of Lemma G3 / Corollary
  G7a with every born pocket retained — under the tilt `Q* = k e^{−Λ} · Q₀`, at every stop before the buffer exit,
  the shifted chart field has the reference (`bR`) word's kernel off the filled hull. For buffers over one
  interval this is the proved `FlowStopIdentCMI.ae_condExp_shift_eq_ref`; in general the hull may contain part of
  the source `F.src`;
* `FlowStopIdentCMI.CMIXHullLocalityLimitStatement` (PROVE-L1-CMIC's remaining Gaussian hull-limit input, unchanged);

and the proved clock (`GSetting.exists_clock`). Contents: `GClock.isCouplingCharFun`, `GClock.isLocalSet_terminal`,
`GSetting.isLocalSet_chartField`, `GClock.isLocalSet_tilt`, the zero-exit case, `GClock.exists_isStoppedFlowLine`,
the statement `FlowLineStopIdentGStatement` (as `FlowStopIdentCMI.FlowLineStopIdentCMIVStatement` without the
interval) and **`flowLineStopIdentGStatement_of_kernel`**.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowLocalityGen
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open Sec7.PocketTraversal
open FlowStopIdentCMI StoppedExtend FlowStopIdentG FlowStopIdentCM

/-! ### The named input: the per-stop identification with retained pockets -/

/-- **Named input: the per-stop Cameron–Martin identification with every born pocket retained** (Corollary G7a's
proof, supplement p. 499: "the projection formula applies componentwise with every born pocket retained"; Aux.
lemma 97's proof, p. 327). In the general setting `D`, at a stop `τ` of the original driving filtration before the
buffer exit, for a continuous driver `W₁` with the path data at `τ` (agreement with the original driver past `τ`,
the source marks at its geometric images, the hulls filled by a trace), under the tilt `Q* = k e^{−Λ} · Q₀` the
shifted chart field `h' + T_y` has, off the filled hull of `W₁` at `τ`, the kernel of the reference (`bR`) word.
For buffers over one interval of `O` this is `FlowStopIdentCMI.ae_condExp_shift_eq_ref`. -/
def ShiftKernelGenStatement : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (D : GSetting S) (τ : S → WithTop ℝ≥0) (hτ : IsStoppingTime D.driving τ),
    (∀ᵐ ω ∂D.Q₀, (τ ω : ℝ≥0∞) < RLC.exitTime D.V (D.Γ ω) (D.U ω)) →
    ∀ W₁ : ℝ≥0 → S → ℝ, (∀ᵐ ω ∂D.Q₀, StopPathData D.b D.J D.y univ D.W₀ W₁ D.VL₀ D.VR₀ τ ω) →
    ∀ uR : S → ℂ → ℝ, (∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR D.y D.θ) (flowLineRhoR D.κ D.bR D.JR D.y D.θ)
        (fun i => geomL (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXL D.bR D.JR D.y i))
        (fun j => geomR (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXR D.bR D.JR D.y j)))
      (forceJumpSet
        (fun i => geomL (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXL D.bR D.JR D.y i))
        (fun j => geomR (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXR D.bR D.JR D.y j)))
      (uR ω)) →
    ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂D.tilt,
      Disjoint (tsupport φ) (fwdHull (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)) →
      D.tilt[fun ω' => Complex.exp (Complex.I * (D.chartField ω' φ : ℂ)) | hτ.measurableSpace] ω =
        LocalExt.cfVal (∫ z, couplingMean D.κ (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (uR ω) z * φ z)
          (loewnerGreenEnergy (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) φ)

/-! ### The clock's clauses -/

namespace GClock
variable {S : Type u} [MeasurableSpace S] {D : GSetting S} (C : GClock D)

/-- The per-stop identification gives the reference kernel for the clock. -/
theorem isCouplingCharFun (hK : ShiftKernelGenStatement.{u}) : Coupling.MartMeans.IsCouplingCharFun
    D.κ (flowLineRhoL D.κ D.bR D.JR D.y D.θ) (flowLineRhoR D.κ D.bR D.JR D.y D.θ)
    D.tilt D.driving C.base.W (geomLW C.base.W fun _ => flowLineXL D.bR D.JR D.y)
    (geomRW C.base.W fun _ => flowLineXR D.bR D.JR D.y) C.base.e D.chartField := by
  classical
  let _ := D.Q₀_prob
  let _ := D.tilt_prob
  intro τ hτ hτe uR huR φ
  have hτe₀ := D.tilt_equivalent.2.ae_le hτe
  have hτx : ∀ᵐ ω ∂D.Q₀, (τ ω : ℝ≥0∞) < RLC.exitTime D.V (D.Γ ω) (D.U ω) := by
    filter_upwards [hτe₀, C.base.ae_exit] with ω hω he
    rwa [he] at hω
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR D.y D.θ)
        (flowLineRhoR D.κ D.bR D.JR D.y D.θ)
        (fun i => geomL (Ito.rpath (C.base.W · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)
          (flowLineXL D.bR D.JR D.y i))
        (fun j => geomR (Ito.rpath (C.base.W · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)
          (flowLineXR D.bR D.JR D.y j)))
      (forceJumpSet
        (fun i => geomL (Ito.rpath (C.base.W · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)
          (flowLineXL D.bR D.JR D.y i))
        (fun j => geomR (Ito.rpath (C.base.W · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)
          (flowLineXR D.bR D.JR D.y j))) (uR ω) := by
    intro ω
    have hr : Bessel.realPath C.base.W ω = Ito.rpath (C.base.W · ω) := rfl
    have hl : Bessel.realPath (fun t ω => -C.base.W t ω) ω =
        (fun s => -Ito.rpath (C.base.W · ω) s) := rfl
    simpa only [geomLW, geomRW, geomL, geomR, hr, hl, Ito.rpath,
      Real.toNNReal_coe] using huR ω
  exact hK D τ hτ hτx C.base.W (C.base.pathData τ hτ hτe₀) uR hu φ

/-- **Terminal hull locality of the original field** through the exit, at stops of the original driving filtration
(`FlowStopIdentCMI.cmiWTerminalHullLocalityStatement_of_hullLimit`'s proof, with the source clock). -/
theorem isLocalSet_terminal (hlimit : CMIXHullLocalityLimitStatement.{u}) {τ : S → WithTop ℝ≥0}
    (hs : IsStoppingTime D.driving τ) (hτe : ∀ᵐ ω ∂D.Q₀, (τ ω : ℝ≥0∞) ≤ C.base.e ω ∧ τ ω ≠ ⊤) :
    IsLocalSet (fun ω => fwdHull (Ito.rpath (C.base.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.h' D.Q₀ := by
  let _ := D.Q₀_prob
  have hτf : ∀ᵐ ω ∂D.Q₀, τ ω ≠ ⊤ := hτe.mono fun _ h => h.2
  have hs' : IsStoppingTime D.driving fun ω => (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) :=
    Coupling.isStoppingTime_untopD hs hτf
  let s : ℕ → S → ℝ≥0 := fun n ω => min ((τ ω).untopD 0) (C.base.announce n ω)
  let u₀ := LocalExt.bheAt D.κ (flowLineRhoL D.κ D.b D.J D.y D.θ)
    (flowLineRhoR D.κ D.b D.J D.y D.θ) (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y)
  have hu₀ := LocalExt.isBoundedHarmonicExtension_bheAt D.κ
    (flowLineRhoL D.κ D.b D.J D.y D.θ) (flowLineRhoR D.κ D.b D.J D.y D.θ)
    (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y)
  have hH : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) QuantumZipper.H :=
    WholeField.isHarmonicDistOn_smoothDist hu₀.1
  have hloc : ∀ n, IsLocalSet (fun ω => fwdHull (Ito.rpath (C.base.W · ω)) (s n ω))
      (WholeField.centredField D.h' u₀) D.Q₀ := by
    intro n
    have hsn : IsStoppingTime D.driving fun ω => (s n ω : WithTop ℝ≥0) := by
      simpa only [s, WithTop.coe_min] using hs'.min (C.base.announcing.1 n)
    have hlt : ∀ᵐ ω ∂D.Q₀, (s n ω : ℝ≥0∞) < C.base.e ω :=
      (C.base.announcing.2.2.1 n).mono fun ω h =>
        (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt h
    have hl := C.base.isLocalSet_original_of_lt hsn hlt
    simp only [WithTop.untopD_coe] at hl
    exact WholeField.IsLocalSet.sub_dist hl hH
  have hlim : ∀ᵐ ω ∂D.Q₀, Tendsto (fun n => (s n ω : ℝ≥0∞)) atTop
      (𝓝 (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞)) := by
    filter_upwards [RetAux79.ae_tendsto_of_isAnnouncingSeq C.base.announcing, hτe] with ω ht hτeω
    have hle : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) ≤ C.base.e ω := by
      change (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤ (C.base.e ω : WithTop ℝ≥0)
      rw [Coupling.coe_untopD_of_ne_top hτeω.2]
      exact hτeω.1
    simpa only [s, ENNReal.coe_min, min_eq_left hle] using
      (tendsto_const_nhds (x := (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞))).min ht
  have hl := hlimit D.Q₀ (WholeField.centredField D.h' u₀)
    (WholeField.isZeroBoundaryGFF_centredField D.coupling hu₀)
    C.base.W C.base.zero C.base.continuous s (fun ω => (τ ω).untopD 0)
    (fun ω => monotone_const.min (C.base.announcing.2.1 ω)) (fun _ _ => min_le_left _ _) hlim hloc
  have hadd := Coupling.IsLocalSet.add_dist hl hH
  simpa only [WholeField.centredField, sub_add_cancel] using hadd

end GClock

namespace GSetting
variable {S : Type u} [MeasurableSpace S] (D : GSetting S)

/-- Any local set of the original chart field remains local for the shifted chart field under the tilt
(`FlowStopIdentCMI.CMIVSetting.isLocalSet_chartField`'s proof; no interval is used). -/
theorem isLocalSet_chartField {A : S → Set ℂ} (hloc : IsLocalSet A D.h' D.Q₀) :
    IsLocalSet A D.chartField D.tilt := by
  let _ := D.Q₀_prob
  let c : ℝ := D.θ * QuantumZipper.chiC D.κ
  let I₀ : ℝ := ∫ z, D.F.src z
  let s' := fun n => chartTest D.y (D.s n)
  let Λ' := fun ω => D.Λ ω + c * I₀
  let k' := D.k * Real.exp (c * I₀)
  have hs : ∀ n z, |s' n z| ≤ |(D.F.shift D.y).src z| := fun n z => by
    change |chartTest D.y (D.s n) z| ≤ |(D.F.shift D.y).src z|
    rw [chartTest_apply, CMCut.src_shift]
    exact D.s_bound n (z + D.y)
  have hslim : ∀ z, Tendsto (fun n => s' n z) atTop (𝓝 ((D.F.shift D.y).src z)) := fun z => by
    simp only [s', chartTest_apply, CMCut.src_shift]
    exact D.s_limit _
  have hints : ∀ n, (∫ z, s' n z) = ∫ z, D.s n z := fun n => by
    simp only [s', chartTest_apply]
    exact integral_add_right_eq_self (fun z => D.s n z) (D.y : ℂ)
  have hI : Tendsto (fun n => ∫ z, D.s n z) atTop (𝓝 I₀) :=
    tendsto_integral_of_dominated_convergence (fun z => |D.F.src z|)
      (fun n => (D.s n).continuous.aestronglyMeasurable) D.F.integrable_src.abs
      (fun n => ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact D.s_bound n z)
      (ae_of_all _ D.s_limit)
  have hΛ : ∀ᵐ ω ∂D.Q₀, Tendsto (fun n => D.h' ω (s' n)) atTop (𝓝 (Λ' ω)) := by
    filter_upwards [D.pairing_limit] with ω hω
    have he : ∀ n, D.h' ω (s' n) = D.H₀ ω (D.s n) + c * ∫ z, s' n z := fun n =>
      D.translate ω (D.s n) (s' n) fun z => chartTest_apply D.y (D.s n) z
    simp only [he, hints]
    exact hω.add (hI.const_mul c)
  have hk : 0 < k' := mul_pos D.k_pos (Real.exp_pos _)
  have hdens : (fun ω => ENNReal.ofReal (k' * Real.exp (-Λ' ω))) =
      fun ω => ENNReal.ofReal (D.k * Real.exp (-D.Λ ω)) := by
    funext ω
    congr 1
    simp only [k', Λ', neg_add, Real.exp_add]
    rw [show D.k * Real.exp (c * I₀) * (Real.exp (-D.Λ ω) * Real.exp (-(c * I₀))) =
      D.k * Real.exp (-D.Λ ω) * (Real.exp (c * I₀) * Real.exp (-(c * I₀))) by ring,
      ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hprob : IsProbabilityMeasure (D.Q₀.withDensity fun ω => ENNReal.ofReal (k' * Real.exp (-Λ' ω))) := by
    rw [hdens]
    exact D.tilt_prob
  have hq : InnerProductSpace.HarmonicOnNhd (fun z => D.q (z + D.y)) H := fun z hz =>
    Exist.harmonicAt_comp_add_const (D.q_extension.1 _ (Exist.add_real_mem_H hz D.y))
  have h := isLocalSet_withDensity_cmiCut hloc D.coupling.2.1 (D.F.shift D.y) hs hslim hΛ hk hprob hq
  rw [hdens] at h
  exact h

/-- The physical shifted GFF, in the reference chart (`FlowStopIdentCMI.CMIVSetting.isGFFWithBoundaryData_chartField`'s
proof). -/
theorem isGFFWithBoundaryData_chartField : IsGFFWithBoundaryData D.tilt D.chartField
    (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR D.y D.θ)
      (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (flowLineXL D.bR D.JR D.y) (flowLineXR D.bR D.JR D.y))
    (forceJumpSet (flowLineXL D.bR D.JR D.y) (flowLineXR D.bR D.JR D.y)) := by
  let _ := D.Q₀_prob
  have hH := isGFFWithBoundaryData_shift D.b_pc D.F D.q_extension D.H₀_gff D.s_bound D.s_limit
    D.Λ_measurable D.pairing_limit
    (integrable_exp_neg_of_prob D.Λ_measurable D.k_pos D.tilt_prob) D.k_pos D.tilt_prob
  have hG := Exist.isGFFWithBoundaryData_flowField D.κ_pos D.bR_pc D.y D.θ hH
  have heq : (fun ω => Exist.flowField D.y (D.θ * QuantumZipper.chiC D.κ) (D.shiftedField ω)) =
      D.chartField := funext fun ω => (Lemma75Bridge.eq_flowField_of_isTranslateAddConst
        (D.translate_shift ω)).symm
  change IsGFFWithBoundaryData D.tilt
    (fun ω => Exist.flowField D.y (D.θ * QuantumZipper.chiC D.κ) (D.shiftedField ω)) _ _ at hG
  rwa [heq] at hG

/-- A zero-exit reference coupling needs no clock or tilt-locality input. -/
theorem exists_isStoppedFlowLine_zero :
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
      IsStoppedFlowLine D.κ D.bR D.JR D.y D.θ (D.tilt.prod ν)
        (fun p => D.shiftedField p.1) (fun p => D.Γ p.1) (fun _ => 0) := by
  let _ : IsProbabilityMeasure D.tilt := D.tilt_prob
  obtain ⟨ν, hν, 𝓦, β, hβ, -, -⟩ := ConverseBefore.exists_noiseBM
  have hμ : (D.tilt.prod ν).map Prod.fst = D.tilt := Measure.map_fst_prod.trans (by simp)
  have hH := D.isGFFWithBoundaryData_chartField
  have hHP : IsGFFWithBoundaryData (D.tilt.prod ν) (fun p => D.chartField p.1)
      (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR D.y D.θ)
        (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (flowLineXL D.bR D.JR D.y) (flowLineXR D.bR D.JR D.y))
      (forceJumpSet (flowLineXL D.bR D.JR D.y) (flowLineXR D.bR D.JR D.y)) := by
    refine ⟨hH.1.comp measurable_fst, fun u hu => ?_⟩
    have h := hH.2 u hu
    rw [← hμ] at h
    exact isZBGFFProcess_comp measurable_fst h
  refine ⟨ν, hν, fun p => D.chartField p.1, WholeField.prodFiltration ⊥ 𝓦,
    fun _ _ => 0, fun i _ _ => flowLineXL D.bR D.JR D.y i,
    fun j _ _ => flowLineXR D.bR D.JR D.y j, fun t p => β t p.2,
    fun p => D.translate_shift p.1,
    isStoppedHullCoupling_zero hHP (StoppedCont.isFilteredBrownianReal_prod_snd ⊥ hβ), ?_⟩
  have hg0 : ∀ᵐ ω ∂D.tilt,
      IsGeneratingTrace (fun _ => 0) 0 (fun t => D.Γ ω t - D.y) := by
    filter_upwards [D.tilt_equivalent.1.ae_le D.trace] with ω hg
    exact StoppedK2.isGeneratingTrace_congr (fun t ht => (not_lt_zero ht).elim)
      (LP.isGeneratingTrace_mono hg bot_le)
  exact ConverseBefore.ae_fst_of_ae (P₀ := ν) hg0

end GSetting

namespace GClock
variable {S : Type u} [MeasurableSpace S] {D : GSetting S} (C : GClock D)

/-- Tilted hull locality at finite reference-driving stops through the exit. -/
theorem isLocalSet_tilt (hlimit : CMIXHullLocalityLimitStatement.{u}) (τ : S → WithTop ℝ≥0)
    (hτ : IsStoppingTime (drivingFiltration D.tilt C.killed) τ)
    (hτe : ∀ᵐ ω ∂D.tilt, (τ ω : ℝ≥0∞) ≤ C.base.e ω ∧ τ ω ≠ ⊤) :
    IsLocalSet (fun ω => fwdHull (Ito.rpath (C.base.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.chartField D.tilt := by
  have hr : IsStoppingTime (drivingFiltration D.Q₀ C.killed) τ := by
    rwa [D.driving_tilt_eq C.killed] at hτ
  have hs : IsStoppingTime D.driving τ := fun t => C.driving_le t _ (hr t)
  exact D.isLocalSet_chartField (C.isLocalSet_terminal hlimit hs (D.tilt_equivalent.2.ae_le hτe))

/-- **The stopped reference flow line on the enlargement**, from the per-stop identification and the hull-limit
input (`FlowStopIdentCMI.CMIVClock.exists_isStoppedFlowLine`'s proof). -/
theorem exists_isStoppedFlowLine (hK : ShiftKernelGenStatement.{u}) (hlimit : CMIXHullLocalityLimitStatement.{u}) :
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
      StoppedExtend.IsStoppedFlowLine D.κ D.bR D.JR D.y D.θ (D.tilt.prod ν)
        (fun p => D.shiftedField p.1) (fun p => D.Γ p.1) (fun p => C.base.e p.1) := by
  let _ := D.Q₀_prob
  let _ : IsProbabilityMeasure D.tilt := D.tilt_prob
  let _ : D.driving.IsRightContinuous := by
    unfold GSetting.driving drivingFiltration usualAugmentation
    infer_instance
  let _ : D.toFake.driving.IsRightContinuous := by
    unfold CMIVSetting.driving drivingFiltration usualAugmentation
    infer_instance
  have hF := Theorem15.isOrderedForceWord_flowLine D.bR D.JR D.y
  have hpos : ∀ᵐ ω ∂D.tilt, 0 < C.base.e ω := D.tilt_equivalent.1.ae_le C.base.ae_pos
  have hinit : ∀ᵐ ω ∂D.tilt, 0 < C.base.e ω ∧
      ContinuousOn (C.base.W · ω) {t | (t : ℝ≥0∞) < C.base.e ω} ∧ C.base.W 0 ω = 0 ∧
      (∀ i, geomLW C.base.W (fun _ => flowLineXL D.bR D.JR D.y) i 0 ω = flowLineXL D.bR D.JR D.y i) ∧
      ∀ j, geomRW C.base.W (fun _ => flowLineXR D.bR D.JR D.y) j 0 ω = flowLineXR D.bR D.JR D.y j := by
    filter_upwards [hpos] with ω hω
    exact ⟨hω, (C.base.continuous ω).continuousOn, C.base.zero ω,
      fun i => geomLW_zero C.base.continuous C.base.zero (hF.2.1 i),
      fun j => geomRW_zero C.base.continuous C.base.zero (hF.2.2.2 j)⟩
  have hcf := C.isCouplingCharFun hK
  have hint := fun φ => Coupling.MartMeans2.integrable_apply_of_isCouplingCharFun
    hcf hinit φ ((LQGMetric.measurable_distOn_apply φ).comp D.measurable_chartField)
  have hgff := fun (u₀ : ℂ → ℝ) hu₀ => Sec7.Lemma71J.isZBGFFProcess_of_isCouplingCharFun
    (u₀ := u₀) hcf D.measurable_chartField hinit hu₀
  have hnull : ∀ A, MeasurableSet A → D.tilt A = 0 → MeasurableSet[D.driving 0] A :=
    fun A hA h0 => Ito.measurableSet_usualAugmentation_of_null hA (D.tilt_equivalent.2 h0) 0
  have hT := RetAux79.isAnnouncingSeq_of_absolutelyContinuous C.base.announcing le_rfl D.tilt_equivalent.1
  have hle : drivingFiltration D.tilt C.killed ≤ D.driving := by
    rw [D.driving_tilt_eq C.killed]
    exact C.driving_le
  have hσ := fun n => show IsStoppingTime (drivingFiltration D.tilt C.killed) (C.σ n) from by
    rw [D.driving_tilt_eq C.killed]
    exact C.σ_stopping n
  obtain ⟨ν, hν, 𝓕, B, hc⟩ := exists_stoppedHullCoupling_prod_of_clock D.κ_pos hF.2.1 hF.2.2.2
    hF.1 hF.2.2.1 C.base.zero C.base.continuous C.base.adapted C.base.stopping hnull hT D.measurable_chartField
    hint hgff hcf (D.tilt_equivalent.1.ae_le C.threshold) C.killed hle hσ C.σ_monotone
    (D.tilt_equivalent.1.ae_le C.σ_lt) (D.tilt_equivalent.1.ae_le C.σ_limit) (C.isLocalSet_tilt hlimit)
  refine ⟨ν, hν, fun p => D.chartField p.1, 𝓕, fun t p => C.base.W t p.1,
    fun i t p => geomLW C.base.W (fun _ => flowLineXL D.bR D.JR D.y) i t p.1,
    fun j t p => geomRW C.base.W (fun _ => flowLineXR D.bR D.JR D.y) j t p.1,
    B, fun p => D.translate_shift p.1, hc, ?_⟩
  exact ConverseBefore.ae_fst_of_ae (P₀ := ν) (D.tilt_equivalent.1.ae_le C.base.ae_generatingTrace)

end GClock

end InteractingSLE.Restart.FlowLocalityGen
