/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripWallInputs
import InteractingSLE.WangWu.ReverseContactImgCode
import InteractingSLE.Spec.Zhan.WordsEscape
import InteractingSLE.Spec.Sec5.Lemma56Stages

/-!
# The continuation of a two-angle wall has a simple transient trace almost surely

Packet PROVE-STRIPSYS28, first half of `IsWallVersion`. Specification §7.4, proof of Aux. lemma 130
(`source/spec/p385-432.md`, p. 410): the continuation of an angle-varying path is, conditionally on the first prefix, a
flow line of the conditional field in the record chart; its word has noncolliding side partial sums, so by Remark 2.3
and Aux. lemma 7 it has infinite lifetime and a simple transient trace.

Ruling R51: an almost sure pathwise property under every regular conditional law passes to `P` only if it is a
measurable event. The event used here is the Borel one of Wang–Wu Lemma 2.10 (`WangWu.ImgDrv.GoodPath`: infinite
lifetime, the transient trace coding `RandRestart.traceSet`, and the rational window conditions `ImPosCond`, `SepCond`
on the measurable trace evaluations `LP.traceAt`), as a set of drivers (`goodPathSet`, `measurableSet_goodPathSet`).

* `ae_goodPath_of_isFlowLineDriver`: a flow-line driver (any measure) whose word has admissible side partial sums
  almost surely lies in `goodPathSet` (Remark 2.3 for `κ ≤ 4`, `Zhan.IsIntegratedSLEEvolution.ae_simple_trace`; Aux.
  lemma 7, `Zhan.aux7Statement`);
* `hasAdmissiblePartialSums_flowLine_of_heights`, `hasAdmissiblePartialSums_stopWord`: the restarted word of a
  two-angle path has admissible partial sums whenever `|θ − θ₀| ≤ π` and `b + θχ ∈ [−∞, −λ + πχ]` left,
  `[λ − πχ, ∞]` right (no reflection is needed: both the increasing and the decreasing change are covered);
* **`ae_goodPath_stage`**: the launched piece of a staged history lies in `goodPathSet` almost surely at a launch, when
  its stage word has admissible partial sums (`StripDet.ae_stageDrv_eq`'s kernel argument, then
  `Sec5.Lemma56Stages.ae_of_ae_condExpKernel` on the measurable event);
* **`ae_goodPath_one`**: the continuation of a two-angle staged history lies in `goodPathSet` almost surely.

No Theorem 1.2/1.3 and no `AdmCode.Theorem12ParamCond44Statement` (R43, R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripWall

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw Exist.StagedLaw.BoundaryWord AdmCode Sec4 QuantumZipper
open StripDet
open WangWu.ImgDrv (GoodPath goodPath_of_trace)

/-! ### The Borel set of drivers with a simple transient trace -/

/-- **The drivers with a simple transient generating trace**, as a set of (driver, lifetime) pairs: Wang–Wu's Borel
good-path event (`WangWu.ImgDrv.GoodPath`). -/
def goodPathSet : Set ((ℝ≥0 → ℝ) × ℝ≥0∞) := {e | GoodPath e.1 e.2}

theorem mem_goodPathSet {e : (ℝ≥0 → ℝ) × ℝ≥0∞} : e ∈ goodPathSet ↔ GoodPath e.1 e.2 := Iff.rfl

theorem measurableSet_goodPathSet : MeasurableSet goodPathSet := by
  have hline : ∀ s : ℝ, Measurable fun e : (ℝ≥0 → ℝ) × ℝ≥0∞ => LP.traceAt s.toNNReal e.1 := fun s =>
    (LP.measurable_traceAt _).comp measurable_fst
  have h1 : MeasurableSet {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | e.2 = ⊤} := measurable_snd (measurableSet_singleton ⊤)
  have h2 : MeasurableSet {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (e.1, (⊤ : ℝ≥0∞)) ∈ RandRestart.traceSet} :=
    (measurable_fst.prodMk measurable_const) RandRestart.measurableSet_traceSet
  have h3 : MeasurableSet
      {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | WangWu.ImPosCond (fun s : ℝ => LP.traceAt s.toNNReal e.1)} := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun a => Measurable.forall fun b => ?_)
    refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.exists fun m => ?_))
    refine Measurable.forall fun p => Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
    exact measurableSet_setOfPred.1
      (measurableSet_le measurable_const (Complex.measurable_im.comp (hline _)))
  have h4 : MeasurableSet
      {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | WangWu.SepCond (fun s : ℝ => LP.traceAt s.toNNReal e.1)} := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun a => Measurable.forall fun b =>
      Measurable.forall fun c => Measurable.forall fun d => ?_)
    refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const
      (Measurable.imp measurable_const (Measurable.exists fun m => ?_))))
    refine Measurable.forall fun p => Measurable.forall fun q => Measurable.imp measurable_const
      (Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const ?_)))
    exact measurableSet_setOfPred.1
      (measurableSet_le measurable_const ((hline _).sub (hline _)).norm)
  have e : goodPathSet = {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | e.2 = ⊤} ∩
      {e | (e.1, (⊤ : ℝ≥0∞)) ∈ RandRestart.traceSet} ∩
      {e | WangWu.ImPosCond (fun s : ℝ => LP.traceAt s.toNNReal e.1)} ∩
      {e | WangWu.SepCond (fun s : ℝ => LP.traceAt s.toNNReal e.1)} := by
    ext e
    simp only [goodPathSet, GoodPath, mem_inter_iff, mem_ofPred_eq, and_assoc]
  rw [e]
  exact ((h1.inter h2).inter h3).inter h4

/-- **A good path has a simple transient generating trace** (`WangWu.ImgDrv.GoodPath.trace`, in the `ℝ≥0`-indexed form):
an injective generating trace on `[0, ∞)`, in `ℍ` at positive times, tending to `∞`. -/
theorem exists_simple_trace_of_goodPath {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) (hg : GoodPath w ⊤) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨η, hη, htend, -, -, hP⟩ := hg.trace hwc hw0
  refine ⟨η, hη, fun s t hst => ?_, fun t ht => ?_, htend⟩
  · have h : (s : ℝ) = t := hP.inj (show (s : ℝ) ∈ Ici (0 : ℝ) from s.coe_nonneg)
      (show (t : ℝ) ∈ Ici (0 : ℝ) from t.coe_nonneg)
      (show η (s : ℝ).toNNReal = η (t : ℝ).toNNReal by rw [Real.toNNReal_coe, Real.toNNReal_coe]; exact hst)
    exact NNReal.coe_injective h
  · have h := hP.mem_H (t : ℝ) (by exact_mod_cast ht)
    simpa only [Real.toNNReal_coe] using h

/-! ### Flow-line drivers with admissible partial sums -/

/-- **A flow-line driver with noncolliding side partial sums is a good path almost surely** (Remark 2.3 for `κ ≤ 4`
and Aux. lemma 7): for a flow-line driver under any measure whose word has admissible side partial sums, almost surely
the lifetime is infinite and the driver has a simple transient generating trace (the Borel event `GoodPath`). -/
theorem ae_goodPath_of_isFlowLineDriver {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c : BoundaryWord} {θ : ℝ}
    (hadm : HasAdmissiblePartialSums κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} {Y : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ c.fn c.jumps θ Q Y W L)
    (hWc : ∀ ω, L ω = ⊤ → Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) :
    ∀ᵐ ω ∂Q, GoodPath (fun t => W t ω) (L ω) := by
  obtain ⟨h'', 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  filter_upwards [Zhan.IsIntegratedSLEEvolution.ae_simple_trace hκ hκ4.le hF hadm hC.1,
    Zhan.aux7Statement hκ hκ4.le _ _ _ _ Q 𝓕 W VL VR B L hF hadm hC.1] with ω h1 h2
  obtain ⟨hζ, -, η, hη, hinj, hH, -⟩ := h1
  rw [hζ]
  exact goodPath_of_trace (hWc ω hζ) (hW0 ω) hη hinj hH (h2.2.2 η hη)

/-- **Admissible partial sums of a flow-line word from the boundary heights**: `b + θχ ≤ −λ + πχ` left of `0` and
`b + θχ ≥ λ − πχ` right of `0`, off the jump candidates (Remark 4.1;
`Sec4.hasAdmissiblePartialSums_of_forall_not_mem`). -/
theorem hasAdmissiblePartialSums_flowLine_of_heights {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ) :
    HasAdmissiblePartialSums κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0)
      (flowLineXR b J 0) := by
  refine hasAdmissiblePartialSums_of_forall_not_mem hκ (insert 0 J) (fun x hx hxE _ => ?_) (fun x hx hxE _ => ?_)
  · have hxJ : x ∉ J := fun h => hxE (Finset.mem_insert_of_mem h)
    rw [Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hx.ne (by rwa [add_zero]), add_zero]
    exact hL x hx hxJ
  · have hx0 : x ≠ 0 := fun h => hxE (h ▸ Finset.mem_insert_self 0 J)
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hxJ : x ∉ J := fun h => hxE (Finset.mem_insert_of_mem h)
    rw [Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hxpos.ne' (by rwa [add_zero]), add_zero]
    exact hR x hxpos hxJ

/-- **The restarted word of a two-angle path has admissible partial sums**: if `|θ − θ₀| ≤ π` and the boundary word
`c` has `c + θχ ≤ −λ + πχ` left of `0` and `c + θχ ≥ λ − πχ` right of `0`, the angle-`θ` flow-line word of the stop
word `stopWord κ (c, θ₀, r)` has admissible side partial sums (its heights are `−λ − θ₀χ` or `c(x)`, `x < 0`, left of
the tip, `λ − θ₀χ` or `c(x)`, `x > 0`, right of it: `stopWord_fn_of_neg`, `stopWord_fn_of_pos`). -/
theorem hasAdmissiblePartialSums_stopWord {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : BoundaryWord) (θ₀ θ : ℝ)
    (r : RecData) (hθ : θ ≤ θ₀ + Real.pi) (hθ' : θ₀ ≤ θ + Real.pi)
    (hL : ∀ y : ℝ, y < 0 → y ∉ c.jumps → c.fn y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ c.jumps → sleLambda κ - Real.pi * chiC κ ≤ c.fn y + θ * chiC κ) :
    HasAdmissiblePartialSums κ (flowLineRhoL κ (stopWord κ (c, θ₀, r)).fn (stopWord κ (c, θ₀, r)).jumps 0 θ)
      (flowLineRhoR κ (stopWord κ (c, θ₀, r)).fn (stopWord κ (c, θ₀, r)).jumps 0 θ)
      (flowLineXL (stopWord κ (c, θ₀, r)).fn (stopWord κ (c, θ₀, r)).jumps 0)
      (flowLineXR (stopWord κ (c, θ₀, r)).fn (stopWord κ (c, θ₀, r)).jumps 0) := by
  have hχ := chiC_pos hκ hκ4
  refine hasAdmissiblePartialSums_flowLine_of_heights hκ (stopWord κ (c, θ₀, r)).isPiecewiseConstantBoundaryData θ
    (fun y hy _ => ?_) (fun y hy _ => ?_)
  · rcases stopWord_fn_of_neg hκ c θ₀ r hy with h1 | ⟨x, hx0, hxJ, h1⟩
    · rw [h1]
      nlinarith
    · rw [h1]
      exact hL x hx0 hxJ
  · rcases stopWord_fn_of_pos hκ c θ₀ r hy with h1 | ⟨x, hx0, hxJ, h1⟩
    · rw [h1]
      nlinarith
    · rw [h1]
      exact hR x hx0 hxJ

/-! ### A launched piece is a good path -/

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A launched piece of a staged history has a simple transient trace** (R51-safe). For a staged history of a GFF
and a stage witness `(β, Y)` at instruction `k` (as in `StripDet.ae_stageDrv_eq`), if almost surely at a launch the
angle-`θ_k` flow-line word of `β` has admissible side partial sums, then almost surely at a launch the piece lies in
the Borel set `goodPathSet`: infinite lifetime and a simple transient generating trace. Under the regular conditional
law given the retained past the piece is the flow-line driver of a GFF with the data of `β ω₀`
(`StripDet.ae_stageDrv_eq`'s argument), so it is a good path there (`ae_goodPath_of_isFlowLineDriver`); the event is
measurable, so it passes to `P`. -/
theorem ae_goodPath_stage (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hpath : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
        (h ω) (Y ω))
    (hker : ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) Y (β ω₀).fn (β ω₀).jumps)
    (hadm : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      HasAdmissiblePartialSums κ (flowLineRhoL κ (β ω).fn (β ω).jumps 0 (instrAngle spec k))
        (flowLineRhoR κ (β ω).fn (β ω).jumps 0 (instrAngle spec k)) (flowLineXL (β ω).fn (β ω).jumps 0)
        (flowLineXR (β ω).fn (β ω).jumps 0)) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → E k ω ∈ goodPathSet := by
  have hB := runMeasStatement.{u}
  have hEm : ∀ j < k, Measurable (E j) := fun j _ => hE.1 j
  have hreg' : ∀ j < k, ∀ ω, IsRegularDriver (E j ω) := fun j _ => hreg j
  have hpm : Measurable (pastMap κ b jumps spec E k) := measurable_pastMap hB hb spec hEm hreg' k le_rfl
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hLm : MeasurableSet {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    measurableSet_launch_self hB hb hEm hreg'
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps spec E k]
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    measurableSet_pastSigma_of_run hB hb spec hEm hreg' hLm fun ω ω' he hω => by
      change (ExplState.run κ b jumps spec (fun j => E j ω') (k + 1)).2.2.2.1 k ≠ none
      rw [← launches_run_succ_of_run_eq spec he]
      exact hω
  have hA : MeasurableSet {ω | E k ω ∈ goodPathSet} := hE.1 k measurableSet_goodPathSet
  have hU : MeasurableSet ({ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none}ᶜ ∪
      {ω | E k ω ∈ goodPathSet}) := (h𝒢 _ hL𝒢).compl.union hA
  have key : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
      ω ∈ {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none}ᶜ ∪
        {ω | E k ω ∈ goodPathSet} := by
    filter_upwards [hE.2.2.2 k, hker, hadm, hpath, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hpath,
      ae_ae_run_eq hB hb spec hEm hreg' (P := P), Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hL𝒢.compl]
      with ω₀ hstg hk₀ hadm₀ hp₀ hpK hrunK hcomp
    by_cases hl : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none
    · obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
      obtain ⟨hspec, -, hc⟩ := eq_launch_of_launches spec _ hcθ
      have hθ : instrAngle spec k = θ := by unfold instrAngle; rw [hspec]
      obtain ⟨b', J', h', hb', hT', hfl⟩ := hstg c θ hcθ
      obtain ⟨hconf, hlift, -⟩ := hp₀ hl
      rw [← hc] at hconf hlift
      have hh'e : h' = fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) :=
        funext fun ω => (hT' ω).eq_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift)
      have hh'm : Measurable h' := by
        rw [hh'e]; exact (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
      have hYh' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), h' ω = Y ω := by
        filter_upwards [hpK, hrunK] with ω hpω hrω
        have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
          rw [launches_run_succ_of_run_eq spec hrω]; exact hl
        obtain ⟨-, -, hT⟩ := hpω hlω
        rw [hrω, ← hc] at hT
        exact IsChartTransport.unique hconf (hT' ω) hT
      have hG : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' (β ω₀).fn
          (β ω₀).jumps := isGFFWithBoundaryData_congr_ae (hk₀ hl) hh'm (hYh'.mono fun ω hω => hω.symm)
      have hfl' := isFlowLineDriver_word hκ hG hb' hfl
      have hadm' := hadm₀ hl
      rw [hθ] at hadm'
      refine (ae_goodPath_of_isFlowLineDriver hκ hκ4 hadm' hfl' (fun ω hω => ?_)
        (fun ω => (hreg k ω).2.1)).mono fun ω hω => Or.inr hω
      exact continuous_of_isRegularDriver (hreg k ω) hω
    · exact (hcomp hl).mono fun ω hω => Or.inl hω
  filter_upwards [Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hU key] with ω hω hl
  rcases hω with h1 | h1
  · exact absurd hl h1
  · exact h1

end Stage

/-! ### The continuation of a two-angle path -/

section TwoAngle

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The continuation of a two-angle path is a good path almost surely** (spec p. 410: the continuation is the
flow line of the conditional field in the record chart, with noncolliding side partial sums). If `b` has the (4.4)
heights at the first angle `θ₀`, the heights `b + θχ ≤ −λ + πχ` left and `b + θχ ≥ λ − πχ` right at the second angle
`θ`, and `|θ − θ₀| ≤ π` (both the increasing and the decreasing change), then almost surely the continuation `E 1` has
infinite lifetime and a simple transient generating trace (`goodPathSet`). -/
theorem ae_goodPath_one (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ)
    (hθ : θ ≤ θ₀ + Real.pi) (hθ' : θ₀ ≤ θ + Real.pi) :
    ∀ᵐ ω ∂P, E 1 ω ∈ goodPathSet := by
  have hB := runMeasStatement.{u}
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hζ₀ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ :=
    (ae_trace_stage_zero hκ hκ4 hb hh hE hL0 hR0).mono fun ω hω => hω.1
  obtain ⟨hβ₀, hY₀, hpath₀, hker₀⟩ := stageWitness_zero (E := E) (θ := θ) (t₀ := t₀) (θ₀ := θ₀) hh hc₀J hc₀
  have hpost := post_stage (spec := StripSys.twoAngleSpec θ₀ t₀ θ) (E := E) (ℓ := 0)
    (StripSideHeightProb.isStopLaw_stopWord hκ) hB hκ hb hh (fun j _ => hE.1 j) (fun j _ => hreg j) (hE.2.2.2 0)
    hβ₀ hY₀ hpath₀ hker₀
  have hpm : Measurable (pastMap κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1) :=
    measurable_pastMap hB hb _ (fun j _ => hE.1 j) (fun j _ => hreg j) 1 le_rfl
  have h𝒢 : pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1 ≤ mΩ := by
    rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hr : Measurable (rec₀ κ b jumps θ₀ θ t₀ E) := measurable_pi_iff.1 hpm (Fin.last 0)
  have hY₁ : Measurable (fun ω => field₁ κ (rec₀ κ b jumps θ₀ θ t₀ E ω) (h ω)) :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => field₁ κ p.1 p.2)
      (f := fun ω => (rec₀ κ b jumps θ₀ θ t₀ E ω, h ω)) (measurable_field₁ κ) (hr.prodMk hh.1)
  have hpath₁ : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) (1 + 1)).2.2.2.1 1
      ≠ none →
      (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1.2.1 w)) H ∧
      IsChartTransport (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1 1 0
        (chiC κ) (h ω) (field₁ κ (rec₀ κ b jumps θ₀ θ t₀ E ω) (h ω)) := by
    filter_upwards [hζ₀] with ω hω _
    have h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2 := by rw [hω]; exact ENNReal.coe_lt_top
    have hrec : rec₀ κ b jumps θ₀ θ t₀ E ω = recOf (t₀ : ℝ≥0∞) (E 0 ω) := pastMap_one_last ω
    rw [chart_one_eq (hreg 0 ω) h0, hrec]
    refine ⟨isConformal_recChart _, continuousOn_recChart_lift _, ?_⟩
    rw [field₁, Prop74B.flowField_zero_zero]
    exact isChartTransport_recField κ _ _
  have hker₁ : ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω₀) (1 + 1)).2.2.2.1 1
      ≠ none → IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1) ω₀)
        (fun ω => field₁ κ (rec₀ κ b jumps θ₀ θ t₀ E ω) (h ω)) (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω₀)).fn
        (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω₀)).jumps := by
    have hG := ae_isGFFWithBoundaryData_condExpKernel h𝒢 (M := univ)
      (β := fun ω => word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω))
      (Eventually.of_forall fun ω _ => isSorted_stopWord κ _) hY₁ (fun φ => by
        filter_upwards [hpost.2 φ] with ω hω _
        exact hω (launch_zero _) (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)))
    filter_upwards [hG] with ω₀ hω₀ _
    exact hω₀ (mem_univ _)
  have hL' : ∀ y : ℝ, y < 0 → y ∉ (shiftW 0 c₀).jumps →
      (shiftW 0 c₀).fn y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ := by
    intro y hy hyJ
    obtain ⟨hyj, he⟩ := shiftW_zero_fn_of_notMem hc₀J hc₀ hyJ
    rw [he]; exact hL y hy hyj
  have hR' : ∀ y : ℝ, 0 < y → y ∉ (shiftW 0 c₀).jumps →
      sleLambda κ - Real.pi * chiC κ ≤ (shiftW 0 c₀).fn y + θ * chiC κ := by
    intro y hy hyJ
    obtain ⟨hyj, he⟩ := shiftW_zero_fn_of_notMem hc₀J hc₀ hyJ
    rw [he]; exact hR y hy hyj
  have hadm : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) (1 + 1)).2.2.2.1 1
      ≠ none → HasAdmissiblePartialSums κ
        (flowLineRhoL κ (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).fn
          (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).jumps 0 (instrAngle (StripSys.twoAngleSpec θ₀ t₀ θ) 1))
        (flowLineRhoR κ (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).fn
          (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).jumps 0 (instrAngle (StripSys.twoAngleSpec θ₀ t₀ θ) 1))
        (flowLineXL (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).fn
          (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).jumps 0)
        (flowLineXR (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).fn
          (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).jumps 0) :=
    Eventually.of_forall fun _ _ => hasAdmissiblePartialSums_stopWord hκ hκ4 (shiftW 0 c₀) θ₀ θ _ hθ hθ' hL' hR'
  filter_upwards [ae_goodPath_stage hκ hκ4 hb hh hE hreg 1 hpath₁ hker₁ hadm, hζ₀] with ω hω hω₀
  have h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2 := by rw [hω₀]; exact ENNReal.coe_lt_top
  exact hω (launch_one_of_lt h0)

end TwoAngle

end StripWall

end Sec7

end InteractingSLE
