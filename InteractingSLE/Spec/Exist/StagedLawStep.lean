/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLawPast
import InteractingSLE.Spec.Jordan.Transport

/-!
# The staged conditional law: one stage

Packet PROVE-STAGEDLAW. The induction invariant `StageLaw k` (the field read in the chart of instruction `k` is, for
almost every sample, the chart transport of `h`, and conditionally on the retained past it is a GFF with the data of a
word read off the past) and its two ingredients:

* `stageLaw_zero`: at the first instruction the retained past is trivial (`pastSigma_zero`), so the regular conditional
  law is the law itself (`ae_isGFFWithBoundaryData_condExpKernel_bot`);
* **`post_stage`**: from `StageLaw ℓ` and the stage's conditional flow line (`StageOK`), the single-stage input
  (`IsStopLaw`) applied under the regular conditional law `κ_ℓ(ω₀)` gives the conditional characteristic functional of
  the field read in the chart right after piece `ℓ`, given the retained past before `ℓ + 1`
  (`ae_condExp_eq_of_condExpKernel`), and the continuity of the stopped driver.

The identification of the stage's flow-line data with the word of the induction is `isFlowLineDriver_word`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open LQGMetric Restart Staged

/-- The single-stage law for a given word map `βA` (the body of `StopLawStatement`). -/
def IsStopLaw (κ : ℝ) (βA : BoundaryWord × ℝ × RecData → BoundaryWord) : Prop :=
  Measurable βA ∧ (∀ x, (βA x).IsSorted) ∧
    ∀ (c : BoundaryWord) (θ : ℝ) (t : ℝ≥0∞) {Ω : Type u} [MeasurableSpace Ω]
      [StandardBorelSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (g : Ω → DistOn upperHalfPlaneOpens)
      (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), Measurable E → (∀ ω, IsRegularDriver (E ω)) →
      IsFlowLineDriver κ c.fn c.jumps θ Q g (fun s ω => (E ω).1 s) (fun ω => (E ω).2) →
      (∀ᵐ ω ∂Q, min t (E ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (E ω)))) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂Q, min t (E ω).2 ≠ ⊤ →
        Q[fun ω' => Complex.exp (Complex.I * (recField κ (recOf t (E ω')) (g ω') φ : ℂ)) |
            MeasurableSpace.comap (fun ω' => recOf t (E ω')) inferInstance] ω =
          gaussCF (βA (c, θ, recOf t (E ω))) φ

theorem stopLawStatement_iff : StopLawStatement.{u} ↔ ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ βA, IsStopLaw.{u} κ βA :=
  Iff.rfl

/-! ### Charts and fields -/

theorem measurable_recField_comp (κ : ℝ) {α : Type*} [MeasurableSpace α] {R : α → RecData}
    {Y : α → DistOn upperHalfPlaneOpens} (hR : Measurable R) (hY : Measurable Y) :
    Measurable fun a => recField κ (R a) (Y a) := by
  have h := (measurable_recField κ).comp (hR.prodMk hY)
  exact h

theorem Chart.recenter_eq_trans (c : Chart) (a : ℝ) : c.recenter a = InteractingSLE.Chart.trans c (shiftChart a) := by
  refine Prod.ext rfl (Prod.ext rfl (funext fun z => ?_))
  change c.2.2 z = 0 + c.2.2 z
  rw [zero_add]

theorem isChartTransport_shiftChart (a k : ℝ) (f : DistOn upperHalfPlaneOpens) :
    IsChartTransport (shiftChart a) 1 0 k f (flowField a 0 f) := by
  have h := Chart.isChartTransport_chartTransport (isConformal_shiftChart a)
    (Chart.locallyIntegrableOn_of_continuousOn (Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift)) 1 0 0 f
  intro φ φ' hs hφ
  rw [show flowField a 0 f = Chart.chartTransport (isConformal_shiftChart a) 1 0 0 f from rfl, h φ φ' hs hφ]
  change _ + 0 * ∫ w, (0 : ℝ) * φ' w = _ + k * ∫ w, (0 : ℝ) * φ' w
  simp

theorem continuousOn_shiftChart_lift (a : ℝ) :
    ContinuousOn (fun w => (shiftChart a).2.2 ((shiftChart a).2.1 w)) QuantumZipper.H :=
  Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift

theorem measurable_flowField_uncurry :
    Measurable fun p : ℝ × DistOn upperHalfPlaneOpens => flowField p.1 0 p.2 := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  have e : (fun p : ℝ × DistOn upperHalfPlaneOpens => flowField p.1 0 p.2 φ) =
      fun p => p.2 (Chart.pushTest (isConformal_shiftChart p.1) φ) := by
    funext p
    rw [flowField_apply, zero_mul, add_zero]
  rw [e]
  refine RandomTest.measurable_apply_of_forall_measurable measurable_snd fun z => ?_
  simp only [pushTest_shiftChart_apply]
  exact (φ.continuous.comp (continuous_const.sub (Complex.continuous_ofReal.comp continuous_id))).measurable.comp
    measurable_fst

/-- **A.e. equal fields have the same GFF law.** -/
theorem isGFFWithBoundaryData_congr_ae {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y Y' : Ω → DistOn upperHalfPlaneOpens} {g : ℝ → ℝ} {S : Set ℝ} (hY : IsGFFWithBoundaryData Q Y g S)
    (hY' : Measurable Y') (he : Y =ᵐ[Q] Y') : IsGFFWithBoundaryData Q Y' g S := by
  refine ⟨hY', fun u hu => ?_⟩
  have hX := hY.2 u hu
  have hXm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable fun f : DistOn upperHalfPlaneOpens =>
      f φ - ∫ z, u z * φ z := fun φ => (measurable_distOn_apply φ).sub_const _
  have h1 := isZBGFFProcess_map hY.1 hXm hX
  rw [Measure.map_congr he] at h1
  exact isZBGFFProcess_comp hY' h1

/-! ### Finite piecewise definitions -/

/-- The map equal to `F ℓ` on `A ℓ` (the first `ℓ < n` from the top), and to `d` elsewhere. -/
def finPw {α β : Type*} (A : ℕ → Set α) (F : ℕ → α → β) (d : α → β) : ℕ → α → β
  | 0 => d
  | n + 1 => fun ω => by classical exact if ω ∈ A n then F n ω else finPw A F d n ω

theorem measurable_finPw {α β : Type*} {mα : MeasurableSpace α} [MeasurableSpace β] {A : ℕ → Set α}
    {F : ℕ → α → β} {d : α → β} (hd : Measurable d) : ∀ n, (∀ m < n, MeasurableSet (A m)) →
      (∀ m < n, Measurable (F m)) → Measurable (finPw A F d n)
  | 0, _, _ => hd
  | n + 1, hA, hF => by
    classical
    exact Measurable.ite (hA n (Nat.lt_succ_self n)) (hF n (Nat.lt_succ_self n))
      (measurable_finPw hd n (fun m hm => hA m (Nat.lt_succ_of_lt hm)) fun m hm => hF m (Nat.lt_succ_of_lt hm))

theorem finPw_eq {α β : Type*} {A : ℕ → Set α} {F : ℕ → α → β} {d : α → β} {ω : α} {ℓ : ℕ}
    (hω : ω ∈ A ℓ) (hdis : ∀ j, j ≠ ℓ → ω ∉ A j) : ∀ n, ℓ < n → finPw A F d n ω = F ℓ ω
  | 0, h => absurd h (Nat.not_lt_zero ℓ)
  | n + 1, h => by
    classical
    simp only [finPw]
    by_cases hn : n = ℓ
    · subst hn
      simp only [hω, ↓reduceIte]
    · simp only [hdis n hn, ↓reduceIte]
      exact finPw_eq hω hdis n (by omega)

/-! ### Runs -/

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem launches_run_succ_of_run_eq (spec : ExplSpec) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (h : ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 = (ExplState.run κ b jumps spec D' (k + 1)).2.2.2.1 := by
  rw [run_succ, run_succ, h]
  cases spec.2.2[k]? with
  | none => rfl
  | some a => exact launches_step_indep _ _ _ _ _

theorem run_succ_eq_of_noLaunch (spec : ExplSpec) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (h : ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k)
    (hn : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none) :
    ExplState.run κ b jumps spec D (k + 1) = ExplState.run κ b jumps spec D' (k + 1) := by
  rw [run_succ] at hn ⊢
  rw [run_succ, ← h]
  cases hk : spec.2.2[k]? with
  | none => rfl
  | some a =>
    rw [hk] at hn
    simp only at hn ⊢
    rcases a with ⟨θ, t⟩ | pref | ⟨v, pref⟩
    · change ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t =
        ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D' k) θ t
      change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t).2.2.2.1 k = none at hn
      rcases flowStep_cases (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k θ t with hc | hc
      · exact hc _ _
      · rw [hc, launches_launch, Function.update_self] at hn
        exact absurd hn (by simp)
    · rfl
    · rfl

end Run

/-! ### The induction invariant -/

section Invariant

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The invariant at instruction `k`**: a word `β` read off the retained past and a measurable field `Y` such that
almost surely, at a launch, the chart of instruction `k` is conformal and `Y` is `h` read in it, and conditionally on
the retained past `Y` is a GFF with the data of `β`. -/
def StageLaw (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : Prop :=
  ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
    Measurable[pastSigma κ b jumps spec E k] β ∧ Measurable Y ∧
    (∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
        (h ω) (Y ω)) ∧
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) Y (β ω₀).fn (β ω₀).jumps

omit mΩ [StandardBorelSpace Ω] in
theorem pastSigma_zero (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    pastSigma κ b jumps spec E 0 = ⊥ := by
  refine le_antisymm (fun A hA => ?_) bot_le
  obtain ⟨s, -, rfl⟩ := hA
  rw [MeasurableSpace.measurableSet_bot_iff]
  by_cases hs : s.Nonempty
  · right
    obtain ⟨x, hx⟩ := hs
    ext ω
    simp only [mem_preimage, mem_univ, iff_true]
    convert hx
  · left
    rw [not_nonempty_iff_eq_empty.1 hs, preimage_empty]

/-- **Under a trivial past, the regular conditional law is the law.** -/
theorem ae_isGFFWithBoundaryData_condExpKernel_bot {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistOn upperHalfPlaneOpens} {g : ℝ → ℝ} {S : Set ℝ} (hY : IsGFFWithBoundaryData P Y g S) :
    ∀ᵐ ω₀ ∂P, IsGFFWithBoundaryData (condExpKernel P ⊥ ω₀) Y g S := by
  have hk : ∀ k : RatComb, ∀ᵐ ω₀ ∂P,
      ∫ ω, Complex.exp (Complex.I * (Y ω (ratComb upperHalfPlaneOpens k) : ℂ)) ∂(condExpKernel P ⊥ ω₀) =
        ∫ ω, Complex.exp (Complex.I * (Y ω (ratComb upperHalfPlaneOpens k) : ℂ)) ∂P := by
    intro k
    filter_upwards [condExp_ae_eq_integral_condExpKernel bot_le
      (GFF.integrable_exp_I_mul (P := P) ((measurable_distOn_apply (ratComb upperHalfPlaneOpens k)).comp hY.1))]
      with ω₀ h2
    have h3 := h2.symm
    rw [condExp_bot', probReal_univ, inv_one, one_smul] at h3
    exact h3
  filter_upwards [ae_all_iff.2 hk] with ω₀ hk'
  have hmap : (condExpKernel P ⊥ ω₀).map Y = P.map Y := by
    refine ext_of_integral_cexp_ratComb fun k => ?_
    rw [integral_map hY.1.aemeasurable (GFF.measurable_exp_I_mul (measurable_distOn_apply _)).aestronglyMeasurable,
      integral_map hY.1.aemeasurable (GFF.measurable_exp_I_mul (measurable_distOn_apply _)).aestronglyMeasurable]
    exact hk' k
  refine ⟨hY.1, fun u hu => ?_⟩
  have hXm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable fun f : DistOn upperHalfPlaneOpens =>
      f φ - ∫ z, u z * φ z := fun φ => (measurable_distOn_apply φ).sub_const _
  have h1 := isZBGFFProcess_map hY.1 hXm (hY.2 u hu)
  rw [← hmap] at h1
  exact isZBGFFProcess_comp hY.1 h1

/-- **The invariant at the first instruction**: the chart is the translation to the root, the retained past is
trivial. -/
theorem stageLaw_zero {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : StageLaw κ b jumps P h spec E 0 := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr P h (S := (jumps : Set ℝ)) fun y hy => hc₀ y hy).2 hh
  have hgff := isGFFWithBoundaryData_shiftW spec.1 hh₀
  refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀, fun ω => flowField spec.1 0 (h ω), measurable_const,
    (measurable_flowField _ _).comp hh.1, Eventually.of_forall fun ω _ => ?_, ?_⟩
  · exact ⟨Chart.isConformal_id.recenter _, Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift,
      isChartTransport_shiftChart _ _ _⟩
  · rw [pastSigma_zero]
    filter_upwards [ae_isGFFWithBoundaryData_condExpKernel_bot hgff] with ω₀ h0 _
    exact h0

end Invariant

/-! ### The flow line of a stage, read with the word of the induction -/

/-- **The flow line of a stage, read with the word of the induction.** If `g` is a GFF with the data of the word `c`
and `W` drives its angle-`θ` flow line for some piecewise-constant data `b'`, then `W` drives its flow line for the data
of `c` (both data are data of the same flow field, so they agree off a finite set). -/
theorem isFlowLineDriver_word {κ : ℝ} (hκ : 0 < κ) {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {g : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord}
    (hg : IsGFFWithBoundaryData Q g c.fn c.jumps) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') {θ : ℝ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b' J' θ Q g W ζ) : IsFlowLineDriver κ c.fn c.jumps θ Q g W ζ := by
  obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := hfl
  have hh'' : h'' = fun ω => flowField 0 (θ * QuantumZipper.chiC κ) (g ω) := by
    funext ω
    ext φ
    have e1 := htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])
    have e2 := isTranslateAddConst_flowField 0 (θ * QuantumZipper.chiC κ) (g ω) φ φ
      (fun z => by rw [Complex.ofReal_zero, add_zero])
    rw [e1, e2]
  have hG1 : IsGFFWithBoundaryData Q h''
      (forceBoundaryData κ (flowLineRhoL κ b' J' 0 θ) (flowLineRhoR κ b' J' 0 θ) (flowLineXL b' J' 0)
        (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) := ⟨hC.2.1, hC.2.2.1⟩
  have hG2 := isGFFWithBoundaryData_flowField hκ c.isPiecewiseConstantBoundaryData 0 θ hg
  rw [← hh''] at hG2
  obtain ⟨u₁, hu₁, -⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ)
    (ρL := flowLineRhoL κ b' J' 0 θ) (ρR := flowLineRhoR κ b' J' 0 θ) (vL := flowLineXL b' J' 0)
    (vR := flowLineXR b' J' 0)
  obtain ⟨u₂, hu₂, -⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ)
    (ρL := flowLineRhoL κ c.fn c.jumps 0 θ) (ρR := flowLineRhoR κ c.fn c.jumps 0 θ) (vL := flowLineXL c.fn c.jumps 0)
    (vR := flowLineXR c.fn c.jumps 0)
  have heq := eq_of_isGFFWithBoundaryData' hu₁ hu₂ hG1 hG2
  refine (isFlowLineDriver_congr_of_eqOn c.isPiecewiseConstantBoundaryData hb'
    (flowExcept b' J' 0 ∪ flowExcept c.fn c.jumps 0) fun y hy => ?_).1 ⟨h'', 𝓕, VL, VR, B, htr, hC⟩
  have hy1 : y ∉ flowExcept b' J' 0 := fun h => hy (Finset.mem_union_left _ h)
  have hy2 : y ∉ flowExcept c.fn c.jumps 0 := fun h => hy (Finset.mem_union_right _ h)
  have e := heq y (notMem_forceJumpSet_of_notMem_flowExcept hy1) (notMem_forceJumpSet_of_notMem_flowExcept hy2)
  rw [forceBoundaryData_flowLine_seed hκ hb' 0 θ (ne_zero_of_notMem_flowExcept hy1)
      (add_notMem_of_notMem_flowExcept hy1),
    forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 θ (ne_zero_of_notMem_flowExcept hy2)
      (add_notMem_of_notMem_flowExcept hy2)] at e
  simp only [add_zero] at e
  linarith

/-! ### One stage -/

section Post

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **One stage.** From the invariant at instruction `ℓ` and the stage's conditional flow line (`StageOK`), the
single-stage law (`IsStopLaw`), applied under the regular conditional law given the retained past before `ℓ`, gives:
the stopped driver of a launched piece with a finite stop is continuous, and conditionally on the retained past before
`ℓ + 1` the field read in the chart right after the piece has the Gaussian characteristic functional of the word
`βA (β, θ_ℓ, record_ℓ)`. -/
theorem post_stage {βA : BoundaryWord × ℝ × RecData → BoundaryWord} (hβA : IsStopLaw.{u} κ βA)
    (hB : RunMeasStatement.{u}) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {ℓ : ℕ}
    (hEm : ∀ j < ℓ + 1, Measurable (E j)) (hreg : ∀ j < ℓ + 1, ∀ ω, IsRegularDriver (E j ω))
    (hok : StageOK κ b jumps P h spec E ℓ) {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hβ : Measurable[pastSigma κ b jumps spec E ℓ] β) (hY : Measurable Y)
    (hpath : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
        (h ω) (Y ω))
    (hker : ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀) Y (β ω₀).fn (β ω₀).jumps) :
    (∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf (instrTime spec ℓ) (E ℓ ω)))) ∧
    ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ →
      P[fun ω' => Complex.exp (Complex.I *
          (recField κ (pastMap κ b jumps spec E (ℓ + 1) ω' (Fin.last ℓ)) (Y ω') φ : ℂ)) |
          pastSigma κ b jumps spec E (ℓ + 1)] ω =
        gaussCF (βA (β ω, instrAngle spec ℓ, pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ))) φ := by
  have hEℓ : Measurable (E ℓ) := hEm ℓ (Nat.lt_succ_self ℓ)
  have hregℓ : ∀ ω, IsRegularDriver (E ℓ ω) := hreg ℓ (Nat.lt_succ_self ℓ)
  have hEm' : ∀ j < ℓ, Measurable (E j) := fun j hj => hEm j (Nat.lt_succ_of_lt hj)
  have hreg' : ∀ j < ℓ, ∀ ω, IsRegularDriver (E j ω) := fun j hj => hreg j (Nat.lt_succ_of_lt hj)
  have hpm : Measurable (pastMap κ b jumps spec E ℓ) := measurable_pastMap hB hb spec hEm hreg ℓ (Nat.le_succ ℓ)
  have hpm1 : Measurable (pastMap κ b jumps spec E (ℓ + 1)) := measurable_pastMap hB hb spec hEm hreg (ℓ + 1) le_rfl
  have h𝒢 : pastSigma κ b jumps spec E ℓ ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hLm : MeasurableSet {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} :=
    measurableSet_launch hB hb spec hEm hreg (Nat.lt_succ_self ℓ)
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps spec E ℓ]
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} :=
    measurableSet_pastSigma_of_run hB hb spec hEm' hreg' hLm fun ω ω' he hω => by
      change (ExplState.run κ b jumps spec (fun j => E j ω') (ℓ + 1)).2.2.2.1 ℓ ≠ none
      rw [← launches_run_succ_of_run_eq spec he]
      exact hω
  have hRm : Measurable fun ω => recOf (instrTime spec ℓ) (E ℓ ω) := measurable_recOf hEℓ hregℓ _
  obtain ⟨Wβ, hWβ, hβW⟩ : ∃ Wβ : PastData ℓ → BoundaryWord, Measurable Wβ ∧
      β = Wβ ∘ pastMap κ b jumps spec E ℓ := by
    rw [pastSigma_eq_comap] at hβ
    exact hβ.exists_eq_measurable_comp
  have hlast : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ) = recOf (instrTime spec ℓ) (E ℓ ω) := by
    intro ω hω
    rw [pastMap_succ, Fin.snoc_last, readRec_retained_succ]
    simp only [hω, ↓reduceIte]
  -- the kernel statements
  have hkey : ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀), min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ →
        LocalExt.IsDrvGood (recHist (recOf (instrTime spec ℓ) (E ℓ ω)))) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀),
        recOf (instrTime spec ℓ) (E ℓ ω) ∈ {r : RecData | r.2.1 ≠ ⊤} →
        (condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀)[fun ω' => Complex.exp (Complex.I *
          (recField κ (pastMap κ b jumps spec E (ℓ + 1) ω' (Fin.last ℓ)) (Y ω') φ : ℂ)) |
            MeasurableSpace.comap (fun ω' => recOf (instrTime spec ℓ) (E ℓ ω')) inferInstance] ω =
          gaussCF (βA (Wβ (pastMap κ b jumps spec E ℓ ω₀), instrAngle spec ℓ,
            recOf (instrTime spec ℓ) (E ℓ ω))) φ := by
    filter_upwards [hok, hpath, hker, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hpath,
      ae_ae_run_eq hB hb spec hEm' hreg' (P := P)] with ω₀ hok₀ hpath₀ hker₀ hpathK hrunK hω₀
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω₀
    obtain ⟨-, -, hc⟩ := eq_launch_of_launches spec _ hcθ
    obtain ⟨hconf, hlift, -⟩ := hpath₀ hω₀
    rw [← hc] at hconf hlift
    have hgT : ∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω)
        (Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω)) := fun ω =>
      Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
    have hgm : Measurable fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) :=
      (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
    have hlaunchK : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀),
        (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      filter_upwards [hrunK] with ω hrω
      rw [launches_run_succ_of_run_eq spec hrω]
      exact hω₀
    have hYg : Y =ᵐ[condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀]
        fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) := by
      filter_upwards [hpathK, hrunK, hlaunchK] with ω hpω hrω hlω
      obtain ⟨-, -, hT⟩ := hpω hlω
      rw [hrω, ← hc] at hT
      exact hT.unique hconf (hgT ω)
    have hgG := isGFFWithBoundaryData_congr_ae (hker₀ hω₀) hgm hYg
    obtain ⟨b', J', h', hb', hT', hfl⟩ := hok₀ c θ' hcθ
    have hh' : h' = fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) :=
      funext fun ω => (hT' ω).unique hconf (hgT ω)
    rw [hh'] at hfl
    have hfl' := isFlowLineDriver_word hκ hgG hb' hfl
    rw [angle_of_launch spec _ hcθ] at hfl'
    obtain ⟨hgood, hcf⟩ := hβA.2.2 (β ω₀) (instrAngle spec ℓ) (instrTime spec ℓ)
      (condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀) _ (E ℓ) hEℓ hregℓ hfl'
    refine ⟨hgood, fun φ => ?_⟩
    have hcong : (fun ω' => Complex.exp (Complex.I *
        (recField κ (pastMap κ b jumps spec E (ℓ + 1) ω' (Fin.last ℓ)) (Y ω') φ : ℂ)))
        =ᵐ[condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀] fun ω' => Complex.exp (Complex.I *
          (recField κ (recOf (instrTime spec ℓ) (E ℓ ω'))
            (Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω')) φ : ℂ)) := by
      filter_upwards [hlaunchK, hYg] with ω h1 h2
      rw [hlast ω h1, h2]
    filter_upwards [condExp_congr_ae (m := MeasurableSpace.comap (fun ω' => recOf (instrTime spec ℓ) (E ℓ ω'))
      inferInstance) hcong, hcf φ] with ω h1 h2 hRN
    rw [h1, h2 hRN, hβW]
    rfl
  refine ⟨?_, fun φ => ?_⟩
  · -- the continuity of the stopped driver
    have hGm : MeasurableSet {ω | min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ →
        LocalExt.IsDrvGood (recHist (recOf (instrTime spec ℓ) (E ℓ ω)))} := by
      have h1 : MeasurableSet {ω | min (instrTime spec ℓ) (E ℓ ω).2 = ⊤} :=
        measurableSet_eq_fun (measurable_const.min (measurable_snd.comp hEℓ)) measurable_const
      have h2 : MeasurableSet ((fun ω => recHist (recOf (instrTime spec ℓ) (E ℓ ω))) ⁻¹'
          {y | LocalExt.IsDrvGood y}) := (measurable_recHist.comp hRm) LocalExt.measurableSet_isDrvGood
      convert h1.union h2 using 1
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_preimage]
      tauto
    have := Sec5.Lemma56Stages.ae_imp_of_ae_condExpKernel h𝒢 hL𝒢 hGm
      (hkey.mono fun ω₀ hω₀ hL => (hω₀ hL).1)
    filter_upwards [this] with ω hω hL hst
    exact hω hL hst
  · -- one more stage: from the kernel to the retained past before `ℓ + 1`
    have hΦ : Measurable fun x : PastData ℓ × RecData => Fin.snoc (α := fun _ => RecData) x.1 x.2 := by
      refine measurable_pi_iff.2 fun i => ?_
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact measurable_snd
      | cast j => simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp measurable_fst
    have hΨ : Measurable fun u : PastData (ℓ + 1) => (Fin.init u, u (Fin.last ℓ)) :=
      (measurable_pi_iff.2 fun i => measurable_pi_apply _).prodMk (measurable_pi_apply _)
    have hpπ : ∀ ω, (Fin.init (pastMap κ b jumps spec E (ℓ + 1) ω), pastMap κ b jumps spec E (ℓ + 1) ω
        (Fin.last ℓ)).1 = pastMap κ b jumps spec E ℓ ω := fun ω => by
      simp only
      rw [pastMap_succ, Fin.init_snoc]
    have hπL : ∀ ω ∈ {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none},
        pastMap κ b jumps spec E (ℓ + 1) ω = Fin.snoc (α := fun _ => RecData)
          (pastMap κ b jumps spec E ℓ ω, recOf (instrTime spec ℓ) (E ℓ ω)).1
          (pastMap κ b jumps spec E ℓ ω, recOf (instrTime spec ℓ) (E ℓ ω)).2 ∧
        (Fin.init (pastMap κ b jumps spec E (ℓ + 1) ω), pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ)).2 =
          recOf (instrTime spec ℓ) (E ℓ ω) := by
      intro ω hω
      refine ⟨?_, hlast ω hω⟩
      rw [pastMap_succ, readRec_retained_succ]
      simp only [show (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none from hω,
        ↓reduceIte]
    have hN : MeasurableSet {r : RecData | r.2.1 ≠ ⊤} :=
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).compl
    have hlastm : Measurable fun ω' => pastMap κ b jumps spec E (ℓ + 1) ω' (Fin.last ℓ) :=
      (measurable_pi_apply (Fin.last ℓ)).comp hpm1
    have hZm : Measurable fun ω' => recField κ (pastMap κ b jumps spec E (ℓ + 1) ω' (Fin.last ℓ)) (Y ω') :=
      measurable_recField_comp κ hlastm hY
    have hXm : Measurable fun ω' => Complex.exp (Complex.I *
        (recField κ (pastMap κ b jumps spec E (ℓ + 1) ω' (Fin.last ℓ)) (Y ω') φ : ℂ)) :=
      GFF.measurable_exp_I_mul ((measurable_distOn_apply φ).comp hZm)
    have hGm : Measurable fun x : PastData ℓ × RecData => gaussCF (βA (Wβ x.1, instrAngle spec ℓ, x.2)) φ :=
      (measurable_gaussCF φ).comp (hβA.1.comp ((hWβ.comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd)))
    have hK := ae_condExp_eq_of_condExpKernel (P := P) hpm hRm hpm1 hΦ hΨ hpπ
      (by rw [← pastSigma_eq_comap]; exact hL𝒢) hπL hN hXm
      (fun ω => (Complex.norm_exp_I_mul_ofReal _).le) hGm (fun x => norm_gaussCF_le _ φ)
      (hkey.mono fun ω₀ hω₀ hL => (hω₀ hL).2 φ)
    filter_upwards [hK] with ω hω hL hst
    have e := hω hL hst
    rw [hlast ω hL]
    rw [hβW]
    exact e

end Post

end StagedLaw

end Exist

end InteractingSLE
