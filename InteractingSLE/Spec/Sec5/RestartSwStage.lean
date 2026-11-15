/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartSwFirstHit
import InteractingSLE.Spec.Sec7.StripWallMean

/-!
# The switched-wall restart law: the conditional world after the first piece

Packet PROVE-SWITCHED. Specification p. 138 (Lemma 5.7's proof, Figure 5.5 right panel) and p. 410 (Aux. lemma 130:
"conditionally on the first prefix, the continuation is a flow line of the conditional field in the record chart"). For
a two-angle staged history `E` of `η^{t₀,∞}_{θ₀,θ}` (`Sec7.StripSys.twoAngleSpec θ₀ t₀ θ`) of a GFF `h` with the (4.4)
heights at `θ₀`, regular at every sample:

* **`ae_stage_one`**: for `P`-almost every `ω₀`, the first piece lives forever, and under the regular conditional law `Q
  = condExpKernel P (pastSigma … 1) ω₀` given the first record, the field read in the record chart of `ω₀`, `h₁ =
  recField κ (recOf t₀ (E 0 ω₀)) ∘ h`, is a GFF with the data of the stop word `word₁ κ θ₀ c₀ (recOf t₀ (E 0 ω₀))`
  (Figure 5.5's right panel), and the continuation `(E 1).1` is its angle-`θ` flow-line driver. This is the content of
  `Sec7.StripDet.ae_drv_one`'s proof (PROVE-STRIPSYS21) without the determination step, with the chart fixed to that of
  `ω₀`.
* **`isHeightBounded44_word₁`**, **`isHeightBounded44_reflWord_word₁`**: the (4.4) heights of the stop word at the
  second angle `θ` and at `π/2` for an increasing change `θ₀ ≤ θ`, and of its mirror image at `−θ` and `π/2` for a
  decreasing change `θ ≤ θ₀`, under Aux. lemma 130's height choice (from PROVE-STRIPSYS21/27's
  `cond44_flowLine_stopWord`, `cond44_reflWord_stopWord` and `isHeightBounded44_of_cond44`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.RestartSw

open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.FlowReflect (reflData reflJumps)
open Restart Exist Exist.Staged Exist.StagedLaw Exist.StagedLaw.BoundaryWord Sec7.StripDet

/-! ### Heights of the stop word -/

section Heights

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {c₀ : BoundaryWord}

/-- **The (4.4) heights of the stop word for an increasing change** `θ₀ ≤ θ`, at `θ` and at `π/2`, under Aux. lemma
130's height choice for `b`. -/
theorem isHeightBounded44_word₁ (hκ : 0 < κ) (hκ4 : κ < 4) (hc₀J : c₀.jumps = J) (hc₀ : ∀ y ∉ J, c₀.fn y = b y)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₀ θ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hle : θ₀ ≤ θ)
    (r : RecData) :
    IsHeightBounded44 κ (word₁ κ θ₀ c₀ r).fn (word₁ κ θ₀ c₀ r).jumps θ ∧
      IsHeightBounded44 κ (word₁ κ θ₀ c₀ r).fn (word₁ κ θ₀ c₀ r).jumps (π / 2) := by
  have hχ : 0 < chiC κ := Sec4.chiC_pos hκ hκ4
  have hb : IsPiecewiseConstantBoundaryData (word₁ κ θ₀ c₀ r).fn (word₁ κ θ₀ c₀ r).jumps :=
    (word₁ κ θ₀ c₀ r).isPiecewiseConstantBoundaryData
  have hpi : (π / 2) ∈ Icc (-(π / 2)) (π / 2) := Sec7.StripSys.pi_div_two_mem_Icc
  have hcases : ∀ a ∈ Icc (-(π / 2)) (π / 2), θ₀ ≤ a →
      Sec4.Cond44 κ (flowLineRhoL κ (word₁ κ θ₀ c₀ r).fn (word₁ κ θ₀ c₀ r).jumps 0 a)
        (flowLineRhoR κ (word₁ κ θ₀ c₀ r).fn (word₁ κ θ₀ c₀ r).jumps 0 a) := by
    intro a ha hθa
    obtain ⟨hL', hR'⟩ := shiftW_zero_heights (κ := κ) (α := a) hc₀J hc₀
      (fun y hy hyJ => by have := hleft a ha y hy hyJ; nlinarith [Real.pi_pos])
      (fun y hy hyJ => hright a ha y hy hyJ)
    exact cond44_flowLine_stopWord hκ hκ4 (shiftW 0 c₀) θ₀ a r hθa
      (by linarith [hθ₀.1, ha.2]) hL' hR'
  exact ⟨isHeightBounded44_of_cond44 hκ hκ4 hb (hcases θ hθ hle),
    isHeightBounded44_of_cond44 hκ hκ4 hb (hcases _ hpi hθ₀.2)⟩

/-- The (4.4) heights of the mirror image of a word, read on `reflData`/`reflJumps`. -/
theorem isHeightBounded44_refl_of_reflWord {c : BoundaryWord} {a : ℝ}
    (h : IsHeightBounded44 κ (Sec7.StripWall.reflWord c).fn (Sec7.StripWall.reflWord c).jumps a) :
    IsHeightBounded44 κ (reflData c.fn) (reflJumps c.jumps) a := by
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · have hyJ' : -y ∉ c.jumps := fun h' => hyJ (Sec7.FlowReflect.mem_reflJumps.2 h')
    have h1 := h.1 y hy (by rw [Sec7.StripWall.jumps_reflWord]; exact hyJ)
    rwa [Sec7.StripWall.fn_reflWord hyJ'] at h1
  · have hyJ' : -y ∉ c.jumps := fun h' => hyJ (Sec7.FlowReflect.mem_reflJumps.2 h')
    have h1 := h.2 y hy (by rw [Sec7.StripWall.jumps_reflWord]; exact hyJ)
    rwa [Sec7.StripWall.fn_reflWord hyJ'] at h1

/-- **The (4.4) heights of the mirrored stop word for a decreasing change** `θ ≤ θ₀`, at `−θ` and at `π/2`, under
Aux. lemma 130's height choice for `b` ("the reflected condition", p. 410). -/
theorem isHeightBounded44_reflWord_word₁ (hκ : 0 < κ) (hκ4 : κ < 4) (hc₀J : c₀.jumps = J)
    (hc₀ : ∀ y ∉ J, c₀.fn y = b y)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₀ θ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hle : θ ≤ θ₀)
    (r : RecData) :
    IsHeightBounded44 κ (reflData (word₁ κ θ₀ c₀ r).fn) (reflJumps (word₁ κ θ₀ c₀ r).jumps) (-θ) ∧
      IsHeightBounded44 κ (reflData (word₁ κ θ₀ c₀ r).fn) (reflJumps (word₁ κ θ₀ c₀ r).jumps) (π / 2) := by
  have hχ : 0 < chiC κ := Sec4.chiC_pos hκ hκ4
  have hb : IsPiecewiseConstantBoundaryData (Sec7.StripWall.reflWord (word₁ κ θ₀ c₀ r)).fn
      (Sec7.StripWall.reflWord (word₁ κ θ₀ c₀ r)).jumps :=
    (Sec7.StripWall.reflWord (word₁ κ θ₀ c₀ r)).isPiecewiseConstantBoundaryData
  have hnpi : -(π / 2) ∈ Icc (-(π / 2)) (π / 2) := Sec7.StripSys.neg_pi_div_two_mem_Icc
  have hcases : ∀ a ∈ Icc (-(π / 2)) (π / 2), a ≤ θ₀ →
      Sec4.Cond44 κ (flowLineRhoL κ (Sec7.StripWall.reflWord (word₁ κ θ₀ c₀ r)).fn
          (Sec7.StripWall.reflWord (word₁ κ θ₀ c₀ r)).jumps 0 (-a))
        (flowLineRhoR κ (Sec7.StripWall.reflWord (word₁ κ θ₀ c₀ r)).fn
          (Sec7.StripWall.reflWord (word₁ κ θ₀ c₀ r)).jumps 0 (-a)) := by
    intro a ha haθ
    have hL' : ∀ y : ℝ, y < 0 → y ∉ (shiftW 0 c₀).jumps → (shiftW 0 c₀).fn y + a * chiC κ ≤ -sleLambda κ := by
      intro y hy hyJ
      obtain ⟨hyj, he⟩ := shiftW_zero_fn_of_notMem hc₀J hc₀ hyJ
      rw [he]; exact hleft a ha y hy hyj
    have hR' : ∀ y : ℝ, 0 < y → y ∉ (shiftW 0 c₀).jumps →
        sleLambda κ - π * chiC κ ≤ (shiftW 0 c₀).fn y + a * chiC κ := by
      intro y hy hyJ
      obtain ⟨hyj, he⟩ := shiftW_zero_fn_of_notMem hc₀J hc₀ hyJ
      rw [he]; have := hright a ha y hy hyj; nlinarith [Real.pi_pos]
    exact Sec7.StripWall.cond44_reflWord_stopWord hκ hκ4 (shiftW 0 c₀) θ₀ a r haθ
      (by linarith [hθ₀.2, ha.1]) hL' hR'
  have h1 := isHeightBounded44_of_cond44 hκ hκ4 hb (hcases θ hθ hle)
  have h2 := isHeightBounded44_of_cond44 hκ hκ4 hb (hcases _ hnpi hθ₀.1)
  rw [neg_neg] at h2
  exact ⟨isHeightBounded44_refl_of_reflWord h1, isHeightBounded44_refl_of_reflWord h2⟩

end Heights

/-! ### The conditional world after the first piece -/

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The retained past before the continuation is the σ-algebra of the first record. -/
theorem pastSigma_one_eq :
    pastSigma κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) E 1 =
      MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (E 0 ω)) inferInstance := by
  have hfun : pastMap κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) E 1 =
      (MeasurableEquiv.funUnique (Fin 1) RecData).symm ∘ fun ω => recOf (t₀ : ℝ≥0∞) (E 0 ω) := by
    funext ω i
    have hi : i = Fin.last 0 := Subsingleton.elim _ _
    subst hi
    exact pastMap_one_last ω
  rw [pastSigma_eq_comap, hfun, ← MeasurableSpace.comap_comp]
  congr 1
  exact (MeasurableEquiv.funUnique (Fin 1) RecData).symm.measurableEmbedding.comap_eq

/-- **The conditional world after the first piece** (spec p. 138, Figure 5.5 right panel; p. 410). For a two-angle
staged history regular at every sample, of a GFF with the (4.4) heights at `θ₀`, almost surely: the first piece lives
forever, and under the regular conditional law given the retained past before the continuation, the field read in the
record chart of the conditioning sample is a GFF with the stop word's data, and the continuation is its angle-`θ`
flow-line driver. -/
theorem ae_stage_one (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J) (hE : IsStagedHistory κ b J P h (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {c₀ : BoundaryWord} (hc₀J : c₀.jumps = J)
    (hc₀ : ∀ y ∉ J, c₀.fn y = b y)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ₀ * chiC κ) :
    ∀ᵐ ω₀ ∂P, (E 0 ω₀).2 = ⊤ ∧
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) E 1) ω₀)
        (fun ω => recField κ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀)) (h ω))
        (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀))).fn (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀))).jumps ∧
      IsFlowLineDriver κ (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀))).fn
        (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀))).jumps θ
        (condExpKernel P (pastSigma κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) E 1) ω₀)
        (fun ω => recField κ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀)) (h ω)) (fun t ω => (E 1 ω).1 t) (fun ω => (E 1 ω).2) := by
  have hB := runMeasStatement.{u}
  set spec := Sec7.StripSys.twoAngleSpec θ₀ t₀ θ with hspec
  have hζ₀ := Sec7.StripWall.ae_trace_stage_zero hκ hκ4 hb hh hE hL0 hR0
  obtain ⟨hβ₀, hY₀, hpath₀, hker₀⟩ := stageWitness_zero (E := E) (θ := θ) (t₀ := t₀) (θ₀ := θ₀) hh hc₀J hc₀
  have hpost := post_stage (spec := spec) (E := E) (ℓ := 0)
    (Sec7.StripSideHeightProb.isStopLaw_stopWord hκ) hB hκ hb hh (fun j _ => hE.1 j) (fun j _ => hreg j)
    (hE.2.2.2 0) hβ₀ hY₀ hpath₀ hker₀
  have hpm : Measurable (pastMap κ b J spec E 1) :=
    measurable_pastMap hB hb _ (fun j _ => hE.1 j) (fun j _ => hreg j) 1 le_rfl
  have h𝒢 : pastSigma κ b J spec E 1 ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hr : Measurable (rec₀ κ b J θ₀ θ t₀ E) := measurable_pi_iff.1 hpm (Fin.last 0)
  have hY₁ : Measurable (fun ω => field₁ κ (rec₀ κ b J θ₀ θ t₀ E ω) (h ω)) :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => field₁ κ p.1 p.2)
      (f := fun ω => (rec₀ κ b J θ₀ θ t₀ E ω, h ω)) (measurable_field₁ κ) (hr.prodMk hh.1)
  -- the moving-chart field is a GFF with the stop word's data under the conditional law
  have hker₁ : ∀ᵐ ω₀ ∂P, IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b J spec E 1) ω₀)
      (fun ω => field₁ κ (rec₀ κ b J θ₀ θ t₀ E ω) (h ω)) (word₁ κ θ₀ c₀ (rec₀ κ b J θ₀ θ t₀ E ω₀)).fn
      (word₁ κ θ₀ c₀ (rec₀ κ b J θ₀ θ t₀ E ω₀)).jumps := by
    have hG := ae_isGFFWithBoundaryData_condExpKernel h𝒢 (M := univ)
      (β := fun ω => word₁ κ θ₀ c₀ (rec₀ κ b J θ₀ θ t₀ E ω))
      (Eventually.of_forall fun ω _ => isSorted_stopWord κ _) hY₁ (fun φ => by
        filter_upwards [hpost.2 φ] with ω hω _
        exact hω (launch_zero _) (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)))
    filter_upwards [hG] with ω₀ hω₀
    exact hω₀ (mem_univ _)
  filter_upwards [hζ₀, hker₁, hE.2.2.2 1, ae_ae_run_eq hB hb spec (k := 1) (fun j _ => hE.1 j)
    (fun j _ => hreg j) (P := P)] with ω₀ hz hk₀ hstg hrunK
  have h0 : (t₀ : ℝ≥0∞) < (E 0 ω₀).2 := by rw [hz.1]; exact ENNReal.coe_lt_top
  have hrec₀ : rec₀ κ b J θ₀ θ t₀ E ω₀ = recOf (t₀ : ℝ≥0∞) (E 0 ω₀) := pastMap_one_last ω₀
  -- the record is fixed by the conditional law
  have hrecK : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b J spec E 1) ω₀),
      rec₀ κ b J θ₀ θ t₀ E ω = recOf (t₀ : ℝ≥0∞) (E 0 ω₀) := by
    filter_upwards [hrunK] with ω hω
    rw [← hrec₀]
    change pastMap κ b J spec E 1 ω (Fin.last 0) = pastMap κ b J spec E 1 ω₀ (Fin.last 0)
    unfold pastMap
    rw [hω]
  have hfm : Measurable fun ω => recField κ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀)) (h ω) :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => recField κ p.1 p.2)
      (f := fun ω => (recOf (t₀ : ℝ≥0∞) (E 0 ω₀), h ω)) (measurable_recField κ) (measurable_const.prodMk hh.1)
  have hGff : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b J spec E 1) ω₀)
      (fun ω => recField κ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀)) (h ω)) (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀))).fn
      (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀))).jumps := by
    have e : (fun ω => field₁ κ (rec₀ κ b J θ₀ θ t₀ E ω) (h ω)) =ᵐ[condExpKernel P (pastSigma κ b J spec E 1) ω₀]
        fun ω => recField κ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀)) (h ω) := by
      filter_upwards [hrecK] with ω hω
      change recField κ (rec₀ κ b J θ₀ θ t₀ E ω) (flowField 0 0 (h ω)) = _
      rw [hω, GlueCond.flowField_zero_zero]
    have hk₀' := hk₀
    rw [hrec₀] at hk₀'
    exact isGFFWithBoundaryData_congr_ae hk₀' hfm e
  refine ⟨hz.1, hGff, ?_⟩
  -- the continuation is launched in the record chart at the angle `θ`
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1
    (launch_one_of_lt (κ := κ) (b := b) (jumps := J) (θ₀ := θ₀) (θ := θ) (D := fun j => E j ω₀) h0)
  have hθ' : θ' = θ := angle_of_launch _ _ hcθ
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches spec _ hcθ
  rw [chart_one_eq (hreg 0 ω₀) h0] at hc
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hstg c θ' hcθ
  subst hθ'
  have hh' : h' = fun ω => recField κ (recOf (t₀ : ℝ≥0∞) (E 0 ω₀)) (h ω) := funext fun ω => by
    rw [hc] at hT'
    exact IsChartTransport.unique (isConformal_recChart _) (hT' ω) (isChartTransport_recField κ _ (h ω))
  rw [hh'] at hfl
  exact isFlowLineDriver_word hκ hGff hb' hfl

end Stage

end InteractingSLE.Sec5.RestartSw
