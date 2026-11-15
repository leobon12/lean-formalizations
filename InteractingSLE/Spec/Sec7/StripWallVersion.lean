/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripWallVersionPiece
import InteractingSLE.Foundations.Loewner.Concat
import InteractingSLE.Spec.Sec5.CrossRestartTrace

/-!
# The strip walls' versions: a simple transient trace of the concatenated driver

Packet PROVE-STRIPSYS28. Specification §7.4, proof of Aux. lemma 130 (`source/spec/p385-432.md`, p. 410): "the
continuously extended inverse own map therefore gives a continuous simple complete concatenation". PROVE-STRIPSYS27
reduced the walls' versions (`IsWallVersion`) to the pathwise statement that the concatenated driver
`catPath (E 0).1 t₀ (E 1).1` almost surely has a simple transient generating trace (`exists_isWallVersion`). Here:

* **the join is simple and transient** (deterministic): for a simple generating trace `η₀` of the first driver and a
  simple transient generating trace `η₁` of the continuation, PROVE-LOEWNERCAT's joined trace
  `LoewnerConcat.joinedTrace w₀ η₀ a η₁` (a generating trace of `catPath w₀ a w₁` on `[0, ∞)`,
  `LoewnerConcat.isGeneratingTrace_catPath`) is injective, in `ℍ` at positive times (`joinedTrace_simple`: the prefix
  points of `ℍ` lie in the hull `K_a`, the continuation points in `F_a(ℍ) = ℍ \ K_a`, `F_a` injective on `ℍ`), and
  tends to `∞` (`tendsto_joinedTrace`: `F_a` moves points a bounded distance);
* **`ae_simple_trace_catPath`**: for a two-angle staged history with the (4.4) heights at the first angle and
  admissible heights at the second, `|θ − θ₀| ≤ π`, almost surely both pieces live forever and the concatenated driver
  has a simple transient generating trace (first piece: `ae_trace_stage_zero`; continuation: `ae_goodPath_one`);
* **`exists_isWallVersion_twoAngle`**, **`isWallVersion_of_isGeneratingTrace`**: a version of the wall exists, and every
  continuous, measurable family that almost surely generates the concatenated chain is one (trace uniqueness);
* the strip system's walls `α = η^{1,∞}_{−π/2,θ₁}` and `β^{(r)} = η^{r,∞}_{π/2,θ₂}` (Aux. lemma 130's height choice):
  `exists_isWallVersion_alpha`, `exists_isWallVersion_beta`, `isWallVersion_alpha`, `isWallVersion_beta`.

No Theorem 1.2/1.3 and no `AdmCode.Theorem12ParamCond44Statement` (R43, R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE

namespace Sec7

namespace StripWall

open QuantumZipper (H chiC fwdHull fwdMapInv)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)
open LoewnerConcat (joinedTrace)
open LQGMetric (DistOn)

/-! ### The join of two simple traces -/

section Joined

variable {w₀ w₁ : ℝ≥0 → ℝ} {η₀ η₁ : ℝ≥0 → ℂ} {a : ℝ≥0}

/-- After the join time the joined trace is the inverse map of the prefix applied to the continuation. -/
theorem joinedTrace_of_lt (h₀ : Continuous w₀) (h00 : w₀ 0 = 0) (hH₁ : ∀ s, 0 < s → η₁ s ∈ H) {t : ℝ≥0}
    (ht : a < t) : joinedTrace w₀ η₀ a η₁ t = fwdMapInv (Ito.rpath w₀) a (η₁ (t - a)) := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  have hta : ¬ t ≤ a := not_le.2 ht
  simp only [joinedTrace, hta, ↓reduceIte]
  exact extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 a.coe_nonneg) (hH₁ _ (tsub_pos_iff_lt.2 ht))

/-- After the join time the joined trace lies in `ℍ \ K_a`. -/
theorem joinedTrace_mem_of_lt (h₀ : Continuous w₀) (h00 : w₀ 0 = 0) (hH₁ : ∀ s, 0 < s → η₁ s ∈ H) {t : ℝ≥0}
    (ht : a < t) : joinedTrace w₀ η₀ a η₁ t ∈ H \ fwdHull (Ito.rpath w₀) a := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  rw [joinedTrace_of_lt h₀ h00 hH₁ ht]
  exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 a.coe_nonneg (hH₁ _ (tsub_pos_iff_lt.2 ht))

/-- The prefix through the join time never lies in `ℍ \ K_a`: its points in `ℍ` are in the hull. -/
theorem prefix_notMem (hη₀ : IsGeneratingTrace w₀ ⊤ η₀) {t : ℝ≥0} (ht : t ≤ a) :
    η₀ t ∉ H \ fwdHull (Ito.rpath w₀) a := by
  rintro ⟨hH, hK⟩
  have hfill : IsFilling (fwdHull (fun s : ℝ => w₀ s.toNNReal) a) (η₀ '' Icc 0 a) :=
    hη₀.2.2 a ENNReal.coe_lt_top
  exact hK (Sec5.CrossRestart.inter_H_subset_of_isFilling hfill ⟨⟨t, ⟨zero_le, ht⟩, rfl⟩, hH⟩)

/-- **The join of two simple traces is simple**: injective, and in `ℍ` at positive times. -/
theorem joinedTrace_simple (h₀ : Continuous w₀) (h00 : w₀ 0 = 0) (hη₀ : IsGeneratingTrace w₀ ⊤ η₀)
    (hinj₀ : Injective η₀) (hH₀ : ∀ t, 0 < t → η₀ t ∈ H) (hinj₁ : Injective η₁) (hH₁ : ∀ s, 0 < s → η₁ s ∈ H) :
    Injective (joinedTrace w₀ η₀ a η₁) ∧ ∀ t, 0 < t → joinedTrace w₀ η₀ a η₁ t ∈ H := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  -- a prefix value never equals a continuation value
  have hcross : ∀ s t : ℝ≥0, s ≤ a → a < t → joinedTrace w₀ η₀ a η₁ s ≠ joinedTrace w₀ η₀ a η₁ t := by
    intro s t hs ht he
    rw [LoewnerConcat.joinedTrace_of_le hs] at he
    exact prefix_notMem hη₀ hs (he ▸ joinedTrace_mem_of_lt h₀ h00 hH₁ ht)
  refine ⟨fun s t hst => ?_, fun t ht => ?_⟩
  · rcases le_or_gt s a with hs | hs <;> rcases le_or_gt t a with ht | ht
    · rw [LoewnerConcat.joinedTrace_of_le hs, LoewnerConcat.joinedTrace_of_le ht] at hst
      exact hinj₀ hst
    · exact absurd hst (hcross s t hs ht)
    · exact absurd hst.symm (hcross t s ht hs)
    · rw [joinedTrace_of_lt h₀ h00 hH₁ hs, joinedTrace_of_lt h₀ h00 hH₁ ht] at hst
      have h1 := QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 a.coe_nonneg (hH₁ _ (tsub_pos_iff_lt.2 hs))
        (hH₁ _ (tsub_pos_iff_lt.2 ht)) hst
      have h2 := hinj₁ h1
      exact (tsub_left_inj hs.le ht.le).1 h2
  · rcases le_or_gt t a with hta | hta
    · rw [LoewnerConcat.joinedTrace_of_le hta]
      exact hH₀ t ht
    · exact (joinedTrace_mem_of_lt h₀ h00 hH₁ hta).1

/-- **The join of a transient continuation is transient**: the inverse map of the prefix moves points of `ℍ` a bounded
distance (`exists_norm_fwdMapInv_sub_le`). -/
theorem tendsto_joinedTrace (h₀ : Continuous w₀) (h00 : w₀ 0 = 0) (hH₁ : ∀ s, 0 < s → η₁ s ∈ H)
    (ht₁ : Tendsto (fun s => ‖η₁ s‖) atTop atTop) :
    Tendsto (fun t => ‖joinedTrace w₀ η₀ a η₁ t‖) atTop atTop := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 a.coe_nonneg
  have hsub : Tendsto (fun t : ℝ≥0 => t - a) atTop atTop :=
    tendsto_atTop_atTop.2 fun c => ⟨c + a, fun t ht => le_tsub_of_add_le_right ht⟩
  have hlow : Tendsto (fun t : ℝ≥0 => ‖η₁ (t - a)‖ + -C) atTop atTop :=
    tendsto_atTop_add_const_right _ (-C) (ht₁.comp hsub)
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [eventually_gt_atTop a] with t ht
  rw [joinedTrace_of_lt h₀ h00 hH₁ ht]
  have h1 := hC _ (hH₁ _ (tsub_pos_iff_lt.2 ht))
  have h2 := norm_sub_norm_le (η₁ (t - a)) (fwdMapInv (Ito.rpath w₀) a (η₁ (t - a)))
  rw [norm_sub_rev (η₁ (t - a))] at h2
  linarith

/-- **A simple transient trace of the concatenated driver** (deterministic): for continuous drivers starting at `0`,
a simple generating trace `η₀` of the first on `[0, ∞)` and a good path `w₁` (`WangWu.ImgDrv.GoodPath`: a simple
transient generating trace), the concatenated driver `catPath w₀ a w₁` has an injective generating trace on `[0, ∞)`,
in `ℍ` at positive times, tending to `∞` (PROVE-LOEWNERCAT's joined trace). -/
theorem exists_simple_trace_catPath (h₀ : Continuous w₀) (h00 : w₀ 0 = 0) (h₁ : Continuous w₁) (h10 : w₁ 0 = 0)
    (hη₀ : IsGeneratingTrace w₀ ⊤ η₀) (hinj₀ : Injective η₀) (hH₀ : ∀ t, 0 < t → η₀ t ∈ H)
    (hg : WangWu.ImgDrv.GoodPath w₁ ⊤) (a : ℝ≥0) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (catPath w₀ a w₁) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
      Tendsto η atTop (cobounded ℂ) := by
  obtain ⟨η₁', hη₁, hinj₁, hH₁, ht₁⟩ := exists_simple_trace_of_goodPath h₁ h10 hg
  obtain ⟨hinj, hH⟩ := joinedTrace_simple (a := a) h₀ h00 hη₀ hinj₀ hH₀ hinj₁ hH₁
  exact ⟨joinedTrace w₀ η₀ a η₁', LoewnerConcat.isGeneratingTrace_catPath h₀ h00 h₁ h10
    (IsGeneratingTrace.mono_horizon hη₀ le_top) hη₁ hH₁, hinj, hH,
    tendsto_norm_atTop_iff_cobounded.1 (tendsto_joinedTrace h₀ h00 hH₁ ht₁)⟩

end Joined

/-! ### The walls' traces and versions -/

section Walls

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The concatenated driver of a two-angle path has a simple transient trace** (spec p. 410). For a two-angle staged
history of a GFF with data `b` having the (4.4) heights at the first angle `θ₀` and the heights `b + θχ ≤ −λ + πχ`
left, `b + θχ ≥ λ − πχ` right at the second angle `θ`, `|θ − θ₀| ≤ π`, almost surely both pieces live forever and
`catPath (E 0).1 t₀ (E 1).1` has an injective generating trace on `[0, ∞)`, in `ℍ` at positive times, tending to
`∞`. -/
theorem ae_simple_trace_catPath (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ)
    (hθ : θ ≤ θ₀ + Real.pi) (hθ' : θ₀ ≤ θ + Real.pi) :
    ∀ᵐ ω ∂P, ((E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤) ∧ ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
        Tendsto η atTop (cobounded ℂ) := by
  filter_upwards [ae_trace_stage_zero hκ hκ4 hb hh hE hL0 hR0,
    ae_goodPath_one hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθ'] with ω h0 h1
  obtain ⟨hζ0, η₀, hη₀, hinj₀, hH₀, -⟩ := h0
  have hζ1 : (E 1 ω).2 = ⊤ := (mem_goodPathSet.1 h1).1
  rw [mem_goodPathSet, hζ1] at h1
  refine ⟨⟨hζ0, hζ1⟩, ?_⟩
  exact exists_simple_trace_catPath (continuous_of_isRegularDriver (hreg 0 ω) hζ0) (hreg 0 ω).2.1
    (continuous_of_isRegularDriver (hreg 1 ω) hζ1) (hreg 1 ω).2.1 hη₀ hinj₀ hH₀ h1 t₀

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Every version of the trace is a wall version**: a family continuous at every sample, starting at `0`, measurable
at fixed times and almost surely a generating trace of the concatenated driver on `[0, ∞)` is an `IsWallVersion`
when the concatenated driver almost surely has a simple transient trace (generating traces of a continuous driver
are unique). -/
theorem isWallVersion_of_isGeneratingTrace (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hsimple : ∀ᵐ ω ∂P, ((E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤) ∧ ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
        Tendsto η atTop (cobounded ℂ))
    {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0)
    (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω)) :
    IsWallVersion P E t₀ γ := by
  refine ⟨hγc, hγ0, hγm, ?_⟩
  filter_upwards [hsimple, hγtr] with ω hs hγ
  obtain ⟨⟨h0, h1⟩, η, hη, hinj, hH, htr⟩ := hs
  obtain ⟨hcc, hc0⟩ := continuous_catPath_of_isRegularDriver (hreg 0 ω) (hreg 1 ω) h0 h1 t₀
  have e : γ ω = η := funext fun t => by
    rw [← LP.traceAt_eq_of_isGeneratingTrace hγ hcc.continuousOn hc0 ENNReal.coe_lt_top,
      LP.traceAt_eq_of_isGeneratingTrace hη hcc.continuousOn hc0 ENNReal.coe_lt_top]
  rw [e]
  exact ⟨hη, hinj, hH, htr⟩

/-- **A version of a two-angle wall exists** (under the hypotheses of `ae_simple_trace_catPath`), read by
`LP.traceAt` from the concatenated driver on a measurable full-measure set. -/
theorem exists_isWallVersion_twoAngle (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ)
    (hθ : θ ≤ θ₀ + Real.pi) (hθ' : θ₀ ≤ θ + Real.pi) :
    ∃ γ : Ω → ℝ≥0 → ℂ, IsWallVersion P E t₀ γ ∧
      ∀ᵐ ω ∂P, ∀ t, γ ω t = LP.traceAt t (catPath (E 0 ω).1 t₀ (E 1 ω).1) := by
  have hs := ae_simple_trace_catPath hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθ'
  exact exists_isWallVersion (fun k => hE.1 k) hreg t₀ (hs.mono fun ω hω => hω.1) (hs.mono fun ω hω => hω.2)

/-! ### The strip system's walls -/

variable {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The wall `α = η^{1,∞}_{−π/2,θ₁}` has a simple transient trace** almost surely (Aux. lemma 130's height choice:
every original-boundary cumulative value nonnegative at every angle in `[−π/2, π/2]`). -/
theorem ae_simple_trace_alpha (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω)) :
    ∀ᵐ ω ∂P, ((Es (StripSys.alphaSpec θ₁) 0 ω).2 = ⊤ ∧ (Es (StripSys.alphaSpec θ₁) 1 ω).2 = ⊤) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
        (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
        Tendsto η atTop (cobounded ℂ) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ; linarith
  exact ae_simple_trace_catPath hκ hκ4 hS.boundaryData hS.gff (hS.isStagedHistory_alpha hθ₁) hregα
    (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁) (fun y hy hyJ => by have := hcumR _ hθ₁ y hy hyJ; linarith)
    (by linarith [hθ₁.2, Real.pi_pos]) (by linarith [hθ₁.1, Real.pi_pos])

/-- **The wall `β^{(r)} = η^{r,∞}_{π/2,θ₂}` has a simple transient trace** almost surely (the decreasing change; Aux.
lemma 130's height choice). -/
theorem ae_simple_trace_beta (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec r θ₂) j ω)) :
    ∀ᵐ ω ∂P, ((Es (StripSys.betaSpec r θ₂) 0 ω).2 = ⊤ ∧ (Es (StripSys.betaSpec r θ₂) 1 ω).2 = ⊤) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r
        (Es (StripSys.betaSpec r θ₂) 1 ω).1) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
        Tendsto η atTop (cobounded ℂ) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hp := StripSys.pi_div_two_mem_Icc
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ; linarith
  exact ae_simple_trace_catPath hκ hκ4 hS.boundaryData hS.gff (hS.isStagedHistory_beta hθ₂ r) hregβ
    (hL44 _ hp) (hcumR _ hp) (hL44 _ hθ₂) (fun y hy hyJ => by have := hcumR _ hθ₂ y hy hyJ; linarith)
    (by linarith [hθ₂.2, Real.pi_pos]) (by linarith [hθ₂.1, Real.pi_pos])

/-- **A version of the wall `α` exists.** -/
theorem exists_isWallVersion_alpha (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω)) :
    ∃ γ : Ω → ℝ≥0 → ℂ, IsWallVersion P (Es (StripSys.alphaSpec θ₁)) 1 γ ∧
      ∀ᵐ ω ∂P, ∀ t, γ ω t = LP.traceAt t (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
        (Es (StripSys.alphaSpec θ₁) 1 ω).1) := by
  have hs := ae_simple_trace_alpha hS hcumL hcumR hθ₁ hregα
  exact exists_isWallVersion (fun k => (hS.isStagedHistory_alpha hθ₁).1 k) hregα 1 (hs.mono fun ω hω => hω.1)
    (hs.mono fun ω hω => hω.2)

/-- **A version of the wall `β^{(r)}` exists.** -/
theorem exists_isWallVersion_beta (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec r θ₂) j ω)) :
    ∃ γ : Ω → ℝ≥0 → ℂ, IsWallVersion P (Es (StripSys.betaSpec r θ₂)) r γ ∧
      ∀ᵐ ω ∂P, ∀ t, γ ω t = LP.traceAt t (catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r
        (Es (StripSys.betaSpec r θ₂) 1 ω).1) := by
  have hs := ae_simple_trace_beta hS hcumL hcumR hθ₂ r hregβ
  exact exists_isWallVersion (fun k => (hS.isStagedHistory_beta hθ₂ r).1 k) hregβ r (hs.mono fun ω hω => hω.1)
    (hs.mono fun ω hω => hω.2)

/-- **Every version of the wall `α` is a wall version** (`isWallVersion_of_isGeneratingTrace`). -/
theorem isWallVersion_alpha (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    {α : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    IsWallVersion P (Es (StripSys.alphaSpec θ₁)) 1 α :=
  isWallVersion_of_isGeneratingTrace hregα (ae_simple_trace_alpha hS hcumL hcumR hθ₁ hregα) hαc hα0 hαm hαtr

/-- **Every version of the wall `β^{(r)}` is a wall version** (`isWallVersion_of_isGeneratingTrace`). -/
theorem isWallVersion_beta (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec r θ₂) j ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r
      (Es (StripSys.betaSpec r θ₂) 1 ω).1) ⊤ (β ω)) :
    IsWallVersion P (Es (StripSys.betaSpec r θ₂)) r β :=
  isWallVersion_of_isGeneratingTrace hregβ (ae_simple_trace_beta hS hcumL hcumR hθ₂ r hregβ) hβc hβ0 hβm hβtr

end Walls

end StripWall

end Sec7

end InteractingSLE
