/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripWallVersion
import InteractingSLE.Spec.Restart.StagedPathVersion

/-!
# Aux. lemma 119's conditional mean in the change pocket for any versions of the strip walls

Packet PROVE-STRIPSYS28, second item. Specification §7.4, Aux. lemma 119 and its proof (`source/spec/p385-432.md`
L3–L54, pp. 385–387) for the walls `L = β^{(r)} = η^{r,∞}_{π/2,θ₂}` and `R = α = η^{1,∞}_{−π/2,θ₁}` of (RS13.1), with
Aux. lemma 130's height choice (pp. 408–410).

PROVE-STRIPSYS27's `StripWall.ae_eqOn_changePocket_strip` assumed that the two walls are `IsWallVersion`s (simple
transient versions of the concatenated drivers' traces). That is now proved (`StripWall.isWallVersion_alpha`,
`StripWall.isWallVersion_beta`, `Spec/Sec7/StripWallVersion`), so here the walls are arbitrary **versions** of the
traces: continuous at every sample, starting at `0`, measurable at fixed times, and almost surely generating the
concatenated Loewner chain on `[0, ∞)`. Such versions exist (`StripWall.exists_isWallVersion_alpha`, `…_beta`, and
`exists_wallVersions_twoAngle` below, which also gives the continuation's own version and the join formula of
PROVE-LOEWNERCAT).

* **`ae_eqOn_changePocket_strip_of_trace`**: Aux. lemma 119's change-pocket mean for any versions `β`, `α` of the two
  walls. The remaining hypotheses are the regularity of the two staged histories' drivers (pathwise, every sample), the
  walls' entrance-history locality (Lemma 6.2's `hloc`; PROVE-STAGEDLOC2, in flight, proves it for the increasing wall
  from a version with a chart trace of the continuation — the data `exists_wallVersions_twoAngle` provides), and the
  local-set means (universally quantified versions);
* **`exists_wallVersions_twoAngle`**: a version `γ` of a two-angle wall and a version `η₁` of its continuation's trace
  (simple and transient almost surely) with `γ(t₀ + s) = F_{t₀}(η₁(s))`, `s > 0` (`F_{t₀}` the centred inverse Loewner
  map of the first piece).

No Theorem 1.2/1.3 (R43, R48); the only named input is `AdmCode.Theorem12ParamCond44Statement` (the §4.2 reference's
word-measurable Theorem 1.2 on (4.4) words, for the walls' field determination, as in PROVE-STRIPSYS21/27).
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

open QuantumZipper (H chiC fwdMapInv)
open LQGMetric (DistOn TestOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)
open Lemma71N (IsPocketBranch)
open PocketCoord PocketMarks Aux119Bdry LocalSets StripGeom Aux119Nested Aux2728Pocket

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-! ### The record chart of the first piece -/

omit mΩ [StandardBorelSpace Ω] in
/-- **The record chart's inverse is the centred inverse Loewner map**: for a regular driver with infinite lifetime, the
chart of its record at a deterministic time `t₀` maps `z ∈ ℍ` to `F_{t₀}(z) = fwdMapInv (rpath e.1) t₀ z`
(`Exist.StagedLaw.recChart_eq_loewner`; the inverse map reads the driver only on `[0, t₀]`). -/
theorem recChart_inv_eq {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) (he2 : e.2 = ⊤) (t₀ : ℝ≥0) {z : ℂ}
    (hz : z ∈ H) : (Exist.StagedLaw.recChart (Exist.StagedLaw.recOf (t₀ : ℝ≥0∞) e)).2.1 z =
      fwdMapInv (Ito.rpath e.1) t₀ z := by
  have hlt : (t₀ : ℝ≥0∞) < e.2 := by rw [he2]; exact ENNReal.coe_lt_top
  have hg := StripMark.isDrvGood_recOf_of_lt he hlt
  have hmin : (min (t₀ : ℝ≥0∞) e.2).toNNReal = t₀ := by rw [min_eq_left hlt.le, ENNReal.toNNReal_coe]
  rw [Exist.StagedLaw.recChart_eq_loewner he hg]
  change fwdMapInv (fun x : ℝ => (Exist.StagedLaw.retOf (t₀ : ℝ≥0∞) e).1 x.toNNReal)
    ((min (t₀ : ℝ≥0∞) e.2).toNNReal : ℝ) z = _
  rw [hmin]
  have hc : Continuous e.1 := continuous_of_isRegularDriver he he2
  have hr : Continuous (Exist.StagedLaw.retOf (t₀ : ℝ≥0∞) e).1 := Exist.StagedLaw.continuous_retOf he hg
  refine LP.fwdMapInv_eq_of_eqOn_Icc (hr.comp continuous_real_toNNReal) (hc.comp continuous_real_toNNReal)
    ?_ ?_ t₀.coe_nonneg (fun x hx => ?_) hz
  · change e.1 (min ((Real.toNNReal 0 : ℝ≥0) : ℝ≥0∞) (min (t₀ : ℝ≥0∞) e.2)).toNNReal = 0
    rw [Real.toNNReal_zero, ENNReal.coe_zero, min_eq_left zero_le, ENNReal.toNNReal_zero]
    exact he.2.1
  · change e.1 (Real.toNNReal 0) = 0
    rw [Real.toNNReal_zero]
    exact he.2.1
  · have hx' : x.toNNReal ≤ t₀ := Real.toNNReal_le_iff_le_coe.2 hx.2
    change e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (t₀ : ℝ≥0∞) e.2)).toNNReal = e.1 x.toNNReal
    rw [min_eq_left hlt.le, min_eq_left (ENNReal.coe_le_coe.2 hx'), ENNReal.toNNReal_coe]

/-! ### Versions of a two-angle wall and of its continuation -/

/-- **Versions of a two-angle wall and of its continuation** (under the hypotheses of `ae_simple_trace_catPath`): a
wall version `γ` (`IsWallVersion`) and a family `η₁`, continuous at every sample, starting at `0` and measurable at
fixed times, that is almost surely a simple transient generating trace of the continuation's driver `(E 1).1` on
`[0, ∞)`, with the join formula `γ(t₀ + s) = F_{t₀}(η₁(s))` for `s > 0`, `F_{t₀} = fwdMapInv (rpath (E 0).1) t₀` (the
centred inverse Loewner map of the first piece; PROVE-LOEWNERCAT), which is also the inverse of the first piece's record
chart (`recChart_inv_eq`; the form of PROVE-STAGEDLOC2's `hcat`). -/
theorem exists_wallVersions_twoAngle {θ₀ θ : ℝ} {t₀ : ℝ≥0} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ)
    (hθ : θ ≤ θ₀ + Real.pi) (hθ' : θ₀ ≤ θ + Real.pi) :
    ∃ γ η₁ : Ω → ℝ≥0 → ℂ, IsWallVersion P E t₀ γ ∧ (∀ ω, Continuous (η₁ ω)) ∧ (∀ ω, η₁ ω 0 = 0) ∧
      (∀ t, Measurable fun ω => η₁ ω t) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (E 1 ω).1 ⊤ (η₁ ω) ∧ Injective (η₁ ω) ∧ (∀ s, 0 < s → η₁ ω s ∈ H) ∧
        Tendsto (η₁ ω) atTop (cobounded ℂ) ∧
        ∀ s, 0 < s → γ ω (t₀ + s) = fwdMapInv (Ito.rpath (E 0 ω).1) t₀ (η₁ ω s) ∧
          γ ω (t₀ + s) = (Exist.StagedLaw.recChart (Exist.StagedLaw.recOf (t₀ : ℝ≥0∞) (E 0 ω))).2.1 (η₁ ω s) := by
  have hg1 := ae_goodPath_one hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθ'
  have hs0 := ae_trace_stage_zero hκ hκ4 hb hh hE hL0 hR0
  -- the continuation's version
  have hW1m : Measurable fun ω => (E 1 ω).1 := measurable_fst.comp (hE.1 1)
  have hW1 : ∀ᵐ ω ∂P, Continuous (E 1 ω).1 ∧ (E 1 ω).1 0 = 0 ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 1 ω).1 ⊤ η := by
    filter_upwards [hg1] with ω hω
    have hζ1 : (E 1 ω).2 = ⊤ := (mem_goodPathSet.1 hω).1
    have hc := continuous_of_isRegularDriver (hreg 1 ω) hζ1
    rw [mem_goodPathSet, hζ1] at hω
    obtain ⟨η, hη, -⟩ := exists_simple_trace_of_goodPath hc (hreg 1 ω).2.1 hω
    exact ⟨hc, (hreg 1 ω).2.1, η, hη⟩
  obtain ⟨η₁, hη₁c, hη₁m, hη₁0, hη₁⟩ := Restart.StagedPathVersion.exists_continuous_version hW1m hW1
  -- the wall's version
  obtain ⟨γ, hγ, -⟩ := exists_isWallVersion_twoAngle hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθ'
  refine ⟨γ, η₁, hγ, hη₁c, hη₁0, hη₁m, ?_⟩
  filter_upwards [hg1, hs0, hη₁, hγ.ae_trace] with ω hg hs hη hγω
  obtain ⟨hζ0, η₀, hη₀, hinj₀, hH₀, -⟩ := hs
  have hζ1 : (E 1 ω).2 = ⊤ := (mem_goodPathSet.1 hg).1
  have hc0 := continuous_of_isRegularDriver (hreg 0 ω) hζ0
  have hc1 := continuous_of_isRegularDriver (hreg 1 ω) hζ1
  rw [mem_goodPathSet, hζ1] at hg
  obtain ⟨η, hηg, hinj, hH, htr⟩ := exists_simple_trace_of_goodPath hc1 (hreg 1 ω).2.1 hg
  have e1 : η₁ ω = η := funext fun t => hη.2 η hηg t
  rw [e1]
  refine ⟨hηg, hinj, hH, tendsto_norm_atTop_iff_cobounded.1 htr, fun s hs => ?_⟩
  -- the wall version is the joined trace
  have hjoin := LoewnerConcat.isGeneratingTrace_catPath hc0 (hreg 0 ω).2.1 hc1 (hreg 1 ω).2.1
    (IsGeneratingTrace.mono_horizon hη₀ (le_top : ((t₀ : ℝ≥0) : ℝ≥0∞) ≤ ⊤)) hηg hH
  obtain ⟨hcc, hcc0⟩ := continuous_catPath_of_isRegularDriver (hreg 0 ω) (hreg 1 ω) hζ0 hζ1 t₀
  have e2 : γ ω (t₀ + s) = LoewnerConcat.joinedTrace (E 0 ω).1 η₀ t₀ η (t₀ + s) := by
    rw [← LP.traceAt_eq_of_isGeneratingTrace hγω.1 hcc.continuousOn hcc0 ENNReal.coe_lt_top,
      LP.traceAt_eq_of_isGeneratingTrace hjoin hcc.continuousOn hcc0 ENNReal.coe_lt_top]
  rw [e2, joinedTrace_of_lt hc0 (hreg 0 ω).2.1 hH (lt_add_of_pos_right t₀ hs), add_tsub_cancel_left,
    recChart_inv_eq (hreg 0 ω) hζ0 t₀ (hH s hs)]
  exact ⟨rfl, rfl⟩

/-! ### The change pocket of the strip walls, for any versions -/

/-- **Aux. lemma 119's conditional mean in the change pocket of the strip walls, for any versions of the walls**
(spec pp. 385–387, 408–410). `β`, `α` are versions of the traces of the walls `β^{(r)} = η^{r,∞}_{π/2,θ₂}` and
`α = η^{1,∞}_{−π/2,θ₁}` of the strip system `hS` (continuous, starting at `0`, measurable at fixed times, almost surely
generating the concatenated chain on `[0, ∞)`); by `isWallVersion_beta`, `isWallVersion_alpha` they are simple
transient wall versions, and `ae_eqOn_changePocket_strip` applies. `hcumL`, `hcumR` are Aux. lemma 130's height
choice. Remaining hypotheses: the regularity of the two staged histories' drivers, the walls' entrance-history locality,
the local-set means. Almost surely, for every harmonic representative `v` of the mean `gU` of the wall union and every
flow chart `c` of a change pocket on the left of `α` with the common lift's integer `n`, on the pocket `v + u₀` is the
bounded Poisson extension `G` of the two-angle heights pulled back by `c`, minus `χ (arg c′ + 2πn)`. -/
theorem ae_eqOn_changePocket_strip_of_trace (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec r θ₂) 0 ω).1 r
      (E (StripSys.betaSpec r θ₂) 1 ω).1) ⊤ (β ω))
    (hlocβ : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => β ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gL q))
    (hgR : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gR q)) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion β α ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion β α ω → gU ω φ = ∫ z, v z * φ z) →
      ∀ (r' : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      IsFlowChart (α ω) (β ω) r' Ψ c → changePocket (α ω) (β ω) r' ⊆ leftSideOf (range (α ω)) →
      IsDerivLog c.1 ℓ (changePocket (α ω) (β ω) r') →
      (∀ z ∈ changePocket (α ω) (β ω) r', c.2.2 z = (ℓ z).im) → IsPocketBranch (β ω) (α ω) c n →
      IsBoundedHarmonicExtension
        (chartData (β ω) (α ω) (fun s => sleLambda κ - (if s < r then π / 2 else θ₂) * chiC κ)
          (fun s => -sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ) c)
        (exSet (β ω) (α ω) {r} {1} c) G →
      ∀ z ∈ changePocket (α ω) (β ω) r', v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) :=
  ae_eqOn_changePocket_strip h44 hS hcumL hcumR hθ₁ hθ₂ r hregα hregβ hu₀
    (isWallVersion_beta hS hcumL hcumR hθ₂ r hregβ hβc hβ0 hβm hβtr) hlocβ
    (isWallVersion_alpha hS hcumL hcumR hθ₁ hregα hαc hα0 hαm hαtr) hlocα hgU hgL hgR

end StripWall

end Sec7

end InteractingSLE
