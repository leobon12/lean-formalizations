/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartSwStage

/-!
# The switched-wall restart law (Lemma 5.7 with `ℓ = 2`) from Lemma 4.7's conditional law at the switch

Packet PROVE-SWITCHED, route (a) of `planning/handoffs/PROVE-RESTART-GEN.md` §4.1. Specification p. 138 (Lemma 5.7's
proof): "Fix an `η` stopping time `σ` … We apply a conformal transformation `ψ : 𝒮 ∖ η([0, σ]) → 𝒮` … the boundary data
for the GFF which describes the evolution of `ψ(η′)` is as in the right panel of Figure 5.5 … This implies that `η′`
almost surely exits `𝒮 ∖ η([0, σ])` at `η(σ)`"; Remark 5.8: "the first-exit conditional law in the remaining
component".

**The named input** (`CounterflowGivenPrefixStatement`, Lemma 4.7's conditional law at a deterministic own time, spec
p. 118 and Remark 5.8): for the strip field (Aux. lemma 130's heights) with its centred counterflow `η′` (driver `W′`,
infinite lifetime), every angle-`θ₀` flow-line driver `D` of `h` (`θ₀ ∈ [−π/2, π/2]`, regular at every sample) and every
own time `t₀`: conditionally on the record of `D` stopped at `t₀`, the counterflow read in the record chart `c` of the
remaining domain `ℍ ∖ K_{t₀}` (tip to `0`, `∞` fixed) is the centred counterflow of the field read in `c` (frozen
`IsCenteredCounterflowDriver`, under `condExpKernel`), with infinite lifetime; pathwise, a continuous increasing clock
`ℓ` from `0` carries the image counterflow `η″` to the physical one: `R(η′(ℓ(u))) = c⁻¹(R(η″(u)))`,
`R(η″(u)) ∈ ℍ`, `u > 0`.

**Proved here:**

* `ae_isFirstHitQ_of_isFlowLine_refl`: the one-angle restart law at relative angle `θ` from Lemma 4.7 at `−θ`, by the
  reflection `z ↦ −z̄` (for the decreasing changes, whose stop word satisfies (4.4) only after reflection);
* `ae_forall_isFirstHitQ_of_heights`: the one-angle law at all rational times, either orientation;
* `isFirstHitQ_wall_of_chart` (pathwise): the conditional first contacts give the wall's first contact after the switch
  (all real times from the rational ones, then the pull-back through the record chart);
* **`ae_isFirstHitQ_switched_of_reg`**: the first exit after the switch for a two-angle staged history regular at every
  sample (the strip walls of `Sec7.PocketWordIn` and `Sec7.WallsPath` are), from Lemma 4.7 at relative angle `θ`
  (`RestartGen.Lemma47QHitTStatement`), the §4.2 reference and the named input. Under `Q = condExpKernel` given the
  first record, the continuation is the angle-`θ` flow line of the stage field (`ae_stage_one`), the input supplies the
  counterflow of the same field, the one-angle law applies under `Q`, and the measurable first-contact code
  (`RestartGen.FirstHitCode`) carries the conclusion back to `P`;
* **`switchedWallFirstHitRegStatement_of_input`**: `SwitchedWallFirstHitRegStatement` (`RestartGen`'s
  `SwitchedWallFirstHitStatement` for staged histories regular at every sample).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull fwdMapInv)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.RestartSw

open WangWu (negInv histLine)
open Prop411Q (IsFirstHitQ)
open Cond44Ref (cfHistory)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.FlowReflect (reflData reflJumps)
open Sec7.Lemma71I (realPath)
open Sec7.StripSideHeightProb (catPath)
open Exist Exist.Staged Exist.StagedLaw Exist.StagedLaw.BoundaryWord Sec7.StripDet

/-! ### The named input: Lemma 4.7's conditional law at a deterministic own time -/

/-- **Named input: the counterflow given a stopped flow-line prefix** (Lemma 4.7's conditional law, spec p. 118;
Lemma 5.7's proof, p. 138, and Remark 5.8: "the first-exit conditional law in the remaining component"). Setting: the
strip field — a GFF `h` on `ℍ` with piecewise-constant data `b` and Aux. lemma 130's heights, its centred counterflow
(driver `W′`, almost surely infinite lifetime, trace `η` in the chart `R(z) = −1/z`) — an angle-`θ₀` flow-line driver
`D` of `h` (`θ₀ ∈ [−π/2, π/2]`, measurable, regular at every sample) and an own time `t₀`. Conclusion: there are a
driver `W″` with lifetime `ζ″` and a family `η″` such that

* for almost every `ω₀`, under the regular conditional law given the record `recOf t₀ D` of the prefix, `W″` drives the
  centred counterflow of the field read in the record chart of `ω₀` (`recField`, the conditional field in the remaining
  domain `ℍ ∖ K_{t₀}`, tip at `0`), with infinite lifetime;
* almost surely `η″` is the generating trace of `W″`, and a continuous increasing clock `ℓ` from `0` carries it to the
  physical counterflow before its arrival at the tip: `R(η′(ℓ u)) = c⁻¹(R(η″ u))` with `R(η″ u) ∈ ℍ` for `u > 0`,
  `c` the record chart (`c⁻¹ : ℍ → ℍ ∖ K_{t₀}`). -/
def CounterflowGivenPrefixStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    0 < κ → κ < 4 → IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ) →
    ∀ θ₀ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) → ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable D →
    (∀ ω, IsRegularDriver (D ω)) → IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2) →
    ∀ (t₀ : ℝ≥0) (η : Ω → ℝ≥0 → ℂ), (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) →
    ∃ (W'' : ℝ≥0 → Ω → ℝ) (ζ'' : Ω → ℝ≥0∞) (η'' : Ω → ℝ≥0 → ℂ),
      (∀ᵐ ω₀ ∂P,
        IsCenteredCounterflowDriver κ
            (condExpKernel P (MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance) ω₀)
            (fun ω => recField κ (recOf (t₀ : ℝ≥0∞) (D ω₀)) (h ω)) W'' ζ'' ∧
          ∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance) ω₀),
            ζ'' ω = ⊤) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → negInv (η'' ω u) ∈ H ∧
            negInv (η ω (ℓ u)) = (recChart (recOf (t₀ : ℝ≥0∞) (D ω))).2.1 (negInv (η'' ω u))

/-- **`SwitchedWallFirstHitStatement` for staged histories regular at every sample** (the form the wall consumers
`Sec7.PocketWordIn.pocketWordEvolution_of_stripSystem_firstHit` and
`Sec7.WallsPath.pocketWordEvolution_of_stripSystem_path` use: they carry `IsRegularDriver` for the two-angle walls at
every sample). -/
def SwitchedWallFirstHitRegStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ) →
    ∀ θ₀ θ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) → θ ∈ Icc (-(π / 2)) (π / 2) →
    ∀ (t₀ : ℝ≥0) (R : Ω → ℝ≥0 → ℂ), (∀ j ω, IsRegularDriver (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) j ω)) →
      Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R →
    ∀ η : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) →
    ∀ q : ℚ, (t₀ : ℝ) < q →
      ∀ᵐ ω ∂P, IsFirstHitQ (realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q

/-! ### The one-angle law at both orientations -/

/-- **The one-angle restart law at relative angle `θ` by reflection**: from Lemma 4.7 at relative angle `−θ` and the
(4.4) heights of the reflected data `y ↦ −b(−y)` at `−θ` and `π/2`. -/
theorem ae_isFirstHitQ_of_isFlowLine_refl {θ : ℝ} (h47 : RestartGen.Lemma47QHitTStatement.{u} (-θ))
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hθ : IsHeightBounded44 κ (reflData b) (reflJumps J) (-θ))
    (hπ : IsHeightBounded44 κ (reflData b) (reflJumps J) (π / 2))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b J 0 θ P h β ζ) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (realPath (β ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  have hβ' := Sec7.FlowReflect.IsFlowLine.reflect hb hβ
  rw [neg_zero] at hβ'
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W') t ω) ⊤ (fun t => LP.reflectC (η ω t)) :=
    hη.mono fun ω hω => LP.isGeneratingTrace_reflect hω
  filter_upwards [RestartGen.ae_isFirstHitQ_of_isFlowLine_heights h47 href hκ hκ4
    (Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb) hθ hπ
    (Sec7.FlowReflect.IsGFFWithBoundaryData.reflect hh) (Sec7.R7Outer.isCenteredCounterflowDriver_reflect hκ hcf)
    hζ' hη' hβ' q hq] with ω hω
  exact RestartGen.isFirstHitQ_reflect hω

/-- **The one-angle law at every positive rational time, either orientation**: Lemma 4.7 at relative angle `θ` with the
(4.4) heights at `θ` and `π/2` (an increasing change), or Lemma 4.7 at `−θ` with the heights of the reflected data at
`−θ` and `π/2` (a decreasing change). -/
theorem ae_forall_isFirstHitQ_of_heights (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ}
    (hhgt : (RestartGen.Lemma47QHitTStatement.{u} θ ∧ IsHeightBounded44 κ b J θ ∧
        IsHeightBounded44 κ b J (π / 2)) ∨
      (RestartGen.Lemma47QHitTStatement.{u} (-θ) ∧ IsHeightBounded44 κ (reflData b) (reflJumps J) (-θ) ∧
        IsHeightBounded44 κ (reflData b) (reflJumps J) (π / 2)))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b J 0 θ P h β ζ) :
    ∀ᵐ ω ∂P, ∀ r : ℚ, 0 < r → IsFirstHitQ (realPath (β ω)) (fun s : ℝ => η ω s.toNNReal) r := by
  rw [ae_all_iff]
  intro r
  by_cases hr : 0 < r
  · rcases hhgt with ⟨h47, h1, h2⟩ | ⟨h47, h1, h2⟩
    · filter_upwards [RestartGen.ae_isFirstHitQ_of_isFlowLine_heights h47 href hκ hκ4 hb h1 h2 hh hcf
        hζ' hη hβ r hr] with ω hω _ using hω
    · filter_upwards [ae_isFirstHitQ_of_isFlowLine_refl h47 href hκ hκ4 hb h1 h2 hh hcf hζ' hη hβ r
        hr] with ω hω _ using hω
  · exact Eventually.of_forall fun ω h' => absurd h' hr

/-! ### Pathwise steps -/

/-- **The wall prefix lies outside the image of the inverse chart**: if `R` generates the concatenated chain
`catPath w₀ t₀ w₁` on `[0, ∞)`, then for `t ≤ t₀` the point `R t ∈ ℍ` lies in the hull `K_{t₀}` of `w₀`, hence not in
`F_{t₀}(ℍ) = ℍ ∖ K_{t₀}`. -/
theorem notMem_fwdMapInv_image_of_le {w₀ w₁ : ℝ≥0 → ℝ} {t₀ : ℝ≥0} {R : ℝ≥0 → ℂ} (h₀ : Continuous w₀)
    (h00 : w₀ 0 = 0) (h₁ : Continuous w₁) (h10 : w₁ 0 = 0) (hR : IsGeneratingTrace (catPath w₀ t₀ w₁) ⊤ R)
    {t : ℝ≥0} (ht : t ≤ t₀) (hRt : R t ∈ H) : R t ∉ fwdMapInv (Ito.rpath w₀) t₀ '' H := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  have hK : fwdHull (Ito.rpath (catPath w₀ t₀ w₁)) t₀ = fwdHull (Ito.rpath w₀) t₀ :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc (Sec7.StripSideHeightProb.continuous_rpath_catPath h₀ h₁ h10) hW
      t₀.coe_nonneg (fun r hr => Sec7.StripSideHeightProb.rpath_catPath_eqOn hr)
  have hfill : IsFilling (fwdHull (fun s : ℝ => catPath w₀ t₀ w₁ s.toNNReal) t₀) (R '' Icc 0 t₀) :=
    hR.2.2 t₀ ENNReal.coe_lt_top
  have hmem : R t ∈ fwdHull (Ito.rpath w₀) t₀ := by
    rw [← hK]
    exact Sec5.CrossRestart.inter_H_subset_of_isFilling hfill ⟨⟨t, ⟨zero_le, ht⟩, rfl⟩, hRt⟩
  rintro ⟨z, hz, hze⟩
  have := (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 t₀.coe_nonneg hz).2
  rw [hze] at this
  exact this hmem

/-- **The wall's first contact after the switch, pathwise** (Lemma 5.7's proof, last step): from the image counterflow's
first contacts with the continuation `β₂` at every positive rational time, the pull-back through `F` (injective on `ℍ`,
the wall `F ∘ β₂` after `t₀`, its prefix outside `F(ℍ)`) and the clock `ℓ`, the physical counterflow first contacts
`R((0, q])` at `R(q)` for every real `q > t₀`. -/
theorem isFirstHitQ_wall_of_chart {R β₂ η η₂ : ℝ≥0 → ℂ} {F : ℂ → ℂ} {t₀ : ℝ≥0} {ℓ : ℝ≥0 → ℝ≥0}
    (hfirst : ∀ r : ℚ, 0 < r → IsFirstHitQ (realPath β₂) (fun s : ℝ => η₂ s.toNNReal) r)
    (hβ₂c : Continuous β₂) (hβ₂ : ∀ s : ℝ≥0, 0 < s → β₂ s ∈ H) (hη₂c : Continuous η₂)
    (hF : InjOn F H) (hjoin : ∀ s : ℝ≥0, 0 < s → R (t₀ + s) = F (β₂ s))
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ t₀ → R t ∉ F '' H)
    (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ) (hℓ0 : ℓ 0 = 0)
    (hrel : ∀ u : ℝ≥0, 0 < u → negInv (η₂ u) ∈ H ∧ negInv (η (ℓ u)) = F (negInv (η₂ u)))
    {q : ℝ} (hq : (t₀ : ℝ) < q) : IsFirstHitQ (realPath R) (fun s : ℝ => η s.toNNReal) q := by
  have hq' : 0 < q - t₀ := sub_pos.2 hq
  have hreal : IsFirstHitQ (realPath β₂) (fun s : ℝ => η₂ s.toNNReal) (q - t₀) := by
    refine isFirstHitQ_of_forall_rat ((hβ₂c.comp continuous_real_toNNReal).continuousOn) (fun s hs => ?_)
      (hη₂c.comp continuous_real_toNNReal) hfirst hq'
    have := hβ₂ s.toNNReal (Real.toNNReal_pos.2 hs)
    intro h0
    change β₂ s.toNNReal = 0 at h0
    rw [h0] at this
    exact lt_irrefl 0 (show (0 : ℂ).im > 0 from this)
  have := isFirstHitQ_of_chart hF hjoin hβ₂ hpre hℓc hℓm hℓ0 hrel hq' hreal
  rwa [add_sub_cancel] at this

/-! ### The assembly -/

/-- **The first exit after the switch of a two-angle wall** (Lemma 5.7 with `ℓ = 2`), for a staged history regular at
every sample: from Lemma 4.7 at every relative angle in `(−π/2, π/2]` (the second angle `θ` itself for an increasing
change, `−θ` by reflection for a decreasing one or for `θ = −π/2`), the §4.2 reference and Lemma 4.7's conditional law
at the switch (`CounterflowGivenPrefixStatement`). -/
theorem ae_isFirstHitQ_switched_of_reg
    (h47 : ∀ θ ∈ Ioc (-(π / 2)) (π / 2), RestartGen.Lemma47QHitTStatement.{u} θ)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hcg : CounterflowGivenPrefixStatement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J) (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₀ θ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0}
    {Es : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEs : IsStagedHistory κ b J P h (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es)
    (hreg : ∀ j ω, IsRegularDriver (Es j ω)) {R : Ω → ℝ≥0 → ℂ} (hR : Sec7.StripWall.IsWallVersion P Es t₀ R)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ)
    (hqt : (t₀ : ℝ) < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  have hχ : 0 < chiC κ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 < Real.pi * chiC κ := mul_pos Real.pi_pos hχ
  have hL0 : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ := fun y hy hyJ => by
    have := hleft θ₀ hθ₀ y hy hyJ; linarith
  have hR0 : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ₀ * chiC κ := hright θ₀ hθ₀
  have hL : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ := fun y hy hyJ => by
    have := hleft θ hθ y hy hyJ; linarith
  have hRθ : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ := fun y hy hyJ => by
    have := hright θ hθ y hy hyJ; linarith
  have hθπ : θ ≤ θ₀ + Real.pi := by linarith [hθ.2, hθ₀.1, Real.pi_pos]
  have hθπ' : θ₀ ≤ θ + Real.pi := by linarith [hθ₀.2, hθ.1, Real.pi_pos]
  have hq0 : (0 : ℚ) < q := by exact_mod_cast t₀.coe_nonneg.trans_lt hqt
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hstage := ae_stage_one hκ hκ4 hb hh hEs hreg hc₀J hc₀ hL0 hR0
  obtain ⟨γ, η₁, hγ, hη₁c, -, -, hη₁⟩ :=
    Sec7.StripWall.exists_wallVersions_twoAngle hκ hκ4 hb hh hEs hreg hL0 hR0 hL hRθ hθπ hθπ'
  have hgood := Sec7.StripWall.ae_goodPath_one hκ hκ4 hb hh hEs hreg hL0 hR0 hL hRθ hθπ hθπ'
  have hζ0 := Sec7.StripWall.ae_trace_stage_zero hκ hκ4 hb hh hEs hL0 hR0
  -- the named input at the first piece
  obtain ⟨W'', ζ'', η'', hK, hpath⟩ := hcg κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ' hleft hright θ₀ hθ₀ (Es 0)
    (hEs.1 0) (hreg 0) (Sec7.StripWall.isFlowLineDriver_stage_zero hκ hb hh hEs) t₀ η hη
  rw [← pastSigma_one_eq (κ := κ) (b := b) (J := J) (θ := θ) (E := Es)] at hK
  have h𝒢 : pastSigma κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 1 ≤ mΩ := hEs.2.1 1
  -- the measurable version of the counterflow trace
  have hYm := Cond44Ref.measurable_cfHistory (Cond44Ref.isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)
  have hpathW : ∀ᵐ ω ∂P, W' 0 ω = 0 ∧ ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < ζ' ω} := by
    obtain ⟨b', J', g, -, -, hd⟩ := hcf
    obtain ⟨g', 𝓕', VL', VR', B', -, hC'⟩ := hd
    filter_upwards [hC'.1.2.2.2.2] with ω hp
    exact ⟨hp.1, hp.2.2.2.1⟩
  have hhl : ∀ᵐ ω ∂P, histLine (cfHistory W' ζ' ω) = fun s : ℝ => η ω s.toNNReal := by
    filter_upwards [hζ', hη, hpathW] with ω hζ hηω hpω
    have hw : Continuous fun t => W' t ω := by
      have := hpω.2
      rw [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    rw [CfRegQ.histLine_eq_traceAt, GlueCond.hDrv_cfHistory hζ hw]
    funext s
    exact LP.traceAt_eq_of_isGeneratingTrace hηω hw.continuousOn hpω.1 ENNReal.coe_lt_top
  have hBm : MeasurableSet {ω | RestartGen.FirstHitCode q (realPath (R ω)) (histLine (cfHistory W' ζ' ω))} :=
    RestartGen.measurableSet_firstHitCode (γ := fun ω => realPath (R ω))
      (β := fun ω => histLine (cfHistory W' ζ' ω)) (fun s => hR.measurable s.toNNReal)
      (fun s => (WangWu.measurable_histLine s).comp hYm) q
  -- the almost sure pathwise facts
  have hG : ∀ᵐ ω ∂P,
      (IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧ ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → negInv (η'' ω u) ∈ H ∧
            negInv (η ω (ℓ u)) = (recChart (recOf (t₀ : ℝ≥0∞) (Es 0 ω))).2.1 (negInv (η'' ω u))) ∧
      (IsGeneratingTrace (Es 1 ω).1 ⊤ (η₁ ω) ∧ (∀ s, 0 < s → η₁ ω s ∈ H) ∧
        ∀ s, 0 < s → R ω (t₀ + s) = (recChart (recOf (t₀ : ℝ≥0∞) (Es 0 ω))).2.1 (η₁ ω s)) ∧
      (Es 0 ω).2 = ⊤ ∧ (Es 1 ω).2 = ⊤ ∧
      IsGeneratingTrace (catPath (Es 0 ω).1 t₀ (Es 1 ω).1) ⊤ (R ω) ∧ (∀ t, 0 < t → R ω t ∈ H) ∧
      IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω) ∧
      histLine (cfHistory W' ζ' ω) = fun s : ℝ => η ω s.toNNReal := by
    filter_upwards [hpath, hη₁, hζ0, hgood, hR.ae_trace, hγ.ae_trace, hη, hhl] with ω hp h1 hz0 hg hRt hγt hηω hhlω
    have hζ1 : (Es 1 ω).2 = ⊤ := (Sec7.StripWall.mem_goodPathSet.1 hg).1
    have hc0 := Sec7.StripWall.continuous_of_isRegularDriver (hreg 0 ω) hz0.1
    have hc1 := Sec7.StripWall.continuous_of_isRegularDriver (hreg 1 ω) hζ1
    have hcat : Continuous (catPath (Es 0 ω).1 t₀ (Es 1 ω).1) :=
      Sec7.StripSideHeightProb.continuous_catPath hc0 hc1 (hreg 1 ω).2.1
    have hcat0 : catPath (Es 0 ω).1 t₀ (Es 1 ω).1 0 = 0 := Sec7.StripSideHeightProb.catPath_zero (hreg 0 ω).2.1
    have hRγ : R ω = γ ω := funext fun t => by
      rw [← LP.traceAt_eq_of_isGeneratingTrace hRt.1 hcat.continuousOn hcat0 ENNReal.coe_lt_top,
        LP.traceAt_eq_of_isGeneratingTrace hγt.1 hcat.continuousOn hcat0 ENNReal.coe_lt_top]
    obtain ⟨hη₁g, -, hη₁H, -, hjoin⟩ := h1
    exact ⟨hp, ⟨hη₁g, hη₁H, fun s hs => by rw [hRγ]; exact (hjoin s hs).2⟩, hz0.1, hζ1, hRt.1, hRt.2.2.1, hηω,
      hhlω⟩
  -- under the conditional law given the first record
  have hGK := Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hG
  have hker : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 1) ω₀),
      ω ∈ {ω | RestartGen.FirstHitCode q (realPath (R ω)) (histLine (cfHistory W' ζ' ω))} := by
    filter_upwards [hstage, hK, hGK] with ω₀ hst hKω₀ hGω₀
    obtain ⟨-, hGff, hfld⟩ := hst
    obtain ⟨hcfQ, hζQ⟩ := hKω₀
    have hβQ : IsFlowLine κ (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).fn
        (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).jumps 0 θ
        (condExpKernel P (pastSigma κ b J (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) Es 1) ω₀)
        (fun ω => recField κ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀)) (h ω)) η₁ (fun ω => (Es 1 ω).2) :=
      Sec7.StripWall.isFlowLine_of_isFlowLineDriver hfld (hGω₀.mono fun ω hω => by
        show IsGeneratingTrace (Es 1 ω).1 (Es 1 ω).2 (η₁ ω)
        rw [hω.2.2.2.1]
        exact hω.2.1.1)
    have hhgt : (RestartGen.Lemma47QHitTStatement.{u} θ ∧
        IsHeightBounded44 κ (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).fn
          (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).jumps θ ∧
        IsHeightBounded44 κ (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).fn
          (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).jumps (π / 2)) ∨
        (RestartGen.Lemma47QHitTStatement.{u} (-θ) ∧
        IsHeightBounded44 κ (reflData (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).fn)
          (reflJumps (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).jumps) (-θ) ∧
        IsHeightBounded44 κ (reflData (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).fn)
          (reflJumps (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).jumps) (π / 2)) := by
      by_cases hm : θ = -(π / 2)
      · -- the extreme angle `−π/2`: by reflection, from Lemma 4.7 at `π/2`
        have hle : θ ≤ θ₀ := by rw [hm]; exact hθ₀.1
        refine Or.inr ⟨h47 (-θ) ⟨by rw [hm, neg_neg]; linarith [Real.pi_pos], by rw [hm, neg_neg]⟩, ?_⟩
        exact isHeightBounded44_reflWord_word₁ hκ hκ4 hc₀J hc₀ hleft hright hθ₀ hθ hle _
      · rcases le_or_gt θ₀ θ with hle | hlt
        · refine Or.inl ⟨h47 θ ⟨lt_of_le_of_ne hθ.1 (Ne.symm hm), hθ.2⟩, ?_⟩
          exact isHeightBounded44_word₁ hκ hκ4 hc₀J hc₀ hleft hright hθ₀ hθ hle _
        · refine Or.inr ⟨h47 (-θ) ⟨by linarith [hθ₀.2], by linarith [hθ.1]⟩, ?_⟩
          exact isHeightBounded44_reflWord_word₁ hκ hκ4 hc₀J hc₀ hleft hright hθ₀ hθ hlt.le _
    have hfirstQ := ae_forall_isFirstHitQ_of_heights href hκ hκ4
      (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (Es 0 ω₀))).isPiecewiseConstantBoundaryData hhgt hGff hcfQ hζQ
      (hGω₀.mono fun ω hω => hω.1.1) hβQ
    filter_upwards [hfirstQ, hGω₀] with ω hf hω
    obtain ⟨⟨hη''g, ℓ, hℓc, hℓm, hℓ0, hrel⟩, ⟨-, hη₁H, hjoin⟩, hz0, hz1, hRt, hRH, hηω, hhlω⟩ := hω
    have hc0 := Sec7.StripWall.continuous_of_isRegularDriver (hreg 0 ω) hz0
    have hc1 := Sec7.StripWall.continuous_of_isRegularDriver (hreg 1 ω) hz1
    have hconf := isConformal_recChart (recOf (t₀ : ℝ≥0∞) (Es 0 ω))
    have hF : InjOn (recChart (recOf (t₀ : ℝ≥0∞) (Es 0 ω))).2.1 H := fun x hx y hy hxy => by
      rw [← hconf.2.2 x hx, ← hconf.2.2 y hy, hxy]
    have hpre : ∀ t : ℝ≥0, 0 < t → t ≤ t₀ → R ω t ∉ (recChart (recOf (t₀ : ℝ≥0∞) (Es 0 ω))).2.1 '' H := by
      rintro t ht htt ⟨z, hz, hze⟩
      refine notMem_fwdMapInv_image_of_le hc0 (hreg 0 ω).2.1 hc1 (hreg 1 ω).2.1 hRt htt (hRH t ht) ⟨z, hz, ?_⟩
      rw [← Sec7.StripWall.recChart_inv_eq (hreg 0 ω) hz0 t₀ hz]
      exact hze
    have hη''c : Continuous (η'' ω) :=
      continuousOn_univ.1 (hη''g.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    have hwall := isFirstHitQ_wall_of_chart hf (hη₁c ω) hη₁H hη''c hF hjoin hpre hℓc hℓm hℓ0 hrel hqt
    have hηc : Continuous (η ω) := continuousOn_univ.1 (hηω.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    show RestartGen.FirstHitCode q (realPath (R ω)) (histLine (cfHistory W' ζ' ω))
    rw [hhlω]
    refine RestartGen.firstHitCode_of_isFirstHitQ (hηc.comp continuous_real_toNNReal) hq0
      ((hR.continuous ω).comp continuous_real_toNNReal).continuousOn (fun s hs h0 => ?_) hwall
    have := hRH s.toNNReal (Real.toNNReal_pos.2 hs.1)
    change R ω s.toNNReal = 0 at h0
    rw [h0] at this
    exact lt_irrefl 0 (show (0 : ℂ).im > 0 from this)
  -- back to `P`
  have hB := Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hBm hker
  filter_upwards [hB, hG] with ω hω hGω
  obtain ⟨-, -, -, -, -, hRH, hηω, hhlω⟩ := hGω
  have hηc : Continuous (η ω) := continuousOn_univ.1 (hηω.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hcode : RestartGen.FirstHitCode q (realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) := by
    have h' : RestartGen.FirstHitCode q (realPath (R ω)) (histLine (cfHistory W' ζ' ω)) := hω
    rwa [hhlω] at h'
  refine RestartGen.isFirstHitQ_of_firstHitCode (hηc.comp continuous_real_toNNReal) ?_ hq0
    ((hR.continuous ω).comp continuous_real_toNNReal).continuousOn (fun s hs h0 => ?_) hcode
  · show η ω (0 : ℝ).toNNReal = 0
    rw [Real.toNNReal_zero]
    exact hηω.1
  · have := hRH s.toNNReal (Real.toNNReal_pos.2 hs.1)
    change R ω s.toNNReal = 0 at h0
    rw [h0] at this
    exact lt_irrefl 0 (show (0 : ℂ).im > 0 from this)

/-- **`SwitchedWallFirstHitRegStatement` from the inputs**: Lemma 4.7 at every relative angle in `(−π/2, π/2]`
(`RestartGen.Lemma47QHitTStatement`; the angle `−π/2` is reached by reflection), the §4.2 reference and Lemma 4.7's
conditional law at the switch. -/
theorem switchedWallFirstHitRegStatement_of_input
    (h47 : ∀ θ ∈ Ioc (-(π / 2)) (π / 2), RestartGen.Lemma47QHitTStatement.{u} θ)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hcg : CounterflowGivenPrefixStatement.{u}) :
    SwitchedWallFirstHitRegStatement.{u} := by
  intro κ b J Ω _ _ P _ h W' ζ' E hS hleft hright θ₀ θ hθ₀ hθ t₀ R hreg hR η hη q hqt
  exact ae_isFirstHitQ_switched_of_reg h47 href hcg hS.kappa_pos hS.kappa_lt_four hS.boundaryData hS.gff
    hS.counterflow hS.lifetime hleft hright hθ₀ hθ
    (hS.staged _ (Sec7.StripSys.isBoundaryContinuedProgram_twoAngleProg hθ₀ hθ t₀)) hreg hR hη q hqt

end InteractingSLE.Sec5.RestartSw
