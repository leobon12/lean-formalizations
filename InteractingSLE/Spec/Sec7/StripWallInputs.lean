/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripWallInputsReflDet
import InteractingSLE.Spec.Sec7.Aux119Heights

/-!
# Aux. lemma 119's conditional mean in the change pocket, from the strip walls' own data

Packet PROVE-STRIPSYS27, last item. Specification §7.4, Aux. lemma 119 and its proof (`source/spec/p385-432.md`
L3–L54, pp. 385–387): in the change pocket `C` of the two angle-varying walls `L = β^{(r)}` and `R = α` of (RS13.1),
the conditional mean of the field given the complete wall union is the bounded Poisson extension of (PW13.1) —
`λ − θ_L(s)χ` on the left arc and `−λ − θ_R(s)χ` on the right arc, at the actual positions of the change points —
pulled back by the flow chart and corrected by `−χ(arg c′ + 2πn)`.

PROVE-STRIPSYS25 proved this (`Aux119Heights.ae_eqOn_changePocket_of_sideHeights`) from Lemma 6.2's inputs of the two
walls and their single-path side heights at rational stops. Here the side heights are proved from the walls' own data
(`StripWall.ae_sideHeights_wall`: the first piece is a frozen flow line of `h`, the second piece is
`RS133.ae_sideHeights_stage`), and Lemma 6.2's determination input is `IsDetTwoPiece.hdet`. The remaining inputs of each
wall are stated as hypotheses on the wall itself:

* `IsWallVersion P E t₀ γ`: `γ` is a version of the wall's trace — continuous at every sample, `γ 0 = 0`, measurable at
  fixed times, and almost surely a simple (injective, in `ℍ` at positive times) transient generating trace of the
  concatenated driver on `[0, ∞)` (spec p. 410: "the continuously extended inverse own map therefore gives a continuous
  simple complete concatenation"; packet PROVE-STAGEDLOC item (3));
* `Sec6.IsEntranceHistoryLocal γ (centredField h u₀) P`: Lemma 6.2's locality input (PROVE-STAGEDLOC, running);
* `IsDetTwoPiece P h E`: both pieces live forever and are Borel functions of the field — proved for both strip walls
  (the increasing change of `α`: `isDetTwoPiece_of_heights`, PROVE-STRIPSYS21; the decreasing change of `β^{(r)}`:
  `isDetTwoPiece_of_heights_refl`, the source's "reflected condition", `Spec/Sec7/StripWallInputsReflDet`).

## Main results

* **`ae_eqOn_changePocket_twoAngle`**: the conditional mean in the change pocket for any two two-angle walls with the
  (4.4) heights at their initial angles;
* **`ae_eqOn_changePocket_strip`**: the strip system's walls `α = η^{1,∞}_{−π/2,θ₁}`, `β^{(r)} = η^{r,∞}_{π/2,θ₂}`, with
  Aux. lemma 130's height choice (every original-boundary cumulative value nonnegative at every angle in
  `[−π/2, π/2]`); both walls' determination from the §4.2 reference (R48-safe), so the remaining hypotheses are the
  walls' versions, their locality, the drivers' regularity and the local-set means.

No Theorem 1.2/1.3 (R43, R48). Conditional helpers; they replace no source theorem.
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

open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)
open Lemma71N (IsPocketBranch)
open PocketCoord PocketMarks Aux119Bdry LocalSets StripGeom Aux119Nested Aux2728Pocket

/-- **A version of a two-angle wall's trace**: continuous at every sample, starting at `0`, measurable at fixed times,
and almost surely a simple transient generating trace of the concatenated driver `catPath (E 0).1 t₀ (E 1).1` on
`[0, ∞)`. -/
structure IsWallVersion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (t₀ : ℝ≥0) (γ : Ω → ℝ≥0 → ℂ) : Prop where
  continuous : ∀ ω, Continuous (γ ω)
  zero : ∀ ω, γ ω 0 = 0
  measurable : ∀ t, Measurable fun ω => γ ω t
  ae_trace : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω) ∧ Injective (γ ω) ∧
    (∀ t, 0 < t → γ ω t ∈ H) ∧ Tendsto (γ ω) atTop (cobounded ℂ)

namespace IsWallVersion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {t₀ : ℝ≥0}
  {γ : Ω → ℝ≥0 → ℂ}

theorem ae_simple (hv : IsWallVersion P E t₀ γ) :
    ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω) ∧ Injective (γ ω) ∧
      ∀ t, 0 < t → γ ω t ∈ H :=
  hv.ae_trace.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

theorem ae_isGeneratingTrace (hv : IsWallVersion P E t₀ γ) :
    ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω) :=
  hv.ae_trace.mono fun _ h => h.1

theorem ae_im_nonneg (hv : IsWallVersion P E t₀ γ) : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (γ ω t).im := by
  filter_upwards [hv.ae_trace] with ω hω t
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · rw [← ht, hv.zero ω, Complex.zero_im]
  · exact (hω.2.2.1 t ht).le

end IsWallVersion

open scoped Classical in
/-- **A version of the wall from its pathwise trace**: if both pieces almost surely live forever and the concatenated
driver almost surely has a simple transient generating trace on `[0, ∞)`, then the trace read by
`LP.traceAt` on a measurable full-measure set (and `0` elsewhere) is a version of the wall (`IsWallVersion`). -/
theorem exists_isWallVersion {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hEm : ∀ k, Measurable (E k)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (t₀ : ℝ≥0)
    (hlife : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ η ∧ Injective η ∧
      (∀ t, 0 < t → η t ∈ H) ∧ Tendsto η atTop (cobounded ℂ)) :
    ∃ γ : Ω → ℝ≥0 → ℂ, IsWallVersion P E t₀ γ ∧
      ∀ᵐ ω ∂P, ∀ t, γ ω t = LP.traceAt t (catPath (E 0 ω).1 t₀ (E 1 ω).1) := by
  set S : Set Ω := {ω | ((E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤) ∧ ∃ η : ℝ≥0 → ℂ,
    IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
      Tendsto η atTop (cobounded ℂ)} with hS
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := by
    filter_upwards [hlife, htr] with ω h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨N, hSN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hSae)
  have hG : ∀ ω, ω ∉ N → ω ∈ S := fun ω hω => by
    by_contra h
    exact hω (hSN h)
  -- on the good set the read trace is the generating trace
  have hread : ∀ ω, ω ∉ N → ∃ η : ℝ≥0 → ℂ, (∀ t, LP.traceAt t (catPath (E 0 ω).1 t₀ (E 1 ω).1) = η t) ∧
      IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
      Tendsto η atTop (cobounded ℂ) := by
    intro ω hω
    obtain ⟨⟨h0, h1⟩, η, hη, hinj, hH, htrn⟩ := hG ω hω
    obtain ⟨hcc, hc0⟩ := continuous_catPath_of_isRegularDriver (hreg 0 ω) (hreg 1 ω) h0 h1 t₀
    exact ⟨η, fun t => LP.traceAt_eq_of_isGeneratingTrace hη hcc.continuousOn hc0 ENNReal.coe_lt_top, hη, hinj,
      hH, htrn⟩
  refine ⟨fun ω t => if ω ∈ N then 0 else LP.traceAt t (catPath (E 0 ω).1 t₀ (E 1 ω).1), ⟨fun ω => ?_, fun ω => ?_,
    fun t => ?_, ?_⟩, ?_⟩
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      exact continuous_const
    · obtain ⟨η, he, hη, -⟩ := hread ω hω
      simp only [hω, ↓reduceIte, he]
      exact continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · obtain ⟨η, he, hη, -⟩ := hread ω hω
      simp only [hω, ↓reduceIte, he]
      exact hη.1
  · refine Measurable.ite hNm measurable_const ?_
    exact (LP.measurable_traceAt t).comp ((StripDet.measurable_catPath t₀).comp
      ((measurable_fst.comp (hEm 0)).prodMk (measurable_fst.comp (hEm 1))))
  · have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hNc] with ω hω
    obtain ⟨η, he, hη, hinj, hH, htrn⟩ := hread ω hω
    simp only [hω, ↓reduceIte, he]
    exact ⟨hη, hinj, hH, htrn⟩
  · have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hNc] with ω hω t
    simp only [hω, ↓reduceIte]

/-! ### The change pocket of two two-angle walls -/

section Pocket

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Aux. lemma 119's conditional mean in the change pocket of two two-angle walls** (see the module docstring). The
left wall `Lw` is a version of the staged history `EL` of `η^{tL,∞}_{θL₀,θL}`, the right wall `Rw` one of `ER` of
`η^{tR,∞}_{θR₀,θR}`; `b` has the (4.4) heights at both initial angles; both walls are field determined
(`IsDetTwoPiece`), simple transient versions (`IsWallVersion`) and history-sensitively local. Then almost surely, for
every harmonic representative `v` of the mean `gU` of the complete wall union and every flow chart `c` of a change
pocket on the left of `Rw` with the common lift's integer `n`, on the pocket `v + u₀` is the bounded Poisson extension
`G` of the two-angle heights `λ − θ_L(s)χ`, `−λ − θ_R(s)χ` pulled back by `c`, minus `χ (arg c′ + 2πn)`. -/
theorem ae_eqOn_changePocket_twoAngle (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {θL₀ θL : ℝ} {tL : ℝ≥0} {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hEL : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θL₀ tL θL) EL)
    (hregL : ∀ j ω, IsRegularDriver (EL j ω))
    (hLL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θL₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hLR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θL₀ * chiC κ)
    (hDL : IsDetTwoPiece P h EL) {Lw : Ω → ℝ≥0 → ℂ} (hvL : IsWallVersion P EL tL Lw)
    (hlocL : Sec6.IsEntranceHistoryLocal Lw (WholeField.centredField h u₀) P)
    {θR₀ θR : ℝ} {tR : ℝ≥0} {ER : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hER : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θR₀ tR θR) ER)
    (hregR : ∀ j ω, IsRegularDriver (ER j ω))
    (hRL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θR₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hRR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θR₀ * chiC κ)
    (hDR : IsDetTwoPiece P h ER) {Rw : Ω → ℝ≥0 → ℂ} (hvR : IsWallVersion P ER tR Rw)
    (hlocR : Sec6.IsEntranceHistoryLocal Rw (WholeField.centredField h u₀) P)
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion Lw Rw) (WholeField.centredField h u₀) P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Lw ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gL q))
    (hgR : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Rw ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gR q)) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion Lw Rw ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion Lw Rw ω → gU ω φ = ∫ z, v z * φ z) →
      ∀ (r : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      IsFlowChart (Rw ω) (Lw ω) r Ψ c → changePocket (Rw ω) (Lw ω) r ⊆ leftSideOf (range (Rw ω)) →
      IsDerivLog c.1 ℓ (changePocket (Rw ω) (Lw ω) r) →
      (∀ z ∈ changePocket (Rw ω) (Lw ω) r, c.2.2 z = (ℓ z).im) → IsPocketBranch (Lw ω) (Rw ω) c n →
      IsBoundedHarmonicExtension
        (chartData (Lw ω) (Rw ω) (fun s => sleLambda κ - (if s < tL then θL₀ else θL) * chiC κ)
          (fun s => -sleLambda κ - (if s < tR then θR₀ else θR) * chiC κ) c)
        (exSet (Lw ω) (Rw ω) {tL} {tR} c) G →
      ∀ z ∈ changePocket (Rw ω) (Lw ω) r, v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hLdet := hDL.hdet hregL u₀ hvL.ae_isGeneratingTrace
  have hRdet := hDR.hdet hregR u₀ hvR.ae_isGeneratingTrace
  have htr : ∀ᵐ ω ∂P, Tendsto (Lw ω) atTop (cobounded ℂ) ∧ Tendsto (Rw ω) atTop (cobounded ℂ) := by
    filter_upwards [hvL.ae_trace, hvR.ae_trace] with ω hL hR
    exact ⟨hL.2.2.2, hR.2.2.2⟩
  have hsideL := ae_sideHeights_wall hκ hκ4 hb hh hEL hregL hLL0 hLR0 hDL.ae_lifetimes hu₀ hvL.continuous
    hvL.zero hvL.measurable hLdet hlocL hvL.ae_simple hgL hvR.zero
  have hsideR := ae_sideHeights_wall hκ hκ4 hb hh hER hregR hRL0 hRR0 hDR.ae_lifetimes hu₀ hvR.continuous
    hvR.zero hvR.measurable hRdet hlocR hvR.ae_simple hgR hvL.zero
  have key := Aux119Heights.ae_eqOn_changePocket_of_sideHeights hX hvL.continuous hvL.zero hvL.measurable hLdet
    hlocL hvL.ae_im_nonneg hvR.continuous hvR.zero hvR.measurable hRdet hlocR hvR.ae_im_nonneg htr hgU hgL hgR
    hu₀.1 hu₀.2.1 (Set.finite_singleton tL) (Set.finite_singleton tR)
    (θL := fun s => if s < tL then θL₀ else θL) (θR := fun s => if s < tR then θR₀ else θR) hsideL hsideR
  filter_upwards [key, hvL.ae_trace, hvR.ae_trace, hDL.ae_lifetimes, hDR.ae_lifetimes]
    with ω hk hL hR hlL hlR v hv hrep r Ψ c ℓ n G hF hCl hℓ hlift hn hG
  obtain ⟨hcL, hcL0⟩ := continuous_catPath_of_isRegularDriver (hregL 0 ω) (hregL 1 ω) hlL.1 hlL.2 tL
  obtain ⟨hcR, hcR0⟩ := continuous_catPath_of_isRegularDriver (hregR 0 ω) (hregR 1 ω) hlR.1 hlR.2 tR
  exact hk v hv hrep r Ψ c ℓ n G hF hCl hℓ hlift hn hL.1 hcL hcL0 hR.1 hcR hcR0 hG

/-! ### The strip system's walls -/

/-- **Aux. lemma 119's conditional mean in the change pocket of the strip walls** `L = β^{(r)} = η^{r,∞}_{π/2,θ₂}` and
`R = α = η^{1,∞}_{−π/2,θ₁}` of (RS13.1) (spec pp. 385–387, 408–410). The strip system `hS` is Aux. lemma 130's
"already established non-boundary-intersecting centered strip coupling"; `hcumL`, `hcumR` are its height choice
("every original-boundary cumulative force value is nonnegative for every angle in `[−π/2, π/2]`": the left value
`−(b + aχ)/λ − 1 ≥ 0`, the right value `(b + aχ)/λ − 1 ≥ 0`). Both walls are field determined, R48-safely, from `h44`
(the §4.2 reference's word-measurable Theorem 1.2 on (4.4) words): `α`'s increasing change by PROVE-STRIPSYS21,
`β^{(r)}`'s decreasing change by the reflected condition (`isDetTwoPiece_of_heights_refl`). The remaining hypotheses are
the regularity of the two staged histories' drivers, versions of the two walls' traces (`IsWallVersion`), their
entrance-history locality (PROVE-STAGEDLOC), and the local-set means. -/
theorem ae_eqOn_changePocket_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hlocβ : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
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
      ∀ z ∈ changePocket (α ω) (β ω) r', v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hEα : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec (-(π / 2)) 1 θ₁) (E (StripSys.alphaSpec θ₁)) :=
    hS.isStagedHistory_alpha hθ₁
  have hEβ : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec (π / 2) r θ₂) (E (StripSys.betaSpec r θ₂)) :=
    hS.isStagedHistory_beta hθ₂ r
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hp := StripSys.pi_div_two_mem_Icc
  have hDα : IsDetTwoPiece P h (E (StripSys.alphaSpec θ₁)) :=
    isDetTwoPiece_of_heights h44 hκ hκ4 hb hh hEα hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁) (hcumR _ hθ₁)
      hθ₁.1 (by linarith [hθ₁.2])
  have hDβ : IsDetTwoPiece P h (E (StripSys.betaSpec r θ₂)) :=
    isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh hEβ hregβ (hL44 _ hp) (hcumR _ hp) (hcumL _ hθ₂)
      (fun y hy hyJ => by have := hcumR _ hθ₂ y hy hyJ; linarith) hθ₂.2 (by linarith [hθ₂.1])
  exact ae_eqOn_changePocket_twoAngle hκ hκ4 hb hh hu₀ hEβ hregβ (hL44 _ hp) (hcumR _ hp) hDβ hvβ hlocβ
    hEα hregα (hL44 _ hm) (hcumR _ hm) hDα hvα hlocα hgU hgL hgR

end Pocket

end StripWall

end Sec7

end InteractingSLE
