/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem14

/-!
# The strip system as Lean data: one GFF, the centred counterflow and the angle-varying flow lines

Packet PROVE-STRIPSYS, item 1. Specification §7.4.1, Aux. lemma 130 (`source/spec/p385-432.md` L401–L489,
pp. 408–413): "Work in the already established non-boundary-intersecting centered strip coupling. […] Write `x` for the
common flow seed and `y` for the counterflow seed. Parametrize each incoming path by its own half-plane capacity with
target `y`. Fix the first path's change time to be `1`. […] the two angle-varying paths
`α = η^{1,∞}_{−π/2,θ₁}`, `β^{(r)} = η^{r,∞}_{π/2,θ₂}` (RS13.1)", and its proof: "First construct only `α` and the
unchanged extremal path `β = η_{π/2}`."

**The vocabulary.** The frozen Theorem 1.4 surface (R29) already describes exactly this configuration on `ℍ`: a GFF `h`
with a piecewise-constant boundary word `b`; the centred counterflow `η′` from `∞` to `0` (frozen
`IsCenteredCounterflowDriver`, the Theorem 1.1 curve of parameter `16/κ` of `F_d(h)` in the chart `R(z) = −1/z`); and
every prescribed staged history of `h` (frozen `IsStagedHistory`: each ordinary piece is, conditionally on the
retained history, the flow line of the conditional field in the current domain, read in the current chart). The
common flow seed is `x = 0` and the counterflow seed is `y = ∞`; own times are the half-plane capacities of the pieces
in their own charts, which add up along a history. The strip of Aux. lemma 130 is one choice of the word `b` (its four
heights `a, b, a′, b′`, transported to `ℍ`).

This file states the strip system in that vocabulary (`IsStripSystem`; its fields are exactly the hypotheses of the
Theorem 1.4 named inputs of `Spec/Theorem14Inputs.lean`), writes the incoming paths of (RS13.1) as programs
(`alphaSpec`, `betaSpec`, `leftExtremalSpec`), and proves:

* `isBoundaryContinuedProgram_twoAngleProg`, `…_alphaSpec`, `…_betaSpec`, `…_leftExtremalSpec`: the three programs
  have their ordinary angles in `[−π/2, π/2]`, so every staged-history statement of the strip system applies to them;
* `IsStripSystem.isStagedHistory_alpha`, `…_beta`, `…_leftExtremal`: their drivers are staged histories of `h`;
* **`exists_isStripSystem_of_construction`**: on any standard Borel space carrying the field and the counterflow, the
  staged histories exist and form a strip system, from Theorem 1.4's named construction input
  (`Theorem14.StagedHistoryConstructionStatement`, GW1/GW2a/BW1–BW2, i.e. Theorems 1.1–1.2 in conditional form);
* **`IsStripSystem.ae_physSet_alpha_subset`**, `…_beta_subset`, `…_leftExtremal_subset`: Lemma 5.7's containment
  ("Their full schedules lie in `[−π/2, π/2]`, so Lemma 5.7 places them in the same continuous counterflow range"),
  from Theorem 1.4's named input `Theorem14.GW2aContainmentStatement` (GW2a, p. 623).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripSys

/-! ### The incoming paths of (RS13.1) as programs -/

/-- The two-piece schedule `η^{t,∞}_{θ₀,θ}` as a program: the ordinary angle-`θ₀` piece for own time `t`, then the
angle-`θ` piece through its available lifetime (`.inl (θ, ⊤)`). -/
def twoAngleProg (θ₀ : ℝ) (t : ℝ≥0) (θ : ℝ) : List Instr :=
  [Sum.inl (θ₀, (t : ℝ≥0∞)), Sum.inl (θ, ⊤)]

/-- The staged history `η^{t,∞}_{θ₀,θ}` from the common flow seed `x = 0`, not under the GW2 schedule convention. -/
def twoAngleSpec (θ₀ : ℝ) (t : ℝ≥0) (θ : ℝ) : ExplSpec :=
  (0, false, twoAngleProg θ₀ t θ)

/-- The first incoming path `α = η^{1,∞}_{−π/2,θ₁}` of (RS13.1): angle `−π/2` until own time `1`, then `θ₁`. -/
def alphaSpec (θ₁ : ℝ) : ExplSpec :=
  twoAngleSpec (-(Real.pi / 2)) 1 θ₁

/-- The second incoming path `β^{(r)} = η^{r,∞}_{π/2,θ₂}` of (RS13.1): angle `π/2` until own time `r`, then `θ₂`. -/
def betaSpec (r : ℝ≥0) (θ₂ : ℝ) : ExplSpec :=
  twoAngleSpec (Real.pi / 2) r θ₂

/-- The unchanged extremal path `β = η_{π/2}`: the angle-`π/2` flow line through its available lifetime. -/
def leftExtremalSpec : ExplSpec :=
  (0, false, [Sum.inl (Real.pi / 2, ⊤)])

theorem isBoundaryContinuedProgram_twoAngleProg {θ₀ θ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (t : ℝ≥0) :
    IsBoundaryContinuedProgram (twoAngleProg θ₀ t θ) := by
  intro θ' t' hmem
  simp only [twoAngleProg, List.mem_cons, List.not_mem_nil, or_false, Sum.inl.injEq, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hθ₀
  · exact hθ

theorem neg_pi_div_two_mem_Icc : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨le_rfl, by linarith [Real.pi_pos]⟩

theorem pi_div_two_mem_Icc : Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨by linarith [Real.pi_pos], le_rfl⟩

theorem isBoundaryContinuedProgram_alphaSpec {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    IsBoundaryContinuedProgram (alphaSpec θ₁).2.2 :=
  isBoundaryContinuedProgram_twoAngleProg neg_pi_div_two_mem_Icc hθ₁ 1

theorem isBoundaryContinuedProgram_betaSpec {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (r : ℝ≥0) : IsBoundaryContinuedProgram (betaSpec r θ₂).2.2 :=
  isBoundaryContinuedProgram_twoAngleProg pi_div_two_mem_Icc hθ₂ r

theorem isBoundaryContinuedProgram_leftExtremalSpec : IsBoundaryContinuedProgram leftExtremalSpec.2.2 := by
  intro θ' t' hmem
  simp only [leftExtremalSpec, List.mem_cons, List.not_mem_nil, or_false, Sum.inl.injEq, Prod.mk.injEq] at hmem
  rw [hmem.1]
  exact pi_div_two_mem_Icc

/-! ### The strip system -/

/-- **The strip system** (Aux. lemma 130's "already established non-boundary-intersecting centered strip coupling"),
for the flow-line parameter `κ ∈ (0, 4)` (counterflow parameter `16/κ > 4`): on one standard Borel probability space,
a GFF `h` on `ℍ` with the piecewise-constant boundary word `b`, the centred counterflow `η′` of `h` from `∞` to `0`
driven (in the chart `R`) by `W′` with almost surely infinite lifetime, and, for every prescribed staged history
whose ordinary angles lie in `[−π/2, π/2]`, its drivers `E spec` realizing it as conditional flow lines of `h`. The
fields are exactly the hypotheses of the Theorem 1.4 named inputs (`Spec/Theorem14Inputs.lean`). -/
structure IsStripSystem (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop where
  kappa_pos : 0 < κ
  kappa_lt_four : κ < 4
  boundaryData : IsPiecewiseConstantBoundaryData b jumps
  gff : IsGFFWithBoundaryData P h b jumps
  counterflow : IsCenteredCounterflowDriver κ P h W' ζ'
  lifetime : ∀ᵐ ω ∂P, ζ' ω = ⊤
  staged : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec)

section System

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The drivers of `α = η^{1,∞}_{−π/2,θ₁}` form a staged history of `h`. -/
theorem IsStripSystem.isStagedHistory_alpha (hS : IsStripSystem κ b jumps P h W' ζ' E) {θ₁ : ℝ}
    (hθ₁ : θ₁ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    IsStagedHistory κ b jumps P h (alphaSpec θ₁) (E (alphaSpec θ₁)) :=
  hS.staged _ (isBoundaryContinuedProgram_alphaSpec hθ₁)

/-- The drivers of `β^{(r)} = η^{r,∞}_{π/2,θ₂}` form a staged history of `h`. -/
theorem IsStripSystem.isStagedHistory_beta (hS : IsStripSystem κ b jumps P h W' ζ' E) {θ₂ : ℝ}
    (hθ₂ : θ₂ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (r : ℝ≥0) :
    IsStagedHistory κ b jumps P h (betaSpec r θ₂) (E (betaSpec r θ₂)) :=
  hS.staged _ (isBoundaryContinuedProgram_betaSpec hθ₂ r)

/-- The drivers of the unchanged extremal path `β = η_{π/2}` form a staged history of `h`. -/
theorem IsStripSystem.isStagedHistory_leftExtremal (hS : IsStripSystem κ b jumps P h W' ζ' E) :
    IsStagedHistory κ b jumps P h leftExtremalSpec (E leftExtremalSpec) :=
  hS.staged _ isBoundaryContinuedProgram_leftExtremalSpec

/-- **Lemma 5.7's containment for every boundary-continued history of the strip system** (GW2a, p. 623: "Every
finite such history is simple, is contained in the counterflow range"), from Theorem 1.4's named input. -/
theorem IsStripSystem.ae_physSet_subset (hS : IsStripSystem κ b jumps P h W' ζ' E)
    (hGW2a : Theorem14.GW2aContainmentStatement.{u}) {p : List Instr} (hp : IsBoundaryContinuedProgram p) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω) ⊆
      counterflowCompletedRange (fun t => W' t ω) :=
  hGW2a κ hS.kappa_pos hS.kappa_lt_four b jumps hS.boundaryData P h hS.gff W' ζ' hS.counterflow hS.lifetime E
    hS.staged p hp

/-- **(RS13.1) in the counterflow range**: `α` lies in the completed counterflow range ("Their full schedules lie in
`[−π/2, π/2]`, so Lemma 5.7 places them in the same continuous counterflow range"). -/
theorem IsStripSystem.ae_physSet_alpha_subset (hS : IsStripSystem κ b jumps P h W' ζ' E)
    (hGW2a : Theorem14.GW2aContainmentStatement.{u}) {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps (alphaSpec θ₁) (fun k => E (alphaSpec θ₁) k ω) ⊆
      counterflowCompletedRange (fun t => W' t ω) :=
  hS.ae_physSet_subset hGW2a (isBoundaryContinuedProgram_alphaSpec hθ₁)

/-- `β^{(r)}` lies in the completed counterflow range. -/
theorem IsStripSystem.ae_physSet_beta_subset (hS : IsStripSystem κ b jumps P h W' ζ' E)
    (hGW2a : Theorem14.GW2aContainmentStatement.{u}) {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (r : ℝ≥0) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps (betaSpec r θ₂) (fun k => E (betaSpec r θ₂) k ω) ⊆
      counterflowCompletedRange (fun t => W' t ω) :=
  hS.ae_physSet_subset hGW2a (isBoundaryContinuedProgram_betaSpec hθ₂ r)

/-- The unchanged extremal path `β = η_{π/2}` lies in the completed counterflow range. -/
theorem IsStripSystem.ae_physSet_leftExtremal_subset (hS : IsStripSystem κ b jumps P h W' ζ' E)
    (hGW2a : Theorem14.GW2aContainmentStatement.{u}) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps leftExtremalSpec (fun k => E leftExtremalSpec k ω) ⊆
      counterflowCompletedRange (fun t => W' t ω) :=
  hS.ae_physSet_subset hGW2a isBoundaryContinuedProgram_leftExtremalSpec

/-- All three incoming paths lie in the counterflow range simultaneously, for every rational change time of the
second path (one null set for the countably many `β^{(r)}`). -/
theorem IsStripSystem.ae_physSet_subset_all (hS : IsStripSystem κ b jumps P h W' ζ' E)
    (hGW2a : Theorem14.GW2aContainmentStatement.{u}) {θ₁ θ₂ : ℝ}
    (hθ₁ : θ₁ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hθ₂ : θ₂ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps (alphaSpec θ₁) (fun k => E (alphaSpec θ₁) k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) ∧
      ExplState.physSet κ b jumps leftExtremalSpec (fun k => E leftExtremalSpec k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) ∧
      ∀ q : ℚ, ExplState.physSet κ b jumps (betaSpec (q : ℝ).toNNReal θ₂)
          (fun k => E (betaSpec (q : ℝ).toNNReal θ₂) k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) := by
  filter_upwards [hS.ae_physSet_alpha_subset hGW2a hθ₁, hS.ae_physSet_leftExtremal_subset hGW2a,
    ae_all_iff.2 fun q : ℚ => hS.ae_physSet_beta_subset hGW2a hθ₂ (q : ℝ).toNNReal] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

end System

/-! ### Existence of the strip system -/

/-- **The staged histories complete a strip system** on any standard Borel space carrying the field and the
centred counterflow, from Theorem 1.4's named construction input (one prescribed history at a time,
`Theorem14.exists_isStagedHistory_of_inputs`). -/
theorem exists_isStripSystem_of_construction (hCon : Theorem14.StagedHistoryConstructionStatement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, IsStripSystem κ b jumps P h W' ζ' E := by
  obtain ⟨E, hE⟩ := Theorem14.exists_isStagedHistory_of_inputs hCon hκ hκ4 b jumps hb hh
  exact ⟨E, ⟨hκ, hκ4, hb, hh, hcf, hζ', hE⟩⟩

end StripSys

end Sec7

end InteractingSLE
