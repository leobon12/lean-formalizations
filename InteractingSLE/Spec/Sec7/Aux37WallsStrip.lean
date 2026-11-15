/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofHwit
import InteractingSLE.Spec.Sec7.StripWallMeanFull
import InteractingSLE.Spec.Sec7.StripPocketPathFinal
import InteractingSLE.Spec.Sec7.StripPocketVersions
import InteractingSLE.Impl.PiecewiseConstant

/-!
# Aux. lemma 37's witness exclusions for the strip pockets: the walls' means and Lemma 6.2 inputs discharged

Packet PROVE-AUX37-WALLS. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L136,
pp. 198–200), used by Aux. lemma 130's pocket (`source/spec/p385-432.md` L401–L515, pp. 408–414).

PROVE-FLATCLOCK's `FlatClockProof.hwit_of_wallMeans` / `hwitI_of_wallMeans` (Aux. lemma 37's exclusion of every
rational witness, with the flat clock and the exploration means proved) still took the walls' local-set means `gU`,
`gL`, `gR`, the walls' versions (`IsWallVersion`), their entrance-history locality, the left extremal path's simple
properness and the common prefix `β^{(q)}(q) = β(q)`. Here all of them are derived from the realization data that the
consumer `StripPocketPath.pocketWordEvolution_of_stripSystem` already has (versions of the three walls: continuous,
`0` at `0`, measurable at fixed times, almost surely generating traces of the staged drivers):

* `rt_eq_coe_toNNRat`: `rt q = ↑q.toNNRat` (the two indexings of rational stage times);
* **`lemma62_walls_rat`**: Lemma 6.2's inputs (field determination, entrance-history locality, transience) of `α`
  and of every `Lr q`, `q > 0` (`StripWall.lemma62_walls` at `q.toNNRat`);
* **`exists_wallMeans_strip`**: the means `gU` (of `wallUnion (Lr q) α`), `gL` (of the prefixes of `Lr q`) and `gR`
  (of the prefixes of `α`) exist (`StripWall.exists_isLocalSetMean_wallUnion_strip`,
  `StripWall.exists_isLocalSetMean_prefix`);
* **`hwit_strip`**, **`hwitI_strip`**: Aux. lemma 37's witness exclusions for the strip pockets, exactly the
  `hwit`/`hwitI` of `pocketWordEvolution_of_stripSystem`, from the consumer's own hypotheses (the walls' versions,
  the counterflow's version, Lemma 5.7's reverse visits `hwalls`/`hwallsL` and the non-boundary avoidance `hav`);
* **`hattach_strip`**, **`hattachI_strip`**: the attachment constancies (`hattach`/`hattachI` of
  `StripPocketConfig.pocketWordEvolution_of_stripPocket` and of the current wiring) that follow;
* **`pocketWordEvolution_of_stripSystem_aux37`**: `pocketWordEvolution_of_stripSystem` without `hwit`, `hwitI`, for the
  source's angles `θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]` (Aux. lemma 130 fixes `θ₁, θ₂ ∈ (−π/2, π/2)`, p. 408);
  **`pocketWordEvolution_of_stripSystem_reg_aux37`**: the same for
  `StripPocketVersions.pocketWordEvolution_of_stripSystem_reg` (R51's `StagedPiecesRegular` in place of per-sample
  driver regularity; the exclusions are proved for the regularized family `StripWall.regStrip`, whose walls have the
  same versions).

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48); `h44` is the walls'
determination input, as in the consumers.
-/

set_option autoImplicit false

noncomputable section

universe u

open MeasureTheory Set Metric Filter Topology Function
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open QuantumZipper (H Hbar chiC fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Aux37Walls

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly Aux37Frame LocalSets PocketWordAssembly PocketSeedOpen
  PocketLeftFrontier PocketCoupling
open Exist.Staged (IsRegularDriver)

/-- The two indexings of rational stage times agree: `rt q = ↑q.toNNRat` for `q ≥ 0`. -/
theorem rt_eq_coe_toNNRat {q : ℚ} (hq : 0 ≤ q) : StripSys.rt q = ((q.toNNRat : ℚ≥0) : ℝ≥0) := by
  ext
  rw [StripSys.coe_rt hq]
  have h3 : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) := by norm_cast
  rw [h3, Rat.coe_toNNRat q hq]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Lemma 6.2's inputs for the walls `α` and `Lr q`** at a rational stage time `q > 0` indexed by `rt q`
(`StripWall.lemma62_walls` at `q.toNNRat`). -/
theorem lemma62_walls_rat (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ} (hq : 0 < q)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {L α : Ω → ℝ≥0 → ℂ} (hLc : ∀ ω, Continuous (L ω)) (hL0 : ∀ ω, L ω 0 = 0)
    (hLm : ∀ t, Measurable fun ω => L ω t)
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1 (StripSys.rt q)
      (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (L ω))
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal L (WholeField.centredField h u₀) P ∧
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P ∧
    ∀ᵐ ω ∂P, Tendsto (L ω) atTop (Bornology.cobounded ℂ) ∧ Tendsto (α ω) atTop (Bornology.cobounded ℂ) := by
  have e := rt_eq_coe_toNNRat hq.le
  rw [e] at hregβ hLtr
  exact lemma62_walls h44 hS hcumL hcumR hθ₁ hθ₂ (q := q.toNNRat) (Rat.toNNRat_pos.2 hq) hregα hregβ hu₀ hLc hL0
    hLm hLtr hαc hα0 hαm hαtr

/-- **The walls' local-set means exist** for the strip system: the mean `gU q` of the walls' union
`wallUnion (Lr q) α`, the means `gL q t` of the prefixes `Lr q '' [0, t] ∩ ℍ` and `gR t` of `α '' [0, t] ∩ ℍ`
(Lemma 6.2's local sets, then Lemma 3.6's means). -/
theorem exists_wallMeans_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω)) :
    (∃ gU : ℚ → Ω → DistOn upperHalfPlaneOpens, ∀ q : ℚ, 0 < q →
      IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q)) ∧
    (∃ gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t)) ∧
    ∃ gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have hW : ∀ q : ℚ, 0 < q → _ := fun q hq =>
    lemma62_walls_rat h44 hS hcumL hcumR hθ₁ hθ₂ hq hregα (hregβ q hq) hu₀ (hLc q) (hL0 q) (hLm q) (hLtr q hq) hαc
      hα0 hαm hαtr
  have hU : ∀ q : ℚ, ∃ g : Ω → DistOn upperHalfPlaneOpens, 0 < q →
      IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P g := fun q => by
    by_cases hq : 0 < q
    · obtain ⟨hdL, hlL, hdα, hlα, htr⟩ := hW q hq
      obtain ⟨hUm, hUloc, -⟩ := isLocalSet_wallUnion hX (hLc q) (hL0 q) (hLm q) hdL hlL hαc hα0 hαm hdα hlα htr
      obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hX hUm hUloc
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  have hL : ∀ q : ℚ, ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (g t) := fun q => by
    by_cases hq : 0 < q
    · obtain ⟨hdL, hlL, -⟩ := hW q hq
      obtain ⟨g, hg⟩ := exists_isLocalSetMean_prefix hX (hLc q) (hL0 q) (hLm q) hdL hlL
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  choose gU hgU using hU
  choose gL hgL using hL
  obtain ⟨-, -, hdα, hlα, -⟩ := hW 1 one_pos
  exact ⟨⟨gU, hgU⟩, ⟨gL, hgL⟩, exists_isLocalSetMean_prefix hX hαc hα0 hαm hdα hlα⟩


/-- **Aux. lemma 37's witness exclusion in the bounded change pocket, for the strip pockets** (`hwit` of
`StripPocketPath.pocketWordEvolution_of_stripSystem`, exactly in its type). The inputs are the consumer's own: the
strip system with its heights and angles `θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]`, the drivers' regularity, versions of
the walls `α`, `β = η_{π/2}`, `Lr q = β^{(q)}` and of the counterflow's trace `η`, Lemma 5.7's reverse visits and the
non-boundary avoidance `hav`. The walls' means, versions, locality, `β`'s simple properness and the common prefix are
derived (`exists_wallMeans_strip`, `lemma62_walls_rat`, `StripWall.isWallVersion_alpha/beta`,
`ae_isSimpleProper_leftExtremal`, `ae_eq_leftExtremal_of_le`). -/
theorem hwit_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hS.boundaryData
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
  obtain ⟨⟨gU, hgU⟩, ⟨gL, hgL⟩, gR, hgR⟩ := exists_wallMeans_strip h44 hS hcumL hcumR hθ₁c hθ₂c hregα hregβ hu₀
    hαc hα0 hαm hαtr hLc hL0 hLm hLtr
  have hW : ∀ q : ℚ, 0 < q → _ := fun q hq =>
    lemma62_walls_rat h44 hS hcumL hcumR hθ₁c hθ₂c hq hregα (hregβ q hq) hu₀ (hLc q) (hL0 q) (hLm q) (hLtr q hq)
      hαc hα0 hαm hαtr
  exact FlatClockProof.hwit_of_wallMeans h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hu₀
    (isWallVersion_alpha hS hcumL hcumR hθ₁c hregα hαc hα0 hαm hαtr) (hW 1 one_pos).2.2.2.1
    (fun q hq => isWallVersion_beta hS hcumL hcumR hθ₂c (StripSys.rt q) (hregβ q hq) (hLc q) (hL0 q) (hLm q)
      (hLtr q hq)) (fun q hq => (hW q hq).2.1) hgU hgL hgR hηc hηtr hwalls hwallsL
    (ae_isSimpleProper_leftExtremal hS hcumL hcumR hregE hβc hβ0 hβtr)
    (fun q hq => (ae_eq_leftExtremal_of_le h44 hS hcumL hcumR hθ₂c (StripSys.rt q) (hregβ q hq 0) (hLtr q hq)
      hβtr).mono fun ω hω => hω _ le_rfl) hav

/-- **Aux. lemma 37's witness exclusion in the change pocket at the flow seed, for the strip pockets** (`hwitI` of
`StripPocketPath.pocketWordEvolution_of_stripSystem`, exactly in its type), from the consumer's own hypotheses (as
`hwit_strip`; `hwallsL` with both conjuncts, as in the consumer). -/
theorem hwitI_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hS.boundaryData
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
  obtain ⟨⟨gU, hgU⟩, ⟨gL, hgL⟩, gR, hgR⟩ := exists_wallMeans_strip h44 hS hcumL hcumR hθ₁c hθ₂c hregα hregβ hu₀
    hαc hα0 hαm hαtr hLc hL0 hLm hLtr
  have hW : ∀ q : ℚ, 0 < q → _ := fun q hq =>
    lemma62_walls_rat h44 hS hcumL hcumR hθ₁c hθ₂c hq hregα (hregβ q hq) hu₀ (hLc q) (hL0 q) (hLm q) (hLtr q hq)
      hαc hα0 hαm hαtr
  exact FlatClockProof.hwitI_of_wallMeans h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hu₀
    (isWallVersion_alpha hS hcumL hcumR hθ₁c hregα hαc hα0 hαm hαtr) (hW 1 one_pos).2.2.2.1
    (fun q hq => isWallVersion_beta hS hcumL hcumR hθ₂c (StripSys.rt q) (hregβ q hq) (hLc q) (hL0 q) (hLm q)
      (hLtr q hq)) (fun q hq => (hW q hq).2.1) hgU hgL hgR hηc hηtr hwalls hwallsL
    (ae_isSimpleProper_leftExtremal hS hcumL hcumR hregE hβc hβ0 hβtr)
    (fun q hq => (ae_eq_leftExtremal_of_le h44 hS hcumL hcumR hθ₂c (StripSys.rt q) (hregβ q hq 0) (hLtr q hq)
      hβtr).mono fun ω hω => hω _ le_rfl) hav

/-- **Aux. lemma 37's attachment constancy in the bounded change pocket, for the strip pockets** (`hattach` of
`StripPocketConfig.pocketWordEvolution_of_stripPocket`): `hwit_strip` and the reduction to rational witnesses
`attachmentConstancy_of_noWitness`. -/
theorem hattach_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
        (cfArcR (α ω) (Lr q ω) (StripSys.rt q)) (cfArcL (α ω) (Lr q ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) := fun q hq => by
  have hwit := hwit_strip h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hregE hαc hα0 hαm hαtr hβc hβ0 hβtr hLc hL0 hLm
    hLtr hηc hηtr hwalls hwallsL hav q hq
  have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
    simp only [ae_all_iff]
    exact hwit
  filter_upwards [ae_isLoewnerTrace_counterflow hS hcumL hcumR hηtr, hwalls, hwallsL q hq, hw]
    with ω htr hwl hwL hwω hconf hpos
  exact attachmentConstancy_of_noWitness hconf hpos htr.1 htr.2.1 htr.2.2 hwl.1 hwL hwl.2
    fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf hpos

/-- **Aux. lemma 37's attachment constancy in the change pocket at the flow seed, for the strip pockets**
(`hattachI` of `StripPocketConfig.pocketWordEvolution_of_stripPocket`): `hwitI_strip`, the counterflow's
transience (Aux. lemma 7 at `κ′ = 16/κ`, `ae_transient_counterflow`) and `attachmentConstancyInf_of_noWitness`. -/
theorem hattachI_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (Lr q ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
          (cfArcRInf (α ω) (Lr q ω) (StripSys.rt q)) (cfArcLInf (α ω) (Lr q ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (α ω) (Lr q ω) (StripSys.rt q) 0)) := fun q hq => by
  have hwitI := hwitI_strip h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hregE hαc hα0 hαm hαtr hβc hβ0 hβtr hLc hL0
    hLm hLtr hηc hηtr hwalls hwallsL hav q hq
  have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
    simp only [ae_all_iff]
    exact hwitI
  filter_upwards [ae_isLoewnerTrace_counterflow hS hcumL hcumR hηtr,
    ae_transient_counterflow haux7 hS hcumL hcumR hηtr, hwalls, hwallsL q hq, hw]
    with ω htr htω hwl hwL hwω hconf h0
  exact ⟨htω, hwL.2, attachmentConstancyInf_of_noWitness hconf h0 htr.1 htr.2.1 htr.2.2 hwl.1 hwL.1 hwl.2 hwL.2
    fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf h0⟩

/-- **Theorem 1.3's pocket word from the strip system, with Aux. lemma 37's witness exclusions proved**:
`StripPocketPath.pocketWordEvolution_of_stripSystem` without its inputs `hwit`, `hwitI` (supplied by `hwit_strip`,
`hwitI_strip`), for the source's angles `θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]` (Aux. lemma 130, p. 408). All other
binders are the consumer's, verbatim. -/
theorem pocketWordEvolution_of_stripSystem_aux37 {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    {rL rR : ℝ} (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4) (hRr : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (Es StripSys.leftExtremalSpec 0 ω)) (h𝓦 : 𝓦 ≤ mΩ)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable[𝓦] fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0)
    (hLm : ∀ q t, Measurable[𝓦] fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (Es (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) ∧
      IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hnohit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω)))
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (𝔥 : DistOn upperHalfPlaneOpens)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (α ω) (Lr q ω) (StripSys.rt q)) →
      PocketUnionPtInput κ rL rR (𝓦 ⊔ Ito.nullSets P) P α (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)} h₀ 𝔥 ∧
        PocketUnionPtInputInf κ rL rR (𝓦 ⊔ Ito.nullSets P) P α (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)} h₀ 𝔥) :
    Lemma725Ref.PocketWordEvolution.{u} (16 / κ) rL rR := by
  have hαm' : ∀ t, Measurable fun ω => α ω t := fun t => (hαm t).mono h𝓦 le_rfl
  have hLm' : ∀ q t, Measurable fun ω => Lr q ω t := fun q t => (hLm q t).mono h𝓦 le_rfl
  have hwα : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) :=
    hwalls.mono fun ω hω => ⟨hω.1, hω.2.1⟩
  exact pocketWordEvolution_of_stripSystem h44 haux7 hS hcumL hcumR hθ₁ (Ioc_subset_Icc_self hθ₂) hL hLd hRr hRd
    hregα hregβ hregE h𝓦 hαc hα0 hαm hαtr hβc hβ0 hβm hβtr hLc hL0 hLm hLtr hηc hηH hη0 hηm hηtr hwalls hwallsL
    hnohit hav
    (hwit_strip h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hregE hαc hα0 hαm' hαtr hβc hβ0 hβtr hLc hL0 hLm' hLtr hηc
      hηtr hwα (fun q hq => (hwallsL q hq).mono fun ω hω => hω.1) hav)
    (hwitI_strip h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hregE hαc hα0 hαm' hαtr hβc hβ0 hβtr hLc hL0 hLm' hLtr hηc
      hηtr hwα hwallsL hav) hh₀ 𝔥 hin

open StripPocketVersions in
/-- **Theorem 1.3's pocket word from the strip system with R51's regularity, with Aux. lemma 37's witness exclusions
proved**: `StripPocketVersions.pocketWordEvolution_of_stripSystem_reg` without `hwit`, `hwitI` (proved by `hwit_strip`,
`hwitI_strip` for the regularized family `StripWall.regStrip`, a strip system with the same field and counterflow whose
concatenated drivers agree almost surely with the original ones), for `θ₂ ∈ (−π/2, π/2]`. All other binders are the
consumer's, verbatim. -/
theorem pocketWordEvolution_of_stripSystem_reg_aux37 {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    {rL rR : ℝ} (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4) (hRr : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    (hRα : StagedPiecesRegular κ b jumps P (StripSys.alphaSpec θ₁) (Es (StripSys.alphaSpec θ₁)))
    (hRβ : ∀ q : ℚ, 0 < q → StagedPiecesRegular κ b jumps P (StripSys.betaSpec (StripSys.rt q) θ₂)
      (Es (StripSys.betaSpec (StripSys.rt q) θ₂))) (h𝓦 : 𝓦 ≤ mΩ)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable[𝓦] fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0)
    (hLm : ∀ q t, Measurable[𝓦] fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (Es (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) ∧
      IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hnohit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω)))
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (𝔥 : DistOn upperHalfPlaneOpens)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (α ω) (Lr q ω) (StripSys.rt q)) →
      PocketUnionPtInput κ rL rR (𝓦 ⊔ Ito.nullSets P) P α (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)} h₀ 𝔥 ∧
        PocketUnionPtInputInf κ rL rR (𝓦 ⊔ Ito.nullSets P) P α (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)} h₀ 𝔥) :
    Lemma725Ref.PocketWordEvolution.{u} (16 / κ) rL rR := by
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
  have hS' := StripWall.isStripSystem_regStrip hS
  obtain ⟨hregα, hαe⟩ := regStrip_alpha hS hcumL hcumR hθ₁c hRα
  obtain ⟨hregE, hEe⟩ := regStrip_leftExtremal hS hcumL hcumR
  have hregβ : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (StripWall.regStrip κ b jumps P Es (StripSys.betaSpec (StripSys.rt q) θ₂) j ω) :=
    fun q hq => (regStrip_beta hS hcumL hcumR hθ₂c (StripSys.rt q) (hRβ q hq)).1
  have hαtr' : ∀ᵐ ω ∂P, IsGeneratingTrace
      (catPath (StripWall.regStrip κ b jumps P Es (StripSys.alphaSpec θ₁) 0 ω).1 1
        (StripWall.regStrip κ b jumps P Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω) := by
    filter_upwards [hαtr, hαe] with ω h1 h2
    rw [h2]
    exact h1
  have hβtr' : ∀ᵐ ω ∂P, IsGeneratingTrace (StripWall.regStrip κ b jumps P Es StripSys.leftExtremalSpec 0 ω).1 ⊤
      (β ω) := by
    filter_upwards [hβtr, hEe] with ω h1 h2
    rw [h2]
    exact h1
  have hLtr' : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace
      (catPath (StripWall.regStrip κ b jumps P Es (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1 (StripSys.rt q)
        (StripWall.regStrip κ b jumps P Es (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω) :=
    fun q hq => by
      filter_upwards [hLtr q hq, (regStrip_beta hS hcumL hcumR hθ₂c (StripSys.rt q) (hRβ q hq)).2] with ω h1 h2
      rw [h2]
      exact h1
  have hαm' : ∀ t, Measurable fun ω => α ω t := fun t => (hαm t).mono h𝓦 le_rfl
  have hLm' : ∀ q t, Measurable fun ω => Lr q ω t := fun q t => (hLm q t).mono h𝓦 le_rfl
  have hwα : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) :=
    hwalls.mono fun ω hω => ⟨hω.1, hω.2.1⟩
  exact pocketWordEvolution_of_stripSystem_reg h44 haux7 hS hcumL hcumR hθ₁ hθ₂c hL hLd hRr hRd hRα hRβ h𝓦 hαc
    hα0 hαm hαtr hβc hβ0 hβm hβtr hLc hL0 hLm hLtr hηc hηH hη0 hηm hηtr hwalls hwallsL hnohit hav
    (hwit_strip h44 hS' hcumL hcumR hθ₁ hθ₂ hregα hregβ hregE hαc hα0 hαm' hαtr' hβc hβ0 hβtr' hLc hL0 hLm' hLtr' hηc
      hηtr hwα (fun q hq => (hwallsL q hq).mono fun ω hω => hω.1) hav)
    (hwitI_strip h44 hS' hcumL hcumR hθ₁ hθ₂ hregα hregβ hregE hαc hα0 hαm' hαtr' hβc hβ0 hβtr' hLc hL0 hLm' hLtr'
      hηc hηtr hwα hwallsL hav) hh₀ 𝔥 hin

end InteractingSLE.Sec7.Aux37Walls
