/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7Aux131Select
import InteractingSLE.Spec.Sec7.StripPocketPathFinal

/-!
# Aux. lemma 131's pocket in the strip system: the two constant-angle flow lines of the angles (CS13.3)

Packet PROVE-R7-AUX131. Specification §7.4.1, proof of Aux. lemma 131 (`source/spec/p385-432.md` L527–L548,
pp. 414–416): "Set `θ₁ = π(1/2 − (r_L + 2)/A)`, `θ₂ = π((r_R + 2)/A − 1/2)` (CS13.3). Condition (CS13.1) is exactly
`−π/2 ≤ θ₁ < θ₂ ≤ π/2` […] Choose large nonhit strip boundary data and the same centered non-boundary counterflow as
above. Its two constant-angle incoming paths are proper, continuous, simple, and reverse-contained in that
counterflow."

For the strip system of flow parameter `κ < 4` (counterflow parameter `κ′ = 16/κ > 4`) and an extremal pair
`max(r_L, r_R) = κ′/2 − 4` (Theorem R.7's case "neither side is outer"), the right wall is the staged history
`constSpec θ_R`, `θ_R = R7.thetaR κ′ r_L`, and the left wall `constSpec θ_L`, `θ_L = R7.thetaL κ′ r_R`; both angles lie
in `[−π/2, π/2]` (`aux131_angles_of_max_eq`). Here:

* **`r7PocketStopStatement_of_stripSystem`**: `R7PocketStopStatement κ′ r_L r_R GoodR7` from the strip system, with
  the walls' simple properness (`ae_isSimpleProper_const`), the counterflow's Loewner trace and transience
  (`StripPocketPath.ae_isLoewnerTrace_counterflow`, `ae_transient_counterflow` from Aux. lemma 7) and Aux. lemma 37's
  attachments from the exclusion of rational witnesses (`attachmentConstancy_of_noWitness`) proved; the remaining
  inputs are Lemma 5.7's reverse visits of the walls, distinct ranges and the walls' order, the witness exclusions,
  the two-seed walls inputs (walls law at `T⁰(q)` and the two-seed side limits), Proposition 5.13 and a standard Borel
  record of the walls (the same list as STRIPSYS's `pocketWordEvolution_of_stripSystem` for Aux. lemma 130).

Conditional helper; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any result taking them as hypotheses, or `h44`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R7Aux131

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketStopField
  PocketStopWallsFin StripPocketConfig StripPocketPath R7Pocket
open Exist.Staged (IsRegularDriver)

universe u

/-- **`R7PocketStopStatement κ′ r_L r_R GoodR7` from the strip system's two constant-angle flow lines** (Aux. lemma
131, Theorem R.7's extremal pairs `max(r_L, r_R) = κ′/2 − 4`, `κ′ = 16/κ`). The walls are versions `R`, `L` of the
staged histories `constSpec θ_R`, `constSpec θ_L` (continuous at every sample, `0` at time `0`, measurable for the
walls' σ-algebra `𝓦`, almost surely generating traces of the first drivers), the counterflow a version `η` of the
centred counterflow's trace. -/
theorem r7PocketStopStatement_of_stripSystem {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ)) (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR) (hmax : max rL rR = 16 / κ / 2 - 4)
    (hregR : ∀ ω, IsRegularDriver (Es (constSpec (R7.thetaR (16 / κ) rL)) 0 ω))
    (hregL : ∀ ω, IsRegularDriver (Es (constSpec (R7.thetaL (16 / κ) rR)) 0 ω)) (h𝓦 : 𝓦 ≤ mΩ)
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hRc : ∀ ω, Continuous (R ω)) (hR0 : ∀ ω, R ω 0 = 0) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es (constSpec (R7.thetaR (16 / κ) rL)) 0 ω).1 ⊤ (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hL0 : ∀ ω, L ω 0 = 0) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es (constSpec (R7.thetaL (16 / κ) rR)) 0 ω).1 ⊤ (L ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) ∧
      IsWallReverseVisit (L ω) (η ω) ∧ IsWallVisited (L ω) (η ω))
    (hne : ∀ᵐ ω ∂P, range (L ω) ≠ range (R ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))))
    (hwit : ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        ¬ IsPocketWitness (R ω) (L ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂)
    (hwitI : ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (R ω) (L ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      TwoSeedWallsInput (16 / κ) rL rR (𝓦 ⊔ Ito.nullSets P) P R L (StripSys.rt q)
          (fun ω (s : ℝ) => W' s.toNNReal ω) η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u ∧
        TwoSeedWallsInputInf (16 / κ) rL rR (𝓦 ⊔ Ito.nullSets P) P R L (StripSys.rt q)
          (fun ω (s : ℝ) => W' s.toNNReal ω) η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    R7PocketStopStatement.{u} (16 / κ) rL rR GoodR7 := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hκ' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  obtain ⟨-, hθ1, hθ2, hθ3⟩ := aux131_angles_of_max_eq hκ' hL hR hmax
  have hθR : R7.thetaR (16 / κ) rL ∈ Icc (-(π / 2)) (π / 2) := ⟨hθ1, hθ2.le.trans hθ3⟩
  have hθL : R7.thetaL (16 / κ) rR ∈ Icc (-(π / 2)) (π / 2) := ⟨hθ1.trans hθ2.le, hθ3⟩
  have htrace := ae_isLoewnerTrace_counterflow hS hcumL hcumR hηtr
  have htrans := ae_transient_counterflow haux7 hS hcumL hcumR hηtr
  have hRsp := ae_isSimpleProper_const hS hcumL hcumR hθR hregR hRc hR0 hRtr
  have hLsp := ae_isSimpleProper_const hS hcumL hcumR hθL hregL hLc hL0 hLtr
  have hRw : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) := by
    filter_upwards [hRsp, hwalls] with ω h1 h2 using ⟨h1, h2.1, h2.2.1⟩
  have hLw : ∀ᵐ ω ∂P, IsSimpleProper (L ω) ∧ IsWallReverseVisit (L ω) (η ω) := by
    filter_upwards [hLsp, hwalls] with ω h1 h2 using ⟨h1, h2.2.2.1⟩
  have hattach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcR (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0)) := fun q hq => by
    have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
        0 < rightLo (R ω) (L ω) (StripSys.rt q) →
          ¬ IsPocketWitness (R ω) (L ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
      simp only [ae_all_iff]
      exact hwit q hq
    filter_upwards [htrace, hwalls, hw] with ω htr hwl hwω hconf hpos
    exact attachmentConstancy_of_noWitness hconf hpos htr.1 htr.2.1 htr.2.2 hwl.1 hwl.2.2.1 hwl.2.1
      fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf hpos
  have hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (L ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) := fun q hq => by
    have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
        rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
          ¬ IsPocketWitnessInf (R ω) (L ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
      simp only [ae_all_iff]
      exact hwitI q hq
    filter_upwards [htrace, htrans, hwalls, hw] with ω htr htω hwl hwω hconf h0
    exact ⟨htω, hwl.2.2.2, attachmentConstancyInf_of_noWitness hconf h0 htr.1 htr.2.1 htr.2.2 hwl.1 hwl.2.2.1
      hwl.2.1 hwl.2.2.2 fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf h0⟩
  exact r7PocketStopStatement_of_aux131Strip (W := fun ω (s : ℝ) => W' s.toNNReal ω) h𝓦 hRm hLm hηm hηc hη0 hRw
    hLw hne hord htrace hattach hattachI hh₀ hu hub hin h513 hE₀ hgen

end InteractingSLE.Sec7.R7Aux131
