/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Cor48ChamberWalls
import InteractingSLE.Spec.Sec7.Lemma71NMain

/-!
# Wang–Wu at `κ = 4`, (J5): the chamber chart coupling clause from the side limits along the middle line

Packet PROVE-WW-B22. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.24
(text dump L1816–1867): with `u₁ = −λ(ρR + 2) < 0 < u₂ = λ(ρL + 2)`, "The conditional field `H = (h|_C) ∘ ψ⁻¹` is a GFF
in `ℍ` with boundary values `λ − u₂ = −λ(1 + ρL)` on `ℝ₋`, `−λ − u₁ = λ(1 + ρR)` on `ℝ₊`. Proposition 4.20 applies at
every stopping time in the filtration enlarged by the walls. Therefore the transformed middle line `X` satisfies the
local Markov coupling with these values."

On every seed three-line space with the chamber construction (`exists_isPocketConstruction_three`,
`exists_capData_three`), **`isChamberChartData_four_of_curveSide`** gives the chamber chart data — in particular the
chart coupling clause `IsChartCouplingCharFun 4 (ρL) (ρR) …` of `WangWu.Chamber4.Chamber4JointStatement` (J5), for the
seed weights `ρL = u₂/λ − 2`, `ρR = −u₁/λ − 2` read off the wall heights — from the side limits of the active
chamber component **along the middle line only** (`Sec7.Lemma71N.PocketCurveSide`, the first alternative of the
prime-end premise at the chart points of `(L_t − W_t, 0) ∪ (0, R_t − W_t)`). The side limits along the two walls are
proved (`IsSeedThreeSpace.ae_outerSideLimit`); the lift coefficient is `χ(4) = 0`, so no branch hypothesis is needed
(the lift shift is `0`). The proof is the specification's `Sec7.Lemma71N.isPocketChartData_of_curveSide` with the wall
heights `λ − u₂`, `−λ − u₁` in place of the (CPF2) heights.

Conditional helper (on the middle-line side limits); it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.WangWu.SeedThree

open QuantumZipper (H Hbar chiC)
open QuantumZipper.CA (cayley cayleyInv)
open Sec7 MartChar Coupling Sec7.Lemma71C Sec7.Lemma71D Sec7.Lemma71E Sec7.Lemma71K Sec7.Lemma71L Sec7.Lemma71M
  Sec7.Lemma71N Sec7.Lemma71G Sec6 LocalSets

/-- The wall heights of the seed weights: `λ(−1 − ρL) = λ − u₂` and `λ(1 + ρR) = −λ − u₁` for `ρL = u₂/λ − 2`,
`ρR = −u₁/λ − 2`. -/
theorem seed_heights (u₁ u₂ : ℝ) :
    sleLambda 4 * (-1 - (u₂ / wwLambda - 2)) - 0 = wwLambda - u₂ ∧
      sleLambda 4 * (1 + (-u₁ / wwLambda - 2)) - 0 = -wwLambda - u₁ := by
  have hl : wwLambda ≠ 0 := wwLambda_pos.ne'
  have e : sleLambda 4 = wwLambda := SeedField.sleLambda_four
  rw [e]
  constructor <;> field_simp <;> ring

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}
  {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

/-- **The fixed-time chamber clause (J5) on every seed three-line space, from the side limits along the middle line**:
at every deterministic capacity time `t`, almost surely on `{t < capLife}`, the conditional characteristic function of
the field given the walls and the mapped middle prefix up to `t` is that of the chamber chart mean of the word
`(u₂/λ − 2; −u₁/λ − 2)` plus a zero-boundary GFF of the remaining chamber (the clause of WW-B23's
`ChamberCond.ChamberClauseStatement`; `isChamberChartData_four_of_curveSide` lifts it to every stopping time). -/
theorem isChartCouplingCharFunConst_four_of_curveSide [IsProbabilityMeasure P] {rL rR u₁ u₂ : ℝ}
    (hS : IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω)
    (hcurve : ∀ (t : ℝ≥0) (gL : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
        PocketCurveSide (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) vL u₀
          (pocketInv (Lemma71E.shiftLift (c ω) 0) (fun s => segDriver (γ' ω) s) t)
          (pocketGl 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2)
            (Lemma71E.shiftLift (c ω) 0) (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t 0)
          (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t)
          (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t)) :
    IsChartCouplingCharFunConst 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2) P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => Lemma71E.shiftLift (c ω) 0) 0 (chiC 4) h := by
  have hT : IsThreeLineSpace P h u₀ β α γ := hS.2.2.2.2.2.2.1
  refine isChartCouplingCharFunConst_of_sideLimit_three hT hpc hG hM hY hMiff hGeq hYeq (n := fun _ => 0)
    measurable_const (a' := 0) fun t gL gT hgL hgT => ?_
  have hT' := hT
  obtain ⟨-, -, -, hβ62, hα62, hγ62, hae⟩ := hT'
  obtain ⟨hc3, -, him3, -, -, -, -⟩ := Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, hbetw, hfr, hsegc, -, hmark⟩ := hpc'
  obtain ⟨hhL, hhR⟩ := seed_heights u₁ u₂
  filter_upwards [hS.ae_outerSideLimit hpc hgT, hcurve t gL hgL, hae, hT.ae_closedLeftSide, hbetw, hfr,
    hmark] with ω hOSω hcv hω hclω hbω hfrω hmω htl vL vT hvL hgvL hvT hgvT
  obtain ⟨-, hsβ, hsα, hsγ, hord, hγα, hγβ⟩ := hω
  have hβα := hclω.2.2
  obtain ⟨a', b', Ψ, hMk, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hseg, hrange⟩ := hmω
  have hg : PocketGood β α γ C c γ' ω :=
    ⟨hord, hγα, hγβ, hbω, hfrω, a', b', Ψ, hMk, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hseg⟩
  have hF : IsPocketFrame (β ω) (α ω) (C ω) (c ω) Ψ a' b' :=
    ⟨hsβ, hsα, hβα, hbω, hMk, hconf ω, hdom ω, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hfrω⟩
  have hCo : IsOpen (C ω) := (hC ω).1
  have hCH : C ω ⊆ H := (hC ω).2.2.2
  have hγc : Continuous (γ ω) := hc3 2 ω
  have hγH : ∀ t, γ ω t ∈ Hbar := fun t => him3 2 ω t
  -- the sets
  set τ := capTime G M Y β α γ t ω with hτdef
  have hAT : explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω =
      (range (β ω) ∪ range (α ω)) ∩ H := Three.explored_threeOuter β α γ ω (by rw [hsγ.2.2.1]; simp)
  have hA := Three.explored_threeStops β α γ (capTime G M Y β α γ t) ω
  set Γ : Set ℂ := γ ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ τ} with hΓdef
  have hτle := capTime_le_visit hg hCo hCH (hconf ω) (hdom ω) hγH hγc (hsegc ω) (hMiff ω) (hGeq ω) (hYeq ω) htl
  have hΓc : IsCompact Γ := by
    refine (Metric.isCompact_of_isClosed_isBounded (isClosed_le ENNReal.continuous_coe continuous_const)
      ((Metric.isBounded_Icc (0 : ℝ≥0)
        (visitClock (γ ω) (closure (cayley '' C ω)) (capInv (γ' ω) t)).toNNReal).subset fun s hs => ?_)).image hγc
    refine ⟨zero_le (a := s), ?_⟩
    have h3 := (show (s : ℝ≥0∞) ≤ τ from hs).trans hτle
    rw [ENNReal.ofReal] at h3
    exact_mod_cast h3
  have hAsub : explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω ⊆
      explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω ∪ Γ := by
    rw [hA, hAT]
    rintro z ⟨(hz | hz) | hz, hzH⟩
    · exact Or.inl ⟨Or.inl hz, hzH⟩
    · exact Or.inl ⟨Or.inr hz, hzH⟩
    · exact Or.inr hz
  have hfr' : frontier (C ω) ∩ H ⊆ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω := by
    rw [hAT]; exact fun z hz => ⟨hfrω hz, hz.2⟩
  have hΓK : ∀ z ∈ closure (cayley '' C ω) \ {wallPt (α ω) b'}, cayleyInv z ∈ Γ →
      Ψ z ∈ γ' ω '' Icc 0 (capInv (γ' ω) t) := fun z hzK hzΓ =>
    mem_image_of_mem_prefix hg hCo hCH (hconf ω) (hdom ω) hγH hγc hsγ.2.1 (hsegc ω) (hMiff ω) (hGeq ω) (hYeq ω) htl
      hΨi hseg hrange hzK (fun h1 => hF.one_notMem (h1 ▸ hzK)) hzΓ
  have hOS : OuterSideLimit (Lemma71E.shiftLift (c ω) 0) vT u₀ (chiC 4)
      (sleLambda 4 * (-1 - (fun _ : Fin 1 => u₂ / wwLambda - 2) 0) - 0)
      (sleLambda 4 * (1 + (fun _ : Fin 1 => -u₁ / wwLambda - 2) 0) - 0) := by
    simp only
    rw [WangWu.chiC_four, hhL, hhR]
    exact hOSω vT hvT hgvT 0
  have hvL' : (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω) 0 t =
      -RealFlow.rightImg (fun s => -Ito.rpath (fun s => segDriver (γ' ω) s) s) 0 t := by
    simp only [geomL, LP.twoSeedXL, neg_zero]
    rfl
  have hvR' : (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) 0 t =
      RealFlow.rightImg (Ito.rpath fun s => segDriver (γ' ω) s) 0 t := by
    simp only [geomR, LP.twoSeedXR]
    rfl
  exact pocketSideLimit_of_curveSide (isConformal_shiftLift (hconf ω) 0) (hdom ω) hCH hF.closePt_notMem hΨc hΨi
    hΨtop hΨe hF.one_notMem (hsegc ω) htl hΓc hAsub hfr' hΓK 4 _ _ hvL' hvR' 0 hOS (hcv htl vL hvL hgvL)

/-- **(J5) on every seed three-line space, from the side limits along the middle line** (Proposition 4.24's chamber
pair, the clause "the transformed middle line `X` satisfies the local Markov coupling with these values"). On a seed
three-line space with the chamber construction and its capacity data: if at every capacity time `t`, for every
version `gL` of the mean of the three complete lines, almost surely on `{t < capLife}` the active chamber component
has the side limits along the middle line (`PocketCurveSide`) for all harmonic representatives of `gL`, then the
chamber chart data hold for the seed weights `(u₂/λ − 2; −u₁/λ − 2)`, the chart `shiftLift (c ω) 0`, `a = 0` and
`k = χ(4) = 0`; in particular the chart coupling clause `IsChartCouplingCharFun 4 …` in the usual augmentation of the
filtration of the walls and the mapped middle prefix. -/
theorem isChamberChartData_four_of_curveSide [IsProbabilityMeasure P] {rL rR u₁ u₂ : ℝ}
    (hS : IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω)
    (hcurve : ∀ (t : ℝ≥0) (gL : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
        PocketCurveSide (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) vL u₀
          (pocketInv (Lemma71E.shiftLift (c ω) 0) (fun s => segDriver (γ' ω) s) t)
          (pocketGl 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2)
            (Lemma71E.shiftLift (c ω) 0) (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t 0)
          (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t)
          (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t)) :
    IsChamberChartData 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2) P β α γ h
      (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
      γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) (fun ω => Lemma71E.shiftLift (c ω) 0) 0
      (chiC 4) :=
  have hS' := hS
  isChamberChartData_of_isPocketConstruction hS'.2.2.2.2.2.2.1 hpc (n := fun _ => 0) measurable_const
    (isChartCouplingCharFunConst_four_of_curveSide hS hpc hG hM hY hMiff hGeq hYeq hcurve)

end InteractingSLE.WangWu.SeedThree
