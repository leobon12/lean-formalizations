/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Cor48ChamberMiddle
import InteractingSLE.WangWu.J5ChartClauseConst

/-!
# (J5) at `κ = 4` from the landing of the chamber chart on the middle line (geometric input only)

Packet PROVE-WW-B22. The side limits of the active chamber component along the middle line (`ChamberCurveSideStatement`,
the last input of `chamberClauseStatement_of_curveSide`) split, as in the specification's Lemma 7.1 (PROVE-LEMMA71Q),
into
* the **side heights** of the three-line mean along the middle line (Proposition 4.20 on the middle line, proved at
  `κ = 4`: `IsSeedThreeSpace.ae_middleSideHeight`),
* the **seed values** `∓λ` of the chart mean on the two middle intervals
(`Sec7.Lemma71Q.tendsto_meanHarmonic_left/right`),
* the **landing**: at every chart point of the two middle intervals the inverse chart of the remaining chamber tends to
  a point `γ(s)` (`s > 0`, before the stop) of the middle prefix off the facing wall, approaching from the corresponding
  side of `γ`.

At `κ = 4` the lift coefficient `χ(4)` vanishes, so the landing is needed **without** the specification's lift clause
(`Sec7.Lemma71Q.MiddleLanding` also asks the chart lift to agree with `Im log g_q′`): `MiddleLand`. This file proves

* `MiddleLanding.middleLand` (the specification's landing implies the lift-free one);
* **`pocketCurveSide_of_land_four`** (deterministic; `Sec7.Lemma71Q.pocketCurveSide_of_middleLanding` without the lift);
* `ChamberLandStatement` (**named input**: the lift-free landing on every three-line space — a purely geometric
statement
  about three ordered simple proper arcs and the chamber chart, the counterpart of
`Sec7.Lemma71Q.MiddleLandingStatement`,
  whose geometric content is `Sec7.Lemma71P.MidRealOffStatement` (PROVE-LEMMA71T) and `Sec7.Lemma71P.ae_curveSideGeom`);
* **`chamberCurveSideStatement_of_land`**: `ChamberLandStatement → ChamberCurveSideStatement`;
* **`chamberClauseStatement_of_land`**: `ChamberLandStatement → ChamberCond.ChamberClauseStatement` (WW-B23's fixed-time
  clause).

Conditional helpers (on the geometric landing); they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.WangWu.SeedThree

open Sec7 MartChar Sec7.Lemma71C Sec7.Lemma71D Sec7.Lemma71E Sec7.Lemma71I Sec7.Lemma71K Sec7.Lemma71L Sec7.Lemma71M
  Sec7.Lemma71N Sec7.Lemma71Q Sec6 LocalSets

/-! ### The lift-free landing and its deterministic assembly -/

section Land

variable {β α γ : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}

/-- **The lift-free landing** of an inverse chart `Finv` at a real point `x`: it tends to a point `γ(s)` with `s > 0`,
before the stop `τ`, off the facing curve `η'`, and approaches it from inside `S` and off the stopped union `A`. -/
def MiddleLand (γ η' : ℝ≥0 → ℂ) (τ : ℝ≥0∞) (A S : Set ℂ) (Finv : ℂ → ℂ) (x : ℝ) : Prop :=
  ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < τ ∧ γ s ∉ range η' ∧ Tendsto Finv (𝓝[H] (x : ℂ)) (𝓝 (γ s)) ∧
    ∀ᶠ y in 𝓝[H] (x : ℂ), Finv y ∈ S \ A

/-- The specification's landing (with the lift clause) implies the lift-free one. -/
theorem MiddleLanding.middleLand {η' : ℝ≥0 → ℂ} {τ : ℝ≥0∞} {A S : Set ℂ} {Finv : ℂ → ℂ} {lift : ℂ → ℝ} {x : ℝ}
    (h : MiddleLanding γ η' W τ A S Finv lift x) : MiddleLand γ η' τ A S Finv x := by
  obtain ⟨s, hs0, hsτ, hsη', hlim, hev, -⟩ := h
  exact ⟨s, hs0, hsτ, hsη', hlim, hev⟩

/-- **The middle-line side limits of the active component from the side heights, the seed values and the lift-free
landing** (`κ = 4`, `χ(4) = 0`; the specification's `Sec7.Lemma71Q.pocketCurveSide_of_middleLanding` without the lift).
Pathwise. -/
theorem pocketCurveSide_of_land_four (hγ : IsSimpleProper γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : IsGeneratingTrace W ⊤ γ) {τ : ℝ≥0∞} {A AL : Set ℂ}
    (hA : A = (range β ∪ range α ∪ γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ}) ∩ H)
    (hAL : AL = (range β ∪ range α ∪ range γ) ∩ H) {vL u₀ : ℂ → ℝ} {lam : ℝ}
    (hM : MiddleSideHeight β α γ W AL vL u₀ 0 lam) {xL xR : ℝ} {Gs : ℂ → ℝ}
    (hGL : ∀ x : ℝ, xL < x → x < 0 → Tendsto Gs (𝓝[H] (x : ℂ)) (𝓝 (-lam)))
    (hGR : ∀ x : ℝ, 0 < x → x < xR → Tendsto Gs (𝓝[H] (x : ℂ)) (𝓝 lam)) {Finv : ℂ → ℂ} (lift : ℂ → ℝ)
    (hlandL : ∀ x : ℝ, xL < x → x < 0 → MiddleLand γ β τ A (leftSideOf (range γ)) Finv x)
    (hlandR : ∀ x : ℝ, 0 < x → x < xR → MiddleLand γ α τ A (rightSideOf (range γ)) Finv x) :
    PocketCurveSide A AL vL u₀ Finv (fun y => Gs y - chiC 4 * lift (Finv y)) xL xR := by
  intro x hx
  have key : ∀ (η' : ℝ≥0 → ℂ) (S : Set ℂ) (h₀ : ℝ), MiddleLand γ η' τ A S Finv x →
      Tendsto Gs (𝓝[H] (x : ℂ)) (𝓝 h₀) →
      (∀ (s : ℝ≥0) (q : ℚ≥0), 0 < s → s < (q : ℝ≥0) → γ s ∉ range η' → Tendsto (fun z => vL z + u₀ z +
        0 * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z).im)
        (𝓝[S \ AL] (γ s)) (𝓝 h₀)) →
      ∃ p : ℂ, Tendsto Finv (𝓝[H] (x : ℂ)) (𝓝 p) ∧ p ∈ A ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, AL ∩ ball p r ⊆ A) ∧
        Tendsto (fun y => vL (Finv y) + u₀ (Finv y) - (Gs y - chiC 4 * lift (Finv y))) (𝓝[H] (x : ℂ))
          (𝓝 0) := by
    intro η' S h₀ hland hG hside
    obtain ⟨s, hs0, hsτ, hsη', hlim, hev⟩ := hland
    obtain ⟨hpA, r, hr, hALA⟩ := landing_mem hγ hA hAL hs0 hsτ
    refine ⟨γ s, hlim, Or.inl hpA, ⟨r, hr, hALA⟩, ?_⟩
    have hF : Tendsto Finv (𝓝[H] (x : ℂ)) (𝓝[S \ AL] (γ s)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hlim, ?_⟩
      filter_upwards [hev, hlim (ball_mem_nhds _ hr)] with y hy hyb
      exact ⟨hy.1, fun hyAL => hy.2 (hALA ⟨hyAL, hyb⟩)⟩
    obtain ⟨q', hsq', -⟩ := Lemma71L.exists_nnrat_btwn s.2 (show (s : ℝ) < s + 1 by linarith)
    have hsq'' : s < (q' : ℝ≥0) := by exact_mod_cast hsq'
    have h1 := (hside s q' hs0 hsq'' hsη').comp hF
    have hsum := h1.sub hG
    rw [sub_self] at hsum
    refine hsum.congr fun y => ?_
    simp only [Function.comp_apply, WangWu.chiC_four, zero_mul, add_zero, sub_zero]
  rcases hx with ⟨hxL, hx0⟩ | ⟨hx0, hxR⟩
  · exact key β (leftSideOf (range γ)) (-lam) (hlandL x hxL hx0) (hGL x hxL hx0)
      fun s q hs0 hsq hsβ => hM.tendsto_left hγ hW hW0 htr hs0 hsq hsβ le_rfl
  · exact key α (rightSideOf (range γ)) lam (hlandR x hx0 hxR) (hGR x hx0 hxR)
      fun s q hs0 hsq hsα => hM.tendsto_right hγ hW hW0 htr hs0 hsq hsα le_rfl

end Land

/-! ### The named geometric input and the reductions -/

section Named

/-- **Named input (the lift-free landing of the chamber chart on the middle line).** On every three-line space, for
every chamber construction with its capacity data, at every capacity time `t`: almost surely on `{t < capLife}` there is
a generating driver `W` of the middle line such that at every chart point of `(L_t − W_t, 0)` the time-`t` inverse chart
of the remaining chamber lands on the left side of `γ` at a point of the stopped prefix off the left wall `β`
(`MiddleLand`), and at every chart point of `(0, R_t − W_t)` on the right side at a point off the right wall `α`. A
geometric statement (no field, no `κ`); the counterpart of the specification's `Sec7.Lemma71Q.MiddleLandingStatement`
without its lift clause. -/
def ChamberLandStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ), IsThreeLineSpace P h u₀ β α γ →
    ∀ (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ), IsPocketConstruction P β α γ C c γ' →
    ∀ (G : (Hist × Hist) × ℂ → ℂ) (M : Set ((Hist × Hist) × ℂ)) (Y : Hist × Hist → ℂ),
      Measurable G → MeasurableSet M → Measurable Y → (∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω) →
      (∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z) → (∀ ω, Y (outerHist β α ω) = closePt α C ω) →
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∃ W : ℝ≥0 → ℝ, IsGeneratingTrace W ⊤ (γ ω) ∧
      (∀ x : ℝ, geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t < x → x < 0 →
        MiddleLand (γ ω) (β ω) (capTime G M Y β α γ t ω)
          (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (leftSideOf (range (γ ω))) (pocketInv (shiftLift (c ω) 0) (fun s => segDriver (γ' ω) s) t) x) ∧
      (∀ x : ℝ, 0 < x → x < geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t →
        MiddleLand (γ ω) (α ω) (capTime G M Y β α γ t ω)
          (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (rightSideOf (range (γ ω))) (pocketInv (shiftLift (c ω) 0) (fun s => segDriver (γ' ω) s) t) x)

/-- **(CS) at `κ = 4` from the lift-free landing**: the side heights are `IsSeedThreeSpace.ae_middleSideHeight`, the
seed
values `tendsto_meanHarmonic_left/right` (with `λ = π/√4`), the assembly `pocketCurveSide_of_land_four` (the proof of
the
specification's `Sec7.Lemma71Q.pocketCurveSideStatement_of_middleLanding`). Conditional helper. -/
theorem chamberCurveSideStatement_of_land (hL : ChamberLandStatement.{u}) : ChamberCurveSideStatement.{u} := by
  intro Ω _ P _ rL rR u₁ u₂ h u₀ β α γ hS C c γ' hpc G M Y hG hM hY hMiff hGeq hYeq t gL hgL
  have hT : IsThreeLineSpace P h u₀ β α γ := hS.2.2.2.2.2.2.1
  have hland := hL P h u₀ β α γ hT C c γ' hpc G M Y hG hM hY hMiff hGeq hYeq t
  have hMS := hS.ae_middleSideHeight hgL
  have hT' := hT
  obtain ⟨-, -, -, -, -, -, hae⟩ := hT'
  have hpc' := hpc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsegc, -⟩ := hpc'
  have hlam : sleLambda 4 = wwLambda := SeedField.sleLambda_four
  filter_upwards [hland, hMS, hae] with ω hlω hMω hω htl vL hvL hvLr
  obtain ⟨W, hWtr, hlL, hlR⟩ := hlω htl
  obtain ⟨-, -, -, hsγ, -⟩ := hω
  have hMω' := hMω W hWtr vL hvL hvLr
  have hWc : Continuous W := continuousOn_univ.1 ((SideHeight.continuousOn_of_isGeneratingTrace hWtr).mono
    fun s _ => show (s : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hW0 : W 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace hWtr (by simp)
  set w : ℝ≥0 → ℝ := fun s => segDriver (γ' ω) s with hwdef
  set vLf : Fin 1 → ℝ≥0 → ℝ := fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω with hvLfdef
  set vRf : Fin 1 → ℝ≥0 → ℝ := fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω with hvRfdef
  have hvL' : vLf 0 t = -RealFlow.rightImg (fun s => -Ito.rpath (fun s => segDriver (γ' ω) s) s) 0 t := by
    simp only [hvLfdef, geomL, LP.twoSeedXL, neg_zero]
    rfl
  have hvR' : vRf 0 t = RealFlow.rightImg (Ito.rpath fun s => segDriver (γ' ω) s) 0 t := by
    simp only [hvRfdef, geomR, LP.twoSeedXR]
    rfl
  obtain ⟨hsL, hsR⟩ := seed_sub_driver (hsegc ω) htl hvL' hvR'
  have e1 : (fun i : Fin 1 => vLf i t - w t) = fun _ => vLf 0 t - segDriver (γ' ω) t := by
    funext i; rw [Subsingleton.elim i 0]
  have e2 : (fun i : Fin 1 => vRf i t - w t) = fun _ => vRf 0 t - segDriver (γ' ω) t := by
    funext i; rw [Subsingleton.elim i 0]
  have hG : pocketG 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2) w vLf vRf t 0 =
      Ito.meanHarmonic 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2)
        (fun _ => vLf 0 t - segDriver (γ' ω) t) (fun _ => vRf 0 t - segDriver (γ' ω) t) := by
    funext y
    unfold Lemma71M.pocketG
    rw [e1, e2, sub_zero]
  have hGL : ∀ x : ℝ, vLf 0 t - segDriver (γ' ω) t < x → x < 0 →
      Tendsto (pocketG 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2) w vLf vRf t 0)
        (𝓝[H] (x : ℂ)) (𝓝 (-wwLambda)) := by
    intro x hxL hx0
    have h1 := tendsto_meanHarmonic_left 4 (fun _ : Fin 1 => u₂ / wwLambda - 2)
      (fun _ : Fin 1 => -u₁ / wwLambda - 2) hxL hx0 hsR
    rw [hlam] at h1
    rw [hG]
    exact h1
  have hGR : ∀ x : ℝ, 0 < x → x < vRf 0 t - segDriver (γ' ω) t →
      Tendsto (pocketG 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2) w vLf vRf t 0)
        (𝓝[H] (x : ℂ)) (𝓝 wwLambda) := by
    intro x hx0 hxR
    have h1 := tendsto_meanHarmonic_right 4 (fun _ : Fin 1 => u₂ / wwLambda - 2)
      (fun _ : Fin 1 => -u₁ / wwLambda - 2) hsL hx0 hxR
    rw [hlam] at h1
    rw [hG]
    exact h1
  exact pocketCurveSide_of_land_four hsγ hWc hW0 hWtr
    (Three.explored_threeStops β α γ (capTime G M Y β α γ t) ω) (Three.explored_threeTop β α γ ω) hMω' hGL hGR
    (pocketLift (shiftLift (c ω) 0) w t) hlL hlR

/-- **WW-B23's fixed-time chamber clause from the lift-free landing alone** (`ChamberCond.ChamberClauseStatement`;
`chamberClauseStatement_of_curveSide` and `chamberCurveSideStatement_of_land`). Conditional helper. -/
theorem chamberClauseStatement_of_land (hL : ChamberLandStatement.{u}) : ChamberCond.ChamberClauseStatement.{u} :=
  chamberClauseStatement_of_curveSide (chamberCurveSideStatement_of_land hL)

end Named

end InteractingSLE.WangWu.SeedThree
