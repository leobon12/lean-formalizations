/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Order
import InteractingSLE.Spec.Supplement.GB6Word
import InteractingSLE.Spec.Supplement.S9DCuts
import InteractingSLE.Spec.Jordan.Coupling

/-!
# Proposition GB6: statement of the first-contact assertion and proof of the final assertion

Packet PROVE-JORDANCPL. Supplement §8.6, Proposition GB6 (`source/spec/p481-528.md` L929–L975, pp. 518–520):

> "Let `k > 4`, `κ = 16/k`, and retain the common centered frame `F = −h − πχ`. In a Jordan domain with boundary
> points `x, y`, suppose the original counterflow `η` from `y` to `x` has a finite boundary force word with every side
> partial sum strictly greater than `−2`. Use its complete continuous transient trace and its universal marked field
> coupling. Let `α` be a simple incoming flow prefix from `x`, stopped at a finite own stopping time `σ` before its
> continuation threshold, with `p = α(σ) ∈ D`. […] The original first-contact time is finite and its contact point
> is exactly `p`. In particular, any complete simple constant-angle flow with angle in `[−π/2, π/2]` and these own laws
> is contained in the ambient counterflow range; its points are first visited in reverse flow order."

Everything is read in the original flow chart `(D, x, y) = (ℍ, 0, ∞)` (GB6, proof: "Work first in the original flow
chart"; a general Jordan domain is reduced to it by a chart, `Spec/Jordan/*`). Physical paths take values in the
Riemann sphere `OnePoint ℂ`: the counterflow, whose own chart is the inversion `R(z) = −1/z` (frozen
`IsCenteredCounterflowDriver`), is `η = R̂ ∘ γ` for its generating trace `γ` from `0`, where `R̂` is the inversion of
the sphere (`sphereInv`, `0 ↦ ∞`); it starts at `y = ∞`.

## Main definitions

* `sphereInv`: `z ↦ −1/z` on `OnePoint ℂ` (continuous, `continuous_sphereInv`);
* `GB6FirstContactStatement`: GB6's first-contact assertion ("the original first-contact time is finite and its
  contact point is exactly `p`") for the constant-angle flows of the final assertion, at every deterministic own time
  on the event of an interior tip before the continuation threshold. **Not proved here** (see the handoff).

## Main results

* **`ae_reverseVisit_of_firstContact`** (GB6's final assertion from its first-contact assertion): for a complete
  constant-angle flow (infinite lifetime, continuous generating trace), the first-contact assertion at each rational
  own time with an interior tip implies, almost surely, containment of every flow point in the closure of the
  counterflow range and reverse first-visit order (`t ↦ T(α(t))` antitone);
* `reverseVisit_of_firstContact`: the same for one realization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

open Sec7.Aux130 (firstVisit)

/-! ### The inversion of the Riemann sphere -/

/-- The inversion `z ↦ −1/z` of the Riemann sphere (`0 ↦ ∞`, `∞ ↦ 0`): the counterflow chart `R` of FD12.1 on the
sphere. -/
def sphereInv (p : OnePoint ℂ) : OnePoint ℂ :=
  p.elim ((0 : ℂ) : OnePoint ℂ) fun z => if z = 0 then OnePoint.infty else ((-z⁻¹ : ℂ) : OnePoint ℂ)

@[simp] theorem sphereInv_infty : sphereInv OnePoint.infty = ((0 : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem sphereInv_coe (z : ℂ) :
    sphereInv (z : OnePoint ℂ) = if z = 0 then OnePoint.infty else ((-z⁻¹ : ℂ) : OnePoint ℂ) := rfl

theorem sphereInv_coe_of_ne {z : ℂ} (hz : z ≠ 0) : sphereInv (z : OnePoint ℂ) = ((-z⁻¹ : ℂ) : OnePoint ℂ) := by
  rw [sphereInv_coe]
  exact ite_eq_right_iff.2 fun h => absurd h hz

theorem tendsto_coe_cobounded_onePointC :
    Tendsto ((↑) : ℂ → OnePoint ℂ) (Bornology.cobounded ℂ) (𝓝 OnePoint.infty) := by
  rw [Metric.cobounded_eq_cocompact, ← Filter.coclosedCompact_eq_cocompact]
  exact OnePoint.tendsto_coe_infty

/-- The inversion of the sphere is continuous. -/
theorem continuous_sphereInv : Continuous sphereInv := by
  rw [OnePoint.continuous_iff]
  constructor
  · -- at `∞`: `−1/z → 0`
    rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    have hev : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 :=
      Bornology.isBounded_def.1 Bornology.isBounded_singleton
    have hlim : Tendsto (fun z : ℂ => -z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
      simpa using (tendsto_inv₀_cobounded (α := ℂ)).neg
    refine ((OnePoint.continuous_coe.tendsto _).comp hlim).congr' ?_
    filter_upwards [hev] with z hz
    simp only [Function.comp_apply, sphereInv_coe_of_ne hz]
  · rw [continuous_iff_continuousAt]
    intro z₀
    by_cases hz₀ : z₀ = 0
    · -- at `0`: `−1/z → ∞`
      subst hz₀
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
      change Tendsto (fun z : ℂ => sphereInv (z : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 (sphereInv ((0 : ℂ) : OnePoint ℂ)))
      rw [sphereInv_coe, ite_eq_left_iff.2 fun h => absurd rfl h]
      have hlim : Tendsto (fun z : ℂ => -z⁻¹) (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
        have h1 := tendsto_inv₀_nhdsNE_zero (α := ℂ)
        rw [← tendsto_norm_atTop_iff_cobounded] at h1 ⊢
        simpa only [norm_neg] using h1
      refine (tendsto_coe_cobounded_onePointC.comp hlim).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Function.comp_apply, sphereInv_coe_of_ne hz]
    · have hev : ∀ᶠ z in 𝓝 z₀, z ≠ 0 := isOpen_compl_singleton.mem_nhds hz₀
      have hg : ContinuousAt (fun z : ℂ => ((-z⁻¹ : ℂ) : OnePoint ℂ)) z₀ :=
        OnePoint.continuous_coe.continuousAt.comp (f := fun z : ℂ => -z⁻¹)
          ((continuousAt_inv₀ hz₀).neg)
      refine hg.congr ?_
      filter_upwards [hev] with z hz
      exact (sphereInv_coe_of_ne hz).symm

/-! ### The final assertion of GB6 from its first-contact assertion -/

/-- **GB6's final assertion for one realization.** Let the flow path `α` be the continuous generating trace (infinite
lifetime) of a continuous driver `w` with `w 0 = 0`, and `η` a continuous path in the sphere. If at every rational
own time `q` with an interior tip `α(q) ∈ ℍ` the path `η` first meets `α([0, q])` at `α(q)`, then every flow point
lies in the closure of the range of `η`, and `t ↦ T(α(t))` is antitone (reverse first-visit order). -/
theorem reverseVisit_of_firstContact {η : ℝ≥0 → OnePoint ℂ} {α : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hη : Continuous η) (hα : IsGeneratingTrace w ⊤ α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hfc : ∀ q : ℚ, α (q : ℝ).toNNReal ∈ H →
      IsFirstContactAtTip η (fun t => (α t : OnePoint ℂ)) (q : ℝ).toNNReal) :
    (∀ t, (α t : OnePoint ℂ) ∈ closure (range η)) ∧
      Antitone fun t => firstVisit η ((α t : ℂ) : OnePoint ℂ) := by
  have hαc : Continuous α := by
    have := hα.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hαc' : Continuous fun t => (α t : OnePoint ℂ) := OnePoint.continuous_coe.comp hαc
  set S : Set ℝ≥0 := {s | ∃ q : ℚ, (q : ℝ).toNNReal = s ∧ α s ∈ H} with hS
  have hSfc : ∀ s ∈ S, IsFirstContactAtTip η (fun t => (α t : OnePoint ℂ)) s := by
    rintro s ⟨q, rfl, hq⟩
    exact hfc q hq
  -- interior rational own times are dense: a generating trace has no real subarc, and `{t | α t ∈ ℍ}` is open
  have hdense : ∀ a b : ℝ≥0, a < b → ∃ s ∈ S, a < s ∧ s < b := by
    intro a b hab
    obtain ⟨z, hz, hzH⟩ := Supp9D.exists_mem_H_of_isGeneratingTrace hα hw.continuousOn hw0 hab
      (ENNReal.coe_lt_top)
    have hopen : IsOpen ({t : ℝ≥0 | α t ∈ H} ∩ Ioo a b) :=
      (QuantumZipper.isOpen_H.preimage hαc).inter isOpen_Ioo
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen z ⟨hzH, hz⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (z : ℝ) < z + ε by linarith)
    have hq0 : (0 : ℝ) ≤ q := le_trans z.coe_nonneg hq1.le
    have hs : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
    have hsU : (q : ℝ).toNNReal ∈ {t : ℝ≥0 | α t ∈ H} ∩ Ioo a b := by
      refine hball ?_
      rw [Metric.mem_ball, NNReal.dist_eq, hs, abs_of_pos (by linarith)]
      linarith
    exact ⟨_, ⟨q, rfl, hsU.1⟩, hsU.2.1, hsU.2.2⟩
  exact ⟨mem_closure_range hαc' hSfc hdense, antitone_firstVisit hη hαc' hSfc hdense⟩

/-- **GB6's final assertion** ("apply the result on the event of an interior tip at each rational own time and
intersect these countably many probability-one events"): for a complete constant-angle flow (infinite lifetime,
continuous generating trace of a continuous driver) and a counterflow with continuous physical path, the
first-contact assertion at each rational own time, on the event of an interior tip, gives almost surely containment
and reverse first-visit order. -/
theorem ae_reverseVisit_of_firstContact {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {η : Ω → ℝ≥0 → OnePoint ℂ} {α : Ω → ℝ≥0 → ℂ} {w : ℝ≥0 → Ω → ℝ}
    (hpaths : ∀ᵐ ω ∂P, Continuous (η ω) ∧ IsGeneratingTrace (fun t => w t ω) ⊤ (α ω) ∧
      Continuous (fun t => w t ω) ∧ w 0 ω = 0)
    (hfc : ∀ q : ℚ, ∀ᵐ ω ∂P, α ω (q : ℝ).toNNReal ∈ H →
      IsFirstContactAtTip (η ω) (fun t => (α ω t : OnePoint ℂ)) (q : ℝ).toNNReal) :
    ∀ᵐ ω ∂P, (∀ t, (α ω t : OnePoint ℂ) ∈ closure (range (η ω))) ∧
      Antitone fun t => firstVisit (η ω) ((α ω t : ℂ) : OnePoint ℂ) := by
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, α ω (q : ℝ).toNNReal ∈ H →
      IsFirstContactAtTip (η ω) (fun t => (α ω t : OnePoint ℂ)) (q : ℝ).toNNReal := ae_all_iff.2 hfc
  filter_upwards [hpaths, hall] with ω ⟨hη, hα, hw, hw0⟩ hq
  exact reverseVisit_of_firstContact hη hα hw hw0 hq

/-! ### The first-contact assertion of GB6 (statement) -/

/-- **Proposition GB6, first-contact assertion** for the constant-angle flows of its final assertion, at deterministic
own times (the form used by "apply the result on the event of an interior tip at each rational own time"). In the
original flow chart `(ℍ, 0, ∞)`: `κ ∈ (0, 4)`, a GFF `h` with piecewise-constant data `b`; `W` drives the centred
counterflow of `h` (frozen `IsCenteredCounterflowDriver`; Theorem 1.1's coupling of `F = −h − πχ` at `16/κ` in the
inversion), whose counterflow word, read in the inversion with the data `b'`, has every side partial sum strictly
greater than `−2` (`hadm`), with a complete continuous transient trace `γ`; `Wα` drives the angle-`θ` flow line of the
same `h`, `θ ∈ [−π/2, π/2]`, with continuous generating trace `α`. Then for every own time `s`, almost surely on
`{s < ζα, α(s) ∈ ℍ}`, the physical counterflow `η = R̂ ∘ γ` first meets `α([0, s])` at a finite time, at `α(s)`.

This is a named statement, not an assumption of any theorem claimed as GB6; it is proved in the source by the
conditional-law identification of GB6 (see `planning/handoffs/PROVE-JORDANCPL.md`). -/
def GB6FirstContactStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    -- the counterflow, written with the witness `(b', J', h')` of its frozen definition
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    -- every side partial sum of the counterflow word is strictly greater than `−2`
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    -- its complete continuous transient trace
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    -- the constant-angle flow line of the same field and its continuous generating trace
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ s : ℝ≥0, ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsFirstContactAtTip (fun t => sphereInv (γ ω t : OnePoint ℂ)) (fun t => (α ω t : OnePoint ℂ)) s

/-- **The final assertion of GB6 from its first-contact assertion** (conditional on the named
`GB6FirstContactStatement`; distinct name, not GB6 itself): in the setting of the statement, a complete constant-angle
flow line (`ζα = ∞` almost surely) is almost surely contained in the closure of the physical counterflow range, and
its points are first visited in reverse flow order. -/
theorem ae_reverseVisit_of_gb6FirstContactStatement (hGB6 : GB6FirstContactStatement.{u}) {κ θ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [hP : IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {b : ℝ → ℝ}
    {J : Finset ℝ} {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {b' : ℝ → ℝ} {J' : Finset ℝ}
    {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hb : IsPiecewiseConstantBoundaryData b J)
    (hG : IsGFFWithBoundaryData P h b J) (hb' : IsPiecewiseConstantBoundaryData b' J')
    (htr : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hadmL : ∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l)
    (hadmR : ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l)
    (hcomp : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (hζα : ∀ᵐ ω ∂P, ζα ω = ⊤) :
    ∀ᵐ ω ∂P, (∀ t, (α ω t : OnePoint ℂ) ∈ closure (range fun t => sphereInv (γ ω t : OnePoint ℂ))) ∧
      Antitone fun t => firstVisit (fun t => sphereInv (γ ω t : OnePoint ℂ)) ((α ω t : ℂ) : OnePoint ℂ) := by
  have hstmt := hGB6 κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' htr hcf hadmL hadmR
    hcomp hfl hα
  obtain ⟨_, _, _, _, _, _, hC⟩ := hfl
  have hpath := hC.1.2.2.2.2
  refine ae_reverseVisit_of_firstContact (w := Wα) ?_ fun q => ?_
  · filter_upwards [hcomp, hα, hζα, hpath] with ω hcω hαω hζω hp
    have hγ := hcω.2.1
    rw [hζω] at hαω hp
    have hγc : Continuous (γ ω) := by
      have := hγ.2.1
      simp only [le_top, ofPred_true] at this
      exact continuousOn_univ.1 this
    have hwc : Continuous fun t => Wα t ω := by
      have := hp.2.2.2.1
      simp only [ENNReal.coe_lt_top, ofPred_true] at this
      exact continuousOn_univ.1 this
    exact ⟨continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγc), hαω, hwc, hp.1⟩
  · filter_upwards [hstmt (q : ℝ).toNNReal, hζα] with ω hω hζω hqH
    exact hω (by rw [hζω]; exact ENNReal.coe_lt_top) hqH

end GB6

end Supp8

end InteractingSLE
