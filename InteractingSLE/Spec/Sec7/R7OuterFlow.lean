/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripDet
import InteractingSLE.Spec.Sec7.StripHeights44
import InteractingSLE.Spec.Sec7.Lemma71HInputs
import InteractingSLE.Spec.Sec7.Lemma75Bridge
import InteractingSLE.Spec.Sec5.Prop55Half
import InteractingSLE.Spec.Supplement.R7Angles

/-!
# Theorem R.7, part (a): the incoming flow lines of every angle, as Borel functions of the field

Packet PROVE-R7-OUTER. Supplement §5.1 and the proof of Theorem R.7 (`source/spec/p433-480.md` L956–L966, L1058–L1063,
pp. 471 and 477):

> "The available non-boundary inputs are the complete simple extremal flow lines `β_R, β_L` of angles `−π/2, +π/2`
> […] An incoming right arm is either a contained strict-angle line, the certified right frontier, or a simple
> non-boundary line `α_R ⊂ Ē_R`." (p. 471)
>
> "A weight below `d` gives a strictly contained side, equality gives the corresponding certified extremal side, and
> a weight above `d` gives an outer side. There is no upper bound on the two weights. Choose the original boundary
> values large enough to make these two complete flow lines and the original counterflow non-boundary." (p. 477)

An outer arm has angle `θ ∉ [−π/2, π/2]` (`R7.d_lt_rL_iff`, `R7.d_lt_rR_iff`), so it is not a staged history of the
strip system (the frozen `IsBoundaryContinuedProgram` allows only `[−π/2, π/2]`). It is constructed here as a
**separate object**: the flow line (frozen `IsFlowLine`) of the same field `h`, with the original boundary values
chosen large enough — the (4.4) heights `StripHeights44.IsHeightBounded44` at its angle. In that regime everything is
R48-safe, from the §4.2 reference `Lemma71H.Cond44ReferenceStatement` alone (no Theorem 1.2/1.3):

* `cond44_of_heights`, `hasAdmissiblePartialSums_of_heights`: (4.4) for the flow-line word (`StripDet`);
* **`exists_isFlowLine_of_heights`**: the flow line of `h` at the angle exists on the given probability space
  (`Lemma71H.exists_isFlowLine_of_det`);
* **`IsFlowLine.ae_regular_of_heights`**: almost surely infinite lifetime and a simple proper curve from `0`, in `ℍ`
  at positive times, tending to `∞` (`Prop55Half.IsFlowLine.ae_isSeedProper`); it does not touch `ℝ ∖ {0}`;
* **`exists_flowLineMap_of_heights`**: one Borel map `Φ` of the field gives the lifetime and the path of every flow
  line at this angle of every field with this datum (`Lemma75Bridge.exists_flowLineMap_of_admissible`, Aux. lemma 23);
* **`exists_isFlowLine_borel_of_heights`**: a version `η = (Φ ∘ h).2` which is a Borel function of the field at every
  sample and is itself a flow line — the outer arm `α_R` (or `α_L`, `β_R`, `β_L`) as a pathwise object;
* `isHeightBounded44_prop74Data`, `isHeightBounded44_prop74Data_of_mem_Icc`: for the data `−a` on `ℝ₋`, `b` on `ℝ₊`
  (Figure 7.1), explicit large values give (4.4) at every angle of a closed interval — in particular at the four R.7
  angles `θ_R ≤ −π/2 < π/2 ≤ θ_L` simultaneously (`r7A`, `r7B`, `isHeightBounded44_r7`).

R48: nothing here takes Theorem 1.2, Theorem 1.3, `Theorem12ParamStatement` or `Theorem13Statement` as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec7.R7Outer

open StripHeights44 (IsHeightBounded44)
open Sec5.Prop55Half (IsSeedProper)

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ}

/-! ### (4.4) heights and the flow-line word -/

/-- (4.4) at the angle `θ` implies Remark 4.1's admissible bounds (the right bound `λ ≤ b + θχ` is stronger than
`λ − πχ ≤ b + θχ` since `χ > 0` for `κ < 4`). -/
theorem admissible_of_heights (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : IsHeightBounded44 κ b J θ) :
    (∀ x : ℝ, x < 0 → x ∉ J → b x + θ * chiC κ ≤ -sleLambda κ + π * chiC κ) ∧
      ∀ x : ℝ, 0 < x → x ∉ J → sleLambda κ - π * chiC κ ≤ b x + θ * chiC κ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  refine ⟨hθ.1, fun x hx hxJ => ?_⟩
  have := hθ.2 x hx hxJ
  nlinarith [Real.pi_pos]

/-- (4.4) for the angle-`θ` flow-line word from `0` (`StripDet.cond44_flowLine_of_heights`). -/
theorem cond44_of_heights (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hθ : IsHeightBounded44 κ b J θ) : Sec4.Cond44 κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) :=
  StripDet.cond44_flowLine_of_heights hκ hb θ hθ.1 hθ.2

/-- The flow-line word has admissible side partial sums (Remark 4.1's regime). -/
theorem hasAdmissiblePartialSums_of_heights (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hθ : IsHeightBounded44 κ b J θ) :
    Sec4.HasAdmissiblePartialSums κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0)
      (flowLineXR b J 0) :=
  Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 (Theorem15.isOrderedForceWord_flowLine b J 0)
    (cond44_of_heights hκ hb hθ)

/-! ### Existence, regularity and determination -/

/-- **The flow line of the field at the angle `θ` exists on the given probability space** (non-boundary data: the
(4.4) heights at `θ`), from the §4.2 reference alone. For an outer angle `θ ∉ [−π/2, π/2]` this is Theorem R.7's
outer arm, constructed as a separate object of the same field. -/
theorem exists_isFlowLine_of_heights (href : Lemma71H.Cond44ReferenceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J θ) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b J 0 θ P h η ζ :=
  Lemma71H.exists_isFlowLine_of_det hκ hκ4.le hb hh (hasAdmissiblePartialSums_of_heights hκ hκ4 hb hθ)
    (Lemma71H.hasFieldDeterminedHistories_of_cond44 href hκ hκ4 (Theorem15.isOrderedForceWord_flowLine b J 0)
      (cond44_of_heights hκ hb hθ))

/-- **Regularity of a non-boundary flow line**: almost surely its lifetime is infinite and it is a simple proper curve
from `0`, in `ℍ` at positive times, tending to `∞` (Remark 2.3 for `κ ≤ 4`, Aux. lemma 7). -/
theorem IsFlowLine.ae_regular_of_heights (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hθ : IsHeightBounded44 κ b J θ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ b J 0 θ P h η ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsSeedProper (η ω) :=
  Sec5.Prop55Half.IsFlowLine.ae_isSeedProper hκ hκ4.le hb (admissible_of_heights hκ hκ4 hθ).1
    (admissible_of_heights hκ hκ4 hθ).2 hfl

/-- A seed-proper curve meets `ℝ` only at its seed `0`. -/
theorem IsSeedProper.ne_ofReal {γ : ℝ≥0 → ℂ} (hγ : IsSeedProper γ) (t : ℝ≥0) {x : ℝ} (hx : x ≠ 0) :
    γ t ≠ x := by
  intro e
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · rw [← ht, hγ.2.2.1] at e
    exact hx (by exact_mod_cast e.symm)
  · have hH := hγ.2.2.2.1 t ht
    rw [e] at hH
    exact absurd hH (by simp [QuantumZipper.H])

/-- **Determination** (Lemma 7.5 in the non-boundary regime, R48-safe): one Borel map `Φ` of the field gives the
lifetime and the path up to the lifetime of every angle-`θ` flow line from `0` of every field with the data `b`
(Aux. lemma 23 and the §4.2 reference). -/
theorem exists_flowLineMap_of_heights (href : Lemma71H.Cond44ReferenceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J θ) :
    ∃ Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b J →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b J 0 θ P h η ζ →
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (Φ (h ω)).2 t = η ω t :=
  Lemma75Bridge.exists_flowLineMap_of_admissible hκ hκ4.le (hasAdmissiblePartialSums_of_heights hκ hκ4 hb hθ)
    (href κ hκ hκ4 _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b J 0) (cond44_of_heights hκ hb hθ))

/-- A generating trace depends only on the curve up to the horizon. -/
theorem isGeneratingTrace_congr {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η η' : ℝ≥0 → ℂ}
    (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → η' t = η t) (hη : IsGeneratingTrace w T η) :
    IsGeneratingTrace w T η' := by
  obtain ⟨h0, hc, hf⟩ := hη
  refine ⟨by rw [he 0 zero_le]; exact h0, hc.congr fun t ht => he t ht, fun t ht => ?_⟩
  have e : η' '' Icc 0 t = η '' Icc 0 t := image_congr fun s hs =>
    he s ((ENNReal.coe_le_coe.2 hs.2).trans ht.le)
  rw [e]
  exact hf t ht

/-- A flow line stays a flow line when its path is modified, almost surely, only after the lifetime. -/
theorem IsFlowLine.congr_path {x : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {η η' : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ b J x θ P h η ζ)
    (he : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η' ω t = η ω t) : IsFlowLine κ b J x θ P h η' ζ := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hc, hgen⟩ := hfl
  refine ⟨h', 𝓕, W, VL, VR, B, htr, hc, ?_⟩
  filter_upwards [hgen, he] with ω hω heω
  exact isGeneratingTrace_congr (fun t ht => by rw [heω t ht]) hω

/-- **The incoming arm as a Borel function of the field** (Theorem R.7's arms as pathwise objects): on any
probability space carrying the GFF `h` with (4.4) heights at `θ`, there are a Borel map `Φ` and a lifetime `ζ` such
that `(Φ ∘ h).2` is the angle-`θ` flow line of `h` from `0` with lifetime `ζ`, almost surely `ζ = (Φ ∘ h).1 = ∞` and
`(Φ ∘ h).2` is a simple proper curve in `ℍ` at positive times; and `Φ` gives every other flow line of every field
with this datum at this angle. -/
theorem exists_isFlowLine_borel_of_heights (href : Lemma71H.Cond44ReferenceStatement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J θ) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) :
    ∃ (Φ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ)) (ζ : Ω → ℝ≥0∞), Measurable Φ ∧
      IsFlowLine κ b J 0 θ P h (fun ω => (Φ (h ω)).2) ζ ∧
      (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (Φ (h ω)).1 = ⊤ ∧ IsSeedProper (Φ (h ω)).2) ∧
      ∀ {Ω' : Type u} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (h' : Ω' → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P' h' b J →
      ∀ (η' : Ω' → ℝ≥0 → ℂ) (ζ' : Ω' → ℝ≥0∞), IsFlowLine κ b J 0 θ P' h' η' ζ' →
        ∀ᵐ ω ∂P', (Φ (h' ω)).1 = ζ' ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ' ω → (Φ (h' ω)).2 t = η' ω t := by
  obtain ⟨η, ζ, hfl⟩ := exists_isFlowLine_of_heights href hκ hκ4 hb hθ hh
  obtain ⟨Φ, hΦm, hΦ⟩ := exists_flowLineMap_of_heights href hκ hκ4 hb hθ
  have hΦη := hΦ P h hh η ζ hfl
  have hfl' : IsFlowLine κ b J 0 θ P h (fun ω => (Φ (h ω)).2) ζ :=
    IsFlowLine.congr_path hfl (hΦη.mono fun ω hω t ht => hω.2 t ht)
  refine ⟨Φ, ζ, hΦm, hfl', ?_, fun P' _ h' hh' η' ζ' hfl'' => hΦ P' h' hh' η' ζ' hfl''⟩
  filter_upwards [hΦη, IsFlowLine.ae_regular_of_heights hκ hκ4 hb hθ hfl'] with ω hω hreg
  exact ⟨hreg.1, hω.1.trans hreg.1, hreg.2⟩

/-! ### Large boundary values for the data of Figure 7.1 -/

/-- (4.4) at `θ` for the data `−a` on `ℝ₋`, `b` on `ℝ₊`: `a ≥ λ − πχ + θχ` and `b ≥ λ − θχ`. -/
theorem isHeightBounded44_prop74Data {a b' : ℝ} (ha : sleLambda κ - π * chiC κ + θ * chiC κ ≤ a)
    (hb' : sleLambda κ - θ * chiC κ ≤ b') : IsHeightBounded44 κ (prop74Data a b') {0} θ := by
  refine ⟨fun y hy _ => ?_, fun y hy _ => ?_⟩
  · simp only [prop74Data, hy, ↓reduceIte]
    linarith
  · simp only [prop74Data, not_lt.2 hy.le, ↓reduceIte]
    linarith

/-- (4.4) at every angle of `[θlo, θhi]` for `a ≥ λ − πχ + θhi χ`, `b ≥ λ − θlo χ` ("Choose the original boundary
values large enough", p. 477). -/
theorem isHeightBounded44_prop74Data_of_mem_Icc (hκ : 0 < κ) (hκ4 : κ < 4) {a b' θlo θhi : ℝ}
    (ha : sleLambda κ - π * chiC κ + θhi * chiC κ ≤ a) (hb' : sleLambda κ - θlo * chiC κ ≤ b')
    (hθ : θ ∈ Icc θlo θhi) : IsHeightBounded44 κ (prop74Data a b') {0} θ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have h1 : θ * chiC κ ≤ θhi * chiC κ := mul_le_mul_of_nonneg_right hθ.2 hχ.le
  have h2 : θlo * chiC κ ≤ θ * chiC κ := mul_le_mul_of_nonneg_right hθ.1 hχ.le
  exact isHeightBounded44_prop74Data (by linarith) (by linarith)

/-- The lowest angle of Theorem R.7's configuration: `min(θ_R, −π/2)` (the right arm and the certified right
frontier `β_R`). -/
def r7ThetaLo (k rL : ℝ) : ℝ := min (R7.thetaR k rL) (-(π / 2))

/-- The highest angle of Theorem R.7's configuration: `max(θ_L, π/2)` (the left arm and `β_L`). -/
def r7ThetaHi (k rR : ℝ) : ℝ := max (R7.thetaL k rR) (π / 2)

/-- The left boundary value `a` of Theorem R.7's field (data `−a` on `ℝ₋`), flow parameter `κ = 16/k`. -/
def r7A (k rR : ℝ) : ℝ := sleLambda (16 / k) - π * chiC (16 / k) + r7ThetaHi k rR * chiC (16 / k)

/-- The right boundary value `b` of Theorem R.7's field (data `b` on `ℝ₊`). -/
def r7B (k rL : ℝ) : ℝ := sleLambda (16 / k) - r7ThetaLo k rL * chiC (16 / k)

/-- **The R.7 data are non-boundary at every angle of `[min(θ_R, −π/2), max(θ_L, π/2)]`**: the two arms, the two
certified frontiers and every angle between them have (4.4) heights for `prop74Data (r7A k r_R + c) (r7B k r_L + c')`,
`c, c' ≥ 0`. -/
theorem isHeightBounded44_r7 {k rL rR : ℝ} (hk4 : 4 < k) {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hθ : θ ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR)) :
    IsHeightBounded44 (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} θ :=
  isHeightBounded44_prop74Data_of_mem_Icc (R7.sixteen_div_pos (by linarith)) (R7.sixteen_div_lt_four hk4)
    (by simp only [r7A]; linarith) (by simp only [r7B]; linarith) hθ

theorem neg_pi_div_two_mem_r7 (k rL rR : ℝ) : -(π / 2) ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR) :=
  ⟨min_le_right _ _, (by linarith [Real.pi_pos] : -(π / 2) ≤ π / 2).trans (le_max_right _ _)⟩

theorem pi_div_two_mem_r7 (k rL rR : ℝ) : π / 2 ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR) :=
  ⟨(min_le_right _ _).trans (by linarith [Real.pi_pos]), le_max_right _ _⟩

/-- The right arm's angle `θ_R` lies in the R.7 range (`θ_R < π/2`). -/
theorem thetaR_mem_r7 {k rL : ℝ} (rR : ℝ) (hk4 : 4 < k) (hL : -2 < rL) :
    R7.thetaR k rL ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR) :=
  ⟨min_le_left _ _, (R7.thetaR_lt_pi_div_two hk4 hL).le.trans (le_max_right _ _)⟩

/-- The left arm's angle `θ_L` lies in the R.7 range (`θ_L > −π/2`). -/
theorem thetaL_mem_r7 {k rR : ℝ} (rL : ℝ) (hk4 : 4 < k) (hR : -2 < rR) :
    R7.thetaL k rR ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR) :=
  ⟨(min_le_right _ _).trans (R7.neg_pi_div_two_lt_thetaL hk4 hR).le, le_max_left _ _⟩

end InteractingSLE.Sec7.R7Outer
