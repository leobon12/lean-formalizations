/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JointKernelProof
import InteractingSLE.Spec.Supplement.GW2JointKernelLaw

/-!
# GW2's pre-contact kernel with the specification's normalization of the joint-chart field

Packet PROVE-T14-TIP10. The chain-rule lift of `jointChart w s = R ∘ f_s ∘ R` is `arg ψ′ − 2π` (the constant `−2π` at
`s = 0`, `jointChart_zero_lift`), while the specification normalizes the joint-chart field by the inherited argument
that "starts at zero and stays zero" (GB9, p. 525). So the specification's joint-chart field is `h` read in
`jointChart` with the coefficients `1, 2πχ, χ` (offset `specOffset κ = 2πχ(κ)`); at `s = 0` it is `h` itself
(`isChartTransport_jointChart_zero_spec`), and its far heights are GB9's `−λ′ + πχ`, `λ′ − πχ` (at angle `0`).
`GW2JointKernelStatement` (PROVE-T14-TIP9) uses the offset `0` and is believed false (`GW2JointDetStatement`'s
docstring). This file states the corrected kernel and reduces it to its (Det) clause. The same normalization is used by
the landed cross-conditioning chart clause (`Sec5.CrossCond`: `cfChart` is `jointChart`, with "height shift `2πχ`") and
by CS3's counterflow-side heights `∓λ′(1 + S) ± πχ + θχ` (`Theorem14.CS3.cs3_rR_half_pi`, `cs3_rL_neg_half_pi`).

## Main results

* `specOffset`, `isChartTransport_add_const`, **`isChartTransport_jointChart_zero_spec`**;
* **`GW2JointKernelCStatement`** (named): `GW2JointKernelStatement` with the offset `specOffset κ`;
* **`GW2JointDetCStatement`** (named): its (Det) clause for the explicit word `jointWord (specOffset κ) κ c′ s W`;
* **`gw2JointKernelCStatement_of_detC`**: `GW2JointDetCStatement → GW2JointKernelCStatement` ((R1) is
  `exists_jointKernel_r1` at the offset `specOffset κ`);
* **`exists_condExpKernel_jointFlowLineC`**: PROVE-T14-TIP9's conditional-law form
  (`exists_condExpKernel_jointFlowLine`) from the corrected kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2JointKernel

open Restart Exist.StagedLaw Sec7.StripSysField Supp8.GB6

/-! ### The specification's offset -/

/-- **The offset of the specification's joint-chart field**: `2πχ(κ)`, compensating the `−2π` of the chain-rule lift
of `jointChart`. -/
def specOffset (κ : ℝ) : ℝ := 2 * Real.pi * QuantumZipper.chiC κ

/-- The constant of the returned word at the specification's offset is `−πχ(κ)`. -/
theorem retA_add_specOffset {κ : ℝ} (hκ : 0 < κ) : retA κ + specOffset κ = -(Real.pi * QuantumZipper.chiC κ) := by
  unfold retA specOffset
  rw [Sec4.chiC_sixteen_div hκ]
  ring

/-- Adding a constant to the transported field adds it to the offset. -/
theorem isChartTransport_add_const {c : Chart} {σ a k : ℝ} {h h' : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport c σ a k h h') (a₁ : ℝ) :
    IsChartTransport c σ (a + a₁) k h (h' + a₁ • Chart.oneDist) := by
  intro φ φ' hsupp hφ
  rw [add_apply, smul_apply, Chart.oneDist_apply, smul_eq_mul,
    ht φ φ' hsupp hφ]
  ring

/-- **At own time `0` the specification's joint-chart field is the field itself.** -/
theorem isChartTransport_jointChart_zero_spec {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (κ : ℝ)
    (h : DistOn upperHalfPlaneOpens) :
    IsChartTransport (jointChart w 0) 1 (specOffset κ) (QuantumZipper.chiC κ) h h := by
  have h1 := isChartTransport_add_const (isChartTransport_jointChart_zero hw hw0 (QuantumZipper.chiC κ) h)
    (2 * Real.pi * QuantumZipper.chiC κ)
  rw [zero_add, sub_add_cancel] at h1
  exact h1

/-! ### GB9's totals at the extreme angle -/

theorem sqrt_sixteen_div {κ : ℝ} (hκ : 0 < κ) : Real.sqrt (16 / κ) = 4 / Real.sqrt κ := by
  rw [Real.sqrt_div' _ hκ.le, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **GB9's totals from the specification's far heights** (p. 525: "At `θ = π/2` the total weights are
`(κ − 4, c_κ)`"): a flow line of angle `π/2` of a field with far heights `−λ′ + πχ` (left) and `λ′ − πχ` (right) has
left total `−(−λ′ + πχ + (π/2)χ)/λ − 1 = κ − 4` and right total `(λ′ − πχ + (π/2)χ)/λ − 1 = κ/2 − 2`. -/
theorem totals_specHeights {κ : ℝ} (hκ : 0 < κ) :
    -((-sleLambda (16 / κ) + Real.pi * QuantumZipper.chiC κ) + Real.pi / 2 * QuantumZipper.chiC κ) /
        sleLambda κ - 1 = κ - 4 ∧
      ((sleLambda (16 / κ) - Real.pi * QuantumZipper.chiC κ) + Real.pi / 2 * QuantumZipper.chiC κ) /
        sleLambda κ - 1 = κ / 2 - 2 := by
  unfold sleLambda QuantumZipper.chiC
  rw [sqrt_sixteen_div hκ]
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ κ = r ^ 2 := ⟨Real.sqrt κ, Real.sqrt_pos.2 hκ, (Real.sq_sqrt hκ.le).symm⟩
  rw [Real.sqrt_sq hr.le]
  have hπ : 0 < Real.pi := Real.pi_pos
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **With the offset `0` of `GW2JointKernelStatement` the totals are wrong**: its field is the specification's minus
`2πχ`, so its far heights are `−λ′ − πχ` and `λ′ − 3πχ`, and the angle-`π/2` totals are `0` and `3κ/2 − 6` instead of
`κ − 4` and `κ/2 − 2`. -/
theorem totals_offsetZeroHeights {κ : ℝ} (hκ : 0 < κ) :
    -((-sleLambda (16 / κ) - Real.pi * QuantumZipper.chiC κ) + Real.pi / 2 * QuantumZipper.chiC κ) /
        sleLambda κ - 1 = 0 ∧
      ((sleLambda (16 / κ) - 3 * (Real.pi * QuantumZipper.chiC κ)) + Real.pi / 2 * QuantumZipper.chiC κ) /
        sleLambda κ - 1 = 3 * κ / 2 - 6 := by
  unfold sleLambda QuantumZipper.chiC
  rw [sqrt_sixteen_div hκ]
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ κ = r ^ 2 := ⟨Real.sqrt κ, Real.sqrt_pos.2 hκ, (Real.sq_sqrt hκ.le).symm⟩
  rw [Real.sqrt_sq hr.le]
  have hπ : 0 < Real.pi := Real.pi_pos
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-! ### The corrected kernel and its (Det) clause -/

/-- **Named input: GB9's pre-contact kernel at a counterflow stop, with the specification's joint-chart field**
(`GW2JointKernelStatement` with the field read in `jointChart` with the coefficients `1, specOffset κ, χ` instead of
`1, 0, χ`; everything else verbatim). -/
def GW2JointKernelCStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (QuantumZipper.chiC κ)
        (h ω) (Hc ω)) →
    ∀ F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞,
      IsCanonicalDriverCode κ θ F →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted ∧ IsGoodDrvCode (F (β ω, Hc ω))) ∧
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ) ∧
      ∀ᵐ ω ∂P, γ ω s ∈ H →
        ω ∈ M ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => (α ω t : OnePoint ℂ))
            ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (β ω, Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t) =
            relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t

/-- **Named input: the (Det) clause of the corrected pre-contact kernel** (`GW2JointDetStatement` with the
specification's joint-chart field, offset `specOffset κ`, and the corresponding explicit word
`jointWord (specOffset κ) κ c′ s W`). Its obstruction is the one recorded at `GW2JointDetStatement`: the two-curve
conditional law at a general angle and flow-line locality up to the first contact. -/
def GW2JointDetCStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (QuantumZipper.chiC κ)
        (h ω) (Hc ω)) →
    ∀ F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞,
      IsCanonicalDriverCode κ θ F →
    ∀ c' : BoundaryWord, c'.jumps = J' → (∀ y ∉ J', c'.fn y = b' y) →
      ∀ᵐ ω ∂P, γ ω s ∈ H →
        IsGoodDrvCode (F (jointWord (specOffset κ) κ c' s (fun t => W t ω), Hc ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => (α ω t : OnePoint ℂ))
            ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull
              (fun r : ℝ => drvDec (F (jointWord (specOffset κ) κ c' s (fun t => W t ω), Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t) =
            relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t

/-- **The corrected pre-contact kernel from its (Det) clause.** -/
theorem gw2JointKernelCStatement_of_detC (hD : GW2JointDetCStatement.{u}) : GW2JointKernelCStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα s Hc
    hHcm hHc F hF
  obtain ⟨c', hc'J, hc'b⟩ := BoundaryWord.exists_fn_eq hb'
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hreg.mono fun ω hω => hω.1
  have hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := hreg.mono fun ω hω => hω.2.1
  obtain ⟨𝒢, M, β, hM, hβ, hsort, hR1, hev⟩ :=
    exists_jointKernel_r1 hκ (specOffset κ) hh.1 hb' hT hcf hζ hγ s hHcm hHc hc'b
  have hDω := hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα
    s Hc hHcm hHc F hF c' hc'J hc'b
  refine ⟨𝒢, M, β, hM, hβ, ?_, hR1, ?_⟩
  · filter_upwards [hev, hDω] with ω hevω hDω hωM
    refine ⟨hsort ω, ?_⟩
    rw [hevω.2]
    exact (hDω (hevω.1.2 hωM)).1
  · filter_upwards [hev, hDω] with ω hevω hDω hsH
    refine ⟨hevω.1.1 hsH, ?_⟩
    rw [hevω.2]
    exact (hDω hsH).2

/-- **The corrected pre-contact kernel in conditional-law form**: PROVE-T14-TIP9's `exists_condExpKernel_jointFlowLine`
(same proof) from `GW2JointKernelCStatement`, for the specification's joint-chart field (offset `specOffset κ`). -/
theorem exists_condExpKernel_jointFlowLineC (hD : GW2JointKernelCStatement.{u}) {κ θ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {b : ℝ → ℝ} {J : Finset ℝ} {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {b' : ℝ → ℝ}
    {J' : Finset ℝ} {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
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
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0)
    {Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (QuantumZipper.chiC κ)
        (h ω) (Hc ω))
    {F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ M → (β ω₀).IsSorted ∧
        (condExpKernel P 𝒢.1 ω₀).map (fun ω => (Hc ω, F (β ω, Hc ω))) =
          (β ω₀).gffLaw.map (fun g => (g, F (β ω₀, g))) ∧
        IsFlowLineDriver κ (β ω₀).fn (β ω₀).jumps θ (β ω₀).gffLaw id
          (fun t g => drvDec (F (β ω₀, g)) t) (fun g => (F (β ω₀, g)).2)) ∧
      ∀ᵐ ω ∂P, γ ω s ∈ H →
        ω ∈ M ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => (α ω t : OnePoint ℂ))
            ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (β ω, Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t) =
            relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t := by
  obtain ⟨𝒢, M, β, hM, hβ, hword, hR1, hdet⟩ :=
    hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P inferInstance h b J W Wα ζ ζα γ α b' J' h' hb hG hb' htr hcf hadmL hadmR hcomp
      hfl hα s Hc hHcm hHc F hF
  refine ⟨𝒢, M, β, hM, hβ, ?_, hdet⟩
  have hβm : Measurable β := hβ.mono 𝒢.2 le_rfl
  have hpair := ae_map_condExpKernel_pair_eq (P := P) 𝒢.2 hβ hHcm hR1 hF.1
  -- the sorted word and the good code, carried to almost every conditional law
  have hgoodK : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀), ω ∈ M → (β ω).IsSorted ∧
      IsGoodDrvCode (F (β ω, Hc ω)) :=
    Sec7.Aux122Disint.ae_ae_condExpKernel 𝒢.2 hword
  filter_upwards [hpair, hgoodK, Sec7.Aux122Disint.ae_ae_condExpKernel_mem 𝒢.2 hM,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq 𝒢.2 hβ, hword] with ω₀ hp hgω₀ hMω₀ hβeq hw₀ hω₀M
  have hsort : (β ω₀).IsSorted := (hw₀ hω₀M).1
  refine ⟨hsort, hp hω₀M, isFlowLineDriver_gffLaw hF hsort ?_⟩
  -- the good code under the word's GFF law, pushed forward from the conditional law
  have hFc : Measurable fun g : DistOn upperHalfPlaneOpens => F (β ω₀, g) :=
    hF.1.comp (measurable_const.prodMk measurable_id)
  have hmeas : MeasurableSet {g : DistOn upperHalfPlaneOpens | IsGoodDrvCode (F (β ω₀, g))} :=
    hFc measurableSet_isGoodDrvCode
  have hmap : (condExpKernel P 𝒢.1 ω₀).map Hc = (β ω₀).gffLaw := by
    have h1 : ((condExpKernel P 𝒢.1 ω₀).map (fun ω => (Hc ω, F (β ω, Hc ω)))).map Prod.fst =
        ((β ω₀).gffLaw.map (fun g => (g, F (β ω₀, g)))).map Prod.fst := by
      rw [hp hω₀M]
    have hm1 : Measurable fun ω => (Hc ω, F (β ω, Hc ω)) := hHcm.prodMk (hF.1.comp (hβm.prodMk hHcm))
    have hm2 : Measurable fun g : DistOn upperHalfPlaneOpens => (g, F (β ω₀, g)) := measurable_id.prodMk hFc
    rw [Measure.map_map measurable_fst hm1, Measure.map_map measurable_fst hm2] at h1
    have e1 : (Prod.fst ∘ fun ω => (Hc ω, F (β ω, Hc ω))) = Hc := rfl
    have e2 : (Prod.fst ∘ fun g : DistOn upperHalfPlaneOpens => (g, F (β ω₀, g))) = id := rfl
    rw [e1, e2, Measure.map_id] at h1
    exact h1
  rw [← hmap, ae_map_iff hHcm.aemeasurable hmeas]
  filter_upwards [hgω₀, hMω₀ hω₀M, hβeq] with ω hω hωM hωβ
  have h2 := (hω hωM).2
  rwa [hωβ] at h2

end GW2JointKernel

end Theorem14

end InteractingSLE
