import QuantumZipper.Proofs.Thm18.G2AgreeReg
import QuantumZipper.Proofs.Zipper.D3PlusN1Model

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 identification nodes: the truncation mass is D3⁺-conditioning measurable

On the `R` side the conditioning variables also contain the truncation mass `g3MassP γ i y`
(the boundary mass of `[−δ, 0]` read from the region-1 field and the gap field of the Palm field
at `y`). Both fields only read `h_y = normField γ (X₀ + ψ_y)` at folded circles giving no mass to
`B(y, κ/2) ⊆ B(t₂, r₂)`, and at such a probability measure `μ`, `h_y(μ)` is the balanced
increment `X₀(μ) − X₀(S)` plus a deterministic constant (`S = refS` gives no mass to the unit
disc). Hence (`measurable_g3MassP`) `g3MassP γ i y` is **exactly** measurable for
`condSigma (palmCField X₀ y) (κ/2)`, and the `R`-side locality node reduces to the cut length
alone (`g2RootRCutLocStmt_of_len`), symmetric to the `x` side.

`g2FixMixStmt_of_finalLeaves`: `G2FixMixStmt γ` from D3⁺(i) (N2 form), the Palm identities, the
length smoothing, the goodness of the Palm field (`G2PalmGoodStmt`) and the two cut-length
locality nodes (`G2RootXCutLocStmt`, `G2RootRCutLenLocStmt`).

Sources: Sheffield, arXiv:1012.4797, proof of Prop. 5.5 (p. 65) and of Thm. 1.8 (p. 71).
Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw

local notation "Ω₀" => gffBase.Ω

/-- Balanced increments of the free field at measures giving no mass to `B(x, κ/2)` are
`condSigma`-measurable. -/
theorem measurable_X_sub_of_null {x κ : ℝ} {μ₁ μ₂ : Measure ℂ} (h₁ : IsAdmissibleH μ₁)
    (h₂ : IsAdmissibleH μ₂) (hm : μ₁ univ = μ₂ univ) (n₁ : μ₁ (ball (x : ℂ) (κ / 2)) = 0)
    (n₂ : μ₂ (ball (x : ℂ) (κ / 2)) = 0) :
    Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X x) (κ / 2)]
      fun ω => gffBase.X ω μ₁ - gffBase.X ω μ₂ := by
  have hnull : ∀ ν : Measure ℂ, ν (ball (x : ℂ) (κ / 2)) = 0 →
      ν.map (· + ((-x : ℝ) : ℂ)) (ball ((0 : ℝ) : ℂ) (κ / 2)) = 0 := by
    intro ν hν
    rw [Measure.map_apply (measurable_add_const _) measurableSet_ball]
    refine measure_mono_null (fun z hz => ?_) hν
    rw [mem_preimage, mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    have e : z - (x : ℂ) = z + ((-x : ℝ) : ℂ) - ((0 : ℝ) : ℂ) := by push_cast; ring
    rwa [e]
  set q : K3.OutIdx 0 (κ / 2) :=
    ⟨(μ₁.map (· + ((-x : ℝ) : ℂ)), μ₂.map (· + ((-x : ℝ) : ℂ))),
      isAdmissibleH_map_add_real h₁ (-x), isAdmissibleH_map_add_real h₂ (-x),
      by rw [map_add_real_univ, map_add_real_univ]; exact hm, hnull _ n₁, hnull _ n₂⟩ with hq
  have hf : Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X x) (κ / 2)]
      fun ω => palmCField gffBase.X x ω q.1.1 - palmCField gffBase.X x ω q.1.2 := by
    rw [measurable_iff_comap_le]
    exact (le_iSup (fun q' : K3.OutIdx 0 (κ / 2) => MeasurableSpace.comap
      (fun ω => palmCField gffBase.X x ω q'.1.1 - palmCField gffBase.X x ω q'.1.2)
        inferInstance) q).trans le_sup_right
  have e : (fun ω => gffBase.X ω μ₁ - gffBase.X ω μ₂) =
      fun ω => palmCField gffBase.X x ω q.1.1 - palmCField gffBase.X x ω q.1.2 := by
    funext ω
    rw [hq]
    exact congrArg₂ (· - ·) (palmCField_rho gffBase.X μ₁ x ω).symm
      (palmCField_rho gffBase.X μ₂ x ω).symm
  rw [e]
  exact hf

/-- The Palm field at a probability measure avoiding `B(y, κ/2)` is `condSigma`-measurable. -/
theorem measurable_normField_xPalm_apply (γ : ℝ) {y κ : ℝ} {μ : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hm : μ univ = 1) (hn : μ (ball (y : ℂ) (κ / 2)) = 0)
    (hS : refS (ball (y : ℂ) (κ / 2)) = 0) :
    Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X y) (κ / 2)]
      fun ω => normField γ (xPalm γ y) ω μ := by
  have hf := measurable_X_sub_of_null (x := y) (κ := κ) hμ (D3Plus.isAdmissibleH_foldedCircle' 0
    one_pos) (by rw [hm, measure_univ]) hn hS
  have e : (fun ω => normField γ (xPalm γ y) ω μ) = fun ω =>
      (gffBase.X ω μ - gffBase.X ω refS) +
        (ofFun (h0rev (γ ^ 2)) μ + ofFun (g2PalmPsi γ y) μ - ofFun (g2PalmPsi γ y) refS) := by
    funext ω
    simp only [normField, xPalm, Pi.add_apply]
    ring
  rw [e]
  exact hf.add measurable_const

theorem measurable_restrictField_of {m : MeasurableSpace Ω₀} (A : Set (Measure ℂ))
    {F : Ω₀ → FieldSample} (hF : ∀ μ ∈ A, Measurable[m] fun ω => F ω μ) :
    Measurable[m] fun ω => restrictField A (F ω) := by
  classical
  refine (@measurable_pi_iff Ω₀ _ (fun _ => ℝ) m _ _).2 fun μ => ?_
  by_cases h : μ ∈ A
  · simp only [restrictField, h, if_true]
    exact hF μ h
  · simp only [restrictField, h, if_false]
    exact measurable_const

/-- **The truncation mass is `condSigma`-measurable.** -/
theorem measurable_g3MassP (γ : ℝ) (i : G3Idx) {m κ y : ℝ} (hκ : 0 < κ) (hκm : κ < m)
    (hy : |y - i.t₂| + m < i.r₂) :
    Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X y) (κ / 2)]
      (g3MassP γ i y) := by
  have hB : ball (y : ℂ) (κ / 2) ⊆ ball (i.t₂ : ℂ) i.r₂ := ball_half_subset_of hκ hκm hy
  have hS : refS (ball (y : ℂ) (κ / 2)) = 0 := by
    refine measure_mono_null (hB.trans fun z hz => ?_)
      (LateralGerm.foldedCircle_ball_eq_zero (s := 1) (δ := 1) one_pos le_rfl)
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right]
    have h2 := i.inUnit₂
    have hn : ‖(i.t₂ : ℂ)‖ = |i.t₂| := by rw [Complex.norm_real, Real.norm_eq_abs]
    calc ‖z‖ = ‖(z - i.t₂) + (i.t₂ : ℂ)‖ := by ring_nf
      _ ≤ ‖z - i.t₂‖ + ‖(i.t₂ : ℂ)‖ := norm_add_le _ _
      _ < 1 := by rw [hn]; linarith
  have hA : Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X y) (κ / 2)]
      fun ω => regionField γ i.t₁ i.r₁ (xPalm γ y) ω := by
    refine measurable_restrictField_of _ fun μ hμ => ?_
    obtain ⟨d, ρ, hρ, rfl, r', hr', hsupp⟩ := hμ
    refine measurable_normField_xPalm_apply γ (D3Plus.isAdmissibleH_foldedCircle' d hρ)
      measure_univ (measure_mono_null (show ball (y : ℂ) (κ / 2) ⊆ (closedBall (i.t₁ : ℂ) r')ᶜ
      from fun z hz hz' => ?_) hsupp) hS
    have h1 := hB hz
    rw [mem_ball] at h1
    rw [mem_closedBall] at hz'
    have hd := i.dist_le
    have := dist_triangle (i.t₁ : ℂ) z (i.t₂ : ℂ)
    rw [dist_comm] at hz'
    linarith
  have hG : Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X y) (κ / 2)]
      fun ω => gapField γ i.t₁ i.r₁ i.t₂ i.r₂ (xPalm γ y) ω := by
    refine measurable_restrictField_of _ fun μ hμ => ?_
    obtain ⟨d, ρ, hρ, rfl, hnull⟩ := hμ
    exact measurable_normField_xPalm_apply γ (D3Plus.isAdmissibleH_foldedCircle' d hρ)
      measure_univ (measure_mono_null (hB.trans subset_union_right) hnull) hS
  have e : g3MassP γ i y = fun ω =>
      bdryM γ (regionField γ i.t₁ i.r₁ (xPalm γ y) ω) (Icc (-i.δ) 0) +
        bdryM γ (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ (xPalm γ y) ω) (Icc (-i.δ) 0) := by
    funext ω
    rw [g3MassP, Measure.add_apply]
  rw [e]
  exact ((Measure.measurable_coe measurableSet_Icc).comp ((measurable_bdryM γ).comp hA)).add
    ((Measure.measurable_coe measurableSet_Icc).comp ((measurable_bdryM γ).comp hG))

/-- **Locality of the cut length, `R` side** (Sheffield, arXiv:1012.4797, proof of Prop. 5.5,
p. 65, mirrored: `ν_h[0, y − κ]` is determined by the field outside `B_κ(y)`). -/
def G2RootRCutLenLocStmt (γ : ℝ) : Prop :=
  ∀ (i : G3Idx) (m κ y : ℝ), 0 < κ → κ < m → |y - i.t₂| + m < i.r₂ →
    ∃ W : Ω₀ → ℝ,
      Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X y) (κ / 2)] W ∧
      ∀ᵐ ω ∂gffBase.P,
        W ω = (qBoundaryMeasure γ (normField γ (xPalm γ y) ω) (Icc 0 (y - κ))).toReal

theorem g2RootRCutLocStmt_of_len {γ : ℝ} (h : G2RootRCutLenLocStmt γ) : G2RootRCutLocStmt γ := by
  intro i m κ y hκ hκm hy
  obtain ⟨W, hWm, hWae⟩ := h i m κ y hκ hκm hy
  exact ⟨fun ω => (W ω, g3MassP γ i y ω), hWm.prodMk (measurable_g3MassP γ i hκ hκm hy),
    hWae.mono fun ω hω => by simp only [hω]⟩

/-- **`G2FixMixStmt` from D3⁺(i) (N2 form), the Palm identities, the length smoothing, the
goodness of the Palm field and the two cut-length locality nodes.** -/
theorem g2FixMixStmt_of_finalLeaves {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hPX : G2RootXPalmIdStmt γ) (hSX : G2RootXLenSmoothStmt γ)
    (hPR : G2RootRPalmIdStmt γ) (hSR : G2RootRLenSmoothStmt γ)
    (hG : G2PalmGoodStmt γ) (hLX : G2RootXCutLocStmt γ) (hLR : G2RootRCutLenLocStmt γ) :
    G2FixMixStmt γ :=
  g2FixMixStmt_of_goodLeaves hγ hγ2 hN2 hPX hSX hPR hSR hG hLX (g2RootRCutLocStmt_of_len hLR)

end Thm18Asm
end QuantumZipper
