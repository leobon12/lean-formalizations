import QuantumZipper.Proofs.Thm18.G2AgreeMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 identification nodes: the outside coordinates are D3⁺-conditioning measurable

The conditioning nodes `G2RootXCondStmt`, `G2RootRCondStmt` (`G2AgreeMain.lean`) ask for a map
`V`, measurable for `condSigma (palmCField X₀ x) (κ/2)` (the free field outside `B(x, κ/2)`),
a.s. equal to the conditioning variables. This file proves the part coming from the outside
coordinates `outMap i (X₀ + ψ_x)`:

* `measurable_outMap_xPalm`: if `B(x, κ/2)` lies in one of the two excluded discs, the outside
  coordinates of the Palm field are `condSigma`-measurable (every out-pair `(μ₁, μ₂)` is the
  translate by `x` of a balanced admissible pair giving no mass to `B(0, κ/2)`, and the Palm
  shift `ψ_x` only adds a deterministic constant);
* `g2RootXCondStmt_of_cutLoc`, `g2RootRCondStmt_of_loc`: the conditioning nodes from the
  remaining **locality of the boundary length** nodes `G2RootXCutLocStmt` (the cut length
  `ν_h[x + κ, 0]`) and `G2RootRCutLocStmt` (the cut length `ν_h[0, y − κ]` and the truncation
  mass `g3MassP`).

Sources: Sheffield, arXiv:1012.4797, proof of Prop. 5.5 (p. 65: the length `ν_h[x + κ, 0]` is a
function of the field outside `B_κ(x)`). Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw

local notation "Ω₀" => gffBase.Ω

/-! ## Outside coordinates -/

/-- **The outside coordinates of the Palm field are `condSigma`-measurable** when
`B(x, κ/2) ⊆ B(t₁, r₁) ∪ B(t₂, r₂)`. -/
theorem measurable_outMap_xPalm (γ : ℝ) (i : G3Idx) {κ x : ℝ}
    (hsub : ball (x : ℂ) (κ / 2) ⊆ ball (i.t₁ : ℂ) i.r₁ ∪ ball (i.t₂ : ℂ) i.r₂) :
    Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X x) (κ / 2)]
      fun ω => outMap i (xPalm γ x ω) := by
  refine (@measurable_pi_iff Ω₀ _ (fun _ => ℝ)
    (D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X x) (κ / 2)) _ _).2 fun p => ?_
  have hnull : ∀ ν : Measure ℂ, ν (ball (i.t₁ : ℂ) i.r₁ ∪ ball (i.t₂ : ℂ) i.r₂) = 0 →
      ν.map (· + ((-x : ℝ) : ℂ)) (ball ((0 : ℝ) : ℂ) (κ / 2)) = 0 := by
    intro ν hν
    rw [Measure.map_apply (measurable_add_const _) measurableSet_ball]
    refine measure_mono_null (fun z hz => hsub ?_) hν
    rw [mem_preimage, mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    have e : z - (x : ℂ) = z + ((-x : ℝ) : ℂ) - ((0 : ℝ) : ℂ) := by push_cast; ring
    rwa [e]
  set q : K3.OutIdx 0 (κ / 2) :=
    ⟨(p.1.1.map (· + ((-x : ℝ) : ℂ)), p.1.2.map (· + ((-x : ℝ) : ℂ))),
      isAdmissibleH_map_add_real p.2.1 (-x), isAdmissibleH_map_add_real p.2.2.1 (-x),
      by rw [map_add_real_univ, map_add_real_univ]; exact p.2.2.2.1,
      hnull _ p.2.2.2.2.1, hnull _ p.2.2.2.2.2⟩ with hq
  have hf : Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X x) (κ / 2)]
      fun ω => palmCField gffBase.X x ω q.1.1 - palmCField gffBase.X x ω q.1.2 := by
    rw [measurable_iff_comap_le]
    exact (le_iSup (fun q' : K3.OutIdx 0 (κ / 2) => MeasurableSpace.comap
      (fun ω => palmCField gffBase.X x ω q'.1.1 - palmCField gffBase.X x ω q'.1.2)
        inferInstance) q).trans le_sup_right
  have e : (fun ω => outMap i (xPalm γ x ω) p) = fun ω =>
      (palmCField gffBase.X x ω q.1.1 - palmCField gffBase.X x ω q.1.2) +
        (ofFun (g2PalmPsi γ x) p.1.1 - ofFun (g2PalmPsi γ x) p.1.2) := by
    funext ω
    rw [hq]
    simp only [outMap, xPalm, Pi.add_apply]
    rw [show palmCField gffBase.X x ω (p.1.1.map (· + ((-x : ℝ) : ℂ))) = gffBase.X ω p.1.1 from
      palmCField_rho gffBase.X p.1.1 x ω,
      show palmCField gffBase.X x ω (p.1.2.map (· + ((-x : ℝ) : ℂ))) = gffBase.X ω p.1.2 from
      palmCField_rho gffBase.X p.1.2 x ω]
    ring
  rw [e]
  exact hf.add measurable_const

/-! ## The remaining locality nodes -/

/-- **Locality of the cut length, `x` side** (Sheffield, arXiv:1012.4797, proof of Prop. 5.5,
p. 65: `ν_h[x + κ, 0]` is determined by the field outside `B_κ(x)`). -/
def G2RootXCutLocStmt (γ : ℝ) : Prop :=
  ∀ (i : G3Idx) (m κ x : ℝ), 0 < κ → κ < m → |x - i.t₁| + m < i.r₁ →
    ∃ W : Ω₀ → ℝ,
      Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X x) (κ / 2)] W ∧
      ∀ᵐ ω ∂gffBase.P,
        W ω = (qBoundaryMeasure γ (normField γ (xPalm γ x) ω) (Icc (x + κ) 0)).toReal

/-- **Locality of the cut length and of the truncation mass, `R` side.** -/
def G2RootRCutLocStmt (γ : ℝ) : Prop :=
  ∀ (i : G3Idx) (m κ y : ℝ), 0 < κ → κ < m → |y - i.t₂| + m < i.r₂ →
    ∃ W : Ω₀ → ℝ × ℝ≥0∞,
      Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X y) (κ / 2)] W ∧
      ∀ᵐ ω ∂gffBase.P,
        W ω = ((qBoundaryMeasure γ (normField γ (xPalm γ y) ω) (Icc 0 (y - κ))).toReal,
          g3MassP γ i y ω)

theorem ball_half_subset_of {t r m κ x : ℝ} (hκ : 0 < κ) (hκm : κ < m) (h : |x - t| + m < r) :
    ball (x : ℂ) (κ / 2) ⊆ ball (t : ℂ) r := by
  intro z hz
  rw [mem_ball, dist_eq_norm] at hz ⊢
  have hxt : ‖(x : ℂ) - (t : ℂ)‖ = |x - t| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc ‖z - (t : ℂ)‖ = ‖(z - x) + ((x : ℂ) - t)‖ := by ring_nf
    _ ≤ ‖z - x‖ + ‖(x : ℂ) - t‖ := norm_add_le _ _
    _ < r := by rw [hxt]; linarith

/-- **`G2RootXCondStmt` from the cut-length locality node.** -/
theorem g2RootXCondStmt_of_cutLoc {γ : ℝ} (h : G2RootXCutLocStmt γ) : G2RootXCondStmt γ := by
  intro i m κ x hκ hκm hx
  obtain ⟨W, hWm, hWae⟩ := h i m κ x hκ hκm hx
  refine ⟨fun ω => (outMap i (xPalm γ x ω), W ω),
    (measurable_outMap_xPalm γ i ((ball_half_subset_of hκ hκm hx).trans
      subset_union_left)).prodMk hWm, hWae.mono fun ω hω => ?_⟩
  simp only [g3PalmCond, hω]

/-- **`G2RootRCondStmt` from the cut-length/mass locality node.** -/
theorem g2RootRCondStmt_of_loc {γ : ℝ} (h : G2RootRCutLocStmt γ) : G2RootRCondStmt γ := by
  intro i m κ y hκ hκm hy
  obtain ⟨W, hWm, hWae⟩ := h i m κ y hκ hκm hy
  refine ⟨fun ω => (outMap i (xPalm γ y ω), W ω),
    (measurable_outMap_xPalm γ i ((ball_half_subset_of hκ hκm hy).trans
      subset_union_right)).prodMk hWm, hWae.mono fun ω hω => ?_⟩
  simp only [g3PalmCondR, hω]

/-- **`G2FixMixStmt` from D3⁺(i) (N2 form), the Palm identities, the length smoothing, the
regularity/goodness node and the two boundary-length locality nodes.** -/
theorem g2FixMixStmt_of_locLeaves {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hPX : G2RootXPalmIdStmt γ) (hSX : G2RootXLenSmoothStmt γ)
    (hPR : G2RootRPalmIdStmt γ) (hSR : G2RootRLenSmoothStmt γ)
    (hRG : G2PalmRegGoodStmt γ) (hLX : G2RootXCutLocStmt γ) (hLR : G2RootRCutLocStmt γ) :
    G2FixMixStmt γ :=
  g2FixMixStmt_of_agreeLeaves hγ hγ2 hN2 hPX hSX hPR hSR hRG (g2RootXCondStmt_of_cutLoc hLX)
    (g2RootRCondStmt_of_loc hLR)

end Thm18Asm
end QuantumZipper
