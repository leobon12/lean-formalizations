/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCIFirstContact
import InteractingSLE.Spec.Supplement.RLCIOrderGlue
import InteractingSLE.Spec.Supplement.RLCCMain

/-!
# Lemma G2a's order (Theorem 1.5, supplement §7.2)

Packet PROVE-RLC-I. Source: Lemma G2a and the proof of Lemma G2 (supplement pp. 490–492,
`source/spec/p481-528.md#id-G2`–`#id-G2a-proof`): "The higher-angle curve `α̂₂` lies to the left of `α̂₁` in closed
Jordan-side order. This assertion uses only the independent finite-force continuity theorem, the already established
common first-contact theorem, and the exact-two-height order of Aux. lemma 94"; G2a: "At their common first contact,
the elementary filling fact removes every middle mark. The remaining proof of G2 is unchanged."

`RLC.G2aReferenceStatement` (PROVE-RLC-C) asserts, for the two reference flow lines of G2a, complete lifetimes,
properness and simplicity (`IsProperCompletion`), the order and opposite-seed avoidance. Here it is split into
`G2aOrderStatement` (the order) and `G2aPartsStatement` (the rest; PROVE-RLC-H), and the order is proved from the parts:

* `ae_range_subset_closedLeftSide_of_exterior`: for two complete proper flow lines from `x₂ < x₁` (angles `θ₂ > θ₁`)
  of a GFF whose finite datum has its marks in `[x₂, x₁]` and the exterior heights of (TH2), each missing the other's
  seed, almost surely the higher-angle curve is in the closed left side of the other. Without a common point this is
  the seed order (`range_subset_leftSide_of_disjoint`); otherwise Lemma 7.7 gives the first contact, the first-contact
  kernel in G2's form (`exists_firstContactKernel_twoHeight`) gives a datum with the (TH2) mean, Aux. lemma 94 with
  Proposition 5.5 (`aux94_twoHeight_reference`) orders the conditional continuations under the kernel, the order is
  transferred to the actual chart continuations through the disintegration (Borel event `twoHeightGood`), and the
  gluing (`range_subset_closedLeftSide_glue`) returns to the physical curves;
* **`g2aOrderStatement_of_parts`** (G2a's order), **`g2aReferenceStatement_of_parts_order`** (G2a = order + parts) and
  **`g2aReferenceStatement_of_parts`**.

Named inputs: Lemmas 7.5 and 7.7 (`Theorem15.Lemma75Statement`, `Supp10.Lemma77Statement`), the first-contact word
kernel (`Restart.FirstContactWordKernelStatement`), the half-plane Proposition 5.5
(`Sec7.Lemma71H.Prop55HalfPlaneStatement`, at universe `0` for the canonical restart space) and G2a's other parts
(`G2aPartsStatement`). All serve Theorem 1.5 only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real

open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace RLC

open Restart Supp9B
open Sec5.Prop55Half (IsSeedProper)

/-! ### The order for data with the marks between the seeds -/

section Order

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The closed-side order of two complete reference flow lines whose data has its marks between the seeds** (proof of
Lemma G2, supplement p. 491, for the G2a data). -/
theorem ae_range_subset_closedLeftSide_of_exterior (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hW : FirstContactWordKernelStatement.{u})
    (h55 : Sec7.Lemma71H.Prop55HalfPlaneStatement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂)
    (hJ : ∀ y ∈ jumps, x₂ ≤ y ∧ y ≤ x₁) (hbL : ∀ y < x₂, b y = -sleLambda κ - θ₂ * chiC κ)
    (hbR : ∀ y, x₁ < y → b y = sleLambda κ - θ₁ * chiC κ)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hparts : ∀ᵐ ω ∂P, ζ₁ ω = ⊤ ∧ ζ₂ ω = ⊤ ∧ IsProperCompletion (η₁ ω) 0 (η₁ ω) ∧
      IsProperCompletion (η₂ ω) 0 (η₂ ω) ∧ (x₂ : ℂ) ∉ range (η₁ ω) ∧ (x₁ : ℂ) ∉ range (η₂ ω)) :
    ∀ᵐ ω ∂P, range (η₂ ω) ⊆ closedLeftSide (η₁ ω) := by
  have hθ' : θ₁ < θ₂ + Real.pi := lt_trans hθ (lt_add_of_pos_right _ Real.pi_pos)
  obtain ⟨M, β, Hc, γ₁, γ₂, U₁, U₂, E, mE, Y, K, hMm, hβm, hHc, m₁, m₂, mU₁, mU₂, hY, hcont₁, hcont₂, hK, hlaw,
    hfl, hpath⟩ := exists_firstContactKernel_twoHeight hL75 hL77 hW hκ hκ4 hb hx hθ' hJ hbL hbR hh hη₁ hη₂
  have : IsMarkovKernel K := hK
  set X : Ω → RestartSpace × E := fun ω => (RestartSpace.mk' (Hc ω) (γ₁ ω) (U₁ ω) (γ₂ ω) (U₂ ω), Y ω) with hXdef
  have hXm : Measurable X := (RestartSpace.measurable_mk' hHc m₁ m₂ mU₁ mU₂).prodMk hY
  -- Aux. lemma 94 with Proposition 5.5 under the kernel, for every datum with the (TH2) mean
  have hker : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c),
      c ∈ twoHeightSet κ θ₁ θ₂ → s ∈ twoHeightGood E := by
    filter_upwards [hfl] with c ⟨hgff, h1, h2⟩
    by_cases hc : c ∈ twoHeightSet κ θ₁ θ₂
    · filter_upwards [aux94_twoHeight_reference h55 hκ hκ4 hθ hc (K c) (fun s => s.1.field)
        (fun s => s.1.path₁) (fun s => s.1.path₂) (fun s => s.1.life₁) (fun s => s.1.life₂) hgff h1 h2]
        with s ⟨hl₁, hl₂, hp₁, hp₂, ho⟩ _
      exact mem_twoHeightGood hl₁ hl₂ hp₁ hp₂ ho
    · exact Eventually.of_forall fun s hc' => absurd hc' hc
  have hset : MeasurableSet {p : BoundaryWord × (RestartSpace × E) |
      p.1 ∈ twoHeightSet κ θ₁ θ₂ → p.2 ∈ twoHeightGood E} :=
    measurableSet_setOfPred.mpr
      ((measurableSet_setOfPred.mp (measurable_fst (measurableSet_twoHeightSet κ θ₁ θ₂))).imp
        (measurableSet_setOfPred.mp (measurable_snd (measurableSet_twoHeightGood E))))
  have hcp := Measure.ae_compProd_of_ae_ae hset hker
  rw [← hlaw] at hcp
  have htr : ∀ᵐ ω ∂P.restrict M, β ω ∈ twoHeightSet κ θ₁ θ₂ → X ω ∈ twoHeightGood E :=
    (ae_map_iff (hβm.prodMk hXm).aemeasurable hset).1 hcp
  rw [ae_restrict_iff' hMm] at htr
  -- pathwise
  filter_upwards [htr, hpath, hparts, hL77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ' P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    Supp10.ae_apply_zero_of_isFlowLine hη₁, Supp10.ae_apply_zero_of_isFlowLine hη₂] with
    ω htrω hpω ⟨hζ₁, hζ₂, hp₁, hp₂, hx₂, hx₁⟩ h77 h0₁ h0₂
  have hα₁ : IsProperCurve (η₁ ω) := isProperCurve_of_isProperCompletion hp₁
  have hc₂ : Continuous (η₂ ω) := hp₂.1
  have hα₂ : ∀ t, 0 ≤ (η₂ ω t).im := hp₂.2.2.1
  by_cases hmeet : ∃ s t, η₁ ω s = η₂ ω t
  · obtain ⟨s, t, hst⟩ := hmeet
    obtain ⟨s₀, t₀, hfc, -⟩ := h77 ⟨s, t, by rw [hζ₁]; exact le_top, by rw [hζ₂]; exact le_top, hst⟩
    obtain ⟨hMω, hAω, φ, ψ, lift, hC, hk⟩ :=
      hpω s₀ t₀ hfc (by rw [hζ₁]; exact ENNReal.coe_lt_top) (by rw [hζ₂]; exact ENNReal.coe_lt_top)
    obtain ⟨hl₁, hl₂, hsp₁, -, hs0₂, hsH₂, hord⟩ := twoHeightGood_spec (htrω hMω hAω)
    have hU₁ : U₁ ω = ⊤ := hl₁
    have hU₂ : U₂ ω = ⊤ := hl₂
    have he₁ : (X ω).1.path₁ = γ₁ ω := funext fun t =>
      RestartSpace.path₁_mk' _ (hcont₁ ω) _ _ (by rw [hU₁]; exact le_top)
    have he₂ : (X ω).1.path₂ = γ₂ ω := funext fun t =>
      RestartSpace.path₂_mk' _ _ _ (hcont₂ ω) (by rw [hU₂]; exact le_top)
    rw [he₁] at hsp₁ hord
    rw [he₂] at hs0₂ hsH₂ hord
    rw [hζ₁, hζ₂] at hfc hk
    rw [hU₁, hU₂] at hk
    exact range_subset_closedLeftSide_glue hα₁ hc₂ hα₂ hx h0₁ h0₂ hx₂ hx₁ hfc hC hk hsp₁ hs0₂ hsH₂ hord
  · push Not at hmeet
    rw [closedLeftSide_eq]
    exact (range_subset_leftSide_of_disjoint hα₁.2.2.1 hc₂ hα₂ hx h0₁ h0₂ hx₁ hmeet).trans subset_union_left

end Order

/-! ### Lemma G2a = order + parts -/

/-- **Named statement: the order part of Lemma G2a** (supplement p. 491: "The higher-angle curve `α̂₂` lies to the left
of `α̂₁` in closed Jordan-side order"; G2a, p. 492: "The same complete ordered-reference conclusion holds"). Binders of
`G2aReferenceStatement`; conclusion: almost surely the range of `α₂` is in the closed left side of `α₁`. -/
def G2aOrderStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ w₂ w₁ : ℝ, θ₁ < θ₂ → w₂ < w₁ →
    ∀ (m : ℝ → ℝ) (Jm : Finset ℝ), (∀ j ∈ Jm, w₂ < j ∧ j < w₁) →
      IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) →
      (∃ ε > 0, ∀ x, w₂ < x → x < w₂ + ε → m x = sleLambda κ - θ₂ * QuantumZipper.chiC κ) →
      (∃ ε > 0, ∀ x, w₁ - ε < x → x < w₁ → m x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ) →
      (∀ x, w₂ < x → x < w₁ → -sleLambda κ - θ₂ * QuantumZipper.chiC κ < m x ∧
        m x < sleLambda κ - θ₁ * QuantumZipper.chiC κ) →
    ∀ {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
      (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData Q Ĥ (g2aData κ θ₁ θ₂ w₂ w₁ m) ((insert w₂ (insert w₁ Jm) : Finset ℝ) : Set ℝ) →
    ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁ θ₁ Q Ĥ α₁ ζ₁ →
      IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂ θ₂ Q Ĥ α₂ ζ₂ →
      ∀ᵐ x ∂Q, range (α₂ x) ⊆ closedLeftSide (α₁ x)

/-- **Named statement: the other parts of Lemma G2a** (supplement pp. 491–492: complete lifetimes, "complete proper
simple traces", opposite-seed avoidance; PROVE-RLC-H). Binders of `G2aReferenceStatement`; conclusion: the conjuncts of
`G2aReferenceStatement` other than the order. -/
def G2aPartsStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ w₂ w₁ : ℝ, θ₁ < θ₂ → w₂ < w₁ →
    ∀ (m : ℝ → ℝ) (Jm : Finset ℝ), (∀ j ∈ Jm, w₂ < j ∧ j < w₁) →
      IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) →
      (∃ ε > 0, ∀ x, w₂ < x → x < w₂ + ε → m x = sleLambda κ - θ₂ * QuantumZipper.chiC κ) →
      (∃ ε > 0, ∀ x, w₁ - ε < x → x < w₁ → m x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ) →
      (∀ x, w₂ < x → x < w₁ → -sleLambda κ - θ₂ * QuantumZipper.chiC κ < m x ∧
        m x < sleLambda κ - θ₁ * QuantumZipper.chiC κ) →
    ∀ {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
      (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData Q Ĥ (g2aData κ θ₁ θ₂ w₂ w₁ m) ((insert w₂ (insert w₁ Jm) : Finset ℝ) : Set ℝ) →
    ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁ θ₁ Q Ĥ α₁ ζ₁ →
      IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂ θ₂ Q Ĥ α₂ ζ₂ →
      ∀ᵐ x ∂Q, ζ₁ x = ⊤ ∧ ζ₂ x = ⊤ ∧ IsProperCompletion (α₁ x) 0 (α₁ x) ∧
        IsProperCompletion (α₂ x) 0 (α₂ x) ∧ (w₂ : ℂ) ∉ range (α₁ x) ∧ (w₁ : ℂ) ∉ range (α₂ x)

/-- **Lemma G2a is its order together with its other parts.** -/
theorem g2aReferenceStatement_of_parts_order (hP : G2aPartsStatement.{u}) (hO : G2aOrderStatement.{u}) :
    G2aReferenceStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ w₂ w₁ hθ hw m Jm hJm hpc hL hR hmid S _ Q _ Ĥ hĤ α₁ α₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [hP κ hκ hκ4 θ₁ θ₂ w₂ w₁ hθ hw m Jm hJm hpc hL hR hmid Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ h₁ h₂,
    hO κ hκ hκ4 θ₁ θ₂ w₂ w₁ hθ hw m Jm hJm hpc hL hR hmid Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ h₁ h₂] with x hp ho
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, ho, hp.2.2.2.2.1, hp.2.2.2.2.2⟩

/-- **The order of Lemma G2a** (supplement pp. 491–492) from its other parts, Lemmas 7.5 and 7.7, the first-contact word
kernel and the half-plane Proposition 5.5. -/
theorem g2aOrderStatement_of_parts (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hW : FirstContactWordKernelStatement.{u}) (h55 : Sec7.Lemma71H.Prop55HalfPlaneStatement.{0})
    (hP : G2aPartsStatement.{u}) : G2aOrderStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ w₂ w₁ hθ hw m Jm hJm hpc hL hR hmid S _ Q _ Ĥ hĤ α₁ α₂ ζ₁ ζ₂ h₁ h₂
  have hJ : ∀ y ∈ insert w₂ (insert w₁ Jm), w₂ ≤ y ∧ y ≤ w₁ := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ⟨le_rfl, hw.le⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ⟨hw.le, le_rfl⟩
    · exact ⟨(hJm y hy).1.le, (hJm y hy).2.le⟩
  have hbL : ∀ y < w₂, g2aData κ θ₁ θ₂ w₂ w₁ m y = -sleLambda κ - θ₂ * chiC κ := fun y hy => by
    simp only [g2aData, hy, ↓reduceIte]
  have hbR : ∀ y, w₁ < y → g2aData κ θ₁ θ₂ w₂ w₁ m y = sleLambda κ - θ₁ * chiC κ := fun y hy => by
    simp only [g2aData, not_lt.2 (hw.trans hy).le, not_lt.2 hy.le, ↓reduceIte]
  exact ae_range_subset_closedLeftSide_of_exterior hL75 hL77 hW h55 hκ hκ4 hpc hw hθ hJ hbL hbR hĤ h₁ h₂
    (hP κ hκ hκ4 θ₁ θ₂ w₂ w₁ hθ hw m Jm hJm hpc hL hR hmid Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ h₁ h₂)

/-- **Lemma G2a** (`G2aReferenceStatement`) from its other parts (PROVE-RLC-H), Lemmas 7.5 and 7.7, the first-contact
word kernel and the half-plane Proposition 5.5. -/
theorem g2aReferenceStatement_of_parts (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hW : FirstContactWordKernelStatement.{u}) (h55 : Sec7.Lemma71H.Prop55HalfPlaneStatement.{0})
    (hP : G2aPartsStatement.{u}) : G2aReferenceStatement.{u} :=
  g2aReferenceStatement_of_parts_order hP (g2aOrderStatement_of_parts hL75 hL77 hW h55 hP)

end RLC

end InteractingSLE
