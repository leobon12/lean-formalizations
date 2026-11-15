/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3Word
import InteractingSLE.Spec.Supplement.GW3LawJointUnion
import InteractingSLE.Spec.Supplement.BR3Ref

/-!
# Theorem 1.4's component kernels: the R51 copies of GW3's word bounds, GW4's kernels and the final assembly

Packet PROVE-T14-GW8. Ruling R51 adds to the frozen component-kernel anchor (version 2) the hypothesis that every
staged family is `StagedPiecesRegular`. PROVE-T14-GW7 stated the R51 forms of Lemma GW3's field law, charts, geometry
and of the no-common-continuum statement (`GW3Joint`, `GW3Sided`, `WalkCont`). This file gives the R51 forms of the
remaining links of the chain `Wire.componentKernels_of_open5`:

* `GW3WordBoundRegStatement` and its proof `gw3WordBoundRegStatement_of_inputs` from the openness of the
  between-components, Lemma GW0's forward implication and the sides of the walks' real connectors (PROVE-T14-GW5's
  argument `GW3Word.gw3WordBoundStatement_of_inputs`, restated pointwise in `wordBound_of_pointwise`);
* `GW4TraversalCoreRegStatement`, `GW4TraversalRegStatement`, `gw4TraversalRegStatement_of_core`;
* `GW4KernelRegStatement`, `gw4KernelRegStatement_of_inputs`, `gw4KernelRegStatement_of_thm12`;
* `componentKernels_of_regKernels` (the anchor's conclusion from the R51 chart and kernel statements) and the provider-
  shaped wrappers `componentKernels_of_regInputs`, `componentKernels_of_unionLaw`.

Every theorem is a conditional helper with a distinct name; none is a provider.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4R51

open GW3Word

/-! ### Lemma GW3's word bounds, pointwise -/

/-- **Lemma GW3's word bounds (GW3.2), pointwise** (PROVE-T14-GW5's argument for
`GW3Word.gw3WordBoundStatement_of_inputs`, for fixed walks `R`, `L` of the boundary-walk instructions `wR`, `wL`
rooted at `0`, conditional law `ν` and ambient original-data bounds `hbneg`, `hbpos` from Lemma GW0). If the
between-components are open and the real connectors of `R` / `L` lie in `[0, ∞)` / `(−∞, 0]`, the counterflow word of
every component field with a GW3.1 word has all side partial sums greater than `−2`. -/
theorem wordBound_of_pointwise {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {wR wL : ExplSpec} (hR0 : (wR.1 : ℂ) = 0) (hL0 : (wL.1 : ℂ) = 0) {DR DL : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hbneg : ∀ t, t < 0 → t ∉ jumps → b t < sleLambda (16 / κ) + Real.pi * QuantumZipper.chiC κ)
    (hbpos : ∀ t, 0 < t → t ∉ jumps → -sleLambda (16 / κ) - Real.pi * QuantumZipper.chiC κ < b t)
    (hOω : ∀ C ∈ betweenComponents (ExplState.physSet κ b jumps wR DR) (ExplState.physSet κ b jumps wL DL),
      IsOpen C)
    (hSω : (∀ a ∈ (ExplState.run κ b jumps wR DR wR.2.2.length).2.1, a ⊆ Ici 0) ∧
      ∀ a ∈ (ExplState.run κ b jumps wL DL wL.2.2.length).2.1, a ⊆ Iic 0)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {C : Set ℂ} (hCm : C ∈ betweenComponents (ExplState.physSet κ b jumps wR DR) (ExplState.physSet κ b jumps wL DL))
    {c : Chart} {hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {bC : ℝ → ℝ} {jumpsC : Finset ℝ}
    (hch : IsComponentChart (ExplState.physSet κ b jumps wR DR) (ExplState.physSet κ b jumps wL DL) C c)
    (hpc : IsPiecewiseConstantBoundaryData bC jumpsC)
    (hbd : IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR DR)
      (ExplState.ordinarySet κ b jumps wL DL) c.2.1 bC jumpsC)
    (hgff : IsGFFWithBoundaryData ν hC bC jumpsC)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {WC : ℝ≥0 → Ω → ℝ}
    {ζC : Ω → ℝ≥0∞} (hb' : IsPiecewiseConstantBoundaryData b' J')
    (htr' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (hC ω) (h' ω))
    (hfl : IsFlowLineDriver (16 / κ) b' J' 0 ν h' WC ζC) :
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) ∧
    ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l := by
  set R := ExplState.physSet κ b jumps wR DR with hRdef
  set L := ExplState.physSet κ b jumps wL DL with hLdef
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 < Real.pi * QuantumZipper.chiC κ := mul_pos Real.pi_pos hχ
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hΛ := Sec4.sleLambda_sixteen_div_eq_sub hκ
  have hCo : IsOpen C := hOω C hCm
  have hgff' : IsGFFWithBoundaryData ν h' b' J' := by
    obtain ⟨h'', 𝓕, VL, VR, B, htac, hcoup⟩ := hfl
    have e : h'' = h' := funext fun ω => GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
    subst e
    exact Sec7.StripSysField.isGFFWithBoundaryData_of_flowLineGFF hκ' hb' ⟨hcoup.2.1, hcoup.2.2.1⟩
  have hoff := GW2Cone.eq_counterflowData_off hpc hb' hgff htr' hgff'
  set F1 := Sec7.StripSysField.returnExcept (jumpsC ∪ Sec7.StripSysField.returnExcept J') with hF1
  set Ex : Finset ℝ := jumpsC ∪ F1.image (fun z => -z⁻¹) with hEx
  set E0 : Finset ℝ := insert 0 jumps with hE0
  -- the generic-point argument on either side
  have key : ∀ y, y ≠ 0 → y ∉ J' → ∃ x : ℝ, x ≠ 0 ∧ x ∉ jumpsC ∧ b' y = Sec7.StripSysField.counterflowData κ bC (-x⁻¹) ∧
      (0 < y ↔ x < 0) ∧ ∃ p : ℂ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) ∧ (0 < x → p ∈ R) ∧ (x < 0 → p ∈ L) ∧
        ∀ t ∈ E0, p ≠ (t : ℂ) := by
    intro y hy0 hyJ
    obtain ⟨ε, hε, hloc⟩ := Metric.eventually_nhds_iff.1 (hb' y hyJ)
    set δ := min ε |y| / 2 with hδ
    have hya : 0 < |y| := abs_pos.2 hy0
    have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hε hya)
    have hδε : δ < ε := by rw [hδ]; linarith [min_le_left ε |y|]
    have hδy : δ < |y| := by rw [hδ]; linarith [min_le_right ε |y|]
    have hs : 0 < y - δ ∨ y + δ < 0 := by
      rcases lt_or_gt_of_ne hy0 with hn | hp
      · right; rw [abs_of_neg hn] at hδy; linarith
      · left; rw [abs_of_pos hp] at hδy; linarith
    have hlt : -(y - δ)⁻¹ < -(y + δ)⁻¹ := by
      rcases hs with hp | hn
      · exact neg_lt_neg ((inv_lt_inv₀ (by linarith) hp).2 (by linarith))
      · exact neg_lt_neg ((inv_lt_inv₀ (by linarith : 0 < -(y - δ)) (by linarith : 0 < -(y + δ))).2
          (by linarith) |> fun h => by rw [inv_neg, inv_neg] at h; linarith)
    obtain ⟨x, hx, hxE, p, hp, hpR, hpL, hpE⟩ := exists_generic hch hCo hlt Ex E0
    have hy'' := negInv_mem_Ioo (by linarith) hs hx
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, inv_zero, neg_zero] at hy''
      rcases hs with hp' | hn'
      · linarith [hy''.1]
      · linarith [hy''.2]
    have hxJ : x ∉ jumpsC := fun h => hxE (Finset.mem_union_left _ h)
    have hF : -x⁻¹ ∉ F1 := fun h => hxE (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, negInv_negInv x⟩))
    have hdist : dist (-x⁻¹) y < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy''.1, hy''.2]
    refine ⟨x, hx0, hxJ, ?_, ?_, p, hp, hpR, hpL, hpE⟩
    · rw [← hloc hdist, hoff _ hF]
    · constructor
      · intro hy
        by_contra hxn
        have hxp : 0 < x := lt_of_le_of_ne (not_lt.1 hxn) (Ne.symm hx0)
        have : -x⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hxp)
        rcases hs with hp' | hn'
        · linarith [hy''.1]
        · linarith
      · intro hxn
        have : 0 < -x⁻¹ := neg_pos.2 (inv_lt_zero.2 hxn)
        rcases hs with hp' | hn'
        · linarith
        · linarith [hy''.2]
  have hR' : ∀ y, 0 < y → y ∉ J' → -sleLambda (16 / κ) < b' y := by
    intro y hy hyJ
    obtain ⟨x, hx0, hxJ, hb'x, hsign, p, hp, -, hpL, hpE⟩ := key y hy.ne' hyJ
    have hxn : x < 0 := hsign.1 hy
    rw [hb'x, counterflowData_of_pos hκ _ (neg_pos.2 (inv_lt_zero.2 hxn)), negInv_negInv,
      (hbd x hxJ p hp).2 hxn]
    split_ifs with hpo
    · rw [hΛ]; linarith
    · rcases mem_physSet_cases (hpL hxn) hpo with h0 | ⟨a, ha, t, ht, rfl⟩
      · exact absurd (h0.trans hL0) (hpE 0 (Finset.mem_insert_self _ _))
      · have ht0 : t ≤ 0 := hSω.2 a ha ht
        have htne : t ≠ 0 := fun h0 => hpE 0 (Finset.mem_insert_self _ _) (by rw [h0])
        have htJ : t ∉ jumps := fun hj => hpE t (Finset.mem_insert_of_mem hj) rfl
        rw [Complex.ofReal_re]
        linarith [hbneg t (lt_of_le_of_ne ht0 htne) htJ]
  have hL' : ∀ y, y < 0 → y ∉ J' → b' y < sleLambda (16 / κ) := by
    intro y hy hyJ
    obtain ⟨x, hx0, hxJ, hb'x, hsign, p, hp, hpR, -, hpE⟩ := key y hy.ne hyJ
    have hxp : 0 < x := lt_of_le_of_ne (not_lt.1 fun h => absurd (hsign.2 h) (not_lt.2 hy.le)) (Ne.symm hx0)
    rw [hb'x, counterflowData_of_neg hκ _ (neg_neg_of_pos (inv_pos.2 hxp)), negInv_negInv,
      (hbd x hxJ p hp).1 hxp]
    split_ifs with hpo
    · rw [hΛ]; linarith
    · rcases mem_physSet_cases (hpR hxp) hpo with h0 | ⟨a, ha, t, ht, rfl⟩
      · exact absurd (h0.trans hR0) (hpE 0 (Finset.mem_insert_self _ _))
      · have ht0 : 0 ≤ t := hSω.1 a ha ht
        have htne : t ≠ 0 := fun h0 => hpE 0 (Finset.mem_insert_self _ _) (by rw [h0])
        have htJ : t ∉ jumps := fun hj => hpE t (Finset.mem_insert_of_mem hj) rfl
        rw [Complex.ofReal_re]
        linarith [hbpos t (lt_of_le_of_ne ht0 (Ne.symm htne)) htJ]
  exact ⟨neg_two_lt_sum_flowLineRhoL_of_forall hκ' hb' hL', neg_two_lt_sum_flowLineRhoR_of_forall hκ' hb' hR'⟩

/-! ### The statements in the R51 form -/

/-- **Named input: Lemma GW3's word bounds (GW3.2), R51 form**: `GW4.GW3WordBoundStatement` for staged families that
are also `StagedPiecesRegular` (proved from its inputs: `gw3WordBoundRegStatement_of_inputs`). -/
def GW3WordBoundRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞),
            IsPiecewiseConstantBoundaryData b' J' →
            (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
              (QuantumZipper.chiC (16 / κ)) (hC ω) (h' ω)) →
            IsFlowLineDriver (16 / κ) b' J' 0 ν h' WC ζC →
            (∀ i : Fin (flowLineNL b' J' 0),
              -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) ∧
            ∀ i : Fin (flowLineNR b' J' 0),
              -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l

/-- **Named input: Theorem GW4's traversal core, R51 form**: `GW4.GW4TraversalCoreStatement` for staged families that
are also `StagedPiecesRegular`. -/
def GW4TraversalCoreRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∃ (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ ν hC WC ζC ∧
            ∀ᵐ ω ∂ν, IsComponentTraversal c.2.1 (fun t => W' t ω) (fun t => WC t ω)

/-- **Theorem GW4's component traversal, R51 form**: `GW4.GW4TraversalStatement` for staged families that are also
`StagedPiecesRegular`. -/
def GW4TraversalRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∃ (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ ν hC WC ζC ∧
            ∀ᵐ ω ∂ν, ζC ω = ⊤ ∧ IsComponentTraversal c.2.1 (fun t => W' t ω) (fun t => WC t ω)

/-- **Theorem GW4's component kernels, R51 form**: `Theorem14.GW4KernelStatement` (the second assertion of the frozen
component-kernel anchor) for staged families that are also `StagedPiecesRegular`. -/
def GW4KernelRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
          ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
            (∀ C ∈ betweenComponents R L,
              IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
              (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
                (hC C ω)) ∧
              (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
                IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                  (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
                IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
              IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
              ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
                IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
            iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν

/-! ### Bridges from the unregularized forms -/

/-- The unregularized word bounds imply their R51 form. -/
theorem gw3WordBoundRegStatement_of_unreg (hW : GW4.GW3WordBoundStatement.{u}) : GW3WordBoundRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- The unregularized traversal core implies its R51 form. -/
theorem gw4TraversalCoreRegStatement_of_unreg (hT : GW4.GW4TraversalCoreStatement.{u}) :
    GW4TraversalCoreRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- The unregularized traversal statement implies its R51 form. -/
theorem gw4TraversalRegStatement_of_unreg (hT : GW4.GW4TraversalStatement.{u}) : GW4TraversalRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- The unregularized kernel statement implies its R51 form. -/
theorem gw4KernelRegStatement_of_unreg (hK : GW4KernelStatement.{u}) : GW4KernelRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hK κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-! ### The word bounds, the traversal and the kernels in the R51 form -/

/-- **Lemma GW3's word bounds (GW3.2), R51 form**, from the openness of the between-components, Lemma GW0's forward
implication and the sides of the walks' real connectors (PROVE-T14-GW5's argument, `wordBound_of_pointwise`). -/
theorem gw3WordBoundRegStatement_of_inputs (hO : GW3Joint.BetweenComponentsOpenRegStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hS : WalkCont.WalkConnectorSideRegStatement.{u}) :
    GW3WordBoundRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  -- the ambient counterflow word is admissible (GW0), so the original data obey the ambient bounds
  obtain ⟨h'a, -, hfla⟩ := GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨hAL, hAR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hfla hζ'
  have hcfb := Sec7.StripSysField.isPiecewiseConstant_counterflowData κ hb
  have hbneg : ∀ t, t < 0 → t ∉ jumps →
      b t < sleLambda (16 / κ) + Real.pi * QuantumZipper.chiC κ := by
    intro t ht htJ
    have hy : 0 < -t⁻¹ := neg_pos.2 (inv_lt_zero.2 ht)
    have h1 := neg_lambda_lt_of_sum_flowLineRhoR hκ' hcfb hAR hy (negInv_notMem_returnExcept ht.ne htJ)
    rw [counterflowData_of_pos hκ b hy, negInv_negInv] at h1
    linarith
  have hbpos : ∀ t, 0 < t → t ∉ jumps →
      -sleLambda (16 / κ) - Real.pi * QuantumZipper.chiC κ < b t := by
    intro t ht htJ
    have hy : -t⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 ht)
    have h1 := lt_lambda_of_sum_flowLineRhoL hκ' hcfb hAL hy (negInv_notMem_returnExcept ht.ne' htJ)
    rw [counterflowData_of_neg hκ b hy, negInv_negInv] at h1
    linarith
  filter_upwards [hO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hOω hSω
  intro R L ν C hCm c hC bC jumpsC hch _ hpc hbd hgff b' J' h' WC ζC hb' htr' hfl
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  exact wordBound_of_pointwise hκ hκ4 (by simp [boundaryWalkSpec]) (by simp [boundaryWalkSpec]) hbneg hbpos
    hOω hSω hCm hch hpc hbd hgff hb' htr' hfl

/-- **GW4's traversal statement from its core and GW3's word bounds, R51 form** (`GW4.gw4TraversalStatement_of_core`:
the relative lifetime is infinite by `GW4.ae_lifetime_eq_top_of_counterflowWord`). -/
theorem gw4TraversalRegStatement_of_core (hT : GW4TraversalCoreRegStatement.{u})
    (hW : GW3WordBoundRegStatement.{u}) : GW4TraversalRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hT' := hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
  have hW' := hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hT', hW'] with ω₀ hTω hWω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  obtain ⟨WC, ζC, hcd, htrav⟩ := hTω C hCm c hC bC jumpsC hch htr hpc hbd hgff
  obtain ⟨b', J', h', hpc', htr', hfl⟩ := hcd
  obtain ⟨hL, hR⟩ := hWω C hCm c hC bC jumpsC hch htr hpc hbd hgff b' J' h' WC ζC hpc' htr' hfl
  refine ⟨WC, ζC, ⟨b', J', h', hpc', htr', hfl⟩, ?_⟩
  filter_upwards [GW4.ae_lifetime_eq_top_of_counterflowWord hfl hL hR, htrav] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **Theorem GW4, the component kernels, R51 form**, from GW3's field law, GW4's traversal law and universal
determination (`GW4.gw4KernelStatement_of_inputs`: each traversal driver is a Borel function of its own component
field, so the independence of the component fields gives that of the field–path pairs). -/
theorem gw4KernelRegStatement_of_inputs (hF : GW3Joint.GW3FieldLawRegStatement.{u})
    (hT : GW4TraversalRegStatement.{u}) (hD : GW4.CounterflowDeterminationStatement.{u}) :
    GW4KernelRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hF' := hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
  have hT' := hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hF', hT'] with ω₀ hFω hTω
  intro R L ν cs hcs
  obtain ⟨ℓ, hC, hC1, hind⟩ := hFω cs hcs
  have hT1 : ∀ C ∈ betweenComponents R L, ∃ (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ ν (hC C) WC ζC ∧
        ∀ᵐ ω ∂ν, ζC ω = ⊤ ∧ IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC t ω) := by
    intro C hCm
    obtain ⟨hch, htr, bC, jumpsC, hpc, hbd, hgff⟩ := hC1 C hCm
    exact hTω C hCm ((cs C).1, (cs C).2.1, ℓ C) (hC C) bC jumpsC hch htr hpc hbd hgff
  choose! WC ζC hWC using hT1
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  have hdet : ∀ C ∈ betweenComponents R L, ∃ G : LQGMetric.DistOn upperHalfPlaneOpens → (ℝ≥0 → ℝ),
      Measurable G ∧ ∀ᵐ ω ∂ν, (fun t => WC C t ω) = G (hC C ω) := by
    intro C hCm
    obtain ⟨-, -, bC, jumpsC, hpc, -, hgff⟩ := hC1 C hCm
    exact hD κ hκ hκ4 ν (hC C) bC jumpsC hpc hgff (WC C) (ζC C) (hWC C hCm).1
      ((hWC C hCm).2.mono fun ω hω => hω.1)
  choose! G hGm hGae using hdet
  refine ⟨ℓ, hC, WC, ζC, fun C hCm => ?_, ?_⟩
  · obtain ⟨hch, htr, hgff⟩ := hC1 C hCm
    exact ⟨hch, htr, hgff, (hWC C hCm).1, (hWC C hCm).2⟩
  · exact GW4.iIndepFun_pair_of_ae_eq_comp (X := fun (C : betweenComponents R L) ω => hC C ω)
      (Y := fun (C : betweenComponents R L) ω => fun t => WC C t ω) (G := fun C => G C.1) hind
      (fun C => hGm C.1 C.2) fun C => hGae C.1 C.2

/-- **Theorem GW4, the component kernels, R51 form**, from GW3's field law, GW4's traversal law and Theorems 1.2–1.3
(universal determination: `GW4.counterflowDeterminationStatement_of_thm12`). -/
theorem gw4KernelRegStatement_of_thm12 (hF : GW3Joint.GW3FieldLawRegStatement.{u})
    (hT : GW4TraversalRegStatement.{u}) (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    GW4KernelRegStatement.{u} :=
  gw4KernelRegStatement_of_inputs hF hT (GW4.counterflowDeterminationStatement_of_thm12 h12 h13)

/-! ### The final assembly -/

/-- **Theorem 1.4, component kernels, version 2** (R51), provider shape (all arguments implicit, the anchor's
hypotheses auto-parameters), from the R51 forms of Lemma GW3's charts and Theorem GW4's kernels (conditional helper;
not the provider). -/
theorem componentKernels_of_regKernels (hGW3 : GW3Sided.GW3ChartRegStatement.{u})
    (hGW4 : GW4KernelRegStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption)
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec) := by assumption) :
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  (hGW3 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg).and
    (hGW4 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg)

/-- **Theorem 1.4, component kernels, version 2** (R51), provider shape, from the R51 forms of the inputs of
`Wire.componentKernels_of_open5`: Lemma GW3's sided geometry and one-chart field law, no common continuum of the walks,
the sides of their real connectors, GW4's traversal core and Theorems 1.2–1.3 (conditional helper; not the provider). -/
theorem componentKernels_of_regInputs (hGS : GW3Sided.GW3GeometrySidedRegStatement.{u})
    (hF1 : GW3Joint.GW3FieldLawOneChartRegStatement.{u}) (hN : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hS : WalkCont.WalkConnectorSideRegStatement.{u}) (hT : GW4TraversalCoreRegStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption)
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec) := by assumption) :
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  componentKernels_of_regKernels
    (GW3Sided.gw3ChartRegStatement_of_geometry (GW3Sided.gw3GeometryRegStatement_of_sided hGS))
    (gw4KernelRegStatement_of_thm12 (GW3Sided.gw3FieldLawRegStatement_of_sided hGS hN hF1)
      (gw4TraversalRegStatement_of_core hT
        (gw3WordBoundRegStatement_of_inputs
          (GW3Sided.betweenComponentsOpenRegStatement_of_geometry (GW3Sided.gw3GeometryRegStatement_of_sided hGS))
          (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hS)) h12 h13) hκ hκ4 hb hh hcf hζ' hE hreg

/-- **Theorem 1.4, component kernels, version 2** (R51), provider shape, from the finest named inputs: Lemma GW3's sided
geometry, the marked union law of the two walks (`GW3Joint.GW3UnionLawRegStatement`), the right walk a proper curve,
the sides of the real connectors, the piece statement (`WalkCont.WalkPieceContinuumRegStatement`), GW4's traversal
core and Theorems 1.2–1.3 (conditional helper; not the provider). -/
theorem componentKernels_of_unionLaw (hGS : GW3Sided.GW3GeometrySidedRegStatement.{u})
    (hU : GW3Joint.GW3UnionLawRegStatement.{u}) (hP : WalkCont.RightWalkProperRegStatement.{u})
    (hS : WalkCont.WalkConnectorSideRegStatement.{u}) (hNP : WalkCont.WalkPieceContinuumRegStatement.{u})
    (hT : GW4TraversalCoreRegStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption)
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec) := by assumption) :
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  componentKernels_of_regInputs hGS (GW3Joint.gw3FieldLawOneChartRegStatement_of_unionLaw hU)
    (WalkCont.walkNoCommonContinuumRegStatement_of_pieces hP hS hNP) hS hT h12 h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hreg

end GW4R51

end Theorem14

end InteractingSLE
