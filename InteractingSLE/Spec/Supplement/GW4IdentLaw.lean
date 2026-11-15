/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4IdentHull
import InteractingSLE.Spec.Supplement.GW4TraverseMain
import InteractingSLE.Spec.Exist.StagedLawStep

/-!
# Theorem GW4: the identification of the relative driver, from the component (Det)

Packet PROVE-T14-GW4R. `GW4Traverse.GW4RelativeIdentStatement` (PROVE-T14-GW4T; Theorem GW4's proof, "The full kernel
and the one phase", pp. 638–639) says: for every centred counterflow `W_C` of the component field `h_C` under the
conditional law `ν` with infinite lifetime, `ν`-almost surely **every** continuous relative driver of the ambient
traversal (continuous `W_rel`, strictly increasing continuous clock `T`, hulls `K^{W_rel}_s = Φ(K'_{T s} ∩ R⁻¹(C))`) is
`W_C`. Here it is reduced to the **existence** of one centred counterflow of `h_C` generating the relative hulls — the
component version of GB6's (Det) (`Supp8.GB6.GB6CondDetStatement`, last clause: "the canonical counterflow of the
conditional field … generates the chart images `Ψ(K'_t)` of the physical counterflow hulls in the relative clock") —
plus Theorems 1.2–1.3:

* **`ae_eq_of_isCenteredCounterflowDriver`**: any two centred counterflows of the same GFF with infinite lifetimes
  agree almost surely (Theorem 1.2 in its word-measurable form: the transported fields are equal, both couplings are
  read with one word (`Exist.StagedLaw.isFlowLineDriver_word`), the parametric determination map is the same for
  both, and the driver is decoded from the determined trace (`Exist.Staged.ae_detCode_eq`));
* `monotone_relHull`: `t ↦ Φ(K'_t ∩ R⁻¹(C))` is monotone;
* **`GW4RelativeLawStatement`** (named input; the component (Det)): some centred counterflow of `h_C` with infinite
  lifetime generates, `ν`-almost surely, the relative hulls `Φ(K'_{T s} ∩ R⁻¹(C))` for some clock `T`;
* **`gw4RelativeIdentStatement_of_law`**: `GW4RelativeIdentStatement` from the law input and Theorems 1.2–1.3 (the
  remaining "every" is `ae_eq_of_isCenteredCounterflowDriver` and the pathwise uniqueness
  `GW4Ident.eq_of_fwdHull_eq_comp`, which uses the strict monotonicity of half-plane capacity);
* `gw4RelativeLawStatement_of_relHulls`: conversely the relative-hull statement gives the law input (with the
  canonical counterflow `GW4Traverse.cfDrv` and GW3's word bounds), so the law input is no stronger than what
  `GW4RelativeHullStatement` asks;
* `gw4RelativeHullStatement_of_chain_law`, `gw4TraversalCoreStatement_of_chain_law`: the traversal core from the
  pathwise chain, the law input, GW3's word bounds and Theorems 1.2–1.3.

**R43/R48.** Theorems 1.2–1.3 are used; GW4 serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Ident

open GW4Traverse Sec7.StripSysField

/-! ### Two centred counterflows of one field agree -/

/-- **Universal determination, two drivers**: two centred counterflows of the same GFF (piecewise-constant data)
with almost surely infinite lifetimes agree almost surely. Both transported fields are `cfField κ h_C`; both drivers
drive the flow line of that field for the data of one word `c₀` (`Exist.StagedLaw.isFlowLineDriver_word`); the
parametric map of Theorem 1.2 is one map for that word, so both determination codes `detCode Φ (word, field)`
coincide, and each driver is decoded from it (`Exist.Staged.ae_detCode_eq`, `Exist.Staged.drvPath_dOf_agree`). -/
theorem ae_eq_of_isCenteredCounterflowDriver (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {bC : ℝ → ℝ} {jumpsC : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData bC jumpsC) {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {hC : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q hC bC jumpsC)
    {W₁ W₂ : ℝ≥0 → Ω → ℝ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hcd₁ : IsCenteredCounterflowDriver κ Q hC W₁ ζ₁) (hζ₁ : ∀ᵐ ω ∂Q, ζ₁ ω = ⊤)
    (hcd₂ : IsCenteredCounterflowDriver κ Q hC W₂ ζ₂) (hζ₂ : ∀ᵐ ω ∂Q, ζ₂ ω = ⊤) :
    ∀ᵐ ω ∂Q, (fun t => W₁ t ω) = (fun t => W₂ t ω) := by
  have hκ' : 0 < 16 / κ := sixteen_div_pos hκ
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq (isPiecewiseConstant_counterflowData κ hb)
  have hcf := isGFFWithBoundaryData_cfField κ hb hh
  have hg₀ : IsGFFWithBoundaryData Q (fun ω => cfField κ (hC ω)) c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr Q _ (S := ((counterflowJumps jumpsC : Finset ℝ) : Set ℝ))
      fun y hy => hc₀ y hy).2 hcf
  have hF := Theorem15.isOrderedForceWord_flowLine c₀.fn c₀.jumps 0
  -- each driver drives the flow line of `cfField κ h_C` for the data of `c₀`
  have hread : ∀ {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}, IsCenteredCounterflowDriver κ Q hC W ζ →
      IsFlowLineDriver (16 / κ) c₀.fn c₀.jumps 0 Q (fun ω => cfField κ (hC ω)) W ζ := by
    intro W ζ hcd
    obtain ⟨b', J', h', hpc', htr', hfl'⟩ := hcd
    have e : h' = fun ω => cfField κ (hC ω) := funext fun ω =>
      (htr' ω).unique Chart.isConformal_infinitySourceChart (isChartTransport_cfField κ (hC ω))
    rw [e] at hfl'
    exact Exist.StagedLaw.isFlowLineDriver_word hκ' hg₀ hpc' hfl'
  obtain ⟨h₁'', 𝓕₁, VL₁, VR₁, B₁, htr₁, hcoup₁⟩ := hread hcd₁
  obtain ⟨h₂'', 𝓕₂, VL₂, VR₂, B₂, htr₂, hcoup₂⟩ := hread hcd₂
  have e₁ : h₁'' = fun ω => Exist.flowField 0 (0 * QuantumZipper.chiC (16 / κ)) (cfField κ (hC ω)) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr₁ ω)
  have e₂ : h₂'' = fun ω => Exist.flowField 0 (0 * QuantumZipper.chiC (16 / κ)) (cfField κ (hC ω)) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr₂ ω)
  have hdet₁ := Exist.Staged.ae_detCode_eq hκ' hF h13 hcoup₁
    ((h12p (16 / κ) hκ' _ _).choose_spec.2 _ _ _ _ hF hcoup₁)
  have hdet₂ := Exist.Staged.ae_detCode_eq hκ' hF h13 hcoup₂
    ((h12p (16 / κ) hκ' _ _).choose_spec.2 _ _ _ _ hF hcoup₂)
  filter_upwards [hdet₁, hdet₂, hζ₁, hζ₂] with ω hω₁ hω₂ hζ₁ω hζ₂ω
  obtain ⟨x₁, -, hζx₁, hw₁, hcode₁⟩ := hω₁
  obtain ⟨x₂, -, hζx₂, hw₂, hcode₂⟩ := hω₂
  rw [e₁] at hcode₁
  rw [e₂] at hcode₂
  have hx : Exist.Staged.dOf x₁ = Exist.Staged.dOf x₂ := hcode₁.symm.trans hcode₂
  funext t
  have ht₁ : (t : ℝ≥0∞) < ζ₁ ω := by rw [hζ₁ω]; exact ENNReal.coe_lt_top
  have ht₂ : (t : ℝ≥0∞) < ζ₂ ω := by rw [hζ₂ω]; exact ENNReal.coe_lt_top
  rw [← (hw₁ t ht₁).1, ← (hw₂ t ht₂).1, ← (Exist.Staged.drvPath_dOf_agree x₁).2 t (hζx₁ ▸ ht₁),
    ← (Exist.Staged.drvPath_dOf_agree x₂).2 t (hζx₂ ▸ ht₂), hx]

/-! ### The relative hull family -/

/-- The relative hulls `t ↦ Φ(K'_t ∩ R⁻¹(C))` of an ambient Loewner chain form a monotone family. -/
theorem monotone_relHull (c : Chart) (C : Set ℂ) (V : ℝ → ℝ) :
    Monotone fun t : ℝ≥0 => relMapC c '' (QuantumZipper.fwdHull V t ∩ relDom C) := by
  intro t₁ t₂ ht
  exact image_mono (inter_subset_inter_left _ (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 ht)))

/-! ### The component (Det) and the identification -/

/-- **Named input: Theorem GW4, the component (Det)** ("The full kernel and the one phase", pp. 638–639: "That lemma
forces `δ_s = 0` and identifies the canonical integrated finite-word system"; the component version of the last
clause of `Supp8.GB6.GB6CondDetStatement`). Binders and component data of `GW4Traverse.GW4RelativeHullStatement`
(verbatim). Some centred counterflow `(W_C, ζ_C)` of the component field under the conditional law `ν`, with almost
surely infinite lifetime, generates `ν`-almost surely the relative hulls of the ambient traversal: for some clock `T`,
`K^{W_C}_s = Φ(K'_{T s} ∩ R⁻¹(C))` for every relative time `s` (no property of `T` is asked).

Compared with `GW4Traverse.GW4RelativeIdentStatement`, the quantifier over **all** centred counterflows and over all
relative drivers is not asked: it is proved (`gw4RelativeIdentStatement_of_law`). Conversely the relative-hull
statement implies this one (`gw4RelativeLawStatement_of_relHulls`). -/
def GW4RelativeLawStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
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
            (∀ᵐ ω ∂ν, ζC ω = ⊤) ∧
            ∀ᵐ ω ∂ν, ∃ T : ℝ≥0 → ℝ≥0, ∀ s : ℝ≥0,
              QuantumZipper.fwdHull (fun r : ℝ => WC r.toNNReal ω) s =
                relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) (T s) ∩ relDom C)

/-- **Theorem GW4's identification of the relative driver from the component (Det)** (conditional helper with a
distinct name). Given a centred counterflow `W_C` with infinite lifetime and a continuous relative driver `W_rel`
with clock `T`: the law input's witness `W₀` equals `W_C` almost surely (`ae_eq_of_isCenteredCounterflowDriver`);
`W₀(ω)` is continuous from `0` (Theorem 1.3, `GW4Traverse.ae_trace_of_isCenteredCounterflowDriver`); its hulls and
those of `W_rel` are members of the one monotone relative family (`monotone_relHull`), so `W₀(ω) = W_rel`
(`eq_of_fwdHull_eq_comp`). -/
theorem gw4RelativeIdentStatement_of_law (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hL : GW4RelativeLawStatement.{u}) :
    GW4RelativeIdentStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  filter_upwards [hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hLω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff WC ζC hcd hζC
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨W₀, ζ₀, hcd₀, hζ₀, hK₀⟩ := hLω C hCm c hC bC jumpsC hch htr hpc hbd hgff
  have he := ae_eq_of_isCenteredCounterflowDriver h12p h13 hκ hpc hgff hcd₀ hζ₀ hcd hζC
  have hreg := ae_trace_of_isCenteredCounterflowDriver h13 hκ hcd₀ hζ₀
  filter_upwards [he, hK₀, hreg] with ω heω hKω hregω
  intro Wrel T hWc _ _ hK
  obtain ⟨T₀, hT₀⟩ := hKω
  rw [← heω]
  exact eq_of_fwdHull_eq_comp (monotone_relHull c C _) hregω.1 hWc hregω.2.1 hT₀ hK

/-- **The law input from the relative-hull statement** (so `GW4RelativeLawStatement` asks no more than
`GW4Traverse.GW4RelativeHullStatement`): the witness is the canonical counterflow `cfDrv` of the component field, with
infinite lifetime by GW3's word bounds. -/
theorem gw4RelativeLawStatement_of_relHulls (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hWB : GW4.GW3WordBoundStatement.{u})
    (hH : GW4RelativeHullStatement.{u}) : GW4RelativeLawStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  filter_upwards [hWB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE,
    hH κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hWω hHω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  have hcd := isCenteredCounterflowDriver_cfDrv h12p hκ bC jumpsC h13 hpc hgff
  obtain ⟨b', J', h', hpc', htr', hfl⟩ := id hcd
  obtain ⟨hLw, hRw⟩ := hWω C hCm c hC bC jumpsC hch htr hpc hbd hgff b' J' h' _ _ hpc' htr' hfl
  have hζC := GW4.ae_lifetime_eq_top_of_counterflowWord hfl hLw hRw
  refine ⟨_, _, hcd, hζC, ?_⟩
  filter_upwards [hHω C hCm c hC bC jumpsC hch htr hpc hbd hgff _ _ hcd hζC] with ω hω
  obtain ⟨T, -, -, -, hK, -⟩ := hω
  exact ⟨T, hK⟩

/-- **The relative-hull statement from the pathwise chain and the component (Det)** (conditional helper). -/
theorem gw4RelativeHullStatement_of_chain_law (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hP : GW4RelativeChainStatement.{u}) (hL : GW4RelativeLawStatement.{u}) :
    GW4RelativeHullStatement.{u} :=
  gw4RelativeHullStatement_of_chain_ident hP (gw4RelativeIdentStatement_of_law h12 h13 hL)

/-- **Theorem GW4's traversal core from the pathwise chain and the component (Det)** (conditional helper). -/
theorem gw4TraversalCoreStatement_of_chain_law (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hO : GW3Word.BetweenComponentsOpenStatement.{u})
    (hWB : GW4.GW3WordBoundStatement.{u}) (hP : GW4RelativeChainStatement.{u})
    (hL : GW4RelativeLawStatement.{u}) : GW4.GW4TraversalCoreStatement.{u} :=
  gw4TraversalCoreStatement_of_relHulls h12 h13 hO hWB (gw4RelativeHullStatement_of_chain_law h12 h13 hP hL)

end GW4Ident

end Theorem14

end InteractingSLE
