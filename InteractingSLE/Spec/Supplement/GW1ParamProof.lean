/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LaterR51

/-!
# Lemma GW1's proper simple curve: the R51 reduction and the finite concatenation

Packet PROVE-T14-GW1X. Lemma GW1 (supplement p. 618): "There is a field-determined continuous injective proper curve
`R` from `x` to `y`"; its proof ends (p. 620): "The finite union of the continuous injective pieces and connectors is
a continuous injective curve through its terminal limit; the only possible new terminal repetition would be `y`, which
no earlier finite prefix contains. It is proper in the Jordan compactification."

* `GW1ParamR51Statement` — `SB.GW1ParamStatement` with R51's hypothesis (the families of the version-2 Theorem 1.4
  anchors); `GW1ParamEveryRegStatement` — the same for families regular at every sample (the class on which the landed
  staged-law machinery works); **`gw1ParamR51Statement_of_everyReg`**: the second implies the first (regularize the
  family, `StagedReg.regFam`; the physical sets agree almost surely); `rightWalkProperRegStatement_of_gw1ParamR51`:
  PROVE-T14-GW7's `WalkCont.RightWalkProperRegStatement` from it.
* **The finite concatenation** (deterministic): `concatArc α ρ` runs the arc `α` on `[0, 1]` and then the proper
  ray `ρ`; `isProperCurve_concatArc`; `ChainOK L ρ` (a finite list of arcs, each meeting everything after it
  only at its endpoint, followed by a proper ray) and **`exists_isProperCurve_of_chainOK`**: the union is the range
  of a proper injective curve from the first point.
* `rescale`, `isArc_rescale`, **`exists_isArc_tipSet`**: the physical points of a regular piece stopped at a finite
  positive time are an arc on `[0, 1]` (seed image to endpoint image) once the chart's boundary extension is injective
  on the piece's trace.
* `walkNoCommonContinuumRegStatement_of_gw1Param`: PROVE-T14-GW7's reduction with the connector sides supplied
  (from Theorem 1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1X

open Exist Exist.StagedLaw StagedReg

/-! ### The R51 form of GW1's parametrization and its reduction to everywhere regular families -/

/-- **GW1's parametrization under ruling R51** (`SB.GW1ParamStatement` with the hypothesis of the version-2 anchors
that every staged family is `StagedPiecesRegular`): almost surely the physical set of the lower walk is the range of a
proper simple curve in `closure ℍ` from `0`. -/
def GW1ParamR51Statement : Prop :=
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
      ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ range γ = SB.lowerWalkSet κ b jumps E ω

/-- **GW1's parametrization for staged families regular at every sample** (`SB.GW1ParamStatement` with
`∀ spec k ω, IsRegularDriver (E spec k ω)`). -/
def GW1ParamEveryRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec k ω, Staged.IsRegularDriver (E spec k ω)) →
      ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ range γ = SB.lowerWalkSet κ b jumps E ω

/-- **R51 reduction**: GW1's parametrization for everywhere regular families gives it for the families of the
version-2 anchors (the regularized family has almost surely the same lower walk). -/
theorem gw1ParamR51Statement_of_everyReg (hG : GW1ParamEveryRegStatement.{u}) : GW1ParamR51Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR
  obtain ⟨hE', hreg', hrun⟩ := regFam_spec hb hE hR
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (regFam E) hE' hreg',
    hrun _ (isBoundaryContinuedProgram_walkR b jumps)] with ω hγ hrω
  obtain ⟨γ, hγ, hγ0, hγR⟩ := hγ
  refine ⟨γ, hγ, hγ0, hγR.trans ?_⟩
  exact physSet_eq_of_run_eq (hrω _)

/-- `SB.GW1ParamStatement` (all staged families) implies its R51 form. -/
theorem gw1ParamR51Statement_of_unreg (hG : SB.GW1ParamStatement.{u}) : GW1ParamR51Statement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h hh W' ζ' hcf hζ' E hE _ => hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- PROVE-T14-GW7's `WalkCont.RightWalkProperRegStatement` is GW1's parametrization in R51 form. -/
theorem rightWalkProperRegStatement_of_gw1ParamR51 (hG : GW1ParamR51Statement.{u}) :
    WalkCont.RightWalkProperRegStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h hh W' ζ' hcf hζ' E hE hR => hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR

/-! ### The finite concatenation of arcs and a proper ray (deterministic) -/

/-- An arc parametrized by `[0, 1]`: continuous and injective there. -/
def IsArc (α : ℝ≥0 → ℂ) : Prop := ContinuousOn α (Iic 1) ∧ InjOn α (Iic 1)

/-- The arc `α` on `[0, 1]`, followed by the ray `ρ`. -/
def concatArc (α ρ : ℝ≥0 → ℂ) (t : ℝ≥0) : ℂ := if t ≤ 1 then α t else ρ (t - 1)

theorem concatArc_zero (α ρ : ℝ≥0 → ℂ) : concatArc α ρ 0 = α 0 := by
  simp only [concatArc, zero_le, ↓reduceIte]

theorem tendsto_sub_one_atTop : Tendsto (fun t : ℝ≥0 => t - 1) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun _ ht => le_tsub_of_add_le_right ht⟩

/-- **An arc followed by a proper ray meeting it only at its endpoint is a proper curve.** -/
theorem isProperCurve_concatArc {α ρ : ℝ≥0 → ℂ} (hα : IsArc α) (hαH : ∀ s ∈ Iic (1 : ℝ≥0), 0 ≤ (α s).im)
    (hρ : Supp9B.IsProperCurve ρ) (h1 : α 1 = ρ 0)
    (hmeet : ∀ s ∈ Iic (1 : ℝ≥0), ∀ t, α s = ρ t → s = 1) : Supp9B.IsProperCurve (concatArc α ρ) := by
  obtain ⟨hρc, hρi, hρH, hρp⟩ := hρ
  refine ⟨?_, fun s t hst => ?_, fun t => ?_, ?_⟩
  · refine continuous_if_le continuous_id continuous_const hα.1
      (hρc.comp (continuous_id.sub continuous_const)).continuousOn fun t ht => ?_
    rw [ht, tsub_self, h1]
  · unfold concatArc at hst
    by_cases hs : s ≤ 1 <;> by_cases ht : t ≤ 1
    · simp only [hs, ht, ↓reduceIte] at hst
      exact hα.2 hs ht hst
    · simp only [hs, ht, ↓reduceIte] at hst
      have hs1 := hmeet s hs _ hst
      subst hs1
      rw [h1] at hst
      exact absurd (tsub_eq_zero_iff_le.1 (hρi hst).symm) ht
    · simp only [hs, ht, ↓reduceIte] at hst
      have ht1 := hmeet t ht _ hst.symm
      subst ht1
      rw [h1] at hst
      exact absurd (tsub_eq_zero_iff_le.1 (hρi hst)) hs
    · simp only [hs, ht, ↓reduceIte] at hst
      exact (tsub_left_inj (not_le.1 hs).le (not_le.1 ht).le).1 (hρi hst)
  · unfold concatArc
    split_ifs with ht
    · exact hαH t ht
    · exact hρH _
  · have e : (fun t => ‖ρ (t - 1)‖) =ᶠ[atTop] fun t => ‖concatArc α ρ t‖ := by
      filter_upwards [eventually_gt_atTop (1 : ℝ≥0)] with t ht
      simp only [concatArc, not_le.2 ht, ↓reduceIte]
    exact (hρp.comp tendsto_sub_one_atTop).congr' e

theorem range_concatArc {α ρ : ℝ≥0 → ℂ} (h1 : α 1 = ρ 0) : range (concatArc α ρ) = α '' Iic 1 ∪ range ρ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    unfold concatArc
    split_ifs with ht
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨t, rfl⟩)
    · exact ⟨s, by simp only [concatArc, show s ≤ 1 from hs, ↓reduceIte]⟩
    · by_cases ht : t = 0
      · subst ht
        exact ⟨1, by simp only [concatArc, le_refl, ↓reduceIte, h1]⟩
      · have hlt : ¬ t + 1 ≤ 1 := by
          rw [not_le]; exact lt_add_of_pos_left 1 (pos_iff_ne_zero.2 ht)
        exact ⟨t + 1, by simp only [concatArc, hlt, ↓reduceIte, add_tsub_cancel_right]⟩

/-- The first point of a list of arcs followed by a ray. -/
def chainStart : List (ℝ≥0 → ℂ) → (ℝ≥0 → ℂ) → ℂ
  | [], ρ => ρ 0
  | α :: _, _ => α 0

/-- The union of a list of arcs (on `[0, 1]`) and a ray. -/
def chainSet (L : List (ℝ≥0 → ℂ)) (ρ : ℝ≥0 → ℂ) : Set ℂ := (⋃ α ∈ L, α '' Iic 1) ∪ range ρ

/-- **A finite chain**: each arc lies in `closure ℍ`, ends at the start of what follows, and meets everything that
follows only at its endpoint. -/
def ChainOK : List (ℝ≥0 → ℂ) → (ℝ≥0 → ℂ) → Prop
  | [], _ => True
  | α :: L, ρ => IsArc α ∧ (∀ s ∈ Iic (1 : ℝ≥0), 0 ≤ (α s).im) ∧ α 1 = chainStart L ρ ∧
      (∀ s ∈ Iic (1 : ℝ≥0), α s ∈ chainSet L ρ → s = 1) ∧ ChainOK L ρ

theorem chainSet_cons (α : ℝ≥0 → ℂ) (L : List (ℝ≥0 → ℂ)) (ρ : ℝ≥0 → ℂ) :
    chainSet (α :: L) ρ = α '' Iic 1 ∪ chainSet L ρ := by
  ext z
  simp only [chainSet, List.mem_cons, mem_union, mem_iUnion, mem_image, exists_prop, mem_range]
  constructor
  · rintro (⟨β, hβ | hβ, hz⟩ | hz)
    · subst hβ; exact Or.inl hz
    · exact Or.inr (Or.inl ⟨β, hβ, hz⟩)
    · exact Or.inr (Or.inr hz)
  · rintro (hz | ⟨β, hβ, hz⟩ | hz)
    · exact Or.inl ⟨α, Or.inl rfl, hz⟩
    · exact Or.inl ⟨β, Or.inr hβ, hz⟩
    · exact Or.inr hz

/-- **The finite union of a chain of arcs and a proper ray is the range of a proper injective curve from its first
point** (GW1, p. 620: "The finite union of the continuous injective pieces and connectors is a continuous injective
curve through its terminal limit"). -/
theorem exists_isProperCurve_of_chainOK {ρ : ℝ≥0 → ℂ} (hρ : Supp9B.IsProperCurve ρ) :
    ∀ {L : List (ℝ≥0 → ℂ)}, ChainOK L ρ →
      ∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = chainStart L ρ ∧ range γ = chainSet L ρ
  | [], _ => ⟨ρ, hρ, rfl, by simp only [chainSet, List.not_mem_nil, iUnion_of_empty, iUnion_empty, empty_union]⟩
  | α :: L, ⟨hα, hαH, h1, hmeet, hL⟩ => by
    obtain ⟨γ, hγ, hγ0, hγR⟩ := exists_isProperCurve_of_chainOK hρ hL
    have h1' : α 1 = γ 0 := h1.trans hγ0.symm
    refine ⟨concatArc α γ, isProperCurve_concatArc hα hαH hγ h1' fun s hs t hst => hmeet s hs ?_,
      concatArc_zero α γ, ?_⟩
    · rw [← hγR]; exact ⟨t, hst.symm⟩
    · rw [range_concatArc h1', hγR, chainSet_cons]

/-! ### A piece stopped at a finite positive time, as an arc on `[0, 1]` -/

/-- The curve `g` on `[0, S]`, run on `[0, 1]`. -/
def rescale (g : ℝ≥0 → ℂ) (S : ℝ≥0) (s : ℝ≥0) : ℂ := g (min s 1 * S)

theorem rescale_zero (g : ℝ≥0 → ℂ) (S : ℝ≥0) : rescale g S 0 = g 0 := by
  simp only [rescale, zero_le, min_eq_left, zero_mul]

theorem rescale_one (g : ℝ≥0 → ℂ) (S : ℝ≥0) : rescale g S 1 = g S := by
  simp only [rescale, min_self, one_mul]

theorem image_rescale {g : ℝ≥0 → ℂ} {S : ℝ≥0} (hS : 0 < S) : rescale g S '' Iic 1 = g '' Iic S := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨min s 1 * S, Set.mem_Iic.2 (mul_le_of_le_one_left (zero_le (a := S)) (min_le_right s 1)), rfl⟩
  · rintro ⟨t, ht, rfl⟩
    have h1 : t / S ≤ 1 := (div_le_one hS).2 ht
    refine ⟨t / S, h1, ?_⟩
    simp only [rescale, min_eq_left h1, div_mul_cancel₀ t hS.ne']

/-- **A curve continuous and injective on `[0, S]`, `0 < S`, run on `[0, 1]` is an arc.** -/
theorem isArc_rescale {g : ℝ≥0 → ℂ} {S : ℝ≥0} (hS : 0 < S) (hc : ContinuousOn g (Iic S))
    (hi : InjOn g (Iic S)) : IsArc (rescale g S) := by
  have hmaps : ∀ s : ℝ≥0, min s 1 * S ∈ Iic S := fun s =>
    Set.mem_Iic.2 (mul_le_of_le_one_left (zero_le (a := S)) (min_le_right s 1))
  refine ⟨(hc.comp_continuous ((continuous_id.min continuous_const).mul continuous_const) hmaps).continuousOn,
    fun s hs s' hs' h => ?_⟩
  have e := hi (hmaps s) (hmaps s') h
  rw [min_eq_left (show s ≤ 1 from hs), min_eq_left (show s' ≤ 1 from hs')] at e
  exact mul_right_cancel₀ hS.ne' e

/-- **The physical points of a regular piece stopped at a finite positive time form an arc** from the image of its
seed to the image of its endpoint, when the boundary extension `f` of the chart is injective on its trace: the tip set
is `rescale (f ∘ α) S '' [0, 1]` (`CounterflowRange.tipSet_stopped_eq_of_tendsto`). -/
theorem exists_isArc_tipSet {c : Chart} {f : ℂ → ℂ} (hf : ∀ p ∈ QuantumZipper.Hbar,
    Tendsto c.2.1 (𝓝[QuantumZipper.H] p) (𝓝 (f p))) {W : ℝ≥0 → ℝ} {S : ℝ≥0} (hS : 0 < S) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace W (S : ℝ≥0∞) α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ (S : ℝ≥0∞)}) (hW0 : W 0 = 0)
    (hinj : InjOn (f ∘ α) (Iic S)) :
    IsArc (rescale (f ∘ α) S) ∧
      rescale (f ∘ α) S '' Iic 1 = c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) (S : ℝ≥0∞)).toNNReal) (S : ℝ≥0∞) ∧
      rescale (f ∘ α) S 0 = f (α 0) ∧ rescale (f ∘ α) S 1 = f (α S) := by
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ QuantumZipper.Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hW.mono fun _ (hs : _ < (S : ℝ≥0∞)) => (le_of_lt hs : _ ≤ (S : ℝ≥0∞)))
      hW0 ht
  have hfc : ContinuousOn f QuantumZipper.Hbar := GW1P.continuousOn_of_tendsto hf
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (S : ℝ≥0∞)} = Iic S := by
    ext t; simp only [mem_ofPred_eq, mem_Iic, ENNReal.coe_le_coe]
  have hαc : ContinuousOn α (Iic S) := hset ▸ hα.2.1
  have hgc : ContinuousOn (f ∘ α) (Iic S) :=
    hfc.comp hαc fun t ht => hαH t (ENNReal.coe_le_coe.2 ht)
  refine ⟨isArc_rescale hS hgc hinj, ?_, rescale_zero _ _, rescale_one _ _⟩
  rw [image_rescale hS, CounterflowRange.tipSet_stopped_eq_of_tendsto hα hW hW0
    fun t ht => hf _ (hαH t ht), hset, image_comp]

/-! ### Wiring into PROVE-T14-GW7's no-common-continuum reduction -/

/-- **The walks share no nondegenerate continuum (R51 form)** from GW1's parametrization (R51 form), Theorem 1.3
(frozen type; it gives the connector sides through GW0) and the piece statements. -/
theorem walkNoCommonContinuumRegStatement_of_gw1Param (hG : GW1ParamR51Statement.{u})
    (hT13 : Exist.Theorem13Statement.{0}) (hN : WalkCont.WalkPieceContinuumRegStatement.{u}) :
    WalkCont.WalkNoCommonContinuumRegStatement.{u} :=
  WalkCont.walkNoCommonContinuumRegStatement_of_pieces (rightWalkProperRegStatement_of_gw1ParamR51 hG)
    (walkConnectorSideRegStatement_of_theorem13 hT13) hN

end GW1X

end Theorem14

end InteractingSLE
