/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.QSchedInput

/-!
# The restart law at one switch, under a regular conditional law

Packet PROVE-QSCHED. The conditional worlds of a staged history are nested: the world after `k + 1` pieces is, for
almost every world after `k` pieces, a conditional law of it. Their conditional counterflow statements are not
measurable events, so they are carried along the filter `stageFilter` (iterated `Filter.bind` of the regular
conditional laws) and only the final, measurable, first-contact event is brought back to `P`.

* `stageFilter`, `stageFilter_of_ae`, `ae_of_stageFilter`: the nested almost-sure filters; almost-sure properties
  hold along them, and a measurable event along them holds almost surely.
* `CfStage`: in the conditional world `condExpKernel P 𝒢 ω₀`, a null modification of the stage field carries a
  centred counterflow with infinite lifetime whose trace is the physical counterflow read in the chart `C`.
* **`ae_cfStage_succ`**: one switch (Lemma 5.7's proof, p. 138: "the boundary data for the GFF which describes the
  evolution of `ψ(η′)` is as in the right panel of Figure 5.5"): from `CfStage` before a piece and the restart law
  `CounterflowGivenPrefix44Statement`, `CfStage` after it, for almost every world after the piece.
* **`ae_firstHit_of_cfStage`**: the one-angle Lemma 4.7 in a conditional world: the image counterflow first contacts
  the piece's prefix at its tip, at every positive rational time.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.QSched

open WangWu (negInv)
open Prop411Q (IsFirstHitQ)
open Sec7.Lemma71I (realPath)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.FlowReflect (reflData reflJumps)
open Prop513Schedule (ExtremeHeights)
open Exist Exist.Staged Exist.StagedLaw

/-! ### Nested almost-sure filters -/

section Filter

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒢 : ℕ → MeasurableSpace Ω}

/-- **The nested almost-sure filter of a sequence of σ-algebras**: `∀ᶠ ω in stageFilter P 𝒢 (k + 1), p ω` means
that for `stageFilter P 𝒢 k`-almost every `ω₀`, `p` holds almost surely under `condExpKernel P (𝒢 k) ω₀`. -/
def stageFilter (P : Measure Ω) [IsFiniteMeasure P] (𝒢 : ℕ → MeasurableSpace Ω) : ℕ → Filter Ω
  | 0 => ae P
  | k + 1 => (stageFilter P 𝒢 k).bind fun ω₀ => ae (condExpKernel P (𝒢 k) ω₀)

theorem eventually_stageFilter_succ {k : ℕ} {p : Ω → Prop} :
    (∀ᶠ ω in stageFilter P 𝒢 (k + 1), p ω) ↔
      ∀ᶠ ω₀ in stageFilter P 𝒢 k, ∀ᵐ ω ∂(condExpKernel P (𝒢 k) ω₀), p ω :=
  Filter.eventually_bind

/-- **Almost-sure properties hold along the nested filters.** -/
theorem stageFilter_of_ae (h𝒢 : ∀ k, 𝒢 k ≤ mΩ) :
    ∀ (k : ℕ) {p : Ω → Prop}, (∀ᵐ ω ∂P, p ω) → ∀ᶠ ω in stageFilter P 𝒢 k, p ω
  | 0, _, h => h
  | k + 1, _, h => eventually_stageFilter_succ.2
      (stageFilter_of_ae h𝒢 k (Sec7.Aux122Disint.ae_ae_condExpKernel (h𝒢 k) h))

/-- **A measurable event along the nested filters holds almost surely.** -/
theorem ae_of_stageFilter (h𝒢 : ∀ k, 𝒢 k ≤ mΩ) :
    ∀ (k : ℕ) {A : Set Ω}, MeasurableSet A → (∀ᶠ ω in stageFilter P 𝒢 k, ω ∈ A) → ∀ᵐ ω ∂P, ω ∈ A
  | 0, _, _, h => h
  | k + 1, A, hA, h => by
    have h1 := eventually_stageFilter_succ.1 h
    have hB : MeasurableSet {ω₀ | condExpKernel P (𝒢 k) ω₀ Aᶜ = 0} :=
      ((measurable_condExpKernel hA.compl).mono (h𝒢 k) le_rfl) (measurableSet_singleton 0)
    have h2 : ∀ᵐ ω₀ ∂P, ω₀ ∈ {ω₀ | condExpKernel P (𝒢 k) ω₀ Aᶜ = 0} :=
      ae_of_stageFilter h𝒢 k hB (h1.mono fun ω₀ hω₀ => ae_iff.1 hω₀)
    exact Lemma56Stages.ae_of_ae_condExpKernel (h𝒢 k) hA (h2.mono fun ω₀ hω₀ => ae_iff.2 hω₀)

end Filter

/-! ### The conditional counterflow of a stage -/

section Stage

variable {Ω : Type u} {𝒢 𝒢' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

variable (𝒢) in
/-- **The conditional counterflow of a stage**: under `condExpKernel P 𝒢 ω₀` a null modification `Z` of the stage
field `Y` carries a centred counterflow (driver `W′`, infinite lifetime, trace `η′`), and almost surely a continuous
increasing clock `ℓ` from `0` carries `η′` to the physical counterflow `γ` read in the chart `C`:
`R(γ(ℓ u)) = C(R(η′(u)))` (`R = negInv`), with `R(η′(u)) ∈ ℍ` if `inner` holds. -/
def CfStage (κ : ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (Y : Ω → DistOn upperHalfPlaneOpens) (C : Ω → ℂ → ℂ) (γ : Ω → ℝ≥0 → ℂ) (inner : Prop) (ω₀ : Ω) : Prop :=
  ∃ (Z : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (η' : Ω → ℝ≥0 → ℂ),
    Measurable Z ∧ Z =ᵐ[condExpKernel P 𝒢 ω₀] Y ∧
    IsCenteredCounterflowDriver κ (condExpKernel P 𝒢 ω₀) Z W' ζ' ∧
    (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ζ' ω = ⊤) ∧
    ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), IsGeneratingTrace (fun t => W' t ω) ⊤ (η' ω) ∧
      ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
        ∀ u : ℝ≥0, 0 < u → (inner → negInv (η' ω u) ∈ H) ∧ negInv (γ ω (ℓ u)) = C ω (negInv (η' ω u))

/-- The field and the piece of a stage, read for a null modification of the stage field. -/
theorem stage_field_of_cfStage {κ : ℝ} (hκ : 0 < κ) {Y Z : Ω → DistOn upperHalfPlaneOpens}
    {ω₀ : Ω} (hZm : Measurable Z) (hZY : Z =ᵐ[condExpKernel P 𝒢 ω₀] Y) {β : Restart.BoundaryWord}
    (hYG : IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Y β.fn β.jumps) {θ : ℝ} {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {h' : Ω → DistOn upperHalfPlaneOpens}
    (hD : IsFlowLineDriver κ β.fn β.jumps θ (condExpKernel P 𝒢 ω₀) h' (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    (hYh' : Y =ᵐ[condExpKernel P 𝒢 ω₀] h') :
    IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Z β.fn β.jumps ∧
      IsFlowLineDriver κ β.fn β.jumps θ (condExpKernel P 𝒢 ω₀) Z (fun t ω => (D ω).1 t) (fun ω => (D ω).2) := by
  have hZG := isGFFWithBoundaryData_congr_ae hYG hZm hZY.symm
  exact ⟨hZG, isFlowLineDriver_congr_field hκ β.isPiecewiseConstantBoundaryData hD hZG (hZY.trans hYh')⟩

/-- **One switch** (Lemma 5.7's proof, p. 138). Before the piece `D` (an angle-`±π/2` flow line of the stage field,
whose word has `ExtremeHeights`), the conditional counterflow of the stage is `CfStage`; the restart law
`CounterflowGivenPrefix44Statement` at the piece's own time `t₀` gives, for almost every world after the piece
(`htower`: the conditional law given the piece's record is the next stage's conditional law), the conditional
counterflow of the next stage, whose field is the stage field read in the record chart (`hY′`) and whose chart is
the old chart after the inverse Loewner map of the piece (`hC′`). -/
theorem ae_cfStage_succ (hcg : CounterflowGivenPrefix44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Y Y' : Ω → DistOn upperHalfPlaneOpens} {C C' : Ω → ℂ → ℂ}
    {γ : Ω → ℝ≥0 → ℂ} {inner inner' : Prop} {ω₀ : Ω} (hst : CfStage 𝒢 κ P Y C γ inner ω₀)
    {β : Restart.BoundaryWord} (hβ : ExtremeHeights κ β)
    (hYG : IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Y β.fn β.jumps) {θ : ℝ} (hθ : θ = -(π / 2) ∨ θ = π / 2)
    {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : Measurable D) (hDr : ∀ ω, IsRegularDriver (D ω))
    (hDtop : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (D ω).2 = ⊤) {h' : Ω → DistOn upperHalfPlaneOpens}
    (hD : IsFlowLineDriver κ β.fn β.jumps θ (condExpKernel P 𝒢 ω₀) h' (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    (hYh' : Y =ᵐ[condExpKernel P 𝒢 ω₀] h') (t₀ : ℝ≥0)
    (htower : ∀ᵐ ω₁ ∂(condExpKernel P 𝒢 ω₀),
      condExpKernel (condExpKernel P 𝒢 ω₀)
        (MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance) ω₁ = condExpKernel P 𝒢' ω₁)
    (hY' : ∀ᵐ ω₁ ∂(condExpKernel P 𝒢 ω₀), ∀ᵐ ω ∂(condExpKernel P 𝒢' ω₁),
      Y' ω = recField κ (recOf (t₀ : ℝ≥0∞) (D ω₁)) (Y ω))
    (hC' : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ z ∈ H, C' ω z = C ω (fwdMapInv (Ito.rpath (D ω).1) t₀ z)) :
    ∀ᵐ ω₁ ∂(condExpKernel P 𝒢 ω₀), CfStage 𝒢' κ P Y' C' γ inner' ω₁ := by
  obtain ⟨Z, W', ζ', η', hZm, hZY, hcf, hζ', hpath⟩ := hst
  obtain ⟨hZG, hZD⟩ := stage_field_of_cfStage hκ hZm hZY hYG hD hYh'
  set R : Ω → RecData := fun ω => recOf (t₀ : ℝ≥0∞) (D ω) with hRdef
  have hRm : Measurable R := measurable_recOf hDm hDr _
  have hRle : MeasurableSpace.comap R inferInstance ≤ mΩ := hRm.comap_le
  obtain ⟨W'', ζ'', η'', hK, hpath''⟩ := hcg κ β.fn β.jumps (condExpKernel P 𝒢 ω₀) Z W' ζ' hκ hκ4
    β.isPiecewiseConstantBoundaryData hZG hcf hζ' θ (mem_Icc_of_extreme hθ) (heights44_of_extreme hβ hθ) D hDm hDr
    hZD t₀ η' (hpath.mono fun ω hω => hω.1)
  -- the combined pathwise relation, under the stage law
  have hG : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧
      ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
        ∀ u : ℝ≥0, 0 < u → (inner' → negInv (η'' ω u) ∈ H) ∧
          negInv (γ ω (ℓ u)) = C' ω (negInv (η'' ω u)) := by
    filter_upwards [hpath, hpath'', hC', hDtop] with ω hp hp'' hc htop
    obtain ⟨-, ℓ₁, hℓ₁c, hℓ₁m, hℓ₁0, hrel₁⟩ := hp
    obtain ⟨hgen, ℓ₂, hℓ₂c, hℓ₂m, hℓ₂0, hrel₂⟩ := hp''
    refine ⟨hgen, ℓ₁ ∘ ℓ₂, hℓ₁c.comp hℓ₂c, hℓ₁m.comp hℓ₂m, by simp only [comp_apply, hℓ₂0, hℓ₁0],
      fun u hu => ⟨fun _ => (hrel₂ u hu).1, ?_⟩⟩
    have hu₂ : 0 < ℓ₂ u := by rw [← hℓ₂0]; exact hℓ₂m hu
    rw [comp_apply, (hrel₁ (ℓ₂ u) hu₂).2, (hrel₂ u hu).2,
      Sec7.StripWall.recChart_inv_eq (hDr ω) htop t₀ (hrel₂ u hu).1, hc _ (hrel₂ u hu).1]
  have hGK := Sec7.Aux122Disint.ae_ae_condExpKernel (P := condExpKernel P 𝒢 ω₀) hRle hG
  have hZK := Sec7.Aux122Disint.ae_ae_condExpKernel (P := condExpKernel P 𝒢 ω₀) hRle hZY
  filter_upwards [hK, htower, hGK, hZK, hY'] with ω₁ hK₁ ht₁ hG₁ hZ₁ hY₁
  rw [ht₁] at hK₁ hG₁ hZ₁
  refine ⟨fun ω => recField κ (R ω₁) (Z ω), W'', ζ'', η'', measurable_recField_comp κ measurable_const hZm,
    ?_, hK₁.1, hK₁.2, hG₁⟩
  filter_upwards [hZ₁, hY₁] with ω h1 h2
  rw [h2, h1]

/-- **The one-angle Lemma 4.7 in a conditional world**: if the stage carries its conditional counterflow (`CfStage`)
and `D` is an angle-`±π/2` flow line of the stage field (word with `ExtremeHeights`) with trace `Γ`, then almost surely
the image counterflow `η₂` (read in `C` through the clock `ℓ`) first contacts `Γ((0, r])` at `Γ(r)` for every
positive rational `r` (Lemma 4.7 at `π/2`, the reflection for `−π/2`). -/
theorem ae_firstHit_of_cfStage (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Y : Ω → DistOn upperHalfPlaneOpens} {C : Ω → ℂ → ℂ} {γ : Ω → ℝ≥0 → ℂ}
    {inner : Prop} {ω₀ : Ω} (hst : CfStage 𝒢 κ P Y C γ inner ω₀) {β : Restart.BoundaryWord}
    (hβ : ExtremeHeights κ β) (hYG : IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Y β.fn β.jumps) {θ : ℝ}
    (hθ : θ = -(π / 2) ∨ θ = π / 2) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hD : IsFlowLineDriver κ β.fn β.jumps θ (condExpKernel P 𝒢 ω₀) h' (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    (hYh' : Y =ᵐ[condExpKernel P 𝒢 ω₀] h') {Γ : Ω → ℝ≥0 → ℂ}
    (hΓ : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), IsGeneratingTrace (D ω).1 (D ω).2 (Γ ω)) :
    ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∃ (η₂ : ℝ≥0 → ℂ) (ℓ : ℝ≥0 → ℝ≥0), Continuous η₂ ∧ Continuous ℓ ∧
      StrictMono ℓ ∧ ℓ 0 = 0 ∧
      (∀ u : ℝ≥0, 0 < u → (inner → negInv (η₂ u) ∈ H) ∧ negInv (γ ω (ℓ u)) = C ω (negInv (η₂ u))) ∧
      ∀ r : ℚ, 0 < r → IsFirstHitQ (realPath (Γ ω)) (fun s : ℝ => η₂ s.toNNReal) r := by
  obtain ⟨Z, W', ζ', η', hZm, hZY, hcf, hζ', hpath⟩ := hst
  obtain ⟨hZG, hZD⟩ := stage_field_of_cfStage hκ hZm hZY hYG hD hYh'
  have hZfl : IsFlowLine κ β.fn β.jumps 0 θ (condExpKernel P 𝒢 ω₀) Z Γ (fun ω => (D ω).2) :=
    Sec7.StripWall.isFlowLine_of_isFlowLineDriver hZD hΓ
  have h47' := RestartGen.lemma47QHitTStatement_pi_div_two h47
  have hhgt : (RestartGen.Lemma47QHitTStatement.{u} θ ∧ IsHeightBounded44 κ β.fn β.jumps θ ∧
        IsHeightBounded44 κ β.fn β.jumps (π / 2)) ∨
      (RestartGen.Lemma47QHitTStatement.{u} (-θ) ∧ IsHeightBounded44 κ (reflData β.fn) (reflJumps β.jumps) (-θ) ∧
        IsHeightBounded44 κ (reflData β.fn) (reflJumps β.jumps) (π / 2)) := by
    rcases hθ with rfl | rfl
    · refine Or.inr ⟨by rw [neg_neg]; exact h47', ?_⟩
      rw [neg_neg]
      exact ⟨isHeightBounded44_refl_of_extremeHeights hβ, isHeightBounded44_refl_of_extremeHeights hβ⟩
    · exact Or.inl ⟨h47', isHeightBounded44_of_extremeHeights hβ, isHeightBounded44_of_extremeHeights hβ⟩
  have hfirst := RestartSw.ae_forall_isFirstHitQ_of_heights href hκ hκ4 β.isPiecewiseConstantBoundaryData hhgt hZG
    hcf hζ' (hpath.mono fun ω hω => hω.1) hZfl
  filter_upwards [hfirst, hpath] with ω hf hp
  obtain ⟨hgen, ℓ, hℓc, hℓm, hℓ0, hrel⟩ := hp
  exact ⟨η' ω, ℓ, continuousOn_univ.1 (hgen.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top), hℓc, hℓm,
    hℓ0, hrel, hf⟩

end Stage

end InteractingSLE.Sec5.QSched
