/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.DeterminationGraph
import InteractingSLE.Spec.Supplement.LPProbDetermination
import InteractingSLE.Spec.Sec7.ContinuityProbInduction

/-!
# Determination for every coupling: Aux. lemmas 52–55 (§D.2.1–§D.2.2) and Theorem 1.2's route

Packet PROVE-AUX52-55. Sources: §D.2 of `source/external/AstraIG1/ig1_followup_proofs.txt` (ruling R38),
lines 1976–2068; the specification's Aux. lemmas 52–55 and the proof of Lemma 7.5 (`source/spec/p241-288.md`
L69–L131, L224–L271, pp. 244–252); Corollary LP11's proof (`p481-528.md` L180–L215, pp. 488–489).

## The reduction

§D.2.2: "At an own-filtration stopping time, Aux. 53 restarts the original optional hull specification in the
active chart. If the old record is field-measurable, this chart and its transformed active field are
field-measurable too. The local comparison therefore supplies a longer field-measurable history. […] Apply the
lemma above [Aux. 52] and let `N` increase."

Lemma 7.5's proof (p. 252): "At every own-filtration stopping time strictly before the continuation threshold, that
[Aux.] lemma constructs a positive additional stopped driving history determined by the previous history and the
active field." The specification's reduction (p. 251): "Truncation at a finite horizon or at the continuation
threshold is a measurable operation on the revealed integrated history. Aux. lemma 52 therefore proves field
determination of the entire finite-force driving evolution under the two-seed input".

* `HasFieldLocalExtensions` is the output of Aux. lemmas 53 and 55 at own-filtration stops: at every stopping time
  `τ ≤ T_*` of the frozen driving filtration there is a stopping time `σ ∈ [τ, T_*]`, strictly larger on
  `{τ < T_*}`, whose stopped history is a Borel function of the field together with the stopped history at `τ`
  (the active chart and the transformed active field are measurable functions of these two).
* `hasFieldLocalRestarts_of_hasFieldLocalExtensions` proves (LG1) of Aux. lemma 52 from it — the composition of
  determinations and the **truncation at the finite horizon** (`isAEDeterminedBy_stoppedHistory_min`: the history
  stopped at `σ ∧ N` is a measurable function of the history stopped at `σ`, by continuity of the completed driving
  state on `[0, T_*]`, Aux. lemma 3).
* `aux55RestartStatement_of_localExtension`: the named input `LP.Aux55RestartStatement` of LP7 and LP11 follows
  from `LocalExtensionStatement` (Aux. 53 + 55 at own-filtration stops).
* `hasFieldDeterminedHistories_of_localExtension`: Aux. lemma 52 then gives determination of the killed driving
  history for every ordered force word and every `κ > 0` ("Aux. lemmas 55 and 52 apply for every positive
  parameter", p. 252).
* `lemma75DeterminationStatement_of_inputs`: **Lemma 7.5 with Aux. 52–55**, the named input
  `LP.Lemma75DeterminationStatement` of LP11, from Proposition 7.3 (determination and trace of the two-seed
  couplings, the packet's "universal two-seed determining graphs") and `LocalExtensionStatement`.
* `exists_measurable_lifetime_trace_eq_comp_field_of_localExtension`: **the conclusion of the frozen Theorem 1.2**
  for every `κ > 0` from the two-seed input and `LocalExtensionStatement` (with LP11's reconstruction of the full
  trace, §D.2.4, `LP.exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory`).
* `twoSeed_exists_common_graph`, `twoSeed_map_field_killedHistory_eq`: under the two-seed input, the two-seed
  reference couplings share one graph and one field–history law (Aux. 55, p. 250: "Its determining function is the
  same for every such reference coupling […] Thus one reference version may be fixed once and for all").

## What is not proved here

`LocalExtensionStatement` itself (Aux. lemmas 53–55: the whole-field Cameron–Martin change (HL1)–(HL4), the Girsanov
identification of the stopped two-seed driving law (HL5)–(HL7), the reference field and its local-set property
(HL8)–(HL9), the extension by one fixed reference (Aux. 54, local-set part) and the restart of the specification in
the active chart (Aux. 53)). See `planning/handoffs/PROVE-AUX52-55.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Determination

open Sec7

/-! ### Composition of determinations and truncation of a stopped history -/

section Truncate

variable {Ω E β γ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [MeasurableSpace β] [MeasurableSpace γ]

/-- Determinations compose. -/
theorem _root_.InteractingSLE.Sec7.IsAEDeterminedBy.trans {H : Ω → γ} {Z : Ω → β} {δ : Type*} [MeasurableSpace δ] {Y : Ω → δ}
    (hY : IsAEDeterminedBy μ Z Y) (hZ : IsAEDeterminedBy μ H Z) : IsAEDeterminedBy μ H Y := by
  obtain ⟨g, hg, hYg⟩ := hY
  obtain ⟨g', hg', hZg⟩ := hZ
  refine ⟨g ∘ g', hg.comp hg', ?_⟩
  filter_upwards [hYg, hZg] with ω h1 h2
  simp only [Function.comp_apply, h1, h2]

/-- A variable determines itself. -/
theorem isAEDeterminedBy_self {H : Ω → γ} : IsAEDeterminedBy μ H H :=
  ⟨id, measurable_id, ae_of_all _ fun _ => rfl⟩

variable [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/-- **Truncation at a finite horizon is a measurable operation on the revealed history** (p. 251). If the paths of
`X` are continuous on `[0, B]` and `σ ≤ B`, the history stopped at `σ ∧ N` is determined by whatever determines the
history stopped at `σ`. -/
theorem isAEDeterminedBy_stoppedHistory_min {X : ℝ≥0 → Ω → E} {σ B : Ω → WithTop ℝ≥0}
    (hσB : ∀ ω, σ ω ≤ B ω)
    (hX : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ B ω}) {H : Ω → γ}
    (hH : Measurable H) (hdet : IsAEDeterminedBy μ H (stoppedHistory X σ)) (N : ℝ≥0) :
    IsAEDeterminedBy μ H (stoppedHistory X fun ω => min (σ ω) N) := by
  obtain ⟨r, hr⟩ := exists_seq_nnrat_tendsto N
  refine (hdet.comp (measurable_fst.min measurable_const)).prodMk (isAEDeterminedBy_pi fun q => ?_)
  refine IsAEDeterminedBy.of_tendsto hH
    (fun n => hdet.comp ((measurable_pi_apply (min q (r n))).comp measurable_snd)) ?_
  filter_upwards [hX] with ω hω
  have hq : Tendsto (fun n => ((min q (r n) : ℚ≥0) : ℝ≥0)) atTop (𝓝 (min (q : ℝ≥0) N)) := by
    have : (fun n => ((min q (r n) : ℚ≥0) : ℝ≥0)) = fun n => min (q : ℝ≥0) ((r n : ℚ≥0) : ℝ≥0) := by
      funext n; exact NNRat.cast_min q (r n)
    rw [this]
    exact tendsto_const_nhds.min hr
  simp only [Function.comp_apply, stoppedHistory]
  cases hσω : σ ω with
  | top =>
    have hB : B ω = ⊤ := top_le_iff.1 (hσω ▸ hσB ω)
    have hmin : stopAt (fun ω => min (σ ω) (N : WithTop ℝ≥0)) q ω = min (q : ℝ≥0) N := by
      simp only [stopAt, hσω]
      rw [min_eq_right le_top, WithTop.untopD_coe]
    have hst : ∀ n, stopAt σ ((min q (r n) : ℚ≥0) : ℝ≥0) ω = min ((min q (r n) : ℚ≥0) : ℝ≥0) (q : ℝ≥0) := by
      intro n
      simp only [stopAt, hσω, WithTop.untopD_top]
      rw [min_self, eq_comm, min_eq_left]
      rw [NNRat.cast_min]; exact min_le_left _ _
    rw [hmin]
    simp only [hst]
    have h := tendsto_comp_min_of_continuousOn hω (s := (q : ℝ≥0)) (by rw [hB]; exact le_top) hq
    rwa [min_eq_left (min_le_left _ _)] at h
  | coe s =>
    have hs : (s : WithTop ℝ≥0) ≤ B ω := hσω ▸ hσB ω
    have hmin : stopAt (fun ω => min (σ ω) (N : WithTop ℝ≥0)) q ω = min (min (q : ℝ≥0) N) s := by
      simp only [stopAt, hσω]
      rw [← WithTop.coe_min, WithTop.untopD_coe, min_comm s N, min_assoc]
    have hst : ∀ n, stopAt σ ((min q (r n) : ℚ≥0) : ℝ≥0) ω = min ((min q (r n) : ℚ≥0) : ℝ≥0) s := by
      intro n
      simp only [stopAt, hσω, WithTop.untopD_coe]
    rw [hmin]
    simp only [hst]
    exact tendsto_comp_min_of_continuousOn hω hs hq

end Truncate

/-! ### The output of Aux. lemmas 53 and 55 at own-filtration stops, and (LG1) -/

section Restart

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **The local extensions of Aux. lemmas 53 and 55 at own-filtration stops** (Lemma 7.5's proof, p. 252: "At every
own-filtration stopping time strictly before the continuation threshold, that lemma constructs a positive
additional stopped driving history determined by the previous history and the active field"; §D.2.2). For every
`𝓖`-stopping time `τ ≤ T_*` there is a `𝓖`-stopping time `σ` with `τ ≤ σ ≤ T_*` and `σ > τ` almost surely on
`{τ < T_*}`, whose stopped history of the completed driving state is almost surely a Borel function of the field
together with the stopped history at `τ` (the active chart and the transformed active field are measurable
functions of these two). -/
def HasFieldLocalExtensions {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ ω, τ ω ≤ (ζ ω : WithTop ℝ≥0)) →
    ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 σ ∧ (∀ ω, τ ω ≤ σ ω) ∧ (∀ ω, σ ω ≤ (ζ ω : WithTop ℝ≥0)) ∧
      (∀ᵐ ω ∂P, τ ω < (ζ ω : WithTop ℝ≥0) → τ ω < σ ω) ∧
      IsAEDeterminedBy P (fun ω => (h ω, stoppedHistory (completedState W VL VR ζ) τ ω))
        (stoppedHistory (completedState W VL VR ζ) σ)

/-- **(LG1) of Aux. lemma 52 from the local extensions** (§D.2.2 and p. 251: the composition of the
determinations, and the truncation at the finite horizon `N`). -/
theorem hasFieldLocalRestarts_of_hasFieldLocalExtensions (hκ : 0 < κ) [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) {𝓖 : Filtration ℝ≥0 mΩ}
    (hext : HasFieldLocalExtensions P 𝓖 h W VL VR ζ) : LP.HasFieldLocalRestarts P 𝓖 h W VL VR ζ := by
  intro τ N hτ hτle hdet
  obtain ⟨σ₀, hσ₀, hτσ₀, hσ₀ζ, hlt, hdet₀⟩ := hext τ hτ fun ω => (hτle ω).trans (min_le_left _ _)
  refine ⟨fun ω => min (σ₀ ω) N, hσ₀.min_const N, fun ω => min_le_min (hσ₀ζ ω) le_rfl,
    hlt.mono fun ω hω => ⟨le_min (hτσ₀ ω) ((hτle ω).trans (min_le_right _ _)), fun hτN => ?_⟩, ?_⟩
  · exact lt_min (hω (lt_of_lt_of_le hτN (min_le_left _ _))) (lt_of_lt_of_le hτN (min_le_right _ _))
  · have hd : IsAEDeterminedBy P h (stoppedHistory (completedState W VL VR ζ) σ₀) :=
      hdet₀.trans (isAEDeterminedBy_self.prodMk hdet)
    exact isAEDeterminedBy_stoppedHistory_min (B := fun ω => (ζ ω : WithTop ℝ≥0)) hσ₀ζ
      (ae_continuousOn_completedState hκ hC.1) hC.2.1 hd N

/-- **Named input: Aux. lemmas 53 and 55 at own-filtration stops** (specification pp. 244–251; §D.2.2 of the
follow-up note), parameter-free: under the two-seed input, every coupling of an ordered force word satisfying the
optional hull specification has the local extensions `HasFieldLocalExtensions` in its own driving filtration. -/
def LocalExtensionStatement (κ : ℝ) : Prop :=
  LP.TwoSeedGraphInput.{u} κ →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      IsOrderedForceWord xL xR →
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
        (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
        ∀ hX : IsMeasurableKilledDriving W VL VR ζ,
          HasFieldLocalExtensions P (drivingFiltration P hX) h W VL VR ζ

/-- The named input `LP.Aux55RestartStatement` (LP7, LP11) follows from `LocalExtensionStatement`. -/
theorem aux55RestartStatement_of_localExtension (hκ : 0 < κ) (hext : LocalExtensionStatement.{u} κ) :
    LP.Aux55RestartStatement.{u} κ := by
  intro h2 nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ h hC hX
  exact hasFieldLocalRestarts_of_hasFieldLocalExtensions hκ hC
    (hext h2 xL xR ρL ρR hF P 𝓕 W VL VR B ζ h hC hX)

/-- **Determination for every coupling, every `κ > 0`** (Aux. lemmas 52–55; p. 252: "Aux. lemmas 55 and 52 apply
for every positive parameter"): under the two-seed input and the restart property, the killed driving history of
every coupling of every ordered force word satisfying the optional hull specification is a Borel function of the
field. -/
theorem hasFieldDeterminedHistories_of_aux55 (hκ : 0 < κ) (h2 : LP.TwoSeedGraphInput.{u} κ)
    (h55 : LP.Aux55RestartStatement.{u} κ) (hF : IsOrderedForceWord xL xR) :
    LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ h hC
  obtain ⟨hX, -⟩ := hC.2.2.2
  exact LP.isFieldDeterminedHistory_of_hasFieldLocalRestarts hκ hC
    (h55 h2 xL xR ρL ρR hF P 𝓕 W VL VR B ζ h hC hX)

/-- `hasFieldDeterminedHistories_of_aux55` from `LocalExtensionStatement`. -/
theorem hasFieldDeterminedHistories_of_localExtension (hκ : 0 < κ) (h2 : LP.TwoSeedGraphInput.{u} κ)
    (hext : LocalExtensionStatement.{u} κ) (hF : IsOrderedForceWord xL xR) :
    LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR :=
  hasFieldDeterminedHistories_of_aux55 hκ h2 (aux55RestartStatement_of_localExtension hκ hext) hF

/-- **The conclusion of the frozen Theorem 1.2 for every `κ > 0`** from the two-seed input and the local extensions
of Aux. 53–55, with LP11's measurable reconstruction of the full trace (§D.2.4). -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_localExtension (hκ : 0 < κ)
    (h2 : LP.TwoSeedGraphInput.{u} κ) (hext : LocalExtensionStatement.{u} κ) (hF : IsOrderedForceWord xL xR)
    [IsProbabilityMeasure P] (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  LP.exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory hC
    (hasFieldDeterminedHistories_of_localExtension hκ h2 hext hF P 𝓕 W VL VR B ζ h hC)

end Restart

/-! ### `0 < κ < 4`: Lemma 7.5 with Aux. 52–55 from Proposition 7.3 -/

/-- **Named input: Proposition 7.3, determination** (Specification p. 242; Lemma 7.5's proof, p. 252: "Proposition
7.3 gives field determination and one common joint law for every original two-seed coupling with admissible seed
weights"; the packet's "universal two-seed determining graphs"). For `0 < κ < 4` and `r_L, r_R > −2`, every
coupling of the two-seed word `SLE_κ(r_L; r_R)` satisfying the optional hull specification has a field-determined
killed driving history. -/
def Prop73DeterminationStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
    LP.HasFieldDeterminedHistories.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR)

/-- Proposition 7.3 (determination and trace) supplies the two-seed input of Aux. lemma 55 for `0 < κ < 4` (Lemma
7.5's proof, p. 252: "It therefore supplies the reference input of Aux. lemma 55 for every seed-weight pair"). -/
theorem twoSeedGraphInput_of_prop73 (h73d : Prop73DeterminationStatement.{u})
    (h73t : Sec7.Prop73TraceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    LP.TwoSeedGraphInput.{u} κ := by
  intro rL rR hL hR
  refine ⟨h73d κ hκ hκ4 rL rR hL hR, fun P _ 𝓕 W VL VR B ζ hE => ?_⟩
  have hc := h73t κ hκ hκ4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) (fun _ => rfl)
    (fun _ => rfl) (fun _ => hL) (fun _ => hR) P 𝓕 W VL VR B ζ hE
  filter_upwards [hc] with ω hω
  obtain ⟨η, hη, -⟩ := hω
  exact ⟨η, hη⟩

/-- **Lemma 7.5 with Aux. 52–55** (the named input `LP.Lemma75DeterminationStatement` of LP11), from Proposition 7.3
and the restart property of Aux. 53–55 (`LP.Aux55RestartStatement`). -/
theorem lemma75DeterminationStatement_of_aux55 (h73d : Prop73DeterminationStatement.{u})
    (h73t : Sec7.Prop73TraceStatement.{u})
    (h55 : ∀ κ : ℝ, 0 < κ → κ < 4 → LP.Aux55RestartStatement.{u} κ) :
    LP.Lemma75DeterminationStatement.{u} :=
  fun κ hκ hκ4 _ _ _ _ _ _ hF =>
    hasFieldDeterminedHistories_of_aux55 hκ (twoSeedGraphInput_of_prop73 h73d h73t hκ hκ4) (h55 κ hκ hκ4) hF

/-- **Lemma 7.5 with Aux. 52–55** (`LP.Lemma75DeterminationStatement`), from Proposition 7.3 and the local extensions
of Aux. 53–55 (`LocalExtensionStatement`). -/
theorem lemma75DeterminationStatement_of_inputs (h73d : Prop73DeterminationStatement.{u})
    (h73t : Sec7.Prop73TraceStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExtensionStatement.{u} κ) :
    LP.Lemma75DeterminationStatement.{u} :=
  lemma75DeterminationStatement_of_aux55 h73d h73t fun κ hκ hκ4 =>
    aux55RestartStatement_of_localExtension hκ (hext κ hκ hκ4)

/-- **Corollary LP7 (`k > 4`) from the local extensions**: `LP.lp7DeterminationStatement_of_inputs` with Aux. 53–55
in the form `LocalExtensionStatement`. -/
theorem lp7DeterminationStatement_of_localExtension (hR7d : LP.R7DeterminationStatement.{u})
    (hR7t : LP.TheoremR7TraceStatement.{u}) (h725d : LP.Lemma725DeterminationStatement.{u})
    (h725t : LP.Lemma725TraceStatement.{u}) (hext : ∀ κ : ℝ, 4 < κ → LocalExtensionStatement.{u} κ) :
    LP.LP7DeterminationStatement.{u} :=
  LP.lp7DeterminationStatement_of_inputs hR7d hR7t h725d h725t fun κ hκ =>
    aux55RestartStatement_of_localExtension (by linarith) (hext κ hκ)

/-! ### One fixed reference version of the two-seed graphs -/

section TwoSeed

variable {κ : ℝ} {rL rR : ℝ} {Ω₁ Ω₂ : Type u} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
  {W₁ : ℝ≥0 → Ω₁ → ℝ} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
  {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞} {ζ₂ : Ω₂ → ℝ≥0∞}
  {h₁ : Ω₁ → LQGMetric.DistOn upperHalfPlaneOpens} {h₂ : Ω₂ → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **One reference version of each two-seed graph** (Aux. 55, p. 250: "Its determining function is the same for
every such reference coupling. Indeed, if two couplings gave different functions, mixing them by an independent fair
coin would still satisfy the original hull specification and optional locality […]. Thus one reference version may
be fixed once and for all"). -/
theorem twoSeed_exists_common_graph [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h2 : LP.TwoSeedGraphInput.{u} κ) (hL : -2 < rL) (hR : -2 < rR)
    (hC₁ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    ∃ Ψ, Measurable Ψ ∧ IsHistoryGraph P₁ h₁ W₁ VL₁ VR₁ ζ₁ Ψ ∧ IsHistoryGraph P₂ h₂ W₂ VL₂ VR₂ ζ₂ Ψ :=
  exists_common_graph (h2 rL rR hL hR).1 hC₁ hC₂

/-- Under the two-seed input, the two-seed couplings have one joint law of the field and the killed history. -/
theorem twoSeed_map_field_killedHistory_eq [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h2 : LP.TwoSeedGraphInput.{u} κ) (hL : -2 < rL) (hR : -2 < rR)
    (hC₁ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    P₁.map (fun ω => (h₁ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      P₂.map (fun ω => (h₂ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω)) :=
  map_field_killedHistory_eq (h2 rL rR hL hR).1 hC₁ hC₂

end TwoSeed

end Determination

end InteractingSLE
