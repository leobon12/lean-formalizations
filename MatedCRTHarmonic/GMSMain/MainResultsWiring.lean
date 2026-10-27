import MatedCRTHarmonic.GMSMain.MainResultsAnchors
import MatedCRTHarmonic.GMSMain.T16DFinal
import MatedCRTHarmonic.GMSMain.EpsBFinal

/-!
# The real-mesh results assembled into the main theorems

The chain for [18] Theorem 1.5 and Corollary 1.6 at every real mesh `ε ∈ (0, 1)` :

* `EpsBFinal`: [18] Lemma 3.11 (3.35) at every real `ε`, for every coupling and `ρ ∈ (0, 1)`,
  `EpsB.lemma311Real_of_coupling` — with the rate `α` chosen **after** `ρ`;
* T15B (`T15BModel`): Theorem 1.5 at every real `ε` from (3.35) at real `ε`: `theorem15_coupling_real` (input with
  `α` uniform in `ρ`) and `theorem15_coupling_real_perRho` (input with `α = α(ρ)`; then Theorem 1.5's `α` is chosen
  after `ρ`);
* T16D (`T16DFinal`, `T16DCorollary16`): the draft's `IsLUB` form of (1.6) and existence of `f_ε`
  (`holderBad_subset_t15b`, `measure_embeddingBad`), the Corollary 1.6 bad-event inclusion `tutteEdgeBad_subset`
  (`f = Re, Im`, adjacent cells intersect) and Lemma 2.7 at real `ε` (`lemma27_cellAt`).

Results:
* `theorem15PerRhoBody_of_coupling` — **[18] Theorem 1.5 at every real `ε`, with `α` chosen after `ρ`, NO input**;
* `corollary16Body_of_perRho`, **`corollary16Body_of_coupling`** — Corollary 1.6 needs Theorem 1.5 only at one radius
  (its statement has no rate), so **the two Corollary 1.6 anchors hold with NO input**:
  `matedCRT_tutte_edge_le_of_matingOfTrees_holds`, `matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected_holds`;
* `theorem15Input_of_lemma311Uniform` — named input 3 of `MainResultsInputs` from the finer input `Lemma311UniformInput`
  ((3.35) at every real `ε` with `α` chosen before `ρ`; using the uniform-rate form), hence the two Theorem 1.5
  anchors `…_of_lemma311Uniform`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

open MatedCRTHarmonic GMS3

/-! ### Theorem 1.5 with the rate chosen after the radius -/

variable {Ω : Type} [MeasurableSpace Ω]

/-- **[18] Theorem 1.5, draft form, with `α` chosen after `ρ`** (one coupling): as `Theorem15Body` with
`∀ ρ, ∃ α` in place of `∃ α, ∀ ρ`. -/
def Theorem15PerRhoBody (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ α : ℝ, 0 < α ∧ ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
    ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsConnected D → IsConnected Dᶜ →
    ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier D)) →
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
        (∃ g : ℤ → ℝ,
          IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g) ∧
        ∀ g : ℤ → ℝ,
          IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g →
          ∀ x ∈ verticesMeeting (cell ε (η ω)) D,
            ∀ y ∈ verticesMeeting (cell ε (η ω)) D,
              |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
        ENNReal.ofReal (C * ε ^ α)

/-- The draft Theorem 1.5 (`∃ α, ∀ ρ`) implies the per-radius form. -/
theorem theorem15PerRhoBody_of_theorem15Body {P : Measure Ω} {η : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (h : Theorem15Body P η bm) : Theorem15PerRhoBody P η bm := by
  obtain ⟨α, hα, h⟩ := h
  exact fun ρ hρ0 hρ1 => ⟨α, hα, h ρ hρ0 hρ1⟩

omit [MeasurableSpace Ω] in
/-- The good event of (3.35) is T15B's (`∀ x, H.cell x = …` versus `H.cell = fun x => …`). -/
theorem lemma311GoodAt_compl_subset {bm : Ω → MatedCRT.Path2} {η : Ω → C(ℝ, ℂ)} {ε ρ β p : ℝ} :
    (T15B.Lemma311GoodAt bm η ε ρ β p)ᶜ ⊆ (EpsB.Lemma311GoodReal bm η ε ρ β p)ᶜ := by
  intro ω hω hgood
  apply hω
  obtain ⟨h, H, hcell, h311⟩ := hgood
  exact ⟨h, H, funext hcell, h311⟩

section Coupling

variable {γ : ℝ} {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] (3.35) at every real `ε`, per radius, in T15B's input shape** (`lemma311Real_of_coupling`). -/
theorem lemma311PerRho_of_coupling (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ α₁ : ℝ, 0 < α₁ ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C₁ : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (T15B.Lemma311GoodAt bm η ε ρ' β p)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ α₁) := by
  intro ρ' h0 h1
  obtain ⟨α, hα, β, hβ, p, hp, C, hC⟩ := EpsB.lemma311Real_of_coupling D hstd hγ h0 h1
  exact ⟨α, hα, β, hβ, p, hp, C, fun ε hε hε1 =>
    (measure_mono lemma311GoodAt_compl_subset).trans (hC ε hε hε1)⟩

/-- **T15B's bad event of (1.9) controls the draft's** (T16D: existence of `f_ε` off a null set, and the `IsLUB` form
implies the `sSup` form). -/
theorem measure_holderBad_le (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {Dom : Set ℂ} (hDb : Bornology.IsBounded Dom) {f : ℂ → ℝ} (hfc : ContinuousOn f (frontier Dom))
    {A₀ ξ ε : ℝ} (hε : 0 < ε) :
    P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
        (∃ g : ℤ → ℝ,
          IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) Dom f g) ∧
        ∀ g : ℤ → ℝ,
          IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) Dom f g →
          ∀ x ∈ verticesMeeting (cell ε (η ω)) Dom,
            ∀ y ∈ verticesMeeting (cell ε (η ω)) Dom,
              |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
      P (T15B.HolderBadAt bm η Dom f A₀ ξ ε) := by
  have hsub : T16D.HolderBad bm η Dom f A₀ ξ ε ⊆
      T15B.HolderBadAt bm η Dom f A₀ ξ ε ∪ T16D.EmbeddingBad bm η ε :=
    T16D.holderBad_subset_t15b hDb hfc
  calc P (T16D.HolderBad bm η Dom f A₀ ξ ε)
      ≤ P (T15B.HolderBadAt bm η Dom f A₀ ξ ε ∪ T16D.EmbeddingBad bm η ε) := measure_mono hsub
    _ ≤ P (T15B.HolderBadAt bm η Dom f A₀ ξ ε) + P (T16D.EmbeddingBad bm η ε) := measure_union_le _ _
    _ = P (T15B.HolderBadAt bm η Dom f A₀ ξ ε) := by rw [T16D.measure_embeddingBad D hε, add_zero]

/-- **[18] Theorem 1.5 at every real `ε`, with `α` chosen after `ρ`, for every frozen coupling, with NO input**
(the real-mesh (3.35), T15B's `theorem15_coupling_real_perRho`, T16D's adapters). -/
theorem theorem15PerRhoBody_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) : Theorem15PerRhoBody P η bm := by
  intro ρ hρ hρ1
  obtain ⟨α, hα, h⟩ :=
    T15B.theorem15_coupling_real_perRho D hstd hγ (lemma311PerRho_of_coupling D hstd hγ) ρ hρ hρ1
  refine ⟨α, hα, fun χ hχ => ?_⟩
  obtain ⟨ξ, hξ, h⟩ := h χ hχ
  refine ⟨ξ, hξ, fun Dom hDo hDsub hc hcc f hf => ?_⟩
  obtain ⟨A₀, hA₀, C, hC⟩ := h Dom hDo hDsub hc hcc f hf
  obtain ⟨K, hK⟩ := hf
  exact ⟨A₀, hA₀, C, fun ε hε hε1 =>
    (measure_holderBad_le D (isBounded_ball.subset hDsub) (hK.continuousOn hχ) hε).trans (hC ε hε hε1)⟩

/-- **[18] Corollary 1.6 from [18] Theorem 1.5 at each radius** (one coupling): Corollary 1.6 has no rate, so it only
needs Theorem 1.5 at the radius `ρ` itself ( the proof of T16D's `corollary16_of_theorem15` with the
rate of Theorem 1.5 chosen after `ρ`). -/
theorem corollary16Body_of_perRho (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) (h15 : Theorem15PerRhoBody P η bm) :
    Corollary16Body P η bm := by
  intro ρ hρ0 hρ1
  obtain ⟨α₁, hα₁, h15'⟩ := h15 ρ hρ0 hρ1
  set q : ℝ := 1 / (2 + γ) ^ 2 with hqdef
  have hden : 4 < (2 + γ) ^ 2 := by nlinarith [hγ.1]
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hq' : q < 2 / (2 + γ) ^ 2 := by
    rw [hqdef]; exact div_lt_div_of_pos_right (by norm_num) (by linarith)
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one (by linarith)]; linarith
  have hL := GMSLemma27.lemma27Exponent_pos hγ.1 hq0 hq'
  set α₃ : ℝ := GMSLemma27.lemma27Exponent q γ / 2 with hα₃def
  have hα₃ : 0 < α₃ := by rw [hα₃def]; linarith
  obtain ⟨ξ, hξ, hξD⟩ := h15' 1 one_pos
  obtain ⟨C₃, -, hC₃⟩ := T16D.lemma27_cellAt D hstd hγ hq0 hq' ⟨hρ0, hρ1⟩ (α := α₃) (by rw [hα₃def]; linarith)
  refine ⟨q * ξ, mul_pos hq0 hξ, fun Dom hDo hDsub hc hcc => ?_⟩
  obtain ⟨A₁, hA₁, C₁, hC₁⟩ := hξD Dom hDo hDsub hc hcc (fun z => z.re) ⟨1, T16D.holderOnWith_re _⟩
  obtain ⟨A₂, hA₂, C₂, hC₂⟩ := hξD Dom hDo hDsub hc hcc (fun z => z.im) ⟨1, T16D.holderOnWith_im _⟩
  set α := min α₁ α₃ with hαdef
  have hα : 0 < α := lt_min hα₁ hα₃
  set K : ℝ := |C₁| + |C₂| + |C₃| with hKdef
  have hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →
      P (T16D.TutteEdgeBad bm η Dom ((A₁ + A₂) * 2 ^ ξ) (q * ξ) ε) ≤ ENNReal.ofReal (K * ε ^ α) := by
    intro ε hε hε1
    have hle : ∀ (C a : ℝ), α ≤ a → ENNReal.ofReal (C * ε ^ a) ≤ ENNReal.ofReal (|C| * ε ^ α) :=
      fun C a ha => ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_abs_self C)
        (Real.rpow_nonneg hε.le _)).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hε hε1.le ha) (abs_nonneg C)))
    calc P (T16D.TutteEdgeBad bm η Dom ((A₁ + A₂) * 2 ^ ξ) (q * ξ) ε)
        ≤ P (T16D.HolderBad bm η Dom (fun z => z.re) A₁ ξ ε ∪ T16D.HolderBad bm η Dom (fun z => z.im) A₂ ξ ε ∪
            T16D.CellDiamBad η ρ q ε ∪ T16D.EmbeddingBad bm η ε) :=
          measure_mono (T16D.tutteEdgeBad_subset hε hε1.le hq1 hξ hA₁.le hA₂.le hDsub)
      _ ≤ P (T16D.HolderBad bm η Dom (fun z => z.re) A₁ ξ ε) +
            P (T16D.HolderBad bm η Dom (fun z => z.im) A₂ ξ ε) +
            P (T16D.CellDiamBad η ρ q ε) + P (T16D.EmbeddingBad bm η ε) :=
          (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
      _ ≤ ENNReal.ofReal (|C₁| * ε ^ α) + ENNReal.ofReal (|C₂| * ε ^ α) +
            ENNReal.ofReal (|C₃| * ε ^ α) + 0 := by
          refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) (le_of_eq (T16D.measure_embeddingBad D hε))
          · exact (hC₁ ε hε hε1).trans (hle C₁ α₁ (min_le_left _ _))
          · exact (hC₂ ε hε hε1).trans (hle C₂ α₁ (min_le_left _ _))
          · exact (hC₃ ε ⟨hε, hε1⟩).trans (hle C₃ α₃ (min_le_right _ _))
      _ = ENNReal.ofReal (K * ε ^ α) := by
          have hr := Real.rpow_nonneg hε.le α
          rw [add_zero, ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hr) (mul_nonneg (abs_nonneg _) hr),
            ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (abs_nonneg _) hr) (mul_nonneg (abs_nonneg _) hr))
              (mul_nonneg (abs_nonneg _) hr)]
          congr 1
          rw [hKdef]
          ring
  refine ⟨(A₁ + A₂) * 2 ^ ξ, ?_⟩
  have hup : Tendsto (fun ε : ℝ => ENNReal.ofReal (K * ε ^ α)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ α) (𝓝[>] 0) (𝓝 0) :=
      (GMSLemma27.tendsto_rpow_nhdsGT_zero hα).mono_right nhdsWithin_le_nhds
    have := ENNReal.tendsto_ofReal (h0.const_mul K)
    rwa [mul_zero, ENNReal.ofReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
  exact hbound ε hε.1 hε.2

/-- **[18] Corollary 1.6 (main form) for every frozen coupling, every real `ε`, with NO input.** -/
theorem corollary16Body_of_coupling (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) : Corollary16Body P η bm :=
  corollary16Body_of_perRho D hstd hγ (theorem15PerRhoBody_of_coupling D hstd hγ)

end Coupling

/-! ### The finer input for Theorem 1.5 (rate chosen before the radius) -/

/-- **Uniform-rate input for Theorem 1.5: [18] (3.35) at every real `ε ∈ (0, 1)` with
the rate `α₁` chosen BEFORE the ambient radius `ρ'`** (`α` depends only on `γ`), for every frozen
coupling, using `EpsB.Lemma311GoodReal`. The existing `lemma311Real_of_coupling` has the
same body with `∀ ρ', ∃ α₁`. -/
def Lemma311UniformInput : Prop :=
  ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 2 → ∀ (Ω : Type) [MeasurableSpace Ω], StandardBorelSpace Ω →
    ∀ (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
      MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
      ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C₁ : ℝ,
        ∀ ε : ℝ, 0 < ε → ε < 1 → P (EpsB.Lemma311GoodReal bm η ε ρ' β p)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ α₁)

/-- **Named input 3 from the finer input**: [18] Theorem 1.5 (draft main form) for every coupling from (3.35) at
every real `ε` with a rate uniform in the radius (T15B's `theorem15_coupling_real`, T16D's adapters). -/
theorem theorem15Input_of_lemma311Uniform (h : Lemma311UniformInput) : Theorem15Input := by
  intro γ hγ Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D
  obtain ⟨α₁, hα₁, h311⟩ := h γ hγ Ω hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D
  have h311' : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C₁ : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (T15B.Lemma311GoodAt bm η ε ρ' β p)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ α₁) := by
    refine ⟨α₁, hα₁, fun ρ' h0 h1 => ?_⟩
    obtain ⟨β, hβ, p, hp, C₁, hC₁⟩ := h311 ρ' h0 h1
    exact ⟨β, hβ, p, hp, C₁, fun ε hε hε1 => (measure_mono lemma311GoodAt_compl_subset).trans (hC₁ ε hε hε1)⟩
  obtain ⟨α, hα, h15⟩ := T15B.theorem15_coupling_real D hstd hγ h311'
  refine ⟨α, hα, fun ρ hρ hρ1 χ hχ => ?_⟩
  obtain ⟨ξ, hξ, h15⟩ := h15 ρ hρ hρ1 χ hχ
  refine ⟨ξ, hξ, fun Dom hDo hDsub hc hcc f hf => ?_⟩
  obtain ⟨A₀, hA₀, C, hC⟩ := h15 Dom hDo hDsub hc hcc f hf
  obtain ⟨K, hK⟩ := hf
  exact ⟨A₀, hA₀, C, fun ε hε hε1 =>
    (measure_holderBad_le D (isBounded_ball.subset hDsub) (hK.continuousOn hχ) hε).trans (hC ε hε hε1)⟩

/-! ### The anchors with the fewest inputs (verbatim statements, local names of `MainResultsDraft`) -/

/-- **[18] Corollary 1.6 (main form, (a)) on every mating-of-trees coupling — NO input.** -/
theorem matedCRT_tutte_edge_le_of_matingOfTrees_holds :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
          ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsConnected D → IsConnected Dᶜ →
          ∃ C : ℝ, Tendsto (fun ε : ℝ =>
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              (∃ Φ : ℤ → ℂ,
                IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D Φ) ∧
              ∀ Φ : ℤ → ℂ,
                IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D Φ →
                ∀ e : MatedCRT.Edge ε (bm ω),
                  (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (cell ε (η ω)) D →
                  (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (cell ε (η ω)) D →
                    ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                      C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) :=
  fun _ hγ0 hγ2 _ _ hstd _ _ _ _ _ _ _ _ _ _ _ _ _ D => corollary16Body_of_coupling D hstd ⟨hγ0, hγ2⟩

/-- **[18] Corollary 1.6 (literal form, (b)) on every mating-of-trees coupling — NO input** (main form and
TOPO). -/
theorem matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected_holds :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
          ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → SimplyConnectedSpace D →
          ∃ C : ℝ, Tendsto (fun ε : ℝ =>
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              (∃ Φ : ℤ → ℂ,
                IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D Φ) ∧
              ∀ Φ : ℤ → ℂ,
                IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D Φ →
                ∀ e : MatedCRT.Edge ε (bm ω),
                  (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (cell ε (η ω)) D →
                  (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (cell ε (η ω)) D →
                    ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                      C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) :=
  fun _ hγ0 hγ2 _ _ hstd _ _ _ _ _ _ _ _ _ _ _ _ _ D =>
    corollary16SCBody_of_corollary16Body (corollary16Body_of_coupling D hstd ⟨hγ0, hγ2⟩)

/-- **[18] Theorem 1.5 (main form) on every mating-of-trees coupling, from the finer input** `Lemma311UniformInput`
(`α` before `ρ`). -/
theorem matedCRT_holder_of_matingOfTrees_of_lemma311Uniform (h : Lemma311UniformInput) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
          ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsConnected D → IsConnected Dᶜ →
          ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier D)) →
          ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              (∃ g : ℤ → ℝ,
                IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g) ∧
              ∀ g : ℤ → ℝ,
                IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g →
                ∀ x ∈ verticesMeeting (cell ε (η ω)) D,
                  ∀ y ∈ verticesMeeting (cell ε (η ω)) D,
                    |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
              ENNReal.ofReal (C * ε ^ α) :=
  matedCRT_holder_of_matingOfTrees_of_inputs (theorem15Input_of_lemma311Uniform h)

/-- **[18] Theorem 1.5 (literal form) on every mating-of-trees coupling, from the finer input**
`Lemma311UniformInput` (`α` before `ρ`). -/
theorem matedCRT_holder_of_matingOfTrees_simplyConnected_of_lemma311Uniform (h : Lemma311UniformInput) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
          ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → SimplyConnectedSpace D →
          ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier D)) →
          ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              (∃ g : ℤ → ℝ,
                IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g) ∧
              ∀ g : ℤ → ℝ,
                IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g →
                ∀ x ∈ verticesMeeting (cell ε (η ω)) D,
                  ∀ y ∈ verticesMeeting (cell ε (η ω)) D,
                    |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
              ENNReal.ofReal (C * ε ^ α) :=
  matedCRT_holder_of_matingOfTrees_simplyConnected_of_inputs (theorem15Input_of_lemma311Uniform h)

end MatedCRTHarmonic.GMSMain.MainResults
