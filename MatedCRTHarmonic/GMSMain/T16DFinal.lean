import MatedCRTHarmonic.GMSMain.T16DCorollary16
import MatedCRTHarmonic.GMSMain.T15BModel

/-!
# [18] Corollary 1.6 from Theorem 1.5

The Theorem 1.5 hypothesis `h15` of `corollary16_tendsto_of_theorem15` (the shape of the draft anchor
`matedCRT_holder_of_matingOfTrees`, main form) is discharged by real-mesh Theorem 1.5,
`GMSMain.T15B.theorem15_coupling_real` (`GMSMain/T15BModel.lean`), whose good event asserts (1.9) for every discrete
harmonic extension in T15B's `sSup` form. Two adapters:

* existence of the harmonic extension (the `∃ g` clause of the draft's good event) is T16D's: on the a.s. cellular
  embedding at mesh `ε`, `isHarmonicExtension_dirichletSol` (`holderBad_subset_t15b`, with `EmbeddingBad` null);
* the draft's `IsLUB` predicate implies T15B's `sSup` predicate for compact cells and `f` continuous on `∂D`
  (`isHarmonicExtension_iff_sSup`; Hölder data are continuous).

Results, for every frozen coupling `D`, every real mesh `ε ∈ (0, 1)`, CONDITIONAL on ONE named input — T15B's own
input `h311`, [18] (3.35) at every real `ε` in T15A's shape (`T15B.Lemma311GoodAt`):

* `theorem15_of_t15b` — [18] Theorem 1.5 in the draft anchor's shape (existence + `IsLUB` predicate);
* **`corollary16_of_t15b`** (quantitative (1.10)), **`corollary16_tendsto_of_t15b`** ((1.10) as printed, the body of
  the draft anchor `matedCRT_tutte_edge_le_of_matingOfTrees`, main form) and
  **`corollary16_tendsto_simplyConnected_of_t15b`** (the body of the literal anchor
  `matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.T16D

open MatedCRTHarmonic GMS3

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

omit [MeasurableSpace Ω] in
/-- **The draft-form bad event of (1.9) is covered by T15B's bad event and `EmbeddingBad`**: off `EmbeddingBad` the
harmonic extension exists (T16D), and every `IsLUB`-form extension is an `sSup`-form one (compact cells, `f` continuous
on `∂D`). -/
theorem holderBad_subset_t15b {Dom : Set ℂ} (hDb : Bornology.IsBounded Dom) {f : ℂ → ℝ}
    (hf : ContinuousOn f (frontier Dom)) {A₀ ξ ε : ℝ} :
    HolderBad bm η Dom f A₀ ξ ε ⊆ T15B.HolderBadAt bm η Dom f A₀ ξ ε ∪ EmbeddingBad bm η ε := by
  intro ω hω
  by_contra hcon
  simp only [mem_union, not_or] at hcon
  obtain ⟨h15, hemb⟩ := hcon
  simp only [T15B.HolderBadAt, EmbeddingBad, mem_compl_iff, mem_ofPred_eq, not_not] at h15 hemb
  obtain ⟨h, hb⟩ := h15
  obtain ⟨h', H, hH⟩ := hemb
  apply hω
  refine ⟨h, ⟨dirichletSol (MatedCRT.graph ε (bm ω) h') (vBd H Dom) (bdryVal H Dom f), ?_⟩, fun g hg => ?_⟩
  · have hex := isHarmonicExtension_dirichletSol H hDb hf
    rw [hH] at hex
    exact hex
  · have hJ : ∀ x, IsCompact (cellAt ε (η ω) x) := fun x => isCompact_Icc.image (η ω).continuous
    exact hb g ((isHarmonicExtension_iff_sSup hJ hf g).mp hg)

variable (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)

include D in
/-- **[18] Theorem 1.5 in the shape of the draft anchor `matedCRT_holder_of_matingOfTrees`** ( main form; good
event: the harmonic extension exists and every one satisfies (1.9)) for every frozen coupling at every real mesh, from
T15B's `theorem15_coupling_real`, CONDITIONAL on T15B's named input `h311` ([18] (3.35) at every real `ε`). -/
theorem theorem15_of_t15b (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (h311 : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C₁ : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (T15B.Lemma311GoodAt bm η ε ρ' β p)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ α₁)) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsConnected Dom → IsConnected Domᶜ →
      ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier Dom)) →
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
          (∃ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g) ∧
          ∀ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g →
            ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, ∀ y ∈ verticesMeeting (cellAt ε (η ω)) Dom,
              |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
          ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨α, hα, h⟩ := T15B.theorem15_coupling_real D hstd hγ h311
  refine ⟨α, hα, fun ρ hρ0 hρ1 χ hχ => ?_⟩
  obtain ⟨ξ, hξ, hD⟩ := h ρ hρ0 hρ1 χ hχ
  refine ⟨ξ, hξ, fun Dom hDo hDsub hc hcc f hf => ?_⟩
  obtain ⟨A₀, hA₀, C, hC⟩ := hD Dom hDo hDsub hc hcc f hf
  obtain ⟨K, hK⟩ := hf
  have hfc : ContinuousOn f (frontier Dom) := hK.continuousOn hχ
  have hDb : Bornology.IsBounded Dom := isBounded_ball.subset hDsub
  refine ⟨A₀, hA₀, C, fun ε hε hε1 => ?_⟩
  calc P (HolderBad bm η Dom f A₀ ξ ε)
      ≤ P (T15B.HolderBadAt bm η Dom f A₀ ξ ε ∪ EmbeddingBad bm η ε) :=
        measure_mono (holderBad_subset_t15b hDb hfc)
    _ ≤ P (T15B.HolderBadAt bm η Dom f A₀ ξ ε) + P (EmbeddingBad bm η ε) := measure_union_le _ _
    _ = P (T15B.HolderBadAt bm η Dom f A₀ ξ ε) := by rw [measure_embeddingBad D hε, add_zero]
    _ ≤ ENNReal.ofReal (C * ε ^ α) := hC ε hε hε1

include D in
/-- **[18] Corollary 1.6, quantitative form**, for every frozen coupling at every real mesh, CONDITIONAL on T15B's
named input `h311` ([18] (3.35) at real `ε`): `∃ α > 0, ∀ ρ ∈ (0, 1), ∃ ξ' > 0, ∀` open connected
`D ⊂ B_ρ(0)` with `ℂ \ D` connected, `∃ C ≥ 0, K, ∀ ε ∈ (0, 1)`, `P[(1.10) fails with constant C] ≤ K ε^α`. -/
theorem corollary16_of_t15b (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (h311 : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C₁ : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (T15B.Lemma311GoodAt bm η ε ρ' β p)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ α₁)) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsConnected Dom → IsConnected Domᶜ →
        ∃ C : ℝ, 0 ≤ C ∧ ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
          P (TutteEdgeBad bm η Dom C ξ' ε) ≤ ENNReal.ofReal (K * ε ^ α) :=
  corollary16_of_theorem15 D hstd hγ (theorem15_of_t15b D hstd hγ h311)

include D in
/-- **[18] Corollary 1.6, (1.10) as printed, main form** (the body of the draft anchor
`matedCRT_tutte_edge_le_of_matingOfTrees`, main form), for every frozen coupling at every real mesh, CONDITIONAL
on T15B's named input `h311` ([18] (3.35) at real `ε`). -/
theorem corollary16_tendsto_of_t15b (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (h311 : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C₁ : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (T15B.Lemma311GoodAt bm η ε ρ' β p)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ α₁)) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsConnected Dom → IsConnected Domᶜ →
      ∃ C : ℝ, Tendsto (fun ε : ℝ =>
        P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
          (∃ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ) ∧
          ∀ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ →
            ∀ e : MatedCRT.Edge ε (bm ω),
              (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (cellAt ε (η ω)) Dom →
              (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (cellAt ε (η ω)) Dom →
                ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                  C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) :=
  corollary16_tendsto_of_theorem15 D hstd hγ (theorem15_of_t15b D hstd hγ h311)

include D in
/-- **[18] Corollary 1.6, (1.10) as printed, literal form** ("`D` simply connected"; the body of the draft anchor
`matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected`, (b)), for every frozen coupling at every real mesh,
CONDITIONAL on T15B's named input `h311` ([18] (3.35) at real `ε`). -/
theorem corollary16_tendsto_simplyConnected_of_t15b (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (h311 : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C₁ : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (T15B.Lemma311GoodAt bm η ε ρ' β p)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ α₁)) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → SimplyConnectedSpace Dom →
      ∃ C : ℝ, Tendsto (fun ε : ℝ =>
        P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
          (∃ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ) ∧
          ∀ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ →
            ∀ e : MatedCRT.Edge ε (bm ω),
              (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (cellAt ε (η ω)) Dom →
              (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (cellAt ε (η ω)) Dom →
                ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                  C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) :=
  corollary16_tendsto_simplyConnected_of_theorem15 D hstd hγ (theorem15_of_t15b D hstd hγ h311)

end Bundle

end MatedCRTHarmonic.GMSMain.T16D
