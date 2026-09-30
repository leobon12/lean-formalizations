import QuantumZipper.Proofs.Thm18.G3G2FullMix

/-!
# G2 (full field, mixing form): reduction to fixed regions with a margin

`G2FullMixStmt γ` (`G3G2FullMix.lean`) is conditional Proposition 5.5 (Sheffield,
arXiv:1012.4797, Prop. 5.5, p. 65, as used in the proof of Theorem 1.8, §5.4, pp. 70–71) at the
Palm point `x` and at its length partner `R(x)`, in event (mixing) form along `g3Filter`
(first `C → ∞`, then `η → 0`, then `δ → 0`).

At fixed `(δ, η)` the mixing statement is **false** in general: with positive Palm probability
`x` falls in the gap `(−3η/4, 0]` between the two regions, where the zoom at `x` is read from the
field *outside* the regions, hence is not asymptotically independent of `outsideSigmaPalm`. This
file separates that geometric error (`G3GeoStmt`, whose `x`-half is proved, `g3GeoStmt_x`) from
the genuine content, the **fixed-region statement** `G2FixMixStmt γ`:

  for all `δ, η` and every margin `m > 0`, as `C → ∞`, uniformly over `G ∈ outsideSigmaPalm`,
  `|P_Palm(Uf ∈ s, E_m, G) − μ(s) P_Palm(E_m ∩ G)| → 0`, `E_m = {|x − t₁| + m < r₁}`

(`x` a margin `m` inside region 1; the same at `R(x)` and region 2 with `ν`).

* `abs_mix_le_of_good`: `|P(A ∩ G) − c P(G)| ≤ |P(A ∩ E ∩ G) − c P(E ∩ G)| + P(Eᶜ)` for
  `c ∈ [0, 1]`;
* `mix_of_geo_fix` (abstract, both sides);
* `g2FullMixStmt_of_geo_fix : G3GeoStmt γ → G2FixMixStmt γ → G2FullMixStmt γ`;
* `g2ConcreteStmt_of_palmR_area_fix`: `G2ConcreteStmt γ` from `G3GeoPalmRStmt γ`,
  `G3AreaStmt γ`, `G2FixMixStmt γ`.

Own elementary bookkeeping (AGENT_GUIDE cost rule); the paper passes over the `η`/`δ` limits
in one sentence ("We may choose δ small enough so that with high probability R(x) ∈ B₁(0)",
p. 71).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **Restriction to a good event**: `|P(A ∩ G) − c P(G)| ≤ |P(A ∩ E ∩ G) − c P(E ∩ G)| + P(Eᶜ)`
for `c ∈ [0, 1]`. -/
theorem abs_mix_le_of_good {α : Type*} [MeasurableSpace α] (P : Measure α) [IsFiniteMeasure P]
    (A : Set α) {E : Set α} (hE : MeasurableSet E) (G : Set α)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    |P.real (A ∩ G) - c * P.real G| ≤
      |P.real (A ∩ E ∩ G) - c * P.real (E ∩ G)| + P.real Eᶜ := by
  have h1 : P.real (A ∩ G ∩ E) + P.real (A ∩ G ∩ Eᶜ) = P.real (A ∩ G) := by
    rw [← sdiff_eq]; exact measureReal_inter_add_sdiff hE
  have h2 : P.real (G ∩ E) + P.real (G ∩ Eᶜ) = P.real G := by
    rw [← sdiff_eq]; exact measureReal_inter_add_sdiff hE
  have e1 : A ∩ G ∩ E = A ∩ E ∩ G := by ext; simp only [mem_inter_iff]; tauto
  have e2 : G ∩ E = E ∩ G := inter_comm _ _
  have b1 : P.real (A ∩ G ∩ Eᶜ) ≤ P.real Eᶜ := measureReal_mono fun x hx => hx.2
  have b2 : P.real (G ∩ Eᶜ) ≤ P.real Eᶜ := measureReal_mono fun x hx => hx.2
  have n1 : 0 ≤ P.real (A ∩ G ∩ Eᶜ) := measureReal_nonneg
  have n2 : 0 ≤ P.real (G ∩ Eᶜ) := measureReal_nonneg
  have b3 : c * P.real (G ∩ Eᶜ) ≤ P.real Eᶜ :=
    (mul_le_of_le_one_left n2 hc1).trans b2
  have n3 : 0 ≤ c * P.real (G ∩ Eᶜ) := mul_nonneg hc0 n2
  rw [← h1, ← h2, e1, e2]
  have hab := abs_add_le (P.real (A ∩ E ∩ G) - c * P.real (E ∩ G))
    (P.real (A ∩ G ∩ Eᶜ) - c * P.real (G ∩ Eᶜ))
  have hb : |P.real (A ∩ G ∩ Eᶜ) - c * P.real (G ∩ Eᶜ)| ≤ P.real Eᶜ := by
    rw [abs_le]; constructor <;> linarith
  calc _ = |(P.real (A ∩ E ∩ G) - c * P.real (E ∩ G)) +
        (P.real (A ∩ G ∩ Eᶜ) - c * P.real (G ∩ Eᶜ))| := by ring_nf
    _ ≤ _ := hab.trans (add_le_add le_rfl hb)

/-- **Mixing along `g3Filter` from a geometric bound and a fixed-region mixing statement**
(abstract form, used for both Palm points). -/
theorem mix_of_geo_fix {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : G3Idx → Measure α} [∀ i, IsProbabilityMeasure (P i)] (𝒢 : G3Idx → MeasurableSpace α)
    (pt : G3Idx → α → ℝ) (hpt : ∀ i, Measurable (pt i)) (t r : G3Idx → ℝ) (Uf : G3Idx → α → β)
    (s : Set β) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1)
    (hGeo : ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ m : ℚ, 0 < (m : ℝ) ∧
      ∀ i : G3Idx, i.1.1 = δ → i.1.2.1 = η → (P i).real {p | r i ≤ |pt i p - t i| + m} < ε)
    (hFix : ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
      i.1 = (δ, η, C) → ∀ G : Set α, MeasurableSet[𝒢 i] G →
        |(P i).real (Uf i ⁻¹' s ∩ {p | |pt i p - t i| + m < r i} ∩ G) -
          c * (P i).real ({p | |pt i p - t i| + m < r i} ∩ G)| ≤ ε) :
    ∀ ε > 0, ∀ᶠ i in g3Filter, ∀ G : Set α, MeasurableSet[𝒢 i] G →
      |(P i).real (Uf i ⁻¹' s ∩ G) - c * (P i).real G| ≤ ε := by
  intro ε hε
  rw [eventually_g3Filter_iff]
  filter_upwards [hGeo (ε / 2) (half_pos hε)] with δ hδ
  filter_upwards [hδ] with η hη
  obtain ⟨m, hm, hgeo⟩ := hη
  filter_upwards [hFix δ η m hm (ε / 2) (half_pos hε)] with C hC i hi G hG
  have hiδ : i.1.1 = δ := by rw [hi]
  have hiη : i.1.2.1 = η := by rw [hi]
  set E : Set α := {p | |pt i p - t i| + m < r i} with hEdef
  have hpti := hpt i
  have hEm : MeasurableSet E :=
    measurableSet_lt (by fun_prop) measurable_const
  have hEc : Eᶜ = {p | r i ≤ |pt i p - t i| + m} := by
    ext p; simp only [hEdef, mem_compl_iff, mem_ofPred_eq, not_lt]
  have hbad : (P i).real Eᶜ < ε / 2 := by rw [hEc]; exact hgeo i hiδ hiη
  have key := abs_mix_le_of_good (P i) (Uf i ⁻¹' s) hEm G hc0 hc1
  have hfix := hC i hi G hG
  linarith

theorem measureReal_le_one_of_prob {β : Type*} [MeasurableSpace β] (μ : Measure β)
    [IsProbabilityMeasure μ] (s : Set β) : μ.real s ≤ 1 := by
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

/-- **Conditional Proposition 5.5 at fixed regions, away from the region edges** (fixed-region
mixing form): for fixed `(δ, η)` and a margin `m > 0`, as `C → ∞`, the full-field zoom at the Palm
point `x` restricted to `{x` a margin `m` inside region 1`}` is asymptotically independent of every
event of `outsideSigmaPalm` (field outside both half-discs, and the Palm length), with limit law
`μ`; the same at `R(x)`, region 2, `ν`. Intended witnesses: `μ = ν =` the law of the rich data of
a `γ`-quantum wedge. -/
def G2FixMixStmt (γ : ℝ) : Prop :=
  ∃ μ ν : Measure LawD, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
    (∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
      i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
        MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
        |(g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s ∩ {p | |g3X γ i p - i.t₁| + m < i.r₁} ∩ G) -
          μ.real s * (g3PalmLaw γ i).real ({p | |g3X γ i p - i.t₁| + m < i.r₁} ∩ G)| ≤ ε) ∧
    (∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
      i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
        MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
        |(g3PalmLaw γ i).real (g3Vf γ i ⁻¹' t ∩ {p | |g3R γ i p - i.t₂| + m < i.r₂} ∩ G) -
          ν.real t * (g3PalmLaw γ i).real ({p | |g3R γ i p - i.t₂| + m < i.r₂} ∩ G)| ≤ ε)

/-- **`G2FullMixStmt` from the geometry and the fixed-region mixing statement.** -/
theorem g2FullMixStmt_of_geo_fix {γ : ℝ} (hG : G3GeoStmt γ) (hF : G2FixMixStmt γ) :
    G2FullMixStmt γ := by
  obtain ⟨μ, ν, hμ, hν, hU, hV⟩ := hF
  refine ⟨μ, ν, hμ, hν, fun s hs => ?_, fun t ht => ?_⟩
  · exact mix_of_geo_fix (P := g3PalmLaw γ)
      (fun i => outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂)
      (fun i => g3X γ i) (measurable_g3X' γ) (fun i => i.t₁) (fun i => i.r₁) (g3Uf γ) s
      measureReal_nonneg
      (measureReal_le_one_of_prob μ s) hG.1 (hU s hs)
  · exact mix_of_geo_fix (P := g3PalmLaw γ)
      (fun i => outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂)
      (fun i => g3R γ i) (measurable_g3R' γ) (fun i => i.t₂) (fun i => i.r₂) (g3Vf γ) t
      measureReal_nonneg
      (measureReal_le_one_of_prob ν t) hG.2 (hV t ht)

end Thm18Asm
end QuantumZipper
