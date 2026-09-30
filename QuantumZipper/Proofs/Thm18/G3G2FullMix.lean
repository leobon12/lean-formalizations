import QuantumZipper.Proofs.Thm18.G3G2Loc
import QuantumZipper.Proofs.Thm18.G3GeoStmt

/-!
# G2 for the full-field zooms: from asymptotic independence of the outside field

`G2FullStmt γ` (`G3G2Loc.lean`) asks for `L¹` convergence of the conditional probabilities
`P_Palm[Uf ∈ s | 𝒢]` to a deterministic `μ(s)`, `𝒢 = outsideSigmaPalm` (field outside both
half-discs, and the Palm length). This file replaces it by the **event (mixing) form**
`G2FullMixStmt γ`: for every cylinder set `s` and `ε > 0`, eventually along `g3Filter`,
uniformly over `𝒢`-events `G`,

  `|P_Palm(Uf ∈ s, G) − μ(s) P_Palm(G)| ≤ ε`

(and the same at `R(x)`). This is the form in which Sheffield's conditional Proposition 5.5
(arXiv:1012.4797, p. 65, used in the proof of Theorem 1.8, §5.4, pp. 70–71: "the zoomed field
near `x` converges to a `γ`-quantum wedge even after conditioning on the field outside `B_ε(x)`")
is naturally proved: the zoom is asymptotically independent, in total variation, of every
outside event.

* `integral_abs_condExp_indicator_sub_const_le`: `∫ |P[1_A | 𝒢] − c| ≤ 2 sup_{G ∈ 𝒢} |P(A ∩ G) − c P(G)|`
  (own elementary proof: split along the `𝒢`-event `{P[1_A|𝒢] ≥ c}`);
* `g2FullStmt_of_mix : G2FullMixStmt γ → G2FullStmt γ`;
* `g2ConcreteStmt_of_palmR_area_mix`: `G2ConcreteStmt γ` from `G3GeoPalmRStmt`, `G3AreaStmt`,
  `G2FullMixStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **`L¹` distance of a conditional probability to a constant**, bounded by the mixing defect:
`∫ |P[1_A | m] − c| dP ≤ 2M` if `|P(A ∩ G) − c P(G)| ≤ M` for every `m`-measurable `G`. -/
theorem integral_abs_condExp_indicator_sub_const_le {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    (hm : m ≤ m₀) {P : @Measure Ω m₀} [IsFiniteMeasure P] {A : Set Ω}
    (hA : MeasurableSet[m₀] A) (c M : ℝ)
    (hM : ∀ G, MeasurableSet[m] G → |P.real (A ∩ G) - c * P.real G| ≤ M) :
    ∫ ω, |P[A.indicator (fun _ => (1 : ℝ)) | m] ω - c| ∂P ≤ 2 * M := by
  set g := P[A.indicator (fun _ => (1 : ℝ)) | m] with hg
  have hgi : Integrable g P := integrable_condExp
  have hfi : Integrable (fun ω => g ω - c) P := hgi.sub (integrable_const c)
  have hfm : Measurable[m] fun ω => g ω - c :=
    (stronglyMeasurable_condExp.sub stronglyMeasurable_const).measurable
  have hind : Integrable (A.indicator fun _ => (1 : ℝ)) P := (integrable_const (1 : ℝ)).indicator hA
  have key : ∀ S, MeasurableSet[m] S →
      ∫ ω in S, (g ω - c) ∂P = P.real (A ∩ S) - c * P.real S := by
    intro S hS
    rw [integral_sub hgi.integrableOn (integrable_const c).integrableOn, hg,
      setIntegral_condExp hm hind hS, setIntegral_indicator hA, setIntegral_const,
      setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one, Set.inter_comm, mul_comm]
  set G : Set Ω := {ω | 0 ≤ g ω - c} with hGdef
  have hGm : MeasurableSet[m] G := measurableSet_le measurable_const hfm
  have hG0 : MeasurableSet[m₀] G := hm _ hGm
  have e1 : ∫ ω in G, |g ω - c| ∂P = ∫ ω in G, (g ω - c) ∂P :=
    setIntegral_congr_fun hG0 fun ω hω => abs_of_nonneg hω
  have e2 : ∫ ω in Gᶜ, |g ω - c| ∂P = -∫ ω in Gᶜ, (g ω - c) ∂P := by
    rw [← integral_neg]
    exact setIntegral_congr_fun hG0.compl fun ω hω => abs_of_neg (not_le.1 hω)
  rw [← integral_add_compl hG0 hfi.abs, e1, e2, key G hGm, key Gᶜ hGm.compl]
  have h1 := hM G hGm
  have h2 := hM Gᶜ hGm.compl
  have a1 := le_abs_self (P.real (A ∩ G) - c * P.real G)
  have a2 := neg_le_abs (P.real (A ∩ Gᶜ) - c * P.real Gᶜ)
  linarith

/-- **Conditional Proposition 5.5 at the two Palm points, event (mixing) form.** -/
def G2FullMixStmt (γ : ℝ) : Prop :=
  ∃ μ ν : Measure LawD, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
    (∀ s ∈ lawCyl, ∀ ε > 0, ∀ᶠ i in g3Filter, ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
        |(g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s ∩ G) - μ.real s * (g3PalmLaw γ i).real G| ≤ ε) ∧
    (∀ t ∈ lawCyl, ∀ ε > 0, ∀ᶠ i in g3Filter, ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
        |(g3PalmLaw γ i).real (g3Vf γ i ⁻¹' t ∩ G) - ν.real t * (g3PalmLaw γ i).real G| ≤ ε)

theorem tendsto_integral_abs_of_mix {γ : ℝ} {Uf : G3Idx → gffBase.Ω × ℝ → LawD}
    (hUf : ∀ i, Measurable (Uf i)) {μ : Measure LawD} {s : Set LawD} (hs : MeasurableSet s)
    (h : ∀ ε > 0, ∀ᶠ i in g3Filter, ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
        |(g3PalmLaw γ i).real (Uf i ⁻¹' s ∩ G) - μ.real s * (g3PalmLaw γ i).real G| ≤ ε) :
    Tendsto (fun i => ∫ p, |(g3PalmLaw γ i)[(Uf i ⁻¹' s).indicator
        (fun _ => (1 : ℝ)) | outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] p - μ.real s|
          ∂(g3PalmLaw γ i)) g3Filter (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h (ε / 4) (by positivity)] with i hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  have := integral_abs_condExp_indicator_sub_const_le (m := outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂)
    (le_sup_right.trans (sig_le_g3 i i.t₁ i.r₁))
    (P := g3PalmLaw γ i) (hUf i hs) (μ.real s) (ε / 4) hi
  linarith

/-- **`G2FullStmt` from its event (mixing) form.** -/
theorem g2FullStmt_of_mix {γ : ℝ} (h : G2FullMixStmt γ) : G2FullStmt γ := by
  obtain ⟨μ, ν, hμ, hν, hU, hV⟩ := h
  exact ⟨μ, ν, hμ, hν,
    fun s hs => tendsto_integral_abs_of_mix (measurable_g3Uf γ) (measurableSet_lawCyl hs)
      (hU s hs),
    fun t ht => tendsto_integral_abs_of_mix (measurable_g3Vf γ) (measurableSet_lawCyl ht)
      (hV t ht)⟩

/-- **G2 for the concrete scheme** from the three remaining inputs: the Palm estimate for `R(x)`
(`G3GeoPalmRStmt`), the area input (`G3AreaStmt`) and conditional Proposition 5.5 at the two
Palm points in event form (`G2FullMixStmt`). The `x`-half of the geometry is proved
(`g3GeoStmt_x`). -/
theorem g2ConcreteStmt_of_palmR_area_mix {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hP : G3GeoPalmRStmt γ) (hA : G3AreaStmt γ) (hF : G2FullMixStmt γ) : G2ConcreteStmt γ :=
  g2ConcreteStmt_of_inputs (g3GeoStmt_of_palmR hγ hγ2 hP) hA (g2FullStmt_of_mix hF)

end Thm18Asm
end QuantumZipper
