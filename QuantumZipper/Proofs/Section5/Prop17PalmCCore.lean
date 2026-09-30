import QuantumZipper.Proofs.Section5.Prop17PalmZoomFree
import QuantumZipper.Proofs.Zipper.LocRichD3

/-!
# Proposition 1.7, Palm-zoom node C: reduction to D3⁺(i) and a model-agreement node (PALM-C)

Node C of `handoff/PROP17-STAT.md` (PALMZOOM) is `Prop17FreeFixedZoomStmt γ ϖ a b`: TV-local
convergence, as `C → ∞`, of the zoom coordinates at a *fixed* boundary point `x ∈ [a, b]` of the
Palm-shifted field `N_ϖ(X + (γ/2)(neumannH x · − kPot ϖ))`, towards the reference `γ`-wedge.

Sources: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25) ("zooming in at a fixed point of
`GFF + γ(−log|x−·|) + smooth` gives the `γ`-quantum wedge"); TV-local form:
Duplantier–Miller–Sheffield, arXiv:1409.7055, Prop. 4.7–4.8 (pp. 77–79). In this project the
zoom convergence at a fixed point is D3⁺(i) (`D3Plus.D3PlusIStmtRich`, decision D25), stated for
the model field `zoomModel γ α L ρ₀ X' g` read locally through `canonicalOn … (halfDisc r)`.

This file proves (own TV bookkeeping, the coupling inequality):

* `palmC_tvDist_le`: if `f = m` off a set `E` and the indicator functionals of `m` are
  `η`-close to those of `w`, then `tvDist (law f) (law w) ≤ η + P E`;
* `prop17FreeFixedZoom_of_model`: `Prop17FreeFixedZoomStmt γ ϖ a b` from `D3PlusIStmtRich` and
  `Prop17PalmCModelStmt γ ϖ a b`, which asks, at every `x ∈ [a, b]`, for a D3⁺ setup (with
  `α = γ`, trivial `Ξ` and a deterministic correction `g`) whose model data agree with the
  Palm zoom data with probability tending to `1` as `C → ∞`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV PalmShift FieldShift PalmNorm

/-- The first component of the rich local data is `locFull R ∘ coordsFull`. -/
theorem palmC_locFieldFull_fst (R : ℕ) (y : FieldSample) :
    (D3Plus.locFieldFull R y).1 = locFull R (coordsFull y) := rfl

/-- The model data read by D3⁺(i) at level `C` (first component of the rich local data of the
local canonical description of `zoomModel γ γ C ρ₀ y g` on `halfDisc r`). -/
def palmCModelData (γ r C : ℝ) (R : ℕ) (ρ₀ : Measure ℂ) (y : FieldSample) (g : ℂ → ℝ) :
    ℕ → ℝ :=
  (D3Plus.locFieldFull R
    (canonicalOn γ (D3Plus.zoomModel γ γ C ρ₀ y g) (D3Plus.halfDisc r))).1

/-- **Node C′ (model agreement).** For every reference construction and every `x ∈ [a, b]` there
are a radius `r`, a normalizing measure `ρ₀`, a field `X'` and a deterministic correction `g`
forming a D3⁺ setup (`α = γ`, trivial conditioning data), such that the Palm zoom coordinates
at `x` are a.e.-measurable and, for every `R`, agree inside `closedBall 0 R` with the D3⁺ model
data except on an (outer-measure) event whose probability tends to `0` as `C → ∞`. -/
def Prop17PalmCModelStmt (γ : ℝ) (ϖ : Measure ℂ) (a b : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ x ∈ Icc a b, ∃ (r : ℝ) (ρ₀ : Measure ℂ) (X' : Ω' → FieldSample) (g : ℂ → ℝ),
      D3Plus.Setup γ γ r ρ₀ P' X' (fun _ : Ω' => ()) (fun _ => g) ∧
      (∀ C : ℝ, AEMeasurable (fun ω => palmZoomCoords γ C ϖ X (ω, x)) P') ∧
      ∀ R : ℕ, Tendsto (fun C : ℝ => P' {ω | locFull R (palmZoomCoords γ C ϖ X (ω, x)) ≠
        palmCModelData γ r C R ρ₀ (X' ω) g}) atTop (𝓝 0)

/-- Indicator functionals of an a.e.-measurable map are its law. -/
theorem palmC_lintegral_indicator {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {f : Ω → β} (hf : AEMeasurable f P) {S : Set β} (hS : MeasurableSet S) :
    ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (f ω) ∂P = P.map f S := by
  rw [← lintegral_map' (measurable_one.indicator hS).aemeasurable hf, lintegral_indicator_one hS]

/-- **Coupling bound** (own bookkeeping): `f = m` off `E`, and the indicator functionals of `m`
are `η`-close to the law of `w`; then `tvDist (law f) (law w) ≤ η + P E`. -/
theorem palmC_tvDist_le {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    {f w : Ω → β} (hf : AEMeasurable f P) (m : Ω → β) (E : Set Ω)
    (hE : ∀ ω, ω ∉ E → f ω = m ω) (η : ℝ≥0∞)
    (hη : ∀ S : Set β, MeasurableSet S →
      ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P ≤ P.map w S + η ∧
        P.map w S ≤ ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P + η) :
    tvDist (P.map f) (P.map w) ≤ η + P E := by
  set E' := toMeasurable P E
  have hE'm : MeasurableSet E' := measurableSet_toMeasurable P E
  have hPE : P E' = P E := measure_toMeasurable E
  refine iSup₂_le fun S hS => ?_
  obtain ⟨h1, h2⟩ := hη S hS
  have hind : Measurable (E'.indicator (1 : Ω → ℝ≥0∞)) := measurable_one.indicator hE'm
  have hint : ∫⁻ ω, E'.indicator (1 : Ω → ℝ≥0∞) ω ∂P = P E := by
    rw [lintegral_indicator_one hE'm, hPE]
  have hpt : ∀ (u v : Ω → β), (∀ ω, ω ∉ E → u ω = v ω) → ∀ ω,
      S.indicator (1 : β → ℝ≥0∞) (u ω) ≤
        S.indicator (1 : β → ℝ≥0∞) (v ω) + E'.indicator (1 : Ω → ℝ≥0∞) ω := by
    intro u v huv ω
    by_cases hω : ω ∈ E'
    · rw [indicator_of_mem hω]
      refine le_add_left ?_
      by_cases hu : u ω ∈ S <;> simp [hu]
    · rw [huv ω fun h => hω (subset_toMeasurable P E h)]
      exact le_self_add
  have hfm : P.map f S ≤ ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P + P E := by
    rw [← palmC_lintegral_indicator hf hS, ← hint, ← lintegral_add_right _ hind]
    exact lintegral_mono (hpt f m hE)
  have hmf : ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P ≤ P.map f S + P E := by
    rw [← palmC_lintegral_indicator hf hS, ← hint, ← lintegral_add_right _ hind]
    exact lintegral_mono (hpt m f fun ω hω => (hE ω hω).symm)
  refine sup_le ?_ ?_
  · rw [tsub_le_iff_left]
    calc P.map f S ≤ ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P + P E := hfm
      _ ≤ P.map w S + η + P E := by gcongr
      _ = P.map w S + (η + P E) := by rw [add_assoc]
  · rw [tsub_le_iff_left]
    calc P.map w S ≤ ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P + η := h2
      _ ≤ P.map f S + P E + η := by gcongr
      _ = P.map f S + (η + P E) := by rw [add_assoc, add_comm (P E)]

/-- **Node C from D3⁺(i) and the model-agreement node** (own TV bookkeeping; the probabilistic
content is D3⁺(i), Sheffield, proof of Prop. 1.6, p. 25; DMS arXiv:1409.7055, Prop. 4.7–4.8). -/
theorem prop17FreeFixedZoom_of_model {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ϖ : Measure ℂ}
    {a b : ℝ} (hI : D3Plus.D3PlusIStmtRich) (hM : Prop17PalmCModelStmt γ ϖ a b) :
    Prop17FreeFixedZoomStmt γ ϖ a b := by
  intro Ω' _ P' X A hP' hX hA hInd x hx R
  obtain ⟨r, ρ₀, X', g, hS, hAm, hdis⟩ := hM Ω' _ P' X A hP' hX hA hInd x hx
  have hW : IsQuantumWedge γ γ (refField γ X A) P' :=
    ⟨gamma_lt_Qc' hγ hγ2, Ω', _, P', X, A, hP', hX, hA, hInd, rfl⟩
  have hWm : AEMeasurable (fun ω => coordsFull (refField γ X A ω)) P' :=
    (Wire3.wedgeDataAEMeasStmt_uncond hγ hγ2 P' _ hW).fst
  have hD := hI γ γ r ρ₀ P' X' (fun _ : Ω' => ()) (fun _ => g) P' (refField γ X A) hS hW R
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  filter_upwards [hD (ε / 2) hε2, (ENNReal.tendsto_nhds_zero.1 (hdis R)) (ε / 2) hε2]
    with C hC hE
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_locFull R).aemeasurable (hAm C),
    AEMeasurable.map_map_of_aemeasurable (measurable_locFull R).aemeasurable hWm]
  refine (palmC_tvDist_le ((measurable_locFull R).comp_aemeasurable (hAm C))
    (fun ω => palmCModelData γ r C R ρ₀ (X' ω) g) _ (fun ω hω => not_not.1 hω) (ε / 2)
    ?_).trans ?_
  · intro S hS
    have hΦ : Measurable[(D3Plus.condSigma (fun _ : Ω' => ()) X' r).prod inferInstance]
        (fun p : Ω' × ((ℕ → ℝ) × (TestFun H → ℝ)) => S.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) p.2.1) := by
      let _ : MeasurableSpace Ω' := D3Plus.condSigma (fun _ : Ω' => ()) X' r
      exact (measurable_one.indicator hS).comp (measurable_fst.comp measurable_snd)
    have hΦ1 : ∀ p : Ω' × ((ℕ → ℝ) × (TestFun H → ℝ)),
        S.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) p.2.1 ≤ 1 := fun p => by
      by_cases hp : p.2.1 ∈ S <;> simp [hp]
    obtain ⟨h1, h2⟩ := hC _ hΦ hΦ1
    have hrhs : ∫⁻ ω, ∫⁻ ω', S.indicator (1 : (ℕ → ℝ) → ℝ≥0∞)
        (D3Plus.locFieldFull R (refField γ X A ω')).1 ∂P' ∂P' =
        P'.map (locFull R ∘ fun ω => coordsFull (refField γ X A ω)) S := by
      simp_rw [palmC_locFieldFull_fst]
      rw [lintegral_const, measure_univ, mul_one]
      exact palmC_lintegral_indicator ((measurable_locFull R).comp_aemeasurable hWm) hS
    rw [hrhs] at h1 h2
    exact ⟨h1, h2⟩
  · rw [add_comm]
    calc _ ≤ ε / 2 + ε / 2 := add_le_add hE le_rfl
      _ = ε := ENNReal.add_halves ε

end Raw
end FieldLaw
end S5
end QuantumZipper
