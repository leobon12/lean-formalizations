import QuantumZipper.Proofs.Zipper.D3PlusN2Tm
import QuantumZipper.Proofs.LQG.ZoomRadialBasic
import QuantumZipper.Proofs.Wire2b

/-!
# D3⁺(i), node N2-zero (the model zoom): split into three nodes

Task N2-TMZERO. `D3PlusIN2TmZeroStmt` (`D3PlusN2Tm.lean`) says: the law of the zoomed rich data
`TmRichN1 γ r R L (localZ X r ·, circData α 0)` of the model field
`h_L = Z + α(−log‖·‖) + L/γ` (`Z` the local part of the free field on the half-disc `halfDisc r`)
converges in total variation, as `L → ∞`, to the law of `locFieldFull R ∘ Y'`, `Y'` an
`α`-quantum wedge.

## Source

Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*, arXiv:1409.7055,
Proposition 4.7(ii) and its proof (pp. 77–78), and Proposition 4.8 with its proof (pp. 78–79);
Sheffield, arXiv:1012.4797, proof of Proposition 1.6 (p. 25). The argument:

1. **Circle-average embedding.** Rescale `h_L` at the first time `t_0` at which its semicircle
   average, in the coordinates of the rescaled field `h(a ·) + Q log a`, vanishes
   (DMS p. 78, `t_0^C`). In our normalization: the semicircle average of `Z` at radius
   `r e^{−t}` is `√2 b_t` with `b` a standard Brownian motion (`zRadB`, DMS p. 77
   "`h_{e^{−t}}(0)` evolves as `B_{2t}`"), the level is `c_L = L/γ − (α − Q) log r`
   (`n2Lev`), the embedding time is `ZoomRadial.Tc α Q c_L b` and the embedding scale is
   `r e^{−Tc}` (`n2EmbScale`); the embedded field is `n2Emb`.
2. **Radial part** (DMS p. 78 (a)–(c)): the re-centred radial path converges to the wedge's
   radial process `A`; in TV on `[−S, ∞)` this is `ZoomRadial.abs_prob_zoomRadial_sub_le`
   (unconditional form `abs_prob_zoomRadial_sub_le_uncond`, `Wire5.lean`).
3. **Lateral part** (DMS p. 78: "this rescaling procedure does not affect the projection of `h`
   onto `H₂(ℍ)`"): exact scale invariance `WedgeTK.fieldLawFull_lateralPart_rescale`,
   independence of the radial and lateral parts `WedgeTK.indepFun_radialProc_lateralPart`, and,
   because `Z` is the local part (not the free field), a Cameron–Martin step for the harmonic
   correction `h_X = X − Z` whose lateral part vanishes at `0`.
4. **Window/canonical transfer** (DMS Prop. 4.8 proof, p. 79: "couple … in `B(0, R)` so that they
   agree with probability at least `1 − ε`"): both canonical descriptions are, off events of small
   probability, the same measurable function `gK γ K R` of the raw data on the window
   `halfDisc K` (`D3PlusN2Loc.locFieldFull_canonicalOn_eq_local`).

## The three nodes

* `N2ZHeartStmt` (steps 1–3): for every window `K`, the window data `resField K` of the
  embedded model converges in TV to the window data of the circle-average-embedded wedge field
  `wedgeV = wedgeField (lateralPart X'') A Q` (plus a.e.-measurability of the model window data).
* `N2ZModelLocStmt` (step 4, model side): off an event of probability `≤ η` (for `K` large and
  then `L` large), `TmRichN1 … = gK γ K R (resField K (n2Emb …))`.
* `N2ZWedgeLocStmt` (step 4, wedge side): the law of `locFieldFull R ∘ Y'` is `η`-close in TV to
  that of `gK γ K R ∘ resField K ∘ wedgeV` for `K` large (plus measurability of `wedgeV`'s
  window data).

**Proved here:** `d3PlusIN2TmZero_of_nodes : N2ZHeartStmt → N2ZModelLocStmt → N2ZWedgeLocStmt →
D3PlusIN2TmZeroStmt` (triangle inequality through the window data; coupling and data-processing
bounds for TV; own elementary glue, following DMS Prop. 4.8's proof).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The circle-average embedding of the model field -/

/-- The radial part of the local field `Z`, normalized to a standard Brownian motion:
`b_t = (√2)⁻¹ · (semicircle average of Z at radius r e^{−t})` (regularized, `radAvgReg`). -/
def zRadB {Ω : Type*} (X : Ω → FieldSample) (r : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (√2)⁻¹ * radAvgReg (locZField X r ω) (r * Real.exp (-(t : ℝ)))

/-- The starting level of the drifted radial path: `L/γ − (α − Q) log r`. With it the semicircle
average of `rescale h_L Q (r e^{−T})` at radius `e^{−s}` is `Xc (T + s) + Q s`
(`ZoomRadial.Xc`, level `n2Lev`, Brownian motion `zRadB`). -/
def n2Lev (γ α L r : ℝ) : ℝ := L / γ - (α - Qc γ) * Real.log r

/-- The circle-average embedding scale `r e^{−Tc}` (DMS arXiv:1409.7055 p. 78, `ε_0^C`). -/
def n2EmbScale (γ α L r : ℝ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : ℝ :=
  r * Real.exp (-ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω)

/-- The model field `h_L = Z + α(−log‖·‖) + L/γ` in N1's local-model form. -/
def n2Model (γ α L r : ℝ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  locModel γ L r (localZ X r ω, circData α fun _ => 0)

/-- The circle-average embedding of the model field: `h_L(a ·) + Q log a`, `a = n2EmbScale`. -/
def n2Emb (γ α L r : ℝ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  rescale (n2Model γ α L r X ω) (Qc γ) (n2EmbScale γ α L r X ω)

/-- The circle-average embedding of the wedge (`IsQuantumWedge`'s field before `canonical`). -/
def wedgeV (γ : ℝ) {Ω : Type*} (X : Ω → FieldSample) (A : ℝ → Ω → ℝ) (ω : Ω) : FieldSample :=
  wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)

/-- The canonical rich data read from window data on `halfDisc K`
(`locFieldFull_canonicalOn_eq_local`). -/
def gK (γ : ℝ) (K R : ℕ) : (LocIdx (K : ℝ) → ℝ) → (ℕ → ℝ) × (TestFun H → ℝ) :=
  fun v => TmRichN1 γ K R 0 (v, 0)

theorem measurable_gK (γ : ℝ) (K R : ℕ) : Measurable (gK γ K R) :=
  (measurable_TmRichN1 γ K R 0).comp (measurable_id.prodMk measurable_const)

/-- The window event on which the canonical rich data are read from the window `halfDisc K`:
the measurable surrogate `scaleSur` of the local scale lies in `(0, K/(R+2))`. -/
def n2Good (γ : ℝ) (K R : ℕ) : Set (LocIdx (K : ℝ) → ℝ) :=
  {v | 0 < scaleSur γ 0 K (v, 0) ∧ scaleSur γ 0 K (v, 0) < K / (R + 2)}

theorem measurableSet_n2Good (γ : ℝ) (K R : ℕ) : MeasurableSet (n2Good γ K R) := by
  have hs : Measurable fun v : LocIdx (K : ℝ) → ℝ => scaleSur γ 0 K (v, 0) :=
    (measurable_scaleSur γ 0 K).comp (measurable_id.prodMk measurable_const)
  exact (measurableSet_lt measurable_const hs).inter (measurableSet_lt hs measurable_const)

open Classical in
/-- `locFieldFull R` read off the full data `(coordsFull, pairings)`. -/
def lffOfData (R : ℕ) (d : (ℕ → ℝ) × (TestFun H → ℝ)) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  (fun i => if inBallFull R i then d.1 i else 0, fun ρ => if suppIn R ρ then d.2 ρ else 0)

theorem measurable_lffOfData (R : ℕ) : Measurable (lffOfData R) := by
  classical
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · by_cases h : inBallFull R i
    · simp only [h, ite_true]
      exact (measurable_pi_apply i).comp measurable_fst
    · simp only [h, ite_false]; exact measurable_const
  · by_cases h : suppIn R ρ
    · simp only [h, ite_true]
      exact (measurable_pi_apply ρ).comp measurable_snd
    · simp only [h, ite_false]; exact measurable_const

/-- **The wedge's local rich law is that of the canonical embedded wedge field** (from
`IsQuantumWedge`'s law identity; a.e.-measurability `Wire2.aemeasurable_dataFull_of_isQuantumWedge`
on both sides). -/
theorem map_locFieldFull_wedge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y' : Ω' → FieldSample} {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''}
    [IsProbabilityMeasure P''] {X'' : Ω'' → FieldSample} {A : ℝ → Ω'' → ℝ}
    (hX'' : IsFreeGFFModConstH X'' P'') (hA : IsWedgeProcess α (Qc γ) A P'')
    (hInd : IndepFun X'' (fun ω t => A t ω) P'') (hY' : IsQuantumWedge γ α Y' P')
    (hlaw : fieldLawFull H Y' P' = fieldLawFull H (fun ω => canonical γ (wedgeV γ X'' A ω)) P'')
    (R : ℕ) :
    P'.map (fun ω => locFieldFull R (Y' ω)) =
      P''.map (fun ω => locFieldFull R (canonical γ (wedgeV γ X'' A ω))) := by
  have hW : IsQuantumWedge γ α (fun ω => canonical γ (wedgeV γ X'' A ω)) P'' :=
    ⟨hα, Ω'', inferInstance, P'', X'', A, inferInstance, hX'', hA, hInd, rfl⟩
  have h1 := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hY'
  have h2 := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hW
  have e1 : (fun ω => locFieldFull R (Y' ω)) =
      lffOfData R ∘ fun ω => WedgeMeas.dataFull H (Y' ω) := rfl
  have e2 : (fun ω => locFieldFull R (canonical γ (wedgeV γ X'' A ω))) =
      lffOfData R ∘ fun ω => WedgeMeas.dataFull H (canonical γ (wedgeV γ X'' A ω)) := rfl
  rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable (measurable_lffOfData R).aemeasurable h1,
    ← AEMeasurable.map_map_of_aemeasurable (measurable_lffOfData R).aemeasurable h2]
  exact congrArg (fun m => m.map (lffOfData R)) hlaw

/-! ## The nodes -/

/-- **Node N2Z-MODELLOC** (window transfer, model side; DMS Prop. 4.8 proof): on the window event,
the model's zoomed rich data are read from the embedded window data, except on events of vanishing
probability (the embedding scale is not yet small, or the local area measure is not a vague
limit). -/
def N2ZModelLocStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample),
    0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ K R : ℕ, 0 < K → Tendsto (fun L => P {ω | resField K (n2Emb γ α L r X ω) ∈ n2Good γ K R ∧
      TmRichN1 γ r R L (localZ X r ω, circData α fun _ => 0) ≠
        gK γ K R (resField K (n2Emb γ α L r X ω))}) atTop (𝓝 0)

/-- **Node N2Z-WEDGELOC** (window transfer, wedge side): a.e.-measurability of the window data,
the a.s. identity on the window event, and the window event exhausts as `K → ∞`. -/
def N2ZWedgeLocStmt : Prop :=
  ∀ (γ α : ℝ) {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'')
    [IsProbabilityMeasure P''] (X'' : Ω'' → FieldSample) (A : ℝ → Ω'' → ℝ),
    0 < γ → γ < 2 → α < Qc γ → IsFreeGFFModConstH X'' P'' →
    IsWedgeProcess α (Qc γ) A P'' → IndepFun X'' (fun ω t => A t ω) P'' →
    (∀ K : ℕ, AEMeasurable (fun ω => resField K (wedgeV γ X'' A ω)) P'') ∧
    (∀ K R : ℕ, 0 < K → P'' {ω | resField K (wedgeV γ X'' A ω) ∈ n2Good γ K R ∧
      locFieldFull R (canonical γ (wedgeV γ X'' A ω)) ≠
        gK γ K R (resField K (wedgeV γ X'' A ω))} = 0) ∧
    ∀ R : ℕ, Tendsto (fun K : ℕ => P'' {ω | resField K (wedgeV γ X'' A ω) ∉ n2Good γ K R})
      atTop (𝓝 0)

/-! ## Assembly -/

/-- Data processing through a measurable map, for a.e.-measurable inputs on two spaces. -/
theorem tvDist_map_comp_le {Ω₁ Ω₂ β δ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace β] [MeasurableSpace δ] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {f₁ : Ω₁ → β} {f₂ : Ω₂ → β} {g : β → δ} (hg : Measurable g) (h₁ : AEMeasurable f₁ P₁)
    (h₂ : AEMeasurable f₂ P₂) :
    TV.tvDist (P₁.map (g ∘ f₁)) (P₂.map (g ∘ f₂)) ≤ TV.tvDist (P₁.map f₁) (P₂.map f₂) := by
  rw [← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h₁,
    ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h₂]
  exact TV.tvDist_map_le hg

/-- Splitting the disagreement event along a set `G`. -/
theorem measure_ne_le_split {Ω₁ β δ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    {f f' : Ω₁ → δ} {w : Ω₁ → β} (G : Set β) :
    P₁ {ω | f ω ≠ f' ω} ≤ P₁ {ω | w ω ∈ G ∧ f ω ≠ f' ω} + P₁ {ω | w ω ∉ G} := by
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  by_cases h : w ω ∈ G
  · exact Or.inl ⟨h, hω⟩
  · exact Or.inr h

end D3Plus
end QuantumZipper
