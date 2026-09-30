import QuantumZipper.Proofs.Section5.Prop16NodeCMain
import QuantumZipper.Proofs.Section5.Prop16PalmMask

/-!
# Proposition 1.6, Palm-zoom node C′ (masked): reduction to D3⁺(i) and a masked coupling node

Decision D30 masks the zoom coordinates of Prop. 1.6 (`Prop16PalmMaskBasic.lean`). The unmasked
node-C reduction (`Prop16NodeCMain.lean`, `Prop16NodeCSplit.lean`) rests on law equalities of the
*full* local zoom coordinates, which read junk circle values outside `closure D`
(`Prop16FixedLawStmt` is false: add `1` to every non-admissible pairing). This file redoes the
reduction for the masked coordinates `palmFixedMask`:

* `Prop16NodeCModelMaskStmt` (**masked coupling node**): as `Prop16NodeCModelStmt`, with the law
  equality and the measurability stated for the masked coordinates;
* `prop16FixedZoomMask_of_model : D3PlusIStmt → Prop16NodeCModelMaskStmt →
  Prop16FixedZoomMaskStmt`, and the variants from the rich and N2 forms of D3⁺(i).

On the good event (model agreement near `0`, local area measure on `D − x`, and model scale
`s ∈ (0, min (r/(R+1)) (gap/(2R+1)))`), the zoom scale of the coupled field equals `s`
(`nodeC_scaleParamOn_eq`), so the mask is inactive inside `closedBall 0 R`
(`locCoords_maskCoords`) and the switch `nodeC_locField_canonicalOn_eq` applies. The bad-scale
probability tends to `0` by D3⁺(iii) (`D3Plus.d3PlusIII_tendsto_prob`).

Sources: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25); Duplantier–Miller–Sheffield,
arXiv:1409.7055, Props. 4.7–4.8 (the zoom convergence, here D3⁺(i)). The TV bookkeeping and the
masking are own elementary arguments (as in `Prop16NodeCMain.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization

/-- **Masked coupling node at a fixed boundary point.** For the Palm hypotheses of Prop. 1.6 and
every `x ∈ (a, b)` there are a probability space `Ω₀` carrying a field `Y₀` whose *masked*
canonical zoom coordinates at `x` have, for all `C` and `R`, the same local laws as the masked
fixed-point zoom coordinates of `X + (γ/2) G_D(x, ·)` under `P`, and are a.e.-measurable; and
D3⁺ data `r, ρ₀, X', Ξ, g` (a `Setup` with `α = γ`, `halfDisc r ⊆ D − x`) such that a.s., for
every `C`, the zoomed `Y₀` agrees with `zoomModel γ γ C ρ₀ X' g` on the dyadic folded circles of
`ball 0 r` and has a local area measure on `D − x`; and the model's local scale is
a.e.-measurable. -/
def Prop16NodeCModelMaskStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    ∀ x ∈ Ioo a b, ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀)
      (Y₀ : Ω₀ → FieldSample) (r : ℝ) (ρ₀ : Measure ℂ) (X' : Ω₀ → FieldSample) (E' : Type)
      (_ : MeasurableSpace E') (Ξ : Ω₀ → E') (g : Ω₀ → ℂ → ℝ),
      IsProbabilityMeasure P₀ ∧
      (∀ (C : ℝ) (R : ℕ), P.map (fun ω => locCoords R (palmFixedMask γ C D c d a b h0 X x ω)) =
        P₀.map (fun ω => locCoords R (palmCanonMask γ C D a b h0 Y₀ (ω, x)))) ∧
      (∀ C : ℝ, AEMeasurable (fun ω => palmCanonMask γ C D a b h0 Y₀ (ω, x)) P₀) ∧
      D3Plus.Setup γ γ r ρ₀ P₀ X' Ξ g ∧ D3Plus.halfDisc r ⊆ zoomDomain D x ∧
      (∀ᵐ ω ∂P₀, ∀ C : ℝ,
        D3Plus.AgreeNear (zoomFree γ C h0 Y₀ (ω, x)) (D3Plus.zoomModel γ γ C ρ₀ (X' ω) (g ω)) r ∧
        ∃ μ, IsVagueLimitOn (zoomDomain D x) (areaApprox γ (zoomFree γ C h0 Y₀ (ω, x))) μ) ∧
      ∀ C : ℝ, AEMeasurable (fun ω => scaleParamOn γ
        (D3Plus.zoomModel γ γ C ρ₀ (X' ω) (g ω)) (D3Plus.halfDisc r)) P₀

/-- **Pointwise switch for the masked coordinates.** On the good event the masked local zoom
coordinates of `y` equal the local canonical coordinates of the model field `y'`. -/
theorem nodeCMask_locCoords_eq {γ r : ℝ} {R : ℕ} {D : Set ℂ} {a b x : ℝ} {y y' : FieldSample}
    (hU : IsOpen (zoomDomain D x)) (hsub : D3Plus.halfDisc r ⊆ zoomDomain D x)
    (hag : D3Plus.AgreeNear y y' r) {μ : Measure ℂ}
    (hy : IsVagueLimitOn (zoomDomain D x) (areaApprox γ y) μ)
    (hpos : 0 < scaleParamOn γ y' (D3Plus.halfDisc r))
    (hlt : scaleParamOn γ y' (D3Plus.halfDisc r) * ((R : ℝ) + 1) < r)
    (hgap : scaleParamOn γ y' (D3Plus.halfDisc r) * (2 * (R : ℝ) + 1) < palmGap D a b x) :
    locCoords R (maskCoords D a b (scaleParamOn γ y (zoomDomain D x)) x
        (coords (canonicalOn γ y (zoomDomain D x)))) =
      TV.locField R (canonicalOn γ y' (D3Plus.halfDisc r)) := by
  set s := scaleParamOn γ y' (D3Plus.halfDisc r) with hs
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hsr : s < r := lt_of_le_of_lt (by nlinarith) hlt
  have he : scaleParamOn γ y (zoomDomain D x) = s := nodeC_scaleParamOn_eq hU hsub hag hy hpos hsr
  rw [he, locCoords_maskCoords hpos (lt_of_le_of_lt (by nlinarith) hgap),
    ← locField_eq_locCoords]
  exact nodeC_locField_canonicalOn_eq hU hsub hag hy hpos hlt

/-- **Node C′ (Prop. 1.6, masked) from D3⁺(i) and the masked coupling node** (own TV
bookkeeping, the masked version of `prop16FixedZoom_of_model`). -/
theorem prop16FixedZoomMask_of_model (hI : D3Plus.D3PlusIStmt) (hM : Prop16NodeCModelMaskStmt) :
    Prop16FixedZoomMaskStmt := by
  intro γ D c d a b h0 Ω _ P X hyp Ω' _ P' W hP' hW x hx R
  have hdat := hyp.1
  obtain ⟨hγ, hγ2, hgeo, -, hca, hbd, -⟩ := id hdat
  have hDo : IsOpen D := hgeo.1
  have hDH : D ⊆ H := hgeo.2.2.2.1
  have hhd := hgeo.2.2.2.2.2.2
  have hUo : IsOpen (zoomDomain D x) := hDo.preimage (continuous_id.add continuous_const)
  obtain ⟨Ω₀, _, P₀, Y₀, r, ρ₀, X', E', _, Ξ, g, hP₀, hlaw, hZm, hS, hsub, hag, hsc⟩ :=
    hM γ D c d a b h0 P X hyp x hx
  have := hP'
  have := hP₀
  have hr : 0 < r := hS.hr
  have hgap := palmGap_pos hDH hhd hca hbd hx
  refine (?_ : Tendsto (fun C => tvDist
      (P₀.map fun ω => locCoords R (palmCanonMask γ C D a b h0 Y₀ (ω, x)))
      (P'.map fun ω => locField R (W ω))) atTop (𝓝 0)).congr fun C => by rw [hlaw C R]
  set sc : ℝ → Ω₀ → ℝ := fun C ω => scaleParamOn γ
    (D3Plus.zoomModel γ γ C ρ₀ (X' ω) (g ω)) (D3Plus.halfDisc r) with hscdef
  set δ : ℝ := min (r / ((R : ℝ) + 1)) (palmGap D a b x / (2 * (R : ℝ) + 1)) with hδ
  have hδ0 : (0 : ℝ) < δ := lt_min (by positivity) (by positivity)
  have hbad : Tendsto (fun C => P₀ {ω | ¬ (0 < sc C ω ∧ sc C ω < δ)}) atTop (𝓝 0) := by
    refine tendsto_of_seq_tendsto fun Cs hCs => ?_
    exact D3Plus.d3PlusIII_tendsto_prob hS hCs hδ0 fun n =>
      (hsc (Cs n)).nullMeasurable measurableSet_Ioo.compl
  set N : Set Ω₀ := {ω | ¬ ∀ C : ℝ,
    D3Plus.AgreeNear (zoomFree γ C h0 Y₀ (ω, x)) (D3Plus.zoomModel γ γ C ρ₀ (X' ω) (g ω)) r ∧
      ∃ μ, IsVagueLimitOn (zoomDomain D x) (areaApprox γ (zoomFree γ C h0 Y₀ (ω, x))) μ}
    with hNdef
  have hN : P₀ N = 0 := ae_iff.1 hag
  have hD := hI γ γ r ρ₀ P₀ X' Ξ g P' W hS hW R
  have hWm := aemeasurable_locField_wedge hγ hγ2 hW R
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε0
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε0.ne'
  filter_upwards [hD (ε / 2) hε2, (ENNReal.tendsto_nhds_zero.1 hbad) (ε / 2) hε2]
    with C hC hE
  set E : Set Ω₀ := N ∪ {ω | ¬ (0 < sc C ω ∧ sc C ω < δ)} with hEdef
  have hPE : P₀ E ≤ ε / 2 :=
    (measure_union_le _ _).trans (by rw [hN, zero_add]; exact hE)
  refine (nodeC_tvDist_le ((measurable_locCoords R).comp_aemeasurable (hZm C))
    (fun ω => TV.locField R (canonicalOn γ (D3Plus.zoomModel γ γ C ρ₀ (X' ω) (g ω))
      (D3Plus.halfDisc r))) _ E ?_ (ε / 2) ?_).trans ?_
  · intro ω hω
    simp only [hEdef, mem_union, not_or, hNdef, mem_ofPred_eq, not_not] at hω
    obtain ⟨hgood, hpos, hlt⟩ := hω
    obtain ⟨hagC, μ, hμ⟩ := hgood C
    have hR1 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
    have hR2 : (0 : ℝ) < 2 * (R : ℝ) + 1 := by positivity
    have hlt' : sc C ω * ((R : ℝ) + 1) < r :=
      (lt_div_iff₀ hR1).1 (lt_of_lt_of_le hlt (min_le_left _ _))
    have hgap' : sc C ω * (2 * (R : ℝ) + 1) < palmGap D a b x :=
      (lt_div_iff₀ hR2).1 (lt_of_lt_of_le hlt (min_le_right _ _))
    exact nodeCMask_locCoords_eq hUo hsub hagC hμ hpos hlt' hgap'
  · intro S hS
    have hΦ : Measurable[(D3Plus.condSigma Ξ X' r).prod inferInstance]
        (fun p : Ω₀ × (ℕ → ℝ) => S.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) p.2) := by
      let _ : MeasurableSpace Ω₀ := D3Plus.condSigma Ξ X' r
      exact (measurable_one.indicator hS).comp measurable_snd
    have hΦ1 : ∀ p : Ω₀ × (ℕ → ℝ), S.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) p.2 ≤ 1 := fun p => by
      by_cases hp : p.2 ∈ S <;> simp [hp]
    obtain ⟨h1, h2⟩ := hC _ hΦ hΦ1
    have hrhs : ∫⁻ ω, ∫⁻ ω', S.indicator (1 : (ℕ → ℝ) → ℝ≥0∞)
        (TV.locField R (W ω')) ∂P' ∂P₀ = P'.map (fun ω => locField R (W ω)) S := by
      rw [lintegral_const, measure_univ, mul_one]
      exact S5.FieldLaw.Raw.palmC_lintegral_indicator hWm hS
    rw [hrhs] at h1 h2
    exact ⟨h1, h2⟩
  · rw [add_comm]
    calc _ ≤ ε / 2 + ε / 2 := add_le_add hPE le_rfl
      _ = ε := ENNReal.add_halves ε

/-- Node C′ from the N2 form of D3⁺(i). -/
theorem prop16FixedZoomMask_of_modelN2 (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hM : Prop16NodeCModelMaskStmt) : Prop16FixedZoomMaskStmt :=
  prop16FixedZoomMask_of_model (D3Plus.d3PlusI_of_N2Rich hN2) hM

end Prop16Asm

end QuantumZipper
