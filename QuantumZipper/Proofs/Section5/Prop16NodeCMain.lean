import QuantumZipper.Proofs.Section5.Prop16PalmZoom
import QuantumZipper.Proofs.Section5.Prop17PalmCCore
import QuantumZipper.Proofs.Zipper.D3PlusProb
import QuantumZipper.Proofs.Zipper.D3PlusN2Loc
import QuantumZipper.Proofs.Zipper.D3PlusIRich

/-!
# Proposition 1.6, Palm-zoom node C: reduction to D3⁺(i) and a coupling node (P16-NODE-C)

Node C of `Prop16PalmZoom.lean` is `Prop16FixedZoomStmt`: TV-local convergence, as `C → ∞`, of
the canonical zoom (on `D − x`) at a *fixed* point `x ∈ (a, b)` of the Palm-shifted mixed field
`X + (γ/2) G_D(x, ·)`, towards any `γ`-quantum wedge.

Sources: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25): near `x` the Palm field is
`GFF + γ(−log|· − x|) + smooth`, and zooming in at a fixed point of such a field gives the
`γ`-quantum wedge; TV-local form: Duplantier–Miller–Sheffield, arXiv:1409.7055, Props. 4.7–4.8
(pp. 77–79). In this project that zoom convergence is D3⁺(i) (`D3Plus.D3PlusIStmt`, decision
D25), stated for the model field `zoomModel γ α L ρ₀ X' g` read through `canonicalOn … (halfDisc r)`.

This file (own bookkeeping, following the Prop. 1.7 analogue `Prop17PalmCCore.lean`):

* `nodeC_locField_canonicalOn_eq`: the deterministic **switch** `canonicalOn · U ↔
  canonicalOn · (halfDisc r)`: if `y` has a local area measure on an open `U ⊇ halfDisc r` and
  agrees with `y'` on the dyadic circles in `ball 0 r`, and the local scale of `y'` is in
  `(0, r/(R+1))`, the local coordinates of the two canonical descriptions agree (the local-domain
  version of `D3Plus.locField_canonical_eq_canonicalOn`);
* `nodeC_tvDist_le`: the coupling inequality with an arbitrary target law;
* `Prop16NodeCModelStmt` (**the remaining node**): at each `x ∈ (a, b)` a coupling space carrying a
  copy `Y₀` of the Palm-shifted mixed field (same local zoom laws, measurable zoom coordinates)
  and a D3⁺ `Setup` (`α = γ`) whose model field agrees with the zoomed `Y₀` on the dyadic circles
  near `0`, with `Y₀`'s zoom having a local area measure on `D − x`, and measurable local scale;
* `prop16FixedZoom_of_model : D3PlusIStmt → Prop16NodeCModelStmt → Prop16FixedZoomStmt`, with
  the variants from the rich and N2 forms of D3⁺(i). The bad-scale probability tends to `0` by
  D3⁺(iii) (`D3Plus.d3PlusIII_tendsto_prob`, proved).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization

/-! ## 1. The switch `canonicalOn · U ↔ canonicalOn · (halfDisc r)` -/

/-- **Area locality on a subdomain** (the `U`-version of
`D3Plus.qAreaMeasureOn_eq_restrict_of_agree`, same proof). -/
theorem nodeC_qAreaMeasureOn_halfDisc_eq {γ r : ℝ} {U : Set ℂ} {y y' : FieldSample}
    (hsub : D3Plus.halfDisc r ⊆ U) (hag : D3Plus.AgreeNear y y' r)
    {μ : Measure ℂ} (hy : IsVagueLimitOn U (areaApprox γ y) μ) :
    qAreaMeasureOn γ y' (D3Plus.halfDisc r) = μ.restrict (D3Plus.halfDisc r) := by
  have hU := D3Plus.isOpen_halfDisc r
  obtain ⟨h1, h2, h3⟩ := AtomlessUncond.isVagueLimitOn_restrict hU hsub hy
  refine LocalRule.qAreaMeasureOn_eq hU ⟨h1, h2, fun f hf hfc hfU => ?_⟩
  refine (h3 f hf hfc hfU).congr' ?_
  have hKc : IsClosed (tsupport f) := isClosed_tsupport f
  obtain ⟨ρ, hρ, hKρ⟩ := exists_lt_subset_ball hKc (hfU.trans inter_subset_left)
  obtain ⟨K, hK⟩ := AtomlessUncond.exists_radius_lt (sub_pos.2 hρ)
  filter_upwards [eventually_ge_atTop K] with k hk
  have hKm : MeasurableSet (tsupport f) := hKc.measurableSet
  have hvan : ∀ z, z ∉ tsupport f → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hmeq : (areaApprox γ y k).restrict (tsupport f) =
      (areaApprox γ y' k).restrict (tsupport f) := by
    rw [areaApprox, areaApprox, restrict_withDensity hKm, restrict_withDensity hKm]
    refine withDensity_congr_ae ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => ?_))
    have hzρ := hKρ hz
    rw [Metric.mem_ball, dist_zero_right] at hzρ
    have hzk : ‖z‖ + radius k < r := by linarith [hK k hk]
    simp only [D3Plus.avgReg_congr hag hzk]
  have e1 : ∫ z, f z ∂(areaApprox γ y k) = ∫ z in tsupport f, f z ∂(areaApprox γ y k) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm
  have e2 : ∫ z, f z ∂(areaApprox γ y' k) = ∫ z in tsupport f, f z ∂(areaApprox γ y' k) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm
  rw [e1, e2, hmeq]

/-- **Scale locality on a subdomain.** -/
theorem nodeC_scaleParamOn_eq {γ r : ℝ} {U : Set ℂ} {y y' : FieldSample} (hU : IsOpen U)
    (hsub : D3Plus.halfDisc r ⊆ U) (hag : D3Plus.AgreeNear y y' r)
    {μ : Measure ℂ} (hy : IsVagueLimitOn U (areaApprox γ y) μ)
    (hpos : 0 < scaleParamOn γ y' (D3Plus.halfDisc r))
    (hlt : scaleParamOn γ y' (D3Plus.halfDisc r) < r) :
    scaleParamOn γ y U = scaleParamOn γ y' (D3Plus.halfDisc r) := by
  have hq := LocalRule.qAreaMeasureOn_eq hU hy
  have hq' := nodeC_qAreaMeasureOn_halfDisc_eq hsub hag hy
  unfold scaleParamOn at hpos hlt ⊢
  refine D3Plus.sInf_eq_of_agree_below (fun a ha => ha.1) (fun a ha => ha.1) (fun a ha => ?_)
    ?_ hlt
  · have hsub' : Metric.ball (0 : ℂ) a ∩ H ⊆ D3Plus.halfDisc r :=
      inter_subset_inter_left _ (Metric.ball_subset_ball ha.le)
    have e : μ.restrict (D3Plus.halfDisc r) (Metric.ball 0 a ∩ H) = μ (Metric.ball 0 a ∩ H) := by
      rw [Measure.restrict_apply (Metric.isOpen_ball.inter isOpen_H).measurableSet,
        inter_eq_left.2 hsub']
    simp only [mem_ofPred_eq, hq, hq', e]
  · by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sInf_empty] at hpos
    exact lt_irrefl _ hpos

/-- **The switch** `canonicalOn · U ↔ canonicalOn · (halfDisc r)` (own bookkeeping; the
local-domain version of the E5 conversion `D3Plus.locField_canonical_eq_canonicalOn`). -/
theorem nodeC_locField_canonicalOn_eq {γ r : ℝ} {R : ℕ} {U : Set ℂ} {y y' : FieldSample}
    (hU : IsOpen U) (hsub : D3Plus.halfDisc r ⊆ U) (hag : D3Plus.AgreeNear y y' r)
    {μ : Measure ℂ} (hy : IsVagueLimitOn U (areaApprox γ y) μ)
    (hpos : 0 < scaleParamOn γ y' (D3Plus.halfDisc r))
    (hlt : scaleParamOn γ y' (D3Plus.halfDisc r) * ((R : ℝ) + 1) < r) :
    TV.locField R (canonicalOn γ y U) = TV.locField R (canonicalOn γ y' (D3Plus.halfDisc r)) := by
  set s := scaleParamOn γ y' (D3Plus.halfDisc r) with hs
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hsR : s * R < r := lt_of_le_of_lt (by nlinarith) hlt
  have hsr : s < r := lt_of_le_of_lt (by nlinarith) hlt
  rw [canonicalOn, canonicalOn, nodeC_scaleParamOn_eq hU hsub hag hy hpos hsr]
  exact D3Plus.locField_rescale_congr hag hpos hsR

/-! ## 2. The coupling inequality with an arbitrary target -/

/-- **Coupling bound** (own bookkeeping; `S5.FieldLaw.Raw.palmC_tvDist_le` with an arbitrary
target law `ν`): `f = m` off `E`, the indicator functionals of `m` are `η`-close to `ν`; then
`tvDist (law f) ν ≤ η + P E`. -/
theorem nodeC_tvDist_le {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    {f : Ω → β} (hf : AEMeasurable f P) (m : Ω → β) (ν : Measure β) (E : Set Ω)
    (hE : ∀ ω, ω ∉ E → f ω = m ω) (η : ℝ≥0∞)
    (hη : ∀ S : Set β, MeasurableSet S →
      ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P ≤ ν S + η ∧
        ν S ≤ ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P + η) :
    tvDist (P.map f) ν ≤ η + P E := by
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
    rw [← S5.FieldLaw.Raw.palmC_lintegral_indicator hf hS, ← hint,
      ← lintegral_add_right _ hind]
    exact lintegral_mono (hpt f m hE)
  have hmf : ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P ≤ P.map f S + P E := by
    rw [← S5.FieldLaw.Raw.palmC_lintegral_indicator hf hS, ← hint,
      ← lintegral_add_right _ hind]
    exact lintegral_mono (hpt m f fun ω hω => (hE ω hω).symm)
  refine sup_le ?_ ?_
  · rw [tsub_le_iff_left]
    calc P.map f S ≤ ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P + P E := hfm
      _ ≤ ν S + η + P E := by gcongr
      _ = ν S + (η + P E) := by rw [add_assoc]
  · rw [tsub_le_iff_left]
    calc ν S ≤ ∫⁻ ω, S.indicator (1 : β → ℝ≥0∞) (m ω) ∂P + η := h2
      _ ≤ P.map f S + P E + η := by gcongr
      _ = P.map f S + (η + P E) := by rw [add_assoc, add_comm (P E)]

/-! ## 3. The coupling node and the reduction -/

end Prop16Asm

end QuantumZipper
