import QuantumZipper.Proofs.Section5.Prop16LitDilRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the dilation clause and the canonical-domain limit, proved (D98)

The Borel event `dilSet` on the local readings holds at the Palm-shifted readings
(`palm_mem_dilSet`: local regularity at fixed points, `dilGood_of_localAreaRegular`), hence, by
the Palm transfer (`ae_readings_of_palm`; Duplantier–Sheffield arXiv:0808.1560 §3.3), at the
weighted readings; there it forces the canonical local limit at the canonical scale
(`dil_of_dilGood`, with `scaleQ_eq_scaleParamOn`). This proves `Prop16LitDilEachStmt` and
`Prop16LitExBStmt`, hence `theorem1_6_literal` (`theorem1_6_literal_proved`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA Prop16Asm

variable {D : Set ℂ} {a b : ℝ} {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ}

theorem palm_mem_dilSet {γ : ℝ} {c d : ℝ} {h0 : ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    (hfam : LitFamily D a b ψ r₀) (C x : ℝ) (hx : x ∈ Ioo a b) :
    ∀ᵐ ω ∂P, (palmRawCoords γ D c d h0 X (repMeas D a b) (ω, x), x) ∈ dilSet hfam γ C := by
  obtain ⟨hγ, -, hgeo, -, hca, hbd, -⟩ := id hdat
  filter_upwards [ae_localAreaRegular_palm hdat hfam x hx] with ω hω
  obtain ⟨μ, hR⟩ := hω C
  have hloc := circAgree_litRep (γ := γ) (C := C) hgeo hca hbd hfam
    (ofFun h0 + palmMixedField γ D (realSet (Icc c d)) X x ω)
    (palmRawCoords γ D c d h0 X (repMeas D a b) (ω, x)) (fun i => rfl) x hx
  refine (mem_dilSet_iff hfam γ C hx).2 fun hpos => ?_
  rw [← scaleQ_congr hloc] at hpos ⊢
  exact dilGood_congr hpos hloc (dilGood_of_localAreaRegular hγ hR hpos)

/-- Both remaining clauses at a weighted point, from the event and the local limit. -/
theorem dil_and_exB_of_event {γ : ℝ} (hγ : 0 < γ) {Z : FieldSample} {r : ℝ} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn (ball 0 r ∩ H) (areaApprox γ Z) μ)
    (hE : 0 < scaleQ γ Z r → DilGood γ Z r (scaleQ γ Z r)) :
    (∃ m, IsVagueLimitOn (canonicalDomainOn γ Z (ball 0 r ∩ H))
        (areaApprox γ (canonicalOn γ Z (ball 0 r ∩ H))) m) ∧
    (0 < scaleParamOn γ Z (ball 0 r ∩ H) →
      qAreaMeasureOn γ (canonicalOn γ Z (ball 0 r ∩ H)) (canonicalDomainOn γ Z (ball 0 r ∩ H)) =
        (qAreaMeasureOn γ Z (ball 0 r ∩ H)).map
          fun z => z / (scaleParamOn γ Z (ball 0 r ∩ H) : ℂ)) := by
  have hsq := scaleQ_eq_scaleParamOn hμ
  set s := scaleParamOn γ Z (ball 0 r ∩ H) with hsdef
  have hdom : canonicalDomainOn γ Z (ball 0 r ∩ H) = (fun z => (s : ℂ) * z) ⁻¹' (ball 0 r ∩ H) :=
    rfl
  have hcan : canonicalOn γ Z (ball 0 r ∩ H) = rescale Z (Qc γ) s := rfl
  by_cases hs : 0 < s
  · have hc := dil_of_dilGood hs hμ (hsq ▸ hE (hsq ▸ hs))
    rw [← preimage_mul_ball_inter_H hs] at hc
    have ho : IsOpen ((fun z => (s : ℂ) * z) ⁻¹' (ball 0 r ∩ H)) :=
      (isOpen_ball.inter isOpen_H).preimage (continuous_const.mul continuous_id)
    refine ⟨⟨_, hdom ▸ hcan ▸ hc⟩, fun _ => ?_⟩
    rw [hdom, hcan, LocalRule.qAreaMeasureOn_eq ho hc,
      LocalRule.qAreaMeasureOn_eq (isOpen_ball.inter isOpen_H) hμ]
  · refine ⟨⟨0, by simp, fun K _ _ => by simp, fun f _ _ hfU => ?_⟩, fun h => absurd h hs⟩
    have hf0 : ∀ z ∈ H, f z = 0 := fun z hz => by
      by_contra hne
      have hmem := hfU (subset_tsupport f hne)
      have h1 : (0 : ℝ) < ((s : ℂ) * z).im := hmem.2
      rw [Complex.im_ofReal_mul] at h1
      have h2 : (0 : ℝ) < z.im := hz
      nlinarith [not_lt.1 hs]
    refine tendsto_const_nhds.congr fun k => ?_
    rw [E6.integral_areaApprox_eq, setIntegral_congr_fun isOpen_H.measurableSet
      (g := fun _ => (0 : ℝ)) fun z hz => by simp only [hf0 z hz, mul_zero]]
    simp

/-- The weighted-law event, read on the actual chart zoom. -/
theorem ae_dil_event {γ : ℝ} {c d : ℝ} {h0 : ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    (hfam : LitFamily D a b ψ r₀) (C : ℝ) :
    ∀ᵐ p ∂(prop16Q γ h0 a b P X),
      (∃ μ, IsVagueLimitOn (ball 0 (r₀ p.2) ∩ H)
        (areaApprox γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))) μ) ∧
      (0 < scaleQ γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2)) (r₀ p.2) →
        DilGood γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2)) (r₀ p.2)
          (scaleQ γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2)) (r₀ p.2))) := by
  obtain ⟨-, -, hgeo, -, hca, hbd, -⟩ := id hdat
  have hgood := ae_readings_of_palm hdat (measurableSet_dilSet hfam γ C)
    (fun x hx => palm_mem_dilSet hdat hfam C x hx)
  filter_upwards [ae_mem_Ioo_prop16Q hdat, hgood, prop16LitExA_holds hdat hfam C] with p hp1 hp2 hμ
  refine ⟨hμ, fun hpos => ?_⟩
  have hloc := circAgree_litRep (γ := γ) (C := C) hgeo hca hbd hfam (ofFun h0 + X p.1)
    (rawCoords h0 X (repMeas D a b) p.1) (fun i => rfl) p.2 hp1
  have hsymm : Prop16Area.G.CircAgree (ball 0 (r₀ p.2) ∩ H)
      (zoomFieldLit γ C (repFam D a b 0 (rawCoords h0 X (repMeas D a b) p.1)) p.2 (ψ p.2))
      (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2)) :=
    fun n k z hz hs => (hloc n k z hz hs).symm
  have hE := (mem_dilSet_iff hfam γ C hp1).1 (hp2 hp1)
  rw [scaleQ_congr hloc] at hpos ⊢
  exact dilGood_congr hpos hsymm (hE hpos)

/-- **`Prop16LitDilEachStmt`, proved.** -/
theorem prop16LitDilEachStmt_proved : Prop16LitDilEachStmt := by
  intro γ D c d a b h0 Ω _ P X hdat ψ r₀ hfam C
  filter_upwards [ae_dil_event hdat hfam C] with p ⟨⟨μ, hμ⟩, hE⟩
  exact (dil_and_exB_of_event hdat.1 hμ hE).2

/-- **`Prop16LitExBStmt`, proved.** -/
theorem prop16LitExBStmt_proved : Prop16LitExBStmt := by
  intro γ D c d a b h0 Ω _ P X hdat ψ r₀ hfam C
  filter_upwards [ae_dil_event hdat hfam C] with p ⟨⟨μ, hμ⟩, hE⟩
  exact (dil_and_exB_of_event hdat.1 hμ hE).1

/-- **Proposition 1.6, literal form (D95), proved.** -/
theorem theorem1_6_literal_proved : theorem1_6_literal :=
  theorem1_6_literal_of_dil_exB prop16LitDilEachStmt_proved prop16LitExBStmt_proved

end Prop16Lit
end QuantumZipper
