import QuantumZipper.Proofs.Thm18.R18T8aDet
import QuantumZipper.Proofs.Thm18.RT6MOGroup
import QuantumZipper.Proofs.Thm18.RT6Neg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6 (D87): the negative cocycle, exactly on the masked data

Sheffield, arXiv:1012.4797, Theorem 1.8 (2), p. 26, case `s, t < 0`. T8a
(`configEqOff_zipLenDownA_add_of`, R18T8aDet.lean) gives `Z^A_{−(ℓ₁+ℓ₂)} ≈ Z^A_{−ℓ₁} ∘ Z^A_{−ℓ₂}`
up to regularization. Its field identity is exact up to one step, the composition of two
rescalings of the regular field `unzippedField c T`, and on folded circles that step is exact
(`rescale_fc_eq`, as in `IsRegularSample.regEq_rescale_rescale`). So the two unzipped fields agree
at every folded circle (`rt6_fc_eq_zipLenDownA_add_of`, a copy of the T8a proof with this exact
last step), and the masked data agree (`rt6_ae_πdO_zipLenDownA_add`). With RT2 at the wedge
(`MaskExactFullAStmt`) and at the unzipped wedge (`MaskExactUnzAStmt`, RT6Neg.lean) this gives
the exact negative cocycle `MONegCocycleExactStmt` for the maps on the pieces.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen B2 RegClosure

/-- **T8a at every folded circle** (deterministic; copy of `configEqOff_zipLenDownA_add_of` with
the last step exact). -/
theorem rt6_fc_eq_zipLenDownA_add_of {γ ℓ₁ ℓ₂ : ℝ} (hγ : 0 < γ) (h₁ : 0 ≤ ℓ₁) (h₂ : 0 ≤ ℓ₂)
    {c : AreaConfig} (hc : Continuous c.drv) (hc0 : c.drv 0 = 0)
    (hA : ∀ t : ℝ, 0 ≤ t → ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure γ (unzippedField γ c.toPair t) S = c.area (fwdMapInv c.drv t '' S))
    (hcap : UnzipCapRegData γ c.toPair)
    (hcan : ∀ τ r : ℝ, 0 ≤ τ → 0 ≤ r → CanonRegArc γ (zipCapDown γ τ c.toPair) r)
    (hreg : ∀ t : ℝ, 0 ≤ t → IsRegularSample (unzippedField γ c.toPair t))
    (hcoc : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → (unzipLengthsOpen γ c.toPair (u + s)).1 =
      (unzipLengthsOpen γ c.toPair u).1 + (unzipLengthsOpen γ (zipCapDown γ u c.toPair) s).1)
    (hpass : (unzipLengthsOpen γ c.toPair (lenTimeOpen γ ℓ₂ c.toPair)).1 = ENNReal.ofReal ℓ₂)
    (hne : ∃ t : ℝ, 0 ≤ t ∧ ENNReal.ofReal (ℓ₁ + ℓ₂) ≤ (unzipLengthsOpen γ c.toPair t).1) :
    ∀ (d : ℂ) (r : ℝ), 0 < r → (zipLenDownA γ (ℓ₁ + ℓ₂) c).fld (foldedCircle d r) =
      (zipLenDownA γ ℓ₁ (zipLenDownA γ ℓ₂ c)).fld (foldedCircle d r) := by
  set p := c.toPair with hp
  set t₂ := lenTimeOpen γ ℓ₂ p with ht₂def
  set c₂ := zipCapDownA γ t₂ c with hc₂def
  set c' := zipCapDown γ t₂ p with hc'def
  have ht₂ : 0 ≤ t₂ := lenTimeOpen_nonneg _ _ _
  have hσ : ∀ t : ℝ, 0 ≤ t →
      areaScale (zipCapDownA γ t c).area = scaleParam γ (unzippedField γ p t) :=
    fun t ht => areaScale_zipCapDownA_eq hc hc0 ht (hA t ht)
  set a := scaleParam γ c'.1 with hadef
  have ha : 0 < a := (hcan t₂ 0 ht₂ le_rfl).1
  have hc₂a : areaScale c₂.area = a := hσ t₂ ht₂
  have hZ₂ : (zipLenDownA γ ℓ₂ c).toPair = canonConfig γ c' := toPair_canonAConfig hc₂a
  obtain ⟨hW', hW'0, hW'max⟩ := F1.zipCapDown_snd_props (γ := γ) (τ := t₂) (c := p) hc
  -- the one-step length cocycle
  have hL : ∀ s : ℝ, 0 ≤ s → (unzipLengthsOpen γ (canonConfig γ c') s).1 + ENNReal.ofReal ℓ₂ =
      (unzipLengthsOpen γ p (t₂ + a ^ 2 * s)).1 := by
    intro s hs
    have e := unzipLengthsArc_canon_of_reg hγ hW' hW'0 hW'max hs (hcan t₂ s ht₂ hs)
    have hco := hcoc t₂ (a ^ 2 * s) ht₂ (by positivity)
    rw [unzipLengthsOpen_eq] at hco hpass ⊢
    rw [e, hco, hpass, add_comm]
  set τ₁ := lenTimeOpen γ ℓ₁ (zipLenDownA γ ℓ₂ c).toPair with hτ₁def
  have hτ₁ : 0 ≤ τ₁ := lenTimeOpen_nonneg _ _ _
  have hT : lenTimeOpen γ (ℓ₁ + ℓ₂) p = t₂ + a ^ 2 * τ₁ := by
    rw [hτ₁def, hZ₂]
    exact lenTimeOpen_add_of h₁ h₂ ha hL hne
  set T := t₂ + a ^ 2 * τ₁ with hTdef
  have hT0 : 0 ≤ T := by positivity
  set σ := scaleParam γ (unzippedField γ p T) with hσdef
  have hσpos : 0 < σ := (hcan T 0 hT0 le_rfl).1
  -- the scale of the composed map, read from the carried area
  set A₁ := areaScale (zipCapDownA γ τ₁ (zipLenDownA γ ℓ₂ c)).area with hA₁def
  have hc₂c : Continuous c₂.drv := hW'
  have hA₁ : A₁ = σ / a := by
    have e1 := zipCapDownA_canonAConfig_area (γ := γ) (T := a ^ 2 * τ₁) (by positivity)
      (c := c₂) hc₂c (hc₂a ▸ ha)
    rw [hc₂a, show a ^ 2 * τ₁ / a ^ 2 = τ₁ by field_simp] at e1
    show areaScale (zipCapDownA γ τ₁ (canonAConfig γ c₂)).area = σ / a
    rw [e1, areaScale_map_inv_mul _ ha,
      areaScale_zipCapDownA_zipCapDownA hc hc0 ht₂ (by positivity), hσ _ hT0]
  have hA₁pos : 0 < A₁ := by rw [hA₁]; exact div_pos hσpos ha
  have hσA : σ = a * A₁ := by rw [hA₁]; field_simp
  have hA₃ : areaScale (zipCapDownA γ (lenTimeOpen γ (ℓ₁ + ℓ₂) p) c).area = σ := by
    rw [hT]; exact hσ _ hT0
  have hF1 : RegEq (unzippedField γ (canonConfig γ c') τ₁)
      (rescale (unzippedField γ c' (a ^ 2 * τ₁)) (Qc γ) a) :=
    WedgeUnzip.regEq_unzippedField_canonConfig (y := c'.1) (W := c'.2) hW' hW'0 hW'max ha hτ₁
      (hcan t₂ τ₁ ht₂ hτ₁).2.1 (hcan t₂ τ₁ ht₂ hτ₁).2.2.1
  have hF2 : rescale (unzippedField γ c' (a ^ 2 * τ₁)) (Qc γ) a =
      rescale (unzippedField γ p T) (Qc γ) a :=
    Cor15Group.coordChange_congr_regEq (hcap t₂ (a ^ 2 * τ₁) ht₂ (by positivity)) _ _
  have hF3 : rescale (unzippedField γ (canonConfig γ c') τ₁) (Qc γ) A₁ =
      rescale (rescale (unzippedField γ p T) (Qc γ) a) (Qc γ) A₁ := by
    rw [← hF2]
    exact Cor15Group.coordChange_congr_regEq hF1 _ _
  obtain ⟨F, hF⟩ := hreg T hT0
  have hFb := hF.rescale' (Qc γ) ha
  intro d r hr
  show rescale (unzippedField γ p (lenTimeOpen γ (ℓ₁ + ℓ₂) p)) (Qc γ)
      (areaScale (zipCapDownA γ (lenTimeOpen γ (ℓ₁ + ℓ₂) p) c).area) (foldedCircle d r) =
    rescale (unzippedField γ (zipLenDownA γ ℓ₂ c).toPair τ₁) (Qc γ) A₁ (foldedCircle d r)
  rw [hA₃, hT, hZ₂, hF3, hσA, rescale_fc_eq hFb (Qc γ) hA₁pos d hr,
    rescale_fc_eq hF (Qc γ) (mul_pos ha hA₁pos) d hr]
  have e1 : (a : ℂ) * foldH ((A₁ : ℂ) * d) = foldH (((a * A₁ : ℝ) : ℂ) * d) := by
    rw [← foldH_mul_pos _ ha]; push_cast; ring_nf
  rw [e1, show a * (A₁ * r) = a * A₁ * r by ring, Real.log_mul ha.ne' hA₁pos.ne']
  ring

/-- **Exact T8a at the wedge**: a.s. the two unzipped fields agree at every folded circle, and the
configurations agree off the curve. -/
theorem rt6_ae_zipLenDownA_add_exact (hX1 : BaseFin.BaseFiniteStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ ω ∂P, (∀ (d : ℂ) (r : ℝ), 0 < r →
      (zipLenDownA γ (a + b) (wedgeAConfig γ B Y ω)).fld (foldedCircle d r) =
        (zipLenDownA γ a (zipLenDownA γ b (wedgeAConfig γ B Y ω))).fld (foldedCircle d r)) ∧
      ConfigEqOff (zipLenDownA γ (a + b) (wedgeAConfig γ B Y ω)).toPair
        (zipLenDownA γ a (zipLenDownA γ b (wedgeAConfig γ B Y ω))).toPair := by
  have hγ : 0 < γ := hS.1
  have hYO := SWCore.yMergeOffTipStmt_holds
  have hC : LenPairCocycleArcStmt := lenPairCocycleArc_of_yMergeOffTip hYO
  have hF : LenFiniteArcStmt :=
    lenFiniteArc_of_baseFinite hX1 (wedgePairCocycleArc_of_yMergeOffTip hYO)
  have hsm : LenStrictMonoArcStmt := lenStrictMonoArc_of_yMergeOffTip hYO hC hF
  have hI : R5c.PStarLenInfArcStmt :=
    R5c.pStarLenInfArc_of (F1.pStarCanonLawStmt_of F1.wedgeAddConstLawStmt_holds)
      (pStarZipLenInputsLoc_of_yMergeOffTip hYO) R5c.lenReadTimeArc_holds hsm
      (pStarGoodOffAll_of_yMergeOffTip hYO) (unzipBdryPosArc_of_yMergeOffTip hYO) hF
  have hsurj : LenLeftSurjArcStmt :=
    lenLeftSurjArc_of_reg (lenLeftRegArc_of_yMergeOffTip hYO hC hF)
      (lenLeftUnbddArc_of_pStarLenInf hI) hC hF
  have hP := isPStarSample_of_setting hS
  have hsm' := hsm (γ ^ 2) P Y B hP
  have hsurj' := hsurj (γ ^ 2) P Y B hP
  have hGO := pStarGoodOffAll_of_yMergeOffTip hYO (γ ^ 2) P Y B hP
  have hC' := hC (γ ^ 2) P Y B hP
  have hcap' := pStarCapRegOff_of_yMergeOffTip hYO (γ ^ 2) P Y B hP
  have hcan' := lenCanonRegArc_of_yMergeOffTip hYO (γ ^ 2) P Y B hP
  rw [Real.sqrt_sq hγ.le] at hsm' hsurj' hGO hC' hcap' hcan'
  filter_upwards [unzipArea_holds γ P B Y hS, D74.ae_wedgeConfig_snd_good hS, hcan', hcap', hGO,
    hC', hsm', hsurj'] with ω hA hω hcn hcp hgo hcoc hm hsu
  have hpass : (unzipLengthsOpen γ (wedgeConfig γ B Y ω)
      (lenTimeOpen γ b (wedgeConfig γ B Y ω))).1 = ENNReal.ofReal b := by
    obtain ⟨t0, ht0, htl⟩ := hsu b hb
    have e : lenTimeOpen γ b (wedgeConfig γ B Y ω) = t0 :=
      leftTimeArc_of_eq (c := wedgeConfig γ B Y ω) hm ht0 htl
    rw [e]; exact htl
  obtain ⟨t1, ht1, htl1⟩ := hsu (a + b) (by linarith)
  exact ⟨rt6_fc_eq_zipLenDownA_add_of hγ ha.le hb.le hω.1 hω.2 hA hcp hcn
    (fun u hu => (hgo u hu).1) (fun u r hu hr => (hcoc u r hu hr).1) hpass ⟨t1, ht1, htl1.ge⟩,
    configEqOff_zipLenDownA_add_of hγ ha.le hb.le hω.1 hω.2 hA hcp hcn
    (fun u hu => (hgo u hu).1) (fun u r hu hr => (hcoc u r hu hr).1) hpass ⟨t1, ht1, htl1.ge⟩⟩

/-- Equal fields at all folded circles and equal drivers on `[0,∞)` give equal masked data. -/
theorem rt6_πdO_eq_of_fc {X X' : AreaConfig}
    (hf : ∀ (d : ℂ) (r : ℝ), 0 < r → X.fld (foldedCircle d r) = X'.fld (foldedCircle d r))
    (hd : ∀ u : ℝ, 0 ≤ u → X.drv u = X'.drv u) : πdO X = πdO X' := by
  classical
  have hcur : curveOf X.drv = curveOf X'.drv := curveOf_congr hd
  refine Prod.ext (funext fun i => ?_) (funext fun u => hd u u.2)
  show (if CircleOff (curveOf X.drv) _ _ then CoordsFull.coordsFull X.fld i else 0) =
    (if CircleOff (curveOf X'.drv) _ _ then CoordsFull.coordsFull X'.fld i else 0)
  rw [hcur]
  split_ifs
  · exact hf _ _ (UnzipFull.fullIndex_radius_pos i)
  · rfl

/-- **The exact negative cocycle for the maps on the pieces** (`MONegCocycleExactStmt`), from X1,
RT2 at the wedge and RT2 at the unzipped wedge. -/
theorem moNegCocycleExactStmt_of (hX1 : BaseFin.BaseFiniteStmt) (hMF : MaskExactFullAStmt)
    (hU : MaskExactUnzAStmt) : MONegCocycleExactStmt := by
  intro γ Ω _ P _ B Y hS hIn a b ha hb
  have hab : -(a + b) < 0 := by linarith
  rw [zipLenMO_of_neg hab, zipLenMO_of_neg (neg_lt_zero.2 ha), zipLenMO_of_neg (neg_lt_zero.2 hb)]
  simp only [neg_neg]
  filter_upwards [rt6_ae_zipLenDownA_add_exact hX1 hS ha hb, hMF γ P B Y hS hIn (a + b) (by linarith),
    hMF γ P B Y hS hIn b hb, hU γ P B Y hS hIn a ha b hb] with ω h1 h2 h3 h4
  rw [zipLenDownMA_congr_offData (ℓ := a) h3]
  have e2 : πdO (zipLenDownMA γ (a + b) (wedgeAConfig γ B Y ω)) =
      πdO (zipLenDownA γ (a + b) (wedgeAConfig γ B Y ω)) := congrArg πd h2
  rw [e2, rt6_πdO_eq_of_fc h1.1 h1.2.2]
  exact h4.symm

end R18
end QuantumZipper
