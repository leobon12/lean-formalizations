import QuantumZipper.Proofs.Thm18.RT6NegEx
import QuantumZipper.Proofs.Thm18.RTBeurMain
import QuantumZipper.Proofs.Thm18.R18T6Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6b: RT2 at the unzipped wedge (`MaskExactUnzAStmt`)

RT2 (Sheffield §4.1 p. 48; Berestycki–Powell arXiv:2404.16642 Thm 8.16, Rem 8.10) at the
configuration `c₁ = Z^A_{−b} c₀`, by the same deterministic route as at `c₀`
(`maskExactFull_of_core`): `offData_zipLenDownA_eq_of_pullOff` with the core estimate
`evalReg_eq_readOffField_of_bounds` (log growth of circle averages, Hu–Miller–Peres 2010 Prop 2.1)
and the Beurling mass bound (`RTBeur.pointwise_det`, Lawler arXiv:0712.3256 Thm 2.10), applied to
the unzipped configuration. Inputs at `c₁`: the driver of `c₁` is a good chordal driver
(`UnzDriverGoodStmt`: the strong Markov property of SLE at the length time, Sheffield Thm 1.8 /
E6) and the log growth of the circle averages of `c₁`'s field (`UnzGrowthStmt`; `c₁` has the full
data law of `c₀`, E6). The area identity and the positivity of the unzipping scale at `c₁` are
proved (T6, and the T8a computation).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen B2 RegClosure

/-- Positivity of the unzipping scale at an unzipped configuration (deterministic; the T8a
computation `A₁ = σ / a`). -/
theorem rt6b_scale_pos_zipLenDownA_of {γ ℓ₁ ℓ₂ : ℝ} (hγ : 0 < γ) (h₁ : 0 ≤ ℓ₁) (h₂ : 0 ≤ ℓ₂)
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
    0 < areaScale (zipCapDownA γ (lenTimeOpen γ ℓ₁ (zipLenDownA γ ℓ₂ c).toPair)
      (zipLenDownA γ ℓ₂ c)).area := by
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
  exact hA₁pos

theorem rt6b_ae_scale_pos_unz (hX1 : BaseFin.BaseFiniteStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < areaScale (zipCapDownA γ (lenTimeOpen γ a
      (zipLenDownA γ b (wedgeAConfig γ B Y ω)).toPair) (zipLenDownA γ b (wedgeAConfig γ B Y ω))).area := by
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
  exact rt6b_scale_pos_zipLenDownA_of hγ ha.le hb.le hω.1 hω.2 hA hcp hcn
    (fun u hu => (hgo u hu).1) (fun u r hu hr => (hcoc u r hu hr).1) hpass ⟨t1, ht1, htl1.ge⟩

/-- **The unzipped driver is a good chordal driver** (open): a.s. the driver of `Z^A_{−b} c₀` has the
radial Hölder property, its trace is a simple chord and its hulls are its trace (strong Markov
property of SLE at the length time; by E6 its law is that of the SLE driver). -/
def UnzDriverGoodStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P,
      RS.RadialGood (zipLenDownA γ b (wedgeAConfig γ B Y ω)).drv ∧
      IsSimpleChord (trace (zipLenDownA γ b (wedgeAConfig γ B Y ω)).drv) ∧
      ∀ t : ℝ, 0 ≤ t → fwdHull (zipLenDownA γ b (wedgeAConfig γ B Y ω)).drv t =
        trace (zipLenDownA γ b (wedgeAConfig γ B Y ω)).drv '' Ioc 0 t

/-- **Log growth of the circle averages of the unzipped field** (open; `CircAvgLogGrowthStmt` at
`Z^A_{−b} c₀`, which has the full-data law of `c₀` by E6). -/
def UnzGrowthStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P,
      ∀ Rr : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k n : ℕ) (w : ℂ), ‖w‖ ≤ Rr →
        |(zipLenDownA γ b (wedgeAConfig γ B Y ω)).fld
          (foldedCircle (dyadicRoundC n w) (radius k))| ≤ C * (k + 1)

/-- The Beurling mass bound for a good driver (deterministic part of
`RTBeur.pullMassBoundStmt_holds`). -/
theorem rt6b_mass_of_good {V : ℝ → ℝ} (hRG : RS.RadialGood V) (hsc : IsSimpleChord (trace V))
    (hhull : ∀ t : ℝ, 0 ≤ t → fwdHull V t = trace V '' Ioc 0 t) {s : ℝ} (hs : 0 ≤ s) {a : ℝ}
    (ha : 0 < a) {d : ℂ} {k₀ : ℕ} (hoff : CircleOff (unzCurve V s a) d (radius k₀)) :
    ∃ Rr Cm q : ℝ, 0 ≤ Cm ∧ 0 ≤ q ∧ q < 1 ∧
      (foldedCircle d (radius k₀)).map (fwdMapInv V s) {w | ¬ ‖w‖ ≤ Rr} = 0 ∧
      ∀ k : ℕ, (foldedCircle d (radius k₀)).map (fwdMapInv V s)
        {w | min (infDist w (curveOf V)) (infDist w ((starRingEnd ℂ) '' curveOf V)) ≤ radius k} ≤
          ENNReal.ofReal (Cm * q ^ k) := by
  obtain ⟨δ₀, hδ₀, hmarg⟩ := RTBeur.margin_of_circleOff hoff
  obtain ⟨Rr, A, ρ₀, hA, hρ₀, hsupp, hkey⟩ := RTBeur.pointwise_det hRG hsc hhull hs ha hδ₀ hmarg
  have hr : 0 < radius k₀ := by unfold radius; positivity
  obtain ⟨Cm, q, hCm, hq0, hq1, h1, h2⟩ := RTBeur.mass_of_pointwise
    (RTBeur.measurable_fwdMapInv_rt hRG.1 hRG.2.1 hs)
    (Φ := fun w => min (infDist w (curveOf V)) (infDist w (conj '' curveOf V)))
    ((continuous_infDist_pt _).min (continuous_infDist_pt _)) hr hA hρ₀ hsupp hkey
  exact ⟨Rr, Cm, q, hCm, hq0, hq1, h1, h2⟩

/-- **RT2 at the unzipped wedge** from X1, the goodness of the unzipped driver and the log growth
of the unzipped field. -/
theorem maskExactUnzAStmt_of (hX1 : BaseFin.BaseFiniteStmt) (hG : UnzDriverGoodStmt)
    (hGr : UnzGrowthStmt) : MaskExactUnzAStmt := by
  intro γ Ω _ P _ B Y hS hIn a ha b hb
  filter_upwards [hG γ P B Y hS hIn b hb, hGr γ P B Y hS hIn b hb,
    ae_zipLenDownA_area_eq_and_good hS hIn b, rt6b_ae_scale_pos_unz hX1 hS ha hb,
    D74.ae_wedgeConfig_snd_good hS] with ω hgood hgr harea hpos hω
  set c₁ := zipLenDownA γ b (wedgeAConfig γ B Y ω) with hc₁
  obtain ⟨hRG, hsc, hhull⟩ := hgood
  have hc1 := zipLenDownA_drv_good (γ := γ) (ℓ := b) (c := wedgeAConfig γ B Y ω) hω.1
  unfold zipLenDownMA
  refine congrArg πd (offData_zipLenDownA_eq_of_pullOff ?_ ?_ ?_ ?_ ?_).symm
  · -- drivers
    funext r
    show c₁.drv r = c₁.drv (max r 0)
    have e : c₁.drv = (c₁.toPair).2 := rfl
    rw [e, hc₁, zipLenDownA_toPair_eq]
    simp only [outDrv, max_eq_left (le_max_right r 0)]
  · exact harea.1
  · intro s hs a' ha' d k₀ hoff
    obtain ⟨Rr, Cm, q, hCm, hq0, hq1, hsupp, hmass⟩ := rt6b_mass_of_good hRG hsc hhull hs ha' hoff
    obtain ⟨C, hC, hgr'⟩ := hgr Rr
    exact evalReg_eq_readOffField_of_bounds (x := c₁.toPair) hc1.1 hc1.2 hC hCm hq0
      hq1 hsupp hgr' fun k =>
        (measure_mono fun w hw => min_infDist_le_of_not_circleOff hw).trans (hmass k)
  · intro s hs t ht
    exact neg_real_not_mem_curveOf_outDrv hRG hsc.2.2.1 hsc.2.2.2.1 hsc.2.2.2.2 hs (hhull s hs) ht
  · exact hpos

end R18
end QuantumZipper
