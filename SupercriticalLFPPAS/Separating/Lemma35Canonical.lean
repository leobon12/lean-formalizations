import SupercriticalLFPPAS.Separating.Lemma35
import SupercriticalLFPPAS.Core.Interfaces

/-!
# Lemma 3.5 in canonical form: the one-annulus events and their probability

Packet P35 (final target form, `planning/packets/P35-targets.md`, ruling P8): ingredients of
`lemma35_of` (`Separating/Lemma35Final.lean`), which proves `Core.Lemma35Stmt S` from
`Core.KappaBoundsStmt S` ((2.6)), `Core.ScalingDStmt S` ((1.3)), `Core.DilationStmt S` ((2.4)) and
`Core.AnnTightStmt S` (annular tightness).

The canonical one-annulus event at a centre `c` and a radius `s ≤ 1` for the pair `(D, Y_{δ,L})` is
the field-local event `B2.Polylog.plEventLoc` of [2, Lemma 3.1] with polylogarithmic parameter
`uniformLocalizationExponent δ L` (whose metric is `Core.locMetricY S δ L`). Its probability
(`p35_canEvent_prob`) follows the paper (proof of Lemma 3.5, l. 343–352; SB2 D3 step 2): by (1.3)
and (2.4) its four normalized costs are the unit-scale costs of `D` and of `Y_{δ/s,L}` for the
recentred field `h^{c,s}`, again a normalized GFF, and annular tightness bounds their tails
uniformly. The rest is the iteration, union bound and deterministic conclusion of
`Separating/Lemma35.lean` and `Separating/DetSeparation.lean` at the unit root `(0, 1)`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Separating

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog (acrossIn plEventLoc plLocMetric annAround annAt plRad
  closedAnn)
open LQGMetric (DistC DistOn addConst restrictTo circleAvg)
open LQGMetric.Blueprint (AEEventIn fieldSigma fieldSigma0On countOcc annulus)

/-! ### Transport of the costs under `u ↦ s u + c` -/

/-- The affine homeomorphism `u ↦ s • u + c` (`s > 0`). -/
def p35AffHomeo {s : ℝ} (hs : 0 < s) (c : ℂ) : ℂ ≃ₜ ℂ :=
  (B2.Polylog.dilateHomeo hs).trans (Homeomorph.addRight c)

theorem p35AffHomeo_apply {s : ℝ} (hs : 0 < s) (c u : ℂ) : p35AffHomeo hs c u = s • u + c := rfl

theorem p35AffHomeo_image {s : ℝ} (hs : 0 < s) (c : ℂ) (X : Set ℂ) :
    p35AffHomeo hs c '' X = (fun x => x + c) '' ((fun x => s • x) '' X) := by
  rw [Set.image_image]
  rfl

/-- **Transport of the local across cost** under `u ↦ s u + c`. -/
theorem p35_acrossIn_affine {m M : LSCMetric} {k : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (c : ℂ)
    {s : ℝ} (hs : 0 < s) (hm : ∀ x y : ℂ, m (x, y) = k * M (s • x + c, s • y + c)) :
    acrossIn m 0 1 2 = k * acrossIn M c s (2 * s) := by
  unfold acrossIn
  rw [B2.Polylog.compactPathInf_comp_mul hk0 hkt (p35AffHomeo hs c) hm, p35AffHomeo_image,
    p35AffHomeo_image, p35AffHomeo_image, B2.Polylog.image_smul_closedAnn hs,
    B2.Polylog.image_smul_sphere hs, B2.Polylog.image_smul_sphere hs, B2.Polylog.image_add_closedAnn,
    B2.Polylog.image_add_sphere, B2.Polylog.image_add_sphere, smul_zero, zero_add, mul_one,
    mul_comm s 2]

/-- **Transport of the around cost** under `u ↦ s u + c`. -/
theorem p35_aroundDist_affine {m M : LSCMetric} {k : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (c : ℂ)
    {s : ℝ} (hs : 0 < s) (hm : ∀ x y : ℂ, m (x, y) = k * M (s • x + c, s • y + c))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    aroundDist m (annAt 0 a b ha hab) =
      k * aroundDist M (annAt c (s * a) (s * b) (mul_pos hs ha) (mul_lt_mul_of_pos_left hab hs)) := by
  obtain ⟨h1, h2, h3⟩ := B2.Polylog.image_dilate_annAt hs 0 a b ha hab
  obtain ⟨g1, g2, g3⟩ := B2.Polylog.image_translate_annAt c ((s : ℝ) • (0 : ℂ)) (s * a) (s * b)
    (mul_pos hs ha) (mul_lt_mul_of_pos_left hab hs)
  have himg : ∀ X : Set ℂ, p35AffHomeo hs c '' X =
      (Homeomorph.addRight c) '' ((B2.Polylog.dilateHomeo hs) '' X) := fun X => by
    rw [Set.image_image]
    rfl
  have hcenter : annAt ((s : ℝ) • (0 : ℂ) + c) (s * a) (s * b) (mul_pos hs ha)
      (mul_lt_mul_of_pos_left hab hs) = annAt c (s * a) (s * b) (mul_pos hs ha)
      (mul_lt_mul_of_pos_left hab hs) :=
    B2.Polylog.annAt_congr (by rw [smul_zero, zero_add]) rfl rfl _ _ _ _
  have key := B2.Polylog.aroundDist_comp_mul hk0 hkt (p35AffHomeo hs c) hm (annAt 0 a b ha hab)
    (annAt ((s : ℝ) • (0 : ℂ) + c) (s * a) (s * b) (mul_pos hs ha) (mul_lt_mul_of_pos_left hab hs))
    (by rw [himg, h1, g1]) (by rw [himg, h2, g2]) (by rw [himg, h3, g3])
  rw [key, hcenter]

/-! ### The one-annulus costs at the unit scale -/

/-- The unit annuli `A_{1,2}(0)` and `A_{2,3}(0)` of [2, Lemma 3.1]. -/
def p35A12 : EuclideanAnnulus := annAt 0 1 2 one_pos one_lt_two

/-- See `p35A12`. -/
def p35A23 : EuclideanAnnulus := annAt 0 2 3 two_pos (by norm_num)

theorem p35_ofReal_inv_eq {x : ℝ} (hx : 0 < x) :
    (ENNReal.ofReal x)⁻¹ = ENNReal.ofReal x⁻¹ := (ENNReal.ofReal_inv_of_pos hx).symm

/-- **(1.3) for the one-annulus costs**: if `D_g(c + s u, c + s v) = s^{ξQ} e^{ξ g_s(c)} D_{g'}(u, v)`,
the normalized local across and around costs of `D_g` at `(c, s)` are the unit-scale costs of
`D_{g'}`. -/
theorem p35_D_costs_scale (S : Core.Setup) {g g' : DistC} (c : ℂ) (s : Set.Ioi (0 : ℝ))
    (hsc : ∀ u v : ℂ, S.D g (c + (s : ℝ) • u, c + (s : ℝ) • v) =
      ENNReal.ofReal ((s : ℝ) ^ ((S.ξ : ℝ) * S.Q) * Real.exp ((S.ξ : ℝ) * circleAvg g s c)) *
        S.D g' (u, v)) :
    B2.Polylog.normD (S.ξ : ℝ) (Compare.powScale S.ξ S.Q) g c s * acrossIn (S.D g) c s (2 * s) =
        acrossIn (S.D g') 0 1 2 ∧
    B2.Polylog.normD (S.ξ : ℝ) (Compare.powScale S.ξ S.Q) g c s * aroundDist (S.D g) (annAround c s) =
        aroundDist (S.D g') p35A23 := by
  have hs : (0 : ℝ) < s := s.2
  set F : ℝ := (s : ℝ) ^ ((S.ξ : ℝ) * S.Q) * Real.exp ((S.ξ : ℝ) * circleAvg g s c) with hF
  have hFpos : 0 < F := by
    have := Real.rpow_pos_of_pos hs ((S.ξ : ℝ) * S.Q)
    positivity
  have hk0 : (ENNReal.ofReal F)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hkt : (ENNReal.ofReal F)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by simpa using hFpos)
  have hm : ∀ x y : ℂ, S.D g' (x, y) = (ENNReal.ofReal F)⁻¹ * S.D g ((s : ℝ) • x + c, (s : ℝ) • y + c) := by
    intro x y
    rw [add_comm _ c, add_comm _ c, hsc x y, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simpa using hFpos) ENNReal.ofReal_ne_top, one_mul]
  have hnorm : B2.Polylog.normD (S.ξ : ℝ) (Compare.powScale S.ξ S.Q) g c s = (ENNReal.ofReal F)⁻¹ := by
    rw [p35_ofReal_inv_eq hFpos]
    unfold B2.Polylog.normD
    congr 1
    simp only [Compare.powScale, hF]
    rw [mul_inv, Real.exp_neg]
  refine ⟨?_, ?_⟩
  · rw [hnorm, p35_acrossIn_affine hk0 hkt c hs hm]
  · rw [hnorm, p35A23, p35_aroundDist_affine hk0 hkt c hs hm 2 3 two_pos (by norm_num)]
    congr 2
    exact B2.Polylog.annAt_congr rfl (mul_comm _ _) (mul_comm _ _) _ _ _ _

/-- **(2.4) for the one-annulus costs**: the normalized local across and around costs of `Y_{δ,L}[g]`
at `(c, s)` are the unit-scale costs of `Y_{δ/s,L}[g^{c,s}]`. -/
theorem p35_Y_costs_scale (S : Core.Setup) (hDil : Core.DilationStmt S) (δ L : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (s : Set.Ioi (0 : ℝ)) (hδs : δ / s ∈ Ioo (0 : ℝ) 1)
    (h1 : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L) (h1s : 1 < Real.log (δ / s)⁻¹)
    (hLs : Real.log (δ / s)⁻¹ ≤ L) (c : ℂ) (g : DistC) :
    B2.Polylog.normL (S.ξ : ℝ) S.m ⟨δ, hδ.1⟩ g c s * acrossIn (Core.locMetricY S δ L hδ g) c s (2 * s) =
        acrossIn (Core.locMetricY S (δ / s) L hδs (Core.recentred s c g)) 0 1 2 ∧
    B2.Polylog.normL (S.ξ : ℝ) S.m ⟨δ, hδ.1⟩ g c s *
        aroundDist (Core.locMetricY S δ L hδ g) (annAround c s) =
        aroundDist (Core.locMetricY S (δ / s) L hδs (Core.recentred s c g)) p35A23 := by
  have hs : (0 : ℝ) < s := s.2
  have hsc := (hDil.2 δ L hδ s hδs h1 hL h1s hLs c (circleAvg g s c) g).2
  set F : ℝ := (s : ℝ) * (S.m ⟨δ / s, hδs.1⟩ : ℝ) / (S.m ⟨δ, hδ.1⟩ : ℝ) *
    Real.exp ((S.ξ : ℝ) * circleAvg g s c) with hF
  have hm1 := (S.m ⟨δ / s, hδs.1⟩).2
  have hm2 := (S.m ⟨δ, hδ.1⟩).2
  simp only [Set.mem_Ioi] at hm1 hm2
  have hFpos : 0 < F := by positivity
  have hk0 : (ENNReal.ofReal F)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hkt : (ENNReal.ofReal F)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by simpa using hFpos)
  have hm : ∀ x y : ℂ, Core.locMetricY S (δ / s) L hδs (Core.recentred s c g) (x, y) =
      (ENNReal.ofReal F)⁻¹ * Core.locMetricY S δ L hδ g ((s : ℝ) • x + c, (s : ℝ) • y + c) := by
    intro x y
    rw [add_comm _ c, add_comm _ c, hsc x y, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simpa using hFpos) ENNReal.ofReal_ne_top, one_mul]
    rfl
  have hnorm : B2.Polylog.normL (S.ξ : ℝ) S.m ⟨δ, hδ.1⟩ g c s = (ENNReal.ofReal F)⁻¹ := by
    rw [p35_ofReal_inv_eq hFpos]
    unfold B2.Polylog.normL B2.Polylog.lfppScaleFactor
    congr 1
    rw [hF, mul_inv, Real.exp_neg]
  refine ⟨?_, ?_⟩
  · rw [hnorm, p35_acrossIn_affine hk0 hkt c hs hm]
  · rw [hnorm, p35A23, p35_aroundDist_affine hk0 hkt c hs hm 2 3 two_pos (by norm_num)]
    congr 2
    exact B2.Polylog.annAt_congr rfl (mul_comm _ _) (mul_comm _ _) _ _ _ _

/-! ### Probability of the canonical one-annulus event -/

/-- A lower bound for `P E` from an upper bound for `P Eᶜ`. -/
theorem p35_prob_ge_of_compl_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Set Ω} (hE : MeasurableSet E) {x : ℝ} (hx : x ≤ 1)
    (h : P Eᶜ ≤ ENNReal.ofReal (1 - x)) : ENNReal.ofReal x ≤ P E := by
  have hsum := measure_add_measure_compl (μ := P) hE
  rw [measure_univ] at hsum
  by_contra hlt
  push Not at hlt
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [ENNReal.ofReal_of_nonpos hx0] at hlt
    exact absurd hlt (not_lt.2 bot_le)
  have : P E + P Eᶜ < ENNReal.ofReal x + ENNReal.ofReal (1 - x) :=
    ENNReal.add_lt_add_of_lt_of_le (measure_ne_top P _) hlt h
  rw [hsum, ← ENNReal.ofReal_add hx0.le (by linarith), show x + (1 - x) = 1 by ring,
    ENNReal.ofReal_one] at this
  exact lt_irrefl _ this

/-- **Probability of the canonical one-annulus event** (SB2 D3 step 2): under (1.3), (2.4) and
annular tightness of `D` and `Y` at the unit annuli with constant `Mt` and failure `ϑ`, the event
`E^δ_s(c; C)` for `(D, Y_{δ,L})`, `C ≥ Mt`, fails with probability at most `4ϑ` whenever `δ/s`
is below the tightness threshold. -/
theorem p35_canEvent_compl_le (S : Core.Setup) (hS : Core.ScalingDStmt S)
    (hDil : Core.DilationStmt S) {Mt δT ϑ : ℝ} (hMt : 0 < Mt)
    (hTD : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        P {ω | acrossDist (S.D (h ω)) p35A12 < ENNReal.ofReal Mt⁻¹} ≤ ENNReal.ofReal ϑ ∧
        P {ω | ENNReal.ofReal Mt < aroundDist (S.D (h ω)) p35A23} ≤ ENNReal.ofReal ϑ)
    (hTY : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1), δ < δT → ∀ L : ℝ, Real.log δ⁻¹ ≤ L →
          P {ω | acrossDist (Core.locMetricY S δ L hδ (h ω)) p35A12 < ENNReal.ofReal Mt⁻¹} ≤
              ENNReal.ofReal ϑ ∧
          P {ω | ENNReal.ofReal Mt < aroundDist (Core.locMetricY S δ L hδ (h ω)) p35A23} ≤
              ENNReal.ofReal ϑ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (c : ℂ) (s : Set.Ioi (0 : ℝ)) (δ L : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hδs : δ / s ∈ Ioo (0 : ℝ) 1) (hδsT : δ / s < δT)
    (h1 : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L) (h1s : 1 < Real.log (δ / s)⁻¹)
    (hLs : Real.log (δ / s)⁻¹ ≤ L) {C : ℝ} (hC : Mt ≤ C) :
    P {ω | h ω ∈ plEventLoc (S.ξ : ℝ) S.D (Compare.powScale S.ξ S.Q) S.m
      (Field.uniformLocalizationExponent δ L) c δ hδ s C}ᶜ ≤ 4 * ENNReal.ofReal ϑ := by
  set h' : Ω → DistC := fun ω => Core.recentred s c (h ω) with hh'def
  obtain ⟨hh', hae⟩ := hS P h hh s c
  obtain ⟨hB1, hB2⟩ := hTD P h' hh'
  obtain ⟨hB3, hB4⟩ := hTY P h' hh' (δ / s) hδs hδsT L hLs
  set B₁ := {ω | acrossDist (S.D (h' ω)) p35A12 < ENNReal.ofReal Mt⁻¹}
  set B₂ := {ω | ENNReal.ofReal Mt < aroundDist (S.D (h' ω)) p35A23}
  set B₃ := {ω | acrossDist (Core.locMetricY S (δ / s) L hδs (h' ω)) p35A12 < ENNReal.ofReal Mt⁻¹}
  set B₄ := {ω | ENNReal.ofReal Mt < aroundDist (Core.locMetricY S (δ / s) L hδs (h' ω)) p35A23}
  have hCpos : 0 < C := lt_of_lt_of_le hMt hC
  have hCinv : ENNReal.ofReal C⁻¹ ≤ ENNReal.ofReal Mt⁻¹ :=
    ENNReal.ofReal_le_ofReal (inv_anti₀ hMt hC)
  have hMtC : ENNReal.ofReal Mt ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC
  have hsub : {ω | h ω ∈ plEventLoc (S.ξ : ℝ) S.D (Compare.powScale S.ξ S.Q) S.m
      (Field.uniformLocalizationExponent δ L) c δ hδ s C}ᶜ ≤ᵐ[P] B₁ ∪ B₂ ∪ B₃ ∪ B₄ := by
    filter_upwards [hae] with ω hω hnot
    by_contra hbad
    simp only [mem_union, not_or] at hbad
    obtain ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩ := hbad
    simp only [B₁, B₂, B₃, B₄, mem_ofPred_eq, not_lt] at h1' h2' h3' h4'
    apply hnot
    obtain ⟨hDa, hDr⟩ := p35_D_costs_scale S c s hω
    obtain ⟨hYa, hYr⟩ := p35_Y_costs_scale S hDil δ L hδ s hδs h1 hL h1s hLs c (h ω)
    refine ⟨?_, ?_, ?_, ?_⟩
    · show ENNReal.ofReal C⁻¹ ≤ B2.Polylog.normD (S.ξ : ℝ) (Compare.powScale S.ξ S.Q) (h ω) c s *
        acrossIn (S.D (h ω)) c s (2 * s)
      rw [hDa]
      exact hCinv.trans (h1'.trans (B2.Polylog.acrossDist_le_acrossIn _ _ _ _))
    · show B2.Polylog.normD (S.ξ : ℝ) (Compare.powScale S.ξ S.Q) (h ω) c s *
        aroundDist (S.D (h ω)) (annAround c s) ≤ ENNReal.ofReal C
      rw [hDr]
      exact h2'.trans hMtC
    · show ENNReal.ofReal C⁻¹ ≤ B2.Polylog.normL (S.ξ : ℝ) S.m ⟨δ, hδ.1⟩ (h ω) c s *
        acrossIn (Core.locMetricY S δ L hδ (h ω)) c s (2 * s)
      rw [hYa]
      exact hCinv.trans (h3'.trans (B2.Polylog.acrossDist_le_acrossIn _ _ _ _))
    · show B2.Polylog.normL (S.ξ : ℝ) S.m ⟨δ, hδ.1⟩ (h ω) c s *
        aroundDist (Core.locMetricY S δ L hδ (h ω)) (annAround c s) ≤ ENNReal.ofReal C
      rw [hYr]
      exact h4'.trans hMtC
  calc P {ω | h ω ∈ plEventLoc (S.ξ : ℝ) S.D (Compare.powScale S.ξ S.Q) S.m
        (Field.uniformLocalizationExponent δ L) c δ hδ s C}ᶜ
      ≤ P (B₁ ∪ B₂ ∪ B₃ ∪ B₄) := measure_mono_ae hsub
    _ ≤ P B₁ + P B₂ + P B₃ + P B₄ := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal ϑ + ENNReal.ofReal ϑ + ENNReal.ofReal ϑ + ENNReal.ofReal ϑ := by
        gcongr
    _ = 4 * ENNReal.ofReal ϑ := by ring

end SupercriticalLFPPAS.Separating
