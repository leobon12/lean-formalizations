/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovShiftIn

/-!
# The late positive cover in R100's relifted chart

Packet PROVE-COLLAR-COVER (third round). Ruling R100: the tops relift the counterflow (base) chart by `2π(n − 1)`
(SIDE-COLLAR2's `SideC17.zeroFrameChart c n = shiftChart c (1 − n)`, `n` the sample-dependent source branch), so the
counterflow offset is `0` on every test, with no refinement. The old (reference) charts are relifted the same way.
Here the cover is ported to that chart:

* `VisitReferenceHeightCoverPosExcS` (def): the cover with a side datum read at each sample (`sideS j ω`);
* `VisitReferenceHeightCoverPosExcShift` (def): the cover with the reference charts relifted,
  `old := shiftChart (j.referenceVisitChart …) (m j ω)` (lift `old.2.2 − 2π m`), the side data unchanged;
* **`visitReferenceHeightCoverPosExcShift_of_S`**: the relifted cover from the sample-dependent one with offset
  `offset − χ·2π m` (a relift by `−2πm` lowers every height by `χ·2πm`);
* `mem_seed_interval_of_domain_landing`: a current coordinate landing in the pocket lies in the open seed interval;
* **`visitReferenceHeightCoverPosExcS_of_split`**: R5-WALL's three-piece split for sample-dependent side data, the
  exposed pieces read for a constant side family `side0` with the same `phase − offset`;
* **`visitReferenceHeightCoverPosExcShift_colCov`**: **the relifted cover** (`X = colCovExc`, finite) from the
  relifted initial mean formula (`χ·(shiftChart baseChart m).2.2` in place of the base lift — the form of
  SIDE-COLLAR2's `initialMeanFormula_zeroFrame_of_ready` with `m = 1 − n` and offset `0`), `LateSeedLand` and the phase
  condition in the relifted frame, `phase = χ·2π (lateCurPhaseInt − m) + offset` (the phase index tied to the
  relifted current integer).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest LocalSets WholeField
open PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PocketStopWallsFin
  R5Ref R5Lift Aux119Heights
open Wire.Current.SideTest (rationalOriginalTime)

/-- **The late cover with a side datum read at each sample** (`VisitReferenceHeightCoverPosExc` with `side j`
replaced by `sideS j ω`). -/
def VisitReferenceHeightCoverPosExcS {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (sideS : SideTest Ω → Ω → Late.SideData Ω)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ q : ℝ≥0, 0 < q → ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ r, IsLocalSetMean (j.capacityReference i d (s j r))
      target.zeroField d.measure (gB r)) →
    ∀ᵐ ω ∂d.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      let current := relChart target.baseChart target.curve q ω;
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a q ω -
          segDriver (target.curve ω) q)
        (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a q ω -
          segDriver (target.curve ω) q) →
        extendFrom H current.2.1 (ξ : ℂ) ∉ X j q ω →
        ∃ (r : ℕ) (x ε b : ℝ), let old := j.referenceVisitChart i d ω (s j r);
          d.curve ω (s j r) ∈ target.domain ω ∧
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q ∧ 0 < ε ∧
          old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (current.dom : Set ℂ) ∧
          Tendsto (fun z => old.1 (current.2.1 z))
            (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (sideMean target.kappa old target.harmonic
            (harmRep (gB r ω) (H \ j.capacityReference i d (s j r) ω)))
            (𝓝[H] (x : ℂ)) (𝓝 b) ∧
          b = forceBoundaryData target.kappa target.rhoL target.rhoR
            (fun a => geomLW (fun t ω => segDriver (target.curve ω) t)
              target.marksL a q ω - segDriver (target.curve ω) q)
            (fun a => geomRW (fun t ω => segDriver (target.curve ω) t)
              target.marksR a q ω - segDriver (target.curve ω) q)
            ξ + (sideS j ω).phase q ω * (Ioo
              (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL q ω -
                segDriver (target.curve ω) q)
              (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR q ω -
                segDriver (target.curve ω) q)).indicator 1 ξ - (sideS j ω).offset

/-- **The late cover in the relifted chart**: `VisitReferenceHeightCoverPosExc` with every reference chart relifted by
`−2π m` (`PocketStopField.shiftChart`), the side data unchanged. With `m = 1 − n` this is R100's zero-frame chart. -/
def VisitReferenceHeightCoverPosExcShift {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω) (m : SideTest Ω → Ω → ℤ)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ q : ℝ≥0, 0 < q → ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ r, IsLocalSetMean (j.capacityReference i d (s j r))
      target.zeroField d.measure (gB r)) →
    ∀ᵐ ω ∂d.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      let current := relChart target.baseChart target.curve q ω;
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a q ω -
          segDriver (target.curve ω) q)
        (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a q ω -
          segDriver (target.curve ω) q) →
        extendFrom H current.2.1 (ξ : ℂ) ∉ X j q ω →
        ∃ (r : ℕ) (x ε b : ℝ), let old := PocketStopField.shiftChart (j.referenceVisitChart i d ω (s j r)) (m j ω);
          d.curve ω (s j r) ∈ target.domain ω ∧
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q ∧ 0 < ε ∧
          old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (current.dom : Set ℂ) ∧
          Tendsto (fun z => old.1 (current.2.1 z))
            (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (sideMean target.kappa old target.harmonic
            (harmRep (gB r ω) (H \ j.capacityReference i d (s j r) ω)))
            (𝓝[H] (x : ℂ)) (𝓝 b) ∧
          b = forceBoundaryData target.kappa target.rhoL target.rhoR
            (fun a => geomLW (fun t ω => segDriver (target.curve ω) t)
              target.marksL a q ω - segDriver (target.curve ω) q)
            (fun a => geomRW (fun t ω => segDriver (target.curve ω) t)
              target.marksR a q ω - segDriver (target.curve ω) q)
            ξ + (side j).phase q ω * (Ioo
              (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL q ω -
                segDriver (target.curve ω) q)
              (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR q ω -
                segDriver (target.curve ω) q)).indicator 1 ξ - (side j).offset

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The relifted cover from the sample-dependent one**: relifting a reference chart by `−2π m` lowers its height
reading by `χ·2π m`, so the sample-dependent cover with offset `offset − χ·2π m` is the relifted cover. -/
theorem visitReferenceHeightCoverPosExcShift_of_S (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (m : SideTest Ω → Ω → ℤ) (s : SideTest Ω → ℕ → ℝ≥0)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (h : VisitReferenceHeightCoverPosExcS i d (fun j ω => { side j with
      offset := (side j).offset - chiC (j.target i d).kappa * (2 * Real.pi * m j ω) }) s X) :
    VisitReferenceHeightCoverPosExcShift i d side m s X := by
  intro j hj target zL zR q hq gB hgB
  filter_upwards [h j hj q hq gB hgB] with ω hω hE hlive current ξ hξ hX
  obtain ⟨r, x, ε, b, h1, h2, h3, h4, h5, h6, hb⟩ := hω hE hlive ξ hξ hX
  refine ⟨r, x, ε, b - chiC target.kappa * (2 * Real.pi * m j ω), h1, h2, h3, h4, h5, ?_, ?_⟩
  · refine (h6.sub_const (chiC target.kappa * (2 * Real.pi * m j ω))).congr' (Eventually.of_forall fun y => ?_)
    simp only [sideMean, PocketStopField.shiftChart]
    ring
  · rw [hb]
    ring

/-- A current coordinate landing in the pocket lies in the open seed interval. -/
theorem mem_seed_interval_of_domain_landing {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hE : ω ∈ (j.target i d).event) {q : ℝ≥0} (hlive : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) {ξ : ℝ}
    (hC : extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∈
      (j.target i d).domain ω) :
    ξ ∈ Ioo (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
          (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
        (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
          (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q) := by
  obtain ⟨⟨hcc, -, -⟩, ⟨E, hE', hEc⟩, -⟩ := baseChart_aux29Facts (i := i) hj hE
  have hγ := isDrivenCurve_target (i := i) hj ω hE
  have hcdom : (((j.target i d).baseChart ω).dom : Set ℂ) = (j.target i d).domain ω :=
    ((isPocketChartOn hj hRc hLc (i := i)).1 ω hE).2.1
  obtain ⟨Fc, hFc, hFcc, -⟩ := exists_relative_inverse_extension (c := (j.target i d).baseChart)
    (γ := (j.target i d).curve) hγ hlive hE' hEc
  have hcurland := (tendsto_of_ext hFc hFcc ξ)
  rw [hcurland.2] at hcurland
  obtain ⟨hmL, hmR⟩ := target_seed_marks j i d ω
  exact mem_seed_interval_of_landing (iL := Late.leftZero i d j) (iR := Late.rightZero i d j) hmL hmR hcc
    hγ hlive hcurland.1 (show _ ∈ (((j.target i d).baseChart ω).dom : Set ℂ) by rw [hcdom]; exact hC)

/-- **R5-WALL's three-piece split for sample-dependent side data**: the initial heights of every test with the datum
read at each sample, the incoming wall selection, and the exposed covers (outer and hull) for a constant side family
`side0` with the same `phase − offset` (on the open seed interval the word reads only `phase − offset`). -/
theorem visitReferenceHeightCoverPosExcS_of_split (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (sideS : SideTest Ω → Ω → Late.SideData Ω) (side0 : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens) (s : SideTest Ω → ℕ → ℝ≥0)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ j : SideTest Ω, j.Ready d → ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ j : SideTest Ω, j.Ready d → ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j : SideTest Ω, j.Ready d → ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hHarm : EqOn d.harmonic d.coupledMean H)
    (hG : ∀ j : SideTest Ω, j.Ready d →
      IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure (G j))
    (hInitial : ∀ j : SideTest Ω, j.Ready d → ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ x : ℝ,
      x ∉ (j.target i d).jumps 0 ω →
      Tendsto (sideMean (j.target i d).kappa ((j.target i d).baseChart ω) (j.target i d).harmonic
        (harmRep (G j ω) (H \ j.capacityReference i d 0 ω))) (𝓝[H] (x : ℂ))
        (𝓝 (j.nativeSideWord i d (sideS j ω) 0 ω x)))
    (hphase : ∀ j q ω, (sideS j ω).phase q ω - (sideS j ω).offset = (side0 j).phase q ω - (side0 j).offset)
    (hIncoming : VisitReferenceIncomingWallCoverPosExc i d s X)
    (hOuter : VisitReferenceHeightCoverOuterPosExc i d side0 s X)
    (hExposed : VisitReferenceHeightCoverPosExc i d side0 s
      (fun j q ω => X j q ω ∪ ((j.target i d).domain ω)ᶜ)) :
    VisitReferenceHeightCoverPosExcS i d sideS s X := by
  intro j hj target zL zR q hq gB hgB
  have hOwn := ae_reference_incoming_own_heights_of_initialS hj hTransport hTranslate hu hh hCoupling hu' hKilled
    hLife (hCont j hj) (hStart j hj) (hMeas j hj) (hDetermined j hj) (hLocal j hj) (sideS j) hHarm (s j) (hG j hj)
    hgB (hInitial j hj)
  filter_upwards [hOwn, hIncoming j hj q hq, hExposed j hj q hq gB hgB, hOuter j hj q hq gB hgB]
    with ω hOwnω hIncomingω hExposedω hOuterω hω hLive current ξ hξ hX
  have hph := hphase j q ω
  by_cases hInside : extendFrom H current.2.1 (ξ : ℂ) ∈ target.domain ω
  · obtain ⟨r, x, ε, b, h1, h2, h3, h4, h5, h6, hb⟩ :=
      hExposedω hω hLive ξ hξ (fun h => h.elim hX (fun h => h hInside))
    have hξI := mem_seed_interval_of_domain_landing hj hRc (hLc j.seed) hω hLive hInside
    refine ⟨r, x, ε, b, h1, h2, h3, h4, h5, h6, ?_⟩
    rw [hb]
    simp only [target, zL, zR, Set.indicator_of_mem hξI, Pi.one_apply, mul_one]
    linarith
  · by_cases hSeed : ξ ∈ Ioo (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
                  (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
            (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
                  (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
    · obtain ⟨r, x, ε, b, h1, h2, h3, h4, h5, h6, hb⟩ := hOuterω hω hLive ξ hξ hX hSeed hInside
      refine ⟨r, x, ε, b, h1, h2, h3, h4, h5, h6, ?_⟩
      rw [hb]
      simp only [target, zL, zR, Set.indicator_of_mem hSeed, Pi.one_apply, mul_one]
      linarith
    obtain ⟨r, W, q', x, a, hVisit, hOrder, hW, hW0, hqq', hEq, ha, haξ, hx, hx₀, hxB⟩ :=
      hIncomingω hω hLive ξ hξ hX hSeed
    have hOwnHeight := hOwnω hω r hVisit q hOrder W hW hW0 q' hqq' hEq x a ha hx hx₀ hxB
    obtain ⟨ε, hε, hCollar, hTransition, -, hWord⟩ :=
      reference_incoming_geometry_and_word hj hRc (hLc j.seed) (sideS j ω) hω (s j r) q hOrder
        hW hW0 hqq' hEq ha hx hxB (by simpa only [haξ, SideTarget.jumps] using hξ)
    rw [haξ] at hTransition hWord
    exact ⟨r, _, ε, _, hVisit, hOrder, hε, hCollar, hTransition, hOwnHeight, hWord⟩

/-- **The late positive cover in R100's relifted chart** (`X = colCovExc`, finite): every reference chart relifted by
`−2π m` (R100: `m = 1 − n`), from the relifted initial mean formula of every test (the base chart's lift replaced by
the relifted one; SIDE-COLLAR2's `initialMeanFormula_zeroFrame_of_ready` with offset `0`), the seed-interval landings,
and the phase condition in the relifted frame: `phase = χ·2π (lateCurPhaseInt − m) + offset`. -/
theorem visitReferenceHeightCoverPosExcShift_colCov (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω) (m : SideTest Ω → Ω → ℤ)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ j : SideTest Ω, j.Ready d → ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ j : SideTest Ω, j.Ready d → ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j : SideTest Ω, j.Ready d → ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t) (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t)
    (hHarm : EqOn d.harmonic d.coupledMean H) (hxL₀ : ∀ a, d.xL a ≤ 0) (hxR₀ : ∀ b, 0 ≤ d.xR b)
    (hG : ∀ j : SideTest Ω, j.Ready d →
      IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure (G j))
    (hGform : ∀ j : SideTest Ω, j.Ready d → ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event →
      ∀ z ∈ (j.target i d).domain ω,
        harmRep (G j ω) (H \ j.capacityReference i d 0 ω) z + (j.target i d).harmonic z +
          chiC (j.target i d).kappa * (PocketStopField.shiftChart ((j.target i d).baseChart ω) (m j ω)).2.2 z =
          j.initialWordExtension i d ω (((j.target i d).baseChart ω).1 z) - (side j).offset)
    (hSeed : LateSeedLand i d)
    (hside : ∀ j q ω, (side j).phase q ω =
      chiC i.kappa * (2 * Real.pi * ((lateCurPhaseInt i d j q ω : ℝ) - (m j ω : ℝ))) + (side j).offset) :
    VisitReferenceHeightCoverPosExcShift i d side m (fun _ => rationalOriginalTime) (colCovExc d) := by
  let sideS : SideTest Ω → Ω → Late.SideData Ω := fun j ω => { side j with
    offset := (side j).offset - chiC (j.target i d).kappa * (2 * Real.pi * m j ω) }
  let side0 : SideTest Ω → Late.SideData Ω := fun j =>
    withLiftPhase { side j with offset := 0 } i.kappa (lateCurPhaseInt i d j)
  have hk : ∀ j : SideTest Ω, chiC (j.target i d).kappa = chiC i.kappa := fun j => by
    rw [Late.target_kappa]
    have := i.kappa_gt_four
    congr 1
    field_simp
  have hside0 : ∀ j q ω, (side0 j).phase q ω =
      chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j q ω) + (side0 j).offset := fun _ _ _ => rfl
  have hphase : ∀ j q ω, (sideS j ω).phase q ω - (sideS j ω).offset = (side0 j).phase q ω - (side0 j).offset := by
    intro j q ω
    show (side j).phase q ω - ((side j).offset - chiC (j.target i d).kappa * (2 * Real.pi * m j ω)) =
      (chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j q ω) + 0) - 0
    rw [hside j q ω, hk j]
    ring
  have hInitial : ∀ j : SideTest Ω, j.Ready d → ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ x : ℝ,
      x ∉ (j.target i d).jumps 0 ω →
      Tendsto (sideMean (j.target i d).kappa ((j.target i d).baseChart ω) (j.target i d).harmonic
        (harmRep (G j ω) (H \ j.capacityReference i d 0 ω))) (𝓝[H] (x : ℂ))
        (𝓝 (j.nativeSideWord i d (sideS j ω) 0 ω x)) := by
    intro j hj
    refine ae_initialHeights_of_meanFormula_testS hj (sideS j) hKilled hRc (hLc j.seed) hRm (hLm j.seed) hCoupling
      (hG j hj) ?_
    filter_upwards [hGform j hj] with ω hω hE z hz
    have h := hω hE z hz
    dsimp only [PocketStopField.shiftChart] at h
    show _ = _ - ((side j).offset - chiC (j.target i d).kappa * (2 * Real.pi * m j ω))
    linarith
  have hpath := hCoupling.1.2.2.2.2
  have hGeom := lateLiftCurGeom_of_seedLand hRc hLc hSeed
  have hRefl := lateOuterRefl_colCovExc (i := i) (d := d) hRc hLc
  have hOuterGeom := lateOuterLiftGeom_of_seedLand _ hRc hLc hCoupling hLife hSeed hRefl
  have hOuter := visitReferenceHeightCoverOuterPosExc_of_liftWord i d side0 (colCovExc d) hTransport hTranslate hu
    hh hCoupling hu' hKilled hLife hCont hStart hMeas hDetermined hLocal hRc hLc hHarm (fun _ _ _ => subset_rfl)
    (lateOuterLiftWord_of_curInt i d _ hRc hLc hpath hxL₀ hxR₀ hGeom hOuterGeom side0 hside0)
  have hHull := visitReferenceAmbientCoverPosExcHull_of_liftWord i d side0 (colCovExc d) hRc hLc hCoupling
    (lateAmbientLiftWord_of_curInt i d _ hRc hLc hpath hxL₀ hxR₀ hGeom side0 hside0)
  have hExp := visitReferenceAmbientCoverPosExc_of_hull i d side0 (fun _ => rationalOriginalTime)
    (X := colCovExc d) (fun _ _ _ => union_subset subset_union_left subset_rfl) hHull
  have hExposed := visitReferenceHeightCoverPosExc_of_ambient i d side0 _ _ hTransport hTranslate hu hh hCoupling
    hu' hKilled hLife hCont hStart hMeas hDetermined hLocal hHarm hExp
  exact visitReferenceHeightCoverPosExcShift_of_S i d side m _ _
    (visitReferenceHeightCoverPosExcS_of_split i d sideS side0 G _ _ hTransport hTranslate hu hh hCoupling hu'
      hKilled hLife hCont hStart hMeas hDetermined hLocal hRc hLc hHarm hG hInitial hphase
      (visitReferenceIncomingWallCoverPosExc_rational i d _) hOuter hExposed)

end InteractingSLE.Sec7.ColCov
