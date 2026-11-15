/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetCode

/-!
# GW2: stopped determination using the proved regular-stop extension

This is the determination step after constructing the pre-contact relative
coupling. It works at every angle and universe and uses the corrected Aux. 54
(R79), with no unproved extension statement. The construction of that relative
coupling for GW2's general boundary data is a separate obligation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2JDet

open Restart Exist Exist.Staged LawUnique Sec2.Assembly Supp8.GB6 Supp8.GB6.RelDrv

/-- A regular Galmarino-stopped coupling is determined by its unshifted field,
at any angle and in any universe. A measurable continuous version of its driver
agrees with the decoded canonical code before the stop. -/
theorem ae_stopped_driver_eq_drvDec (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12p₀ : Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) {κ θ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) {c : BoundaryWord} (hc : c.IsSorted)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Hc X : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsGFFWithBoundaryData Q Hc c.fn c.jumps)
    (hX : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞}
    (hSC : StoppedExtend.IsStoppedHullCoupling κ
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
      Q 𝓕 W VL VR B e X)
    {R : HistorySpace (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0) → ℝ≥0∞}
    (hRm : Measurable R) (hRG : StoppedExtendWF.IsHistGalmarino R)
    (hRe : ∀ᵐ ω ∂Q, e ω = R (killedHistory W VL VR e ω))
    (hreg : Aux54.IsRegularStop (flowLineRhoL κ c.fn c.jumps 0 θ)
      (flowLineRhoR κ c.fn c.jumps 0 θ) Q W VL VR e)
    {Wb : ℝ≥0 → Ω → ℝ} (hWb : ∀ t, Measurable (Wb t)) (he : Measurable e)
    (hWbc : ∀ ω, ContinuousOn (fun t => Wb t ω) {t | (t : ℝ≥0∞) < e ω})
    (hagb : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω → W t ω = Wb t ω) :
    ∀ᵐ ω ∂Q, IsStopDrvMatch (F (c, Hc ω)) (fun t => Wb t ω) (e ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → Wb t ω = drvDec (F (c, Hc ω)) t := by
  obtain ⟨C, mC, K, hK, 𝓕', W', VL', VR', B', ζ', hC, hag⟩ :=
    Aux54.stoppedHullExtendRStatement.{u} hκ _ _ _ _
      (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0) R hRm hRG
      Q 𝓕 W VL VR B e X hSC hRe hreg
  have hmap : (Q ⊗ₘ K).map Prod.fst = Q := by
    rw [← Measure.fst, Measure.fst_compProd]
  have hGE : IsGFFWithBoundaryData (Q ⊗ₘ K) (fun p => Hc p.1) c.fn c.jumps := by
    refine ⟨hG.1.comp measurable_fst, fun u₀ hu₀ => ?_⟩
    have hz := hG.2 u₀ hu₀
    rw [← hmap] at hz
    exact isZBGFFProcess_comp measurable_fst hz
  have hfl : IsFlowLineDriver κ c.fn c.jumps θ (Q ⊗ₘ K)
      (fun p => Hc p.1) W' ζ' :=
    ⟨fun p => X p.1, 𝓕', VL', VR', B', fun p => hX p.1, hC⟩
  have hfull := ae_flowLineDriver_eq_drvDec_theta h12p h13 h12p₀ h13₀ hκ hF hc hGE hfl
  have hgood := ae_isGoodDrvCode_of_isGFF_theta h12p₀ h13₀ hκ hF hc hG
  have hfst : AEMeasurable (Prod.fst : Ω × C → Ω) (Q ⊗ₘ K) :=
    measurable_fst.aemeasurable
  have hgoodE : ∀ᵐ p ∂(Q ⊗ₘ K), IsGoodDrvCode (F (c, Hc p.1)) :=
    ae_of_ae_map hfst (by rw [hmap]; exact hgood)
  have hagbE : ∀ᵐ p ∂(Q ⊗ₘ K), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e p.1 →
      W t p.1 = Wb t p.1 := ae_of_ae_map hfst (by rw [hmap]; exact hagb)
  have hSm : MeasurableSet
      {ω | IsStopDrvMatch (F (c, Hc ω)) (fun t => Wb t ω) (e ω)} :=
    measurableSet_isStopDrvMatch (hF.1.comp (measurable_const.prodMk hG.1)) hWb he
  have hmatch : ∀ᵐ ω ∂Q, IsStopDrvMatch (F (c, Hc ω)) (fun t => Wb t ω) (e ω) := by
    rw [← hmap]
    refine (ae_map_iff hfst hSm).2 ?_
    filter_upwards [hfull, hag, hagbE, hgoodE] with p hp hagp hbp hgp
    refine ⟨hp.1 ▸ hagp.1, fun n k hnk => ?_⟩
    have hlt : (dyad n k : ℝ≥0∞) < ζ' p := lt_of_lt_of_le hnk hagp.1
    calc
      Wb (dyad n k) p.1 = W (dyad n k) p.1 := (hbp _ hnk.le).symm
      _ = W' (dyad n k) p := ((hagp.2 _ hnk.le hlt).1).symm
      _ = drvDec (F (c, Hc p.1)) (dyad n k) := hp.2 _ hlt
      _ = (F (c, Hc p.1)).1 n k :=
        (isDriverCodeMatch_drvDec hgp).2.2 n k (hp.1 ▸ hlt)
  filter_upwards [hmatch, hgood] with ω hm hg
  exact ⟨hm, fun t ht =>
    (eqOn_drvDec_of_isStopDrvMatch hg (hWbc ω) hm t ht).symm⟩

end InteractingSLE.Theorem14.GW2JDet
