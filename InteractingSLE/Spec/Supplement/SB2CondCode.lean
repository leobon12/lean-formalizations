/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowCodeMain

/-!
# The canonical driver code in every universe (determination and realization)

Packet PROVE-T14-SB2COND. Lemma SB2's conditional identifications (supplement pp. 630–633) are stated with the carrier
`SB.IsCondFlowLineDriverOn` on a probability space `Ω : Type u`. The landed canonical driver code
(`Restart.isCanonicalDriverCode_driverCode`, PROVE-CONDDET) is proved at universe `0` only, because the predicate
`Restart.IsCanonicalDriverCode` quantifies over spaces in `Type`. Its two halves only use universe-polymorphic inputs
(`Exist.Staged.ae_detCode_eq` and `Restart.isOptionalHullCoupling_of_detAgree`), so they hold verbatim for the code
`Restart.driverCode h12p hκ θ` built from Theorem 1.2's parametric form at universe `u`:

* **`ae_driverCodeMatch_of_isFlowLineDriver_univ`** (determination): every driver of a flow line from `0`, on any
  probability space of `Type u`, matches the code almost surely;
* **`isFlowLineDriver_of_driverCodeMatch_univ`** (realization): a measurable driver, continuous before its measurable
  lifetime, which matches the code almost surely, drives the flow line.

The proofs are those of `Restart.ae_driverCodeMatch_of_isFlowLineDriver` and
`Restart.isFlowLineDriver_of_driverCodeMatch` (`Spec/Restart/FlowCodeMain.lean`) with the universe generalized.

**R48.** These lemmas take Theorems 1.2–1.3 as hypotheses; they serve Theorem 1.4 (and 1.5) only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Cond

open LQGMetric Sec2.Assembly Exist.Staged Restart

section Driver

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)

/-- **Determination in universe `u`**: every driver of a flow line from `0` matches the canonical driver code almost
surely (`Restart.ae_driverCodeMatch_of_isFlowLineDriver` for spaces in `Type u`). -/
theorem ae_driverCodeMatch_of_isFlowLineDriver_univ (h13 : Exist.Theorem13Statement.{u}) (c : BoundaryWord)
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ Q h W L) :
    ∀ᵐ ω ∂Q, IsDriverCodeMatch (driverCode h12p hκ θ (c, h ω)) (fun t => W t ω) (L ω) := by
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := hfl
  have hh' : h' = fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)
  subst hh'
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hdet := ae_detCode_eq hκ hF h13 hC ((h12p κ hκ _ _).choose_spec.2 _ _ _ _ hF hC)
  filter_upwards [hdet, hC.1.2.2.2.2] with ω ⟨x₀, hx₀, hζx, hwx, hcode⟩ hpath
  have hD : driverOf h12p hκ θ (c, h ω) = (drvPath (dOf x₀), cζ x₀) := by
    rw [driverOf_mk]
    have hcode' : detCode (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
        (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
          (flowLineRhoL κ c.fn c.jumps 0 θ, flowLineRhoR κ c.fn c.jumps 0 θ)),
          Exist.flowField 0 (θ * QuantumZipper.chiC κ) (h ω)) = dOf x₀ := hcode
    rw [hcode', drvOf_of_mem (dOf_mem_DSet hx₀)]
    rfl
  refine ⟨?_, ?_, fun n k hnk => ?_⟩
  · change L ω = (driverOf h12p hκ θ (c, h ω)).2
    rw [hD]
    exact hζx.symm
  · change W 0 ω = (driverOf h12p hκ θ (c, h ω)).1 (dyad 0 0)
    rw [Exist.dyad_zero_zero, driverOf_mk, (drvOf_regular _).2.1]
    exact hpath.1
  · change W (dyad n k) ω = (driverOf h12p hκ θ (c, h ω)).1 (dyad n k)
    rw [hD]
    have hlt : ((dyad n k : ℝ≥0) : ℝ≥0∞) < cζ x₀ := hζx ▸ hnk
    exact ((hwx _ hnk).1.symm).trans ((drvPath_dOf_agree x₀).2 _ hlt).symm

/-- **Realization in universe `u`**: a measurable driver, continuous before its measurable lifetime, that matches the
canonical driver code almost surely drives the flow line from `0` (`Restart.isFlowLineDriver_of_driverCodeMatch` for
spaces in `Type u`). -/
theorem isFlowLineDriver_of_driverCodeMatch_univ (h13 : Exist.Theorem13Statement.{u}) (c : BoundaryWord)
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}
    (hgff : IsGFFWithBoundaryData Q h c.fn c.jumps) (hWm : ∀ t, Measurable (W t)) (hLm : Measurable L)
    (hWc : ∀ ω, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < L ω})
    (hmatch : ∀ᵐ ω ∂Q, IsDriverCodeMatch (driverCode h12p hκ θ (c, h ω)) (fun t => W t ω) (L ω)) :
    IsFlowLineDriver κ c.fn c.jumps θ Q h W L := by
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hh' := Exist.isGFFWithBoundaryData_flowField hκ c.isPiecewiseConstantBoundaryData 0 θ hgff
  have hag : ∀ᵐ ω ∂Q, L ω = (driverOf h12p hκ θ (c, h ω)).2 ∧ W 0 ω = (driverOf h12p hκ θ (c, h ω)).1 0 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → W t ω = (driverOf h12p hκ θ (c, h ω)).1 t := by
    filter_upwards [hmatch] with ω ⟨hL, h0, hd⟩
    have hL' : L ω = (driverOf h12p hκ θ (c, h ω)).2 := hL
    refine ⟨hL', ?_, fun t ht => ?_⟩
    · have h0' : W 0 ω = (driverOf h12p hκ θ (c, h ω)).1 (dyad 0 0) := h0
      rwa [Exist.dyad_zero_zero] at h0'
    · have hreg := (drvOf_regular (detCode
        (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
          (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
            (flowLineRhoL κ c.fn c.jumps 0 θ, flowLineRhoR κ c.fn c.jumps 0 θ)),
            Exist.flowField 0 (θ * QuantumZipper.chiC κ) (h ω)))).1
      rw [← driverOf_mk, ← hL'] at hreg
      exact eq_of_eq_dyad_lt (hWc ω) hreg (fun n k hnk => hd n k hnk) ht
  simp only [driverOf_mk] at hag
  obtain ⟨𝓕, VL, VR, B, hC⟩ := isOptionalHullCoupling_of_detAgree h12p h13 hκ hF hh' hWm hLm hag
  exact ⟨_, 𝓕, VL, VR, B, fun ω => Exist.isTranslateAddConst_flowField 0 _ (h ω), hC⟩

end Driver

end InteractingSLE.Theorem14.SB.Cond
