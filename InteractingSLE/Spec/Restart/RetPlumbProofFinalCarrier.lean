/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalTrace

/-!
# Standard Borel compression of retained model coordinates

Packet PROVE-RETPLUMB. The word, field, driver, lifetime and closed trace on an
arbitrary source space admit one concrete measurable reader into a standard
Borel carrier in `Type`. This supplies coordinate and law transport; it does
not assert the remaining filtration-dependent stochastic laws on that carrier.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open LQGMetric (DistOn)
open Sec2.Assembly

/-- The six observable coordinates needed by the stopped model. -/
abbrev RetCanonSpace : Type :=
  BoundaryWord × DistOn upperHalfPlaneOpens × PCode × ℝ≥0∞ × PCode × PCode

instance : StandardBorelSpace (ℝ≥0∞ × PCode × PCode) := StandardBorelSpace.prod
instance : StandardBorelSpace (PCode × ℝ≥0∞ × PCode × PCode) := StandardBorelSpace.prod
instance : StandardBorelSpace (DistOn upperHalfPlaneOpens × PCode × ℝ≥0∞ × PCode × PCode) :=
  StandardBorelSpace.prod
instance : StandardBorelSpace RetCanonSpace := StandardBorelSpace.prod

namespace RetCanonSpace
def word (s : RetCanonSpace) : BoundaryWord := s.1
def field (s : RetCanonSpace) : DistOn upperHalfPlaneOpens := s.2.1
def driver (t : ℝ≥0) (s : RetCanonSpace) : ℝ := FCDet.decDrv s.2.2.1 t
def life (s : RetCanonSpace) : ℝ≥0∞ := s.2.2.2.1
def trace (s : RetCanonSpace) (t : ℝ≥0) : ℂ :=
  ⟨FCDet.decDrv s.2.2.2.2.1 t, FCDet.decDrv s.2.2.2.2.2 t⟩

theorem measurable_word : Measurable word := measurable_fst
theorem measurable_field : Measurable field := measurable_fst.comp measurable_snd
theorem measurable_driver (t : ℝ≥0) : Measurable (driver t) :=
  (FCDet.measurable_decDrv t).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
theorem measurable_life : Measurable life :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
theorem continuous_driver (s : RetCanonSpace) : Continuous (driver · s) := FCDet.continuous_decDrv _
theorem driver_zero (s : RetCanonSpace) : driver 0 s = 0 := FCDet.decDrv_zero _
theorem measurable_trace (t : ℝ≥0) : Measurable fun s => trace s t := by
  have hR : Measurable fun s : RetCanonSpace => FCDet.decDrv s.2.2.2.2.1 t :=
    (FCDet.measurable_decDrv t).comp (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have hI : Measurable fun s : RetCanonSpace => FCDet.decDrv s.2.2.2.2.2 t :=
    (FCDet.measurable_decDrv t).comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  convert (Complex.measurable_ofReal.comp hR).add
    ((Complex.measurable_ofReal.comp hI).mul_const Complex.I) using 1
  funext s
  apply Complex.ext <;> simp [trace]
theorem continuous_trace (s : RetCanonSpace) : Continuous (trace s) := by
  convert (Complex.continuous_ofReal.comp (FCDet.continuous_decDrv s.2.2.2.2.1)).add
    ((Complex.continuous_ofReal.comp (FCDet.continuous_decDrv s.2.2.2.2.2)).mul_const Complex.I) using 1
  funext t
  apply Complex.ext <;> simp [trace]
theorem trace_zero (s : RetCanonSpace) : trace s 0 = 0 := by
  simp only [trace, FCDet.decDrv_zero]
  rfl
end RetCanonSpace

universe v
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]

/-- Concrete coordinate compression, including the finite closed trace endpoint.
Only closed-lifetime trace continuity is required on the original source. -/
theorem exists_retCanonicalReader {c : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hc : Measurable c) (hH : Measurable Hc) (hW : ∀ t, Measurable (W t))
    (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    (hV : Measurable V) (hγ : ∀ t, Measurable fun ω => γ ω t)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ V ω})
    (hγ0 : ∀ ω, γ ω 0 = 0) :
    ∃ Y : Ω → RetCanonSpace, Measurable Y ∧ ∀ ω,
      RetCanonSpace.word (Y ω) = c ω ∧ RetCanonSpace.field (Y ω) = Hc ω ∧
        RetCanonSpace.life (Y ω) = V ω ∧
        (∀ t, RetCanonSpace.driver t (Y ω) = W t ω) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → RetCanonSpace.trace (Y ω) t = γ ω t := by
  obtain ⟨hTm, hTc, hTe⟩ := retClosedTrace_data hV hγ hγc hγ0
  let Γ := retClosedTrace V γ
  let Y : Ω → RetCanonSpace := fun ω => (c ω, Hc ω, enc (W · ω), V ω,
    enc (fun t => (Γ ω t).re), enc (fun t => (Γ ω t).im))
  have hY : Measurable Y := hc.prodMk (hH.prodMk
    ((measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => hW (dyad n k)).prodMk
      (hV.prodMk ((measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
        Complex.measurable_re.comp (hTm (dyad n k))).prodMk
          (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
            Complex.measurable_im.comp (hTm (dyad n k)))))))
  refine ⟨Y, hY, fun ω => ⟨rfl, rfl, rfl, ?_, ?_⟩⟩
  · intro t
    exact congrFun (FCDet.decDrv_enc (hWc ω) (hW0 ω)) t
  · intro t ht
    have hΓ0 : retClosedTrace V γ ω 0 = 0 := (hTe ω 0 zero_le).trans (hγ0 ω)
    have hR := congrFun (FCDet.decDrv_enc (Complex.continuous_re.comp (hTc ω))
      (by simp [hΓ0])) t
    have hI := congrFun (FCDet.decDrv_enc (Complex.continuous_im.comp (hTc ω))
      (by simp [hΓ0])) t
    exact (Complex.ext hR hI).trans (hTe ω t ht)

/-- The compressed conditional law is a probability law because the reader is
measurable. It therefore never uses `Measure.map`'s nonmeasurable fallback. -/
theorem isProbabilityMeasure_retCanonicalLaw {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Set Ω} (hPF : P F ≠ 0) {Y : Ω → RetCanonSpace} (hY : Measurable Y) :
    IsProbabilityMeasure ((P[|F]).map Y) := by
  let _ : IsProbabilityMeasure (P[|F]) := cond_isProbabilityMeasure hPF
  exact (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance

end InteractingSLE.Restart.RetAux79
