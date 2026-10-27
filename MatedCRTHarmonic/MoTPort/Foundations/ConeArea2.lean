/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import QuantumZipper.Proofs.LQG.AtomlessUncond

/-!
# C.area-exist for the cone field: localization at the singular point `0`

Node C.area-exist for the cone field (the only remaining input of C.meas after
`ConeMeas2.coneRefMeas_of_area`) asks for an a.s. vague limit on all of `ℂ` of the whole-plane
approximations `areaApproxC γ (coneField (lateralPartC X) A Q)`. The cone field is a whole-plane
GFF plus a function that is continuous on `ℂ \ {0}` and has a (random) `α`-log singularity at `0`
(DMS Def. 4.10; `α < Q`). As for QZ's interior log singularities
(QZ `AtomlessUncond` §3b, `isVagueLimitOn_of_local_of_tight`), the vague limit on `ℂ` follows from

* (b1) the vague limit on the punctured plane `ℂ \ {0}` (GFF plus a continuous function, DS
  Prop. 1.1 + the Ding–Gwynne density-change statement as in LM `DG.ae_isVagueLimitOn_muOfMod_loc`),
* (b2) eventual finiteness of the approximations on compacts, and
* (b3) eventual uniform smallness of the approximations near `0` (QZ `tight_of_balls` shape).

This file proves that localization (`isVagueLimitOn_univ_of_punctured`, `coneRefMeas_of_punctured`)
and the quantum-cone existence wrapper `exists_isQuantumCone_of_area` (the existing
`Cone.exists_isQuantumCone` with C.meas discharged by `ConeMeas2.coneRefMeas_of_area`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace MatedCRTHarmonic.MoTPort

namespace ConeArea2

/-- vague limit on `ℂ` from the punctured plane plus finiteness and tightness at `0`
(QZ `AtomlessUncond.isVagueLimitOn_of_local_of_tight` at `z = 0`, `U = ℂ`) -/
theorem isVagueLimitOn_univ_of_punctured {νs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hloc : QuantumZipper.IsVagueLimitOn (univ \ {0}) νs μ)
    (hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, νs k K < ⊤)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop,
      νs k (Metric.ball 0 δ) ≤ ENNReal.ofReal ε) :
    QuantumZipper.IsVagueLimitOn univ νs μ :=
  QuantumZipper.AtomlessUncond.isVagueLimitOn_of_local_of_tight isOpen_univ (mem_univ 0) hloc
    (fun K hK _ => hfin K hK) htight

/-- **C.meas from the three localized inputs (b1)–(b3)** of C.area-exist for the cone field -/
theorem coneRefMeas_of_punctured {γ W : ℝ}
    (harea : ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → Field)
      (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → LQGMetric.IsWholePlaneGFF X P' →
      IsConeProcess (coneAlpha γ W) (QuantumZipper.Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
      ∀ᵐ ω ∂P',
        (∃ μ, QuantumZipper.IsVagueLimitOn (univ \ {0}) (areaApproxC γ
          (coneField (lateralPartC (X ω)) (fun t => A t ω) (QuantumZipper.Qc γ))) μ) ∧
        (∀ K, IsCompact K → ∀ᶠ k in atTop, areaApproxC γ
          (coneField (lateralPartC (X ω)) (fun t => A t ω) (QuantumZipper.Qc γ)) k K < ⊤) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop, areaApproxC γ
          (coneField (lateralPartC (X ω)) (fun t => A t ω) (QuantumZipper.Qc γ)) k
            (Metric.ball 0 δ) ≤ ENNReal.ofReal ε) :
    ConeRefMeas γ W :=
  ConeMeas2.coneRefMeas_of_area fun Ω' _ P' X A hP hX hA hI => by
    filter_upwards [harea Ω' _ P' X A hP hX hA hI] with ω ⟨⟨μ, hμ⟩, hfin, htight⟩
    exact ⟨μ, isVagueLimitOn_univ_of_punctured hμ hfin htight⟩

/-- **quantum cones exist** given C.area-exist for the cone field (the measurability input (a) of
C.meas is proved: `ConeMeas2.aemeasurable_coneField`) -/
theorem exists_isQuantumCone_of_area (γ : ℝ) {W : ℝ} (hW : 0 < W)
    (harea : ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → Field)
      (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → LQGMetric.IsWholePlaneGFF X P' →
      IsConeProcess (coneAlpha γ W) (QuantumZipper.Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
      ∀ᵐ ω ∂P', ∃ μ, QuantumZipper.IsVagueLimitOn univ
        (areaApproxC γ (coneField (lateralPartC (X ω)) (fun t => A t ω) (QuantumZipper.Qc γ))) μ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Y : Ω → Field),
      IsProbabilityMeasure P ∧ IsQuantumCone γ W Y P :=
  Cone.exists_isQuantumCone γ hW (ConeMeas2.coneRefMeas_of_area harea)

end ConeArea2

end MatedCRTHarmonic.MoTPort
