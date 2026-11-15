/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmMean
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71
import InteractingSLE.Spec.Sec2.MartingaleFinalImage

/-!
# GW2's open lines: the instance's typed bounded harmonic extension in the flowed form

Packet PROVE-GW2-STAGEMEAN, R121 round. For ROOTX's root-`x` instance objects, at a sample whose stage driver is
continuous and starts at `0`:

* **`bhe_bheProc_typedX`**: the instance's `bheProc` at stage time `s` is the bounded harmonic extension of the typed
  force data with the marks flowed by `rightImg` along the stage driver (the reader `Q3Stop.canonDrv` of `relVar`
  IS the stage driver, `GB6.RelDrv.relDrv_relVar`);
* **`bhe_bheProc_typedX_zero`**: at stage time `0`, of the typed force data itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.Q3Stop GW2Sde GW2Rz GW2TipSystem GW2TipSystem.RootC24 GW2Rd Supp8.GB6.RelDrv MartChar.RealFlow

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **The instance's typed bounded harmonic extension in the flowed form.** -/
theorem bhe_bheProc_typedX (I : StageInst Ω) (x₀ : ℝ) (w : WordType) (ω : Ω)
    (hc : Continuous fun t => I.drvX c x₀ t ω) (h0 : I.drvX c x₀ 0 ω = 0) (s : ℝ≥0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData c.κ (typedRhoL w) (typedRhoR w)
        (fun i => -rightImg (fun q => -(fun q : ℝ => I.drvX c x₀ q.toNNReal ω) q)
            (-typedXL c.κ w (I.β (I.srecX c r l x₀ ω)) i) s - (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) s)
        (fun j => rightImg (fun q : ℝ => I.drvX c x₀ q.toNNReal ω)
            (typedXR c.κ w (I.β (I.srecX c r l x₀ ω)) j) s - (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) s))
      (forceJumpSet
        (fun i => -rightImg (fun q => -(fun q : ℝ => I.drvX c x₀ q.toNNReal ω) q)
            (-typedXL c.κ w (I.β (I.srecX c r l x₀ ω)) i) s - (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) s)
        (fun j => rightImg (fun q : ℝ => I.drvX c x₀ q.toNNReal ω)
            (typedXR c.κ w (I.β (I.srecX c r l x₀ ω)) j) s - (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) s))
      (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c x₀)
        (fun i t ω => geomLW Supp8.Q3Stop.canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
          (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))
        (fun j t ω => geomRW Supp8.Q3Stop.canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
          (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω)) ω s) := by
  have hread : ∀ q : ℝ≥0, Supp8.Q3Stop.canonDrv q (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω) =
      I.drvX c x₀ q ω := fun q => relDrv_relVar hc h0 q
  have h := isBoundedHarmonicExtension_bheProc (κ := c.κ) (ρL := typedRhoL w) (ρR := typedRhoR w)
    (W := I.drvX c x₀)
    (VL := fun i t ω => geomLW Supp8.Q3Stop.canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
      (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))
    (VR := fun j t ω => geomRW Supp8.Q3Stop.canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
      (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω)) ω s
  have eL : (fun i => geomLW Supp8.Q3Stop.canonDrv (fun y => typedXL c.κ w (I.β y.1)) i s
      (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω) - I.drvX c x₀ s ω) =
      fun i => -rightImg (fun q => -(fun q : ℝ => I.drvX c x₀ q.toNNReal ω) q)
        (-typedXL c.κ w (I.β (I.srecX c r l x₀ ω)) i) s - (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) s := by
    funext i
    have hrp : Bessel.realPath (fun t ω' => -Supp8.Q3Stop.canonDrv t ω')
        (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω) =
        fun q => -(fun q : ℝ => I.drvX c x₀ q.toNNReal ω) q :=
      funext fun q => by
        show -Supp8.Q3Stop.canonDrv q.toNNReal (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω) = _
        rw [hread]
    simp only [geomLW]
    rw [hrp]
    simp only [Real.toNNReal_coe]
  have eR : (fun j => geomRW Supp8.Q3Stop.canonDrv (fun y => typedXR c.κ w (I.β y.1)) j s
      (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω) - I.drvX c x₀ s ω) =
      fun j => rightImg (fun q : ℝ => I.drvX c x₀ q.toNNReal ω)
        (typedXR c.κ w (I.β (I.srecX c r l x₀ ω)) j) s - (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) s := by
    funext j
    have hrp : Bessel.realPath Supp8.Q3Stop.canonDrv
        (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω) =
        fun q : ℝ => I.drvX c x₀ q.toNNReal ω :=
      funext fun q => by
        show Supp8.Q3Stop.canonDrv q.toNNReal (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω) = _
        rw [hread]
    simp only [geomRW]
    rw [hrp]
    simp only [Real.toNNReal_coe]
  rw [eL, eR] at h
  exact h

/-- **At stage time `0`, the instance's typed bounded harmonic extension is that of the typed force data.** -/
theorem bhe_bheProc_typedX_zero (I : StageInst Ω) (x₀ : ℝ) (w : WordType) (ω : Ω)
    (hc : Continuous fun t => I.drvX c x₀ t ω) (h0 : I.drvX c x₀ 0 ω = 0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData c.κ (typedRhoL w) (typedRhoR w) (typedXL c.κ w (I.β (I.srecX c r l x₀ ω)))
        (typedXR c.κ w (I.β (I.srecX c r l x₀ ω))))
      (forceJumpSet (typedXL c.κ w (I.β (I.srecX c r l x₀ ω))) (typedXR c.κ w (I.β (I.srecX c r l x₀ ω))))
      (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c x₀)
        (fun i t ω => geomLW Supp8.Q3Stop.canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
          (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))
        (fun j t ω => geomRW Supp8.Q3Stop.canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
          (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω)) ω 0) := by
  have h := bhe_bheProc_typedX (r := r) (l := l) I x₀ w ω hc h0 0
  have hS : Continuous fun q : ℝ => I.drvX c x₀ q.toNNReal ω := hc.comp continuous_real_toNNReal
  have hS0 : (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) 0 = 0 := by simp [h0]
  have eL : (fun i => -rightImg (fun q => -(fun q : ℝ => I.drvX c x₀ q.toNNReal ω) q)
      (-typedXL c.κ w (I.β (I.srecX c r l x₀ ω)) i) ((0 : ℝ≥0) : ℝ) -
        (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) ((0 : ℝ≥0) : ℝ)) =
      typedXL c.κ w (I.β (I.srecX c r l x₀ ω)) := by
    funext i
    have hS' : Continuous fun q : ℝ => -I.drvX c x₀ q.toNNReal ω := hS.neg
    have hS0' : (fun q : ℝ => -I.drvX c x₀ q.toNNReal ω) 0 = 0 := by simp [h0]
    show -rightImg (fun q : ℝ => -I.drvX c x₀ q.toNNReal ω) (-typedXL c.κ w (I.β (I.srecX c r l x₀ ω)) i)
        ((0 : ℝ≥0) : ℝ) - I.drvX c x₀ ((0 : ℝ≥0) : ℝ).toNNReal ω = _
    rw [NNReal.coe_zero, rightImg_zero hS' hS0' (neg_nonneg.2 (typedXL_nonpos c.κ w _ i)), Real.toNNReal_zero, h0]
    ring
  have eR : (fun j => rightImg (fun q : ℝ => I.drvX c x₀ q.toNNReal ω)
      (typedXR c.κ w (I.β (I.srecX c r l x₀ ω)) j) ((0 : ℝ≥0) : ℝ) -
        (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) ((0 : ℝ≥0) : ℝ)) =
      typedXR c.κ w (I.β (I.srecX c r l x₀ ω)) := by
    funext j
    show rightImg (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) (typedXR c.κ w (I.β (I.srecX c r l x₀ ω)) j)
        ((0 : ℝ≥0) : ℝ) - I.drvX c x₀ ((0 : ℝ≥0) : ℝ).toNNReal ω = _
    rw [NNReal.coe_zero, rightImg_zero hS hS0 (typedXR_nonneg c.κ w _ j), Real.toNNReal_zero, h0, sub_zero]
  rw [eL, eR] at h
  exact h

end InteractingSLE.Theorem14.GW2Psm
