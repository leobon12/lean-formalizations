/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC8Geometry

/-!
# Surviving incoming heights for the literal native force positions

PROVE-SIDE-COLLAR2. Geometric force coordinates only use the driver up
to the current time. Thus the real-flow word theorem applies to the locally
continuous driver of the actual traversal, without assuming global
continuity. The phase may be arbitrary at either reference or current time.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketTraversal

open MartChar.RealFlow

/-- Causality identifies both native force-position families with the
positions of a continuous driver agreeing up to the specified time. -/
theorem geom_positions_eq_of_driver_eqOn {Ω : Type*} {nL nR : ℕ}
    (w : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ)
    {ω : Ω} {q : ℝ≥0} {W : ℝ → ℝ} (hW : Continuous W)
    (hEq : EqOn (fun r : ℝ => w r.toNNReal ω) W (Icc 0 (q : ℝ))) :
    (fun i => geomLW w xL i q ω - w q ω) =
        (fun i => -rightImg (fun r => -W r) (-xL ω i) q - W q) ∧
      (fun j => geomRW w xR j q ω - w q ω) =
        (fun j => rightImg W (xR ω j) q - W q) := by
  have hAt : w q ω = W q := by
    simpa only [Real.toNNReal_coe] using hEq ⟨q.coe_nonneg, le_rfl⟩
  constructor
  · funext i
    change -rightImg (fun r => -w r.toNNReal ω) (-xL ω i) q - w q ω = _
    rw [Lemma71B.rightImg_congr hW.neg q.coe_nonneg
      (fun r hr => congrArg Neg.neg (hEq hr)) _, hAt]
    rfl
  · funext j
    change rightImg (fun r => w r.toNNReal ω) (xR ω j) q - w q ω = _
    rw [Lemma71B.rightImg_congr hW q.coe_nonneg hEq _, hAt]

end InteractingSLE.Sec7.PocketTraversal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketTraversal Sec7.PocketStopSide Sec7.Lemma71C

variable {Ω : Type} [MeasurableSpace Ω]

/-- The exact native boundary value, including its phase-window and offset. -/
def nativeSideWord (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (e : Late.SideData Ω) (q : ℝ≥0) (ω : Ω) (ξ : ℝ) : ℝ :=
  let target := j.target i d
  let vL := fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a q ω -
    segDriver (target.curve ω) q
  let vR := fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a q ω -
    segDriver (target.curve ω) q
  forceBoundaryData target.kappa target.rhoL target.rhoR vL vR ξ +
    e.phase q ω * (Ioo (vL (Late.leftZero i d j))
      (vR (Late.rightZero i d j))).indicator 1 ξ - e.offset

/-- At a surviving incoming real image, the literal native word is the
initial force word minus the common offset, for every supplied phase. -/
theorem nativeSideWord_of_surviving_real (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (e : Late.SideData Ω) {ω : Ω} {q : ℝ≥0} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0)
    (hEq : EqOn (fun r : ℝ => segDriver ((j.target i d).curve ω) r.toNNReal) W
      (Icc 0 (q : ℝ))) {x : ℝ} {a : ℝ → ℂ}
    (ha : QuantumZipper.IsForwardSol W x q a)
    (hx : x ∉ forceJumpSet ((j.target i d).marksL ω) ((j.target i d).marksR ω))
    (hy : (a q).re ∉ (j.target i d).jumps q ω) :
    j.nativeSideWord i d e q ω (a q).re =
      forceBoundaryData (j.target i d).kappa (j.target i d).rhoL (j.target i d).rhoR
        ((j.target i d).marksL ω) ((j.target i d).marksR ω) x - e.offset := by
  have hCoords := geom_positions_eq_of_driver_eqOn
    (fun t ω => segDriver ((j.target i d).curve ω) t)
    (j.target i d).marksL (j.target i d).marksR hW hEq
  rw [SideTarget.jumps, hCoords.1, hCoords.2] at hy
  obtain ⟨hL0, hR0⟩ := target_seed_marks j i d ω
  have hWord := force_word_of_surviving_real (κ := (j.target i d).kappa) hW hW0 q.coe_nonneg ha
    (j.target i d).rhoL (j.target i d).rhoR ((j.target i d).marksL ω)
    ((j.target i d).marksR ω) (Late.leftZero i d j) (Late.rightZero i d j)
    hL0 hR0 hx hy (e.phase q ω)
  unfold nativeSideWord
  dsimp only
  rw [hCoords.1, hCoords.2, congrFun hCoords.1 (Late.leftZero i d j),
    congrFun hCoords.2 (Late.rightZero i d j)]
  exact congrArg (fun b => b - e.offset) hWord

end InteractingSLE.Wire.Current.SideTest
