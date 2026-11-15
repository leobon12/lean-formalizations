/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC10Mean

/-!
# The actual initial incoming angle profiles and their finite word

PROVE-SIDE-COLLAR2. At the inverse boundary coordinate the two possible
left words and the right word have exactly the cumulative CF9.5 weights.
The remote marks select the outer angles `-π/2` and `π/2`; all other
coordinates use the actual RS13.6 angles of the side target.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketMarks Sec7.PocketCoupling

variable {Ω : Type} [MeasurableSpace Ω]

/-- The incoming right-wall angle, read in the flow coordinate. The
right wall's change point occurs only in the two-left-mark shape. -/
def initialFlowAngle₁ (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (ω : Ω) (y : ℝ) : ℝ :=
  if j.twoLeft then
    if -y⁻¹ < marksL2All d.rightWall j.chart ω 1 then -(π / 2)
    else rs136Theta1 (16 / i.kappa) i.leftWeight
  else rs136Theta1 (16 / i.kappa) i.leftWeight

/-- The incoming left-wall angle, read in the flow coordinate. -/
def initialFlowAngle₂ (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (ω : Ω) (y : ℝ) : ℝ :=
  if marksRAll (d.leftWall j.seed) (StripSys.rt j.seed) j.chart ω 1 ≤ -y⁻¹ then π / 2
  else rs136Theta2 (16 / i.kappa) i.rightWeight

/-- Exact cumulative left weights at every negative coordinate, for
both actual native word shapes. This includes the remote angle change. -/
theorem initialFlowAngle₁_cumulative (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (ω : Ω) {x : ℝ} (hx : x < 0) :
    ∑ a ∈ Finset.univ.filter (fun a => x < (j.target i d).marksL ω a), (j.target i d).rhoL a =
      cf95RhoL (16 / i.kappa) (j.initialFlowAngle₁ i d ω (-x⁻¹)) := by
  classical
  rcases j with ⟨seed, outerEvent, event, chart, infinite, twoLeft⟩
  cases twoLeft
  · change (∑ a ∈ Finset.univ.filter (fun _ : Fin 1 => x < 0),
        wordL1 (16 / i.kappa) (rs136Theta1 (16 / i.kappa) i.leftWeight) a) = _
    simp [wordL1, hx, initialFlowAngle₁]
  · let b := marksL2All d.rightWall chart ω 1
    change (∑ a ∈ Finset.univ.filter (fun a : Fin 2 => x < (![0, b] : Fin 2 → ℝ) a),
        wordL2 (16 / i.kappa) (rs136Theta1 (16 / i.kappa) i.leftWeight) a) =
      cf95RhoL (16 / i.kappa)
        (if -(-x⁻¹)⁻¹ < b then -(π / 2) else rs136Theta1 (16 / i.kappa) i.leftWeight)
    simp only [inv_neg, inv_inv, neg_neg, Matrix.cons_val_one,
      Finset.sum_filter, Fin.sum_univ_two, Matrix.cons_val_zero, wordL2, hx, ↓reduceIte]
    by_cases hxb : x < b <;> simp [hxb]

/-- Exact cumulative right weights at every positive coordinate. -/
theorem initialFlowAngle₂_cumulative (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (ω : Ω) {x : ℝ} (hx : 0 < x) :
    ∑ a ∈ Finset.univ.filter (fun a => (j.target i d).marksR ω a ≤ x), (j.target i d).rhoR a =
      cf95RhoR (16 / i.kappa) (j.initialFlowAngle₂ i d ω (-x⁻¹)) := by
  classical
  rcases j with ⟨seed, outerEvent, event, chart, infinite, twoLeft⟩
  cases twoLeft <;>
    change (∑ a ∈ Finset.univ.filter (fun a : Fin 2 =>
        (![0, marksRAll (d.leftWall seed) (StripSys.rt seed) chart ω 1] : Fin 2 → ℝ) a ≤ x),
        wordR2 (16 / i.kappa) (rs136Theta2 (16 / i.kappa) i.rightWeight) a) =
      cf95RhoR (16 / i.kappa)
        (if marksRAll (d.leftWall seed) (StripSys.rt seed) chart ω 1 ≤ -(-x⁻¹)⁻¹ then π / 2
          else rs136Theta2 (16 / i.kappa) i.rightWeight) <;>
    simp only [inv_neg, inv_inv, neg_neg,
      Finset.sum_filter, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      wordR2, hx.le, ↓reduceIte] <;>
    by_cases hbx : marksRAll (d.leftWall seed) (StripSys.rt seed) chart ω 1 ≤ x <;>
      simp [hbx]

end InteractingSLE.Wire.Current.SideTest

namespace InteractingSLE.Wire

open Current Sec7

/-- Remaining initial boundary mathematics: the bounded flow-coordinate
mean has the actual incoming-angle heights. All cumulative-weight
equalities are proved separately, rather than assumed here. -/
def InitialPocketFlowBoundary {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (M : SideTest Ω → Ω → ℂ → ℝ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
    ∀ᵐ ω ∂d.measure, ω ∈ target.event →
      (∀ a, target.marksL ω a ≤ 0) ∧ (∀ a, 0 ≤ target.marksR ω a) ∧
      InnerProductSpace.HarmonicOnNhd (M j ω) H ∧
      (∃ C : ℝ, ∀ z ∈ H, |M j ω z| ≤ C) ∧
      ∀ x : ℝ, x ∉ forceJumpSet (target.marksL ω) (target.marksR ω) →
        Tendsto (M j ω) (𝓝[H] (-((x : ℂ)⁻¹)))
          (𝓝 (cf92Lower (16 / i.kappa) (j.initialFlowAngle₁ i d ω (-x⁻¹))
            (j.initialFlowAngle₂ i d ω (-x⁻¹)) (-x⁻¹)))

/-- The actual finite-word equalities discharge both cumulative-weight
clauses in the generic flow-word normalization input. -/
theorem initialPocketFlowWord_of_boundary {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (M : SideTest Ω → Ω → ℂ → ℝ)
    (h : InitialPocketFlowBoundary i d M) :
    InitialPocketFlowWord i d M (fun j => j.initialFlowAngle₁ i d)
      (fun j => j.initialFlowAngle₂ i d) := by
  intro j hj target
  filter_upwards [h j hj] with ω hω hA
  obtain ⟨hL, hR, hM, hBdd, hHeight⟩ := hω hA
  exact ⟨hL, hR, hM, hBdd, hHeight,
    fun x _ hx => j.initialFlowAngle₁_cumulative i d ω hx,
    fun x _ hx => j.initialFlowAngle₂_cumulative i d ω hx⟩

end InteractingSLE.Wire
