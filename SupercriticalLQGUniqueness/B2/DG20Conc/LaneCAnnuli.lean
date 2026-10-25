import SupercriticalLQGUniqueness.B2.DG20Conc.LaneAInputs

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 
def laneCUnitBlock : Set ℂ := (rectAB 1 1).toSet

 
def laneCUnitNeighborhood : Set ℂ := thickening 1 laneCUnitBlock

 
def laneCPrimeCross : Set ℂ := closure (laneCUnitNeighborhood \ laneCUnitBlock)

 
def laneCPrimeAround : Set ℂ := laneCUnitNeighborhood \ laneCUnitBlock

 
def laneCPrimeInner : Set ℂ := frontier laneCUnitBlock
def laneCPrimeOuter : Set ℂ := frontier laneCUnitNeighborhood

 
def laneCInnerCluster : Set ℂ := Icc (-1 : ℝ) 2 ×ℂ Icc (-1 : ℝ) 2

 
def laneCOuterCluster : Set ℂ := Icc (-2 : ℝ) 3 ×ℂ Icc (-2 : ℝ) 3

 
def laneCDoublePrimeCross : Set ℂ :=
  laneCOuterCluster \ interior laneCInnerCluster

 
def laneCDoublePrimeAround : Set ℂ :=
  interior laneCOuterCluster \ laneCInnerCluster

 
def laneCDoublePrimeInner : Set ℂ := frontier laneCInnerCluster
def laneCDoublePrimeOuter : Set ℂ := frontier laneCOuterCluster

 
def laneCDoublePrimeSquares : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2)).filter
    (fun b => b.1 = -2 ∨ b.1 = 2 ∨ b.2 = -2 ∨ b.2 = 2)

theorem laneCDoublePrimeSquares_card : laneCDoublePrimeSquares.card = 16 := by
  decide

 
def laneCUnitUcross : Bool → Set ℂ
  | false => laneCPrimeCross
  | true => laneCDoublePrimeCross

def laneCUnitUaround : Bool → Set ℂ
  | false => laneCPrimeAround
  | true => laneCDoublePrimeAround

def laneCUnitInner : Bool → Set ℂ
  | false => laneCPrimeInner
  | true => laneCDoublePrimeInner

def laneCUnitOuter : Bool → Set ℂ
  | false => laneCPrimeOuter
  | true => laneCDoublePrimeOuter

 
theorem laneC_unit_around_subset_cross (i : Bool) :
    laneCUnitUaround i ⊆ laneCUnitUcross i := by
  cases i
  · intro x hx
    exact subset_closure hx
  · intro x hx
    exact ⟨interior_subset hx.1, fun hi => hx.2 (interior_subset hi)⟩

 
theorem laneC_unit_around_isOpen (i : Bool) : IsOpen (laneCUnitUaround i) := by
  cases i
  · exact isOpen_thickening.sdiff (rectAB 1 1).isCompact_toSet.isClosed
  · exact isOpen_interior.sdiff (isClosed_Icc.reProdIm isClosed_Icc)

end SupercriticalLQGUniqueness.B2.DG20Conc
