/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GateBridgeFace

/-!
# Fresh-start separation for a selected face

PROVE-R7-GAPEQ. Adapt the landed fresh-start gate argument to a selected face with possible
forbidden outer bulges. Face confinement and image inclusion replace the contained-pocket
global equivalence; no assertion about unvisited outer suffixes is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GateBridge

open Sec6

/-- The fresh-start gate theorem needs only the selected face's inclusion and confinement.
One gate is the current driver; the other may represent a different old access. -/
theorem ownFuture_gap_eq_of_face_of_gate {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {C : Set ℂ} (hC : IsOpen C) {q₁ q₂ : ℝ} {z : ℂ} {a₁ a₂ a₃ : ℝ → ℂ} (hq : q₁ < q₂)
    (ha₁ : ContinuousOn a₁ (Icc 0 1)) (ha₂ : ContinuousOn a₂ (Icc 0 1))
    (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1)) (ha₁0 : a₁ 0 = q₁)
    (ha₂0 : a₂ 0 = q₂) (ha₁1 : a₁ 1 = z) (ha₂1 : a₂ 1 = z)
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (h12 : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {z})
    (ha₃ : ContinuousOn a₃ (Ici 0)) (ha₃i : InjOn a₃ (Ici 0)) (ha₃0 : a₃ 0 = z)
    (ha₃H : ∀ t ∈ Ici (0 : ℝ), a₃ t ∈ H) (ha₃t : Tendsto (fun t => ‖a₃ t‖) atTop atTop)
    (h13 : a₁ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {z}) (h23 : a₂ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {z})
    {s a b : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hab : a < b)
    (h11 : ∀ t, a ≤ t → η t ∈ C → trMap W a t 0 ∈ H →
      trMap W a t 0 ∈ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂))
    (hFC : trMap W 0 a '' innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) ⊆ C)
    (hgate : q₁ = 0 ∨ q₂ = 0) (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (htree : ∀ t ∈ Icc a b, trMap W a t 0 ∉ a₁ '' Ioc 0 1 ∪ a₂ '' Ioc 0 1 ∪ a₃ '' Ici 0)
    (hb : b ∈ closure {t | a < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have ha0 := hs.trans hsa
  have hδF : ∀ t ∈ Icc a b,
      trMap W a t 0 ∉ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) := by
    intro t ht hF
    have hc := hFC ⟨_, hF, rfl⟩
    rw [traceMapOut_trMap_zero hη hW hW0 ha0 ht.1] at hc
    exact hgap t ht hc
  have hδa : trMap W a a 0 = 0 := YuanSimpleApprox.trMap_self hW a zero_mem_Hbar
  have heq := gate_lemma_of_gate hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H ha₂H h12
    ha₃ ha₃i ha₃0 ha₃H ha₃t h13 h23 hab
    ((YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 ha0).mono fun _ ht => ht.1)
    (fun _ ht => YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 ha0 ht.1) hδF
    (fun t ht h => htree t ht (Or.inl (Or.inl h)))
    (fun t ht h => htree t ht (Or.inl (Or.inr h))) (fun t ht h => htree t ht (Or.inr h))
    (fun c d hac hcd _ => ownFuture_not_forall_real hη hW hW0 ha0 hac hcd)
    (by rw [hδa]; rcases hgate with h | h
        · left; rw [h, ofReal_zero]
        · right; rw [h, ofReal_zero])
    (ownFuture_mem_closure_face hη hW hW0 hC ha0 h11 hb)
  exact ownFuture_and_trace_eq hη hW hW0 hs hsa le_rfl hab.le heq

/-- The equal fresh gates require only the right endpoint's face closure and open-arm
avoidance. This is the degenerate real-segment case of the same selected-face argument. -/
theorem ownFuture_gap_eq_of_face_eq_of_gate {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {C : Set ℂ} (hC : IsOpen C) {a₁ a₂ : ℝ → ℂ}
    (hJc : IsClosed (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1)) (ha₁0 : a₁ 0 = (0 : ℝ))
    (ha₂0 : a₂ 0 = (0 : ℝ)) {s a b : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hab : a ≤ b)
    (h11 : ∀ t, a ≤ t → η t ∈ C → trMap W a t 0 ∈ H →
      trMap W a t 0 ∈ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1))
    (hFC : trMap W 0 a '' innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1) ⊆ C)
    (hgapb : η b ∉ C)
    (htree : trMap W a b 0 ∉ a₁ '' Ioc 0 1 ∪ a₂ '' Ioc 0 1)
    (hb : b ∈ closure {t | a < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have ha0 := hs.trans hsa
  have hFb : trMap W a b 0 ∉ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1) := by
    intro hF
    have hc := hFC ⟨_, hF, rfl⟩
    rw [traceMapOut_trMap_zero hη hW hW0 ha0 hab] at hc
    exact hgapb hc
  have hcl := ownFuture_mem_closure_face hη hW hW0 hC ha0 h11 hb
  have h := gate_lemma_eq (δ := fun _ : ℝ => trMap W a b 0) (a := b) (b := b) rfl hJc ha₁0 ha₂0
    hFb hFb (fun _ _ h => htree (Or.inl h)) (fun _ _ h => htree (Or.inr h)) hcl hcl
  have hδa : trMap W a a 0 = ((0 : ℝ) : ℂ) := by
    rw [ofReal_zero]; exact YuanSimpleApprox.trMap_self hW a zero_mem_Hbar
  exact ownFuture_and_trace_eq hη hW hW0 hs hsa le_rfl hab (hδa.trans h.1.symm)

end InteractingSLE.Sec7.R7GateBridge
