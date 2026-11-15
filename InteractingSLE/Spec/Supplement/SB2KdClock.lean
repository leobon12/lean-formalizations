/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLvStage
import InteractingSLE.Spec.Supplement.SBTail2EraseClock
import Mathlib.Order.Hom.WithTopBot

/-!
# Forward clocks and the lifetime in SB2's remainder link

The forward capacity clock is an order isomorphism after extension beyond a
finite available interval. Its extension to infinity transports the remaining
physical lifetime exactly. The inverse clock then reconstructs the original
stop in `IsRemainderLink`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Lv

/-- The relative lifetime obtained by applying the forward clock to the
physical lifetime remaining after the entrance. -/
def clockLife (e : ℝ≥0 ≃o ℝ≥0) (τ : ℝ≥0) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  e.withTopCongr (ζ - (τ : ℝ≥0∞))

/-- The inverse clock reconstructs exactly the available physical times. -/
theorem lt_clockLife_iff (e : ℝ≥0 ≃o ℝ≥0) (τ s : ℝ≥0) (ζ : ℝ≥0∞) :
    (s : ℝ≥0∞) < clockLife e τ ζ ↔ ((τ + e.symm s : ℝ≥0) : ℝ≥0∞) < ζ := by
  have he : e.withTopCongr ((e.symm s : ℝ≥0) : ℝ≥0∞) = (s : ℝ≥0∞) := by
    change ((e (e.symm s) : ℝ≥0) : ℝ≥0∞) = _
    rw [e.apply_symm_apply]
  rw [clockLife, ← he]
  refine e.withTopCongr.lt_iff_lt.trans ?_
  rw [ENNReal.coe_add]
  exact (ENNReal.cancel_of_ne (ENNReal.coe_ne_top (r := τ))).lt_tsub_iff_left

/-- A clock fixes zero, including when the remaining lifetime vanishes. -/
theorem clockLife_zero (e : ℝ≥0 ≃o ℝ≥0) (τ ζ : ℝ≥0) (hζ : ζ ≤ τ) :
    clockLife e τ ζ = 0 := by
  rw [clockLife, tsub_eq_zero_of_le (ENNReal.coe_le_coe.2 hζ)]
  exact e.withTopCongr.map_bot

/-- An unbounded physical remainder has infinite relative lifetime. -/
theorem clockLife_top (e : ℝ≥0 ≃o ℝ≥0) (τ : ℝ≥0) : clockLife e τ ⊤ = ⊤ := by
  rw [clockLife, ENNReal.top_sub_coe]
  exact e.withTopCongr.map_top

/-- The existing linear extension of a finite clock sends its terminal physical
time to exactly the original clock's terminal relative time. -/
theorem clockLife_prefixClockIso (a : ℝ≥0 → ℝ≥0) (d τ : ℝ≥0)
    (hc : ContinuousOn a (Iic d)) (hm : StrictMonoOn a (Iic d)) (h0 : a 0 = 0) :
    clockLife (Erase.prefixClockIso a d hc hm h0) τ ((τ + d : ℝ≥0) : ℝ≥0∞) =
      (a d : ℝ≥0∞) := by
  rw [clockLife, ENNReal.coe_add, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]
  change ((Erase.prefixClockIso a d hc hm h0 d : ℝ≥0) : ℝ≥0∞) = _
  rw [Erase.prefixClockIso_apply_of_le hc hm h0 le_rfl]

/-- The geometric data of an erased remainder in forward capacity time.
The trace `γ` is centered at the selected relative seed `m`. No conditional
flow-line law or canonical trace occurs in this predicate. -/
def HasForwardRemainderClock (c : Chart) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞)
    (L m : ℝ) (γ : ℝ≥0 → ℂ) (V : ℝ≥0∞) : Prop :=
  firstVisit η ζ L < ζ → ∃ e : ℝ≥0 ≃o ℝ≥0,
    V = clockLife e (firstVisit η ζ L).toNNReal ζ ∧
    ∀ r : ℝ≥0, (((firstVisit η ζ L).toNNReal + r : ℝ≥0) : ℝ≥0∞) < ζ →
      γ (e r) + m ∈ H →
        c.2.1 (γ (e r) + m) = η ((firstVisit η ζ L).toNNReal + r)

/-- A finite continuous strictly increasing geometric clock suffices: reuse
`Erase.prefixClockIso` to extend it, preserving every available time. -/
theorem hasForwardRemainderClock_of_finiteClock
    {c : Chart} {η γ : ℝ≥0 → ℂ} {ζ V : ℝ≥0∞} {L m : ℝ}
    (a : ℝ≥0 → ℝ≥0) (d : ℝ≥0) (hc : ContinuousOn a (Iic d))
    (hm : StrictMonoOn a (Iic d)) (h0 : a 0 = 0)
    (hζ : ζ = (((firstVisit η ζ L).toNNReal + d : ℝ≥0) : ℝ≥0∞))
    (hV : V = (a d : ℝ≥0∞))
    (hlift : ∀ r : ℝ≥0, r < d → γ (a r) + m ∈ H →
      c.2.1 (γ (a r) + m) = η ((firstVisit η ζ L).toNNReal + r)) :
    HasForwardRemainderClock c η ζ L m γ V := by
  intro _
  let e := Erase.prefixClockIso a d hc hm h0
  refine ⟨e, ?_, fun r hr hH => ?_⟩
  · exact hV.trans ((clockLife_prefixClockIso a d
      (firstVisit η ζ L).toNNReal hc hm h0).symm.trans
        (congrArg (clockLife e (firstVisit η ζ L).toNNReal) hζ.symm))
  · have hrd : r < d := by
      exact lt_of_add_lt_add_left (ENNReal.coe_lt_coe.1 (hr.trans_eq hζ))
    have he : e r = a r := Erase.prefixClockIso_apply_of_le hc hm h0 hrd.le
    simpa only [he] using hlift r hrd (by simpa only [he] using hH)

/-- A forward clock and its transported lifetime give the source's inverse
clock link. -/
theorem isRemainderLink_of_forwardClock {c : Chart} {η γ : ℝ≥0 → ℂ}
    {ζ V : ℝ≥0∞} {L m : ℝ}
    (h : HasForwardRemainderClock c η ζ L m γ V) :
    IsRemainderLink c η ζ L (fun s => γ s + m) V := by
  intro hvisit
  obtain ⟨e, hV, hlift⟩ := h hvisit
  refine ⟨e.symm, e.symm.map_bot, e.symm.strictMono, e.symm.continuous,
    fun s => ⟨?_, ?_⟩⟩
  · rw [hV]
    exact lt_clockLife_iff e _ s ζ
  · intro hs hH
    have ht := (lt_clockLife_iff e (firstVisit η ζ L).toNNReal s ζ).1 (hV ▸ hs)
    simpa only [e.apply_symm_apply] using hlift (e.symm s) ht (by
      simpa only [e.apply_symm_apply] using hH)

/-- Remainder links depend only on the relative path before its lifetime. -/
theorem IsRemainderLink.congr_rel {c : Chart} {η γ γ' : ℝ≥0 → ℂ}
    {ζ V : ℝ≥0∞} {L : ℝ} (h : IsRemainderLink c η ζ L γ V)
    (he : ∀ s : ℝ≥0, (s : ℝ≥0∞) < V → γ' s = γ s) :
    IsRemainderLink c η ζ L γ' V := by
  intro hv
  obtain ⟨σ, h0, hm, hc, hσ⟩ := h hv
  refine ⟨σ, h0, hm, hc, fun s => ⟨(hσ s).1, ?_⟩⟩
  intro hs hH
  rw [he s hs] at hH ⊢
  exact (hσ s).2 hs hH

/-- Two generating traces of the same regular driver have the same physical
remainder link. -/
theorem isRemainderLink_of_forwardClock_of_generatingTrace
    {c : Chart} {η γ γ' : ℝ≥0 → ℂ} {ζ V : ℝ≥0∞} {L m : ℝ}
    {W : ℝ≥0 → ℝ} (hgeom : HasForwardRemainderClock c η ζ L m γ V)
    (hγ : IsGeneratingTrace W V γ) (hγ' : IsGeneratingTrace W V γ')
    (hWc : ContinuousOn W {t | (t : ℝ≥0∞) < V}) (hW0 : W 0 = 0) :
    IsRemainderLink c η ζ L (fun s => γ' s + m) V := by
  apply (isRemainderLink_of_forwardClock hgeom).congr_rel
  intro s hs
  rw [IsGeneratingTrace.eq_of_le hγ' hγ hWc hW0 hs.le]

end InteractingSLE.Theorem14.SB.Lv
