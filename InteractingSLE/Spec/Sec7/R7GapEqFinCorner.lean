/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinBoundary

/-!
# The old shared corner from the full contained-arm extension

PROVE-R7-GAPEQ continuation. A clipped contained barrier ends at the pocket entrance, but
the full incoming arm continues past that point in reverse visit order. Its strict old-tail
cover supplies the corner argument after adjoining the forbidden exterior to the pocket.
The exact remaining geometry is the open enlargement `V` and its local boundary cover.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace InteractingSLE.Sec7.R7GapEqFin

open Sec6 R7GapEq R7StopIn

/-- An old boundary cover of an allowed open enlargement supplies the shared-corner input.
The outer wall need not be visited: it can be absorbed into the enlargement. -/
theorem hasOldAllowedCover_of_enlargement
    {η : ℝ → ℂ} {C F K V : Set ℂ} {p : ℂ} {t : ℝ}
    (hVo : IsOpen V) (hCV : C ⊆ V) (hV : V ⊆ C ∪ F ∪ K)
    (hVK : frontier V ⊆ K) (hold : HasOldBoundaryCover η V p t) :
    HasOldAllowedCover η C F K p t := by
  obtain ⟨r, hr, hrt, U, J, hU, hpU, hJ, hfr⟩ := hold
  exact ⟨V, hVo, hCV, hV, r, hr, hrt, U, J, hU, hpU, hJ,
    fun z hz => ⟨hfr hz, hVK hz.1⟩⟩

/-- **Shared entrance corner, clipped barrier form.** Let `B` be the subarc `α([a,b])` of a
larger reverse-visited contained arm, with `b < 1`. An attachment of `B` strictly before its
entrance endpoint makes that endpoint a strict old point of `α`. The landed strict-tail cover
then proves the corner input on an allowed enlargement `V`.

The new mathematical input is explicit: `V` is open, uses only `C ∪ F ∪ K`, and its boundary
near the entrance belongs to this full contained arm. No property of an unvisited outer arm
has been assumed in the visit-order hypotheses. -/
theorem cornerCover_of_contained_extension
    {η B α : ℝ → ℂ} {C F K V A : Set ℂ} {τ σ a b : ℝ}
    (hη : ContinuousOn η (Ici 0)) (hBc : ContinuousOn B (Icc 0 1))
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder α fun t => η '' Icc 0 t)
    (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hB : ∀ v ∈ Icc (0 : ℝ) 1, B v = α (a + v * (b - a)))
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1)
    (hVo : IsOpen V) (hCV : C ⊆ V) (hV : V ⊆ C ∪ F ∪ K)
    (hVK : frontier V ⊆ K) (hA : IsClosed A)
    (hfr : frontier V ⊆ α '' Icc 0 1 ∪ A) (hpA : α b ∉ A) :
    ∀ t ∈ Ioo τ σ, firstVisit (fun s => η '' Icc 0 s) B t < 1 →
      η t = B 1 → HasOldAllowedCover η C F K (η t) t := by
  have hB1 : B 1 = α b := by
    rw [hB 1 ⟨zero_le_one, le_rfl⟩, one_mul, add_sub_cancel]
  intro t ht hlt hp
  let u := firstVisit (fun s => η '' Icc 0 s) B t
  have hmem := firstVisit_mem (R := fun s => η '' Icc 0 s) hBc
    (isCompact_Icc.image_of_continuousOn (hη.mono fun _ hs => hs.1)).isClosed
    ⟨1, ⟨zero_le_one, le_rfl⟩, τ, ⟨hτ0, ht.1.le⟩, hτ⟩
  have hw0 : 0 ≤ a + u * (b - a) := add_nonneg ha
    (mul_nonneg hmem.1.1 (sub_nonneg.2 hab.le))
  have hwb : a + u * (b - a) < b := by
    have hm := mul_lt_mul_of_pos_right hlt (sub_pos.2 hab)
    dsimp [u] at ⊢
    linarith
  have hfirst : firstVisit (fun s => η '' Icc 0 s) α t < b :=
    (firstVisit_le ⟨hw0, hwb.le.trans hb.le⟩
      (by rw [← hB u hmem.1]; exact hmem.2)).trans_lt hwb
  apply hasOldAllowedCover_of_enlargement hVo hCV hV hVK
  exact hasOldBoundaryCover_of_strict_tail hη hαc hαi hrev hA hfr
    (hτ0.trans ht.1.le) ⟨ha.trans hab.le, hb.le⟩ (hp.trans hB1) hpA hfirst

end InteractingSLE.Sec7.R7GapEqFin
