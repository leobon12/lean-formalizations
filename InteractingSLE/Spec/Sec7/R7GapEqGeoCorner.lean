/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinCorner

/-!
# Local allowed-side geometry at the shared corner

PROVE-R7-GAPEQ. A local one-sided enlargement suffices: patch it to the pocket inside an
open neighborhood. No global allowed enlargement or global simple frontier is assumed.
The remaining input is the exact local side inclusion, stated explicitly in the theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace InteractingSLE.Sec7.R7GapEqGeo

open Sec6 R7GapEq R7GapEqFin

/-- Patch a local allowed side to the pocket. Only its boundary near the marked point must
be old and contained in `K`; no global condition on the side's frontier is necessary. -/
theorem hasOldAllowedCover_of_local_side {η : ℝ → ℂ} {C F K S U : Set ℂ} {p : ℂ} {t : ℝ}
    (hCo : IsOpen C) (hSo : IsOpen S) (hUo : IsOpen U) (hpU : p ∈ U)
    (hCS : C ∩ U ⊆ S) (hSC : S ∩ U ⊆ C ∪ F ∪ K)
    (hSK : frontier S ∩ U ⊆ K) (hold : HasOldBoundaryCover η S p t) :
    HasOldAllowedCover η C F K p t := by
  let V := C ∪ (S ∩ U)
  have hVo : IsOpen V := hCo.union (hSo.inter hUo)
  have hfront : frontier V ∩ U ⊆ frontier S := by
    intro z hz
    have hzcl : z ∈ closure (U ∩ V) := hUo.inter_closure ⟨hz.2, hz.1.1⟩
    have hUS : U ∩ V ⊆ S := by
      rintro w ⟨hwU, hwC | hwS⟩
      · exact hCS ⟨hwC, hwU⟩
      · exact hwS.1
    refine ⟨closure_mono hUS hzcl, ?_⟩
    rw [hSo.interior_eq]
    intro hzS
    exact hz.1.2 (hVo.interior_eq.symm ▸ (Or.inr ⟨hzS, hz.2⟩ : z ∈ V))
  obtain ⟨r, hr, hrt, O, hJ, hO, hpO, hJold, hfr⟩ := hold
  refine ⟨V, hVo, subset_union_left, fun z hz => ?_, r, hr, hrt,
    O ∩ U, hJ, hO.inter hUo, ⟨hpO, hpU⟩, hJold, fun z hz => ?_⟩
  · exact hz.elim (fun h => Or.inl (Or.inl h)) (fun h => hSC h)
  · have hzS := hfront ⟨hz.1, hz.2.2⟩
    exact ⟨hfr ⟨hzS, hz.2.1⟩, hSK ⟨hzS, hz.2.2⟩⟩

/-- An attained attachment on an affine subarc bounds the full arm's attachment strictly
before the subarc's entrance endpoint. This is the local step used in the landed corner proof. -/
theorem firstVisit_full_lt_of_subarc {η B α : ℝ → ℂ} {τ a b t : ℝ}
    (hη : ContinuousOn η (Ici 0)) (hBc : ContinuousOn B (Icc 0 1))
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hB : ∀ v ∈ Icc (0 : ℝ) 1, B v = α (a + v * (b - a)))
    (hτ0 : 0 ≤ τ) (hτt : τ ≤ t) (hτ : η τ = B 1)
    (hlt : firstVisit (fun s => η '' Icc 0 s) B t < 1) :
    firstVisit (fun s => η '' Icc 0 s) α t < b := by
  let u := firstVisit (fun s => η '' Icc 0 s) B t
  have hmem := firstVisit_mem (R := fun s => η '' Icc 0 s) hBc
    (isCompact_Icc.image_of_continuousOn (hη.mono fun _ hs => hs.1)).isClosed
    ⟨1, ⟨zero_le_one, le_rfl⟩, τ, ⟨hτ0, hτt⟩, hτ⟩
  have hu0 : 0 ≤ a + u * (b - a) := add_nonneg ha
    (mul_nonneg hmem.1.1 (sub_nonneg.2 hab.le))
  have hub : a + u * (b - a) < b := by
    have hm := mul_lt_mul_of_pos_right hlt (sub_pos.2 hab)
    dsimp [u]
    linarith only [hm]
  exact (firstVisit_le ⟨hu0, hub.le.trans hb⟩
    (by rw [← hB u hmem.1]; exact hmem.2)).trans_lt hub

/-- **The corner cover from local side geometry.** The full reverse-visited arm supplies
the old boundary. The only remaining geometric data concern the side `S` inside `U`.
This replaces the previous requirement for a global enlargement `V`. -/
theorem cornerCover_of_local_extension
    {η B α : ℝ → ℂ} {C F K S U D : Set ℂ} {τ σ a b : ℝ}
    (hη : ContinuousOn η (Ici 0)) (hBc : ContinuousOn B (Icc 0 1))
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder α fun t => η '' Icc 0 t)
    (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hB : ∀ v ∈ Icc (0 : ℝ) 1, B v = α (a + v * (b - a)))
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1) (hCo : IsOpen C)
    (hSo : IsOpen S) (hUo : IsOpen U) (hpU : B 1 ∈ U)
    (hCS : C ∩ U ⊆ S) (hSC : S ∩ U ⊆ C ∪ F ∪ K)
    (hSK : frontier S ∩ U ⊆ K) (hD : IsClosed D)
    (hfrS : frontier S ⊆ α '' Icc 0 1 ∪ D) (hpD : α b ∉ D) :
    ∀ t ∈ Ioo τ σ, firstVisit (fun s => η '' Icc 0 s) B t < 1 →
      η t = B 1 → HasOldAllowedCover η C F K (η t) t := by
  intro t ht hlt hp
  have hB1 : B 1 = α b := by rw [hB 1 ⟨zero_le_one, le_rfl⟩, one_mul, add_sub_cancel]
  apply hasOldAllowedCover_of_local_side hCo hSo hUo (hp ▸ hpU) hCS hSC hSK
  exact hasOldBoundaryCover_of_strict_tail hη hαc hαi hrev hD hfrS
    (hτ0.trans ht.1.le) ⟨ha.trans hab.le, hb.le⟩ (hp.trans hB1) hpD
    (firstVisit_full_lt_of_subarc hη hBc ha hab hb.le hB hτ0 ht.1.le hτ hlt)

end InteractingSLE.Sec7.R7GapEqGeo
