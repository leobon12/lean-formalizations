import QuantumZipper.Proofs.Zipper.E1Defs

/-!
# TR-MEAS, part 1: the live set at time `t` depends only on the driver on `[0,t]`

`handoff/E1-PLAN.md`, node E1-TR (TR-MEAS: `trInt` must be a function of the stopped driver
`V^t`). A real reverse solution on `[0,t]` extends past `t` (local existence at the restarted
point `u t ≠ 0`, `RealLine.exists_isRealRevSol_local`), so `IsLive v t x` holds iff a solution
exists on `[0,t]`, which only reads `v` on `[0,t]`.

Source: none needed — **own elementary proof** (continuation of an ODE solution by gluing a
local solution; standard ODE fact).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

variable {W : ℝ → ℝ} {x t : ℝ} {u : ℝ → ℝ}

/-- A real reverse solution on `[0,t]` extends to some `[0,T']` with `T' > t`. -/
theorem exists_isRealRevSol_extend (hW : Continuous W) (ht : 0 ≤ t)
    (hu : IsRealRevSol W x t u) : ∃ T' > t, ∃ u', IsRealRevSol W x T' u' := by
  have hut := hu.2 t ⟨ht, le_rfl⟩
  set x' := u t + W t with hx'
  have hWs : Continuous fun r => W (t + r) := hW.comp (continuous_const.add continuous_id)
  obtain ⟨ε, hε, v, hv⟩ := RealLine.exists_isRealRevSol_local (x := x') hWs
    (by simp only [add_zero, hx']; intro h; exact hut.1 (by linarith))
  have hv0 : v 0 = u t := by
    have := (hv.2 0 ⟨le_rfl, hε.le⟩).2
    simp only [add_zero, intervalIntegral.integral_same, sub_zero] at this
    rw [this, hx']; ring
  set u' : ℝ → ℝ := fun s => if s ≤ t then u s else v (s - t) with hu'
  have e1 : ∀ s ∈ Icc 0 t, u' s = u s := fun s hs => if_pos hs.2
  have e2 : ∀ s ∈ Icc t (t + ε), u' s = v (s - t) := fun s hs => by
    by_cases h : s ≤ t
    · have : s = t := le_antisymm h hs.1
      simp [hu', h, this, hv0]
    · simp [hu', h]
  have hmaps : MapsTo (fun s => s - t) (Icc t (t + ε)) (Icc 0 ε) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hc1 : ContinuousOn u' (Icc 0 t) := hu.1.congr e1
  have hc2 : ContinuousOn u' (Icc t (t + ε)) :=
    (hv.1.comp (continuousOn_id.sub continuousOn_const) hmaps).congr e2
  have hIcc : Icc 0 (t + ε) = Icc 0 t ∪ Icc t (t + ε) :=
    (Icc_union_Icc_eq_Icc ht (by linarith)).symm
  have hcont : ContinuousOn u' (Icc 0 (t + ε)) := by
    rw [hIcc]; exact hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc
  have hne : ∀ s ∈ Icc 0 (t + ε), u' s ≠ 0 := by
    intro s hs
    by_cases h : s ≤ t
    · rw [e1 s ⟨hs.1, h⟩]; exact (hu.2 s ⟨hs.1, h⟩).1
    · push Not at h
      rw [e2 s ⟨h.le, hs.2⟩]; exact (hv.2 _ (hmaps ⟨h.le, hs.2⟩)).1
  have hdc : ContinuousOn (fun s => 2 / u' s) (Icc 0 (t + ε)) :=
    continuousOn_const.div hcont hne
  have hII : ∀ a b, a ∈ Icc 0 (t + ε) → b ∈ Icc 0 (t + ε) → a ≤ b →
      IntervalIntegrable (fun s => 2 / u' s) volume a b := fun a b ha hb hab =>
    (hdc.mono (Icc_subset_Icc ha.1 hb.2)).intervalIntegrable_of_Icc hab
  have hI0 : ∀ s ∈ Icc 0 t, (∫ r in (0 : ℝ)..s, 2 / u' r) = ∫ r in (0 : ℝ)..s, 2 / u r := by
    intro s hs
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    simp only [e1 r ⟨hr.1, hr.2.trans hs.2⟩]
  refine ⟨t + ε, by linarith, u', hcont, fun s hs => ⟨hne s hs, ?_⟩⟩
  by_cases h : s ≤ t
  · rw [e1 s ⟨hs.1, h⟩, hI0 s ⟨hs.1, h⟩]; exact (hu.2 s ⟨hs.1, h⟩).2
  · push Not at h
    have hst : s - t ∈ Icc 0 ε := hmaps ⟨h.le, hs.2⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hII 0 t ⟨le_rfl, by linarith⟩ ⟨ht, by linarith⟩ ht)
      (hII t s ⟨ht, by linarith⟩ hs h.le)
    have hshift : (∫ r in t..s, 2 / u' r) = ∫ r in (0 : ℝ)..(s - t), 2 / v r := by
      have := intervalIntegral.integral_comp_add_right (fun r => 2 / u' r) t
        (a := 0) (b := s - t)
      simp only [zero_add, sub_add_cancel] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hst.1] at hr
      rw [e2 (r + t) ⟨by linarith [hr.1], by linarith [hr.2, hst.2]⟩, add_sub_cancel_right]
    rw [e2 s ⟨h.le, hs.2⟩, (hv.2 _ hst).2, ← hsplit, hI0 t ⟨ht, le_rfl⟩, hshift, hx', hut.2]
    simp only [show t + (s - t) = s by ring]
    ring

/-- For a continuous driver and `t ≥ 0`, `x` is live at time `t` iff a real reverse solution
exists on `[0,t]`. -/
theorem isLive_iff_exists (hW : Continuous W) (ht : 0 ≤ t) :
    IsLive W t x ↔ ∃ u, IsRealRevSol W x t u := by
  refine ⟨exists_isRealRevSol_of_isLive, fun ⟨u, hu⟩ => ?_⟩
  obtain ⟨T', hT', u', hu'⟩ := exists_isRealRevSol_extend hW ht hu
  exact lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hT', ht.trans_lt hT'⟩)
    (RealLine.ofReal_le_realHitTime (ht.trans hT'.le) hu')

theorem isRealRevSol_congr_drive {W' : ℝ → ℝ} (h : EqOn W W' (Icc 0 t)) :
    IsRealRevSol W x t u ↔ IsRealRevSol W' x t u := by
  unfold IsRealRevSol
  refine and_congr Iff.rfl (forall₂_congr fun s hs => ?_)
  rw [h hs]

/-- The live set at time `t` depends only on the driver on `[0,t]`. -/
theorem isLive_congr_drive {W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') (ht : 0 ≤ t)
    (h : EqOn W W' (Icc 0 t)) : IsLive W t x ↔ IsLive W' t x := by
  rw [isLive_iff_exists hW ht, isLive_iff_exists hW' ht]
  exact exists_congr fun u => isRealRevSol_congr_drive h

theorem liveNeg_congr_drive {W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') (ht : 0 ≤ t)
    (h : EqOn W W' (Icc 0 t)) : liveNeg W t = liveNeg W' t := by
  ext y
  exact and_congr Iff.rfl (isLive_congr_drive hW hW' ht h)

end E1
end QuantumZipper
