/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaClock

/-! # GW4: a single actual winding integer throughout physical time -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull logDerivFwd)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse Sec7.PocketStopSide MartChar.RealFlow

/-- The actual component phase integer is independent of physical time.
A persistent earlier seed collar identifies all nearby integers, and the
positive-capacity physical times below the version lifetime are connected. -/
theorem Frame.exists_time_common_current_phase_int {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t) :
    ∃ n : ℤ, ∀ t q : ℝ≥0, F.ent w ≤ t → (t : ℝ≥0∞) < F.exit w →
      0 < q → (q : ℝ≥0∞) < V → (q : ℝ) = F.rcap w t → ∀ ξ ∈ Ioo
        (-rightImg (fun s : ℝ => -R s.toNNReal) 0 q - R q)
        (rightImg (fun s : ℝ => R s.toNNReal) 0 q - R q),
      Tendsto (fun y =>
        (componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).2.2
          ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).2.1 y) -
        (logDerivFwd (fun s : ℝ => w s.toNNReal) t
          ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).2.1 y)).im)
        (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  classical
  let I : Set ℝ≥0 := {t | 0 < F.rcap w t ∧ (t : ℝ≥0∞) < F.exit w ∧
    ENNReal.ofReal (F.rcap w t) < V}
  let cap : I → ℝ≥0 := fun t => (F.rcap w t.1).toNNReal
  have hcap (t : I) : (cap t : ℝ) = F.rcap w t.1 := Real.coe_toNNReal _ t.2.1.le
  have hcapPos (t : I) : 0 < cap t := NNReal.coe_pos.1 (by rw [hcap]; exact t.2.1)
  have hcapV (t : I) : (cap t : ℝ≥0∞) < V := t.2.2.2
  have hEnt (t : I) : F.ent w < t.1 := Frame.ent_lt_of_rcap_pos hF hw t.2.1
  have hEach (t : I) := Frame.exists_current_phase_int hF hw hR hR0 hVer
    (hEnt t).le t.2.2.1 (hcapPos t) (hcapV t) (hcap t)
  choose n hn using hEach
  have hBase := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 (Frame.isOpen_C hF hw)
      (subset_H_of_mem_betweenComponents hF.2.1))).trans Chart.isConformal_infinitySourceChart
  have hRR : Continuous (fun r : ℝ => R r.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun r : ℝ => R r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  have hcapCont : Continuous (fun t : I => F.rcap w t.1) :=
    (Frame.continuousOn_rcap_real hF hw).comp_continuous continuous_subtype_val fun t => t.2.2.1
  have hnLoc : IsLocallyConstant n := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨p, x, hp, hpq, hx, hnear⟩ := exists_persistent_seed_collar hBase hRR hRR0
      (show 0 < (cap t₀ : ℝ) by exact NNReal.coe_pos.2 (hcapPos t₀))
    let pN : ℝ≥0 := ⟨p, hp.le⟩
    have hpN : 0 < pN := hp
    have hpV : (pN : ℝ≥0∞) < V :=
      (ENNReal.coe_lt_coe.2 (show pN < cap t₀ from hpq)).trans (hcapV t₀)
    obtain ⟨s, hsEnt, hsExit, hps⟩ := Frame.exists_physical_time_of_capacity hF hw hR hR0 hpN (hVer pN hpV)
    obtain ⟨m, hm⟩ := Frame.exists_current_phase_int hF hw hR hR0 hVer hsEnt.le hsExit hpN hpV hps
    have hxN : x ∈ Ioo (-rightImg (fun r : ℝ => -R r.toNNReal) 0 pN - R pN)
        (rightImg (fun r : ℝ => R r.toNNReal) 0 pN - R pN) := by
      simpa only [← show (pN : ℝ) = p from rfl, Real.toNNReal_coe] using hx
    have hnear' := (hcapCont.continuousAt (x := t₀)).eventually (by simpa only [hcap] using hnear)
    have heq : ∀ᶠ t : I in 𝓝 t₀, m = n t := by
      filter_upwards [hnear'] with t ht
      rw [← hcap t] at ht
      obtain ⟨hpt, ξ, hξ, ε, hε, hcol, htr, hlift⟩ := ht
      have hst := Frame.lt_of_rcap_lt hF hw hsExit t.2.2.1
        (show F.rcap w s < F.rcap w t.1 by rw [← hps, ← hcap t]; exact hpt)
      exact Frame.phase_int_eq_of_seed_collar hF hw hR hR0 hVer hsEnt.le (hEnt t).le
        t.2.2.1 hst.le hpN (show pN ≤ cap t from hpt.le) (hcapV t) hps (hcap t)
        hxN hε hcol htr hlift (hm x hxN) (hn t ξ (by simpa only [Real.toNNReal_coe] using hξ))
    have heq₀ : m = n t₀ := heq.self_of_nhds
    exact heq.mono fun t ht => ht.symm.trans heq₀
  have hPre : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.1
    (Frame.ordConnected_phase_times hF hw V).isPreconnected
  let : PreconnectedSpace I := hPre
  by_cases hI : I.Nonempty
  · obtain ⟨t₀, ht₀⟩ := hI
    refine ⟨n ⟨t₀, ht₀⟩, fun t q htEnt htExit hq hqV hqt ξ hξ => ?_⟩
    have htI : t ∈ I := ⟨by rw [← hqt]; exact NNReal.coe_pos.2 hq, htExit,
      by rw [← hqt, ENNReal.ofReal_coe_nnreal]; exact hqV⟩
    have hqc : cap ⟨t, htI⟩ = q := NNReal.eq (by rw [hcap]; exact hqt.symm)
    have h := hn ⟨t, htI⟩
    rw [hqc, hnLoc.apply_eq_of_preconnectedSpace ⟨t, htI⟩ ⟨t₀, ht₀⟩] at h
    exact h ξ hξ
  · refine ⟨0, fun t q _ htExit hq hqV hqt => ?_⟩
    exact (hI ⟨t, by
      exact ⟨by rw [← hqt]; exact NNReal.coe_pos.2 hq, htExit,
        by rw [← hqt, ENNReal.ofReal_coe_nnreal]; exact hqV⟩⟩).elim

end InteractingSLE.Theorem14.GW4Fix
