/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessPullEnd
import InteractingSLE.Spec.Sec7.ContinuityProb4Band

/-!
# Closing a trace at a finite horizon from its coded condition

Packet PROVE-SEC7-C10 (step R5 of `planning/handoffs/PROVE-SEC7-C8.md`). The coded trace event of a finite horizon
`Z` (`Sec7.RandRestart.FinCond`) contains the uniform continuity of the trace values `traceAt p w` at rational times
`p < Z`. Together with generating traces on `[0, r]` for the rational `r < Z`, it gives a generating trace on the
closed interval `[0, Z]` (`exists_isGeneratingTrace_of_finCond`), without a left limit of the driver at `Z` (which the
decoding `mem_traceSet_iff` would need).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal NNRat
open QuantumZipper (H fwdHull)

namespace InteractingSLE

namespace Zhan

namespace Retarget

open Sec7.RandRestart

/-- A rational strictly between two nonnegative reals. -/
theorem exists_nnrat_btwn {a b : ℝ≥0} (h : a < b) : ∃ q : ℚ≥0, a < (q : ℝ≥0) ∧ (q : ℝ≥0) < b := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (a : ℝ) < b by exact_mod_cast h)
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast (a.coe_nonneg.trans hq1.le)
  have hc : ((((q.toNNRat : ℚ≥0) : ℝ≥0)) : ℝ) = (q : ℝ) := by
    have h1 : (((q.toNNRat : ℚ≥0) : ℚ) : ℝ) = (q : ℝ) := by rw [Rat.coe_toNNRat q hq0]
    rw [← h1]; norm_cast
  refine ⟨q.toNNRat, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, hc]; exact hq1
  · rw [← NNReal.coe_lt_coe, hc]; exact hq2

/-- **A generating trace on `[0, Z]` from the coded finite-horizon condition.** If the driver is continuous before
`Z` with `w 0 = 0`, has a generating trace on `[0, r]` for every rational `r < Z`, and satisfies `FinCond w Z`, then it
has a generating trace on `[0, Z]`. -/
theorem exists_isGeneratingTrace_of_finCond {w : ℝ≥0 → ℝ} {Z : ℝ≥0}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < Z}) (hw0 : w 0 = 0)
    (hrat : ∀ t : ℝ≥0, t < Z → ∃ q : ℝ≥0, t < q ∧ q < Z ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w q η)
    (hF : FinCond w Z) : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w Z η := by
  rcases eq_or_ne Z 0 with rfl | hZ0
  · exact ⟨fun _ => 0, rfl, fun t ht => continuousWithinAt_const, fun t ht => absurd ht (by simp)⟩
  have hZpos : 0 < Z := pos_iff_ne_zero.2 hZ0
  set f : ℝ≥0 → ℂ := fun t => LP.traceAt t w with hf
  -- local traces: `f = η_q` before a rational `q < Z`
  have hloc : ∀ t : ℝ≥0, t < Z → ∃ q : ℝ≥0, t < q ∧ q < Z ∧ ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace w q η ∧ ∀ s : ℝ≥0, s < q → f s = η s := by
    intro t ht
    obtain ⟨q, htq, hqZ, η, hη⟩ := hrat t ht
    refine ⟨q, htq, hqZ, η, hη, fun s hs => ?_⟩
    exact LP.traceAt_eq_of_isGeneratingTrace hη
      (hw.mono fun r (hr : (r : ℝ≥0∞) < q) => hr.trans (by exact_mod_cast hqZ)) hw0
      (by exact_mod_cast hs)
  have hcont : ∀ t : ℝ≥0, t < Z → ContinuousAt f t := by
    intro t ht
    obtain ⟨q, htq, -, η, hη, hfη⟩ := hloc t ht
    have hopen : IsOpen (Iio q) := isOpen_Iio
    have hηc : ContinuousAt η t := (hη.2.1 t (by exact_mod_cast htq.le)).continuousAt
      (Filter.mem_of_superset (hopen.mem_nhds htq) fun s (hs : s < q) =>
        show (s : ℝ≥0∞) ≤ q by exact_mod_cast hs.le)
    exact hηc.congr (Filter.eventuallyEq_of_mem (hopen.mem_nhds htq) fun s hs => (hfη s hs).symm)
  -- the limit at `Z`
  have hcauchy : Cauchy (map f (𝓝[<] Z)) := by
    have hne : (𝓝[<] Z).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hZpos⟩
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
    obtain ⟨k, hk⟩ := hF.1 m
    set δ : ℝ≥0 := (1 / ((k : ℝ) + 1) / 2).toNNReal with hδ
    have hδpos : 0 < δ := by rw [hδ]; exact Real.toNNReal_pos.2 (by positivity)
    set a : ℝ≥0 := Z - δ with ha
    have haZ : a < Z := tsub_lt_self hZpos hδpos
    refine ⟨f '' Ioo a Z, image_mem_map (Ioo_mem_nhdsLT haZ), ?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    -- rational approximations
    have happrox : ∀ u ∈ Ioo a Z, ∀ η' > 0, ∃ p : ℚ≥0, (p : ℝ≥0) ∈ Ioo a Z ∧
        dist (p : ℝ≥0) u < η' ∧ dist (f p) (f u) < ε / 3 := by
      intro u hu η' hη'
      obtain ⟨d, hd, hdf⟩ := Metric.continuousAt_iff.1 (hcont u hu.2) (ε / 3) (by positivity)
      set d' : ℝ≥0 := (min d η').toNNReal with hd'
      have hd'pos : 0 < d' := Real.toNNReal_pos.2 (lt_min hd hη')
      have hlo : max a (u - d') < u := max_lt hu.1 (tsub_lt_self (lt_of_le_of_lt bot_le hu.1) hd'pos)
      obtain ⟨p, hp1, hp2⟩ := exists_nnrat_btwn hlo
      have hpu : dist (p : ℝ≥0) u < min d η' := by
        rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (by
          have : (p : ℝ≥0) < u := hp2; exact sub_pos.2 (by exact_mod_cast this))]
        have h1 : u - d' < (p : ℝ≥0) := lt_of_le_of_lt (le_max_right _ _) hp1
        have h2 : (u : ℝ) - d' ≤ ((u - d' : ℝ≥0) : ℝ) := by
          rw [NNReal.coe_sub_def]; exact le_max_left _ _
        have h3 : (d' : ℝ) = min d η' := Real.coe_toNNReal _ (le_min hd.le hη'.le)
        have h4 : ((u - d' : ℝ≥0) : ℝ) < (p : ℝ≥0) := by exact_mod_cast h1
        linarith
      exact ⟨p, ⟨lt_of_le_of_lt (le_max_left _ _) hp1, hp2.trans hu.2⟩,
        hpu.trans_le (min_le_right _ _), hdf (hpu.trans_le (min_le_left _ _))⟩
    have hδ' : (δ : ℝ) = 1 / ((k : ℝ) + 1) / 2 := Real.coe_toNNReal _ (by positivity)
    obtain ⟨p, hp, hps, hfp⟩ := happrox s hs ((δ : ℝ) / 2) (by positivity)
    obtain ⟨p', hp', hps', hfp'⟩ := happrox s' hs' ((δ : ℝ) / 2) (by positivity)
    have hss' : dist s s' < δ := by
      have h1 : (Z : ℝ) - δ ≤ (a : ℝ) := by rw [ha, NNReal.coe_sub_def]; exact le_max_left _ _
      rw [NNReal.dist_eq]
      have := hs.1; have := hs.2; have := hs'.1; have := hs'.2
      have e1 : (a : ℝ) < s := by exact_mod_cast hs.1
      have e2 : (s : ℝ) < Z := by exact_mod_cast hs.2
      have e3 : (a : ℝ) < s' := by exact_mod_cast hs'.1
      have e4 : (s' : ℝ) < Z := by exact_mod_cast hs'.2
      rw [abs_lt]; constructor <;> linarith
    have hpp' : dist (p : ℝ≥0) (p' : ℝ≥0) < 1 / ((k : ℝ) + 1) := by
      calc dist (p : ℝ≥0) (p' : ℝ≥0) ≤ dist (p : ℝ≥0) s + dist s s' + dist s' (p' : ℝ≥0) :=
            dist_triangle4 _ _ _ _
        _ < δ / 2 + δ + δ / 2 := by
            rw [dist_comm s' (p' : ℝ≥0)] at *
            have := dist_comm (p' : ℝ≥0) s'
            linarith
        _ = 1 / ((k : ℝ) + 1) := by rw [hδ']; ring
    have hkey := hk p p' (by exact_mod_cast hp.2) (by exact_mod_cast hp'.2) hpp'
    calc dist (f s) (f s') ≤ dist (f s) (f p) + dist (f p) (f p') + dist (f p') (f s') :=
          dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
          rw [dist_comm (f s) (f p)]
          have : dist (LP.traceAt (p : ℝ≥0) w) (LP.traceAt (p' : ℝ≥0) w) ≤ 1 / ((m : ℝ) + 1) := hkey
          have : dist (f p) (f p') ≤ 1 / ((m : ℝ) + 1) := this
          linarith
      _ = ε := by ring
  have hne : (𝓝[<] Z).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hZpos⟩
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hcauchy
  refine ⟨_, isGeneratingTrace_piecewise (T := (Z : ℝ≥0∞)) (f := f) (e := L) (fun _ => ?_)
    (fun h => absurd (by exact_mod_cast h) hZ0) (fun t ht => hcont t (by exact_mod_cast ht))
    (fun t ht => ?_) fun S hS => ?_⟩
  · obtain ⟨q, hq0, -, η, hη, hfη⟩ := hloc 0 hZpos
    rw [hfη 0 hq0, hη.1]
  · obtain ⟨q, htq, -, η, hη, hfη⟩ := hloc t (by exact_mod_cast ht)
    rw [image_congr fun s hs => hfη s (lt_of_le_of_lt hs.2 htq)]
    exact hη.2.2 t (by exact_mod_cast htq)
  · have : S = Z := by exact_mod_cast hS
    rw [this]
    exact hL

end Retarget

end Zhan

end InteractingSLE
