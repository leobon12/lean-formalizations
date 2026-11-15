/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbStage
import InteractingSLE.Spec.Supplement.GW2NgJunc

/-!
# The tip event of the stage code from the versions (one sample)

Packet PROVE-GW2-RELDET (round 38, decisions D73 route (ii) and D81). At one sample, let a good driver code `p` match a
family of stage drivers `D n` below their caps `C n` (`IsStopDrvMatch`: GB6's engine on every version), let the stage
word `b` carry the far right height `λ' − πχ + θa χ` beyond `J` (`GW2Ni.FarRAt`, `θa ∈ (−π/2, π/2)`), and let every
point `q > J` be alive for every `D n` below its cap (nothing has touched the counterflow side before the contact).
At a first contact at the tip, either

* the caps exhaust `ℝ≥0` (the relative clock is unbounded before the contact): then `p` has infinite lifetime, its
  decoded driver is every `D n` below `C n`, and `BadCode` holds (a rational `r > J`; the far height has weight in
  `(κ/2 − 4, κ/2 − 2)`, `lt_cumWeightRight_far` and NEARIMG2's `GW2Ni.cumWeightRight_far_lt`);
* or the caps are bounded while the drivers are unbounded (the relative curve reaches the tip at a finite relative
  capacity): then `BadFin` holds.

* **`tipCode_of_versions`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rd

open MartChar.RealFlow Restart Sec2.Assembly Supp8.GB6 Supp8.GB6.RelDrv Sec4

/-- **The tip event of the stage code from the versions** (one sample). -/
theorem tipCode_of_versions {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : BoundaryWord} {p : PCode × ℝ≥0∞}
    (hgood : IsGoodDrvCode p) {D : ℕ → ℝ≥0 → ℝ} {C : ℕ → ℝ≥0∞}
    (hD : ∀ n, ContinuousOn (D n) {u | (u : ℝ≥0∞) < C n}) (hmatch : ∀ n, IsStopDrvMatch p (D n) (C n))
    {J θa : ℝ} (hJ : 0 < J) (hθ : θa ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hfar : GW2Ni.FarRAt b (sleLambda (16 / κ) - Real.pi * chiC κ + θa * chiC κ) J)
    (halive : ∀ (n : ℕ) (u : ℝ≥0), (u : ℝ≥0∞) < C n → ∀ q : ℝ, J < q →
      Alive (fun s : ℝ => D n s.toNNReal) q u)
    (hcases : (∀ U : ℝ≥0, ∃ n, (U : ℝ≥0∞) < C n) ∨
      ((∃ B : ℝ≥0, ∀ n, C n ≤ B) ∧ ∀ M : ℝ, ∃ (n : ℕ) (u : ℝ≥0), (u : ℝ≥0∞) < C n ∧ M < |D n u|)) :
    TipCode κ b p := by
  have hdec : ∀ n (u : ℝ≥0), (u : ℝ≥0∞) < C n → drvDec p u = D n u := fun n =>
    eqOn_drvDec_of_isStopDrvMatch hgood (hD n) (hmatch n)
  rcases hcases with hall | ⟨⟨B, hB⟩, hunb⟩
  · -- the caps exhaust `ℝ≥0`: `BadCode`
    have hp2 : p.2 = ⊤ := by
      by_contra hne
      obtain ⟨n, hn⟩ := hall p.2.toNNReal
      rw [ENNReal.coe_toNNReal hne] at hn
      exact absurd ((hmatch n).1.trans_lt hn) (lt_irrefl _)
    obtain ⟨r, hr⟩ := exists_rat_gt J
    have hr0 : (0 : ℚ) < r := by exact_mod_cast hJ.trans hr
    have hcont : ContinuousOn (drvDec p) univ :=
      (continuousOn_drvDec p).mono fun t _ => show (t : ℝ≥0∞) < p.2 by rw [hp2]; exact ENNReal.coe_lt_top
    refine Or.inr (Or.inl ⟨hp2, hgood, r, hr0, fun x x' hx hx' hxj hx'j => ?_, fun x hx hxj => ?_,
      fun q hq N => ?_⟩)
    · have h1 := hfar x (hr.trans (by exact_mod_cast hx)) hxj
      have h2 := hfar x' (hr.trans (by exact_mod_cast hx')) hx'j
      rw [h1, h2]
    · rw [hfar x (hr.trans (by exact_mod_cast hx)) hxj]
      refine ⟨lt_cumWeightRight_far hκ hκ4 hθ.1, ?_⟩
      have h := GW2Ni.cumWeightRight_far_lt hκ hκ4 hθ.2
      rwa [zero_mul, add_zero] at h
    · obtain ⟨n, hn⟩ := hall (N : ℝ≥0)
      have hal := halive n N hn q (hr.trans (by exact_mod_cast hq))
      refine (GW2Bh.aliveRead_iff (q : ℝ) (hcont.mono (subset_univ _))).2 ?_
      refine (Supp8.GB6.alive_congr fun s hs => ?_).2 hal
      have hsN : s.toNNReal ≤ (N : ℝ≥0) := Real.toNNReal_le_iff_le_coe.2 (by simpa using hs.2)
      have hsC : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < C n := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsN) hn
      simp only [frozenDrive]
      rw [min_eq_left (by simpa using hs.2), hdec n _ hsC]
  · -- bounded caps, unbounded drivers: `BadFin`
    refine Or.inr (Or.inr ⟨fun hp2 => ?_, fun M => ?_⟩)
    · -- an infinite lifetime would bound the decoded driver on `[0, B]`
      have hcont : ContinuousOn (drvDec p) (Icc 0 B) :=
        (continuousOn_drvDec p).mono fun t _ => show (t : ℝ≥0∞) < p.2 by rw [hp2]; exact ENNReal.coe_lt_top
      obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      obtain ⟨n, u, hu, hMu⟩ := hunb M₀
      have huB : u ∈ Icc 0 B := ⟨zero_le, ENNReal.coe_le_coe.1 (hu.le.trans (hB n))⟩
      have h := hM₀ u huB
      rw [Real.norm_eq_abs, hdec n u hu] at h
      linarith
    · obtain ⟨n, u, hu, hMu⟩ := hunb ((M : ℝ) + 1)
      -- a rational time near `u`, below the cap, where the driver is still above `M`
      have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < C n} := isOpen_lt ENNReal.continuous_coe continuous_const
      have hca : ContinuousAt (D n) u := (hD n).continuousAt (hopen.mem_nhds hu)
      have hg : ContinuousAt (fun s : ℝ => D n s.toNNReal) (u : ℝ) := by
        refine ContinuousAt.comp (f := Real.toNNReal) ?_ continuous_real_toNNReal.continuousAt
        rw [Real.toNNReal_coe]
        exact hca
      have hgC : ContinuousAt (fun s : ℝ => ((s.toNNReal : ℝ≥0) : ℝ≥0∞)) (u : ℝ) :=
        (ENNReal.continuous_coe.comp continuous_real_toNNReal).continuousAt
      have hev : ∀ᶠ s in 𝓝 (u : ℝ), |D n s.toNNReal - D n u| < 1 ∧ ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < C n := by
        refine (Metric.tendsto_nhds.1 hg 1 one_pos).mono (fun s hs => ?_) |>.and ?_
        · rw [Real.dist_eq] at hs
          simpa only [Real.toNNReal_coe] using hs
        · have hu' : (fun s : ℝ => ((s.toNNReal : ℝ≥0) : ℝ≥0∞)) (u : ℝ) < C n := by
            simpa only [Real.toNNReal_coe] using hu
          exact hgC.eventually (eventually_lt_nhds hu')
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (u : ℝ) < u + ε by linarith)
      have hqd : dist (q : ℝ) u < ε := by
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        linarith
      obtain ⟨h1, h2⟩ := hball hqd
      refine ⟨q, h2.trans_le (hmatch n).1, ?_⟩
      rw [hdec n _ h2]
      have := abs_sub_abs_le_abs_sub (D n u) (D n (q : ℝ).toNNReal)
      rw [abs_sub_comm] at this
      linarith

end InteractingSLE.Theorem14.GW2Rd
