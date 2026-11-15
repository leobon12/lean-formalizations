/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB8Proof
import InteractingSLE.Spec.Supplement.G12Low
import InteractingSLE.Spec.Supplement.GB7aCmp
import InteractingSLE.Spec.Sec5.Aux22StripAlive
import InteractingSLE.Spec.Sec5.Aux22StripAvoid
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# Lemma GB8, input 3: no contact with `[x₊, ∞)`

Packet PROVE-T14-TIP4. Specification supplement §8.8, proof of **Lemma GB8** (`source/spec/p481-528.md` L1023, p. 523):
"Lemma GB7a protects the open right tail, and G12 protects its junction `x₊` because `c_κ > d_κ`."

This file proves PROVE-T14-TIP2's named input `Supp8.GB8.RightNoContactStatement` (driver form: the outermost right
mark never meets the driver before the lifetime), for every universe. Two cases.

* **Some right mark lies strictly below `x₊`.** Lemma GB7a (`GB7a.gb7aEvol_right` with the proved pathwise input
  `GB7a.gb7aCmpInput`; cumulative weight `κ/2 − 2 ≥ κ/2 − 2`) keeps the trace off `(x₊, ∞)`, and Lemma G12 at the point
  `x₊` (`Supp7.G12Low.ae_trace_ne_right_of_exists`, which needs a mark strictly below `x₊`; weight `κ/2 − 2 > κ/2 − 4`)
  keeps it off `x₊`. A trace off `[x₊, ∞)` up to `t₀` leaves a ball around `x₊` outside the hull, so `x₊` is alive and
  its force coordinate stays right of the driver (`w_lt_vR_of_trace_avoid`, deterministic).
* **Every right mark is at `x₊`.** Then the right force coordinates coincide (`vR_eq_of_xR_eq`) and the right side is
  one group of weight `κ/2 − 2`. At the first meeting time `T` of the outer right coordinate with the driver, every left
  coordinate is at distance at least `x₊` from it (the left and right coordinates move apart), so on `[q, T)` for a
  rational `q` close to `T` the change to the comparison word of GB7a (all left weights `0`, the whole right weight on
  the outer right mark) has bounded energy: its right part vanishes identically. This is GB7a's comparison picture
  (`GB7a.RightCmp`, `exists_rightCmp_of_meet`), which is null for `S = κ/2 − 2` (`GB7a.measure_rightCmp_eq_zero`,
  Aux. lemmas 62–64).

The inner partial-sum hypotheses of GB8 are not used.

## Main results

* `w_lt_vR_of_trace_avoid`: deterministic bridge from the trace to the driver;
* `vR_eq_of_xR_eq`, `exists_rightCmp_of_meet`: the coincident case along one path;
* `rightNoContactStatement`: **`RightNoContactStatement.{u}`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol fwdHull)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB8

/-! ### From the trace to the driver -/

/-- **A point whose ray the trace avoids is alive** (deterministic). If the trace `η` of a driver `w` (continuous
before `ζ`) avoids `[x, ∞)`, `x > 0`, before `ζ`, then a force coordinate `v` from `x` (the Loewner equation, `w ≤ v`)
stays strictly right of the driver before `ζ`. -/
theorem w_lt_vR_of_trace_avoid {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {x : ℝ} (hx : 0 < x)
    (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hvc : ContinuousOn v {s | (s : ℝ≥0∞) < ζ})
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t ≤ v t) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η)
    (havoid : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ y : ℝ, x ≤ y → η t ≠ y) {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) :
    w t₀ < v t₀ := by
  by_contra hcon
  have heq : v t₀ = w t₀ := le_antisymm (not_lt.1 hcon) (hle t₀ ht₀)
  have hv0 : v 0 = x := by
    have := hveq 0 (lt_of_le_of_lt (zero_le (a := (t₀ : ℝ≥0∞))) ht₀)
    simpa using this
  have ht₀pos : 0 < t₀ := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hv0, hw0] at heq
    linarith
  obtain ⟨t₂, h02, h2ζ⟩ : ∃ t₂ : ℝ≥0, t₀ < t₂ ∧ (t₂ : ℝ≥0∞) < ζ := by
    obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
    exact ⟨r, ENNReal.coe_lt_coe.1 hr1, hr2⟩
  have hW2 : ContinuousOn w (Set.Iic t₂) := hwc.mono fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) h2ζ
  set W' : ℝ → ℝ := fun s => Sec5.Aux22Strip.freezeAt w t₂ s.toNNReal with hW'def
  have hW'c : Continuous W' := Sec5.Aux22Strip.continuous_freezeAt hW2
  have hW'0 : W' 0 = 0 := by
    simp only [hW'def, Real.toNNReal_zero]
    rw [Sec5.Aux22Strip.freezeAt_of_le zero_le, hw0]
  have hW'w : ∀ t : ℝ≥0, t ≤ t₂ → W' t = w t := fun t ht => by
    simp only [hW'def, Real.toNNReal_coe]
    exact Sec5.Aux22Strip.freezeAt_of_le ht
  -- the hull at `t₀` is the filling of the trace
  set A := η '' Set.Icc 0 t₀ with hA
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans ht₀.le)
  have hKeq := (fillH_eq_iff_isFilling_of_isClosed hAc.isBounded hAc.isClosed
    ((QuantumZipper.fwdHull_mono).2 _)).1 (hη.2.2 t₀ ht₀)
  have hK' : fwdHull (fun s : ℝ => w s.toNNReal) t₀ = fwdHull W' t₀ := by
    refine fwdHull_eq_of_eqOn t₀.coe_nonneg (NNReal.coe_lt_coe.2 h02) fun r hr => ?_
    have hr' : r.toNNReal ≤ t₂ := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
      exact hr.2
    exact (Sec5.Aux22Strip.freezeAt_of_le hr').symm
  -- a ball around `x` outside the hull
  obtain ⟨R₀, hR₀⟩ := hAc.isBounded.subset_closedBall 0
  have hAR : A ⊆ Metric.closedBall 0 (max R₀ 0) :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨ρ, hρ, hball⟩ := Sec5.Aux22Strip.exists_ball_notMem_fillH_aux hAc hAR (a := x)
    (b := max x (max R₀ 0 + 1)) (e := max x (max R₀ 0 + 1))
    (fun r hr ⟨s, hs, hsr⟩ => havoid s ((ENNReal.coe_le_coe.2 hs.2).trans_lt ht₀) r hr.1 hsr)
    ⟨le_rfl, le_max_left _ _⟩ ⟨le_max_left _ _, le_rfl⟩ (by
      rw [abs_of_pos (lt_of_lt_of_le hx (le_max_left _ _))]
      linarith [le_max_right x (max R₀ 0 + 1)])
  have hdisj : Disjoint (Metric.ball (x : ℂ) ρ) (fwdHull W' t₀) := by
    rw [← hK', hKeq, Set.disjoint_left]
    exact fun z hz => hball z hz
  obtain ⟨u, hu⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW'c hW'0 hx.ne' t₀.coe_nonneg hρ hdisj
  -- the gap tends to `0` at `t₀`, impossible for an alive point
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hlim : Tendsto (fun t => v t - w t) (𝓝[<] t₀) (𝓝 0) := by
    have hc : ContinuousAt (fun t => v t - w t) t₀ :=
      (hvc.continuousAt (hopen.mem_nhds ht₀)).sub (hwc.continuousAt (hopen.mem_nhds ht₀))
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio t₀))
    rwa [heq, sub_self] at this
  have hsub : Set.Iio t₀ ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := fun s hs =>
    lt_trans (ENNReal.coe_lt_coe.2 hs) ht₀
  exact Sec5.Aux22Strip.not_isForwardSol_of_tendsto_gap hW'c ht₀pos
    (fun t ht => hW'w t (ht.le.trans h02.le)) (hwc.mono hsub) (hvc.mono hsub)
    (fun t ht => hveq t (hsub ht)) hlim hu

/-! ### The coincident case -/

section Coincident

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- Right force coordinates from the same initial position coincide. -/
theorem vR_eq_of_xR_eq {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {i j : Fin nR} (hx : xR i = xR j) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : vR i t = vR j t := by
  rcases le_total i j with hij | hji
  · have h1 := hp.vR_sub_vR_le ht hij
    have h2 := hp.monotone_vR ht hij
    linarith
  · have h1 := hp.vR_sub_vR_le ht hji
    have h2 := hp.monotone_vR ht hji
    linarith

theorem sum_refWeightR_none (k : Fin nR) (S : ℝ) : ∑ j, GB7a.refWeightR k none S j = S := by
  simp [GB7a.refWeightR]

/-- **The coincident case along one path.** If every right mark sits at `x₊ = xR k > 0` and the outer right coordinate
meets the driver before the lifetime, GB7a's comparison picture (`S = Σ ρR`) holds at some rational time: just before
the first meeting time `T` every left coordinate is at distance more than `x₊/2` from the driver, and the right part of
the change vanishes. -/
theorem exists_rightCmp_of_meet {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hp : Sec2.IsForcePath xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    (hL0 : ∀ i, xL i ≤ 0) {k : Fin nR} (hxk : 0 < xR k) (hco : ∀ j, xR j = xR k) {S : ℝ}
    (hS : ∑ j, ρR j = S) {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ ω) (hmeet : ¬ W t₀ ω < VR k t₀ ω) :
    ∃ q : ℚ, GB7a.RightCmp ρL ρR W VL VR ζ k none S (q : ℝ).toNNReal ω := by
  set g : ℝ≥0 → ℝ := fun t => VR k t ω - W t ω with hg
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hgc : ContinuousOn g {s | (s : ℝ≥0∞) < ζ ω} := (hp.continuousOn_vR k).sub hp.continuousOn_w
  have hIcc : Set.Icc 0 t₀ ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := fun s hs =>
    (ENNReal.coe_le_coe.2 hs.2).trans_lt ht₀
  set K : Set ℝ≥0 := Set.Icc 0 t₀ ∩ g ⁻¹' Set.Iic 0 with hK
  have hKc : IsClosed K := (hgc.mono hIcc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have ht₀K : t₀ ∈ K := ⟨⟨zero_le, le_rfl⟩, by
    simp only [Set.mem_preimage, Set.mem_Iic, hg]
    linarith [not_lt.1 hmeet]⟩
  set T : ℝ≥0 := sInf K with hTdef
  have hTK : T ∈ K := hKc.csInf_mem ⟨t₀, ht₀K⟩ (OrderBot.bddBelow K)
  have hTt₀ : T ≤ t₀ := hTK.1.2
  have hTζ : (T : ℝ≥0∞) < ζ ω := (ENNReal.coe_le_coe.2 hTt₀).trans_lt ht₀
  have hmeetT : VR k T ω = W T ω := by
    have h1 : g T ≤ 0 := hTK.2
    have h2 := hp.w_le_vR hTζ k
    simp only [hg] at h1
    linarith
  have hbefore : ∀ t, t < T → W t ω < VR k t ω := fun t htT => by
    by_contra h
    have htK : t ∈ K := ⟨⟨zero_le, htT.le.trans hTt₀⟩, by
      simp only [Set.mem_preimage, Set.mem_Iic, hg]
      linarith [not_lt.1 h]⟩
    exact absurd (csInf_le (OrderBot.bddBelow K) htK) (not_le.2 htT)
  have hT0 : 0 < T := by
    refine pos_iff_ne_zero.2 fun h => ?_
    have h1 := hmeetT
    rw [h, hp.vR_zero k, hp.w_zero] at h1
    linarith
  -- the left gaps at `T`, and near `T`
  have hleftT : ∀ i, xR k ≤ W T ω - VL i T ω := fun i => by
    have h1 := hp.xR_le_vR hTζ k
    have h2 := hp.vL_le_xL hTζ i
    have h3 := hL0 i
    linarith
  have hev : ∀ᶠ t in 𝓝 T, ∀ i, xR k / 2 < W t ω - VL i t ω := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun t => W t ω - VL i t ω) T :=
      (hp.continuousOn_w.continuousAt (hopen.mem_nhds hTζ)).sub
        ((hp.continuousOn_vL i).continuousAt (hopen.mem_nhds hTζ))
    exact hc.eventually (lt_mem_nhds (by linarith [hleftT i]))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hmax : max ((T : ℝ) - ε) 0 < T := max_lt (sub_lt_self _ hε) (NNReal.coe_pos.2 hT0)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hmax
  have hq0 : (0 : ℝ) ≤ q := (le_max_right _ _).trans hq1.le
  set q' : ℝ≥0 := (q : ℝ).toNNReal with hq'
  have hq'c : (q' : ℝ) = q := Real.coe_toNNReal _ hq0
  have hq'T : q' < T := by rw [← NNReal.coe_lt_coe, hq'c]; exact hq2
  -- on `[q', T)`: the left gaps exceed `x₊/2`, the right coordinates are strictly right of the driver
  have hnear : ∀ t : ℝ≥0, q' ≤ t → t < T → ∀ i, xR k / 2 < W t ω - VL i t ω := fun t hqt htT => by
    refine hball ?_
    rw [NNReal.dist_eq, abs_of_neg (sub_neg.2 (NNReal.coe_lt_coe.2 htT))]
    have h1 : (q' : ℝ) ≤ t := NNReal.coe_le_coe.2 hqt
    have h2 := (le_max_left ((T : ℝ) - ε) 0).trans_lt hq1
    linarith
  have hζt : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ ω := fun t htT =>
    (ENNReal.coe_lt_coe.2 htT).trans hTζ
  have hright : ∀ t : ℝ≥0, t < T → ∀ j, W t ω < VR j t ω := fun t htT j => by
    rw [show VR j t ω = VR k t ω from vR_eq_of_xR_eq hp (hco j) (hζt t htT)]
    exact hbefore t htT
  -- the energy bound: the right part of the change vanishes
  set M : ℝ := ∑ i, |ρL i| / (xR k / 2) with hM
  have hpt : ∀ t : ℝ≥0, q' ≤ t → t < T →
      ‖((∑ i, -ρL i / (W t ω - VL i t ω)) +
        ∑ j, (GB7a.refWeightR k none S j - ρR j) / (W t ω - VR j t ω)) ^ 2‖ ≤ M ^ 2 := by
    intro t hqt htT
    have hR0 : ∑ j, (GB7a.refWeightR k none S j - ρR j) / (W t ω - VR j t ω) = 0 := by
      have he : ∀ j, (GB7a.refWeightR k none S j - ρR j) / (W t ω - VR j t ω) =
          (GB7a.refWeightR k none S j - ρR j) / (W t ω - VR k t ω) := fun j => by
        rw [vR_eq_of_xR_eq hp (hco j) (hζt t htT)]
      rw [Finset.sum_congr rfl fun j _ => he j, ← Finset.sum_div, Finset.sum_sub_distrib,
        sum_refWeightR_none, hS, sub_self, zero_div]
    have hL : |∑ i, -ρL i / (W t ω - VL i t ω)| ≤ M := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      have hpos := hnear t hqt htT i
      have hx2 : 0 < xR k / 2 := by linarith
      rw [abs_div, abs_neg, abs_of_pos (hx2.trans hpos)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hx2 hpos.le
    rw [hR0, add_zero, Real.norm_eq_abs, abs_pow, sq_abs]
    have h0 : 0 ≤ |∑ i, -ρL i / (W t ω - VL i t ω)| := abs_nonneg _
    have := pow_le_pow_left₀ h0 hL 2
    rwa [sq_abs] at this
  refine ⟨q, T, hq'T, hTζ.le, fun t hqt htT => ⟨fun i _ => ?_, fun j _ => (hright t htT j).ne⟩,
    ⟨M ^ 2 * T, fun t hqt htT => ?_⟩, ?_⟩
  · exact (sub_pos.1 ((by linarith : (0 : ℝ) < xR k / 2).trans (hnear t hqt htT i))).ne'
  · have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (q' : ℝ)) (b := (t : ℝ))
      (C := M ^ 2) (f := fun s : ℝ => ((∑ i, -ρL i / (W s.toNNReal ω - VL i s.toNNReal ω)) +
        ∑ j, (GB7a.refWeightR k none S j - ρR j) / (W s.toNNReal ω - VR j s.toNNReal ω)) ^ 2) (fun s hs => by
      have hqt' : (q' : ℝ) ≤ t := NNReal.coe_le_coe.2 hqt
      rw [Set.uIoc_of_le hqt'] at hs
      have hs0 : 0 ≤ s := (NNReal.coe_nonneg q').trans hs.1.le
      refine hpt s.toNNReal ?_ ?_
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hs.1.le
      · refine lt_of_le_of_lt ?_ htT
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hs.2)
    have hlen : |(t : ℝ) - q'| ≤ T := by
      rw [abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hqt))]
      have := NNReal.coe_le_coe.2 htT.le
      linarith [NNReal.coe_nonneg q']
    calc _ ≤ ‖∫ s in (q' : ℝ)..t, ((∑ i, -ρL i / (W s.toNNReal ω - VL i s.toNNReal ω)) +
            ∑ j, (GB7a.refWeightR k none S j - ρR j) / (W s.toNNReal ω - VR j s.toNNReal ω)) ^ 2‖ :=
          Real.le_norm_self _
      _ ≤ M ^ 2 * |(t : ℝ) - q'| := hb
      _ ≤ M ^ 2 * T := mul_le_mul_of_nonneg_left hlen (sq_nonneg _)
  · have hc : ContinuousAt g T := hgc.continuousAt (hopen.mem_nhds hTζ)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio T))
    have hg0 : g T = 0 := by simp only [hg]; linarith
    rwa [hg0] at this

end Coincident

/-! ### Input 3 -/

/-- **Input 3 of GB8: no contact with `[x₊, ∞)`** (GB8 proof, p. 523: "Lemma GB7a protects the open right tail, and G12
protects its junction `x₊` because `c_κ > d_κ`"). For the GB8 word with a continuous trace through its lifetime, almost
surely the outermost right mark never meets the driver before the lifetime. -/
theorem rightNoContactStatement : RightNoContactStatement.{u} := by
  intro κ hκ hκ4 nL nR hnL hnR xL xR ρL ρR hF hxm hxp hsL hsR hpsL hpsR Ω mΩ P 𝓕 W VL VR B ζ hE htr
  set k : Fin nR := ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ with hk
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hlast : ∀ j, xR j ≤ xR k := fun j => hF.2.2.1 (Fin.le_iff_val_le_val.2 (by simp only [hk]; omega))
  have hfilt : ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i = κ / 2 - 2 := by
    rw [Finset.filter_true_of_mem (fun i _ => hlast i)]
    exact hsR
  by_cases hex : ∃ j, xR j < xR k
  · -- a right mark strictly below `x₊`: Lemma GB7a and Lemma G12
    classical
    set η : Ω → ℝ≥0 → ℂ := fun ω => if h : ∃ γ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ then h.choose
      else fun _ => 0 with hηdef
    have hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω) := by
      filter_upwards [htr] with ω hω
      simp only [hηdef, dite_eq_left hω]
      exact hω.choose_spec
    have hG12 := Supp7.G12Low.ae_trace_ne_right_of_exists hκ hκ4 hF hE hη hxp hex
      (by rw [hfilt]; linarith)
    have hGB : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω →
        ∀ y ∈ Set.Ioo (xR k) (xR k + n + 1), η ω t ≠ y := fun n =>
      GB7a.gb7aEvol_right GB7a.gb7aCmpInput hκ hκ4 hF hE hη (k := k) (by linarith [n.cast_nonneg (α := ℝ)])
        (fun j hj => absurd (hlast j) (not_le.2 hj)) (by rw [hfilt])
    filter_upwards [hη, hG12, ae_all_iff.2 hGB, hE.ae_isIntegratedSLEPath] with ω hηω hg hgb hp t ht
    have hpf := hp.isForcePath
    refine w_lt_vR_of_trace_avoid hxp hpf.continuousOn_w hpf.w_zero (hpf.continuousOn_vR k)
      (fun t ht => hpf.vR_eq ht k) (fun t ht => hpf.w_le_vR ht k) hηω (fun s hs y hy => ?_) ht
    rcases hy.lt_or_eq with hy | hy
    · obtain ⟨n, hn⟩ := exists_nat_gt (y - xR k)
      exact hgb n s hs.le y ⟨hy, by linarith⟩
    · rw [← hy]
      exact hg s hs.le
  · -- every right mark at `x₊`: the comparison picture of GB7a
    have hco : ∀ j, xR j = xR k := fun j => le_antisymm (hlast j) (not_lt.1 fun h => hex ⟨j, h⟩)
    have hnull : P (⋃ q : ℚ, {ω | GB7a.RightCmp ρL ρR W VL VR ζ k none (κ / 2 - 2) (q : ℝ).toNNReal ω}) = 0 :=
      measure_iUnion_null fun q => GB7a.measure_rightCmp_eq_zero hκ hκ4.le hE (by simp) le_rfl _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull, hE.ae_isIntegratedSLEPath] with ω hω hp t ht
    by_contra hcon
    obtain ⟨q, hq⟩ := exists_rightCmp_of_meet hp.isForcePath hF.2.1 hxp hco hsR ht hcon
    exact hω (Set.mem_iUnion.2 ⟨q, hq⟩)

end GB8

end Supp8

end InteractingSLE
