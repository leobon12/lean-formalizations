/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinLand
import InteractingSLE.Spec.Supplement.SBLemmaS2
import InteractingSLE.Spec.Supplement.Q3RelBHLand

/-!
# SB2(1)'s free left collar

Packet PROVE-T14-SB2FIN. The field `collar` of `SB.Union.IsRelConfigJ` / `IsRelConfigJC` for SB2(1)'s relative chain
(SB2, p. 632: "The far-left original-real interval anchors the derivative logarithm at zero. The upper flow has a free
left collar, which joins that anchor"): left of the relative hull's left base `a_L` the joint parametrization lands at
real points, and some of them are untouched (off the closed retained set, off the closed physical filling, `≠ 0`).

* `exists_neg_of_lt_chartAL`: left of `a_L` the relative inverse lands at a negative real point;
* the physical landing is `g` of it, a real point `< L` (`SB.IsLeftEntryChart.exists_boundary_orient`: `g` inverts the
  boundary value `e` of the left entry chart, a bijection of `(−∞, L)` onto `(−∞, 0)`);
* it is off `closure (fill A)` (`SB.isFreeAt_of_lt`), and off the closed physical filling: a point of the physical
  filling near it has its chart image in the relative hull (`hullIn`), and the chart tends to `e(p₀)` = the relative
  landing, which is off the closed relative hull;
* **`collar_of_isSB2RelChain`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.SB.FinRel

open Sec7.Lemma71C
open WangWu (chartAL chartAR)
open MartChar.RealFlow

/-- **Left of `a_L` the relative inverse lands at a negative real point.** -/
theorem exists_neg_of_lt_chartAL {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {u : ℝ} (hu : 0 ≤ u) {x : ℝ} (hx : x < chartAL W u) :
    ∃ y : ℝ, 0 < y ∧ extendFrom H (fwdMapInv W u) (x : ℂ) = ((-y : ℝ) : ℂ) := by
  have hM : rightImg (fun s => -W s) 0 u < -x - W u := by rw [WangWu.chartAL] at hx; linarith
  obtain ⟨y, hy0, hal, hg⟩ := Restart.RetAux79.exists_alive_gImg_eq hW.neg hu hM
  have hv := WangWu.isForwardSol_neg_of_alive hW hal
  have hv' : QuantumZipper.IsForwardSol W ((-y : ℝ) : ℂ) u (fun s => -(cflow (fun s => -W s) y s : ℂ)) := by
    rw [Complex.ofReal_neg]; exact hv
  have hg' : -W u + cflow (fun s => -W s) y u = -x - W u := hg
  have hc : cflow (fun s => -W s) y u = -x := by linarith
  have h := Sec5.CrossRestart.extendFrom_eq_of_isForwardSol_real hη hW hW0 hu hv'
  simp only [hc, Complex.ofReal_neg, neg_neg] at h
  exact ⟨y, hy0, by rw [h, Complex.ofReal_neg]⟩

/-- The smallest real point of a compact set containing `0` is `≤ 0`, and every real point of the set is above it. -/
theorem realMin_le_of_mem {A : Set ℂ} (hA : IsCompact A) {y : ℝ} (hy : (y : ℂ) ∈ A) : realMin A ≤ y := by
  refine csInf_le ?_ hy
  obtain ⟨M, hM⟩ := hA.isBounded.exists_norm_le
  refine ⟨-M, fun z hz => ?_⟩
  have := hM _ hz
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  linarith [neg_abs_le z]

section Collar

variable {p : ℝ → ℂ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ : ℝ} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ}

/-- **SB2(1)'s free left collar** (the field `collar` of `IsRelConfigJ`/`IsRelConfigJC` with `Sb = ∅`, for the filled
retained set `fill A`, `A = p([0, 1])`, the chart inverse `c.inv`, the relative chain at the relative time `a s`, and
the physical filling `fill β'([0, t_L + s])`). -/
theorem collar_of_isSB2RelChain (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hch : IsSB2RelChain (p '' Icc 0 1) c β' γ tL S₀ Wr ηr) {s : ℝ} (hs : s ∈ Icc 0 S₀) :
    ∃ x₁ < chartAL Wr (capClock (fun r : ℝ => γ r.toNNReal) s),
      (∀ x ∈ Ioo x₁ (chartAR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)),
        Supp8.Q3Rel.IsGoodPt ∅ Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (x : ℂ)) ∧
      (∀ x ∈ Ioo x₁ (chartAL Wr (capClock (fun r : ℝ => γ r.toNNReal) s)),
        (extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ)).im = 0) ∧
      ∃ x₀ ∈ Ioo x₁ (chartAL Wr (capClock (fun r : ℝ => γ r.toNNReal) s)),
        extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x₀ : ℂ) ∉
          closure (fillH (p '' Icc 0 1)) ∧
        extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x₀ : ℂ) ∉
          closure (fillH (β' '' Icc 0 (tL + s.toNNReal))) ∧
        extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x₀ : ℂ) ≠ 0 := by
  obtain ⟨hWr, hWr0, hηr, -, -, -, hK⟩ := hch
  obtain ⟨hu, -, hKs, hIn, -⟩ := hK s hs
  set u := capClock (fun r : ℝ => γ r.toNNReal) s with hudef
  set A := p '' Icc 0 1 with hAdef
  set L := realMin A with hLdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have hL0 : L ≤ 0 := realMin_le_of_mem hAc ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hp0]; simp⟩
  obtain ⟨e, he, -, heg, hesurj⟩ := hc.exists_boundary_orient hp hp0 hgc hgi
  -- the landing left of `a_L`
  have hland : ∀ x < chartAL Wr u, ∃ x' < L, e x' = extendFrom H (fwdMapInv Wr u) (x : ℂ) ∧
      extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr u) (x : ℂ) = (x' : ℂ) := by
    intro x hx
    obtain ⟨y, hy0, hyF⟩ := exists_neg_of_lt_chartAL hηr hWr hWr0 hu hx
    obtain ⟨x', hx'L, hex'⟩ := hesurj (-y) (by linarith)
    refine ⟨x', hx'L, by rw [hex', hyF], ?_⟩
    rw [extendFrom_jointInv_eq hgc hgi hWr hWr0 hηr hu (show (0 : ℝ) ≤ ((x : ℂ)).im by simp), hyF, ← hex',
      (heg x' hx'L).2]
  refine ⟨chartAL Wr u - 1, by linarith, fun x _ b hb => absurd hb (Finset.notMem_empty b), fun x hx => ?_, ?_⟩
  · obtain ⟨x', -, -, hx'⟩ := hland x hx.2
    rw [hx']
    simp
  · refine ⟨chartAL Wr u - 1 / 2, ⟨by linarith, by linarith⟩, ?_⟩
    obtain ⟨x', hx'L, hex', hx'⟩ := hland (chartAL Wr u - 1 / 2) (by linarith)
    rw [hx']
    -- free for `A`
    have hfree : HalfPlaneSep.IsFreeAt A (x' : ℂ) :=
      SB.isFreeAt_of_lt hAc (fun y hy => realMin_le_of_mem hAc hy) hx'L
    obtain ⟨ε, hε, hball⟩ := hfree
    have hAcl : (x' : ℂ) ∉ closure (fillH A) := by
      intro hcl
      obtain ⟨z, hzF, hzb⟩ := Metric.mem_closure_iff.1 hcl ε hε
      have hz := hball ⟨mem_ball.2 (by rw [dist_comm]; exact hzb), hzF.1⟩
      exact hz.2 hzF
    refine ⟨hAcl, fun hcl => ?_, by
      intro h0
      have : x' = 0 := by exact_mod_cast h0
      linarith⟩
    -- off the closed physical filling: otherwise the relative landing would be in the closed relative hull
    have hF : extendFrom H (fwdMapInv Wr u) ((chartAL Wr u - 1 / 2 : ℝ) : ℂ) ∉ closure (fwdHull Wr u) :=
      Supp8.RelTrans.extendFrom_notMem_closure_of_lt_chartAL hηr hWr hWr0 hu (by linarith)
    apply hF
    rw [← hex']
    -- points of the physical filling near `x'`
    have hlim : Tendsto c.1 (𝓝[fillH (β' '' Icc 0 (tL + s.toNNReal))] (x' : ℂ)) (𝓝 (e x' : ℂ)) := by
      refine (he x' hx'L).mono_left (nhdsWithin_mono _ fun z hz => hz.1)
    have hne : (𝓝[fillH (β' '' Icc 0 (tL + s.toNNReal))] (x' : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    refine mem_closure_of_tendsto hlim ?_
    have hev : ∀ᶠ z in 𝓝[fillH (β' '' Icc 0 (tL + s.toNNReal))] (x' : ℂ), z ∈ ball (x' : ℂ) ε :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hε)
    filter_upwards [hev, self_mem_nhdsWithin] with z hzb hzF
    have hzA : z ∉ fillH A := (hball ⟨hzb, hzF.1⟩).2
    exact hIn z hzF hzA

end Collar

end InteractingSLE.Theorem14.SB.FinRel
