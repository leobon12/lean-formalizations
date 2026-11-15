/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMISrc
import InteractingSLE.Spec.Supplement.Aux61Cutoff

/-!
# Aux. lemma 61's comparison identity for a general cutoff field

Packet PROVE-L1-CMI, step (c) of `planning/handoffs/PROVE-G3SRC.md` §4.1 (the deterministic mean identity), Aux. 61
half. `GB7a.compFun_eq_zero` (PROVE-GB7A2) proves, under `GB7a.IdentHyp`, that the comparison function
`G_{ℍ∖K_s} v − argSum_s + argSum_0 − f` vanishes on `ℍ ∖ K_s`. PROVE-CFBARRIER2 built `IdentHyp` for its two-core
cutoff (`Sec5.GB7aAbove4.exists_markDrift_energy_le_seed`). Here the same construction for **any** cutoff field
`F : CMCut` that equals the arg sum on an open buffer `N ∋ 0` and is harmonic there, along a driver whose hull closure
lies in `N`:

* **`identHyp_of_cut`**: the hypotheses `GB7a.IdentHyp` for `v = 1_ℍ greenDensity F.f = −F.src`;
* **`compFun_eq_zero_of_cut`**: `argSum_s = G_{ℍ∖K_s}(1_ℍ gD F.f) + argSum_0 − F.f` on `ℍ ∖ K_s`, `0 < s ≤ t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Interval

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol greenH fwdMapInv)
open GB7a

variable {ι : Type*} [Fintype ι] {p c : ι → ℝ} {c₀ : ℝ}

/-- **`GB7a.IdentHyp` for a general cutoff field** (the construction of
`Sec5.GB7aAbove4.exists_markDrift_energy_le_seed`, with the two-core cutoff replaced by `F` and its buffer by `N`). -/
theorem identHyp_of_cut (F : CMCut) {N : Set ℂ} (hNo : IsOpen N) (h0N : (0 : ℂ) ∈ N)
    (hfN : ∀ z ∈ N, z ∈ H → F.f z = argSum0 p c c₀ z)
    (hΔN : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0)
    (hseed : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => 0 < p j), c j = 0)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t) {η : ℝ → ℂ}
    (hηc : ContinuousOn η (Icc 0 t)) (hfill : ∀ s ∈ Ioc (0 : ℝ) t, fwdHull W s = fillH (η '' Icc 0 s))
    (hKN : closure (fwdHull W t) ⊆ N) (hp : MarksAlive W p t) :
    ∃ Cv R m, IdentHyp W t η p c c₀ (H.indicator (QuantumZipper.K3.greenDensity F.f)) Cv R m F.f N := by
  classical
  set v : ℂ → ℝ := H.indicator (QuantumZipper.K3.greenDensity F.f) with hv
  have hvc : Continuous (QuantumZipper.K3.greenDensity F.f) := F.continuous_greenDensity
  have hvs : HasCompactSupport (QuantumZipper.K3.greenDensity F.f) := F.hasCompactSupport_greenDensity
  obtain ⟨Cv₀, hCv₀⟩ := hvs.exists_bound_of_continuous hvc
  set Cv := max Cv₀ 0 with hCv
  have hHm : MeasurableSet H := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hvb : ∀ z, |v z| ≤ Cv := fun z => by
    by_cases hz : z ∈ H
    · rw [hv, Set.indicator_of_mem hz, ← Real.norm_eq_abs]; exact (hCv₀ z).trans (le_max_left _ _)
    · rw [hv, Set.indicator_of_notMem hz, abs_zero]; exact le_max_right _ _
  have hvN : ∀ z, v z ≠ 0 → z ∉ N := fun z hz hzN => by
    apply hz
    by_cases hzH : z ∈ H
    · rw [hv, Set.indicator_of_mem hzH, hΔN z hzN]
    · rw [hv, Set.indicator_of_notMem hzH]
  have htsupN : Disjoint (tsupport (QuantumZipper.K3.greenDensity F.f)) N := by
    rw [Set.disjoint_right]
    intro z hzN hzt
    have hev : QuantumZipper.K3.greenDensity F.f =ᶠ[𝓝 z] 0 := by
      filter_upwards [hNo.mem_nhds hzN] with w hw
      rw [hΔN w hw, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.2 hev) hzt
  have hvH : ∀ z, v z ≠ 0 → z ∈ H := fun z hz => by
    by_contra hzH; exact hz (by rw [hv, Set.indicator_of_notMem hzH])
  have hvt : ∀ z, v z ≠ 0 → z ∈ tsupport (QuantumZipper.K3.greenDensity F.f) ∩ Hbar := fun z hz =>
    ⟨subset_tsupport _ fun h0 => hz (by rw [hv, Set.indicator_of_mem (hvH z hz), h0]),
      show (0 : ℝ) ≤ z.im from le_of_lt (hvH z hz)⟩
  obtain ⟨R, hR⟩ := (hvs.isCompact.isBounded).subset_closedBall 0
  have hsupR : ∀ z, v z ≠ 0 → ‖z‖ ≤ R := fun z hz => by
    have := hR (hvt z hz).1
    rwa [mem_closedBall, dist_zero_right] at this
  have halive : ∀ z ∈ tsupport (QuantumZipper.K3.greenDensity F.f) ∩ Hbar, ∃ u, IsForwardSol W z t u := by
    rintro z ⟨hzt, hzH⟩
    have hzN : z ∉ N := Set.disjoint_left.1 htsupN hzt
    rcases (show (0 : ℝ) ≤ z.im from hzH).lt_or_eq with hpos | hzero
    · exact Ito.exists_isForwardSol_of_mem ht.le ⟨hpos, fun hK => hzN (hKN (subset_closure hK))⟩
    · have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      have hz0 : z.re ≠ 0 := fun h => hzN (by rw [hzr, h, Complex.ofReal_zero]; exact h0N)
      have hzcl : z ∉ closure (fwdHull W t) := fun h => hzN (hKN h)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hzcl
      have hd : Disjoint (ball ((z.re : ℝ) : ℂ) r) (fwdHull W t) := by
        rw [← hzr]
        exact Set.disjoint_left.2 fun w hw hwK => hball hw (subset_closure hwK)
      obtain ⟨u, hu⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 hz0 ht.le hr hd
      exact ⟨u, by rw [hzr]; exact hu⟩
  obtain ⟨m, hm, hmfar⟩ := exists_far hW ht.le ((hvs.isCompact).inter_right
    (isClosed_le continuous_const Complex.continuous_im)) halive
  have hsrc : IsSrc W v t Cv R m :=
    { meas := hvc.measurable.indicator hHm
      bound := hvb
      m_pos := hm
      alive := fun z hz => ⟨hvH z hz, fun hK => hvN z hz (hKN (subset_closure hK))⟩
      norm_le := hsupR
      far := fun z hz u hu => hmfar z (hvt z hz) u hu }
  have hp0 : ∀ j, (p j : ℂ) ≠ 0 := fun j => by
    obtain ⟨u, hu⟩ := hp j
    exact ne_zero_of_isForwardSol hW0 ht.le hu
  exact ⟨Cv, R, m,
    { cont := hW
      zero := hW0
      t_pos := ht
      trace_cont := hηc
      fill := hfill
      marks := hp
      seed := hseed
      src := hsrc
      open_N := hNo
      hull_N := hKN
      zero_N := h0N
      src_N := hvN
      green := fun y _ => integral_greenH_mul_indicator_greenDensity (F.smooth.of_le (by simp)) F.compact F.odd y
      f_eq := fun y ⟨hyN, hyH⟩ => by
        have hy0 : y ≠ 0 := fun h => by
          have : (0 : ℝ) < y.im := hyH
          rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
        rw [hfN y hyN hyH, argSum0, argSum, fwdMap_zero_time hW hW0 hy0]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [fwdMap_zero_time hW hW0 (hp0 j)] }⟩

/-- **The comparison identity for a general cutoff field** (Aux. lemmas 61–62, `GB7a.compFun_eq_zero`):
`argSum_s(y) = G_{ℍ∖K_s}(1_ℍ gD F.f)(y) + argSum_0(y) − F.f(y)` for `y ∈ ℍ ∖ K_s`, `0 < s ≤ t`. -/
theorem compFun_eq_zero_of_cut (F : CMCut) {N : Set ℂ} (hNo : IsOpen N) (h0N : (0 : ℂ) ∈ N)
    (hfN : ∀ z ∈ N, z ∈ H → F.f z = argSum0 p c c₀ z)
    (hΔN : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0)
    (hseed : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => 0 < p j), c j = 0)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t) {η : ℝ → ℂ}
    (hηc : ContinuousOn η (Icc 0 t)) (hfill : ∀ s ∈ Ioc (0 : ℝ) t, fwdHull W s = fillH (η '' Icc 0 s))
    (hKN : closure (fwdHull W t) ⊆ N) (hp : MarksAlive W p t) {s : ℝ} (hs : s ∈ Ioc 0 t) {y : ℂ}
    (hy : y ∈ H \ fwdHull W s) :
    argSum W p c c₀ s y =
      greenPot W (H.indicator (QuantumZipper.K3.greenDensity F.f)) s y + argSum W p c c₀ 0 y - F.f y := by
  obtain ⟨Cv, R, m, hI⟩ := identHyp_of_cut F hNo h0N hfN hΔN hseed hW hW0 ht hηc hfill hKN hp
  have h := compFun_eq_zero hI hs hy
  rw [compFun] at h
  linarith

end FlowStopIdentCMI

end Restart

end InteractingSLE
