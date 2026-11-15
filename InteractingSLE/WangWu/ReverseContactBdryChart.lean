/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactBdry
import InteractingSLE.WangWu.Cor48TwoSlit
import InteractingSLE.WangWu.Prop418RangeGlue
import InteractingSLE.WangWu.ReverseContactLocal

/-!
# The reversed-slit chart and the image of the forward slit

Packet PROVE-WW-B14 (the deterministic half of the contact step's N3). Wang–Wu
(`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of Proposition 4.18 (text dump
L1624–1629: "In the remaining slit domain, the two boundary paths from the original start to `β(s)` have values at
most `−λ` on the left and at least `λ` on the right. […] Map this domain to `H`, taking the start to `0` and `β(s)` to
`∞`. Before contact, the simple forward trace has continuous driving in this domain.").

For a continuous driver `W` with `W(0) = 0` and `s ≥ 0`, with hull `K = K_s` and `R(z) = −1/z`:

* `revChart W s = R ∘ f_s ∘ R` maps `ℍ \ R(K)` conformally onto `ℍ` (`f_s = g_s − W_s` centred), with inverse
  `revChartInv W s = R ∘ F_s ∘ R` (PROVE-WW-B11's chart of the reversed slit). It fixes `0` (`f_s(w) − w` is bounded),
  and sends the tip `R(β(s))` to `∞`.
* **`exists_imageTrace`**: if `α` is a simple proper trace with `α((0, t]) ∩ R(K) = ∅`, the image `Ψ ∘ α` on `[0, t]`
  is a Loewner trace after capacity parametrization: there are a continuous driver `W̃`, a clock `σ` and a simple proper
  Loewner trace `η̃` of the driver frozen after `σ(t)` with `η̃(σ(u)) = Ψ(α(u))`, and `K̃_{σ(t)} = Ψ(α((0, t]))`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.WangWu

/-! ### The reversed-slit chart -/

section Chart

variable {W : ℝ → ℝ} {s : ℝ}

/-- The reversed-slit chart `Ψ = R ∘ f_s ∘ R` of `ℍ \ R(K_s)`. -/
def revChart (W : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℂ := negInv (fwdMap W s (negInv z))

/-- Its inverse `Ψ⁻¹ = R ∘ F_s ∘ R`. -/
def revChartInv (W : ℝ → ℝ) (s : ℝ) (ζ : ℂ) : ℂ := negInv (fwdMapInv W s (negInv ζ))

theorem negInv_notMem_fwdHull {K : Set ℂ} {z : ℂ} (hz : z ∈ H \ negInv '' K) : negInv z ∈ H \ K :=
  ⟨negInv_mem_H hz.1, fun h => hz.2 ⟨negInv z, h, negInv_negInv' z⟩⟩

theorem isConformalBijection_revChartInv (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) :
    IsConformalBijection (revChartInv W s) H (H \ negInv '' fwdHull W s) :=
  isConformalBijection_negInv_fwdMapInv_negInv hW hW0 hs

theorem revChartInv_mem (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) {ζ : ℂ} (hζ : ζ ∈ H) :
    revChartInv W s ζ ∈ H \ negInv '' fwdHull W s :=
  (isConformalBijection_revChartInv hW hW0 hs).2.mapsTo hζ

theorem revChart_mem_H (hW : Continuous W) (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ H \ negInv '' fwdHull W s) :
    revChart W s z ∈ H :=
  negInv_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (negInv_notMem_fwdHull hz))

theorem revChart_revChartInv (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) {ζ : ℂ} (hζ : ζ ∈ H) :
    revChart W s (revChartInv W s ζ) = ζ := by
  rw [revChart, revChartInv, negInv_negInv',
    QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hs (negInv_mem_H hζ), negInv_negInv']

theorem revChartInv_revChart (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ H \ negInv '' fwdHull W s) : revChartInv W s (revChart W s z) = z := by
  rw [revChart, revChartInv, negInv_negInv',
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs (negInv_notMem_fwdHull hz), negInv_negInv']

theorem injOn_revChart (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) :
    InjOn (revChart W s) (H \ negInv '' fwdHull W s) := fun z hz z' hz' e => by
  rw [← revChartInv_revChart hW hW0 hs hz, e, revChartInv_revChart hW hW0 hs hz']

theorem isOpen_H_diff_negInv_fwdHull (hW : Continuous W) (hs : 0 ≤ s) :
    IsOpen (H \ negInv '' fwdHull W s) := by
  rw [H_diff_image_negInv]
  exact isOpen_image_negInv (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs) sdiff_subset

theorem continuousOn_revChart (hW : Continuous W) (hs : 0 ≤ s) :
    ContinuousOn (revChart W s) (H \ negInv '' fwdHull W s) := by
  intro z hz
  have h1 : z ≠ 0 := fun h => by
    have := hz.1; rw [h] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
  have hw := negInv_notMem_fwdHull hz
  have h2 : ContinuousAt (fwdMap W s) (negInv z) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).continuousOn.continuousAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs).mem_nhds hw)
  have h3 : fwdMap W s (negInv z) ≠ 0 := fun h => by
    have := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hw
    rw [h] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
  have h4 : ContinuousAt (fun z => fwdMap W s (negInv z)) z := h2.comp (continuousAt_negInv h1)
  exact (ContinuousAt.comp (g := negInv) (f := fun z => fwdMap W s (negInv z)) (x := z)
    (continuousAt_negInv h3) h4).continuousWithinAt

theorem continuousOn_revChartInv (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) :
    ContinuousOn (revChartInv W s) H :=
  fun ζ hζ => ((isConformalBijection_revChartInv hW hW0 hs).1 ζ hζ).continuousWithinAt

/-- `f_s` moves points of `ℍ \ K_s` by a bounded amount. -/
theorem exists_norm_fwdMap_sub_le (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) :
    ∃ C, 0 ≤ C ∧ ∀ w ∈ H \ fwdHull W s, ‖fwdMap W s w - w‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hs
  refine ⟨max C 0, le_max_right _ _, fun w hw => ?_⟩
  have hfw := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hw
  have h := hC _ hfw
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs hw, norm_sub_rev] at h
  exact h.trans (le_max_left _ _)

/-- **`Ψ` fixes `0`**: `Ψ(z) → 0` as `z → 0` in `ℍ \ R(K_s)`. -/
theorem tendsto_revChart_zero (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) :
    Tendsto (revChart W s) (𝓝[H \ negInv '' fwdHull W s] 0) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fwdMap_sub_le hW hW0 hs
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨1 / (C + 1 / ε), by positivity, fun {z} hz hzd => ?_⟩
  rw [dist_zero_right] at hzd ⊢
  have hz0 : z ≠ 0 := fun h => by
    have := hz.1; rw [h] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hw := negInv_notMem_fwdHull hz
  have h1 := hC _ hw
  have hnw : ‖negInv z‖ = ‖z‖⁻¹ := by rw [negInv, norm_neg, norm_inv]
  have h2 : ‖z‖⁻¹ - C ≤ ‖fwdMap W s (negInv z)‖ := by
    have := norm_sub_norm_le (negInv z) (negInv z - fwdMap W s (negInv z))
    rw [sub_sub_cancel, norm_sub_rev] at this
    rw [← hnw]; linarith
  have h3 : C + 1 / ε < ‖z‖⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hzpos]
    rwa [one_div] at hzd
  have h4 : 1 / ε < ‖fwdMap W s (negInv z)‖ := by linarith
  rw [revChart, negInv, norm_neg, norm_inv]
  calc ‖fwdMap W s (negInv z)‖⁻¹ < (1 / ε)⁻¹ := inv_strictAnti₀ (by positivity) h4
    _ = ε := by rw [one_div, inv_inv]

end Chart

/-! ### The forward slit in the chart of the reversed slit -/

section Image

variable {Wα Wβ : ℝ → ℝ} {α : ℝ → ℂ} {s t : ℝ}

/-- A curve continuous on `[0, ∞)` that avoids a closed set `G` on `[0, t]` avoids it on some longer `[0, S]`. -/
theorem exists_gt_forall_notMem {G : Set ℂ} (hG : IsClosed G) (hc : ContinuousOn α (Ici 0))
    (h : ∀ u ∈ Icc 0 t, α u ∉ G) : ∃ S, t < S ∧ ∀ u ∈ Icc 0 S, α u ∉ G := by
  set F := Icc (0 : ℝ) (t + 1) ∩ α ⁻¹' G with hF
  have hFc : IsClosed F := (hc.mono Icc_subset_Ici_self).preimage_isClosed_of_isClosed isClosed_Icc hG
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · refine ⟨t + 1, by linarith, fun u hu hG' => ?_⟩
    have : u ∈ F := ⟨hu, hG'⟩
    rw [hFe] at this; exact this
  · have hbdd : BddBelow F := ⟨0, fun u hu => hu.1.1⟩
    have hm := hFc.csInf_mem hFne hbdd
    have hmt : t < sInf F := by
      by_contra hle
      push Not at hle
      exact h _ ⟨hm.1.1, hle⟩ hm.2
    refine ⟨(t + sInf F) / 2, by linarith, fun u hu hG' => ?_⟩
    have huF : u ∈ F := ⟨⟨hu.1, by linarith [hu.2, hm.1.2]⟩, hG'⟩
    have := csInf_le hbdd huF
    linarith [hu.2]

/-- **The forward slit in the chart of the reversed slit is a simple Loewner trace** (Wang–Wu, proof of Proposition
4.18: "Before contact, the simple forward trace has continuous driving in this domain"). Let `α` be a simple proper
Loewner trace of `Wα`, `t > 0`, and let `G = R(K^β_s)` be closed and disjoint from `α((0, t])`. Then there are a
continuous driver `W̃` (`W̃(0) = 0`), a time `T > 0` and a simple proper Loewner trace `η̃` of `W̃` with
`K̃_T = Ψ(α((0, t]))` and `η̃(T) = Ψ(α(t))`, where `Ψ = revChart Wβ s`. -/
theorem exists_imageTrace (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (hWβ : Continuous Wβ)
    (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hG : IsClosed (negInv '' fwdHull Wβ s)) (ht : 0 < t)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s)) :
    ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ T : ℝ, 0 < T ∧ ∃ η' : ℝ → ℂ, IsLoewnerTrace W' η' ∧
      IsProperArc η' ∧ fwdHull W' T = revChart Wβ s '' fwdHull Wα t ∧ η' T = revChart Wβ s (α t) := by
  set G := negInv '' fwdHull Wβ s with hGdef
  have hA : fwdHull Wα t = α '' Ioc 0 t := fwdHull_eq_image_Ioc hα hαp ht.le
  have hαG : ∀ u ∈ Icc 0 t, α u ∉ G := by
    intro u hu hu'
    rcases hu.1.eq_or_lt with h0 | hpos
    · have hGH : G ⊆ H := fun z ⟨w, hw, e⟩ => e ▸ negInv_mem_H hw.1
      have := hGH hu'
      rw [← h0, hαp.zero] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · exact Set.disjoint_left.1 hdisj (by rw [hA]; exact ⟨u, ⟨hpos, hu.2⟩, rfl⟩) hu'
  obtain ⟨S, htS, hS⟩ := exists_gt_forall_notMem hG hαp.cont hαG
  have hmem : ∀ u ∈ Ioc 0 S, α u ∈ H \ G := fun u hu => ⟨hαp.mem_H u hu.1, hS u ⟨hu.1.le, hu.2⟩⟩
  set γ : ℝ → ℂ := fun u => if u ≤ 0 then 0 else revChart Wβ s (α u) with hγ
  have hγpos : ∀ u, 0 < u → γ u = revChart Wβ s (α u) := fun u hu => by
    simp only [hγ, not_le.2 hu, ↓reduceIte]
  have hγ0 : γ 0 = 0 := by simp [hγ]
  have hγH : ∀ u ∈ Ioc 0 S, γ u ∈ H := fun u hu => by
    rw [hγpos u hu.1]; exact revChart_mem_H hWβ hs (hmem u hu)
  have hγc : ContinuousOn γ (Icc 0 S) := by
    intro u hu
    rcases hu.1.eq_or_lt with h0 | hpos
    · rw [← h0, Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁, hR⟩ := Metric.tendsto_nhdsWithin_nhds.1 (tendsto_revChart_zero hWβ hWβ0 hs) ε hε
      have hα0 : ContinuousWithinAt α (Ici 0) 0 := hαp.cont 0 self_mem_Ici
      obtain ⟨δ₂, hδ₂, hαδ⟩ := Metric.continuousWithinAt_iff.1 hα0 δ₁ hδ₁
      refine ⟨δ₂, hδ₂, fun {v} hv hvd => ?_⟩
      rw [hγ0, dist_zero_right]
      rcases hv.1.eq_or_lt with hv0 | hvpos
      · rw [← hv0, hγ0, norm_zero]; exact hε
      · rw [hγpos v hvpos]
        have h1 := hαδ (mem_Ici.2 hv.1) hvd
        rw [hαp.zero] at h1
        have h2 := hR (hmem v ⟨hvpos, hv.2⟩) h1
        rwa [dist_zero_right] at h2
    · have hcα : ContinuousAt α u := hαp.cont.continuousAt (Ici_mem_nhds hpos)
      have hcR : ContinuousAt (revChart Wβ s) (α u) :=
        (continuousOn_revChart hWβ hs).continuousAt
          ((isOpen_H_diff_negInv_fwdHull hWβ hs).mem_nhds (hmem u ⟨hpos, hu.2⟩))
      have hcA : ContinuousAt (fun v => revChart Wβ s (α v)) u := hcR.comp hcα
      refine (hcA.congr ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds hpos] with v hv
      exact (hγpos v hv).symm
  have hγi : InjOn γ (Icc 0 S) := by
    intro u hu v hv e
    rcases hu.1.eq_or_lt with hu0 | hupos <;> rcases hv.1.eq_or_lt with hv0 | hvpos
    · rw [← hu0, ← hv0]
    · exfalso
      have := hγH v ⟨hvpos, hv.2⟩
      rw [← e, ← hu0, hγ0] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · exfalso
      have := hγH u ⟨hupos, hu.2⟩
      rw [e, ← hv0, hγ0] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · rw [hγpos u hupos, hγpos v hvpos] at e
      have e2 := injOn_revChart hWβ hWβ0 hs (hmem u ⟨hupos, hu.2⟩) (hmem v ⟨hvpos, hv.2⟩) e
      exact hαp.inj (mem_Ici.2 hu.1) (mem_Ici.2 hv.1) e2
  have hS0 : 0 < S := ht.trans htS
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, -, -, η, hη, hηp, hηγ, hK⟩ :=
    exists_trace_of_simple hS0 hγc hγi hγ0 hγH ⟨ht, htS⟩
  have hσt : 0 < σ t := by
    have := hσm ⟨le_rfl, hS0.le⟩ ⟨ht.le, htS.le⟩ ht
    rwa [hσ0] at this
  refine ⟨_, YuanCorollary13.continuous_extDrive hW, YuanCorollary13.extDrive_zero hW0 hσt.le, σ t, hσt,
    η, hη, hηp, ?_, ?_⟩
  · rw [hK, hA, image_image]
    exact image_congr fun u hu => hγpos u hu.1
  · rw [hηγ t ⟨ht.le, le_rfl⟩, hγpos t ht]

end Image

/-! ### Real points: images off the slit interval, order, boundary data -/

section RealLine

open MeasureTheory MartChar.RealFlow

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {T : ℝ}

/-- A solution of QuantumZipper's centred flow from a positive real point is a positive real solution. -/
theorem isPosSol_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {y : ℝ} (hy : 0 < y) {v : ℝ → ℂ}
    (hv : QuantumZipper.IsForwardSol W (y : ℂ) T v) : IsPosSol W y T (fun s => (v s).re) := by
  refine ⟨Complex.continuous_re.comp_continuousOn hv.1, fun s hs => ⟨?_, ?_⟩⟩
  · show 0 < (v s).re
    rw [← fwdMap_eq_of_isForwardSol hW hv hs]
    exact re_fwdMap_pos hW hW0 hy hv hs
  · have h := congrArg Complex.re (hv.2 s hs).2
    have hint : (∫ r in (0 : ℝ)..s, 2 / v r) = ((∫ r in (0 : ℝ)..s, 2 / (v r).re : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      have him := im_eq_zero_of_isForwardSol_real hW hv ⟨hr.1, hr.2.trans hs.2⟩
      have hvr : v r = ((v r).re : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [hvr, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_re]
    rw [hint] at h
    simpa using h

/-- **Images of positive alive points lie right of the right force image**: `rightImg W 0 T − W T ≤ f_T(y)` for
`y > 0` alive on `[0, T]`. -/
theorem rightImg_sub_le_re_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) {y : ℝ} (hy : 0 < y)
    {v : ℝ → ℂ} (hv : QuantumZipper.IsForwardSol W (y : ℂ) T v) :
    rightImg W 0 T - W T ≤ (fwdMap W T y).re := by
  have hX := isPosSol_of_isForwardSol hW hW0 hy hv
  have hle := rightImg_le_gImg hW hT hy ⟨_, hX⟩
  rw [gImg, cflow_eq_of_isPosSol hW hX ⟨hT, le_rfl⟩] at hle
  rw [fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩]
  linarith

/-- **Images of negative alive points lie left of the left force image**: `f_T(y) ≤ −rightImg (−W) 0 T − W T` for
`y < 0` alive on `[0, T]`. -/
theorem re_fwdMap_le_neg_rightImg (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) {y : ℝ} (hy : y < 0)
    {v : ℝ → ℂ} (hv : QuantumZipper.IsForwardSol W (y : ℂ) T v) :
    (fwdMap W T y).re ≤ -rightImg (fun s => -W s) 0 T - W T := by
  obtain ⟨v', hv'⟩ := (exists_isForwardSol_neg_iff (W := W) (x := y) (T := T)).2 ⟨v, hv⟩
  have h := rightImg_sub_le_re_fwdMap (W := fun s => -W s) hW.neg (by simp [hW0]) hT (neg_pos.2 hy) hv'
  have e := fwdMap_neg_real hW hv ⟨hT, le_rfl⟩
  rw [e] at h
  simp only [neg_re] at h
  linarith

/-- **The real flow preserves order on each side of `0`.** -/
theorem re_fwdMap_lt_re_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) {y₁ y₂ : ℝ} (h12 : y₁ < y₂)
    (hsign : 0 < y₁ ∨ y₂ < 0) {v₁ v₂ : ℝ → ℂ} (hv₁ : QuantumZipper.IsForwardSol W (y₁ : ℂ) T v₁)
    (hv₂ : QuantumZipper.IsForwardSol W (y₂ : ℂ) T v₂) : (fwdMap W T y₁).re < (fwdMap W T y₂).re := by
  rcases hsign with hpos | hneg
  · rw [fwdMap_eq_of_isForwardSol hW hv₁ ⟨hT, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hv₂ ⟨hT, le_rfl⟩]
    exact re_lt_of_isForwardSol hW hW0 hpos h12 hv₁ hv₂ T ⟨hT, le_rfl⟩
  · have hu₁ : QuantumZipper.IsForwardSol (fun t => -W t) ((-y₁ : ℝ) : ℂ) T (fun t => -v₁ t) := by
      rw [Complex.ofReal_neg]; exact isForwardSol_neg_iff.2 hv₁
    have hu₂ : QuantumZipper.IsForwardSol (fun t => -W t) ((-y₂ : ℝ) : ℂ) T (fun t => -v₂ t) := by
      rw [Complex.ofReal_neg]; exact isForwardSol_neg_iff.2 hv₂
    have h := re_lt_of_isForwardSol (W := fun s => -W s) hW.neg (by simp [hW0]) (neg_pos.2 hneg)
      (neg_lt_neg h12) hu₂ hu₁ T ⟨hT, le_rfl⟩
    rw [fwdMap_eq_of_isForwardSol hW hv₁ ⟨hT, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hv₂ ⟨hT, le_rfl⟩]
    simp only [neg_re] at h
    linarith

/-- **A real point sent to a real point `r ≠ 0` is the image of `r`**: if `F̄_T(x) = r`, then `x = f_T(r)` (a real
number). -/
theorem eq_re_fwdMap_of_extendFrom_eq (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) (hT : 0 ≤ T) {x r : ℝ} (hr : r ≠ 0) (hF : extendFrom H (fwdMapInv W T) x = r) :
    x = (fwdMap W T r).re ∧ (fwdMap W T r).im = 0 := by
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη hγ hW hW0 hr hT
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have h := eq_of_extendFrom_eq_of_isForwardSol hW hW0 hT hv hη hxH hF
  rw [fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩, ← h]
  simp

end RealLine

/-! ### The boundary data of the one- and two-force words -/

section Data

theorem fbd_one_neg {ρL ρR vL vR ξ : ℝ} (hξ : ξ < 0) :
    forceBoundaryData 4 (fun _ : Fin 1 => ρL) (fun _ : Fin 1 => ρR) (fun _ => vL) (fun _ => vR) ξ =
      -(Real.pi / Real.sqrt 4) * (1 + if ξ < vL then ρL else 0) := by
  simp only [forceBoundaryData, hξ, ↓reduceIte]
  split_ifs with h <;> simp [h]

theorem fbd_one_nonneg {ρL ρR vL vR ξ : ℝ} (hξ : 0 ≤ ξ) :
    forceBoundaryData 4 (fun _ : Fin 1 => ρL) (fun _ : Fin 1 => ρR) (fun _ => vL) (fun _ => vR) ξ =
      (Real.pi / Real.sqrt 4) * (1 + if vR ≤ ξ then ρR else 0) := by
  simp only [forceBoundaryData, not_lt.2 hξ, ↓reduceIte]
  split_ifs with h <;> simp [h]

theorem fbd_two_neg {a₁ a₂ b₁ b₂ p₁ p₂ q₁ q₂ ξ : ℝ} (hξ : ξ < 0) :
    forceBoundaryData 4 ![a₁, a₂] ![b₁, b₂] ![p₁, p₂] ![q₁, q₂] ξ =
      -(Real.pi / Real.sqrt 4) * (1 + ((if ξ < p₁ then a₁ else 0) + if ξ < p₂ then a₂ else 0)) := by
  simp only [forceBoundaryData, hξ, ↓reduceIte, Finset.sum_filter, Fin.sum_univ_two]
  split_ifs <;> simp_all

theorem fbd_two_nonneg {a₁ a₂ b₁ b₂ p₁ p₂ q₁ q₂ ξ : ℝ} (hξ : 0 ≤ ξ) :
    forceBoundaryData 4 ![a₁, a₂] ![b₁, b₂] ![p₁, p₂] ![q₁, q₂] ξ =
      (Real.pi / Real.sqrt 4) * (1 + ((if q₁ ≤ ξ then b₁ else 0) + if q₂ ≤ ξ then b₂ else 0)) := by
  simp only [forceBoundaryData, not_lt.2 hξ, ↓reduceIte, Finset.sum_filter, Fin.sum_univ_two]
  split_ifs <;> simp_all

/-- **The data of the reversed slit match the data of the two-force word** (the arithmetic of Proposition 4.18's
"two boundary paths from the original start to `β(s)` have values at most `−λ` on the left and at least `λ` on the
right"): if a real point `ξ` of the reverse chart and a real point `x` of the image chart lie in corresponding
intervals, the reverse mean at `ξ` and the two-force mean at `x` have opposite boundary values. -/
theorem fbd_add_fbd_eq_zero {rL rR vL vR aL aR bL bR ξ x : ℝ}
    (hbaL : bL < aL) (haL : aL ≤ 0) (haR : 0 ≤ aR) (habR : aR < bR)
    (hξ0 : ξ ≠ 0) (hξL : ξ ≠ vL) (hξR : ξ ≠ vR)
    (hA : 0 < ξ → ξ < vR → x < bL) (hB : vR < ξ → bL < x ∧ x < aL)
    (hC : ξ < vL → aR < x ∧ x < bR) (hD : vL < ξ → ξ < 0 → bR < x) :
    forceBoundaryData 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (fun _ => vL) (fun _ => vR) ξ +
      forceBoundaryData 4 ![rL, -rL] ![rR, -rR] ![aL, bL] ![aR, bR] x = 0 := by
  rcases lt_or_gt_of_ne hξ0 with hneg | hpos
  · rcases lt_or_gt_of_ne hξL with hlt | hgt
    · obtain ⟨h1, h2⟩ := hC hlt
      rw [fbd_one_neg hneg, fbd_two_nonneg (by linarith)]
      simp only [hlt, show aR ≤ x from h1.le, show ¬ bR ≤ x from not_le.2 h2, ↓reduceIte]
      ring
    · have h1 := hD hgt hneg
      rw [fbd_one_neg hneg, fbd_two_nonneg (by linarith)]
      simp only [show ¬ ξ < vL from not_lt.2 hgt.le, show aR ≤ x by linarith, show bR ≤ x from h1.le,
        ↓reduceIte]
      ring
  · rcases lt_or_gt_of_ne hξR with hlt | hgt
    · have h1 := hA hpos hlt
      rw [fbd_one_nonneg hpos.le, fbd_two_neg (by linarith)]
      simp only [show ¬ vR ≤ ξ from not_le.2 hlt, show x < aL by linarith, show x < bL from h1, ↓reduceIte]
      ring
    · obtain ⟨h1, h2⟩ := hB hgt
      rw [fbd_one_nonneg hpos.le, fbd_two_neg (by linarith)]
      simp only [show vR ≤ ξ from hgt.le, show x < aL from h2, show ¬ x < bL from not_lt.2 h1.le,
        ↓reduceIte]
      ring

end Data

end InteractingSLE.WangWu
