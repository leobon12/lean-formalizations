import InteractingSLE.Foundations.Loewner.ConformalImage
import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# Clearance of a fixed obstacle from the driver of a Loewner chain

Packet PROVE-GEO-LOC2, step (1) (`planning/handoffs/PROVE-GEO-LOC.md`, "What remains" (1)).
Let `W` be continuous with `W 0 = 0`, `K_t = fwdHull W t`, `g_t = f_t + W_t`, and let `A` be a
bounded set with `closure A ∩ closure K_T = ∅` and `0 ∉ closure A`. Then the centered images of
`A` keep a uniform distance from the driver:

`exists_clearance`: `∃ ρ > 0, ∀ t ∈ [0, T], ∀ a ∈ A, ρ ≤ |f_t(a)|`.

## Proof

Near a point of `closure A` in `ℍ` this is the stability of the flow (`RealPoints`). Near a real
point `y ∉ closure K_T` the maps `g_t`, `t ≤ T`, extend by reflection across a fixed disc
`B(y, r)`, are `48`-Lipschitz there, and have a boundary value `G_t(y)` that is continuous in `t`.
The key claim is `G_t(y) ≠ W_t` for `t ∈ [0, T]` (the real point `y` is not swallowed by time `T`):

* for `t < T`, `W_t` is in the closure of `g_t(K_T \ K_t)` (local growth), while the open mapping
  theorem puts a half-disc around `G_t(y)` inside `g_t(B(y, r/2) ∩ ℍ)`, which misses
  `g_t(K_T \ K_t)` by injectivity;
* at `t = T`, if `G_T(y) = W_T`, the open mapping theorem gives a nearby real point `y'` with
  `G_T(y') − W_T` of the sign opposite to `y' − W_0 = G_0(y') − W_0`, so by the intermediate value
  theorem `G_τ(y') = W_τ` for some `τ < T`, which the first case excludes.

No ODE for real points is needed. This is the step that Lawler's proof of [Law05] Proposition
4.43 calls "by compactness".
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace ConformalImageFull

open ConformalImage

variable {W : ℝ → ℝ}

/-- The boundary value at the real point `y` of the uncentered Loewner map `g_t = f_t + W_t`. -/
def bdryVal (W : ℝ → ℝ) (y t : ℝ) : ℂ := limUnder (𝓝[H] (y : ℂ)) (gmap W t)

theorem gmap_isMapOut (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsMapOut (QuantumZipper.fwdHull W t) (gmap W t) := isMapOut_fwdMap hW hW0 ht

theorem disjoint_ball_of_le {y r s t : ℝ}
    (hd : Disjoint (ball (y : ℂ) r) (QuantumZipper.fwdHull W t))
    (hst : s ≤ t) : Disjoint (ball (y : ℂ) r) (QuantumZipper.fwdHull W s) :=
  hd.mono_right ((QuantumZipper.fwdHull_mono (W := W)).1 hst)

/-- The boundary value is real and is the limit of `g_t` from `ℍ`. -/
theorem bdryVal_spec (hW : Continuous W) (hW0 : W 0 = 0) {y r t : ℝ} (ht : 0 ≤ t) (hr : 0 < r)
    (hd : Disjoint (ball (y : ℂ) r) (QuantumZipper.fwdHull W t)) :
    (bdryVal W y t).im = 0 ∧ Tendsto (gmap W t) (𝓝[H] (y : ℂ)) (𝓝 (bdryVal W y t)) :=
  (gmap_isMapOut hW hW0 ht).tendsto_limUnder_of_disjoint (isHPHull_fwdHull hW ht) hr hd

/-- `g_t` is `48`-Lipschitz towards its boundary value. -/
theorem norm_gmap_sub_bdryVal_le (hW : Continuous W) (hW0 : W 0 = 0) {y r t : ℝ} (ht : 0 ≤ t)
    (hd : Disjoint (ball (y : ℂ) r) (QuantumZipper.fwdHull W t)) {ζ : ℂ}
    (hζ : ζ ∈ ball (y : ℂ) (r / 2) ∩ H) :
    ‖gmap W t ζ - bdryVal W y t‖ ≤ 48 * ‖ζ - y‖ :=
  (gmap_isMapOut hW hW0 ht).norm_sub_limUnder_le (isHPHull_fwdHull hW ht) hd hζ

/-- At time `0` the boundary value is the point itself. -/
theorem bdryVal_zero (hW : Continuous W) (hW0 : W 0 = 0) (y : ℝ) : bdryVal W y 0 = y := by
  have h0 : QuantumZipper.fwdHull W 0 = ∅ := by
    have := hcap_fwdHull hW hW0 (le_refl 0)
    rw [mul_zero] at this
    exact (HPHull.hcap_eq_zero_iff _).1 this
  have heq : EqOn (gmap W 0) id H := fun z hz => by
    have := fwdMap_zero_eq hW hW0 (le_refl 0) (z := z) ⟨hz, by rw [h0]; exact Set.notMem_empty z⟩
    simp [gmap, this, hW0]
  have hne : (𝓝[H] (y : ℂ)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 ?_
    exact closure_mono inter_subset_right
      (subset_closure_ball_inter_H (y : ℂ) 1 ⟨mem_ball_self one_pos, show (0 : ℝ) ≤ (y : ℂ).im
        by simp⟩)
  have hT : Tendsto (gmap W 0) (𝓝[H] (y : ℂ)) (𝓝 (y : ℂ)) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (y : ℂ)))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (heq hz).symm
  exact hT.limUnder_eq
/-- `t ↦ g_t(z)` is continuous on `[0, T]` for `z ∈ ℍ \ K_T`. -/
theorem continuousOn_gmap (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H \ QuantumZipper.fwdHull W T) :
    ContinuousOn (fun t => gmap W t z) (Icc 0 T) := by
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hT hz.1 hz.2
  have heq : EqOn (fun t => u t + W t) (fun t => gmap W t z) (Icc 0 T) := fun t ht => by
    simp only [gmap, QuantumZipper.fwdMap_eq hW hz.1 hu ht]
  exact (hu.1.add (continuous_ofReal.comp hW).continuousOn).congr heq.symm

theorem mem_ball_inter_H {y r ε : ℝ} (hε : 0 < ε) (hεr : ε < r) :
    ((y : ℂ) + (ε : ℂ) * I) ∈ ball (y : ℂ) r ∩ H := by
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    exact hεr
  · show 0 < ((y : ℂ) + (ε : ℂ) * I).im
    simpa using hε

/-- **Continuity of the boundary value in time**: a uniform limit (rate `48 ε`) of the continuous
functions `t ↦ g_t(y + iε)`. -/
theorem continuousOn_bdryVal (hW : Continuous W) (hW0 : W 0 = 0) {y r T : ℝ} (hT : 0 ≤ T)
    (hr : 0 < r) (hd : Disjoint (ball (y : ℂ) r) (QuantumZipper.fwdHull W T)) :
    ContinuousOn (bdryVal W y) (Icc 0 T) := by
  have hmem : ∀ ε : ℝ, 0 < ε → ε < r / 2 →
      ((y : ℂ) + (ε : ℂ) * I) ∈ H \ QuantumZipper.fwdHull W T := fun ε hε hεr =>
    ⟨(mem_ball_inter_H hε hεr).2, fun hK => Set.disjoint_left.1 hd
      (ball_subset_ball (by linarith) (mem_ball_inter_H hε hεr).1) hK⟩
  refine TendstoUniformlyOn.continuousOn (F := fun (ε t : ℝ) => gmap W t ((y : ℂ) + (ε : ℂ) * I))
    (p := 𝓝[>] (0 : ℝ)) ?_ ?_
  · rw [Metric.tendstoUniformlyOn_iff]
    intro e he
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (r / 2) (e / 96) by positivity)] with
      ε hε t ht
    have hεr : ε < r / 2 := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hεe : ε < e / 96 := lt_of_lt_of_le hε.2 (min_le_right _ _)
    rw [dist_comm, dist_eq_norm]
    have h48 := norm_gmap_sub_bdryVal_le hW hW0 ht.1 (disjoint_ball_of_le hd ht.2)
      (mem_ball_inter_H (y := y) hε.1 hεr)
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε.1] at h48
    linarith
  · refine Filter.Eventually.frequently ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r / 2 by positivity)] with ε hε
    exact continuousOn_gmap hW hT (hmem ε hε.1 hε.2)
theorem conj_mem_ball {y r : ℝ} {z : ℂ} (hz : z ∈ ball (y : ℂ) r) : conj z ∈ ball (y : ℂ) r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  have : conj z - (y : ℂ) = conj (z - y) := by simp [map_sub, Complex.conj_ofReal]
  rw [this, Complex.norm_conj]
  exact hz

/-- **Open mapping at a real point**: if `B(y, r)` misses `K_t`, then `g_t(B(y, r/2) ∩ ℍ)` contains
a half-disc around the boundary value `G_t(y)`, and every real point close to `G_t(y)` is the
boundary value at a real point of `B(y, r/2)`. -/
theorem exists_ball_subset_image (hW : Continuous W) (hW0 : W 0 = 0) {y r t : ℝ} (ht : 0 ≤ t)
    (hr : 0 < r) (hd : Disjoint (ball (y : ℂ) r) (QuantumZipper.fwdHull W t)) :
    ∃ η > 0, (∀ w ∈ ball (bdryVal W y t) η ∩ H,
        ∃ z ∈ ball (y : ℂ) (r / 2) ∩ H, gmap W t z = w) ∧
      ∀ v : ℝ, (v : ℂ) ∈ ball (bdryVal W y t) η →
        ∃ y' : ℝ, (y' : ℂ) ∈ ball (y : ℂ) (r / 2) ∧ bdryVal W y' t = v := by
  have hK := isHPHull_fwdHull hW ht
  have hg := gmap_isMapOut hW hW0 ht
  obtain ⟨G, hGd, hGS, hGconj, hGreal, -, hGlim⟩ := hg.exists_reflection hK hd
  set B := ball (y : ℂ) (r / 2) with hB
  have hlimeq : ∀ z ∈ B, z.im = 0 → bdryVal W z.re t = G z := by
    intro z hz hz0
    have hzre : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
    have hnhds : 𝓝[B ∩ H] z = 𝓝[H] z :=
      nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz))
    have hlim := hGlim z hz hz0
    rw [hnhds] at hlim
    have hne : (𝓝[H] z).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.1 ?_
      exact closure_mono inter_subset_right
        (subset_closure_ball_inter_H z 1 ⟨mem_ball_self one_pos, show (0 : ℝ) ≤ z.im by
          rw [hz0]⟩)
    unfold bdryVal
    rw [hzre]
    exact hlim.limUnder_eq
  have hupper : ∀ z ∈ B ∩ H, 0 < (G z).im := fun z hz => by
    rw [hGS hz]
    exact hg.1.2.mapsTo (ball_half_inter_H_subset hd hz)
  have hlower : ∀ z ∈ B, z.im < 0 → (G z).im < 0 := fun z hz hz0 => by
    have hcz : conj z ∈ B ∩ H := ⟨conj_mem_ball hz, show 0 < (conj z).im by simp; linarith⟩
    have h1 := hupper _ hcz
    rw [hGconj z hz, Complex.conj_im] at h1
    linarith
  have hGa : AnalyticOnNhd ℂ G B := hGd.analyticOnNhd isOpen_ball
  have hy1 : ((y : ℂ) + ((r / 4 : ℝ) : ℂ) * I) ∈ B ∩ H :=
    mem_ball_inter_H (by positivity) (by linarith)
  have hy2 : ((y : ℂ) + ((r / 8 : ℝ) : ℂ) * I) ∈ B ∩ H :=
    mem_ball_inter_H (by positivity) (by linarith)
  have hopen : ∀ s ⊆ B, IsOpen s → IsOpen (G '' s) := by
    rcases hGa.is_constant_or_isOpen (convex_ball _ _).isPreconnected with ⟨c, hc⟩ | h
    · exfalso
      have h12 : gmap W t ((y : ℂ) + ((r / 4 : ℝ) : ℂ) * I) =
          gmap W t ((y : ℂ) + ((r / 8 : ℝ) : ℂ) * I) :=
        (hGS hy1).symm.trans ((hc _ hy1.1).trans ((hc _ hy2.1).symm.trans (hGS hy2)))
      have := hg.1.2.injOn (ball_half_inter_H_subset hd hy1) (ball_half_inter_H_subset hd hy2) h12
      have him := congrArg Complex.im this
      simp at him
      linarith
    · exact h
  have hyB : (y : ℂ) ∈ B := mem_ball_self (by positivity)
  have hGy : bdryVal W y t = G y := by simpa using hlimeq y hyB (by simp)
  obtain ⟨η, hη, hηsub⟩ :=
    Metric.isOpen_iff.1 (hopen B subset_rfl isOpen_ball) (G y) ⟨y, hyB, rfl⟩
  refine ⟨η, hη, ?_, ?_⟩
  · rintro w ⟨hwb, hwH⟩
    rw [hGy] at hwb
    obtain ⟨z, hzB, rfl⟩ := hηsub hwb
    have hzH : z ∈ H := by
      rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
      · exact absurd (hlower z hzB hneg) (not_lt.2 (le_of_lt hwH))
      · exact absurd (hGreal z hzB hzero) (ne_of_gt hwH)
      · exact hpos
    exact ⟨z, ⟨hzB, hzH⟩, (hGS ⟨hzB, hzH⟩).symm⟩
  · intro v hv
    rw [hGy] at hv
    obtain ⟨z, hzB, hzv⟩ := hηsub hv
    have hvim : (G z).im = 0 := by rw [hzv]; simp
    have hz0 : z.im = 0 := by
      rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
      · exact absurd hvim (ne_of_lt (hlower z hzB hneg))
      · exact hzero
      · exact absurd hvim (ne_of_gt (hupper z ⟨hzB, hpos⟩))
    refine ⟨z.re, ?_, ?_⟩
    · have : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
      rw [this]
      exact hzB
    · rw [hlimeq z hzB hz0, hzv]
/-- `ImageHyp` with the empty obstacle (no clearance needed): gives access to the local-growth
lemmas of `ConformalImage.lean`. -/
theorem imageHyp_empty (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    ImageHyp W ∅ id T 1 :=
  ⟨hW, hW0, hT, isHPHull_empty, isMapOut_empty_id, by simp, one_pos,
    fun _ _ a ha => absurd ha (Set.notMem_empty a)⟩

/-- **The driver is in the closure of the image of the future hull**: for `τ < T` and `η > 0`
some `z ∈ K_T \ K_τ` has `g_τ(z) ∈ B(W_τ, η)`. -/
theorem exists_mem_diff_gmap_mem_ball (hW : Continuous W) (hW0 : W 0 = 0) {τ T : ℝ}
    (hτ : 0 ≤ τ) (hτT : τ < T) {η : ℝ} (hη : 0 < η) :
    ∃ z ∈ QuantumZipper.fwdHull W T \ QuantumZipper.fwdHull W τ,
      gmap W τ z ∈ ball (W τ : ℂ) η := by
  have h := imageHyp_empty hW hW0 (hτ.trans hτT.le)
  obtain ⟨δ, hδ, hsub⟩ := h.exists_gmap_diff_subset (half_pos hη)
  have hτt : τ < min T (τ + δ) := lt_min hτT (by linarith)
  have hts : min T (τ + δ) ∈ Icc 0 T := ⟨by linarith, min_le_left _ _⟩
  obtain ⟨z, hz⟩ := h.diff_nonempty ⟨hτ, hτT.le⟩ hts hτt
  refine ⟨z, ⟨(QuantumZipper.fwdHull_mono (W := W)).1 (min_le_left _ _) hz.1, hz.2⟩, ?_⟩
  have := hsub τ ⟨hτ, hτT.le⟩ _ hts hτt.le (by have := min_le_right T (τ + δ); linarith)
    ⟨z, hz, rfl⟩
  exact closedBall_subset_ball (half_lt_self hη) this

/-- `W_0 = 0` is in the closure of `K_T` for `T > 0`. -/
theorem zero_mem_closure_fwdHull (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) :
    (0 : ℂ) ∈ closure (QuantumZipper.fwdHull W T) := by
  rw [Metric.mem_closure_iff]
  intro η hη
  obtain ⟨z, hz, hzb⟩ := exists_mem_diff_gmap_mem_ball hW hW0 (le_refl 0) hT hη
  have h0 : QuantumZipper.fwdMap W 0 z = z := fwdMap_zero_eq hW hW0 (le_refl 0) ⟨hz.1.1, hz.2⟩
  refine ⟨z, hz.1, ?_⟩
  simp only [gmap, h0, hW0, ofReal_zero, add_zero] at hzb
  rw [mem_ball, dist_comm] at hzb
  exact hzb

/-- **A real point away from `K_T` is not met by the driver before time `T`.** -/
theorem bdryVal_ne_of_lt (hW : Continuous W) (hW0 : W 0 = 0) {y r τ T : ℝ} (hτ : 0 ≤ τ)
    (hτT : τ < T) (hr : 0 < r) (hd : Disjoint (ball (y : ℂ) r) (QuantumZipper.fwdHull W T)) :
    bdryVal W y τ ≠ W τ := by
  intro heq
  have hdτ := disjoint_ball_of_le hd hτT.le
  obtain ⟨η, hη, hsub, -⟩ := exists_ball_subset_image hW hW0 hτ hr hdτ
  obtain ⟨z, hz, hzb⟩ := exists_mem_diff_gmap_mem_ball hW hW0 hτ hτT hη
  have hg := gmap_isMapOut hW hW0 hτ
  have hzH : gmap W τ z ∈ H := hg.1.2.mapsTo ⟨hz.1.1, hz.2⟩
  rw [← heq] at hzb
  obtain ⟨z', hz', hzz'⟩ := hsub _ ⟨hzb, hzH⟩
  have := hg.1.2.injOn (ball_half_inter_H_subset hdτ hz') ⟨hz.1.1, hz.2⟩ hzz'
  exact Set.disjoint_left.1 hd (ball_subset_ball (half_le_self hr.le) (this ▸ hz'.1)) hz.1

/-- A sign change of `G_s(y') − W_s` on `[0, t]` is impossible (intermediate value theorem and
`bdryVal_ne_of_lt`). -/
theorem false_of_sign_change (hW : Continuous W) (hW0 : W 0 = 0) {y' ρ t : ℝ} (ht : 0 ≤ t)
    (hρ : 0 < ρ) (hd : Disjoint (ball (y' : ℂ) ρ) (QuantumZipper.fwdHull W t))
    (hsign : y' * ((bdryVal W y' t).re - W t) < 0) : False := by
  set φ : ℝ → ℝ := fun s => (bdryVal W y' s).re - W s with hφ
  have hφc : ContinuousOn φ (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    exact (continuous_re.comp_continuousOn (continuousOn_bdryVal hW hW0 ht hρ hd)).sub
      hW.continuousOn
  have hφ0 : φ 0 = y' := by simp [φ, bdryVal_zero hW hW0, hW0]
  have hφt : φ t = (bdryVal W y' t).re - W t := rfl
  have h0 : (0 : ℝ) ∈ uIcc (φ 0) (φ t) := by
    rw [hφ0, hφt, mem_uIcc]
    rcases mul_neg_iff.1 hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2.le, h1.le⟩
    · exact Or.inl ⟨h1.le, h2.le⟩
  obtain ⟨τ, hτ, hφτ⟩ := intermediate_value_uIcc hφc h0
  rw [uIcc_of_le ht] at hτ
  have hne : τ ≠ t := by
    rintro rfl
    rw [hφt] at hφτ
    rw [hφτ, mul_zero] at hsign
    exact lt_irrefl _ hsign
  have heq : bdryVal W y' τ = W τ := by
    apply Complex.ext
    · simp only [ofReal_re]
      have : (bdryVal W y' τ).re - W τ = 0 := hφτ
      linarith
    · rw [(bdryVal_spec hW hW0 hτ.1 hρ (disjoint_ball_of_le hd hτ.2)).1]
      simp
  exact bdryVal_ne_of_lt hW hW0 hτ.1 (lt_of_le_of_ne hτ.2 hne) hρ hd heq

/-- **A real point `y ≠ 0` away from `K_T` is not swallowed by time `T`**: the boundary value of
`g_t` at `y` never meets the driver on `[0, T]` ([Law05] §4.1: `T_y > T`). -/
theorem bdryVal_ne (hW : Continuous W) (hW0 : W 0 = 0) {y r T : ℝ} (hr : 0 < r)
    (hd : Disjoint (ball (y : ℂ) r) (QuantumZipper.fwdHull W T)) (hy : y ≠ 0) {t : ℝ}
    (ht : t ∈ Icc 0 T) : bdryVal W y t ≠ W t := by
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact bdryVal_ne_of_lt hW hW0 ht.1 hlt hr hd
  intro heq
  have hr' : 0 < min r |y| := lt_min hr (abs_pos.2 hy)
  have hd' : Disjoint (ball (y : ℂ) (min r |y|)) (QuantumZipper.fwdHull W t) :=
    hd.mono_left (ball_subset_ball (min_le_left _ _))
  obtain ⟨η, hη, -, hreal⟩ := exists_ball_subset_image hW hW0 ht.1 hr' hd'
  have hsub : ∀ y' : ℝ, (y' : ℂ) ∈ ball (y : ℂ) (min r |y| / 2) →
      Disjoint (ball (y' : ℂ) (min r |y| / 2)) (QuantumZipper.fwdHull W t) := fun y' hy' =>
    hd'.mono_left (ball_subset_ball' (by rw [mem_ball] at hy'; linarith))
  have hclose : ∀ y' : ℝ, (y' : ℂ) ∈ ball (y : ℂ) (min r |y| / 2) → |y' - y| < |y| / 2 :=
    fun y' hy' => by
      rw [mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hy'
      have := min_le_right r |y|
      linarith
  have hball : ∀ s : ℝ, |s| < η → ((W t + s : ℝ) : ℂ) ∈ ball (bdryVal W y t) η := fun s hs => by
    rw [heq, mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa using hs
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · obtain ⟨y', hy', hv⟩ := hreal _ (hball (η / 2) (by rw [abs_of_pos (half_pos hη)]; linarith))
    have := hclose y' hy'
    rw [abs_of_neg hneg] at this
    have hy'neg : y' < 0 := by linarith [le_abs_self (y' - y)]
    refine false_of_sign_change hW hW0 ht.1 (half_pos hr') (hsub y' hy') ?_
    rw [hv, ofReal_re]
    nlinarith
  · obtain ⟨y', hy', hv⟩ := hreal _ (hball (-(η / 2)) (by
      rw [abs_neg, abs_of_pos (half_pos hη)]; linarith))
    have := hclose y' hy'
    rw [abs_of_pos hpos] at this
    have hy'pos : 0 < y' := by linarith [neg_abs_le (y' - y)]
    refine false_of_sign_change hW hW0 ht.1 (half_pos hr') (hsub y' hy') ?_
    rw [hv, ofReal_re]
    nlinarith
/-- **Clearance near a real point** `p ≠ 0` away from `K_T`. -/
theorem exists_clearance_real (hW : Continuous W) (hW0 : W 0 = 0) {p r T : ℝ} (hT : 0 ≤ T)
    (hr : 0 < r) (hd : Disjoint (ball (p : ℂ) r) (QuantumZipper.fwdHull W T)) (hp : p ≠ 0) :
    ∃ ρ > 0, ∃ s > 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ ball (p : ℂ) s ∩ H,
      ρ ≤ ‖QuantumZipper.fwdMap W t a‖ := by
  set ψ : ℝ → ℝ := fun t => ‖bdryVal W p t - W t‖ with hψ
  have hψc : ContinuousOn ψ (Icc 0 T) :=
    ((continuousOn_bdryVal hW hW0 hT hr hd).sub (continuous_ofReal.comp hW).continuousOn).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hψc
  have hψ0 : 0 < ψ t₀ := norm_pos_iff.2 (sub_ne_zero.2 (bdryVal_ne hW hW0 hr hd hp ht₀))
  refine ⟨ψ t₀ / 2, half_pos hψ0, min (r / 2) (ψ t₀ / 96),
    lt_min (half_pos hr) (by positivity), ?_⟩
  intro t ht a ha
  have hab : a ∈ ball (p : ℂ) (r / 2) ∩ H := ⟨ball_subset_ball (min_le_left _ _) ha.1, ha.2⟩
  have h48 := norm_gmap_sub_bdryVal_le hW hW0 ht.1 (disjoint_ball_of_le hd ht.2) hab
  have hap : ‖a - p‖ < ψ t₀ / 96 := by
    have := ha.1
    rw [mem_ball, dist_eq_norm] at this
    exact lt_of_lt_of_le this (min_le_right _ _)
  have hψt : ψ t₀ ≤ ψ t := hmin ht
  have hfa : QuantumZipper.fwdMap W t a =
      (gmap W t a - bdryVal W p t) + (bdryVal W p t - W t) := by
    simp only [gmap]
    ring
  have h1 : ψ t ≤ ‖(gmap W t a - bdryVal W p t) + (bdryVal W p t - W t)‖ +
      ‖gmap W t a - bdryVal W p t‖ := by
    have := norm_add_le ((gmap W t a - bdryVal W p t) + (bdryVal W p t - W t))
      (-(gmap W t a - bdryVal W p t))
    rw [norm_neg] at this
    have e : (gmap W t a - bdryVal W p t) + (bdryVal W p t - W t) +
        -(gmap W t a - bdryVal W p t) = bdryVal W p t - W t := by ring
    rw [e] at this
    exact this
  rw [hfa]
  linarith

/-- **Clearance near a point of `ℍ \ K_T`** (stability of the flow, `RealPoints`). -/
theorem exists_clearance_interior (hW : Continuous W) {p : ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hp : p ∈ H \ QuantumZipper.fwdHull W T) :
    ∃ ρ > 0, ∃ s > 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ ball p s ∩ (H \ QuantumZipper.fwdHull W T),
      ρ ≤ ‖QuantumZipper.fwdMap W t a‖ := by
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hT hp.1 hp.2
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hu
  have hE := Real.exp_pos (2 / δ ^ 2 * T)
  refine ⟨δ, hδ, δ / (2 * Real.exp (2 / δ ^ 2 * T)), by positivity, ?_⟩
  intro t ht a ha
  obtain ⟨v, hv⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hT ha.2.1 ha.2.2
  have hap : ‖a - p‖ * Real.exp (2 / δ ^ 2 * T) < δ := by
    have := ha.1
    rw [mem_ball, dist_eq_norm] at this
    calc ‖a - p‖ * Real.exp (2 / δ ^ 2 * T)
        < δ / (2 * Real.exp (2 / δ ^ 2 * T)) * Real.exp (2 / δ ^ 2 * T) :=
          mul_lt_mul_of_pos_right this hE
      _ = δ / 2 := by field_simp
      _ < δ := half_lt_self hδ
  have hcl := norm_sub_le_of_isForwardSol hW hu hv hδ hT le_rfl hlow hap t ht
  have hexp : ‖a - p‖ * Real.exp (2 / δ ^ 2 * t) ≤ ‖a - p‖ * Real.exp (2 / δ ^ 2 * T) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2
      (by positivity))) (norm_nonneg _)
  rw [QuantumZipper.fwdMap_eq hW ha.2.1 hv ht]
  have h2 := hlow t ht
  have h3 := norm_sub_norm_le (u t) (u t - v t)
  rw [sub_sub_cancel, norm_sub_rev] at h3
  linarith

/-- **Clearance from (HD1)** (`planning/handoffs/PROVE-GEO-LOC.md`, "What remains" (1)): if
`closure A ∩ closure K_T = ∅` and `0 = W_0 ∉ closure A`, the centered images `f_t(A)`,
`t ∈ [0, T]`, keep a uniform positive distance from `0`. -/
theorem exists_clearance (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {A : Set ℂ} (hA : IsHPHull A)
    (hd : Disjoint (closure A) (closure (QuantumZipper.fwdHull W T)))
    (h0 : (0 : ℂ) ∉ closure A) :
    ∃ ρ > 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, ρ ≤ ‖QuantumZipper.fwdMap W t a‖ := by
  have hAK : ∀ a ∈ A, a ∈ H \ QuantumZipper.fwdHull W T := fun a ha =>
    ⟨hA.1 ha, fun h => Set.disjoint_left.1 hd (subset_closure ha) (subset_closure h)⟩
  have hloc : ∀ p ∈ closure A, ∃ ρ > 0, ∃ s > 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ ball p s ∩ A,
      ρ ≤ ‖QuantumZipper.fwdMap W t a‖ := by
    intro p hp
    have hpK : p ∉ closure (QuantumZipper.fwdHull W T) := Set.disjoint_left.1 hd hp
    have hpim : 0 ≤ p.im := closure_minimal (fun z hz => le_of_lt (hA.1 hz))
      (isClosed_le continuous_const continuous_im) hp
    rcases hpim.lt_or_eq with hpos | hzero
    · obtain ⟨ρ, hρ, s, hs, h⟩ :=
        exists_clearance_interior hW hT ⟨hpos, fun h => hpK (subset_closure h)⟩
      exact ⟨ρ, hρ, s, hs, fun t ht a ha => h t ht a ⟨ha.1, hAK a ha.2⟩⟩
    · have hpre : ((p.re : ℝ) : ℂ) = p := Complex.ext (by simp) (by simp [← hzero])
      obtain ⟨r, hr, hsub⟩ :=
        Metric.mem_nhds_iff.1 (isClosed_closure.isOpen_compl.mem_nhds hpK)
      have hrK : Disjoint (ball ((p.re : ℝ) : ℂ) r) (QuantumZipper.fwdHull W T) := by
        rw [hpre]
        exact Set.disjoint_left.2 fun z hz hzK => hsub hz (subset_closure hzK)
      have hp0 : p.re ≠ 0 := fun h => h0 (by rw [← hpre, h, ofReal_zero] at hp; exact hp)
      obtain ⟨ρ, hρ, s, hs, h⟩ := exists_clearance_real hW hW0 hT hr hrK hp0
      rw [hpre] at h
      exact ⟨ρ, hρ, s, hs, fun t ht a ha => h t ht a ⟨ha.1, hA.1 ha.2⟩⟩
  choose! ρ hρ s hs hcl using hloc
  obtain ⟨F, hFs, hcover⟩ := hA.2.1.isCompact_closure.elim_nhds_subcover (fun p => ball p (s p))
    fun p hp => ball_mem_nhds p (hs p hp)
  rcases F.eq_empty_or_nonempty with hF | hF
  · refine ⟨1, one_pos, fun t _ a ha => absurd (hcover (subset_closure ha)) ?_⟩
    simp [hF]
  obtain ⟨p₀, hp₀, hmin⟩ := F.exists_min_image ρ hF
  refine ⟨ρ p₀, hρ p₀ (hFs p₀ hp₀), fun t ht a ha => ?_⟩
  obtain ⟨p, hpF, hap⟩ := mem_iUnion₂.1 (hcover (subset_closure ha))
  exact (hmin p hpF).trans (hcl p (hFs p hpF) t ht a ⟨hap, ha⟩)

/-- **Clearance from (HD1)** for `T > 0`: `W_0 = 0 ∈ closure K_T`, so `0 ∉ closure A` follows from
`closure A ∩ closure K_T = ∅`. -/
theorem exists_clearance_of_pos (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    {A : Set ℂ} (hA : IsHPHull A)
    (hd : Disjoint (closure A) (closure (QuantumZipper.fwdHull W T))) :
    ∃ ρ > 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, ρ ≤ ‖QuantumZipper.fwdMap W t a‖ :=
  exists_clearance hW hW0 hT.le hA hd fun h =>
    Set.disjoint_left.1 hd h (zero_mem_closure_fwdHull hW hW0 hT)

end ConformalImageFull

end InteractingSLE
