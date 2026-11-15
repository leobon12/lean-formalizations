/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelRev
import InteractingSLE.Spec.Sec5.GlueCondUnionImgSlit
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite

/-!
# Lemma 4.7's direction, item (B): the new curve's side of the mean identification, read in its own chart

Packet PROVE-CFRESTART. In the reversed-slit chart of `CrossRestartKernelRev`, the new curve is the counterflow
(driver `Wα`, time `t`, **not simple**), the obstacle is `R(K^{Wβ}_s)`, and the image chain `W'` has hull
`K^{W'}_T = revChart Wβ s (K^{Wα}_t)`. Proposition 4.9's chain (PROVE-GLUECOND8/10) read the new curve's side through
the boundary values of `F′_T` on the image hull, which needs a simple image trace (and, for a non-simple one, the
singleton tip fibre — ruling R41's eliminated input). Here the new curve's side is read in the **new curve's own
chart** `f_t`, where its hull is flattened onto the real line: the inverse transition map `Θ = f_t ∘ Ψ⁻¹ ∘ F′_T`
needs no boundary values of `F′_T` at all.

* `exists_frozen_isLoewnerTrace`: a driver continuous before its lifetime, with a generating trace, agrees up to any
  `t` before the lifetime with a continuous driver that has a continuous Loewner trace on `[0, ∞)` (frozen after `t`,
  trace continued by the image of the vertical slit, `IsLoewnerTraceLT.isLoewnerTrace_ext`);
* `imgTheta_mem`: `Θ` maps `ℍ` into `ℍ ∖ f_t(G)`, the domain of the transition map's Möbius form;
* **`eq_of_tendsto_imgTheta_zero`**: `Θ` has the cluster value `0` (the new curve's tip in its own chart) at **one**
  image-chart point at most — the image under the transition map's Möbius form of `∞` — without any tip-fibre
  information (the image tip may have many prime ends; `Θ` sees only the one at `0`);
* `IsRevData.imgTheta_limits_of_ultrafilter`: GLUECOND8's per-point inputs (`Θ → x₁ ≠ 0`, the `arg Θ′` branch in
  `2πℤ`) at every real image-chart point where `Θ` has a nonzero real cluster value, for the counterflow restart;
* **`tendsto_imgChart_of_newChart`**: the comparison step on the new curve's side — at a real image-chart point where
  `Θ → x₁` and the branch tends to `0`, the candidate (image word mean minus `χ` times the image branch) has the
  boundary limit of the union mean, provided the image word's datum at the point equals the new curve's datum at
  `x₁` (the data transport).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal Real

open QuantumZipper (H fwdHull fwdMap fwdMapInv)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open GlueImg

/-! ### A Loewner trace for the frozen counterflow driver -/

/-- **The counterflow driver frozen after `t`, with a Loewner trace on `[0, ∞)`.** If `γ` is a generating trace of
`w` of lifetime `ζ`, `w` continuous before `ζ` with `w 0 = 0`, and `t < ζ`, there are a continuous driver `V`,
`V 0 = 0`, and a continuous Loewner trace `α` of `V` on `[0, ∞)` such that `V = w` and `α = γ` on `[0, t]` (read on
`ℝ`) and the hulls agree up to `t`. -/
theorem exists_frozen_isLoewnerTrace {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ζ γ)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ∃ (V : ℝ → ℝ) (α : ℝ → ℂ), Continuous V ∧ V 0 = 0 ∧ IsLoewnerTrace V α ∧
      (∀ s ∈ Icc (0 : ℝ) t, V s = w s.toNNReal) ∧ (∀ s ∈ Icc (0 : ℝ) t, α s = γ s.toNNReal) ∧
      ∀ s ∈ Icc (0 : ℝ) t, fwdHull V s = fwdHull (fun r : ℝ => w r.toNNReal) s := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := exists_real_btwn_of_lt ht
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hw ht₂ζ
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  have hLT := hγ.isLoewnerTraceLT ht₂ζ
  have htr := hLT.isLoewnerTrace_ext hW hW0 (NNReal.coe_nonneg t) htt₂
  refine ⟨YuanCorollary13.extDrive (frozenDrive w t₂) t,
    YuanCorollary13.extTrace (frozenDrive w t₂) (fun s : ℝ => γ s.toNNReal) t,
    YuanCorollary13.continuous_extDrive hW, YuanCorollary13.extDrive_zero hW0 (NNReal.coe_nonneg t), htr,
    fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · rw [YuanCorollary13.extDrive_eq hs.2]
    exact frozenDrive_eq ⟨hs.1, hs.2.trans htt₂.le⟩
  · exact YuanCorollary13.extTrace_eq hs.2
  · have h1 : fwdHull (YuanCorollary13.extDrive (frozenDrive w t₂) t) s = fwdHull (frozenDrive w t₂) s :=
      YuanCorollary13.fwdHull_eq_of_eqOn_Icc (YuanCorollary13.continuous_extDrive hW) hW hs.1
        fun r hr => YuanCorollary13.extDrive_eq (hr.2.trans hs.2)
    rw [h1]
    exact fwdHull_eq_of_eqOn hs.1 (lt_of_le_of_lt hs.2 htt₂) fun r hr => frozenDrive_eq hr

/-! ### The inverse transition map and its cluster value `0` -/

section Theta

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

/-- **`Θ` maps `ℍ` into `ℍ ∖ f_t(G)`**, `G = R(K^{Wβ}_s)`. -/
theorem imgTheta_mem (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hWβ : Continuous Wβ)
    (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {y : ℂ} (hy : y ∈ H) :
    imgTheta Wα t Wβ s W' T y ∈ H \ fwdMap Wα t '' (negInv '' fwdHull Wβ s) := by
  have hp := revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' hy
  have hpA : revChartInv Wβ s (fwdMapInv W' T y) ∈ H \ fwdHull Wα t := ⟨hp.1, fun h => hp.2 (Or.inl h)⟩
  refine ⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht hpA, ?_⟩
  rintro ⟨g, hg, hge⟩
  have hgH : g ∈ H := image_negInv_subset_H (isHPHull_fwdHull hWβ hs).1 hg
  have hgA : g ∈ H \ fwdHull Wα t := ⟨hgH, fun hgK => Set.disjoint_left.1 hdisj hgK hg⟩
  have hgp : g = revChartInv Wβ s (fwdMapInv W' T y) := injOn_fwdMap' hWα hWα0 ht hgA hpA hge
  exact hp.2 (Or.inr (hgp ▸ hg))

/-- **The cluster value `0` of `Θ` occurs at one image-chart point at most.** There is a point `y₁` such that
whenever `Θ` tends to `0` (the new curve's tip in its own chart) along an ultrafilter at a point `y₀` of the closed
half-plane, `y₀ = y₁`. (Through the Möbius form `φ = N ∘ g'' ∘ R` of the transition map: along such an ultrafilter
`g''(R(Θ y))` is unbounded, while `y = N(g''(R(Θ y)))` stays near `y₀`, which forces `y₀` to be the image `N(∞)`.) No
information on the fibre of the image hull's boundary map over the image tip is used. -/
theorem exists_eq_of_tendsto_imgTheta_zero (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 ≤ t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) :
    ∃ y₁ : ℂ, ∀ (y₀ : ℂ) (U : Ultrafilter ℂ), (U : Filter ℂ) ≤ 𝓝[H] y₀ →
      Tendsto (imgTheta Wα t Wβ s W' T) U (𝓝 0) → y₀ = y₁ := by
  obtain ⟨W'', τ, a, b, c, d, hW''c, hW''0, hτ, hK'', hdet, hdecomp⟩ :=
    exists_imgPhi_eq_realMobius hWα hWα0 ht hKt hWβ hWβ0 hs hW' hW'0 hT hdisj hdis hK'
  obtain ⟨C, -, hC⟩ := exists_norm_fwdMap_sub_le hW''c hW''0 hτ
  refine ⟨(a / c : ℝ), fun y₀ U hU hΘ => ?_⟩
  set Θ := imgTheta Wα t Wβ s W' T with hΘdef
  have hUH : ∀ᶠ y in (U : Filter ℂ), y ∈ H := hU (self_mem_nhdsWithin)
  have hUy : Tendsto id (U : Filter ℂ) (𝓝 y₀) := le_trans hU nhdsWithin_le_nhds
  have hG : negInv '' fwdHull W'' τ = fwdMap Wα t '' (negInv '' fwdHull Wβ s) := by
    rw [hK'', fwdMap_image_negInv_eq]
  -- the Möbius argument `w y = g''(R(Θ y))` is unbounded along `U`
  set w : ℂ → ℂ := fun y => fwdMap W'' τ (negInv (Θ y)) + (W'' τ : ℂ) with hw
  have hdom : ∀ y ∈ H, negInv (Θ y) ∈ H \ fwdHull W'' τ := fun y hy => by
    have hm := imgTheta_mem hWα hWα0 ht hWβ hWβ0 hs hW' hW'0 hT hdisj hK' hy
    rw [← hG] at hm
    exact negInv_notMem_fwdHull hm
  have hnorm : Tendsto (fun y => ‖Θ y‖⁻¹) (U : Filter ℂ) atTop := by
    have h0 : Tendsto (fun y => ‖Θ y‖) (U : Filter ℂ) (𝓝[>] 0) := by
      have hn := (continuous_norm.tendsto (0 : ℂ)).comp hΘ
      rw [norm_zero] at hn
      refine tendsto_nhdsWithin_iff.2 ⟨hn, ?_⟩
      filter_upwards [hUH] with y hy
      exact norm_pos_iff.2 (ne_zero_of_mem_H
        (imgTheta_mem hWα hWα0 ht hWβ hWβ0 hs hW' hW'0 hT hdisj hK' hy).1)
    exact tendsto_inv_nhdsGT_zero.comp h0
  have hwinf : Tendsto (fun y => ‖w y‖) (U : Filter ℂ) atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-(C + |W'' τ|)) hnorm)
    filter_upwards [hUH] with y hy
    have h1 := hC _ (hdom y hy)
    have h2 : ‖negInv (Θ y)‖ = ‖Θ y‖⁻¹ := norm_negInv _
    have h3 : ‖((W'' τ : ℝ) : ℂ)‖ = |W'' τ| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h4 := norm_sub_norm_le (negInv (Θ y)) (fwdMap W'' τ (negInv (Θ y)))
    have h5 := norm_sub_le (fwdMap W'' τ (negInv (Θ y)) + (W'' τ : ℂ)) (W'' τ : ℂ)
    simp only [add_sub_cancel_right] at h5
    rw [norm_sub_rev] at h1
    show ‖Θ y‖⁻¹ + -(C + |W'' τ|) ≤ ‖fwdMap W'' τ (negInv (Θ y)) + (W'' τ : ℂ)‖
    linarith
  -- along `U`, `y = N(w y)`
  have hrel : ∀ᶠ y in (U : Filter ℂ), y = realMobius a b c d (w y) := by
    filter_upwards [hUH] with y hy
    have hm := imgTheta_mem hWα hWα0 ht hWβ hWβ0 hs hW' hW'0 hT hdisj hK' hy
    rw [← hG] at hm
    rw [← hdecomp _ hm]
    exact (imgPhi_imgTheta hWα ht hWβ hWβ0 hs hW' hW'0 hT hK' hWα0 hy).symm
  -- if `c y₀ ≠ a`, then `w y = (b − d y)/(c y − a)` stays bounded near `y₀`
  by_contra hne
  have hcy : (c : ℂ) * y₀ - a ≠ 0 := by
    intro h
    apply hne
    by_cases hc : c = 0
    · exfalso
      rw [hc] at h
      simp only [ofReal_zero, zero_mul, zero_sub, neg_eq_zero, ofReal_eq_zero] at h
      rw [h, hc] at hdet
      simp at hdet
    · have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc
      push_cast
      field_simp
      linear_combination h
  have hcont : ContinuousAt (fun y : ℂ => ((b : ℂ) - d * y) / (c * y - a)) y₀ :=
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).div
      ((continuousAt_const.mul continuousAt_id).sub continuousAt_const) hcy
  have hev : ∀ᶠ y in (U : Filter ℂ), (c : ℂ) * y - a ≠ 0 :=
    hUy.eventually ((continuous_const.mul continuous_id |>.sub continuous_const).continuousAt.eventually_ne hcy)
  have hweq : ∀ᶠ y in (U : Filter ℂ), w y = ((b : ℂ) - d * y) / (c * y - a) := by
    filter_upwards [hrel, hev, hUH] with y hy hcy' hyH
    have hy0 : y ≠ 0 := ne_zero_of_mem_H hyH
    rw [realMobius] at hy
    have hden : (c : ℂ) * w y + d ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hy
      exact hy0 hy
    rw [eq_div_iff hcy']
    rw [eq_div_iff hden] at hy
    linear_combination hy
  have hb : Tendsto w (U : Filter ℂ) (𝓝 (((b : ℂ) - d * y₀) / (c * y₀ - a))) :=
    (hcont.tendsto.comp hUy).congr' (hweq.mono fun y hy => hy.symm)
  exact not_tendsto_atTop_of_tendsto_nhds ((continuous_norm.tendsto _).comp hb) hwinf

end Theta

/-! ### The per-point inputs for the counterflow restart, and the comparison step -/

namespace IsRevData

variable {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ} {Wc : ℝ → ℝ} {t : ℝ} {Ũ : ℝ → ℝ} {σ' c : ℝ}

/-- **The per-point inputs on the counterflow's side** (GLUECOND8's `imgTheta_limits_of_ultrafilter`, which needs no
simple new curve), for the counterflow restart: at every real image-chart point where `Θ` has a nonzero real cluster
value along one ultrafilter, `Θ` has a nonzero real limit and the branch of `arg Θ′` tends to a multiple of `2π`. -/
theorem imgTheta_limits_of_ultrafilter (hd : IsRevData q U σ x₁ Wc t Ũ σ' c) {α : ℝ → ℂ} (hα : IsLoewnerTrace Wc α)
    (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) (ht : 0 ≤ t) {W' : ℝ → ℝ} {T : ℝ} (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) (hK' : fwdHull W' T = revChart Ũ σ' '' fwdHull Wc t) {y x₀ : ℝ} (hx₀ : x₀ ≠ 0)
    {V : Ultrafilter ℂ} (hV : (V : Filter ℂ) ≤ 𝓝[H] (y : ℂ)) (hΘ : Tendsto (imgTheta Wc t Ũ σ' W' T) V (𝓝 (x₀ : ℂ))) :
    (∃ p : ℝ, p ≠ 0 ∧ Tendsto (imgTheta Wc t Ũ σ' W' T) (𝓝[H] (y : ℂ)) (𝓝 (p : ℂ))) ∧
      ∃ k : ℤ, Tendsto (fun z => (QuantumZipper.logDerivFwd Wc t (revChartInv Ũ σ' (fwdMapInv W' T z))).im -
        ((QuantumZipper.logDerivFwd W' T (fwdMapInv W' T z)).im +
          (logDerivPsi Ũ σ' (revChartInv Ũ σ' (fwdMapInv W' T z))).im)) (𝓝[H] (y : ℂ)) (𝓝 (2 * π * k)) :=
  GlueImg.imgTheta_limits_of_ultrafilter hα hWc hWc0 ht hd.real_new hd.drv_cont hd.drv_zero hd.time_nonneg hW' hW'0 hT
    hd.obst_closed hd.disj hd.dis_obst hK' hx₀ hV hΘ

/-- **The cluster value `0` of `Θ` at one point at most**, for the counterflow restart. -/
theorem exists_eq_of_tendsto_imgTheta_zero (hd : IsRevData q U σ x₁ Wc t Ũ σ' c) (hWc : Continuous Wc)
    (hWc0 : Wc 0 = 0) (ht : 0 ≤ t) {W' : ℝ → ℝ} {T : ℝ} (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hK' : fwdHull W' T = revChart Ũ σ' '' fwdHull Wc t) :
    ∃ y₁ : ℂ, ∀ (y₀ : ℂ) (V : Ultrafilter ℂ), (V : Filter ℂ) ≤ 𝓝[H] y₀ →
      Tendsto (imgTheta Wc t Ũ σ' W' T) V (𝓝 0) → y₀ = y₁ :=
  CrossRestart.exists_eq_of_tendsto_imgTheta_zero hWc hWc0 ht hd.real_new hd.drv_cont hd.drv_zero hd.time_nonneg hW'
    hW'0 hT hd.disj hd.dis_obst hK'

end IsRevData

/-- **The comparison step on the new curve's side.** At a point `y₀` of the image chart where the inverse transition
map `Θ` (mapping `ℍ` into `ℍ`) tends to `x₀`, suppose the new curve's mean `uA` tends to `dA` at `x₀`, the image
word's mean `u` tends to `dI` at `y₀`, the data agree (`dI = dA`, the data transport), and the two branches
`LA` (new curve's chart, read through `Θ`) and `LB` (image chart) agree in the limit. If the union-mean expression
`M ∘ Φ + c` is asymptotic to the new curve's candidate `uA ∘ Θ − χ LA` at `y₀` (Proposition 3.8 read in the new
curve's chart), then it is asymptotic to the image candidate `u − χ LB`. -/
theorem tendsto_imgChart_of_newChart {M uA u LA LB : ℂ → ℝ} {Φ Θ : ℂ → ℂ} {c χ : ℝ} {y₀ x₀ : ℂ} {dA dI : ℝ}
    (hΘH : ∀ y ∈ H, Θ y ∈ H) (hΘ : Tendsto Θ (𝓝[H] y₀) (𝓝 x₀)) (huA : Tendsto uA (𝓝[H] x₀) (𝓝 dA))
    (hu : Tendsto u (𝓝[H] y₀) (𝓝 dI)) (hdata : dI = dA)
    (harg : Tendsto (fun y => LA y - LB y) (𝓝[H] y₀) (𝓝 0))
    (hA : Tendsto (fun y => M (Φ y) + c - (uA (Θ y) - χ * LA y)) (𝓝[H] y₀) (𝓝 0)) :
    Tendsto (fun y => M (Φ y) + c - (u y - χ * LB y)) (𝓝[H] y₀) (𝓝 0) := by
  have hΘ' : Tendsto Θ (𝓝[H] y₀) (𝓝[H] x₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hΘ, eventually_nhdsWithin_of_forall hΘH⟩
  have h1 := huA.comp hΘ'
  have h := (hA.add (h1.sub hu)).sub (harg.const_mul χ)
  rw [hdata, sub_self, add_zero, mul_zero, sub_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply]
  ring

end InteractingSLE.Sec5.CrossRestart
