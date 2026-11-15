/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfFreshSplit
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite
import InteractingSLE.Foundations.Loewner.YuanSimpleApproxTrans

/-!
# Lemma R.5's side agreement at the left stop without a fresh tip

Packet PROVE-R5-FRESHTIP. `R5Lift.R7FreshTip` asked, besides the seed-interval landings in `ℍ`, that the left stop
`T = T⁰(q)` be a fresh interior tip (`η(T)` in the pocket and `T` a cut time). That fact was used only for the side
agreement "a current coordinate `u` and every real limit `y` of `f_T ∘ cur⁻¹` at `u` lie on the same side of `0`"
(`R5Lift.side_of_tip`, through Lemma 1.1 of the singleton-tip elimination note). Here the side agreement is proved
**pathwise from the seed-interval landings alone**, in the spirit of that note's device ("compare in one fixed earlier
chart; neither end is identified with the current driver"):

* **`norm_le_of_tendsto_increment`**: if a path in `ℍ ∖ K_T` tends to a point `p ∈ K_T ∖ K_t`, every limit of `f_T`
  along it has modulus at most `25 M + 11 √(T − t)`, `M` the oscillation of the driver on `[t, T]` (the increment hull
  lies in `B(0, M + 3√(T − t))` and moves points by at most `24 M + 8 √(T − t)`, Lawler 4.12, QuantumZipper);
* **`exists_trMap_mem_H`**: for a continuous Loewner trace and `q' < q`, if the real coordinates off an interval `J`
  have non-interior `F̄_q`-values, then arbitrarily close to `0` some `u ∈ J` has `F̄_{q', q}(u) ∈ ℍ` (otherwise
  `F̄_{q', q}` reflects near `0` and its image contains a half-disc about the increment tip, a limit of hull points);
* **`exists_boundaryMap`**, **`side_of_anchor`**: on an interval of hull landings the boundary map of `f_T ∘ cur⁻¹` is
  continuous and strictly increasing; with an anchor (coordinates arbitrarily close to `0` with arbitrarily small real
  limits) the two sides agree;
* `exists_isLoewnerTrace_of_driven`: the relative chain past a live capacity is a continuous Loewner trace (slit
  extension);
* **`curSide_of_seedLand`**: the side agreement at `T(q)` for any pocket shape whose relative domains at `q' ≤ q` are
  `C ∩ (ℍ ∖ K_{T(q')})` and whose stops `T(q')`, `q' < q`, approach `T(q)` from below.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Fresh

/-- **The ambient image of a new landing is small.** -/
theorem norm_le_of_tendsto_increment {W : ℝ → ℝ} (hW : Continuous W) {t T M : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) (hM : ∀ r ∈ Icc (0 : ℝ) (T - t), |W (t + r) - W t| ≤ M) {α : Type*} {l : Filter α}
    [l.NeBot] {F : α → ℂ} (hF : ∀ᶠ a in l, F a ∈ H \ fwdHull W T) {p : ℂ} (hFp : Tendsto F l (𝓝 p))
    (hpt : p ∈ H \ fwdHull W t) (hpT : p ∈ fwdHull W T) {y : ℂ}
    (hy : Tendsto (fun a => fwdMap W T (F a)) l (𝓝 y)) :
    ‖y‖ ≤ 25 * M + 11 * Real.sqrt (T - t) := by
  set s := T - t with hsdef
  have hs : 0 ≤ s := sub_nonneg.2 htT
  have hTe : T = t + s := by rw [hsdef]; ring
  set V : ℝ → ℝ := fun r => W (t + r) - W t with hVdef
  have hVc : Continuous V := (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hV0 : V 0 = 0 := by simp [hVdef]
  have hdiff := QuantumZipper.fwdHull_add_diff hW ht hs
  rw [← hTe] at hdiff
  have hpV : fwdMap W t p ∈ fwdHull V s := by
    have hmem : p ∈ fwdHull W T \ fwdHull W t := ⟨hpT, hpt.2⟩
    rw [hdiff] at hmem
    exact hmem.2
  have hs0 : 0 < s := by
    rcases hs.eq_or_lt with h | h
    · exfalso
      apply hpt.2
      have hTt : T = t := by rw [hTe, ← h, add_zero]
      rw [← hTt]
      exact hpT
    · exact h
  have hMV : ∀ r ∈ Icc (0 : ℝ) s, |V r| ≤ M := fun r hr => hM r hr
  have hball := QuantumZipper.CaraR.fwdHull_subset_closedBall hVc hs0 hMV hpV
  rw [mem_closedBall, dist_zero_right] at hball
  have hcont : Tendsto (fun a => fwdMap W t (F a)) l (𝓝 (fwdMap W t p)) := by
    have hca : ContinuousAt (fwdMap W t) p :=
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).continuousOn).continuousAt
        ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht).mem_nhds hpt)
    exact hca.tendsto.comp hFp
  have hle : ∀ᶠ a in l, ‖fwdMap W T (F a)‖ ≤ ‖fwdMap W t (F a)‖ + (24 * M + 8 * Real.sqrt s) := by
    filter_upwards [hF] with a ha
    have haT : F a ∉ fwdHull W t := fun h => ha.2 ((QuantumZipper.fwdHull_mono).1 htT h)
    have hwH : fwdMap W t (F a) ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht ⟨ha.1, haT⟩
    have hwV : fwdMap W t (F a) ∉ fwdHull V s := fun h => by
      have hmem : F a ∈ {z | z ∈ H \ fwdHull W t ∧ fwdMap W t z ∈ fwdHull V s} := ⟨⟨ha.1, haT⟩, h⟩
      rw [← hdiff] at hmem
      exact ha.2 hmem.1
    have hsol := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull (ht.trans htT) ha.1 ha.2
    rw [hTe] at hsol
    have hadd := QuantumZipper.fwdMap_add hW ha.1 ht hs hsol
    rw [← hTe] at hadd
    have hb := QuantumZipper.CoreArc.norm_fwdMap_sub_le_uniform hVc hV0 hs0 hMV ⟨hwH, hwV⟩
    rw [hadd]
    calc ‖fwdMap V s (fwdMap W t (F a))‖
        = ‖fwdMap W t (F a) + (fwdMap V s (fwdMap W t (F a)) - fwdMap W t (F a))‖ := by ring_nf
      _ ≤ ‖fwdMap W t (F a)‖ + ‖fwdMap V s (fwdMap W t (F a)) - fwdMap W t (F a)‖ := norm_add_le _ _
      _ ≤ ‖fwdMap W t (F a)‖ + (24 * M + 8 * Real.sqrt s) := by gcongr
  have hlim := le_of_tendsto_of_tendsto hy.norm (hcont.norm.add_const (24 * M + 8 * Real.sqrt s)) hle
  linarith


open YuanSimpleApprox in
/-- **The tip of a Loewner trace is a limit of hull points** (at a positive time). -/
theorem tip_mem_closure_fwdHull {V : ℝ → ℝ} {γ : ℝ → ℂ} (hγ : IsLoewnerTrace V γ) (hV : Continuous V)
    (hV0 : V 0 = 0) {h : ℝ} (hh : 0 < h) : γ h ∈ closure (fwdHull V h) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hc : ContinuousWithinAt γ (Ici 0) h := hγ.2.1 h hh.le
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδc⟩ := hc ε hε
  obtain ⟨t, ht, hcut⟩ := exists_isCutTime_mem_Ioo hγ hV hV0 (le_max_left 0 (h - δ / 2))
    (max_lt hh (by linarith))
  have ht0 : 0 ≤ t := (le_max_left 0 (h - δ / 2)).trans ht.1.le
  refine ⟨γ t, ?_, ?_⟩
  · rw [hγ.2.2 h hh.le]
    exact ⟨hcut.1, Or.inl (subset_closure ⟨t, ⟨ht0, ht.2.le⟩, rfl⟩)⟩
  · have hd : dist t h < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [ht.2, le_max_right 0 (h - δ / 2), ht.1]
    rw [dist_comm]
    exact hδc ht0 hd

open YuanSimpleApprox in
/-- **A coordinate near the driver whose transition value lies in `ℍ`.** Let `V` drive a continuous Loewner trace,
`0 ≤ q' < q`, and let every real coordinate outside `J` have a non-interior boundary value of `F_q`. Then arbitrarily
close to `0` some `u ∈ J` has `F̄_{q', q}(u) ∈ ℍ`: otherwise `F̄_{q', q}` would be real near `0`, so its image would
contain a half-disc about the increment tip, which is a limit of points of the increment hull. -/
theorem exists_trMap_mem_H {V : ℝ → ℝ} {γ : ℝ → ℂ} (hγ : IsLoewnerTrace V γ) (hV : Continuous V)
    (hV0 : V 0 = 0) {q' q : ℝ} (hq' : 0 ≤ q') (hqq : q' < q) {J : Set ℝ}
    (hout : ∀ u : ℝ, u ∉ J → extendFrom H (fwdMapInv V q) u ∉ H) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u ∈ J, |u| < δ ∧ trMap V q' q u ∈ H := by
  by_contra hne
  push Not at hne
  set g := trMap V q' q with hg
  have hσ := isLoewnerTrace_shift' hγ hV hV0 hq'
  have hVs := QuantumZipper.RS.continuous_shiftDrive hV q'
  have hVs0 := QuantumZipper.RS.shiftDrive_zero V q'
  have hd : DifferentiableOn ℂ g H := trMap_differentiableOn hγ hV hV0 hq' hqq.le
  have hc : ContinuousOn g Hbar := trMap_continuousOn hγ hV hV0 hq' hqq.le
  have hinj : InjOn g H := trMap_injOn hγ hV hV0 hq' hqq.le
  have hHbar : MapsTo g Hbar Hbar := trMap_mapsTo_Hbar hγ hV hV0 hq' hqq.le
  have hreal : ∀ z ∈ ball ((0 : ℝ) : ℂ) δ, z.im = 0 → (g z).im = 0 := by
    intro z hz hzim
    have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hzim])
    have hzbar : z ∈ Hbar := show 0 ≤ z.im by rw [hzim]
    have hgz : 0 ≤ (g z).im := hHbar hzbar
    by_contra hne0
    have hgH : g z ∈ H := lt_of_le_of_ne hgz (Ne.symm hne0)
    have hu : |z.re| < δ := by
      have h1 : ‖z‖ < δ := by simpa using hz
      have h2 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      linarith
    by_cases hJ : z.re ∈ J
    · rw [hz'] at hgH
      exact hne z.re hJ hu hgH
    · apply hout z.re hJ
      rw [← hz', ← trMap_zero_left hV0 q, ← trMap_trMap hγ hV hV0 le_rfl hq' hqq.le hzbar]
      exact trMap_mem_H hV hq' hgH
  obtain ⟨ρ, hρ, hsub⟩ := R5Lift.exists_halfBall_subset_image_of_reflect hδ (hd.mono inter_subset_left)
    (hc.mono inter_subset_left) hreal (fun z hz => trMap_mem_H hV hqq.le hz.1) (hinj.mono inter_subset_left)
  have htip : g ((0 : ℝ) : ℂ) ∈ closure (fwdHull (QuantumZipper.RS.shiftDrive V q') (q - q')) := by
    rw [Complex.ofReal_zero, hg, trMap_zero]
    exact tip_mem_closure_fwdHull hσ hVs hVs0 (sub_pos.2 hqq)
  obtain ⟨k, hk, hkd⟩ := Metric.mem_closure_iff.1 htip ρ hρ
  have hkH : k ∈ H := hk.1
  obtain ⟨w, hw, hwk⟩ := hsub ⟨hkH, by rw [mem_ball, dist_comm]; exact hkd⟩
  have := trMap_image_subset hV hqq.le ⟨w, hw.1, hwk⟩
  exact this.2 hk

open QuantumZipper (isOpen_H) in
/-- **The boundary map of `f_T ∘ cur⁻¹` along an interval of hull landings** is continuous, injective and strictly
increasing (LIFT2's argument in `R5Lift.side_of_tip`, without the anchor at `0`). -/
theorem exists_boundaryMap {cur : Chart} (hcur : cur.IsConformal) {Fc : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H)
    (hFcc : ContinuousOn Fc Hbar) {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hK : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T) {a b : ℝ} (hab : a < b)
    (hland : ∀ u ∈ Ioo a b, Fc u ∈ fwdHull W T) :
    ∃ φ : ℝ → ℝ, (∀ u ∈ Ioo a b, Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (φ u : ℂ))) ∧
      ContinuousOn φ (Ioo a b) ∧ StrictMonoOn φ (Ioo a b) := by
  set S : ℂ → ℂ := fun z => fwdMap W T (cur.2.1 z) with hS
  set g := extendFrom H S with hg
  have hlandB : ∀ u ∈ Ioo a b, ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (u : ℂ) ρ → Fc v ∈ fwdHull W T := by
    intro u hu
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo u hu
    exact ⟨ρ, hρ, fun v hv => hland v (hball (R5Lift.mem_ball_of_ofReal_mem_ball hv))⟩
  have hdat : ∀ u ∈ Ioo a b, Tendsto S (𝓝[H] (u : ℂ)) (𝓝 (g u)) ∧ (g u).im = 0 := by
    intro u hu
    obtain ⟨ρ, hρ, hl⟩ := hlandB u hu
    obtain ⟨-, -, hgr, -, -, -, hgl⟩ := R5Lift.reflect_data_of_hull_landing (x := u) (ρ := ρ) hcur hFc hFcc hη hW hW0
      hT hK hl
    have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
    exact ⟨hgl u ⟨hubar, mem_ball_self hρ⟩, hgr u (mem_ball_self hρ) (ofReal_im u)⟩
  set φ : ℝ → ℝ := fun v => (g v).re with hφ
  have hgu : ∀ u ∈ Ioo a b, g u = (φ u : ℂ) := fun u hu =>
    Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im]; exact (hdat u hu).2)
  have hφc : ContinuousOn φ (Ioo a b) :=
    R5Lift.continuousOn_of_tendsto_nhdsWithin_H (f := fun z => (S z).re) fun u hu =>
      (continuous_re.tendsto _).comp (hdat u hu).1
  have hSinj : InjOn S H := fun z₁ hz₁ z₂ hz₂ h => by
    have h' := congrArg (fwdMapInv W T) h
    simp only [hS] at h'
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT (hK (hcur.inv_mem_dom hz₁)),
      QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT (hK (hcur.inv_mem_dom hz₂))] at h'
    exact hcur.injOn hz₁ hz₂ h'
  have hinjφ : InjOn φ (Ioo a b) := by
    intro u₁ hu₁ u₂ hu₂ heq
    by_contra hne
    have hd0 : 0 < |u₁ - u₂| := abs_pos.2 (sub_ne_zero.2 hne)
    set δ := |u₁ - u₂| / 2 with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨ρ₁, hρ₁, hl₁⟩ := hlandB u₁ hu₁
    obtain ⟨ρ₂, hρ₂, hl₂⟩ := hlandB u₂ hu₂
    obtain ⟨hgΦ₁, hgc₁, hgr₁, hm₁, hi₁, hgd₁, -⟩ := R5Lift.reflect_data_of_hull_landing (x := u₁)
      (ρ := min ρ₁ δ) hcur hFc hFcc hη hW hW0 hT hK fun v hv => hl₁ v (ball_subset_ball (min_le_left _ _) hv)
    obtain ⟨hgΦ₂, hgc₂, hgr₂, hm₂, hi₂, hgd₂, -⟩ := R5Lift.reflect_data_of_hull_landing (x := u₂)
      (ρ := min ρ₂ δ) hcur hFc hFcc hη hW hW0 hT hK fun v hv => hl₂ v (ball_subset_ball (min_le_left _ _) hv)
    obtain ⟨ρ'₁, hρ'₁, hs₁⟩ :=
      R5Lift.exists_halfBall_subset_image_of_reflect (lt_min hρ₁ hδ0) hgd₁ hgc₁ hgr₁ hm₁ hi₁
    obtain ⟨ρ'₂, hρ'₂, hs₂⟩ :=
      R5Lift.exists_halfBall_subset_image_of_reflect (lt_min hρ₂ hδ0) hgd₂ hgc₂ hgr₂ hm₂ hi₂
    have hg12 : g u₁ = g u₂ := by rw [hgu u₁ hu₁, hgu u₂ hu₂, heq]
    set ε := min ρ'₁ ρ'₂ / 2 with hε
    have hε0 : 0 < ε := by positivity
    set w : ℂ := g u₁ + (ε : ℂ) * I with hw
    have hwH : w ∈ H := show 0 < w.im by
      simp only [hw, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, zero_add, add_zero,
        (hdat u₁ hu₁).2]
      exact hε0
    have hdist : dist w (g u₁) = ε := by
      rw [hw, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hε0.le]
    obtain ⟨z₁, hz₁, hzw₁⟩ := hs₁ ⟨hwH, by
      rw [mem_ball, hdist]; linarith [min_le_left ρ'₁ ρ'₂]⟩
    obtain ⟨z₂, hz₂, hzw₂⟩ := hs₂ ⟨hwH, by
      show dist w (g u₂) < ρ'₂
      rw [← hg12, hdist]; linarith [min_le_right ρ'₁ ρ'₂]⟩
    have hSz : S z₁ = S z₂ :=
      calc S z₁ = g z₁ := hgΦ₁ hz₁
        _ = w := hzw₁
        _ = g z₂ := hzw₂.symm
        _ = S z₂ := (hgΦ₂ hz₂).symm
    have hz := hSinj hz₁.1 hz₂.1 hSz
    have h1 : dist z₁ (u₁ : ℂ) < δ := lt_of_lt_of_le (mem_ball.1 hz₁.2) (min_le_right _ _)
    have h2 : dist z₂ (u₂ : ℂ) < δ := lt_of_lt_of_le (mem_ball.1 hz₂.2) (min_le_right _ _)
    have h12 : dist (u₁ : ℂ) (u₂ : ℂ) = |u₁ - u₂| := by
      rw [Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have htri := dist_triangle (u₁ : ℂ) z₁ (u₂ : ℂ)
    rw [hz, dist_comm (u₁ : ℂ) z₂] at htri
    rw [hz] at h1
    linarith [dist_comm z₂ (u₁ : ℂ)]
  -- orientation at the midpoint
  set u₀ := (a + b) / 2 with hu₀
  have hu₀m : u₀ ∈ Ioo a b := ⟨by rw [hu₀]; linarith, by rw [hu₀]; linarith⟩
  obtain ⟨ρ₀, hρ₀, hl₀⟩ := hlandB u₀ hu₀m
  obtain ⟨-, hgc₀, hgr₀, hm₀, hi₀, hgd₀, -⟩ := R5Lift.reflect_data_of_hull_landing (x := u₀) (ρ := ρ₀) hcur hFc
    hFcc hη hW hW0 hT hK hl₀
  obtain ⟨-, hright⟩ := R5Lift.reflect_orient hρ₀ hgd₀ hgc₀ hgr₀ hm₀ hi₀
  have hmono : StrictMonoOn φ (Ioo a b) := by
    refine (hφc.strictMonoOn_of_injOn_Ioo hab hinjφ).resolve_right fun hanti => ?_
    obtain ⟨v, hv, hvm⟩ := (hright.and (Ioo_mem_nhdsGT hu₀m.2)).exists
    have hvab : v ∈ Ioo a b := ⟨hu₀m.1.trans hvm.1, hvm.2⟩
    have := hanti hu₀m hvab hvm.1
    exact lt_asymm hv this
  refine ⟨φ, fun u hu => ?_, hφc, hmono⟩
  rw [← hgu u hu]
  exact (hdat u hu).1

/-- **The side agreement from an anchor.** On an interval of hull landings, if arbitrarily close to `0` some
coordinate has an arbitrarily small real limit of `f_T ∘ cur⁻¹`, then at every coordinate `u` every real limit `y`
satisfies `u < 0 ↔ y < 0`. -/
theorem side_of_anchor {cur : Chart} (hcur : cur.IsConformal) {Fc : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H)
    (hFcc : ContinuousOn Fc Hbar) {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hK : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T) {a b : ℝ}
    (hland : ∀ u ∈ Ioo a b, Fc u ∈ fwdHull W T)
    (hanch : ∀ ε > 0, ∀ δ > 0, ∃ u ∈ Ioo a b, |u| < δ ∧ ∀ y : ℝ,
      Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) → |y| < ε) :
    ∀ u ∈ Ioo a b, ∀ y : ℝ, Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) →
      (u < 0 ↔ y < 0) := by
  intro u hu y hy
  have hab : a < b := hu.1.trans hu.2
  obtain ⟨φ, hφl, hφc, hmono⟩ := exists_boundaryMap hcur hFc hFcc hη hW hW0 hT hK hab hland
  have hlim : ∀ v ∈ Ioo a b, ∀ y : ℝ,
      Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (v : ℂ)) (𝓝 (y : ℂ)) → y = φ v := by
    intro v hv y hy
    have := R5Lift.nhdsWithin_H_neBot v
    exact_mod_cast tendsto_nhds_unique hy (hφl v hv)
  have hanchφ : ∀ ε > 0, ∀ δ > 0, ∃ v ∈ Ioo a b, |v| < δ ∧ |φ v| < ε := by
    intro ε hε δ hδ
    obtain ⟨v, hv, hvδ, hvε⟩ := hanch ε hε δ hδ
    exact ⟨v, hv, hvδ, hvε (φ v) (hφl v hv)⟩
  have hneg : ∀ v ∈ Ioo a b, v < 0 → φ v ≤ 0 := by
    intro v hv hv0
    by_contra hpos
    push Not at hpos
    obtain ⟨w, hw, hwδ, hwε⟩ := hanchφ (φ v) hpos (-v) (by linarith)
    have hvw : v < w := by have := neg_abs_le w; linarith
    have := hmono hv hw hvw
    have := le_abs_self (φ w)
    linarith
  have hpos : ∀ v ∈ Ioo a b, 0 < v → 0 ≤ φ v := by
    intro v hv hv0
    by_contra hneg'
    push Not at hneg'
    obtain ⟨w, hw, hwδ, hwε⟩ := hanchφ (-φ v) (by linarith) v hv0
    have hwv : w < v := by have := le_abs_self w; linarith
    have := hmono hw hv hwv
    have := neg_abs_le (φ w)
    linarith
  rw [hlim u hu y hy]
  constructor
  · intro hu0
    obtain ⟨w, hw, hwδ, -⟩ := hanchφ 1 one_pos (-u / 2) (by linarith)
    have hw' : u / 2 < w := by have := neg_abs_le w; linarith
    have hhalf : u / 2 ∈ Ioo a b := ⟨by linarith [hu.1], hw'.trans hw.2⟩
    have h1 := hmono hu hhalf (by linarith)
    have h2 := hneg (u / 2) hhalf (by linarith)
    linarith
  · intro hφu
    by_contra hu0
    push Not at hu0
    rcases hu0.eq_or_lt with h0 | h0
    · subst h0
      have hca : ContinuousAt φ 0 := hφc.continuousAt (isOpen_Ioo.mem_nhds hu)
      have hev : ∀ᶠ v in 𝓝[>] (0 : ℝ), φ v < 0 :=
        (hca.eventually (gt_mem_nhds hφu)).filter_mono nhdsWithin_le_nhds
      obtain ⟨v, hv, hvm⟩ := (hev.and (Ioo_mem_nhdsGT hu.2)).exists
      have := hpos v ⟨hu.1.trans hvm.1, hvm.2⟩ hvm.1
      linarith
    · have := hpos u hu h0
      linarith


section Sample

open PocketTraversal PocketStop Lemma71C YuanSimpleApprox

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- **A continuous Loewner trace for the relative chain** past a live capacity `q`: the traversal's capacity driver
agrees on `[0, q₁]`, `q₁ > q`, with a continuous driver `V` (`V 0 = 0`) of a continuous Loewner trace on `[0, ∞)`
(the slit extension of the capacity trace, `IsLoewnerTraceLT.isLoewnerTrace_ext`). -/
theorem exists_isLoewnerTrace_of_driven {γ₀ : ℝ → ℂ} (hγ : IsDrivenCurve γ₀) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife γ₀) :
    ∃ (V : ℝ → ℝ) (γ₁ : ℝ → ℂ) (q₁ : ℝ), (q : ℝ) < q₁ ∧ Continuous V ∧ V 0 = 0 ∧ IsLoewnerTrace V γ₁ ∧
      ∀ s ∈ Icc (0 : ℝ) q₁, segDriver γ₀ s.toNNReal = V s := by
  obtain ⟨q₂, hqq₂, hq₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqq₂' : (q : ℝ) < q₂ := by exact_mod_cast hqq₂
  set W₁ := Ito.clampDrv (Ito.rpath fun s => segDriver γ₀ s) q₂
  have hW₁ : Continuous W₁ := Ito.continuous_clampDrv q₂.coe_nonneg
    (Ito.continuousOn_rpath hγ.segDriver_spec.2.1 hq₂)
  have heq₁ : EqOn W₁ (Ito.rpath fun s => segDriver γ₀ s) (Icc 0 q₂) := Ito.clampDrv_eqOn
  have hW₁0 : W₁ 0 = 0 := by
    rw [heq₁ ⟨le_rfl, q₂.coe_nonneg⟩]
    simpa only [Ito.rpath, Real.toNNReal_zero] using hγ.segDriver_spec.1
  have hLT := Theorem14.CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace (hγ.isGeneratingTrace hq₂)
  have hLT₁ : IsLoewnerTraceLT W₁ q₂ (fun s : ℝ => capTrace γ₀ s.toNNReal) :=
    ⟨hLT.1, hLT.2.1, fun s hs hsq => by
      rw [← hLT.2.2 s hs hsq]
      exact fwdHull_eq_of_eqOn hs hsq fun r hr => heq₁ hr⟩
  set q₁ : ℝ := ((q : ℝ) + q₂) / 2
  have hqq₁ : (q : ℝ) < q₁ := by dsimp [q₁]; linarith
  have hq₁q₂ : q₁ < q₂ := by dsimp [q₁]; linarith
  have hq₁0 : 0 ≤ q₁ := q.coe_nonneg.trans hqq₁.le
  refine ⟨YuanCorollary13.extDrive W₁ q₁, YuanCorollary13.extTrace W₁ (fun s : ℝ => capTrace γ₀ s.toNNReal) q₁, q₁,
    hqq₁, YuanCorollary13.continuous_extDrive hW₁, YuanCorollary13.extDrive_zero hW₁0 hq₁0,
    hLT₁.isLoewnerTrace_ext hW₁ hW₁0 hq₁0 hq₁q₂, fun s hs => ?_⟩
  rw [YuanCorollary13.extDrive_eq hs.2]
  exact (heq₁ ⟨hs.1, hs.2.trans hq₁q₂.le⟩).symm

/-- **The side agreement at the left stop from the seed-interval landings alone** (one sample, generic pocket
shape). Let the relative chart at every capacity `q' ≤ q` have domain `C ∩ (ℍ ∖ K_{T(q')})` for a stop function `T`
whose values at smaller capacities approach `T(q)` from below, and let every coordinate of the open seed interval at
`q` land in `ℍ`. Then at every coordinate `u` of that interval every real limit `y` of `f_{T(q)} ∘ cur⁻¹` satisfies
`u < 0 ↔ y < 0`. No freshness of the tip is used: an anchor near `0` with small ambient value is a coordinate whose
landing is new after `T(q')` (`exists_trMap_mem_H`), and its ambient value is bounded by the increment
(`norm_le_of_tendsto_increment`). -/
theorem curSide_of_seedLand {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) (hc : (c ω).IsConformal) (hγ : IsDrivenCurve (γ ω)) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hq0 : 0 < q) {E : ℂ → ℂ} (hE : EqOn E (c ω).2.1 H)
    (hEc : ContinuousOn E Hbar) {C : Set ℂ} (hcdom : ((c ω).dom : Set ℂ) = C) {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ≥0 → ℝ} (hT0 : ∀ q', 0 ≤ T q')
    (hdomq : ∀ q' : ℝ≥0, q' ≤ q → ((relChart c γ q' ω).dom : Set ℂ) = C ∩ (H \ fwdHull W (T q')))
    (hsel : ∀ t₀ < T q, ∃ q' : ℝ≥0, q' < q ∧ t₀ < T q' ∧ T q' ≤ T q)
    (hN1 : ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
      (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q),
      extendFrom H (relChart c γ q ω).2.1 u ∈ H) :
    ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
      (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q), ∀ y : ℝ,
      Tendsto (fun z => fwdMap W (T q) ((relChart c γ q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) →
        (u < 0 ↔ y < 0) := by
  set I := Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
    (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q) with hI
  have hTq := hT0 q
  have hcur := PocketStopSide.isConformal_relChart_of_driven (c := c) hγ hq hc
  obtain ⟨Fc, hFc, hFcc, -⟩ := PocketStopSide.exists_relative_inverse_extension (c := c) (γ := γ) hγ hq hE hEc
  have hdq := hdomq q le_rfl
  have hK : ((relChart c γ q ω).dom : Set ℂ) ⊆ H \ fwdHull W (T q) := by rw [hdq]; exact inter_subset_right
  have hKo := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hTq
  have hland : ∀ u ∈ I, Fc u ∈ fwdHull W (T q) := by
    intro u hu
    obtain ⟨hlim, hFu⟩ := R5Lift.tendsto_of_ext hFc hFcc u
    refine R5Lift.landing_mem_hull_of_mem_seed_interval hxL hxR hc hγ hq hq0 hE hEc hcdom hKo hdq hu hlim ?_
    rw [hFu]; exact hN1 u hu
  -- the relative chain as a continuous Loewner trace
  obtain ⟨V, γ₁, q₁, hqq₁, hV, hV0, htr, hVeq⟩ := exists_isLoewnerTrace_of_driven hγ hq
  have hrel : ∀ q' : ℝ≥0, q' ≤ q → relChart c γ q' ω = (c ω).loewner V q' := fun q' hq' =>
    loewner_congr (c ω) q'.coe_nonneg (lt_of_le_of_lt (NNReal.coe_le_coe.2 hq') hqq₁) hVeq
  have hEqV : EqOn (fun r : ℝ => (fun t ω => segDriver (γ ω) t) r.toNNReal ω) V (Icc 0 (q : ℝ)) :=
    fun r hr => hVeq r ⟨hr.1, hr.2.trans hqq₁.le⟩
  obtain ⟨hLeq, hReq⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver (γ ω) t) xL xR hV hEqV
  have hL' := congrFun hLeq 0
  have hR' := congrFun hReq 0
  simp only [hxL, hxR, neg_zero] at hL' hR'
  have hB := htr.hasBdryLimits hV hV0 q.coe_nonneg
  have hout : ∀ u : ℝ, u ∉ I → extendFrom H (fwdMapInv V q) u ∉ H := by
    intro u hu hmem
    apply hu
    rw [hI, hL', hR']
    exact ⟨SideHeight.neg_rightImg_sub_lt_of_extendFrom_mem_H' hB hV hV0 q.coe_nonneg hmem,
      SideHeight.lt_rightImg_sub_of_extendFrom_mem_H' hB hV hV0 q.coe_nonneg hmem⟩
  -- the anchor
  have hanch : ∀ ε > 0, ∀ δ > 0, ∃ u ∈ I, |u| < δ ∧ ∀ y : ℝ,
      Tendsto (fun z => fwdMap W (T q) ((relChart c γ q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) → |y| < ε := by
    intro ε hε δ hδ
    obtain ⟨η₀, hη₀, hWc⟩ := Metric.continuous_iff.1 hW (T q) (ε / 100) (by positivity)
    set κ := min η₀ ((ε / 100) ^ 2) with hκ
    have hκ0 : 0 < κ := lt_min hη₀ (by positivity)
    have hκ1 := min_le_left η₀ ((ε / 100) ^ 2)
    have hκ2 := min_le_right η₀ ((ε / 100) ^ 2)
    obtain ⟨q', hq'q, ht₀, hTq'⟩ := hsel (T q - κ / 2) (by linarith)
    have hq'q' : (q' : ℝ) < q := by exact_mod_cast hq'q
    have hq'live : (q' : ℝ≥0∞) < capLife (γ ω) := lt_trans (by exact_mod_cast hq'q) hq
    have hM : ∀ r ∈ Icc (0 : ℝ) (T q - T q'), |W (T q' + r) - W (T q')| ≤ ε / 50 := by
      intro r hr
      have h1 : dist (T q' + r) (T q) < η₀ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2]
      have h2 : dist (T q') (T q) < η₀ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have e1 := hWc _ h1
      have e2 := hWc _ h2
      rw [Real.dist_eq] at e1 e2
      calc |W (T q' + r) - W (T q')| = |(W (T q' + r) - W (T q)) - (W (T q') - W (T q))| := by ring_nf
        _ ≤ |W (T q' + r) - W (T q)| + |W (T q') - W (T q)| := abs_sub _ _
        _ ≤ ε / 50 := by linarith
    have hsq : Real.sqrt (T q - T q') ≤ ε / 100 := by
      have h1 : Real.sqrt (T q - T q') ≤ Real.sqrt ((ε / 100) ^ 2) := Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_sq (by positivity)] at h1
    obtain ⟨u, hu, huδ, hgH⟩ := exists_trMap_mem_H htr hV hV0 q'.coe_nonneg hq'q' hout hδ
    refine ⟨u, hu, huδ, fun y hy => ?_⟩
    have hcur' := PocketStopSide.isConformal_relChart_of_driven (c := c) hγ hq'live hc
    set w₀ := trMap V q' q u with hw₀
    set p := (relChart c γ q' ω).2.1 w₀ with hp
    have hpdom : p ∈ ((relChart c γ q' ω).dom : Set ℂ) := hcur'.inv_mem_dom hgH
    rw [hdomq q' hq'q.le] at hpdom
    have hpH : p ∈ H := hpdom.2.1
    have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
    have hlimp : Tendsto (relChart c γ q ω).2.1 (𝓝[H] (u : ℂ)) (𝓝 p) := by
      have h1 : Tendsto (trMap V q' q) (𝓝[H] (u : ℂ)) (𝓝[H] w₀) := tendsto_nhdsWithin_iff.2
        ⟨((trMap_continuousOn htr hV hV0 q'.coe_nonneg hq'q'.le _ hubar).mono QuantumZipper.H_subset_Hbar).tendsto,
          eventually_nhdsWithin_of_forall fun z hz => trMap_mem_H hV hq'q'.le hz⟩
      have h2 : ContinuousWithinAt (relChart c γ q' ω).2.1 H w₀ := hcur'.1.continuousOn w₀ hgH
      refine (h2.tendsto.comp h1).congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
      simp only [Function.comp_apply]
      rw [hrel q le_rfl, hrel q' hq'q.le]
      show (c ω).2.1 (fwdMapInv V q' (trMap V q' q z)) = (c ω).2.1 (fwdMapInv V q z)
      rw [trMap_eq_fwdMapInv hV hq'q'.le hz,
        ← QuantumZipper.RS.fwdMapInv_add_shift hV hV0 q'.coe_nonneg (sub_nonneg.2 hq'q'.le) hz, add_sub_cancel]
    have hpT : p ∈ fwdHull W (T q) :=
      R5Lift.landing_mem_hull_of_mem_seed_interval hxL hxR hc hγ hq hq0 hE hEc hcdom hKo hdq hu hlimp hpH
    have hF : ∀ᶠ z in 𝓝[H] (u : ℂ), (relChart c γ q ω).2.1 z ∈ H \ fwdHull W (T q) :=
      eventually_nhdsWithin_of_forall fun z hz => hK (hcur.inv_mem_dom hz)
    have := R5Lift.nhdsWithin_H_neBot u
    have hb := norm_le_of_tendsto_increment hW (hT0 q') hTq' hM hF hlimp hpdom.2 hpT hy
    rw [Complex.norm_real, Real.norm_eq_abs] at hb
    linarith
  exact side_of_anchor hcur hFc hFcc hη hW hW0 hTq hK hland hanch

end Sample

end InteractingSLE.Sec7.R5Fresh
