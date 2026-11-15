/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71OMeas
import InteractingSLE.Spec.ZhanGT4.RealTip
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import InteractingSLE.Spec.ZhanGT4.CollarBoundary
import InteractingSLE.Spec.Sec7.Lemma76EJunction
import InteractingSLE.Spec.Restart.ChartDataFibre
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite

/-!
# Lemma 7.1's (CS), geometric half: where the time-`t` inverse map lands

Packet PROVE-LEMMA71P (specification Remark 6.7, `source/spec/p145-192.md` L566–L590; Lemma 7.1,
`source/spec/p193-240.md` L576–L606). Deterministic facts about a continuous Loewner trace `η` of a driver `W` at a time
`t`, with `F̄_t` the boundary extension of `f_t⁻¹ = fwdMapInv W t`:

* `exists_isForwardSol_of_notMem`: a real value `F̄_t(x)` off the trace prefix is an alive real point whose flow ends at
  `x` (a half disc around it misses the hull);
* **`mem_image_of_mid`**: at every real `x` strictly between the images `L_t − W_t` of `0⁻` and `R_t − W_t` of `0⁺`,
  `F̄_t(x)` lies on the trace prefix `η([0, t])`;
* **`eq_zero_of_extendFrom_eq_tip`**: if `η` is injective on `[0, t]`, the tip `η(t)` is sent only by `0`
  (`Restart.eq_of_apply_eq_of_linked`, the singleton-fibre lemma; also for a real tip);
* **`exists_mem_H_of_lt`**: if moreover the real times of `η` on `[0, t]` have empty interior, every open real interval
  of middle points contains a point `z` with `F̄_t(z) ∈ ℍ`;
* **`exists_loewnerTrace`**: a segment curve below its terminal capacity time is, in the capacity parametrization, the
  trace of a continuous driver agreeing with its canonical driver up to `t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71P

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd IsForwardSol)
open MartChar.RealFlow

section Mid

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ}

/-- The boundary extension of `f_t⁻¹` takes values in `ℍ̄`. -/
theorem extendFrom_mem_Hbar (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ Hbar) : extendFrom H (fwdMapInv W t) x ∈ Hbar := by
  have : (𝓝[H] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hx)
  rw [← closure_H]
  exact mem_closure_of_tendsto ((hη.hasBdryLimits hW hW0 ht).tendsto hx)
    (eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hy)

/-- **A real boundary value off the trace prefix is an alive point.** If `F̄_t(x)` is real and not on `η([0, t])`,
then it is a real point `ξ ≠ 0` with a forward solution on `[0, t]` ending at `x`: a half disc around `ξ` misses the
prefix, meets `ℍ ∖ K_t` (it is a limit of points `f_t⁻¹(y)`), hence lies in the unbounded component, i.e. misses
`K_t`. -/
theorem exists_isForwardSol_of_notMem (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    {x : ℝ} (him : (extendFrom H (fwdMapInv W t) x).im = 0)
    (hnot : extendFrom H (fwdMapInv W t) x ∉ η '' Icc 0 t) :
    ∃ v : ℝ → ℂ, IsForwardSol W ((extendFrom H (fwdMapInv W t) x).re : ℂ) t v ∧ v t = x ∧
      (extendFrom H (fwdMapInv W t) x).re ≠ 0 := by
  set p := extendFrom H (fwdMapInv W t) x with hp
  set A := η '' Icc 0 t with hA
  have hAc : IsCompact A := hη.isCompact_image t
  have hAne : A.Nonempty := ⟨η 0, 0, ⟨le_rfl, ht⟩, rfl⟩
  have hpr : p = ((p.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hxH : ((x : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hNe : (𝓝[H] ((x : ℝ) : ℂ)).NeBot := Lemma71O.nhdsWithin_H_ofReal_neBot x
  have hlim : Tendsto (fwdMapInv W t) (𝓝[H] ((x : ℝ) : ℂ)) (𝓝 p) := (hη.hasBdryLimits hW hW0 ht).tendsto hxH
  have hr0 : 0 < infDist p A := (hAc.isClosed.notMem_iff_infDist_pos hAne).1 hnot
  set r := infDist p A with hr
  have hpcl : p ∈ closure (H \ fwdHull W t) := mem_closure_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hy)
  obtain ⟨z₀, hz₀, hz₀b⟩ := Metric.mem_closure_iff.1 hpcl r hr0
  set B := ball p r ∩ H with hB
  have hBc : IsPreconnected B := ((convex_ball p r).inter convex_H).isPreconnected
  have hBA : B ⊆ H \ A := fun w hw => ⟨hw.2, fun hwA => by
    have h1 := infDist_le_dist_of_mem hwA (x := p)
    have h2 := mem_ball.1 hw.1
    rw [dist_comm] at h2
    linarith⟩
  have hz₀B : z₀ ∈ B := ⟨mem_ball.2 (by rwa [dist_comm]), hz₀.1⟩
  have hBsub : B ⊆ connectedComponentIn (H \ A) z₀ := hBc.subset_connectedComponentIn hz₀B hBA
  have hunb : ¬ Bornology.IsBounded (connectedComponentIn (H \ A) z₀) := by
    intro hb
    apply hz₀.2
    rw [hη.2.2 t ht]
    exact ⟨hz₀.1, Or.inr (by rwa [hAc.isClosed.closure_eq])⟩
  have hdisj : Disjoint (ball p r) (fwdHull W t) := by
    rw [Set.disjoint_left]
    intro w hw hwK
    rw [hη.2.2 t ht] at hwK
    have hwB : w ∈ B := ⟨hw, hwK.1⟩
    rcases hwK.2 with hcl | hbd
    · rw [hAc.isClosed.closure_eq] at hcl
      exact (hBA hwB).2 hcl
    · rw [hAc.isClosed.closure_eq, ← connectedComponentIn_eq (hBsub hwB)] at hbd
      exact hunb hbd
  have hp0 : p.re ≠ 0 := fun h => hnot ⟨0, ⟨le_rfl, ht⟩, by rw [hη.1, hpr, h]; simp⟩
  have hball : Disjoint (ball ((p.re : ℝ) : ℂ) r) (fwdHull W t) := by rwa [← hpr]
  obtain ⟨v, hv⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 hp0 ht hr0 hball
  refine ⟨v, hv, ?_, hp0⟩
  have h1 : Tendsto (fwdMap W t) (𝓝[H] ((p.re : ℝ) : ℂ)) (𝓝 (v t)) := tendsto_fwdMap_of_isForwardSol hW ht hv
  have h2 : Tendsto (fwdMapInv W t) (𝓝[H] ((x : ℝ) : ℂ)) (𝓝[H] ((p.re : ℝ) : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨by rw [← hpr]; exact hlim,
      eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hy⟩
  have h4 : Tendsto (fun y => fwdMap W t (fwdMapInv W t y)) (𝓝[H] ((x : ℝ) : ℂ)) (𝓝 ((x : ℝ) : ℂ)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun y hy =>
      (QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht hy).symm)
  exact tendsto_nhds_unique (h1.comp h2) h4

/-- **The middle chart points land on the trace prefix.** At every real `x` strictly between the image
`L_t − W_t` of `0⁻` and the image `R_t − W_t` of `0⁺`, the boundary value `F̄_t(x)` lies on `η([0, t])`: an interior
value is a boundary point of `ℍ ∖ K_t` inside `K_t` (`ZhanGT4.mem_image_of_mem_fwdHull_of_mem_closure`), and a real
value off the prefix would be an alive point whose image lies outside `[L_t − W_t, R_t − W_t]`. -/
theorem mem_image_of_mid (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {x : ℝ}
    (hxL : -rightImg (fun s => -W s) 0 t - W t < x) (hxR : x < rightImg W 0 t - W t) :
    extendFrom H (fwdMapInv W t) x ∈ η '' Icc 0 t := by
  by_contra hnot
  set p := extendFrom H (fwdMapInv W t) x with hp
  have hpHb : p ∈ Hbar := extendFrom_mem_Hbar hη hW hW0 ht (mem_Hbar_of_im_eq_zero (by simp))
  rcases (show (0 : ℝ) ≤ p.im from hpHb).eq_or_lt with h0 | hpos
  · obtain ⟨v, hv, hvt, hp0⟩ := exists_isForwardSol_of_notMem hη hW hW0 ht h0.symm hnot
    have hfv := fwdMap_eq_of_isForwardSol hW hv ⟨ht, le_rfl⟩
    rcases lt_or_gt_of_ne hp0 with hneg | hpos'
    · have hWn : Continuous fun s => -W s := hW.neg
      obtain ⟨u, hu⟩ := (exists_isForwardSol_neg_iff (W := W)).2 ⟨v, hv⟩
      have halive : Alive (fun s => -W s) (-p.re) t :=
        Lemma76E.alive_of_isForwardSol hWn ht (show -W 0 < -p.re by rw [hW0]; linarith) hu
      have h1 := rightImg_le_gImg hWn ht (show (0 : ℝ) < -p.re by linarith) halive
      have hf := fwdMap_eq_of_isForwardSol hWn (WangWu.isForwardSol_of_alive hWn halive) ⟨ht, le_rfl⟩
      have hn := fwdMap_neg_real hW hv ⟨ht, le_rfl⟩
      have hc : (cflow (fun s => -W s) (-p.re) t : ℂ) = ((-x : ℝ) : ℂ) := by
        rw [← hf, hn, hfv, hvt]; push_cast; ring
      have hc' : cflow (fun s => -W s) (-p.re) t = -x := by exact_mod_cast hc
      simp only [gImg] at h1
      linarith
    · have halive : Alive W p.re t := Lemma76E.alive_of_isForwardSol hW ht (by rw [hW0]; exact hpos') hv
      have h1 := rightImg_le_gImg hW ht hpos' halive
      have hf := fwdMap_eq_of_isForwardSol hW (WangWu.isForwardSol_of_alive hW halive) ⟨ht, le_rfl⟩
      have hc : (cflow W p.re t : ℂ) = ((x : ℝ) : ℂ) := by rw [← hf, hfv, hvt]
      have hc' : cflow W p.re t = x := by exact_mod_cast hc
      simp only [gImg] at h1
      linarith
  · obtain ⟨hK, hcl⟩ := ZhanGT4.extendFrom_mem_fwdHull hη hW hW0 ht hpos
    exact hnot (ZhanGT4.mem_image_of_mem_fwdHull_of_mem_closure hη ht hK hcl)

/-- The boundary extension moves points of `ℍ̄` by a bounded amount. -/
theorem exists_norm_extendFrom_sub_le' (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ w ∈ Hbar, ‖extendFrom H (fwdMapInv W t) w - w‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 ht
  refine ⟨C, fun w hw => ?_⟩
  have : (𝓝[H] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hw)
  have hlim := (hη.hasBdryLimits hW hW0 ht).tendsto hw
  have h2 : Tendsto (fun y => ‖fwdMapInv W t y - y‖) (𝓝[H] w) (𝓝 ‖extendFrom H (fwdMapInv W t) w - w‖) :=
    (hlim.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm
  exact le_of_tendsto h2 (eventually_nhdsWithin_of_forall fun y hy => hC y hy)

/-- **The tip is a single prime end.** If `η` is injective on `[0, t]`, the only real point sent to the tip `η(t)` by
`F̄_t` is `0` (`Restart.eq_of_apply_eq_of_linked`: every point of `ℝ ∪ η([0, t])` other than the tip is joined to the
real line inside `η([0, s])`, `s < t`, avoiding the tip). The tip may be real. -/
theorem eq_zero_of_extendFrom_eq_tip (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hi : InjOn η (Icc 0 t)) {x : ℝ} (hx : extendFrom H (fwdMapInv W t) x = η t) : x = 0 := by
  set F := extendFrom H (fwdMapInv W t) with hFdef
  set A := η '' Icc 0 t with hA
  have hAc : IsCompact A := hη.isCompact_image t
  have h0 : F ((0 : ℝ) : ℂ) = η t := by rw [ofReal_zero]; exact ZhanGT4.extendFrom_zero_eq hη hW hW0 ht
  obtain ⟨hFd, hFc, hFi, -⟩ := hη.fiber_hyps hW hW0 ht
  have hFeq : EqOn F (fwdMapInv W t) H := fun w hw => ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 ht hw
  have hDo : IsOpen (H \ fwdHull W t) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht
  have hFD : MapsTo F H (H \ fwdHull W t) := fun w hw => by
    rw [hFeq hw]; exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hw
  have hFs : SurjOn F H (H \ fwdHull W t) := (isConformalBijection_fwdMapInv hW hW0 ht).2.surjOn.congr hFeq.symm
  have hFbd : MapsTo F (Hbar \ H) (frontier (H \ fwdHull W t)) := by
    intro w hw
    have him : w.im = 0 := le_antisymm (not_lt.1 hw.2) hw.1
    rw [hDo.frontier_eq]
    refine ⟨?_, hη.extendFrom_not_mem hW hW0 ht him⟩
    have : (𝓝[H] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hw.1)
    exact mem_closure_of_tendsto ((hη.hasBdryLimits hW hW0 ht).tendsto hw.1)
      (eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hy)
  have hFinf : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) := by
    obtain ⟨C, hC⟩ := exists_norm_extendFrom_sub_le' hη hW hW0 ht
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    have hn : Tendsto (fun w : ℂ => ‖w‖ - C) (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
    refine tendsto_atTop_mono' _ ?_ hn
    filter_upwards [mem_inf_of_right (mem_principal_self Hbar)] with w hw
    have h1 := hC w hw
    have h2 := norm_sub_norm_le w (F w)
    rw [norm_sub_rev] at h1
    linarith
  have hDE : Disjoint (H \ fwdHull W t) ({z : ℂ | z.im = 0} ∪ A) := by
    refine Set.disjoint_left.2 fun z hz hzE => ?_
    rcases hzE with h | h
    · exact (ne_of_gt (show 0 < z.im from hz.1)) h
    · apply hz.2
      rw [hη.2.2 t ht]
      exact ⟨hz.1, Or.inl (subset_closure h)⟩
  have hfr : frontier (H \ fwdHull W t) ⊆ {z : ℂ | z.im = 0} ∪ A := by
    rw [hη.2.2 t ht]
    have := frontier_H_diff_fillH_subset hAc.isBounded (A := A)
    rwa [hAc.isClosed.closure_eq] at this
  have hq : Restart.IsUnboundedLinked (({z : ℂ | z.im = 0} ∪ A) \ {η t}) := by
    refine Restart.isUnboundedLinked_of_forall fun z hz hzq => ?_
    obtain ⟨s, hs, rfl⟩ := hz
    have hst : s < t := lt_of_le_of_ne hs.2 fun h => hzq (by rw [h])
    refine ⟨η '' Icc 0 s, image_mono (Icc_subset_Icc_right hst.le),
      isPreconnected_Icc.image _ (hη.2.1.mono fun u hu => hu.1), ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩, ?_,
      η 0, ⟨0, ⟨le_rfl, hs.1⟩, rfl⟩, by rw [hη.1]; simp⟩
    rintro ⟨u, hu, he⟩
    have := hi ⟨hu.1, hu.2.trans hst.le⟩ ⟨ht, le_rfl⟩ he
    linarith [hu.2]
  exact Restart.eq_of_apply_eq_of_linked hDo hFd hFc hFi hFD hFs hFbd hFinf hDE hfr hq hx h0

/-- **A middle interval contains a point landing off the real line.** If `η` is injective on `[0, t]` and every open
time interval inside `[0, t]` contains a time where `η` is off the real line, then every open real interval `(a, b)` of
chart points landing on the trace prefix contains a point `z` with `F̄_t(z) ∈ ℍ`: otherwise `F̄_t` maps `(a, b)` into
the real points of the prefix; it is not constant there (`exists_ne_of_injOn`), so the real values fill an interval,
whose time preimage (through the closed embedding `η|[0, t]`) is a nondegenerate interval of real times. -/
theorem exists_mem_H_of_lt (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hi : InjOn η (Icc 0 t)) (hint : ∀ a b : ℝ, a < b → Ioo a b ⊆ Icc 0 t → ∃ u ∈ Ioo a b, (η u).im ≠ 0)
    {a b : ℝ} (hab : a < b) (hmid : ∀ z ∈ Ioo a b, extendFrom H (fwdMapInv W t) z ∈ η '' Icc 0 t) :
    ∃ z ∈ Ioo a b, extendFrom H (fwdMapInv W t) z ∈ H := by
  by_contra hcon
  push Not at hcon
  set F := extendFrom H (fwdMapInv W t) with hFdef
  obtain ⟨hFd, hFc, hFi, -⟩ := hη.fiber_hyps hW hW0 ht
  have hreal : ∀ z ∈ Ioo a b, (F z).im = 0 := fun z hz =>
    le_antisymm (not_lt.1 (hcon z hz)) (extendFrom_mem_Hbar hη hW hW0 ht (mem_Hbar_of_im_eq_zero (by simp)))
  have hFr : ∀ z ∈ Ioo a b, F z = (((F z).re : ℝ) : ℂ) := fun z hz => Complex.ext (by simp) (by simp [hreal z hz])
  set m₀ := (a + b) / 2 with hm₀
  have hm₀I : m₀ ∈ Ioo a b := ⟨by rw [hm₀]; linarith, by rw [hm₀]; linarith⟩
  obtain ⟨m, hm, hne⟩ := exists_ne_of_injOn hFd hFc hFi hab (F m₀)
  -- the real values fill an interval
  have hSc : IsPreconnected ((fun z : ℝ => (F z).re) '' Ioo a b) := by
    refine isPreconnected_Ioo.image _ ?_
    refine Complex.continuous_re.comp_continuousOn (hFc.comp Complex.continuous_ofReal.continuousOn ?_)
    exact fun z _ => mem_Hbar_of_im_eq_zero (by simp)
  set c₁ := (F m₀).re with hc₁
  set c₂ := (F m).re with hc₂
  have hne' : F m ≠ F m₀ := hne
  have hc12 : c₁ ≠ c₂ := fun h => hne' (by
    rw [hFr m hm, hFr m₀ hm₀I]; exact congrArg (fun r : ℝ => (r : ℂ)) h.symm)
  have hI : Icc (min c₁ c₂) (max c₁ c₂) ⊆ (fun z : ℝ => (F z).re) '' Ioo a b := by
    refine hSc.Icc_subset ?_ ?_
    · rcases le_total c₁ c₂ with h | h
      · rw [min_eq_left h]; exact ⟨m₀, hm₀I, rfl⟩
      · rw [min_eq_right h]; exact ⟨m, hm, rfl⟩
    · rcases le_total c₁ c₂ with h | h
      · rw [max_eq_right h]; exact ⟨m, hm, rfl⟩
      · rw [max_eq_left h]; exact ⟨m₀, hm₀I, rfl⟩
  have hIA : ∀ y ∈ Icc (min c₁ c₂) (max c₁ c₂), ((y : ℝ) : ℂ) ∈ η '' Icc 0 t := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hI hy
    rw [← hFr z hz]
    exact hmid z hz
  -- the time preimage through the closed embedding `η|[0, t]`
  set f : Icc (0 : ℝ) t → ℂ := fun u => η u with hfdef
  have hfc : Continuous f := continuousOn_iff_continuous_domRestrict.1 (hη.2.1.mono Icc_subset_Ici_self)
  have hfi : Function.Injective f := fun u v h => Subtype.ext (hi u.2 v.2 h)
  have : CompactSpace (Icc (0 : ℝ) t) := isCompact_iff_compactSpace.1 isCompact_Icc
  have hemb := hfc.isClosedEmbedding hfi
  set J : Set ℂ := (fun y : ℝ => (y : ℂ)) '' Icc (min c₁ c₂) (max c₁ c₂) with hJ
  have hJc : IsPreconnected J := isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
  have hfJ : f '' (f ⁻¹' J) = J := by
    refine image_preimage_eq_of_subset fun w hw => ?_
    obtain ⟨y, hy, rfl⟩ := hw
    obtain ⟨u, hu, hue⟩ := hIA y hy
    exact ⟨⟨u, hu⟩, hue⟩
  have hsc : IsPreconnected (f ⁻¹' J) := hemb.isInducing.isPreconnected_image.1 (by rw [hfJ]; exact hJc)
  have hTc : IsPreconnected ((Subtype.val : Icc (0 : ℝ) t → ℝ) '' (f ⁻¹' J)) :=
    hsc.image _ continuous_subtype_val.continuousOn
  have hpt : ∀ y ∈ Icc (min c₁ c₂) (max c₁ c₂), ∃ u ∈ (Subtype.val : Icc (0 : ℝ) t → ℝ) '' (f ⁻¹' J),
      η u = ((y : ℝ) : ℂ) := by
    intro y hy
    obtain ⟨u, hu, hue⟩ := hIA y hy
    exact ⟨u, ⟨⟨u, hu⟩, show f ⟨u, hu⟩ ∈ J from ⟨y, hy, hue.symm⟩, rfl⟩, hue⟩
  obtain ⟨u₁, hu₁T, hu₁⟩ := hpt c₁ ⟨min_le_left _ _, le_max_left _ _⟩
  obtain ⟨u₂, hu₂T, hu₂⟩ := hpt c₂ ⟨min_le_right _ _, le_max_right _ _⟩
  have hu12 : u₁ ≠ u₂ := fun h => hc12 (by
    have := hu₁.symm.trans ((congrArg η h).trans hu₂)
    exact_mod_cast this)
  have hTsub : Icc (min u₁ u₂) (max u₁ u₂) ⊆ (Subtype.val : Icc (0 : ℝ) t → ℝ) '' (f ⁻¹' J) := by
    refine hTc.Icc_subset ?_ ?_
    · rcases le_total u₁ u₂ with h | h
      · rw [min_eq_left h]; exact hu₁T
      · rw [min_eq_right h]; exact hu₂T
    · rcases le_total u₁ u₂ with h | h
      · rw [max_eq_right h]; exact hu₂T
      · rw [max_eq_left h]; exact hu₁T
  have hlt : min u₁ u₂ < max u₁ u₂ := by
    rcases lt_or_gt_of_ne hu12 with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  have hIoo : Ioo (min u₁ u₂) (max u₁ u₂) ⊆ Icc 0 t := fun u hu => by
    obtain ⟨⟨v, hv⟩, -, rfl⟩ := hTsub (Ioo_subset_Icc_self hu)
    exact hv
  obtain ⟨u, hu, hune⟩ := hint _ _ hlt hIoo
  obtain ⟨⟨v, hv⟩, hvJ, rfl⟩ := hTsub (Ioo_subset_Icc_self hu)
  obtain ⟨y, -, hy⟩ := hvJ
  exact hune (by rw [show η v = f ⟨v, hv⟩ from rfl, ← hy]; simp)

end Mid

/-! ### The mapped segment as a Loewner trace -/

section Seg

open Lemma71C PocketTraversal

variable {γ' : ℝ → ℂ}

/-- The capacity inverse is strictly increasing below the terminal capacity time. -/
theorem capInv_lt_capInv (hΓ : IsSegCurve γ') {s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s')
    (hs' : ENNReal.ofReal s' < capLife γ') : capInv γ' s < capInv γ' s' := by
  have hd := isDrivenCurve_of_isSegCurve hΓ
  have hs'' : ENNReal.ofReal s < capLife γ' := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hss'.le) hs'
  obtain ⟨h0, h1⟩ := hd.capInv_spec hs hs''
  obtain ⟨h0', h1'⟩ := hd.capInv_spec (hs.trans hss'.le) hs'
  by_contra hle
  have := hd.strictMonoOn_capClock.monotoneOn h0' h0 (not_lt.1 hle)
  rw [h1, h1'] at this
  linarith

/-- **The mapped segment is a Loewner trace up to `t`**: for `t` below the terminal capacity time there are a
continuous driver `W` (`W 0 = 0`) agreeing with the canonical driver on `[0, t]` and a continuous Loewner trace `η` of
`W` with `η s = γ'(capInv s)` on `[0, t]` (the slit extension `YuanCorollary13.extTrace` of the capacity trace). -/
theorem exists_loewnerTrace (hΓ : IsSegCurve γ') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < capLife γ') :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ EqOn W (Ito.rpath fun s => segDriver γ' s) (Icc 0 t) ∧
      ∃ η : ℝ → ℂ, IsLoewnerTrace W η ∧ ∀ s : ℝ, 0 ≤ s → s ≤ t → η s = γ' (capInv γ' s) := by
  set w : ℝ≥0 → ℝ := fun s => segDriver γ' s with hwdef
  have hw : ContinuousOn w {s | (s : ℝ≥0∞) < capLife γ'} := hΓ.segDriver_spec.2.1
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  set W₁ := Ito.clampDrv (Ito.rpath w) t₂ with hW₁
  have hW₁c : Continuous W₁ := Ito.continuous_clampDrv t₂.coe_nonneg (Ito.continuousOn_rpath hw ht₂ζ)
  have hW₁e : EqOn W₁ (Ito.rpath w) (Icc 0 t₂) := Ito.clampDrv_eqOn
  have hW₁0 : W₁ 0 = 0 := by
    rw [hW₁e ⟨le_rfl, t₂.coe_nonneg⟩]
    show w (0 : ℝ).toNNReal = 0
    rw [Real.toNNReal_zero]
    exact hΓ.segDriver_spec.1
  have hgen := (isDrivenCurve_of_isSegCurve hΓ).isGeneratingTrace (T := (t₂ : ℝ≥0∞)) ht₂ζ
  have hLT := Theorem14.CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hgen
  have hLT₁ : IsLoewnerTraceLT W₁ t₂ (fun s : ℝ => capTrace γ' s.toNNReal) :=
    ⟨hLT.1, hLT.2.1, fun s hs hst => by
      rw [← hLT.2.2 s hs hst]
      exact fwdHull_eq_of_eqOn hs hst fun r hr => hW₁e hr⟩
  have hext := hLT₁.isLoewnerTrace_ext hW₁c hW₁0 t.coe_nonneg htt₂'
  refine ⟨YuanCorollary13.extDrive W₁ t, YuanCorollary13.continuous_extDrive hW₁c,
    YuanCorollary13.extDrive_zero hW₁0 t.coe_nonneg, fun r hr => ?_, _, hext, fun s hs hst => ?_⟩
  · rw [YuanCorollary13.extDrive_eq hr.2]
    exact hW₁e ⟨hr.1, hr.2.trans htt₂'.le⟩
  · rw [YuanCorollary13.extTrace_eq hst]
    simp only [capTrace, Real.coe_toNNReal _ hs]

/-- On `[0, t]`, the capacity trace `s ↦ γ'(capInv s)` is injective. -/
theorem injOn_capInv (hΓ : IsSegCurve γ') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < capLife γ') :
    InjOn (fun s => γ' (capInv γ' s)) (Icc 0 t) := by
  intro s hs s' hs' h
  have hlt : ∀ r ∈ Icc (0 : ℝ) t, ENNReal.ofReal r < capLife γ' := fun r hr =>
    lt_of_le_of_lt (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hr.2) ht
  have hu := hΓ.2.1 (capInv_nonneg γ' s) (capInv_nonneg γ' s') h
  have hd := isDrivenCurve_of_isSegCurve hΓ
  rw [← (hd.capInv_spec hs.1 (hlt s hs)).2, ← (hd.capInv_spec hs'.1 (hlt s' hs')).2, hu]

/-- On `[0, t]`, every open time interval contains a time where the capacity trace is off the real line. -/
theorem exists_im_ne_zero (hΓ : IsSegCurve γ') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < capLife γ') {a b : ℝ} (hab : a < b)
    (hI : Ioo a b ⊆ Icc 0 (t : ℝ)) : ∃ u ∈ Ioo a b, (γ' (capInv γ' u)).im ≠ 0 := by
  have hd := isDrivenCurve_of_isSegCurve hΓ
  have ha : 0 ≤ a := by
    by_contra h
    push Not at h
    have hu : min ((a + b) / 2) (a / 2) ∈ Ioo a b :=
      ⟨lt_min (by linarith) (by linarith), lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩
    have := (hI hu).1
    linarith [min_le_right ((a + b) / 2) (a / 2)]
  have hb : b ≤ t := by
    by_contra h
    push Not at h
    have hu : max ((a + b) / 2) ((b + t) / 2) ∈ Ioo a b :=
      ⟨lt_of_lt_of_le (by linarith) (le_max_left _ _), max_lt (by linarith) (by linarith)⟩
    have := (hI hu).2
    linarith [le_max_right ((a + b) / 2) ((b + t) / 2)]
  have hlt : ∀ r, r ≤ (t : ℝ) → ENNReal.ofReal r < capLife γ' := fun r hr =>
    lt_of_le_of_lt (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hr) ht
  have hab' := capInv_lt_capInv hΓ ha hab (hlt b hb)
  have hsub : ¬ Ioo (capInv γ' a) (capInv γ' b) ⊆ {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ' u).im = 0} := by
    intro h
    have h' := interior_mono h
    rw [interior_Ioo, hΓ.2.2.2.2.2] at h'
    exact (nonempty_Ioo.2 hab').ne_empty (subset_empty_iff.1 h')
  obtain ⟨v, hv, hvS⟩ := not_subset.1 hsub
  have hv0 : 0 < v := lt_of_le_of_lt (capInv_nonneg γ' a) hv.1
  have hvim : (γ' v).im ≠ 0 := fun h => hvS ⟨mem_Ici.2 hv0.le, hv0, h⟩
  obtain ⟨hA0, hA1⟩ := hd.capInv_spec ha (hlt a (hab.le.trans hb))
  obtain ⟨hB0, hB1⟩ := hd.capInv_spec (ha.trans hab.le) (hlt b hb)
  have hmono := hd.strictMonoOn_capClock
  refine ⟨capClock γ' v, ⟨?_, ?_⟩, ?_⟩
  · have := hmono hA0 hv0.le hv.1
    rwa [hA1] at this
  · have := hmono hv0.le hB0 hv.2
    rwa [hB1] at this
  · rwa [hd.capInv_eq hv0.le]

end Seg

end InteractingSLE.Sec7.Lemma71P
