/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aInClock
import InteractingSLE.Spec.Supplement.HullDetGenMean
import InteractingSLE.Spec.Restart.FCAux79MeanFlow
import InteractingSLE.Spec.Supplement.BHMeanReal
import InteractingSLE.Foundations.Loewner.YuanFiber

/-!
# BR4a's relative words: the Möbius conjugation at one original time (deterministic)

Packet PROVE-T14-BR4A3 (`BR4aChain.BR4aWordDetStatement`, supplement p. 610, (BR4a.1)–(BR4a.2)). For a continuous
driver `w` from `0`, a relative driver `u` whose hulls are the target-change images `mob v (K_s)` at the relative
times `clock v w s` (`s ≤ t`), and the pole `−1/v` off the closed hull `K_t`:

* **`exists_conj`**: there are real `α`, `κN > 0`, `P` with `P = g_t(−1/v)` (`bdryVal`), the driver correspondence
  `u(q) = N(w(t))` and the conjugation `g̃_q ∘ mob v = N ∘ g_t` on `ℍ ∖ K_t`, `N = nf α κN P`, `q = clock v w t`
  (`Sec5.CrossRestart.exists_loewner_mobius_image`, the drivers identified by `Sec6.eqOn_of_fwdHull_eq`, as in
  `BR4aPath.tipAt_newChart_iff`);
* `tendsto_gmap_of_isForwardSol`, `bdryVal_eq_of_isForwardSol`: `g_t` at a real point with a forward solution;
* `notMem_closure_mob`: real points off the closed hull have images off the closed image hull;
* **`conj_flow`**: at a real point `y` off the closed hull, the forward-solution values satisfy
  `g̃_q(mob v y) = N(g_t(y))`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BR4aIn

open BR4aPath BR4aChain ConformalImage ConformalImageFull Supp8.HullDetGen Sec5.CrossRestart

/-- `𝓝[ℍ] y` is nontrivial at a real point. -/
theorem neBot_nhdsWithin_H (y : ℝ) : (𝓝[H] (y : ℂ)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))

/-- **The conjugation of the relative chain at one original time.** -/
theorem exists_conj {w u : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hu : Continuous u) (hu0 : u 0 = 0)
    {v : ℝ} (hv : v ≠ 0) {t : ℝ} (ht : 0 ≤ t) (hp : ((pole v : ℝ) : ℂ) ∉ closure (fwdHull w t))
    (hK : ∀ s ∈ Icc (0 : ℝ) t, fwdHull u (clock v w s) = mob v '' fwdHull w s) :
    ∃ α κN P : ℝ, 0 < κN ∧ (P : ℂ) = bdryVal w (pole v) t ∧ u (clock v w t) = α - κN / (w t - P) ∧
      ∀ z ∈ H \ fwdHull w t, gmap u (clock v w t) (mob v z) = nf α κN P (gmap w t z) := by
  obtain ⟨r, hr, hd⟩ := exists_disjoint_ball_of_notMem_closure hp
  have hpole : mobPole v 1 ≠ 0 := by
    rw [mobPole_eq]
    simpa [pole] using hv
  have hd' : Disjoint (ball (mobPole v 1 : ℂ) r) (fwdHull w t) := by
    rw [mobPole_eq]
    exact hd
  obtain ⟨σ, W', α, κ, P, hW', hW'0, hσ0, hσm, hσc, hall⟩ :=
    exists_loewner_mobius_image hw hw0 ht (a := 1) (b := 0) (c := v) (d := 1) (by norm_num) hv hpole hr hd'
  have htt : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  obtain ⟨-, -, hdrv, hκ, hP, hmap⟩ := hall t htt
  have hσ : ∀ s ∈ Icc (0 : ℝ) t, σ s = clock v w s := fun s hs => (hall s hs).1
  have hA0 : 0 ≤ clock v w t := by
    rw [← hσ t htt, ← hσ0]
    exact hσm.monotoneOn ⟨le_rfl, ht⟩ htt ht
  have hagree : EqOn W' u (Icc 0 (clock v w t)) := by
    refine Sec6.eqOn_of_fwdHull_eq hW' hu (by simpa using hW'0) hu0 hA0 fun s hs => ?_
    have hsub := intermediate_value_Icc ht hσc
    rw [hσ0, hσ t htt] at hsub
    obtain ⟨s', hs', rfl⟩ := hsub hs
    rw [(hall s' hs').2.1, hσ s' hs', hK s' hs']
    rfl
  have hgmap : ∀ z, gmap W' (clock v w t) z = gmap u (clock v w t) z := fun z => by
    rw [gmap, gmap, fwdMap_eq_of_eqOn hA0 (fun r hr => hagree hr), hagree ⟨hA0, le_rfl⟩]
  refine ⟨α t, κ t, P t, hκ, by rw [hP, mobPole_eq], ?_, fun z hz => ?_⟩
  · rw [← hagree ⟨hA0, le_rfl⟩, ← hσ t htt]
    exact hdrv
  · rw [← hgmap, ← hσ t htt]
    exact hmap z hz

/-- `g_t` tends to the forward-solution value at a point with a forward solution. -/
theorem tendsto_gmap_of_isForwardSol {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {x : ℂ} {f : ℝ → ℂ}
    (hf : QuantumZipper.IsForwardSol w x t f) : Tendsto (gmap w t) (𝓝[H] x) (𝓝 (f t + w t)) :=
  (QuantumZipper.RS.tendsto_fwdMap_of_sol hw ht hf).add_const _

/-- The boundary value of `g_t` at a real point with a forward solution. -/
theorem bdryVal_eq_of_isForwardSol {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {y : ℝ} {f : ℝ → ℂ}
    (hf : QuantumZipper.IsForwardSol w (y : ℂ) t f) : bdryVal w y t = f t + w t := by
  have := neBot_nhdsWithin_H y
  exact (tendsto_gmap_of_isForwardSol hw ht hf).limUnder_eq

/-- `mob v` at a real point. -/
theorem mob_ofReal (v y : ℝ) : mob v (y : ℂ) = ((y / (v * y + 1) : ℝ) : ℂ) := by
  rw [mob_apply]
  push_cast
  rfl

/-- `mob v` tends to `mob v y` within `ℍ` at a real point off the pole. -/
theorem tendsto_mob_nhdsWithin_H {v y : ℝ} (hyp : v * y + 1 ≠ 0) :
    Tendsto (mob v) (𝓝[H] (y : ℂ)) (𝓝[H] (mob v (y : ℂ))) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => mob_mem_H v hz⟩
  have hden : (v : ℂ) * (y : ℂ) + 1 ≠ 0 := by exact_mod_cast hyp
  have hc : ContinuousAt (mob v) (y : ℂ) := (hasDerivAt_mob hden).continuousAt
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-- `−v · mob v z + 1 = 1/(v z + 1)`. -/
theorem neg_mul_mob_add_one {v : ℝ} {z : ℂ} (hden : (v : ℂ) * z + 1 ≠ 0) :
    -(v : ℂ) * (z / ((v : ℂ) * z + 1)) + 1 = 1 / ((v : ℂ) * z + 1) := by
  field_simp
  ring

/-- `mobInv v (mob v y) = y` at a real point off the pole. -/
theorem mobInv_mob_ofReal {v y : ℝ} (hyp : v * y + 1 ≠ 0) : mobInv v (mob v (y : ℂ)) = y := by
  have hden : (v : ℂ) * (y : ℂ) + 1 ≠ 0 := by exact_mod_cast hyp
  rw [mobInv_eq, mob_apply, neg_mul_mob_add_one hden, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ hden]

/-- **Real points off the closed hull have images off the closed image hull.** -/
theorem notMem_closure_mob {w u : ℝ → ℝ} {t q v : ℝ} (hK : mob v '' fwdHull w t = fwdHull u q) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fwdHull w t)) (hyp : v * y + 1 ≠ 0) :
    mob v (y : ℂ) ∉ closure (fwdHull u q) := by
  rw [← hK]
  intro hm
  have hden : (v : ℂ) * (y : ℂ) + 1 ≠ 0 := by exact_mod_cast hyp
  have hden' : -(v : ℂ) * mob v (y : ℂ) + 1 ≠ 0 := by
    rw [mob_apply, neg_mul_mob_add_one hden]
    exact one_div_ne_zero hden
  have hc : ContinuousAt (mobInv v) (mob v (y : ℂ)) := by
    have he : mobInv v = fun z : ℂ => z / (-(v : ℂ) * z + 1) := funext fun z => mobInv_eq v z
    rw [he]
    exact continuousAt_id.div ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hden'
  have h1 := hc.continuousWithinAt.mem_closure_image hm
  rw [mobInv_image_mob_image v ((QuantumZipper.fwdHull_mono).2 t), mobInv_mob_ofReal hyp] at h1
  exact hy h1

/-- **The conjugation at a real point**: if `y` is off the closed hull and off the pole, with forward solutions `f`
(original, from `y`) and `g` (relative, from `mob v y`), and `g_t(y) ≠ P`, then `g̃_q(mob v y) = N(g_t(y))`. -/
theorem conj_flow {w u : ℝ → ℝ} (hw : Continuous w) (hu : Continuous u) {t q v α κN P : ℝ} (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hconj : ∀ z ∈ H \ fwdHull w t, gmap u q (mob v z) = nf α κN P (gmap w t z)) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fwdHull w t)) (hyp : v * y + 1 ≠ 0) {f g : ℝ → ℂ}
    (hf : QuantumZipper.IsForwardSol w (y : ℂ) t f) (hg : QuantumZipper.IsForwardSol u (mob v (y : ℂ)) q g)
    (hfP : f t + w t ≠ (P : ℂ)) : g q + u q = nf α κN P (f t + w t) := by
  have := neBot_nhdsWithin_H y
  have hL : Tendsto (fun z => gmap u q (mob v z)) (𝓝[H] (y : ℂ)) (𝓝 (g q + u q)) :=
    (tendsto_gmap_of_isForwardSol hu hq hg).comp (tendsto_mob_nhdsWithin_H hyp)
  have hnf : ContinuousAt (nf α κN P) (f t + w t) := by
    have he : nf α κN P = fun ζ : ℂ => (α : ℂ) - (κN : ℂ) / (ζ - P) := rfl
    rw [he]
    exact continuousAt_const.sub (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.2 hfP))
  have hR : Tendsto (fun z => nf α κN P (gmap w t z)) (𝓝[H] (y : ℂ)) (𝓝 (nf α κN P (f t + w t))) :=
    hnf.tendsto.comp (tendsto_gmap_of_isForwardSol hw ht hf)
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  have hev : ∀ᶠ z in 𝓝[H] (y : ℂ), z ∉ fwdHull w t := by
    refine (eventually_nhdsWithin_of_eventually_nhds ?_)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz hzK
    exact hz (subset_closure hzK)
  filter_upwards [hev, self_mem_nhdsWithin] with z hzK hzH
  exact (hconj z ⟨hzH, hzK⟩).symm

end InteractingSLE.Theorem14.BR4aIn
