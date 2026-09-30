import QuantumZipper.Proofs.Zipper.JointModDet
import QuantumZipper.Proofs.Zipper.RegUnif

/-!
# UNIF-RC3, deterministic inputs: joint continuity of the double-unzip maps in `(u, s)`

For a continuous driver `W` and `(u, s)` in the time triangle `tri T`, the map of the second
unzipping is `R_{u,s} = revMap (vrev W (u + s)) s` (`RegUnifCocycle.eqOn_fwdMapInv_shift`).

* `continuousOn_revMap_family`: `(t, s, z) ↦ revMap (V t) s z` is jointly continuous on
  `{s ≥ 0, Im z > 0}` for a jointly continuous family of drivers `(t, r) ↦ V t r`
  (Gronwall stability in the driver and in the starting point, `ReverseFlow`, plus continuity in
  time at a fixed point).
* `continuousOn_revMap_vrev`: hence `((u, s), z) ↦ R_{u,s}(z)` is continuous on `tri T × ℍ`.
* `log_norm_deriv_R_eq`: `log |R_{u,s}'| = log |ψ_{u+s}'| − log |ψ_u' ∘ R_{u,s}|` on `ℍ`
  (flow property `RegCont.fwdMapInv_add`, `ψ_t = fwdMapInv W t`).
* `continuousOn_integral_log_deriv_R`: `(u, s) ↦ ∫ log |R_{u,s}'| dfc(w, r)` is continuous on
  `tri T` (dominated convergence with the bound `A + |log Im|`,
  `TwoPoint.abs_log_norm_deriv_revMap_le`).
* `continuousOn_integral_comp_R`: for `G` continuous on `parSet T`,
  `(u, s) ↦ ∫ G(u, R_{u,s}(z), ρ) dfc(w, r)(z)` is continuous on `tri T` (bounded convergence;
  the images `R_{u,s}(z)` stay in a fixed compact subset of `Hbar`, `RegCont.norm_revMap_le_revBound`).

All proofs are **own elementary arguments** (cost rule of `AGENT_GUIDE.md`): Gronwall stability
and dominated convergence; no published source treats these bookkeeping facts.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint UnzipInvariance B2

variable {W : ℝ → ℝ}

/-- **Joint continuity of the reverse maps of a continuous family of drivers.** -/
theorem continuousOn_revMap_family {V : ℝ → ℝ → ℝ}
    (hV : Continuous fun p : ℝ × ℝ => V p.1 p.2) :
    ContinuousOn (fun q : ℝ × ℝ × ℂ => revMap (V q.1) q.2.1 q.2.2)
      {q | 0 ≤ q.2.1 ∧ 0 < q.2.2.im} := by
  rintro ⟨t₀, s₀, z₀⟩ ⟨hs₀, hz₀⟩
  simp only at hs₀ hz₀
  have hVt : ∀ t, Continuous (V t) := fun t => hV.comp (continuous_const.prodMk continuous_id)
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set δ := z₀.im / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set S := s₀ + 1 with hS
  set E := Real.exp (2 * S / δ ^ 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hK : IsCompact (Icc (t₀ - 1) (t₀ + 1) ×ˢ Icc (0 : ℝ) S) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨η₁, hη₁, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hV.continuousOn) (ε / (3 * E)) (by positivity)
  obtain ⟨η₂, hη₂, hTm⟩ := Metric.continuousWithinAt_iff.1
    (ReverseFlow.continuousOn_revMap_time (V t₀) (hVt t₀) z₀ hz₀ s₀ hs₀) (ε / 3) (by positivity)
  set η := min (min η₁ 1) (min η₂ (min δ (ε / (3 * E)))) with hη
  refine ⟨η, by positivity, ?_⟩
  rintro ⟨t, s, z⟩ ⟨hs, hz⟩ hd
  simp only at hs hz
  have hd3 : dist t t₀ < η ∧ dist s s₀ < η ∧ dist z z₀ < η := by
    simpa only [Prod.dist_eq, max_lt_iff] using hd
  obtain ⟨ht, hsd, hzd⟩ := hd3
  have ht1 : dist t t₀ < η₁ := ht.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have ht2 : dist t t₀ < 1 := ht.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hs1 : dist s s₀ < η₂ := hsd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs2 : dist s s₀ < 1 := by
    have := hsd.trans_le ((min_le_left _ _).trans (min_le_right _ _) : η ≤ 1)
    exact this
  have hz1 : dist z z₀ < δ :=
    hzd.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hz2 : dist z z₀ < ε / (3 * E) :=
    hzd.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hzδ : δ ≤ z.im := by
    have h1 : |z.im - z₀.im| ≤ dist z z₀ := by
      rw [dist_eq_norm, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have := (abs_le.1 h1).1
    linarith
  have hz₀δ : δ ≤ z₀.im := by linarith
  have hsS : s ≤ S := by
    have := (abs_lt.1 (show |s - s₀| < 1 by rw [← Real.dist_eq]; linarith)).2
    linarith
  have hexp : ∀ x : ℝ, 0 < x → δ ≤ x → Real.exp (2 * s / x ^ 2) ≤ E := by
    intro x hx hδx
    refine Real.exp_le_exp.2 ?_
    have h1 : δ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hδ0.le hδx 2
    calc 2 * s / x ^ 2 ≤ 2 * S / x ^ 2 := by gcongr
      _ ≤ 2 * S / δ ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) h1
  -- driver term
  have hdrv : ∀ r ∈ Icc (0 : ℝ) s, |V t r - V t₀ r| ≤ ε / (3 * E) := by
    intro r hr
    have hm1 : (t, r) ∈ Icc (t₀ - 1) (t₀ + 1) ×ˢ Icc (0 : ℝ) S := by
      refine ⟨⟨?_, ?_⟩, hr.1, hr.2.trans hsS⟩
      · have := (abs_lt.1 (show |t - t₀| < 1 by rw [← Real.dist_eq]; exact ht2)).1; linarith
      · have := (abs_lt.1 (show |t - t₀| < 1 by rw [← Real.dist_eq]; exact ht2)).2; linarith
    have hm2 : (t₀, r) ∈ Icc (t₀ - 1) (t₀ + 1) ×ˢ Icc (0 : ℝ) S :=
      ⟨⟨by linarith, by linarith⟩, hr.1, hr.2.trans hsS⟩
    have hdd : dist (t, r) (t₀, r) < η₁ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact ht1
    have := hU _ hm1 _ hm2 hdd
    rw [Real.dist_eq] at this
    exact this.le
  have e1 : ‖revMap (V t) s z - revMap (V t₀) s z‖ ≤ ε / 3 := by
    refine (ReverseFlow.norm_revMap_sub_revMap_le (V t) (V t₀) (hVt t) (hVt t₀) z hz hs
      hdrv).trans ?_
    have h2 : Real.exp (2 * s / z.im ^ 2) ≤ E := hexp _ hz hzδ
    calc ε / (3 * E) * Real.exp (2 * s / z.im ^ 2) ≤ ε / (3 * E) * E :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε / 3 := by field_simp
  have e2 : ‖revMap (V t₀) s z - revMap (V t₀) s z₀‖ ≤ ε / 3 := by
    refine (ReverseFlow.norm_revMap_sub_revMap_point (V t₀) (hVt t₀) hδ0 hzδ hz₀δ hs).trans ?_
    have h2 : Real.exp (2 * s / δ ^ 2) ≤ E := hexp δ hδ0 le_rfl
    have h3 : ‖z - z₀‖ ≤ ε / (3 * E) := by rw [← dist_eq_norm]; exact hz2.le
    calc ‖z - z₀‖ * Real.exp (2 * s / δ ^ 2) ≤ ε / (3 * E) * E :=
          mul_le_mul h3 h2 (Real.exp_pos _).le (by positivity)
      _ = ε / 3 := by field_simp
  have e3 : ‖revMap (V t₀) s z₀ - revMap (V t₀) s₀ z₀‖ < ε / 3 := by
    rw [← dist_eq_norm]; exact hTm (show s ∈ Ici (0 : ℝ) from hs) hs1
  rw [dist_eq_norm]
  calc ‖revMap (V t) s z - revMap (V t₀) s₀ z₀‖
      ≤ ‖revMap (V t) s z - revMap (V t₀) s z‖ + ‖revMap (V t₀) s z - revMap (V t₀) s z₀‖ +
          ‖revMap (V t₀) s z₀ - revMap (V t₀) s₀ z₀‖ := by
        have a := norm_sub_le_norm_sub_add_norm_sub (revMap (V t) s z) (revMap (V t₀) s z)
          (revMap (V t₀) s₀ z₀)
        have b := norm_sub_le_norm_sub_add_norm_sub (revMap (V t₀) s z) (revMap (V t₀) s z₀)
          (revMap (V t₀) s₀ z₀)
        linarith
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- `(t, r) ↦ vrev W t r` is jointly continuous. -/
theorem continuous_vrev_joint (hW : Continuous W) :
    Continuous fun p : ℝ × ℝ => vrev W p.1 p.2 := by
  unfold vrev; fun_prop

/-- **`((u, s), z) ↦ R_{u,s}(z)` is continuous on `tri T × ℍ`.** -/
theorem continuousOn_revMap_vrev (hW : Continuous W) (T : ℝ) :
    ContinuousOn (fun q : (ℝ × ℝ) × ℂ => revMap (vrev W (q.1.1 + q.1.2)) q.1.2 q.2)
      (tri T ×ˢ H) :=
  (continuousOn_revMap_family (continuous_vrev_joint hW)).comp
    (f := fun q : (ℝ × ℝ) × ℂ => (q.1.1 + q.1.2, q.1.2, q.2)) (by fun_prop)
    fun q hq => ⟨hq.1.2.1, hq.2⟩

/-- `|vrev W t r| ≤ 2M` for `t ∈ [0, T]` and `|W| ≤ M` on `[0, T]`. -/
theorem abs_vrev_le {T M t : ℝ} (hM : ∀ x ∈ Icc (0 : ℝ) T, |W x| ≤ M) (ht : t ∈ Icc (0 : ℝ) T)
    (r : ℝ) : |vrev W t r| ≤ 2 * M := by
  unfold vrev
  have h1 : 0 ≤ min (max r 0) t := le_min (le_max_right _ _) ht.1
  have h2 : min (max r 0) t ≤ t := min_le_right _ _
  have ha : t - min (max r 0) t ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [ht.2]⟩
  calc |W (t - min (max r 0) t) - W t| ≤ |W (t - min (max r 0) t)| + |W t| := abs_sub _ _
    _ ≤ M + M := add_le_add (hM _ ha) (hM _ ht)
    _ = 2 * M := by ring

/-- **`log |R'|` through the flow property.** -/
theorem log_norm_deriv_R_eq (hW : Continuous W) (hW0 : W 0 = 0) {u s : ℝ} (hu : 0 ≤ u)
    (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ H) :
    Real.log ‖deriv (revMap (vrev W (u + s)) s) z‖ =
      Real.log ‖deriv (fwdMapInv W (u + s)) z‖ -
        Real.log ‖deriv (fwdMapInv W u) (revMap (vrev W (u + s)) s z)‖ := by
  set R := revMap (vrev W (u + s)) s with hR
  have hVc : Continuous (vrev W (u + s)) := continuous_vrev hW _
  have hRz : R z ∈ H := im_revMap_pos hVc hz hs
  have hEq : EqOn (fwdMapInv W (u + s)) (fwdMapInv W u ∘ R) H := by
    intro w hw
    rw [fwdMapInv_add hW hW0 hu hs hw]
    show fwdMapInv W u (revMap (fun r => W (u + s - r) - W (u + s)) s w) =
      fwdMapInv W u (revMap (vrev W (u + s)) s w)
    rw [ReverseFlow.revMap_congr_drive w fun r hr =>
      (vrev_of_mem ⟨hr.1, hr.2.trans (le_add_of_nonneg_left hu)⟩).symm]
  have hFd : DifferentiableAt ℂ (fwdMapInv W u) (R z) :=
    ((differentiableOn_revMap (fun r => W (u - r) - W u) (by fun_prop) hu).differentiableAt
      (isOpen_H.mem_nhds hRz)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hRz)
        fun v hv => fwdMapInv_eq_revMap_timeRev W hW hW0 hu hv)
  have hd : deriv (fwdMapInv W (u + s)) z = deriv (fwdMapInv W u) (R z) * deriv R z := by
    rw [Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hz) hEq)]
    exact deriv_comp z hFd (hasDerivAt_revMap _ hVc hs hz).differentiableAt
  have h1 : deriv (fwdMapInv W u) (R z) ≠ 0 := by
    rw [deriv_fwdMapInv_eq hW hW0 hu hRz]
    exact deriv_revMap_ne_zero _ (continuous_vRev hW u) hu hRz
  have h2 : deriv R z ≠ 0 := deriv_revMap_ne_zero _ hVc hs hz
  rw [hd, norm_mul, Real.log_mul (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2)]
  ring

/-- **Continuity in `(u, s)` of `∫ log |R_{u,s}'| dfc(w, r)`.** -/
theorem continuousOn_integral_log_deriv_R (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) (w : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun p : ℝ × ℝ =>
      ∫ z, Real.log ‖deriv (revMap (vrev W (p.1 + p.2)) p.2) z‖ ∂foldedCircle w r) (tri T) := by
  set R₀ := ‖w‖ + r + 1 with hR₀
  have hR₀1 : 1 ≤ R₀ := by have := norm_nonneg w; linarith
  set A := Real.log (Real.sqrt (R₀ ^ 2 + 4 * |T|)) with hA
  have hsq : ∀ s : ℝ, 0 ≤ s → s ≤ |T| →
      |Real.log (Real.sqrt (R₀ ^ 2 + 4 * s))| ≤ A := by
    intro s hs hsT
    have h1 : 1 ≤ Real.sqrt (R₀ ^ 2 + 4 * s) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [abs_of_nonneg (Real.log_nonneg h1)]
    exact Real.log_le_log (by linarith) (Real.sqrt_le_sqrt (by linarith))
  refine continuousOn_of_dominated (bound := fun z => A + |Real.log z.im|) ?_ ?_ ?_ ?_
  · intro p _
    exact (Real.measurable_log.comp (measurable_deriv _).norm).aestronglyMeasurable
  · rintro ⟨u, s⟩ ⟨hu, hs, hus⟩
    filter_upwards [foldedCircle_ae_mem_H w hr, foldedCircle_ae_abs_im_le w hr.le] with z hz hzi
    rw [Real.norm_eq_abs]
    have hzR : z.im ≤ R₀ := by linarith [le_abs_self z.im]
    refine (abs_log_norm_deriv_revMap_le (continuous_vrev hW _) hs hz hzR).trans ?_
    have := hsq s hs ((by linarith : s ≤ T).trans (le_abs_self T))
    linarith
  · exact (integrable_const A).add (integrable_log_im_foldedCircle w hr).abs
  · filter_upwards [foldedCircle_ae_mem_H w hr] with z hz
    have hJ := continuousOn_log_deriv_fwdMapInv_joint hW hW0 T
    have c1 : ContinuousOn (fun p : ℝ × ℝ => Real.log ‖deriv (fwdMapInv W (p.1 + p.2)) z‖)
        (tri T) :=
      hJ.comp (f := fun p : ℝ × ℝ => (p.1 + p.2, z)) (by fun_prop) fun p hp =>
        ⟨⟨add_nonneg hp.1 hp.2.1, hp.2.2⟩, hz⟩
    have hRc : ContinuousOn (fun p : ℝ × ℝ => revMap (vrev W (p.1 + p.2)) p.2 z) (tri T) :=
      (continuousOn_revMap_vrev hW T).comp (f := fun p : ℝ × ℝ => (p, z)) (by fun_prop)
        fun p hp => ⟨hp, hz⟩
    have c2 : ContinuousOn (fun p : ℝ × ℝ =>
        Real.log ‖deriv (fwdMapInv W p.1) (revMap (vrev W (p.1 + p.2)) p.2 z)‖) (tri T) :=
      hJ.comp (f := fun p : ℝ × ℝ => (p.1, revMap (vrev W (p.1 + p.2)) p.2 z))
        (continuousOn_fst.prodMk hRc) fun p hp =>
          ⟨⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩, im_revMap_pos (continuous_vrev hW _) hz hp.2.1⟩
    exact (c1.sub c2).congr fun p hp => log_norm_deriv_R_eq hW hW0 hp.1 hp.2.1 hz

/-- **Continuity in `(u, s)` of `∫ G(u, R_{u,s}(z), ρ) dfc(w, r)(z)`** for `G` continuous on
`parSet T` (bounded convergence). -/
theorem continuousOn_integral_comp_R (hW : Continuous W) {T : ℝ} {G : ℝ × (ℂ × ℝ) → ℝ}
    (hG : ContinuousOn G (parSet T)) (w : ℂ) {r : ℝ} (hr : 0 < r) {ρ : ℝ} (hρ : 0 < ρ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      ∫ z, G (p.1, (revMap (vrev W (p.1 + p.2)) p.2 z, ρ)) ∂foldedCircle w r) (tri T) := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  set Rb := revBound (2 * M) T (‖w‖ + r) with hRb
  set K := Icc (0 : ℝ) T ×ˢ ((Metric.closedBall (0 : ℂ) Rb ∩ Hbar) ×ˢ ({ρ} : Set ℝ)) with hK
  have hKc : IsCompact K :=
    isCompact_Icc.prod (((isCompact_closedBall _ _).inter_right isClosed_Hbar).prod
      isCompact_singleton)
  have hKs : K ⊆ parSet T := fun q hq =>
    ⟨hq.1, hq.2.1.2, by rw [show q.2.2 = ρ from hq.2.2]; exact hρ⟩
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hG.mono hKs)
  have hmem : ∀ p ∈ tri T, ∀ z ∈ H, ‖z‖ ≤ ‖w‖ + r →
      (p.1, (revMap (vrev W (p.1 + p.2)) p.2 z, ρ)) ∈ K := by
    rintro ⟨u, s⟩ ⟨hu, hs, hus⟩ z hz hzn
    have hV := continuous_vrev hW (u + s)
    have hb : ‖revMap (vrev W (u + s)) s z‖ ≤ revBound (2 * M) s (‖w‖ + r) :=
      norm_revMap_le_revBound hV hs (fun x _ => abs_vrev_le hM ⟨add_nonneg hu hs, hus⟩ x) _ hzn
    have hmono : revBound (2 * M) s (‖w‖ + r) ≤ Rb := by
      rw [hRb]; unfold revBound; linarith
    exact ⟨⟨hu, by linarith⟩, ⟨mem_closedBall_zero_iff.2 (hb.trans hmono),
      (im_revMap_pos hV hz hs).le⟩, rfl⟩
  have hmaps : ∀ p ∈ tri T, ∀ z ∈ H, (p.1, (revMap (vrev W (p.1 + p.2)) p.2 z, ρ)) ∈ parSet T := by
    rintro ⟨u, s⟩ ⟨hu, hs, hus⟩ z hz
    exact ⟨⟨hu, by linarith⟩, (im_revMap_pos (continuous_vrev hW _) hz hs).le, hρ⟩
  refine continuousOn_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_
  · rintro ⟨u, s⟩ hp
    have hc : ContinuousOn (fun z => G (u, (revMap (vrev W (u + s)) s z, ρ))) H :=
      hG.comp (continuousOn_const.prodMk
        ((differentiableOn_revMap _ (continuous_vrev hW _) hp.2.1).continuousOn.prodMk
          continuousOn_const)) fun z hz => hmaps (u, s) hp z hz
    have := hc.aestronglyMeasurable (μ := foldedCircle w r) isOpen_H.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (foldedCircle_ae_mem_H w hr)] at this
  · intro p hp
    filter_upwards [foldedCircle_ae_mem_H w hr, foldedCircle_ae_norm_le w hr.le] with z hz hzn
    exact hC _ (hmem p hp z hz hzn)
  · filter_upwards [foldedCircle_ae_mem_H w hr] with z hz
    have hRc : ContinuousOn (fun p : ℝ × ℝ => revMap (vrev W (p.1 + p.2)) p.2 z) (tri T) :=
      (continuousOn_revMap_vrev hW T).comp (f := fun p : ℝ × ℝ => (p, z)) (by fun_prop)
        fun p hp => ⟨hp, hz⟩
    exact hG.comp (continuousOn_fst.prodMk (hRc.prodMk continuousOn_const))
      fun p hp => hmaps p hp z hz

end RegUnif
end QuantumZipper
