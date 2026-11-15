import InteractingSLE.Foundations.Loewner.YuanTrace
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Frozen.Spec.IsGeneratingTrace

/-!
# Mapping out a prefix of a continuous Loewner trace ([Yua22] Corollary 1.3)

Packet GEO-YUAN of `planning/INFRA-GEO.md` §4. Y. Yuan, *Topological characterisations of Loewner
traces*, Indiana Univ. Math. J. 71 (2022), arXiv:2003.05535v4 ([Yua22]), Corollary 1.3 and the
paragraph before it (`source/external/Yua22/arxiv-latex/TraceTopology.tex` L156–L161): if `η` is a
continuous Loewner trace of `W` and `a ≥ 0`, the shifted driver `W(a + ·) − W(a)`
(QuantumZipper `RS.shiftDrive W a`) generates the continuous trace `γ_a(s) = g_a(η(a + s)) − W(a)`.

Here `γ_a(s)` is the tip `loewnerTip (shiftDrive W a) s` of the shifted chain, i.e. the boundary
value at `0` of its inverse map. Everything except the left-continuity of `γ_a` is proved:

* `IsLoewnerTrace.exists_tendsto_shift`: every inverse map `F^{(a)}_u` of the shifted chain has a
  limit at every point of `ℍ̄` (cluster-set lemma applied to `F̄_a ∘ F^{(a)}_u = F_{a+u}`), and
  `F̄_a ∘ F̄^{(a)}_u = F̄_{a+u}` on `ℍ̄`;
* `IsLoewnerTrace.extendFrom_shift_tip`: `F̄_a(γ_a(u)) = η(a + u)`: `γ_a(u)` is a point of the fibre
  of `η(a + u)`, so it is the "boundary interpretation" of `g_a(η(a + u))` of [Yua22] Remark 1.2;
* `IsLoewnerTrace.continuousWithinAt_shift_Ici`: `γ_a` is right-continuous;
* `IsLoewnerTrace.continuousWithinAt_shift_of_subsingleton`: `γ_a` is continuous at every time
  whose fibre is a single point (for instance whenever `η(a + s) ∉ K_a`), so the only possible
  discontinuities are left jumps between two prime ends over one boundary point of `ℍ \ K_a`;
* `IsLoewnerTrace.fwdHull_shift_eq`: the hulls of the shifted chain are the fillings of
  `γ_a([0, u])` (no continuity needed);
* `IsLoewnerTrace.isLoewnerTrace_shift_of_continuousOn`: hence Corollary 1.3 holds as soon as
  `γ_a` is continuous; the remaining input is left-continuity (`[Yua22]` §3,
  Proposition 3.1, "excursions"), see the handoff `planning/handoffs/PROVE-GEO-YUAN.md`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

/-- The **tip** of the Loewner chain driven by `W` at time `t`: the boundary value `F̄_t(0)` of the
centred inverse map (junk if `F_t` has no limit at `0`). For a continuous Loewner trace it is the
trace itself (`IsLoewnerTrace.loewnerTip_eq`). -/
def loewnerTip (W : ℝ → ℝ) (t : ℝ) : ℂ := extendFrom H (fwdMapInv W t) 0

theorem zero_mem_Hbar : (0 : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (z := 0) (by simp)

theorem tendsto_ofReal_mul_I_nhdsWithin_H :
    Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝[H] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
      ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    show 0 < ((y : ℂ) * I).im
    simpa using hy

/-! ### Unbounded connected sets lie in the unbounded component -/

theorem subset_H_diff_fillH_of_isPreconnected {C S : Set ℂ} (hC : Bornology.IsBounded C)
    (hS : IsPreconnected S) (hSsub : S ⊆ H \ closure C) (hSb : ¬ Bornology.IsBounded S) :
    S ⊆ H \ fillH C := by
  obtain ⟨R, hR, hCR⟩ := exists_closure_subset_ball hC
  obtain ⟨z, hz⟩ : S.Nonempty := by
    by_contra h
    exact hSb (by rw [not_nonempty_iff_eq_empty.1 h]; exact Bornology.isBounded_empty)
  have h1 := hS.subset_connectedComponentIn hz hSsub
  have hb : ¬ Bornology.IsBounded (connectedComponentIn (H \ closure C) z) := fun h =>
    hSb (h.subset h1)
  rw [connectedComponentIn_eq_of_not_isBounded hR hCR hb, ← H_diff_fillH hR hCR] at h1
  exact h1

theorem not_isBounded_H_diff_fillH {C : Set ℂ} (hC : Bornology.IsBounded C) :
    ¬ Bornology.IsBounded (H \ fillH C) := by
  obtain ⟨R, hR, hCR⟩ := exists_closure_subset_ball hC
  rw [H_diff_fillH hR hCR]
  exact not_isBounded_connectedComponentIn_of_lt hR hCR

theorem not_isBounded_image_of_norm_sub_le {f : ℂ → ℂ} {S : Set ℂ}
    (hS : ¬ Bornology.IsBounded S) {C : ℝ} (hf : ∀ z ∈ S, ‖f z - z‖ ≤ C) :
    ¬ Bornology.IsBounded (f '' S) := by
  intro h
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 h
  refine hS ((Metric.isBounded_iff_subset_closedBall 0).2 ⟨R + C, fun z hz => ?_⟩)
  have h1 := hR (mem_image_of_mem f hz)
  rw [mem_closedBall_zero_iff] at h1 ⊢
  have h2 := hf z hz
  linarith [norm_sub_norm_le z (f z), norm_sub_rev z (f z)]

/-! ### The shifted chain -/

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

theorem shiftDrive_zero (W : ℝ → ℝ) (a : ℝ) : shiftDrive W a 0 = 0 := by
  simp [shiftDrive]

theorem IsLoewnerTrace.loewnerTip_eq (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) : loewnerTip W t = η t :=
  extendFrom_eq (by rw [closure_H]; exact zero_mem_Hbar) (hη.tendsto_fwdMapInv_tip hW hW0 ht)

/-- **The shifted inverse maps have boundary limits.** For `a, u ≥ 0` and `x ∈ ℍ̄`, the inverse map
`F^{(a)}_u` of the chain driven by `W(a + ·) − W(a)` has a limit `ξ` at `x`, and
`F̄_a(ξ) = F̄_{a+u}(x)`. -/
theorem IsLoewnerTrace.exists_tendsto_shift (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) {x : ℂ} (hx : x ∈ Hbar) :
    ∃ ξ ∈ Hbar, extendFrom H (fwdMapInv W a) ξ = extendFrom H (fwdMapInv W (a + u)) x ∧
      Tendsto (fwdMapInv (shiftDrive W a) u) (𝓝[H] x) (𝓝 ξ) := by
  obtain ⟨hd, hc, hinj, hR⟩ := hη.fiber_hyps hW hW0 ha
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 := shiftDrive_zero W a
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hV hV0 hu
  refine exists_tendsto_of_tendsto_comp hd hc hinj hR hx (continuousOn_fwdMapInv hV hV0 hu)
    (fun w hw => H_subset_Hbar (QuantumZipper.RS.fwdMapInv_mem_H hV hV0 hu hw))
    (R := C + ‖x‖ + 1) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds x one_pos)]
      with w hw hwx
    have h1 := hC w hw
    rw [mem_ball, dist_eq_norm] at hwx
    have h2 : ‖w‖ ≤ ‖x‖ + 1 := by linarith [norm_le_norm_add_norm_sub' w x]
    linarith [norm_le_norm_add_norm_sub' (fwdMapInv (shiftDrive W a) u w) w]
  · refine ((hη.hasBdryLimits hW hW0 (add_nonneg ha hu)).tendsto hx).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hGw := QuantumZipper.RS.fwdMapInv_mem_H hV hV0 hu hw
    rw [extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 ha) hGw,
      QuantumZipper.RS.fwdMapInv_add_shift hW hW0 ha hu hw]

theorem IsLoewnerTrace.hasBdryLimits_shift (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) :
    HasBdryLimits (fwdMapInv (shiftDrive W a) u) := fun _ hx =>
  let ⟨ξ, _, _, h⟩ := hη.exists_tendsto_shift hW hW0 ha hu hx
  ⟨ξ, h⟩

/-- **The shifted tip lies over the trace:** `F̄_a(γ_a(u)) = η(a + u)`, and `F^{(a)}_u(w) → γ_a(u)`
as `w → 0` in `ℍ`. -/
theorem IsLoewnerTrace.extendFrom_shift_tip (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) :
    loewnerTip (shiftDrive W a) u ∈ Hbar ∧
      extendFrom H (fwdMapInv W a) (loewnerTip (shiftDrive W a) u) = η (a + u) ∧
      Tendsto (fwdMapInv (shiftDrive W a) u) (𝓝[H] 0) (𝓝 (loewnerTip (shiftDrive W a) u)) := by
  obtain ⟨ξ, hξ, hFξ, hlim⟩ := hη.exists_tendsto_shift hW hW0 ha hu zero_mem_Hbar
  have htip : loewnerTip (shiftDrive W a) u = ξ :=
    extendFrom_eq (by rw [closure_H]; exact zero_mem_Hbar) hlim
  refine ⟨htip ▸ hξ, ?_, htip ▸ hlim⟩
  rw [htip, hFξ]
  exact hη.loewnerTip_eq hW hW0 (add_nonneg ha hu)

theorem loewnerTip_shiftDrive_zero (hW : Continuous W) (a : ℝ) :
    loewnerTip (shiftDrive W a) 0 = 0 := by
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 := shiftDrive_zero W a
  have h : Tendsto (fwdMapInv (shiftDrive W a) 0) (𝓝[H] 0) (𝓝 0) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (fwdMapInv_zero_time hV hV0 hw).symm
  exact extendFrom_eq (by rw [closure_H]; exact zero_mem_Hbar) h

/-- Bound on the tips: `‖γ_a(u)‖ ≤ 24 M + 8 √u` if `|W(a + ·) − W(a)| ≤ M` on `[0, u]`. -/
theorem IsLoewnerTrace.norm_shift_tip_le (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a u M : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hM : ∀ r ∈ Icc (0 : ℝ) u, |shiftDrive W a r| ≤ M) :
    ‖loewnerTip (shiftDrive W a) u‖ ≤ 24 * M + 8 * Real.sqrt u := by
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 := shiftDrive_zero W a
  have hlim := (hη.extendFrom_shift_tip hW hW0 ha hu).2.2
  have hlim' := (hlim.comp tendsto_ofReal_mul_I_nhdsWithin_H).norm
  refine le_of_forall_pos_le_add fun ε hε => le_of_tendsto hlim' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds hε)] with y hy hyε
  have hy0 : (0 : ℝ) < y := hy
  have hw : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa using hy0
  have h1 := norm_fwdMapInv_sub_le hV hV0 hu hM hw
  have h2 : ‖(y : ℂ) * I‖ = y := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
  simp only [Function.comp]
  linarith [norm_le_norm_add_norm_sub' (fwdMapInv (shiftDrive W a) u ((y : ℂ) * I))
    ((y : ℂ) * I)]

/-! ### Right-continuity and continuity at simple fibre points -/

/-- **Right-continuity of the shifted trace** ([Yua22] §2.1, "`γ_t` is right-continuous"). For
`u ↓ s`, `F^{(a)}_u = F^{(a)}_s ∘ F^{(a,s)}_{u-s}` and the second map moves `iy` by at most
`24 osc + 8 √(u − s)`; continuity of `F̄^{(a)}_s` at `0` concludes. -/
theorem IsLoewnerTrace.continuousWithinAt_shift_Ici (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    ContinuousWithinAt (loewnerTip (shiftDrive W a)) (Ici s) s := by
  set V := shiftDrive W a with hVdef
  have hV : Continuous V := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : V 0 = 0 := shiftDrive_zero W a
  set E := extendFrom H (fwdMapInv V s) with hE
  have hEc : ContinuousOn E Hbar := (hη.hasBdryLimits_shift hW hW0 ha hs).continuousOn
  have hE0 : E 0 = loewnerTip V s := rfl
  have hV' : Continuous (shiftDrive V s) := QuantumZipper.RS.continuous_shiftDrive hV s
  have hV'0 : shiftDrive V s 0 = 0 := shiftDrive_zero V s
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨ρ, hρ, hρE⟩ :=
    Metric.continuousWithinAt_iff.1 (hEc 0 zero_mem_Hbar) (ε / 2) (by positivity)
  obtain ⟨d, hd, hdV⟩ := Metric.continuous_iff.1 hV' 0 (ρ / 100) (by positivity)
  refine ⟨min d ((ρ / 100) ^ 2), by positivity, fun u hu hud => ?_⟩
  have hus : s ≤ u := hu
  set r := u - s with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hu' : u = s + r := by rw [hr]; ring
  rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ u - s)] at hud
  have hM : ∀ x ∈ Icc (0 : ℝ) r, |shiftDrive V s x| ≤ ρ / 100 := by
    intro x hx
    have hx' : dist x 0 < d := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
      exact lt_of_le_of_lt hx.2 (lt_of_lt_of_le hud (min_le_left _ _))
    have h := hdV x hx'
    rw [Real.dist_eq, hV'0, sub_zero] at h
    exact h.le
  have hsq : Real.sqrt r < ρ / 100 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact lt_of_lt_of_le hud (min_le_right _ _)
  have hlim := (hη.extendFrom_shift_tip hW hW0 ha (hs.trans hus)).2.2.comp
    tendsto_ofReal_mul_I_nhdsWithin_H
  have hbound : dist (loewnerTip V u) (loewnerTip V s) ≤ ε / 2 := by
    refine le_of_tendsto (hlim.dist tendsto_const_nhds) ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : ℝ) < ρ / 2 by positivity))]
      with y hy hyρ
    have hy0 : (0 : ℝ) < y := hy
    have hw : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa using hy0
    have hζH := QuantumZipper.RS.fwdMapInv_mem_H hV' hV'0 hr0 hw
    have h1 := norm_fwdMapInv_sub_le hV' hV'0 hr0 hM hw
    have hnorm : ‖(y : ℂ) * I‖ = y := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy0]
    have hζρ : dist (fwdMapInv (shiftDrive V s) r ((y : ℂ) * I)) 0 < ρ := by
      rw [dist_zero_right]
      linarith [norm_le_norm_add_norm_sub' (fwdMapInv (shiftDrive V s) r ((y : ℂ) * I))
        ((y : ℂ) * I)]
    have h2 := hρE (H_subset_Hbar hζH) hζρ
    have heq : fwdMapInv V u ((y : ℂ) * I) = E (fwdMapInv (shiftDrive V s) r ((y : ℂ) * I)) := by
      rw [hE, extendFrom_H_eq (continuousOn_fwdMapInv hV hV0 hs) hζH, hu',
        QuantumZipper.RS.fwdMapInv_add_shift hV hV0 hs hr0 hw]
    simp only [Function.comp]
    rw [heq, ← hE0]
    exact h2.le
  linarith

/-- **Continuity at simple fibre points.** If the fibre of `η(a + s)` under `F̄_a` is a single
point, the shifted trace is continuous at `s`: every cluster value of `γ_a` at `s` lies in that
fibre, because `F̄_a ∘ γ_a = η(a + ·)` is continuous. -/
theorem IsLoewnerTrace.continuousWithinAt_shift_of_subsingleton (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hfib : {ξ ∈ Hbar | extendFrom H (fwdMapInv W a) ξ = η (a + s)}.Subsingleton) :
    ContinuousWithinAt (loewnerTip (shiftDrive W a)) (Ici 0) s := by
  obtain ⟨-, hc, -, -⟩ := hη.fiber_hyps hW hW0 ha
  obtain ⟨M, hM0, hM⟩ :=
    exists_abs_le_of_continuous (QuantumZipper.RS.continuous_shiftDrive hW a) (s + 1)
  set K := closedBall (0 : ℂ) (24 * M + 8 * Real.sqrt (s + 1)) ∩ Hbar with hKdef
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hmem : ∀ᶠ v in 𝓝[Ici 0] s, loewnerTip (shiftDrive W a) v ∈ K := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (show s < s + 1 by linarith))] with v hv hvs
    have hv0 : 0 ≤ v := hv
    refine ⟨mem_closedBall_zero_iff.2 ((hη.norm_shift_tip_le hW hW0 ha hv0
      fun r hr => hM r ⟨hr.1, hr.2.trans hvs.le⟩).trans ?_),
      (hη.extendFrom_shift_tip hW hW0 ha hv0).1⟩
    gcongr
  have hshift : Tendsto (fun v : ℝ => a + v) (𝓝[Ici 0] s) (𝓝[Ici 0] (a + s)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_const.add continuous_id).tendsto s).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact add_nonneg ha hv
  have hFτ : Tendsto (fun v => extendFrom H (fwdMapInv W a) (loewnerTip (shiftDrive W a) v))
      (𝓝[Ici 0] s) (𝓝 (η (a + s))) := by
    refine ((hη.2.1 (a + s) (add_nonneg ha hs)).tendsto.comp hshift).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact ((hη.extendFrom_shift_tip hW hW0 ha hv).2.1).symm
  have hτs := hη.extendFrom_shift_tip hW hW0 ha hs
  refine hK.tendsto_nhds_of_unique_mapClusterPt hmem fun ξ hξK hξ => ?_
  have hFξ := eq_of_mapClusterPt hc (hmem.mono fun _ h => h.2) hFτ hξK.2 hξ
  exact hfib ⟨hξK.2, hFξ⟩ ⟨hτs.1, hτs.2.1⟩

/-- **Continuity during excursions.** If `η(a + s) ∉ K_a` (an interior point of `ℍ \ K_a`), the
shifted trace is continuous at `s`. -/
theorem IsLoewnerTrace.continuousWithinAt_shift_of_mem (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hint : η (a + s) ∈ H \ fwdHull W a) :
    ContinuousWithinAt (loewnerTip (shiftDrive W a)) (Ici 0) s := by
  obtain ⟨-, -, hinj, hR⟩ := hη.fiber_hyps hW hW0 ha
  have hcb := isConformalBijection_fwdMapInv hW hW0 ha
  have hFeq : EqOn (extendFrom H (fwdMapInv W a)) (fwdMapInv W a) H := fun x hx =>
    extendFrom_H_eq hcb.1.continuousOn hx
  have himg : extendFrom H (fwdMapInv W a) '' H = H \ fwdHull W a := by
    rw [hFeq.image_eq]; exact hcb.2.image_eq
  refine hη.continuousWithinAt_shift_of_subsingleton hW hW0 ha hs ?_
  have hinH : ∀ ξ ∈ {ξ ∈ Hbar | extendFrom H (fwdMapInv W a) ξ = η (a + s)}, ξ ∈ H := by
    rintro ξ ⟨hξ, hFξ⟩
    by_contra hn
    have h0 : ξ.im = 0 := le_antisymm (not_lt.1 hn) hξ
    exact hR ξ h0 (by rw [himg, hFξ]; exact hint)
  intro ξ₁ h₁ ξ₂ h₂
  exact hinj (hinH ξ₁ h₁) (hinH ξ₂ h₂) (h₁.2.trans h₂.2.symm)

/-! ### The hulls of the shifted chain -/

/-- **The hulls of the shifted chain are the fillings of the shifted tips.** For `a, u ≥ 0`, the
hull at time `u` of the chain driven by `W(a + ·) − W(a)` is `fill(γ_a([0, u]))`. No continuity of
`γ_a` is used: `g_a` is a homeomorphism of `ℍ \ K_a` onto `ℍ` which carries the trace points
`η([a, a + u]) \ K_a` onto `γ_a([0, u]) ∩ ℍ` and the unbounded component onto the unbounded
component. -/
theorem IsLoewnerTrace.fwdHull_shift_eq (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) :
    fwdHull (shiftDrive W a) u = fillH (loewnerTip (shiftDrive W a) '' Icc 0 u) := by
  set V := shiftDrive W a with hVdef
  have hV : Continuous V := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : V 0 = 0 := shiftDrive_zero W a
  set τ := loewnerTip V with hτdef
  set A := η '' Icc 0 (a + u) with hAdef
  set B := τ '' Icc 0 u with hBdef
  set Da := H \ fwdHull W a with hDa
  have hau : 0 ≤ a + u := add_nonneg ha hu
  obtain ⟨-, -, -, hR⟩ := hη.fiber_hyps hW hW0 ha
  have hcb := isConformalBijection_fwdMapInv hW hW0 ha
  have hFeq : EqOn (extendFrom H (fwdMapInv W a)) (fwdMapInv W a) H := fun x hx =>
    extendFrom_H_eq hcb.1.continuousOn hx
  have himg : extendFrom H (fwdMapInv W a) '' H = Da := by
    rw [hFeq.image_eq]; exact hcb.2.image_eq
  have hgF : ∀ w ∈ H, fwdMap W a (fwdMapInv W a w) = w := fun w hw =>
    QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ha hw
  have hFg : ∀ z ∈ Da, fwdMapInv W a (fwdMap W a z) = z := fun z hz =>
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ha hz
  have hgH : MapsTo (fwdMap W a) Da H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ha
  have hFDa : ∀ w ∈ H, fwdMapInv W a w ∈ Da := fun w hw =>
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ha hw
  have htip : ∀ v ∈ Icc (0 : ℝ) u,
      τ v ∈ Hbar ∧ extendFrom H (fwdMapInv W a) (τ v) = η (a + v) := fun v hv =>
    ⟨(hη.extendFrom_shift_tip hW hW0 ha hv.1).1, (hη.extendFrom_shift_tip hW hW0 ha hv.1).2.1⟩
  -- the shifted tips in `ℍ` are the images of the new trace points
  have hBH : B ∩ H = fwdMap W a '' (A ∩ Da) := by
    ext z
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hzH⟩
      obtain ⟨-, h2⟩ := htip v hv
      rw [hFeq hzH] at h2
      refine ⟨η (a + v), ⟨⟨a + v, ⟨by linarith [hv.1], by linarith [hv.2]⟩, rfl⟩,
        h2 ▸ hFDa _ hzH⟩, ?_⟩
      rw [← h2, hgF _ hzH]
    · rintro ⟨w, ⟨⟨c, hc', rfl⟩, hwDa⟩, rfl⟩
      have hca : a < c := by
        by_contra hle
        push Not at hle
        apply hwDa.2
        rw [hη.2.2 a ha]
        exact ⟨hwDa.1, Or.inl (subset_closure ⟨c, ⟨hc'.1, hle⟩, rfl⟩)⟩
      have hv : c - a ∈ Icc (0 : ℝ) u := ⟨by linarith, by linarith [hc'.2]⟩
      obtain ⟨hτH, hτ⟩ := htip (c - a) hv
      rw [show a + (c - a) = c by ring] at hτ
      have hτH' : τ (c - a) ∈ H := by
        by_contra hn
        have h0 : (τ (c - a)).im = 0 := le_antisymm (not_lt.1 hn) hτH
        exact hR _ h0 (by rw [himg, hτ]; exact hwDa)
      rw [hFeq hτH'] at hτ
      refine ⟨⟨c - a, hv, ?_⟩, ?_⟩
      · rw [← hτ, hgF _ hτH']
      · rw [← hτ, hgF _ hτH']; exact hτH'
  have hAc : IsClosed A := (hη.isCompact_image (a + u)).isClosed
  -- `B ∩ ℍ` is relatively closed in `ℍ`
  have hclB : closure B ∩ H ⊆ B ∩ H := by
    rintro z ⟨hzB, hzH⟩
    have hz1 : z ∈ closure (B ∩ H) := by
      rw [mem_closure_iff_nhds] at hzB ⊢
      intro U hU
      obtain ⟨x, hxU, hxB⟩ := hzB (U ∩ H) (inter_mem hU (QuantumZipper.isOpen_H.mem_nhds hzH))
      exact ⟨x, hxU.1, hxB, hxU.2⟩
    have hFz : fwdMapInv W a z ∈ closure (fwdMapInv W a '' (B ∩ H)) :=
      mem_closure_image (QuantumZipper.RS.continuousAt_fwdMapInv hW hW0 ha hzH) hz1
    have hsub : fwdMapInv W a '' (B ∩ H) ⊆ A := by
      rw [hBH]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      rw [hFg w hw.2]
      exact hw.1
    have hFzA : fwdMapInv W a z ∈ A := hAc.closure_subset_iff.2 hsub hFz
    rw [hBH]
    exact ⟨fwdMapInv W a z, ⟨hFzA, hFDa z hzH⟩, hgF z hzH⟩
  -- the shifted domain is the image of the original one
  have hstep1 : H \ fwdHull V u = fwdMap W a '' (H \ fwdHull W (a + u)) := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hV hV0 hu,
      ← QuantumZipper.RS.image_fwdMapInv_H hW hW0 hau, image_image]
    refine image_congr fun w hw => ?_
    rw [QuantumZipper.RS.fwdMapInv_add_shift hW hW0 ha hu hw,
      hgF _ (QuantumZipper.RS.fwdMapInv_mem_H hV hV0 hu hw)]
  have hA_K : fwdHull W (a + u) = fillH A := hη.2.2 _ hau
  have hAb : Bornology.IsBounded A := (hη.isCompact_image _).isBounded
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hV u
  have hBb : Bornology.IsBounded B := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨24 * M + 8 * Real.sqrt u, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_closedBall_zero_iff]
    refine (hη.norm_shift_tip_le hW hW0 ha hv.1 fun r hr => hM r ⟨hr.1, hr.2.trans hv.2⟩).trans ?_
    gcongr
    exact hv.2
  obtain ⟨Ma, -, hMa⟩ := exists_abs_le_of_continuous hW a
  have hgdisp : ∀ z ∈ Da, ‖fwdMap W a z - z‖ ≤ 24 * Ma + 8 * Real.sqrt a := fun z hz =>
    norm_fwdMap_sub_self_le hW hW0 ha hMa hz ⟨ha, le_rfl⟩
  obtain ⟨CF, hCF⟩ := exists_norm_fwdMapInv_sub_le hW hW0 ha
  have hDaA : H \ fillH A ⊆ Da \ A := by
    intro z hz
    refine ⟨⟨hz.1, fun hzK => hz.2 ?_⟩, fun hzA => hz.2 ⟨hz.1, Or.inl (subset_closure hzA)⟩⟩
    rw [← hA_K]
    exact fwdHull_mono' (by linarith) hzK
  have hgcont : ContinuousOn (fwdMap W a) Da :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ha).continuousOn
  have hginj : InjOn (fwdMap W a) Da := QuantumZipper.FwdHolo.injOn_fwdMap hW ha
  have hsub1 : fwdMap W a '' (H \ fillH A) ⊆ H \ fillH B := by
    apply subset_H_diff_fillH_of_isPreconnected hBb
    · have hpc : IsPreconnected (H \ fillH A) := by
        obtain ⟨R, hR', hAR⟩ := exists_closure_subset_ball hAb
        rw [H_diff_fillH hR' hAR]
        exact isPreconnected_connectedComponentIn
      exact hpc.image _ (hgcont.mono fun z hz => (hDaA hz).1)
    · rintro _ ⟨w, hw, rfl⟩
      have hwD := hDaA hw
      refine ⟨hgH hwD.1, fun hcl => ?_⟩
      have h1 := hclB ⟨hcl, hgH hwD.1⟩
      rw [hBH] at h1
      obtain ⟨w', hw', hww'⟩ := h1
      exact hwD.2 (hginj hw'.2 hwD.1 hww' ▸ hw'.1)
    · exact not_isBounded_image_of_norm_sub_le (not_isBounded_H_diff_fillH hAb)
        fun z hz => hgdisp z (hDaA hz).1
  have hsub2 : H \ fillH B ⊆ fwdMap W a '' (H \ fillH A) := by
    intro z hz
    have hpcB : IsPreconnected (H \ fillH B) := by
      obtain ⟨R, hR', hBR⟩ := exists_closure_subset_ball hBb
      rw [H_diff_fillH hR' hBR]
      exact isPreconnected_connectedComponentIn
    have himgsub : fwdMapInv W a '' (H \ fillH B) ⊆ H \ fillH A := by
      apply subset_H_diff_fillH_of_isPreconnected hAb
      · exact hpcB.image _ ((continuousOn_fwdMapInv hW hW0 ha).mono fun x hx => hx.1)
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨(hFDa x hx.1).1, fun hxA => ?_⟩
        rw [hAc.closure_eq] at hxA
        have hxB : x ∈ B ∩ H := by
          rw [hBH]; exact ⟨fwdMapInv W a x, ⟨hxA, hFDa x hx.1⟩, hgF x hx.1⟩
        exact hx.2 ⟨hx.1, Or.inl (subset_closure hxB.1)⟩
      · exact not_isBounded_image_of_norm_sub_le (not_isBounded_H_diff_fillH hBb)
          fun x hx => hCF x hx.1
    exact ⟨fwdMapInv W a z, himgsub ⟨z, hz, rfl⟩, hgF z hz.1⟩
  have hfin : H \ fwdHull V u = H \ fillH B := by
    rw [hstep1, hA_K]
    exact Subset.antisymm hsub1 hsub2
  ext z
  by_cases hzH : z ∈ H
  · constructor
    · intro hz
      by_contra hn
      have h1 : z ∈ H \ fillH B := ⟨hzH, hn⟩
      rw [← hfin] at h1
      exact h1.2 hz
    · intro hz
      by_contra hn
      have h1 : z ∈ H \ fwdHull V u := ⟨hzH, hn⟩
      rw [hfin] at h1
      exact h1.2 hz
  · exact ⟨fun hz => absurd ((QuantumZipper.fwdHull_mono (W := V)).2 u hz) hzH,
      fun hz => absurd (fillH_subset_H B hz) hzH⟩

/-! ### Corollary 1.3, conditional on continuity -/

/-- **[Yua22] Corollary 1.3, given continuity of the shifted trace.** If `η` is a continuous
Loewner trace of `W` and the shifted tips `γ_a = loewnerTip (shiftDrive W a)` are continuous, then
`γ_a` is a continuous Loewner trace of `W(a + ·) − W(a)`, lying over `η(a + ·)`. -/
theorem IsLoewnerTrace.isLoewnerTrace_shift_of_continuousOn (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 ≤ a)
    (hcont : ContinuousOn (loewnerTip (shiftDrive W a)) (Ici 0)) :
    IsLoewnerTrace (shiftDrive W a) (loewnerTip (shiftDrive W a)) :=
  ⟨loewnerTip_shiftDrive_zero hW a, hcont, fun _ hu => hη.fwdHull_shift_eq hW hW0 ha hu⟩

/-- **[Yua22] Corollary 1.3, given left-continuity of the shifted trace.** Right-continuity is
proved (`continuousWithinAt_shift_Ici`); left-continuity at positive times is the remaining input
([Yua22] §3, Proposition 3.1). -/
theorem IsLoewnerTrace.isLoewnerTrace_shift_of_left (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 ≤ a)
    (hleft : ∀ s : ℝ, 0 < s → ContinuousWithinAt (loewnerTip (shiftDrive W a)) (Iic s) s) :
    IsLoewnerTrace (shiftDrive W a) (loewnerTip (shiftDrive W a)) := by
  refine hη.isLoewnerTrace_shift_of_continuousOn hW hW0 ha fun s hs => ?_
  have hs0 : 0 ≤ s := hs
  have hright := hη.continuousWithinAt_shift_Ici hW hW0 ha hs0
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0] at hright ⊢
    exact hright
  · exact (continuousAt_iff_continuous_left_right.2 ⟨hleft s hpos, hright⟩).continuousWithinAt

/-! ### Bridge to the frozen `IsGeneratingTrace` -/

open scoped NNReal ENNReal in
/-- A continuous generating trace on `[0, ∞)` in the sense of the frozen `IsGeneratingTrace`
(`T = ∞`) is a continuous Loewner trace of the extended driver `s ↦ w s.toNNReal`. -/
theorem isLoewnerTrace_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}
    (h : IsGeneratingTrace w ⊤ η) :
    IsLoewnerTrace (fun s : ℝ => w s.toNNReal) (fun s : ℝ => η s.toNNReal) := by
  obtain ⟨h0, hc, hfill⟩ := h
  have hcont : Continuous η := continuousOn_univ.1 (hc.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  refine ⟨by simpa using h0, (hcont.comp continuous_real_toNNReal).continuousOn, fun t ht => ?_⟩
  have himg : (fun s : ℝ => η s.toNNReal) '' Icc 0 t = η '' Icc 0 t.toNNReal := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.toNNReal, ⟨bot_le, Real.toNNReal_le_toNNReal hs.2⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨(s : ℝ), ⟨s.2, ?_⟩, by simp⟩
      have := hs.2
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht] at this
      exact this
  have hK := hfill t.toNNReal (ENNReal.coe_lt_top)
  rw [Real.coe_toNNReal _ ht] at hK
  have hcpt : IsCompact (η '' Icc 0 t.toNNReal) :=
    isCompact_Icc.image hcont
  rw [himg]
  exact (fillH_eq_iff_isFilling_of_isClosed hcpt.isBounded hcpt.isClosed
    (QuantumZipper.fwdHull_mono.2 _)).1 hK

end InteractingSLE
