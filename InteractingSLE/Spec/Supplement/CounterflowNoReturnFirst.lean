/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowNoReturnBack
import InteractingSLE.Spec.Sec5.CfLocalCmp
import InteractingSLE.Spec.Sec2.Assembly2Pathwise

/-!
# No return of a counterflow: the first return closes a seed gap (deterministic)

Packet PROVE-CFNORETURN. Let `γ` be a continuous generating trace on `[0, ∞)` of an integrated `SLE_κ(ρ)` path of an
ordered word with a left mark `l` and a right mark `k` at the seed (`x_l = x_k = 0`). If `γ(u) = 0` at a first
return time `u > 0` (`γ ≠ 0` on `(0, u)`), then (`first_return`)

* either the right seed collides with the driver at `u`, `V_k(u) = W(u)`, and `γ` has not visited `(0, ∞)` before `u`,
* or the left seed collides, `V_l(u) = W(u)`, and `γ` has not visited `(−∞, 0)` before `u`.

**Proof.** For `t < u` the return transports to a real zero `c_t` of `F̄_t` with `|c_t| ≤ 24 osc W|[t,u] + 8 √(u − t)`
(`exists_extendFrom_eq_zero_of_return`). Since `γ(t) = F̄_t(0) ≠ 0`, `c_t ≠ 0`; by the classification of
`CounterflowNoReturnBack.lean` (`zero_right`, and `zero_left` through the reflection `z ↦ −z̄`), `c_t` is the seed gap
`V_k(t) − W(t)` with `(0, ∞)` unvisited by `t`, or `V_l(t) − W(t)` with `(−∞, 0)` unvisited by `t`. As `t ↑ u` both
gaps cannot stay positive; they cannot both vanish at `u` because the seeds separate at positive times
(`IsIntegratedSLEPath.vL_lt_vR_of_pos`); so one gap vanishes at `u` and the other stays positive near `u`, which forces
the corresponding alternative for all `t` near `u`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE

namespace CfNoReturn

section First

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}

theorem continuous_of_lt_top {f : ℝ≥0 → ℝ} (hf : ContinuousOn f {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤}) : Continuous f :=
  continuousOn_univ.1 (hf.mono fun _ _ => ENNReal.coe_lt_top)

/-- **Right real zeros before the first return** (generating-trace form). -/
theorem zero_right (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ⊤) (hγ : IsGeneratingTrace w ⊤ γ)
    {k : Fin nR} (hk : xR k = 0) {t : ℝ≥0} (hret : ∀ s : ℝ≥0, 0 < s → s ≤ t → γ s ≠ 0) {c : ℝ}
    (hc : 0 < c) (hF : extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) t) (c : ℂ) = 0) :
    c = vR k t - w t ∧ ∀ s : ℝ≥0, s ≤ t → ∀ x : ℝ, 0 < x → γ s ≠ x := by
  have hwc := continuous_of_lt_top h.continuousOn_w
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := hwc.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp [hWdef, h.w_zero]
  have hη := isLoewnerTrace_of_isGeneratingTrace hγ
  have htT : (t : ℝ) < ((t + 1 : ℝ≥0) : ℝ) := by push_cast; linarith
  obtain ⟨hc', hue, hi, hn⟩ := GB7a.centredPkg h.continuousOn_w (h.continuousOn_vR k)
    (fun s hs => h.integrable_gapR hs k) (fun s hs => h.vR_eq hs k) (h.volume_collisionR k)
    (T := t + 1) le_top (U := W) (fun s _ _ => rfl) t.coe_nonneg htT
  have hu0 : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ vR k s.toNNReal - w s.toNNReal := fun s _ =>
    sub_nonneg.2 (h.w_le_vR ENNReal.coe_lt_top k)
  have huz : vR k (0 : ℝ).toNNReal - w (0 : ℝ).toNNReal = 0 := by
    simp [h.vR_zero k, hk, h.w_zero]
  have hret' : ∀ s ∈ Ioc (0 : ℝ) t, (fun s : ℝ => γ s.toNNReal) s ≠ 0 := fun s hs =>
    hret _ (Real.toNNReal_pos.2 hs.1) (Real.toNNReal_le_iff_le_coe.2 hs.2)
  obtain ⟨hceq, hoff⟩ := eq_of_extendFrom_eq_zero_right hη hW hW0 t.coe_nonneg hc' hu0 huz hue hi hn hret'
    hc hF
  refine ⟨by simpa using hceq, fun s hs x hx hvis => hoff s ⟨s.coe_nonneg, hs⟩ x hx ?_⟩
  simpa using hvis

/-- **Left real zeros before the first return** (the reflection of `zero_right`). -/
theorem zero_left (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ⊤) (hγ : IsGeneratingTrace w ⊤ γ)
    {l : Fin nL} (hl : xL l = 0) {t : ℝ≥0} (hret : ∀ s : ℝ≥0, 0 < s → s ≤ t → γ s ≠ 0) {c : ℝ}
    (hc : c < 0) (hF : extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) t) (c : ℂ) = 0) :
    c = vL l t - w t ∧ ∀ s : ℝ≥0, s ≤ t → ∀ x : ℝ, x < 0 → γ s ≠ x := by
  have hR := h.reflect
  have hγR := LP.isGeneratingTrace_reflect hγ
  have hwc := continuous_of_lt_top h.continuousOn_w
  have hW : Continuous (fun s : ℝ => w s.toNNReal) := hwc.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [h.w_zero]
  have hη := isLoewnerTrace_of_isGeneratingTrace hγ
  have hFR : extendFrom H (fwdMapInv (fun s : ℝ => (-w) s.toNNReal) t) ((-c : ℝ) : ℂ) = 0 := by
    have e := extendFrom_fwdMapInv_neg hη hW hW0 t.coe_nonneg (ofReal_mem_Hbar' c)
    rw [hF, LP.reflectC_ofReal, LP.reflectC_zero] at e
    exact e
  have hretR : ∀ s : ℝ≥0, 0 < s → s ≤ t → LP.reflectC (γ s) ≠ 0 := fun s hs hst he => by
    refine hret s hs hst ?_
    have := congrArg LP.reflectC he
    rwa [LP.reflectC_reflectC, LP.reflectC_zero] at this
  obtain ⟨h1, h2⟩ := zero_right hR hγR (k := l) (by simp [hl]) hretR (by linarith : (0 : ℝ) < -c) hFR
  refine ⟨by simp only [Pi.neg_apply] at h1; linarith, fun s hs x hx hvis => h2 s hs (-x) (by linarith) ?_⟩
  rw [hvis, LP.reflectC_ofReal]

/-- **The first return closes a seed gap.** -/
theorem first_return (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ⊤) (hord : IsOrderedForceWord xL xR)
    (hγ : IsGeneratingTrace w ⊤ γ) {k : Fin nR} (hk : xR k = 0) {l : Fin nL} (hl : xL l = 0)
    {u : ℝ≥0} (hu0 : 0 < u) (hu : γ u = 0) (hfirst : ∀ s : ℝ≥0, 0 < s → s < u → γ s ≠ 0) :
    (vR k u = w u ∧ ∀ s : ℝ≥0, s < u → ∀ x : ℝ, 0 < x → γ s ≠ x) ∨
      (vL l u = w u ∧ ∀ s : ℝ≥0, s < u → ∀ x : ℝ, x < 0 → γ s ≠ x) := by
  have h := hp.isForcePath
  have hwc := continuous_of_lt_top h.continuousOn_w
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := hwc.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp [hWdef, h.w_zero]
  have hη := isLoewnerTrace_of_isGeneratingTrace hγ
  have hev : ∀ ε > 0, ∀ᶠ t in 𝓝[<] u,
      (vR k t - w t < ε ∧ ∀ s : ℝ≥0, s ≤ t → ∀ x : ℝ, 0 < x → γ s ≠ x) ∨
        (w t - vL l t < ε ∧ ∀ s : ℝ≥0, s ≤ t → ∀ x : ℝ, x < 0 → γ s ≠ x) := by
    intro ε hε
    have hWu : UniformContinuousOn W (Icc 0 u) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hW.continuousOn
    obtain ⟨ρ, hρ, hWρ⟩ := Metric.uniformContinuousOn_iff.1 hWu (ε / 96) (by positivity)
    have hlim : Tendsto (fun t : ℝ≥0 => (u : ℝ) - t) (𝓝[<] u) (𝓝 0) := by
      have : Tendsto (fun t : ℝ≥0 => (u : ℝ) - t) (𝓝 u) (𝓝 ((u : ℝ) - u)) :=
        (continuous_const.sub NNReal.continuous_coe).tendsto u
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    filter_upwards [hlim.eventually (gt_mem_nhds (lt_min hρ (by positivity : (0 : ℝ) < (ε / 32) ^ 2))),
      Ioo_mem_nhdsLT hu0] with t ht htu
    have htu' : (t : ℝ) ≤ u := NNReal.coe_le_coe.2 htu.2.le
    have hM : ∀ r ∈ Icc (0 : ℝ) (u - t), |W (t + r) - W t| ≤ ε / 96 := fun r hr => by
      have hd : dist (t + r) (t : ℝ) < ρ := by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hr.1]
        linarith [ht.trans_le (min_le_left _ _), hr.2]
      have := hWρ (t + r) ⟨by linarith [hr.1, t.coe_nonneg], by linarith [hr.2]⟩ t ⟨t.coe_nonneg, htu'⟩ hd
      rw [Real.dist_eq] at this
      exact this.le
    have hu' : (fun s : ℝ => γ s.toNNReal) (u : ℝ) = 0 := by simpa using hu
    obtain ⟨c, hcb, hcF⟩ := exists_extendFrom_eq_zero_of_return hη hW hW0 t.coe_nonneg htu' hu' hM
    have hsq : 8 * Real.sqrt ((u : ℝ) - t) < ε / 4 := by
      have : Real.sqrt ((u : ℝ) - t) < ε / 32 := by
        rw [Real.sqrt_lt' (by positivity)]
        exact ht.trans_le (min_le_right _ _)
      linarith
    have hcε : |c| < ε := by linarith
    have hret : ∀ s : ℝ≥0, 0 < s → s ≤ t → γ s ≠ 0 := fun s hs hst => hfirst s hs (hst.trans_lt htu.2)
    rcases lt_trichotomy c 0 with hneg | hzero | hpos
    · obtain ⟨h1, h2⟩ := zero_left h hγ hl hret hneg hcF
      right
      refine ⟨?_, h2⟩
      rw [abs_of_neg hneg] at hcε
      linarith
    · exfalso
      rw [hzero] at hcF
      have htip : extendFrom H (fwdMapInv W t) ((0 : ℝ) : ℂ) = γ t := by
        have := hη.loewnerTip_eq hW hW0 t.coe_nonneg
        unfold loewnerTip at this
        simpa using this
      exact hfirst t htu.1 htu.2 (by rw [← htip]; exact hcF)
    · obtain ⟨h1, h2⟩ := zero_right h hγ hk hret hpos hcF
      left
      refine ⟨?_, h2⟩
      rw [abs_of_pos hpos] at hcε
      linarith
  have hsep : vL l u < vR k u := hp.vL_lt_vR_of_pos hord hu0 ENNReal.coe_lt_top l k
  have hgR : 0 ≤ vR k u - w u := sub_nonneg.2 (h.w_le_vR ENNReal.coe_lt_top k)
  have hgL : 0 ≤ w u - vL l u := sub_nonneg.2 (h.vL_le_w ENNReal.coe_lt_top l)
  have hcR : Tendsto (fun t => vR k t - w t) (𝓝[<] u) (𝓝 (vR k u - w u)) :=
    (((continuous_of_lt_top (h.continuousOn_vR k)).sub hwc).tendsto u).mono_left nhdsWithin_le_nhds
  have hcL : Tendsto (fun t => w t - vL l t) (𝓝[<] u) (𝓝 (w u - vL l u)) :=
    ((hwc.sub (continuous_of_lt_top (h.continuousOn_vL l))).tendsto u).mono_left nhdsWithin_le_nhds
  have hne : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu0⟩
  by_cases hR0 : vR k u - w u = 0
  · left
    refine ⟨by linarith, fun s hs x hx => ?_⟩
    have hLpos : 0 < w u - vL l u := by linarith
    obtain ⟨t, ⟨ht, htL⟩, hts⟩ := (((hev ((w u - vL l u) / 2) (by positivity)).and
      (hcL.eventually (lt_mem_nhds (by linarith : (w u - vL l u) / 2 < w u - vL l u)))).and
        (Ioo_mem_nhdsLT hs)).exists
    rcases ht with ⟨-, hoff⟩ | ⟨hlt, -⟩
    · exact hoff s hts.1.le x hx
    · exact absurd htL (not_lt.2 hlt.le)
  · by_cases hL0 : w u - vL l u = 0
    · right
      refine ⟨by linarith, fun s hs x hx => ?_⟩
      have hRpos : 0 < vR k u - w u := lt_of_le_of_ne hgR (Ne.symm hR0)
      obtain ⟨t, ⟨ht, htR⟩, hts⟩ := (((hev ((vR k u - w u) / 2) (by positivity)).and
        (hcR.eventually (lt_mem_nhds (by linarith : (vR k u - w u) / 2 < vR k u - w u)))).and
          (Ioo_mem_nhdsLT hs)).exists
      rcases ht with ⟨hlt, -⟩ | ⟨-, hoff⟩
      · exact absurd htR (not_lt.2 hlt.le)
      · exact hoff s hts.1.le x hx
    · exfalso
      have hRpos : 0 < vR k u - w u := lt_of_le_of_ne hgR (Ne.symm hR0)
      have hLpos : 0 < w u - vL l u := lt_of_le_of_ne hgL (Ne.symm hL0)
      set ε := min (vR k u - w u) (w u - vL l u) / 2 with hεdef
      have hε : 0 < ε := by positivity
      have hεR : ε < vR k u - w u := by
        have := min_le_left (vR k u - w u) (w u - vL l u); rw [hεdef]; linarith
      have hεL : ε < w u - vL l u := by
        have := min_le_right (vR k u - w u) (w u - vL l u); rw [hεdef]; linarith
      obtain ⟨t, ht, htR, htL⟩ := ((hev ε hε).and ((hcR.eventually (lt_mem_nhds hεR)).and
        (hcL.eventually (lt_mem_nhds hεL)))).exists
      rcases ht with ⟨hlt, -⟩ | ⟨hlt, -⟩
      · linarith
      · linarith

end First

end CfNoReturn

end InteractingSLE
