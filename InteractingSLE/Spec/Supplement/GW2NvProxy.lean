/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NvSeed

/-!
# The canonical stage path at the death, read through the versions (one sample)

Packet PROVE-GW2-NOTHR (round 4, D46). BUF's `DeathThrXStatement` quantifies over every canonical driver `Wc`
(continuous, equal to every version below its cap). For the kernel-to-`P` step the threshold at the death must be a
measurable event. On a sample where the versions' caps increase, stay below the death clock `d` and exhaust
`[0, d)` (RELDET's death family, D27), every such `Wc` is the limit of the versions on `[0, d]`. Each version is
frozen after its cap. The stage path's value at the death and its right images are iterated limits of the versions'
stage paths:

* **`tendsto_versions`**: `R n q → Wc q` for `q ≤ d`;
* **`tendsto_stage_at`**, **`eventually_rightImg_eq`**, **`eventually_rightImg_neg_eq`**: the stage paths and their
  right images before the death;
* **`stageProxyW`**, **`stageProxyR`**, **`stageProxyL`** and **`stageProxy_eq`**: the iterated `limsup`s, equal to the
  value at the death and its right / left images.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Nv

open MartChar.RealFlow GW2Rd

/-- The times `u − 1/(k+1)` (clipped at `0`) increasing to `u`. -/
def tk (u : ℝ≥0) (k : ℕ) : ℝ≥0 := ((u : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal

theorem tk_le (u : ℝ≥0) (k : ℕ) : tk u k ≤ u := by
  unfold tk
  rw [Real.toNNReal_le_iff_le_coe]
  have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  linarith

theorem tk_lt {u : ℝ≥0} (hu : 0 < u) (k : ℕ) : tk u k < u := by
  unfold tk
  have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  rcases le_or_gt ((u : ℝ) - 1 / ((k : ℝ) + 1)) 0 with h | h
  · rw [Real.toNNReal_of_nonpos h]; exact hu
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ h.le]
    linarith

theorem tendsto_tk (u : ℝ≥0) : Tendsto (tk u) atTop (𝓝 u) := by
  have h : Tendsto (fun k : ℕ => (u : ℝ) - 1 / ((k : ℝ) + 1)) atTop (𝓝 ((u : ℝ) - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at h
  have h2 := (continuous_real_toNNReal.tendsto _).comp h
  rwa [Real.toNNReal_coe] at h2

/-- The value of a stage path at the death, read through the versions. -/
def stageProxyW (R : ℕ → ℝ≥0 → ℝ) (S u : ℝ≥0) : ℝ := limsup (fun n => stgDrv (R n) S u) atTop

/-- The right image of a mark at the death, read through the versions' stage paths. -/
def stageProxyR (R : ℕ → ℝ≥0 → ℝ) (S u : ℝ≥0) (x : ℝ) : ℝ :=
  limsup (fun k => limsup (fun n => rightImg (fun v : ℝ => stgDrv (R n) S v.toNNReal) x (tk u k)) atTop) atTop

/-- The left image of a mark at the death, read through the versions' stage paths (reflected). -/
def stageProxyL (R : ℕ → ℝ≥0 → ℝ) (S u : ℝ≥0) (x : ℝ) : ℝ :=
  -limsup (fun k => limsup (fun n => rightImg (fun v : ℝ => -stgDrv (R n) S v.toNNReal) (-x) (tk u k)) atTop)
    atTop

section Sample

variable {R : ℕ → ℝ≥0 → ℝ} {V : ℕ → ℝ≥0∞} {d : ℝ≥0} {Wc : ℝ≥0 → ℝ}
  (hRc : ∀ n, Continuous (R n)) (hR0 : ∀ n, R n 0 = 0) (hmono : Monotone V)
  (hfrz : ∀ n (t : ℝ≥0), V n ≤ t → R n t = R n (V n).toNNReal)
  (hcaps : ∀ n, V n < d) (hexh : ∀ q : ℝ≥0, q < d → ∃ n, (q : ℝ≥0∞) < V n)
  (hWc : Continuous Wc) (hW0 : Wc 0 = 0) (hagree : ∀ n (q : ℝ≥0), (q : ℝ≥0∞) < V n → R n q = Wc q)

include hmono hagree in
/-- Before the death the versions eventually equal the canonical driver up to a time. -/
theorem eventually_eqOn_versions {t : ℝ≥0} (ht : ∃ n, (t : ℝ≥0∞) < V n) :
    ∀ᶠ n in atTop, ∀ q ≤ t, R n q = Wc q := by
  obtain ⟨N, hN⟩ := ht
  filter_upwards [eventually_ge_atTop N] with n hn q hq
  exact hagree n q ((ENNReal.coe_le_coe.2 hq).trans_lt (hN.trans_le (hmono hn)))

include hRc hR0 hcaps hWc hW0 hagree in
/-- At its cap a version is the canonical driver. -/
theorem version_at_cap (n : ℕ) : R n (V n).toNNReal = Wc (V n).toNNReal := by
  set v := (V n).toNNReal with hvdef
  have hVv : V n = v := (ENNReal.coe_toNNReal (hcaps n).ne_top).symm
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ v) with h0 | hpos
  · rw [← h0, hR0, hW0]
  · have hcl : IsClosed {t : ℝ≥0 | R n t = Wc t} := isClosed_eq (hRc n) hWc
    have hsub : Iio v ⊆ {t : ℝ≥0 | R n t = Wc t} := fun t ht =>
      hagree n t (by rw [hVv]; exact ENNReal.coe_lt_coe.2 ht)
    have hmem : v ∈ closure (Iio v) := by
      rw [closure_Iio' (show (Iio v).Nonempty from ⟨0, hpos⟩)]
      exact Set.mem_Iic.2 le_rfl
    exact closure_minimal hsub hcl hmem

include hmono hcaps hexh in
/-- The caps increase to the death. -/
theorem tendsto_caps : Tendsto (fun n => (V n).toNNReal) atTop (𝓝 d) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun n => ?_⟩
  · obtain ⟨N, hN⟩ := hexh a ha
    filter_upwards [eventually_ge_atTop N] with n hn
    have h := hN.trans_le (hmono hn)
    rw [← ENNReal.coe_toNNReal (hcaps n).ne_top] at h
    exact ENNReal.coe_lt_coe.1 h
  · have h := hcaps n
    rw [← ENNReal.coe_toNNReal h.ne_top] at h
    exact (ENNReal.coe_lt_coe.1 h).trans ha

include hRc hR0 hmono hfrz hcaps hexh hWc hW0 hagree in
/-- **The versions converge to the canonical driver on `[0, d]`.** -/
theorem tendsto_versions {q : ℝ≥0} (hq : q ≤ d) : Tendsto (fun n => R n q) atTop (𝓝 (Wc q)) := by
  rcases hq.lt_or_eq with hlt | rfl
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_eqOn_versions hmono hagree (hexh q hlt)] with n hn
    exact (hn q le_rfl).symm
  · have heq : ∀ n, R n q = Wc (V n).toNNReal := fun n => by
      rw [hfrz n q (hcaps n).le]
      exact version_at_cap hRc hR0 hcaps hWc hW0 hagree n
    simp only [heq]
    exact (hWc.tendsto q).comp (tendsto_caps hmono hcaps hexh)

include hRc hR0 hmono hfrz hcaps hexh hWc hW0 hagree in
/-- The versions' stage paths converge to the canonical stage path up to the death. -/
theorem tendsto_stage_at {S u : ℝ≥0} (hSu : S + u ≤ d) :
    Tendsto (fun n => stgDrv (R n) S u) atTop (𝓝 (stgDrv Wc S u)) :=
  (tendsto_versions hRc hR0 hmono hfrz hcaps hexh hWc hW0 hagree hSu).sub
    (tendsto_versions hRc hR0 hmono hfrz hcaps hexh hWc hW0 hagree (le_self_add.trans hSu))

include hmono hexh hWc hagree in
/-- Before the death the versions' stage paths eventually have the canonical stage path's right images. -/
theorem eventually_rightImg_eq {S t : ℝ≥0} (hSt : S + t < d) (x : ℝ) :
    ∀ᶠ n in atTop, rightImg (fun v : ℝ => stgDrv (R n) S v.toNNReal) x t =
      rightImg (fun v : ℝ => stgDrv Wc S v.toNNReal) x t := by
  filter_upwards [eventually_eqOn_versions hmono hagree (hexh _ hSt)] with n hn
  refine Sec7.Lemma71B.rightImg_congr ((continuous_stgDrv hWc S).comp continuous_real_toNNReal) t.coe_nonneg
    (fun v hv => ?_) x
  have hvt : v.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hv.2
  simp only [Function.comp_apply, stgDrv]
  rw [hn _ (add_le_add le_rfl hvt), hn _ le_self_add]

include hmono hexh hWc hagree in
/-- Before the death the versions' stage paths eventually have the canonical stage path's reflected right images. -/
theorem eventually_rightImg_neg_eq {S t : ℝ≥0} (hSt : S + t < d) (x : ℝ) :
    ∀ᶠ n in atTop, rightImg (fun v : ℝ => -stgDrv (R n) S v.toNNReal) x t =
      rightImg (fun v : ℝ => -stgDrv Wc S v.toNNReal) x t := by
  filter_upwards [eventually_eqOn_versions hmono hagree (hexh _ hSt)] with n hn
  refine Sec7.Lemma71B.rightImg_congr ((continuous_stgDrv hWc S).comp continuous_real_toNNReal).neg
    t.coe_nonneg (fun v hv => ?_) x
  have hvt : v.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hv.2
  simp only [Function.comp_apply, Pi.neg_apply, stgDrv]
  rw [hn _ (add_le_add le_rfl hvt), hn _ le_self_add]

include hRc hR0 hmono hfrz hcaps hexh hWc hW0 hagree in
/-- **The proxies are the canonical stage path's value and images at the death** (`S + u = d`, `0 < u`). -/
theorem stageProxy_eq {S u : ℝ≥0} (hSu : S + u = d) (hu : 0 < u) :
    stageProxyW R S u = stgDrv Wc S u ∧
      (∀ x, stageProxyR R S u x = rightImg (fun v : ℝ => stgDrv Wc S v.toNNReal) x u) ∧
      ∀ x, stageProxyL R S u x = -rightImg (fun v : ℝ => -stgDrv Wc S v.toNNReal) (-x) u := by
  have hD : Continuous fun v : ℝ => stgDrv Wc S v.toNNReal := (continuous_stgDrv hWc S).comp continuous_real_toNNReal
  have hlt : ∀ k, S + tk u k < d := fun k => by
    rw [← hSu]; exact add_lt_add_of_le_of_lt le_rfl (tk_lt hu k)
  have htime : ∀ (w : ℝ → ℝ), Continuous w → ∀ x,
      Tendsto (fun k => rightImg w x (tk u k)) atTop (𝓝 (rightImg w x u)) := fun w hw x =>
    ((continuousOn_rightImg hw x).continuousWithinAt (u.coe_nonneg : (0 : ℝ) ≤ u)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨(NNReal.continuous_coe.tendsto u).comp (tendsto_tk u),
        Eventually.of_forall fun k => (tk u k).coe_nonneg⟩)
  refine ⟨(tendsto_stage_at hRc hR0 hmono hfrz hcaps hexh hWc hW0 hagree hSu.le).limsup_eq, fun x => ?_,
    fun x => ?_⟩
  · unfold stageProxyR
    have hin : ∀ k, limsup (fun n => rightImg (fun v : ℝ => stgDrv (R n) S v.toNNReal) x (tk u k)) atTop =
        rightImg (fun v : ℝ => stgDrv Wc S v.toNNReal) x (tk u k) := fun k =>
      (tendsto_const_nhds.congr'
        ((eventually_rightImg_eq hmono hexh hWc hagree (hlt k) x).mono fun _ h => h.symm)).limsup_eq
    simp only [hin]
    exact (htime _ hD x).limsup_eq
  · unfold stageProxyL
    have hin : ∀ k, limsup (fun n => rightImg (fun v : ℝ => -stgDrv (R n) S v.toNNReal) (-x) (tk u k)) atTop =
        rightImg (fun v : ℝ => -stgDrv Wc S v.toNNReal) (-x) (tk u k) := fun k =>
      (tendsto_const_nhds.congr'
        ((eventually_rightImg_neg_eq hmono hexh hWc hagree (hlt k) (-x)).mono fun _ h => h.symm)).limsup_eq
    simp only [hin]
    rw [(htime (fun v : ℝ => -stgDrv Wc S v.toNNReal) hD.neg (-x)).limsup_eq]

end Sample

end InteractingSLE.Theorem14.GW2Nv
