/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactImgDriver

/-!
# The image word of the contact step, part 1: the killed word of a killed arc

Packet PROVE-WW-B17, deterministic part of steps B1–B2 of PROVE-WW-B15's plan. Wang–Wu
(`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of Proposition 4.18 (text dump L1626–1629:
"Map this domain to `H`, taking the start to `0` and `β(s)` to `∞`. Before contact, the simple forward trace has
continuous driving in this domain. … satisfy Lemma 2.11").

For a killed arc `γ` on `P` (`IsKilledArc`, PROVE-WW-B15) this file builds the killed force-point word that Lemma 2.11 is
applied to, pathwise:

* `kLife γ P` (the terminal capacity `sup_{S ∈ P} σ(S)` of the arc) and `lt_kLife_iff`;
* `kW γ P` (the glued driver `chainDrv γ P`, killed at `kLife`, `0` afterwards), continuous before `kLife`;
* `kVL γ P xL`, `kVR γ P xR` (the geometric images of real marks under the killed driver);
* **`IsKilledArc.exists_traceDriver`**: on each `[0, σ(S)]` the glued driver agrees with a continuous driver whose
  Loewner trace is a simple proper arc through `γ(u)` at `σ(u)`, `u ≤ S`;
* **`IsKilledArc.kVLr_lt_kW`**, **`IsKilledArc.kW_lt_kVRr`**: strict separation of the marks at positive times (the arc is
  simple and lies in `ℍ`), and the deterministic clauses of `ImgDrv.IsKilledWord`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open MartChar MartChar.RealFlow

namespace ImgWord

variable {γ : ℝ → ℂ} {P : Set ℝ}

/-! ### A trace driver on each prefix -/

/-- **A trace driver on each prefix**: on `[0, σ(S)]`, `0 < S ∈ P`, the glued driver agrees with a continuous driver
started at `0` whose Loewner trace is a simple proper arc passing through `γ(u)` at the capacity time `σ(u)`, `u ≤ S`
(PROVE-WW-B14's `exists_trace_of_simple` on a longer prefix, frozen after `σ(S)`). -/
theorem _root_.InteractingSLE.WangWu.IsKilledArc.exists_traceDriver (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P)
    (hS0 : 0 < S) :
    ∃ w : ℝ → ℝ, Continuous w ∧ w 0 = 0 ∧ EqOn (chainDrv γ P) w (Icc 0 (capClock γ S)) ∧
      ∃ η : ℝ → ℂ, IsLoewnerTrace w η ∧ IsProperArc η ∧ ∀ u ∈ Icc 0 S, η (capClock γ u) = γ u := by
  obtain ⟨S', hS', hSS'⟩ := hγ.exists_gt S hS
  have hS'0 : 0 < S' := hS0.trans hSS'
  have hsub := hγ.icc S' hS'
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, -, hσ, η, hηL, hηP, hηγ, -⟩ := exists_trace_of_simple hS'0
    (hγ.cont.mono hsub) (hγ.inj.mono hsub) hγ.zero (fun u hu => hγ.mem_H u (hsub ⟨hu.1.le, hu.2⟩) hu.1)
    (t := S) ⟨hS0, hSS'⟩
  have hσnn : ∀ u ∈ Icc 0 S', 0 ≤ σ u := fun u hu => by
    rw [← hσ0]; exact hσm.monotoneOn ⟨le_rfl, hS'0.le⟩ hu hu.1
  have heq : EqOn σ (capClock γ) (Icc 0 S') := fun u hu => by
    have h1 : fwdHull W (σ u) = fillH (γ '' Icc 0 u) := by
      rw [hσ u hu, hγ.fillH_eq (hsub ⟨hu.1, hu.2⟩)]
    have := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hW hW0 (hσnn u hu) h1
    simp only [capClock, this]
    ring
  have hσS : σ S = capClock γ S := heq ⟨hS0.le, hSS'.le⟩
  -- the chosen driver agrees with the glued driver on `[0, σ(S')]`
  obtain ⟨W₂, hW₂, hW₂0, hEq₂, hK₂⟩ := hγ.chainDrv_spec hS' hS'0
  obtain ⟨-, -, -, -, -, hcc, -⟩ := hγ.exists_localDriver hS' hS'0
  have hagree : EqOn W₂ W (Icc 0 (capClock γ S')) := by
    refine Sec6.eqOn_of_fwdHull_eq hW₂ hW hW₂0 hW0 (hγ.capClock_nonneg hS') fun r hr => ?_
    obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc hS'0.le hcc (by rw [hγ.capClock_zero]; exact hr)
    rw [hK₂ u hu, ← heq hu, hσ u hu]
  have hmono : capClock γ S ≤ capClock γ S' :=
    hγ.strictMonoOn_capClock.monotoneOn hS hS' hSS'.le
  refine ⟨YuanCorollary13.extDrive W (σ S), YuanCorollary13.continuous_extDrive hW,
    YuanCorollary13.extDrive_zero hW0 (hσnn S ⟨hS0.le, hSS'.le⟩), fun r hr => ?_, η, hηL, hηP,
    fun u hu => ?_⟩
  · rw [YuanCorollary13.extDrive_eq (by rw [hσS]; exact hr.2)]
    exact (hEq₂ ⟨hr.1, hr.2.trans hmono⟩).trans (hagree ⟨hr.1, hr.2.trans hmono⟩)
  · rw [← heq ⟨hu.1, hu.2.trans hSS'.le⟩]
    exact hηγ u hu

/-! ### The terminal capacity -/

/-- **The terminal capacity of a killed arc**: `sup_{S ∈ P} σ(S)`. -/
def kLife (γ : ℝ → ℂ) (P : Set ℝ) : WithTop ℝ≥0 :=
  ⨆ S ∈ P, (((capClock γ S).toNNReal : ℝ≥0) : WithTop ℝ≥0)

theorem lt_kLife_iff {t : ℝ≥0} : (t : WithTop ℝ≥0) < kLife γ P ↔ ∃ S ∈ P, (t : ℝ) < capClock γ S := by
  unfold kLife
  simp only [lt_iSup_iff, WithTop.coe_lt_coe, exists_prop, Real.lt_toNNReal_iff_coe_lt]

end ImgWord

open ImgWord

variable {γ : ℝ → ℂ} {P : Set ℝ}

theorem IsKilledArc.lt_kLife (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P) :
    (((capClock γ S).toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := by
  obtain ⟨S', hS', hSS'⟩ := hγ.exists_gt S hS
  refine lt_kLife_iff.2 ⟨S', hS', ?_⟩
  rw [Real.coe_toNNReal _ (hγ.capClock_nonneg hS)]
  exact hγ.strictMonoOn_capClock hS hS' hSS'

theorem IsKilledArc.zero_lt_kLife (hγ : IsKilledArc γ P) : (0 : WithTop ℝ≥0) < kLife γ P := by
  have := hγ.lt_kLife hγ.zero_mem
  rwa [hγ.capClock_zero, Real.toNNReal_zero, WithTop.coe_zero] at this

/-! ### Driver paths that are locally continuous before a time -/

namespace ImgWord

/-- `p` agrees, on `[0, c]` for some `c` beyond each time `t` before `L`, with a continuous driver. -/
def IsLocCont (p : ℝ → ℝ) (L : WithTop ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < L → ∃ c : ℝ, (t : ℝ) < c ∧ ∃ w : ℝ → ℝ, Continuous w ∧ EqOn p w (Icc 0 c)

/-- The geometric image of a right mark `x` under the driver path `p`, read on `ℝ≥0`. -/
def kImg (p : ℝ → ℝ) (x : ℝ) (t : ℝ≥0) : ℝ := rightImg p x t

variable {p : ℝ → ℝ} {L : WithTop ℝ≥0}

theorem continuousOn_of_locally_eq' {f : ℝ≥0 → ℝ} {U : Set ℝ≥0}
    (h : ∀ t ∈ U, ∃ g : ℝ≥0 → ℝ, Continuous g ∧ f =ᶠ[𝓝 t] g) : ContinuousOn f U := fun t ht => by
  obtain ⟨g, hg, hfg⟩ := h t ht
  exact (hg.continuousAt.congr hfg.symm).continuousWithinAt

theorem IsLocCont.neg (hp : IsLocCont p L) : IsLocCont (fun r => -p r) L := fun t ht => by
  obtain ⟨c, htc, w, hw, h⟩ := hp t ht
  exact ⟨c, htc, fun r => -w r, hw.neg, fun r hr => by simp only [h hr]⟩

theorem kImg_eq {w : ℝ → ℝ} (hw : Continuous w) {c : ℝ} (h : EqOn p w (Icc 0 c)) {t : ℝ≥0} (ht : (t : ℝ) ≤ c)
    (x : ℝ) : kImg p x t = rightImg w x t :=
  Sec7.Lemma71B.rightImg_congr hw t.coe_nonneg (h.mono (Icc_subset_Icc_right ht)) x

theorem IsLocCont.le_kImg (hp : IsLocCont p L) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < L) (x : ℝ) :
    p t ≤ kImg p x t := by
  obtain ⟨c, htc, w, hw, h⟩ := hp t ht
  rw [kImg_eq hw h htc.le, h ⟨t.coe_nonneg, htc.le⟩]
  exact le_rightImg hw x t.coe_nonneg

theorem IsLocCont.kImg_mono_time (hp : IsLocCont p L) {a b : ℝ≥0} (hb : (b : WithTop ℝ≥0) < L) (hab : a ≤ b)
    (x : ℝ) : kImg p x a ≤ kImg p x b := by
  obtain ⟨c, hbc, w, hw, h⟩ := hp b hb
  rw [kImg_eq hw h ((NNReal.coe_le_coe.2 hab).trans hbc.le), kImg_eq hw h hbc.le]
  exact rightImg_mono_time hw x a.coe_nonneg (NNReal.coe_le_coe.2 hab)

theorem IsLocCont.kImg_mono_index (hp : IsLocCont p L) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < L) {x x' : ℝ}
    (hx : x ≤ x') : kImg p x t ≤ kImg p x' t := by
  obtain ⟨c, htc, w, hw, h⟩ := hp t ht
  rw [kImg_eq hw h htc.le, kImg_eq hw h htc.le]
  exact rightImg_mono_index hw t.coe_nonneg hx

theorem IsLocCont.kImg_merge (hp : IsLocCont p L) {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : WithTop ℝ≥0) < L)
    {x x' : ℝ} (heq : kImg p x s = kImg p x' s) : kImg p x t = kImg p x' t := by
  obtain ⟨c, htc, w, hw, h⟩ := hp t ht
  have hsc : (s : ℝ) ≤ c := (NNReal.coe_le_coe.2 hst).trans htc.le
  rw [kImg_eq hw h hsc, kImg_eq hw h hsc] at heq
  rw [kImg_eq hw h htc.le, kImg_eq hw h htc.le]
  exact rightImg_eq_of_eq' hw s.coe_nonneg (NNReal.coe_le_coe.2 hst) heq

theorem IsLocCont.continuousOn_kImg (hp : IsLocCont p L) (x : ℝ) :
    ContinuousOn (kImg p x) {t | (t : WithTop ℝ≥0) < L} := by
  refine continuousOn_of_locally_eq' fun t₀ ht₀ => ?_
  obtain ⟨c, htc, w, hw, h⟩ := hp t₀ ht₀
  refine ⟨fun t => rightImg w x t, (continuousOn_rightImg hw x).comp_continuous NNReal.continuous_coe
    fun t => t.coe_nonneg, ?_⟩
  have hU : {t : ℝ≥0 | (t : ℝ) < c} ∈ 𝓝 t₀ :=
    (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds htc
  filter_upwards [hU] with t ht
  exact kImg_eq hw h ht.le x

theorem IsLocCont.continuousOn (hp : IsLocCont p L) :
    ContinuousOn (fun t : ℝ≥0 => p t) {t | (t : WithTop ℝ≥0) < L} := by
  refine continuousOn_of_locally_eq' fun t₀ ht₀ => ?_
  obtain ⟨c, htc, w, hw, h⟩ := hp t₀ ht₀
  refine ⟨fun t => w t, hw.comp NNReal.continuous_coe, ?_⟩
  have hU : {t : ℝ≥0 | (t : ℝ) < c} ∈ 𝓝 t₀ :=
    (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds htc
  filter_upwards [hU] with t ht
  exact h ⟨t.coe_nonneg, ht.le⟩

/-- **The force-path derivative** of a killed geometric image away from collisions. -/
theorem IsLocCont.hasDerivAt_kImg (hp : IsLocCont p L) (x : ℝ) {u : ℝ} (hu : 0 < u)
    (huL : ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) < L) (hne : kImg p x u.toNNReal ≠ p u) :
    HasDerivAt (fun r : ℝ => kImg p x r.toNNReal) (2 / (kImg p x u.toNNReal - p u)) u := by
  obtain ⟨c, huc, w, hw, h⟩ := hp _ huL
  rw [Real.coe_toNNReal _ hu.le] at huc
  have hcu : ((u.toNNReal : ℝ≥0) : ℝ) = u := Real.coe_toNNReal _ hu.le
  have hpu : p u = w u := h ⟨hu.le, huc.le⟩
  have hku : kImg p x u.toNNReal = rightImg w x u := by rw [kImg_eq hw h (by rw [hcu]; exact huc.le), hcu]
  have hne' : rightImg w x (u.toNNReal : ℝ) ≠ w (u.toNNReal : ℝ) := by
    rw [hcu, ← hku, ← hpu]; exact hne
  have hD := (isForcePath_rightImg hw x).2.2.1 u hu hne'
  simp only [hcu] at hD
  rw [hku, hpu]
  refine hD.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds huc] with r hr
  exact kImg_eq hw h ((Real.coe_toNNReal' r).trans_le (max_le hr.le (hu.le.trans huc.le))) x

/-- **A killed geometric image is a force path before `L`**, given strict separation at positive times. -/
theorem IsLocCont.isForcePathBefore (hp : IsLocCont p L) (x : ℝ)
    (hsep : ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) < L → p t < kImg p x t) :
    Sec7.PhaseSelAdapt.IsForcePathBefore (fun t : ℝ≥0 => p t) (kImg p x) L := by
  refine ⟨hp.continuousOn_kImg x, fun u hu huL hne => ?_, ?_⟩
  · have hne' : kImg p x u.toNNReal ≠ p u := by
      have e : ((u.toNNReal : ℝ≥0) : ℝ) = u := Real.coe_toNNReal _ hu.le
      simpa only [e] using hne
    have := hp.hasDerivAt_kImg x hu huL hne'
    rwa [show p u = p (u.toNNReal : ℝ≥0) by rw [Real.coe_toNNReal _ hu.le]] at this
  · refine measure_mono_null (fun u hu => ?_) (measure_singleton (0 : ℝ))
    obtain ⟨hu0, huL, heq⟩ := hu
    rcases hu0.eq_or_lt with h | h
    · exact h.symm
    · exfalso
      have := hsep u.toNNReal (Real.toNNReal_pos.2 h) huL
      rw [heq] at this
      exact lt_irrefl _ this

theorem isForcePathBefore_neg {w v : ℝ≥0 → ℝ} (h : Sec7.PhaseSelAdapt.IsForcePathBefore w v L) :
    Sec7.PhaseSelAdapt.IsForcePathBefore (fun t => -w t) (fun t => -v t) L := by
  obtain ⟨hc, hd, hz⟩ := h
  refine ⟨hc.neg, fun u hu huL hne => ?_, ?_⟩
  · have hne' : v u.toNNReal ≠ w u.toNNReal := fun h => hne (by simp only [h])
    have hD := (hd u hu huL hne').neg
    have he : 2 / (-v u.toNNReal - -w u.toNNReal) = -(2 / (v u.toNNReal - w u.toNNReal)) := by
      rw [show -v u.toNNReal - -w u.toNNReal = -(v u.toNNReal - w u.toNNReal) by ring, div_neg]
    rw [he]
    exact hD
  · simpa only [neg_inj] using hz

/-! ### The killed word of a killed arc -/

open scoped Classical in
/-- **The killed glued driver** of a killed arc: `chainDrv γ P` before `kLife γ P`, `0` afterwards. -/
def kW (γ : ℝ → ℂ) (P : Set ℝ) (t : ℝ≥0) : ℝ := if (t : WithTop ℝ≥0) < kLife γ P then chainDrv γ P t else 0

/-- The killed driver as a path on `ℝ`. -/
def kPath (γ : ℝ → ℂ) (P : Set ℝ) (r : ℝ) : ℝ := kW γ P r.toNNReal

/-- The images of right marks `xR j ≥ 0` under the killed driver (at every time). -/
def kVRr (γ : ℝ → ℂ) (P : Set ℝ) {n : ℕ} (xR : Fin n → ℝ) (j : Fin n) (t : ℝ≥0) : ℝ := kImg (kPath γ P) (xR j) t

/-- The images of left marks `xL i ≤ 0` under the killed driver (by reflection; at every time). -/
def kVLr (γ : ℝ → ℂ) (P : Set ℝ) {n : ℕ} (xL : Fin n → ℝ) (i : Fin n) (t : ℝ≥0) : ℝ :=
  -kImg (fun r => -kPath γ P r) (-xL i) t

variable {γ : ℝ → ℂ} {P : Set ℝ}

theorem kPath_coe (t : ℝ≥0) : kPath γ P t = kW γ P t := by simp [kPath]

theorem kPath_eq_kW : (fun t : ℝ≥0 => kPath γ P t) = kW γ P := funext kPath_coe

theorem kW_of_lt {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kLife γ P) : kW γ P t = chainDrv γ P t := by
  simp only [kW, ht, ↓reduceIte]

end ImgWord

open ImgWord

/-- **The killed driver near a time before the terminal capacity**: up to some `c = σ(S)` beyond `t` it agrees with a
continuous driver started at `0` whose Loewner trace is a simple proper arc through `γ(u)` at `σ(u)`, `u ≤ S`. -/
theorem IsKilledArc.exists_kPath_trace (hγ : IsKilledArc γ P) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kLife γ P) :
    ∃ S ∈ P, 0 < S ∧ (t : ℝ) < capClock γ S ∧ ∃ w : ℝ → ℝ, Continuous w ∧ w 0 = 0 ∧
      EqOn (kPath γ P) w (Icc 0 (capClock γ S)) ∧
      ∃ η : ℝ → ℂ, IsLoewnerTrace w η ∧ IsProperArc η ∧ ∀ u ∈ Icc 0 S, η (capClock γ u) = γ u := by
  obtain ⟨S, hS, htS⟩ := lt_kLife_iff.1 ht
  have hS0 : 0 < S := by
    refine lt_of_le_of_ne (hγ.nonneg S hS) fun h => ?_
    rw [← h, hγ.capClock_zero] at htS
    exact absurd htS (not_lt.2 t.coe_nonneg)
  obtain ⟨w, hw, hw0, hEq, η, hηL, hηP, hηγ⟩ := hγ.exists_traceDriver hS hS0
  refine ⟨S, hS, hS0, htS, w, hw, hw0, fun r hr => ?_, η, hηL, hηP, hηγ⟩
  have hlt : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife γ P :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr.2)) (hγ.lt_kLife hS)
  show kW γ P r.toNNReal = w r
  rw [kW_of_lt hlt, Real.coe_toNNReal _ hr.1]
  exact hEq hr

theorem IsKilledArc.isLocCont (hγ : IsKilledArc γ P) : IsLocCont (kPath γ P) (kLife γ P) := fun t ht => by
  obtain ⟨S, -, -, htS, w, hw, -, hEq, -⟩ := hγ.exists_kPath_trace ht
  exact ⟨_, htS, w, hw, hEq⟩

theorem IsKilledArc.kW_zero (hγ : IsKilledArc γ P) : kW γ P 0 = 0 := by
  obtain ⟨S, hS, -, -, w, -, hw0, hEq, -⟩ := hγ.exists_kPath_trace hγ.zero_lt_kLife
  have := hEq ⟨le_rfl, hγ.capClock_nonneg hS⟩
  rw [← kPath_coe, ← hw0]
  simpa using this

theorem IsKilledArc.continuousOn_kW (hγ : IsKilledArc γ P) :
    ContinuousOn (kW γ P) {t | (t : WithTop ℝ≥0) < kLife γ P} := by
  rw [← kPath_eq_kW]
  exact hγ.isLocCont.continuousOn

/-! ### Order and strict separation of the marks -/

theorem IsKilledArc.kW_le_kVRr (hγ : IsKilledArc γ P) {n : ℕ} (xR : Fin n → ℝ) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < kLife γ P) (j : Fin n) : kW γ P t ≤ kVRr γ P xR j t := by
  rw [← kPath_coe]
  exact hγ.isLocCont.le_kImg ht (xR j)

theorem IsKilledArc.kVLr_le_kW (hγ : IsKilledArc γ P) {n : ℕ} (xL : Fin n → ℝ) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < kLife γ P) (i : Fin n) : kVLr γ P xL i t ≤ kW γ P t := by
  have := hγ.isLocCont.neg.le_kImg ht (-xL i)
  rw [← kPath_coe]
  unfold kVLr
  linarith

/-- **Strict separation on the right**: at positive times before the terminal capacity, the images of marks
`xR j ≥ 0` lie strictly right of the driver (the arc is simple and lies in `ℍ`: PROVE-WW-B14's `chartAR_pos`). -/
theorem IsKilledArc.kW_lt_kVRr (hγ : IsKilledArc γ P) {n : ℕ} {xR : Fin n → ℝ} (hx : ∀ j, 0 ≤ xR j) {t : ℝ≥0}
    (ht0 : 0 < t) (ht : (t : WithTop ℝ≥0) < kLife γ P) (j : Fin n) : kW γ P t < kVRr γ P xR j t := by
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, η, hηL, hηP, -⟩ := hγ.exists_kPath_trace ht
  have hpos := chartAR_pos hηL hηP hw hw0 (show (0 : ℝ) < t from ht0)
  unfold chartAR at hpos
  have hm := rightImg_mono_index hw t.coe_nonneg (hx j)
  rw [← kPath_coe, kVRr, kImg_eq hw hEq htS.le, hEq ⟨t.coe_nonneg, htS.le⟩]
  linarith

/-- **Strict separation on the left** (PROVE-WW-B14's `chartAL_neg`). -/
theorem IsKilledArc.kVLr_lt_kW (hγ : IsKilledArc γ P) {n : ℕ} {xL : Fin n → ℝ} (hx : ∀ i, xL i ≤ 0) {t : ℝ≥0}
    (ht0 : 0 < t) (ht : (t : WithTop ℝ≥0) < kLife γ P) (i : Fin n) : kVLr γ P xL i t < kW γ P t := by
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, η, hηL, hηP, -⟩ := hγ.exists_kPath_trace ht
  have hneg0 := chartAL_neg hηL hηP hw hw0 (show (0 : ℝ) < t from ht0)
  unfold chartAL at hneg0
  have hneg : -rightImg (-w) 0 t - w t < 0 := hneg0
  have hEq' : EqOn (fun r => -kPath γ P r) (fun r => -w r) (Icc 0 (capClock γ S)) := fun r hr => by
    simp only [hEq hr]
  have hm := rightImg_mono_index hw.neg t.coe_nonneg (neg_nonneg.2 (hx i))
  rw [← kPath_coe, kVLr, kImg_eq hw.neg hEq' htS.le, hEq ⟨t.coe_nonneg, htS.le⟩]
  linarith

/-! ### The killed word -/

/-- **The killed word of a family of killed arcs**: the killed glued drivers with the images of left marks
`xL ≤ 0` (antitone in the index) and right marks `xR ≥ 0` (monotone in the index) satisfy the deterministic clauses of
Lemma 2.11's killed form (`ImgDrv.IsKilledWord`), killed at the terminal capacities. -/
theorem isKilledWord_kWr {Ω : Type*} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ}
    (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : ∀ ω i, xL ω i ≤ 0) (hxR : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) :
    ImgDrv.IsKilledWord (fun t ω => kW (γ ω) (P ω) t) (fun i t ω => kVLr (γ ω) (P ω) (xL ω) i t)
      (fun j t ω => kVRr (γ ω) (P ω) (xR ω) j t) (fun ω => kLife (γ ω) (P ω)) where
  w_zero ω := (hγ ω).kW_zero
  contW ω := (hγ ω).continuousOn_kW
  ordL ω t i ht := (hγ ω).kVLr_le_kW (xL ω) ht i
  ordR ω t j ht := (hγ ω).kW_le_kVRr (xR ω) ht j
  pathL ω i := by
    have h := isForcePathBefore_neg ((hγ ω).isLocCont.neg.isForcePathBefore (-xL ω i) fun t ht0 ht => by
      have := (hγ ω).kVLr_lt_kW (hxL ω) ht0 ht i
      rw [← kPath_coe] at this
      unfold kVLr at this
      show -kPath (γ ω) (P ω) t < _
      linarith)
    simp only [neg_neg, kPath_coe] at h
    exact h
  pathR ω j := by
    have h := (hγ ω).isLocCont.isForcePathBefore (xR ω j) fun t ht0 ht => by
      have := (hγ ω).kW_lt_kVRr (hxR ω) ht0 ht j
      rwa [← kPath_coe] at this
    simp only [kPath_coe] at h
    exact h
  antiL ω i a ha b hb hab := by
    have := (hγ ω).isLocCont.neg.kImg_mono_time hb hab (-xL ω i)
    show -kImg _ _ _ ≤ -kImg _ _ _
    linarith
  monoR ω j a ha b hb hab := (hγ ω).isLocCont.kImg_mono_time hb hab (xR ω j)
  idxL ω t ht a b hab := by
    have := (hγ ω).isLocCont.neg.kImg_mono_index ht (neg_le_neg (hxLa ω hab))
    show -kImg _ _ _ ≤ -kImg _ _ _
    linarith
  idxR ω t ht a b hab := (hγ ω).isLocCont.kImg_mono_index ht (hxRm ω hab)
  mergeL ω i j s t hst ht heq := by
    have heq' : kImg (fun r => -kPath (γ ω) (P ω) r) (-xL ω i) s =
        kImg (fun r => -kPath (γ ω) (P ω) r) (-xL ω j) s := neg_inj.1 heq
    show -kImg _ _ _ = -kImg _ _ _
    rw [(hγ ω).isLocCont.neg.kImg_merge hst ht heq']
  mergeR ω i j s t hst ht heq := (hγ ω).isLocCont.kImg_merge hst ht heq
  sepL ω t ht0 ht i := (hγ ω).kVLr_lt_kW (hxL ω) ht0 ht i
  sepR ω t ht0 ht j := (hγ ω).kW_lt_kVRr (hxR ω) ht0 ht j


namespace ImgWord

open scoped Classical in
/-- **The images of right marks** `xR j ≥ 0` under the killed driver before `kLife γ P`, `0` afterwards. -/
def kVR (γ : ℝ → ℂ) (P : Set ℝ) {n : ℕ} (xR : Fin n → ℝ) (j : Fin n) (t : ℝ≥0) : ℝ :=
  if (t : WithTop ℝ≥0) < kLife γ P then kVRr γ P xR j t else 0

open scoped Classical in
/-- **The images of left marks** `xL i ≤ 0` under the killed driver before `kLife γ P`, `0` afterwards. -/
def kVL (γ : ℝ → ℂ) (P : Set ℝ) {n : ℕ} (xL : Fin n → ℝ) (i : Fin n) (t : ℝ≥0) : ℝ :=
  if (t : WithTop ℝ≥0) < kLife γ P then kVLr γ P xL i t else 0

theorem kVR_of_lt {γ : ℝ → ℂ} {P : Set ℝ} {n : ℕ} (xR : Fin n → ℝ) (j : Fin n) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < kLife γ P) : kVR γ P xR j t = kVRr γ P xR j t := by
  simp only [kVR, ht, ↓reduceIte]

theorem kVL_of_lt {γ : ℝ → ℂ} {P : Set ℝ} {n : ℕ} (xL : Fin n → ℝ) (i : Fin n) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < kLife γ P) : kVL γ P xL i t = kVLr γ P xL i t := by
  simp only [kVL, ht, ↓reduceIte]

/-- A force path before `L` only depends on the force coordinate before `L`. -/
theorem isForcePathBefore_congr {L : WithTop ℝ≥0} {w v v' : ℝ≥0 → ℝ}
    (h : Sec7.PhaseSelAdapt.IsForcePathBefore w v L) (hv : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < L → v' t = v t) :
    Sec7.PhaseSelAdapt.IsForcePathBefore w v' L := by
  obtain ⟨hc, hd, hz⟩ := h
  refine ⟨hc.congr fun t ht => hv t ht, fun u hu huL hne => ?_, ?_⟩
  · have hvu := hv _ huL
    rw [hvu] at hne ⊢
    refine (hd u hu huL hne).congr_of_eventuallyEq ?_
    have hopen : IsOpen {r : ℝ | ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) < L} :=
      isOpen_lt (WithTop.continuous_coe.comp continuous_real_toNNReal) continuous_const
    filter_upwards [hopen.mem_nhds huL] with r hr
    exact hv _ hr
  · have e : {u : ℝ | 0 ≤ u ∧ ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) < L ∧ v' u.toNNReal = w u.toNNReal} =
        {u : ℝ | 0 ≤ u ∧ ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) < L ∧ v u.toNNReal = w u.toNNReal} := by
      ext u
      simp only [mem_ofPred_eq]
      exact and_congr_right fun _ => ⟨fun ⟨hL, he⟩ => ⟨hL, (hv _ hL).symm.trans he⟩,
        fun ⟨hL, he⟩ => ⟨hL, (hv _ hL).trans he⟩⟩
    rw [e]
    exact hz

end ImgWord

/-- **A killed word only depends on its force coordinates before the killing time.** -/
theorem ImgDrv.IsKilledWord.congr_marks {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}
    (h : ImgDrv.IsKilledWord W VL VR T) (hL : ∀ ω i (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → VL' i t ω = VL i t ω)
    (hR : ∀ ω j (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → VR' j t ω = VR j t ω) :
    ImgDrv.IsKilledWord W VL' VR' T where
  w_zero := h.w_zero
  contW := h.contW
  ordL ω t i ht := by rw [hL ω i t ht]; exact h.ordL ω t i ht
  ordR ω t j ht := by rw [hR ω j t ht]; exact h.ordR ω t j ht
  pathL ω i := isForcePathBefore_congr (h.pathL ω i) fun t ht => hL ω i t ht
  pathR ω j := isForcePathBefore_congr (h.pathR ω j) fun t ht => hR ω j t ht
  antiL ω i a ha b hb hab := by
    show VL' i b ω ≤ VL' i a ω
    rw [hL ω i a ha, hL ω i b hb]; exact h.antiL ω i ha hb hab
  monoR ω j a ha b hb hab := by
    show VR' j a ω ≤ VR' j b ω
    rw [hR ω j a ha, hR ω j b hb]; exact h.monoR ω j ha hb hab
  idxL ω t ht a b hab := by
    show VL' b t ω ≤ VL' a t ω
    rw [hL ω a t ht, hL ω b t ht]; exact h.idxL ω t ht hab
  idxR ω t ht a b hab := by
    show VR' a t ω ≤ VR' b t ω
    rw [hR ω a t ht, hR ω b t ht]; exact h.idxR ω t ht hab
  mergeL ω i j s t hst ht heq := by
    have hs : (s : WithTop ℝ≥0) < T ω := lt_of_le_of_lt (WithTop.coe_le_coe.2 hst) ht
    rw [hL ω i s hs, hL ω j s hs] at heq
    rw [hL ω i t ht, hL ω j t ht]; exact h.mergeL ω i j s t hst ht heq
  mergeR ω i j s t hst ht heq := by
    have hs : (s : WithTop ℝ≥0) < T ω := lt_of_le_of_lt (WithTop.coe_le_coe.2 hst) ht
    rw [hR ω i s hs, hR ω j s hs] at heq
    rw [hR ω i t ht, hR ω j t ht]; exact h.mergeR ω i j s t hst ht heq
  sepL ω t ht0 ht i := by rw [hL ω i t ht]; exact h.sepL ω t ht0 ht i
  sepR ω t ht0 ht j := by rw [hR ω j t ht]; exact h.sepR ω t ht0 ht j

/-- **The killed word of a family of killed arcs**: the killed glued drivers with the images of left marks
`xL ≤ 0` (antitone in the index) and right marks `xR ≥ 0` (monotone in the index), set to `0` after the killing,
satisfy the deterministic clauses of Lemma 2.11's killed form (`ImgDrv.IsKilledWord`), killed at the terminal
capacities. -/
theorem isKilledWord_kW {Ω : Type*} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ}
    (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : ∀ ω i, xL ω i ≤ 0) (hxR : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) :
    ImgDrv.IsKilledWord (fun t ω => kW (γ ω) (P ω) t) (fun i t ω => kVL (γ ω) (P ω) (xL ω) i t)
      (fun j t ω => kVR (γ ω) (P ω) (xR ω) j t) (fun ω => kLife (γ ω) (P ω)) :=
  (isKilledWord_kWr hγ hxL hxR hxLa hxRm).congr_marks (fun ω i _ ht => kVL_of_lt (xL ω) i ht)
    fun ω j _ ht => kVR_of_lt (xR ω) j ht

/-! ### The image trace in capacity time -/

namespace ImgWord

open scoped Classical in
/-- The inverse of the capacity clock of a killed arc on `P` (`0` off its range). -/
def kInv (γ : ℝ → ℂ) (P : Set ℝ) (r : ℝ) : ℝ := if h : ∃ u ∈ P, capClock γ u = r then h.choose else 0

/-- **The image trace in capacity time**: `γ ∘ σ⁻¹`. -/
def kTrace (γ : ℝ → ℂ) (P : Set ℝ) (r : ℝ≥0) : ℂ := γ (kInv γ P r)

/-- A generating trace on `[0, σ]` only depends on the trace on `[0, σ]`. -/
theorem isGeneratingTraceIcc_congr_trace {w : ℝ≥0 → ℝ} {σ : ℝ≥0} {η η' : ℝ≥0 → ℂ}
    (h : Sec7.IsGeneratingTraceIcc w σ η) (hη : ∀ r ≤ σ, η r = η' r) : Sec7.IsGeneratingTraceIcc w σ η' := by
  have himg : ∀ t ≤ σ, η '' Icc 0 t = η' '' Icc 0 t := fun t ht =>
    image_congr fun r hr => hη r (hr.2.trans ht)
  obtain ⟨⟨h0, hc, hf⟩, hfσ, htip⟩ := h
  refine ⟨⟨by rw [← hη 0 zero_le, h0], hc.congr fun r hr => (hη r (ENNReal.coe_le_coe.1 hr)).symm,
    fun t ht => ?_⟩, by rw [← himg σ le_rfl]; exact hfσ, by rw [← hη σ le_rfl]; exact htip⟩
  rw [← himg t (ENNReal.coe_le_coe.1 ht.le)]
  exact hf t ht

end ImgWord

theorem IsKilledArc.kInv_spec (hγ : IsKilledArc γ P) {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) < kLife γ P) :
    kInv γ P r ∈ P ∧ capClock γ (kInv γ P r) = r := by
  classical
  obtain ⟨S, hS, hrS⟩ := lt_kLife_iff.1 hr
  have hS0 : 0 ≤ S := hγ.nonneg S hS
  have hcc : ContinuousOn (capClock γ) (Icc 0 S) := hγ.continuousOn_capClock.mono (hγ.icc S hS)
  obtain ⟨u, hu, hur⟩ := intermediate_value_Icc hS0 hcc (by rw [hγ.capClock_zero]; exact ⟨r.coe_nonneg, hrS.le⟩)
  have hex : ∃ u ∈ P, capClock γ u = r := ⟨u, hγ.icc S hS hu, hur⟩
  rw [kInv, dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

theorem IsKilledArc.kInv_capClock (hγ : IsKilledArc γ P) {u : ℝ} (hu : u ∈ P) :
    kInv γ P (capClock γ u) = u := by
  classical
  have hex : ∃ v ∈ P, capClock γ v = capClock γ u := ⟨u, hu, rfl⟩
  rw [kInv, dite_eq_left_of_eq_true (eq_true hex)]
  exact hγ.strictMonoOn_capClock.injOn hex.choose_spec.1 hu hex.choose_spec.2

theorem IsKilledArc.kInv_le (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P) {r : ℝ≥0}
    (hr : (r : WithTop ℝ≥0) < kLife γ P) (hrS : (r : ℝ) ≤ capClock γ S) : kInv γ P r ≤ S := by
  obtain ⟨hm, he⟩ := hγ.kInv_spec hr
  by_contra hlt
  have := hγ.strictMonoOn_capClock hS hm (not_le.1 hlt)
  rw [he] at this
  linarith

/-- **The image trace generates the killed chain** on every `[0, t]`, `t` before the terminal capacity, with its tip. -/
theorem IsKilledArc.isGeneratingTraceIcc_kTrace (hγ : IsKilledArc γ P) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < kLife γ P) : Sec7.IsGeneratingTraceIcc (kW γ P) t (kTrace γ P) := by
  obtain ⟨S, hS, hS0, htS, w, hw, hw0, hEq, η, hηL, hηP, hηγ⟩ := hγ.exists_kPath_trace ht
  set w' : ℝ≥0 → ℝ := fun s => w s with hw'
  have hηL' : IsLoewnerTrace (fun s : ℝ => w' s.toNNReal) η := by
    refine ⟨hηL.1, hηL.2.1, fun u hu => ?_⟩
    rw [← hηL.2.2 u hu]
    exact YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hw.comp (NNReal.continuous_coe.comp continuous_real_toNNReal)) hw hu
      fun r hr => by show w ((r.toNNReal : ℝ≥0) : ℝ) = w r; rw [Real.coe_toNNReal _ hr.1]
  have hgen := hηL'.isGeneratingTrace
  have hIcc := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hgen (hw.comp NNReal.continuous_coe).continuousOn
    (by show w ((0 : ℝ≥0) : ℝ) = 0; rw [NNReal.coe_zero, hw0]) (ENNReal.coe_lt_top (r := t))
  have hT : ((t : ℝ≥0) : ℝ≥0∞) < (((capClock γ S).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe, Real.lt_toNNReal_iff_coe_lt]; exact htS
  refine isGeneratingTraceIcc_congr_trace (ImgDrv.IsGeneratingTraceIcc.congr_of_lt hIcc hT fun r hr => ?_)
    fun r hr => ?_
  · rw [ENNReal.coe_lt_coe, Real.lt_toNNReal_iff_coe_lt] at hr
    rw [← kPath_coe]
    exact (hEq ⟨r.coe_nonneg, hr.le⟩).symm
  · have hrL : (r : WithTop ℝ≥0) < kLife γ P := lt_of_le_of_lt (WithTop.coe_le_coe.2 hr) ht
    have hrS : (r : ℝ) ≤ capClock γ S := (NNReal.coe_le_coe.2 hr).trans htS.le
    obtain ⟨hm, he⟩ := hγ.kInv_spec hrL
    show η r = γ (kInv γ P r)
    rw [← hηγ _ ⟨hγ.nonneg _ hm, hγ.kInv_le hS hrL hrS⟩, he]

theorem IsKilledArc.kTrace_injOn (hγ : IsKilledArc γ P) {a b : ℝ≥0} (ha : (a : WithTop ℝ≥0) < kLife γ P)
    (hb : (b : WithTop ℝ≥0) < kLife γ P) (hab : kTrace γ P a = kTrace γ P b) : a = b := by
  obtain ⟨hma, hea⟩ := hγ.kInv_spec ha
  obtain ⟨hmb, heb⟩ := hγ.kInv_spec hb
  have := hγ.inj hma hmb hab
  apply NNReal.coe_injective
  rw [← hea, ← heb, this]

theorem IsKilledArc.kTrace_mem_H (hγ : IsKilledArc γ P) {t : ℝ≥0} (ht0 : 0 < t)
    (ht : (t : WithTop ℝ≥0) < kLife γ P) : kTrace γ P t ∈ H := by
  obtain ⟨hm, he⟩ := hγ.kInv_spec ht
  refine hγ.mem_H _ hm (lt_of_le_of_ne (hγ.nonneg _ hm) fun h => ?_)
  rw [← h, hγ.capClock_zero] at he
  exact (ne_of_gt ht0) (NNReal.coe_injective he.symm)

/-- **Identification on each prefix**: the capacity of every prefix in `P` lies before the terminal capacity, and on
its capacity range the killed driver is the glued driver. -/
theorem IsKilledArc.kW_eq_chainDrv (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P) :
    (((capClock γ S).toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife γ P ∧
      ∀ r ∈ Icc 0 (capClock γ S), kW γ P r.toNNReal = chainDrv γ P r := by
  refine ⟨hγ.lt_kLife hS, fun r hr => ?_⟩
  have hlt : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife γ P :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr.2)) (hγ.lt_kLife hS)
  rw [kW_of_lt hlt, Real.coe_toNNReal _ hr.1]

end InteractingSLE.WangWu
