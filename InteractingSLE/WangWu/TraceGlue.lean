/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.RS.TipB
import QuantumZipper.Proofs.RS.GenerationCor
import QuantumZipper.Proofs.Loewner.CaraRZ
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# Gluing the traces of the mapped-out futures (Wang–Wu, proof of Lemma 4.12)

Packet PROVE-WW-TRACE. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), proof of
Lemma 4.12 (text dump L1319–L1381): "Fix a positive rational `s` … Girsanov makes its increment law equivalent to
ordinary SLE₄ in the `g_s` image domain. The ordinary trace is simple and belongs to `ℍ` at every strictly positive
increment time. Its pullback by `g_s⁻¹` is therefore continuous at those times, because `g_s⁻¹` is analytic on `ℍ`.
… On overlaps, the traces agree because both are the inverse-Loewner tip limit `lim_{y↓0} g_t⁻¹(W_t + iy)`. For
`0 < u < v`, choose rational `s ∈ (u, v)`. The later trace point `γ(v)` belongs to the active domain `D_s`, whereas
`γ(u)` belongs to `K_s`. Thus the trace has no repeated point. … the deterministic Loewner bounds give
`Re K_t ⊂ [inf W, sup W]`, `sup Im ≤ 2√t`. Continuity of `W` at zero implies `K_t → {0}` … The incremental hull
composition and this shrinking initial hull show that it generates the original Loewner chain. Its simplicity and
absence of later real contacts make each hull exactly the trace initial segment."

This file is the deterministic part of that argument, for a continuous driver `W` with `W 0 = 0` (QuantumZipper's
carriers: `fwdMapInv W t` is the inverse `f_t⁻¹` of the centred map, `trace W t = lim_{y ↓ 0} f_t⁻¹(iy)`, and
`shiftDrive W a = W(a + ·) − W a` drives the mapped-out future `f_a(K_{a+u} \ K_a)`).

* `IsSimpleRadialChainOn V T`: on `[0, T]` the chain driven by `V` has its radial limits, the radial-limit trace is
  continuous, lies in `ℍ` at positive times, and every hull is the trace image `trace V '' (0, u]`
  (`IsSimpleRadialChain V`: for every `T`). Ordinary SLE₄ has this property almost surely (QuantumZipper,
  `RS.ae_radialGood_drive`, `RS.ae_sleTrace_simple_of_le_four`, `RS.ae_fwdHull_eq_sleTrace_image_of_le_four`).
* `IsSimpleRadialChainOn.congr`: the property only depends on the driver on `[0, T]`.
* **`isSimpleRadialChain_of_shift`**: if the mapped-out futures `shiftDrive W a` are simple radial chains for a dense
  set of positive times `a`, then so is the chain of `W`; moreover its trace is injective on `[0, ∞)`. The steps are
  the source's: the tip identity `γ(a + u) = f_a⁻¹(γ_a(u))` (QuantumZipper `RS.trace_add_of_tendsto_shift`), continuity
  of `f_a⁻¹` on `ℍ`, the hull radius bound `K_s ⊆ B̄(0, sup|W| + 3√s)` (QuantumZipper `CaraR.fwdHull_subset_closedBall`)
  for continuity at `0` and for the hull identity, the incremental hull composition (`fwdHull_add_diff`), and
  `γ(u) ∈ K_s`, `γ(v) ∈ ℍ \ K_s` for injectivity.
* `isGeneratingTrace_of_isSimpleRadialChain`: such a chain has the frozen `IsGeneratingTrace` on `[0, ∞]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.TraceGlue

open QuantumZipper QuantumZipper.RS

/-! ### Simple radial chains -/

/-- **A simple radial chain on `[0, T]`**: for every `u ∈ [0, T]` the radial limit `lim_{y ↓ 0} f_u⁻¹(iy)` exists (and
is `trace V u`), the trace is continuous on `[0, T]`, lies in `ℍ` at every time of `(0, T]`, and every hull `K_u`,
`u ∈ [0, T]`, is the trace image `trace V '' (0, u]`. -/
def IsSimpleRadialChainOn (V : ℝ → ℝ) (T : ℝ) : Prop :=
  (∀ u ∈ Icc (0 : ℝ) T,
      Tendsto (fun y : ℝ => fwdMapInv V u (y * I)) (𝓝[>] 0) (𝓝 (trace V u))) ∧
    ContinuousOn (trace V) (Icc 0 T) ∧ (∀ u ∈ Ioc (0 : ℝ) T, trace V u ∈ H) ∧
    ∀ u ∈ Icc (0 : ℝ) T, fwdHull V u = trace V '' Ioc 0 u

/-- **A simple radial chain**: a simple radial chain on every interval `[0, T]`. -/
def IsSimpleRadialChain (V : ℝ → ℝ) : Prop := ∀ T : ℝ, IsSimpleRadialChainOn V T

theorem IsSimpleRadialChainOn.mono {V : ℝ → ℝ} {T T' : ℝ} (h : IsSimpleRadialChainOn V T)
    (hT : T' ≤ T) : IsSimpleRadialChainOn V T' :=
  ⟨fun u hu => h.1 u ⟨hu.1, hu.2.trans hT⟩, h.2.1.mono (Icc_subset_Icc_right hT),
    fun u hu => h.2.2.1 u ⟨hu.1, hu.2.trans hT⟩, fun u hu => h.2.2.2 u ⟨hu.1, hu.2.trans hT⟩⟩

/-- The hull at time `u` is the complement in `ℍ` of the image of `ℍ` under `f_u⁻¹`. -/
theorem fwdHull_eq_H_diff_image {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) {u : ℝ}
    (hu : 0 ≤ u) : fwdHull V u = H \ fwdMapInv V u '' H := by
  rw [image_fwdMapInv_H hV hV0 hu, sdiff_sdiff_cancel_left (fwdHull_mono.2 u)]

/-- **Locality.** Being a simple radial chain on `[0, T]` only depends on the driver on `[0, T]`. -/
theorem IsSimpleRadialChainOn.congr {V V' : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0)
    (hV' : Continuous V') (hV'0 : V' 0 = 0) {T : ℝ} (hVV' : EqOn V V' (Icc 0 T))
    (h : IsSimpleRadialChainOn V T) : IsSimpleRadialChainOn V' T := by
  have hinv : ∀ u ∈ Icc (0 : ℝ) T, ∀ z ∈ H, fwdMapInv V u z = fwdMapInv V' u z := fun u hu z hz =>
    LP.fwdMapInv_eq_of_eqOn_Icc hV hV' hV0 hV'0 hu.1 (hVV'.mono (Icc_subset_Icc_right hu.2)) hz
  have htr : ∀ u ∈ Icc (0 : ℝ) T, trace V u = trace V' u := fun u hu =>
    trace_congr_drive hV hV0 hV' hV'0 hu.1 (hVV'.mono (Icc_subset_Icc_right hu.2))
  have hhull : ∀ u ∈ Icc (0 : ℝ) T, fwdHull V u = fwdHull V' u := fun u hu => by
    rw [fwdHull_eq_H_diff_image hV hV0 hu.1, fwdHull_eq_H_diff_image hV' hV'0 hu.1,
      image_congr fun z hz => hinv u hu z hz]
  have himg : ∀ u ∈ Icc (0 : ℝ) T, trace V '' Ioc 0 u = trace V' '' Ioc 0 u := fun u hu =>
    image_congr fun r hr => htr r ⟨hr.1.le, hr.2.trans hu.2⟩
  refine ⟨fun u hu => ?_, h.2.1.congr fun u hu => (htr u hu).symm, fun u hu => ?_, fun u hu => ?_⟩
  · rw [← htr u hu]
    refine (h.1 u hu).congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
    exact hinv u hu _ (mul_I_mem_H hy)
  · rw [← htr u ⟨hu.1.le, hu.2⟩]
    exact h.2.2.1 u hu
  · rw [← hhull u hu, ← himg u hu]
    exact h.2.2.2 u hu

/-! ### Deterministic Loewner facts used in the gluing -/

variable {W : ℝ → ℝ}

/-- **The initial hulls shrink to the base point**: for every `ε > 0` there is `δ > 0` with `‖z‖ < ε` for every
`z ∈ K_s`, `0 < s < δ` (hull radius bound `K_s ⊆ B̄(0, sup_{[0,s]} |W| + 3√s)` and continuity of `W` at `0`). -/
theorem exists_forall_norm_lt_of_mem_fwdHull (hW : Continuous W) (hW0 : W 0 = 0) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ s, 0 < s → s < δ → ∀ z ∈ fwdHull W s, ‖z‖ < ε := by
  obtain ⟨δ₁, hδ₁, hW1⟩ := Metric.continuous_iff.1 hW 0 (ε / 2) (by positivity)
  refine ⟨min δ₁ ((ε / 6) ^ 2), lt_min hδ₁ (by positivity), fun s hs hsδ z hz => ?_⟩
  have hM : ∀ r ∈ Icc (0 : ℝ) s, |W r| ≤ ε / 2 := fun r hr => by
    have h := hW1 r (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
      exact lt_of_le_of_lt hr.2 (lt_of_lt_of_le hsδ (min_le_left _ _)))
    rw [Real.dist_eq, hW0, sub_zero] at h
    exact h.le
  have hball := CaraR.fwdHull_subset_closedBall hW hs hM hz
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  have hsq : Real.sqrt s < ε / 6 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact lt_of_lt_of_le hsδ (min_le_right _ _)
  linarith

/-- **The tip identity after a time `a`** (`γ(t) = f_a⁻¹(γ_a(t − a))`, QuantumZipper P3(b)): if the mapped-out
future after `a` is a simple radial chain on `[0, t − a]`, `a < t`, then the radial limit of the chain of `W` at `t`
exists, `trace W t = f_a⁻¹(trace (shiftDrive W a) (t − a))`, and `trace W t ∈ ℍ \ K_a`. -/
theorem tendsto_trace_of_shift (hW : Continuous W) (hW0 : W 0 = 0) {a t : ℝ} (ha : 0 ≤ a)
    (hat : a < t) (hsh : IsSimpleRadialChainOn (shiftDrive W a) (t - a)) :
    Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (trace W t)) ∧
      trace W t = fwdMapInv W a (trace (shiftDrive W a) (t - a)) ∧ trace W t ∈ H \ fwdHull W a := by
  have hu : 0 < t - a := sub_pos.2 hat
  have hpH := hsh.2.2.1 (t - a) ⟨hu, le_rfl⟩
  have key := trace_add_of_tendsto_shift hW hW0 ha hu.le hpH (hsh.1 (t - a) ⟨hu.le, le_rfl⟩)
  rw [show a + (t - a) = t by ring] at key
  obtain ⟨h1, -, h3⟩ := key
  refine ⟨?_, h3, ?_⟩
  · rw [h3]; exact h1
  · rw [h3]; exact fwdMapInv_mem_compl_fwdHull hW hW0 ha hpH

/-- At time `0` the radial limit is `W 0 = 0` (`f_0⁻¹(w) = w + W 0`). -/
theorem tendsto_trace_zero (hW : Continuous W) (hW0 : W 0 = 0) :
    Tendsto (fun y : ℝ => fwdMapInv W 0 (y * I)) (𝓝[>] 0) (𝓝 (trace W 0)) := by
  rw [Thm18Asm.G1Pkg.trace_zero_time hW, hW0]
  have hc : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
      (continuous_ofReal.mul continuous_const).tendsto 0
    simpa using h1.mono_left nhdsWithin_le_nhds
  refine hc.congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
  show (y : ℂ) * I = fwdMapInv W 0 ((y : ℂ) * I)
  rw [Thm18Asm.G1Pkg.fwdMapInv_zero_time hW (show 0 < ((y : ℂ) * I).im by simpa using hy), hW0]
  simp

theorem trace_zero_eq (hW : Continuous W) (hW0 : W 0 = 0) : trace W 0 = 0 := by
  rw [Thm18Asm.G1Pkg.trace_zero_time hW, hW0]; simp

theorem zero_notMem_H : (0 : ℂ) ∉ H := fun h => by
  have h' : (0 : ℝ) < (0 : ℂ).im := h
  simp at h'

/-! ### The gluing theorem -/

section Glue

variable {D : Set ℝ}

/-- The hypothesis of the gluing theorem: the mapped-out future after every time `a ∈ D`, `a > 0`, is a simple
radial chain. -/
def ShiftGood (W : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ a ∈ D, 0 < a → IsSimpleRadialChain (shiftDrive W a)

theorem ShiftGood.exists_mem_Ioo (hD : Dense D) {b c : ℝ} (hbc : b < c) : ∃ a ∈ D, b < a ∧ a < c := by
  obtain ⟨a, haD, hab, hac⟩ := hD.exists_between hbc
  exact ⟨a, haD, hab, hac⟩

/-- Radial limits, the tip identity and `trace W t ∈ ℍ \ K_a` at every positive time. -/
theorem ShiftGood.tendsto_of_pos (hW : Continuous W) (hW0 : W 0 = 0) (hD : Dense D)
    (hg : ShiftGood W D) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (trace W t)) ∧ trace W t ∈ H := by
  obtain ⟨a, haD, ha0, hat⟩ := ShiftGood.exists_mem_Ioo hD ht
  obtain ⟨h1, -, h3⟩ := tendsto_trace_of_shift hW hW0 ha0.le hat (hg a haD ha0 (t - a))
  exact ⟨h1, h3.1⟩

theorem ShiftGood.tendsto (hW : Continuous W) (hW0 : W 0 = 0) (hD : Dense D) (hg : ShiftGood W D)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (trace W t)) := by
  rcases ht.lt_or_eq with ht | rfl
  · exact (hg.tendsto_of_pos hW hW0 hD ht).1
  · exact tendsto_trace_zero hW hW0

/-- Every positive-time trace point lies in the hull at that time. -/
theorem ShiftGood.trace_mem_fwdHull (hW : Continuous W) (hW0 : W 0 = 0) (hD : Dense D)
    (hg : ShiftGood W D) {t : ℝ} (ht : 0 < t) : trace W t ∈ fwdHull W t := by
  obtain ⟨h1, hH⟩ := hg.tendsto_of_pos hW hW0 hD ht
  rcases trace_mem_fwdHull_or_real hW hW0 ht.le h1 with h | h
  · exact h
  · exact absurd h (ne_of_gt hH)

/-- Continuity of the trace at every positive time: near `t`, `trace W = f_a⁻¹ ∘ trace (shiftDrive W a) ∘ (· − a)`
for some `a ∈ D ∩ (0, t)`. -/
theorem ShiftGood.continuousAt_of_pos (hW : Continuous W) (hW0 : W 0 = 0) (hD : Dense D)
    (hg : ShiftGood W D) {t : ℝ} (ht : 0 < t) : ContinuousAt (trace W) t := by
  obtain ⟨a, haD, ha0, hat⟩ := ShiftGood.exists_mem_Ioo hD ht
  have hsh := hg a haD ha0 (t - a + 1)
  have heq : trace W =ᶠ[𝓝 t] fun s => fwdMapInv W a (trace (shiftDrive W a) (s - a)) := by
    filter_upwards [Ioo_mem_nhds hat (lt_add_one t)] with s hs
    exact (tendsto_trace_of_shift hW hW0 ha0.le hs.1
      (hsh.mono (by linarith [hs.2]))).2.1
  refine ContinuousAt.congr ?_ heq.symm
  have hpH := hsh.2.2.1 (t - a) ⟨sub_pos.2 hat, by linarith⟩
  have hcs : ContinuousAt (trace (shiftDrive W a)) (t - a) :=
    hsh.2.1.continuousAt (Icc_mem_nhds (sub_pos.2 hat) (lt_add_one _))
  have h1 : ContinuousAt (fun s : ℝ => s - a) t := continuousAt_id.sub continuousAt_const
  have h2 : ContinuousAt (trace (shiftDrive W a) ∘ fun s : ℝ => s - a) t :=
    ContinuousAt.comp_of_eq (g := trace (shiftDrive W a)) (f := fun s : ℝ => s - a) hcs h1 rfl
  exact ContinuousAt.comp_of_eq (g := fwdMapInv W a)
    (f := trace (shiftDrive W a) ∘ fun s : ℝ => s - a) (continuousAt_fwdMapInv hW hW0 ha0.le hpH) h2 rfl

/-- Continuity of the trace at `0` (the initial hulls shrink to `0`). -/
theorem ShiftGood.continuousWithinAt_zero (hW : Continuous W) (hW0 : W 0 = 0) (hD : Dense D)
    (hg : ShiftGood W D) : ContinuousWithinAt (trace W) (Ici 0) 0 := by
  rw [ContinuousWithinAt, trace_zero_eq hW hW0, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := exists_forall_norm_lt_of_mem_fwdHull hW hW0 hε
  refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
  rw [Real.dist_eq, sub_zero] at hxδ
  rw [dist_zero_right]
  rcases (show (0 : ℝ) ≤ x from hx).lt_or_eq with hx0 | rfl
  · rw [abs_of_pos hx0] at hxδ
    exact hsmall x hx0 hxδ _ (hg.trace_mem_fwdHull hW hW0 hD hx0)
  · rw [trace_zero_eq hW hW0, norm_zero]; exact hε

theorem ShiftGood.continuousOn (hW : Continuous W) (hW0 : W 0 = 0) (hD : Dense D)
    (hg : ShiftGood W D) : ContinuousOn (trace W) (Ici 0) := by
  intro t ht
  rcases (show (0 : ℝ) ≤ t from ht).lt_or_eq with ht0 | rfl
  · exact (hg.continuousAt_of_pos hW hW0 hD ht0).continuousWithinAt
  · exact hg.continuousWithinAt_zero hW hW0 hD

/-- **The hull is the trace initial segment**: `K_t = trace W '' (0, t]`. A point `z ∈ K_t` lies outside some small
initial hull `K_a`, `a ∈ D`; by the incremental hull composition `f_a(z) ∈ K^{(a)}_{t−a} = γ_a((0, t − a])`, so
`z = f_a⁻¹(γ_a(u)) = γ(a + u)`. -/
theorem ShiftGood.fwdHull_eq (hW : Continuous W) (hW0 : W 0 = 0) (hD : Dense D)
    (hg : ShiftGood W D) {t : ℝ} (ht : 0 ≤ t) : fwdHull W t = trace W '' Ioc 0 t := by
  refine subset_antisymm (fun z hz => ?_) ?_
  · have hzH : z ∈ H := fwdHull_mono.2 t hz
    have ht0 : 0 < t := by
      rcases ht.lt_or_eq with h | rfl
      · exact h
      · rw [fwdHull_zero_eq_empty hW] at hz; exact absurd hz (notMem_empty z)
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 fun h => zero_notMem_H (h ▸ hzH)
    obtain ⟨δ, hδ, hsmall⟩ := exists_forall_norm_lt_of_mem_fwdHull hW hW0 hz0
    obtain ⟨a, haD, ha0, hat⟩ := ShiftGood.exists_mem_Ioo hD (lt_min ht0 hδ)
    have hzKa : z ∉ fwdHull W a := fun h =>
      lt_irrefl _ (hsmall a ha0 (lt_of_lt_of_le hat (min_le_right _ _)) z h)
    have hat' : a < t := lt_of_lt_of_le hat (min_le_left _ _)
    have hdiff : z ∈ fwdHull W (a + (t - a)) \ fwdHull W a := by
      rw [show a + (t - a) = t by ring]; exact ⟨hz, hzKa⟩
    rw [fwdHull_add_diff hW ha0.le (sub_nonneg.2 hat'.le)] at hdiff
    obtain ⟨hzc, hfz⟩ := hdiff
    have hsh := hg a haD ha0 (t - a)
    rw [show (fun r => W (a + r) - W a) = shiftDrive W a from rfl,
      hsh.2.2.2 (t - a) ⟨sub_nonneg.2 hat'.le, le_rfl⟩] at hfz
    obtain ⟨u, hu, hu_eq⟩ := hfz
    have hau : a < a + u := by linarith [hu.1]
    have key := (tendsto_trace_of_shift hW hW0 ha0.le hau
      (hsh.mono (by linarith [hu.2]))).2.1
    rw [show a + u - a = u by ring, hu_eq, fwdMapInv_fwdMap hW hW0 ha0.le hzc] at key
    exact ⟨a + u, ⟨by linarith, by linarith [hu.2]⟩, key⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact fwdHull_mono.1 hr.2 (hg.trace_mem_fwdHull hW hW0 hD hr.1)

/-- **Simplicity**: the trace is injective on `[0, ∞)` (for `0 < u < v` and `a ∈ D ∩ (u, v)`: `γ(u) ∈ K_a`,
`γ(v) ∈ ℍ \ K_a`; and `γ(0) = 0 ∉ ℍ`). -/
theorem ShiftGood.injOn (hW : Continuous W) (hW0 : W 0 = 0) (hD : Dense D) (hg : ShiftGood W D) :
    InjOn (trace W) (Ici 0) := by
  have hlt : ∀ {u v : ℝ}, 0 ≤ u → u < v → trace W u ≠ trace W v := by
    intro u v hu huv heq
    rcases hu.lt_or_eq with hu0 | rfl
    · obtain ⟨a, haD, hua, hav⟩ := ShiftGood.exists_mem_Ioo hD huv
      have ha0 : 0 < a := hu0.trans hua
      have hK : trace W u ∈ fwdHull W a :=
        fwdHull_mono.1 hua.le (hg.trace_mem_fwdHull hW hW0 hD hu0)
      have hc := (tendsto_trace_of_shift hW hW0 ha0.le hav (hg a haD ha0 (v - a))).2.2
      exact hc.2 (heq ▸ hK)
    · rw [trace_zero_eq hW hW0] at heq
      exact zero_notMem_H (heq ▸ (hg.tendsto_of_pos hW hW0 hD huv).2)
  intro u hu v hv huv
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hlt hu h huv
  · exact hlt hv h huv.symm

/-- **The gluing theorem** (proof of Lemma 4.12, deterministic part): if the mapped-out futures after a dense set
of positive times are simple radial chains, then so is the chain of `W`, and its trace is injective on `[0, ∞)`. -/
theorem isSimpleRadialChain_of_shift (hW : Continuous W) (hW0 : W 0 = 0) (hD : Dense D)
    (hg : ShiftGood W D) : IsSimpleRadialChain W ∧ InjOn (trace W) (Ici 0) := by
  refine ⟨fun T => ⟨fun u hu => hg.tendsto hW hW0 hD hu.1,
    (hg.continuousOn hW hW0 hD).mono fun u hu => hu.1,
    fun u hu => (hg.tendsto_of_pos hW hW0 hD hu.1).2, fun u hu => hg.fwdHull_eq hW hW0 hD hu.1⟩,
    hg.injOn hW hW0 hD⟩

end Glue

/-! ### The frozen generating trace -/

/-- A hull at a fixed time is bounded. -/
theorem isBounded_fwdHull (hW : Continuous W) {t : ℝ} : Bornology.IsBounded (fwdHull W t) := by
  rcases le_or_gt t 0 with ht | ht
  · have hsub : fwdHull W t ⊆ fwdHull W 0 := fwdHull_mono.1 ht
    rw [fwdHull_zero_eq_empty hW] at hsub
    exact Bornology.isBounded_empty.subset hsub
  · obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
      hW.continuousOn
    exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := C + 3 * Real.sqrt t)).subset
      (CaraR.fwdHull_subset_closedBall hW ht fun r hr => by simpa using hC r hr)

theorem norm_ofReal_mul_I (r : ℝ) : ‖(r : ℂ) * I‖ = |r| := by simp

theorem ofReal_mul_I_mem_H {r : ℝ} (hr : 0 < r) : (r : ℂ) * I ∈ H := mul_I_mem_H hr

/-- If `ℍ \ A = ℍ \ K_t`, then `K_t` is the frozen filling of `A` (`ℍ \ K_t` is preconnected and unbounded). -/
theorem isFilling_of_diff_eq (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {A : Set ℂ}
    (hA : H \ A = H \ fwdHull W t) : IsFilling (fwdHull W t) A := by
  have hKb := isBounded_fwdHull (W := W) (t := t) hW
  obtain ⟨R, hR⟩ := hKb.subset_closedBall 0
  have hpos : 0 < max R 0 + 1 := by positivity
  have hzH := ofReal_mul_I_mem_H hpos
  have hzK : ((max R 0 + 1 : ℝ) : ℂ) * I ∉ fwdHull W t := fun h => by
    have h1 := hR h
    rw [mem_closedBall, dist_zero_right, norm_ofReal_mul_I, abs_of_pos hpos] at h1
    linarith [le_max_left R 0]
  refine ⟨⟨_, ⟨hzH, hzK⟩, ?_⟩, fun hb => ?_⟩
  · rw [hA]
    exact (isPreconnected_compl_fwdHull hW hW0 ht).connectedComponentIn ⟨hzH, hzK⟩
  · obtain ⟨R', hR'⟩ := (hb.union hKb).subset_closedBall 0
    have hpos' : 0 < max R' 0 + 1 := by positivity
    have hy := ofReal_mul_I_mem_H hpos'
    have hmem : ((max R' 0 + 1 : ℝ) : ℂ) * I ∈ (H \ fwdHull W t) ∪ fwdHull W t := by
      by_cases h : ((max R' 0 + 1 : ℝ) : ℂ) * I ∈ fwdHull W t
      · exact Or.inr h
      · exact Or.inl ⟨hy, h⟩
    have h1 := hR' hmem
    rw [mem_closedBall, dist_zero_right, norm_ofReal_mul_I, abs_of_pos hpos'] at h1
    linarith [le_max_left R' 0]

/-- The trace read on `ℝ≥0`. -/
abbrev nnTrace (w : ℝ≥0 → ℝ) : ℝ≥0 → ℂ := fun t => trace (fun s : ℝ => w s.toNNReal) t

/-- **A simple radial chain gives the frozen generating trace**, and its hulls are the trace images of `(0, t]`. -/
theorem isGeneratingTrace_of_isSimpleRadialChain {w : ℝ≥0 → ℝ}
    (hw : Continuous fun s : ℝ => w s.toNNReal) (hw0 : w 0 = 0)
    (h : IsSimpleRadialChain fun s : ℝ => w s.toNNReal) :
    IsGeneratingTrace w ⊤ (nnTrace w) ∧
      ∀ t : ℝ≥0, fwdHull (fun s : ℝ => w s.toNNReal) t = nnTrace w '' Ioc 0 t := by
  set W : ℝ → ℝ := fun s : ℝ => w s.toNNReal with hWdef
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  have hc : ContinuousOn (trace W) (Ici 0) := fun t ht => by
    have h1 := (h (t + 1)).2.1 t ⟨ht, by linarith⟩
    refine h1.mono_of_mem_nhdsWithin (mem_of_superset (inter_mem_nhdsWithin (Ici (0 : ℝ))
      (Iio_mem_nhds (lt_add_one t))) fun x hx => ⟨hx.1, hx.2.le⟩)
  have h0 : trace W 0 = 0 := trace_zero_eq hw hW0
  have hhull : ∀ t : ℝ≥0, fwdHull W t = nnTrace w '' Ioc 0 t := fun t => by
    rw [(h t).2.2.2 t ⟨t.coe_nonneg, le_rfl⟩]
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨r.toNNReal, ⟨Real.toNNReal_pos.2 hr.1, Real.toNNReal_le_iff_le_coe.2 hr.2⟩, ?_⟩
      show trace W (r.toNNReal : ℝ) = trace W r
      rw [Real.coe_toNNReal _ hr.1.le]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, ⟨NNReal.coe_pos.2 hs.1, NNReal.coe_le_coe.2 hs.2⟩, rfl⟩
  refine ⟨⟨?_, ?_, fun t _ => ?_⟩, hhull⟩
  · show trace W ((0 : ℝ≥0) : ℝ) = 0
    rw [NNReal.coe_zero, h0]
  · exact (hc.comp_continuous NNReal.continuous_coe fun t => t.coe_nonneg).continuousOn
  · refine isFilling_of_diff_eq hw hW0 t.coe_nonneg ?_
    rw [hhull t]
    ext z
    simp only [Set.mem_sdiff, and_congr_right_iff]
    intro hzH
    constructor
    · intro hA hK
      exact hA (image_mono Ioc_subset_Icc_self hK)
    · rintro hK ⟨s, hs, rfl⟩
      rcases (zero_le : (0 : ℝ≥0) ≤ s).lt_or_eq with hs0 | hs0
      · exact hK ⟨s, ⟨hs0, hs.2⟩, rfl⟩
      · subst hs0
        refine zero_notMem_H ?_
        have : nnTrace w 0 = 0 := by
          show trace W ((0 : ℝ≥0) : ℝ) = 0
          rw [NNReal.coe_zero, h0]
        rw [← this]; exact hzH

/-- **The gluing theorem in the frozen form**: a continuous driver whose mapped-out futures after a dense set of
positive times are simple radial chains has a simple generating trace on `[0, ∞]`, lying in `ℍ` at positive times,
whose hulls are the trace initial segments `η((0, t])`. -/
theorem exists_isGeneratingTrace_of_shift {w : ℝ≥0 → ℝ}
    (hw : Continuous fun s : ℝ => w s.toNNReal) (hw0 : w 0 = 0) {D : Set ℝ} (hD : Dense D)
    (hg : ShiftGood (fun s : ℝ => w s.toNNReal) D) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η ∧ Function.Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
      ∀ t : ℝ≥0, fwdHull (fun s : ℝ => w s.toNNReal) t = η '' Ioc 0 t := by
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  obtain ⟨hs, hinj⟩ := isSimpleRadialChain_of_shift hw hW0 hD hg
  obtain ⟨hgen, hhull⟩ := isGeneratingTrace_of_isSimpleRadialChain hw hw0 hs
  refine ⟨nnTrace w, hgen, fun s t hst => ?_, fun t ht => ?_, hhull⟩
  · exact NNReal.coe_injective (hinj s.coe_nonneg t.coe_nonneg hst)
  · exact (hs t).2.2.1 t ⟨NNReal.coe_pos.2 ht, le_rfl⟩

end InteractingSLE.WangWu.TraceGlue
