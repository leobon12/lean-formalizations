/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux36Face
import InteractingSLE.Spec.Sec6.Aux36Lift

/-!
# The lifted incoming arms of a fixed chart (Aux. lemma 36, chart-face geometry)

Specification §6.2, **Aux.** lemma 36 (`source/spec/p193-240.md` L36–L78, p. 195): "Map `D_T` to the
half-plane using its original target at infinity. The first-exit prime-end lemma continuously lifts
the two incoming subarcs to simple arcs, ending at real points `q₁, q₂`. Their open interiors are
disjoint." Ruling R41's note (§1.1): "its current incoming subarcs lift simply in the `g_r` chart,
from `z_r = g_r(x_C)` to `q₁, q₂ ∈ ℝ`."

For a continuous Loewner trace with continuous driver, `D_r = ℍ \ K_r`, `g_r = fwdMap W r`
(centred) and `f̄_r = trMap W 0 r`. A physical incoming subarc `α` on `[c, u]` which runs in `D_r`
on `[c, u)` and whose endpoint `α(u)` is not in `D_r` lifts to an arm `a : [0, 1] → ℍ̄` from the
gate `q` (`a 0 = q`, `f̄_r(q) = α(u)`) to `g_r(α(c))`, simple, open in `ℍ`, with
`a((0, 1]) = g_r(α([c, u)))`.

## Main results

* `trMap_zero_fwdMap`, `fwdMap_trMap_zero`, `trMap_zero_mem_domain`,
  `exists_norm_trMap_zero_sub_le`: the chart `f̄_r : ℍ → D_r` and its inverse `g_r`;
* `exists_arm`: **the lifted arm**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- `f̄_r ∘ g_r = id` on `D_r`. -/
theorem trMap_zero_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) {p : ℂ}
    (hp : p ∈ H \ fwdHull W r) : trMap W 0 r (fwdMap W r p) = p := by
  rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hr (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr hp),
    YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero,
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr hp]

/-- `g_r ∘ f̄_r = id` on `ℍ`. -/
theorem fwdMap_trMap_zero (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) {w : ℂ}
    (hw : w ∈ H) : fwdMap W r (trMap W 0 r w) = w := by
  rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hr hw, YuanSimpleApprox.shiftDrive_zero_eq hW0,
    sub_zero, QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hr hw]

/-- `f̄_r(ℍ) ⊆ D_r`. -/
theorem trMap_zero_mem_domain (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) {w : ℂ}
    (hw : w ∈ H) : trMap W 0 r w ∈ H \ fwdHull W r := by
  rw [← trMap_zero_image_H hW hW0 hr]; exact ⟨w, hw, rfl⟩

/-- `f̄_r` moves points of `ℍ` by a bounded amount. -/
theorem exists_norm_trMap_zero_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) :
    ∃ K, ∀ w ∈ H, ‖trMap W 0 r w - w‖ ≤ K := by
  obtain ⟨K, hK⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hr
  refine ⟨K, fun w hw => ?_⟩
  rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hr hw, YuanSimpleApprox.shiftDrive_zero_eq hW0,
    sub_zero]
  exact hK w hw

/-- **The lifted arm** (Aux. lemma 36: "The first-exit prime-end lemma continuously lifts the two
incoming subarcs to simple arcs, ending at real points"). Let `α` be continuous and injective on
`[c, u]` (`c < u`), with `α([c, u)) ⊆ D_r` and `α(u) ∉ D_r`. Then there are a real gate `q` with
`f̄_r(q) = α(u)` and a simple arm `a : [0, 1] → ℍ̄` from `q` to `g_r(α(c))`, open in `ℍ`, with
`a((0, 1]) = g_r(α([c, u)))`. -/
theorem exists_arm (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {r c u : ℝ}
    (hr : 0 ≤ r) (hcu : c < u) {α : ℝ → ℂ} (hα : ContinuousOn α (Icc c u))
    (hαi : InjOn α (Icc c u)) (hαD : ∀ v ∈ Ico c u, α v ∈ H \ fwdHull W r)
    (hαu : α u ∉ H \ fwdHull W r) :
    ∃ (q : ℝ) (a : ℝ → ℂ), ContinuousOn a (Icc 0 1) ∧ InjOn a (Icc 0 1) ∧ a 0 = q ∧
      a 1 = fwdMap W r (α c) ∧ (∀ t ∈ Ioc (0 : ℝ) 1, a t ∈ H) ∧ trMap W 0 r q = α u ∧
      a '' Ioc 0 1 = fwdMap W r '' (α '' Ico c u) := by
  obtain ⟨q, hqu, hlim⟩ := exists_tendsto_lift hη hW hW0 hr hcu hα hαD hαu
  set φ : ℝ → ℝ := fun t => u - t * (u - c) with hφ
  have hφc : Continuous φ := continuous_const.sub (continuous_id.mul continuous_const)
  have hφmem : ∀ t ∈ Ioc (0 : ℝ) 1, φ t ∈ Ico c u := by
    intro t ht
    have h1 : 0 < u - c := by linarith
    refine ⟨?_, ?_⟩
    · have : t * (u - c) ≤ 1 * (u - c) := mul_le_mul_of_nonneg_right ht.2 h1.le
      simp only [hφ]; linarith
    · have : 0 < t * (u - c) := mul_pos ht.1 h1
      simp only [hφ]; linarith
  set a : ℝ → ℂ := fun t => if t = 0 then (q : ℂ) else fwdMap W r (α (φ t)) with ha
  have ha0 : a 0 = q := by simp [ha]
  have hapos : ∀ t ∈ Ioc (0 : ℝ) 1, a t = fwdMap W r (α (φ t)) := fun t ht => by
    simp [ha, ht.1.ne']
  -- the composite on `(0, 1]`
  set g : ℝ → ℂ := fun t => fwdMap W r (α (φ t)) with hg
  have hgc : ContinuousOn g (Ioc 0 1) := by
    have h1 : ContinuousOn (fun t => α (φ t)) (Ioc 0 1) :=
      hα.comp hφc.continuousOn fun t ht => Ico_subset_Icc_self (hφmem t ht)
    exact (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hr).continuousOn.comp h1
      fun t ht => hαD _ (hφmem t ht)
  have hgH : ∀ t ∈ Ioc (0 : ℝ) 1, g t ∈ H := fun t ht =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr (hαD _ (hφmem t ht))
  refine ⟨q, a, ?_, ?_, ha0, ?_, ?_, hqu, ?_⟩
  · -- continuity
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0
      have hIcc : Icc (0 : ℝ) 1 = insert 0 (Ioc 0 1) := (Ioc_insert_left zero_le_one).symm
      show ContinuousWithinAt a (Icc 0 1) 0
      rw [hIcc]
      refine continuousWithinAt_insert_self.2 ?_
      show Tendsto a (𝓝[Ioc 0 1] 0) (𝓝 (a 0))
      rw [ha0]
      have hφt : Tendsto φ (𝓝[Ioc 0 1] 0) (𝓝[<] u) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := hφc.tendsto 0
          simp only [hφ, zero_mul, sub_zero] at this ⊢
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht using (hφmem t ht).2
      refine (hlim.comp hφt).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht using (hapos t ht).symm
    · have hmem : Ioc (0 : ℝ) 1 ∈ 𝓝[Icc 0 1] t :=
        mem_nhdsWithin.2 ⟨Ioi 0, isOpen_Ioi, h0, fun s hs => ⟨hs.1, hs.2.2⟩⟩
      have h1 : ContinuousWithinAt g (Icc 0 1) t :=
        (hgc t ⟨h0, ht.2⟩).mono_of_mem_nhdsWithin hmem
      refine h1.congr_of_eventuallyEq ?_ (hapos t ⟨h0, ht.2⟩)
      filter_upwards [hmem] with s hs using hapos s hs
  · -- injectivity
    have hreal : ∀ t ∈ Ioc (0 : ℝ) 1, a t ≠ q := by
      intro t ht h
      have h1 : (0 : ℝ) < (a t).im := by rw [hapos t ht]; exact hgH t ht
      rw [h] at h1; simp at h1
    intro t ht t' ht' h
    rcases eq_or_lt_of_le ht.1 with h0 | h0 <;> rcases eq_or_lt_of_le ht'.1 with h0' | h0'
    · rw [← h0, ← h0']
    · subst h0; exact absurd (h.symm.trans ha0) (hreal t' ⟨h0', ht'.2⟩)
    · subst h0'; exact absurd (h.trans ha0) (hreal t ⟨h0, ht.2⟩)
    · rw [hapos t ⟨h0, ht.2⟩, hapos t' ⟨h0', ht'.2⟩] at h
      have h1 := QuantumZipper.FwdHolo.injOn_fwdMap hW hr (hαD _ (hφmem t ⟨h0, ht.2⟩))
        (hαD _ (hφmem t' ⟨h0', ht'.2⟩)) h
      have h2 := hαi (Ico_subset_Icc_self (hφmem t ⟨h0, ht.2⟩))
        (Ico_subset_Icc_self (hφmem t' ⟨h0', ht'.2⟩)) h1
      simp only [hφ] at h2
      have h3 : (t - t') * (u - c) = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h4 | h4
      · linarith
      · linarith
  · rw [hapos 1 ⟨one_pos, le_rfl⟩]; simp [hφ]
  · intro t ht; rw [hapos t ht]; exact hgH t ht
  · -- the image
    ext w
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [hapos t ht]
      exact ⟨α (φ t), ⟨φ t, hφmem t ht, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      have h1 : 0 < u - c := by linarith
      set t := (u - v) / (u - c) with ht
      have htmem : t ∈ Ioc (0 : ℝ) 1 := by
        refine ⟨div_pos (by linarith [hv.2]) h1, (div_le_one h1).2 (by linarith [hv.1])⟩
      have hφv : φ t = v := by
        simp only [hφ, ht]; field_simp; ring
      exact ⟨t, htmem, by rw [hapos t htmem, hφv]⟩

end InteractingSLE.Sec6
