/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux39Inf
import InteractingSLE.Spec.Sec6.Aux36FaceArm

/-!
# Proper incoming arms and their compactification (junction at infinity)

When the pocket junction is the original target, the unvisited incoming prefixes at the chart time
`r` are proper simple paths `α : [u, ∞) → ℂ` with `α((u, ∞)) ⊆ D_r` and the attachment `α(u)` not
in `D_r`. Their lifts `g_r ∘ α` are proper arcs from a real gate `q` (`f̄_r(q) = α(u)`) to `∞`
(ruling R41's note, Lemma 1.3: "If the target junction is infinity, the two proper incoming arms
...").

The real Möbius map `ψ_p(w) = −(w − p)⁻¹` (`p` real) preserves `ℍ` and `ℝ`, is injective, and
sends `∞` to `0`. Composing the lift with `ψ_p` and compactifying the parameter gives an arc
`b : [0, 1] → ℂ` from the real point `ψ_p(q)` to `0`, open in `ℍ` — the data of
`IsArcPairInf` (`Aux39Inf.lean`).

## Main results

* `psiMap`, `psiMapInv` and their API (`psiMap_mem_H_iff`, `psiMap_injective`,
  `continuousOn_psiMap`, `psiMapInv_psiMap`, `tendsto_psiMap_zero`, `psiMap_ofReal_lt`);
* `exists_tendsto_lift_right`: the first-exit lifting lemma approached from the right;
* `exists_psiArm`: **the compactified arm**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

/-! ### The real Möbius map `ψ_p` -/

/-- The real Möbius map `ψ_p(w) = −(w − p)⁻¹`: it sends `p` to `∞` and `∞` to `0`. -/
def psiMap (p : ℝ) (w : ℂ) : ℂ := -(w - p)⁻¹

/-- Its inverse `ζ ↦ p − ζ⁻¹`. -/
def psiMapInv (p : ℝ) (ζ : ℂ) : ℂ := p - ζ⁻¹

variable {p : ℝ}

theorem psiMap_im (w : ℂ) : (psiMap p w).im = w.im / normSq (w - p) := by
  simp [psiMap, inv_im, neg_div]

theorem psiMap_mem_H_iff {w : ℂ} (hw : w ≠ p) : psiMap p w ∈ H ↔ w ∈ H := by
  have hpos : 0 < normSq (w - p) := normSq_pos.2 (sub_ne_zero.2 hw)
  show 0 < (psiMap p w).im ↔ 0 < w.im
  rw [psiMap_im]
  exact div_pos_iff_of_pos_right hpos

theorem psiMap_mem_Hbar {w : ℂ} (hw : w ∈ Hbar) : psiMap p w ∈ Hbar := by
  show 0 ≤ (psiMap p w).im
  rw [psiMap_im]
  exact div_nonneg hw (normSq_nonneg _)

theorem psiMap_ofReal (x : ℝ) : psiMap p x = ((-(x - p)⁻¹ : ℝ) : ℂ) := by
  simp [psiMap]

theorem psiMap_injective : Function.Injective (psiMap p) := by
  intro w w' h
  simp only [psiMap, neg_inj, inv_inj] at h
  exact sub_left_injective h

theorem psiMap_eq_zero_iff {w : ℂ} : psiMap p w = 0 ↔ w = p := by
  simp [psiMap, sub_eq_zero]

theorem continuousOn_psiMap : ContinuousOn (psiMap p) {(p : ℂ)}ᶜ := by
  have h : ContinuousOn (fun w : ℂ => (w - p)⁻¹) {(p : ℂ)}ᶜ :=
    continuousOn_inv₀.comp (continuous_id.sub continuous_const).continuousOn
      fun w hw => sub_ne_zero.2 hw
  exact h.neg

theorem psiMapInv_psiMap (w : ℂ) : psiMapInv p (psiMap p w) = w := by
  simp [psiMapInv, psiMap, inv_neg]

theorem psiMap_psiMapInv (ζ : ℂ) : psiMap p (psiMapInv p ζ) = ζ := by
  simp [psiMapInv, psiMap, inv_inv]

theorem continuousOn_psiMapInv : ContinuousOn (psiMapInv p) {(0 : ℂ)}ᶜ :=
  continuousOn_const.sub continuousOn_inv₀

theorem psiMapInv_mem_H {ζ : ℂ} (hζ : ζ ∈ H) : psiMapInv p ζ ∈ H := by
  have hζ0 : ζ ≠ 0 := fun h => by
    have h1 : (0 : ℝ) < ζ.im := hζ
    rw [h] at h1; simp at h1
  have hne : psiMapInv p ζ ≠ p := by
    simp [psiMapInv, hζ0]
  rw [← psiMap_mem_H_iff hne, psiMap_psiMapInv]; exact hζ

theorem psiMapInv_mem_Hbar {ζ : ℂ} (hζ : ζ ∈ Hbar) : psiMapInv p ζ ∈ Hbar := by
  show 0 ≤ (psiMapInv p ζ).im
  have : (psiMapInv p ζ).im = ζ.im / normSq ζ := by simp [psiMapInv, inv_im, neg_div]
  rw [this]
  exact div_nonneg hζ (normSq_nonneg ζ)

/-- `ψ_p(w) → 0` as `‖w‖ → ∞`. -/
theorem tendsto_psiMap_zero {ι : Type*} {l : Filter ι} {w : ι → ℂ}
    (hw : Tendsto (fun i => ‖w i‖) l atTop) : Tendsto (fun i => psiMap p (w i)) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun i => ‖w i - p‖) l atTop := by
    refine tendsto_atTop_mono (fun i => ?_) (tendsto_atTop_add_const_right _ (-|p|) hw)
    have := norm_sub_norm_le (w i) (p : ℂ)
    rw [norm_real, Real.norm_eq_abs] at this
    linarith
  have h2 := tendsto_inv_atTop_zero.comp h1
  refine h2.congr fun i => ?_
  simp [psiMap, norm_inv]

/-- `ψ_p` is increasing on `(p, ∞)` with negative values. -/
theorem psiMap_ofReal_lt {x y : ℝ} (hpx : p < x) (hxy : x < y) :
    -(x - p)⁻¹ < -(y - p)⁻¹ ∧ -(y - p)⁻¹ < 0 := by
  have h1 : 0 < x - p := by linarith
  have h2 : 0 < y - p := by linarith
  refine ⟨neg_lt_neg ((inv_lt_inv₀ h2 h1).2 (by linarith)), neg_neg_of_pos (inv_pos.2 h2)⟩

/-! ### Lifts approached from the right -/

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The first-exit lifting lemma, from the right.** Let `α` be continuous on `[u, u + 1]` with
`α((u, u + 1]) ⊆ D_r` and `α(u) ∉ D_r`. Then `g_r(α(t))` converges, as `t ↓ u`, to a real point
`q` with `f̄_r(q) = α(u)`. -/
theorem exists_tendsto_lift_right (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r u : ℝ} (hr : 0 ≤ r) {α : ℝ → ℂ} (hα : ContinuousOn α (Icc u (u + 1)))
    (hαD : ∀ t ∈ Ioc u (u + 1), α t ∈ H \ fwdHull W r) (hαu : α u ∉ H \ fwdHull W r) :
    ∃ q : ℝ, trMap W 0 r q = α u ∧
      Tendsto (fun t => fwdMap W r (α t)) (𝓝[>] u) (𝓝 (q : ℂ)) := by
  set α' : ℝ → ℂ := fun v => α (2 * u - v) with hα'
  have hmaps : MapsTo (fun v : ℝ => 2 * u - v) (Icc (u - 1) u) (Icc u (u + 1)) := fun v hv =>
    ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have hc : ContinuousOn α' (Icc (u - 1) u) :=
    hα.comp (continuous_const.sub continuous_id).continuousOn hmaps
  have hD : ∀ v ∈ Ico (u - 1) u, α' v ∈ H \ fwdHull W r := fun v hv =>
    hαD _ ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have hαu' : α' u ∉ H \ fwdHull W r := by
    simp only [hα', show 2 * u - u = u by ring]; exact hαu
  obtain ⟨q, hq, hlim⟩ := exists_tendsto_lift hη hW hW0 hr (by linarith) hc hD hαu'
  refine ⟨q, by rw [hq]; simp [hα', show 2 * u - u = u by ring], ?_⟩
  have hrefl : Tendsto (fun t : ℝ => 2 * u - t) (𝓝[>] u) (𝓝[<] u) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => 2 * u - t) (𝓝 u) (𝓝 u) :=
        (continuous_const.sub continuous_id).tendsto' u u (by simp only [Pi.sub_apply, id]; ring)
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      show 2 * u - t < u
      have : u < t := ht
      linarith
  refine (hlim.comp hrefl).congr fun t => ?_
  simp [hα']

/-- **The compactified arm.** Let `α` be continuous and injective on `[u, ∞)`, proper, with
`α((u, ∞)) ⊆ D_r`, and let its lift converge to the real gate `q` as `t ↓ u`. For real `p < q`
there is an arc `b : [0, 1] → ℂ` from `ψ_p(q) < 0` to `0`, open in `ℍ`, with
`b((0, 1)) = ψ_p(g_r(α((u, ∞))))`. -/
theorem exists_psiArm (hW : Continuous W) (hW0 : W 0 = 0) {r u : ℝ} (hr : 0 ≤ r) {α : ℝ → ℂ}
    (hα : ContinuousOn α (Ici u)) (hαi : InjOn α (Ici u))
    (hαD : ∀ t ∈ Ioi u, α t ∈ H \ fwdHull W r) (hαt : Tendsto (fun t => ‖α t‖) atTop atTop)
    {q : ℝ} (hlim : Tendsto (fun t => fwdMap W r (α t)) (𝓝[>] u) (𝓝 (q : ℂ))) (hpq : p < q) :
    ∃ b : ℝ → ℂ, ContinuousOn b (Icc 0 1) ∧ InjOn b (Icc 0 1) ∧
      b 0 = ((-(q - p)⁻¹ : ℝ) : ℂ) ∧ b 1 = 0 ∧ (∀ s ∈ Ioo (0 : ℝ) 1, b s ∈ H) ∧
      b '' Ioo 0 1 = psiMap p '' (fwdMap W r '' (α '' Ioi u)) := by
  obtain ⟨K, hK⟩ := exists_norm_trMap_zero_sub_le hW hW0 hr
  set τ : ℝ → ℝ := fun s => u + s / (1 - s) with hτ
  have hτI : ∀ s ∈ Ioo (0 : ℝ) 1, τ s ∈ Ioi u := fun s hs => by
    show u < u + s / (1 - s)
    have : 0 < s / (1 - s) := div_pos hs.1 (by linarith [hs.2])
    linarith
  set e : ℝ → ℂ := fun s => psiMap p (fwdMap W r (α (τ s))) with he
  set b : ℝ → ℂ := fun s => if s = 0 then psiMap p q else if s = 1 then 0 else e s with hb
  have hbI : ∀ s ∈ Ioo (0 : ℝ) 1, b s = e s := fun s hs => by
    show (if s = 0 then psiMap p q else if s = 1 then 0 else e s) = e s
    simp only [hs.1.ne', hs.2.ne, ↓reduceIte]
  have hgH : ∀ s ∈ Ioo (0 : ℝ) 1, fwdMap W r (α (τ s)) ∈ H := fun s hs =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr (hαD _ (hτI s hs))
  have hgp : ∀ s ∈ Ioo (0 : ℝ) 1, fwdMap W r (α (τ s)) ≠ p := fun s hs h => by
    have := hgH s hs; rw [h] at this; exact not_mem_H_ofReal p this
  have heH : ∀ s ∈ Ioo (0 : ℝ) 1, e s ∈ H := fun s hs =>
    (psiMap_mem_H_iff (hgp s hs)).2 (hgH s hs)
  -- continuity of `e` on `(0, 1)`
  have hτc : ContinuousOn τ (Ioo 0 1) :=
    continuousOn_const.add (continuousOn_id.div (continuousOn_const.sub continuousOn_id)
      fun s hs => sub_ne_zero.2 (ne_of_gt hs.2))
  have hec : ContinuousOn e (Ioo 0 1) := by
    have h1 : ContinuousOn (fun s => α (τ s)) (Ioo 0 1) :=
      hα.comp hτc fun s hs => (le_of_lt (hτI s hs) : u ≤ τ s)
    have h2 : ContinuousOn (fun s => fwdMap W r (α (τ s))) (Ioo 0 1) :=
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hr).continuousOn.comp h1
        fun s hs => hαD _ (hτI s hs)
    exact continuousOn_psiMap.comp h2 fun s hs => hgp s hs
  -- the limits at the two ends
  have hq0 : psiMap p q = ((-(q - p)⁻¹ : ℝ) : ℂ) := psiMap_ofReal q
  have hqp : (q : ℂ) ≠ p := fun h => by have := ofReal_injective h; linarith
  have hlim0 : Tendsto e (𝓝[>] 0) (𝓝 (psiMap p q)) := by
    have hτ0 : Tendsto τ (𝓝[>] 0) (𝓝[>] u) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : ContinuousAt τ 0 :=
          continuousAt_const.add (continuousAt_id.div (continuousAt_const.sub continuousAt_id)
            (by norm_num))
        have h0 : τ 0 = u := by simp [hτ]
        exact (h0 ▸ this.tendsto).mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
        exact hτI s hs
    have hψ : ContinuousAt (psiMap p) q :=
      continuousOn_psiMap.continuousAt (isOpen_compl_singleton.mem_nhds hqp)
    exact hψ.tendsto.comp (hlim.comp hτ0)
  have hlim1 : Tendsto e (𝓝[<] 1) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 0) :=
          (continuous_const.sub continuous_id).tendsto' 1 0 (by simp)
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        show 0 < 1 - s
        have : s < 1 := hs
        linarith
    have h2 : Tendsto (fun s : ℝ => s / (1 - s)) (𝓝[<] 1) atTop := by
      have h3 : Tendsto (fun s : ℝ => s) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds
        (continuous_id.tendsto 1)
      exact (h3.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp h1)).congr fun s => by
        simp [div_eq_mul_inv]
    have h4 : Tendsto τ (𝓝[<] 1) atTop := tendsto_atTop_add_const_left _ u h2
    have h5 : Tendsto (fun s => ‖fwdMap W r (α (τ s))‖) (𝓝[<] 1) atTop := by
      refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-K) (hαt.comp h4))
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      have h6 := hK _ (hgH s hs)
      rw [trMap_zero_fwdMap hW hW0 hr (hαD _ (hτI s hs))] at h6
      have h7 := norm_sub_norm_le (α (τ s)) (fwdMap W r (α (τ s)))
      simp only [Function.comp]
      linarith
    exact tendsto_psiMap_zero h5
  refine ⟨b, ?_, ?_, by simp [hb, hq0], by simp [hb], fun s hs => (hbI s hs).symm ▸ heH s hs, ?_⟩
  · -- continuity
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · subst h0
      have hI : Icc (0 : ℝ) 1 = insert 0 (Ioc 0 1) := (Ioc_insert_left zero_le_one).symm
      show ContinuousWithinAt b (Icc 0 1) 0
      rw [hI]
      refine continuousWithinAt_insert_self.2 ?_
      show Tendsto b (𝓝[Ioc 0 1] 0) (𝓝 (b 0))
      have hb0 : b 0 = psiMap p q := by simp [hb]
      rw [hb0]
      have hle : 𝓝[Ioc (0 : ℝ) 1] 0 ≤ 𝓝[>] 0 := nhdsWithin_mono _ Ioc_subset_Ioi_self
      refine (hlim0.mono_left hle).congr' ?_
      filter_upwards [self_mem_nhdsWithin, hle (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))]
        with t _ ht using (hbI t ht).symm
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · subst h1
      have hI : Icc (0 : ℝ) 1 = insert 1 (Ico 0 1) := (Ico_insert_right zero_le_one).symm
      show ContinuousWithinAt b (Icc 0 1) 1
      rw [hI]
      refine continuousWithinAt_insert_self.2 ?_
      show Tendsto b (𝓝[Ico 0 1] 1) (𝓝 (b 1))
      have hb1 : b 1 = 0 := by simp [hb]
      rw [hb1]
      have hle : 𝓝[Ico (0 : ℝ) 1] 1 ≤ 𝓝[<] 1 := nhdsWithin_mono _ Ico_subset_Iio_self
      refine (hlim1.mono_left hle).congr' ?_
      filter_upwards [hle (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num))] with t ht using
        (hbI t ht).symm
    · have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝 s := Ioo_mem_nhds h0 h1
      have hcont : ContinuousAt e s := hec.continuousAt hmem
      refine (hcont.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [hmem] with t ht using hbI t ht
  · -- injectivity
    have hne0 : ∀ s ∈ Ioo (0 : ℝ) 1, b s ≠ psiMap p q := fun s hs h => by
      have h1 := heH s hs
      rw [← hbI s hs, h, hq0] at h1
      exact not_mem_H_ofReal _ h1
    have hne1 : ∀ s ∈ Ioo (0 : ℝ) 1, b s ≠ 0 := fun s hs h => by
      have h1 := heH s hs
      rw [← hbI s hs, h] at h1
      simpa using not_mem_H_ofReal 0 (by simpa using h1)
    have hq0' : psiMap p q ≠ 0 := fun h => hqp (psiMap_eq_zero_iff.1 h)
    have hb0 : b 0 = psiMap p q := by simp [hb]
    have hb1 : b 1 = 0 := by simp [hb]
    intro s hs t ht hst
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0 <;> rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [← hs0, ← ht0]
    · rcases eq_or_lt_of_le ht.2 with ht1 | ht1
      · subst ht1; subst hs0; rw [hb0, hb1] at hst; exact absurd hst hq0'
      · subst hs0; exact absurd (hst.symm.trans hb0) (hne0 t ⟨ht0, ht1⟩)
    · rcases eq_or_lt_of_le hs.2 with hs1 | hs1
      · subst hs1; subst ht0; rw [hb0, hb1] at hst; exact absurd hst.symm hq0'
      · subst ht0; exact absurd (hst.trans hb0) (hne0 s ⟨hs0, hs1⟩)
    rcases eq_or_lt_of_le hs.2 with hs1 | hs1 <;> rcases eq_or_lt_of_le ht.2 with ht1 | ht1
    · rw [hs1, ht1]
    · subst hs1; exact absurd (hst.symm.trans hb1) (hne1 t ⟨ht0, ht1⟩)
    · subst ht1; exact absurd (hst.trans hb1) (hne1 s ⟨hs0, hs1⟩)
    · have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, hs1⟩
      have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
      rw [hbI s hsI, hbI t htI] at hst
      have h1 := psiMap_injective hst
      have h2 := QuantumZipper.FwdHolo.injOn_fwdMap hW hr (hαD _ (hτI s hsI))
        (hαD _ (hτI t htI)) h1
      have h3 := hαi (le_of_lt (hτI s hsI) : u ≤ τ s) (le_of_lt (hτI t htI) : u ≤ τ t) h2
      simp only [hτ, add_right_inj] at h3
      have hs' : 1 - s ≠ 0 := by linarith
      have ht' : 1 - t ≠ 0 := by linarith
      field_simp at h3
      linarith
  · -- the image
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [hbI s hs]
      exact ⟨_, ⟨_, ⟨τ s, hτI s hs, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩
      have ht0 : 0 < t - u := sub_pos.2 ht
      set s := (t - u) / (1 + (t - u)) with hs
      have hsI : s ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos ht0 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
      have hτs : τ s = t := by
        simp only [hτ, hs]
        have h1 : (1 + (t - u)) ≠ 0 := by linarith
        have h2 : 1 - (t - u) / (1 + (t - u)) = 1 / (1 + (t - u)) := by field_simp; ring
        rw [h2]; field_simp; ring
      exact ⟨s, hsI, by rw [hbI s hsI]; simp only [he, hτs]⟩

end InteractingSLE.Sec6
