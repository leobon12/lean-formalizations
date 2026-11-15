/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11ChartBdryPlanar
import InteractingSLE.Spec.Supplement.GB11ChartBdryDilation
import InteractingSLE.Spec.Supplement.GW3Chart
import InteractingSLE.Spec.Sec6.Aux40InfJordan
import InteractingSLE.Spec.Sec7.InteractionLens

/-!
# Lemma GB11's pocket charts: the boundary correspondence (`GB11ChartBdryStatement` PROVED)

Packet PROVE-T14-GW4T5, item (1a). `GB11Conn.GB11ChartBdryStatement` (PROVE-T14-GW4T4's named input: Carathéodory's
boundary map of a shaped pocket, read in the relative chart, `GB11Conn.ChartBdryCorr`) is proved, deterministically,
from the walls' properties in GB11's barrier input that it actually needs: the two walls are complete simple flows whose
common contacts have the same order along both curves. The trace, the (GB11.B) and visit-order clauses, GB10 and the
walk pocket shape are not used.

## The argument

* The two boundary arcs of the pocket meet only at its ends (`GB11ChartBdryPlanar`, Janiszewski), so the frontier is the
  Jordan curve `α_R([s₁, s₂]) ∪ α_L([t₁, t₂])` (bounded pocket), resp. `μ(α_R([s₁, ∞)) ∪ α_L([t₁, ∞))) ∪ {0}` after
  `μ(z) = −1/(z + i)` (unbounded pocket, `∞ ↦ 0`), and the pocket is its inner domain.
* The Jordan coordinate (`Sec6.exists_jordanCoord`: exit `↦ 0`, entry `↦ ∞`) has an inverse `G` continuous and injective
  on `ℍ̄`; every component chart is `c⁻¹(w) = G(k w)`, `k > 0` (`GB11ChartBdryDilation`), with the positive reals on the
  right arc and the negative reals on the left arc.
* In the relative chart `relInvC c (v) = −1/c⁻¹(−1/v)`: the limit at `x ≠ 0` is `−1/G(−k/x)`, on the left wall for
  `x > 0` and on the right wall for `x < 0`; the wall parameters `r_L`, `r_R` are continuous (the walls are closed
  embeddings) and injective, hence strictly monotone, and their direction is forced by the limit at the exit
  (`x → ±∞`); the limit at `0` is `−1/(entry)` (bounded pocket) or `0` (unbounded pocket, `G → ∞`).

## Main results

* `antitoneOn_Ioi_of_injOn`, `monotoneOn_Iio_of_injOn` (continuous injective wall parameters);
* `chartBdryCorr_of_dilation` (the assembly);
* `IsPocketCoord`, `exists_isPocketCoord_of_bounded`, `exists_isPocketCoord_of_unbounded` (the pocket's Jordan
  coordinate adapted to the chart, exported for the relative trace, `GB11LocalGrowthCurve`);
* `exists_chartBdryCorr_of_bounded`, `exists_chartBdryCorr_of_unbounded`;
* **`gb11ChartBdryStatement : GB11Conn.GB11ChartBdryStatement`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Theorem14

namespace GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-! ### Monotone wall parameters -/

/-- A continuous injective `f : (0, ∞) → ℝ≥0` staying above its limit `t` at `+∞` is antitone. -/
theorem antitoneOn_Ioi_of_injOn {f : ℝ → ℝ≥0} {t : ℝ≥0} (hc : ContinuousOn f (Ioi 0)) (hi : InjOn f (Ioi 0))
    (hgt : ∀ x : ℝ, 0 < x → t < f x) (hlim : Tendsto f atTop (𝓝 t)) : AntitoneOn f (Ioi 0) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · exact le_rfl
  by_contra hlt
  push Not at hlt
  have hge : ∀ z : ℝ, y ≤ z → f y ≤ f z := by
    intro z hz
    have hsub : Icc x z ⊆ Ioi 0 := fun w hw => lt_of_lt_of_le (mem_Ioi.1 hx) hw.1
    rcases (hc.mono hsub).strictMonoOn_of_injOn_Icc' (hxy.le.trans hz) (hi.mono hsub) with h | h
    · rcases eq_or_lt_of_le hz with rfl | hz
      · exact le_rfl
      · exact (h ⟨hxy.le, hz.le⟩ ⟨hxy.le.trans hz.le, le_rfl⟩ hz).le
    · exact absurd (h ⟨le_rfl, hxy.le.trans hz⟩ ⟨hxy.le, hz⟩ hxy) (not_lt.2 hlt.le)
  have : f y ≤ t := ge_of_tendsto hlim (eventually_atTop.2 ⟨y, hge⟩)
  exact absurd (hgt y hy) (not_lt.2 this)

/-- A continuous injective `f : (−∞, 0) → ℝ≥0` staying above its limit `t` at `−∞` is monotone. -/
theorem monotoneOn_Iio_of_injOn {f : ℝ → ℝ≥0} {t : ℝ≥0} (hc : ContinuousOn f (Iio 0)) (hi : InjOn f (Iio 0))
    (hgt : ∀ x : ℝ, x < 0 → t < f x) (hlim : Tendsto f atBot (𝓝 t)) : MonotoneOn f (Iio 0) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · exact le_rfl
  by_contra hlt
  push Not at hlt
  have hge : ∀ z : ℝ, z ≤ x → f x ≤ f z := by
    intro z hz
    have hsub : Icc z y ⊆ Iio 0 := fun w hw => lt_of_le_of_lt hw.2 (mem_Iio.1 hy)
    rcases (hc.mono hsub).strictMonoOn_of_injOn_Icc' (hz.trans hxy.le) (hi.mono hsub) with h | h
    · exact absurd (h ⟨hz, hxy.le⟩ ⟨hz.trans hxy.le, le_rfl⟩ hxy) (not_lt.2 hlt.le)
    · rcases eq_or_lt_of_le hz with rfl | hz
      · exact le_rfl
      · exact (h ⟨le_rfl, hz.le.trans hxy.le⟩ ⟨hz.le, hxy.le⟩ hz).le
  have : f x ≤ t := ge_of_tendsto hlim (eventually_atBot.2 ⟨x, hge⟩)
  exact absurd (hgt x hx) (not_lt.2 this)

/-! ### The assembly -/

/-- A complete simple flow is a closed embedding (proper, continuous, injective). -/
theorem isClosedEmbedding_of_isCompleteSimpleFlow {α : ℝ≥0 → ℂ} (h : GB11.IsCompleteSimpleFlow α) :
    Topology.IsClosedEmbedding α :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap h.1 h.2.1
    fun _ hS => Supp9B.isClosed_image ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩ hS

/-- **The boundary correspondence from a dilated Jordan coordinate.** If `c⁻¹(w) = G(k w)` on `ℍ` (`k > 0`), with `G`
continuous and injective on `ℍ̄`, `G(0)` the exit `α_R(s₁) = α_L(t₁)`, the positive reals going to the right wall beyond
`s₁` and the negative reals to the left wall beyond `t₁`, and `−1/G → e₀` at `∞` (`e₀` the entry value of
`ChartBdryCorr`), then `c` has the boundary correspondence `ChartBdryCorr`. -/
theorem chartBdryCorr_of_dilation {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR)
    (hL : GB11.IsCompleteSimpleFlow αL) {c : Chart} {G : ℂ → ℂ} {k : ℝ} (hk : 0 < k)
    (hcG : ∀ w ∈ H, c.2.1 w = G ((k : ℂ) * w)) (hGc : ContinuousOn G Hbar) (hGi : InjOn G Hbar)
    {s₁ t₁ : ℝ≥0} (hG0 : G 0 = αR s₁) (h1 : αR s₁ = αL t₁)
    (hGpos : ∀ r : ℝ, 0 < r → G r ∈ αR '' Ioi s₁) (hGneg : ∀ r : ℝ, r < 0 → G r ∈ αL '' Ioi t₁)
    {s₂ : ℝ≥0∞} {e₀ : ℂ} (he₀ : Tendsto (fun w => -(G w)⁻¹) (cobounded ℂ ⊓ 𝓟 H) (𝓝 e₀))
    (hs₂ : (s₂ = ⊤ → e₀ = 0) ∧ (s₂ ≠ ⊤ → e₀ = -(αR s₂.toNNReal)⁻¹)) :
    ∃ (e : ℝ → ℂ) (rR rL : ℝ → ℝ≥0), ChartBdryCorr αR αL c s₂ e rR rL := by
  classical
  set g : ℝ → ℂ := fun x => G ((k * -x⁻¹ : ℝ) : ℂ) with hg
  have hkx : ∀ x : ℝ, x ≠ 0 → k * -x⁻¹ ≠ 0 := fun x hx =>
    mul_ne_zero hk.ne' (neg_ne_zero.2 (inv_ne_zero hx))
  -- `G` vanishes nowhere on `ℝ \ {0}` (the walls meet `0` only at time `0`)
  have hGne : ∀ r : ℝ, r ≠ 0 → G r ≠ 0 := by
    intro r hr h0
    rcases lt_or_gt_of_ne hr with h | h
    · obtain ⟨a, ha, he⟩ := hGneg r h
      have : a = 0 := hL.2.1 (he.trans (h0.trans hL.2.2.1.symm))
      exact absurd (this ▸ mem_Ioi.1 ha) (not_lt.2 zero_le)
    · obtain ⟨a, ha, he⟩ := hGpos r h
      have : a = 0 := hR.2.1 (he.trans (h0.trans hR.2.2.1.symm))
      exact absurd (this ▸ mem_Ioi.1 ha) (not_lt.2 zero_le)
  have hgc : ∀ x : ℝ, x ≠ 0 → ContinuousAt g x := fun x hx => by
    have h1 : ContinuousAt (fun x : ℝ => ((k * -x⁻¹ : ℝ) : ℂ)) x :=
      Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul (continuousAt_inv₀ hx).neg)
    exact (continuousWithinAt_univ _ _).1 (ContinuousWithinAt.comp (g := G)
      (f := fun x : ℝ => ((k * -x⁻¹ : ℝ) : ℂ)) (x := x) (s := univ) (t := Hbar)
      (hGc _ (ofReal_mem_Hbar _)) h1.continuousWithinAt fun y _ => ofReal_mem_Hbar _)
  have hglim : ∀ {l : Filter ℝ}, Tendsto (fun x => k * -x⁻¹) l (𝓝 0) → Tendsto g l (𝓝 (G 0)) := by
    intro l hl
    have h1 : Tendsto (fun x : ℝ => ((k * -x⁻¹ : ℝ) : ℂ)) l (𝓝[Hbar] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun x => ofReal_mem_Hbar _⟩
      have h := (Complex.continuous_ofReal.tendsto 0).comp hl
      rw [Complex.ofReal_zero] at h
      exact h
    exact (hGc 0 (by simpa using ofReal_mem_Hbar 0)).tendsto.comp h1
  have hginj : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → g x = g y → x = y := by
    intro x y _ _ hxy
    have h := hGi (ofReal_mem_Hbar _) (ofReal_mem_Hbar _) hxy
    have h' : k * -x⁻¹ = k * -y⁻¹ := Complex.ofReal_injective h
    have : x⁻¹ = y⁻¹ := by
      have := mul_left_cancel₀ hk.ne' h'
      linarith
    exact inv_injective this
  set e : ℝ → ℂ := fun x => if x = 0 then e₀ else -(g x)⁻¹ with he
  set rL : ℝ → ℝ≥0 := fun x => Function.invFun αL (g x) with hrL
  set rR : ℝ → ℝ≥0 := fun x => Function.invFun αR (g x) with hrR
  have hrL_spec : ∀ x : ℝ, 0 < x → αL (rL x) = g x ∧ t₁ < rL x := by
    intro x hx
    have hneg' : k * -x⁻¹ < 0 := mul_neg_of_pos_of_neg hk (neg_neg_of_pos (inv_pos.2 hx))
    obtain ⟨a, ha, he'⟩ := hGneg _ hneg'
    have h1 : αL (rL x) = g x := Function.invFun_eq ⟨a, he'⟩
    refine ⟨h1, ?_⟩
    have : rL x = a := hL.2.1 (h1.trans he'.symm)
    rw [this]; exact ha
  have hrR_spec : ∀ x : ℝ, x < 0 → αR (rR x) = g x ∧ s₁ < rR x := by
    intro x hx
    have hpos' : 0 < k * -x⁻¹ := mul_pos hk (neg_pos.2 (inv_lt_zero.2 hx))
    obtain ⟨a, ha, he'⟩ := hGpos _ hpos'
    have h1 : αR (rR x) = g x := Function.invFun_eq ⟨a, he'⟩
    refine ⟨h1, ?_⟩
    have : rR x = a := hR.2.1 (h1.trans he'.symm)
    rw [this]; exact ha
  have hLe := (isClosedEmbedding_of_isCompleteSimpleFlow hL).isInducing
  have hRe := (isClosedEmbedding_of_isCompleteSimpleFlow hR).isInducing
  have hkH : ∀ w ∈ H, (k : ℂ) * w ∈ H := fun w hw => by
    show (0 : ℝ) < ((k : ℂ) * w).im
    simpa [Complex.mul_im] using mul_pos hk hw
  have hrel : ∀ v ∈ H, relInvC c v = -(G ((k : ℂ) * -v⁻¹))⁻¹ := fun v hv => by
    simp only [relInvC]
    rw [hcG _ (negInv_mem_H' hv)]
  refine ⟨e, rR, rL, fun x => ?_, fun x hx => ?_, ?_, fun x hx => ?_, ?_, fun h => ?_, fun h => ?_⟩
  · by_cases hx : x = 0
    · subst hx
      have h0 : Tendsto (fun v : ℂ => -v⁻¹) (𝓝[H] ((0 : ℝ) : ℂ)) (cobounded ℂ ⊓ 𝓟 H) := by
        rw [Complex.ofReal_zero]; exact GW3.tendsto_neg_inv_nhdsWithin_zero
      have hmul : Tendsto (fun w : ℂ => (k : ℂ) * w) (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ ⊓ 𝓟 H) :=
        tendsto_inf.2 ⟨(tendsto_mul_left_cobounded (Complex.ofReal_ne_zero.2 hk.ne')).mono_left inf_le_left,
          tendsto_principal.2 (mem_inf_of_right (mem_principal.2 fun w hw => hkH w hw))⟩
      have := he₀.comp (hmul.comp h0)
      simp only [he, ↓reduceIte]
      exact this.congr' (eventually_nhdsWithin_of_forall fun v hv => (hrel v hv).symm)
    · simp only [he, hx, ↓reduceIte]
      have h0 := GW3.tendsto_neg_inv_nhdsWithin hx
      have hmul : Tendsto (fun w : ℂ => (k : ℂ) * w) (𝓝[H] ((-x⁻¹ : ℝ) : ℂ))
          (𝓝[Hbar] ((k * -x⁻¹ : ℝ) : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw =>
          H_subset_Hbar (hkH w hw)⟩
        have : ((k * -x⁻¹ : ℝ) : ℂ) = (k : ℂ) * ((-x⁻¹ : ℝ) : ℂ) := by push_cast; ring
        rw [this]
        exact ((continuous_const.mul continuous_id).tendsto _).mono_left nhdsWithin_le_nhds
      have hG := (hGc _ (ofReal_mem_Hbar _)).tendsto.comp (hmul.comp h0)
      have := (hG.inv₀ (hGne _ (hkx x hx))).neg
      exact this.congr' (eventually_nhdsWithin_of_forall fun v hv => (hrel v hv).symm)
  · obtain ⟨h1, -⟩ := hrL_spec x hx
    refine ⟨h1 ▸ hGne _ (hkx x hx.ne'), ?_⟩
    simp only [he, hx.ne', ↓reduceIte, h1]
  · refine antitoneOn_Ioi_of_injOn ?_ ?_ (fun x hx => (hrL_spec x hx).2) ?_
    · refine hLe.continuousOn_iff.2 ?_
      refine ContinuousOn.congr (fun x hx => (hgc x (ne_of_gt hx)).continuousWithinAt) fun x hx => ?_
      exact (hrL_spec x hx).1
    · intro x hx y hy hxy
      have := congrArg αL hxy
      rw [(hrL_spec x hx).1, (hrL_spec y hy).1] at this
      exact hginj x y (ne_of_gt hx) (ne_of_gt hy) this
    · refine hLe.tendsto_nhds_iff.2 ?_
      have hl : Tendsto (fun x : ℝ => k * -x⁻¹) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.neg.const_mul k)
      rw [← h1, ← hG0]
      refine (hglim hl).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      exact (hrL_spec x hx).1.symm
  · obtain ⟨h1, -⟩ := hrR_spec x hx
    refine ⟨h1 ▸ hGne _ (hkx x hx.ne), ?_⟩
    simp only [he, hx.ne, ↓reduceIte, h1]
  · refine monotoneOn_Iio_of_injOn ?_ ?_ (fun x hx => (hrR_spec x hx).2) ?_
    · refine hRe.continuousOn_iff.2 ?_
      refine ContinuousOn.congr (fun x hx => (hgc x (ne_of_lt hx)).continuousWithinAt) fun x hx => ?_
      exact (hrR_spec x hx).1
    · intro x hx y hy hxy
      have := congrArg αR hxy
      rw [(hrR_spec x hx).1, (hrR_spec y hy).1] at this
      exact hginj x y (ne_of_lt hx) (ne_of_lt hy) this
    · refine hRe.tendsto_nhds_iff.2 ?_
      have hl : Tendsto (fun x : ℝ => k * -x⁻¹) atBot (𝓝 0) := by
        simpa using (tendsto_inv_atBot_zero.neg.const_mul k)
      rw [← hG0]
      refine (hglim hl).congr' ?_
      filter_upwards [eventually_lt_atBot 0] with x hx
      exact (hrR_spec x hx).1.symm
  · simp only [he, ↓reduceIte]; exact hs₂.1 h
  · simp only [he, ↓reduceIte]; exact hs₂.2 h

/-! ### The bounded pocket -/

/-- A parameter interval `[a, b]` of a continuous injective curve, reparametrized by `[0, 1]`. -/
theorem exists_unitParam {α : ℝ≥0 → ℂ} (hα : Continuous α) (hαi : Function.Injective α) {a b : ℝ≥0}
    (hab : a < b) :
    ∃ u : ℝ → ℂ, ContinuousOn u (Icc 0 1) ∧ InjOn u (Icc 0 1) ∧ u 0 = α a ∧ u 1 = α b ∧
      u '' Icc 0 1 = α '' Icc a b := by
  have hba : (0 : ℝ) < (b : ℝ) - a := sub_pos.2 (NNReal.coe_lt_coe.2 hab)
  set φ : ℝ → ℝ≥0 := fun x => ((a : ℝ) + x * ((b : ℝ) - a)).toNNReal with hφ
  have hφnn : ∀ x ∈ Icc (0 : ℝ) 1, (0 : ℝ) ≤ (a : ℝ) + x * ((b : ℝ) - a) := fun x hx =>
    add_nonneg a.coe_nonneg (mul_nonneg hx.1 hba.le)
  have hφc : ∀ x ∈ Icc (0 : ℝ) 1, ((φ x : ℝ≥0) : ℝ) = (a : ℝ) + x * ((b : ℝ) - a) := fun x hx =>
    Real.coe_toNNReal _ (hφnn x hx)
  refine ⟨α ∘ φ, (hα.comp (continuous_real_toNNReal.comp (by fun_prop))).continuousOn, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have h1 : φ x = φ y := hαi hxy
    have h2 := congrArg (fun r : ℝ≥0 => (r : ℝ)) h1
    simp only [hφc x hx, hφc y hy] at h2
    have := mul_right_cancel₀ hba.ne' (by linarith : x * ((b : ℝ) - a) = y * ((b : ℝ) - a))
    exact this
  · simp [hφ]
  · simp [hφ]
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨φ x, ⟨?_, ?_⟩, rfl⟩
      · rw [← NNReal.coe_le_coe, hφc x hx]
        nlinarith [hx.1, hba]
      · rw [← NNReal.coe_le_coe, hφc x hx]
        nlinarith [hx.2, hba]
    · rintro ⟨r, hr, rfl⟩
      have hr1 : (a : ℝ) ≤ r := NNReal.coe_le_coe.2 hr.1
      have hr2 : (r : ℝ) ≤ b := NNReal.coe_le_coe.2 hr.2
      set x : ℝ := ((r : ℝ) - a) / ((b : ℝ) - a) with hx
      have hx0 : 0 ≤ x := div_nonneg (by linarith) hba.le
      have hx1 : x ≤ 1 := (div_le_one hba).2 (by linarith)
      refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
      have : φ x = r := by
        apply NNReal.coe_injective
        rw [hφc x ⟨hx0, hx1⟩, hx]
        field_simp
        ring
      simp only [Function.comp_apply, this]

/-! ### The pocket coordinate -/

/-- **A Jordan coordinate of a shaped pocket adapted to a component chart** `c` (the data produced by Carathéodory's
theorem, exported for the relative trace of Lemma GB11): `ψ` is continuous on `C̄ \ E` (`E` the entry: `{α_R(s₂)}`
for a bounded pocket, `∅` for the unbounded one, whose entry is `∞`) with values in `ℍ̄`, `G` is continuous on `ℍ̄`
with values in `C̄ \ E`, they are mutually inverse, `c⁻¹(w) = G(k w)` on `ℍ` (`k > 0`), `G(0)` is the exit
`α_R(s₁)`, and `G` sends the positive reals into the right wall beyond `s₁`, the negative reals into the left wall
beyond `t₁`. -/
structure IsPocketCoord (αR αL : ℝ≥0 → ℂ) (C : Set ℂ) (c : Chart) (s₁ t₁ : ℝ≥0) (E : Set ℂ) (ψ G : ℂ → ℂ)
    (k : ℝ) : Prop where
  pos : 0 < k
  inv_eq : ∀ w ∈ H, c.2.1 w = G ((k : ℂ) * w)
  continuousOn_G : ContinuousOn G Hbar
  mapsTo_G : MapsTo G Hbar (closure C \ E)
  left_inv : ∀ w ∈ Hbar, ψ (G w) = w
  right_inv : ∀ z ∈ closure C \ E, G (ψ z) = z
  continuousOn_ψ : ContinuousOn ψ (closure C \ E)
  mapsTo_ψ : MapsTo ψ (closure C \ E) Hbar
  G_zero : G 0 = αR s₁
  pos_arc : ∀ r : ℝ, 0 < r → G r ∈ αR '' Ioi s₁
  neg_arc : ∀ r : ℝ, r < 0 → G r ∈ αL '' Ioi t₁

theorem IsPocketCoord.injOn_G {αR αL : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {s₁ t₁ : ℝ≥0} {E : Set ℂ}
    {ψ G : ℂ → ℂ} {k : ℝ} (h : IsPocketCoord αR αL C c s₁ t₁ E ψ G k) : InjOn G Hbar :=
  fun w hw w' hw' he => by rw [← h.left_inv w hw, ← h.left_inv w' hw', he]

/-- **The pocket coordinate of a bounded shaped pocket.** -/
theorem exists_isPocketCoord_of_bounded {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR)
    (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) (hs₂ : s₂ ≠ ⊤) {c : Chart}
    (hc : IsComponentChart (range αR) (range αL) C c) (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁))) :
    ∃ (ψ G : ℂ → ℂ) (k : ℝ), IsPocketCoord αR αL C c s₁ t₁ {αR s₂.toNNReal} ψ G k ∧
      Tendsto G (cobounded ℂ ⊓ 𝓟 H) (𝓝 (αR s₂.toNNReal)) ∧
      Tendsto ψ (𝓝[closure C \ {αR s₂.toNNReal}] (αR s₂.toNNReal)) (cobounded ℂ) := by
  -- the pocket
  obtain ⟨z₀, hz₀, -, -, hCz⟩ := id hC
  have hRc : IsClosed (range αR) := isClosed_range_of_isCompleteSimpleFlow hR
  have hLc : IsClosed (range αL) := isClosed_range_of_isCompleteSimpleFlow hL
  have hCo : IsOpen C := isOpen_of_mem_betweenComponents hRc hLc hC
  have hCc : IsPreconnected C := hCz ▸ isPreconnected_connectedComponentIn
  have hz₀C : z₀ ∈ C := hCz ▸ mem_connectedComponentIn hz₀
  have hCsub : C ⊆ H \ (range αR ∪ range αL) := hCz ▸ connectedComponentIn_subset _ _
  have hCF : ∀ z ∈ C, z ∉ range αR ∪ range αL := fun z hz => (hCsub hz).2
  have ht₂ : t₂ ≠ ⊤ := fun h => hs₂ (hs.top_iff.2 h)
  set s₂' := s₂.toNNReal with hs₂'
  set t₂' := t₂.toNNReal with ht₂'
  obtain ⟨h2, hQ, hCb⟩ := hs.entry hs₂
  have h1 := hs.contact
  have hP := hs.mem_closure_exit
  have hs12 : s₁ < s₂' := ENNReal.coe_lt_coe.1 (by rw [hs₂', ENNReal.coe_toNNReal hs₂]; exact hs.lt)
  have hconv : ∀ (r : ℝ≥0) {u : ℝ≥0∞}, u ≠ ⊤ → ((r : ℝ≥0∞) ≤ u ↔ r ≤ u.toNNReal) := fun r u hu => by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hu]
  have hfr : frontier C ⊆ αR '' Icc s₁ s₂' ∪ αL '' Icc t₁ t₂' := by
    refine hs.frontier_subset.trans (union_subset_union (image_mono fun r hr => ?_) (image_mono fun r hr => ?_))
    · exact ⟨hr.1, (hconv r hs₂).1 hr.2⟩
    · exact ⟨hr.1, (hconv r ht₂).1 hr.2⟩
  have hinter := inter_subset_of_boundedPocket hR hL hord h1 h2 hCo hCc hCb hz₀C hCF hfr hP hQ
  have ht12 : t₁ < t₂' := (hord s₁ s₂' t₁ t₂' h1 h2).1 hs12
  set A := αR '' Icc s₁ s₂' with hA
  set B := αL '' Icc t₁ t₂' with hB
  set P := αR s₁ with hPdef
  set Q := αR s₂' with hQdef
  have hPQ : P ≠ Q := fun h => hs12.ne (hR.2.1 h)
  have hPA : P ∈ A := ⟨s₁, ⟨le_rfl, hs12.le⟩, rfl⟩
  have hQA : Q ∈ A := ⟨s₂', ⟨hs12.le, le_rfl⟩, rfl⟩
  have hPB : P ∈ B := ⟨t₁, ⟨le_rfl, ht12.le⟩, h1.symm⟩
  have hQB : Q ∈ B := ⟨t₂', ⟨ht12.le, le_rfl⟩, h2.symm⟩
  -- the Jordan curve `A ∪ B`
  obtain ⟨u, huc, hui, hu0, hu1, huim⟩ := exists_unitParam hR.1 hR.2.1 hs12
  obtain ⟨v, hvc, hvi, hv0, hv1, hvim⟩ := exists_unitParam hL.1 hL.2.1 ht12
  have hJ : LQGMetric.JordanMap.IsJordanCurve (A ∪ B) := by
    rw [hA, hB, ← huim, ← hvim]
    refine Sec7.isJordanCurve_image_union huc hvc hui hvi (by rw [hu0, hv0]; exact h1) (by rw [hu1, hv1]; exact h2) ?_
    rw [huim, hvim, hu0, hu1]
    exact hinter
  have hJsub : A ∪ B ⊆ range αR ∪ range αL := union_subset_union (image_subset_range _ _) (image_subset_range _ _)
  have hCeq : connectedComponentIn (A ∪ B)ᶜ z₀ = C :=
    eq_connectedComponentIn_of_frontier_subset hCo hCc hz₀C (fun z hz hzJ => hCF z hz (hJsub hzJ)) hfr
  obtain ⟨ψ, G, hψc, hψm, hGc, hGm, hGψ, hψG, hconf, hreal, hψP, hψQ⟩ :=
    Sec6.exists_jordanCoord hJ (p := z₀) (fun h => hCF z₀ hz₀C (hJsub h)) (by rw [hCeq]; exact hCb)
      (Or.inl hQA : Q ∈ A ∪ B) (Or.inl hPA : P ∈ A ∪ B)
  rw [hCeq] at hψc hψm hGm hGψ hconf hψQ
  have hQC : Q ∉ C := fun h => hCF Q h (Or.inl ⟨s₂', rfl⟩)
  have hGψ' : ∀ z ∈ C, G (ψ z) = z := fun z hz =>
    hGψ z ⟨subset_closure hz, fun h => hQC (mem_singleton_iff.1 h ▸ hz)⟩
  have hψG' : ∀ w ∈ H, ψ (G w) = w := fun w hw => hψG w (H_subset_Hbar hw)
  have hG0 : G 0 = P := by
    rw [← hψP]; exact hGψ P ⟨hP, fun h => hPQ (mem_singleton_iff.1 h)⟩
  have hGi : InjOn G Hbar := fun w hw w' hw' h => by rw [← hψG w hw, ← hψG w' hw', h]
  -- points of `ℍ̄` go to `C` (from `ℍ`) or to the frontier (from `ℝ`)
  have hGfr : ∀ w ∈ Hbar, G w ∉ C → G w ∈ frontier C := fun w hw hn =>
    ⟨(hGm hw).1, by rw [hCo.interior_eq]; exact hn⟩
  have hGH : MapsTo G H C := by
    intro w hw
    by_contra hn
    have hfw := hfr (hGfr w (H_subset_Hbar hw) hn)
    have him := hreal (G w) ⟨hfw, (hGm (H_subset_Hbar hw)).2⟩
    rw [hψG' w hw] at him
    exact absurd him (ne_of_gt hw)
  have hGr : ∀ r : ℝ, r ≠ 0 → G r ∈ (A \ B) ∪ (B \ A) := by
    intro r hr
    have hrC : G r ∉ C := fun h => by
      have := hconf.2.1 h
      rw [hψG r (ofReal_mem_Hbar r)] at this
      exact absurd (show (0 : ℝ) < (r : ℂ).im from this) (by simp)
    have hfr' := hfr (hGfr r (ofReal_mem_Hbar r) hrC)
    have hrP : G r ≠ P := fun h => hr (Complex.ofReal_eq_zero.1
      (hGi (ofReal_mem_Hbar r) (by simpa using ofReal_mem_Hbar 0) (h.trans hG0.symm)))
    have hrQ : G r ≠ Q := (hGm (ofReal_mem_Hbar r)).2
    rcases hfr' with h | h
    · refine Or.inl ⟨h, fun hB' => ?_⟩
      rcases hinter ⟨h, hB'⟩ with h' | h'
      exacts [hrP h', hrQ h']
    · refine Or.inr ⟨h, fun hA' => ?_⟩
      rcases hinter ⟨hA', h⟩ with h' | h'
      exacts [hrP h', hrQ h']
  have hAL : ∀ z ∈ A \ B, z ∉ range αL := by
    rintro _ ⟨⟨m, hm, rfl⟩, hnB⟩ ⟨m'', he⟩
    rcases eq_or_lt_of_le hm.1 with h | h
    · exact hnB (h ▸ hPB)
    rcases eq_or_lt_of_le hm.2 with h' | h'
    · exact hnB (h' ▸ hQB)
    exact hnB ⟨m'', ⟨((hord s₁ m t₁ m'' h1 he.symm).1 h).le, ((hord m s₂' m'' t₂' he.symm h2).1 h').le⟩, he⟩
  have hBR : ∀ z ∈ B \ A, z ∉ range αR := by
    rintro _ ⟨⟨m, hm, rfl⟩, hnA⟩ ⟨m'', he⟩
    rcases eq_or_lt_of_le hm.1 with h | h
    · exact hnA (by rw [← h, ← h1]; exact hPA)
    rcases eq_or_lt_of_le hm.2 with h' | h'
    · exact hnA (by rw [h', ← h2]; exact hQA)
    exact hnA ⟨m'', ⟨((hord s₁ m'' t₁ m h1 he).2 h).le, ((hord m'' s₂' m t₂' he h2).2 h').le⟩, he⟩
  have hAc : IsClosed A := (isCompact_Icc.image hR.1).isClosed
  have hBc : IsClosed B := (isCompact_Icc.image hL.1).isClosed
  have hGinf : Tendsto G (cobounded ℂ ⊓ 𝓟 H) (𝓝 Q) := GW3.tendsto_cobounded_of_coord hCb hψc hψG hGm
  obtain ⟨k, hk, hcG, hGpos, hGneg⟩ := exists_dilation_of_extInv hc hCo hconf.1 hconf.2.1 hGψ' hψG' hGH hGc hGi
    hAc hBc hGr hAL hBR (by rw [hG0]; exact hxC) hGinf (by rw [hG0]; exact disjoint_nhds_nhds.2 hPQ.symm)
  refine ⟨ψ, G, k, ⟨hk, hcG, hGc, hGm, hψG, hGψ, hψc, hψm, hG0, fun r hr => ?_, fun r hr => ?_⟩, hGinf, hψQ⟩
  · obtain ⟨⟨m, hm, he⟩, hnB⟩ := hGpos r hr
    refine ⟨m, lt_of_le_of_ne hm.1 fun h => hnB ?_, he⟩
    rw [← he, ← h]; exact hPB
  · obtain ⟨⟨m, hm, he⟩, hnA⟩ := hGneg r hr
    refine ⟨m, lt_of_le_of_ne hm.1 fun h => hnA ?_, he⟩
    rw [← he, ← h, ← h1]; exact hPA

/-- **The boundary correspondence of a bounded shaped pocket.** -/
theorem exists_chartBdryCorr_of_bounded {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR)
    (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) (hs₂ : s₂ ≠ ⊤) {c : Chart}
    (hc : IsComponentChart (range αR) (range αL) C c) (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁))) :
    ∃ (e : ℝ → ℂ) (rR rL : ℝ → ℝ≥0), ChartBdryCorr αR αL c s₂ e rR rL := by
  obtain ⟨ψ, G, k, hpc, hGinf, -⟩ := exists_isPocketCoord_of_bounded hR hL hord hC hs hs₂ hc hxC
  have hs12 : s₁ < s₂.toNNReal :=
    ENNReal.coe_lt_coe.1 (by rw [ENNReal.coe_toNNReal hs₂]; exact hs.lt)
  have hQ0 : αR s₂.toNNReal ≠ 0 := fun h => by
    have : s₂.toNNReal = 0 := hR.2.1 (h.trans hR.2.2.1.symm)
    exact absurd (this ▸ hs12) (not_lt.2 zero_le)
  exact chartBdryCorr_of_dilation hR hL hpc.pos hpc.inv_eq hpc.continuousOn_G hpc.injOn_G hpc.G_zero hs.contact
    hpc.pos_arc hpc.neg_arc ((hGinf.inv₀ hQ0).neg) ⟨fun h => absurd h hs₂, fun _ => rfl⟩

/-! ### The unbounded pocket -/

/-- The `μ`-image of a proper wall beyond a parameter, compactified by `0 = μ(∞)`, is an arc from `μ(α(s))` to `0`
(`Sec6.exists_compactArm` for `v ↦ α(s + v) + i` and `ψ_0`). -/
theorem exists_muArm {α : ℝ≥0 → ℂ} (hα : GB11.IsCompleteSimpleFlow α) (s : ℝ≥0) :
    ∃ b : ℝ → ℂ, ContinuousOn b (Icc 0 1) ∧ InjOn b (Icc 0 1) ∧ b 0 = mu (α s) ∧ b 1 = 0 ∧
      b '' Icc 0 1 = mu '' (α '' Ici s) ∪ {0} := by
  set α₁ : ℝ → ℂ := fun v => α (s + v.toNNReal) + Complex.I with hα₁
  have hc : ContinuousOn α₁ (Ici 0) :=
    ((hα.1.comp (continuous_const.add continuous_real_toNNReal)).add continuous_const).continuousOn
  have hi : InjOn α₁ (Ici 0) := by
    intro v hv w hw h
    have h1 : s + v.toNNReal = s + w.toNNReal := hα.2.1 (add_right_cancel h)
    have h2 : v.toNNReal = w.toNNReal := add_left_cancel h1
    exact (Real.toNNReal_eq_toNNReal_iff hv hw).1 h2
  have ht : Tendsto (fun v => ‖α₁ v‖) atTop atTop := by
    have h0 : Tendsto (fun v : ℝ => s + v.toNNReal) atTop atTop :=
      tendsto_atTop_mono (fun v => le_add_self) tendsto_real_toNNReal_atTop
    have h1 : Tendsto (fun v : ℝ => ‖α (s + v.toNNReal)‖ - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ (-1) (hα.2.2.2.2.comp h0)
    refine tendsto_atTop_mono (fun v => ?_) h1
    have := norm_sub_le (α (s + v.toNNReal) + Complex.I) Complex.I
    rw [add_sub_cancel_right, Complex.norm_I] at this
    show ‖α (s + v.toNNReal)‖ - 1 ≤ ‖α (s + v.toNNReal) + Complex.I‖
    linarith
  have hp : ∀ v ∈ Ici (0 : ℝ), α₁ v ≠ ((0 : ℝ) : ℂ) := by
    intro v _ h
    have h' := congrArg Complex.im h
    have hnn : (0 : ℝ) ≤ (α (s + v.toNNReal)).im := hα.2.2.2.1 _
    simp only [hα₁, Complex.add_im, Complex.I_im, Complex.ofReal_zero, Complex.zero_im] at h'
    linarith
  obtain ⟨b, hbc, hbi, hb0, hb1, hbim⟩ := Sec6.exists_compactArm hc hi ht hp
  have hpsi : ∀ v : ℝ, Sec6.psiMap 0 (α₁ v) = mu (α (s + v.toNNReal)) := fun v => by
    simp [Sec6.psiMap, mu, hα₁]
  refine ⟨b, hbc, hbi, by rw [hb0, hpsi]; simp, hb1, ?_⟩
  rw [hbim]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨v, -, rfl⟩, rfl⟩
    exact ⟨α (s + v.toNNReal), ⟨s + v.toNNReal, mem_Ici.2 le_self_add, rfl⟩, (hpsi v).symm⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    refine ⟨α₁ ((r - s : ℝ≥0) : ℝ), ⟨((r - s : ℝ≥0) : ℝ), mem_Ici.2 (NNReal.coe_nonneg _), rfl⟩, ?_⟩
    rw [hpsi, Real.toNNReal_coe, add_tsub_cancel_of_le (mem_Ici.1 hr)]

/-- **The pocket coordinate of the unbounded shaped pocket** (entry at `∞`). -/
theorem exists_isPocketCoord_of_unbounded {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR)
    (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) (hs₂ : s₂ = ⊤) {c : Chart}
    (hc : IsComponentChart (range αR) (range αL) C c) (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁))) :
    ∃ (ψ G : ℂ → ℂ) (k : ℝ), IsPocketCoord αR αL C c s₁ t₁ ∅ ψ G k ∧
      Tendsto G (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ) ∧
      Tendsto ψ (cobounded ℂ ⊓ 𝓟 (closure C)) (cobounded ℂ) := by
  -- the pocket
  obtain ⟨z₀, hz₀, -, -, hCz⟩ := id hC
  have hRc : IsClosed (range αR) := isClosed_range_of_isCompleteSimpleFlow hR
  have hLc : IsClosed (range αL) := isClosed_range_of_isCompleteSimpleFlow hL
  have hCo : IsOpen C := isOpen_of_mem_betweenComponents hRc hLc hC
  have hCc : IsPreconnected C := hCz ▸ isPreconnected_connectedComponentIn
  have hz₀C : z₀ ∈ C := hCz ▸ mem_connectedComponentIn hz₀
  have hCsub : C ⊆ H \ (range αR ∪ range αL) := hCz ▸ connectedComponentIn_subset _ _
  have hCH : C ⊆ H := fun z hz => (hCsub hz).1
  have hCF : ∀ z ∈ C, z ∉ range αR ∪ range αL := fun z hz => (hCsub hz).2
  have hCu : ¬ IsBounded C := hs.unbounded hs₂
  have hfr : frontier C ⊆ αR '' Ici s₁ ∪ αL '' Ici t₁ := hs.frontier_subset_Ici
  have h1 := hs.contact
  have hP := hs.mem_closure_exit
  have hinter := inter_subset_of_unboundedPocket hR hL hord h1 hCo hCc hCH hCu hz₀C hCF hfr hP
  set A := αR '' Ici s₁ with hA
  set B := αL '' Ici t₁ with hB
  set P := αR s₁ with hPdef
  have hPA : P ∈ A := ⟨s₁, mem_Ici.2 le_rfl, rfl⟩
  have hPB : P ∈ B := ⟨t₁, mem_Ici.2 le_rfl, h1.symm⟩
  have hAc : IsClosed A := Supp9B.isClosed_image ⟨hR.1, hR.2.1, hR.2.2.2.1, hR.2.2.2.2⟩ isClosed_Ici
  have hBc : IsClosed B := Supp9B.isClosed_image ⟨hL.1, hL.2.1, hL.2.2.2.1, hL.2.2.2.2⟩ isClosed_Ici
  have hJsub : A ∪ B ⊆ range αR ∪ range αL := union_subset_union (image_subset_range _ _) (image_subset_range _ _)
  have hPH : P ∈ Hbar := hR.2.2.2.1 s₁
  -- the Jordan curve `μ(A ∪ B) ∪ {0}`
  obtain ⟨b₁, hb₁c, hb₁i, hb₁0, hb₁1, hb₁im⟩ := exists_muArm hR s₁
  obtain ⟨b₂, hb₂c, hb₂i, hb₂0, hb₂1, hb₂im⟩ := exists_muArm hL t₁
  set Γ := b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 with hΓ
  have hΓJ : LQGMetric.JordanMap.IsJordanCurve Γ := by
    refine Sec7.isJordanCurve_image_union hb₁c hb₂c hb₁i hb₂i (by rw [hb₁0, hb₂0, ← h1])
      (by rw [hb₁1, hb₂1]) ?_
    rw [hb₁im, hb₂im, hb₁0, hb₁1]
    rintro w ⟨hw1 | hw1, hw2 | hw2⟩
    · obtain ⟨a, ha, rfl⟩ := hw1
      obtain ⟨b, hb, he⟩ := hw2
      have : b = a := mu_injective he
      rw [mem_singleton_iff.1 (hinter ⟨ha, this ▸ hb⟩)]
      exact Or.inl rfl
    · exact Or.inr hw2
    · exact Or.inr hw1
    · exact Or.inr hw1
  have hAH : ∀ z ∈ A ∪ B, z ∈ Hbar := by
    rintro _ (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩)
    exacts [hR.2.2.2.1 a, hL.2.2.2.1 a]
  have hΓeq : Γ = mu '' (A ∪ B) ∪ {0} := by
    rw [hΓ, hb₁im, hb₂im, image_union]
    ext w; simp only [mem_union, mem_singleton_iff]; tauto
  -- the bounded domain `μ(C)`
  set C' := mu '' C with hC'
  have hCH' : C ⊆ Hbar := fun z hz => mem_Hbar_of_mem_H (hCH hz)
  have hC'o : IsOpen C' := isOpen_mu_image hCo hCH
  have hC'c : IsPreconnected C' := hCc.image _ (continuousOn_mu_Hbar.mono hCH')
  have hC'b : IsBounded C' := by
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact mem_closedBall_zero_iff.2 (norm_mu_le_one (hCH' hz))
  have hC'Γ : ∀ w ∈ C', w ∉ Γ := by
    rintro _ ⟨z, hz, rfl⟩ hw
    rw [hΓeq] at hw
    rcases hw with ⟨a, ha, he⟩ | h0
    · exact hCF z hz (hJsub (mu_injective he ▸ ha))
    · exact mu_ne_zero_of_mem_Hbar (hCH' hz) (mem_singleton_iff.1 h0)
  have hfr' : frontier C' ⊆ Γ := by
    refine (frontier_mu_image_subset hCo hCH).trans ?_
    rw [hΓeq]
    exact union_subset_union (image_mono hfr) le_rfl
  have hCeq : connectedComponentIn Γᶜ (mu z₀) = C' :=
    eq_connectedComponentIn_of_frontier_subset hC'o hC'c (mem_image_of_mem mu hz₀C) hC'Γ hfr'
  have h0Γ : (0 : ℂ) ∈ Γ := by rw [hΓeq]; exact Or.inr rfl
  have hPΓ : mu P ∈ Γ := by rw [hΓeq]; exact Or.inl ⟨P, Or.inl hPA, rfl⟩
  obtain ⟨ψ', G', hψc, hψm', hGc', hGm, hGψ, hψG, hconf, hreal, hψP, hψ0⟩ :=
    Sec6.exists_jordanCoord hΓJ (p := mu z₀) (hC'Γ _ (mem_image_of_mem mu hz₀C)) (by rw [hCeq]; exact hC'b)
      h0Γ hPΓ
  rw [hCeq] at hψc hψm' hGm hGψ hconf hψ0
  have hPcl : mu P ∈ closure C' :=
    (continuousAt_mu fun h => neg_I_notMem_Hbar (h ▸ hPH)).continuousWithinAt.mem_closure_image hP
  have hP0 : mu P ≠ 0 := mu_ne_zero_of_mem_Hbar hPH
  have hG'0 : G' 0 = mu P := by rw [← hψP]; exact hGψ _ ⟨hPcl, hP0⟩
  have hG'i : InjOn G' Hbar := fun w hw w' hw' h => by rw [← hψG w hw, ← hψG w' hw', h]
  have hG'fr : ∀ w ∈ Hbar, G' w ∉ C' → G' w ∈ frontier C' := fun w hw hn =>
    ⟨(hGm hw).1, by rw [hC'o.interior_eq]; exact hn⟩
  have hG'C' : ∀ w ∈ H, G' w ∈ C' := by
    intro w hw
    by_contra hn
    have him := hreal (G' w) ⟨hfr' (hG'fr w (H_subset_Hbar hw) hn), (hGm (H_subset_Hbar hw)).2⟩
    rw [hψG w (H_subset_Hbar hw)] at him
    exact absurd him (ne_of_gt hw)
  -- the coordinate `ψ = ψ' ∘ μ` of `C` and its extended inverse `G = μ⁻¹ ∘ G'`
  set ψ : ℂ → ℂ := fun z => ψ' (mu z) with hψdef
  set G : ℂ → ℂ := fun w => muInv (G' w) with hGdef
  have hmuC : MapsTo mu C C' := fun z hz => mem_image_of_mem mu hz
  have hψd : DifferentiableOn ℂ ψ C := by
    refine hconf.1.comp (fun z hz => ?_) hmuC
    have h : z + Complex.I ≠ 0 := fun h => neg_I_notMem_Hbar ((by linear_combination h : z = -Complex.I) ▸ hCH' hz)
    exact (((differentiableAt_id.add_const Complex.I).inv h).neg).differentiableWithinAt
  have hψC : MapsTo ψ C H := fun z hz => hconf.2.1 (hmuC hz)
  have hGψ' : ∀ z ∈ C, G (ψ z) = z := fun z hz => by
    simp only [hψdef, hGdef]
    rw [hGψ _ ⟨subset_closure (hmuC hz), mu_ne_zero_of_mem_Hbar (hCH' hz)⟩, muInv_mu]
  have hψG' : ∀ w ∈ H, ψ (G w) = w := fun w hw => by
    simp only [hψdef, hGdef, mu_muInv]
    exact hψG w (H_subset_Hbar hw)
  have hGH : MapsTo G H C := by
    intro w hw
    obtain ⟨z, hz, he⟩ := hG'C' w hw
    simp only [hGdef, ← he, muInv_mu]
    exact hz
  have hGc : ContinuousOn G Hbar :=
    continuousOn_muInv.comp hGc' fun w hw => (hGm hw).2
  have hGi : InjOn G Hbar := fun w hw w' hw' h => by
    have : G' w = G' w' := by
      have := congrArg mu h
      simpa only [hGdef, mu_muInv] using this
    exact hG'i hw hw' this
  have hG0 : G 0 = P := by simp only [hGdef, hG'0, muInv_mu]
  have hGr : ∀ r : ℝ, r ≠ 0 → G r ∈ (A \ B) ∪ (B \ A) := by
    intro r hr
    have hrC : G' r ∉ C' := fun h => by
      have := hconf.2.1 h
      rw [hψG r (ofReal_mem_Hbar r)] at this
      exact absurd (show (0 : ℝ) < (r : ℂ).im from this) (by simp)
    have hfrr := frontier_mu_image_subset hCo hCH (hG'fr r (ofReal_mem_Hbar r) hrC)
    rcases hfrr with ⟨z, hz, he⟩ | h0
    · have hGz : G r = z := by simp only [hGdef, ← he, muInv_mu]
      have hrP : z ≠ P := fun h => hr (Complex.ofReal_eq_zero.1
        (hGi (ofReal_mem_Hbar r) (by simpa using ofReal_mem_Hbar 0) (by rw [hGz, h, hG0])))
      rw [hGz]
      rcases hfr hz with h | h
      · exact Or.inl ⟨h, fun hB' => hrP (mem_singleton_iff.1 (hinter ⟨h, hB'⟩))⟩
      · exact Or.inr ⟨h, fun hA' => hrP (mem_singleton_iff.1 (hinter ⟨hA', h⟩))⟩
    · exact absurd (mem_singleton_iff.1 h0) (hGm (ofReal_mem_Hbar r)).2
  have hAL : ∀ z ∈ A \ B, z ∉ range αL := by
    rintro _ ⟨⟨m, hm, rfl⟩, hnB⟩ ⟨m'', he⟩
    rcases eq_or_lt_of_le (mem_Ici.1 hm) with h | h
    · exact hnB (h ▸ hPB)
    exact hnB ⟨m'', mem_Ici.2 ((hord s₁ m t₁ m'' h1 he.symm).1 h).le, he⟩
  have hBR : ∀ z ∈ B \ A, z ∉ range αR := by
    rintro _ ⟨⟨m, hm, rfl⟩, hnA⟩ ⟨m'', he⟩
    rcases eq_or_lt_of_le (mem_Ici.1 hm) with h | h
    · exact hnA (by rw [← h, ← h1]; exact hPA)
    exact hnA ⟨m'', mem_Ici.2 ((hord s₁ m'' t₁ m h1 he).2 h).le, he⟩
  -- `G → ∞` at `∞`
  have hG'inf : Tendsto G' (cobounded ℂ ⊓ 𝓟 H) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨GW3.tendsto_cobounded_of_coord hC'b hψc hψG hGm,
      mem_inf_of_right (mem_principal.2 fun w hw => (hGm (H_subset_Hbar hw)).2)⟩
  have hGinf : Tendsto G (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ) := by
    have h := (tendsto_affine_cobounded (α := (-1 : ℂ)) (β := -Complex.I) (by norm_num)).comp
      (tendsto_inv₀_nhdsNE_zero.comp hG'inf)
    refine h.congr fun w => ?_
    simp only [Function.comp_apply, hGdef, muInv]
    ring
  obtain ⟨k, hk, hcG, hGpos, hGneg⟩ := exists_dilation_of_extInv hc hCo hψd hψC hGψ' hψG' hGH hGc hGi
    hAc hBc hGr hAL hBR (by rw [hG0]; exact hxC) hGinf (disjoint_cobounded_nhds _)
  -- the closed pocket
  have hclH : closure C ⊆ Hbar := closure_minimal hCH' QuantumZipper.isClosed_Hbar
  have hmucl : ∀ z ∈ closure C, mu z ∈ closure C' \ {0} := fun z hz =>
    ⟨(continuousAt_mu fun h => neg_I_notMem_Hbar (h ▸ hclH hz)).continuousWithinAt.mem_closure_image hz,
      mu_ne_zero_of_mem_Hbar (hclH hz)⟩
  have hGm' : MapsTo G Hbar (closure C \ ∅) := by
    intro w hw
    have h1 := hGm hw
    have h2 : G' w ∈ mu '' closure C ∪ {0} :=
      closure_mu_image_subset isClosed_closure (closure_mono (image_mono subset_closure) h1.1)
    rcases h2 with ⟨z, hz, he⟩ | h0
    · rw [sdiff_empty]
      simp only [hGdef, ← he, muInv_mu]
      exact hz
    · exact absurd (mem_singleton_iff.1 h0) h1.2
  have hψ'' : ∀ z ∈ closure C \ ∅, G (ψ z) = z := fun z hz => by
    simp only [hψdef, hGdef]
    rw [hGψ _ (hmucl z hz.1), muInv_mu]
  have hψc' : ContinuousOn ψ (closure C \ ∅) := by
    rw [sdiff_empty]
    exact hψc.comp (continuousOn_mu_Hbar.mono hclH) fun z hz => hmucl z hz
  have hψm'' : MapsTo ψ (closure C \ ∅) Hbar := fun z hz => hψm' (hmucl z hz.1)
  have hψinf : Tendsto ψ (cobounded ℂ ⊓ 𝓟 (closure C)) (cobounded ℂ) := by
    have h1 : Tendsto mu (cobounded ℂ ⊓ 𝓟 (closure C)) (𝓝[closure C' \ {0}] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_mu_cobounded.mono_left inf_le_left,
        mem_inf_of_right (mem_principal.2 fun z hz => hmucl z hz)⟩
    exact hψ0.comp h1
  refine ⟨ψ, G, k, ⟨hk, hcG, hGc, hGm', fun w hw => ?_, hψ'', hψc', hψm'', hG0, fun r hr => ?_,
    fun r hr => ?_⟩, hGinf, hψinf⟩
  · simp only [hψdef, hGdef, mu_muInv]
    exact hψG w hw
  · obtain ⟨⟨m, hm, he⟩, hnB⟩ := hGpos r hr
    refine ⟨m, lt_of_le_of_ne (mem_Ici.1 hm) fun h => hnB ?_, he⟩
    rw [← he, ← h]; exact hPB
  · obtain ⟨⟨m, hm, he⟩, hnA⟩ := hGneg r hr
    refine ⟨m, lt_of_le_of_ne (mem_Ici.1 hm) fun h => hnA ?_, he⟩
    rw [← he, ← h, ← h1]; exact hPA

/-- **The boundary correspondence of the unbounded shaped pocket.** -/
theorem exists_chartBdryCorr_of_unbounded {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR)
    (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) (hs₂ : s₂ = ⊤) {c : Chart}
    (hc : IsComponentChart (range αR) (range αL) C c) (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁))) :
    ∃ (e : ℝ → ℂ) (rR rL : ℝ → ℝ≥0), ChartBdryCorr αR αL c s₂ e rR rL := by
  obtain ⟨ψ, G, k, hpc, hGinf, -⟩ := exists_isPocketCoord_of_unbounded hR hL hord hC hs hs₂ hc hxC
  have he₀ : Tendsto (fun w => -(G w)⁻¹) (cobounded ℂ ⊓ 𝓟 H) (𝓝 0) := by
    simpa using (tendsto_inv₀_cobounded.comp hGinf).neg
  exact chartBdryCorr_of_dilation hR hL hpc.pos hpc.inv_eq hpc.continuousOn_G hpc.injOn_G hpc.G_zero hs.contact
    hpc.pos_arc hpc.neg_arc he₀ ⟨fun _ => rfl, fun h => absurd hs₂ h⟩

/-! ### `GB11ChartBdryStatement` -/

/-- **`GB11ChartBdryStatement` is proved** (PROVE-T14-GW4T4's named input; deterministic): every component chart of a
shaped pocket between GB11's barrier walls, with its exit at `0`, has the boundary correspondence `ChartBdryCorr`.
Only the walls' part of the barrier input is used (complete simple flows, same contact order). -/
theorem gb11ChartBdryStatement : GB11ChartBdryStatement := by
  intro W' γ _ _ _ _ αR αL hB _ C hC s₁ t₁ s₂ t₂ hs c hc hxC
  by_cases hs₂ : s₂ = ⊤
  · exact exists_chartBdryCorr_of_unbounded hB.1 hB.2.1 hB.2.2.1 hC hs hs₂ hc hxC
  · exact exists_chartBdryCorr_of_bounded hB.1 hB.2.1 hB.2.2.1 hC hs hs₂ hc hxC

/-- **`GB11RelConnGrowthStatement` from the local growth alone** (the boundary correspondence is now proved). -/
theorem gb11RelConnGrowthStatement_of_localGrowth (hgr : GB11RelLocalGrowthStatement) :
    GW4Reg.GB11RelConnGrowthStatement :=
  gb11RelConnGrowthStatement_of_bdry gb11ChartBdryStatement hgr

/-- **`GB11RelParamStatement` from the local growth alone.** -/
theorem gb11RelParamStatement_of_localGrowth (hgr : GB11RelLocalGrowthStatement) :
    GW4Reg.GB11RelParamStatement :=
  gb11RelParamStatement_of_bdry gb11ChartBdryStatement hgr

end GB11Chart

end Theorem14

end InteractingSLE
