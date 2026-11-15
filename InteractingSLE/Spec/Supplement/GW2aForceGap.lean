/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aForceAbel
import InteractingSLE.Stochastic.Bessel.Uniqueness

/-!
# The nearest right force gap dominates a Bessel path on a final interval before a collision

Packet PROVE-GW2A-FORCE (input of `FlowFixedTimeInteriorStatement`). Deterministic, one integrated path at a time.

Let `Z = v^{0,R} − w` be the nearest right gap of an integrated `SLE_κ(ρ)` path. On an interval `[a, t]` before the
lifetime on which
* the marks `j ≥ m` and all left marks stay at distance `≥ δ` from the driver,
* the gap stays below `ε`, with `ε M ≤ c₀/2` for `M = (∑|ρ^R| + ∑|ρ^L|)/δ`,
* every *break* `k < m` of the first `m` right marks at time `a` (the last one, or a mark not merged with the next one)
  has `2 + S_k ≥ c₀ > 0` (`S_k` the partial sums of the right weights),

the drift of `Z` is at least `c₀/(2Z)` (`le_gapDrift`, by the Abel bound `le_sum_div_of_breaks_fin` and the
permanence of merges `vR_eq_vR_of_eq`). The comparison principle then puts `√κ X` below `Z` on `[a, t]`, where `X` is
the Bessel path with coefficient `c₀/(2κ)` started at `0` and driven by `s ↦ −(b(a+s) − b(a))`
(`bessel_mul_sqrt_le_gap`). In particular a collision `Z(t) = 0` forces `X(t − a) = 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2aForce

open Sec2

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The drift of the nearest right gap `v^{0,R} − w` at real time `r`. -/
def gapDrift (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (j₀ : Fin nR) (r : ℝ) : ℝ :=
  2 / (vR j₀ r.toNNReal - w r.toNNReal) - driverDrift ρL ρR w vL vR r

/-- The constant bounding the drift of the separated marks. -/
def sepConst (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (δ : ℝ) : ℝ := (∑ j, |ρR j| + ∑ i, |ρL i|) / δ

/-! ### The drift bound at one time -/

/-- A weight over a gap at least `δ` contributes at least `−|ρ|/δ`. -/
theorem neg_abs_div_le_div {ρ x δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) : -(|ρ| / δ) ≤ ρ / x := by
  have hx0 : 0 < x := hδ.trans_le hx
  have h1 : |ρ / x| ≤ |ρ| / δ := by
    rw [abs_div, abs_of_pos hx0]
    exact div_le_div_of_nonneg_left (abs_nonneg ρ) hδ hx
  linarith [neg_abs_le (ρ / x)]

/-- **The drift of the nearest gap near a collision** at a time `τ` (deterministic): with the separated marks at
distance `≥ δ`, the Abel conditions at the breaks of the first `m` right marks, and a small gap `Z < ε`,
the drift `2/Z − (drift of w)` is at least `c₀ / (2 Z)`. -/
theorem le_gapDrift (hp : IsForcePath xL xR ρL ρR w vL vR ζ) {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < ζ) (hnR : 0 < nR)
    {m : ℕ} (hm : 0 < m) (hmn : m ≤ nR) {ε δ c₀ : ℝ} (hδ : 0 < δ) (hεM : ε * sepConst ρL ρR δ ≤ c₀ / 2)
    (hZ : 0 < vR ⟨0, hnR⟩ τ - w τ) (hsmall : vR ⟨0, hnR⟩ τ - w τ < ε)
    (hfar : ∀ j : Fin nR, m ≤ j.val → δ ≤ vR j τ - w τ) (hleft : ∀ i, δ ≤ w τ - vL i τ)
    (habel : ∀ k : Fin nR, k.val < m → (k.val + 1 = m ∨ ∀ k' : Fin nR, k'.val = k.val + 1 → vR k τ < vR k' τ) →
      c₀ - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin nR => i ≤ k), ρR i) :
    c₀ / (2 * (vR ⟨0, hnR⟩ τ - w τ)) ≤ gapDrift ρL ρR w vL vR ⟨0, hnR⟩ (τ : ℝ) := by
  set Z := vR ⟨0, hnR⟩ τ - w τ with hZdef
  have hτr : ((τ : ℝ)).toNNReal = τ := Real.toNNReal_coe
  simp only [gapDrift, driverDrift, hτr]
  -- the right drift, split into the first `m` marks and the separated ones
  have hR : -(∑ j, ρR j / (w τ - vR j τ)) = ∑ j, ρR j / (vR j τ - w τ) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← neg_sub (vR j τ) (w τ), div_neg, neg_neg]
  have hsplit := sum_filter_add_sum_filter_not univ (fun j : Fin nR => j.val < m)
    (fun j => ρR j / (vR j τ - w τ))
  -- Abel on the first `m` marks
  have hnear : (c₀ - 2) / Z ≤ ∑ j ∈ univ.filter (fun j : Fin nR => j.val < m), ρR j / (vR j τ - w τ) := by
    refine le_sum_div_of_breaks_fin ρR (fun j => vR j τ - w τ) (c₀ - 2) hm hmn (fun j _ => ?_)
      (fun i j hij _ => sub_le_sub_right (hp.monotone_vR hτ hij) _) (fun k hk hbr => habel k hk ?_)
    · exact hZ.trans_le (sub_le_sub_right (hp.monotone_vR hτ (by rw [Fin.le_def]; exact Nat.zero_le _)) _)
    · rcases hbr with h | h
      · exact Or.inl h
      · exact Or.inr fun k' hk' => by have := h k' hk'; linarith
  -- the separated right marks
  have hfar' : -(∑ j, |ρR j|) / δ ≤
      ∑ j ∈ univ.filter (fun j : Fin nR => ¬ j.val < m), ρR j / (vR j τ - w τ) := by
    calc -(∑ j, |ρR j|) / δ ≤ -(∑ j ∈ univ.filter (fun j : Fin nR => ¬ j.val < m), |ρR j|) / δ := by
          refine div_le_div_of_nonneg_right (neg_le_neg ?_) hδ.le
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => abs_nonneg (ρR j)
      _ = ∑ j ∈ univ.filter (fun j : Fin nR => ¬ j.val < m), -(|ρR j| / δ) := by
          rw [neg_div, sum_div, ← sum_neg_distrib]
      _ ≤ _ := sum_le_sum fun j hj => neg_abs_div_le_div hδ (hfar j (by
          have := (mem_filter.1 hj).2; omega))
  -- the left marks
  have hleft' : -(∑ i, |ρL i|) / δ ≤ -(∑ i, ρL i / (w τ - vL i τ)) := by
    rw [neg_div, neg_le_neg_iff, sum_div]
    refine sum_le_sum fun i _ => ?_
    have := neg_abs_div_le_div (ρ := -ρL i) hδ (hleft i)
    rw [abs_neg, neg_div] at this
    linarith
  -- assembly
  have hM : sepConst ρL ρR δ * Z ≤ c₀ / 2 := by
    have hM0 : 0 ≤ sepConst ρL ρR δ := div_nonneg (add_nonneg (sum_nonneg fun j _ => abs_nonneg _)
      (sum_nonneg fun i _ => abs_nonneg _)) hδ.le
    nlinarith
  have hsum : 2 / Z - (∑ i, ρL i / (w τ - vL i τ) + ∑ j, ρR j / (w τ - vR j τ)) =
      2 / Z + (-(∑ i, ρL i / (w τ - vL i τ))) + (∑ j ∈ univ.filter (fun j : Fin nR => j.val < m),
        ρR j / (vR j τ - w τ) + ∑ j ∈ univ.filter (fun j : Fin nR => ¬ j.val < m), ρR j / (vR j τ - w τ)) := by
    rw [hsplit, ← hR]; ring
  rw [hsum]
  have hsc : sepConst ρL ρR δ = (∑ j, |ρR j|) / δ + (∑ i, |ρL i|) / δ := by
    rw [sepConst, add_div]
  have h2Z : 2 / Z + (c₀ - 2) / Z = c₀ / Z := by rw [← add_div]; ring_nf
  have hfin : c₀ / (2 * Z) = c₀ / Z - c₀ / (2 * Z) := by field_simp; ring
  have hcZ : sepConst ρL ρR δ ≤ c₀ / (2 * Z) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  rw [hsc] at hcZ
  rw [neg_div] at hfar' hleft'
  linarith

/-! ### The integrated equation of the nearest gap -/

/-- The drift of the nearest gap is interval integrable on `[0, t]`, `t < ζ`. -/
theorem intervalIntegrable_gapDrift (hp : IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (j₀ : Fin nR) : IntervalIntegrable (gapDrift ρL ρR w vL vR j₀) volume 0 t :=
  (hp.intervalIntegrable_forceR ht j₀).sub (hp.intervalIntegrable_driverDrift ht)

/-- **The increment of the nearest gap**: `Z_τ − Z_a = −√κ (b_τ − b_a) + ∫ₐ^τ (drift)`. -/
theorem gap_sub (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {a τ : ℝ≥0} (haτ : a ≤ τ)
    (hτ : (τ : ℝ≥0∞) < ζ) (j₀ : Fin nR) :
    (vR j₀ τ - w τ) - (vR j₀ a - w a) =
      -(Real.sqrt κ * (b τ - b a)) + ∫ r in (a : ℝ)..τ, gapDrift ρL ρR w vL vR j₀ r := by
  have hf := hp.isForcePath
  have haτ' : (a : ℝ) ≤ τ := by exact_mod_cast haτ
  have hsub : uIcc (a : ℝ) τ ⊆ uIcc 0 (τ : ℝ) := by
    rw [uIcc_of_le haτ', uIcc_of_le (NNReal.coe_nonneg τ)]
    exact Icc_subset_Icc (NNReal.coe_nonneg a) le_rfl
  have h1 := hf.vR_sub haτ hτ j₀
  have h2 := hf.w_sub hp.driverEq haτ hτ
  have hI : ∫ r in (a : ℝ)..τ, gapDrift ρL ρR w vL vR j₀ r =
      (∫ r in (a : ℝ)..τ, 2 / (vR j₀ r.toNNReal - w r.toNNReal)) -
        ∫ r in (a : ℝ)..τ, driverDrift ρL ρR w vL vR r :=
    intervalIntegral.integral_sub ((hf.intervalIntegrable_forceR hτ j₀).mono_set hsub)
      ((hf.intervalIntegrable_driverDrift hτ).mono_set hsub)
  rw [hI]
  linarith

/-! ### Comparison with a Bessel path -/

/-- `c₀/(2κ) / (Z/√κ) = c₀/(2Z) / √κ`. -/
theorem div_div_sqrt_eq (c₀ : ℝ) {κ Z : ℝ} (hκ : 0 < κ) (hZ : 0 < Z) :
    c₀ / (2 * κ) / (Z / Real.sqrt κ) = c₀ / (2 * Z) / Real.sqrt κ := by
  have h := Real.mul_self_sqrt hκ.le
  have hs := Real.sqrt_pos.2 hκ
  have e1 : c₀ / (2 * Z) / Real.sqrt κ = c₀ * Real.sqrt κ / (2 * Z * (Real.sqrt κ * Real.sqrt κ)) := by
    field_simp
  rw [h] at e1
  rw [e1]
  field_simp

/-- `(a + s.toNNReal : ℝ) = a + s` for `s ≥ 0`. -/
theorem coe_add_toNNReal (a : ℝ≥0) {s : ℝ} (hs : 0 ≤ s) : ((a + s.toNNReal : ℝ≥0) : ℝ) = a + s := by
  rw [NNReal.coe_add, Real.coe_toNNReal _ hs]

/-- **The nearest right gap dominates `√κ` times a Bessel path on a final interval before a collision.** With the
separated marks at distance `≥ δ`, the gap below `ε` (`ε M ≤ c₀/2`) and the Abel conditions at the breaks at time
`a`, on `[a, t]` (`t < ζ`), the Bessel path `X` with coefficient `c₀/(2κ)` from `0` driven by
`s ↦ −(b(a+s) − b(a))` satisfies `√κ X(s) ≤ Z(a + s)`; at `s = t − a` this reads `X(t − a) √κ ≤ Z(t)`. -/
theorem bessel_mul_sqrt_le_gap (hκ : 0 < κ) (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {a t : ℝ≥0}
    (hat : a ≤ t) (htζ : (t : ℝ≥0∞) < ζ) (hnR : 0 < nR) {m : ℕ} (hm : 0 < m) (hmn : m ≤ nR) {ε δ c₀ : ℝ}
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hεM : ε * sepConst ρL ρR δ ≤ c₀ / 2)
    (hfar : ∀ τ : ℝ≥0, a ≤ τ → τ ≤ t → ∀ j : Fin nR, m ≤ j.val → δ ≤ vR j τ - w τ)
    (hleft : ∀ τ : ℝ≥0, a ≤ τ → τ ≤ t → ∀ i, δ ≤ w τ - vL i τ)
    (hsmall : ∀ τ : ℝ≥0, a ≤ τ → τ ≤ t → vR ⟨0, hnR⟩ τ - w τ < ε)
    (habel : ∀ k : Fin nR, k.val < m →
      (k.val + 1 = m ∨ ∀ k' : Fin nR, k'.val = k.val + 1 → vR k a < vR k' a) →
        c₀ - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin nR => i ≤ k), ρR i)
    {X : ℝ≥0 → ℝ} (hX : Bessel.IsBesselPath (c₀ / (2 * κ)) 0 (fun s => -(b (a + s) - b a)) X) :
    X (t - a) * Real.sqrt κ ≤ vR ⟨0, hnR⟩ t - w t := by
  have hf := hp.isForcePath
  set j₀ : Fin nR := ⟨0, hnR⟩ with hj₀
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  set c : ℝ := c₀ / (2 * κ) with hc
  have hcpos : 0 < c := div_pos hc₀ (by positivity)
  -- times `a + s` for `s ∈ [0, T]`
  have hτle : ∀ s ∈ Icc (0 : ℝ) ((t : ℝ) - a), a + s.toNNReal ≤ t := fun s hs => by
    rw [← NNReal.coe_le_coe, coe_add_toNNReal a hs.1]; linarith [hs.2]
  have hτζ : ∀ s ∈ Icc (0 : ℝ) ((t : ℝ) - a), ((a + s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hτle s hs) htζ
  -- the shifted gap and the drift
  set Y : ℝ → ℝ := fun s => (vR j₀ (a + s.toNNReal) - w (a + s.toNNReal)) / Real.sqrt κ with hY
  set hfun : ℝ → ℝ := fun s => gapDrift ρL ρR w vL vR j₀ ((a : ℝ) + s) / Real.sqrt κ with hhfun
  set Xr : ℝ → ℝ := fun s => X s.toNNReal with hXr
  set ffun : ℝ → ℝ := fun s => c / X s.toNNReal with hffun
  -- continuity
  have hYc : ContinuousOn Y (Icc 0 ((t : ℝ) - a)) := by
    have hcont : ContinuousOn (fun s : ℝ => a + s.toNNReal) (Icc 0 ((t : ℝ) - a)) :=
      (continuous_const.add continuous_real_toNNReal).continuousOn
    have hmap : MapsTo (fun s : ℝ => a + s.toNNReal) (Icc 0 ((t : ℝ) - a)) {τ : ℝ≥0 | (τ : ℝ≥0∞) < ζ} :=
      fun s hs => hτζ s hs
    exact (((hf.continuousOn_vR j₀).comp hcont hmap).sub (hf.continuousOn_w.comp hcont hmap)).div_const _
  have hXc : ContinuousOn Xr (Icc 0 ((t : ℝ) - a)) := (hX.1.comp continuous_real_toNNReal).continuousOn
  -- integrability
  have hfi : IntervalIntegrable ffun volume 0 ((t : ℝ) - a) := by
    have := hX.intervalIntegrable_div (t - a)
    rwa [NNReal.coe_sub hat] at this
  have hgi : IntervalIntegrable (gapDrift ρL ρR w vL vR j₀) volume a t :=
    (intervalIntegrable_gapDrift hf htζ j₀).mono_set (by
      rw [uIcc_of_le (by exact_mod_cast hat : (a : ℝ) ≤ t), uIcc_of_le (NNReal.coe_nonneg t)]
      exact Icc_subset_Icc (NNReal.coe_nonneg a) le_rfl)
  have hhi : IntervalIntegrable hfun volume 0 ((t : ℝ) - a) := by
    have := (hgi.comp_add_left (a : ℝ)).div_const (Real.sqrt κ)
    rwa [sub_self] at this
  -- the identity for `Y`
  have hYeq : ∀ s ∈ Icc (0 : ℝ) ((t : ℝ) - a), Y s - Y 0 = -(b (a + s.toNNReal) - b a) + ∫ r in (0 : ℝ)..s, hfun r := by
    intro s hs
    have hkey := gap_sub hp (le_self_add : a ≤ a + s.toNNReal) (hτζ s hs) j₀
    have hshift : ∫ r in (a : ℝ)..((a + s.toNNReal : ℝ≥0) : ℝ), gapDrift ρL ρR w vL vR j₀ r =
        ∫ r in (0 : ℝ)..s, gapDrift ρL ρR w vL vR j₀ ((a : ℝ) + r) := by
      rw [intervalIntegral.integral_comp_add_left, add_zero, coe_add_toNNReal a hs.1]
    rw [hshift] at hkey
    simp only [hY, hhfun, Real.toNNReal_zero, add_zero]
    rw [intervalIntegral.integral_div, ← sub_div, hkey]
    field_simp
  -- the Bessel equation for `Xr`
  have hX0 : Xr 0 = 0 := by
    simp only [hXr, Real.toNNReal_zero]
    rw [hX.2.2.2.2 0]
    simp
  have hXeq : ∀ s ∈ Icc (0 : ℝ) ((t : ℝ) - a), Xr s = -(b (a + s.toNNReal) - b a) + ∫ r in (0 : ℝ)..s, ffun r := by
    intro s hs
    simp only [hXr, hffun]
    rw [hX.2.2.2.2 s.toNNReal, Real.coe_toNNReal _ hs.1, zero_add]
  have hsub : ∀ s ∈ Icc (0 : ℝ) ((t : ℝ) - a), uIcc 0 s ⊆ uIcc 0 ((t : ℝ) - a) := fun s hs => by
    rw [uIcc_of_le hs.1, uIcc_of_le (hs.1.trans hs.2)]
    exact Icc_subset_Icc le_rfl hs.2
  have heq : ∀ s ∈ Icc (0 : ℝ) ((t : ℝ) - a), Xr s - Y s = Xr 0 - Y 0 + ∫ r in (0 : ℝ)..s, (ffun r - hfun r) := by
    intro s hs
    rw [intervalIntegral.integral_sub (hfi.mono_set (hsub s hs)) (hhi.mono_set (hsub s hs)), hXeq s hs, hX0]
    have := hYeq s hs
    linarith
  have h0 : Xr 0 ≤ Y 0 := by
    rw [hX0]
    simp only [hY, Real.toNNReal_zero, add_zero]
    exact div_nonneg (sub_nonneg.2 (hf.w_le_vR (lt_of_le_of_lt (by exact_mod_cast hat) htζ) j₀)) hsκ.le
  -- the drift inequality almost everywhere
  have hnull := hf.volume_collisionR j₀
  have hnull' : volume ((fun s : ℝ => (a : ℝ) + s) ⁻¹'
      {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < ζ ∧ w r.toNNReal = vR j₀ r.toNNReal}) = 0 := by
    rw [measure_preimage_add]; exact hnull
  have hmono : ∀ᵐ s ∂volume, s ∈ Icc (0 : ℝ) ((t : ℝ) - a) → Y s < Xr s → ffun s ≤ hfun s := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull'] with s hns hs hlt
    set τ : ℝ≥0 := a + s.toNNReal with hτdef
    have hτr : ((a : ℝ) + s).toNNReal = τ :=
      NNReal.eq (by rw [Real.coe_toNNReal _ (add_nonneg (NNReal.coe_nonneg a) hs.1), coe_add_toNNReal a hs.1])
    have hτζ' := hτζ s hs
    have haτ : a ≤ τ := le_self_add
    have hτt := hτle s hs
    have hne : w τ ≠ vR j₀ τ := fun he => hns ⟨add_nonneg (NNReal.coe_nonneg a) hs.1, by rwa [hτr],
      by rw [hτr]; exact he⟩
    have hZ : 0 < vR j₀ τ - w τ := sub_pos.2 (lt_of_le_of_ne (hf.w_le_vR hτζ' j₀) hne)
    have hYs : Y s = (vR j₀ τ - w τ) / Real.sqrt κ := rfl
    have hYpos : 0 < Y s := by rw [hYs]; exact div_pos hZ hsκ
    -- the Abel conditions at `τ`
    have habel' : ∀ k : Fin nR, k.val < m →
        (k.val + 1 = m ∨ ∀ k' : Fin nR, k'.val = k.val + 1 → vR k τ < vR k' τ) →
          c₀ - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin nR => i ≤ k), ρR i := by
      intro k hk hbr
      refine habel k hk ?_
      rcases hbr with h | h
      · exact Or.inl h
      · refine Or.inr fun k' hk' => ?_
        have hkk' : k ≤ k' := by rw [Fin.le_def]; omega
        have hle := hf.monotone_vR (lt_of_le_of_lt (by exact_mod_cast haτ) hτζ') hkk'
        refine lt_of_le_of_ne hle fun he => ?_
        have := hf.vR_eq_vR_of_eq haτ hτζ' hkk' he
        exact absurd (h k' hk') (by rw [this]; exact lt_irrefl _)
    have hD := le_gapDrift hf hτζ' hnR hm hmn hδ hεM hZ (hsmall τ haτ hτt) (hfar τ haτ hτt)
      (hleft τ haτ hτt) habel'
    have hτc : ((τ : ℝ≥0) : ℝ) = (a : ℝ) + s := coe_add_toNNReal a hs.1
    rw [hτc] at hD
    have hXpos : 0 < Xr s := hYpos.trans hlt
    calc ffun s = c / Xr s := rfl
      _ ≤ c / Y s := div_le_div_of_nonneg_left hcpos.le hYpos hlt.le
      _ = c₀ / (2 * (vR j₀ τ - w τ)) / Real.sqrt κ := by
          rw [hYs, hc]
          exact div_div_sqrt_eq c₀ hκ hZ
      _ ≤ hfun s := div_le_div_of_nonneg_right hD hsκ.le
  -- comparison
  have hT0 : (0 : ℝ) ≤ (t : ℝ) - a := sub_nonneg.2 (by exact_mod_cast hat)
  have hcmp := Bessel.le_of_sub_eq_integral hXc hYc hfi hhi h0 heq hmono ((t : ℝ) - a) ⟨hT0, le_rfl⟩
  have hTn : ((t : ℝ) - a).toNNReal = t - a := by
    rw [← NNReal.coe_sub hat, Real.toNNReal_coe]
  have hat' : a + ((t : ℝ) - a).toNNReal = t := by rw [hTn, add_tsub_cancel_of_le hat]
  simp only [hXr, hY, hTn] at hcmp
  rw [add_tsub_cancel_of_le hat] at hcmp
  calc X (t - a) * Real.sqrt κ ≤ (vR j₀ t - w t) / Real.sqrt κ * Real.sqrt κ :=
        mul_le_mul_of_nonneg_right hcmp hsκ.le
    _ = vR j₀ t - w t := div_mul_cancel₀ _ hsκ.ne'

end GW2aForce

end Theorem14

end InteractingSLE
