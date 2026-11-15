/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Aux25Hit
import InteractingSLE.Spec.Sec4.Aux25Path
import InteractingSLE.Spec.Sec2.OneForceLip
import InteractingSLE.Spec.Dimension.FiniteGirsanov

/-!
# Aux. lemma 25: identifying the endpoint case with a hit of the tamed process (pathwise)

Packet PROVE-AUX25. Along one path in the endpoint case of `NoRightEndpoint` (at a restart time `r`, first collision
`σ` of the leftmost right mark `k`, the other gaps at least `δ`, every point to the right of `k` alive), after the
Girsanov removal of the marks not at `k`'s position (drift `(√κ)⁻¹ Σ σ'_k r_δ(W − U_k)`), the force gap and the
passive gap solve the one-group equations in the chart at `r` driven by the shifted Girsanov Brownian path; the tamed
processes of `Aux25Hit.lean` coincide with them up to the first time the ratio `u = û/X` reaches `1/2`, which is then
the exit time of the region, so the stopped tamed path is a hit.

## Main results

* `markFlow_eq_of_sol`: a tamed flow agrees with every continuous solution of its integral equation;
* `hittingBtwn_eq_of_first`: the hitting time of a closed set is the first visit;
* `sub_eq_of_partialCut`: the algebra of a partial cut drift.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Aux25

open Girsanov

/-! ### Uniqueness for tamed flows -/

section Unique

variable {Ω : Type*} {F : ℝ → ℝ} {K : ℝ≥0} {M : ℝ} {W : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- **A tamed flow is the solution of its integral equation.** For a bounded Lipschitz `F` and a driver
continuous along `ω`, every continuous solution of `Z = ∫₀ˢ F(Z − W)` on `[0, T]` is the tamed flow from `0`. -/
theorem markFlow_eq_of_sol (hF : LipschitzWith K F) (hM : ∀ x, |F x| ≤ M)
    (hWc : Continuous (W · ω)) {T : ℝ≥0} {Z : ℝ → ℝ} (hZc : ContinuousOn Z (Icc 0 T))
    (hZ : ∀ s ∈ Icc (0 : ℝ) T, Z s = ∫ r in (0 : ℝ)..s, F (Z r - W r.toNNReal ω)) :
    ∀ s ∈ Icc (0 : ℝ) T, Sec2.markFlow F 0 (fun _ => ⊤) W s.toNNReal ω = Z s := by
  obtain ⟨u, huc, hueq, hmu⟩ := Sec2.exists_markFlow_eq (y := 0) (ζ := fun _ : Ω => (⊤ : ℝ≥0∞))
    (W := W) hF hM hWc.continuousOn (t₁ := T) ENNReal.coe_lt_top
  have hwc : Continuous fun s : ℝ => -W s.toNNReal ω := (hWc.comp continuous_real_toNNReal).neg
  have hD : OneForce.LipData F (fun s : ℝ => -W s.toNNReal ω) :=
    ⟨⟨K, hF⟩, ⟨M, hM⟩, hwc⟩
  have hu' := OneForce.eqOn_lipSol hD (x := 0) (T := T) T.coe_nonneg (Z := fun s => u s - W s.toNNReal ω)
    (huc.sub (hWc.comp continuous_real_toNNReal).continuousOn) fun s hs => by
      rw [hueq s hs]; ring
  have hZ' := OneForce.eqOn_lipSol hD (x := 0) (T := T) T.coe_nonneg (Z := fun s => Z s - W s.toNNReal ω)
    (hZc.sub (hWc.comp continuous_real_toNNReal).continuousOn) fun s hs => by
      rw [hZ s hs]; ring
  intro s hs
  rw [hmu s hs]
  have h1 := hu' hs
  have h2 := hZ' hs
  simp only at h1 h2
  linarith

end Unique

/-! ### First hitting times -/

theorem hittingBtwn_eq_of_first {Ω β : Type*} {X : ℝ≥0 → Ω → β} {C : Set β} {ω : Ω} {N t₀ : ℝ≥0}
    (ht₀N : t₀ ≤ N) (hC : X t₀ ω ∈ C) (hbefore : ∀ t < t₀, X t ω ∉ C) :
    hittingBtwn X C 0 N ω = t₀ := by
  have hex : ∃ j ∈ Icc (0 : ℝ≥0) N, X j ω ∈ C := ⟨t₀, ⟨zero_le, ht₀N⟩, hC⟩
  simp only [hittingBtwn, hex, ↓reduceIte]
  refine IsLeast.csInf_eq ⟨⟨⟨zero_le, ht₀N⟩, hC⟩, fun t ht => ?_⟩
  by_contra hlt
  exact hbefore t (not_le.1 hlt) ht.2

/-! ### The algebra of a partial cut drift -/

/-- **Partial cut drift.** If `w = √κ b + Σ ∫ σ_k/(w − u_k)` at `a` and `a + t`,
`b̂ = b + ∫ κ^{-1/2} Σ σ'_k r_δ(w − u_k)` at the same times, every removed mark (`σ'_k ≠ 0`) has gap `≥ δ` on
`[a, a + t]`, then `w_{a+t} − w_a = √κ (b̂_{a+t} − b̂_a) + Σ_k ∫ₐ^{a+t} (σ_k − σ'_k)/(w − u_k)`. -/
theorem sub_eq_of_partialCut {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) {m : ℕ} (σ σ' : Fin m → ℝ)
    {w b bh : ℝ≥0 → ℝ} {u : Fin m → ℝ≥0 → ℝ} {a t : ℝ≥0}
    (hint : ∀ k, IntervalIntegrable (fun s : ℝ => σ k / (w s.toNNReal - u k s.toNNReal)) volume 0
      ((a + t : ℝ≥0) : ℝ))
    (hint' : ∀ k, IntervalIntegrable (fun s : ℝ => σ' k / (w s.toNNReal - u k s.toNNReal)) volume 0
      ((a + t : ℝ≥0) : ℝ))
    (hfint : IntervalIntegrable (fun s : ℝ => (Real.sqrt κ)⁻¹ *
      addedDriftCut σ' δ (w s.toNNReal) (fun k => u k s.toNNReal)) volume 0 ((a + t : ℝ≥0) : ℝ))
    (hw1 : w (a + t) = Real.sqrt κ * b (a + t) + ∑ k, ∫ s in (0 : ℝ)..((a + t : ℝ≥0) : ℝ),
      σ k / (w s.toNNReal - u k s.toNNReal))
    (hw2 : w a = Real.sqrt κ * b a + ∑ k, ∫ s in (0 : ℝ)..(a : ℝ),
      σ k / (w s.toNNReal - u k s.toNNReal))
    (hb1 : bh (a + t) = b (a + t) + ∫ s in (0 : ℝ)..((a + t : ℝ≥0) : ℝ), (Real.sqrt κ)⁻¹ *
      addedDriftCut σ' δ (w s.toNNReal) (fun k => u k s.toNNReal))
    (hb2 : bh a = b a + ∫ s in (0 : ℝ)..(a : ℝ), (Real.sqrt κ)⁻¹ *
      addedDriftCut σ' δ (w s.toNNReal) (fun k => u k s.toNNReal))
    (hgap : ∀ s : ℝ≥0, a ≤ s → s ≤ a + t → ∀ k, σ' k ≠ 0 → δ ≤ |w s - u k s|) :
    w (a + t) - w a = Real.sqrt κ * (bh (a + t) - bh a) +
      ∑ k, ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), (σ k - σ' k) / (w s.toNNReal - u k s.toNNReal) := by
  have hsκ : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have haat : ((a : ℝ≥0) : ℝ) ≤ ((a + t : ℝ≥0) : ℝ) := by exact_mod_cast le_self_add
  have hsub : uIcc (0 : ℝ) (a : ℝ) ⊆ uIcc 0 ((a + t : ℝ≥0) : ℝ) := by
    rw [uIcc_of_le (NNReal.coe_nonneg a), uIcc_of_le (NNReal.coe_nonneg _)]
    exact Icc_subset_Icc_right haat
  have hsub2 : uIcc (a : ℝ) ((a + t : ℝ≥0) : ℝ) ⊆ uIcc 0 ((a + t : ℝ≥0) : ℝ) := by
    rw [uIcc_of_le haat, uIcc_of_le (NNReal.coe_nonneg _)]
    exact Icc_subset_Icc_left (NNReal.coe_nonneg a)
  have hcongr : ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), (Real.sqrt κ)⁻¹ *
        addedDriftCut σ' δ (w s.toNNReal) (fun k => u k s.toNNReal)
      = (Real.sqrt κ)⁻¹ * ∑ k, ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ),
          σ' k / (w s.toNNReal - u k s.toNNReal) := by
    rw [← intervalIntegral.integral_finsetSum fun k _ => (hint' k).mono_set hsub2,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le haat] at hs
    have hs0 : 0 ≤ s := (NNReal.coe_nonneg a).trans hs.1
    have h1 : a ≤ s.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hs.1
    have h2 : s.toNNReal ≤ a + t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hs.2
    simp only [addedDriftCut]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : σ' k = 0
    · simp [hk]
    · rw [recipCut_of_le hδ (hgap _ h1 h2 k hk), div_eq_mul_inv]
  have hD : ∀ k, (∫ s in (0 : ℝ)..((a + t : ℝ≥0) : ℝ), σ k / (w s.toNNReal - u k s.toNNReal))
      - (∫ s in (0 : ℝ)..(a : ℝ), σ k / (w s.toNNReal - u k s.toNNReal))
      = ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), σ k / (w s.toNNReal - u k s.toNNReal) := fun k =>
    intervalIntegral.integral_interval_sub_left (hint k) ((hint k).mono_set hsub)
  have hF := intervalIntegral.integral_interval_sub_left hfint (hfint.mono_set hsub)
  have hsum : (∑ k, ∫ s in (0 : ℝ)..((a + t : ℝ≥0) : ℝ), σ k / (w s.toNNReal - u k s.toNNReal))
      - (∑ k, ∫ s in (0 : ℝ)..(a : ℝ), σ k / (w s.toNNReal - u k s.toNNReal))
      = ∑ k, ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), σ k / (w s.toNNReal - u k s.toNNReal) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => hD k
  have key : Real.sqrt κ * ((∫ s in (0 : ℝ)..((a + t : ℝ≥0) : ℝ), (Real.sqrt κ)⁻¹ *
        addedDriftCut σ' δ (w s.toNNReal) (fun k => u k s.toNNReal))
      - ∫ s in (0 : ℝ)..(a : ℝ), (Real.sqrt κ)⁻¹ *
        addedDriftCut σ' δ (w s.toNNReal) (fun k => u k s.toNNReal))
      = ∑ k, ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), σ' k / (w s.toNNReal - u k s.toNNReal) := by
    rw [hF, hcongr, ← mul_assoc, mul_inv_cancel₀ hsκ, one_mul]
  have hdiff : ∑ k, ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), (σ k - σ' k) / (w s.toNNReal - u k s.toNNReal)
      = (∑ k, ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), σ k / (w s.toNNReal - u k s.toNNReal)) -
        ∑ k, ∫ s in (a : ℝ)..((a + t : ℝ≥0) : ℝ), σ' k / (w s.toNNReal - u k s.toNNReal) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← intervalIntegral.integral_sub ((hint k).mono_set hsub2) ((hint' k).mono_set hsub2)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [sub_div]
  rw [hdiff, hw1, hw2, hb1, hb2]
  linear_combination hsum - key

/-! ### Order preservation of right marks along a frozen path -/

section Order

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- Two right marks keep their order: `v_j(t₁) ≤ v_k(t₁)` implies `v_j(t) ≤ v_k(t)` for `t₁ ≤ t < ζ`. -/
theorem vR_le_of_le (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {j k : Fin nR}
    {t₁ t : ℝ≥0} (ht₁ : t₁ ≤ t) (htζ : (t : ℝ≥0∞) < ζ) (h : vR j t₁ ≤ vR k t₁) : vR j t ≤ vR k t := by
  obtain ⟨-, -, -, hwc, -, hvRc, -, -, hwvR, -, -, hgapR, -, -, hvReq, -, hcolR, -⟩ := hp
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := exists_real_btwn_of_lt htζ
  have hT0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hm : ∀ i, _ := fun i => centred_eq_of_frozen hwc (hvRc i) (fun s hs => hgapR s hs i)
    (fun s hs => hvReq s hs i) (hcolR i) ht₂ζ hT0 htt₂.le
  have ha : (0 : ℝ) ≤ t₁ := t₁.coe_nonneg
  have hab : (t₁ : ℝ) ≤ t := by exact_mod_cast ht₁
  have hRj := centred_restrict ha hab le_rfl (hm j)
  have hRk := centred_restrict ha hab le_rfl (hm k)
  have hlt : ∀ x ∈ Icc (0 : ℝ) t, ((x.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := fun x hx =>
    toNNReal_lt_of_le ht₂ζ (hx.2.trans htt₂.le)
  have hu0 : ∀ x ∈ Icc (t₁ : ℝ) t, 0 ≤ centred (vR k) (frozenDrive w t₂) x := fun x hx => by
    have hxI : x ∈ Icc (0 : ℝ) t := ⟨ha.trans hx.1, hx.2⟩
    simp only [centred, frozenDrive_eq ⟨hxI.1, hxI.2.trans htt₂.le⟩]
    linarith [hwvR _ (hlt x hxI) k]
  have hcmp := sub_le_max_of_centredEq hRk.1 hu0 hRk.2.1 hRk.2.2.1 hRk.2.2.2 hRj.1 hRj.2.1
    hRj.2.2.1 (t : ℝ) ⟨hab, le_rfl⟩
  have e : ∀ x : ℝ≥0, (x : ℝ) ≤ t₂ → ∀ i, centred (vR i) (frozenDrive w t₂) x = vR i x - w x :=
    fun x hx i => by simp only [centred, Real.toNNReal_coe, frozenDrive_eq ⟨x.coe_nonneg, hx⟩]
  rw [e t htt₂.le, e t htt₂.le, e t₁ (hab.trans htt₂.le), e t₁ (hab.trans htt₂.le),
    max_eq_right (by linarith)] at hcmp
  linarith

theorem vR_eq_of_eq (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {j k : Fin nR}
    {t₁ t : ℝ≥0} (ht₁ : t₁ ≤ t) (htζ : (t : ℝ≥0∞) < ζ) (h : vR j t₁ = vR k t₁) : vR j t = vR k t :=
  le_antisymm (vR_le_of_le hp ht₁ htζ h.le) (vR_le_of_le hp ht₁ htζ h.ge)

end Order

/-! ### The driver after the Girsanov removal of the marks off the group -/

section Driver

variable {nL nR : ℕ}

/-- The removed weights: all left marks and the right marks outside `S`. -/
def removedWeights (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (S : Finset (Fin nR)) : Fin (nL + nR) → ℝ :=
  Fin.addCases ρL (fun j => if j ∈ S then 0 else ρR j)

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The driver of the group.** After removing (Girsanov, cut at `δ`) the drift of all marks except the right
marks of `S`, on an interval `[r, σ]` where the removed marks have gaps `≥ δ` and the marks of `S` move with `k`,
`w(s) − w(r) = √κ (b̂(s) − b̂(r)) + ∫ᵣˢ ρ_S/(w − v_k)` with `ρ_S = Σ_{j ∈ S} ρ_j`. -/
theorem driver_oneGroup (hκ : 0 < κ) {δ : ℝ} (hδ : 0 < δ)
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {S : Finset (Fin nR)} {k : Fin nR}
    {u : Fin (nL + nR) → ℝ≥0 → ℝ} (huL : ∀ i, u (Fin.castAdd nR i) = vL i)
    (huR : ∀ j, u (Fin.natAdd nL j) = vR j) {bh : ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hident : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ → bh t = b t + ∫ s in (0 : ℝ)..(t : ℝ), (Real.sqrt κ)⁻¹ *
      addedDriftCut (removedWeights ρL ρR S) δ (w s.toNNReal) (fun j => u j s.toNNReal))
    {r σ : ℝ≥0} (hστ : (σ : ℝ≥0∞) ≤ τ) (hσζ : (σ : ℝ≥0∞) < ζ)
    (hgrp : ∀ j ∈ S, ∀ s : ℝ≥0, r ≤ s → s ≤ σ → vR j s = vR k s)
    (hgapR : ∀ s : ℝ≥0, r ≤ s → s ≤ σ → ∀ j, j ∉ S → δ ≤ vR j s - w s)
    (hgapL : ∀ s : ℝ≥0, r ≤ s → s ≤ σ → ∀ i, δ ≤ w s - vL i s) {s : ℝ≥0} (hrs : r ≤ s) (hsσ : s ≤ σ) :
    w s - w r = Real.sqrt κ * (bh s - bh r) +
      ∫ t in (r : ℝ)..s, (∑ j ∈ S, ρR j) / (w t.toNNReal - vR k t.toNNReal) := by
  obtain ⟨-, -, -, hwc, hvLc, hvRc, -, -, -, -, hgL, hgR, hweq, -, -, -, -, -⟩ := hp
  have hsζ : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsσ) hσζ
  have hrζ : (r : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hrs) hsζ
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Fin (nL + nR) → ℝ, σ₀ = Fin.addCases ρL ρR := ⟨_, rfl⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Fin (nL + nR) → ℝ, σ' = removedWeights ρL ρR S := ⟨_, rfl⟩
  rw [← hσ'] at hident
  have hrs' : r + (s - r) = s := add_tsub_cancel_of_le hrs
  -- integrability of the gaps on `[0, s]`
  have hintk : ∀ (c : Fin (nL + nR) → ℝ) (hc : ∀ i, c (Fin.castAdd nR i) = 0 ∨ c (Fin.castAdd nR i) = ρL i)
      (hc' : ∀ j, c (Fin.natAdd nL j) = 0 ∨ c (Fin.natAdd nL j) = ρR j),
      ∀ m, IntervalIntegrable (fun t : ℝ => c m / (w t.toNNReal - u m t.toNNReal)) volume 0 (s : ℝ) := by
    intro c hc hc' m
    cases m using Fin.addCases with
    | left i =>
      rw [huL i]
      simp only [div_eq_mul_inv]
      exact (hgL s hsζ i).const_mul _
    | right j =>
      rw [huR j]
      simp only [div_eq_mul_inv]
      exact (hgR s hsζ j).const_mul _
  have hint := hintk σ₀ (fun i => Or.inr (by simp [hσ₀])) (fun j => Or.inr (by simp [hσ₀]))
  have hint' := hintk σ' (fun i => Or.inr (by simp [hσ', removedWeights]))
    (fun j => by by_cases hj : j ∈ S <;> simp [hσ', removedWeights, hj])
  have hlt : ∀ t ∈ Icc (0 : ℝ) s, ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := fun t ht =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht.1]; exact ht.2)) hsζ
  have hfint : IntervalIntegrable (fun t : ℝ => (Real.sqrt κ)⁻¹ *
      addedDriftCut σ' δ (w t.toNNReal) (fun j => u j t.toNNReal)) volume 0 (s : ℝ) := by
    have hc := continuous_addedDriftCut σ' hδ
    have hpath : ContinuousOn (fun t : ℝ => ((w t.toNNReal, fun j => u j t.toNNReal) :
        ℝ × (Fin (nL + nR) → ℝ))) (Icc 0 s) := by
      refine ContinuousOn.prodMk ?_ (continuousOn_pi.2 fun m => ?_)
      · exact hwc.comp continuous_real_toNNReal.continuousOn fun t ht => hlt t ht
      · cases m using Fin.addCases with
        | left i =>
          simp only [huL i]
          exact (hvLc i).comp continuous_real_toNNReal.continuousOn fun t ht => hlt t ht
        | right j =>
          simp only [huR j]
          exact (hvRc j).comp continuous_real_toNNReal.continuousOn fun t ht => hlt t ht
    have hcomp := hc.comp_continuousOn hpath
    exact ContinuousOn.intervalIntegrable_of_Icc s.coe_nonneg (continuousOn_const.mul hcomp)
  have hsplit : ∀ t : ℝ≥0, (∑ m, ∫ x in (0 : ℝ)..(t : ℝ), σ₀ m / (w x.toNNReal - u m x.toNNReal))
      = (∑ i, ∫ x in (0 : ℝ)..(t : ℝ), ρL i / (w x.toNNReal - vL i x.toNNReal))
        + (∑ j, ∫ x in (0 : ℝ)..(t : ℝ), ρR j / (w x.toNNReal - vR j x.toNNReal)) := by
    intro t
    rw [Fin.sum_univ_add]
    simp only [hσ₀, Fin.addCases_left, Fin.addCases_right, huL, huR]
  have key := sub_eq_of_partialCut (a := r) (t := s - r) hκ hδ σ₀ σ' (w := w) (b := b) (bh := bh)
    (u := u) (by rw [hrs']; exact hint) (by rw [hrs']; exact hint') (by rw [hrs']; exact hfint)
    (by rw [hrs', hsplit, hweq s hsζ]; ring) (by rw [hsplit, hweq r hrζ]; ring)
    (by rw [hrs']; exact hident s (le_trans (ENNReal.coe_le_coe.2 hsσ) hστ))
    (hident r (le_trans (ENNReal.coe_le_coe.2 (hrs.trans hsσ)) hστ)) ?_
  · rw [hrs'] at key
    rw [key]
    congr 1
    -- the kept drift is that of the group
    rw [Fin.sum_univ_add]
    have hL0 : ∀ i, ∫ t in (r : ℝ)..(s : ℝ),
        (σ₀ (Fin.castAdd nR i) - σ' (Fin.castAdd nR i)) / (w t.toNNReal - u (Fin.castAdd nR i) t.toNNReal)
          = 0 := fun i => by simp [hσ₀, hσ', removedWeights]
    simp only [hL0, Finset.sum_const_zero, zero_add]
    have hR : ∀ j, ∫ t in (r : ℝ)..(s : ℝ),
        (σ₀ (Fin.natAdd nL j) - σ' (Fin.natAdd nL j)) / (w t.toNNReal - u (Fin.natAdd nL j) t.toNNReal)
          = if j ∈ S then ∫ t in (r : ℝ)..(s : ℝ), ρR j / (w t.toNNReal - vR k t.toNNReal) else 0 := by
      intro j
      by_cases hj : j ∈ S
      · simp only [hσ₀, hσ', removedWeights, Fin.addCases_right, hj, ↓reduceIte, sub_zero, huR j]
        refine intervalIntegral.integral_congr fun t ht => ?_
        have hrsr : (r : ℝ) ≤ s := by exact_mod_cast hrs
        rw [uIcc_of_le hrsr] at ht
        have ht0 : 0 ≤ t := (NNReal.coe_nonneg r).trans ht.1
        have h1 : r ≤ t.toNNReal := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]; exact ht.1
        have h2 : t.toNNReal ≤ σ := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]
          exact ht.2.trans (by exact_mod_cast hsσ)
        simp only [hgrp j hj _ h1 h2]
      · simp [hσ₀, hσ', removedWeights, hj]
    simp only [hR]
    rw [← Finset.sum_filter, ← intervalIntegral.integral_finsetSum fun j _ => ?_]
    · refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_div]
    · have hk := hgR s hsζ k
      have hrsr : (r : ℝ) ≤ s := by exact_mod_cast hrs
      simp only [div_eq_mul_inv]
      refine ((hk.mono_set ?_).const_mul (ρR j)).congr fun t _ => ?_
      · rw [uIcc_of_le hrsr, uIcc_of_le s.coe_nonneg]
        exact Icc_subset_Icc_left r.coe_nonneg
      · simp only
  · intro t h1 h2 m hm
    rw [hrs'] at h2
    cases m using Fin.addCases with
    | left i =>
      rw [huL i, abs_of_nonneg (by linarith [hgapL t h1 (h2.trans hsσ) i])]
      exact hgapL t h1 (h2.trans hsσ) i
    | right j =>
      have hj : j ∉ S := fun hj => hm (by simp [hσ', removedWeights, hj])
      rw [huR j, abs_sub_comm, abs_of_nonneg (by linarith [hgapR t h1 (h2.trans hsσ) j hj])]
      exact hgapR t h1 (h2.trans hsσ) j hj

end Driver

/-! ### The one-group equations in the chart at the restart time -/

section Relative

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}

theorem toNNReal_add_rel (r : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) : ((r : ℝ) + t).toNNReal = r + t.toNNReal := by
  rw [Real.toNNReal_add r.coe_nonneg ht, Real.toNNReal_coe]

/-- Shifting an integral over `[r, r + s]` to `[0, s]`. -/
theorem integral_shift_rel (r : ℝ≥0) (f : ℝ≥0 → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ∫ t in (r : ℝ)..((r + s.toNNReal : ℝ≥0) : ℝ), f t.toNNReal = ∫ t in (0 : ℝ)..s, f (r + t.toNNReal) := by
  have h1 : ((r + s.toNNReal : ℝ≥0) : ℝ) = (r : ℝ) + s := by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hs]
  rw [h1]
  have h := intervalIntegral.integral_comp_add_left (fun t : ℝ => f t.toNNReal) (r : ℝ) (a := 0) (b := s)
  rw [add_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hs] at ht
  simp only [toNNReal_add_rel r ht.1]

/-- **The force gap in the chart at `r`.** -/
theorem gap_eq_rel (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {k : Fin nR} {r σ : ℝ≥0}
    (hσζ : (σ : ℝ≥0∞) < ζ) {ρS : ℝ} {bh : ℝ≥0 → ℝ}
    (hdrv : ∀ s : ℝ≥0, r ≤ s → s ≤ σ → w s - w r = Real.sqrt κ * (bh s - bh r) +
      ∫ t in (r : ℝ)..s, ρS / (w t.toNNReal - vR k t.toNNReal))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) ((σ : ℝ) - r)) :
    vR k (r + s.toNNReal) - w (r + s.toNNReal) = (vR k r - w r) -
      Real.sqrt κ * (bh (r + s.toNNReal) - bh r) +
        ∫ t in (0 : ℝ)..s, (2 + ρS) / (vR k (r + t.toNNReal) - w (r + t.toNNReal)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgR, -, -, hvReq, -, -, -⟩ := hp
  have hrs : r ≤ r + s.toNNReal := le_self_add
  have hsσ : r + s.toNNReal ≤ σ := by
    rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hs.1]; linarith [hs.2]
  have hsζ : ((r + s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsσ) hσζ
  have hrζ : (r : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hrs) hsζ
  have hgi : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun x : ℝ => 2 / (vR k x.toNNReal - w x.toNNReal)) volume 0 t := by
    intro t ht
    have h := hgR t ht k
    have e : (fun x : ℝ => 2 / (vR k x.toNNReal - w x.toNNReal)) =
        fun x => (-2) * (w x.toNNReal - vR k x.toNNReal)⁻¹ := by
      funext x; rw [div_eq_mul_inv, ← neg_sub, inv_neg]; ring
    rw [e]; exact h.const_mul _
  have hv := hvReq _ hsζ k
  have hv0 := hvReq r hrζ k
  have hvdiff : vR k (r + s.toNNReal) - vR k r =
      ∫ t in (r : ℝ)..((r + s.toNNReal : ℝ≥0) : ℝ), 2 / (vR k t.toNNReal - w t.toNNReal) := by
    rw [hv, hv0, ← intervalIntegral.integral_interval_sub_left (hgi _ hsζ) (hgi _ hrζ)]
    ring
  have hw := hdrv _ hrs hsσ
  -- combine the two drift integrals over `[r, r + s]`
  have hsub : uIcc (r : ℝ) ((r + s.toNNReal : ℝ≥0) : ℝ) ⊆ uIcc 0 ((r + s.toNNReal : ℝ≥0) : ℝ) := by
    rw [uIcc_of_le (by exact_mod_cast hrs), uIcc_of_le (NNReal.coe_nonneg _)]
    exact Icc_subset_Icc_left r.coe_nonneg
  have hi1 := (hgi _ hsζ).mono_set hsub
  have hi2 : IntervalIntegrable (fun t : ℝ => ρS / (w t.toNNReal - vR k t.toNNReal)) volume (r : ℝ)
      ((r + s.toNNReal : ℝ≥0) : ℝ) := by
    have h := ((hgR _ hsζ k).mono_set hsub).const_mul ρS
    exact h.congr fun x _ => by simp only [div_eq_mul_inv]
  have hcomb : (∫ t in (r : ℝ)..((r + s.toNNReal : ℝ≥0) : ℝ), 2 / (vR k t.toNNReal - w t.toNNReal)) -
      ∫ t in (r : ℝ)..((r + s.toNNReal : ℝ≥0) : ℝ), ρS / (w t.toNNReal - vR k t.toNNReal) =
      ∫ t in (r : ℝ)..((r + s.toNNReal : ℝ≥0) : ℝ), (2 + ρS) / (vR k t.toNNReal - w t.toNNReal) := by
    rw [← intervalIntegral.integral_sub hi1 hi2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show 2 / (vR k t.toNNReal - w t.toNNReal) - ρS / (w t.toNNReal - vR k t.toNNReal) = _
    rw [show w t.toNNReal - vR k t.toNNReal = -(vR k t.toNNReal - w t.toNNReal) by ring, div_neg]
    ring
  rw [integral_shift_rel r (fun t => (2 + ρS) / (vR k t - w t)) hs.1] at hcomb
  linarith

/-- **The passive gap in the chart at `r`.** -/
theorem passive_eq_rel {k : Fin nR} {r σ : ℝ≥0} {ρS : ℝ} {bh : ℝ≥0 → ℝ}
    (hgi : IntervalIntegrable (fun x : ℝ => ρS / (w x.toNNReal - vR k x.toNNReal)) volume (r : ℝ) σ)
    (hdrv : ∀ s : ℝ≥0, r ≤ s → s ≤ σ → w s - w r = Real.sqrt κ * (bh s - bh r) +
      ∫ t in (r : ℝ)..s, ρS / (w t.toNNReal - vR k t.toNNReal))
    {y₀ : ℝ} {Xa : ℝ → ℝ} (hXc : ContinuousOn Xa (Icc (r : ℝ) σ)) (hXpos : ∀ x ∈ Icc (r : ℝ) σ, 0 < Xa x)
    (hXeq : ∀ x ∈ Icc (r : ℝ) σ, Xa x = y₀ - (w x.toNNReal - w r) + ∫ t in (r : ℝ)..x, 2 / Xa t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) ((σ : ℝ) - r)) :
    Xa (r + s) = y₀ - Real.sqrt κ * (bh (r + s.toNNReal) - bh r) +
      ∫ t in (0 : ℝ)..s, (2 / Xa (r + t) + ρS / (vR k (r + t.toNNReal) - w (r + t.toNNReal))) := by
  have hrs : r ≤ r + s.toNNReal := le_self_add
  have hsσ : r + s.toNNReal ≤ σ := by
    rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hs.1]; linarith [hs.2]
  have hxs : (r : ℝ) + s ∈ Icc (r : ℝ) σ := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hX := hXeq _ hxs
  have hcoe : (((r : ℝ) + s).toNNReal) = r + s.toNNReal := toNNReal_add_rel r hs.1
  rw [hcoe] at hX
  have hw := hdrv _ hrs hsσ
  have hc1 : ((r + s.toNNReal : ℝ≥0) : ℝ) = (r : ℝ) + s := by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hs.1]
  have hsub : uIcc (r : ℝ) ((r : ℝ) + s) ⊆ uIcc (r : ℝ) σ := by
    rw [uIcc_of_le (by linarith [hs.1]), uIcc_of_le (by linarith [hs.1, hs.2])]
    exact Icc_subset_Icc_right hxs.2
  have hXi : IntervalIntegrable (fun t => 2 / Xa t) volume (r : ℝ) ((r : ℝ) + s) :=
    ((continuousOn_const.div hXc fun x hx => (hXpos x hx).ne').intervalIntegrable_of_Icc
      (by linarith [hs.1, hs.2] : (r : ℝ) ≤ σ)).mono_set hsub
  have hgi' := hgi.mono_set hsub
  rw [hc1] at hw
  have h1 : (∫ t in (r : ℝ)..((r : ℝ) + s), 2 / Xa t) = ∫ t in (0 : ℝ)..s, 2 / Xa (r + t) := by
    have h := intervalIntegral.integral_comp_add_left (fun t => 2 / Xa t) (r : ℝ) (a := 0) (b := s)
    rw [add_zero] at h
    exact h.symm
  have h2 : (∫ t in (r : ℝ)..((r : ℝ) + s), ρS / (w t.toNNReal - vR k t.toNNReal)) =
      ∫ t in (0 : ℝ)..s, ρS / (w (r + t.toNNReal) - vR k (r + t.toNNReal)) := by
    have := integral_shift_rel r (fun t => ρS / (w t - vR k t)) hs.1
    rwa [hc1] at this
  have hXi' : IntervalIntegrable (fun t => 2 / Xa (r + t)) volume 0 s := by
    have h := hXi.comp_add_left (r : ℝ)
    simpa [sub_self, add_sub_cancel_left] using h
  have hgi'' : IntervalIntegrable (fun t => ρS / (w (r + t.toNNReal) - vR k (r + t.toNNReal))) volume 0 s := by
    have h := hgi'.comp_add_left (r : ℝ)
    simp only [sub_self, add_sub_cancel_left] at h
    refine h.congr fun t ht => ?_
    rw [uIoc_of_le hs.1] at ht
    simp only [toNNReal_add_rel r ht.1.le]
  rw [intervalIntegral.integral_add hXi' ?_]
  · have e : (∫ t in (0 : ℝ)..s, ρS / (vR k (r + t.toNNReal) - w (r + t.toNNReal))) =
        -∫ t in (0 : ℝ)..s, ρS / (w (r + t.toNNReal) - vR k (r + t.toNNReal)) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => ?_
      show ρS / (vR k (r + t.toNNReal) - w (r + t.toNNReal)) = -(ρS / (w (r + t.toNNReal) - vR k (r + t.toNNReal)))
      rw [show vR k (r + t.toNNReal) - w (r + t.toNNReal) = -(w (r + t.toNNReal) - vR k (r + t.toNNReal))
        by ring, div_neg]
    rw [e, ← h1, ← h2]
    linarith
  · refine hgi''.neg.congr fun t _ => ?_
    simp only [Pi.neg_apply]
    rw [show vR k (r + t.toNNReal) - w (r + t.toNNReal) = -(w (r + t.toNNReal) - vR k (r + t.toNNReal))
      by ring, div_neg]

end Relative

/-! ### The endpoint case is a hit of the tamed process -/

section HitPath

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}

/-- **The endpoint case is a hit.** In the endpoint case after the restart time `r` (first collision `σ` of the
group of `k`, whose driver equation is `hdrv`, and a passive point `y₀ ∈ (û(r), 2û(r))` alive up to `σ`), for
every large `L` the tamed process with cut `1/L` driven by `B = b̂(r + ·) − b̂(r)` from `(û(r), y₀)` starts inside
the region `keepK` and its value at the exit time is a hit (`û ≤ X/2`). -/
theorem tamed_hit_of_endpoint (hκ : 0 < κ) (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    {k : Fin nR} {r σ : ℝ≥0} (hrσ : r < σ) (hσζ : (σ : ℝ≥0∞) < ζ) {ρS : ℝ} (hρS : -2 < ρS)
    {bh : ℝ≥0 → ℝ} (hbhc : Continuous bh)
    (hdrv : ∀ s : ℝ≥0, r ≤ s → s ≤ σ → w s - w r = Real.sqrt κ * (bh s - bh r) +
      ∫ t in (r : ℝ)..s, ρS / (w t.toNNReal - vR k t.toNNReal))
    (hpos : ∀ s : ℝ≥0, r ≤ s → s < σ → w s < vR k s) (hcol : vR k σ = w σ)
    {y₀ : ℝ} (hy1 : y₀ / 2 < vR k r - w r) (halive : AliveFrom w r σ y₀)
    {N : ℝ≥0} (hσN : (σ : ℝ) - r ≤ N)
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {g₀ : Ω → ℝ} {ω : Ω} (hB : ∀ t, B t ω = bh (r + t) - bh r)
    (hg : g₀ ω = vR k r - w r) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      statePath (tState (Real.sqrt κ) ρS (1 / L) y₀ g₀ B) B 0 ω ∉ exitC (Real.sqrt κ) (1 / L) L ∧
      gapU (Real.sqrt κ) 0 (statePath (tState (Real.sqrt κ) ρS (1 / L) y₀ g₀ B) B
          (hitStop (tState (Real.sqrt κ) ρS (1 / L) y₀ g₀ B) B (exitC (Real.sqrt κ) (1 / L) L) N ω) ω) ≤
        gapX (Real.sqrt κ) (statePath (tState (Real.sqrt κ) ρS (1 / L) y₀ g₀ B) B
          (hitStop (tState (Real.sqrt κ) ρS (1 / L) y₀ g₀ B) B (exitC (Real.sqrt κ) (1 / L) L) N ω) ω) / 2 := by
  have hp' := hp
  obtain ⟨-, -, -, hwc, -, hvRc, -, -, -, -, -, hgR, -, -, -, -, -, -⟩ := hp'
  obtain ⟨Xa, hXc, hXpos, hXeq⟩ := halive
  set sk := Real.sqrt κ with hskdef
  have hsk0 : 0 < sk := Real.sqrt_pos.2 hκ
  set T : ℝ := (σ : ℝ) - r with hTdef
  have hT0 : 0 < T := by rw [hTdef]; exact sub_pos.2 (by exact_mod_cast hrσ)
  -- the actual gaps in the chart at `r`
  set u : ℝ → ℝ := fun s => vR k (r + s.toNNReal) - w (r + s.toNNReal) with hudef
  set X : ℝ → ℝ := fun s => Xa (r + s) with hXdef
  set Bt : ℝ → ℝ := fun s => bh (r + s.toNNReal) - bh r with hBtdef
  have hBtc : Continuous Bt :=
    (hbhc.comp (continuous_const.add continuous_real_toNNReal)).sub continuous_const
  have hmemσ : ∀ s ∈ Icc (0 : ℝ) T, r + s.toNNReal ≤ σ := fun s hs => by
    rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hs.1]; linarith [hs.2]
  have hltζ : ∀ s ∈ Icc (0 : ℝ) T, ((r + s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hmemσ s hs)) hσζ
  have huc : ContinuousOn u (Icc 0 T) := by
    have hm : MapsTo (fun s : ℝ => r + s.toNNReal) (Icc 0 T) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} :=
      fun s hs => hltζ s hs
    have hcc : Continuous fun s : ℝ => r + s.toNNReal := continuous_const.add continuous_real_toNNReal
    exact ((hvRc k).comp hcc.continuousOn hm).sub (hwc.comp hcc.continuousOn hm)
  have hXmem : ∀ s ∈ Icc (0 : ℝ) T, (r : ℝ) + s ∈ Icc (r : ℝ) σ := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hXc' : ContinuousOn X (Icc 0 T) :=
    hXc.comp (continuous_const.add continuous_id).continuousOn hXmem
  have hXpos' : ∀ s ∈ Icc (0 : ℝ) T, 0 < X s := fun s hs => hXpos _ (hXmem s hs)
  have hu0 : u 0 = vR k r - w r := by simp [hudef]
  have hX0 : X 0 = y₀ := by
    have h := hXeq r ⟨le_rfl, by exact_mod_cast hrσ.le⟩
    simp only [Real.toNNReal_coe, sub_self, intervalIntegral.integral_same, add_zero, sub_zero] at h
    simp [hXdef, h]
  have hupos : ∀ s ∈ Ico (0 : ℝ) T, 0 < u s := fun s hs => by
    have h1 : r ≤ r + s.toNNReal := le_self_add
    have h2 : r + s.toNNReal < σ := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_add, Real.coe_toNNReal _ hs.1]; linarith [hs.2]
    simp only [hudef]; linarith [hpos _ h1 h2]
  have huT : u T = 0 := by
    have : r + T.toNNReal = σ := by
      rw [← NNReal.coe_inj, NNReal.coe_add, Real.coe_toNNReal _ hT0.le, hTdef]; ring
    simp only [hudef, this, hcol, sub_self]
  -- the equations
  have hgi : IntervalIntegrable (fun x : ℝ => ρS / (w x.toNNReal - vR k x.toNNReal)) volume (r : ℝ) σ := by
    have h := (hgR σ hσζ k).const_mul ρS
    refine (h.mono_set ?_).congr fun x _ => by simp only [div_eq_mul_inv]
    rw [uIcc_of_le (by exact_mod_cast hrσ.le), uIcc_of_le σ.coe_nonneg]
    exact Icc_subset_Icc_left r.coe_nonneg
  have hE1 : ∀ s ∈ Icc (0 : ℝ) T, u s = u 0 - sk * Bt s + ∫ t in (0 : ℝ)..s, (2 + ρS) / u t :=
    fun s hs => by rw [hu0]; exact gap_eq_rel hp hσζ hdrv hs
  have hE2 : ∀ s ∈ Icc (0 : ℝ) T, X s = y₀ - sk * Bt s + ∫ t in (0 : ℝ)..s, (2 / X t + ρS / u t) :=
    fun s hs => passive_eq_rel hgi hdrv hXc hXpos hXeq hs
  -- the first time `τ'` at which `û = X/2`
  set H := Icc (0 : ℝ) T ∩ (fun s => u s - X s / 2) ⁻¹' Iic 0 with hHdef
  have hHc : IsCompact H := isCompact_Icc.of_isClosed_subset
    ((huc.sub (hXc'.div_const 2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
    inter_subset_left
  have hTH : T ∈ H := ⟨⟨hT0.le, le_rfl⟩, by
    show u T - X T / 2 ≤ 0
    rw [huT]; linarith [hXpos' T ⟨hT0.le, le_rfl⟩]⟩
  set τ' := sInf H with hτ'def
  have hτ'H : τ' ∈ H := hHc.sInf_mem ⟨T, hTH⟩
  have hτ'le : u τ' - X τ' / 2 ≤ 0 := hτ'H.2
  have hbefore : ∀ s ∈ Ico (0 : ℝ) τ', X s / 2 < u s := fun s hs => by
    by_contra hcon
    have hsH : s ∈ H := ⟨⟨hs.1, hs.2.le.trans hτ'H.1.2⟩, show u s - X s / 2 ≤ 0 by linarith [not_lt.1 hcon]⟩
    exact absurd (csInf_le hHc.bddBelow hsH) (not_le.2 hs.2)
  have hτ'0 : 0 < τ' := by
    rcases hτ'H.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := hτ'le
      rw [← h, hu0, hX0] at h2
      linarith
  have hτ'T : τ' ≤ T := hτ'H.1.2
  have hIsub : Icc (0 : ℝ) τ' ⊆ Icc 0 T := Icc_subset_Icc_right hτ'T
  have hfc : ContinuousOn (fun s => u s - X s / 2) (Icc 0 τ') :=
    (huc.sub (hXc'.div_const 2)).mono hIsub
  have hτ'eq : u τ' = X τ' / 2 := by
    have hcl : IsClosed (Icc 0 τ' ∩ (fun s => u s - X s / 2) ⁻¹' Ici 0) :=
      hfc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Ico 0 τ' ⊆ Icc 0 τ' ∩ (fun s => u s - X s / 2) ⁻¹' Ici 0 := fun s hs =>
      ⟨Ico_subset_Icc_self hs, show 0 ≤ u s - X s / 2 by linarith [hbefore s hs]⟩
    have hmem : τ' ∈ closure (Ico 0 τ') := by
      rw [closure_Ico hτ'0.ne]; exact ⟨hτ'0.le, le_rfl⟩
    have h := (hcl.closure_subset_iff.2 hsub) hmem
    have h2 : 0 ≤ u τ' - X τ' / 2 := h.2
    linarith
  have hXτ' : 0 < X τ' := hXpos' τ' hτ'H.1
  have hτ'lt : τ' < T := by
    rcases hτ'T.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h, huT] at hτ'eq; linarith [hXpos' T ⟨hT0.le, le_rfl⟩]
  -- positivity and integrability on `[0, τ']`
  have hupos' : ∀ s ∈ Icc (0 : ℝ) τ', X s / 2 ≤ u s := fun s hs => by
    rcases hs.2.lt_or_eq with h | h
    · exact (hbefore s ⟨hs.1, h⟩).le
    · rw [h, hτ'eq]
  obtain ⟨s₁, hs₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hτ'0.le) (hXc'.mono hIsub)
  obtain ⟨s₂, hs₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hτ'0.le) (hXc'.mono hIsub)
  set m₁ := X s₁ with hm₁
  set M₁ := X s₂ with hM₁
  have hm₁pos : 0 < m₁ := hXpos' s₁ (hIsub hs₁)
  have hXge : ∀ s ∈ Icc (0 : ℝ) τ', m₁ ≤ X s := fun s hs => hmin hs
  have hXle : ∀ s ∈ Icc (0 : ℝ) τ', X s ≤ M₁ := fun s hs => hmax hs
  have hugt : ∀ s ∈ Icc (0 : ℝ) τ', m₁ / 2 ≤ u s := fun s hs => by
    linarith [hupos' s hs, hXge s hs]
  have hune : ∀ s ∈ Icc (0 : ℝ) τ', u s ≠ 0 := fun s hs =>
    (lt_of_lt_of_le (by linarith) (hugt s hs)).ne'
  have hXne : ∀ s ∈ Icc (0 : ℝ) τ', X s ≠ 0 := fun s hs =>
    (lt_of_lt_of_le hm₁pos (hXge s hs)).ne'
  have hiu : ∀ c : ℝ, IntervalIntegrable (fun t => c / u t) volume 0 τ' := fun c =>
    (continuousOn_const.div (huc.mono hIsub) hune).intervalIntegrable_of_Icc hτ'0.le
  have hiX : ∀ c : ℝ, IntervalIntegrable (fun t => c / X t) volume 0 τ' := fun c =>
    (continuousOn_const.div (hXc'.mono hIsub) hXne).intervalIntegrable_of_Icc hτ'0.le
  have hsubI : ∀ a' ∈ Icc (0 : ℝ) τ', ∀ b' ∈ Icc (0 : ℝ) τ', uIcc a' b' ⊆ uIcc 0 τ' := fun a' ha' b' hb' =>
    by rw [uIcc_of_le hτ'0.le]; exact uIcc_subset_Icc ha' hb'
  have hdiff : ∀ {f : ℝ → ℝ}, IntervalIntegrable f volume 0 τ' → ∀ a' ∈ Icc (0 : ℝ) τ',
      ∀ b' ∈ Icc (0 : ℝ) τ', (∫ t in (0 : ℝ)..b', f t) - (∫ t in (0 : ℝ)..a', f t) = ∫ t in a'..b', f t :=
    fun hf a' ha' b' hb' => intervalIntegral.integral_interval_sub_left
      (hf.mono_set (hsubI 0 ⟨le_rfl, hτ'0.le⟩ b' hb')) (hf.mono_set (hsubI 0 ⟨le_rfl, hτ'0.le⟩ a' ha'))
  -- the margin `X − û ≥ X(τ')/2` (backward comparison with the common driver)
  set Wt : ℝ → ℝ := fun s => sk * Bt s - ∫ t in (0 : ℝ)..s, ρS / u t with hWtdef
  have hc₀ : 0 < X τ' / 2 := by linarith
  have hmargin : ∀ s ∈ Icc (0 : ℝ) τ', X τ' / 2 ≤ X s - u s := by
    refine le_sub_of_backward_cut (W := Wt) (t := τ') hc₀ (huc.mono hIsub)
      (fun s hs => by linarith [hugt s hs]) ?_ (hiu 2) ?_ (δ := m₁) hm₁pos (hXc'.mono hIsub)
      (by rw [hτ'eq]; ring) ?_
    · intro a' ha' b' hb' hab
      have e1 := hE1 b' (hIsub hb')
      have e2 := hE1 a' (hIsub ha')
      have h3 := hdiff (hiu (2 + ρS)) a' ha' b' hb'
      have h4 := hdiff (hiu ρS) a' ha' b' hb'
      have h5 : ∫ t in a'..b', (2 + ρS) / u t = (∫ t in a'..b', ρS / u t) + ∫ t in a'..b', 2 / u t := by
        rw [← intervalIntegral.integral_add ((hiu ρS).mono_set (hsubI a' ha' b' hb'))
          ((hiu 2).mono_set (hsubI a' ha' b' hb'))]
        refine intervalIntegral.integral_congr fun t _ => ?_
        show (2 + ρS) / u t = ρS / u t + 2 / u t
        ring
      simp only [hWtdef]
      linarith
    · refine measure_mono_null (fun s hs => ?_) measure_empty
      exact absurd hs.2 (hune s hs.1)
    · intro a' ha' b' hb' hab
      have e1 := hE2 b' (hIsub hb')
      have e2 := hE2 a' (hIsub ha')
      have hiXu : IntervalIntegrable (fun t => 2 / X t + ρS / u t) volume 0 τ' := (hiX 2).add (hiu ρS)
      have h3 := hdiff hiXu a' ha' b' hb'
      have h4 := hdiff (hiu ρS) a' ha' b' hb'
      have h5 : ∫ t in a'..b', (2 / X t + ρS / u t) = (∫ t in a'..b', ρS / u t) +
          ∫ t in a'..b', Bessel.regDrift 2 m₁ (X t) := by
        rw [intervalIntegral.integral_add ((hiX 2).mono_set (hsubI a' ha' b' hb'))
          ((hiu ρS).mono_set (hsubI a' ha' b' hb')), add_comm]
        congr 1
        refine intervalIntegral.integral_congr fun t ht => ?_
        have htI : t ∈ Icc (0 : ℝ) τ' := by
          rw [uIcc_of_le hab] at ht; exact ⟨ha'.1.trans ht.1, ht.2.trans hb'.2⟩
        simp only [Bessel.regDrift_of_le (hXge t htI)]
      simp only [hWtdef]
      linarith
  -- uniform bounds and the level `L₀`
  set aP : ℝ → StateE 0 1 × ℝ := fun s =>
    (((0 : ℝ), (fun _ => u s + sk * Bt s), (fun _ => (0 : ℝ)), X s + sk * Bt s), Bt s) with haPdef
  have haPc : ContinuousOn aP (Icc 0 τ') := by
    have h1 : ContinuousOn (fun s => u s + sk * Bt s) (Icc 0 τ') :=
      (huc.mono hIsub).add (continuous_const.mul hBtc).continuousOn
    have h2 : ContinuousOn (fun s => X s + sk * Bt s) (Icc 0 τ') :=
      (hXc'.mono hIsub).add (continuous_const.mul hBtc).continuousOn
    refine ContinuousOn.prodMk (continuousOn_const.prodMk (ContinuousOn.prodMk ?_
      (continuousOn_const.prodMk h2))) hBtc.continuousOn
    exact continuousOn_pi.2 fun _ => h1
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn haPc
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (2 / m₁ + M₁ + M₁ / (X τ' / 2) + |M₂| + 1)
  refine ⟨L₀, fun L hL => ?_⟩
  have hLr : (L₀ : ℝ) ≤ L := by exact_mod_cast hL
  have hM₁pos : 0 < M₁ := lt_of_lt_of_le hm₁pos (hXge s₂ hs₂)
  have hLbig : 2 / m₁ + M₁ + M₁ / (X τ' / 2) + |M₂| + 1 < L := lt_of_lt_of_le hL₀ hLr
  have h2m : 0 ≤ 2 / m₁ := by positivity
  have h3m : 0 ≤ M₁ / (X τ' / 2) := by positivity
  have habs := abs_nonneg M₂
  have hLpos : (0 : ℝ) < L := by linarith
  set c : ℝ := 1 / (L : ℝ) with hcdef
  have hc : 0 < c := by positivity
  have h2c : 2 * c < m₁ := by
    have h1 : 2 / m₁ < L := by linarith
    rw [div_lt_iff₀ hm₁pos] at h1
    rw [hcdef, show 2 * (1 / (L : ℝ)) = 2 / L by ring, div_lt_iff₀ hLpos]
    linarith
  have hM₁L : M₁ < L := by linarith
  have hcM : M₁ * c < X τ' / 2 := by
    have h1 : M₁ / (X τ' / 2) < L := by linarith
    rw [div_lt_iff₀ hc₀] at h1
    rw [hcdef, show M₁ * (1 / (L : ℝ)) = M₁ / L by ring, div_lt_iff₀ hLpos]
    linarith
  have hM₂L : |M₂| < L := by linarith
  have hTτ : ((τ'.toNNReal : ℝ≥0) : ℝ) = τ' := Real.coe_toNNReal _ hτ'0.le
  have hBω : ∀ t : ℝ, B t.toNNReal ω = Bt t := fun t => by rw [hB]
  have hBc : Continuous fun t => B t ω := by
    have : (fun t : ℝ≥0 => B t ω) = fun t => bh (r + t) - bh r := funext hB
    rw [this]; exact (hbhc.comp (continuous_const.add continuous_id)).sub continuous_const
  -- the tamed force increment is the actual one
  set Z₁ : ℝ → ℝ := fun s => u s + sk * Bt s - u 0 with hZ₁def
  have hZ₁c : ContinuousOn Z₁ (Icc 0 τ') :=
    (((huc.mono hIsub).add (continuous_const.mul hBtc).continuousOn).sub continuousOn_const)
  have hU1 : ∀ s ∈ Icc (0 : ℝ) τ', tU1 sk ρS c g₀ B s.toNNReal ω = Z₁ s := by
    have hW1c : Continuous fun t => sk * B t ω - g₀ ω := (continuous_const.mul hBc).sub continuous_const
    have h := markFlow_eq_of_sol (W := fun t ω => sk * B t ω - g₀ ω) (ω := ω) (lipschitz_regDrift' hρS hc)
      (fun x => Bessel.abs_regDrift_le (by linarith) hc x) hW1c (T := τ'.toNNReal) (Z := Z₁)
      (by rw [hTτ]; exact hZ₁c) ?_
    · intro s hs
      rw [← hTτ] at hs
      exact h s hs
    · rw [hTτ]
      intro s hs
      have e1 := hE1 s (hIsub hs)
      have hcongr : ∫ t in (0 : ℝ)..s, Bessel.regDrift (2 + ρS) c (Z₁ t - (sk * B t.toNNReal ω - g₀ ω)) =
          ∫ t in (0 : ℝ)..s, (2 + ρS) / u t := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hs.1] at ht
        have htI : t ∈ Icc (0 : ℝ) τ' := ⟨ht.1, ht.2.trans hs.2⟩
        have hval : Z₁ t - (sk * B t.toNNReal ω - g₀ ω) = u t := by
          rw [hBω, hg, ← hu0]; simp only [hZ₁def]; ring
        rw [hval, Bessel.regDrift_of_le (by linarith [hugt t htI])]
      rw [hcongr]
      simp only [hZ₁def]
      linarith
  -- the tamed passive increment is the actual one
  set r' : ℝ := ρS / (2 + ρS) with hr'def
  set Z₂ : ℝ → ℝ := fun s => X s + sk * Bt s - y₀ - r' * Z₁ s with hZ₂def
  have hZ₂c : ContinuousOn Z₂ (Icc 0 τ') :=
    ((((hXc'.mono hIsub).add (continuous_const.mul hBtc).continuousOn).sub continuousOn_const).sub
      (continuousOn_const.mul hZ₁c))
  have hU2 : ∀ s ∈ Icc (0 : ℝ) τ', tU2 sk ρS c y₀ g₀ B s.toNNReal ω = Z₂ s := by
    obtain ⟨hU1c, -, -, -⟩ := tU_facts (sk := sk) (y₀ := y₀) (g₀ := g₀) hρS hc hBc
    have hW2c : Continuous fun t => sk * B t ω - y₀ - r' * tU1 sk ρS c g₀ B t ω :=
      ((continuous_const.mul hBc).sub continuous_const).sub (continuous_const.mul hU1c)
    have h := markFlow_eq_of_sol (W := fun t ω => sk * B t ω - y₀ - r' * tU1 sk ρS c g₀ B t ω)
      (ω := ω) (Bessel.lipschitzWith_regDrift (c := 2) (by norm_num) hc)
      (fun x => Bessel.abs_regDrift_le (by norm_num) hc x) hW2c (T := τ'.toNNReal) (Z := Z₂)
      (by rw [hTτ]; exact hZ₂c) ?_
    · intro s hs
      rw [← hTτ] at hs
      exact h s hs
    · rw [hTτ]
      intro s hs
      have e1 := hE1 s (hIsub hs)
      have e2 := hE2 s (hIsub hs)
      have hcongr : ∫ t in (0 : ℝ)..s, Bessel.regDrift 2 c (Z₂ t -
          (sk * B t.toNNReal ω - y₀ - r' * tU1 sk ρS c g₀ B t.toNNReal ω)) =
          ∫ t in (0 : ℝ)..s, 2 / X t := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hs.1] at ht
        have htI : t ∈ Icc (0 : ℝ) τ' := ⟨ht.1, ht.2.trans hs.2⟩
        have hval : Z₂ t - (sk * B t.toNNReal ω - y₀ - r' * tU1 sk ρS c g₀ B t.toNNReal ω) = X t := by
          rw [hBω, hU1 t htI]; simp only [hZ₂def]; ring
        rw [hval, Bessel.regDrift_of_le (by linarith [hXge t htI])]
      rw [hcongr]
      have hsI : ∀ f : ℝ → ℝ, IntervalIntegrable f volume 0 τ' → IntervalIntegrable f volume 0 s :=
        fun f hf => hf.mono_set (hsubI 0 ⟨le_rfl, hτ'0.le⟩ s hs)
      have hsplit : ∫ t in (0 : ℝ)..s, (2 / X t + ρS / u t) =
          (∫ t in (0 : ℝ)..s, 2 / X t) + ∫ t in (0 : ℝ)..s, ρS / u t :=
        intervalIntegral.integral_add (hsI _ (hiX 2)) (hsI _ (hiu ρS))
      have hr2 : r' * ∫ t in (0 : ℝ)..s, (2 + ρS) / u t = ∫ t in (0 : ℝ)..s, ρS / u t := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t _ => ?_
        show r' * ((2 + ρS) / u t) = ρS / u t
        have h2ρ : (2 + ρS) ≠ 0 := by linarith
        rw [hr'def, ← mul_div_assoc, div_mul_cancel₀ _ h2ρ]
      have h3 : r' * (u s + sk * Bt s - u 0) = ∫ t in (0 : ℝ)..s, ρS / u t := by
        rw [show u s + sk * Bt s - u 0 = ∫ t in (0 : ℝ)..s, (2 + ρS) / u t by linarith]
        exact hr2
      simp only [hZ₂def, hZ₁def]
      linarith
  -- the tamed path is the actual one on `[0, τ']`
  have hpath : ∀ t : ℝ≥0, (t : ℝ) ≤ τ' → statePath (tState sk ρS c y₀ g₀ B) B t ω = aP t := by
    intro t ht
    have htI : (t : ℝ) ∈ Icc (0 : ℝ) τ' := ⟨t.coe_nonneg, ht⟩
    have h1 := hU1 t htI
    have h2 := hU2 t htI
    rw [Real.toNNReal_coe] at h1 h2
    have hBt : B t ω = Bt t := by rw [← hBω, Real.toNNReal_coe]
    refine Prod.ext (Prod.ext rfl (Prod.ext (funext fun _ => ?_) (Prod.ext rfl ?_))) ?_
    · show g₀ ω + tU1 sk ρS c g₀ B t ω = u t + sk * Bt t
      rw [h1, hg, ← hu0]; simp only [hZ₁def]; ring
    · show y₀ + tU2 sk ρS c y₀ g₀ B t ω + ρS / (2 + ρS) * tU1 sk ρS c g₀ B t ω = X t + sk * Bt t
      rw [h1, h2]; simp only [hZ₂def, hr'def]; ring
    · exact hBt
  have hgapU : ∀ s, gapU sk 0 (aP s) = u s := fun s => by simp only [gapU, stW, haPdef]; ring
  have hgapX : ∀ s, gapX sk (aP s) = X s := fun s => by simp only [gapX, stW, haPdef]; ring
  have hnotC : ∀ t : ℝ≥0, (t : ℝ) < τ' → aP t ∉ exitC sk c L := by
    intro t ht hC
    have htI : (t : ℝ) ∈ Icc (0 : ℝ) τ' := ⟨t.coe_nonneg, ht.le⟩
    have hb := hbefore t ⟨t.coe_nonneg, ht⟩
    have hm := hmargin t htI
    have hxg := hXge t htI
    have hxl := hXle t htI
    have hn := hM₂ t htI
    have hXc : X t * c ≤ M₁ * c := mul_le_mul_of_nonneg_right hxl hc.le
    simp only [exitC, mem_ofPred_eq, hgapU, hgapX] at hC
    rcases hC with h | h | h | h | h
    · linarith
    · rw [← hcdef] at h; nlinarith
    · linarith
    · linarith
    · linarith [le_abs_self M₂]
  have hinC : aP τ' ∈ exitC sk c L := by
    simp only [exitC, mem_ofPred_eq, hgapU, hgapX]
    left; rw [hτ'eq]
  have hτN : τ'.toNNReal ≤ N := by
    rw [← NNReal.coe_le_coe, hTτ]; linarith [hτ'lt, hσN]
  have hhit : hitStop (tState sk ρS c y₀ g₀ B) B (exitC sk c L) N ω = τ'.toNNReal := by
    refine hittingBtwn_eq_of_first hτN ?_ ?_
    · rw [hpath _ (by rw [hTτ]), hTτ]; exact hinC
    · intro t ht
      have ht' : (t : ℝ) < τ' := by rw [← hTτ]; exact_mod_cast ht
      rw [hpath t ht'.le]; exact hnotC t ht'
  refine ⟨?_, ?_⟩
  · rw [hpath 0 (by simp [hτ'0.le])]
    exact hnotC 0 (by simpa using hτ'0)
  · rw [hhit, hpath _ (by rw [hTτ]), hTτ, hgapU, hgapX, hτ'eq]

end HitPath

end Aux25

end InteractingSLE
