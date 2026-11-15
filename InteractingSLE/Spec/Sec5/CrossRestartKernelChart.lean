/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux8Inf

/-!
# The counterflow restart chart is the reversed-slit chart of Proposition 4.9's chain, with the roles exchanged

Packet PROVE-CFRESTART (Lemma 4.7's and Lemma 5.7's proofs, pp. 118, 138: "We apply a conformal transformation
`ψ : 𝒮 ∖ η([0, σ]) → 𝒮` which fixes `±∞` and sends `η(σ)` to `0`").

The cross-conditioning chain of Proposition 4.9's direction (PROVE-GLUECOND3–10) works with a *new* curve, a Loewner
hull `K^α_t` from `0` in `ℍ`, and an *obstacle* `R(K^β_s)` (`R z = −1/z`) attached at `∞`, mapped out by the
reversed-slit chart `Ψ = revChart Wβ s = R ∘ f^β_s ∘ R` (which fixes `0` and sends the tip of the obstacle to `∞`).
In Lemma 4.7's direction the new curve is the counterflow `η′`, read in its own chart `M_q`
(`Sec4.stripCounterflowChart`; `M_q(z) = −1 − (1 + q)/z`, start `E(z₀) = −1 − q ↦ 0`), and the obstacle is the
`M_q`-image of the flow-line segment `K^U_σ = η((0, σ])` (chart `E`), which is attached at `M_q(0) = ∞`. The restart
chart of PROVE-SEC5-F/G is `Φ = restartMap q U σ x₁` (`x₁ = g_σ(−1 − q)`).

This file identifies the two pictures exactly:

* `cfMob q z = z/(z + 1 + q)` (`realMobius 1 0 1 (1 + q)`) satisfies `R ∘ cfMob = M_q` and `cfMob ∘ M_q⁻¹ = R`
  (`negInv_cfMob`, `cfMob_stripInv`): so the obstacle `M_q(K^U_σ)` is `R(cfMob(K^U_σ))`;
* **`exists_revChart_restartMap`**: `cfMob(K^U_σ)` is the Loewner hull `K^Ũ_{σ̃}` of a continuous driver `Ũ`
  (`Ũ 0 = 0`; PROVE-SEC5-F's Möbius image theorem), and **the restart chart is a positive dilation of the reversed-slit
  chart**: `Φ = c · revChart Ũ σ̃` on `ℍ ∖ M_q(K^U_σ)`, with `c = κ/(U_σ − x₁) > 0`;
* the hypotheses of the reversed-slit lemmas (Aux. 8 for an obstacle at `∞`, `Aux8Inf`; the transition map of
  `GlueCondUnionImg`) in terms of the restart data: the closure of `K^Ũ_{σ̃}` meets `ℝ` only at `0`
  (`ofReal_notMem_closure_cfMob_image`), and the closures of the counterflow hull and of the obstacle are disjoint
  (`disjoint_closure_cfHull_negInv`).

So every deterministic lemma of the Proposition 4.9 chain that does not use the simplicity of the new curve applies to
the counterflow in the restart chart with `(Wα, t) :=` (counterflow driver, time) and `(Wβ, s) := (Ũ, σ̃)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H fwdHull fwdMap)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open ConformalImage ConformalImageFull

/-! ### The Möbius map `z ↦ z/(z + 1 + q)` -/

section Mob

variable {q : ℝ}

/-- **The Möbius map `z ↦ z/(z + 1 + q)`**: `R ∘ cfMob q = M_q`; it fixes `0` and has its pole at `E(z₀) = −1 − q`. -/
abbrev cfMob (q : ℝ) : ℂ → ℂ := realMobius 1 0 1 (1 + q)

theorem cfMob_apply (q : ℝ) (z : ℂ) : cfMob q z = z / (z + (1 + q : ℝ)) := by
  simp [realMobius]

theorem mobPole_cfMob (q : ℝ) : mobPole 1 (1 + q) = -1 - q := by
  simp only [mobPole]; ring

theorem cfMob_det (hq : 0 < q) : 0 < (1 : ℝ) * (1 + q) - 0 * 1 := by linarith

/-- `R ∘ cfMob = M_q` (off `0` and the pole). -/
theorem negInv_cfMob {z : ℂ} (hz : z ≠ 0) :
    negInv (cfMob q z) = (Sec4.stripCounterflowChart q).1 z := by
  rw [cfMob_apply, Sec4.stripCounterflowChart_fwd, negInv]
  field_simp
  push_cast
  ring

/-- `cfMob ∘ M_q⁻¹ = R` (off `0` and `−1`). -/
theorem cfMob_stripInv (hq : 0 < q) {ξ : ℂ} (hξ : ξ ≠ 0) (hξ1 : ξ + 1 ≠ 0) :
    cfMob q (realMobius 0 (-(1 + q)) 1 1 ξ) = negInv ξ := by
  have hq1 : (1 + q : ℂ) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.2 (by linarith)
  rw [cfMob_apply, negInv]
  simp only [realMobius, ofReal_zero, zero_mul, zero_add, ofReal_one, one_mul, ofReal_neg, ofReal_add]
  have h1 : -(1 + (q : ℂ)) / (ξ + 1) + (1 + q) = (1 + q) * ξ / (ξ + 1) := by
    field_simp; ring
  rw [h1]
  field_simp

end Mob

/-! ### The restart chart as a dilation of the reversed-slit chart -/

section Chart

variable {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ}

/-- **The restart chart is a positive dilation of the reversed-slit chart of a Loewner hull at `∞`.** Let `U`
(continuous, `U 0 = 0`) drive the flow line in the chart `E` up to time `σ ≥ 0`, with a ball around the counterflow
start `−1 − q` (`q > 0`) disjoint from `K^U_σ`, and `x₁ = g_σ(−1 − q)` the boundary value there. Then there are a
continuous driver `Ũ` with `Ũ 0 = 0`, a time `σ̃ ≥ 0` and a constant `c > 0` such that
* `K^Ũ_{σ̃} = cfMob q (K^U_σ)`, i.e. the obstacle `M_q(K^U_σ)` of the counterflow chart is `R(K^Ũ_{σ̃})`;
* for every point `ξ` of `ℍ` whose `E`-image `M_q⁻¹ ξ` is off `K^U_σ`: `restartMap q U σ x₁ ξ = c · revChart Ũ σ̃ ξ`.
-/
theorem exists_revChart_restartMap (hq : 0 < q) (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {r : ℝ}
    (hr : 0 < r) (hd : Disjoint (ball ((-1 - q : ℝ) : ℂ) r) (fwdHull U σ)) (hx₁ : (x₁ : ℂ) = bdryVal U (-1 - q) σ) :
    ∃ (Ũ : ℝ → ℝ) (σ' c : ℝ), Continuous Ũ ∧ Ũ 0 = 0 ∧ 0 ≤ σ' ∧ 0 < c ∧
      fwdHull Ũ σ' = cfMob q '' fwdHull U σ ∧
      ∀ ξ ∈ H, realMobius 0 (-(1 + q)) 1 1 ξ ∉ fwdHull U σ →
        restartMap q U σ x₁ ξ = (c : ℂ) * revChart Ũ σ' ξ := by
  have hpole : mobPole 1 (1 + q) = -1 - q := mobPole_cfMob q
  have hp0 : mobPole 1 (1 + q) ≠ 0 := by rw [hpole]; linarith
  have hd' : Disjoint (ball ((mobPole 1 (1 + q) : ℝ) : ℂ) r) (fwdHull U σ) := by rw [hpole]; exact hd
  obtain ⟨σf, Ũ, α, κ, P, hŨc, hŨ0, hσf0, hσfm, -, hrel⟩ :=
    exists_loewner_mobius_image hU hU0 hσ (cfMob_det hq) one_ne_zero hp0 hr hd'
  obtain ⟨-, hK, hŨσ, hκ, hP, hmap⟩ := hrel σ ⟨hσ, le_rfl⟩
  have hPx : P σ = x₁ := by
    have : (P σ : ℂ) = x₁ := by rw [hP, hpole, hx₁]
    exact_mod_cast this
  have hx₁U : x₁ < U σ := by
    have := bdryVal_re_lt hU hU0 hσ hr hd (by linarith)
    rw [← hx₁] at this
    simpa using this
  have hσ' : 0 ≤ σf σ := by
    rw [← hσf0]; exact hσfm.monotoneOn ⟨le_rfl, hσ⟩ ⟨hσ, le_rfl⟩ hσ
  have hŨ0' : Ũ 0 = 0 := by rw [hŨ0]; simp
  set c : ℝ := κ σ / (U σ - x₁) with hc
  have hUx : 0 < U σ - x₁ := by linarith
  refine ⟨Ũ, σf σ, c, hŨc, hŨ0', hσ', div_pos hκ hUx, hK, fun ξ hξ hξK => ?_⟩
  -- the `E`-point and its forward image
  set z : ℂ := realMobius 0 (-(1 + q)) 1 1 ξ with hz
  have hzH : z ∈ H := by
    rw [hz, ← stripCounterflowChart_inv_eq_realMobius]
    exact Sec4.stripCounterflowChart_inv_mem_H hq hξ
  have hξ0 : ξ ≠ 0 := ne_zero_of_mem_H hξ
  have hξ1 : ξ + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [add_im, one_im, add_zero, zero_im] at this
    exact (ne_of_gt (show (0 : ℝ) < ξ.im from hξ)) this
  have hneg : negInv ξ = cfMob q z := (cfMob_stripInv hq hξ0 hξ1).symm
  set w : ℂ := gmap U σ z with hw
  have hwH : w ∈ H := by
    rw [hw, gmap]
    have := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ ⟨hzH, hξK⟩
    show 0 < (fwdMap U σ z + (U σ : ℂ)).im
    rw [add_im, ofReal_im, add_zero]
    exact this
  have hgm := hmap z ⟨hzH, hξK⟩
  -- the two charts as functions of `w`
  have hwU : w - (U σ : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [sub_im, ofReal_im, sub_zero, zero_im] at this
    exact (ne_of_gt (show (0 : ℝ) < w.im from hwH)) this
  have hwP : w - (x₁ : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [sub_im, ofReal_im, sub_zero, zero_im] at this
    exact (ne_of_gt (show (0 : ℝ) < w.im from hwH)) this
  have hUx' : (U σ : ℂ) - x₁ ≠ 0 := by
    rw [← ofReal_sub]; exact ofReal_ne_zero.2 hUx.ne'
  have hκ' : (κ σ : ℂ) ≠ 0 := ofReal_ne_zero.2 hκ.ne'
  have hfwd : fwdMap Ũ (σf σ) (cfMob q z) = (κ σ : ℂ) * (w - U σ) / ((U σ - x₁) * (w - x₁)) := by
    have e1 : fwdMap Ũ (σf σ) (cfMob q z) = gmap Ũ (σf σ) (cfMob q z) - Ũ (σf σ) := by
      rw [gmap]; ring
    rw [e1, hgm, ← hw, nf, hŨσ, hPx]
    push_cast
    field_simp
    ring
  rw [revChart, hneg, hfwd]
  show realMobius (-1) 0 1 (-(U σ - x₁)) (w - x₁) = (c : ℂ) * negInv _
  rw [realMobius, negInv, hc]
  push_cast
  have hden : (1 : ℂ) * (w - x₁) + -((U σ : ℂ) - x₁) = w - U σ := by ring
  rw [hden]
  field_simp
  ring

/-- **The restart chart is the source's map `ψ` followed by the counterflow chart of the mapped strip** (Lemma 5.7's
proof, p. 138: "`ψ : 𝒮 ∖ η([0, σ]) → 𝒮` which fixes `±∞` and sends `η(σ)` to `0`"). In the chart `E`, `ψ` is
`m ∘ g_σ` with the real affine map `m(w) = (w − U_σ)/(U_σ − y₁)` (`y₁ = g_σ(−1)`, the image of the strip end `−∞`;
`m` fixes `∞`, sends `y₁ ↦ −1` and the tip `U_σ ↦ 0`), and `Φ = M_Q ∘ ψ ∘ M_q⁻¹` with
`Q = (y₁ − x₁)/(U_σ − y₁)` (the moved counterflow start `ψ(z₀)` has `E`-image `m(x₁) = −1 − Q`). Pointwise: for every
`w ≠ U_σ`, `m₂(w − x₁) = M_Q(m(w))`, where `restartMap q U σ x₁ ξ = m₂(g_σ(M_q⁻¹ ξ) − x₁)`. -/
theorem restartMap_eq_stripChart {U : ℝ → ℝ} {σ x₁ y₁ : ℝ} (hy₁ : y₁ ≠ U σ) {w : ℂ} (hw : w ≠ (U σ : ℂ)) :
    realMobius (-1) 0 1 (-(U σ - x₁)) (w - x₁) =
      (Sec4.stripCounterflowChart ((y₁ - x₁) / (U σ - y₁))).1 ((w - U σ) / (U σ - y₁)) := by
  have hUy : (U σ : ℂ) - y₁ ≠ 0 := by
    rw [← ofReal_sub]; exact ofReal_ne_zero.2 (sub_ne_zero.2 hy₁.symm)
  have hwU : w - (U σ : ℂ) ≠ 0 := sub_ne_zero.2 hw
  rw [Sec4.stripCounterflowChart_fwd, realMobius]
  push_cast
  have hden : (1 : ℂ) * (w - x₁) + -((U σ : ℂ) - x₁) = w - U σ := by ring
  rw [hden]
  field_simp
  ring

/-- The restart chart sends the image `q` (in the chart `M_q`) of the strip end `−∞` to `Q = (y₁ − x₁)/(U_σ − y₁)`
when `y₁ = g_σ(−1)` (the value of `g_σ` at the `E`-image `−1 = M_q⁻¹(q)`). -/
theorem realMobius_stripInv_self (hq : 0 < q) : realMobius 0 (-(1 + q)) 1 1 (q : ℂ) = -1 := by
  have hq1 : (q : ℂ) + 1 ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.2 (by linarith)
  simp only [realMobius, ofReal_zero, zero_mul, zero_add, ofReal_one, one_mul, ofReal_neg, ofReal_add]
  field_simp
  ring

end Chart

/-! ### The hypotheses of the reversed-slit lemmas from the restart data -/

section Hyp

variable {q : ℝ}

/-- `cfMob q` is continuous off its pole. -/
theorem continuousOn_cfMob (q : ℝ) : ContinuousOn (cfMob q) {z | z + (1 + q : ℝ) ≠ 0} := by
  intro z hz
  have : (fun z : ℂ => z / (z + (1 + q : ℝ))) = cfMob q := funext fun z => (cfMob_apply q z).symm
  rw [← this]
  exact (continuousAt_id.div (continuousAt_id.add continuousAt_const) hz).continuousWithinAt

/-- A real point is sent by `cfMob q` to a real point (off the pole). -/
theorem cfMob_ofReal (q x : ℝ) : cfMob q x = ((x / (x + (1 + q)) : ℝ) : ℂ) := by
  rw [cfMob_apply]; push_cast; ring

/-- `cfMob q z` is real only for real `z` (off the pole), and it vanishes only at `0`. -/
theorem im_cfMob (q : ℝ) (z : ℂ) :
    (cfMob q z).im = (1 + q) * z.im / Complex.normSq (z + (1 + q : ℝ)) := by
  rw [cfMob_apply, div_im]
  simp only [add_re, add_im, ofReal_re, ofReal_im, add_zero]
  rw [Complex.normSq_apply]
  simp only [add_re, add_im, ofReal_re, ofReal_im, add_zero]
  field_simp
  ring

/-- **The closure of `cfMob(K)` meets `ℝ` only at `0`** when the closure of `K` meets `ℝ` only at `0` and avoids the
pole `−1 − q` (`q > 0`; `K` bounded). -/
theorem ofReal_notMem_closure_cfMob_image (hq : 0 < q) {K : Set ℂ} (hKb : Bornology.IsBounded K)
    (hKp : ((-1 - q : ℝ) : ℂ) ∉ closure K) (hK0 : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure K) :
    ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (cfMob q '' K) := by
  intro x hx hxc
  have hcpt : IsCompact (closure K) := hKb.isCompact_closure
  have hcont : ContinuousOn (cfMob q) (closure K) := (continuousOn_cfMob q).mono fun z hz h => by
    apply hKp
    have : z = ((-1 - q : ℝ) : ℂ) := by
      rw [show ((-1 - q : ℝ) : ℂ) = -((1 + q : ℝ) : ℂ) by push_cast; ring]
      exact eq_neg_of_add_eq_zero_left h
    rw [← this]; exact hz
  have hsub : closure (cfMob q '' K) ⊆ cfMob q '' closure K :=
    closure_minimal (image_mono subset_closure) (hcpt.image_of_continuousOn hcont).isClosed
  obtain ⟨y, hy, hyx⟩ := hsub hxc
  have hyp : y + (1 + q : ℝ) ≠ 0 := fun h => by
    apply hKp
    have : y = ((-1 - q : ℝ) : ℂ) := by
      rw [show ((-1 - q : ℝ) : ℂ) = -((1 + q : ℝ) : ℂ) by push_cast; ring]
      exact eq_neg_of_add_eq_zero_left h
    rw [← this]; exact hy
  have hns : 0 < Complex.normSq (y + (1 + q : ℝ)) := Complex.normSq_pos.2 hyp
  have him : y.im = 0 := by
    have h1 : (cfMob q y).im = 0 := by rw [hyx]; simp
    rw [im_cfMob] at h1
    have h2 : (1 + q) * y.im = 0 := by
      rcases div_eq_zero_iff.1 h1 with h | h
      · exact h
      · exact absurd h hns.ne'
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · exact h
  have hyr : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hy0 : y.re = 0 := by
    by_contra hne
    exact hK0 y.re hne (hyr ▸ hy)
  apply hx
  have : cfMob q y = 0 := by rw [hyr, hy0]; simp [cfMob_apply]
  rw [hyx] at this
  exact_mod_cast this

/-- **The counterflow hull and the obstacle have disjoint closures** (the hypothesis `hdis` of the reversed-slit
lemmas): if `Kt = cfMob(K)` with `K ⊆ ℍ`, and `K′` is bounded with `−1` off its closure, then the closures of `K′`
and of the obstacle `R(Kt) = M_q(K)` are disjoint as soon as the closures of `K` and of the `E`-image `M_q⁻¹(K′)`
are (the restart condition `IsRestartAlive.far₂`). -/
theorem disjoint_closure_cfHull_negInv (hq : 0 < q) {K K' Kt : Set ℂ} (hKt : Kt = cfMob q '' K)
    (hKH : K ⊆ H) (hK'1 : (-1 : ℂ) ∉ closure K')
    (hdis : Disjoint (closure K) (closure (realMobius 0 (-(1 + q)) 1 1 '' K'))) :
    Disjoint (closure K') (closure (negInv '' Kt)) := by
  set M : ℂ → ℂ := realMobius 0 (-(1 + q)) 1 1 with hM
  have hMc : ∀ ξ : ℂ, ξ + 1 ≠ 0 → ContinuousAt M ξ := fun ξ hξ => by
    have e : M = fun z : ℂ => (0 * z + ((-(1 + q) : ℝ) : ℂ)) / (1 * z + 1) := by
      funext z; simp [hM, realMobius]
    rw [e]
    exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const) (by simpa using hξ)
  rw [Set.disjoint_left]
  intro ξ hξ' hξ
  have hξ1 : ξ + 1 ≠ 0 := fun h => hK'1 (by rwa [show ξ = -1 from eq_neg_of_add_eq_zero_left h] at hξ')
  have h1 : M ξ ∈ closure (M '' K') := mem_closure_image (hMc ξ hξ1) hξ'
  have hsub : M '' (negInv '' Kt) ⊆ K := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    rw [hKt] at hv
    obtain ⟨y, hy, rfl⟩ := hv
    have hyH : 0 < y.im := hKH hy
    have hy0 : y ≠ 0 := ne_zero_of_mem_H (hKH hy)
    rw [negInv_cfMob hy0, hM, ← stripCounterflowChart_inv_eq_realMobius,
      Sec4.stripCounterflowChart_inv_fwd hq hy0]
    exact hy
  have h2 : M ξ ∈ closure K := closure_mono hsub (mem_closure_image (hMc ξ hξ1) hξ)
  exact Set.disjoint_left.1 hdis h2 h1

end Hyp

end InteractingSLE.Sec5.CrossRestart
