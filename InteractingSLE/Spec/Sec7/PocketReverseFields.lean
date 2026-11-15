/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketReverseFieldsInf

/-!
# The counterflow fields of `IsReversePocket(Inf)` for the change pocket, from the walls' reverse visit order

Packet PROVE-STRIPSYS18 (specification §7.4.1, Aux. lemma 130's proof, p. 410: "Lemma 5.7 places them in the same
continuous counterflow range, in reverse first-visit order. […] For a point in the completed counterflow range let
`T(z)` be its first counterflow visit time. Distinct points of an incoming path have strictly decreasing `T` in its
incoming order"; Aux. lemmas 39–41, pp. 189–206; Lemma 7.25's proof, p. 414).

PROVE-STRIPSYS17 proved the topological fields of `Sec6.IsReversePocket` for the change pocket `m(C)` in the
counterflow chart `m(z) = −1/z` (`IsCfPocket`, bounded case) and this packet the ones of `Sec6.IsReversePocketInf`
(`IsCfPocketInf`, pocket opening at the flow seed). The remaining fields concern the counterflow `η` (a Loewner trace
from `0` in the chart `m`): its driver, the reverse visit orders of the two arcs, the earlier part `β` of the first
incoming path, and the first visits of `y₀`, `x₀`. Here:

* `β` is explicit: `cfBeta v = m(R̃(rightLo/(1 + v)))`, the right wall before `x₀` read backwards from `x₀` to the flow
  seed (`∞` in the chart `m`); its five topological fields are proved (`IsChangeConfigInc.cfBeta_props`);
* the reverse visit orders `rev₁`, `rev₂`, `rev_β` (resp. `rev₁`, `rev₂` at infinity) follow from **one order statement
  per wall**: points later along the wall (in its own flow time) are visited no later by the counterflow
  (`IsWallReverseVisit`, the reverse first-visit order of Lemma 5.7 / Proposition GB6 read in the chart `m`);
* the first visits `τ = T(y₀)`, `σ = T(x₀)` exist as soon as the walls' points are visited (`IsWallVisited`), by
  `exists_firstVisit`.

## Main results

* `firstHit`, `firstHit_spec`: the first hitting time of a visited point is its first visit;
* **`IsChangeConfigInc.isReversePocket_of_counterflow`**: `Sec6.IsReversePocket W η (cfPocket R L r)
  (cfArcR R L r) (cfArcL R L r) (cfBeta R L r) τ σ` with `τ`, `σ` the first hitting times of `m(y₀)`, `m(x₀)`
  (bounded case);
* **`IsChangeConfigInc.isReversePocketInf_of_counterflow`**: `Sec6.IsReversePocketInf W η (cfPocket R L r)
  (cfArcRInf R L r) (cfArcLInf R L r) τ`, `τ` the first hitting time of `m(y₀)` (the pocket opens at the flow seed).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketJordan

open WangWu PocketCoord Lemma71I

/-! ### First visits -/

/-- **The first hitting time** of a point `p` by a path `η` on `[0, ∞)` (`0` if `p` is never hit). -/
def firstHit (η : ℝ → ℂ) (p : ℂ) : ℝ := sInf {u ∈ Ici (0 : ℝ) | η u = p}

/-- **The first hitting time of a visited point** by a path continuous on `[0, ∞)` is its first visit. -/
theorem firstHit_spec {η : ℝ → ℂ} (hη : ContinuousOn η (Ici 0)) {p : ℂ} (hp : ∃ t, p ∈ η '' Icc 0 t) :
    0 ≤ firstHit η p ∧ η (firstHit η p) = p ∧ p ∉ η '' Ico 0 (firstHit η p) := by
  obtain ⟨t, s, hs, hsp⟩ := hp
  set S := {u ∈ Ici (0 : ℝ) | η u = p} with hSdef
  have hSne : S.Nonempty := ⟨s, hs.1, hsp⟩
  have hSb : BddBelow S := ⟨0, fun u hu => hu.1⟩
  have hSc : IsClosed S := hη.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
  have hmem : sInf S ∈ S := hSc.csInf_mem hSne hSb
  refine ⟨hmem.1, hmem.2, ?_⟩
  rintro ⟨u, hu, hup⟩
  exact absurd (csInf_le hSb ⟨hu.1, hup⟩) (not_le.2 hu.2)

/-- **The first visit of a visited point** by a path continuous on `[0, ∞)`. -/
theorem exists_firstVisit {η : ℝ → ℂ} (hη : ContinuousOn η (Ici 0)) {p : ℂ} (hp : ∃ t, p ∈ η '' Icc 0 t) :
    ∃ τ, 0 ≤ τ ∧ η τ = p ∧ p ∉ η '' Ico 0 τ :=
  ⟨_, firstHit_spec hη hp⟩

/-! ### The walls in the counterflow chart -/

section Wall

variable {R : ℝ≥0 → ℂ} {η : ℝ → ℂ}

/-- **The reverse visit order of a wall** in the counterflow chart: for flow times `0 < a ≤ b`, if the counterflow has
visited `m(R a)` by time `t`, it has visited `m(R b)` (points later along the flow line are visited no later). -/
def IsWallReverseVisit (R : ℝ≥0 → ℂ) (η : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, ∀ a b : ℝ≥0, 0 < a → a ≤ b → negInv (R a) ∈ η '' Icc 0 t → negInv (R b) ∈ η '' Icc 0 t

/-- **Every point of the wall after its seed is visited** by the counterflow (in the counterflow chart). -/
def IsWallVisited (R : ℝ≥0 → ℂ) (η : ℝ → ℂ) : Prop :=
  ∀ a : ℝ≥0, 0 < a → ∃ t, negInv (R a) ∈ η '' Icc 0 t

/-- The counterflow-chart image of an interior disc point of a wall. -/
theorem cfPt_toDisc_of_mem (hR : IsSimpleProper R) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    cfPt (toDisc (realPath R) s) = negInv (R (arcTime s).toNNReal) ∧ 0 < (arcTime s).toNNReal := by
  have ha : 0 < (arcTime s).toNNReal := Real.toNNReal_pos.2 (arcTime_pos hs)
  have hH : R (arcTime s).toNNReal ∈ H := hR.2.2.2.1 _ ha
  refine ⟨?_, ha⟩
  rw [toDisc_of_lt hs.2]
  exact cfPt_cayley (H_subset_Hbar' hH) (ne_zero_of_mem_H hH)

/-- **Reverse visit order along the disc parametrization of a wall** (points `s₁ ≤ s₂` in `(0, 1]`; the end `s = 1`
is the flow target, the counterflow seed `0`). -/
theorem wall_rev (hR : IsSimpleProper R) (hη0 : η 0 = 0) (hrev : IsWallReverseVisit R η) {s₁ s₂ : ℝ}
    (hs₁ : s₁ ∈ Ioc (0 : ℝ) 1) (hs₂ : s₂ ∈ Ioc (0 : ℝ) 1) (h12 : s₁ ≤ s₂) {t : ℝ}
    (h : cfPt (toDisc (realPath R) s₁) ∈ η '' Icc 0 t) : cfPt (toDisc (realPath R) s₂) ∈ η '' Icc 0 t := by
  rcases hs₂.2.lt_or_eq with hs₂1 | hs₂1
  · have hs₁1 : s₁ < 1 := h12.trans_lt hs₂1
    obtain ⟨e₁, ha⟩ := cfPt_toDisc_of_mem hR ⟨hs₁.1, hs₁1⟩
    obtain ⟨e₂, -⟩ := cfPt_toDisc_of_mem hR ⟨hs₂.1, hs₂1⟩
    rw [e₁] at h
    rw [e₂]
    refine hrev t _ _ ha (Real.toNNReal_le_toNNReal ?_) h
    exact strictMonoOn_arcTime.monotoneOn ⟨hs₁.1.le, hs₁1⟩ ⟨hs₂.1.le, hs₂1⟩ h12
  · obtain ⟨u, hu, -⟩ := h
    rw [hs₂1, toDisc_one, cfPt_one]
    exact ⟨0, ⟨le_rfl, hu.1.trans hu.2⟩, hη0⟩

/-- **Every disc point of a wall in `(0, 1]` is visited.** -/
theorem wall_visited (hη0 : η 0 = 0) (hR : IsSimpleProper R) (hvis : IsWallVisited R η) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) : ∃ t, cfPt (toDisc (realPath R) s) ∈ η '' Icc 0 t := by
  rcases hs.2.lt_or_eq with hs1 | hs1
  · obtain ⟨e, ha⟩ := cfPt_toDisc_of_mem hR ⟨hs.1, hs1⟩
    rw [e]
    exact hvis _ ha
  · rw [hs1, toDisc_one, cfPt_one]
    exact ⟨0, 0, ⟨le_rfl, le_rfl⟩, hη0⟩

end Wall

/-! ### The earlier part `β` of the right wall -/

section Change

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **The earlier part of the right wall, from `x₀` toward the flow seed** (`∞` in the counterflow chart):
`v ↦ m(R̃(rightLo/(1 + v)))` (the `β` of `Sec6.IsReversePocket`). -/
def cfBeta (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (v : ℝ) : ℂ := cfPt (toDisc (realPath R) (rightLo R L r / (1 + v)))

end Change

end InteractingSLE.Sec7.PocketJordan

namespace InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc

open WangWu Lemma71I PocketJordan

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **The topological fields of `β`** in the bounded case: continuous and injective on `[0, ∞)`, starting at the
junction `cfArcR 0 = m(x₀)`, tending to `∞`, in `ℍ`. -/
theorem cfBeta_props (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    ContinuousOn (cfBeta R L r) (Ici 0) ∧ InjOn (cfBeta R L r) (Ici 0) ∧ cfBeta R L r 0 = cfArcR R L r 0 ∧
      Tendsto (fun v => ‖cfBeta R L r v‖) atTop atTop ∧ ∀ v ∈ Ici (0 : ℝ), cfBeta R L r v ∈ H := by
  obtain ⟨-, hv, huv, -⟩ := h.changeCorner_props
  have hu0 := h.rightLo_pos h0
  have hu1 : rightLo R L r < 1 := huv.trans_le hv.2
  obtain ⟨hc, hi, ht, -, -⟩ := crosscut_arcInf_props h.isDiscCrosscut_right hu0 hu1.le
  refine ⟨hc, hi, ?_, ht, fun v hv' => ?_⟩
  · simp only [cfBeta, cfArcR, add_zero, div_one, zero_mul]
  · have hm := div_one_add_mem hu0 hv'
    exact cfPt_mem_H (h.isDiscCrosscut_right.mem_disc _ ⟨hm.1, hm.2.trans_lt hu1⟩)

/-- **`Sec6.IsReversePocket` for the change pocket in the counterflow chart** (bounded case), from the counterflow's
trace and the reverse visit order of the two walls with their points visited: the first visits `τ = T(y₀)`,
`σ = T(x₀)` are the first hitting times. -/
theorem isReversePocket_of_counterflow (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {W : ℝ → ℝ} {η : ℝ → ℂ} (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η) :
    Sec6.IsReversePocket W η (cfPocket R L r) (cfArcR R L r) (cfArcL R L r) (cfBeta R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) := by
  have hC := h.isCfPocket h0
  obtain ⟨hu, hv, huv, ha, hb, hab, -⟩ := h.changeCorner_props
  have hu0 := h.rightLo_pos h0
  have ha0 := h.leftLo_pos h0
  have hη0 : η 0 = 0 := trace.1
  obtain ⟨hβc, hβi, hβ0, hβt, hβH⟩ := h.cfBeta_props h0
  have hdR : ∀ s ∈ Icc (0 : ℝ) 1, rightLo R L r + s * (rightHi R L r - rightLo R L r) ∈ Ioc (0 : ℝ) 1 :=
    fun s hs => ⟨hu0.trans_le ((affine_mem huv).1 hs).1, ((affine_mem huv).1 hs).2.trans hv.2⟩
  have hdL : ∀ s ∈ Icc (0 : ℝ) 1, leftLo R L r + s * (leftHi R L r - leftLo R L r) ∈ Ioc (0 : ℝ) 1 :=
    fun s hs => ⟨ha0.trans_le ((affine_mem hab).1 hs).1, ((affine_mem hab).1 hs).2.trans hb.2⟩
  have hmR : ∀ s₁ s₂ : ℝ, s₁ ≤ s₂ → rightLo R L r + s₁ * (rightHi R L r - rightLo R L r) ≤
      rightLo R L r + s₂ * (rightHi R L r - rightLo R L r) := fun s₁ s₂ h12 => by
    have := mul_le_mul_of_nonneg_right h12 (sub_nonneg.2 huv.le)
    linarith
  have hmL : ∀ s₁ s₂ : ℝ, s₁ ≤ s₂ → leftLo R L r + s₁ * (leftHi R L r - leftLo R L r) ≤
      leftLo R L r + s₂ * (leftHi R L r - leftLo R L r) := fun s₁ s₂ h12 => by
    have := mul_le_mul_of_nonneg_right h12 (sub_nonneg.2 hab.le)
    linarith
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨hτ0, hτ, hτf⟩ := firstHit_spec trace.2.1 (wall_visited hη0 h.right hvisR (hdR 1 hone))
  obtain ⟨hσ0, hσ, hσf⟩ := firstHit_spec trace.2.1 (wall_visited hη0 h.right hvisR (hdR 0 hzero))
  refine hC.isReversePocket trace hW hW0 ?_ ?_ hβc hβi hβ0 hβt hβH ?_ hτ0 hσ0 hτ hτf hσ hσf
  · intro t v₁ hv₁ v₂ hv₂ h12 hvis
    exact wall_rev h.right hη0 hrevR (hdR v₁ hv₁) (hdR v₂ hv₂) (hmR v₁ v₂ h12) hvis
  · intro t v₁ hv₁ v₂ hv₂ h12 hvis
    exact wall_rev h.left hη0 hrevL (hdL v₁ hv₁) (hdL v₂ hv₂) (hmL v₁ v₂ h12) hvis
  · intro t s hs hvis
    have hm := div_one_add_mem hu0 hs
    have e : cfArcR R L r 0 = cfPt (toDisc (realPath R) (rightLo R L r)) := by
      simp only [cfArcR, zero_mul, add_zero]
    rw [e]
    exact wall_rev h.right hη0 hrevR ⟨hm.1, hm.2.trans (huv.le.trans hv.2)⟩ ⟨hu0, huv.le.trans hv.2⟩ hm.2 hvis

/-- **`Sec6.IsReversePocketInf` for the change pocket opening at the flow seed**, from the counterflow's trace and the
reverse visit order of the two walls with their points visited: `τ = T(y₀)` is the first hitting time of `m(y₀)`. -/
theorem isReversePocketInf_of_counterflow (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η)
    (hvisL : IsWallVisited L η) :
    Sec6.IsReversePocketInf W η (cfPocket R L r) (cfArcRInf R L r) (cfArcLInf R L r)
      (firstHit η (cfArcRInf R L r 0)) := by
  have hC := h.isCfPocketInf h0
  obtain ⟨-, hv, huv, -, hb, hab, -⟩ := h.changeCorner_props
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  have hu0 : 0 < rightHi R L r := h0 ▸ huv
  have hb0 : 0 < leftHi R L r := ha0 ▸ hab
  have hη0 : η 0 = 0 := trace.1
  have hdR : ∀ v ∈ Ici (0 : ℝ), rightHi R L r / (1 + v) ∈ Ioc (0 : ℝ) 1 := fun v hv' =>
    ⟨(div_one_add_mem hu0 hv').1, (div_one_add_mem hu0 hv').2.trans hv.2⟩
  have hdL : ∀ v ∈ Ici (0 : ℝ), leftHi R L r / (1 + v) ∈ Ioc (0 : ℝ) 1 := fun v hv' =>
    ⟨(div_one_add_mem hb0 hv').1, (div_one_add_mem hb0 hv').2.trans hb.2⟩
  have hanti : ∀ {u : ℝ}, 0 < u → ∀ v₁ ∈ Ici (0 : ℝ), ∀ v₂ ∈ Ici (0 : ℝ), v₁ ≤ v₂ → u / (1 + v₂) ≤ u / (1 + v₁) :=
    fun {u} hu v₁ hv₁ v₂ _ h12 => by
      have h1 : (0 : ℝ) < 1 + v₁ := by linarith [mem_Ici.1 hv₁]
      exact div_le_div_of_nonneg_left hu.le h1 (by linarith)
  obtain ⟨hτ0, hτ, hτf⟩ := firstHit_spec trace.2.1 (wall_visited hη0 h.right hvisR (hdR 0 self_mem_Ici))
  refine hC.isReversePocketInf trace hW hW0 ?_ ?_ (fun v hv' => wall_visited hη0 h.right hvisR (hdR v hv'))
    (fun v hv' => wall_visited hη0 h.left hvisL (hdL v hv')) hτ0 hτ hτf
  · intro t v₁ hv₁ v₂ hv₂ h12 hvis
    exact wall_rev h.right hη0 hrevR (hdR v₂ hv₂) (hdR v₁ hv₁) (hanti hu0 v₁ hv₁ v₂ hv₂ h12) hvis
  · intro t v₁ hv₁ v₂ hv₂ h12 hvis
    exact wall_rev h.left hη0 hrevL (hdL v₂ hv₂) (hdL v₁ hv₁) (hanti hb0 v₁ hv₁ v₂ hv₂ h12) hvis

end InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc
