/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketJordanChange
import InteractingSLE.Spec.Sec6.Aux40InfJordan

/-!
# The change pocket opening at the flow seed: Jordan coordinate at infinity in the counterflow chart

Packet PROVE-STRIPSYS17 (specification §7.4.1, end of the proof of Aux. lemma 130, p. 412: "If `x₀ = x` or `y₀ = y`,
the same Jordan argument applies in the compactified domain. […] In the first case the terminal visit may be at
infinite ambient capacity"; Aux. lemmas 40–41 at infinity, `Sec6.IsReversePocketInf`).

When the opening contact `x₀` of the change pocket is the flow seed `0` (`openPt = −1` in the disc), the inverted
pocket `m(C)` is unbounded: its junction is `m(0) = ∞`. A two-point uniformizer `Ψ` of the Cayley image (`−1 ↦ 0`,
`cayley y₀ ↦ ∞`) then gives a Jordan coordinate at infinity of `m(C)` (`Sec6.IsJordanCoordInf`: continuous and
injective on the whole closure, `m(y₀) ↦ 0`, `∞ ↦ ∞`), by the same formula `cfCoord a Ψ q` as in the bounded case: no
point of the closed half-plane is sent to `−1` by `−cayley`.

## Main results

* **`isJordanCoordInf_cfCoord`** (generic);
* **`IsChangeConfigInc.exists_isJordanCoordInf_cfPocket`**: the change pocket opening at the flow seed has a Jordan
  coordinate at infinity in the counterflow chart.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketJordan

/-- `−cayley` never takes the value `−1` on the closed half-plane. -/
theorem neg_cayley_ne_neg_one {z : ℂ} (hz : z ∈ Hbar) : -cayley z ≠ -1 := fun h =>
  QuantumZipper.CA.cayley_ne_one (add_I_ne_zero_of_mem_Hbar hz) (neg_injective (h.trans rfl))

/-- **The Jordan coordinate at infinity of the inverted pocket.** Let `C ⊆ ℍ` be open and let `Ψ` be a two-point
uniformizer of its Cayley image with its boundary extension, `−1 ↦ 0` (the pocket opens at the flow seed) and
`q ↦ ∞` (`q ≠ −1` on the frontier). For every `a > 0`, `cfCoord a Ψ q` is a Jordan coordinate at infinity of `m(C)`
sending `cfPt q = m(y₀)` to `0`. -/
theorem isJordanCoordInf_cfCoord {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) {q : ℂ} {Ψ : ℂ → ℂ}
    (hU : IsBdryUniformizer (cayley '' C) (-1) q Ψ) (hp : (-1 : ℂ) ∈ frontier (cayley '' C))
    (hq : q ∈ frontier (cayley '' C)) (hq1 : q ≠ -1) {a : ℝ} (ha : 0 < a) :
    Sec6.IsJordanCoordInf (negInv '' C) (cfPt q) (cfCoord a Ψ q) := by
  set D := cayley '' C with hD
  set C' := negInv '' C with hC'
  have hDo : IsOpen D := Lemma71F.isOpen_cayley_image hCo hCH
  have hpc : (-1 : ℂ) ∈ closure D := frontier_subset_closure hp
  have hpq : (-1 : ℂ) ≠ q := fun h => hq1 h.symm
  have hqD : q ∉ D := by
    rw [hDo.frontier_eq] at hq
    exact hq.2
  have hC'H : closure C' ⊆ Hbar := closure_image_negInv_subset_Hbar hCH
  have hmaps : MapsTo (fun z => -cayley z) (closure C') (closure D \ {-1}) := fun z hz =>
    ⟨neg_cayley_mem_closure hCH hz, neg_cayley_ne_neg_one (hC'H hz)⟩
  have hFc : ContinuousOn (fun z => -cayley z) (closure C') := continuousOn_neg_cayley.mono hC'H
  refine ⟨(continuousOn_cfMap hU ha hpc hpq).comp hFc hmaps,
    (injOn_cfMap hU ha hpc hpq).comp (injOn_neg_cayley.mono hC'H) hmaps,
    (mapsTo_cfMap hU ha).comp hmaps, ?_, ?_, ?_, ?_⟩
  · -- conformal bijection
    have hcomp := isConformalBijection_comp isConformalBijection_negInv_H
      (isConformalBijection_comp (isConformalBijection_ofReal_mul ha)
        (isConformalBijection_comp hU.conf (isConformalBijection_neg_cayley hCH)))
    have heq : EqOn (cfCoord a Ψ q) (negInv ∘ (fun z => (a : ℂ) * z) ∘ Ψ ∘ fun z => -cayley z) C' := by
      intro z hz
      have hzD : -cayley z ∈ D := by
        rw [hD, ← image_neg_cayley_image_negInv hCH]
        exact mem_image_of_mem _ hz
      have hzq : -cayley z ≠ q := fun h => hqD (h ▸ hzD)
      simp only [cfCoord, cfMap_of_ne hzq, comp_apply]
    exact ⟨hcomp.1.congr fun z hz => heq hz, hcomp.2.congr heq.symm⟩
  · -- real on the frontier
    intro z hz
    have hF := neg_cayley_mem_frontier hCo hCH hz
    by_cases hzq : -cayley z = q
    · simp only [cfCoord, hzq, cfMap_self, zero_im]
    · simp only [cfCoord]
      rw [cfMap_of_ne hzq]
      refine im_negInv_eq_zero ?_
      rw [im_ofReal_mul, hU.im_eq_zero hDo hqD hF hzq, mul_zero]
  · -- `m(y₀) ↦ 0`
    simp only [cfCoord, neg_cayley_cfPt hq1, cfMap_self]
  · -- `∞ ↦ ∞`
    rw [← tendsto_norm_atTop_iff_cobounded]
    set l := cobounded ℂ ⊓ 𝓟 (closure C') with hl
    have hFt : Tendsto (fun z => -cayley z) l (𝓝 (-1)) :=
      (QuantumZipper.CA.tendsto_cayley_cobounded.neg).mono_left inf_le_left
    have hev : ∀ᶠ z in l, -cayley z ∈ closure D \ {q} ∧ -cayley z ≠ -1 := by
      have h1 : ∀ᶠ z in l, -cayley z ≠ q := hFt (isOpen_compl_singleton.mem_nhds hpq)
      have h2 : ∀ᶠ z in l, z ∈ closure C' := (eventually_principal.2 fun _ hz => hz).filter_mono inf_le_right
      filter_upwards [h1, h2] with z hz1 hz2
      exact ⟨⟨(hmaps hz2).1, hz1⟩, (hmaps hz2).2⟩
    have hFt' : Tendsto (fun z => -cayley z) l (𝓝[closure D \ {q}] (-1)) :=
      tendsto_nhdsWithin_iff.2 ⟨hFt, hev.mono fun z hz => hz.1⟩
    have hΨ0 : Tendsto (fun z => Ψ (-cayley z)) l (𝓝 0) := by
      have := (hU.cont (-1) ⟨hpc, hpq⟩).tendsto.comp hFt'
      rwa [hU.zero] at this
    have hpos : Tendsto (fun z => a * ‖Ψ (-cayley z)‖) l (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hev.mono fun z hz => ?_⟩
      · have := (hΨ0.norm).const_mul a
        rwa [norm_zero, mul_zero] at this
      · exact mul_pos ha (norm_pos_iff.2 (hU.ne_zero hpc hpq hz.1 hz.2))
    refine (tendsto_inv_nhdsGT_zero.comp hpos).congr' (hev.mono fun z hz => ?_)
    simp only [comp_apply, cfCoord]
    exact (norm_cfMap_of_ne ha hz.1.2).symm

end InteractingSLE.Sec7.PocketJordan

namespace InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc

open WangWu Lemma71I PocketJordan

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **The change pocket opening at the flow seed has a Jordan coordinate at infinity in the counterflow chart**
(`openPt = −1`, i.e. `rightLo = 0`): `m(y₀) ↦ 0`, `∞ ↦ ∞`. The coordinate is `cfCoord a Ψ q` for the two-point
uniformizer `Ψ` of the Cayley image and any `a > 0`. -/
theorem isJordanCoordInf_cfCoord (h : IsChangeConfigInc R L r) (h0 : openPt R L r = -1) {Ψ : ℂ → ℂ}
    (hU : IsBdryUniformizer (cayley '' changePocket R L r) (openPt R L r) (closePt R L r) Ψ) {a : ℝ}
    (ha : 0 < a) :
    Sec6.IsJordanCoordInf (cfPocket R L r) (cfPt (closePt R L r)) (cfCoord a Ψ (closePt R L r)) := by
  rw [h0] at hU
  exact PocketJordan.isJordanCoordInf_cfCoord h.isOpen_changePocket h.changePocket_subset_H hU
    (h0 ▸ h.openPt_mem_frontier) h.closePt_mem_frontier h.closePt_ne_neg_one ha

/-- The opening contact is the flow seed exactly when its right-wall parameter is `0`. -/
theorem openPt_eq_neg_one_iff (h : IsChangeConfigInc R L r) : openPt R L r = -1 ↔ rightLo R L r = 0 := by
  constructor
  · intro he
    exact h.isDiscCrosscut_right.inj h.changeCorner_props.1 ⟨le_rfl, zero_le_one⟩
      (he.trans h.isDiscCrosscut_right.zero.symm)
  · intro he
    rw [openPt, he]
    exact h.isDiscCrosscut_right.zero

/-- **The change pocket opening at the flow seed has a Jordan coordinate at infinity** in the counterflow chart. -/
theorem exists_isJordanCoordInf_cfPocket (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) :
    ∃ ψ : ℂ → ℂ, Sec6.IsJordanCoordInf (cfPocket R L r) (cfPt (closePt R L r)) ψ := by
  obtain ⟨Ψ, hU⟩ := h.exists_isBdryUniformizer
  exact ⟨_, h.isJordanCoordInf_cfCoord (h.openPt_eq_neg_one_iff.2 h0) hU one_pos⟩

end InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc
