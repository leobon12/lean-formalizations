/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RefChain
import InteractingSLE.Spec.ZhanGT4.TwoTime2Ext

/-!
# A.1 on one reference space: the landed image data are the canonical ones

Packet PROVE-ZHAN-A1REF. The landed A.1 line (A10–A22, A15F, A15G) builds its image processes (`imgSelAux`,
`condW`, `condA`, the seeded coordinates) from `OwnData W A φ T a W'`, the output of Aux. lemma 8 on a horizon `T`
(`exists_ownData`). This file shows that every such image driver and clock agree with the canonical ones of
`A1RefChain` (for a curve started at `0`, the frame of the landed line), so the landed conditional laws are laws of the
canonical image processes of `A1RefCond` (up to the horizon):

* `hcapSet_fwdHull`: `hcap(K_σ) = 2σ` for every continuous driver (not only centred ones);
* **`isImgDrvOn_of_ownData`**: `OwnData` gives an image driver in the sense of `IsImgDrvOn`, and its clock is `imgClk`;
* **`imgDrv_eqOn_of_ownData`**: on a good horizon the landed image driver is the canonical image driver on
  `[0, a(T)]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Ref

open QuantumZipper (H)
open A2X ConformalImage

/-- **Half-plane capacity of a Loewner hull** for any continuous driver: `hcap(K_σ) = 2σ`. -/
theorem hcapSet_fwdHull {W : ℝ → ℝ} (hW : Continuous W) {σ : ℝ} (hσ : 0 ≤ σ) :
    hcapSet (QuantumZipper.fwdHull W σ) = 2 * σ := by
  set c := W 0
  set V : ℝ → ℝ := fun s => W s - c with hV
  have hVc : Continuous V := hW.sub continuous_const
  have hV0 : V 0 = 0 := sub_self _
  have hK : QuantumZipper.fwdHull W σ = affHomeo 1 one_pos c '' QuantumZipper.fwdHull V σ := by
    have h := ConformalImageFull.fwdHull_add_const V c σ
    simp only [hV, sub_add_cancel] at h
    rw [h]
    exact image_congr fun z _ => (ConformalImageFull.affHomeo_one_apply c z).symm
  have hKV := isHPHull_fwdHull hVc hσ
  rw [hK, hcapSet_eq (hKV.image_affHomeo one_pos)]
  have h1 := HPHull.hcap_affHomeo (x := c) ⟨_, hKV⟩ one_pos
  rw [one_pow, one_mul] at h1
  rw [h1, hcap_fwdHull hVc hV0 hσ]

theorem physHull_zero (w : ℝ → ℝ) (t : ℝ) : physHull 0 w t = QuantumZipper.fwdHull w t := by
  simp [physHull]

/-- **The landed image data (`OwnData`, Aux. lemma 8 on the horizon `T`) are canonical**: for curve `j` started at
`0` with centred driver `wj`, obstacle `K_k(τ) = physHull xk wk τ` and `φ = g_τ = physMap xk wk τ`, the image driver
`W'` is an image driver on `T` (`IsImgDrvOn`), and the clock `a` is the canonical clock on `[0, T]`. -/
theorem isImgDrvOn_of_ownData {wj wk : ℝ → ℝ} {xk τ T : ℝ} {a W' : ℝ → ℝ}
    (h : OwnData wj (physHull xk wk τ) (physMap xk wk τ) T a W') :
    IsImgDrvOn 0 wj xk wk τ T W' ∧ EqOn a (imgClk 0 wj xk wk τ) (Icc 0 T) := by
  have hEq : EqOn a (imgClk 0 wj xk wk τ) (Icc 0 T) := fun t ht => by
    rcases ht.1.eq_or_lt with h0 | hpos
    · rw [← h0, h.a0, imgClk_zero]
    have hat : 0 ≤ a t := by
      rw [← h.a0]; exact h.mono.monotoneOn ⟨le_rfl, h.pos.le⟩ ht ht.1
    simp only [imgClk, hpos, ↓reduceIte]
    rw [physHull_zero, ← h.img t ht, hcapSet_fwdHull h.contW' hat]
    ring
  refine ⟨⟨h.contW', ?_, fun t ht => ?_⟩, hEq⟩
  · obtain ⟨-, hR, -⟩ := h.rate 0 ⟨le_rfl, h.pos.le⟩ (physMap xk wk τ) (by
      have hE : (fun z => QuantumZipper.fwdMap wj 0 z + (wj 0 : ℂ)) '' physHull xk wk τ = physHull xk wk τ := by
        conv_rhs => rw [← image_id (physHull xk wk τ)]
        refine image_congr fun z hz => ?_
        have hz' : z ∈ H \ QuantumZipper.fwdHull wj 0 := by
          rw [QuantumZipper.RS.fwdHull_zero_eq_empty h.cont, sdiff_empty]; exact h.hull.1 hz
        rw [fwdMap_zero_eq h.cont h.zero (le_refl 0) hz', h.zero, id]
        simp
      rw [hE]; exact h.mapOut)
    rw [h.zero, h.a0] at hR
    simpa using hR
  · rw [← hEq ht, h.img t ht, physHull_zero]

/-- **On a good horizon the landed image driver is the canonical one** on `[0, a(T)]`. -/
theorem imgDrv_eqOn_of_ownData {wj wk : ℝ → ℝ} {ζj : ℝ≥0∞} {xk τ T : ℝ} {a W' : ℝ → ℝ}
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ)
    (hT : IsGoodTime 0 wj ζj xk wk τ T) (h : OwnData wj (physHull xk wk τ) (physMap xk wk τ) T a W') :
    EqOn (imgDrv 0 wj ζj xk wk τ) W' (Icc 0 (a T)) := by
  obtain ⟨hW', hEq⟩ := isImgDrvOn_of_ownData h
  rw [hEq ⟨hT.1.le, le_rfl⟩]
  exact imgDrv_eqOn hj hj0 hk hk0 hτ hT hW'

end InteractingSLE.ZhanGT4.A1Ref
