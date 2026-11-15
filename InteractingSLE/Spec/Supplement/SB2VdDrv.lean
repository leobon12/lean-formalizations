/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinConfig
import InteractingSLE.Spec.Sec7.PocketTraversalErase

/-!
# SB2(1)'s version half: the flow's lift is a driven curve

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The version's driver `W`, trace `Γ` and
relative lifetime `Vg` come from `Lk.exists_measurable_driver_of_drivenCurves`, which needs a driven curve
(`PocketTraversal.IsDrivenCurve`: continuous on `[0, ∞)`, from `0`, local Loewner drivers in the capacity clock). The
lift `γ` of the remainder lives on the remaining life `[0, ℓ)`:

* `liftR γ`: the lift as a curve of a real parameter (`r ↦ γ r⁺`); `image_liftR`;
* **`isDrivenCurve_liftR`**: if `ℓ = ∞`, a continuous lift from `0` carrying a relative chain on every `[0, S₀]` is
  a driven curve;
* **`isDrivenCurve_relCurve_liftR`**: if `ℓ < ∞`, the reparametrization `relCurve (liftR γ) ℓ` of `[0, ℓ)` onto
  `[0, ∞)` is a driven curve (`PocketTraversal.isDrivenCurve_relCurve`).

The relative chains are those of the chain records (`FinRel.IsSB2RelChain`, transferred to the flow's lift by
`Vc.IsSB2RelChain.congr_lift`). Deterministic; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vd

open Sec7.PocketTraversal

/-- The lift as a curve of a real parameter. -/
def liftR (γ : ℝ≥0 → ℂ) : ℝ → ℂ := fun r => γ r.toNNReal

theorem image_liftR (γ : ℝ≥0 → ℂ) {t : ℝ} (ht : 0 ≤ t) : liftR γ '' Icc 0 t = γ '' Icc 0 t.toNNReal := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal hr.2⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, ⟨s.2, ?_⟩, by simp [liftR]⟩
    have := NNReal.coe_le_coe.2 hs.2
    rwa [Real.coe_toNNReal _ ht] at this

/-- The driver data of a relative chain, in the form of `IsDrivenCurve`'s local drivers. -/
theorem localDriver_of_chain {A : Set ℂ} {c : Chart} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ : ℝ} {Wr : ℝ → ℝ}
    {ηr : ℝ → ℂ} (h : FinRel.IsSB2RelChain A c β' γ tL S₀ Wr ηr) :
    Continuous Wr ∧ Wr 0 = 0 ∧ Sec7.Lemma71C.capClock (liftR γ) 0 = 0 ∧
      StrictMonoOn (Sec7.Lemma71C.capClock (liftR γ)) (Icc 0 S₀) ∧
      ContinuousOn (Sec7.Lemma71C.capClock (liftR γ)) (Icc 0 S₀) ∧
      ∀ t ∈ Icc 0 S₀, 0 ≤ Sec7.Lemma71C.capClock (liftR γ) t ∧
        QuantumZipper.fwdHull Wr (Sec7.Lemma71C.capClock (liftR γ) t) = fillH (liftR γ '' Icc 0 t) := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h4, h5, h6, fun t ht => ⟨(h7 t ht).1, ?_⟩⟩
  rw [image_liftR γ ht.1]
  exact (h7 t ht).2.2.1

/-- **An infinite remaining life: the lift is a driven curve.** -/
theorem isDrivenCurve_liftR {γ : ℝ≥0 → ℂ} (hc : Continuous γ) (hγ0 : γ 0 = 0)
    (hchain : ∀ S₀ : ℝ, 0 < S₀ → ∃ (A : Set ℂ) (c : Chart) (β' : ℝ≥0 → ℂ) (tL : ℝ≥0) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
      FinRel.IsSB2RelChain A c β' γ tL S₀ Wr ηr) :
    IsDrivenCurve (liftR γ) := by
  refine ⟨(hc.comp continuous_real_toNNReal).continuousOn, by simp [liftR, hγ0], fun S hS => ?_⟩
  obtain ⟨A, c, β', tL, Wr, ηr, hch⟩ := hchain S hS
  obtain ⟨h1, h2, h4, h5, h6, h7⟩ := localDriver_of_chain hch
  exact ⟨Wr, h1, h2, h4, h5, h6, h7⟩

/-- **A finite remaining life `ℓ`: the reparametrized lift is a driven curve.** -/
theorem isDrivenCurve_relCurve_liftR {γ : ℝ≥0 → ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hc : ∀ s : ℝ≥0, (s : ℝ) < ℓ → ContinuousAt γ s) (hγ0 : γ 0 = 0)
    (hchain : ∀ S₀ : ℝ, 0 < S₀ → S₀ < ℓ → ∃ (A : Set ℂ) (c : Chart) (β' : ℝ≥0 → ℂ) (tL : ℝ≥0) (Wr : ℝ → ℝ)
      (ηr : ℝ → ℂ), FinRel.IsSB2RelChain A c β' γ tL S₀ Wr ηr) :
    IsDrivenCurve (relCurve (liftR γ) ℓ) := by
  refine isDrivenCurve_relCurve hℓ (fun r hr => ?_) (by simp [liftR, hγ0]) fun S' hS'0 hS' => ?_
  · have hrr : ((r.toNNReal : ℝ≥0) : ℝ) < ℓ := by rw [Real.coe_toNNReal _ hr.1]; exact hr.2
    exact ((hc _ hrr).comp continuous_real_toNNReal.continuousAt).continuousWithinAt
  · obtain ⟨A, c, β', tL, Wr, ηr, hch⟩ := hchain S' hS'0 hS'
    obtain ⟨h1, h2, h4, h5, h6, h7⟩ := localDriver_of_chain hch
    exact ⟨Wr, h1, h2, Sec7.Lemma71C.capClock (liftR γ), h4, h5, h6, fun t ht => (h7 t ht).2⟩

end InteractingSLE.Theorem14.SB.Vd
