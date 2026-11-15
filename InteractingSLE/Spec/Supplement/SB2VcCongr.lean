/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinConfig

/-!
# SB2(1)'s relative chain depends on the lift only up to the time read

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The record's lift `γ` agrees with the
flow's lift `Vc.liftOf` below the horizon (`Vc.ae_lineGeom_liftOf`); the chain clauses then hold for `liftOf`:

* `capClock_congr`: the capacity clock at `s` only sees the lift on `[0, s]`;
* **`IsSB2RelChain.congr_lift`**: a relative chain on `[0, S₀]` for `γ₁` is one for any `γ₂` equal to `γ₁` on
  `[0, S₀]`.

Deterministic; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace InteractingSLE.Theorem14.SB.Vc

/-- **The capacity clock at `s` only sees the lift on `[0, s]`.** -/
theorem capClock_congr {γ₁ γ₂ : ℝ≥0 → ℂ} {s : ℝ} (h : ∀ r : ℝ≥0, r ≤ s.toNNReal → γ₁ r = γ₂ r) :
    Sec7.Lemma71C.capClock (fun r : ℝ => γ₁ r.toNNReal) s = Sec7.Lemma71C.capClock (fun r : ℝ => γ₂ r.toNNReal) s := by
  unfold Sec7.Lemma71C.capClock
  congr 3
  refine image_congr fun r hr => h _ (Real.toNNReal_le_toNNReal hr.2)

/-- **A relative chain transfers to any lift equal on `[0, S₀]`.** -/
theorem IsSB2RelChain.congr_lift {A : Set ℂ} {c : Chart} {β' γ₁ γ₂ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ : ℝ}
    {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} (h : FinRel.IsSB2RelChain A c β' γ₁ tL S₀ Wr ηr)
    (heq : ∀ r : ℝ≥0, r ≤ S₀.toNNReal → γ₁ r = γ₂ r) :
    FinRel.IsSB2RelChain A c β' γ₂ tL S₀ Wr ηr := by
  have hcap : EqOn (Sec7.Lemma71C.capClock fun r : ℝ => γ₁ r.toNNReal)
      (Sec7.Lemma71C.capClock fun r : ℝ => γ₂ r.toNNReal) (Icc 0 S₀) := fun s hs =>
    capClock_congr fun r hr => heq r (hr.trans (Real.toNNReal_le_toNNReal hs.2))
  have hcap0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ₁ r.toNNReal) 0 =
      Sec7.Lemma71C.capClock (fun r : ℝ => γ₂ r.toNNReal) 0 :=
    capClock_congr fun r hr => heq r (hr.trans (by simp))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, by rw [← hcap0]; exact h4, h5.congr hcap, h6.congr hcap.symm, fun s hs => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h7 s hs
  have hs' : s.toNNReal ≤ S₀.toNNReal := Real.toNNReal_le_toNNReal hs.2
  have himg : γ₁ '' Icc 0 s.toNNReal = γ₂ '' Icc 0 s.toNNReal :=
    image_congr fun r hr => heq r (hr.2.trans hs')
  rw [← hcap hs]
  exact ⟨a1, by rw [a2]; exact heq _ hs', by rw [a3, himg], a4, a5⟩

end InteractingSLE.Theorem14.SB.Vc
