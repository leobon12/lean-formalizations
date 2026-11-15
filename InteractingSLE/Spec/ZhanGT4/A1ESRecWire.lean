/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ESRecCov
import InteractingSLE.Spec.ZhanGT4.A1ERecWire

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the record facts and `EightRectLawSndC`

Packet PROVE-A1-EIGHTSNDREC.

* **`eightSndRecordStatement`**: PROVE-A1-EIGHTSND's remaining input `EightSndRecordStatement κ` (the seven record
  facts `hSm`, `hstop`, `hgW`, `hgVL`, `hgVR`, `hgS`, `hcov` of `eightSndResStop`) holds for every `κ`
  (`A1ESRecCap`, `A1ESRecDrv`, `A1ESRecCov`);
* **`eightRectLawSndC`**: **`EightRectLawSndC κ`** for every `κ` (EIGHTSND's `eightRectLawSndC_of_records`);
* **`a1DualCouplingEightCoreStatement`**: with PROVE-A1-EIGHTREC's large direction `A1ERec.eightRectLawFstC`,
  A1CORE's **`A1DualCouplingEightCoreStatement κ`** for every `κ` (A1-RECTLAW2's
  `a1DualCouplingEightCoreStatement_of_dirsC`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` or Aux. 7.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESRec

open A1RLaw A1ESnd A1Patch

/-- **The record facts of the small (Eight) direction hold** (`EightSndRecordStatement κ` for every `κ`): at every
stop `τ` of the large curve's usual augmentation, the masked raw caps, the canonical image driver and the forces read,
before the cap, only the records `(S₁ᵐ, τ ∧ S₂ᵐ)` of the patched exits, and the caps exhaust the pre-contact clock
almost surely. -/
theorem eightSndRecordStatement (κ : ℝ) : EightSndRecordStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂'
    ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd G₁ G₂ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ τ hτ
  obtain ⟨-, -, -, h₂', hB₂', -, -⟩ := hp₂
  obtain ⟨-, -, -, h₁', hB₁', hg₁', -⟩ := hp₁
  -- the agreement in the orientation of the stopped-record lemmas (original = patched)
  have hagO₁ : ∀ x' ∈ G₁, (∀ t, W₁ t x' = W₁' t x') ∧ ζ₁ x' = ζ₁' x' := fun x' hx' =>
    ⟨fun t => ((hag₁ x' hx').1 t).symm, (hag₁ x' hx').2.2.2.2.symm⟩
  have hagO₂ : ∀ y' ∈ G₂, (∀ t, W₂ t y' = W₂' t y') ∧ (∀ i t, VL₂ i t y' = VL₂' i t y') ∧ ζ₂ y' = ζ₂' y' :=
    fun y' hy' => ⟨fun t => ((hag₂ y' hy').1 t).symm, fun i t => ((hag₂ y' hy').2.1 i t).symm,
      (hag₂ y' hy').2.2.2.2.symm⟩
  exact ⟨eightStop_hSm hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hagO₁ hagO₂,
    eightStop_hstop hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hagO₁ hagO₂,
    eightStop_hgW hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hagO₁ hagO₂,
    eightStop_hgVL hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hagO₁ hagO₂,
    eightStop_hgVR hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hagO₁ hagO₂,
    eightStop_hgS hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hagO₁ hagO₂,
    eightStop_hcov hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hG₁ hG₂ hG₁0 hG₂0 hagO₁ hagO₂ τ hμ₁ hμ₂⟩

/-- **`EightRectLawSndC κ` holds** (Zhan's A.1 under R83, (Eight), the small-curve direction), for every `κ`. -/
theorem eightRectLawSndC (κ : ℝ) : EightRectLawSndC κ :=
  eightRectLawSndC_of_records (eightSndRecordStatement κ)

/-- **A1CORE's Eight Core statement holds** for every `κ`: both directions of the C-form Eight law are proved
(`eightRectLawSndC` here, PROVE-A1-EIGHTREC's `A1ERec.eightRectLawFstC`). -/
theorem a1DualCouplingEightCoreStatement (κ : ℝ) : A1Canon.A1DualCouplingEightCoreStatement κ :=
  a1DualCouplingEightCoreStatement_of_dirsC (eightRectLawSndC κ) (A1ERec.eightRectLawFstC κ)

end InteractingSLE.ZhanGT4.A1ESRec
