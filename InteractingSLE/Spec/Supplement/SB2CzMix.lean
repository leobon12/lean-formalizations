/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LcdNested
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# A conditional GFF law moves from finer to coarser marks when the word is known to the coarser marks

Packet PROVE-SB2-CANON. The retained-law induction of SB2(2) produces the law of the field read in the canonical hull
chart given the completed line σ-algebra of a stage (`Fl.MvLaw`), while `Mz.TailCanonAt` asks for it given the
retained past `Ms.stageMarks ℓ`, which is coarser. **`ae_isGFF_of_le_fine`**: if `m ≤ m'`, `F ∈ m`, the word `β` is
almost surely constant under the regular conditional laws given `m` and sorted almost surely on `F`, and given `m'` the
field is almost surely on `F`
the GFF of the data of `β`, then given `m` it is too.

Proof: under the coarser law, the finer characteristic value at a test is almost surely the Gaussian value of the
word, which is constant in the fibre; by the tower identity the coarser characteristic value is the same number. So
the moduli agree at the countably many rational tests, and the two regular conditional laws of the field agree
(`Lcd.ae_map_condExpKernel_eq_of_norm_eq`).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.SB.Cz

open Restart

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A conditional GFF law moves from finer to coarser marks** when its sorted word is almost surely constant under
the coarser regular conditional laws. -/
theorem ae_isGFF_of_le_fine (hm : m ≤ m') (hm' : m' ≤ mΩ) {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : Measurable Y) {F : Set Ω} (hF : MeasurableSet[m] F) {β : Ω → BoundaryWord}
    (hβs : ∀ᵐ ω ∂P, ω ∈ F → (β ω).IsSorted) (hβk : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P m ω₀), β ω = β ω₀)
    (hlaw : ∀ᵐ ω ∂P, ω ∈ F → IsGFFWithBoundaryData (condExpKernel P m' ω) Y (β ω).fn (β ω).jumps) :
    ∀ᵐ ω ∂P, ω ∈ F → IsGFFWithBoundaryData (condExpKernel P m ω) Y (β ω).fn (β ω).jumps := by
  have hmΩ : m ≤ mΩ := hm.trans hm'
  have hk : ∀ k : RatComb, ∀ᵐ ω ∂P, ω ∈ F →
      ‖Lcd.condCF m' P Y (ratComb upperHalfPlaneOpens k) ω‖ =
        ‖Lcd.condCF m P Y (ratComb upperHalfPlaneOpens k) ω‖ := by
    intro k
    set φ := ratComb upperHalfPlaneOpens k with hφ
    set f : Ω → ℂ := fun x => Complex.exp (Complex.I * (Y x φ : ℂ)) with hfdef
    have hfm : Measurable f :=
      Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((Sobolev.measurable_distOn_apply φ).comp hY)))
    have hfb : ∀ x, ‖f x‖ ≤ 1 := fun x => by
      rw [hfdef, Complex.norm_exp]
      simp
    have hfi : Integrable f P :=
      Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall hfb)
    have htower := Lcd.ae_integral_integral_condExpKernel_eq hm hm' hfi
    have hlawk := KernelTower.ae_ae_condExpKernel_of_ae hmΩ hlaw
    have hsk := KernelTower.ae_ae_condExpKernel_of_ae hmΩ hβs
    have hmem := Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) hmΩ hF
    filter_upwards [htower, hlawk, hmem, hβk, hlaw, hsk, hβs] with ω₀ ht hl hmem0 hβ0 hl0 hs hs0 hω₀
    have hval : ∀ᵐ ω ∂(condExpKernel P m ω₀), (∫ x, f x ∂(condExpKernel P m' ω)) = gaussCF (β ω₀) φ := by
      filter_upwards [hl, hmem0 hω₀, hβ0, hs] with ω h1 h2 h3 h4
      rw [Exist.StagedLaw.integral_cexp_eq_gaussCF (h4 h2) (h1 h2), h3]
    have hc : (∫ ω, (∫ x, f x ∂(condExpKernel P m' ω)) ∂(condExpKernel P m ω₀)) = gaussCF (β ω₀) φ := by
      rw [integral_congr_ae hval, integral_const]
      simp
    have h0 : Lcd.condCF m' P Y φ ω₀ = gaussCF (β ω₀) φ :=
      Exist.StagedLaw.integral_cexp_eq_gaussCF (hs0 hω₀) (hl0 hω₀) φ
    have h1 : Lcd.condCF m P Y φ ω₀ = gaussCF (β ω₀) φ := by
      change ∫ x, f x ∂(condExpKernel P m ω₀) = _
      rw [← ht, hc]
    rw [h0, h1]
  have hmap := Lcd.ae_map_condExpKernel_eq_of_norm_eq hm hm' hY hF hk
  filter_upwards [hmap, hlaw] with ω h1 h2 hω
  exact Sec5.CfRegQ.isGFFWithBoundaryData_of_map_eq (h2 hω) hY (h1 hω)

/-- The kernel constancy of a word measurable for the coarser marks (input of `ae_isGFF_of_le_fine`). -/
theorem ae_ae_word_eq (hm : m ≤ mΩ) {β : Ω → BoundaryWord} (hβ : Measurable[m] β) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P m ω₀), β ω = β ω₀ :=
  Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hm hβ

end InteractingSLE.Theorem14.SB.Cz
