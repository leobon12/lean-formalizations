import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Proposition LP4, last step: the dilation argument for the terminal cluster set

Packet PROVE-LP (specification supplement §6.3, proof of Proposition LP4, `source/spec/p481-528.md` L66–L74, p. 483;
graph node `SPEC.id-LP4#zero-one-dilation`).

After the dilation zero–one law, LP4 sets `Z = inf{|z| : z ∈ Q ∩ ℂ}` for the terminal cluster set `Q`, notes
`Z > 0`, and concludes: "Exact dilation invariance of the trace law gives `Z =ᵈ aZ` for every `a > 0`. A random
variable in `(0, ∞]` with this property equals `∞` almost surely: `P(Z ≤ x)` is constant over `x > 0` and tends to
zero as `x ↓ 0`." This file proves that last sentence (`ae_eq_top_of_map_const_mul_eq`): the distribution function
is constant on `(0, ∞)` (`measure_le_eq_measure_le_one`), tends to `P(Z = 0) = 0` along `x = 1/(n+1)` (continuity from
above), hence vanishes, and `{Z < ∞}` is the countable union of the null sets `{Z ≤ n + 1}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace InteractingSLE

namespace LP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ≥0∞}

/-- Under dilation invariance `aZ =ᵈ Z` (`0 < a < ∞`), `P(Z ≤ x) = P(Z ≤ 1)` for every `0 < x < ∞`. -/
theorem measure_le_eq_measure_le_one (hZm : Measurable Z)
    (hdil : ∀ a : ℝ≥0∞, a ≠ 0 → a ≠ ⊤ → P.map (fun ω => a * Z ω) = P.map Z) {x : ℝ≥0∞}
    (hx0 : x ≠ 0) (hxt : x ≠ ⊤) : P {ω | Z ω ≤ x} = P {ω | Z ω ≤ 1} := by
  have hset : {ω | Z ω ≤ x} = (fun ω => x⁻¹ * Z ω) ⁻¹' Iic 1 := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_Iic]
    conv_lhs => rw [← inv_inv x]
    rw [ENNReal.le_inv_iff_mul_le, mul_comm]
  have h1 : P ((fun ω => x⁻¹ * Z ω) ⁻¹' Iic 1) = P.map (fun ω => x⁻¹ * Z ω) (Iic 1) :=
    (Measure.map_apply (hZm.const_mul _) measurableSet_Iic).symm
  have h2 : P.map Z (Iic 1) = P (Z ⁻¹' Iic 1) := Measure.map_apply hZm measurableSet_Iic
  rw [hset, h1, hdil x⁻¹ (ENNReal.inv_ne_zero.2 hxt) (ENNReal.inv_ne_top.2 hx0), h2]
  rfl

/-- **LP4's dilation step.** A random variable `Z` with values in `(0, ∞]` almost surely, whose law is invariant
under every dilation `Z ↦ aZ`, `0 < a < ∞`, equals `∞` almost surely. -/
theorem ae_eq_top_of_map_const_mul_eq [IsFiniteMeasure P] (hZm : Measurable Z)
    (hpos : ∀ᵐ ω ∂P, 0 < Z ω)
    (hdil : ∀ a : ℝ≥0∞, a ≠ 0 → a ≠ ⊤ → P.map (fun ω => a * Z ω) = P.map Z) :
    ∀ᵐ ω ∂P, Z ω = ⊤ := by
  -- `P(Z ≤ 1) = 0`: along `x = 1/(n+1)` the constant distribution function tends to `P(Z = 0) = 0`
  set s : ℕ → Set Ω := fun n => {ω | Z ω ≤ ((n : ℝ≥0∞) + 1)⁻¹} with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_le hZm measurable_const
  have hanti : Antitone s := by
    intro m n hmn ω hω
    exact le_trans (show Z ω ≤ ((n : ℝ≥0∞) + 1)⁻¹ from hω) (ENNReal.inv_le_inv.2 (add_le_add_left (Nat.cast_le.2 hmn) 1))
  have hconst : ∀ n, P (s n) = P {ω | Z ω ≤ 1} := fun n =>
    measure_le_eq_measure_le_one hZm hdil (ENNReal.inv_ne_zero.2 (by simp))
      (ENNReal.inv_ne_top.2 (by simp))
  have hlim := tendsto_measure_iInter_atTop (μ := P) (fun n => (hsm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  have hfun : (P ∘ s) = fun _ => P {ω | Z ω ≤ 1} := funext hconst
  rw [hfun] at hlim
  have hinter : P (⋂ n, s n) = 0 := by
    have hnull : P {ω | ¬ 0 < Z ω} = 0 := ae_iff.1 hpos
    refine measure_mono_null (fun ω hω => ?_) hnull
    simp only [mem_iInter, hs, mem_ofPred_eq] at hω
    simp only [mem_ofPred_eq, not_lt, nonpos_iff_eq_zero]
    by_contra hne
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
    have h1 := hω n
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    exact absurd (h1.trans h2) (not_le.2 hn)
  have hone : P {ω | Z ω ≤ 1} = 0 := by
    rw [← hinter]
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  -- `{Z < ∞}` is the union of the null sets `{Z ≤ n + 1}`
  have hn : ∀ n : ℕ, P {ω | Z ω ≤ (n : ℝ≥0∞) + 1} = 0 := fun n => by
    rw [measure_le_eq_measure_le_one hZm hdil (by simp) (by simp), hone]
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hn)
  obtain ⟨n, hn'⟩ := ENNReal.exists_nat_gt (show Z ω ≠ ⊤ from hω)
  exact mem_iUnion.2 ⟨n, hn'.le.trans le_self_add⟩

end LP

end InteractingSLE
