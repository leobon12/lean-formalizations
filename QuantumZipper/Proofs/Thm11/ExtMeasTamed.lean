/-
# Measurability of the field `𝔥_s = h₀ ∘ f_s − χ Im log f_s'` on `ℍ ∖ K_s` (arbitrary time)

Time-`s` analogue of `measurable_fwdMap_dom` / `measurable_imLogDeriv_dom`
(`QuantumZipper/Proofs/Thm11/ClockIntegrable.lean`, which prove the same statements at the
fixed time `T`): own port of the proved pattern, no new mathematics. The only structural
additions are (i) the transfer of aliveness/alive-point equations from time `s` to the
sub-interval `[0,s]` via `fwdMap_eq`/`tamedZ_eq_of_isForwardSol`, and (ii) the fact that
`fwdHull` is monotone in time (`fwdHull_mono`, definitional from `ENNReal.ofReal_le_ofReal`),
which lets the `s`-hull appear in place of the `T`-hull.
-/
import QuantumZipper.Proofs.Thm11.NonSwallowing
import QuantumZipper.Statements.CouplingFields

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace QuantumZipper
namespace Thm11Asm
namespace MeasTamed

open QuantumZipper.NonSwallow

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-- For `z` alive at time `s`, the `1/(k+1)`-tamed flow and argument process agree with the true
ones at time `s` for all large `k`. Time-`s` analogue of `ClockInt.eventually_tamed_eq`
(which is stated on the whole interval `[0,T]`). -/
theorem eventually_tamed_eq_at {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {s : ℝ} (hs : 0 ≤ s) (hzs : z ∉ fwdHull W s) :
    ∀ᶠ k : ℕ in atTop, tamedZ W (1 / ((k : ℝ) + 1)) z s = fwdMap W s z ∧
      tamedA W (1 / ((k : ℝ) + 1)) z s = (logDerivFwd W s z).im := by
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hs (show z ∈ H from hz) hzs
  have hfu : ∀ t ∈ Icc (0 : ℝ) s, fwdMap W t z = u t := fun t ht => fwdMap_eq hW hz hu ht
  obtain ⟨hanti, hpos⟩ := im_isForwardSol_le hW hz hu
  have hsm : s ∈ Icc (0 : ℝ) s := ⟨hs, le_rfl⟩
  have hm : 0 < (u s).im := hpos s hsm
  have hge : ∀ t ∈ Icc (0 : ℝ) s, (u s).im ≤ (u t).im := fun t ht => hanti ht hsm ht.2
  obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt hm
  filter_upwards [eventually_ge_atTop k0] with k hk
  have hc : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have hkk : (k0 : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have : (k0 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcm : 1 / ((k : ℝ) + 1) ≤ (u s).im :=
    (one_div_le_one_div_of_le (by positivity) hkk).trans hk0.le
  have htz := tamedZ_eq_of_isForwardSol hW hc hs hu (fun t ht => hcm.trans (hge t ht))
  have htA := im_logDerivFwd_eq_tamedA hW hc hs hz
    (fun t ht => by rw [htz t ht]; exact hcm.trans (hge t ht))
  exact ⟨by rw [htz s hsm, hfu s hsm], (htA s hsm).symm⟩

/-- Time-`s` analogue of `ClockInt.measurableSet_dom_prod`: the set of pairs `(a, ω)` with `a`
alive at time `s` is measurable. Uses `measurableSet_fwdHull_prod`, which is stated for a
general time. -/
theorem measurableSet_dom_prod_at (hBm : ∀ r : ℝ≥0, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    MeasurableSet {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) s} := by
  have e : {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) s}
      = {p : ℂ × Ω | 0 < p.1.im} \ {p | p.1 ∈ fwdHull (drive κ B p.2) s} := by
    ext p; exact Iff.rfl
  rw [e]
  exact (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).diff
    (measurableSet_fwdHull_prod hBm hBc κ hs)

/-- Time-`s` analogue of the pair `measurable_fwdMap_dom` + `measurable_imLogDeriv_dom`
(`ClockIntegrable.lean`): joint measurability of the field
`(a, ω) ↦ 1_{a ∈ ℍ∖K_s}(h₀(f_s(a)) − χ Im log f_s'(a))` at the general time `s ≥ 0`. -/
theorem measured_fieldAt_dom_at (hBm : ∀ r : ℝ≥0, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Measurable ({p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) s}.indicator
      (fun p => h0fwd κ (fwdMap (drive κ B p.2) s p.1)
        - chiC κ * (logDerivFwd (drive κ B p.2) s p.1).im)) := by
  have hD := measurableSet_dom_prod_at hBm hBc κ hs
  refine measurable_of_tendsto_metrizable (f := fun (k : ℕ) =>
    {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) s}.indicator
      (fun p => h0fwd κ (tamedZ (drive κ B p.2) (1 / ((k : ℝ) + 1)) p.1 s)
        - chiC κ * tamedA (drive κ B p.2) (1 / ((k : ℝ) + 1)) p.1 s))
    (fun k => ?_) ?_
  · obtain ⟨hZ, hA⟩ := measurable_tamed_drive κ (c := 1 / ((k : ℝ) + 1)) (by positivity) B hBc
      hs (fun r _ => hBm r)
    refine Measurable.indicator (Measurable.sub ?_ ?_) hD
    · show Measurable fun p : ℂ × Ω => -(2 / Real.sqrt κ) *
        Complex.arg (tamedZ (drive κ B p.2) (1 / ((k : ℝ) + 1)) p.1 s)
      exact (Complex.measurable_arg.comp hZ).const_mul _
    · exact hA.const_mul (chiC κ)
  · rw [tendsto_pi_nhds]
    intro p
    by_cases hp : p ∈ {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) s}
    · simp only [indicator_of_mem hp]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_tamed_eq_at (continuous_drive_ns hBc κ p.2) hp.1 hs hp.2]
        with k hk
      rw [hk.1, hk.2]
    · simp only [indicator_of_notMem hp]; exact tendsto_const_nhds

end MeasTamed
end Thm11Asm
end QuantumZipper
