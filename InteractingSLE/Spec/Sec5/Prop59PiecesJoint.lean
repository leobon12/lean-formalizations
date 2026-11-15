/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Joint measurability of processes killed at a measurable lifetime

Packet PROVE-PROP59-PIECES (regularity of Proposition 5.9's concrete pieces, `IsRegPiece`). The pieces of the
alternating construction are read in the joint chart through killed arcs: at every sample they are continuous before
their lifetime and `0` from the lifetime on, and at every fixed time they are measurable. Such a process is jointly
measurable in (time, sample): it is the pointwise limit of its values at the dyadic times above the current time
(`upApprox`), each of which is a countable mixture of measurable maps.

## Main results

* `upApprox`: the dyadic time `⌈u 2ⁿ⌉ / 2ⁿ ≥ u` (`le_upApprox`, `tendsto_upApprox`, `measurable_upApprox`);
* **`measurable_uncurry_killed`**: a process continuous before a lifetime `L` at every sample and measurable at every
  fixed time after killing at `L` is jointly measurable after killing at `L`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59Pieces

/-! ### Dyadic times from above -/

/-- The dyadic time `⌈u 2ⁿ⌉ / 2ⁿ` at or above `u`. -/
def upApprox (n : ℕ) (u : ℝ≥0) : ℝ≥0 := (⌈u * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n

theorem le_upApprox (n : ℕ) (u : ℝ≥0) : u ≤ upApprox n u := by
  unfold upApprox
  rw [le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

theorem upApprox_le (n : ℕ) (u : ℝ≥0) : upApprox n u ≤ u + 1 / 2 ^ n := by
  unfold upApprox
  rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem tendsto_upApprox (u : ℝ≥0) : Tendsto (fun n => upApprox n u) atTop (𝓝 u) := by
  have h2 : Tendsto (fun n : ℕ => u + 1 / (2 : ℝ≥0) ^ n) atTop (𝓝 (u + 0)) := by
    refine tendsto_const_nhds.add ?_
    simp only [one_div]
    exact (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2 : ℝ≥0)⁻¹ < 1)).congr
      fun n => inv_pow _ _
  rw [add_zero] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (le_upApprox · u)
    (upApprox_le · u)

theorem measurable_upApprox_nat (n : ℕ) : Measurable fun u : ℝ≥0 => ⌈u * 2 ^ n⌉₊ :=
  Nat.measurable_ceil.comp (measurable_id.mul measurable_const)

/-! ### Killed processes -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A process continuous before a measurable lifetime is jointly measurable after killing.** If `f · ω` is
continuous on `{u < L ω}` for every `ω`, and the killed process `ω ↦ f s ω · 1{s < L ω}` is measurable for every `s`,
then the killed process is jointly measurable in `(s, ω)`. -/
theorem measurable_uncurry_killed {f : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}
    (hm : ∀ s : ℝ≥0, Measurable fun ω => if (s : ℝ≥0∞) < L ω then f s ω else 0)
    (hc : ∀ ω, ContinuousOn (f · ω) {u | (u : ℝ≥0∞) < L ω}) :
    Measurable (Function.uncurry fun (u : ℝ≥0) ω => if (u : ℝ≥0∞) < L ω then f u ω else 0) := by
  set X : ℝ≥0 → Ω → ℝ := fun u ω => if (u : ℝ≥0∞) < L ω then f u ω else 0 with hX
  -- the approximants `X (upApprox n u) ω`
  have hF : ∀ n, Measurable fun p : ℝ≥0 × Ω => X (upApprox n p.1) p.2 := by
    intro n
    set g : Ω × ℕ → ℝ := fun q => X ((q.2 : ℝ≥0) / 2 ^ n) q.1 with hg
    have hgm : Measurable g := measurable_from_prod_countable_left fun k => hm ((k : ℝ≥0) / 2 ^ n)
    have e : (fun p : ℝ≥0 × Ω => X (upApprox n p.1) p.2) =
        g ∘ fun p : ℝ≥0 × Ω => (p.2, ⌈p.1 * 2 ^ n⌉₊) := rfl
    rw [e]
    exact hgm.comp (measurable_snd.prodMk ((measurable_upApprox_nat n).comp measurable_fst))
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun p => ?_)
  obtain ⟨u, ω⟩ := p
  show Tendsto (fun n => X (upApprox n u) ω) atTop (𝓝 (X u ω))
  by_cases hu : (u : ℝ≥0∞) < L ω
  · have hopen : IsOpen {v : ℝ≥0 | (v : ℝ≥0∞) < L ω} := isOpen_lt ENNReal.continuous_coe continuous_const
    have hca : ContinuousAt (f · ω) u := (hc ω).continuousAt (hopen.mem_nhds hu)
    have hev : ∀ᶠ n in atTop, ((upApprox n u : ℝ≥0) : ℝ≥0∞) < L ω :=
      (tendsto_upApprox u).eventually (hopen.mem_nhds hu)
    have hlim : Tendsto (fun n => f (upApprox n u) ω) atTop (𝓝 (f u ω)) := hca.tendsto.comp (tendsto_upApprox u)
    simp only [hX, hu, ↓reduceIte]
    refine hlim.congr' ?_
    filter_upwards [hev] with n hn
    simp only [hn, ↓reduceIte]
  · have hn : ∀ n, ¬ ((upApprox n u : ℝ≥0) : ℝ≥0∞) < L ω := fun n h =>
      hu (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (le_upApprox n u)) h)
    simp only [hX, hu, ↓reduceIte, hn]
    exact tendsto_const_nhds

/-- A process that vanishes from its lifetime on, is continuous before it and measurable at every time, is jointly
measurable. -/
theorem measurable_uncurry_of_killed {f : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} (hm : ∀ s, Measurable (f s))
    (hc : ∀ ω, ContinuousOn (f · ω) {u | (u : ℝ≥0∞) < L ω}) (hL : Measurable L)
    (h0 : ∀ (u : ℝ≥0) ω, ¬ (u : ℝ≥0∞) < L ω → f u ω = 0) : Measurable (Function.uncurry f) := by
  have e : f = fun (u : ℝ≥0) ω => if (u : ℝ≥0∞) < L ω then f u ω else 0 := by
    funext u ω
    by_cases hu : (u : ℝ≥0∞) < L ω
    · simp only [hu, ↓reduceIte]
    · simp only [hu, ↓reduceIte, h0 u ω hu]
  rw [e]
  refine measurable_uncurry_killed (fun s => ?_) hc
  exact Measurable.ite (measurableSet_lt measurable_const hL) (hm s) measurable_const

end InteractingSLE.Sec5.Prop59Pieces
