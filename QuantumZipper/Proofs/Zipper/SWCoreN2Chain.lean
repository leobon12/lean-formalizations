import QuantumZipper.Proofs.Zipper.SWCoreV6
import QuantumZipper.Proofs.Zipper.UnifSWGaussRatio

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2 (1): small Gaussian families with a scale-relative modulus are uniformly small a.s.

Task SWC-N (`handoff/SW-CORE.md` §5), the chaining + Borel–Cantelli step of the distortion core,
for families indexed by a bounded countable set `D ⊂ ℝ^d` (sup norm). For each scale
`k` let `Z k θ` (`θ ∈ D`) be a centred Gaussian process with

* `Var (Z k θ) ≤ V · r_k^{β₀}`                              (SW (3.20): pushed vs round),
* `Var (Z k θ − Z k θ') ≤ L² (‖θ − θ'‖ / r_k)^β` for `‖θ − θ'‖ ≤ r_k²`  (the modulus),

`r_k = 2^{-k}`. Then almost surely, for every `η > 0`, eventually in `k`, `|Z k θ| ≤ η` for all
`θ ∈ D` (`swcn2_ae_eventually_small`).

Proof (Sheffield–Wang, arXiv:1605.06171, Lemma 3.5 and the Borel–Cantelli step after (3.23),
p. 16): cover `D` by `≲ 4^{kd}` sup-norm boxes of side `r_k²`; in each box the supremum of
`Z − Z(i₀)` has exponential moments `≤ exp(t m + π²/8 t² σ²)` by Dudley chaining + Borell–TIS
(`RegUnif.swg_exp_sup_le`) with `m ≲ L r_k^{β/2}`, `σ² ≤ L² r_k^β`; the value at the box
representative has Gaussian exponential moments (`RegUnif.swg_lintegral_exp_gauss`). With
`t = r_k^{-β/2}` (resp. `r_k^{-β₀/2}`) and Markov's inequality each box contributes
`≲ exp(−(η/3) 2^{kβ/2})`, which beats the box count `4^{kd}` (`swcn2_summable`); Borel–Cantelli.
Own assembly of cited tools.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Real

namespace QuantumZipper
namespace SWCore

open RegUnif

/-- `A^k e^{−c B^k}` is summable for `B > 1`, `c > 0`. -/
theorem swcn2_summable {A c B : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hB : 1 < B) :
    Summable fun k : ℕ => A ^ k * Real.exp (-(c * B ^ k)) := by
  have hB0 : 0 < B := by linarith
  -- choose `j` with `B^j ≥ 2 (A + 1)`
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (2 * (A + 1)) hB
  have hBj : 0 < B ^ j := pow_pos hB0 j
  set q : ℝ := A / B ^ j with hq
  have hq0 : 0 ≤ q := div_nonneg hA hBj.le
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hBj]; linarith
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left ((j.factorial : ℝ) / c ^ j))
  have hx : 0 ≤ c * B ^ k := by positivity
  have hexp := Real.pow_div_factorial_le_exp (c * B ^ k) hx j
  have hpos : 0 < (c * B ^ k) ^ j := by positivity
  have h1 : Real.exp (-(c * B ^ k)) ≤ (j.factorial : ℝ) / (c * B ^ k) ^ j := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact hexp
  calc A ^ k * Real.exp (-(c * B ^ k)) ≤ A ^ k * ((j.factorial : ℝ) / (c * B ^ k) ^ j) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hA k)
    _ = (j.factorial : ℝ) / c ^ j * q ^ k := by
        rw [hq, div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k j]
        field_simp
    _ ≤ _ := le_rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Markov's inequality for an exponential moment bound. -/
theorem swcn2_markov_exp {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {c s : ℝ}
    (hb : ∫⁻ ω, f ω ∂P ≤ ENNReal.ofReal (Real.exp c)) :
    P {ω | ENNReal.ofReal (Real.exp s) ≤ f ω} ≤ ENNReal.ofReal (Real.exp (c - s)) := by
  have hs0 : ENNReal.ofReal (Real.exp s) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos s
  refine (meas_ge_le_lintegral_div hf hs0 ENNReal.ofReal_ne_top).trans ?_
  calc (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp s)
      ≤ ENNReal.ofReal (Real.exp c) / ENNReal.ofReal (Real.exp s) := by gcongr
    _ = ENNReal.ofReal (Real.exp (c - s)) := by
        rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos s), Real.exp_sub]

/-- **One box**: the supremum over a countable set of a centred Gaussian process relative to a
reference point exceeds `η` with probability `≤ exp(t m + π²/8 t² σ² − t η)`. -/
theorem swcn2_box_tail [IsProbabilityMeasure P] {ι : Type} [Countable ι] {Z : ι → Ω → ℝ} (hZ : IsGaussianProcess Z P)
    (hc : ∀ i, ∫ ω, Z i ω ∂P = 0) (hZm : ∀ i, Measurable (Z i)) {d : ℕ} (p : ι → Fin d → ℝ)
    {L a β σ t η : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 ≤ L) (hσ0 : 0 ≤ σ) (ht : 0 ≤ t)
    (i₀ : ι) (A : Set ι) (hp : ∀ i ∈ A, ∀ j ∈ A, ‖p i - p j‖ ≤ a)
    (hv : ∀ i ∈ A, ∀ j ∈ A, Var[fun ω => Z i ω - Z j ω; P] ≤ L ^ 2 * ‖p i - p j‖ ^ β)
    (hσ : ∀ i ∈ A, Var[fun ω => Z i ω - Z i₀ ω; P] ≤ σ ^ 2) :
    P {ω | ∃ i ∈ A, η ≤ Z i ω - Z i₀ ω} ≤
      ENNReal.ofReal (Real.exp (t * (fgmChainConst d β * L * a ^ (β / 2)) +
        π ^ 2 / 8 * t ^ 2 * σ ^ 2 - t * η)) := by
  have hmeas : AEMeasurable (fun ω => ⨆ i ∈ A, ENNReal.ofReal (Real.exp (t * (Z i ω - Z i₀ ω))))
      P := by
    refine (Measurable.biSup _ (Set.to_countable A) fun i _ => ?_).aemeasurable
    exact (Real.measurable_exp.comp (((hZm i).sub (hZm i₀)).const_mul t)).ennreal_ofReal
  refine (measure_mono fun ω hω => ?_).trans
    (swcn2_markov_exp hmeas (swg_exp_sup_le hZ hc p hβ hβ1 hL hσ0 ht i₀ A hp hv hσ))
  obtain ⟨i, hi, hle⟩ := hω
  show ENNReal.ofReal (Real.exp (t * η)) ≤ _
  refine le_trans ?_ (le_iSup₂_of_le i hi le_rfl)
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hle ht))

/-- **One point**: a centred Gaussian exceeds `η` with probability `≤ exp(Var t²/2 − t η)`. -/
theorem swcn2_point_tail {U : Ω → ℝ} (hU : HasGaussianLaw U P) (hc : ∫ ω, U ω ∂P = 0)
    (hUm : Measurable U) {t η : ℝ} (ht : 0 ≤ t) :
    P {ω | η ≤ U ω} ≤ ENNReal.ofReal (Real.exp (Var[U; P] * t ^ 2 / 2 - t * η)) := by
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (t * U ω))) P :=
    (Real.measurable_exp.comp (hUm.const_mul t)).ennreal_ofReal.aemeasurable
  refine (measure_mono fun ω hω => ?_).trans
    (swcn2_markov_exp hmeas (swg_lintegral_exp_gauss hU hc t).le)
  show ENNReal.ofReal (Real.exp (t * η)) ≤ _
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω ht))

end SWCore
end QuantumZipper
