import InteractingSLE.SLE8.SpaceFilling.InitialDisc

/-!
# Space filling of SLE₈, §5: transience and space filling (Theorem 1)

Source: `source/external/SLE8SF/sle8_space_filling_formalization.pdf`, §5, proof of Theorem 1.
Packet `planning/packets/PROVE-SF8-A.md`.

**Theorem 1.** Let `B` be a Brownian motion, `W = √8 B`, and `γ(t) = lim_{y ↓ 0} F_t(iy)` the
canonical SLE₈ trace (continuous by the proved anchor
`InteractingSLE.SLE8.ae_exists_continuous_trace`, which is the note's standing assumption). Almost
surely:

* (i) for every `t > 0` there is `r > 0` with `B(0, r) ∩ ℍ ⊆ K_t` (Proposition 6,
  `ae_forall_sleHull_halfBall_eight`);
* (ii) `|γ(t)| → ∞` as `t → ∞` (`ae_tendsto_norm_sleTrace_eight`; [RS05, Theorem 7.1] at `κ = 8`);
* (iii) `γ([0, ∞)) = \overline{ℍ}` (`ae_sleTrace_image_eq_Hbar_eight`; [RS05, Corollary 7.4] at
  `κ = 8`).

Moreover, for every deterministic `t > 0`, `H^{14/9}(∂K_t ∩ ℍ) = 0` almost surely (Proposition 5,
PROVE-SF8-B). The combined statement is `ae_spaceFilling_eight`.

(ii) and (iii) discharge the `κ = 8` reductions landed by PROVE-GEO-RSALL and PROVE-RS05-74:
`ae_tendsto_norm_sleTrace_eight_of_interior` (with the interior property from Proposition 6) and
`ae_sleTrace_image_eq_Hbar_eight_of_density` (with positivity from Proposition 6 and the density
from Lemma 2). Their proofs are the scaling step of [RS05, Theorem 7.1] and the closedness of the
range of a transient curve; the note's proof of (ii) (monotone `R_t = dist(0, D_t)` and scaling) is
replaced by that landed scaling step.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.SLE8

open QuantumZipper QuantumZipper.RS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Theorem 1 (ii): transience of the SLE₈ trace** ([RS05, Theorem 7.1] at `κ = 8`): almost
surely `|γ(t)| → ∞` as `t → ∞`. -/
theorem ae_tendsto_norm_sleTrace_eight (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖sleTrace 8 B ω t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact ae_tendsto_norm_sleTrace_eight_of_interior hB (fun hB' => ae_exists_continuous_trace hB')
    fun hB' => (ae_forall_sleHull_halfBall_eight hB').mono fun _ h => h 1 one_pos

/-- **Theorem 1 (iii): the SLE₈ trace is space filling** ([RS05, Corollary 7.4] at `κ = 8`):
almost surely `γ([0, ∞)) = \overline{ℍ}`. -/
theorem ae_sleTrace_image_eq_Hbar_eight (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, sleTrace 8 B ω '' Ici 0 = Hbar := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ae_drive_of_forall_canon hB 8 (Q := fun W => trace W '' Ici 0 = Hbar)
    fun μ _ hμ => ?_
  exact ae_sleTrace_image_eq_Hbar_eight_of_density hμ (fun hB' => ae_exists_continuous_trace hB')
    (exists_measure_hullContainsHalfBall_eight_ne_zero_of_type hμ)
    fun _ hz => (ae_mem_sleTrace_image_eight hμ hz).mono fun _ h => subset_closure h

/-- **Theorem 1** of the note "Space filling of a continuous SLE₈ trace". For a Brownian motion
`B`, `W = √8 B` and the canonical SLE₈ trace `γ`, almost surely: (i) every hull `K_t`, `t > 0`,
contains `B(0, r) ∩ ℍ` for some `r > 0`; (ii) `|γ(t)| → ∞`; (iii) `γ([0, ∞)) = \overline{ℍ}`.
Moreover, for every deterministic `t > 0`, almost surely `H^{14/9}(∂K_t ∩ ℍ) = 0`. -/
theorem ae_spaceFilling_eight (hB : IsBrownianReal B P) :
    (∀ᵐ ω ∂P, (∀ t > (0 : ℝ), ∃ r > (0 : ℝ), ∀ z ∈ H, ‖z‖ < r → z ∈ sleHull 8 B ω t) ∧
      Tendsto (fun t => ‖sleTrace 8 B ω t‖) atTop atTop ∧
      sleTrace 8 B ω '' Ici 0 = Hbar) ∧
    ∀ t > (0 : ℝ), ∀ᵐ ω ∂P, μH[14 / 9] (frontier (sleHull 8 B ω t) ∩ H) = 0 := by
  refine ⟨?_, fun t ht =>
    SpaceFilling.ae_hausdorffMeasure_frontier_fwdHull_inter_H_eq_zero hB ht.le⟩
  filter_upwards [ae_forall_sleHull_halfBall_eight hB, ae_tendsto_norm_sleTrace_eight hB,
    ae_sleTrace_image_eq_Hbar_eight hB] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

end InteractingSLE.SLE8
