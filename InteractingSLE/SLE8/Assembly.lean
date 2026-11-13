import InteractingSLE.SLE8.Radial
import InteractingSLE.SLE8.Lemma21
import InteractingSLE.SLE8.AL14.Theorem2

/-!
# SLE₈ note, Theorem 1.1: assembly from Lemma 2.1 and Proposition 4.1

Source: `source/sle8-continuity.pdf`, proof of Theorem 1.1 (anchor `thm-1.1-proof`, pp. 11–12),
Lemma 2.1 (anchors `lem-2.1`, `lem-2.1-proof`, pp. 2–3), Proposition 4.1 (anchor `prop-4.1`,
p. 7); transcription `source/sle8/sle8-continuity.md`.

The frozen Theorem 1.1 (`InteractingSLE.SLE8.ae_exists_continuous_trace`) follows from
`ae_exists_continuous_trace_of_scale_count` (`Radial.lean`), whose two hypotheses are Lemma 2.1 and
Proposition 4.1 of the note. Lemma 2.1 is `lemma21_of_al14` (`Lemma21.lean`), from [AL14] Theorem 2
(proved: `AL14.exists_ae_eventually_derivGridMaxStar_le`, `AL14/Theorem2.lean`) and the convergent
half of [AL14] Corollary 1 (`AL14CorollaryOneStatement`).

## Main results

* `al14TheoremTwoStatement_holds`: [AL14] Theorem 2 in the form `lemma21_of_al14` consumes.
* `lemma21_of_al14CorollaryOne`: Lemma 2.1, from [AL14] Corollary 1 alone.
* `ae_exists_continuous_trace_of_corollaryOne_of_scale_count`: the conclusion of the frozen
  Theorem 1.1, whose only hypotheses are the two results that have not landed yet: [AL14]
  Corollary 1 (packet PROVE-AL14-T4) and Proposition 4.1 of the note (packet PROVE-S8-P41), the
  latter stated exactly as the hypothesis `hP41` of `ae_exists_continuous_trace_of_scale_count`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace InteractingSLE.SLE8

open QuantumZipper

/-- **[AL14] Theorem 2** in the form consumed by `lemma21_of_al14`
(from `AL14.exists_ae_eventually_derivGridMaxStar_le`, with the power `q = p / 2` of `log k`). -/
theorem al14TheoremTwoStatement_holds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :
    AL14TheoremTwoStatement P :=
  fun _B _ _ _ hB b _ p _ => by
    obtain ⟨C, -, h⟩ := AL14.exists_ae_eventually_derivGridMaxStar_le hB p b
    exact ⟨C, (p : ℝ) / 2, h⟩

/-- **Lemma 2.1 of the SLE₈ note from [AL14] Corollary 1** ([AL14] Theorem 2 is proved):
for every `β ∈ (0, 1/4)`, a.s. there is `C_β` with `sup_{t ≤ 1} A_k(t) ≤ C_β k^{-β}` for `k ≥ 1`. -/
theorem lemma21_of_al14CorollaryOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (hC1 : AL14CorollaryOneStatement P)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (β : ℝ) (hβ : 0 < β) (hβ4 : β < 1 / 4) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      ∀ t ∈ Icc (0 : ℝ) 1, normalizedDeriv (drive 8 B ω) k t ≤ C * (k : ℝ) ^ (-β) :=
  lemma21_of_al14 hC1 (al14TheoremTwoStatement_holds P) B hB β hβ hβ4

/-- **Theorem 1.1 of the SLE₈ note, conditional on [AL14] Corollary 1 and Proposition 4.1.**
The conclusion is that of the frozen `ae_exists_continuous_trace`. The hypotheses are exactly the
two results that have not landed: `hC1`, the convergent half of [AL14] Corollary 1, and `hP41`,
Proposition 4.1 of the note for every standard Brownian motion on `(Ω, P)` (as in
`ae_exists_continuous_trace_of_scale_count`): for every `δ ∈ (0, 1/10)`, a.s. eventually in `n`,
`N = 2^n`, `r = N^δ`, `sup_{t ≤ 1} #{N < k ≤ 2N : A_k(t_k) ≥ exp(-r/n²)} ≤ r^7`. -/
theorem ae_exists_continuous_trace_of_corollaryOne_of_scale_count {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (hC1 : AL14CorollaryOneStatement P)
    (hP41 : ∀ B : ℝ≥0 → Ω → ℝ, IsBrownianReal B P → ∀ δ : ℝ, 0 < δ → δ < 1 / 10 →
      ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (0 : ℝ) 1,
        (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k =>
            Real.exp (-(((2 : ℝ) ^ n) ^ δ / (n : ℝ) ^ 2)) ≤
              normalizedDeriv (drive 8 B ω) k (gridTime k t)).card : ℝ) ≤
          (((2 : ℝ) ^ n) ^ δ) ^ 7)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ,
      TendstoLocallyUniformly
          (fun (y : ℝ) (t : ℝ≥0) =>
            QuantumZipper.fwdMapInv (QuantumZipper.drive 8 B ω) t (y * Complex.I))
          γ (𝓝[>] 0) ∧
        Continuous γ ∧ (∀ t, γ t ∈ QuantumZipper.Hbar) ∧ γ 0 = 0 ∧
        ∀ t : ℝ≥0,
          (∃ z ∈ QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t,
              connectedComponentIn (QuantumZipper.H \ γ '' Icc 0 t) z =
                QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t) ∧
            ¬ Bornology.IsBounded
              (QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t) :=
  ae_exists_continuous_trace_of_scale_count (lemma21_of_al14CorollaryOne hC1) hP41 hB

end InteractingSLE.SLE8
