import QuantumZipper.Proofs.Probability.KolmN
import QuantumZipper.Proofs.Thm18.G1RegRepKolm

/-!
# G1-RC, part 1: continuous modification of a GFF tested against an `n`-parameter family

For the G1 regularity package (RC2 in the parameters `(d, r, s)`, RC3 with the smoothing radius
`t` in addition, see DECISIONS.md D32) we need the Duplantier–Sheffield Kolmogorov step for the
free-boundary GFF `X` tested against an **arbitrary** family of probability measures
`μ : (Fin n → ℝ) → Measure ℂ` indexed by `n` real parameters:

* `G1RC.FamilyBounds μ β`: on every box `[-R, R]^n` the measures `μ q` are supported in a fixed
  bounded part `ballH B` of `Hbar`, have a uniformly bounded singular logarithmic potential, and
  satisfy the variance modulus `|Var(X(μ q) − X(μ q'))| ≤ K ‖q − q'‖^β`;
* `G1RC.exists_modification_family`: then `q ↦ X(μ q)` has a modification `Y`, continuous for
  every `ω`, with a.s. convergence along the dyadic approximations (any `n`).

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (arXiv:0808.1560, p. 18): variance modulus ⇒ Gaussian moments ⇒ Kolmogorov–Čentsov
(Revuz–Yor, 3rd ed., Ch. I, Thm (2.1), in the `n`-parameter form `KolmN`). The proof is that of
`G1Kolm.momentBound_qK` / `exists_modification_map` (G1RegRep{Kolm,Wit}.lean) with the pushed
circles replaced by a general family and `KolmG` (`n ≤ 4`) by `KolmN`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open KolmD KolmG CircleFubini

variable {n : ℕ}

/-- Support, potential and variance-modulus bounds of an `n`-parameter family of probability
measures, uniform on boxes. -/
def FamilyBounds (μ : (Fin n → ℝ) → Measure ℂ) (β : ℝ) : Prop :=
  (∀ q, IsProbabilityMeasure (μ q)) ∧
  ∀ R : ℕ, (∃ B : ℝ, ∀ q ∈ boxD (d := n) R, μ q (ballH B)ᶜ = 0) ∧
    (∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ q ∈ boxD (d := n) R, ∀ y : ℂ,
      ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(μ q) ≤ C) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ boxD (d := n) R, ∀ q' ∈ boxD (d := n) R,
      |kernelCov2 neumannH (μ q, μ q') (μ q, μ q')| ≤ K * ‖q - q'‖ ^ β

theorem FamilyBounds.admissible {μ : (Fin n → ℝ) → Measure ℂ} {β : ℝ} (h : FamilyBounds μ β)
    (q : Fin n → ℝ) : IsAdmissibleH (μ q) := by
  have := h.1 q
  obtain ⟨R, hR⟩ : ∃ R : ℕ, q ∈ boxD (d := n) R := by
    obtain ⟨R, hR⟩ := exists_nat_ge (∑ i, |q i|)
    refine ⟨R, fun i => le_trans ?_ hR⟩
    exact Finset.single_le_sum (f := fun i => |q i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
  obtain ⟨⟨B, hB⟩, ⟨C, hCt, hC⟩, -⟩ := h.2 R
  exact admissible_of_bounds (hB q hR) hCt (hC q hR)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem map_diff_eq_gaussianReal {μ : (Fin n → ℝ) → Measure ℂ} {β : ℝ} (h : FamilyBounds μ β)
    (hX : IsFreeGFFModConstH X P) (q q' : Fin n → ℝ) :
    P.map (fun ω => X ω (μ q) - X ω (μ q')) =
      gaussianReal 0 (kernelCov2 neumannH (μ q, μ q') (μ q, μ q')).toNNReal := by
  have hadz := h.admissible q
  have hadw := h.admissible q'
  have := h.1 q
  have := h.1 q'
  have hmass : (μ q) univ = (μ q') univ := by simp [measure_univ]
  have hG : HasGaussianLaw (fun ω => X ω (μ q) - X ω (μ q')) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨(μ q, μ q'), hadz, hadw, hmass⟩
  have hm : AEMeasurable (fun ω => X ω (μ q) - X ω (μ q')) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hc : P[fun ω => X ω (μ q) - X ω (μ q')] = 0 := hX.centered _ _ hadz hadw hmass
  have hcov := hX.covariance_eq (μ q, μ q') (μ q, μ q') hadz hadw hmass hadz hadw hmass
  rw [hG.map_eq_gaussianReal, hc, ← covariance_self hm, hcov]

/-- Gaussian moment bound for the tested process. -/
theorem momentBound_family {μ : (Fin n → ℝ) → Measure ℂ} {β : ℝ} (h : FamilyBounds μ β)
    (hX : IsFreeGFFModConstH X P) (m R : ℕ) :
    ∃ K, 0 ≤ K ∧ MomentBoundG (fun q ω => X ω (μ q)) P (2 * m) (m * β) K R := by
  obtain ⟨-, -, K₁, hK₁, hb⟩ := h.2 R
  refine ⟨K₁ ^ m * gaussianAbsMoment (2 * m),
    mul_nonneg (pow_nonneg hK₁ _) (gaussianAbsMoment_nonneg _), fun q hq q' hq' => ?_⟩
  beta_reduce
  rw [lintegral_pow_two_mul_of_map_eq (U := fun ω => X ω (μ q) - X ω (μ q'))
    ((hX.measurable_coord _).sub (hX.measurable_coord _)) m
    (map_diff_eq_gaussianReal h hX q q')]
  apply ENNReal.ofReal_le_ofReal
  set E := kernelCov2 neumannH (μ q, μ q') (μ q, μ q')
  have hv : ((E.toNNReal : ℝ≥0) : ℝ) ≤ K₁ * ‖q - q'‖ ^ β := by
    rw [Real.coe_toNNReal']
    exact max_le ((le_abs_self E).trans (hb q hq q' hq')) (by positivity)
  have hm := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv m
  have e : (K₁ * ‖q - q'‖ ^ β) ^ m = K₁ ^ m * ‖q - q'‖ ^ ((m : ℝ) * β) := by
    rw [mul_pow, mul_comm (m : ℝ) β, Real.rpow_mul (norm_nonneg _), Real.rpow_natCast]
  calc ((E.toNNReal : ℝ≥0) : ℝ) ^ m * gaussianAbsMoment (2 * m)
      ≤ (K₁ * ‖q - q'‖ ^ β) ^ m * gaussianAbsMoment (2 * m) :=
        mul_le_mul_of_nonneg_right hm (gaussianAbsMoment_nonneg _)
    _ = K₁ ^ m * gaussianAbsMoment (2 * m) * ‖q - q'‖ ^ ((m : ℝ) * β) := by rw [e]; ring

/-- **DS11 Prop 3.1 / Revuz–Yor I.(2.1) for an `n`-parameter family**: the GFF tested against a
family with `FamilyBounds` has a modification continuous for every `ω`, which is a.s. the
limit along the dyadic approximations. -/
theorem exists_modification_family {μ : (Fin n → ℝ) → Measure ℂ} {β : ℝ} (hβ : 0 < β)
    (h : FamilyBounds μ β) (hX : IsFreeGFFModConstH X P) :
    ∃ Y : (Fin n → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      (∀ q, (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (μ q)) ∧
      (∀ᵐ ω ∂P, ∀ q, Tendsto (fun j => X ω (μ (rndD j q))) atTop (𝓝 (Y q ω))) := by
  set m : ℕ := ⌈(n : ℝ) / β⌉₊ + 1 with hm
  have hmβ : (n : ℝ) < (m : ℝ) * β := by
    have h1 : (n : ℝ) / β ≤ (⌈(n : ℝ) / β⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (n : ℝ) / β * β = n := div_mul_cancel₀ _ hβ.ne'
    have h3 : ((n : ℝ) / β + 1) * β ≤ (m : ℝ) * β := by
      apply mul_le_mul_of_nonneg_right _ hβ.le
      rw [hm]; push_cast; linarith
    nlinarith
  have hp : 0 < 2 * m := by omega
  exact KolmN.exists_continuous_modification_N (Z := fun q ω => X ω (μ q))
    (fun q => (hX.measurable_coord _).aemeasurable) hp hmβ
    (fun R => momentBound_family h hX m R)

end G1RC
end Thm18Asm
end QuantumZipper
