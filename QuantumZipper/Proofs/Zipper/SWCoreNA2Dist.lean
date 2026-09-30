import QuantumZipper.Proofs.Zipper.SWCoreNA2Small
import QuantumZipper.Proofs.Thm18.G1RCKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-NA2 (N2): pathwise distortion smallness for two families of test measures

Task SWC-NA (`handoff/SW-CORE.md` §5), step N2 for finite-parameter families. Let `μ_k, ν_k`
(`k ∈ ℕ`, e.g. pushed circles `ψ_* fc(z, 2^{-k})` and image circles `fc(ψ z, 2^{-k}‖ψ'(z)‖)`,
parametrized by `q ∈ ℝⁿ`) be families with the Kolmogorov bounds `G1RC.FamilyBounds`, such that on
every box
* `Var[X(μ_k q) − X(ν_k q)] ≤ C 2^{-k}` (SW (3.20); `swcVA_variance_push_round`), and
* `Var[X(μ_k q) − X(μ_k q')]`, `Var[X(ν_k q) − X(ν_k q')] ≤ L 2^k ‖q − q'‖` (the VA moduli at
  radius `2^{-k}`).

Then the continuous modifications satisfy, almost surely, for every box and `η > 0`,
eventually in `k`, `sup_q |Y^μ_k(q) − Y^ν_k(q)| ≤ η` (`swcNA2_distortion_small`).

Proof: Gaussian moments of order `2m`, `m = 4(n+1)` (`CoordRegKolm.lintegral_pow_two_mul_of_map_eq`),
the elementary interpolation `min(x⁴, y⁴) ≤ x y³` between the increment bound
`(L 2^k δ)^{4M}` and the size bound `(C 2^{-k})^{4M}`, giving Kolmogorov constants
`O((1/4)^{Mk})`, summable in `k`; then `swcNA2_ae_eventually_sup_le`. This is the pathwise form of
Sheffield–Wang arXiv:1605.06171, Lemma 3.5 ((3.21)–(3.23), p. 16) with Kolmogorov chaining in place
of Borell–TIS. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace SWCore

open KolmD KolmG Thm18Asm.G1RC

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The law of `X(a) − X(b)` for admissible probability measures. -/
theorem swcNA2_map_pair [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {a b : Measure ℂ}
    [IsProbabilityMeasure a] [IsProbabilityMeasure b] (ha : IsAdmissibleH a)
    (hb : IsAdmissibleH b) :
    P.map (fun ω => X ω a - X ω b) =
      gaussianReal 0 (kernelCov2 neumannH (a, b) (a, b)).toNNReal := by
  have hmass : a univ = b univ := by simp [measure_univ]
  have hG : HasGaussianLaw (fun ω => X ω a - X ω b) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨(a, b), ha, hb, hmass⟩
  have hm : AEMeasurable (fun ω => X ω a - X ω b) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hc : P[fun ω => X ω a - X ω b] = 0 := hX.centered _ _ ha hb hmass
  have hcov := hX.covariance_eq (a, b) (a, b) ha hb hmass ha hb hmass
  rw [hG.map_eq_gaussianReal, hc, ← covariance_self hm, hcov]

/-- Gaussian `2m`-th moment of `X(a) − X(b)`. -/
theorem swcNA2_moment_pair [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {a b : Measure ℂ} [IsProbabilityMeasure a] [IsProbabilityMeasure b] (ha : IsAdmissibleH a)
    (hb : IsAdmissibleH b) {v : ℝ} (hv : |kernelCov2 neumannH (a, b) (a, b)| ≤ v) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (|X ω a - X ω b| ^ (2 * m)) ∂P ≤
      ENNReal.ofReal (v ^ m * gaussianAbsMoment (2 * m)) := by
  have e := lintegral_pow_two_mul_of_map_eq (U := fun ω => X ω a - X ω b)
    ((hX.measurable_coord _).sub (hX.measurable_coord _)) m (swcNA2_map_pair hX ha hb)
  rw [e]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (gaussianAbsMoment_nonneg _))
  refine pow_le_pow_left₀ (NNReal.coe_nonneg _) ?_ m
  rw [Real.coe_toNNReal']
  exact max_le ((le_abs_self _).trans hv) ((abs_nonneg _).trans hv)

/-- `|x − y|^{2m} ≤ 4^m (|x|^{2m} + |y|^{2m})`. -/
theorem swcNA2_abs_sub_pow_le (x y : ℝ) (m : ℕ) :
    |x - y| ^ (2 * m) ≤ 4 ^ m * (|x| ^ (2 * m) + |y| ^ (2 * m)) := by
  have h1 : |x - y| ≤ 2 * max |x| |y| :=
    (abs_sub _ _).trans (by linarith [le_max_left |x| |y|, le_max_right |x| |y|])
  have h2 : max |x| |y| ^ (2 * m) ≤ |x| ^ (2 * m) + |y| ^ (2 * m) := by
    rcases le_total |x| |y| with h | h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (by positivity)
  calc |x - y| ^ (2 * m) ≤ (2 * max |x| |y|) ^ (2 * m) :=
        pow_le_pow_left₀ (abs_nonneg _) h1 _
    _ = 4 ^ m * max |x| |y| ^ (2 * m) := by
        rw [mul_pow, pow_mul]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `min(x⁴, y⁴) ≤ x y³` for `x, y ≥ 0`. -/
theorem swcNA2_min_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min (x ^ 4) (y ^ 4) ≤ x * y ^ 3 := by
  rcases le_total x y with h | h
  · refine (min_le_left _ _).trans ?_
    have : x ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hx h 3
    nlinarith
  · refine (min_le_right _ _).trans ?_
    have : y ≤ x := h
    nlinarith [pow_nonneg hy 3]

/-- Moment of a difference from the moments of the parts. -/
theorem swcNA2_lintegral_sub_le {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B) (m : ℕ)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∫⁻ ω, ENNReal.ofReal (|A ω| ^ (2 * m)) ∂P ≤ ENNReal.ofReal a)
    (hb : ∫⁻ ω, ENNReal.ofReal (|B ω| ^ (2 * m)) ∂P ≤ ENNReal.ofReal b) :
    ∫⁻ ω, ENNReal.ofReal (|A ω - B ω| ^ (2 * m)) ∂P ≤ ENNReal.ofReal (4 ^ m * (a + b)) := by
  have hmA : Measurable fun ω => ENNReal.ofReal (|A ω| ^ (2 * m)) :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp hA).pow_const _)
  calc ∫⁻ ω, ENNReal.ofReal (|A ω - B ω| ^ (2 * m)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (4 ^ m) * (ENNReal.ofReal (|A ω| ^ (2 * m)) +
          ENNReal.ofReal (|B ω| ^ (2 * m))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (swcNA2_abs_sub_pow_le _ _ m)
    _ = ENNReal.ofReal (4 ^ m) * (∫⁻ ω, ENNReal.ofReal (|A ω| ^ (2 * m)) ∂P +
          ∫⁻ ω, ENNReal.ofReal (|B ω| ^ (2 * m)) ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmA]
    _ ≤ ENNReal.ofReal (4 ^ m) * (ENNReal.ofReal a + ENNReal.ofReal b) := by gcongr
    _ = ENNReal.ofReal (4 ^ m * (a + b)) := by
        rw [← ENNReal.ofReal_add ha0 hb0, ← ENNReal.ofReal_mul (by positivity)]

/-- **(N2) Pathwise distortion smallness for two finite-parameter families.** -/
theorem swcNA2_distortion_small [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {μ ν : ℕ → (Fin n → ℝ) → Measure ℂ} {β : ℝ} (hβ : 0 < β)
    (hμ : ∀ k, FamilyBounds (μ k) β) (hν : ∀ k, FamilyBounds (ν k) β)
    (hvar : ∀ R : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ∀ q ∈ boxD (d := n) R,
      |kernelCov2 neumannH (μ k q, ν k q) (μ k q, ν k q)| ≤ C * (1 / 2) ^ k)
    (hmod : ∀ R : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ k, ∀ q ∈ boxD (d := n) R, ∀ q' ∈ boxD (d := n) R,
      |kernelCov2 neumannH (μ k q, μ k q') (μ k q, μ k q')| ≤ L * 2 ^ k * ‖q - q'‖ ^ (1 / 2 : ℝ) ∧
      |kernelCov2 neumannH (ν k q, ν k q') (ν k q, ν k q')| ≤
        L * 2 ^ k * ‖q - q'‖ ^ (1 / 2 : ℝ)) :
    ∃ Yμ Yν : ℕ → (Fin n → ℝ) → Ω → ℝ, (∀ k ω, Continuous fun q => Yμ k q ω) ∧
      (∀ k ω, Continuous fun q => Yν k q ω) ∧
      (∀ k q, (fun ω => Yμ k q ω) =ᵐ[P] fun ω => X ω (μ k q)) ∧
      (∀ k q, (fun ω => Yν k q ω) =ᵐ[P] fun ω => X ω (ν k q)) ∧
      ∀ᵐ ω ∂P, ∀ R : ℕ, ∀ η : ℝ, 0 < η →
        ∀ᶠ k in atTop, ∀ q ∈ boxD (d := n) R, |Yμ k q ω - Yν k q ω| ≤ η := by
  choose Yμ hYμc hYμV _ using fun k => exists_modification_family hβ (hμ k) hX
  choose Yν hYνc hYνV _ using fun k => exists_modification_family hβ (hν k) hX
  refine ⟨Yμ, Yν, hYμc, hYνc, hYμV, hYνV, ?_⟩
  set M : ℕ := 2 * (n + 1) with hM
  set m : ℕ := 4 * M with hm
  set g : ℝ := gaussianAbsMoment (2 * m) with hg
  have hg0 : 0 ≤ g := gaussianAbsMoment_nonneg _
  have hXm : ∀ ν' : Measure ℂ, Measurable fun ω => X ω ν' := fun ν' => hX.measurable_coord ν'
  have hZm : ∀ k q, AEMeasurable (fun ω => Yμ k q ω - Yν k q ω) P := fun k q =>
    (((hXm _).sub (hXm _)).aemeasurable).congr
      ((hYμV k q).symm.sub (hYνV k q).symm)
  refine swcNA2_ae_eventually_sup_le (Z := fun k q ω => Yμ k q ω - Yν k q ω)
    (fun k ω => (hYμc k ω).sub (hYνc k ω)) hZm (p := 2 * m) (by positivity) (a := (M : ℝ) / 2)
    (by rw [hM]; push_cast; linarith) fun R => ?_
  obtain ⟨C, hC0, hC⟩ := hvar (R + 1)
  obtain ⟨L, hL0, hL⟩ := hmod (R + 1)
  set Kc : ℝ := 4 ^ m * (2 * g) * (L * C ^ 3) ^ M + g * C ^ m with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set ρ : ℝ := (1 / 4 : ℝ) ^ M with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hboxR : ∀ q ∈ boxD (d := n) R, q ∈ boxD (d := n) (R + 1) := fun q hq i =>
    (hq i).trans (by push_cast; linarith)
  -- the value moment at a point
  have hval : ∀ k, ∀ q ∈ boxD (d := n) (R + 1),
      ∫⁻ ω, ENNReal.ofReal (|X ω (μ k q) - X ω (ν k q)| ^ (2 * m)) ∂P ≤
        ENNReal.ofReal ((C * (1 / 2) ^ k) ^ m * g) := by
    intro k q hq
    have := (hμ k).1 q
    have := (hν k).1 q
    exact swcNA2_moment_pair hX ((hμ k).admissible q) ((hν k).admissible q) (hC k q hq) m
  have hdecay : ∀ k : ℕ, ((1 / 2 : ℝ) ^ k) ^ m ≤ ρ ^ k := by
    intro k
    have h0 : (1 / 2 : ℝ) ^ (4 * M) ≤ (1 / 4 : ℝ) ^ M := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) M
    calc ((1 / 2 : ℝ) ^ k) ^ m = ((1 / 2 : ℝ) ^ (4 * M)) ^ k := by
          rw [hm, ← pow_mul, ← pow_mul, mul_comm]
      _ ≤ ρ ^ k := pow_le_pow_left₀ (by positivity) h0 k
  refine ⟨fun k => Kc * ρ ^ k, fun k => by positivity,
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left Kc, fun k q hq q' hq' => ?_,
    fun k q hq => ?_⟩
  · -- increments
    have := (hμ k).1 q
    have := (hν k).1 q
    have := (hμ k).1 q'
    have := (hν k).1 q'
    set δ := ‖q - q'‖ ^ (1 / 2 : ℝ) with hδ
    have hδ0 : 0 ≤ δ := by positivity
    have hae : (fun ω => ENNReal.ofReal (|(Yμ k q ω - Yν k q ω) - (Yμ k q' ω - Yν k q' ω)| ^
        (2 * m))) =ᵐ[P] fun ω => ENNReal.ofReal (|(X ω (μ k q) - X ω (ν k q)) -
          (X ω (μ k q') - X ω (ν k q'))| ^ (2 * m)) := by
      filter_upwards [hYμV k q, hYνV k q, hYμV k q', hYνV k q'] with ω h1 h2 h3 h4
      rw [h1, h2, h3, h4]
    rw [lintegral_congr_ae hae]
    set b2 : ℝ := 4 ^ m * ((C * (1 / 2) ^ k) ^ m * g + (C * (1 / 2) ^ k) ^ m * g) with hb2
    set b1 : ℝ := 4 ^ m * ((L * 2 ^ k * δ) ^ m * g + (L * 2 ^ k * δ) ^ m * g) with hb1
    have h2 : ∫⁻ ω, ENNReal.ofReal (|(X ω (μ k q) - X ω (ν k q)) -
        (X ω (μ k q') - X ω (ν k q'))| ^ (2 * m)) ∂P ≤ ENNReal.ofReal b2 :=
      swcNA2_lintegral_sub_le ((hXm _).sub (hXm _)) ((hXm _).sub (hXm _)) m (by positivity)
        (by positivity) (hval k q hq) (hval k q' hq')
    have h1 : ∫⁻ ω, ENNReal.ofReal (|(X ω (μ k q) - X ω (ν k q)) -
        (X ω (μ k q') - X ω (ν k q'))| ^ (2 * m)) ∂P ≤ ENNReal.ofReal b1 := by
      have e : ∀ ω, (X ω (μ k q) - X ω (ν k q)) - (X ω (μ k q') - X ω (ν k q')) =
          (X ω (μ k q) - X ω (μ k q')) - (X ω (ν k q) - X ω (ν k q')) := fun ω => by ring
      simp_rw [e]
      exact swcNA2_lintegral_sub_le ((hXm _).sub (hXm _)) ((hXm _).sub (hXm _)) m
        (by positivity) (by positivity)
        (swcNA2_moment_pair hX ((hμ k).admissible q) ((hμ k).admissible q')
          (hL k q hq q' hq').1 m)
        (swcNA2_moment_pair hX ((hν k).admissible q) ((hν k).admissible q')
          (hL k q hq q' hq').2 m)
    refine (le_min h1 h2).trans ?_
    rw [← ENNReal.ofReal_min]
    refine ENNReal.ofReal_le_ofReal ?_
    set x : ℝ := (L * 2 ^ k * δ) ^ M with hx
    set y : ℝ := (C * (1 / 2) ^ k) ^ M with hy
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have eb1 : b1 = 4 ^ m * (2 * g) * x ^ 4 := by
      rw [hb1, hx, hm, ← pow_mul, mul_comm M 4]; ring
    have eb2 : b2 = 4 ^ m * (2 * g) * y ^ 4 := by
      rw [hb2, hy, hm, ← pow_mul, mul_comm M 4]; ring
    have hmin : min b1 b2 ≤ 4 ^ m * (2 * g) * (x * y ^ 3) := by
      rw [eb1, eb2]
      have hc : 0 ≤ 4 ^ m * (2 * g) := by positivity
      have key := swcNA2_min_pow_le hx0 hy0
      rcases le_total (x ^ 4) (y ^ 4) with h | h
      · rw [min_eq_left (mul_le_mul_of_nonneg_left h hc)]
        rw [min_eq_left h] at key
        exact mul_le_mul_of_nonneg_left key hc
      · rw [min_eq_right (mul_le_mul_of_nonneg_left h hc)]
        rw [min_eq_right h] at key
        exact mul_le_mul_of_nonneg_left key hc
    have h4 : (2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ k) ^ 3 = (1 / 4 : ℝ) ^ k := by
      rw [← pow_mul, mul_comm k 3, pow_mul, ← mul_pow]; norm_num
    have exy : x * y ^ 3 = (L * C ^ 3) ^ M * ρ ^ k * δ ^ M := by
      have e1 : x * y ^ 3 = (L * 2 ^ k * δ * (C * (1 / 2) ^ k) ^ 3) ^ M := by
        rw [hx, hy, mul_pow (L * 2 ^ k * δ) ((C * (1 / 2 : ℝ) ^ k) ^ 3) M,
          ← pow_mul (C * (1 / 2 : ℝ) ^ k) 3 M, Nat.mul_comm 3 M,
          pow_mul (C * (1 / 2 : ℝ) ^ k) M 3]
      have e2 : L * 2 ^ k * δ * (C * (1 / 2 : ℝ) ^ k) ^ 3 = L * C ^ 3 * δ * (1 / 4 : ℝ) ^ k := by
        rw [← h4]; ring
      rw [e1, e2, mul_pow, mul_pow, hρ, ← pow_mul, ← pow_mul, mul_comm k M]
      ring
    have eδ : δ ^ M = ‖q - q'‖ ^ ((M : ℝ) / 2) := by
      rw [hδ, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; ring_nf
    rw [← eδ]
    calc min b1 b2 ≤ 4 ^ m * (2 * g) * (x * y ^ 3) := hmin
      _ = 4 ^ m * (2 * g) * (L * C ^ 3) ^ M * ρ ^ k * δ ^ M := by rw [exy]; ring
      _ ≤ Kc * ρ ^ k * δ ^ M := by
        gcongr
        rw [hKc]
        exact le_add_of_nonneg_right (by positivity)
  · -- values
    have hae : (fun ω => ENNReal.ofReal (|Yμ k q ω - Yν k q ω| ^ (2 * m))) =ᵐ[P]
        fun ω => ENNReal.ofReal (|X ω (μ k q) - X ω (ν k q)| ^ (2 * m)) := by
      filter_upwards [hYμV k q, hYνV k q] with ω h1 h2
      rw [h1, h2]
    rw [lintegral_congr_ae hae]
    refine (hval k q (hboxR q hq)).trans (ENNReal.ofReal_le_ofReal ?_)
    calc (C * (1 / 2) ^ k) ^ m * g = g * C ^ m * ((1 / 2 : ℝ) ^ k) ^ m := by ring
      _ ≤ g * C ^ m * ρ ^ k := by gcongr; exact hdecay k
      _ ≤ Kc * ρ ^ k := by
        gcongr
        rw [hKc]
        exact le_add_of_nonneg_left (by positivity)

end SWCore
end QuantumZipper
