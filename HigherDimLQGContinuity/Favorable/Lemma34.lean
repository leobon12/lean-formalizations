import HigherDimLQGContinuity.Favorable.Prob
import HigherDimLQGContinuity.Amplify.Prop33
import HigherDimLQGContinuity.Witness.Subdiv

/-!
# Lemma 3.4: favorable arcs (packet P8a)

Packet P8a, targets `lemma34`, `lemma34_arc` (blueprint Part A, Lemma `a:lem34`; [C] Lemma 3.4, p. 8–9,
l. 405–434; planning audits NA1 item 26 and R10, NA0 §2.3; erratum EA19). Consumed interface: I1,
`UniformEstimates d ξ̄ s` for `s ∈ [1, 10]` (Lemma 2.1, taken as a hypothesis, as by Proposition 3.3).

**Statement** (`lemma34`). There are `p_* ∈ (0, 1)`, `v₀ ∈ (0, 1/2]`, `C₄, c₄ > 0` and reference constants `𝓡'`
(from Lemma `a:lem-refs-prob` at pin `1` with failure `p_*/2`) such that for `ξ, η ∈ (0, ξ̄]`, `D, E` strong,
`0 < v < v₀` and `τ = |η - ξ| ≤ c₄ v^{C₄}`: `𝐏₁(H↓(D, E; 1 + 2v)) ≥ p_*` and
`𝐏₁(H↓(D, E; 1 + 2v) ∩ PairRefs(D, E; 𝓡')) ≥ p_*/2`. On the latter event, Lemma `a:lem-subdiv`(b) supplies a
favorable arc for `b = 1 + 2v` (`lemma34_arc`, almost surely, where `ρ^D_g, ρ^E_g` are length metrics).

**Proof** (the blueprint's quantified contradiction, EA19: `A = 3`, `δ = v/100`, `e = v⁴/100`,
`n(v) = C₅ v^{-M₃-1}`, `τ ≤ c₄ v^{M₃+2}`). `p₀` is Proposition 3.3's constant, `p_* = min(p₀, 1)/2`, `𝓡'` the
references with failure `p_*/2`, `(M₃, C₃, c₃)` Proposition 3.3's constants for `𝓡'`, `C_b = 1`, `s₁ = s₂ = 1`.
Suppose `𝐏₁(H↓(D, E; 1 + 2v)) < p_*`. Since `H↑(E, D; (1 + 2v)⁻¹) ⊆ H↓(D, E; 1 + 2v)` (`a:lem-H-incl`),
`𝐏₁(H↑(E, D; (1 + 2v)⁻¹) ∪ PairRefs(E, D; 𝓡')ᶜ) < 3p_*/2 ≤ p₀`, and Proposition 3.3 for the ordered pair `(E, D)`
with `b = (1 + 2v)⁻¹ ≤ 1`, `R = 1`, `δ = v/100`, `e = v⁴/100`, `n = n(v)` gives
`𝐏₁(¬ ρ^D ≤ ((1 + 2v)⁻¹ + v/100) ρ^E + v⁴/100 on B̄₁²) ≤ c₁ v²/4`. With Cantelli
(`𝐏₁(ρ^E(0, e₁) < (1 + v) ρ^D(0, e₁)) ≥ c₁ v²`) and the inverse crossing (`𝐏₁(ρ^D(0, e₁) < v³) ≤ K_inv v³ ≤ c₁ v²/4`
for `v < v₀ ≤ c₁/(4 K_inv)`), the three events have a common point, where (3.11) gives `D₀ < D₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- An outer-measure bound for an intersection: `μ A ≥ p` and `μ Bᶜ ≤ q` give `μ (A ∩ B) ≥ p - q`. -/
theorem p8a_measure_inter_ge {α : Type*} [MeasurableSpace α] (μ : Measure α) {A B : Set α} {p q : ℝ}
    (hq : 0 ≤ q) (hA : ENNReal.ofReal p ≤ μ A) (hB : μ Bᶜ ≤ ENNReal.ofReal q) :
    ENNReal.ofReal (p - q) ≤ μ (A ∩ B) := by
  have hsub : A ⊆ (A ∩ B) ∪ Bᶜ := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx, hxB⟩
    · exact Or.inr hxB
  have h1 : ENNReal.ofReal p ≤ μ (A ∩ B) + ENNReal.ofReal q := by
    calc ENNReal.ofReal p ≤ μ A := hA
      _ ≤ μ ((A ∩ B) ∪ Bᶜ) := measure_mono hsub
      _ ≤ μ (A ∩ B) + μ Bᶜ := measure_union_le _ _
      _ ≤ μ (A ∩ B) + ENNReal.ofReal q := by gcongr
  rw [ENNReal.ofReal_sub p hq]
  exact tsub_le_iff_right.2 h1

/-- Three events with `μ A ≥ a`, `μ B ≤ a/4`, `μ C ≤ a/4` (`a > 0`) have a point in `A \ (B ∪ C)`. -/
theorem p8a_exists_mem_diff {α : Type*} [MeasurableSpace α] (μ : Measure α) {A B C : Set α} {a : ℝ}
    (ha : 0 < a) (hA : ENNReal.ofReal a ≤ μ A) (hB : μ B ≤ ENNReal.ofReal (a / 4))
    (hC : μ C ≤ ENNReal.ofReal (a / 4)) : ∃ x ∈ A, x ∉ B ∧ x ∉ C := by
  by_contra hno
  push Not at hno
  have hsub : A ⊆ B ∪ C := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    · exact Or.inr (hno x hx hxB)
  have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal (a / 4 + a / 4) := by
    calc ENNReal.ofReal a ≤ μ A := hA
      _ ≤ μ (B ∪ C) := measure_mono hsub
      _ ≤ μ B + μ C := measure_union_le _ _
      _ ≤ ENNReal.ofReal (a / 4) + ENNReal.ofReal (a / 4) := add_le_add hB hC
      _ = ENNReal.ofReal (a / 4 + a / 4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  linarith

/-- **Lemma 3.4** (favorable arcs; blueprint Part A `a:lem34`, [C] Lemma 3.4 with NA1 R10 and erratum EA19), under the
sphere-one pin `𝐏₁ = pinLaw d 1`. From Lemma 2.1 (`UniformEstimates`, I1) at the pins `s ∈ [1, 10]`: there are
`p_* ∈ (0, 1)`, `v₀ ∈ (0, 1/2]`, `C₄, c₄ > 0` and pin-`1` reference constants `𝓡' = (H₀, σ₀, β₀, m, M)`
(`0 < σ₀ < 1 < β₀`, `0 < m < M`, `1 ≤ H₀`, failure `≤ p_*/2`, as given by Lemma `a:lem-refs-prob` at `p = p_*/2`)
such that for all `ξ, η ∈ (0, ξ̄]`, `D, E` strong, `0 < v < v₀` and `|η - ξ| ≤ c₄ v^{C₄}`:
`𝐏₁(H↓(D, E; 1 + 2v)) ≥ p_*` and `𝐏₁(H↓(D, E; 1 + 2v) ∩ PairRefs(D, E; 𝓡')) ≥ p_*/2`. (In the proof `C₄ = M₃ + 2`
with Proposition 3.3's exponent `M₃`.) -/
theorem lemma34 (hd : 2 ≤ d) {ξbar : ℝ} (hU : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s) :
    ∃ pstar v₀ C₄ c₄ : ℝ, 0 < pstar ∧ pstar < 1 ∧ 0 < v₀ ∧ v₀ ≤ 1 / 2 ∧ 0 < C₄ ∧ 0 < c₄ ∧
    ∃ H₀ σ₀ β₀ m M : ℝ, 0 < σ₀ ∧ σ₀ < 1 ∧ 1 < β₀ ∧ 0 < m ∧ m < M ∧ 1 ≤ H₀ ∧
      (∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar, ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
          pinLaw d 1 (PairRefs D E H₀ σ₀ β₀ m M)ᶜ ≤ ENNReal.ofReal (pstar / 2)) ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar, ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
        ∀ v : ℝ, 0 < v → v < v₀ → |η - ξ| ≤ c₄ * v ^ C₄ →
          ENNReal.ofReal pstar ≤ pinLaw d 1 (Hdown D E (1 + 2 * v)) ∧
          ENNReal.ofReal (pstar / 2) ≤
            pinLaw d 1 (Hdown D E (1 + 2 * v) ∩ PairRefs D E H₀ σ₀ β₀ m M) := by
  have hU1 : UniformEstimates d ξbar 1 := hU 1 ⟨le_rfl, by norm_num⟩
  -- Proposition 3.3's constant `p₀`, then `p_*` and the references
  obtain ⟨p₀, hp₀, hprop⟩ := prop33 hd hU
  set pstar : ℝ := min p₀ 1 / 2 with hpstar
  have hpstar0 : 0 < pstar := by positivity
  have hpstar1 : pstar ≤ 1 / 2 := by
    have := min_le_right p₀ 1
    rw [hpstar]
    linarith
  have hpstarp₀ : 3 * pstar / 2 ≤ p₀ := by
    have := min_le_left p₀ 1
    rw [hpstar]
    linarith
  obtain ⟨H₀, σ₀, β₀, m, M, hσ₀, hσ₀1, hβ₀, hm, hmM, hH₀, hrefs⟩ :=
    refs_prob hd one_pos hU1 (p := pstar / 2) (by positivity)
  obtain ⟨M₃, C₃, c₃, hM₃, hC₃, hc₃, h33⟩ :=
    hprop 1 H₀ σ₀ β₀ m M one_pos hm hmM.le 1 1 le_rfl (by norm_num) le_rfl (by norm_num)
  -- the unit-distance events and the depth
  obtain ⟨c₁, hc₁, -, hratio⟩ := p8a_ratio_prob hd hU1
  obtain ⟨Kinv, hKinv, hsmall⟩ := p8a_small_prob hd hU1
  obtain ⟨C₅, hC₅, hnum⟩ := p8a_numerics hM₃ hC₃ hc₃ hc₁
  set v₀ : ℝ := min (1 / 2) (c₁ / (4 * Kinv)) with hv₀
  have hv₀0 : 0 < v₀ := lt_min (by norm_num) (by positivity)
  refine ⟨pstar, v₀, M₃ + 2, c₃ / (100 * C₅), hpstar0, by linarith, hv₀0, min_le_left _ _, by linarith,
    by positivity, H₀, σ₀, β₀, m, M, hσ₀, hσ₀1, hβ₀, hm, hmM, hH₀, hrefs, ?_⟩
  intro ξ hξ η hη D E hD hE v hv hvv₀ hτ
  have hv12 : v < 1 / 2 := lt_of_lt_of_le hvv₀ (min_le_left _ _)
  have hvK : v < c₁ / (4 * Kinv) := lt_of_lt_of_le hvv₀ (min_le_right _ _)
  -- the first assertion, by contradiction
  have hfirst : ENNReal.ofReal pstar ≤ pinLaw d 1 (Hdown D E (1 + 2 * v)) := by
    by_contra hlt
    push Not at hlt
    have h12 : 0 < 1 + 2 * v := by linarith
    have hb0 : 0 < (1 + 2 * v)⁻¹ := inv_pos.2 h12
    have hb1 : (1 + 2 * v)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    -- Proposition 3.3's hypothesis for the ordered pair `(E, D)`
    have hhyp : pinLaw d 1 (Hup E D (1 + 2 * v)⁻¹ ∪ (PairRefs E D H₀ σ₀ β₀ m M)ᶜ) ≤
        ENNReal.ofReal p₀ := by
      have hinc : Hup E D (1 + 2 * v)⁻¹ ⊆ Hdown D E (1 + 2 * v) := by
        have := hup_subset_hdown (D := D) (E := E) hb0
        rwa [inv_inv] at this
      calc pinLaw d 1 (Hup E D (1 + 2 * v)⁻¹ ∪ (PairRefs E D H₀ σ₀ β₀ m M)ᶜ)
          ≤ pinLaw d 1 (Hup E D (1 + 2 * v)⁻¹) + pinLaw d 1 (PairRefs E D H₀ σ₀ β₀ m M)ᶜ :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal pstar + ENNReal.ofReal (pstar / 2) :=
            add_le_add ((measure_mono hinc).trans hlt.le) (hrefs η hη ξ hξ E D hE hD)
        _ = ENNReal.ofReal (3 * pstar / 2) := by
            rw [← ENNReal.ofReal_add hpstar0.le (by positivity)]
            ring_nf
        _ ≤ ENNReal.ofReal p₀ := ENNReal.ofReal_le_ofReal hpstarp₀
    -- Proposition 3.3 at `R = 1`, `δ = v/100`, `e = v⁴/100`, `n = n(v)`
    have hv1 : v ≤ 1 := by linarith
    have hnv := hnum v hv hv1
    have hdrift : |ξ - η| * (C₅ * v⁻¹ ^ (M₃ + 1)) ≤ c₃ * (v / 100) := by
      rw [abs_sub_comm]
      exact p8a_drift hC₅ hv hτ
    have hcomp := h33 η hη ξ hξ E D hE hD (1 + 2 * v)⁻¹ hb0 hb1 hhyp 1 (v / 100) (v ^ 4 / 100)
      (C₅ * v⁻¹ ^ (M₃ + 1)) le_rfl (by positivity) (by linarith) (by positivity)
      (by have : v ^ 4 < 1 := pow_lt_one₀ hv.le (by linarith) (by norm_num); linarith) hnv.1 hdrift
    have hC : pinLaw d 1 {g | ¬ CompOn (rho D g) (rho E g) ((1 + 2 * v)⁻¹ + v / 100) (v ^ 4 / 100) 1} ≤
        ENNReal.ofReal (c₁ * v ^ 2 / 4) := hcomp.trans (ENNReal.ofReal_le_ofReal hnv.2)
    -- the small-distance event
    have hB : pinLaw d 1 {g | (rho D g).1 (0, e₁ d) < v ^ 3} ≤ ENNReal.ofReal (c₁ * v ^ 2 / 4) := by
      refine (hsmall ξ hξ D hD (v ^ 3) (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : Kinv * v ≤ c₁ / 4 := by
        rw [lt_div_iff₀ (by positivity)] at hvK
        linarith
      calc Kinv * v ^ 3 = (Kinv * v) * v ^ 2 := by ring
        _ ≤ c₁ / 4 * v ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = c₁ * v ^ 2 / 4 := by ring
    -- the ratio event
    have hA := hratio ξ hξ η hη D E hD hE v hv hv1
    obtain ⟨g, hgA, hgB, hgC⟩ := p8a_exists_mem_diff (pinLaw d 1) (by positivity) hA hB hC
    -- the contradiction (3.11) at `g`
    have hA' := p8a_lt_of_logRatio_lt (by omega) (by linarith) hgA
    have hB' : v ^ 3 ≤ (rho D g).1 (0, e₁ d) := not_lt.1 hgB
    have hC' : CompOn (rho D g) (rho E g) ((1 + 2 * v)⁻¹ + v / 100) (v ^ 4 / 100) 1 := not_not.1 hgC
    have he₁ : e₁ d ∈ closedBall (0 : Rd d) 1 := by
      rw [mem_closedBall, dist_zero_right, HigherDimLFPP.norm_e₁ (by omega)]
    exact p8a_contra hv (by linarith) hB' hA'.le (hC' 0 (mem_closedBall_self zero_le_one) (e₁ d) he₁)
  refine ⟨hfirst, ?_⟩
  -- the second assertion
  have h2 := p8a_measure_inter_ge (pinLaw d 1) (by positivity) hfirst (hrefs ξ hξ η hη D E hD hE)
  rwa [show pstar - pstar / 2 = pstar / 2 by ring] at h2

/-- **Lemma 3.4, the favorable arc** (blueprint Part A `a:lem34`, last clause, with Lemma `a:lem-subdiv`(b)):
almost surely under `𝐏₁` (where `ρ^D_g`, `ρ^E_g` are length metrics), on `H↓(D, E; 1 + 2v) ∩ PairRefs(D, E; 𝓡)`
there are a `ρ^E_g`-witness `γ` with own-unit ratio `≤ 1 + 2v` and a favorable arc `η'` of it: one of the `N∗` pieces
of `γ`, a globally minimizing `ρ^E_g`-geodesic in `K` of speed `lam ∈ [m/N∗, M/N∗]` with the two-sided moduli,
endpoint separation `≥ w∗`, `ρ^E_g`-length `≥ d∗`, and `ρ^E_g(η' 0, η' 1) ≤ (1 + 2v) ρ^D_g(η' 0, η' 1)`, the
`ρ^D_g`-distance of its endpoints being realized inside `A`. -/
theorem lemma34_arc (hd : 2 ≤ d) {ξ η : ℝ} {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) (hE : IsStrongExpMetric d η (distExp d η) E)
    {H₀ σ₀ β₀ m M : ℝ} (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m) {v : ℝ} (hv : 0 ≤ v) :
    ∀ᵐ g ∂(pinLaw d 1), g ∈ Hdown D E (1 + 2 * v) ∩ PairRefs D E H₀ σ₀ β₀ m M →
      ∃ γ : C(unitInterval, Rd d), IsWitness (rho E g) γ ∧
        (rho E g).internal (annA d) (γ 0) (γ 1) ≤
          ENNReal.ofReal (1 + 2 * v) * (rho D g).internal (annA d) (γ 0) (γ 1) ∧
        ∃ η' : ℝ → Rd d, ∃ lam : ℝ,
          (∃ i : ℕ, i < subdivN H₀ σ₀ β₀ M ∧ η' = subdivPiece γ (subdivN H₀ σ₀ β₀ M) i) ∧
          m / subdivN H₀ σ₀ β₀ M ≤ lam ∧ lam ≤ M / subdivN H₀ σ₀ β₀ M ∧
          ENNReal.ofReal (lam * subdivN H₀ σ₀ β₀ M) = (rho E g).internal (annA d) (γ 0) (γ 1) ∧
          IsSubdivPiece (rho E g) H₀ σ₀ β₀ (subdivDelta0 H₀ σ₀ β₀) lam η' ∧
          subdivW H₀ σ₀ β₀ m M ≤ ‖η' 0 - η' 1‖ ∧
          subdivD H₀ σ₀ β₀ m M ≤ (rho E g).1 (η' 0, η' 1) ∧
          (rho E g).1 (η' 0, η' 1) ≤ (1 + 2 * v) * (rho D g).1 (η' 0, η' 1) ∧
          (rho D g).internal (annA d) (η' 0) (η' 1) = ENNReal.ofReal ((rho D g).1 (η' 0, η' 1)) := by
  filter_upwards [p5b_ae_isLength_rho hd hD one_pos, p5b_ae_isLength_rho hd hE one_pos] with g hlD hlE hg
  obtain ⟨hdown, hrefs⟩ := hg
  obtain ⟨γ, hγ, hgood⟩ := hdown
  exact ⟨γ, hγ, hgood, hdown_subdivision hlD hlE hH₀ hσ₀ hβ₀ hm hrefs.1 hrefs.2 (by linarith) hγ hgood⟩

end HigherDimLQGContinuity
