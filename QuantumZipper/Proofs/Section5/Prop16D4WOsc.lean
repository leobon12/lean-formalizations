import QuantumZipper.Proofs.Section5.Prop16D4WLoc
import QuantumZipper.Proofs.Section5.Prop16GNu

/-!
# Proposition 1.6, D4⁺ʷ input `hφ`: the continuous remainder is small at the canonical scale

Decision D24 (`DECISIONS.md`): `φ = ψ(a·) → 0` uniformly on bounded sets in probability, from the
continuity of `𝔥₀` and `a → 0`. Here `ψ(z) = 𝔥₀(z + t) − 𝔥₀(t)` with the marked point `t`
random in `(a,b)`, and the scale `s C ω → 0` in probability:

* `exists_uniform_osc`: a function continuous on `S` has uniformly small oscillation, relative
  to `S`, around a compact `K ⊆ S` (Lebesgue number lemma);
* `tendsto_prob_osc`: `Q{∃ z, z + t ∈ S, ‖z‖ < ρ s, |𝔥₀(z + t) − 𝔥₀(t)| > ε} → 0` for a finite
  measure `Q`, a measurable marked point `t ∈ (a,b)` a.s., `realSet (a,b) ⊆ S`.

This is the "approximately constant" step of Sheffield, arXiv:1012.4797, proof of Prop. 1.6
(p. 25). Own elementary argument (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-- **Uniform oscillation around a compact set** (relative to `S`). -/
theorem exists_uniform_osc {S : Set ℂ} {h0 : ℂ → ℝ} (hh : ContinuousOn h0 S) {K : Set ℂ}
    (hK : IsCompact K) (hKS : K ⊆ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ t ∈ K, ∀ w ∈ S, dist w t < r → |h0 w - h0 t| ≤ ε := by
  have hloc : ∀ t : K, ∃ r > 0, ∀ w ∈ S, dist w t < r → dist (h0 w) (h0 t) < ε / 2 :=
    fun t => Metric.continuousWithinAt_iff.1 (hh _ (hKS t.2)) _ (half_pos hε)
  choose r hr hrw using hloc
  obtain ⟨δ, hδ, hδK⟩ := lebesgue_number_lemma_of_metric (c := fun i : K => ball (i : ℂ) (r i))
    hK (fun _ => isOpen_ball) (fun t ht => mem_iUnion.2 ⟨⟨t, ht⟩, mem_ball_self (hr _)⟩)
  refine ⟨δ, hδ, fun t ht w hw hwt => ?_⟩
  obtain ⟨i, hi⟩ := hδK t ht
  have h1 := hrw i w hw (hi hwt)
  have h2 := hrw i t (hKS ht) (hi (mem_ball_self hδ))
  rw [Real.dist_eq] at h1 h2
  have := abs_sub_le (h0 w) (h0 i) (h0 t)
  rw [abs_sub_comm (h0 i) (h0 t)] at this
  linarith

/-- **The remainder is small at a vanishing scale, in probability.** -/
theorem tendsto_prob_osc {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsFiniteMeasure Q]
    {S : Set ℂ} {h0 : ℂ → ℝ} (hh : ContinuousOn h0 S) {a b : ℝ} (hab : realSet (Ioo a b) ⊆ S)
    (t : Ω → ℝ) (ht : Measurable t) (hta : ∀ᵐ ω ∂Q, t ω ∈ Ioo a b) (s : ℝ → Ω → ℝ)
    (hs : ∀ r > 0, Tendsto (fun C => Q {ω | ¬ s C ω < r}) atTop (𝓝 0)) {ρ ε : ℝ} (hρ : 0 < ρ)
    (hε : 0 < ε) :
    Tendsto (fun C => Q {ω | ¬ ∀ z : ℂ, z + (t ω : ℂ) ∈ S → ‖z‖ < ρ * s C ω →
      |h0 (z + t ω) - h0 (t ω)| ≤ ε}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro θ hθ
  -- the marked point stays in a compact part of `(a,b)` with high probability
  set A : ℕ → Set Ω := fun N => {ω | t ω ∉ Icc (a + 1 / ((N : ℝ) + 1)) (b - 1 / ((N : ℝ) + 1))}
  have hAm : ∀ N, MeasurableSet (A N) := fun N => (ht measurableSet_Icc).compl
  have hAa : Antitone A := fun m n hmn ω hω h => hω (by
    obtain ⟨h1, h2⟩ := h
    have h : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    exact ⟨by linarith, by linarith⟩)
  have hAi : Q (⋂ N, A N) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hta)
    simp only [mem_iInter] at hω
    intro htab
    obtain ⟨N, hN⟩ := Prop16Area.G.mem_iUnion_ioo htab
    exact hω N ⟨hN.1.le, hN.2.le⟩
  have hlim := tendsto_measure_iInter_atTop (μ := Q) (fun N => (hAm N).nullMeasurableSet) hAa
    ⟨0, measure_ne_top _ _⟩
  rw [hAi] at hlim
  have hθ2 : 0 < θ / 2 := ENNReal.div_pos hθ.ne' (by norm_num)
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1 hlim (θ / 2) hθ2).exists
  -- uniform oscillation on the compact part
  set K : Set ℂ := realSet (Icc (a + 1 / ((N : ℝ) + 1)) (b - 1 / ((N : ℝ) + 1)))
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKS : K ⊆ S := by
    rintro _ ⟨u, hu, rfl⟩
    have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    exact hab ⟨u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩
  obtain ⟨r, hr, hrK⟩ := exists_uniform_osc hh hK hKS hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (hs (r / ρ) (div_pos hr hρ))) (θ / 2) hθ2]
    with C hC
  refine (measure_mono (fun ω hω => ?_ : _ ⊆ A N ∪ {ω | ¬ s C ω < r / ρ})).trans
    ((measure_union_le _ _).trans ((add_le_add hN hC).trans (le_of_eq (ENNReal.add_halves θ))))
  simp only [mem_ofPred_eq] at hω
  by_contra hc
  simp only [mem_union, mem_ofPred_eq, not_or, not_not, A] at hc
  obtain ⟨htK, hsC⟩ := hc
  refine hω fun z hzS hz => ?_
  have hdist : dist (z + (t ω : ℂ)) (t ω : ℂ) < r := by
    rw [dist_eq_norm, add_sub_cancel_right]
    calc ‖z‖ < ρ * s C ω := hz
      _ < ρ * (r / ρ) := mul_lt_mul_of_pos_left hsC hρ
      _ = r := by field_simp
  exact hrK _ ⟨t ω, htK, rfl⟩ _ hzS hdist

end Prop16Asm

end QuantumZipper
