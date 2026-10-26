import SupercriticalConformalCovariance.BiLip.Source
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Tail

/-!
# Lemma 2.1, steps 1 and 3: source tightness and the loop-to-crossing comparison (4)

**Step 1** (l. 100–107): "Set `m_{z,r} = r^{ξQ} e^{ξ h_r(z)}`. Fix `K ⋐ U`. The source quantities
`m⁻¹ D_h(around A_{r,2r}(z))`, `m D_h(across A_{r/2,r}(z))⁻¹` are tight uniformly for `z ∈ K` and `r` small by
affine covariance and the annular estimates of [1]."
These are the sealed annulus tail bounds (`Objects.AnnulusTails.around_upper_tail`, `acr_lower_tail`), which holds
for EVERY `z ∈ ℂ` and EVERY `r > 0`, uniformly over normalized whole-plane GFFs, for a weak LQG metric
with `Q > 0` (`source_tails`). The normalizer is `nrm ξ Q h r z = r^{ξQ} e^{ξ h_r(z)}`, the paper's `m_{z,r}`.

**Step 3** (l. 128–132): "for each prescribed `p < 1`, there is `C0 = C0(p, ξ)` such that, for all sufficiently
small `r` and all `z ∈ K`, `P[e(around A_{r,2r}(z)) ≤ C0 D_h(across A_{r/2,r}(z))] ≥ p`. No independence of
the two displayed distances is used." This is the union bound `prob_lt_of_tails`: an upper tail of
`m⁻¹ X` and a lower tail of `m⁻¹ Y` at level `M`, each of probability `≤ δ`, give
`P[X < 2M² Y] ≥ 1 − 2δ`. The strict inequality, with `Y > 0`, is what the chain consumes.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric IsWeakLQGMetric IsNormalizedWholePlaneGFF)
open SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails (nrm around_upper_tail acr_lower_tail)
open LQGMetric (DistC)

/-! ## Step 3: the union bound -/

/-- On `{X ≤ M m} ∩ {M⁻¹ m ≤ Y}` with `0 < m < ∞`: `X < 2M² Y`. -/
theorem lt_of_tails_compl {X Y m : ℝ≥0∞} (hm0 : 0 < m) (hmt : m < ∞) {M : ℝ} (hM : 0 < M)
    (hX : X ≤ ENNReal.ofReal M * m) (hY : ENNReal.ofReal M⁻¹ * m ≤ Y) :
    X < ENNReal.ofReal (2 * M ^ 2) * Y := by
  have hM0 : ENNReal.ofReal M ≠ 0 := (ENNReal.ofReal_pos.2 hM).ne'
  have hMt : ENNReal.ofReal M ≠ ∞ := ENNReal.ofReal_ne_top
  have hXt : X < ∞ := lt_of_le_of_lt hX (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmt)
  have hMM : ENNReal.ofReal M * ENNReal.ofReal M⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hM.le, mul_inv_cancel₀ hM.ne', ENNReal.ofReal_one]
  -- `M m ≤ M² Y`
  have hmY : ENNReal.ofReal M * m ≤ ENNReal.ofReal (M ^ 2) * Y := by
    calc ENNReal.ofReal M * m = ENNReal.ofReal M * (ENNReal.ofReal M * (ENNReal.ofReal M⁻¹ * m)) := by
          rw [← mul_assoc (ENNReal.ofReal M) (ENNReal.ofReal M⁻¹) m, hMM, one_mul]
      _ ≤ ENNReal.ofReal M * (ENNReal.ofReal M * Y) := by gcongr
      _ = ENNReal.ofReal (M ^ 2) * Y := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hM.le, sq]
  have hpos : 0 < ENNReal.ofReal (M ^ 2) * Y :=
    lt_of_lt_of_le (ENNReal.mul_pos hM0 hm0.ne') hmY
  rcases eq_top_or_lt_top Y with hYt | hYt
  · rw [hYt, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']; exact hXt
  · have hfin : ENNReal.ofReal (M ^ 2) * Y < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hYt
    calc X ≤ ENNReal.ofReal (M ^ 2) * Y := hX.trans hmY
      _ < 2 * (ENNReal.ofReal (M ^ 2) * Y) := by
          rw [two_mul]; exact ENNReal.lt_add_right hfin.ne hpos.ne'
      _ = ENNReal.ofReal (2 * M ^ 2) * Y := by
          rw [← mul_assoc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- **(4), the union bound** (l. 128–132). No independence is used: only the two marginal tails. -/
theorem prob_lt_of_tails {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y m : Ω → ℝ≥0∞) (hm : ∀ ω, 0 < m ω ∧ m ω < ∞) {M δ : ℝ} (hM : 0 < M) (hδ : 0 ≤ δ)
    (hX : P {ω | ENNReal.ofReal M * m ω < X ω} ≤ ENNReal.ofReal δ)
    (hY : P {ω | Y ω < ENNReal.ofReal M⁻¹ * m ω} ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (1 - 2 * δ) ≤ P {ω | X ω < ENNReal.ofReal (2 * M ^ 2) * Y ω} := by
  set F := {ω | X ω < ENNReal.ofReal (2 * M ^ 2) * Y ω}
  have hsub : Fᶜ ⊆ {ω | ENNReal.ofReal M * m ω < X ω} ∪ {ω | Y ω < ENNReal.ofReal M⁻¹ * m ω} := by
    intro ω hω
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hn
    exact hω (lt_of_tails_compl (hm ω).1 (hm ω).2 hM hn.1 hn.2)
  have h1 : (1 : ℝ≥0∞) ≤ P F + ENNReal.ofReal (2 * δ) := by
    calc (1 : ℝ≥0∞) = P (F ∪ Fᶜ) := by rw [union_compl_self, measure_univ]
      _ ≤ P F + P Fᶜ := measure_union_le _ _
      _ ≤ P F + (ENNReal.ofReal δ + ENNReal.ofReal δ) := by
          gcongr
          exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hX hY))
      _ = P F + ENNReal.ofReal (2 * δ) := by
          rw [← ENNReal.ofReal_add hδ hδ, two_mul]
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  exact tsub_le_iff_right.2 h1

/-! ## Step 1: source tightness (sealed annulus tail bounds) -/

open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent (acr around)

theorem nrm_pos_lt_top (ξ Q : ℝ) (g : DistC) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    0 < nrm ξ Q g r z ∧ nrm ξ Q g r z < ∞ :=
  ⟨ENNReal.ofReal_pos.2 (mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)),
    ENNReal.ofReal_lt_top⟩

/-- **Step 1** (l. 100–107): for every `δ > 0` there is `M` such that, for EVERY normalized whole-plane GFF,
every `z ∈ ℂ` and every `r > 0`, `P[D_h(around A_{r,2r}(z)) > M m_{z,r}] ≤ δ` and
`P[D_h(across A_{r/2,r}(z)) < M⁻¹ m_{z,r}] ≤ δ`. -/
theorem source_tails (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
        P {ω | ENNReal.ofReal M * nrm ξ Q (h ω) r z < aroundHit (D (h ω)) z r} ≤
            ENNReal.ofReal δ ∧
          P {ω | acrAt (D (h ω)) z r < ENNReal.ofReal M⁻¹ * nrm ξ Q (h ω) r z} ≤
            ENNReal.ofReal δ := by
  obtain ⟨R₁, C₁, hR₁, hC₁, hup⟩ := around_upper_tail ξ Q hQ D hD (a := 1) (b := 2) one_pos
    one_lt_two 1 one_pos
  obtain ⟨R₂, C₂, hR₂, hC₂, hlow⟩ := acr_lower_tail ξ Q hQ D hD (a := 1 / 2) (b := 1)
    (by norm_num) (by norm_num) 1 one_pos
  set M : ℝ := max (max R₁ R₂) (max (C₁ / δ) (C₂ / δ)) with hMdef
  have hM1 : 1 ≤ M := le_trans hR₁ (le_trans (le_max_left _ _) (le_max_left _ _))
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  have hbound : ∀ C : ℝ, 0 < C → C / δ ≤ M → C * M ^ (-(1 : ℝ)) ≤ δ := by
    intro C hC hCM
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hM0]
    rw [div_le_iff₀ hδ] at hCM
    linarith
  refine ⟨M, hM0, ?_⟩
  intro Ω _ P _ h hh z r hr
  have hR₁M : R₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR₂M : R₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC₁M : C₁ / δ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC₂M : C₂ / δ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  constructor
  · have h1 := hup P h hh M hR₁M ⟨r, hr⟩ z
    simp only [one_mul] at h1
    exact h1.trans (ENNReal.ofReal_le_ofReal (hbound C₁ hC₁ hC₁M))
  · have h2 := hlow P h hh M hR₂M ⟨r, hr⟩ z
    simp only [one_mul] at h2
    have he : (1 / 2 : ℝ) * r = r / 2 := by ring
    rw [he] at h2
    exact h2.trans (ENNReal.ofReal_le_ofReal (hbound C₂ hC₂ hC₂M))

end SupercriticalConformalCovariance.BiLip
