import SupercriticalLFPPAS.Escape.Deterministic
import SupercriticalLFPPAS.Inputs.EscapeTendsto
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong

/-!
# Lemma 6.2: almost sure confinement through all cutoffs (packet L62)

Paper `source/almost-sure-supercritical-lfpp.txt`, Lemma 6.2 (l. 605–622); binding proof: planning audit
`planning/audits/SB2-sections-3-7.md` §2.7 and Details **D10** (with M10), SB3 §2 "Lemma 6.2".

* `ae_compare_mesh` (D10 step 1, M10): for a fixed `U` with the polynomial failure bound `c₀ε^{p₀}` of (2.8), the mesh
  exponent `a = 2/p₀` makes the failure probabilities `c₀n^{-2}` summable; by Borel–Cantelli for outer measures
  (`MeasureTheory.ae_eventually_notMem`), almost surely (2.8) holds eventually on the mesh `n^{-a}`.
* `lemma62_of` (Lemma 6.2, interface `Core.Lemma62Stmt`, I28): from (2.8) (`Core.LocCompareStmt`, with `ζ = 1/2` and
  `U = B_{R+1}(0)` for every integer `R`), (2.1), (2.2), (6.1) and (1.4) (`ae_d2EscapeSetDist_tendsto`), via the
  deterministic `Escape.escape_core` on the countable intersection of the probability-one events.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Escape

open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog (compareHolds)

/-- **Borel–Cantelli on the mesh for (2.8)** (SB2 D10 step 1, M10). If the comparison (2.8) on `U` at radius
`ε^{1−ζ}` fails with outer probability at most `c₀ε^{p₀}` for `ε < ε₀`, then, almost surely, it holds eventually on the
mesh `n^{-a}`, `a = 2/p₀`. -/
theorem ae_compare_mesh (S : Core.Setup) {ζ C₀ p₀ c₀ ε₀ : ℝ} {U : Set ℂ} (hp₀ : 0 < p₀) (hc₀ : 0 < c₀)
    (hε₀ : 0 < ε₀) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hP : ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
      P {ω | ¬ compareHolds (Core.locMetric S ε hε (h ω)) (S.D (h ω)) (ε ^ (1 - ζ)) U C₀} ≤
        ENNReal.ofReal (c₀ * ε ^ p₀)) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ hδ : (n : ℝ) ^ (-(2 / p₀)) ∈ Ioo (0 : ℝ) 1,
      compareHolds (Core.locMetric S _ hδ (h ω)) (S.D (h ω)) (((n : ℝ) ^ (-(2 / p₀))) ^ (1 - ζ)) U C₀ := by
  have ha : 0 < 2 / p₀ := by positivity
  set a := 2 / p₀ with ha_def
  -- the failure events on the mesh (empty outside the range of (2.8))
  set Bad : ℕ → Set Ω := fun n => {ω | ∃ hδ : (n : ℝ) ^ (-a) ∈ Ioo (0 : ℝ) 1, (n : ℝ) ^ (-a) < ε₀ ∧
    ¬ compareHolds (Core.locMetric S _ hδ (h ω)) (S.D (h ω)) (((n : ℝ) ^ (-a)) ^ (1 - ζ)) U C₀} with hBad
  have hbound : ∀ n : ℕ, P (Bad n) ≤ ENNReal.ofReal (c₀ * (n : ℝ) ^ (-2 : ℝ)) := by
    intro n
    by_cases hn : ∃ hδ : (n : ℝ) ^ (-a) ∈ Ioo (0 : ℝ) 1, (n : ℝ) ^ (-a) < ε₀
    · obtain ⟨hδ, hδ₀⟩ := hn
      have hsub : Bad n ⊆ {ω | ¬ compareHolds (Core.locMetric S _ hδ (h ω)) (S.D (h ω))
          (((n : ℝ) ^ (-a)) ^ (1 - ζ)) U C₀} := fun ω hω => by
        obtain ⟨_, _, hω⟩ := hω
        exact hω
      have hpow : ((n : ℝ) ^ (-a)) ^ p₀ = (n : ℝ) ^ (-2 : ℝ) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 1
        rw [ha_def]
        field_simp
      calc P (Bad n) ≤ _ := measure_mono hsub
        _ ≤ ENNReal.ofReal (c₀ * ((n : ℝ) ^ (-a)) ^ p₀) := hP _ hδ hδ₀
        _ = ENNReal.ofReal (c₀ * (n : ℝ) ^ (-2 : ℝ)) := by rw [hpow]
    · have hempty : Bad n = ∅ := by
        ext ω
        simp only [hBad, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hδ, hδ₀, -⟩
        exact hn ⟨hδ, hδ₀⟩
      rw [hempty, measure_empty]
      exact zero_le
  have hsumm : Summable fun n : ℕ => c₀ * (n : ℝ) ^ (-2 : ℝ) :=
    (Real.summable_nat_rpow.2 (by norm_num)).mul_left c₀
  have hsum : ∑' n, P (Bad n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg hc₀.le (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hsumm]
    exact ENNReal.ofReal_ne_top
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-a) < ε₀ :=
    ((Main.tendsto_mesh_pow ha).mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hε₀)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω, hsmall] with n hn hnε hδ
  by_contra hcon
  exact hn ⟨hδ, hnε, hcon⟩

/-- **Lemma 6.2** (paper l. 605–622; SB2 D10; interface I28). Almost surely, for every compact `K` and every `M`, there
are `R` with `K ⊆ B_R(0)` and `ε₀ > 0` such that for every cutoff `ε < ε₀` the localized and the ordinary normalized
LFPP distances from `K` to `∂B_R(0)` exceed `M`. -/
theorem lemma62_of (S : Core.Setup) (hL : Core.LocCompareStmt S) (hA : Core.LocApproxStmt)
    (hM : Core.MeshOscStmt) (hW : Core.NormalizerWindowStmt S) : Core.Lemma62Stmt S := by
  intro Ω _ P _ h hh X hX
  obtain ⟨C₀, hC₀, hU⟩ := hL (1 / 2) (by norm_num) (by norm_num)
  -- (2.8) on `B_{R+1}(0)`, eventually on the mesh `n^{-a(R)}`, almost surely
  have hdata : ∀ R : ℕ, ∃ a : ℝ, 0 < a ∧ ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      ∀ hδ : (n : ℝ) ^ (-a) ∈ Ioo (0 : ℝ) 1,
        compareHolds (Core.locMetric S _ hδ (h ω)) (S.D (h ω)) (((n : ℝ) ^ (-a)) ^ (1 - 1 / 2 : ℝ))
          (ball (0 : ℂ) ((R : ℝ) + 1)) C₀ := by
    intro R
    obtain ⟨p₀, c₀, ε₀, hp₀, hc₀, hε₀, -, hP⟩ := hU (ball (0 : ℂ) ((R : ℝ) + 1)) isOpen_ball
      ((convex_ball (0 : ℂ) _).isConnected (nonempty_ball.2 (by positivity))) isBounded_ball
    exact ⟨2 / p₀, by positivity, ae_compare_mesh S hp₀ hc₀ hε₀ P h (hP P h hh)⟩
  choose a ha hae using hdata
  have hcomp := ae_all_iff.2 hae
  have hosc := ae_all_iff.2 fun R : ℕ => hM P h hh X hX (a R) (ha R)
  filter_upwards [hcomp, hosc, hA P h hh X hX,
    ae_d2EscapeSetDist_tendsto (B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric S.hD) P h hh]
    with ω h1 h2 h3 h4
  exact escape_core S hW (ζ := 1 / 2) (by norm_num) hC₀ ha (g := h ω) (Y := fun ε => X ε ω)
    h1 h3 h2 h4

end SupercriticalLFPPAS.Escape
