import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.ClosedLocal
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S9
import LQGMetric.Field.HarmExistA




 












set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC restrictTo addConst)

theorem acr_eq_of_internal_eq (D₁ D₂ : LSCMetric) (hB₁ : BiLipschitz.Barrier.Barrier D₁) (hB₂ : BiLipschitz.Barrier.Barrier D₂)
    (hL₁ : D₁.IsLengthSpace) (hL₂ : D₂.IsLengthSpace) (U : Set ℂ)
    (hint : D₁.internal U = D₂.internal U) (w : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hK : Objects.CorrectedEvent.cann w a b ⊆ U) : Objects.CorrectedEvent.acr D₁ w a b = Objects.CorrectedEvent.acr D₂ w a b := by
  let A : EuclideanAnnulus := ⟨(w, a, b), ha, hab⟩
  have hY : BiLipschitz.Barrier.closedAnn A.center A.innerRadius A.outerRadius ⊆ U := by
    intro x hx
    apply hK
    simpa only [A, EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
      EuclideanAnnulus.outerRadius, BiLipschitz.Barrier.closedAnn, Objects.CorrectedEvent.cann,
      mem_ofPred_eq, dist_eq_norm] using hx
  rw [Objects.ProbabilityS3.acr_eq_ambientAcross_of_barrier D₁ hB₁ hL₁ w a b ha hab,
    Objects.ProbabilityS3.acr_eq_ambientAcross_of_barrier D₂ hB₂ hL₂ w a b ha hab]
  change acrossDist D₁ A = acrossDist D₂ A
  rw [BiLipschitz.Barrier.acrossDist_eq_iInf_internal D₁ hB₁ hL₁ A hY,
    BiLipschitz.Barrier.acrossDist_eq_iInf_internal D₂ hB₂ hL₂ A hY, hint]

theorem around_eq_of_internal_eq (D₁ D₂ : LSCMetric) (U : Set ℂ)
    (hint : D₁.internal U = D₂.internal U) (w : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hA : Objects.CorrectedEvent.ann w a b ⊆ U) : Objects.CorrectedEvent.around D₁ w a b = Objects.CorrectedEvent.around D₂ w a b := by
  rw [Objects.ClauseMeasurability.around_eq_aroundDist D₁ w a b ha hab, Objects.ClauseMeasurability.around_eq_aroundDist D₂ w a b ha hab]
  apply BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq D₁ D₂ U hint
  intro x hx
  apply hA
  change x ∈ ball w b \ closure (ball w a) at hx
  rw [closure_ball w ha.ne'] at hx
  simp only [Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hx
  exact ⟨hx.2, hx.1⟩

theorem apply_eq_of_restrictTo_eq {U : TopologicalSpace.Opens ℂ} {g₁ g₂ : DistC}
    (h : restrictTo U g₁ = restrictTo U g₂) (φ : LQGMetric.TestC)
    (hφ : tsupport (φ : ℂ → ℝ) ⊆ U) : g₁ φ = g₂ φ := by
  rw [← LQGMetric.HarmExist.restrictTo_testOnHE U g₁ φ hφ,
    ← LQGMetric.HarmExist.restrictTo_testOnHE U g₂ φ hφ, h]

theorem circleAvg_eq_of_restrictTo_eq {U : TopologicalSpace.Opens ℂ} {g₁ g₂ : DistC}
    (h : restrictTo U g₁ = restrictTo U g₂) {r ε : ℝ} {z : ℂ} (hε : 0 < ε)
    (hU : thickening ε (sphere z |r|) ⊆ U) :
    LQGMetric.circleAvg g₁ r z = LQGMetric.circleAvg g₂ r z := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hev : (fun n : ℕ => Real.circleAverage (fun x => g₁ (LQGMetric.bumpTest n x)) z r) =ᶠ[atTop]
      (fun n : ℕ => Real.circleAverage (fun x => g₂ (LQGMetric.bumpTest n x)) z r) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    apply Real.circleAverage_congr_sphere
    intro x hx
    have hsupp : tsupport (LQGMetric.bumpTest n x : ℂ → ℝ) ⊆ U := by
      rw [LQGMetric.GM.tsupport_bumpTest]
      intro y hy
      apply hU
      refine mem_thickening_iff.2 ⟨x, hx, ?_⟩
      rw [mem_closedBall] at hy
      calc dist y x ≤ (2 : ℝ)⁻¹ ^ n := hy
        _ ≤ (2 : ℝ)⁻¹ ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
        _ < ε := hN
    exact apply_eq_of_restrictTo_eq h _ hsupp
  unfold LQGMetric.circleAvg limUnder
  rw [Filter.map_congr hev]

theorem pair0_eq_of_restrictTo_eq {U : TopologicalSpace.Opens ℂ} {g₁ g₂ : DistC}
    (h : restrictTo U g₁ = restrictTo U g₂) (φ : LQGMetric.TestC0)
    (hφ : tsupport (φ.1 : ℂ → ℝ) ⊆ U) : LQGMetric.pair0 g₁ φ = LQGMetric.pair0 g₂ φ :=
  apply_eq_of_restrictTo_eq h φ.1 hφ

theorem pair0_cmTest0_addConst (g : DistC) (f : LQGMetric.TestC) (c : ℝ) :
    LQGMetric.pair0 (addConst g c) (LQGMetric.cmTest0 f) =
      LQGMetric.pair0 g (LQGMetric.cmTest0 f) := by
  show addConst g c (LQGMetric.cmTest f) = g (LQGMetric.cmTest f)
  rw [LQGMetric.GFFInv.addConst_apply, LQGMetric.integral_cmTest, zero_mul, add_zero]

theorem tsupport_cmTest_subset (f : LQGMetric.TestC) :
    tsupport (LQGMetric.cmTest f : ℂ → ℝ) ⊆ tsupport (f : ℂ → ℝ) :=
  closure_minimal (fun x hx => by_contra fun h' => hx (by
    rw [LQGMetric.cmTest_apply, QuantumZipper.K3.laplacian_eq_zero_of_notMem_tsupport h', mul_zero]))
    (isClosed_tsupport _)

theorem normalizer_eq_of_circleAvg_eq (C : Objects.CorrectedEvent.Constants) {g₁ g₂ : DistC} {s : ℝ} {w : ℂ}
    (h : LQGMetric.circleAvg g₁ s w = LQGMetric.circleAvg g₂ s w) :
    Objects.CorrectedEvent.normalizer C g₁ s w = Objects.CorrectedEvent.normalizer C g₂ s w := by
  unfold Objects.CorrectedEvent.normalizer
  rw [h]

theorem normalizer_addConst (C : Objects.CorrectedEvent.Constants) {g : DistC} {s : ℝ} {w : ℂ} {c : ℝ}
    (hc : LQGMetric.circleAvg (addConst g c) s w = LQGMetric.circleAvg g s w + c) :
    Objects.CorrectedEvent.normalizer C (addConst g c) s w =
      ENNReal.ofReal (Real.exp (C.ξ * c)) * Objects.CorrectedEvent.normalizer C g s w := by
  unfold Objects.CorrectedEvent.normalizer
  rw [hc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [mul_add, Real.exp_add]
  ring

 

theorem scale_pos_iff {e : ℝ≥0∞} (he0 : e ≠ 0) (x : ℝ≥0∞) : 0 < e * x ↔ 0 < x := by
  rw [ENNReal.mul_pos_iff]
  simp [pos_iff_ne_zero, he0]

theorem scale_lt_top_iff {e : ℝ≥0∞} (he0 : e ≠ 0) (heTop : e ≠ ⊤) (x : ℝ≥0∞) :
    e * x < ⊤ ↔ x < ⊤ := by
  constructor
  · intro hx
    exact ENNReal.lt_top_of_mul_ne_top_right hx.ne he0
  · intro hx
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr heTop) hx

theorem scale_le_iff {e : ℝ≥0∞} (he0 : e ≠ 0) (heTop : e ≠ ⊤) (a x y : ℝ≥0∞) :
    a * (e * x) ≤ e * y ↔ a * x ≤ y := by
  rw [mul_left_comm a e x, ENNReal.mul_le_mul_iff_right he0 heTop]

theorem scale_le_iff' {e : ℝ≥0∞} (he0 : e ≠ 0) (heTop : e ≠ ⊤) (a x y : ℝ≥0∞) :
    e * x ≤ a * (e * y) ↔ x ≤ a * y := by
  rw [mul_left_comm a e y, ENNReal.mul_le_mul_iff_right he0 heTop]

theorem scale_lt_iff' {e : ℝ≥0∞} (he0 : e ≠ 0) (heTop : e ≠ ⊤) (a x y : ℝ≥0∞) :
    e * x < a * (e * y) ↔ x < a * y := by
  rw [mul_left_comm a e y, ENNReal.mul_lt_mul_iff_right he0 heTop]

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
