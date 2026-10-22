import HigherDimLQGContinuity.Sewing.Crossing
import HigherDimLQGContinuity.Sewing.Spheres
import HigherDimLQGMetric.Shell.Chain
import LQGMetric.Metric.CurveLength

/-!
# Lemma 3.1(a): path replacement by sphere shortcuts

The existing `HigherDimLQGMetric.sphere_chain` supplies the finite exit chain and
backward elimination of nested balls. The local crossing estimate below converts its
time-increment premise into the assumptions of the comparison lemma.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric (ContMetric)
open LQGMetric.MetricGeometry
open scoped ENNReal

/-- A ball indexed by its center and radius. -/
abbrev SewBall (d : ℕ) := Rd d × ℝ

private theorem sew31a_unit {d : ℕ} (hd : 2 ≤ d)
    (R Q : ContMetric d) (F : Finset (SewBall d))
    (SR SQ : SewBall d → ℝ) (rm rp m M L : ℝ)
    (hrm : 0 < rm) (hm : 0 < m) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hF : ∀ B ∈ F, rm ≤ B.2 ∧ B.2 ≤ rp ∧ 0 < SR B ∧
      0 < SQ B ∧ SQ B ≤ L * SR B)
    (hcross : ∀ B ∈ F,
      ENNReal.ofReal (m * SR B) ≤
        HigherDimLQGMetric.setDistIn R Set.univ
          (sphere B.1 (3 * B.2 / 4)) (sphere B.1 B.2))
    (hdiam : ∀ B ∈ F,
      HigherDimLQGMetric.diamIn Q
        (HigherDimLQGMetric.ann B.1 (B.2 / 2) (7 * B.2 / 2))
        (sphere B.1 B.2) ≤ ENNReal.ofReal (M * SQ B))
    (P : ℝ → Rd d) (hP : ContinuousOn P (Icc 0 1))
    (hfinite : R.len P 0 1 ≠ ⊤)
    (hcov : ∀ u ∈ Icc (0 : ℝ) 1, ∃ B ∈ F, ‖P u - B.1‖ < B.2 / 10) :
    ∃ x' y' : Rd d, ‖x' - P 0‖ ≤ 2 * rp ∧ ‖y' - P 1‖ ≤ 2 * rp ∧
      ENNReal.ofReal (Q.1 (x', y')) ≤
        ENNReal.ofReal (2 * (M / m) * L) * R.len P 0 1 := by
  let C : ℝ := M / m * L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcover' : ∀ u ∈ Icc (0 : ℝ) 1,
      ∃ w r, rm ≤ r ∧ r ≤ rp ∧ ‖P u - w‖ < r / 2 ∧ (w, r) ∈ F := by
    intro u hu
    obtain ⟨B, hBF, hcent⟩ := hcov u hu
    refine ⟨B.1, B.2, (hF B hBF).1, (hF B hBF).2.1, ?_, hBF⟩
    linarith [(hF B hBF).1, hcent]
  have hgood : ∀ w r, (w, r) ∈ F →
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        a ≤ b → ‖P a - w‖ < r / 2 → ‖P b - w‖ = r →
        ∀ u ∈ sphere w r, ∀ v ∈ sphere w r,
          edist (Q.pt u) (Q.pt v) ≤
            ENNReal.ofReal C *
              ENNReal.ofReal ((R.len P 0 b).toReal - (R.len P 0 a).toReal) := by
    intro w r hwr a ha b hb hab hcent hexit u hu v hv
    let B : SewBall d := (w, r)
    have hBF : B ∈ F := hwr
    have hSR : 0 < SR B := (hF B hBF).2.2.1
    have hSQ : SQ B ≤ L * SR B := (hF B hBF).2.2.2.2
    have hr : 0 < r := lt_of_lt_of_le hrm (hF B hBF).1
    have hlenlower : ENNReal.ofReal (m * SR B) ≤ R.len P a b :=
      (hcross B hBF).trans
        (sew_crossing_lower R P hab (hP.mono (Icc_subset_Icc ha.1 hb.2))
          w hr hcent hexit)
    have hlenfinite : R.len P a b ≠ ⊤ :=
      ne_top_of_le_ne_top hfinite (R.len_mono P ha.1 hb.2)
    have hreal : m * SR B ≤ (R.len P a b).toReal := by
      have h := ENNReal.toReal_mono hlenfinite hlenlower
      simpa [ENNReal.toReal_ofReal (mul_nonneg hm.le hSR.le)] using h
    have hcoef : M * SQ B ≤ C * (R.len P a b).toReal := by
      calc
        M * SQ B ≤ M * (L * SR B) := mul_le_mul_of_nonneg_left hSQ hM
        _ = C * (m * SR B) := by
          dsimp [C]
          field_simp
        _ ≤ C * (R.len P a b).toReal := mul_le_mul_of_nonneg_left hreal hC
    have hqdiam : edist (Q.pt u) (Q.pt v) ≤
        ENNReal.ofReal (M * SQ B) := by
      rw [Q.edist_pt]
      calc
        ENNReal.ofReal (Q.1 (u, v)) ≤
            Q.internal (HigherDimLQGMetric.ann w (r / 2) (7 * r / 2)) u v :=
          Q.ofReal_le_internal _ _ _
        _ ≤ HigherDimLQGMetric.diamIn Q
            (HigherDimLQGMetric.ann w (r / 2) (7 * r / 2)) (sphere w r) := by
          unfold HigherDimLQGMetric.diamIn
          exact le_iSup_of_le u (le_iSup_of_le hu
            (le_iSup_of_le v (le_iSup_of_le hv le_rfl)))
        _ ≤ ENNReal.ofReal (M * SQ B) := hdiam B hBF
    have hdiff := sew_cumulative_diff R P hfinite ha hb hab
    rw [hdiff]
    calc
      edist (Q.pt u) (Q.pt v) ≤ ENNReal.ofReal (M * SQ B) := hqdiam
      _ ≤ ENNReal.ofReal (C * (R.len P a b).toReal) :=
        ENNReal.ofReal_le_ofReal hcoef
      _ = ENNReal.ofReal C * ENNReal.ofReal (R.len P a b).toReal := by
        rw [ENNReal.ofReal_mul hC]
  obtain ⟨x', y', hx', hy', hxy⟩ := HigherDimLQGMetric.sphere_chain hd
    (fun u v => edist (Q.pt u) (Q.pt v))
    (fun x => edist_self _) (fun x y z => edist_triangle _ _ _)
    hrm P hP (fun u => (R.len P 0 u).toReal)
    (sew_cumulative_mono R P hfinite)
    (fun w r => (w, r) ∈ F) hcover'
    (ENNReal.ofReal C) hgood
  refine ⟨x', y', hx', hy', ?_⟩
  rw [Q.edist_pt] at hxy
  have hlenReal : ENNReal.ofReal ((R.len P 0 1).toReal - (R.len P 0 0).toReal) =
      R.len P 0 1 := by
    simpa [R.len_of_ge P (le_refl 0)] using ENNReal.ofReal_toReal hfinite
  rw [hlenReal] at hxy
  have htwice : C ≤ 2 * (M / m) * L := by
    calc
      C ≤ 2 * C := by linarith
      _ = 2 * (M / m) * L := by dsimp [C]; ring
  apply hxy.trans
  gcongr

/-- Lemma 3.1(a), with an arbitrary compact parameter interval `[0,ℓ]`. -/
theorem lemma31a {d : ℕ} (hd : 2 ≤ d)
    (R Q : ContMetric d) (F : Finset (SewBall d))
    (SR SQ : SewBall d → ℝ) (ℓ rm rp m M L : ℝ)
    (hℓ : 0 ≤ ℓ) (hrm : 0 < rm) (hm : 0 < m) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hF : ∀ B ∈ F, rm ≤ B.2 ∧ B.2 ≤ rp ∧ 0 < SR B ∧
      0 < SQ B ∧ SQ B ≤ L * SR B)
    (hcross : ∀ B ∈ F,
      ENNReal.ofReal (m * SR B) ≤
        HigherDimLQGMetric.setDistIn R Set.univ
          (sphere B.1 (3 * B.2 / 4)) (sphere B.1 B.2))
    (hdiam : ∀ B ∈ F,
      HigherDimLQGMetric.diamIn Q
        (HigherDimLQGMetric.ann B.1 (B.2 / 2) (7 * B.2 / 2))
        (sphere B.1 B.2) ≤ ENNReal.ofReal (M * SQ B))
    (P : ℝ → Rd d) (hP : ContinuousOn P (Icc 0 ℓ))
    (hfinite : R.len P 0 ℓ ≠ ⊤)
    (hcov : ∀ u ∈ Icc (0 : ℝ) ℓ, ∃ B ∈ F, ‖P u - B.1‖ < B.2 / 10) :
    ∃ x' y' : Rd d, ‖x' - P 0‖ ≤ 2 * rp ∧ ‖y' - P ℓ‖ ≤ 2 * rp ∧
      ENNReal.ofReal (Q.1 (x', y')) ≤
        ENNReal.ofReal (2 * (M / m) * L) * R.len P 0 ℓ := by
  rcases hℓ.eq_or_lt with hzero | hpos
  · subst ℓ
    obtain ⟨B, hBF, hcent⟩ := hcov 0 ⟨le_rfl, le_rfl⟩
    have hrad : 0 < B.2 := lt_of_lt_of_le hrm (hF B hBF).1
    have hrp : B.2 ≤ rp := (hF B hBF).2.1
    refine ⟨B.1, B.1, ?_, ?_, ?_⟩
    · have hnorm : ‖B.1 - P 0‖ = ‖P 0 - B.1‖ := norm_sub_rev _ _
      rw [hnorm]
      linarith
    · have hnorm : ‖B.1 - P 0‖ = ‖P 0 - B.1‖ := norm_sub_rev _ _
      rw [hnorm]
      linarith
    · simp [Q.apply_self, R.len_of_ge P (le_refl 0)]
  · let φ : ℝ → ℝ := fun u => ℓ * u
    let P₁ : ℝ → Rd d := P ∘ φ
    have hφc : ContinuousOn φ (Icc (0 : ℝ) 1) := by
      dsimp [φ]
      fun_prop
    have hφm : MonotoneOn φ (Icc (0 : ℝ) 1) := by
      intro u _ v _ huv
      exact mul_le_mul_of_nonneg_left huv hpos.le
    have hφmap : MapsTo φ (Icc (0 : ℝ) 1) (Icc 0 ℓ) := by
      intro u hu
      change 0 ≤ ℓ * u ∧ ℓ * u ≤ ℓ
      constructor
      · exact mul_nonneg hpos.le hu.1
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hu.2 hpos.le
    have hP₁ : ContinuousOn P₁ (Icc (0 : ℝ) 1) := hP.comp hφc hφmap
    have hlen : R.len P₁ 0 1 = R.len P 0 ℓ := by
      have h := curveLength_comp_of_continuousOn_monotoneOn
        (R.pt ∘ P) zero_le_one hφc hφm
      simpa only [P₁, φ, R.len_def, Function.comp_def, mul_zero, mul_one] using h
    have hcov₁ : ∀ u ∈ Icc (0 : ℝ) 1, ∃ B ∈ F, ‖P₁ u - B.1‖ < B.2 / 10 := by
      intro u hu
      exact hcov (φ u) (hφmap hu)
    obtain ⟨x', y', hx', hy', hxy⟩ :=
      sew31a_unit hd R Q F SR SQ rm rp m M L hrm hm hM hL
        hF hcross hdiam P₁ hP₁ (hlen ▸ hfinite) hcov₁
    refine ⟨x', y', ?_, ?_, ?_⟩
    · simpa only [P₁, φ, Function.comp_def, mul_zero] using hx'
    · simpa only [P₁, φ, Function.comp_def, mul_one] using hy'
    · rwa [hlen] at hxy

end HigherDimLQGContinuity
