import HigherDimLQGContinuity.Caps.ShellEvents
import HigherDimLQGContinuity.Caps.CoverGeom
import HigherDimLQGMetric.WNSplit.Local
import HigherDimLFPP.Field.OscBlock

/-! Finite anchor covering estimate (2.10). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HigherDimLQGContinuity
open MeasureTheory Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt roundLat)

def p4_radius (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℝ))
private def p4_mesh (d : ℕ) (V : ℝ) : ℝ := Real.exp (-2 * V) / (100 * (d : ℝ))
private def p4_anchorGrid (d : ℕ) (W V : ℝ) : Finset (Rd d) :=
  HigherDimLFPP.Osc.grid 0 W (p4_mesh d V)
private def p4_round (d : ℕ) (k : ℕ) (a : Rd d) : Rd d :=
  latPt ((1 / (20 * Real.sqrt d)) * p4_radius k)
    (roundLat ((1 / (20 * Real.sqrt d)) * p4_radius k) a)

private theorem p4_radius_pos (k : ℕ) : 0 < p4_radius k := by
  unfold p4_radius
  positivity
private theorem p4_radius_step (k : ℕ) : p4_radius (k + 1) = (1 / 2 : ℝ) * p4_radius k := by
  unfold p4_radius
  have h : (-(↑(k + 1) : ℝ)) = -(k : ℝ) + -1 := by push_cast; ring
  rw [h, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  ring
private theorem p4_mesh_pos {d : ℕ} (hd : 2 ≤ d) (V : ℝ) : 0 < p4_mesh d V := by
  unfold p4_mesh
  have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  positivity
private theorem p4_mesh_small {d : ℕ} (hd : 2 ≤ d) {V r : ℝ}
    (hr : Real.exp (-2 * V) ≤ r) :
    (d : ℝ) * p4_mesh d V ≤ r / 100 := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold p4_mesh
  have heq : (d : ℝ) * (Real.exp (-2 * V) / (100 * d)) = Real.exp (-2 * V) / 100 := by
    field_simp
  rw [heq]
  linarith

private theorem p4_anchor_card {d : ℕ} (hd : 2 ≤ d) {W V : ℝ}
    (hW : 0 ≤ W) (hV : 0 ≤ V) :
    ((p4_anchorGrid d W V).card : ℝ) ≤
      (201 * (d : ℝ)) ^ d * (1 + W) ^ d * Real.exp (2 * d * V) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hm := p4_mesh_pos hd V
  have hc := HigherDimLFPP.Osc.card_grid_le (0 : Rd d) hW hm
  have hexp : 1 ≤ Real.exp (2 * V) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hbase : 2 * W / p4_mesh d V + 1 ≤
      201 * (d : ℝ) * (1 + W) * Real.exp (2 * V) := by
    unfold p4_mesh
    have heq : 2 * W / (Real.exp (-2 * V) / (100 * d)) =
        200 * d * W * Real.exp (2 * V) := by
      have he : Real.exp (-2 * V) = (Real.exp (2 * V))⁻¹ := by
        convert Real.exp_neg (2 * V) using 1
        ring
      rw [he]
      field_simp
      ring
    rw [heq]
    nlinarith [mul_nonneg (mul_nonneg hdp.le hW) (Real.exp_pos (2 * V)).le]
  calc
    ((p4_anchorGrid d W V).card : ℝ) ≤ (2 * W / p4_mesh d V + 1) ^ d := hc
    _ ≤ (201 * (d : ℝ) * (1 + W) * Real.exp (2 * V)) ^ d :=
      pow_le_pow_left₀ (by positivity) hbase d
    _ = (201 * (d : ℝ)) ^ d * (1 + W) ^ d * Real.exp (2 * d * V) := by
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
      congr 1
      ring

/-- The covering consequence (2.10) with the concentric shell exponent. -/
theorem cover210 {d : ℕ} (hd : 2 ≤ d) :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧
      ∀ {s s₀ : ℝ}, 1 ≤ s → s ≤ 10 → 1 ≤ s₀ → s₀ ≤ 10 →
      ∀ {E : Set (DistRd d)},
        AEEventIn (pinLaw d s) (fieldSigma0 id (ann 0 (1 / 2) (max (7 / 2) (s + 1)))) E →
      ∀ {p W V : ℝ}, 0 ≤ p → pinLaw d s Eᶜ ≤ ENNReal.ofReal p →
        0 ≤ W → 1 ≤ V →
      ∀ (T : Finset ℕ),
        (∀ k ∈ T, Real.exp (-2 * V) ≤ p4_radius k ∧
          p4_radius k ≤ Real.exp (-V)) →
      pinLaw d s₀ {g | ∃ x ∈ closedBall (0 : Rd d) W,
        ∀ k ∈ T, ∀ j : Fin d → ℤ,
          ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ < p4_radius k / 10 →
          recentre s (p4_radius k)
            (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) g ∉ E} ≤
        ENNReal.ofReal (C * (1 + W) ^ d * Real.exp (2 * d * V) *
          p ^ ((T.card : ℝ) / K)) := by
  classical
  obtain ⟨K, hK, hdec⟩ := p4_shell_event_bound (by omega : 1 ≤ d)
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 12) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨K, (201 * (d : ℝ)) ^ d, hK, ?_, ?_⟩
  · have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  intro s s₀ hs hs10 hs₀ hs₀10 E hE p W V hp hpE hW hV T hT
  let μ := p4_mesh d V
  let A := p4_anchorGrid d W V
  let z (k : ℕ) (a : Rd d) := p4_round d k a
  let B (a : Rd d) (k : ℕ) : Set (DistRd d) :=
    {g | recentre s (p4_radius k) (z k a) g ∈ Eᶜ}
  have hspos : 0 < s := by linarith
  have hs₀pos : 0 < s₀ := by linarith
  have hμ : 0 < μ := p4_mesh_pos hd V
  have hlocal (a : Rd d) (k : ℕ) :
      AEEventIn (pinLaw d s₀)
        (fieldSigma0 id (ann a ((1 / 4) * p4_radius k) (12 * p4_radius k)))
        (B a k) := by
    have hr := p4_radius_pos k
    have hnear : ‖z k a - a‖ ≤ p4_radius k / 20 := by
      simpa only [z, p4_round, norm_sub_rev] using p4_round_center hd hr a
    have hgeom := p4_affine_ann_subset hr hs hs10 hnear
    have hcompl := wns_aeEventIn_compl hE
    convert p4_aeEventIn_recentre hd hspos hs₀pos hr (z k a) hgeom hcompl using 1
    · simp only [one_div, inv_mul_eq_div]
  have hprob (a : Rd d) (k : ℕ) :
      pinLaw d s₀ (B a k) ≤ ENNReal.ofReal p := by
    exact (pinLaw_preimage_recentre_le hd hspos hs₀pos (p4_radius_pos k) (z k a) Eᶜ).trans hpE
  have hbadsub :
      {g | ∃ x ∈ closedBall (0 : Rd d) W,
        ∀ k ∈ T, ∀ j : Fin d → ℤ,
          ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ < p4_radius k / 10 →
          recentre s (p4_radius k)
            (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) g ∉ E} ⊆
        ⋃ a ∈ A, {g | ∀ k ∈ T, g ∈ B a k} := by
    intro g ⟨x, hx, hbad⟩
    let a := HigherDimLFPP.Osc.gridOf 0 W μ x
    have ha : a ∈ A := HigherDimLFPP.Osc.gridOf_mem_grid 0 hμ
      (l2a_closedBall_subset_box hx)
    refine mem_biUnion ha ?_
    intro k hk
    have hr := p4_radius_pos k
    have hxa : ‖x - a‖ ≤ (d : ℝ) * μ := by
      simpa only [a, μ] using shellCover_gridOf_dist_le_dim
        (by omega : 1 ≤ d) W hμ (l2a_closedBall_subset_box hx)
    have hμr : (d : ℝ) * μ ≤ p4_radius k / 100 :=
      p4_mesh_small hd (hT k hk).1
    have haz : ‖a - z k a‖ ≤ p4_radius k / 20 := by
      simpa only [z, p4_round] using p4_round_center hd hr a
    have hnear : ‖x - z k a‖ < p4_radius k / 10 := by
      calc
        ‖x - z k a‖ = ‖(x - a) + (a - z k a)‖ := by congr 1; abel
        _ ≤ ‖x - a‖ + ‖a - z k a‖ := norm_add_le _ _
        _ ≤ p4_radius k / 100 + p4_radius k / 20 := add_le_add (hxa.trans hμr) haz
        _ < p4_radius k / 10 := by linarith
    exact hbad k hk (roundLat ((1 / (20 * Real.sqrt d)) * p4_radius k) a) hnear
  have hA (a : Rd d) :
      pinLaw d s₀ {g | ∀ k ∈ T, g ∈ B a k} ≤
        ENNReal.ofReal (p ^ ((T.card : ℝ) / K)) := by
    let P := pinLaw d s₀
    let h : DistRd d → DistRd d := id
    let hP : IsProbabilityMeasure P := isProbabilityMeasure_pinLaw hd s₀
    have hh := (isWholeSpaceLGF_pinLaw hd hs₀pos).1
    have hstep (i : ℕ) : p4_radius (i + 1) ≤ (1 / 2 : ℝ) * p4_radius i :=
      (p4_radius_step i).le
    exact @hdec _ _ P hP h hh a p4_radius p4_radius_pos hstep (B a) (hlocal a) T p hp
      (fun i hi => hprob a i)
  have hfin : (pinLaw d s₀) (⋃ a ∈ A, {g | ∀ k ∈ T, g ∈ B a k}) ≤
      ENNReal.ofReal (((A.card : ℝ) * p ^ ((T.card : ℝ) / K))) := by
    calc
      (pinLaw d s₀) (⋃ a ∈ A, {g | ∀ k ∈ T, g ∈ B a k}) ≤
          ∑ a ∈ A, (pinLaw d s₀) {g | ∀ k ∈ T, g ∈ B a k} :=
            measure_biUnion_finset_le A _
      _ ≤ ∑ _a ∈ A, ENNReal.ofReal (p ^ ((T.card : ℝ) / K)) :=
        Finset.sum_le_sum (fun a ha => hA a)
      _ = ENNReal.ofReal (((A.card : ℝ) * p ^ ((T.card : ℝ) / K))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (A.card : ℝ))]
        simp
  have hcard := p4_anchor_card hd hW (by linarith : 0 ≤ V)
  calc
    pinLaw d s₀ _ ≤ pinLaw d s₀ (⋃ a ∈ A, {g | ∀ k ∈ T, g ∈ B a k}) :=
      measure_mono hbadsub
    _ ≤ ENNReal.ofReal (((A.card : ℝ) * p ^ ((T.card : ℝ) / K))) := hfin
    _ ≤ ENNReal.ofReal ((201 * (d : ℝ)) ^ d * (1 + W) ^ d *
      Real.exp (2 * d * V) * p ^ ((T.card : ℝ) / K)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hp _)
end HigherDimLQGContinuity
