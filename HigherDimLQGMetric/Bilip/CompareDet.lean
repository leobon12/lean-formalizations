import HigherDimLQGMetric.Bilip.GridCount
import HigherDimLQGMetric.Sharp.CompareDet

/-! The path-cover comparison with the observable larger-shell diameter. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGMetric
open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal
variable {d : ℕ}

theorem bilip_compare_of_path_cover (hd : 2 ≤ d) (D₁ D₂ : ContMetric d)
    {C ρ ε η : ℝ} (hC : 0 < C) (hρ : 0 < ρ) (hη : 0 ≤ η)
    {u v : Rd d} (P : ℝ → Rd d) (hP : ContinuousOn P (Icc 0 1))
    (hP0 : P 0 = u) (hP1 : P 1 = v)
    (hLen : D₁.len P 0 1 ≤ ENNReal.ofReal (D₁.1 (u, v) + η))
    (hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∃ w r,
      ρ ≤ r ∧ r ≤ ε ∧ ‖P s - w‖ < r / 2 ∧
      internalDiamRd D₂ (sphere w r) (shellOpen w (r / 4) (4 * r)) ≤ ENNReal.ofReal C * acrossDist D₁ w (r / 2) r) :
    ∃ x y, ‖x - u‖ ≤ 2 * ε ∧ ‖y - v‖ ≤ 2 * ε ∧
      D₂.1 (x, y) ≤ C * (D₁.1 (u, v) + η) := by
  have hLfin : D₁.len P 0 1 ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := D₁.1 (u, v) + η)) hLen
  let ℓ : ℝ → ℝ := fun s => (D₁.len P 0 s).toReal
  have hfin : ∀ a b, 0 ≤ a → b ≤ 1 → D₁.len P a b ≠ ∞ := by
    intro a b ha hb
    exact ne_top_of_le_ne_top hLfin (D₁.len_mono P ha hb)
  have hsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
      (D₁.len P a b).toReal = ℓ b - ℓ a := by
    intro a b ha hab hb
    have hadd := D₁.len_add P ha hab
    have he : ℓ b = (D₁.len P 0 a).toReal + (D₁.len P a b).toReal := by
      simp only [ℓ]
      rw [← hadd, ENNReal.toReal_add (hfin 0 a le_rfl (hab.trans hb))
        (hfin a b ha hb)]
    linarith
  have hℓ : MonotoneOn ℓ (Icc 0 1) := by
    intro a ha b hb hab
    have h := hsub a b ha.1 hab hb.2
    linarith [ENNReal.toReal_nonneg (a := D₁.len P a b)]
  obtain ⟨x, y, hx, hy, hxy⟩ := sphere_chain hd
    (fun x y => ENNReal.ofReal (D₂.1 (x, y)))
    (fun x => by rw [D₂.apply_self]; norm_num)
    (fun x y z => by
      calc
        ENNReal.ofReal (D₂.1 (x, z)) ≤
            ENNReal.ofReal (D₂.1 (x, y) + D₂.1 (y, z)) :=
          ENNReal.ofReal_le_ofReal (D₂.apply_triangle x y z)
        _ = ENNReal.ofReal (D₂.1 (x, y)) + ENNReal.ofReal (D₂.1 (y, z)) :=
          ENNReal.ofReal_add (D₂.nonneg x y) (D₂.nonneg y z))
    hρ P hP ℓ hℓ
    (fun w r => internalDiamRd D₂ (sphere w r) (shellOpen w (r / 4) (4 * r)) ≤ ENNReal.ofReal C * acrossDist D₁ w (r / 2) r)
    hcov (ENNReal.ofReal C) (by
      intro w r hgood a ha b hb hab ha' hb' q hq q' hq'
      have hcont : ContinuousOn (fun t => ‖P t - w‖) (Icc a b) :=
        ((hP.mono (Icc_subset_Icc ha.1 hb.2)).sub continuousOn_const).norm
      have hr : 0 < r := by
        linarith [norm_nonneg (P a - w)]
      obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hab hcont
        (show r / 2 ∈ Icc ‖P a - w‖ ‖P b - w‖ from ⟨ha'.le, by rw [hb']; linarith⟩)
      have hsSphere : P s ∈ sphere w (r / 2) := by
        rw [mem_sphere, dist_eq_norm]
        exact hfs
      have hbSphere : P b ∈ sphere w r := by
        rw [mem_sphere, dist_eq_norm]
        exact hb'
      have hdiam : ENNReal.ofReal (D₂.1 (q, q')) ≤ internalDiamRd D₂ (sphere w r) (shellOpen w (r / 4) (4 * r)) := by
        exact (D₂.ofReal_le_internal _ q q').trans
          (le_iSup₂_of_le q hq (le_iSup₂_of_le q' hq' le_rfl))
      have hacross : acrossDist D₁ w (r / 2) r ≤
          ENNReal.ofReal (D₁.1 (P s, P b)) := by
        unfold acrossDist
        exact iInf₂_le_of_le (P s) hsSphere (iInf₂_le (P b) hbSphere)
      have hlenSb : ENNReal.ofReal (D₁.1 (P s, P b)) ≤ D₁.len P s b :=
        D₁.ofReal_le_len P hs.2
      have hlenAB : D₁.len P s b ≤ D₁.len P a b := D₁.len_mono P hs.1 le_rfl
      have hto : D₁.len P a b = ENNReal.ofReal (ℓ b - ℓ a) := by
        rw [← hsub a b ha.1 hab hb.2]
        exact (ENNReal.ofReal_toReal (hfin a b ha.1 hb.2)).symm
      calc
        ENNReal.ofReal (D₂.1 (q, q')) ≤ internalDiamRd D₂ (sphere w r) (shellOpen w (r / 4) (4 * r)) := hdiam
        _ ≤ ENNReal.ofReal C * acrossDist D₁ w (r / 2) r := hgood
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal (D₁.1 (P s, P b)) := by gcongr
        _ ≤ ENNReal.ofReal C * D₁.len P a b :=
          mul_le_mul_of_nonneg_left (hlenSb.trans hlenAB) bot_le
        _ = ENNReal.ofReal C * ENNReal.ofReal (ℓ b - ℓ a) := by rw [hto])
  refine ⟨x, y, hP0 ▸ hx, hP1 ▸ hy, ?_⟩
  have h01 : ℓ 1 - ℓ 0 = (D₁.len P 0 1).toReal := by
    simp only [ℓ, D₁.len_of_ge P le_rfl, ENNReal.toReal_zero, sub_zero]
  rw [h01] at hxy
  have hLle : (D₁.len P 0 1).toReal ≤ D₁.1 (u, v) + η :=
    ENNReal.toReal_le_of_le_ofReal (by linarith [D₁.nonneg u v]) hLen
  have hrhs : 0 ≤ C * (D₁.1 (u, v) + η) :=
    mul_nonneg hC.le (add_nonneg (D₁.nonneg u v) hη)
  have h2 : ENNReal.ofReal (D₂.1 (x, y)) ≤
      ENNReal.ofReal (C * (D₁.1 (u, v) + η)) := by
    calc
      ENNReal.ofReal (D₂.1 (x, y)) ≤
          ENNReal.ofReal C * ENNReal.ofReal (D₁.len P 0 1).toReal := hxy
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (D₁.1 (u, v) + η) := by gcongr
      _ = ENNReal.ofReal (C * (D₁.1 (u, v) + η)) :=
        (ENNReal.ofReal_mul hC.le).symm
  exact (ENNReal.ofReal_le_ofReal_iff hrhs).1 h2

end HigherDimLQGMetric
