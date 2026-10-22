import HigherDimLQGMetric.Sec8b.Lemma85CenterGeometry
import HigherDimLQGMetric.Sec8b.Lemma85CompareLen

/-! Assemble disjoint local shortcuts using the pointwise comparison metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_surgery_from_windows {ι : Type*} [DecidableEq ι]
    (D Dt : ContMetric d) (P : ℝ → Rd d)
    (Z : Finset ι) (center : ι → Rd d)
    (win : ι → ℝ × ℝ) (L : ι → ℝ)
    (r Cs cplus total : ℝ) (hCs : 0 < Cs) (hcplus : 0 ≤ cplus)
    (hcomp : ∀ u v : Rd d, Dt.1 (u, v) ≤ Cs * D.1 (u, v))
    (hballs : (Z : Set ι).Pairwise
      (fun z z' => Disjoint (ball (center z) (4 * r))
        (ball (center z') (4 * r))))
    (hwin : ∀ z ∈ Z, 0 ≤ (win z).1 ∧ (win z).1 < (win z).2 ∧
      (win z).2 ≤ 1 ∧ 0 < L z ∧
      (∀ t ∈ Icc (win z).1 (win z).2,
        P t ∈ ball (center z) (4 * r)) ∧
      D.len P (win z).1 (win z).2 = ENNReal.ofReal (L z) ∧
      Dt.1 (P (win z).1, P (win z).2) ≤ cplus * L z)
    (htotal : D.len P 0 1 = ENNReal.ofReal total)
    (htotal0 : 0 ≤ total) :
    Dt.1 (P 0, P 1) + Cs * ∑ z ∈ Z, L z ≤
      Cs * total + cplus * ∑ z ∈ Z, L z := by
  let Ds := D.smul Cs hCs
  have hdisj : (Z : Set ι).PairwiseDisjoint
      (fun z => Ioo (win z).1 (win z).2) := by
    intro z hz z' hz' hne
    apply disjoint_left.mpr
    intro t ht ht'
    have hzball := (hwin z hz).2.2.2.2.1 t ⟨ht.1.le, ht.2.le⟩
    have hz'ball := (hwin z' hz').2.2.2.2.1 t ⟨ht'.1.le, ht'.2.le⟩
    exact disjoint_left.mp (hballs hz hz' hne) hzball hz'ball
  have htot : Ds.len P 0 1 = ENNReal.ofReal (Cs * total) := by
    rw [amplify_len_smul D hCs, htotal, ENNReal.ofReal_mul hCs.le]
  have hlocal : ∀ z ∈ Z,
      ENNReal.ofReal (Cs * L z) ≤ Ds.len P (win z).1 (win z).2 := by
    intro z hz
    rw [amplify_len_smul D hCs, (hwin z hz).2.2.2.2.2.1,
      ENNReal.ofReal_mul hCs.le]
  exact s7b_many_shortcuts_real Ds Dt P Z win L Cs cplus (Cs * total)
    hdisj (fun z hz => (hwin z hz).2.1)
    (fun z hz => (hwin z hz).2.2.2.1.le) hCs.le hcplus
    (mul_nonneg hCs.le htotal0) hlocal
    (fun z hz => (hwin z hz).2.2.2.2.2.2)
    (fun a b _ => s7b_compare_len D Dt Cs hCs hcomp P a b)
    (fun z hz => ⟨(hwin z hz).1, (hwin z hz).2.2.1⟩) htot

end HigherDimLQGMetric
