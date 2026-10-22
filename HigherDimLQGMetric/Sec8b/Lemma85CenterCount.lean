import HigherDimLQGMetric.Sec8b.Lemma85SurgeryBridge

/-! The deterministic shortcut and occupation inequalities count centres. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical Set Metric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

variable {d : ℕ}

def S7bShortcutWindow (D : ContMetric d) (P : ℝ → Rd d)
    (z : Rd d) (r c qS : ℝ) (w : (ℝ × ℝ) × ℝ) : Prop :=
  0 ≤ w.1.1 ∧ w.1.1 < w.1.2 ∧ w.1.2 ≤ 1 ∧
    0 < w.2 ∧
    (∀ t ∈ Icc w.1.1 w.1.2, P t ∈ ball z (4 * r)) ∧
    c * qS ≤ w.2 ∧
    D.len P w.1.1 w.1.2 = ENNReal.ofReal w.2

theorem s7b_center_count_of_windows
    (hd : 1 ≤ d) {r qS Cs c' c H Dbase total : ℝ}
    (hr : 0 < r) (hqS : 0 < qS) (hCs : 0 < Cs)
    (hc' : c' < Cs) (hc : 0 < c) (hH : 0 ≤ H)
    (colour : Fin d → ℤ)
    (good Z0 : Finset (Rd d × ℕ)) (k : ℕ)
    (hk : 1 ≤ k) (hZ0k : Z0.card ≤ k)
    (hgeom : ∀ site ∈ good, ∃ index : Fin d → ℤ,
      site.1 = latPt (r / (100 * d)) index ∧
        sec8Color d index = colour)
    (D Dt : ContMetric d) (P : ℝ → Rd d)
    (hcomp : ∀ u v : Rd d, Dt.1 (u, v) ≤ Cs * D.1 (u, v))
    (hnear : Cs * Dbase - qS ≤ Dt.1 (P 0, P 1))
    (htotal : D.len P 0 1 = ENNReal.ofReal total)
    (htotal0 : 0 ≤ total)
    (hocc : total ≤ Dbase + 2 * H * k * qS)
    (hchoice : ∀ z ∈ good.image Prod.fst \ Z0.image Prod.fst,
      ∃ w : (ℝ × ℝ) × ℝ,
        S7bShortcutWindow D P z r c qS w ∧
        Dt.1 (P w.1.1, P w.1.2) ≤ max c' 0 * w.2) :
    (good.image Prod.fst).card ≤
      (1 + ⌈(2 * Cs * H + 1) / ((Cs - max c' 0) * c)⌉₊) * k := by
  classical
  let centers := good.image Prod.fst
  let outside := centers \ Z0.image Prod.fst
  let cplus := max c' 0
  have hcplus : 0 ≤ cplus := le_max_right _ _
  have hcplus_lt : cplus < Cs := max_lt hc' hCs
  have hgap : 0 < (Cs - cplus) * c := mul_pos (sub_pos.mpr hcplus_lt) hc
  let W : Rd d → (ℝ × ℝ) × ℝ := fun z =>
    if hz : z ∈ outside then Classical.choose (hchoice z hz)
    else ((0, 0), 0)
  have hW (z : Rd d) (hz : z ∈ outside) :
      S7bShortcutWindow D P z r c qS (W z) ∧
      Dt.1 (P (W z).1.1, P (W z).1.2) ≤ cplus * (W z).2 := by
    dsimp [W]
    rw [dite_eq_left hz]
    exact Classical.choose_spec (hchoice z hz)
  let win : Rd d → ℝ × ℝ := fun z => (W z).1
  let L : Rd d → ℝ := fun z => (W z).2
  have hballs : (outside : Set (Rd d)).Pairwise
      (fun z z' => Disjoint (ball z (4 * r)) (ball z' (4 * r))) := by
    have h := s7b_good_centers_balls_disjoint hd hr colour good hgeom
    intro z hz z' hz' hne
    exact h (Finset.mem_sdiff.mp hz).1
      (Finset.mem_sdiff.mp hz').1 hne
  have hwin : ∀ z ∈ outside,
      0 ≤ (win z).1 ∧ (win z).1 < (win z).2 ∧
      (win z).2 ≤ 1 ∧ 0 < L z ∧
      (∀ t ∈ Icc (win z).1 (win z).2, P t ∈ ball z (4 * r)) ∧
      D.len P (win z).1 (win z).2 = ENNReal.ofReal (L z) ∧
      Dt.1 (P (win z).1, P (win z).2) ≤ cplus * L z := by
    intro z hz
    obtain ⟨hw, hshort⟩ := hW z hz
    exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1,
      hw.2.2.2.2.1, hw.2.2.2.2.2.2, hshort⟩
  have hsurgery := s7b_surgery_from_windows D Dt P outside id win L
    r Cs cplus total hCs hcplus hcomp hballs hwin htotal htotal0
  have hoccScaled : Cs * total ≤ Cs * Dbase + 2 * Cs * H * k * qS := by
    have hm := mul_le_mul_of_nonneg_left hocc hCs.le
    nlinarith only [hm]
  have hbound := s7b_shortcut_card_bound outside L
    (C := Cs) (c' := cplus) (c := c) (H := H) (qS := qS)
    (k := k) (Dbase := Dbase) (Ebase := Dt.1 (P 0, P 1))
    (total := Cs * total) hcplus_lt hqS
    (fun z hz => (hW z hz).1.2.2.2.2.2.1)
    hnear hoccScaled hsurgery
  have hK : (2 * Cs * H + 1) / ((Cs - cplus) * c) ≤
      (⌈(2 * Cs * H + 1) / ((Cs - cplus) * c)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnum : 0 ≤ 2 * Cs * H + 1 := by positivity
  have houtside : (outside.card : ℝ) ≤
      (⌈(2 * Cs * H + 1) / ((Cs - cplus) * c)⌉₊ : ℝ) * k := by
    have hmul : 2 * Cs * H * k + 1 ≤ (2 * Cs * H + 1) * k := by
      nlinarith only [hkR]
    have hfrac : (outside.card : ℝ) ≤
        ((2 * Cs * H + 1) * k) / ((Cs - cplus) * c) := by
      apply (le_div_iff₀ hgap).mpr
      nlinarith only [hbound, hmul]
    have hKmul := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ k)
    have hqeq : ((2 * Cs * H + 1) * k) / ((Cs - cplus) * c) =
        ((2 * Cs * H + 1) / ((Cs - cplus) * c)) * k := by ring
    rw [hqeq] at hfrac
    exact hfrac.trans hKmul
  have hsplit := Finset.card_sdiff_add_card_inter centers (Z0.image Prod.fst)
  have hsplit' : outside.card + (centers ∩ Z0.image Prod.fst).card =
      centers.card := hsplit
  have hZ0centers : (Z0.image Prod.fst).card ≤ Z0.card := Finset.card_image_le
  have hinter : (centers ∩ Z0.image Prod.fst).card ≤ Z0.card :=
    (Finset.card_le_card Finset.inter_subset_right).trans hZ0centers
  have htotalCard : centers.card ≤ outside.card + k := by
    omega
  have hcast : (centers.card : ℝ) ≤
      (1 + (⌈(2 * Cs * H + 1) / ((Cs - cplus) * c)⌉₊ : ℝ)) * k := by
    have hcard : (centers.card : ℝ) ≤ (outside.card : ℝ) + k := by
      exact_mod_cast htotalCard
    nlinarith only [hcard, houtside]
  exact_mod_cast hcast

end HigherDimLQGMetric
