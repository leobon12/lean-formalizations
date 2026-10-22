import HigherDimLQGMetric.Sec8b.Lemma85MapWindow
import HigherDimLQGMetric.Sec8b.Lemma85Surgery
import HigherDimLQGMetric.Sec6.Geometry

/-! Convert the extended-real T3 shortcut into a finite real window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_real_shortcut_window (D E : ContMetric d)
    (P : ℝ → Rd d) (B : Set (Rd d))
    (hP : IsGeod D P) {t₁ t₂ ℓ c' : ℝ}
    (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ 1)
    (hinside : ∀ t ∈ Icc t₁ t₂, P t ∈ B)
    (hℓ : 0 < ℓ) (hc' : 0 ≤ c')
    (hcost : ENNReal.ofReal ℓ ≤ D.len P t₁ t₂)
    (hshort : E.internal B (P t₁) (P t₂) ≤
      ENNReal.ofReal c' * D.len P t₁ t₂) :
    ∃ L : ℝ, 0 < L ∧ t₁ < t₂ ∧
      (∀ t ∈ Icc t₁ t₂, P t ∈ B) ∧
      ENNReal.ofReal L = D.len P t₁ t₂ ∧
      ℓ ≤ L ∧ E.1 (P t₁, P t₂) ≤ c' * L := by
  have hfin : D.len P t₁ t₂ ≠ ⊤ := by
    have hle := S6a.len_le_of_isGeod hP h0 h12 h2
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  let L := (D.len P t₁ t₂).toReal
  have hLen : ENNReal.ofReal L = D.len P t₁ t₂ :=
    ENNReal.ofReal_toReal hfin
  have hℓL : ℓ ≤ L := by
    apply (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp
    rw [hLen]
    exact hcost
  have hL : 0 < L := lt_of_lt_of_le hℓ hℓL
  have ht : t₁ < t₂ := by
    rcases lt_or_eq_of_le h12 with hlt | heq
    · exact hlt
    · subst t₂
      have hzero : D.len P t₁ t₁ = 0 := by
        simp [ContMetric.len_def, LQGMetric.MetricGeometry.curveLength_self]
      rw [hzero] at hcost
      exact False.elim ((not_le_of_gt (ENNReal.ofReal_pos.mpr hℓ)) hcost)
  have hshort' : ENNReal.ofReal (E.1 (P t₁, P t₂)) ≤
      ENNReal.ofReal (c' * L) := by
    calc
      ENNReal.ofReal (E.1 (P t₁, P t₂)) ≤
          E.internal B (P t₁) (P t₂) := E.ofReal_le_internal B _ _
      _ ≤ ENNReal.ofReal c' * D.len P t₁ t₂ := hshort
      _ = ENNReal.ofReal (c' * L) := by rw [← hLen, ENNReal.ofReal_mul hc']
  have hshortReal : E.1 (P t₁, P t₂) ≤ c' * L :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc' hL.le)).mp hshort'
  exact ⟨L, hL, ht, hinside, hLen, hℓL, hshortReal⟩

end HigherDimLQGMetric
