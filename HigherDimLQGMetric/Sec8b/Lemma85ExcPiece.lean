import HigherDimLQGMetric.Sec8b.GeodPiece
import HigherDimLQGMetric.Sec8.ExcursionEquiv

/-! A source excursion contains a closed-collector-to-closed-collector
internal geodesic segment of the unshifted selected path. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric unitInterval
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_exc_geod_piece (η : C(unitInterval, Rd d))
    (D Dplus : ContMetric d) (V : Set (Rd d))
    (z : Rd d) (r θ : ℝ)
    (hgeo : IsGeod D (s7b_realPath η))
    (hVball : closure V ⊆ ball z (4 * r))
    (hExc : Exc η Dplus V z r θ) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      (∀ t ∈ Icc a b, s7b_realPath η t ∈ ball z (4 * r)) ∧
      ∃ R : ℝ → Rd d,
        IsGeodIn D (ball z (4 * r)) R ∧
        R 0 = s7b_realPath η a ∧
        R 1 = s7b_realPath η b ∧
        R 0 ∈ closure V ∧ R 1 ∈ closure V ∧
        ENNReal.ofReal θ ≤ Dplus.internal (ball z (4 * r)) (R 0) (R 1) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          R t = s7b_realPath η (a + t * (b - a)) := by
  rcases hExc with ⟨α, β, hαβ, hαout, hβout, hin, hvisit, hthreshold⟩
  obtain ⟨hασ₁, hσ₁σ₂, hσ₂β, hσ₁eq, hσ₂eq⟩ :=
    sec8_collector_times_eq η V z r hαout hβout hVball hvisit
  let σ₁ := sec8FirstHit η (closure V) α
  let σ₂ := sec8LastHit η (closure V) β
  change α < σ₁ at hασ₁
  change σ₁ ≤ σ₂ at hσ₁σ₂
  change σ₂ < β at hσ₂β
  have hσ₁V : η σ₁ ∈ closure V := by
    have hm := sec8FirstHit_mem η (closure V) isClosed_closure α
    rcases hm with hone | ⟨_, hV⟩
    · have hbad : (1 : unitInterval) < β := by
        rw [show σ₁ = 1 from hone] at hσ₁σ₂
        exact hσ₁σ₂.trans_lt hσ₂β
      exact False.elim ((not_lt_of_ge le_top) hbad)
    · exact hV
  have hσ₂V : η σ₂ ∈ closure V := by
    have hm := sec8LastHit_mem η (closure V) isClosed_closure β
    rcases hm with hzero | ⟨_, hV⟩
    · have hbad : α < (0 : unitInterval) := by
        rw [show σ₂ = 0 from hzero] at hσ₁σ₂
        exact hασ₁.trans_le hσ₁σ₂
      exact False.elim ((not_lt_of_ge bot_le) hbad)
    · exact hV
  let a : ℝ := σ₁
  let b : ℝ := σ₂
  have ha : 0 ≤ a := σ₁.2.1
  have hab : a ≤ b := hσ₁σ₂
  have hb : b ≤ 1 := σ₂.2.2
  have hinside : ∀ t ∈ Icc a b,
      s7b_realPath η t ∈ ball z (4 * r) := by
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 :=
      ⟨ha.trans ht.1, ht.2.trans hb⟩
    have htα : (α : ℝ) < t := by
      exact lt_of_lt_of_le (by exact_mod_cast hασ₁) ht.1
    have htβ : t < (β : ℝ) := by
      exact lt_of_le_of_lt ht.2 (by exact_mod_cast hσ₂β)
    have hproj : (⟨t, ht01⟩ : unitInterval) ∈ Ioo α β := by
      exact ⟨htα, htβ⟩
    have hco : s7b_realPath η t = η ⟨t, ht01⟩ := by
      exact s7b_realPath_coe η ⟨t, ht01⟩
    rw [hco]
    exact hin ⟨t, ht01⟩ hproj
  obtain ⟨R, hRgeo, hRform, hR0, hR1, _⟩ :=
    s7b_affine_geod_piece D (s7b_realPath η) (ball z (4 * r))
      hgeo ha hab hb hinside
  refine ⟨a, b, ha, hab, hb, hinside, R, hRgeo, hR0, hR1, ?_, ?_, ?_, hRform⟩
  · rw [hR0]
    simpa only [a, s7b_realPath_coe] using hσ₁V
  · rw [hR1]
    simpa only [b, s7b_realPath_coe] using hσ₂V
  · rw [hR0, hR1]
    simpa only [a, b, s7b_realPath_coe, ← hσ₁eq, ← hσ₂eq] using hthreshold

end HigherDimLQGMetric
