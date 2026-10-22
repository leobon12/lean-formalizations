import HigherDimLQGMetric.Sharp.TightCore

/-!
# Uniform lower metric bounds from tightness

Port of the off-diagonal part of `LQGMetric.GM.Tight.gm_S2_4a` to `Rd d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Filter Topology Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem cmetric_nonneg {g : C(Rd d × Rd d, ℝ)} (hg : IsContinuousMetric g)
    (p : Rd d × Rd d) : 0 ≤ g p := by
  have ht := hg.triangle p.1 p.2 p.1
  rw [hg.self_eq_zero, hg.symm p.2 p.1] at ht
  linarith

/-- A tight family of metric laws is uniformly separated on compact sets away from the diagonal. -/
theorem TightOver.lower_offDiag {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}
    (hT : TightOver P X S) {A : Set (Rd d × Rd d)} (hA : IsCompact A)
    (hAd : ∀ p ∈ A, p.1 ≠ p.2) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ ∀ r ∈ S, P {ω | ¬ ∀ p ∈ A, s < X r ω p} < ε := by
  have hanti : Antitone (fun _ : ℕ => A) := fun _ _ _ => le_rfl
  have hmono : Monotone (fun n : ℕ => Ioi ((1 : ℝ) / (n + 1))) := by
    intro m n hmn
    exact Ioi_subset_Ioi (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hmn))
  obtain ⟨n, hn⟩ := hT.mapsTo (A := fun _ => A) (fun _ => hA) hanti
    (U := fun n => Ioi ((1 : ℝ) / (n + 1))) (fun _ => isOpen_Ioi) hmono
    (by
      intro g hg x hx
      have hxA : x ∈ A := mem_iInter.1 hx 0
      have hpos : 0 < g x := lt_of_le_of_ne (cmetric_nonneg hg x)
        (fun h0 => hAd x hxA (hg.eq_of_eq_zero x.1 x.2 h0.symm))
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      exact ⟨k, hk⟩) hε
  refine ⟨1 / (n + 1), by positivity, ?_⟩
  intro r hr
  exact hn r hr

end HigherDimLQGMetric
