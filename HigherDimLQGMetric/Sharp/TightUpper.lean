import HigherDimLQGMetric.Sharp.TightCore

/-!
# Uniform upper bounds and a modulus from tightness

Ports of `LQGMetric.GM.Tight.gm_S2_4b` and `gm_S2_4b'` before field-law transfer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Filter Topology Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}

private theorem compact_near_diag {K : Set (Rd d)} (hK : IsCompact K) (b : ℝ) :
    IsCompact {p : Rd d × Rd d | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ b} :=
  (hK.prod hK).inter_right
    (isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const)

/-- Uniform Euclidean modulus on a compact set for tight metric laws. -/
theorem TightOver.modulus (hT : TightOver P X S) {K : Set (Rd d)} (hK : IsCompact K)
    {a : ℝ} (ha : 0 < a) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ ∀ r ∈ S,
      P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → X r ω (u, v) < a} < ε := by
  have hanti : Antitone (fun n : ℕ =>
      {p : Rd d × Rd d | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ 1 / (n + 1)}) := by
    intro m n hmn p hp
    exact ⟨hp.1, hp.2.trans
      (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn))⟩
  obtain ⟨n, hn⟩ := hT.mapsTo
    (A := fun n => {p : Rd d × Rd d | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ 1 / (n + 1)})
    (fun n => compact_near_diag hK _) hanti
    (U := fun _ => Iio a) (fun _ => isOpen_Iio) (fun _ _ _ => le_rfl)
    (by
      intro g hg x hx
      have h0 : ‖x.1 - x.2‖ ≤ 0 := by
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
        exact ((mem_iInter.1 hx n).2.trans hn.le).trans (by linarith)
      have hxy : x.1 = x.2 := sub_eq_zero.1 (norm_le_zero_iff.1 h0)
      refine ⟨0, ?_⟩
      show g x < a
      obtain ⟨u, v⟩ := x
      simp only at hxy
      subst v
      simpa only [hg.self_eq_zero] using ha) hε
  refine ⟨1 / (n + 1), by positivity, fun r hr => ?_⟩
  simpa [MapsTo, Set.mem_prod, Set.mem_ofPred_eq] using hn r hr

/-- A tight family has uniformly bounded values on any fixed compact set of pairs. -/
theorem TightOver.upper_compact (hT : TightOver P X S) {K : Set (Rd d)}
    (hK : IsCompact K) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ∈ S,
      P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, X r ω (u, v) < a} < ε := by
  obtain ⟨n, hn⟩ := hT.mapsTo
    (A := fun _ => K ×ˢ K) (fun _ => hK.prod hK) (fun _ _ _ => le_rfl)
    (U := fun n => Iio ((n : ℝ) + 1)) (fun _ => isOpen_Iio)
    (fun m n hmn => Iio_subset_Iio (by exact_mod_cast Nat.succ_le_succ hmn))
    (by
      intro g _ x _
      obtain ⟨n, hn⟩ := exists_nat_gt (g x)
      exact ⟨n, show g x < (n : ℝ) + 1 by linarith⟩) hε
  refine ⟨n + 1, by positivity, fun r hr => ?_⟩
  simpa [MapsTo, Set.mem_prod, Set.mem_ofPred_eq] using hn r hr

end HigherDimLQGMetric
