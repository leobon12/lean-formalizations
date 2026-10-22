import HigherDimLQGMetric.Amplify.SetDist
import HigherDimLQGMetric.Metric.Internal
import HigherDimLQGMetric.Metric.WeylBridge

/-! A collar lower bound charges every path that leaves its open core. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Topology Filter
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

variable {d : ℕ}

/-- A path from the core to the complement of an open set pays the internal
set distance to the frontier, provided the closure of the open set lies in
the region where the internal distance is measured. -/
theorem amplify_setDistIn_le_len_of_exit (D : ContMetric d)
    {V J A : Set (Rd d)} (hV : IsOpen V) (hVJ : closure V ⊆ J)
    {u : Rd d} (hu : u ∈ A) (huV : u ∈ V)
    {P : ℝ → Rd d} {T : ℝ} (hP : ContinuousOn P (Icc 0 T))
    (hP0 : P 0 = u)
    (hexit : ∃ t ∈ Icc (0 : ℝ) T, P t ∉ V) :
    setDistIn D J A (frontier V) ≤ D.len P 0 T := by
  obtain ⟨t, ht, hnot⟩ := hexit
  obtain ⟨s, hs, hsA, hbefore⟩ :=
    exists_first_hit hP (hV.isClosed_compl) ⟨t, ht, hnot⟩
  have hs0 : 0 < s := by
    rcases hs.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hP0] at hsA
      exact hsA huV
    · exact h
  have hsT : s ≤ T := hs.2
  have hfr : P s ∈ frontier V := by
    have hne : (𝓝[Ico 0 s] s).NeBot := right_nhdsWithin_Ico_neBot hs0
    have hcl : P s ∈ closure V :=
      mem_closure_of_tendsto
        (((hP.mono (Icc_subset_Icc le_rfl hsT)).continuousWithinAt
          ⟨hs.1, le_rfl⟩).tendsto.mono_left
            (nhdsWithin_mono _ Ico_subset_Icc_self))
        (eventually_nhdsWithin_of_forall fun q hq => not_not.1 (hbefore q hq))
    exact ⟨hcl, by simpa only [hV.interior_eq, mem_compl_iff] using hsA⟩
  have hmap : MapsTo P (Icc 0 s) J := by
    intro q hq
    rcases hq.2.eq_or_lt with h | h
    · exact hVJ (h ▸ hfr.1)
    · exact hVJ (subset_closure (not_not.1 (hbefore q ⟨hq.1, h⟩)))
  have hset : setDistIn D J A (frontier V) ≤ D.internal J u (P s) := by
    unfold setDistIn
    exact iInf_le_of_le u (iInf_le_of_le hu
      (iInf_le_of_le (P s) (iInf_le_of_le hfr le_rfl)))
  calc
    setDistIn D J A (frontier V) ≤ D.internal J u (P s) := hset
    _ = D.internal J (P 0) (P s) := by rw [hP0]
    _ ≤ D.len P 0 s := D.internal_le_len hs.1
      (hP.mono (Icc_subset_Icc le_rfl hsT)) hmap
    _ ≤ D.len P 0 T := curveLength_mono _ le_rfl hsT

/-- A path whose `E`-length is shorter than the `D` collar, after comparison,
cannot exit the open set. -/
theorem amplify_path_stays_of_collar (D E : ContMetric d)
    {V J A : Set (Rd d)} (hV : IsOpen V) (hVJ : closure V ⊆ J)
    {u : Rd d} (hu : u ∈ A) (huV : u ∈ V)
    {P : ℝ → Rd d} {T : ℝ} (hP : ContinuousOn P (Icc 0 T))
    (hP0 : P 0 = u) {cs : ℝ}
    (hcomp : ∀ x y, cs * D.1 (x, y) ≤ E.1 (x, y))
    (hlen : E.len P 0 T < ENNReal.ofReal cs * setDistIn D J A (frontier V)) :
    ∀ t ∈ Icc (0 : ℝ) T, P t ∈ V := by
  intro t ht
  by_contra hnot
  have hcost := amplify_setDistIn_le_len_of_exit D hV hVJ hu huV hP hP0
    ⟨t, ht, hnot⟩
  have hcmp := ContMetric.mul_len_le_of_le (D := D) (E := E) hcomp P 0 T
  have hmul : ENNReal.ofReal cs * setDistIn D J A (frontier V) ≤
      ENNReal.ofReal cs * D.len P 0 T := by gcongr
  exact (not_lt_of_ge (hmul.trans hcmp)) hlen

end HigherDimLQGMetric
