import LQGMetric.LFPP.Chain
import LQGMetric.Papers.DDDF.RSWPath




 





set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.PolygonCofinality

open LQGMetric LQGMetric.LFPP

 
def polygonPath (v : ℕ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => v 0
  | n + 1 => concatPath (polygonPath v n) (segPath (v n) (v (n + 1)))

theorem polygonPath_data {ξ : ℝ} {f : ℂ → ℝ} {S : Set ℂ}
    (hS : Convex ℝ S) (v : ℕ → ℂ) (n : ℕ)
    (hv : ∀ i ≤ n, v i ∈ S) :
    IsPiecewiseC1Path (polygonPath v n) (v 0) (v n) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, polygonPath v n t ∈ S) ∧
      lfppLen ξ f (polygonPath v n) =
        ∑ i ∈ Finset.range n, segCost ξ f (v i) (v (i + 1)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simpa [polygonPath] using DDDF.isPiecewiseC1Path_const (v 0)
    · intro t ht
      simpa [polygonPath] using hv 0 le_rfl
    · simp [polygonPath, DDDF.lfppLen_const]
  | succ n ih =>
    obtain ⟨hp, hm, hl⟩ := ih (fun i hi => hv i (hi.trans (Nat.le_succ n)))
    have hseg := isPiecewiseC1Path_segPath (v n) (v (n + 1))
    have hj : polygonPath v n 1 = segPath (v n) (v (n + 1)) 0 := by
      rw [hp.target]
      simp [segPath]
    refine ⟨?_, ?_, ?_⟩
    · simpa [polygonPath] using isPiecewiseC1Path_concatPath hp hseg
    · intro t ht
      change concatPath (polygonPath v n) (segPath (v n) (v (n + 1))) t ∈ S
      unfold concatPath
      split_ifs with h
      · simpa only [add_zero] using hm (2 * t) ⟨by linarith [ht.1], by linarith⟩
      · exact hS.add_smul_sub_mem (hv n (Nat.le_succ n)) (hv (n + 1) le_rfl)
          ⟨by linarith [not_le.mp h], by linarith [ht.2]⟩
    · change lfppLen ξ f (concatPath (polygonPath v n)
          (segPath (v n) (v (n + 1)))) = _
      rw [lfppLen_concatPath hj, hl, Finset.sum_range_succ]
      rfl

 

theorem exists_polygonPath_le {ξ : ℝ} {f : ℂ → ℝ} {S : Set ℂ}
    (hf : Continuous f) (hS : Convex ℝ S) {P : ℝ → ℂ} {z w : ℂ}
    (hP : IsPiecewiseC1Path P z w) (hPS : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ S)
    {η : ℝ} (hη : 0 < η) :
    ∃ (n : ℕ) (v : ℕ → ℂ), v 0 = z ∧ v n = w ∧
      (∀ i ≤ n, v i ∈ S) ∧
      IsPiecewiseC1Path (polygonPath v n) z w ∧
      (∀ t ∈ Icc (0 : ℝ) 1, polygonPath v n t ∈ S) ∧
      lfppLen ξ f (polygonPath v n) ≤ lfppLen ξ f P + ENNReal.ofReal η := by
  have hzd : z ∈ S := hP.source ▸ hPS 0 ⟨le_rfl, zero_le_one⟩
  have hwd : w ∈ S := hP.target ▸ hPS 1 ⟨zero_le_one, le_rfl⟩
  have hC : ∀ x ∈ S, ∀ ρ : ℝ, ρ > 0 → ∃ q ∈ S, ‖q - x‖ < ρ := by
    intro x hx ρ hρ
    exact ⟨x, hx, by simpa using hρ⟩
  obtain ⟨N, v, hv0, hvN, hvC, hcost⟩ :=
    exists_chain_le (ξ := ξ) (φ := f) (S := S) hf hC hP hPS hη
  have hvertices : ∀ i ≤ N + 1, v i ∈ S := by
    intro i hi
    by_cases h0 : i = 0
    · simpa [h0, hv0] using hzd
    by_cases hlast : i = N + 1
    · simpa [hlast, hvN] using hwd
    · exact hvC i (by omega) (by omega)
  obtain ⟨hpath, hmem, hlen⟩ := polygonPath_data hS v (N + 1) hvertices
  refine ⟨N + 1, v, hv0, hvN, hvertices, ?_, hmem, ?_⟩
  · simpa [hv0, hvN] using hpath
  · rw [hlen]
    exact hcost

 
theorem convex_markedRect (R : DDDF.MarkedRect) : Convex ℝ R.toSet :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

 
theorem admPath_exists_polygon_le {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) (R : DDDF.MarkedRect) {P : ℝ → ℂ}
    (hP : DDDF.AdmPath R.toSet R.side₁ R.side₂ P)
    {η : ℝ} (hη : 0 < η) :
    ∃ (n : ℕ) (v : ℕ → ℂ),
      DDDF.AdmPath R.toSet R.side₁ R.side₂ (polygonPath v n) ∧
      lfppLen ξ f (polygonPath v n) ≤ lfppLen ξ f P + ENNReal.ofReal η := by
  obtain ⟨z, hz, w, hw, hpath, hmem⟩ := hP
  obtain ⟨n, v, hv0, hvn, -, hpoly, hpolymem, hcost⟩ :=
    exists_polygonPath_le (ξ := ξ) hf (convex_markedRect R) hpath hmem hη
  exact ⟨n, v, ⟨z, hz, w, hw, hpoly, hpolymem⟩, hcost⟩


end SupercriticalLQGUniqueness.Exponent.PolygonCofinality
