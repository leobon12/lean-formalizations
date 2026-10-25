import SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceIdx
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBCoarseIndexRange

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

def j1SourceRadius (Q : PsiParams) (K : ℕ) : ℝ :=
  2 * (2 : ℝ)⁻¹ ^ K * (K : ℝ) ^ Q.ε₀

private theorem nat_le_two_pow_sub_three (K : ℕ) (hK : 6 ≤ K) :
    K ≤ 2 ^ (K - 3) := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hsub : k + 1 - 3 = (k - 3) + 1 := by omega
      rw [hsub, pow_succ]
      have hp : 0 < 2 ^ (k - 3) := pow_pos (by omega : 0 < 2) _
      omega

theorem j1_source_radius_le_quarter (Q : PsiParams) (K : ℕ)
    (hε : Q.ε₀ ≤ 1) (hK : 6 ≤ K) :
    j1SourceRadius Q K ≤ 1 / 4 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hpow : (K : ℝ) ^ Q.ε₀ ≤ K :=
    Real.rpow_le_self_of_one_le hKr hε
  have hnat := nat_le_two_pow_sub_three K hK
  have hbound : (8 : ℝ) * K ≤ (2 : ℝ)^K := by
    have hr : (K : ℝ) ≤ (2 : ℝ) ^ (K - 3) := by exact_mod_cast hnat
    have hK3 : K - 3 + 3 = K := by omega
    have he : (2 : ℝ) ^ (K - 3) * 8 = (2 : ℝ)^K := by
      convert (pow_add (2 : ℝ) (K - 3) 3).symm using 1 <;> norm_num [hK3]
    nlinarith
  have h2pos : 0 < (2 : ℝ)^K := by positivity
  have hrpow : 0 ≤ (K : ℝ)^Q.ε₀ :=
    (Real.rpow_pos_of_pos (by linarith [hKr]) _).le
  dsimp [j1SourceRadius]
  rw [inv_pow]
  field_simp
  nlinarith

theorem j1_source_mem_sourceIdx (Q : PsiParams) (K : ℕ)
    (hε : Q.ε₀ ≤ 1) (hK : 6 ≤ K) {b : ℤ × ℤ}
    (hb : T20.dyBlock K b ⊆
      Metric.thickening (j1SourceRadius Q K) L23.sq01) :
    b ∈ j1SourceIdx K (j1SourceRadius Q K) := by
  exact (j1_mem_sourceIdx_iff (j1_source_radius_le_quarter Q K hε hK)).2 hb

end SupercriticalLQGUniqueness.B2.DG20Conc
