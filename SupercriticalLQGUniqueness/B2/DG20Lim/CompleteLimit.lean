import SupercriticalLQGUniqueness.B2.DG20Lim.LowerSemi

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem tendsto_lsc_distance_of_euclidean_subseq
    (d : ℂ × ℂ → ℝ≥0∞) (hd : LowerSemicontinuous d)
    (z : ℕ → ℂ) (w : ℂ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hz : Tendsto (z ∘ φ) atTop (nhds w))
    (hc : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, d (z n, z m) ≤ ε) :
    Tendsto (fun n => d (z n, w)) atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall fun n => False.elim (not_lt_of_ge bot_le hb)
  · intro b hb
    obtain ⟨ε, hε, hεb⟩ := exists_between hb
    obtain ⟨N, hN⟩ := hc ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    have hclosed : IsClosed (d ⁻¹' Set.Iic ε) := hd.isClosed_preimage ε
    have hlim : Tendsto (fun m : ℕ => (z n, z (φ m))) atTop (nhds (z n, w)) :=
      by simpa only [nhds_prod_eq, Function.comp_apply] using (tendsto_const_nhds.prodMk hz)
    have hev : ∀ᶠ m : ℕ in atTop, (z n, z (φ m)) ∈ d ⁻¹' Set.Iic ε := by
      filter_upwards [(hφ.tendsto_atTop.eventually (eventually_ge_atTop N))] with m hm
      exact hN n hn (φ m) hm
    have hle : d (z n, w) ≤ ε := hclosed.mem_of_tendsto hlim hev
    exact lt_of_le_of_lt hle hεb

 

theorem tendsto_lsc_distance_of_euclidean_limit
    (d : ℂ × ℂ → ℝ≥0∞) (hd : LowerSemicontinuous d)
    (z : ℕ → ℂ) (w : ℂ)
    (hz : Tendsto z atTop (nhds w))
    (hc : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, d (z n, z m) ≤ ε) :
    Tendsto (fun n => d (z n, w)) atTop (nhds 0) := by
  simpa only [Function.comp_id] using
    tendsto_lsc_distance_of_euclidean_subseq d hd z w id strictMono_id hz hc

 

theorem exists_lsc_distance_limit_of_compact_range
    (d : ℂ × ℂ → ℝ≥0∞) (hd : LowerSemicontinuous d)
    (z : ℕ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hzK : ∀ n, z n ∈ K)
    (hc : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, d (z n, z m) ≤ ε) :
    ∃ w ∈ K, Tendsto (fun n => d (z n, w)) atTop (nhds 0) := by
  obtain ⟨w, hwK, φ, hφ, hz⟩ := hK.tendsto_subseq hzK
  exact ⟨w, hwK,
    tendsto_lsc_distance_of_euclidean_subseq d hd z w φ hφ hz hc⟩

 
theorem RData.tendsto_DfromR_of_euclidean_limit (R : RData)
    (z : ℕ → ℂ) (w : ℂ)
    (hz : Tendsto z atTop (nhds w))
    (hc : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, R.DfromR (z n) (z m) ≤ ε) :
    Tendsto (fun n => R.DfromR (z n) w) atTop (nhds 0) :=
  tendsto_lsc_distance_of_euclidean_limit
    (fun p : ℂ × ℂ => R.DfromR p.1 p.2) R.lowerSemicontinuous_DfromR z w hz hc

 
theorem RData.exists_DfromR_limit_of_compact_range (R : RData)
    (z : ℕ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hzK : ∀ n, z n ∈ K)
    (hc : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, R.DfromR (z n) (z m) ≤ ε) :
    ∃ w ∈ K, Tendsto (fun n => R.DfromR (z n) w) atTop (nhds 0) :=
  exists_lsc_distance_limit_of_compact_range
    (fun p : ℂ × ℂ => R.DfromR p.1 p.2) R.lowerSemicontinuous_DfromR
    z K hK hzK hc

end SupercriticalLQGUniqueness.B2.DG20Lim
