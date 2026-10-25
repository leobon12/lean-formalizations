import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.GeomInputs




 










set_option autoImplicit false

noncomputable section

open Set Metric Filter Real
open scoped Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

 
def arcCount (Asp : ℝ) : ℕ := ⌈16 * π / Asp⌉₊

 
def blockCount (K : ℕ) (Asp : ℝ) : ℕ := ⌊(K : ℝ) * Asp / (16 * π)⌋₊

 
def blockStart (K m i : ℕ) : ℕ := ⌈(i : ℝ) * K / m⌉₊

 
def blockIdx (T : Objects.CorrectedEvent.TubeData) (m i N : ℕ) : Finset (Fin T.K) :=
  (Finset.range N).image (fun t => ⟨(blockStart T.K m i + t) % T.K, Nat.mod_lt _ T.Kpos⟩)

 
def blockSites (T : Objects.CorrectedEvent.TubeData) (m i N : ℕ) : Finset ℂ :=
  (blockIdx T m i N).image (Objects.CorrectedEvent.site T)

theorem site_eq_exp (T : Objects.CorrectedEvent.TubeData) (n : ℕ) :
    Objects.CorrectedEvent.site T ⟨n % T.K, Nat.mod_lt _ T.Kpos⟩ =
      ((2 * T.r : ℝ) : ℂ) * Complex.exp (((2 * π * n / T.K : ℝ) : ℂ) * Complex.I) := by
  have hK : (0 : ℝ) < T.K := by exact_mod_cast T.Kpos
  obtain ⟨d, hd⟩ : ∃ d : ℕ, n = n % T.K + T.K * d := ⟨n / T.K, (Nat.mod_add_div n T.K).symm⟩
  have hdR : (n : ℝ) = ((n % T.K : ℕ) : ℝ) + (T.K : ℝ) * (d : ℝ) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) hd
    simpa only [Nat.cast_add, Nat.cast_mul] using h
  have hθ : (2 * π * n / T.K : ℝ) = 2 * π * ((n % T.K : ℕ) : ℝ) / T.K + 2 * π * d := by
    rw [hdR]
    field_simp
  unfold Objects.CorrectedEvent.site Objects.CorrectedEvent.polar
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(d : ℤ), ?_⟩
  rw [hθ]
  push_cast
  ring

theorem arcCount_pos {Asp : ℝ} (hA : 0 < Asp) : 0 < arcCount Asp := by
  unfold arcCount
  exact Nat.ceil_pos.2 (by positivity)

 
theorem arc_contains_block (T : Objects.CorrectedEvent.TubeData) (Asp : ℝ) (hA : 0 < Asp) (hr : 0 < T.r) {N : ℕ}
    (hN : N ≤ blockCount T.K Asp) (θ0 θ1 : ℝ)
    (hθ : Asp * T.r / 2 ≤ 2 * T.r * (θ1 - θ0)) :
    ∃ i < arcCount Asp, ∀ k ∈ blockIdx T (arcCount Asp) i N, Objects.CorrectedEvent.onArc T.r θ0 θ1 (Objects.CorrectedEvent.site T k) := by
  set m := arcCount Asp with hm
  have hm0 : 0 < m := arcCount_pos hA
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hK : (0 : ℝ) < T.K := by exact_mod_cast T.Kpos
  have hπ := Real.pi_pos
  have hmge : 16 * π / Asp ≤ m := Nat.le_ceil _
  set δ : ℝ := 2 * π / m with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ Asp / 8 := by
    rw [hδ, div_le_iff₀ hmR]
    have h1 := (div_le_iff₀ hA).1 hmge
    nlinarith
  have hNle : (N : ℝ) ≤ T.K * Asp / (16 * π) :=
    (Nat.cast_le.2 hN).trans (Nat.floor_le (by positivity))
  have hlen : Asp / 4 ≤ θ1 - θ0 := by nlinarith
  set n : ℤ := ⌈θ0 / δ⌉ with hn
  have hn1 : θ0 ≤ n * δ := by
    have := Int.le_ceil (θ0 / δ)
    rwa [div_le_iff₀ hδpos] at this
  have hn2 : (n : ℝ) * δ < θ0 + δ := by
    have := Int.ceil_lt_add_one (θ0 / δ)
    rw [← hn] at this
    have h2 := mul_lt_mul_of_pos_right this hδpos
    rw [add_mul, one_mul, div_mul_cancel₀ _ hδpos.ne'] at h2
    exact h2
  set i : ℕ := (n % (m : ℤ)).toNat with hi
  set q : ℤ := n / (m : ℤ) with hq
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm0
  have hmod0 : 0 ≤ n % (m : ℤ) := Int.emod_nonneg _ hmZ.ne'
  have hmodlt : n % (m : ℤ) < m := Int.emod_lt_of_pos _ hmZ
  have hi_eq : (i : ℤ) = n % (m : ℤ) := Int.toNat_of_nonneg hmod0
  have hilt : i < m := by omega
  have hdecomp : (n : ℝ) = (i : ℝ) + (m : ℝ) * q := by
    have h := Int.mul_ediv_add_emod n (m : ℤ)
    have h' : (n : ℤ) = (i : ℤ) + (m : ℤ) * q := by rw [hi_eq, hq]; linarith
    exact_mod_cast h'
  refine ⟨i, hilt, ?_⟩
  intro k hk
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hk
  have htN : t < N := Finset.mem_range.1 ht
  set ki := blockStart T.K m i with hki
  have hki1 : (i : ℝ) * T.K / m ≤ ki := Nat.le_ceil _
  have hki2 : (ki : ℝ) < (i : ℝ) * T.K / m + 1 := Nat.ceil_lt_add_one (by positivity)
  set θ : ℝ := 2 * π * ((ki + t : ℕ) : ℝ) / T.K + 2 * π * q with hθdef
  refine ⟨θ, ⟨?_, ?_⟩, ?_⟩
  · 
    have h1 : 2 * π * (i : ℝ) / m ≤ 2 * π * ((ki + t : ℕ) : ℝ) / T.K := by
      have e : 2 * π * (i : ℝ) / m = 2 * π * ((i : ℝ) * T.K / m) / T.K := by
        field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ hK.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      push_cast
      linarith [show (0:ℝ) ≤ t from Nat.cast_nonneg t]
    have h2 : (n : ℝ) * δ = 2 * π * (i : ℝ) / m + 2 * π * q := by
      rw [hdecomp, hδ]; field_simp
    linarith
  · 
    have h1 : 2 * π * ((ki + t : ℕ) : ℝ) / T.K < 2 * π * (i : ℝ) / m + 2 * π * N / T.K := by
      push_cast
      have htN' : (t : ℝ) + 1 ≤ N := by exact_mod_cast htN
      have e1 : 2 * π * ((ki : ℝ) + t) / T.K = 2 * π * ki / T.K + 2 * π * t / T.K := by ring
      have e2 : 2 * π * (ki : ℝ) / T.K < 2 * π * (i : ℝ) / m + 2 * π / T.K := by
        have := mul_lt_mul_of_pos_left hki2 (show (0:ℝ) < 2 * π / T.K by positivity)
        have e3 : 2 * π / T.K * ((i : ℝ) * T.K / m + 1) = 2 * π * i / m + 2 * π / T.K := by
          field_simp
        have e4 : 2 * π / T.K * (ki : ℝ) = 2 * π * ki / T.K := by ring
        linarith
      have e5 : 2 * π * (t : ℝ) / T.K + 2 * π / T.K ≤ 2 * π * N / T.K := by
        rw [← add_div, div_le_div_iff_of_pos_right hK]
        nlinarith
      linarith
    have h2 : (n : ℝ) * δ = 2 * π * (i : ℝ) / m + 2 * π * q := by
      rw [hdecomp, hδ]; field_simp
    have h3 : 2 * π * (N : ℝ) / T.K ≤ Asp / 8 := by
      rw [div_le_iff₀ hK]
      have := mul_le_mul_of_nonneg_left hNle (show (0:ℝ) ≤ 2 * π by positivity)
      have e : 2 * π * (T.K * Asp / (16 * π)) = Asp / 8 * T.K := by field_simp; ring
      linarith
    linarith
  · 
    rw [site_eq_exp]
    congr 1
    · push_cast; ring
    · rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-q, ?_⟩
      rw [hθdef]
      push_cast
      ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
