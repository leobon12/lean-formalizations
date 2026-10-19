import HigherDimLFPP.Lower.Lemma53Class

/-!
# Lemma 5.3 (source §5.2): invariance of `C_δ` and the gain, for every `d ≥ 2`

Packet P-L3, target T3 (ruling H6; audit HA4, "Details for later use" D6; findings HA4-3,
HA4-4, HA4-5, HA4-10, HA4-11).

**Main result** `lemma53Holds_holds : Lemma53Holds d κ` (P-L4's interface, `Iteration.lean`) for
every `d ≥ 2` and every admissible kernel, with no hypotheses: for `n ≥ N₀`, with the Lemma 2.2
family `F_{n,d}` (P-V2's `lemma22b_fin`), `g = g_n`, `e = e_{n,d}` and the constants of HA4 D6,

* `M₀ = √e + 1`, `c = √2 c₁` (P-L1's Lemma 5.1), `q₀ = 2/K`,
  `M = (M₀ + q₀ + 1)/(1 - q₀)` (5.16), `C' = √(C_d L) √(2 log 2(J+1))` ((K5)),
  `B = (E₀ + q₀ c M + 3C' + 1)/(1 - q₀)` (5.22);

for every `θ > 0` and all small `δ`, the equal-edge polygons of Lemma 5.1 satisfy (i)
`T_i^j(V_δ) ⊆ V_δ ⊆ U`, and for every Riemann parameter `N ≥ δ^{-2}` and every finitely supported
`μ ∈ C_δ`: (ii) `T μ ∈ C_δ`, (iii) `E ∫ e^{ζH} dν_{I,μ} ≤ 1 - δ²(4e - 5) + θδ²`.

Ingredients: the coupling (5.17) of `ν_{j,μ}` with `ν_j` (`coupledWithin_repl_polyM`, from the
quantile coupling) and of `ν_j^N` with `ν_j` (`coupledWithin_riemann_polyM`); (3.14)
(`bandLemma34c`, `norm_repl_sub_riem_le`); (3.16) (`bandLemma34d_var`, `norm_replM_le`); the
gain `lp_tiltMass_le` with Lemma 5.2 (`lemma52`, `lemma52_riemann`); the normalization
`tmap_props` with P-L1's `inCDelta_of_hCDF_close`; and the containment
`edgeSim_mapsTo_Vdelta`, `Vdelta_subset_cube`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

open LQGDimension (gaussianExpectedMax)

variable {d : ℕ} {κ : Rd d → ℝ}

namespace LowerData

variable (D : LowerData d)

/-- `‖v‖ ≤ √X` when `‖v‖² = Var ≤ X`. -/
theorem norm_bandVecM_le_sqrt {S : Set ℝ} {μ ν : Measure (Rd d)} {X : ℝ}
    (h : scaleCov κ S μ ν μ ν ≤ X) : ‖bandVecM κ S μ ν‖ ≤ Real.sqrt X := by
  rw [← Real.sqrt_sq (norm_nonneg (bandVecM κ S μ ν))]
  refine Real.sqrt_le_sqrt ?_
  rwa [← scaleCov_self]

/-- **(3.14) for the replacement step** (HA4 D6 Step 4): with the couplings of `ν_{j,μ}` and of
`ν_j^N` with `ν_j`, `‖⟨H, ν_{j,μ} - ν_j^N⟩‖ ≤ √(C u²/(ρq)) + √(C (q/N)²/(ρq))`,
`u = q(r + m)`. -/
theorem norm_repl_sub_riem_le (hd : 0 < d) {Cc : ℝ}
    (hCc : ∀ (a u : ℝ) (S : Set ℝ), 0 < a → 0 ≤ u → u ≤ a → MeasurableSet S → S ⊆ Ioi a →
      ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      GrowthBound ν 4 1 → CoupledWithin μ ν u →
        IsPairable κ S μ ν ∧ scaleCov κ S μ ν μ ν ≤ Cc * u ^ 2 / a)
    {δ : ℝ} (hρq : 0 < D.ρ δ * D.q δ) {N : ℕ} (hN : 0 < N) {M₀ c : ℝ}
    (hE : ∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ M₀ c (D.vert δ j))
    (hgν : ∀ j, GrowthBound (D.ν δ j) 4 1) (hq0 : 0 < D.q δ)
    {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hμ : IsFinProb Sμ w) {r m : ℝ} (hW : HorizW Sμ w r)
    (htr : ∀ z ∈ Sμ, w z ≠ 0 → ‖transv z‖ ≤ m) (hu0 : 0 ≤ D.q δ * (r + m))
    (hu : D.q δ * (r + m) ≤ D.ρ δ * D.q δ) (hNu : D.q δ / N ≤ D.ρ δ * D.q δ)
    (j : Fin (D.J + 1)) :
    ‖bandVecM κ (D.band δ) ((D.lp δ N).replM Sμ w (fun _ => 1) j) (D.νR δ N j)‖ ≤
      Real.sqrt (Cc * (D.q δ * (r + m)) ^ 2 / (D.ρ δ * D.q δ)) +
        Real.sqrt (Cc * (D.q δ / N) ^ 2 / (D.ρ δ * D.q δ)) := by
  have hK := D.K_pos
  have hpA := (D.lp δ N).isProbabilityMeasure_replM_one hμ hK j
  have hpν : IsProbabilityMeasure (D.ν δ j) := isProbabilityMeasure_polyM hK _
  have hpR : IsProbabilityMeasure (D.νR δ N j) := D.isProbabilityMeasure_νR δ hN j
  have hcplA : CoupledWithin ((D.lp δ N).replM Sμ w (fun _ => 1) j) (D.ν δ j)
      (D.q δ * (r + m)) := by
    rw [(D.lp δ N).replM_one]
    exact coupledWithin_repl_polyM hd hq0 (hE j).edge_len hμ hW htr
  have hcplR : CoupledWithin (D.νR δ N j) (D.ν δ j) (D.q δ / N) :=
    coupledWithin_riemann_polyM hd hN hq0 (hE j).edge_len
  obtain ⟨hpA', hvA⟩ := hCc (D.ρ δ * D.q δ) (D.q δ * (r + m)) (D.band δ) hρq hu0 hu
    measurableSet_Ioo Ioo_subset_Ioi_self _ (D.ν δ j) (hgν j) hcplA
  obtain ⟨hpR', hvR⟩ := hCc (D.ρ δ * D.q δ) (D.q δ / N) (D.band δ) hρq (by positivity) hNu
    measurableSet_Ioo Ioo_subset_Ioi_self _ (D.ν δ j) (hgν j) hcplR
  rw [bandVecM_trans hpA' (isPairable_comm.1 hpR')]
  refine (norm_add_le _ _).trans (add_le_add (norm_bandVecM_le_sqrt hvA) ?_)
  rw [bandVecM_swap, norm_neg]
  exact norm_bandVecM_le_sqrt hvR

/-- **(3.16) for the replacement step** (HA4 (K2), (K5)): `‖⟨H, h ν_{j,μ}⟩‖ ≤ √(C ρ)` for every
weight `0 ≤ h ≤ 1` (in particular the prefixes `{z₁ ≤ x}`). -/
theorem norm_replM_le (hd : 0 < d) {Cd : ℝ} (hCd0 : 0 ≤ Cd)
    (hCd : ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∀ (ν ν' : Measure (Rd d)) [IsFiniteMeasure ν] [IsFiniteMeasure ν'],
        GrowthBound ν' 4 1 → CoupledWithin ν ν' a →
        ∀ (η : Measure (Rd d)) [IsFiniteMeasure η], η ≤ ν →
          IsPairable κ (Ioo a b) η 0 ∧ scaleCov κ (Ioo a b) η 0 η 0 ≤ Cd * b * η.real univ)
    {δ : ℝ} (hρq : 0 < D.ρ δ * D.q δ) (hq1 : D.q δ ≤ 1) {N : ℕ} {M₀ c : ℝ}
    (hE : ∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ M₀ c (D.vert δ j))
    (hgν : ∀ j, GrowthBound (D.ν δ j) 4 1) (hq0 : 0 < D.q δ)
    {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hμ : IsFinProb Sμ w) {r m : ℝ} (hW : HorizW Sμ w r)
    (htr : ∀ z ∈ Sμ, w z ≠ 0 → ‖transv z‖ ≤ m) (hu : D.q δ * (r + m) ≤ D.ρ δ * D.q δ)
    {h : Rd d → ℝ} (hh : ∀ p, 0 ≤ h p) (hh1 : ∀ p, h p ≤ 1) (j : Fin (D.J + 1)) :
    ‖bandVecM κ (Ioo ((D.lp δ N).ρ * (D.lp δ N).q) (D.lp δ N).ρ)
        ((D.lp δ N).replM Sμ w h j) 0‖ ≤ Real.sqrt (Cd * D.ρ δ) := by
  have hK := D.K_pos
  have hρ : 0 < D.ρ δ := pos_of_mul_pos_left hρq hq0.le
  have hcplA : CoupledWithin ((D.lp δ N).replM Sμ w (fun _ => 1) j) (D.ν δ j)
      (D.ρ δ * D.q δ) := by
    rw [(D.lp δ N).replM_one]
    exact coupledWithin_mono (coupledWithin_repl_polyM hd hq0 (hE j).edge_len hμ hW htr) hu
  obtain ⟨-, hv⟩ := hCd (D.ρ δ * D.q δ) (D.ρ δ) hρq (mul_le_of_le_one_right hρ.le hq1)
    ((D.lp δ N).replM Sμ w (fun _ => 1) j) (D.ν δ j) (hgν j) hcplA
    ((D.lp δ N).replM Sμ w h j) ((D.lp δ N).replM_le hμ.1 hh1 j)
  refine norm_bandVecM_le_sqrt (hv.trans ?_)
  have hmass := (D.lp δ N).replM_real_univ_le hμ hK hh hh1 j
  calc Cd * D.ρ δ * ((D.lp δ N).replM Sμ w h j).real univ ≤ Cd * D.ρ δ * 1 :=
        mul_le_mul_of_nonneg_left hmass (mul_nonneg hCd0 hρ.le)
    _ = Cd * D.ρ δ := mul_one _

end LowerData

/-- The error of (5.23) (HA4 D6 Step 4), real arithmetic: with `u = q(Bδ² + Mδ)`, `ρ = δL`,
`q ≤ 2/K`, `Bδ ≤ 1`, `δ ≤ 1` and `1/N ≤ δ²`,
`√(C u²/(ρq)) + √(C (q/N)²/(ρq)) ≤ √δ (M + 2) √(C (2/K)/L)`. -/
theorem gain_arith {Cc q K L δ B M N : ℝ} (hCc : 0 ≤ Cc) (hq : 0 < q) (hK : 0 < K)
    (hq2 : q ≤ 2 / K) (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hBδ : B * δ ≤ 1) (hN : 0 < N) (hNδ : 1 / N ≤ δ ^ 2) :
    Real.sqrt (Cc * (q * (B * δ ^ 2 + M * δ)) ^ 2 / (δ * L * q)) +
        Real.sqrt (Cc * (q / N) ^ 2 / (δ * L * q)) ≤
      Real.sqrt δ * ((M + 2) * Real.sqrt (Cc * (2 / K) / L)) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Cc * (2 / K) / L := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hX1 : Cc * (q * (B * δ ^ 2 + M * δ)) ^ 2 / (δ * L * q) ≤ (M + 1) ^ 2 * δ * Y := by
    have e : Cc * (q * (B * δ ^ 2 + M * δ)) ^ 2 / (δ * L * q) =
        Cc * q * δ * (B * δ + M) ^ 2 / L := by
      field_simp
    rw [e, hY]
    have hBM : (B * δ + M) ^ 2 ≤ (M + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc Cc * q * δ * (B * δ + M) ^ 2 / L ≤ Cc * (2 / K) * δ * (M + 1) ^ 2 / L := by gcongr
      _ = (M + 1) ^ 2 * δ * (Cc * (2 / K) / L) := by ring
  have hX2 : Cc * (q / N) ^ 2 / (δ * L * q) ≤ δ * Y := by
    have e : Cc * (q / N) ^ 2 / (δ * L * q) = Cc * q * (1 / N) ^ 2 / (δ * L) := by
      field_simp
    rw [e, hY]
    have h4 : (1 / N) ^ 2 ≤ δ ^ 2 := by
      calc (1 / N) ^ 2 ≤ (δ ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hNδ 2
        _ ≤ δ ^ 2 := by
            have : δ ^ 2 ≤ 1 := by nlinarith
            nlinarith [sq_nonneg δ]
    calc Cc * q * (1 / N) ^ 2 / (δ * L) ≤ Cc * (2 / K) * δ ^ 2 / (δ * L) := by gcongr
      _ = δ * (Cc * (2 / K) / L) := by field_simp
  have ht1 : Real.sqrt (Cc * (q * (B * δ ^ 2 + M * δ)) ^ 2 / (δ * L * q)) ≤
      (M + 1) * Real.sqrt δ * Real.sqrt Y := by
    calc Real.sqrt (Cc * (q * (B * δ ^ 2 + M * δ)) ^ 2 / (δ * L * q))
        ≤ Real.sqrt ((M + 1) ^ 2 * δ * Y) := Real.sqrt_le_sqrt hX1
      _ = (M + 1) * Real.sqrt δ * Real.sqrt Y := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by linarith)]
  have ht2 : Real.sqrt (Cc * (q / N) ^ 2 / (δ * L * q)) ≤ Real.sqrt δ * Real.sqrt Y :=
    (Real.sqrt_le_sqrt hX2).trans_eq (Real.sqrt_mul hδ.le _)
  rw [← hY]
  have hs1 := Real.sqrt_nonneg δ
  have hs2 := Real.sqrt_nonneg Y
  nlinarith [ht1, ht2, mul_nonneg hs1 hs2]

/-- `ζ √(C ρ) = δ² √(C L)` for `ζ = δ^{3/2}`, `ρ = δL` (the constant `C'` of (5.20)). -/
theorem zeta_sigma_arith {Cd L δ S : ℝ} (hδ : 0 ≤ δ) :
    δ ^ (3 / 2 : ℝ) * (Real.sqrt (Cd * (δ * L)) * S) = Real.sqrt (Cd * L) * S * δ ^ 2 := by
  have e2 : Real.sqrt (Cd * (δ * L)) = Real.sqrt δ * Real.sqrt (Cd * L) := by
    rw [← Real.sqrt_mul hδ]
    congr 1
    ring
  rw [e2, ← LowerData.rpow_three_halves_mul_sqrt hδ]
  ring

/-- `1/N ≤ δ²` for `N ≥ δ^{-2}`. -/
theorem one_div_le_sq_of_zpow_le {δ N : ℝ} (hδ : 0 < δ) (hNδ : δ ^ (-2 : ℤ) ≤ N) :
    1 / N ≤ δ ^ 2 := by
  have hpos : 0 < δ ^ (-2 : ℤ) := zpow_pos hδ _
  have h := one_div_le_one_div_of_le hpos hNδ
  have e : 1 / δ ^ (-2 : ℤ) = δ ^ 2 := by
    rw [zpow_neg, one_div, inv_inv]
    norm_cast
  rwa [e] at h

namespace LowerData

variable (D : LowerData d)

/-- **Lemma 5.3 (iii) at a fixed `δ`, `N` and `μ`** (HA4 D6 Step 4, (5.15)), under explicit
numerical conditions on the constants: `E ∫ e^{ζH} dν_{I,μ} ≤ 1 - δ²(4e - 5) + θδ²`. -/
theorem lemma53_iii_at (hd : 0 < d) (hκ : IsLFPPKernel κ) {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ (a u : ℝ) (S : Set ℝ), 0 < a → 0 ≤ u → u ≤ a → MeasurableSet S → S ⊆ Ioi a →
      ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      GrowthBound ν 4 1 → CoupledWithin μ ν u →
        IsPairable κ S μ ν ∧ scaleCov κ S μ ν μ ν ≤ Cc * u ^ 2 / a)
    (he : 0 ≤ D.e) (hn : 1 ≤ D.n) (hg : 1 ≤ D.g)
    {δ M B M₀ c θ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hE : ∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ M₀ c (D.vert δ j))
    (hcδ : c * δ ≤ 1 / 2) (hδE : δ ^ 2 * D.E₀ ≤ 1) (hBδ : B * δ ≤ 1) (hML : M + 1 ≤ D.L)
    (hgain : (M + 2) * Real.sqrt (Cc * (2 / D.K) / D.L) *
      Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) ≤ 1)
    (hεθ : ((D.J : ℝ) + 1) * (Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1) ≤ θ * δ ^ 2 / 2)
    {N : ℕ} (hN : 0 < N) (hNδ : δ ^ (-2 : ℤ) ≤ (N : ℝ))
    (hwR : 4 * D.e - 4 - θ / 2 ≤ D.wR κ δ N)
    {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hμC : InCDelta δ M B Sμ w) :
    ∫ Y, (D.lp δ N).tiltMass Sμ w Y ∂gLawD κ ((D.lp δ N).stepTris Sμ) ≤
      1 - δ ^ 2 * (4 * D.e - 5) + θ * δ ^ 2 := by
  obtain ⟨hμ, htr, hW⟩ := hμC
  have hK := D.K_pos
  have hL := D.L_pos
  have hq0 : 0 < D.q δ := D.q_pos he δ
  have hqK : 1 / (D.K : ℝ) ≤ D.q δ := D.one_div_K_le_q he δ
  have hq2 : D.q δ ≤ 2 / D.K := D.q_le_two_div_K hδE
  have hρ : 0 < D.ρ δ := mul_pos hδ hL
  have hρq : 0 < D.ρ δ * D.q δ := mul_pos hρ hq0
  have hG : (D.lp δ N).Good := D.lp_good hd he hn hg hδ hδE hN hE
  have hgν : ∀ j, GrowthBound (D.ν δ j) 4 1 := fun j =>
    growthBound_polyM hd hK hqK fun i hi => half_le_horiz_edge hd (hE j) hq0 hcδ hi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hinvN : 1 / (N : ℝ) ≤ δ ^ 2 := one_div_le_sq_of_zpow_le hδ hNδ
  have hL1 : (1 : ℝ) ≤ D.L := by linarith
  have hu0 : 0 ≤ D.q δ * (B * δ ^ 2 + M * δ) := by positivity
  have hu : D.q δ * (B * δ ^ 2 + M * δ) ≤ D.ρ δ * D.q δ := by
    rw [mul_comm (D.ρ δ)]
    refine mul_le_mul_of_nonneg_left ?_ hq0.le
    have e : B * δ ^ 2 + M * δ = δ * (B * δ + M) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hδ.le
  have hNu : D.q δ / N ≤ D.ρ δ * D.q δ := by
    rw [div_eq_mul_one_div, mul_comm (D.ρ δ)]
    refine mul_le_mul_of_nonneg_left (hinvN.trans ?_) hq0.le
    have h1 : δ ^ 2 ≤ δ := by
      rw [sq]
      exact mul_le_of_le_one_left hδ.le hδ1
    exact h1.trans (le_mul_of_one_le_right hδ.le hL1)
  have hs := fun j => D.norm_repl_sub_riem_le hd hCc hρq hN hE hgν hq0 hμ hW htr hu0 hu hNu j
  have hs0 : 0 ≤ Real.sqrt (Cc * (D.q δ * (B * δ ^ 2 + M * δ)) ^ 2 / (D.ρ δ * D.q δ)) +
      Real.sqrt (Cc * (D.q δ / N) ^ 2 / (D.ρ δ * D.q δ)) := by positivity
  have hiii := D.lp_tiltMass_le hκ hδ hG hμ hs0 hs
  have hga := gain_arith hCc0 hq0 D.K_cast_pos hq2 hL hδ hδ1 hB hM hBδ hNpos hinvN
  obtain ⟨S₂, hS₂⟩ : ∃ S, S = Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) := ⟨_, rfl⟩
  rw [← hS₂] at hiii hgain
  have hS₂0 : 0 ≤ S₂ := hS₂ ▸ Real.sqrt_nonneg _
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (Cc * (D.q δ * (B * δ ^ 2 + M * δ)) ^ 2 /
      (D.ρ δ * D.q δ)) + Real.sqrt (Cc * (D.q δ / N) ^ 2 / (D.ρ δ * D.q δ)) := ⟨_, rfl⟩
  rw [← hsdef] at hiii
  have hsY : s * S₂ ≤ Real.sqrt δ := by
    have h1 : s ≤ Real.sqrt δ * ((M + 2) * Real.sqrt (Cc * (2 / D.K) / D.L)) := by
      rw [hsdef]
      exact hga
    calc s * S₂ ≤ Real.sqrt δ * ((M + 2) * Real.sqrt (Cc * (2 / D.K) / D.L)) * S₂ :=
          mul_le_mul_of_nonneg_right h1 hS₂0
      _ = Real.sqrt δ * ((M + 2) * Real.sqrt (Cc * (2 / D.K) / D.L) * S₂) := by ring
      _ ≤ Real.sqrt δ * 1 := mul_le_mul_of_nonneg_left hgain (Real.sqrt_nonneg _)
      _ = Real.sqrt δ := mul_one _
  have hζs : δ ^ (3 / 2 : ℝ) * (s * S₂) ≤ δ ^ 2 := by
    rw [← rpow_three_halves_mul_sqrt hδ.le]
    exact mul_le_mul_of_nonneg_left hsY (Real.rpow_nonneg hδ.le _)
  have hw2 := mul_le_mul_of_nonneg_left hwR (sq_nonneg δ)
  calc ∫ Y, (D.lp δ N).tiltMass Sμ w Y ∂gLawD κ ((D.lp δ N).stepTris Sμ)
      ≤ 1 - δ ^ 2 * D.wR κ δ N + δ ^ (3 / 2 : ℝ) * (s * S₂) +
          ((D.J : ℝ) + 1) * (Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1) := hiii
    _ ≤ 1 - δ ^ 2 * (4 * D.e - 4 - θ / 2) + δ ^ 2 + θ * δ ^ 2 / 2 := by linarith
    _ = 1 - δ ^ 2 * (4 * D.e - 5) + θ * δ ^ 2 := by ring

/-- **Lemma 5.3 (ii) at a fixed `δ`, `N` and `μ`** (HA4 D6 Steps 1–3, (5.20)–(5.22)), under
explicit numerical conditions on the constants: `T μ ∈ C_δ`. -/
theorem lemma53_ii_at (hd : 0 < d) (hκ : IsLFPPKernel κ) {Cd : ℝ} (hCd0 : 0 ≤ Cd)
    (hCd : ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∀ (ν ν' : Measure (Rd d)) [IsFiniteMeasure ν] [IsFiniteMeasure ν'],
        GrowthBound ν' 4 1 → CoupledWithin ν ν' a →
        ∀ (η : Measure (Rd d)) [IsFiniteMeasure η], η ≤ ν →
          IsPairable κ (Ioo a b) η 0 ∧ scaleCov κ (Ioo a b) η 0 η 0 ≤ Cd * b * η.real univ)
    (he : 0 ≤ D.e) (hn : 1 ≤ D.n) (hg : 1 ≤ D.g)
    {δ M B M₀ c : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hB : 0 ≤ B)
    (hE : ∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ M₀ c (D.vert δ j))
    (hcδ : c * δ ≤ 1 / 2) (hδE : δ ^ 2 * D.E₀ ≤ 1)
    (h1 : D.q δ * (B + c * M) ≤ B) (h2 : M₀ + D.q δ * (B * δ + M) ≤ M) (hBδ : B * δ ≤ 1)
    (hML : M + 1 ≤ D.L)
    (hbudget : D.E₀ + D.q δ * (B + c * M) +
      3 * (Real.sqrt (Cd * D.L) * Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1)))) + 1 ≤ B)
    (hε3 : ((D.J : ℝ) + 1) * (Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1) ≤ δ ^ 2 / 3)
    (hC'δ : Real.sqrt (Cd * D.L) * Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) * δ ^ 2 ≤
      1 / 6)
    {N : ℕ} (hN : 0 < N) {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hμC : InCDelta δ M B Sμ w) :
    InCDelta δ M B ((D.lp δ N).stepPts Sμ) ((D.lp δ N).Tmap κ Sμ w) := by
  obtain ⟨hμ, htr, hW⟩ := hμC
  have hK := D.K_pos
  have hL := D.L_pos
  have hq0 : 0 < D.q δ := D.q_pos he δ
  have hqK : 1 / (D.K : ℝ) ≤ D.q δ := D.one_div_K_le_q he δ
  have hq1 : D.q δ < 1 := D.q_lt_one hn hg hδE
  have hρ : 0 < D.ρ δ := mul_pos hδ hL
  have hρq : 0 < D.ρ δ * D.q δ := mul_pos hρ hq0
  have hG : (D.lp δ N).Good := D.lp_good hd he hn hg hδ hδE hN hE
  have hgν : ∀ j, GrowthBound (D.ν δ j) 4 1 := fun j =>
    growthBound_polyM hd hK hqK fun i hi => half_le_horiz_edge hd (hE j) hq0 hcδ hi
  have hu : D.q δ * (B * δ ^ 2 + M * δ) ≤ D.ρ δ * D.q δ := by
    rw [mul_comm (D.ρ δ)]
    refine mul_le_mul_of_nonneg_left ?_ hq0.le
    have e : B * δ ^ 2 + M * δ = δ * (B * δ + M) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hδ.le
  have hσ := fun x j => D.norm_replM_le (N := N) hd hCd0 hCd hρq hq1.le hE hgν hq0 hμ hW htr hu
    (h := LParams.preW x) (LParams.preW_nonneg x) (LParams.preW_le_one x) j
  have hσ1 := fun j => D.norm_replM_le (N := N) hd hCd0 hCd hρq hq1.le hE hgν hq0 hμ hW htr hu
    (h := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl) j
  have hζ0 : 0 ≤ (D.lp δ N).ζ := Real.rpow_nonneg hδ.le _
  obtain ⟨S₂, hS₂⟩ : ∃ S, S = Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) := ⟨_, rfl⟩
  have hS₂0 : 0 ≤ S₂ := hS₂ ▸ Real.sqrt_nonneg _
  obtain ⟨C', hC'⟩ : ∃ C', C' = Real.sqrt (Cd * D.L) * S₂ := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := hC' ▸ mul_nonneg (Real.sqrt_nonneg _) hS₂0
  obtain ⟨ε, hε⟩ : ∃ ε, ε = ((D.J : ℝ) + 1) *
      (Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1) := ⟨_, rfl⟩
  rw [← hS₂, ← hC'] at hbudget hC'δ
  rw [← hε] at hε3
  have hζσ : (D.lp δ N).ζ * (Real.sqrt (Cd * D.ρ δ) * S₂) = C' * δ ^ 2 := by
    rw [hC']
    exact zeta_sigma_arith hδ.le
  have hεζ : (((D.lp δ N).J : ℝ) + 1) *
      (Real.exp ((D.lp δ N).ζ ^ 2 * Real.log (1 / (D.lp δ N).q) / 2) - 1) = ε := by
    have e1 : (D.lp δ N).ζ ^ 2 = δ ^ 3 := rpow_three_halves_sq hδ.le
    rw [e1, hε]
  have hS₂' : Real.sqrt (2 * Real.log (2 * (((D.lp δ N).J : ℝ) + 1))) = S₂ := hS₂.symm
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by
    have := mul_le_mul hδ1 hδ1 hδ.le (by norm_num)
    nlinarith
  have hsmall : (D.lp δ N).ζ * (Real.sqrt (Cd * D.ρ δ) *
      Real.sqrt (2 * Real.log (2 * (((D.lp δ N).J : ℝ) + 1)))) +
      (((D.lp δ N).J : ℝ) + 1) *
        (Real.exp ((D.lp δ N).ζ ^ 2 * Real.log (1 / (D.lp δ N).q) / 2) - 1) ≤ 1 / 3 := by
    rw [hS₂', hζσ, hεζ]
    linarith
  obtain ⟨hfin, hsupp, p, hp0, hp1, hclose⟩ := (D.lp δ N).tmap_props hG hκ hμ
    (Real.sqrt_nonneg _) hσ hσ1 hζ0 hsmall
  rw [hS₂', hζσ, hεζ] at hclose
  have hη : 0 ≤ 3 * C' * δ ^ 2 + δ ^ 2 := by positivity
  have hclose' : ∀ x, |hCDF ((D.lp δ N).stepPts Sμ) ((D.lp δ N).Tmap κ Sμ w) x -
      ∑ j, p j * replCDF D.K (D.q δ) (D.vert δ j) Sμ w x| ≤ 3 * C' * δ ^ 2 + δ ^ 2 := by
    intro x
    refine (hclose x).trans ?_
    linarith
  refine inCDelta_of_hCDF_close hd hK (v := D.vert δ) hE hq0 hδ.le hB h1 h2 ⟨hμ, htr, hW⟩
    hp0 hp1 hfin hsupp hη hclose' ?_
  have hB2 := mul_le_mul_of_nonneg_right hbudget (sq_nonneg δ)
  calc δ ^ 2 * D.E₀ + D.q δ * (B * δ ^ 2 + c * δ * (M * δ)) + (3 * C' * δ ^ 2 + δ ^ 2)
      = (D.E₀ + D.q δ * (B + c * M) + 3 * C' + 1) * δ ^ 2 := by ring
    _ ≤ B * δ ^ 2 := hB2

end LowerData

/-! ## The constants (HA4 §1 "order of choices", D6 "Constants") -/

theorem exists_unit_vector (hd : 2 ≤ d) : ∃ v : Rd (d - 1), ‖v‖ = 1 := by
  have hm : 0 < d - 1 := by omega
  refine ⟨EuclideanSpace.single (⟨0, hm⟩ : Fin (d - 1)) (1 : ℝ), ?_⟩
  simp

/-- `(n + 2)^{20} ≤ 2^{g_n}`, `g_n = ⌈20 log₂(n + 2)⌉` (source (5.1)). -/
theorem pad_le_two_pow_gPad (n : ℕ) : ((n : ℝ) + 2) ^ 20 ≤ 2 ^ gPad n := by
  have hx : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h1 : 20 * Real.logb 2 ((n : ℝ) + 2) ≤ (gPad n : ℝ) := Nat.le_ceil _
  have h2 : (2 : ℝ) ^ (20 * Real.logb 2 ((n : ℝ) + 2)) ≤ (2 : ℝ) ^ ((gPad n : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have h3 : (2 : ℝ) ^ (20 * Real.logb 2 ((n : ℝ) + 2)) = ((n : ℝ) + 2) ^ 20 := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx]
    exact_mod_cast Real.rpow_natCast ((n : ℝ) + 2) 20
  rw [Real.rpow_natCast, h3] at h2
  exact h2

theorem exp_sub_one_le_two_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x - 1 ≤ 2 * x := by
  have h := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at h
  exact (le_abs_self _).trans h

namespace LowerData

variable {D : LowerData d} {C : ℝ}

/-- **The Taylor remainder is `o(δ²)`** (HA4 D6 Step 2): for `δ³ log K ≤ 2` and `δ² E₀ ≤ 1`,
`J (e^{δ³ log(1/q)/2} - 1) ≤ J δ³ log K`. -/
theorem remainder_le (he : 0 ≤ D.e) (hn : 1 ≤ D.n) (hg : 1 ≤ D.g) {δ : ℝ} (hδ : 0 < δ)
    (hδE : δ ^ 2 * D.E₀ ≤ 1) (hsmall : δ ^ 3 * Real.log D.K ≤ 2) :
    ((D.J : ℝ) + 1) * (Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1) ≤
      ((D.J : ℝ) + 1) * (δ ^ 3 * Real.log D.K) := by
  have hq0 : 0 < D.q δ := D.q_pos he δ
  have hq1 : D.q δ < 1 := D.q_lt_one hn hg hδE
  have hqK : 1 / (D.K : ℝ) ≤ D.q δ := D.one_div_K_le_q he δ
  have hK := D.K_cast_pos
  have hl0 : 0 ≤ Real.log (1 / D.q δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hq0, one_mul]; exact hq1.le)
  have hlK : Real.log (1 / D.q δ) ≤ Real.log D.K := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hq0]
    rw [div_le_iff₀ hK] at hqK
    linarith
  have hx0 : 0 ≤ δ ^ 3 * Real.log (1 / D.q δ) / 2 := by positivity
  have hx1 : δ ^ 3 * Real.log (1 / D.q δ) / 2 ≤ 1 := by
    have : δ ^ 3 * Real.log (1 / D.q δ) ≤ δ ^ 3 * Real.log D.K :=
      mul_le_mul_of_nonneg_left hlK (by positivity)
    linarith
  have h := exp_sub_one_le_two_mul hx0 hx1
  refine mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
  have : δ ^ 3 * Real.log (1 / D.q δ) ≤ δ ^ 3 * Real.log D.K :=
    mul_le_mul_of_nonneg_left hlK (by positivity)
  linarith

/-- The geometric constant `M = (M₀ + q₀ + 1)/(1 - q₀)` (5.16), `M₀ = √e + 1`, `q₀ = 2/K`:
`M ≤ 2√e + 5`. -/
theorem constM_le (hn : 1 ≤ D.n) (hg : 1 ≤ D.g) :
    (√D.e + 1 + 2 / D.K + 1) / (1 - 2 / D.K) ≤ 2 * √D.e + 5 := by
  have hK4 := D.K_ge_four hn hg
  have hq₀ : 2 / (D.K : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hq₀0 : 0 ≤ 2 / (D.K : ℝ) := by positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Real.sqrt_nonneg D.e]

theorem sqrt_e_le (hD : D.Hyp C) : √D.e ≤ C * D.n + 1 := by
  have he := hD.e_nonneg
  have h1 : √D.e ≤ D.e + 1 := by
    rw [Real.sqrt_le_left]
    · nlinarith
    · linarith
  linarith [hD.e_le]

/-- `M + 1 ≤ L` and `M + 2 ≤ (2C + 9)(n + 2)` for `n + 2 ≥ 2C + 8` (HA4 D6: `L ≥ 2(M + 1)` is
not needed, `M + 1 ≤ L` suffices for `u ≤ ρq`). -/
theorem Hyp.constM_bounds (hD : D.Hyp C) (hx : 2 * C + 8 ≤ (D.n : ℝ) + 2) :
    (√D.e + 1 + 2 / D.K + 1) / (1 - 2 / D.K) + 1 ≤ D.L ∧
      (√D.e + 1 + 2 / D.K + 1) / (1 - 2 / D.K) + 2 ≤ (2 * C + 9) * ((D.n : ℝ) + 2) := by
  have hC := hD.C_nonneg
  have hM := constM_le (D := D) hD.one_le_n hD.one_le_g
  have hs := sqrt_e_le hD
  have hn0 : (0 : ℝ) ≤ D.n := Nat.cast_nonneg _
  set x : ℝ := (D.n : ℝ) + 2 with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; linarith
  have hnx : (D.n : ℝ) ≤ x := by rw [hxdef]; linarith
  have hCn : C * D.n ≤ C * x := mul_le_mul_of_nonneg_left hnx hC
  constructor
  · have hL : D.L = x ^ 4 := rfl
    rw [hL]
    have h2 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
    have h3 : (2 * C + 8) * x ≤ x * x := mul_le_mul_of_nonneg_right hx (by linarith)
    nlinarith
  · nlinarith

/-- The error of (5.23) is `≤ 1` once `n + 2 ≥ 4 C C_c (2C + 9)²` (HA4 §2.3, Step 4). -/
theorem Hyp.gain_le (hD : D.Hyp C) {Cc : ℝ} (hCc : 0 ≤ Cc)
    (hx : 4 * C * Cc * (2 * C + 9) ^ 2 ≤ (D.n : ℝ) + 2) {M : ℝ} (hM0 : 0 ≤ M)
    (hMb : M + 2 ≤ (2 * C + 9) * ((D.n : ℝ) + 2)) :
    (M + 2) * Real.sqrt (Cc * (2 / D.K) / D.L) *
      Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) ≤ 1 := by
  have hC := hD.C_nonneg
  have hn0 : (0 : ℝ) ≤ D.n := Nat.cast_nonneg _
  set x : ℝ := (D.n : ℝ) + 2 with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; linarith
  have hx0 : 0 < x := by linarith
  have hnx : (D.n : ℝ) ≤ x := by rw [hxdef]; linarith
  set P : ℝ := 2 ^ D.n with hP
  have hP0 : 0 < P := by positivity
  have hK := hD.K_ge
  have hlog := hD.log_le
  have hlog0 := log_two_mul_nonneg D.J
  have hL : D.L = x ^ 4 := rfl
  rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ M + 2), ← Real.sqrt_mul (sq_nonneg _),
    ← Real.sqrt_mul (by positivity)]
  refine sqrt_le_one_of_le ?_
  rw [hL]
  have hMb2 : (M + 2) ^ 2 ≤ ((2 * C + 9) * x) ^ 2 := pow_le_pow_left₀ (by linarith) hMb 2
  calc (M + 2) ^ 2 * (Cc * (2 / D.K) / x ^ 4) * (2 * Real.log (2 * ((D.J : ℝ) + 1)))
      ≤ ((2 * C + 9) * x) ^ 2 * (Cc * (2 / (x ^ 20 * P)) / x ^ 4) * (2 * C * D.n * P) := by
        have h2K : 2 / (D.K : ℝ) ≤ 2 / (x ^ 20 * P) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hK
        gcongr
    _ = 4 * C * Cc * (2 * C + 9) ^ 2 * (D.n * x ^ 2 / x ^ 24) := by
        field_simp
        ring
    _ ≤ 4 * C * Cc * (2 * C + 9) ^ 2 * (x ^ 3 / x ^ 24) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        calc (D.n : ℝ) * x ^ 2 ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right hnx (by positivity)
          _ = x ^ 3 := by ring
    _ ≤ 4 * C * Cc * (2 * C + 9) ^ 2 * (1 / x) :=
        mul_le_mul_of_nonneg_left (pow_div_pow_le_inv hx1 (by norm_num)) (by positivity)
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one hx0]
        exact hx

end LowerData

/-- **Lemma 5.3** (source §5.2; HA4 D6, Claim (i)–(iii)) for the lower-comparison data: for every
`C` there is `N₀` such that for all data `D` with the standing hypotheses (`LowerData.Hyp`) and
`n ≥ N₀` there are constants `M, B > 0` (chosen before `δ`) such that for every `θ > 0` and all
small `δ`: the equal-edge polygons of Lemma 5.1 satisfy `EqualEdgeData`, (i) `V_δ ⊆ U` and
`T_i^j(V_δ) ⊆ V_δ`, and for every Riemann parameter `N ≥ δ^{-2}` and every finitely supported
`μ ∈ C_δ`: (ii) `T μ ∈ C_δ` and (iii) `E ∫ e^{ζH} dν_{I,μ} ≤ 1 - δ²(4e - 5) + θδ²`, for P-L4's
construction `D.lp δ N` (the selector (5.7) at left Riemann points). -/
theorem lemma53 (hd : 2 ≤ d) (hκ : IsLFPPKernel κ) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ D : LowerData d, D.Hyp C → N₀ ≤ D.n →
      ∃ M B : ℝ, 0 < M ∧ 0 < B ∧ ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0,
        (∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ (√D.e + 1) (√2 * incrConst D.n D.e)
          (D.vert δ j)) ∧
        Vdelta δ M B ⊆ cube d ∧
        (∀ j, ∀ i < D.K,
          MapsTo (edgeSim (D.q δ) (D.vert δ j) i).app (Vdelta δ M B) (Vdelta δ M B)) ∧
        ∀ N : ℕ, 0 < N → δ ^ (-2 : ℤ) ≤ (N : ℝ) →
          ∀ (Sμ : Finset (Rd d)) (w : Rd d → ℝ), InCDelta δ M B Sμ w →
            InCDelta δ M B ((D.lp δ N).stepPts Sμ) ((D.lp δ N).Tmap κ Sμ w) ∧
            ∫ Y, (D.lp δ N).tiltMass Sμ w Y ∂gLawD κ ((D.lp δ N).stepTris Sμ) ≤
              1 - δ ^ 2 * (4 * D.e - 5) + θ * δ ^ 2 := by
  have hd0 : 0 < d := by omega
  obtain ⟨N₁, h52⟩ := lemma52 hd hκ C
  obtain ⟨N₂, h52R⟩ := lemma52_riemann hd hκ C
  obtain ⟨Cc, hCc0, hCc⟩ := bandLemma34c hκ 4
  obtain ⟨Cd, hCd0, hCd⟩ := bandLemma34d_var hκ 4
  refine ⟨max (max N₁ N₂) ⌈2 * C + 8 + 4 * C * Cc * (2 * C + 9) ^ 2⌉₊, fun D hD hN => ?_⟩
  have hN₁ : N₁ ≤ D.n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂ : N₂ ≤ D.n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hC := hD.C_nonneg
  have he := hD.e_nonneg
  have hn := hD.one_le_n
  have hg := hD.one_le_g
  have hx : 2 * C + 8 + 4 * C * Cc * (2 * C + 9) ^ 2 ≤ (D.n : ℝ) + 2 := by
    have h1 := Nat.le_ceil (2 * C + 8 + 4 * C * Cc * (2 * C + 9) ^ 2)
    have h2 : (⌈2 * C + 8 + 4 * C * Cc * (2 * C + 9) ^ 2⌉₊ : ℝ) ≤ D.n := by
      exact_mod_cast le_trans (le_max_right _ _) hN
    linarith
  have hx1 : 2 * C + 8 ≤ (D.n : ℝ) + 2 := by
    have : 0 ≤ 4 * C * Cc * (2 * C + 9) ^ 2 := by positivity
    linarith
  have hx2 : 4 * C * Cc * (2 * C + 9) ^ 2 ≤ (D.n : ℝ) + 2 := by linarith
  -- the constants of HA4 D6
  have hK4 := D.K_ge_four hn hg
  have hK := D.K_cast_pos
  have hq₀1 : 2 / (D.K : ℝ) < 1 := by rw [div_lt_one hK]; linarith
  have hq₀0 : 0 ≤ 2 / (D.K : ℝ) := by positivity
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (√D.e + 1 + 2 / D.K + 1) / (1 - 2 / D.K) := ⟨_, rfl⟩
  have hM0 : 0 < M := by
    rw [hMdef]
    exact div_pos (by positivity) (by linarith)
  obtain ⟨hML, hMb⟩ := hD.constM_bounds hx1
  rw [← hMdef] at hML hMb
  have hgain := hD.gain_le hCc0 hx2 hM0.le hMb
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = √2 * incrConst D.n D.e := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by
    rw [hc₁]
    exact mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one (one_le_incrConst _ _))
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = Real.sqrt (Cd * D.L) *
      Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
      B = (D.E₀ + 2 / D.K * c₁ * M + 3 * C' + 1) / (1 - 2 / D.K) := ⟨_, rfl⟩
  have hE₀ : 0 ≤ D.E₀ := by simp only [LowerData.E₀]; linarith
  have hB0 : 0 < B := by
    rw [hBdef]
    exact div_pos (by positivity) (by linarith)
  refine ⟨M, B, hM0, hB0, fun θ hθ => ?_⟩
  -- Lemma 5.1 for every profile
  have hK51 := hD.sqrt_le_K (by linarith)
  have hspec := fun j => ampl_spec hd0 hg (hD.mem j) (hD.energy_le j) hD.v_norm hK51
  choose hamp hδ₁ using hspec
  choose δ₁ hδ₁pos hδ₁spec using hδ₁
  -- the eventual smallness conditions
  have ev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j, δ ∈ Ioo 0 (δ₁ j) :=
    eventually_all.2 fun j => Ioo_mem_nhdsGT (hδ₁pos j)
  have ev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), c₁ * δ < 1 / 2 :=
    (tendsto_zero_of_continuous (continuous_const.mul continuous_id) (by simp)).eventually
      (gt_mem_nhds (by norm_num))
  have ev3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ 2 * D.E₀ < 1 :=
    (tendsto_zero_of_continuous ((continuous_pow 2).mul continuous_const) (by simp)).eventually
      (gt_mem_nhds (by norm_num))
  have ev4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 / 2 :=
    (tendsto_zero_of_continuous continuous_id (by simp)).eventually (gt_mem_nhds (by norm_num))
  have ev5 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), B * δ < 1 :=
    (tendsto_zero_of_continuous (continuous_const.mul continuous_id) (by simp)).eventually
      (gt_mem_nhds (by norm_num))
  have ev6 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), M * δ < 2 :=
    (tendsto_zero_of_continuous (continuous_const.mul continuous_id) (by simp)).eventually
      (gt_mem_nhds (by norm_num))
  have ev7 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((D.J : ℝ) + 1) * (δ * Real.log D.K) < min (θ / 2) (1 / 3) :=
    (tendsto_zero_of_continuous (continuous_const.mul (continuous_id.mul continuous_const))
      (by simp)).eventually (gt_mem_nhds (lt_min (by linarith) (by norm_num)))
  have ev8 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ 3 * Real.log D.K < 2 :=
    (tendsto_zero_of_continuous ((continuous_pow 3).mul continuous_const) (by simp)).eventually
      (gt_mem_nhds (by norm_num))
  have ev9 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), C' * δ ^ 2 < 1 / 6 :=
    (tendsto_zero_of_continuous (continuous_const.mul (continuous_pow 2)) (by simp)).eventually
      (gt_mem_nhds (by norm_num))
  have ev10 := h52 D hD hN₁ (θ / 4) (by linarith)
  have ev11 := h52R D hD hN₂ (θ / 4) (by linarith)
  filter_upwards [ev1, ev2, ev3, ev4, ev5, ev6, ev7, ev8, ev9, ev10, ev11, self_mem_nhdsWithin]
    with δ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  have hE : ∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ (√D.e + 1) (√2 * incrConst D.n D.e)
      (D.vert δ j) := fun j => ((hδ₁spec j) δ (e1 j)).2
  have hE' : ∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ (√D.e + 1) c₁ (D.vert δ j) := by
    rw [hc₁]
    exact hE
  have hq0 : 0 < D.q δ := D.q_pos he δ
  have hq2 : D.q δ ≤ 2 / D.K := D.q_le_two_div_K e3.le
  have hBδ : B * δ ≤ 1 := e5.le
  have h2 : (√D.e + 1) + D.q δ * (B * δ + M) ≤ M := by
    rw [hMdef]
    exact constM_spec (by positivity) hq₀1 hq0.le hq2 hBδ
  have hBspec := constB_spec (E₀ := D.E₀) (X := 3 * C') (c := c₁) (M := M)
    (by linarith) hc₁0 hM0.le hq₀1 hq0.le hq2
  rw [← hBdef] at hBspec
  obtain ⟨h1, hbudget⟩ := hBspec
  have hBδ2 : B * δ ^ 2 < 1 := by
    have : B * δ ^ 2 = B * δ * δ := by ring
    rw [this]
    nlinarith
  refine ⟨hE, Vdelta_subset_cube hd0 hBδ2 e6, fun j i hi =>
    edgeSim_mapsTo_Vdelta hd0 (hE' j) hq0 hδ0.le hB0.le h1 h2 hi, fun N hN0 hNδ Sμ w hμC => ?_⟩
  -- the remainder
  have hrem := LowerData.remainder_le (D := D) he hn hg hδ0 e3.le e8.le
  have hrem' : ((D.J : ℝ) + 1) * (δ ^ 3 * Real.log D.K) =
      δ ^ 2 * (((D.J : ℝ) + 1) * (δ * Real.log D.K)) := by ring
  rw [hrem'] at hrem
  have hεθ : ((D.J : ℝ) + 1) * (Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1) ≤
      θ * δ ^ 2 / 2 := by
    refine hrem.trans ?_
    have := mul_le_mul_of_nonneg_left (e7.le.trans (min_le_left _ _)) (sq_nonneg δ)
    linarith
  have hε3 : ((D.J : ℝ) + 1) * (Real.exp (δ ^ 3 * Real.log (1 / D.q δ) / 2) - 1) ≤
      δ ^ 2 / 3 := by
    refine hrem.trans ?_
    have := mul_le_mul_of_nonneg_left (e7.le.trans (min_le_right _ _)) (sq_nonneg δ)
    linarith
  have hwR : 4 * D.e - 4 - θ / 2 ≤ D.wR κ δ N := by
    have := abs_le.1 (e11 N hNδ)
    linarith [e10]
  rw [hC'] at e9
  refine ⟨D.lemma53_ii_at hd0 hκ hCd0 hCd he hn hg hδ0 e4.le hB0.le hE' e2.le e3.le h1 h2 hBδ
    hML ?_ hε3 e9.le hN0 hμC,
    D.lemma53_iii_at hd0 hκ hCc0 hCc he hn hg hδ0 (by linarith) hM0.le hB0.le hE' e2.le e3.le
      hBδ hML hgain hεθ hN0 hNδ hwR hμC⟩
  rw [← hC']
  exact hbudget

/-- **Lemma 5.3 holds** (source §5.2; P-L4's `Lemma53Holds`, the only hypothesis of the lower
comparison): for every `d ≥ 2` and every admissible kernel `κ`, with the Lemma 2.2 family
(P-V2's `lemma22b_fin`), `g = g_n` and `e = e_{n,d}`. -/
theorem lemma53Holds_holds (d : ℕ) (hd : 2 ≤ d) (κ : Rd d → ℝ) (hκ : IsLFPPKernel κ) :
    Lemma53Holds d κ := by
  obtain ⟨C₁, hC₁⟩ := lemma22a d hd
  obtain ⟨C₂, hC₂⟩ := lemma22b_fin d hd
  obtain ⟨N₀, h53⟩ := lemma53 hd hκ (max (max C₁ C₂) 0)
  obtain ⟨v₀, hv₀⟩ := exists_unit_vector hd
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N₀ ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨J, f, -, hmem, hen, hgem, hlog⟩ := hC₂ n hn1
  obtain ⟨-, -, heC⟩ := hC₁ n hn1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hD : (⟨n, gPad n, eN n d, J, f, v₀⟩ : LowerData d).Hyp (max (max C₁ C₂) 0) :=
    { one_le_n := hn1
      one_le_g := gPad_pos n
      pad := pad_le_two_pow_gPad n
      mem := hmem
      energy_le := hen
      e_le := heC.trans (mul_le_mul_of_nonneg_right
        ((le_max_left C₁ C₂).trans (le_max_left _ _)) hn0)
      gem := hgem
      log_card := hlog.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        ((le_max_right C₁ C₂).trans (le_max_left _ _)) hn0) (by positivity))
      v_norm := hv₀ }
  obtain ⟨M, B, hM, hB, hθ⟩ := h53 _ hD hnN
  refine ⟨J, M, B, hM, hB, fun θ hθ0 => (hθ θ hθ0).mono fun δ hδ => ?_⟩
  obtain ⟨hE, hcube, hmaps, hNμ⟩ := hδ
  refine ⟨(⟨n, gPad n, eN n d, J, f, v₀⟩ : LowerData d).vert δ,
    fun j => ⟨(hE j).start, (hE j).finish, (hE j).edge_len⟩, hcube, hmaps, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 ⌈δ ^ (-2 : ℤ)⌉₊)] with N hN Sμ μ hμC
  have hN1 : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hN)
  have hNδ : δ ^ (-2 : ℤ) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  exact hNμ N hN1 hNδ Sμ μ hμC

end HigherDimLFPP.Lower
