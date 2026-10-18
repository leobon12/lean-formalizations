import MeshRates.Section6OneSided
import MeshRates.Section6Torsion
import MeshRates.Section6ExitBound

/-!
# MR Theorem 1.1 (10): the normalized one-sided estimate at one vertex (MR pp. 14–15)

For a normalized solution (`hD - h ≤ 2` on the closed region, `‖D²h‖ ≤ 1` near the vertex,
`‖hD - h‖²_{2,m} ≤ C₅ ε²`), combine the one-sided estimate (79), Chebyshev (73), Lemma 6.1 and the
choice (80) of `η = ε^{4/(d+4)}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Topology ENNReal NNReal

namespace BouRabeeGwynne.MeshRates

/-- The constant of MR (81) in terms of `d`, the radius `r`, `C₅` (Lemma 5.1) and `C₆` (Lemma 6.1). -/
noncomputable def theorem11RateConst (d : ℕ) (r C₅ C₆ : ℝ) : ℝ :=
  4 * (1 + ((2 / r ^ 2 + 1 / 2) * (2 * (d : ℝ) * C₆ * (4 * C₅) ^ (2 / (d : ℝ))) +
    (2 / r ^ 2 + 1 / 2) * (2 * (d : ℝ) * C₆ * (4 * C₅) ^ (1 / (d : ℝ))) +
    (2 / r ^ 2 + 1 / 2) * (4 * r)))

lemma theorem11RateConst_nonneg (d : ℕ) {r C₅ C₆ : ℝ} (hr : 0 < r) (hC₅ : 0 ≤ C₅)
    (hC₆ : 0 < C₆) : 0 ≤ theorem11RateConst d r C₅ C₆ := by
  unfold theorem11RateConst; positivity

lemma theorem11_rate_alg {P Q S η X Y ε : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hS : 0 ≤ S)
    (hη : 0 ≤ η) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hε : 0 ≤ ε) :
    η / 2 + (P * X + Q * Y + S * ε) ≤ (1 + P + Q + S) * (η + X + Y + ε) := by
  nlinarith [mul_nonneg hP hη, mul_nonneg hP hY, mul_nonneg hP hε, mul_nonneg hQ hη,
    mul_nonneg hQ hX, mul_nonneg hQ hε, mul_nonneg hS hη, mul_nonneg hS hX, mul_nonneg hS hY]

open Classical in
/-- MR pp. 14–15, (72)–(80), normalized form at one vertex `z ∈ V[U]`. -/
theorem theorem11_rate_core {d : ℕ} (hd : 2 ≤ d) {C₅ C₆ : ℝ} (hC₅ : 0 ≤ C₅) (hC₆ : 0 < C₆)
    (H61 : ∀ (T : OrthogonalTiling d) (R : Set T.V) [Fintype R] [MeasurableSpace R]
      [MeasurableSingletonClass R] (S : Set R),
      T.mesh ≠ ∞ → S.Nonempty →
      (∀ v ∈ S, (T.cell v).carrier ⊆ interior T.domain) →
      (∀ v ∈ S, ∀ w : T.V, T.adj v w → w ∈ R) →
      ∀ x ∈ S, expectedExitTime T R S x ≤
        ENNReal.ofReal (C₆ *
          ((∑ v : R, S.indicator (fun v => (T.cell v).volume.toReal) v) ^ (2 / (d : ℝ)) +
            T.mesh.toReal *
              (∑ v : R, S.indicator (fun v => (T.cell v).volume.toReal) v) ^ (1 / (d : ℝ)))))
    (T : OrthogonalTiling d) (hmesh : T.mesh ≠ ∞) (hε1 : T.mesh.toReal ≤ 1)
    (U : Set (Euc d)) [Fintype (T.closedVertices U)]
    (hcellU : ∀ v : T.V, T.pos v ∈ U → (T.cell v).carrier ⊆ interior T.domain)
    (h : Euc d → ℝ) (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => h (T.pos v)) hD)
    (hf2 : ∀ v : T.closedVertices U, hD v - h (T.pos v) ≤ 2)
    (hL2 : ∑ v : T.closedVertices U, (T.cell v).volume.toReal * (hD v - h (T.pos v)) ^ 2 ≤
      C₅ * T.mesh.toReal ^ 2)
    (z : T.closedVertices U) (hz : T.pos z ∈ U) {r : ℝ} (hr : 0 < r)
    (hsmall : 4 * T.mesh.toReal ≤ r)
    (hball : Metric.closedBall (T.pos z) (2 * r) ⊆ interior T.domain)
    {W : Set (Euc d)} (hW : IsOpen W) (hballW : Metric.closedBall (T.pos z) (2 * r) ⊆ W)
    (hh : ContDiffOn ℝ 2 h W)
    (hH : ∀ x ∈ Metric.closedBall (T.pos z) (2 * r), ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ 1) :
    hD z - h (T.pos z) ≤
      theorem11RateConst d r C₅ C₆ * T.mesh.toReal ^ (4 / ((d : ℝ) + 4)) := by
  set ε := T.mesh.toReal with hεdef
  have hε0 : 0 < ε := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    exact mesh_toReal_pos_of_ne_top T hmesh z
  set η := ε ^ (4 / ((d : ℝ) + 4)) with hηdef
  have hη0 : 0 < η := Real.rpow_pos_of_pos hε0 _
  let R := T.closedVertices U
  letI : MeasurableSpace R := ⊤
  haveI : MeasurableSingletonClass R := ⟨fun _ => trivial⟩
  set m : R → ℝ := fun v => (T.cell v).volume.toReal with hmdef
  have hm : ∀ v, 0 < m v := fun v => cellVolume_toReal_pos T v
  set A : Set R := {v | T.pos v ∈ U ∧ η / 2 < hD v - h (T.pos v) ∧ dist (T.pos v) (T.pos z) < r}
    with hAdef
  obtain ⟨Ad, Bd, hAd, hBd, hdec⟩ := lemma61_survival_exp_decay hd
  have hcellA : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain := fun v hv => hcellU v hv.1
  have hnbA : ∀ v ∈ A, ∀ w : T.V, T.adj v w → w ∈ R :=
    fun v hv w hw => T.neighbor_mem_closedVertices hv.1 hw
  have hfin : ∀ x ∈ A, expectedExitTime T R A x ≠ ∞ := fun x hx =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (H61 T R A hmesh ⟨x, hx⟩ hcellA hnbA x hx)
  have hdecay : ∀ x ∈ A, Filter.Tendsto (fun t : ℝ≥0 => survivalProb T R A x t) Filter.atTop
      (nhds 0) := by
    intro x hx
    obtain ⟨hρ, hb⟩ := hdec T R A hmesh ⟨x, hx⟩ hcellA hnbA _ rfl
    set ρ := (∑ v : R, A.indicator (fun v => (T.cell v).volume.toReal) v) ^ (2 / (d : ℝ)) +
      T.mesh.toReal * (∑ v : R, A.indicator (fun v => (T.cell v).volume.toReal) v) ^
        (1 / (d : ℝ))
    have h1 : Filter.Tendsto (fun t : ℝ => Ad * Real.exp (-(t - ρ) / (Bd * ρ))) Filter.atTop
        (nhds 0) := by
      have h2 : Filter.Tendsto (fun t : ℝ => (t - ρ) / (Bd * ρ)) Filter.atTop Filter.atTop :=
        (Filter.tendsto_atTop_add_const_right _ (-ρ) Filter.tendsto_id).atTop_div_const
          (by positivity)
      have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h2).const_mul Ad
      simp only [mul_zero] at h3
      refine h3.congr (fun t => ?_)
      show Ad * Real.exp (-((t - ρ) / (Bd * ρ))) = _
      congr 2; ring
    have hg := h1.comp (NNReal.tendsto_coe_atTop.mpr Filter.tendsto_id)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Filter.Eventually.of_forall fun t => ENNReal.toReal_nonneg) ?_
    filter_upwards [Filter.eventually_ge_atTop ρ.toNNReal] with t ht
    have := hb x hx t (by simpa using (Real.toNNReal_le_iff_le_coe.mp ht))
    simpa using this
  obtain ⟨hG0', hGgen⟩ := expectedExitTime_torsion T R A hfin hdecay
  set G : R → ℝ := fun y => (expectedExitTime T R A y).toReal with hGdef
  have key := section6_oneSided_estimate hd T hmesh U hcellU h hD hsol hf2 z hz hr hη0
    zero_le_one hsmall hball hW hballW hh hH G
    (fun v hv => by
      have := hGgen v hv
      unfold FiniteConductanceNetwork.massGenerator at this
      rw [div_eq_iff (hm v).ne'] at this
      simpa [G, m] using this)
    (fun v hv => by simp [G, hG0' v hv])
  -- (73): Chebyshev
  set mA := ∑ v : R, A.indicator (fun v => (T.cell v).volume.toReal) v with hmAdef
  have hmA0 : 0 ≤ mA :=
    Finset.sum_nonneg (fun v _ => Set.indicator_nonneg (fun v _ => (hm v).le) v)
  have hmA : mA ≤ 4 * C₅ * (ε / η) ^ 2 := by
    calc mA ≤ ∑ v : R, (4 / η ^ 2) * ((T.cell v).volume.toReal * (hD v - h (T.pos v)) ^ 2) := by
          refine Finset.sum_le_sum (fun v _ => ?_)
          by_cases hv : v ∈ A
          · rw [Set.indicator_of_mem hv]
            have hf : η / 2 < hD v - h (T.pos v) := hv.2.1
            have hsq : η ^ 2 / 4 ≤ (hD v - h (T.pos v)) ^ 2 := by nlinarith
            have hmv := hm v
            rw [← mul_assoc, mul_comm (4 / η ^ 2), mul_assoc]
            have : 1 ≤ 4 / η ^ 2 * (hD v - h (T.pos v)) ^ 2 := by
              rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
            nlinarith
          · rw [Set.indicator_of_notMem hv]
            have := (hm v).le
            positivity
      _ = (4 / η ^ 2) * ∑ v : R, (T.cell v).volume.toReal * (hD v - h (T.pos v)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (4 / η ^ 2) * (C₅ * ε ^ 2) := mul_le_mul_of_nonneg_left hL2 (by positivity)
      _ = 4 * C₅ * (ε / η) ^ 2 := by field_simp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set X := (ε / η) ^ (4 / (d : ℝ)) with hX
  set Y := (ε / η) ^ (2 / (d : ℝ)) with hY
  have hq0 : 0 ≤ ε / η := by positivity
  have hpow : ∀ p : ℝ, 0 ≤ p → mA ^ p ≤ (4 * C₅) ^ p * ((ε / η) ^ 2) ^ p := fun p hp =>
    (Real.rpow_le_rpow hmA0 hmA hp).trans_eq (Real.mul_rpow (by positivity) (by positivity))
  have hsq : ∀ p : ℝ, ((ε / η) ^ 2) ^ p = (ε / η) ^ (2 * p) := fun p => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0]; norm_num
  have hA2 : mA ^ (2 / (d : ℝ)) ≤ (4 * C₅) ^ (2 / (d : ℝ)) * X := by
    have := hpow (2 / (d : ℝ)) (by positivity)
    rw [hsq] at this
    rw [hX]; convert this using 3; ring
  have hA1 : mA ^ (1 / (d : ℝ)) ≤ (4 * C₅) ^ (1 / (d : ℝ)) * Y := by
    have := hpow (1 / (d : ℝ)) (by positivity)
    rw [hsq] at this
    rw [hY]; convert this using 3; ring
  -- Lemma 6.1 at z
  have hGz : G z ≤ C₆ * (mA ^ (2 / (d : ℝ)) + ε * mA ^ (1 / (d : ℝ))) := by
    by_cases hzA : z ∈ A
    · exact ENNReal.toReal_le_of_le_ofReal (by positivity)
        (H61 T R A hmesh ⟨z, hzA⟩ hcellA hnbA z hzA)
    · simp only [G, hG0' z hzA, ENNReal.toReal_zero]; positivity
  have hGz' : G z ≤ C₆ * ((4 * C₅) ^ (2 / (d : ℝ)) * X + ε * ((4 * C₅) ^ (1 / (d : ℝ)) * Y)) := by
    refine hGz.trans (mul_le_mul_of_nonneg_left ?_ hC₆.le)
    gcongr
  -- (80)
  have hrate := rate_choice_le (d := d) (by omega) hε0 hε1
  rw [← hηdef, ← hX, ← hY] at hrate
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  set K1 := 2 / r ^ 2 + 1 / 2 with hK1
  have hK1pos : 0 < K1 := by positivity
  have hbr : 2 * ε * (r + 2 * ε) ≤ 4 * r * ε := by nlinarith
  have hstep : hD z - h (T.pos z) ≤ η / 2 +
      (K1 * (2 * d * C₆ * (4 * C₅) ^ (2 / (d : ℝ))) * X +
        K1 * (2 * d * C₆ * (4 * C₅) ^ (1 / (d : ℝ))) * (ε * Y) + K1 * (4 * r) * ε) := by
    refine key.trans ?_
    have h1 : 2 * (d : ℝ) * G z ≤
        2 * d * (C₆ * ((4 * C₅) ^ (2 / (d : ℝ)) * X + ε * ((4 * C₅) ^ (1 / (d : ℝ)) * Y))) :=
      mul_le_mul_of_nonneg_left hGz' (by positivity)
    have h2 : K1 * (2 * (d : ℝ) * G z + 2 * ε * (r + 2 * ε)) ≤
        K1 * (2 * d * (C₆ * ((4 * C₅) ^ (2 / (d : ℝ)) * X + ε * ((4 * C₅) ^ (1 / (d : ℝ)) * Y)))
          + 4 * r * ε) :=
      mul_le_mul_of_nonneg_left (by linarith) hK1pos.le
    have h3 : (1 : ℝ) / 2 = 1 / 2 := rfl
    simp only [one_div] at h2 ⊢
    linarith [h2, show K1 * (2 * d * (C₆ * ((4 * C₅) ^ (2 / (d : ℝ)) * X +
        ε * ((4 * C₅) ^ (1 / (d : ℝ)) * Y))) + 4 * r * ε) =
      K1 * (2 * d * C₆ * (4 * C₅) ^ (2 / (d : ℝ))) * X +
        K1 * (2 * d * C₆ * (4 * C₅) ^ (1 / (d : ℝ))) * (ε * Y) + K1 * (4 * r) * ε by ring]
  have halg := theorem11_rate_alg (P := K1 * (2 * d * C₆ * (4 * C₅) ^ (2 / (d : ℝ))))
    (Q := K1 * (2 * d * C₆ * (4 * C₅) ^ (1 / (d : ℝ)))) (S := K1 * (4 * r))
    (η := η) (X := X) (Y := ε * Y) (ε := ε)
    (by positivity) (by positivity) (by positivity) hη0.le hX0 (by positivity) hε0.le
  have hCs : 0 ≤ 1 + K1 * (2 * d * C₆ * (4 * C₅) ^ (2 / (d : ℝ))) +
      K1 * (2 * d * C₆ * (4 * C₅) ^ (1 / (d : ℝ))) + K1 * (4 * r) := by positivity
  have := mul_le_mul_of_nonneg_left hrate hCs
  calc hD z - h (T.pos z) ≤ _ := hstep
    _ ≤ _ := halg
    _ ≤ _ := this
    _ = theorem11RateConst d r C₅ C₆ * η := by
      rw [theorem11RateConst, ← hK1]; ring

end BouRabeeGwynne.MeshRates
