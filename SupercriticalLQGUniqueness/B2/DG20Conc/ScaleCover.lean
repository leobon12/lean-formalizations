import SupercriticalLQGUniqueness.B2.DG20Conc.ConnectedDomain
import LQGMetric.LFPP.PathAnalytic

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory
open LQGMetric.DDDF
open LQGDimension.TreeIneqJ42 (exists_piece deriv_bound_piece)

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem exists_linear_grid_cover_of_lipschitz_path
    {q : ℝ → ℂ} {L c : ℝ} (hL : 0 ≤ L) (hc : 0 < c)
    (hq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (q s) (q t) ≤ L * |s - t|) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * R ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          ∃ j : ℕ, j ≤ m ∧
            dist (R • q t) (R • q ((j : ℝ) / m)) ≤ c := by
  refine ⟨L / c + 3, by positivity, fun R hR => ?_⟩
  let a : ℝ := R * L / c
  let m : ℕ := ⌊a⌋₊ + 1
  have hR0 : 0 ≤ R := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hmpos : 0 < m := by dsimp [m]; omega
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hfloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have hceil : a < (m : ℝ) := by
    dsimp [m]
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one a
  have hmC : (m : ℝ) ≤ (L / c + 3) * R := by
    have hm1 : (m : ℝ) ≤ a + 1 := by
      dsimp [m]
      push_cast
      linarith
    have hrewrite : R * L / c = R * (L / c) := by ring
    change (m : ℝ) ≤ R * L / c + 1 at hm1
    rw [hrewrite] at hm1
    have : 0 ≤ L / c := div_nonneg hL hc.le
    nlinarith
  refine ⟨m, hmpos, hmC, fun t ht => ?_⟩
  let j : ℕ := ⌊t * (m : ℝ)⌋₊
  have htm0 : 0 ≤ t * (m : ℝ) := mul_nonneg ht.1 hmr.le
  have hjle : j ≤ m := by
    have hcast : (j : ℝ) ≤ m :=
      (Nat.floor_le htm0).trans (mul_le_of_le_one_left hmr.le ht.2)
    exact_mod_cast hcast
  have hjr : (j : ℝ) ≤ t * m := Nat.floor_le htm0
  have hjr' : t * m < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hgrid : (j : ℝ) / m ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hmr.le
    · apply (div_le_iff₀ hmr).2
      simpa only [one_mul] using (show (j : ℝ) ≤ m by exact_mod_cast hjle)
  have hdiff0 : 0 ≤ t - (j : ℝ) / m := by
    exact sub_nonneg.mpr ((div_le_iff₀ hmr).2 hjr)
  have hdiff : t - (j : ℝ) / m ≤ 1 / m := by
    rw [sub_le_iff_le_add, ← add_div]
    apply (le_div_iff₀ hmr).2
    nlinarith [hjr'.le]
  have hbound : R * L / m ≤ c := by
    apply (div_le_iff₀ hmr).2
    have hmul : R * L < m * c := (div_lt_iff₀ hc).1 hceil
    linarith
  refine ⟨j, hjle, ?_⟩
  calc
    dist (R • q t) (R • q ((j : ℝ) / m))
        = R * dist (q t) (q ((j : ℝ) / m)) := by
          simp [dist_eq_norm, ← mul_sub, Complex.norm_real, abs_of_nonneg hR0]
    _ ≤ R * (L * |t - (j : ℝ) / m|) :=
      mul_le_mul_of_nonneg_left (hq t ht _ hgrid) hR0
    _ ≤ R * L / m := by
      rw [abs_of_nonneg hdiff0]
      have hRL : 0 ≤ R * L := mul_nonneg hR0 hL
      calc
        R * (L * (t - (j : ℝ) / m)) = (R * L) * (t - (j : ℝ) / m) := by ring
        _ ≤ (R * L) * (1 / m) := mul_le_mul_of_nonneg_left hdiff hRL
        _ = R * L / m := by ring
    _ ≤ c := hbound

 


theorem IsPiecewiseC1Path.exists_lipschitz_bound
    {P : ℝ → ℂ} {z w : ℂ} (hP : LQGMetric.IsPiecewiseC1Path P z w) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (P s) (P t) ≤ L * |s - t| := by
  obtain ⟨k, τ, hτ, hτ0, hτ1, hC⟩ := hP.piecewise
  have hB : ∀ i : Fin k, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Ioo (τ i.castSucc) (τ i.succ), ‖deriv P x‖ ≤ C :=
    fun i => deriv_bound_piece (hτ Fin.castSucc_lt_succ) (hC i)
  choose C hC0 hCb using hB
  let L : ℝ := ∑ i, C i
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => hC0 i
  have hbound : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ range τ → ‖deriv P x‖ ≤ L := by
    intro x hx hxt
    obtain ⟨i, h1, h2⟩ := exists_piece hτ0 hτ1 hx hxt
    exact (hCb i x ⟨h1, h2⟩).trans
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))
  have hfin : (insert (1 : ℝ) (range τ)).Countable :=
    ((finite_range τ).insert 1).countable
  have hpoint : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      ‖P b - P a‖ ≤ L * (b - a) := by
    intro a b ha hab hb
    have hfi : IntervalIntegrable (fun x => ‖deriv P x‖) volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
        (hP.integrableOn_norm_deriv ha hb)
    have hgi : IntervalIntegrable (fun _ : ℝ => L) volume a b :=
      intervalIntegrable_const
    have hae : (fun x => ‖deriv P x‖) ≤ᵐ[volume.restrict (Icc a b)]
        (fun _ : ℝ => L) := by
      change ∀ᵐ x ∂volume.restrict (Icc a b), ‖deriv P x‖ ≤ L
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hfin.ae_notMem volume] with x hx hxI
      rw [mem_insert_iff, not_or] at hx
      have hxOpen : x ∈ Ioo (0 : ℝ) 1 := by
        constructor
        · exact lt_of_le_of_ne (ha.trans hxI.1) (by
            intro heq
            apply hx.2
            exact ⟨0, by simp [← heq, hτ0]⟩)
        · exact lt_of_le_of_ne (hxI.2.trans hb) hx.1
      exact hbound x hxOpen hx.2
    calc
      ‖P b - P a‖ ≤ ∫ x in a..b, ‖deriv P x‖ := hP.norm_sub_le ha hab hb
      _ ≤ ∫ _x in a..b, L :=
        intervalIntegral.integral_mono_ae_restrict hab hfi hgi hae
      _ = L * (b - a) := by simp [mul_comm]
  refine ⟨L, hL, fun s hs t ht => ?_⟩
  rcases le_total s t with hst | hts
  · have h := hpoint s t hs.1 hst ht.2
    have habs : |s - t| = t - s := by
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      ring
    calc
      dist (P s) (P t) = ‖P t - P s‖ := by rw [dist_comm, dist_eq_norm]
      _ ≤ L * (t - s) := h
      _ = L * |s - t| := by rw [habs]
  · have h := hpoint t s ht.1 hts hs.2
    simpa [dist_eq_norm, abs_of_nonneg (sub_nonneg.mpr hts)] using h

 



theorem exists_linear_grid_cover_of_open_connected
    {U A B : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAU : A ⊆ U) (hBU : B ⊆ U) :
    ∃ (q : ℝ → ℂ) (c δ C : ℝ),
      AdmPath U A B q ∧ 0 < c ∧ 0 < δ ∧ 2 * c ≤ δ ∧ 0 < C ∧
      (∀ t ∈ Icc (0 : ℝ) 1, closedBall (q t) δ ⊆ U) ∧
      ∀ R : ℝ, 1 ≤ R →
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * R ∧
          (∀ j : ℕ, j ≤ m → closedBall (q ((j : ℝ) / m)) δ ⊆ U) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∃ j : ℕ, j ≤ m ∧
            dist (R • q t) (R • q ((j : ℝ) / m)) ≤ c) := by
  obtain ⟨q, hq⟩ := exists_admPath_of_open_connected hU hUc hA hB hAU hBU
  obtain ⟨δ, hδ, htube⟩ := exists_uniform_tube_of_admPath hU hq
  rcases hq with ⟨z, hz, w, hw, hqp, hqU⟩
  obtain ⟨L, hL, hLip⟩ := IsPiecewiseC1Path.exists_lipschitz_bound hqp
  obtain ⟨C, hC, hcover⟩ :=
    exists_linear_grid_cover_of_lipschitz_path hL (half_pos hδ) hLip
  refine ⟨q, δ / 2, δ, C, ⟨z, hz, w, hw, hqp, hqU⟩,
    half_pos hδ, hδ, by ring_nf; rfl, hC, htube, fun R hR => ?_⟩
  obtain ⟨m, hm, hmC, hgrid⟩ := hcover R hR
  refine ⟨m, hm, hmC, ?_, hgrid⟩
  intro j hj
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  apply htube
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hmr.le
  · apply (div_le_iff₀ hmr).2
    simpa only [one_mul] using (show (j : ℝ) ≤ m by exact_mod_cast hj)

 

theorem closedBall_smul_subset_image_of_tube
    {U : Set ℂ} {z : ℂ} {δ c R : ℝ}
    (hR : 0 < R) (hc : c ≤ R * δ)
    (htube : closedBall z δ ⊆ U) :
    closedBall (R • z) c ⊆ (fun w : ℂ => R • w) '' U := by
  intro x hx
  refine ⟨R⁻¹ • x, htube ?_, ?_⟩
  · have hz : R⁻¹ • (R • z) = z := by
      rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    have hdist : dist (R⁻¹ • x) z = R⁻¹ * dist x (R • z) := by
      calc
        dist (R⁻¹ • x) z = dist (R⁻¹ • x) (R⁻¹ • (R • z)) := by rw [hz]
        _ = R⁻¹ * dist x (R • z) := by
          rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le)]
    rw [mem_closedBall, hdist]
    have hcx : dist x (R • z) ≤ c := mem_closedBall.mp hx
    have hci : R⁻¹ * c ≤ δ := by
      apply (inv_mul_le_iff₀ hR).2
      simpa only [inv_inv] using hc
    exact (mul_le_mul_of_nonneg_left hcx (inv_nonneg.mpr hR.le)).trans hci
  · change R • (R⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

 


theorem exists_linear_ball_cover_of_open_connected
    {U A B : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAU : A ⊆ U) (hBU : B ⊆ U) :
    ∃ (q : ℝ → ℂ) (c C : ℝ),
      AdmPath U A B q ∧ 0 < c ∧ 0 < C ∧
      ∀ R : ℝ, 1 ≤ R →
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * R ∧
          (∀ j : ℕ, j ≤ m →
            closedBall (R • q ((j : ℝ) / m)) (2 * c) ⊆
              (fun w : ℂ => R • w) '' U) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∃ j : ℕ, j ≤ m ∧
            dist (R • q t) (R • q ((j : ℝ) / m)) ≤ c) := by
  obtain ⟨q, c, δ, C, hq, hc, hδ, hcδ, hC, _htube, hcover⟩ :=
    exists_linear_grid_cover_of_open_connected hU hUc hA hB hAU hBU
  refine ⟨q, c, C, hq, hc, hC, fun R hR => ?_⟩
  obtain ⟨m, hm, hmC, hcenters, hgrid⟩ := hcover R hR
  refine ⟨m, hm, hmC, ?_, hgrid⟩
  intro j hj
  apply closedBall_smul_subset_image_of_tube (by linarith : 0 < R) ?_
    (hcenters j hj)
  exact hcδ.trans (le_mul_of_one_le_left hδ.le hR)

end SupercriticalLQGUniqueness.B2.DG20Conc
