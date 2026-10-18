import MeshRates.ExitTime
import MeshRates.Section2Nash
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# MR Lemma 6.1: expected exit time from a finite set

Route (MR (69)–(71)), with the eigenvalue bound (69) replaced by the equivalent `L²(m)`
contraction of `P^S_s 1_S`, proved by Grönwall from the support inequality (23).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal NNReal
open MeasureTheory

namespace BouRabeeGwynne.MeshRates

section Abstract

variable {V : Type*} [Fintype V] [DecidableEq V] (N : FiniteConductanceNetwork V)

/-- (69) in contraction form: if `‖f‖²_{2,m} ≤ κ D(f)` for all `f` supported on `S`, then
`‖P^S_s 1_S‖²_{2,m} ≤ e^{-2s/κ} m(S)`. -/
lemma exitDecay_weighted_sq_le (m : V → ℝ) (hm : ∀ v, m v ≠ 0) (S : Set V) {κ : ℝ}
    (hκ : 0 < κ)
    (hY : ∀ f : V → ℝ, S.indicator f = f → (∑ v, m v * f v ^ 2) ≤ κ * N.energy f)
    {s : ℝ} (hs : 0 ≤ s) :
    (∑ v, m v * (N.killedHeatFlow m S 1 s v) ^ 2) ≤
      Real.exp (-2 * s / κ) * ∑ v, S.indicator m v := by
  set Y : ℝ → ℝ := fun s => ∑ v, m v * (N.killedHeatFlow m S 1 s v) ^ 2 with hYdef
  have hder (r : ℝ) : HasDerivAt Y (-2 * N.energy (N.killedHeatFlow m S 1 r)) r := by
    have h := N.hasDerivAt_weighted_sq_of_killed_heat m hm S (N.killedHeatFlow m S 1) r
      (fun v => N.hasDerivAt_killedHeatFlow_apply m S 1 r v)
    simpa only [N.indicator_killedHeatFlow] using h
  set g : ℝ → ℝ := fun r => Real.exp (2 * r / κ) * Y r
  have hg (r : ℝ) : HasDerivAt g (Real.exp (2 * r / κ) * (2 / κ) * Y r +
      Real.exp (2 * r / κ) * (-2 * N.energy (N.killedHeatFlow m S 1 r))) r := by
    have he : HasDerivAt (fun r => Real.exp (2 * r / κ)) (Real.exp (2 * r / κ) * (2 / κ)) r := by
      have := ((hasDerivAt_id r).const_mul (2 / κ)).exp
      convert this using 1
      · funext r; simp only [id]; ring_nf
      · simp only [id, mul_one]; ring_nf
    exact he.mul (hder r)
  have hanti : Antitone g := by
    refine antitone_of_hasDerivAt_nonpos hg (fun r => ?_)
    have h1 := hY _ (N.indicator_killedHeatFlow m S 1 r)
    have hep := Real.exp_pos (2 * r / κ)
    have : (2 / κ) * Y r ≤ 2 * N.energy (N.killedHeatFlow m S 1 r) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hκ]; simp only [Y]; nlinarith
    calc _ = Real.exp (2 * r / κ) * ((2 / κ) * Y r - 2 * N.energy (N.killedHeatFlow m S 1 r)) := by
          ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hep.le (by linarith)
  have hg0 : g 0 = ∑ v, S.indicator m v := by
    simp only [g, Y, mul_zero, zero_div, Real.exp_zero, one_mul, N.killedHeatFlow_zero]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ S <;> simp [hv]
  have hle : g s ≤ g 0 := hanti hs
  rw [hg0] at hle
  have : Y s = Real.exp (-2 * s / κ) * g s := by
    simp only [g, ← mul_assoc, ← Real.exp_add]
    rw [show -2 * s / κ + 2 * s / κ = 0 by ring, Real.exp_zero, one_mul]
  change Y s ≤ _
  rw [this]
  exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-- The survival probability is `(P^S_t 1_S)(x)`. -/
lemma exitDecay_survival_eq_flow (m : V → ℝ) (hm : ∀ v, 0 < m v) [MeasurableSpace V]
    [MeasurableSingletonClass V] (S : Set V) {x : V} (hx : x ∈ S) (t : ℝ≥0) :
    (N.poissonizedUniformizedLaw m hm S x t S).toReal = N.killedHeatFlow m S 1 t x := by
  rw [N.poissonizedUniformizedLaw_survival m hm S hx]
  simp only [FiniteConductanceNetwork.killedHeatFlow, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [N.mass_mul_killedHeatDensity m (fun v => (hm v).ne') S hx]
  by_cases hy : y ∈ S
  · simp [hy]
  · have h0 : N.killedHeatDensity m S x t y = 0 :=
      N.killedHeatFlow_eq_zero_of_not_mem m S _ _ hy
    have : N.killedHeatMatrix m S t x y = 0 := by
      rw [← N.mass_mul_killedHeatDensity m (fun v => (hm v).ne') S hx, h0, mul_zero]
    simp [hy, this]

/-- (71), squared: `((P^S_{ρ+u} 1_S)(x))² ≤ p^S_{2ρ}(x,x) ‖P^S_u 1_S‖²_{2,m}` (semigroup property
and Cauchy–Schwarz). -/
lemma exitDecay_flow_sq_le (m : V → ℝ) (hm : ∀ v, 0 < m v) (S : Set V) {x : V} (hx : x ∈ S)
    (ρ u : ℝ) :
    (N.killedHeatFlow m S 1 (ρ + u) x) ^ 2 ≤
      N.killedHeatDensity m S x (2 * ρ) x * ∑ v, m v * (N.killedHeatFlow m S 1 u v) ^ 2 := by
  have hsplit : N.killedHeatFlow m S 1 (ρ + u) x =
      ∑ z, m z * N.killedHeatDensity m S x ρ z * N.killedHeatFlow m S 1 u z := by
    simp only [FiniteConductanceNetwork.killedHeatFlow]
    rw [N.killedHeatMatrix_add, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [N.mass_mul_killedHeatDensity m (fun v => (hm v).ne') S hx]
  rw [hsplit, ← N.killedHeatDensity_weighted_sq_eq_double m (fun v => (hm v).ne') S hx]
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun v _ => mul_nonneg (hm v).le (sq_nonneg _))
    (fun v _ => mul_nonneg (hm v).le (sq_nonneg _)) (fun v _ => le_of_eq (by ring))

end Abstract

/-- (70), the scalar part: with `ρ = M^{2/d} + ε M^{1/d}`,
`M (ρ^{-d/2} + ε^d ρ^{-d}) = (M^{2/d}/ρ)^{d/2} + (ε M^{1/d}/ρ)^d ≤ 2`. -/
lemma lemma61_mass_mul_kernelScale_le {d : ℕ} (hd : 1 ≤ d) {M ε ρ : ℝ} (hM : 0 < M)
    (hε : 0 ≤ ε) (hρ : ρ = M ^ (2 / (d : ℝ)) + ε * M ^ (1 / (d : ℝ))) :
    M * (ρ ^ (-(d : ℝ) / 2) + ε ^ d * ρ ^ (-(d : ℝ))) ≤ 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h2pos : 0 < M ^ (2 / (d : ℝ)) := Real.rpow_pos_of_pos hM _
  have h1nn : 0 ≤ ε * M ^ (1 / (d : ℝ)) := mul_nonneg hε (Real.rpow_nonneg hM.le _)
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hA : M ≤ ρ ^ ((d : ℝ) / 2) := by
    have hMe : M = (M ^ (2 / (d : ℝ))) ^ ((d : ℝ) / 2) := by
      rw [← Real.rpow_mul hM.le, show 2 / (d : ℝ) * ((d : ℝ) / 2) = 1 by field_simp,
        Real.rpow_one]
    rw [hMe]
    exact Real.rpow_le_rpow h2pos.le (by rw [hρ]; linarith) (by positivity)
  have hB : ε ^ d * M ≤ ρ ^ d := by
    have hMe : M = (M ^ (1 / (d : ℝ))) ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le,
        show 1 / (d : ℝ) * (d : ℝ) = 1 by field_simp, Real.rpow_one]
    rw [hMe, ← mul_pow]
    exact pow_le_pow_left₀ h1nn (by rw [hρ]; linarith) d
  have e1 : ρ ^ (-(d : ℝ) / 2) = (ρ ^ ((d : ℝ) / 2))⁻¹ := by
    rw [neg_div, Real.rpow_neg hρpos.le]
  have e2 : ρ ^ (-(d : ℝ)) = (ρ ^ d)⁻¹ := by
    rw [Real.rpow_neg hρpos.le, Real.rpow_natCast]
  have p1 : 0 < ρ ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hρpos _
  have p2 : 0 < ρ ^ d := pow_pos hρpos d
  rw [e1, e2, mul_add, ← mul_assoc, mul_comm M (ε ^ d)]
  have q1 : M * (ρ ^ ((d : ℝ) / 2))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one p1]; exact hA
  have q2 : ε ^ d * M * (ρ ^ d)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one p2]; exact hB
  linarith

open Classical in
/-- MR (69)–(71): exponential decay of the survival probability after time `ρ`,
`P_x(τ_S > t) ≤ A e^{-(t-ρ)/(Bρ)}` for `t ≥ ρ = m(S)^{2/d} + ε m(S)^{1/d}`; `A, B` depend only
on `d`. -/
theorem lemma61_survival_exp_decay {d : ℕ} (hd : 2 ≤ d) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (T : OrthogonalTiling d) (R : Set T.V) [Fintype R]
      [MeasurableSpace R] [MeasurableSingletonClass R] (S : Set R),
      T.mesh ≠ ∞ → S.Nonempty →
      (∀ v ∈ S, (T.cell v).carrier ⊆ interior T.domain) →
      (∀ v ∈ S, ∀ w : T.V, T.adj v w → w ∈ R) →
      ∀ ρ : ℝ, ρ = (∑ v : R, S.indicator (fun v => (T.cell v).volume.toReal) v) ^ (2 / (d : ℝ)) +
            T.mesh.toReal *
              (∑ v : R, S.indicator (fun v => (T.cell v).volume.toReal) v) ^ (1 / (d : ℝ)) →
      0 < ρ ∧ ∀ x ∈ S, ∀ t : ℝ, ρ ≤ t →
        survivalProb T R S x t.toNNReal ≤ A * Real.exp (-(t - ρ) / (B * ρ)) := by
  obtain ⟨C₂, hC₂, h23⟩ := prop23_defectiveNash_and_support hd
  obtain ⟨C₃, hC₃, h31⟩ := prop31_onDiagonal_and_survival hd
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  refine ⟨Real.sqrt (2 * C₃), C₂ + 1, Real.sqrt_pos.mpr (by linarith), by linarith, ?_⟩
  intro T R _ _ _ S hmesh hne hcell hnb ρ hρ
  set m : R → ℝ := fun v => (T.cell v).volume.toReal with hmdef
  have hm : ∀ v, 0 < m v := fun v => cellVolume_toReal_pos T v
  set M := ∑ v : R, S.indicator m v with hMdef
  obtain ⟨x₀, hx₀⟩ := hne
  have hM : 0 < M := Finset.sum_pos' (fun v _ => Set.indicator_nonneg (fun v _ => (hm v).le) v)
    ⟨x₀, Finset.mem_univ _, by simpa [hx₀] using hm x₀⟩
  have hε : 0 < T.mesh.toReal := mesh_toReal_pos_of_ne_top T hmesh (x₀ : T.V)
  have hρpos : 0 < ρ := by
    rw [hρ]
    have := Real.rpow_pos_of_pos hM (2 / ((n + 1 : ℕ) : ℝ))
    have := mul_nonneg hε.le (Real.rpow_nonneg hM.le (1 / ((n + 1 : ℕ) : ℝ)))
    linarith
  refine ⟨hρpos, ?_⟩
  intro x hx t ht
  set N := T.finiteNetwork R
  set κ := (C₂ + 1) * ρ with hκdef
  have hκ : 0 < κ := by positivity
  -- (23) with `V = m(S)`: `‖f‖²_{2,m} ≤ κ D(f)` for `f` supported on `S`.
  have hY : ∀ f : R → ℝ, S.indicator f = f → (∑ v, m v * f v ^ 2) ≤ κ * N.energy f := by
    intro f hf
    have hsupp : ∀ v : R, f v ≠ 0 → v ∈ S := by
      intro v hv; by_contra h; apply hv; rw [← hf]; simp [h]
    have h := (h23 T R f hmesh (fun v hv => hcell v (hsupp v hv))
      (fun v hv => hnb v (hsupp v hv))).2
    set Vf := ∑ v : R, if f v ≠ 0 then (T.cell v).volume.toReal else 0
    have hVf0 : 0 ≤ Vf := Finset.sum_nonneg fun v _ => by split_ifs <;> simp
    have hVfM : Vf ≤ M := Finset.sum_le_sum fun v _ => by
      by_cases hv : f v ≠ 0
      · simp [hv, hsupp v hv, m]
      · simp only [hv, ite_false]; exact Set.indicator_nonneg (fun v _ => (hm v).le) v
    have hVρ : Vf ^ (2 / ((n + 1 : ℕ) : ℝ)) + T.mesh.toReal * Vf ^ (1 / ((n + 1 : ℕ) : ℝ)) ≤ ρ := by
      rw [hρ]; gcongr
    have hE := N.energy_nonneg f
    have hX0 : 0 ≤ Vf ^ (2 / ((n + 1 : ℕ) : ℝ)) + T.mesh.toReal * Vf ^ (1 / ((n + 1 : ℕ) : ℝ)) :=
      add_nonneg (Real.rpow_nonneg hVf0 _) (mul_nonneg hε.le (Real.rpow_nonneg hVf0 _))
    calc (∑ v, m v * f v ^ 2) ≤ _ := h
      _ ≤ C₂ * ρ * N.energy f := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVρ hC₂) hE
      _ ≤ κ * N.energy f := by
        rw [hκdef]; nlinarith [mul_nonneg hρpos.le hE]
  have hs : 0 ≤ t - ρ := by linarith
  have hdecay := exitDecay_weighted_sq_le N m (fun v => (hm v).ne') S hκ hY hs
  have hsq := exitDecay_flow_sq_le N m hm S hx ρ (t - ρ)
  rw [add_sub_cancel] at hsq
  have hp := (h31 T R S hmesh hcell hnb x hx).1 ρ hρpos
  have hp0 : 0 ≤ N.killedHeatDensity m S x (2 * ρ) x :=
    N.killedHeatDensity_nonneg m hm S hx (by linarith) x
  have h70 := lemma61_mass_mul_kernelScale_le (d := n + 1) (by omega) hM hε.le hρ
  have hMp : M * N.killedHeatDensity m S x (2 * ρ) x ≤ 2 * C₃ := by
    calc M * N.killedHeatDensity m S x (2 * ρ) x
        ≤ M * (C₃ * (ρ ^ (-((n + 1 : ℕ) : ℝ) / 2) +
            T.mesh.toReal ^ (n + 1) * ρ ^ (-((n + 1 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hp hM.le
      _ = C₃ * (M * (ρ ^ (-((n + 1 : ℕ) : ℝ) / 2) +
            T.mesh.toReal ^ (n + 1) * ρ ^ (-((n + 1 : ℕ) : ℝ)))) := by ring
      _ ≤ C₃ * 2 := mul_le_mul_of_nonneg_left h70 hC₃.le
      _ = 2 * C₃ := by ring
  have hsurv : survivalProb T R S x t.toNNReal = N.killedHeatFlow m S 1 t x := by
    unfold survivalProb
    rw [exitDecay_survival_eq_flow N m hm S hx, Real.coe_toNNReal _ (by linarith)]
  have hexp : Real.exp (-2 * (t - ρ) / κ) = Real.exp (-(t - ρ) / κ) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hP2 : (N.killedHeatFlow m S 1 t x) ^ 2 ≤
      (Real.sqrt (2 * C₃) * Real.exp (-(t - ρ) / κ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith), ← hexp]
    calc _ ≤ _ := hsq
      _ ≤ N.killedHeatDensity m S x (2 * ρ) x * (Real.exp (-2 * (t - ρ) / κ) * M) :=
          mul_le_mul_of_nonneg_left hdecay hp0
      _ = Real.exp (-2 * (t - ρ) / κ) * (M * N.killedHeatDensity m S x (2 * ρ) x) := by ring
      _ ≤ Real.exp (-2 * (t - ρ) / κ) * (2 * C₃) :=
          mul_le_mul_of_nonneg_left hMp (Real.exp_pos _).le
      _ = _ := by ring
  rw [hsurv]
  calc _ ≤ |N.killedHeatFlow m S 1 t x| := le_abs_self _
    _ = Real.sqrt ((N.killedHeatFlow m S 1 t x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Real.sqrt (2 * C₃) * Real.exp (-(t - ρ) / κ)) ^ 2) := Real.sqrt_le_sqrt hP2
    _ = _ := Real.sqrt_sq (by positivity)

open Classical in
/-- `P_x(τ_S > t) ≤ 1`. -/
lemma survivalProb_le_one {d : ℕ} (T : OrthogonalTiling d) (R : Set T.V) [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] (S : Set R) {x : R} (hx : x ∈ S)
    (t : ℝ≥0) : survivalProb T R S x t ≤ 1 := by
  unfold survivalProb
  rw [(T.finiteNetwork R).poissonizedUniformizedLaw_survival _ _ S hx]
  refine le_trans (Finset.sum_le_sum fun y _ => ?_)
    ((T.finiteNetwork R).killedHeatDensity_weighted_L1_le_one _
      (fun v => cellVolume_toReal_pos T v) S hx t.2)
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (cellVolume_toReal_pos T y).le

open Classical in
/-- MR Lemma 6.1, (67)–(68): for a nonempty finite set `S` of vertices whose cells lie in the
interior of the tiled set (MR: `⋃_{v∈S} P_v ⋐ D`), with `R = m(S)^{1/d}`,
`sup_{x∈S} E_x τ_S ≤ C_d (R² + εR)`; `C_d` depends only on `d`. The chain lives on a finite region
`R` containing every neighbour of `S`. -/
theorem lemma61_expectedExitTime_le {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : OrthogonalTiling d) (R : Set T.V) [Fintype R] [MeasurableSpace R]
      [MeasurableSingletonClass R] (S : Set R),
      T.mesh ≠ ∞ → S.Nonempty →
      (∀ v ∈ S, (T.cell v).carrier ⊆ interior T.domain) →
      (∀ v ∈ S, ∀ w : T.V, T.adj v w → w ∈ R) →
      ∀ x ∈ S, expectedExitTime T R S x ≤
        ENNReal.ofReal (C *
          ((∑ v : R, S.indicator (fun v => (T.cell v).volume.toReal) v) ^ (2 / (d : ℝ)) +
            T.mesh.toReal *
              (∑ v : R, S.indicator (fun v => (T.cell v).volume.toReal) v) ^ (1 / (d : ℝ)))) := by
  obtain ⟨A, B, hA, hB, hdec⟩ := lemma61_survival_exp_decay hd
  refine ⟨1 + A * B, by positivity, ?_⟩
  intro T R _ _ _ S hmesh hne hcell hnb x hx
  set ρ := (∑ v : R, S.indicator (fun v => (T.cell v).volume.toReal) v) ^ (2 / (d : ℝ)) +
    T.mesh.toReal * (∑ v : R, S.indicator (fun v => (T.cell v).volume.toReal) v) ^ (1 / (d : ℝ))
    with hρdef
  obtain ⟨hρ, hbound⟩ := hdec T R S hmesh hne hcell hnb ρ rfl
  set b := 1 / (B * ρ) with hbdef
  have hb : 0 < b := by positivity
  set K := A * Real.exp (1 / B) with hKdef
  have hfun : ∀ t : ℝ, A * Real.exp (-(t - ρ) / (B * ρ)) = K * Real.exp (-b * t) := by
    intro t
    rw [hKdef, mul_assoc, ← Real.exp_add]
    congr 2
    rw [hbdef]; field_simp; ring
  unfold expectedExitTime
  rw [← Set.Ioc_union_Ioi_eq_Ioi hρ.le]
  refine (lintegral_union_le _ _ _).trans ?_
  have h1 : ∫⁻ t in Set.Ioc (0 : ℝ) ρ, ENNReal.ofReal (survivalProb T R S x t.toNNReal) ≤
      ENNReal.ofReal ρ := by
    calc _ ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) ρ, (1 : ℝ≥0∞) :=
          setLIntegral_mono' measurableSet_Ioc fun t _ =>
            ENNReal.ofReal_le_one.mpr (survivalProb_le_one T R S hx _)
      _ = ENNReal.ofReal ρ := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero]
  have hint : IntegrableOn (fun t : ℝ => K * Real.exp (-b * t)) (Set.Ioi ρ) :=
    (exp_neg_integrableOn_Ioi ρ hb).const_mul K
  have hval : ∫ t in Set.Ioi ρ, K * Real.exp (-b * t) = A * B * ρ := by
    rw [integral_const_mul]
    have := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) ρ hb
    simp only [smul_eq_mul] at this
    simp_rw [neg_mul]
    rw [this, integral_exp_neg_Ioi, show b * ρ = 1 / B by rw [hbdef]; field_simp, hKdef,
      hbdef]
    have : Real.exp (1 / B) * Real.exp (-(1 / B)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [one_div (B * ρ), inv_inv]
    linear_combination (A * B * ρ) * this
  have h2 : ∫⁻ t in Set.Ioi ρ, ENNReal.ofReal (survivalProb T R S x t.toNNReal) ≤
      ENNReal.ofReal (A * B * ρ) := by
    calc _ ≤ ∫⁻ t in Set.Ioi ρ, ENNReal.ofReal (K * Real.exp (-b * t)) :=
          setLIntegral_mono' measurableSet_Ioi fun t ht => ENNReal.ofReal_le_ofReal (by
            rw [← hfun]; exact hbound x hx t (le_of_lt ht))
      _ = ENNReal.ofReal (A * B * ρ) := by
          rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun t => by positivity)]
  calc _ ≤ ENNReal.ofReal ρ + ENNReal.ofReal (A * B * ρ) := add_le_add h1 h2
    _ = ENNReal.ofReal ((1 + A * B) * ρ) := by
        rw [← ENNReal.ofReal_add hρ.le (by positivity)]; ring_nf

end BouRabeeGwynne.MeshRates
