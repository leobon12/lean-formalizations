import LQGMetric.Metric.WeylPathLength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The Weyl competitor along a Lipschitz path (blueprint `lem:weyl-lipschitz`; BP2 detail D4)

Let `D₁ = e^{ξF}·D₂` (Weyl scaling, `weylScale ξ F D₂ = D₁`) and let `c : ℝ → ℂ` be continuous on
`[0,1]` and `L`-Lipschitz for `D₂` (`D₂(c s, c t) ≤ L (t − s)` for `0 ≤ s ≤ t ≤ 1`). Then
`D₁(c 0, c 1) ≤ L ∫₀¹ e^{ξ F(c t)} dt` (`dist_le_mul_integral_exp_of_weyl`).

Proof (blueprint, with a multiplicative modulus): fix `ε > 0` and let `δ` be a modulus of uniform
continuity of `g = ξ F ∘ c` on `[0,1]`; take `N` with `1/N < δ` and the partition `t_i = i/N`. On
`[t_i, t_{i+1}]`, `ξF ≤ b_i := g(t_i) + ε`, so `len(c; D₁) ≤ e^{b_i} len(c; D₂) ≤ e^{b_i} L/N`
(LQGMetric's `curveLength_weyl_le` and the Lipschitz bound), and `e^{b_i}/N ≤ e^{2ε} ∫_{t_i}^{t_{i+1}} e^g`.
Summing, `D₁(c 0, c 1) ≤ len(c; D₁) ≤ L e^{2ε} ∫₀¹ e^g`; let `ε → 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SmallGammaGeodesics

open LQGMetric LQGMetric.MetricGeometry

/-- A `C`-Lipschitz curve on `[a, b]` has length at most `C (b − a)` (as LQGMetric's
`GM.curveLength_le_lip_m2m2`, restated here to keep the imports light). -/
theorem curveLength_le_ofReal_of_lipschitzOn {X : Type*} [PseudoMetricSpace X] {P : ℝ → X}
    {C a b : ℝ} (hC : 0 ≤ C)
    (hP : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (P s) (P t) ≤ C * dist s t) :
    curveLength P a b ≤ ENNReal.ofReal (C * (b - a)) := by
  have hL : LipschitzOnWith C.toNNReal P (Icc a b) :=
    LipschitzOnWith.of_dist_le_mul fun s hs t ht => by
      rw [Real.coe_toNNReal _ hC]; exact hP s hs t ht
  calc curveLength P a b = eVariationOn (P ∘ id) (Icc a b) := rfl
    _ ≤ C.toNNReal * eVariationOn id (Icc a b) := hL.comp_eVariationOn_le (mapsTo_id _)
    _ = ENNReal.ofReal (C * (b - a)) := by
        rw [eVariationOn_id_Icc, ENNReal.ofReal_mul hC]; rfl

/-- **Lemma `lem:weyl-lipschitz`** (BP2 D4): the Weyl competitor bound along a path that is
`L`-Lipschitz for `D₂`, where `D₁ = e^{ξF}·D₂`. -/
theorem dist_le_mul_integral_exp_of_weyl {ξ : ℝ} {F : C(ℂ, ℝ)} {D₁ D₂ : ContMetric}
    (hW : ∀ x y, weylScale ξ F D₂ x y = ENNReal.ofReal (D₁.1 (x, y))) {c : ℝ → ℂ}
    (hc : ContinuousOn c (Icc 0 1)) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, s ≤ t → D₂.1 (c s, c t) ≤ L * (t - s)) :
    D₁.1 (c 0, c 1) ≤ L * ∫ t in (0:ℝ)..1, Real.exp (ξ * F (c t)) := by
  have hD' : ∀ x y : ℂ, ENNReal.ofReal (D₁.1 (x, y)) = weylScale ξ F D₂ x y :=
    fun x y => (hW x y).symm
  set g : ℝ → ℝ := fun t => ξ * F (c t) with hgdef
  have hgc : ContinuousOn g (Icc 0 1) :=
    continuousOn_const.mul (F.continuous.comp_continuousOn hc)
  set I := ∫ t in (0:ℝ)..1, Real.exp (g t) with hIdef
  have hI0 : 0 ≤ I :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => (Real.exp_pos _).le
  -- the `D₂`-Lipschitz bound, symmetrized
  have hLip' : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
      dist (D₂.pt (c s)) (D₂.pt (c t)) ≤ L * dist s t := by
    intro s hs t ht
    show D₂.1 (c s, c t) ≤ L * dist s t
    rcases le_total s t with hst | hts
    · rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      have := hLip s hs t ht hst
      linarith
    · rw [D₂.2.symm, Real.dist_eq, abs_of_nonneg (by linarith)]
      exact hLip t ht s hs hts
  have hcont₂ : ContinuousOn (D₂.pt ∘ c) (Icc 0 1) :=
    (continuous_weylPt D₂).comp_continuousOn hc
  -- the bound with a multiplicative error `e^{2ε}`
  have key : ∀ ε > 0, D₁.1 (c 0, c 1) ≤ L * Real.exp (2 * ε) * I := by
    intro ε hε
    obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hgc) ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    set N : ℕ := n + 1 with hNdef
    have hN : (0 : ℝ) < N := by rw [hNdef]; positivity
    set u : ℕ → ℝ := fun i => (i : ℝ) / N with hudef
    have hu : Monotone u := fun i k hik => by
      simp only [hudef]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hik) hN.le
    have hu0 : u 0 = 0 := by simp [hudef]
    have huN : u N = 1 := by simp only [hudef]; exact div_self hN.ne'
    have hustep : ∀ i, u (i + 1) - u i = 1 / N := fun i => by
      simp only [hudef]; push_cast; ring
    have humem : ∀ i < N, Icc (u i) (u (i + 1)) ⊆ Icc 0 1 := by
      intro i hi
      refine Icc_subset_Icc ?_ ?_
      · rw [← hu0]; exact hu (Nat.zero_le _)
      · rw [← huN]; exact hu (by omega)
    -- the modulus on each piece
    have hmod : ∀ i < N, ∀ τ ∈ Icc (u i) (u (i + 1)), g (u i) ≤ g τ + ε := by
      intro i hi τ hτ
      have hτ01 := humem i hi hτ
      have hui01 : u i ∈ Icc (0:ℝ) 1 := humem i hi ⟨le_rfl, hu (Nat.le_succ i)⟩
      have hd : dist (u i) τ < δ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hτ.1])]
        have : τ - u i ≤ 1 / N := by linarith [hτ.2, hustep i]
        have hn' : (1 : ℝ) / N = 1 / ((n : ℝ) + 1) := by simp [hNdef]
        linarith
      have := hδg (u i) hui01 τ hτ01 hd
      rw [Real.dist_eq] at this
      linarith [le_abs_self (g (u i) - g τ)]
    -- the length bound on each piece
    have hpiece : ∀ i < N, curveLength (D₁.pt ∘ c) (u i) (u (i + 1)) ≤
        ENNReal.ofReal (Real.exp (g (u i) + ε) * (L * (1 / N))) := by
      intro i hi
      have hsub := humem i hi
      have hst : u i ≤ u (i + 1) := hu (Nat.le_succ i)
      have h1 := curveLength_weyl_le D₁ hD' hst (hcont₂.mono hsub)
        (V := c '' Icc (u i) (u (i + 1))) (fun τ hτ => mem_image_of_mem c hτ)
        (b := g (u i) + ε) (by
          rintro _ ⟨τ, hτ, rfl⟩
          show g τ ≤ g (u i) + ε
          have hτ01 := hsub hτ
          have hui01 : u i ∈ Icc (0:ℝ) 1 := hsub ⟨le_rfl, hst⟩
          have hd : dist τ (u i) < δ := by
            rw [Real.dist_eq, abs_of_nonneg (by linarith [hτ.1])]
            have : τ - u i ≤ 1 / N := by linarith [hτ.2, hustep i]
            have hn' : (1 : ℝ) / N = 1 / ((n : ℝ) + 1) := by simp [hNdef]
            linarith
          have h2 := hδg τ hτ01 (u i) hui01 hd
          rw [Real.dist_eq] at h2
          linarith [le_abs_self (g τ - g (u i))])
      have h2 : curveLength (D₂.pt ∘ c) (u i) (u (i + 1)) ≤ ENNReal.ofReal (L * (1 / N)) := by
        rw [← hustep i]
        exact curveLength_le_ofReal_of_lipschitzOn hL fun s hs t ht =>
          hLip' s (hsub hs) t (hsub ht)
      calc curveLength (D₁.pt ∘ c) (u i) (u (i + 1))
          ≤ ENNReal.ofReal (Real.exp (g (u i) + ε)) * curveLength (D₂.pt ∘ c) (u i) (u (i + 1)) :=
            h1
        _ ≤ ENNReal.ofReal (Real.exp (g (u i) + ε)) * ENNReal.ofReal (L * (1 / N)) := by gcongr
        _ = ENNReal.ofReal (Real.exp (g (u i) + ε) * (L * (1 / N))) :=
            (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    -- the Riemann-sum bound on each piece
    have hint : ∀ i < N, Real.exp (g (u i) + ε) * (1 / N) ≤
        ∫ t in u i..u (i + 1), Real.exp (g t + 2 * ε) := by
      intro i hi
      have hst : u i ≤ u (i + 1) := hu (Nat.le_succ i)
      have hcont : ContinuousOn (fun t => Real.exp (g t + 2 * ε)) (Icc (u i) (u (i + 1))) :=
        Real.continuous_exp.comp_continuousOn ((hgc.mono (humem i hi)).add continuousOn_const)
      calc Real.exp (g (u i) + ε) * (1 / N)
          = ∫ _ in u i..u (i + 1), Real.exp (g (u i) + ε) := by
            rw [intervalIntegral.integral_const, hustep i, smul_eq_mul, mul_comm]
        _ ≤ ∫ t in u i..u (i + 1), Real.exp (g t + 2 * ε) := by
            refine intervalIntegral.integral_mono_on hst intervalIntegrable_const
              (hcont.intervalIntegrable_of_Icc hst) fun τ hτ => ?_
            exact Real.exp_le_exp.2 (by linarith [hmod i hi τ hτ])
    -- summing up
    have hsum_int : ∑ i ∈ Finset.range N, ∫ t in u i..u (i + 1), Real.exp (g t + 2 * ε) =
        Real.exp (2 * ε) * I := by
      have hii : ∀ i < N, IntervalIntegrable (fun t => Real.exp (g t + 2 * ε)) volume (u i)
          (u (i + 1)) := fun i hi =>
        ContinuousOn.intervalIntegrable_of_Icc (hu (Nat.le_succ i))
          (Real.continuous_exp.comp_continuousOn ((hgc.mono (humem i hi)).add continuousOn_const))
      rw [intervalIntegral.sum_integral_adjacent_intervals hii, hu0, huN, hIdef,
        ← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      rw [Real.exp_add, mul_comm]
    have hlen : ENNReal.ofReal (D₁.1 (c 0, c 1)) ≤ curveLength (D₁.pt ∘ c) 0 1 := by
      have := edist_le_curveLength (D₁.pt ∘ c) (zero_le_one' ℝ)
      rw [edist_dist] at this
      exact this
    have hsplit : curveLength (D₁.pt ∘ c) 0 1 =
        ∑ i ∈ Finset.range N, curveLength (D₁.pt ∘ c) (u i) (u (i + 1)) := by
      rw [sum_curveLength_eq' (D₁.pt ∘ c) hu N, hu0, huN]
    have hfin : ENNReal.ofReal (D₁.1 (c 0, c 1)) ≤
        ENNReal.ofReal (L * Real.exp (2 * ε) * I) := by
      calc ENNReal.ofReal (D₁.1 (c 0, c 1))
          ≤ ∑ i ∈ Finset.range N, curveLength (D₁.pt ∘ c) (u i) (u (i + 1)) := hsplit ▸ hlen
        _ ≤ ∑ i ∈ Finset.range N, ENNReal.ofReal (Real.exp (g (u i) + ε) * (L * (1 / N))) :=
            Finset.sum_le_sum fun i hi => hpiece i (Finset.mem_range.1 hi)
        _ = ENNReal.ofReal (∑ i ∈ Finset.range N, Real.exp (g (u i) + ε) * (L * (1 / N))) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity).symm
        _ ≤ ENNReal.ofReal (L * Real.exp (2 * ε) * I) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc ∑ i ∈ Finset.range N, Real.exp (g (u i) + ε) * (L * (1 / N))
                = L * ∑ i ∈ Finset.range N, Real.exp (g (u i) + ε) * (1 / N) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun i _ => by ring
              _ ≤ L * ∑ i ∈ Finset.range N, ∫ t in u i..u (i + 1), Real.exp (g t + 2 * ε) :=
                  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi =>
                    hint i (Finset.mem_range.1 hi)) hL
              _ = L * Real.exp (2 * ε) * I := by rw [hsum_int]; ring
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfin
  -- let `ε → 0`
  have ht : Tendsto (fun ε : ℝ => L * Real.exp (2 * ε) * I) (𝓝[>] 0)
      (𝓝 (L * Real.exp (2 * 0) * I)) :=
    (((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [mul_zero, Real.exp_zero, mul_one] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

end SmallGammaGeodesics
