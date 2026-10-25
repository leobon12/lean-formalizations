import SupercriticalLQGUniqueness.B2.PfeWeyl.W1LocalBounds
import SupercriticalLQGUniqueness.B2.PfeWeyl.CurveOscillation
import SupercriticalLQGUniqueness.B2.PfeWeyl.LocalizedSampling
import SupercriticalLQGUniqueness.B2.PfeWeyl.GeoAnnuli

 






















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


def AcrossUnbounded (D : LSCMetric) : Prop :=
  ∀ k : ℕ, ∀ T : ℝ≥0∞, T ≠ ⊤ →
    ∃ R : Set.Ioi (2 * ((k : ℝ) + 1)),
      T < acrossDist D (outerAnnulus ((k : ℝ) + 1) (Nat.cast_add_one_pos k) R)

 
theorem le_of_forall_small_add_mul {a X C : ℝ≥0∞} (hC : C ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ η' : ℝ, 0 < η' → η' ≤ δ → a ≤ X + ENNReal.ofReal η' * C) : a ≤ X := by
  have htend : Tendsto (fun η' : ℝ => X + ENNReal.ofReal η' * C) (𝓝[>] 0)
      (𝓝 (X + ENNReal.ofReal 0 * C)) := by
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hC)
    exact (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [ENNReal.ofReal_zero, zero_mul, add_zero] at htend
  refine ge_of_tendsto htend ?_
  have hev : ∀ᶠ η' in 𝓝[>] (0 : ℝ), η' < δ :=
    nhdsWithin_le_nhds (gt_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hev] with η' hη' hη'δ
  exact h η' hη' hη'δ.le

 
theorem ofReal_exp_shift (ξ a θ : ℝ) :
    ENNReal.ofReal (Real.exp (ξ * (a + θ))) =
      ENNReal.ofReal (Real.exp (2 * ξ * θ)) * ENNReal.ofReal (Real.exp (ξ * (a - θ))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

 

theorem weyl_gamma_liminf_core
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (M : ℝ) (hfnM : ∀ n z, |fn n z| ≤ M)
    (hGforget : ∀ n, Continuous (euclidForget (G n)))
    (hDlen : D.IsLengthSpace) (hDforget : Continuous (euclidForget D))
    (hacross : AcrossUnbounded D)
    {p : ℕ → ℂ × ℂ} {q : ℂ × ℂ} (hp : Tendsto p atTop (𝓝 q))
    {θ : ℝ} (hθ : 0 < θ) {B : ℝ} (hB : 0 < B) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hfreq : ∃ᶠ n in atTop, weylScale ξ (fn n) (G n) (p n) < ENNReal.ofReal B) :
    weylScale ξ f D q ≤
      ENNReal.ofReal (Real.exp (2 * ξ * θ)) * (ENNReal.ofReal B + ENNReal.ofReal η) := by
  
  obtain ⟨k, hk⟩ := exists_nat_gt (max ‖q.1‖ ‖q.2‖)
  set r : ℝ := (k : ℝ) + 1 with hrdef
  have hr : 0 < r := Nat.cast_add_one_pos k
  have hq1 : ‖q.1‖ < 2 * r := by
    have := le_max_left ‖q.1‖ ‖q.2‖
    linarith
  have hq2 : ‖q.2‖ < 2 * r := by
    have := le_max_right ‖q.1‖ ‖q.2‖
    linarith
  set Λ : ℝ := Real.exp (ξ * M) * (B + 1) with hΛdef
  obtain ⟨R, hR⟩ := hacross k (ENNReal.ofReal Λ) ENNReal.ofReal_ne_top
  set A : EuclideanAnnulus := outerAnnulus r hr R with hAdef
  have hAc : A.center = 0 := rfl
  have hAin : A.innerRadius = 2 * r := rfl
  have hAout : A.outerRadius = (R : ℝ) := rfl
  set K : Set ℂ := Metric.closedBall 0 (R : ℝ) with hKdef
  have hK : IsCompact K := isCompact_closedBall 0 _
  
  obtain ⟨δ₁, hδ₁, -, hGosc⟩ := eventual_compact_oscillation hG hK f fn (hfn K hK) hθ
  
  obtain ⟨c₀, hc₀, hctrl⟩ := exists_uniform_euclidean_control D hDlen hDforget hK one_pos
  set K' : Set ℂ := Metric.closedBall 0 ((R : ℝ) + 1) with hK'def
  obtain ⟨δ₂, hδ₂, hDosc⟩ :=
    compact_oscillation D f (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 1)) hθ
  obtain ⟨c₁, -, hc₁pos, hc₁⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc₀
  have hc₁' : 0 < c₁ := ENNReal.ofReal_pos.1 hc₁pos
  set δ : ℝ := min δ₁ (min (δ₂ / 2) (c₁ / 2)) with hδdef
  have hδ : 0 < δ := lt_min hδ₁ (lt_min (half_pos hδ₂) (half_pos hc₁'))
  have hδδ₁ : δ ≤ δ₁ := min_le_left _ _
  have hδδ₂ : 2 * δ ≤ δ₂ := by
    have h1 := min_le_right δ₁ (min (δ₂ / 2) (c₁ / 2))
    have h2 := min_le_left (δ₂ / 2) (c₁ / 2)
    linarith
  have hδc₁ : 2 * δ ≤ c₁ := by
    have h1 := min_le_right δ₁ (min (δ₂ / 2) (c₁ / 2))
    have h2 := min_le_right (δ₂ / 2) (c₁ / 2)
    linarith
  
  set N : ℕ := ⌈Λ / δ⌉₊ + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos _
  have hΛδ : Λ / (N : ℝ) ≤ δ := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hNpos]
    have h1 : Λ / δ ≤ (⌈Λ / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Λ / δ⌉₊ : ℝ) ≤ N := by
      simp only [hNdef, Nat.cast_add, Nat.cast_one]
      linarith
    have h3 : Λ / δ ≤ N := h1.trans h2
    rw [div_le_iff₀ hδ] at h3
    linarith
  
  have hp1 : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hp
  have hp2 : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp hp
  have hball1 : ∀ᶠ n in atTop, (p n).1 ∈ Metric.ball (0 : ℂ) (2 * r) :=
    hp1.eventually (Metric.isOpen_ball.mem_nhds (by simpa using hq1))
  have hball2 : ∀ᶠ n in atTop, (p n).2 ∈ Metric.ball (0 : ℂ) (2 * r) :=
    hp2.eventually (Metric.isOpen_ball.mem_nhds (by simpa using hq2))
  have hGacross := eventually_lt_acrossDist hG A hR
  have hall := hfreq.and_eventually (hball1.and (hball2.and (hGacross.and hGosc)))
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hall
  
  have hcurve : ∀ n, ∃ (P : ℝ → ℂ) (L : ℝ), (G (φ n)).IsCurve P 0 L ∧
      HasUnitSpeedOn ((G (φ n)).pt ∘ P) (Icc 0 L) ∧
      P 0 = (p (φ n)).1 ∧ P L = (p (φ n)).2 ∧
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * fn (φ n) (P t))) <
        weylScale ξ (fn (φ n)) (G (φ n)) ((p (φ n)).1, (p (φ n)).2) +
          ENNReal.ofReal η := by
    intro n
    apply exists_near_min_weyl_curve _ ξ _ _ _ _ hη
    rw [Prod.mk.eta]
    exact ((hφP n).1.trans ENNReal.ofReal_lt_top).ne
  choose P L hP hu hP0 hPL hcost using hcurve
  have hcostB : ∀ n, (∫⁻ t in Icc 0 (L n),
      ENNReal.ofReal (Real.exp (ξ * fn (φ n) (P n t)))) <
        ENNReal.ofReal B + ENNReal.ofReal η := by
    intro n
    refine (hcost n).trans_le ?_
    rw [Prod.mk.eta]
    exact add_le_add (hφP n).1.le le_rfl
  
  have hLΛ : ∀ n, L n ≤ Λ := by
    intro n
    have hb := (unitSpeed_weyl_cost_bounds (G (φ n)) ξ hξ (fn (φ n)) (hGforget _)
      (hP n) (hu n) (-M) M
      (fun t _ => (abs_le.1 (hfnM (φ n) (P n t))).1)
      (fun t _ => (abs_le.1 (hfnM (φ n) (P n t))).2)).1
    rw [len_eq_ofReal_of_unitSpeed _ (hP n).1 (hu n)] at hb
    have hBη : ENNReal.ofReal B + ENNReal.ofReal η ≤ ENNReal.ofReal (B + 1) := by
      rw [← ENNReal.ofReal_add hB.le hη.le]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have h1 := (hb.trans_lt (hcostB n)).trans_le hBη
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_lt_ofReal_iff (by linarith)] at h1
    have h2 := mul_lt_mul_of_pos_left h1 (Real.exp_pos (ξ * M))
    have h3 : Real.exp (ξ * M) * (Real.exp (ξ * -M) * L n) = L n := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [h3] at h2
    exact h2.le
  
  have hPK : ∀ n, ∀ t ∈ Icc 0 (L n), P n t ∈ K := by
    intro n t ht
    have hc := continuousOn_of_isCurve_of_forget _ (hGforget (φ n)) (hP n)
    have ha : dist (P n 0) A.center ≤ A.innerRadius := by
      rw [hP0 n, hAc, hAin]
      exact (Metric.mem_ball.1 (hφP n).2.1).le
    have hlen : (G (φ n)).len (P n) 0 (L n) < acrossDist (G (φ n)) A := by
      rw [len_eq_ofReal_of_unitSpeed _ (hP n).1 (hu n)]
      exact (ENNReal.ofReal_le_ofReal (hLΛ n)).trans_lt (hφP n).2.2.2.1
    have hmem := curve_mem_ball_of_len_lt_acrossDist (G (φ n)) A hc ha hlen t ht
    rw [hAc, hAout] at hmem
    exact Metric.ball_subset_closedBall hmem
  
  have hosc : ∀ n, ∀ u ∈ K, ∀ v ∈ K, G (φ n) (u, v) ≤ ENNReal.ofReal δ →
      |fn (φ n) u - fn (φ n) v| < θ :=
    fun n u hu v hv huv =>
      (hφP n).2.2.2.2 u hu v hv (huv.trans (ENNReal.ofReal_le_ofReal hδδ₁))
  have hgrid := fun n => uniformGrid_props (G (φ n)) (hP n) (hu n) hN (hLΛ n) hΛδ
  set v : ℕ → Fin (N + 1) → ℂ := fun n i => P n (uniformGrid (L n) N i) with hvdef
  have hvK : ∀ n i, v n i ∈ K := fun n i =>
    hPK n _ ((hgrid n).2.2.2.1 i (Nat.lt_succ_iff.1 i.isLt))
  have hchain : ∀ n, (∑ j ∈ Finset.range N,
      chainWeightMinus ξ (fn (φ n)) θ (P n (uniformGrid (L n) N j)) *
        G (φ n) (P n (uniformGrid (L n) N j), P n (uniformGrid (L n) N (j + 1)))) ≤
      ∫⁻ s in Icc 0 (L n), ENNReal.ofReal (Real.exp (ξ * fn (φ n) (P n s))) :=
    fun n => uniformGrid_weighted_chain_le_cost (G (φ n)) ξ hξ (fn (φ n)) (hGforget _)
      (hosc n) (hP n) (hu n) (hPK n) hN (hLΛ n) hΛδ
  have hstep : ∀ n, ∀ j < N, G (φ n) (P n (uniformGrid (L n) N j),
      P n (uniformGrid (L n) N (j + 1))) ≤ ENNReal.ofReal δ := by
    intro n j hj
    exact (LSCMetric.apply_le_len _ _ ((hgrid n).1 (Nat.le_succ j))).trans
      ((hgrid n).2.2.2.2 j hj)
  
  have hGφ : Tendsto (fun n => G (φ n)) atTop (𝓝 D) := hG.comp hφ.tendsto_atTop
  have hfnφ : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ K, |fn (φ n) x - f x| < ε :=
    fun ε hε => hφ.tendsto_atTop.eventually (hfn K hK ε hε)
  obtain ⟨χ, wl, hχ, hwK, hconv, hsum⟩ :=
    finiteChain_weighted_liminf_shift hGφ hK ξ θ f (fun n => fn (φ n)) hfnφ N v hvK
  have hφχ : StrictMono (fun n => φ (χ n)) := hφ.comp hχ
  have hsumB : (∑ j : Fin N, chainWeightMinus ξ f θ (wl (chainLeft N j)) *
      D (wl (chainLeft N j), wl (chainRight N j))) ≤
        ENNReal.ofReal B + ENNReal.ofReal η := by
    refine hsum.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
    have hfin := Fin.sum_univ_eq_sum_range (fun j =>
      chainWeightMinus ξ (fn (φ (χ n))) θ (P (χ n) (uniformGrid (L (χ n)) N j)) *
        G (φ (χ n)) (P (χ n) (uniformGrid (L (χ n)) N j),
          P (χ n) (uniformGrid (L (χ n)) N (j + 1)))) N
    exact (le_of_eq hfin).trans ((hchain (χ n)).trans (hcostB (χ n)).le)
  
  have hw0 : wl ⟨0, Nat.zero_lt_succ N⟩ = q.1 := by
    have h2 : Tendsto (fun n => v (χ n) ⟨0, Nat.zero_lt_succ N⟩) atTop (𝓝 q.1) := by
      have heq : (fun n => v (χ n) ⟨0, Nat.zero_lt_succ N⟩) =
          fun n => (p (φ (χ n))).1 := by
        funext n
        simp only [hvdef]
        rw [(hgrid (χ n)).2.1, hP0]
      rw [heq]
      exact hp1.comp hφχ.tendsto_atTop
    exact tendsto_nhds_unique (hconv _) h2
  have hwN : wl ⟨N, Nat.lt_succ_self N⟩ = q.2 := by
    have h2 : Tendsto (fun n => v (χ n) ⟨N, Nat.lt_succ_self N⟩) atTop (𝓝 q.2) := by
      have heq : (fun n => v (χ n) ⟨N, Nat.lt_succ_self N⟩) =
          fun n => (p (φ (χ n))).2 := by
        funext n
        simp only [hvdef]
        rw [(hgrid (χ n)).2.2.1, hPL]
      rw [heq]
      exact hp2.comp hφχ.tendsto_atTop
    exact tendsto_nhds_unique (hconv _) h2
  
  have hDstep : ∀ j : Fin N, D (wl (chainLeft N j), wl (chainRight N j)) ≤
      ENNReal.ofReal δ := by
    intro j
    have hGφχ : Tendsto (fun n => G (φ (χ n))) atTop (𝓝 D) :=
      hG.comp hφχ.tendsto_atTop
    have hpair : Tendsto (fun n => (v (χ n) (chainLeft N j), v (χ n) (chainRight N j)))
        atTop (𝓝 (wl (chainLeft N j), wl (chainRight N j))) :=
      (hconv _).prodMk_nhds (hconv _)
    refine ((LSCMetric.tendsto_iff.1 hGφχ).1 _ _ hpair).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
    exact hstep (χ n) j j.isLt
  
  have hDloc : ∀ j : Fin N, ∀ η' : ℝ, 0 < η' → η' ≤ δ →
      weylScale ξ f D (wl (chainLeft N j), wl (chainRight N j)) ≤
        ENNReal.ofReal (Real.exp (ξ * (f (wl (chainLeft N j)) + θ))) *
          (D (wl (chainLeft N j), wl (chainRight N j)) + ENNReal.ofReal η') := by
    intro j η' hη' hη'δ
    have huK : wl (chainLeft N j) ∈ K := hwK _
    have hfin : D (wl (chainLeft N j), wl (chainRight N j)) < ⊤ :=
      (hDstep j).trans_lt ENNReal.ofReal_lt_top
    refine weylScale_le_exp_mul_of_local ξ hξ f D hDlen hfin hη' ?_
    intro x hx
    have h2δ : D (wl (chainLeft N j), x) < ENNReal.ofReal (2 * δ) := by
      refine hx.trans_le ?_
      calc D (wl (chainLeft N j), wl (chainRight N j)) + ENNReal.ofReal η'
          ≤ ENNReal.ofReal δ + ENNReal.ofReal δ :=
            add_le_add (hDstep j) (ENNReal.ofReal_le_ofReal hη'δ)
        _ = ENNReal.ofReal (2 * δ) := by
            rw [← ENNReal.ofReal_add hδ.le hδ.le]
            ring_nf
    have hux : dist (wl (chainLeft N j)) x < 1 :=
      hctrl _ huK x (h2δ.trans ((ENNReal.ofReal_le_ofReal hδc₁).trans_lt hc₁))
    have hu0 : dist (wl (chainLeft N j)) 0 ≤ (R : ℝ) := Metric.mem_closedBall.1 huK
    have huK' : wl (chainLeft N j) ∈ K' := Metric.mem_closedBall.2 (by linarith)
    have hxK' : x ∈ K' := by
      rw [Metric.mem_closedBall]
      have := dist_triangle x (wl (chainLeft N j)) 0
      rw [dist_comm x (wl (chainLeft N j))] at this
      linarith
    have hosc' := hDosc _ huK' x hxK' (h2δ.le.trans (ENNReal.ofReal_le_ofReal hδδ₂))
    have := (abs_sub_lt_iff.1 hosc').2
    linarith
  
  have hchainD := weylScale_chain_le_sum D ξ f hDforget N wl
  rw [hw0, hwN, Prod.mk.eta] at hchainD
  set C : ℝ≥0∞ := ∑ j : Fin N,
    ENNReal.ofReal (Real.exp (ξ * (f (wl (chainLeft N j)) + θ))) with hCdef
  have hC : C ≠ ⊤ := by
    rw [hCdef]
    exact ENNReal.sum_ne_top.2 fun j _ => ENNReal.ofReal_ne_top
  refine le_of_forall_small_add_mul hC hδ fun η' hη' hη'δ => ?_
  calc weylScale ξ f D q
      ≤ ∑ j : Fin N, weylScale ξ f D (wl (chainLeft N j), wl (chainRight N j)) := hchainD
    _ ≤ ∑ j : Fin N, ENNReal.ofReal (Real.exp (ξ * (f (wl (chainLeft N j)) + θ))) *
          (D (wl (chainLeft N j), wl (chainRight N j)) + ENNReal.ofReal η') :=
        Finset.sum_le_sum fun j _ => hDloc j η' hη' hη'δ
    _ = ENNReal.ofReal (Real.exp (2 * ξ * θ)) *
          (∑ j : Fin N, chainWeightMinus ξ f θ (wl (chainLeft N j)) *
            D (wl (chainLeft N j), wl (chainRight N j))) + ENNReal.ofReal η' * C := by
        rw [hCdef, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ofReal_exp_shift]
        simp only [chainWeightMinus]
        ring
    _ ≤ ENNReal.ofReal (Real.exp (2 * ξ * θ)) * (ENNReal.ofReal B + ENNReal.ofReal η) +
          ENNReal.ofReal η' * C := by
        gcongr

 





theorem weyl_gamma_liminf
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (M : ℝ) (hfnM : ∀ n z, |fn n z| ≤ M)
    (hGforget : ∀ n, Continuous (euclidForget (G n)))
    (hDlen : D.IsLengthSpace) (hDforget : Continuous (euclidForget D))
    (hacross : AcrossUnbounded D)
    {p : ℕ → ℂ × ℂ} {q : ℂ × ℂ} (hp : Tendsto p atTop (𝓝 q)) :
    weylScale ξ f D q ≤ liminf (fun n => weylScale ξ (fn n) (G n) (p n)) atTop := by
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨B, hB0, hlt, hBc⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc
  obtain ⟨B', -, hBB', hB'c⟩ := ENNReal.lt_iff_exists_real_btwn.1 hBc
  have hBpos : 0 < B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · subst h
      simp at hlt
  have hBB'r : B < B' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hB0).1 hBB'
  have hfreq : ∃ᶠ n in atTop, weylScale ξ (fn n) (G n) (p n) < ENNReal.ofReal B :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
  set η : ℝ := min 1 ((B' - B) / 2) with hηdef
  have hη : 0 < η := lt_min one_pos (by linarith)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hBη : B + η < B' := by
    have := min_le_right 1 ((B' - B) / 2)
    linarith
  have hcont : Continuous (fun θ : ℝ => Real.exp (2 * ξ * θ) * (B + η)) := by
    fun_prop
  have hev : ∀ᶠ θ in 𝓝 (0 : ℝ), Real.exp (2 * ξ * θ) * (B + η) < B' :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hBη)
  obtain ⟨θ, hθ1, hθ2⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).and
      self_mem_nhdsWithin).exists
  have hcore := weyl_gamma_liminf_core hG ξ hξ f fn hfn M hfnM hGforget hDlen
    hDforget hacross hp hθ2 hBpos hη hη1 hfreq
  refine hcore.trans_lt ?_
  rw [← ENNReal.ofReal_add hBpos.le hη.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hθ1).trans hB'c

end SupercriticalLQGUniqueness.B2.PfeWeyl
