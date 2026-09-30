import QuantumZipper.Proofs.Thm18.G1SideFamExt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (4): the two-parameter dilation family of the reflected side map

Deterministic input of `G1Side.ae_wedge_transport_family`. From reflection data
`SideReflGood left ψ Φ` (Ahlfors, *Complex Analysis*, Ch. 4 §6.5, used only through
`SideReflGood`), with `ψ(ℍ) ⊆ ℍ`, a compact window `[p, q]` of the side half-line and `N ≥ 1`,
`exists_dilFamily` produces rational class constants, a Lipschitz retraction onto the box
`K = {s | s 0 ∈ [1/N, N], s 1 ∈ [1, 2]}` and a separation constant, such that the family
`Ψ s z = s₀ · Ψe (s₁ z)` (`Ψe` the holomorphic extension) satisfies every family hypothesis of
`ae_wedge_transport_family`, agrees with `s₀ · ψ (s₁ ·)` on `ℍ`, and has boundary values
`s₀ Φ (s₁ t)`. Own elementary bookkeeping.
-/

noncomputable section

open Set Metric Function
open scoped Topology NNReal

namespace QuantumZipper
namespace G1Side

open SWCore Thm18Asm

/-- The box of parameters `(s₀, s₁) ∈ [1/N, N] × [1, 2]`. -/
def dilBox (N : ℕ) : Set (Fin 2 → ℝ) := {s | s 0 ∈ Icc (1 / (N : ℝ)) N ∧ s 1 ∈ Icc 1 2}

/-- The dilation family `z ↦ s₀ · Ψe (s₁ z)`. -/
def dilFam (Ψe : ℂ → ℂ) (s : Fin 2 → ℝ) (z : ℂ) : ℂ := (s 0 : ℂ) * Ψe ((s 1 : ℂ) * z)

/-- The coordinatewise clamp onto `dilBox N`. -/
def dilRetr (N : ℕ) (s : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![max (1 / (N : ℝ)) (min N (s 0)), max 1 (min 2 (s 1))]

theorem dilRetr_mem {N : ℕ} (hN : 1 ≤ N) (s : Fin 2 → ℝ) : dilRetr N s ∈ dilBox N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 1 / (N : ℝ) ≤ N := (div_le_one_of_le₀ hN' (by linarith)).trans hN'
  simp only [dilBox, dilRetr, mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    mem_Icc]
  refine ⟨⟨le_max_left _ _, max_le h1 (min_le_left _ _)⟩, ⟨le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩⟩

theorem dilRetr_id {N : ℕ} {s : Fin 2 → ℝ} (hs : s ∈ dilBox N) : dilRetr N s = s := by
  ext i
  fin_cases i
  · simp [dilRetr, min_eq_right hs.1.2]; simpa using hs.1.1
  · simp [dilRetr, min_eq_right hs.2.2, max_eq_right hs.2.1]

theorem dilRetr_lipschitz (N : ℕ) : LipschitzWith 1 (dilRetr N) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  have key : ∀ (l h u v : ℝ), dist (max l (min h u)) (max l (min h v)) ≤ dist u v := by
    intro l h u v
    rw [Real.dist_eq, Real.dist_eq, max_comm l, max_comm l]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    refine (abs_min_sub_min_le_max h u h v).trans ?_
    simp
  intro i
  fin_cases i
  · exact (key _ _ _ _).trans (dist_le_pi_dist x y 0)
  · exact (key _ _ _ _).trans (dist_le_pi_dist x y 1)

theorem dilBox_norm_le {N : ℕ} {s : Fin 2 → ℝ} (hs : s ∈ dilBox N) : ‖s‖ ≤ N + 2 := by
  have h0 : (0 : ℝ) ≤ 1 / N := by positivity
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  fin_cases i
  · exact ⟨by simp; linarith [hs.1.1], by simp; linarith [hs.1.2]⟩
  · exact ⟨by simp; linarith [hs.2.1], by simp; linarith [hs.2.2]⟩

theorem isCompact_dilBox (N : ℕ) : IsCompact (dilBox N) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_Icc.preimage (continuous_apply 0)).inter
      (isClosed_Icc.preimage (continuous_apply 1))
  · exact isBounded_iff_forall_norm_le.2 ⟨N + 2, fun s hs => dilBox_norm_le hs⟩

set_option maxHeartbeats 1000000 in
/-- **The dilation family of the reflected side map satisfies the family hypotheses of
`ae_wedge_transport_family`.** -/
theorem exists_dilFamily {left : Bool} {ψ : ℂ → ℂ} {Φ : ℝ ≃o ℝ} (hR : SideReflGood left ψ Φ)
    (hH : ∀ z ∈ H, ψ z ∈ H) {p q : ℝ} (hpq : p < q) (hsub : Icc p q ⊆ g1SideHalf left)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (Ψe : ℂ → ℂ) (a b ρ M m : ℚ) (L R c₀ : ℝ),
      (a : ℝ) < p ∧ q < (b : ℝ) ∧ Icc (a : ℝ) b ⊆ g1SideHalf left ∧
      (∀ c ∈ Icc (1 : ℝ) 2, ∀ t ∈ Icc (a : ℝ) b,
        c * t ∈ g1SideHalf left ∧ Ψe ((c * t : ℝ) : ℂ) = (Φ (c * t) : ℂ)) ∧
      EqOn ψ Ψe H ∧
      (a : ℝ) < b ∧ (0 : ℝ) < ρ ∧ (0 : ℝ) < m ∧ 0 ≤ L ∧
      (∀ s ∈ dilBox N, dilFam Ψe s ∈ BdryClass a b ρ M m) ∧
      (∀ s ∈ dilBox N, ∀ s' ∈ dilBox N, ∀ z ∈ thickening (ρ : ℝ) (segC a b),
        ‖dilFam Ψe s z - dilFam Ψe s' z‖ ≤ L * ‖s - s'‖) ∧
      LipschitzWith 1 (dilRetr N) ∧ (∀ s, dilRetr N s ∈ dilBox N) ∧
      (∀ s ∈ dilBox N, dilRetr N s = s) ∧
      0 ≤ R ∧ (∀ s ∈ dilBox N, ‖s‖ ≤ R) ∧ IsCompact (dilBox N) ∧ 0 < c₀ ∧
      (∀ s ∈ dilBox N, ∀ z ∈ thickening (ρ : ℝ) (segC a b), c₀ ≤ ‖dilFam Ψe s z‖) ∧
      (∀ s ∈ dilBox N, ∀ z ∈ thickening (ρ : ℝ) (segC a b), z ∈ Hbar → dilFam Ψe s z ∈ Hbar) ∧
      (∀ s ∈ dilBox N, EqOn (dilFam Ψe s) (fun z => (s 0 : ℂ) * ψ ((s 1 : ℂ) * z)) H) ∧
      (∀ s ∈ dilBox N, ∀ t ∈ Icc (a : ℝ) b, dilFam Ψe s t = ((s 0 * Φ (s 1 * t) : ℝ) : ℂ)) := by
  obtain ⟨e, he, hEs⟩ := exists_side_margin hpq hsub
  have hE : min (p - e) (2 * (p - e)) < max (q + e) (2 * (q + e)) :=
    (min_le_left _ _).trans_lt (lt_of_lt_of_le (by linarith) (le_max_left _ _))
  obtain ⟨Ψe, ρ₀, M₀, m₀, c₁, hρ₀, hM₀, hm₀, hc₁, hcl0, hsep0, heq, hreal⟩ :=
    sideExt_class hR hE hEs
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show p - e / 2 < p by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show q < q + e / 2 by linarith)
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_rat_btwn (show (0 : ℝ) < min (ρ₀ / 4) (e / 2) by positivity)
  have hρ4 : 4 * (ρ : ℝ) ≤ ρ₀ := by linarith [min_le_left (ρ₀ / 4) (e / 2)]
  have hρe : (ρ : ℝ) < e / 2 := lt_of_lt_of_le hρ2 (min_le_right _ _)
  set Nr : ℝ := (N : ℝ) with hNr
  have hN1 : (1 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast hN
  have hN0 : 0 < Nr := by linarith
  obtain ⟨m, hm1, hm2⟩ := exists_rat_btwn (show (0 : ℝ) < m₀ / Nr by positivity)
  obtain ⟨M, hM⟩ := exists_rat_gt (Nr * M₀)
  have hab : (a : ℝ) < b := by linarith
  have hwin : ∀ t ∈ Icc (a : ℝ) b, t ∈ Icc (p - e) (q + e) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hin : ∀ c ∈ Icc (1 : ℝ) 2, ∀ t ∈ Icc (a : ℝ) b,
      c * t ∈ Icc (min (p - e) (2 * (p - e))) (max (q + e) (2 * (q + e))) :=
    fun c hc t ht => dil_mem_window hc (hwin t ht)
  have hthk : ∀ s ∈ dilBox N, ∀ z ∈ thickening (ρ : ℝ) (segC a b),
      (s 1 : ℂ) * z ∈ thickening ρ₀ (segC (min (p - e) (2 * (p - e)))
        (max (q + e) (2 * (q + e)))) := fun s hs z hz =>
    thickening_mono (by linarith) _ (dil_mem_thick hs.2 (hin _ hs.2) hz)
  have hs0 : ∀ s ∈ dilBox N, 0 < s 0 := fun s hs =>
    lt_of_lt_of_le (by positivity) hs.1.1
  set L : ℝ := M₀ + Nr * (4 * M₀ / ρ₀ * (|(a : ℝ)| + |(b : ℝ)| + ρ)) with hL
  refine ⟨Ψe, a, b, ρ, M, m, L, Nr + 2, c₁ / Nr, by linarith, by linarith,
    fun t ht => hEs (by simpa using hin 1 ⟨le_rfl, by norm_num⟩ t ht),
    fun c hc t ht => ⟨hEs (hin c hc t ht), hreal _ (hin c hc t ht)⟩, heq, hab, hρ1, hm1,
    by positivity, ?_, ?_, dilRetr_lipschitz N, dilRetr_mem hN, fun s hs => dilRetr_id hs,
    by positivity, fun s hs => dilBox_norm_le hs, isCompact_dilBox N, by positivity,
    ?_, ?_, ?_, ?_⟩
  · -- class membership
    intro s hs
    have h1 := dil_mem_class hcl0 (ρ' := ρ) hρ1 (by linarith) hs.2 (hin _ hs.2) hm₀.le
    have h2 := const_mul_mem_class h1 hρ1 hm₀.le hN0 hs.1.1 hs.1.2
    exact ⟨h2.1, fun z hz => (h2.2.1 z hz).trans hM.le, h2.2.2.1, h2.2.2.2.1,
      fun t ht => hm2.le.trans (h2.2.2.2.2 t ht)⟩
  · -- Lipschitz in the parameters
    intro s hs s' hs' z hz
    have e1 : dilFam Ψe s z - dilFam Ψe s' z = ((s 0 - s' 0 : ℝ) : ℂ) * Ψe ((s 1 : ℂ) * z) +
        (s' 0 : ℂ) * (Ψe ((s 1 : ℂ) * z) - Ψe ((s' 1 : ℂ) * z)) := by
      simp only [dilFam]; push_cast; ring
    have hb := hcl0.2.1 _ (hthk s hs z hz)
    have hl := dil_lipschitz hcl0 hρ₀ hρ1 hρ4 (fun c hc t ht => hin c hc t ht) hs.2 hs'.2 hz
    have hzn := norm_le_of_mem_thick_segC hz
    have c0 := abs_coord_le_norm' s s' 0
    have c1 := abs_coord_le_norm' s s' 1
    have hK0 : 0 ≤ 4 * M₀ / ρ₀ := by positivity
    have hs'0 := hs0 s' hs'
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hs'0]
    have t1 : |s 0 - s' 0| * ‖Ψe ((s 1 : ℂ) * z)‖ ≤ ‖s - s'‖ * M₀ :=
      mul_le_mul c0 hb (norm_nonneg _) (norm_nonneg _)
    have t2 : ‖Ψe ((s 1 : ℂ) * z) - Ψe ((s' 1 : ℂ) * z)‖ ≤
        4 * M₀ / ρ₀ * (|(a : ℝ)| + |(b : ℝ)| + ρ) * ‖s - s'‖ :=
      hl.trans (mul_le_mul (mul_le_mul_of_nonneg_left hzn hK0) c1 (abs_nonneg _)
        (mul_nonneg hK0 (by positivity)))
    have t3 : s' 0 * ‖Ψe ((s 1 : ℂ) * z) - Ψe ((s' 1 : ℂ) * z)‖ ≤
        Nr * (4 * M₀ / ρ₀ * (|(a : ℝ)| + |(b : ℝ)| + ρ) * ‖s - s'‖) :=
      mul_le_mul hs'.1.2 t2 (norm_nonneg _) hN0.le
    calc _ ≤ ‖s - s'‖ * M₀ + Nr * (4 * M₀ / ρ₀ * (|(a : ℝ)| + |(b : ℝ)| + ρ) * ‖s - s'‖) :=
          add_le_add t1 t3
      _ = L * ‖s - s'‖ := by rw [hL]; ring
  · -- separation from `0`
    intro s hs z hz
    have h := hsep0 _ (hthk s hs z hz)
    simp only [dilFam]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs0 s hs)]
    calc c₁ / Nr = 1 / Nr * c₁ := by ring
      _ ≤ s 0 * ‖Ψe ((s 1 : ℂ) * z)‖ := mul_le_mul hs.1.1 h hc₁.le (hs0 s hs).le
  · -- `Hbar` is preserved
    intro s hs z hz hzH
    have hs1 : 0 < s 1 := by linarith [hs.2.1]
    have hzH' : 0 ≤ z.im := hzH
    show 0 ≤ (dilFam Ψe s z).im
    rcases hzH'.lt_or_eq with hpos | hzero
    · have hw : (s 1 : ℂ) * z ∈ H := by
        show 0 < ((s 1 : ℂ) * z).im
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        exact mul_pos hs1 hpos
      have hψw : 0 < (ψ ((s 1 : ℂ) * z)).im := hH _ hw
      simp only [dilFam, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero]
      rw [← heq hw]
      exact (mul_pos (hs0 s hs) hψw).le
    · obtain ⟨_, ⟨t, ht, rfl⟩, hzt⟩ := mem_thickening_iff.1 hz
      have hre : |z.re - t| < ρ := by
        have := Complex.abs_re_le_norm (z - t)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        rw [dist_eq_norm] at hzt
        linarith
      have hzr : z.re ∈ Icc (p - e) (q + e) := by
        rw [abs_lt] at hre
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      rw [hz']
      simp only [dilFam]
      rw [← Complex.ofReal_mul, hreal _ (dil_mem_window hs.2 hzr)]
      simp
  · -- agreement with `ψ` on `ℍ`
    intro s hs z hz
    have hs1 : 0 < s 1 := by linarith [hs.2.1]
    have hw : (s 1 : ℂ) * z ∈ H := by
      show 0 < ((s 1 : ℂ) * z).im
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos hs1 hz
    simp only [dilFam]
    rw [heq hw]
  · -- boundary values
    intro s hs t ht
    simp only [dilFam]
    rw [← Complex.ofReal_mul, hreal _ (hin _ hs.2 t ht)]
    push_cast
    ring

end G1Side
end QuantumZipper
