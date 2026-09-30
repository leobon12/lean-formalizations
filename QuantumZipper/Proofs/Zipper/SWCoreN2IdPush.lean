import QuantumZipper.Proofs.Zipper.SWCoreN2IdFam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2-ID (2): the pushed semicircle family of a Lipschitz family of class maps

Task SWC-N2-ID. Setting: `Ψ : ℝⁿ → ℂ → ℂ` with `Ψ q ∈ BdryClass a b ρ M m` for `q ∈ K` and
`‖Ψ q z − Ψ q' z‖ ≤ L ‖q − q'‖` on the `ρ`-thickening of `[a,b]`, and a Lipschitz retraction
`π : ℝⁿ → K` (e.g. the coordinatewise clamp onto a box). For small `r`, the family
`(q, t) ↦ fc(t, r).map (Ψ q)` (`t` clamped to `[a − r, b + r]`, `q` retracted to `K`) is bounded,
`1`-Frostman (the class maps are co-Lipschitz on `B(s₀, 2r)`, `swcv_ball_facts`) and Lipschitz in
`(q,t)`, so `swcN2_ae_evalReg` applies: a.s. `(q,t) ↦ evalReg x (fc(t,r).map (Ψ q))` is continuous
on `K × [a − r, b + r]`, and equals the raw value for each fixed `(q,t)` (`swcN2_push_ae`).
Sources as in `SWCoreN2IdFam.lean`; own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open Thm18Asm.G1RC

/-- The clamp of `t` to `[lo, hi]`. -/
def swcN2Clamp (lo hi t : ℝ) : ℝ := max lo (min hi t)

theorem swcN2Clamp_lip (lo hi t t' : ℝ) :
    |swcN2Clamp lo hi t - swcN2Clamp lo hi t'| ≤ |t - t'| := by
  unfold swcN2Clamp
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (abs_nonneg _) ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  exact max_le (abs_nonneg _) le_rfl

theorem swcN2Clamp_mem {lo hi : ℝ} (h : lo ≤ hi) (t : ℝ) : swcN2Clamp lo hi t ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem swcN2Clamp_of_mem {lo hi t : ℝ} (ht : t ∈ Icc lo hi) : swcN2Clamp lo hi t = t := by
  unfold swcN2Clamp; rw [min_eq_right ht.2, max_eq_right ht.1]

theorem continuous_swcN2Clamp (lo hi : ℝ) : Continuous (swcN2Clamp lo hi) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem swcN2Clamp_near {a b r u : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) (hu : u ∈ Icc (a - r) (b + r)) :
    |u - swcN2Clamp a b u| ≤ r := by
  have h1 := hu.1; have h2 := hu.2
  unfold swcN2Clamp
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

variable {n : ℕ}

/-- Joint continuity of a Lipschitz-in-the-parameter family of maps continuous in `z`. -/
theorem swcN2_continuousOn_family {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)} {T : Set ℂ}
    {L : ℝ} (hc : ∀ q ∈ K, ContinuousOn (Ψ q) T)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ T, ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖) :
    ContinuousOn (fun x : (Fin n → ℝ) × ℂ => Ψ x.1 x.2) (K ×ˢ T) := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun y : (Fin n → ℝ) × ℂ => L * ‖y.1 - x.1‖) (𝓝[K ×ˢ T] x) (𝓝 0) := by
    have : Tendsto (fun y : (Fin n → ℝ) × ℂ => L * ‖y.1 - x.1‖) (𝓝 x)
        (𝓝 (L * ‖x.1 - x.1‖)) :=
      (((continuous_fst.sub continuous_const).norm).const_mul L).tendsto x
    rw [sub_self, norm_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun y : (Fin n → ℝ) × ℂ => ‖Ψ x.1 y.2 - Ψ x.1 x.2‖) (𝓝[K ×ˢ T] x)
      (𝓝 0) := by
    have := ((hc x.1 hx.1).comp continuous_snd.continuousOn
      (fun y hy => (mem_prod.1 hy).2)) x hx
    exact tendsto_iff_norm_sub_tendsto_zero.1 this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using h1.add h2)
  filter_upwards [self_mem_nhdsWithin] with y hy
  calc ‖Ψ y.1 y.2 - Ψ x.1 x.2‖ = ‖(Ψ y.1 y.2 - Ψ x.1 y.2) + (Ψ x.1 y.2 - Ψ x.1 x.2)‖ := by
        ring_nf
    _ ≤ ‖Ψ y.1 y.2 - Ψ x.1 y.2‖ + ‖Ψ x.1 y.2 - Ψ x.1 x.2‖ := norm_add_le _ _
    _ ≤ L * ‖y.1 - x.1‖ + ‖Ψ x.1 y.2 - Ψ x.1 x.2‖ := by
        gcongr; exact hL _ hy.1 _ hx.1 _ hy.2

/-- The pushed semicircle family with parameters `(q, t)` (`q` retracted by `π`, `t` clamped). -/
def swcN2PushΦ (Ψ : (Fin n → ℝ) → ℂ → ℂ) (π : (Fin n → ℝ) → Fin n → ℝ) (a b r : ℝ) :
    (Fin (n + 1) → ℝ) → ℝ → ℂ := fun p θ =>
  Ψ (π (Fin.init p))
    (foldH (circleMap ((swcN2Clamp (a - r) (b + r) (p (Fin.last n)) : ℝ) : ℂ) r θ))

/-- Folded circle points around a clamped centre lie in `B(s₀, 2r)`, `s₀ ∈ [a,b]`. -/
theorem swcN2_fold_mem_ball2 {a b r u : ℝ} (hab : a ≤ b) (hr : 0 ≤ r)
    (hu : u ∈ Icc (a - r) (b + r)) (θ : ℝ) :
    foldH (circleMap (u : ℂ) r θ) ∈ closedBall ((swcN2Clamp a b u : ℝ) : ℂ) (2 * r) := by
  have h1 := swcN2_fold_circle_mem (s := u) hr θ
  have h2 := swcN2Clamp_near hab hr hu
  have h3 : dist (u : ℂ) ((swcN2Clamp a b u : ℝ) : ℂ) = |u - swcN2Clamp a b u| := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [mem_closedBall] at h1 ⊢
  linarith [dist_triangle (foldH (circleMap (u : ℂ) r θ)) (u : ℂ) ((swcN2Clamp a b u : ℝ) : ℂ)]

theorem swcN2_ball_sub_thick {a b ρ R s : ℝ} (hs : s ∈ Icc a b) (hR : R < ρ) :
    closedBall (s : ℂ) R ⊆ thickening ρ (segC a b) := fun z hz => by
  rw [mem_thickening_iff]
  exact ⟨(s : ℂ), ⟨s, hs, rfl⟩, lt_of_le_of_lt (mem_closedBall.1 hz) hR⟩

section Push

variable {a b ρ M m L : ℝ} {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)}
  {Kπ : ℝ≥0} {π : (Fin n → ℝ) → Fin n → ℝ}

set_option maxHeartbeats 800000 in
/-- **Box bounds of the pushed family** (input of `swcN2_ae_evalReg`), for all small `r`. -/
theorem swcN2_push_bounds (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m) (hL0 : 0 ≤ L)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ ∀ r ∈ Ioo 0 r₂,
      Continuous (uncurry (swcN2PushΦ Ψ π a b r)) ∧
      (∀ p θ, swcN2PushΦ Ψ π a b r p θ ∈ Hbar) ∧
      ∀ R : ℕ, ∃ B C H : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 ≤ H ∧ ∀ p ∈ KolmD.boxD (d := n + 1) R,
        (∀ θ, ‖swcN2PushΦ Ψ π a b r p θ‖ ≤ B) ∧
        TwoPoint.IsFrostman (circM.map (swcN2PushΦ Ψ π a b r p)) 1 C ∧
        ∀ p' ∈ KolmD.boxD (d := n + 1) R, ∀ θ,
          ‖swcN2PushΦ Ψ π a b r p θ - swcN2PushΦ Ψ π a b r p' θ‖ ≤ H * ‖p - p'‖ ^ (1 : ℝ) := by
  obtain ⟨r₁, hr₁, C₁, hC₁, hF⟩ := swcv_ball_facts a b ρ M m hab hρ hm
  refine ⟨min (r₁ / 3) (ρ / 3), lt_min (by linarith) (by linarith), fun r hr => ?_⟩
  have hr0 : 0 < r := hr.1
  have hr1 : 3 * r < r₁ := by have := lt_of_lt_of_le hr.2 (min_le_left _ _); linarith
  have hrρ : 3 * r < ρ := by have := lt_of_lt_of_le hr.2 (min_le_right _ _); linarith
  set Φ := swcN2PushΦ Ψ π a b r with hΦdef
  set T := thickening ρ (segC a b) with hT
  set U : ℝ → ℝ := swcN2Clamp (a - r) (b + r) with hU
  set g : ℝ → ℝ → ℂ := fun u θ => foldH (circleMap (u : ℂ) r θ) with hg
  have hUmem : ∀ t, U t ∈ Icc (a - r) (b + r) := fun t => swcN2Clamp_mem (by linarith) t
  have hs0 : ∀ t, swcN2Clamp a b (U t) ∈ Icc a b := fun t => swcN2Clamp_mem hab.le _
  have hg2 : ∀ t θ, g (U t) θ ∈ closedBall ((swcN2Clamp a b (U t) : ℝ) : ℂ) (2 * r) :=
    fun t θ => swcN2_fold_mem_ball2 hab.le hr0.le (hUmem t) θ
  have hgT : ∀ t θ, g (U t) θ ∈ T := fun t θ =>
    swcN2_ball_sub_thick (hs0 t) (by linarith) (hg2 t θ)
  have hΦeq : ∀ p θ, Φ p θ = Ψ (π (Fin.init p)) (g (U (p (Fin.last n))) θ) := fun _ _ => rfl
  have hB2 := fun q (hq : q ∈ K) t =>
    hF (Ψ q) (hΨ q hq) _ (hs0 t) (2 * r) ⟨by linarith, by linarith⟩
  have hB3 := fun q (hq : q ∈ K) t =>
    hF (Ψ q) (hΨ q hq) _ (hs0 t) (3 * r) ⟨by linarith, by linarith⟩
  have hcont : Continuous (uncurry Φ) := by
    have hin : Continuous fun x : (Fin (n + 1) → ℝ) × ℝ =>
        (π (Fin.init x.1), g (U (x.1 (Fin.last n))) x.2) := by
      refine (hπ.continuous.comp ((continuous_pi fun i => continuous_apply _).comp
        continuous_fst)).prodMk ?_
      have hu : Continuous fun x : (Fin (n + 1) → ℝ) × ℝ => ((U (x.1 (Fin.last n)) : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp ((continuous_swcN2Clamp _ _).comp
          ((continuous_apply _).comp continuous_fst))
      refine CircleFubini.continuous_foldH'.comp ?_
      simp only [circleMap]
      exact hu.add (continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))
    exact (swcN2_continuousOn_family (T := T) (fun q hq => (hΨ q hq).1.continuousOn)
      hL).comp_continuous hin (fun x => ⟨hπK _, hgT _ _⟩)
  have hΦc : ∀ p, Continuous (Φ p) := fun p =>
    hcont.comp (continuous_const.prodMk continuous_id)
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨hcont, fun p θ => ?_, fun R => ?_⟩
  · rw [hΦeq]
    exact (hB2 _ (hπK _) _).2.2 _ (hg2 _ _) (CircleFubini.foldH_mem_Hbar' _)
  refine ⟨max M 0, 12 / (m / 2 * r), L * Kπ + 2 * C₁ + 2 * max M 0 / r, hM0,
    by positivity, add_nonneg (add_nonneg (mul_nonneg hL0 Kπ.2) (by linarith))
      (by positivity), fun p _ => ⟨fun θ => ?_, ?_, fun p' _ θ => ?_⟩⟩
  · rw [hΦeq]; exact ((hΨ _ (hπK _)).2.1 _ (hgT _ _)).trans (le_max_left _ _)
  · refine swcN2_frostman (y := ((U (p (Fin.last n)) : ℝ) : ℂ)) hr0 (by positivity) (hΦc p).measurable fun θ θ' => ?_
    obtain ⟨⟨hmD, -⟩, hco, -⟩ := hB2 _ (hπK (Fin.init p)) (p (Fin.last n))
    have h1 := (hco _ (hg2 _ θ) _ (hg2 _ θ')).1
    rw [hΦeq, hΦeq]
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · set q := Fin.init p with hq
    set q' := Fin.init p' with hq'
    set u := U (p (Fin.last n)) with hu
    set u' := U (p' (Fin.last n)) with hu'
    have hδ : ‖q - q'‖ ≤ ‖p - p'‖ := swcNA2_norm_init_sub_le
    have hδt : |p (Fin.last n) - p' (Fin.last n)| ≤ ‖p - p'‖ := by
      have := norm_le_pi_norm (p - p') (Fin.last n); simpa using this
    have huu : |u - u'| ≤ ‖p - p'‖ := (swcN2Clamp_lip _ _ _ _).trans hδt
    have h1 : ‖Ψ (π q) (g u θ) - Ψ (π q') (g u θ)‖ ≤ L * Kπ * ‖p - p'‖ := by
      refine (hL _ (hπK _) _ (hπK _) _ (hgT _ _)).trans ?_
      have := hπ.dist_le_mul q q'
      rw [dist_eq_norm, dist_eq_norm] at this
      calc L * ‖π q - π q'‖ ≤ L * (Kπ * ‖q - q'‖) := mul_le_mul_of_nonneg_left this hL0
        _ ≤ L * (Kπ * ‖p - p'‖) := by gcongr
        _ = _ := by ring
    have h2 : ‖Ψ (π q') (g u θ) - Ψ (π q') (g u' θ)‖ ≤
        (2 * C₁ + 2 * max M 0 / r) * ‖p - p'‖ := by
      by_cases hc : |u - u'| ≤ r
      · have hw : ‖g u θ - g u' θ‖ ≤ |u - u'| := by
          have := swcN2_norm_fold_circle_sub (s := u) (s' := u') hr0 hr0 θ
          simpa using this
        obtain ⟨⟨-, hDC⟩, hlip, -⟩ := hB3 _ (hπK q') (p (Fin.last n))
        have hx : g u θ ∈ closedBall ((swcN2Clamp a b u : ℝ) : ℂ) (3 * r) :=
          closedBall_subset_closedBall (by linarith) (hg2 _ θ)
        have hy : g u' θ ∈ closedBall ((swcN2Clamp a b u : ℝ) : ℂ) (3 * r) := by
          have h3 := hg2 (p (Fin.last n)) θ
          rw [mem_closedBall] at h3 ⊢
          refine (dist_triangle _ (g u θ) _).trans ?_
          rw [dist_comm, dist_eq_norm]
          linarith
        have h4 := (hlip _ hx _ hy).2
        have h5 : 2 * (deriv (Ψ (π q')) (swcN2Clamp a b u)).re * ‖g u θ - g u' θ‖ ≤
            2 * C₁ * ‖p - p'‖ := by
          have := mul_le_mul hDC (hw.trans huu) (norm_nonneg _) hC₁
          linarith
        have h6 : 0 ≤ 2 * max M 0 / r * ‖p - p'‖ := by positivity
        nlinarith
      · push_neg at hc
        have e1 : ‖Ψ (π q') (g u θ)‖ ≤ max M 0 :=
          ((hΨ _ (hπK _)).2.1 _ (hgT _ _)).trans (le_max_left _ _)
        have e2 : ‖Ψ (π q') (g u' θ)‖ ≤ max M 0 :=
          ((hΨ _ (hπK _)).2.1 _ (hgT _ _)).trans (le_max_left _ _)
        have e3 : 2 * max M 0 ≤ 2 * max M 0 / r * ‖p - p'‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hr0]
          exact mul_le_mul_of_nonneg_left (hc.le.trans huu) (by linarith)
        have e4 : 0 ≤ 2 * C₁ * ‖p - p'‖ := by
          have := norm_nonneg (p - p'); nlinarith
        calc _ ≤ ‖Ψ (π q') (g u θ)‖ + ‖Ψ (π q') (g u' θ)‖ := norm_sub_le _ _
          _ ≤ 2 * max M 0 := by linarith
          _ ≤ _ := by nlinarith
    calc ‖Φ p θ - Φ p' θ‖ = ‖(Ψ (π q) (g u θ) - Ψ (π q') (g u θ)) +
          (Ψ (π q') (g u θ) - Ψ (π q') (g u' θ))‖ := by
          rw [hΦeq, hΦeq]; congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ L * Kπ * ‖p - p'‖ + (2 * C₁ + 2 * max M 0 / r) * ‖p - p'‖ := add_le_add h1 h2
      _ = _ := by rw [Real.rpow_one]; ring

/-- On `K × [a − r, b + r]` the pushed family is the pushed semicircle. -/
theorem swcN2_push_eq (hab : a ≤ b) {r : ℝ} (hr : 0 < r) (hrρ : 3 * r < ρ)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m) (hπid : ∀ q ∈ K, π q = q)
    {q : Fin n → ℝ} (hq : q ∈ K) {t : ℝ} (ht : t ∈ Icc (a - r) (b + r)) :
    circM.map (swcN2PushΦ Ψ π a b r (Fin.snoc q t : Fin (n + 1) → ℝ)) =
      (foldedCircle (t : ℂ) r).map (Ψ q) := by
  have hball : closedBall (t : ℂ) r ⊆ thickening ρ (segC a b) := by
    intro z hz
    refine swcN2_ball_sub_thick (swcN2Clamp_mem hab t) (R := 2 * r) (by linarith) ?_
    have h3 : dist (t : ℂ) ((swcN2Clamp a b t : ℝ) : ℂ) = |t - swcN2Clamp a b t| := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have := swcN2Clamp_near hab hr.le ht
    rw [mem_closedBall] at hz ⊢
    linarith [dist_triangle z (t : ℂ) ((swcN2Clamp a b t : ℝ) : ℂ)]
  rw [swcN2_fc_map_eq hr.le ((hΨ q hq).1.continuousOn.mono hball)]
  congr 1
  funext θ
  simp only [swcN2PushΦ, Fin.init_snoc, Fin.snoc_last, hπid q hq, swcN2Clamp_of_mem ht]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **(ii)+(iii) for the pushed family**: for all small `r`, a.s. the regularized pushed
semicircle average `(q,t) ↦ evalReg x (fc(t,r).map (Ψ q))` is continuous on `K × [a−r, b+r]`,
and for each `(q,t)` it equals the raw value `X(fc(t,r).map (Ψ q))` a.s. -/
theorem swcN2_push_ae (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m) (hL0 : 0 ≤ L)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q)
    (hX : IsFreeGFFModConstH X P) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ ∀ r ∈ Ioo 0 r₂,
      (∀ᵐ ω ∂P, ContinuousOn (fun x : (Fin n → ℝ) × ℝ =>
          evalReg (X ω) ((foldedCircle (x.2 : ℂ) r).map (Ψ x.1)))
          (K ×ˢ Icc (a - r) (b + r))) ∧
      ∀ q ∈ K, ∀ t ∈ Icc (a - r) (b + r), ∀ᵐ ω ∂P,
        evalReg (X ω) ((foldedCircle (t : ℂ) r).map (Ψ q)) =
          X ω ((foldedCircle (t : ℂ) r).map (Ψ q)) := by
  obtain ⟨r₂, hr₂, h⟩ := swcN2_push_bounds hab hρ hm hΨ hL0 hL hπ hπK
  refine ⟨min r₂ (ρ / 3), lt_min hr₂ (by linarith), fun r hr => ?_⟩
  have hr' : r ∈ Ioo 0 r₂ := ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
  have hrρ : 3 * r < ρ := by have := lt_of_lt_of_le hr.2 (min_le_right _ _); linarith
  obtain ⟨hc, hH, hb⟩ := h r hr'
  obtain ⟨hae, hpt⟩ := swcN2_ae_evalReg hc hH hb hX
  have hsnoc : Continuous fun x : (Fin n → ℝ) × ℝ => (Fin.snoc x.1 x.2 : Fin (n + 1) → ℝ) :=
    continuous_fst.finSnoc (A := fun _ => ℝ) continuous_snd
  refine ⟨?_, fun q hq t ht => ?_⟩
  · filter_upwards [hae] with ω hω
    refine ((hω.comp hsnoc).continuousOn).congr fun x hx => ?_
    simp only [comp_apply]
    rw [swcN2_push_eq hab.le hr.1 hrρ hΨ hπid hx.1 hx.2]
  · filter_upwards [hpt (Fin.snoc q t)] with ω hω
    rwa [swcN2_push_eq hab.le hr.1 hrρ hΨ hπid hq ht] at hω

end Push

end SWCore
end QuantumZipper
