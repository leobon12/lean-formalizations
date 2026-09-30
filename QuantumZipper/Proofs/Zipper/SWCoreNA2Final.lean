import QuantumZipper.Proofs.Zipper.SWCoreNA2Inst
import QuantumZipper.Proofs.Zipper.SWCoreNA2Core
import QuantumZipper.Proofs.Zipper.SWCoreNA2Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-NA2: the primed area distortion core for uniform families

Task SWC-NA (`handoff/SW-CORE.md` §5, decision D59). For a uniform family `SwcNA2Unif F c a …`
all deterministic inputs of `swcNA2_family_core` (joint continuity, `Hbar` values, smoothed
Kolmogorov bounds via `swcNA2_familyBounds` with `α = η = 1`, and the common-`β` bounds of
`swcNA2I_hyps`) hold from one dyadic level `k₀` on, giving the conclusion of
`swcNA2_primed_family` (`swcNA2I_primed`). No measurability of `F q` is assumed: the pushed circle
is identified with `circM.map (swcPhiPush …)` by `swcNA2I_map_push`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology

namespace QuantumZipper
namespace SWCore

open E6 E6.XAreaPC TwoPoint KolmD Thm18Asm.G1RC

section NA2Final

variable {n : ℕ} {F : (Fin n → ℝ) → ℂ → ℂ} {c : (Fin n → ℝ) → ℂ} {a : (Fin n → ℝ) → ℝ}
  {x₁ x₂ y₁ y₂ ρ M m H : ℝ}

theorem swcNA2F_cont_of_lip {E : Type*} [SeminormedAddCommGroup E] {f : (Fin n → ℝ) → E}
    {K : ℝ} (hK : 0 ≤ K) (hf : ∀ q q', ‖f q - f q'‖ ≤ K * ‖q - q'‖) : Continuous f :=
  (LipschitzWith.of_dist_le_mul (K := K.toNNReal) fun x y => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK]; exact hf x y).continuous

/-- Lipschitz in the parameter plus continuity on a common domain gives joint continuity. -/
theorem swcNA2F_joint {G : (Fin n → ℝ) → ℂ → ℂ} {U : Set ℂ} {K : ℝ}
    (hGc : ∀ q, ContinuousOn (G q) U) (hGL : ∀ q q', ∀ w ∈ U, ‖G q w - G q' w‖ ≤ K * ‖q - q'‖)
    {u : (Fin n → ℝ) × ℝ → ℂ} (hu : Continuous u) (huU : ∀ p, u p ∈ U) :
    Continuous fun p => G p.1 (u p) := by
  rw [continuous_iff_continuousAt]
  intro x
  have h1 : Tendsto (fun p => G x.1 (u p)) (𝓝 x) (𝓝 (G x.1 (u x))) :=
    ((hGc x.1).continuousWithinAt (huU x)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hu.continuousAt, Eventually.of_forall huU⟩)
  have h3 : Tendsto (fun p : (Fin n → ℝ) × ℝ => K * ‖p.1 - x.1‖) (𝓝 x) (𝓝 0) := by
    have : Tendsto (fun p : (Fin n → ℝ) × ℝ => K * ‖p.1 - x.1‖) (𝓝 x)
        (𝓝 (K * ‖x.1 - x.1‖)) :=
      ((continuous_fst.sub continuous_const).norm.const_mul K).tendsto x
    simpa using this
  have h2 : Tendsto (fun p => G p.1 (u p) - G x.1 (u p)) (𝓝 x) (𝓝 0) :=
    squeeze_zero_norm (fun p => hGL p.1 x.1 (u p) (huU p)) h3
  have h4 := h2.add h1
  simp only [sub_add_cancel, zero_add] at h4
  exact h4

/-- Lipschitz bounds for the image centre and the derivative at the centre. -/
theorem swcNA2F_wd (h : SwcNA2Unif F c a x₁ x₂ y₁ y₂ ρ M m H) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q q' : Fin n → ℝ,
      ‖F q (c q) - F q' (c q')‖ ≤ K * ‖q - q'‖ ∧
      ‖deriv (F q) (c q) - deriv (F q') (c q')‖ ≤ K * ‖q - q'‖ := by
  have hρ := h.rho_pos
  have hH := h.H_nonneg
  set L₁ := |M| / (ρ / 4) + 2 * |M| / (ρ / 4) with hL₁
  have hL₁0 : 0 ≤ L₁ := by positivity
  set L₂ := |M| / (ρ / 4) / (ρ / 4) + 2 * (|M| / (ρ / 4)) / (ρ / 16) with hL₂
  have hL₂0 : 0 ≤ L₂ := by positivity
  have hcU : ∀ p : Fin n → ℝ, ∀ {s : ℝ}, 0 < s → c p ∈ thickening s (rectC x₁ x₂ y₁ y₂) :=
    fun p s hs => self_subset_thickening hs _ (h.cen p)
  refine ⟨(L₁ * H + H) + (L₂ * H + H / (ρ / 4)), by positivity, fun q q' => ?_⟩
  set δ := ‖q - q'‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hw : ‖F q (c q) - F q' (c q')‖ ≤ L₁ * (H * δ) + H * δ := by
    have h1 := swcNA2I_lip hρ (h.cls q) (hcU q (by positivity : 0 < ρ / 4))
      (hcU q' (by positivity : 0 < ρ / 4))
    have h2 := h.F_lip q q' (c q') (hcU q' hρ)
    calc ‖F q (c q) - F q' (c q')‖ =
          ‖(F q (c q) - F q (c q')) + (F q (c q') - F q' (c q'))‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ L₁ * (H * δ) + H * δ :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left (h.c_lip q q') hL₁0)) h2
  have hdd : ‖deriv (F q) (c q) - deriv (F q') (c q')‖ ≤ L₂ * (H * δ) + H * δ / (ρ / 4) := by
    have h1 := swcNA2I_lip_deriv hρ (h.cls q) (hcU q (by positivity : 0 < ρ / 16))
      (hcU q' (by positivity : 0 < ρ / 16))
    have h2 := swcNA2I_deriv_sub hρ (h.cls q) (h.cls q') (fun w hw => h.F_lip q q' w hw)
      (hcU q' (by positivity : 0 < ρ / 2))
    calc ‖deriv (F q) (c q) - deriv (F q') (c q')‖ =
          ‖(deriv (F q) (c q) - deriv (F q) (c q')) +
            (deriv (F q) (c q') - deriv (F q') (c q'))‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ L₂ * (H * δ) + H * δ / (ρ / 4) :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left (h.c_lip q q') hL₂0)) h2
  have e1 : L₁ * (H * δ) + H * δ ≤ ((L₁ * H + H) + (L₂ * H + H / (ρ / 4))) * δ := by
    have : 0 ≤ (L₂ * H + H / (ρ / 4)) * δ := by positivity
    nlinarith
  have e2 : L₂ * (H * δ) + H * δ / (ρ / 4) ≤ ((L₁ * H + H) + (L₂ * H + H / (ρ / 4))) * δ := by
    have : 0 ≤ (L₁ * H + H) * δ := by positivity
    have e : L₂ * (H * δ) + H * δ / (ρ / 4) = (L₂ * H + H / (ρ / 4)) * δ := by ring
    nlinarith
  exact ⟨hw.trans e1, hdd.trans e2⟩

/-- Scale-wise facts for `k ≥ k₀`: radii, Frostman bounds and parameter-Lipschitz bounds of the
two parametrizations. -/
theorem swcNA2F_scale (h : SwcNA2Unif F c a x₁ x₂ y₁ y₂ ρ M m H) :
    ∃ k₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ k ≥ k₀, ∀ q : Fin n → ℝ,
      0 < a q * radius k ∧ a q * radius k < ρ ∧ a q * radius k ≤ (c q).im ∧
      0 < a q * radius k * ‖deriv (F q) (c q)‖ ∧
      a q * radius k * ‖deriv (F q) (c q)‖ ≤ (F q (c q)).im ∧
      IsFrostman (circM.map (swcPhiPush F c a k q)) 1 (24 / (m * radius k)) ∧
      IsFrostman (circM.map (swcPhiRound F c a k q)) 1 (24 / (m * radius k)) ∧
      (∀ q' θ, ‖swcPhiPush F c a k q θ - swcPhiPush F c a k q' θ‖ ≤ K * ‖q - q'‖) ∧
      (∀ q' θ, ‖swcPhiRound F c a k q θ - swcPhiRound F c a k q' θ‖ ≤ K * ‖q - q'‖) := by
  have hρ := h.rho_pos
  have hm := h.m_pos
  have hH := h.H_nonneg
  obtain ⟨R₀, hR₀, hpf⟩ := swcVA_push_facts (a := x₁) (b := x₂) (d := y₂) (M := M)
    h.y_pos hρ hm
  obtain ⟨Kw, hKw, hwd⟩ := swcNA2F_wd h
  set M₁ := |M| / (ρ / 4) with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  set L₁ := |M| / (ρ / 4) + 2 * |M| / (ρ / 4) with hL₁
  have hL₁0 : 0 ≤ L₁ := by positivity
  set P := L₁ * (2 * H) + H with hP
  have hP0 : 0 ≤ P := by positivity
  set Q := Kw + (H * M₁ + 2 * Kw) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  obtain ⟨k₀, hk₀⟩ := swcNA2I_k0 (lt_min hR₀ (lt_min (by positivity : 0 < ρ / 8)
    (lt_min h.y_pos (by positivity : 0 < ρ / (M₁ + 1)))))
  refine ⟨k₀, P + Q, by positivity, fun k hk q => ?_⟩
  simp only [swcNA2I_push_eq, swcNA2I_round_eq]
  set t := radius k with ht_def
  have ht := swcNA2I_radius_pos k
  have ht1 := swcNA2I_radius_le_one k
  have h2t := hk₀ k hk
  have h2tR : 2 * t ≤ R₀ := h2t.trans (min_le_left _ _)
  have h2t8 : 2 * t ≤ ρ / 8 := h2t.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h2ty : 2 * t ≤ y₁ :=
    h2t.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h2tM : 2 * t ≤ ρ / (M₁ + 1) :=
    h2t.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hap : ∀ p : Fin n → ℝ, a p * t ≤ 2 * t := fun p =>
    mul_le_mul_of_nonneg_right (h.a_le p) ht.le
  have hap0 : ∀ p : Fin n → ℝ, 0 < a p * t := fun p => mul_pos (by linarith [h.a_ge p]) ht
  have hta : ∀ p : Fin n → ℝ, t ≤ a p * t := fun p => le_mul_of_one_le_left ht.le (h.a_ge p)
  have hU4 : ∀ p : Fin n → ℝ, ∀ θ, circleMap (c p) (a p * t) θ ∈
      thickening (ρ / 4) (rectC x₁ x₂ y₁ y₂) := fun p θ =>
    swcNA2I_mem_thick (h.cen p) (swcNA2I_circ_norm _ (hap0 p).le θ).le (by linarith [hap p])
  have hd : ∀ p : Fin n → ℝ, ‖deriv (F p) (c p)‖ ≤ M₁ := fun p =>
    swcNA2I_deriv_le hρ (h.cls p) (self_subset_thickening (by positivity) _ (h.cen p))
  have hdm : ∀ p : Fin n → ℝ, m ≤ ‖deriv (F p) (c p)‖ := fun p =>
    (h.cls p).2.2.2 (c p) (h.cen p)
  have hFc : ∀ p : Fin n → ℝ, ρ ≤ (F p (c p)).im := fun p =>
    ((h.cls p).2.2.1 (c p) (self_subset_thickening hρ _ (h.cen p))).2
  have hsmall : ∀ p : Fin n → ℝ, a p * t * ‖deriv (F p) (c p)‖ ≤ ρ := fun p => by
    have h2 : a p * t * ‖deriv (F p) (c p)‖ ≤ 2 * t * (M₁ + 1) :=
      mul_le_mul (hap p) (by linarith [hd p]) (norm_nonneg _) (by positivity)
    have h3 := mul_le_mul_of_nonneg_right h2tM (by positivity : (0 : ℝ) ≤ M₁ + 1)
    rw [div_mul_cancel₀ _ (by positivity)] at h3
    linarith
  have hlow : ∀ p : Fin n → ℝ, m * t ≤ a p * t * ‖deriv (F p) (c p)‖ := fun p => by
    have h1 : m * t ≤ ‖deriv (F p) (c p)‖ * t := mul_le_mul_of_nonneg_right (hdm p) ht.le
    have h2 := mul_nonneg (mul_nonneg (sub_nonneg.2 (h.a_ge p)) ht.le)
      (norm_nonneg (deriv (F p) (c p)))
    nlinarith
  have hmt : 0 < m * t := mul_pos hm ht
  have hs0 : ∀ p : Fin n → ℝ, 0 < a p * t * ‖deriv (F p) (c p)‖ := fun p =>
    hmt.trans_le (hlow p)
  refine ⟨hap0 q, by linarith [hap q], by linarith [hap q, (h.cen q).2.1], hs0 q,
    (hsmall q).trans (hFc q), ?_, ?_, fun q' θ => ?_, fun q' θ => ?_⟩
  · obtain ⟨χt, -, hχe, hχF, -⟩ := hpf (F q) (h.cls q) (c q) (h.cen q) (a q * t) (hap0 q)
      (by linarith [hap q])
    rw [swcNA2I_map_push (h.cls q) (h.cen q) (hap0 q) (by linarith [hap q])
      (by linarith [hap q, (h.cen q).2.1]), hχe]
    refine swcNA2I_frost_mono hχF ?_
    rw [div_le_div_iff₀ (mul_pos (by positivity) (hap0 q)) (by positivity)]
    have := mul_le_mul_of_nonneg_left (hta q) hm.le
    linarith
  · rw [swcNA2I_map_round (hs0 q).le ((hsmall q).trans (hFc q))]
    have := swcVA_isFrostman_push (ψ := id) measurable_id (hs0 q) one_pos
      (K := closedBall (F q (c q)) (a q * t * ‖deriv (F q) (c q)‖)) (fun x _ y _ => by simp)
      ((hsmall q).trans (hFc q)) subset_rfl
    rw [Measure.map_id] at this
    refine swcNA2I_frost_mono this ?_
    rw [div_le_div_iff₀ (by rw [one_mul]; exact hs0 q) hmt]
    have := hlow q
    nlinarith
  · set δ := ‖q - q'‖ with hδ
    have hδ0 : 0 ≤ δ := norm_nonneg _
    set u := circleMap (c q) (a q * t) θ
    set u' := circleMap (c q') (a q' * t) θ
    have huu : ‖u - u'‖ ≤ 2 * H * δ := by
      refine (swcNA2I_circ_sub _ _ _ _ θ).trans ?_
      have e : a q * t - a q' * t = (a q - a q') * t := by ring
      rw [e, abs_mul, abs_of_pos ht]
      have h1 := h.c_lip q q'
      have h2 : |a q - a q'| * t ≤ H * δ :=
        (mul_le_of_le_one_right (abs_nonneg _) ht1).trans (h.a_lip q q')
      linarith
    have h1 := swcNA2I_lip hρ (h.cls q) (hU4 q θ) (hU4 q' θ)
    have h2 := h.F_lip q q' u' (thickening_mono (by linarith) _ (hU4 q' θ))
    have hQδ : 0 ≤ Q * δ := by positivity
    calc ‖F q u - F q' u'‖ = ‖(F q u - F q u') + (F q u' - F q' u')‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖F q u - F q u'‖ + ‖F q u' - F q' u'‖ := norm_add_le _ _
      _ ≤ L₁ * (2 * H * δ) + H * δ :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left huu hL₁0)) h2
      _ = P * δ := by rw [hP]; ring
      _ ≤ (P + Q) * δ := by nlinarith
  · set δ := ‖q - q'‖ with hδ
    have hδ0 : 0 ≤ δ := norm_nonneg _
    obtain ⟨hw, hdd⟩ := hwd q q'
    have hs : |a q * t * ‖deriv (F q) (c q)‖ - a q' * t * ‖deriv (F q') (c q')‖| ≤
        H * δ * M₁ + 2 * (Kw * δ) := by
      have e : a q * t * ‖deriv (F q) (c q)‖ - a q' * t * ‖deriv (F q') (c q')‖ =
          t * ((a q - a q') * ‖deriv (F q) (c q)‖ +
            a q' * (‖deriv (F q) (c q)‖ - ‖deriv (F q') (c q')‖)) := by ring
      rw [e, abs_mul, abs_of_pos ht]
      have h1 : |(a q - a q') * ‖deriv (F q) (c q)‖ +
            a q' * (‖deriv (F q) (c q)‖ - ‖deriv (F q') (c q')‖)| ≤
          H * δ * M₁ + 2 * (Kw * δ) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
          exact mul_le_mul (h.a_lip q q') (hd q) (norm_nonneg _) (by positivity)
        · rw [abs_mul, abs_of_pos (by linarith [h.a_ge q'] : 0 < a q')]
          exact mul_le_mul (h.a_le q') ((abs_norm_sub_norm_le _ _).trans hdd) (abs_nonneg _)
            (by norm_num)
      have h0 := abs_nonneg ((a q - a q') * ‖deriv (F q) (c q)‖ +
            a q' * (‖deriv (F q) (c q)‖ - ‖deriv (F q') (c q')‖))
      nlinarith
    refine (swcNA2I_circ_sub _ _ _ _ θ).trans ?_
    have hPδ : 0 ≤ P * δ := by positivity
    have e : Kw * δ + (H * δ * M₁ + 2 * (Kw * δ)) = Q * δ := by rw [hQ]; ring
    nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Primed area distortion core for a uniform family** (conclusion of `swcNA2_primed_family`
with all hypotheses discharged from `SwcNA2Unif`; no measurability of `F q` needed). -/
theorem swcNA2I_primed [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (h : SwcNA2Unif F c a x₁ x₂ y₁ y₂ ρ M m H) :
    ∃ k₀ : ℕ, ∀ᵐ ω ∂P,
      (∀ k, ∀ K : Set (Fin n → ℝ), IsCompact K →
        TendstoUniformlyOn (fun j q => ∫ u, avgReg (X ω) j u
            ∂((foldedCircle (c q) (a q * radius (k + k₀))).map (F q)))
          (fun q => evalReg (X ω) ((foldedCircle (c q) (a q * radius (k + k₀))).map (F q)))
          atTop K) ∧
      (∀ k, Continuous fun q =>
        evalReg (X ω) ((foldedCircle (c q) (a q * radius (k + k₀))).map (F q))) ∧
      ∀ R : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q ∈ boxD (d := n) R,
        |evalReg (X ω) ((foldedCircle (c q) (a q * radius (k + k₀))).map (F q)) -
          evalReg (X ω) (foldedCircle (F q (c q)) (a q * radius (k + k₀) *
            ‖deriv (F q) (c q)‖))| ≤ η := by
  have hρ := h.rho_pos
  have hH := h.H_nonneg
  obtain ⟨k₁, K, hK, hsc⟩ := swcNA2F_scale h
  obtain ⟨k₂, C, hC, hv⟩ := swcNA2I_hvar h
  obtain ⟨k₃, L, hL, hmd⟩ := swcNA2I_hmod h
  obtain ⟨k₄, hfb⟩ := swcNA2I_familyBounds h
  obtain ⟨Kw, hKw, hwd⟩ := swcNA2F_wd h
  set k₀ := max (max k₁ k₂) (max k₃ k₄) with hk₀
  refine ⟨k₀, ?_⟩
  have e1 : ∀ k, k + k₀ ≥ k₁ := fun k =>
    le_add_left ((le_max_left _ _).trans (le_max_left _ _))
  have e2 : ∀ k, k + k₀ ≥ k₂ := fun k =>
    le_add_left ((le_max_right _ _).trans (le_max_left _ _))
  have e3 : ∀ k, k + k₀ ≥ k₃ := fun k =>
    le_add_left ((le_max_left _ _).trans (le_max_right _ _))
  have e4 : ∀ k, k + k₀ ≥ k₄ := fun k =>
    le_add_left ((le_max_right _ _).trans (le_max_right _ _))
  have hcC : Continuous c := swcNA2F_cont_of_lip hH h.c_lip
  have haC : Continuous a := swcNA2F_cont_of_lip hH fun q q' => by
    rw [Real.norm_eq_abs]; exact h.a_lip q q'
  have hwC : Continuous fun q => F q (c q) := swcNA2F_cont_of_lip hKw fun q q' => (hwd q q').1
  have hdC : Continuous fun q => deriv (F q) (c q) :=
    swcNA2F_cont_of_lip hKw fun q q' => (hwd q q').2
  have hmem : ∀ k q θ, circleMap (c q) (a q * radius (k + k₀)) θ ∈
      thickening ρ (rectC x₁ x₂ y₁ y₂) := fun k q θ =>
    swcNA2I_mem_thick (h.cen q) (swcNA2I_circ_norm _ (hsc _ (e1 k) q).1.le θ).le
      (hsc _ (e1 k) q).2.1
  have hcμ : ∀ k, Continuous (uncurry (swcPhiPush F c a (k + k₀))) := fun k => by
    have hu : Continuous fun p : (Fin n → ℝ) × ℝ =>
        circleMap (c p.1) (a p.1 * radius (k + k₀)) p.2 := by
      simp only [circleMap]; fun_prop
    exact swcNA2F_joint (G := F) (fun q => (h.cls q).1.continuousOn) h.F_lip hu
      (fun p => hmem k p.1 p.2)
  have hcν : ∀ k, Continuous (uncurry (swcPhiRound F c a (k + k₀))) := fun k => by
    show Continuous fun p : (Fin n → ℝ) × ℝ =>
      circleMap (F p.1 (c p.1)) (a p.1 * radius (k + k₀) * ‖deriv (F p.1) (c p.1)‖) p.2
    simp only [circleMap]
    exact (hwC.comp continuous_fst).add ((Complex.continuous_ofReal.comp
      (((haC.comp continuous_fst).mul continuous_const).mul
        (hdC.comp continuous_fst).norm)).mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
        continuous_const)))
  have hHμ : ∀ k q θ, swcPhiPush F c a (k + k₀) q θ ∈ Hbar := fun k q θ => by
    show 0 ≤ (F q (circleMap (c q) (a q * radius (k + k₀)) θ)).im
    linarith [((h.cls q).2.2.1 _ (hmem k q θ)).2]
  have hHν : ∀ k q θ, swcPhiRound F c a (k + k₀) q θ ∈ Hbar := fun k q θ => by
    show 0 ≤ (circleMap (F q (c q)) (a q * radius (k + k₀) * ‖deriv (F q) (c q)‖) θ).im
    have h1 := Complex.abs_im_le_norm
      (circleMap (F q (c q)) (a q * radius (k + k₀) * ‖deriv (F q) (c q)‖) θ - F q (c q))
    rw [swcNA2I_circ_norm _ (hsc _ (e1 k) q).2.2.2.1.le, Complex.sub_im] at h1
    linarith [(abs_le.1 h1).1, (hsc _ (e1 k) q).2.2.2.2.1]
  have hnμ : ∀ k q θ, ‖swcPhiPush F c a (k + k₀) q θ‖ ≤ |M| := fun k q θ =>
    ((h.cls q).2.2.1 _ (hmem k q θ)).1.trans (le_abs_self M)
  have hnν : ∀ k q θ, ‖swcPhiRound F c a (k + k₀) q θ‖ ≤ |M| + |M| := fun k q θ => by
    have hb := ((h.cls q).2.2.1 (c q) (self_subset_thickening hρ _ (h.cen q))).1.trans
      (le_abs_self M)
    have hs := (hsc _ (e1 k) q).2.2.2.2.1
    have him := Complex.im_le_norm (F q (c q))
    have h1 := swcNA2I_circ_norm (F q (c q)) (hsc _ (e1 k) q).2.2.2.1.le θ
    show ‖circleMap (F q (c q)) (a q * radius (k + k₀) * ‖deriv (F q) (c q)‖) θ‖ ≤ _
    calc _ = ‖(circleMap (F q (c q)) (a q * radius (k + k₀) * ‖deriv (F q) (c q)‖) θ -
          F q (c q)) + F q (c q)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ |M| + |M| := by rw [h1]; linarith
  have hBμ : ∀ k, ∃ β' : ℝ, 0 < β' ∧
      FamilyBounds (smoothFam circM (swcPhiPush F c a (k + k₀))) β' := fun k => by
    have hm := h.m_pos
    have hr := swcNA2I_radius_pos (k + k₀)
    exact swcNA2_familyBounds (hcμ k) (hHμ k) one_pos le_rfl one_pos le_rfl fun R =>
      ⟨|M|, 24 / (m * radius (k + k₀)), K, abs_nonneg _, by positivity, hK, fun q _ =>
        ⟨hnμ k q, (hsc _ (e1 k) q).2.2.2.2.2.1, fun q' _ θ => by
          rw [Real.rpow_one]; exact (hsc _ (e1 k) q).2.2.2.2.2.2.2.1 q' θ⟩⟩
  have hBν : ∀ k, ∃ β' : ℝ, 0 < β' ∧
      FamilyBounds (smoothFam circM (swcPhiRound F c a (k + k₀))) β' := fun k => by
    have hm := h.m_pos
    have hr := swcNA2I_radius_pos (k + k₀)
    exact swcNA2_familyBounds (hcν k) (hHν k) one_pos le_rfl one_pos le_rfl fun R =>
      ⟨|M| + |M|, 24 / (m * radius (k + k₀)), K, by positivity, by positivity, hK, fun q _ =>
        ⟨hnν k q, (hsc _ (e1 k) q).2.2.2.2.2.2.1, fun q' _ θ => by
          rw [Real.rpow_one]; exact (hsc _ (e1 k) q).2.2.2.2.2.2.2.2 q' θ⟩⟩
  have hμ : ∀ k, FamilyBounds (fun q => circM.map (swcPhiPush F c a (k + k₀) q)) (1 / 2) :=
    fun k => (hfb _ (e4 k)).1
  have hν : ∀ k, FamilyBounds (fun q => circM.map (swcPhiRound F c a (k + k₀) q)) (1 / 2) :=
    fun k => (hfb _ (e4 k)).2
  have hvar : ∀ R : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ∀ q ∈ boxD (d := n) R,
      |kernelCov2 neumannH (circM.map (swcPhiPush F c a (k + k₀) q),
          circM.map (swcPhiRound F c a (k + k₀) q))
        (circM.map (swcPhiPush F c a (k + k₀) q), circM.map (swcPhiRound F c a (k + k₀) q))| ≤
        C * (1 / 2) ^ k := fun R => ⟨C, hC, fun k q _ =>
    (hv (k + k₀) (e2 k) q).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right k k₀)) hC)⟩
  have hmod : ∀ R : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ k, ∀ q ∈ boxD (d := n) R, ∀ q' ∈ boxD (d := n) R,
      |kernelCov2 neumannH (circM.map (swcPhiPush F c a (k + k₀) q),
          circM.map (swcPhiPush F c a (k + k₀) q'))
        (circM.map (swcPhiPush F c a (k + k₀) q), circM.map (swcPhiPush F c a (k + k₀) q'))| ≤
        L * 2 ^ k * ‖q - q'‖ ^ (1 / 2 : ℝ) ∧
      |kernelCov2 neumannH (circM.map (swcPhiRound F c a (k + k₀) q),
          circM.map (swcPhiRound F c a (k + k₀) q'))
        (circM.map (swcPhiRound F c a (k + k₀) q), circM.map (swcPhiRound F c a (k + k₀) q'))| ≤
        L * 2 ^ k * ‖q - q'‖ ^ (1 / 2 : ℝ) := fun R =>
    ⟨L * 2 ^ k₀, by positivity, fun k q _ q' _ => by
      obtain ⟨h1, h2⟩ := hmd (k + k₀) (e3 k) q q'
      have e : L * 2 ^ (k + k₀) = L * 2 ^ k₀ * 2 ^ k := by rw [pow_add]; ring
      rw [e] at h1 h2
      exact ⟨h1, h2⟩⟩
  have eμ : ∀ k q, circM.map (swcPhiPush F c a (k + k₀) q) =
      (foldedCircle (c q) (a q * radius (k + k₀))).map (F q) := fun k q => by
    rw [swcNA2I_push_eq]
    exact swcNA2I_map_push (h.cls q) (h.cen q) (hsc _ (e1 k) q).1 (hsc _ (e1 k) q).2.1
      (hsc _ (e1 k) q).2.2.1
  have eν : ∀ k q, circM.map (swcPhiRound F c a (k + k₀) q) =
      foldedCircle (F q (c q)) (a q * radius (k + k₀) * ‖deriv (F q) (c q)‖) := fun k q => by
    rw [swcNA2I_round_eq]
    exact swcNA2I_map_round (hsc _ (e1 k) q).2.2.2.1.le (hsc _ (e1 k) q).2.2.2.2.1
  filter_upwards [swcNA2_family_core hX (Φμ := fun k => swcPhiPush F c a (k + k₀))
    (Φν := fun k => swcPhiRound F c a (k + k₀)) hcμ hcν hHμ hHν hBμ hBν
    (by norm_num : (0 : ℝ) < 1 / 2) hμ hν hvar hmod] with ω hω
  obtain ⟨h1, -, h3, -, h5⟩ := hω
  refine ⟨fun k K hK => ?_, fun k => ?_, fun R η hη => ?_⟩
  · simpa only [eμ] using h1 k K hK
  · simpa only [eμ] using h3 k
  · simpa only [eμ, eν] using h5 R η hη

end NA2Final

end SWCore
end QuantumZipper
