import QuantumZipper.Proofs.Zipper.SWCoreNA2InstBase
import QuantumZipper.Proofs.Zipper.SWCoreNA2Dist
import QuantumZipper.Proofs.Zipper.SWCoreNA2Fam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-NA2: the variance and modulus hypotheses for pushed and image circles of a uniform family

Task SWC-NA (`handoff/SW-CORE.md` §5). For a uniform family `SwcNA2Unif F c a …` (maps of one area
class, centres in the rectangle, radius factors in `[1,2]`, all Lipschitz in `q`), the pushed
circles `circM.map (swcPhiPush F c a (k + k₀) q)` and image circles
`circM.map (swcPhiRound F c a (k + k₀) q)` satisfy the hypotheses `hμ`, `hν` (with `β = 1/2`),
`hvar` and `hmod` of `swcNA2_distortion_small` (`swcNA2I_hyps`, `swcNA2I_familyBounds_push`,
`swcNA2I_familyBounds_round`).

`hmod` is the generic map-direction energy bound `swcNA2I_kernelCov2_map_map_le` applied with
`σ = circM` to the two parametrizations at once (centre, radius and map changing), which are
`O(‖q − q'‖)`-close by the Lipschitz hypotheses and the Cauchy estimates. This is the modulus
(3.21)–(3.22) of Sheffield–Wang arXiv:1605.06171, Lemma 3.5 (p. 16), in the repository's
potential-theoretic form. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

open E6 E6.XAreaPC TwoPoint Thm18Asm.G1RC

section NA2InstMod

variable {n : ℕ} {F : (Fin n → ℝ) → ℂ → ℂ} {c : (Fin n → ℝ) → ℂ} {a : (Fin n → ℝ) → ℝ}
  {x₁ x₂ y₁ y₂ ρ M m H : ℝ}

/-- **`hmod` for the uniform family**, for `k ≥ k₀`, with a constant independent of the box. -/
theorem swcNA2I_hmod (h : SwcNA2Unif F c a x₁ x₂ y₁ y₂ ρ M m H) :
    ∃ k₀ : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ k ≥ k₀, ∀ q q' : Fin n → ℝ,
      |kernelCov2 neumannH (circM.map (swcPhiPush F c a k q), circM.map (swcPhiPush F c a k q'))
        (circM.map (swcPhiPush F c a k q), circM.map (swcPhiPush F c a k q'))| ≤
          L * 2 ^ k * ‖q - q'‖ ^ (1 / 2 : ℝ) ∧
      |kernelCov2 neumannH (circM.map (swcPhiRound F c a k q), circM.map (swcPhiRound F c a k q'))
        (circM.map (swcPhiRound F c a k q), circM.map (swcPhiRound F c a k q'))| ≤
          L * 2 ^ k * ‖q - q'‖ ^ (1 / 2 : ℝ) := by
  have hρ := h.rho_pos
  have hm := h.m_pos
  have hH := h.H_nonneg
  obtain ⟨R₀, hR₀, hpm⟩ := swcNA2I_push_mod (x₁ := x₁) (x₂ := x₂) (y₂ := y₂) (M := M)
    h.y_pos hρ hm
  set M₁ := |M| / (ρ / 4) with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  set L₁ := |M| / (ρ / 4) + 2 * |M| / (ρ / 4) with hL₁
  have hL₁0 : 0 ≤ L₁ := by positivity
  set L₂ := |M| / (ρ / 4) / (ρ / 4) + 2 * (|M| / (ρ / 4)) / (ρ / 16) with hL₂
  have hL₂0 : 0 ≤ L₂ := by positivity
  set P := L₁ * (2 * H) + H with hP
  have hP0 : 0 ≤ P := by positivity
  set Q := L₁ * H + H + (H * M₁ + 2 * (L₂ * H + H / (ρ / 4))) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set K := P + Q with hK
  have hK0 : 0 ≤ K := by positivity
  set B := |M| + ρ with hB
  have hB0 : 0 ≤ B := by positivity
  set A := 2 + 288 / m + 4 * Real.log (B + B + 1) with hA
  have hA0 : 0 ≤ A := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ B + B + 1); positivity
  obtain ⟨k₀, hk₀⟩ := swcNA2I_k0
    (lt_min hR₀ (lt_min (by positivity : 0 < ρ / 8) (by positivity : 0 < ρ / (M₁ + 1))))
  refine ⟨k₀, 2 * A * K ^ (1 / 2 : ℝ), by positivity, fun k hk q q' => ?_⟩
  simp only [swcNA2I_push_eq, swcNA2I_round_eq]
  set t := radius k with ht_def
  have ht := swcNA2I_radius_pos k
  have ht1 := swcNA2I_radius_le_one k
  have h2t := hk₀ k hk
  have h2tR : 2 * t ≤ R₀ := h2t.trans (min_le_left _ _)
  have h2t8 : 2 * t ≤ ρ / 8 := h2t.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h2tM : 2 * t ≤ ρ / (M₁ + 1) := h2t.trans ((min_le_right _ _).trans (min_le_right _ _))
  set δ := ‖q - q'‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  -- the final numerical bound
  have hfin : ∀ C' B' ε : ℝ, 0 ≤ C' → C' ≤ 24 / (m * t) → 0 ≤ B' → B' ≤ B → 0 ≤ ε →
      ε ≤ K * δ →
      2 * (swcPotK C' B' * ε ^ (1 / 2 : ℝ)) ≤ 2 * A * K ^ (1 / 2 : ℝ) * 2 ^ k *
        δ ^ (1 / 2 : ℝ) := by
    intro C' B' ε hC'0 hC' hB'0 hB' hε0 hε
    have h1 := swcNA2I_potK_mono hC' hB'0 hB'
    have h2 := swcNA2I_potK_le hm ht ht1 hB0
    have e : A / t = A * 2 ^ k := by
      rw [ht_def]; unfold radius; rw [inv_pow, div_inv_eq_mul]
    have h3 : ε ^ (1 / 2 : ℝ) ≤ K ^ (1 / 2 : ℝ) * δ ^ (1 / 2 : ℝ) := by
      rw [← Real.mul_rpow hK0 hδ0]; exact Real.rpow_le_rpow hε0 hε (by norm_num)
    have hP0' : 0 ≤ swcPotK C' B' := by
      unfold swcPotK
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ B' + B' + 1)
      positivity
    have h4 : swcPotK C' B' ≤ A / t := h1.trans h2
    calc 2 * (swcPotK C' B' * ε ^ (1 / 2 : ℝ))
        ≤ 2 * (A / t * (K ^ (1 / 2 : ℝ) * δ ^ (1 / 2 : ℝ))) := by
          gcongr
      _ = 2 * A * K ^ (1 / 2 : ℝ) * 2 ^ k * δ ^ (1 / 2 : ℝ) := by rw [e]; ring
  have hU4 : ∀ p : Fin n → ℝ, ∀ θ, circleMap (c p) (a p * t) θ ∈
      thickening (ρ / 4) (rectC x₁ x₂ y₁ y₂) := fun p θ => by
    have hap : a p * t ≤ 2 * t := mul_le_mul_of_nonneg_right (h.a_le p) ht.le
    have hap0 : 0 ≤ a p * t := mul_nonneg (by linarith [h.a_ge p]) ht.le
    exact swcNA2I_mem_thick (h.cen p) (swcNA2I_circ_norm _ hap0 θ).le (by linarith)
  have hcU : ∀ p : Fin n → ℝ, ∀ {s : ℝ}, 0 < s → c p ∈ thickening s (rectC x₁ x₂ y₁ y₂) :=
    fun p s hs => self_subset_thickening hs _ (h.cen p)
  have hUρ : ∀ {s : ℝ} {u : ℂ}, s ≤ ρ → u ∈ thickening s (rectC x₁ x₂ y₁ y₂) →
      u ∈ thickening ρ (rectC x₁ x₂ y₁ y₂) := fun hs hu => thickening_mono hs _ hu
  refine ⟨?_, ?_⟩
  · -- pushed circles
    have hε : ∀ θ, ‖F q (circleMap (c q) (a q * t) θ) - F q' (circleMap (c q') (a q' * t) θ)‖ ≤
        P * δ := by
      intro θ
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
      have h2 := h.F_lip q q' u' (hUρ (by linarith) (hU4 q' θ))
      calc ‖F q u - F q' u'‖ = ‖(F q u - F q u') + (F q u' - F q' u')‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ ‖F q u - F q u'‖ + ‖F q u' - F q' u'‖ := norm_add_le _ _
        _ ≤ L₁ * (2 * H * δ) + H * δ :=
            add_le_add (h1.trans (mul_le_mul_of_nonneg_left huu hL₁0)) h2
        _ = P * δ := by rw [hP]; ring
    have hta : ∀ p : Fin n → ℝ, t ≤ a p * t := fun p => le_mul_of_one_le_left ht.le (h.a_ge p)
    have htR : ∀ p : Fin n → ℝ, a p * t ≤ R₀ := fun p =>
      (mul_le_mul_of_nonneg_right (h.a_le p) ht.le).trans h2tR
    refine (hpm (F q) (h.cls q) (F q') (h.cls q') (c q) (h.cen q) (c q') (h.cen q') _ _ t ht
      (hta q) (hta q') (htR q) (htR q') _ hε).trans ?_
    refine hfin _ _ _ (by positivity) (le_of_eq ?_) (abs_nonneg M) (by linarith)
      (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hδ0)
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  · -- round circles
    have hd : ∀ p : Fin n → ℝ, ‖deriv (F p) (c p)‖ ≤ M₁ := fun p =>
      swcNA2I_deriv_le hρ (h.cls p) (hcU p (by positivity))
    have hdm : ∀ p : Fin n → ℝ, m ≤ ‖deriv (F p) (c p)‖ := fun p =>
      (h.cls p).2.2.2 (c p) (h.cen p)
    have hFc : ∀ p : Fin n → ℝ, ‖F p (c p)‖ ≤ |M| ∧ ρ ≤ (F p (c p)).im := fun p =>
      ⟨((h.cls p).2.2.1 (c p) (hcU p hρ)).1.trans (le_abs_self M),
        ((h.cls p).2.2.1 (c p) (hcU p hρ)).2⟩
    have hsmall : ∀ p : Fin n → ℝ, a p * t * ‖deriv (F p) (c p)‖ ≤ ρ := fun p => by
      have h1 : a p * t ≤ 2 * t := mul_le_mul_of_nonneg_right (h.a_le p) ht.le
      have h2 : a p * t * ‖deriv (F p) (c p)‖ ≤ 2 * t * (M₁ + 1) :=
        mul_le_mul h1 (by linarith [hd p]) (norm_nonneg _) (by positivity)
      have h3 := mul_le_mul_of_nonneg_right h2tM (by positivity : (0 : ℝ) ≤ M₁ + 1)
      rw [div_mul_cancel₀ _ (by positivity)] at h3
      linarith
    have hlow : ∀ p : Fin n → ℝ, m * t ≤ a p * t * ‖deriv (F p) (c p)‖ := fun p => by
      have h1 : m * t ≤ ‖deriv (F p) (c p)‖ * t := mul_le_mul_of_nonneg_right (hdm p) ht.le
      have h2 := mul_nonneg (mul_nonneg (sub_nonneg.2 (h.a_ge p)) ht.le)
        (norm_nonneg (deriv (F p) (c p)))
      nlinarith
    have hBp : ∀ p : Fin n → ℝ, ‖F p (c p)‖ + a p * t * ‖deriv (F p) (c p)‖ ≤ B := fun p => by
      linarith [hsmall p, (hFc p).1]
    have hr := swcNA2I_round_mod (mul_pos hm ht) (hlow q) (hlow q')
      ((hsmall q).trans (hFc q).2) ((hsmall q').trans (hFc q').2) (hBp q) (hBp q')
    refine hr.trans ?_
    -- the closeness of centres and radii
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
    have hs : |a q * t * ‖deriv (F q) (c q)‖ - a q' * t * ‖deriv (F q') (c q')‖| ≤
        H * δ * M₁ + 2 * (L₂ * (H * δ) + H * δ / (ρ / 4)) := by
      have e : a q * t * ‖deriv (F q) (c q)‖ - a q' * t * ‖deriv (F q') (c q')‖ =
          t * ((a q - a q') * ‖deriv (F q) (c q)‖ +
            a q' * (‖deriv (F q) (c q)‖ - ‖deriv (F q') (c q')‖)) := by ring
      rw [e, abs_mul, abs_of_pos ht]
      have h1 : |(a q - a q') * ‖deriv (F q) (c q)‖ +
            a q' * (‖deriv (F q) (c q)‖ - ‖deriv (F q') (c q')‖)| ≤
          H * δ * M₁ + 2 * (L₂ * (H * δ) + H * δ / (ρ / 4)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
          exact mul_le_mul (h.a_lip q q') (hd q) (norm_nonneg _) (by positivity)
        · rw [abs_mul, abs_of_pos (by linarith [h.a_ge q'] : 0 < a q')]
          exact mul_le_mul (h.a_le q') ((abs_norm_sub_norm_le _ _).trans hdd) (abs_nonneg _)
            (by norm_num)
      calc t * |(a q - a q') * ‖deriv (F q) (c q)‖ +
            a q' * (‖deriv (F q) (c q)‖ - ‖deriv (F q') (c q')‖)| ≤
          1 * |(a q - a q') * ‖deriv (F q) (c q)‖ +
            a q' * (‖deriv (F q) (c q)‖ - ‖deriv (F q') (c q')‖)| :=
            mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h1
    have hεK : ‖F q (c q) - F q' (c q')‖ +
        |a q * t * ‖deriv (F q) (c q)‖ - a q' * t * ‖deriv (F q') (c q')‖| ≤ K * δ := by
      have e : L₁ * (H * δ) + H * δ + (H * δ * M₁ + 2 * (L₂ * (H * δ) + H * δ / (ρ / 4))) =
          Q * δ := by rw [hQ]; ring
      have h3 : Q * δ ≤ K * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0
      linarith
    have hmt : 0 < m * t := mul_pos hm ht
    have hC12 : 12 / (m * t) ≤ 24 / (m * t) := div_le_div_of_nonneg_right (by norm_num) hmt.le
    exact hfin (12 / (m * t)) B _ (by positivity) hC12 hB0 le_rfl (by positivity) hεK

/-- `FamilyBounds` with `β = 1/2` for a family of `circM`-pushforwards of continuous
parametrizations, from support, uniform Frostman and modulus bounds. -/
theorem swcNA2I_fb_of {Φ : (Fin n → ℝ) → ℝ → ℂ} {B C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hc : ∀ q, Continuous (Φ q)) (hB : ∀ q, circM.map (Φ q) (CircleFubini.ballH B)ᶜ = 0)
    (hF : ∀ q, IsFrostman (circM.map (Φ q)) 1 C)
    (hmod : ∀ q q', |kernelCov2 neumannH (circM.map (Φ q), circM.map (Φ q'))
        (circM.map (Φ q), circM.map (Φ q'))| ≤ K * ‖q - q'‖ ^ (1 / 2 : ℝ)) :
    FamilyBounds (fun q => circM.map (Φ q)) (1 / 2) := by
  have hP : ∀ q, IsProbabilityMeasure (circM.map (Φ q)) := fun q =>
    (Measure.isProbabilityMeasure_map_iff (hc q).aemeasurable).2 inferInstance
  refine ⟨hP, fun R => ⟨⟨B, fun q _ => hB q⟩,
    ⟨ENNReal.ofReal (C / 1), ENNReal.ofReal_ne_top, fun q _ y => ?_⟩,
    ⟨K, hK, fun q _ q' _ => hmod q q'⟩⟩⟩
  have := hP q
  exact Thm18Asm.G1RC.frostman_pot_le (hF q) one_pos hC y

/-- **`FamilyBounds` (`β = 1/2`) for the pushed and the round families**, for `k ≥ k₀`. -/
theorem swcNA2I_familyBounds (h : SwcNA2Unif F c a x₁ x₂ y₁ y₂ ρ M m H) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, FamilyBounds (fun q => circM.map (swcPhiPush F c a k q)) (1 / 2) ∧
      FamilyBounds (fun q => circM.map (swcPhiRound F c a k q)) (1 / 2) := by
  have hρ := h.rho_pos
  have hm := h.m_pos
  obtain ⟨R₀, hR₀, hpf⟩ := swcVA_push_facts (a := x₁) (b := x₂) (d := y₂) (M := M)
    h.y_pos hρ hm
  obtain ⟨k₁, L, hL, hmd⟩ := swcNA2I_hmod h
  set M₁ := |M| / (ρ / 4) with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  obtain ⟨k₂, hk₂⟩ := swcNA2I_k0 (lt_min hR₀ (lt_min (by positivity : 0 < ρ / 2)
    (lt_min h.y_pos (by positivity : 0 < ρ / (M₁ + 1)))))
  refine ⟨max k₁ k₂, fun k hk => ?_⟩
  have hk1 : k ≥ k₁ := (le_max_left _ _).trans hk
  have hk2 : k ≥ k₂ := (le_max_right _ _).trans hk
  have hK : 0 ≤ L * 2 ^ k := by positivity
  set t := radius k with ht_def
  have ht := swcNA2I_radius_pos k
  have h2t := hk₂ k hk2
  have h2tR : 2 * t ≤ R₀ := h2t.trans (min_le_left _ _)
  have h2tρ : 2 * t ≤ ρ / 2 := h2t.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h2ty : 2 * t ≤ y₁ :=
    h2t.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h2tM : 2 * t ≤ ρ / (M₁ + 1) :=
    h2t.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hap : ∀ p : Fin n → ℝ, a p * t ≤ 2 * t := fun p =>
    mul_le_mul_of_nonneg_right (h.a_le p) ht.le
  have hap0 : ∀ p : Fin n → ℝ, 0 < a p * t := fun p => mul_pos (by linarith [h.a_ge p]) ht
  have hta : ∀ p : Fin n → ℝ, t ≤ a p * t := fun p => le_mul_of_one_le_left ht.le (h.a_ge p)
  have hmem : ∀ p : Fin n → ℝ, ∀ θ, circleMap (c p) (a p * t) θ ∈
      thickening ρ (rectC x₁ x₂ y₁ y₂) := fun p θ =>
    swcNA2I_mem_thick (h.cen p) (swcNA2I_circ_norm _ (hap0 p).le θ).le (by linarith [hap p])
  constructor
  · have hcont : ∀ q, Continuous (swcPhiPush F c a k q) := fun q => by
      rw [swcNA2I_push_eq]
      exact (h.cls q).1.continuousOn.comp_continuous (continuous_circleMap _ _) (hmem q)
    refine swcNA2I_fb_of (B := |M|) (C := 24 / (m * t)) (by positivity) hK hcont
      (fun q => ?_) (fun q => ?_) (fun q q' => (hmd k hk1 q q').1)
    · rw [Measure.map_apply (hcont q).measurable (CircleFubini.measurableSet_ballH _).compl]
      convert measure_empty (μ := circM)
      ext θ
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      have hb := (h.cls q).2.2.1 _ (hmem q θ)
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right]
        exact hb.1.trans (le_abs_self M)
      · show 0 ≤ (F q (circleMap (c q) (a q * t) θ)).im
        linarith [hb.2]
    · obtain ⟨χt, -, hχe, hχF, -⟩ := hpf (F q) (h.cls q) (c q) (h.cen q) (a q * t) (hap0 q)
        (by linarith [hap q])
      rw [swcNA2I_push_eq, swcNA2I_map_push (h.cls q) (h.cen q) (hap0 q) (by linarith [hap q])
        (by linarith [hap q, (h.cen q).2.1]), hχe]
      refine swcNA2I_frost_mono hχF ?_
      rw [div_le_div_iff₀ (mul_pos (by positivity) (hap0 q)) (by positivity)]
      have := mul_le_mul_of_nonneg_left (hta q) hm.le
      linarith
  · have hd : ∀ p : Fin n → ℝ, ‖deriv (F p) (c p)‖ ≤ M₁ := fun p =>
      swcNA2I_deriv_le hρ (h.cls p) (self_subset_thickening (by positivity) _ (h.cen p))
    have hdm : ∀ p : Fin n → ℝ, m ≤ ‖deriv (F p) (c p)‖ := fun p =>
      (h.cls p).2.2.2 (c p) (h.cen p)
    have hFc : ∀ p : Fin n → ℝ, ‖F p (c p)‖ ≤ |M| ∧ ρ ≤ (F p (c p)).im := fun p =>
      ⟨((h.cls p).2.2.1 (c p) (self_subset_thickening hρ _ (h.cen p))).1.trans (le_abs_self M),
        ((h.cls p).2.2.1 (c p) (self_subset_thickening hρ _ (h.cen p))).2⟩
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
    have hcont : ∀ q, Continuous (swcPhiRound F c a k q) := fun q => by
      rw [swcNA2I_round_eq]; exact continuous_circleMap _ _
    refine swcNA2I_fb_of (B := |M| + ρ) (C := 24 / (m * t)) (by positivity) hK hcont
      (fun q => ?_) (fun q => ?_) (fun q q' => (hmd k hk1 q q').2)
    · rw [swcNA2I_round_eq, swcNA2I_map_round (hs0 q).le ((hsmall q).trans (hFc q).2)]
      exact CircleFubini.foldedCircle_support (hs0 q).le (by linarith [hsmall q, (hFc q).1])
    · rw [swcNA2I_round_eq, swcNA2I_map_round (hs0 q).le ((hsmall q).trans (hFc q).2)]
      have := swcVA_isFrostman_push (ψ := id) measurable_id (hs0 q) one_pos
        (K := closedBall (F q (c q)) (a q * t * ‖deriv (F q) (c q)‖)) (fun x _ y _ => by simp)
        ((hsmall q).trans (hFc q).2) subset_rfl
      rw [Measure.map_id] at this
      refine swcNA2I_frost_mono this ?_
      rw [div_le_div_iff₀ (by rw [one_mul]; exact hs0 q) hmt]
      have := hlow q
      nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end NA2InstMod

end SWCore
end QuantumZipper
