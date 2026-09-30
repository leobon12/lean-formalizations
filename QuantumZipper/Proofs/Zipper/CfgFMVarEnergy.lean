import QuantumZipper.Proofs.Zipper.CfgFMVarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FM-VAR (4): the time energy node from the potential Lipschitz bound

`CfgFM.tEnergy_of_lip : TPushPotLip W T → TDisp W T → TEnergy W T`, the time analogue of
`Thm18Asm.G1FM2.g1FMEnergyStmt_of_pushPotLip` (`G1FM2Energy.lean`), whose proof is followed step
by step: the energy of a balanced pair is the integral of its potential against the pair
(`D3Plus.kernelCov2_self_eq_pot`); the pushed integrals are integrals of the potential composed
with `ψ_t` over the first-mode measures, Lipschitz on a disc containing all supports, so the
synchronous coupling `G1FM2.abs_integral_fmMeas_sub_le_on` applies; the change of map
`ψ_t → ψ_{t'}` costs `L/τ · C |t − t'|^{1/3}` (`TDisp`) in place of `L/τ · M₀ |S − S'|`. Far-apart
parameters: the parallelogram bound `G1FM2.kernelCov2_sub_le`. Own elementary argument.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped Real ENNReal NNReal

namespace QuantumZipper.E6
namespace CfgFM

open Thm18Asm Thm18Asm.G1FM2

/-- **The time energy node from `TPushPotLip` and `TDisp`.** -/
theorem tEnergy_of_lip {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hP : TPushPotLip W T) (hD : TDisp W T) : TEnergy W T := by
  intro m
  obtain ⟨M₀, M₁, rD, L, ρ₁, τ₁, hM₀, hM₁, hrD, hL, hρ₁, hτ₁, hτrD, hP⟩ := hP m
  obtain ⟨CD, hCD, hDm⟩ := hD m
  set B : ℝ := D3Plus.fmBase.real univ with hBdef
  have hB : 0 ≤ B := measureReal_nonneg
  set a : ℝ := (m : ℝ) + 1 with ha_def
  have ha : 0 < a := by positivity
  set κ : ℝ := M₁ + CD + 1 with hκ
  have hκ0 : 0 < κ := by positivity
  have hM₁κ : M₁ ≤ κ := by rw [hκ]; linarith
  have hCκ : CD ≤ κ := by rw [hκ]; linarith
  set r₂ : ℝ := min rD (min (ρ₁ / (8 * κ)) (1 / (2 * a))) with hr₂
  have hr₂0 : 0 < r₂ := lt_min hrD (lt_min (by positivity) (by positivity))
  have hr₂D : r₂ ≤ rD := min_le_left _ _
  have hr₂a : r₂ ≤ 1 / (2 * a) := (min_le_right _ _).trans (min_le_right _ _)
  have hr₂1 : r₂ ≤ 1 := by
    refine hr₂a.trans ?_
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hr₂κ : 4 * (κ * r₂) < ρ₁ := by
    have h1 : r₂ ≤ ρ₁ / (8 * κ) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : κ * r₂ ≤ κ * (ρ₁ / (8 * κ)) := mul_le_mul_of_nonneg_left h1 hκ0.le
    have h3 : κ * (ρ₁ / (8 * κ)) = ρ₁ / 8 := by field_simp
    linarith
  have hκr : 0 < κ * r₂ := mul_pos hκ0 hr₂0
  set δ₀ : ℝ := r₂ / 2 with hδ₀
  have hδ₀0 : 0 < δ₀ := by positivity
  set τ₀ : ℝ := min (min (τ₁ / 2) (r₂ / 8)) 1 with hτ₀def
  have hτ₀0 : 0 < τ₀ := lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hτ₀1 : τ₀ ≤ τ₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hτ₀2 : τ₀ ≤ r₂ / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hτ₀3 : τ₀ ≤ 1 := min_le_right _ _
  set c₀ : ℝ := 2 * B * L * κ with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  refine ⟨c₀ * (3 + 4 / δ₀), by positivity, τ₀, hτ₀0, ?_⟩
  intro u hu w w' hw hw' hwi hwi' τ τ' hτ hτ₀ hττ' hτ'τ s s' hs0 hsτ hs0' hs'τ' t ht t' ht'
  -- general facts
  have hψm : ∀ t ∈ Icc (0 : ℝ) T, Measurable (tpsi W t) := fun t ht =>
    (tpsi_psiGood hW hW0 ht.1).1
  have hfT : ∀ t ∈ Icc (0 : ℝ) T, Measurable fun z => ((1 : ℝ) : ℂ) * tpsi W t z :=
    fun t ht => measurable_const.mul (hψm t ht)
  have hnu : ∀ r : ℝ, 0 < r → ‖(r : ℂ) * u‖ = r := fun r hr => by
    rw [D3Plus.norm_ofReal_mul_unit hu, abs_of_pos hr]
  have hnu' : ∀ r : ℝ, 0 < r → ‖-((r : ℂ) * u)‖ = r := fun r hr => by rw [norm_neg, hnu r hr]
  have adm : ∀ t ∈ Icc (0 : ℝ) T, ∀ (w₀ v₀ : ℂ) (r σ : ℝ), 0 < r → ‖v₀‖ = r → 0 ≤ σ → σ ≤ r →
      2 * r < w₀.im → IsAdmissibleH (tfm W t w₀ v₀ σ) :=
    fun t ht w₀ v₀ r σ hr hv hσ hσr h2 =>
      G1FM.isAdmissibleH_pushFm (tpsi_psiGood hW hW0 ht.1) hσ (by rw [hv]; exact hr)
        (by rw [hv]; linarith) one_pos
  have imap : ∀ t ∈ Icc (0 : ℝ) T, ∀ (G : ℂ → ℝ), Measurable G → ∀ (w₀ v₀ : ℂ) (σ : ℝ),
      ∫ x, G x ∂tfm W t w₀ v₀ σ = ∫ x, G (tpsi W t x) ∂D3Plus.fmMeas w₀ v₀ σ := by
    intro t ht G hG w₀ v₀ σ
    rw [tfm, pfmMeas, integral_map (hfT t ht).aemeasurable hG.aestronglyMeasurable]
    simp only [Complex.ofReal_one, one_mul]
  have ppm : ∀ (t : ℝ) (w₀ v₀ : ℂ) (σ : ℝ), IsAdmissibleH (tfm W t w₀ v₀ σ) →
      IsAdmissibleH (tfm W t w₀ (-v₀) σ) → Measurable (pushPot (tpsi W t) 1 w₀ v₀ σ) := by
    intro t w₀ v₀ σ h1 h2
    have := h1.1
    have := h2.1
    exact (D3Plus.measurable_pot _).sub (D3Plus.measurable_pot _)
  have hreg : ∀ x ∈ closedBall w r₂, ‖x‖ ≤ 2 * a + 1 ∧ 1 / (2 * a) ≤ x.im := by
    intro x hx
    have hx' : ‖x - w‖ ≤ r₂ := by rw [← dist_eq_norm]; exact hx
    have h1 := norm_le_norm_add_norm_sub' x w
    have h2 : |(x - w).im| ≤ ‖x - w‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h2
    have h3 : 1 / a = 1 / (2 * a) + 1 / (2 * a) := by field_simp; ring
    constructor
    · linarith
    · linarith [neg_abs_le (x.im - w.im)]
  -- the pair bound
  have pair : ∀ (w₀ : ℂ) (r σ : ℝ) (t₀ : ℝ), ‖w₀‖ ≤ 2 * a → 1 / a ≤ w₀.im → 0 < r →
      r ≤ 2 * τ₀ → 0 ≤ σ → σ ≤ r → t₀ ∈ Icc (0 : ℝ) T →
      kernelCov2 neumannH (tfm W t₀ w₀ ((r : ℂ) * u) σ, tfm W t₀ w₀ (-((r : ℂ) * u)) σ)
        (tfm W t₀ w₀ ((r : ℂ) * u) σ, tfm W t₀ w₀ (-((r : ℂ) * u)) σ) ≤ c₀ := by
    intro w₀ r σ t₀ h1 h2 hr hrτ hσ hσr ht₀
    obtain ⟨hrw, hfam⟩ := hP w₀ h1 h2
    obtain ⟨-, hlip, hpot⟩ := hfam t₀ ht₀
    have hr1 : r ≤ τ₁ := by linarith
    have aP := adm t₀ ht₀ w₀ _ r σ hr (hnu r hr) hσ hσr (by linarith)
    have aN := adm t₀ ht₀ w₀ _ r σ hr (hnu' r hr) hσ hσr (by linarith)
    have e : kernelCov2 neumannH
        (tfm W t₀ w₀ ((r : ℂ) * u) σ, tfm W t₀ w₀ (-((r : ℂ) * u)) σ)
        (tfm W t₀ w₀ ((r : ℂ) * u) σ, tfm W t₀ w₀ (-((r : ℂ) * u)) σ) =
        ∫ x, pushPot (tpsi W t₀) 1 w₀ ((r : ℂ) * u) σ x ∂tfm W t₀ w₀ ((r : ℂ) * u) σ -
          ∫ x, pushPot (tpsi W t₀) 1 w₀ ((r : ℂ) * u) σ x ∂tfm W t₀ w₀ (-((r : ℂ) * u)) σ :=
      D3Plus.kernelCov2_self_eq_pot aP aN
    have hm := ppm t₀ w₀ _ σ aP aN
    rw [e, imap t₀ ht₀ _ hm, imap t₀ ht₀ _ hm]
    have psL : ∀ x ∈ closedBall w₀ r₂, ∀ x' ∈ closedBall w₀ r₂,
        ‖tpsi W t₀ x - tpsi W t₀ x'‖ ≤ M₁ * ‖x - x'‖ := fun x hx x' hx' =>
      hlip x (closedBall_subset_closedBall hr₂D hx) x' (closedBall_subset_closedBall hr₂D hx')
    have hfU : ∀ x ∈ closedBall w₀ r₂, tpsi W t₀ x ∈ ball (tpsi W t₀ w₀) ρ₁ := by
      intro x hx
      rw [mem_ball, dist_eq_norm]
      have h3 := psL x hx w₀ (mem_closedBall_self hr₂0.le)
      have hx' : ‖x - w₀‖ ≤ r₂ := by rw [← dist_eq_norm]; exact hx
      have h4 : M₁ * ‖x - w₀‖ ≤ κ * r₂ := mul_le_mul hM₁κ hx' (norm_nonneg _) hκ0.le
      linarith
    have hLipD := lip_comp (hpot u hu r σ hr hr1 hσ hσr) (by positivity) psL hfU
    have hsub : ∀ v₀ : ℂ, ‖v₀‖ = r → closedBall w₀ (‖v₀‖ + σ) ⊆ closedBall w₀ r₂ :=
      fun v₀ hv => closedBall_subset_closedBall (by rw [hv]; linarith)
    have hc := abs_integral_fmMeas_sub_le_on (by positivity) hLipD hσ hσ
      (by rw [hnu r hr]; linarith) (by rw [hnu' r hr]; linarith) (hsub _ (hnu r hr))
      (hsub _ (hnu' r hr))
    have e2 : ‖(r : ℂ) * u - -((r : ℂ) * u)‖ = 2 * r := by
      rw [sub_neg_eq_add, ← two_mul, norm_mul, hnu r hr]; norm_num
    rw [sub_self, norm_zero, sub_self, abs_zero, e2] at hc
    have e3 : D3Plus.fmBase.real univ * (L / r * M₁ * (0 + 2 * r + 0)) =
        2 * B * L * M₁ := by rw [hBdef]; field_simp; ring
    rw [e3] at hc
    have : 2 * B * L * M₁ ≤ c₀ := mul_le_mul_of_nonneg_left hM₁κ (by positivity)
    exact (le_abs_self _).trans (hc.trans this)
  -- the four measures
  have hτ' : 0 < τ' := by linarith
  have hτ1 : τ ≤ τ₁ := by linarith
  have hτ'1 : τ' ≤ τ₁ := by linarith
  obtain ⟨hrw, hfam⟩ := hP w hw hwi
  obtain ⟨hbd, hlip, hpot⟩ := hfam t ht
  obtain ⟨hrw', hfam'⟩ := hP w' hw' hwi'
  obtain ⟨-, hlip', hpot'⟩ := hfam' t' ht'
  obtain ⟨-, hlipw, -⟩ := hfam t' ht'
  have aP := adm t ht w _ τ s hτ (hnu τ hτ) hs0 hsτ (by linarith)
  have aN := adm t ht w _ τ s hτ (hnu' τ hτ) hs0 hsτ (by linarith)
  have aP' := adm t' ht' w' _ τ' s' hτ' (hnu τ' hτ') hs0' hs'τ' (by linarith)
  have aN' := adm t' ht' w' _ τ' s' hτ' (hnu' τ' hτ') hs0' hs'τ' (by linarith)
  constructor
  · have h13' : 0 ≤ 4 / δ₀ := by positivity
    have h13 : 1 ≤ 3 + 4 / δ₀ := by linarith
    exact (pair w τ s t hw hwi hτ (by linarith) hs0 hsτ ht).trans
      (le_mul_of_one_le_right hc₀0 h13)
  set e3 : ℝ := |t - t'| ^ ((1 : ℝ) / 3) with he3
  have he30 : 0 ≤ e3 := Real.rpow_nonneg (abs_nonneg _) _
  set Δ := ‖w - w'‖ + |τ - τ'| + |s - s'| + e3 with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  rcases le_or_gt Δ δ₀ with hsm | hlg
  swap
  · -- far apart: parallelogram
    have hmass : ∀ t₀ ∈ Icc (0 : ℝ) T, ∀ (w₀ v₀ : ℂ) (σ : ℝ),
        tfm W t₀ w₀ v₀ σ univ = tfm W t₀ w₀ (-v₀) σ univ := fun t₀ ht₀ w₀ v₀ σ => by
      rw [tfm, tfm, G1FM.pfmMeas_univ (hψm t₀ ht₀), G1FM.pfmMeas_univ (hψm t₀ ht₀)]
    have k := kernelCov2_sub_le aP aN aP' aN' (hmass _ ht _ _ _) (hmass _ ht' _ _ _)
    have p1 := pair w τ s t hw hwi hτ (by linarith) hs0 hsτ ht
    have p2 := pair w' τ' s' t' hw' hwi' hτ' (by linarith) hs0' hs'τ' ht'
    have hΔτ : δ₀ ≤ Δ / τ := by
      rw [le_div_iff₀ hτ]
      have : δ₀ * τ ≤ δ₀ * 1 := mul_le_mul_of_nonneg_left (by linarith) hδ₀0.le
      linarith
    have h4 : 4 ≤ (3 + 4 / δ₀) * (Δ / τ) := by
      have h5 : 4 / δ₀ * δ₀ = 4 := div_mul_cancel₀ _ hδ₀0.ne'
      have h6 : 4 / δ₀ * δ₀ ≤ 4 / δ₀ * (Δ / τ) :=
        mul_le_mul_of_nonneg_left hΔτ (by positivity)
      have h7 : 0 ≤ 3 * (Δ / τ) := by positivity
      have e : (3 + 4 / δ₀) * (Δ / τ) = 3 * (Δ / τ) + 4 / δ₀ * (Δ / τ) := by ring
      linarith
    have h8 : c₀ * 4 ≤ c₀ * ((3 + 4 / δ₀) * (Δ / τ)) := mul_le_mul_of_nonneg_left h4 hc₀0
    have e : c₀ * (3 + 4 / δ₀) * Δ / τ = c₀ * ((3 + 4 / δ₀) * (Δ / τ)) := by ring
    rw [e]
    linarith
  -- close parameters: synchronous coupling
  have hdw : ‖w - w'‖ ≤ δ₀ := by
    have := abs_nonneg (τ - τ'); have := abs_nonneg (s - s')
    linarith
  have hdS : e3 ≤ δ₀ := by
    have := norm_nonneg (w - w'); have := abs_nonneg (τ - τ'); have := abs_nonneg (s - s')
    linarith
  have hDD : closedBall w r₂ ⊆ closedBall w rD := closedBall_subset_closedBall hr₂D
  have hw'D : w' ∈ closedBall w rD := by
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; linarith
  have hw'2 : w' ∈ closedBall w r₂ := by
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; linarith
  have sup1 : ∀ v : ℂ, ‖v‖ = τ → closedBall w (‖v‖ + s) ⊆ closedBall w r₂ :=
    fun v hv => closedBall_subset_closedBall (by rw [hv]; linarith)
  have sup2 : ∀ v : ℂ, ‖v‖ = τ' → closedBall w' (‖v‖ + s') ⊆ closedBall w r₂ :=
    fun v hv => closedBall_subset_closedBall' (by
      rw [hv, dist_eq_norm, norm_sub_rev]; linarith)
  have dT : ∀ x ∈ closedBall w r₂, ‖tpsi W t x - tpsi W t' x‖ ≤ CD * e3 := fun x hx =>
    hDm t ht t' ht' x (hreg x hx).1 (hreg x hx).2
  have psL : ∀ x ∈ closedBall w r₂, ∀ x' ∈ closedBall w r₂,
      ‖tpsi W t x - tpsi W t x'‖ ≤ M₁ * ‖x - x'‖ := fun x hx x' hx' =>
    hlip x (hDD hx) x' (hDD hx')
  set U := ball (tpsi W t w) ρ₁ ∩ ball (tpsi W t' w') ρ₁ with hUdef
  have hU : ∀ x ∈ closedBall w r₂, tpsi W t x ∈ U ∧ tpsi W t' x ∈ U := by
    intro x hx
    have hx' : ‖x - w‖ ≤ r₂ := by rw [← dist_eq_norm]; exact hx
    have hxw' : ‖x - w'‖ ≤ 2 * r₂ := by
      have := norm_sub_le_norm_sub_add_norm_sub x w w'
      linarith
    have A1 : ‖tpsi W t x - tpsi W t w‖ ≤ κ * r₂ :=
      (psL x hx w (mem_closedBall_self hr₂0.le)).trans
        (mul_le_mul hM₁κ hx' (norm_nonneg _) hκ0.le)
    have A2 : ‖tpsi W t x - tpsi W t' x‖ ≤ κ * r₂ :=
      (dT x hx).trans (mul_le_mul hCκ (hdS.trans (by linarith)) he30 hκ0.le)
    have A3 : ‖tpsi W t' x - tpsi W t' w'‖ ≤ κ * (2 * r₂) :=
      (hlipw x (hDD hx) w' hw'D).trans (mul_le_mul hM₁κ hxw' (norm_nonneg _) hκ0.le)
    have t1 := norm_sub_le_norm_sub_add_norm_sub (tpsi W t x) (tpsi W t' x) (tpsi W t' w')
    have t2 := norm_sub_le_norm_sub_add_norm_sub (tpsi W t' x) (tpsi W t x) (tpsi W t w)
    rw [norm_sub_rev (tpsi W t' x) (tpsi W t x)] at t2
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> rw [mem_ball, dist_eq_norm] <;> linarith
  have hτw : τ ≤ w.im := by linarith
  have hτw' : τ' ≤ w'.im := by linarith
  set Kg : ℝ := L / τ + L / τ' with hKg
  have hKg0 : 0 ≤ Kg := by positivity
  have hKg3 : Kg ≤ 3 * L / τ := by
    have : L / τ' ≤ 2 * L / τ := by
      rw [div_le_div_iff₀ hτ' hτ]
      calc L * τ ≤ L * (2 * τ') := mul_le_mul_of_nonneg_left hττ' hL
        _ = 2 * L * τ' := by ring
    rw [hKg]
    have e : 3 * L / τ = L / τ + 2 * L / τ := by ring
    linarith
  set Φ : ℂ → ℝ := fun p => pushPot (tpsi W t) 1 w ((τ : ℂ) * u) s p -
    pushPot (tpsi W t') 1 w' ((τ' : ℂ) * u) s' p with hΦ
  have hΦL : ∀ p ∈ U, ∀ p' ∈ U, |Φ p - Φ p'| ≤ Kg * ‖p - p'‖ := by
    intro p hp p' hp'
    have a1 := hpot u hu τ s hτ hτ1 hs0 hsτ p hp.1 p' hp'.1
    have a2 := hpot' u hu τ' s' hτ' hτ'1 hs0' hs'τ' p hp.2 p' hp'.2
    have : Φ p - Φ p' = (pushPot (tpsi W t) 1 w ((τ : ℂ) * u) s p -
        pushPot (tpsi W t) 1 w ((τ : ℂ) * u) s p') -
        (pushPot (tpsi W t') 1 w' ((τ' : ℂ) * u) s' p -
          pushPot (tpsi W t') 1 w' ((τ' : ℂ) * u) s' p') := by
      simp only [hΦ]; ring
    rw [this, hKg, add_mul]
    exact (abs_sub _ _).trans (add_le_add a1 a2)
  have hΦm : Measurable Φ := (ppm _ _ _ _ aP aN).sub (ppm _ _ _ _ aP' aN')
  have intΦ : ∀ {M : Measure ℂ}, IsAdmissibleH M → Integrable Φ M := fun hM =>
    ((integrable_pot hM aP).sub (integrable_pot hM aN)).sub
      ((integrable_pot hM aP').sub (integrable_pot hM aN'))
  have hpotE : (fun x => (∫ y, neumannH x y ∂(tfm W t w ((τ : ℂ) * u) s +
      tfm W t' w' (-((τ' : ℂ) * u)) s')) - ∫ y, neumannH x y ∂(tfm W t w
      (-((τ : ℂ) * u)) s + tfm W t' w' ((τ' : ℂ) * u) s')) = Φ := by
    funext x
    rw [pot_add aP aN' x, pot_add aN aP' x]
    simp only [hΦ, pushPot]
    ring
  rw [D3Plus.kernelCov2_self_eq_pot (isAdmissibleH_add aP aN') (isAdmissibleH_add aN aP'), hpotE,
    integral_add_measure (intΦ aP) (intΦ aN'), integral_add_measure (intΦ aN) (intΦ aP')]
  -- one sign
  have one : ∀ v v' : ℂ, ‖v‖ = τ → ‖v'‖ = τ' → ‖v - v'‖ = |τ - τ'| →
      IsAdmissibleH (tfm W t w' v' s') →
      |∫ x, Φ x ∂tfm W t w v s - ∫ x, Φ x ∂tfm W t' w' v' s'| ≤
        B * (3 * L / τ * κ * Δ) := by
    intro v v' hv hv' hvv a3
    rw [imap t ht Φ hΦm, imap t' ht' Φ hΦm]
    have hLD := lip_comp hΦL hKg0 psL (fun x hx => (hU x hx).1)
    have hvw : ‖v‖ ≤ w.im := by rw [hv]; exact hτw
    have hvw' : ‖v'‖ ≤ w'.im := by rw [hv']; exact hτw'
    have c1 := abs_integral_fmMeas_sub_le_on (F := fun x => Φ (tpsi W t x))
      (mul_nonneg hKg0 hM₁) hLD hs0 hs0' hvw hvw' (sup1 v hv) (sup2 v' hv')
    rw [hvv] at c1
    have : IsFiniteMeasure (D3Plus.fmMeas w' v' s') :=
      CircleFubini.isFiniteMeasure_bind_circle _
    have i1 : Integrable (fun x => Φ (tpsi W t x)) (D3Plus.fmMeas w' v' s') := by
      have := (integrable_map_measure hΦm.aestronglyMeasurable (hfT t ht).aemeasurable).1
        (intΦ a3)
      simpa only [Function.comp_def, Complex.ofReal_one, one_mul] using this
    have i2 : Integrable (fun x => Φ (tpsi W t' x)) (D3Plus.fmMeas w' v' s') := by
      have := (integrable_map_measure hΦm.aestronglyMeasurable (hfT t' ht').aemeasurable).1
        (intΦ (adm t' ht' w' v' τ' s' hτ' hv' hs0' hs'τ' (by linarith)))
      simpa only [Function.comp_def, Complex.ofReal_one, one_mul] using this
    have c2 : ‖∫ x, (Φ (tpsi W t x) - Φ (tpsi W t' x)) ∂D3Plus.fmMeas w' v' s'‖ ≤
        Kg * (CD * e3) * (D3Plus.fmMeas w' v' s').real univ := by
      refine norm_integral_le_of_norm_le_const ?_
      filter_upwards [G1FM.ae_dist_fmMeas_le hs0' hvw'] with x hx
      have hxD : x ∈ closedBall w r₂ := sup2 v' hv' (mem_closedBall.2 hx)
      rw [Real.norm_eq_abs]
      exact (hΦL _ (hU x hxD).1 _ (hU x hxD).2).trans
        (mul_le_mul_of_nonneg_left (dT x hxD) hKg0)
    rw [integral_sub i1 i2, Real.norm_eq_abs] at c2
    have hμB : (D3Plus.fmMeas w' v' s').real univ = B := by
      rw [hBdef, measureReal_def, measureReal_def, D3Plus.fmMeas_univ]
    rw [hμB] at c2
    set X := ‖w - w'‖ + |τ - τ'| + |s - s'| with hX
    have hX0 : 0 ≤ X := by positivity
    have t1 : B * (Kg * M₁ * X) ≤ B * Kg * X * κ := by
      calc B * (Kg * M₁ * X) = B * Kg * X * M₁ := by ring
        _ ≤ B * Kg * X * κ := mul_le_mul_of_nonneg_left hM₁κ (by positivity)
    have t2 : Kg * (CD * e3) * B ≤ B * Kg * e3 * κ := by
      calc Kg * (CD * e3) * B = B * Kg * e3 * CD := by ring
        _ ≤ B * Kg * e3 * κ := mul_le_mul_of_nonneg_left hCκ (by positivity)
    have t3 : B * Kg * κ * Δ ≤ B * (3 * L / τ * κ * Δ) := by
      calc B * Kg * κ * Δ = B * κ * Δ * Kg := by ring
        _ ≤ B * κ * Δ * (3 * L / τ) := mul_le_mul_of_nonneg_left hKg3 (by positivity)
        _ = B * (3 * L / τ * κ * Δ) := by ring
    have e : B * Kg * X * κ + B * Kg * e3 * κ = B * Kg * κ * Δ := by rw [hΔ, hX]; ring
    have hsplit : ∫ x, Φ (tpsi W t x) ∂D3Plus.fmMeas w v s -
        ∫ x, Φ (tpsi W t' x) ∂D3Plus.fmMeas w' v' s' =
        (∫ x, Φ (tpsi W t x) ∂D3Plus.fmMeas w v s -
          ∫ x, Φ (tpsi W t x) ∂D3Plus.fmMeas w' v' s') +
        (∫ x, Φ (tpsi W t x) ∂D3Plus.fmMeas w' v' s' -
          ∫ x, Φ (tpsi W t' x) ∂D3Plus.fmMeas w' v' s') := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have c1' : |∫ x, Φ (tpsi W t x) ∂D3Plus.fmMeas w v s -
        ∫ x, Φ (tpsi W t x) ∂D3Plus.fmMeas w' v' s'| ≤ B * (Kg * M₁ * X) := c1
    linarith
  have o1 := one _ _ (hnu τ hτ) (hnu τ' hτ') (by
      rw [show (τ : ℂ) * u - (τ' : ℂ) * u = ((τ - τ' : ℝ) : ℂ) * u by push_cast; ring,
        D3Plus.norm_ofReal_mul_unit hu])
    (adm t ht w' _ τ' s' hτ' (hnu τ' hτ') hs0' hs'τ' (by linarith))
  have o2 := one _ _ (hnu' τ hτ) (hnu' τ' hτ') (by
      rw [show -((τ : ℂ) * u) - -((τ' : ℂ) * u) = ((τ' - τ : ℝ) : ℂ) * u by push_cast; ring,
        D3Plus.norm_ofReal_mul_unit hu, abs_sub_comm])
    (adm t ht w' _ τ' s' hτ' (hnu' τ' hτ') hs0' hs'τ' (by linarith))
  have key : (∫ x, Φ x ∂tfm W t w ((τ : ℂ) * u) s +
      ∫ x, Φ x ∂tfm W t' w' (-((τ' : ℂ) * u)) s') -
      (∫ x, Φ x ∂tfm W t w (-((τ : ℂ) * u)) s +
        ∫ x, Φ x ∂tfm W t' w' ((τ' : ℂ) * u) s') ≤ 2 * (B * (3 * L / τ * κ * Δ)) := by
    have := le_abs_self (∫ x, Φ x ∂tfm W t w ((τ : ℂ) * u) s -
      ∫ x, Φ x ∂tfm W t' w' ((τ' : ℂ) * u) s')
    have := neg_abs_le (∫ x, Φ x ∂tfm W t w (-((τ : ℂ) * u)) s -
      ∫ x, Φ x ∂tfm W t' w' (-((τ' : ℂ) * u)) s')
    linarith
  have fin : 2 * (B * (3 * L / τ * κ * Δ)) ≤ c₀ * (3 + 4 / δ₀) * Δ / τ := by
    have e1 : 2 * (B * (3 * L / τ * κ * Δ)) = c₀ * 3 * (Δ / τ) := by rw [hc₀]; ring
    have h10 : c₀ * (3 + 4 / δ₀) * Δ / τ = c₀ * 3 * (Δ / τ) + c₀ * (4 / δ₀) * (Δ / τ) := by
      ring
    have h11 : 0 ≤ c₀ * (4 / δ₀) * (Δ / τ) := by positivity
    rw [e1, h10]; linarith
  exact key.trans fin

end CfgFM
end QuantumZipper.E6
