import QuantumZipper.Proofs.Thm18.G1FM2EnergyLem

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1FM2-ENERGY (2): node G1-FM-ENERGY from the Lipschitz bound of the pushed potential

`G1FM2.g1FMEnergyStmt_of_pushPotLip : (∀ ψ, PsiGood ψ → PushPotLip ψ) → G1FMEnergyStmt`.

As `D3Plus.n2ZFMEnergy_of_potLip`: the energy of a balanced admissible pair is the integral of its
potential against the pair (`D3Plus.kernelCov2_self_eq_pot`); the pushed integrals are integrals
over the first-mode measures of the potential composed with `S ψ` (`integral_map`), which is
Lipschitz on a disc containing all supports (Lipschitz bound of `ψ` and `L/τ` bound of the
potential on a ball around `S ψ(w)`), so the synchronous coupling
`G1FM2.abs_integral_fmMeas_sub_le_on` applies; the change `S → S'` costs `L/τ · M₀ |S − S'|`.
For far-apart parameters the parallelogram bound `G1FM2.kernelCov2_sub_le` and the pair bound
give the increment bound. Own elementary argument.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped Real ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM2

theorem lip_comp {G : ℂ → ℝ} {U : Set ℂ} {Kg : ℝ}
    (hG : ∀ p ∈ U, ∀ p' ∈ U, |G p - G p'| ≤ Kg * ‖p - p'‖) (hKg : 0 ≤ Kg) {g : ℂ → ℂ}
    {D : Set ℂ} {Kf : ℝ} (hg : ∀ x ∈ D, ∀ x' ∈ D, ‖g x - g x'‖ ≤ Kf * ‖x - x'‖)
    (hgD : ∀ x ∈ D, g x ∈ U) :
    ∀ x ∈ D, ∀ x' ∈ D, |G (g x) - G (g x')| ≤ Kg * Kf * ‖x - x'‖ := by
  intro x hx x' hx'
  calc |G (g x) - G (g x')| ≤ Kg * ‖g x - g x'‖ := hG _ (hgD x hx) _ (hgD x' hx')
    _ ≤ Kg * (Kf * ‖x - x'‖) := mul_le_mul_of_nonneg_left (hg x hx x' hx') hKg
    _ = Kg * Kf * ‖x - x'‖ := by ring

/-- **Node G1-FM-ENERGY from `PushPotLip`.** -/
theorem g1FMEnergyStmt_of_pushPotLip (h : ∀ ψ : ℂ → ℂ, G1RC.PsiGood ψ → PushPotLip ψ) :
    G1FMEnergyStmt := by
  intro ψ hψ m
  obtain ⟨M₀, M₁, rD, L, ρ₁, τ₁, hM₀, hM₁, hrD, hL, hρ₁, hτ₁, hτrD, hP⟩ := h ψ hψ m
  have hψm : Measurable ψ := hψ.1
  set B : ℝ := D3Plus.fmBase.real univ with hBdef
  have hB : 0 ≤ B := measureReal_nonneg
  set a : ℝ := (m : ℝ) + 1 with ha_def
  have ha : 0 < a := by positivity
  set κ : ℝ := a * M₁ + M₀ + 1 with hκ
  have hκ0 : 0 < κ := by positivity
  have haM : a * M₁ ≤ κ := by rw [hκ]; linarith
  have hM₀κ : M₀ ≤ κ := by rw [hκ]; nlinarith [mul_nonneg ha.le hM₁]
  set r₂ : ℝ := min rD (ρ₁ / (8 * κ)) with hr₂
  have hr₂0 : 0 < r₂ := lt_min hrD (by positivity)
  have hr₂D : r₂ ≤ rD := min_le_left _ _
  have hr₂κ : 4 * (κ * r₂) < ρ₁ := by
    have h1 : r₂ ≤ ρ₁ / (8 * κ) := min_le_right _ _
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
  intro u hu w w' hw hw' hwi hwi' τ τ' hτ hτ₀ hττ' hτ'τ s s' hs0 hsτ hs0' hs'τ' S S' hS hS'
  -- general facts
  have hSa : ∀ T ∈ Icc (1 / a) a, 0 < T ∧ T ≤ a := fun T hT =>
    ⟨lt_of_lt_of_le (by positivity) hT.1, hT.2⟩
  have nT : ∀ (T : ℝ) (y z : ℂ), ‖(T : ℂ) * ψ y - (T : ℂ) * ψ z‖ = |T| * ‖ψ y - ψ z‖ :=
    fun T y z => by rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have nT' : ∀ (T T' : ℝ) (y : ℂ), ‖(T : ℂ) * ψ y - (T' : ℂ) * ψ y‖ = |T - T'| * ‖ψ y‖ :=
    fun T T' y => by rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  have hfT : ∀ T : ℝ, Measurable fun z => (T : ℂ) * ψ z := fun T => measurable_const.mul hψm
  have hnu : ∀ t : ℝ, 0 < t → ‖(t : ℂ) * u‖ = t := fun t ht => by
    rw [D3Plus.norm_ofReal_mul_unit hu, abs_of_pos ht]
  have hnu' : ∀ t : ℝ, 0 < t → ‖-((t : ℂ) * u)‖ = t := fun t ht => by rw [norm_neg, hnu t ht]
  have adm : ∀ (w₀ v₀ : ℂ) (t σ T : ℝ), 0 < t → ‖v₀‖ = t → 0 ≤ σ → σ ≤ t → 2 * t < w₀.im →
      0 < T → IsAdmissibleH (pfmMeas ψ T w₀ v₀ σ) :=
    fun w₀ v₀ t σ T ht hv hσ hσt h2 hT =>
      G1FM.isAdmissibleH_pushFm hψ hσ (by rw [hv]; exact ht) (by rw [hv]; linarith) hT
  have imap : ∀ (G : ℂ → ℝ), Measurable G → ∀ (T : ℝ) (w₀ v₀ : ℂ) (σ : ℝ),
      ∫ x, G x ∂pfmMeas ψ T w₀ v₀ σ = ∫ x, G ((T : ℂ) * ψ x) ∂D3Plus.fmMeas w₀ v₀ σ :=
    fun G hG T w₀ v₀ σ => integral_map (hfT T).aemeasurable hG.aestronglyMeasurable
  have ppm : ∀ (T : ℝ) (w₀ v₀ : ℂ) (σ : ℝ), IsAdmissibleH (pfmMeas ψ T w₀ v₀ σ) →
      IsAdmissibleH (pfmMeas ψ T w₀ (-v₀) σ) → Measurable (pushPot ψ T w₀ v₀ σ) := by
    intro T w₀ v₀ σ h1 h2
    have := h1.1
    have := h2.1
    exact (D3Plus.measurable_pot _).sub (D3Plus.measurable_pot _)
  have psL : ∀ w₀ : ℂ, (∀ x ∈ closedBall w₀ rD, ∀ x' ∈ closedBall w₀ rD,
      ‖ψ x - ψ x'‖ ≤ M₁ * ‖x - x'‖) → ∀ T ∈ Icc (1 / a) a, ∀ x ∈ closedBall w₀ r₂,
      ∀ x' ∈ closedBall w₀ r₂, ‖(T : ℂ) * ψ x - (T : ℂ) * ψ x'‖ ≤ (a * M₁) * ‖x - x'‖ := by
    intro w₀ hl T hT x hx x' hx'
    obtain ⟨hT0, hTa⟩ := hSa T hT
    rw [nT, abs_of_pos hT0]
    calc T * ‖ψ x - ψ x'‖ ≤ a * (M₁ * ‖x - x'‖) :=
          mul_le_mul hTa (hl x (closedBall_subset_closedBall hr₂D hx) x'
            (closedBall_subset_closedBall hr₂D hx')) (norm_nonneg _) ha.le
      _ = a * M₁ * ‖x - x'‖ := by ring
  -- the pair bound
  have pair : ∀ (w₀ : ℂ) (t σ T : ℝ), ‖w₀‖ ≤ 2 * a → 1 / a ≤ w₀.im → 0 < t → t ≤ 2 * τ₀ →
      0 ≤ σ → σ ≤ t → T ∈ Icc (1 / a) a →
      kernelCov2 neumannH (pfmMeas ψ T w₀ ((t : ℂ) * u) σ, pfmMeas ψ T w₀ (-((t : ℂ) * u)) σ)
        (pfmMeas ψ T w₀ ((t : ℂ) * u) σ, pfmMeas ψ T w₀ (-((t : ℂ) * u)) σ) ≤ c₀ := by
    intro w₀ t σ T h1 h2 ht htτ hσ hσt hT
    obtain ⟨hrw, -, hlip, hpot⟩ := hP w₀ h1 h2
    obtain ⟨hT0, hTa⟩ := hSa T hT
    have ht1 : t ≤ τ₁ := by linarith
    have aP := adm w₀ _ t σ T ht (hnu t ht) hσ hσt (by linarith) hT0
    have aN := adm w₀ _ t σ T ht (hnu' t ht) hσ hσt (by linarith) hT0
    have e : kernelCov2 neumannH
        (pfmMeas ψ T w₀ ((t : ℂ) * u) σ, pfmMeas ψ T w₀ (-((t : ℂ) * u)) σ)
        (pfmMeas ψ T w₀ ((t : ℂ) * u) σ, pfmMeas ψ T w₀ (-((t : ℂ) * u)) σ) =
        ∫ x, pushPot ψ T w₀ ((t : ℂ) * u) σ x ∂pfmMeas ψ T w₀ ((t : ℂ) * u) σ -
          ∫ x, pushPot ψ T w₀ ((t : ℂ) * u) σ x ∂pfmMeas ψ T w₀ (-((t : ℂ) * u)) σ :=
      D3Plus.kernelCov2_self_eq_pot aP aN
    have hm := ppm T w₀ _ σ aP aN
    rw [e, imap _ hm, imap _ hm]
    have hfU : ∀ x ∈ closedBall w₀ r₂, (T : ℂ) * ψ x ∈ ball ((T : ℂ) * ψ w₀) ρ₁ := by
      intro x hx
      rw [mem_ball, dist_eq_norm]
      have h3 := psL w₀ hlip T hT x hx w₀ (mem_closedBall_self hr₂0.le)
      have hx' : ‖x - w₀‖ ≤ r₂ := by rw [← dist_eq_norm]; exact hx
      have h4 : a * M₁ * ‖x - w₀‖ ≤ κ * r₂ :=
        mul_le_mul haM hx' (norm_nonneg _) hκ0.le
      linarith
    have hLipD := lip_comp (hpot u hu T hT t σ ht ht1 hσ hσt) (by positivity)
      (psL w₀ hlip T hT) hfU
    have hsub : ∀ v₀ : ℂ, ‖v₀‖ = t → closedBall w₀ (‖v₀‖ + σ) ⊆ closedBall w₀ r₂ :=
      fun v₀ hv => closedBall_subset_closedBall (by rw [hv]; linarith)
    have hc := abs_integral_fmMeas_sub_le_on (by positivity) hLipD hσ hσ
      (by rw [hnu t ht]; linarith) (by rw [hnu' t ht]; linarith) (hsub _ (hnu t ht))
      (hsub _ (hnu' t ht))
    have e2 : ‖(t : ℂ) * u - -((t : ℂ) * u)‖ = 2 * t := by
      rw [sub_neg_eq_add, ← two_mul, norm_mul, hnu t ht]; norm_num
    rw [sub_self, norm_zero, sub_self, abs_zero, e2] at hc
    have e3 : D3Plus.fmBase.real univ * (L / t * (a * M₁) * (0 + 2 * t + 0)) =
        2 * B * L * (a * M₁) := by rw [hBdef]; field_simp; ring
    rw [e3] at hc
    have : 2 * B * L * (a * M₁) ≤ c₀ :=
      mul_le_mul_of_nonneg_left haM (by positivity)
    exact (le_abs_self _).trans (hc.trans this)
  -- the four measures
  have hτ' : 0 < τ' := by linarith
  have hτ1 : τ ≤ τ₁ := by linarith
  have hτ'1 : τ' ≤ τ₁ := by linarith
  obtain ⟨hS0, hSa1⟩ := hSa S hS
  obtain ⟨hS0', hSa1'⟩ := hSa S' hS'
  obtain ⟨hrw, hbd, hlip, hpot⟩ := hP w hw hwi
  obtain ⟨hrw', -, hlip', hpot'⟩ := hP w' hw' hwi'
  have aP := adm w _ τ s S hτ (hnu τ hτ) hs0 hsτ (by linarith) hS0
  have aN := adm w _ τ s S hτ (hnu' τ hτ) hs0 hsτ (by linarith) hS0
  have aP' := adm w' _ τ' s' S' hτ' (hnu τ' hτ') hs0' hs'τ' (by linarith) hS0'
  have aN' := adm w' _ τ' s' S' hτ' (hnu' τ' hτ') hs0' hs'τ' (by linarith) hS0'
  constructor
  · have h13' : 0 ≤ 4 / δ₀ := by positivity
    have h13 : 1 ≤ 3 + 4 / δ₀ := by linarith
    exact (pair w τ s S hw hwi hτ (by linarith) hs0 hsτ hS).trans
      (le_mul_of_one_le_right hc₀0 h13)
  set Δ := ‖w - w'‖ + |τ - τ'| + |s - s'| + |S - S'| with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  rcases le_or_gt Δ δ₀ with hsm | hlg
  swap
  · -- far apart: parallelogram
    have hmass : ∀ (T : ℝ) (w₀ v₀ : ℂ) (σ : ℝ),
        pfmMeas ψ T w₀ v₀ σ univ = pfmMeas ψ T w₀ (-v₀) σ univ := fun T w₀ v₀ σ => by
      rw [G1FM.pfmMeas_univ hψm, G1FM.pfmMeas_univ hψm]
    have k := kernelCov2_sub_le aP aN aP' aN' (hmass _ _ _ _) (hmass _ _ _ _)
    have p1 := pair w τ s S hw hwi hτ (by linarith) hs0 hsτ hS
    have p2 := pair w' τ' s' S' hw' hwi' hτ' (by linarith) hs0' hs'τ' hS'
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
    have := abs_nonneg (τ - τ'); have := abs_nonneg (s - s'); have := abs_nonneg (S - S')
    linarith
  have hdS : |S - S'| ≤ δ₀ := by
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
  have dT : ∀ x ∈ closedBall w rD, ‖(S : ℂ) * ψ x - (S' : ℂ) * ψ x‖ ≤ M₀ * |S - S'| := by
    intro x hx
    rw [nT', mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd x hx) (abs_nonneg _)
  set U := ball ((S : ℂ) * ψ w) ρ₁ ∩ ball ((S' : ℂ) * ψ w') ρ₁ with hUdef
  have hU : ∀ x ∈ closedBall w r₂, (S : ℂ) * ψ x ∈ U ∧ (S' : ℂ) * ψ x ∈ U := by
    intro x hx
    have hx' : ‖x - w‖ ≤ r₂ := by rw [← dist_eq_norm]; exact hx
    have hxw' : ‖x - w'‖ ≤ 2 * r₂ := by
      have := norm_sub_le_norm_sub_add_norm_sub x w w'
      linarith
    have A1 : ‖(S : ℂ) * ψ x - (S : ℂ) * ψ w‖ ≤ κ * r₂ :=
      (psL w hlip S hS x hx w (mem_closedBall_self hr₂0.le)).trans
        (mul_le_mul haM hx' (norm_nonneg _) hκ0.le)
    have A2 : ‖(S : ℂ) * ψ x - (S' : ℂ) * ψ x‖ ≤ κ * r₂ :=
      (dT x (hDD hx)).trans (mul_le_mul hM₀κ (hdS.trans (by linarith)) (abs_nonneg _) hκ0.le)
    have A3 : ‖(S' : ℂ) * ψ x - (S' : ℂ) * ψ w'‖ ≤ κ * (2 * r₂) := by
      obtain ⟨hS0'', hSa''⟩ := hSa S' hS'
      rw [nT, abs_of_pos hS0'']
      calc S' * ‖ψ x - ψ w'‖ ≤ a * (M₁ * ‖x - w'‖) :=
            mul_le_mul hSa'' (hlip x (hDD hx) w' hw'D) (norm_nonneg _) ha.le
        _ = a * M₁ * ‖x - w'‖ := by ring
        _ ≤ κ * (2 * r₂) := mul_le_mul haM hxw' (norm_nonneg _) hκ0.le
    have t1 := norm_sub_le_norm_sub_add_norm_sub ((S : ℂ) * ψ x) ((S' : ℂ) * ψ x)
      ((S' : ℂ) * ψ w')
    have t2 := norm_sub_le_norm_sub_add_norm_sub ((S' : ℂ) * ψ x) ((S : ℂ) * ψ x)
      ((S : ℂ) * ψ w)
    rw [norm_sub_rev ((S' : ℂ) * ψ x) ((S : ℂ) * ψ x)] at t2
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
  set Φ : ℂ → ℝ := fun p => pushPot ψ S w ((τ : ℂ) * u) s p -
    pushPot ψ S' w' ((τ' : ℂ) * u) s' p with hΦ
  have hΦL : ∀ p ∈ U, ∀ p' ∈ U, |Φ p - Φ p'| ≤ Kg * ‖p - p'‖ := by
    intro p hp p' hp'
    have a1 := hpot u hu S hS τ s hτ hτ1 hs0 hsτ p hp.1 p' hp'.1
    have a2 := hpot' u hu S' hS' τ' s' hτ' hτ'1 hs0' hs'τ' p hp.2 p' hp'.2
    have : Φ p - Φ p' = (pushPot ψ S w ((τ : ℂ) * u) s p - pushPot ψ S w ((τ : ℂ) * u) s p') -
        (pushPot ψ S' w' ((τ' : ℂ) * u) s' p - pushPot ψ S' w' ((τ' : ℂ) * u) s' p') := by
      simp only [hΦ]; ring
    rw [this, hKg, add_mul]
    exact (abs_sub _ _).trans (add_le_add a1 a2)
  have hΦm : Measurable Φ := (ppm _ _ _ _ aP aN).sub (ppm _ _ _ _ aP' aN')
  have intΦ : ∀ {M : Measure ℂ}, IsAdmissibleH M → Integrable Φ M := fun hM =>
    ((integrable_pot hM aP).sub (integrable_pot hM aN)).sub
      ((integrable_pot hM aP').sub (integrable_pot hM aN'))
  have hpotE : (fun x => (∫ y, neumannH x y ∂(pfmMeas ψ S w ((τ : ℂ) * u) s +
      pfmMeas ψ S' w' (-((τ' : ℂ) * u)) s')) - ∫ y, neumannH x y ∂(pfmMeas ψ S w
      (-((τ : ℂ) * u)) s + pfmMeas ψ S' w' ((τ' : ℂ) * u) s')) = Φ := by
    funext x
    rw [pot_add aP aN' x, pot_add aN aP' x]
    simp only [hΦ, pushPot]
    ring
  rw [D3Plus.kernelCov2_self_eq_pot (isAdmissibleH_add aP aN') (isAdmissibleH_add aN aP'), hpotE,
    integral_add_measure (intΦ aP) (intΦ aN'), integral_add_measure (intΦ aN) (intΦ aP')]
  -- one sign
  have one : ∀ v v' : ℂ, ‖v‖ = τ → ‖v'‖ = τ' → ‖v - v'‖ = |τ - τ'| →
      IsAdmissibleH (pfmMeas ψ S w' v' s') →
      |∫ x, Φ x ∂pfmMeas ψ S w v s - ∫ x, Φ x ∂pfmMeas ψ S' w' v' s'| ≤
        B * (3 * L / τ * κ * Δ) := by
    intro v v' hv hv' hvv a3
    rw [imap Φ hΦm, imap Φ hΦm]
    have hLD := lip_comp hΦL hKg0 (psL w hlip S hS) (fun x hx => (hU x hx).1)
    have hvw : ‖v‖ ≤ w.im := by rw [hv]; exact hτw
    have hvw' : ‖v'‖ ≤ w'.im := by rw [hv']; exact hτw'
    have c1 := abs_integral_fmMeas_sub_le_on (F := fun x => Φ ((S : ℂ) * ψ x))
      (mul_nonneg hKg0 (mul_nonneg ha.le hM₁)) hLD hs0 hs0' hvw hvw' (sup1 v hv) (sup2 v' hv')
    rw [hvv] at c1
    have : IsFiniteMeasure (D3Plus.fmMeas w' v' s') :=
      CircleFubini.isFiniteMeasure_bind_circle _
    have i1 : Integrable (fun x => Φ ((S : ℂ) * ψ x)) (D3Plus.fmMeas w' v' s') :=
      (integrable_map_measure hΦm.aestronglyMeasurable (hfT S).aemeasurable).1 (intΦ a3)
    have i2 : Integrable (fun x => Φ ((S' : ℂ) * ψ x)) (D3Plus.fmMeas w' v' s') :=
      (integrable_map_measure hΦm.aestronglyMeasurable (hfT S').aemeasurable).1
        (intΦ (adm w' v' τ' s' S' hτ' hv' hs0' hs'τ' (by linarith) hS0'))
    have c2 : ‖∫ x, (Φ ((S : ℂ) * ψ x) - Φ ((S' : ℂ) * ψ x)) ∂D3Plus.fmMeas w' v' s'‖ ≤
        Kg * (M₀ * |S - S'|) * (D3Plus.fmMeas w' v' s').real univ := by
      refine norm_integral_le_of_norm_le_const ?_
      filter_upwards [G1FM.ae_dist_fmMeas_le hs0' hvw']
        with x hx
      have hxD : x ∈ closedBall w r₂ := sup2 v' hv' (mem_closedBall.2 hx)
      rw [Real.norm_eq_abs]
      exact (hΦL _ (hU x hxD).1 _ (hU x hxD).2).trans
        (mul_le_mul_of_nonneg_left (dT x (hDD hxD)) hKg0)
    rw [integral_sub i1 i2, Real.norm_eq_abs] at c2
    have hμB : (D3Plus.fmMeas w' v' s').real univ = B := by
      rw [hBdef, measureReal_def, measureReal_def, D3Plus.fmMeas_univ]
    rw [hμB] at c2
    set X := ‖w - w'‖ + |τ - τ'| + |s - s'| with hX
    have hX0 : 0 ≤ X := by positivity
    have t1 : B * (Kg * (a * M₁) * X) ≤ B * Kg * X * κ := by
      calc B * (Kg * (a * M₁) * X) = B * Kg * X * (a * M₁) := by ring
        _ ≤ B * Kg * X * κ := mul_le_mul_of_nonneg_left haM (by positivity)
    have t2 : Kg * (M₀ * |S - S'|) * B ≤ B * Kg * |S - S'| * κ := by
      calc Kg * (M₀ * |S - S'|) * B = B * Kg * |S - S'| * M₀ := by ring
        _ ≤ B * Kg * |S - S'| * κ := mul_le_mul_of_nonneg_left hM₀κ (by positivity)
    have t3 : B * Kg * κ * Δ ≤ B * (3 * L / τ * κ * Δ) := by
      calc B * Kg * κ * Δ = B * κ * Δ * Kg := by ring
        _ ≤ B * κ * Δ * (3 * L / τ) := mul_le_mul_of_nonneg_left hKg3 (by positivity)
        _ = B * (3 * L / τ * κ * Δ) := by ring
    have e : B * Kg * X * κ + B * Kg * |S - S'| * κ = B * Kg * κ * Δ := by rw [hΔ, hX]; ring
    have hsplit : ∫ x, Φ ((S : ℂ) * ψ x) ∂D3Plus.fmMeas w v s -
        ∫ x, Φ ((S' : ℂ) * ψ x) ∂D3Plus.fmMeas w' v' s' =
        (∫ x, Φ ((S : ℂ) * ψ x) ∂D3Plus.fmMeas w v s -
          ∫ x, Φ ((S : ℂ) * ψ x) ∂D3Plus.fmMeas w' v' s') +
        (∫ x, Φ ((S : ℂ) * ψ x) ∂D3Plus.fmMeas w' v' s' -
          ∫ x, Φ ((S' : ℂ) * ψ x) ∂D3Plus.fmMeas w' v' s') := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have c1' : |∫ x, Φ ((S : ℂ) * ψ x) ∂D3Plus.fmMeas w v s -
        ∫ x, Φ ((S : ℂ) * ψ x) ∂D3Plus.fmMeas w' v' s'| ≤ B * (Kg * (a * M₁) * X) := c1
    linarith
  have o1 := one _ _ (hnu τ hτ) (hnu τ' hτ') (by
      rw [show (τ : ℂ) * u - (τ' : ℂ) * u = ((τ - τ' : ℝ) : ℂ) * u by push_cast; ring,
        D3Plus.norm_ofReal_mul_unit hu])
    (adm w' _ τ' s' S hτ' (hnu τ' hτ') hs0' hs'τ' (by linarith) hS0)
  have o2 := one _ _ (hnu' τ hτ) (hnu' τ' hτ') (by
      rw [show -((τ : ℂ) * u) - -((τ' : ℂ) * u) = ((τ' - τ : ℝ) : ℂ) * u by push_cast; ring,
        D3Plus.norm_ofReal_mul_unit hu, abs_sub_comm])
    (adm w' _ τ' s' S hτ' (hnu' τ' hτ') hs0' hs'τ' (by linarith) hS0)
  have key : (∫ x, Φ x ∂pfmMeas ψ S w ((τ : ℂ) * u) s +
      ∫ x, Φ x ∂pfmMeas ψ S' w' (-((τ' : ℂ) * u)) s') -
      (∫ x, Φ x ∂pfmMeas ψ S w (-((τ : ℂ) * u)) s +
        ∫ x, Φ x ∂pfmMeas ψ S' w' ((τ' : ℂ) * u) s') ≤ 2 * (B * (3 * L / τ * κ * Δ)) := by
    have := le_abs_self (∫ x, Φ x ∂pfmMeas ψ S w ((τ : ℂ) * u) s -
      ∫ x, Φ x ∂pfmMeas ψ S' w' ((τ' : ℂ) * u) s')
    have := neg_abs_le (∫ x, Φ x ∂pfmMeas ψ S w (-((τ : ℂ) * u)) s -
      ∫ x, Φ x ∂pfmMeas ψ S' w' (-((τ' : ℂ) * u)) s')
    linarith
  have fin : 2 * (B * (3 * L / τ * κ * Δ)) ≤ c₀ * (3 + 4 / δ₀) * Δ / τ := by
    have e1 : 2 * (B * (3 * L / τ * κ * Δ)) = c₀ * 3 * (Δ / τ) := by rw [hc₀]; ring
    have h10 : c₀ * (3 + 4 / δ₀) * Δ / τ = c₀ * 3 * (Δ / τ) + c₀ * (4 / δ₀) * (Δ / τ) := by
      ring
    have h11 : 0 ≤ c₀ * (4 / δ₀) * (Δ / τ) := by positivity
    rw [e1, h10]; linarith
  exact key.trans fin

end G1FM2
end Thm18Asm
end QuantumZipper
