import InteractingSLE.Spec.Sec5.Aux61RestartInstHistory
import InteractingSLE.Spec.Sec5.Aux61RestartInstLift

/-!
# A measurable restart chart from the two retained accesses

Packet PROVE-AUX61-R1, ruling R71. `CollarPrimeEndComparison` isolates the
remaining boundary-extension mathematics: the recorded current and original
target collars approach distinct prime ends of the retained component. Given
that exact input, this file constructs countable approaches and a measurable
chart normalized on the entire collars, not merely on the selected sequences.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

open Sec7.Lemma71E

/-- Named remaining boundary-extension input. `F₀` is the recorded own inverse
chart at the current tip; `F₁` is the original target access in the retained
counterflow chart. Neither is selected using the future continuation. -/
def CollarPrimeEndComparison (D : Set ℂ) (F₀ F₁ : ℂ → ℂ) : Prop :=
  ∃ ψ : HChart D, ∃ p q : OnePoint ℝ, p ≠ q ∧
    Tendsto (ψ.1 ∘ F₀) (𝓝[H] 0) (PrimeEnd.approachH p) ∧
    Tendsto (ψ.1 ∘ F₁) (𝓝[H] 0) (PrimeEnd.approachH q)

/-- An inverse-chart collar lies in the selected component eventually. -/
theorem eventually_mem_of_collar {D : Set ℂ} {F : ℂ → ℂ}
    (h : ∃ δ > 0, MapsTo F (ball 0 δ ∩ H) D) :
    ∀ᶠ w in 𝓝[H] 0, F w ∈ D := by
  obtain ⟨δ, hδ, hf⟩ := h
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) hδ)] with w hwH hwball
  exact hf ⟨hwball, hwH⟩

/-- Normalize both whole collar approaches, and the dense sequences describing
them, at the same two prime ends. -/
theorem exists_normalized_chart_of_collar_comparison
    {D : Set ℂ} (hDo : IsOpen D) {g₀ F₀ g₁ F₁ : ℂ → ℂ}
    (hF₀ : ∃ δ > 0, MapsTo F₀ (ball 0 δ ∩ H) D)
    (hF₁ : ∃ δ > 0, MapsTo F₁ (ball 0 δ ∩ H) D)
    (hcmp : CollarPrimeEndComparison D F₀ F₁) {x y : ℕ → ℂ}
    (hxD : ∀ n, x n ∈ D) (hyD : ∀ n, y n ∈ D)
    (hinv₀ : ∀ n, F₀ (g₀ (x n)) = x n)
    (hinv₁ : ∀ n, F₁ (g₁ (y n)) = y n)
    (hx : Tendsto (g₀ ∘ x) atTop (𝓝[H] 0))
    (hy : Tendsto (g₁ ∘ y) atTop (𝓝[H] 0)) :
    ∃ φ : HChart D,
      Tendsto (φ.1 ∘ x) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖φ.1 (y n)‖) atTop atTop ∧
      Tendsto (φ.1 ∘ F₀) (𝓝[H] 0) (𝓝 0) ∧
      Tendsto (fun w => ‖φ.1 (F₁ w)‖) (𝓝[H] 0) atTop := by
  obtain ⟨ψ, p, q, hpq, h₀, h₁⟩ := hcmp
  obtain ⟨φ, hseed, htarget⟩ := exists_hChart_marking hDo ψ
    (PrimeEnd.mk ψ p) (PrimeEnd.mk ψ q)
    (fun h => hpq (PrimeEnd.mk_injective ψ h))
  have hnorm₀ := tendsto_comp_of_primeEnd_eq hDo hseed
    (eventually_mem_of_collar hF₀) h₀
  have hnorm₁ := tendsto_comp_of_primeEnd_eq hDo htarget
    (eventually_mem_of_collar hF₁) h₁
  have hxs := tendsto_primeEnd_of_chart_access h₀ hinv₀ hx
  have hys := tendsto_primeEnd_of_chart_access h₁ hinv₁ hy
  refine ⟨φ, (tendsto_comp_of_primeEnd_eq hDo hseed
    (Eventually.of_forall hxD) hxs).mono_right nhdsWithin_le_nhds, ?_,
    hnorm₀.mono_right nhdsWithin_le_nhds, ?_⟩
  · exact tendsto_norm_cobounded_atTop.comp
      ((tendsto_comp_of_primeEnd_eq hDo htarget
        (Eventually.of_forall hyD) hys).mono_right inf_le_left)
  · exact tendsto_norm_cobounded_atTop.comp (hnorm₁.mono_right inf_le_left)

/-- Measurable restart charts from recorded current and original-target
collars. The named comparison premise records the outstanding prime-end
extension, explicitly. All countable approach indices are constructed here. -/
theorem exists_measurable_chart_of_retained_collars
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → Set ℂ}
    (hDo : ∀ ω, IsOpen (D ω)) (hDc : ∀ ω, IsConnected (D ω))
    (hDs : ∀ ω, IsSimplyConnected (D ω)) (hDH : ∀ ω, D ω ⊆ H)
    (hDm : ∀ z ρ, MeasurableSet {ω | closedBall z ρ ⊆ D ω})
    {e : ℕ → ℂ} (he : DenseRange e) {g₀ F₀ g₁ F₁ : Ω → ℂ → ℂ}
    (hgc₀ : ∀ ω, ContinuousOn (g₀ ω) (D ω))
    (hgc₁ : ∀ ω, ContinuousOn (g₁ ω) (D ω))
    (hgm₀ : ∀ z, Measurable ({ω | z ∈ D ω}.indicator fun ω => g₀ ω z))
    (hgm₁ : ∀ z, Measurable ({ω | z ∈ D ω}.indicator fun ω => g₁ ω z))
    (hgH₀ : ∀ ω, MapsTo (g₀ ω) (D ω) H)
    (hgH₁ : ∀ ω, MapsTo (g₁ ω) (D ω) H)
    (hinv₀ : ∀ ω w, w ∈ H → g₀ ω (F₀ ω w) = w)
    (hinv₁ : ∀ ω w, w ∈ H → g₁ ω (F₁ ω w) = w)
    (hback₀ : ∀ ω z, z ∈ D ω → F₀ ω (g₀ ω z) = z)
    (hback₁ : ∀ ω z, z ∈ D ω → F₁ ω (g₁ ω z) = z)
    (hF₀ : ∀ ω, ∃ δ > 0, MapsTo (F₀ ω) (ball 0 δ ∩ H) (D ω))
    (hF₁ : ∀ ω, ∃ δ > 0, MapsTo (F₁ ω) (ball 0 δ ∩ H) (D ω))
    (hcmp : ∀ ω, CollarPrimeEndComparison (D ω) (F₀ ω) (F₁ ω)) :
    ∃ c : Ω → Chart,
      (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ((c ω).dom : Set ℂ) = D ω) ∧
      (∀ ω, IsConformalBijection (c ω).1 (D ω) H) ∧
      (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      (∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (D ω) ∧
        ∀ z ∈ D ω, (c ω).2.2 z = (L z).im) ∧
      (∀ ω, Tendsto ((c ω).1 ∘ F₀ ω) (𝓝[H] 0) (𝓝 0) ∧
        Tendsto (fun w => ‖(c ω).1 (F₁ ω w)‖) (𝓝[H] 0) atTop) := by
  have hmem := measurableSet_mem_of_closedBall hDo hDm
  obtain ⟨Nx, hNx, hxD, hx⟩ := exists_measurable_chart_access_sequence hDo hmem
    hgc₀ hgm₀ hgH₀ (fun ω => exists_small_chart_value_of_collar (hinv₀ ω) (hF₀ ω)) he
  obtain ⟨Ny, hNy, hyD, hy⟩ := exists_measurable_chart_access_sequence hDo hmem
    hgc₁ hgm₁ hgH₁ (fun ω => exists_small_chart_value_of_collar (hinv₁ ω) (hF₁ ω)) he
  have hnorm := fun ω => exists_normalized_chart_of_collar_comparison (hDo ω)
    (hF₀ ω) (hF₁ ω) (hcmp ω) (fun n => hxD n ω) (fun n => hyD n ω)
    (fun n => hback₀ ω _ (hxD n ω)) (fun n => hback₁ ω _ (hyD n ω)) (hx ω) (hy ω)
  choose φ hφx hφy hφ₀ hφ₁ using hnorm
  obtain ⟨c, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, -, huniq⟩ :=
    exists_measurable_twoPointChart hDo hDc hDs hDH hDm he hNx hNy hxD hyD
      (fun ω => ⟨(φ ω).1, (φ ω).2, hφx ω, hφy ω⟩)
  refine ⟨c, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, fun ω => ?_⟩
  obtain ⟨a, ha, heq⟩ := huniq ω (φ ω).1 (φ ω).2 (hφx ω) (hφy ω)
  constructor
  · have h := (hφ₀ ω).const_mul (a : ℂ)
    rw [mul_zero] at h
    exact h.congr' ((eventually_mem_of_collar (hF₀ ω)).mono fun w hw => (heq hw).symm)
  · have h := (hφ₁ ω).const_mul_atTop ha
    refine h.congr' ((eventually_mem_of_collar (hF₁ ω)).mono fun w hw => ?_)
    change a * ‖(φ ω).1 (F₁ ω w)‖ = ‖(c ω).1 (F₁ ω w)‖
    rw [heq hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]

end InteractingSLE.Sec5.Aux61Restart
