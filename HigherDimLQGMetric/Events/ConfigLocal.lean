import HigherDimLQGMetric.Events.Locality

/-!
# Locality of the four-component configuration

The configuration is measurable modulo constants in the surrounding shell,
up to a null set. This is the configuration part of D-LOC.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

private theorem inner_config_shell_subset (z : Rd d) {r : ℝ} (hr : 0 < r) :
    ann z (3 * r / 4) (7 * r / 2) ⊆ ann z (r / 2) (5 * r) := by
  intro x hx
  dsimp [ann] at hx ⊢
  constructor <;> linarith

private theorem sphere_subset_config_shell (z : Rd d) {r : ℝ} (hr : 0 < r) :
    Metric.sphere z r ⊆ ann z (r / 2) (5 * r) := by
  intro x hx
  have hd : ‖x - z‖ = r := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  dsimp [ann]
  rw [hd]
  constructor <;> linarith

/-- D-LOC for the configuration: it has a version measurable for mean-zero
pairings in the shell. -/
theorem exists_measurable_config
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ Q : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (z : Rd d) {r : ℝ} (hr : 0 < r) :
    ∃ F : Ω → Config d,
      Measurable[fieldSigma0 h (ann z (r / 2) (5 * r))] F ∧
      ∀ᵐ ω ∂P, F ω = config (D (h ω)) (Dt (h ω))
        (sNorm ξ Q (h ω) r z) r z := by
  let J : TopologicalSpace.Opens (Rd d) := ⟨ann z (r / 2) (5 * r), isOpen_ann z _ _⟩
  let V : TopologicalSpace.Opens (Rd d) := ⟨ann z (3 * r / 4) (7 * r / 2), isOpen_ann z _ _⟩
  have hVJ : V ≤ J := inner_config_shell_subset z hr
  have hSJ : Metric.sphere z r ⊆ J := sphere_subset_config_shell z hr
  obtain ⟨F₁, hF₁m, hF₁ae⟩ :=
    hD.exists_measurable_normInternal_all hd hh J J le_rfl z hr hSJ
  obtain ⟨F₂, hF₂m, hF₂ae⟩ :=
    hDt.exists_measurable_normInternal_all hd hh J J le_rfl z hr hSJ
  obtain ⟨F₃, hF₃m, hF₃ae⟩ :=
    hD.exists_measurable_normInternal_all hd hh V J hVJ z hr hSJ
  obtain ⟨F₄, hF₄m, hF₄ae⟩ :=
    hDt.exists_measurable_normInternal_all hd hh V J hVJ z hr hSJ
  let F : Ω → Config d := fun ω =>
    (fun u v => F₁ ω (r • u + z) (r • v + z),
     fun u v => F₂ ω (r • u + z) (r • v + z),
     fun u v => F₃ ω (r • u + z) (r • v + z),
     fun u v => F₄ ω (r • u + z) (r • v + z))
  have hcomp (G : Ω → Rd d → Rd d → ℝ≥0∞)
      (hG : Measurable[fieldSigma0 h J] G) :
      Measurable[fieldSigma0 h J]
        (fun ω (u v : Rd d) => G ω (r • u + z) (r • v + z)) := by
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun u => ?_
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun v => ?_
    simpa only [Function.comp_def] using
      (measurable_pi_apply (r • v + z)).comp
        ((measurable_pi_apply (r • u + z)).comp hG)
  refine ⟨F, ?_, ?_⟩
  · exact (hcomp F₁ hF₁m).prodMk ((hcomp F₂ hF₂m).prodMk
      ((hcomp F₃ hF₃m).prodMk (hcomp F₄ hF₄m)))
  filter_upwards [hF₁ae, hF₂ae, hF₃ae, hF₄ae] with ω h₁ h₂ h₃ h₄
  unfold F config
  apply Prod.ext
  · funext u v
    exact h₁ _ _
  apply Prod.ext
  · funext u v
    exact h₂ _ _
  apply Prod.ext
  · funext u v
    exact h₃ _ _
  · funext u v
    exact h₄ _ _

/-- Every Borel configuration event is a shell event modulo null sets. -/
theorem aeEventIn_config
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ Q : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (z : Rd d) {r : ℝ} (hr : 0 < r)
    (S : Set (Config d)) (hS : MeasurableSet S) :
    AEEventIn P (fieldSigma0 h (ann z (r / 2) (5 * r)))
      {ω | config (D (h ω)) (Dt (h ω)) (sNorm ξ Q (h ω) r z) r z ∈ S} := by
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_config hD hDt hd hh z hr
  refine ⟨F ⁻¹' S, hFm hS, ?_⟩
  filter_upwards [hFae] with ω hω
  exact propext (by simp only [mem_preimage, hω])

end HigherDimLQGMetric
