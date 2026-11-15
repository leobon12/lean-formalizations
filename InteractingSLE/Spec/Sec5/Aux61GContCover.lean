/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GContData
import InteractingSLE.Spec.Sec5.Aux61GContEndpoint
import InteractingSLE.Spec.Sec5.Aux61GInstAccessLocal

/-! # Fibre cover with the constructed correction and physical endpoint data

This conditional assembly discharges the measurable word/cutoff fields,
`hexit`, and the code-level visit premise. The genuinely mathematical inputs
left to callers are named: the restart specification, a history cover,
physical completed-window capture, and the Gaussian/mean identification.
It does not assert that an arbitrary history event captures future paths.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GCont
open Aux61GInst Aux61FibData
open Aux61Fib (FibData)
open Aux61UnionK (HasFibreLocalCover canonMean chartHull)
open Aux61ChLoc (IsChartGaussAt)

universe u

/-- A captured pre-contact event has a fibre-local cover. The fixed-window
data are the constructed correction/cutoff families, so their measurability,
word invariance and cut conditions are proved rather than assumed again.
`hcompleted_window` states precisely the remaining physical localization. -/
theorem hasFibreLocalCover_of_captured_access
    {X : Type u} [mX : MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : X → Prop} {ι : Type} [Countable ι] {β : ι → Type u}
    [mβ : ∀ i, MeasurableSpace (β i)]
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i))
    (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i))
    (d₀ : ι → FibData) (T₀ : ∀ i, β i → DistOn upperHalfPlaneOpens)
    (D : ∀ i, InitialWindowData (β i) (μ.map (Z i)) (d₀ i) (T₀ i))
    (Er : ι → Set X) (c : ι → X → Chart) (ρ : ι → X → ℝ≥0 → ℂ) (T : ι → X → ℝ≥0∞)
    (hrestart_spec : ∀ i, IsRestartSpec (Er i) (c i) (ρ i) (T i))
    (V : ι → Set ℂ) (hVo : ∀ i, IsOpen (V i)) (hV0 : ∀ i, (0 : ℂ) ∈ V i)
    (hland : ∀ i, HasAccessLanding (Er i) (c i) (ρ i) (T i) (V i))
    (hinj : ∀ i, ∀ x ∈ Er i, InjOn (ρ i x) {u | (u : ℝ≥0∞) < T i x})
    (hliftc : ∀ i, ∀ x ∈ Er i, ContinuousOn (c i x).2.2 (c i x).dom)
    (h : X → DistOn upperHalfPlaneOpens) (hh : Measurable h) (a k : ℝ)
    (hdV : ∀ i, (d₀ i).V = V i) (hdℓ : ∀ i, (d₀ i).ℓ = clr (V i))
    (p q : ι → ℝ)
    (hreference_window : ∀ i, Aux61Cov.RefWin (d₀ i).κ (d₀ i).bR (d₀ i).JR (Ioo (p i) (q i)))
    (hphysical_stop : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i →
      x ∈ Er i ∧ 0 < T i x ∧ (T i x < ⊤ ∨ ∃ u : ℝ≥0,
        (u : ℝ≥0∞) < T i x ∧ inPath (Er i) (c i) (ρ i) (T i) x u ∉ V i))
    (hhistory_cover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i)
    (hcompleted_window : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x →
      T i x < ⊤ ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < T i x → inPath (Er i) (c i) (ρ i) (T i) x u ∈ V i) ∧
      ∃ y ∈ Ioo (p i) (q i), Tendsto (inPath (Er i) (c i) (ρ i) (T i) x)
        (𝓝[<] (T i x).toNNReal) (𝓝 (y : ℂ)))
    (𝒢 : ι → ℝ≥0 → MeasurableSpace X)
    (h₁ : ι → ℝ≥0 → X → DistOn upperHalfPlaneOpens)
    (hgaussian : ∀ i (r : ℝ≥0), IsChartGaussAt μ (Z i) (B i)
      (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h) r (𝒢 i r) (h₁ i r))
    (hcanonical_mean : ∀ i (r : ℝ≥0), ∀ᵐ x ∂μ, Z i x ∈ B i →
      (r : ℝ≥0∞) < (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x).life →
      ∀ ψ : TestOn upperHalfPlaneOpens,
      Disjoint (tsupport ψ) (chartHull (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h) r x) →
      h₁ i r x ψ = ∫ z, canonMean (withQ (d₀ i) ((D i).correction (Z i x))) ((D i).cutoff (Z i x))
        (ULift.up.{u} (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)) r z * ψ z) :
    HasFibreLocalCover μ E := by
  let d : ∀ i, β i → FibData := fun i z => withQ (d₀ i) ((D i).correction z)
  have hword : ∀ i z, (d i z).κ = (d₀ i).κ ∧ (d i z).bR = (d₀ i).bR ∧ (d i z).JR = (d₀ i).JR :=
    fun i z => ⟨withQ_κ _ _, withQ_bR _ _, withQ_JR _ _⟩
  have hcut : ∀ i, ∀ z ∈ B i,
      Aux61Win.IsCutoffOn ((D i).cutoff z) (d i z).q (D i).neighbourhood (d i z).O₀ ∧
        (d i z).buffer ⊆ (D i).neighbourhood := by
    intro i z hz
    dsimp only [d]
    rw [withQ_O₀, withQ_buffer]
    exact ⟨(D i).cut_on z, (D i).buffer_sub⟩
  have hexit : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → x ∈ exitEv (Er i) (c i) (ρ i) (T i) (V i) := by
    intro i
    filter_upwards [hphysical_stop i] with x hx hxB
    exact mem_exitEv_of_contact_or_exit (hx hxB).1 (hx hxB).2.1 (hx hxB).2.2
  have hvisit : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x →
      accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x ∈ visitSet (p i) (q i) := by
    intro i
    filter_upwards [hphysical_stop i, hcompleted_window i] with x hs hc hxB hxE
    obtain ⟨y, hy, hylim⟩ := (hc hxB hxE).2.2
    exact accessExitCode_mem_visitSet_of_contact (hrestart_spec i) (hVo i) (hV0 i)
      (hland i) (hinj i) (hs hxB).1 (hs hxB).2.1 (hc hxB hxE).1 (hc hxB hxE).2.1 hy hylim
  exact hasFibreLocalCover_of_accessRestart_gauss Z hZ B hB Er c ρ T hrestart_spec V hVo hV0 hland hinj hliftc h hh
    a k d (fun i z => (withQ_V _ _).trans (hdV i)) (fun i z => (withQ_ℓ _ _).trans (hdℓ i)) p q
    (fun i z hz => by
      dsimp only [d]
      rw [withQ_κ, withQ_bR, withQ_JR]
      exact hreference_window i) hexit hhistory_cover hvisit
    (fun i => (D i).cutoff) (fun i _ => (D i).neighbourhood) hcut
    (fun i => (d₀ i).κ) (fun i => (d₀ i).bR) (fun i => (d₀ i).JR) hword
    (fun i => (D i).q_meas) (fun i => (D i).cut_meas) (fun i => (D i).source_meas)
    𝒢 h₁ hgaussian hcanonical_mean

end InteractingSLE.Sec5.Aux61GCont
