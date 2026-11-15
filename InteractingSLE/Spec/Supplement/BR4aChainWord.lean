/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aChainWire
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# BR4a's relative chain: the time-0 identity and the deterministic word input

Packet PROVE-T14-BR4A2. The words input `BR4aRelWordStatement` (`BR4aChainWire`) is reduced to a purely deterministic
statement about one sample, `BR4aWordDetStatement`:

* `integral_apply_of_isGFF`: the mean of a GFF with boundary data is the pairing with its harmonic extension;
* **`bhe_transport_eq`** (the time-0 identity, HULLDET §4.1 (b)): if `h'` is a GFF with data `b'` and
  `X = chartTransport (brChart v) 1 0 k h'` is a GFF with data `g`, the harmonic extension of `g` is
  `u_{b'} ∘ mobInv v + k · lift ∘ mobInv v` on `ℍ` (means of the transport, `Sec6.eqOn_of_integral_mul_eq`);
* **`BR4aWordDetStatement`** (named input, deterministic): seed, no threshold, and the coupling-mean identity for one
  sample of the original integrated path with the relative driver `relDrv`;
* **`br4aRelWordStatement_of_det`** and **`br4aRelChainStatement_of_clock_det`**: BR4a's relative chain from
  `BR4aClockStatement`, `BR4aWordDetStatement` and Theorem 1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.BR4aChain

open Restart Restart.FCDet Restart.DomainMarkov Restart.DomainMarkov.K2 Sec2.Assembly Sec7.PocketTraversal
  BR4aPath Supp8.HullDetGen MartChar.RealFlow

/-- The mean of a GFF with boundary data is the pairing with its bounded harmonic extension. -/
theorem integral_apply_of_isGFF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → DistOn upperHalfPlaneOpens} {g : ℝ → ℝ} {S : Set ℝ} {u : ℂ → ℝ}
    (hX : IsGFFWithBoundaryData P X g S) (hu : IsBoundedHarmonicExtension g S u) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => X ω φ) P ∧ ∫ ω, X ω φ ∂P = ∫ z, u z * φ z := by
  have hZ := hX.2 u hu
  have hi : Integrable (fun ω => X ω φ - ∫ z, u z * φ z) P := (hZ.gaussian.hasGaussianLaw_eval φ).integrable
  have hi' : Integrable (fun ω => X ω φ) P :=
    (hi.add (integrable_const (∫ z, u z * φ z))).congr (Eventually.of_forall fun ω => by simp)
  refine ⟨hi', ?_⟩
  have h0 := hZ.centered φ
  rw [integral_sub hi' (integrable_const _), integral_const, probReal_univ, one_smul] at h0
  linarith

/-- **The time-0 identity of BR4a's target change**: if `h'` is a GFF with boundary data `b'` and its transport
`X = chartTransport (brChart v) 1 0 k h'` is a GFF with boundary data `g`, then the bounded harmonic extension of `g`
is the transported one of `b'` plus the lift: `u_g = u_{b'} ∘ mobInv v + k · lift ∘ mobInv v` on `ℍ`. -/
theorem bhe_transport_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h' : Ω → DistOn upperHalfPlaneOpens} {b' : ℝ → ℝ} {J' : Set ℝ} {u₀ : ℂ → ℝ}
    (hh' : IsGFFWithBoundaryData P h' b' J') (hu₀ : IsBoundedHarmonicExtension b' J' u₀) (v k : ℝ)
    {g : ℝ → ℝ} {S : Set ℝ} {ug : ℂ → ℝ}
    (hX : IsGFFWithBoundaryData P (fun ω => Chart.chartTransport (isConformal_brChart v) 1 0 k (h' ω)) g S)
    (hug : IsBoundedHarmonicExtension g S ug) :
    ∀ z ∈ H, ug z = u₀ (mobInv v z) + k * (brChart v).2.2 (mobInv v z) := by
  have hc := isConformal_brChart v
  have hℓc := continuousOn_brChart_lift_inv v
  have hmaps : MapsTo (mobInv v) H H := fun w hw => mobInv_mem_H v hw
  have hdiff : DifferentiableOn ℂ (mobInv v) H := fun w hw =>
    (analyticAt_mob (-v) hw).differentiableAt.differentiableWithinAt
  have hH₁ : InnerProductSpace.HarmonicOnNhd (u₀ ∘ mobInv v) H :=
    LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H hu₀.1 hdiff hmaps
  have hlift : InnerProductSpace.HarmonicOnNhd (brChart v).2.2 H := by
    have := harmonicOnNhd_brChart_lift v
    rwa [coe_dom_brChart] at this
  have hH₂ : InnerProductSpace.HarmonicOnNhd ((brChart v).2.2 ∘ mobInv v) H :=
    LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H hlift hdiff hmaps
  have hH : InnerProductSpace.HarmonicOnNhd (fun z => u₀ (mobInv v z) + k * (brChart v).2.2 (mobInv v z)) H :=
    hH₁.add (Impl.harmonicOnNhd_const_mul k hH₂)
  refine Sec6.eqOn_of_integral_mul_eq QuantumZipper.isOpen_H le_rfl hug.1 hH fun φ _ => ?_
  obtain ⟨-, hm⟩ := integral_apply_of_isGFF hX hug φ
  have hpush := integral_apply_of_isGFF hh' hu₀ (Chart.pushTest hc φ)
  rw [← hm]
  have hexp : (fun ω => Chart.chartTransport hc 1 0 k (h' ω) φ) =
      fun ω => h' ω (Chart.pushTest hc φ) + k * Chart.liftDist (brChart v) φ := funext fun ω => by
    rw [Chart.chartTransport_apply']; ring
  rw [hexp, integral_add hpush.1 (integrable_const _), integral_const, probReal_univ, one_smul, hpush.2,
    Chart.integral_mul_pushTest hc, Chart.liftDist_apply (Chart.locallyIntegrableOn_of_continuousOn hℓc)]
  have hi₁ : Integrable fun w => u₀ ((brChart v).2.1 w) * φ w := by
    have := SupercriticalConformalCovariance.GM24.integrable_test_mul (B := upperHalfPlaneOpens)
      (hu₀.1.continuousOn.comp hdiff.continuousOn hmaps) φ
    have h2 : Integrable fun w => u₀ (mobInv v w) * φ w := by simpa only [mul_comm, Function.comp] using this
    exact h2
  have hi₂ : Integrable fun w => (brChart v).2.2 ((brChart v).2.1 w) * φ w := by
    have := SupercriticalConformalCovariance.GM24.integrable_test_mul (B := upperHalfPlaneOpens) hℓc φ
    simpa only [mul_comm] using this
  rw [← integral_const_mul, ← integral_add hi₁ (hi₂.const_mul k)]
  congr 1
  funext w
  simp only [add_mul, mul_assoc]
  rfl


/-- **Named input (deterministic): the words of BR4a's relative chain, one sample.** For a piecewise-constant datum
`b'` with its angle-`0` flow-line word (parameter `κ' = 16/κ`), `v ≠ 0`, and a sorted word `c` whose bounded harmonic
extension is the time-0 transport of that of `b'` (`bhe_transport_eq`): for every sample `(w, vL, vR)` of the
integrated `SLE_{κ'}` path of the word of `b'` with infinite lifetime, a transient complete generating trace, a visit
of `v` and an unbounded clock `clock v` before it, (1) the flow-line seed of `c` is admissible, (2) the relative
driver `relDrv v w` never reaches a continuation threshold of the flowed marks of `c`, and (3) at every original
time `t` before the visit, `q = clock v w t`, the original coupling mean at `t` read through `brChart v` is the
coupling mean of `relDrv v w` at `q` with the flowed word of `c` (supplement p. 610, (BR4a.1)–(BR4a.2)). -/
def BR4aWordDetStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b' : ℝ → ℝ) (J' : Finset ℝ), IsPiecewiseConstantBoundaryData b' J' →
    ∀ v : ℝ, v ≠ 0 → ∀ c : BoundaryWord, c.IsSorted →
    (∀ u₀ uc : ℂ → ℝ, IsBoundedHarmonicExtension b' J' u₀ → IsBoundedHarmonicExtension c.fn c.jumps uc →
      ∀ z ∈ H, uc z = u₀ (mobInv v z) + chiC (16 / κ) * (brChart v).2.2 (mobInv v z)) →
    ∀ (w : ℝ≥0 → ℝ) (vL : Fin (flowLineNL b' J' 0) → ℝ≥0 → ℝ) (vR : Fin (flowLineNR b' J' 0) → ℝ≥0 → ℝ)
      (bm : ℝ≥0 → ℝ),
      IsIntegratedSLEPath (16 / κ) (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL (16 / κ) b' J' 0 0)
        (flowLineRhoR (16 / κ) b' J' 0 0) w vL vR bm ⊤ →
    ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ γ → Tendsto (fun t => ‖γ t‖) atTop atTop →
    (v : ℂ) ∈ infinitySourceChart.tipSet w ⊤ →
    (∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} ∧
      M ≤ clock v (fun s : ℝ => w s.toNNReal) t) →
    ¬ ForceWord.ThresholdCondition (flowLineRhoL (16 / κ) c.fn c.jumps 0 0)
        (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) 0 (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) ∧
    MartChar.thresholdTime (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0)
        (relDrv v w) (fun i t => -rightImg (fun s : ℝ => -relDrv v w s.toNNReal) (-flowLineXL c.fn c.jumps 0 i) t)
        (fun j t => rightImg (fun s : ℝ => relDrv v w s.toNNReal) (flowLineXR c.fn c.jumps 0 j) t) = ⊤ ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} →
      ∀ z ∈ H \ fwdHull (fun s : ℝ => relDrv v w s.toNNReal) ((clock v (fun s : ℝ => w s.toNNReal) t).toNNReal : ℝ),
        couplingMean (16 / κ) (fun s : ℝ => w s.toNNReal) t
            (LocalExt.bheAt (16 / κ) (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0)
              (fun i => vL i t - w t) (fun j => vR j t - w t)) (mobInv v z) + 0 +
            chiC (16 / κ) * (brChart v).2.2 (mobInv v z) =
          couplingMean (16 / κ) (fun s : ℝ => relDrv v w s.toNNReal)
            ((clock v (fun s : ℝ => w s.toNNReal) t).toNNReal : ℝ)
            (LocalExt.bheAt (16 / κ) (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0)
              (fun i => -rightImg (fun s : ℝ => -relDrv v w s.toNNReal) (-flowLineXL c.fn c.jumps 0 i)
                  ((clock v (fun s : ℝ => w s.toNNReal) t).toNNReal : ℝ) -
                relDrv v w (clock v (fun s : ℝ => w s.toNNReal) t).toNNReal)
              (fun j => rightImg (fun s : ℝ => relDrv v w s.toNNReal) (flowLineXR c.fn c.jumps 0 j)
                  ((clock v (fun s : ℝ => w s.toNNReal) t).toNNReal : ℝ) -
                relDrv v w (clock v (fun s : ℝ => w s.toNNReal) t).toNNReal)) z


/-- **BR4a's relative words from the deterministic statement** (conditional helper with a distinct name; named
input `BR4aWordDetStatement`): the time-0 identity is `bhe_transport_eq`, the sample facts are the integrated path
of the original coupling (infinite lifetime), the trace, the visit and the clock. -/
theorem br4aRelWordStatement_of_det (hdet : BR4aWordDetStatement) : BR4aRelWordStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hζ' v hv0 hvis b' J' h' hb' htr' 𝓕 VL VR B hC htrace hclkω c
    hcs hXc
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hh' : IsGFFWithBoundaryData P h' b' J' :=
    Sec7.StripSysField.isGFFWithBoundaryData_of_flowLineGFF hκ' hb' ⟨hC.2.1, hC.2.2.1⟩
  have h0 : ∀ u₀ uc : ℂ → ℝ, IsBoundedHarmonicExtension b' J' u₀ → IsBoundedHarmonicExtension c.fn c.jumps uc →
      ∀ z ∈ H, uc z = u₀ (mobInv v z) + chiC (16 / κ) * (brChart v).2.2 (mobInv v z) :=
    fun u₀ uc hu₀ huc => bhe_transport_eq hh' hu₀ v _ hXc huc
  have hgood : ∀ᵐ ω ∂P, IsIntegratedSLEPath (16 / κ) (flowLineXL b' J' 0) (flowLineXR b' J' 0)
      (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0) (fun t => W' t ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) ⊤ ∧
      (∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ ∧ Tendsto (fun t => ‖γ t‖) atTop atTop) ∧
      (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤ ∧
      ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)} ∧
        M ≤ clock v (fun s : ℝ => W' s.toNNReal ω) t := by
    filter_upwards [hC.1.2.2.2.2, hζ', htrace, hvis, hclkω] with ω hp hζω hγ hvisω hcω
    rw [hζω] at hp
    exact ⟨hp, hγ, hvisω, hcω⟩
  obtain ⟨ω₀, hp₀, ⟨γ₀, hγ₀, htr₀⟩, hvis₀, hc₀⟩ := hgood.exists
  refine ⟨(hdet κ hκ hκ4 b' J' hb' v hv0 c hcs h0 _ _ _ _ hp₀ γ₀ hγ₀ htr₀ hvis₀ hc₀).1, ?_, ?_⟩
  · filter_upwards [hgood] with ω hω
    obtain ⟨hp, ⟨γ, hγ, htr⟩, hvisω, hcω⟩ := hω
    exact (hdet κ hκ hκ4 b' J' hb' v hv0 c hcs h0 _ _ _ _ hp γ hγ htr hvisω hcω).2.1
  · filter_upwards [hgood] with ω hω
    obtain ⟨hp, ⟨γ, hγ, htr⟩, hvisω, hcω⟩ := hω
    exact (hdet κ hκ hκ4 b' J' hb' v hv0 c hcs h0 _ _ _ _ hp γ hγ htr hvisω hcω).2.2

/-- **BR4a's relative chain from the clock input and the deterministic word input** (conditional helper with a
distinct name; Theorem 1.3 is a permitted root of Theorem 1.4, R48). -/
theorem br4aRelChainStatement_of_clock_det (hclk : BR4aClockStatement.{u}) (hdet : BR4aWordDetStatement)
    (h13 : Exist.Theorem13Statement.{u}) : Supp8.HullDetGen.BR4aRelChainStatement.{u} :=
  br4aRelChainStatement_of_clock_word hclk (br4aRelWordStatement_of_det hdet) h13

end InteractingSLE.Theorem14.BR4aChain
