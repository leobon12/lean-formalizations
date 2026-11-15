/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2OmLine
import InteractingSLE.Spec.Supplement.SB2QtNested
import InteractingSLE.Spec.Supplement.GW4SafeRKernel
import InteractingSLE.Spec.Restart.R1Glue
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71

/-!
# SB2(2)'s line mean at the times of zero relative clock

Packet PROVE-GW2-GEOM2, round 9 (PROVE-SB2-LCMEAN's handoff R13.8, item 1). At a B-time `t` with `a t = 0` (B's piece
still inside the retained hull, the relative hull empty) the line mean is the retained law's mean. The proof uses no
configuration:

* the version's hull clause gives `ℍ ∖ (A₁ t ∪ A₂ t) = Φ⁻¹ ℍ`, the canonical chart's domain;
* the marked line kernel of `A₁ t ∪ A₂ t` (`GW4Fix.ae_condExp_cexp_boundary_marked`, marks the completed line
  filtration at `t`) read through the canonical chart (`Restart.ae_condExp_cexp_chartTransport_random_on`) is, on
  `{a t = 0}`, Gaussian with the covariance of `ℍ` and the mean `chartTransport Φ (g t + u₀)`, given
  `germ ⊔ lineFiltC t`;
* the retained law (given `lineFiltC 0`, the chart field is the GFF of `β₁`) and REVIEW-FABLE-T14's nested Gaussian
  identity on an event of the finer σ-algebra (`Qt.ae_eq_of_gaussian_le_on`) give equal means:
  **`ae_pairing_eq_of_le_on`** (the mean form);
* **`ae_lineMean_zero`**: the `hmean` equation on `seedCell ∩ {a t < Λ} ∩ {a t = 0}`; the coupling mean at time `0` is
  `bheProc` at `0`, the type's force data at the cell positions (`eqOn_typed_mean`).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMap logDerivFwd zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.SB.Om

open Restart Exist Exist.StagedLaw Restart.DomainMarkov Supp8.Q3Stop Sec7.PocketTraversal LocalSets Lv Ms

section Pairing

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

open LQGMetric QuantumZipper Restart in
/-- **The nested Gaussian identity, mean form**: if given `m` the field `Y` has on `L ∈ m` the characteristic
functional of the word `β` (`β` measurable for `m`), and given `m' ≥ m` it has on `G ∈ m'`, `G ⊆ L`, a Gaussian
characteristic functional with the covariance of `ℍ` and the mean distribution `M'` (pairings measurable for `m'`),
then on `G` the pairing of `M'` with a test is the word mean's pairing. -/
theorem ae_pairing_eq_of_le_on (hm : m ≤ m') (hm' : m' ≤ mΩ)
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y) {β : Ω → BoundaryWord} (hβ : Measurable[m] β)
    {M' : Ω → DistOn upperHalfPlaneOpens}
    (hM' : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable[m'] fun ω => M' ω ψ)
    {L G : Set Ω} (hL : MeasurableSet[m] L) (hG : MeasurableSet[m'] G) (hGL : G ⊆ L)
    (hc : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ L →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | m] ω = gaussCF (β ω) ψ)
    (hf : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | m'] ω =
        Complex.exp (Complex.I * (M' ω ψ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov H ψ ψ : ℝ) : ℂ)))
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ G → M' ω ψ = ∫ z, (β ω).mean z * ψ z := by
  have hXm : Measurable fun ω => Y ω ψ := (measurable_distOn_apply ψ).comp hY
  have hcov0 : 0 ≤ zeroGFFTestCov H ψ ψ := by
    rw [LocalExt.zeroGFFTestCov_self_eq_norm_sq isOpen_H Subset.rfl]
    positivity
  have hHU : (upperHalfPlaneOpens : Set ℂ) = H := rfl
  have hfun : ∀ t : ℝ, (fun ω' => Complex.exp ((t : ℂ) * ((Y ω' ψ : ℝ) : ℂ) * Complex.I)) =
      fun ω' => Complex.exp (Complex.I * ((Y ω' (t • ψ) : ℝ) : ℂ)) := by
    intro t
    funext ω'
    rw [map_smul, smul_eq_mul]
    congr 1
    push_cast
    ring
  have hcovt : ∀ t : ℝ, zeroGFFTestCov H ⇑(t • ψ) ⇑(t • ψ) = t ^ 2 * zeroGFFTestCov H ψ ψ := fun t =>
    LocalSets.zeroGFFTestCov_smul_self isOpen_H Subset.rfl t ψ
  have hmeant : ∀ (t : ℝ) (c : BoundaryWord), ∫ z, c.mean z * (t • ψ) z = t * ∫ z, c.mean z * ψ z := by
    intro t c
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show c.mean z * (t • ψ) z = t * (c.mean z * ψ z)
    rw [show (t • ψ) z = t * ψ z from rfl]
    ring
  have hc' : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ L →
      P[fun ω' => Complex.exp ((t : ℂ) * ((Y ω' ψ : ℝ) : ℂ) * Complex.I) | m] ω =
        Complex.exp ((t : ℂ) * ((∫ z, (β ω).mean z * ψ z : ℝ) : ℂ) * Complex.I -
          (((zeroGFFTestCov H ψ ψ).toNNReal : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro t
    filter_upwards [hc (t • ψ)] with ω hω hωL
    rw [hfun t, hω hωL, gaussCF, hHU, hcovt, hmeant, Real.coe_toNNReal _ hcov0]
    congr 1
    push_cast
    ring
  have hf' : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp ((t : ℂ) * ((Y ω' ψ : ℝ) : ℂ) * Complex.I) | m'] ω =
        Complex.exp ((t : ℂ) * ((M' ω ψ : ℝ) : ℂ) * Complex.I -
          (((zeroGFFTestCov H ψ ψ).toNNReal : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro t
    filter_upwards [hf (t • ψ)] with ω hω hωG
    rw [hfun t, hω hωG, hcovt, map_smul, smul_eq_mul, Real.coe_toNNReal _ hcov0]
    congr 1
    push_cast
    ring
  have hcK := Qt.ae_map_condExpKernel_eq_gaussianReal (hm.trans hm') hXm hc'
  have hfK := Qt.ae_map_condExpKernel_eq_gaussianReal hm' hXm hf'
  have hμ : Measurable[m] fun ω => ∫ z, (β ω).mean z * ψ z :=
    (BoundaryWord.measurable_integral_mean_mul ψ).comp hβ
  exact Qt.ae_eq_of_gaussian_le_on hm hm' hXm hμ (hM' ψ) hL hG hGL hcK hfK

end Pairing

/-! ### The line mean at zero relative clock -/

section Zero

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

/-- **The line mean at the times of zero relative clock** (K2's `hmean` equation on
`seedCell ∩ {a t < Λ} ∩ {a t = 0}`): from the line family's union locality (marks `𝓖 t`), the version's hull clause
and the retained law of the canonical chart field given `lineFiltC 𝓖 0` (the word `β₁`). -/
theorem ae_lineMean_zero {ψ : ℝ} (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL L relLife)
    (hK : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hβ₁ : Measurable[lineFiltC P 𝓖 0] β₁) (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (hsort : ∀ ω, (β₁ ω).IsSorted)
    (hUm : ∀ t, Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω))
    (hcU : ∀ t ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω)))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P)
    (hlaw : ∀ᵐ ω ∂P, ω ∈ F → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω)
      (fun ω' => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω') 1 0 (chiC κ) (h ω'))
      (β₁ ω).fn (β₁ ω).jumps)
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hg : ∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P (g t))
    (m : ℕ) (w : WordType) (hw : w ∈ types) (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → (S.ver m).a t ω < (S.ver m).Λ w ω → (S.ver m).a t ω = 0 →
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ)
          (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ ψ β₁ w))
            (geomRW (S.ver m).W (cellXR κ ψ β₁ w)) ω ((S.ver m).a t ω).toNNReal) z * φ z := by
  classical
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hΦ : ∀ ω, (Mo.hullChart (fillH (K ω)) (x₀ ω)).IsConformal := Mu.isConformal_canon x₀ hKc hKp
  obtain ⟨-, hliftc, -, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hK hKc hKp hx₀
  -- the σ-algebras: `lineFiltC 0 ≤ lineFiltC t ≤ germ ⊔ lineFiltC t`
  have h01 : lineFiltC P 𝓖 0 ≤ lineFiltC P 𝓖 t := (lineFiltC P 𝓖).mono (zero_le (a := t))
  have hm : lineFiltC P 𝓖 0 ≤
      germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t :=
    h01.trans le_sup_right
  have hm₁ : lineFiltC P 𝓖 t ≤ mΩ := (lineFiltC P 𝓖).le t
  have hm'Ω : germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t ≤ mΩ :=
    sup_le (germSigma_le (hUm t) hh0.measurable) hm₁
  have hloc₁ : WholeField.IsHistoryAvoidanceLocal (lineFiltC P 𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P := Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma (hloc t)
  -- the event
  have hE₀m : MeasurableSet[germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔
      lineFiltC P 𝓖 t] (seedCell κ ψ β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩
        {ω | (S.ver m).a t ω = 0}) := by
    have h1 : MeasurableSet[lineFiltC P 𝓖 0] (seedCell κ ψ β₁ F w) := measurableSet_seedCell hβ₁ hF w
    have h2 : MeasurableSet[lineFiltC P 𝓖 t] {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} := by
      have := (S.ver m).safeS w hw 0 t
      have e : {ω | (S.ver m).a t ω < (S.ver m).Λ w ω ∧ Disjoint (tsupport ⇑(0 : TestOn upperHalfPlaneOpens))
          (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal)} =
          {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} := by
        ext ω
        simp only [mem_ofPred_eq, and_iff_left_iff_imp]
        intro _
        have e0 : tsupport ⇑(0 : TestOn upperHalfPlaneOpens) = ∅ := by
          rw [show ⇑(0 : TestOn upperHalfPlaneOpens) = (0 : ℂ → ℝ) from rfl, tsupport_zero]
        rw [e0]
        exact Set.empty_disjoint _
      rwa [e] at this
    have h3 : MeasurableSet[lineFiltC P 𝓖 t] {ω | (S.ver m).a t ω = 0} :=
      ((S.ver m).clock_meas t) (measurableSet_singleton 0)
    exact ((hm _ h1).inter (le_sup_right (a := germSigma _ _) _ h2)).inter (le_sup_right (a := germSigma _ _) _ h3)
  -- the union's kernel given its germ and the completed marks at `t`
  have hker : ∀ φ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ' : ℂ)) |
        germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t] ω =
      Complex.exp (Complex.I * ((g t ω + smoothDist upperHalfPlaneOpens u₀) φ' : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov (H \ (A₁ t ω ∪ A₂ t ω)) φ' φ' : ℝ) : ℂ)) := fun φ' =>
    GW4Fix.ae_condExp_cexp_boundary_marked hu₀.1 hh0 (hUm t) (hcU t) hm₁ hloc₁ (hg t) φ'
  -- on `{a t = 0}` the union's complement is the chart domain
  have hcomp : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩
      {ω | (S.ver m).a t ω = 0} →
      H \ (A₁ t ω ∪ A₂ t ω) = ((Mo.hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) := by
    filter_upwards [(S.ver m).hull w hw t] with ω hω hE
    have h0 : (S.ver m).a t ω = 0 := hE.2
    have hc : Continuous fun s : ℝ => (S.ver m).W s.toNNReal ω :=
      ((S.ver m).W_cont ω).comp continuous_real_toNNReal
    rw [hω hE.1.1 hE.1.2, h0, ENNReal.toNNReal_zero, NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hc,
      sdiff_empty, (hΦ ω).coe_dom]
  have hcond : ∀ φ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ω ∈ seedCell κ ψ β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩ {ω | (S.ver m).a t ω = 0} →
      tsupport φ' ⊆ (Mo.hullChart (fillH (K ω)) (x₀ ω)).dom →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ' : ℂ)) |
        germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t] ω =
      Complex.exp (Complex.I * ((g t ω + smoothDist upperHalfPlaneOpens u₀) φ' : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov ((Mo.hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) φ' φ' : ℝ) : ℂ)) := by
    intro φ'
    filter_upwards [hker φ', hcomp] with ω h1 h2 hE _
    rw [h1, h2 hE]
  -- the chart field's conditional law on the event, given the finer σ-algebra
  have hR1 := fun ψ' => Restart.ae_condExp_cexp_chartTransport_random_on (P := P) hm'Ω hΦ
    (fun z => hm _ (hdom z)) (fun z => (hfwd z).mono hm le_rfl) (fun z => (hliftm z).mono hm le_rfl) hliftc
    hh.1 (chiC κ) hE₀m (M := fun ω => g t ω + smoothDist upperHalfPlaneOpens u₀) hcond ψ'
  -- the measurability inputs
  have hm₀Ω : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hY : Measurable fun ω => Chart.chartTransport (hΦ ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' hΦ (fun z => hm₀Ω _ (hdom z)) (fun z => (hfwd z).mono hm₀Ω le_rfl)
      (fun z => (hliftm z).mono hm₀Ω le_rfl) hliftc hh.1 1 0 (chiC κ)
  have hgm : Measurable[germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔
      lineFiltC P 𝓖 t] fun ω => g t ω + smoothDist upperHalfPlaneOpens u₀ := by
    exact (WholeField.measurable_add_dist _).comp ((hg t).1.mono le_sup_left le_rfl)
  have hM' : ∀ ψ' : TestOn upperHalfPlaneOpens, Measurable[germSigma (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t]
      fun ω => Chart.chartTransport (hΦ ω) 1 0 (chiC κ) (g t ω + smoothDist upperHalfPlaneOpens u₀) ψ' := fun ψ' =>
    (LQGMetric.measurable_distOn_apply ψ').comp (@Chart.measurable_chartTransport_random' Ω
      (germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t) _ hΦ
      (fun z => hm _ (hdom z)) (fun z => (hfwd z).mono hm le_rfl) (fun z => (hliftm z).mono hm le_rfl) hliftc
      _ hgm 1 0 (chiC κ))
  have hc : ∀ ψ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ F →
      P[fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hΦ ω') 1 0 (chiC κ) (h ω') ψ' : ℂ)) |
        lineFiltC P 𝓖 0] ω = gaussCF (β₁ ω) ψ' := by
    intro ψ'
    have hXm : Measurable fun ω => Chart.chartTransport (hΦ ω) 1 0 (chiC κ) (h ω) ψ' :=
      (LQGMetric.measurable_distOn_apply ψ').comp hY
    filter_upwards [hlaw, condExp_ae_eq_integral_condExpKernel hm₀Ω (GFF.integrable_exp_I_mul (P := P) hXm)]
      with ω h1 h2 hωF
    rw [h2]
    exact Exist.StagedLaw.integral_cexp_eq_gaussCF (hsort ω) (h1 hωF) ψ'
  have hGL : seedCell κ ψ β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩ {ω | (S.ver m).a t ω = 0} ⊆ F :=
    fun ω hω => hω.1.1.1.1
  have hpair := ae_pairing_eq_of_le_on hm hm'Ω hY hβ₁ hM' hF hE₀m hGL hc hR1 φ
  -- the equation
  filter_upwards [hpair] with ω hω hcell hlt h0
  have hωE : ω ∈ seedCell κ ψ β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩
      {ω | (S.ver m).a t ω = 0} := ⟨⟨hcell, hlt⟩, h0⟩
  have e : h ω - WholeField.centredField h u₀ ω = smoothDist upperHalfPlaneOpens u₀ := by
    simp only [WholeField.centredField, sub_sub_cancel]
  rw [e]
  have e1 : Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ)
      (g t ω + smoothDist upperHalfPlaneOpens u₀) φ =
      Chart.chartTransport (hΦ ω) 1 0 (chiC κ) (g t ω + smoothDist upperHalfPlaneOpens u₀) φ +
        ψ * chiC κ * ∫ z, φ z := by
    rw [Chart.chartTransport_apply', Chart.chartTransport_apply', Chart.oneDist_apply]
    ring
  rw [e1, hω hωE, h0, ENNReal.toNNReal_zero, NNReal.coe_zero]
  -- the coupling mean at time `0`
  have hW0 : (fun s : ℝ => (S.ver m).W s.toNNReal ω) 0 = 0 := by simp [(S.ver m).W_zero ω]
  have hxL := (FCDet.isOrderedForceWord_typeXL (κ := κ) (θ := ψ) (nL := w.1) (nR := w.2.1)
    (ρL := typedRhoL w) (ρR := typedRhoR w) (β₁ ω)).2.1
  have hxR := (FCDet.isOrderedForceWord_typeXL (κ := κ) (θ := ψ) (nL := w.1) (nR := w.2.1)
    (ρL := typedRhoL w) (ρR := typedRhoR w) (β₁ ω)).2.2.2
  have hbhe := isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := typedRhoL w) (ρR := typedRhoR w)
    (W := (S.ver m).W) (VL := geomLW (S.ver m).W (cellXL κ ψ β₁ w))
    (VR := geomRW (S.ver m).W (cellXR κ ψ β₁ w)) ω 0
  have eL : (fun i => geomLW (S.ver m).W (cellXL κ ψ β₁ w) i 0 ω - (S.ver m).W 0 ω) = cellXL κ ψ β₁ w ω := by
    funext i
    rw [geomLW_zero (S.ver m).W_cont (S.ver m).W_zero (hxL i), (S.ver m).W_zero ω, sub_zero]
  have eR : (fun j => geomRW (S.ver m).W (cellXR κ ψ β₁ w) j 0 ω - (S.ver m).W 0 ω) = cellXR κ ψ β₁ w ω := by
    funext j
    rw [geomRW_zero (S.ver m).W_cont (S.ver m).W_zero (hxR j), (S.ver m).W_zero ω, sub_zero]
  rw [eL, eR] at hbhe
  have hmean := eqOn_typed_mean hκ hcell.1 (hsort ω) hbhe
  have hcont : ContinuousOn (β₁ ω).mean H :=
    Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd (BoundaryWord.isBoundedHarmonicExtension_mean _ (hsort ω)).1
  have hi₁ : Integrable fun z => (β₁ ω).mean z * φ z := integrable_mul_testOn_of_continuousOn hcont φ
  have hi₂ : Integrable fun z => φ z := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hRHS : ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((0 : ℝ≥0) : ℝ)
      (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ ψ β₁ w))
        (geomRW (S.ver m).W (cellXR κ ψ β₁ w)) ω 0) z * φ z =
      ∫ z, ((β₁ ω).mean z * φ z + ψ * chiC κ * φ z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · have hzH : z ∈ H := φ.tsupport_subset hz
      have hz0 : z ≠ 0 := fun h' => by rw [h'] at hzH; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hzH)
      show couplingMean κ _ ((0 : ℝ≥0) : ℝ) _ z * φ z = _
      rw [NNReal.coe_zero, Coupling.MartMeans2.couplingMean_zero κ hW0 _ hz0, hmean hzH]
      ring
    · show _ * φ z = (β₁ ω).mean z * φ z + ψ * chiC κ * φ z
      rw [image_eq_zero_of_notMem_tsupport hz]
      ring
  rw [NNReal.coe_zero] at hRHS
  rw [hRHS, integral_add hi₁ (hi₂.const_mul _), integral_const_mul]

end Zero

end InteractingSLE.Theorem14.SB.Om
