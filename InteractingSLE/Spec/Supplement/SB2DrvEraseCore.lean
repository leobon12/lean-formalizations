/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvEraseLaw

/-!
# SB2(1)'s erasure, part 2: the entrance σ-algebra leaves the same conditional field in `D_A`

Packet PROVE-T14-SB2DRV (round 3), the probabilistic core of clause (E2) (supplement p. 632: "The initial erased
portion adds no set in `D_A` [...] Thus even the full erased history, its entry germ and stopping flags leave the same
conditional field in `D_A`"). For every test function `φ`, almost surely on the launch event with `supp φ ⊆ D_A`:

  `E[exp(i⟨h, φ⟩) | 𝒢'] = E[exp(i⟨h, φ⟩) | pastSigma (k + 1)]`   (**`ae_condExp_cexp_marks_eq`**),

for the entrance σ-algebra `𝒢' = D.marks`. Proof: for each cap `n`, the finite union `B_n` (on a nice version of the
retained prefix) is a marked local set for the marks `𝓜_n`; given its germs and marks the field on `ℍ \ B_n` is its
local-set mean plus a zero-boundary GFF (`RelSafeS.ae_condExp_cexp_marked`); on `D_A` the mean is the chart mean of the
retained past (`ae_apply_eq_chartMean_of_chartLaw`, the marks of `B_n` contain the retained past) and the covariance is
`G_{D_A}` (`D_A` is clopen in `ℍ \ B_n`, `ae_dom_iterSet`), which is the conditional characteristic functional given
the retained past (`ae_condExp_cexp_of_chartLaw`); the tower property (`ae_condExp_eq_of_le_of_sup`) gives the identity
given `𝓜_n`, and Lévy's upward theorem passes it to `𝒢' = ⨆ 𝓜_n`.

Also **`exists_mean_hcond`**: one mean process `M₀` with the Gaussian conditional characteristic functionals on `D_A`
given both σ-algebras (the input of `Restart.ae_condExp_cexp_chartTransport_random_on`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw LocalSets Sec6 Restart WalkInf

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- The chart mean of a test function in the launch chart record. -/
def chartMean (I : K2LaunchInputs κ b jumps P h E k u ψ) (φ : TestOn upperHalfPlaneOpens) (ω : Ω) : ℝ :=
  ∫ z, ((sortedRep (I.word ω)).mean ((I.chart ω).1 z) - chiC κ * (I.chart ω).2.2 z) * φ z

/-- **The erasure data**: the finite unions on a nice version of the retained prefix, with their marked locality,
local-set means, the identification of the means with the chart mean on `D_A`, and the clopen geometry. -/
theorem exists_eraseData (hgeo : SB2ErasedAvoidStatement.{u}) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∃ (B : ℕ → Ω → Set ℂ) (g : ℕ → Ω → DistOn upperHalfPlaneOpens),
      (∀ n, Measurable[mΩ, hittingSigma] (B n)) ∧ (∀ n ω, B n ω ⊆ H ∧ IsOpen (H \ B n ω)) ∧
      (∀ n, WholeField.IsHistoryAvoidanceLocal
        (iterMarks (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc (capLife ζ) D.point hitQ n)
        (B n) (WholeField.centredField h u₀) P) ∧
      (∀ n, IsLocalSetMean (B n) (WholeField.centredField h u₀) P (g n)) ∧
      (∀ n (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
        tsupport φ ⊆ (I.chart ω).dom → g n ω φ = chartMean I φ ω - ∫ z, u₀ z * φ z) ∧
      (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → ∀ n,
        ((I.chart ω).dom : Set ℂ) ⊆ H \ B n ω ∧ IsOpen ((H \ B n ω) \ (I.chart ω).dom)) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have h𝒢 := hS.2.1 (k + 1)
  have hhm : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField HP.field.1 u₀
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  obtain ⟨A'', hA''H, hA''o, hA''ae, hA''m⟩ := exists_walkVersion h12p h13 HP hu₀
  obtain ⟨hev0, -, hloc0⟩ := walkPrefix_markedLocal h12p h13 HP hu₀ (k + 1)
  have hdet := EntranceUnion.past_le_aeSigma h12p h13 HP u₀
  have hlocA := WalkLaw.isHistoryAvoidanceLocal_congr_ae (hA''ae.mono fun ω h' => h'.symm) hloc0
  have hevA : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P]
        {ω | Disjoint (A'' ω) U} := by
    intro U hU
    obtain ⟨E', hE', hEE'⟩ := hev0 U hU
    obtain ⟨K, hK, hE'K⟩ := hdet E' hE'
    refine ⟨K, hK, Filter.EventuallyEq.trans ?_ (hEE'.trans hE'K)⟩
    filter_upwards [hA''ae] with ω hω
    show Disjoint (A'' ω) U = _
    rw [hω]
  have hA := fun U G hUH hG hd F hF =>
    complSigma_of_isHistoryAvoidanceLocal (P := P) hhm hlocA hevA hdet U G hUH hG hd F hF
  have hp : Measurable D.point := D.point_meas.mono h𝒢 le_rfl
  have hRm : ∀ j, Measurable (ruleHist (D.ηc j) (capLife ζ j) D.point hitQ) := by
    intro j
    have hcm : Measurable fun ω => pathCoord (D.ηc j ω) := Measurable.of_eval fun q => D.paths.meas j q
    have hτ : Measurable fun ω => hitQ (D.point ω) (pathCoord (D.ηc j ω)) :=
      Measurable.comp (g := Function.uncurry hitQ) (f := fun ω => (D.point ω, pathCoord (D.ηc j ω)))
        measurable_hitQ (hp.prodMk hcm)
    exact (measurable_histOf.comp (hτ.prodMk hcm)).prodMk
      (measurable_lifeRec.comp ((D.paths.life_meas j).prodMk hτ))
  set B : ℕ → Ω → Set ℂ := fun n => iterSet A'' D.ηc D.point hitQ n with hBdef
  have hBm : ∀ n, Measurable[mΩ, hittingSigma] (B n) := fun n =>
    WalkMean.measurable_hitting_of_avoid le_rfl fun U hUH =>
      measurableSet_disjoint_iterSet D.paths.cont D.paths.start hA''m hRm n hUH
  have hBc : ∀ n ω, B n ω ⊆ H ∧ IsOpen (H \ B n ω) := fun n ω =>
    ⟨iterSet_subset_H hA''H n ω,
      isOpen_H_sdiff_iterSet (hA''o ω) (fun j => isClosed_image_frozen (D.paths.cont j ω) (D.frozen j ω) _) n⟩
  have hBloc : ∀ n, WholeField.IsHistoryAvoidanceLocal
      (iterMarks (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc (capLife ζ) D.point hitQ n)
      (B n) (WholeField.centredField h u₀) P := fun n =>
    WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF =>
      mem_complSigma_iterSet hhm hA D.paths D.point_meas measurable_hitQ isParamGalmarino_hitQ n U G hUH hG hd F hF
  have hBlocal : ∀ n, IsLocalSet (B n) (WholeField.centredField h u₀) P := fun n =>
    ((isLocalSet_tfae hh0 (hBm n) (Eventually.of_forall (hBc n))).out 4 1).2 (hBloc n).isAvoidanceLocal
  choose g hg using fun n => IsLocalSet.exists_isLocalSetMean hh0 (hBm n) (hBlocal n)
  have hAD := ae_dom_iterSet hgeo HP I D hA''o hA''ae
  obtain ⟨hc, hliftc, -, hdom, hfwd, hCm, hliftm⟩ := I.chart_measurable
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma HP.boundary hS.1 (HP.drivers_regular _) (k + 1)
  have htr : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      IsChartTransport (I.chart ω) 1 0 (chiC κ) (h ω) (chartField I h ω) :=
    Eventually.of_forall fun ω _ => isChartTransport_chartField I ω
  refine ⟨B, g, hBm, hBc, hBloc, hg, fun n φ => ?_, hAD⟩
  have hmark𝒢 : WholeField.IsHistoryAvoidanceLocal
      (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) (B n) (WholeField.centredField h u₀) P :=
    fun U G hUH hG hd F hF => hBloc n U G hUH hG hd F (le_iterMarks n _ hF)
  exact Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw h𝒢 hc hdom hfwd hCm hliftm hliftc HP.field hu₀
    (measurable_chartField I HP.field.1 h𝒢) hL𝒢 htr (fun ψ' => ae_condExp_chartField_eq_gaussCF HP I ψ')
    (hBm n) (hBlocal n) hmark𝒢 (hAD.mono fun ω hω hl => hω hl n) (hg n) φ

/-- **The erasure core and a common mean process.** There is a mean process `M₀` with the Gaussian conditional
characteristic functionals on `D_A`, almost surely on the launch event, both given the retained past and given the
entrance σ-algebra. -/
theorem exists_mean_hcond (hgeo : SB2ErasedAvoidStatement.{u}) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∃ M₀ : Ω → DistOn upperHalfPlaneOpens,
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
        tsupport φ ⊆ (I.chart ω).dom →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
          pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] ω =
          Complex.exp (Complex.I * (M₀ ω φ : ℂ) -
            (((1 / 2 : ℝ) * zeroGFFTestCov ((I.chart ω).dom : Set ℂ) φ φ : ℝ) : ℂ))) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
        tsupport φ ⊆ (I.chart ω).dom →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | D.marks] ω =
          Complex.exp (Complex.I * (M₀ ω φ : ℂ) -
            (((1 / 2 : ℝ) * zeroGFFTestCov ((I.chart ω).dom : Set ℂ) φ φ : ℝ) : ℂ))) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have h𝒢 := hS.2.1 (k + 1)
  have hhm : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField HP.field.1 u₀
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  obtain ⟨B, g, hBm, hBc, hBloc, hg, hid, hAD⟩ := exists_eraseData hgeo h12p h13 HP I hu₀ D
  obtain ⟨hc, hliftc, -, hdom, hfwd, hCm, hliftm⟩ := I.chart_measurable
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma HP.boundary hS.1 (HP.drivers_regular _) (k + 1)
  have htr : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      IsChartTransport (I.chart ω) 1 0 (chiC κ) (h ω) (chartField I h ω) :=
    Eventually.of_forall fun ω _ => isChartTransport_chartField I ω
  -- the physical law given the retained past
  have hphys := fun φ : TestOn upperHalfPlaneOpens =>
    Sec5.CrossCond.Staged.ae_condExp_cexp_of_chartLaw h𝒢 hc hdom hfwd hCm hliftm hliftc HP.field.1
      (measurable_chartField I HP.field.1 h𝒢) hL𝒢 htr (fun ψ' => ae_condExp_chartField_eq_gaussCF HP I ψ') φ
  -- the marks of the finite unions
  have hMle : ∀ n, iterMarks (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc (capLife ζ) D.point hitQ n ≤ mΩ :=
    fun n => (le_iSup (iterMarks _ D.ηc (capLife ζ) D.point hitQ) n).trans (D.marks_le HP)
  refine ⟨fun ω => g 0 ω + (h ω - WholeField.centredField h u₀ ω), ?_, ?_⟩
  · intro φ
    filter_upwards [hphys φ, hid 0 φ] with ω h1 h2 hl hs
    rw [h1 hl hs]
    have e : (g 0 ω + (h ω - WholeField.centredField h u₀ ω)) φ = chartMean I φ ω := by
      show g 0 ω φ + (h ω φ - WholeField.centredField h u₀ ω φ) = _
      rw [h2 hl hs, WholeField.centredField_apply h hu₀.1 ω φ]
      ring
    rw [e]
    rfl
  · intro φ
    set U₀ : ℝ := ∫ z, u₀ z * φ z with hU₀
    set X : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) with hXdef
    set X₀ : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) with hX₀def
    have hXm : Measurable X :=
      Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((LQGMetric.measurable_distOn_apply φ).comp HP.field.1)))
    have hX : Integrable X P := Integrable.of_bound hXm.aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
    have hXX₀ : X = Complex.exp (Complex.I * (U₀ : ℂ)) • X₀ := by
      funext ω'
      simp only [hXdef, hX₀def, Pi.smul_apply, smul_eq_mul, ← Complex.exp_add,
        WholeField.centredField_apply h hu₀.1 ω' φ]
      congr 1
      push_cast
      ring
    have hSm : MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)]
        (launchSet κ b jumps E (k + 1) ∩ {ω | tsupport φ ⊆ (I.chart ω).dom}) :=
      hL𝒢.inter (@Sec7.StripSideHeightProb.measurableSet_tsupport_subset_dom Ω
        (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) I.chart hCm φ)
    -- each cap
    have hn : ∀ n, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) ∩ {ω | tsupport φ ⊆ (I.chart ω).dom} →
        P[X | iterMarks (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc (capLife ζ) D.point hitQ n] ω =
        P[X | pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] ω := by
      intro n
      refine ae_condExp_eq_of_le_of_sup (le_iterMarks n) le_sup_right
        (sup_le (germSigma_le (hBm n) hhm) (hMle n)) hSm hX ?_
      have hsmul := condExp_smul (μ := P) (Complex.exp (Complex.I * (U₀ : ℂ))) X₀
        (germSigma (B n) (WholeField.centredField h u₀) ⊔ iterMarks (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (k + 1)) D.ηc (capLife ζ) D.point hitQ n)
      filter_upwards [hsmul, Supp8.RelSafeS.ae_condExp_cexp_marked hh0 (hBm n) (hBc n) (hMle n) (hBloc n) (hg n) φ,
        hid n φ, hAD, hphys φ] with ω h1 h2 h3 h4 h5 hω
      obtain ⟨hl, hs⟩ := hω
      have hcov : zeroGFFTestCov (H \ B n ω) φ φ = zeroGFFTestCov ((I.chart ω).dom : Set ℂ) φ φ :=
        zeroGFFTestCov_eq_of_isClopen (hBc n ω).2 sdiff_subset (I.chart ω).dom.isOpen (h4 hl n).1 (h4 hl n).2 φ hs
      have hL : P[X | germSigma (B n) (WholeField.centredField h u₀) ⊔ iterMarks (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (k + 1)) D.ηc (capLife ζ) D.point hitQ n] ω =
          Complex.exp (Complex.I * (U₀ : ℂ)) * P[X₀ | germSigma (B n) (WholeField.centredField h u₀) ⊔
            iterMarks (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc (capLife ζ) D.point hitQ n] ω := by
        rw [hXX₀]
        exact h1
      have h5' : P[X | pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] ω =
          Complex.exp (Complex.I * (chartMean I φ ω : ℂ) -
            (((1 / 2 : ℝ) * zeroGFFTestCov ((I.chart ω).dom : Set ℂ) φ φ : ℝ) : ℂ)) := h5 hl hs
      rw [hL, h2, h3 hl hs, hcov, h5']
      rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    let F : Filtration ℕ mΩ := ⟨fun n => iterMarks (pastSigma κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
      (k + 1)) D.ηc (capLife ζ) D.point hitQ n, iterMarks_mono, hMle⟩
    have hlim := ae_condExp_iSup_eq_of_forall F hX hn
    have e : D.marks = ⨆ n, F n := rfl
    filter_upwards [hlim, hphys φ, hid 0 φ] with ω h1 h2 h3 hl hs
    rw [e, h1 ⟨hl, hs⟩, h2 hl hs]
    have e' : (g 0 ω + (h ω - WholeField.centredField h u₀ ω)) φ = chartMean I φ ω := by
      show g 0 ω φ + (h ω φ - WholeField.centredField h u₀ ω φ) = _
      rw [h3 hl hs, WholeField.centredField_apply h hu₀.1 ω φ]
      ring
    rw [e']
    rfl

end InteractingSLE.Theorem14.SB.Lv
