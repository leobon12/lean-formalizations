/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Ge8Germ

/-!
# Aux. lemma 50 for `κ ≥ 8`: the variance identity for frozen piece means, (HGV5)–(HGV8)

Packet PROVE-AUX50C. Specification Aux. lemma 50, proof (`source/spec/p193-240.md` L837–L870, pp. 236–238):
"For nested raw marked sigma-algebras the squared `L²` distance between the two conditional means is the
expectation of the difference of these conditional variances", (HGV5) and (HGV8).

A test `φ = ∑ₖ ψₖ` is cut into pieces; each piece `ψₖ` is frozen at a driving stop `τₖ ≤ N` at which it is still
active (its mean there is the explicit active mean `E[(h, ψₖ) | 𝓕_{τₖ}]`). The defect of the frozen means against the
germ conditional mean at `N` is computed exactly:

`E[(N_N(φ) − ∑ₖ m_{τₖ}(ψₖ))²] = ∑_{k,j} E[G_{D_{τₖ ∨ τⱼ}}(ψₖ, ψⱼ) − G_{D_N}(ψₖ, ψⱼ)]`  (`integral_sq_germ_sub_sum_eq`).

No stochastic integral is used: the increments of the germ conditional means over `[τₖ ∨ τⱼ, N]` are orthogonal to the
germ at `τₖ ∨ τⱼ`, and before `τₖ ∨ τⱼ` one of the two pieces is still frozen (its mean at `τₖ ∨ τⱼ` is its active
mean at its own time). The abstract step is `integral_mul_sub_condExp_eq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Aux50Ge8

open QuantumZipper LQGMetric LocalSets WholeField Coupling

/-! ### The abstract step -/

section Abstract

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- `∫ P[X | m] g = ∫ X g` for `g` square integrable and `m`-measurable. -/
theorem integral_condExp_mul_eq {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X g : Ω → ℝ} (hX : MemLp X 2 P)
    (hg : MemLp g 2 P) (hgm : StronglyMeasurable[m] g) :
    ∫ ω, (P[X | m]) ω * g ω ∂P = ∫ ω, X ω * g ω ∂P := by
  have h1 : P[g * X | m] =ᵐ[P] g * P[X | m] :=
    condExp_mul_of_stronglyMeasurable_left hgm (hg.integrable_mul hX) (hX.integrable one_le_two)
  calc ∫ ω, (P[X | m]) ω * g ω ∂P = ∫ ω, (g * P[X | m]) ω ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [Pi.mul_apply]; ring
    _ = ∫ ω, (P[g * X | m]) ω ∂P := integral_congr_ae h1.symm
    _ = ∫ ω, (g * X) ω ∂P := integral_condExp hm
    _ = ∫ ω, X ω * g ω ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [Pi.mul_apply]; ring

/-- **Two frozen increments.** Let `ma, mb ≤ mσ ≤ mN` be σ-algebras, `X, X'` square integrable with conditional
covariances `C` given `mσ` and `C'` given `mN`, and suppose that almost surely either the mean of `X` given `mσ` is its
mean given `ma` or the mean of `X'` given `mσ` is its mean given `mb`. Then
`E[(E[X | mN] − E[X | ma]) (E[X' | mN] − E[X' | mb])] = E[C] − E[C']`. -/
theorem integral_mul_sub_condExp_eq {ma mb mσ mN : MeasurableSpace Ω} (haσ : ma ≤ mσ) (hbσ : mb ≤ mσ)
    (hσN : mσ ≤ mN) (hN : mN ≤ mΩ) {X X' C C' : Ω → ℝ} (hX : MemLp X 2 P) (hX' : MemLp X' 2 P)
    (hCσ : P[X * X' | mσ] =ᵐ[P] P[X | mσ] * P[X' | mσ] + C)
    (hCN : P[X * X' | mN] =ᵐ[P] P[X | mN] * P[X' | mN] + C')
    (hloc : ∀ᵐ ω ∂P, (P[X | mσ]) ω = (P[X | ma]) ω ∨ (P[X' | mσ]) ω = (P[X' | mb]) ω) :
    Integrable C P ∧ Integrable C' P ∧
      ∫ ω, ((P[X | mN]) ω - (P[X | ma]) ω) * ((P[X' | mN]) ω - (P[X' | mb]) ω) ∂P =
        ∫ ω, C ω ∂P - ∫ ω, C' ω ∂P := by
  have hσ : mσ ≤ mΩ := hσN.trans hN
  -- square integrable conditional means
  have hN2 : MemLp (P[X | mN]) 2 P := hX.condExp one_le_two
  have hN2' : MemLp (P[X' | mN]) 2 P := hX'.condExp one_le_two
  have hσ2 : MemLp (P[X | mσ]) 2 P := hX.condExp one_le_two
  have hσ2' : MemLp (P[X' | mσ]) 2 P := hX'.condExp one_le_two
  have ha2 : MemLp (P[X | ma]) 2 P := hX.condExp one_le_two
  have hb2' : MemLp (P[X' | mb]) 2 P := hX'.condExp one_le_two
  have hXX : Integrable (X * X') P := hX.integrable_mul hX'
  -- integrability of the covariances
  have hCi : Integrable C P := by
    have : C =ᵐ[P] P[X * X' | mσ] - P[X | mσ] * P[X' | mσ] := by
      filter_upwards [hCσ] with ω hω
      simp only [Pi.sub_apply, hω, Pi.add_apply, Pi.mul_apply]; ring
    exact (integrable_condExp.sub (hσ2.integrable_mul hσ2')).congr this.symm
  have hC'i : Integrable C' P := by
    have : C' =ᵐ[P] P[X * X' | mN] - P[X | mN] * P[X' | mN] := by
      filter_upwards [hCN] with ω hω
      simp only [Pi.sub_apply, hω, Pi.add_apply, Pi.mul_apply]; ring
    exact (integrable_condExp.sub (hN2.integrable_mul hN2')).congr this.symm
  refine ⟨hCi, hC'i, ?_⟩
  -- the second moments of the conditional means
  have hmomσ : ∫ ω, (P[X | mσ]) ω * (P[X' | mσ]) ω ∂P = ∫ ω, X ω * X' ω ∂P - ∫ ω, C ω ∂P := by
    have h1 : ∫ ω, (P[X * X' | mσ]) ω ∂P = ∫ ω, (X * X') ω ∂P := integral_condExp hσ
    rw [integral_congr_ae hCσ, integral_add' (hσ2.integrable_mul hσ2') hCi] at h1
    simp only [Pi.mul_apply] at h1
    linarith
  have hmomN : ∫ ω, (P[X | mN]) ω * (P[X' | mN]) ω ∂P = ∫ ω, X ω * X' ω ∂P - ∫ ω, C' ω ∂P := by
    have h1 : ∫ ω, (P[X * X' | mN]) ω ∂P = ∫ ω, (X * X') ω ∂P := integral_condExp hN
    rw [integral_congr_ae hCN, integral_add' (hN2.integrable_mul hN2') hC'i] at h1
    simp only [Pi.mul_apply] at h1
    linarith
  -- the cross moments: the mean given `mN` tested against `mσ`-measurable variables
  have hsm : ∀ {m : MeasurableSpace Ω}, m ≤ mσ → ∀ {Y : Ω → ℝ}, StronglyMeasurable[mσ] (P[Y | m]) := by
    intro m hm Y
    exact stronglyMeasurable_condExp.mono hm
  have cross : ∀ {Y Z : Ω → ℝ}, MemLp Y 2 P → MemLp Z 2 P → StronglyMeasurable[mσ] Z →
      ∫ ω, (P[Y | mN]) ω * Z ω ∂P = ∫ ω, (P[Y | mσ]) ω * Z ω ∂P := by
    intro Y Z hY hZ hZm
    rw [integral_condExp_mul_eq hN hY hZ (hZm.mono hσN), integral_condExp_mul_eq hσ hY hZ hZm]
  set U : Ω → ℝ := fun ω => (P[X | mσ]) ω - (P[X | ma]) ω with hU
  set U' : Ω → ℝ := fun ω => (P[X' | mσ]) ω - (P[X' | mb]) ω with hU'
  have hU2 : MemLp U 2 P := hσ2.sub ha2
  have hU2' : MemLp U' 2 P := hσ2'.sub hb2'
  have hUm : StronglyMeasurable[mσ] U := stronglyMeasurable_condExp.sub (hsm haσ)
  have hUm' : StronglyMeasurable[mσ] U' := stronglyMeasurable_condExp.sub (hsm hbσ)
  have hUU : ∫ ω, U ω * U' ω ∂P = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hloc] with ω hω
    rcases hω with h | h
    · simp only [hU, h, sub_self, zero_mul, Pi.zero_apply]
    · simp only [hU', h, sub_self, mul_zero, Pi.zero_apply]
  have hexp : ∀ ω, ((P[X | mN]) ω - (P[X | ma]) ω) * ((P[X' | mN]) ω - (P[X' | mb]) ω) =
      ((P[X | mN]) ω * (P[X' | mN]) ω - (P[X | mN]) ω * (P[X' | mσ]) ω) -
        ((P[X | mσ]) ω * (P[X' | mN]) ω - (P[X | mσ]) ω * (P[X' | mσ]) ω) +
        (((P[X | mN]) ω * U' ω - (P[X | mσ]) ω * U' ω) +
          ((U ω * (P[X' | mN]) ω - U ω * (P[X' | mσ]) ω) + U ω * U' ω)) := by
    intro ω; simp only [hU, hU']; ring
  -- each term
  have t1 := cross hX hσ2' stronglyMeasurable_condExp
  have t2 : ∫ ω, (P[X | mσ]) ω * (P[X' | mN]) ω ∂P = ∫ ω, (P[X | mσ]) ω * (P[X' | mσ]) ω ∂P := by
    have := cross hX' hσ2 stronglyMeasurable_condExp
    simp only [mul_comm] at this ⊢
    exact this
  have t3 := cross hX hU2' hUm'
  have t4 : ∫ ω, U ω * (P[X' | mN]) ω ∂P = ∫ ω, U ω * (P[X' | mσ]) ω ∂P := by
    have := cross hX' hU2 hUm
    simp only [mul_comm] at this ⊢
    exact this
  have i1 : Integrable (fun ω => (P[X | mN]) ω * (P[X' | mN]) ω) P := hN2.integrable_mul hN2'
  have i2 : Integrable (fun ω => (P[X | mN]) ω * (P[X' | mσ]) ω) P := hN2.integrable_mul hσ2'
  have i3 : Integrable (fun ω => (P[X | mσ]) ω * (P[X' | mN]) ω) P := hσ2.integrable_mul hN2'
  have i4 : Integrable (fun ω => (P[X | mσ]) ω * (P[X' | mσ]) ω) P := hσ2.integrable_mul hσ2'
  have i5 : Integrable (fun ω => (P[X | mN]) ω * U' ω) P := hN2.integrable_mul hU2'
  have i6 : Integrable (fun ω => U ω * (P[X' | mN]) ω) P := hU2.integrable_mul hN2'
  have i7 : Integrable (fun ω => (P[X | mσ]) ω * U' ω) P := hσ2.integrable_mul hU2'
  have i8 : Integrable (fun ω => U ω * (P[X' | mσ]) ω) P := hU2.integrable_mul hσ2'
  have i9 : Integrable (fun ω => U ω * U' ω) P := hU2.integrable_mul hU2'
  have j12 : Integrable (fun ω => (P[X | mN]) ω * (P[X' | mN]) ω - (P[X | mN]) ω * (P[X' | mσ]) ω) P :=
    i1.sub i2
  have j34 : Integrable (fun ω => (P[X | mσ]) ω * (P[X' | mN]) ω - (P[X | mσ]) ω * (P[X' | mσ]) ω) P :=
    i3.sub i4
  have jA : Integrable (fun ω => ((P[X | mN]) ω * (P[X' | mN]) ω - (P[X | mN]) ω * (P[X' | mσ]) ω) -
      ((P[X | mσ]) ω * (P[X' | mN]) ω - (P[X | mσ]) ω * (P[X' | mσ]) ω)) P := j12.sub j34
  have j57 : Integrable (fun ω => (P[X | mN]) ω * U' ω - (P[X | mσ]) ω * U' ω) P := i5.sub i7
  have j68 : Integrable (fun ω => U ω * (P[X' | mN]) ω - U ω * (P[X' | mσ]) ω) P := i6.sub i8
  have j689 : Integrable (fun ω => (U ω * (P[X' | mN]) ω - U ω * (P[X' | mσ]) ω) + U ω * U' ω) P :=
    j68.add i9
  have jB : Integrable (fun ω => ((P[X | mN]) ω * U' ω - (P[X | mσ]) ω * U' ω) +
      ((U ω * (P[X' | mN]) ω - U ω * (P[X' | mσ]) ω) + U ω * U' ω)) P := j57.add j689
  rw [integral_congr_ae (Eventually.of_forall hexp), integral_add jA jB, integral_sub j12 j34,
    integral_sub i1 i2, integral_sub i3 i4, integral_add j57 j689, integral_sub i5 i7,
    integral_add j68 i9, integral_sub i6 i8]
  rw [t1, t2, t3, t4, hUU, hmomN, hmomσ]
  ring

end Abstract

/-! ### The coupling -/

section Coupling

universe v

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- An announcing sequence of the lifetime, when the lifetime is infinite. -/
theorem exists_announcingSeq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∃ σ₀ : ℕ → Ω → ℝ≥0, IsAnnouncingSeq (drivingFiltration P hX) P ζ σ₀ := by
  have hE := hC.1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hζ] with ω hp hz
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hz
      exact ENNReal.zero_ne_top hz
    obtain ⟨_, h'⟩ := hF.exists
    exact h'
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ₀, hσ₀, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B)
    (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  exact ⟨σ₀, hσ₀⟩

omit [IsProbabilityMeasure P] in
/-- Germ σ-algebras are nested along ordered real driving stops. -/
theorem histGerm_le_of_le (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : IsAnnouncingSeq (drivingFiltration P hX) P ζ σ₀) {u₀ : ℂ → ℝ} {a b : Ω → ℝ≥0}
    (ha : IsStoppingTime (drivingFiltration P hX) fun ω => (a ω : WithTop ℝ≥0))
    (hb : IsStoppingTime (drivingFiltration P hX) fun ω => (b ω : WithTop ℝ≥0)) (hab : ∀ ω, a ω ≤ b ω)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {Aa Ab : Ω → Set ℂ} (hAa : Measurable[mΩ, hittingSigma] Aa)
    (hAb : Measurable[mΩ, hittingSigma] Ab)
    (hAaK : ∀ᵐ ω ∂P, Aa ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (a ω))
    (hAbK : ∀ᵐ ω ∂P, Ab ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (b ω)) :
    histGerm ha.measurableSpace Aa (centredField h u₀) ≤ histGerm hb.measurableSpace Ab (centredField h u₀) := by
  refine histGerm_hull_mono hC.1 hX hσ₀ ha hb (fun ω => WithTop.coe_le_coe.2 (hab ω))
    (hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top)
    (hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top) hAa hAb
    (hAaK.mono fun ω hω => by rw [hω, WithTop.untopD_coe]) (hAbK.mono fun ω hω => by rw [hω, WithTop.untopD_coe])
    (measurable_centredField hC.2.1 u₀)

omit [IsProbabilityMeasure P] in
theorem isStoppingTime_max_coe {𝓖 : Filtration ℝ≥0 mΩ} {a b : Ω → ℝ≥0}
    (ha : IsStoppingTime 𝓖 fun ω => (a ω : WithTop ℝ≥0)) (hb : IsStoppingTime 𝓖 fun ω => (b ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓖 fun ω => ((max (a ω) (b ω) : ℝ≥0) : WithTop ℝ≥0) := by
  have := ha.max hb
  convert this using 2 with ω
  exact WithTop.coe_max _ _

/-- **One pair of frozen pieces** (HGV5) at the level of expectations: for pieces `ψ, ψ'` active at driving stops
`a, b ≤ N`,
`E[(N_N(ψ) − m_a(ψ)) (N_N(ψ') − m_b(ψ'))] = E[G_{D_{a ∨ b}}(ψ, ψ')] − E[G_{D_N}(ψ, ψ')]`,
`N_N` the germ conditional mean of the centred field at `N` and `m_a(ψ) = E[(h, ψ) | 𝓕_a] − ∫ u₀ ψ`. -/
theorem integral_mul_germ_sub_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {N : ℕ}
    (hN : IsStoppingTime (drivingFiltration P hX) fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0)) {AN : Ω → Set ℂ}
    (hAN : Measurable[mΩ, hittingSigma] AN)
    (hANK : ∀ᵐ ω ∂P, AN ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((N : ℝ≥0) : ℝ)) {a b : Ω → ℝ≥0}
    (ha : IsStoppingTime (drivingFiltration P hX) fun ω => (a ω : WithTop ℝ≥0))
    (hb : IsStoppingTime (drivingFiltration P hX) fun ω => (b ω : WithTop ℝ≥0)) (haN : ∀ ω, a ω ≤ N)
    (hbN : ∀ ω, b ω ≤ N) (ψ ψ' : TestOn upperHalfPlaneOpens)
    (hψa : ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a ω)))
    (hψb : ∀ᵐ ω ∂P, Disjoint (tsupport ψ') (fwdHull (fun s : ℝ => W s.toNNReal ω) (b ω))) :
    Integrable (fun ω => covAt W (max (a ω) (b ω)) ψ ψ' ω) P ∧ Integrable (fun ω => covAt W N ψ ψ' ω) P ∧
      ∫ ω, ((P[fun ω' => centredField h u₀ ω' ψ | histGerm hN.measurableSpace AN (centredField h u₀)]) ω -
          ((P[fun ω' => h ω' ψ | ha.measurableSpace]) ω - ∫ z, u₀ z * ψ z)) *
        ((P[fun ω' => centredField h u₀ ω' ψ' | histGerm hN.measurableSpace AN (centredField h u₀)]) ω -
          ((P[fun ω' => h ω' ψ' | hb.measurableSpace]) ω - ∫ z, u₀ z * ψ' z)) ∂P =
        ∫ ω, covAt W (max (a ω) (b ω)) ψ ψ' ω ∂P - ∫ ω, covAt W N ψ ψ' ω ∂P := by
  obtain ⟨σ₀, hσ₀⟩ := exists_announcingSeq hC hκ hX hζ
  have hσ := isStoppingTime_max_coe ha hb
  have hlt : ∀ c : Ω → ℝ≥0, ∀ᵐ ω ∂P, (c ω : ℝ≥0∞) < ζ ω := fun c =>
    hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top
  obtain ⟨Aa, hAa, hAaK, -⟩ := exists_hullVersion hC hκ hX ha (hlt a)
  obtain ⟨Ab, hAb, hAbK, -⟩ := exists_hullVersion hC hκ hX hb (hlt b)
  obtain ⟨Aσ, hAσ, hAσK, -⟩ := exists_hullVersion hC hκ hX hσ (hlt fun ω => max (a ω) (b ω))
  have hh0m := measurable_centredField hC.2.1 u₀
  have haσ := histGerm_le_of_le (u₀ := u₀) hC hX hσ₀ ha hσ (fun ω => le_max_left _ _) hζ hAa hAσ hAaK hAσK
  have hbσ := histGerm_le_of_le (u₀ := u₀) hC hX hσ₀ hb hσ (fun ω => le_max_right _ _) hζ hAb hAσ hAbK hAσK
  have hσN := histGerm_le_of_le (u₀ := u₀) hC hX hσ₀ hσ hN (fun ω => max_le (haN ω) (hbN ω)) hζ hAσ hAN
    hAσK hANK
  have hNle := histGerm_le (h := centredField h u₀) hN.measurableSpace_le hAN hh0m
  have hX2 := memLp_centredField hC hu₀ ψ
  have hX2' := memLp_centredField hC hu₀ ψ'
  have hCσ := ae_condExp_mul_germ_eq hC hκ hu₀ hX hσ (hlt _) hAσ hAσK ψ ψ'
  have hCN := ae_condExp_mul_germ_eq hC hκ hu₀ hX hN (hlt _) hAN hANK ψ ψ'
  -- the active means
  have ga := ae_condExp_germ_eq_of_active hC hu₀ hX ha (hlt a) hAa hAaK hκ ψ
  have gb := ae_condExp_germ_eq_of_active hC hu₀ hX hb (hlt b) hAb hAbK hκ ψ'
  have gσ := ae_condExp_germ_eq_of_active hC hu₀ hX hσ (hlt _) hAσ hAσK hκ ψ
  have gσ' := ae_condExp_germ_eq_of_active hC hu₀ hX hσ (hlt _) hAσ hAσK hκ ψ'
  have pa := ae_condExp_pairing_eq_actMean hC hX ha (hlt a) ψ
  have pb := ae_condExp_pairing_eq_actMean hC hX hb (hlt b) ψ'
  have pσ := ae_condExp_pairing_eq_actMean hC hX hσ (hlt _) ψ
  have pσ' := ae_condExp_pairing_eq_actMean hC hX hσ (hlt _) ψ'
  have hloc : ∀ᵐ ω ∂P,
      (P[fun ω' => centredField h u₀ ω' ψ | histGerm hσ.measurableSpace Aσ (centredField h u₀)]) ω =
        (P[fun ω' => centredField h u₀ ω' ψ | histGerm ha.measurableSpace Aa (centredField h u₀)]) ω ∨
      (P[fun ω' => centredField h u₀ ω' ψ' | histGerm hσ.measurableSpace Aσ (centredField h u₀)]) ω =
        (P[fun ω' => centredField h u₀ ω' ψ' | histGerm hb.measurableSpace Ab (centredField h u₀)]) ω := by
    filter_upwards [ga, gb, gσ, gσ', pa, pb, pσ, pσ', hψa, hψb] with ω e1 e2 e3 e4 e5 e6 e7 e8 da db
    rcases le_total (a ω) (b ω) with hle | hle
    · right
      have hm : max (a ω) (b ω) = b ω := max_eq_right hle
      have db' : Disjoint (tsupport ψ') (fwdHull (fun s : ℝ => W s.toNNReal ω) (max (a ω) (b ω) : ℝ≥0)) := by
        rw [hm]; exact db
      rw [e4 db', e2 db, e8 db', e6 db, hm]
    · left
      have hm : max (a ω) (b ω) = a ω := max_eq_left hle
      have da' : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (max (a ω) (b ω) : ℝ≥0)) := by
        rw [hm]; exact da
      rw [e3 da', e1 da, e7 da', e5 da, hm]
  obtain ⟨hCi, hC'i, key⟩ := integral_mul_sub_condExp_eq haσ hbσ hσN hNle hX2 hX2' hCσ hCN hloc
  refine ⟨hCi, hC'i, ?_⟩
  rw [← key]
  refine integral_congr_ae ?_
  filter_upwards [ga, gb, hψa, hψb] with ω e1 e2 da db
  rw [e1 da, e2 db]

open scoped Classical in
/-- **The variance identity for frozen piece means** (HGV5)–(HGV8): for pieces `ψₖ`, `k ∈ s`, frozen at driving stops
`τₖ ≤ N` at which they are active,
`E[(N_N(∑ ψₖ) − ∑ m_{τₖ}(ψₖ))²] = ∑_{k,j} (E[G_{D_{τₖ ∨ τⱼ}}(ψₖ, ψⱼ)] − E[G_{D_N}(ψₖ, ψⱼ)])`. -/
theorem integral_sq_germ_sub_sum_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {N : ℕ}
    (hN : IsStoppingTime (drivingFiltration P hX) fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0)) {AN : Ω → Set ℂ}
    (hAN : Measurable[mΩ, hittingSigma] AN)
    (hANK : ∀ᵐ ω ∂P, AN ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((N : ℝ≥0) : ℝ)) {ι : Type*}
    (s : Finset ι) (ψ : ι → TestOn upperHalfPlaneOpens) {τ : ι → Ω → ℝ≥0}
    (hτ : ∀ k, IsStoppingTime (drivingFiltration P hX) fun ω => (τ k ω : WithTop ℝ≥0)) (hτN : ∀ k ω, τ k ω ≤ N)
    (hact : ∀ k, ∀ᵐ ω ∂P, Disjoint (tsupport (ψ k)) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ k ω))) :
    ∫ ω, ((P[fun ω' => centredField h u₀ ω' (∑ k ∈ s, ψ k) |
        histGerm hN.measurableSpace AN (centredField h u₀)]) ω -
        ∑ k ∈ s, ((P[fun ω' => h ω' (ψ k) | (hτ k).measurableSpace]) ω - ∫ z, u₀ z * ψ k z)) ^ 2 ∂P =
      ∑ k ∈ s, ∑ j ∈ s, (∫ ω, covAt W (max (τ k ω) (τ j ω)) (ψ k) (ψ j) ω ∂P -
        ∫ ω, covAt W N (ψ k) (ψ j) ω ∂P) := by
  set d : ι → Ω → ℝ := fun k ω =>
    (P[fun ω' => centredField h u₀ ω' (ψ k) | histGerm hN.measurableSpace AN (centredField h u₀)]) ω -
      ((P[fun ω' => h ω' (ψ k) | (hτ k).measurableSpace]) ω - ∫ z, u₀ z * ψ k z) with hd
  have hh2 : ∀ k, MemLp (fun ω => h ω (ψ k)) 2 P := by
    intro k
    have e : (fun ω => h ω (ψ k)) = fun ω => centredField h u₀ ω (ψ k) + ∫ z, u₀ z * ψ k z := by
      funext ω; rw [centredField_apply h hu₀.1 ω (ψ k)]; ring
    rw [e]
    exact (memLp_centredField hC hu₀ (ψ k)).add (memLp_const _)
  have hd2 : ∀ k, MemLp (d k) 2 P := fun k =>
    ((memLp_centredField hC hu₀ (ψ k)).condExp one_le_two).sub
      (((hh2 k).condExp one_le_two).sub (memLp_const _))
  have hsum : ∀ᵐ ω ∂P,
      (P[fun ω' => centredField h u₀ ω' (∑ k ∈ s, ψ k) | histGerm hN.measurableSpace AN (centredField h u₀)]) ω =
        ∑ k ∈ s, (P[fun ω' => centredField h u₀ ω' (ψ k) |
          histGerm hN.measurableSpace AN (centredField h u₀)]) ω := by
    have e : (fun ω => centredField h u₀ ω (∑ k ∈ s, ψ k)) = ∑ k ∈ s, fun ω => centredField h u₀ ω (ψ k) := by
      funext ω; rw [map_sum, Finset.sum_apply]
    rw [e]
    filter_upwards [condExp_finsetSum (μ := P) (fun k _ => (memLp_centredField hC hu₀ (ψ k)).integrable one_le_two)
      (histGerm hN.measurableSpace AN (centredField h u₀))] with ω hω
    rw [hω, Finset.sum_apply]
  have hint : ∀ k j, Integrable (fun ω => d k ω * d j ω) P := fun k j => (hd2 k).integrable_mul (hd2 j)
  calc ∫ ω, ((P[fun ω' => centredField h u₀ ω' (∑ k ∈ s, ψ k) |
        histGerm hN.measurableSpace AN (centredField h u₀)]) ω -
        ∑ k ∈ s, ((P[fun ω' => h ω' (ψ k) | (hτ k).measurableSpace]) ω - ∫ z, u₀ z * ψ k z)) ^ 2 ∂P
      = ∫ ω, ∑ k ∈ s, ∑ j ∈ s, d k ω * d j ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hsum] with ω hω
        rw [hω, ← Finset.sum_sub_distrib, sq, Finset.sum_mul_sum]
    _ = ∑ k ∈ s, ∑ j ∈ s, ∫ ω, d k ω * d j ω ∂P := by
        rw [integral_finsetSum s fun k _ => integrable_finsetSum s fun j _ => hint k j]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum s fun j _ => hint k j]
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        exact (integral_mul_germ_sub_eq hC hκ hu₀ hX hζ hN hAN hANK (hτ k) (hτ j) (hτN k) (hτN j) (ψ k) (ψ j)
          (hact k) (hact j)).2.2

end Coupling


end Aux50Ge8

end InteractingSLE
