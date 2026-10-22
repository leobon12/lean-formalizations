import HigherDimLQGMetric.CM.Holder
import HigherDimLQGMetric.Sphere.PotCov
import QuantumZipper.Proofs.LQG.PalmNorm

/-! Gaussian tilting by a difference of sphere averages. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The logarithmic potential of the signed sphere measure `σ_{r,z} - σ_{ρ,w}`. -/
def sf4Potential (hd : 2 ≤ d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (z w : Rd d) : C(Rd d, ℝ) :=
  ⟨fun x => logPotM (sphMeas r z) x - logPotM (sphMeas ρ w) x,
    (continuous_logPotM_sphMeas hd hr z).sub (continuous_logPotM_sphMeas hd hρ w)⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistRd d}

/-- SF4's Gaussian tilt on the mean-zero pairings. It is the joint law of the sphere-average
difference and all mean-zero pairings, with the covariance shift written as a log potential. -/
theorem sf4_tilt_pair0 (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) (a : ℝ)
    (Φ : (TestRd0 d → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ ω, Φ (fun φ => pair0Rd (h ω) φ +
      a * ∫ x, (sf4Potential hd hr hρ z w) x * φ.1 x) ∂P) =
      ∫⁻ ω, Φ (pair0Rd (h ω)) *
        ENNReal.ofReal (Real.exp (a * (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) -
          a ^ 2 * Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] / 2)) ∂P := by
  by_cases ha : a = 0
  · subst a
    simp
  let q : SphPair d := ⟨((r, z), (ρ, w)), hr, hρ⟩
  let V : Ω → ℝ := fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w
  have hVm : Measurable V := ((measurable_sphereAvg_left r z).comp hh.measurable).sub
    ((measurable_sphereAvg_left ρ w).comp hh.measurable)
  let Z : Sum Unit (TestRd0 d) → Ω → ℝ :=
    Sum.elim (fun _ : Unit => V) (fun φ : TestRd0 d => fun ω => h ω φ.1)
  have hZg : IsGaussianProcess Z P := by
    have H := (hh.isGaussianProcess_sphereAvg_sub hd).comp_right
      (Sum.map (fun _ : Unit => q) id)
    refine H.congr fun j => ?_
    cases j with
    | inl u => exact ae_of_all _ fun ω => rfl
    | inr φ => exact ae_of_all _ fun ω => rfl
  have hZm : ∀ j, Measurable (Z j) := by
    intro j
    cases j with
    | inl u =>
        exact ((measurable_sphereAvg_left r z).comp hh.measurable).sub
          ((measurable_sphereAvg_left ρ w).comp hh.measurable)
    | inr φ => exact (measurable_distOn_apply φ.1).comp hh.measurable
  have hZ0 : ∀ j, ∫ ω, Z j ω ∂P = 0 := by
    intro j
    cases j with
    | inl u => exact (hh.hasGaussianLaw_sphereAvg_sub hd hr hρ z w).2
    | inr φ => exact hh.centered φ
  let σ : Sum Unit (TestRd0 d) →₀ ℝ := Finsupp.single (Sum.inl ()) a
  let Ψ : (Sum Unit (TestRd0 d) → ℝ) → ℝ≥0∞ :=
    fun a => Φ (fun φ => a (Sum.inr φ))
  have hΨ : Measurable Ψ := hΦ.comp (measurable_pi_iff.mpr fun φ => measurable_pi_apply _)
  have ht := QuantumZipper.PalmNorm.lintegral_mul_tiltDensity hZg hZm hZ0 σ Ψ hΨ
  have hCov (φ : TestRd0 d) :
      QuantumZipper.CameronMartin.covShift Z P σ (Sum.inr φ) =
        a * ∫ x, (sf4Potential hd hr hρ z w) x * φ.1 x := by
    simp only [QuantumZipper.CameronMartin.covShift, QuantumZipper.CameronMartin.covK,
      σ, Finsupp.support_single _ ha, Finset.sum_singleton, Finsupp.single_eq_same]
    change a * cov[fun ω => h ω φ.1, V; P] = _
    rw [ProbabilityTheory.covariance_comm]
    rw [hh.covariance_sphereAvg_sub_apply_eq_integral hd hr hρ z w φ]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp [sf4Potential, mul_comm]
  have hVar : QuantumZipper.CameronMartin.covNorm Z P σ = a ^ 2 * Var[V; P] := by
    simp only [QuantumZipper.CameronMartin.covNorm, QuantumZipper.CameronMartin.covShift,
      QuantumZipper.CameronMartin.covK, σ, Finsupp.support_single _ ha,
      Finset.sum_singleton, Finsupp.single_eq_same]
    change a * (a * cov[V, V; P]) = a ^ 2 * Var[V; P]
    rw [ProbabilityTheory.covariance_self hVm.aemeasurable]
    ring_nf
  have hD (ω : Ω) : QuantumZipper.CameronMartin.tiltDensity Z P σ ω =
      Real.exp (a * V ω - a ^ 2 * Var[V; P] / 2) := by
    rw [QuantumZipper.CameronMartin.tiltDensity]
    change Real.exp (QuantumZipper.CameronMartin.comb Z σ ω -
      QuantumZipper.CameronMartin.covNorm Z P σ / 2) = _
    rw [hVar]
    simp only [QuantumZipper.CameronMartin.comb, σ, Finsupp.support_single _ ha,
      Finset.sum_singleton, Finsupp.single_eq_same]
    rfl
  calc
    (∫⁻ ω, Φ (fun φ => pair0Rd (h ω) φ +
      a * ∫ x, (sf4Potential hd hr hρ z w) x * φ.1 x) ∂P) =
        ∫⁻ ω, Ψ (fun j => Z j ω + QuantumZipper.CameronMartin.covShift Z P σ j) ∂P := by
          apply lintegral_congr
          intro ω
          congr 1
          funext φ
          simp only [Z, Sum.elim_inr]
          rw [hCov]
          rfl
    _ = ∫⁻ ω, Ψ (fun j => Z j ω) *
          ENNReal.ofReal (QuantumZipper.CameronMartin.tiltDensity Z P σ ω) ∂P := ht.symm
    _ = _ := by
          apply lintegral_congr
          intro ω
          rw [hD]
          rfl

private def sf4ConvSet (r : ℝ) (z : Rd d) : Set (DistRd d) :=
  {g | ∃ b, Tendsto (sphereAvgSeq g r z) atTop (𝓝 b)}

/-- Return a distribution to the representative whose average over `∂B_r(z)` is zero. -/
def sf4Recenter (r : ℝ) (z : Rd d) (g : DistRd d) (G : C(Rd d, ℝ)) : DistRd d :=
  addConst (addFun g G)
    (-(sphereAvg g r z + ∫ u, G (z + r • u) ∂(unitSphereProb d)))

/-- The deterministic potential shift after recentering at `∂B_r(z)`. -/
def sf4CenteredPotential (hd : 2 ≤ d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (z w : Rd d) : C(Rd d, ℝ) :=
  sf4Potential hd hr hρ z w - ContinuousMap.const _
    (∫ u, (sf4Potential hd hr hρ z w) (z + r • u) ∂(unitSphereProb d))

/-- The recentered field is exactly `H + a k`, with `H = h - h_r(z)` and the centered potential
`k = F - ⨍_{∂B_r(z)} F`. -/
theorem sf4Recenter_eq_addFun_centered (hd : 2 ≤ d) {r ρ : ℝ} (hr : 0 < r)
    (hρ : 0 < ρ) (z w : Rd d) (g : DistRd d) (a : ℝ) :
    sf4Recenter r z g (a • sf4Potential hd hr hρ z w) =
      addFun (addConst g (-sphereAvg g r z))
        (a • sf4CenteredPotential hd hr hρ z w) := by
  let F := sf4Potential hd hr hρ z w
  let c := ∫ u, F (z + r • u) ∂(unitSphereProb d)
  have hc : (∫ u, (a • F) (z + r • u) ∂(unitSphereProb d)) = a * c := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul, c]
  have hk : a • sf4CenteredPotential hd hr hρ z w =
      a • F - ContinuousMap.const _ (a * c) := by
    ext x
    simp only [sf4CenteredPotential, F, c, ContinuousMap.smul_apply,
      ContinuousMap.sub_apply, ContinuousMap.const_apply, smul_eq_mul]
    ring
  rw [hk]
  change addConst (addFun g (a • F))
      (-(sphereAvg g r z + ∫ u, (a • F) (z + r • u) ∂(unitSphereProb d))) =
    addFun (addConst g (-sphereAvg g r z))
      (a • F - ContinuousMap.const _ (a * c))
  rw [hc]
  change addFun (addFun g (a • F))
      (ContinuousMap.const _ (-(sphereAvg g r z + a * c))) =
    addFun (addFun g (ContinuousMap.const _ (-sphereAvg g r z)))
      (a • F - ContinuousMap.const _ (a * c))
  rw [addFun_addFun, addFun_addFun]
  congr 1
  ext x
  simp only [ContinuousMap.add_apply, ContinuousMap.neg_apply,
    ContinuousMap.const_apply, sub_eq_add_neg]
  ring_nf

private theorem sf4Recenter_conv (hd : 1 ≤ d) {r : ℝ} {z : Rd d} {g : DistRd d}
    (hg : g ∈ sf4ConvSet r z) (G : C(Rd d, ℝ)) :
    sf4Recenter r z g G ∈ sf4ConvSet r z := by
  obtain ⟨b, hb⟩ := hg
  have hG := (tendsto_sphereAvgSeq_addFun_iff g G r z b).2 hb
  let c := ∫ u, G (z + r • u) ∂(unitSphereProb d)
  have hC := hG.add_const (-(sphereAvg g r z + c))
  refine ⟨b + c - (sphereAvg g r z + c), ?_⟩
  have he : sphereAvgSeq (sf4Recenter r z g G) r z =
      fun n => sphereAvgSeq (addFun g G) r z n - (sphereAvg g r z + c) := by
    funext n
    simp only [sf4Recenter, sphereAvgSeq_addConst hd, sub_eq_add_neg, c]
  rw [he]
  simpa only [sub_eq_add_neg] using hC

private theorem sf4Recenter_zero (hd : 1 ≤ d) {r : ℝ} {z : Rd d} {g : DistRd d}
    (hg : g ∈ sf4ConvSet r z) (G : C(Rd d, ℝ)) :
    sphereAvg (sf4Recenter r z g G) r z = 0 := by
  have hlim := tendsto_sphereAvgSeq_sphereAvg hg
  have hG := (tendsto_sphereAvgSeq_addFun_iff g G r z (sphereAvg g r z)).2 hlim
  rw [sf4Recenter, sphereAvg_addConst_of_tendsto hd hG,
    sphereAvg_addFun_of_tendsto hlim]
  ring

private def sf4Retract (r : ℝ) (z : Rd d) (g : DistRd d) : DistRd d :=
  addConst (recenter (bumpTest 0 (0 : Rd d)) g)
    (-sphereAvg (recenter (bumpTest 0 (0 : Rd d)) g) r z)

private theorem measurable_sf4Retract_sigma0 (r : ℝ) (z : Rd d) :
    Measurable[sigma0 d] (sf4Retract r z) := by
  have hK : Measurable (fun g : DistRd d => addConst g (-sphereAvg g r z)) :=
    Measurable.addConst measurable_id (measurable_sphereAvg_left r z).neg
  exact hK.comp (measurable_recenter_sigma0 integral_bumpTest_zero)

private theorem sf4Retract_eq_self (hd : 1 ≤ d) {r : ℝ} {z : Rd d} {g : DistRd d}
    (hg : g ∈ sf4ConvSet r z) (hn : sphereAvg g r z = 0) : sf4Retract r z g = g := by
  unfold sf4Retract recenter
  rw [sphereAvg_addConst_of_tendsto hd (tendsto_sphereAvgSeq_sphereAvg hg),
    addConst_addConst, hn]
  simp only [zero_add, neg_neg, neg_add_cancel, addConst_zero]

private theorem exists_sf4_pair0_event (hd : 1 ≤ d) (r : ℝ) (z : Rd d)
    (A : Set (DistRd d)) (hA : MeasurableSet A) :
    ∃ A0 : Set (TestRd0 d → ℝ), MeasurableSet A0 ∧
      ∀ g : DistRd d, g ∈ sf4ConvSet r z → sphereAvg g r z = 0 →
        (g ∈ A ↔ pair0Rd g ∈ A0) := by
  have hS : MeasurableSet[sigma0 d] ((sf4Retract r z) ⁻¹' A) :=
    hA.preimage (measurable_sf4Retract_sigma0 r z)
  obtain ⟨A0, hA0, he⟩ := hS
  refine ⟨A0, hA0, fun g hg hn => ?_⟩
  have hmem : g ∈ (sf4Retract r z) ⁻¹' A ↔ pair0Rd g ∈ A0 := by
    change g ∈ sf4Retract r z ⁻¹' A ↔ g ∈ ev0 ⁻¹' A0
    rw [he]
  simpa only [Set.mem_preimage, sf4Retract_eq_self hd hg hn] using hmem

private theorem sf4Recenter_pair0 (g : DistRd d) (G : C(Rd d, ℝ))
    (r : ℝ) (z : Rd d) : pair0Rd (sf4Recenter r z g G) = pair0Rd (addFun g G) := by
  funext φ
  exact addConst_apply_testRd0 (addFun g G) _ φ

/-- SF4 tilt for the recentered distribution `H = h - h_r(z)` and the potential shift.
The left field is `H + a(F - sphereAvg F)`; the right density uses
`X = h_r(z) - h_ρ(w)`. -/
theorem sf4_tilt (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) (a : ℝ)
    (A : Set (DistRd d)) (hA : MeasurableSet A) :
    P {ω | sf4Recenter r z (h ω) (a • sf4Potential hd hr hρ z w) ∈ A} =
      ∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞))
        (sf4Recenter r z (h ω) 0) *
        ENNReal.ofReal (Real.exp (a * (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) -
          a ^ 2 * Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] / 2)) ∂P := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨A0, hA0, hrepr⟩ := exists_sf4_pair0_event hd1 r z A hA
  have hconv : ∀ᵐ ω ∂P, h ω ∈ sf4ConvSet r z :=
    hh.ae_exists_tendsto_sphereAvgSeq hd hr z
  let F := sf4Potential hd hr hρ z w
  have hPairShift (ω : Ω) :
      pair0Rd (sf4Recenter r z (h ω) (a • F)) =
        fun φ => pair0Rd (h ω) φ + a * ∫ x, F x * φ.1 x := by
    rw [sf4Recenter_pair0]
    funext φ
    rw [cmPair0_addFun]
    congr 1
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  have hPairBase (ω : Ω) : pair0Rd (sf4Recenter r z (h ω) 0) = pair0Rd (h ω) := by
    rw [sf4Recenter_pair0]
    simp
  have hleft : P {ω | sf4Recenter r z (h ω) (a • F) ∈ A} =
      P {ω | (fun φ => pair0Rd (h ω) φ + a * ∫ x, F x * φ.1 x) ∈ A0} := by
    apply measure_congr
    filter_upwards [hconv] with ω hc
    exact propext ((hrepr _ (sf4Recenter_conv hd1 hc _) (sf4Recenter_zero hd1 hc _)).trans
      (by rw [hPairShift]))
  have hright : (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞))
      (sf4Recenter r z (h ω) 0) *
      ENNReal.ofReal (Real.exp (a * (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) -
        a ^ 2 * Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] / 2)) ∂P) =
      ∫⁻ ω, A0.indicator (fun _ => (1 : ℝ≥0∞)) (pair0Rd (h ω)) *
      ENNReal.ofReal (Real.exp (a * (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) -
        a ^ 2 * Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] / 2)) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hconv] with ω hc
    have he := hrepr _ (sf4Recenter_conv hd1 hc (0 : C(Rd d, ℝ)))
      (sf4Recenter_zero hd1 hc (0 : C(Rd d, ℝ)))
    rw [hPairBase] at he
    classical
    by_cases hω : pair0Rd (h ω) ∈ A0 <;> simp [he, hω]
  rw [hleft, hright]
  have hΦ : Measurable (A0.indicator fun _ => (1 : ℝ≥0∞)) :=
    measurable_const.indicator hA0
  have htilt := sf4_tilt_pair0 hd hh hr hρ z w a _ hΦ
  have hE : MeasurableSet {ω | (fun φ => pair0Rd (h ω) φ +
      a * ∫ x, F x * φ.1 x) ∈ A0} := by
    apply hA0.preimage
    exact measurable_pi_iff.mpr fun φ =>
      ((measurable_distOn_apply φ.1).comp hh.measurable).add_const _
  rw [← lintegral_indicator_one hE]
  convert htilt using 1; rfl

/-- The SF4 tilt as an equality of laws of recentered distributions. -/
theorem sf4_tilt_measure (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) (a : ℝ) :
    P.map (fun ω => sf4Recenter r z (h ω) (a • sf4Potential hd hr hρ z w)) =
      (P.withDensity fun ω =>
        ENNReal.ofReal (Real.exp (a * (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) -
          a ^ 2 * Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] / 2))).map
        (fun ω => sf4Recenter r z (h ω) 0) := by
  let H : Ω → DistRd d := fun ω => sf4Recenter r z (h ω) 0
  let J : Ω → DistRd d := fun ω =>
    sf4Recenter r z (h ω) (a • sf4Potential hd hr hρ z w)
  let D : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (a * (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) -
      a ^ 2 * Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] / 2))
  have hmR (G : C(Rd d, ℝ)) : Measurable (fun g : DistRd d => sf4Recenter r z g G) := by
    have hC : Measurable (fun g : DistRd d =>
        -(sphereAvg g r z + ∫ u, G (z + r • u) ∂(unitSphereProb d))) :=
      ((measurable_sphereAvg_left r z).add_const _).neg
    exact Measurable.addConst (measurable_addFun_left G) hC
  have hmH : Measurable H := (hmR 0).comp hh.measurable
  have hmJ : Measurable J := (hmR _).comp hh.measurable
  ext A hA
  calc
    P.map J A = P {ω | J ω ∈ A} := Measure.map_apply hmJ hA
    _ = ∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) (H ω) * D ω ∂P :=
      sf4_tilt hd hh hr hρ z w a A hA
    _ = (P.withDensity D).map H A := by
      rw [Measure.map_apply hmH hA, withDensity_apply _ (hA.preimage hmH),
        ← lintegral_indicator (hA.preimage hmH)]
      apply lintegral_congr
      intro ω
      classical
      by_cases hω : H ω ∈ A <;> simp [hω]

end HigherDimLQGMetric
