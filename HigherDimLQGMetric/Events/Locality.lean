import HigherDimLQGMetric.Events.TightLaw
import HigherDimLQGMetric.Field.StandardBorel
import HigherDimLQGMetric.Field.Version
import HigherDimLQGMetric.Sphere.Conv

/-!
# Shell measurability modulo constants

The normalized restriction of a whole-space LGF is measurable, up to null sets,
for the mean-zero pairings supported in a shell. This is the field step of D-LOC.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set TopologicalSpace Filter
open HigherDimLFPP (Rd)
open scoped Topology ENNReal

variable {d : ℕ} {Ω : Type}

/-- A generator of `fieldSigma0` is measurable for that sigma algebra. -/
theorem measurable_pairing_fieldSigma0 (h : Ω → DistRd d) (J : Set (Rd d))
    (φ : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ J}) :
    Measurable[fieldSigma0 h J] (fun ω => h ω φ.1.1) := by
  have hsrc : Measurable[fieldSigma0 h J]
      (fun ω (ψ : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ J}) => h ω ψ.1.1) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply φ).comp hsrc

/-- A test pairing recentered by a unit-mass sphere mollifier is a mean-zero
pairing supported in `J`. -/
private def localCenterTest0 (hd : 1 ≤ d) (V J : Opens (Rd d)) (hVJ : V ≤ J)
    (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (φ : TestOn V) (n : ℕ) :
    {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ J} := by
  let ψ : TestRd d := (∫ x, φ x) • sphBump (n + N) z r
  have hmass : ∫ x, (testIncl V φ) x = ∫ x, ψ x := by
    have h1 : ∫ x, (testIncl V φ) x = ∫ x, φ x := by
      simp only [testIncl_apply]
    rw [h1]
    change (∫ x, φ x) = ∫ x, (∫ y, φ y) * sphBump (n + N) z r x
    rw [integral_const_mul, integral_sphBump hd]
    ring
  refine ⟨testSub0 (testIncl V φ) ψ hmass, ?_⟩
  change tsupport (⇑(testIncl V φ - ψ)) ⊆ J
  refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
  · rw [coe_testIncl]
    exact φ.tsupport_subset.trans hVJ
  · change tsupport (fun x => (∫ y, φ y) • sphBump (n + N) z r x) ⊆ J
    exact (tsupport_smul_subset_right (fun _ => ∫ y, φ y)
      (fun x => sphBump (n + N) z r x)).trans (hN n)

private theorem localCenterTest0_apply (hd : 1 ≤ d) (V J : Opens (Rd d))
    (hVJ : V ≤ J) (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (φ : TestOn V) (n : ℕ) (g : DistRd d) :
    g ((localCenterTest0 hd V J hVJ z r N hN φ n).1.1) =
      restrictTo V g φ - (∫ x, φ x) * sphereAvgSeq g r z (n + N) := by
  simp only [localCenterTest0, testSub0_val, map_sub, map_smul,
    restrictTo_apply, sphereAvgSeq_eq_apply_sphBump, smul_eq_mul]

/-- Countable coordinates of the restriction recentered at the sphere average,
constructed using only mean-zero shell pairings. -/
private def localRecPair (hd : 1 ≤ d) (V J : Opens (Rd d)) (hVJ : V ≤ J)
    (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (h : Ω → DistRd d) (ω : Ω) : CoordJ → ℝ :=
  fun c => limUnder atTop (fun n =>
    h ω ((localCenterTest0 hd V J hVJ z r N hN (comb V c) n).1.1))

private theorem measurable_localRecPair (hd : 1 ≤ d) (V J : Opens (Rd d))
    (hVJ : V ≤ J) (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (h : Ω → DistRd d) :
    Measurable[fieldSigma0 h J] (localRecPair hd V J hVJ z r N hN h) := by
  refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun c => ?_
  have hm : ∀ n : ℕ, StronglyMeasurable[fieldSigma0 h J]
      (fun ω => h ω ((localCenterTest0 hd V J hVJ z r N hN (comb V c) n).1.1)) :=
    fun n => (measurable_pairing_fieldSigma0 h J
      (localCenterTest0 hd V J hVJ z r N hN (comb V c) n)).stronglyMeasurable
  exact (@StronglyMeasurable.limUnder ℕ Ω ℝ (fieldSigma0 h J) _ _ atTop _
    (fun n ω => h ω ((localCenterTest0 hd V J hVJ z r N hN (comb V c) n).1.1))
    _ _ hm).measurable

/-- A measurable distribution-valued version of the recentered restriction. -/
private def localRecVersion (hd : 1 ≤ d) (V J : Opens (Rd d)) (hVJ : V ≤ J)
    (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (h : Ω → DistRd d) (ω : Ω) : DistOn V :=
  pairJInv V (localRecPair hd V J hVJ z r N hN h ω)

private theorem measurable_localRecVersion (hd : 1 ≤ d) (V J : Opens (Rd d))
    (hVJ : V ≤ J) (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (h : Ω → DistRd d) :
    Measurable[fieldSigma0 h J] (localRecVersion hd V J hVJ z r N hN h) :=
  (measurable_pairJInv V).comp (measurable_localRecPair hd V J hVJ z r N hN h)

/-- The recentered restriction has a version measurable for the mean-zero
pairings in `J`. This is the field sigma-algebra step of D-LOC. -/
theorem exists_measurable_recentered_restrict [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V J : Opens (Rd d)) (hVJ : V ≤ J) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hSJ : Metric.sphere z r ⊆ J) :
    ∃ F : Ω → DistOn V, Measurable[fieldSigma0 h J] F ∧
      ∀ᵐ ω ∂P, F ω = restrictTo V (addConst (h ω) (-sphereAvg (h ω) r z)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨N, hN₀⟩ := exists_tsupport_sphBump_subset
    (U := J) (r := r) (z := z) (by simpa only [abs_of_pos hr] using hSJ)
  have hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J :=
    fun n => hN₀ (n + N) (Nat.le_add_left N n)
  refine ⟨localRecVersion hd1 V J hVJ z r N hN h,
    measurable_localRecVersion hd1 V J hVJ z r N hN h, ?_⟩
  filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd hr z] with ω hc
  have ha := tendsto_sphereAvgSeq_sphereAvg hc
  have hashift : Tendsto (fun n => sphereAvgSeq (h ω) r z (n + N)) atTop
      (𝓝 (sphereAvg (h ω) r z)) := ha.comp (tendsto_add_atTop_nat N)
  have hcoord : localRecPair hd1 V J hVJ z r N hN h ω =
      pairJ V (restrictTo V (addConst (h ω) (-sphereAvg (h ω) r z))) := by
    funext c
    let φ : TestOn V := comb V c
    have heval : (restrictTo V (addConst (h ω) (-sphereAvg (h ω) r z))) φ =
        restrictTo V (h ω) φ - (∫ x, φ x) * sphereAvg (h ω) r z := by
      rw [restrictTo_apply, addConst_apply, restrictTo_apply]
      simp only [testIncl_apply]
      ring
    have hseq : (fun n => h ω ((localCenterTest0 hd1 V J hVJ z r N hN φ n).1.1)) =
        fun n => restrictTo V (h ω) φ - (∫ x, φ x) * sphereAvgSeq (h ω) r z (n + N) :=
      funext fun n => localCenterTest0_apply hd1 V J hVJ z r N hN φ n (h ω)
    have hlim : Tendsto (fun n => h ω
        ((localCenterTest0 hd1 V J hVJ z r N hN φ n).1.1)) atTop
        (𝓝 (restrictTo V (h ω) φ - (∫ x, φ x) * sphereAvg (h ω) r z)) := by
      rw [hseq]
      exact tendsto_const_nhds.sub (tendsto_const_nhds.mul hashift)
    show limUnder atTop (fun n => h ω
        ((localCenterTest0 hd1 V J hVJ z r N hN (comb V c) n).1.1)) = _
    rw [hlim.limUnder_eq, ← heval]
    rfl
  change pairJInv V (localRecPair hd1 V J hVJ z r N hN h ω) = _
  rw [hcoord, pairJInv_pairJ]

/-- Axiom II composed with the shell-measurable recentered restriction. -/
theorem IsWeakExpMetric.exists_measurable_internal_recentered
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V J : Opens (Rd d)) (hVJ : V ≤ J) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hSJ : Metric.sphere z r ⊆ J) :
    ∃ F : Ω → Rd d → Rd d → ℝ≥0∞,
      Measurable[fieldSigma0 h J] F ∧
      ∀ᵐ ω ∂P, ∀ u ∈ V, ∀ v ∈ V,
        F ω u v = (D (addConst (h ω) (-sphereAvg (h ω) r z))).internal V u v := by
  let k : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) r z)
  have hk : IsWholeSpaceLGF k P :=
    hh.addConst (((measurable_sphereAvg_left r z).comp hh.measurable).neg)
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P k hk.isLGFPlusCont V
  obtain ⟨G, hG, hGae⟩ := exists_measurable_recentered_restrict hd hh V J hVJ z hr hSJ
  refine ⟨fun ω => Φ (G ω), hΦ.comp hG, ?_⟩
  filter_upwards [hΦae, hGae] with ω hloc hrec
  intro u hu v hv
  rw [hrec]
  exact (hloc u hu v hv).symm

/-- D-LOC in its normalized metric form, before the deterministic factor
`r^(-ξQ)` is applied. -/
theorem IsWeakExpMetric.exists_measurable_expNormalized_internal
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V J : Opens (Rd d)) (hVJ : V ≤ J) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hSJ : Metric.sphere z r ⊆ J) :
    ∃ F : Ω → Rd d → Rd d → ℝ≥0∞,
      Measurable[fieldSigma0 h J] F ∧
      ∀ᵐ ω ∂P, ∀ u ∈ V, ∀ v ∈ V,
        F ω u v = ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z)) *
          (D (h ω)).internal V u v := by
  obtain ⟨F, hFm, hFae⟩ :=
    hD.exists_measurable_internal_recentered hd hh V J hVJ z hr hSJ
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hFae, hD.ae_internal_mem_Icc hh.isLGFPlusCont] with ω hF hW
  intro u hu v hv
  rw [hF u hu v hv]
  let f : C(Rd d, ℝ) := ContinuousMap.const (Rd d) (-sphereAvg (h ω) r z)
  have he : (D (addConst (h ω) (-sphereAvg (h ω) r z))).internal V u v =
      ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z)) *
        (D (h ω)).internal V u v := by
    have hI := hW f V (ξ * -sphereAvg (h ω) r z)
      (ξ * -sphereAvg (h ω) r z) V.isOpen
      (fun x hx => by simp only [f, ContinuousMap.const_apply]; exact le_rfl)
      (fun x hx => by simp only [f, ContinuousMap.const_apply]; exact le_rfl) u v
    have hEq := le_antisymm hI.2 hI.1
    simpa only [f, addFun_const, mul_neg, neg_mul] using hEq
  exact he

/-- The reciprocal sharp normalizer splits into a deterministic scale factor
and the recentering factor. -/
theorem ofReal_sNorm_inv (ξ Q : ℝ) (g : DistRd d) (r : ℝ) (z : Rd d) :
    ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) =
      ENNReal.ofReal ((r ^ (ξ * Q))⁻¹) *
        ENNReal.ofReal (Real.exp (-ξ * sphereAvg g r z)) := by
  rw [sNorm, mul_inv_rev]
  have he : (Real.exp (ξ * sphereAvg g r z))⁻¹ =
      Real.exp (-ξ * sphereAvg g r z) := by
    rw [← Real.exp_neg]
    congr 1
    ring_nf
  rw [he, ENNReal.ofReal_mul (by positivity)]
  exact mul_comm _ _

/-- D-LOC: the sharp-normalized internal metric on `V` is a.s. a measurable
function of the mean-zero field pairings supported in `J`. -/
theorem IsSharpWeakExpMetric.exists_measurable_normInternal
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V J : Opens (Rd d)) (hVJ : V ≤ J) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hSJ : Metric.sphere z r ⊆ J) :
    ∃ F : Ω → Rd d → Rd d → ℝ≥0∞,
      Measurable[fieldSigma0 h J] F ∧
      ∀ᵐ ω ∂P, ∀ u ∈ V, ∀ v ∈ V,
        F ω u v = ENNReal.ofReal ((sNorm ξ Q (h ω) r z)⁻¹) *
          (D (h ω)).internal V u v := by
  obtain ⟨G, hGm, hGae⟩ :=
    (show IsWeakExpMetric d ξ D (fun t => t ^ (ξ * Q)) from hD).exists_measurable_expNormalized_internal
      hd hh V J hVJ z hr hSJ
  let F : Ω → Rd d → Rd d → ℝ≥0∞ :=
    fun ω u v => ENNReal.ofReal ((r ^ (ξ * Q))⁻¹) * G ω u v
  have hFm : Measurable[fieldSigma0 h J] F := by
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun u => ?_
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun v => ?_
    exact measurable_const.mul
      ((measurable_pi_apply v).comp ((measurable_pi_apply u).comp hGm))
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hGae] with ω hω
  intro u hu v hv
  dsimp only [F]
  rw [hω u hu v hv, ofReal_sNorm_inv]
  exact (mul_assoc _ _ _).symm

/-- Every Borel event of the sharp-normalized internal metric on `V × V`
is a shell event modulo null sets. -/
theorem IsSharpWeakExpMetric.aeEventIn_normInternal
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V J : Opens (Rd d)) (hVJ : V ≤ J) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hSJ : Metric.sphere z r ⊆ J)
    (E : Set (V × V → ℝ≥0∞)) (hE : MeasurableSet E) :
    AEEventIn P (fieldSigma0 h J)
      {ω | (fun p : V × V =>
        ENNReal.ofReal ((sNorm ξ Q (h ω) r z)⁻¹) *
          (D (h ω)).internal V p.1.1 p.2.1) ∈ E} := by
  obtain ⟨F, hFm, hFae⟩ := hD.exists_measurable_normInternal hd hh V J hVJ z hr hSJ
  let G : Ω → (V × V → ℝ≥0∞) := fun ω p => F ω p.1.1 p.2.1
  have hGm : Measurable[fieldSigma0 h J] G := by
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun p => ?_
    exact (measurable_pi_apply p.2.1).comp
      ((measurable_pi_apply p.1.1).comp hFm)
  refine ⟨G ⁻¹' E, hGm hE, ?_⟩
  filter_upwards [hFae] with ω hω
  have heq : G ω = fun p : V × V =>
      ENNReal.ofReal ((sNorm ξ Q (h ω) r z)⁻¹) *
        (D (h ω)).internal V p.1.1 p.2.1 := by
    funext p
    exact hω p.1.1 p.1.2 p.2.1 p.2.2
  exact propext (by simp only [mem_preimage, heq])

/-- Extend the shell-measurable version of an internal metric by infinity off
the domain. This makes it usable as an ambient two-point function. -/
theorem IsSharpWeakExpMetric.exists_measurable_normInternal_all
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V J : Opens (Rd d)) (hVJ : V ≤ J) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hSJ : Metric.sphere z r ⊆ J) :
    ∃ F : Ω → Rd d → Rd d → ℝ≥0∞,
      Measurable[fieldSigma0 h J] F ∧
      ∀ᵐ ω ∂P, ∀ u v,
        F ω u v = ENNReal.ofReal ((sNorm ξ Q (h ω) r z)⁻¹) *
          (D (h ω)).internal V u v := by
  classical
  obtain ⟨F, hFm, hFae⟩ :=
    hD.exists_measurable_normInternal hd hh V J hVJ z hr hSJ
  let G : Ω → Rd d → Rd d → ℝ≥0∞ :=
    fun ω u v => if u ∈ V ∧ v ∈ V then F ω u v else ⊤
  have hGm : Measurable[fieldSigma0 h J] G := by
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun u => ?_
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun v => ?_
    by_cases huv : u ∈ V ∧ v ∈ V
    · simpa [G, huv, Function.comp_def] using
        (measurable_pi_apply v).comp ((measurable_pi_apply u).comp hFm)
    · simp [G, huv]
  refine ⟨G, hGm, ?_⟩
  filter_upwards [hFae] with ω hω
  intro u v
  have hsNorm : 0 < sNorm ξ Q (h ω) r z := by
    unfold sNorm
    positivity
  have hfactor : ENNReal.ofReal ((sNorm ξ Q (h ω) r z)⁻¹) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hsNorm))
  by_cases huv : u ∈ V ∧ v ∈ V
  · simpa [G, huv] using hω u huv.1 v huv.2
  · rcases not_and_or.mp huv with hu | hv
    · rw [(D (h ω)).internal_eq_top_of_notMem_left hu]
      simp [G, huv, ENNReal.mul_top hfactor]
    · rw [(D (h ω)).internal_eq_top_of_notMem_right hv]
      simp [G, huv, ENNReal.mul_top hfactor]

end HigherDimLQGMetric
