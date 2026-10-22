import HigherDimLQGMetric.Events.Locality
import HigherDimLQGMetric.Sphere.Cont

/-!
# Shell recentering for an LGF plus a continuous field

The §6 fine field is an LGF plus a possibly dependent continuous function. The
existing shell recentering theorem covers an LGF; the same deterministic code
works once the sphere average converges, which holds for this larger class.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set TopologicalSpace Filter
open HigherDimLFPP (Rd)
open scoped Topology ENNReal

variable {d : ℕ} {Ω : Type}

private def amplify_localCenterTest0 (hd : 1 ≤ d) (V J : Opens (Rd d)) (hVJ : V ≤ J)
    (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (φ : TestOn V) (n : ℕ) :
    {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ J} := by
  let ψ : TestRd d := (∫ x, φ x) • sphBump (n + N) z r
  have hmass : ∫ x, (testIncl V φ) x = ∫ x, ψ x := by
    have h1 : ∫ x, (testIncl V φ) x = ∫ x, φ x := by simp only [testIncl_apply]
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

private theorem amplify_localCenterTest0_apply (hd : 1 ≤ d) (V J : Opens (Rd d))
    (hVJ : V ≤ J) (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (φ : TestOn V) (n : ℕ) (g : DistRd d) :
    g ((amplify_localCenterTest0 hd V J hVJ z r N hN φ n).1.1) =
      restrictTo V g φ - (∫ x, φ x) * sphereAvgSeq g r z (n + N) := by
  simp only [amplify_localCenterTest0, testSub0_val, map_sub, map_smul,
    restrictTo_apply, sphereAvgSeq_eq_apply_sphBump, smul_eq_mul]

private def amplify_localRecPair (hd : 1 ≤ d) (V J : Opens (Rd d)) (hVJ : V ≤ J)
    (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (h : Ω → DistRd d) (ω : Ω) : CoordJ → ℝ :=
  fun c => limUnder atTop (fun n =>
    h ω ((amplify_localCenterTest0 hd V J hVJ z r N hN (comb V c) n).1.1))

private theorem amplify_measurable_localRecPair (hd : 1 ≤ d) (V J : Opens (Rd d))
    (hVJ : V ≤ J) (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (h : Ω → DistRd d) :
    Measurable[fieldSigma0 h J] (amplify_localRecPair hd V J hVJ z r N hN h) := by
  refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun c => ?_
  have hm : ∀ n : ℕ, StronglyMeasurable[fieldSigma0 h J]
      (fun ω => h ω ((amplify_localCenterTest0 hd V J hVJ z r N hN (comb V c) n).1.1)) :=
    fun n => (measurable_pairing_fieldSigma0 h J
      (amplify_localCenterTest0 hd V J hVJ z r N hN (comb V c) n)).stronglyMeasurable
  exact (@StronglyMeasurable.limUnder ℕ Ω ℝ (fieldSigma0 h J) _ _ atTop _
    (fun n ω => h ω ((amplify_localCenterTest0 hd V J hVJ z r N hN (comb V c) n).1.1))
    _ _ hm).measurable

private def amplify_localRecVersion (hd : 1 ≤ d) (V J : Opens (Rd d)) (hVJ : V ≤ J)
    (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (h : Ω → DistRd d) (ω : Ω) : DistOn V :=
  pairJInv V (amplify_localRecPair hd V J hVJ z r N hN h ω)

private theorem amplify_measurable_localRecVersion (hd : 1 ≤ d) (V J : Opens (Rd d))
    (hVJ : V ≤ J) (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J)
    (h : Ω → DistRd d) :
    Measurable[fieldSigma0 h J] (amplify_localRecVersion hd V J hVJ z r N hN h) :=
  (measurable_pairJInv V).comp (amplify_measurable_localRecPair hd V J hVJ z r N hN h)

/-- A shell-measurable version of recentering for an LGF plus continuous field. -/
theorem amplify_exists_measurable_recentered_restrict [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hd : 2 ≤ d) (hh : IsLGFPlusCont h P)
    (V J : Opens (Rd d)) (hVJ : V ≤ J) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hSJ : Metric.sphere z r ⊆ J) :
    ∃ F : Ω → DistOn V, Measurable[fieldSigma0 h J] F ∧
      ∀ᵐ ω ∂P, F ω = restrictTo V (addConst (h ω) (-sphereAvg (h ω) r z)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨N, hN₀⟩ := exists_tsupport_sphBump_subset
    (U := J) (r := r) (z := z) (by simpa only [abs_of_pos hr] using hSJ)
  have hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ J :=
    fun n => hN₀ (n + N) (Nat.le_add_left N n)
  refine ⟨amplify_localRecVersion hd1 V J hVJ z r N hN h,
    amplify_measurable_localRecVersion hd1 V J hVJ z r N hN h, ?_⟩
  filter_upwards [hh.ae_continuousOn_sphereAvg hd] with ω hc
  have ha := hc.1 r hr z
  have hashift : Tendsto (fun n => sphereAvgSeq (h ω) r z (n + N)) atTop
      (𝓝 (sphereAvg (h ω) r z)) := ha.comp (tendsto_add_atTop_nat N)
  have hcoord : amplify_localRecPair hd1 V J hVJ z r N hN h ω =
      pairJ V (restrictTo V (addConst (h ω) (-sphereAvg (h ω) r z))) := by
    funext c
    let φ : TestOn V := comb V c
    have heval : (restrictTo V (addConst (h ω) (-sphereAvg (h ω) r z))) φ =
        restrictTo V (h ω) φ - (∫ x, φ x) * sphereAvg (h ω) r z := by
      rw [restrictTo_apply, addConst_apply, restrictTo_apply]
      simp only [testIncl_apply]
      ring
    have hseq : (fun n => h ω ((amplify_localCenterTest0 hd1 V J hVJ z r N hN φ n).1.1)) =
        fun n => restrictTo V (h ω) φ - (∫ x, φ x) * sphereAvgSeq (h ω) r z (n + N) :=
      funext fun n => amplify_localCenterTest0_apply hd1 V J hVJ z r N hN φ n (h ω)
    have hlim : Tendsto (fun n => h ω
        ((amplify_localCenterTest0 hd1 V J hVJ z r N hN φ n).1.1)) atTop
        (𝓝 (restrictTo V (h ω) φ - (∫ x, φ x) * sphereAvg (h ω) r z)) := by
      rw [hseq]
      exact tendsto_const_nhds.sub (tendsto_const_nhds.mul hashift)
    show limUnder atTop (fun n => h ω
        ((amplify_localCenterTest0 hd1 V J hVJ z r N hN (comb V c) n).1.1)) = _
    rw [hlim.limUnder_eq, ← heval]
    rfl
  change pairJInv V (amplify_localRecPair hd1 V J hVJ z r N hN h ω) = _
  rw [hcoord, pairJInv_pairJ]

/-- Axiom II applied to the shell-measurable recentered restriction. -/
theorem amplify_exists_measurable_internal_recentered_plus
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d) (hh : IsLGFPlusCont h P)
    (V J : Opens (Rd d)) (hVJ : V ≤ J) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hSJ : Metric.sphere z r ⊆ J) :
    ∃ F : Ω → Rd d → Rd d → ℝ≥0∞,
      Measurable[fieldSigma0 h J] F ∧
      ∀ᵐ ω ∂P, ∀ u ∈ V, ∀ v ∈ V,
        F ω u v = (D (addConst (h ω) (-sphereAvg (h ω) r z))).internal V u v := by
  let k : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) r z)
  have hk : IsLGFPlusCont k P :=
    hh.addConst (((measurable_sphereAvg_left r z).comp hh.measurable).neg)
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P k hk V
  obtain ⟨G, hG, hGae⟩ :=
    amplify_exists_measurable_recentered_restrict hd hh V J hVJ z hr hSJ
  refine ⟨fun ω => Φ (G ω), hΦ.comp hG, ?_⟩
  filter_upwards [hΦae, hGae] with ω hloc hrec
  intro u hu v hv
  rw [hrec]
  exact (hloc u hu v hv).symm

/-- The sharp-normalized internal metric has a shell-measurable version for
an LGF plus a continuous field. -/
theorem amplify_exists_measurable_normInternal_plus
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d) (hh : IsLGFPlusCont h P)
    (V J : Opens (Rd d)) (hVJ : V ≤ J) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hSJ : Metric.sphere z r ⊆ J) :
    ∃ F : Ω → Rd d → Rd d → ℝ≥0∞,
      Measurable[fieldSigma0 h J] F ∧
      ∀ᵐ ω ∂P, ∀ u ∈ V, ∀ v ∈ V,
        F ω u v = ENNReal.ofReal ((sNorm ξ Q (h ω) r z)⁻¹) *
          (D (h ω)).internal V u v := by
  obtain ⟨G, hGm, hGae⟩ :=
    amplify_exists_measurable_internal_recentered_plus hD hd hh V J hVJ z hr hSJ
  let F : Ω → Rd d → Rd d → ℝ≥0∞ :=
    fun ω u v => ENNReal.ofReal ((r ^ (ξ * Q))⁻¹) * G ω u v
  have hFm : Measurable[fieldSigma0 h J] F := by
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun u => ?_
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h J) _ _ |>.2 fun v => ?_
    exact measurable_const.mul
      ((measurable_pi_apply v).comp ((measurable_pi_apply u).comp hGm))
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hGae, hD.ae_internal_mem_Icc hh] with ω hF hW
  intro u hu v hv
  dsimp only [F]
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
  rw [he, ← mul_assoc, ← ofReal_sNorm_inv]

/-- Extend the shell-measurable version by infinity off the domain. -/
theorem amplify_exists_measurable_normInternal_all_plus
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d) (hh : IsLGFPlusCont h P)
    (V J : Opens (Rd d)) (hVJ : V ≤ J) (z : Rd d) {r : ℝ} (hr : 0 < r)
    (hSJ : Metric.sphere z r ⊆ J) :
    ∃ F : Ω → Rd d → Rd d → ℝ≥0∞,
      Measurable[fieldSigma0 h J] F ∧
      ∀ᵐ ω ∂P, ∀ u v,
        F ω u v = ENNReal.ofReal ((sNorm ξ Q (h ω) r z)⁻¹) *
          (D (h ω)).internal V u v := by
  classical
  obtain ⟨F, hFm, hFae⟩ :=
    amplify_exists_measurable_normInternal_plus hD hd hh V J hVJ z hr hSJ
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
  have hsNorm : 0 < sNorm ξ Q (h ω) r z := by unfold sNorm; positivity
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
