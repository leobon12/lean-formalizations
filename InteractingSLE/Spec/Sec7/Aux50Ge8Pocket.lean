/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Ge8Var
import InteractingSLE.Spec.Sec7.Aux50Ge8Path
import InteractingSLE.Spec.Sec7.Aux50HitBirth

/-!
# Aux. lemma 50 for `κ ≥ 8`: the fresh pocket field at a birth, (HGV9)–(HGV11)

Packet PROVE-AUX50C. Specification Aux. lemma 50, proof, "Identifying the jumps, as distributions"
(`source/spec/p193-240.md` L893–L912, pp. 239–240): "Fix a birth time `τ` […] Let `τ_n ↑ τ` announce that birth.
Conditional expectations of the entire field given the increasing old marked germs converge […] Their covariance is
the monotone limit of `G_{D_{τ_n}}`", (HGV9)–(HGV10), and (HGV11): "`E[(N_t(φ) − N_0(φ)) J_t(φ)] = E ∑ G_P(φ, φ)`".

For a test `ψ` with nonempty compact support `K` and the pocket event `E = {K is swallowed at one time β ≤ N}`, the
pocket fluctuation is `1_E ((h, ψ) − E[(h, ψ) | 𝓕_N])`. Its covariance with the whole field tested against **any** `φ`
is the retained Green form:

`E[(h⁰, φ) · 1_E ((h, ψ) − E[(h, ψ) | 𝓕_N])] = E[1_E ∬ φ(a) ψ(b) V_N(a, b)]`  (`integral_mul_pocket_eq`).

Proof: the safe exit rules `ρ_m` of `K` announce the birth (PROVE-AUX50B); along the germs `Γ_{ρ_m}` the whole field
is Gaussian with covariance `G_{D_{ρ_m}}` (`ae_condExp_mul_germ_eq`), Lévy's upward theorem passes the conditional
moments to `Γ^- = ⋁ Γ_{ρ_m}`; the announced mean of `ψ` is the pocket mean `E[(h, ψ) | 𝓕_N]` (PROVE-AUX50B's freeze),
the announced covariance is `lim G_{D_{ρ_m}}(φ, ψ) = ∬ φ ψ V_N` (`tendsto_aGreen_VT_of_birth`), and the pocket event is
announced (quasi-left continuity `WholeField.stopping_le_iSup_of_tendsto`, pocket event
`WholeField.exists_pocketEvent`).

The pocket event is read off the recorded history by the Borel predicate `histPoc` (`histPoc_iff`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Aux50Ge8

open QuantumZipper QuantumZipper.K3 LQGMetric LocalSets WholeField Coupling Aux50Hit Sec4 LawUnique

variable {nL nR : ℕ}

/-! ### The pocket event of a history -/

/-- **The Borel pocket predicate** of a recorded history at `N`: `C` is a label at `N` and meets the hull. -/
def histPoc (N : ℕ) (C : Set ℂ) (γ : HistorySpace nL nR) : Prop :=
  histLab N C γ ∧ ¬ Disjoint C (regHull (stopHistory (cstop N) γ))

theorem measurableSet_histPoc (N : ℕ) {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) :
    MeasurableSet {γ : HistorySpace nL nR | histPoc N C γ} :=
  (measurableSet_histLab N hC hCH).inter
    ((measurable_stopHistory (measurable_cstop (N : ℝ≥0))) (measurableSet_disjoint_regHull hC)).compl

section Path

universe v

variable {Ω : Type v} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {ω : Ω}

/-- On a good path, the Borel pocket predicate of the history at `N` is the pocket event of a nonempty set. -/
theorem histPoc_iff (hg : IsGoodPath W VL VR ζ ω) (N : ℕ) {C : Set ℂ} (hCH : C ⊆ H) (hne : C.Nonempty) :
    histPoc N C (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) ↔ IsPocketLabel (fun t => W t ω) C N := by
  have hreg : regHull (stopHistory (cstop (N : ℝ≥0)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))) =
      fwdHull (Ito.rpath fun t => W t ω) (N : ℝ≥0) := by
    rw [stopHistory_cstop_natStop le_rfl, regHull_stopHistory_cstop hg]
  rw [histPoc, histLab_iff hg N hCH, hreg, IsLabel]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd h1 h2
    · exact h1
  · intro hp
    refine ⟨Or.inr hp, fun hd => ?_⟩
    obtain ⟨z, hz⟩ := hne
    exact Set.disjoint_left.1 hd hz (hp.subset_fwdHull hCH hz)

end Path

/-! ### The birth limit of the covariance, pathwise -/

/-- `φ(a) ψ(b) V_N(a, b)` is integrable on `ℂ × ℂ`, dominated by the time-`0` kernel. -/
theorem integrable_test_VT {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (N : ℝ≥0)
    (φ ψ : TestOn upperHalfPlaneOpens) :
    Integrable (fun q : ℂ × ℂ => φ q.1 * ψ q.2 * VT (Ito.rpath w) N q.1 q.2) ((volume : Measure ℂ).prod volume) := by
  have hW := continuous_rpath_of hw
  have hW0 : Ito.rpath w 0 = 0 := by simp [Ito.rpath, hw0]
  have hmV := measurable_indicator_VTe hW hW0 (N : ℝ)
  have heq : (fun q : ℂ × ℂ => φ q.1 * ψ q.2 * VT (Ito.rpath w) N q.1 q.2) =
      fun q => φ q.1 * ψ q.2 * (c5Vm (Ito.rpath w) N q).toReal := by
    funext q
    by_cases hq : q ∈ H ×ˢ H
    · rw [c5Vm, indicator_of_mem hq]; rfl
    · rcases not_and_or.1 hq with h | h
      · rw [image_eq_zero_of_notMem_tsupport fun hs => h (φ.tsupport_subset hs)]; ring
      · rw [image_eq_zero_of_notMem_tsupport (f := ψ) fun hs => h (ψ.tsupport_subset hs)]; ring
  rw [heq]
  refine (integrable_abs_test_aGreen_zero hW hW0 φ ψ).mono' ?_ (Eventually.of_forall fun q => ?_)
  · exact ((φ.continuous.measurable.comp measurable_fst).mul (ψ.continuous.measurable.comp measurable_snd)).mul
      (ENNReal.measurable_toReal.comp hmV) |>.aestronglyMeasurable
  · by_cases hq : q ∈ H ×ˢ H
    · rw [c5Vm, indicator_of_mem hq, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left (VT_le_aGreen_zero hW N.coe_nonneg hq.1 hq.2) (by positivity)
    · rw [c5Vm, indicator_of_notMem hq]
      simp only [ENNReal.toReal_zero, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (aGreen_nonneg _ _ _ _)

/-- **The covariance of a test with a newborn pocket test converges to the retained form.** If every point of
`tsupport ψ` is swallowed at `β ≤ N` and `s_m < β` increase to `β`, then
`∬ φ(a) ψ(b) G_{s_m}(a, b) → ∬ φ(a) ψ(b) V_N(a, b)`. -/
theorem tendsto_covInt_of_birth {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {N β : ℝ≥0} (hβN : β ≤ N)
    (φ ψ : TestOn upperHalfPlaneOpens)
    (hβ : ∀ b ∈ tsupport ψ, swallowTime (Ito.rpath w) b = ENNReal.ofReal (β : ℝ)) {s : ℕ → ℝ≥0}
    (hsβ : ∀ m, s m < β) (hlim : Tendsto s atTop (𝓝 β)) :
    Tendsto (fun m => ∫ a, ∫ b, φ a * ψ b * aGreen (Ito.rpath w) (s m) a b) atTop
      (𝓝 (∫ a, ∫ b, φ a * ψ b * VT (Ito.rpath w) N a b)) := by
  have hW := continuous_rpath_of hw
  have hW0 : Ito.rpath w 0 = 0 := by simp [Ito.rpath, hw0]
  have hprod : ∀ m, ∫ a, ∫ b, φ a * ψ b * aGreen (Ito.rpath w) (s m) a b =
      ∫ q, φ q.1 * ψ q.2 * aGreen (Ito.rpath w) (s m) q.1 q.2 ∂((volume : Measure ℂ).prod volume) := fun m =>
    (integral_prod _ (integrable_test_aGreen hW hW0 (NNReal.coe_nonneg _) φ ψ)).symm
  have hprodV : ∫ a, ∫ b, φ a * ψ b * VT (Ito.rpath w) N a b =
      ∫ q, φ q.1 * ψ q.2 * VT (Ito.rpath w) N q.1 q.2 ∂((volume : Measure ℂ).prod volume) :=
    (integral_prod _ (integrable_test_VT hw hw0 N φ ψ)).symm
  simp only [hprod, hprodV]
  refine tendsto_integral_of_dominated_convergence (fun q => |φ q.1| * |ψ q.2| * aGreen (Ito.rpath w) 0 q.1 q.2)
    (fun m => (integrable_test_aGreen hW hW0 (NNReal.coe_nonneg _) φ ψ).aestronglyMeasurable)
    (integrable_abs_test_aGreen_zero hW hW0 φ ψ) (fun m => Eventually.of_forall fun q => ?_)
    (Eventually.of_forall fun q => ?_)
  · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (aGreen_nonneg _ _ _ _)]
    exact mul_le_mul_of_nonneg_left (aGreen_le_zero hW (NNReal.coe_nonneg _) _ _) (by positivity)
  · by_cases hb : q.2 ∈ tsupport ψ
    · by_cases ha : q.1 ∈ H
      · exact (tendsto_aGreen_VT_of_birth hw ha (ψ.tsupport_subset hb) hβN (hβ q.2 hb) hsβ hlim).const_mul _
      · rw [image_eq_zero_of_notMem_tsupport fun hs => ha (φ.tsupport_subset hs)]
        simp only [zero_mul]
        exact tendsto_const_nhds
    · rw [image_eq_zero_of_notMem_tsupport (f := ψ) hb]
      simp only [mul_zero, zero_mul]
      exact tendsto_const_nhds

/-! ### A compact set in every germ neighbourhood of a relatively closed set lies in it -/

theorem subset_of_forall_germNbhd {S K : Set ℂ} (hS : IsOpen (H \ S)) (hKH : K ⊆ H)
    (hK : ∀ δ : ℝ, 0 < δ → K ⊆ germNbhd δ S) : K ⊆ S := by
  intro z hz
  by_contra hzS
  have hzH : 0 < z.im := hKH hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hS z ⟨hzH, hzS⟩
  set δ : ℝ := min (min r z.im) (1 / (‖z‖ + 1)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hr hzH) (by positivity)
  have hmem := hK δ hδ0 hz
  rcases hmem.2 with h1 | h1
  · obtain ⟨y, hy, hyz⟩ := Metric.mem_thickening_iff.1 h1
    rcases hy with ⟨hyS, -⟩ | hy
    · have : y ∈ ball z r := by
        rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hyz ((min_le_left _ _).trans (min_le_left _ _))
      exact (hball this).2 hyS
    · have h2 : z.im ≤ dist z y := by
        have := Complex.abs_im_le_norm (z - y)
        rw [Complex.sub_im, show y.im = 0 from hy, sub_zero, abs_of_pos hzH] at this
        rwa [dist_eq_norm]
      linarith [hyz, (min_le_left _ _).trans (min_le_right r z.im) |>.trans_eq' hδ.symm]
  · have h2 : 1 / δ < ‖z‖ := h1
    have h3 : ‖z‖ + 1 ≤ 1 / δ := by
      rw [le_one_div (by positivity) hδ0]; exact min_le_right _ _
    linarith

/-! ### The conditional variance on an event -/

section Variance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Conditional variance on an event.** If, on an event `F` of `m`, the conditional characteristic function of `Z`
given `m` is Gaussian with mean `E[Z | m]` and variance `q` at every frequency, then `F.indicator q` is integrable
and `E[1_F (Z − E[Z | m])²] = E[1_F q]`. -/
theorem integral_indicator_sq_sub_condExp_eq {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {F : Set Ω}
    (hF : MeasurableSet[m] F) {Z q : Ω → ℝ} (hZ : MemLp Z 2 P) (hZm : Measurable[mΩ] Z)
    (hc : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ F → (P[fun ω => cexp (I * ((c * Z ω : ℝ) : ℂ)) | m]) ω =
      WangWu.gaussCF (c * (P[Z | m]) ω) (c ^ 2 * q ω)) :
    Integrable (F.indicator q) P ∧
      ∫ ω, F.indicator (fun ω => (Z ω - (P[Z | m]) ω) ^ 2) ω ∂P = ∫ ω, F.indicator q ω ∂P := by
  have hFm : MeasurableSet[mΩ] F := hm F hF
  set μ := P[Z | m] with hμ
  have hμ2 : MemLp μ 2 P := hZ.condExp one_le_two
  set Y : Ω → ℝ := F.indicator Z with hY
  have hYm : Measurable[mΩ] Y := hZm.indicator hFm
  have hY2 : MemLp Y 2 P := hZ.indicator hFm
  have hc' : ∀ c : ℝ, P[fun ω => cexp (I * ((c * Y ω : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => LocalExt.cfVal (c * F.indicator μ ω) (c ^ 2 * F.indicator q ω) := by
    intro c
    have hint : Integrable (fun ω => cexp (I * ((c * Z ω : ℝ) : ℂ))) P :=
      Integrable.of_bound (μ := P) (Measurable.aestronglyMeasurable (m := mΩ) (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_const.mul hZm))))) 1
        (Eventually.of_forall fun ω => (LocalExt.norm_cexp_I_mul _).le)
    have e : (fun ω => cexp (I * ((c * Y ω : ℝ) : ℂ))) =
        F.indicator (fun ω => cexp (I * ((c * Z ω : ℝ) : ℂ))) + Fᶜ.indicator (fun _ => 1) := by
      funext ω
      by_cases hω : ω ∈ F
      · simp [hY, hω]
      · simp [hY, hω]
    have h1 := condExp_indicator (m := m) hint hF
    have h2 : P[Fᶜ.indicator (fun _ : Ω => (1 : ℂ)) | m] = Fᶜ.indicator (fun _ => 1) :=
      condExp_of_stronglyMeasurable hm (stronglyMeasurable_const.indicator hF.compl)
        ((integrable_const (1 : ℂ)).indicator hFm.compl)
    rw [e]
    filter_upwards [condExp_add (m := m) (hint.indicator hFm) ((integrable_const (1 : ℂ)).indicator hFm.compl),
      h1, hc c] with ω k1 k2 k3
    rw [k1, Pi.add_apply, k2, h2]
    by_cases hω : ω ∈ F
    · rw [indicator_of_mem hω, indicator_of_notMem (show ω ∉ Fᶜ from not_not.2 hω), add_zero, k3 hω,
        indicator_of_mem hω, indicator_of_mem hω]
      rfl
    · simp only [indicator_of_notMem hω, indicator_of_mem (show ω ∈ Fᶜ from hω), zero_add, mul_zero,
        LocalExt.cfVal]
      simp
  have hint2 : Integrable (fun ω => (Y ω - 0) ^ 2) P := by simpa only [sub_zero] using hY2.integrable_sq
  have key := LocalExt.ae_condExp_sq_sub_of_condGauss hm hYm hc' 0 hint2
  simp only [sub_zero] at key
  -- integrability of the variance on `F`
  have hqi : Integrable (F.indicator q) P := by
    have : F.indicator q =ᵐ[P] fun ω => (P[fun ω => Y ω ^ 2 | m]) ω - (F.indicator μ ω) ^ 2 := by
      filter_upwards [key] with ω hω; rw [hω]; ring
    exact (integrable_condExp.sub ((hμ2.indicator hFm).integrable_sq)).congr this.symm
  refine ⟨hqi, ?_⟩
  have m1 : ∫ ω, Y ω ^ 2 ∂P = ∫ ω, F.indicator q ω ∂P + ∫ ω, (F.indicator μ ω) ^ 2 ∂P := by
    rw [← integral_condExp hm (f := fun ω => Y ω ^ 2), integral_congr_ae key,
      integral_add hqi (hμ2.indicator hFm).integrable_sq]
  have m2 : ∫ ω, Z ω * F.indicator μ ω ∂P = ∫ ω, (F.indicator μ ω) ^ 2 ∂P := by
    rw [← integral_condExp_mul_eq hm hZ (hμ2.indicator hFm) (stronglyMeasurable_condExp.indicator hF)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ F
    · simp only [indicator_of_mem hω, hμ]; ring
    · simp only [indicator_of_notMem hω]; ring
  have i1 : Integrable (fun ω => Y ω ^ 2) P := hY2.integrable_sq
  have i2 : Integrable (fun ω => Z ω * F.indicator μ ω) P := hZ.integrable_mul (hμ2.indicator hFm)
  have i3 : Integrable (fun ω => (F.indicator μ ω) ^ 2) P := (hμ2.indicator hFm).integrable_sq
  have e : ∀ ω, F.indicator (fun ω => (Z ω - μ ω) ^ 2) ω =
      Y ω ^ 2 - 2 * (Z ω * F.indicator μ ω) + (F.indicator μ ω) ^ 2 := by
    intro ω
    by_cases hω : ω ∈ F
    · simp only [hY, indicator_of_mem hω]; ring
    · simp only [hY, indicator_of_notMem hω]; ring
  have i4 : Integrable (fun ω => 2 * (Z ω * F.indicator μ ω)) P := i2.const_mul 2
  have i5 : Integrable (fun ω => Y ω ^ 2 - 2 * (Z ω * F.indicator μ ω)) P := i1.sub i4
  rw [integral_congr_ae (Eventually.of_forall e), integral_add i5 i3, integral_sub i1 i4,
    integral_const_mul, m1, m2]
  ring

end Variance

section Coupling

universe v

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The pocket fluctuation against the whole field** ((HGV9)–(HGV11)): for tests `φ, ψ` and `N ≥ 1`,
`E[(h⁰, φ) 1_E ((h, ψ) − E[(h, ψ) | 𝓕_N])] = E[1_E ∬ φ(a) ψ(b) V_N(a, b)]`, `E` the pocket event of `tsupport ψ`
at `N` (read off the history by `histPoc`). -/
theorem integral_mul_pocket_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop N) W VL VR ζ))
    (φ ψ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => {ω | histPoc N (tsupport ψ) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
        (fun ω => ∫ a, ∫ b, φ a * ψ b * VT (Ito.rpath fun t => W t ω) N a b) ω) P ∧
    ∫ ω, centredField h u₀ ω φ *
        {ω | histPoc N (tsupport ψ) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
          (fun ω => h ω ψ - (P[fun ω' => h ω' ψ | hN.measurableSpace]) ω) ω ∂P =
      ∫ ω, {ω | histPoc N (tsupport ψ) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
        (fun ω => ∫ a, ∫ b, φ a * ψ b * VT (Ito.rpath fun t => W t ω) N a b) ω ∂P := by
  set E : Set Ω := {ω | histPoc N (tsupport ψ) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))} with hEdef
  set K : Set ℂ := tsupport ψ with hKdef
  by_cases hne : K.Nonempty
  swap
  · have hE0 : E = ∅ := by
      ext ω
      simp only [hEdef, mem_ofPred_eq, mem_empty_iff_false, iff_false, histPoc, not_and, not_not]
      intro _
      rw [Set.not_nonempty_iff_eq_empty.1 hne]
      exact Set.empty_disjoint _
    simp only [hE0, indicator_empty, mul_zero, integral_zero]
    exact ⟨integrable_zero _ _ _, trivial⟩
  have hE := hC.1
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  have hKH : K ⊆ H := ψ.tsupport_subset
  set m : ℝ := testLow ψ with hmdef
  have hm : 0 < m := testLow_pos ψ
  have hKm : ∀ z ∈ K, m ≤ z.im := fun z hz => testLow_le ψ hz
  set ρ : ℕ → Ω → ℝ≥0 := fun k ω => safeKRule K m N k (killedHistory W VL VR ζ ω) with hρdef
  have hρ : ∀ k, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ k ω : WithTop ℝ≥0) := fun k =>
    isStoppingTime_safeKRule hE hζ hX hKH hm N k
  have hgood := ae_isGoodPath hE hζ
  have hρN : ∀ k ω, ρ k ω ≤ (N : ℝ≥0) := fun k ω => safeRule_le K m N k _
  have hρm : ∀ ω, Monotone fun k => ρ k ω := by
    intro ω k k' hkk'
    simp only [hρdef, safeKRule, safeRule]
    have hk : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
    exact Coupling.safeExitTime_mono (div_le_div_of_nonneg_left hm.le (by positivity) (by linarith)) hk le_rfl
  have hbdd : ∀ ω, BddAbove (range fun k => ρ k ω) := fun ω => ⟨N, by rintro _ ⟨k, rfl⟩; exact hρN k ω⟩
  set T : Ω → ℝ≥0 := fun ω => ⨆ k, ρ k ω with hTdef
  have hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0) :=
    WangWu.isStoppingTime_iSup_coe hρ hρN
  have hρT : ∀ k ω, ρ k ω ≤ T ω := fun k ω => le_ciSup (hbdd ω) k
  have hρlim : ∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (T ω)) := fun ω =>
    tendsto_atTop_ciSup (hρm ω) (hbdd ω)
  have hlt : ∀ c : Ω → ℝ≥0, ∀ᵐ ω ∂P, (c ω : ℝ≥0∞) < ζ ω := fun c =>
    hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top
  have hdis : ∀ᵐ ω ∂P, ∀ k, Disjoint K (fwdHull (Ito.rpath fun t => W t ω) (ρ k ω)) := by
    filter_upwards [hgood] with ω hg using (safeKRule_props hg hK hKH hm hKm N).2.2.1
  have hT0 : ∀ᵐ ω ∂P, 0 < T ω ∨ ∀ i j, xL i < xR j := by
    filter_upwards [hgood] with ω hg
    left
    obtain ⟨t, ht0, -, htd⟩ := exists_pos_disjoint_fwdHull_of_path hg.2.2.1 hg.2.1
      (by rw [hg.1]; exact ENNReal.zero_lt_top) hK hKH
    have ht1 : min t 1 ≤ (N : ℝ≥0) := (min_le_right _ _).trans (by exact_mod_cast hN1)
    have hd1 : Disjoint K (fwdHull (Ito.rpath fun t => W t ω) (min t 1 : ℝ≥0)) :=
      htd.mono_right (fwdHull_mono.1 (by exact_mod_cast min_le_left t 1))
    obtain ⟨k, hk⟩ := ((safeKRule_props hg hK hKH hm hKm N).2.2.2 _ ht1 hd1).exists
    exact lt_of_lt_of_le (lt_min ht0 one_pos) (hk.trans (hρT k ω))
  have hev : ∀ᵐ ω ∂P, IsPocketLabel (fun t => W t ω) K N → ∃ β : ℝ≥0, T ω = β ∧ (∀ k, ρ k ω < β) ∧
      (∀ z ∈ K, swallowTime (Ito.rpath fun t => W t ω) z = β) ∧ β ≤ N := by
    filter_upwards [hgood] with ω hg ⟨β, hβN, hβ⟩
    obtain ⟨-, -, hd, hex⟩ := safeKRule_props hg hK hKH hm hKm N
    obtain ⟨z₀, hz₀⟩ := hne
    have hlt : ∀ k, ρ k ω < β := fun k => by
      by_contra hle
      refine Set.disjoint_left.1 (hd k) hz₀ (mem_fwdHull_rpath_iff.2 ⟨hKH hz₀, ?_⟩)
      rw [hβ z₀ hz₀]; exact_mod_cast not_lt.1 hle
    refine ⟨β, le_antisymm (ciSup_le fun k => (hlt k).le) ?_, hlt, hβ, hβN⟩
    refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
    have hdisj : Disjoint K (fwdHull (Ito.rpath fun t => W t ω) (t : ℝ)) :=
      isActiveLabel_of_lt_swallowTime (w := fun t => W t ω) (C := K) (t := t) fun z hz => by
        rw [hβ z hz]; exact_mod_cast ht
    obtain ⟨k, hk⟩ := (hex t (ht.le.trans hβN) hdisj).exists
    exact hk.trans (hρT k ω)
  -- the announced germs along the safe rules
  choose A hAm hAK hA𝓕 using fun k => exists_hullVersion hC hκ hX (hρ k) (hlt (ρ k))
  obtain ⟨σ₀, hσ₀⟩ := exists_announcingSeq hC hκ hX hζ
  have hh0m := measurable_centredField hC.2.1 u₀
  let 𝒢 : Filtration ℕ mΩ :=
    { seq := fun k => histGerm (hρ k).measurableSpace (A k) (centredField h u₀)
      mono' := fun i j hij => histGerm_le_of_le hC hX hσ₀ (hρ i) (hρ j) (fun ω => hρm ω hij) hζ (hAm i) (hAm j)
        (hAK i) (hAK j)
      le' := fun k => histGerm_le (hρ k).measurableSpace_le (hAm k) hh0m }
  have h𝒢le : (⨆ k, 𝒢 k) ≤ mΩ := iSup_le fun k => 𝒢.le k
  set X : Ω → ℝ := fun ω => centredField h u₀ ω φ with hXdef
  set Y : Ω → ℝ := fun ω => centredField h u₀ ω ψ with hYdef
  have hX2 : MemLp X 2 P := memLp_centredField hC hu₀ φ
  have hY2 : MemLp Y 2 P := memLp_centredField hC hu₀ ψ
  have lXY := tendsto_ae_condExp (μ := P) (ℱ := 𝒢) (fun ω => X ω * Y ω)
  have lX := tendsto_ae_condExp (μ := P) (ℱ := 𝒢) X
  have lY := tendsto_ae_condExp (μ := P) (ℱ := 𝒢) Y
  have hCk : ∀ k, ∀ᵐ ω ∂P, (P[fun ω => X ω * Y ω | 𝒢 k]) ω =
      (P[X | 𝒢 k]) ω * (P[Y | 𝒢 k]) ω + covAt W (ρ k ω) φ ψ ω := fun k =>
    ae_condExp_mul_germ_eq hC hκ hu₀ hX (hρ k) (hlt (ρ k)) (hAm k) (hAK k) φ ψ
  have hYk : ∀ k, ∀ᵐ ω ∂P, (P[Y | 𝒢 k]) ω =
      (P[fun ω' => h ω' ψ | (hρ k).measurableSpace]) ω - ∫ z, u₀ z * ψ z := fun k => by
    filter_upwards [ae_condExp_germ_eq_of_active hC hu₀ hX (hρ k) (hlt (ρ k)) (hAm k) (hAK k) hκ ψ, hdis]
      with ω e hd
    exact e (hd k)
  have hlimψ := ae_tendsto_condExp_safeKRule_of_pocket hC hκ hζ hX hN1 ψ hne hN
  -- the announced mean of the pocket test is the pocket mean
  have hNY : ∀ᵐ ω ∂P, IsPocketLabel (fun t => W t ω) K N →
      (P[Y | ⨆ k, 𝒢 k]) ω = (P[fun ω' => h ω' ψ | hN.measurableSpace]) ω - ∫ z, u₀ z * ψ z := by
    filter_upwards [lY, ae_all_iff.2 hYk, hlimψ] with ω h1 h2 h3 hp
    refine tendsto_nhds_unique h1 ?_
    simp only [h2]
    exact (h3 hp).sub_const _
  -- the announced covariance
  set c : Ω → ℝ := fun ω => (P[fun ω => X ω * Y ω | ⨆ k, 𝒢 k]) ω -
    (P[X | ⨆ k, 𝒢 k]) ω * (P[Y | ⨆ k, 𝒢 k]) ω with hc
  have hck : ∀ᵐ ω ∂P, Tendsto (fun k => covAt W (ρ k ω) φ ψ ω) atTop (𝓝 (c ω)) := by
    filter_upwards [lXY, lX, lY, ae_all_iff.2 hCk] with ω h1 h2 h3 h4
    have e : (fun k => covAt W (ρ k ω) φ ψ ω) =
        fun k => (P[fun ω => X ω * Y ω | 𝒢 k]) ω - (P[X | 𝒢 k]) ω * (P[Y | 𝒢 k]) ω := by
      funext k; rw [h4 k]; ring
    rw [e]
    exact h1.sub (h2.mul h3)
  have hcpath : ∀ᵐ ω ∂P, IsPocketLabel (fun t => W t ω) K N →
      c ω = ∫ a, ∫ b, φ a * ψ b * VT (Ito.rpath fun t => W t ω) N a b := by
    filter_upwards [hck, hgood, hev] with ω h1 hg hevω hp
    obtain ⟨β, hTβ, hρβ, hβ, hβN⟩ := hevω hp
    refine tendsto_nhds_unique h1 ?_
    have hw0 : Ito.rpath (fun t => W t ω) 0 = 0 := by simp [Ito.rpath, hg.2.1]
    have e : ∀ k, covAt W (ρ k ω) φ ψ ω =
        ∫ a, ∫ b, φ a * ψ b * aGreen (Ito.rpath fun t => W t ω) (ρ k ω) a b := fun k =>
      zeroGFFTestCov_actDom_eq (continuous_rpath_of hg.continuous) hw0 (NNReal.coe_nonneg _) φ ψ
    simp only [e]
    refine tendsto_covInt_of_birth hg.continuous hg.2.1 hβN φ ψ
      (fun b hb => by rw [hβ b hb, ENNReal.ofReal_coe_nnreal]) hρβ ?_
    rw [← hTβ]
    exact hρlim ω
  -- the pocket event, announced
  have hEp : ∀ᵐ ω ∂P, (ω ∈ E ↔ IsPocketLabel (fun t => W t ω) K N) :=
    hgood.mono fun ω hg => histPoc_iff hg N hKH hne
  obtain ⟨AT, hATm, hATK, hAT𝓕⟩ := exists_hullVersion hC hκ hX hT (hlt T)
  obtain ⟨F, hFm, hFsub, hFmem⟩ := exists_pocketEvent hAT𝓕 hKH
  have hEF : ∀ᵐ ω ∂P, (ω ∈ E ↔ ω ∈ F) := by
    filter_upwards [hEp, hev, hATK, hgood, hdis] with ω e1 e2 e3 hg hd
    rw [e1]
    constructor
    · intro hp
      obtain ⟨β, hTβ, -, hβ, -⟩ := e2 hp
      refine hFmem ω ?_
      rw [e3, hTβ]
      intro z hz
      exact ⟨hKH hz, le_of_eq ((hβ z hz).trans ENNReal.ofReal_coe_nnreal.symm)⟩
    · intro hF
      have hopen : IsOpen (H \ AT ω) := by
        rw [e3]; exact FwdHolo.isOpen_compl_fwdHull (continuous_rpath_of hg.continuous) (NNReal.coe_nonneg _)
      have hKA : K ⊆ AT ω := subset_of_forall_germNbhd hopen hKH (hFsub ω hF)
      rw [e3] at hKA
      refine ⟨T ω, ciSup_le fun k => hρN k ω, fun z hz => le_antisymm ?_ ?_⟩
      · have := (hKA hz).2; rwa [ENNReal.ofReal_coe_nnreal] at this
      · have hlim' : Tendsto (fun k => ((ρ k ω : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 (T ω : ℝ≥0∞)) :=
          ENNReal.tendsto_coe.2 (hρlim ω)
        refine le_of_tendsto hlim' (Eventually.of_forall fun k => ?_)
        have hzk : z ∉ fwdHull (Ito.rpath fun t => W t ω) (ρ k ω) := fun h' => Set.disjoint_left.1 (hd k) hz h'
        have := lt_swallowTime_of_not_mem (hKH hz) hzk
        rw [ENNReal.ofReal_coe_nnreal] at this
        exact this.le
  have hQLC := stopping_le_iSup_of_tendsto hC hκ hu₀ hX hT (hlt T) hT0 hρ hρT (Eventually.of_forall hρlim)
  have hF𝒢 : MeasurableSet[⨆ k, 𝒢 k] F :=
    (hQLC.trans (iSup_mono fun k => le_histGerm (A k) (centredField h u₀))) F hFm
  have hFm' : MeasurableSet F := h𝒢le F hF𝒢
  -- the computation
  have hXY : Integrable (fun ω => X ω * Y ω) P := hX2.integrable_mul hY2
  have hNinf : MemLp (P[Y | ⨆ k, 𝒢 k]) 2 P := hY2.condExp one_le_two
  have hgF : MemLp (F.indicator (P[Y | ⨆ k, 𝒢 k])) 2 P := hNinf.indicator hFm'
  have hgFm : StronglyMeasurable[⨆ k, 𝒢 k] (F.indicator (P[Y | ⨆ k, 𝒢 k])) :=
    stronglyMeasurable_condExp.indicator hF𝒢
  have e1 : ∫ ω, X ω * E.indicator (fun ω => h ω ψ - (P[fun ω' => h ω' ψ | hN.measurableSpace]) ω) ω ∂P =
      ∫ ω, F.indicator (fun ω => X ω * Y ω) ω ∂P - ∫ ω, X ω * F.indicator (P[Y | ⨆ k, 𝒢 k]) ω ∂P := by
    have i1 : Integrable (fun ω => F.indicator (fun ω => X ω * Y ω) ω) P := hXY.indicator hFm'
    have i2 : Integrable (fun ω => X ω * F.indicator (P[Y | ⨆ k, 𝒢 k]) ω) P := hX2.integrable_mul hgF
    rw [← integral_sub i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [hEF, hEp, hNY] with ω f1 f2 f3
    by_cases hω : ω ∈ E
    · have hωF := f1.1 hω
      rw [indicator_of_mem hω, indicator_of_mem hωF, indicator_of_mem hωF, f3 (f2.1 hω)]
      simp only [hYdef, centredField_apply h hu₀.1]
      ring
    · have hωF : ω ∉ F := fun h' => hω (f1.2 h')
      rw [indicator_of_notMem hω, indicator_of_notMem hωF, indicator_of_notMem hωF]
      ring
  have e2 : ∫ ω, F.indicator (fun ω => X ω * Y ω) ω ∂P =
      ∫ ω, F.indicator (P[fun ω => X ω * Y ω | ⨆ k, 𝒢 k]) ω ∂P := by
    rw [integral_indicator hFm', integral_indicator hFm', setIntegral_condExp h𝒢le hXY hF𝒢]
  have e3 : ∫ ω, X ω * F.indicator (P[Y | ⨆ k, 𝒢 k]) ω ∂P =
      ∫ ω, (P[X | ⨆ k, 𝒢 k]) ω * F.indicator (P[Y | ⨆ k, 𝒢 k]) ω ∂P :=
    (integral_condExp_mul_eq h𝒢le hX2 hgF hgFm).symm
  have e4 : ∫ ω, F.indicator (P[fun ω => X ω * Y ω | ⨆ k, 𝒢 k]) ω ∂P -
      ∫ ω, (P[X | ⨆ k, 𝒢 k]) ω * F.indicator (P[Y | ⨆ k, 𝒢 k]) ω ∂P = ∫ ω, F.indicator c ω ∂P := by
    have i1 : Integrable (fun ω => F.indicator (P[fun ω => X ω * Y ω | ⨆ k, 𝒢 k]) ω) P :=
      integrable_condExp.indicator hFm'
    have i2 : Integrable (fun ω => (P[X | ⨆ k, 𝒢 k]) ω * F.indicator (P[Y | ⨆ k, 𝒢 k]) ω) P :=
      (hX2.condExp one_le_two).integrable_mul hgF
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ F
    · simp only [indicator_of_mem hω, hc]
    · simp only [indicator_of_notMem hω, mul_zero, sub_zero]
  have hfin : (fun ω => E.indicator (fun ω => ∫ a, ∫ b, φ a * ψ b * VT (Ito.rpath fun t => W t ω) N a b) ω)
      =ᵐ[P] F.indicator c := by
    filter_upwards [hEF, hEp, hcpath] with ω f1 f2 f3
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω, indicator_of_mem (f1.1 hω), f3 (f2.1 hω)]
    · rw [indicator_of_notMem hω, indicator_of_notMem fun h' => hω (f1.2 h')]
  have hci : Integrable c P :=
    integrable_condExp.sub ((hX2.condExp one_le_two).integrable_mul hNinf)
  refine ⟨(hci.indicator hFm').congr hfin.symm, ?_⟩
  rw [e1, e2, e3, e4]
  exact (integral_congr_ae hfin).symm

omit [IsProbabilityMeasure P] in
/-- The pocket event of a test at `N` is an event of the driving filtration at `N`. -/
theorem measurableSet_pocketEvent (hX : IsMeasurableKilledDriving W VL VR ζ) {N : ℕ}
    (hN : IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop N) W VL VR ζ)) (ψ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[hN.measurableSpace]
      {ω | histPoc N (tsupport ψ) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))} :=
  (measurable_stopHistory_killedHistory hX hN)
    (measurableSet_histPoc N ψ.hasCompactSupport.isCompact ψ.tsupport_subset)

open scoped Classical in
/-- **The variance of the pocket fluctuations** (C.4 on each pattern of pocket pieces): for tests `ψₖ`, `k ∈ s`,
`E[(∑ₖ 1_{Eₖ} ((h, ψₖ) − E[(h, ψₖ) | 𝓕_N]))²] = E[Q_{U_N}(∑ₖ 1_{Eₖ} ψₖ)]`, `Eₖ` the pocket events at `N`. -/
theorem integral_sq_pocketSum_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hX : IsMeasurableKilledDriving W VL VR ζ) {N : ℕ}
    (hN : IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop N) W VL VR ζ)) {ι : Type*} (s : Finset ι)
    (ψ : ι → TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => WangWu.retainedGreenEnergy (W · ω) N (fun z => ∑ k ∈ s,
        {ω | histPoc N (tsupport (ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
          (fun _ => (1 : ℝ)) ω * ψ k z)) P ∧
    ∫ ω, (∑ k ∈ s, {ω | histPoc N (tsupport (ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
        (fun ω => h ω (ψ k) - (P[fun ω' => h ω' (ψ k) | hN.measurableSpace]) ω) ω) ^ 2 ∂P =
      ∫ ω, WangWu.retainedGreenEnergy (W · ω) N (fun z => ∑ k ∈ s,
        {ω | histPoc N (tsupport (ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
          (fun _ => (1 : ℝ)) ω * ψ k z) ∂P := by
  set E : ι → Set Ω := fun k =>
    {ω | histPoc N (tsupport (ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))} with hEdef
  have hEm : ∀ k, MeasurableSet[hN.measurableSpace] (E k) := fun k => measurableSet_pocketEvent hX hN (ψ k)
  have hNle : hN.measurableSpace ≤ mΩ := hN.measurableSpace_le
  set lamf : ι → Ω → ℝ := fun k ω => (P[fun ω' => h ω' (ψ k) | hN.measurableSpace]) ω with hlamf
  set Sω : Ω → Finset ι := fun ω => s.filter fun k => ω ∈ E k with hS
  set F : Finset ι → Set Ω := fun t => {ω | Sω ω = t} with hF
  have hFm : ∀ t ∈ s.powerset, MeasurableSet[hN.measurableSpace] (F t) := by
    intro t ht
    have ht' : t ⊆ s := Finset.mem_powerset.1 ht
    have e : F t = ⋂ k ∈ s, {ω | (ω ∈ E k ↔ k ∈ t)} := by
      ext ω
      simp only [hF, hS, mem_ofPred_eq, mem_iInter]
      constructor
      · rintro rfl k hk; simp [hk]
      · intro hω
        ext k
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hk, hkE⟩; exact (hω k hk).1 hkE
        · intro hkt; exact ⟨ht' hkt, (hω k (ht' hkt)).2 hkt⟩
    rw [e]
    refine MeasurableSet.biInter s.countable_toSet fun k _ => ?_
    by_cases hkt : k ∈ t
    · simp only [hkt, iff_true, ofPred_mem_eq]; exact hEm k
    · simp only [hkt, iff_false]; exact (hEm k).compl
  have hh2 : ∀ k, MemLp (fun ω => h ω (ψ k)) 2 P := by
    intro k
    obtain ⟨u₀, hu₀⟩ := exists_bhe κ ρL ρR xL xR
    have e : (fun ω => h ω (ψ k)) = fun ω => centredField h u₀ ω (ψ k) + ∫ z, u₀ z * ψ k z := by
      funext ω; rw [centredField_apply h hu₀.1 ω (ψ k)]; ring
    rw [e]
    exact (memLp_centredField hC hu₀ (ψ k)).add (memLp_const _)
  set Y : Ω → ℝ := fun ω => ∑ k ∈ s, (E k).indicator (fun ω => h ω (ψ k) - lamf k ω) ω with hYdef
  have hY2 : MemLp Y 2 P := by
    have e : Y = ∑ k ∈ s, (E k).indicator (fun ω => h ω (ψ k) - lamf k ω) := by
      funext ω; simp only [hYdef, Finset.sum_apply]
    rw [e]
    refine memLp_finsetSum' s fun k _ => ?_
    exact ((hh2 k).sub ((hh2 k).condExp one_le_two)).indicator (hNle _ (hEm k))
  have hYsq : Integrable (fun ω => Y ω ^ 2) P := hY2.integrable_sq
  -- the partition into pocket patterns
  have hpart : ∀ (g : Ω → ℝ) ω, ∑ t ∈ s.powerset, (F t).indicator g ω = g ω := by
    intro g ω
    rw [Finset.sum_eq_single (Sω ω)]
    · rw [indicator_of_mem (show ω ∈ F (Sω ω) from rfl)]
    · intro t _ hne
      exact indicator_of_notMem (fun h' => hne h'.symm) _
    · intro hn
      exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ s)) hn
  have hYF : ∀ t ω, ω ∈ F t → Y ω = ∑ k ∈ t, (h ω (ψ k) - lamf k ω) := by
    intro t ω hω
    have hω' : Sω ω = t := hω
    rw [hYdef]
    simp only
    rw [← hω', hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : ω ∈ E k
    · simp [hk]
    · simp [hk]
  -- each pattern
  have hpat : ∀ t ∈ s.powerset, Integrable ((F t).indicator fun ω =>
        WangWu.retainedGreenEnergy (W · ω) N (∑ k ∈ t, ψ k)) P ∧
      ∫ ω, (F t).indicator (fun ω => Y ω ^ 2) ω ∂P =
        ∫ ω, (F t).indicator (fun ω => WangWu.retainedGreenEnergy (W · ω) N (∑ k ∈ t, ψ k)) ω ∂P := by
    intro t ht
    have hNσ : IsStoppingTime (drivingFiltration P hX) fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0) := hN
    have hms : hNσ.measurableSpace = hN.measurableSpace := rfl
    set Z : Ω → ℝ := fun ω => h ω (∑ k ∈ t, ψ k) with hZdef
    have hZsum : Z = ∑ k ∈ t, fun ω => h ω (ψ k) := by
      funext ω; simp only [hZdef, map_sum, Finset.sum_apply]
    have hZ2 : MemLp Z 2 P := by rw [hZsum]; exact memLp_finsetSum' t fun k _ => hh2 k
    have hZm : Measurable[mΩ] Z := (Sobolev.measurable_distOn_apply _).comp hC.2.1
    have hμ : P[Z | hN.measurableSpace] =ᵐ[P] fun ω => ∑ k ∈ t, lamf k ω := by
      rw [hZsum]
      filter_upwards [condExp_finsetSum (μ := P) (fun k _ => (hh2 k).integrable one_le_two) hN.measurableSpace]
        with ω hω
      rw [hω, Finset.sum_apply]
    have hgood := ae_isGoodPath hC.1 hζ
    have hc : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ F t → (P[fun ω => cexp (I * ((c * Z ω : ℝ) : ℂ)) | hN.measurableSpace]) ω =
        WangWu.gaussCF (c * (P[Z | hN.measurableSpace]) ω) (c ^ 2 *
          WangWu.retainedGreenEnergy (W · ω) N (∑ k ∈ t, ψ k)) := by
      intro c
      have h4 := ae_condExp_exp_eq_cmKer_of_isLabel hC hκ hX ψ t (σ := fun _ => (N : ℝ≥0)) hNσ
        (hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top) (N := (N : ℝ≥0)) (fun _ => le_rfl) c
      rw [hms] at h4
      filter_upwards [h4, hgood, ae_cmKer_smul (P := P) hN.measurableSpace h W (fun _ => (N : ℝ≥0)) c
        (∑ k ∈ t, ψ k)] with ω e4 hg e5 hω
      have hlab : ∀ k ∈ t, IsLabel (W · ω) (tsupport (ψ k)) (N : ℝ≥0) := by
        intro k hk
        have hkE : ω ∈ E k := by
          have hω' : Sω ω = t := hω
          rw [← hω', hS, Finset.mem_filter] at hk
          exact hk.2
        exact (histLab_iff hg N (ψ k).tsupport_subset).1 hkE.1
      have e1 : (fun ω => cexp (I * ((c * Z ω : ℝ) : ℂ))) =
          fun ω' => cexp (I * (h ω' (c • ∑ k ∈ t, ψ k) : ℂ)) := (exp_pairing_smul h c _).symm
      rw [e1]
      refine (e4 hlab).trans ?_
      rw [e5, WangWu.gaussCF]
      congr 1
      push_cast
      ring
    obtain ⟨hint, heq⟩ := integral_indicator_sq_sub_condExp_eq hNle (hFm t ht) hZ2 hZm hc
    refine ⟨hint, ?_⟩
    rw [← heq]
    refine integral_congr_ae ?_
    filter_upwards [hμ] with ω hω
    by_cases hωF : ω ∈ F t
    · rw [indicator_of_mem hωF, indicator_of_mem hωF, hYF t ω hωF, hω, Finset.sum_sub_distrib]
      simp only [hZdef, map_sum]
    · rw [indicator_of_notMem hωF, indicator_of_notMem hωF]
  -- sum over the patterns
  have hRGE : (fun ω => WangWu.retainedGreenEnergy (W · ω) N (fun z => ∑ k ∈ s,
      {ω | histPoc N (tsupport (ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
        (fun _ => (1 : ℝ)) ω * ψ k z)) = fun ω => ∑ t ∈ s.powerset, (F t).indicator
          (fun ω => WangWu.retainedGreenEnergy (W · ω) N (∑ k ∈ t, ψ k)) ω := by
    funext ω
    rw [Finset.sum_eq_single (Sω ω)]
    · rw [indicator_of_mem (show ω ∈ F (Sω ω) from rfl)]
      congr 1
      funext z
      rw [Finset.sum_apply, hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : ω ∈ E k
      · have hk' : histPoc N (tsupport ⇑(ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) := hk
        simp [Set.indicator, hk, hk']
      · have hk' : ¬ histPoc N (tsupport ⇑(ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) := hk
        simp [Set.indicator, hk, hk']
    · intro t _ hne
      exact indicator_of_notMem (fun h' => hne h'.symm) _
    · intro hn
      exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ s)) hn
  refine ⟨by rw [hRGE]; exact integrable_finsetSum _ fun t ht => (hpat t ht).1, ?_⟩
  calc ∫ ω, (∑ k ∈ s, (E k).indicator (fun ω => h ω (ψ k) - lamf k ω) ω) ^ 2 ∂P
      = ∫ ω, ∑ t ∈ s.powerset, (F t).indicator (fun ω => Y ω ^ 2) ω ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp only
        rw [hpart (fun ω => Y ω ^ 2) ω]
    _ = ∑ t ∈ s.powerset, ∫ ω, (F t).indicator (fun ω => Y ω ^ 2) ω ∂P :=
        integral_finsetSum _ fun t ht => hYsq.indicator (hNle _ (hFm t ht))
    _ = ∑ t ∈ s.powerset, ∫ ω, (F t).indicator
          (fun ω => WangWu.retainedGreenEnergy (W · ω) N (∑ k ∈ t, ψ k)) ω ∂P :=
        Finset.sum_congr rfl fun t ht => (hpat t ht).2
    _ = ∫ ω, ∑ t ∈ s.powerset, (F t).indicator
          (fun ω => WangWu.retainedGreenEnergy (W · ω) N (∑ k ∈ t, ψ k)) ω ∂P :=
        (integral_finsetSum _ fun t ht => (hpat t ht).1).symm
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp only
        rw [Finset.sum_eq_single (Sω ω)]
        · rw [indicator_of_mem (show ω ∈ F (Sω ω) from rfl)]
          congr 1
          funext z
          rw [Finset.sum_apply, hS, Finset.sum_filter]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hk : ω ∈ E k
          · have hk' : histPoc N (tsupport ⇑(ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) := hk
            simp [Set.indicator, hk, hk']
          · have hk' : ¬ histPoc N (tsupport ⇑(ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) := hk
            simp [Set.indicator, hk, hk']
        · intro t _ hne
          exact indicator_of_notMem (fun h' => hne h'.symm) _
        · intro hn
          exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ s)) hn

end Coupling

end Aux50Ge8

end InteractingSLE
