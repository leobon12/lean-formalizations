/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50HitBirth

/-!
# Aux. lemma 50 for the two-seed words, every `0 < κ < 8`: the common kernel at the integer times

Packet PROVE-AUX50B. Specification Aux. lemma 50 (`source/spec/p193-240.md` L816ff., pp. 236–242: "Then the conditional
law of the entire field given its recorded driving history through `t ∧ S` is Gaussian […] Before comparing two
couplings, fix common measurable versions […] the same functions apply in every coupling with that marginal") and
Aux. lemma 51 (p. 242: "every coupling with the original outside-filled-hull specification has the same full
field–history joint law through `S`"), along the route of the follow-up note Part C (ruling R38): (WF2) at the integer
times, with the ambient extension across the trace by the Sobolev removability of Aux. lemma 23 (the core
`Sec4.map_prod_eq_of_condCharFun_off_ae`) instead of the square-average reconstruction.

1. **The kernel off the trace is a Borel function of the history** (`ae_condExp_exp_eq_kerFun`): for a coupling with
   infinite lifetime, at the integer time `N`, for every test `φ` whose support misses the set `labA` off the labelled
   rational balls, `E[e^{i(h, φ)} | 𝓕_N] = kerFun(history through N)(φ)`. This is C.4 (`WholeField.
   ae_condExp_exp_eq_cmKer_of_isLabel`, every `κ > 0`) on the pieces of a fine partition of unity of `φ`, with the
   conditional means of the pieces identified by the Borel label means (`ae_labelMean_eq_condExp`) and the retained
   Green energy by `histQ`.
2. **Thinness** (`ae_dimH_labA_inter_lt`): along a continuous trace, `labA` lies in the trace, of dimension at most
   `d_κ < 2` for `κ < 8` (Aux. lemma 15, `IsIntegratedSLEEvolution.ae_dimH_image_inter_H_le`).
3. **Aux. lemma 51 at the integer times** (`map_stopHistory_prod_eq_of_lt_eight`, `traceStopLawUnique_of_lt_eight`):
   the Sobolev core of Aux. lemma 23 with this kernel, the random set `labA` and Theorem 2.2's uniqueness of the stopped
   history law.
4. **The named input `Aux50.HasTraceStopKernel` for every `0 < κ < 8`** (`hasTraceStopKernel_of_lt_eight`), hence
   **`Prop73Det.Prop73FieldKernelStatement`** (proved, `prop73FieldKernelStatement`) and `R7.R7FieldKernelStatement`
   from its `κ ≥ 8` part alone (`r7FieldKernelStatement_of_geEight`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal Classical

universe u v

namespace InteractingSLE

namespace Aux50Hit

open LawUnique Sec4 QuantumZipper LQGMetric WholeField

variable {nL nR : ℕ}

/-! ### The kernel off the trace -/

section Kernel

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **(WF2) at the integer time `N`, off the trace, as a Borel function of the history.** For a coupling with the
frozen optional hull specification and infinite lifetime, for every test `φ`: almost surely, if `supp φ` misses the
set `labA` off the labelled rational balls of the history through `N`, then
`E[e^{i(h, φ)} | 𝓕_N] = kerFun (histG …) N φ (history through N)`. -/
theorem ae_condExp_exp_eq_kerFun (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hX : IsMeasurableKilledDriving W VL VR ζ) (N : ℕ)
    (hN : IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop N) W VL VR ζ))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (labA N (stopHistory (natStop N) (killedHistory W VL VR ζ ω))) →
      P[fun o => Complex.exp (↑(h o φ) * Complex.I) | hN.measurableSpace] ω =
        kerFun (histG κ ρL ρR) N φ (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) := by
  have hgood := ae_isGoodPath hC.1 hζ
  set R : ℝ := testRad φ with hRdef
  have hsum : ∀ n : ℕ, ∑ k ∈ WangWu.pouIdx (WangWu.scaleIdx R n), WangWu.pouTest φ n k = φ := fun n =>
    WangWu.sum_pouTest (tsupport_subset_testRad φ) (WangWu.le_scaleIdx R n)
  have hσζ : ∀ᵐ ω ∂P, (((fun _ : Ω => (N : ℝ≥0)) ω : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top
  -- C.4 on the pieces at each scale
  have hC4 : ∀ n : ℕ, ∀ᵐ ω ∂P, (∀ k ∈ WangWu.pouIdx (WangWu.scaleIdx R n),
      IsLabel (W · ω) (tsupport (WangWu.pouTest φ n k)) N) →
      (P[fun ω' => cexp (Complex.I * (h ω' φ : ℂ)) | hN.measurableSpace]) ω =
        cmKer P hN.measurableSpace h W N φ ω := fun n => by
    have := ae_condExp_exp_eq_cmKer_of_isLabel (σ := fun _ => (N : ℝ≥0)) hC hκ hX
      (fun k => WangWu.pouTest φ n k) (WangWu.pouIdx (WangWu.scaleIdx R n)) hN hσζ (N := (N : ℝ≥0))
      (fun _ => le_rfl) 1
    simp only [hsum n, one_smul] at this
    exact this
  -- linearity of the conditional means at each scale
  have hlin : ∀ n : ℕ, P[fun ω' => h ω' φ | hN.measurableSpace] =ᵐ[P]
      fun ω => ∑ k ∈ WangWu.pouIdx (WangWu.scaleIdx R n),
        (P[fun ω' => h ω' (WangWu.pouTest φ n k) | hN.measurableSpace]) ω := fun n => by
    have e : (fun ω' => h ω' φ) =
        ∑ k ∈ WangWu.pouIdx (WangWu.scaleIdx R n), fun ω' => h ω' (WangWu.pouTest φ n k) := by
      funext ω'
      rw [Finset.sum_apply]
      conv_lhs => rw [← hsum n]
      rw [map_sum]
    rw [e]
    refine (condExp_finsetSum (fun k _ => integrable_pairing hC _) _).trans ?_
    exact Eventually.of_forall fun ω => by rw [Finset.sum_apply]
  -- the label means
  have hlab : ∀ (n : ℕ) (k : ℤ × ℤ), ∀ᵐ ω ∂P, IsLabel (W · ω) (tsupport (WangWu.pouTest φ n k)) N →
      labelMean (histG κ ρL ρR) N (WangWu.pouTest φ n k) (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) =
        (P[fun ω' => h ω' (WangWu.pouTest φ n k) | hN.measurableSpace]) ω := fun n k =>
    ae_labelMean_eq_condExp hC hκ hζ hX N hN _
  filter_upwards [ae_all_iff.2 hC4, ae_all_iff.2 hlin, ae_all_iff.2 fun n => ae_all_iff.2 (hlab n), hgood]
    with ω h1 h2 h3 hg hd
  -- the labelled balls of the history are labels of the driver
  have hG : ∀ q, ω ∈ {ω' : Ω | stopHistory (natStop N) (killedHistory W VL VR ζ ω') ∈ ballLab N q} →
      IsLabel (W · ω) (closedBall (qCentre q) (qRad q)) N := fun q hq =>
    (histLab_iff hg N hq.1.2).1 hq.2
  obtain ⟨n₀, hn₀⟩ := exists_scale_isLabel (t := (N : ℝ≥0))
    (G := fun q => {ω' : Ω | stopHistory (natStop N) (killedHistory W VL VR ζ ω') ∈ ballLab N q}) hG φ hd
  -- the total mean is the conditional mean
  have htot : totMean (histG κ ρL ρR) N φ (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) =
      (P[fun ω' => h ω' φ | hN.measurableSpace]) ω := by
    unfold totMean
    have hev : ∀ᶠ n in atTop, ∑ k ∈ WangWu.pouIdx (WangWu.scaleIdx (testRad φ) n),
        labelMean (histG κ ρL ρR) N (WangWu.pouTest φ n k)
          (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) =
        (P[fun ω' => h ω' φ | hN.measurableSpace]) ω := by
      filter_upwards [eventually_ge_atTop n₀] with n hn
      rw [h2 n]
      exact Finset.sum_congr rfl fun k _ => h3 n k (hn₀ n hn k)
    exact (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)).limsup_eq
  have e : (fun o => Complex.exp (↑(h o φ) * Complex.I)) = fun ω' => cexp (Complex.I * (h ω' φ : ℂ)) := by
    funext o; rw [mul_comm]
  rw [e, h1 n₀ fun k _ => hn₀ n₀ le_rfl k, kerFun, htot, histQ_eq hg N φ]
  rfl

end Kernel

/-! ### Thinness of the set off the labels -/

section Thin

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The set off the labels is thin** (Aux. lemma 15): for `0 < κ < 8`, along a continuous trace and with infinite
lifetime, `labA` of the history through `N` lies in the trace, whose interior dimension is at most `d_κ`. -/
theorem ae_dimH_labA_inter_le (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (hκ8 : κ < 8) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) (N : ℕ) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, dimH (labA N (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) ∩ K) ≤
      ENNReal.ofReal (Dimension.interiorDimBound κ) := by
  filter_upwards [htr, hE.ae_dimH_image_inter_H_le hκ hκ8, ae_isGoodPath hE hζ] with ω ⟨η, hη⟩ hdim hg K
  have hG : ∀ q, IsGoodBall q → IsLabel (W · ω) (closedBall (qCentre q) (qRad q)) N →
      ω ∈ {ω' : Ω | stopHistory (natStop N) (killedHistory W VL VR ζ ω') ∈ ballLab N q} := fun q hq hl =>
    ⟨hq, (histLab_iff hg N hq.2).2 hl⟩
  have hlt : ((N : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hg.1]; exact ENNReal.coe_lt_top
  have hsub := offLabels_subset_image hg.2.2.1 hη hlt hG
  have hS : Icc 0 (N : ℝ≥0) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ ω} := fun t _ => by
    show (t : ℝ≥0∞) ≤ ζ ω
    rw [hg.1]; exact le_top
  refine (dimH_mono fun z hz => ?_).trans (hdim η hη _ hS)
  exact ⟨hsub hz.1, labA_subset_H N _ hz.1⟩

end Thin

/-! ### Aux. lemma 51 at the integer times -/

section Law

variable {κ rL rR : ℝ}

/-- The integer stop `n` is a stopping time of every driving filtration. -/
theorem isStoppingTime_natStop {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR ζ) (n : ℕ) :
    IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop n) W VL VR ζ) := by
  show IsStoppingTime _ fun _ => ((n : ℝ≥0) : WithTop ℝ≥0)
  exact isStoppingTime_const _ _

/-- **Aux. lemma 51 at the integer times, for every `0 < κ < 8`.** Two couplings of the two-seed word
`SLE_κ(rL; rR)` (`rL, rR > −2`) with the frozen optional hull specification, the first of whose drivers has a continuous
generating trace, have the same joint law of the history stopped at `N` and the whole field. -/
theorem map_stopHistory_prod_eq_of_lt_eight (hκ : 0 < κ) (hκ8 : κ < 8) (hL : -2 < rL) (hR : -2 < rR) (N : ℕ)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ}
    {ζ₁ : Ω₁ → ℝ≥0∞} {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (htr₁ : ∀ᵐ ω ∂P₁, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) η)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    P₁.map (fun ω => (stopHistory (natStop N) (killedHistory W₁ VL₁ VR₁ ζ₁ ω), h₁ ω)) =
      P₂.map (fun ω => (stopHistory (natStop N) (killedHistory W₂ VL₂ VR₂ ζ₂ ω), h₂ ω)) := by
  set d : ℝ := Dimension.interiorDimBound κ with hddef
  have hd : d < 2 := Dimension.interiorDimBound_lt_two hκ8
  set ε : ℝ := min (1 / 2) ((2 - d) / 4) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hdε : d < 2 - 2 * ε := by
    have := min_le_right (1 / 2 : ℝ) ((2 - d) / 4)
    linarith
  obtain ⟨hX₁, -⟩ := hC₁.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hζ₁ := R7.ae_lifetime_eq_top hκ hL hR hC₁.1
  have hζ₂ := R7.ae_lifetime_eq_top hκ hL hR hC₂.1
  have hN₁ := isStoppingTime_natStop (P := P₁) hX₁ N
  have hN₂ := isStoppingTime_natStop (P := P₂) hX₂ N
  have hst : Measurable (stopHistory (nL := 1) (nR := 1) (natStop N)) :=
    measurable_stopHistory (measurable_natStop N)
  refine map_prod_eq_of_condCharFun_off_ae (U := upperHalfPlaneOpens) hε0 hε1 (closure_labA_inter_subset N)
    (fun K hK => measurableSet_disjoint_labA N hK) (measurable_kerFun (measurable_histG κ _ _) N)
    hC₁.2.1 (hst.comp (measurable_killedHistory hX₁))
    (measurable_stopHistory_killedHistory hX₁ hN₁).comap_le hN₁.measurableSpace_le
    (fun ζc => hC₁.lintegral_negSobolevSq_lt_top hε0 ζc)
    (fun φ => ae_condExp_exp_eq_kerFun hC₁ hκ hζ₁ hX₁ N hN₁ φ)
    hC₂.2.1 (hst.comp (measurable_killedHistory hX₂))
    (measurable_stopHistory_killedHistory hX₂ hN₂).comap_le hN₂.measurableSpace_le
    (fun ζc => hC₂.lintegral_negSobolevSq_lt_top hε0 ζc)
    (fun φ => ae_condExp_exp_eq_kerFun hC₂ hκ hζ₂ hX₂ N hN₂ φ)
    (map_stopHistory_eq (killedStateLawUnique_of_isOrderedForceWord hκ _ _ LP.isOrderedForceWord_twoSeed)
      (measurable_natStop N) hC₁.1 hX₁ hC₂.1 hX₂) ?_
  filter_upwards [ae_dimH_labA_inter_le hC₁.1 hκ hκ8 hζ₁ htr₁ N] with ω hω K _ _
  refine (hω K).trans_lt ?_
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hdε

/-- **Aux. lemma 51 at the integer times for every `0 < κ < 8`** (`Aux50.TraceStopLawUnique`). -/
theorem traceStopLawUnique_of_lt_eight (hκ : 0 < κ) (hκ8 : κ < 8) (hL : -2 < rL) (hR : -2 < rR) :
    Aux50.TraceStopLawUnique.{u, v} κ rL rR := by
  intro Ω₁ m₁ P₁ _ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁ hC₁ htr₁ Ω₂ m₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ _ n
  have hlaw := map_stopHistory_prod_eq_of_lt_eight hκ hκ8 hL hR n hC₁ htr₁ hC₂
  have hst : Measurable (stopHistory (nL := 1) (nR := 1) (natStop n)) :=
    measurable_stopHistory (measurable_natStop n)
  have hm₁ : Measurable fun ω => (stopHistory (natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω), h₁ ω) :=
    (hst.comp (measurable_killedHistory hC₁.2.2.2.1)).prodMk hC₁.2.1
  have hm₂ : Measurable fun ω => (stopHistory (natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω), h₂ ω) :=
    (hst.comp (measurable_killedHistory hC₂.2.2.2.1)).prodMk hC₂.2.1
  have e₁ : (fun ω => (h₁ ω, stopHistory (natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
      Prod.swap ∘ fun ω => (stopHistory (natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω), h₁ ω) := rfl
  have e₂ : (fun ω => (h₂ ω, stopHistory (natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) =
      Prod.swap ∘ fun ω => (stopHistory (natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω), h₂ ω) := rfl
  rw [e₁, e₂, ← Measure.map_map measurable_swap hm₁, ← Measure.map_map measurable_swap hm₂, hlaw]

/-- **The named input of PROVE-PROP73R, proved for every `0 < κ < 8`**: Aux. lemma 50's common kernel at the integer
times (`Aux50.HasTraceStopKernel`) for every two-seed word with seed weights `rL, rR > −2`. -/
theorem hasTraceStopKernel_of_lt_eight (hκ : 0 < κ) (hκ8 : κ < 8) (hL : -2 < rL) (hR : -2 < rR) :
    Aux50.HasTraceStopKernel.{u, v} κ rL rR :=
  Aux50.hasTraceStopKernel_of_traceStopLawUnique (traceStopLawUnique_of_lt_eight hκ hκ8 hL hR)
    (traceStopLawUnique_of_lt_eight hκ hκ8 hL hR) (traceStopLawUnique_of_lt_eight hκ hκ8 hL hR)

end Law

/-! ### The two uses -/

/-- **Aux. lemma 50 for the boundary-hitting two-seed words, `0 < κ < 4`** (`Prop73Det.Prop73FieldKernelStatement`,
Proposition 7.3's kernel input): **proved**. -/
theorem prop73FieldKernelStatement : Prop73Det.Prop73FieldKernelStatement.{u} :=
  Aux50.prop73FieldKernelStatement_of_aux50 fun _ hκ hκ4 _ _ hL hR _ =>
    hasTraceStopKernel_of_lt_eight hκ (by linarith) hL hR

/-- **Named input: Aux. lemma 50 for the R.7 two-seed words at `κ ≥ 8`** (the part of `R7.R7FieldKernelStatement` not
covered by `hasTraceStopKernel_of_lt_eight`: for `κ ≥ 8` the trace has positive area, so the Sobolev removability of
Aux. lemma 23 does not apply; the specification's covariance-exhaustion argument (HGV1)–(HGV12) is needed). -/
def R7KernelGeEightStatement : Prop :=
  ∀ κ : ℝ, 8 ≤ κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR → Aux50.HasTraceStopKernel.{u, v} κ rL rR

/-- **Theorem R.7's field kernel** (`R7.R7FieldKernelStatement`) from its `κ ≥ 8` part alone (`4 < κ < 8`: proved). -/
theorem r7FieldKernelStatement_of_geEight (h8 : R7KernelGeEightStatement.{u, v}) : R7.R7FieldKernelStatement.{u, v} :=
  Aux50.r7FieldKernelStatement_of_aux50 fun κ hκ rL rR hL hR hmax => by
    rcases lt_or_ge κ 8 with hκ8 | hκ8
    · exact hasTraceStopKernel_of_lt_eight (by linarith) hκ8 hL hR
    · exact h8 κ hκ8 rL rR hL hR hmax

/-- **Proposition 7.3's determination** (`Determination.Prop73DeterminationStatement`) from the embedded reference and
the trace part only (the kernel input is proved). -/
theorem prop73DeterminationStatement_of_reference (h73t : Sec7.Prop73TraceStatement.{u})
    (href : Prop73Det.Prop73ReferenceStatement.{u}) : Determination.Prop73DeterminationStatement.{u} :=
  Prop73Det.prop73DeterminationStatement_of_reference h73t href prop73FieldKernelStatement

/-- **Theorem R.7's determination consequence** (`LP.R7DeterminationStatement`) from the R.7 reference and the `κ ≥ 8`
part of Aux. lemma 50 for the R.7 pairs. -/
theorem r7DeterminationStatement_of_geEight (href : R7.R7ReferenceStatement.{v})
    (h8 : R7KernelGeEightStatement.{v, u}) : LP.R7DeterminationStatement.{u} :=
  R7.r7DeterminationStatement_of_inputs href (r7FieldKernelStatement_of_geEight h8)

end Aux50Hit

end InteractingSLE
