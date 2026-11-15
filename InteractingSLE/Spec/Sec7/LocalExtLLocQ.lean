/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtLRef
import InteractingSLE.Spec.Coupling.ResampleProjCore
import InteractingSLE.Spec.Coupling.WholeField2Hull

/-!
# Aux. lemma 54, (Loc) before the stop: the stopped coupling's projection identity on history events

Packet PROVE-LOCEXT-L. For a stopped seed coupling `(Q, h)` through `S`, rational times `t₁ < t₂`, a Borel set `Γ` of
histories, a compact `C ⊆ ℍ` and an open `U ⊆ C`, on the history event

`A = {t₁ < S, truncH t₁ Y ∈ Γ, C ∩ K_{t₂ ∧ S} = ∅}`

the centred field `X = h − 𝔥₀` satisfies the projection identity of `Coupling.IsFamilyLocal`:

`∫_A e^{i X(−Δf/2π + Ξ)} dQ = projFactor U f Ξ · ∫_A e^{i X(Ξ)} dQ`    (`f ∈ C_c^∞(U)`, `Ξ` any test function).

Proof (a coding stop; no history-marked germ theory). Put `τ' = t₂ ∧ S`, `F₀ = {t₁ < S, truncH t₁ Y ∈ Γ} ∈ 𝓓_{t₁}`, and
`τ'' = t₁` on `G = F₀ᶜ ∩ {t₁ < τ'}`, `τ''= τ'` off `G` (a `𝓓`-stopping time `≤ S`). By clause (e) the hull `K_{τ''}` is a
local set of `X`. Its capacity clock is `t₁` on `G` and `τ'` off `G`, so `F₀ ∩ {V ∩ K_{τ'} = ∅}` is the recorded event
`{clock(K_{τ''}) > t₁, V ∩ K_{τ''} = ∅}` of the local set `K_{τ''}`. For such events the projection identity at `V` holds
(`LocalSets.exists_const_integral_exp_lapTest`), hence at `U ⊆ V` (the Gram data of `C_c^∞(U)` do not depend on `V`).
Letting the open neighbourhoods `V_m` of `C` shrink to `C` gives the identity on `A`.

## Main results

* `measurableSet_trunc_stopping`: the truncated-history events are events of `𝓓_t`;
* **`IsStoppedSeedCoupling.setIntegral_lapTest_pre`**: the projection identity above.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper Metric TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric LQGMetric.MarkovZB Coupling LocalSets GFF QuantumZipper.K3 QuantumZipper.Thm11Asm
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-! ### Small facts -/

theorem lapTest_zero {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) : lapTest U (0 : zsSub (U : Set ℂ)) = 0 := by
  ext z
  rw [coe_lapTest hU]
  have : (0 : ℂ → ℝ) = fun _ => (0 : ℝ) := rfl
  simp [cmTest, zsTest, this]

theorem gradFeat_zsSub_zero (U : Opens ℂ) :
    QuantumZipper.K3.gradFeat (U : Set ℂ) ((0 : zsSub (U : Set ℂ)) : ℂ → ℝ) = 0 := by
  simpa using QuantumZipper.K3.gradFeat_zero (QuantumZipper.K3.isDNSpace_zeroSpace (U : Set ℂ))

/-- **The projection identity on the avoidance events of a local set, with a recorded weight.** For a local set `A` of
`X`, an open `V ⊆ ℍ`, an open `U ⊆ V` and a bounded hitting-measurable weight `k`,
`∫ 1_{A∩V=∅} k(A) e^{iX(−Δf/2π + Ξ)} = projFactor U f Ξ · ∫ 1_{A∩V=∅} k(A) e^{iX(Ξ)}`. -/
theorem integral_indicator_lapTest_eq {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {A : Ω → Set ℂ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hloc : IsLocalSet A X P) {V : Opens ℂ}
    (hV : V ≤ upperHalfPlaneOpens) {U : Opens ℂ} (hUV : U ≤ V) {k : Set ℂ → ℂ}
    (hk : Measurable[hittingSigma] k) (hkb : ∀ S, ‖k S‖ ≤ 1) (f : zsSub (U : Set ℂ))
    (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω, {ω | Disjoint (A ω) V}.indicator (fun ω => k (A ω)) ω *
        Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω, {ω | Disjoint (A ω) V}.indicator (fun ω => k (A ω)) ω *
        Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P := by
  obtain ⟨J, hJ⟩ := exists_const_integral_exp_lapTest hloc hV hk hkb Ξ
  have hUV' : (U : Set ℂ) ⊆ V := hUV
  have hVH : (V : Set ℂ) ⊆ H := hV
  set f' : zsSub (V : Set ℂ) := zsSubIncl hUV' f with hf'
  have hL : lapTest V f' = lapTest U f := by
    ext z
    rw [coe_lapTest hV, coe_lapTest (show U ≤ upperHalfPlaneOpens from fun z hz => hVH (hUV hz))]
    rfl
  have h1 := hJ f' 0
  have h0 := hJ 0 0
  rw [lapTest_zero hV, sub_zero, hL] at h1
  rw [sub_self, zero_add, gradFeat_zsSub_zero, sub_self, norm_zero] at h0
  simp only [inner_zero_left, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Real.exp_zero, Complex.ofReal_one, one_mul] at h0
  have hf1 : (f' : ℂ → ℝ) = f.1 := rfl
  have hc : Coupling.projFactor V f' Ξ = Coupling.projFactor U f Ξ := by
    rw [Coupling.projFactor, Coupling.projFactor, hf1, norm_gradFeat_eq hUV' f.2,
      inner_gradFeat_covVec_eq U.isOpen V.isOpen hVH hUV' f.2]
  rw [h1, ← h0, gradFeat_zsSub_zero, sub_zero, ← hc]
  congr 1
  rw [Coupling.projFactor, ← Complex.ofReal_exp]
  congr 2
  ring

/-! ### Shrinking neighbourhoods of a compact set -/

section Nbhd

/-- **A compact set avoiding the relative closure of `K` in `ℍ` has a neighbourhood avoiding `K`**, eventually along the
thickenings `C^{δ/(m+1)}`; if it meets that closure, every thickening meets `K`. -/
theorem eventually_disjoint_thickening_iff {C K : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) {δ : ℝ} (hδ : 0 < δ) :
    (Disjoint C (closure K ∩ H) → ∀ᶠ m : ℕ in atTop, Disjoint K (thickening (δ / ((m : ℝ) + 1)) C)) ∧
      (¬ Disjoint C (closure K ∩ H) → ∀ m : ℕ, ¬ Disjoint K (thickening (δ / ((m : ℝ) + 1)) C)) := by
  constructor
  · intro hd
    have hdc : Disjoint C (closure K) := by
      rw [Set.disjoint_left]
      intro z hzC hzK
      exact Set.disjoint_left.1 hd hzC ⟨hzK, hCH hzC⟩
    obtain ⟨ε, hε, hεC⟩ := hC.exists_thickening_subset_open isClosed_closure.isOpen_compl
      (fun z hz => Set.disjoint_left.1 hdc hz)
    have hlim : Tendsto (fun m : ℕ => δ / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with m hm
    refine Set.disjoint_right.2 fun z hz hzK => ?_
    exact hεC (thickening_mono hm.le C hz) (subset_closure hzK)
  · intro hnd m hdis
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨z, hzC, hzK, -⟩ := hnd
    have hpos : 0 < δ / ((m : ℝ) + 1) := by positivity
    have hzV : z ∈ thickening (δ / ((m : ℝ) + 1)) C := self_subset_thickening hpos C hzC
    obtain ⟨y, hyV, hyK⟩ := mem_closure_iff.1 hzK _ isOpen_thickening hzV
    exact Set.disjoint_left.1 hdis hyK hyV

end Nbhd

/-! ### The projection identity on history events before the stop -/

/-- The hull read from a truncated history of a continuous stopped state. -/
theorem tsHull_truncH_tsOf {S₀ : ℝ≥0} {X : ℝ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)} (hX : ContinuousOn X (Iic S₀))
    {w : ℝ≥0 → ℝ} {a : ℝ≥0∞} (hSa : (S₀ : ℝ≥0∞) < a) (hw : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < a})
    (hwX : ∀ t ≤ S₀, (X t).1 = w t) (t₂ : ℚ≥0) :
    tsHull (truncH t₂ (tsOf S₀ X)) =
      closure (fwdHull (fun r : ℝ => w r.toNNReal) (min S₀ (t₂ : ℝ≥0))) ∩ (upperHalfPlaneOpens : Set ℂ) := by
  rw [truncH_tsOf]
  have hle : min S₀ (t₂ : ℝ≥0) ≤ S₀ := min_le_left _ _
  exact tsHull_tsOf_eq (hX.mono (Iic_subset_Iic.2 hle)) (lt_of_le_of_lt (by exact_mod_cast hle) hSa) hw
    fun t ht => hwX t (ht.trans hle)


/-- **The pre-stop history events**: the stop is after `t₁`, the history truncated at `t₁` lies in `Γ`, and the hull
truncated at `t₂` avoids `C`. -/
def preHistSet (t₁ t₂ : ℚ≥0) (Γ : Set TwoSeedHist) (C : Set ℂ) : Set TwoSeedHist :=
  {y | ((t₁ : ℝ≥0) : WithTop ℝ≥0) < y.1 ∧ truncH t₁ y ∈ Γ ∧ Disjoint C (tsHull (truncH t₂ y))}

theorem measurableSet_preHistSet (t₁ t₂ : ℚ≥0) {Γ : Set TwoSeedHist} (hΓ : MeasurableSet Γ) {C : Set ℂ}
    (hC : IsCompact C) : MeasurableSet (preHistSet t₁ t₂ Γ C) :=
  (measurableSet_lt measurable_const measurable_fst).inter (((measurable_truncH t₁) hΓ).inter
    ((measurable_truncH t₂) (measurableSet_disjoint_tsHull hC)))

section Pre

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- The truncated-history events of a stopped coupling are events of `𝓓_t`. -/
theorem measurableSet_trunc_stopping {𝓓 : Filtration ℝ≥0 mΩ} (hS : IsStoppingTime 𝓓 S)
    (hWa : AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) W) (hVLa : ∀ i, AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) (VL i))
    (hVRa : ∀ j, AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) (VR j)) (t : ℚ≥0) {D : Set TwoSeedHist}
    (hD : MeasurableSet D) :
    MeasurableSet[𝓓 (t : ℝ≥0)] {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < S ω ∧ truncH t (stRaw xL xR W VL VR S ω) ∈ D} := by
  have hAeq : {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < S ω ∧ truncH t (stRaw xL xR W VL VR S ω) ∈ D} =
      {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < S ω} ∩
        killedTrunc (stMerge xL xR) (fun ω => (S ω : ℝ≥0∞)) W VL VR t ⁻¹' D := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    refine and_congr_right fun htS => ?_
    rw [killedTrunc_eq (show ((t : ℝ≥0) : ℝ≥0∞) < (S ω : ℝ≥0∞) from htS), stRaw,
      truncH_twoSeedProj_stoppedHistory htS]
    rfl
  rw [hAeq]
  exact (measurableSet_lt_stop hS _).inter (measurable_killedTrunc (measurable_stMerge xL xR) hWa hVLa hVRa t hD)

/-- The pre-stop marks: the stop is after `t₁` and the history truncated at `t₁` lies in `Γ`. -/
def preMarkSet (t₁ : ℚ≥0) (Γ : Set TwoSeedHist) : Set TwoSeedHist :=
  {y | ((t₁ : ℝ≥0) : WithTop ℝ≥0) < y.1 ∧ truncH t₁ y ∈ Γ}

/-- **The coding stop.** For a stopped seed coupling and rationals `t₁ < t₂`, some local set `A` of the centred field
has, almost surely, capacity clock beyond `t₁` exactly on the marks `{t₁ < S, truncH t₁ Y ∈ Γ}`, and on the marks its
relative closure in `ℍ` is the hull read from the history truncated at `t₂`. (`A = K_{τ''}`, `τ'' = t₁` on
`G = F₀ᶜ ∩ {t₁ < t₂ ∧ S}`, `τ'' = t₂ ∧ S` off `G`.) -/
theorem IsStoppedSeedCoupling.exists_codedHull [IsProbabilityMeasure Q] (hr : 0 < r)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) {T₀ : DistOn upperHalfPlaneOpens}
    (hT₀ : IsHarmonicDistOn T₀ H) {t₁ t₂ : ℚ≥0} (ht : t₁ < t₂) {Γ : Set TwoSeedHist} (hΓ : MeasurableSet Γ) :
    ∃ A : Ω → Set ℂ, IsLocalSet A (fun ω => h ω - T₀) Q ∧ ∀ᵐ ω ∂Q,
      (((t₁ : ℝ≥0) : ℝ≥0∞) < WholeField.hullClock (A ω) ↔ stRecHist xL xR W VL VR S ω ∈ preMarkSet t₁ Γ) ∧
      (stRecHist xL xR W VL VR S ω ∈ preMarkSet t₁ Γ →
        tsHull (truncH t₂ (stRecHist xL xR W VL VR S ω)) = closure (A ω) ∩ (upperHalfPlaneOpens : Set ℂ)) := by
  classical
  have hreg := hc.ae_isRegularStop hr
  have hraw := hc.ae_stRecHist_eq hr
  obtain ⟨𝓓, hS, ⟨Q', 𝓕, B, -, hQQ', -, -, hEv, -⟩, hb, hWa, hVLa, hVRa, -, -, he⟩ := id hc
  have hW0 : ∀ᵐ ω ∂Q, W 0 ω = 0 := by
    filter_upwards [hQQ'.ae_le hEv.ae_path] with ω hp
    exact hp.w_zero
  have hF₀ : MeasurableSet[𝓓 (t₁ : ℝ≥0)]
      {ω | ((t₁ : ℝ≥0) : WithTop ℝ≥0) < S ω ∧ truncH t₁ (stRaw xL xR W VL VR S ω) ∈ Γ} :=
    measurableSet_trunc_stopping hS hWa hVLa hVRa t₁ hΓ
  have hτ' : IsStoppingTime 𝓓 fun ω => min ((t₂ : ℝ≥0) : WithTop ℝ≥0) (S ω) := (isStoppingTime_const 𝓓 _).min hS
  have hτ₁ : IsStoppingTime 𝓓 fun ω => min ((t₁ : ℝ≥0) : WithTop ℝ≥0) (min ((t₂ : ℝ≥0) : WithTop ℝ≥0) (S ω)) :=
    (isStoppingTime_const 𝓓 _).min hτ'
  have ht12 : ((t₁ : ℝ≥0) : WithTop ℝ≥0) < ((t₂ : ℝ≥0) : WithTop ℝ≥0) := by exact_mod_cast ht
  have hlt_iff : ∀ ω, ((t₁ : ℝ≥0) : WithTop ℝ≥0) < min ((t₂ : ℝ≥0) : WithTop ℝ≥0) (S ω) ↔
      ((t₁ : ℝ≥0) : WithTop ℝ≥0) < S ω := fun ω => by
    simp only [lt_min_iff, ht12, true_and]
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ((t₁ : ℝ≥0) : WithTop ℝ≥0) < S ω ∧
      truncH t₁ (stRaw xL xR W VL VR S ω) ∈ Γ}ᶜ ∩ {ω | ((t₁ : ℝ≥0) : WithTop ℝ≥0) < S ω} := ⟨_, rfl⟩
  have hGm : MeasurableSet[hτ₁.measurableSpace] G := by
    rw [hGdef]
    refine measurableSet_stopping_min_of_subset_lt (hF₀.compl.inter (measurableSet_lt_stop hS _))
      (fun ω hω => (hlt_iff ω).2 hω.2) hτ₁
  obtain ⟨τ'', hτ''def⟩ : ∃ τ'' : Ω → WithTop ℝ≥0, τ'' = G.piecewise
      (fun ω => min ((t₁ : ℝ≥0) : WithTop ℝ≥0) (min ((t₂ : ℝ≥0) : WithTop ℝ≥0) (S ω)))
      (fun ω => min ((t₂ : ℝ≥0) : WithTop ℝ≥0) (S ω)) := ⟨_, rfl⟩
  have hτ'' : IsStoppingTime 𝓓 τ'' := by
    rw [hτ''def]
    exact WholeField.isStoppingTime_piecewise_of_le hτ₁ hτ' (fun ω => min_le_right _ _) hGm
  have hτ''S : ∀ ω, τ'' ω ≤ S ω := by
    intro ω
    rw [hτ''def]
    by_cases hω : ω ∈ G
    · simp only [Set.piecewise, hω, ↓reduceIte]
      exact (min_le_right _ _).trans (min_le_right _ _)
    · simp only [Set.piecewise, hω, ↓reduceIte]
      exact min_le_right _ _
  refine ⟨fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ'' ω).untopD 0 : ℝ≥0),
    WholeField.IsLocalSet.sub_dist (he τ'' hτ'' (ae_of_all _ hτ''S)).1 hT₀, ?_⟩
  filter_upwards [hreg, hraw, hb, hW0] with ω hreg' hraw' hbω hw0
  obtain ⟨ζ₀, hSζ, -, hcont⟩ := hbω
  obtain ⟨S₀, hS₀⟩ := WithTop.ne_top_iff_exists.1 hreg'.2.1
  have hSω : S ω = (S₀ : WithTop ℝ≥0) := hS₀.symm
  have hWc : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀} := continuous_fst.comp_continuousOn hcont
  have hS₀ζ : (S₀ : ℝ≥0∞) < ζ₀ := by
    have : ((S₀ : WithTop ℝ≥0) : ℝ≥0∞) < ζ₀ := by rw [hS₀]; exact hSζ
    exact this
  have hclock : ∀ u : ℝ≥0, u ≤ S₀ → WholeField.hullClock (fwdHull (fun s : ℝ => W s.toNNReal ω) u) = u :=
    fun u hu => WholeField.hullClock_fwdHull_rpath hWc hw0 (lt_of_le_of_lt (by exact_mod_cast hu) hS₀ζ)
  have hmark : stRecHist xL xR W VL VR S ω ∈ preMarkSet t₁ Γ ↔
      ((t₁ : ℝ≥0) : WithTop ℝ≥0) < S ω ∧ truncH t₁ (stRaw xL xR W VL VR S ω) ∈ Γ := by
    simp only [preMarkSet, mem_ofPred_eq, hraw']
    rfl
  by_cases hG : ω ∈ G
  · -- the code stops at `t₁`
    rw [hGdef] at hG
    have hG2 : ((t₁ : ℝ≥0) : WithTop ℝ≥0) < S ω := hG.2
    have ht1S₀ : (t₁ : ℝ≥0) ≤ S₀ := by
      rw [hSω] at hG2; exact (WithTop.coe_lt_coe.1 hG2).le
    have hGω : ω ∈ G := by rw [hGdef]; exact hG
    have hτω : ((τ'' ω).untopD 0 : ℝ≥0) = (t₁ : ℝ≥0) := by
      rw [hτ''def]
      simp only [Set.piecewise, hGω, ↓reduceIte, min_eq_left ((hlt_iff ω).2 hG2).le, WithTop.untopD_coe]
    refine ⟨?_, fun hm => absurd (hmark.1 hm) hG.1⟩
    simp only [hτω, hclock _ ht1S₀, lt_irrefl, false_iff]
    exact fun hm => hG.1 (hmark.1 hm)
  · -- the code is `t₂ ∧ S`
    have hτω : ((τ'' ω).untopD 0 : ℝ≥0) = min S₀ (t₂ : ℝ≥0) := by
      rw [hτ''def]
      simp only [Set.piecewise, hG, ↓reduceIte, hSω]
      rw [← WithTop.coe_min, WithTop.untopD_coe, min_comm]
    have hT₂ : min S₀ (t₂ : ℝ≥0) ≤ S₀ := min_le_left _ _
    simp only [hτω, hclock _ hT₂]
    refine ⟨?_, fun hm => ?_⟩
    · rw [hmark]
      constructor
      · intro h1
        have h1' : (t₁ : ℝ≥0) < S₀ := lt_of_lt_of_le (by exact_mod_cast h1) hT₂
        have ht1S : ((t₁ : ℝ≥0) : WithTop ℝ≥0) < S ω := by rw [hSω]; exact WithTop.coe_lt_coe.2 h1'
        by_contra hn
        exact hG (by rw [hGdef]; exact ⟨hn, ht1S⟩)
      · rintro ⟨h1, -⟩
        rw [hSω] at h1
        have h1' : (t₁ : ℝ≥0) < S₀ := WithTop.coe_lt_coe.1 h1
        exact_mod_cast lt_min h1' (by exact_mod_cast ht)
    · rw [hraw', twoSeedProj_stoppedHistory_eq_tsOf hS₀.symm]
      exact tsHull_truncH_tsOf (continuousOn_stState_of_regular hreg' hS₀.symm) hS₀ζ hWc (fun _ _ => rfl) t₂

/-- **The stopped coupling's projection identity on pre-stop history events** (`Coupling.IsFamilyLocal`'s identity for
the centred field `h − T₀` on `{t₁ < S, truncH t₁ Y ∈ Γ, C ∩ K_{t₂ ∧ S} = ∅}`, `U ⊆ C`). -/
theorem IsStoppedSeedCoupling.setIntegral_lapTest_pre [IsProbabilityMeasure Q] (hr : 0 < r)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) {T₀ : DistOn upperHalfPlaneOpens}
    (hT₀ : IsHarmonicDistOn T₀ H) {t₁ t₂ : ℚ≥0} (ht : t₁ < t₂) {Γ : Set TwoSeedHist} (hΓ : MeasurableSet Γ)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) {U : Opens ℂ} (hUC : (U : Set ℂ) ⊆ C)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω in stRecHist xL xR W VL VR S ⁻¹' preHistSet t₁ t₂ Γ C,
        Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂Q =
      Coupling.projFactor U f Ξ * ∫ ω in stRecHist xL xR W VL VR S ⁻¹' preHistSet t₁ t₂ Γ C,
        Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂Q := by
  classical
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨A, hloc, hA⟩ := hc.exists_codedHull hr hT₀ ht hΓ
  have hRm := hc.measurable_stRecHist
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := id hc
  obtain ⟨k, hkdef⟩ : ∃ k : Set ℂ → ℂ, k = {Sc : Set ℂ | ((t₁ : ℝ≥0) : ℝ≥0∞) < WholeField.hullClock Sc}.indicator
      fun _ => (1 : ℂ) := ⟨_, rfl⟩
  have hk : Measurable[hittingSigma] k := by
    rw [hkdef]; exact measurable_const.indicator (measurableSet_lt measurable_const WholeField.measurable_hullClock)
  have hkb : ∀ Sc, ‖k Sc‖ ≤ 1 := fun Sc => by
    rw [hkdef]
    by_cases hS' : Sc ∈ {Sc : Set ℂ | ((t₁ : ℝ≥0) : ℝ≥0∞) < WholeField.hullClock Sc}
    · rw [indicator_of_mem hS', norm_one]
    · rw [indicator_of_notMem hS', norm_zero]; exact zero_le_one
  obtain ⟨δ, hδ, hδH⟩ := hC.exists_thickening_subset_open QuantumZipper.isOpen_H hCH
  have hVH : ∀ m : ℕ, thickening (δ / ((m : ℝ) + 1)) C ⊆ H := fun m => by
    have hle : δ / ((m : ℝ) + 1) ≤ δ := div_le_self hδ.le (by have := m.cast_nonneg (α := ℝ); linarith)
    exact (thickening_mono hle C).trans hδH
  have hid : ∀ m : ℕ, ∀ χ₁ χ₂ : TestOn upperHalfPlaneOpens, χ₁ = lapTest U f + Ξ → χ₂ = Ξ →
      ∫ ω, {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)}.indicator (fun ω => k (A ω)) ω *
          Complex.exp (Complex.I * ((h ω - T₀) χ₁ : ℂ)) ∂Q =
        Coupling.projFactor U f Ξ * ∫ ω, {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)}.indicator
          (fun ω => k (A ω)) ω * Complex.exp (Complex.I * ((h ω - T₀) χ₂ : ℂ)) ∂Q := by
    intro m χ₁ χ₂ h1 h2
    rw [h1, h2]
    exact integral_indicator_lapTest_eq (V := ⟨thickening (δ / ((m : ℝ) + 1)) C, isOpen_thickening⟩) hloc
      (hVH m) (show (U : Set ℂ) ⊆ thickening (δ / ((m : ℝ) + 1)) C from
        hUC.trans (self_subset_thickening (by positivity) C)) hk hkb f Ξ
  set T : Set Ω := stRecHist xL xR W VL VR S ⁻¹' preHistSet t₁ t₂ Γ C with hTdef
  have hTm : MeasurableSet T := hRm (measurableSet_preHistSet t₁ t₂ hΓ hC)
  have hconv : ∀ᵐ ω ∂Q, Tendsto (fun m : ℕ => {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)}.indicator
      (fun ω => k (A ω)) ω) atTop (𝓝 (T.indicator (fun _ => (1 : ℂ)) ω)) := by
    filter_upwards [hA] with ω ⟨hclk, hhull⟩
    obtain ⟨hev, hnev⟩ := eventually_disjoint_thickening_iff (K := A ω) hC hCH hδ
    by_cases hm : stRecHist xL xR W VL VR S ω ∈ preMarkSet t₁ Γ
    · have hk1 : k (A ω) = 1 := by
        rw [hkdef, indicator_of_mem (show A ω ∈ {Sc : Set ℂ | ((t₁ : ℝ≥0) : ℝ≥0∞) < WholeField.hullClock Sc} from
          hclk.2 hm)]
      have hTiff : ω ∈ T ↔ Disjoint C (closure (A ω) ∩ (upperHalfPlaneOpens : Set ℂ)) := by
        simp only [hTdef, mem_preimage, preHistSet, ← hhull hm]
        exact ⟨fun h' => h'.2.2, fun h' => ⟨hm.1, hm.2, h'⟩⟩
      have hind : ∀ m : ℕ, {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)}.indicator (fun ω => k (A ω)) ω =
          if Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C) then 1 else 0 := fun m => by
        by_cases hd : Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)
        · rw [indicator_of_mem (show ω ∈ {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)} from hd), hk1]
          simp only [hd, ↓reduceIte]
        · rw [indicator_of_notMem (show ω ∉ {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)} from hd)]
          simp only [hd, ↓reduceIte]
      by_cases hd : Disjoint C (closure (A ω) ∩ (upperHalfPlaneOpens : Set ℂ))
      · rw [indicator_of_mem (hTiff.2 hd)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev hd] with m hm'
        rw [hind m]
        simp only [hm', ↓reduceIte]
      · rw [indicator_of_notMem (fun h' => hd (hTiff.1 h'))]
        refine tendsto_const_nhds.congr fun m => ?_
        rw [hind m]
        simp only [hnev hd m, ↓reduceIte]
    · have hk0 : k (A ω) = 0 := by
        rw [hkdef, indicator_of_notMem (show A ω ∉ {Sc : Set ℂ | ((t₁ : ℝ≥0) : ℝ≥0∞) < WholeField.hullClock Sc} from
          fun h' => hm (hclk.1 h'))]
      have hnT : ω ∉ T := fun hT => hm ⟨hT.1, hT.2.1⟩
      rw [indicator_of_notMem hnT]
      refine tendsto_const_nhds.congr fun m => ?_
      by_cases hd : ω ∈ {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)}
      · rw [indicator_of_mem hd, hk0]
      · rw [indicator_of_notMem hd]
  -- dominated convergence
  have hAae : AEMeasurable A Q := measurable_fst.comp_aemeasurable hloc.1
  have hhm' : Measurable fun ω => h ω - T₀ := (WholeField.measurable_sub_dist T₀).comp hhm
  have hlim : ∀ χ : TestOn upperHalfPlaneOpens,
      Tendsto (fun m : ℕ => ∫ ω, {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)}.indicator
        (fun ω => k (A ω)) ω * Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) ∂Q) atTop
        (𝓝 (∫ ω in T, Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) ∂Q)) := by
    intro χ
    have hcm : Measurable fun ω => Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) :=
      Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((measurable_distOn_apply χ).comp hhm')))
    rw [← integral_indicator hTm]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun m => ?_) (integrable_const _)
      (fun m => Eventually.of_forall fun ω => ?_) ?_
    · have hgm : Measurable[hittingSigma] fun Sc : Set ℂ =>
          {Sc : Set ℂ | Disjoint Sc (thickening (δ / ((m : ℝ) + 1)) C)}.indicator k Sc :=
        hk.indicator (measurableSet_avoid isOpen_thickening (hVH m))
      have he : (fun ω => {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)}.indicator (fun ω => k (A ω)) ω) =
          fun ω => (fun Sc : Set ℂ => {Sc : Set ℂ | Disjoint Sc (thickening (δ / ((m : ℝ) + 1)) C)}.indicator k Sc)
            (A ω) := by
        funext ω
        simp only [indicator, mem_ofPred_eq]
      have h1 : AEStronglyMeasurable (fun ω => {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)}.indicator
          (fun ω => k (A ω)) ω) Q := by
        rw [he]; exact (hgm.comp_aemeasurable hAae).aestronglyMeasurable
      exact h1.mul hcm.aestronglyMeasurable
    · rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
      by_cases hd : ω ∈ {ω | Disjoint (A ω) (thickening (δ / ((m : ℝ) + 1)) C)}
      · rw [indicator_of_mem hd]; exact hkb _
      · rw [indicator_of_notMem hd, norm_zero]; exact zero_le_one
    · filter_upwards [hconv] with ω hω
      have he : T.indicator (fun ω => Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ))) ω =
          T.indicator (fun _ => (1 : ℂ)) ω * Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) := by
        by_cases hT : ω ∈ T
        · rw [indicator_of_mem hT, indicator_of_mem hT, one_mul]
        · rw [indicator_of_notMem hT, indicator_of_notMem hT, zero_mul]
      rw [he]
      exact hω.mul_const _
  have h1 := hlim (lapTest U f + Ξ)
  have h2 := (hlim Ξ).const_mul (Coupling.projFactor U f Ξ)
  exact tendsto_nhds_unique h1 (h2.congr fun m => (hid m _ _ rfl rfl).symm)

end Pre

end LocalExt

end InteractingSLE
