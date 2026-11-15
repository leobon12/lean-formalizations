/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField6Cond
import InteractingSLE.WangWu.CouplingBridge
import InteractingSLE.WangWu.CouplingVersionTwo

/-!
# C.4 at `κ = 4`: the retained kernel value, active tests, and pocket observables of the germ

Packet PROVE-WHOLEFIELD6 (follow-up note C.4, `ig1_followup_proofs.txt` L1651–1704; the `κ = 4` mean of C.5,
L1834–1840; Wang–Wu Definition 1.5).

The target kernel of the whole-field identification at `κ = 4` is written trace-free, with Wang–Wu's frozen mean
`η̄_t` and retained Green form `Q_{U_t}` (`kerCF`):

  `E[e^{i(h,ψ)} | 𝓕_σ] = exp(i ∫ η̄_σ ψ − ½ Q_{U_σ}(ψ, ψ))`.

* **Active tests** (`ae_condExp_exp_eq_kerCF_of_active`, the base case of the pocket induction): for a test avoiding
  `K_σ` this is the frozen conditional law of Theorem 1.1 (`IsOptionalHullCoupling`), rewritten with
  `WangWu.integral_frozenMean_mul_eq` and `WangWu.retainedGreenEnergy_eq_loewnerGreenEnergy`.
* **Pocket observables** (`stronglyMeasurable_indicator_histGerm`, `exists_pocketEvent`): on an event `F ∈ 𝓕_T` on
  which the support of `ψ` lies in the hull `K_T`, `1_F g((h⁰, ψ))` is measurable for the germ `Γ(𝓕_T, K_T)`. This is
  the germ hypothesis of the birth transfer `ae_condExp_eq_of_birth` (and of the freeze (WF7a)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets

/-! ### The kernel value -/

section Kernel

variable {nL nR : ℕ} {Ω : Type*}

/-- **The retained Gaussian kernel value at `κ = 4`** (Wang–Wu Definition 1.5; follow-up note (WF13)):
`exp(i ∫ η̄_t ψ − ½ Q_{U_t}(ψ, ψ))` at the path of `ω`. -/
def kerCF (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ψ : ℂ → ℝ) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * ((∫ z, WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω))
      (fun i => (VR i · ω)) t z * ψ z : ℝ) : ℂ) -
    (((1 / 2 : ℝ) * WangWu.retainedGreenEnergy (W · ω) t ψ : ℝ) : ℂ))

variable {nL' nR' : ℕ}

/-- **The frozen mean does not move after the swallowing** of the point. -/
theorem frozenMean_eq_of_swallowTime_le {ρL : Fin nL' → ℝ} {ρR : Fin nR' → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL' → ℝ≥0 → ℝ} {vR : Fin nR' → ℝ≥0 → ℝ} {z : ℂ} {t₁ t₂ : ℝ≥0}
    (hz : swallowTime (Ito.rpath w) z ≤ t₁) (h12 : t₁ ≤ t₂) :
    WangWu.frozenMean ρL ρR w vL vR t₂ z = WangWu.frozenMean ρL ρR w vL vR t₁ z := by
  have h1 : ¬ ((t₁ : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath w) z := not_lt.2 hz
  have h2 : ¬ ((t₂ : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath w) z :=
    not_lt.2 (hz.trans (by exact_mod_cast h12))
  simp only [WangWu.frozenMean, h1, h2, ↓reduceIte]

/-- **The retained Green energy of a test swallowed by `t₁` does not move after `t₁`.** -/
theorem retainedGreenEnergy_eq_of_swallowTime_le {w : ℝ≥0 → ℝ} {ψ : ℂ → ℝ} {t₁ t₂ : ℝ≥0}
    (hψ : ∀ z, ψ z ≠ 0 → swallowTime (Ito.rpath w) z ≤ t₁) (h12 : t₁ ≤ t₂) :
    WangWu.retainedGreenEnergy w t₂ ψ = WangWu.retainedGreenEnergy w t₁ ψ := by
  unfold WangWu.retainedGreenEnergy
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  by_cases ha : ψ a = 0
  · simp [ha]
  have e := WangWu.retainedGreen_min_eq (w := w) (y := a) (z := b) h12 (Or.inr (Or.inl (hψ a ha))) t₂
  rw [min_self, min_eq_right h12] at e
  show ψ a * WangWu.retainedGreen w t₂ a b * ψ b = ψ a * WangWu.retainedGreen w t₁ a b * ψ b
  rw [e]

/-- **The kernel value of a test swallowed by `t₁` does not move after `t₁`** (a pocket's field is frozen at its
birth: C.4, "Its mean on each pocket is frozen at birth"). -/
theorem kerCF_eq_of_swallowTime_le {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ψ : ℂ → ℝ} {ω : Ω} {t₁ t₂ : ℝ≥0}
    (hψ : ∀ z, ψ z ≠ 0 → swallowTime (Ito.rpath (W · ω)) z ≤ t₁) (h12 : t₁ ≤ t₂) :
    kerCF ρL ρR W VL VR t₂ ψ ω = kerCF ρL ρR W VL VR t₁ ψ ω := by
  have hm : (∫ z, WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) t₂ z * ψ z) =
      ∫ z, WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) t₁ z * ψ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : ψ z = 0
    · simp [hz]
    show _ * ψ z = _ * ψ z
    rw [frozenMean_eq_of_swallowTime_le (hψ z hz) h12]
  rw [kerCF, kerCF, hm, retainedGreenEnergy_eq_of_swallowTime_le hψ h12]

end Kernel

/-! ### Active tests -/

section Active

universe u

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- **The kernel of an active test** (base case of C.4). For the frozen `κ = 4` coupling, a driving stop `σ < ζ` and a
test `ψ`: almost surely on `{supp ψ ∩ K_σ = ∅}`, `E[e^{i(h,ψ)} | 𝓕_σ] = exp(i ∫ η̄_σ ψ − ½ Q_{U_σ}(ψ, ψ))`. -/
theorem ae_condExp_exp_eq_kerCF_of_active (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ)) | hσ.measurableSpace]) ω =
        kerCF ρL ρR W VL VR (σ ω) ψ ω := by
  have hker := (hC.2.2.2.choose_spec _ hσ (hσζ.mono fun ω hω => hω)).2
    (fun ω => bheAt 4 ρL ρR (W (σ ω) ω) (fun i => VL i (σ ω) ω) (fun i => VR i (σ ω) ω))
    (fun ω => bheAt_spec 4 ρL ρR _ _ _) ψ
  filter_upwards [hker, hC.1.2.2.2.2, hσζ] with ω h1 hP hlt hdisj
  simp only [WithTop.untopD_coe] at h1
  have hdisj' : Disjoint (tsupport ψ) (fwdHull (Ito.rpath (W · ω)) (σ ω)) := hdisj
  rw [show (P[fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ)) | hσ.measurableSpace]) ω =
    condExp hσ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ))) ω from rfl]
  rw [h1 hdisj, kerCF, WangWu.integral_frozenMean_mul_eq (ρL := ρL) (ρR := ρR) hP hlt
    ψ.tsupport_subset hdisj' (bheAt_spec 4 ρL ρR _ _ _),
    WangWu.retainedGreenEnergy_eq_loewnerGreenEnergy (ρL := ρL) (ρR := ρR) hP hlt ψ.tsupport_subset hdisj']
  rfl

end Active

/-! ### Pocket observables are germ observables -/

section Germ

variable {Ω : Type*} {ℋ : MeasurableSpace Ω}

open scoped Classical in
/-- **A pocket observable is a germ observable.** If `F ∈ ℋ` and on `F` the support of `ψ` lies in every germ
neighbourhood of `A`, then `1_F g((h₀, ψ))` is measurable for `Γ(ℋ, A) = ⨅ₙ (ℋ ⊔ 𝒜_{1/(n+1)})`. -/
theorem stronglyMeasurable_indicator_histGerm {A : Ω → Set ℂ} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    {ψ : TestOn upperHalfPlaneOpens} {F : Set Ω} (hF : MeasurableSet[ℋ] F)
    (hFsub : ∀ ω ∈ F, ∀ δ : ℝ, 0 < δ → tsupport ψ ⊆ germNbhd δ (A ω)) {g : ℝ → ℂ} (hg : Measurable g) :
    StronglyMeasurable[histGerm ℋ A h₀] (F.indicator fun ω => g (h₀ ω ψ)) := by
  have hmeas : Measurable[histGerm ℋ A h₀] (F.indicator fun ω => g (h₀ ω ψ)) := by
    intro U hU
    show MeasurableSet[⨅ n : ℕ, ℋ ⊔ germSigmaAt A h₀ (1 / ((n : ℝ) + 1))] _
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
    set E : Set Ω := {ω | tsupport ψ ⊆ germNbhd δ (A ω)} ∩ (fun ω => h₀ ω ψ) ⁻¹' (g ⁻¹' U) with hEdef
    have hE : MeasurableSet[germSigmaAt A h₀ δ] E :=
      le_sup_right (a := MeasurableSpace.comap A hittingSigma) _
        (MeasurableSpace.measurableSet_generateFrom ⟨ψ, g ⁻¹' U, hg hU, rfl⟩)
    have e : (F.indicator fun ω => g (h₀ ω ψ)) ⁻¹' U = (F ∩ E) ∪ (if (0 : ℂ) ∈ U then Fᶜ else ∅) := by
      ext ω
      by_cases hω : ω ∈ F
      · have hs := hFsub ω hω δ hδ
        by_cases h0 : (0 : ℂ) ∈ U <;> simp [hω, h0, E, hs]
      · by_cases h0 : (0 : ℂ) ∈ U <;> simp [hω, h0, E]
    rw [e]
    have hF' : MeasurableSet[ℋ ⊔ germSigmaAt A h₀ δ] F := le_sup_left (a := ℋ) _ hF
    refine (hF'.inter (le_sup_right (a := ℋ) _ hE)).union ?_
    split_ifs
    · exact hF'.compl
    · exact @MeasurableSet.empty _ (ℋ ⊔ germSigmaAt A h₀ δ)
  exact hmeas.stronglyMeasurable

/-- **The pocket event.** For a hitting-measurable random set `A` (measurable for `ℋ`) and `C ⊆ ℍ`, there is an event
`F ∈ ℋ` containing `{C ⊆ A}` on which `C` lies in every germ neighbourhood of `A` (every point of a countable dense
subset of `C` is in the relative closure of `A ∩ ℍ`). -/
theorem exists_pocketEvent {A : Ω → Set ℂ} (hA : Measurable[ℋ, hittingSigma] A) {C : Set ℂ}
    (hCH : C ⊆ H) :
    ∃ F : Set Ω, MeasurableSet[ℋ] F ∧ (∀ ω ∈ F, ∀ δ : ℝ, 0 < δ → C ⊆ germNbhd δ (A ω)) ∧
      ∀ ω, C ⊆ A ω → ω ∈ F := by
  obtain ⟨D, hDC, hDc, hCD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace C).exists_countable_dense_subset
  set F : Set Ω := ⋂ z ∈ D, ⋂ n : ℕ, {ω | (A ω ∩ (ball z (1 / ((n : ℝ) + 1)) ∩ H)).Nonempty} with hFdef
  refine ⟨F, ?_, ?_, ?_⟩
  · refine MeasurableSet.biInter hDc fun z _ => MeasurableSet.iInter fun n => ?_
    exact hA (MeasurableSpace.measurableSet_generateFrom
      ⟨ball z (1 / ((n : ℝ) + 1)) ∩ H, isOpen_ball.inter isOpen_H, inter_subset_right, rfl⟩)
  · intro ω hω δ hδ x hx
    have hxH : x ∈ H := hCH hx
    obtain ⟨z, hzD, hxz⟩ := Metric.mem_closure_iff.1 (hCD hx) (δ / 2) (half_pos hδ)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hδ)
    have hωz := mem_iInter.1 (mem_iInter₂.1 hω z hzD) n
    obtain ⟨a, haA, haB, haH⟩ := hωz
    refine ⟨hxH, Or.inl ?_⟩
    rw [Metric.mem_thickening_iff]
    refine ⟨a, Or.inl ⟨haA, haH⟩, ?_⟩
    have h1 : dist a z < δ / 2 := lt_of_lt_of_le (mem_ball.1 haB) hn.le
    linarith [dist_triangle x z a, dist_comm a z]
  · intro ω hCA
    refine mem_iInter₂.2 fun z hzD => mem_iInter.2 fun n => ?_
    exact ⟨z, hCA (hDC hzD), mem_ball_self (by positivity), hCH (hDC hzD)⟩

end Germ

/-! ### The pocket mean is the left limit of the active means, for almost every point -/

section MeanLimit

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

open WangWu in
/-- **The frozen mean is the left limit at the swallowing time, almost surely for almost every point** (Wang–Wu
Lemma 3.5 one-point limit, `exists_martingale_frozenMean`, made simultaneous in `z` by Fubini through the measurable
guard of `WangWu.goodPair`, as in the proof of `exists_frozenMean_version`). For a marked chain and a bounded stop
`σ₀ < T` of the usual augmentation: almost surely, for Lebesgue-almost every `z ∈ ℍ` with `s(z) ≤ σ₀`,
`η_r(z) → η̄_{σ₀}(z)` as `r ↑ s(z)`. -/
theorem ae_ae_tendsto_meanAt_frozenMean [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ H → swallowTime (Ito.rpath (W · ω)) z ≤ σ₀ ω →
      Tendsto (fun r => meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z)
        (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal)
        (𝓝 (frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) z)) := by
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hE' := hE
  obtain ⟨-, hWa, hVLa, hVRa, -⟩ := hE'
  obtain ⟨G, hG0, hGae, hGsub⟩ := exists_goodSet hE hσ₀ζ
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGsub ω hω).1.2.2.2.1
  have hW𝓖 : AdaptedBefore 𝓖 ζ W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) hWa
  have hVL𝓖 : ∀ i, AdaptedBefore 𝓖 ζ (VL i) := fun i =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hVLa i)
  have hVR𝓖 : ∀ i, AdaptedBefore 𝓖 ζ (VR i) := fun i =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hVRa i)
  -- for each `z ∈ ℍ`, almost every `(z, ω)` is good
  have hgood : ∀ z ∈ H, ∀ᵐ ω ∂P, (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀ := by
    intro z hz
    obtain ⟨hlim, -⟩ := exists_martingale_frozenMean (ρL := ρL) (ρR := ρR) hE hz hσ₀ hσ₀ζ hσ₀N
    filter_upwards [hlim, hGae] with ω hl hω
    obtain ⟨hP, hσζ⟩ := hGsub ω hω
    refine ⟨⟨hω, hz⟩, ?_⟩
    by_cases hs : (σ₀ ω : ℝ≥0∞) < swallowTime (Ito.rpath (W · ω)) z
    · left
      obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min hs hσζ)
      have hc1' : (σ₀ ω : ℝ) < c := by exact_mod_cast hc1
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hc1'
      have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg _).trans hq1.le
      have hqc : ((q : ℝ).toNNReal : ℝ≥0∞) < c := by
        exact_mod_cast (Real.toNNReal_lt_iff_lt_coe hq0).2 hq2
      have hqm := hqc.trans hc2
      refine mem_iUnion.2 ⟨q, ?_, ?_⟩
      · show σ₀ ω < (q : ℝ).toNNReal
        exact Real.lt_toNNReal_iff_coe_lt.2 hq1
      · exact (mem_aliveProd_iff hP hω hz (hqm.trans_le (min_le_right _ _))).2
          (hqm.trans_le (min_le_left _ _))
    · right
      have hsσ := not_lt.1 hs
      exact (guardG_iff hP hω hz (lt_of_le_of_lt hsσ hσζ)).2 ⟨_, hl hsσ⟩
  have hgm := measurableSet_goodPair (ρL := ρL) (ρR := ρR) hW𝓖 hVL𝓖 hVR𝓖 hGc hG0 hσ₀
  have e : {x : ℂ × Ω | x.1 ∈ H → x ∈ goodPair ρL ρR W VL VR ζ G σ₀} =
      (Prod.fst ⁻¹' H)ᶜ ∪ goodPair ρL ρR W VL VR ζ G σ₀ := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]
    tauto
  have hmeas : MeasurableSet {x : ℂ × Ω | x.1 ∈ H → x ∈ goodPair ρL ρR W VL VR ζ G σ₀} := by
    rw [e]
    exact (isOpen_H.measurableSet.preimage measurable_fst).compl.union hgm
  have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ ω ∂P, z ∈ H →
      (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀ := Eventually.of_forall fun z => by
    by_cases hz : z ∈ H
    · filter_upwards [hgood z hz] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hz
  have h2 := (Measure.ae_ae_comm (μ := (volume : Measure ℂ)) (ν := P)
    (p := fun z ω => z ∈ H → (z, ω) ∈ goodPair ρL ρR W VL VR ζ G σ₀) hmeas).1 h1
  filter_upwards [h2, hGae] with ω hω hωG
  obtain ⟨hP, hσζ⟩ := hGsub ω hωG
  filter_upwards [hω] with z hz hzH hsσ
  obtain ⟨-, hg⟩ := hz hzH
  rcases hg with hal | hgd
  · exfalso
    obtain ⟨q, hq1, hq2⟩ := mem_iUnion.1 hal
    have hq1' : σ₀ ω < (q : ℝ).toNNReal := hq1
    obtain ⟨-, -, hqζ, hsol⟩ := hq2
    have := lt_swallowTime_of_path hP hqζ hzH hsol
    exact absurd (hsσ.trans (by exact_mod_cast hq1'.le)) (not_le.2 this)
  · obtain ⟨L, hL⟩ := (guardG_iff hP hωG hzH (lt_of_le_of_lt hsσ hσζ)).1 hgd
    have hlt : ¬ ((σ₀ ω : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath (W · ω)) z := not_lt.2 hsσ
    have hpos : 0 < (swallowTime (Ito.rpath (W · ω)) z).toNNReal := by
      have h0 := swallowTime_pos_of_path hP (lt_of_le_of_lt zero_le hσζ) hzH
      have hne : swallowTime (Ito.rpath (W · ω)) z ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top hsσ
      exact ENNReal.toNNReal_pos h0.ne' hne
    have : (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
    have hfm : frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) z = L := by
      simp only [frozenMean, hlt, ↓reduceIte]
      exact hL.limUnder_eq
    rw [hfm]; exact hL

end MeanLimit

end WholeField

end InteractingSLE
