/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.FiltrationBasic
import InteractingSLE.Spec.Ito.Dynkin
import InteractingSLE.Stochastic.Martingale.OptionalSampling
import QuantumZipper.Proofs.Probability.StrongMarkov
import QuantumZipper.Proofs.RS.TransienceCanon

/-!
# Restarting at a stopping time: the strong Markov property of a filtered Brownian motion

Packet PROVE-RESTART (specification, proof of Theorem 2.2 and §5.2: "by the strong Markov property, the
process after the stopping time is again an integrated evolution from the state at that time").

The frozen `IsFilteredBrownianReal 𝓕 B P` asks only that each increment `B_t − B_s` be independent of
`𝓕_s`. This file derives the strong Markov property in the form a restart needs:

* `indep_sup_right_of_indep`: if `m₁ ⊥ m₂` and `m₁ ⊔ m₂ ⊥ m₃` then `m₁ ⊥ m₂ ⊔ m₃`;
* `indep_future`: the whole future path `(B_{t+s} − B_t)_{s ≥ 0}` is independent of `𝓕_t` (induction on the
  largest time of a finite set of increments, then a directed supremum);
* `exists_continuous_version`: a Brownian motion of `𝓕` has a version with every path continuous that is a
  Brownian motion of the usual augmentation of `𝓕`;
* `restartFiltration 𝓕 T hT`: the filtration `s ↦ 𝓕_{T+s}` of a finite stopping time `T`;
* `isFilteredBrownianReal_restart_cond`: for `A ∈ 𝓕_T` with `P A ≠ 0`, the restarted process
  `B_{T+·} − B_T` is a Brownian motion of `s ↦ 𝓕_{T+s}` under the conditional measure `P[·|A]`
  (QuantumZipper's strong Markov property `QuantumZipper.StrongMarkov`, applied at the stopping times
  `T + s`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Restart

open QuantumZipper.StrongMarkov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Independence of a σ-algebra from a supremum -/

/-- If `m₁` is independent of `m₂` and `m₁ ⊔ m₂` is independent of `m₃`, then `m₁` is independent of
`m₂ ⊔ m₃` (the π-system of intersections `B ∩ C` generates `m₂ ⊔ m₃`). -/
theorem indep_sup_right_of_indep [IsZeroOrProbabilityMeasure P] {m₁ m₂ m₃ : MeasurableSpace Ω}
    (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) (h₃ : m₃ ≤ mΩ) (h12 : Indep m₁ m₂ P)
    (h123 : Indep (m₁ ⊔ m₂) m₃ P) : Indep m₁ (m₂ ⊔ m₃) P := by
  set p₂ : Set (Set Ω) := image2 (· ∩ ·) {B | MeasurableSet[m₂] B} {C | MeasurableSet[m₃] C}
    with hp₂
  have hpi : IsPiSystem p₂ := by
    rintro _ ⟨B, hB, C, hC, rfl⟩ _ ⟨B', hB', C', hC', rfl⟩ -
    refine ⟨B ∩ B', hB.inter hB', C ∩ C', hC.inter hC', ?_⟩
    simp only
    ext ω
    simp only [mem_inter_iff]
    tauto
  have hgen : m₂ ⊔ m₃ = MeasurableSpace.generateFrom p₂ := by
    refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
    · intro B hB
      refine MeasurableSpace.measurableSet_generateFrom ⟨B, hB, univ, MeasurableSet.univ, ?_⟩
      simp
    · intro C hC
      refine MeasurableSpace.measurableSet_generateFrom ⟨univ, MeasurableSet.univ, C, hC, ?_⟩
      simp
    · rintro _ ⟨B, hB, C, hC, rfl⟩
      exact (le_sup_left (a := m₂) (b := m₃) B hB).inter (le_sup_right (a := m₂) (b := m₃) C hC)
  refine IndepSets.indep h₁ (sup_le h₂ h₃) (@MeasurableSpace.isPiSystem_measurableSet Ω m₁) hpi
    (@MeasurableSpace.generateFrom_measurableSet Ω m₁).symm hgen ?_
  rw [IndepSets_iff]
  rintro A _ hA ⟨B, hB, C, hC, rfl⟩
  have hAB : MeasurableSet[m₁ ⊔ m₂] (A ∩ B) :=
    (le_sup_left (a := m₁) (b := m₂) A hA).inter (le_sup_right (a := m₁) (b := m₂) B hB)
  have e1 : P (A ∩ (B ∩ C)) = P (A ∩ B) * P C := by
    rw [← inter_assoc]; exact (Indep_iff _ _ _).1 h123 _ _ hAB hC
  have e2 : P (B ∩ C) = P B * P C :=
    (Indep_iff _ _ _).1 h123 _ _ (le_sup_right (a := m₁) (b := m₂) B hB) hC
  rw [e1, e2, (Indep_iff _ _ _).1 h12 _ _ hA hB, mul_assoc]

/-- Independence passes to a conditional measure `P[·|A]` when `A` belongs to the second σ-algebra. -/
theorem indep_cond {m₁ m₂ : MeasurableSpace Ω} (h₂ : m₂ ≤ mΩ) (h12 : Indep m₁ m₂ P) {A : Set Ω}
    (hA : MeasurableSet[m₂] A) : Indep m₁ m₂ (P[|A]) := by
  rw [Indep_iff] at h12 ⊢
  intro S G hS hG
  have hAm : MeasurableSet[mΩ] A := h₂ _ hA
  rw [cond_apply hAm P, cond_apply hAm P, cond_apply hAm P]
  have hGA : MeasurableSet[m₂] (A ∩ G) := hA.inter hG
  have e1 : P (A ∩ (S ∩ G)) = P S * P (A ∩ G) := by
    rw [show A ∩ (S ∩ G) = S ∩ (A ∩ G) by ext; simp only [mem_inter_iff]; tauto]
    exact h12 _ _ hS hGA
  have e2 : P (A ∩ S) = P S * P A := by
    rw [inter_comm]; exact h12 _ _ hS hA
  rw [e1, e2]
  by_cases h0 : P A = 0
  · simp [h0, measure_mono_null inter_subset_left h0]
  by_cases htop : P A = ∞
  · simp [htop]
  rw [show (P A)⁻¹ * (P S * P A) = P S by
    rw [mul_comm (P S), ← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]]
  ring

/-! ### The future path of a filtered Brownian motion is independent of the past -/

section Future

variable {𝓖 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The σ-algebra of the increments `X_{t+s} − X_t`, `s ∈ I`. -/
abbrev incrSigma (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (I : Finset ℝ≥0) : MeasurableSpace Ω :=
  ⨆ s ∈ I, MeasurableSpace.comap (fun ω => X (t + s) ω - X t ω) inferInstance

theorem measurable_incr_of_mem {t : ℝ≥0} {I : Finset ℝ≥0} {s : ℝ≥0} (hs : s ∈ I) :
    Measurable[incrSigma X t I] fun ω => X (t + s) ω - X t ω := by
  intro S hS
  exact le_iSup₂ (f := fun s (_ : s ∈ I) =>
    MeasurableSpace.comap (fun ω => X (t + s) ω - X t ω) inferInstance) s hs _ ⟨S, hS, rfl⟩

theorem incrSigma_le_of_le (hX : Adapted 𝓖 X) {t M : ℝ≥0} {I : Finset ℝ≥0}
    (hI : ∀ s ∈ I, s ≤ M) : incrSigma X t I ≤ 𝓖 (t + M) := by
  refine iSup₂_le fun s hs => ?_
  have h1 : Measurable[𝓖 (t + M)] (X (t + s)) :=
    (hX (t + s)).mono (𝓖.mono (add_le_add le_rfl (hI s hs))) le_rfl
  have h2 : Measurable[𝓖 (t + M)] (X t) :=
    (hX t).mono (𝓖.mono le_self_add) le_rfl
  exact (h1.sub h2).comap_le

theorem incrSigma_le (hX : Adapted 𝓖 X) (t : ℝ≥0) (I : Finset ℝ≥0) : incrSigma X t I ≤ mΩ :=
  (incrSigma_le_of_le hX (M := I.sup id) fun _ hs => Finset.le_sup (f := id) hs).trans (𝓖.le _)

theorem incrSigma_mono (t : ℝ≥0) : Monotone (incrSigma X t) := fun _ _ hIJ =>
  biSup_mono fun _ hs => hIJ hs

/-- Each finite family of future increments is independent of `𝓖_t`. -/
theorem indep_incrSigma (hB : IsFilteredBrownianReal 𝓖 X P) (t : ℝ≥0) (I : Finset ℝ≥0) :
    Indep (𝓖 t) (incrSigma X t I) P := by
  have := hB.isProbabilityMeasure'
  have hX : Adapted 𝓖 X := hB.2.1
  induction I using Finset.induction_on_max with
  | empty => simp [incrSigma, indep_bot_right]
  | insert a s has ih =>
    set M : ℝ≥0 := s.sup id with hM
    have hsM : ∀ x ∈ s, x ≤ M := fun x hx => Finset.le_sup (f := id) hx
    have hMa : M ≤ a := Finset.sup_le fun x hx => (has x hx).le
    set c : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω => X (t + a) ω - X (t + M) ω) inferInstance with hc
    have hc_le : c ≤ mΩ :=
      (((hX (t + a)).mono (𝓖.le _) le_rfl).sub
        ((hX (t + M)).mono (𝓖.le _) le_rfl)).comap_le
    have hpast : 𝓖 t ⊔ incrSigma X t s ≤ 𝓖 (t + M) :=
      sup_le (𝓖.mono le_self_add) (incrSigma_le_of_le hX hsM)
    have hind : Indep (𝓖 t ⊔ incrSigma X t s) c P := by
      have h := hB.2.2 (t + M) (t + a) (add_le_add le_rfl hMa)
      exact (indep_of_indep_of_le_right h hpast).symm
    have hsup := indep_sup_right_of_indep (𝓖.le t) (incrSigma_le hX t s) hc_le ih hind
    refine indep_of_indep_of_le_right hsup ?_
    -- `incrSigma X t (insert a s) ≤ incrSigma X t s ⊔ c`
    have hMm : Measurable[incrSigma X t s] fun ω => X (t + M) ω - X t ω := by
      rcases s.eq_empty_or_nonempty with hs | hs
      · have hM0 : M = 0 := by rw [hM, hs]; rfl
        have : (fun ω => X (t + M) ω - X t ω) = fun _ => 0 := by
          funext ω; rw [hM0, add_zero, sub_self]
        rw [this]; exact measurable_const
      · obtain ⟨m, hm, hmM⟩ := Finset.exists_mem_eq_sup s hs id
        have : M = m := hmM
        rw [this]
        exact measurable_incr_of_mem hm
    refine iSup₂_le fun x hx => ?_
    rcases Finset.mem_insert.1 hx with rfl | hx
    · have hsplit : (fun ω => X (t + x) ω - X t ω) =
          fun ω => (X (t + x) ω - X (t + M) ω) + (X (t + M) ω - X t ω) := by
        funext ω; ring
      rw [hsplit]
      have h1 : Measurable[incrSigma X t s ⊔ c] fun ω => X (t + x) ω - X (t + M) ω :=
        (comap_measurable _).mono le_sup_right le_rfl
      have h2 : Measurable[incrSigma X t s ⊔ c] fun ω => X (t + M) ω - X t ω :=
        hMm.mono le_sup_left le_rfl
      exact (h1.add h2).comap_le
    · exact (measurable_incr_of_mem hx).comap_le.trans le_sup_left

/-- **The future path is independent of the past**: for a Brownian motion of `𝓖`, the restarted path
`s ↦ X_{t+s} − X_t` is independent of `𝓖_t` (the hypothesis `hind` of `QuantumZipper.StrongMarkov`). -/
theorem indep_future (hB : IsFilteredBrownianReal 𝓖 X P) (t : ℝ≥0) :
    Indep (𝓖 t) (MeasurableSpace.comap (smPath X (fun _ => t)) MeasurableSpace.pi) P := by
  have := hB.isProbabilityMeasure'
  have hX : Adapted 𝓖 X := hB.2.1
  have hpath : MeasurableSpace.comap (smPath X (fun _ => t)) MeasurableSpace.pi =
      ⨆ I : Finset ℝ≥0, incrSigma X t I := by
    refine le_antisymm ?_ ?_
    · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le fun s => ?_
      rw [MeasurableSpace.comap_comp]
      exact (measurable_incr_of_mem (Finset.mem_singleton_self s)).comap_le.trans
        (le_iSup (fun I : Finset ℝ≥0 => incrSigma X t I) {s})
    · refine iSup_le fun I => iSup₂_le fun s _hs => ?_
      have : Measurable[MeasurableSpace.comap (smPath X (fun _ => t)) MeasurableSpace.pi]
          fun ω => X (t + s) ω - X t ω :=
        (measurable_pi_apply s).comp (comap_measurable (smPath X (fun _ => t)))
      exact this.comap_le
  rw [hpath]
  refine (indep_iSup_of_directed_le (fun I => (indep_incrSigma hB t I).symm)
    (fun I => incrSigma_le hX t I) (𝓖.le t) ?_).symm
  exact (incrSigma_mono t).directed_le

end Future

/-! ### A continuous version in the usual augmentation -/

section Version

variable {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- A measurable function almost everywhere equal to an `m`-measurable one is `m`-measurable when `m`
contains the measurable null sets. -/
theorem measurable_of_ae_eq_of_null {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hnull : ∀ s, MeasurableSet[mΩ] s → P s = 0 → MeasurableSet[m] s)
    {f g : Ω → ℝ} (hf : Measurable[m] f) (hg : Measurable[mΩ] g) (hfg : f =ᵐ[P] g) :
    Measurable[m] g := by
  intro D hD
  set N : Set Ω := {ω | f ω ≠ g ω} with hN
  have hNm : MeasurableSet[mΩ] N := (measurableSet_eq_fun (hf.mono hm le_rfl) hg).compl
  have hN0 : P N = 0 := ae_iff.1 hfg
  have e : g ⁻¹' D = (f ⁻¹' D ∩ Nᶜ) ∪ (g ⁻¹' D ∩ N) := by
    ext ω
    by_cases h : f ω = g ω <;> simp [hN, h]
  rw [e]
  exact ((hf hD).inter (hnull N hNm hN0).compl).union
    (hnull _ ((hg hD).inter hNm) (measure_mono_null inter_subset_right hN0))

/-- Independence of `σ(f)` from `m` passes to an almost everywhere equal `g`. -/
theorem indep_comap_congr {m : MeasurableSpace Ω} {f g : Ω → ℝ} (hfg : f =ᵐ[P] g)
    (h : Indep (MeasurableSpace.comap f inferInstance) m P) :
    Indep (MeasurableSpace.comap g inferInstance) m P := by
  rw [Indep_iff] at h ⊢
  rintro _ G ⟨D, hD, rfl⟩ hG
  have e : (g ⁻¹' D : Set Ω) =ᵐ[P] f ⁻¹' D := by
    filter_upwards [hfg] with ω hω
    show (g ω ∈ D) = (f ω ∈ D)
    rw [hω]
  rw [measure_congr e, measure_congr (e.inter (EventuallyEq.refl _ G))]
  exact h _ _ ⟨D, hD, rfl⟩ hG

/-- **A continuous version.** A Brownian motion of `𝓕` has a version with every path continuous that is a
Brownian motion of the usual augmentation of `𝓕`. -/
theorem exists_continuous_version (hB : IsFilteredBrownianReal 𝓕 B P) :
    ∃ B' : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B' t)) ∧ (∀ ω, Continuous (B' · ω)) ∧
      IsFilteredBrownianReal (usualAugmentation 𝓕 P) B' P ∧ ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω := by
  obtain ⟨B', hm, hc, -, hBM, hae⟩ := QuantumZipper.RS.exists_good_version0 hB.1
  have hU := Ito.isFilteredBrownianReal_usualAugmentation hB
  have hae' : ∀ t, B t =ᵐ[P] B' t := fun t => hae.mono fun ω h => (h t).symm
  refine ⟨B', hm, hc, ⟨hBM, fun t => ?_, fun s t hst => ?_⟩, hae⟩
  · exact measurable_of_ae_eq_of_null ((usualAugmentation 𝓕 P).le t)
      (fun S hS h0 => Ito.measurableSet_usualAugmentation_of_null hS h0 t) (hU.2.1 t) (hm t)
      (hae' t)
  · refine indep_comap_congr ?_ (hU.2.2 s t hst)
    filter_upwards [hae] with ω h
    simp [h]

end Version

/-! ### The restarted filtration `s ↦ 𝓕_{T+s}` -/

section RestartFiltration

variable {𝓕 : Filtration ℝ≥0 mΩ} {T : Ω → ℝ≥0}

/-- `T + s` is a stopping time. -/
theorem isStoppingTime_add_const (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (s : ℝ≥0) :
    IsStoppingTime 𝓕 fun ω => ((T ω + s : ℝ≥0) : WithTop ℝ≥0) := by
  intro u
  by_cases hs : s ≤ u
  · have e : {ω | ((T ω + s : ℝ≥0) : WithTop ℝ≥0) ≤ u} =
        {ω | (T ω : WithTop ℝ≥0) ≤ ((u - s : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
      exact (le_tsub_iff_right hs).symm
    rw [e]
    exact 𝓕.mono tsub_le_self _ (hT (u - s))
  · have e : {ω | ((T ω + s : ℝ≥0) : WithTop ℝ≥0) ≤ u} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_empty_iff_false, iff_false, not_le]
      exact (lt_of_not_ge hs).trans_le le_add_self
    rw [e]
    exact @MeasurableSet.empty Ω (𝓕 u)

/-- The filtration `s ↦ 𝓕_{T+s}` of the σ-algebras of the stopping times `T + s`. -/
def restartFiltration (𝓕 : Filtration ℝ≥0 mΩ) (T : Ω → ℝ≥0)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) : Filtration ℝ≥0 mΩ where
  seq s := (isStoppingTime_add_const hT s).measurableSpace
  mono' _ _ hss' := IsStoppingTime.measurableSpace_mono _ _ fun _ =>
    WithTop.coe_le_coe.2 (add_le_add le_rfl hss')
  le' _ := IsStoppingTime.measurableSpace_le _

theorem restartFiltration_apply (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (s : ℝ≥0) :
    restartFiltration 𝓕 T hT s = (isStoppingTime_add_const hT s).measurableSpace := rfl

theorem restartFiltration_zero (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) :
    restartFiltration 𝓕 T hT 0 = hT.measurableSpace := by
  ext S
  rw [restartFiltration_apply, IsStoppingTime.measurableSet, IsStoppingTime.measurableSet]
  simp only [add_zero]

theorem measurableSpace_le_restartFiltration (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (s : ℝ≥0) : hT.measurableSpace ≤ restartFiltration 𝓕 T hT s := by
  rw [← restartFiltration_zero hT]
  exact (restartFiltration 𝓕 T hT).mono bot_le

theorem restartFiltration_mono {𝓖 : Filtration ℝ≥0 mΩ} (h : 𝓕 ≤ 𝓖)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hT' : IsStoppingTime 𝓖 fun ω => (T ω : WithTop ℝ≥0)) :
    restartFiltration 𝓕 T hT ≤ restartFiltration 𝓖 T hT' := fun _ =>
  Ito.measurableSpace_le_of_filtration_le h (isStoppingTime_add_const hT _)
    (isStoppingTime_add_const hT' _)

/-- The value at `T + s` of a progressive process is `𝓕_{T+s}`-measurable. -/
theorem measurable_restart_eval {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyProgressive 𝓕 X)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (s : ℝ≥0) :
    Measurable[restartFiltration 𝓕 T hT s] fun ω => X (T ω + s) ω := by
  have h := measurable_stoppedValue hX (isStoppingTime_add_const hT s)
  have e : (fun ω => X (T ω + s) ω) = stoppedValue X fun ω => ((T ω + s : ℝ≥0) : WithTop ℝ≥0) := by
    funext ω
    rfl
  rw [e]
  exact h

/-- The value at `T` of a progressive process is `𝓕_{T+s}`-measurable for every `s`. -/
theorem measurable_restart_eval_zero {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyProgressive 𝓕 X)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (s : ℝ≥0) :
    Measurable[restartFiltration 𝓕 T hT s] fun ω => X (T ω) ω := by
  have h := measurable_stoppedValue hX hT
  have e : (fun ω => X (T ω) ω) = stoppedValue X fun ω => (T ω : WithTop ℝ≥0) := by
    funext ω
    rfl
  rw [e]
  exact (h.mono (measurableSpace_le_restartFiltration hT s) le_rfl)

end RestartFiltration

/-! ### The strong Markov property under a conditional measure -/

section StrongMarkov

variable {𝓖 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0}

/-- **Strong Markov property, filtered form.** Let `B` be a Brownian motion of `𝓖` with every path
continuous, `T` a finite stopping time and `A ∈ 𝓖_T` with `P A ≠ 0`. Under `P[·|A]`, the restarted
process `B_{T+·} − B_T` is a Brownian motion of the filtration `s ↦ 𝓖_{T+s}`. -/
theorem isFilteredBrownianReal_restart_cond (hB : IsFilteredBrownianReal 𝓖 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hT : IsStoppingTime 𝓖 fun ω => (T ω : WithTop ℝ≥0))
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A) (hPA : P A ≠ 0) :
    IsFilteredBrownianReal (restartFiltration 𝓖 T hT) (smShift B T) (P[|A]) := by
  have := hB.isProbabilityMeasure'
  have hBm : ∀ t, Measurable (B t) := hB.measurable'
  have hind := indep_future hB
  have hpre := hB.1.toIsPreBrownianReal
  have hprog : IsStronglyProgressive 𝓖 B :=
    isStronglyProgressive_of_rightContinuous (fun t => (hB.2.1 t).stronglyMeasurable)
      fun ω _ => (hBc ω).continuousWithinAt
  refine ⟨⟨IsPreBrownianReal.mk' fun I => ?_, ae_of_all _ fun ω =>
    ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const⟩, fun s => ?_,
    fun s t hst => ?_⟩
  · have hgm : Measurable fun ω => I.restrict (smPath B T ω) :=
      (Finset.measurable_restrict I).comp
        (measurable_smPath hBc hBm (measurable_of_isStoppingTime hT))
    refine ⟨hgm.aemeasurable, ?_⟩
    have h := map_restrict_finite_eq hpre hBc hBm hind hT hA I
    change (P[|A]).map (fun ω => I.restrict (smPath B T ω)) = _
    rw [ProbabilityTheory.cond, Measure.map_smul, h, smul_smul,
      ENNReal.inv_mul_cancel hPA (measure_ne_top _ _), one_smul]
    all_goals exact hgm.aemeasurable
  · exact (measurable_restart_eval hprog hT s).sub (measurable_restart_eval_zero hprog hT s)
  · have hTs := isStoppingTime_add_const hT s
    have h := indep_smPath hpre hBc hBm hind hTs
    have heq : (fun ω => smShift B T t ω - smShift B T s ω) =
        smShift B (fun ω => T ω + s) (t - s) := by
      funext ω
      simp only [smShift]
      rw [add_assoc, add_tsub_cancel_of_le hst]
      ring
    have hle : MeasurableSpace.comap (fun ω => smShift B T t ω - smShift B T s ω) inferInstance ≤
        MeasurableSpace.comap (smPath B (fun ω => T ω + s)) MeasurableSpace.pi := by
      rw [heq]
      exact ((measurable_pi_apply (t - s)).comp
        (comap_measurable (smPath B (fun ω => T ω + s)))).comap_le
    have hA' : MeasurableSet[hTs.measurableSpace] A :=
      IsStoppingTime.measurableSpace_mono hT hTs (fun ω => WithTop.coe_le_coe.2 le_self_add) _ hA
    exact indep_cond hTs.measurableSpace_le (indep_of_indep_of_le_left h.symm hle) hA'

end StrongMarkov

end Restart

end Sec2

end InteractingSLE
