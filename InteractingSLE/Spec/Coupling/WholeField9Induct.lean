/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField9Birth

/-!
# C.4 for every `κ > 0`: all pockets, in conditional-mean form

Packet PROVE-WHOLEFIELD9 (follow-up note C.4, `source/external/AstraIG1/ig1_followup_proofs.txt` L1651–1704; ruling
R38). PROVE-WHOLEFIELD7's induction on the number of pocket labels (`WholeField7Induct`), with the kernel value written
with the conditional mean (`cmKer`) instead of the `κ = 4` bounded frozen mean.

* `gaussCF_mul_gaussCF`, `ae_condExp_exp_eq_cmKer_of_active`, `ae_cmKer_add_of_active`: the active base case and the
  active factor;
* `ae_condExp_exp_eq_cmKer_pocket_step`, `ae_condExp_exp_eq_cmKer_succ`: the induction;
* **`ae_condExp_exp_eq_cmKer_of_isLabel`**: for the frozen coupling with any `κ > 0`, finitely many deterministic tests
  `ψ_k`, a bounded driving stop `σ < ζ` and a real `c`: almost surely, if every `supp ψ_k` is a label at `σ`, then
  `E[e^{i(h, c ∑ ψ_k)} | 𝓕_σ] = exp(i E[(h, c ∑ ψ_k) | 𝓕_σ] − ½ Q_{U_σ}(c ∑ ψ_k))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Ito Coupling

theorem gaussCF_mul_gaussCF (a q b r : ℝ) :
    WangWu.gaussCF a q * WangWu.gaussCF b r = WangWu.gaussCF (a + b) (q + r) := by
  unfold WangWu.gaussCF
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

section Induct

universe v

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {ι : Type*}

/-- **The active base case in `cmKer` form**: almost surely on `{supp ψ ∩ K_σ = ∅}`,
`E[e^{i(h,ψ)} | 𝓕_σ] = cmKer_σ(ψ)`. -/
theorem ae_condExp_exp_eq_cmKer_of_active (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) →
      (P[fun ω' => cexp (Complex.I * (h ω' ψ : ℂ)) | hσ.measurableSpace]) ω =
        cmKer P hσ.measurableSpace h W (σ ω) ψ ω := by
  filter_upwards [ae_condExp_exp_eq_gaussCF_actMean hC hX hσ hσζ ψ,
    ae_condExp_pairing_eq_actMean hC hX hσ hσζ ψ] with ω h1 h2 hd
  rw [h1 hd, cmKer, h2 hd]

/-- **The active factor in `cmKer` form**: almost surely, if `ψA` is an active label and `supp ψP ⊆ K_σ`, and the
pocket part has the kernel value, so does the sum. -/
theorem ae_cmKer_add_of_active (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (ψA ψP : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, IsActiveLabel (W · ω) (tsupport ψA) (σ ω) →
      tsupport ψP ⊆ fwdHull (Ito.rpath (W · ω)) (σ ω) →
      (P[fun ω' => cexp (Complex.I * (h ω' ψP : ℂ)) | hσ.measurableSpace]) ω =
        cmKer P hσ.measurableSpace h W (σ ω) ψP ω →
      (P[fun ω' => cexp (Complex.I * (h ω' (ψA + ψP) : ℂ)) | hσ.measurableSpace]) ω =
        cmKer P hσ.measurableSpace h W (σ ω) (ψA + ψP) ω := by
  have hint := integrable_pairing hC
  have hadd := condExp_add (m := hσ.measurableSpace) (hint ψA) (hint ψP)
  filter_upwards [ae_condExp_exp_add_eq_of_active' hC hκ hu₀ hX hσ hσζ ψA ψP,
    ae_condExp_pairing_eq_actMean hC hX hσ hσζ ψA, hadd, hC.1.2.2.2.2, hσζ] with ω h1 h2 h3 hp hlt hA hPK hP
  have hd : Disjoint (tsupport ψA) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) := hA
  rw [h1 hA hPK, hP, cmKer, cmKer, ← h2 hd, gaussCF_mul_gaussCF]
  have e1 : (fun ω' => h ω' (ψA + ψP)) = (fun ω' => h ω' ψA) + fun ω' => h ω' ψP := by
    funext ω'; simp [map_add]
  rw [e1, h3, Pi.add_apply,
    show (⇑(ψA + ψP) : ℂ → ℝ) = ⇑ψA + ⇑ψP from rfl,
    retainedGreenEnergy_add_of_active hp.2.2.2.1 hp.1 hlt hA hPK]

open scoped Classical in
/-- The claim of the induction: for every real `c`, the kernel identity for `c ∑_{k∈s} ψ_k` at every bounded driving
stop, almost surely on `{all labels, at most p non-active}`. -/
def CmClaim (P : Measure Ω) (hX : IsMeasurableKilledDriving W VL VR ζ) (h : Ω → DistOn upperHalfPlaneOpens)
    (ψ : ι → TestOn upperHalfPlaneOpens) (p : ℕ) : Prop :=
  ∀ (c : ℝ) (s : Finset ι) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0)),
    (∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) → ∀ N : ℝ≥0, (∀ ω, σ ω ≤ N) →
    ∀ᵐ ω ∂P, (∀ k ∈ s, IsLabel (W · ω) (tsupport (ψ k)) (σ ω)) →
      (s.filter fun k => ¬ IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω)).card ≤ p →
      (P[fun ω' => cexp (Complex.I * (h ω' (c • ∑ k ∈ s, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
        cmKer P hσ.measurableSpace h W (σ ω) (c • ∑ k ∈ s, ψ k) ω

open scoped Classical in
/-- **The pocket part of the induction step** (conditional-mean form). -/
theorem ae_condExp_exp_eq_cmKer_pocket_step (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (ψ : ι → TestOn upperHalfPlaneOpens) (p : ℕ)
    (hIH : CmClaim P hX h ψ p) {Poc I : Finset ι} (hIP : I ⊆ Poc) (hIne : I.Nonempty) (hcard : Poc.card ≤ p + 1)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ β : ℝ≥0, β ≤ σ ω →
      (∀ k ∈ I, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = β) →
      (∀ k ∈ Poc \ I, ∃ βk < β, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = βk) →
      (P[fun ω' => cexp (Complex.I * (h ω' (c • ∑ k ∈ Poc, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
        cmKer P hσ.measurableSpace h W (σ ω) (c • ∑ k ∈ Poc, ψ k) ω := by
  have hsplit : (∑ k ∈ Poc, ψ k) = (∑ k ∈ I, ψ k) + ∑ k ∈ Poc \ I, ψ k := by
    rw [add_comm, Finset.sum_sdiff hIP]
  have hJcard : (Poc \ I).card ≤ p := by
    have h1 := Finset.card_sdiff_add_card_eq_card hIP
    have h2 := hIne.card_pos
    omega
  rw [hsplit]
  by_cases hI0 : tsupport (⇑(∑ k ∈ I, ψ k)) = ∅
  · have hψI : (∑ k ∈ I, ψ k) = 0 := by
      ext z
      exact image_eq_zero_of_notMem_tsupport (by rw [hI0]; exact notMem_empty z)
    rw [hψI, zero_add]
    filter_upwards [hIH c (Poc \ I) σ hσ hσζ N hσN] with ω hω β hβσ _ hJ
    refine hω (fun k hk => Or.inr ?_) ((Finset.card_filter_le _ _).trans hJcard)
    obtain ⟨βk, hβk, hs⟩ := hJ k hk
    exact ⟨βk, hβk.le.trans hβσ, hs⟩
  have hIne' : (tsupport ⇑(∑ k ∈ I, ψ k)).Nonempty := nonempty_iff_ne_empty.2 hI0
  have hb := (ae_condExp_exp_eq_cmKer_of_birth hC hκ hu₀ hX hσ hσζ hσN (∑ k ∈ I, ψ k) (∑ k ∈ Poc \ I, ψ k)
    (fun t ω => (∀ k ∈ I, IsActiveLabel (W · ω) (tsupport (ψ k)) t) ∧
      ∀ k ∈ Poc \ I, IsPocketLabel (W · ω) (tsupport (ψ k)) t)
    (fun ω β => (∀ k ∈ I, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = β) ∧
      ∀ k ∈ Poc \ I, ∃ βk < β, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = βk)
    (fun c' τ hτ hτζ hτN => by
      filter_upwards [hIH c' Poc τ hτ hτζ (N + 1) hτN] with ω hω hQ
      rw [← hsplit]
      refine hω (fun k hk => ?_) ?_
      · by_cases hkI : k ∈ I
        · exact Or.inl (hQ.1 k hkI)
        · exact Or.inr (hQ.2 k (Finset.mem_sdiff.2 ⟨hk, hkI⟩))
      · refine (Finset.card_le_card fun k hk => ?_).trans hJcard
        obtain ⟨hkP, hna⟩ := Finset.mem_filter.1 hk
        exact Finset.mem_sdiff.2 ⟨hkP, fun hkI => hna (hQ.1 k hkI)⟩)
    (fun ω β hβ hEv => by
      obtain ⟨hI, hJ⟩ := hEv
      choose! βk hβk hsk using hJ
      refine ⟨(Poc \ I).sup βk, (Finset.sup_lt_iff hβ).2 fun k hk => hβk k hk,
        fun t ht0 htβ => ⟨fun k hk => ?_, fun k hk => ⟨βk k, (Finset.le_sup hk).trans ht0, hsk k hk⟩⟩⟩
      exact isActiveLabel_of_lt_swallowTime (w := (W · ω)) fun z hz => by
        rw [hI k hk z hz]; exact_mod_cast htβ)).1 c
  filter_upwards [hb] with ω hω β hβσ hI hJ
  refine hω β hβσ ⟨hI, hJ⟩ ⟨hIne', fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (tsupport_sum_subset I ψ hz)
    exact hI k hk z hzk
  · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (tsupport_sum_subset (Poc \ I) ψ hz)
    obtain ⟨βk, hβk, hs⟩ := hJ k hk
    rw [hs z hzk]
    exact_mod_cast hβk

open scoped Classical in
/-- **The induction step** (conditional-mean form). -/
theorem ae_condExp_exp_eq_cmKer_succ (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (ψ : ι → TestOn upperHalfPlaneOpens) (p : ℕ)
    (hIH : CmClaim P hX h ψ p) : CmClaim P hX h ψ (p + 1) := by
  intro c s σ hσ hσζ N hσN
  have hpocket : ∀ᵐ ω ∂P, ∀ x ∈ s.powerset ×ˢ s.powerset, x.2 ⊆ x.1 → x.2.Nonempty →
      x.1.card ≤ p + 1 → ∀ β : ℝ≥0, β ≤ σ ω →
      (∀ k ∈ x.2, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = β) →
      (∀ k ∈ x.1 \ x.2, ∃ βk < β, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = βk) →
      (P[fun ω' => cexp (Complex.I * (h ω' (c • ∑ k ∈ x.1, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
        cmKer P hσ.measurableSpace h W (σ ω) (c • ∑ k ∈ x.1, ψ k) ω := by
    rw [Filter.eventually_all_finset]
    intro x _
    by_cases hc : x.2 ⊆ x.1 ∧ x.2.Nonempty ∧ x.1.card ≤ p + 1
    · filter_upwards [ae_condExp_exp_eq_cmKer_pocket_step hC hκ hu₀ hX ψ p hIH hc.1 hc.2.1 hc.2.2 hσ hσζ hσN c]
        with ω hω _ _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc
  have hact : ∀ᵐ ω ∂P, ∀ Poc ∈ s.powerset,
      IsActiveLabel (W · ω) (tsupport ⇑(c • ∑ k ∈ s \ Poc, ψ k)) (σ ω) →
      tsupport ⇑(c • ∑ k ∈ Poc, ψ k) ⊆ fwdHull (Ito.rpath (W · ω)) (σ ω) →
      (P[fun ω' => cexp (Complex.I * (h ω' (c • ∑ k ∈ Poc, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
        cmKer P hσ.measurableSpace h W (σ ω) (c • ∑ k ∈ Poc, ψ k) ω →
      (P[fun ω' => cexp (Complex.I * (h ω' (c • (∑ k ∈ s \ Poc, ψ k) + c • ∑ k ∈ Poc, ψ k) : ℂ)) |
        hσ.measurableSpace]) ω =
        cmKer P hσ.measurableSpace h W (σ ω) (c • (∑ k ∈ s \ Poc, ψ k) + c • ∑ k ∈ Poc, ψ k) ω := by
    rw [Filter.eventually_all_finset]
    exact fun Poc _ => ae_cmKer_add_of_active hC hκ hu₀ hX hσ hσζ _ _
  filter_upwards [hIH c s σ hσ hσζ N hσN, hpocket, hact] with ω h0 hpk hac hlab hcard
  by_cases hc : (s.filter fun k => ¬ IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω)).card ≤ p
  · exact h0 hlab hc
  set Poc := s.filter fun k => ¬ IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω) with hPocdef
  have hPs : Poc ⊆ s := Finset.filter_subset _ _
  have hne : Poc.Nonempty := Finset.card_pos.1 (by omega)
  have hpoc : ∀ k ∈ Poc, IsPocketLabel (W · ω) (tsupport (ψ k)) (σ ω) := fun k hk => by
    obtain ⟨hks, hna⟩ := Finset.mem_filter.1 hk
    exact (hlab k hks).resolve_left hna
  choose! βk hβkσ hβks using hpoc
  set β : ℝ≥0 := Poc.sup' hne βk with hβdef
  set I := Poc.filter fun k => βk k = β with hIdef
  have hIP : I ⊆ Poc := Finset.filter_subset _ _
  obtain ⟨k₀, hk₀, hk₀eq⟩ := Finset.exists_mem_eq_sup' hne βk
  have hIne : I.Nonempty := ⟨k₀, Finset.mem_filter.2 ⟨hk₀, hk₀eq.symm⟩⟩
  have hβσ : β ≤ σ ω := Finset.sup'_le hne _ fun k hk => hβkσ k hk
  have hpart := hpk (Poc, I) (Finset.mem_product.2 ⟨Finset.mem_powerset.2 hPs,
    Finset.mem_powerset.2 (hIP.trans hPs)⟩) hIP hIne (show Poc.card ≤ p + 1 from hcard) β hβσ
    (fun k hk z hz => by
      obtain ⟨hkP, hkβ⟩ := Finset.mem_filter.1 hk
      rw [hβks k hkP z hz, hkβ])
    (fun k hk => by
      obtain ⟨hkP, hkI⟩ := Finset.mem_sdiff.1 hk
      refine ⟨βk k, lt_of_le_of_ne (Finset.le_sup' βk hkP) fun he => hkI (Finset.mem_filter.2 ⟨hkP, he⟩),
        hβks k hkP⟩)
  have hA : IsActiveLabel (W · ω) (tsupport ⇑(∑ k ∈ s \ Poc, ψ k)) (σ ω) := by
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (tsupport_sum_subset (s \ Poc) ψ hz)
    obtain ⟨hks, hkP⟩ := Finset.mem_sdiff.1 hk
    have hak : IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω) := by
      by_contra hna; exact hkP (Finset.mem_filter.2 ⟨hks, hna⟩)
    exact Set.disjoint_left.1 hak hzk hzK
  have hPK : tsupport ⇑(∑ k ∈ Poc, ψ k) ⊆ fwdHull (Ito.rpath (W · ω)) (σ ω) := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (tsupport_sum_subset Poc ψ hz)
    exact (show IsPocketLabel (W · ω) (tsupport (ψ k)) (σ ω) from ⟨βk k, hβkσ k hk, hβks k hk⟩).subset_fwdHull
      (ψ k).tsupport_subset hzk
  have hsum : c • (∑ k ∈ s, ψ k) = c • (∑ k ∈ s \ Poc, ψ k) + c • ∑ k ∈ Poc, ψ k := by
    rw [← smul_add, Finset.sum_sdiff hPs]
  rw [hsum]
  exact hac Poc (Finset.mem_powerset.2 hPs)
    (hA.mono (tsupport_smul_subset_right (fun _ => c) _))
    ((tsupport_smul_subset_right (fun _ => c) _).trans hPK) hpart

open scoped Classical in
/-- **C.4 for every `κ > 0` (conditional-mean form): the whole-field kernel on finitely many labels.** For the frozen
coupling, finitely many deterministic test functions `ψ_k`, `k ∈ s`, a bounded driving stop `σ < ζ` and a real `c`:
almost surely, if every `supp ψ_k` is a label at `σ` (active, or a pocket swallowed at once), then
`E[e^{i(h, c ∑ ψ_k)} | 𝓕_σ] = exp(i E[(h, c ∑ ψ_k) | 𝓕_σ] − ½ Q_{U_σ}(c ∑ ψ_k))`. -/
theorem ae_condExp_exp_eq_cmKer_of_isLabel (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) (ψ : ι → TestOn upperHalfPlaneOpens)
    (s : Finset ι) {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N) (c : ℝ) :
    ∀ᵐ ω ∂P, (∀ k ∈ s, IsLabel (W · ω) (tsupport (ψ k)) (σ ω)) →
      (P[fun ω' => cexp (Complex.I * (h ω' (c • ∑ k ∈ s, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
        cmKer P hσ.measurableSpace h W (σ ω) (c • ∑ k ∈ s, ψ k) ω := by
  obtain ⟨u₀, hu₀⟩ := exists_bhe κ ρL ρR xL xR
  have key : ∀ p : ℕ, CmClaim P hX h ψ p := by
    intro p
    induction p with
    | zero =>
      intro c s σ hσ hσζ N hσN
      filter_upwards [ae_condExp_exp_eq_cmKer_of_active hC hX hσ hσζ (c • ∑ k ∈ s, ψ k)] with ω hω _ hcard
      refine hω (Set.disjoint_left.2 fun z hz hzK => ?_)
      obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (tsupport_sum_subset s ψ (tsupport_smul_subset_right (fun _ => c) _ hz))
      have hak : IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω) := by
        by_contra hna
        have hmem : k ∈ s.filter fun k => ¬ IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω) :=
          Finset.mem_filter.2 ⟨hk, hna⟩
        rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)] at hmem
        exact Finset.notMem_empty _ hmem
      exact Set.disjoint_left.1 hak hzk hzK
    | succ p ih => exact ae_condExp_exp_eq_cmKer_succ hC hκ hu₀ hX ψ p ih
  filter_upwards [key s.card c s σ hσ hσζ N hσN] with ω hω hlab
  exact hω hlab (Finset.card_filter_le _ _)

end Induct
