/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField7Birth

/-!
# C.4 at `κ = 4`: the whole-field kernel on finitely many labels, by induction on the pockets

Packet PROVE-WHOLEFIELD7 (follow-up note C.4, `source/external/AstraIG1/ig1_followup_proofs.txt` L1651–1704; ruling
R38).

**Statement** (`ae_condExp_exp_eq_kerCF_of_isLabel`). Let `ψ_k`, `k ∈ s`, be finitely many deterministic test
functions and `σ < ζ` a bounded stopping time of the driving filtration. Almost surely, if at time `σ` every support
`supp ψ_k` is a label (it avoids the hull `K_σ`, or all its points were swallowed at one time), then

  `E[e^{i(h, ∑ ψ_k)} | 𝓕_σ] = exp(i ∫ η̄_σ ∑ ψ_k − ½ Q_{U_σ}(∑ ψ_k))` (`kerCF`),

with Wang–Wu's frozen mean `η̄_σ` (frozen in each pocket at its birth) and the retained Green form `Q_{U_σ}`.

**Proof: induction on the number `p` of labels that are pockets** (no batches, no pasting of σ-algebras). `p = 0` is
the frozen kernel of Theorem 1.1 for an active test. For `p + 1` pockets, on the event where the pockets are `Poc` and
the ones born last are `I ⊆ Poc` (born at `β`), the pocket sum `∑_{Poc} ψ_k` is handled by the birth step
`ae_condExp_exp_eq_kerCF_of_birth`, whose induction hypothesis — at the announcing stops before `β`, where `I` is active
and `Poc \ I` are at most `p` pockets — is the claim for `p`; the active labels are added by the active factor
`ae_condExp_exp_add_eq_of_active` and recombined by `kerCF_add_of_active`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Ito Coupling

section Induct

universe v

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {ι : Type*}

open scoped Classical in
/-- **The pocket part of the induction step.** Given the claim for at most `p` pockets (`hIH`), for pockets `Poc`
(at most `p + 1`) of which `I ≠ ∅` are born last, at `β ≤ σ`, and the others earlier: almost surely
`E[e^{i(h, ∑_{Poc} ψ_k)} | 𝓕_σ] = kerCF_σ(∑_{Poc} ψ_k)`. -/
theorem ae_condExp_exp_eq_kerCF_pocket_step
    (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (ψ : ι → TestOn upperHalfPlaneOpens) (p : ℕ)
    (hIH : ∀ (s : Finset ι) (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0)),
      (∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) → ∀ N : ℝ≥0, (∀ ω, σ ω ≤ N) →
      ∀ᵐ ω ∂P, (∀ k ∈ s, IsLabel (W · ω) (tsupport (ψ k)) (σ ω)) →
        (s.filter fun k => ¬ IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω)).card ≤ p →
        (P[fun ω' => Complex.exp (Complex.I * (h ω' (∑ k ∈ s, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
          kerCF ρL ρR W VL VR (σ ω) (⇑(∑ k ∈ s, ψ k)) ω)
    {Poc I : Finset ι} (hIP : I ⊆ Poc) (hIne : I.Nonempty) (hcard : Poc.card ≤ p + 1) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N) :
    ∀ᵐ ω ∂P, ∀ β : ℝ≥0, β ≤ σ ω →
      (∀ k ∈ I, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = β) →
      (∀ k ∈ Poc \ I, ∃ βk < β, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = βk) →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' (∑ k ∈ Poc, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
        kerCF ρL ρR W VL VR (σ ω) (⇑(∑ k ∈ Poc, ψ k)) ω := by
  have hsplit : (∑ k ∈ Poc, ψ k) = (∑ k ∈ I, ψ k) + ∑ k ∈ Poc \ I, ψ k := by
    rw [add_comm, Finset.sum_sdiff hIP]
  have hJcard : (Poc \ I).card ≤ p := by
    have h1 := Finset.card_sdiff_add_card_eq_card hIP
    have h2 := hIne.card_pos
    omega
  rw [hsplit]
  by_cases hI0 : tsupport (⇑(∑ k ∈ I, ψ k)) = ∅
  · -- the last-born supports cancel: fewer pockets
    have hψI : (∑ k ∈ I, ψ k) = 0 := by
      ext z
      exact image_eq_zero_of_notMem_tsupport (by rw [hI0]; exact notMem_empty z)
    rw [hψI, zero_add]
    filter_upwards [hIH (Poc \ I) σ hσ hσζ N hσN] with ω hω β hβσ _ hJ
    refine hω (fun k hk => Or.inr ?_) ((Finset.card_filter_le _ _).trans hJcard)
    obtain ⟨βk, hβk, hs⟩ := hJ k hk
    exact ⟨βk, hβk.le.trans hβσ, hs⟩
  have hIne' : (tsupport ⇑(∑ k ∈ I, ψ k)).Nonempty := nonempty_iff_ne_empty.2 hI0
  have hb := ae_condExp_exp_eq_kerCF_of_birth hC hu₀ hX hσ hσζ hσN (∑ k ∈ I, ψ k) (∑ k ∈ Poc \ I, ψ k)
    (fun t ω => (∀ k ∈ I, IsActiveLabel (W · ω) (tsupport (ψ k)) t) ∧
      ∀ k ∈ Poc \ I, IsPocketLabel (W · ω) (tsupport (ψ k)) t)
    (fun ω β => (∀ k ∈ I, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = β) ∧
      ∀ k ∈ Poc \ I, ∃ βk < β, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = βk)
    (fun τ hτ hτζ hτN => by
      filter_upwards [hIH Poc τ hτ hτζ (N + 1) hτN] with ω hω hQ
      rw [← hsplit]
      refine hω (fun k hk => ?_) ?_
      · by_cases hkI : k ∈ I
        · exact Or.inl (hQ.1 k hkI)
        · exact Or.inr (hQ.2 k (Finset.mem_sdiff.2 ⟨hk, hkI⟩))
      · refine (Finset.card_le_card fun k hk => ?_).trans hJcard
        obtain ⟨hkP, hna⟩ := Finset.mem_filter.1 hk
        refine Finset.mem_sdiff.2 ⟨hkP, fun hkI => hna (hQ.1 k hkI)⟩)
    (fun ω β hβ hEv => by
      obtain ⟨hI, hJ⟩ := hEv
      choose! βk hβk hsk using hJ
      refine ⟨(Poc \ I).sup βk, (Finset.sup_lt_iff hβ).2 fun k hk => hβk k hk,
        fun t ht0 htβ => ⟨fun k hk => ?_, fun k hk => ⟨βk k, (Finset.le_sup hk).trans ht0, hsk k hk⟩⟩⟩
      exact isActiveLabel_of_lt_swallowTime (w := (W · ω)) fun z hz => by
        rw [hI k hk z hz]; exact_mod_cast htβ)
  filter_upwards [hb] with ω hω β hβσ hI hJ
  refine hω β hβσ ⟨hI, hJ⟩ ⟨hIne', fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (tsupport_sum_subset I ψ hz)
    exact hI k hk z hzk
  · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (tsupport_sum_subset (Poc \ I) ψ hz)
    obtain ⟨βk, hβk, hs⟩ := hJ k hk
    rw [hs z hzk]
    exact_mod_cast hβk

open scoped Classical in
/-- **The induction step**: the claim for at most `p` pockets gives the claim for at most `p + 1` pockets. -/
theorem ae_condExp_exp_eq_kerCF_succ (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (ψ : ι → TestOn upperHalfPlaneOpens) (p : ℕ)
    (hIH : ∀ (s : Finset ι) (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0)),
      (∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) → ∀ N : ℝ≥0, (∀ ω, σ ω ≤ N) →
      ∀ᵐ ω ∂P, (∀ k ∈ s, IsLabel (W · ω) (tsupport (ψ k)) (σ ω)) →
        (s.filter fun k => ¬ IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω)).card ≤ p →
        (P[fun ω' => Complex.exp (Complex.I * (h ω' (∑ k ∈ s, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
          kerCF ρL ρR W VL VR (σ ω) (⇑(∑ k ∈ s, ψ k)) ω)
    (s : Finset ι) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (N : ℝ≥0) (hσN : ∀ ω, σ ω ≤ N) :
    ∀ᵐ ω ∂P, (∀ k ∈ s, IsLabel (W · ω) (tsupport (ψ k)) (σ ω)) →
      (s.filter fun k => ¬ IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω)).card ≤ p + 1 →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' (∑ k ∈ s, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
        kerCF ρL ρR W VL VR (σ ω) (⇑(∑ k ∈ s, ψ k)) ω := by
  have hE := hC.1
  have hpocket : ∀ᵐ ω ∂P, ∀ x ∈ s.powerset ×ˢ s.powerset, x.2 ⊆ x.1 → x.2.Nonempty →
      x.1.card ≤ p + 1 → ∀ β : ℝ≥0, β ≤ σ ω →
      (∀ k ∈ x.2, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = β) →
      (∀ k ∈ x.1 \ x.2, ∃ βk < β, ∀ z ∈ tsupport (ψ k), swallowTime (Ito.rpath (W · ω)) z = βk) →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' (∑ k ∈ x.1, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
        kerCF ρL ρR W VL VR (σ ω) (⇑(∑ k ∈ x.1, ψ k)) ω := by
    rw [Filter.eventually_all_finset]
    intro x _
    by_cases hc : x.2 ⊆ x.1 ∧ x.2.Nonempty ∧ x.1.card ≤ p + 1
    · filter_upwards [ae_condExp_exp_eq_kerCF_pocket_step hC hu₀ hX ψ p hIH hc.1 hc.2.1 hc.2.2 hσ hσζ hσN]
        with ω hω _ _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc
  have hact : ∀ᵐ ω ∂P, ∀ Poc ∈ s.powerset, IsActiveLabel (W · ω) (tsupport ⇑(∑ k ∈ s \ Poc, ψ k)) (σ ω) →
      tsupport ⇑(∑ k ∈ Poc, ψ k) ⊆ fwdHull (Ito.rpath (W · ω)) (σ ω) →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' ((∑ k ∈ s \ Poc, ψ k) + ∑ k ∈ Poc, ψ k) : ℂ)) |
        hσ.measurableSpace]) ω =
        kerCF ρL ρR W VL VR (σ ω) (⇑(∑ k ∈ s \ Poc, ψ k)) ω *
          (P[fun ω' => Complex.exp (Complex.I * (h ω' (∑ k ∈ Poc, ψ k) : ℂ)) | hσ.measurableSpace]) ω := by
    rw [Filter.eventually_all_finset]
    exact fun Poc _ => ae_condExp_exp_add_eq_of_active hC hu₀ hX hσ hσζ _ _
  have hdu : drivingFiltration P hX ≤ usualAugmentation 𝓕 P := Ito.drivingFiltration_le_usualAugmentation hE hX
  have hmg := ae_isMeanGood hE (IsStoppingTime.mono_filtration hdu hσ) hσζ hσN
  filter_upwards [hIH s σ hσ hσζ N hσN, hpocket, hact, hmg, hE.2.2.2.2, hσζ] with ω h0 hpk hac hmω hp hlt
    hlab hcard
  by_cases hc : (s.filter fun k => ¬ IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω)).card ≤ p
  · exact h0 hlab hc
  -- exactly `p + 1` pockets
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
  -- the active labels
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
  have hsum : (∑ k ∈ s, ψ k) = (∑ k ∈ s \ Poc, ψ k) + ∑ k ∈ Poc, ψ k := (Finset.sum_sdiff hPs).symm
  have e1 := hac Poc (Finset.mem_powerset.2 hPs) hA hPK
  rw [hpart] at e1
  rw [hsum, e1]
  have e2 := kerCF_add_of_active (ρL := ρL) (ρR := ρR) (VL := VL) (VR := VR) hp hlt hmω hA hPK
  exact e2.symm

open scoped Classical in
/-- **C.4 at `κ = 4`: the whole-field kernel on finitely many labels.** For the frozen `κ = 4` coupling, finitely
many deterministic test functions `ψ_k`, `k ∈ s`, and a bounded driving stop `σ < ζ`: almost surely, if every
`supp ψ_k` is a label at `σ` (active, or a pocket swallowed at once), then
`E[e^{i(h, ∑ ψ_k)} | 𝓕_σ] = exp(i ∫ η̄_σ ∑ ψ_k − ½ Q_{U_σ}(∑ ψ_k))`. -/
theorem ae_condExp_exp_eq_kerCF_of_isLabel (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (ψ : ι → TestOn upperHalfPlaneOpens) (s : Finset ι)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N) :
    ∀ᵐ ω ∂P, (∀ k ∈ s, IsLabel (W · ω) (tsupport (ψ k)) (σ ω)) →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' (∑ k ∈ s, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
        kerCF ρL ρR W VL VR (σ ω) (⇑(∑ k ∈ s, ψ k)) ω := by
  have key : ∀ p : ℕ, ∀ (s : Finset ι) (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0)),
      (∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) → ∀ N : ℝ≥0, (∀ ω, σ ω ≤ N) →
      ∀ᵐ ω ∂P, (∀ k ∈ s, IsLabel (W · ω) (tsupport (ψ k)) (σ ω)) →
        (s.filter fun k => ¬ IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω)).card ≤ p →
        (P[fun ω' => Complex.exp (Complex.I * (h ω' (∑ k ∈ s, ψ k) : ℂ)) | hσ.measurableSpace]) ω =
          kerCF ρL ρR W VL VR (σ ω) (⇑(∑ k ∈ s, ψ k)) ω := by
    intro p
    induction p with
    | zero =>
      intro s σ hσ hσζ N hσN
      filter_upwards [ae_condExp_exp_eq_kerCF_of_active hC hX hσ hσζ (∑ k ∈ s, ψ k)] with ω hω _ hcard
      refine hω (Set.disjoint_left.2 fun z hz hzK => ?_)
      obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 (tsupport_sum_subset s ψ hz)
      have hak : IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω) := by
        by_contra hna
        have hmem : k ∈ s.filter fun k => ¬ IsActiveLabel (W · ω) (tsupport (ψ k)) (σ ω) :=
          Finset.mem_filter.2 ⟨hk, hna⟩
        rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)] at hmem
        exact Finset.notMem_empty _ hmem
      exact Set.disjoint_left.1 hak hzk hzK
    | succ p ih => exact ae_condExp_exp_eq_kerCF_succ hC hu₀ hX ψ p ih
  filter_upwards [key s.card s σ hσ hσζ N hσN] with ω hω hlab
  exact hω hlab (Finset.card_filter_le _ _)

end Induct

end WholeField

end InteractingSLE
