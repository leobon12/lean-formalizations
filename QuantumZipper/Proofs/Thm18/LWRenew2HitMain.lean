import QuantumZipper.Proofs.Thm18.LWRenew2HitMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWS-0′-HIT, part 5: the hitting time is a.s. a stopping time of the raw filtration

Classical fact: the hitting time of a closed set by a continuous adapted process is a stopping
time (Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Problem 1.2.7; Revuz–Yor,
*Continuous Martingales and Brownian Motion*, Prop. I.4.5). Here the closed set
`closure (c '' {j | ω ∈ M j})` is random (given by `𝓕_σ`-events), the process is the SLE trace
after the stopping time `σ`, and the trace is only **a.s.** continuous while the natural
filtration is not completed. We therefore run the countable criterion under the pathwise guard
`RadGuard` (part 3), which is an `𝓕_v`-event (part 4): `hitTime` is a stopping time for every
sample point (`isStoppingTime_hitTime`), and it equals the hitting time on the a.s. event of
Rohde–Schramm's radial bound (`RS.ae_sleTrace_good`; RS Thm 3.6, 5.1). The guard device is own
bookkeeping replacing the completion of the filtration.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- The guarded hitting event at level `C` by time `u`. -/
def hitEv (κ δ : ℝ) (B : ℝ≥0 → Ω → ℝ) (σ : Ω → WithTop ℝ≥0) (c : ℕ → ℂ) (M : ℕ → Set Ω)
    (C : ℕ) (u : ℝ≥0) : Set Ω :=
  {ω | ∃ s0 : ℝ≥0, σ ω = s0 ∧ HitE (drive κ B ω) δ (C : ℝ) s0 (c '' {j | ω ∈ M j}) u}

lemma mem_hitEv_iff {κ δ : ℝ} (hS : SMSetup P B 𝓕) (hδ : 0 < δ) {σ : Ω → WithTop ℝ≥0}
    {c : ℕ → ℂ} {M : ℕ → Set Ω} {C : ℕ} {u : ℝ≥0} {ω : Ω} :
    ω ∈ hitEv κ δ B σ c M C u ↔ ∃ s0 : ℝ≥0, σ ω = s0 ∧ ∃ s ∈ Icc (s0 : ℝ) u,
      RadGuard (drive κ B ω) δ C s ∧ sleTrace κ B ω s ∈ closure (c '' {j | ω ∈ M j}) := by
  simp only [hitEv, mem_setOf_eq]
  refine exists_congr fun s0 => and_congr_right fun _ => ?_
  exact hitE_iff (drive_continuous (hS.cont ω)) (drive_zero (hS.zero ω)) hδ s0.coe_nonneg _ _

lemma measurableSet_hitEv (hS : SMSetup P B 𝓕) (κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) (c : ℕ → ℂ) (M : ℕ → Set Ω)
    (hM : ∀ j (t : ℝ≥0), MeasurableSet[𝓕 t] (M j ∩ {ω | σ ω ≤ t})) (C : ℕ) (u : ℝ≥0) :
    MeasurableSet[𝓕 u] (hitEv κ δ B σ c M C u) := by
  have heq : hitEv κ δ B σ c M C u = {ω | σ ω ≤ u} ∩ ⋂ n : ℕ, ⋃ q : ℚ,
      ⋃ (_ : (q : ℝ) ∈ Icc 0 (u : ℝ)),
      {ω | RadGuard (drive κ B ω) δ C q} ∩
        ({ω | σ ω < ((Real.toNNReal (q + 1 / ((n : ℝ) + 1)) : ℝ≥0) : WithTop ℝ≥0)} ∩
          {ω | σ ω ≤ u}) ∩
      ⋃ j : ℕ, (M j ∩ {ω | σ ω ≤ u}) ∩
        {ω | sleTrace κ B ω q ∈ ball (c j) (1 / ((n : ℝ) + 1))} := by
    ext ω
    simp only [hitEv, HitE, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_iUnion, exists_prop,
      mem_image, mem_ball]
    constructor
    · rintro ⟨s0, hs0, hsu, h⟩
      have hσu : σ ω ≤ u := by rw [hs0]; exact WithTop.coe_le_coe.2 (by exact_mod_cast hsu)
      refine ⟨hσu, fun n => ?_⟩
      obtain ⟨q, hqI, hqG, hσq, z, ⟨j, hj, rfl⟩, hz⟩ := h n
      refine ⟨q, hqI, ⟨hqG, ⟨?_, hσu⟩⟩, j, ⟨hj, hσu⟩, hz⟩
      rw [hs0]; exact WithTop.coe_lt_coe.2 (Real.lt_toNNReal_iff_coe_lt.2 hσq)
    · rintro ⟨hσu, h⟩
      obtain ⟨s0, hs0⟩ :=
        WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hσu)
      refine ⟨s0, hs0.symm, ?_, fun n => ?_⟩
      · rw [← hs0] at hσu; exact_mod_cast WithTop.coe_le_coe.1 hσu
      · obtain ⟨q, hqI, ⟨hqG, hσq, -⟩, j, ⟨hj, -⟩, hz⟩ := h n
        refine ⟨q, hqI, hqG, ?_, c j, ⟨j, hj, rfl⟩, hz⟩
        rw [← hs0] at hσq
        exact Real.lt_toNNReal_iff_coe_lt.1 (WithTop.coe_lt_coe.1 hσq)
  rw [heq]
  refine (hσ u).inter (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q =>
    MeasurableSet.iUnion fun hq => ?_)
  have hq0 : (0 : ℝ) ≤ q := hq.1
  have hqu : Real.toNNReal q ≤ u := Real.toNNReal_le_iff_le_coe.2 hq.2
  refine ((?_ : MeasurableSet[𝓕 u] _).inter
    (((hσ.measurableSet _).1 (hσ.measurableSet_lt' _)).2 u)).inter
    (MeasurableSet.iUnion fun j => (hM j u).inter ?_)
  · have h := measurableSet_radGuard hS κ hδ C (Real.toNNReal q)
    rw [Real.coe_toNNReal _ hq0] at h
    exact 𝓕.mono hqu _ h
  · have h := measurable_sleTrace_adapt hS κ (Real.toNNReal q)
    rw [Real.coe_toNNReal _ hq0] at h
    exact (h.mono (𝓕.mono hqu) le_rfl) measurableSet_ball

/-- The guarded hitting time. -/
def hitTime (κ δ : ℝ) (B : ℝ≥0 → Ω → ℝ) (σ : Ω → WithTop ℝ≥0) (c : ℕ → ℂ) (M : ℕ → Set Ω)
    (ω : Ω) : WithTop ℝ≥0 :=
  sInf {x | ∃ u : ℝ≥0, x = (u : WithTop ℝ≥0) ∧ ∃ C : ℕ, ω ∈ hitEv κ δ B σ c M C u}

lemma hitTime_le_iff {κ δ : ℝ} (hS : SMSetup P B 𝓕) (hδ : 0 < δ) {σ : Ω → WithTop ℝ≥0}
    {c : ℕ → ℂ} {M : ℕ → Set Ω} (ω : Ω) (u : ℝ≥0) :
    hitTime κ δ B σ c M ω ≤ u ↔ ∃ C : ℕ, ω ∈ hitEv κ δ B σ c M C u := by
  constructor
  · intro h
    by_cases hne : ∃ u0 : ℝ≥0, ∃ C0 : ℕ, ω ∈ hitEv κ δ B σ c M C0 u0
    · obtain ⟨u0, C0, hmem⟩ := hne
      obtain ⟨s0, hs0, s, hs, hsG, hsK⟩ := (mem_hitEv_iff hS hδ).1 hmem
      obtain ⟨m, hmσ, hmG, hmK, hmin⟩ :=
        exists_first_guardedHit (drive_continuous (hS.cont ω)) (drive_zero (hS.zero ω)) hδ
          s0.coe_nonneg _ ⟨s, hs.1, hsG, hsK⟩
      have hlb : ((Real.toNNReal m : ℝ≥0) : WithTop ℝ≥0) ≤ hitTime κ δ B σ c M ω := by
        refine le_sInf ?_
        rintro x ⟨v, rfl, C, hC⟩
        obtain ⟨s0', hs0', s', hs', hs'G, hs'K⟩ := (mem_hitEv_iff hS hδ).1 hC
        have hss : s0' = s0 := WithTop.coe_injective (hs0'.symm.trans hs0)
        subst hss
        have hms' : m ≤ s' := by
          by_contra hlt
          push Not at hlt
          exact absurd (hmin s' hs'.1 (hmG.mono hlt.le) hs'K) (not_le.2 hlt)
        exact WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 (hms'.trans hs'.2))
      have hmu : m ≤ u := Real.toNNReal_le_iff_le_coe.1 (WithTop.coe_le_coe.1 (hlb.trans h))
      exact ⟨C0, (mem_hitEv_iff hS hδ).2 ⟨s0, hs0, m, ⟨hmσ, hmu⟩, hmG, hmK⟩⟩
    · exfalso
      have hempty : {x | ∃ u : ℝ≥0, x = (u : WithTop ℝ≥0) ∧ ∃ C : ℕ,
          ω ∈ hitEv κ δ B σ c M C u} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
        intro v _ C hC
        exact hne ⟨v, C, hC⟩
      simp only [hitTime, hempty, sInf_empty, top_le_iff] at h
      exact WithTop.coe_ne_top h
  · rintro ⟨C, hC⟩
    exact sInf_le ⟨u, rfl, C, hC⟩

/-- **The guarded hitting time is a stopping time** (every sample point). -/
theorem isStoppingTime_hitTime (hS : SMSetup P B 𝓕) (κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) (c : ℕ → ℂ) (M : ℕ → Set Ω)
    (hM : ∀ j (t : ℝ≥0), MeasurableSet[𝓕 t] (M j ∩ {ω | σ ω ≤ t})) :
    IsStoppingTime 𝓕 (hitTime κ δ B σ c M) := by
  intro u
  have heq : {ω | hitTime κ δ B σ c M ω ≤ u} = ⋃ C : ℕ, hitEv κ δ B σ c M C u := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion]
    exact hitTime_le_iff hS hδ ω u
  rw [heq]
  exact MeasurableSet.iUnion fun C => measurableSet_hitEv hS κ hδ hσ c M hM C u

end LWFar
end Thm18Asm
end QuantumZipper
