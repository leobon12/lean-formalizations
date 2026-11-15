/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Process.Stopping

/-!
# §7.3: the terminal trial principle (Astra's follow-up note D.3.4)

Packet PROVE-SEC7-C5. Astra, *Follow-up proofs and dependency audit* (ruling R38), D.3.4,
`source/external/AstraIG1/ig1_followup_proofs.txt` L2140–L2153, the final step of Aux. lemma 113 (Specification
p. 372, `source/spec/p337-384.md` L731–L737, the event `G` of (TI15.1)):

> Let `G ∈ 𝓕_∞` be a terminal success event. Suppose that on `Gᶜ` there are infinitely many trial stopping times
> `ξ_n → ∞`, and that at every finite trial `P(G ∣ 𝓕_{ξ_n}) ≥ p > 0`, where the same `p` may be random but is
> measurable at the initial restart. Then `P(Gᶜ) = 0`. Indeed, the bounded martingale `M_t = P(G ∣ 𝓕_t)` converges
> to `1_G` as `t → ∞`. It therefore converges to zero along the trial times on `Gᶜ`, contradicting the fixed
> positive lower bound there.

The proof here uses Lévy's upward theorem for the discrete filtration `n ↦ 𝓕_{ξ_n}` of the trial stopping times
(`MeasureTheory.tendsto_ae_condExp`): when the trial times are nondecreasing and eventually exceed every time,
`⨆ₙ 𝓕_{ξ_n}` contains every `𝓕_t` (`le_iSup_trialFiltration`), so `P(G ∣ 𝓕_{ξ_n}) → 1_G` almost surely. No optional
sampling of the continuous-time martingale is needed. The lower bound `p` may be any function that is almost surely
positive on `Gᶜ`; it is used only pointwise.

## Main results

* `trialFiltration`: the filtration `n ↦ 𝓕_{ξ_n}` of a nondecreasing sequence of stopping times;
* `le_iSup_trialFiltration`: `𝓕_t ≤ ⨆ₙ 𝓕_{ξ_n}` when the trial times eventually exceed `t`;
* **`measure_compl_eq_zero_of_trials`**: the terminal trial principle.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology

namespace InteractingSLE

namespace Sec7

namespace Trial

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [LinearOrder ι] {𝓕 : Filtration ι mΩ}

/-- **The trial filtration** `n ↦ 𝓕_{ξ_n}` of a pointwise nondecreasing sequence of stopping times. -/
def trialFiltration {ξ : ℕ → Ω → WithTop ι} (hξ : ∀ n, IsStoppingTime 𝓕 (ξ n))
    (hmono : ∀ ω, Monotone fun n => ξ n ω) : Filtration ℕ mΩ where
  seq n := (hξ n).measurableSpace
  mono' _ _ hnm := IsStoppingTime.measurableSpace_mono (hξ _) (hξ _) fun ω => hmono ω hnm
  le' n := (hξ n).measurableSpace_le

theorem trialFiltration_apply {ξ : ℕ → Ω → WithTop ι} (hξ : ∀ n, IsStoppingTime 𝓕 (ξ n))
    (hmono : ∀ ω, Monotone fun n => ξ n ω) (n : ℕ) :
    trialFiltration hξ hmono n = (hξ n).measurableSpace := rfl

/-- An event of `𝓕_t`, restricted to `{t < τ}`, is an event of `𝓕_τ`. -/
theorem measurableSet_inter_lt {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) {t : ι} {A : Set Ω}
    (hA : MeasurableSet[𝓕 t] A) : MeasurableSet[hτ.measurableSpace] (A ∩ {ω | (t : WithTop ι) < τ ω}) := by
  have hlt : MeasurableSet[𝓕 t] {ω | (t : WithTop ι) < τ ω} := by
    have h := (hτ t).compl
    convert h using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_le]
  refine ⟨?_, fun i => ?_⟩
  · exact (le_iSup (fun s => 𝓕 s) t) _ (hA.inter hlt)
  · rcases le_or_gt i t with hit | hti
    · convert @MeasurableSet.empty Ω (𝓕 i) using 1
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      rintro ⟨_, h⟩
      exact lt_of_le_of_lt (WithTop.coe_le_coe.2 hit) h
    · exact (𝓕.mono hti.le _ (hA.inter hlt)).inter (hτ i)

/-- **The trial σ-algebras exhaust the filtration**: if the trial times eventually exceed `t` everywhere, then
`𝓕_t ≤ ⨆ₙ 𝓕_{ξ_n}`. -/
theorem le_iSup_trialFiltration {ξ : ℕ → Ω → WithTop ι} (hξ : ∀ n, IsStoppingTime 𝓕 (ξ n))
    (hmono : ∀ ω, Monotone fun n => ξ n ω) (hinf : ∀ ω (t : ι), ∃ n, (t : WithTop ι) < ξ n ω) (t : ι) :
    𝓕 t ≤ ⨆ n, trialFiltration hξ hmono n := by
  intro A hA
  have hU : A = ⋃ n, A ∩ {ω | (t : WithTop ι) < ξ n ω} := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_and_left, iff_self_and]
    exact fun _ => hinf ω t
  rw [hU]
  exact MeasurableSet.iUnion fun n => (le_iSup (fun n => trialFiltration hξ hmono n) n) _
    (measurableSet_inter_lt (hξ n) hA)

/-- `⨆_t 𝓕_t ≤ ⨆ₙ 𝓕_{ξ_n}` (and hence equality, `𝓕_{ξ_n} ≤ ⨆_t 𝓕_t` being automatic). -/
theorem iSup_le_iSup_trialFiltration {ξ : ℕ → Ω → WithTop ι} (hξ : ∀ n, IsStoppingTime 𝓕 (ξ n))
    (hmono : ∀ ω, Monotone fun n => ξ n ω) (hinf : ∀ ω (t : ι), ∃ n, (t : WithTop ι) < ξ n ω) :
    (⨆ t, 𝓕 t) ≤ ⨆ n, trialFiltration hξ hmono n :=
  iSup_le fun t => le_iSup_trialFiltration hξ hmono hinf t

/-- **The terminal trial principle** (Astra D.3.4; the last step of Aux. lemma 113, (TI15.1)). Let `G` be an event of
`⨆_t 𝓕_t`, and `ξ_n` pointwise nondecreasing stopping times that eventually exceed every time. Suppose that almost
surely on `Gᶜ` every trial is finite and the success probability at every trial is at least `p > 0`:
`P(G ∣ 𝓕_{ξ_n}) ≥ p` (the lower bound `p` may be random). Then `P(Gᶜ) = 0`. -/
theorem measure_compl_eq_zero_of_trials {P : Measure Ω} [IsFiniteMeasure P] {G : Set Ω}
    (hG : MeasurableSet[⨆ t, 𝓕 t] G) {ξ : ℕ → Ω → WithTop ι} (hξ : ∀ n, IsStoppingTime 𝓕 (ξ n))
    (hmono : ∀ ω, Monotone fun n => ξ n ω) (hinf : ∀ ω (t : ι), ∃ n, (t : WithTop ι) < ξ n ω) {p : Ω → ℝ}
    (htrial : ∀ n, ∀ᵐ ω ∂P, ω ∉ G → p ω ≤ (P[G.indicator (fun _ => (1 : ℝ)) | (hξ n).measurableSpace]) ω)
    (hp : ∀ᵐ ω ∂P, ω ∉ G → 0 < p ω) : P Gᶜ = 0 := by
  set ℱ := trialFiltration hξ hmono with hℱ
  set g : Ω → ℝ := G.indicator fun _ => (1 : ℝ) with hg
  have hGm : MeasurableSet[⨆ n, ℱ n] G := iSup_le_iSup_trialFiltration hξ hmono hinf _ hG
  have hgm : StronglyMeasurable[⨆ n, ℱ n] g :=
    (stronglyMeasurable_const.indicator hGm)
  have hgi : Integrable g P := (integrable_const (1 : ℝ)).indicator ((iSup_le fun n => ℱ.le n) _ hGm)
  -- Lévy's upward theorem along the trial filtration
  have hlim := hgi.tendsto_ae_condExp (ℱ := ℱ) hgm
  have htrial' : ∀ᵐ ω ∂P, ∀ n, ω ∉ G → p ω ≤ (P[g | ℱ n]) ω := ae_all_iff.2 fun n => by
    filter_upwards [htrial n] with ω hω
    exact hω
  refine measure_mono_null (fun ω hω => ?_) (show P {ω | ¬ (ω ∈ Gᶜ → False)} = 0 from ?_)
  · exact fun h => h hω
  rw [← ae_iff]
  filter_upwards [hlim, htrial', hp] with ω hl ht hpω hωG
  have hω : ω ∉ G := hωG
  have hgω : g ω = 0 := by rw [hg, indicator_of_notMem hω]
  rw [hgω] at hl
  have hge : p ω ≤ 0 := ge_of_tendsto hl (Eventually.of_forall fun n => ht n hω)
  exact absurd (hpω hω) (not_lt.2 hge)

end Trial

end Sec7

end InteractingSLE
