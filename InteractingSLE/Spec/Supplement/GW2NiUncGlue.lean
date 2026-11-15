/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NiUnc
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# The uncapped joined driver: gluing the capped drivers and traces; D-b against it

Packet PROVE-GW2-NEARIMG2 (D50). A family of drivers `w k` (the capped candidates of one angle) agreeing pairwise
up to the smaller horizon `C k` glues to one driver `W t = w (κ t) t` (`κ t` a candidate with `t ≤ C (κ t)`); the
generating traces glue too, because a generating trace at `t` is `LP.traceAt t` of the driver, which reads the
driver only up to `t`.

* deterministic: `glue_eq`, `continuous_glue`, **`isGeneratingTrace_glue`**, `trace_eq_of_agree`;
* **`ae_uncW_regular`**: almost surely `uncW` is continuous from `0` and `uncTr` is a generating trace on `[0, ∞)`;
* **`uncAgreeStatement`**: `UncAgreeStatement` (D-b against the uncapped driver), from RELDET's
  `GW2Rd.ae_schedW_eq_of_angle` and the capped regularity `GW2Rd.ae_schedW_regular`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

/-! ### Gluing, deterministic -/

section Glue

/-- Two generating traces on `[0, ∞)` of drivers agreeing up to `t` agree at `t`. -/
theorem trace_eq_of_agree {w₁ w₂ : ℝ≥0 → ℝ} {η₁ η₂ : ℝ≥0 → ℂ} (h₁ : Continuous w₁) (h₂ : Continuous w₂)
    (h₁0 : w₁ 0 = 0) (h₂0 : w₂ 0 = 0) (hη₁ : IsGeneratingTrace w₁ ⊤ η₁) (hη₂ : IsGeneratingTrace w₂ ⊤ η₂)
    {t : ℝ≥0} (heq : ∀ r ≤ t, w₁ r = w₂ r) : η₁ t = η₂ t := by
  rw [← LP.traceAt_eq_of_isGeneratingTrace hη₁ h₁.continuousOn h₁0 ENNReal.coe_lt_top,
    ← LP.traceAt_eq_of_isGeneratingTrace hη₂ h₂.continuousOn h₂0 ENNReal.coe_lt_top]
  exact LP.traceAt_congr heq


variable {w : ℕ → ℝ≥0 → ℝ} {C : ℕ → ℝ≥0} {κ : ℝ≥0 → ℕ}
  (hκ : ∀ t, t ≤ C (κ t)) (hag : ∀ k k' t, t ≤ C k → t ≤ C k' → w k t = w k' t)

include hκ hag

/-- The glued driver is every member up to its horizon. -/
theorem glue_eq (k : ℕ) {t : ℝ≥0} (ht : t ≤ C k) : w (κ t) t = w k t := hag _ _ _ (hκ t) ht

/-- **The glued driver is continuous.** -/
theorem continuous_glue (hc : ∀ k, Continuous (w k)) : Continuous fun t => w (κ t) t := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  have hev : (fun t => w (κ t) t) =ᶠ[𝓝 t₀] w (κ (t₀ + 1)) := by
    filter_upwards [Iio_mem_nhds (lt_add_one t₀)] with t ht
    exact glue_eq hκ hag _ (le_trans (le_of_lt ht) (hκ _))
  exact ((hc _).continuousAt).congr hev.symm

/-- **The glued traces generate the glued driver.** -/
theorem isGeneratingTrace_glue (hc : ∀ k, Continuous (w k)) (h0 : ∀ k, w k 0 = 0) {η : ℕ → ℝ≥0 → ℂ}
    (hη : ∀ k, IsGeneratingTrace (w k) ⊤ (η k)) :
    IsGeneratingTrace (fun t => w (κ t) t) ⊤ (fun t => η (κ t) t) := by
  have hηeq : ∀ k {t : ℝ≥0}, t ≤ C k → η (κ t) t = η k t := fun k t ht =>
    trace_eq_of_agree (hc _) (hc _) (h0 _) (h0 _) (hη _) (hη _) fun r hr =>
      hag _ _ _ (hr.trans (hκ t)) (hr.trans ht)
  refine ⟨(hη (κ 0)).1, ?_, fun t _ => ?_⟩
  · refine (continuous_iff_continuousAt.2 fun t₀ => ?_).continuousOn
    have hev : (fun t => η (κ t) t) =ᶠ[𝓝 t₀] η (κ (t₀ + 1)) := by
      filter_upwards [Iio_mem_nhds (lt_add_one t₀)] with t ht
      exact hηeq _ (le_trans (le_of_lt ht) (hκ _))
    have hcη : Continuous (η (κ (t₀ + 1))) := continuousOn_univ.1 ((hη _).2.1.mono fun t _ =>
      show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    exact (hcη.continuousAt).congr hev.symm
  · set k := κ (t + 1) with hk
    have hle : ∀ r ≤ t + 1, w (κ r) r = w k r := fun r hr => glue_eq hκ hag k (hr.trans (hκ _))
    have hH : fwdHull (fun s : ℝ => w (κ s.toNNReal) s.toNNReal) (t : ℝ) =
        fwdHull (fun s : ℝ => w k s.toNNReal) (t : ℝ) := by
      refine InteractingSLE.fwdHull_eq_of_eqOn (t₂ := ((t + 1 : ℝ≥0) : ℝ)) t.coe_nonneg (by push_cast; linarith)
        fun s hs => hle _ ?_
      exact (Real.toNNReal_le_iff_le_coe).2 hs.2
    have hI : (fun t => η (κ t) t) '' Icc 0 t = η k '' Icc 0 t :=
      image_congr fun s hs => hηeq k ((hs.2.trans (le_add_of_nonneg_right zero_le_one)).trans (hκ _))
    rw [hH, hI]
    exact (hη k).2.2 t ENNReal.coe_lt_top

end Glue

/-! ### The uncapped driver -/

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (i : ℕ)

include h13 in
/-- The capped candidates of the angle agree up to the smaller horizon, and each is regular (almost surely). -/
theorem ae_angCand_facts : ∀ᵐ ω ∂c.P,
    (∀ k k' (t : ℝ≥0), t ≤ historyTime c r l + (timeEnumeration c r k : ℝ≥0) →
      t ≤ historyTime c r l + (timeEnumeration c r k' : ℝ≥0) →
      schedW c r l (angCand i k) t ω = schedW c r l (angCand i k') t ω) ∧
    ∀ k, Continuous (schedW c r l (angCand i k) · ω) ∧ schedW c r l (angCand i k) 0 ω = 0 ∧
      IsGeneratingTrace (schedW c r l (angCand i k) · ω) ⊤ (schedTr c r l (angCand i k) ω) := by
  have : Countable ℕ := inferInstance
  filter_upwards [ae_schedW_eq_of_angle h13 c r,
    ae_all_iff.2 fun k => ae_schedW_regular h13 c r l (angCand i k)] with ω hDb hreg
  refine ⟨fun k k' t hk hk' => ?_, fun k => ⟨(hreg k).1, (hreg k).2.1, (hreg k).2.2.1⟩⟩
  refine hDb l _ _ (by rw [candidateAngle_angCand, candidateAngle_angCand]) t ?_
  rw [candidateCap_angCand, candidateCap_angCand]
  exact le_trans (le_of_eq rfl) (by
    rcases le_total (timeEnumeration c r k : ℝ≥0) (timeEnumeration c r k') with h | h
    · rw [min_eq_left h]; exact hk
    · rw [min_eq_right h]; exact hk')

omit [StandardBorelSpace Ω] in
theorem le_hist_capIdx (t : ℝ≥0) :
    t ≤ historyTime c r l + (timeEnumeration c r (capIdx c r t) : ℝ≥0) :=
  (le_capIdx c r t).trans le_add_self

include h13 in
/-- **Regularity of the uncapped joined driver** (almost surely): continuous from `0`, and `uncTr` is a
generating trace on `[0, ∞)`. -/
theorem ae_uncW_regular : ∀ᵐ ω ∂c.P,
    Continuous (uncW c r l i · ω) ∧ uncW c r l i 0 ω = 0 ∧
      IsGeneratingTrace (uncW c r l i · ω) ⊤ (uncTr c r l i ω) := by
  filter_upwards [ae_angCand_facts h13 c r l i] with ω ⟨hag, hreg⟩
  have hκ : ∀ t, t ≤ historyTime c r l + (timeEnumeration c r (capIdx c r t) : ℝ≥0) := le_hist_capIdx c r l
  have hg := isGeneratingTrace_glue (w := fun k t => schedW c r l (angCand i k) t ω) hκ hag
    (fun k => (hreg k).1) (fun k => (hreg k).2.1) (fun k => (hreg k).2.2)
  have hex : ∃ η, IsGeneratingTrace (fun t => uncW c r l i t ω) ⊤ η := ⟨_, hg⟩
  refine ⟨continuous_glue (w := fun k t => schedW c r l (angCand i k) t ω) hκ hag fun k => (hreg k).1,
    (hreg _).2.1, ?_⟩
  have e : uncTr c r l i ω = hex.choose := by simp only [uncTr, hex, ↓reduceDIte]
  rw [e]
  exact hex.choose_spec

include h13 in
/-- **D-b against the uncapped driver.** -/
theorem uncAgreeStatement' : ∀ᵐ ω ∂c.P, ∀ a : ℕ, candidateAngle c r a = angleEnumeration c r i →
    ∀ t ≤ historyTime c r l + candidateCap c r a,
      schedW c r l a t ω = uncW c r l i t ω ∧ schedTr c r l a ω t = uncTr c r l i ω t := by
  have : Countable ℕ := inferInstance
  filter_upwards [ae_schedW_eq_of_angle h13 c r, ae_all_iff.2 fun a => ae_schedW_regular h13 c r l a,
    ae_uncW_regular h13 c r l i] with ω hDb hreg hU a ha t ht
  have hW : ∀ s ≤ historyTime c r l + candidateCap c r a, schedW c r l a s ω = uncW c r l i s ω := by
    intro s hs
    refine hDb l a _ (by rw [ha, candidateAngle_angCand]) s ?_
    rw [candidateCap_angCand]
    exact (le_min hs (le_hist_capIdx c r l s)).trans_eq (min_add_add_left _ _ _)
  refine ⟨hW t ht, ?_⟩
  exact trace_eq_of_agree (hreg a).1 hU.1 (hreg a).2.1 hU.2.1 (hreg a).2.2.1 hU.2.2
    fun s hs => hW s (hs.trans ht)

/-- **`UncAgreeStatement`** (from Theorem 1.3). -/
theorem uncAgreeStatement (h13 : Exist.Theorem13Statement.{u}) : UncAgreeStatement.{u} :=
  fun _ _ _ c r l i => uncAgreeStatement' h13 c r l i

end InteractingSLE.Theorem14.GW2Ni
