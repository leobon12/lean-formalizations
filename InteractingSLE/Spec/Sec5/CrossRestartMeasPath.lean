/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartLawMeas

/-!
# The measurable-form restart objects of an arbitrary path: congruence and measurability

Packet PROVE-SEC5-I. The measurable-form objects of PROVE-SEC5-H (`lawClock`, `lawLife`, `lawInv`, `lawPath`) read the
chart path `restartPath q U σ x₁ γ'` only

* at the time `0`, and
* at the times strictly before the exit time `lawExit` (the grid capacities of the prefixes before the exit and the
  dyadic times above the inverse clock, which is before the exit or `⊤`).

Here the four objects are written for an arbitrary path `Γ` and exit `E` (`pathClock`, `pathLife`, `pathInv`,
`pathLaw`; the SEC5-H objects are the special case `Γ = restartPath …`, `E = lawExit …`, by `rfl`), with:

* **congruence**: `pathLife_congr`, `pathLaw_congr` (two paths that agree at `0` and before `E` give the same
  objects);
* **measurability**: `measurable_pathLife`, `measurable_pathLaw`, `measurable_encPath_pathLaw` (from the
  measurability of the path at each fixed time and of `E`);
* **the restart variable reads the traces only before their lifetimes** (`restartVar_congr`): it is unchanged when the
  flow-line trace is changed off `[0, σ]` and the counterflow trace off `[0, ζ′)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open Restart

/-! ### The objects of an arbitrary path -/

/-- The chart capacity clock of a path `Γ`: half the grid capacity of `Γ` on the rational grid of `[0, t]`. -/
def pathClock (Γ : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ := (WholeField.hcapHit (Γ '' ratGrid t)).toReal / 2

/-- The chart capacity lifetime of `Γ` before the exit `E`. -/
def pathLife (Γ : ℝ≥0 → ℂ) (E : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (r : ℚ) (_ : (qnn r : ℝ≥0∞) < E), ENNReal.ofReal (pathClock Γ (qnn r))

/-- The inverse clock of `Γ` before the exit `E`. -/
def pathInv (Γ : ℝ≥0 → ℂ) (E : ℝ≥0∞) (u : ℝ≥0) : ℝ≥0∞ :=
  ⨅ (r : ℚ) (_ : (qnn r : ℝ≥0∞) < E ∧ (u : ℝ) ≤ pathClock Γ (qnn r)), (qnn r : ℝ≥0∞)

/-- `Γ` in chart capacity time: the limit of `Γ` along the dyadic times above the inverse clock. -/
def pathLaw (Γ : ℝ≥0 → ℂ) (E : ℝ≥0∞) (u : ℝ≥0) : ℂ :=
  limOr0 fun n => Γ (dyadicUp n (pathInv Γ E u).toNNReal)

section Bridge

variable {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ} {η : ℝ≥0 → ℂ} {s : ℝ≥0} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ}

theorem lawClock_eq_pathClock (t : ℝ≥0) : lawClock q U σ x₁ γ' t = pathClock (restartPath q U σ x₁ γ') t := rfl

theorem lawLife_eq_pathLife :
    lawLife q U σ x₁ η s ζ' γ' = pathLife (restartPath q U σ x₁ γ') (lawExit q η s ζ' γ') := rfl

theorem lawInv_eq_pathInv (u : ℝ≥0) :
    lawInv q U σ x₁ η s ζ' γ' u = pathInv (restartPath q U σ x₁ γ') (lawExit q η s ζ' γ') u := rfl

theorem lawPath_eq_pathLaw :
    lawPath q U σ x₁ η s ζ' γ' = pathLaw (restartPath q U σ x₁ γ') (lawExit q η s ζ' γ') := rfl

/-- The explicit restart variable in terms of the objects of its chart path. -/
theorem restartVar_eq_encPath (q : ℝ) (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (η : ℝ≥0 → ℂ) (σ : ℝ≥0) (ζ' : ℝ≥0∞)
    (γ' : ℝ≥0 → ℂ) :
    restartVar q w ζ η σ ζ' γ' =
      encPath (pathLaw (restartPath q (segDrive w ζ σ) σ (segStart q w ζ σ) γ') (lawExit q η σ ζ' γ'))
        (pathLife (restartPath q (segDrive w ζ σ) σ (segStart q w ζ σ) γ') (lawExit q η σ ζ' γ')) := rfl

end Bridge

/-! ### Congruence -/

section Congr

variable {Γ₁ Γ₂ : ℝ≥0 → ℂ} {E : ℝ≥0∞}

theorem dyadicUp_zero (n : ℕ) : dyadicUp n 0 = 0 := by simp [dyadicUp]

/-- `limOr0` only sees the tail of the sequence. -/
theorem limOr0_congr {f g : ℕ → ℂ} (h : f =ᶠ[atTop] g) : limOr0 f = limOr0 g := by
  by_cases hf : ∃ l, Tendsto f atTop (𝓝 l)
  · obtain ⟨l, hl⟩ := hf
    rw [limOr0_eq hl, limOr0_eq (hl.congr' h)]
  · have hg : ¬ ∃ l, Tendsto g atTop (𝓝 l) := fun ⟨l, hl⟩ => hf ⟨l, hl.congr' h.symm⟩
    unfold limOr0
    rw [dite_eq_right_of_eq_false (eq_false hf), dite_eq_right_of_eq_false (eq_false hg)]

theorem pathClock_congr {t : ℝ≥0} (h : ∀ x : ℝ≥0, x ≤ t → Γ₁ x = Γ₂ x) : pathClock Γ₁ t = pathClock Γ₂ t := by
  unfold pathClock
  rw [image_congr fun x hx => h x (ratGrid_subset_Icc t hx).2]

theorem pathClock_congr_of_lt (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < E → Γ₁ t = Γ₂ t) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < E) :
    pathClock Γ₁ r = pathClock Γ₂ r :=
  pathClock_congr fun x hx => h x (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hx) hr)

theorem pathLife_congr (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < E → Γ₁ t = Γ₂ t) : pathLife Γ₁ E = pathLife Γ₂ E := by
  unfold pathLife
  refine iSup_congr fun r => iSup_congr_Prop Iff.rfl fun hr => ?_
  rw [pathClock_congr_of_lt h hr]

theorem pathInv_congr (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < E → Γ₁ t = Γ₂ t) (u : ℝ≥0) :
    pathInv Γ₁ E u = pathInv Γ₂ E u := by
  unfold pathInv
  refine iInf_congr fun r => iInf_congr_Prop ?_ fun _ => rfl
  constructor
  · rintro ⟨hr, hu⟩
    exact ⟨hr, (pathClock_congr_of_lt h hr) ▸ hu⟩
  · rintro ⟨hr, hu⟩
    exact ⟨hr, (pathClock_congr_of_lt h hr).symm ▸ hu⟩

/-- The inverse clock is before the exit, or `⊤`. -/
theorem pathInv_lt_or_eq_top (Γ : ℝ≥0 → ℂ) (E : ℝ≥0∞) (u : ℝ≥0) : pathInv Γ E u < E ∨ pathInv Γ E u = ⊤ := by
  by_cases hex : ∃ r : ℚ, (qnn r : ℝ≥0∞) < E ∧ (u : ℝ) ≤ pathClock Γ (qnn r)
  · obtain ⟨r, hr⟩ := hex
    exact Or.inl (lt_of_le_of_lt (iInf₂_le r hr) hr.1)
  · push Not at hex
    refine Or.inr (le_antisymm le_top (le_iInf₂ fun r hr => ?_))
    exact absurd hr.2 (not_le.2 (hex r hr.1))

/-- **`pathLaw` reads the path only at `0` and before the exit.** -/
theorem pathLaw_congr (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < E → Γ₁ t = Γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) :
    pathLaw Γ₁ E = pathLaw Γ₂ E := by
  funext u
  unfold pathLaw
  rw [pathInv_congr h u]
  refine limOr0_congr ?_
  rcases pathInv_lt_or_eq_top Γ₂ E u with hlt | htop
  · have hne : pathInv Γ₂ E u ≠ ⊤ := ne_top_of_lt hlt
    set t := (pathInv Γ₂ E u).toNNReal with ht
    have htE : (t : ℝ≥0∞) < E := by rwa [ht, ENNReal.coe_toNNReal hne]
    have hopen : IsOpen {x : ℝ≥0 | (x : ℝ≥0∞) < E} := isOpen_lt ENNReal.continuous_coe continuous_const
    filter_upwards [(tendsto_dyadicUp t).eventually (hopen.mem_nhds htE)] with n hn
    exact h _ hn
  · refine Eventually.of_forall fun n => ?_
    simp only [htop, ENNReal.toNNReal_top, dyadicUp_zero, h0]

end Congr

/-! ### Measurability -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {Γ : Ω → ℝ≥0 → ℂ} {E : Ω → ℝ≥0∞}
  (hΓ : ∀ t, Measurable fun ω => Γ ω t) (hE : Measurable E)

include hΓ in
theorem measurable_pathClock (t : ℝ≥0) : Measurable fun ω => pathClock (Γ ω) t :=
  ((measurable_hcapHit_image_of_countable (countable_ratGrid t) hΓ).ennreal_toReal).div_const 2

include hΓ hE in
theorem measurable_pathLife : Measurable fun ω => pathLife (Γ ω) (E ω) := by
  classical
  have heq : (fun ω => pathLife (Γ ω) (E ω)) = fun ω =>
      ⨆ r : ℚ, if (qnn r : ℝ≥0∞) < E ω then ENNReal.ofReal (pathClock (Γ ω) (qnn r)) else ⊥ := by
    funext ω
    simp only [pathLife, iSup_eq_if]
  rw [heq]
  exact Measurable.iSup fun r => Measurable.ite (measurableSet_lt measurable_const hE)
    (ENNReal.measurable_ofReal.comp (measurable_pathClock hΓ _)) measurable_const

include hΓ hE in
theorem measurable_pathInv (u : ℝ≥0) : Measurable fun ω => pathInv (Γ ω) (E ω) u := by
  classical
  have heq : (fun ω => pathInv (Γ ω) (E ω) u) = fun ω =>
      ⨅ r : ℚ, if (qnn r : ℝ≥0∞) < E ω ∧ (u : ℝ) ≤ pathClock (Γ ω) (qnn r) then (qnn r : ℝ≥0∞) else ⊤ := by
    funext ω
    simp only [pathInv, iInf_eq_if]
  rw [heq]
  exact Measurable.iInf fun r => Measurable.ite
    ((measurableSet_lt measurable_const hE).inter (measurableSet_le measurable_const (measurable_pathClock hΓ _)))
    measurable_const measurable_const

include hΓ hE in
theorem measurable_pathLaw (u : ℝ≥0) : Measurable fun ω => pathLaw (Γ ω) (E ω) u := by
  refine measurable_limOr0 fun n => ?_
  exact measurable_comp_of_countable_time (countable_range_dyadicUp n)
    ((measurable_dyadicUp n).comp (ENNReal.measurable_toNNReal.comp (measurable_pathInv hΓ hE u))) hΓ

include hΓ hE in
/-- **The code of a path in chart capacity time is measurable** as soon as the path at every fixed time and the exit
are. -/
theorem measurable_encPath_pathLaw :
    Measurable fun ω => encPath (pathLaw (Γ ω) (E ω)) (pathLife (Γ ω) (E ω)) :=
  measurable_encPath (fun u => measurable_pathLaw hΓ hE u) (measurable_pathLife hΓ hE)

end Meas

/-! ### The restart variable reads the traces only before their lifetimes -/

section Versions

variable {q : ℝ} {s : ℝ≥0} {ζ' : ℝ≥0∞} {η η₀ γ γ₀ : ℝ≥0 → ℂ}

theorem zero_mem_ratGrid (t : ℝ≥0) : (0 : ℝ≥0) ∈ ratGrid t := ⟨0, by simp⟩

theorem isTraceGoodQ_of_congr (hη : ∀ t : ℝ≥0, t ≤ s → η₀ t = η t)
    (hγ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → γ₀ t = γ t) {r : ℝ≥0} (h : IsTraceGoodQ q η₀ s ζ' γ₀ r) :
    IsTraceGoodQ q η s ζ' γ r := by
  obtain ⟨hr, h0, h1, m, h2⟩ := h
  have hγr : ∀ t ∈ ratGrid r, γ₀ t = γ t := fun t ht =>
    hγ t (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (ratGrid_subset_Icc r ht).2) hr)
  refine ⟨hr, ?_, fun k => ?_, m, fun a ha b hb => ?_⟩
  · rw [← hγr 0 (zero_mem_ratGrid r)]
    exact h0
  · obtain ⟨m', hm'⟩ := h1 k
    exact ⟨m', fun t ht htp htk => (hγr t ht) ▸ hm' t ht htp htk⟩
  · rw [← hη a (ratGrid_subset_Icc s ha).2, ← hγr b hb]
    exact h2 a ha b hb

theorem isTraceGoodQ_congr (hη : ∀ t : ℝ≥0, t ≤ s → η₀ t = η t)
    (hγ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → γ₀ t = γ t) (r : ℝ≥0) :
    IsTraceGoodQ q η₀ s ζ' γ₀ r ↔ IsTraceGoodQ q η s ζ' γ r :=
  ⟨isTraceGoodQ_of_congr hη hγ, isTraceGoodQ_of_congr (fun t ht => (hη t ht).symm) fun t ht => (hγ t ht).symm⟩

theorem lawExit_congr (hη : ∀ t : ℝ≥0, t ≤ s → η₀ t = η t)
    (hγ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → γ₀ t = γ t) : lawExit q η₀ s ζ' γ₀ = lawExit q η s ζ' γ := by
  unfold lawExit
  exact iSup_congr fun r => iSup_congr_Prop (isTraceGoodQ_congr hη hγ _) fun _ => rfl

/-- **The explicit restart variable reads the flow-line trace only on `[0, σ]` and the counterflow trace only before
its lifetime.** -/
theorem restartVar_congr {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {σ : ℝ≥0} (hη : ∀ t : ℝ≥0, t ≤ σ → η₀ t = η t)
    (hγ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → γ₀ t = γ t) :
    restartVar q w ζ η₀ σ ζ' γ₀ = restartVar q w ζ η σ ζ' γ := by
  rw [restartVar_eq_encPath, restartVar_eq_encPath, lawExit_congr hη hγ]
  have hP : ∀ t : ℝ≥0, (t : ℝ≥0∞) < lawExit q η σ ζ' γ →
      restartPath q (segDrive w ζ σ) σ (segStart q w ζ σ) γ₀ t =
        restartPath q (segDrive w ζ σ) σ (segStart q w ζ σ) γ t := fun t ht => by
    unfold restartPath
    rw [hγ t (lt_of_lt_of_le ht lawExit_le)]
  rw [pathLaw_congr hP (by rw [restartPath_zero, restartPath_zero]), pathLife_congr hP]

end Versions

end CrossRestart

end Sec5

end InteractingSLE
