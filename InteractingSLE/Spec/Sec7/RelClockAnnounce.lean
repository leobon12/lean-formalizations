/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.RelClock

/-!
# The pocket traversal announces its own lifetime

Packet PROVE-STRIPSYS7. Specification §7.4, proof of Aux. lemma 125 (`source/spec/p385-432.md` L213–L222, p. 396):

> In fact the complete Jordan traversal announces its own lifetime. Put
>
>   `ζₙ = n ∧ inf {s < ζ : |X_C(s)| ≥ n}`.
>
> If `ζ` is finite, its terminal endpoint maps to infinity, so continuity makes `ζₙ < ζ` and `ζₙ ↑ ζ`. If `ζ = ∞`,
> continuity on every compact time interval instead gives `ζₙ ↑ ∞`. These are genuine stopping times in the relative
> history and supply pre-lifetime localizations for the martingale and SDE arguments.

Here `X` is any real process (for the source, `|X_C|`) that is continuous before a lifetime `ζ` and adapted before it,
in a right-continuous filtration. The level set is entered strictly (`X > n`), the first entrance of an open set, which
is a stopping time of a right-continuous filtration; this changes nothing in the three properties.

## Main results

* `entrance X ζ c`: the first time before `ζ` at which `X > c`;
* **`isStoppingTime_entrance`**, **`isStoppingTime_announce`**;
* **`announce_lt`**: `ζₙ < ζ` when `X` is unbounded before every finite `ζ`;
* **`exists_le_announce`**: every time before `ζ` is below some `ζₙ`;
* `monotone_announce`.

These are the hypotheses `hσ`, `hσT`, `hσlim` of `PhaseSelAdapt.ae_phase_eq_zero_of_announcing` (PROVE-STRIPSYS6).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace RelClock

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- The first time before `ζ` at which `X > c` (`⊤` if there is none). -/
def entrance (X : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (c : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) < ζ ω ∧ c < X t ω), (t : WithTop ℝ≥0)

/-- The announcing times `ζₙ = n ∧ entrance(X > n)`, as nonnegative reals. -/
def announce (X : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  min (n : ℝ≥0) ((entrance X ζ n ω).untopD n)

variable {X : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0}

theorem entrance_le {c : ℝ} {ω : Ω} {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < ζ ω) (hc : c < X t ω) :
    entrance X ζ c ω ≤ t :=
  iInf₂_le t ⟨ht, hc⟩

theorem le_entrance_iff {c : ℝ} {ω : Ω} {a : WithTop ℝ≥0} :
    a ≤ entrance X ζ c ω ↔ ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → c < X t ω → a ≤ t := by
  simp only [entrance, le_iInf_iff, and_imp]

theorem entrance_lt_iff {c : ℝ} {ω : Ω} {a : WithTop ℝ≥0} :
    entrance X ζ c ω < a ↔ ∃ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω ∧ c < X t ω ∧ (t : WithTop ℝ≥0) < a := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact absurd h (not_lt.2 (le_entrance_iff.2 fun t ht hc => hne t ht hc))
  · rintro ⟨t, ht, hc, hta⟩
    exact (entrance_le ht hc).trans_lt hta

theorem coe_announce (n : ℕ) (ω : Ω) :
    ((announce X ζ n ω : ℝ≥0) : WithTop ℝ≥0) = min ((n : ℝ≥0) : WithTop ℝ≥0) (entrance X ζ n ω) := by
  unfold announce
  by_cases he : entrance X ζ n ω = ⊤
  · rw [he, WithTop.untopD_top, min_self, min_top_right]
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 he
    rw [← ht, WithTop.untopD_coe, WithTop.coe_min]

/-- **The first entrance into `(c, ∞)` before `ζ` is a stopping time** of a right-continuous filtration, for a
process continuous and adapted before `ζ`. -/
theorem isStoppingTime_entrance [𝓖.IsRightContinuous]
    (hXa : ∀ (t : ℝ≥0) (c : ℝ), MeasurableSet[𝓖 t] {ω | (t : WithTop ℝ≥0) < ζ ω ∧ c < X t ω})
    (hXc : ∀ ω, ContinuousOn (X · ω) {t | (t : WithTop ℝ≥0) < ζ ω}) (c : ℝ) :
    IsStoppingTime 𝓖 (entrance X ζ c) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i => ?_
  have e : {ω | entrance X ζ c ω < i} = ⋃ (r : ℚ) (_ : (r : ℝ).toNNReal < i),
      {ω | (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < ζ ω ∧ c < X (r : ℝ).toNNReal ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨t, htζ, hc, hti⟩ := entrance_lt_iff.1 h
      -- an open neighbourhood of `t` on which `X > c` and which stays before `ζ` and `i`
      have hopen : IsOpen {s : ℝ≥0 | (s : WithTop ℝ≥0) < ζ ω} :=
        isOpen_lt WithTop.continuous_coe continuous_const
      have hcont : ContinuousAt (X · ω) t := (hXc ω).continuousAt (hopen.mem_nhds htζ)
      have hopen' : IsOpen {s : ℝ≥0 | (s : WithTop ℝ≥0) < (i : WithTop ℝ≥0)} :=
        isOpen_lt WithTop.continuous_coe continuous_const
      have hev : ∀ᶠ s : ℝ≥0 in 𝓝 t, (s : WithTop ℝ≥0) < ζ ω ∧ c < X s ω ∧ (s : WithTop ℝ≥0) < i := by
        filter_upwards [hopen.mem_nhds htζ, hcont.eventually (lt_mem_nhds hc), hopen'.mem_nhds hti]
          with s h1 h2 h3
        exact ⟨h1, h2, h3⟩
      obtain ⟨u, htu, hsub⟩ := exists_Ico_subset_of_mem_nhds hev ⟨t + 1, lt_add_one t⟩
      obtain ⟨r, htr, hru⟩ := exists_rat_btwn_nnreal htu
      have hr := hsub ⟨htr.le, hru⟩
      exact ⟨r, WithTop.coe_lt_coe.1 hr.2.2, hr.1, hr.2.1⟩
    · rintro ⟨r, hri, hr, hc⟩
      exact (entrance_le hr hc).trans_lt (WithTop.coe_lt_coe.2 hri)
  rw [e]
  exact MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun hri => 𝓖.mono hri.le _ (hXa _ c)

/-- **The announcing times are stopping times.** -/
theorem isStoppingTime_announce [𝓖.IsRightContinuous]
    (hXa : ∀ (t : ℝ≥0) (c : ℝ), MeasurableSet[𝓖 t] {ω | (t : WithTop ℝ≥0) < ζ ω ∧ c < X t ω})
    (hXc : ∀ ω, ContinuousOn (X · ω) {t | (t : WithTop ℝ≥0) < ζ ω}) (n : ℕ) :
    IsStoppingTime 𝓖 fun ω => ((announce X ζ n ω : ℝ≥0) : WithTop ℝ≥0) := by
  have h := (isStoppingTime_const 𝓖 (n : ℝ≥0)).min (isStoppingTime_entrance hXa hXc (n : ℝ))
  have e : (fun ω => ((announce X ζ n ω : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => min ((n : ℝ≥0) : WithTop ℝ≥0) (entrance X ζ (n : ℝ) ω) := by
    funext ω
    rw [coe_announce]
  rw [e]
  exact h

/-- **`ζₙ < ζ`** ("If `ζ` is finite, its terminal endpoint maps to infinity, so continuity makes `ζₙ < ζ`"): when `X`
is unbounded before every finite lifetime. -/
theorem announce_lt {ω : Ω} (hunb : ζ ω ≠ ⊤ → ∀ M : ℝ, ∃ s : ℝ≥0, (s : WithTop ℝ≥0) < ζ ω ∧ M < X s ω)
    (n : ℕ) : ((announce X ζ n ω : ℝ≥0) : WithTop ℝ≥0) < ζ ω := by
  rw [coe_announce]
  by_cases hζ : ζ ω = ⊤
  · rw [hζ]
    exact lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top _)
  · obtain ⟨s, hs, hM⟩ := hunb hζ n
    exact lt_of_le_of_lt (min_le_right _ _) ((entrance_le hs hM).trans_lt hs)

/-- **Every time before `ζ` lies below some `ζₙ`** ("`ζₙ ↑ ζ`"): `X` is bounded on `[0, t]` for `t < ζ`. -/
theorem exists_le_announce (hXc : ∀ ω, ContinuousOn (X · ω) {t | (t : WithTop ℝ≥0) < ζ ω}) {ω : Ω}
    {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < ζ ω) : ∃ n : ℕ, t ≤ announce X ζ n ω := by
  have hsub : Icc (0 : ℝ≥0) t ⊆ {s : ℝ≥0 | (s : WithTop ℝ≥0) < ζ ω} := fun s hs =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 hs.2) ht
  obtain ⟨K, hK⟩ := (isCompact_Icc.image_of_continuousOn ((hXc ω).mono hsub)).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt (max K (t : ℝ))
  refine ⟨n, ?_⟩
  have hnK : K < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnt : t ≤ (n : ℝ≥0) := by
    have : (t : ℝ) ≤ n := (le_max_right _ _).trans hn.le
    exact_mod_cast this
  have hle : ((t : ℝ≥0) : WithTop ℝ≥0) ≤ ((announce X ζ n ω : ℝ≥0) : WithTop ℝ≥0) := by
    rw [coe_announce]
    refine le_min (WithTop.coe_le_coe.2 hnt) (le_entrance_iff.2 fun s _ hs => ?_)
    by_contra hlt
    push Not at hlt
    have hst : s ≤ t := (WithTop.coe_lt_coe.1 hlt).le
    have h1 : ‖X s ω‖ ≤ K := hK _ ⟨s, ⟨zero_le, hst⟩, rfl⟩
    rw [Real.norm_eq_abs] at h1
    have h2 : X s ω ≤ K := (le_abs_self _).trans h1
    have : ((n : ℕ) : ℝ) < K := by exact_mod_cast hs.trans_le h2
    linarith
  exact WithTop.coe_le_coe.1 hle

theorem entrance_mono {c c' : ℝ} (hcc' : c ≤ c') (ω : Ω) : entrance X ζ c ω ≤ entrance X ζ c' ω :=
  le_entrance_iff.2 fun _ ht hc => entrance_le ht (hcc'.trans_lt hc)

/-- The announcing times increase with `n`. -/
theorem monotone_announce (ω : Ω) : Monotone fun n => announce X ζ n ω := by
  intro n m hnm
  have h : ((announce X ζ n ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((announce X ζ m ω : ℝ≥0) : WithTop ℝ≥0) := by
    rw [coe_announce, coe_announce]
    exact min_le_min (WithTop.coe_le_coe.2 (by exact_mod_cast hnm)) (entrance_mono (by exact_mod_cast hnm) ω)
  exact WithTop.coe_le_coe.1 h

end RelClock

end Sec7

end InteractingSLE
