/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ScheduleIdent
import InteractingSLE.Spec.Exist.StagedLaw4Def

/-!
# Identification of the staged pieces with the canonical construction under ruling R51 (pathwise part)

Packet PROVE-T14-TIP6. PROVE-T14-TIP3 identified a staged history `E` of a GW2 schedule with the canonical construction
(`GW2Schedule.ae_agree_canon`) for families whose drivers are regular at **every** sample. Ruling R51 only provides
`StagedPiecesRegular`: almost surely, every launched piece is continuous on `[0, min t ζ]` (`t` its own time, `ζ` its
lifetime) and starts at `0`. This file contains the deterministic facts that make that weaker regularity sufficient:

* `run_eq_of_canonDrv_eq`: the run of a program depends on each driver only through the driver stopped at the
  instruction's own time and the flag "the lifetime came first" (`canonDrv`);
* `canonDrv_eq_of_agreeRat`: a driver that is continuous on `[0, min t ζ]` and starts at `0`, and agrees at the rational
  times before its lifetime (with the same lifetime) with a driver regular at every sample, has the same stopped driver;
* `eq_of_rat_le`: two functions continuous on `[0, x]` that agree at the rational times in `[0, x]` agree at `x`.

The probabilistic part is `GW2ScheduleR51Ident.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Schedule

open Exist Staged StagedLaw Restart LQGMetric

/-! ### The run depends on the stopped drivers only -/

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The run depends on each driver only through its stopped driver** (`canonDrv` at the instruction's own time:
the driver stopped at `min t ζ`, with the lifetime kept only when it came first). -/
theorem run_eq_of_canonDrv_eq (spec : ExplSpec) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} : ∀ {k : ℕ},
    (∀ j < k, canonDrv (instrTime spec j) (D j) = canonDrv (instrTime spec j) (D' j)) →
    ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k
  | 0, _ => rfl
  | k + 1, h => by
    have ih : ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k :=
      run_eq_of_canonDrv_eq spec fun j hj => h j (Nat.lt_succ_of_lt hj)
    have hk := h k (Nat.lt_succ_self k)
    rw [Staged.run_succ, Staged.run_succ, ← ih]
    cases hins : spec.2.2[k]? with
    | none => rfl
    | some ins =>
      rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
      · have ht : instrTime spec k = t := by simp only [instrTime, hins]
        rw [ht] at hk
        change ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t =
          ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D' k) θ t
        rcases flowStep_cases (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k θ t with hc | hc
        · exact hc _ _
        · rw [hc, hc, ← launch_canonDrv _ _ (D k), ← launch_canonDrv _ _ (D' k), hk]
      · rfl
      · rfl

/-- A GW2 flow step from a stuck state does not read its driver. -/
theorem flowStep_eq_of_isStuck (s : ExplState) (hs : IsStuck (stStatus s)) (k : ℕ) (D D' : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (θ : ℝ) (t : ℝ≥0∞) : ExplState.flowStep κ b true s k D θ t = ExplState.flowStep κ b true s k D' θ t := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases hs with h | ⟨o, h⟩
  · change status = stDead at h
    subst h
    rfl
  · change status = stThr o at h
    subst h
    rfl

/-- **The run of a GW2 flow program depends only on the stopped drivers of its successful prefix**: if the stopped
drivers agree at every instruction `j < k` reached after `j` successful pieces of `D`, the runs agree before `k`. -/
theorem run_gw2_eq_of_canonDrv {spec : ExplSpec} (hgw : spec.2.1 = true) {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}
    (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} :
    ∀ k ≤ spec.2.2.length, (∀ j < k, AllSucc Δ D j → canonDrv (Δ j) (D j) = canonDrv (Δ j) (D' j)) →
      ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k
  | 0, _, _ => rfl
  | k + 1, hk1, h => by
    have hk : k < spec.2.2.length := hk1
    have ih := run_gw2_eq_of_canonDrv hgw hprog hΔ k hk.le fun j hj => h j (Nat.lt_succ_of_lt hj)
    have hrun : ∀ X : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞, ExplState.run κ b jumps spec X (k + 1) =
        ExplState.flowStep κ b true (ExplState.run κ b jumps spec X k) k (X k) (θ k) (Δ k) := by
      intro X
      rw [Staged.run_succ, hprog k hk]
      change ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec X k) k (X k) (θ k) (Δ k) = _
      rw [hgw]
    rw [hrun, hrun, ← ih]
    by_cases hs : AllSucc Δ D k
    · have hc := h k (Nat.lt_succ_self k) hs
      rcases flowStep_cases (κ := κ) (b := b) true (ExplState.run κ b jumps spec D k) k (θ k) (Δ k) with hc' | hc'
      · exact hc' _ _
      · rw [hc', hc', ← launch_canonDrv _ _ (D k), ← launch_canonDrv _ _ (D' k), hc]
    · exact flowStep_eq_of_isStuck _ ((run_gw2 hgw hprog hΔ D k hk.le).2 hs) k _ _ _ _

end Run

/-! ### Stopped drivers from rational agreement -/

section Stopped

/-- **Two functions continuous on `[0, x]` that agree at the rational times in `[0, x]` agree at `x`.** -/
theorem eq_of_rat_le {f g : ℝ≥0 → ℝ} {x : ℝ≥0} (hf : ContinuousOn f (Iic x)) (hg : ContinuousOn g (Iic x))
    (hq : ∀ q : ℚ, ((q : ℝ).toNNReal : ℝ≥0) ≤ x → f (q : ℝ).toNNReal = g (q : ℝ).toNNReal) : f x = g x := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ x) with hx | hx
  · rw [← hx]
    have := hq 0 (by rw [Rat.cast_zero, Real.toNNReal_zero]; exact bot_le)
    rwa [Rat.cast_zero, Real.toNNReal_zero] at this
  have hEq : EqOn f g (Iic x ∩ range fun q : ℚ => (q : ℝ).toNNReal) := by
    rintro s ⟨hs, q, rfl⟩
    exact hq q hs
  have hsub : Iic x ⊆ closure (Iic x ∩ range fun q : ℚ => (q : ℝ).toNNReal) := by
    intro s hs
    rcases eq_or_lt_of_le (show s ≤ x from hs) with rfl | hlt
    · have h1 : s ∈ closure (Iio s) := by
        rw [closure_Iio' (a := s) ⟨0, hx⟩]; exact self_mem_Iic
      have h2 : Iio s ⊆ closure (Iio s ∩ range fun q : ℚ => (q : ℝ).toNNReal) :=
        denseRange_rat_toNNReal.open_subset_closure_inter isOpen_Iio
      have h3 : closure (Iio s) ⊆ closure (Iic s ∩ range fun q : ℚ => (q : ℝ).toNNReal) := by
        refine closure_minimal (h2.trans (closure_mono ?_)) isClosed_closure
        exact inter_subset_inter_left _ Iio_subset_Iic_self
      exact h3 h1
    · have h2 : Iio x ⊆ closure (Iio x ∩ range fun q : ℚ => (q : ℝ).toNNReal) :=
        denseRange_rat_toNNReal.open_subset_closure_inter isOpen_Iio
      exact closure_mono (inter_subset_inter_left _ Iio_subset_Iic_self) (h2 hlt)
  exact hEq.of_subset_closure hf hg inter_subset_left hsub self_mem_Iic

/-- **Agreement before the lifetime**: a driver continuous on `[0, min t ζ]` that agrees at the rational times
before its
lifetime with a driver regular at every sample (same lifetime) agrees with it at every time before the lifetime and not
after `t`. -/
theorem eq_of_agreeRat_lt {t : ℝ≥0∞} {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h : AgreeRat e e')
    (hec : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min t e.2}) (he' : IsRegularDriver e') {s : ℝ≥0}
    (hst : (s : ℝ≥0∞) ≤ t) (hsζ : (s : ℝ≥0∞) < e.2) : e.1 s = e'.1 s := by
  have hsub : Iic s ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) ≤ min t e.2} := fun r hr =>
    le_min ((ENNReal.coe_le_coe.2 hr).trans hst) ((ENNReal.coe_le_coe.2 hr).trans hsζ.le)
  have hsub' : Iic s ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) < e'.2} := fun r hr => by
    rw [← h.1]; exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hsζ
  refine eq_of_rat_le (hec.mono hsub) (he'.1.mono hsub') fun q hq => h.2 q ?_
  exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 hq) hsζ

/-- **The stopped drivers agree**: a driver continuous on `[0, min t ζ]` and starting at `0`, that agrees at the
rational times before its lifetime with a driver regular at every sample (with the same lifetime), has the same
stopped driver `canonDrv t`. At a finite lifetime reached before `t`, both values are the continuous left limit. -/
theorem canonDrv_eq_of_agreeRat {t : ℝ≥0∞} {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h : AgreeRat e e') (he0 : e.1 0 = 0)
    (hec : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min t e.2}) (he' : IsRegularDriver e') :
    canonDrv t e = canonDrv t e' := by
  have hζ : e.2 = e'.2 := h.1
  refine Prod.ext (funext fun r => ?_) (by simp only [canonDrv, hζ])
  change e.1 (min (r : ℝ≥0∞) (min t e.2)).toNNReal = e'.1 (min (r : ℝ≥0∞) (min t e'.2)).toNNReal
  rw [← hζ]
  set s : ℝ≥0 := (min (r : ℝ≥0∞) (min t e.2)).toNNReal with hs
  have hsr : (s : ℝ≥0∞) = min (r : ℝ≥0∞) (min t e.2) :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
  have hsm : (s : ℝ≥0∞) ≤ min t e.2 := by rw [hsr]; exact min_le_right _ _
  have hst : (s : ℝ≥0∞) ≤ t := hsm.trans (min_le_left _ _)
  rcases lt_or_ge (s : ℝ≥0∞) e.2 with hsζ | hsζ
  · exact eq_of_agreeRat_lt h hec he' hst hsζ
  -- the stop is the (finite) lifetime, reached before `t`
  have hsζ' : (s : ℝ≥0∞) = e.2 := le_antisymm (hsm.trans (min_le_right _ _)) hsζ
  have hζtop : e.2 ≠ ⊤ := by rw [← hsζ']; exact ENNReal.coe_ne_top
  have hζs : e.2.toNNReal = s := by rw [← hsζ', ENNReal.toNNReal_coe]
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
  · rw [← hs0, he0, he'.2.1]
  -- the left limit
  have hpos : 0 < e'.2 := by rw [← hζ, ← hsζ']; exact ENNReal.coe_pos.2 hs0
  have hcont : ContinuousWithinAt e.1 (Iic s) s := by
    have hsub : Iic s ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) ≤ min t e.2} := fun r hr =>
      (ENNReal.coe_le_coe.2 hr).trans hsm
    exact (hec.mono hsub) s self_mem_Iic
  have hlim : Tendsto e.1 (𝓝[<] s) (𝓝 (e.1 s)) := hcont.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  have hlim' : Tendsto e'.1 (𝓝[<] s) (𝓝 (e.1 s)) := by
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun r (hr : r < s) => ?_)
    have hrζ : (r : ℝ≥0∞) < e.2 := by rw [← hsζ']; exact ENNReal.coe_lt_coe.2 hr
    exact eq_of_agreeRat_lt h hec he' ((ENNReal.coe_le_coe.2 hr.le).trans hst) hrζ
  have := he'.2.2.2 (by rw [← hζ]; exact hζtop) hpos (e.1 s) (by rw [← hζ, hζs]; exact hlim')
  rw [← hζ, hζs] at this
  exact this.symm

end Stopped

end GW2Schedule

end Theorem14

end InteractingSLE
