/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CovWire
import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc

/-!
# The pre-clock hulls of a simple restarted path stay in its window

Packet PROVE-AUX61-R2C. Astra's follow-up 4 L104–L106: "Until its next contact with `∂D`, the forward continuation is
an interior simple slit in `D`." Before the window clock `e` (the first exit of the restarted path from the window
`V`, capped by its lifetime) a simple path started at `0` and in `ℍ` afterwards has filled hull equal to its own
range (`YuanCharacterisation.fillH_image_eq`), which lies in `V`. So the `hull_buffer` field of `ActFibre` follows
from `V ⊆ buffer`, a.s. injectivity and a.s. interiority of the path before its lifetime (the path inputs of
PROVE-AUX61-R45's clock constructors).

* `closure_fwdHull_subset_of_exit` (deterministic);
* **`ae_hull_buffer_of_exit`**: the `hull_buffer` clause for a reference clock of a clock source.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cov

open QuantumZipper (H fwdHull)

universe u

/-- **Before the exit from `V`, the hull of a simple interior path lies in `V`** (with its closure). -/
theorem closure_fwdHull_subset_of_exit {w : ℝ≥0 → ℝ} {e U : ℝ≥0∞} {Γ : ℝ≥0 → ℂ} {V : Set ℂ}
    (htr : IsGeneratingTrace w e Γ) (hinj : InjOn Γ {t | (t : ℝ≥0∞) ≤ e})
    (hint : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < e → Γ t ∈ H) (hexit : e = RLC.exitTime V Γ U)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < e) : closure (fwdHull (Ito.rpath w) t) ⊆ V := by
  obtain ⟨h0, hc, hfill⟩ := htr
  set ζ : ℝ → ℂ := fun s => Γ s.toNNReal with hζ
  have hle : ∀ s : ℝ, s ∈ Icc (0 : ℝ) t → ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e := fun s hs => by
    refine le_trans ?_ ht.le
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have himg : Γ '' Icc 0 t = ζ '' Icc 0 (t : ℝ) := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, ⟨s.coe_nonneg, NNReal.coe_le_coe.2 hs.2⟩, by simp [hζ]⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩, rfl⟩
  have hζc : ContinuousOn ζ (Icc 0 (t : ℝ)) := by
    refine hc.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    exact hle s hs
  have hζi : InjOn ζ (Icc 0 (t : ℝ)) := by
    intro a ha b hb hab
    have := hinj (hle a ha) (hle b hb) hab
    rw [← Real.coe_toNNReal a ha.1, ← Real.coe_toNNReal b hb.1, this]
  have hζ0 : (ζ 0).im = 0 := by simp [hζ, h0]
  have hζH : MapsTo ζ (Ioc 0 (t : ℝ)) H := by
    intro s hs
    refine hint _ (Real.toNNReal_pos.2 hs.1) (lt_of_le_of_lt ?_ ht)
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hcomp : IsCompact (ζ '' Icc 0 (t : ℝ)) := isCompact_Icc.image_of_continuousOn hζc
  have hhull : fwdHull (Ito.rpath w) t = fillH (ζ '' Icc 0 (t : ℝ)) := by
    rw [← himg]
    exact Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling (himg ▸ hcomp) (hfill t ht)
  rw [hhull, YuanCharacterisation.fillH_image_eq t.coe_nonneg hζc hζi hζ0 hζH]
  refine (closure_mono (image_mono Ioc_subset_Icc_self)).trans ?_
  rw [hcomp.isClosed.closure_eq]
  rintro _ ⟨s, hs, rfl⟩
  by_contra hV
  have hex : RLC.exitTime V Γ U ≤ ((s.toNNReal : ℝ≥0) : ℝ≥0∞) :=
    (min_le_right _ _).trans
      (iInf₂_le (f := fun (s' : ℝ≥0) (_ : Γ s' ∉ V) => (s' : ℝ≥0∞)) s.toNNReal hV)
  rw [← hexit] at hex
  exact absurd (lt_of_le_of_lt hex (lt_of_le_of_lt
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) ht)) (lt_irrefl _)

/-- **The `hull_buffer` clause of an actual fibre from its path inputs**: for a reference clock with window `V`
of a clock source started at `0`, if `V ⊆ buffer`, the source path is a.s. injective through the clock and a.s. in
`ℍ` at positive times before its lifetime, then a.s. every pre-clock hull has its closure in the buffer. -/
theorem ae_hull_buffer_of_exit {S : Type u} [MeasurableSpace S] {CS : Aux61R45.ClockSource S} (hy : CS.y = 0)
    {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {V buffer : Set ℂ} (RC : Aux61R45.ReferenceClock CS κ b J 0 V)
    (hVb : V ⊆ buffer) (hinj : ∀ᵐ ω ∂CS.P, InjOn (CS.Γ ω) {t | (t : ℝ≥0∞) ≤ RC.e ω})
    (hint : ∀ᵐ ω ∂CS.P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < CS.U ω → CS.Γ ω t ∈ H) :
    ∀ᵐ ω ∂CS.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < RC.e ω → closure (fwdHull (Ito.rpath (RC.W · ω)) t) ⊆ buffer := by
  filter_upwards [RC.trace, RC.ae_exit, hinj, hint] with ω htr hex hi hH t ht
  have htr' : IsGeneratingTrace (RC.W · ω) (RC.e ω) (CS.Γ ω) := by
    simpa only [hy, Complex.ofReal_zero, sub_zero] using htr
  refine (closure_fwdHull_subset_of_exit htr' hi (fun s hs hse => hH s hs (lt_of_lt_of_le hse (RC.le_source ω)))
    hex ht).trans hVb

end InteractingSLE.Sec5.Aux61Cov
