import InteractingSLE.Foundations.Loewner.TraceClose
import InteractingSLE.Foundations.Loewner.YuanCharacterisationLimit
import InteractingSLE.Spec.Sec7.ContinuityProb9Prefix

/-!
# The trace-closure fact (`Sec7.TraceClosureStatement`), proved

Packet PROVE-TRACECLOSE. The named input `Sec7.TraceClosureStatement` of PROVE-SEC7-C10
(`Spec/Sec7/ContinuityProb9Prefix.lean`): if `η` generates the chain of `w` on `[0, σ]` (the frozen
`IsGeneratingTrace w σ η`: hulls before `σ`, continuity up to `σ`) and `w` is continuous on `[0, T)` with
`T > σ`, then `η` generates the chain on the closed interval `[0, σ]` with its tip at `σ`
(`IsGeneratingTraceIcc w σ η`).

The deterministic Loewner theory is `Foundations/Loewner/TraceClose.lean` (on `ℝ`, for a continuous
driver); here the driver is frozen after a time `t₂ ∈ (σ, T)` (`frozenDrive`, as in `TraceBridge`), which
changes neither the hull nor the inverse map at time `σ`.

## Main results

* `Sec7.IsGeneratingTrace.isGeneratingTraceIcc_of_lt`: the closed-interval form at the horizon itself;
* `Sec7.traceClosureStatement : Sec7.TraceClosureStatement`;
* `Sec7.oneSidedPrefixStatement`: Theorem 1.3's one-sided input, unconditionally;
* `Sec7.lp9PrefixStatement_of_seed`: the LP9 input from the two-sided seed trace alone.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

universe u

namespace InteractingSLE

variable {w : ℝ≥0 → ℝ} {σ : ℝ≥0} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- The frozen generating trace on `[0, σ]`, read on `ℝ`, is a continuous Loewner trace of the driver
frozen after `t₂ > σ`, before the horizon `σ`. -/
theorem IsGeneratingTrace.isLoewnerTraceLT_horizon (hη : IsGeneratingTrace w σ η) {t₂ : ℝ}
    (hσt₂ : (σ : ℝ) < t₂) :
    IsLoewnerTraceLT (frozenDrive w t₂) σ (fun s : ℝ => η s.toNNReal) := by
  refine ⟨by simpa using hη.1, ?_, fun t ht htσ => ?_⟩
  · refine hη.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ σ
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2.le)
  · have htT : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < σ :=
      ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe ht).2 htσ)
    have hfill := hη.2.2 t.toNNReal htT
    rw [Real.coe_toNNReal _ ht] at hfill
    have hA : IsCompact (η '' Icc 0 t.toNNReal) := isCompact_Icc.image_of_continuousOn
      (hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans htT.le)
    rw [fwdHull_eq_of_eqOn ht (htσ.trans hσt₂) (fun r hr => frozenDrive_eq hr),
      image_toNNReal_Icc η ht]
    exact (fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed
      ((QuantumZipper.fwdHull_mono).2 _)).1 hfill

namespace Sec7

/-- **Closing a generating trace at its horizon.** If `η` generates the chain of `w` on `[0, σ]` and `w`
is continuous on `[0, T)` with `T > σ`, then the hull at `σ` is the filling of `η([0, σ])` and
`F_σ(z) → η(σ)` as `z → 0` in `ℍ`. -/
theorem IsGeneratingTrace.isGeneratingTraceIcc_of_lt (hη : IsGeneratingTrace w σ η)
    (hσT : (σ : ℝ≥0∞) < T) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0) :
    IsGeneratingTraceIcc w σ η := by
  refine ⟨hη, ?_⟩
  obtain ⟨t₂, hσt₂, ht₂T⟩ := exists_real_btwn_of_lt hσT
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg σ).trans hσt₂.le
  set W := frozenDrive w t₂ with hWdef
  have hW : Continuous W := continuous_frozenDrive_of_lt hw ht₂T
  have hW0 : W 0 = 0 := by rw [hWdef, frozenDrive_zero ht₂, hw0]
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) σ = fwdHull W σ :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg σ) hσt₂ (fun r hr => (frozenDrive_eq hr).symm)
  have hF : fwdMapInv (fun s : ℝ => w s.toNNReal) σ = fwdMapInv W σ :=
    fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg σ) hσt₂ (fun r hr => (frozenDrive_eq hr).symm)
  have hAc : IsCompact (η '' Icc 0 σ) := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun r hr => ENNReal.coe_le_coe.2 hr.2)
  rw [hK, hF]
  rcases eq_or_ne σ 0 with h0 | hσ0
  · -- `σ = 0`: the hull is empty and `F_0` is the identity
    subst h0
    refine ⟨?_, ?_⟩
    · refine (fillH_eq_iff_isFilling_of_isClosed hAc.isBounded hAc.isClosed
        (QuantumZipper.fwdHull_mono.2 _)).2 ?_
      rw [show ((0 : ℝ≥0) : ℝ) = 0 from rfl, QuantumZipper.RS.fwdHull_zero_eq_empty hW]
      refine (YuanCharacterisation.fillH_eq_empty_of_subset ?_).symm
      rintro _ ⟨r, hr, rfl⟩
      have : r = 0 := le_antisymm hr.2 hr.1
      subst this
      show (η 0).im ≤ 0
      rw [hη.1, zero_im]
    · rw [hη.1]
      refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (fwdMapInv_zero_time hW hW0 hz).symm
  · have hσ : (0 : ℝ) < σ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ0)
    have hη' := hη.isLoewnerTraceLT_horizon hσt₂
    have hησ : ContinuousOn (fun s : ℝ => η s.toNNReal) (Icc 0 σ) :=
      hη.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => by
        show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ σ
        exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    refine ⟨?_, ?_⟩
    · rw [TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT hη' hW hW0 hσ hησ,
        image_toNNReal_Icc η (NNReal.coe_nonneg σ), Real.toNNReal_coe]
      exact isFilling_fillH hAc
    · have := TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT hη' hW hW0 hσ hησ
      simpa using this

/-- **The trace-closure fact** (PROVE-SEC7-C10's named input; PROVE-ZHAN-A6 item 4), proved. -/
theorem traceClosureStatement : TraceClosureStatement :=
  fun _ _ _ hσT hw hw0 _ hη => IsGeneratingTrace.isGeneratingTraceIcc_of_lt hη hσT hw hw0

/-- **Theorem 1.3's one-sided input** (R7 of the target change, `κ < 4` induction), unconditionally. -/
theorem oneSidedPrefixStatement : OneSidedPrefixStatement.{u} :=
  oneSidedPrefixStatement_of_closure traceClosureStatement

/-- **Theorem 1.3's LP9 input** from the two-sided seed case of the retargeted trace alone. -/
theorem lp9PrefixStatement_of_seed {κ : ℝ} (hκ : 0 < κ) (hseed : LP9SeedTraceStatement.{u} κ) :
    LP9PrefixStatement.{u} κ :=
  lp9PrefixStatement_of_closure hκ traceClosureStatement hseed

end Sec7

end InteractingSLE
