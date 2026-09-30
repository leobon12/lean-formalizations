import QuantumZipper.Proofs.Thm11.ExtMeasFloor
import QuantumZipper.Proofs.Thm11.ExtMeasLimit

/-!
# THM11-AD8: joint measurability of `𝔥^ext_T` — the pointwise identification (task EXT-MEAS)

`hTfwdExt_eq_candExt` identifies the extended field of Theorem 1.1's addendum with the manifestly
measurable candidate `candExt` of `ExtMeas.lean`, and `extMeasStmt` is the node consumed by the
addendum assembly (`Thm11Asm.ExtMeasStmt`).

The identification: on the hull of time `T`, `hTfwdExt` is `limUnder (𝓝[<] τ(z))` of the field
formula `rawFieldAt`.  If the guard `guardAt` holds, then by `MeasLimit.tendsto_iff_ratOsc`
(continuity below the swallowing time, `MeasCont.continuousOn_fieldAt_Icc`) the left limit `L`
exists; the dyadic floors `dpt j (cellK j)` tend to `τ(z)` from below, so the candidate's
`atTop`-limit of `dval` is also `L` (`Tendsto.limUnder_eq`).  If the guard fails, then no left
limit exists and both `limUnder`s take the same junk value `Classical.choice ‹Nonempty ℝ›`
(`limUnder_of_not_tendsto`): the candidate's by construction, `hTfwdExt`'s because
`limUnder_of_not_tendsto_eq_junkReal`.  Off the hull both sides are `hTfwd = extFieldAt · T`.

Own argument (blueprint §9 AD-8); the analytic inputs are the companion modules
`ExtMeasTamed`/`ExtMeasCont`/`ExtMeasLimit` (own elementary proofs).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Classical
open scoped NNReal ENNReal Topology
open QuantumZipper.NonSwallow

namespace QuantumZipper
namespace Thm11Asm

section Final

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {κ T : ℝ}

/-- The field formula is continuous on `[a,b]` as long as `b < tauAt`. -/
theorem continuousOn_rawField_Icc {p : ℂ × Ω} (hW : Continuous (drive κ B p.2))
    (hσ : swallowTime (drive κ B p.2) p.1 = ENNReal.ofReal (tauAt κ B p)) (hz : 0 < p.1.im) :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b < tauAt κ B p →
      ContinuousOn (rawFieldAt κ B · p) (Icc a b) := by
  intro a b ha hab hb
  have hb' : p.1 ∉ fwdHull (drive κ B p.2) b :=
    not_mem_hull_of_lt_tauAt hσ hz (ha.trans hab) hb
  simpa only [rawFieldAt] using
    MeasCont.continuousOn_fieldAt_Icc hW κ hz ha hab hb'

/-- **The guard is the rational-oscillation condition of `MeasLimit`.** -/
theorem guardAt_iff_ratOsc {p : ℂ × Ω}
    (hσ : swallowTime (drive κ B p.2) p.1 = ENNReal.ofReal (tauAt κ B p)) (hz : 0 < p.1.im) :
    guardAt κ B p ↔ ∀ n : ℕ, ∃ m : ℕ, MeasLimit.RatOsc (rawFieldAt κ B · p) (tauAt κ B p) m n := by
  constructor
  · intro hg n
    obtain ⟨m, hm⟩ := hg n
    refine ⟨m, fun q q' hq0 hq hqm hq'0 hq' hq'm => ?_⟩
    have hqm' : tauAt κ B p ≤ (q : ℝ) + 1 / ((m : ℝ) + 1) := by linarith
    have hq'm' : tauAt κ B p ≤ (q' : ℝ) + 1 / ((m : ℝ) + 1) := by linarith
    have hw : win κ B m ⟨q, hq0⟩ p :=
      ⟨not_mem_hull_of_lt_tauAt hσ hz hq0 hq,
        (mem_hull_iff_tauAt hσ hz (by positivity)).mpr hqm'⟩
    have hw' : win κ B m ⟨q', hq'0⟩ p :=
      ⟨not_mem_hull_of_lt_tauAt hσ hz hq'0 hq',
        (mem_hull_iff_tauAt hσ hz (by positivity)).mpr hq'm'⟩
    have h1 := hm ⟨q, hq0⟩ ⟨q', hq'0⟩ hw hw'
    rwa [extFieldAt_eq_raw hσ hz hq0 hq, extFieldAt_eq_raw hσ hz hq'0 hq'] at h1
  · intro h n
    obtain ⟨m, hm⟩ := h n
    refine ⟨m, fun q q' hw hw' => ?_⟩
    have hq0 : (0 : ℝ) ≤ (q.1 : ℝ) := q.2
    have hq'0 : (0 : ℝ) ≤ (q'.1 : ℝ) := q'.2
    have hq : (q.1 : ℝ) < tauAt κ B p := by
      by_contra hle
      exact hw.1 ((mem_hull_iff_tauAt hσ hz hq0).mpr (not_lt.mp hle))
    have hq' : (q'.1 : ℝ) < tauAt κ B p := by
      by_contra hle
      exact hw'.1 ((mem_hull_iff_tauAt hσ hz hq'0).mpr (not_lt.mp hle))
    have hqm : tauAt κ B p - 1 / ((m : ℝ) + 1) ≤ (q.1 : ℝ) := by
      have := (mem_hull_iff_tauAt hσ hz (by positivity :
        (0 : ℝ) ≤ (q.1 : ℝ) + 1 / ((m : ℝ) + 1))).mp hw.2
      linarith
    have hq'm : tauAt κ B p - 1 / ((m : ℝ) + 1) ≤ (q'.1 : ℝ) := by
      have := (mem_hull_iff_tauAt hσ hz (by positivity :
        (0 : ℝ) ≤ (q'.1 : ℝ) + 1 / ((m : ℝ) + 1))).mp hw'.2
      linarith
    have h1 := hm q.1 q'.1 hq0 hq hqm hq'0 hq' hq'm
    rwa [extFieldAt_eq_raw hσ hz hq0 hq, extFieldAt_eq_raw hσ hz hq'0 hq']

/-- **The extended field equals the measurable candidate.** -/
theorem hTfwdExt_eq_candExt (hBm : ∀ r : ℝ≥0, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (hκ4 : 4 < κ) (hκ8 : κ < 8) (hT : 0 < T)
    (p : ℂ × Ω) :
    hTfwdExt κ (drive κ B p.2) T p.1 = candExt κ B T p := by
  have hW : Continuous (drive κ B p.2) := continuous_drive_ns hBc κ p.2
  by_cases hmem : p.1 ∈ fwdHull (drive κ B p.2) T
  · obtain ⟨hσ, hτ0, hτT⟩ := tauAt_spec hW hT.le hmem
    have hz : 0 < p.1.im := hmem.1
    have hcont := continuousOn_rawField_Icc hW hσ hz
    rw [hTfwdExt, if_pos hmem, candExt, if_pos hmem]
    by_cases hg : guardAt κ B p
    · rw [if_pos hg]
      obtain ⟨L, hL⟩ :=
        (MeasLimit.tendsto_iff_ratOsc hτ0 hcont).mpr ((guardAt_iff_ratOsc hσ hz).mp hg)
      rw [show limUnder (𝓝[<] (swallowTime (drive κ B p.2) p.1).toReal)
          (fun s => h0fwd κ (fwdMap (drive κ B p.2) s p.1)
            - chiC κ * (logDerivFwd (drive κ B p.2) s p.1).im) =
          limUnder (𝓝[<] (tauAt κ B p)) (rawFieldAt κ B · p) from rfl,
        hL.limUnder_eq]
      have hseq : Tendsto (fun j => dval κ B T j p) atTop (𝓝 L) :=
        (hL.comp (tendsto_dpt_cellK (κ := κ) (B := B) hτ0)).congr'
          (Eventually.of_forall fun j => (dval_eq hσ hz hτ0 hτT j).trans
            (extFieldAt_eq_raw hσ hz (dpt_nonneg j (cellK κ B j p))
              (cellK_spec hτ0 j).1) |>.symm)
      exact hseq.limUnder_eq.symm
    · rw [if_neg hg]
      have hno : ¬ ∃ L : ℝ, Tendsto (fun s => h0fwd κ (fwdMap (drive κ B p.2) s p.1)
          - chiC κ * (logDerivFwd (drive κ B p.2) s p.1).im) (𝓝[<] (tauAt κ B p)) (𝓝 L) := by
        rintro ⟨L, hL⟩
        refine hg ((guardAt_iff_ratOsc hσ hz).mpr
          ((MeasLimit.tendsto_iff_ratOsc hτ0 hcont).mp ⟨L, ?_⟩))
        simpa only [rawFieldAt] using hL
      exact limUnder_of_not_tendsto_eq_junkReal hno
  · rw [hTfwdExt, if_neg hmem, candExt, if_neg hmem]
    by_cases hD : p.1 ∈ H \ fwdHull (drive κ B p.2) T
    · rw [extFieldAt_of_mem (p := p) (s := T) (κ := κ) (B := B) hD, rawFieldAt]
      unfold hTfwd
      rw [if_pos hD]
    · rw [extFieldAt_of_notMem (p := p) (s := T) (κ := κ) (B := B) hD]
      unfold hTfwd
      rw [if_neg hD]

/-- **AD-8 measurability node.** For `4 < κ < 8`, `T > 0` and a driving field with measurable
coordinates and continuous paths, the extended field is jointly measurable in `(ω, z)`. -/
theorem extMeasStmt : ExtMeasStmt := by
  intro κ T hκ4 hκ8 hT Ω _ B hBm hBc
  have h1 : Measurable (fun q : ℂ × Ω => candExt κ B T q) := measurable_candExt hBm hBc κ hT.le
  have h2 : Measurable (fun p : Ω × ℂ => candExt κ B T (p.2, p.1)) :=
    h1.comp (measurable_snd.prodMk measurable_fst :
      Measurable fun p : Ω × ℂ => (p.2, p.1))
  rw [show (fun p : Ω × ℂ => hTfwdExt κ (drive κ B p.1) T p.2) =
      fun p : Ω × ℂ => candExt κ B T (p.2, p.1) from
    funext fun p => hTfwdExt_eq_candExt hBm hBc hκ4 hκ8 hT (p.2, p.1)]
  exact h2

end Final

end Thm11Asm
end QuantumZipper
