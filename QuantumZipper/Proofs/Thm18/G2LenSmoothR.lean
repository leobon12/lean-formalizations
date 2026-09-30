import QuantumZipper.Proofs.Thm18.G2LenSmoothRMeas
import QuantumZipper.Proofs.Thm18.G2LenSmoothX

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 smoothing, `R` side: `G2RootRLenSmoothStmt` from the clipped-shift node

The twin of `G2LenSmoothGap.lean` + `G2LenSmoothX.lean` at the rooted point `y` in region 2
(Sheffield, arXiv:1012.4797, proof of Prop. 5.5, pp. 65–66; proof of Thm. 1.8, p. 71: "the same
applies when we zoom in near `R(x)`"). The length is `L = ν_h[0, y]`, the cut length
`ν_h[0, y − κ]`, the gap `ν_h(y − κ, y]`:

1. **gap → 0** (proved, `g3GapR_small`): no atoms and continuity from below give
   `ν_h[0, y − 1/(n+1)] ↑ ν_h[0, y) = ν_h[0, y]`; the rooted measure is the finite measure
   `g3RootR` (`G2LenSmoothRMeas.lean`);
2. **node** `G2RootRClipSmoothStmt`: conditioning (outside event and truncation `≤ M`) on `L`
   versus on the clipped length `max(ν_h[0, y − κ], L − ρ) = L − min(gap, ρ)`; Sheffield's bump
   `φ₂` sits in region 2 between `0` and `y − κ` (to the left of the margin), so `M = ν_h[−δ, 0]`,
   the outside field and the gap do not depend on its coefficient `α₂`.

`g2RootRLenSmoothStmt_of_clip` assembles them; `g2RootLenSmooth_of_clip` gives both smoothing
nodes of `g2FixMixStmt_of_agreeNodes`. Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The rooted event `{y a margin m inside (t − r, t + r), ν_h[0, y] − ν_h[0, y − κ] > ρ}`. -/
def g3GapEvR (γ t r m κ ρ : ℝ) : Set (Ω₀ × ℝ × ℝ) :=
  {q | |q.2.2 - t| + m < r ∧ ρ < q.2.1 - g3CutLenR γ κ q.1 q.2.2}

def g3GapEvRM (γ : ℝ) (i : G3Idx) (m κ ρ : ℝ) : Set (Ω₀ × ℝ × ℝ) :=
  {q | |q.2.2 - i.t₂| + m < i.r₂ ∧ ρ < q.2.1 - g3CutLenRM γ i κ q.1 q.2.2}

theorem measurableSet_margin₂ (i : G3Idx) (m : ℝ) :
    MeasurableSet {q : Ω₀ × ℝ × ℝ | |q.2.2 - i.t₂| + m < i.r₂} := by
  have hf : Measurable fun q : Ω₀ × ℝ × ℝ => |q.2.2 - i.t₂| + m := by fun_prop
  exact measurableSet_lt hf measurable_const

theorem measurableSet_g3GapEvRM (γ : ℝ) (i : G3Idx) (m κ ρ : ℝ) :
    MeasurableSet (g3GapEvRM γ i m κ ρ) :=
  (measurableSet_margin₂ i m).inter (measurableSet_lt measurable_const
    ((measurable_fst.comp measurable_snd).sub (measurable_g3CutLenRM γ i κ)))

theorem g3GapEvRM_mono (γ : ℝ) (i : G3Idx) (m ρ : ℝ) {κ κ' : ℝ} (h : κ ≤ κ') :
    g3GapEvRM γ i m κ ρ ⊆ g3GapEvRM γ i m κ' ρ := fun q hq =>
  ⟨hq.1, by linarith [hq.2, g3CutLenRM_mono γ i q.1 q.2.2 h]⟩

/-- The window `(a, b)` of the margin, with `0 < b < t₂ + r₂`. -/
def g3bR (i : G3Idx) (m : ℝ) : ℝ := max (i.t₂ + i.r₂ - m) ((i.t₂ + i.r₂) / 2)

theorem g3bR_props (i : G3Idx) {m : ℝ} (hm : 0 < m) :
    0 < i.t₂ - i.r₂ ∧ 0 < g3bR i m ∧ g3bR i m < i.t₂ + i.r₂ ∧
      ∀ y : ℝ, |y - i.t₂| + m < i.r₂ → i.t₂ - i.r₂ < y ∧ y < g3bR i m := by
  have h1 := i.t₂_sub_r₂
  have h2 := i.t₂_add_r₂
  have hη := i.hη
  refine ⟨by linarith, lt_max_of_lt_right (by linarith),
    max_lt (by linarith) (by linarith), fun y hy => ?_⟩
  have a1 := le_abs_self (y - i.t₂)
  have a2 := neg_abs_le (y - i.t₂)
  exact ⟨by linarith, lt_max_of_lt_left (by linarith)⟩

/-- Pointwise: along `κ = 1/(n+1)` the gap at `y` tends to `ν_h{y} = 0`. -/
theorem not_mem_iInter_g3GapEvRM {γ : ℝ} (i : G3Idx) {ω : Ω₀} {m ρ : ℝ} (hm : 0 < m)
    (hρ : 0 < ρ) (hwin : ∀ s ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4),
      (g3ν₀ γ i ω + g3ν₂ γ i ω) s = g3Hν γ ω s)
    (hat : ∀ t, g3Hν γ ω {t} = 0) (y : ℝ) :
    (ω, (g3Hν γ ω (Icc 0 y)).toReal, y) ∉ ⋂ n : ℕ, g3GapEvRM γ i m (1 / ((n : ℝ) + 1)) ρ := by
  intro hmem
  simp only [mem_iInter] at hmem
  obtain ⟨ha0, -, hbt, hsub⟩ := g3bR_props i hm
  have hy := hsub y (hmem 0).1
  set ν := g3Hν γ ω
  have hW : Icc 0 y ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4) := fun z hz =>
    ⟨by linarith [hz.1, i.hη], by linarith [hz.2, i.t₂_add_r₂]⟩
  have hcut : ∀ n : ℕ, g3CutLenRM γ i (1 / ((n : ℝ) + 1)) ω y =
      (ν (Icc 0 (y - 1 / ((n : ℝ) + 1)))).toReal := fun n => by
    have h0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hs : Icc 0 (y - 1 / ((n : ℝ) + 1)) ⊆ Icc 0 y := Icc_subset_Icc_right (by linarith)
    unfold g3CutLenRM
    rw [hwin _ (hs.trans hW)]
  have hfin : ν (Icc 0 y) ≠ ⊤ := by
    rw [← hwin _ hW]; exact g3ν₀₂_Icc_ne_top γ i ω y
  have hmono : Monotone fun n : ℕ => Icc (0 : ℝ) (y - 1 / ((n : ℝ) + 1)) := by
    intro n k hnk
    have hnk' : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnk
    exact Icc_subset_Icc_right (by linarith [one_div_le_one_div_of_le (by positivity) hnk'])
  have hU : (⋃ n : ℕ, Icc (0 : ℝ) (y - 1 / ((n : ℝ) + 1))) = Ico 0 y := by
    ext z
    simp only [mem_iUnion, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨n, h1, h2⟩
      exact ⟨h1, by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                    linarith⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h2)
      exact ⟨n, h1, by linarith⟩
  have hIco : ν (Ico 0 y) = ν (Icc 0 y) := by
    refine le_antisymm (measure_mono Ico_subset_Icc_self) ?_
    calc ν (Icc 0 y) ≤ ν ({y} ∪ Ico 0 y) := measure_mono fun z hz => by
          rcases eq_or_lt_of_le hz.2 with h | h
          · exact Or.inl h
          · exact Or.inr ⟨hz.1, h⟩
      _ ≤ ν {y} + ν (Ico 0 y) := measure_union_le _ _
      _ = ν (Ico 0 y) := by rw [hat, zero_add]
  have ht := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hU, hIco] at ht
  have ht' : Tendsto (fun n : ℕ => (ν (Icc 0 y)).toReal -
      (ν (Icc 0 (y - 1 / ((n : ℝ) + 1)))).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal hfin).comp ht
    have h2 := (tendsto_const_nhds (x := (ν (Icc 0 y)).toReal)).sub this
    rw [sub_self] at h2
    exact h2
  obtain ⟨n, hn⟩ := (ht'.eventually (gt_mem_nhds hρ)).exists
  have := (hmem n).2
  rw [hcut n] at this
  linarith

/-- **The gap at `R` tends to zero in rooted measure.** -/
theorem g3GapR_small {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    {ρ : ℝ} (hρ : 0 < ρ) {ε : ℝ} (hε : 0 < ε) : ∃ ε₀ > 0, ∀ κ ∈ Ioo 0 ε₀,
      (g3RootIntR γ i ((g3GapEvR γ i.t₂ i.r₂ m κ ρ).indicator 1)).toReal ≤ ε := by
  obtain ⟨ha0, hb0, hbt, hsub⟩ := g3bR_props i hm
  set b := g3bR i m
  have hsubT : ∀ κ, ∀ q ∈ g3GapEvRM γ i m κ ρ, i.t₂ - i.r₂ < q.2.2 ∧ q.2.2 < b :=
    fun κ q hq => hsub _ hq.1
  set T : ℕ → Set (Ω₀ × ℝ × ℝ) := fun n => g3GapEvRM γ i m (1 / ((n : ℝ) + 1)) ρ with hT
  have hTm : ∀ n, MeasurableSet (T n) := fun n => measurableSet_g3GapEvRM γ i m _ ρ
  have hanti : Antitone T := by
    intro n k hnk
    have hnk' : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnk
    exact g3GapEvRM_mono γ i m ρ (one_div_le_one_div_of_le (by positivity) hnk')
  have hfin0 : g3RootR γ i b (T 0) ≠ ⊤ := by
    rw [g3RootR_apply_eq hγ hγ2 i (hTm 0) ha0 hb0 hbt (hsubT _)]
    exact (g3RootIntR_indicator_lt_top hγ hγ2 i _).ne
  have ht := tendsto_measure_iInter_atTop (μ := g3RootR γ i b)
    (fun n => (hTm n).nullMeasurableSet) hanti ⟨0, hfin0⟩
  have hzero : g3RootR γ i b (⋂ n, T n) = 0 := by
    rw [g3RootR_apply_eq hγ hγ2 i (MeasurableSet.iInter hTm) ha0 hb0 hbt
      (fun q hq => hsubT _ q (mem_iInter.1 hq 0))]
    unfold g3RootIntR
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_g3Fid_sets hγ hγ2, G3Fid.ae_normField_good gffBase.gff hγ hγ2]
      with ω hω hgood
    refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Icc
      fun y _ => ?_).trans lintegral_zero
    exact indicator_of_notMem (not_mem_iInter_g3GapEvRM i hm hρ (hω i).2 hgood.2.2 y) _
  rw [hzero] at ht
  obtain ⟨N, hN⟩ := (ht.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  have hN' : g3RootR γ i b (T N) < ENNReal.ofReal ε := hN
  refine ⟨1 / ((N : ℝ) + 1), by positivity, fun κ hκ => ?_⟩
  rw [show g3GapEvR γ i.t₂ i.r₂ m κ ρ =
      {q | |q.2.2 - i.t₂| + m < i.r₂ ∧ ρ < q.2.1 - g3CutLenR γ κ q.1 q.2.2} from rfl,
    g3RootIntR_cut_eq hγ hγ2 i hκ.1.le hm.le (fun q c => |q.2.2 - i.t₂| + m < i.r₂ ∧ ρ < q.2.1 - c)
      (fun q c h => h.1)]
  change (g3RootIntR γ i ((g3GapEvRM γ i m κ ρ).indicator 1)).toReal ≤ ε
  rw [← g3RootR_apply_eq hγ hγ2 i (measurableSet_g3GapEvRM γ i m κ ρ) ha0 hb0 hbt (hsubT κ)]
  refine ENNReal.toReal_le_of_le_ofReal hε.le (le_of_lt (lt_of_le_of_lt ?_ hN'))
  exact measure_mono (g3GapEvRM_mono γ i m ρ hκ.2.le)

end Thm18Asm
end QuantumZipper
