import QuantumZipper.Proofs.Zipper.LocLenR5aFlowDet
import QuantumZipper.Proofs.Zipper.LocLenR5aLen
import QuantumZipper.Proofs.Zipper.FlowRegG4
import QuantumZipper.Proofs.Wire2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5a (D75): `E6PalmRegArcStmt` from the open-arc length-infinity of the `Γ⁰` sample

* `ae_flowLenArc`: open-arc copy of the flow length node `E6.FlowLenStmt` (E6FlowGood.lean:141):
  a.s., for every `u ≥ 0`, the left open-arc length `M_u(s)` of `C_u = zipCapDown γ u 𝒵` is
  monotone, tends to `0` as `s ↓ 0`, and is unbounded. Proof: `M_u(s)` is the `ν_{h⁰_N}`-mass of
  `(0₋(N − u), 0₋(N − u − s))` at every integer horizon `N ≥ u + s` (`lenCollidedArcStmt_holds`),
  the fixed-chart measure is atomless and finite on compacts (`Wire2.ae_nu0_regular`), `0₋` is
  continuous and strictly decreasing (`Wire2.ae_zeroMinus_Vr_facts`); unboundedness from the
  total left open-arc length of `𝒵` (`CfgLenInfArcStmt`) and the three-piece split
  `(0₋(N), 0₋(N − t)) ⊆ (0₋(N), 0₋(N − u)) ∪ {0₋(N − u)} ∪ (0₋(N − u), 0₋(N − u − t))`.
* `flowGoodArcStmt_of_lenInf`, `e6PalmRegArc_of_lenInf`: copies of `E6.flowGoodStmt_of`,
  `E6.flowGoodAllStmt_of` (E6FlowGood.lean:152–177) with `hitScaleGoodArc_canon`.

**Remaining input** `CfgLenInfArcStmt`: the open-arc copy of `E6.CfgLenInfStmt`
(E6FlowLen.lean:90): the left side of `η[0,t]` has quantum length tending to `∞` as `t → ∞`
(Sheffield arXiv:1012.4797 §5.4 pp. 70–72 uses it without proof; the old proof is the drift
argument of LenInfCore.lean, which was wired through the tip core).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 E1 D3Plus E6 R5c

/-- Open-arc copy of `E6.CfgLenInfStmt` at every setup: a.s. the total left open-arc length of
the `Γ⁰` sample is infinite. -/
def CfgLenInfArcStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ⨆ t ∈ Ici (0 : ℝ), (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) t).1 = ⊤

/-- Three-piece split of an open interval, with no atom at the cut. -/
theorem measure_Ioo_le_split {ν : Measure ℝ} {a b c d : ℝ} (hcd : c ≤ d) (hb : ν {b} = 0) :
    ν (Ioo a c) ≤ ν (Ioo a b) + ν (Ioo b d) := by
  calc ν (Ioo a c) ≤ ν (Ioo a b ∪ ({b} ∪ Ioo b d)) := measure_mono fun x hx => by
        rcases lt_trichotomy x b with h | h | h
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨h, hx.2.trans_le hcd⟩)
    _ ≤ ν (Ioo a b) + (ν {b} + ν (Ioo b d)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ = ν (Ioo a b) + ν (Ioo b d) := by rw [hb, zero_add]

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The flow length node with open arcs** (copy of `E6.FlowLenStmt`, all `u ≥ 0`). -/
theorem ae_flowLenArc {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hI : ∀ᵐ ω ∂P, ⨆ t ∈ Ici (0 : ℝ), (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) t).1 = ⊤) :
    ∀ᵐ ω ∂P, ∀ u : ℝ, 0 ≤ u →
      MonotoneOn (fun t => (unzipLengthsArc (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) t).1) (Ici 0) ∧
      Tendsto (fun t => (unzipLengthsArc (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) t).1) (𝓝[>] 0) (𝓝 0) ∧
      ⨆ t ∈ Ici (0 : ℝ),
        (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) t).1 = ⊤ := by
  have hN : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  filter_upwards [ae_all_iff.2 fun n : ℕ =>
      lenCollidedArcStmt_holds (T := (n : ℝ) + 1) hκ hκ4 (hN n) hB hX hind,
    ae_all_iff.2 fun n : ℕ => b5UniformArcStmt_holds κ hκ hκ4 ((n : ℝ) + 1) (hN n) P B X hB hX hind,
    ae_all_iff.2 fun n : ℕ => Wire2.ae_nu0_regular (T := (n : ℝ) + 1) hκ hκ4 (hN n) hB hX hind,
    ae_all_iff.2 fun n : ℕ => Wire2.ae_zeroMinus_Vr_facts hκ hκ4.le (hN n) P B hB, hI]
    with ω hLC hU hν hzm hinf
  intro u hu
  refine ⟨fun s hs t ht hst => ?_, ?_, ?_⟩
  · -- monotone
    have hs' : (0 : ℝ) ≤ s := hs
    have ht' : (0 : ℝ) ≤ t := ht
    obtain ⟨n, hn⟩ := exists_nat_ge (u + t)
    obtain ⟨-, -, hanti, -⟩ := hzm n
    show (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).1 ≤
      (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) t).1
    rw [hLC n u s hu hs' (by linarith), hLC n u t hu ht' (by linarith)]
    exact measure_mono (Ioo_subset_Ioo_right (hanti.antitoneOn ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith)))
  · -- tends to `0`
    obtain ⟨n, hn⟩ := exists_nat_ge (u + 1)
    obtain ⟨-, -, hanti, hzc, -⟩ := hzm n
    set N : ℝ := (n : ℝ) + 1 with hNdef
    set z := zeroMinus (Vr κ N B ω) with hz
    set ν := qBoundaryMeasure (Real.sqrt κ) (h0f κ N B X ω) with hνdef
    set a := z (N - u) with ha
    have hg : Tendsto (fun x => ν (Ioo a x)) (𝓝[>] a) (𝓝 0) := by
      have h := tendsto_measure_biInter_gt (μ := ν) (s := fun x => Ioo a x) (a := a)
        (fun r _ => measurableSet_Ioo.nullMeasurableSet)
        (fun i j _ hij => Ioo_subset_Ioo_right hij)
        ⟨a + 1, by linarith, ((measure_mono Ioo_subset_Icc_self).trans_lt
          ((hν n).2.2 a (a + 1))).ne⟩
      have e : (⋂ r > a, Ioo a r) = ∅ := by
        ext x
        simp only [mem_iInter, mem_Ioo, mem_empty_iff_false, iff_false]
        push Not
        by_cases hx : a < x
        · exact ⟨x, hx, fun _ => le_rfl⟩
        · exact ⟨a + 1, by linarith, fun h => absurd h hx⟩
      rw [e, measure_empty] at h
      exact h
    have hmap : Tendsto (fun s : ℝ => z (N - u - s)) (𝓝[>] 0) (𝓝[>] a) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc : ContinuousWithinAt z (Icc 0 N) (N - u) := hzc (N - u) ⟨by linarith, by linarith⟩
        have h1 : Tendsto (fun s : ℝ => N - u - s) (𝓝[>] 0) (𝓝[Icc 0 N] (N - u)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
          · have : Tendsto (fun s : ℝ => N - u - s) (𝓝 0) (𝓝 (N - u - 0)) :=
              (continuous_const.sub continuous_id).tendsto 0
            rw [sub_zero] at this
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
            exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
        exact hc.tendsto.comp h1
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
        exact hanti ⟨by linarith [hs.2], by linarith [hs.1]⟩ ⟨by linarith, by linarith⟩
          (by linarith [hs.1])
    refine (hg.comp hmap).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact (hLC n u s hu hs.1.le (by linarith [hs.2])).symm
  · -- unbounded
    by_contra hne
    have hS := lt_top_iff_ne_top.2 hne
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge u
    have hLu : (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) u).1 < ⊤ := by
      rw [(hU n₀ u ⟨hu, by linarith⟩).1]
      exact (measure_mono Ioo_subset_Icc_self).trans_lt ((hν n₀).2.2 _ _)
    have hle : ⨆ t ∈ Ici (0 : ℝ), (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) t).1 ≤
        (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) u).1 + ⨆ t ∈ Ici (0 : ℝ),
          (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) t).1 := by
      refine iSup₂_le fun t ht => ?_
      have ht' : (0 : ℝ) ≤ t := ht
      obtain ⟨n, hn⟩ := exists_nat_ge (u + t)
      obtain ⟨-, -, hanti, -⟩ := hzm n
      rw [(hU n t ⟨ht', by linarith⟩).1]
      refine (measure_Ioo_le_split
        (b := zeroMinus (Vr κ ((n : ℝ) + 1) B ω) ((n : ℝ) + 1 - u))
        (d := zeroMinus (Vr κ ((n : ℝ) + 1) B ω) ((n : ℝ) + 1 - u - t))
        (hanti.antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith))
        ((hν n).1 _)).trans ?_
      rw [← (hU n u ⟨hu, by linarith⟩).1, ← hLC n u t hu ht' (by linarith)]
      exact add_le_add le_rfl (le_iSup₂ (f := fun t (_ : t ∈ Ici (0 : ℝ)) =>
        (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) t).1) t ht)
    rw [hinf] at hle
    exact absurd hle (not_le.2 (ENNReal.add_lt_top.2 ⟨hLu, hS⟩))

/-- **`FlowGoodArcStmt` from the open-arc length infinity** (copy of `E6.flowGoodStmt_of`). -/
theorem flowGoodArcStmt_of_lenInf (hI : CfgLenInfArcStmt) {κ T ℓ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hℓ : 0 < ℓ) {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) : FlowGoodArcStmt κ T ℓ P B X := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  filter_upwards [zipLenInputsArc_holds (T := T) hκ hκ4 hB hX hind,
    ae_flowLenArc hκ hκ4 hB hX hind (hI κ hκ hκ4 P B X hB hX hind),
    Thm18Asm.g4ShiftAliveStmt_holds κ hκ hκ4 P B hB, RegUnif.ae_drive_good hB κ,
    RegUnif.ae_forall_isRegularSample (κ := κ) (γ := Real.sqrt κ) hB hX hind,
    B3d.ZipLen.yExactAllStmt_holds κ hκ hκ4 P B X hB hX hind,
    B3d.ZipLen.yFlowRC3Stmt_holds κ hκ hκ4 P B X hB hX hind,
    B3d.ZipLen.yFlowContStmt_holds κ hκ hκ4 P B X hB hX hind]
    with ω hZ hLω hAω hdr hRg he hrc hcont
  intro u k hu huT
  obtain ⟨ha, hb, hside, hgood, hfield⟩ := hZ u k hu huT
  obtain ⟨hm, h0, hi⟩ := hLω u hu
  have hEq : ∀ t, unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t =
      F2.unzY κ (X ω) (drive κ B ω) t := fun t => B3d.ZipLen.unzippedField_cfg_eq κ t (X ω) _
  simp_rw [← hEq] at he hrc hcont
  have hregY := fun s (hs : 0 ≤ s) => isRegularSample_unzippedField_canon_pt
    (γ := Real.sqrt κ) hdr.1 hdr.2 (fun t ht => (hRg t ht).1) he hrc hcont hu k ha hs
  refine hitScaleGoodArc_canon hγ hℓ ?_ ?_ (Thm18Asm.zipCapDown_snd_max _ u _)
    (fun x hx S hS => hAω u hu x hx S hS) ha hb hside hgood hfield hregY hm h0 hi
  · exact (hdr.1.comp (continuous_const.add (continuous_id.max continuous_const))).sub
      continuous_const
  · show drive κ B ω (u + max 0 0) - drive κ B ω u = 0
    simp

/-- **`FlowGoodArcAllStmt` from `CfgLenInfArcStmt`.** -/
theorem flowGoodArcAll_of_lenInf (hI : CfgLenInfArcStmt) : FlowGoodArcAllStmt :=
  fun _ _ _ _ _ _ _ _ hκ hκ4 _ hB hX hind _ hℓ =>
    flowGoodArcStmt_of_lenInf hI hκ hκ4 hℓ hB hX hind

/-- **`E6PalmRegArcStmt` from `CfgLenInfArcStmt`** (no tip core). -/
theorem e6PalmRegArc_of_lenInf (hI : CfgLenInfArcStmt) : E6PalmRegArcStmt :=
  e6PalmRegArc_of_flow (flowGoodArcAll_of_lenInf hI)

end LocLen
end QuantumZipper
