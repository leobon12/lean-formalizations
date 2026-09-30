import QuantumZipper.Proofs.Thm18.G2RootXCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 smoothing, `x` side: the gap `ν_h[x, x + κ)` tends to `0` under the rooted measure

Sheffield (arXiv:1012.4797, proof of Proposition 5.5, p. 66) uses that "the amount by which
resampling `h₀'` [the field near `x`] changes `ν_h[a, x]` ... is a quantity that tends to zero in
probability" as `ε̄ → 0`. In our coordinates the length is `L = ν_h[x, 0]`, the cut length is
`ν_h[x + κ, 0]` (`g3CutLen`), and the gap is `L − ν_h[x + κ, 0] = ν_h[x, x + κ)`. This file proves
that the rooted measure `g3RootInt` of `{gap > ρ}` tends to `0` as `κ → 0`
(`g3GapX_small`): `ν_h` has no atoms (`G3Fid.ae_normField_good`), so
`ν_h[x + 1/(n+1), 0] ↑ ν_h(x, 0] = ν_h[x, 0]`, and the rooted measure is a finite measure
(`g3LenRoot_rooted`, `g3Z_pos_lt_top`), so continuity from above applies.

Measurability: `g3CutLen` uses the honest measure `ν_h`, whose measurability in `ω` is not
available; on the window `[−δ, 0]` it agrees a.s. with the measurable `g3ν₁ + g3ν₀`
(`ae_g3Fid_sets`), whose distribution function is jointly measurable
(`measurable_measure_Icc_zero`, by left-continuity through rationals).

Own elementary proofs (AGENT_GUIDE cost rule): continuity of measures and bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-! ## Joint measurability of the distribution function -/

/-- Left-continuity through rationals: `m[a, 0] = ⨅_{q < a, q ∈ ℚ} m[q, 0]`. -/
theorem measure_Icc_zero_eq_iInf_rat {m : Measure ℝ} (hfin : ∀ b, m (Icc b 0) ≠ ⊤) (a : ℝ) :
    m (Icc a 0) = ⨅ q : ℚ, if (q : ℝ) < a then m (Icc (q : ℝ) 0) else ⊤ := by
  refine le_antisymm (le_iInf fun q => ?_) ?_
  · split_ifs with h
    · exact measure_mono (Icc_subset_Icc_left h.le)
    · exact le_top
  · obtain ⟨u, hu_mono, hu, hlim⟩ :=
      Rat.denseRange_cast.exists_seq_strictMono_tendsto (Rat.cast_mono (K := ℝ)) a
    have hanti : Antitone fun n => Icc ((u n : ℝ)) (0 : ℝ) := fun n k hnk =>
      Icc_subset_Icc_left (Rat.cast_mono (hu_mono.monotone hnk))
    have hinter : (⋂ n, Icc ((u n : ℝ)) (0 : ℝ)) = Icc a 0 := by
      ext x
      simp only [mem_iInter, mem_Icc]
      constructor
      · intro h
        exact ⟨le_of_tendsto hlim (Eventually.of_forall fun n => (h n).1), (h 0).2⟩
      · intro h n
        exact ⟨(le_of_lt (hu n)).trans h.1, h.2⟩
    have ht := tendsto_measure_iInter_atTop (μ := m)
      (fun n => measurableSet_Icc.nullMeasurableSet) hanti ⟨0, hfin _⟩
    rw [hinter] at ht
    refine ge_of_tendsto' ht fun n => ?_
    refine (iInf_le _ (u n)).trans ?_
    have hun : ((u n : ℚ) : ℝ) < a := hu n
    rw [if_pos hun]
    rfl

/-- **Joint measurability** of `(ω, a) ↦ μ_ω[a, 0]` for a measurable family of measures that
are finite on the intervals `[b, 0]`. -/
theorem measurable_measure_Icc_zero {α : Type*} {mα : MeasurableSpace α} {μ : α → Measure ℝ}
    (hμ : Measurable μ) (hfin : ∀ ω b, μ ω (Icc b 0) ≠ ⊤) :
    Measurable fun p : α × ℝ => μ p.1 (Icc p.2 0) := by
  have e : (fun p : α × ℝ => μ p.1 (Icc p.2 0)) = fun p =>
      ⨅ q : ℚ, if (q : ℝ) < p.2 then μ p.1 (Icc (q : ℝ) 0) else ⊤ := by
    funext p; exact measure_Icc_zero_eq_iInf_rat (hfin p.1) p.2
  rw [e]
  refine Measurable.iInf fun q => Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt measurable_const measurable_snd
  · exact ((Measure.measurable_coe measurableSet_Icc).comp hμ).comp measurable_fst

theorem measurable_g3sum₁' (γ : ℝ) (i : G3Idx) :
    Measurable fun ω : Ω₀ => g3ν₁ γ i ω + g3ν₀ γ i ω :=
  (measurable_g3sum₁ γ i).mono
    (sup_le (localSigma_le gffBase.gff _ _) (outsideSigma2_le gffBase.gff _ _ _ _)) le_rfl

/-- The **measurable cut length** `(g3ν₁ + g3ν₀)[x + κ, 0]` (a.s. `= g3CutLen` on `[−δ, 0]`). -/
def g3CutLenM (γ : ℝ) (i : G3Idx) (κ : ℝ) (ω : Ω₀) (x : ℝ) : ℝ :=
  ((g3ν₁ γ i ω + g3ν₀ γ i ω) (Icc (x + κ) 0)).toReal

theorem measurable_g3sum_Icc (γ : ℝ) (i : G3Idx) :
    Measurable fun p : Ω₀ × ℝ => (g3ν₁ γ i p.1 + g3ν₀ γ i p.1) (Icc p.2 0) :=
  measurable_measure_Icc_zero (μ := fun ω => g3ν₁ γ i ω + g3ν₀ γ i ω)
    (measurable_g3sum₁' γ i) (g3ν_Icc_ne_top γ i)

theorem measurable_g3CutLenM (γ : ℝ) (i : G3Idx) (κ : ℝ) :
    Measurable fun q : Ω₀ × ℝ × ℝ => g3CutLenM γ i κ q.1 q.2.2 := by
  have h2 : Measurable fun q : Ω₀ × ℝ × ℝ => ((q.1, q.2.2 + κ) : Ω₀ × ℝ) :=
    measurable_fst.prodMk ((measurable_snd.comp measurable_snd).add_const κ)
  have h3 : Measurable fun q : Ω₀ × ℝ × ℝ =>
      (g3ν₁ γ i q.1 + g3ν₀ γ i q.1) (Icc (q.2.2 + κ) 0) :=
    Measurable.comp (g := fun p : Ω₀ × ℝ => (g3ν₁ γ i p.1 + g3ν₀ γ i p.1) (Icc p.2 0))
      (f := fun q : Ω₀ × ℝ × ℝ => ((q.1, q.2.2 + κ) : Ω₀ × ℝ)) (measurable_g3sum_Icc γ i) h2
  exact h3.ennreal_toReal

theorem g3CutLenM_mono (γ : ℝ) (i : G3Idx) (ω : Ω₀) (x : ℝ) {κ κ' : ℝ} (h : κ ≤ κ') :
    g3CutLenM γ i κ' ω x ≤ g3CutLenM γ i κ ω x :=
  ENNReal.toReal_mono (g3ν_Icc_ne_top γ i _ _) (measure_mono (Icc_subset_Icc_left (by linarith)))

/-! ## Honest versus measurable cut length under the rooted measure -/

theorem ae_g3CutLen_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ᵐ ω ∂gffBase.P, ∀ x ∈ Icc (-i.δ) 0, g3CutLen γ κ ω x = g3CutLenM γ i κ ω x := by
  filter_upwards [ae_g3Fid_sets hγ hγ2] with ω hω x hx
  unfold g3CutLen g3CutLenM
  have h1 : Icc (x + κ) 0 ⊆ Icc (-i.δ) 0 :=
    Icc_subset_Icc_left (show -i.δ ≤ x + κ by linarith [hx.1])
  have h2 : Icc (-i.δ) 0 ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4) :=
    Icc_neg_subset_win i (show i.δ < i.δ + i.η / 4 by linarith [i.hη])
  rw [(hω i).1 _ (h1.trans h2)]

theorem g3RootInt_congr {γ : ℝ} {i : G3Idx} {F F' : Ω₀ × ℝ × ℝ → ℝ≥0∞}
    (h : ∀ᵐ ω ∂gffBase.P, ∀ x ∈ Icc (-i.δ) 0, ∀ ℓ : ℝ, F (ω, ℓ, x) = F' (ω, ℓ, x)) :
    g3RootInt γ i F = g3RootInt γ i F' := by
  unfold g3RootInt
  refine lintegral_congr_ae ?_
  filter_upwards [h] with ω hω
  exact setLIntegral_congr_fun measurableSet_Icc fun x hx => hω x hx _

/-- Any rooted event read through the cut length may use the measurable version. -/
theorem g3RootInt_cut_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {κ : ℝ} (hκ : 0 ≤ κ)
    (P : Ω₀ × ℝ × ℝ → ℝ → Prop) :
    g3RootInt γ i ({q | P q (g3CutLen γ κ q.1 q.2.2)}.indicator 1) =
      g3RootInt γ i ({q | P q (g3CutLenM γ i κ q.1 q.2.2)}.indicator 1) := by
  refine g3RootInt_congr ?_
  filter_upwards [ae_g3CutLen_eq hγ hγ2 i hκ] with ω hω x hx ℓ
  have e : ((ω, ℓ, x) ∈ {q : Ω₀ × ℝ × ℝ | P q (g3CutLen γ κ q.1 q.2.2)}) ↔
      ((ω, ℓ, x) ∈ {q : Ω₀ × ℝ × ℝ | P q (g3CutLenM γ i κ q.1 q.2.2)}) := by
    show P (ω, ℓ, x) (g3CutLen γ κ ω x) ↔ P (ω, ℓ, x) (g3CutLenM γ i κ ω x)
    rw [hω x hx]
  by_cases h : (ω, ℓ, x) ∈ {q : Ω₀ × ℝ × ℝ | P q (g3CutLen γ κ q.1 q.2.2)}
  · rw [indicator_of_mem h, indicator_of_mem (e.1 h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (e.2 h'))]

theorem g3RootInt_eq_of_δ {γ : ℝ} {i i' : G3Idx} (h : i.δ = i'.δ) (F : Ω₀ × ℝ × ℝ → ℝ≥0∞) :
    g3RootInt γ i F = g3RootInt γ i' F := by
  unfold g3RootInt; rw [h]

/-! ## The gap tends to zero -/

/-- The rooted event `{ν_h[x, 0] − ν_h[x + κ, 0] > ρ}` (gap larger than `ρ`). -/
def g3GapEvX (γ κ ρ : ℝ) : Set (Ω₀ × ℝ × ℝ) := {q | ρ < q.2.1 - g3CutLen γ κ q.1 q.2.2}

/-- Its measurable version. -/
def g3GapEvXM (γ : ℝ) (i : G3Idx) (κ ρ : ℝ) : Set (Ω₀ × ℝ × ℝ) :=
  {q | ρ < q.2.1 - g3CutLenM γ i κ q.1 q.2.2}

theorem measurableSet_g3GapEvXM (γ : ℝ) (i : G3Idx) (κ ρ : ℝ) :
    MeasurableSet (g3GapEvXM γ i κ ρ) :=
  measurableSet_lt measurable_const
    ((measurable_fst.comp measurable_snd).sub (measurable_g3CutLenM γ i κ))

theorem g3GapEvXM_mono (γ : ℝ) (i : G3Idx) (ρ : ℝ) {κ κ' : ℝ} (h : κ ≤ κ') :
    g3GapEvXM γ i κ ρ ⊆ g3GapEvXM γ i κ' ρ := fun q hq => by
  simp only [g3GapEvXM, mem_setOf_eq] at hq ⊢
  linarith [g3CutLenM_mono γ i q.1 q.2.2 h]

/-- Pointwise: along `κ = 1/(n+1)` the gap tends to `ν_h{x} = 0`. -/
theorem not_mem_iInter_g3GapEvXM {γ : ℝ} (i : G3Idx) {ω : Ω₀} {ρ : ℝ} (hρ : 0 < ρ)
    (hwin : ∀ s ⊆ Icc (-i.δ) 0, (g3ν₁ γ i ω + g3ν₀ γ i ω) s = g3Hν γ ω s)
    (hat : ∀ t, g3Hν γ ω {t} = 0) {x : ℝ} (hx : x ∈ Icc (-i.δ) 0) :
    (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∉ ⋂ n : ℕ, g3GapEvXM γ i (1 / ((n : ℝ) + 1)) ρ := by
  intro hmem
  simp only [mem_iInter, g3GapEvXM, mem_setOf_eq] at hmem
  set ν := g3Hν γ ω
  have hsub : ∀ n : ℕ, Icc (x + 1 / ((n : ℝ) + 1)) 0 ⊆ Icc (-i.δ) 0 := fun n =>
    Icc_subset_Icc_left (by have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
                            linarith [hx.1])
  have hcut : ∀ n : ℕ, g3CutLenM γ i (1 / ((n : ℝ) + 1)) ω x =
      (ν (Icc (x + 1 / ((n : ℝ) + 1)) 0)).toReal := fun n => by
    unfold g3CutLenM; rw [hwin _ (hsub n)]
  have hfin : ν (Icc x 0) ≠ ⊤ := by
    rw [← hwin _ (Icc_subset_Icc_left hx.1)]; exact g3ν_Icc_ne_top γ i ω x
  have hmono : Monotone fun n : ℕ => Icc (x + 1 / ((n : ℝ) + 1)) (0 : ℝ) := by
    intro n k hnk
    have hnk' : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnk
    exact Icc_subset_Icc_left (by linarith [one_div_le_one_div_of_le (by positivity) hnk'])
  have hU : (⋃ n : ℕ, Icc (x + 1 / ((n : ℝ) + 1)) (0 : ℝ)) = Ioc x 0 := by
    ext y
    simp only [mem_iUnion, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨n, h1, h2⟩
      exact ⟨by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h1)
      exact ⟨n, by linarith, h2⟩
  have hIoc : ν (Ioc x 0) = ν (Icc x 0) := by
    refine le_antisymm (measure_mono Ioc_subset_Icc_self) ?_
    calc ν (Icc x 0) ≤ ν ({x} ∪ Ioc x 0) := measure_mono fun y hy => by
          rcases eq_or_lt_of_le hy.1 with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨h, hy.2⟩
      _ ≤ ν {x} + ν (Ioc x 0) := measure_union_le _ _
      _ = ν (Ioc x 0) := by rw [hat, zero_add]
  have ht := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hU, hIoc] at ht
  have ht' : Tendsto (fun n : ℕ => (ν (Icc x 0)).toReal -
      (ν (Icc (x + 1 / ((n : ℝ) + 1)) 0)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal hfin).comp ht
    have h2 := (tendsto_const_nhds (x := (ν (Icc x 0)).toReal)).sub this
    rw [sub_self] at h2
    exact h2
  obtain ⟨n, hn⟩ := (ht'.eventually (gt_mem_nhds hρ)).exists
  have := hmem n
  rw [hcut n] at this
  linarith

/-- **The gap tends to zero in rooted measure** (Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 66: the change of `ν_h[a, x]` under resampling near `x` tends to `0` in
probability). -/
theorem g3GapX_small {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {ρ : ℝ} (hρ : 0 < ρ)
    {ε : ℝ} (hε : 0 < ε) : ∃ ε₀ > 0, ∀ κ ∈ Ioo 0 ε₀,
      (g3RootInt γ i ((g3GapEvX γ κ ρ).indicator 1)).toReal ≤ ε := by
  have hZ := g3Z_pos_lt_top hγ hγ2 i
  have := isFiniteMeasure_g3LenRoot γ i hZ.2
  set f : Ω₀ × ℝ → Ω₀ × ℝ × ℝ := fun p => (p.1, p.2, g3X γ i p) with hf
  have hfm : Measurable f := measurable_fst.prodMk (measurable_snd.prodMk (measurable_g3X' γ i))
  set T : ℕ → Set (Ω₀ × ℝ × ℝ) := fun n => g3GapEvXM γ i (1 / ((n : ℝ) + 1)) ρ with hT
  have hTm : ∀ n, MeasurableSet (T n) := fun n => measurableSet_g3GapEvXM γ i _ ρ
  have hanti : Antitone fun n => f ⁻¹' T n := by
    intro n k hnk
    have hnk' : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnk
    exact preimage_mono (g3GapEvXM_mono γ i ρ (one_div_le_one_div_of_le (by positivity) hnk'))
  have ht := tendsto_measure_iInter_atTop (μ := g3LenRoot γ i)
    (fun n => (hfm (hTm n)).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hzero : g3LenRoot γ i (⋂ n, f ⁻¹' T n) = 0 := by
    rw [← preimage_iInter, show f ⁻¹' (⋂ n, T n) = {p | (p.1, p.2, g3X γ i p) ∈ ⋂ n, T n}
      from rfl, g3LenRoot_rooted hγ hγ2 i (MeasurableSet.iInter hTm)]
    unfold g3RootInt
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_g3Fid_sets hγ hγ2, G3Fid.ae_normField_good gffBase.gff hγ hγ2]
      with ω hω hgood
    have hW : Icc (-i.δ) 0 ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4) :=
      Icc_neg_subset_win i (show i.δ < i.δ + i.η / 4 by linarith [i.hη])
    have hwin : ∀ s ⊆ Icc (-i.δ) 0, (g3ν₁ γ i ω + g3ν₀ γ i ω) s = g3Hν γ ω s := fun s hs =>
      (hω i).1 s (hs.trans hW)
    refine (setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Icc
      fun x hx => ?_).trans lintegral_zero
    exact indicator_of_notMem (not_mem_iInter_g3GapEvXM i hρ hwin hgood.2.2 hx) _
  rw [hzero] at ht
  obtain ⟨N, hN⟩ := (ht.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  have hN' : g3LenRoot γ i (f ⁻¹' T N) < ENNReal.ofReal ε := hN
  refine ⟨1 / ((N : ℝ) + 1), by positivity, fun κ hκ => ?_⟩
  rw [show g3GapEvX γ κ ρ = {q | ρ < q.2.1 - g3CutLen γ κ q.1 q.2.2} from rfl,
    g3RootInt_cut_eq hγ hγ2 i hκ.1.le (fun q c => ρ < q.2.1 - c)]
  change (g3RootInt γ i ((g3GapEvXM γ i κ ρ).indicator 1)).toReal ≤ ε
  rw [← g3LenRoot_rooted hγ hγ2 i (measurableSet_g3GapEvXM γ i κ ρ)]
  refine ENNReal.toReal_le_of_le_ofReal hε.le (le_of_lt (lt_of_le_of_lt ?_ hN'))
  exact measure_mono (preimage_mono (g3GapEvXM_mono γ i ρ hκ.2.le))

end Thm18Asm
end QuantumZipper
