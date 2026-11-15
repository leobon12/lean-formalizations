/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Trace

/-!
# The trace with marks at the seed, for `κ ≤ 4` (Remark 2.3; Astra §3 "Simplicity", L1296–L1307)

Packet PROVE-ZHAN-B2. Astra, *Formalization proofs and dependency audit* (`source/external/AstraIG1/
ig1_formalization_proofs.txt`, ruling R35), L1296–L1307: "With seed forces, restart at positive rational times `ε`,
whose gaps are positive by the noncollision proof. The localized relative ordinary traces lie in `ℍ` at every strictly
positive elapsed time. Their pullbacks by `g_ε⁻¹` therefore use only its analytic interior map … They define one
continuous trace on `(0, ∞)`. It is simple … Finally, shrinking initial hulls make the tips converge to zero."

This is the argument of Wang–Wu's Lemma 4.12 (`WangWu.IsMarkedChain.ae_simple_trace`, written for `κ = 4`), which
uses `κ = 4` only through ordinary `SLE₄`. Here it is run for every `0 < κ ≤ 4` and every ordered force word with
admissible side partial sums (marks at `0⁻`, `0⁺` allowed):

1. Aux. lemma 6 (`Sec4.aux6Statement`): `ζ = ∞` and every force point is strictly separated from the driver at every
   positive time;
2. after each positive rational time, bounded-drift Girsanov on compact gap-localizations
   (`Dimension.exists_brownian_localization`) and ordinary `SLE_κ`, `κ ≤ 4`, being a simple radial chain
   (QuantumZipper: `RS.ae_radialGood_drive`, `RS.ae_sleTrace_simple_of_le_four`,
   `RS.ae_fwdHull_eq_sleTrace_image_of_le_four`) make the mapped-out future a simple radial chain;
3. the gluing theorem `WangWu.TraceGlue.exists_isGeneratingTrace_of_shift`.

## Main results

* `Zhan.ae_isSimpleRadialChain_drive`: ordinary `SLE_κ`, `0 < κ ≤ 4`, is a simple radial chain.
* `Zhan.IsIntegratedSLEEvolution.ae_simple_trace` (**Remark 2.3 for `κ ≤ 4`**): almost surely `ζ = ∞`, the marks are
  separated from the driver at positive times, and there is a simple generating trace on `[0, ∞]` lying in `ℍ` at
  positive times, with `K_t = η((0, t])`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Zhan

open QuantumZipper QuantumZipper.RS InteractingSLE.WangWu InteractingSLE.WangWu.TraceGlue

variable {nL nR : ℕ}

/-- **Ordinary `SLE_κ`, `0 < κ ≤ 4`, is a simple radial chain** on the canonical path space (QuantumZipper: radial
limits and continuity, simplicity, and `K_t = γ((0, t])`). -/
theorem ae_isSimpleRadialChain_drive {μ : Measure CPath} [IsProbabilityMeasure μ]
    (hμ : IsBrownianReal canonBM μ) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    ∀ᵐ x ∂μ, Continuous (drive κ canonBM x) ∧ drive κ canonBM x 0 = 0 ∧
      IsSimpleRadialChain (drive κ canonBM x) := by
  filter_upwards [ae_radialGood_drive hμ hκ (by linarith),
    ae_sleTrace_simple_of_le_four hμ hκ hκ4,
    ae_fwdHull_eq_sleTrace_image_of_le_four hμ hκ hκ4] with x hg hs hh
  exact ⟨hg.1, hg.2.1, fun T => ⟨fun u hu => hg.tendsto hu.1, hg.2.2.2.1.mono fun u hu => hu.1,
    fun u hu => hs.2 u hu.1, fun u hu => hh u hu.1⟩⟩

section Evolution

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The localized comparison with ordinary `SLE_κ` after a time `a`** (`κ ≤ 4`): almost surely, if `ζ = ∞` and all
force gaps are `≥ δ` on `[a, a + m]`, the mapped-out future `shiftDrive W a` is a simple radial chain on `[0, m]`. -/
theorem IsIntegratedSLEEvolution.ae_shift_isSimpleRadialChainOn [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hκ4 : κ ≤ 4) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (a : ℝ≥0) (m : ℕ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ s : ℝ≥0, a ≤ s → s ≤ a + m →
        Dimension.GapsGE δ (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) →
      IsSimpleRadialChainOn (shiftDrive (fun r : ℝ => W r.toNNReal ω) a) m := by
  obtain ⟨X, hXm, μ, hμP, hμB, hac, hloc⟩ := Dimension.exists_brownian_localization hκ hE a m hδ
  have hgood := ae_of_ae_map hXm.aemeasurable (hac.ae_le (ae_isSimpleRadialChain_drive hμB hκ hκ4))
  filter_upwards [hgood, hloc, hE.2.2.2.2] with ω ⟨hVc, hV0, hV⟩ hlocω hp hζ hgap
  have hWc := continuous_realDriver_of_eq_top hζ hp.2.2.2.1
  refine (hV m).congr hVc hV0 (continuous_shiftDrive hWc a) (shiftDrive_zero _ _) fun r hr => ?_
  have ht : r.toNNReal ≤ (m : ℝ≥0) := Real.toNNReal_le_iff_le_coe.2 (by exact_mod_cast hr.2)
  have h1 := hlocω r.toNNReal ht (by rw [hζ]; exact ENNReal.coe_lt_top)
    fun s hs1 hs2 => hgap s hs1 (hs2.trans (add_le_add_right ht a))
  show Real.sqrt κ * canonBM r.toNNReal (X ω) = W ((a : ℝ) + r).toNNReal ω - W (a : ℝ).toNNReal ω
  rw [Real.toNNReal_coe, Real.toNNReal_add a.coe_nonneg hr.1, Real.toNNReal_coe, h1]
  rfl

/-- **Positive minimal gap on compact intervals after a positive time** (any `κ`): if the path has infinite lifetime
and every force point is strictly separated from the driver at positive times, then on every `[a, b]`, `a > 0`, all
gaps are `≥ δ` for some `δ > 0`. -/
theorem exists_gapsGE_Icc_of_sep {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b0 : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b0 T) (hT : T = ⊤)
    (hsep : ∀ t : ℝ≥0, 0 < t → (∀ i, vL i t < w t) ∧ ∀ i, w t < vR i t) {a b : ℝ≥0} (ha : 0 < a)
    (hab : a ≤ b) : ∃ δ > 0, ∀ s : ℝ≥0, a ≤ s → s ≤ b → Dimension.GapsGE δ (w s) (fun i => vL i s)
      (fun i => vR i s) := by
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < T} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => by
      show (t : ℝ≥0∞) < T
      rw [hT]; exact ENNReal.coe_lt_top)
  have hw := hcont hp.2.2.2.1
  have hL : ∀ i, ∃ ε > 0, ∀ s ∈ Icc a b, ε ≤ |w s - vL i s| := fun i =>
    exists_pos_le_of_continuous_Icc (hw.sub (hcont (hp.2.2.2.2.1 i))).abs hab fun s hs =>
      abs_pos.2 (sub_ne_zero.2 ((hsep s (ha.trans_le hs.1)).1 i).ne')
  have hR : ∀ i, ∃ ε > 0, ∀ s ∈ Icc a b, ε ≤ |w s - vR i s| := fun i =>
    exists_pos_le_of_continuous_Icc (hw.sub (hcont (hp.2.2.2.2.2.1 i))).abs hab fun s hs =>
      abs_pos.2 (sub_ne_zero.2 ((hsep s (ha.trans_le hs.1)).2 i).ne)
  choose εL hεL hεLle using hL
  choose εR hεR hεRle using hR
  obtain ⟨δL, hδL, hδLle⟩ := exists_pos_le_of_pos εL
  obtain ⟨δR, hδR, hδRle⟩ := exists_pos_le_of_pos εR
  refine ⟨min δL δR, lt_min hδL hδR, fun s hs1 hs2 => ⟨fun i => ?_, fun i => ?_⟩⟩
  · exact (min_le_left _ _).trans ((hδLle i (hεL i)).trans (hεLle i s ⟨hs1, hs2⟩))
  · exact (min_le_right _ _).trans ((hδRle i (hεR i)).trans (hεRle i s ⟨hs1, hs2⟩))

/-- **Remark 2.3 for `κ ≤ 4`: the simple trace with marks at the seed.** For an integrated `SLE_κ(ρ)` evolution,
`0 < κ ≤ 4`, of an ordered force word with admissible side partial sums (marks at `0⁻`, `0⁺` allowed), almost surely:
the lifetime is infinite; every force point is strictly separated from the driver at every positive time; and there
is a generating trace `η` on `[0, ∞]` which is injective, lies in `ℍ` at positive times, and has `K_t = η((0, t])`. -/
theorem IsIntegratedSLEEvolution.ae_simple_trace (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧ Function.Injective η ∧
        (∀ t, 0 < t → η t ∈ H) ∧
        ∀ t : ℝ≥0, fwdHull (fun s : ℝ => W s.toNNReal ω) t = η '' Ioc 0 t := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have h6 := Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE
  have hloc : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ m n : ℕ, ζ ω = ⊤ → (∀ s : ℝ≥0, (q : ℝ).toNNReal ≤ s →
      s ≤ (q : ℝ).toNNReal + m →
        Dimension.GapsGE (1 / ((n : ℝ) + 1)) (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) →
      IsSimpleRadialChainOn (shiftDrive (fun r : ℝ => W r.toNNReal ω) ((q : ℝ).toNNReal : ℝ)) m := by
    rw [ae_all_iff]; intro q
    rw [ae_all_iff]; intro m
    rw [ae_all_iff]; intro n
    exact IsIntegratedSLEEvolution.ae_shift_isSimpleRadialChainOn hκ hκ4 hE _ m (by positivity)
  filter_upwards [h6, hloc, hE.2.2.2.2] with ω ⟨hζ, hsep⟩ hlω hp
  refine ⟨hζ, hsep, ?_⟩
  have hWc := continuous_realDriver_of_eq_top hζ hp.2.2.2.1
  refine exists_isGeneratingTrace_of_shift hWc hp.1 (D := range ((↑) : ℚ → ℝ))
    Rat.denseRange_cast ?_
  rintro _ ⟨q, rfl⟩ hq T
  obtain ⟨m, hm⟩ := exists_nat_ge T
  have ha : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq.le
  have ha0 : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 hq
  obtain ⟨δ, hδ, hgapδ⟩ := exists_gapsGE_Icc_of_sep hp hζ hsep ha0 (le_self_add (b := (m : ℝ≥0)))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have h := hlω q m n hζ fun s h1 h2 =>
    ⟨fun i => hn.le.trans ((hgapδ s h1 h2).1 i), fun i => hn.le.trans ((hgapδ s h1 h2).2 i)⟩
  rw [ha] at h
  exact h.mono hm

end Evolution

end InteractingSLE.Zhan
