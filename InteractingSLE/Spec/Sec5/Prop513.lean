/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TimeDensityHalfBall
import InteractingSLE.Spec.Sec5.Prop59Ext
import InteractingSLE.Spec.Sec5.LightCone
import InteractingSLE.Spec.Restart.ClockMeasCap
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Sec7.Lemma71Capacity

/-!
# Proposition 5.13 from the extreme-angle light cone, Lemma 5.7 and (5.8)

Packet PROVE-PROP513. Specification §5.2, Proposition 5.13 and its proof (`source/spec/p145-192.md` L91–L140,
pp. 149–151): "Almost surely, `η'` is determined by `h`."

PROVE-SEC5-C's `prop513_path_of_lightConeIdentity` derived the proposition from the light-cone identity together
with the time density (5.7) and a capacity functional. Here the last two are discharged:

* the capacity functional is the frozen-σ-algebra-measurable `WholeField.hcapHit`, which reads `2t` off every prefix
  of a generating trace (`hcapHit_image_Icc_of_isGeneratingTrace`; "Filling a compact set and taking its
  half-plane capacity are measurable operations", "`hcap(K_t) = 2t`");
* the time density (5.7) is `ae_dense_traceFirstVisit` (PROVE-PROP513, `TimeDensity.lean`), from Lemma 5.7's
  containment, Corollary 5.12's spatial density and (5.8).

The light-cone identity `L_z = η'([0, T_z])` at a root `z ∈ Γ` splits into the inclusion `L_z ⊆ η'([0, T_z])`, which
is Lemma 5.7's reverse chronological order for the descendants (`closure_subset_image_traceFirstVisit`), and the
reverse inclusion, which is the extreme-angle Proposition 5.9 at the root `z` (`lightCone_eq_of_reverseOrder`).

## Main results

* `hcapHit_image_Icc_of_isGeneratingTrace`: `hcapHit(η([0, t])) = 2t` for a generating trace on `[0, ∞)`.
* `lightCone_eq_of_reverseOrder`: `L_z = η'([0, T_z])` from Lemma 5.7's order and Proposition 5.9's reverse
  inclusion.
* **`prop513_path_of_lightCone`** (conditional helper, distinct name; it replaces no source theorem): Proposition 5.13
  (the whole counterflow path is almost surely equal to a path whose evaluations are `𝒢`-measurable, `𝒢 = σ(h)`)
  from:
  - the field determination of the countable family `Γ = {z n}` and of the cones `L n` (Lemma 5.6;
    `measurable_closure_iUnion_image`);
  - the counterflow trace `γ` in the capacity chart (a generating trace of its continuous driver on `[0, ∞)`);
  - Lemma 5.7: every `z n` is on the trace;
  - the extreme-angle light-cone identity at the roots, `L n = γ([0, T_{z n}])` (Proposition 5.9 and Lemma 5.7);
  - Corollary 5.12 (extreme angles): `Γ` is dense in the trace range;
  - (5.8) at the positive rational windows.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

open QuantumZipper

/-- **The measurable capacity reads `2t` off every prefix of a generating trace** on `[0, ∞)`. -/
theorem hcapHit_image_Icc_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (hw : Continuous w)
    (hw0 : w 0 = 0) (hη : IsGeneratingTrace w ⊤ η) (t : ℝ≥0) :
    WholeField.hcapHit (η '' Icc 0 t) = 2 * (t : ℝ≥0∞) := by
  have hηc := continuous_of_isGeneratingTrace_top hη
  have h0 : (η 0).im ≤ 0 := by rw [hη.1]; simp
  rw [Restart.hcapHit_image_eq hηc.continuousOn h0,
    ← Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hη ENNReal.coe_lt_top,
    Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq (W := fun s : ℝ => w s.toNNReal) (hw.comp continuous_real_toNNReal)
      (by simp [hw0]) t.coe_nonneg rfl,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]

/-- **The light-cone identity at a root** (Proposition 5.9, extreme-angle version, with Lemma 5.7's first visit):
if `L = closure S`, every point of `S` is visited strictly before the first visit of `z` (Lemma 5.7: the counterflow
hits the descendants of the prefix ending at `z` in reverse chronological order), and `γ([0, T_z]) ⊆ L`
(Proposition 5.9's reverse inclusion at the root `z`), then `L = γ([0, T_z])`. -/
theorem lightCone_eq_of_reverseOrder {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {z : ℂ} (hz : ∃ t, γ t = z)
    {S L : Set ℂ} (hL : L = closure S) (hS : ∀ p ∈ S, ∃ v, γ v = p ∧ ∀ w ≤ v, γ w ≠ z)
    (hrev : γ '' Icc 0 (traceFirstVisit γ z) ⊆ L) :
    L = γ '' Icc 0 (traceFirstVisit γ z) :=
  le_antisymm (hL ▸ closure_subset_image_traceFirstVisit hγ hz hS) hrev

/-- **Proposition 5.13 from the extreme-angle light cone** (conditional helper; proof of Proposition 5.13,
pp. 149–151). Let `γ ω` be the counterflow trace in the capacity chart, a generating trace on `[0, ∞)` of its
continuous driver `w ω` (`w ω 0 = 0`); let `z n` (the countable family `Γ` of terminal points of the allowed
extreme-angle prefixes) and `L n` (their descendant cones) be `𝒢`-measurable, resp. measurable for the hitting
σ-algebra. Assume, almost surely:
* (Lemma 5.7) every `z n` is visited by `γ`;
* (Proposition 5.9, extreme angles, at the roots `z n`) `L n = γ([0, T_{z n}])`;
* (Corollary 5.12, extreme angles) the points `z n` are dense in the range of `γ`;
* ((5.8)) at every positive rational window, the restarted hull contains a half-ball.

Then there is a path-valued map `Γ'` whose evaluations are `𝒢`-measurable and which almost surely equals `γ`
("This determines `η'(t)` measurably from `h`; doing so at all positive rational `t` determines the entire continuous
path"). -/
theorem prop513_path_of_lightCone {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒢 : MeasurableSpace Ω}
    {w : Ω → ℝ≥0 → ℝ} {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ} {L : ℕ → Ω → Set ℂ}
    (hz : ∀ n, Measurable[𝒢] (z n)) (hL : ∀ n, @Measurable Ω (Set ℂ) 𝒢 hittingSigma (L n))
    (htr : ∀ᵐ ω ∂P, Continuous (w ω) ∧ w ω 0 = 0 ∧ IsGeneratingTrace (w ω) ⊤ (γ ω))
    (hzγ : ∀ᵐ ω ∂P, ∀ n, ∃ t, γ ω t = z n ω)
    (hcone : ∀ᵐ ω ∂P, ∀ n, L n ω = γ ω '' Icc 0 (traceFirstVisit (γ ω) (z n ω)))
    (hspat : ∀ᵐ ω ∂P, range (γ ω) ⊆ closure (range fun n => z n ω))
    (hb : ∀ r δ : ℚ, 0 < r → 0 < δ → ∀ᵐ ω ∂P, HasFutureHalfBall (w ω) (r : ℝ).toNNReal (δ : ℝ).toNNReal) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  have hdense := @ae_dense_traceFirstVisit Ω mΩ P w γ ℕ z htr hzγ hspat hb
  refine @prop513_path_of_lightConeIdentity Ω mΩ P 𝒢 γ z L WholeField.hcapHit WholeField.measurable_hcapHit hz hL
    ?_ ?_ ?_ ?_
  · filter_upwards [htr] with ω ⟨hw, hw0, hη⟩
    exact hcapHit_image_Icc_of_isGeneratingTrace hw hw0 hη
  · filter_upwards [htr] with ω ⟨_, _, hη⟩
    exact continuous_of_isGeneratingTrace_top hη
  · filter_upwards [htr, hzγ, hcone] with ω ⟨_, _, hη⟩ hzω hcω n
    exact ⟨_, hcω n, (apply_traceFirstVisit (continuous_of_isGeneratingTrace_top hη) (hzω n)).symm⟩
  · filter_upwards [hcone, hdense] with ω hcω hdω t ht ε hε
    obtain ⟨n, hn⟩ := hdω t (by exact_mod_cast ht) ε hε
    exact ⟨n, _, hcω n, hn⟩

/-- **Proposition 5.13 from the extreme-angle light cone, with (5.8) proved** (conditional helper; distinct name).
The counterflow driver `W` is an integrated `SLE_κ(ρ)` evolution with `κ > 4` (the counterflow parameter
`κ' = 16/κ`), almost surely of infinite lifetime, whose force points are almost surely strictly separated from the
driver at every fixed positive time ("At time `r` the original force points of the present non-boundary-intersecting
counterflow are almost surely separated from its driver"). Then (5.8) holds at every positive rational window
(`IsIntegratedSLEEvolution.ae_hasFutureHalfBall`), and the remaining inputs are those of
`prop513_path_of_lightCone`: the field determination of `Γ` and of the cones, the generating trace, Lemma 5.7's
containment, the light-cone identity at the roots (Proposition 5.9) and Corollary 5.12's spatial density. -/
theorem prop513_path_of_lightCone_of_evolution {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ : 4 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hsep : ∀ r : ℝ≥0, 0 < r → ∀ᵐ ω ∂P, (∀ i, VL i r ω < W r ω) ∧ ∀ j, W r ω < VR j r ω)
    {𝒢 : MeasurableSpace Ω} {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ} {L : ℕ → Ω → Set ℂ}
    (hz : ∀ n, Measurable[𝒢] (z n)) (hL : ∀ n, @Measurable Ω (Set ℂ) 𝒢 hittingSigma (L n))
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (hzγ : ∀ᵐ ω ∂P, ∀ n, ∃ t, γ ω t = z n ω)
    (hcone : ∀ᵐ ω ∂P, ∀ n, L n ω = γ ω '' Icc 0 (traceFirstVisit (γ ω) (z n ω)))
    (hspat : ∀ᵐ ω ∂P, range (γ ω) ⊆ closure (range fun n => z n ω)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  have hpath := hE.2.2.2.2
  have htr' : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [hpath, hζ, htr] with ω hp hζω hη
    refine ⟨continuousOn_univ.1 ?_, hp.1, hη⟩
    have := hp.2.2.2.1
    rw [hζω] at this
    simpa using this
  refine @prop513_path_of_lightCone Ω mΩ P 𝒢 (fun ω t => W t ω) γ z L hz hL htr' hzγ hcone hspat ?_
  intro r δ hr hδ
  have hr' : (0 : ℝ≥0) < (r : ℝ).toNNReal := Real.toNNReal_pos.2 (by exact_mod_cast hr)
  filter_upwards [IsIntegratedSLEEvolution.ae_hasFutureHalfBall hκ hE (r : ℝ).toNNReal (δ : ℝ).toNNReal
    (Real.toNNReal_pos.2 (by exact_mod_cast hδ)), hsep _ hr', hζ, htr'] with ω hω hsω hζω htω
  exact hω (by rw [hζω]; exact ENNReal.coe_lt_top) hsω.1 hsω.2 _ htω.1 fun _ _ => rfl

/-- **Proposition 5.13 from the tips of the alternating construction** (conditional helper; distinct name). As
`prop513_path_of_lightCone_of_evolution`, with the light-cone identity and the spatial density replaced by their
per-time cores:
* `L n ω = closure ({z n ω} ∪ S n ω)`, `S n ω` the post-`σ` portions of the descendants of the prefix ending at
  `z n ω` ("include the root `z` itself");
* (Lemma 5.7) every point of `S n ω` is visited strictly before the first visit of `z n ω` (reverse chronological
  order), and every `z n ω` is visited;
* (Proposition 5.9, extreme angles, at the root `z n`) for every rational `q ≥ 0`, almost surely, if `q < T_{z n}`
  the tip `γ(q)` lies in `L n` (the conclusion of the alternating construction at the deterministic time `q`);
* (Corollary 5.12, extreme angles: Proposition 5.9 at the root `0`) for every rational `q ≥ 0`, almost surely the tip
  `γ(q)` lies in the closure of `Γ`. -/
theorem prop513_path_of_tips_of_evolution {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ : 4 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hsep : ∀ r : ℝ≥0, 0 < r → ∀ᵐ ω ∂P, (∀ i, VL i r ω < W r ω) ∧ ∀ j, W r ω < VR j r ω)
    {𝒢 : MeasurableSpace Ω} {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ} {S L : ℕ → Ω → Set ℂ}
    (hz : ∀ n, Measurable[𝒢] (z n)) (hL : ∀ n, @Measurable Ω (Set ℂ) 𝒢 hittingSigma (L n))
    (hLS : ∀ n ω, L n ω = closure (insert (z n ω) (S n ω)))
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (hzγ : ∀ᵐ ω ∂P, ∀ n, ∃ t, γ ω t = z n ω)
    (hord : ∀ᵐ ω ∂P, ∀ n, ∀ p ∈ S n ω, ∃ v, γ ω v = p ∧ ∀ w ≤ v, γ ω w ≠ z n ω)
    (htip : ∀ n, ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P,
      (q : ℝ) < traceFirstVisit (γ ω) (z n ω) → γ ω (q : ℝ).toNNReal ∈ L n ω)
    (htip0 : ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P, γ ω (q : ℝ).toNNReal ∈ closure (range fun n => z n ω)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  have htip' : ∀ᵐ ω ∂P, ∀ n, ∀ q : ℚ, 0 ≤ q →
      (q : ℝ) < traceFirstVisit (γ ω) (z n ω) → γ ω (q : ℝ).toNNReal ∈ L n ω := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun q => ?_
    by_cases hq : 0 ≤ q
    · filter_upwards [htip n q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  have htip0' : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ q → γ ω (q : ℝ).toNNReal ∈ closure (range fun n => z n ω) := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 ≤ q
    · filter_upwards [htip0 q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  refine @prop513_path_of_lightCone_of_evolution κ nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hκ hE hζ hsep 𝒢
    γ z L hz hL htr hzγ ?_ ?_
  · filter_upwards [htr, hzγ, hord, htip'] with ω hη hzω hoω htω n
    exact lightCone_eq_image_Icc (continuous_of_isGeneratingTrace_top hη) (hzω n) (hLS n ω) (hoω n)
      (htω n)
  · filter_upwards [htr, htip0'] with ω hη htω
    exact range_subset_of_rat (continuous_of_isGeneratingTrace_top hη) isClosed_closure htω

/-- **Proposition 5.13 from the tips of the alternating construction, for a counterflow avoiding the boundary**
(conditional helper; distinct name). As `prop513_path_of_tips_of_evolution`, with the separation of the force points
at fixed times derived from the non-boundary-intersecting property of the counterflow: almost surely its trace is in
the open half-plane at every positive time (`sep_of_trace_mem_H`). -/
theorem prop513_path_of_tips {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ : 4 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {𝒢 : MeasurableSpace Ω} {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ} {S L : ℕ → Ω → Set ℂ}
    (hz : ∀ n, Measurable[𝒢] (z n)) (hL : ∀ n, @Measurable Ω (Set ℂ) 𝒢 hittingSigma (L n))
    (hLS : ∀ n ω, L n ω = closure (insert (z n ω) (S n ω)))
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (htrH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H)
    (hzγ : ∀ᵐ ω ∂P, ∀ n, ∃ t, γ ω t = z n ω)
    (hord : ∀ᵐ ω ∂P, ∀ n, ∀ p ∈ S n ω, ∃ v, γ ω v = p ∧ ∀ w ≤ v, γ ω w ≠ z n ω)
    (htip : ∀ n, ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P,
      (q : ℝ) < traceFirstVisit (γ ω) (z n ω) → γ ω (q : ℝ).toNNReal ∈ L n ω)
    (htip0 : ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P, γ ω (q : ℝ).toNNReal ∈ closure (range fun n => z n ω)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  refine @prop513_path_of_tips_of_evolution κ nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hκ hE hζ ?_ 𝒢 γ z S L
    hz hL hLS htr hzγ hord htip htip0
  intro r hr
  filter_upwards [hE.2.2.2.2, hζ, htr, htrH] with ω hp hζω hη hH
  have hc : Continuous fun t => W t ω := by
    have := hp.2.2.2.1
    rw [hζω] at this
    exact continuousOn_univ.1 (by simpa using this)
  exact sep_of_trace_mem_H hp hc hη (by rw [hζω]; exact ENNReal.coe_lt_top) (hH r hr)

end Sec5

end InteractingSLE
