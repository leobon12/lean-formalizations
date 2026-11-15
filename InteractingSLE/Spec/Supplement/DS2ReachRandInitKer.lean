/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachRandInit
import InteractingSLE.Spec.Supplement.DS2ReachRandInitRestart
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# DS2 with converging random initial states, III: lower semicontinuity of the restart kernel

Packet PROVE-T14-DS3. The input of the Fatou lemma (`DSReach.lintegral_le_liminf_of_tendsto`) in step (iii) of the
proof of Lemma DS3: the restart kernel `RandInit.reachKer` of a reach event is lower semicontinuous jointly in the
weights, the absolute shift and the relative start, along separated DS1 words with a cross gap bounded below
(`reachKer_le_liminf`). The pointwise input is DS2 itself (`DSReach.ds2Reach_general`), applied to evolutions from the
converging starts (Theorem 2.2's existence, `exists_isIntegratedSLEEvolution_assembled`); the shift is absorbed by
shrinking the open sets (`shrink`), which costs nothing in the limit by continuity of the paths and compactness.

* `shiftSet w U`: states `p` with `p + (w, w, w) ∈ U`; `shrink ε U`: points with a ball of radius `> ε` in `U`;
* `reachKer_shift`: `reachKer … O Bf w s = reachKer … (shiftSet w O) (shiftSet w Bf) 0 s`;
* `measure_reachEvent_le_reachKer`, `measure_reachEvent_eq_reachKer`: for every evolution from a separated start `s`,
  `P(reach of the w-shifted state) ≤ reachKer w s`, with equality when the start is not a threshold state;
* **`reachKer_le_liminf`**: `reachKer ρ₀ w s ≤ liminf_k reachKer ρ_{m_k} w_k s_k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace RandInit

open Sec2 Sec2.Assembly DS2 DSReach

variable {nL nR : ℕ}

/-! ### Shifted and shrunk sets -/

/-- The constant shift `(w, w, w)` of a state. -/
def cst (w : ℝ) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := (w, fun _ => w, fun _ => w)

/-- States whose `w`-shift lies in `U`. -/
def shiftSet (w : ℝ) (U : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  (· + cst w) ⁻¹' U

theorem isOpen_shiftSet (w : ℝ) {U : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hU : IsOpen U) :
    IsOpen (shiftSet w U) :=
  hU.preimage (continuous_id.add continuous_const)

/-- Points with a ball of radius `> ε` inside `U`. -/
def shrink (ε : ℝ) (U : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  {p | ∃ δ > ε, Metric.ball p δ ⊆ U}

theorem isOpen_shrink (ε : ℝ) (U : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) : IsOpen (shrink ε U) := by
  refine Metric.isOpen_iff.2 fun p ⟨δ, hδ, hp⟩ => ⟨(δ - ε) / 2, by linarith, fun p' hp' => ?_⟩
  refine ⟨(δ + ε) / 2, by linarith, fun q hq => hp ?_⟩
  rw [Metric.mem_ball] at hp' hq ⊢
  linarith [dist_triangle q p' p]

theorem shrink_subset (ε : ℝ) (hε : 0 ≤ ε) (U : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) : shrink ε U ⊆ U :=
  fun _ ⟨_, hδ, hp⟩ => hp (Metric.mem_ball_self (by linarith))

theorem shrink_anti {ε ε' : ℝ} (h : ε' ≤ ε) (U : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) :
    shrink ε U ⊆ shrink ε' U :=
  fun _ ⟨δ, hδ, hp⟩ => ⟨δ, lt_of_le_of_lt h hδ, hp⟩

/-- A shrunk set survives a shift by at most `ε`. -/
theorem mem_shiftSet_of_shrink {ε w w' : ℝ} (hww : |w' - w| ≤ ε) {U : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))}
    {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (hp : p ∈ shiftSet w (shrink ε U)) : p ∈ shiftSet w' U := by
  obtain ⟨δ, hδ, hball⟩ := hp
  refine hball (lt_of_le_of_lt ?_ hδ)
  have e : p + cst w' - (p + cst w) = cst (nL := nL) (nR := nR) (w' - w) := by
    simp only [cst, add_sub_add_left_eq_sub]; ext <;> simp
  rw [dist_eq_norm, e]
  simp only [cst, Prod.norm_def]
  refine max_le (by rwa [Real.norm_eq_abs]) (max_le ?_ ?_)
  · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _ |>.trans hww)).2 fun _ => by
      rwa [Real.norm_eq_abs]
  · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _ |>.trans hww)).2 fun _ => by
      rwa [Real.norm_eq_abs]

/-- A point of an open set, and a compact set inside an open set, are in every small shrinking. -/
theorem exists_mem_shrink_of_isCompact {K U : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) : ∃ ε > 0, K ⊆ shrink ε U := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ / 2, by positivity, fun p hp => ⟨δ, by linarith, fun q hq => hsub ?_⟩⟩
  exact Metric.mem_thickening_iff.2 ⟨p, hp, by rw [Metric.mem_ball] at hq; exact hq⟩

theorem infDist_preimage_add {E : Type*} [NormedAddCommGroup E] (c p : E) (S : Set E) :
    Metric.infDist p ((· + c) ⁻¹' S) = Metric.infDist (p + c) S := by
  have h : (· + c) ⁻¹' S = (fun x => x + -c) '' S := by
    ext x; simp only [mem_preimage, mem_image]
    exact ⟨fun h => ⟨x + c, h, by abel⟩, fun ⟨y, hy, hyx⟩ => by rw [← hyx]; simpa using hy⟩
  rw [h, ← Metric.infDist_image (Φ := fun x => x + -c) (isometry_add_right (-c)) (x := p + c)]
  simp

theorem inBuffer_of_add {mL mR : ℕ} {R g w : ℝ} {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)}
    (h : InBuffer mL mR R g (p + cst w)) : InBuffer mL mR (R + |w|) g p := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := h
  simp only [cst, Prod.fst_add, Prod.snd_add, Pi.add_apply] at h1 h2 h3 h4 h5
  refine ⟨⟨?_, fun i => ?_, fun j => ?_⟩, fun j hj => ?_, fun i hi => ?_⟩
  · calc |p.1| = |(p.1 + w) - w| := by ring_nf
      _ ≤ |p.1 + w| + |w| := abs_sub _ _
      _ < R + |w| := by linarith
  · calc |p.2.1 i| = |(p.2.1 i + w) - w| := by ring_nf
      _ ≤ |p.2.1 i + w| + |w| := abs_sub _ _
      _ < R + |w| := by linarith [h2 i]
  · calc |p.2.2 j| = |(p.2.2 j + w) - w| := by ring_nf
      _ ≤ |p.2.2 j + w| + |w| := abs_sub _ _
      _ < R + |w| := by linarith [h3 j]
  · have := h4 j hj; linarith
  · have := h5 i hi; linarith

/-! ### The kernel and the reach probabilities of evolutions -/

theorem codeState_eq_add (w : ℝ) (y : XCode nL nR) (t : ℝ≥0) :
    codeState w y t = codeState 0 y t + cst w := by
  simp only [codeState, cst, zero_add, Prod.mk_add_mk]
  refine Prod.ext (add_comm _ _) (Prod.ext (funext fun i => ?_) (funext fun j => ?_)) <;>
    simp only [Pi.add_apply] <;> ring

theorem codeReach_shift (T' : ℝ≥0) (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (w : ℝ)
    (y : XCode nL nR) :
    CodeReach T' (shiftSet w O) (shiftSet w Bf) 0 y ↔ CodeReach T' O Bf w y := by
  have h1 : ∀ t, codeState 0 y t ∈ shiftSet w O ↔ codeState w y t ∈ O := fun t => by
    rw [codeState_eq_add w y t]; rfl
  have h2 : ∀ t, Metric.infDist (codeState 0 y t) (shiftSet w Bf)ᶜ =
      Metric.infDist (codeState w y t) Bfᶜ := fun t => by
    rw [codeState_eq_add w y t, shiftSet, ← preimage_compl, infDist_preimage_add]
  simp only [CodeReach, h1, h2]

theorem reachKer_shift (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (T' : ℝ≥0)
    (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (w : ℝ) (s : (Fin nL → ℝ) × (Fin nR → ℝ)) :
    reachKer a ρL ρR T' O Bf w s = reachKer a ρL ρR T' (shiftSet w O) (shiftSet w Bf) 0 s := by
  unfold reachKer
  congr 1
  ext b
  simp only [mem_ofPred_eq, reachSetF, mem_image]
  constructor
  · rintro ⟨⟨w', y⟩, ⟨hy, hr⟩, hb⟩
    simp only [Prod.mk.injEq] at hb
    obtain ⟨⟨rfl, hs⟩, hb⟩ := hb
    exact ⟨(0, y), ⟨hy, (codeReach_shift T' O Bf w' y).2 hr⟩, by simp only [hs, hb]⟩
  · rintro ⟨⟨w', y⟩, ⟨hy, hr⟩, hb⟩
    simp only [Prod.mk.injEq] at hb
    obtain ⟨⟨rfl, hs⟩, hb⟩ := hb
    exact ⟨(w, y), ⟨hy, (codeReach_shift T' O Bf w y).1 hr⟩, by simp only [hs, hb]⟩

/-- For every evolution from a separated start, the reach probability of the `w`-shifted state is at most the
kernel (with equality when the start is not a threshold state). -/
theorem measure_reachEvent_mul_eq_reachKer {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (hsep : ∀ i j, xL i < xR j)
    (T' : ℝ≥0) {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hO : IsOpen O) (hBf : IsOpen Bf)
    (hBfc : Bfᶜ.Nonempty) (w : ℝ) :
    P (reachEvent T' (shiftSet w O) (shiftSet w Bf) W VL VR ζ) =
      reachKer a ρL ρR T' O Bf w (xL, xR) * P {ω | 0 < ζ ω} := by
  have hT : IsStoppingTime 𝓕 fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const 𝓕 _
  set A : Set Ω := {ω | 0 < ζ ω} with hAdef
  have hA0 : MeasurableSet[𝓕 0] A := by
    have := hE.2.1 0 univ MeasurableSet.univ
    simp only [mem_univ, and_true, ENNReal.coe_zero] at this
    exact this
  have hA : MeasurableSet[hT.measurableSpace] A := by
    refine (hT.measurableSet A).2 ⟨le_iSup (fun t => (𝓕 t : MeasurableSpace Ω)) 0 _ hA0, fun t => ?_⟩
    have : {ω : Ω | ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ t} = univ := by
      ext ω; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact_mod_cast zero_le
    rw [this, inter_univ]
    exact 𝓕.mono zero_le _ hA0
  have hBfc' : (shiftSet w Bf)ᶜ.Nonempty := by
    obtain ⟨q, hq⟩ := hBfc
    exact ⟨q - cst w, by simpa [shiftSet] using hq⟩
  have key := measure_restart_reach ha hE hT hA (fun ω hω => ⟨by rw [ENNReal.coe_zero]; exact hω, Or.inr hsep⟩) T'
    (isOpen_shiftSet w hO) (isOpen_shiftSet w hBf) hBfc'
  have hset : A ∩ restartReach (fun _ => (0 : ℝ≥0)) T' (shiftSet w O) (shiftSet w Bf) W VL VR ζ =
      reachEvent T' (shiftSet w O) (shiftSet w Bf) W VL VR ζ := by
    ext ω
    simp only [restartReach, reachEvent, mem_inter_iff, mem_ofPred_eq, zero_add, ENNReal.coe_zero,
      tsub_zero, hAdef]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨t, h1, h2, h3, h4⟩; exact ⟨lt_of_le_of_lt zero_le h2, t, h1, h2, h3, h4⟩
  rw [hset] at key
  rw [key, reachKer_shift a ρL ρR T' O Bf w, ← setLIntegral_const]
  refine setLIntegral_congr_fun_ae (𝓕.le 0 _ hA0) ?_
  filter_upwards [hE.2.2.2.2] with ω hp _
  simp only [hp.1, hp.2.1, hp.2.2.1, sub_zero]

theorem sep_of_ds1Word {mL mR : ℕ} {Rw ε a : ℝ} (hnL : 0 < nL) (hnR : 0 < nR) (ha : 0 < a)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR) (hcr : a ≤ xR ⟨0, hnR⟩ - xL ⟨0, hnL⟩) : ∀ i j, xL i < xR j := by
  intro i j
  have h1 : xL i ≤ xL ⟨0, hnL⟩ := hw.1.1 (Fin.le_def.2 (Nat.zero_le _))
  have h2 : xR ⟨0, hnR⟩ ≤ xR j := hw.1.2.2.1 (Fin.le_def.2 (Nat.zero_le _))
  linarith

theorem compl_nonempty_of_inBuffer {mL mR : ℕ} {R g : ℝ} {Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))}
    (hBR : ∀ p ∈ Bf, InBuffer mL mR R g p) : Bfᶜ.Nonempty := by
  refine ⟨(|R| + 1, 0, 0), fun h => ?_⟩
  have := (hBR _ h).1.1
  simp only at this
  rw [abs_of_pos (by positivity)] at this
  linarith [le_abs_self R]

/-- **Lower semicontinuity of the restart kernel** in the weights, the shift and the start (DS2). -/
theorem reachKer_le_liminf {κ : ℝ} (hκ : 0 < κ) (hnL : 0 < nL) (hnR : 0 < nR) {mL mR : ℕ}
    {Rw ε a g R : ℝ} (hε : 0 < ε) (ha : 0 < a) (hg : 0 < g) {T' : ℝ≥0}
    {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hO : IsOpen O) (hBo : IsOpen Bf)
    (hBR : ∀ p ∈ Bf, InBuffer mL mR R g p) {ρL : ℕ → Fin nL → ℝ} {ρR : ℕ → Fin nR → ℝ}
    {ρL₀ : Fin nL → ℝ} {ρR₀ : Fin nR → ℝ} (hρL : Tendsto ρL atTop (𝓝 ρL₀)) (hρR : Tendsto ρR atTop (𝓝 ρR₀))
    {w : ℝ} {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hs : IsDS1Word mL mR Rw ε s.1 s.2 ρL₀ ρR₀)
    (hsa : a ≤ s.2 ⟨0, hnR⟩ - s.1 ⟨0, hnL⟩) (hthr : ¬ ForceWord.ThresholdCondition ρL₀ ρR₀ 0 s.1 s.2)
    {mk : ℕ → ℕ} (hmk : Tendsto mk atTop atTop) {wk : ℕ → ℝ} {sk : ℕ → (Fin nL → ℝ) × (Fin nR → ℝ)}
    (hwk : Tendsto wk atTop (𝓝 w)) (hsk : Tendsto sk atTop (𝓝 s))
    (hskw : ∀ k, IsDS1Word mL mR Rw ε (sk k).1 (sk k).2 (ρL (mk k)) (ρR (mk k)))
    (hska : ∀ k, a ≤ (sk k).2 ⟨0, hnR⟩ - (sk k).1 ⟨0, hnL⟩) :
    reachKer κ ρL₀ ρR₀ T' O Bf w s ≤
      liminf (fun k => reachKer κ (ρL (mk k)) (ρR (mk k)) T' O Bf (wk k) (sk k)) atTop := by
  classical
  have hBfc := compl_nonempty_of_inBuffer hBR
  -- evolutions from the starts
  have hFk : ∀ k, IsOrderedForceWord (sk k).1 (sk k).2 := fun k => (hskw k).1
  choose Ωk mΩk Pk hPk 𝓕k Wk VLk VRk Bk ζk hEk using fun k =>
    exists_isIntegratedSLEEvolution_assembled hκ (hFk k) (ρL := ρL (mk k)) (ρR := ρR (mk k))
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hs.1 (ρL := ρL₀) (ρR := ρR₀)
  have hsepk : ∀ k, ∀ i j, (sk k).1 i < (sk k).2 j := fun k => sep_of_ds1Word hnL hnR ha (hskw k) (hska k)
  have hsep₀ : ∀ i j, s.1 i < s.2 j := sep_of_ds1Word hnL hnR ha hs hsa
  -- the kernel bounds the reach probabilities
  have hle : ∀ k, Pk k (reachEvent T' (shiftSet (wk k) O) (shiftSet (wk k) Bf) (Wk k) (VLk k) (VRk k) (ζk k)) ≤
      reachKer κ (ρL (mk k)) (ρR (mk k)) T' O Bf (wk k) (sk k) := fun k => by
    rw [measure_reachEvent_mul_eq_reachKer hκ (hEk k) (hsepk k) T' hO hBo hBfc (wk k)]
    exact mul_le_of_le_one_right zero_le prob_le_one
  have hP₀1 : P₀ {ω | 0 < ζ₀ ω} = 1 := by
    rw [← prob_compl_eq_zero_iff (measurableSet_lt measurable_const (Sec2.Assembly.measurable_lifetime hE₀.2.1))]
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hE₀.2.2.2.2)
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] at hω
    exact fun hp => hthr (hp.isForcePath.threshold_of_eq_zero hω)
  have heq₀ : P₀ (reachEvent T' (shiftSet w O) (shiftSet w Bf) W₀ VL₀ VR₀ ζ₀) =
      reachKer κ ρL₀ ρR₀ T' O Bf w s := by
    rw [measure_reachEvent_mul_eq_reachKer hκ hE₀ hsep₀ T' hO hBo hBfc w, hP₀1, mul_one]
  -- the shrunk sets
  set Oj : ℕ → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) := fun j => shiftSet w (shrink (1 / ((j : ℝ) + 1)) O)
  set Bj : ℕ → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) := fun j => shiftSet w (shrink (1 / ((j : ℝ) + 1)) Bf)
  have hDS2 : ∀ j, P₀ (reachEvent T' (Oj j) (Bj j) W₀ VL₀ VR₀ ζ₀) ≤
      liminf (fun k => Pk k (reachEvent T' (Oj j) (Bj j) (Wk k) (VLk k) (VRk k) (ζk k))) atTop := fun j =>
    ds2Reach_general.{0} κ hκ hnL hnR mL mR Rw ε a g hε ha hg (fun k => (sk k).1) (fun k => (sk k).2)
      (fun k => ρL (mk k)) (fun k => ρR (mk k)) s.1 s.2 ρL₀ ρR₀ hskw hs hska hsa
      ((continuous_fst.tendsto _).comp hsk) ((continuous_snd.tendsto _).comp hsk) (hρL.comp hmk)
      (hρR.comp hmk) Ωk Pk 𝓕k Wk VLk VRk Bk ζk hEk P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hE₀ T' (R + |w|) (Oj j) (Bj j)
      (isOpen_shiftSet w (isOpen_shrink _ _)) (isOpen_shiftSet w (isOpen_shrink _ _))
      (fun p hp => inBuffer_of_add (hBR _ (shrink_subset _ (by positivity) _ hp)))
  have hk : ∀ j, liminf (fun k => Pk k (reachEvent T' (Oj j) (Bj j) (Wk k) (VLk k) (VRk k) (ζk k))) atTop ≤
      liminf (fun k => reachKer κ (ρL (mk k)) (ρR (mk k)) T' O Bf (wk k) (sk k)) atTop := fun j => by
    have hev : ∀ᶠ k in atTop, |wk k - w| ≤ 1 / ((j : ℝ) + 1) := by
      have := (hwk.sub_const w).abs
      rw [sub_self, abs_zero] at this
      exact this.eventually (ge_mem_nhds (by positivity))
    refine liminf_le_liminf (hev.mono fun k hkw => ?_) (by isBoundedDefault) (by isBoundedDefault)
    refine le_trans (measure_mono ?_) (hle k)
    exact reachEvent_mono le_rfl (fun p hp => mem_shiftSet_of_shrink hkw hp)
      (fun p hp => mem_shiftSet_of_shrink hkw hp) _ _ _ _
  -- the reach event is the increasing union of the shrunk ones, almost surely
  have hmono : Monotone fun j => reachEvent T' (Oj j) (Bj j) W₀ VL₀ VR₀ ζ₀ := by
    intro j j' hjj'
    have h : 1 / ((j' : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjj' 1)
    exact reachEvent_mono le_rfl (fun p hp => shrink_anti h O hp) (fun p hp => shrink_anti h Bf hp) _ _ _ _
  have hcover : reachEvent T' (shiftSet w O) (shiftSet w Bf) W₀ VL₀ VR₀ ζ₀ ≤ᵐ[P₀]
      ⋃ j, reachEvent T' (Oj j) (Bj j) W₀ VL₀ VR₀ ζ₀ := by
    filter_upwards [hE₀.2.2.2.2] with ω hp hω
    obtain ⟨t, htT, htζ, htO, htB⟩ := hω
    have hfp := hp.isForcePath
    have hcont : ContinuousOn (fun u => Coupling.stateAt W₀ VL₀ VR₀ u ω + cst w) (Icc 0 t) := by
      refine ContinuousOn.add ?_ continuousOn_const
      refine ((hfp.continuousOn_w.prodMk ((continuousOn_pi.2 fun i => hfp.continuousOn_vL i).prodMk
        (continuousOn_pi.2 fun j => hfp.continuousOn_vR j)))).mono fun u hu => ?_
      exact lt_of_le_of_lt (by exact_mod_cast hu.2) htζ
    obtain ⟨ε₁, hε₁, hK⟩ := exists_mem_shrink_of_isCompact (isCompact_Icc.image_of_continuousOn hcont)
      hBo (by rintro _ ⟨u, hu, rfl⟩; exact htB u hu.2)
    obtain ⟨ε₂, hε₂, hK₂⟩ := exists_mem_shrink_of_isCompact (isCompact_singleton
      (x := Coupling.stateAt W₀ VL₀ VR₀ t ω + cst w)) hO (by rw [singleton_subset_iff]; exact htO)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (lt_min hε₁ hε₂)
    refine mem_iUnion.2 ⟨j, t, htT, htζ, ?_, fun u hu => ?_⟩
    · exact shrink_anti (hj.le.trans (min_le_right _ _)) O (hK₂ rfl)
    · exact shrink_anti (hj.le.trans (min_le_left _ _)) Bf (hK ⟨u, ⟨zero_le, hu⟩, rfl⟩)
  calc reachKer κ ρL₀ ρR₀ T' O Bf w s = P₀ (reachEvent T' (shiftSet w O) (shiftSet w Bf) W₀ VL₀ VR₀ ζ₀) :=
        heq₀.symm
    _ ≤ P₀ (⋃ j, reachEvent T' (Oj j) (Bj j) W₀ VL₀ VR₀ ζ₀) := measure_mono_ae hcover
    _ = ⨆ j, P₀ (reachEvent T' (Oj j) (Bj j) W₀ VL₀ VR₀ ζ₀) := hmono.measure_iUnion
    _ ≤ _ := iSup_le fun j => (hDS2 j).trans (hk j)

end RandInit

end Supp12

end InteractingSLE
