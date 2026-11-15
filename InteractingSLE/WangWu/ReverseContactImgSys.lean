/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelAdaptCont
import InteractingSLE.Spec.Sec7.PhaseSelFullLevy
import InteractingSLE.Spec.Sec7.PhaseSelFullPhase

/-!
# The image driver of the contact step, part 1: killed force-point words and their continued systems

Packet PROVE-WW-B16, step B5 of PROVE-WW-B15's plan. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`,
ruling R31), Lemma 2.11 (text dump L477–L560: "Stop before the first collision whose total weight on either side is at
most −2. Then … W satisfies (1.1) for a Brownian motion in the given filtration, up to the stopped lifetime"), used in
the proof of Proposition 4.18 (L1627–L1629: "Its conditional harmonic means and conformal-radius brackets, just
identified, satisfy Lemma 2.11").

The image driver of the contact step is only defined before its terminal capacity time `T` (a *killed* driver). This
file sets up the killed form of Lemma 2.11's hypotheses and the device that makes the landed (global) tools apply:

* `IsKilledWord W VL VR T`: driver and force coordinates with the deterministic properties of geometric force images
  **before** `T` (continuity, force paths, order, monotonicity, index order, merging), strictly separated from the
  driver at positive times before `T` (the forward line is simple and lies in `ℍ`);
* `sysW W σ`, `sysVL W VL σ`, `sysVR W VR σ` (**the continued system at `σ < T`**): the driver frozen after `σ` and the
  force points continued by the Loewner flow of the frozen driver (`Sec7.PhaseSelAdapt.contW`, `contV`); they are
  global continuous force paths (`IsKilledWord.isForcePath_sysVL`, …), adapted when `σ` is a stopping time, strictly
  separated at positive times (`IsKilledWord.sysVL_lt_sysW`, `sysW_lt_sysVR`), and agree with the killed coordinates up
  to `σ`;
* `IsKilledWord.continuousWithinAt_coupProc`: the explicit coupling means of the killed word are right-continuous before
  `min (swallowTime z) T`;
* **`IsKilledWord.isLocalMartingaleBefore_sys`**: if the coupling means of the killed word are local martingales before
  `min (swallowTime z) T`, those of the continued system at a stopping time `σ < T` are local martingales before
  `min (swallowTime z) σ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

namespace ImgDrv

open MartChar Sec7.PhaseSelAdapt Sec7.PhaseSelFull

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

/-! ### Killed words -/

/-- **A killed force-point word**: a driver `W` and force coordinates `VL`, `VR` with the deterministic properties of
geometric force images before the time `T` (`W₀ = 0`, continuity, force paths, order around the driver, monotonicity,
index order, merging), strictly separated from the driver at every positive time before `T`. -/
structure IsKilledWord (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) : Prop where
  w_zero : ∀ ω, W 0 ω = 0
  contW : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω}
  ordL : ∀ ω (t : ℝ≥0) i, (t : WithTop ℝ≥0) < T ω → VL i t ω ≤ W t ω
  ordR : ∀ ω (t : ℝ≥0) j, (t : WithTop ℝ≥0) < T ω → W t ω ≤ VR j t ω
  pathL : ∀ ω i, IsForcePathBefore (W · ω) (VL i · ω) (T ω)
  pathR : ∀ ω j, IsForcePathBefore (W · ω) (VR j · ω) (T ω)
  antiL : ∀ ω i, AntitoneOn (VL i · ω) {t | (t : WithTop ℝ≥0) < T ω}
  monoR : ∀ ω j, MonotoneOn (VR j · ω) {t | (t : WithTop ℝ≥0) < T ω}
  idxL : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Antitone fun i => VL i t ω
  idxR : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Monotone fun j => VR j t ω
  mergeL : ∀ ω i j (s t : ℝ≥0), s ≤ t → (t : WithTop ℝ≥0) < T ω → VL i s ω = VL j s ω →
    VL i t ω = VL j t ω
  mergeR : ∀ ω i j (s t : ℝ≥0), s ≤ t → (t : WithTop ℝ≥0) < T ω → VR i s ω = VR j s ω →
    VR i t ω = VR j t ω
  sepL : ∀ ω (t : ℝ≥0), 0 < t → (t : WithTop ℝ≥0) < T ω → ∀ i, VL i t ω < W t ω
  sepR : ∀ ω (t : ℝ≥0), 0 < t → (t : WithTop ℝ≥0) < T ω → ∀ j, W t ω < VR j t ω

/-! ### The continued system -/

/-- The driver frozen after the random time `σ`. -/
def sysW (W : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ := fun t ω => contW (W · ω) (σ ω) t

/-- The left force points continued after `σ` by the Loewner flow of the frozen driver. -/
def sysVL (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) : Fin nL → ℝ≥0 → Ω → ℝ :=
  fun i t ω => contV (-1) (W · ω) (VL i · ω) (σ ω) t

/-- The right force points continued after `σ` by the Loewner flow of the frozen driver. -/
def sysVR (W : ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) : Fin nR → ℝ≥0 → Ω → ℝ :=
  fun j t ω => contV 1 (W · ω) (VR j · ω) (σ ω) t

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}
  {σ : Ω → ℝ≥0}

theorem lt_of_le_sys (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) {ω : Ω} {t : ℝ≥0} (ht : t ≤ σ ω) :
    (t : WithTop ℝ≥0) < T ω :=
  lt_of_le_of_lt (WithTop.coe_le_coe.2 ht) (hσT ω)

theorem Iic_subset_sys (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) (ω : Ω) :
    Iic (σ ω) ⊆ {t : ℝ≥0 | (t : WithTop ℝ≥0) < T ω} := fun _ ht => lt_of_le_sys hσT ht

theorem sysW_of_le {ω : Ω} {t : ℝ≥0} (ht : t ≤ σ ω) : sysW W σ t ω = W t ω := contW_of_le ht

theorem sysW_zero (hW0 : ∀ ω, W 0 ω = 0) (ω : Ω) : sysW W σ 0 ω = 0 := by
  rw [sysW_of_le zero_le, hW0]

/-- The driver paths of the continued system and of the killed word agree up to `σ`. -/
theorem wpath_sys_eq {ω : Ω} {r : ℝ} (hr : r.toNNReal ≤ σ ω) : wpath (sysW W σ) ω r = wpath W ω r :=
  sysW_of_le hr

section Sys

variable (hK : IsKilledWord W VL VR T) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω)
include hK hσT

theorem IsKilledWord.sysVL_of_le {ω : Ω} {t : ℝ≥0} (ht : t ≤ σ ω) (i : Fin nL) :
    sysVL W VL σ i t ω = VL i t ω :=
  contV_left_of_le (hK.ordL ω t i (lt_of_le_sys hσT ht)) ht

theorem IsKilledWord.sysVR_of_le {ω : Ω} {t : ℝ≥0} (ht : t ≤ σ ω) (j : Fin nR) :
    sysVR W VR σ j t ω = VR j t ω :=
  contV_right_of_le (hK.ordR ω t j (lt_of_le_sys hσT ht)) ht

theorem IsKilledWord.continuousOn_Iic (ω : Ω) : ContinuousOn (W · ω) (Iic (σ ω)) :=
  (hK.contW ω).mono (Iic_subset_sys hσT ω)

theorem IsKilledWord.continuousOn_Iic_VL (ω : Ω) (i : Fin nL) : ContinuousOn (VL i · ω) (Iic (σ ω)) :=
  (hK.pathL ω i).1.mono (Iic_subset_sys hσT ω)

theorem IsKilledWord.continuousOn_Iic_VR (ω : Ω) (j : Fin nR) : ContinuousOn (VR j · ω) (Iic (σ ω)) :=
  (hK.pathR ω j).1.mono (Iic_subset_sys hσT ω)

theorem IsKilledWord.continuous_sysW (ω : Ω) : Continuous fun t => sysW W σ t ω :=
  continuous_contW (hK.continuousOn_Iic hσT ω)

theorem IsKilledWord.continuous_sysVL (i : Fin nL) (ω : Ω) : Continuous fun t => sysVL W VL σ i t ω :=
  continuous_contV (-1) (hK.continuousOn_Iic hσT ω) (hK.continuousOn_Iic_VL hσT ω i)

theorem IsKilledWord.continuous_sysVR (j : Fin nR) (ω : Ω) : Continuous fun t => sysVR W VR σ j t ω :=
  continuous_contV 1 (hK.continuousOn_Iic hσT ω) (hK.continuousOn_Iic_VR hσT ω j)

theorem IsKilledWord.isForcePath_sysVL (ω : Ω) (i : Fin nL) :
    IsForcePath (fun t => sysW W σ t ω) (fun t => sysVL W VL σ i t ω) :=
  isForcePath_contV_left (hK.continuousOn_Iic hσT ω) (hK.continuousOn_Iic_VL hσT ω i)
    (fun t ht => hK.ordL ω t i (lt_of_le_sys hσT ht)) ((hK.antiL ω i).mono (Iic_subset_sys hσT ω))
    (fun u hu hus hne => (hK.pathL ω i).2.1 u hu (lt_of_le_sys hσT (Real.toNNReal_le_iff_le_coe.2 hus)) hne)
    (by
      refine measure_mono_null (fun u hu => ?_) (hK.pathL ω i).2.2
      exact ⟨hu.1, lt_of_le_sys hσT (Real.toNNReal_le_iff_le_coe.2 hu.2.1), hu.2.2⟩)

theorem IsKilledWord.isForcePath_sysVR (ω : Ω) (j : Fin nR) :
    IsForcePath (fun t => sysW W σ t ω) (fun t => sysVR W VR σ j t ω) :=
  isForcePath_contV_right (hK.continuousOn_Iic hσT ω) (hK.continuousOn_Iic_VR hσT ω j)
    (fun t ht => hK.ordR ω t j (lt_of_le_sys hσT ht)) ((hK.monoR ω j).mono (Iic_subset_sys hσT ω))
    (fun u hu hus hne => (hK.pathR ω j).2.1 u hu (lt_of_le_sys hσT (Real.toNNReal_le_iff_le_coe.2 hus)) hne)
    (by
      refine measure_mono_null (fun u hu => ?_) (hK.pathR ω j).2.2
      exact ⟨hu.1, lt_of_le_sys hσT (Real.toNNReal_le_iff_le_coe.2 hu.2.1), hu.2.2⟩)

theorem IsKilledWord.antitone_sysVL (ω : Ω) (i : Fin nL) : Antitone fun t => sysVL W VL σ i t ω :=
  antitone_contV_left (fun t ht => hK.ordL ω t i (lt_of_le_sys hσT ht))
    ((hK.antiL ω i).mono (Iic_subset_sys hσT ω))

theorem IsKilledWord.monotone_sysVR (ω : Ω) (j : Fin nR) : Monotone fun t => sysVR W VR σ j t ω :=
  monotone_contV_right (fun t ht => hK.ordR ω t j (lt_of_le_sys hσT ht))
    ((hK.monoR ω j).mono (Iic_subset_sys hσT ω))

theorem IsKilledWord.antitone_idx_sysVL (ω : Ω) (t : ℝ≥0) : Antitone fun i => sysVL W VL σ i t ω :=
  fun i _ hij => contV_left_le (fun t ht => hK.ordL ω t i (lt_of_le_sys hσT ht))
    (fun t ht => hK.idxL ω t (lt_of_le_sys hσT ht) hij) t

theorem IsKilledWord.monotone_idx_sysVR (ω : Ω) (t : ℝ≥0) : Monotone fun j => sysVR W VR σ j t ω :=
  fun j _ hij => contV_right_le (fun t ht => hK.ordR ω t j (lt_of_le_sys hσT ht))
    (fun t ht => hK.idxR ω t (lt_of_le_sys hσT ht) hij) t

theorem IsKilledWord.merge_sysVL (ω : Ω) (i j : Fin nL) (s t : ℝ≥0) (hst : s ≤ t)
    (h : sysVL W VL σ i s ω = sysVL W VL σ j s ω) : sysVL W VL σ i t ω = sysVL W VL σ j t ω :=
  contV_eq_of_eq (Or.inr rfl)
    (by have := hK.ordL ω (σ ω) i (hσT ω); linarith) (by have := hK.ordL ω (σ ω) j (hσT ω); linarith)
    (fun t ht => ⟨hK.sysVL_of_le hσT ht i, hK.sysVL_of_le hσT ht j⟩)
    (fun t₀ t h1 h2 h3 => hK.mergeL ω i j t₀ t h1 (lt_of_le_sys hσT h2) h3) hst h

theorem IsKilledWord.merge_sysVR (ω : Ω) (i j : Fin nR) (s t : ℝ≥0) (hst : s ≤ t)
    (h : sysVR W VR σ i s ω = sysVR W VR σ j s ω) : sysVR W VR σ i t ω = sysVR W VR σ j t ω :=
  contV_eq_of_eq (Or.inl rfl)
    (by have := hK.ordR ω (σ ω) i (hσT ω); linarith) (by have := hK.ordR ω (σ ω) j (hσT ω); linarith)
    (fun t ht => ⟨hK.sysVR_of_le hσT ht i, hK.sysVR_of_le hσT ht j⟩)
    (fun t₀ t h1 h2 h3 => hK.mergeR ω i j t₀ t h1 (lt_of_le_sys hσT h2) h3) hst h

/-- The continued left force points stay strictly left of the frozen driver at positive times. -/
theorem IsKilledWord.sysVL_lt_sysW (ω : Ω) {t : ℝ≥0} (ht : 0 < t) (i : Fin nL) :
    sysVL W VL σ i t ω < sysW W σ t ω := by
  rcases le_or_gt t (σ ω) with hts | hts
  · rw [hK.sysVL_of_le hσT hts i, sysW_of_le hts]
    exact hK.sepL ω t ht (lt_of_le_sys hσT hts) i
  · exact lt_of_le_of_ne (contV_left_le_contW t) (contV_ne_contW (by norm_num) hts)

/-- The continued right force points stay strictly right of the frozen driver at positive times. -/
theorem IsKilledWord.sysW_lt_sysVR (ω : Ω) {t : ℝ≥0} (ht : 0 < t) (j : Fin nR) :
    sysW W σ t ω < sysVR W VR σ j t ω := by
  rcases le_or_gt t (σ ω) with hts | hts
  · rw [hK.sysVR_of_le hσT hts j, sysW_of_le hts]
    exact hK.sepR ω t ht (lt_of_le_sys hσT hts) j
  · exact lt_of_le_of_ne (contW_le_contV_right t) (contV_ne_contW one_ne_zero hts).symm

theorem IsKilledWord.sep_sys (ω : Ω) (t : ℝ≥0) (ht : 0 < t) (i : Fin nL) (j : Fin nR)
    (hL : sysVL W VL σ i t ω = sysW W σ t ω) : sysVR W VR σ j t ω ≠ sysW W σ t ω :=
  absurd hL (hK.sysVL_lt_sysW hσT ω ht i).ne

theorem IsKilledWord.stronglyAdapted_sysW {𝓖 : Filtration ℝ≥0 mΩ}
    (hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0)) (hWa : StronglyAdapted 𝓖 W) :
    StronglyAdapted 𝓖 (sysW W σ) :=
  stronglyAdapted_contW hσ hWa (hK.continuousOn_Iic hσT)

theorem IsKilledWord.stronglyAdapted_sysVL {𝓖 : Filtration ℝ≥0 mΩ}
    (hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0)) (hWa : StronglyAdapted 𝓖 W)
    (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i)) (i : Fin nL) : StronglyAdapted 𝓖 (sysVL W VL σ i) :=
  stronglyAdapted_contV (-1) hσ hWa (hVLa i) (hK.continuousOn_Iic hσT) fun ω => hK.continuousOn_Iic_VL hσT ω i

theorem IsKilledWord.stronglyAdapted_sysVR {𝓖 : Filtration ℝ≥0 mΩ}
    (hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0)) (hWa : StronglyAdapted 𝓖 W)
    (hVRa : ∀ j, StronglyAdapted 𝓖 (VR j)) (j : Fin nR) : StronglyAdapted 𝓖 (sysVR W VR σ j) :=
  stronglyAdapted_contV 1 hσ hWa (hVRa j) (hK.continuousOn_Iic hσT) fun ω => hK.continuousOn_Iic_VR hσT ω j


/-- The coupling means of the continued system and of the killed word agree up to `σ`. -/
theorem IsKilledWord.coupProc_sys_eq {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {z : ℂ} {ω : Ω} {t : ℝ≥0}
    (ht : t ≤ σ ω) :
    coupProc κ ρL ρR (sysW W σ) (sysVL W VL σ) (sysVR W VR σ) z t ω = coupProc κ ρL ρR W VL VR z t ω := by
  have h1 : (fun i => sysVL W VL σ i t ω) = fun i => VL i t ω := funext fun i => hK.sysVL_of_le hσT ht i
  have h2 : (fun j => sysVR W VR σ j t ω) = fun j => VR j t ω := funext fun j => hK.sysVR_of_le hσT ht j
  simp only [coupProc]
  rw [sysW_of_le ht, h1, h2]
  refine Sec7.Lemma71B.couplingMean_congr t.coe_nonneg (fun r hr => ?_) κ _ z
  exact wpath_sys_eq ((Real.toNNReal_le_toNNReal hr.2).trans (by rw [Real.toNNReal_coe]; exact ht))

end Sys

/-! ### Right-continuity of the coupling means of a killed word -/

/-- **The coupling means of a killed word are right-continuous before `min (swallowTime z) T`**: continue the
coordinates after a deterministic time strictly between the given time and `min (swallowTime z) T`, where the landed
continuity (`Sec7.PhaseSelFull.continuousAt_coupProc`) applies. -/
theorem IsKilledWord.continuousWithinAt_coupProc (hK : IsKilledWord W VL VR T) {κ : ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {z : ℂ} (hz : z ∈ H) (ω : Ω) (s : ℝ≥0)
    (hs : (s : WithTop ℝ≥0) < min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω)) :
    ContinuousWithinAt (coupProc κ ρL ρR W VL VR z · ω) (Ici s) s := by
  obtain ⟨r, hsr, hr⟩ := WithTop.lt_iff_exists_coe_btwn.1 hs
  have hsr' : s < r := WithTop.coe_lt_coe.1 hsr
  have hrT : (r : WithTop ℝ≥0) < T ω := lt_of_lt_of_le hr (min_le_right _ _)
  have hrS : (r : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) :=
    lt_of_lt_of_le hr (min_le_left _ _)
  -- the coordinates of the path `ω`, continued after `r` (constant in the sample)
  set σ' : Ω → ℝ≥0 := fun _ => r with hσ'
  set T' : Ω → WithTop ℝ≥0 := fun _ => T ω with hT'
  set W' : ℝ≥0 → Ω → ℝ := fun t _ => W t ω with hW'
  set VL' : Fin nL → ℝ≥0 → Ω → ℝ := fun i t _ => VL i t ω with hVL'
  set VR' : Fin nR → ℝ≥0 → Ω → ℝ := fun j t _ => VR j t ω with hVR'
  have hK' : IsKilledWord W' VL' VR' T' :=
    { w_zero := fun _ => hK.w_zero ω
      contW := fun _ => hK.contW ω
      ordL := fun _ => hK.ordL ω
      ordR := fun _ => hK.ordR ω
      pathL := fun _ => hK.pathL ω
      pathR := fun _ => hK.pathR ω
      antiL := fun _ => hK.antiL ω
      monoR := fun _ => hK.monoR ω
      idxL := fun _ => hK.idxL ω
      idxR := fun _ => hK.idxR ω
      mergeL := fun _ => hK.mergeL ω
      mergeR := fun _ => hK.mergeR ω
      sepL := fun _ => hK.sepL ω
      sepR := fun _ => hK.sepR ω }
  have hσT' : ∀ ω', (σ' ω' : WithTop ℝ≥0) < T' ω' := fun _ => hrT
  -- the swallowing time is not changed before `r`
  have hsw : (s : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath (sysW W' σ') ω) z : WithTop ℝ≥0) := by
    have he := Sec7.Lemma71B.min_swallowTime_congr (w := wpath W ω) (w' := wpath (sysW W' σ') ω)
      (c := (r : WithTop ℝ≥0)) (fun x _ hx => (wpath_sys_eq (WithTop.coe_le_coe.1 hx)).symm) hz
    have h1 : (s : WithTop ℝ≥0) < min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) r :=
      lt_min (lt_trans hsr hrS) hsr
    exact lt_of_lt_of_le (h1.trans_eq he) (min_le_left _ _)
  have hca := continuousAt_coupProc (κ := κ) (ρL := ρL) (ρR := ρR) (hK'.continuous_sysW hσT')
    (fun i => hK'.continuous_sysVL hσT' i) (fun j => hK'.continuous_sysVR hσT' j)
    (fun _ t i => contV_left_le_contW t) (fun _ t j => contW_le_contV_right t) hz ω hsw
  refine hca.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hsr')] with t ht
    exact (hK'.coupProc_sys_eq hσT' ht).symm
  · exact (hK'.coupProc_sys_eq hσT' hsr'.le).symm

/-! ### The coupling means of the continued system -/

/-- **The coupling means of the continued system at a stopping time `σ < T` are local martingales before
`min (swallowTime z) σ`**, when those of the killed word are local martingales before `min (swallowTime z) T`. -/
theorem IsKilledWord.isLocalMartingaleBefore_sys {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
    (hK : IsKilledWord W VL VR T) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω)
    (hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0)) {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc κ ρL ρR W VL VR z)) :
    ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (wpath (sysW W σ) ω) z : WithTop ℝ≥0) (σ ω))
      (coupProc κ ρL ρR (sysW W σ) (sysVL W VL σ) (sysVR W VR σ) z) := by
  intro z hz
  have h2 := isLocalMartingaleBefore_min_stop (hmart z hz) (hK.continuousWithinAt_coupProc hz) hσ
  have hζ : ∀ ω, min (min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (σ ω : WithTop ℝ≥0) =
      min (QuantumZipper.swallowTime (wpath (sysW W σ) ω) z : WithTop ℝ≥0) (σ ω) := fun ω => by
    calc _ = min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (min (T ω) (σ ω : WithTop ℝ≥0)) :=
          min_assoc _ _ _
      _ = min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (σ ω : WithTop ℝ≥0) :=
          congrArg (min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) (min_eq_right (hσT ω).le)
      _ = _ := Sec7.Lemma71B.min_swallowTime_congr
          (fun x _ hx => (wpath_sys_eq (WithTop.coe_le_coe.1 hx)).symm) hz
  have h3 := isLocalMartingaleBefore_congr_life hζ h2
  refine isLocalMartingaleBefore_sub_const_before 0 h3 fun t ω ht => ?_
  have hts : t ≤ σ ω := WithTop.coe_le_coe.1 (ht.trans (min_le_right _ _))
  rw [sub_zero]
  exact hK.coupProc_sys_eq hσT hts

end ImgDrv

end InteractingSLE.WangWu
