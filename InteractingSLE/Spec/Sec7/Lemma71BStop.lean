/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.AnnounceLifetime
import InteractingSLE.Spec.Sec7.Lemma71BMart
import InteractingSLE.Spec.Sec2.MartingaleFinalGeom
import InteractingSLE.Spec.Ito.Loewner
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# Lemma 7.1, terminal capacity: drivers killed at a random time and their stopped versions

Packet PROVE-LEMMA71B. Specification, proof of Lemma 7.1 (`source/spec/p193-240.md` L600–L604, p. 225) and Remark
6.14 (p. 218: "That proposition gives a continuous Loewner driver up to the terminal capacity time of `ψ(η_C)`").

The mapped pocket segment of Lemma 7.1 has a continuous Loewner driver `W` only up to its terminal capacity time
`T`, and its coupling means are local martingales only before `min (swallowTime z) T`. This file gives the tools to
apply Theorem 2.4's localization to such a killed driver:

* causality of the real Loewner flow (`rightImg_congr`), of the coupling mean (`couplingMean_congr`) and of the
  swallowing time below a random time (`min_swallowTime_congr`);
* `HasMartingaleMeansBefore`: the martingale hypothesis of Theorem 2.4 below a killing time `T`;
* `exitAbove W T G n`: the first time before `T` at which `|W| > n` (on an event `G`; `0` off `G`), a stopping time
  of a right-continuous filtration (`isStoppingTime_exitAbove`);
* `stopDrv W T G n`: the killed driver stopped at `exitAbove W T G n`, a continuous adapted driver bounded by `n`
  that agrees with `W` up to the exit time;
* **`isLocalMartingaleBefore_coupProc_stopDrv`**: the coupling means of the stopped driver are local martingales
  before `min (swallowTime z) (exitAbove W T G n)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71B

open MartChar MartChar.RealFlow Coupling

/-! ### Causality of the real Loewner flow and of the coupling mean -/

section Causality

theorem isPosSol_congr {w w' : ℝ → ℝ} {y t : ℝ} (h : EqOn w w' (Icc 0 t)) (X : ℝ → ℝ) :
    IsPosSol w y t X ↔ IsPosSol w' y t X := by
  unfold IsPosSol
  refine and_congr Iff.rfl (forall₂_congr fun s hs => ?_)
  rw [h hs]

theorem alive_congr {w w' : ℝ → ℝ} {y t : ℝ} (h : EqOn w w' (Icc 0 t)) :
    Alive w y t ↔ Alive w' y t :=
  exists_congr fun X => isPosSol_congr h X

theorem gImg_congr {w w' : ℝ → ℝ} (hw' : Continuous w') {y t : ℝ} (ht : 0 ≤ t)
    (h : EqOn w w' (Icc 0 t)) (hA : Alive w y t) : gImg w y t = gImg w' y t := by
  classical
  have hX' := (isPosSol_congr h _).1 hA.choose_spec
  show w t + cflow w y t = w' t + cflow w' y t
  rw [cflow_eq_of_isPosSol hw' hX' ⟨ht, le_rfl⟩, h ⟨ht, le_rfl⟩]
  unfold cflow
  simp only [hA, ↓reduceDIte]

/-- **The geometric image at time `t` only depends on the driver on `[0, t]`.** -/
theorem rightImg_congr {w w' : ℝ → ℝ} (hw' : Continuous w') {t : ℝ} (ht : 0 ≤ t)
    (h : EqOn w w' (Icc 0 t)) (x : ℝ) : rightImg w x t = rightImg w' x t := by
  unfold rightImg imgSet
  congr 1
  ext g
  constructor
  · rintro ⟨y, hxy, hy, rfl⟩
    exact ⟨y, hxy, (alive_congr h).1 hy, (gImg_congr hw' ht h hy).symm⟩
  · rintro ⟨y, hxy, hy, rfl⟩
    have hy' := (alive_congr h).2 hy
    exact ⟨y, hxy, hy', gImg_congr hw' ht h hy'⟩

/-- **The coupling mean at time `t` only depends on the driver on `[0, t]`.** -/
theorem couplingMean_congr {w w' : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (h : EqOn w w' (Icc 0 t)) (κ : ℝ)
    (u : ℂ → ℝ) (z : ℂ) : couplingMean κ w t u z = couplingMean κ w' t u z := by
  unfold couplingMean
  rw [Ito.fwdMap_congr_of_eqOn_of_le h le_rfl, Ito.logDerivFwd_congr_of_eqOn h ht le_rfl]

/-- Two extended times that agree below `c` have the same minimum with `c`. -/
theorem min_eq_min_of_forall_lt {a b c : WithTop ℝ≥0}
    (h : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) < c → (a ≤ s ↔ b ≤ s)) : min a c = min b c := by
  rcases lt_or_ge a c with hac | hca
  · obtain ⟨s, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hac)
    have hb : b ≤ s := (h s hac).1 le_rfl
    rw [min_eq_left hac.le, min_eq_left (hb.trans hac.le)]
    rcases lt_or_ge b (s : WithTop ℝ≥0) with hbs | hbs
    · exfalso
      obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hbs)
      exact absurd ((h r (hbs.trans hac)).2 le_rfl) (not_le.2 hbs)
    · exact le_antisymm hbs hb
  · rw [min_eq_right hca]
    rcases lt_or_ge b c with hbc | hcb
    · exfalso
      obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hbc)
      exact absurd (hca.trans ((h r hbc).2 le_rfl)) (not_le.2 hbc)
    · rw [min_eq_right hcb]

/-- **Swallowing times agree below a time up to which the drivers agree.** -/
theorem min_swallowTime_congr {w w' : ℝ → ℝ} {c : WithTop ℝ≥0}
    (h : ∀ r : ℝ, 0 ≤ r → ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ c → w r = w' r) {z : ℂ} (hz : z ∈ H) :
    min (QuantumZipper.swallowTime w z : WithTop ℝ≥0) c =
      min (QuantumZipper.swallowTime w' z : WithTop ℝ≥0) c := by
  refine min_eq_min_of_forall_lt fun s hs => ?_
  have hK : QuantumZipper.fwdHull w s = QuantumZipper.fwdHull w' s := by
    rcases eq_or_ne c ⊤ with hc | hc
    · refine fwdHull_eq_of_eqOn (t₂ := (s : ℝ) + 1) s.coe_nonneg (by linarith) fun r hr =>
        h r hr.1 (by rw [hc]; exact le_top)
    · obtain ⟨u, rfl⟩ := WithTop.ne_top_iff_exists.1 hc
      have hsu : s < u := WithTop.coe_lt_coe.1 hs
      refine fwdHull_eq_of_eqOn (t₂ := u) s.coe_nonneg (by exact_mod_cast hsu) fun r hr =>
        h r hr.1 ?_
      exact WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)
  have key : ∀ v : ℝ → ℝ, ((QuantumZipper.swallowTime v z : WithTop ℝ≥0) ≤ s ↔
      z ∈ QuantumZipper.fwdHull v s) := by
    intro v
    simp only [QuantumZipper.fwdHull, mem_ofPred_eq, hz, true_and, ENNReal.ofReal_coe_nnreal]
  exact (key w).trans (by rw [hK]; exact (key w').symm)

end Causality

/-! ### The martingale hypothesis of Theorem 2.4 below a killing time -/

section Before

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The martingale hypothesis of Theorem 2.4 below a killing time `T`** (proof of Lemma 7.1, p. 225, applied to the
driver of the mapped segment, which is defined up to its terminal capacity time). For the word with positions
`(xL; xR)` and weights `(ρL; ρR)`, with the force points at the geometric images (`MartChar.geomL`,
`MartChar.geomR`): every coupling mean `𝔥_t(z)`, `z ∈ ℍ`, for every choice of the bounded harmonic extensions, is a
local martingale in `𝓖` before `min (swallowTime z) T`. With `T = ⊤` it is the hypothesis of
`MartChar.isIntegratedSLEEvolution_geom_of_couplingMean`. -/
def HasMartingaleMeansBefore (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (P : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0∞) : Prop :=
  ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
    (∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => geomL W xL i t ω - W t ω)
        (fun i => geomR W xR i t ω - W t ω))
      (forceJumpSet (fun i => geomL W xL i t ω - W t ω) (fun i => geomR W xR i t ω - W t ω))
      (u ω t)) →
    ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z : WithTop ℝ≥0) (T ω))
      (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z)

end Before

/-! ### The exit time and the stopped driver -/

section Exit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {G : Set Ω}

open scoped Classical in
/-- **The exit time**: on `G`, the first time before `T` at which `|W| > n` (`⊤` if there is none); `0` off `G`. -/
def exitAbove (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (G : Set Ω) (n : ℝ) : Ω → WithTop ℝ≥0 :=
  fun ω => if ω ∈ G then hitBelow (fun s => -|W s ω|) (T ω) (-n) else 0

theorem exitAbove_of_mem {n : ℝ} {ω : Ω} (hω : ω ∈ G) :
    exitAbove W T G n ω = hitBelow (fun s => -|W s ω|) (T ω) (-n) := by
  classical
  simp only [exitAbove, hω, ↓reduceIte]

theorem exitAbove_of_notMem {n : ℝ} {ω : Ω} (hω : ω ∉ G) : exitAbove W T G n ω = 0 := by
  classical
  simp only [exitAbove, hω, ↓reduceIte]

/-- **The exit time is a stopping time** of a right-continuous filtration in which `W` is adapted before `T`. -/
theorem isStoppingTime_exitAbove {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
    (hWa : AdaptedBefore 𝓖 T W) (hG : MeasurableSet[𝓖 0] G)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω}) (n : ℝ) :
    IsStoppingTime 𝓖 (exitAbove W T G n) := by
  classical
  have h1 := isStoppingTime_hitBelow_state (nL := 0) (nR := 0) (VL := fun i => Fin.elim0 i)
    (VR := fun i => Fin.elim0 i) hWa (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hG
    (fun ω _ => (hc ω).prodMk ((continuousOn_pi.2 fun i => Fin.elim0 i).prodMk
      (continuousOn_pi.2 fun i => Fin.elim0 i))) (Φ := fun p => -|p.1|) continuous_fst.abs.neg (-n)
  have h2 : IsStoppingTime 𝓖 fun ω => if ω ∈ G then (⊤ : WithTop ℝ≥0) else 0 := by
    intro t
    have heq : {ω | (if ω ∈ G then (⊤ : WithTop ℝ≥0) else 0) ≤ t} = Gᶜ := by
      ext ω
      by_cases hω : ω ∈ G
      · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_compl_iff, not_true_eq_false, iff_false]
        exact fun h => WithTop.coe_ne_top (top_le_iff.1 h)
      · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_compl_iff, not_false_eq_true, iff_true]
        rw [← WithTop.coe_zero]
        exact WithTop.coe_le_coe.2 zero_le
    rw [heq]
    exact 𝓖.mono (by simp : (0 : ℝ≥0) ≤ t) _ hG.compl
  convert h1.min h2 using 1
  funext ω
  by_cases hω : ω ∈ G
  · simp [exitAbove, hω, stateAt]
  · simp [exitAbove, hω]

variable {ω : Ω}

theorem exitAbove_ne_top {n : ℝ} (hω : ω ∈ G)
    (hunb : T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) (hT : T ω ≠ ⊤) :
    exitAbove W T G n ω ≠ ⊤ := by
  obtain ⟨s, hs, hlt⟩ := hunb hT n
  rw [exitAbove_of_mem hω]
  exact ne_top_of_le_ne_top WithTop.coe_ne_top
    (hitBelow_le (f := fun s => -|W s ω|) hs (by linarith : -|W s ω| < -n))

theorem lt_of_exitAbove_eq {n : ℝ} (hω : ω ∈ G) {u : ℝ≥0} (h : exitAbove W T G n ω = u) :
    (u : ℝ≥0∞) < T ω := by
  rw [exitAbove_of_mem hω] at h
  exact lt_of_hitBelow_eq h

/-- Times up to the exit time are before `T`. -/
theorem lt_of_le_exitAbove {n : ℝ} (hω : ω ∈ G)
    (hunb : T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ exitAbove W T G n ω) : (s : ℝ≥0∞) < T ω := by
  rcases eq_or_ne (exitAbove W T G n ω) ⊤ with htop | hne
  · have hT : T ω = ⊤ := by
      by_contra hT
      exact exitAbove_ne_top hω hunb hT htop
    rw [hT]
    exact ENNReal.coe_lt_top
  · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 hne
    have hsu : s ≤ u := by rw [← hu] at hs; exact WithTop.coe_le_coe.1 hs
    exact lt_of_le_of_lt (by exact_mod_cast hsu) (lt_of_exitAbove_eq hω hu.symm)

/-- **Up to the exit time, `|W| ≤ n`.** -/
theorem abs_le_of_le_exitAbove {n : ℝ} (hn : 0 ≤ n) (hω : ω ∈ G) (hW0 : W 0 ω = 0)
    (hc : ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hunb : T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ exitAbove W T G n ω) : |W s ω| ≤ n := by
  have hsT := lt_of_le_exitAbove hω hunb hs
  by_contra hlt
  rw [not_le] at hlt
  have hhit : exitAbove W T G n ω ≤ s := by
    rw [exitAbove_of_mem hω]
    exact hitBelow_le (f := fun s => -|W s ω|) hsT (by linarith)
  have heq : exitAbove W T G n ω = s := le_antisymm hhit hs
  have hs0 : 0 < s := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, hW0, abs_zero] at hlt
    linarith
  have hopen := (isOpen_setOf_coe_lt (T ω)).mem_nhds hsT
  have hca : ContinuousAt (fun r => W r ω) s := hc.continuousAt hopen
  have hev : ∀ᶠ r in 𝓝 s, n < |W r ω| ∧ (r : ℝ≥0∞) < T ω :=
    ((hca.abs).eventually (lt_mem_nhds hlt)).and hopen
  have hne : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs0⟩
  have hev' : ∀ᶠ r in 𝓝[<] s, (n < |W r ω| ∧ (r : ℝ≥0∞) < T ω) ∧ r ∈ Iio s :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨r, ⟨hr1, hr2⟩, hrs⟩ := hev'.exists
  have hle : exitAbove W T G n ω ≤ r := by
    rw [exitAbove_of_mem hω]
    exact hitBelow_le (f := fun s => -|W s ω|) hr2 (by linarith)
  rw [heq] at hle
  exact absurd (WithTop.coe_le_coe.1 hle) (not_le.2 hrs)

/-- **The exit times exhaust `[0, T)`.** -/
theorem exists_lt_exitAbove (hω : ω ∈ G)
    (hc : ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T ω) : ∃ C : ℝ, ∀ n : ℝ, C < n → (t : WithTop ℝ≥0) < exitAbove W T G n ω := by
  obtain ⟨t', htt', ht'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hsub : Icc (0 : ℝ≥0) t' ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < T ω} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs.2) ht'T
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono hsub)
  refine ⟨C, fun n hn => ?_⟩
  rw [exitAbove_of_mem hω]
  refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 htt')) (le_hitBelow fun s _ hfs => ?_)
  by_contra hst
  rw [not_le] at hst
  have h := hC s ⟨zero_le, hst.le⟩
  rw [Real.norm_eq_abs] at h
  linarith

/-- The minimum with the zero time. -/
theorem untopA_min_zero (s : ℝ≥0) : (min (s : WithTop ℝ≥0) 0).untopA = 0 := by
  have h : min (s : WithTop ℝ≥0) 0 = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
    rw [WithTop.coe_zero]
    exact min_eq_right (by rw [← WithTop.coe_zero]; exact WithTop.coe_le_coe.2 zero_le)
  rw [h]
  rfl

/-- **The killed driver stopped at the exit time.** -/
def stopDrv (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (G : Set Ω) (n : ℝ) : ℝ≥0 → Ω → ℝ :=
  stoppedProcess (Girsanov.killed T W) (exitAbove W T G n)

/-- The stopped driver agrees with `W` up to the exit time (also off `G`, where the exit time is `0`). -/
theorem stopDrv_eq_of_le {n : ℝ} (hW0 : W 0 ω = 0)
    (hunb : ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ exitAbove W T G n ω) : stopDrv W T G n s ω = W s ω := by
  rw [stopDrv, stoppedProcess_eq_of_le hs]
  by_cases hω : ω ∈ G
  · exact Girsanov.killed_of_lt (lt_of_le_exitAbove hω (hunb hω) hs)
  · rw [exitAbove_of_notMem hω] at hs
    have hs0 : s = 0 := le_antisymm (by exact_mod_cast hs) zero_le
    subst hs0
    simp only [Girsanov.killed, hW0, ite_self]

/-- The stopped driver at `s` is its value at `min s (exitAbove)`. -/
theorem stopDrv_eq_min {n : ℝ} (s : ℝ≥0) (ω : Ω) :
    stopDrv W T G n s ω = stopDrv W T G n (min (s : WithTop ℝ≥0) (exitAbove W T G n ω)).untopA ω := by
  have hne : min (s : WithTop ℝ≥0) (exitAbove W T G n ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hle : (((min (s : WithTop ℝ≥0) (exitAbove W T G n ω)).untopA : ℝ≥0) : WithTop ℝ≥0) ≤
      exitAbove W T G n ω := by
    rw [coe_untopA_of_ne_top hne]
    exact min_le_right _ _
  rw [stopDrv, stoppedProcess_eq_of_le hle]
  rfl

theorem le_exitAbove_min {n : ℝ} (s : ℝ≥0) (ω : Ω) :
    (((min (s : WithTop ℝ≥0) (exitAbove W T G n ω)).untopA : ℝ≥0) : WithTop ℝ≥0) ≤
      exitAbove W T G n ω := by
  rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
  exact min_le_right _ _

theorem stopDrv_zero {n : ℝ} (hW0 : W 0 ω = 0)
    (hunb : ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) :
    stopDrv W T G n 0 ω = 0 := by
  rw [stopDrv_eq_of_le hW0 hunb (by simp), hW0]

/-- **The stopped driver is bounded by `n`.** -/
theorem abs_stopDrv_le {n : ℝ} (hn : 0 ≤ n) (hW0 : W 0 ω = 0)
    (hc : ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hunb : ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) (s : ℝ≥0) :
    |stopDrv W T G n s ω| ≤ n := by
  rw [stopDrv_eq_min, stopDrv_eq_of_le hW0 hunb (le_exitAbove_min s ω)]
  by_cases hω : ω ∈ G
  · exact abs_le_of_le_exitAbove hn hω hW0 hc (hunb hω) (le_exitAbove_min s ω)
  · have h0 : (min (s : WithTop ℝ≥0) (exitAbove W T G n ω)).untopA = 0 := by
      rw [exitAbove_of_notMem hω]
      exact untopA_min_zero s
    rw [h0, hW0, abs_zero]
    exact hn

/-- **The stopped driver is continuous.** -/
theorem continuous_stopDrv {n : ℝ} (hW0 : W 0 ω = 0)
    (hc : ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hunb : ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) :
    Continuous fun s => stopDrv W T G n s ω := by
  by_cases hω : ω ∈ G
  · rcases eq_or_ne (exitAbove W T G n ω) ⊤ with htop | hne
    · have hT : T ω = ⊤ := by
        by_contra hT
        exact exitAbove_ne_top hω (hunb hω) hT htop
      have heq : (fun s => stopDrv W T G n s ω) = fun s => W s ω := funext fun s =>
        stopDrv_eq_of_le hW0 hunb (by rw [htop]; exact le_top)
      rw [heq]
      have huniv : {s : ℝ≥0 | (s : ℝ≥0∞) < T ω} = univ := by
        ext s
        simp [hT]
      rw [huniv] at hc
      exact continuousOn_univ.1 hc
    · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 hne
      have huT := lt_of_exitAbove_eq hω hu.symm
      have hmem : ∀ s : ℝ≥0, min s u ∈ {s : ℝ≥0 | (s : ℝ≥0∞) < T ω} := fun s =>
        lt_of_le_of_lt (by exact_mod_cast min_le_right s u) huT
      have heq : (fun s => stopDrv W T G n s ω) = fun s => W (min s u) ω := funext fun s => by
        rw [stopDrv_eq_min, stopDrv_eq_of_le hW0 hunb (le_exitAbove_min s ω), ← hu]
        rfl
      rw [heq]
      exact hc.comp_continuous (continuous_id.min continuous_const) hmem
  · have heq : (fun s => stopDrv W T G n s ω) = fun _ => (0 : ℝ) := funext fun s => by
      rw [stopDrv_eq_min, stopDrv_eq_of_le hW0 hunb (le_exitAbove_min s ω), exitAbove_of_notMem hω,
        untopA_min_zero s, hW0]
    rw [heq]
    exact continuous_const

/-- **The stopped driver is adapted.** The killed process is right-continuous and adapted, hence progressive, and
the exit time is a stopping time. -/
theorem stronglyAdapted_stopDrv {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
    (hWa : AdaptedBefore 𝓖 T W) (hG : MeasurableSet[𝓖 0] G)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω}) (n : ℝ) :
    StronglyAdapted 𝓖 (stopDrv W T G n) := by
  have hKa : StronglyAdapted 𝓖 (Girsanov.killed T W) := fun t =>
    (Girsanov.measurable_killed hWa t).stronglyMeasurable
  have hKrc : ∀ ω t, ContinuousWithinAt (Girsanov.killed T W · ω) (Ici t) t := by
    intro ω t
    by_cases ht : (t : ℝ≥0∞) < T ω
    · have hopen := (isOpen_setOf_coe_lt (T ω)).mem_nhds ht
      have hca : ContinuousAt (fun s => W s ω) t := (hc ω).continuousAt hopen
      refine (hca.congr ?_).continuousWithinAt
      filter_upwards [hopen] with s hs
      exact (Girsanov.killed_of_lt hs).symm
    · have hzero : ∀ s ∈ Ici t, Girsanov.killed T W s ω = 0 := fun s hs => by
        have h : ¬ ((s : ℝ≥0∞) < T ω) := fun h => ht (lt_of_le_of_lt (by exact_mod_cast hs) h)
        simp only [Girsanov.killed, h, ↓reduceIte]
      exact (continuousWithinAt_const (b := (0 : ℝ))).congr (fun s hs => hzero s hs)
        (hzero t (mem_Ici.2 le_rfl))
  exact (isStronglyProgressive_of_rightContinuous hKa hKrc).stronglyAdapted_stoppedProcess
    (isStoppingTime_exitAbove hWa hG hc n)

end Exit

end InteractingSLE.Sec7.Lemma71B
