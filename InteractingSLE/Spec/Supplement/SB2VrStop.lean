/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VrBad
import InteractingSLE.Spec.Supplement.SB2VcClock

/-!
# D10's stops, steps 2 and 3 (deterministic part)

Packet PROVE-AUX61-NOJUMP (decision D10). Along one sample, with `γ` the lift, `t_L` the entrance, `Z` the physical
lifetime, `a = Vc.clockOf γ t_L Z` the relative clock, `η'` the centred physical flow and `F` the closed bad set:

* **`physStop`**: the `m`-th stop, the relative clock at the first entrance after `t_L` of the flow into the
  `min(d₀, 1)·(m+2)⁻¹`-neighbourhood of `F` (`d₀` the extended distance of the start from `F`, so an empty `F` is
  never entered and the stop is positive when the start is off `F`), capped at the relative clock of the physical time
  `t_L + m + 1`;
* **`physStop_lt`** (step 2): every stop is strictly below the relative lifetime: at a finite `Z` the flow is on `F`
  (step 1) and continuous at `Z` (Theorem 1.3), so the entrance happens strictly before `Z`; the capacity clock is
  strictly increasing before `Z`;
* **`physStop_mono`**, **`iSup_physStop`** (step 3): the stops increase to the relative lifetime when the flow avoids
  `F` before `Z` (`ae_notMem_closure_badSet`): on each `[t_L, t_L + s]` the flow keeps a positive distance from `F`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vr

/-- The level of the `m`-th stop. -/
def lev (m : ℕ) : ℝ≥0∞ := ((m : ℝ≥0∞) + 1)⁻¹

theorem lev_pos (m : ℕ) : 0 < lev m := ENNReal.inv_pos.2 (by simp)

theorem lev_anti : Antitone lev := fun m m' h =>
  ENNReal.inv_le_inv.2 (by gcongr)

/-- The level of the `m`-th stop, relative to the distance `d₀` of the start from `F`: `min d₀ 1 · (m+2)⁻¹`. -/
def stopLev (η' : ℝ≥0 → ℂ) (F : Set ℂ) (tL : ℝ≥0) (m : ℕ) : ℝ≥0∞ := min (infEDist (η' tL) F) 1 * lev (m + 1)

/-- The entrance set of the `m`-th stop: physical times in `[t_L, Z)` at which the flow is within `stopLev m` of `F`. -/
def entSet (η' : ℝ≥0 → ℂ) (F : Set ℂ) (tL : ℝ≥0) (Z : ℝ≥0∞) (m : ℕ) : Set ℝ≥0 :=
  {t | tL ≤ t ∧ (t : ℝ≥0∞) < Z ∧ infEDist (η' t) F ≤ stopLev η' F tL m}

/-- **D10's `m`-th stop (physical form).** -/
def physStop (γ η' : ℝ≥0 → ℂ) (F : Set ℂ) (tL : ℝ≥0) (Z : ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  min (⨅ t ∈ entSet η' F tL Z m, Vc.clockOf γ tL Z t) (Vc.clockOf γ tL Z (tL + (m + 1 : ℕ)))

/-- The relative lifetime: the supremum of the capacity clock of the lift before the physical lifetime. -/
def relLifeOf (γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (Z : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (s : ℝ≥0) (_ : ((tL + s : ℝ≥0) : ℝ≥0∞) < Z),
    ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s)

section Det

variable {γ η' : ℝ≥0 → ℂ} {F : Set ℂ} {tL : ℝ≥0} {Z : ℝ≥0∞}

/-- The capacity clock is strictly increasing before the lifetime. -/
def StrictBefore (γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (Z : ℝ≥0∞) : Prop :=
  ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ < s₂ → ENNReal.ofReal ((tL : ℝ) + s₂) < Z →
    Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s₁ < Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s₂

theorem clockOf_val (hstr : StrictBefore γ tL Z) {t : ℝ≥0} (htL : tL ≤ t) (htZ : (t : ℝ≥0∞) < Z) :
    Vc.clockOf γ tL Z t =
      ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) ((t : ℝ) - tL)) := by
  refine Vc.clockOf_eq htL htZ fun x hx y hy hxy => ?_
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · refine (hstr x y hx.1 h ?_).le
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (show (tL : ℝ) + y ≤ t by linarith [hy.2])) ?_
    rwa [ENNReal.ofReal_coe_nnreal]

theorem capClock_nonneg (h0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0 = 0)
    (hstr : StrictBefore γ tL Z) {s : ℝ} (hs : 0 ≤ s) (hsZ : ENNReal.ofReal ((tL : ℝ) + s) < Z) :
    0 ≤ Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, h0]
  · rw [← h0]; exact (hstr 0 s le_rfl h hsZ).le

/-- **Before the lifetime the clock is strictly below the relative lifetime.** -/
theorem clockOf_lt_relLifeOf (h0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0 = 0)
    (hstr : StrictBefore γ tL Z) {t : ℝ≥0} (htL : tL ≤ t) (htZ : (t : ℝ≥0∞) < Z) :
    Vc.clockOf γ tL Z t < relLifeOf γ tL Z := by
  obtain ⟨t₂, htt₂, ht₂Z⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htZ
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast ENNReal.coe_lt_coe.1 htt₂
  have htL' : (tL : ℝ) ≤ t := by exact_mod_cast htL
  set s₂ : ℝ≥0 := t₂ - tL with hs₂
  have hs₂r : (s₂ : ℝ) = (t₂ : ℝ) - tL := NNReal.coe_sub (by exact_mod_cast (htL'.trans htt₂'.le))
  have hts : tL + s₂ = t₂ := add_tsub_cancel_of_le (by exact_mod_cast (htL'.trans htt₂'.le))
  have hZ2 : ENNReal.ofReal ((tL : ℝ) + s₂) < Z := by
    rw [hs₂r, add_sub_cancel, ENNReal.ofReal_coe_nnreal]; exact ht₂Z
  have hlt := hstr ((t : ℝ) - tL) s₂ (by linarith) (by rw [hs₂r]; linarith) hZ2
  have hnn := capClock_nonneg h0 hstr (s := (t : ℝ) - tL) (by linarith)
    (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by rw [hs₂r]; linarith)) hZ2)
  rw [clockOf_val hstr htL htZ]
  refine lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (hnn.trans_lt hlt)).2 hlt) ?_
  exact le_iSup₂_of_le s₂ (by rw [hts]; exact ht₂Z) le_rfl

theorem stopLev_le_lev (η' : ℝ≥0 → ℂ) (F : Set ℂ) (tL : ℝ≥0) (m : ℕ) : stopLev η' F tL m ≤ lev (m + 1) :=
  (mul_le_mul' (min_le_right _ _) le_rfl).trans (one_mul _).le

theorem stopLev_pos {η' : ℝ≥0 → ℂ} {F : Set ℂ} {tL : ℝ≥0} (hd : 0 < infEDist (η' tL) F) (m : ℕ) :
    0 < stopLev η' F tL m :=
  ENNReal.mul_pos (lt_min hd one_pos).ne' (lev_pos _).ne'

theorem stopLev_lt {η' : ℝ≥0 → ℂ} {F : Set ℂ} {tL : ℝ≥0} (hd : 0 < infEDist (η' tL) F) (m : ℕ) :
    stopLev η' F tL m < infEDist (η' tL) F := by
  have hlev : lev (m + 1) < 1 := by
    unfold lev
    rw [ENNReal.inv_lt_one]
    exact_mod_cast (show (1 : ℕ) < m + 1 + 1 by omega)
  have h := ENNReal.mul_lt_mul_left (lt_min hd one_pos).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)) hlev
  calc stopLev η' F tL m = lev (m + 1) * min (infEDist (η' tL) F) 1 := mul_comm _ _
    _ < 1 * min (infEDist (η' tL) F) 1 := h
    _ ≤ infEDist (η' tL) F := by rw [one_mul]; exact min_le_left _ _

theorem stopLev_anti {η' : ℝ≥0 → ℂ} {F : Set ℂ} {tL : ℝ≥0} : Antitone (stopLev η' F tL) := fun _ _ h =>
  mul_le_mul' le_rfl (lev_anti (by omega))

/-- **Step 2: every stop is strictly below the relative lifetime.** -/
theorem physStop_lt (h0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0 = 0)
    (hstr : StrictBefore γ tL Z) (hTZ : (tL : ℝ≥0∞) < Z)
    (hcont : ContinuousOn η' {t | tL ≤ t ∧ (t : ℝ≥0∞) ≤ Z})
    (hend : ∀ T : ℝ≥0, (T : ℝ≥0∞) = Z → η' T ∈ F) (m : ℕ) :
    physStop γ η' F tL Z m < relLifeOf γ tL Z := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ infEDist (η' tL) F) with hd | hd
  · -- the start is on `F`: the stop is at the start
    refine lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt (iInf₂_le tL ⟨le_rfl, hTZ, ?_⟩) ?_)
    · exact clockOf_lt_relLifeOf h0 hstr le_rfl hTZ
    · rw [← hd]; exact zero_le
  by_cases hZ : Z = ⊤
  · refine lt_of_le_of_lt (min_le_right _ _) (clockOf_lt_relLifeOf h0 hstr le_self_add ?_)
    rw [hZ]; exact ENNReal.coe_lt_top
  · obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = Z := ⟨Z.toNNReal, ENNReal.coe_toNNReal hZ⟩
    have hLT : tL < T := by rw [← hT] at hTZ; exact_mod_cast hTZ
    have hf : ContinuousWithinAt (fun t => infEDist (η' t) F) {t | tL ≤ t ∧ (t : ℝ≥0∞) ≤ Z} T :=
      (continuous_infEDist.comp_continuousOn hcont) T ⟨hLT.le, hT.le⟩
    have hfT : infEDist (η' T) F = 0 := infEDist_zero_of_mem (hend T hT)
    have hev : ∀ᶠ t in 𝓝[{t | tL ≤ t ∧ (t : ℝ≥0∞) ≤ Z}] T, infEDist (η' t) F < stopLev η' F tL m :=
      hf.eventually (gt_mem_nhds (show infEDist (η' T) F < stopLev η' F tL m by rw [hfT]; exact stopLev_pos hd m))
    have hsub : Ioo tL T ⊆ {t | tL ≤ t ∧ (t : ℝ≥0∞) ≤ Z} := fun t ht =>
      ⟨ht.1.le, by rw [← hT]; exact_mod_cast ht.2.le⟩
    have hne : (𝓝[Ioo tL T] T).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hLT.ne]; exact ⟨hLT.le, le_rfl⟩
    obtain ⟨t, htev, htI⟩ := ((hev.filter_mono (nhdsWithin_mono T hsub)).and self_mem_nhdsWithin).exists
    have htZ : (t : ℝ≥0∞) < Z := by rw [← hT]; exact_mod_cast htI.2
    refine lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt (iInf₂_le t ⟨htI.1.le, htZ, htev.le⟩) ?_)
    exact clockOf_lt_relLifeOf h0 hstr htI.1.le htZ

/-- **Step 3, monotonicity.** -/
theorem physStop_mono : Monotone (physStop γ η' F tL Z) := fun m m' hmm' =>
  min_le_min (iInf₂_mono' fun t ht => ⟨t, ⟨ht.1, ht.2.1, ht.2.2.trans (stopLev_anti hmm')⟩, le_rfl⟩)
    (Vc.monotone_clockOf γ tL Z (add_le_add_right (by exact_mod_cast (by omega : m + 1 ≤ m' + 1)) tL))

/-- **Step 3: the stops increase to the relative lifetime.** -/
theorem iSup_physStop (h0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0 = 0)
    (hstr : StrictBefore γ tL Z) (hTZ : (tL : ℝ≥0∞) < Z)
    (hcont : ContinuousOn η' {t | tL ≤ t ∧ (t : ℝ≥0∞) ≤ Z})
    (hend : ∀ T : ℝ≥0, (T : ℝ≥0∞) = Z → η' T ∈ F) (hF : IsClosed F)
    (hnv : ∀ t : ℝ≥0, tL ≤ t → (t : ℝ≥0∞) < Z → η' t ∉ F) :
    ⨆ m, physStop γ η' F tL Z m = relLifeOf γ tL Z := by
  refine le_antisymm (iSup_le fun m => (physStop_lt h0 hstr hTZ hcont hend m).le) (iSup₂_le fun s hs => ?_)
  set ts := tL + s with htsdef
  have hK : ContinuousOn (fun t => infEDist (η' t) F) (Icc tL ts) :=
    continuous_infEDist.comp_continuousOn (hcont.mono fun t ht =>
      ⟨ht.1, (ENNReal.coe_le_coe.2 ht.2).trans hs.le⟩)
  obtain ⟨t₀, ht₀K, ht₀min⟩ := isCompact_Icc.exists_isMinOn ⟨tL, left_mem_Icc.2 le_self_add⟩ hK
  have hδ : 0 < infEDist (η' t₀) F := by
    rw [infEDist_pos_iff_notMem_closure, hF.closure_eq]
    exact hnv t₀ ht₀K.1 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₀K.2) hs)
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
  set m := max n ⌈(s : ℝ)⌉₊ with hm
  have hsm : (s : ℝ) ≤ ((m + 1 : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans (Nat.le_succ m))
  have hval : Vc.clockOf γ tL Z ts = ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s) := by
    rw [clockOf_val hstr le_self_add hs, NNReal.coe_add, add_sub_cancel_left]
  refine le_trans ?_ (le_iSup _ m)
  rw [← hval]
  refine le_min (le_iInf₂ fun t ht => Vc.monotone_clockOf γ tL Z ?_) (Vc.monotone_clockOf γ tL Z ?_)
  · by_contra hlt
    rw [not_le] at hlt
    have h1 := ht₀min ⟨ht.1, hlt.le⟩
    have h2 : stopLev η' F tL m ≤ (n : ℝ≥0∞)⁻¹ := (stopLev_le_lev η' F tL m).trans
      (ENNReal.inv_le_inv.2 ((by exact_mod_cast (le_max_left n _).trans (Nat.le_succ m) :
        (n : ℝ≥0∞) ≤ ((m + 1 : ℕ) : ℝ≥0∞)).trans le_self_add))
    exact lt_irrefl _ (lt_of_le_of_lt (h1.trans (ht.2.2.trans h2)) hn)
  · refine add_le_add_right ?_ tL
    exact_mod_cast hsm

/-- After the entrance the clock is positive. -/
theorem clockOf_pos (h0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0 = 0)
    (hstr : StrictBefore γ tL Z) {t : ℝ≥0} (htL : tL < t) (htZ : (t : ℝ≥0∞) < Z) : 0 < Vc.clockOf γ tL Z t := by
  rw [clockOf_val hstr htL.le htZ, ENNReal.ofReal_pos, ← h0]
  have htL' : (tL : ℝ) < t := by exact_mod_cast htL
  refine hstr 0 _ le_rfl (by linarith) ?_
  rw [add_sub_cancel, ENNReal.ofReal_coe_nnreal]; exact htZ

/-- **Every stop is positive** when the start is off `F`. -/
theorem physStop_pos (h0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0 = 0)
    (hstr : StrictBefore γ tL Z) (hTZ : (tL : ℝ≥0∞) < Z)
    (hcont : ContinuousOn η' {t | tL ≤ t ∧ (t : ℝ≥0∞) ≤ Z}) (hd : 0 < infEDist (η' tL) F) (m : ℕ) :
    0 < physStop γ η' F tL Z m := by
  -- a time just after the start, before `Z`, `t_L + 1` and the first entrance
  have hf : ContinuousWithinAt (fun t => infEDist (η' t) F) {t | tL ≤ t ∧ (t : ℝ≥0∞) ≤ Z} tL :=
    (continuous_infEDist.comp_continuousOn hcont) tL ⟨le_rfl, hTZ.le⟩
  have hev : ∀ᶠ t in 𝓝[{t | tL ≤ t ∧ (t : ℝ≥0∞) ≤ Z}] tL, stopLev η' F tL m < infEDist (η' t) F :=
    hf.eventually (lt_mem_nhds (stopLev_lt hd m))
  obtain ⟨T, hTL, hTZ'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTZ
  have hLT : tL < T := by exact_mod_cast hTL
  -- on `[t_L, t₁]` the flow stays farther than the level
  obtain ⟨ε, hε, hball⟩ := (Metric.mem_nhdsWithin_iff.1 hev)
  set t₁ : ℝ≥0 := min (tL + (ε / 2).toNNReal) (min T (tL + 1)) with ht₁
  have ht₁L : tL < t₁ := lt_min (lt_add_of_pos_right _ (Real.toNNReal_pos.2 (half_pos hε)))
    (lt_min hLT (lt_add_of_pos_right _ one_pos))
  have ht₁T : t₁ ≤ T := (min_le_right _ _).trans (min_le_left _ _)
  have ht₁Z : (t₁ : ℝ≥0∞) < Z := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₁T) hTZ'
  have hfar : ∀ t : ℝ≥0, tL ≤ t → t ≤ t₁ → stopLev η' F tL m < infEDist (η' t) F := fun t h1 h2 => by
    refine hball ⟨?_, h1, (ENNReal.coe_le_coe.2 (h2.trans ht₁T)).trans hTZ'.le⟩
    rw [mem_ball, NNReal.dist_eq]
    have h3 : (t₁ : ℝ) ≤ tL + ε / 2 := by
      have := min_le_left (tL + (ε / 2).toNNReal) (min T (tL + 1))
      rw [← ht₁] at this
      have h6 : ((tL + (ε / 2).toNNReal : ℝ≥0) : ℝ) = tL + ε / 2 := by
        rw [NNReal.coe_add, Real.coe_toNNReal _ (by positivity)]
      rw [← h6]; exact_mod_cast this
    have h4 : (tL : ℝ) ≤ t := by exact_mod_cast h1
    have h5 : (t : ℝ) ≤ t₁ := by exact_mod_cast h2
    rw [abs_lt]; constructor <;> linarith
  have hpos₁ := clockOf_pos h0 hstr ht₁L ht₁Z
  refine lt_min (lt_of_lt_of_le hpos₁ (le_iInf₂ fun t ht => Vc.monotone_clockOf γ tL Z ?_)) ?_
  · by_contra hlt
    rw [not_le] at hlt
    exact absurd ht.2.2 (not_le.2 (hfar t ht.1 hlt.le))
  · refine lt_of_lt_of_le hpos₁ (Vc.monotone_clockOf γ tL Z ?_)
    have h1 : t₁ ≤ tL + 1 := (min_le_right _ _).trans (min_le_right _ _)
    exact h1.trans (add_le_add_right (by exact_mod_cast (by omega : 1 ≤ m + 1)) tL)

end Det

end InteractingSLE.Theorem14.SB.Vr
