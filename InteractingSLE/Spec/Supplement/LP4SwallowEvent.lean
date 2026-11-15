/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP4SwallowFlow
import InteractingSLE.Spec.Supplement.LP4HalfBallStraddle
import InteractingSLE.Spec.ZhanGT4.NoClusterCode
import InteractingSLE.Spec.ZhanGT4.TwoForceRatio
import InteractingSLE.Spec.Sec4.ZeroMarks
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# LP4's right swallowing: the swallowing events and their canonical laws

Packet PROVE-LP18. The event of LP4's first paragraph (specification p. 482) for a word with one right mark at
`r = x_R ≥ 0`: "some point beyond the right mark is swallowed at a finite time", and its windowed form "… by a time
`t < N`, before which the driver stays above `−M`" (the buffered stop of the source).

* `RWin M N r w`, `RAll r w`: the real-time events; `rAll_iff_exists_rWin`;
* `rWin_dilPath_iff`, `rAll_dilPath_iff`: Brownian scaling (`Θ_c w = c^{-1/2} w(c ·)` maps the window `(√c M, c N)`
  beyond `r` to the window `(M, N)` beyond `c^{-1/2} r`);
* `SwalWin`, `SwalAll`: the same events through countably many rational data (positive rational points, rational
  times, the universal measurable alive sets `LP3.aliveSet`), so that their code sets `winSet`, `allSet` are Borel;
  `swalWin_top_iff`, `swalAll_top_iff`: they are the real events for continuous drivers with infinite lifetime;
* `codeLaw_winSet_dilate`, `codeLaw_allSet_dilate`: dilation of their canonical probabilities;
* `codeLaw_winSet_zero`, `codeLaw_allSet_zero`: a left mark of weight `0` does not change them (deletion of the
  zero-weight mark, `IsIntegratedSLEEvolution.compEmb`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.LP.LP4S

open QuantumZipper QuantumZipper.RS Sec2 Sec2.Assembly Sec7.RandRestart Sec7.Dilation

/-! ### The real-time events -/

/-- **Swallowing beyond `r` within a window**: some point `y > max(r, 0)` is swallowed by a time `t < N` before which
the driver stays above `−M`. -/
def RWin (M N r : ℝ) (w : ℝ≥0 → ℝ) : Prop :=
  ∃ y : ℝ, 0 < y ∧ r < y ∧ ∃ t : ℝ≥0, (t : ℝ) < N ∧ ¬ LP3.Alive (fun s : ℝ => w s.toNNReal) y t ∧
    ∀ u : ℝ≥0, u ≤ t → -M < w u

/-- **Swallowing beyond `r`**: some point `y > max(r, 0)` is swallowed at a finite time. -/
def RAll (r : ℝ) (w : ℝ≥0 → ℝ) : Prop :=
  ∃ y : ℝ, 0 < y ∧ r < y ∧ ∃ t : ℝ≥0, ¬ LP3.Alive (fun s : ℝ => w s.toNNReal) y t

theorem RWin.mono {M N M' N' r : ℝ} {w : ℝ≥0 → ℝ} (h : RWin M N r w) (hM : M ≤ M') (hN : N ≤ N') :
    RWin M' N' r w := by
  obtain ⟨y, hy0, hry, t, htN, hd, hlow⟩ := h
  exact ⟨y, hy0, hry, t, htN.trans_le hN, hd, fun u hu => by linarith [hlow u hu]⟩

theorem RWin.rAll {M N r : ℝ} {w : ℝ≥0 → ℝ} (h : RWin M N r w) : RAll r w := by
  obtain ⟨y, hy0, hry, t, -, hd, -⟩ := h
  exact ⟨y, hy0, hry, t, hd⟩

theorem rAll_iff_exists_rWin {r : ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous w) :
    RAll r w ↔ ∃ M N : ℝ, RWin M N r w := by
  refine ⟨fun ⟨y, hy0, hry, t, hd⟩ => ?_, fun ⟨M, N, h⟩ => h.rAll⟩
  obtain ⟨u₀, -, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_isMinOn
    (nonempty_Icc.2 (zero_le)) hw.continuousOn
  refine ⟨-w u₀ + 1, t + 1, y, hy0, hry, t, by linarith, hd, fun u hu => ?_⟩
  have := hmin (show u ∈ Icc (0 : ℝ≥0) t from ⟨zero_le, hu⟩)
  simp only [mem_ofPred_eq] at this
  linarith

/-! ### Brownian scaling -/

section Dilation

variable {c : ℝ≥0}

theorem rWin_dilPath_of (hc : c ≠ 0) {M N r : ℝ} {w : ℝ≥0 → ℝ} (h : RWin (√(c : ℝ) * M) (c * N) r w) :
    RWin M N ((√(c : ℝ))⁻¹ * r) (dilPath c w) := by
  obtain ⟨y, hy0, hry, t, htN, hd, hlow⟩ := h
  have hc0 : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < √(c : ℝ) := Real.sqrt_pos.2 hc0
  have hsi : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 hs
  refine ⟨(√(c : ℝ))⁻¹ * y, mul_pos hsi hy0, mul_lt_mul_of_pos_left hry hsi, c⁻¹ * t, ?_, ?_, ?_⟩
  · rw [NNReal.coe_mul, NNReal.coe_inv, inv_mul_lt_iff₀ hc0]
    exact htN
  · have h1 := LP4HB.isSwallowedBy_dilPath_of hc hd
    have e1 : y / √(c : ℝ) = (√(c : ℝ))⁻¹ * y := by ring
    have e2 : (t : ℝ) / c = ((c⁻¹ * t : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_mul, NNReal.coe_inv]; ring
    rw [e1, e2] at h1
    exact h1
  · intro u hu
    have hcu : c * u ≤ t := by
      calc c * u ≤ c * (c⁻¹ * t) := mul_le_mul_right hu c
        _ = t := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    have h1 := hlow (c * u) hcu
    show -M < (√(c : ℝ))⁻¹ * w (c * u)
    have h2 : -(√(c : ℝ) * M) * (√(c : ℝ))⁻¹ < w (c * u) * (√(c : ℝ))⁻¹ :=
      mul_lt_mul_of_pos_right h1 hsi
    have e : -(√(c : ℝ) * M) * (√(c : ℝ))⁻¹ = -M := by field_simp
    rw [e] at h2
    linarith

/-- **Scaling of the windowed event.** -/
theorem rWin_dilPath_iff (hc : c ≠ 0) {M N r : ℝ} {w : ℝ≥0 → ℝ} :
    RWin M N ((√(c : ℝ))⁻¹ * r) (dilPath c w) ↔ RWin (√(c : ℝ) * M) (c * N) r w := by
  refine ⟨fun h => ?_, rWin_dilPath_of hc⟩
  have hc0 : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < √(c : ℝ) := Real.sqrt_pos.2 hc0
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hsq : √((c⁻¹ : ℝ≥0) : ℝ) = (√(c : ℝ))⁻¹ := by rw [NNReal.coe_inv, Real.sqrt_inv]
  have h' : RWin (√((c⁻¹ : ℝ≥0) : ℝ) * (√(c : ℝ) * M)) ((c⁻¹ : ℝ≥0) * (c * N))
      ((√(c : ℝ))⁻¹ * r) (dilPath c w) := by
    have e1 : √((c⁻¹ : ℝ≥0) : ℝ) * (√(c : ℝ) * M) = M := by rw [hsq]; field_simp
    have e2 : ((c⁻¹ : ℝ≥0) : ℝ) * (c * N) = N := by rw [NNReal.coe_inv]; field_simp
    rw [e1, e2]; exact h
  have h2 := rWin_dilPath_of hci h'
  rw [dilPath_inv_dilPath hc, hsq, inv_inv, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at h2
  exact h2

/-- **Scaling of the swallowing event.** -/
theorem rAll_dilPath_iff (hc : c ≠ 0) {r : ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous w) :
    RAll ((√(c : ℝ))⁻¹ * r) (dilPath c w) ↔ RAll r w := by
  have hc0 : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < √(c : ℝ) := Real.sqrt_pos.2 hc0
  rw [rAll_iff_exists_rWin (continuous_dilPath w hw), rAll_iff_exists_rWin hw]
  constructor
  · rintro ⟨M, N, h⟩
    exact ⟨_, _, (rWin_dilPath_iff hc).1 h⟩
  · rintro ⟨M, N, h⟩
    refine ⟨(√(c : ℝ))⁻¹ * M, (c : ℝ)⁻¹ * N, (rWin_dilPath_iff hc).2 ?_⟩
    have e1 : √(c : ℝ) * ((√(c : ℝ))⁻¹ * M) = M := by field_simp
    have e2 : (c : ℝ) * ((c : ℝ)⁻¹ * N) = N := by field_simp
    rw [e1, e2]; exact h

end Dilation

/-! ### The rational forms -/

/-- A closed lower bound at the rational times `≤ t` holds at every time `≤ t`. -/
theorem forall_le_of_forall_rat {w : ℝ≥0 → ℝ} (hw : Continuous w) {t : ℚ≥0} {a : ℝ}
    (h : ∀ u : ℚ≥0, u ≤ t → a ≤ w u) : ∀ u : ℝ≥0, u ≤ (t : ℝ≥0) → a ≤ w u := by
  intro u hu
  by_contra hlt
  push Not at hlt
  rcases hu.lt_or_eq with hut | hut
  · obtain ⟨δ, hδ, hδw⟩ := Metric.continuous_iff.1 hw u (a - w u) (by linarith)
    have hu' : (u : ℝ) < ((t : ℝ≥0) : ℝ) := hut
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (show (u : ℝ) < u + δ by linarith) hu')
    have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast (u.coe_nonneg.trans hq1.le)
    set q' : ℚ≥0 := ⟨q, hq0⟩ with hq'
    have hq'r : (((q' : ℚ≥0) : ℝ≥0) : ℝ) = (q : ℝ) := rfl
    have hq't : q' ≤ t := by
      have h1 : ((q' : ℚ≥0) : ℝ≥0) ≤ (t : ℝ≥0) := by
        rw [← NNReal.coe_le_coe, hq'r]; exact (hq2.trans_le (min_le_right _ _)).le
      exact_mod_cast h1
    have hdist : dist ((q' : ℚ≥0) : ℝ≥0) u < δ := by
      rw [NNReal.dist_eq, hq'r, abs_lt]
      constructor <;> linarith [hq2.trans_le (min_le_left _ _)]
    have h1 := hδw _ hdist
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h q' hq't]
  · rw [hut] at hlt
    linarith [h t le_rfl]

/-- **The windowed swallowing event, rational form** (for words with one right mark): a positive rational point
`q > r` (`r` the right mark of the start) is swallowed by a rational time `t < N` before the lifetime, and the
driver stays above `−M + 1/(k + 1)` at the rational times `≤ t`. -/
def SwalWin (M N : ℝ) {nL : ℕ} (s : (Fin nL → ℝ) × (Fin 1 → ℝ)) (w : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  ∃ (q : {q : ℚ // (0 : ℝ) < q}) (t : ℚ≥0) (k : ℕ), s.2 0 < ((q : ℚ) : ℝ) ∧ ((t : ℝ≥0) : ℝ≥0∞) < τ ∧
    ((t : ℝ≥0) : ℝ) < N ∧ LP3.stopPath (t : ℝ≥0) w ∉ LP3.aliveSet 1 ((q : ℚ) : ℝ) q.2 (t : ℝ≥0) ∧
    ∀ u : ℚ≥0, u ≤ t → -M + 1 / ((k : ℝ) + 1) ≤ w (u : ℝ≥0)

/-- **The swallowing event, rational form.** -/
def SwalAll {nL : ℕ} (s : (Fin nL → ℝ) × (Fin 1 → ℝ)) (w : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  ∃ n : ℕ, SwalWin n n s w τ

theorem swalWin_congr {M N : ℝ} {nL : ℕ} (s : (Fin nL → ℝ) × (Fin 1 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (hw : SwalWin M N s w τ) : SwalWin M N s w' τ := by
  obtain ⟨q, t, k, hq, htτ, htN, hal, hlow⟩ := hw
  have hst : LP3.stopPath (t : ℝ≥0) w = LP3.stopPath (t : ℝ≥0) w' := by
    funext r
    simp only [LP3.stopPath]
    exact h _ (lt_of_le_of_lt (by exact_mod_cast min_le_right r (t : ℝ≥0)) htτ)
  refine ⟨q, t, k, hq, htτ, htN, hst ▸ hal, fun u hu => ?_⟩
  rw [← h (u : ℝ≥0) (lt_of_le_of_lt (by exact_mod_cast hu) htτ)]
  exact hlow u hu

theorem swalAll_congr {nL : ℕ} (s : (Fin nL → ℝ) × (Fin 1 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (hw : SwalAll s w τ) : SwalAll s w' τ :=
  hw.imp fun _ hn => swalWin_congr s w w' τ h hn

/-- **The rational windowed event is the real one** for a continuous driver started at `0`, infinite lifetime. -/
theorem swalWin_top_iff {M N : ℝ} {nL : ℕ} {s : (Fin nL → ℝ) × (Fin 1 → ℝ)} {w : ℝ≥0 → ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) : SwalWin M N s w ⊤ ↔ RWin M N (s.2 0) w := by
  have hWc : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  constructor
  · rintro ⟨q, t, k, hq, -, htN, hal, hlow⟩
    rw [LP3.mem_aliveSet_iff (LP3.continuous_stopPath _ hw) (LP3.stopPath_zero _ hw0),
      LP3.alive_stopPath_iff, LP4HB.pathDrive_one] at hal
    refine ⟨(q : ℚ), q.2, hq, t, htN, hal, fun u hu => ?_⟩
    have := forall_le_of_forall_rat hw hlow u hu
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  · rintro ⟨y, hy0, hry, t, htN, hd, hlow⟩
    -- room after `t` for the lower bound
    obtain ⟨δ, hδ, hsub⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_cthickening_subset_open
      (isOpen_lt continuous_const hw) (fun u hu => hlow u hu.2)
    -- a rational time in `[t, t + δ) ∩ [0, N)`
    obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn (lt_min (show (t : ℝ) < t + δ by linarith) htN)
    have hq₁0 : (0 : ℚ) ≤ q₁ := by exact_mod_cast (t.coe_nonneg.trans hq₁a.le)
    set t' : ℚ≥0 := ⟨q₁, hq₁0⟩ with ht'
    have ht'r : (((t' : ℚ≥0) : ℝ≥0) : ℝ) = (q₁ : ℝ) := rfl
    have htt' : t ≤ ((t' : ℚ≥0) : ℝ≥0) := by rw [← NNReal.coe_le_coe, ht'r]; exact hq₁a.le
    have hmem : ∀ u : ℝ≥0, u ≤ ((t' : ℚ≥0) : ℝ≥0) → -M < w u := by
      intro u hu
      by_cases hut : u ≤ t
      · exact hlow u hut
      · push Not at hut
        refine hsub (Metric.mem_cthickening_of_dist_le u t δ _ ⟨zero_le, le_rfl⟩ ?_)
        rw [NNReal.dist_eq, abs_of_pos (sub_pos.2 (show (t : ℝ) < u from hut))]
        have : (u : ℝ) ≤ q₁ := by rw [← ht'r]; exact_mod_cast hu
        linarith [hq₁b.trans_le (min_le_left _ _)]
    -- the minimum on `[0, t']`
    obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := ((t' : ℚ≥0) : ℝ≥0))).exists_isMinOn
      (nonempty_Icc.2 (zero_le)) hw.continuousOn
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 (hmem u₀ hu₀.2))
    -- a rational point in `(max r 0, y)`
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hry hy0)
    have hq0 : (0 : ℝ) < q := (le_max_right _ _).trans_lt hq1
    refine ⟨⟨q, hq0⟩, t', k, (le_max_left _ _).trans_lt hq1, ENNReal.coe_lt_top, ?_, ?_, ?_⟩
    · rw [ht'r]; exact hq₁b.trans_le (min_le_right _ _)
    · rw [LP3.mem_aliveSet_iff (LP3.continuous_stopPath _ hw) (LP3.stopPath_zero _ hw0),
        LP3.alive_stopPath_iff, LP4HB.pathDrive_one]
      rintro ⟨v, hv⟩
      have hvt := QuantumZipper.isForwardSol_restrict hv t.coe_nonneg (by exact_mod_cast htt')
      exact hd (exists_isForwardSol_of_lt hWc t.coe_nonneg (by simpa [hw0] using hq0) hq2 hvt)
    · intro u hu
      have hu' : (u : ℝ≥0) ∈ Icc (0 : ℝ≥0) ((t' : ℚ≥0) : ℝ≥0) := ⟨zero_le, by exact_mod_cast hu⟩
      have := hmin hu'
      simp only [mem_ofPred_eq] at this
      linarith

/-- **The rational swallowing event is the real one** for a continuous driver started at `0`, infinite lifetime. -/
theorem swalAll_top_iff {nL : ℕ} {s : (Fin nL → ℝ) × (Fin 1 → ℝ)} {w : ℝ≥0 → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) : SwalAll s w ⊤ ↔ RAll (s.2 0) w := by
  rw [rAll_iff_exists_rWin hw]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, n, (swalWin_top_iff hw hw0).1 hn⟩
  · rintro ⟨M, N, h⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (max M N)
    exact ⟨n, (swalWin_top_iff hw hw0).2 (h.mono ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn))⟩

/-! ### Code sets -/

/-- The code set of the windowed event. -/
def winSet (M N : ℝ) {nL : ℕ} : Set (XCode nL 1) := {x | SwalWin M N (startOf x) (cw x) (cζ x)}

/-- The code set of the swallowing event. -/
def allSet {nL : ℕ} : Set (XCode nL 1) := {x | SwalAll (startOf x) (cw x) (cζ x)}

theorem measurable_swalWin (M N : ℝ) {nL : ℕ} :
    Measurable fun x : XCode nL 1 => SwalWin M N (startOf x) (cw x) (cζ x) := by
  have hcw : Measurable (cw : XCode nL 1 → ℝ≥0 → ℝ) := measurable_pi_iff.2 fun t => measurable_cw_at t
  unfold SwalWin
  refine Measurable.exists fun q => Measurable.exists fun t => Measurable.exists fun k => ?_
  refine Measurable.and (measurableSet_lt (measurable_startOf_snd 0) measurable_const).mem
    (Measurable.and (measurableSet_lt measurable_const measurable_cζ).mem
    (Measurable.and measurable_const (Measurable.and ?_ ?_)))
  · exact (((LP3.measurableSet_aliveSet _ _ _ _).compl).preimage
      ((LP3.measurable_stopPath _).comp hcw)).mem
  · exact Measurable.forall fun u => Measurable.imp measurable_const
      (measurableSet_le measurable_const (measurable_cw_at _)).mem

theorem measurableSet_winSet (M N : ℝ) {nL : ℕ} : MeasurableSet (winSet M N (nL := nL)) :=
  (measurable_swalWin M N).setOf

theorem measurableSet_allSet {nL : ℕ} : MeasurableSet (allSet (nL := nL)) :=
  (Measurable.exists fun n : ℕ => measurable_swalWin (nL := nL) (n : ℝ) (n : ℝ)).setOf

/-! ### Canonical laws: dilation and deletion of a zero-weight left mark -/

section Laws

variable {κ : ℝ} {nL : ℕ} {xL : Fin nL → ℝ} {xR : Fin 1 → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin 1 → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem measure_winSet_eq_codeLaw [IsProbabilityMeasure P] (hκ : 0 < κ) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (M N : ℝ) :
    P {ω | SwalWin M N (xL, xR) (fun t => W t ω) (ζ ω)} = codeLaw κ ρL ρR (winSet M N) (xL, xR) :=
  ZhanGT4.measure_eventOf_eq_codeLawS hκ hsep hE (measurableSet_winSet M N) (fun _ _ _ => Iff.rfl)
    (fun s w w' τ h hw => swalWin_congr s w w' τ h hw)

theorem measure_allSet_eq_codeLaw [IsProbabilityMeasure P] (hκ : 0 < κ) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    P {ω | SwalAll (xL, xR) (fun t => W t ω) (ζ ω)} = codeLaw κ ρL ρR allSet (xL, xR) :=
  ZhanGT4.measure_eventOf_eq_codeLawS hκ hsep hE measurableSet_allSet (fun _ _ _ => Iff.rfl)
    (fun s w w' τ h hw => swalAll_congr s w w' τ h hw)

/-- **Dilation of the windowed canonical probability.** -/
theorem codeLaw_winSet_dilate [IsProbabilityMeasure P] (hκ : 0 < κ) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {c : ℝ≥0} (hc : c ≠ 0) (M N : ℝ) :
    codeLaw κ ρL ρR (winSet M N) ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) =
      codeLaw κ ρL ρR (winSet (√(c : ℝ) * M) (c * N)) (xL, xR) := by
  have hc0 : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc0)
  have hsep' : ∀ i j, (√(c : ℝ))⁻¹ * xL i < (√(c : ℝ))⁻¹ * xR j := fun i j =>
    mul_lt_mul_of_pos_left (hsep i j) hs
  rw [← measure_winSet_eq_codeLaw hκ hsep' (hE.dilate hc), ← measure_winSet_eq_codeLaw hκ hsep hE]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp
  rw [hζω] at hp
  obtain ⟨hwc, hw0⟩ := Sec7.IsIntegratedSLEPath.continuous_w_of_top hp
  show SwalWin M N _ (dilPath c fun t => W t ω) (ζ ω / c) ↔
    SwalWin (√(c : ℝ) * M) (c * N) (xL, xR) (fun t => W t ω) (ζ ω)
  rw [hζω, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top, swalWin_top_iff (continuous_dilPath _ hwc)
    (dilPath_zero hw0), swalWin_top_iff hwc hw0]
  exact rWin_dilPath_iff hc

/-- **Dilation invariance of the swallowing canonical probability.** -/
theorem codeLaw_allSet_dilate [IsProbabilityMeasure P] (hκ : 0 < κ) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {c : ℝ≥0} (hc : c ≠ 0) :
    codeLaw κ ρL ρR allSet ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) =
      codeLaw κ ρL ρR allSet (xL, xR) := by
  have hc0 : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc0)
  have hsep' : ∀ i j, (√(c : ℝ))⁻¹ * xL i < (√(c : ℝ))⁻¹ * xR j := fun i j =>
    mul_lt_mul_of_pos_left (hsep i j) hs
  rw [← measure_allSet_eq_codeLaw hκ hsep' (hE.dilate hc), ← measure_allSet_eq_codeLaw hκ hsep hE]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp
  rw [hζω] at hp
  obtain ⟨hwc, hw0⟩ := Sec7.IsIntegratedSLEPath.continuous_w_of_top hp
  show SwalAll _ (dilPath c fun t => W t ω) (ζ ω / c) ↔ SwalAll (xL, xR) (fun t => W t ω) (ζ ω)
  rw [hζω, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top, swalAll_top_iff (continuous_dilPath _ hwc)
    (dilPath_zero hw0), swalAll_top_iff hwc hw0]
  exact rAll_dilPath_iff hc hwc

end Laws

section Zero

variable {κ : ℝ}

/-- An evolution of the word with a zero-weight left mark at `−L` and a right mark at `R`, and the one-force evolution
obtained by deleting the left mark (same driver, same lifetime). -/
theorem exists_zeroLeft (hκ : 0 < κ) {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (ρ : ℝ) (x0 ρ0 : Fin 0 → ℝ) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ (fun _ => -L) (fun _ => R) (fun _ => 0) (fun _ => ρ) P 𝓕 W VL VR B ζ ∧
      IsIntegratedSLEEvolution κ x0 (fun _ => R) ρ0 (fun _ => ρ) P 𝓕 W (fun j => VL (Fin.elim0 j)) VR B ζ := by
  have hF : IsOrderedForceWord (fun _ : Fin 1 => -L) (fun _ : Fin 1 => R) :=
    ⟨antitone_const, fun _ => by linarith, monotone_const, fun _ => hR⟩
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := fun _ => (0 : ℝ)) (ρR := fun _ => ρ)
  have hD := hE.compEmb (OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1)
    (RelEmbedding.refl (· ≤ ·) : Fin 1 ↪o Fin 1) (fun _ _ => rfl) (fun i hi => absurd ⟨i, rfl⟩ hi)
  obtain rfl : x0 = fun j => (fun _ : Fin 1 => -L) ((OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1) j) :=
    Subsingleton.elim _ _
  obtain rfl : ρ0 = fun j => (fun _ : Fin 1 => (0 : ℝ)) ((OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1) j) :=
    Subsingleton.elim _ _
  have e : (fun j => VL ((OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1) j)) = fun j => VL (Fin.elim0 j) :=
    Subsingleton.elim _ _
  rw [e] at hD
  exact ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, hD⟩

/-- **A zero-weight left mark does not change the windowed canonical probability.** -/
theorem codeLaw_winSet_zero (hκ : 0 < κ) {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (ρ M N : ℝ) (x0 ρ0 : Fin 0 → ℝ) :
    codeLaw κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => ρ) (winSet M N) ((fun _ => -L), fun _ => R) =
      codeLaw κ ρ0 (fun _ : Fin 1 => ρ) (winSet M N) (x0, fun _ => R) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, hD⟩ := exists_zeroLeft hκ hL hR ρ x0 ρ0
  rw [← measure_winSet_eq_codeLaw hκ (fun _ _ => by linarith) hE,
    ← measure_winSet_eq_codeLaw hκ (fun i => i.elim0) hD]
  rfl

/-- **A zero-weight left mark does not change the swallowing canonical probability.** -/
theorem codeLaw_allSet_zero (hκ : 0 < κ) {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (ρ : ℝ) (x0 ρ0 : Fin 0 → ℝ) :
    codeLaw κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => ρ) allSet ((fun _ => -L), fun _ => R) =
      codeLaw κ ρ0 (fun _ : Fin 1 => ρ) allSet (x0, fun _ => R) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, hD⟩ := exists_zeroLeft hκ hL hR ρ x0 ρ0
  rw [← measure_allSet_eq_codeLaw hκ (fun _ _ => by linarith) hE,
    ← measure_allSet_eq_codeLaw hκ (fun i => i.elim0) hD]
  rfl

end Zero

end InteractingSLE.LP.LP4S
