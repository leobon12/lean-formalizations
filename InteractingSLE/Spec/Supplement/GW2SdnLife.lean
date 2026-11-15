/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdzLife
import InteractingSLE.Spec.Supplement.GW2RdGauge
import InteractingSLE.Spec.Supplement.GW2BiCap

/-!
# Review defect N4, item 1: the death gauge along relative coordinates

Packet PROVE-GW2-SDE (round 13). The cap gauge of `GW2Sdz.exists_schedVersionsA_mono_gauge` for the candidate's death:
the distance of GB6's physical trace reader to a closed set `F` (D10's bad set), read after the stage start
`A = timeCapRule s T` and normalized by its value at `A`.

* `startDist s F A`: the distance read AT the path-rule time `A`, as a Borel causal functional (the supremum over
  shrinking rational windows `[A − 1/(m+1), A]` of the infimum of `min 1 dist`); **`startDist_eq`**: it is
  `min 1 (dist at A)` whenever the reading is continuous up to `A`;
* `deathGauge s F A`: `1` before `A`; from `A` on, `min 1 (dist / startDist)` (and `1` if `startDist = 0`);
  **`isCausal_deathGauge`**, **`measurable_deathGauge`**, **`deathGauge_nonneg`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Sdn

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId GW2Sdz

section Gauge

variable (s : ℝ≥0) (F : Set ℂ) (A : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞)

/-- The window term: `min 1 dist` at the rational time `q` if `q ∈ [A − 1/(m+1), A]`, else `1`. -/
def winTerm (m : ℕ) (q : ℚ≥0) (p : RecData × (ℝ≥0 → ℝ)) : ℝ :=
  if ((q : ℝ≥0) : ℝ≥0∞) ≤ A p ∧ A p ≤ (((q : ℝ≥0) + ((m : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞) then
    min 1 (traceDist s F q p) else 1

/-- **The distance read at the path-rule time `A`** (as a Borel causal functional). -/
def startDist (p : RecData × (ℝ≥0 → ℝ)) : ℝ :=
  ⨆ m : ℕ, ⨅ q : ℚ≥0, winTerm s F A m q p

/-- **The death gauge**: `1` before `A`; from `A` on, `min 1 (dist / startDist)` (`1` if `startDist = 0`). -/
def deathGauge : GaugeReadout := fun t p =>
  if A p ≤ (t : ℝ≥0∞) then
    (if startDist s F A p = 0 then 1 else min 1 (traceDist s F t p / startDist s F A p)) else 1

variable {s F A}

theorem winTerm_nonneg (m : ℕ) (q : ℚ≥0) (p : RecData × (ℝ≥0 → ℝ)) : 0 ≤ winTerm s F A m q p := by
  unfold winTerm
  split_ifs
  · exact le_min zero_le_one Metric.infDist_nonneg
  · exact zero_le_one

theorem winTerm_le_one (m : ℕ) (q : ℚ≥0) (p : RecData × (ℝ≥0 → ℝ)) : winTerm s F A m q p ≤ 1 := by
  unfold winTerm
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem iInf_winTerm_nonneg (m : ℕ) (p : RecData × (ℝ≥0 → ℝ)) : 0 ≤ ⨅ q : ℚ≥0, winTerm s F A m q p :=
  le_ciInf fun q => winTerm_nonneg m q p

theorem iInf_winTerm_le_one (m : ℕ) (p : RecData × (ℝ≥0 → ℝ)) : ⨅ q : ℚ≥0, winTerm s F A m q p ≤ 1 :=
  (ciInf_le ⟨0, by rintro _ ⟨q, rfl⟩; exact winTerm_nonneg m q p⟩ 0).trans (winTerm_le_one m 0 p)

theorem bddAbove_iInf_winTerm (p : RecData × (ℝ≥0 → ℝ)) :
    BddAbove (range fun m : ℕ => ⨅ q : ℚ≥0, winTerm s F A m q p) :=
  ⟨1, by rintro _ ⟨m, rfl⟩; exact iInf_winTerm_le_one m p⟩

theorem startDist_nonneg (p : RecData × (ℝ≥0 → ℝ)) : 0 ≤ startDist s F A p :=
  (iInf_winTerm_nonneg 0 p).trans (le_ciSup (bddAbove_iInf_winTerm p) 0)

theorem deathGauge_nonneg (t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : 0 ≤ deathGauge s F A t p := by
  unfold deathGauge
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (div_nonneg Metric.infDist_nonneg (startDist_nonneg p))
  · exact zero_le_one

theorem measurable_winTerm (hAm : Measurable A) (m : ℕ) (q : ℚ≥0) : Measurable (winTerm s F A m q) := by
  unfold winTerm
  refine Measurable.ite ?_ (measurable_const.min (measurable_traceDist s F _)) measurable_const
  exact (measurableSet_le measurable_const hAm).inter (measurableSet_le hAm measurable_const)

theorem measurable_startDist (hAm : Measurable A) : Measurable (startDist s F A) :=
  Measurable.iSup fun m => Measurable.iInf fun q => measurable_winTerm hAm m q

/-- **The death gauge is Borel.** -/
theorem measurable_deathGauge (hAm : Measurable A) (t : ℝ≥0) : Measurable (deathGauge s F A t) := by
  unfold deathGauge
  refine Measurable.ite (measurableSet_le hAm measurable_const) ?_ measurable_const
  refine Measurable.ite ((measurable_startDist hAm) (measurableSet_singleton 0)) measurable_const ?_
  exact measurable_const.min ((measurable_traceDist s F t).div (measurable_startDist hAm))

/-- A window term is decided by the path up to any time after `A`. -/
theorem winTerm_congr (hA : IsPathRule A) {r : RecData} {w w' : ℝ≥0 → ℝ} {t : ℝ≥0}
    (h : ∀ u ≤ t, w u = w' u) (hle : A (r, w) ≤ t) (m : ℕ) (q : ℚ≥0) :
    winTerm s F A m q (r, w') = winTerm s F A m q (r, w) := by
  have hAe := GW2Bh.pathRule_eq_of_le hA h hle
  unfold winTerm
  rw [hAe]
  split_ifs with hq
  · have hqt : q ≤ t := ENNReal.coe_le_coe.1 (hq.1.trans hle)
    rw [isCausal_traceDist s F q r w w' fun u hu => h u (hu.trans hqt)]
  · rfl

/-- The reading at `A` is decided by the path up to any time after `A`. -/
theorem startDist_congr (hA : IsPathRule A) {r : RecData} {w w' : ℝ≥0 → ℝ} {t : ℝ≥0}
    (h : ∀ u ≤ t, w u = w' u) (hle : A (r, w) ≤ t) : startDist s F A (r, w') = startDist s F A (r, w) := by
  unfold startDist
  simp only [winTerm_congr hA h hle]

/-- **The death gauge is causal.** -/
theorem isCausal_deathGauge (hA : IsPathRule A) : IsCausal (deathGauge s F A) := by
  intro t r w w' h
  unfold deathGauge
  by_cases hle : A (r, w) ≤ (t : ℝ≥0∞)
  · have hle' : A (r, w') ≤ (t : ℝ≥0∞) := (GW2Bh.pathRule_le_iff hA h).1 hle
    simp only [hle, hle', ↓reduceIte, startDist_congr hA h hle, isCausal_traceDist s F t r w w' h]
  · have hle' : ¬ A (r, w') ≤ (t : ℝ≥0∞) := fun h' => hle ((GW2Bh.pathRule_le_iff hA h).2 h')
    simp only [hle, hle', ↓reduceIte]

/-- **The reading at `A` is the distance at `A`** whenever the distance is continuous up to `A`. -/
theorem startDist_eq {p : RecData × (ℝ≥0 → ℝ)} {a : ℝ≥0} (hA : A p = a)
    (hg : ContinuousOn (fun u => traceDist s F u p) (Iic a)) :
    startDist s F A p = min 1 (traceDist s F a p) := by
  set g : ℝ≥0 → ℝ := fun u => min 1 (traceDist s F u p) with hgdef
  have hgc : ContinuousOn g (Iic a) := continuous_min.comp_continuousOn (continuousOn_const.prodMk hg)
  have hga : ContinuousWithinAt g (Iic a) a := hgc a Set.self_mem_Iic
  have hwin : ∀ m (q : ℚ≥0), winTerm s F A m q p =
      if (q : ℝ≥0) ≤ a ∧ a ≤ (q : ℝ≥0) + ((m : ℝ≥0) + 1)⁻¹ then g q else 1 := by
    intro m q
    simp only [winTerm, hA, ENNReal.coe_le_coe, hgdef]
  have hbddB : ∀ m, BddBelow (range fun q : ℚ≥0 => winTerm s F A m q p) := fun m =>
    ⟨0, by rintro _ ⟨q, rfl⟩; exact winTerm_nonneg m q p⟩
  -- every window infimum is at most `g a`
  have hle : ∀ m, ⨅ q : ℚ≥0, winTerm s F A m q p ≤ g a := by
    intro m
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.1 hga ε hε
    set η : ℝ := min δ ((m : ℝ) + 1)⁻¹ with hη
    have hη0 : 0 < η := lt_min hδ (by positivity)
    -- a rational point of `[a − η, a]`
    obtain ⟨q, hqa', hqlt⟩ : ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ) ≤ a ∧ (a : ℝ) - η < ((q : ℝ≥0) : ℝ) := by
      by_cases ha0 : (a : ℝ) - η < 0
      · refine ⟨0, ?_, ?_⟩
        · change ((0 : ℚ≥0) : ℝ) ≤ a
          simp
        · change (a : ℝ) - η < ((0 : ℚ≥0) : ℝ)
          simpa using ha0
      · have ha0' : 0 ≤ (a : ℝ) - η := not_lt.1 ha0
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (a : ℝ) - η < a by linarith)
        have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast ha0'.trans hq1.le
        let q' : ℚ≥0 := ⟨q, hq0⟩
        have hq' : ((q' : ℝ≥0) : ℝ) = (q : ℝ) := rfl
        exact ⟨q', by rw [hq']; exact hq2.le, by rw [hq']; exact hq1⟩
    have hqin : (q : ℝ≥0) ≤ a ∧ a ≤ (q : ℝ≥0) + ((m : ℝ≥0) + 1)⁻¹ := by
      refine ⟨by exact_mod_cast hqa', ?_⟩
      rw [← NNReal.coe_le_coe]
      push_cast
      have : (a : ℝ) - ((m : ℝ) + 1)⁻¹ ≤ (a : ℝ) - η := by linarith [min_le_right δ ((m : ℝ) + 1)⁻¹]
      have hq' : (a : ℝ) - η < ((q : ℝ≥0) : ℝ) := hqlt
      linarith
    have hterm : winTerm s F A m q p = g q := by rw [hwin]; exact ite_eq_left_iff.2 fun h => absurd hqin h
    have hdist : dist (q : ℝ≥0) a < δ := by
      rw [NNReal.dist_eq, abs_sub_lt_iff]
      have hq' : (a : ℝ) - η < ((q : ℝ≥0) : ℝ) := hqlt
      constructor <;> linarith [min_le_left δ ((m : ℝ) + 1)⁻¹]
    have hgq := hδg (show (q : ℝ≥0) ∈ Iic a from hqin.1) hdist
    rw [Real.dist_eq, abs_sub_lt_iff] at hgq
    calc ⨅ q : ℚ≥0, winTerm s F A m q p ≤ winTerm s F A m q p := ciInf_le (hbddB m) q
      _ = g q := hterm
      _ < g a + ε := by linarith [hgq.1]
  -- for every ε, a late window infimum is at least `g a − ε`
  have hge : ∀ ε > 0, ∃ m, g a - ε ≤ ⨅ q : ℚ≥0, winTerm s F A m q p := by
    intro ε hε
    obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.1 hga ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, le_ciInf fun q => ?_⟩
    rw [hwin]
    split_ifs with hq
    · have hdist : dist (q : ℝ≥0) a < δ := by
        rw [NNReal.dist_eq, abs_sub_lt_iff]
        have h1 : ((q : ℝ≥0) : ℝ) ≤ a := by exact_mod_cast hq.1
        have h2 : (a : ℝ) ≤ ((q : ℝ≥0) : ℝ) + ((m : ℝ) + 1)⁻¹ := by exact_mod_cast hq.2
        have h3 : ((m : ℝ) + 1)⁻¹ = 1 / ((m : ℝ) + 1) := by rw [one_div]
        constructor <;> linarith
      have hgq := hδg (show (q : ℝ≥0) ∈ Iic a from hq.1) hdist
      rw [Real.dist_eq, abs_sub_lt_iff] at hgq
      linarith [hgq.2]
    · have : g a ≤ 1 := min_le_left _ _
      linarith
  refine le_antisymm (ciSup_le hle) ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨m, hm⟩ := hge ε hε
  have hsd : startDist s F A p = ⨆ m : ℕ, ⨅ q : ℚ≥0, winTerm s F A m q p := rfl
  have := hm.trans (le_ciSup (bddAbove_iInf_winTerm p) m)
  change g a ≤ startDist s F A p + ε
  rw [hsd]
  linarith

end Gauge

/-! ### The death gauge along relative coordinates (item 1) -/

/-- The entrance set of a curve into `F` at or after `T`. -/
def entrySet (γ : ℝ≥0 → ℂ) (F : Set ℂ) (T : ℝ≥0) : Set ℝ≥0 := {τ | T ≤ τ ∧ γ τ ∈ F}

theorem isClosed_entrySet {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {F : Set ℂ} (hF : IsClosed F) (T : ℝ≥0) :
    IsClosed (entrySet γ F T) :=
  isClosed_Ici.inter (hF.preimage hγ)

open Classical in
/-- **The life of the death gauge**: the relative clock of the explored curve's first entrance into `F` after `T`,
when the curve is outside `F` at `T` and enters `F` before contact; `⊤` otherwise. -/
def lifeClock {Ω : Type*} (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (γ α : Ω → ℝ≥0 → ℂ) (F : Set ℂ) (T : ℝ≥0) (ω : Ω) :
    ℝ≥0∞ :=
  if γ ω T ∉ F ∧ ∃ τ ∈ entrySet (γ ω) F T, (τ : ℝ≥0∞) < gb6Tc s γ α ω then
    ENNReal.ofReal (gb6Clock s W Wα ω (sInf (entrySet (γ ω) F T))) else ⊤

section Coord

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
  {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}

/-- **Item 1: the death gauge along every relative coordinate.** Almost surely on the record event, the death gauge of
a closed set `F` after the stage start `timeCapRule s T` is continuous before the coordinates' life, positive before
`lifeClock` (the relative clock of the explored curve's first entrance into `F` after `T`), and zero there. -/
theorem ae_deathGauge_coord (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (s : ℝ≥0) (hs0 : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L)
    {F : Set ℂ} (hFc : IsClosed F) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → 0 < lifeClock s W Wα γ α F T ω ∧
      ContinuousOn (fun t => deathGauge s F (GW2Rd.timeCapRule s T) t (gb6Rec s Wα ζα ω, fun u => D u ω))
        {t | (t : ℝ≥0∞) < L ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < lifeClock s W Wα γ α F T ω →
        0 < deathGauge s F (GW2Rd.timeCapRule s T) t (gb6Rec s Wα ζα ω, fun u => D u ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = lifeClock s W Wα γ α F T ω →
        deathGauge s F (GW2Rd.timeCapRule s T) t (gb6Rec s Wα ζα ω, fun u => D u ω) = 0 := by
  classical
  filter_upwards [GW2Rd.ae_physicalReadback_nr hF hα hNR hW s hs0 hC,
    GW2Rd.ae_separationRead_regular_nr hF hα hNR hW s hs0 hC, GW2Bh.ae_timeCapRule_coord hF hα hW hC,
    GW2Bh.ae_min_timeCapRule_coord hF hα hW hC, ae_gb6RecGood hF hα s, hC.relative, hW]
    with ω hread hreg hcapR hminR hgood hrel hWω hrec
  obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hgood).2 hrec
  obtain ⟨-, ham, -, hat, hcapacity⟩ := hread hs hsH
  have hXc := (hreg hrec).2.2.2.2
  obtain ⟨-, hhull⟩ := hrel hs hsH
  have hγc : Continuous (γ ω) := by
    have hc := hWω.2.2.2.1
    simp only [le_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  set p : RecData × (ℝ≥0 → ℝ) := (gb6Rec s Wα ζα ω, fun u => D u ω) with hp
  set A := GW2Rd.timeCapRule s (T : ℝ≥0∞) with hAdef
  set f : ℝ≥0 → ℝ := fun u => traceDist s F u p with hfdef
  have hfc : ContinuousOn f {u | (u : ℝ≥0∞) < L ω} :=
    (Metric.continuous_infDist_pt F).comp_continuousOn hXc
  by_cases hT : (T : ℝ≥0∞) < gb6Tc s γ α ω
  swap
  · -- contact before `T`: the gauge is `1` before the life, and the life clock is `⊤`
    have hAL : L ω ≤ A p := by
      have hm := hminR hrec T
      simp only [GW2Rd.capClock, hT, ↓reduceIte, min_top_right] at hm
      exact min_eq_left_iff.1 hm
    have hLz : lifeClock s W Wα γ α F T ω = ⊤ := by
      unfold lifeClock
      refine ite_eq_right_iff.2 fun hc => absurd ?_ hT
      obtain ⟨-, τ, hτ, hτT⟩ := hc
      exact (ENNReal.coe_le_coe.2 hτ.1).trans_lt hτT
    have hG1 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → deathGauge s F A t p = 1 := fun t ht => by
      simp only [deathGauge, not_le.2 (ht.trans_le hAL), ↓reduceIte]
    refine ⟨by rw [hLz]; exact ENNReal.zero_lt_top, continuousOn_const.congr fun t ht => hG1 t ht,
      fun t ht _ => by rw [hG1 t ht]; exact one_pos, fun t _ ht => absurd (ht.trans hLz) ENNReal.coe_ne_top⟩
  -- `T` before contact
  have hclkT0 : 0 ≤ gb6Clock s W Wα ω T := (hhull T hT).1
  set a : ℝ≥0 := (gb6Clock s W Wα ω T).toNNReal with ha
  have hAa : A p = (a : ℝ≥0∞) := hcapR hrec T hT
  have haL : (a : ℝ≥0∞) < L ω := (hhull T hT).2.1
  have hXa : ReadD.physicalTrace s a p = γ ω T := hat T hT
  have hfa : f a = Metric.infDist (γ ω T) F := by simp only [hfdef, traceDist, hXa]
  have hsd : startDist s F A p = min 1 (Metric.infDist (γ ω T) F) := by
    rw [startDist_eq hAa (hfc.mono fun u hu => (ENNReal.coe_le_coe.2 hu).trans_lt haL)]
    change min 1 (f a) = _
    rw [hfa]
  -- the readback of every relative time below the life
  have hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → a ≤ u → ∃ t' : ℝ≥0, (t' : ℝ≥0∞) < gb6Tc s γ α ω ∧ T ≤ t' ∧
      gb6Clock s W Wα ω t' = u ∧ f u = Metric.infDist (γ ω t') F := by
    intro u hu hau
    obtain ⟨t', ht', hclk, hX⟩ := hcapacity u hu
    refine ⟨t', ht', ?_, hclk, by simp only [hfdef, traceDist, hX]⟩
    by_contra hlt
    have h1 := ham ht' hT (lt_of_not_ge hlt)
    rw [hclk] at h1
    have : (u : ℝ) < a := by rw [ha, Real.coe_toNNReal _ hclkT0]; exact h1
    exact absurd (NNReal.coe_le_coe.2 hau) (not_le.2 this)
  by_cases hsd0 : startDist s F A p = 0
  · -- the curve is in `F` at `T` (or `F` is empty): the gauge is `1`, the life clock is `⊤`
    have hG1 : ∀ t : ℝ≥0, deathGauge s F A t p = 1 := fun t => by
      unfold deathGauge
      split_ifs <;> rfl
    have hLz : lifeClock s W Wα γ α F T ω = ⊤ := by
      unfold lifeClock
      refine ite_eq_right_iff.2 fun hc => ?_
      obtain ⟨hγT, τ, hτ, -⟩ := hc
      have hpos : 0 < Metric.infDist (γ ω T) F := (hFc.notMem_iff_infDist_pos ⟨_, hτ.2⟩).1 hγT
      rw [hsd] at hsd0
      exact absurd hsd0 (lt_min one_pos hpos).ne'
    refine ⟨by rw [hLz]; exact ENNReal.zero_lt_top, continuousOn_const.congr fun t _ => hG1 t,
      fun t _ _ => by rw [hG1 t]; exact one_pos, fun t _ ht => absurd (ht.trans hLz) ENNReal.coe_ne_top⟩
  -- the curve is outside `F` at `T`
  have hsdpos : 0 < startDist s F A p := lt_of_le_of_ne (startDist_nonneg p) (Ne.symm hsd0)
  have hdistT : 0 < Metric.infDist (γ ω T) F := by
    rw [hsd] at hsdpos
    by_contra hle
    have : Metric.infDist (γ ω T) F = 0 := le_antisymm (not_lt.1 hle) Metric.infDist_nonneg
    rw [this, min_eq_right zero_le_one] at hsdpos
    exact lt_irrefl _ hsdpos
  have hγT : γ ω T ∉ F := fun hm => (Metric.infDist_zero_of_mem hm ▸ hdistT).false
  have hFne : F.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Metric.infDist_empty] at hdistT
    exact lt_irrefl _ hdistT
  -- the gauge before the life, in closed form
  have hrep : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω →
      deathGauge s F A t p = min 1 (f (max t a) / startDist s F A p) := by
    intro t ht
    unfold deathGauge
    by_cases hat' : a ≤ t
    · have hle : A p ≤ (t : ℝ≥0∞) := hAa ▸ ENNReal.coe_le_coe.2 hat'
      simp only [hle, hsd0, ↓reduceIte, max_eq_left hat']
      rfl
    · have hle : ¬ A p ≤ (t : ℝ≥0∞) := by rw [hAa]; exact fun h' => hat' (ENNReal.coe_le_coe.1 h')
      simp only [hle, ↓reduceIte, max_eq_right (le_of_lt (lt_of_not_ge hat'))]
      have h1 : 1 ≤ f a / startDist s F A p := by
        rw [le_div_iff₀ hsdpos, one_mul, hsd, hfa]
        exact min_le_right _ _
      exact (min_eq_left h1).symm
  have hcont : ContinuousOn (fun t => deathGauge s F A t p) {t | (t : ℝ≥0∞) < L ω} := by
    refine ContinuousOn.congr ?_ fun t ht => hrep t ht
    have hmax : ContinuousOn (fun t : ℝ≥0 => f (max t a)) {t | (t : ℝ≥0∞) < L ω} :=
      hfc.comp (continuous_id.max continuous_const).continuousOn fun t ht => by
        simp only [mem_ofPred_eq, ENNReal.coe_max]
        exact max_lt ht haL
    exact continuous_min.comp_continuousOn (continuousOn_const.prodMk (hmax.div_const _))
  -- positivity where the readback is outside `F`
  have hposOf : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → 0 < f (max t a) → 0 < deathGauge s F A t p := by
    intro t ht hf
    rw [hrep t ht]
    exact lt_min one_pos (div_pos hf hsdpos)
  by_cases hent : ∃ τ ∈ entrySet (γ ω) F T, (τ : ℝ≥0∞) < gb6Tc s γ α ω
  · obtain ⟨τ₀, hτ₀, hτ₀c⟩ := hent
    set τF := sInf (entrySet (γ ω) F T) with hτF
    have hmem : τF ∈ entrySet (γ ω) F T :=
      (isClosed_entrySet hγc hFc T).csInf_mem ⟨τ₀, hτ₀⟩ (OrderBot.bddBelow _)
    have hτFc : (τF : ℝ≥0∞) < gb6Tc s γ α ω :=
      (ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) hτ₀)).trans_lt hτ₀c
    have hTτ : T < τF := lt_of_le_of_ne hmem.1 fun he => hγT (he ▸ hmem.2)
    have hclk : gb6Clock s W Wα ω T < gb6Clock s W Wα ω τF := ham hT hτFc hTτ
    have hLz : lifeClock s W Wα γ α F T ω = ENNReal.ofReal (gb6Clock s W Wα ω τF) := by
      unfold lifeClock
      exact ite_eq_left_iff.2 fun hc => absurd ⟨hγT, τ₀, hτ₀, hτ₀c⟩ hc
    have haLz : (a : ℝ≥0∞) < ENNReal.ofReal (gb6Clock s W Wα ω τF) := by
      rw [ha]
      exact (ENNReal.ofReal_lt_ofReal_iff (hclkT0.trans_lt hclk)).2 hclk
    refine ⟨?_, hcont, fun t ht htz => ?_, fun t ht htz => ?_⟩
    · rw [hLz]
      exact ENNReal.ofReal_pos.2 (hclkT0.trans_lt hclk)
    · rw [hLz] at htz
      refine hposOf t ht ?_
      have hmL : ((max t a : ℝ≥0) : ℝ≥0∞) < L ω := by rw [ENNReal.coe_max]; exact max_lt ht haL
      obtain ⟨t', ht', hTt', hclk', hft'⟩ := hback _ hmL (le_max_right _ _)
      rw [hft']
      have hlt : t' < τF := by
        by_contra hge
        have h1 := ham.monotoneOn hτFc ht' (not_lt.1 hge)
        rw [hclk'] at h1
        have h2 : ((max t a : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal (gb6Clock s W Wα ω τF) := by
          rw [ENNReal.coe_max]; exact max_lt htz haLz
        have h3 : ENNReal.ofReal (gb6Clock s W Wα ω τF) ≤ ((max t a : ℝ≥0) : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal h1
        exact absurd h2 (not_lt.2 h3)
      have hγt' : γ ω t' ∉ F := fun hm =>
        absurd (csInf_le (OrderBot.bddBelow _) (show t' ∈ entrySet (γ ω) F T from ⟨hTt', hm⟩)) (not_le.2 hlt)
      exact (hFc.notMem_iff_infDist_pos hFne).1 hγt'
    · rw [hLz] at htz
      have htv : t = (gb6Clock s W Wα ω τF).toNNReal := by
        rw [← ENNReal.coe_inj]
        exact htz.trans rfl
      have hta : a ≤ t := by
        rw [htv, ha]
        exact Real.toNNReal_le_toNNReal hclk.le
      rw [hrep t ht, max_eq_left hta]
      have hXt : ReadD.physicalTrace s t p = γ ω τF := by rw [htv]; exact hat τF hτFc
      have hft : f t = 0 := by
        simp only [hfdef, traceDist, hXt]
        exact Metric.infDist_zero_of_mem hmem.2
      rw [hft, zero_div, min_eq_right zero_le_one]
  · have hLz : lifeClock s W Wα γ α F T ω = ⊤ := by
      unfold lifeClock
      exact ite_eq_right_iff.2 fun hc => absurd hc.2 hent
    refine ⟨by rw [hLz]; exact ENNReal.zero_lt_top, hcont, fun t ht _ => ?_,
      fun t _ ht => absurd (ht.trans hLz) ENNReal.coe_ne_top⟩
    refine hposOf t ht ?_
    have hmL : ((max t a : ℝ≥0) : ℝ≥0∞) < L ω := by rw [ENNReal.coe_max]; exact max_lt ht haL
    obtain ⟨t', ht', hTt', -, hft'⟩ := hback _ hmL (le_max_right _ _)
    rw [hft']
    have hγt' : γ ω t' ∉ F := fun hm => hent ⟨t', ⟨hTt', hm⟩, ht'⟩
    exact (hFc.notMem_iff_infDist_pos hFne).1 hγt'

end Coord

/-! ### D10's bad set -/

/-- **D10's bad real set** of the original data for a flow line of angle `θ` launched at `u`: the closure of the real
points beyond which the cumulative weight seen from `u` is at most `−2`. -/
def badSet (κ : ℝ) (b : ℝ → ℝ) (θ u : ℝ) : Set ℝ :=
  closure ({y | u < y ∧
      Sec4.cumWeightRight κ (PiecewiseConstantBoundaryData.rightLim b y + θ * QuantumZipper.chiC κ) ≤ -2} ∪
    {y | y < u ∧ Sec4.cumWeightLeft κ (PiecewiseConstantBoundaryData.leftLim b y + θ * QuantumZipper.chiC κ) ≤ -2})

/-- D10's bad set as a set of the plane. -/
def badSetC (κ : ℝ) (b : ℝ → ℝ) (θ u : ℝ) : Set ℂ := (fun y : ℝ => (y : ℂ)) '' badSet κ b θ u

/-- **D10's bad set is closed** (so it is an admissible set for `exists_schedVersionsA_mono_life`). -/
theorem isClosed_badSetC (κ : ℝ) (b : ℝ → ℝ) (θ u : ℝ) : IsClosed (badSetC κ b θ u) :=
  Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ isClosed_closure

/-! ### The schedule family capped strictly before the death -/

section Sched

open GW2TipSystem GW2TipSystem.RootC24 GW2Rd

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **The schedule instance's versions capped strictly before the death** (review defect N4, item 1): finite,
monotone, exhausting announced GB6 versions whose caps lie strictly below `lifeClock` — the relative clock of the
explored curve's first entrance into the closed set `F` after the stage start `RootJ31.historyTime c r l` — on the
record event, and which exhaust every clock below it before contact. With `F` D10's closed bad set of the candidate's
angle (`badSetC`) this is the cap `min (V n) (D n)` of D3a. -/
theorem exists_schedVersionsA_mono_life (hs : 0 < c.s) {F : Set ℂ} (hFc : IsClosed F) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n,
        V n ω < lifeClock c.s (schedW c r l a) c.W (schedTr c r l a) c.α F (RootJ31.historyTime c r l) ω) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) <
          lifeClock c.s (schedW c r l a) c.W (schedTr c r l a) c.α F (RootJ31.historyTime c r l) ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  have hW' : ∀ᵐ ω ∂c.P, Continuous (schedW c r l a · ω) ∧ schedW c r l a 0 ω = 0 ∧
      IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) :=
    (ae_schedW_regular h13 c r l a).mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  exact exists_schedVersionsA_mono_gauge h13 c r l a hs
    (measurable_deathGauge (measurable_timeCapRule c.s _)) (isCausal_deathGauge (isPathRule_timeCapRule c.s _))
    deathGauge_nonneg
    (fun D L hC => ae_deathGauge_coord hfl hα (ae_source_noReturn h13 c) hW' c.s hs hC hFc (RootJ31.historyTime c r l))

end Sched

end InteractingSLE.Theorem14.GW2Sdn
