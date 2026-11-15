/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3StopWire
import InteractingSLE.Spec.Supplement.GB6HullIdReadout

/-!
# The gauge-stop versions of GB6's relative exploration are announced

Packet PROVE-Q3-REL4 (step (D) for GB6). The exhausting versions built from the read-back coordinates
(`HullId.isGB6RelVersionR_coord`: the source driver frozen at `T = gaugeStop g ε (m + 1)`, the first time the
continuous gauge `g` reaches the level `ε = gaugeLevel (g 0) m`, capped at `m + 1`) are announced:

* `gaugeStop_mono`, `gaugeStop_lt_of_lt`, `exists_lt_gaugeStop`: a lower level reached before a smaller cap comes
  strictly earlier; every time before `T` is passed by the stops of levels decreasing to `ε` with caps increasing to
  `m + 1` (compactness of `[0, t]`);
* `isPathRule_min_const`, `isPathRule_finsetSup`: path rules are closed under capping by a constant and finite
  suprema;
* `annLevel`, `annCap`, `annRule`, `annRules`: the announcing rules `max_{k ≤ n} min(hitRule (level ε_k) (cap c_k),
  c_k)` with `ε_k = ε + (g 0 − ε)/(k + 2)` read from the record and `c_k = (m + 1)(k + 1)/(k + 2)`: measurable finite
  path rules, nondecreasing in `n`;
* **`isGB6RelVersionA_coord`**: the coordinate versions are announced versions (`IsGB6RelVersionA`);
* **`gb6RelVersionAStatement_of_readoutCoord`**, **`gb6HullDetStatement_of_liveReadout_relSafe`**: GB6's hull identity
  from PROVE-GB6-HULLID's read-back input (`HullId.GB6LiveReadoutStatement`) and the relative safe law
  (`GB6RelSafeStatement`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Supp8.Q3Stop

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC

/-! ### Gauge stops -/

section Gauge

variable {g : ℝ≥0 → ℝ}

/-- A lower level and a larger cap give a later stop. -/
theorem gaugeStop_mono (hg : Continuous g) {ε ε' : ℝ} {c c' : ℝ≥0} (hε : ε' ≤ ε) (hc : c ≤ c') :
    gaugeStop g ε c ≤ gaugeStop g ε' c' := by
  by_cases h : c ≤ gaugeStop g ε' c'
  · exact (gaugeStop_le g ε c).trans h
  · replace h := lt_of_not_ge h
    exact gaugeStop_le_of_le h.le ((gaugeStop_mem hg (h.trans_le hc)).trans hε)

/-- A strictly higher level (below the start) and a strictly smaller cap give a strictly earlier stop. -/
theorem gaugeStop_lt_of_lt (hg : Continuous g) {ε ε' : ℝ} {c c' : ℝ≥0} (hε : ε < ε') (h0 : ε' < g 0)
    (hc : c' < c) : gaugeStop g ε' c' < gaugeStop g ε c := by
  rcases (gaugeStop_le g ε c).lt_or_eq with hT | hT
  · have hgT : g (gaugeStop g ε c) ≤ ε := gaugeStop_mem hg hT
    obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ gaugeStop g ε c from zero_le)
      hg.continuousOn (show ε' ∈ Icc (g (gaugeStop g ε c)) (g 0) from ⟨by linarith, h0.le⟩)
    have huT : u < gaugeStop g ε c := lt_of_le_of_ne hu.2 fun he => by
      rw [he] at hgu
      linarith
    rcases le_total u c' with huc | hcu
    · exact (gaugeStop_le_of_le huc hgu.le).trans_lt huT
    · exact (gaugeStop_le g ε' c').trans_lt (hcu.trans_lt huT)
  · rw [hT]
    exact (gaugeStop_le g ε' c').trans_lt hc

/-- Every time before the stop is passed by the stops of levels decreasing to `ε` with caps increasing to `c`. -/
theorem exists_lt_gaugeStop (hg : Continuous g) {ε : ℝ} {c t : ℝ≥0} (ht : t < gaugeStop g ε c)
    {εs : ℕ → ℝ} {cs : ℕ → ℝ≥0} (hεs : ∀ δ > 0, ∃ N, ∀ n ≥ N, εs n < ε + δ)
    (hcs : ∀ t' < c, ∃ N, ∀ n ≥ N, t' < cs n) : ∃ n, t < gaugeStop g (εs n) (cs n) := by
  have hpos : ∀ u ≤ t, ε < g u := fun u hu => by
    by_contra hn
    replace hn := le_of_not_gt hn
    exact absurd ((gaugeStop_le_of_le (hu.trans (ht.le.trans (gaugeStop_le g ε c))) hn).trans hu)
      (not_le.2 ht)
  obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_isMinOn
    (nonempty_Icc.2 zero_le) hg.continuousOn
  have hδ : 0 < g u₀ - ε := sub_pos.2 (hpos u₀ hu₀.2)
  obtain ⟨N₁, hN₁⟩ := hεs _ hδ
  obtain ⟨N₂, hN₂⟩ := hcs t (ht.trans_le (gaugeStop_le g ε c))
  refine ⟨max N₁ N₂, ?_⟩
  have h1 := hN₁ _ (le_max_left N₁ N₂)
  have h2 := hN₂ _ (le_max_right N₁ N₂)
  by_contra hn
  replace hn := le_of_not_gt hn
  obtain ⟨u, hu, hgu⟩ := (gaugeStop_le_iff hg h2).1 hn
  have h3 := (isMinOn_iff.1 hmin) u ⟨zero_le, hu⟩
  linarith

end Gauge

/-! ### Path rules -/

theorem isPathRule_min_const {h : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hh : IsPathRule h) (c : ℝ≥0∞) :
    IsPathRule fun x => min (h x) c := by
  intro r w w' hag
  simp only at hag ⊢
  by_cases hc : h (r, w) ≤ c
  · have e : h (r, w') = h (r, w) := hh r w w' fun u hu => hag u (by rw [min_eq_left hc]; exact hu)
    simp only [e]
  · replace hc := lt_of_not_ge hc
    have hge : c ≤ h (r, w') := by
      by_contra hlt
      replace hlt := lt_of_not_ge hlt
      have e := hh r w' w fun u hu => (hag u (by rw [min_eq_right hc.le]; exact hu.trans hlt.le)).symm
      rw [e] at hc
      exact absurd hc (not_lt.2 hlt.le)
    simp only [min_eq_right hge, min_eq_right hc.le]

theorem isPathRule_finsetSup {f : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hf : ∀ k, IsPathRule (f k))
    (s : Finset ℕ) : IsPathRule fun x => s.sup fun k => f k x := by
  intro r w w' hag
  exact Finset.sup_congr rfl fun k hk => hf k r w w' fun u hu =>
    hag u (hu.trans (Finset.le_sup (f := fun k => f k (r, w)) hk))

/-! ### The announcing rules -/

/-- The announcing levels `ε + (g₀ − ε)/(k + 2)`, read from the record (`ε = recLevel G m r`, `g₀ = G 0 (r, 0)`). -/
def annLevel (G : GaugeReadout) (m k : ℕ) (r : RecData) : ℝ :=
  recLevel G m r + (G 0 (r, fun _ => 0) - recLevel G m r) / ((k : ℝ) + 2)

/-- The announcing caps `(m + 1)(k + 1)/(k + 2)`. -/
def annCap (m k : ℕ) : ℝ≥0 := ((m : ℝ≥0) + 1) * (((k : ℝ≥0) + 1) / ((k : ℝ≥0) + 2))

/-- One announcing rule: the prefix-test rule of the level `ε_k` and the cap `c_k`, capped at `c_k`. -/
def annRule (G : GaugeReadout) (m k : ℕ) (x : RecData × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  min (hitRule G (annLevel G m k) (annCap m k) x) (annCap m k)

/-- The announcing rules: running maxima of the `annRule`s. -/
def annRules (G : GaugeReadout) (m n : ℕ) (x : RecData × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  (Finset.range (n + 1)).sup fun k => annRule G m k x

theorem annCap_coe (m k : ℕ) : (annCap m k : ℝ) = ((m : ℝ) + 1) - ((m : ℝ) + 1) / ((k : ℝ) + 2) := by
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  simp only [annCap, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one,
    NNReal.coe_ofNat]
  field_simp
  ring

theorem annCap_lt (m k : ℕ) : annCap m k < (m : ℝ≥0) + 1 := by
  rw [← NNReal.coe_lt_coe, annCap_coe]
  push_cast
  have : 0 < ((m : ℝ) + 1) / ((k : ℝ) + 2) := by positivity
  linarith

theorem annCap_pos (m k : ℕ) : 0 < annCap m k := by
  rw [← NNReal.coe_pos, annCap_coe]
  have hk : (1 : ℝ) < (k : ℝ) + 2 := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have : ((m : ℝ) + 1) / ((k : ℝ) + 2) < (m : ℝ) + 1 := div_lt_self hm hk
  linarith

theorem annCap_mono (m : ℕ) : Monotone (annCap m) := fun k l hkl => by
  rw [← NNReal.coe_le_coe, annCap_coe, annCap_coe]
  have hkl' : (k : ℝ) + 2 ≤ (l : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hkl 2
  have : ((m : ℝ) + 1) / ((l : ℝ) + 2) ≤ ((m : ℝ) + 1) / ((k : ℝ) + 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hkl'
  linarith

/-- `a / (n + 2)` eventually drops below any positive `δ`. -/
theorem exists_div_add_two_lt {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, a / ((n : ℝ) + 2) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (a / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at hN
  nlinarith

theorem exists_lt_annCap (m : ℕ) {t : ℝ≥0} (ht : t < (m : ℝ≥0) + 1) :
    ∃ N, ∀ n ≥ N, t < annCap m n := by
  have ht' : (t : ℝ) < (m : ℝ) + 1 := by exact_mod_cast ht
  obtain ⟨N, hN⟩ := exists_div_add_two_lt (a := (m : ℝ) + 1) (by positivity) (sub_pos.2 ht')
  refine ⟨N, fun n hn => ?_⟩
  rw [← NNReal.coe_lt_coe, annCap_coe]
  have := hN n hn
  linarith

theorem measurable_annLevel {G : GaugeReadout} (hG : ∀ t, Measurable (G t)) (m k : ℕ) :
    Measurable (annLevel G m k) :=
  (measurable_recLevel hG m).add ((((hG 0).comp (measurable_id.prodMk measurable_const)).sub
    (measurable_recLevel hG m)).div_const _)

theorem measurable_annRules {G : GaugeReadout} (hG : ∀ t, Measurable (G t)) (m n : ℕ) :
    Measurable (annRules G m n) := by
  have e : annRules G m n = fun x => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => annRule G m k x) := funext fun x => (Finset.sup'_eq_sup _ _).symm
  rw [e]
  exact Finset.measurable_range_sup'' fun k _ =>
    (measurable_hitRule hG (measurable_annLevel hG m k)).min measurable_const

theorem isPathRule_annRules {G : GaugeReadout} (hG : IsCausal G) (m n : ℕ) : IsPathRule (annRules G m n) :=
  isPathRule_finsetSup (fun _ => isPathRule_min_const (isPathRule_hitRule hG) _) _

theorem annRules_ne_top (G : GaugeReadout) (m n : ℕ) (x : RecData × (ℝ≥0 → ℝ)) : annRules G m n x ≠ ⊤ := by
  refine ne_of_lt ((Finset.sup_lt_iff (show (⊥ : ℝ≥0∞) < ⊤ from bot_lt_top)).2 fun _ _ => ?_)
  exact (min_le_right _ _).trans_lt ENNReal.coe_lt_top

theorem monotone_annRules (G : GaugeReadout) (m : ℕ) (x : RecData × (ℝ≥0 → ℝ)) :
    Monotone fun n => annRules G m n x := fun _ _ hnn' =>
  Finset.sup_mono (Finset.range_subset_range.2 (Nat.add_le_add_right hnn' 1))

/-! ### The coordinate versions are announced -/

section Coord

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
  {γ α : Ω → ℝ≥0 → ℂ} {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}

/-- **On the read-back event the announcing rules announce the coordinate stop**: at the coordinate version they are
the gauge stops of the levels `ε_k` and caps `c_k`, strictly below the coordinate stop, with supremum the coordinate
stop. -/
theorem ae_annRules_coord (hread : AESeparationReadout P (gb6Rec s Wα ζα) D L g G) (m : ℕ) :
    ∀ᵐ ω ∂P, (∀ n, annRules G m n (gb6Rec s Wα ζα ω, fun u => coordDriver (D := D) (g := g) m u ω) <
        (coordStop (g := g) m ω : ℝ≥0∞)) ∧
      ⨆ n, annRules G m n (gb6Rec s Wα ζα ω, fun u => coordDriver (D := D) (g := g) m u ω) =
        (coordStop (g := g) m ω : ℝ≥0∞) := by
  have hv : ∀ ω, (coordStop (g := g) m ω : ℝ≥0∞) < L ω :=
    fun ω => localStop_lt (hread.continuous ω) (hread.zero_pos ω) (hread.terminal ω) m
  filter_upwards [hread.readout] with ω hω
  set r := gb6Rec s Wα ζα ω with hr
  set w : ℝ≥0 → ℝ := fun u => coordDriver (D := D) (g := g) m u ω with hw
  set gω : ℝ≥0 → ℝ := fun t => g t ω with hgω
  have hgc : Continuous gω := hread.continuous ω
  set ε := gaugeLevel (gω 0) m with hεdef
  have hε0 : ε < gω 0 := gaugeLevel_lt (hread.zero_pos ω) m
  set T := coordStop (g := g) m ω with hTdef
  have hrec : recLevel G m r = ε := by
    change gaugeLevel (G 0 (r, fun _ => 0)) m = _
    rw [hω.1]
  have hG0 : G 0 (r, fun _ => 0) = gω 0 := hω.1
  have hrd : ∀ u ≤ T, G u (r, w) = gω u := fun u hu => by
    calc
      _ = G u (r, fun u => D u ω) := hread.causal u _ _ _ fun v hv' => freeze_eq (hv'.trans hu)
      _ = gω u := hω.2 u ((ENNReal.coe_le_coe.2 hu).trans_lt (hv ω))
  set εs : ℕ → ℝ := fun k => ε + (gω 0 - ε) / ((k : ℝ) + 2) with hεs
  have hlev : ∀ k, annLevel G m k r = εs k := fun k => by
    simp only [annLevel, hrec, hG0, hεs]
  have hεs_gt : ∀ k, ε < εs k := fun k =>
    lt_add_of_pos_right _ (div_pos (sub_pos.2 hε0) (by positivity))
  have hεs_lt : ∀ k, εs k < gω 0 := fun k => by
    have hk : (1 : ℝ) < (k : ℝ) + 2 := by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    have h2 : (gω 0 - ε) / ((k : ℝ) + 2) < gω 0 - ε := div_lt_self (sub_pos.2 hε0) hk
    simp only [hεs]
    linarith
  have hεs_anti : Antitone εs := fun k l hkl => by
    have : (gω 0 - ε) / ((l : ℝ) + 2) ≤ (gω 0 - ε) / ((k : ℝ) + 2) :=
      div_le_div_of_nonneg_left (sub_pos.2 hε0).le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hkl 2)
    simp only [hεs]
    linarith
  have hstop : ∀ k, annRule G m k (r, w) = (gaugeStop gω (εs k) (annCap m k) : ℝ≥0∞) := fun k => by
    have hle : gaugeStop gω (εs k) (annCap m k) ≤ T :=
      gaugeStop_mono hgc (hεs_gt k).le (annCap_lt m k).le
    have hh : hitRule G (annLevel G m k) (annCap m k) (r, w) = gaugeStop gω (annLevel G m k r) (annCap m k) :=
      hitRule_eq_gaugeStop hgc (annCap_pos m k) (by rw [hlev]; exact hεs_lt k) fun u hu =>
        hrd u (by rw [hlev] at hu; exact hu.trans hle)
    rw [annRule, hh, hlev, min_eq_left (ENNReal.coe_le_coe.2 (gaugeStop_le _ _ _))]
  have hmono : Monotone fun k => gaugeStop gω (εs k) (annCap m k) := fun k l hkl =>
    gaugeStop_mono hgc (hεs_anti hkl) (annCap_mono m hkl)
  have hrules : ∀ n, annRules G m n (r, w) = (gaugeStop gω (εs n) (annCap m n) : ℝ≥0∞) := fun n => by
    refine le_antisymm (Finset.sup_le fun k hk => ?_) ?_
    · rw [hstop]
      exact ENNReal.coe_le_coe.2 (hmono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
    · rw [← hstop]
      exact Finset.le_sup (f := fun k => annRule G m k (r, w)) (Finset.self_mem_range_succ n)
  have hlt : ∀ n, gaugeStop gω (εs n) (annCap m n) < T := fun n =>
    gaugeStop_lt_of_lt hgc (hεs_gt n) (hεs_lt n) (annCap_lt m n)
  refine ⟨fun n => by rw [hrules]; exact ENNReal.coe_lt_coe.2 (hlt n),
    le_antisymm (iSup_le fun n => by rw [hrules]; exact ENNReal.coe_le_coe.2 (hlt n).le) ?_⟩
  refine le_of_forall_lt fun a ha => ?_
  have ha' : a ≠ ⊤ := (ha.trans ENNReal.coe_lt_top).ne
  have htT : a.toNNReal < T := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal ha']
    exact ha
  obtain ⟨n, hn⟩ := exists_lt_gaugeStop hgc htT (εs := εs) (cs := annCap m)
    (fun δ hδ => by
      obtain ⟨N, hN⟩ := exists_div_add_two_lt (sub_pos.2 hε0).le hδ
      exact ⟨N, fun n hn => by simp only [hεs]; linarith [hN n hn]⟩)
    (fun t' ht' => exists_lt_annCap m ht')
  rw [← ENNReal.coe_toNNReal ha']
  exact (ENNReal.coe_lt_coe.2 hn).trans_le (by
    rw [← hrules]
    exact le_iSup (fun n => annRules G m n (r, w)) n)

/-- **The coordinate versions are announced versions.** -/
theorem isGB6RelVersionA_coord (hC : RelativeDriverCoordinates s P W Wα ζα γ α D L)
    (hread : AESeparationReadout P (gb6Rec s Wα ζα) D L g G) (m : ℕ) :
    IsGB6RelVersionA s P W Wα ζα γ α (coordDriver (D := D) (g := g) m)
      (fun ω => (coordStop (g := g) m ω : ℝ≥0∞)) :=
  ⟨isGB6RelVersionR_coord hC hread m, annRules G m, measurable_annRules hread.readout_measurable m,
    isPathRule_annRules hread.causal m, annRules_ne_top G m, monotone_annRules G m, by
      filter_upwards [ae_annRules_coord hread m] with ω hω _ using hω⟩

end Coord

/-! ### The wiring from the read-back input -/

/-- **Exhausting announced versions from the corrected read-back input** (`HullId.gb6RelVersionRStatement_of_
readoutCoord` with announcing rules). -/
theorem gb6RelVersionAStatement_of_readoutCoord (hread : GB6ReadoutCoordStatement.{u}) :
    GB6RelVersionAStatement.{u} := by
  intro κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hchart hcf hγ hflow hα s
  by_cases hs : s = 0
  · subst s
    have hα0 : ∀ᵐ ω ∂P, α ω 0 = 0 := hα.mono fun _ hω => hω.1
    obtain ⟨R, V, hRV, hex⟩ := exists_versionsR_at_zero (P := P) (W := W) (Wα := Wα) (ζα := ζα) (γ := γ) hα0
    refine ⟨R, V, fun m => ⟨hRV m, fun _ _ => 0, fun _ => measurable_const, fun _ _ _ _ _ => rfl,
      fun _ _ => ENNReal.zero_ne_top, fun _ _ _ _ => le_rfl, ?_⟩, hex⟩
    filter_upwards [ae_gb6RecGood hflow hα 0, hα0] with ω hg hω hm
    obtain ⟨-, hH⟩ := (mem_gb6TS_iff hg).2 hm
    rw [hω] at hH
    exact ((lt_irrefl (0 : ℝ)) hH).elim
  · have hsp : 0 < s := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ s) (Ne.symm hs)
    obtain ⟨D, L, g, G, hC, hg⟩ := hread κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
      hb hG hb' hchart hcf hγ hflow hα s hsp
    refine ⟨coordDriver (D := D) (g := g), fun m ω => (coordStop (g := g) m ω : ℝ≥0∞),
      isGB6RelVersionA_coord hC hg, ?_⟩
    filter_upwards [hC.relative] with ω hrel hs hαs t ht
    obtain ⟨-, haL, -⟩ := (hrel hs hαs).2 t ht
    obtain ⟨m, hm⟩ := exists_lt_localStop (hg.continuous ω)
      (t := (gb6Clock s W Wα ω t).toNNReal) fun u hu =>
        hg.positive ω u ((ENNReal.coe_le_coe.2 hu).trans_lt haL)
    exact ⟨m, ENNReal.coe_lt_coe.2 hm⟩

/-- **GB6's hull identity from the corrected read-back input and the relative safe law.** -/
theorem gb6HullDetStatement_of_readoutCoord_relSafe (hread : GB6ReadoutCoordStatement.{u})
    (hS : GB6RelSafeStatement.{u}) : Supp8.GB6.GB6HullDetStatement.{u} :=
  gb6HullDetStatement_of_relSafe (gb6RelVersionAStatement_of_readoutCoord hread) hS

/-- **GB6's hull identity from the read-back on the record event (`HullId.GB6LiveReadoutStatement`) and the relative
safe law (`GB6RelSafeStatement`).** -/
theorem gb6HullDetStatement_of_liveReadout_relSafe (hread : GB6LiveReadoutStatement.{u})
    (hS : GB6RelSafeStatement.{u}) : Supp8.GB6.GB6HullDetStatement.{u} :=
  gb6HullDetStatement_of_readoutCoord_relSafe (gb6ReadoutCoordStatement_of_liveReadout hread) hS

end InteractingSLE.Supp8.Q3Stop
