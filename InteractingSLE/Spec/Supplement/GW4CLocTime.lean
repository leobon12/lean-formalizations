/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocFac
import InteractingSLE.Spec.Coupling.LawUniqueHistory
import InteractingSLE.GFF.LocalSets.Characterization
import InteractingSLE.Spec.Coupling.WholeFieldMarked

/-!
# From dyadic times to all times

Packet PROVE-GW4-CLOC, step 6 (generic). Let `A t` be an increasing family of relatively closed random subsets of `ℍ`
that is right-continuous on compact sets (a compact `K ⊆ ℍ` avoided by `A t` is avoided by some `A t'`, `t' > t`), and
`ℋ` increasing marks. If `A` satisfies the history-marked avoidance criterion for `ℋ` at every dyadic time, it
satisfies it at every time (`isHistoryAvoidanceLocal_of_dyadic`).

Proof: for an open `U ⊆ ℍ` exhaust `U` by open sets `W m` with compact closures in `U`
(`exhaustOpen`). The avoidance event of `cl(W m)` by `A t` is the increasing union over dyadic times `uₙ ↓ t` and over
shrinking open neighbourhoods of `cl(W m)` of dyadic avoidance events, which factor through the complement along
`W m` (Markov nesting `Fac.mono_open`; limits `Fac.iUnion`); the avoidance event of `U` is the decreasing intersection
over `m` (`Fac.iInter`); the canonical criterion `fac_of_exhaust` (Proposition 3.2) concludes for every Markov map
of `U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW4Fix.CLoc

open LocalSets WholeField

/-! ### Dyadic times from above -/

theorem antitone_dyadicTime_upperDyadic (r : ℝ≥0) :
    Antitone fun n => LawUnique.dyadicTime (LawUnique.upperDyadic r n) := by
  refine antitone_nat_of_succ_le fun n => ?_
  simp only [LawUnique.dyadicTime, LawUnique.upperDyadic]
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  set x : ℝ≥0 := 2 ^ n * r with hx
  have hx2 : (2 : ℝ≥0) ^ (n + 1) * r = 2 * x := by rw [hx, pow_succ]; ring
  rw [hx2]
  have hfl : ⌊2 * x⌋₊ ≤ 2 * ⌊x⌋₊ + 1 := by
    have h1 : 2 * x < ((2 * ⌊x⌋₊ + 2 : ℕ) : ℝ≥0) := by
      have := Nat.lt_floor_add_one x
      push_cast
      linarith
    have := (Nat.floor_lt (by positivity)).2 h1
    omega
  rw [div_le_div_iff₀ (pow_pos two_pos _) h2, pow_succ]
  push_cast
  have hc : ((⌊2 * x⌋₊ : ℝ≥0) + 1) ≤ 2 * ((⌊x⌋₊ : ℝ≥0) + 1) := by
    have : ((⌊2 * x⌋₊ : ℕ) : ℝ≥0) ≤ ((2 * ⌊x⌋₊ + 1 : ℕ) : ℝ≥0) := by exact_mod_cast hfl
    push_cast at this
    linarith
  calc ((⌊2 * x⌋₊ : ℝ≥0) + 1) * 2 ^ n ≤ 2 * ((⌊x⌋₊ : ℝ≥0) + 1) * 2 ^ n := by gcongr
    _ = ((⌊x⌋₊ : ℝ≥0) + 1) * (2 ^ n * 2) := by ring

/-! ### An exhaustion by relatively compact open sets -/

/-- The open set of points of `U` of norm `< m` at distance `> 1/(m+1)` from the complement. -/
def exhaustOpen (U : Opens ℂ) (m : ℕ) : Opens ℂ :=
  ⟨{z | z ∈ U ∧ ‖z‖ < m ∧ 1 / ((m : ℝ) + 1) < infDist z (U : Set ℂ)ᶜ},
    U.isOpen.inter ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const (continuous_infDist_pt _)))⟩

theorem exhaustOpen_le (U : Opens ℂ) (m : ℕ) : exhaustOpen U m ≤ U := fun _ hz => hz.1

theorem monotone_exhaustOpen (U : Opens ℂ) : Monotone (exhaustOpen U) := by
  intro m m' hmm' z ⟨hzU, hzn, hzd⟩
  refine ⟨hzU, hzn.trans_le (by exact_mod_cast hmm'), lt_of_le_of_lt ?_ hzd⟩
  have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
  gcongr

theorem closure_exhaustOpen_subset (U : Opens ℂ) (m : ℕ) :
    closure (exhaustOpen U m : Set ℂ) ⊆ {z | ‖z‖ ≤ m ∧ 1 / ((m : ℝ) + 1) ≤ infDist z (U : Set ℂ)ᶜ} := by
  refine closure_minimal (fun z hz => ⟨hz.2.1.le, hz.2.2.le⟩) ?_
  exact (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le continuous_const (continuous_infDist_pt _))

theorem closure_exhaustOpen_subset_U (U : Opens ℂ) (m : ℕ) : closure (exhaustOpen U m : Set ℂ) ⊆ U := by
  intro z hz
  have h := (closure_exhaustOpen_subset U m hz).2
  have hpos : 0 < infDist z (U : Set ℂ)ᶜ := lt_of_lt_of_le (by positivity) h
  by_contra hzU
  exact (lt_irrefl _) (hpos.trans_le (infDist_zero_of_mem hzU).le)

theorem isCompact_closure_exhaustOpen (U : Opens ℂ) (m : ℕ) : IsCompact (closure (exhaustOpen U m : Set ℂ)) := by
  refine (isCompact_closedBall (0 : ℂ) m).of_isClosed_subset isClosed_closure fun z hz => ?_
  rw [mem_closedBall, dist_zero_right]
  exact (closure_exhaustOpen_subset U m hz).1

theorem exists_subset_exhaustOpen (U : Opens ℂ) (hU : (U : Set ℂ)ᶜ.Nonempty) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ m, K ⊆ exhaustOpen U m := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, empty_subset _⟩
  have hcl : IsClosed ((U : Set ℂ)ᶜ) := U.isOpen.isClosed_compl
  obtain ⟨z₀, hz₀K, hz₀⟩ := hK.exists_isMinOn hKne (continuous_infDist_pt ((U : Set ℂ)ᶜ)).continuousOn
  have hδ : 0 < infDist z₀ (U : Set ℂ)ᶜ := by
    rw [← hcl.notMem_iff_infDist_pos hU]
    exact fun h => h (hKU hz₀K)
  obtain ⟨r, hr⟩ := hK.isBounded.exists_norm_le
  obtain ⟨m₁, hm₁⟩ := exists_nat_one_div_lt hδ
  obtain ⟨m₂, hm₂⟩ := exists_nat_gt r
  refine ⟨max m₁ m₂, fun z hz => ⟨hKU hz, (hr z hz).trans_lt (hm₂.trans_le (by exact_mod_cast le_max_right _ _)),
    ?_⟩⟩
  refine lt_of_le_of_lt ?_ (hm₁.trans_le (hz₀ hz))
  have : (m₁ : ℝ) ≤ (max m₁ m₂ : ℕ) := by exact_mod_cast le_max_left _ _
  gcongr

/-! ### Avoidance of a compact set -/

theorem exists_disjoint_thickening {A K : Set ℂ} (hA : IsOpen (H \ A)) (hK : IsCompact K) (hKH : K ⊆ H)
    (hd : Disjoint A K) : ∃ k : ℕ, Disjoint A (thickening (1 / ((k : ℝ) + 1)) K) := by
  have hsub : K ⊆ H \ A := fun z hz => ⟨hKH hz, fun hzA => Set.disjoint_left.1 hd hzA hz⟩
  obtain ⟨δ, hδ, hδsub⟩ := hK.exists_thickening_subset_open hA hsub
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  refine ⟨k, Set.disjoint_right.2 fun z hz hzA => ?_⟩
  exact (hδsub (thickening_mono hk.le K hz)).2 hzA

/-- The open neighbourhoods `ℍ ∩ (cl W)^{1/(k+1)}` of a compact closure. -/
def nbhdK (W : Set ℂ) (k : ℕ) : Opens ℂ :=
  ⟨H ∩ thickening (1 / ((k : ℝ) + 1)) (closure W), QuantumZipper.isOpen_H.inter isOpen_thickening⟩

theorem disjoint_closure_iff_exists_nbhdK {A W : Set ℂ} (hAH : A ⊆ H) (hA : IsOpen (H \ A))
    (hK : IsCompact (closure W)) (hKH : closure W ⊆ H) :
    Disjoint A (closure W) ↔ ∃ k, Disjoint A (nbhdK W k : Set ℂ) := by
  constructor
  · intro hd
    obtain ⟨k, hk⟩ := exists_disjoint_thickening hA hK hKH hd
    exact ⟨k, hk.mono_right inter_subset_right⟩
  · rintro ⟨k, hk⟩
    refine Set.disjoint_left.2 fun z hzA hzK => Set.disjoint_left.1 hk hzA ⟨hAH hzA, ?_⟩
    exact self_subset_thickening (by positivity) _ hzK

theorem antitone_nbhdK (W : Set ℂ) : Antitone (nbhdK W) := by
  intro k k' hkk' z ⟨hzH, hz⟩
  refine ⟨hzH, thickening_mono ?_ _ hz⟩
  have : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
  gcongr

/-! ### The time extension -/

section Time

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- **From dyadic times to all times.** -/
theorem isHistoryAvoidanceLocal_of_dyadic (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X Q)
    {ℋ : ℝ≥0 → MeasurableSpace Ω} (hℋ : Monotone ℋ) (hℋle : ∀ t, ℋ t ≤ mΩ)
    {A : ℝ≥0 → Ω → Set ℂ} (hAm : ∀ t, Measurable[mΩ, hittingSigma] (A t))
    (hAc : ∀ t ω, A t ω ⊆ H ∧ IsOpen (H \ A t ω)) (hmono : ∀ ω, Monotone fun t => A t ω)
    (hright : ∀ t ω (K : Set ℂ), IsCompact K → K ⊆ H → Disjoint (A t ω) K →
      ∃ t', t < t' ∧ Disjoint (A t' ω) K)
    (hdy : ∀ p : ℕ × ℕ, IsHistoryAvoidanceLocal (ℋ (LawUnique.dyadicTime p)) (A (LawUnique.dyadicTime p)) X Q)
    (t : ℝ≥0) : IsHistoryAvoidanceLocal (ℋ t) (A t) X Q := by
  intro U G hUH hG hd E hE
  have hXm := hX.measurable
  have hUH' : U ≤ upperHalfPlaneOpens := hUH
  have hUc : (U : Set ℂ)ᶜ.Nonempty := ⟨0, fun h0 => by
    have h := hUH h0
    simp [QuantumZipper.H] at h⟩
  -- Markov maps of all open subsets of `ℍ`
  have hmk : ∀ V : Opens ℂ, (V : Set ℂ) ⊆ H → ∃ GV : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens,
      Measurable GV ∧ GFF.IsMarkovDecomposition V upperHalfPlaneOpens X (fun ω => GV (X ω)) Q := fun V hV => by
    obtain ⟨GV, hGVm, hGV⟩ := exists_markovMap V hV
    exact ⟨GV, hGVm, hGV hX⟩
  set W : ℕ → Opens ℂ := exhaustOpen U with hW
  have hWU : ∀ m, (W m : Set ℂ) ⊆ U := fun m => exhaustOpen_le U m
  have hWH : ∀ m, closure (W m : Set ℂ) ⊆ H := fun m => (closure_exhaustOpen_subset_U U m).trans hUH
  have hWc : ∀ m, IsCompact (closure (W m : Set ℂ)) := isCompact_closure_exhaustOpen U
  choose GW hGWm hGW using fun m => hmk (W m) ((subset_closure).trans (hWH m))
  choose GN hGNm hGN using fun (m k : ℕ) => hmk (nbhdK (W m) k) inter_subset_left
  have hEm : MeasurableSet E := hℋle t _ hE
  set u : ℕ → ℝ≥0 := fun n => LawUnique.dyadicTime (LawUnique.upperDyadic t n) with hu
  have hut : ∀ n, t ≤ u n := fun n => (LawUnique.lt_dyadicTime_upperDyadic t n).le
  have hmeasA : ∀ s (V : Opens ℂ), (V : Set ℂ) ⊆ H → MeasurableSet {ω | Disjoint (A s ω) V} := fun s V hV =>
    hAm s (measurableSet_avoid V.isOpen hV)
  have hmeasK : ∀ s m, MeasurableSet {ω | Disjoint (A s ω) (closure (W m : Set ℂ))} := by
    intro s m
    have he : {ω | Disjoint (A s ω) (closure (W m : Set ℂ))} =
        ⋃ k, {ω | Disjoint (A s ω) (nbhdK (W m) k : Set ℂ)} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      exact disjoint_closure_iff_exists_nbhdK (hAc s ω).1 (hAc s ω).2 (hWc m) (hWH m)
    rw [he]
    exact MeasurableSet.iUnion fun k => hmeasA s _ inter_subset_left
  -- step 1: closed sets at a dyadic time
  have hstep1 : ∀ m n, Fac Q X (GW m) ({ω | Disjoint (A (u n) ω) (closure (W m : Set ℂ))} ∩ E) := by
    intro m n
    have he : {ω | Disjoint (A (u n) ω) (closure (W m : Set ℂ))} ∩ E =
        ⋃ k, ({ω | Disjoint (A (u n) ω) (nbhdK (W m) k : Set ℂ)} ∩ E) := by
      rw [← iUnion_inter]
      congr 1
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      exact disjoint_closure_iff_exists_nbhdK (hAc _ ω).1 (hAc _ ω).2 (hWc m) (hWH m)
    rw [he]
    refine Fac.iUnion hXm (hGWm m) (hGW m) (fun k => (hmeasA _ _ inter_subset_left).inter hEm) ?_ fun k => ?_
    · intro k k' hkk' ω ⟨hω, hωE⟩
      exact ⟨hω.mono_right (antitone_nbhdK _ hkk'), hωE⟩
    · have hloc := hdy (LawUnique.upperDyadic t n) (nbhdK (W m) k) (GN m k) inter_subset_left (hGNm m k)
        (hGN m k) E (hℋ (hut n) _ hE)
      have hWN : W m ≤ nbhdK (W m) k := fun z hz =>
        ⟨(hWH m) (subset_closure hz), self_subset_thickening (by positivity) _ (subset_closure hz)⟩
      exact Fac.mono_open hXm hWN inter_subset_left (hGW m) (hGN m k) hloc
  -- step 2: closed sets at the time `t`
  have hstep2 : ∀ m, Fac Q X (GW m) ({ω | Disjoint (A t ω) (closure (W m : Set ℂ))} ∩ E) := by
    intro m
    have he : {ω | Disjoint (A t ω) (closure (W m : Set ℂ))} ∩ E =
        ⋃ n, ({ω | Disjoint (A (u n) ω) (closure (W m : Set ℂ))} ∩ E) := by
      rw [← iUnion_inter]
      congr 1
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · intro hdj
        obtain ⟨t', htt', hdj'⟩ := hright t ω _ (hWc m) (hWH m) hdj
        have hlim := LawUnique.tendsto_dyadicTime_upperDyadic t
        obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds htt')).exists
        exact ⟨n, hdj'.mono_left (hmono ω hn.le)⟩
      · rintro ⟨n, hn⟩
        exact hn.mono_left (hmono ω (hut n))
    rw [he]
    refine Fac.iUnion hXm (hGWm m) (hGW m) (fun n => (hmeasK _ m).inter hEm) ?_ (hstep1 m)
    intro n n' hnn' ω ⟨hω, hωE⟩
    exact ⟨hω.mono_left (hmono ω (antitone_dyadicTime_upperDyadic t hnn')), hωE⟩
  -- step 3: the open set `U`, through every `W m`
  have hstep3 : ∀ m, Fac Q X (GW m) ({ω | Disjoint (A t ω) (U : Set ℂ)} ∩ E) := by
    intro m
    have he : {ω | Disjoint (A t ω) (U : Set ℂ)} ∩ E =
        ⋂ j, ({ω | Disjoint (A t ω) (closure (W (m + j) : Set ℂ))} ∩ E) := by
      rw [← iInter_inter]
      congr 1
      ext ω
      simp only [mem_ofPred_eq, mem_iInter]
      constructor
      · intro hdj j
        exact hdj.mono_right (closure_exhaustOpen_subset_U U (m + j))
      · intro hdj
        refine Set.disjoint_right.2 fun z hzU hzA => ?_
        obtain ⟨j, hj⟩ := exists_subset_exhaustOpen U hUc (isCompact_singleton (x := z))
          (singleton_subset_iff.2 hzU)
        have hz : z ∈ closure (W (m + j) : Set ℂ) :=
          subset_closure (monotone_exhaustOpen U (Nat.le_add_left j m) (hj (mem_singleton z)))
        exact Set.disjoint_left.1 (hdj j) hzA hz
    rw [he]
    refine Fac.iInter hXm (hGWm m) (hGW m) (fun j => (hmeasK _ _).inter hEm) ?_ fun j => ?_
    · intro j j' hjj' ω ⟨hω, hωE⟩
      refine ⟨hω.mono_right (closure_mono ?_), hωE⟩
      exact monotone_exhaustOpen U (Nat.add_le_add_left hjj' m)
    · exact Fac.mono_open hXm (monotone_exhaustOpen U (Nat.le_add_right m j))
        ((subset_closure).trans (hWH (m + j))) (hGW m) (hGW (m + j)) (hstep2 (m + j))
  exact fac_of_exhaust hX hUH' hG hd (monotone_exhaustOpen U) hWc hWH
    (fun K hK hKU => exists_subset_exhaustOpen U hUc hK hKU) hGW hstep3

end Time

end InteractingSLE.Theorem14.GW4Fix.CLoc
