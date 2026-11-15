/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.CondMeanStop

/-!
# Lemma 7.1: history locality of complete curves from their finite prefixes

Packet PROVE-LEMMA71G, part (A) (specification §7.1, proof of Lemma 7.1, p. 225, `source/spec/p193-240.md` L600–L601:
"the optional history marking of the original coupling supplies the required history locality. The extension to
complete outer curves is obtained by increasing finite prefixes").

Lemma 6.2's history-sensitive hypothesis (`Sec6.IsEntranceHistoryLocal`) asks, for every deterministic open `U ⊆ ℍ`,
that the history of the path through its first entrance time `T^U` be conditionally independent of `h_U` given
`h_{U^c}`. The landed form of Aux. lemma 56 (`Restart.RetainedRangeEntranceStatement`) gives this for the path frozen
after a finite cap `n`. This file proves the passage to the complete path:

* `condIndepEv_of_le_iSup`: conditional independence of `𝒦 n` and `B` given `G` for an increasing sequence `𝒦 n`
  passes to every `A ≤ ⨆ n, 𝒦 n` (the Markov form `P[b | 𝒦 n ∨ G] = P[b | G]` and identification of conditional
  expectations on the π-system `⋃ n, 𝒦 n ∨ G`);
* the pathwise facts for the frozen path `capAt γ n = γ(· ∧ n)` of a continuous path started outside the open `U`:
  its first entrance time is `T^U` if `T^U < n` and `∞` otherwise (`firstEntrance_capAt_of_lt`,
  `firstEntrance_capAt_of_le`); its history is a measurable function of the history of `capAt γ (n + 1)`
  (`entHist_capAt_eq_restrictHist`); the history of `γ` is a measurable function of all of them
  (`entHist_eq_joinHist`);
* **`isEntranceHistoryLocal_of_capAt`**: if every frozen path `η(· ∧ n)`, `n ∈ ℕ`, has Lemma 6.2's history locality,
  so does the complete path.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71G

open QuantumZipper (H)
open LQGMetric (DistOn CondIndepEv)
open Sec6 LocalSets

/-! ### Conditional independence passes to the join of an increasing sequence -/

section Join

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Conditional independence passes to the join of an increasing sequence of σ-algebras.** If `𝒦 n` is increasing
and each `𝒦 n` is conditionally independent of `B` given `G`, then so is every `A ≤ ⨆ n, 𝒦 n`. -/
theorem condIndepEv_of_le_iSup {G B A : MeasurableSpace Ω} {𝒦 : ℕ → MeasurableSpace Ω} (hG : G ≤ mΩ)
    (hB : B ≤ mΩ) (hmono : Monotone 𝒦) (h𝒦 : ∀ n, 𝒦 n ≤ mΩ) (hind : ∀ n, CondIndepEv G (𝒦 n) B P)
    (hA : A ≤ ⨆ n, 𝒦 n) : CondIndepEv G A B P := by
  have hK : (⨆ n, 𝒦 n) ≤ mΩ := iSup_le h𝒦
  have hsup : ∀ b, MeasurableSet[B] b → P⟦b | (⨆ n, 𝒦 n) ⊔ G⟧ =ᵐ[P] P⟦b | G⟧ := by
    intro b hb
    have hb0 := hB b hb
    have hn : ∀ n, P⟦b | 𝒦 n ⊔ G⟧ =ᵐ[P] P⟦b | G⟧ := fun n =>
      LQGMetric.condExp_sup_eq_of_condIndepEv hG (h𝒦 n) hB (hind n) hb
    have hgen : (⨆ n, 𝒦 n) ⊔ G =
        MeasurableSpace.generateFrom (⋃ n, {s | MeasurableSet[𝒦 n ⊔ G] s}) := by
      rw [iSup_sup]
      exact (MeasurableSpace.generateFrom_iUnion_measurableSet fun n => 𝒦 n ⊔ G).symm
    have hpi : IsPiSystem (⋃ n, {s | MeasurableSet[𝒦 n ⊔ G] s}) :=
      isPiSystem_iUnion_of_monotone _ (fun n => @MeasurableSpace.isPiSystem_measurableSet Ω (𝒦 n ⊔ G))
        fun i j hij s hs => (sup_le_sup_right (hmono hij) G) s hs
    refine (LQGMetric.ae_eq_condExp_of_isPiSystem (sup_le hK hG) hgen hpi (LQGMetric.integrable_indOne hb0)
      integrable_condExp (stronglyMeasurable_condExp.mono le_sup_right) (integral_condExp hG) ?_).symm
    intro s hs
    obtain ⟨n, hsn⟩ := mem_iUnion.1 hs
    calc ∫ x in s, (P⟦b | G⟧) x ∂P = ∫ x in s, (P⟦b | 𝒦 n ⊔ G⟧) x ∂P :=
          setIntegral_congr_ae (sup_le (h𝒦 n) hG s hsn) ((hn n).mono fun x hx _ => hx.symm)
      _ = ∫ x in s, b.indicator (fun _ => (1 : ℝ)) x ∂P :=
          setIntegral_condExp (sup_le (h𝒦 n) hG) (LQGMetric.integrable_indOne hb0) hsn
  have h1 : CondIndepEv G B (⨆ n, 𝒦 n) P := LQGMetric.condIndepEv_of_condExp_sup_eq hG hB hK hsup
  exact h1.symm.mono hA le_rfl

end Join

/-! ### Paths frozen after a cap -/

section Path

/-- The path frozen after time `n`: `γ(· ∧ n)`. -/
def capAt (γ : ℝ≥0 → ℂ) (n : ℝ≥0) : ℝ≥0 → ℂ := fun t => γ (min t n)

theorem continuous_capAt {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (n : ℝ≥0) : Continuous (capAt γ n) :=
  hγ.comp (continuous_id.min continuous_const)

theorem capAt_zero (γ : ℝ≥0 → ℂ) (n : ℝ≥0) : capAt γ n 0 = γ 0 := by
  simp only [capAt, zero_le, min_eq_left]

theorem capAt_of_le (γ : ℝ≥0 → ℂ) {n t : ℝ≥0} (ht : t ≤ n) : capAt γ n t = γ t := by
  simp only [capAt, min_eq_left ht]

/-- The stopped history of a path through its first entrance time into `U`. -/
def entHist (U : Set ℂ) (γ : ℝ≥0 → ℂ) : Hist :=
  histOf (pathCoord γ) (firstEntrance U (pathCoord γ))

theorem entHist_fst (U : Set ℂ) (γ : ℝ≥0 → ℂ) : (entHist U γ).1 = firstEntrance U (pathCoord γ) := rfl

variable {U : Set ℂ} {γ : ℝ≥0 → ℂ}

/-- The first entrance time is at most every time at which the path is in the open set `U`. -/
theorem firstEntrance_le_of_mem (hU : IsOpen U) (hγ : Continuous γ) {s : ℝ≥0} (hs : γ s ∈ U) :
    firstEntrance U (pathCoord γ) ≤ s := by
  rw [firstEntrance_eq_sInf hU hγ]
  exact iInf₂_le s hs

/-- A continuous path started outside the open `U` avoids `U` through its first entrance time. -/
theorem avoidsUpTo_firstEntrance (hU : IsOpen U) (hγ : Continuous γ) (h0 : γ 0 ∉ U) :
    AvoidsUpTo γ (firstEntrance U (pathCoord γ)) U := fun _ ht =>
  notMem_of_le_firstEntrance hU hγ h0 ht

/-- **The frozen path enters `U` at the same time** if the path enters before the cap. -/
theorem firstEntrance_capAt_of_lt (hU : IsOpen U) (hγ : Continuous γ) {n : ℝ≥0}
    (hn : firstEntrance U (pathCoord γ) < n) :
    firstEntrance U (pathCoord (capAt γ n)) = firstEntrance U (pathCoord γ) := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt fun b hb => ?_
    have hlt := lt_min hb hn
    rw [firstEntrance_eq_sInf hU hγ] at hlt
    obtain ⟨t, ht⟩ := iInf_lt_iff.1 hlt
    obtain ⟨htU, htlt⟩ := iInf_lt_iff.1 ht
    have htn : t ≤ n := ENNReal.coe_le_coe.1 (htlt.trans_le (min_le_right _ _)).le
    have hmem : pathCoord (capAt γ n) = fun q : ℚ≥0 => capAt γ n q := rfl
    rw [firstEntrance_eq_sInf hU (continuous_capAt hγ n)]
    refine (iInf₂_le t (show capAt γ n t ∈ U by rw [capAt_of_le γ htn]; exact htU)).trans_lt ?_
    exact htlt.trans_le (min_le_left _ _)
  · rw [firstEntrance_eq_sInf hU (continuous_capAt hγ n)]
    refine le_iInf₂ fun t ht => (firstEntrance_le_of_mem hU hγ ht).trans ?_
    exact ENNReal.coe_le_coe.2 (min_le_left t n)

/-- **The frozen path never enters `U`** if the path does not enter before the cap. -/
theorem firstEntrance_capAt_of_le (hU : IsOpen U) (hγ : Continuous γ) (h0 : γ 0 ∉ U) {n : ℝ≥0}
    (hn : (n : ℝ≥0∞) ≤ firstEntrance U (pathCoord γ)) : firstEntrance U (pathCoord (capAt γ n)) = ⊤ := by
  rw [firstEntrance_eq_sInf hU (continuous_capAt hγ n)]
  refine iInf₂_eq_top.2 fun t ht => absurd ht ?_
  exact notMem_of_le_firstEntrance hU hγ h0 ((ENNReal.coe_le_coe.2 (min_le_right t n)).trans hn)

theorem coe_min_natCast (q : ℚ≥0) (n : ℕ) : ((min q (n : ℚ≥0) : ℚ≥0) : ℝ≥0) = min (q : ℝ≥0) (n : ℝ≥0) := by
  rw [NNRat.cast_min, NNRat.cast_natCast]

/-- Restricting a history recorded with the cap `n + 1` to the cap `n`. -/
def restrictHist (n : ℕ) (p : Hist) : Hist :=
  if p.1 < (n : ℝ≥0∞) then p else (⊤, fun q => p.2 (min q (n : ℚ≥0)))

theorem measurable_restrictHist (n : ℕ) : Measurable (restrictHist n) :=
  Measurable.ite (measurableSet_lt measurable_fst measurable_const) measurable_id
    (measurable_const.prodMk (Measurable.of_eval fun q => (measurable_pi_apply (min q (n : ℚ≥0))).comp measurable_snd))

/-- **The history of `γ(· ∧ n)` is a function of that of `γ(· ∧ (n + 1))`.** -/
theorem entHist_capAt_eq_restrictHist (hU : IsOpen U) (hγ : Continuous γ) (h0 : γ 0 ∉ U) (n : ℕ) :
    entHist U (capAt γ n) = restrictHist n (entHist U (capAt γ ((n + 1 : ℕ) : ℝ≥0))) := by
  have hn1 : ((n : ℝ≥0) : ℝ≥0∞) ≤ ((n + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_succ n
  rcases lt_or_ge (firstEntrance U (pathCoord γ)) (n : ℝ≥0) with hlt | hge
  · have hlt1 : firstEntrance U (pathCoord γ) < ((n + 1 : ℕ) : ℝ≥0) := hlt.trans_le hn1
    have e1 := firstEntrance_capAt_of_lt hU hγ hlt
    have e2 := firstEntrance_capAt_of_lt hU hγ hlt1
    have hTn : firstEntrance U (pathCoord γ) < (n : ℝ≥0∞) := by exact_mod_cast hlt
    unfold entHist restrictHist
    rw [e1, e2]
    split_ifs with hc
    swap
    · exact absurd hTn hc
    refine Prod.ext rfl (funext fun q => ?_)
    show stopCoord (pathCoord (capAt γ n)) (firstEntrance U (pathCoord γ)) q =
      stopCoord (pathCoord (capAt γ ((n + 1 : ℕ) : ℝ≥0))) (firstEntrance U (pathCoord γ)) q
    simp only [stopCoord]
    split_ifs with hq
    · have hqn : (q : ℝ≥0) ≤ (n : ℝ≥0) := ENNReal.coe_le_coe.1 (hq.trans hlt.le)
      have hqn1 : (q : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) := hqn.trans (by exact_mod_cast Nat.le_succ n)
      simp only [pathCoord, capAt_of_le γ hqn, capAt_of_le γ hqn1]
    · rfl
  · have e1 := firstEntrance_capAt_of_le hU hγ h0 hge
    have hT'n : ((n : ℝ≥0) : ℝ≥0∞) ≤ firstEntrance U (pathCoord (capAt γ ((n + 1 : ℕ) : ℝ≥0))) := by
      rcases lt_or_ge (firstEntrance U (pathCoord γ)) (((n + 1 : ℕ) : ℝ≥0)) with h1 | h1
      · rw [firstEntrance_capAt_of_lt hU hγ h1]; exact hge
      · rw [firstEntrance_capAt_of_le hU hγ h0 h1]; exact le_top
    have hnot : ¬ firstEntrance U (pathCoord (capAt γ ((n + 1 : ℕ) : ℝ≥0))) < (n : ℝ≥0∞) :=
      not_lt.2 (by exact_mod_cast hT'n)
    unfold entHist restrictHist
    rw [e1]
    split_ifs with hc
    · exact absurd hc hnot
    refine Prod.ext rfl (funext fun q => ?_)
    have hle : (((min q (n : ℚ≥0) : ℚ≥0) : ℝ≥0) : ℝ≥0∞) ≤
        firstEntrance U (pathCoord (capAt γ ((n + 1 : ℕ) : ℝ≥0))) := by
      rw [coe_min_natCast]
      exact (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans hT'n
    have hmn1 : ((min q (n : ℚ≥0) : ℚ≥0) : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) := by
      rw [coe_min_natCast]
      exact (min_le_right _ _).trans (by exact_mod_cast Nat.le_succ n)
    show stopCoord (pathCoord (capAt γ n)) ⊤ q = stopCoord (pathCoord (capAt γ ((n + 1 : ℕ) : ℝ≥0)))
      (firstEntrance U (pathCoord (capAt γ ((n + 1 : ℕ) : ℝ≥0)))) (min q (n : ℚ≥0))
    rw [stopCoord_of_le le_top, stopCoord_of_le hle]
    simp only [pathCoord]
    rw [capAt_of_le γ hmn1, coe_min_natCast]
    rfl

/-- The history of the complete path from the histories of all its frozen versions: the entrance time is the infimum,
the coordinate at `q` is read off the cap `⌈q⌉ + 1`. -/
def joinHist (p : ℕ → Hist) : Hist :=
  (⨅ n, (p n).1, fun q => (p (⌈(q : ℝ≥0)⌉₊ + 1)).2 q)

theorem lt_ceil_add_one (x : ℝ≥0) : x < ((⌈x⌉₊ + 1 : ℕ) : ℝ≥0) := by
  have := Nat.le_ceil x
  push_cast
  exact this.trans_lt (lt_add_one _)

/-- **The history of the complete path is the join of the histories of its frozen versions.** -/
theorem entHist_eq_joinHist (hU : IsOpen U) (hγ : Continuous γ) (h0 : γ 0 ∉ U) :
    entHist U γ = joinHist fun n => entHist U (capAt γ n) := by
  -- each frozen entrance time is `T` or `⊤`, and is `T` beyond `T`
  have hTn : ∀ n : ℕ, (firstEntrance U (pathCoord γ) < ((n : ℝ≥0) : ℝ≥0∞) ∧
      firstEntrance U (pathCoord (capAt γ n)) = firstEntrance U (pathCoord γ)) ∨
      (((n : ℝ≥0) : ℝ≥0∞) ≤ firstEntrance U (pathCoord γ) ∧ firstEntrance U (pathCoord (capAt γ n)) = ⊤) := fun n => by
    rcases lt_or_ge (firstEntrance U (pathCoord γ)) (n : ℝ≥0) with h | h
    · exact Or.inl ⟨h, firstEntrance_capAt_of_lt hU hγ h⟩
    · exact Or.inr ⟨h, firstEntrance_capAt_of_le hU hγ h0 h⟩
  refine Prod.ext ?_ (funext fun q => ?_)
  · show (entHist U γ).1 = ⨅ n : ℕ, (entHist U (capAt γ n)).1
    simp only [entHist_fst]
    refine le_antisymm (le_iInf fun n => ?_) ?_
    · rcases hTn n with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
      exact le_top
    · rcases eq_or_ne (firstEntrance U (pathCoord γ)) ⊤ with htop | htop
      · rw [htop]; exact le_top
      · set n : ℕ := ⌈(firstEntrance U (pathCoord γ)).toNNReal⌉₊ + 1
        have hlt : firstEntrance U (pathCoord γ) < ((n : ℝ≥0) : ℝ≥0∞) := by
          rw [← ENNReal.coe_toNNReal htop, ENNReal.coe_lt_coe]
          exact lt_ceil_add_one _
        exact (iInf_le _ n).trans (firstEntrance_capAt_of_lt hU hγ hlt).le
  · set n : ℕ := ⌈(q : ℝ≥0)⌉₊ + 1 with hn
    have hqn : (q : ℝ≥0) < (n : ℝ≥0) := lt_ceil_add_one _
    show stopCoord (pathCoord γ) (firstEntrance U (pathCoord γ)) q = stopCoord (pathCoord (capAt γ n)) (firstEntrance U (pathCoord (capAt γ n))) q
    have hcq : pathCoord (capAt γ n) q = pathCoord γ q := capAt_of_le γ hqn.le
    rcases hTn n with ⟨-, e⟩ | ⟨hle, e⟩
    · rw [e]
      simp only [stopCoord, hcq]
    · rw [e]
      have hqT : (((q : ℝ≥0) : ℝ≥0∞)) ≤ firstEntrance U (pathCoord γ) := (ENNReal.coe_le_coe.2 hqn.le).trans hle
      simp only [stopCoord, hqT, le_top, ↓reduceIte, hcq]

theorem measurable_joinHist : Measurable joinHist := by
  refine Measurable.prodMk (Measurable.iInf fun n => measurable_fst.comp (measurable_pi_apply n)) ?_
  exact Measurable.of_eval fun q =>
    (measurable_pi_apply q).comp (measurable_snd.comp (measurable_pi_apply (⌈(q : ℝ≥0)⌉₊ + 1)))

end Path

/-! ### History locality of the complete path -/

/-- The marked history σ-algebra of an event that always holds is the σ-algebra of the history. -/
theorem markedHistSigma_univ {Ω' : Type*} {X : Type*} [MeasurableSpace X] (Y : Ω' → X) :
    markedHistSigma (univ : Set Ω') Y = MeasurableSpace.comap Y inferInstance := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ ⟨B, hB, rfl⟩
    exact ⟨B, hB, by rw [univ_inter]⟩
  · rintro _ ⟨B, hB, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨B, hB, by rw [univ_inter]⟩


section Local

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem measurable_entHist {U : Set ℂ} (hU : MeasurableSet U) {η : Ω → ℝ≥0 → ℂ}
    (hηm : ∀ t, Measurable fun ω => η ω t) : Measurable fun ω => entHist U (η ω) := by
  have hc : Measurable fun ω => pathCoord (η ω) := Measurable.of_eval fun q => hηm q
  exact measurable_histOf.comp (((measurable_firstEntrance hU).comp hc).prodMk hc)

/-- **Lemma 6.2's history locality of a complete path from that of its finite prefixes** ("the extension to complete
outer curves is obtained by increasing finite prefixes", p. 225). Let `η` be continuous for every `ω`, measurable at
each time and started on `ℝ`. If for every `n ∈ ℕ` the frozen path `η(· ∧ n)` has the history-sensitive locality at
first entrance times, so does `η`. -/
theorem isEntranceHistoryLocal_of_capAt {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {η : Ω → ℝ≥0 → ℂ} (hc : ∀ ω, Continuous (η ω))
    (hηm : ∀ t, Measurable fun ω => η ω t) (h0 : ∀ ω, η ω 0 ∉ H)
    (hcap : ∀ n : ℕ, IsEntranceHistoryLocal (fun ω => capAt (η ω) n) h P) : IsEntranceHistoryLocal η h P := by
  intro U G hUH hG hd
  have hUo : IsOpen (U : Set ℂ) := U.isOpen
  have h0U : ∀ ω, η ω 0 ∉ (U : Set ℂ) := fun ω hω => h0 ω (hUH hω)
  have h0Un : ∀ (n : ℝ≥0) ω, capAt (η ω) n 0 ∉ (U : Set ℂ) := fun n ω => by rw [capAt_zero]; exact h0U ω
  have hEu : {ω | AvoidsUpTo (η ω) (firstEntrance U (pathCoord (η ω))) U} = univ :=
    eq_univ_of_forall fun ω => avoidsUpTo_firstEntrance hUo (hc ω) (h0U ω)
  have hEn : ∀ n : ℕ, {ω | AvoidsUpTo (capAt (η ω) n) (firstEntrance U (pathCoord (capAt (η ω) n))) U} = univ :=
    fun n => eq_univ_of_forall fun ω => avoidsUpTo_firstEntrance hUo (continuous_capAt (hc ω) n) (h0Un n ω)
  have hηnm : ∀ (n : ℝ≥0) t, Measurable fun ω => capAt (η ω) n t := fun n t => hηm _
  set 𝒦 : ℕ → MeasurableSpace Ω := fun n =>
    MeasurableSpace.comap (fun ω => entHist U (capAt (η ω) n)) inferInstance with h𝒦def
  have hYn : ∀ n : ℕ, Measurable fun ω => entHist U (capAt (η ω) n) := fun n =>
    measurable_entHist hUo.measurableSet (hηnm n)
  have hGle : MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance ≤ mΩ :=
    ((LocalSets.measurable_markovCompl hG).comp hhm).comap_le
  have hBle : MeasurableSpace.comap (fun ω => G (h ω)) inferInstance ≤ mΩ := (hG.comp hhm).comap_le
  have hind : ∀ n, CondIndepEv (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) (𝒦 n)
      (MeasurableSpace.comap (fun ω => G (h ω)) inferInstance) P := fun n => by
    have h1 := hcap n U G hUH hG hd
    simp only [hEn n] at h1
    rw [markedHistSigma_univ] at h1
    exact h1
  have hmono : Monotone 𝒦 := monotone_nat_of_le_succ fun n => by
    have e : (fun ω => entHist U (capAt (η ω) n)) =
        (restrictHist n) ∘ fun ω => entHist U (capAt (η ω) ((n + 1 : ℕ) : ℝ≥0)) :=
      funext fun ω => entHist_capAt_eq_restrictHist hUo (hc ω) (h0U ω) n
    show MeasurableSpace.comap (fun ω => entHist U (capAt (η ω) n)) inferInstance ≤ 𝒦 (n + 1)
    rw [e]
    exact ((measurable_restrictHist n).comp (comap_measurable _)).comap_le
  have hjoin : MeasurableSpace.comap (fun ω => entHist U (η ω)) inferInstance ≤ ⨆ n, 𝒦 n := by
    have e : (fun ω => entHist U (η ω)) = joinHist ∘ fun ω n => entHist U (capAt (η ω) n) :=
      funext fun ω => entHist_eq_joinHist hUo (hc ω) (h0U ω)
    rw [e]
    have hcomp : Measurable[⨆ n, 𝒦 n] fun ω (n : ℕ) => entHist U (capAt (η ω) (n : ℝ≥0)) :=
      @Measurable.of_eval Ω ℕ (fun _ => Hist) (⨆ n, 𝒦 n) _ _ fun n =>
        (comap_measurable (fun ω => entHist U (capAt (η ω) (n : ℝ≥0)))).mono (le_iSup 𝒦 n) le_rfl
    have hm : Measurable[⨆ n, 𝒦 n] (joinHist ∘ fun ω (n : ℕ) => entHist U (capAt (η ω) (n : ℝ≥0))) :=
      measurable_joinHist.comp hcomp
    exact measurable_iff_comap_le.1 hm
  have hfin := condIndepEv_of_le_iSup hGle hBle hmono (fun n => (hYn n).comap_le) hind hjoin
  rw [hEu, markedHistSigma_univ]
  exact hfin

end Local

end InteractingSLE.Sec7.Lemma71G
