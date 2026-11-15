/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HOuterGeo
import InteractingSLE.Spec.Restart.RetPlumbProofFilled

/-!
# Theorem R.7's outer pockets: the marked union law for the relative hull sets

Packet PROVE-HOUTER. Supplement §5.5, Corollary "the full stopped Gaussian kernel" (`source/spec/p433-480.md`
L1010–L1015, p. 475: "The relative-history stopping rule is handled by the inverse clock and the marked optional union
law"), and Aux. lemma 124's union law of `B ∪ R_T` (`source/spec/p385-432.md` L171–L196).

For a contained pocket the union law of `B ∪ R_{T(q)}` (with `B = ℍ ∖ C`) is the union law of the relative complement,
because the relative active domain is `C ∩ D_{T(q)}` (PROVE-STRIPSYS32/41/43). For a mixed or outer pocket the
relative active domain `C ∩ ψ⁻¹(ℍ ∖ K_q)` is smaller (inactive outer bulges stay in `D_{T(q)}`), and the set needed by
the stop-level statement is `extHullSet C (relHull C ψ γ q) = ℍ ∖ (C ∩ ψ⁻¹(ℍ ∖ K_q))`. It is obtained here from the
walls' marked union law at the ambient stop `T⁰(q)` (`PocketStopWallsLaw` for `m(walls) ∪ R_{T⁰(q)}`, the landed form
of Aux. lemma 35's law) by monotonicity of the history-marked avoidance criterion: the larger set is measurable for the
relative history, since on an open `U ⊆ ℍ`

  `U ⊆ C ∩ ψ⁻¹(ℍ ∖ K_q)` iff `U` misses `m(walls) ∪ R_{T⁰(q)}`, the dense points of `U` lie in `C`, and their
  `ψ`-images are off `K_q` (`disjoint_extHullSet_relHull_iff`),

where the last condition is an event of `𝓦 ∨ σ(prefix events up to q)` (`K_q` is the filling of the prefix of the
traversal up to capacity `q`; `measurableSet_notMem_fillH`).

## Main results

* `notMem_of_mem_Ioc_fibre'`, `notMem_of_mem_Ioc_fibreInf'`: no pocket visit between the two ends of a clock fibre of
  an erasure pocket;
* `mem_hull_of_mem_image`, `mem_hull_of_mem_imageInf`: a pocket point whose Jordan image is on the erased prefix up to
  `u` is in the ambient hull at the left fibre end of `u`;
* `disjoint_extHullSet_relHull_iff` (deterministic criterion), `measurableSet_notMem_fillH`;
* **`pocketStopUnionLaw_relHull_of_wallsLaw`**: `PocketStopUnionLaw` for the relative hull sets from
  `PocketStopWallsLaw` at any ambient stop whose hull contains the erased prefix's pocket points and misses the relative
  active domain.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar fwdHull)
open SupercriticalConformalCovariance (IsConformalBijection)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.HOuter

open Sec6 PocketTraversal Lemma71C R7StopIn PocketStopWallsFin

/-! ### No visit inside a clock fibre; pocket points on the erased prefix are in the hull -/

section Fibre

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **No visit to the pocket between the two ends of a fibre** (erasure form of
`PocketStopWallsFin.notMem_of_mem_Ioc_fibre`): `η(t) ∉ C` for `t ∈ (fL(v), fR(v)]`. -/
theorem notMem_of_mem_Ioc_fibre' (hP : IsErasurePocket η C x₀ y₀ τ σ) {v : ℝ}
    (hv : v ∈ Ico 0 (pocketClock η C τ σ σ)) {t : ℝ}
    (ht : t ∈ Ioc (pocketFibreLeft η C τ σ v) (pocketFibre η C τ σ v)) : η t ∉ C := by
  set a := pocketFibreLeft η C τ σ v with ha
  set b := pocketFibre η C τ σ v with hb
  have hab : a < b := ht.1.trans_le ht.2
  have hv' : v ∈ Icc (pocketClock η C τ σ τ) (pocketClock η C τ σ σ) := by
    rw [IsErasurePocket.clock_τ]; exact ⟨hv.1, hv.2.le⟩
  have hτa : τ ≤ a := (fibreLeft_mem hP.continuous_clock hP.lt.le v).1
  have hbσ : b < σ := hP.fibre_lt_σ hv
  have hclk : pocketClock η C τ σ a = pocketClock η C τ σ b := by
    rw [ha, hb, pocketFibreLeft, clock_fibreLeft hP.continuous_clock hP.monotone_clock hP.lt.le hv',
      hP.clock_fibre ⟨hv.1, hv.2.le⟩]
  have hno : ∀ t' ∈ Ioo a b, η t' ∉ C := fun t' ht' ht'C =>
    notMem_of_erasureClock_eq hP.isOpen_visitSet hclk ht'
      ⟨⟨hτa.trans_lt ht'.1, ht'.2.trans hbσ⟩, ht'C⟩
  rcases ht.2.lt_or_eq with htb | htb
  · exact hno t ⟨ht.1, htb⟩
  · rw [htb]
    exact notMem_right_of_notMem_Ioo hP.cont hP.isOpen (hP.nonneg.trans hτa) hab hno

/-- **A pocket point on the Jordan image of the erased prefix up to `u` is in the ambient hull at the left end of the
fibre of `u`** (bounded erasure pocket): by injectivity of the coordinate on `C̄ ∖ {x₀}`, (GC2), and no visit inside
the fibre. -/
theorem mem_hull_of_mem_image (hP : IsErasurePocket η C x₀ y₀ τ σ) (hη : IsLoewnerTrace W η) (hCH : C ⊆ H)
    (hψ : IsJordanCoord C x₀ y₀ ψ) {u : ℝ} (hu : u ∈ Ico 0 (pocketClock η C τ σ σ)) {y : ℂ} (hyC : y ∈ C)
    (hy : ψ y ∈ (fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 u) :
    y ∈ fwdHull W (pocketFibreLeft η C τ σ u) := by
  obtain ⟨v, hv, hvy⟩ := hy
  have hvI : v ∈ Ico 0 (pocketClock η C τ σ σ) := ⟨hv.1, hv.2.trans_lt hu.2⟩
  have hyx : y ∈ closure C \ {x₀} := ⟨subset_closure hyC, fun h => hP.notMem_x (h ▸ hyC)⟩
  have he : erasedPath η C τ σ v = y := hψ.2.1 (hP.erasedPath_mem hvI) hyx hvy
  have hmem : y ∈ erasedPath η C τ σ '' Icc 0 u ∩ C := ⟨⟨v, hv, he⟩, hyC⟩
  rw [hP.erasedPath_image_inter ⟨hu.1, hu.2.le⟩] at hmem
  obtain ⟨⟨t, ht, rfl⟩, htC⟩ := hmem
  have hv' : u ∈ Icc (pocketClock η C τ σ τ) (pocketClock η C τ σ σ) := by
    rw [IsErasurePocket.clock_τ]; exact ⟨hu.1, hu.2.le⟩
  have hs₀ := fibreLeft_mem hP.continuous_clock hP.lt.le u
  have hts : t ≤ pocketFibreLeft η C τ σ u := by
    by_contra hlt
    exact notMem_of_mem_Ioc_fibre' hP hu ⟨not_le.1 hlt, ht.2⟩ htC
  exact Sec6.mem_fwdHull_of_mem_trace hη (hP.nonneg.trans hs₀.1) (hCH htC) ⟨t, ⟨ht.1, hts⟩, rfl⟩

end Fibre

section FibreInf

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-- The left end of a fibre at infinity is in its fibre and before the right end (erasure form). -/
theorem pocketFibreLeftInf_props (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ} (hv : v ∈ Ico 0 (clockEnd η C τ)) :
    τ ≤ pocketFibreLeftInf η C τ v ∧ v ≤ pocketClockInf η C τ (pocketFibreLeftInf η C τ v) ∧
      pocketFibreLeftInf η C τ v ≤ pocketFibreInf η C τ v := by
  obtain ⟨T, hτT, hvT⟩ := hP.exists_clock_gt hv.2
  have hmem := (isClosed_Ici.inter (isClosed_le continuous_const hP.continuous_clock)).csInf_mem
    (s := {t ∈ Ici τ | v ≤ pocketClockInf η C τ t}) ⟨T, hτT, hvT.le⟩ ⟨τ, fun _ ht => ht.1⟩
  exact ⟨hmem.1, hmem.2, csInf_le ⟨τ, fun _ ht => ht.1⟩ ⟨hP.fibre_mem hv, (hP.clock_fibre hv).ge⟩⟩

/-- **No visit to the pocket between the two ends of a fibre at infinity** (erasure form). -/
theorem notMem_of_mem_Ioc_fibreInf' (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) {t : ℝ}
    (ht : t ∈ Ioc (pocketFibreLeftInf η C τ v) (pocketFibreInf η C τ v)) : η t ∉ C := by
  set a := pocketFibreLeftInf η C τ v with ha
  set b := pocketFibreInf η C τ v with hb
  obtain ⟨hτa, hva, hab'⟩ := pocketFibreLeftInf_props hP hv
  have hab : a < b := ht.1.trans_le ht.2
  have hclk : pocketClockInf η C τ a = pocketClockInf η C τ b := by
    refine le_antisymm ?_ ?_
    · exact hP.monotone_clock hab'
    · rw [hb, hP.clock_fibre hv]; exact hva
  have hno : ∀ t' ∈ Ioo a b, η t' ∉ C := fun t' ht' ht'C =>
    notMem_of_erasureClock_eq hP.isOpen_visitSet hclk ht' ⟨hτa.trans_lt ht'.1, ht'C⟩
  rcases ht.2.lt_or_eq with htb | htb
  · exact hno t ⟨ht.1, htb⟩
  · rw [htb]
    exact notMem_right_of_notMem_Ioo hP.cont hP.isOpen (hP.nonneg.trans hτa) hab hno

/-- **A pocket point on the Jordan image of the erased prefix up to `u` is in the ambient hull at the left end of the
fibre of `u`** (erasure pocket opening at the flow seed). -/
theorem mem_hull_of_mem_imageInf (hP : IsErasurePocketInf η C y₀ τ) (hη : IsLoewnerTrace W η) (hCH : C ⊆ H)
    (hψ : IsJordanCoordInf C y₀ ψ) {u : ℝ} (hu : u ∈ Ico 0 (clockEnd η C τ)) {y : ℂ} (hyC : y ∈ C)
    (hy : ψ y ∈ (fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 u) :
    y ∈ fwdHull W (pocketFibreLeftInf η C τ u) := by
  obtain ⟨v, hv, hvy⟩ := hy
  have hvI : v ∈ Ico 0 (clockEnd η C τ) := ⟨hv.1, hv.2.trans_lt hu.2⟩
  have he : erasedPathInf η C τ v = y := hψ.2.1 (hP.erasedPath_mem hvI) (subset_closure hyC) hvy
  have hmem : y ∈ erasedPathInf η C τ '' Icc 0 u ∩ C := ⟨⟨v, hv, he⟩, hyC⟩
  rw [hP.erasedPath_image_inter hu] at hmem
  obtain ⟨⟨t, ht, rfl⟩, htC⟩ := hmem
  obtain ⟨hτa, -, -⟩ := pocketFibreLeftInf_props hP hu
  have hts : t ≤ pocketFibreLeftInf η C τ u := by
    by_contra hlt
    exact notMem_of_mem_Ioc_fibreInf' hP hu ⟨not_le.1 hlt, ht.2⟩ htC
  exact Sec6.mem_fwdHull_of_mem_trace hη (hP.nonneg.trans hτa) (hCH htC) ⟨t, ⟨ht.1, hts⟩, rfl⟩

end FibreInf

/-! ### The deterministic criterion -/

/-- **Avoidance of the relative complement** (deterministic): for an open pocket `C ⊆ ℍ` bounded in `ℍ` by walls `Γ`,
a coordinate `ψ : C → ℍ` continuous on `C`, a hull `K_q = fill(Z)` (`Z` closed), and an ambient hull `F₀` with
`C ∩ ψ⁻¹(ℍ ∖ fill Z) ⊆ ℍ ∖ F₀` and `C ∩ ψ⁻¹(Z) ⊆ F₀`: an open `U ⊆ ℍ` misses `ℍ ∖ (C ∩ ψ⁻¹(ℍ ∖ K_q))` iff it misses
`ℍ ∩ (Γ ∪ F₀)`, the points of a dense sequence in `U` lie in `C`, and their `ψ`-images are off `fill Z`. -/
theorem disjoint_extHullSet_relHull_iff {C Γ F₀ U Z : Set ℂ} {ψ : ℂ → ℂ} {γ : ℝ → ℂ} {q : ℝ≥0}
    (hCo : IsOpen C) (hΓC : Disjoint (H ∩ Γ) C) (hfr : frontier C ∩ H ⊆ Γ) (hψc : ContinuousOn ψ C)
    (hψH : MapsTo ψ C H) (hKZ : fwdHull (fun s : ℝ => segDriver γ s.toNNReal) q = fillH Z) (hZc : IsClosed Z)
    (hDF : C ∩ ψ ⁻¹' (H \ fillH Z) ⊆ H \ F₀) (hZF : ∀ y ∈ C, ψ y ∈ Z → y ∈ F₀) (hUo : IsOpen U) (hUH : U ⊆ H)
    {e : ℕ → ℂ} (he : DenseRange e) :
    Disjoint (PocketUnionPt.extHullSet C (relHull C ψ γ q)) U ↔
      Disjoint (H ∩ (Γ ∪ F₀)) U ∧ (∀ n, e n ∈ U → e n ∈ C) ∧ ∀ n, e n ∈ U → ψ (e n) ∉ fillH Z := by
  set D := C ∩ ψ ⁻¹' (H \ fillH Z) with hDdef
  have hrel : relHull C ψ γ q = H \ D := by rw [relHull, hKZ]
  have hiff : Disjoint (PocketUnionPt.extHullSet C (relHull C ψ γ q)) U ↔ U ⊆ D := by
    rw [hrel]
    constructor
    · intro hd z hzU
      by_contra hzD
      exact Set.disjoint_left.1 hd ⟨hUH hzU, Or.inr ⟨hUH hzU, hzD⟩⟩ hzU
    · intro hsub
      refine Set.disjoint_left.2 fun z hz hzU => ?_
      rcases hz.2 with hzC | hzD
      · exact hzC (hsub hzU).1
      · exact hzD.2 (hsub hzU)
  rw [hiff]
  constructor
  · intro hsub
    refine ⟨Set.disjoint_left.2 fun z hz hzU => ?_, fun n hn => (hsub hn).1, fun n hn => (hsub hn).2.2⟩
    rcases hz.2 with hΓ | hF
    · exact Set.disjoint_left.1 hΓC ⟨hz.1, hΓ⟩ (hsub hzU).1
    · exact (hDF (hsub hzU)).2 hF
  · rintro ⟨hd, hpt, hrelpt⟩
    have hd' := (PocketStopField.disjoint_extHullSet_iff (F := F₀) hCo hΓC hfr hUo hUH he).2 ⟨hd, hpt⟩
    have hUC : ∀ z ∈ U, z ∈ C ∧ z ∉ F₀ := fun z hz => by
      have hz' : z ∉ PocketUnionPt.extHullSet C F₀ := fun h => Set.disjoint_left.1 hd' h hz
      simp only [PocketUnionPt.extHullSet, mem_inter_iff, mem_union, mem_compl_iff, not_and, not_or,
        not_not] at hz'
      exact hz' (hUH hz)
    intro z hzU
    set V := connectedComponentIn U z with hV
    have hVo : IsOpen V := hUo.connectedComponentIn
    have hzV : z ∈ V := mem_connectedComponentIn hzU
    have hVU : V ⊆ U := connectedComponentIn_subset U z
    have hVC : V ⊆ C := fun y hy => (hUC y (hVU hy)).1
    obtain ⟨n, hn⟩ := he.exists_mem_open hVo ⟨z, hzV⟩
    have hnU : e n ∈ U := hVU hn
    have hnH : ψ (e n) ∈ H := hψH (hVC hn)
    have hnZ : ψ (e n) ∉ closure Z := fun h => hrelpt n hnU ⟨hnH, Or.inl h⟩
    have hnb : ¬ IsBounded (connectedComponentIn (H \ closure Z) (ψ (e n))) :=
      fun h => hrelpt n hnU ⟨hnH, Or.inr h⟩
    have hVpre : IsPreconnected (ψ '' V) := isPreconnected_connectedComponentIn.image _ (hψc.mono hVC)
    have hVsub : ψ '' V ⊆ H \ closure Z := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hψH (hVC hy), fun hyZ => ?_⟩
      rw [hZc.closure_eq] at hyZ
      exact (hUC y (hVU hy)).2 (hZF y (hVC hy) hyZ)
    have hcomp := hVpre.subset_connectedComponentIn ⟨e n, hn, rfl⟩ hVsub
    have hzc : ψ z ∈ connectedComponentIn (H \ closure Z) (ψ (e n)) := hcomp ⟨z, hzV, rfl⟩
    refine ⟨(hUC z hzU).1, hψH (hUC z hzU).1, fun hzK => ?_⟩
    rcases hzK.2 with hzcl | hzb
    · exact (hVsub ⟨z, hzV, rfl⟩).2 hzcl
    · rw [← connectedComponentIn_eq hzc] at hzb
      exact hnb hzb

/-! ### A random point off a random filled compact set -/

section Meas

variable {Ω : Type*}

/-- **A random point of `ℍ` off a random filled compact set is an event**: for an `ℋ`-event `S`, a point `p` whose
indicator on `S` is `ℋ`-measurable and which lies in `ℍ` on `S`, and compact `K ω` with `ℋ`-measurable dyadic hitting
events, `{ω ∈ S | p ω ∉ fill(K ω)}` is an `ℋ`-event (`ℍ ∖ fill(K ω)` is open: test the balls of a dense sequence with
radii `1/(k + 1)` contained in `ℍ`, whose avoidance events are hitting events of `fill ∘ K`). -/
theorem measurableSet_notMem_fillH {ℋ : MeasurableSpace Ω} {S : Set Ω} (hS : MeasurableSet[ℋ] S) {p : Ω → ℂ}
    (hp : Measurable[ℋ] (S.indicator p)) (hpH : ∀ ω ∈ S, p ω ∈ H) {K : Ω → Set ℂ}
    (hK : @Restart.IsDyadicHitMeasurable Ω ℋ K) (hKc : ∀ ω, IsCompact (K ω)) :
    MeasurableSet[ℋ] {ω | ω ∈ S ∧ p ω ∉ fillH (K ω)} := by
  classical
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  set B : ℕ → ℕ → Set ℂ := fun m k => ball (e m) (1 / ((k : ℝ) + 1)) with hB
  have hfill : Measurable[ℋ, hittingSigma] fun ω => fillH (K ω) :=
    @Restart.RetAux79.measurable_fillH_of_dyadic Ω ℋ K hK hKc
  set T : ℕ → ℕ → Set Ω := fun m k => if B m k ⊆ H then
    S ∩ ((S.indicator p) ⁻¹' B m k ∩ {ω | Disjoint (fillH (K ω)) (B m k)}) else ∅ with hT
  have hTm : ∀ m k, MeasurableSet[ℋ] (T m k) := by
    intro m k
    by_cases hBH : B m k ⊆ H
    · simp only [hT, hBH, ↓reduceIte]
      refine hS.inter ((hp isOpen_ball.measurableSet).inter ?_)
      exact hfill (LocalSets.measurableSet_avoid isOpen_ball hBH)
    · simp only [hT, hBH, ↓reduceIte]
      exact MeasurableSet.empty
  convert MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun k => hTm m k using 1
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨hωS, hpK⟩
    have hopen : IsOpen (H \ fillH (K ω)) := InteractingSLE.isOpen_H_diff_fillH (hKc ω).isBounded
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen (p ω) ⟨hpH ω hωS, hpK⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨m, hm⟩ := Metric.denseRange_iff.1 he (p ω) (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
    have hsub : B m k ⊆ H \ fillH (K ω) := by
      intro z hz
      refine hball ?_
      rw [mem_ball] at hz ⊢
      calc dist z (p ω) ≤ dist z (e m) + dist (e m) (p ω) := dist_triangle _ _ _
        _ < 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := add_lt_add hz (by rw [dist_comm]; exact hm)
        _ < ε / 2 + ε / 2 := add_lt_add hk hk
        _ = ε := add_halves ε
    have hBH : B m k ⊆ H := fun z hz => (hsub hz).1
    refine ⟨m, k, ?_⟩
    simp only [hT, hBH, ↓reduceIte]
    refine ⟨hωS, ?_, Set.disjoint_right.2 fun z hz => (hsub hz).2⟩
    rw [mem_preimage, indicator_of_mem hωS, mem_ball]
    exact hm
  · rintro ⟨m, k, hmk⟩
    by_cases hBH : B m k ⊆ H
    · simp only [hT, hBH, ↓reduceIte] at hmk
      obtain ⟨hωS, hpB, hd⟩ := hmk
      rw [mem_preimage, indicator_of_mem hωS] at hpB
      exact ⟨hωS, fun h => Set.disjoint_left.1 hd h hpB⟩
    · simp only [hT, hBH, ↓reduceIte] at hmk
      exact hmk.elim

end Meas

/-! ### The marked union law of the relative complement -/

section Union

open PocketCoupling PocketStop PocketStopField PocketUnionPt WholeField

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The marked union law for the relative hull sets from the walls' marked union law at an ambient stop**
(Aux. lemma 124 from Aux. lemma 35 for a mixed or outer pocket): on the walls' event `A`, if the pocket `C` is open,
bounded in `ℍ` by the walls `Γ`, its points are walls' events, the coordinate `ψ` is measurable for the walls at fixed
points, continuous on `C` and maps `C` into `ℍ`, the traversal `γ` is driven, and the ambient hull `F₀` at the stop
misses the relative active domain and contains every pocket point whose image is on the traversal's prefix, then
`PocketStopWallsLaw` for `Γ ∪ F₀` gives `PocketStopUnionLaw` for the relative hull sets `relHull C ψ γ q`. -/
theorem pocketStopUnionLaw_relHull_of_wallsLaw {A : Set Ω} {γ : Ω → ℝ → ℂ} {q : ℝ≥0} (h𝓦 : 𝓦 ≤ mΩ)
    (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ) {C Γ F₀ : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hΓC : ∀ ω ∈ A, Disjoint (H ∩ Γ ω) (C ω))
    (hfr : ∀ ω ∈ A, frontier (C ω) ∩ H ⊆ Γ ω) (hψc : ∀ ω ∈ A, ContinuousOn (ψ ω) (C ω))
    (hψH : ∀ ω ∈ A, MapsTo (ψ ω) (C ω) H) (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hDF : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      C ω ∩ ψ ω ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) ⊆ H \ F₀ ω)
    (hZF : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → ∀ y ∈ C ω,
      ψ ω y ∈ γ ω '' Icc 0 (capInv (γ ω) q) → y ∈ F₀ ω)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hW : PocketStopWallsLaw 𝓦 P A γ Γ F₀ h₀ q) :
    PocketStopUnionLaw 𝓦 P A γ C (fun ω => relHull (C ω) (ψ ω) (γ ω) q) h₀ q := by
  classical
  obtain ⟨E', hE'm, hE'loc, hE'eq⟩ := hW
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  set Lv : Set Ω := {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} with hLv
  have hLvH : MeasurableSet[locPrefixSigma 𝓦 A γ q] Lv := measurableSet_live (𝓦 := 𝓦) A γ q
  have hW𝓗 : 𝓦 ≤ locPrefixSigma 𝓦 A γ q := le_sup_left
  set Frel : Ω → Set ℂ := fun ω => relHull (C ω) (ψ ω) (γ ω) q with hFrel
  -- the traversal's prefix up to capacity `q`, on the live event
  set Kp : Ω → Set ℂ := fun ω => if ω ∈ Lv then γ ω '' Icc 0 (capInv (γ ω) q) else ∅ with hKp
  have hKpc : ∀ ω, IsCompact (Kp ω) := fun ω => by
    by_cases hl : ω ∈ Lv
    · simp only [hKp, hl, ↓reduceIte]
      exact isCompact_Icc.image_of_continuousOn ((hγ ω hl.1).continuousOn.mono fun t ht => ht.1)
    · simp only [hKp, hl, ↓reduceIte]
      exact isCompact_empty
  have hKpm : @Restart.IsDyadicHitMeasurable Ω (locPrefixSigma 𝓦 A γ q) Kp := by
    intro n k
    have e1 : {ω | (Restart.dyadicSquare n k ∩ Kp ω).Nonempty} = A ∩ PocketAdapt.prefixEvent γ q n k := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, PocketAdapt.prefixEvent]
      by_cases hl : ω ∈ Lv
      · simp only [hKp, hl, ↓reduceIte]
        exact ⟨fun h => ⟨hl.1, hl.2, h⟩, fun h => h.2.2⟩
      · simp only [hKp, hl, ↓reduceIte, inter_empty, Set.not_nonempty_empty, false_iff, not_and]
        exact fun hA hq _ => hl ⟨hA, hq⟩
    rw [e1]
    exact le_sup_right (a := 𝓦) _ (MeasurableSpace.measurableSet_generateFrom ⟨q, le_rfl, n, k, rfl⟩)
  -- the relative point events
  set Sn : ℕ → Set Ω := fun n => {ω | ω ∈ A ∧ e n ∈ C ω} with hSn
  set RE : ℕ → Set Ω := fun n => {ω | ω ∈ Sn n ∧ ψ ω (e n) ∉ fillH (Kp ω)} with hRE
  have hREm : ∀ n, MeasurableSet[locPrefixSigma 𝓦 A γ q] (RE n) := fun n =>
    measurableSet_notMem_fillH (hW𝓗 _ (hCm (e n))) ((hψm (e n)).mono hW𝓗 le_rfl)
      (fun ω hω => hψH ω hω.1 hω.2) hKpm hKpc
  set relEv : Set ℂ → Set Ω := fun U => {ω | ∀ n, e n ∈ U → ω ∈ RE n} with hrelEv
  have hrelEvm : ∀ U, MeasurableSet[locPrefixSigma 𝓦 A γ q] (relEv U) := by
    intro U
    have e1 : relEv U = ⋂ n, {ω | e n ∈ U → ω ∈ RE n} := by
      ext ω
      simp only [hrelEv, mem_ofPred_eq, mem_iInter]
    rw [e1]
    refine MeasurableSet.iInter fun n => ?_
    by_cases hn : e n ∈ U
    · simp only [hn, true_imp_iff]
      exact hREm n
    · simp only [hn, false_imp_iff, ofPred_true]
      exact MeasurableSet.univ
  -- the key identity on the live event
  have key : ∀ U : Set ℂ, IsOpen U → U ⊆ H → ∀ ω ∈ Lv,
      (Disjoint (liveExt A γ C Frel q ω) U ↔
        Disjoint (E' ω) U ∧ ω ∈ ptEvent A C e U ∧ ω ∈ relEv U) := by
    intro U hUo hUH ω hω
    have hKω : Kp ω = γ ω '' Icc 0 (capInv (γ ω) q) := by simp only [hKp, hω, ↓reduceIte]
    have hqr : ENNReal.ofReal (q : ℝ) < capLife (γ ω) := by rw [ENNReal.ofReal_coe_nnreal]; exact hω.2
    have hKZ := (hγ ω hω.1).fwdHull_segDriver q.coe_nonneg hqr
    have hDF' : C ω ∩ ψ ω ⁻¹' (H \ fillH (γ ω '' Icc 0 (capInv (γ ω) q))) ⊆ H \ F₀ ω := by
      rw [← hKZ]; exact hDF ω hω.1 hω.2
    rw [liveExt_of_live hω, hE'eq ω hω.1 hω.2,
      disjoint_extHullSet_relHull_iff (hCo ω hω.1) (hΓC ω hω.1) (hfr ω hω.1) (hψc ω hω.1) (hψH ω hω.1) hKZ
        (by rw [← hKω]; exact (hKpc ω).isClosed)
        hDF' (hZF ω hω.1 hω.2) hUo hUH he]
    rw [← hKω]
    constructor
    · rintro ⟨hd, hpt, hrel⟩
      exact ⟨hd, fun n hn => ⟨hω.1, hpt n hn⟩, fun n hn => ⟨⟨hω.1, hpt n hn⟩, hrel n hn⟩⟩
    · rintro ⟨hd, hpt, hrel⟩
      exact ⟨hd, fun n hn => (hpt n hn).2, fun n hn => (hrel n hn).2⟩
  -- off the live event `liveExt = ℍ` meets every nonempty `U ⊆ ℍ`
  have off : ∀ U : Set ℂ, U.Nonempty → U ⊆ H → ∀ ω ∉ Lv, ¬ Disjoint (liveExt A γ C Frel q ω) U := by
    intro U hU hUH ω hω hd
    rw [liveExt_of_not_live hω] at hd
    obtain ⟨z, hz⟩ := hU
    exact Set.disjoint_left.1 hd (hUH hz) hz
  refine ⟨liveExt A γ C Frel q, ?_, ?_, fun ω hω hq => liveExt_of_live ⟨hω, hq⟩⟩
  · -- hitting measurability
    refine @measurable_generateFrom Ω (Set ℂ) mΩ _ _ ?_
    rintro _ ⟨U, hUo, hUH, rfl⟩
    rcases U.eq_empty_or_nonempty with hU | hU
    · have e0 : liveExt A γ C Frel q ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} = ∅ := by
        ext ω
        simp only [hU, inter_empty, Set.not_nonempty_empty, ofPred_false, preimage_empty, mem_empty_iff_false]
      rw [e0]
      exact MeasurableSet.empty
    · have e1 : liveExt A γ C Frel q ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
          Lvᶜ ∪ (Lv ∩ ((E' ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty}) ∪ ((ptEvent A C e U)ᶜ ∪ (relEv U)ᶜ))) := by
        ext ω
        simp only [mem_preimage, mem_ofPred_eq, mem_union, mem_compl_iff, mem_inter_iff]
        rw [← Set.not_disjoint_iff_nonempty_inter, ← Set.not_disjoint_iff_nonempty_inter]
        by_cases hω : ω ∈ Lv
        · rw [key U hUo hUH ω hω]
          tauto
        · exact ⟨fun _ => Or.inl hω, fun _ => off U hU hUH ω hω⟩
      rw [e1]
      have hLm : MeasurableSet[mΩ] Lv := hpre _ hLvH
      exact hLm.compl.union (hLm.inter ((hE'm (MeasurableSpace.measurableSet_generateFrom ⟨U, hUo, hUH, rfl⟩)).union
        ((h𝓦 _ (measurableSet_ptEvent hCm e U)).compl.union (hpre _ (hrelEvm U)).compl)))
  · -- the history-marked locality
    intro U G hUH hG hd F₁ hF₁
    rcases (U : Set ℂ).eq_empty_or_nonempty with hU | hU
    · obtain ⟨g, hg, hge⟩ := hE'loc U G hUH hG hd F₁ hF₁
      refine ⟨g, hg, ?_⟩
      have e0 : {ω | Disjoint (liveExt A γ C Frel q ω) U} ∩ F₁ = {ω | Disjoint (E' ω) U} ∩ F₁ := by
        simp only [hU, disjoint_empty, ofPred_true]
      rw [e0]
      exact hge
    · have hF₂ : MeasurableSet[locPrefixSigma 𝓦 A γ q] (F₁ ∩ Lv ∩ ptEvent A C e U ∩ relEv U) :=
        ((hF₁.inter hLvH).inter (hW𝓗 _ (measurableSet_ptEvent hCm e U))).inter (hrelEvm U)
      obtain ⟨g, hg, hge⟩ := hE'loc U G hUH hG hd _ hF₂
      refine ⟨g, hg, ?_⟩
      have e1 : {ω | Disjoint (liveExt A γ C Frel q ω) U} ∩ F₁ =
          {ω | Disjoint (E' ω) U} ∩ (F₁ ∩ Lv ∩ ptEvent A C e U ∩ relEv U) := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq]
        by_cases hω : ω ∈ Lv
        · rw [key U U.isOpen hUH ω hω]
          tauto
        · exact ⟨fun h => absurd h.1 (off U hU hUH ω hω), fun h => absurd h.2.1.1.2 hω⟩
      rw [e1]
      exact hge

end Union

end InteractingSLE.Sec7.HOuter
