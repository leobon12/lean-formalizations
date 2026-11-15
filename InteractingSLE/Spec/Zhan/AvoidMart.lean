/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Localize
import InteractingSLE.Spec.Ito.Bracket
import InteractingSLE.Spec.Ito.Measurability
import QuantumZipper.Proofs.ItoLite.OptionalStopping

/-!
# A positive Itô observable with nonpositive drift has finite quadratic variation

Packet PROVE-ZHAN-B. Astra, *Formalization proofs and dependency audit* (`source/external/AstraIG1/`,
text dump L1200–1206 and L1373–1376, ruling R35): "a convergent continuous local martingale has bounded
paths almost surely; stopping at levels `N` gives finite expected quadratic variation, and the union of
the no-exit events over `N` proves finiteness on convergent paths"; in the avoidance lemma, the strip
driver is bounded above, so "Brownian motion is unbounded above, so `S < ∞`".

The form proved here needs no stochastic integral and no time change. Let `B` be a Brownian motion with
continuous paths, `Λ` an adapted path in a finite-dimensional space solving `Λ' = Ψ(Λ, B)`, and `Φ ≥ 0`
a `C³` function on an open set `U` that contains `(Λ_t, B_t)` for all `t`, whose Itô drift
`itoGen Φ p (Ψ p) = ∂_Λ Φ · Ψ + ½ ∂²_x Φ` is `≤ 0` along the path. Then almost surely
`∫₀^∞ (∂_x Φ(Λ_s, B_s))² ds < ∞` (`ae_bddAbove_integral_sq_partialSnd`).

Proof. Localize at the first exit `σ_{n,L}` from `{dist(·, Uᶜ) > 1/(n+1), ‖·‖ < n, Φ < L}`, capped at
`n` (the localized Itô formula `Ito.martingale_itoLocalized` applies there). Optional stopping for `Φ`
gives `E Φ(X_σ) ≤ Φ₀`, so the probability that `Φ` ever reaches `L` is at most `Φ₀/L`. For
`H = Φ² − 2LΦ` the drift is `(∂_x Φ)² + 2(Φ − L) itoGen Φ ≥ (∂_x Φ)²` while `Φ ≤ L`, and `H ≤ 0` there, so
`E ∫₀^σ (∂_x Φ)² ≤ 2LΦ₀`. On paths along which `Φ` stays below `L` the stopping times exhaust `[0, ∞)`;
Markov's inequality and `L → ∞` conclude.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

/-! ### The exit and keep sets -/

section Sets

variable {E : Type*} [NormedAddCommGroup E] {U : Set (E × ℝ)}
  {Φ : E × ℝ → ℝ} {L : ℝ} {n : ℕ}

/-- The exit set of the localization at level `(n, L)`: within `1/(n+1)` of `Uᶜ`, of norm `≥ n`,
or `Φ ≥ L`. -/
def exitSet (U : Set (E × ℝ)) (Φ : E × ℝ → ℝ) (L : ℝ) (n : ℕ) : Set (E × ℝ) :=
  {p | infDist p Uᶜ ≤ 1 / ((n : ℝ) + 1) ∨ (n : ℝ) ≤ ‖p‖ ∨ (p ∈ U ∧ L ≤ Φ p)}

/-- The compact region kept up to the exit time. -/
def keepSet (U : Set (E × ℝ)) (Φ : E × ℝ → ℝ) (L : ℝ) (n : ℕ) : Set (E × ℝ) :=
  {p | 1 / ((n : ℝ) + 1) ≤ infDist p Uᶜ ∧ ‖p‖ ≤ n ∧ Φ p ≤ L}

theorem mem_of_one_div_le_infDist {p : E × ℝ}
    (hp : 1 / ((n : ℝ) + 1) ≤ infDist p Uᶜ) : p ∈ U := by
  by_contra hpU
  have : infDist p Uᶜ = 0 := infDist_zero_of_mem hpU
  have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem keepSet_subset : keepSet U Φ L n ⊆ U := fun _ hp =>
  mem_of_one_div_le_infDist hp.1

/-- The set `{dist(·, Uᶜ) ≥ 1/(n+1), ‖·‖ ≤ n}` is closed. -/
theorem isClosed_infDist_norm : IsClosed {p : E × ℝ | 1 / ((n : ℝ) + 1) ≤ infDist p Uᶜ ∧ ‖p‖ ≤ n} :=
  (isClosed_le continuous_const (continuous_infDist_pt _)).inter
    (isClosed_le continuous_norm continuous_const)

theorem isClosed_keepSet (hΦ : ContinuousOn Φ U) :
    IsClosed (keepSet U Φ L n) := by
  have hS := isClosed_infDist_norm (E := E) (U := U) (n := n)
  have h := (hΦ.mono fun p hp => mem_of_one_div_le_infDist hp.1).preimage_isClosed_of_isClosed
    hS (isClosed_Iic (a := L))
  convert h using 1
  ext p
  simp only [keepSet, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iic, and_assoc]

theorem isCompact_keepSet [NormedSpace ℝ E] [FiniteDimensional ℝ E] (hΦ : ContinuousOn Φ U) :
    IsCompact (keepSet U Φ L n) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_keepSet hΦ) ?_
  refine (Metric.isBounded_closedBall (x := (0 : E × ℝ)) (r := n)).subset fun p hp => ?_
  rw [mem_closedBall, dist_zero_right]
  exact hp.2.1

theorem isClosed_exitSet (hΦ : ContinuousOn Φ U) :
    IsClosed (exitSet U Φ L n) := by
  set V : Set (E × ℝ) := {p | 1 / ((n : ℝ) + 1) < infDist p Uᶜ ∧ ‖p‖ < n} with hV
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const (continuous_infDist_pt _)).inter
      (isOpen_lt continuous_norm continuous_const)
  have hVU : V ⊆ U := fun p hp => mem_of_one_div_le_infDist hp.1.le
  have ho := (hΦ.mono hVU).isOpen_inter_preimage hVo (isOpen_Iio (a := L))
  rw [← isOpen_compl_iff]
  convert ho using 1
  ext p
  simp only [exitSet, mem_compl_iff, mem_ofPred_eq, not_or, not_le, not_and, mem_inter_iff,
    mem_preimage, mem_Iio, hV]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3 (mem_of_one_div_le_infDist h1.le)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun _ => h3⟩

theorem closure_compl_exitSet_subset (hΦ : ContinuousOn Φ U) :
    closure (exitSet U Φ L n)ᶜ ⊆ keepSet U Φ L n := by
  refine closure_minimal (fun p hp => ?_) (isClosed_keepSet hΦ)
  simp only [exitSet, mem_compl_iff, mem_ofPred_eq, not_or, not_le, not_and] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨h1.le, h2.le, (h3 (mem_of_one_div_le_infDist h1.le)).le⟩

theorem exitSet_succ_subset : exitSet U Φ L (n + 1) ⊆ exitSet U Φ L n := by
  intro p hp
  have h1 : 1 / ((↑(n + 1) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
  have h2 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  rcases hp with hp | hp | hp
  · exact Or.inl (hp.trans h1)
  · exact Or.inr (Or.inl (h2.trans hp))
  · exact Or.inr (Or.inr hp)

end Sets

/-! ### Hitting times of closed sets by continuous paths -/

section Hitting

variable {Ω : Type*} {β : Type*} [TopologicalSpace β] {X : ℝ≥0 → Ω → β} {F : Set β} {ω : Ω}
  {N : ℝ≥0}

/-- A continuous path is in `closure Fᶜ` up to (and including) its hitting time of `F`, if it
starts off `F`. -/
theorem mem_closure_compl_of_le_hittingBtwn (hc : Continuous (X · ω)) (h0 : X 0 ω ∉ F) {t : ℝ≥0}
    (ht : t ≤ hittingBtwn X F 0 N ω) : X t ω ∈ closure Fᶜ := by
  rcases ht.lt_or_eq with hlt | heq
  · exact subset_closure (notMem_of_lt_hittingBtwn hlt zero_le)
  · rcases (zero_le : (0 : ℝ≥0) ≤ t).lt_or_eq with hpos | h0'
    · -- `X t` is a limit of `X s`, `s < t`, all off `F`
      have hlim : Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 (X t ω)) :=
        (hc.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
      refine mem_closure_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact notMem_of_lt_hittingBtwn (hs.trans_eq heq) zero_le
    · rw [← h0']; exact subset_closure h0

/-- A continuous path attains a closed set at its hitting time, if it meets the set before `N`. -/
theorem mem_of_hittingBtwn (hc : Continuous (X · ω)) (hF : IsClosed F)
    (hex : ∃ j ∈ Icc (0 : ℝ≥0) N, X j ω ∈ F) : X (hittingBtwn X F 0 N ω) ω ∈ F := by
  set S : Set ℝ≥0 := Icc 0 N ∩ {i | X i ω ∈ F} with hS
  have hSc : IsClosed S := isClosed_Icc.inter (hF.preimage hc)
  have hSne : S.Nonempty := by obtain ⟨j, hj, hjF⟩ := hex; exact ⟨j, hj, hjF⟩
  have hmem := hSc.csInf_mem hSne (OrderBot.bddBelow S)
  have heq : hittingBtwn X F 0 N ω = sInf S := by simp only [hittingBtwn, hex, ↓reduceIte, hS]
  rw [heq]
  exact hmem.2

end Hitting

/-! ### The generator of `Φ(Φ − 2L)` -/

section Gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E × ℝ → ℝ} {p : E × ℝ}

theorem fderiv_sub_const_eq (c : ℝ) : fderiv ℝ (fun q => Φ q - c) = fderiv ℝ Φ := by
  funext q; exact fderiv_sub_const c

theorem itoGen_sub_const (c : ℝ) (v : E) : Ito.itoGen (fun q => Φ q - c) p v = Ito.itoGen Φ p v := by
  unfold Ito.itoGen Ito.partialFst Ito.partialSndSnd
  rw [fderiv_sub_const_eq c]

theorem partialSnd_sub_const (c : ℝ) : Ito.partialSnd (fun q => Φ q - c) p = Ito.partialSnd Φ p := by
  unfold Ito.partialSnd
  rw [fderiv_sub_const_eq c]

/-- `itoGen (Φ(Φ − 2L)) = 2(Φ − L) itoGen Φ + (∂_x Φ)²`. -/
theorem itoGen_mul_sub (hΦ : ContDiffAt ℝ 2 Φ p) (L : ℝ) (v : E) :
    Ito.itoGen (fun q => Φ q * (Φ q - 2 * L)) p v =
      2 * (Φ p - L) * Ito.itoGen Φ p v + Ito.partialSnd Φ p ^ 2 := by
  have h2 : ContDiffAt ℝ 2 (fun q => Φ q - 2 * L) p := hΦ.sub contDiffAt_const
  rw [Ito.itoGen_mul hΦ h2, itoGen_sub_const, partialSnd_sub_const]
  ring

/-- The Itô drift of a `C³` function on an open set, along a continuous vector field, is
continuous there. -/
theorem continuousOn_itoGen {U : Set (E × ℝ)} (hU : IsOpen U) (hΦ : ContDiffOn ℝ 3 Φ U)
    {Ψ : E × ℝ → E} (hΨ : ContinuousOn Ψ U) : ContinuousOn (fun p => Ito.itoGen Φ p (Ψ p)) U := by
  have h1 : ContinuousOn (fun p => fderiv ℝ Φ p) U := hΦ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hd : ContDiffOn ℝ 1 (fun p => fderiv ℝ Φ p) U := hΦ.fderiv_of_isOpen hU (by norm_num)
  have h2 : ContinuousOn (fun p => fderiv ℝ (fderiv ℝ Φ) p) U :=
    hd.continuousOn_fderiv_of_isOpen hU le_rfl
  unfold Ito.itoGen Ito.partialFst Ito.partialSndSnd
  refine ((h1.clm_comp continuousOn_const).clm_apply hΨ).add (continuousOn_const.mul ?_)
  exact (h2.clm_apply continuousOn_const).clm_apply continuousOn_const

theorem continuousOn_partialSnd {U : Set (E × ℝ)} (hU : IsOpen U) (hΦ : ContDiffOn ℝ 3 Φ U) :
    ContinuousOn (fun p => Ito.partialSnd Φ p) U := by
  have h1 : ContinuousOn (fun p => fderiv ℝ Φ p) U := hΦ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  unfold Ito.partialSnd
  exact h1.clm_apply continuousOn_const

end Gen

/-! ### The localized martingales -/

section PathX

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E] {B : ℝ≥0 → Ω → ℝ} {Λ : ℝ≥0 → Ω → E}

/-- The path `X_t = (Λ_t, B_t)`. -/
def pathX (Λ : ℝ≥0 → Ω → E) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : E × ℝ := (Λ t ω, B t ω)

theorem continuous_pathX (hΛc : ∀ ω, Continuous (Λ · ω)) (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    Continuous fun t => pathX Λ B t ω :=
  (hΛc ω).prodMk (hBc ω)

end PathX

section Mart

open scoped Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] {B : ℝ≥0 → Ω → ℝ} {U : Set (E × ℝ)} {Φ : E × ℝ → ℝ} {Ψ : E × ℝ → E}
  {Λ : ℝ≥0 → Ω → E} {G : Set Ω} {p₀ : E} {L : ℝ} {n : ℕ}

/-- The localizing time: the hitting time of the exit set, capped at `n`, on `G` (`0` off `G`). -/
def locStop (G : Set Ω) (Λ : ℝ≥0 → Ω → E) (B : ℝ≥0 → Ω → ℝ) (U : Set (E × ℝ)) (Φ : E × ℝ → ℝ)
    (L : ℝ) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  if ω ∈ G then hittingBtwn (pathX Λ B) (exitSet U Φ L n) 0 n ω else 0

/-- The density of `Λ` on `G` (`0` off `G`). -/
def locDens (G : Set Ω) (Λ : ℝ≥0 → Ω → E) (B : ℝ≥0 → Ω → ℝ) (Ψ : E × ℝ → E) (s : ℝ) (ω : Ω) : E :=
  if ω ∈ G then Ψ (pathX Λ B s.toNNReal ω) else 0

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem locStop_le (ω : Ω) : locStop G Λ B U Φ L n ω ≤ n := by
  unfold locStop
  split_ifs
  · exact hittingBtwn_le ω
  · exact zero_le

variable (hB : IsFilteredBrownianReal 𝓖 B P) (hBc : ∀ ω, Continuous (B · ω)) (hU : IsOpen U)
  (hΦc : ContinuousOn Φ U) (hΨ : ContinuousOn Ψ U) (hΛm : ∀ t, Measurable[𝓖 t] (Λ t))
  (hΛc : ∀ ω, Continuous (Λ · ω)) (hG : MeasurableSet[𝓖 0] G) (hΛ0 : ∀ ω, Λ 0 ω = p₀)
  (hB0 : ∀ ω, B 0 ω = 0)
  (hpath : ∀ ω ∈ G, ∀ t : ℝ≥0, Λ t ω = p₀ + ∫ s in (0 : ℝ)..t, Ψ (pathX Λ B s.toNNReal ω))
  (hX0 : ((p₀, 0) : E × ℝ) ∉ exitSet U Φ L n)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
include hB hΦc hΛm hΛc hBc hG in
theorem isStoppingTime_locStop :
    IsStoppingTime 𝓖 fun ω => (locStop G Λ B U Φ L n ω : WithTop ℝ≥0) := by
  have hτ := QuantumZipper.ItoLite.isStoppingTime_hittingBtwn_of_isClosed (𝓕 := 𝓖)
    (U := pathX Λ B) (fun t => (hΛm t).prodMk (hB.2.1 t)) (continuous_pathX hΛc hBc)
    (isClosed_exitSet (L := L) (n := n) hΦc) (n : ℝ≥0)
  intro t
  have heq : {ω | (locStop G Λ B U Φ L n ω : WithTop ℝ≥0) ≤ t} =
      (G ∩ {ω | ((hittingBtwn (pathX Λ B) (exitSet U Φ L n) 0 n ω : ℝ≥0) : WithTop ℝ≥0) ≤ t}) ∪
        Gᶜ := by
    ext ω
    by_cases hω : ω ∈ G
    · simp [locStop, hω]
    · simp only [locStop, hω, ↓reduceIte, mem_ofPred_eq, WithTop.coe_zero, mem_union,
        mem_inter_iff, false_and, mem_compl_iff, not_false_eq_true, or_true, iff_true]
      exact_mod_cast (zero_le (a := t))
  rw [heq]
  have hGt : MeasurableSet[𝓖 t] G := 𝓖.mono zero_le _ hG
  exact (hGt.inter (hτ t)).union hGt.compl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
include hΦc hΛc hBc hΛ0 hB0 hX0 in
/-- Up to the localizing time the path stays in the compact keep set. -/
theorem pathX_mem_keepSet {ω : Ω} {t : ℝ≥0} (ht : t ≤ locStop G Λ B U Φ L n ω) :
    pathX Λ B t ω ∈ keepSet U Φ L n := by
  have h0 : pathX Λ B 0 ω ∉ exitSet U Φ L n := by
    simp only [pathX, hΛ0, hB0]; exact hX0
  by_cases hω : ω ∈ G
  · simp only [locStop, hω, ↓reduceIte] at ht
    exact closure_compl_exitSet_subset hΦc
      (mem_closure_compl_of_le_hittingBtwn (continuous_pathX hΛc hBc ω) h0 ht)
  · simp only [locStop, hω, ↓reduceIte, nonpos_iff_eq_zero] at ht
    subst ht
    exact closure_compl_exitSet_subset hΦc (subset_closure h0)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
include hΦc hΨ hΛc hBc hΛ0 hB0 hX0 in
theorem continuousOn_locDens {ω : Ω} :
    ContinuousOn (fun s => locDens G Λ B Ψ s ω) (Icc 0 (locStop G Λ B U Φ L n ω)) := by
  by_cases hω : ω ∈ G
  · simp only [locDens, hω, ↓reduceIte]
    refine hΨ.comp ((continuous_pathX hΛc hBc ω).comp continuous_real_toNNReal).continuousOn
      fun s hs => ?_
    have : s.toNNReal ≤ locStop G Λ B U Φ L n ω := Real.toNNReal_le_iff_le_coe.2 hs.2
    exact keepSet_subset (pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0 this)
  · simp only [locDens, hω, ↓reduceIte]; exact continuousOn_const

include hB hBc hU hΦc hΨ hΛm hΛc hG hΛ0 hB0 hpath hX0 in
/-- **The localized Itô martingale** of a `C³` observable `F` on `U`. -/
theorem martingale_loc {F : E × ℝ → ℝ} (hF : ContDiffOn ℝ 3 F U) :
    Martingale (fun t ω => F (pathX Λ B (min t (locStop G Λ B U Φ L n ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (locStop G Λ B U Φ L n ω) : ℝ≥0),
        Ito.itoGen F (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω)) 𝓖 P := by
  set σ := locStop G Λ B U Φ L n with hσdef
  have hσ := isStoppingTime_locStop hB hBc hΦc hΛm hΛc hG (L := L) (n := n) (U := U)
  have hK := isCompact_keepSet (U := U) (L := L) (n := n) hΦc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hΨ.mono keepSet_subset)
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hΛσm : ∀ t, Measurable[𝓖 t] fun ω => Λ (min t (σ ω)) ω := fun t => by
    have h := Ito.measurable_stopped_of_agree (X := Λ) hσ hΛm (G := univ)
      (@MeasurableSet.univ _ (𝓖 0)) (0 : E) (fun _ _ _ _ => rfl)
      (fun ω _ => (hΛc ω).continuousOn) t
    simpa using h
  refine Ito.martingale_itoLocalized (B := B) (Λ := Λ) (lam := locDens G Λ B Ψ) hB hBc hU hF hK
    keepSet_subset hσ hΛσm (fun ω => ?_) (fun ω t ht => ?_) (Kb := n * max C 0) (fun ω => ?_)
    (fun ω t ht => pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0 ht)
  · exact (continuousOn_locDens hBc hΦc hΨ hΛc hΛ0 hB0 hX0).intervalIntegrable_of_Icc
      (σ ω).coe_nonneg
  · by_cases hω : ω ∈ G
    · rw [hpath ω hω t, hΛ0 ω]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [locDens, hω, ↓reduceIte]
    · have : t = 0 := by
        have h := ht.trans_eq (show σ ω = 0 by simp [hσdef, locStop, hω])
        exact nonpos_iff_eq_zero.1 h
      subst this
      simp
  · have hle : ∀ s ∈ uIoc (0 : ℝ) (σ ω), ‖locDens G Λ B Ψ s ω‖ ≤ max C 0 := by
      intro s hs
      rw [uIoc_of_le (σ ω).coe_nonneg] at hs
      by_cases hω : ω ∈ G
      · simp only [locDens, hω, ↓reduceIte]
        have : s.toNNReal ≤ σ ω := Real.toNNReal_le_iff_le_coe.2 hs.2
        exact (hC _ (pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0 this)).trans (le_max_left _ _)
      · simp [locDens, hω]
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := σ ω)
      (f := fun s => ‖locDens G Λ B Ψ s ω‖) (fun s hs => by rw [norm_norm]; exact hle s hs)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (σ ω).coe_nonneg] at hint
    have h1 : ∫ s in (0 : ℝ)..(σ ω), ‖locDens G Λ B Ψ s ω‖ ≤ max C 0 * (σ ω) :=
      (le_abs_self _).trans hint
    have h2 : ((σ ω : ℝ≥0) : ℝ) ≤ n := by exact_mod_cast locStop_le ω
    nlinarith

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
include hB hBc hΦc hΛm hΛc hG in
/-- The path stopped at the localizing time is measurable. -/
theorem measurable_pathX_locStop :
    Measurable fun ω => pathX Λ B (locStop G Λ B U Φ L n ω) ω := by
  have hσ := isStoppingTime_locStop hB hBc hΦc hΛm hΛc hG (L := L) (n := n) (U := U)
  have h1 := Ito.measurable_stopped_of_agree (X := Λ) hσ hΛm (G := univ)
    (@MeasurableSet.univ _ (𝓖 0)) (0 : E) (fun _ _ _ _ => rfl) (fun ω _ => (hΛc ω).continuousOn)
    (n : ℝ≥0)
  have h2 := Ito.measurable_stopped_of_agree (X := B) hσ hB.2.1 (G := univ)
    (@MeasurableSet.univ _ (𝓖 0)) (0 : ℝ) (fun _ _ _ _ => rfl) (fun ω _ => (hBc ω).continuousOn)
    (n : ℝ≥0)
  simp only [mem_univ, ↓reduceIte] at h1 h2
  have heq : (fun ω => pathX Λ B (locStop G Λ B U Φ L n ω) ω) =
      fun ω => (Λ (min (n : ℝ≥0) (locStop G Λ B U Φ L n ω)) ω,
        B (min (n : ℝ≥0) (locStop G Λ B U Φ L n ω)) ω) := by
    funext ω; rw [min_eq_right (locStop_le ω)]; rfl
  rw [heq]
  exact (h1.prodMk h2).mono (𝓖.le _) le_rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
include hB hBc hU hΦc hΛm hΛc hG in
/-- A function continuous on `U` along the stopped path is measurable. -/
theorem measurable_comp_pathX_locStop {F : E × ℝ → ℝ} (hF : ContinuousOn F U)
    (hin : ∀ ω, pathX Λ B (locStop G Λ B U Φ L n ω) ω ∈ U) :
    Measurable fun ω => F (pathX Λ B (locStop G Λ B U Φ L n ω) ω) := by
  have hp := (hF.measurable_piecewise (continuousOn_const (c := (0 : ℝ)))
    hU.measurableSet).comp (measurable_pathX_locStop (L := L) (n := n) hB hBc hΦc hΛm hΛc hG)
  have heq : (fun ω => F (pathX Λ B (locStop G Λ B U Φ L n ω) ω)) =
      (U.piecewise F fun _ => (0 : ℝ)) ∘ fun ω => pathX Λ B (locStop G Λ B U Φ L n ω) ω := by
    funext ω; simp only [Function.comp_apply, Set.piecewise_eq_of_mem _ _ _ (hin ω)]
  rw [heq]; exact hp

variable [IsProbabilityMeasure P] (hΦ : ContDiffOn ℝ 3 Φ U) (hΦ0 : ∀ p ∈ U, 0 ≤ Φ p)
  (hgen : ∀ ω ∈ G, ∀ t, Ito.itoGen Φ (pathX Λ B t ω) (Ψ (pathX Λ B t ω)) ≤ 0) (hGc : P Gᶜ = 0)

include hB hBc hU hΨ hΛm hΛc hG hΛ0 hB0 hpath hX0 hΦ hΦ0 hgen hGc in
/-- **Optional stopping for `Φ`**: `E Φ(X_σ) ≤ Φ(X_0)`. -/
theorem integral_stopped_le :
    ∫ ω, Φ (pathX Λ B (locStop G Λ B U Φ L n ω) ω) ∂P ≤ Φ (p₀, 0) := by
  have hΦc : ContinuousOn Φ U := hΦ.continuousOn
  have hM := martingale_loc hB hBc hU hΦc hΨ hΛm hΛc hG hΛ0 hB0 hpath hX0 hΦ
  have hsi := hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ (n : ℝ≥0)) MeasurableSet.univ
  simp only [setIntegral_univ] at hsi
  set σ := locStop G Λ B U Φ L n with hσdef
  have h0 : ∀ ω, Φ (pathX Λ B (min 0 (σ ω)) ω) -
      ∫ s in (0 : ℝ)..((min 0 (σ ω) : ℝ≥0) : ℝ), Ito.itoGen Φ (pathX Λ B s.toNNReal ω)
        (locDens G Λ B Ψ s ω) = Φ (p₀, 0) := fun ω => by
    simp [pathX, hΛ0, hB0]
  simp only [h0] at hsi
  rw [integral_const] at hsi
  simp only [probReal_univ, one_smul] at hsi
  have hmin : ∀ ω, min (n : ℝ≥0) (σ ω) = σ ω := fun ω => min_eq_right (locStop_le ω)
  simp only [hmin] at hsi
  have hin : ∀ ω, pathX Λ B (σ ω) ω ∈ U := fun ω =>
    keepSet_subset (pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0 le_rfl)
  have hmeas := measurable_comp_pathX_locStop hB hBc hU hΦc hΛm hΛc hG hΦc hin
  have hbd : ∀ ω, ‖Φ (pathX Λ B (σ ω) ω)‖ ≤ L := fun ω => by
    have hk := pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0 (le_refl (σ ω))
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 _ (hin ω))]
    exact hk.2.2
  have hint1 : Integrable (fun ω => Φ (pathX Λ B (σ ω) ω)) P :=
    Integrable.of_bound hmeas.aestronglyMeasurable L (Eventually.of_forall hbd)
  have hintM := hM.integrable (n : ℝ≥0)
  simp only [hmin] at hintM
  have hint2 := hint1.sub hintM
  -- the drift integral is nonpositive on `G`
  have hI : ∀ᵐ ω ∂P, ∫ s in (0 : ℝ)..((σ ω : ℝ≥0) : ℝ),
      Ito.itoGen Φ (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω) ≤ 0 := by
    have hG' : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
    filter_upwards [hG'] with ω hω
    have hpc : ContinuousOn (fun s : ℝ => pathX Λ B s.toNNReal ω) (Icc 0 (σ ω)) :=
      ((continuous_pathX hΛc hBc ω).comp continuous_real_toNNReal).continuousOn
    have hmapsU : MapsTo (fun s : ℝ => pathX Λ B s.toNNReal ω) (Icc 0 (σ ω)) U := fun s hs =>
      keepSet_subset (pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0
        (Real.toNNReal_le_iff_le_coe.2 hs.2))
    have hgc := (continuousOn_itoGen hU hΦ hΨ).comp hpc hmapsU
    have heq : ∀ s ∈ Icc (0 : ℝ) (σ ω), Ito.itoGen Φ (pathX Λ B s.toNNReal ω)
        (locDens G Λ B Ψ s ω) = Ito.itoGen Φ (pathX Λ B s.toNNReal ω)
          (Ψ (pathX Λ B s.toNNReal ω)) := fun s _ => by simp only [locDens, hω, ↓reduceIte]
    have hle := intervalIntegral.integral_mono_on (σ ω).coe_nonneg
      ((hgc.congr heq).intervalIntegrable_of_Icc (σ ω).coe_nonneg)
      (intervalIntegrable_const (μ := volume) (c := (0 : ℝ))) fun s hs => by
        rw [heq s hs]; exact hgen ω hω s.toNNReal
    simpa using hle
  have hIeq : (fun ω => ∫ s in (0 : ℝ)..((σ ω : ℝ≥0) : ℝ),
      Ito.itoGen Φ (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω)) = fun ω =>
        Φ (pathX Λ B (σ ω) ω) - (Φ (pathX Λ B (σ ω) ω) - ∫ s in (0 : ℝ)..((σ ω : ℝ≥0) : ℝ),
          Ito.itoGen Φ (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω)) := by
    funext ω; ring
  have hInt := integral_nonpos_of_ae hI
  rw [hIeq, integral_sub hint1 hintM, ← hsi] at hInt
  linarith

include hB hBc hU hΨ hΛm hΛc hG hΛ0 hB0 hpath hX0 hΦ hΦ0 hgen in
/-- **The quadratic-variation bound.** With `H = Φ(Φ − 2L)` and `Q = ∫₀^σ itoGen H`:
on `G`, `∫₀^σ (∂_x Φ)² ≤ Q`; `Q` is integrable and `E Q ≤ 2LΦ₀`. -/
theorem stopped_qv_bound :
    (∀ ω ∈ G, ∫ s in (0 : ℝ)..((locStop G Λ B U Φ L n ω : ℝ≥0) : ℝ),
        Ito.partialSnd Φ (pathX Λ B s.toNNReal ω) ^ 2 ≤
      ∫ s in (0 : ℝ)..((locStop G Λ B U Φ L n ω : ℝ≥0) : ℝ),
        Ito.itoGen (fun q => Φ q * (Φ q - 2 * L)) (pathX Λ B s.toNNReal ω)
          (locDens G Λ B Ψ s ω)) ∧
    Integrable (fun ω => ∫ s in (0 : ℝ)..((locStop G Λ B U Φ L n ω : ℝ≥0) : ℝ),
        Ito.itoGen (fun q => Φ q * (Φ q - 2 * L)) (pathX Λ B s.toNNReal ω)
          (locDens G Λ B Ψ s ω)) P ∧
    ∫ ω, (∫ s in (0 : ℝ)..((locStop G Λ B U Φ L n ω : ℝ≥0) : ℝ),
        Ito.itoGen (fun q => Φ q * (Φ q - 2 * L)) (pathX Λ B s.toNNReal ω)
          (locDens G Λ B Ψ s ω)) ∂P ≤ 2 * L * Φ (p₀, 0) := by
  have hΦc : ContinuousOn Φ U := hΦ.continuousOn
  set H : E × ℝ → ℝ := fun q => Φ q * (Φ q - 2 * L) with hHdef
  have hH : ContDiffOn ℝ 3 H U := hΦ.mul (hΦ.sub contDiffOn_const)
  have hM := martingale_loc hB hBc hU hΦc hΨ hΛm hΛc hG hΛ0 hB0 hpath hX0 hH
  have hsi := hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ (n : ℝ≥0)) MeasurableSet.univ
  simp only [setIntegral_univ] at hsi
  set σ := locStop G Λ B U Φ L n with hσdef
  have h0 : ∀ ω, H (pathX Λ B (min 0 (σ ω)) ω) -
      ∫ s in (0 : ℝ)..((min 0 (σ ω) : ℝ≥0) : ℝ), Ito.itoGen H (pathX Λ B s.toNNReal ω)
        (locDens G Λ B Ψ s ω) = H (p₀, 0) := fun ω => by
    simp [pathX, hΛ0, hB0]
  simp only [h0] at hsi
  rw [integral_const] at hsi
  simp only [probReal_univ, one_smul] at hsi
  have hmin : ∀ ω, min (n : ℝ≥0) (σ ω) = σ ω := fun ω => min_eq_right (locStop_le ω)
  simp only [hmin] at hsi
  have hin : ∀ ω, pathX Λ B (σ ω) ω ∈ U := fun ω =>
    keepSet_subset (pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0 le_rfl)
  have hkeep : ∀ ω, Φ (pathX Λ B (σ ω) ω) ∈ Icc 0 L := fun ω =>
    ⟨hΦ0 _ (hin ω), (pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0 (le_refl (σ ω))).2.2⟩
  have hk0 : ((p₀, 0) : E × ℝ) ∈ keepSet U Φ L n := closure_compl_exitSet_subset hΦc (subset_closure hX0)
  have hΦ00 : 0 ≤ Φ (p₀, 0) := hΦ0 _ (keepSet_subset hk0)
  have hL0 : 0 ≤ L := hΦ00.trans hk0.2.2
  have hmeas := measurable_comp_pathX_locStop hB hBc hU hΦc hΛm hΛc hG hH.continuousOn hin
  have hHbd : ∀ ω, ‖H (pathX Λ B (σ ω) ω)‖ ≤ 2 * L * L := fun ω => by
    obtain ⟨h1, h2⟩ := hkeep ω
    simp only [hHdef, Real.norm_eq_abs]
    rw [abs_le]; constructor <;> nlinarith
  have hint1 : Integrable (fun ω => H (pathX Λ B (σ ω) ω)) P :=
    Integrable.of_bound hmeas.aestronglyMeasurable _ (Eventually.of_forall hHbd)
  have hintM := hM.integrable (n : ℝ≥0)
  simp only [hmin] at hintM
  have hQeq : (fun ω => ∫ s in (0 : ℝ)..((σ ω : ℝ≥0) : ℝ),
      Ito.itoGen H (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω)) = fun ω =>
        H (pathX Λ B (σ ω) ω) - (H (pathX Λ B (σ ω) ω) - ∫ s in (0 : ℝ)..((σ ω : ℝ≥0) : ℝ),
          Ito.itoGen H (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω)) := by
    funext ω; ring
  have hQint : Integrable (fun ω => ∫ s in (0 : ℝ)..((σ ω : ℝ≥0) : ℝ),
      Ito.itoGen H (pathX Λ B s.toNNReal ω) (locDens G Λ B Ψ s ω)) P := by
    rw [hQeq]; exact hint1.sub hintM
  refine ⟨fun ω hω => ?_, hQint, ?_⟩
  · have hpc : ContinuousOn (fun s : ℝ => pathX Λ B s.toNNReal ω) (Icc 0 (σ ω)) :=
      ((continuous_pathX hΛc hBc ω).comp continuous_real_toNNReal).continuousOn
    have hmapsK : MapsTo (fun s : ℝ => pathX Λ B s.toNNReal ω) (Icc 0 (σ ω)) (keepSet U Φ L n) :=
      fun s hs => pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    have hmapsU : MapsTo (fun s : ℝ => pathX Λ B s.toNNReal ω) (Icc 0 (σ ω)) U := fun s hs =>
      keepSet_subset (hmapsK hs)
    have hgc := (continuousOn_itoGen hU hH hΨ).comp hpc hmapsU
    have hsc := ((continuousOn_partialSnd hU hΦ).comp hpc hmapsU).pow 2
    have heq : ∀ s ∈ Icc (0 : ℝ) (σ ω), Ito.itoGen H (pathX Λ B s.toNNReal ω)
        (locDens G Λ B Ψ s ω) = Ito.itoGen H (pathX Λ B s.toNNReal ω)
          (Ψ (pathX Λ B s.toNNReal ω)) := fun s _ => by simp only [locDens, hω, ↓reduceIte]
    refine intervalIntegral.integral_mono_on (σ ω).coe_nonneg
      (hsc.intervalIntegrable_of_Icc (σ ω).coe_nonneg)
      ((hgc.congr heq).intervalIntegrable_of_Icc (σ ω).coe_nonneg) fun s hs => ?_
    rw [heq s hs]
    have hpU := hmapsU hs
    have hcd : ContDiffAt ℝ 2 Φ (pathX Λ B s.toNNReal ω) :=
      (hΦ.contDiffAt (hU.mem_nhds hpU)).of_le (by norm_num)
    simp only [hHdef]
    rw [itoGen_mul_sub hcd L]
    have hg := hgen ω hω s.toNNReal
    have hle : Φ (pathX Λ B s.toNNReal ω) ≤ L := (hmapsK hs).2.2
    have : 0 ≤ 2 * (Φ (pathX Λ B s.toNNReal ω) - L) * Ito.itoGen Φ (pathX Λ B s.toNNReal ω)
        (Ψ (pathX Λ B s.toNNReal ω)) := by nlinarith
    linarith
  · rw [hQeq, integral_sub hint1 hintM, ← hsi]
    have hHle : ∫ ω, H (pathX Λ B (σ ω) ω) ∂P ≤ 0 := by
      refine integral_nonpos fun ω => ?_
      obtain ⟨h1, h2⟩ := hkeep ω
      simp only [Pi.zero_apply, hHdef]; nlinarith
    simp only [hHdef]
    nlinarith [sq_nonneg (Φ (p₀, 0))]

end Mart


/-! ### Pathwise exhaustion -/

section Exhaust

variable {E : Type*} [NormedAddCommGroup E] {U : Set (E × ℝ)} {Φ : E × ℝ → ℝ} {L : ℝ}

/-- A compact path segment in `U` is eventually avoided by the first two clauses of the exit set. -/
theorem exists_level_of_continuousOn (hUc : Uᶜ.Nonempty) (hU : IsOpen U) {x : ℝ≥0 → E × ℝ}
    {T : ℝ≥0} (hxc : ContinuousOn x (Icc 0 T)) (hxU : ∀ t ∈ Icc 0 T, x t ∈ U) :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, (T : ℝ) ≤ n ∧
      ∀ t ∈ Icc 0 T, 1 / ((n : ℝ) + 1) < infDist (x t) Uᶜ ∧ ‖x t‖ < n := by
  have hK : IsCompact (x '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hxc
  have hne : (x '' Icc 0 T).Nonempty := (nonempty_Icc.2 zero_le).image x
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne (continuous_infDist_pt (Uᶜ)).continuousOn
  have hδ : 0 < infDist p Uᶜ := by
    obtain ⟨t, ht, rfl⟩ := hp
    exact (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 (fun h => h (hxU t ht))
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (max (1 / infDist p Uᶜ) (max R T))
  refine ⟨n₁, fun n hn => ⟨?_, fun t ht => ⟨?_, ?_⟩⟩⟩
  · have : (n₁ : ℝ) ≤ n := by exact_mod_cast hn
    linarith [le_max_right R (T : ℝ), le_max_right (1 / infDist p Uᶜ) (max R T)]
  · have h1 : infDist p Uᶜ ≤ infDist (x t) Uᶜ := hmin ⟨t, ht, rfl⟩
    have h2 : (n₁ : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : 1 / infDist p Uᶜ < (n : ℝ) + 1 := by
      linarith [le_max_left (1 / infDist p Uᶜ) (max R T)]
    have h4 : 1 / ((n : ℝ) + 1) < infDist p Uᶜ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at h3
      linarith
    linarith
  · have h1 := hR (x t) ⟨t, ht, rfl⟩
    have h2 : (n₁ : ℝ) ≤ n := by exact_mod_cast hn
    linarith [le_max_left R (T : ℝ), le_max_right (1 / infDist p Uᶜ) (max R T)]

variable {Ω : Type*} {X : ℝ≥0 → Ω → E × ℝ} {ω : Ω} {n : ℕ}

/-- Before the exit set's first two clauses can trigger, the first hit is through `Φ ≥ L`. -/
theorem le_Φ_hittingBtwn (hc : Continuous (X · ω)) (hΦc : ContinuousOn Φ U) {t₁ : ℝ≥0}
    (hU1 : X t₁ ω ∈ U) (hL : L ≤ Φ (X t₁ ω)) (htn : (t₁ : ℝ) ≤ n)
    (hgood : ∀ t ∈ Icc 0 t₁, 1 / ((n : ℝ) + 1) < infDist (X t ω) Uᶜ ∧ ‖X t ω‖ < n) :
    L ≤ Φ (X (hittingBtwn X (exitSet U Φ L n) 0 n ω) ω) := by
  have ht₁ : t₁ ≤ (n : ℝ≥0) := by exact_mod_cast htn
  have hin : X t₁ ω ∈ exitSet U Φ L n := Or.inr (Or.inr ⟨hU1, hL⟩)
  have hle : hittingBtwn X (exitSet U Φ L n) 0 n ω ≤ t₁ := hittingBtwn_le_of_mem zero_le ht₁ hin
  have hmem := mem_of_hittingBtwn hc (isClosed_exitSet hΦc) ⟨t₁, ⟨zero_le, ht₁⟩, hin⟩
  obtain ⟨h1, h2⟩ := hgood _ ⟨zero_le, hle⟩
  rcases hmem with h | h | h
  · linarith
  · linarith
  · exact h.2

/-- If `Φ < L` along the whole path, the hitting time is at least `T` once the first two clauses
cannot trigger on `[0, T]`. -/
theorem le_hittingBtwn_of_lt (hc : Continuous (X · ω)) (hΦc : ContinuousOn Φ U)
    (hlt : ∀ t, X t ω ∈ U → Φ (X t ω) < L) {T : ℝ≥0} (hTn : (T : ℝ) ≤ n)
    (hgood : ∀ t ∈ Icc 0 T, 1 / ((n : ℝ) + 1) < infDist (X t ω) Uᶜ ∧ ‖X t ω‖ < n) :
    T ≤ hittingBtwn X (exitSet U Φ L n) 0 n ω := by
  by_contra hcon
  push Not at hcon
  have hTn' : T ≤ (n : ℝ≥0) := by exact_mod_cast hTn
  have hex : ∃ j ∈ Icc (0 : ℝ≥0) n, X j ω ∈ exitSet U Φ L n := by
    by_contra hno
    have : hittingBtwn X (exitSet U Φ L n) 0 n ω = n := by simp only [hittingBtwn, hno, ↓reduceIte]
    rw [this] at hcon
    exact absurd hTn' (not_le.2 hcon)
  have hmem := mem_of_hittingBtwn hc (isClosed_exitSet hΦc) hex
  obtain ⟨h1, h2⟩ := hgood _ ⟨zero_le, hcon.le⟩
  rcases hmem with h | h | h
  · linarith
  · linarith
  · exact absurd h.2 (not_le.2 (hlt _ h.1))

end Exhaust

/-! ### The main statement -/

section Final

open scoped Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {B : ℝ≥0 → Ω → ℝ}
  {U : Set (E × ℝ)} {Φ : E × ℝ → ℝ} {Ψ : E × ℝ → E} {Λ : ℝ≥0 → Ω → E} {G : Set Ω} {p₀ : E}

/-- **A positive Itô observable with nonpositive drift has finite quadratic variation.** -/
theorem ae_bddAbove_integral_sq_partialSnd (hB : IsFilteredBrownianReal 𝓖 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    (hΦ : ContDiffOn ℝ 3 Φ U) (hΦ0 : ∀ p ∈ U, 0 ≤ Φ p) (hΨ : ContinuousOn Ψ U)
    (hgen : ∀ ω ∈ G, ∀ t, Ito.itoGen Φ (pathX Λ B t ω) (Ψ (pathX Λ B t ω)) ≤ 0)
    (hΛm : ∀ t, Measurable[𝓖 t] (Λ t))
    (hΛc : ∀ ω, Continuous (Λ · ω)) (hG : MeasurableSet[𝓖 0] G) (hGc : P Gᶜ = 0)
    (hΛ0 : ∀ ω, Λ 0 ω = p₀) (hB0 : ∀ ω, B 0 ω = 0)
    (hpath : ∀ ω ∈ G, ∀ t : ℝ≥0, Λ t ω = p₀ + ∫ s in (0 : ℝ)..t, Ψ (pathX Λ B s.toNNReal ω))
    (hmem : ∀ ω ∈ G, ∀ t, pathX Λ B t ω ∈ U) :
    ∀ᵐ ω ∂P, ∃ S : ℝ, ∀ t : ℝ≥0,
      ∫ s in (0 : ℝ)..t, Ito.partialSnd Φ (pathX Λ B s.toNNReal ω) ^ 2 ≤ S := by
  have hΦc : ContinuousOn Φ U := hΦ.continuousOn
  set Φ₀ := Φ (p₀, 0) with hΦ₀def
  -- `G` is nonempty, so `(p₀, 0) ∈ U`
  have hGne : G.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, compl_empty, measure_univ] at hGc
    exact one_ne_zero hGc
  obtain ⟨ω₀, hω₀⟩ := hGne
  have hp0U : ((p₀, 0) : E × ℝ) ∈ U := by
    have := hmem ω₀ hω₀ 0; simpa [pathX, hΛ0, hB0] using this
  have hΦ₀0 : 0 ≤ Φ₀ := hΦ0 _ hp0U
  obtain ⟨n₀, hn₀⟩ := exists_level_of_continuousOn (x := fun _ => ((p₀, 0) : E × ℝ)) (T := 0)
    hUc hU continuousOn_const fun _ _ => hp0U
  have hX0 : ∀ L, Φ₀ < L → ∀ n ≥ n₀, ((p₀, 0) : E × ℝ) ∉ exitSet U Φ L n := by
    intro L hL n hn h
    obtain ⟨-, h1⟩ := hn₀ n hn
    obtain ⟨h2, h3⟩ := h1 0 ⟨le_rfl, le_rfl⟩
    rcases h with h | h | h
    · linarith
    · linarith
    · exact absurd h.2 (not_le.2 hL)
  -- the paths
  have hXc : ∀ ω, Continuous fun t => pathX Λ B t ω := continuous_pathX hΛc hBc
  -- the bad set
  rw [ae_iff]
  set Bad := {ω | ¬ ∃ S : ℝ, ∀ t : ℝ≥0,
    ∫ s in (0 : ℝ)..t, Ito.partialSnd Φ (pathX Λ B s.toNNReal ω) ^ 2 ≤ S} with hBad
  -- integrability of the square of `∂_x Φ` along a path in `U`
  have hsqint : ∀ ω ∈ G, ∀ T : ℝ≥0, IntervalIntegrable
      (fun s : ℝ => Ito.partialSnd Φ (pathX Λ B s.toNNReal ω) ^ 2) volume 0 T := by
    intro ω hω T
    refine ContinuousOn.intervalIntegrable_of_Icc T.coe_nonneg ?_
    refine ((continuousOn_partialSnd hU hΦ).comp ((hXc ω).comp
      continuous_real_toNNReal).continuousOn fun s _ => hmem ω hω _).pow 2
  have key : ∀ L : ℝ, Φ₀ < L → ∀ M : ℝ, 0 < M →
      P Bad ≤ ENNReal.ofReal (Φ₀ / L) + ENNReal.ofReal (2 * L * Φ₀ / M) := by
    intro L hL M hM
    have hL0 : 0 < L := lt_of_le_of_lt hΦ₀0 hL
    set σ : ℕ → Ω → ℝ≥0 := fun n => locStop G Λ B U Φ L n with hσdef
    set A : ℕ → Set Ω := fun n => {ω | L ≤ Φ (pathX Λ B (σ n ω) ω)} with hAdef
    set Q : ℕ → Ω → ℝ := fun n ω => ∫ s in (0 : ℝ)..((σ n ω : ℝ≥0) : ℝ),
      Ito.itoGen (fun q => Φ q * (Φ q - 2 * L)) (pathX Λ B s.toNNReal ω)
        (locDens G Λ B Ψ s ω) with hQdef
    set C : ℕ → Set Ω := fun n => {ω | M ≤ Q n ω} with hCdef
    -- Markov for `A`
    have hA : ∀ n ≥ n₀, P (A n) ≤ ENNReal.ofReal (Φ₀ / L) := by
      intro n hn
      have hX0n := hX0 L hL n hn
      have hin : ∀ ω, pathX Λ B (σ n ω) ω ∈ U := fun ω =>
        keepSet_subset (pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0n le_rfl)
      have hmeas := measurable_comp_pathX_locStop (L := L) (n := n) hB hBc hU hΦc hΛm hΛc hG
        hΦc hin
      have hbd : ∀ ω, ‖Φ (pathX Λ B (σ n ω) ω)‖ ≤ L := fun ω => by
        have hk := pathX_mem_keepSet hBc hΦc hΛc hΛ0 hB0 hX0n (le_refl (σ n ω))
        rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 _ (hin ω))]
        exact hk.2.2
      have hint : Integrable (fun ω => Φ (pathX Λ B (σ n ω) ω)) P :=
        Integrable.of_bound hmeas.aestronglyMeasurable L (Eventually.of_forall hbd)
      have hmk := mul_meas_ge_le_integral_of_nonneg
        (Eventually.of_forall fun ω => hΦ0 _ (hin ω)) hint L
      have hle := integral_stopped_le hB hBc hU hΨ hΛm hΛc hG hΛ0 hB0 hpath hX0n hΦ hΦ0 hgen hGc
      have hreal : P.real (A n) ≤ Φ₀ / L := by
        rw [le_div_iff₀ hL0, mul_comm]; exact hmk.trans hle
      rw [← ofReal_measureReal (measure_ne_top P (A n))]
      exact ENNReal.ofReal_le_ofReal hreal
    -- Markov for `C`
    have hC : ∀ n ≥ n₀, P (C n) ≤ ENNReal.ofReal (2 * L * Φ₀ / M) := by
      intro n hn
      have hX0n := hX0 L hL n hn
      obtain ⟨hpw, hQint, hQle⟩ := stopped_qv_bound hB hBc hU hΨ hΛm hΛc hG hΛ0 hB0 hpath hX0n
        hΦ hΦ0 hgen
      have hnn : ∀ᵐ ω ∂P, 0 ≤ Q n ω := by
        filter_upwards [(ae_iff.2 hGc : ∀ᵐ ω ∂P, ω ∈ G)] with ω hω
        refine le_trans ?_ (hpw ω hω)
        exact intervalIntegral.integral_nonneg (σ n ω).coe_nonneg fun s _ => sq_nonneg _
      have hmk := mul_meas_ge_le_integral_of_nonneg hnn hQint M
      have hreal : P.real (C n) ≤ 2 * L * Φ₀ / M := by
        rw [le_div_iff₀ hM, mul_comm]; exact hmk.trans hQle
      rw [← ofReal_measureReal (measure_ne_top P (C n))]
      exact ENNReal.ofReal_le_ofReal hreal
    -- the tail events
    set D : ℕ → Set Ω := fun N => ⋂ k, A (k + N + n₀) with hDdef
    set D' : ℕ → Set Ω := fun N => ⋂ k, C (k + N + n₀) with hD'def
    have hDm : Monotone D := by
      intro N N' hNN' ω hω
      simp only [hDdef, mem_iInter] at hω ⊢
      intro k
      have := hω (k + (N' - N))
      rwa [show k + (N' - N) + N + n₀ = k + N' + n₀ by omega] at this
    have hD'm : Monotone D' := by
      intro N N' hNN' ω hω
      simp only [hD'def, mem_iInter] at hω ⊢
      intro k
      have := hω (k + (N' - N))
      rwa [show k + (N' - N) + N + n₀ = k + N' + n₀ by omega] at this
    have hDle : P (⋃ N, D N) ≤ ENNReal.ofReal (Φ₀ / L) := by
      rw [hDm.measure_iUnion]
      refine iSup_le fun N => (measure_mono (iInter_subset _ 0)).trans ?_
      exact hA _ (by omega)
    have hD'le : P (⋃ N, D' N) ≤ ENNReal.ofReal (2 * L * Φ₀ / M) := by
      rw [hD'm.measure_iUnion]
      refine iSup_le fun N => (measure_mono (iInter_subset _ 0)).trans ?_
      exact hC _ (by omega)
    -- the covering
    have hcover : Bad ⊆ Gᶜ ∪ (⋃ N, D N) ∪ (⋃ N, D' N) := by
      intro ω hω
      by_cases hωG : ω ∈ G
      swap
      · exact Or.inl (Or.inl hωG)
      have hσG : ∀ n, σ n ω = hittingBtwn (pathX Λ B) (exitSet U Φ L n) 0 n ω := fun n => by
        simp only [hσdef, locStop, hωG, ↓reduceIte]
      by_cases hhit : ∃ t₁, L ≤ Φ (pathX Λ B t₁ ω)
      · obtain ⟨t₁, ht₁⟩ := hhit
        obtain ⟨n₁, hn₁⟩ := exists_level_of_continuousOn (x := fun t => pathX Λ B t ω) (T := t₁)
          hUc hU (hXc ω).continuousOn fun t _ => hmem ω hωG t
        refine Or.inl (Or.inr (mem_iUnion.2 ⟨n₁, mem_iInter.2 fun k => ?_⟩))
        obtain ⟨hT, hgood⟩ := hn₁ (k + n₁ + n₀) (by omega)
        show L ≤ Φ (pathX Λ B (σ (k + n₁ + n₀) ω) ω)
        rw [hσG]
        exact le_Φ_hittingBtwn (hXc ω) hΦc (hmem ω hωG t₁) ht₁ hT hgood
      · push Not at hhit
        simp only [hBad, mem_ofPred_eq, not_exists, not_forall, not_le] at hω
        obtain ⟨T, hT⟩ := hω M
        obtain ⟨n₁, hn₁⟩ := exists_level_of_continuousOn (x := fun t => pathX Λ B t ω) (T := T)
          hUc hU (hXc ω).continuousOn fun t _ => hmem ω hωG t
        refine Or.inr (mem_iUnion.2 ⟨n₁, mem_iInter.2 fun k => ?_⟩)
        set n := k + n₁ + n₀ with hndef
        obtain ⟨hTn, hgood⟩ := hn₁ n (by omega)
        have hTσ : T ≤ σ n ω := by
          rw [hσG]; exact le_hittingBtwn_of_lt (hXc ω) hΦc (fun t _ => hhit t) hTn hgood
        have hX0n := hX0 L hL n (by omega)
        obtain ⟨hpw, -, -⟩ := stopped_qv_bound hB hBc hU hΨ hΛm hΛc hG hΛ0 hB0 hpath hX0n
          hΦ hΦ0 hgen
        show M ≤ Q n ω
        refine le_trans ?_ (hpw ω hωG)
        refine hT.le.trans ?_
        refine intervalIntegral.integral_mono_interval le_rfl T.coe_nonneg
          (by exact_mod_cast hTσ) (Eventually.of_forall fun s => sq_nonneg _) (hsqint ω hωG _)
    calc P Bad ≤ P (Gᶜ ∪ (⋃ N, D N) ∪ (⋃ N, D' N)) := measure_mono hcover
      _ ≤ P Gᶜ + P (⋃ N, D N) + P (⋃ N, D' N) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ 0 + ENNReal.ofReal (Φ₀ / L) + ENNReal.ofReal (2 * L * Φ₀ / M) := by
        rw [hGc]; gcongr
      _ = ENNReal.ofReal (Φ₀ / L) + ENNReal.ofReal (2 * L * Φ₀ / M) := by rw [zero_add]
  -- conclude: let `M → ∞`, then `L → ∞`
  have hL : ∀ L : ℝ, Φ₀ < L → P Bad ≤ ENNReal.ofReal (Φ₀ / L) := by
    intro L hL
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hL0 : 0 < L := lt_of_le_of_lt hΦ₀0 hL
    set M : ℝ := 2 * L * Φ₀ / ε + 1 with hMdef
    have hM : 0 < M := by positivity
    refine (key L hL M hM).trans (add_le_add le_rfl ?_)
    rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal,
      div_le_iff₀ hM]
    have hε' : (0 : ℝ) < ε := hε
    rw [hMdef, mul_add, mul_div_cancel₀ _ hε'.ne', mul_one]
    linarith
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  have hε' : (0 : ℝ) < ε := hε
  set L : ℝ := Φ₀ / ε + Φ₀ + 1 with hLdef
  have hLΦ : Φ₀ < L := by rw [hLdef]; have := div_nonneg hΦ₀0 hε'.le; linarith
  refine (hL L hLΦ).trans ?_
  rw [zero_add, ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
  have hL0 : 0 < L := lt_of_le_of_lt hΦ₀0 hLΦ
  rw [div_le_iff₀ hL0, hLdef, mul_add, mul_add, mul_div_cancel₀ _ hε'.ne', mul_one]
  nlinarith

end Final

end Zhan

end InteractingSLE
