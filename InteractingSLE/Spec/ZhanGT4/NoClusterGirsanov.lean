/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.NoClusterLift
import InteractingSLE.Spec.Dimension.FiniteGirsanov

/-!
# (G5) at stopping times of integrated evolutions, by bounded-drift Girsanov

Packet PROVE-ZHAN-GT4-B2. Source: Astra, *Follow-up proofs*, §B.1 L1101–L1109 (ruling R38): "The ordinary
stopping-time inverse-boundary and real-collar statements also transfer to each bounded-drift … law used below. …
stop on a finite … horizon with all carried gaps … between fixed positive bounds, and apply the equivalent bounded-drift
Girsanov law. … The countable localization events exhaust every finite … stopping time." Additional note (G1),
L1351–L1358: "Local covariance and bounded-drift Girsanov give the same assertions at finite stops of the
separated-force … laws used below."

For an integrated `SLE_κ(ρ)` evolution and a positive stopping time `T` of its filtration, the inverse boundary at `T`
is interior almost surely on the event that `T` comes before the lifetime with all force gaps positive on `[0, T]`,
given (G5) for ordinary `SLE_κ` (`StoppingInverseBoundaryStatement κ`, Part A's output). With the cut drift of
`Girsanov.girsanov_cutDrift` at level `δ = 1/(n+1)` up to the horizon `n + 1`, the process
`B̂ = B + ∫ κ^{-1/2}·drift` is
a Brownian motion of the same filtration under an equivalent probability; (G5) applies to it at the stopping time
`T ∧ (n + 1)`; on the event that `T ≤ n` and all gaps are `≥ δ` on `[0, T]`, the driver is `√κ B̂` on `[0, T]`.

## Main results

* `hasInteriorInverseBoundary_congr`: (G5) at `T` reads the driver on `[0, T]` only.
* `IsIntegratedSLEEvolution.ae_hasInteriorInverseBoundary`: the transfer.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open QuantumZipper QuantumZipper.RS InteractingSLE.Girsanov

/-- **(G5) reads the driver up to the current time.** -/
theorem hasInteriorInverseBoundary_congr {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W')
    (hW0 : W 0 = 0) (hW'0 : W' 0 = 0) {T : ℝ} (hT : 0 ≤ T) (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r)
    (hG : HasInteriorInverseBoundary W T) : HasInteriorInverseBoundary W' T := by
  intro u hu
  rw [← exteriorCoords_congr hW hW' hT h] at hu
  obtain ⟨p, hp, hlim⟩ := hG u hu
  refine ⟨p, hp, hlim.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)⟩
  exact fwdMapInv_congr hW hW' hW0 hW'0 hT h hz

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **One localization level.** For `n : ℕ`, almost surely: if `T ≤ n`, `T` comes before the lifetime and all gaps
are `≥ 1/(n+1)` on `[0, T]`, then the inverse boundary at `T` is interior for every continuous driver agreeing with
`W` on `[0, T]`. -/
theorem IsIntegratedSLEEvolution.ae_hasInteriorInverseBoundary_level [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{u} κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hT0 : ∀ ω, 0 < T ω) (n : ℕ) :
    ∀ᵐ ω ∂P, T ω ≤ n → (T ω : ℝ≥0∞) < ζ ω →
      (∀ s : ℝ≥0, s ≤ T ω → Dimension.GapsGE (1 / ((n : ℝ) + 1)) (W s ω) (fun i => VL i s ω)
        (fun i => VR i s ω)) →
      ∀ W' : ℝ → ℝ, Continuous W' → (∀ r ∈ Icc (0 : ℝ) (T ω), W' r = W r.toNNReal ω) →
        HasInteriorInverseBoundary W' (T ω) := by
  obtain ⟨hBF, hW, hVL, hVR, hpath⟩ := hE
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  set U : Fin (nL + nR) → ℝ≥0 → Ω → ℝ := allMarks VL VR with hUdef
  set σ : Fin (nL + nR) → ℝ := Fin.addCases (motive := fun _ => ℝ) ρL ρR with hσ
  set F : ℝ → (Fin (nL + nR) → ℝ) → ℝ := fun w u => (Real.sqrt κ)⁻¹ * addedDriftCut σ δ w u
    with hFdef
  have hFc : Continuous fun p : ℝ × (Fin (nL + nR) → ℝ) => F p.1 p.2 :=
    continuous_const.mul (continuous_addedDriftCut σ hδ)
  have hFb : ∀ w u, |F w u| ≤ (Real.sqrt κ)⁻¹ * ((∑ j, |σ j|) * δ⁻¹) := fun w u => by
    rw [hFdef, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg κ))]
    exact mul_le_mul_of_nonneg_left (abs_addedDriftCut_le σ hδ w u)
      (inv_nonneg.2 (Real.sqrt_nonneg κ))
  set N : ℝ≥0 := (n : ℝ≥0) with hN
  set τ : Ω → ℝ≥0∞ := fun ω => min (ζ ω) (N : ℝ≥0∞) with hτdef
  have hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s} := by
    intro s
    have h1 : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ (univ : Set ℝ)} :=
      hW s univ MeasurableSet.univ
    have h2 : {ω | τ ω ≤ s} = {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ (univ : Set ℝ)}ᶜ ∪
        {_ω : Ω | (N : ℝ≥0∞) ≤ s} := by
      ext ω
      simp [hτdef, min_le_iff, not_lt]
    rw [h2]
    exact h1.compl.union (MeasurableSet.const _)
  have hτζ : ∀ ω, τ ω ≤ ζ ω := fun ω => min_le_left _ _
  have hτT : ∀ ω, τ ω ≤ (N : ℝ≥0∞) := fun ω => min_le_right _ _
  have hU : ∀ k, AdaptedBefore 𝓕 ζ (U k) := fun k => by
    cases k using Fin.addCases with
    | left i => simpa [hUdef, allMarks] using hVL i
    | right i => simpa [hUdef, allMarks] using hVR i
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => U k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hpath] with ω hp
    refine ⟨hp.2.2.2.1, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [hUdef, allMarks] using hp.2.2.2.2.1 i
    | right i => simpa [hUdef, allMarks] using hp.2.2.2.2.2.1 i
  obtain ⟨hequiv, hBM, hident⟩ := girsanov_cutDrift hBF hFc hFb hW hU hτ hτζ hτT hcont
  set θ := cutDrift τ ζ F W U with hθ
  set Q := girsanovMeasure P 𝓕 B θ (N + 1) with hQ
  set Bh := girsanovProcess B θ with hBh
  have : IsProbabilityMeasure Q := hequiv.isProb
  -- (G5) for `√κ B̂` at the stopping time `T ∧ (n + 1)`
  set Tn : Ω → ℝ≥0 := fun ω => min (T ω) (N + 1) with hTn
  have hTns : IsStoppingTime 𝓕 fun ω => ((Tn ω : ℝ≥0) : WithTop ℝ≥0) := by
    have h := hT.min_const (N + 1)
    have he : (fun ω => ((Tn ω : ℝ≥0) : WithTop ℝ≥0)) = fun ω => min (T ω : WithTop ℝ≥0) ((N + 1 : ℝ≥0)) :=
      funext fun ω => by rw [hTn]; push_cast; rfl
    rw [he]; exact h
  have hTn0 : ∀ ω, 0 < Tn ω := fun ω => lt_min (hT0 ω) (by positivity)
  have hQG5 := hG5 Q 𝓕 Bh hBM Tn hTns hTn0
  have hPG5 := hequiv.ac'.ae_le hQG5
  have hPcont := hequiv.ac'.ae_le hBM.1.cont
  have hP0 := hequiv.ac'.ae_le hBM.1.eval_zero_ae_eq_zero
  filter_upwards [hident, hpath, hPG5, hPcont, hP0, hcont, hBF.1.eval_zero_ae_eq_zero] with ω hid hp hG hBc hB0
    hc hB00 hTN hTζ hgap W' hW'c hW'eq
  obtain ⟨hw0, -, -, -, -, -, -, -, -, -, hgapL, hgapR, hweq, -⟩ := hp
  have hTnω : Tn ω = T ω := min_eq_left (hTN.trans (le_self_add))
  rw [hTnω] at hG
  -- the driver is `√κ B̂` on `[0, T]`
  have hagree : ∀ t : ℝ≥0, t ≤ T ω → W t ω = Real.sqrt κ * Bh t ω := by
    intro t htT
    have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 htT) hTζ
    have ht' : ((0 + t : ℝ≥0) : ℝ≥0∞) ≤ τ ω := by
      rw [zero_add]
      exact le_min htζ.le (ENNReal.coe_le_coe.2 (htT.trans hTN))
    have h0' : ((0 : ℝ≥0) : ℝ≥0∞) ≤ τ ω := by simp
    have hsplit : ∀ r : ℝ≥0, (∑ k, ∫ s in (0 : ℝ)..(r : ℝ), σ k / (W s.toNNReal ω - U k s.toNNReal ω))
        = (∑ i, ∫ s in (0 : ℝ)..(r : ℝ), ρL i / (W s.toNNReal ω - VL i s.toNNReal ω))
          + (∑ i, ∫ s in (0 : ℝ)..(r : ℝ), ρR i / (W s.toNNReal ω - VR i s.toNNReal ω)) := by
      intro r
      rw [Fin.sum_univ_add]
      simp only [hσ, hUdef, allMarks, Fin.addCases_left, Fin.addCases_right]
    have hint : ∀ k, IntervalIntegrable (fun s : ℝ => σ k / (W s.toNNReal ω - U k s.toNNReal ω))
        volume 0 ((0 + t : ℝ≥0) : ℝ) := fun k => by
      rw [zero_add]
      cases k using Fin.addCases with
      | left i =>
        simp only [hσ, hUdef, allMarks, Fin.addCases_left, div_eq_mul_inv]
        exact (hgapL t htζ i).const_mul (ρL i)
      | right i =>
        simp only [hσ, hUdef, allMarks, Fin.addCases_right, div_eq_mul_inv]
        exact (hgapR t htζ i).const_mul (ρR i)
    have hfint := intervalIntegrable_comp_of_le hFc hFb hW hU hτ (hτζ ω) hc.1 hc.2 ht'
    have key := Dimension.sub_eq_sqrt_mul_sub_of_cut (u := fun k s => U k s ω) (w := fun s => W s ω)
      (b := fun s => B s ω) (bh := fun s => Bh s ω) hκ hδ σ hint hfint ?_ ?_ (hid _ ht') (hid _ h0') ?_
    · have hw0' : W 0 ω = 0 := hw0
      simp only [zero_add] at key
      rw [hw0', hB0] at key
      simpa using key
    · have h1 := hweq (0 + t) (by rw [zero_add]; exact htζ)
      beta_reduce at h1
      rw [hsplit]; linarith
    · have h1 := hweq 0 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 bot_le) htζ)
      beta_reduce at h1
      rw [hsplit]; linarith
    · intro s _ hs k
      rw [zero_add] at hs
      obtain ⟨hL, hR⟩ := hgap s (hs.trans htT)
      cases k using Fin.addCases with
      | left i => simpa [hUdef, allMarks] using hL i
      | right i => simpa [hUdef, allMarks] using hR i
  have hdc : Continuous (drive κ Bh ω) := drive_continuous hBc
  refine hasInteriorInverseBoundary_congr hdc hW'c (by simp [drive, hB0]) ?_ (T ω).coe_nonneg
    (fun r hr => ?_) hG
  · have := hW'eq 0 ⟨le_rfl, (T ω).coe_nonneg⟩
    rw [this]; simpa using hw0
  · rw [hW'eq r hr, drive, hagree r.toNNReal (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)]

/-- A positive lower bound for finitely many positive quantities. -/
theorem exists_pos_forall_of_fintype {ι : Type*} [Fintype ι] {p : ι → ℝ → Prop}
    (hmono : ∀ i a b, a ≤ b → p i b → p i a) (h : ∀ i, ∃ δ > (0 : ℝ), p i δ) :
    ∃ δ > (0 : ℝ), ∀ i, p i δ := by
  choose δ hδ hp using h
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, (Finset.lt_inf'_iff _).2 fun i _ => hδ i,
      fun i => hmono i _ _ (Finset.inf'_le _ (Finset.mem_univ i)) (hp i)⟩

/-- A continuous positive function on `[0, T] ⊆ ℝ≥0` is bounded below by a positive constant. -/
theorem exists_pos_le_of_continuousOn {f : ℝ≥0 → ℝ} {T : ℝ≥0} (hf : ContinuousOn f (Icc 0 T))
    (hpos : ∀ s ∈ Icc 0 T, 0 < f s) : ∃ δ > (0 : ℝ), ∀ s ∈ Icc 0 T, δ ≤ f s := by
  obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_isMinOn
    (nonempty_Icc.2 bot_le) hf
  exact ⟨f s₀, hpos s₀ hs₀, fun s hs => hmin hs⟩

/-- **(G5) at a positive stopping time of an integrated evolution** (B.1 L1101–L1109; additional note (G1)), given (G5)
for ordinary `SLE_κ`: almost surely, if `T` comes before the lifetime and every force point is strictly separated from
the driver on `[0, T]`, then the inverse boundary at `T` is interior, for every continuous driver agreeing with `W` on
`[0, T]`. -/
theorem IsIntegratedSLEEvolution.ae_hasInteriorInverseBoundary [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{u} κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hT0 : ∀ ω, 0 < T ω) :
    ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
      (∀ s : ℝ≥0, s ≤ T ω → (∀ i, VL i s ω < W s ω) ∧ ∀ j, W s ω < VR j s ω) →
      ∀ W' : ℝ → ℝ, Continuous W' → (∀ r ∈ Icc (0 : ℝ) (T ω), W' r = W r.toNNReal ω) →
        HasInteriorInverseBoundary W' (T ω) := by
  have hall := ae_all_iff.2 fun n : ℕ =>
    IsIntegratedSLEEvolution.ae_hasInteriorInverseBoundary_level hκ hG5 hE hT hT0 n
  filter_upwards [hall, hE.2.2.2.2] with ω hlev hp hTζ hsep W' hW'c hW'eq
  have hsub : Icc (0 : ℝ≥0) (T ω) ⊆ {s | (s : ℝ≥0∞) < ζ ω} := fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) hTζ
  -- a uniform lower bound for the gaps on `[0, T]`
  obtain ⟨δL, hδL, hL⟩ := exists_pos_forall_of_fintype
    (p := fun (i : Fin nL) (d : ℝ) => ∀ s ∈ Icc (0 : ℝ≥0) (T ω), d ≤ W s ω - VL i s ω)
    (fun i a b hab h s hs => hab.trans (h s hs)) fun i =>
      exists_pos_le_of_continuousOn ((hp.2.2.2.1.sub (hp.2.2.2.2.1 i)).mono hsub)
        fun s hs => sub_pos.2 ((hsep s hs.2).1 i)
  obtain ⟨δR, hδR, hR⟩ := exists_pos_forall_of_fintype
    (p := fun (j : Fin nR) (d : ℝ) => ∀ s ∈ Icc (0 : ℝ≥0) (T ω), d ≤ VR j s ω - W s ω)
    (fun j a b hab h s hs => hab.trans (h s hs)) fun j =>
      exists_pos_le_of_continuousOn (((hp.2.2.2.2.2.1 j).sub hp.2.2.2.1).mono hsub)
        fun s hs => sub_pos.2 ((hsep s hs.2).2 j)
  obtain ⟨n, hn⟩ := exists_nat_ge (max (T ω : ℝ) (1 / min δL δR))
  have hTn : T ω ≤ n := by
    rw [← NNReal.coe_le_coe]; exact (le_max_left _ _).trans (by exact_mod_cast hn)
  have hmin : 0 < min δL δR := lt_min hδL hδR
  have hδn : 1 / ((n : ℝ) + 1) ≤ min δL δR := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 / min δL δR ≤ n := (le_max_right _ _).trans hn
    rw [div_le_iff₀ hmin] at h1
    nlinarith
  refine hlev n hTn hTζ (fun s hs => ⟨fun i => ?_, fun j => ?_⟩) W' hW'c hW'eq
  · have h := hL i s ⟨bot_le, hs⟩
    rw [abs_of_pos (by linarith)]
    linarith [min_le_left δL δR]
  · have h := hR j s ⟨bot_le, hs⟩
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith [min_le_right δL δR]

end InteractingSLE.ZhanGT4
