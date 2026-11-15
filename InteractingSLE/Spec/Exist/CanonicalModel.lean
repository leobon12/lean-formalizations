/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.CanonicalUnif
import InteractingSLE.Spec.Coupling.WholeField5Restart
import InteractingSLE.Spec.Exist.BrownianTransfer

/-!
# The model: the killed driving noise continued by an independent Brownian motion

Packet PROVE-FLOWEXIST3 (AUD-3c N1). On `Ω × Ω` with `P ⊗ P`, the noise of the frozen coupling stopped at the lifetime,
`N_u = B'(u ∧ ζ)`, continued by an independent Brownian motion `B''` after the lifetime,
`β_u = N_u + B''_u − B''_{u ∧ ζ}` (`WholeField.complNoise`), is the noise of an integrated evolution with the lifted
driving process (`model_isIntegratedSLEEvolution`). The clock and the stopped noise are identified exactly
(`exists_lifetimeGerm_clamp`: the construction of `WholeField.exists_lifetimeGerm`, with `ℓ_u = u ∧ ζ` exported; for an
inadmissible seed `ζ = 0` and `β = B''`).

* `clampT ζ u = (u ∧ ζ)` as a real time; `annClock_eq_clampT` (the clock of an announcing sequence);
* **`isIntegratedSLEEvolution_congr_ae`**: an integrated evolution with a filtration containing the null sets stays one
  after an almost sure modification of the driving process before the lifetime, of the lifetime and of the noise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

open LQGMetric Sec2.Assembly WholeField Coupling

variable {nL nR : ℕ}

/-! ### The clock `u ∧ ζ` -/

/-- The time `u ∧ ζ`. -/
def clampT (ζ : ℝ≥0∞) (u : ℝ≥0) : ℝ≥0 := (min (u : ℝ≥0∞) ζ).toNNReal

theorem clampT_of_lt {ζ : ℝ≥0∞} {u : ℝ≥0} (h : (u : ℝ≥0∞) < ζ) : clampT ζ u = u := by
  rw [clampT, min_eq_left h.le, ENNReal.toNNReal_coe]

theorem clampT_of_le {ζ : ℝ≥0∞} {u : ℝ≥0} (h : ζ ≤ u) : clampT ζ u = ζ.toNNReal := by
  rw [clampT, min_eq_right h]

theorem clampT_top (u : ℝ≥0) : clampT ⊤ u = u := clampT_of_lt ENNReal.coe_lt_top

theorem clampT_zero (u : ℝ≥0) : clampT 0 u = 0 := by
  rw [clampT_of_le zero_le]; rfl

theorem continuous_clampT (ζ : ℝ≥0∞) : Continuous (clampT ζ) := by
  by_cases hζ : ζ = ⊤
  · subst hζ
    have : clampT ⊤ = id := funext clampT_top
    rw [this]; exact continuous_id
  · have e : clampT ζ = fun u => min u ζ.toNNReal := by
      funext u
      rw [clampT, ← ENNReal.coe_toNNReal hζ, ← ENNReal.coe_min, ENNReal.toNNReal_coe,
        ENNReal.coe_toNNReal hζ]
    rw [e]
    exact continuous_id.min continuous_const

theorem measurable_clampT : Measurable fun p : ℝ≥0∞ × ℝ≥0 => clampT p.1 p.2 :=
  ENNReal.measurable_toNNReal.comp ((measurable_coe_nnreal_ennreal.comp measurable_snd).min
    measurable_fst)

theorem clampT_le (ζ : ℝ≥0∞) (u : ℝ≥0) : clampT ζ u ≤ u := by
  rcases lt_or_ge (u : ℝ≥0∞) ζ with h | h
  · rw [clampT_of_lt h]
  · rw [clampT_of_le h]
    have hfin : ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]; exact h

/-- The clock of an announcing sequence is `u ∧ ζ`. -/
theorem annClock_eq_clampT {Ω : Type*} {σ : ℕ → Ω → ℝ≥0} {ω : Ω} {ζ : ℝ≥0∞}
    (hlt : ∀ m, (σ m ω : ℝ≥0∞) < ζ) (hexh : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∃ m, t ≤ σ m ω) (u : ℝ≥0) :
    annClock σ u ω = clampT ζ u := by
  rcases lt_or_ge (u : ℝ≥0∞) ζ with h | h
  · obtain ⟨m, hm⟩ := hexh u h
    rw [annClock_eq_of_le hm, clampT_of_lt h]
  · have hfin : ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h
    rw [clampT_of_le h]
    have hσle : ∀ m, σ m ω ≤ ζ.toNNReal := fun m => by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]; exact (hlt m).le
    have hσu : ∀ m, σ m ω ≤ u := fun m => by
      rw [← ENNReal.coe_le_coe]; exact (hlt m).le.trans h
    have e : annClock σ u ω = ⨆ m, σ m ω := by
      rw [annClock]; congr 1; funext m; exact min_eq_right (hσu m)
    rw [e]
    refine le_antisymm (ciSup_le hσle) (le_of_forall_lt fun t ht => ?_)
    have htζ : (t : ℝ≥0∞) < ζ := by
      rw [← ENNReal.coe_toNNReal hfin]; exact ENNReal.coe_lt_coe.2 ht
    obtain ⟨m, hm⟩ := hexh t htζ
    obtain ⟨t', htt', ht'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htζ
    obtain ⟨m', hm'⟩ := hexh t' ht'ζ
    have htt'' : t < t' := by exact_mod_cast htt'
    exact lt_of_lt_of_le htt'' (hm'.trans (le_ciSup ⟨ζ.toNNReal, by rintro _ ⟨k, rfl⟩; exact hσle k⟩ m'))

/-! ### Almost sure modifications of an integrated evolution -/

/-- **An integrated evolution survives almost sure modifications** of the driving process before the lifetime, of
the lifetime and of the noise, when its filtration contains the null sets and the modified objects are measurable
and satisfy the pathwise relation. -/
theorem isIntegratedSLEEvolution_congr_ae {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {W W' : ℝ≥0 → Ω → ℝ} {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B B' : ℝ≥0 → Ω → ℝ} {ζ ζ' : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR Q 𝓖 W VL VR B ζ)
    (hnull : ∀ t (N : Set Ω), MeasurableSet N → Q N = 0 → MeasurableSet[𝓖 t] N)
    (hX' : IsMeasurableKilledDriving W' VL' VR' ζ') (hB'm : ∀ t, Measurable (B' t))
    (hagree : ∀ᵐ p ∂Q, ζ' p = ζ p ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ p → W' t p = W t p ∧
      (∀ i, VL' i t p = VL i t p) ∧ ∀ j, VR' j t p = VR j t p) ∧ ∀ t, B' t p = B t p)
    (hpath : ∀ᵐ p ∂Q, IsIntegratedSLEPath a xL xR ρL ρR (fun t => W' t p) (fun i t => VL' i t p)
      (fun j t => VR' j t p) (fun t => B' t p) (ζ' p)) :
    IsIntegratedSLEEvolution a xL xR ρL ρR Q 𝓖 W' VL' VR' B' ζ' := by
  have hBB : ∀ t, B t =ᵐ[Q] B' t := fun t => hagree.mono fun p hp => (hp.2.2 t).symm
  -- adaptedness before `ζ` from an almost sure equality of events
  have hadapt : ∀ (X : ℝ≥0 → Ω → ℝ) (X' : ℝ≥0 → Ω → ℝ), AdaptedBefore 𝓖 ζ X →
      (∀ (t : ℝ≥0) (A : Set ℝ), MeasurableSet A → MeasurableSet {p | (t : ℝ≥0∞) < ζ' p ∧ X' t p ∈ A}) →
      (∀ᵐ p ∂Q, ζ' p = ζ p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ p → X' t p = X t p) →
      AdaptedBefore 𝓖 ζ' X' := by
    intro X X' hX hm hXX t A hA
    refine WholeField.measurableSet_of_ae_eq (𝓖.le t) (hnull t) (hm t A hA) (hX t A hA) ?_
    filter_upwards [hXX] with p hp
    apply propext
    rw [hp.1]
    exact ⟨fun h => ⟨h.1, hp.2 t h.1 ▸ h.2⟩, fun h => ⟨h.1, (hp.2 t h.1).symm ▸ h.2⟩⟩
  refine ⟨⟨⟨hE.1.1.toIsPreBrownianReal.congr hBB, ?_⟩, fun t => ?_, fun s t hst => ?_⟩,
    hadapt W W' hE.2.1 (fun (t : ℝ≥0) A hA => hX' t _ (measurable_fst hA))
      (hagree.mono fun p hp => ⟨hp.1, fun t ht => (hp.2.1 t ht).1⟩),
    fun i => hadapt (VL i) (VL' i) (hE.2.2.1 i)
      (fun (t : ℝ≥0) A hA => hX' t _ ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd) hA))
      (hagree.mono fun p hp => ⟨hp.1, fun t ht => (hp.2.1 t ht).2.1 i⟩),
    fun j => hadapt (VR j) (VR' j) (hE.2.2.2.1 j)
      (fun (t : ℝ≥0) A hA => hX' t _ ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd) hA))
      (hagree.mono fun p hp => ⟨hp.1, fun t ht => (hp.2.1 t ht).2.2 j⟩), hpath⟩
  · filter_upwards [hE.1.1.cont, hagree] with p hp hq
    have e : (fun t => B' t p) = fun t => B t p := funext fun t => hq.2.2 t
    rw [e]; exact hp
  · exact Sec2.Restart.measurable_of_ae_eq_of_null (𝓖.le t) (hnull t) (hE.1.2.1 t) (hB'm t) (hBB t)
  · refine Sec2.Restart.indep_comap_congr ?_ (hE.1.2.2 s t hst)
    filter_upwards [hagree] with p hp
    simp only [hp.2.2]

/-! ### The lifetime germ with the clock identified -/

section Germ

universe u

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The noise stopped at the lifetime is an exponential martingale with the clock `u ∧ ζ`** in a filtration to which
the driving process is adapted before `ζ` and which contains the null sets (the construction of
`WholeField.exists_lifetimeGerm` with the clock exported; for an inadmissible seed, `ζ = 0` and the clock is `0`). -/
theorem exists_lifetimeGerm_clamp (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) {B' : ℝ≥0 → Ω → ℝ}
    (hB'm : ∀ t, Measurable (B' t)) (hB'c : ∀ ω, Continuous (B' · ω)) (hB'0 : ∀ ω, B' 0 ω = 0)
    (hB'ae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) :
    ∃ (𝒢 : Filtration ℝ≥0 mΩ) (ℓ : ℝ≥0 → Ω → ℝ≥0),
      Sec6.Prop65.IsTCExpMartingale P 𝒢 (fun u ω => B' (ℓ u ω) ω) ℓ ∧
      (∀ u (M : Set Ω), MeasurableSet M → P M = 0 → MeasurableSet[𝒢 u] M) ∧
      AdaptedBefore 𝒢 ζ W ∧ (∀ i, AdaptedBefore 𝒢 ζ (VL i)) ∧ (∀ j, AdaptedBefore 𝒢 ζ (VR j)) ∧
      ∀ᵐ ω ∂P, ∀ u, ℓ u ω = clampT (ζ ω) u := by
  have hE := hC.1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- an inadmissible seed: `ζ = 0`
    refine ⟨drivingFiltration P hX, fun _ _ => 0, ?_, fun u M hM h0 =>
      Ito.measurableSet_usualAugmentation_of_null hM h0 u,
      Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX),
      fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i),
      fun j => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX j), ?_⟩
    · have e : (fun (u : ℝ≥0) (ω : Ω) => B' ((fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ≥0)) u ω) ω) =
          fun _ _ => (0 : ℝ) := by
        funext u ω; exact hB'0 ω
      rw [e]
      refine ⟨fun _ => measurable_const, fun _ => measurable_const, fun _ _ => zero_le, fun s u ω _ => ?_,
        fun _ => continuous_const, fun _ => rfl, fun a s u _ Wf _ => ?_⟩
      · simp
      · simp
    · filter_upwards [ae_lifetime_eq_zero hE hseed] with ω hω u
      rw [hω, clampT_zero]
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨u₀, hu₀⟩ := WholeField.exists_bhe κ ρL ρR xL xR
  obtain ⟨σ₀, hσ₀, hσ₀n⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B)
    (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  have key := fun m => martingale_stoppedNoise_germ_exp hC hκ hu₀ hX (hσ₀.1 m) (hσ₀.2.2.1 m) (hσ₀n m)
  choose A 𝒢 hAm hAK h𝒢 h𝓓𝒢 Y hYm hYc hY0 hYB hY2 hYexp using key
  have hnull : ∀ m t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝒢 m t] N :=
    fun m t N hN h0 => h𝓓𝒢 m t _ (measurableSet_stopping_driving_of_null hX ((hσ₀.1 m).min_const t) hN h0)
  have hAK' : ∀ m u, ∀ᵐ ω ∂P, A m u ω =
      QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (σ₀ m ω : WithTop ℝ≥0) u).untopD 0 : ℝ≥0) := by
    intro m u
    filter_upwards [hAK m u] with ω hω
    rw [hω, ← WithTop.coe_min, WithTop.untopD_coe]
  have hσζ : ∀ m u, ∀ᵐ ω ∂P, ((min (σ₀ m ω : WithTop ℝ≥0) u : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω :=
    fun m u => (hσ₀.2.2.1 m).mono fun ω hω => lt_of_le_of_lt (min_le_left _ _) hω
  have hh0 : Measurable (centredField h u₀) := measurable_centredField hC.2.1 u₀
  have hmono : ∀ u, Monotone fun m => 𝒢 m u := by
    intro u
    refine monotone_nat_of_le_succ fun m => ?_
    rw [h𝒢 m u, h𝒢 (m + 1) u]
    exact histGerm_hull_mono hE hX hσ₀ ((hσ₀.1 m).min_const u) ((hσ₀.1 (m + 1)).min_const u)
      (fun ω => min_le_min (WithTop.coe_le_coe.2 (hσ₀.2.1 ω (Nat.le_succ m))) le_rfl) (hσζ m u)
      (hσζ (m + 1) u) (hAm m u) (hAm (m + 1) u) (hAK' m u) (hAK' (m + 1) u) hh0
  have hSm : ∀ m u, Measurable[𝒢 m u] fun ω => min u (σ₀ m ω) := by
    intro m u
    have h1 := (WithTop.measurable_untopD (0 : ℝ≥0)).comp ((hσ₀.1 m).min_const u).measurable
    have e : (fun ω => min u (σ₀ m ω)) = (fun x : WithTop ℝ≥0 => x.untopD 0) ∘
        fun ω => min (σ₀ m ω : WithTop ℝ≥0) u := by
      funext ω
      simp only [Function.comp_apply, ← WithTop.coe_min, WithTop.untopD_coe, min_comm]
    rw [e]
    exact h1.mono (h𝓓𝒢 m u) le_rfl
  have hBvj : Measurable (Function.uncurry fun s ω => B' s ω) :=
    measurable_uncurry_of_continuous_of_measurable hB'c hB'm
  have hexp : ∀ m (a : ℝ), Martingale (fun t ω => Real.exp (a * B' (min t (σ₀ m ω)) ω -
      a ^ 2 * ((min t (σ₀ m ω) : ℝ≥0) : ℝ) / 2)) (𝒢 m) P := by
    intro m a
    refine martingale_of_ae_eq_of_null (hYexp m a) (fun t => ?_) (fun t => ?_) (hnull m)
    · have hc : Measurable fun ω => min t (σ₀ m ω) := (hSm m t).mono ((𝒢 m).le t) le_rfl
      exact Real.measurable_exp.comp (((hBvj.comp (hc.prodMk measurable_id)).const_mul a).sub
        (((measurable_coe_nnreal_real.comp hc).const_mul _).div_const _))
    · filter_upwards [hYB m, hB'ae] with ω h1 h2
      simp only [h1 t, h2]
  have hTC := isTCExpMartingale_annClock hmono (fun ω => hσ₀.2.1 ω) hSm hB'c hB'0 hexp
  have hnullI : ∀ u (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[iSupFiltration 𝒢 u] N :=
    fun u N hN h0 => le_iSupFiltration 𝒢 0 u _ (hnull 0 u N hN h0)
  have hleI : ∀ m u, ((hσ₀.1 m).min_const u).measurableSpace ≤ iSupFiltration 𝒢 u :=
    fun m u => (h𝓓𝒢 m u).trans (le_iSupFiltration 𝒢 m u)
  refine ⟨iSupFiltration 𝒢, annClock σ₀, hTC, hnullI,
    adaptedBefore_of_announce hσ₀.1 hσ₀.2.2.2 hleI hnullI
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX)),
    fun i => adaptedBefore_of_announce hσ₀.1 hσ₀.2.2.2 hleI hnullI
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i)),
    fun j => adaptedBefore_of_announce hσ₀.1 hσ₀.2.2.2 hleI hnullI
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX j)), ?_⟩
  filter_upwards [hσ₀.2.2.2, ae_all_iff.2 hσ₀.2.2.1] with ω hω hlt u
  exact annClock_eq_clampT hlt hω u

end Germ

/-! ### The noise on the joint code space -/

section Codes

/-- The noise on the joint code space `XCode × PCode`: the frozen driving path up to the lifetime, continued by the
decoded Brownian code: `β_u = b(u ∧ ζ) + c(u) − c(u ∧ ζ)`. -/
def noiseY (y : XCode nL nR × PCode) (u : ℝ≥0) : ℝ :=
  cb y.1 (clampT (cζ y.1) u) + dec y.2 u - dec y.2 (clampT (cζ y.1) u)

theorem measurable_noiseY (u : ℝ≥0) : Measurable fun y : XCode nL nR × PCode => noiseY y u := by
  have hcl : Measurable fun y : XCode nL nR × PCode => clampT (cζ y.1) u :=
    measurable_clampT.comp ((measurable_cζ.comp measurable_fst).prodMk measurable_const)
  have h1 : Measurable fun y : XCode nL nR × PCode => cb y.1 (clampT (cζ y.1) u) :=
    measurable_dec.comp ((measurable_code_b.comp measurable_fst).prodMk hcl)
  have h2 : Measurable fun y : XCode nL nR × PCode => dec y.2 u :=
    measurable_dec.comp (measurable_snd.prodMk measurable_const)
  have h3 : Measurable fun y : XCode nL nR × PCode => dec y.2 (clampT (cζ y.1) u) :=
    measurable_dec.comp (measurable_snd.prodMk hcl)
  exact (h1.add h2).sub h3

/-- Before the lifetime the noise is the frozen driving path. -/
theorem noiseY_of_lt {y : XCode nL nR × PCode} {u : ℝ≥0} (hu : (u : ℝ≥0∞) < cζ y.1) :
    noiseY y u = cb y.1 u := by
  rw [noiseY, clampT_of_lt hu, add_sub_cancel_right]

theorem continuous_noiseY {y : XCode nL nR × PCode} (hb : Continuous (cb y.1))
    (hc : Continuous (dec y.2)) : Continuous (noiseY y) :=
  ((hb.comp (continuous_clampT _)).add hc).sub (hc.comp (continuous_clampT _))

/-- The Brownian code, killed (set to `0`) after an infinite lifetime. -/
def killB (x : XCode nL nR) (c : PCode) : PCode := if cζ x < ⊤ then c else 0

theorem measurable_killB : Measurable fun y : XCode nL nR × PCode => killB y.1 y.2 :=
  Measurable.ite ((measurableSet_lt measurable_cζ measurable_const).preimage measurable_fst)
    measurable_snd measurable_const

theorem dec_zero_code (t : ℝ≥0) : dec (0 : PCode) t = 0 := by
  unfold dec
  simp

/-- The paths of a code pair read as a killed driving process (lifetime, driver, force points). -/
theorem isMeasurableKilledDriving_codeY :
    IsMeasurableKilledDriving (fun t (y : XCode nL nR × PCode) => cw y.1 t)
      (fun i t (y : XCode nL nR × PCode) => cvL y.1 i t) (fun j t (y : XCode nL nR × PCode) => cvR y.1 j t)
      (fun y => cζ y.1) :=
  isMeasurableKilledDriving_paths (measurable_pathsOfCode.comp measurable_fst)

/-- The frozen code of a continuous noise with `B'₀ = 0`, read at `u ∧ ζ`, is the noise at `u ∧ ζ`. -/
theorem cb_frz_codeOf_clampT {Ω : Type*} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {B' : ℝ≥0 → Ω → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hc : Continuous (B' · ω)) (h0 : B' 0 ω = 0) (u : ℝ≥0) :
    cb (frz (codeOf xL xR B' W VL VR ζ ω)) (clampT (ζ ω) u) = B' (clampT (ζ ω) u) ω := by
  have hb : cb (codeOf xL xR B' W VL VR ζ ω) = fun t => B' t ω := by
    funext t
    exact dec_enc hc.continuousWithinAt
  rw [cb_frz (by rw [hb]; exact hc), frzPath]
  have hζ : cζ (codeOf xL xR B' W VL VR ζ ω) = ζ ω := rfl
  rw [hζ, hb]
  by_cases h0' : ζ ω = 0
  · simp only [h0', ↓reduceIte, clampT_zero, h0]
  · simp only [h0', ↓reduceIte]
    rcases lt_or_ge (u : ℝ≥0∞) (ζ ω) with hu | hu
    · rw [clampT_of_lt hu]; simp only [hu, ↓reduceIte]
    · rw [clampT_of_le hu]
      have hfin : ζ ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hu
      have hnlt : ¬ ((ζ ω).toNNReal : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_toNNReal hfin]; exact lt_irrefl _
      simp only [hnlt, ↓reduceIte]

end Codes

/-! ### The model evolution -/

section Model

universe u

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The model map `(ω, ω') ↦ (X₀(ω), code of B'(ω'), killed after an infinite lifetime)`. -/
def modelMap (X₀ : Ω → XCode nL nR) (B' : ℝ≥0 → Ω → ℝ) (p : Ω × Ω) : XCode nL nR × PCode :=
  (X₀ p.1, killB (X₀ p.1) (enc fun t => B' t p.2))

theorem measurable_enc_proc {α : Type*} [MeasurableSpace α] {B' : ℝ≥0 → α → ℝ}
    (hB'm : ∀ t, Measurable (B' t)) : Measurable fun a => enc fun t => B' t a :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => hB'm (dyad n k)

theorem measurable_modelMap {X₀ : Ω → XCode nL nR} (hX₀m : Measurable X₀) {B' : ℝ≥0 → Ω → ℝ}
    (hB'm : ∀ t, Measurable (B' t)) : Measurable (modelMap X₀ B') :=
  (hX₀m.comp measurable_fst).prodMk (measurable_killB.comp ((hX₀m.comp measurable_fst).prodMk
    ((measurable_enc_proc hB'm).comp measurable_snd)))

/-- **The model evolution.** On `Ω × Ω` with `P ⊗ P`, the processes read off the model map — the driving process
from the history code `X₀(ω)`, the noise `noiseY` from `X₀(ω)` and the code of an independent copy `B'(ω')` — form an
integrated `SLE_κ(ρ)` evolution. -/
theorem model_isIntegratedSLEEvolution (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {B' : ℝ≥0 → Ω → ℝ} (hB'm : ∀ t, Measurable (B' t)) (hB'c : ∀ ω, Continuous (B' · ω))
    (hB'0 : ∀ ω, B' 0 ω = 0) (hB'B : IsBrownianReal B' P) (hB'ae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω)
    {X₀ : Ω → XCode nL nR} (hX₀m : Measurable X₀)
    (hX₀ : ∀ᵐ ω ∂P, X₀ ω ∈ DetSet κ xL xR ρL ρR ∧ X₀ ω = frz (codeOf xL xR B' W VL VR ζ ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → cw (X₀ ω) t = W t ω ∧ (∀ i, cvL (X₀ ω) i t = VL i t ω) ∧
        ∀ j, cvR (X₀ ω) j t = VR j t ω) :
    ∃ 𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω)),
      IsIntegratedSLEEvolution κ xL xR ρL ρR (P.prod P) 𝓖 (fun t p => cw (modelMap X₀ B' p).1 t)
        (fun i t p => cvL (modelMap X₀ B' p).1 i t) (fun j t p => cvR (modelMap X₀ B' p).1 j t)
        (fun t p => noiseY (modelMap X₀ B' p) t) (fun p => cζ (modelMap X₀ B' p).1) := by
  have hE := hC.1
  have hX : IsMeasurableKilledDriving W VL VR ζ :=
    Coupling.isMeasurableKilledDriving_of_adaptedBefore hE.2.1 hE.2.2.1 hE.2.2.2.1
  obtain ⟨𝒢, ℓ, hTC, -, hWa, hVLa, hVRa, hℓ⟩ := exists_lifetimeGerm_clamp hC hκ hX hB'm hB'c hB'0 hB'ae
  have hFB := hB'B.toIsPreBrownianReal.isFilteredPreBrownian hB'm
  set 𝓦 := Filtration.natural B' fun t => (hB'm t).stronglyMeasurable with h𝓦
  obtain ⟨hβ, -⟩ := IsTCExpMartingale.isFilteredBrownianReal_complNoise hTC hFB hB'c hB'0
  set Q : Measure (Ω × Ω) := P.prod P with hQ
  set 𝓖 := usualAugmentation (prodFiltration 𝒢 𝓦) Q with h𝓖
  have hle : ∀ t, (𝒢 t).comap Prod.fst ≤ 𝓖 t := fun t =>
    (comap_fst_le_prodFiltration 𝒢 𝓦 t).trans (Ito.le_usualAugmentation _ Q t)
  set N : ℝ≥0 → Ω → ℝ := fun u ω => B' (ℓ u ω) ω with hN
  have hNB : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → ℓ u ω = u ∧ N u ω = B u ω := by
    filter_upwards [hℓ, hB'ae] with ω h1 h2 u hu
    have e := h1 u
    rw [clampT_of_lt hu] at e
    exact ⟨e, by simp only [hN, e, h2]⟩
  -- the lifted evolution
  have hÊ : IsIntegratedSLEEvolution κ xL xR ρL ρR Q 𝓖 (fun t p => W t p.1) (fun i t p => VL i t p.1)
      (fun j t p => VR j t p.1) (complNoise N ℓ B') (fun p => ζ p.1) := by
    refine ⟨Ito.isFilteredBrownianReal_usualAugmentation hβ, fun t A' hA' => hle t _ ⟨_, hWa t A' hA', rfl⟩,
      fun i t A' hA' => hle t _ ⟨_, hVLa i t A' hA', rfl⟩,
      fun j t A' hA' => hle t _ ⟨_, hVRa j t A' hA', rfl⟩, ?_⟩
    have hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) ∧
        ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → ℓ u ω = u ∧ N u ω = B u ω := by
      filter_upwards [hE.2.2.2.2, hNB] with ω h1 h2 using ⟨h1, h2⟩
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hpath] with p hp
    exact isIntegratedSLEPath_congr hp.1 rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) fun t ht => by
        rw [complNoise_of_eq (hp.2 t ht).1, (hp.2 t ht).2]
  -- the read-through processes are a modification
  have hgm := measurable_modelMap hX₀m hB'm
  refine ⟨𝓖, isIntegratedSLEEvolution_congr_ae hÊ
    (fun t N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t)
    (isMeasurableKilledDriving_comp isMeasurableKilledDriving_codeY hgm)
    (fun t => (measurable_noiseY t).comp hgm) ?_ ?_⟩
  · have hgood : ∀ᵐ ω ∂P, (X₀ ω ∈ DetSet κ xL xR ρL ρR ∧ X₀ ω = frz (codeOf xL xR B' W VL VR ζ ω) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → cw (X₀ ω) t = W t ω ∧ (∀ i, cvL (X₀ ω) i t = VL i t ω) ∧
          ∀ j, cvR (X₀ ω) j t = VR j t ω) ∧ ∀ u, ℓ u ω = clampT (ζ ω) u := by
      filter_upwards [hX₀, hℓ] with ω h1 h2 using ⟨h1, h2⟩
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood] with p hp
    obtain ⟨⟨-, hfrz, hagr⟩, hℓp⟩ := hp
    have hζp : cζ (X₀ p.1) = ζ p.1 := by rw [hfrz]; rfl
    refine ⟨hζp, fun t ht => hagr t ht, fun t => ?_⟩
    simp only [noiseY, modelMap, complNoise, hN, hℓp, hζp]
    rw [hfrz, cb_frz_codeOf_clampT (hB'c p.1) (hB'0 p.1)]
    have hc2 : ∀ s, dec (enc fun r => B' r p.2) s = B' s p.2 := fun s =>
      dec_enc (hB'c p.2).continuousWithinAt
    by_cases hfin : ζ p.1 < ⊤
    · have hk : killB (frz (codeOf xL xR B' W VL VR ζ p.1)) (enc fun r => B' r p.2) =
          enc fun r => B' r p.2 := by
        simp only [killB, show cζ (frz (codeOf xL xR B' W VL VR ζ p.1)) < ⊤ from hfin, ↓reduceIte]
      rw [hk, hc2, hc2]
    · have htop : ζ p.1 = ⊤ := not_lt_top_iff.1 hfin
      have hk : killB (frz (codeOf xL xR B' W VL VR ζ p.1)) (enc fun r => B' r p.2) = 0 := by
        simp only [killB, show ¬ cζ (frz (codeOf xL xR B' W VL VR ζ p.1)) < ⊤ from hfin, ↓reduceIte]
      rw [hk, htop, dec_zero_code, dec_zero_code, clampT_top]
      ring
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hX₀] with p hp
    obtain ⟨⟨⟨⟨⟨-, -, hpath⟩, -⟩, -⟩, -⟩, -, -⟩ := hp
    exact isIntegratedSLEPath_congr hpath rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) fun t ht => noiseY_of_lt ht

end Model

end Exist

end InteractingSLE
