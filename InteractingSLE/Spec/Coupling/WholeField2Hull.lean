import InteractingSLE.Spec.Coupling.WholeField2Code
import InteractingSLE.Spec.Coupling.WholeField2Cap
import InteractingSLE.Spec.Coupling.AnnounceLifetime
import InteractingSLE.Spec.Coupling.Assembly11Drv
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.GFF.LocalSets.Prop38
import InteractingSLE.GFF.LocalSets.Prop39
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling
import SupercriticalConformalCovariance.GM24.TVReduce
import InteractingSLE.WangWu.Defs

/-!
# History marking of the hull `K_τ` for the frozen optional hull coupling

Packet PROVE-WHOLEFIELD2 (ruling R36), item (1). Specification Aux. lemmas 18–19 (pp. 96–100). The abstract coding
theorem `WholeField.isHistoryAvoidanceLocal_of_capacity` (`WholeField2Code`) is applied to the frozen coupling
`IsOptionalHullCoupling`:

* **the clock** `Φ(K) = hcapHit K / 2` (`WholeField2Cap`) reads `Φ(K_t) = t` from the hulls of a driver continuous
  before the lifetime with `W₀ = 0` (`hcapHit_fwdHull_rpath`, through the driver frozen after a time `t₂ < ζ`);
* **the announcing sequence** of the lifetime in the frozen driving filtration
  (`exists_isAnnouncingSeq_of_adapted`): the landed construction `Coupling.exists_isAnnouncingSeq_le` uses only the
  adaptedness of the state, right continuity of the filtration, its null sets at time `0` and the pathwise conditions,
  so it is restated for an arbitrary such filtration;
* **local sets of `h` are local sets of `h − 𝔥₀`** (`IsLocalSet.sub_dist`) for a deterministic distribution harmonic on
  `ℍ`, and a local set has a hitting-measurable version (`IsLocalSet.exists_measurable_version`);
* **`isHistoryAvoidanceLocal_hull`**: for every stopping time `τ < ζ` of the frozen driving filtration and every
  hitting-measurable version `A` of `K_τ`, the centred field `h − 𝔥₀` satisfies the history-marked avoidance
  criterion for `A` and the marks `𝓕_τ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LocalSets QuantumZipper LQGMetric Coupling

/-! ### The announcing sequence in any usual filtration -/

section Announce

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

open scoped Classical in
/-- **The lifetime has an announcing sequence in every right-continuous filtration containing the null sets to which
the state is adapted** (the construction of `Coupling.exists_isAnnouncingSeq_le`, Astra §1 (1.2), restated for a
general filtration `𝓖`: it uses only these properties of the filtration, the pathwise conditions of the integrated
equation and Aux. lemma 3's terminal state). -/
theorem exists_isAnnouncingSeq_of_adapted [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
    [𝓖.IsRightContinuous] (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    (hWa : AdaptedBefore 𝓖 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω))
    (hthr : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T)
          (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ T : ℕ → Ω → ℝ≥0, IsAnnouncingSeq 𝓖 P ζ T ∧ ∀ n ω, T n ω ≤ n := by
  -- the good event: the pathwise conditions and Aux. lemma 3's terminal state
  set good : Ω → Prop := fun ω =>
    IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
      (fun t => B t ω) (ζ ω) ∧
    ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T)
          (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, hthr] with ω h1 h2 using ⟨h1, h2⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[𝓖 0] G := by
    have := (hnull _ hGm.compl hGc).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hF : ∀ ω ∈ G, Sec2.IsForcePath xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (ζ ω) := fun ω hω => (hGgood ω hω).1.isForcePath
  have hcont : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
    fun ω hω => (hF ω hω).continuousOn_w.prodMk ((continuousOn_pi.2 (hF ω hω).continuousOn_vL).prodMk
      (continuousOn_pi.2 (hF ω hω).continuousOn_vR))
  -- the random candidates
  set a : ℕ → ℕ → Ω → WithTop ℝ≥0 := fun p k ω => if ω ∈ G then
    candTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) p k else ⊤
    with ha_def
  have hatop : ∀ p k, (∀ ω ∈ G, candTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (ζ ω) p k = ⊤) → IsStoppingTime 𝓖 (a p k) := by
    intro p k htop
    have : a p k = fun _ => ⊤ := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [ha_def, hω, ite_true]; exact htop ω hω
      · simp only [ha_def, hω, ite_false]
    rw [this]
    exact isStoppingTime_top'
  have ha : ∀ p k, IsStoppingTime 𝓖 (a p k) := by
    intro p k
    by_cases hc : (Nat.unpair p).1 < nL
    · set j : Fin nL := ⟨(Nat.unpair p).1, hc⟩ with hj
      set m := (Nat.unpair p).2 with hm
      by_cases hs : (∑ i ∈ Finset.Iic j, ρL i) ≤ -2
      · have e : a p k = fun ω => if ω ∈ G then hitBelow (fun s =>
            (fun x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => sideVal m j x.1 x.2.1) (stateAt W VL VR s ω))
            (ζ ω) (1 / ((k : ℝ) + 1)) else ⊤ := by
          funext ω
          simp only [ha_def, candTime, hc, ↓reduceDIte, hitL, ← hj, ← hm, hs, ↓reduceIte, stateAt]
        rw [e]
        exact isStoppingTime_hitBelow_state hWa hVLa hVRa hG0 hcont
          ((continuous_sideVal m j).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))) _
      · exact hatop p k fun ω _ => by
          simp only [candTime, hc, ↓reduceDIte, hitL, ← hj, hs, ↓reduceIte]
    by_cases hc' : (Nat.unpair p).1 - nL < nR
    · set j : Fin nR := ⟨(Nat.unpair p).1 - nL, hc'⟩ with hj
      set m := (Nat.unpair p).2 with hm
      by_cases hs : (∑ i ∈ Finset.Iic j, ρR i) ≤ -2
      · have e : a p k = fun ω => if ω ∈ G then hitBelow (fun s =>
            (fun x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => sideVal m j (-x.1) (-x.2.2))
              (stateAt W VL VR s ω)) (ζ ω) (1 / ((k : ℝ) + 1)) else ⊤ := by
          funext ω
          simp only [ha_def, candTime, hc, hc', ↓reduceDIte, hitL, ← hj, ← hm, hs, ↓reduceIte, stateAt]
          rfl
        rw [e]
        exact isStoppingTime_hitBelow_state hWa hVLa hVRa hG0 hcont
          ((continuous_sideVal m j).comp
            (continuous_fst.neg.prodMk (continuous_snd.comp continuous_snd).neg)) _
      · exact hatop p k fun ω _ => by
          simp only [candTime, hc, hc', ↓reduceDIte, hitL, ← hj, hs, ↓reduceIte]
    · exact hatop p k fun ω _ => by simp only [candTime, hc, hc', ↓reduceDIte]
  have hmono : ∀ p ω, Monotone fun k => a p k ω := by
    intro p ω
    by_cases hω : ω ∈ G
    · simp only [ha_def, hω, ite_true]
      exact candTime_mono p
    · simp only [ha_def, hω, ite_false]
      exact monotone_const
  have hbdd : ∀ ω ∈ G, ∀ p, BddSeq (a p) ω ↔ ∃ M : ℕ, ∀ k, candTime ρL ρR (fun t => W t ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) p k ≤ ((M : ℝ≥0) : WithTop ℝ≥0) := by
    intro ω hω p
    simp only [BddSeq, ha_def, hω, ite_true]
  refine exists_isAnnouncingSeq_le_of_candidates ha hmono ?_ ?_ ?_
  · filter_upwards [hGae] with ω hω p hp k
    have := candTime_lt_of_bdd ((hbdd ω hω p).1 hp) k
    simpa only [ha_def, hω, ite_true] using this
  · filter_upwards [hGae] with ω hω t ht
    obtain ⟨K, hK⟩ := exists_eventually_le_candTime (hF ω hω) ht
    refine ⟨K, fun p hp k hk => ?_⟩
    have := hK p ((hbdd ω hω p).1 hp) k hk
    simpa only [ha_def, hω, ite_true] using this
  · filter_upwards [hGae] with ω hω hζ
    have hTζ : (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hζ
    have hT : 0 < (ζ ω).toNNReal := by
      refine pos_iff_ne_zero.2 fun h0 => hseed ((hF ω hω).threshold_of_eq_zero ?_)
      rw [← hTζ, h0, ENNReal.coe_zero]
    obtain ⟨w₀, vL₀, vR₀, hlim, hth⟩ := (hGgood ω hω).2 _ hT hTζ
    obtain ⟨p, hp⟩ := exists_bdd_candTime (hF ω hω) hT hTζ hlim hth
    exact ⟨p, (hbdd ω hω p).2 hp⟩

end Announce

/-! ### The clock of the Loewner hulls -/

/-- **The clock before the lifetime.** For a driver `w` continuous before `ζ` with `w 0 = 0`, the hull of the real
path at a time `t < ζ` has measurable capacity `2t`. -/
theorem hcapHit_fwdHull_rpath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    hcapHit (fwdHull (fun s : ℝ => w s.toNNReal) t) = 2 * (t : ℝ≥0∞) := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  have hc := Ito.continuous_clampDrv (W := Ito.rpath w) t₂.coe_nonneg (Ito.continuousOn_rpath hw ht₂ζ)
  have heq : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull (Ito.clampDrv (Ito.rpath w) t₂) t :=
    fwdHull_eq_of_eqOn t.coe_nonneg htt₂' fun r hr =>
      (Ito.clampDrv_eqOn (W := Ito.rpath w) (T := (t₂ : ℝ)) hr).symm
  have h0 : Ito.clampDrv (Ito.rpath w) t₂ 0 = 0 := by
    rw [Ito.clampDrv_eqOn ⟨le_rfl, t₂.coe_nonneg⟩]
    simp [Ito.rpath, hw0]
  rw [heq, hcapHit_fwdHull hc h0 t.coe_nonneg, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_coe_nnreal]

/-- The clock `Φ(K) = hcapHit K / 2`. -/
def hullClock (K : Set ℂ) : ℝ≥0∞ := hcapHit K / 2

theorem measurable_hullClock : Measurable[hittingSigma] hullClock := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  exact measurable_hcapHit.div_const _

theorem hullClock_fwdHull_rpath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    hullClock (fwdHull (fun s : ℝ => w s.toNNReal) t) = t := by
  rw [hullClock, hcapHit_fwdHull_rpath hw hw0 ht]
  rw [mul_comm]
  exact ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top

/-! ### Local sets of `h` and of `h − 𝔥₀` -/

section Shift

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem measurable_sub_dist (T : DistOn upperHalfPlaneOpens) :
    Measurable fun x : DistOn upperHalfPlaneOpens => x - T :=
  measurable_distOn_iff.2 fun φ => by
    simp only [sub_apply]
    exact (measurable_distOn_apply φ).sub_const _

theorem measurable_add_dist (T : DistOn upperHalfPlaneOpens) :
    Measurable fun x : DistOn upperHalfPlaneOpens => x + T :=
  measurable_distOn_iff.2 fun φ => by
    simp only [add_apply]
    exact (measurable_distOn_apply φ).add_const _

omit mΩ in
/-- Translating a random distribution by a deterministic one does not change the σ-algebra it generates. -/
theorem comap_sub_dist (X : Ω → DistOn upperHalfPlaneOpens) (T : DistOn upperHalfPlaneOpens) :
    MeasurableSpace.comap (fun ω => X ω - T) inferInstance = MeasurableSpace.comap X inferInstance := by
  have e : (fun ω => X ω - T) = (fun x => x - T) ∘ X := rfl
  rw [e, ← MeasurableSpace.comap_comp]
  congr 1
  refine le_antisymm (measurable_sub_dist T).comap_le fun S hS => ?_
  refine ⟨(fun x => x + T) ⁻¹' S, measurable_add_dist T hS, ?_⟩
  ext x
  simp

/-- **Local sets of `h` are local sets of `h − T`** for a deterministic distribution `T` harmonic on `ℍ` (the
harmonic part of the two-step model absorbs `−T`). -/
theorem IsLocalSet.sub_dist {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hloc : IsLocalSet A h P) {T : DistOn upperHalfPlaneOpens} (hT : IsHarmonicDistOn T H) :
    IsLocalSet A (fun ω => h ω - T) P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hAE, hsub, Ω', mΩ', P', hP', A', h₁, h₂, hA'm, hh₁m, hh₂m, hA'sub, hharm, hcond, hlaw⟩ :=
    hloc
  have hF : Measurable fun p : Set ℂ × DistOn upperHalfPlaneOpens => (p.1, p.2 - T) :=
    measurable_fst.prodMk ((measurable_sub_dist T).comp measurable_snd)
  have hsum : Measurable fun ω' => h₁ ω' + h₂ ω' :=
    measurable_distOn_iff.2 fun φ => by
      simp only [add_apply]
      exact ((measurable_distOn_apply φ).comp hh₁m).add ((measurable_distOn_apply φ).comp hh₂m)
  refine ⟨hF.comp_aemeasurable hAE, hsub, Ω', mΩ', P', hP', A', fun ω' => h₁ ω' - T, h₂, hA'm,
    (measurable_sub_dist T).comp hh₁m, hh₂m, hA'sub, ?_, ?_, ?_⟩
  · filter_upwards [hharm] with ω' hω'
    exact IsHarmonicDistOn.sub' (hA'sub ω').2 hω' (IsHarmonicDistOn.mono hT sdiff_subset)
  · rw [comap_sub_dist]
    exact hcond
  · have e1 : (fun ω' => (A' ω', (h₁ ω' - T) + h₂ ω')) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (p.1, p.2 - T)) ∘
          fun ω' => (A' ω', h₁ ω' + h₂ ω') := by
      funext ω'
      simp only [Function.comp_apply, Prod.mk.injEq, true_and]
      abel
    have e2 : (fun ω => (A ω, h ω - T)) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (p.1, p.2 - T)) ∘ fun ω => (A ω, h ω) := rfl
    rw [e1, ← Measure.map_map hF (hA'm.prodMk hsum), hlaw, e2,
      AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hAE]

/-- **A local set has a hitting-measurable version.** -/
theorem IsLocalSet.exists_measurable_version {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hloc : IsLocalSet A h P) (hh : Measurable h) :
    ∃ A' : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A' ∧ A' =ᵐ[P] A ∧ IsLocalSet A' h P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hAE, hsub, Ω', mΩ', P', hP', A'', h₁, h₂, hA''m, hh₁m, hh₂m, hA''sub, hharm, hcond, hlaw⟩ :=
    hloc
  have hA : AEMeasurable A P := hAE.fst
  refine ⟨hA.mk A, hA.measurable_mk, hA.ae_eq_mk.symm, (hA.measurable_mk.prodMk hh).aemeasurable, ?_,
    Ω', mΩ', P', hP', A'', h₁, h₂, hA''m, hh₁m, hh₂m, hA''sub, hharm, hcond, ?_⟩
  · filter_upwards [hsub, hA.ae_eq_mk] with ω h1 h2
    rwa [← h2]
  · rw [hlaw]
    refine Measure.map_congr ?_
    filter_upwards [hA.ae_eq_mk] with ω hω
    rw [hω]

end Shift

/-! ### The frozen coupling -/

section Coupling

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

/-- The centred field `h⁰ = h − 𝔥₀` of a coupling, `𝔥₀ = ∫ u₀ · φ`. -/
def centredField (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) : Ω → DistOn upperHalfPlaneOpens :=
  fun ω => h ω - smoothDist upperHalfPlaneOpens u₀

omit [IsProbabilityMeasure P] in
theorem measurable_centredField (hh : Measurable h) (u₀ : ℂ → ℝ) : Measurable (centredField h u₀) :=
  (measurable_sub_dist _).comp hh

/-- A bounded harmonic extension defines a distribution harmonic on `ℍ`. -/
theorem isHarmonicDistOn_smoothDist {u₀ : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u₀ H) :
    IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H := by
  have hc : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) := fun z hz =>
    (hu z hz).1.continuousAt.continuousWithinAt
  refine ⟨u₀, hu, fun φ _ => ?_⟩
  rw [smoothDist_apply hc]
  congr 1
  funext z
  ring

omit mΩ [IsProbabilityMeasure P] in
theorem centredField_apply (h : Ω → DistOn upperHalfPlaneOpens) {u₀ : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u₀ H) (ω : Ω) (φ : TestOn upperHalfPlaneOpens) :
    centredField h u₀ ω φ = h ω φ - ∫ z, u₀ z * φ z := by
  have hc : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) := fun z hz =>
    (hu z hz).1.continuousAt.continuousWithinAt
  rw [centredField, sub_apply, smoothDist_apply hc]
  congr 2
  funext z
  ring

/-- **History marking of `K_τ` for the frozen optional hull coupling** (Aux. lemmas 18–19, first conclusion, at
every stopping time below the lifetime). For a coupling satisfying `IsOptionalHullCoupling` with `κ > 0`, a stopping
time `τ < ζ` of the frozen driving filtration and a hitting-measurable version `A` of the hull `K_τ`, the centred
field `h − 𝔥₀` satisfies the history-marked avoidance criterion for `A` and the stopped history `𝓕_τ`. -/
theorem isHistoryAvoidanceLocal_hull (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :
    IsHistoryAvoidanceLocal hτ.measurableSpace A (centredField h u₀) P := by
  obtain ⟨hE, hhm, -, hX', hker⟩ := hC
  have hFd := isHarmonicDistOn_smoothDist hu₀.1
  have hh0m := measurable_centredField hhm u₀
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- at an inadmissible seed the lifetime vanishes, and no stopping time lies below it
    exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hτζ] with ω hp hlt
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
      exact ENNReal.not_lt_zero hlt
    obtain ⟨_, h⟩ := hF.exists
    exact h
  · have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
    obtain ⟨σ, hσ, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B) (κ := κ)
      (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
      (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
      (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
      hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
    refine isHistoryAvoidanceLocal_of_capacity (K := fun t ω => fwdHull (fun s : ℝ => W s.toNNReal ω) t)
      hh0m measurable_hullClock ?_ hσ ?_ hτ hτζ hA hAK
    · filter_upwards [hE.2.2.2.2] with ω hp t ht
      exact hullClock_fwdHull_rpath hp.2.2.2.1 hp.1 ht
    · intro S hS hSζ
      have hloc := IsLocalSet.sub_dist (hker S hS hSζ).1 hFd
      obtain ⟨A', hA'm, hA'e, hA'loc⟩ := IsLocalSet.exists_measurable_version hloc hh0m
      exact ⟨A', hA'm, hA'e, LocalSets.IsLocalSet.isMarkedAvoidanceLocal hh0m hA'm hA'loc⟩

end Coupling

end WholeField

end InteractingSLE
