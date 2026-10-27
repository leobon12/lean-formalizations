import MatedCRTHarmonic.GMS4b.L46TTransfer
import MatedCRTHarmonic.GMS4c.L46SPrimeTail
import MatedCRTHarmonic.GMS4cP.LocalEvents

/-!
# The all-visit form of the (4.16) transfer of [18] Lemma 4.6

Source: [18] Lemma 4.6 and its proof via Lemma 4.3 and (4.16) (`2070–2116`).

The first-visit inner degree `deg^ε_in(z) = deg^ε_in(η, τ_z)` is not a function of the local data: the
excursions into an observation disk do not record which one visits `z` first. The **all-visit** event
`InnerAt c S ε N = {∃ t, c t ∈ S, deg^ε_in(c, t) ≥ N}` dominates the first-visit event, is local on the
non-escape event (`GMS4cP/LocalEvents.lean`), and the `innerDegreeBoundPolylog_prime_coupled` extends
L46S's Brownian-chain count to it on the γ-cone. Hölder's inequality (4.16) applied to the escape event and
The all-visit event then gives the first-visit polylog bound `InnerDegreeBoundPolylog` for the target.

`L43PLocalReconstruction` is the exact form of measurable Lemma 4.3 consumed here: one pair of Borel sets of
The observation `(h|_V, h^IG|_V, U)` which almost surely equals the escape and the all-visit non-escape events
under both laws.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4c

/-- The integer threshold equivalent to `deg > log(1/ε)^(k(1+ζ)+1)`. -/
def l43pThreshold (ε : ℝ) (k : ℕ) (ζ : ℝ) : ℕ :=
  ⌊Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)⌋₊ + 1

theorem ofReal_lt_coe_enat_iff (x : ℝ) (d : ℕ∞) :
    ENNReal.ofReal x < (d : ℝ≥0∞) ↔ ((⌊x⌋₊ + 1 : ℕ) : ℕ∞) ≤ d := by
  induction d using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [ENat.toENNReal_coe, Nat.cast_le]
    rcases le_or_gt x 0 with hx | hx
    · rw [ENNReal.ofReal_of_nonpos hx, Nat.floor_of_nonpos hx, zero_add, Nat.one_le_iff_ne_zero]
      simp [pos_iff_ne_zero]
    · rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx.le,
        Nat.add_one_le_iff, Nat.floor_lt hx.le]

/-- **Measurable Lemma 4.3 for the all-visit inner degree**: one pair of Borel sets of the three-coordinate
observation reconstructs the escape event and the all-visit inner-degree event on its complement, almost
surely under both laws. -/
def L43PLocalReconstruction {Ωγ Ω₀ : Type*} [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    (V U : TopologicalSpace.Opens ℂ) (Pγ : Measure Ωγ) (P₀ : Measure Ω₀)
    (hγ hIGγ : Ωγ → LQGMetric.DistC) (uγ : Ωγ → ℝ)
    (h₀ hIG₀ : Ω₀ → LQGMetric.DistC) (u₀ : Ω₀ → ℝ)
    (cγ : Ωγ → ℝ → ℂ) (c₀ : Ω₀ → ℝ → ℂ) (S : Set ℂ) (ε : ℝ) (N : ℕ) : Prop :=
  ∃ E A : Set (L46TLocalFieldPhase V), MeasurableSet E ∧ MeasurableSet A ∧
    ({ω | EscBad (cγ ω) S U ε} =ᵐ[Pγ] l46tLocalFieldPhase V hγ hIGγ uγ ⁻¹' E) ∧
    ({ω | EscBad (c₀ ω) S U ε} =ᵐ[P₀] l46tLocalFieldPhase V h₀ hIG₀ u₀ ⁻¹' E) ∧
    ({ω | InnerAt (cγ ω) S ε N ∧ ¬ EscBad (cγ ω) S U ε} =ᵐ[Pγ]
      l46tLocalFieldPhase V hγ hIGγ uγ ⁻¹' A) ∧
    ({ω | InnerAt (c₀ ω) S ε N ∧ ¬ EscBad (c₀ ω) S U ε} =ᵐ[P₀]
      l46tLocalFieldPhase V h₀ hIG₀ u₀ ⁻¹' A)

/-- The two applications of (4.16) to the all-visit events. -/
theorem l43p_innerAt_le_holder {Ωγ Ω₀ : Type*} [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V U : TopologicalSpace.Opens ℂ} {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → LQGMetric.DistC} {uγ : Ωγ → ℝ}
    {h₀ hIG₀ : Ω₀ → LQGMetric.DistC} {u₀ : Ω₀ → ℝ}
    {cγ : Ωγ → ℝ → ℂ} {c₀ : Ω₀ → ℝ → ℂ} {S : Set ℂ} {ε : ℝ} {N : ℕ} {p q : ℝ}
    (hcmp : L46TPhaseLawComparison V Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀ p q)
    (hloc : L43PLocalReconstruction V U Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀ cγ c₀ S ε N) :
    P₀ {ω | InnerAt (c₀ ω) S ε N} ≤
      (∫⁻ x, hcmp.density x ^ p
        ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p) *
        (Pγ {ω | EscBad (cγ ω) S U ε}) ^ (1 / q) +
      (∫⁻ x, hcmp.density x ^ p
        ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p) *
        (Pγ {ω | InnerAt (cγ ω) S ε N}) ^ (1 / q) := by
  obtain ⟨E, A, hE, hA, hγE, h₀E, hγA, h₀A⟩ := hloc
  set K : ℝ≥0∞ := (∫⁻ x, hcmp.density x ^ p
    ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p)
  have hq : 0 ≤ 1 / q := one_div_nonneg.mpr hcmp.conjugate.symm.pos.le
  have hesc : P₀ {ω | EscBad (c₀ ω) S U ε} ≤ K * (Pγ {ω | EscBad (cγ ω) S U ε}) ^ (1 / q) := by
    rw [measure_congr h₀E, measure_congr hγE]
    exact l46t_phase_badEvent_le_holder hcmp hE
  have hinn : P₀ {ω | InnerAt (c₀ ω) S ε N ∧ ¬ EscBad (c₀ ω) S U ε} ≤
      K * (Pγ {ω | InnerAt (cγ ω) S ε N}) ^ (1 / q) := by
    rw [measure_congr h₀A]
    refine (l46t_phase_badEvent_le_holder hcmp hA).trans ?_
    rw [← measure_congr hγA]
    gcongr
    exact fun h => h.1
  calc
    P₀ {ω | InnerAt (c₀ ω) S ε N} ≤
        P₀ ({ω | EscBad (c₀ ω) S U ε} ∪
          {ω | InnerAt (c₀ ω) S ε N ∧ ¬ EscBad (c₀ ω) S U ε}) := by
      refine measure_mono fun ω hω => ?_
      by_cases he : EscBad (c₀ ω) S U ε
      · exact Or.inl he
      · exact Or.inr ⟨hω, he⟩
    _ ≤ P₀ {ω | EscBad (c₀ ω) S U ε} +
        P₀ {ω | InnerAt (c₀ ω) S ε N ∧ ¬ EscBad (c₀ ω) S U ε} := measure_union_le _ _
    _ ≤ _ := add_le_add hesc hinn

/-- The all-visit event of the translated curve is controlled by the all-visit polylog tail. -/
theorem innerAt_translate_subset {c : ℝ → ℂ} {z₀ w : ℂ} {ρ r ε ζ : ℝ} {k : ℕ}
    (hsub : ball w r ⊆ ball z₀ ρ) (h : InnerAt (l46tTranslateCurve z₀ c) (ball w r) ε
      (l43pThreshold ε k ζ)) :
    ∃ z ∈ ball (0 : ℂ) ρ, ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
      ((degreeInPrime ε c z : ℕ∞) : ℝ≥0∞) := by
  obtain ⟨t, ht, hdeg⟩ := h
  refine ⟨c t, ?_, ?_⟩
  · have := hsub ht
    simpa [Metric.mem_ball, dist_eq_norm, l46tTranslateCurve] using this
  · rw [ofReal_lt_coe_enat_iff]
    have hcurve : l46tTranslateCurve z₀ c = simC 1 z₀ one_ne_zero ∘ c := by
      funext u
      simp [l46tTranslateCurve, simC_apply]
    rw [hcurve, locDegIn_simC] at hdeg
    exact hdeg.trans (le_iSup_of_le t (le_iSup_of_le rfl le_rfl))

/-- The first-visit failure is contained in the all-visit one when first hitting times are attained. -/
theorem l46tInnerBad_subset_innerAt {Ω : Type*} {c : Ω → ℝ → ℂ} {S : Set ℂ} {ε ζ : ℝ}
    {k : ℕ} {ω : Ω} (hhit : ∀ z ∈ S, c ω (hitTime (c ω) z) = z)
    (h : ω ∈ l46tInnerBad c S ε k ζ) : InnerAt (c ω) S ε (l43pThreshold ε k ζ) := by
  obtain ⟨z, hz, hbad⟩ := h
  rw [ofReal_lt_coe_enat_iff] at hbad
  exact ⟨hitTime (c ω) z, (hhit z hz).symm ▸ hz, hbad⟩

/-- **Transferred Lemma 4.6 on one disk**, from the all-visit γ-cone tail. -/
theorem l43p_innerDegreeBound_disk
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hS : Ω → LQGMetric.DistC) (uS : Ω → ℝ) (k : ℕ)
    (hprime : InnerDegreeBoundPolylogPrime (MoTInput.cellModelOfCoupling D hγ) (2 * k))
    (M₀ : GMSLemma27.CellModel γ) (hIGtarget : M₀.Ω → LQGMetric.DistC) (u₀ : M₀.Ω → ℝ)
    (hhit : ∀ᵐ ω ∂M₀.P, ∀ z : ℂ, M₀.curve ω (hitTime (M₀.curve ω) z) = z)
    (z₀ w : ℂ) {ρ r R : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hsub : ball w r ⊆ ball z₀ ρ) (hrR : r < R)
    (V : TopologicalSpace.Opens ℂ) {p q : ℝ}
    (hcmp : L46TPhaseLawComparison V P M₀.P
      (l46tTranslatedField z₀ hS) (l46tTranslatedField z₀ hIG₀) uS
      M₀.field hIGtarget u₀ p q)
    (hlocal : ∀ (ζ ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 →
      L43PLocalReconstruction V ⟨ball w R, isOpen_ball⟩ P M₀.P
        (l46tTranslatedField z₀ hS) (l46tTranslatedField z₀ hIG₀) uS
        M₀.field hIGtarget u₀
        (fun ω => l46tTranslateCurve z₀ (η ω)) M₀.curve
        (ball w r) ε (l43pThreshold ε (2 * k) ζ)) :
    ∀ ζ ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
        M₀.P (l46tInnerBad M₀.curve (ball w r) ε (2 * k) ζ) ≤
          ENNReal.ofReal (C * ε ^ s) := by
  let Mγ := MoTInput.cellModelOfCoupling D hγ
  let _ : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hSLE : GMSLemma27.SegmentsContainBalls Mγ :=
    MoTInput.segmentsContainBalls_of_coupling D hγ
  have hGMC : GMSLemma27.GMCLowerTail γ :=
    GMCFacts.gmcLowerTail_holds hγ.1 hγ.2
  have hcone : GMCFacts.ConeAreaExists γ P X B B' :=
    GMCFacts.coneAreaExists_holds hγ.1 hγ.2 D.gff D.bm_B D.bm_B' D.indep_cone
  have hdom : GMSLemma27.AreaDominatesWholePlaneGFF Mγ :=
    MoTInput.areaDominatesWholePlaneGFF_of_coupling D hγ hcone
  intro ζ hζ s
  obtain ⟨Cdeg, hdeg⟩ := hprime ρ hρ ζ hζ (q * s)
  obtain ⟨Cloc, hloc⟩ := l46t_localization_shifted_disk Mγ hγ.1
    hSLE hGMC hdom z₀ w hρ hsub hrR (q * s)
  let K : ℝ≥0∞ :=
    (∫⁻ x, hcmp.density x ^ p
      ∂(P.map (l46tLocalFieldPhase V
        (l46tTranslatedField z₀ hS) (l46tTranslatedField z₀ hIG₀) uS))) ^ (1 / p)
  have hK : K < ⊤ := l46t_phase_holder_constant_finite hcmp
  have hq : 0 < q := hcmp.conjugate.symm.pos
  let C : ℝ := K.toReal * (max Cloc 0) ^ (1 / q) + K.toReal * (max Cdeg 0) ^ (1 / q)
  refine ⟨C, fun ε hε => ?_⟩
  set N := l43pThreshold ε (2 * k) ζ
  have hlocγ : P {ω | EscBad (l46tTranslateCurve z₀ (η ω)) (ball w r) (ball w R) ε} ≤
      ENNReal.ofReal (Cloc * ε ^ (q * s)) := hloc ε hε
  have hdegγ : P {ω | InnerAt (l46tTranslateCurve z₀ (η ω)) (ball w r) ε N} ≤
      ENNReal.ofReal (Cdeg * ε ^ (q * s)) := by
    refine (measure_mono fun ω hω => ?_).trans (hdeg ε hε)
    exact innerAt_translate_subset (k := 2 * k) hsub hω
  have hholder := l43p_innerAt_le_holder hcmp (hlocal ζ ε hε)
  have htarget : M₀.P (l46tInnerBad M₀.curve (ball w r) ε (2 * k) ζ) ≤
      M₀.P {ω | InnerAt (M₀.curve ω) (ball w r) ε N} := by
    refine measure_mono_ae ?_
    filter_upwards [hhit] with ω hω hbad
    exact l46tInnerBad_subset_innerAt (fun z _ => hω z) hbad
  calc
    M₀.P (l46tInnerBad M₀.curve (ball w r) ε (2 * k) ζ) ≤
        M₀.P {ω | InnerAt (M₀.curve ω) (ball w r) ε N} := htarget
    _ ≤ K * (P {ω | EscBad (l46tTranslateCurve z₀ (η ω)) (ball w r) (ball w R) ε}) ^ (1 / q) +
        K * (P {ω | InnerAt (l46tTranslateCurve z₀ (η ω)) (ball w r) ε N}) ^ (1 / q) :=
      hholder
    _ ≤ K * (ENNReal.ofReal (Cloc * ε ^ (q * s))) ^ (1 / q) +
        K * (ENNReal.ofReal (Cdeg * ε ^ (q * s))) ^ (1 / q) := by
      gcongr
    _ ≤ ENNReal.ofReal (K.toReal * (max Cloc 0) ^ (1 / q) * ε ^ s) +
        ENNReal.ofReal (K.toReal * (max Cdeg 0) ^ (1 / q) * ε ^ s) :=
      add_le_add (l46t_holder_power_bound K hK q Cloc ε s hq hε.1)
        (l46t_holder_power_bound K hK q Cdeg ε s hq hε.1)
    _ = ENNReal.ofReal (C * ε ^ s) := by
      have h₁ : 0 ≤ K.toReal * (max Cloc 0) ^ (1 / q) * ε ^ s :=
        mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg (le_max_right _ _) _)) (Real.rpow_nonneg hε.1.le _)
      have h₂ : 0 ≤ K.toReal * (max Cdeg 0) ^ (1 / q) * ε ^ s :=
        mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg (le_max_right _ _) _)) (Real.rpow_nonneg hε.1.le _)
      rw [← ENNReal.ofReal_add h₁ h₂]
      congr 1
      dsimp [C]
      ring

/-- Each test disk lies inside the disk where the translated γ-cone tail is controlled. -/
theorem l43p_testDisk_subset_sourceDisk {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (w : ℂ) :
    ball w ((1 - ρ) / 16) ⊆ ball (w + ((1 - ρ) / 2 : ℝ)) (3 / 4 : ℝ) := by
  intro z hz
  have hzw : dist z w < (1 - ρ) / 16 := hz
  have hone : 0 ≤ 1 - ρ := by linarith [hρ.2]
  have hw : dist w (w + ((1 - ρ) / 2 : ℝ)) = (1 - ρ) / 2 := by
    simp [dist_eq_norm]
    change ‖((1 : ℝ) : ℂ) - (ρ : ℂ)‖ = 1 - ρ
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hone]
  have htri := dist_triangle z w (w + ((1 - ρ) / 2 : ℝ))
  rw [Metric.mem_ball, hw] at *
  linarith [hρ.1]

/-- **The transferred polylogarithmic Lemma 4.6 on the whole unit disk**, from the all-visit form of
measurable Lemma 4.3 and the (4.16) comparison on finitely many observation disks. -/
theorem l43p_innerDegreeBoundPolylog_of_localComparison
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hS : Ω → LQGMetric.DistC) (uS : Ω → ℝ)
    (M₀ : GMSLemma27.CellModel γ) (hIGtarget : M₀.Ω → LQGMetric.DistC) (u₀ : M₀.Ω → ℝ)
    (hhit : ∀ᵐ ω ∂M₀.P, ∀ z : ℂ, M₀.curve ω (hitTime (M₀.curve ω) z) = z)
    (hcmp : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      Σ p q : ℝ, L46TPhaseLawComparison (l46tObservation ρ w) P M₀.P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hS)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) uS
        M₀.field hIGtarget u₀ p q)
    (hlocal : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      ∀ (ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 → ∀ N : ℕ,
      L43PLocalReconstruction (l46tObservation ρ w) (l46tLocalRegion ρ w) P M₀.P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hS)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) uS
        M₀.field hIGtarget u₀
        (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω)) M₀.curve
        (ball w ((1 - ρ) / 16)) ε N) :
    ∃ k : ℕ, InnerDegreeBoundPolylog M₀ (2 * k) := by
  obtain ⟨k, hk⟩ := innerDegreeBoundPolylog_prime_coupled D hγ
  refine ⟨k, ?_⟩
  intro ρ hρ ζ hζ s
  let W : Type := {w : ℂ // w ∈ closedBall (0 : ℂ) ρ}
  have hrpos : 0 < (1 - ρ) / 16 := by linarith [hρ.2]
  obtain ⟨F, hF⟩ := (isCompact_closedBall (0 : ℂ) ρ).elim_finite_subcover
    (fun w : W => ball (w : ℂ) ((1 - ρ) / 16)) (fun _ => isOpen_ball) (by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, by simpa [Metric.mem_ball] using hrpos⟩)
  have hcover : ball (0 : ℂ) ρ ⊆ ⋃ w ∈ F, ball (w : ℂ) ((1 - ρ) / 16) := by
    intro z hz
    exact hF (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hz)))
  have hdisk : ∀ w ∈ F, ∃ Cw : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M₀.P (l46tInnerBad M₀.curve (ball (w : ℂ) ((1 - ρ) / 16)) ε (2 * k) ζ) ≤
        ENNReal.ofReal (Cw * ε ^ s) := by
    intro w _
    obtain ⟨p, q, hcmpw⟩ := hcmp ρ hρ w w.2
    have hw := l43p_innerDegreeBound_disk D hγ hS uS k hk M₀ hIGtarget u₀ hhit
      ((w : ℂ) + ((1 - ρ) / 2 : ℝ)) w
      (show (3 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num)
      (l43p_testDisk_subset_sourceDisk hρ w)
      (show (1 - ρ) / 16 < (1 - ρ) / 8 by linarith [hρ.2])
      (l46tObservation ρ w) hcmpw
      (by intro ζ' ε hε
          simpa [l46tLocalRegion] using hlocal ρ hρ w w.2 ε hε (l43pThreshold ε (2 * k) ζ'))
    exact hw ζ hζ s
  let Cw (w : W) : ℝ := if hw : w ∈ F then Classical.choose (hdisk w hw) else 0
  have hCw : ∀ w ∈ F, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M₀.P (l46tInnerBad M₀.curve (ball (w : ℂ) ((1 - ρ) / 16)) ε (2 * k) ζ) ≤
        ENNReal.ofReal (Cw w * ε ^ s) := by
    intro w hw ε hε
    simp only [Cw, dite_eq_left hw]
    exact (Classical.choose_spec (hdisk w hw)) ε hε
  let C : ℝ := ∑ w ∈ F, max (Cw w) 0
  refine ⟨C, fun ε hε => ?_⟩
  have hsub : l46tInnerBad M₀.curve (ball (0 : ℂ) ρ) ε (2 * k) ζ ⊆
      ⋃ w ∈ F, l46tInnerBad M₀.curve (ball (w : ℂ) ((1 - ρ) / 16)) ε (2 * k) ζ := by
    rintro ω ⟨z, hz, hbad⟩
    have hzF := hcover hz
    simp only [Set.mem_iUnion] at hzF
    obtain ⟨w, hwF, hzw⟩ := hzF
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hwF, ⟨z, hzw, hbad⟩⟩⟩
  calc
    M₀.P (l46tInnerBad M₀.curve (ball (0 : ℂ) ρ) ε (2 * k) ζ) ≤
        M₀.P (⋃ w ∈ F, l46tInnerBad M₀.curve
          (ball (w : ℂ) ((1 - ρ) / 16)) ε (2 * k) ζ) := measure_mono hsub
    _ ≤ ∑ w ∈ F, M₀.P (l46tInnerBad M₀.curve
        (ball (w : ℂ) ((1 - ρ) / 16)) ε (2 * k) ζ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ w ∈ F, ENNReal.ofReal (max (Cw w) 0 * ε ^ s) := by
      apply Finset.sum_le_sum
      intro w hw
      exact (hCw w hw ε hε).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.1.le _)))
    _ = ENNReal.ofReal (C * ε ^ s) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ =>
        mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hε.1.le _))]
      congr 1
      simp only [C, Finset.sum_mul]

end MatedCRTHarmonic.GMS4cP
