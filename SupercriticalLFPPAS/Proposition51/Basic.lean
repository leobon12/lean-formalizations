import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MetricLemmas

/-!
# Proposition 5.1: comparison events, monotonicity, the initial comparison (packet P51)

Deterministic and measure-theoretic tools for the proof of Proposition 5.1 (paper §5, l. 505–581; SB2 §2.6 and
Details D8–D9):

* the two directions of the comparison `Core.CompIn` as one family `compDir S b` (`b = true`: source `D`, target `X̂_ε`;
  `b = false`: source `X̂_ε`, target `D`), with the matching scale ratio `kapDir S b` (`κ_ε` resp. `κ_ε⁻¹`);
* monotonicity of `Core.CompIn` in the constant and in the endpoint radius, and of internal set distances in the domain
  and in the sets;
* the initial comparison (D9 step 2): `compareHolds` at radius `ρ ≤ 1` on `U = B_{R+1}(0)` gives `Core.CompIn` with
  target domain `B_{R+2}(0)` in both directions (a subsegment of a unit-speed geodesic in `B_R(0)` is a curve in `U` whose
  length is the parameter length);
* `DirStep`: the contraction step of `Core.ContractionStmt` in the direction-uniform form (`dirStep_of`);
* the uniform choice of rate constants over a finite index set (`uniform_rate`), and the telescoping bound
  `P(A₀ \ Aₙ) ≤ ∑ P(Aᵢ \ Aᵢ₊₁)` for outer measures (`measure_sdiff_le_sum`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Proposition51

open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric IsNormalizedWholePlaneGFF)
open SupercriticalLQGUniqueness.B2.Polylog (compareHolds)

/-! ### The two directions -/

/-- Source metric of direction `b`: `D_h` for `b = true`, `X̂_ε` for `b = false`. -/
def srcM (S : Core.Setup) (b : Bool) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (g : DistC) : LSCMetric :=
  bif b then S.D g else Core.locMetric S ε hε g

/-- Target metric of direction `b`: `X̂_ε` for `b = true`, `D_h` for `b = false`. -/
def tgtM (S : Core.Setup) (b : Bool) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (g : DistC) : LSCMetric :=
  bif b then Core.locMetric S ε hε g else S.D g

/-- The comparison `(C, ρ)` of direction `b` for geodesics in `B_R(0)`, target costs internal to `B_{R+2}(0)`. -/
def compDir (S : Core.Setup) (b : Bool) (R ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (g : DistC) (C ρ : ℝ) : Prop :=
  Core.CompIn (srcM S b ε hε g) (tgtM S b ε hε g) (ball 0 (R + 2)) R C ρ

/-- The scale ratio of direction `b` at the radius `4096^j`: `κ_ε` for `b = true`, `κ_ε⁻¹` for `b = false`. -/
def kapDir (S : Core.Setup) (b : Bool) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (j : ℤ) : ℝ :=
  bif b then Core.kappaS S ⟨ε, hε.1⟩ (Core.bandRad j) else (Core.kappaS S ⟨ε, hε.1⟩ (Core.bandRad j))⁻¹

theorem kappaS_pos (S : Core.Setup) (ε r : Set.Ioi (0 : ℝ)) : 0 < Core.kappaS S ε r := by
  have hr : (0 : ℝ) < r := r.2
  have hm₁ : (0 : ℝ) < (S.m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.2 r.2)⟩ : ℝ) := (S.m _).2
  have hm₂ : (0 : ℝ) < (S.m ε : ℝ) := (S.m ε).2
  exact div_pos (mul_pos hr hm₁) (mul_pos (Real.rpow_pos_of_pos hr _) hm₂)

/-! ### Monotonicity of internal set distances and of `CompIn` -/

theorem p51_internal_mono (d : LSCMetric) {V V' : Set ℂ} (hV : V ⊆ V') (x y : V) :
    d.internal V' (⟨x, hV x.2⟩, ⟨y, hV y.2⟩) ≤ d.internal V (x, y) := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hPV => le_iInf fun ha => le_iInf fun hb => ?_
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hP <|
    iInf_le_of_le (fun t ht => hV (hPV t ht)) <| iInf_le_of_le ha <| iInf_le_of_le hb le_rfl

/-- Internal set distances decrease when the domain grows. -/
theorem p51_internalSetDist_mono_domain (d : LSCMetric) {V V' : Set ℂ} (hV : V ⊆ V') (X Y : Set ℂ) :
    d.internalSetDist V' {x | (x : ℂ) ∈ X} {x | (x : ℂ) ∈ Y} ≤
      d.internalSetDist V {x | (x : ℂ) ∈ X} {x | (x : ℂ) ∈ Y} := by
  unfold LSCMetric.internalSetDist
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  exact iInf₂_le_of_le ⟨x, hV x.2⟩ hx (iInf₂_le_of_le ⟨y, hV y.2⟩ hy (p51_internal_mono d hV x y))

/-- Internal set distances decrease when the sets grow. -/
theorem p51_internalSetDist_mono_sets (d : LSCMetric) (V : Set ℂ) {A A' B B' : Set V} (hA : A ⊆ A')
    (hB : B ⊆ B') : d.internalSetDist V A' B' ≤ d.internalSetDist V A B := by
  unfold LSCMetric.internalSetDist
  exact iInf₂_mono' fun x hx => ⟨x, hA hx, iInf₂_mono' fun y hy => ⟨y, hB hy, le_rfl⟩⟩

/-- `CompIn` is monotone in the constant and in the endpoint radius. -/
theorem compIn_mono {d d' : LSCMetric} {W : Set ℂ} {R C C' ρ ρ' : ℝ} (hC : C ≤ C') (hρ : ρ ≤ ρ')
    (h : Core.CompIn d d' W R C ρ) : Core.CompIn d d' W R C' ρ' := by
  intro P T hP s t hs hst ht
  calc d'.internalSetDist W {y | (y : ℂ) ∈ ball (P s) ρ'} {y | (y : ℂ) ∈ ball (P t) ρ'}
      ≤ d'.internalSetDist W {y | (y : ℂ) ∈ ball (P s) ρ} {y | (y : ℂ) ∈ ball (P t) ρ} :=
        p51_internalSetDist_mono_sets d' W (fun x hx => ball_subset_ball hρ hx)
          (fun x hx => ball_subset_ball hρ hx)
    _ ≤ ENNReal.ofReal (C * (t - s)) := h P T hP s t hs hst ht
    _ ≤ ENNReal.ofReal (C' * (t - s)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (sub_nonneg.2 hst))

theorem compDir_mono {S : Core.Setup} {b : Bool} {R ε : ℝ} {hε : ε ∈ Ioo (0 : ℝ) 1} {g : DistC}
    {C C' ρ ρ' : ℝ} (hC : C ≤ C') (hρ : ρ ≤ ρ') (h : compDir S b R ε hε g C ρ) :
    compDir S b R ε hε g C' ρ' :=
  compIn_mono hC hρ h

/-! ### The initial comparison (D9 step 2) -/

/-- On a unit-speed geodesic, the length of a subsegment is its parameter length. -/
theorem p51_len_eq {d : LSCMetric} {P : ℝ → ℂ} {L s t : ℝ}
    (hu : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 L)) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) :
    d.len P s t = ENNReal.ofReal (t - s) := by
  have h := hu ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩
  rw [inter_eq_right.mpr (Icc_subset_Icc hs ht)] at h
  unfold LSCMetric.len
  simpa only [NNReal.coe_one, one_mul] using h

/-- A one-sided `compareHolds` bound on `U = B_{R+1}(0)` at radius `ρ ≤ 1` gives `CompIn` with target domain
`B_{R+2}(0)`: for a subsegment `P|[s,t]` of a unit-speed `d`-geodesic in `B_R(0)`, `d(P s, P t; U) ≤ t − s`, and the
internal set distance in `B_ρ(U) ⊆ B_{R+2}(0)` dominates the one in `B_{R+2}(0)`. -/
theorem compIn_of_internal {d d' : LSCMetric} {R C₀ ρ : ℝ} (hR : 0 ≤ R) (hC₀ : 0 ≤ C₀) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (H : ∀ (z w : ℂ) (hz : z ∈ ball (0 : ℂ) (R + 1)) (hw : w ∈ ball (0 : ℂ) (R + 1)),
      d'.internalSetDist (thickening ρ (ball (0 : ℂ) (R + 1))) {x | (x : ℂ) ∈ ball z ρ}
          {x | (x : ℂ) ∈ ball w ρ} ≤
        ENNReal.ofReal C₀ * d.internal (ball (0 : ℂ) (R + 1)) (⟨z, hz⟩, ⟨w, hw⟩)) :
    Core.CompIn d d' (ball 0 (R + 2)) R C₀ ρ := by
  intro P T hP s t hs hst htT
  have hsub : ball (0 : ℂ) R ⊆ ball (0 : ℂ) (R + 1) := ball_subset_ball (by linarith)
  have hPU : ∀ u ∈ Icc s t, P u ∈ ball (0 : ℂ) (R + 1) := fun u hu =>
    hsub (hP.2.2.2 u ⟨hs.trans hu.1, hu.2.trans htT⟩)
  have hthick : thickening ρ (ball (0 : ℂ) (R + 1)) ⊆ ball (0 : ℂ) (R + 2) := by
    rw [thickening_ball hρ (by linarith) (0 : ℂ)]
    exact ball_subset_ball (by linarith)
  have hcurve : d.IsCurve P s t := ⟨hst, hP.1.2.1.mono (Icc_subset_Icc hs htT)⟩
  have hint : d.internal (ball (0 : ℂ) (R + 1))
      (⟨P s, hPU s ⟨le_rfl, hst⟩⟩, ⟨P t, hPU t ⟨hst, le_rfl⟩⟩) ≤ ENNReal.ofReal (t - s) := by
    have h1 := LSCMetric.internal_le_len d (ball (0 : ℂ) (R + 1)) P s t hcurve hPU
    rwa [p51_len_eq hP.2.1 hs hst htT] at h1
  calc d'.internalSetDist (ball 0 (R + 2)) {y | (y : ℂ) ∈ ball (P s) ρ} {y | (y : ℂ) ∈ ball (P t) ρ}
      ≤ d'.internalSetDist (thickening ρ (ball (0 : ℂ) (R + 1))) {y | (y : ℂ) ∈ ball (P s) ρ}
          {y | (y : ℂ) ∈ ball (P t) ρ} := p51_internalSetDist_mono_domain d' hthick _ _
    _ ≤ ENNReal.ofReal C₀ * d.internal (ball (0 : ℂ) (R + 1))
          (⟨P s, hPU s ⟨le_rfl, hst⟩⟩, ⟨P t, hPU t ⟨hst, le_rfl⟩⟩) := H _ _ _ _
    _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (t - s) := mul_le_mul_right hint _
    _ = ENNReal.ofReal (C₀ * (t - s)) := (ENNReal.ofReal_mul hC₀).symm

/-- `compareHolds` on `B_{R+1}(0)` at radius `ρ ≤ 1` gives both directions of the comparison with target domain
`B_{R+2}(0)`. -/
theorem compDir_of_compareHolds {S : Core.Setup} {R ε : ℝ} {hε : ε ∈ Ioo (0 : ℝ) 1} {g : DistC}
    {C₀ ρ : ℝ} (hR : 0 ≤ R) (hC₀ : 0 ≤ C₀) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h : compareHolds (Core.locMetric S ε hε g) (S.D g) ρ (ball (0 : ℂ) (R + 1)) C₀) (b : Bool) :
    compDir S b R ε hε g C₀ ρ := by
  cases b
  · exact compIn_of_internal hR hC₀ hρ hρ1 fun z w hz hw => (h z w hz hw).2
  · exact compIn_of_internal hR hC₀ hρ hρ1 fun z w hz hw => (h z w hz hw).1

/-- The initial comparison event of D9 step 2 holds with polynomially small failure probability, with the constant `C₀`
of (2.7)–(2.8) at `ζ = 1/2` chosen before `R`, at the radius `513 ε^{1/4} = 513 ε^{s₀}` (`s₀ = bandLower 0`). -/
def InitProp (S : Core.Setup) (Cinit : ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → ∃ p₀ c₀ ε₀ : ℝ, 0 < p₀ ∧ 0 < c₀ ∧ 0 < ε₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P → ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
        P {ω | ¬ (compDir S true R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
          compDir S false R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0))} ≤
          ENNReal.ofReal (c₀ * ε ^ p₀)

theorem bandLower_zero : Iteration.bandLower 0 = 1 / 4 := by
  norm_num [Iteration.bandLower, Iteration.bandUpper]

theorem init_of (S : Core.Setup) (hL : Core.LocCompareStmt S) : ∃ Cinit : ℝ, 0 < Cinit ∧ InitProp S Cinit := by
  obtain ⟨C₀, hC₀, hU⟩ := hL (1 / 2) (by norm_num) (by norm_num)
  refine ⟨C₀, hC₀, fun R hR => ?_⟩
  obtain ⟨p₀, c₀, ε₀, hp₀, hc₀, hε₀, -, H⟩ := hU (ball (0 : ℂ) (R + 1)) isOpen_ball
    (isConnected_ball (by linarith)) isBounded_ball
  refine ⟨p₀, c₀, ε₀, hp₀, hc₀, hε₀, fun P _ h hh ε hε hεε₀ => ?_⟩
  refine le_trans (measure_mono ?_) (H P h hh ε hε hεε₀)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hcomp
  apply hω
  have hρ : 0 < ε ^ (1 - (1 / 2 : ℝ)) := Real.rpow_pos_of_pos hε.1 _
  have hρ1 : ε ^ (1 - (1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one hε.1.le hε.2.le (by norm_num)
  have hρρ : ε ^ (1 - (1 / 2 : ℝ)) ≤ 513 * ε ^ Iteration.bandLower 0 := by
    rw [bandLower_zero]
    have h1 : ε ^ (1 - (1 / 2 : ℝ)) ≤ ε ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (by norm_num)
    have h2 : 0 ≤ ε ^ (1 / 4 : ℝ) := (Real.rpow_pos_of_pos hε.1 _).le
    linarith
  exact ⟨compDir_mono le_rfl hρρ (compDir_of_compareHolds (by linarith) hC₀.le hρ hρ1 hcomp true),
    compDir_mono le_rfl hρρ (compDir_of_compareHolds (by linarith) hC₀.le hρ hρ1 hcomp false)⟩

/-! ### The contraction step in direction-uniform form -/

/-- The contraction step of `Core.ContractionStmt` (with its `λ`), for both directions at once. -/
def DirStep (S : Core.Setup) (lam : ℝ) : Prop :=
  ∀ d₀ : ℝ, 0 < d₀ → ∀ R : ℝ, 1 ≤ R → ∀ s t told C : ℝ,
    0 < s → 4 * s ≤ t → t < told → told < 1 → 0 ≤ C →
    ∃ β c₁ ε₁ : ℝ, 0 < β ∧ 0 < c₁ ∧ 0 < ε₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₁ →
        ∀ Sε : Finset ℤ, Sε ⊆ Iteration.radiusExponents ε s t →
          (Iteration.radiusExponents ε s t).card ≤ 3 * Sε.card → ∀ K : ℝ, 0 ≤ K → ∀ b : Bool,
          (∀ j ∈ Sε, kapDir S b ε hε j ≤ K) →
            P {ω | compDir S b R ε hε (h ω) C (513 * ε ^ told) ∧
              ¬ compDir S b R ε hε (h ω) (Iteration.contractionFactor C K lam d₀) (513 * ε ^ s)} ≤
              ENNReal.ofReal (c₁ * ε ^ β)

theorem dirStep_of (S : Core.Setup) (hC : Core.ContractionStmt S) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ DirStep S lam := by
  obtain ⟨lam, hlam, hlam1, hstep⟩ := hC
  refine ⟨lam, hlam, hlam1, ?_⟩
  intro d₀ hd₀ R hR s t told C hs hst htt htold hC0
  obtain ⟨β, c₁, ε₁, hβ, hc₁, hε₁, H⟩ := hstep d₀ hd₀ R hR s t told C hs hst htt htold hC0
  refine ⟨β, c₁, ε₁, hβ, hc₁, hε₁, ?_⟩
  intro Ω _ P _ h hh ε hε hεε₁ Sε hSε hcard K hK b hκ
  cases b
  · exact (H P h hh ε hε hεε₁ Sε hSε hcard K hK).2 hκ
  · exact (H P h hh ε hε hεε₁ Sε hSε hcard K hK).1 hκ

/-! ### Uniform rate constants and telescoping -/

/-- Rate bounds `c ε^β` valid for `ε < e`, one for each index of a finite set, can be chosen uniformly (minimum
exponent, maximum constant, minimum threshold), for any upward-closed family of bounds. -/
theorem uniform_rate {ι : Type*} (s : Finset ι) (Φ : ι → ℝ → ℝ≥0∞ → Prop)
    (hΦ : ∀ i ε x y, x ≤ y → Φ i ε x → Φ i ε y)
    (h : ∀ i ∈ s, ∃ β c e : ℝ, 0 < β ∧ 0 < c ∧ 0 < e ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ε < e → Φ i ε (ENNReal.ofReal (c * ε ^ β))) :
    ∃ β c e : ℝ, 0 < β ∧ 0 < c ∧ 0 < e ∧
      ∀ i ∈ s, ∀ ε : ℝ, 0 < ε → ε < 1 → ε < e → Φ i ε (ENNReal.ofReal (c * ε ^ β)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, 1, 1, one_pos, one_pos, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
      obtain ⟨β₁, c₁, e₁, hβ₁, hc₁, he₁, H₁⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨β₂, c₂, e₂, hβ₂, hc₂, he₂, H₂⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine ⟨min β₁ β₂, max c₁ c₂, min e₁ e₂, lt_min hβ₁ hβ₂, lt_max_of_lt_left hc₁,
        lt_min he₁ he₂, ?_⟩
      intro i hi ε hε hε1 hεe
      have key : ∀ β c : ℝ, 0 < c → min β₁ β₂ ≤ β → c ≤ max c₁ c₂ →
          ENNReal.ofReal (c * ε ^ β) ≤ ENNReal.ofReal (max c₁ c₂ * ε ^ min β₁ β₂) := by
        intro β c hc hβ hcm
        apply ENNReal.ofReal_le_ofReal
        have h1 : ε ^ β ≤ ε ^ min β₁ β₂ := Real.rpow_le_rpow_of_exponent_ge hε hε1.le hβ
        have h2 : 0 ≤ ε ^ β := (Real.rpow_pos_of_pos hε β).le
        calc c * ε ^ β ≤ max c₁ c₂ * ε ^ β := mul_le_mul_of_nonneg_right hcm h2
          _ ≤ max c₁ c₂ * ε ^ min β₁ β₂ := mul_le_mul_of_nonneg_left h1 (hc.le.trans hcm)
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hΦ _ _ _ _ (key β₁ c₁ hc₁ (min_le_left _ _) (le_max_left _ _))
          (H₁ ε hε hε1 (lt_of_lt_of_le hεe (min_le_left _ _)))
      · exact hΦ _ _ _ _ (key β₂ c₂ hc₂ (min_le_right _ _) (le_max_right _ _))
          (H₂ i hi ε hε hε1 (lt_of_lt_of_le hεe (min_le_right _ _)))

/-- `A₀ \ Aₙ ⊆ ⋃_{i<n} (Aᵢ \ Aᵢ₊₁)`. -/
theorem sdiff_subset_biUnion {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) :
    A 0 \ A n ⊆ ⋃ i ∈ Finset.range n, (A i \ A (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      intro x hx
      by_cases hn : x ∈ A n
      · exact mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_self n)) ⟨hn, hx.2⟩
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ih ⟨hx.1, hn⟩)
        exact mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))) hxi

/-- Telescoping for outer measures: `P(A₀ \ Aₙ) ≤ ∑_{i<n} P(Aᵢ \ Aᵢ₊₁)`. -/
theorem measure_sdiff_le_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : ℕ → Set Ω) (n : ℕ) :
    P (A 0 \ A n) ≤ ∑ i ∈ Finset.range n, P (A i \ A (i + 1)) :=
  (measure_mono (sdiff_subset_biUnion A n)).trans (measure_biUnion_finset_le _ _)

end SupercriticalLFPPAS.Proposition51
