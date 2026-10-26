import SupercriticalLFPPAS.Separating.Locality

/-!
# The one-annulus event with a general separating annulus

Packet P35, for §3.3 ((3.5): `d(around A_{7,8}) ≤ A d(across A_{1,2})`, `d(across A_{1,2}) ≥ m`,
`d(around A_{7,8}) ≤ M`, in canonical units, for both metrics). The library's field-local
one-annulus event `B2.Polylog.plEventLoc` of [2, Lemma 3.1] fixes the separating annulus
`A_{2r,3r}(z)`; `p35EventAB` allows `A_{αr,βr}(z)` (`plEventLoc` is `α = 2`, `β = 3`). Its
measurability, deterministic transfer, almost sure invariance under adding a constant and locality
modulo constants are adapted from `B2.Polylog.measurableSet_plEventLoc`, `plEventLoc_transfer`,
`ae_plEventLoc_addConst_iff` and `canonical_plEventLoc_local` (`B2/Polylog/P4{Event,Local}.lean`):
only the separating annulus and the carrier `A_{r/2,(β+1)r}(z)` change.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Separating

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog
open LQGMetric (DistC DistOn addConst restrictTo circleAvg)
open LQGMetric.Blueprint (AEEventIn fieldSigma)

/-- The separating annulus `A_{αr,βr}(z)`. -/
def p35AnnAB (z : ℂ) (r : Set.Ioi (0 : ℝ)) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    EuclideanAnnulus :=
  annAt z (α * r) (β * r) (mul_pos hα r.2) (mul_lt_mul_of_pos_right hαβ r.2)

/-- **The one-annulus event with separating annulus `A_{αr,βr}(z)`**: normalized lower bounds
for the local across costs of `Ā_{r,2r}(z)` and upper bounds for the around costs of `A_{αr,βr}(z)`,
for the metric `D` (scale `c`) and the localized LFPP metric with parameter `q` at cutoff `ε`. -/
def p35EventAB (ξ : ℝ) (D : DistC → LSCMetric) (c m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (q : ℝ) (z : ℂ) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (α β : ℝ)
    (hα : 0 < α) (hαβ : α < β) (C : ℝ) : Set DistC :=
  {g | ENNReal.ofReal C⁻¹ ≤ normD ξ c g z r * acrossIn (D g) z r (2 * r) ∧
    normD ξ c g z r * aroundDist (D g) (p35AnnAB z r α β hα hαβ) ≤ ENNReal.ofReal C ∧
    ENNReal.ofReal C⁻¹ ≤ normL ξ m ⟨ε, hε.1⟩ g z r *
      acrossIn (plLocMetric ξ q m ε hε g) z r (2 * r) ∧
    normL ξ m ⟨ε, hε.1⟩ g z r * aroundDist (plLocMetric ξ q m ε hε g) (p35AnnAB z r α β hα hαβ) ≤
      ENNReal.ofReal C}

theorem p35_measurableSet_eventAB (ξ : ℝ) {D : DistC → LSCMetric} (hD : Measurable D)
    (c m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ) (z : ℂ) (ε : ℝ)
    (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (C : ℝ) : MeasurableSet (p35EventAB ξ D c m q z ε hε r α β hα hαβ C) := by
  have hA := (measurable_acrossIn z r (2 * r)).comp hD
  have hR := (Uniqueness.Toolkit.CountableBase.aroundBoundedAnnulus_borel
    (p35AnnAB z r α β hα hαβ)).comp hD
  have hL := measurable_plLocMetric ξ q m ε hε
  have hAL := (measurable_acrossIn z r (2 * r)).comp hL
  have hRL := (Uniqueness.Toolkit.CountableBase.aroundBoundedAnnulus_borel
    (p35AnnAB z r α β hα hαβ)).comp hL
  have hnD := measurable_normD ξ c z r
  have hnL := measurable_normL ξ m ⟨ε, hε.1⟩ z r
  have hc1 : Measurable fun _ : DistC => ENNReal.ofReal C⁻¹ := measurable_const
  have hc2 : Measurable fun _ : DistC => ENNReal.ofReal C := measurable_const
  have h := ((measurableSet_le hc1 (hnD.mul hA)).inter
    (measurableSet_le (hnD.mul hR) hc2)).inter
    (((measurableSet_le hc1 (hnL.mul hAL)).inter
    (measurableSet_le (hnL.mul hRL) hc2)))
  convert h using 1
  ext g
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

/-- The carrier `A_{r/2,(β+1)r}(z)` of the event. -/
def p35CarrierAB (z : ℂ) (r β : ℝ) : Set ℂ := {w | r / 2 < ‖w - z‖ ∧ ‖w - z‖ < (β + 1) * r}

/-- Equality of the two localized LFPP costs from equality of the fields on an open set
containing the closed across annulus and the separating annulus. -/
theorem p35_lfpp_costs_eq_of_eqOn (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} {V : Set ℂ}
    (hV : IsOpen V) (heq : ∀ x ∈ V, φ x = φ' x) (z : ℂ) (r : Set.Ioi (0 : ℝ))
    (A : EuclideanAnnulus) (hS : closedAnn z r (2 * r) ⊆ V) (hA : A.toSet ⊆ V) :
    acrossIn (B2.Median.lfppMetric ξ a φ) z r (2 * r) = acrossIn (B2.Median.lfppMetric ξ a φ') z r (2 * r) ∧
    aroundDist (B2.Median.lfppMetric ξ a φ) A = aroundDist (B2.Median.lfppMetric ξ a φ') A := by
  have h1 : ∀ x ∈ V, |φ' x - φ x| ≤ 0 := fun x hx => by rw [heq x hx, sub_self, abs_zero]
  have h2 : ∀ x ∈ V, |φ x - φ' x| ≤ 0 := fun x hx => by rw [heq x hx, sub_self, abs_zero]
  have e : ENNReal.ofReal (Real.exp (|ξ| * 0)) = 1 := by simp
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · have := compactPathInf_lfppMetric_le ξ a hV h2 (E := sphere z r) (F := sphere z (2 * r)) hS
    rwa [e, one_mul] at this
  · have := compactPathInf_lfppMetric_le ξ a hV h1 (E := sphere z r) (F := sphere z (2 * r)) hS
    rwa [e, one_mul] at this
  · have := aroundDist_lfppMetric_le ξ a hV h2 hA
    rwa [e, one_mul] at this
  · have := aroundDist_lfppMetric_le ξ a hV h1 hA
    rwa [e, one_mul] at this

/-- **Deterministic transfer of the event**: two fields with equal restriction and equal internal
metric on an open `U ⊇ A_{r/2,(β+1)r}(z)` are in the event together (for `2 ρ_ε < r`). -/
theorem p35_eventAB_transfer {ξ : ℝ} {D : DistC → LSCMetric}
    {c m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {q : ℝ} {z : ℂ} {ε : ℝ} {hε : ε ∈ Ioo (0 : ℝ) 1}
    {r : Set.Ioi (0 : ℝ)} {α β : ℝ} {hα : 0 < α} {hαβ : α < β} {C : ℝ} (hα2 : 2 ≤ α)
    {g₁ g₂ : DistC} {U : TopologicalSpace.Opens ℂ}
    (hI : (D g₁).internal U = (D g₂).internal U) (hres : restrictTo U g₁ = restrictTo U g₂)
    (hU : p35CarrierAB z r β ⊆ U) (hρ : 2 * plRad q ε < r) :
    g₁ ∈ p35EventAB ξ D c m q z ε hε r α β hα hαβ C ↔
      g₂ ∈ p35EventAB ξ D c m q z ε hε r α β hα hαβ C := by
  have hr : (0 : ℝ) < r := r.2
  have hρ0 : 0 < plRad q ε := plRad_pos q hε
  set ρ := plRad q ε
  have hβ : 2 < β := lt_of_le_of_lt hα2 hαβ
  have hS : closedAnn z r (2 * r) ⊆ U := fun w hw => hU ⟨by linarith [hw.1], by nlinarith [hw.2]⟩
  have hA : (p35AnnAB z r α β hα hαβ).toSet ⊆ U := fun w hw => by
    rw [p35AnnAB, annAt_toSet] at hw
    exact hU ⟨by nlinarith [hw.1], by nlinarith [hw.2]⟩
  have hsph : sphere z r ⊆ U := fun w hw => by
    rw [mem_sphere, dist_eq_norm] at hw
    exact hU ⟨by linarith, by nlinarith⟩
  have hacc := acrossIn_eq_of_internal_eq hS hI (z := z) (r₁ := r) (r₂ := 2 * r)
  have hround := Uniqueness.BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq
    (D g₁) (D g₂) U hI (p35AnnAB z r α β hα hαβ) hA
  have hca := Uniqueness.Objects.AnnulusTails.circleAvg_congr_restrict hres hr z hsph
  -- the localized field agrees near the annuli
  set η := (r / 2 - ρ) / 2
  have hηv : η = (r / 2 - ρ) / 2 := rfl
  have hη : 0 < η := by rw [hηv]; linarith
  set V : Set ℂ := {w | (r : ℝ) - η < ‖w - z‖ ∧ ‖w - z‖ < β * r + η}
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  have hball : ∀ x ∈ V, closedBall x ρ ⊆ U := fun x hx y hy => by
    rw [mem_closedBall, dist_eq_norm] at hy
    have t1 : ‖y - z‖ ≤ ‖y - x‖ + ‖x - z‖ := by
      calc ‖y - z‖ = ‖(y - x) + (x - z)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have t2 : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
      calc ‖x - z‖ = ‖(x - y) + (y - z)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have t3 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev x y
    have hx1 : (r : ℝ) - η < ‖x - z‖ := hx.1
    have hx2 : ‖x - z‖ < β * r + η := hx.2
    exact hU ⟨by linarith, by nlinarith⟩
  have heq : ∀ x ∈ V, plMollifyC q ε hε g₁ x = plMollifyC q ε hε g₂ x := fun x hx =>
    plMollify_congr q ε hε U hres (hball x hx)
  have hSV : closedAnn z r (2 * r) ⊆ V := fun w hw => ⟨by linarith [hw.1], by nlinarith [hw.2]⟩
  have hAV : (p35AnnAB z r α β hα hαβ).toSet ⊆ V := fun w hw => by
    rw [p35AnnAB, annAt_toSet] at hw
    exact ⟨by nlinarith [hw.1], by linarith [hw.2]⟩
  obtain ⟨hLa, hLr⟩ := p35_lfpp_costs_eq_of_eqOn ξ (m ⟨ε, hε.1⟩) hVo heq z r _ hSV hAV
  simp only [p35EventAB, mem_ofPred_eq, normD, normL, plLocMetric]
  rw [hacc, hround, hca, hLa, hLr]

/-- **Almost sure invariance under adding a random constant** (Axiom III; `plMollify_addConst`). -/
theorem p35_ae_eventAB_addConst_iff {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    (hw : LQGMetric.IsWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : B2.Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ) (z : ℂ)
    (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (α β : ℝ) (hα : 0 < α)
    (hαβ : α < β) (C : ℝ) (k : Ω → ℝ) :
    ∀ᵐ ω ∂P, (addConst (h ω) (k ω) ∈ p35EventAB ξ D c m q z ε hε r α β hα hαβ C ↔
      h ω ∈ p35EventAB ξ D c m q z ε hε r α β hα hαβ C) := by
  filter_upwards [ae_addConst_eq_mul_of_pfe P h hh hD k,
    LQGMetric.CircleAvg.ae_circleAvg_addConst hw z r.2] with ω hsc hca
  set s : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * k ω))
  have hs0 : s ≠ 0 := by simpa [s] using Real.exp_pos _
  have hst : s ≠ ∞ := ENNReal.ofReal_ne_top
  have hD' : ∀ x y, D (addConst (h ω) (k ω)) (x, y) = s * D (h ω) (x, y) := fun x y => hsc (x, y)
  have hL' : ∀ x y, plLocMetric (ξ : ℝ) q m ε hε (addConst (h ω) (k ω)) (x, y) =
      s * plLocMetric (ξ : ℝ) q m ε hε (h ω) (x, y) := fun x y => by
    unfold plLocMetric
    rw [lfppMetric_affine (ξ : ℝ) (m ⟨ε, hε.1⟩) (m ⟨ε, hε.1⟩) (φ := plMollifyC q ε hε (h ω))
      (φ' := plMollifyC q ε hε (addConst (h ω) (k ω))) (b := 0) (c := 1) one_ne_zero (k ω)
      (fun u => by
        show plMollify q ε hε (addConst (h ω) (k ω)) u = plMollify q ε hε (h ω) (0 + 1 * u) + k ω
        rw [plMollify_addConst, zero_add, one_mul])]
    have hm := (m ⟨ε, hε.1⟩).2
    simp only [mem_Ioi] at hm
    rw [norm_one, mul_one, mul_div_cancel_left₀ _ hm.ne', zero_add, zero_add, one_mul, one_mul]
  have hnD : normD ξ c (addConst (h ω) (k ω)) z r =
      normD ξ c (h ω) z r * ENNReal.ofReal (Real.exp ((ξ : ℝ) * -k ω)) := by
    unfold normD
    rw [hca, ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (c r).2.le) (Real.exp_pos _).le),
      mul_assoc, ← Real.exp_add]
    congr 3; ring
  have hnL : normL ξ m ⟨ε, hε.1⟩ (addConst (h ω) (k ω)) z r =
      normL ξ m ⟨ε, hε.1⟩ (h ω) z r * ENNReal.ofReal (Real.exp ((ξ : ℝ) * -k ω)) := by
    unfold normL
    rw [hca, ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (lfppScaleFactor_pos m _ r).le)
      (Real.exp_pos _).le), mul_assoc, ← Real.exp_add]
    congr 3; ring
  have hcancel : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -k ω)) * s = 1 := by
    rw [mul_comm]; exact exp_mul_cancel (ξ : ℝ) (k ω)
  have key : ∀ (n n' X : ℝ≥0∞), n' = n * ENNReal.ofReal (Real.exp ((ξ : ℝ) * -k ω)) →
      n' * (s * X) = n * X := fun n n' X hn => by
    rw [hn, mul_assoc, ← mul_assoc _ s, hcancel, one_mul]
  simp only [p35EventAB, mem_ofPred_eq]
  rw [acrossIn_eq_mul_of_dist_scale _ _ s hs0 hst hD',
    Uniqueness.Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale _ _ s hs0 hst hD',
    acrossIn_eq_mul_of_dist_scale _ _ s hs0 hst hL',
    Uniqueness.Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale _ _ s hs0 hst hL',
    key _ _ _ hnD, key _ _ _ hnD, key _ _ _ hnL, key _ _ _ hnL]

/-- **Canonical local representative** under the Gaussian-shifted law. -/
theorem p35_canonical_eventAB_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : B2.Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ) (z : ℂ)
    (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (α β : ℝ) (hα : 0 < α)
    (hαβ : α < β) (hα2 : 2 ≤ α) (C : ℝ) (U : TopologicalSpace.Opens ℂ)
    (hU : p35CarrierAB z r β ⊆ U) (hρ : 2 * plRad q ε < r) :
    ∃ S : Set (DistOn U), MeasurableSet S ∧
      p35EventAB (ξ : ℝ) D c m q z ε hε r α β hα hαβ C =ᵐ[Uniqueness.TwoScale.S36.muH P h]
        restrictTo U ⁻¹' S := by
  have hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) (Uniqueness.TwoScale.S36.muH P h) :=
    Uniqueness.BiLipschitz.OneScale.canonical_gaussianShift_isGFFPlusCont P h hh.1
  have hprob := Uniqueness.TwoScale.S36.muH_isProb P h hh.1
  set E := p35EventAB (ξ : ℝ) D c m q z ε hε r α β hα hαβ C with hEdef
  obtain ⟨FD, -, hlocD⟩ := hD.2.2.1 (Uniqueness.TwoScale.S36.muH P h) id hμ U
  obtain ⟨W, hWae, hWm, hWsub⟩ := hlocD.exists_measurable_mem
  let R : DistC → LQGMetric.CoordJ → ℝ := fun g => LQGMetric.pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[LQGMetric.Blueprint.fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ E → g₂ ∈ E := by
    intro g₁ hg₁ g₂ hg₂ he hE₁
    have hres : restrictTo U g₁ = restrictTo U g₂ := LQGMetric.injective_pairJ U he
    have hI : (D g₁).internal U = (D g₂).internal U := by
      have h1 : (D (id g₁)).internal U = FD (restrictTo U (id g₁)) := hWsub g₁ hg₁
      have h2 : (D (id g₂)).internal U = FD (restrictTo U (id g₂)) := hWsub g₂ hg₂
      simp only [id] at h1 h2
      rw [h1, h2, hres]
    exact (p35_eventAB_transfer hα2 hI hres hU hρ).mp hE₁
  have hB : NullMeasurableSet E ((Uniqueness.TwoScale.S36.muH P h).map id) :=
    (p35_measurableSet_eventAB (ξ : ℝ) hD.1 c m q z ε hε r α β hα hαβ C).nullMeasurableSet
  have hLocal := LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := E) (W := W)
    measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl) hWm hB hWae hsat
  obtain ⟨F, hFm, hFe⟩ := hLocal
  obtain ⟨S, hS, hF⟩ := MeasurableSpace.measurableSet_comap.mp hFm
  refine ⟨S, hS, ?_⟩
  rw [← hF] at hFe
  exact hFe

/-- **Locality of the event modulo constants, arbitrary recentring.** -/
theorem p35_eventAB_aeEventIn {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : B2.Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ) (z : ℂ)
    (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (α β : ℝ) (hα : 0 < α)
    (hαβ : α < β) (hα2 : 2 ≤ α) (C : ℝ) (U : TopologicalSpace.Opens ℂ)
    (hU : p35CarrierAB z r β ⊆ U) (hρ : 2 * plRad q ε < r) (X : Ω → ℝ) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-X ω)) U)
      {ω | h ω ∈ p35EventAB (ξ : ℝ) D c m q z ε hε r α β hα hαβ C} := by
  refine p35_aeEventIn_of_canonical P h hh _ U
    (p35_canonical_eventAB_local P h hh hD m q z ε hε r α β hα hαβ hα2 C U hU hρ) ?_ X
  have hprodW : LQGMetric.IsWholePlaneGFF (fun y : Ω × ℝ => h y.1)
      (P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian) :=
    Uniqueness.BiLipschitz.OneScale.gff_prod_fst P
      Uniqueness.BiLipschitz.OneScale.standardGaussian h hh.1
  have hprod : LQGMetric.IsGFFPlusCont (fun y : Ω × ℝ => h y.1)
      (P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian) :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hprodW
  exact p35_ae_eventAB_addConst_iff (P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian)
    (fun y => h y.1) hprod hprodW hD m q z ε hε r α β hα hαβ C (fun y => y.2)

end SupercriticalLFPPAS.Separating
