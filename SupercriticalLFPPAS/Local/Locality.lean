import SupercriticalLFPPAS.Local.Measurability
import SupercriticalLFPPAS.Local.Transfer
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.ClosedEventToolkit
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import LQGMetric.Field.CircleAvgGauss
import LQGMetric.Papers.CONF.S3D114S4

/-!
# Locality of the localized event of Lemma 3.2 (packet P32)

Paper `source/almost-sure-supercritical-lfpp.txt`, Lemma 3.2, l. 254–256 and 275–278: "If `δL → 0`
[corrected: `δL < 1/16`, SB1 item 27], the latter event is measurable from the field in
`A_{1/16,32}(0)` modulo its additive constant, when all lengths and additive errors are expressed
in units `e^{ξ h_1(0)}`". Planning audit `planning/audits/SB1-sections-1-3.md` A12 step 9 and A13.

For a whole-plane GFF `h` normalized by `h_1(0) = 0` and `1 < log δ⁻¹ ≤ L` with `δL < 1/16`:

* `aeEventIn_lemma32EventU_loc`: the unit-adjusted event
  `Lemma32EventU (D_h) (Y_{δ,L}[h]) η ν M (e^{ξ h_1(0)})` is almost surely equal to an event of
  `fieldSigma0On h A_{1/16,32}(0)`, the σ-algebra of the field restricted to the open annulus
  modulo additive constants;
* `aeEventIn_lemma32Event_loc`: the same for the plain event (`h_1(0) = 0` a.s.);
* `aeEventIn_lemma32Event_loc_closed`: the same in `fieldSigmaClosed0` of the closed annulus
  `{1/16 ≤ |z| ≤ 32}`, the σ-algebra of the annulus concentration theorem (1.6)
  (`Concentration.paper_annulus_concentration`).

Proof: the event depends on the field only through the internal metric of `D` on `U`
(`internal_eq_of_internal_eq`), the localized field on a neighbourhood of `U` whose `δL`-balls lie
in the window (`plMollify_congr`), and `h_1(0)` (bump averages supported near `∂B_1`); it is
universally measurable (`umeasurableSet_lemma32EventU`); a saturation argument on the canonical
field space (`aeEventIn_internal_subset_local`, a variant of the host's `aeEventIn_internal_subset`
that also allows a deterministic dependence on the field in the window) gives locality; finally it is
invariant under additive constants (Weyl scaling by a random constant), which gives the
mean-zero σ-algebra (`aeEventIn_fieldSigma0On_of_normIn`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric (DistC DistOn restrictTo pairJ addConst circleAvg)
open LQGMetric.Blueprint
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Local

/-- The field window `A_{1/16,32}(0)` of Lemma 3.2's locality clause. -/
abbrev window : TopologicalSpace.Opens ℂ := LQGMetric.Blueprint.annulus 0 (1 / 16) 32

theorem mem_window {z : ℂ} : z ∈ (window : Set ℂ) ↔ 1 / 16 < ‖z‖ ∧ ‖z‖ < 32 := by
  change 1 / 16 < ‖z - 0‖ ∧ ‖z - 0‖ < 32 ↔ _
  rw [sub_zero]

theorem tgtU_subset_window : tgtU ⊆ (window : Set ℂ) := fun z hz =>
  mem_window.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-! ### A saturation variant of the host's `aeEventIn_internal_subset` -/

/-- A null-measurable event of finitely many whole internal metrics on `K ⊆ U` and of the field,
which depends on the field only through its restriction to `U`, has a raw open local
representative. Same proof as the host's `aeEventIn_internal_subset`. -/
theorem aeEventIn_internal_subset_local
    {ι : Type} [Fintype ι] (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (K : Set ℂ) (U : TopologicalSpace.Opens ℂ) (hKU : K ⊆ (U : Set ℂ))
    (Φ : (ι → (K × K → ℝ≥0∞)) → DistC → Prop)
    (hΦ : ∀ ρ g₁ g₂, restrictTo U g₁ = restrictTo U g₂ → Φ ρ g₁ → Φ ρ g₂)
    (hB : NullMeasurableSet {g : DistC | Φ (fun i => (D i g).internal K) g} μ) :
    AEEventIn μ (fieldSigma id U) {g : DistC | Φ (fun i => (D i g).internal K) g} := by
  classical
  let B : Set DistC := {g | Φ (fun i => (D i g).internal K) g}
  have hLoc : ∀ i : ι, ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞),
      ∀ᵐ g ∂μ, (D i g).internal (U : Set ℂ) = F (restrictTo U g) := by
    intro i
    obtain ⟨F, _, hF⟩ := (hD i).locality μ id hμ U
    exact ⟨F, hF⟩
  choose F hF using hLoc
  let Wraw : Set DistC := {g | ∀ i, (D i g).internal (U : Set ℂ) = F i (restrictTo U g)}
  have hWraw : ∀ᵐ g ∂μ, g ∈ Wraw := by
    change ∀ᵐ g ∂μ, ∀ i, (D i g).internal (U : Set ℂ) = F i (restrictTo U g)
    exact ae_all_iff.mpr hF
  obtain ⟨W, hWae, hWm, hWsub⟩ := hWraw.exists_measurable_mem
  let R : DistC → LQGMetric.CoordJ → ℝ := fun g => pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hSat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    intro g₁ hg₁ g₂ hg₂ he hB₁
    have hRes : restrictTo U g₁ = restrictTo U g₂ := LQGMetric.injective_pairJ U he
    have hIntU : ∀ i, (D i g₁).internal (U : Set ℂ) = (D i g₂).internal (U : Set ℂ) := by
      intro i
      calc _ = F i (restrictTo U g₁) := hWsub g₁ hg₁ i
        _ = F i (restrictTo U g₂) := by rw [hRes]
        _ = _ := (hWsub g₂ hg₂ i).symm
    have hIntK : ∀ i, (D i g₁).internal K = (D i g₂).internal K := fun i =>
      Uniqueness.Toolkit.InternalMetrics.internal_eq_of_internal_eq (D i g₁) (D i g₂) hKU
        (hIntU i)
    change Φ (fun i => (D i g₁).internal K) g₁ at hB₁
    change Φ (fun i => (D i g₂).internal K) g₂
    rw [show (fun i => (D i g₂).internal K) = (fun i => (D i g₁).internal K) from
      funext fun i => (hIntK i).symm]
    exact hΦ _ g₁ g₂ hRes hB₁
  simpa only [B, Set.preimage_id] using
    (LQGMetric.LocalEvent.aeEventIn_of_saturated
      (Y := id) (R := R) (V := R) (B := B) (W := W)
      measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl)
      hWm (by simpa only [B, Measure.map_id] using hB) hWae hSat)

/-! ### Deterministic locality -/

/-- **Locality of the localized LFPP metric, general form**: if `1 < log δ⁻¹ ≤ L`, `τ > 0` and the
closed `δL`-balls around the `τ`-neighbourhood of `S` lie in the open set `O`, the internal metric of
`Y_{δ,L}[g]` on `S` depends on `g` only through its restriction to `O`. -/
theorem locMetric_internal_congr_of (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) {δ L : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hδ1 : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L) (S : Set ℂ)
    (O : TopologicalSpace.Opens ℂ) {τ : ℝ} (hτ : 0 < τ)
    (hball : ∀ z ∈ thickening τ S, closedBall z (δ * L) ⊆ (O : Set ℂ))
    {g₁ g₂ : DistC} (he : restrictTo O g₁ = restrictTo O g₂) :
    (locMetric ξ m δ L hδ g₁).internal S = (locMetric ξ m δ L hδ g₂).internal S := by
  have hρ : B2.Polylog.plRad (Field.uniformLocalizationExponent δ L) δ = δ * L :=
    Field.plRad_uniform_eq δ L hδ1 hL
  set W₂ : Set ℂ := thickening τ S with hW₂
  have hW₂o : IsOpen W₂ := isOpen_thickening
  have hUW₂ : S ⊆ W₂ := self_subset_thickening hτ _
  have hclose : ∀ z ∈ W₂, |B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ L) δ hδ g₂ z
      - B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ L) δ hδ g₁ z| ≤ 0 := by
    intro z hz
    have := B2.Polylog.plMollify_congr (Field.uniformLocalizationExponent δ L) δ hδ O he
      (by rw [hρ]; exact hball z hz)
    change |B2.Polylog.plMollify _ δ hδ g₂ z - B2.Polylog.plMollify _ δ hδ g₁ z| ≤ 0
    rw [this, sub_self, abs_zero]
  have hclose' : ∀ z ∈ W₂, |B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ L) δ hδ g₁ z
      - B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ L) δ hδ g₂ z| ≤ 0 := by
    intro z hz
    rw [abs_sub_comm]
    exact hclose z hz
  funext p
  apply le_antisymm
  · have h := lfpp_internal_le_of_close ξ (m ⟨δ, hδ.1⟩) hW₂o hUW₂ hclose' p
    rwa [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h
  · have h := lfpp_internal_le_of_close ξ (m ⟨δ, hδ.1⟩) hW₂o hUW₂ hclose p
    rwa [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h

/-- **Locality of the localized LFPP metric**: if `1 < log δ⁻¹ ≤ L` and `δL < 1/16`, the internal
metric of `Y_{δ,L}[g]` on `U` depends on `g` only through its restriction to `A_{1/16,32}(0)`. -/
theorem locMetric_internal_congr (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) {δ L : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hδ1 : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L)
    (hδL : δ * L < 1 / 16) {g₁ g₂ : DistC} (he : restrictTo window g₁ = restrictTo window g₂) :
    (locMetric ξ m δ L hδ g₁).internal tgtU = (locMetric ξ m δ L hδ g₂).internal tgtU := by
  refine locMetric_internal_congr_of ξ m hδ hδ1 hL tgtU window (τ := 1 / 16 - δ * L)
    (by linarith) (fun z hz w hw => ?_) he
  rw [mem_closedBall] at hw
  obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.1 hz
  have hwy : dist w y < 1 / 16 := by
    calc dist w y ≤ dist w z + dist z y := dist_triangle _ _ _
      _ < δ * L + (1 / 16 - δ * L) := add_lt_add_of_le_of_lt hw hzy
      _ = 1 / 16 := by ring
  rw [dist_eq_norm] at hwy
  have h1 := norm_sub_norm_le w y
  have h2 := norm_sub_norm_le y w
  rw [norm_sub_rev] at h2
  exact mem_window.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- **Locality of `h_1(0)`**: the circle average on `∂B_1` depends only on the field in the
window (its approximating bump averages are supported near `∂B_1` from the first index on). -/
theorem circleAvg_one_congr {g₁ g₂ : DistC} (he : restrictTo window g₁ = restrictTo window g₂) :
    circleAvg g₁ 1 0 = circleAvg g₂ 1 0 := by
  have hev : (fun n : ℕ => Real.circleAverage (fun x => g₁ (LQGMetric.bumpTest n x)) 0 1) =ᶠ[atTop]
      (fun n : ℕ => Real.circleAverage (fun x => g₂ (LQGMetric.bumpTest n x)) 0 1) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine Real.circleAverage_congr_sphere fun x hx => ?_
    have hx1 : ‖x‖ = 1 := by
      rw [mem_sphere, dist_zero_right, abs_one] at hx
      exact hx
    refine LQGMetric.DFGPS.L217.apply_eq_of_restrictTo_eq he _ ?_
    have hts : tsupport (LQGMetric.bumpTest n x : ℂ → ℝ) ⊆ closedBall x ((2 : ℝ)⁻¹ ^ n) := by
      change tsupport (ContDiffBump.normed _ MeasureTheory.volume) ⊆ _
      rw [ContDiffBump.tsupport_normed_eq]
    refine hts.trans fun w hw => ?_
    have hpow : (2 : ℝ)⁻¹ ^ n ≤ 1 / 2 := by
      calc (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
        _ = 1 / 2 := by norm_num
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 := norm_sub_norm_le w x
    have h2 := norm_sub_norm_le x w
    rw [norm_sub_rev] at h2
    exact mem_window.2 ⟨by linarith, by linarith⟩
  unfold circleAvg limUnder
  rw [Filter.map_congr hev]

/-! ### Scaling -/

/-- Curves of a metric and of a positive finite multiple coincide. -/
theorem isCurve_iff_of_eq_mul {S S' : LSCMetric} {e : ℝ≥0∞} (he0 : e ≠ 0) (het : e ≠ ⊤)
    (h : ∀ p, S' p = e * S p) {P : ℝ → ℂ} {a b : ℝ} : S'.IsCurve P a b ↔ S.IsCurve P a b := by
  let ι : S.Space → S'.Space := fun x => x
  let ι' : S'.Space → S.Space := fun x => x
  have hL : LipschitzWith e.toNNReal ι := fun x y => by
    change S' (x, y) ≤ (e.toNNReal : ℝ≥0∞) * S (x, y)
    rw [h, ENNReal.coe_toNNReal het]
  have hL' : LipschitzWith e⁻¹.toNNReal ι' := fun x y => by
    change S (x, y) ≤ (e⁻¹.toNNReal : ℝ≥0∞) * S' (x, y)
    rw [h, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2 he0), ← mul_assoc,
      ENNReal.inv_mul_cancel he0 het, one_mul]
  constructor
  · intro hP
    exact ⟨hP.1, hL'.continuous.comp_continuousOn hP.2⟩
  · intro hP
    exact ⟨hP.1, hL.continuous.comp_continuousOn hP.2⟩

/-- Internal metrics scale with the metric. -/
theorem internal_eq_mul_of_eq_mul {S S' : LSCMetric} {e : ℝ≥0∞} (he0 : e ≠ 0) (het : e ≠ ⊤)
    (h : ∀ p, S' p = e * S p) (Y : Set ℂ) (p : Y × Y) :
    S'.internal Y p = e * S.internal Y p := by
  unfold LSCMetric.internal
  simp only [ENNReal.mul_iInf_of_ne he0 het]
  refine iInf_congr fun P => iInf_congr fun a => iInf_congr fun b => ?_
  rw [show (S'.IsCurve P a b) = (S.IsCurve P a b) from propext (isCurve_iff_of_eq_mul he0 het h)]
  refine iInf_congr fun _ => iInf_congr fun _ => iInf_congr fun _ => iInf_congr fun _ => ?_
  exact len_eq_mul_len e h P a b

/-- Internal set distances scale with the metric. -/
theorem internalSetDist_eq_mul_of_eq_mul {S S' : LSCMetric} {e : ℝ≥0∞} (he0 : e ≠ 0)
    (het : e ≠ ⊤) (h : ∀ p, S' p = e * S p) (Y : Set ℂ) (K₁ K₂ : Set Y) :
    S'.internalSetDist Y K₁ K₂ = e * S.internalSetDist Y K₁ K₂ := by
  unfold LSCMetric.internalSetDist
  simp only [ENNReal.mul_iInf_of_ne he0 het]
  exact iInf_congr fun x => iInf_congr fun _ => iInf_congr fun y => iInf_congr fun _ =>
    internal_eq_mul_of_eq_mul he0 het h Y (x, y)

/-- **Lemma 3.2's unit-adjusted event is invariant under a common scaling** of both metrics and
of the unit. -/
theorem lemma32EventU_scale {S T S' T' : LSCMetric} (c : ℝ)
    (hS : ∀ p, S' p = ENNReal.ofReal (Real.exp c) * S p)
    (hT : ∀ p, T' p = ENNReal.ofReal (Real.exp c) * T p) (η ν M t : ℝ) :
    Lemma32EventU S' T' η ν M (Real.exp c * t) ↔ Lemma32EventU S T η ν M t := by
  set e : ℝ≥0∞ := ENNReal.ofReal (Real.exp c) with he
  have he0 : e ≠ 0 := by simpa [he] using Real.exp_pos c
  have het : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmul : ∀ x : ℝ, ENNReal.ofReal (x * (Real.exp c * t)) = e * ENNReal.ofReal (x * t) := by
    intro x
    rw [he, ← ENNReal.ofReal_mul (Real.exp_pos c).le]
    congr 1
    ring
  have hone : ∀ (A B : LSCMetric) (A' B' : LSCMetric), (∀ p, A' p = e * A p) →
      (∀ p, B' p = e * B p) →
      (OneWayCompare A' B' η (ν * (Real.exp c * t)) (M * (Real.exp c * t)) ↔
        OneWayCompare A B η (ν * t) (M * t)) := by
    intro A B A' B' hA hB
    unfold OneWayCompare
    refine forall_congr' fun u => forall_congr' fun v => forall_congr' fun _ =>
      forall_congr' fun _ => ?_
    rw [internal_eq_mul_of_eq_mul he0 het hA, internalSetDist_eq_mul_of_eq_mul he0 het hB,
      hmul, hmul, ← mul_add, ENNReal.mul_le_mul_iff_right he0 het,
      ENNReal.mul_le_mul_iff_right he0 het]
  exact and_congr (hone S T S' T' hS hT) (hone T S T' S' hT hS)

/-- Lemma 3.2's event depends on the two metrics only through their internal metrics on `U`. -/
theorem lemma32EventU_congr {S₁ S₂ T₁ T₂ : LSCMetric}
    (hS : S₁.internal tgtU = S₂.internal tgtU) (hT : T₁.internal tgtU = T₂.internal tgtU)
    (η ν M t : ℝ) : Lemma32EventU S₁ T₁ η ν M t ↔ Lemma32EventU S₂ T₂ η ν M t := by
  have hSV : S₁.internal srcV = S₂.internal srcV :=
    Uniqueness.Toolkit.InternalMetrics.internal_eq_of_internal_eq S₁ S₂ srcV_subset_tgtU hS
  have hTV : T₁.internal srcV = T₂.internal srcV :=
    Uniqueness.Toolkit.InternalMetrics.internal_eq_of_internal_eq T₁ T₂ srcV_subset_tgtU hT
  have hSd : ∀ K₁ K₂ : Set tgtU, S₁.internalSetDist tgtU K₁ K₂ = S₂.internalSetDist tgtU K₁ K₂ :=
    fun K₁ K₂ => by unfold LSCMetric.internalSetDist; rw [hS]
  have hTd : ∀ K₁ K₂ : Set tgtU, T₁.internalSetDist tgtU K₁ K₂ = T₂.internalSetDist tgtU K₁ K₂ :=
    fun K₁ K₂ => by unfold LSCMetric.internalSetDist; rw [hT]
  simp only [Lemma32EventU, Lemma32Event, OneWayCompare, hSV, hTV, hSd, hTd]

/-- Adding a constant to the field multiplies the localized LFPP metric by `e^{ξc}`. -/
theorem locMetric_addConst (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (δ L : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (g : DistC) (c : ℝ) (p : ℂ × ℂ) :
    locMetric ξ m δ L hδ (addConst g c) p = ENNReal.ofReal (Real.exp (ξ * c)) *
      locMetric ξ m δ L hδ g p :=
  lfppMetric_add_const ξ (m ⟨δ, hδ.1⟩) c
    (fun z => B2.Polylog.plMollify_addConst _ δ hδ g c z) p

/-! ### The locality clause -/

/-- The unit-adjusted event of Lemma 3.2 for the localized metric, as a set of fields. -/
def locEventSet (D : DistC → LSCMetric) (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (δ L : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (η ν M : ℝ) : Set DistC :=
  {g | Lemma32EventU (D g) (locMetric ξ m δ L hδ g) η ν M (Real.exp (ξ * circleAvg g 1 0))}

theorem umeasurableSet_locEventSet {D : DistC → LSCMetric} (hD : Measurable D) (ξ : ℝ)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (δ L : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (η ν M : ℝ) :
    LQGMetric.UMeasurableSet (locEventSet D ξ m δ L hδ η ν M) :=
  umeasurableSet_lemma32EventU hD (B2.Polylog.measurable_plLocMetric ξ _ m δ hδ)
    (Real.measurable_exp.comp (measurable_const.mul (LQGMetric.measurable_circleAvg_left 1 0)))
    η ν M

/-- **Locality on the canonical space**: under the law `μ` of a whole-plane GFF plus a continuous
function, the localized event is a.s. an event of the field in the window. -/
theorem aeEventIn_locEventSet_canonical (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) {δ L : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hδ1 : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L) (hδL : δ * L < 1 / 16) (η ν M : ℝ) :
    AEEventIn μ (fieldSigma id window) (locEventSet D (ξ : ℝ) m δ L hδ η ν M) := by
  let F : Fin 1 → DistC → LSCMetric := fun _ => D
  let Φ : (Fin 1 → (tgtU × tgtU → ℝ≥0∞)) → DistC → Prop := fun ρ g =>
    ∃ d : LSCMetric, d.internal tgtU = ρ 0 ∧
      Lemma32EventU d (locMetric (ξ : ℝ) m δ L hδ g) η ν M (Real.exp ((ξ : ℝ) * circleAvg g 1 0))
  have hEq : {g : DistC | Φ (fun i => (F i g).internal tgtU) g} =
      locEventSet D (ξ : ℝ) m δ L hδ η ν M := by
    ext g
    constructor
    · rintro ⟨d, hd, hE⟩
      exact (lemma32EventU_congr hd rfl η ν M _).1 hE
    · intro hE
      exact ⟨D g, rfl, hE⟩
  have hΦ : ∀ ρ g₁ g₂, restrictTo window g₁ = restrictTo window g₂ → Φ ρ g₁ → Φ ρ g₂ := by
    rintro ρ g₁ g₂ he ⟨d, hd, hE⟩
    refine ⟨d, hd, ?_⟩
    rw [← circleAvg_one_congr he]
    exact (lemma32EventU_congr rfl (locMetric_internal_congr (ξ : ℝ) m hδ hδ1 hL hδL he) η ν M
      _).1 hE
  have hB : NullMeasurableSet {g : DistC | Φ (fun i => (F i g).internal tgtU) g} μ := by
    rw [hEq]
    exact (umeasurableSet_locEventSet hD.measurable (ξ : ℝ) m δ L hδ η ν M).nullMeasurableSet μ
  have h := aeEventIn_internal_subset_local μ hμ ξ Q F (fun _ => hD) tgtU window
    tgtU_subset_window Φ hΦ hB
  rwa [hEq] at h

/-- The test function `bumpTest 1 1` (a normalized bump at `1`, supported in `B̄_{1/2}(1)`) used to
remove the additive constant. -/
theorem integral_bumpTest_one : ∫ x, LQGMetric.bumpTest 1 1 x = 1 :=
  ContDiffBump.integral_normed _

theorem tsupport_bumpTest_one_subset :
    tsupport (LQGMetric.bumpTest 1 1 : ℂ → ℝ) ⊆ (window : Set ℂ) := by
  have hts : tsupport (LQGMetric.bumpTest 1 1 : ℂ → ℝ) = closedBall (1 : ℂ) ((2 : ℝ)⁻¹ ^ 1) := by
    change tsupport (ContDiffBump.normed _ MeasureTheory.volume) = _
    rw [ContDiffBump.tsupport_normed_eq]
  rw [hts]
  intro w hw
  rw [mem_closedBall, dist_eq_norm, pow_one] at hw
  have h1 := norm_sub_norm_le w 1
  have h2 := norm_sub_norm_le 1 w
  rw [norm_sub_rev] at h2
  rw [norm_one] at h1 h2
  exact mem_window.2 ⟨by linarith, by norm_num at hw; linarith⟩

/-- **Locality clause of Lemma 3.2** (unit-adjusted form): for a normalized whole-plane GFF and
`1 < log δ⁻¹ ≤ L` with `δL < 1/16`, the event of Lemma 3.2 for `(D_h, Y_{δ,L}[h])`, with height
`M` and error `ν` in units `e^{ξ h_1(0)}`, is almost surely equal to an event measurable from the
field in `A_{1/16,32}(0)` modulo additive constants. -/
theorem aeEventIn_lemma32EventU_loc (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsStrongLQGMetric ξ Q D) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) {δ L : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hδ1 : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L) (hδL : δ * L < 1 / 16) (η ν M : ℝ) :
    AEEventIn P (fieldSigma0On h window)
      {ω | Lemma32EventU (D (h ω)) (locMetric (ξ : ℝ) m δ L hδ (h ω)) η ν M
        (Real.exp ((ξ : ℝ) * circleAvg (h ω) 1 0))} := by
  have hDw : IsWeakLQGMetric ξ Q D := B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  have hhm : Measurable h := hh.1.measurable
  set ψ : LQGMetric.TestC := LQGMetric.bumpTest 1 1
  set c : Ω → ℝ := fun ω => -(h ω ψ) with hc
  have hcm : Measurable c := ((LQGMetric.measurable_evalDist ψ).comp hhm).neg
  set Y : Ω → DistC := LQGMetric.CONF.normIn h ψ with hYdef
  have hYc : Y = fun ω => addConst (h ω) (c ω) := rfl
  have hY : LQGMetric.IsWholePlaneGFF Y P := by
    rw [hYc]
    exact hh.1.addConst hcm
  have hYm : Measurable Y := hY.measurable
  have : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).2 inferInstance
  have hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) (P.map Y) :=
    LQGMetric.GM.detGFFPlusCont (LQGMetric.GM.isWholePlaneGFF_id_map hY)
  -- locality on the canonical space, pulled back to `Ω`
  obtain ⟨F, hFm, hFa⟩ := aeEventIn_locEventSet_canonical (P.map Y) hμ ξ Q D hDw m hδ hδ1 hL hδL
    η ν M
  have hFgm : MeasurableSet[fieldSigma Y window] (Y ⁻¹' F) := by
    unfold fieldSigma at hFm ⊢
    rcases hFm with ⟨S, hS, hFS⟩
    exact ⟨S, hS, by rw [← hFS]; rfl⟩
  have hFaP : ∀ᵐ ω ∂P, (Y ω ∈ locEventSet D (ξ : ℝ) m δ L hδ η ν M) = (Y ω ∈ F) :=
    ae_of_ae_map hYm.aemeasurable hFa
  have hEY : AEEventIn P (fieldSigma Y window)
      {ω | Y ω ∈ locEventSet D (ξ : ℝ) m δ L hδ η ν M} :=
    ⟨Y ⁻¹' F, hFgm, by filter_upwards [hFaP] with ω hω; exact hω⟩
  have hE0 := Uniqueness.Toolkit.LocalEvents.aeEventIn_fieldSigma0On_of_normIn h ψ
    integral_bumpTest_one window tsupport_bumpTest_one_subset hEY
  -- invariance under the additive constant
  have hshiftD := Uniqueness.Positivity.Witnesses.ae_addConst_eq_mul P h
    (B2.PfeAxioms.isGFFPlusCont_of_normalized hh) ξ Q D hDw c
  have hcirc : ∀ᵐ ω ∂P, circleAvg (Y ω) 1 0 = circleAvg (h ω) 1 0 + c ω := by
    filter_upwards [hh.2] with ω hω
    exact LQGMetric.CircleAvg.circleAvg_addConst_of_tendsto hω (c ω)
  obtain ⟨G, hGm, hGa⟩ := hE0
  refine ⟨G, hGm, ?_⟩
  filter_upwards [hGa, hshiftD, hcirc] with ω hG hDω hcω
  rw [← hG]
  change Lemma32EventU (D (h ω)) (locMetric (ξ : ℝ) m δ L hδ (h ω)) η ν M
      (Real.exp ((ξ : ℝ) * circleAvg (h ω) 1 0)) =
    Lemma32EventU (D (Y ω)) (locMetric (ξ : ℝ) m δ L hδ (Y ω)) η ν M
      (Real.exp ((ξ : ℝ) * circleAvg (Y ω) 1 0))
  have hunit : Real.exp ((ξ : ℝ) * circleAvg (Y ω) 1 0) =
      Real.exp ((ξ : ℝ) * c ω) * Real.exp ((ξ : ℝ) * circleAvg (h ω) 1 0) := by
    rw [hcω, ← Real.exp_add]
    congr 1
    ring
  rw [hunit]
  refine propext (lemma32EventU_scale ((ξ : ℝ) * c ω) (fun p => hDω p) (fun p => ?_) η ν M _).symm
  exact locMetric_addConst (ξ : ℝ) m δ L hδ (h ω) (c ω) p

/-- **Locality clause of Lemma 3.2** for the plain event (the normalized field has `h_1(0) = 0`
almost surely, so the units are `1`). -/
theorem aeEventIn_lemma32Event_loc (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsStrongLQGMetric ξ Q D) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) {δ L : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hδ1 : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L) (hδL : δ * L < 1 / 16) (η ν M : ℝ) :
    AEEventIn P (fieldSigma0On h window)
      {ω | Lemma32Event (D (h ω)) (locMetric (ξ : ℝ) m δ L hδ (h ω)) η ν M} := by
  obtain ⟨G, hGm, hGa⟩ := aeEventIn_lemma32EventU_loc ξ Q D hD m P h hh hδ hδ1 hL hδL η ν M
  refine ⟨G, hGm, ?_⟩
  filter_upwards [hGa, hh.2] with ω hG hω
  rw [← hG]
  have h0 : circleAvg (h ω) 1 0 = 0 := LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hω
  change Lemma32Event (D (h ω)) (locMetric (ξ : ℝ) m δ L hδ (h ω)) η ν M =
    Lemma32EventU (D (h ω)) (locMetric (ξ : ℝ) m δ L hδ (h ω)) η ν M
      (Real.exp ((ξ : ℝ) * circleAvg (h ω) 1 0))
  rw [h0, mul_zero, Real.exp_zero]
  exact propext (lemma32EventU_one _ _ η ν M).symm

/-- The open-window σ-algebra modulo constants is contained in the closed-annulus σ-algebra modulo
constants of the annulus concentration theorem (1.6). -/
theorem fieldSigma0On_window_le_closed {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC) :
    fieldSigma0On h window ≤ fieldSigmaClosed0 h {z | 1 / 16 ≤ ‖z‖ ∧ ‖z‖ ≤ 32} := by
  refine le_iInf₂ fun ε hε => ?_
  refine LQGMetric.CONF.conf36_fieldSigma0On_mono h ?_
  intro z hz
  have hz' := mem_window.1 hz
  exact self_subset_thickening hε _ ⟨hz'.1.le, hz'.2.le⟩

/-- **Locality clause of Lemma 3.2**, in the closed-annulus σ-algebra modulo constants. -/
theorem aeEventIn_lemma32Event_loc_closed (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsStrongLQGMetric ξ Q D) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) {δ L : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hδ1 : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L) (hδL : δ * L < 1 / 16) (η ν M : ℝ) :
    AEEventIn P (fieldSigmaClosed0 h {z | 1 / 16 ≤ ‖z‖ ∧ ‖z‖ ≤ 32})
      {ω | Lemma32Event (D (h ω)) (locMetric (ξ : ℝ) m δ L hδ (h ω)) η ν M} := by
  obtain ⟨G, hGm, hGa⟩ := aeEventIn_lemma32Event_loc ξ Q D hD m P h hh hδ hδ1 hL hδL η ν M
  exact ⟨G, fieldSigma0On_window_le_closed h G hGm, hGa⟩

end SupercriticalLFPPAS.Local
