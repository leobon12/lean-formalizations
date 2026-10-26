import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge

/-!
# Good covers, part 1: annulus-local events and the finite test family

Source: the paper, display (10) (l. 441–451), and the same scheme in Lemma 2.1 (l. 133–138, 145–147).
Generic in the events `F z r`: nothing here depends on how the metric `e` is defined.

* `eventAnnulus z r = cl A_{r/2,2r}(z)`, the closed annulus of the event `F_{z,r}` (`lem-5.1#locality`: the internal
  metrics of a closed annulus are determined by `σ(h|_{cl A}) = ⋂_δ σ(h|_{B_δ(cl A)})`, DG L1007–L1022).
* `localSigma h z r`: the σ-algebra of the field on the ENLARGED open annulus `A_{3r/7, 9r/4}(z) ⊇ cl A_{r/2,2r}(z)`,
  centred at the circle average `h_{3r}(z)` (corrected reference radius `3r`, `s₁ = 1/7`, `s₂ = 3/4`).
  This is exactly what the annulus iteration consumes, and it is the weakest of the usual forms:
  - the paper's / `lem-5.1#locality`'s closed form, `σ(h|_{cl A_{r/2,2r}(z)})` modulo constants (`fieldSigmaClosed0`), implies it
    (`aeEventIn_localSigma_of_closed`);
  - the sealed library's form, "for every open `U ⊇ cl A_{r/2,2r}(z)` and every `R`, an event of `σ((h − h_R(z))|_U)`"
    (SLU `S36.attained_centered_local`), implies it (`aeEventIn_localSigma_of_open`).
* `IsAnnulusLocalOn P h F K ρ r₀`: for centres `z ∈ cl B_ρ(K)` and radii `r ∈ (0, r₀]`, `F z r` is almost
  surely an event of `localSigma h z r`. `AEEventIn` asks only for almost-sure equality with a sub-σ-algebra
  event, so it fits universally measurable (co-analytic) events: `aeEventIn_of_nullMeasurable_preimage`,
  `aeEventIn_of_universallyMeasurable`. `IsClosedAnnulusLocalOn` is the closed form; `.toAnnulusLocalOn`.
* `IsProbLowerOn P F K ρ r₀ p`: `P[F z r] ≥ p` on the same region.
* `coverFamily K ε`: the FINITE test family of (10): centres of the lattice `(ε²/100)ℤ²` in
  `cl B_ε(K)` and radii `8^{-k} ε ∈ [ε², ε]`, `k ≥ 1` (`coverFamily_finite`, `coverFamily_radius`).
* `coverEvent F K ε`: every `x ∈ K` lies in `B_{r/2}(z)` for some `(z, r)` in the family with `F z r`.
  It is a finite Boolean combination of the `F z r` (`coverEvent_eq_biUnion`), hence null-measurable
  (`nullMeasurableSet_coverEvent`); it is monotone in `K` and closed under finite unions of `K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Cover

open LQGMetric LQGMetric.Blueprint
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration (closedAnnulus)

/-! ## 1. Annuli -/

/-- the closed annulus `cl A_{r/2,2r}(z) = {w : r/2 ≤ |w − z| ≤ 2r}` of the event `F_{z,r}` -/
def eventAnnulus (z : ℂ) (r : ℝ) : Set ℂ := closedAnnulus z (r / 2) (2 * r)

theorem isCompact_closedAnnulus (z : ℂ) (u v : ℝ) : IsCompact (closedAnnulus z u v) := by
  have hclosed : IsClosed (closedAnnulus z u v) :=
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
  refine (isCompact_closedBall z v).of_isClosed_subset hclosed fun w hw => ?_
  exact mem_closedBall.2 (by simpa only [dist_eq_norm] using hw.2)

theorem isCompact_eventAnnulus (z : ℂ) (r : ℝ) : IsCompact (eventAnnulus z r) :=
  isCompact_closedAnnulus z _ _

/-- `cl A_{r/2,2r}(z) ⊆ A_{(1/7)·3r, (3/4)·3r}(z)`: the enlarged open annulus of reference radius `3r`
(corrected reference radius `R = 3r`, `s₁ = 1/7`, `s₂ = 3/4`). -/
theorem eventAnnulus_subset_annulus (z : ℂ) {r : ℝ} (hr : 0 < r) :
    eventAnnulus z r ⊆ (annulus z (1 / 7 * (3 * r)) (3 / 4 * (3 * r)) : Set ℂ) := by
  intro w hw
  obtain ⟨h1, h2⟩ := hw
  change 1 / 7 * (3 * r) < ‖w - z‖ ∧ ‖w - z‖ < 3 / 4 * (3 * r)
  constructor <;> linarith

/-! ## 2. Locality and probability hypotheses -/

section Hyp

variable {Ω : Type} [MeasurableSpace Ω]

/-- the σ-algebra of the field on the enlarged open annulus `A_{3r/7, 9r/4}(z)`, centred at `h_{3r}(z)` -/
abbrev localSigma (h : Ω → DistC) (z : ℂ) (r : ℝ) : MeasurableSpace Ω :=
  fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (3 * r) z))
    (annulus z (1 / 7 * (3 * r)) (3 / 4 * (3 * r)))

/-- **annulus locality on a neighbourhood of `K`**: for `z ∈ cl B_ρ(K)` and `r ∈ (0, r₀]`, the event
`F z r` is almost surely an event of `localSigma h z r`. -/
def IsAnnulusLocalOn (P : Measure Ω) (h : Ω → DistC) (F : ℂ → ℝ → Set Ω) (K : Set ℂ) (ρ r₀ : ℝ) :
    Prop :=
  ∀ z ∈ cthickening ρ K, ∀ r ∈ Ioc (0 : ℝ) r₀, AEEventIn P (localSigma h z r) (F z r)

/-- **closed-annulus locality** (`lem-5.1#locality`): `F z r` is almost surely an event of `σ(h|_{cl A_{r/2,2r}(z)})`
modulo additive constants -/
def IsClosedAnnulusLocalOn (P : Measure Ω) (h : Ω → DistC) (F : ℂ → ℝ → Set Ω) (K : Set ℂ)
    (ρ r₀ : ℝ) : Prop :=
  ∀ z ∈ cthickening ρ K, ∀ r ∈ Ioc (0 : ℝ) r₀,
    AEEventIn P (fieldSigmaClosed0 h (eventAnnulus z r)) (F z r)

/-- the closed mod-constant form implies the centred enlarged-annulus form -/
theorem aeEventIn_localSigma_of_closed {P : Measure Ω} {h : Ω → DistC} {z : ℂ} {r : ℝ}
    (hr : 0 < r) {E : Set Ω} (hE : AEEventIn P (fieldSigmaClosed0 h (eventAnnulus z r)) E) :
    AEEventIn P (localSigma h z r) E := by
  obtain ⟨G, hG, hEG⟩ := hE
  exact ⟨G, SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.fieldSigmaClosed0_le_centered_open
    h (fun ω => -circleAvg (h ω) (3 * r) z) _ _ (isCompact_eventAnnulus z r)
    (eventAnnulus_subset_annulus z hr) G hG, hEG⟩

/-- the sealed library's form (every open `U ⊇ cl A_{r/2,2r}(z)`, every centring radius `R`) implies the
centred enlarged-annulus form -/
theorem aeEventIn_localSigma_of_open {P : Measure Ω} {h : Ω → DistC} {z : ℂ} {r : ℝ}
    (hr : 0 < r) {E : Set Ω}
    (hE : ∀ U : TopologicalSpace.Opens ℂ, eventAnnulus z r ⊆ U → ∀ R : ℝ,
      AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) R z)) U) E) :
    AEEventIn P (localSigma h z r) E :=
  hE _ (eventAnnulus_subset_annulus z hr) (3 * r)

theorem IsClosedAnnulusLocalOn.toAnnulusLocalOn {P : Measure Ω} {h : Ω → DistC}
    {F : ℂ → ℝ → Set Ω} {K : Set ℂ} {ρ r₀ : ℝ} (H : IsClosedAnnulusLocalOn P h F K ρ r₀) :
    IsAnnulusLocalOn P h F K ρ r₀ := fun z hz r hr =>
  aeEventIn_localSigma_of_closed hr.1 (H z hz r hr)

/-- `localSigma h z r` is a sub-σ-algebra for a whole-plane GFF -/
theorem localSigma_le {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ) (r : ℝ) :
    localSigma h z r ≤ ‹MeasurableSpace Ω› :=
  ((measurable_restrictTo _).comp
    (hh.addConst ((measurable_circleAvg_left (3 * r) z).comp hh.measurable).neg).measurable).comap_le

/-- **the lower probability bound on a neighbourhood of `K`**: `P[F z r] ≥ p` for `z ∈ cl B_ρ(K)` and
`r ∈ (0, r₀]` -/
def IsProbLowerOn (P : Measure Ω) (F : ℂ → ℝ → Set Ω) (K : Set ℂ) (ρ r₀ p : ℝ) : Prop :=
  ∀ z ∈ cthickening ρ K, ∀ r ∈ Ioc (0 : ℝ) r₀, ENNReal.ofReal p ≤ P (F z r)

theorem IsAnnulusLocalOn.mono {P : Measure Ω} {h : Ω → DistC} {F : ℂ → ℝ → Set Ω} {K L : Set ℂ}
    {ρ ρ' r₀ r₀' : ℝ} (H : IsAnnulusLocalOn P h F K ρ r₀) (hLK : L ⊆ K) (hρ : ρ' ≤ ρ)
    (hr : r₀' ≤ r₀) : IsAnnulusLocalOn P h F L ρ' r₀' := fun z hz r hr' =>
  H z ((cthickening_mono hρ L).trans (cthickening_subset_of_subset ρ hLK) hz) r
    ⟨hr'.1, hr'.2.trans hr⟩

theorem IsProbLowerOn.mono {P : Measure Ω} {F : ℂ → ℝ → Set Ω} {K L : Set ℂ}
    {ρ ρ' r₀ r₀' p : ℝ} (H : IsProbLowerOn P F K ρ r₀ p) (hLK : L ⊆ K) (hρ : ρ' ≤ ρ)
    (hr : r₀' ≤ r₀) : IsProbLowerOn P F L ρ' r₀' p := fun z hz r hr' =>
  H z ((cthickening_mono hρ L).trans (cthickening_subset_of_subset ρ hLK) hz) r
    ⟨hr'.1, hr'.2.trans hr⟩

omit [MeasurableSpace Ω] in
/-- **universally measurable events fit `AEEventIn`**: if `X` is `m`-measurable, `B` is null-measurable
for the law of `X`, and `E = {X ∈ B}` almost surely, then `E` is almost surely an event of `m`. -/
theorem aeEventIn_of_nullMeasurable_preimage {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) {P : Measure Ω} {β : Type*} [MeasurableSpace β] {X : Ω → β}
    (hX : Measurable[m] X) {B : Set β} (hB : NullMeasurableSet B (P.map X)) {E : Set Ω}
    (hE : E =ᵐ[P] X ⁻¹' B) : AEEventIn P m E := by
  refine ⟨X ⁻¹' toMeasurable (P.map X) B, hX (measurableSet_toMeasurable _ _), ?_⟩
  have hX' : Measurable X := hX.mono hm le_rfl
  exact hE.trans ((hX'.quasiMeasurePreserving P).preimage_ae_eq hB.toMeasurable_ae_eq.symm)

omit [MeasurableSpace Ω] in
/-- the same, for a **universally measurable** `B` (null-measurable for every finite measure) -/
theorem aeEventIn_of_universallyMeasurable {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) {P : Measure Ω} [IsFiniteMeasure P] {β : Type*}
    [MeasurableSpace β] {X : Ω → β} (hX : Measurable[m] X) {B : Set β}
    (hB : ∀ μ : Measure β, IsFiniteMeasure μ → NullMeasurableSet B μ) {E : Set Ω}
    (hE : E =ᵐ[P] X ⁻¹' B) : AEEventIn P m E :=
  aeEventIn_of_nullMeasurable_preimage hm hX (hB _ inferInstance) hE

omit [MeasurableSpace Ω] in
/-- an event a.s. in a sub-σ-algebra is null-measurable -/
theorem aeEventIn_nullMeasurableSet {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) {P : Measure Ω} {E : Set Ω} (hE : AEEventIn P m E) : NullMeasurableSet E P := by
  obtain ⟨F, hF, hEF⟩ := hE
  exact (hm _ hF).nullMeasurableSet.congr hEF.symm

/-- `σ(h|_V mod constants)` is a sub-σ-algebra when `h` is measurable -/
theorem fieldSigma0On_le {h : Ω → DistC} (hh : Measurable h) (V : Set ℂ) :
    fieldSigma0On h V ≤ ‹MeasurableSpace Ω› := by
  rintro s ⟨t, ht, rfl⟩
  exact (measurable_pi_iff.2 fun ψ => (measurable_evalDist ψ.1.1).comp hh) ht

/-- `σ(h|_K mod constants)` is a sub-σ-algebra when `h` is measurable -/
theorem fieldSigmaClosed0_le {h : Ω → DistC} (hh : Measurable h) (K : Set ℂ) :
    fieldSigmaClosed0 h K ≤ ‹MeasurableSpace Ω› :=
  (iInf₂_le (1 : ℝ) one_pos).trans (fieldSigma0On_le hh _)

end Hyp

/-! ## 3. The finite test family and the cover event -/

/-- the lattice point `(ε²/100) m` of mesh `ε²/100` -/
def meshPt (ε : ℝ) (m : ℤ × ℤ) : ℂ := ⟨ε ^ 2 / 100 * m.1, ε ^ 2 / 100 * m.2⟩

/-- the geometric radius `8^{-k} ε` -/
def scaleRad (ε : ℝ) (k : ℕ) : ℝ := (8 : ℝ)⁻¹ ^ k * ε

/-- **the finite test family of (10)**: the pairs `(z, r)` with `z` a lattice point of mesh
`ε²/100` in `cl B_ε(K)` and `r = 8^{-k} ε` with `k ≥ 1` and `8^{-k} ≥ ε`, i.e. `r ∈ [ε², ε/8]`. -/
def coverFamily (K : Set ℂ) (ε : ℝ) : Set (ℂ × ℝ) :=
  {zr | ∃ m : ℤ × ℤ, ∃ k : ℕ, 1 ≤ k ∧ ε ≤ (8 : ℝ)⁻¹ ^ k ∧ meshPt ε m ∈ cthickening ε K ∧
    zr = (meshPt ε m, scaleRad ε k)}

/-- **the good-cover event of (10)**: every `x ∈ K` lies in `B_{r/2}(z)` for some `(z, r)` of the
finite test family with `F z r`. -/
def coverEvent {Ω : Type} (F : ℂ → ℝ → Set Ω) (K : Set ℂ) (ε : ℝ) : Set Ω :=
  {ω | ∀ x ∈ K, ∃ zr ∈ coverFamily K ε, x ∈ ball zr.1 (zr.2 / 2) ∧ ω ∈ F zr.1 zr.2}

theorem scaleRad_pos {ε : ℝ} (hε : 0 < ε) (k : ℕ) : 0 < scaleRad ε k :=
  mul_pos (pow_pos (by norm_num) k) hε

theorem scaleRad_le {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) : scaleRad ε k ≤ ε := by
  have : (8 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc scaleRad ε k ≤ 1 * ε := mul_le_mul_of_nonneg_right this hε
    _ = ε := one_mul ε

/-- the radii of the family lie in `[ε², ε/8] ⊆ [ε², ε]` -/
theorem coverFamily_radius {K : Set ℂ} {ε : ℝ} (hε : 0 ≤ ε) {zr : ℂ × ℝ}
    (hzr : zr ∈ coverFamily K ε) : ε ^ 2 ≤ zr.2 ∧ zr.2 ≤ ε / 8 := by
  obtain ⟨m, k, hk, hεk, -, rfl⟩ := hzr
  have h8 : (8 : ℝ)⁻¹ ^ k ≤ 8⁻¹ := by
    calc (8 : ℝ)⁻¹ ^ k ≤ (8 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 8⁻¹ := pow_one _
  refine ⟨?_, ?_⟩
  · show ε ^ 2 ≤ (8 : ℝ)⁻¹ ^ k * ε
    rw [sq]; exact mul_le_mul_of_nonneg_right hεk hε
  · show (8 : ℝ)⁻¹ ^ k * ε ≤ ε / 8
    rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_right h8 hε

/-- the centres of the family lie in `cl B_ε(K)` -/
theorem coverFamily_centre {K : Set ℂ} {ε : ℝ} {zr : ℂ × ℝ} (hzr : zr ∈ coverFamily K ε) :
    zr.1 ∈ cthickening ε K := by
  obtain ⟨m, k, -, -, hm, rfl⟩ := hzr
  exact hm

/-- **the test family is finite** (for bounded `K` and `ε > 0`) -/
theorem coverFamily_finite {K : Set ℂ} (hK : Bornology.IsBounded K) {ε : ℝ} (hε : 0 < ε) :
    (coverFamily K ε).Finite := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (hK.cthickening (δ := ε))
  -- the exponents: `8^{-k} → 0`, so `ε ≤ 8^{-k}` only for `k < N`
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (show (8 : ℝ)⁻¹ < 1 by norm_num)
  have hkN : ∀ k : ℕ, ε ≤ (8 : ℝ)⁻¹ ^ k → k < N := by
    intro k hk
    by_contra hkn
    have := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 8⁻¹ by norm_num) (by norm_num) (not_lt.1 hkn)
    linarith
  -- the lattice indices: `|m_i| ε²/100 ≤ R`
  set δ : ℝ := ε ^ 2 / 100 with hδ
  have hδ0 : 0 < δ := by positivity
  set B : ℤ := ⌈R / δ⌉ with hB
  have hmB : ∀ t : ℤ, |δ * t| ≤ R → t ∈ Icc (-B) B := by
    intro t ht
    rw [abs_mul, abs_of_pos hδ0] at ht
    have h1 : |(t : ℝ)| ≤ R / δ := by rw [le_div_iff₀ hδ0]; linarith
    have h2 : R / δ ≤ (B : ℝ) := Int.le_ceil _
    have h3 := abs_le.1 (h1.trans h2)
    exact ⟨by exact_mod_cast h3.1, by exact_mod_cast h3.2⟩
  have hfin : (((Icc (-B) B) ×ˢ (Icc (-B) B)) ×ˢ (Iio N) : Set ((ℤ × ℤ) × ℕ)).Finite :=
    ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).prod (Set.finite_Iio N)
  refine (hfin.image fun mk => (meshPt ε mk.1, scaleRad ε mk.2)).subset ?_
  rintro _ ⟨m, k, -, hεk, hm, rfl⟩
  have hnorm := hR _ hm
  have hre : |δ * (m.1 : ℝ)| ≤ R := (Complex.abs_re_le_norm (meshPt ε m)).trans hnorm
  have him : |δ * (m.2 : ℝ)| ≤ R := (Complex.abs_im_le_norm (meshPt ε m)).trans hnorm
  exact ⟨(m, k), ⟨⟨hmB _ hre, hmB _ him⟩, hkN k hεk⟩, rfl⟩

/-- **monotonicity in `K`**: a good cover of `K` restricts to a good cover of `L ⊆ K` -/
theorem coverEvent_mono {Ω : Type} (F : ℂ → ℝ → Set Ω) {K L : Set ℂ} (hLK : L ⊆ K) {ε : ℝ}
    (hε : 0 ≤ ε) : coverEvent F K ε ⊆ coverEvent F L ε := by
  intro ω hω x hx
  obtain ⟨zr, hzr, hxb, hωF⟩ := hω x (hLK hx)
  refine ⟨zr, ?_, hxb, hωF⟩
  obtain ⟨m, k, hk, hεk, -, rfl⟩ := hzr
  refine ⟨m, k, hk, hεk, ?_, rfl⟩
  refine mem_cthickening_of_dist_le _ x ε L hx ?_
  have hb : dist x (meshPt ε m) < scaleRad ε k / 2 := hxb
  have := scaleRad_le hε k
  rw [dist_comm]; linarith

/-- **finite unions**: good covers of `K` and of `L` give a good cover of `K ∪ L` -/
theorem coverEvent_union {Ω : Type} (F : ℂ → ℝ → Set Ω) (K L : Set ℂ) (ε : ℝ) :
    coverEvent F K ε ∩ coverEvent F L ε ⊆ coverEvent F (K ∪ L) ε := by
  have hsub : ∀ {A : Set ℂ}, A ⊆ K ∪ L → coverFamily A ε ⊆ coverFamily (K ∪ L) ε := by
    intro A hA zr hzr
    obtain ⟨m, k, hk, hεk, hm, rfl⟩ := hzr
    exact ⟨m, k, hk, hεk, cthickening_subset_of_subset ε hA hm, rfl⟩
  rintro ω ⟨hK, hL⟩ x (hx | hx)
  · obtain ⟨zr, hzr, h1, h2⟩ := hK x hx
    exact ⟨zr, hsub subset_union_left hzr, h1, h2⟩
  · obtain ⟨zr, hzr, h1, h2⟩ := hL x hx
    exact ⟨zr, hsub subset_union_right hzr, h1, h2⟩

/-- **the cover event is a finite Boolean combination of the `F z r`**: a union, over the subfamilies `S`
of the test family whose half-balls cover `K`, of `⋂_{(z,r) ∈ S} F z r` -/
theorem coverEvent_eq_biUnion {Ω : Type} (F : ℂ → ℝ → Set Ω) (K : Set ℂ) (ε : ℝ) :
    coverEvent F K ε = ⋃ S ∈ {S : Set (ℂ × ℝ) | S ⊆ coverFamily K ε ∧
      K ⊆ ⋃ zr ∈ S, ball zr.1 (zr.2 / 2)}, ⋂ zr ∈ S, F zr.1 zr.2 := by
  ext ω
  simp only [mem_iUnion, mem_iInter, mem_ofPred_eq, exists_prop]
  constructor
  · intro hω
    refine ⟨{zr | zr ∈ coverFamily K ε ∧ ω ∈ F zr.1 zr.2}, ⟨fun zr hzr => hzr.1, ?_⟩,
      fun zr hzr => hzr.2⟩
    intro x hx
    obtain ⟨zr, hzr, hxb, hωF⟩ := hω x hx
    exact mem_biUnion (x := zr) ⟨hzr, hωF⟩ hxb
  · rintro ⟨S, ⟨hSf, hSK⟩, hωS⟩ x hx
    obtain ⟨zr, hzrS, hxb⟩ := mem_iUnion₂.1 (hSK hx)
    exact ⟨zr, hSf hzrS, hxb, hωS zr hzrS⟩

/-- **the cover event is null-measurable** when the events of the (finite) test family are -/
theorem nullMeasurableSet_coverEvent {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {F : ℂ → ℝ → Set Ω} {K : Set ℂ} (hK : Bornology.IsBounded K) {ε : ℝ} (hε : 0 < ε)
    (hF : ∀ zr ∈ coverFamily K ε, NullMeasurableSet (F zr.1 zr.2) P) :
    NullMeasurableSet (coverEvent F K ε) P := by
  rw [coverEvent_eq_biUnion]
  have hfin := coverFamily_finite hK hε
  refine Set.Finite.nullMeasurableSet_biUnion
    (hfin.finite_subsets.subset fun S hS => hS.1) fun S hS => ?_
  exact Set.Finite.nullMeasurableSet_biInter (hfin.subset hS.1) fun zr hzr => hF zr (hS.1 hzr)

/-- the events of the test family are null-measurable under the locality hypothesis (`ε ≤ ρ`, `ε ≤ r₀`) -/
theorem nullMeasurableSet_coverEvent_of_local {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {F : ℂ → ℝ → Set Ω} {K : Set ℂ}
    (hK : Bornology.IsBounded K) {ρ r₀ : ℝ} (hloc : IsAnnulusLocalOn P h F K ρ r₀) {ε : ℝ}
    (hε : 0 < ε) (hερ : ε ≤ ρ) (hεr : ε ≤ r₀) : NullMeasurableSet (coverEvent F K ε) P := by
  refine nullMeasurableSet_coverEvent hK hε fun zr hzr => ?_
  obtain ⟨m, k, -, -, hm, rfl⟩ := hzr
  exact aeEventIn_nullMeasurableSet (localSigma_le hh _ _)
    (hloc _ (cthickening_mono hερ K hm) _ ⟨scaleRad_pos hε k, (scaleRad_le hε.le k).trans hεr⟩)

end SupercriticalConformalCovariance.Cover
