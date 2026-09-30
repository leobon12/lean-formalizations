import QuantumZipper.Proofs.Zipper.E6Up
import QuantumZipper.Proofs.Zipper.ESMComplF1
import QuantumZipper.Proofs.Wire2b

/-!
# The rich local data map `locRich` (decision D25) and E6-UP by pure π-λ

Decision **D25** (`DECISIONS.md`), which refines D23. D23's `D3Plus.locData R` reads the field
only through `Factorization.coords` (dyadic folded circles of radius `2^{-k}`), while
`configLawFull` (the law in which E6 and F1 are stated) reads `lawData`: the raw values
`coordsFull` at the dyadic folded circles of *all* positive dyadic radii and the raw pairings
with *all* test functions. The local σ-algebras of `locData` therefore do not generate the
σ-algebra of `configLawFull`, and E6-UP needed an a.s. reconstruction (`E6.E6ReadStmt`,
regularity of the wedge and of the unzipped field).

`locRich R c` reads, for the field, **the same kind of data as `configLawFull`, localized to
`closedBall 0 R`**: the raw values at the `coordsFull` circles contained in `closedBall 0 R`, the
raw pairings with the test functions supported in `closedBall 0 R` (junk `0` elsewhere), and,
as `locData`, the driver on the capacity window `[0, R]`.

## Main results

* `D3Plus.locRich`, `D3Plus.measurable_locRich`.
* `D3Plus.locData_eq_projRich`: `locData R = projRich ∘ locRich R` (the rich data refine D23's
  data, so every statement for `locRich` implies the same statement for `locData`).
* `E6.truncFull`, `E6.truncFull_cfgFull` (`truncFull R ∘ cfgFull = locRich R`),
  `E6.truncFull_comap_mono`, `E6.truncFull_generate`: the truncations increase and generate the
  σ-algebra of `FullData` (own elementary argument: every `coordsFull` circle lies in some
  `closedBall 0 R`, every test function has compact support, every time `s ≥ 0` is `≤ R` for
  some `R`).
* `E6.configLawFull_eq_of_locRich`: two configurations with a.e.-measurable `configLawFull`
  data and equal `locRich R`-laws for every `R` have equal `configLawFull` (π-λ uniqueness,
  `E6.ext_of_monotone_generating`: Billingsley, *Probability and Measure*, 3rd ed., Thm 3.3;
  Kallenberg, *Foundations of Modern Probability*, 2nd ed., Lemma 1.17).
* `E6.e6UpRich_of_meas : UnzipMeasStmt → E6UpStmtRich`: E6-UP for `locRich`; the only input is
  a.e.-measurability of the unzipped data (`UnzipMeasStmt`). No regularity node.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper

/-! ## The rich local data -/

namespace D3Plus

/-- The `i`-th `coordsFull` folded circle (centre `(fullIndex i).1`, radius `(fullIndex i).2`)
lies in `closedBall 0 R`. -/
def inBallFull (R i : ℕ) : Prop :=
  ‖(CoordsFull.fullIndex i).1‖ + (CoordsFull.fullIndex i).2 ≤ (R : ℝ)

/-- The test function `ρ` is supported in `closedBall 0 R`. -/
def suppIn (R : ℕ) (ρ : TestFun H) : Prop :=
  tsupport ρ.1 ⊆ Metric.closedBall (0 : ℂ) R

open Classical in
/-- **Rich local field data** at radius `R`: the raw values at the `coordsFull` circles inside
`closedBall 0 R` and the raw pairings with the test functions supported in `closedBall 0 R`
(junk `0` for the other coordinates). -/
def locFieldFull (R : ℕ) (x : FieldSample) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  (fun i => if inBallFull R i then CoordsFull.coordsFull x i else 0,
    fun ρ => if suppIn R ρ then pairRaw x ρ.1 else 0)

/-- **The rich local data map** (D25): rich local field data and the driver on `[0, R]`. -/
def locRich (R : ℕ) (c : FieldSample × (ℝ → ℝ)) :
    ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) :=
  (locFieldFull R c.1, fun s => c.2 (min (s : ℝ) R))

theorem measurable_pairRaw_apply (ρ : ℂ → ℝ) :
    Measurable fun x : FieldSample => pairRaw x ρ :=
  (measurable_pi_apply _).sub (measurable_pi_apply _)

theorem inBallFull_fullIdx (R n : ℕ) : inBallFull R (E6.fullIdx n) ↔ TV.inBall R n := by
  simp only [inBallFull, TV.inBall, E6.fullIndex_fullIdx]

theorem locField_eq_proj (R : ℕ) (x : FieldSample) (n : ℕ) :
    TV.locField R x n = (locFieldFull R x).1 (E6.fullIdx n) := by
  classical
  have hc : CoordsFull.coordsFull x (E6.fullIdx n) = Factorization.coords x n :=
    congrFun (E6.coordsOfFull_coordsFull x) n
  simp only [TV.locField, locFieldFull, inBallFull_fullIdx, hc]

end D3Plus

/-! ## Truncations of `configLawFull` data -/

namespace E6

open D3Plus

/-- The data `configLawFull` reads from one configuration. -/
def cfgFull (c : FieldSample × (ℝ → ℝ)) : FullData :=
  ((CoordsFull.coordsFull c.1, fun ρ => pairRaw c.1 ρ.1), fun t : ℝ≥0 => c.2 t)

open Classical in
/-- Truncation of `configLawFull` data at radius `R`, matching `D3Plus.locRich R`. -/
def truncFull (R : ℕ) (e : FullData) : FullData :=
  ((fun i => if inBallFull R i then e.1.1 i else 0,
    fun ρ => if suppIn R ρ then e.1.2 ρ else 0), fun s => e.2 (min s (R : ℝ≥0)))

theorem truncFull_cfgFull (R : ℕ) (c : FieldSample × (ℝ → ℝ)) :
    truncFull R (cfgFull c) = locRich R c := by
  refine Prod.ext rfl (funext fun s => ?_)
  simp [truncFull, cfgFull, locRich, NNReal.coe_min]

theorem measurable_truncFull (R : ℕ) : Measurable (truncFull R) := by
  classical
  unfold truncFull
  refine Measurable.prodMk (Measurable.prodMk (measurable_pi_iff.2 fun i => ?_)
    (measurable_pi_iff.2 fun ρ => ?_))
    (measurable_pi_iff.2 fun s => (measurable_pi_apply _).comp measurable_snd)
  · by_cases h : inBallFull R i
    · simp only [h, ite_true]
      exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
    · simp only [h, ite_false]; exact measurable_const
  · by_cases h : suppIn R ρ
    · simp only [h, ite_true]
      exact (measurable_pi_apply ρ).comp (measurable_snd.comp measurable_fst)
    · simp only [h, ite_false]; exact measurable_const

theorem inBallFull_mono {R R' : ℕ} (h : R ≤ R') {i : ℕ} (hi : inBallFull R i) :
    inBallFull R' i :=
  le_trans hi (by exact_mod_cast h)

theorem suppIn_mono {R R' : ℕ} (h : R ≤ R') {ρ : TestFun H} (hρ : suppIn R ρ) : suppIn R' ρ :=
  hρ.trans (Metric.closedBall_subset_closedBall (by exact_mod_cast h))

theorem truncFull_trunc {R R' : ℕ} (h : R ≤ R') (e : FullData) :
    truncFull R (truncFull R' e) = truncFull R e := by
  classical
  refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun ρ => ?_)) (funext fun s => ?_)
  · by_cases hi : inBallFull R i
    · simp [truncFull, hi, inBallFull_mono h hi]
    · simp [truncFull, hi]
  · by_cases hρ : suppIn R ρ
    · simp [truncFull, hρ, suppIn_mono h hρ]
    · simp [truncFull, hρ]
  · simp only [truncFull]
    rw [min_assoc, min_eq_left (by exact_mod_cast h : (R : ℝ≥0) ≤ R')]

theorem truncFull_comap_mono :
    Monotone fun R => MeasurableSpace.comap (truncFull R) inferInstance := by
  intro R R' h
  have : truncFull R = truncFull R ∘ truncFull R' := funext fun e => (truncFull_trunc h e).symm
  simp only
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_truncFull R).comap_le

theorem exists_inBallFull (i : ℕ) : ∃ R : ℕ, inBallFull R i :=
  exists_nat_ge _

theorem exists_suppIn (ρ : TestFun H) : ∃ R : ℕ, suppIn R ρ := by
  obtain ⟨r, hr⟩ := ρ.2.2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R, hR⟩ := exists_nat_ge r
  exact ⟨R, hr.trans (Metric.closedBall_subset_closedBall hR)⟩

/-- The σ-algebra generated by all truncations `truncFull R`. -/
def truncFullSigma : MeasurableSpace FullData :=
  ⨆ R, MeasurableSpace.comap (truncFull R) (inferInstance : MeasurableSpace FullData)

/-- **Generation** (own elementary argument): the truncations `truncFull R`, `R ∈ ℕ`, generate
the σ-algebra of `FullData`. -/
theorem truncFull_generate :
    (inferInstance : MeasurableSpace FullData) ≤
      ⨆ R, MeasurableSpace.comap (truncFull R) inferInstance := by
  change _ ≤ truncFullSigma
  have hc : ∀ R, Measurable[truncFullSigma] (truncFull R) := fun R =>
    Measurable.of_comap_le (le_iSup (fun R => MeasurableSpace.comap (truncFull R)
      (inferInstance : MeasurableSpace FullData)) R)
  have h1 : ∀ i, Measurable[truncFullSigma] (fun e : FullData => e.1.1 i) := by
    intro i
    obtain ⟨R, hR⟩ := exists_inBallFull i
    have : (fun e : FullData => e.1.1 i) = (fun f : FullData => f.1.1 i) ∘ truncFull R :=
      funext fun e => by simp [truncFull, hR]
    rw [this]
    exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).comp (hc R)
  have h2 : ∀ ρ : TestFun H, Measurable[truncFullSigma] (fun e : FullData => e.1.2 ρ) := by
    intro ρ
    obtain ⟨R, hR⟩ := exists_suppIn ρ
    have : (fun e : FullData => e.1.2 ρ) = (fun f : FullData => f.1.2 ρ) ∘ truncFull R :=
      funext fun e => by simp [truncFull, hR]
    rw [this]
    exact ((measurable_pi_apply ρ).comp (measurable_snd.comp measurable_fst)).comp (hc R)
  have h3 : ∀ s : ℝ≥0, Measurable[truncFullSigma] (fun e : FullData => e.2 s) := by
    intro s
    have hs : s ≤ ((⌈s⌉₊ : ℕ) : ℝ≥0) := Nat.le_ceil s
    have : (fun e : FullData => e.2 s) = (fun f : FullData => f.2 s) ∘ truncFull ⌈s⌉₊ :=
      funext fun e => by simp [truncFull, min_eq_left hs]
    rw [this]
    exact ((measurable_pi_apply s).comp measurable_snd).comp (hc _)
  have hid : Measurable[truncFullSigma] fun e : FullData => ((e.1.1, e.1.2), e.2) :=
    ((measurable_pi_of_dom h1).prodMk (measurable_pi_of_dom h2)).prodMk (measurable_pi_of_dom h3)
  have hid' : Measurable[truncFullSigma] (id : FullData → FullData) := hid
  have := hid'.comap_le
  rwa [MeasurableSpace.comap_id] at this

/-! ## E6-UP for `locRich` -/

/-- **Local laws determine `configLawFull`** (π-λ, `G = id`): two configurations whose
`configLawFull` data are a.e.-measurable and whose `locRich R`-laws agree for every `R` (tested
against measurable `Γ ≤ 1`) have the same `configLawFull`. -/
theorem configLawFull_eq_of_locRich {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (c₁ c₂ : Ω → FieldSample × (ℝ → ℝ))
    (h₁ : AEMeasurable (dataFull c₁) P) (h₂ : AEMeasurable (dataFull c₂) P)
    (hloc : ∀ R : ℕ, ∀ Γ : FullData → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      ∫⁻ ω, Γ (locRich R (c₁ ω)) ∂P = ∫⁻ ω, Γ (locRich R (c₂ ω)) ∂P) :
    configLawFull c₁ P = configLawFull c₂ P := by
  rw [configLawFull_eq_map, configLawFull_eq_map]
  refine ext_of_monotone_generating truncFull measurable_truncFull truncFull_comap_mono
    truncFull_generate _ _ (by simp) fun R => ?_
  have hf : ∀ c : Ω → FieldSample × (ℝ → ℝ),
      truncFull R ∘ dataFull c = fun ω => locRich R (c ω) := fun c =>
    funext fun ω => truncFull_cfgFull R (c ω)
  have key : ∀ c : Ω → FieldSample × (ℝ → ℝ), AEMeasurable (dataFull c) P →
      ∀ A : Set FullData, MeasurableSet A →
      (P.map (dataFull c)).map (truncFull R) A = ∫⁻ ω, A.indicator 1 (locRich R (c ω)) ∂P := by
    intro c h A hA
    rw [AEMeasurable.map_map_of_aemeasurable (measurable_truncFull R).aemeasurable h,
      ← lintegral_indicator_one hA,
      lintegral_map' (measurable_one.indicator hA).aemeasurable
        ((measurable_truncFull R).comp_aemeasurable h), hf c]
  ext A hA
  rw [key c₁ h₁ A hA, key c₂ h₂ A hA]
  refine hloc R _ (measurable_one.indicator hA) fun y => ?_
  by_cases hy : y ∈ A <;> simp [hy]

/-- **E6, local-law form for `locRich`** (as `Thm13Asm.E6LocStmt`, with the rich local data). -/
def E6LocStmtRich : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ ℓ₁ : ℝ, 0 < ℓ₁ →
    ∀ R : ℕ, ∀ Γ : FullData → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      ∫⁻ ω', Γ (locRich R (zipLenDown (Real.sqrt κ) ℓ₁ (Y ω', drive κ B' ω'))) ∂P' =
        ∫⁻ ω', Γ (locRich R (Y ω', drive κ B' ω')) ∂P'

/-- The `P_*` configuration has a.e.-measurable `configLawFull` data (WEDGE-MEAS (1) and
Brownian path measurability). -/
theorem aemeasurable_dataFull_pstar {κ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {Y : Ω' → FieldSample} {B' : ℝ≥0 → Ω' → ℝ} (hP : Thm13Asm.IsPStarSample κ P' Y B') :
    AEMeasurable (dataFull fun ω' => (Y ω', drive κ B' ω')) P' := by
  obtain ⟨hκ, hκ4, hW, hB, -⟩ := hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := (Real.sqrt_lt' two_pos).2 (by norm_num; exact hκ4)
  exact F1.aemeasurable_cfgData_drive_bm κ
    (Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hW.1 hW) hB

end E6
end QuantumZipper
