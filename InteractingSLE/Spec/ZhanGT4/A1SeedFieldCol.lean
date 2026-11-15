/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1SeedFieldBound

/-!
# Zhan's A.1 (R80): a protected rectangle of the seeded field from the source records

Packet PROVE-A1-SEEDFIELD. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`ig1_followup_proofs.txt` L300–L407) and
follow-up 4 §2.5 items 1–2, 4 (`ig1_followup4_audited.txt` L739–L788: "each coordinate section of `M` is a true bounded
martingale … the staircase density (D11)–(D12) … uses only coordinate martingales and their axis values").

PROVE-A1-PATCH reduced A.1's finite patches to `A1Patch.IsRectField` for the seeded height field
`N = seedHeightField d` (`A1Patch.isRectField_seedHeightField`). Here every field of `IsRectField` except the row
martingale (the opposite-time view, A22's `SeedNormalizedTView`) is derived from the **source records** of the seeded
data, i.e. from the hypotheses of A22's `seeded_source_calculus_right`:

* `IsProtectedPair`: the deterministic enclosure data of one rectangle (two compact `ℍ`-hulls, separated, with a
  protected point between the sources);
* `IsSourceRecord`: one seeded record built from the source (`SeedData.fromSource`) with the growing curve's own-time
  data, the frozen path and the seed coordinates, protected by the enclosures up to the horizon;
* `IsSourceColumn`: the source records of a whole column (the frozen sample fixed) together with the stochastic data
  of the growing curve (Brownian motion, adapted continuous drift with the force-point rate, adapted force
  coordinates).

## Main results

* `IsSourceRecord.abs_normEll_le`: the uniform bound (`exists_abs_normEll_le_uniform_right`) for a source record;
* **`IsSourceColumn.martingale`**, `IsSourceColumn.continuous`: the column martingale and its continuity (A22's
  `seeded_source_calculus_right`);
* `martingale_seedDensityProcess_of_identity`: the column at frozen height zero (identity chart) is constant;
* **`isRectField_of_source`**: `IsRectField` of the seeded height field on one rectangle from the source columns at the
  rectangle's frozen heights, the source records at all lower heights (for (D9)), the identity chart at height zero,
  and the row martingales.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4.A1SeedField

open QuantumZipper (H fwdMap fwdHull)
open A1Patch

/-- **The enclosure data of a protected rectangle** (§A.1.3): compact `ℍ`-hulls `H₁` (around the growing curve's
source `0`) and `H₂` (around the other source `p`), `2δ`-separated, with a protected point `q ∈ (0, p)` whose
`2d`-ball avoids both. These are the deterministic hypotheses of `seeded_source_calculus_right`. -/
structure IsProtectedPair (H₁ H₂ : Set ℂ) (δ p q d : ℝ) : Prop where
  hull₁ : IsHPHull H₁
  hull₂ : IsHPHull H₂
  sep_pos : 0 < δ
  sep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖
  src : (p : ℂ) ∈ closure H₂
  prot_pos : 0 < q
  prot_lt : q < p
  rad_pos : 0 < d
  prot : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)

variable {n : ℕ}

/-- **A seeded record built from the source and protected by the enclosures** up to the own horizon `T`: the record is
`SeedData.fromSource` of its own driver, image data and seed coordinates, in the frozen chart of the path `W₂` (from
`p`) at the height `0 < t₂ ≤ Tm`, with `OwnData` up to `T ≤ Tm`, both hulls inside their enclosures, the driver and the
seed coordinates between the two outermost seeds `Vlo`, `Vhi`, every mark an integrated seed coordinate, and distinct
seeds at positive times. -/
structure IsSourceRecord (H₁ H₂ : Set ℂ) (p Tm κ : ℝ) (rr : Fin n → ℝ) (W₂ : ℝ → ℝ) (t₂ : ℝ) (s : SeedData n)
    (Vlo Vhi : ℝ → ℝ) (T : ℝ) : Prop where
  source : s = SeedData.fromSource s.W s.W' s.a (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p s.V
  own : OwnData s.W (fwdHull W₂ t₂) s.φ T s.a s.W'
  contW₂ : Continuous W₂
  zeroW₂ : W₂ 0 = p
  pos₂ : 0 < t₂
  le₂ : t₂ ≤ Tm
  le₁ : T ≤ Tm
  sub₁ : fwdHull s.W T ⊆ H₁
  sub₂ : fwdHull W₂ t₂ ⊆ H₂
  lo : IsSeedCoordinate s.W Vlo T
  hi : IsSeedCoordinate s.W Vhi T
  drv : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ uIcc (Vlo t) (Vhi t)
  marks : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ uIcc (Vlo t) (Vhi t)
  seed : ∀ m, IsSeedCoordinate s.W (s.V m) T
  inj : ∀ t ∈ Ioc (0 : ℝ) T, Function.Injective fun m => s.V m t

namespace IsSourceRecord

variable {H₁ H₂ : Set ℂ} {p Tm κ : ℝ} {rr : Fin n → ℝ} {W₂ : ℝ → ℝ} {t₂ : ℝ} {s : SeedData n} {Vlo Vhi : ℝ → ℝ}
  {T : ℝ}

theorem φ_eq (h : IsSourceRecord H₁ H₂ p Tm κ rr W₂ t₂ s Vlo Vhi T) :
    s.φ = fun z => fwdMap W₂ t₂ z + W₂ t₂ :=
  congrArg SeedData.φ h.source

/-- **The uniform bound of a source record**: with the constant `K` of `exists_abs_normEll_le_uniform_right` (chosen
before every path), `|normEll t| ≤ K` for every own time `t ≤ T`. -/
theorem abs_normEll_le (h : IsSourceRecord H₁ H₂ p Tm κ rr W₂ t₂ s Vlo Vhi T) {K : ℝ}
    (hK : ∀ (W W₂ a W' Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ) (T t₂ : ℝ),
        OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
        Continuous W₂ → W₂ 0 = p → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
        fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
        (∀ t ∈ Icc (0 : ℝ) T, W t ∈ uIcc (Vlo t) (Vhi t)) →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ m, V m t ∈ uIcc (Vlo t) (Vhi t)) →
        ∀ t ∈ Icc (0 : ℝ) T,
          |(SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p V).normEll t| ≤ K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : |s.normEll t| ≤ K := by
  have hown : OwnData s.W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T s.a s.W' := by
    rw [← h.φ_eq]; exact h.own
  have hb := hK s.W W₂ s.a s.W' Vlo Vhi s.V T t₂ hown h.contW₂ h.zeroW₂ h.pos₂ h.le₂ h.le₁ h.sub₁ h.sub₂ h.lo h.hi
    h.drv h.marks t ht
  rwa [← h.source] at hb

end IsSourceRecord

section Column

variable {X : Type*} {mX : MeasurableSpace X}

/-- **The source data of one column** (the frozen sample fixed, frozen height `t₂ > 0`): every record
`sdata x` of the growing curve is a source record up to its horizon `T x` (a bounded stopping time of `𝓕`), and the
growing driver is `√κ B + D` with `B` an `𝓕`-Brownian motion, `D` adapted and continuous with derivative the
force-point drift, and the force coordinates (the seeds, the other source and its derivative) adapted before the
horizon. These are exactly the hypotheses of A22's `seeded_source_calculus_right`. -/
def IsSourceColumn (H₁ H₂ : Set ℂ) (p Tm κ : ℝ) (rr : Fin n → ℝ) (𝓕 : Filtration ℝ≥0 mX) (P : Measure X)
    (t₂ : ℝ) (sdata : X → SeedData n) (T : X → ℝ≥0) : Prop :=
  ∃ (W₂ : ℝ → ℝ) (Vlo Vhi : X → ℝ → ℝ) (B D : ℝ≥0 → X → ℝ),
    (∀ x, IsSourceRecord H₁ H₂ p Tm κ rr W₂ t₂ (sdata x) (Vlo x) (Vhi x) (T x)) ∧
    IsStoppingTime 𝓕 (fun x => (T x : WithTop ℝ≥0)) ∧
    IsFilteredBrownianReal 𝓕 B P ∧ (∀ x, Continuous (B · x)) ∧
    (∀ u, Measurable[𝓕 u] (D u)) ∧ (∀ x, Continuous (D · x)) ∧
    (∀ x, (sdata x).W = driftDriver (Real.sqrt κ) B D x) ∧
    (∀ x t, t ∈ Ioc (0 : ℝ) (T x) →
      HasDerivWithinAt (fun u : ℝ => D u.toNNReal x) ((sdata x).drift t) (Ioc 0 (T x)) t) ∧
    (∀ (u : ℝ≥0) m, Measurable[𝓕 u] ({x | u ≤ T x}.indicator fun x => (sdata x).V m u)) ∧
    (∀ u : ℝ≥0, Measurable[𝓕 u] ({x | u ≤ T x}.indicator fun x => (sdata x).V₀ u)) ∧
    (∀ u : ℝ≥0, Measurable[𝓕 u] ({x | u ≤ T x}.indicator fun x => (sdata x).G₀ u))

namespace IsSourceColumn

variable {H₁ H₂ : Set ℂ} {δ p q d Tm κ : ℝ} {rr : Fin n → ℝ} {𝓕 : Filtration ℝ≥0 mX} {P : Measure X}
  [IsProbabilityMeasure P] {t₂ : ℝ} {sdata : X → SeedData n} {T : X → ℝ≥0}

/-- **The column martingale** (§A.1.3, (D8); follow-up 4 §2.5 item 2): the stopped seeded density of a source column is
a bounded continuous `𝓕`-martingale — A22's `seeded_source_calculus_right`. -/
theorem calculus (hpp : IsProtectedPair H₁ H₂ δ p q d) (hκ : 0 < κ)
    (h : IsSourceColumn H₁ H₂ p Tm κ rr 𝓕 P t₂ sdata T) :
    Martingale (seedDensityProcess sdata T) 𝓕 P ∧ (∀ x, Continuous (seedDensityProcess sdata T · x)) := by
  obtain ⟨W₂, Vlo, Vhi, B, D, hrec, hT, hB, hBc, hDm, hDc, hdW, hD, hVm, hV₀m, hG₀m⟩ := h
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    have hE : IsEmpty X := not_nonempty_iff.1 hX
    have h1 := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h1
    exact zero_ne_one h1
  have r₀ := hrec x₀
  have hTm : ∀ x, (T x : ℝ) ≤ Tm := fun x => (hrec x).le₁
  have hsrc := seeded_source_calculus_right hpp.hull₁ hpp.hull₂ hpp.sep_pos hpp.sep
    hpp.src hpp.prot_pos hpp.prot_lt hpp.rad_pos hpp.prot 𝓕 hκ rr
    r₀.contW₂ r₀.zeroW₂ r₀.pos₂ r₀.le₂ r₀.sub₂ hB hBc hDm hDc (sdata := sdata) (Vlo := Vlo) (Vhi := Vhi) (T := T)
    (fun x => (hrec x).source) hdW hT hTm (fun x => (hrec x).own) (fun x => (hrec x).sub₁) (fun x => (hrec x).lo)
    (fun x => (hrec x).hi) (fun x => (hrec x).drv) (fun x => (hrec x).marks) (fun x => (hrec x).seed)
    (fun x => (hrec x).inj) hD hVm hV₀m hG₀m
  exact ⟨hsrc.2.1, hsrc.2.2.1⟩

end IsSourceColumn

/-- **The column at frozen height zero** (identity chart): if the normalized logarithm of every zero-height record is
constant in own time, the stopped seeded density is the constant one, a martingale. -/
theorem martingale_seedDensityProcess_of_identity {𝓕 : Filtration ℝ≥0 mX} {P : Measure X} [IsFiniteMeasure P]
    {sdata : X → SeedData n} {T : X → ℝ≥0} (h0 : ∀ x s, (sdata x).normEll s = (sdata x).normEll 0) :
    Martingale (seedDensityProcess sdata T) 𝓕 P ∧ (∀ x, Continuous (seedDensityProcess sdata T · x)) := by
  have e : seedDensityProcess sdata T = fun _ _ => (1 : ℝ) := by
    funext u x
    simp only [seedDensityProcess, h0 x, sub_self, Real.exp_zero]
  rw [e]
  exact ⟨martingale_const 𝓕 P 1, fun _ => continuous_const⟩

end Column

section Rect

variable {X Y : Type*} [mX' : MeasurableSpace X] [mY : MeasurableSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
  [IsProbabilityMeasure P₁] {𝓕₁ : Filtration ℝ≥0 mX'} {𝓕₂ : Filtration ℝ≥0 mY}

/-- **A protected rectangle of the seeded height field from the source records** (§A.1.3–A.1.4): bounded stopping
times `S₁`, `S₂`; one protected enclosure pair; at each frozen sample `y` with `S₂ y > 0` the source column at the
height `S₂ y` (column martingale), at every height `0 < t ≤ S₂ y` the source records of the growing curve up to `S₁`
(the uniform bound (D9)); the identity chart at height zero; and the row martingales (the opposite-time view, A22's
open t-view). -/
theorem isRectField_of_source {d : ℝ → X × Y → SeedData n} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0}
    {H₁ H₂ : Set ℂ} {δ p q dd Tm κ : ℝ} {rr : Fin n → ℝ} (hpp : IsProtectedPair H₁ H₂ δ p q dd) (hκ : 0 < κ)
    (h₁ : IsStoppingTime 𝓕₁ fun x => (S₁ x : WithTop ℝ≥0)) (h₂ : IsStoppingTime 𝓕₂ fun y => (S₂ y : WithTop ℝ≥0))
    (hU : ∃ U : ℝ≥0, (∀ x, S₁ x ≤ U) ∧ ∀ y, S₂ y ≤ U)
    (hcol : ∀ y, 0 < (S₂ y : ℝ) →
      IsSourceColumn H₁ H₂ p Tm κ rr 𝓕₁ P₁ (S₂ y) (fun x => d (S₂ y) (x, y)) S₁)
    (hrec : ∀ x y (t : ℝ), 0 < t → t ≤ S₂ y →
      ∃ (W₂ Vlo Vhi : ℝ → ℝ), IsSourceRecord H₁ H₂ p Tm κ rr W₂ t (d t (x, y)) Vlo Vhi (S₁ x))
    (hzero : ∀ x y s, (d 0 (x, y)).normEll s = (d 0 (x, y)).normEll 0)
    (hrow : ∀ x (a : ℝ), 0 ≤ a → a ≤ S₁ x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField d (x, y) a (min (t : ℝ) (S₂ y))) 𝓕₂ P₂)
    (hrowc : ∀ x y (a : ℝ), 0 ≤ a → a ≤ S₁ x →
      Continuous fun t : ℝ≥0 => seedHeightField d (x, y) a (min (t : ℝ) (S₂ y))) :
    IsRectField P₁ P₂ 𝓕₁ 𝓕₂ S₁ S₂ (seedHeightField d) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_normEll_le_uniform_right hpp.hull₁ hpp.hull₂ hpp.sep_pos hpp.sep hpp.src
    hpp.prot_pos hpp.prot_lt hpp.rad_pos hpp.prot Tm κ rr
  have hcol' : ∀ y, Martingale (seedDensityProcess (fun x => d (S₂ y) (x, y)) S₁) 𝓕₁ P₁ ∧
      (∀ x, Continuous (seedDensityProcess (fun x => d (S₂ y) (x, y)) S₁ · x)) := by
    intro y
    rcases (S₂ y).coe_nonneg.eq_or_lt with h0 | hpos
    · rw [← h0]
      exact martingale_seedDensityProcess_of_identity fun x s => hzero x y s
    · exact (hcol y hpos).calculus hpp hκ
  refine isRectField_seedHeightField h₁ h₂ hU ?_ (fun y => (hcol' y).1) (fun x y => (hcol' y).2 x) hrow hrowc
  refine seedHeightField_bound_of_pos_zero hK0 (fun x y s t hs hsS ht htS => ?_)
    (fun x y s _ _ => hzero x y s)
  obtain ⟨W₂, Vlo, Vhi, hr⟩ := hrec x y t ht htS
  exact ⟨hr.abs_normEll_le hK ⟨hs, hsS⟩, hr.abs_normEll_le hK ⟨le_rfl, (S₁ x).coe_nonneg⟩⟩

end Rect

end InteractingSLE.ZhanGT4.A1SeedField
