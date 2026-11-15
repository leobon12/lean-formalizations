/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3CalcMain
import InteractingSLE.Spec.ZhanGT4.A1EightSeedGlue

/-!
# Zhan's A.1, G3: source records, columns and protected rectangles with mixed marks

Packet PROVE-A1-G3CALC (R48). A1-SEEDFIELD's record layer (`IsProtectedPair`, `IsSourceRecord`, `IsSourceColumn`,
`IsSourceColumn.calculus`, `exists_abs_normEll_le_uniform_right`) and A1-EIGHTSEED's `isRectField_of_sourceR`, for
records whose marks are seeds or ordinary marks (`IsMarkCoordinate`) in the extended interval
`[V_lo(t), g_t(q) + W_t]`. The column martingale is the new `seeded_source_calculus_ext`.

## Main results

* `exists_abs_normEll_le_ext_of_remote_scale`, **`exists_abs_normEll_le_uniform_ext`**: (D9) for mixed records, one
  constant uniform in both paths, the frozen height, the horizon and the own time;
* **`IsProtectedPairG`**, **`IsSourceRecordG`**, **`IsSourceColumnG`**, **`IsSourceColumnG.calculus`**;
* **`isRectField_of_sourceG`**: A1-PATCH's `IsRectField` of the seeded height field from mixed source records.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4.A1G3Calc

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

open InteractingSLE.ZhanGT4 A1Patch A1SeedField A1EightSeed

/-- A22's `exists_abs_normEll_le_right_of_remote_scale` on the extended interval. -/
theorem exists_abs_normEll_le_ext_of_remote_scale {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {q d : ℝ} (hq : 0 < q) (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (hseg : ∀ a ∈ H₂, ∀ y : ℝ, 0 < y → y ≤ q → 2 * δ ≤ ‖a - y‖)
    (Tm Lrem κ : ℝ) {n : ℕ} (rr : Fin n → ℝ) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ (s : SeedData n) (W₂ Vlo Vhi : ℝ → ℝ) (T t₂ : ℝ),
        OwnData s.W (fwdHull W₂ t₂) s.φ T s.a s.W' →
        s.φ = (fun z => fwdMap W₂ t₂ z + W₂ t₂) →
        s.κ = κ → s.r = rr → Continuous W₂ → 0 < t₂ → t₂ ≤ Tm →
        ((s.W 0 : ℝ) : ℂ) ∈ closure H₁ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ →
        q < W₂ 0 →
        fwdHull s.W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate s.W Vlo T → IsSeedCoordinate s.W Vhi T →
        (∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ uIcc (Vlo t) ((fwdMap s.W t q).re + s.W t)) →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ uIcc (Vlo t) ((fwdMap s.W t q).re + s.W t)) →
        (∀ t ∈ Icc (0 : ℝ) T, s.RemoteScale t Lrem) →
        ∀ t ∈ Icc (0 : ℝ) T, |s.normEll t| ≤ coefTot κ rr * L := by
  obtain ⟨r, L₀, hr, hL₀, hb⟩ :=
    exists_ext_interval_own_bounds_right hH₁ hH₂ hδ hsepδ hq hd hqH hseg Tm
  refine ⟨r, max L₀ Lrem, hr, hL₀.trans (le_max_left _ _), ?_⟩
  intro s W₂ Vlo Vhi T t₂ h hφ hκ hrr hW₂ ht₂ ht₂m hW₁H hW₂H hqW hK₁ hK₂
    hlo hhi hWI hVI hremote t ht
  have h' : OwnData s.W (fwdHull W₂ t₂)
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) T s.a s.W' := by rwa [← hφ]
  have hbound := hb s.W W₂ Vlo Vhi T t₂ s.a s.W' h' hW₂ ht₂
    hW₁H hW₂H hqW ht₂m hK₁ hK₂ hlo hhi t ht
  have hdiff : ∀ x ∈ uIcc (Vlo t) ((fwdMap s.W t q).re + s.W t),
      DifferentiableAt ℂ (ownExt s.W s.W' s.a s.φ t) x := by
    intro x hx
    have hcl := (hbound x hx).1
    have hf := (h.ownExt_props ht hcl).1
    exact hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
  rw [← hκ, ← hrr]
  apply s.abs_normEll_le_of_interval_scale (hL₀.trans (le_max_left _ _))
    (le_max_left _ _) (convex_uIcc _ _) ?_ ?_ ?_ (hWI t ht) (hVI t ht)
    (FrzData.inScale_mono (hremote t ht).A21 (le_max_right _ _))
    ((hremote t ht).logF.trans (le_max_right _ _))
    (fun m => FrzData.inScale_mono ((hremote t ht).mark m) (le_max_right _ _))
    (FrzData.inScale_mono (hremote t ht).driver (le_max_right _ _))
  · intro x hx
    exact (hdiff x hx).hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt
  · intro x hx
    change deriv (fun y : ℝ => (ownExt s.W s.W' s.a s.φ t y).re) x ∈
      Icc (Real.exp (-L₀)) (Real.exp L₀)
    rw [hφ]
    exact (hbound x hx).2
  · intro x hx
    exact (s.deriv_F_zero (hdiff x hx)).symm

/-- **The seeded logarithm of mixed records is bounded uniformly in both paths** (A1-SEEDFIELD's
`exists_abs_normEll_le_uniform_right` on the extended interval `[V_lo(t), g_t(q) + W_t]`). -/
theorem exists_abs_normEll_le_uniform_ext {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hpH₂ : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (hseg : ∀ a ∈ H₂, ∀ y : ℝ, 0 < y → y ≤ q → 2 * δ ≤ ‖a - y‖) (Tm κ : ℝ) {n : ℕ} (rr : Fin n → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (W W₂ a W' Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ) (T t₂ : ℝ),
        OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
        Continuous W₂ → W₂ 0 = p → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
        fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
        (∀ t ∈ Icc (0 : ℝ) T, W t ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t)) →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ m, V m t ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t)) →
        ∀ t ∈ Icc (0 : ℝ) T,
          |(SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p V).normEll t| ≤ K := by
  obtain ⟨Lrem, -, hrem⟩ := exists_ext_remoteScale_right hH₁ hH₂ hδ hsep hpH₂ hq hqp hd hqH hseg Tm
  obtain ⟨r, L, -, hL, hb⟩ :=
    exists_abs_normEll_le_ext_of_remote_scale hH₁ hH₂ hδ hsep hq hd hqH hseg Tm Lrem κ rr
  have hcoef : 0 ≤ coefTot κ rr := by
    unfold coefTot
    have h1 : 0 ≤ ∑ m, (|rr m| + |dualGamma κ (rr m)| + |κ / 4 * rr m|) :=
      Finset.sum_nonneg fun m _ => by positivity
    have h2 : 0 ≤ pairSum (fun m k => |dualDelta κ (rr m) (rr k)|) :=
      pairSum_nonneg fun m k => abs_nonneg _
    positivity
  refine ⟨coefTot κ rr * L, mul_nonneg hcoef hL, ?_⟩
  intro W W₂ a W' Vlo Vhi V T t₂ h hW₂ hW₂0 ht₂ ht₂m hTm hK₁ hK₂ hlo hhi hWI hVI t ht
  have hW0H : ((W 0 : ℝ) : ℂ) ∈ closure H₁ := closure_mono hK₁ (start_mem_closure_fwdHull h.cont h.pos)
  have hW₂H : ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ := by rw [hW₂0]; exact hpH₂
  have hqW : q < W₂ 0 := by rw [hW₂0]; exact hqp
  have hremote := hrem κ rr W W₂ a W' Vlo Vhi V T t₂ h hW₂ hW₂0 ht₂ ht₂m hTm hK₁ hK₂ hlo hhi hWI hVI
  exact hb (SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p V) W₂ Vlo Vhi T t₂ h rfl
    rfl rfl hW₂ ht₂ ht₂m hW0H hW₂H hqW hK₁ hK₂ hlo hhi hWI hVI hremote t ht

/-! ### Protected pairs, source records and columns with mixed marks -/

/-- **The enclosure data of a G3 rectangle**: A1-SEEDFIELD's `IsProtectedPair` (enclosures `H₁ ∋ 0`, `H₂ ∋ p`,
`2δ`-separated, protected point `q ∈ (0, p)`) and the real segment `(0, q]` `2δ`-far from `H₂` (it carries the ordinary
marks of the growing curve). -/
structure IsProtectedPairG (H₁ H₂ : Set ℂ) (δ p q d : ℝ) : Prop where
  pair : IsProtectedPair H₁ H₂ δ p q d
  seg : ∀ a ∈ H₂, ∀ y : ℝ, 0 < y → y ≤ q → 2 * δ ≤ ‖a - y‖

variable {n : ℕ}

/-- **A seeded record with seeds and ordinary marks, built from the source and protected by the enclosures** up to
the own horizon `T`: A1-SEEDFIELD's `IsSourceRecord` with the marks arbitrary mark coordinates (`IsMarkCoordinate`)
and the driver and the marks in the extended interval `[V_lo(t), g_t(q) + W_t]` instead of the seed interval. -/
structure IsSourceRecordG (H₁ H₂ : Set ℂ) (p q Tm κ : ℝ) (rr : Fin n → ℝ) (W₂ : ℝ → ℝ) (t₂ : ℝ) (s : SeedData n)
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
  drv : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ uIcc (Vlo t) ((fwdMap s.W t q).re + s.W t)
  marks : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ uIcc (Vlo t) ((fwdMap s.W t q).re + s.W t)
  mark : ∀ m, IsMarkCoordinate s.W (s.V m) T
  inj : ∀ t ∈ Ioc (0 : ℝ) T, Function.Injective fun m => s.V m t

namespace IsSourceRecordG

variable {H₁ H₂ : Set ℂ} {p q Tm κ : ℝ} {rr : Fin n → ℝ} {W₂ : ℝ → ℝ} {t₂ : ℝ} {s : SeedData n}
  {Vlo Vhi : ℝ → ℝ} {T : ℝ}

theorem φ_eq (h : IsSourceRecordG H₁ H₂ p q Tm κ rr W₂ t₂ s Vlo Vhi T) :
    s.φ = fun z => fwdMap W₂ t₂ z + W₂ t₂ :=
  congrArg SeedData.φ h.source

/-- **The uniform bound of a mixed source record**: with the constant `K` of `exists_abs_normEll_le_uniform_ext`,
`|normEll t| ≤ K` for every own time `t ≤ T`. -/
theorem abs_normEll_le (h : IsSourceRecordG H₁ H₂ p q Tm κ rr W₂ t₂ s Vlo Vhi T) {K : ℝ}
    (hK : ∀ (W W₂ a W' Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ) (T t₂ : ℝ),
        OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
        Continuous W₂ → W₂ 0 = p → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
        fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
        (∀ t ∈ Icc (0 : ℝ) T, W t ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t)) →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ m, V m t ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t)) →
        ∀ t ∈ Icc (0 : ℝ) T,
          |(SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p V).normEll t| ≤ K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : |s.normEll t| ≤ K := by
  have hown : OwnData s.W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T s.a s.W' := by
    rw [← h.φ_eq]; exact h.own
  have hb := hK s.W W₂ s.a s.W' Vlo Vhi s.V T t₂ hown h.contW₂ h.zeroW₂ h.pos₂ h.le₂ h.le₁ h.sub₁ h.sub₂ h.lo h.hi
    h.drv h.marks t ht
  rwa [← h.source] at hb

end IsSourceRecordG

section Column

variable {X : Type*} {mX : MeasurableSpace X}

/-- **The source data of one column with mixed marks** (A1-SEEDFIELD's `IsSourceColumn` with `IsSourceRecordG`):
these are exactly the hypotheses of `seeded_source_calculus_ext`. -/
def IsSourceColumnG (H₁ H₂ : Set ℂ) (p q Tm κ : ℝ) (rr : Fin n → ℝ) (𝓕 : Filtration ℝ≥0 mX) (P : Measure X)
    (t₂ : ℝ) (sdata : X → SeedData n) (T : X → ℝ≥0) : Prop :=
  ∃ (W₂ : ℝ → ℝ) (Vlo Vhi : X → ℝ → ℝ) (B D : ℝ≥0 → X → ℝ),
    (∀ x, IsSourceRecordG H₁ H₂ p q Tm κ rr W₂ t₂ (sdata x) (Vlo x) (Vhi x) (T x)) ∧
    IsStoppingTime 𝓕 (fun x => (T x : WithTop ℝ≥0)) ∧
    IsFilteredBrownianReal 𝓕 B P ∧ (∀ x, Continuous (B · x)) ∧
    (∀ u, Measurable[𝓕 u] (D u)) ∧ (∀ x, Continuous (D · x)) ∧
    (∀ x, (sdata x).W = driftDriver (Real.sqrt κ) B D x) ∧
    (∀ x t, t ∈ Ioc (0 : ℝ) (T x) →
      HasDerivWithinAt (fun u : ℝ => D u.toNNReal x) ((sdata x).drift t) (Ioc 0 (T x)) t) ∧
    (∀ (u : ℝ≥0) m, Measurable[𝓕 u] ({x | u ≤ T x}.indicator fun x => (sdata x).V m u)) ∧
    (∀ u : ℝ≥0, Measurable[𝓕 u] ({x | u ≤ T x}.indicator fun x => (sdata x).V₀ u)) ∧
    (∀ u : ℝ≥0, Measurable[𝓕 u] ({x | u ≤ T x}.indicator fun x => (sdata x).G₀ u))

namespace IsSourceColumnG

variable {H₁ H₂ : Set ℂ} {δ p q d Tm κ : ℝ} {rr : Fin n → ℝ} {𝓕 : Filtration ℝ≥0 mX} {P : Measure X}
  [IsProbabilityMeasure P] {t₂ : ℝ} {sdata : X → SeedData n} {T : X → ℝ≥0}

/-- **The column martingale with mixed marks** (§A.1.3, (D8)): the stopped seeded density of a mixed source column is
a continuous `𝓕`-martingale (`seeded_source_calculus_ext`). -/
theorem calculus (hpp : IsProtectedPairG H₁ H₂ δ p q d) (hκ : 0 < κ)
    (h : IsSourceColumnG H₁ H₂ p q Tm κ rr 𝓕 P t₂ sdata T) :
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
  have hsrc := seeded_source_calculus_ext hpp.pair.hull₁ hpp.pair.hull₂ hpp.pair.sep_pos hpp.pair.sep
    hpp.pair.src hpp.pair.prot_pos hpp.pair.prot_lt hpp.pair.rad_pos hpp.pair.prot hpp.seg 𝓕 hκ rr
    r₀.contW₂ r₀.zeroW₂ r₀.pos₂ r₀.le₂ r₀.sub₂ hB hBc hDm hDc (sdata := sdata) (Vlo := Vlo) (Vhi := Vhi) (T := T)
    (fun x => (hrec x).source) hdW hT hTm (fun x => (hrec x).own) (fun x => (hrec x).sub₁) (fun x => (hrec x).lo)
    (fun x => (hrec x).hi) (fun x => (hrec x).drv) (fun x => (hrec x).marks) (fun x => (hrec x).mark)
    (fun x => (hrec x).inj) hD hVm hV₀m hG₀m
  exact ⟨hsrc.2.1, hsrc.2.2.1⟩

end IsSourceColumnG

end Column

section Rect

variable {X Y : Type*} [mX' : MeasurableSpace X] [mY : MeasurableSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
  [IsProbabilityMeasure P₁] {𝓕₁ : Filtration ℝ≥0 mX'} {𝓕₂ : Filtration ℝ≥0 mY}

/-- **A protected rectangle of the seeded height field from mixed source records** (A1-EIGHTSEED's
`isRectField_of_sourceR` with `IsProtectedPairG`, `IsSourceColumnG` and `IsSourceRecordG`). -/
theorem isRectField_of_sourceG {d : ℝ → X × Y → SeedData n} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0}
    {H₁ H₂ : Set ℂ} {δ p q dd Tm κ : ℝ} {rr : Fin n → ℝ} (hpp : IsProtectedPairG H₁ H₂ δ p q dd) (hκ : 0 < κ)
    (h₁ : IsStoppingTime 𝓕₁ fun x => (S₁ x : WithTop ℝ≥0)) (h₂ : IsStoppingTime 𝓕₂ fun y => (S₂ y : WithTop ℝ≥0))
    (hU : ∃ U : ℝ≥0, (∀ x, S₁ x ≤ U) ∧ ∀ y, S₂ y ≤ U)
    (hcol : ∀ y, 0 < (S₂ y : ℝ) →
      IsSourceColumnG H₁ H₂ p q Tm κ rr 𝓕₁ P₁ (S₂ y) (fun x => d (S₂ y) (x, y)) S₁)
    (hrec : ∀ x y (t : ℝ), 0 < t → t ≤ S₂ y →
      ∃ (W₂ Vlo Vhi : ℝ → ℝ), IsSourceRecordG H₁ H₂ p q Tm κ rr W₂ t (d t (x, y)) Vlo Vhi (S₁ x))
    (hzero : ∀ x y (s : ℝ), 0 ≤ s → s ≤ S₁ x → (d 0 (x, y)).normEll s = (d 0 (x, y)).normEll 0)
    (hrow : ∀ x (a : ℝ), 0 ≤ a → a ≤ S₁ x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField d (x, y) a (min (t : ℝ) (S₂ y))) 𝓕₂ P₂)
    (hrowc : ∀ x y (a : ℝ), 0 ≤ a → a ≤ S₁ x →
      Continuous fun t : ℝ≥0 => seedHeightField d (x, y) a (min (t : ℝ) (S₂ y))) :
    IsRectField P₁ P₂ 𝓕₁ 𝓕₂ S₁ S₂ (seedHeightField d) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_normEll_le_uniform_ext hpp.pair.hull₁ hpp.pair.hull₂ hpp.pair.sep_pos
    hpp.pair.sep hpp.pair.src hpp.pair.prot_pos hpp.pair.prot_lt hpp.pair.rad_pos hpp.pair.prot hpp.seg Tm κ rr
  have hcol' : ∀ y, Martingale (seedDensityProcess (fun x => d (S₂ y) (x, y)) S₁) 𝓕₁ P₁ ∧
      (∀ x, Continuous (seedDensityProcess (fun x => d (S₂ y) (x, y)) S₁ · x)) := by
    intro y
    rcases (S₂ y).coe_nonneg.eq_or_lt with h0 | hpos
    · rw [← h0]
      exact martingale_seedDensityProcess_of_identityOn fun x s hs hsS => hzero x y s hs hsS
    · exact (hcol y hpos).calculus hpp hκ
  refine isRectField_seedHeightField h₁ h₂ hU ?_ (fun y => (hcol' y).1) (fun x y => (hcol' y).2 x) hrow hrowc
  refine seedHeightField_bound_of_pos_zero hK0 (fun x y s t hs hsS ht htS => ?_) hzero
  obtain ⟨W₂, Vlo, Vhi, hr⟩ := hrec x y t ht htS
  exact ⟨hr.abs_normEll_le hK ⟨hs, hsS⟩, hr.abs_normEll_le hK ⟨le_rfl, (S₁ x).coe_nonneg⟩⟩

end Rect

end InteractingSLE.ZhanGT4.A1G3Calc
