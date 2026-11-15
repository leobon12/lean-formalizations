/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformGeometry

/-!
# Uniform interval scales for the normalized seeded density

Packet PROVE-ZHAN-GT4-A22. The geometric lower derivative estimate and the
mapping-out upper bound give a deterministic derivative scale on the whole
seed interval. The normalized-density estimate then uses that scale for
derivatives and divided differences, including coincident coordinates.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H fwdMap fwdHull)

/-- Convert the enclosure estimate into uniform real derivative scales for
the reflected own-time map. The transposed image data are constructed from
the two disjoint hulls by the existing image-chain existence theorem. -/
theorem exists_seed_interval_own_bounds_right {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {q d : ℝ} (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) (Tm : ℝ) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ (W₁ W₂ Vlo Vhi : ℝ → ℝ) (T t₂ : ℝ) (a W' : ℝ → ℝ),
        OwnData W₁ (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
        Continuous W₂ → 0 < t₂ →
        ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ →
        W₁ 0 < q → q < W₂ 0 → t₂ ≤ Tm →
        fwdHull W₁ T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W₁ Vlo T → IsSeedCoordinate W₁ Vhi T →
        ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ uIcc (Vlo t) (Vhi t),
          Disjoint (ball (x : ℂ) r)
            ((fun z => fwdMap W₁ t z + W₁ t) '' fwdHull W₂ t₂) ∧
          deriv (fun y : ℝ => (ownExt W₁ W' a
            (fun z => fwdMap W₂ t₂ z + W₂ t₂) t y).re) x ∈
              Icc (Real.exp (-L)) (Real.exp L) := by
  obtain ⟨r, γ, hr, hγ, hgeo⟩ :=
    exists_seed_interval_deriv_lower_right hH₁ hH₂ hδ hsepδ hd hqH
  let L : ℝ := 2 / γ ^ 2 * |Tm|
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨r, L, hr, hL, ?_⟩
  intro W₁ W₂ Vlo Vhi T t₂ a W' h hW₂ ht₂ hW₁H hW₂H hWq hqW ht₂m hK₁ hK₂ hlo hhi t ht x hx
  obtain ⟨a₂, W₂', h₂⟩ := exists_imgData hW₂ ht₂
    (isHPHull_fwdHull h.cont ht.1) (isMapOut_fwdMap_gen h.cont ht.1)
    (h.disj.symm.mono (closure_mono ((QuantumZipper.fwdHull_mono).1 ht.2)) Subset.rfl)
  have hKt : fwdHull W₁ t ⊆ H₁ :=
    ((QuantumZipper.fwdHull_mono).1 ht.2).trans hK₁
  obtain ⟨hclear, hlower⟩ := hgeo W₁ W₂ Vlo Vhi t t₂ a₂ W₂'
    h.cont ht.1 hW₁H hW₂H hWq hqW hKt hK₂
    (hlo.restrict ht.2) (hhi.restrict ht.2) h₂ x hx
  obtain ⟨R, hR⟩ := (h.isHPHull_E ht).exists_isMapOut
  obtain ⟨hGd, -, -, -, -, hGR⟩ := h.ownExt_props ht hclear
  have hrl : 0 < r / 2 := by positivity
  have hb := hlower R _ (r / 2) hR hrl hGd (hGR R hR)
  have hd' := h.deriv_ownExt_real ht hr hclear
  have hnorm : ‖deriv (ownExt W₁ W' a
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) t) x‖ =
      (deriv (ownExt W₁ W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) t) x).re := by
    have he : deriv (ownExt W₁ W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) t) x =
        (((deriv (ownExt W₁ W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) t) x).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using hd'.1)
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd'.2.1]
    rfl
  have hdx := hGd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrl))
  have hder := hdx.hasDerivAt.real_of_complex.deriv
  refine ⟨hclear, ?_⟩
  rw [hder]
  constructor
  · apply (Real.exp_le_exp.2 ?_).trans (hnorm ▸ hb)
    dsimp only [L]
    have hh : t₂ ≤ |Tm| := ht₂m.trans (le_abs_self Tm)
    exact neg_le_neg (mul_le_mul_of_nonneg_left hh (by positivity))
  · exact hd'.2.2.trans (Real.one_le_exp hL)

namespace SeedData

/-- The separated-source factors still needed after the whole seed interval
has been controlled. This is an explicit internal hypothesis, not a source
theorem: deriving it requires identifying `V₀`, `G₀` and the other tip with
the two original flows. -/
structure RemoteScale {n : ℕ} (d : SeedData n) (t L : ℝ) : Prop where
  A21 : InScale L (d.A21 t)
  logF : |d.L t| ≤ L
  mark : ∀ m, InScale L ((d.A20 t - d.B0 t m) / (d.V₀ t - d.V m t))
  driver : InScale L ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t))

/-- Interval derivative scales may be enlarged to absorb the finitely many
separated-source factors of the normalized density. -/
theorem abs_normEll_le_of_interval_scale {n : ℕ} (d : SeedData n)
    {t L₀ L : ℝ} {I : Set ℝ} (hL : 0 ≤ L) (hLL : L₀ ≤ L)
    (hI : Convex ℝ I) (hd : DifferentiableOn ℝ (d.F 0 t) I)
    (hb : ∀ x ∈ I, deriv (d.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hF1 : ∀ x ∈ I, d.F 1 t x = deriv (d.F 0 t) x)
    (hW : d.W t ∈ I) (hV : ∀ m, d.V m t ∈ I)
    (h21 : InScale L (d.A21 t)) (hlogF : |d.L t| ≤ L)
    (h2m : ∀ m, InScale L ((d.A20 t - d.B0 t m) / (d.V₀ t - d.V m t)))
    (h0 : InScale L ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t))) :
    |d.normEll t| ≤ coefTot d.κ d.r * L := by
  apply d.abs_normEll_le_of_deriv_bounds hL hI hd ?_ hF1 hW hV h21 hlogF h2m h0
  intro x hx
  exact ⟨(Real.exp_le_exp.2 (neg_le_neg hLL)).trans (hb x hx).1,
    (hb x hx).2.trans (Real.exp_le_exp.2 hLL)⟩

end SeedData

/-- A deterministic seeded bound with the interval derivative and divided
difference estimates discharged from the protected enclosures. The remaining
separated-source hypothesis is exactly `SeedData.RemoteScale`, at one scale
chosen before the paths and the stopping times. -/
theorem exists_abs_normEll_le_right_of_remote_scale {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {q d : ℝ} (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (Tm Lrem κ : ℝ) {n : ℕ} (rr : Fin n → ℝ) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ (s : SeedData n) (W₂ Vlo Vhi : ℝ → ℝ) (T t₂ : ℝ),
        OwnData s.W (fwdHull W₂ t₂) s.φ T s.a s.W' →
        s.φ = (fun z => fwdMap W₂ t₂ z + W₂ t₂) →
        s.κ = κ → s.r = rr → Continuous W₂ → 0 < t₂ → t₂ ≤ Tm →
        ((s.W 0 : ℝ) : ℂ) ∈ closure H₁ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ →
        s.W 0 < q → q < W₂ 0 →
        fwdHull s.W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate s.W Vlo T → IsSeedCoordinate s.W Vhi T →
        (∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ uIcc (Vlo t) (Vhi t)) →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ uIcc (Vlo t) (Vhi t)) →
        (∀ t ∈ Icc (0 : ℝ) T, s.RemoteScale t Lrem) →
        ∀ t ∈ Icc (0 : ℝ) T, |s.normEll t| ≤ coefTot κ rr * L := by
  obtain ⟨r, L₀, hr, hL₀, hb⟩ :=
    exists_seed_interval_own_bounds_right hH₁ hH₂ hδ hsepδ hd hqH Tm
  refine ⟨r, max L₀ Lrem, hr, hL₀.trans (le_max_left _ _), ?_⟩
  intro s W₂ Vlo Vhi T t₂ h hφ hκ hrr hW₂ ht₂ ht₂m hW₁H hW₂H hWq hqW hK₁ hK₂
    hlo hhi hWI hVI hremote t ht
  have h' : OwnData s.W (fwdHull W₂ t₂)
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) T s.a s.W' := by rwa [← hφ]
  have hbound := hb s.W W₂ Vlo Vhi T t₂ s.a s.W' h' hW₂ ht₂
    hW₁H hW₂H hWq hqW ht₂m hK₁ hK₂ hlo hhi t ht
  have hdiff : ∀ x ∈ uIcc (Vlo t) (Vhi t),
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

end InteractingSLE.ZhanGT4
