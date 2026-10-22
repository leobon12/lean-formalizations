import HigherDimLQGMetric.Sec8b.Lemma84Class
import HigherDimLQGMetric.Sec8b.Lemma83
import HigherDimLQGMetric.Sec8b.Lemma84Count

/-! One almost-sure pruning event for all lattice indexed labeled sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical
open Set Metric MeasureTheory
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

variable {d : ℕ}

def s7b_indexSite (r : ℝ) (p : (Fin d → ℤ) × ℕ) : Rd d × ℕ :=
  (latPt (r / (100 * d)) p.1, p.2)

def s7b_indexSites (r : ℝ) (W : Finset ((Fin d → ℤ) × ℕ)) :
    Finset (Rd d × ℕ) := W.image (s7b_indexSite r)

/-- Every finite labeled lattice set has a finite integer-index
representation, even if the same center appears with several labels. -/
theorem s7b_labeled_index_rep {J : ℕ} {r R : ℝ} {x y : Rd d}
    {colour : Fin d → ℤ} {s : Finset (Rd d × ℕ)}
    (hs : IsSec8LabeledSet d J r R x y colour s) :
    ∃ W : Finset ((Fin d → ℤ) × ℕ), s7b_indexSites r W = s := by
  classical
  let index : Rd d × ℕ → (Fin d → ℤ) × ℕ := fun site =>
    if hsite : site ∈ s then (Classical.choose (hs.1 site hsite), site.2)
    else (fun _ => 0, site.2)
  have hindex (site : Rd d × ℕ) (hsite : site ∈ s) :
      s7b_indexSite r (index site) = site := by
    obtain ⟨k, hk, _, _, _, _, _⟩ := hs.1 site hsite
    have hchoose := (Classical.choose_spec (hs.1 site hsite)).1
    dsimp only [s7b_indexSite, index]
    rw [dite_eq_left hsite]
    exact Prod.ext hchoose.symm rfl
  refine ⟨s.image index, ?_⟩
  ext site
  simp only [s7b_indexSites, Finset.mem_image]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    simpa only [hindex q hq] using hq
  · intro hsite
    exact ⟨index site, ⟨site, hsite, rfl⟩, hindex site hsite⟩

/-- The finite class selected after seeing the field is allowed in the
pruning step: the almost-sure event is uniform over all integer indices. -/
theorem lemma83_ae_all_indexed {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P)
    {ξ Q cs Cs R : ℝ}
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hR : 0 < R)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt) (x y : Rd d) :
    ∀ᵐ ω ∂P,
      ∀ j i : ℤ, ∀ colour : Fin d → ℤ,
      ∀ W : Finset ((Fin d → ℤ) × ℕ),
        IsSec8LabeledSet d T.J ((64 : ℝ) ^ j) R x y colour
          (s7b_indexSites ((64 : ℝ) ^ j) W) →
        sec8C1 D Dt ξ Q Cs ((2 : ℝ) ^ i) R x y (h ω) →
        sec8C2 D Dt ξ Q ((2 : ℝ) ^ i) R ((64 : ℝ) ^ j)
          T.J T.N (s7b_indexSites ((64 : ℝ) ^ j) W) (h ω) →
        sec8C3 D x y ((64 : ℝ) ^ j)
          (s7b_indexSites ((64 : ℝ) ^ j) W) (h ω) →
        ∃ Z' ⊆ s7b_indexSites ((64 : ℝ) ^ j) W,
          T.g / (4 * T.H) * (s7b_indexSites ((64 : ℝ) ^ j) W).card ≤ Z'.card ∧
          h ω ∈ FavEvent D Dt ξ Q Cs ((2 : ℝ) ^ i) R ((64 : ℝ) ^ j)
            T.b T.J T.N T.V T.f x y Z' := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro colour
  apply ae_all_iff.mpr
  intro W
  by_cases hZ : IsSec8LabeledSet d T.J ((64 : ℝ) ^ j) R x y colour
      (s7b_indexSites ((64 : ℝ) ^ j) W)
  · filter_upwards [lemma83_ae P h hh hd hξ hQ
      (show 0 < (2 : ℝ) ^ i by positivity) hR
      (show 0 < (64 : ℝ) ^ j by positivity)
      hD hDt hcomp T x y colour _ hZ] with ω hω
    exact fun _ => hω
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hZ h))

/-- The class image count holds simultaneously for every integer-indexed
class and every pair of natural parameters `k,m`. -/
theorem lemma84_class_ae_all_indexed {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P)
    {ξ Q cs Cs R : ℝ}
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hR : 0 < R)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt) (x y : Rd d) :
    ∀ᵐ ω ∂P,
      ∀ j i : ℤ, ∀ colour : Fin d → ℤ,
      ∀ W : Finset ((Fin d → ℤ) × ℕ), ∀ k m : ℕ,
        let r := (64 : ℝ) ^ j
        let q := (2 : ℝ) ^ i
        let s := s7b_indexSites r W
        IsSec8LabeledSet d T.J r R x y colour s →
        1 ≤ m → m ≤ k → k ≤ s.card →
        (∀ n : ℕ, T.g / (4 * T.H) * k ≤ n → m ≤ n) →
        sec8C1 D Dt ξ Q Cs q R x y (h ω) →
        sec8C2 D Dt ξ Q q R r T.J T.N s (h ω) →
        sec8C3 D x y r s (h ω) →
        ((s.card : ℝ) / k) ^ m ≤
          (((s.powerset.filter fun t =>
            1 ≤ t.card ∧ t.card ≤ k ∧
              h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y t).card : ℕ) : ℝ) := by
  classical
  apply ae_all_iff.mpr; intro j
  apply ae_all_iff.mpr; intro i
  apply ae_all_iff.mpr; intro colour
  apply ae_all_iff.mpr; intro W
  apply ae_all_iff.mpr; intro k
  apply ae_all_iff.mpr; intro m
  dsimp only
  by_cases hinputs : IsSec8LabeledSet d T.J ((64 : ℝ) ^ j) R x y colour
      (s7b_indexSites ((64 : ℝ) ^ j) W) ∧
      1 ≤ m ∧ m ≤ k ∧ k ≤ (s7b_indexSites ((64 : ℝ) ^ j) W).card ∧
      (∀ n : ℕ, T.g / (4 * T.H) * k ≤ n → m ≤ n)
  · rcases hinputs with ⟨hZ, hmpos, hmk, hks, hm⟩
    filter_upwards [lemma84_class P h hh hd hξ hQ
      (show 0 < (2 : ℝ) ^ i by positivity) hR
      (show 0 < (64 : ℝ) ^ j by positivity)
      hD hDt hcomp T x y colour _ hZ hmpos hmk hks hm] with ω hω
    exact fun _ _ _ _ _ => hω
  · exact Filter.Eventually.of_forall (fun _ hZ hmpos hmk hks hm =>
      False.elim (hinputs ⟨hZ, hmpos, hmk, hks, hm⟩))

end HigherDimLQGMetric
