import HigherDimLQGContinuity.Improve.Catalogue
import HigherDimLQGContinuity.Improve.Class

/-!
# A large class of supplied eligible sites
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

open Classical in
/-- Pigeonholing supplied sites produces a single deterministic catalogue
with at least `n` eligible centres. The label and path hypotheses are the
pointwise conclusions of the source event and the site normalization. -/
theorem q11_sites_to_catalogue {d m n : ℕ} (hd : 1 ≤ d) (hm : 0 < m)
    {V Δ K0 : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hn : 0 < n)
    (hcount : (q11ClassSet d V Δ K0).card * n ≤ m)
    (K : CountData d) (H : DistRd d)
    (c : Fin m → Rd d) (r : Fin m → ℝ)
    (k : Fin m → ℕ) (j : Fin m → Fin d → ℤ)
    (hinj : Function.Injective (fun i => (c i, r i)))
    (hk : ∀ i, k i ∈ p4_fullScales V)
    (hr : ∀ i, r i = p4_radius (k i))
    (hc : ∀ i, c i = latPt (r i / (20 * Real.sqrt d)) (j i))
    (hgeom : ∀ i, closedBall (c i) (4 * r i) ⊆ ball (0 : Rd d) 4 ∧
      K.x ∉ closedBall (c i) (4 * r i) ∧ K.y ∉ closedBall (c i) (4 * r i))
    (hrange : ∀ i, Δ ^ (2 : ℕ) ≤ r i ∧ r i ≤ Δ)
    (hunit : ∀ i, Δ ^ K0 ≤ countUnit K (r i) (c i) H ∧
      countUnit K (r i) (c i) H ≤ Δ ^ (-K0))
    (hlabel : ∀ i, ∃ ℓ : K.cat.Label,
      K.cat.Source ℓ (countSiteD K (r i) (c i) H) (countSiteE K (r i) (c i) H))
    (hvisit : ∀ i, ∃ t ∈ Icc (0 : ℝ) 1,
      q9Path K.D K.x K.y H t ∈ ball (c i) (r i / 10)) :
    ∃ cl ∈ q11ClassSet d V Δ K0,
      let 𝔆 := q11Catalogue d (p4_radius cl.1) cl.2.1 cl.2.2 K.x K.y
      𝔆.Valid K.x K.y ∧
      n ≤ (𝔆.Z.filter fun z => IsEligible K 𝔆 z H).card ∧
      (𝔆.Z.card : ℝ) ≤
        (160 * Real.sqrt d + 5) ^ d * Δ ^ (-(2 * (d : ℝ))) := by
  classical
  let S : Fin m → ℝ := fun i => countUnit K (r i) (c i) H
  obtain ⟨cl, hcl, I, hI, hclass⟩ := q11_class_pigeonhole hd hΔ hm k j S hk hunit hcount
  let rad : ℝ := p4_radius cl.1
  let 𝔆 : Catalogue d := q11Catalogue d rad cl.2.1 cl.2.2 K.x K.y
  have hrad : 0 < rad := by dsimp [rad, p4_radius]; positivity
  obtain ⟨i₀, hi₀⟩ : I.Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le hn hI)
  have hrclass (i : Fin m) (hi : i ∈ I) : r i = rad := by
    calc
      r i = p4_radius (k i) := hr i
      _ = p4_radius cl.1 := congrArg p4_radius (hclass i hi).1
  have hrad1 : rad ≤ 1 := by
    have hri := (hrange i₀).2
    rw [← hrclass i₀ hi₀]
    exact hri.trans hΔ1
  have hradΔ : Δ ^ (2 : ℕ) ≤ rad := by
    rw [← hrclass i₀ hi₀]
    exact (hrange i₀).1
  have hvalid : 𝔆.Valid K.x K.y := q11_catalogue_valid hd hrad hrad1 _ _ _ _
  have hcard : (𝔆.Z.card : ℝ) ≤
      (160 * Real.sqrt d + 5) ^ d * Δ ^ (-(2 * (d : ℝ))) :=
    q11_catalogue_card_for_prop45 hd hΔ hΔ1 hradΔ _ _ _ _
  refine ⟨cl, hcl, hvalid, ?_, hcard⟩
  have hmem (i : Fin m) (hi : i ∈ I) : c i ∈ 𝔆.Z := by
    have hci := (hclass i hi).2.1
    have hri : r i = rad := hrclass i hi
    change c i ∈ q11CentreSet d rad cl.2.1 K.x K.y
    exact q11_centre_mem hd hrad (by rw [← hri]; exact hc i) hci (by
      rw [← hri]
      exact hgeom i)
  have helig (i : Fin m) (hi : i ∈ I) : IsEligible K 𝔆 (c i) H := by
    have hri : r i = rad := hrclass i hi
    obtain ⟨ℓ, hℓ⟩ := hlabel i
    obtain ⟨t, ht, hhit⟩ := hvisit i
    have hunitI := (hclass i hi).2.2
    dsimp [IsEligible]
    refine ⟨⟨ℓ, ?_⟩, ?_, t, ht, ?_⟩
    · simpa only [𝔆, q11Catalogue, hri] using hℓ
    · simpa only [𝔆, q11Catalogue, ← hri, S, Set.mem_Icc] using hunitI
    · have hclose : q9Path K.D K.x K.y H t ∈ closedBall (c i) (3 * r i / 2) := by
        exact mem_closedBall.mpr (le_trans (mem_ball.mp hhit).le (by linarith [((hrange i).1)]))
      simpa only [𝔆, q11Catalogue, ← hri] using hclose
  have hinjI : Set.InjOn c I := by
    intro i hi i' hi' hcEq
    apply hinj
    have hri : r i = rad := hrclass i hi
    have hri' : r i' = rad := hrclass i' hi'
    exact Prod.ext hcEq (hri.trans hri'.symm)
  have himage : I.image c ⊆ 𝔆.Z.filter (fun z => IsEligible K 𝔆 z H) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨hmem i hi, helig i hi⟩
  have hcardI : I.card ≤ (𝔆.Z.filter fun z => IsEligible K 𝔆 z H).card := by
    calc
      I.card = (I.image c).card := (Finset.card_image_iff.mpr hinjI).symm
      _ ≤ _ := Finset.card_le_card himage
  exact hI.trans hcardI

end HigherDimLQGContinuity
