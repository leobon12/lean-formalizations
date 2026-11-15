/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomCap
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomWord
import InteractingSLE.Spec.ZhanGT4.A1FamilyCanon

/-!
# Zhan's A.1 (R80): the geometry `hgeom` of A1-FAMILY's per-stop data from the seeded capacity coordinates

Packet PROVE-A1-SEEDGEOM. `A1Family.FamilyRect.ofRect` (and its mirror) asks, for each rectangle `m` and almost every
live sample `z = (x, y)` at the stop `τ`, for `SeedImageGeometry` of the masked canonical image driver and the family's
image force points, all stopped at the cap `F.Sat τ m z`, with the image word `ΘL (τ y) y`, `ΘR (τ y) y` as initial
values (its premise `hgeom`).

Here that premise is reduced, sample by sample, to the geometry of the seeded capacity coordinates
(`seedImageGeometry_seedCapacity`): up to the capacity horizon the canonical image driver is the seeded capacity driver
(A1-FAMILY's `rDrv_eq_seedCapacityDriver`), the cap is at most the horizon, and the family's force points agree with
the seeded capacity force points up to the cap.

## Main results

* **`seedImageGeometry_seedCapacity_of_isSeedWord`**: the seeded capacity geometry with the initial capacity word equal
  to a given admissible word (`IsSeedWord`, proved for the four A.1 words in `A1SeedGeomWord`);
* **`seedImageGeometry_rDrv`** (image curve on `X`, conditioning curve on `Y`);
* **`seedImageGeometry_rDrvFst`** (the mirror).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1SeedGeom

open A1Ref A1Core A1Family

variable {X Y : Type*} {n nL nR : ℕ}

/-- **The seeded capacity geometry with a given admissible initial word**: if the initial own-time image forces,
centred at the image driver, form the word `(xL, xR)` (`hx0L`, `hx0R`) and the word is admissible, the seeded capacity
coordinates have `SeedImageGeometry` with initial word `(xL, xR)`. -/
theorem seedImageGeometry_seedCapacity_of_isSeedWord {Ω : Type*} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    {A : Ω → Set ℂ} {c : ℝ} (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω))
    (hc : 0 < c) (hlb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r)
    (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1)) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hword : IsSeedWord xL xR ρL ρR) (ω : Ω)
    (hcont : ∀ k, ContinuousOn (fun t => (d ω).imageForce t k) (Icc 0 (S ω)))
    (himg : ∀ k, ∀ t ∈ Icc (0 : ℝ) (S ω),
      IntervalIntegrable (fun u => 2 * (d ω).A 1 u ^ 2 / ((d ω).imageForce u k - (d ω).A 0 u)) volume 0 t ∧
        (d ω).imageForce t k = (d ω).imageForce 0 k +
          ∫ u in (0 : ℝ)..t, 2 * (d ω).A 1 u ^ 2 / ((d ω).imageForce u k - (d ω).A 0 u))
    (hltL : ∀ i, ∀ t ∈ Ioc (0 : ℝ) (S ω), (d ω).imageForce t (e (.inl i)) < (d ω).A 0 t)
    (hgtR : ∀ j, ∀ t ∈ Ioc (0 : ℝ) (S ω), (d ω).A 0 t < (d ω).imageForce t (e (.inr j)))
    (hx0L : ∀ i, (d ω).imageForce 0 (e (.inl i)) - (d ω).A 0 0 = xL i)
    (hx0R : ∀ j, (d ω).imageForce 0 (e (.inr j)) - (d ω).A 0 0 = xR j) :
    SeedImageGeometry xL xR ρL ρR (seedCapacityDriver d S · ω)
      (fun i u => seedCapacityForce d S (e (.inl i)) u ω) (fun j u => seedCapacityForce d S (e (.inr j)) u ω)
      (seedCapacityHorizon d S ω) := by
  have h0 (k : Fin (n + 1)) := seedCapacityForce_zero hown hCc hCs hc hlb ω k
  have eL : (fun i => seedCapacityForce d S (e (.inl i)) 0 ω) = xL := funext fun i => by rw [h0, hx0L]
  have eR : (fun j => seedCapacityForce d S (e (.inr j)) 0 ω) = xR := funext fun j => by rw [h0, hx0R]
  obtain ⟨⟨hordL, hxL, hordR, hxR⟩, hsL, hsR, hthr⟩ := hword
  obtain ⟨hseedL, hseedR⟩ := (Sec2.not_thr_iff_seedSum xL xR ρL ρR).1 hthr
  have h := seedImageGeometry_seedCapacity hown hCc hCs hc hlb e (ρL := ρL) (ρR := ρR) ω hcont himg hltL hgtR
    (fun i => by linarith [hxL i, hx0L i]) (fun j => by linarith [hxR j, hx0R j])
    (fun i i' hii' => by have := hordL hii'; linarith [hx0L i, hx0L i'])
    (fun j j' hjj' => by have := hordR hjj'; linarith [hx0R j, hx0R j'])
    (fun i i' hx hx0 => hsL i i' (by linarith [hx0L i, hx0L i']) (by linarith [hx0L i]))
    (fun j j' hx hx0 => hsR j j' (by linarith [hx0R j, hx0R j']) (by linarith [hx0R j]))
    (by rw [eL]; exact hseedL) (by rw [eR]; exact hseedR)
  rwa [eL, eR] at h

/-- **`hgeom` from the seeded capacity coordinates** (image curve on `X` started at `xj`, conditioning sample `y` live
at its stop `τ y`; seeded data `d` in the image curve's frame with the frozen hull of `y` at `τ y`): if the seeded
capacity coordinates have the geometry with initial word `(xL, xR)` up to their horizon, the cap is at most the horizon
and the force points `VL`, `VR` agree with the seeded capacity force points up to the cap, then the masked canonical
image driver and `VL`, `VR`, all stopped at the cap, have the geometry up to the cap. -/
theorem seedImageGeometry_rDrv {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ}
    {Wk : ℝ≥0 → Y → ℝ} {τ : Y → ℝ≥0} {y : Y} (hlive : live (τ y) y) {d : X → SeedData n} {S : X → ℝ≥0}
    (hW : ∀ x, (d x).W = Strip.extPath (Wj · x))
    (hown : ∀ x, OwnData (d x).W (A2X.physHull (xk - xj) (Strip.extPath (Wk · y)) (τ y)) (d x).φ (S x) (d x).a
      (d x).W')
    (hφ : ∀ x, (d x).φ = A2X.physMap (xk - xj) (Strip.extPath (Wk · y)) (τ y))
    (hj : ∀ x T, ENNReal.ofReal T < ζj x → ContinuousOn (d x).W (Icc 0 T))
    (hk : ∃ τ', ((τ y : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · y)) (Icc 0 τ')) (hk0 : Wk 0 y = 0)
    (hgood : ∀ x, A1Ref.IsGoodTime 0 (d x).W (ζj x) (xk - xj) (Strip.extPath (Wk · y)) (τ y) (S x))
    (hCc : ∀ x, Continuous (seedQuadClock (seedCapacityCoeff d S) x))
    (hCs : ∀ x, StrictMono (seedQuadClock (seedCapacityCoeff d S) x)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ x r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) x r) (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1))
    (x : X) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hgeo : SeedImageGeometry xL xR ρL ρR (seedCapacityDriver d S · x)
      (fun i u => seedCapacityForce d S (e (.inl i)) u x) (fun j u => seedCapacityForce d S (e (.inr j)) u x)
      (seedCapacityHorizon d S x))
    {VL : Fin nL → ℝ≥0 → ℝ} {VR : Fin nR → ℝ≥0 → ℝ} {cap : ℝ≥0} (hcap : cap ≤ seedCapacityHorizon d S x)
    (hVL : ∀ i, ∀ t ≤ cap, VL i t = seedCapacityForce d S (e (.inl i)) t x)
    (hVR : ∀ j, ∀ t ≤ cap, VR j t = seedCapacityForce d S (e (.inr j)) t x) :
    SeedImageGeometry xL xR ρL ρR (fun t => rDrv live xj Wj ζj xk Wk τ (min t cap) (x, y))
      (fun i t => VL i (min t cap)) (fun j t => VR j (min t cap)) cap :=
  (hgeo.mono hcap).stop_of_eqOn (fun t ht => by
    show rDrv live xj Wj ζj xk Wk (fun _ => τ y) t (x, y) = _
    exact rDrv_eq_seedCapacityDriver hlive hW hown hφ hj hk hk0 hgood hCc hCs hc hClb x (ht.trans hcap))
    hVL hVR

/-- **`hgeom` from the seeded capacity coordinates, mirror** (image curve on `Y`, conditioning sample `x` live at its
stop `τ x`). -/
theorem seedImageGeometry_rDrvFst {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ}
    {Wk : ℝ≥0 → X → ℝ} {τ : X → ℝ≥0} {x : X} (hlive : live (τ x) x) {d : Y → SeedData n} {S : Y → ℝ≥0}
    (hW : ∀ y, (d y).W = Strip.extPath (Wj · y))
    (hown : ∀ y, OwnData (d y).W (A2X.physHull (xk - xj) (Strip.extPath (Wk · x)) (τ x)) (d y).φ (S y) (d y).a
      (d y).W')
    (hφ : ∀ y, (d y).φ = A2X.physMap (xk - xj) (Strip.extPath (Wk · x)) (τ x))
    (hj : ∀ y T, ENNReal.ofReal T < ζj y → ContinuousOn (d y).W (Icc 0 T))
    (hk : ∃ τ', ((τ x : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · x)) (Icc 0 τ')) (hk0 : Wk 0 x = 0)
    (hgood : ∀ y, A1Ref.IsGoodTime 0 (d y).W (ζj y) (xk - xj) (Strip.extPath (Wk · x)) (τ x) (S y))
    (hCc : ∀ y, Continuous (seedQuadClock (seedCapacityCoeff d S) y))
    (hCs : ∀ y, StrictMono (seedQuadClock (seedCapacityCoeff d S) y)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ y r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) y r) (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1))
    (y : Y) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hgeo : SeedImageGeometry xL xR ρL ρR (seedCapacityDriver d S · y)
      (fun i u => seedCapacityForce d S (e (.inl i)) u y) (fun j u => seedCapacityForce d S (e (.inr j)) u y)
      (seedCapacityHorizon d S y))
    {VL : Fin nL → ℝ≥0 → ℝ} {VR : Fin nR → ℝ≥0 → ℝ} {cap : ℝ≥0} (hcap : cap ≤ seedCapacityHorizon d S y)
    (hVL : ∀ i, ∀ t ≤ cap, VL i t = seedCapacityForce d S (e (.inl i)) t y)
    (hVR : ∀ j, ∀ t ≤ cap, VR j t = seedCapacityForce d S (e (.inr j)) t y) :
    SeedImageGeometry xL xR ρL ρR (fun t => rDrvFst live xj Wj ζj xk Wk τ (min t cap) (x, y))
      (fun i t => VL i (min t cap)) (fun j t => VR j (min t cap)) cap :=
  (hgeo.mono hcap).stop_of_eqOn (fun t ht => by
    show rDrvFst live xj Wj ζj xk Wk (fun _ => τ x) t (x, y) = _
    exact rDrvFst_eq_seedCapacityDriver hlive hW hown hφ hj hk hk0 hgood hCc hCs hc hClb y (ht.trans hcap))
    hVL hVR

end InteractingSLE.ZhanGT4.A1SeedGeom
