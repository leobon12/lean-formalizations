import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Norm.Pin
import HigherDimLQGMetric.Sec8b.GeodBridge

/-!
# The forcing count: catalogues, selections, eligible sites, the events `B_𝔆` and `A_Z`

Packet Q9, blueprint Part B `b:def-catalogue` ([C] Prop. 4.5, p. 17–18, l. 900–935; NA2 items 20–21, R13).

* `q9SiteNorm G z s S`: the site-normalized metric `G(z + s·, z + s·)/S` (Part B `b:lem-site-normal`);
* `q9SitePath P z s`: the path in site coordinates `(P - z)/s`;
* `q9Path D x y H`: the canonical `ρ^D_H`-geodesic `P_H` from `x` to `y` on `[0, 1]` (the library's Borel
  scalar-invariant selector `sec8Sel`, Part A `a:lem24`, extended constantly off `[0, 1]`);
* `q9Bump ψ M z s`: the bump `M ψ((· - z)/s)` of a label profile placed at the site `(z, s)` (`b:def-bump`);
* `CountData`: the fixed data of Definition `b:def-catalogue` (label catalogue, metrics, parameters, endpoints, the
  comparison constants);
* `Catalogue`, `Catalogue.Valid`, `IsSelection`, `selBump` (`f_Z`), `IsEligible`, `countEventB` (`B_𝔆`),
  `countEventA` (`A_Z`);
* `SiteContract`: the parts (i), (ii), (iv) of the site certificate `SiteCertOfLabel` (interface version 2) for one
  catalogue, as delivered by that interface.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## Site normalization, site paths, canonical geodesics, bumps -/

/-- The site-normalized metric `G(z + s x, z + s y) / S` (Part B `b:lem-site-normal`; junk value `G` unless
`0 < s` and `0 < S`). -/
def q9SiteNorm (G : ContMetric d) (z : Rd d) (s S : ℝ) : ContMetric d :=
  if h : 0 < s ∧ 0 < S then (G.affine s h.1.ne' z).smul S⁻¹ (inv_pos.2 h.2) else G

/-- The path `P` in the coordinates of the site `(z, s)`: `(P - z)/s`. -/
def q9SitePath (P : ℝ → Rd d) (z : Rd d) (s : ℝ) : ℝ → Rd d :=
  fun t => s⁻¹ • (P t - z)

/-- The canonical `ρ^D_H`-geodesic `P_H` from `x` to `y` (Part B `b:def-catalogue`(c)): the library's Borel
scalar-invariant selector applied to `ρ^D_H`, read on `[0, 1]` and extended constantly. -/
def q9Path (D : DistRd d → ContMetric d) (x y : Rd d) (H : DistRd d) : ℝ → Rd d :=
  s7b_realPath (sec8Sel x y (rho D H).1)

/-- The bump `M ψ((· - z)/s)` of a profile `ψ` placed at the site `(z, s)` (Part B `b:def-bump`). -/
def q9Bump (ψ : C(Rd d, ℝ)) (M : ℝ) (z : Rd d) (s : ℝ) : C(Rd d, ℝ) :=
  M • ψ.comp ⟨fun x => s⁻¹ • (x - z), by fun_prop⟩

/-! ## The data of the count -/

/-- The fixed data of Definition `b:def-catalogue`: the label catalogue of the site certificate, the primary and
secondary strong assignments `D, E` with their parameters `ξ` (primary; it fixes the site units) and `η`, the bump height
`M = M_ξ = ξ⁻¹ log θ⁻¹`, the trigger threshold `btrig`, the deterministic endpoints `x, y`, the comparison constant
`c`, the gap `gΔ`, the local error `ηloc`, the source bounds `U₀`, `Rsrc` and the depth `Δ`. -/
structure CountData (d : ℕ) where
  cat : SiteCatalogue d
  D : DistRd d → ContMetric d
  E : DistRd d → ContMetric d
  ξ : ℝ
  η : ℝ
  M : ℝ
  btrig : ℝ
  x : Rd d
  y : Rd d
  c : ℝ
  gΔ : ℝ
  ηloc : ℝ
  U₀ : ℝ
  Rsrc : ℝ
  Δ : ℝ

/-- A catalogue `𝔆 = (s, 𝒵, Q)` (Part B `b:def-catalogue`(a)): a site radius, a finite set of centres and a unit bin. -/
structure Catalogue (d : ℕ) where
  s : ℝ
  Z : Finset (Rd d)
  Q : ℝ

/-- Validity of a catalogue for the endpoints `x, y` (Part B `b:def-catalogue`(a)): `s ∈ (0, 1]`, `Q > 0`, the full
inspections `B̄_{4s}(z)` lie in `B₄`, avoid `x` and `y`, and are pairwise disjoint. -/
def Catalogue.Valid (𝔆 : Catalogue d) (x y : Rd d) : Prop :=
  0 < 𝔆.s ∧ 𝔆.s ≤ 1 ∧ 0 < 𝔆.Q ∧
    (∀ z ∈ 𝔆.Z, closedBall z (4 * 𝔆.s) ⊆ ball (0 : Rd d) 4 ∧ x ∉ closedBall z (4 * 𝔆.s) ∧
      y ∉ closedBall z (4 * 𝔆.s)) ∧
    ∀ z ∈ 𝔆.Z, ∀ z' ∈ 𝔆.Z, z ≠ z' → Disjoint (closedBall z (4 * 𝔆.s)) (closedBall z' (4 * 𝔆.s))

/-- A selection (Part B `b:def-catalogue`(b)): labelled sites of the catalogue, at most one label per site. -/
def IsSelection {Λ : Type} (𝔆 : Catalogue d) (Z : Finset (Rd d × Λ)) : Prop :=
  (∀ p ∈ Z, p.1 ∈ 𝔆.Z) ∧ ∀ p ∈ Z, ∀ q ∈ Z, p.1 = q.1 → p = q

/-- `f_Z = ∑_{(z, ℓ) ∈ Z} f_{z, s, ℓ}` (Part B `b:def-catalogue`(b)). -/
def selBump (K : CountData d) (s : ℝ) (Z : Finset (Rd d × K.cat.Label)) : C(Rd d, ℝ) :=
  ∑ p ∈ Z, q9Bump (K.cat.prof p.2) K.M p.1 s

/-- The site unit `S_i(H) = s^{ϕ(ξ)} e^{ξ H_s(z)}` (Part B `b:lem-site-normal`). -/
def countUnit (K : CountData d) (s : ℝ) (z : Rd d) (H : DistRd d) : ℝ :=
  scaleS d K.ξ 1 s z H

/-- The site-normalized primary metric `D̂^{z,s}_H`. -/
def countSiteD (K : CountData d) (s : ℝ) (z : Rd d) (H : DistRd d) : ContMetric d :=
  q9SiteNorm (rho K.D H) z s (countUnit K s z H)

/-- The site-normalized secondary metric `Ê^{z,s}_H` (in primary site units). -/
def countSiteE (K : CountData d) (s : ℝ) (z : Rd d) (H : DistRd d) : ContMetric d :=
  q9SiteNorm (rho K.E H) z s (countUnit K s z H)

/-- Eligibility of the site `(z, s)` at the field `H` (Part B `b:def-catalogue`(d)): (E1) a valid label, (E2) the
unit in `[Q, 2Q]`, (E3) the canonical geodesic meets the inner core `B̄_{3s/2}(z)`. -/
def IsEligible (K : CountData d) (𝔆 : Catalogue d) (z : Rd d) (H : DistRd d) : Prop :=
  (∃ ℓ, K.cat.Source ℓ (countSiteD K 𝔆.s z H) (countSiteE K 𝔆.s z H)) ∧
    countUnit K 𝔆.s z H ∈ Icc 𝔆.Q (2 * 𝔆.Q) ∧
    ∃ t ∈ Icc (0 : ℝ) 1, q9Path K.D K.x K.y H t ∈ closedBall z (3 * 𝔆.s / 2)

open Classical in
/-- The event `B_𝔆` (Part B `b:def-catalogue`(e)): (i) the local comparison on `B̄_{Rsrc}`, (ii) the gap at the
endpoints and `D_H(x, y) ≤ U₀`, (iii) the barrier between `∂B₈` and `∂B_{Rsrc}`, (iv) at least `Δ^{-1/2}` eligible
sites (equivalently `⌈Δ^{-1/2}⌉`, the count being an integer). -/
def countEventB (K : CountData d) (𝔆 : Catalogue d) : Set (DistRd d) :=
  {H | CompOn (rho K.E H) (rho K.D H) K.c K.ηloc K.Rsrc ∧
    (K.c - K.gΔ) * (rho K.D H).1 (K.x, K.y) ≤ (rho K.E H).1 (K.x, K.y) ∧
    (rho K.D H).1 (K.x, K.y) ≤ K.U₀ ∧
    ENNReal.ofReal (2 * K.U₀) <
      setDistIn (rho K.D H) univ (sphere (0 : Rd d) 8) (sphere (0 : Rd d) K.Rsrc) ∧
    K.Δ ^ (-(1 / 2 : ℝ)) ≤ ((𝔆.Z.filter fun z => IsEligible K 𝔆 z H).card : ℝ)}

/-- The event `A_Z` of a selection (Part B `b:def-catalogue`(f)): `H ∈ B_𝔆` and, for every labelled site of `Z`, the
label is valid, the unit lies in `[Q, 2Q]`, and the trigger passes for the source metric `D̂^i_H` along the canonical
geodesic of the modified field `H - f_Z`. -/
def countEventA (K : CountData d) (𝔆 : Catalogue d) (Z : Finset (Rd d × K.cat.Label)) :
    Set (DistRd d) :=
  {H | H ∈ countEventB K 𝔆 ∧ ∀ p ∈ Z,
    K.cat.Source p.2 (countSiteD K 𝔆.s p.1 H) (countSiteE K 𝔆.s p.1 H) ∧
    countUnit K 𝔆.s p.1 H ∈ Icc 𝔆.Q (2 * 𝔆.Q) ∧
    PassesTrigger (countSiteD K 𝔆.s p.1 H)
      (q9SitePath (q9Path K.D K.x K.y (addFun H (-selBump K 𝔆.s Z))) p.1 𝔆.s) 0 1 K.btrig}

/-! ## The site-certificate contract of one catalogue -/

/-- Parts (i), (ii), (iv) of the site certificate `SiteCertOfLabel` (interface version 2) for one label catalogue
`cat` and the scales `θ, ς, δsep, εnet, εatt` at the tolerance `v`, with the reference constants (F1)
`(Hup, sR, Hlo, b, mc, A0)` and the polynomial `polyB Ap kp`: exactly the conjunction delivered by the interface for a
fixed `v` (minus the exhaustion (iii), which the count does not use). -/
structure SiteContract (cat : SiteCatalogue d) (Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt : ℝ) :
    Prop where
  θ_lower : Real.exp (-polyB Ap kp 0 v⁻¹) ≤ θ
  θ_lt_one : θ < 1
  ς_pos : 0 < ς
  sep : 4 * ς ≤ δsep
  net : εnet ≤ siteEps0 mc Hlo
  budget : 2 * εatt + εnet < Hlo⁻¹ * (δsep / 2) ^ b
  card : Real.log (@Fintype.card cat.Label cat.fintypeLabel) ≤ polyB Ap kp 0 v⁻¹
  prof : ∀ ℓ, (∀ x, 0 ≤ cat.prof ℓ x ∧ cat.prof ℓ x ≤ 1) ∧ tsupport (cat.prof ℓ) ⊆ interior (siteC d) ∧
    IsCMBounded (cat.prof ℓ) (polyB Ap kp 0 v⁻¹)
  borel : ∀ ℓ, ∃ S : Set (ContMetric d × ContMetric d), MeasurableSet S ∧
    ∀ D E : ContMetric d, D.IsLength → E.IsLength → ((D, E) ∈ S ↔ cat.Source ℓ D E)
  local_ : ∀ ℓ (D E D₂ E₂ : ContMetric d), (∀ x y, D.internal (siteB d) x y = D₂.internal (siteB d) x y) →
    (∀ x y, E.internal (siteB d) x y = E₂.internal (siteB d) x y) →
    (cat.Source ℓ D E ↔ cat.Source ℓ D₂ E₂)
  refs : ∀ ℓ (D E : ContMetric d), cat.Source ℓ D E → SiteRefs Hup sR Hlo b mc A0 D
  cert : ∀ ξ : ℝ, 0 < ξ → ∀ ℓ (D E : ContMetric d), D.IsLength → cat.Source ℓ D E →
    Nonempty (ForcingCert D E ((ξ⁻¹ * Real.log θ⁻¹) • cat.prof ℓ) ξ (ξ⁻¹ * Real.log θ⁻¹) θ ς δsep
      (siteEps0 mc Hlo) εnet εatt (siteAout mc Hlo) Hlo b v d₀)

end HigherDimLQGContinuity
