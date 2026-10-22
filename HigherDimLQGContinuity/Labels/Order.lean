import HigherDimLQGContinuity.Labels.Realizable
import HigherDimLQGContinuity.Routing.LeadsDefs

/-!
# The explicit order of site constants

This is Definition `b:def-order` (O1)–(O10). The constants are functions of
fixed site data and the tolerance `v`; only the bump height also uses `ξ`.
-/

set_option autoImplicit false

noncomputable section

open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- The fixed denominator of the site-port lattice. -/
def sitePortDenom {d : ℕ} (S : SiteData d) : ℕ := 2 ^ (S.mesh.kMesh + 7) * d

/-- The exponent in the initial tolerance scale. -/
def siteTExponent {d : ℕ} (S : SiteData d) : ℝ := max 1 (1 / (S.seed.α * S.s))

/-- The fixed coefficient of `t₀`. -/
def siteTCoeff {d : ℕ} (S : SiteData d) : ℝ :=
  min (1 / 6) (min ((16 * S.seed.A) ^ (-(1 / S.seed.α)) *
    (S.seed.d₀ / (1000 * S.Hup)) ^ (1 / (S.seed.α * S.s)))
    (S.seed.d₀ / (4000 * S.seed.ℓ₁)))

/-- The coefficient in the fixed lead-count bound (O3). -/
def siteCN (d : ℕ) : ℝ := 2 * (6 * √(d : ℝ)) ^ d + 15

/-- The geometric-series constant used for doubled-ball access. -/
def siteCS (s : ℝ) : ℝ := 2 ^ s + (2 ^ s - 1)⁻¹

/-- The fixed coefficient of the rational grid spacing. -/
def siteNuCoeff {d : ℕ} (S : SiteData d) : ℝ :=
  min (Routing.gpC0 d / (4 * √(d : ℝ) * (siteCN d) ^ 3))
    (min (1 / (800 * d : ℝ))
      ((4 * siteCS S.seed.sE) ^ (-(1 / S.seed.sE)) / (100 * d : ℝ)))

/-- The fixed coefficient of the chamber-ball radius. -/
def siteOmegaCoeff (d : ℕ) : ℝ :=
  min (Routing.gpC1 4 / 8) (1 / (8 * √(d : ℝ)))

/-- The corrected lead-clearance exponent `p/(α²β³)`. -/
def siteRExponent {d : ℕ} (S : SiteData d) : ℝ :=
  siteTExponent S / (S.seed.α ^ 2 * S.seed.β ^ 3)

/-- The corrected exponent `q_ν` from ruling N29. -/
def siteNuExponent {d : ℕ} (S : SiteData d) : ℝ :=
  max ((3 * d + 2 : ℝ) * siteRExponent S)
    (max (1 / S.s) (1 / S.seed.sE))

/-- The exponent of `θ` as a power of `ν`. -/
def siteThetaExponent {d : ℕ} (S : SiteData d) : ℝ :=
  8 * d + 3 * S.b

/-- The corrected exponent `q_ς` from ruling N29. -/
def siteVarsigmaExponent {d : ℕ} (S : SiteData d) : ℝ :=
  max (4 * siteNuExponent S)
    (max ((3 * S.b / S.s) * siteNuExponent S)
      ((1 + siteThetaExponent S * siteNuExponent S) / S.seed.sE))

/-- (O6) as a function of the grid spacing. -/
def siteAnetFromNu {d : ℕ} (S : SiteData d) (Cnet ν : ℝ) : ℝ :=
  Cnet * S.Hup * ν ^ (-(8 * d : ℝ))

/-- (O5) as a function of the grid spacing. -/
def siteDeltaFromNu (ν : ℝ) : ℝ := Routing.gpC1 4 * ν ^ 3 / 4

/-- The numerator in (O7). -/
def siteThetaNumerator {d : ℕ} (S : SiteData d) (ν : ℝ) : ℝ :=
  min (siteEps0 S.mc S.Hlo) (S.Hlo⁻¹ * (siteDeltaFromNu ν / 2) ^ S.b)

/-- (O7) as a function of the grid spacing. -/
def siteThetaFromNu {d : ℕ} (S : SiteData d) (Cnet ν : ℝ) : ℝ :=
  siteThetaNumerator S ν / (4 * siteAnetFromNu S Cnet ν)

def siteVarsigmaTerm1 (ν : ℝ) : ℝ := siteDeltaFromNu ν / 4

def siteVarsigmaTerm2 (d : ℕ) (ν : ℝ) : ℝ := siteOmegaCoeff d * ν ^ 4 / 4

def siteVarsigmaTerm3 {d : ℕ} (S : SiteData d) (v : ℝ) : ℝ :=
  (v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) / 8

def siteVarsigmaTerm4 {d : ℕ} (S : SiteData d) (ν : ℝ) : ℝ :=
  ((S.Hlo⁻¹ * (siteDeltaFromNu ν / 2) ^ S.b) / (4 * S.Hup)) ^ (1 / S.s) / 4

def siteVarsigmaTerm5 {d : ℕ} (S : SiteData d) (v θ : ℝ) : ℝ :=
  (v * θ * S.seed.d₀ / (1000 * S.seed.HE)) ^ (1 / S.seed.sE) / 4

/-- (O8) as a function of `v`, `ν` and `θ`. -/
def siteVarsigmaFrom {d : ℕ} (S : SiteData d) (v ν θ : ℝ) : ℝ :=
  min (siteVarsigmaTerm1 ν)
    (min (siteVarsigmaTerm2 d ν)
      (min (siteVarsigmaTerm3 S v)
        (min (siteVarsigmaTerm4 S ν) (siteVarsigmaTerm5 S v θ))))

/-- The exact constants in (O1)–(O10). -/
structure SiteConsts where
  p : ℝ
  ct : ℝ
  t₀ : ℝ
  uLead : ℝ
  r : ℝ
  N : ℕ
  q₀ : ℕ
  CN : ℝ
  CsE : ℝ
  cν : ℝ
  barν : ℝ
  Mν : ℕ
  ν : ℝ
  g : ℝ
  cω : ℝ
  ω : ℝ
  μ : ℝ
  δsep : ℝ
  Anet : ℝ
  θ : ℝ
  enet : ℝ
  eD : ℝ
  ς : ℝ
  eatt : ℝ
  cseed : ℝ

/-- The bump height (O9); this is the only constant depending on `ξ`. -/
def SiteConsts.bumpHeight (C : SiteConsts) (ξ : ℝ) : ℝ := ξ⁻¹ * Real.log C.θ⁻¹

/-- Construct the constants literally in the order (O1)–(O10). -/
def siteConsts {d : ℕ} (S : SiteData d) (Cnet v : ℝ) : SiteConsts := Id.run do
  let p := siteTExponent S
  let ct := siteTCoeff S
  let t₀ := ct * v ^ p
  let uLead := Routing.leadU S.seed.A S.seed.β S.boxHalfSide t₀
  let r := Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀
  let N := Routing.leadN d r
  let q₀ := sitePortDenom S
  let CN := siteCN d
  let CsE := siteCS S.seed.sE
  let cν := siteNuCoeff S
  let barν := cν * min (r ^ (3 * d + 2))
    (min ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s))
      ((v * S.seed.d₀ / (1000 * S.seed.HE)) ^ (1 / S.seed.sE)))
  let Mν := max 1 ⌈((q₀ : ℝ) * barν)⁻¹⌉₊
  let ν := 1 / ((q₀ : ℝ) * Mν)
  let g := 100 * d * ν
  let cω := siteOmegaCoeff d
  let ω := cω * ν ^ 4
  let μ := ω ^ 2 / (2 * √(d : ℝ))
  let δsep := siteDeltaFromNu ν
  let Anet := siteAnetFromNu S Cnet ν
  let θ := siteThetaFromNu S Cnet ν
  let enet := θ * Anet
  let eD := ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s)) / 2
  let ς := siteVarsigmaFrom S v ν θ
  let eatt := S.Hup * (4 * ς) ^ S.s
  let cseed := θ * S.seed.d₀ / 2
  return ⟨p, ct, t₀, uLead, r, N, q₀, CN, CsE, cν, barν, Mν, ν,
    g, cω, ω, μ, δsep, Anet, θ, enet, eD, ς, eatt, cseed⟩

end HigherDimLQGContinuity
