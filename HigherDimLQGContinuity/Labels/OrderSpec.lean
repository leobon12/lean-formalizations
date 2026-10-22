import HigherDimLQGContinuity.Labels.OrderSpecC

/-!
# The complete corrected site-constant specification

`siteConsts_spec` assembles clauses (a)–(d) of blueprint `b:lem-order` with the
exponents authorized by ruling N29. The named polynomial fields below are
available directly to subsequent packets.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

/-- Ruling N29's generic polynomial clause with named fields. -/
structure SiteConstsPolynomial (C : SiteConsts) (v c Cmax K : ℝ) : Prop where
  t₀ : c * v ^ K ≤ C.t₀ ∧ C.t₀ ≤ 1
  r : c * v ^ K ≤ C.r ∧ C.r ≤ 1
  ν : c * v ^ K ≤ C.ν ∧ C.ν ≤ 1
  g : c * v ^ K ≤ C.g ∧ C.g ≤ 1
  ω : c * v ^ K ≤ C.ω ∧ C.ω ≤ 1
  μ : c * v ^ K ≤ C.μ ∧ C.μ ≤ 1
  δsep : c * v ^ K ≤ C.δsep ∧ C.δsep ≤ 1
  θ : c * v ^ K ≤ C.θ ∧ C.θ ≤ 1
  ς : c * v ^ K ≤ C.ς ∧ C.ς ≤ 1
  cseed : c * v ^ K ≤ C.cseed ∧ C.cseed ≤ 1
  Anet : C.Anet ≤ Cmax * v ^ (-K)
  N : (C.N : ℝ) ≤ Cmax * v ^ (-K)

/-- Clause (a): lead hypotheses and separation scales. -/
def SiteConstsA {d : ℕ} (S : SiteData d) (C : SiteConsts) : Prop :=
  C.ν ≤ Routing.gpC0 d * (C.r / (4 * √(d : ℝ))) /
    (2 * (C.N : ℝ) + 5) ^ 3 ∧
  √(d : ℝ) * C.ν ≤ C.r ∧ C.g ≤ C.r / 8 ∧
  C.ω ≤ min (C.r / (8 * √(d : ℝ)))
    (Routing.gpC1 4 * C.ν ^ 3 / 8) ∧
  (√(d : ℝ) / 2) * C.μ ≤ C.ω / 4 ∧
  C.δsep ≤ min (C.r / 2)
    (min (C.g / 2)
      (min (Routing.gpC1 4 * C.ν ^ 3 / 2) (S.boxHalfSide / 2))) ∧
  2 * C.g + 8 * C.ς < S.seedMin / 4

/-- Clause (b): gate width and attached-lead cost. -/
def SiteConstsB {d : ℕ} (S : SiteData d) (C : SiteConsts) (v : ℝ) : Prop :=
  S.seed.A * (2 * C.t₀) ^ S.seed.α + C.g + C.ω + C.ς ≤
    min C.eD (1 / 8) ∧
  2 * siteCS S.seed.sE * S.seed.HE * C.g ^ S.seed.sE +
    2 * C.t₀ * S.seed.ℓ₁ ≤ v * S.seed.d₀ / 1000

/-- Clause (c): network and attachment scales. -/
def SiteConstsC {d : ℕ} (S : SiteData d) (C : SiteConsts) (v : ℝ) : Prop :=
  C.enet ≤ siteEps0 S.mc S.Hlo ∧
  4 * C.ς ≤ C.δsep ∧ C.ς ≤ C.ω / 4 ∧
  2 * C.eatt + C.enet < S.Hlo⁻¹ * (C.δsep / 2) ^ S.b ∧
  S.seed.HE * (4 * C.ς) ^ S.seed.sE ≤
    v * C.θ * S.seed.d₀ / 1000

/-- All of (a)–(d) with a single fixed threshold and fixed polynomial
constants. `SitePowerBounds` and the displayed `θ` comparison give exactly
the corrected exponents `q_ν`, `8d+3b` and `q_ς`. -/
theorem siteConsts_spec {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) (hCnet : 0 < Cnet) :
    ∃ vsite c Cmax K : ℝ,
      0 < vsite ∧ vsite ≤ 1 / 100 ∧ 0 < c ∧ 0 < Cmax ∧ 0 < K ∧
      SitePowerBounds (fun v => (siteConsts S Cnet v).r) (siteRExponent S) ∧
      SitePowerBounds (fun v => (siteConsts S Cnet v).ν) (siteNuExponent S) ∧
      (∃ cθ Cθ : ℝ, 0 < cθ ∧ 0 < Cθ ∧
        ∀ v, 0 < v → v ≤ 1 →
          cθ * (siteConsts S Cnet v).ν ^ siteThetaExponent S ≤
            (siteConsts S Cnet v).θ ∧
          (siteConsts S Cnet v).θ ≤
            Cθ * (siteConsts S Cnet v).ν ^ siteThetaExponent S) ∧
      SitePowerBounds (fun v => (siteConsts S Cnet v).ς)
        (siteVarsigmaExponent S) ∧
      (∀ v, 0 < v → v ≤ vsite →
        let C := siteConsts S Cnet v
        SiteConstsA S C ∧ SiteConstsB S C v ∧ SiteConstsC S C v ∧
          SiteConstsPolynomial C v c Cmax K) := by
  obtain ⟨va, hva, hva100, ha⟩ := siteConsts_spec_a S hd Cnet hCnet
  obtain ⟨vb, hvb, hvb100, hb⟩ := siteConsts_spec_b S hd Cnet
  obtain ⟨vp, c, Cmax, K, hvp, hvp1, hc, hCmax, hK, hp⟩ :=
    siteConsts_polynomial S hd Cnet hCnet
  let vsite := min va (min vb (min vp (1 / 100 : ℝ)))
  have hvsite : 0 < vsite := by
    dsimp [vsite]
    exact lt_min hva (lt_min hvb (lt_min hvp (by norm_num)))
  have hvsite100 : vsite ≤ 1 / 100 := by
    dsimp [vsite]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨vsite, c, Cmax, K, hvsite, hvsite100, hc, hCmax, hK,
    siteConsts_r_power_corrected S hd Cnet,
    siteConsts_ν_power S hd Cnet,
    siteConsts_θ_nu_power S hd Cnet hCnet,
    siteConsts_ς_power S hd Cnet hCnet, ?_⟩
  intro v hv hvsite'
  let C := siteConsts S Cnet v
  have hva' : v ≤ va := hvsite'.trans (min_le_left _ _)
  have hvb' : v ≤ vb := hvsite'.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hvp' : v ≤ vp := hvsite'.trans
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hv1 : v ≤ 1 :=
    (hvsite'.trans hvsite100).trans (by norm_num)
  have hA : SiteConstsA S C := ha v hv hva'
  have hB : SiteConstsB S C v := hb v hv hvb'
  have hC : SiteConstsC S C v := siteConsts_spec_c S hd Cnet v hCnet hv hv1
  obtain ⟨hsmall, hAnet, hN⟩ := hp v hv hvp'
  have hpoly : SiteConstsPolynomial C v c Cmax K := by
    exact ⟨hsmall 0, hsmall 1, hsmall 2, hsmall 3, hsmall 4,
      hsmall 5, hsmall 6, hsmall 7, hsmall 8, hsmall 9, hAnet, hN⟩
  exact ⟨hA, hB, hC, hpoly⟩

end HigherDimLQGContinuity
