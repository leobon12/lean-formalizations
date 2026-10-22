import HigherDimLQGContinuity.LabelEvents.LabelExists
import HigherDimLQGContinuity.Labels.OrderSpec

/-!
# The fixed site data of the certificate (packet Q7b)

Source: blueprint Part B `b:def-sitedata` (F1)–(F6), `b:lem-label-exists` (the derived seed constants), and the
quantifier order of the frozen interface `SiteCertOfLabel` (Part B `b:thm-sitecert`): the mesh, the tree and the box
geometry are fixed by the site references (F1) alone, **before** the number of trials and the seed constants (F6).

* `q7bSeedMin mesh Ntr = (L/4) 8^{-Ntr}`, `L = δ_m/(64 d)` (the smallest seed radius, before the seed data).
* `q7bSeed`: the seed data (F6) of the interface constants `(H₀, σ₀, β₀, m, M, Hsd, σsd, Λ)` with the derived
  constants of `b:lem-label-exists` (`seedConstHE`, `seedConstA`, `seedConstEll0`, `seedConstEll1`, `seedConstD0`;
  `s_E = σsd`, `α = 1/β₀`, `β = σ₀`). The pin bound `K_pin` of (F6) is not read by any certificate clause (the unit
  bound `Λ` is an input of the interface); it is set to `0`.
* `q7bSiteData`: the site data with a given mesh, number of trials and seed data. Its edges, centres and box half-side
  depend on the mesh only (`rfl`).
* `q7b_finite_edge`, `q7bLabel`: finiteness of the tree edges; the label type at the constants `siteConsts S Cnet v`.
* `q7b_eD_cost`: `H_up (2 e_D(v))^s = v d₀/1000`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-- The smallest seed radius `(L/4) 8^{-Ntr}` of a mesh (`L = δ_m/(64 d)`). -/
def q7bSeedMin {Hup s ε₀ : ℝ} (mesh : SiteMeshData d Hup s ε₀) (Ntr : ℕ) : ℝ :=
  mesh.δm / (64 * d) / 4 * 8 ^ (-(Ntr : ℝ))

theorem q7bSeedMin_pos {Hup s ε₀ : ℝ} (hd : 1 ≤ d) (mesh : SiteMeshData d Hup s ε₀) (Ntr : ℕ) :
    0 < q7bSeedMin mesh Ntr := by
  unfold q7bSeedMin
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have := mesh.δm_pos
  have h8 : (0 : ℝ) < 8 ^ (-(Ntr : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  positivity

theorem q7bSeedMin_le_one {Hup s ε₀ : ℝ} (hd : 1 ≤ d) (mesh : SiteMeshData d Hup s ε₀) (Ntr : ℕ) :
    q7bSeedMin mesh Ntr ≤ 1 := by
  unfold q7bSeedMin
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hδ := mesh.δm_pos
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.2 hdR
  have hδ1 : mesh.δm ≤ 1 / 40 := by nlinarith [mesh.δm_small]
  have h8 : (8 : ℝ) ^ (-(Ntr : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
      have : (0 : ℝ) ≤ Ntr := Nat.cast_nonneg _
      linarith)
  have h8' : (0 : ℝ) ≤ 8 ^ (-(Ntr : ℝ)) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq : mesh.δm / (64 * d) / 4 ≤ 1 := by
    rw [div_div, div_le_one (by positivity)]
    nlinarith
  calc mesh.δm / (64 * d) / 4 * 8 ^ (-(Ntr : ℝ)) ≤ 1 * 1 :=
        mul_le_mul hq h8 h8' zero_le_one
    _ = 1 := by ring

/-- **The seed data (F6)** of the interface constants, with the derived constants of `b:lem-label-exists`. -/
def q7bSeed (H₀ σ₀ β₀ m M Hsd σsd Λ smin : ℝ) (hH₀ : 1 ≤ H₀) (hσ₀ : 0 < σ₀) (hσ₀1 : σ₀ < 1)
    (hβ₀ : 1 < β₀) (hm : 0 < m) (hmM : m < M) (hHsd : 1 ≤ Hsd) (hσsd : 0 < σsd) (hσsd1 : σsd ≤ 1)
    (hΛ : 1 ≤ Λ) (hsmin : 0 < smin) (hsmin1 : smin ≤ 1) : SiteSeedData where
  H₀ := H₀
  σ₀ := σ₀
  β₀ := β₀
  m := m
  M := M
  Hsd := Hsd
  σsd := σsd
  Kpin := 0
  Λ := Λ
  HE := seedConstHE Hsd σsd Λ smin
  sE := σsd
  A := seedConstA H₀ σ₀ β₀ m M smin
  α := 1 / β₀
  β := σ₀
  ℓ₀ := seedConstEll0 H₀ σ₀ β₀ m M Λ
  ℓ₁ := seedConstEll1 H₀ σ₀ β₀ M Λ
  d₀ := seedConstD0 H₀ σ₀ β₀ m M Λ
  H₀_ge := hH₀
  σ₀_pos := hσ₀
  σ₀_lt := hσ₀1
  β₀_gt := hβ₀
  m_pos := hm
  m_lt_M := hmM
  Hsd_ge := hHsd
  σsd_pos := hσsd
  σsd_le := hσsd1
  Λ_ge := hΛ
  HE_ge := one_le_seedConstHE hHsd hσsd.le hΛ hsmin hsmin1
  sE_pos := hσsd
  sE_le := hσsd1
  A_ge := one_le_seedConstA H₀ σ₀ β₀ m M smin
  α_pos := by
    have : 0 < β₀ := by linarith
    positivity
  α_le := by
    rw [div_le_one (by linarith)]
    exact hβ₀.le
  β_pos := hσ₀
  β_le := hσ₀1.le
  ℓ₀_pos := seedConstEll0_pos hm (by linarith)
  ℓ₀_le_ℓ₁ := seedConstEll0_le_seedConstEll1 hm.le hmM.le hΛ
  d₀_pos := seedConstD0_pos hm (by linarith)

/-- **The site data** with the reference constants (F1), a fixed mesh and tree, the number of trials and the seed
data (F6). -/
def q7bSiteData (Hup s Hlo b mc A0 : ℝ) (hHup : 1 ≤ Hup) (hs : 0 < s) (hs1 : s ≤ 1) (hHlo : 1 ≤ Hlo)
    (hb : 1 ≤ b) (hmc : 0 < mc) (hA0 : Hlo⁻¹ ≤ A0) (mesh : SiteMeshData d Hup s (siteEps0 mc Hlo))
    (Ntr : ℕ) (seed : SiteSeedData) : SiteData d where
  Hup := Hup
  s := s
  Hlo := Hlo
  b := b
  mc := mc
  A0 := A0
  Hup_ge := hHup
  s_pos := hs
  s_le := hs1
  Hlo_ge := hHlo
  b_ge := hb
  mc_pos := hmc
  A0_ge := hA0
  mesh := mesh
  Ntr := Ntr
  seed := seed

/-- The tree edges of the site data are finite. -/
theorem q7b_finite_edge (S : SiteData d) : Finite S.Edge := by
  have : Finite S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).to_subtype
  infer_instance

/-- The label type of the catalogue at the explicit constants `siteConsts S Cnet v`. -/
abbrev q7bLabel (S : SiteData d) (Cnet v : ℝ) : Type :=
  SiteLabel S (labelCellCutoff S (siteConsts S Cnet v).μ) (labelLeadCutoff (siteConsts S Cnet v).ν)
    (siteConsts S Cnet v).N (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν (siteConsts S Cnet v).r
    (Routing.gpC1 4)

theorem q7b_finite_label (S : SiteData d) (Cnet v : ℝ) : Finite (q7bLabel S Cnet v) := by
  have := q7b_finite_edge S
  have : ∀ e : S.Edge, Finite (EdgeLabel S e (labelCellCutoff S (siteConsts S Cnet v).μ)
      (labelLeadCutoff (siteConsts S Cnet v).ν) (siteConsts S Cnet v).N (siteConsts S Cnet v).μ
      (siteConsts S Cnet v).ν (siteConsts S Cnet v).r (Routing.gpC1 4)) := fun _ => inferInstance
  exact Pi.finite

/-- `H_up (2 e_D(v))^s = v d₀ / 1000`, where `e_D(v) = ½ (v d₀/(1000 H_up))^{1/s}` (Definition `b:def-order`). -/
theorem q7b_eD_cost (S : SiteData d) (Cnet : ℝ) {v : ℝ} (hv : 0 < v) :
    S.Hup * (2 * (siteConsts S Cnet v).eD) ^ S.s = v * S.seed.d₀ / 1000 := by
  have hH : 0 < S.Hup := by linarith [S.Hup_ge]
  have hs := S.s_pos
  have hB : 0 ≤ v * S.seed.d₀ / (1000 * S.Hup) := by
    have := S.seed.d₀_pos
    positivity
  change S.Hup * (2 * ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) / 2)) ^ S.s = v * S.seed.d₀ / 1000
  rw [show 2 * ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) / 2) =
      (v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) by ring, ← Real.rpow_mul hB,
    show 1 / S.s * S.s = 1 by field_simp, Real.rpow_one]
  field_simp

end HigherDimLQGContinuity
