import HigherDimLFPP.Lower.PolyMeasure
import HigherDimLFPP.Lower.WNMax
import HigherDimLFPP.Var.Lemma22Family

/-!
# The objects of Lemmas 5.2 and 5.3 (source §5.1, (5.2), (5.6), (5.7))

Packet P-L3 (ruling H6; audit HA4 §1 and "Details for later use" D1, D5, D6).

* `ampl K e δ f v`: the amplitude `a_{f,δ}` of Lemma 5.1, defined canonically as the unique
  zero of `S_δ - 1` in `(0, a_f + 1)` (finding HA4-9); `ampl_spec` transfers P-L1's `lemma51`
  (convergence `a_{f,δ} → a_f` and the polygon geometry `EqualEdgeData`).
* `LowerData d`: the data fixed before `δ` (source "the order of choices", HA4 §1): the block
  level `n`, the padding `g` (`K = 2^{n+g}`), the energy level `e = e_{n,d}`, the family
  `f_0, …, f_J` of Lemma 2.2 and the unit vector `v ∈ ℝ^{d-1}`.  `LowerData.Hyp D C` records the
  properties (2.9) of the family (with constant `C`), `e ≤ C n` (2.8), `g ≥ 1`,
  `2^g ≥ (n+2)^{20}` and `‖v‖ = 1`.
* For `δ > 0`: `q = (1 + δ²E₀)/K`, `ρ = δL` with `L = (n+2)^4` (5.2); the equal-edge polygons
  `vert δ j` of Lemma 5.1, their normalized arclength `ν δ j`, the band `H = H_{ρq,ρ}` (5.6), the
  white-noise vectors `selVec κ δ j` of the selector statistics `-δ^{-1/2}⟨H, ν_j - ν₀⟩` (5.7) and
  `w κ δ = w_{n,d,δ} = E max_j (-δ^{-1/2}⟨H, ν_j - ν₀⟩)` (5.7).
* The Riemann version (HA4 D5 step 6): `νR δ N j = ν_j^N = (KN)⁻¹ Σ_{i,l} δ_{T_i^j(l/N e₁)}`,
  `νR₀ N = ν₀^N = N⁻¹ Σ_l δ_{(l/N) e₁}`, `selVecR`, and `wR κ δ N = w^N_{n,d,δ}`.

`w` and `wR` are Gaussian expected maxima of explicit Gram matrices (`gaussianExpectedMax`);
for every white noise they are the expected maxima of the white-noise pairings
(`integral_iSup_W_eq_gEM`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP.Lower

open LQGDimension (gaussianExpectedMax)

variable {d : ℕ}

/-! ## The amplitude of Lemma 5.1 -/

/-- The amplitude `a_{f,δ}`: the unique zero of `S_δ - 1` in `(0, a_f + 1)` (junk `a_f` if there
is none). -/
def ampl (K : ℕ) (e δ : ℝ) (f : ℝ → Rd (d - 1)) (v : Rd (d - 1)) : ℝ := by
  classical
  exact if h : ∃ a ∈ Ioo 0 (aLim e f + 1), sumHIncr K (qOf K (e + 1) δ) δ f v a = 1 then
    h.choose else aLim e f

/-- **Lemma 5.1 for the canonical amplitude** (P-L1's `lemma51`): `a_{f,δ} → a_f`, and for small
`δ` the amplitude lies in `(0, a_f + 1)` and the polygon satisfies `EqualEdgeData` with
`E₀ = e + 1`, `M₀ = √e + 1` and angle constant `√2 c₁`. -/
theorem ampl_spec (hd : 0 < d) {n g : ℕ} (hg : 1 ≤ g) {e : ℝ} {f : ℝ → Rd (d - 1)}
    (hf : f ∈ Vg (Rd (d - 1)) n) (hfe : energy f ≤ e) {v : Rd (d - 1)} (hv : ‖v‖ = 1)
    (hK : √(2 * (e + 1)) + 1 ≤ ((2 ^ (n + g) : ℕ) : ℝ)) :
    Tendsto (fun δ => ampl (2 ^ (n + g)) e δ f v) (𝓝[>] 0) (𝓝 (aLim e f)) ∧
      ∃ δ₁ > 0, ∀ δ ∈ Ioo 0 δ₁, ampl (2 ^ (n + g)) e δ f v ∈ Ioo 0 (aLim e f + 1) ∧
        EqualEdgeData (2 ^ (n + g)) δ (qOf (2 ^ (n + g)) (e + 1) δ) (e + 1) (√e + 1)
          (√2 * incrConst n e)
          (eqVert (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v
            (ampl (2 ^ (n + g)) e δ f v)) := by
  classical
  obtain ⟨δ₁, hδ₁, a, ha_lim, ha⟩ := lemma51 hd hg hf hfe hv hK
  have heq : ∀ δ ∈ Ioo 0 δ₁, ampl (2 ^ (n + g)) e δ f v = a δ := by
    intro δ hδ
    obtain ⟨hmem, hS, huniq, -, -⟩ := ha δ hδ
    have hex : ∃ b ∈ Ioo 0 (aLim e f + 1),
        sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v b = 1 := ⟨a δ, hmem, hS⟩
    have h1 : ampl (2 ^ (n + g)) e δ f v = hex.choose := by
      unfold ampl
      exact dite_eq_left hex
    rw [h1]
    exact huniq _ hex.choose_spec.1 hex.choose_spec.2
  refine ⟨ha_lim.congr' ?_, δ₁, hδ₁, fun δ hδ => ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT hδ₁] with δ hδ
    exact (heq δ hδ).symm
  · rw [heq δ hδ]
    exact ⟨(ha δ hδ).1, (ha δ hδ).2.2.2.1⟩

/-! ## The data of the lower comparison -/

/-- The data fixed before `δ` (source §5.1): block level `n`, padding `g`, energy level `e`,
the family `f_0, …, f_J` of Lemma 2.2 and a unit vector `v ∈ ℝ^{d-1}`. -/
structure LowerData (d : ℕ) where
  /-- The block level `n`. -/
  n : ℕ
  /-- The padding exponent `g` (`K = 2^{n+g}`). -/
  g : ℕ
  /-- The energy level `e = e_{n,d}`. -/
  e : ℝ
  /-- The family has `J + 1` profiles. -/
  J : ℕ
  /-- The profiles `f_j ∈ V_{n,d}` of Lemma 2.2. -/
  f : Fin (J + 1) → ℝ → Rd (d - 1)
  /-- The padding direction `v ∈ ℝ^{d-1}`. -/
  v : Rd (d - 1)

namespace LowerData

variable (D : LowerData d)

/-- `K = 2^{n+g}` (5.2). -/
abbrev K : ℕ := 2 ^ (D.n + D.g)

/-- `L = (n+2)^4` (5.2). -/
abbrev L : ℝ := ((D.n : ℝ) + 2) ^ 4

/-- `E₀ = e + 1` (5.2). -/
abbrev E₀ : ℝ := D.e + 1

/-- `q = s/K = (1 + δ²E₀)/K` (5.2). -/
abbrev q (δ : ℝ) : ℝ := qOf D.K D.E₀ δ

/-- `ρ = δL` (5.2). -/
abbrev ρ (δ : ℝ) : ℝ := δ * D.L

/-- The amplitudes `a_{j,δ}` (Lemma 5.1). -/
def amp (δ : ℝ) (j : Fin (D.J + 1)) : ℝ := ampl D.K D.e δ (D.f j) D.v

/-- The vertices of the equal-edge polygon `Q_{j,δ}` (Lemma 5.1). -/
def vert (δ : ℝ) (j : Fin (D.J + 1)) : ℕ → Rd d :=
  eqVert D.K (D.q δ) δ (D.f j) D.v (D.amp δ j)

/-- The padded profile `g_{j,δ} = f_j + a_{j,δ} ψ_K v`. -/
def prof (δ : ℝ) (j : Fin (D.J + 1)) : ℝ → Rd (d - 1) := padProf D.K (D.f j) D.v (D.amp δ j)

/-- The limit padded profile `g_j = f_j + a_j ψ_K v`, `a_j = (2(E₀ - E(f_j)))^{1/2}`. -/
def prof₀ (j : Fin (D.J + 1)) : ℝ → Rd (d - 1) := padProf D.K (D.f j) D.v (aLim D.e (D.f j))

/-- `ν_j = ν_{Q_{j,δ}}`: normalized arclength of the equal-edge polygon. -/
def ν (δ : ℝ) (j : Fin (D.J + 1)) : Measure (Rd d) := polyM D.K (D.vert δ j)

/-- The band `(ρq, ρ)` of `H = H_{ρq,ρ}` (5.6). -/
def band (δ : ℝ) : Set ℝ := Ioo (D.ρ δ * D.q δ) (D.ρ δ)

/-- The white-noise vector of the selector statistic `-δ^{-1/2}⟨H, ν_j - ν₀⟩` (5.7), with
`ν₀ = 𝓛` the uniform measure on `[0,1] e₁`. -/
def selVec (κ : Rd d → ℝ) (δ : ℝ) (j : Fin (D.J + 1)) : WN d :=
  -((Real.sqrt δ)⁻¹ • bandVecM κ (D.band δ) (D.ν δ j) (Upper.segMeasure 0 (e₁ d)))

/-- `w_{n,d,δ} = E max_j (-δ^{-1/2}⟨H, ν_j - ν₀⟩)` (5.7). -/
def w (κ : Rd d → ℝ) (δ : ℝ) : ℝ :=
  gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
    (fun j k => ⟪D.selVec κ δ j, D.selVec κ δ k⟫) 0

/-- The left Riemann measure `ν_j^N = (KN)⁻¹ Σ_{i<K, l<N} δ_{T_i^j((l/N) e₁)}`. -/
def νR (δ : ℝ) (N : ℕ) (j : Fin (D.J + 1)) : Measure (Rd d) :=
  atomM (Finset.range D.K ×ˢ Finset.range N) (fun _ => 1 / ((D.K : ℝ) * N))
    (fun x => (edgeSim (D.q δ) (D.vert δ j) x.1).app (refPt N x.2))

end LowerData

/-- The left Riemann measure `ν₀^N = N⁻¹ Σ_{l<N} δ_{(l/N) e₁}` of `ν₀ = 𝓛`. -/
def refM (d N : ℕ) : Measure (Rd d) := atomM (Finset.range N) (fun _ => 1 / (N : ℝ)) (refPt N)

namespace LowerData

variable (D : LowerData d)

/-- The white-noise vector of the Riemann selector statistic `-δ^{-1/2}⟨H, ν_j^N - ν₀^N⟩`. -/
def selVecR (κ : Rd d → ℝ) (δ : ℝ) (N : ℕ) (j : Fin (D.J + 1)) : WN d :=
  -((Real.sqrt δ)⁻¹ • bandVecM κ (D.band δ) (D.νR δ N j) (refM d N))

/-- `w^N_{n,d,δ} = E max_j (-δ^{-1/2}⟨H, ν_j^N - ν₀^N⟩)` (HA4 D5 step 6). -/
def wR (κ : Rd d → ℝ) (δ : ℝ) (N : ℕ) : ℝ :=
  gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
    (fun j k => ⟪D.selVecR κ δ N j, D.selVecR κ δ N k⟫) 0

/-- **The standing hypotheses** on the data with constant `C`: the properties (2.9) of the
Lemma 2.2 family `F_{n,d}` at energy level `e` (membership, energy, the gain
`E max_j G(f_j) ≥ 4e - 1`, `log(2(J+1)) ≤ C n 2ⁿ`), the bound `e ≤ C n` of (2.8), the padding
`g ≥ 1` with `2^g ≥ (n+2)^{20}` (source (5.1)), and `‖v‖ = 1`. -/
structure Hyp (C : ℝ) : Prop where
  one_le_n : 1 ≤ D.n
  one_le_g : 1 ≤ D.g
  pad : ((D.n : ℝ) + 2) ^ 20 ≤ 2 ^ D.g
  mem : ∀ j, D.f j ∈ Vg (Rd (d - 1)) D.n
  energy_le : ∀ j, energy (D.f j) ≤ D.e
  e_le : D.e ≤ C * D.n
  gem : 4 * D.e - 1 ≤ gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
    (fun j k => gCov (D.f j) (D.f k)) (fun _ => 0)
  log_card : Real.log (2 * ((D.J : ℝ) + 1)) ≤ C * D.n * 2 ^ D.n
  v_norm : ‖D.v‖ = 1

variable {D}

theorem Hyp.e_nonneg {C : ℝ} (h : D.Hyp C) : 0 ≤ D.e :=
  (Var.energy_nonneg (D.f 0)).trans (h.energy_le 0)

theorem Hyp.C_nonneg {C : ℝ} (h : D.Hyp C) : 0 ≤ C := by
  have h1 := h.e_nonneg.trans h.e_le
  have hn : (0 : ℝ) < D.n := by exact_mod_cast h.one_le_n
  by_contra hC
  push Not at hC
  nlinarith

theorem K_pos : 0 < D.K := by positivity

theorem K_cast_pos : (0 : ℝ) < D.K := by exact_mod_cast D.K_pos

theorem L_pos : 0 < D.L := by positivity

end LowerData

end HigherDimLFPP.Lower
