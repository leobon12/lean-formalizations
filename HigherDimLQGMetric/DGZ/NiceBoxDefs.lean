import HigherDimLQGMetric.DGZ.SuperExpAround

/-!
# DGZ §5.1: nice and bad boxes (Definition 5.3′) — definitions (packet L4a1)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), §5.1: the constants (5.3)–(5.7), Definition
5.3 (TeX l. 2103–2128, p. 41) and the events `𝒥₁`, `𝒥₂` of (5.21); planning audit
`planning/audits/MA7-ref2-sections-4-6.md`, §5 row L4a1, Details (a) D-5.3 (Definition 5.3′, Remark
5.4′; gaps G9, G11, G24) and D-OSC (the oscillation conditions (1′), (a′), `𝒥₂′`); blueprint Part C
(`blueprint/sections/ref2-compare.tex`: Convention `r2:conv:coarse`, Definitions `r2:def:oscconds`,
`r2:def:nice`; ruling M23).

Everything here is **deterministic**: the conditions are properties of one family `H : ℕ → Rd d → ℝ`
of fields, read as `h_q = H q` (for a dyadic realization, `H q = h_q` is the given version of
`H_{2^{-q}, 1}`), and every band is a pointwise difference `h_{q', q} := H q - H q'` (blueprint
Convention `r2:conv:standing`(iii), ruling M23(ii)), so `h_{q'', q} = h_{q'', q'} + h_{q', q}` holds
identically. The random events are the preimages `{ω | NiceBox p (fun q z => H q z ω) j u}`.

* `dgzAlpha`, `dgzLambda`, `dgzR`, `dgzSeq`, `dgzLevel`: `α = Q²/4 - d/2`, `λ = α/(4(α+d))`, `R =
  ⌊100 r₀⌋ + 100`, the exponents `a₀ = 0`, `a₁ = K⁴`, `a_{i+1} = ⌊(1+λ)a_i⌋ + 1` and the top level
  `m = sup{i ≥ 1 : a_i ≤ (1-λ) n}` (DGZ (5.3)–(5.5)).
* `NiceParams`: the parameters `ξ, Q, θ, ε, L, K, R, n, k` and the exponent sequence `a` (any
  sequence; DGZ's is `dgzSeq (dgzLambda d Q) K`, see `dgzParams`); `NiceParams.s i = 2^{-(n - a_i)}`
  is the scale `s_i = 2^{-n + a_i}` and the `a_i`-boxes are `obox (latPt (s i) u) (s i)`, `u ∈ ℤ^d`
  (`𝒴_i = s_i ℤ^d`).
* The conditions of Definition 5.3′ (MA7 D-5.3 with D-OSC):
  - `NiceOscOne` (1′): `osc_{B̄_{3s₀}(y)} h_{n-a₁,n} ≤ L` for `y ∈ 𝒴₀ ∩ B_{s₁}(x)`;
  - `NiceAcrossOne` (3): `D_{n,n+k}(across B_{2s₀}(y) \ B_{s₀}(y)) > L⁻¹ 2^{-n-(1-ξQ+ε)k}`;
  - `NiceOscCond` (a′): `osc_{B̄_{8s_i}(y)} h_{n-a_j,n-a_{j-1}} ≤ K √a_{j-1} 2^{-(a_{j-1}-a_i)}` for
    `0 ≤ i ≤ j-1`, `y ∈ 𝒴_i ∩ B_{4s_j}(x)`;
  - `NiceCert` (`Cert_{j-1}(z)`): L3c3's `aroundCertAt` at level `N = a_{j-1}`, with `δ = θ`, radii
    `(4R, 2R)`, for the two bands `h_{n-N, n-N+m(N)}` and `h_{n-N+m(N), n}` of `h_{n-N,n}` rescaled
    by `s_{j-1}` around `z` (`certCoarse`, `certFine`; `m(N) = superScale N`). No cube enters.
  - `NiceCEvent` (`𝒞(x,z)`): the across term `D_{n-a_j,n}(across B_{4s_j}(x) \ B_{2s_j}(x)) >
    2^{-n+(ξQ-θ)a_j}`, `Cert_{j-1}(z)`, and `h_{n-a_j,n-a_{j-1}} ≤ s_j*` on `B̄_{4Rs_{j-1}}(z)`.
* `NiceBox p H j u`: the `a_j`-box `B_{s_j}(s_j u)` is nice (levels `1 ≤ j`; level `0` is `True`):
  level 1 is (1′) ∧ (3); level `j ≥ 2` is (a′) ∧ ((b) ∨ (c′)), with (b) "all `a_{j-1}`-boxes
  contained in `B_{s_j}(x)` are nice" and (c′) "there is `z ∈ 𝒴_{j-1} ∩ B_{s_j}(x)` such that every
  bad `a_{j-1}`-box contained in `B_{s_j}(x)` is contained in `B_{R s_{j-1}}(z)`, and `𝒞(x,z)`".
  Condition (2) of [2] is dropped (MA7 D-5.3: only used for Lemma 5.12(2)).
* `EventJ1 p H m` (`𝒥₁`): every `a_m`-box contained in `B₂(0)` is nice; `EventJ2' p H m` (`𝒥₂′`,
  D-OSC): `osc_{B̄_{8s_i}(y)} h_{n-a_m} ≤ K √a_m 2^{-(a_m - a_i)}` for `0 ≤ i ≤ m`, `y ∈ 𝒴_i ∩
  B₃(0)`.

Formulation notes (no strengthening of the source):
* the supremum condition of `𝒞(x,z)` is written `h ≤ s_j*` pointwise on the closed box (DGZ: `sup <
  s_j*`; the non-strict form is weaker, its complement is `{∃ z, s_j* < h(z)}`, the event of L3b2's
  `prob_smallBox_sup_le`, and the deterministic consequence only uses `≤`);
* the oscillation `osc_A f ≤ c` is written `∀ z w ∈ A, |f z - f w| ≤ c`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox obox_subset_cbox)

variable {d : ℕ}

/-! ## The coarse-graining constants (DGZ (5.3)–(5.7)) -/

/-- `α = Q²/4 - d/2` (DGZ (5.3)). -/
def dgzAlpha (d : ℕ) (Q : ℝ) : ℝ := Q ^ 2 / 4 - d / 2

/-- `λ = α/(4(α + d))` (DGZ (5.3)). -/
def dgzLambda (d : ℕ) (Q : ℝ) : ℝ := dgzAlpha d Q / (4 * (dgzAlpha d Q + d))

/-- `R = ⌊100 r₀⌋ + 100` (DGZ (5.3)), for a support radius `r₀` of the kernel. -/
def dgzR (r₀ : ℝ) : ℕ := ⌊100 * r₀⌋₊ + 100

/-- The scale exponents of DGZ (5.4): `a₀ = 0` (MA7 D-OSC), `a₁ = K⁴` and
`a_{i+1} = ⌊(1+λ) a_i⌋ + 1` for `i ≥ 1`. -/
def dgzSeq (lam : ℝ) (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => K ^ 4
  | i + 2 => ⌊(1 + lam) * (dgzSeq lam K (i + 1) : ℝ)⌋₊ + 1

/-- The top level `m = sup{i ≥ 1 : a_i ≤ (1 - λ) n}` (DGZ (5.5)). -/
def dgzLevel (lam : ℝ) (K n : ℕ) : ℕ :=
  sSup {i : ℕ | 1 ≤ i ∧ (dgzSeq lam K i : ℝ) ≤ (1 - lam) * n}

/-! ## Parameters and scales -/

/-- The parameters of DGZ §5 (Definition 5.3′): the LFPP parameters `ξ, Q`, the margins `θ`
(Lemma 5.6: the certificate and the across term of `𝒞(x,z)`) and `ε` (Prop 5.1: condition (3)),
the constants `L, K, R`, the scales `n` (`h_n`) and `k` (`h_{n,n+k}`), and the exponent sequence
`a` (`s_i = 2^{-n+a_i}`; DGZ's sequence is `dgzSeq (dgzLambda d Q) K`, see `dgzParams`). -/
structure NiceParams where
  /-- the LFPP parameter `ξ` -/
  ξ : ℝ
  /-- the exponent `Q` -/
  Q : ℝ
  /-- the margin `θ` of Lemma 5.6 -/
  θ : ℝ
  /-- the margin `ε` of Proposition 5.1 (condition (3)) -/
  ε : ℝ
  /-- the constant `L` of conditions (1′) and (3) -/
  L : ℝ
  /-- the constant `K` of (a′), `𝒥₂′` and `s_j*` -/
  K : ℕ
  /-- the constant `R` (the boxes `B_{R s_{j-1}}(z)` and the around shells) -/
  R : ℕ
  /-- the scale `n` -/
  n : ℕ
  /-- the extra scale `k` -/
  k : ℕ
  /-- the scale exponents `a_i` -/
  a : ℕ → ℕ

/-- DGZ's parameters: the sequence `a = dgzSeq λ K` with `λ = dgzLambda d Q`. -/
def dgzParams (d : ℕ) (ξ Q θ ε L : ℝ) (K R n k : ℕ) : NiceParams :=
  ⟨ξ, Q, θ, ε, L, K, R, n, k, dgzSeq (dgzLambda d Q) K⟩

namespace NiceParams

/-- The scale `s_i = 2^{-n+a_i}`, written `(1/2)^{n - a_i}` (equal when `a_i ≤ n`); the
`a_i`-boxes are `obox (latPt (s i) u) (s i)`, `u ∈ ℤ^d`. -/
def s (p : NiceParams) (i : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (p.n - p.a i)

/-- `s_j* = Q(a_j - a_{j-1}) log 2 - (θ/ξ)(a_j + a_{j-1}) log 2 - K^{3/2} √a_j / ξ` (DGZ's `s_j`,
Lemma 5.6; MA7 D-5.3). -/
def supLevel (p : NiceParams) (j : ℕ) : ℝ :=
  p.Q * ((p.a j : ℝ) - p.a (j - 1)) * Real.log 2 -
    p.θ / p.ξ * ((p.a j : ℝ) + p.a (j - 1)) * Real.log 2 -
      (p.K : ℝ) ^ ((3 : ℝ) / 2) * √(p.a j : ℝ) / p.ξ

/-- `t* = e^{ξ s_j*} t_{j-1}` with `t_{j-1} = 2^{-n+(ξQ+θ)a_{j-1}}` (MA7 D-5.3, the threshold of the
deterministic consequence of `𝒞(x,z)`). -/
def tStar (p : NiceParams) (j : ℕ) : ℝ :=
  Real.exp (p.ξ * p.supLevel j) * (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q + p.θ) * p.a (j - 1))

/-- The split index `n - a_i + m(a_i)` (`m(N) = superScale N`) of `h_{n-a_i,n}` into its coarse
band `h_{n-a_i, n-a_i+m(a_i)}` and its fine band `h_{n-a_i+m(a_i), n}`. -/
def certIdx (p : NiceParams) (i : ℕ) : ℕ := p.n - p.a i + superScale (p.a i)

end NiceParams

/-! ## The conditions of Definition 5.3′ -/

/-- Condition **(1′)** (MA7 D-OSC) for the `a₁`-box `B_{s₁}(s₁ u)`:
`osc_{B̄_{3s₀}(y)} h_{n-a₁,n} ≤ L` for every `y ∈ 𝒴₀ ∩ B_{s₁}(s₁ u)`. -/
def NiceOscOne (p : NiceParams) (H : ℕ → Rd d → ℝ) (u : Zd d) : Prop :=
  ∀ v : Zd d, latPt (p.s 0) v ∈ obox (latPt (p.s 1) u) (p.s 1) →
    ∀ z ∈ cbox (latPt (p.s 0) v) (3 * p.s 0), ∀ w ∈ cbox (latPt (p.s 0) v) (3 * p.s 0),
      |(H p.n z - H (p.n - p.a 1) z) - (H p.n w - H (p.n - p.a 1) w)| ≤ p.L

/-- Condition **(3)** of [2, Def. 5.3] for the `a₁`-box `B_{s₁}(s₁ u)`:
`D_{n,n+k}(across B_{2s₀}(y) \ B_{s₀}(y)) > L⁻¹ 2^{-n-(1-ξQ+ε)k}` for every
`y ∈ 𝒴₀ ∩ B_{s₁}(s₁ u)`. -/
def NiceAcrossOne (p : NiceParams) (H : ℕ → Rd d → ℝ) (u : Zd d) : Prop :=
  ∀ v : Zd d, latPt (p.s 0) v ∈ obox (latPt (p.s 1) u) (p.s 1) →
    p.L⁻¹ * (2 : ℝ) ^ (-(p.n : ℝ) - (1 - p.ξ * p.Q + p.ε) * p.k) <
      acrossDist p.ξ (fun z => H (p.n + p.k) z - H p.n z) (latPt (p.s 0) v) (2 * p.s 0) (p.s 0)

/-- Condition **(a′)** (MA7 D-OSC) for the `a_j`-box `B_{s_j}(s_j u)` (`j ≥ 2`):
`osc_{B̄_{8s_i}(y)} h_{n-a_j,n-a_{j-1}} ≤ K √a_{j-1} 2^{-(a_{j-1}-a_i)}` for every `0 ≤ i ≤ j-1` and
`y ∈ 𝒴_i ∩ B_{4s_j}(s_j u)`. -/
def NiceOscCond (p : NiceParams) (H : ℕ → Rd d → ℝ) (j : ℕ) (u : Zd d) : Prop :=
  ∀ i < j, ∀ v : Zd d, latPt (p.s i) v ∈ obox (latPt (p.s j) u) (4 * p.s j) →
    ∀ z ∈ cbox (latPt (p.s i) v) (8 * p.s i), ∀ w ∈ cbox (latPt (p.s i) v) (8 * p.s i),
      |(H (p.n - p.a (j - 1)) z - H (p.n - p.a j) z) -
          (H (p.n - p.a (j - 1)) w - H (p.n - p.a j) w)| ≤
        p.K * √(p.a (j - 1) : ℝ) * (2 : ℝ)⁻¹ ^ (p.a (j - 1) - p.a i)

/-- The coarse band of `h_{n-a_i,n}` rescaled by `s_i` around `z`:
`w ↦ h_{n-a_i, n-a_i+m(a_i)}(z + s_i w)` (a version of `H_{2^{-m(a_i)},1}` for a white noise). -/
def certCoarse (p : NiceParams) (H : ℕ → Rd d → ℝ) (i : ℕ) (z : Rd d) : Rd d → ℝ :=
  fun w => H (p.certIdx i) (z + p.s i • w) - H (p.n - p.a i) (z + p.s i • w)

/-- The fine band of `h_{n-a_i,n}` rescaled by `s_i` around `z`:
`w ↦ h_{n-a_i+m(a_i), n}(z + s_i w)` (a version of `H_{2^{-a_i}, 2^{-m(a_i)}}` for a white noise).
-/
def certFine (p : NiceParams) (H : ℕ → Rd d → ℝ) (i : ℕ) (z : Rd d) : Rd d → ℝ :=
  fun w => H p.n (z + p.s i • w) - H (p.certIdx i) (z + p.s i • w)

/-- The certificate **`Cert_i(z)`** (MA7 D-5.3, blueprint Definition `r2:def:nice`): L3c3's
`aroundCertAt` at level `N = a_i`, with `δ = θ` and radii `(r₁, r₂) = (4R, 2R)`, evaluated at the
coarse and fine bands of `h_{n-a_i,n}` rescaled by `s_i` around `z`. It involves no cube. -/
def NiceCert (p : NiceParams) (H : ℕ → Rd d → ℝ) (i : ℕ) (z : Rd d) : Prop :=
  aroundCertAt p.ξ p.Q p.θ (4 * p.R) (2 * p.R) (p.a i) (certCoarse p H i z) (certFine p H i z)

/-- The event **`𝒞(x,z)`** (MA7 D-5.3) for `x = s_j u` and `z = s_{j-1} w`:
`D_{n-a_j,n}(across B_{4s_j}(x) \ B_{2s_j}(x)) > 2^{-n+(ξQ-θ)a_j}`, `Cert_{j-1}(z)`, and
`h_{n-a_j,n-a_{j-1}} ≤ s_j*` on `B̄_{4R s_{j-1}}(z)`. -/
def NiceCEvent (p : NiceParams) (H : ℕ → Rd d → ℝ) (j : ℕ) (u w : Zd d) : Prop :=
  (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) <
      acrossDist p.ξ (fun z => H p.n z - H (p.n - p.a j) z) (latPt (p.s j) u) (4 * p.s j)
        (2 * p.s j) ∧
    NiceCert p H (j - 1) (latPt (p.s (j - 1)) w) ∧
    ∀ z ∈ cbox (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1)),
      H (p.n - p.a (j - 1)) z - H (p.n - p.a j) z ≤ p.supLevel j

/-- **Nice boxes** (DGZ Definition 5.3, corrected: MA7 D-5.3 Definition 5.3′, blueprint
`r2:def:nice`): `NiceBox p H j u` says that the `a_j`-box `B_{s_j}(s_j u)` is nice.
* Level 1: (1′) and (3).
* Level `j ≥ 2`: (a′), and either (b) every `a_{j-1}`-box contained in `B_{s_j}(s_j u)` is nice, or
  (c′) there is `z = s_{j-1} w ∈ B_{s_j}(s_j u)` such that every bad `a_{j-1}`-box contained in
  `B_{s_j}(s_j u)` is contained in `B_{R s_{j-1}}(z)`, and `𝒞(s_j u, z)` holds.
Level `0` is not used (`True`). A box that is not nice is *bad*. -/
def NiceBox (p : NiceParams) (H : ℕ → Rd d → ℝ) : ℕ → Zd d → Prop
  | 0, _ => True
  | 1, u => NiceOscOne p H u ∧ NiceAcrossOne p H u
  | j + 2, u => NiceOscCond p H (j + 2) u ∧
      ((∀ v : Zd d, obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
            obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) → NiceBox p H (j + 1) v) ∨
        ∃ w : Zd d, latPt (p.s (j + 1)) w ∈ obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) ∧
          (∀ v : Zd d, obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
              obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) → ¬ NiceBox p H (j + 1) v →
            obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
              obox (latPt (p.s (j + 1)) w) (p.R * p.s (j + 1))) ∧
          NiceCEvent p H (j + 2) u w)

/-! ## The events `𝒥₁` and `𝒥₂′` -/

/-- **`𝒥₁`** (DGZ (5.21)): every `a_m`-box contained in `B₂(0)` is nice. -/
def EventJ1 (p : NiceParams) (H : ℕ → Rd d → ℝ) (m : ℕ) : Prop :=
  ∀ u : Zd d, obox (latPt (p.s m) u) (p.s m) ⊆ obox (0 : Rd d) 2 → NiceBox p H m u

/-- **`𝒥₂′`** (MA7 D-OSC; replaces DGZ's gradient event `𝒥₂` of (5.21)): for every `0 ≤ i ≤ m` and
`y ∈ 𝒴_i ∩ B₃(0)`, `osc_{B̄_{8s_i}(y)} h_{0,n-a_m} ≤ K √a_m 2^{-(a_m - a_i)}` (`h_{0,n-a_m} =
h_{n-a_m}`). -/
def EventJ2' (p : NiceParams) (H : ℕ → Rd d → ℝ) (m : ℕ) : Prop :=
  ∀ i ≤ m, ∀ v : Zd d, latPt (p.s i) v ∈ obox (0 : Rd d) 3 →
    ∀ z ∈ cbox (latPt (p.s i) v) (8 * p.s i), ∀ w ∈ cbox (latPt (p.s i) v) (8 * p.s i),
      |H (p.n - p.a m) z - H (p.n - p.a m) w| ≤
        p.K * √(p.a m : ℝ) * (2 : ℝ)⁻¹ ^ (p.a m - p.a i)

/-! ## Unfolding lemmas -/

section Unfold

variable (p : NiceParams) (H : ℕ → Rd d → ℝ)

@[simp] theorem niceBox_zero (u : Zd d) : NiceBox p H 0 u := trivial

theorem niceBox_one_iff (u : Zd d) :
    NiceBox p H 1 u ↔ NiceOscOne p H u ∧ NiceAcrossOne p H u := Iff.rfl

theorem niceBox_add_two_iff (j : ℕ) (u : Zd d) :
    NiceBox p H (j + 2) u ↔ NiceOscCond p H (j + 2) u ∧
      ((∀ v : Zd d, obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
            obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) → NiceBox p H (j + 1) v) ∨
        ∃ w : Zd d, latPt (p.s (j + 1)) w ∈ obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) ∧
          (∀ v : Zd d, obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
              obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) → ¬ NiceBox p H (j + 1) v →
            obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
              obox (latPt (p.s (j + 1)) w) (p.R * p.s (j + 1))) ∧
          NiceCEvent p H (j + 2) u w) := Iff.rfl

end Unfold

end DGZ

end HigherDimLQGMetric
