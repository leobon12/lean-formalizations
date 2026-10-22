import HigherDimLQGMetric.DGZ.FreeSitesDefs
import HigherDimLFPP.Exist.Sites

/-!
# DGZ §4.1: the dyadic setting, the site configurations and the events `𝒢_n`, `ℰ_{m,n}`, `ℱ_{m,n}`
(packet L3c1)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), §4.1: (4.4) (`m`-open sites), (4.5)
(`ℰ_{m,n}`), (4.6) (`𝒢_n`), (4.7) (`ℱ_{m,n}`), and the proof of Lemma 4.2 ((4.10): `m`-good sites;
TeX l. 1438: `m`-nice sites); planning audit `planning/audits/MA7-ref2-sections-4-6.md`, §5 row
L3c1, Details (a) D-4.1, D-4.2 and Details (c) §D.

* §D of MA7 Details (c), **verbatim** (names, binders, bodies, docstrings; namespace `MA7Scratch`
  replaced by `HigherDimLQGMetric.DGZ`): `IsDyadicRealization` (white noise with continuous
  versions `H n` of `h_n = H_{2^{-n},1}`), `aQ` (the lower quantile `a_n^{(p)}` of
  `D_n(0, e₁; B₂(0))`), `IsDGZExponent`, `DGZHyp`.
* `latRegion m`: the region `𝓛_m = 2^{-m} ℤ^d ∩ B₂(0)` in lattice coordinates.
* The configurations (sets of *open* sites of `ℤ^d`, `x ↦ 2^{-m} x`), all built on HigherDimLFPP's
  `DGZ.SiteClosed` with region radius `2 - 2^{-m}` (the lattice points of `B₂(0)`):
  - `mGood ξ φ m a` (DGZ (4.10), MA7 D-4.2): `x ∈ 𝓛_m` is good if
    `D(x, x ± 2^{-m} e_i; B_{2^{1-m}}(x)) ≤ 2^{-m} a` for every `i, ±` (`φ = h_{m,n}`,
    `a = a^{(q)}_{n-m}`); sites outside `𝓛_m` are good;
  - `mOpen ξ Q η φ m a` (DGZ (4.4)): the same with threshold `2^{-(1-ξQ+η)m} a` (`φ = h_n`);
  - `mNice ξ φ₁ φ₂ m a₁ a₂` (DGZ l. 1438): a site `y` of the coarse lattice `2^{1-m} ℤ^d` in
    `𝓛_{m-1}` is nice if it is `(m-1)`-good for `φ₁ = h_{m-1,n}` and every site of `2^{-m} ℤ^d` in
    `B_{2^{1-m}}(2^{1-m} y)` (the fine sites `z` with `|z - 2y|_∞ ≤ 1`) is `m`-good for
    `φ₂ = h_{m,n}`; sites outside `𝓛_{m-1}` are nice.
* The events: `eventG` (`𝒢_n`, on the closed box `B̄₃(0)` as in MA7 D-4.2 and L3b2), `eventE`
  (`ℰ_{m,n}`: `SmallClusters` of the `m`-open configuration with `D_m = m² - 101²`), `eventF`
  (`ℱ_{m,n}`, the free-site form of MA7 D-4.2: `ℰ_{m,n} ∩ ℰ_{m-1,n}` and every `x ∈ 𝓛_m` is
  within `m² 2^{-m}` of a coarse site `y ∈ 2^{1-m} ℤ^d` that is free for `O_m` and for `O_{m-1}`).
* Open clusters (DGZ Lemma 4.1): `IsOpenCluster O K` (a maximal L-connected set of open sites)
  and `infCluster O` (the open sites joined by open L-paths to sites outside every box: the
  unbounded open cluster `𝒪`).

Conventions. A coarse site `y` (mesh `2^{1-m}`) is the fine site `2 • y` (mesh `2^{-m}`); real
points are `latPt s x = s x`. `ℓ^∞` balls of real points become `WithinInf` on sites:
`|2^{-m} x - 2^{1-m} y|_∞ ≤ m² 2^{-m}` iff `WithinInf (m²) x (2 • y)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox SiteClosed)

variable {d : ℕ}

/-! ## §D. The dyadic setting (verbatim from MA7 Details (c) §D) -/

/-- `(P, W, H)`: white noise with continuous versions `H n` of `h_n = H_{2^{-n}, 1}` -/
structure IsDyadicRealization (κ : Rd d → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ) : Prop where
  whiteNoise : IsWhiteNoise P W
  band : ∀ n, IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) 1 (H n)

/-- `a_n^{(p)}`: the lower `p`-quantile of `D_n(0, e₁; B₂(0))` (DGZ (3.2); `λ_n = a_n^{(1/2)}`) -/
def aQ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ) (ξ : ℝ) (n : ℕ)
    (p : ℝ≥0∞) : ℝ :=
  LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H n z ω)) p

/-- `Q` is the DGZ exponent of the kernel `κ` at `ξ`: `λ_n = 2^{-(1-ξQ)n + o(n)}` for every
realization (HigherDimLFPP `prop31`/`dgzProp11` give existence) -/
def IsDGZExponent (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
    IsDyadicRealization κ P W H →
      Tendsto (fun n : ℕ => Real.log (aQ P H ξ n 2⁻¹) / n) atTop
        (𝓝 (-(1 - ξ * Q) * Real.log 2))

/-- the standing hypotheses of DGZ §§4–6 -/
structure DGZHyp (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop where
  dim : 2 ≤ d
  kernel : IsLFPPKernel κ
  xi_pos : 0 < ξ
  exponent : IsDGZExponent d κ ξ Q
  subcritical : Real.sqrt (2 * d) < Q

/-! ## The region `𝓛_m` and the site configurations -/

/-- `𝓛_m = 2^{-m} ℤ^d ∩ B₂(0)` in lattice coordinates: the sites `x` with `|x_i| < 2^{m+1}` for
all `i` (i.e. `|2^{-m} x|_∞ < 2`) -/
def latRegion (m : ℕ) : Set (Zd d) := {x | ∀ i, |x i| < 2 ^ (m + 1)}

/-- the `m`-good sites (DGZ (4.10); MA7 D-4.2) for the field `φ` (`= h_{m,n}`) and the level `a`
(`= a^{(q)}_{n-m}`): a site `x ∈ 𝓛_m` is good iff
`D(x, x ± 2^{-m} e_i; B_{2^{1-m}}(x)) ≤ 2^{-m} a` for all `i, ±` (HigherDimLFPP's
`DGZ.SiteClosed` with mesh `2^{-m}` and region radius `2 - 2^{-m}`); sites outside `𝓛_m` are
good -/
def mGood (ξ : ℝ) (φ : Rd d → ℝ) (m : ℕ) (a : ℝ) : Set (Zd d) :=
  {x | ¬ SiteClosed ξ φ ((2 : ℝ)⁻¹ ^ m) a (2 - (2 : ℝ)⁻¹ ^ m) x}

/-- the `m`-open sites (DGZ (4.4)) for the field `φ` (`= h_n`) and the level `a`
(`= a^{(q)}_{n-m}`): a site `x ∈ 𝓛_m` is open iff
`D(x, x ± 2^{-m} e_i; B_{2^{1-m}}(x)) ≤ 2^{-(1-ξQ+η)m} a` for all `i, ±`
(`= 2^{-m} · 2^{(ξQ-η)m} a`, see `mem_mOpen_iff`); sites outside `𝓛_m` are open -/
def mOpen (ξ Q η : ℝ) (φ : Rd d → ℝ) (m : ℕ) (a : ℝ) : Set (Zd d) :=
  {x | ¬ SiteClosed ξ φ ((2 : ℝ)⁻¹ ^ m) ((2 : ℝ) ^ ((ξ * Q - η) * m) * a) (2 - (2 : ℝ)⁻¹ ^ m) x}

/-- the `m`-nice sites (DGZ proof of Lemma 4.2, TeX l. 1438; MA7 D-4.2), a configuration on the
coarse lattice `2^{1-m} ℤ^d` (`m ≥ 1`): a site `y ∈ 𝓛_{m-1}` is nice iff it is `(m-1)`-good for
`φ₁` (`= h_{m-1,n}`, level `a₁ = a^{(q)}_{n-m+1}`) and every site of `2^{-m} ℤ^d` in
`B_{2^{1-m}}(2^{1-m} y)`, i.e. every fine site `z` with `|z - 2y|_∞ ≤ 1`, is `m`-good for `φ₂`
(`= h_{m,n}`, level `a₂ = a^{(q)}_{n-m}`; fine sites outside `𝓛_m` are good); sites outside
`𝓛_{m-1}` are nice -/
def mNice (ξ : ℝ) (φ₁ φ₂ : Rd d → ℝ) (m : ℕ) (a₁ a₂ : ℝ) : Set (Zd d) :=
  {y | y ∈ latRegion (m - 1) → y ∈ mGood ξ φ₁ (m - 1) a₁ ∧
    ∀ z : Zd d, WithinInf 1 z (2 • y) → z ∈ mGood ξ φ₂ m a₂}

/-! ## The events -/

/-- `𝒢_n` (DGZ (4.6), on the closed box `B̄₃(0)` as in MA7 D-4.2):
`sup_{B̄₃(0)} h_n ≤ n (Q - η/ξ) log 2`, i.e. `sup e^{ξ h_n} ≤ 2^{(ξQ - η) n}` for `ξ > 0` -/
def eventG {Ω : Type*} (ξ Q η : ℝ) (H : ℕ → Rd d → Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ z ∈ cbox (0 : Rd d) 3, H n z ω ≤ n * (Q - η / ξ) * Real.log 2}

/-- `ℰ_{m,n}` (DGZ (4.5); MA7 D-4.1): every `m`-closed `*`-cluster of `h_n` (level
`a^{(q)}_{n-m}`) is bounded with `ℓ^∞`-diameter at most `m² - 101²` (in `ℕ`) -/
def eventE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ Q η : ℝ) (q : ℝ≥0∞) (m n : ℕ) : Set Ω :=
  {ω | SmallClusters (mOpen ξ Q η (fun z => H n z ω) m (aQ P H ξ (n - m) q)) (m ^ 2 - 101 ^ 2)}

/-- `ℱ_{m,n}` (DGZ (4.7), free-site form of MA7 D-4.2): `ℰ_{m,n} ∩ ℰ_{m-1,n}`, and every site
`x ∈ 𝓛_m` is within `ℓ^∞`-distance `m² 2^{-m}` of a coarse site `y ∈ 2^{1-m} ℤ^d` (the fine site
`2 • y`) that is free for the `m`-open and for the `(m-1)`-open configuration -/
def eventF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ Q η : ℝ) (q : ℝ≥0∞) (m n : ℕ) : Set Ω :=
  eventE P H ξ Q η q m n ∩ eventE P H ξ Q η q (m - 1) n ∩
    {ω | ∀ x ∈ latRegion m, ∃ y : Zd d, WithinInf ((m : ℤ) ^ 2) x (2 • y) ∧
      FreeSite (mOpen ξ Q η (fun z => H n z ω) m (aQ P H ξ (n - m) q)) (2 • y) ∧
      FreeSite (mOpen ξ Q η (fun z => H n z ω) (m - 1) (aQ P H ξ (n - (m - 1)) q)) y}

/-! ## Open clusters (DGZ Lemma 4.1) -/

/-- an open cluster of the configuration `O`: a nonempty, L-connected set of open sites that is
maximal (closed under open L-steps) -/
def IsOpenCluster (O K : Set (Zd d)) : Prop :=
  K.Nonempty ∧ K ⊆ O ∧ ConnIn K LAdj ∧ ∀ x ∈ K, ∀ y, y ∈ O → LAdj x y → y ∈ K

/-- the unbounded open cluster `𝒪` (DGZ Lemma 4.1): the open sites joined by open L-paths to
sites outside every box -/
def infCluster (O : Set (Zd d)) : Set (Zd d) :=
  {x | x ∈ O ∧ ∀ R : ℤ, ∃ v, ¬ WithinInf R v 0 ∧ Relation.ReflTransGen (StepIn O LAdj) x v}

/-! ## Basic API -/

theorem two_smul_apply (y : Zd d) (i : Fin d) : (2 • y) i = 2 * y i := by
  rw [Pi.smul_apply, nsmul_eq_mul]
  push_cast
  ring

/-- The region condition of `SiteClosed` with mesh `2^{-m}` and radius `2 - 2^{-m}` is
`|x_i| < 2^{m+1}`. -/
theorem abs_latPt_le_iff (m : ℕ) (x : Zd d) (i : Fin d) :
    |latPt ((2 : ℝ)⁻¹ ^ m) x i| ≤ 2 - (2 : ℝ)⁻¹ ^ m ↔ |x i| < 2 ^ (m + 1) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rw [HigherDimLFPP.DGZ.latPt_apply, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m),
    inv_pow, ← Int.cast_abs]
  have key : (2 ^ m : ℝ)⁻¹ * (((|x i| : ℤ)) : ℝ) ≤ 2 - (2 ^ m : ℝ)⁻¹ ↔
      ((|x i| + 1 : ℤ) : ℝ) ≤ ((2 ^ (m + 1) : ℤ) : ℝ) := by
    rw [le_sub_iff_add_le, ← mul_add_one, inv_mul_le_iff₀ hpos]
    push_cast
    rw [pow_succ]
  rw [key, Int.cast_le]
  omega

/-- The region of `SiteClosed` with mesh `2^{-m}` and radius `2 - 2^{-m}` is `𝓛_m`. -/
theorem region_iff_mem_latRegion (m : ℕ) (x : Zd d) :
    (∀ i, |latPt ((2 : ℝ)⁻¹ ^ m) x i| ≤ 2 - (2 : ℝ)⁻¹ ^ m) ↔ x ∈ latRegion m :=
  forall_congr' fun i => abs_latPt_le_iff m x i

theorem withinInf_of_mem_latRegion {m : ℕ} {x : Zd d} (hx : x ∈ latRegion m) :
    WithinInf (2 ^ (m + 1)) x 0 := fun i => by
  rw [Pi.zero_apply, sub_zero]
  exact (hx i).le

/-- `𝓛_m` is the lattice box `[-(2^{m+1} - 1), 2^{m+1} - 1]^d`. -/
theorem withinInf_sub_one_of_mem_latRegion {m : ℕ} {x : Zd d} (hx : x ∈ latRegion m) :
    WithinInf (2 ^ (m + 1) - 1) x 0 := fun i => by
  rw [Pi.zero_apply, sub_zero]
  have := hx i
  omega

theorem mem_latRegion_iff_withinInf {m : ℕ} {x : Zd d} :
    x ∈ latRegion m ↔ WithinInf (2 ^ (m + 1) - 1) x 0 := by
  refine ⟨withinInf_sub_one_of_mem_latRegion, fun h i => ?_⟩
  have := h i
  rw [Pi.zero_apply, sub_zero] at this
  omega

/-- `x ∈ 𝓛_m` iff the real point `2^{-m} x` lies in the open box `B₂(0)`. -/
theorem mem_latRegion_iff_mem_obox (m : ℕ) (x : Zd d) :
    x ∈ latRegion m ↔ latPt ((2 : ℝ)⁻¹ ^ m) x ∈ obox (0 : Rd d) 2 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  refine forall_congr' fun i => ?_
  rw [PiLp.zero_apply, sub_zero, HigherDimLFPP.DGZ.latPt_apply, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m), inv_pow, ← Int.cast_abs,
    inv_mul_lt_iff₀ hpos]
  have e : (2 : ℝ) ^ m * 2 = ((2 ^ (m + 1) : ℤ) : ℝ) := by push_cast; ring
  rw [e, Int.cast_lt]

section Sites

variable {ξ Q η a : ℝ} {φ : Rd d → ℝ} {m : ℕ} {x : Zd d}

theorem mem_latRegion_of_not_mem_mGood (hx : x ∉ mGood ξ φ m a) : x ∈ latRegion m := by
  simp only [mGood, mem_ofPred_eq, not_not] at hx
  exact (region_iff_mem_latRegion m x).1 hx.1

theorem mem_mGood_of_not_mem_latRegion (hx : x ∉ latRegion m) : x ∈ mGood ξ φ m a :=
  fun h => hx ((region_iff_mem_latRegion m x).1 h.1)

theorem mem_latRegion_of_not_mem_mOpen (hx : x ∉ mOpen ξ Q η φ m a) : x ∈ latRegion m := by
  simp only [mOpen, mem_ofPred_eq, not_not] at hx
  exact (region_iff_mem_latRegion m x).1 hx.1

theorem mem_mOpen_of_not_mem_latRegion (hx : x ∉ latRegion m) : x ∈ mOpen ξ Q η φ m a :=
  fun h => hx ((region_iff_mem_latRegion m x).1 h.1)

/-- `m`-open is `m`-good with the threshold `2^{(ξQ-η)m} a`. -/
theorem mOpen_eq_mGood : mOpen ξ Q η φ m a = mGood ξ φ m ((2 : ℝ) ^ ((ξ * Q - η) * m) * a) :=
  rfl

/-- DGZ (4.10), literally: `x` is `m`-good iff, when `x ∈ 𝓛_m`,
`D(x, x'; B_{2^{1-m}}(x)) ≤ 2^{-m} a` for every L-neighbour `x'`. -/
theorem mem_mGood_iff : x ∈ mGood ξ φ m a ↔ (x ∈ latRegion m → ∀ x', LAdj x x' →
    lfppDistOn ξ φ (obox (latPt ((2 : ℝ)⁻¹ ^ m) x) (2 * (2 : ℝ)⁻¹ ^ m)) (latPt ((2 : ℝ)⁻¹ ^ m) x)
      (latPt ((2 : ℝ)⁻¹ ^ m) x') ≤ (2 : ℝ)⁻¹ ^ m * a) := by
  simp only [mGood, mem_ofPred_eq, SiteClosed, not_and, not_exists, not_lt,
    region_iff_mem_latRegion]

/-- `2^{-m} · 2^{(ξQ-η)m} = 2^{-(1-ξQ+η)m}`. -/
theorem inv_two_pow_mul_rpow (m : ℕ) (ξ Q η : ℝ) :
    (2 : ℝ)⁻¹ ^ m * (2 : ℝ) ^ ((ξ * Q - η) * m) = (2 : ℝ) ^ (-(1 - ξ * Q + η) * m) := by
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- DGZ (4.4), literally: `x` is `m`-open iff, when `x ∈ 𝓛_m`,
`D(x, x'; B_{2^{1-m}}(x)) ≤ 2^{-(1-ξQ+η)m} a` for every L-neighbour `x'`. -/
theorem mem_mOpen_iff : x ∈ mOpen ξ Q η φ m a ↔ (x ∈ latRegion m → ∀ x', LAdj x x' →
    lfppDistOn ξ φ (obox (latPt ((2 : ℝ)⁻¹ ^ m) x) (2 * (2 : ℝ)⁻¹ ^ m)) (latPt ((2 : ℝ)⁻¹ ^ m) x)
      (latPt ((2 : ℝ)⁻¹ ^ m) x') ≤ (2 : ℝ) ^ (-(1 - ξ * Q + η) * m) * a) := by
  rw [mOpen_eq_mGood, mem_mGood_iff, ← mul_assoc, inv_two_pow_mul_rpow]

/-- The DGZ (4.4) bound at an `m`-open site of `𝓛_m`. -/
theorem lfppDistOn_le_of_mem_mOpen (hx : x ∈ mOpen ξ Q η φ m a) (hreg : x ∈ latRegion m)
    {x' : Zd d} (hxx' : LAdj x x') :
    lfppDistOn ξ φ (obox (latPt ((2 : ℝ)⁻¹ ^ m) x) (2 * (2 : ℝ)⁻¹ ^ m)) (latPt ((2 : ℝ)⁻¹ ^ m) x)
      (latPt ((2 : ℝ)⁻¹ ^ m) x') ≤ (2 : ℝ) ^ (-(1 - ξ * Q + η) * m) * a :=
  mem_mOpen_iff.1 hx hreg x' hxx'

/-- The closed sites of the `m`-open configuration lie in the box `[-2^{m+1}, 2^{m+1}]^d`. -/
theorem withinInf_of_not_mem_mOpen (hx : x ∉ mOpen ξ Q η φ m a) :
    WithinInf (2 ^ (m + 1)) x 0 :=
  withinInf_of_mem_latRegion (mem_latRegion_of_not_mem_mOpen hx)

/-- The closed sites of the `m`-good configuration lie in the box `[-2^{m+1}, 2^{m+1}]^d`. -/
theorem withinInf_of_not_mem_mGood (hx : x ∉ mGood ξ φ m a) :
    WithinInf (2 ^ (m + 1)) x 0 :=
  withinInf_of_mem_latRegion (mem_latRegion_of_not_mem_mGood hx)

end Sites

end DGZ

end HigherDimLQGMetric
