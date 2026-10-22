import HigherDimLQGContinuity.LabelEvents.Source
import HigherDimLQGContinuity.Witness.Subdiv

/-!
# The arc of a favorable seed (packet Q5; Part B `b:lem-label-exists`, arc part)

Source: blueprint Part B `b:lem-label-exists` (proof, paragraph *Arc*), `b:def-seedfav`, `b:lem-arcmod`(a); [C]
l. 1066–1079; planning audit NA2, items 13, 25–27, R14 (conversion from own seed units to primary site units).
Inputs: Part A's subdivision of witnesses `hdown_subdivision` (packet P5a, `Witness/Subdiv.lean`) and the reference
facts `LocalRefs.exit_barrier`, `LocalRefs.local_competitor` (`Witness/Refs.lean`).

Certificates of the (F6) constants (for the site data's seed structure): `one_le_seedConstA`, `one_le_seedConstHE`,
`seedConstEll0_pos`, `seedConstEll0_le_seedConstEll1`, `seedConstD0_pos`.

**Statement** (`exists_seedArc_of_seedFav`). Let `D, E` be continuous length metrics (site coordinates, primary site
units) with a favorable seed `SeedFav(D, E; c, r)` (seed references `(H₀, σ₀, β₀, m, M)`, seed doubled-ball constants
`(Hsd, σsd)`, unit bound `Λ`, tolerance `v ∈ [0, 1/2]`), at a seed radius `r ∈ [s_min, 1]`. Then, with the derived
constants (F6) of Part B (`seedConstHE`, `seedConstA`, `seedConstEll0`, `seedConstEll1`, `seedConstD0`;
`s_E = σsd`, `α = 1/β₀`, `β = σ₀`):
`DUp(E, A_seed, H_E, s_E)`, and there are an arc `γ` of the arc space of the seed shell with constants `(A, α, β)` and
an own length `λ ∈ [ℓ₀, ℓ₁]` with (V2)(a)–(d) of `b:def-source`. Together with a label whose geometric predicate the
arc satisfies (packets Q2/Q3: cells met by the arc and the two leads of `b:lem-leads`), this is `EdgeSource`.

**Proof** (Part B, with explicit constants). Let `D'' = S_D⁻¹ D(c + r·)`, `E'' = S_E⁻¹ E(c + r·)` (length metrics),
`N = N∗`. `hdown_subdivision` (with `b = 1 + 2v`) gives a piece `η` of the `E''`-witness with slope
`λ'' ∈ [m/N, M/N]`, `E''(η s, η t; A) = E''(η s, η t) = λ''|s - t|`, `η([0, 1]) ⊆ K`, Euclidean diameter `< δ₀/2`,
two-sided moduli `H₀⁻¹|η s - η t|^{β₀} ≤ λ''|s - t| ≤ H₀|η s - η t|^{σ₀}`, `d∗ ≤ E''(η 0, η 1) ≤ (1 + 2v) D''(η 0, η 1)`
and `D''(η 0, η 1; A) = D''(η 0, η 1)`. Put `γ = c + r η`, `λ = S_E λ''`; internal metrics transform by
`G(c + r x, c + r y; c + r U) = S_G G''(x, y; U)` (`q5_internal_seedPull`). (a) by scaling. (b)
`D(γ 0, γ 1; A_seed) = S_D D''(η 0, η 1) ≥ Λ⁻¹ d∗/(1 + 2v) ≥ d∗/(2Λ)`. (c) `λ = S_E E''(η 0, η 1) ≤ (S_E/S_D)(1 + 2v)
D(γ 0, γ 1; A_seed)` and `S_E/S_D ≤ e^{v/10} ≤ 1 + v/5`, `(1 + v/5)(1 + 2v) ≤ 1 + 4v`. (d) first exit: the exit
barrier `H₀⁻¹ 8^{-β₀}` of the lower reference against the local competitor `< H₀⁻¹ 8^{-β₀}` (`|η 0 - η 1| ≤ δ₀`).
Moduli: `r|η s - η t| ≤ (H₀ M/N)^{1/β₀}|s - t|^{1/β₀}` (`r ≤ 1`) and
`|s - t| ≤ (H₀/λ'') r^{-σ₀}|γ s - γ t|^{σ₀} ≤ H₀ N/(m s_min^{σ₀}) |γ s - γ t|^{σ₀}` (`r ≥ s_min`). `DUp`: a ball
`B_{2ρ}(z) ⊆ A_seed` pulls back to `B_{2ρ/r}(z'') ⊆ A`, so
`diamIn ≤ S_E H_sd (ρ/r)^{σsd} ≤ Λ H_sd s_min^{-σsd} ρ^{σsd}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-! ## The derived constants (F6) of `b:lem-label-exists` -/

/-- `H_E = Λ H_sd s_min^{-σ_sd}` (secondary doubled-ball constant in primary site units). -/
def seedConstHE (Hsd σsd Λ smin : ℝ) : ℝ := Λ * Hsd * smin ^ (-σsd)

/-- `A = max{(H₀ M/N∗)^{1/β₀}, H₀ N∗/(m s_min^{σ₀}), 1}` (arc constant). -/
def seedConstA (H₀ σ₀ β₀ m M smin : ℝ) : ℝ :=
  max (max ((H₀ * M / subdivN H₀ σ₀ β₀ M) ^ (1 / β₀)) (H₀ * subdivN H₀ σ₀ β₀ M / (m * smin ^ σ₀))) 1

/-- `ℓ₀ = m/(Λ N∗)` (lower end of the own-length interval). -/
def seedConstEll0 (H₀ σ₀ β₀ m M Λ : ℝ) : ℝ := m / (Λ * subdivN H₀ σ₀ β₀ M)

/-- `ℓ₁ = Λ M/N∗` (upper end of the own-length interval). -/
def seedConstEll1 (H₀ σ₀ β₀ M Λ : ℝ) : ℝ := Λ * M / subdivN H₀ σ₀ β₀ M

/-- `d₀ = d∗/(2Λ)` (unit-pair lower bound). -/
def seedConstD0 (H₀ σ₀ β₀ m M Λ : ℝ) : ℝ := subdivD H₀ σ₀ β₀ m M / (2 * Λ)

theorem one_le_seedConstA (H₀ σ₀ β₀ m M smin : ℝ) : 1 ≤ seedConstA H₀ σ₀ β₀ m M smin :=
  le_max_right _ _

theorem seedConstEll0_pos {H₀ σ₀ β₀ m M Λ : ℝ} (hm : 0 < m) (hΛ : 0 < Λ) : 0 < seedConstEll0 H₀ σ₀ β₀ m M Λ :=
  div_pos hm (mul_pos hΛ (subdivN_pos H₀ σ₀ β₀ M))

theorem seedConstD0_pos {H₀ σ₀ β₀ m M Λ : ℝ} (hm : 0 < m) (hΛ : 0 < Λ) : 0 < seedConstD0 H₀ σ₀ β₀ m M Λ :=
  div_pos (subdivD_pos hm) (mul_pos two_pos hΛ)

theorem one_le_seedConstHE {Hsd σsd Λ smin : ℝ} (hHsd : 1 ≤ Hsd) (hσsd : 0 ≤ σsd) (hΛ : 1 ≤ Λ)
    (hsmin : 0 < smin) (hsmin1 : smin ≤ 1) : 1 ≤ seedConstHE Hsd σsd Λ smin := by
  have h1 : 1 ≤ smin ^ (-σsd) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hsmin hsmin1 (neg_nonpos.2 hσsd)
  unfold seedConstHE
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ Λ * Hsd * smin ^ (-σsd) := by gcongr

theorem seedConstEll0_le_seedConstEll1 {H₀ σ₀ β₀ m M Λ : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M) (hΛ : 1 ≤ Λ) :
    seedConstEll0 H₀ σ₀ β₀ m M Λ ≤ seedConstEll1 H₀ σ₀ β₀ M Λ := by
  have hN : 0 < (subdivN H₀ σ₀ β₀ M : ℝ) := subdivN_pos H₀ σ₀ β₀ M
  have hΛ0 : 0 < Λ := by linarith
  unfold seedConstEll0 seedConstEll1
  rw [div_le_div_iff₀ (mul_pos hΛ0 hN) hN]
  have hM : 0 ≤ M := hm.trans hmM
  have hΛΛ : 1 ≤ Λ * Λ := by nlinarith
  have h1 : m ≤ Λ * Λ * M := by
    calc m ≤ M := hmM
      _ = 1 * M := (one_mul M).symm
      _ ≤ Λ * Λ * M := mul_le_mul_of_nonneg_right hΛΛ hM
  calc m * ↑(subdivN H₀ σ₀ β₀ M) ≤ Λ * Λ * M * ↑(subdivN H₀ σ₀ β₀ M) :=
        mul_le_mul_of_nonneg_right h1 hN.le
    _ = Λ * M * (Λ * ↑(subdivN H₀ σ₀ β₀ M)) := by ring

/-! ## Seed pull-backs -/

/-- Internal metrics of the seed pull-back `S⁻¹ G(r · + c)`: `G(c + r x, c + r y; c + r U) = S G''(x, y; U)`. -/
theorem q5_internal_seedPull (G : ContMetric d) {r : ℝ} (hr : r ≠ 0) (c : Rd d) {S : ℝ} (hS : 0 < S)
    (U : Set (Rd d)) (x y : Rd d) :
    G.internal ((fun u => c + r • u) '' U) (c + r • x) (c + r • y) =
      ENNReal.ofReal S * ((G.affine r hr c).smul S⁻¹ (inv_pos.2 hS)).internal U x y := by
  rw [ContMetric.internal_smul, ContMetric.internal_affine, ← mul_assoc, ← ENNReal.ofReal_mul hS.le,
    mul_inv_cancel₀ hS.ne', ENNReal.ofReal_one, one_mul, q5_affine_comm, add_comm c (r • x),
    add_comm c (r • y)]

theorem q5_image_seed_ball {r : ℝ} (hr : 0 < r) (c z : Rd d) (a : ℝ) :
    (fun u : Rd d => c + r • u) '' ball (r⁻¹ • (z - c)) (a / r) = ball z a := by
  rw [q5_affine_comm, p2_image_affine_ball hr, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel,
    mul_div_cancel₀ _ hr.ne']

theorem q5_image_seed_closedBall {r : ℝ} (hr : 0 < r) (c z : Rd d) (a : ℝ) :
    (fun u : Rd d => c + r • u) '' closedBall (r⁻¹ • (z - c)) (a / r) = closedBall z a := by
  rw [q5_affine_comm, p2_image_affine_closedBall hr, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
    sub_add_cancel, mul_div_cancel₀ _ hr.ne']

/-- The secondary doubled-ball reference of the seed, scaled to primary site units (`DUp(E, A_seed, H_E, s_E)`). -/
theorem q5_dUpper_seed {E : ContMetric d} {r : ℝ} (hr : 0 < r) (c : Rd d) {SE Λ Hsd σsd smin : ℝ}
    (hSE : 0 < SE) (hSEΛ : SE ≤ Λ) (hHsd : 0 ≤ Hsd) (hσsd : 0 ≤ σsd) (hsmin : 0 < smin) (hsr : smin ≤ r)
    (h : DUpper ((E.affine r hr.ne' c).smul SE⁻¹ (inv_pos.2 hSE)) (annA d) Hsd σsd) :
    DUpper E (srcSeedA c r) (seedConstHE Hsd σsd Λ smin) σsd := by
  intro z ρ hρ hball
  set z'' : Rd d := r⁻¹ • (z - c) with hz''
  have hρr : 0 < ρ / r := div_pos hρ hr
  have hinj : Function.Injective fun u : Rd d => c + r • u := by
    rw [q5_affine_comm]
    exact q5_affine_injective hr.ne' c
  have hball'' : closedBall z'' (2 * (ρ / r)) ⊆ annA d := by
    intro u hu
    have hu' : c + r • u ∈ closedBall z (2 * ρ) := by
      rw [← q5_image_seed_closedBall hr c z (2 * ρ)]
      refine ⟨u, ?_, rfl⟩
      rwa [mul_div_assoc]
    obtain ⟨u', hu'A, he⟩ := hball hu'
    rw [← hinj he]
    exact hu'A
  have hdiam := h z'' (ρ / r) hρr hball''
  have hb2 : (fun u : Rd d => c + r • u) '' ball z'' (2 * (ρ / r)) = ball z (2 * ρ) := by
    rw [← mul_div_assoc]
    exact q5_image_seed_ball hr c z (2 * ρ)
  have hb1 : (fun u : Rd d => c + r • u) '' ball z'' (ρ / r) = ball z ρ := q5_image_seed_ball hr c z ρ
  have htr := p2_diamIn_image_of_internal (G := E)
    (G' := (E.affine r hr.ne' c).smul SE⁻¹ (inv_pos.2 hSE)) (Φ := fun u : Rd d => c + r • u)
    (c := ENNReal.ofReal SE) (fun U x y => q5_internal_seedPull E hr.ne' c hSE U x y)
    (ball z'' (2 * (ρ / r))) (ball z'' (ρ / r))
  rw [hb2, hb1] at htr
  rw [htr]
  have hkey : SE * (Hsd * (ρ / r) ^ σsd) ≤ seedConstHE Hsd σsd Λ smin * ρ ^ σsd := by
    have hpow : (ρ / r) ^ σsd = ρ ^ σsd * r ^ (-σsd) := by
      rw [Real.div_rpow hρ.le hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
    have hrs : r ^ (-σsd) ≤ smin ^ (-σsd) :=
      Real.rpow_le_rpow_of_nonpos hsmin hsr (neg_nonpos.2 hσsd)
    have h1 : 0 ≤ ρ ^ σsd := Real.rpow_nonneg hρ.le _
    have h2 : 0 ≤ r ^ (-σsd) := Real.rpow_nonneg hr.le _
    rw [hpow, seedConstHE]
    have hΛ0 : 0 ≤ Λ := hSE.le.trans hSEΛ
    calc SE * (Hsd * (ρ ^ σsd * r ^ (-σsd))) ≤ Λ * (Hsd * (ρ ^ σsd * smin ^ (-σsd))) := by
          gcongr
      _ = Λ * Hsd * smin ^ (-σsd) * ρ ^ σsd := by ring
  calc ENNReal.ofReal SE * diamIn ((E.affine r hr.ne' c).smul SE⁻¹ (inv_pos.2 hSE))
        (ball z'' (2 * (ρ / r))) (ball z'' (ρ / r))
      ≤ ENNReal.ofReal SE * ENNReal.ofReal (Hsd * (ρ / r) ^ σsd) := by gcongr
    _ = ENNReal.ofReal (SE * (Hsd * (ρ / r) ^ σsd)) := (ENNReal.ofReal_mul hSE.le).symm
    _ ≤ ENNReal.ofReal (seedConstHE Hsd σsd Λ smin * ρ ^ σsd) := ENNReal.ofReal_le_ofReal hkey

/-! ## Elementary inequalities -/

/-- `e^{v/10}(1 + 2v) ≤ 1 + 4v` for `0 ≤ v ≤ 1`. -/
theorem q5_exp_mul_le {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    Real.exp (v / 10) * (1 + 2 * v) ≤ 1 + 4 * v := by
  have habs : |v / 10| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have h := Real.abs_exp_sub_one_le habs
  have hexp : Real.exp (v / 10) ≤ 1 + v / 5 := by
    have := (abs_le.1 h).2
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ v / 10)] at this
    linarith
  calc Real.exp (v / 10) * (1 + 2 * v) ≤ (1 + v / 5) * (1 + 2 * v) :=
        mul_le_mul_of_nonneg_right hexp (by linarith)
    _ ≤ 1 + 4 * v := by nlinarith

/-- From `x^β₀ ≤ y` (`x, y ≥ 0`, `β₀ > 0`): `x ≤ y^{1/β₀}`. -/
theorem q5_le_rpow_inv_of_rpow_le {x y β₀ : ℝ} (hx : 0 ≤ x) (hβ₀ : 0 < β₀) (h : x ^ β₀ ≤ y) :
    x ≤ y ^ (1 / β₀) := by
  have hy : 0 ≤ y := le_trans (Real.rpow_nonneg hx _) h
  calc x = (x ^ β₀) ^ (1 / β₀) := by rw [one_div, Real.rpow_rpow_inv hx hβ₀.ne']
    _ ≤ y ^ (1 / β₀) := Real.rpow_le_rpow (Real.rpow_nonneg hx _) h (by positivity)

/-! ## The arc of a favorable seed -/

/-- **The arc of a favorable seed** (`b:lem-label-exists`, arc part; Part B (F6) constants): a favorable seed at
radius `r ∈ [s_min, 1]` gives `DUp(E, A_seed, H_E, σsd)` and an arc of the arc space of the seed shell with
constants `(A, 1/β₀, σ₀)` and an own length `λ ∈ [ℓ₀, ℓ₁]` satisfying (V2)(a)–(d) with `d₀ = d∗/(2Λ)`. -/
theorem exists_seedArc_of_seedFav {D E : ContMetric d} (hD : D.IsLength) (hE : E.IsLength)
    {H₀ σ₀ β₀ m M Hsd σsd Λ v : ℝ} (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    (hHsd : 0 ≤ Hsd) (hσsd : 0 ≤ σsd) (hv : 0 ≤ v) (hv1 : v ≤ 1 / 2)
    {c : Rd d} {r smin : ℝ} (hsmin : 0 < smin) (hsr : smin ≤ r) (hr1 : r ≤ 1)
    (hfav : SeedFav H₀ σ₀ β₀ m M Hsd σsd Λ v D E c r) :
    DUpper E (srcSeedA c r) (seedConstHE Hsd σsd Λ smin) σsd ∧
      ∃ γ ∈ ArcSpace (srcSeedK c r) (seedConstA H₀ σ₀ β₀ m M smin) (1 / β₀) σ₀,
      ∃ lam ∈ Icc (seedConstEll0 H₀ σ₀ β₀ m M Λ) (seedConstEll1 H₀ σ₀ β₀ M Λ),
        (∀ s t : unitInterval,
          E.internal (srcSeedA c r) (γ s) (γ t) = ENNReal.ofReal (lam * |(s : ℝ) - t|)) ∧
        ENNReal.ofReal (seedConstD0 H₀ σ₀ β₀ m M Λ) ≤ D.internal (srcSeedA c r) (γ 0) (γ 1) ∧
        ENNReal.ofReal lam ≤ ENNReal.ofReal (1 + 4 * v) * D.internal (srcSeedA c r) (γ 0) (γ 1) ∧
        (∀ w : Rd d, ‖w - γ 0‖ = r / 8 →
          D.internal (srcSeedA c r) (γ 0) (γ 1) ≤ D.internal (srcSeedA c r) (γ 0) w) := by
  obtain ⟨hr0, SD, SE, hSD, hSE, hSDl, hSDu, hSEl, hSEu, hcap, ⟨hRD, hRE, -, hUE⟩, γ'', hwit, hgood⟩ := hfav
  have hr : 0 < r := hsmin.trans_le hsr
  have hΛ : 0 < Λ := lt_of_lt_of_le hSD hSDu
  have hD'' : ((D.affine r hr0 c).smul SD⁻¹ (inv_pos.2 hSD)).IsLength :=
    ContMetric.isLength_smul _ (ContMetric.isLength_affine _ _ hD)
  have hE'' : ((E.affine r hr0 c).smul SE⁻¹ (inv_pos.2 hSE)).IsLength :=
    ContMetric.isLength_smul _ (ContMetric.isLength_affine _ _ hE)
  obtain ⟨η, lam, -, hlam1, hlam2, -, hP, -, hdE, hEle, hDA⟩ :=
    hdown_subdivision hD'' hE'' hH₀ hσ₀ hβ₀ hm hRD hRE (b := 1 + 2 * v) (by linarith) hwit hgood
  set N : ℝ := (subdivN H₀ σ₀ β₀ M : ℝ) with hNdef
  have hN : 0 < N := subdivN_pos H₀ σ₀ β₀ M
  have hlam0 : 0 < lam := lt_of_lt_of_le (div_pos hm hN) hlam1
  set D'' := (D.affine r hr0 c).smul SD⁻¹ (inv_pos.2 hSD) with hD''def
  set E'' := (E.affine r hr0 c).smul SE⁻¹ (inv_pos.2 hSE) with hE''def
  have hmem : ∀ t : unitInterval, (t : ℝ) ∈ Icc (0 : ℝ) 1 := fun t => t.2
  -- the physical arc
  let γ : C(unitInterval, Rd d) :=
    ⟨fun t => c + r • η t, continuous_const.add ((hP.continuous.comp continuous_subtype_val).const_smul r)⟩
  have hγ : ∀ t : unitInterval, γ t = c + r • η t := fun t => rfl
  have hγ0 : γ 0 = c + r • η 0 := by rw [hγ]; rfl
  have hγ1 : γ 1 = c + r • η 1 := by rw [hγ]; rfl
  have hA : srcSeedA c r = (fun u => c + r • u) '' annA d := rfl
  have hDsc := q5_internal_seedPull D hr0 c hSD (annA d)
  have hEsc := q5_internal_seedPull E hr0 c hSE (annA d)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hη0K : η 0 ∈ annK d := hP.mem_annK 0 h0
  have hη1K : η 1 ∈ annK d := hP.mem_annK 1 h1
  have hElam : E''.1 (η 0, η 1) = lam := by
    rw [hP.apply_eq 0 h0 1 h1]
    norm_num
  have hDnn : 0 ≤ D''.1 (η 0, η 1) := D''.nonneg _ _
  -- the primary distance of the endpoints
  have hDend : D.internal (srcSeedA c r) (γ 0) (γ 1) = ENNReal.ofReal (SD * D''.1 (η 0, η 1)) := by
    rw [hγ0, hγ1, hA, hDsc, hDA, ← ENNReal.ofReal_mul hSD.le]
  refine ⟨q5_dUpper_seed hr c hSE hSEu hHsd hσsd hsmin hsr hUE, γ, ⟨fun t => ⟨η t, hP.mem_annK t (hmem t), rfl⟩,
    fun s t => ⟨?_, ?_⟩⟩, SE * lam, ⟨?_, ?_⟩, fun s t => ?_, ?_, ?_, fun w hw => ?_⟩
  · -- first modulus
    have hm' := (hP.moduli s (hmem s) t (hmem t)).1
    have hηst : ‖η s - η t‖ ^ β₀ ≤ H₀ * M / N * |(s : ℝ) - t| := by
      have h3 : lam * |(s : ℝ) - t| ≤ M / N * |(s : ℝ) - t| :=
        mul_le_mul_of_nonneg_right hlam2 (abs_nonneg _)
      have h4 : ‖η s - η t‖ ^ β₀ ≤ H₀ * (lam * |(s : ℝ) - t|) := by
        rw [← inv_mul_le_iff₀ hH₀]
        exact hm'
      calc ‖η s - η t‖ ^ β₀ ≤ H₀ * (lam * |(s : ℝ) - t|) := h4
        _ ≤ H₀ * (M / N * |(s : ℝ) - t|) := mul_le_mul_of_nonneg_left h3 hH₀.le
        _ = H₀ * M / N * |(s : ℝ) - t| := by ring
    have hle := q5_le_rpow_inv_of_rpow_le (norm_nonneg _) hβ₀ hηst
    have hMN : 0 ≤ H₀ * M / N := by
      have hM : 0 ≤ M := le_trans hm.le (by
        have := hlam1.trans hlam2
        rw [div_le_div_iff_of_pos_right hN] at this
        exact this)
      positivity
    rw [Real.mul_rpow hMN (abs_nonneg _)] at hle
    rw [hγ, hγ, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc r * ‖η s - η t‖ ≤ ‖η s - η t‖ := mul_le_of_le_one_left (norm_nonneg _) hr1
      _ ≤ (H₀ * M / N) ^ (1 / β₀) * |(s : ℝ) - t| ^ (1 / β₀) := hle
      _ ≤ seedConstA H₀ σ₀ β₀ m M smin * |(s : ℝ) - t| ^ (1 / β₀) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (abs_nonneg _) _)
          exact le_trans (le_max_left _ _) (le_max_left _ _)
  · -- inverse modulus
    have hm' := (hP.moduli s (hmem s) t (hmem t)).2
    have hnorm : ‖γ s - γ t‖ = r * ‖η s - η t‖ := by
      rw [hγ, hγ, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hst : |(s : ℝ) - t| ≤ H₀ / lam * ‖η s - η t‖ ^ σ₀ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam0, mul_comm]
      exact hm'
    have hH0lam : H₀ / lam ≤ H₀ * N / m := by
      rw [div_le_div_iff₀ hlam0 hm]
      have : m ≤ lam * N := by rwa [div_le_iff₀ hN] at hlam1
      nlinarith
    have hηpow : ‖η s - η t‖ ^ σ₀ ≤ smin ^ (-σ₀) * ‖γ s - γ t‖ ^ σ₀ := by
      have e : ‖η s - η t‖ = r⁻¹ * ‖γ s - γ t‖ := by
        rw [hnorm, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
      rw [e, Real.mul_rpow (inv_nonneg.2 hr.le) (norm_nonneg _), Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hsmin hsr (neg_nonpos.2 hσ₀.le))
        (Real.rpow_nonneg (norm_nonneg _) _)
    calc |(s : ℝ) - t| ≤ H₀ / lam * ‖η s - η t‖ ^ σ₀ := hst
      _ ≤ H₀ * N / m * (smin ^ (-σ₀) * ‖γ s - γ t‖ ^ σ₀) :=
          mul_le_mul hH0lam hηpow (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
      _ = H₀ * N / (m * smin ^ σ₀) * ‖γ s - γ t‖ ^ σ₀ := by
          rw [Real.rpow_neg hsmin.le]
          field_simp
      _ ≤ seedConstA H₀ σ₀ β₀ m M smin * ‖γ s - γ t‖ ^ σ₀ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
          exact le_trans (le_max_right _ _) (le_max_left _ _)
  · -- `ℓ₀ ≤ S_E λ''`
    rw [seedConstEll0]
    calc m / (Λ * N) = Λ⁻¹ * (m / N) := by field_simp
      _ ≤ SE * lam := mul_le_mul hSEl hlam1 (div_pos hm hN).le hSE.le
  · -- `S_E λ'' ≤ ℓ₁`
    rw [seedConstEll1]
    calc SE * lam ≤ Λ * (M / N) := mul_le_mul hSEu hlam2 hlam0.le hΛ.le
      _ = Λ * M / N := by ring
  · -- (a)
    rw [hγ, hγ, hA, hEsc, hP.internal_eq s (hmem s) t (hmem t), ← ENNReal.ofReal_mul hSE.le, mul_assoc]
  · -- (b)
    rw [hDend]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdD : subdivD H₀ σ₀ β₀ m M ≤ 2 * D''.1 (η 0, η 1) := by
      have := hdE.trans hEle
      nlinarith
    rw [seedConstD0, div_le_iff₀ (by positivity)]
    calc subdivD H₀ σ₀ β₀ m M ≤ 2 * D''.1 (η 0, η 1) := hdD
      _ = 2 * (Λ⁻¹ * Λ) * D''.1 (η 0, η 1) := by rw [inv_mul_cancel₀ hΛ.ne', mul_one]
      _ ≤ 2 * (SD * Λ) * D''.1 (η 0, η 1) := by gcongr
      _ = SD * D''.1 (η 0, η 1) * (2 * Λ) := by ring
  · -- (c)
    rw [hDend, ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hratio : SE ≤ SD * Real.exp (v / 10) := by
      have hlog : Real.log (SE / SD) ≤ v / 10 := (abs_le.1 hcap).2
      have := (Real.log_le_iff_le_exp (div_pos hSE hSD)).1 hlog
      rwa [div_le_iff₀ hSD, mul_comm] at this
    have hexp := q5_exp_mul_le hv (by linarith)
    calc SE * lam = SE * E''.1 (η 0, η 1) := by rw [hElam]
      _ ≤ SE * ((1 + 2 * v) * D''.1 (η 0, η 1)) := mul_le_mul_of_nonneg_left hEle hSE.le
      _ ≤ SD * Real.exp (v / 10) * ((1 + 2 * v) * D''.1 (η 0, η 1)) :=
          mul_le_mul_of_nonneg_right hratio (mul_nonneg (by linarith) hDnn)
      _ = (Real.exp (v / 10) * (1 + 2 * v)) * (SD * D''.1 (η 0, η 1)) := by ring
      _ ≤ (1 + 4 * v) * (SD * D''.1 (η 0, η 1)) :=
          mul_le_mul_of_nonneg_right hexp (mul_nonneg hSD.le hDnn)
  · -- (d) first exit
    set w'' : Rd d := r⁻¹ • (w - c) with hw''
    have hw_eq : w = c + r • w'' := by
      rw [hw'', smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
    have hw''n : ‖w'' - η 0‖ = 1 / 8 := by
      have e : w'' - η 0 = r⁻¹ • (w - γ 0) := by
        rw [hγ0, hw'', smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
        abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), hw]
      field_simp
    have hbar := hRD.exit_barrier hη0K hw''n
    have hcomp := hRD.local_competitor hH₀ hσ₀ hη0K hη1K
      (le_trans (hP.norm_sub_lt 0 h0 1 h1).le (by linarith [subdivDelta0_pos (σ₀ := σ₀) (β₀ := β₀) hH₀]))
    rw [hγ0, hγ1, hw_eq, hA, hDsc, hDsc]
    gcongr
    exact hcomp.le.trans hbar

end HigherDimLQGContinuity
