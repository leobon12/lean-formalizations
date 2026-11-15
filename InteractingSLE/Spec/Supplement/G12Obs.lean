/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripNoncollisionGen
import InteractingSLE.Spec.Ito.TwoPointGen
import InteractingSLE.Spec.Ito.Observable

/-!
# Lemma G12: the mark observable of an arbitrary force word and its Itô generator

Packet PROVE-G12. Supplement §7.9, Lemma G12 (p. 504). For an integrated `SLE_κ(ρ)` evolution of any force word and a
right mark `j₀` (position `y = x_{j₀}`; `Y` the group of right marks at `y`, of total weight `ρ_Y`), the observable

  `Φ = log(V^{j₀} − W) + Σᵢ (ρ_{i,L}/2) log(V^{j₀} − V^{i,L}) + Σ_{j ∉ Y} (ρ_{j,R}/2) log|V^{j₀} − V^{j,R}| + c' T`,
  `c' = κ/2 − 2 − ρ_Y`, `T = ∫ (V^{j₀} − W)⁻²`

(every mark of the word, on both sides of `y`, enters; `Real.log` is `log |·|`) is a continuous local martingale with
`d⟨Φ⟩ = κ dT` before the mark is swallowed. This generalizes the strip observable of PROVE-ZHAN-A2
(`Zhan.stripMartObs`, whose end mark must be the outermost left mark) to marks with force points on both sides.

The generator is computed in the coordinates of the localized Itô formula: `Λ = (V^L, V^R, T)` with density
`(2/(V^L − W), 2/(V^R − W), (V^{j₀} − W)⁻²)` (`g12Dens`), the driver recovered from `W = √κ B + ℓ(V)`,
`ℓ(V) = −½ Σ ρ (V − x)` (the identity (N1)).

* `g12Obs`, `g12Region`, `isOpen_g12Region`, `contDiffOn_g12Obs`;
* `itoGen_g12Obs_dens`: the generator vanishes along the density off collisions (per-mark cancellation
  `G12.mark_term_eq_zero`, and the charge `c'` with the coincident marks of `Y`);
* `g12ExpObs = exp(λΦ − λ²κT/2)`, `itoGen_g12ExpObs_dens`: the exponential martingale has no drift either.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12

variable {nL nR : ℕ}

/-- Coordinates `(V^L, V^R, T)`. -/
abbrev GCoord (nL nR : ℕ) : Type := (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ

/-- `ℓ(q) = −½ Σ ρ (q − x)`. -/
def gDriftLin (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (q : GCoord nL nR) : ℝ :=
  -(1 / 2) * ∑ i, ρL i * (q.1 i - xL i) - (1 / 2) * ∑ j, ρR j * (q.2.1 j - xR j)

/-- Linear part of `ℓ`. -/
def gDriftLin₀ (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (v : GCoord nL nR) : ℝ :=
  -(1 / 2) * ∑ i, ρL i * v.1 i - (1 / 2) * ∑ j, ρR j * v.2.1 j

/-- The right marks off the group of `j₀`. -/
def offY (xR : Fin nR → ℝ) (j₀ : Fin nR) : Finset (Fin nR) := univ.filter fun j => xR j ≠ xR j₀

/-- The right marks of the group of `j₀`. -/
def onY (xR : Fin nR → ℝ) (j₀ : Fin nR) : Finset (Fin nR) := univ.filter fun j => xR j = xR j₀

/-- The weight `ρ_Y` of the group of `j₀`. -/
def rhoY (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR) : ℝ := ∑ j ∈ onY xR j₀, ρR j

/-- The charge `c' = κ/2 − 2 − ρ_Y`. -/
def chargeY (κ : ℝ) (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR) : ℝ := κ / 2 - 2 - rhoY xR ρR j₀

/-- The gap `u = V^{j₀} − W`, with `W = √κ b + ℓ(V)`. -/
def gGap (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR)
    (p : GCoord nL nR × ℝ) : ℝ :=
  p.1.2.1 j₀ - (Real.sqrt κ * p.2 + gDriftLin xL xR ρL ρR p.1)

/-- The state part `Ψ = log u + Σᵢ (ρ_{i,L}/2) log(V^{j₀} − V^{i,L}) + Σ_{j ∉ Y} (ρ_{j,R}/2) log(V^{j₀} − V^{j,R})`. -/
def g12Psi (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR)
    (p : GCoord nL nR × ℝ) : ℝ :=
  Real.log (gGap κ xL xR ρL ρR j₀ p) + ∑ i, ρL i / 2 * Real.log (p.1.2.1 j₀ - p.1.1 i)
    + ∑ j ∈ offY xR j₀, ρR j / 2 * Real.log (p.1.2.1 j₀ - p.1.2.1 j)

/-- **The mark observable** `Φ = Ψ + c' T`. -/
def g12Obs (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR)
    (p : GCoord nL nR × ℝ) : ℝ :=
  g12Psi κ xL xR ρL ρR j₀ p + chargeY κ xR ρR j₀ * p.1.2.2

/-- The open region of smoothness: `u > 0` and `V^{j₀}` distinct from every mark off its group. -/
def g12Region (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR) :
    Set (GCoord nL nR × ℝ) :=
  {p | 0 < gGap κ xL xR ρL ρR j₀ p ∧ (∀ i, p.1.2.1 j₀ - p.1.1 i ≠ 0) ∧
    ∀ j ∈ offY xR j₀, p.1.2.1 j₀ - p.1.2.1 j ≠ 0}

/-- The density `(2/(V^L − w), 2/(V^R − w), (V^{j₀} − w)⁻²)`. -/
def g12Dens (j₀ : Fin nR) (w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) : GCoord nL nR :=
  (fun i => 2 / (vL i - w), fun j => 2 / (vR j - w), ((vR j₀ - w) ^ 2)⁻¹)

variable (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR)

theorem contDiff_gGap {n : WithTop ℕ∞} : ContDiff ℝ n (gGap κ xL xR ρL ρR j₀) := by
  unfold gGap gDriftLin
  fun_prop

theorem isOpen_g12Region : IsOpen (g12Region κ xL xR ρL ρR j₀) := by
  have h1 : IsOpen {p : GCoord nL nR × ℝ | 0 < gGap κ xL xR ρL ρR j₀ p} :=
    isOpen_lt continuous_const (contDiff_gGap κ xL xR ρL ρR j₀ (n := 0)).continuous
  have h2 : IsOpen {p : GCoord nL nR × ℝ | ∀ i, p.1.2.1 j₀ - p.1.1 i ≠ 0} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (by fun_prop) continuous_const
  have h3 : IsOpen {p : GCoord nL nR × ℝ | ∀ j ∈ offY xR j₀, p.1.2.1 j₀ - p.1.2.1 j ≠ 0} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
      isOpen_ne_fun (by fun_prop) continuous_const
  exact h1.inter (h2.inter h3)

theorem contDiffOn_g12Psi {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (g12Psi κ xL xR ρL ρR j₀) (g12Region κ xL xR ρL ρR j₀) := by
  refine ((ContDiffOn.log (contDiff_gGap κ xL xR ρL ρR j₀).contDiffOn fun p hp => hp.1.ne').add
    (ContDiffOn.sum fun i _ => ?_)).add (ContDiffOn.sum fun j hj => ?_)
  · exact contDiffOn_const.mul (ContDiffOn.log (by fun_prop) fun p hp => hp.2.1 i)
  · exact contDiffOn_const.mul (ContDiffOn.log (by fun_prop) fun p hp => hp.2.2 j hj)

theorem contDiffOn_g12Obs {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (g12Obs κ xL xR ρL ρR j₀) (g12Region κ xL xR ρL ρR j₀) :=
  (contDiffOn_g12Psi κ xL xR ρL ρR j₀).add (by fun_prop)

theorem contDiffAt_g12Obs {n : WithTop ℕ∞} {p : GCoord nL nR × ℝ} (hp : p ∈ g12Region κ xL xR ρL ρR j₀) :
    ContDiffAt ℝ n (g12Obs κ xL xR ρL ρR j₀) p :=
  (contDiffOn_g12Obs κ xL xR ρL ρR j₀).contDiffAt ((isOpen_g12Region κ xL xR ρL ρR j₀).mem_nhds hp)

theorem hasDerivAt_log_add_mul {c d : ℝ} (hc : c ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (c + t * d)) (d / c) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => c + t * d) (1 * d) 0 :=
    ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add c
  have h2 := h1.log (by simpa using hc)
  simpa using h2

/-- `∂_Λ` of the mark observable. -/
theorem partialFst_g12Obs {p : GCoord nL nR × ℝ} (hp : p ∈ g12Region κ xL xR ρL ρR j₀) (v : GCoord nL nR) :
    Ito.partialFst (g12Obs κ xL xR ρL ρR j₀) p v =
      (v.2.1 j₀ - gDriftLin₀ ρL ρR v) / gGap κ xL xR ρL ρR j₀ p
      + ∑ i, ρL i / 2 * ((v.2.1 j₀ - v.1 i) / (p.1.2.1 j₀ - p.1.1 i))
      + ∑ j ∈ offY xR j₀, ρR j / 2 * ((v.2.1 j₀ - v.2.1 j) / (p.1.2.1 j₀ - p.1.2.1 j))
      + chargeY κ xR ρR j₀ * v.2.2 := by
  have hd : DifferentiableAt ℝ (g12Obs κ xL xR ρL ρR j₀) p :=
    (contDiffAt_g12Obs κ xL xR ρL ρR j₀ (n := 1) hp).differentiableAt (by norm_num)
  refine Ito.partialFst_eq_of_hasDerivAt hd ?_
  have hL : ∑ i, ρL i * ((p.1.1 i + 0 * v.1 i) - xL i) = ∑ i, ρL i * (p.1.1 i - xL i) := by simp
  have hline : (fun t : ℝ => g12Obs κ xL xR ρL ρR j₀ (p.1 + t • v, p.2)) = fun t =>
      Real.log (gGap κ xL xR ρL ρR j₀ p + t * (v.2.1 j₀ - gDriftLin₀ ρL ρR v))
      + ∑ i, ρL i / 2 * Real.log ((p.1.2.1 j₀ - p.1.1 i) + t * (v.2.1 j₀ - v.1 i))
      + ∑ j ∈ offY xR j₀, ρR j / 2 * Real.log ((p.1.2.1 j₀ - p.1.2.1 j) + t * (v.2.1 j₀ - v.2.1 j))
      + chargeY κ xR ρR j₀ * (p.1.2.2 + t * v.2.2) := by
    funext t
    simp only [g12Obs, g12Psi, gGap, gDriftLin, gDriftLin₀, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e1 : ∑ i, ρL i * (p.1.1 i + t * v.1 i - xL i) =
        ∑ i, ρL i * (p.1.1 i - xL i) + t * ∑ i, ρL i * v.1 i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ j, ρR j * (p.1.2.1 j + t * v.2.1 j - xR j) =
        ∑ j, ρR j * (p.1.2.1 j - xR j) + t * ∑ j, ρR j * v.2.1 j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2]
    congr 1
    · congr 1
      · congr 1
        · congr 1; ring
        · exact Finset.sum_congr rfl fun i _ => by congr 2; ring
      · exact Finset.sum_congr rfl fun j _ => by congr 2; ring
  rw [hline]
  refine (((hasDerivAt_log_add_mul hp.1.ne').add (HasDerivAt.fun_sum fun i _ => ?_)).add
    (HasDerivAt.fun_sum fun j hj => ?_)).add ?_
  · exact (hasDerivAt_log_add_mul (hp.2.1 i)).const_mul _
  · exact (hasDerivAt_log_add_mul (hp.2.2 j hj)).const_mul _
  · have := (((hasDerivAt_id (0 : ℝ)).mul_const v.2.2).const_add p.1.2.2).const_mul (chargeY κ xR ρR j₀)
    simpa using this

/-- The Brownian-slot derivative of the mark observable: `∂_b Φ = −√κ/u`. -/
theorem hasDerivAt_g12Obs_snd {p : GCoord nL nR × ℝ} (hp : 0 < gGap κ xL xR ρL ρR j₀ p) :
    HasDerivAt (fun y : ℝ => g12Obs κ xL xR ρL ρR j₀ (p.1, y))
      (-Real.sqrt κ / gGap κ xL xR ρL ρR j₀ p) p.2 := by
  have h1 : HasDerivAt (fun y : ℝ => p.1.2.1 j₀ - (Real.sqrt κ * y + gDriftLin xL xR ρL ρR p.1))
      (-(Real.sqrt κ * 1)) p.2 :=
    (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).add_const _).const_sub _
  have h2 := (((h1.log hp.ne').add_const (∑ i, ρL i / 2 * Real.log (p.1.2.1 j₀ - p.1.1 i))).add_const
    (∑ j ∈ offY xR j₀, ρR j / 2 * Real.log (p.1.2.1 j₀ - p.1.2.1 j))).add_const
    (chargeY κ xR ρR j₀ * p.1.2.2)
  refine h2.congr_deriv ?_
  simp only [gGap, mul_one, neg_div]

theorem partialSnd_g12Obs {p : GCoord nL nR × ℝ} (hp : p ∈ g12Region κ xL xR ρL ρR j₀) :
    Ito.partialSnd (g12Obs κ xL xR ρL ρR j₀) p = -Real.sqrt κ / gGap κ xL xR ρL ρR j₀ p :=
  Ito.partialSnd_eq_of_hasDerivAt ((contDiffAt_g12Obs κ xL xR ρL ρR j₀ (n := 1) hp).differentiableAt
    (by norm_num)) (hasDerivAt_g12Obs_snd κ xL xR ρL ρR j₀ hp.1)

theorem partialSndSnd_g12Obs (hκ : 0 ≤ κ) {p : GCoord nL nR × ℝ} (hp : p ∈ g12Region κ xL xR ρL ρR j₀) :
    Ito.partialSndSnd (g12Obs κ xL xR ρL ρR j₀) p = -(κ / gGap κ xL xR ρL ρR j₀ p ^ 2) := by
  set c := p.1.2.1 j₀ - gDriftLin xL xR ρL ρR p.1 with hc
  have hline : ContinuousAt (fun y : ℝ => ((p.1, y) : GCoord nL nR × ℝ)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : GCoord nL nR × ℝ) ∈ g12Region κ xL xR ρL ρR j₀ :=
    hline.eventually ((isOpen_g12Region κ xL xR ρL ρR j₀).mem_nhds (by simpa using hp))
  have hg : ∀ y : ℝ, gGap κ xL xR ρL ρR j₀ (p.1, y) = c - Real.sqrt κ * y := fun y => by
    simp only [gGap, hc]; ring
  refine Ito.partialSndSnd_eq_of_hasDerivAt (contDiffAt_g12Obs κ xL xR ρL ρR j₀ hp)
    (g := fun y => -Real.sqrt κ * (c - Real.sqrt κ * y)⁻¹) (hev.mono fun y hy => ?_) ?_
  · rw [partialSnd_g12Obs κ xL xR ρL ρR j₀ hy, hg, div_eq_mul_inv]
  · have h1 : HasDerivAt (fun y : ℝ => c - Real.sqrt κ * y) (-(Real.sqrt κ * 1)) p.2 :=
      ((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).const_sub c
    have hne : c - Real.sqrt κ * p.2 ≠ 0 := by rw [← hg]; exact hp.1.ne'
    have h2 := (h1.inv hne).const_mul (-Real.sqrt κ)
    refine h2.congr_deriv ?_
    have hgp : gGap κ xL xR ρL ρR j₀ p = c - Real.sqrt κ * p.2 := by rw [← hg]
    rw [hgp]
    have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ
    field_simp
    rw [hs]

/-- **The Itô generator of the mark observable.** -/
theorem itoGen_g12Obs (hκ : 0 ≤ κ) {p : GCoord nL nR × ℝ} (hp : p ∈ g12Region κ xL xR ρL ρR j₀)
    (v : GCoord nL nR) :
    Ito.itoGen (g12Obs κ xL xR ρL ρR j₀) p v =
      (v.2.1 j₀ - gDriftLin₀ ρL ρR v) / gGap κ xL xR ρL ρR j₀ p
      + ∑ i, ρL i / 2 * ((v.2.1 j₀ - v.1 i) / (p.1.2.1 j₀ - p.1.1 i))
      + ∑ j ∈ offY xR j₀, ρR j / 2 * ((v.2.1 j₀ - v.2.1 j) / (p.1.2.1 j₀ - p.1.2.1 j))
      + chargeY κ xR ρR j₀ * v.2.2
      - κ / (2 * gGap κ xL xR ρL ρR j₀ p ^ 2) := by
  rw [Ito.itoGen, partialFst_g12Obs κ xL xR ρL ρR j₀ hp, partialSndSnd_g12Obs κ xL xR ρL ρR j₀ hκ hp]
  ring

omit κ xL xR ρL ρR j₀ in
/-- One mark's contribution cancels: `(ρ/2)(2/(a − w))/u + (ρ/2)(2/u − 2/(a − w))/(v − a) = 0`, `u = v − w`. -/
theorem mark_term_eq_zero {ρ a v w : ℝ} (haw : a ≠ w) (hva : v - a ≠ 0) (hvw : v - w ≠ 0) :
    1 / 2 * (ρ * (2 / (a - w))) / (v - w) + ρ / 2 * ((2 / (v - w) - 2 / (a - w)) / (v - a)) = 0 := by
  have h1 : a - w ≠ 0 := sub_ne_zero.2 haw
  field_simp
  ring

/-- **The mark observable has no drift along the evolution** (off collisions of the marks with the driver, with the
marks of the group of `j₀` at `V^{j₀}`). -/
theorem itoGen_g12Obs_dens (hκ : 0 ≤ κ) {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {T b w : ℝ}
    (hw : w = Real.sqrt κ * b + gDriftLin xL xR ρL ρR (vL, vR, T))
    (hp : ((vL, vR, T), b) ∈ g12Region κ xL xR ρL ρR j₀) (hL : ∀ i, vL i ≠ w)
    (hR : ∀ j ∈ offY xR j₀, vR j ≠ w) (hY : ∀ j ∈ onY xR j₀, vR j = vR j₀) :
    Ito.itoGen (g12Obs κ xL xR ρL ρR j₀) ((vL, vR, T), b) (g12Dens j₀ w vL vR) = 0 := by
  rw [itoGen_g12Obs κ xL xR ρL ρR j₀ hκ hp]
  have hg : gGap κ xL xR ρL ρR j₀ ((vL, vR, T), b) = vR j₀ - w := by
    simp only [gGap, hw]
  have hu : vR j₀ - w ≠ 0 := by rw [← hg]; exact hp.1.ne'
  rw [hg]
  simp only [g12Dens, gDriftLin₀]
  set u := vR j₀ - w with hudef
  have hsplitR : ∑ j, ρR j * (2 / (vR j - w)) =
      ∑ j ∈ offY xR j₀, ρR j * (2 / (vR j - w)) + rhoY xR ρR j₀ * (2 / u) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => xR j ≠ xR j₀)]
    congr 1
    rw [rhoY, onY, Finset.sum_mul]
    refine Finset.sum_congr (by ext j; simp) fun j hj => ?_
    have hj' : j ∈ onY xR j₀ := by simpa [onY] using hj
    rw [hY j hj']
  have hLz : ∀ i, 1 / 2 * (ρL i * (2 / (vL i - w))) / u +
      ρL i / 2 * ((2 / u - 2 / (vL i - w)) / (vR j₀ - vL i)) = 0 := fun i =>
    mark_term_eq_zero (hL i) (hp.2.1 i) hu
  have hRz : ∀ j ∈ offY xR j₀, 1 / 2 * (ρR j * (2 / (vR j - w))) / u +
      ρR j / 2 * ((2 / u - 2 / (vR j - w)) / (vR j₀ - vR j)) = 0 := fun j hj =>
    mark_term_eq_zero (hR j hj) (hp.2.2 j hj) hu
  have eL : ∑ i, ρL i / 2 * ((2 / u - 2 / (vL i - w)) / (vR j₀ - vL i)) =
      -(1 / 2 * ∑ i, ρL i * (2 / (vL i - w))) / u := by
    have h := Finset.sum_eq_zero (s := (univ : Finset (Fin nL))) fun i _ => hLz i
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum] at h
    rw [neg_div]
    linarith
  have eR : ∑ j ∈ offY xR j₀, ρR j / 2 * ((2 / u - 2 / (vR j - w)) / (vR j₀ - vR j)) =
      -(1 / 2 * ∑ j ∈ offY xR j₀, ρR j * (2 / (vR j - w))) / u := by
    have h := Finset.sum_eq_zero hRz
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum] at h
    rw [neg_div]
    linarith
  rw [hsplitR, eL, eR]
  simp only [chargeY]
  generalize ∑ i, ρL i * (2 / (vL i - w)) = AL
  generalize ∑ j ∈ offY xR j₀, ρR j * (2 / (vR j - w)) = AR
  field_simp
  ring

/-! ### The exponential martingale -/

/-- The exponential observable `Z_λ = exp(λΦ − λ²κT/2)`. -/
def g12ExpObs (lam : ℝ) (p : GCoord nL nR × ℝ) : ℝ :=
  Real.exp (lam * g12Obs κ xL xR ρL ρR j₀ p + -(lam ^ 2 * κ / 2) * p.1.2.2)

theorem contDiffOn_g12ExpObs (lam : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (g12ExpObs κ xL xR ρL ρR j₀ lam) (g12Region κ xL xR ρL ρR j₀) :=
  Real.contDiff_exp.comp_contDiffOn
    ((contDiffOn_const.mul (contDiffOn_g12Obs κ xL xR ρL ρR j₀)).add (by fun_prop))

theorem itoGen_tObs (c : ℝ) (p : GCoord nL nR × ℝ) (v : GCoord nL nR) :
    Ito.itoGen (fun q : GCoord nL nR × ℝ => c * q.1.2.2) p v = c * v.2.2 := by
  have hc : ContDiff ℝ 2 (fun q : GCoord nL nR × ℝ => c * q.1.2.2) := by fun_prop
  have h1 : Ito.partialFst (fun q : GCoord nL nR × ℝ => c * q.1.2.2) p v = c * v.2.2 := by
    refine Ito.partialFst_eq_of_hasDerivAt (hc.differentiable (by norm_num) p) ?_
    have := (((hasDerivAt_id (0 : ℝ)).mul_const v.2.2).const_add p.1.2.2).const_mul c
    simpa using this
  have h2 : Ito.partialSndSnd (fun q : GCoord nL nR × ℝ => c * q.1.2.2) p = 0 := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt hc.contDiffAt (g := fun _ => 0)
      (Eventually.of_forall fun y => ?_) (hasDerivAt_const _ _)
    refine Ito.partialSnd_eq_of_hasDerivAt (hc.differentiable (by norm_num) _) ?_
    simpa using hasDerivAt_const y (c * p.1.2.2)
  rw [Ito.itoGen, h1, h2]
  ring

/-- **`Z_λ` has no drift along the evolution** (off collisions). -/
theorem itoGen_g12ExpObs_dens (hκ : 0 ≤ κ) (lam : ℝ) {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {T b w : ℝ}
    (hw : w = Real.sqrt κ * b + gDriftLin xL xR ρL ρR (vL, vR, T))
    (hp : ((vL, vR, T), b) ∈ g12Region κ xL xR ρL ρR j₀) (hL : ∀ i, vL i ≠ w)
    (hR : ∀ j ∈ offY xR j₀, vR j ≠ w) (hY : ∀ j ∈ onY xR j₀, vR j = vR j₀) :
    Ito.itoGen (g12ExpObs κ xL xR ρL ρR j₀ lam) ((vL, vR, T), b) (g12Dens j₀ w vL vR) = 0 := by
  set p : GCoord nL nR × ℝ := ((vL, vR, T), b) with hpdef
  have hΦ := contDiffAt_g12Obs κ xL xR ρL ρR j₀ (n := 2) hp
  set H : GCoord nL nR × ℝ → ℝ :=
    fun q => lam * g12Obs κ xL xR ρL ρR j₀ q + -(lam ^ 2 * κ / 2) * q.1.2.2 with hHdef
  have hH1 : ContDiffAt ℝ 2 (fun q => lam * g12Obs κ xL xR ρL ρR j₀ q) p := contDiffAt_const.mul hΦ
  have hH2 : ContDiffAt ℝ 2 (fun q : GCoord nL nR × ℝ => -(lam ^ 2 * κ / 2) * q.1.2.2) p := by fun_prop
  have hH : ContDiffAt ℝ 2 H p := hH1.add hH2
  have e : g12ExpObs κ xL xR ρL ρR j₀ lam = fun q => Real.exp (H q) := rfl
  rw [e, Zhan.itoGen_comp_of_hasDerivAt (φ := Real.exp) (φ' := Real.exp) (d2 := Real.exp (H p))
    Real.contDiff_exp.contDiffAt hH (Eventually.of_forall fun x => Real.hasDerivAt_exp x)
    (Real.hasDerivAt_exp _)]
  have hgenH : Ito.itoGen H p (g12Dens j₀ w vL vR) = -(lam ^ 2 * κ / 2) * (g12Dens j₀ w vL vR).2.2 := by
    have eH : H = fun q => (fun q => lam * g12Obs κ xL xR ρL ρR j₀ q) q +
        (fun q : GCoord nL nR × ℝ => -(lam ^ 2 * κ / 2) * q.1.2.2) q := rfl
    rw [eH, Ito.itoGen_add hH1 hH2, itoGen_tObs,
      Zhan.itoGen_comp_of_hasDerivAt (φ := fun x => lam * x) (φ' := fun _ => lam) (d2 := 0)
        (contDiff_const.mul contDiff_id).contDiffAt hΦ
        (Eventually.of_forall fun x => by simpa using (hasDerivAt_id x).const_mul lam) (hasDerivAt_const _ _),
      itoGen_g12Obs_dens κ xL xR ρL ρR j₀ hκ hw hp hL hR hY]
    ring
  have hsndH : Ito.partialSnd H p = lam * (-Real.sqrt κ / gGap κ xL xR ρL ρR j₀ p) := by
    refine Ito.partialSnd_eq_of_hasDerivAt (hH.differentiableAt (by norm_num)) ?_
    have := ((hasDerivAt_g12Obs_snd κ xL xR ρL ρR j₀ hp.1).const_mul lam).add_const
      (-(lam ^ 2 * κ / 2) * p.1.2.2)
    simpa [hHdef] using this
  rw [hgenH, hsndH]
  have hg : gGap κ xL xR ρL ρR j₀ p = vR j₀ - w := by
    simp only [hpdef, gGap, hw]
  have hG : vR j₀ - w ≠ 0 := by rw [← hg]; exact hp.1.ne'
  rw [hg]
  simp only [g12Dens]
  have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ
  field_simp
  rw [hs]
  ring

end G12

end Supp7

end InteractingSLE
