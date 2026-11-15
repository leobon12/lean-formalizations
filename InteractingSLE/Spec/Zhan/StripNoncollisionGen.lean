/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripNoncollisionFun
import InteractingSLE.Spec.Zhan.StripTimeObs
import InteractingSLE.Spec.Sec4.RepulsionDrift
import InteractingSLE.Foundations.Strip.SLE

/-!
# Noncollision on the strip life: the Lyapunov observable and its Itô generator

Packet PROVE-ZHAN-A3. On the strip coordinates `p = ((V^L, V^R, T), b)` of `StripTimeObs.lean` (the driver is
`W = √κ b + ℓ(V)` by (N1), the end mark is `v = V^{L, last}`, `G = W − v = gapArg p`), the nearest lower left and
right strip gaps are

  `X = log G − log(V^{L,0} − v)`,  `Y = log(V^{R,0} − v) − log G`,

and the Lyapunov observable of `StripNoncollisionFun.lean` is `H = ψ(G) + h(X) + h(Y)` (a side term is absent when
the side has no lower mark), with `Ψ = e^{−λT} H` (`ncLyap`). This file computes the chordal Itô generator of `Ψ`
along the strip density `stripDens` (force-point velocities `2/(V − W)` and clock rate `(W − v)⁻²`):

  `G² · itoGen H = Gψ'(G) A + (κ/2) G²ψ''(G) + genL X A + genR Y A`,  `A = G(ℓ'(λ) − λ_v)`,

(`itoGen_ncObs_stripDens`), splits the force sum `A = Σ_L + τ₋ + Σ_R + 2` and bounds it by Abel summation of the
prefix sums (`Sec4.le_sum_div_of_hasGroupEndSums`), and concludes with `ncGen_bound` that the generator of `Ψ` is
nonpositive for a suitable `λ` (`itoGen_ncLyap_nonpos`).

## Main results

* `itoGen_comp_of_hasDerivAt`, `partialSnd_comp_of_hasDerivAt`: the one-dimensional chain rule for the generator;
* `ncX`, `ncY`, `ncObs`, `ncLyap`, `ncRegion`; `contDiffOn_ncObs`, `contDiffOn_ncLyap`, `isOpen_ncRegion`;
* `itoGen_ncLyap_nonpos`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE

namespace Zhan

/-! ### The one-dimensional chain rule for the Itô generator -/

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E × ℝ → ℝ} {p : E × ℝ}
  {φ φ' : ℝ → ℝ} {d2 : ℝ}

theorem partialSnd_comp_of_hasDerivAt (hF : DifferentiableAt ℝ F p)
    (h1 : HasDerivAt φ (φ' (F p)) (F p)) :
    Ito.partialSnd (fun q => φ (F q)) p = φ' (F p) * Ito.partialSnd F p := by
  have hc : HasFDerivAt (fun q => φ (F q)) (φ' (F p) • fderiv ℝ F p) p :=
    h1.comp_hasFDerivAt p hF.hasFDerivAt
  simp only [Ito.partialSnd, hc.fderiv, smul_apply, smul_eq_mul]

/-- **The chain rule for the Itô generator**: `itoGen (φ ∘ F) = φ'(F) itoGen F + ½ φ''(F) (∂_x F)²`. -/
theorem itoGen_comp_of_hasDerivAt (hφ : ContDiffAt ℝ 2 φ (F p)) (hF : ContDiffAt ℝ 2 F p)
    (h1 : ∀ᶠ x in 𝓝 (F p), HasDerivAt φ (φ' x) x) (h2 : HasDerivAt φ' d2 (F p)) (v : E) :
    Ito.itoGen (fun q => φ (F q)) p v =
      φ' (F p) * Ito.itoGen F p v + 1 / 2 * d2 * Ito.partialSnd F p ^ 2 := by
  have hFd : DifferentiableAt ℝ F p := hF.differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun q => φ (F q)) (φ' (F p) • fderiv ℝ F p) p :=
    h1.self_of_nhds.comp_hasFDerivAt p hFd.hasFDerivAt
  have hfst : Ito.partialFst (fun q => φ (F q)) p v = φ' (F p) * Ito.partialFst F p v := by
    simp only [Ito.partialFst_apply, hc.fderiv, smul_apply, smul_eq_mul]
  have hline : ContinuousAt (fun y : ℝ => ((p.1, y) : E × ℝ)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hevF : ∀ᶠ y in 𝓝 p.2, ContDiffAt ℝ 2 F (p.1, y) :=
    hline.eventually (hF.eventually (by simp))
  have hFcont : ContinuousAt (fun y : ℝ => F (p.1, y)) p.2 :=
    hFd.continuousAt.comp hline
  have hevφ : ∀ᶠ y in 𝓝 p.2, HasDerivAt φ (φ' (F (p.1, y))) (F (p.1, y)) :=
    hFcont.eventually h1
  have hss : Ito.partialSndSnd (fun q => φ (F q)) p =
      d2 * Ito.partialSnd F p * Ito.partialSnd F p + φ' (F p) * Ito.partialSndSnd F p := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt (hφ.comp p hF)
      (g := fun y => φ' (F (p.1, y)) * Ito.partialSnd F (p.1, y))
      ((hevF.and hevφ).mono fun y hy => partialSnd_comp_of_hasDerivAt
        (hy.1.differentiableAt (by norm_num)) hy.2) ?_
    have hy : HasDerivAt (fun y : ℝ => F (p.1, y)) (Ito.partialSnd F p) p.2 :=
      Ito.hasDerivAt_snd_line hFd
    have h2' : HasDerivAt φ' d2 (F (p.1, p.2)) := by simpa using h2
    exact (h2'.comp p.2 hy).mul (Ito.hasDerivAt_partialSnd hF)
  rw [Ito.itoGen, Ito.itoGen, hfst, hss]
  ring

end Chain

/-! ### Affine coordinates -/

variable {nL nR : ℕ}

section Coord

variable (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)

theorem gapArg_line (p : SCoord nL nR × ℝ) (v : SCoord nL nR) (t : ℝ) :
    gapArg κ xL xR ρL ρR (p.1 + t • v, p.2) =
      gapArg κ xL xR ρL ρR p + t * (driftLin₀ ρL ρR v - v.1 (Fin.last nL)) := by
  have hL : ∑ i, ρL i * ((p.1.1 i + t * v.1 i) - xL i) =
      ∑ i, ρL i * (p.1.1 i - xL i) + t * ∑ i, ρL i * v.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : ∑ j, ρR j * ((p.1.2.1 j + t * v.2.1 j) - xR j) =
      ∑ j, ρR j * (p.1.2.1 j - xR j) + t * ∑ j, ρR j * v.2.1 j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [gapArg, driftLin, driftLin₀, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hL, hR]
  ring

theorem partialFst_gapArg (p : SCoord nL nR × ℝ) (v : SCoord nL nR) :
    Ito.partialFst (gapArg κ xL xR ρL ρR) p v = driftLin₀ ρL ρR v - v.1 (Fin.last nL) := by
  refine Ito.partialFst_eq_of_hasDerivAt ((contDiff_gapArg κ xL xR ρL ρR (n := 1)).differentiable
    (by norm_num) p) ?_
  rw [show (fun t : ℝ => gapArg κ xL xR ρL ρR (p.1 + t • v, p.2)) = _ from
    funext (gapArg_line κ xL xR ρL ρR p v)]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (driftLin₀ ρL ρR v - v.1 (Fin.last nL))).const_add
    (gapArg κ xL xR ρL ρR p)

theorem hasDerivAt_gapArg_snd (p : SCoord nL nR × ℝ) :
    HasDerivAt (fun y : ℝ => gapArg κ xL xR ρL ρR (p.1, y)) (Real.sqrt κ) p.2 := by
  have h := (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).add_const (driftLin xL xR ρL ρR p.1)).sub_const
    (p.1.1 (Fin.last nL))
  simpa [gapArg] using h

theorem partialSnd_gapArg (p : SCoord nL nR × ℝ) :
    Ito.partialSnd (gapArg κ xL xR ρL ρR) p = Real.sqrt κ :=
  Ito.partialSnd_eq_of_hasDerivAt ((contDiff_gapArg κ xL xR ρL ρR (n := 1)).differentiable
    (by norm_num) p) (hasDerivAt_gapArg_snd κ xL xR ρL ρR p)

theorem itoGen_gapArg (p : SCoord nL nR × ℝ) (v : SCoord nL nR) :
    Ito.itoGen (gapArg κ xL xR ρL ρR) p v = driftLin₀ ρL ρR v - v.1 (Fin.last nL) := by
  have hss : Ito.partialSndSnd (gapArg κ xL xR ρL ρR) p = 0 :=
    Ito.partialSndSnd_eq_of_hasDerivAt (contDiff_gapArg κ xL xR ρL ρR).contDiffAt
      (g := fun _ => Real.sqrt κ) (Eventually.of_forall fun y => partialSnd_gapArg κ xL xR ρL ρR (p.1, y))
      (hasDerivAt_const _ _)
  rw [Ito.itoGen, partialFst_gapArg, hss]
  ring

/-- A coordinate function of the marks only (no Brownian slot). -/
theorem itoGen_of_fst {f : SCoord nL nR → ℝ} (hf : ContDiff ℝ 2 f) (p : SCoord nL nR × ℝ)
    (v : SCoord nL nR) {d : ℝ} (hd : HasDerivAt (fun t : ℝ => f (p.1 + t • v)) d 0) :
    Ito.itoGen (fun q : SCoord nL nR × ℝ => f q.1) p v = d ∧
      Ito.partialSnd (fun q : SCoord nL nR × ℝ => f q.1) p = 0 := by
  have hc : ContDiff ℝ 2 (fun q : SCoord nL nR × ℝ => f q.1) := hf.comp contDiff_fst
  have hsnd : ∀ q : SCoord nL nR × ℝ, Ito.partialSnd (fun q : SCoord nL nR × ℝ => f q.1) q = 0 :=
    fun q => Ito.partialSnd_eq_of_hasDerivAt (hc.differentiable (by norm_num) q)
      (by simpa using hasDerivAt_const q.2 (f q.1))
  have hss : Ito.partialSndSnd (fun q : SCoord nL nR × ℝ => f q.1) p = 0 :=
    Ito.partialSndSnd_eq_of_hasDerivAt hc.contDiffAt (g := fun _ => 0)
      (Eventually.of_forall fun y => hsnd (p.1, y)) (hasDerivAt_const _ _)
  have hfst : Ito.partialFst (fun q : SCoord nL nR × ℝ => f q.1) p v = d :=
    Ito.partialFst_eq_of_hasDerivAt (hc.differentiable (by norm_num) p) hd
  refine ⟨?_, hsnd p⟩
  rw [Ito.itoGen, hfst, hss]
  ring

end Coord

/-! ### Linearity helpers -/

section Lin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F G : E × ℝ → ℝ} {p : E × ℝ}

theorem itoGen_neg (hF : ContDiffAt ℝ 2 F p) (v : E) :
    Ito.itoGen (fun q => -F q) p v = -Ito.itoGen F p v := by
  have h := itoGen_comp_of_hasDerivAt (φ := fun x => -x) (φ' := fun _ => -1) (d2 := 0) (F := F) (p := p)
    contDiff_id.neg.contDiffAt hF (Eventually.of_forall fun x => by simpa using hasDerivAt_neg x)
    (hasDerivAt_const _ _) v
  rw [h]; ring

theorem itoGen_sub (hF : ContDiffAt ℝ 2 F p) (hG : ContDiffAt ℝ 2 G p) (v : E) :
    Ito.itoGen (fun q => F q - G q) p v = Ito.itoGen F p v - Ito.itoGen G p v := by
  have e : (fun q => F q - G q) = fun q => F q + (fun q => -G q) q := by funext q; ring
  rw [e, Ito.itoGen_add hF hG.neg, itoGen_neg hG]; ring

theorem partialSnd_sub (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    Ito.partialSnd (fun q => F q - G q) p = Ito.partialSnd F p - Ito.partialSnd G p := by
  simp only [Ito.partialSnd, fderiv_fun_sub hF hG, sub_apply]

theorem partialSnd_add (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    Ito.partialSnd (fun q => F q + G q) p = Ito.partialSnd F p + Ito.partialSnd G p := by
  simp only [Ito.partialSnd, fderiv_fun_add hF hG, add_apply]

/-- The generator of `log ∘ F` at a point where `F > 0`. -/
theorem itoGen_log (hF : ContDiffAt ℝ 2 F p) (hpos : 0 < F p) (v : E) :
    Ito.itoGen (fun q => Real.log (F q)) p v =
      (F p)⁻¹ * Ito.itoGen F p v - 1 / 2 * ((F p) ^ 2)⁻¹ * Ito.partialSnd F p ^ 2 := by
  have h := itoGen_comp_of_hasDerivAt (φ := Real.log) (φ' := fun x => x⁻¹) (d2 := -((F p) ^ 2)⁻¹)
    (Real.contDiffAt_log.2 hpos.ne') hF
    ((eventually_ne_nhds hpos.ne').mono fun x hx => Real.hasDerivAt_log hx)
    (hasDerivAt_inv hpos.ne') v
  rw [h]; ring

theorem partialSnd_log (hF : DifferentiableAt ℝ F p) (hpos : 0 < F p) :
    Ito.partialSnd (fun q => Real.log (F q)) p = (F p)⁻¹ * Ito.partialSnd F p :=
  partialSnd_comp_of_hasDerivAt (φ' := fun x => x⁻¹) hF (Real.hasDerivAt_log hpos.ne')

end Lin

/-! ### The strip gaps and the Lyapunov observable -/

section Obs

variable (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)

/-- `V^{L,i} − v` for a lower left mark `i`. -/
def ncEL (i : Fin nL) (p : SCoord nL nR × ℝ) : ℝ := p.1.1 i.castSucc - p.1.1 (Fin.last nL)

/-- `V^{R,j} − v` for a right mark `j`. -/
def ncFR (j : Fin nR) (p : SCoord nL nR × ℝ) : ℝ := p.1.2.1 j - p.1.1 (Fin.last nL)

/-- The strip gap of the lower left mark `i`: `X = log G − log(V^{L,i} − v)` (`= ξ − p^L_i` in strip coordinates). -/
def ncX (i : Fin nL) (p : SCoord nL nR × ℝ) : ℝ :=
  Real.log (gapArg κ xL xR ρL ρR p) - Real.log (ncEL i p)

/-- The strip gap of the right mark `j`: `Y = log(V^{R,j} − v) − log G` (`= p^R_j − ξ`). -/
def ncY (j : Fin nR) (p : SCoord nL nR × ℝ) : ℝ :=
  Real.log (ncFR j p) - Real.log (gapArg κ xL xR ρL ρR p)

/-- The open region of the Lyapunov observable: `G > 0` and the nearest lower marks strictly separated from the
driver (`v < V^{L,0} < W < V^{R,0}`). -/
def ncRegion : Set (SCoord nL nR × ℝ) :=
  {p | 0 < gapArg κ xL xR ρL ρR p ∧
    (∀ h : 0 < nL, 0 < ncEL ⟨0, h⟩ p ∧ ncEL ⟨0, h⟩ p < gapArg κ xL xR ρL ρR p) ∧
    ∀ h : 0 < nR, gapArg κ xL xR ρL ρR p < ncFR ⟨0, h⟩ p}

/-- **The Lyapunov observable** `H = ψ(G) + h(X) + h(Y)` (side terms only for nonempty sides). -/
def ncObs (β c₁ c₂ : ℝ) (p : SCoord nL nR × ℝ) : ℝ :=
  ncPsi (gapArg κ xL xR ρL ρR p)
    + (if h : 0 < nL then ncH β c₁ c₂ (ncX κ xL xR ρL ρR ⟨0, h⟩ p) else 0)
    + (if h : 0 < nR then ncH β c₁ c₂ (ncY κ xL xR ρL ρR ⟨0, h⟩ p) else 0)

/-- `Ψ = e^{−λT} H` (`T` the strip clock coordinate). -/
def ncLyap (β c₁ c₂ lam : ℝ) (p : SCoord nL nR × ℝ) : ℝ :=
  Real.exp (-(lam * p.1.2.2)) * ncObs κ xL xR ρL ρR β c₁ c₂ p

theorem contDiff_ncEL (i : Fin nL) {n : WithTop ℕ∞} : ContDiff ℝ n (ncEL (nR := nR) i) := by
  unfold ncEL; fun_prop

theorem contDiff_ncFR (j : Fin nR) {n : WithTop ℕ∞} : ContDiff ℝ n (ncFR (nL := nL) j) := by
  unfold ncFR; fun_prop

theorem isOpen_ncRegion : IsOpen (ncRegion κ xL xR ρL ρR) := by
  have hg := (contDiff_gapArg κ xL xR ρL ρR (n := 0)).continuous
  have h1 : IsOpen {p : SCoord nL nR × ℝ | 0 < gapArg κ xL xR ρL ρR p} := isOpen_lt continuous_const hg
  have h2 : IsOpen {p : SCoord nL nR × ℝ | ∀ h : 0 < nL,
      0 < ncEL ⟨0, h⟩ p ∧ ncEL ⟨0, h⟩ p < gapArg κ xL xR ρL ρR p} := by
    by_cases hn : 0 < nL
    · have e : {p : SCoord nL nR × ℝ | ∀ h : 0 < nL,
          0 < ncEL ⟨0, h⟩ p ∧ ncEL ⟨0, h⟩ p < gapArg κ xL xR ρL ρR p} =
          {p | 0 < ncEL ⟨0, hn⟩ p} ∩ {p | ncEL ⟨0, hn⟩ p < gapArg κ xL xR ρL ρR p} := by
        ext p; simp only [mem_ofPred_eq, mem_inter_iff]
        exact ⟨fun h => h hn, fun h _ => h⟩
      rw [e]
      exact (isOpen_lt continuous_const (contDiff_ncEL _ (n := 0)).continuous).inter
        (isOpen_lt (contDiff_ncEL _ (n := 0)).continuous hg)
    · have e : {p : SCoord nL nR × ℝ | ∀ h : 0 < nL,
          0 < ncEL ⟨0, h⟩ p ∧ ncEL ⟨0, h⟩ p < gapArg κ xL xR ρL ρR p} = univ := by
        ext p; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact fun h => absurd h hn
      rw [e]; exact isOpen_univ
  have h3 : IsOpen {p : SCoord nL nR × ℝ | ∀ h : 0 < nR, gapArg κ xL xR ρL ρR p < ncFR ⟨0, h⟩ p} := by
    by_cases hn : 0 < nR
    · have e : {p : SCoord nL nR × ℝ | ∀ h : 0 < nR, gapArg κ xL xR ρL ρR p < ncFR ⟨0, h⟩ p} =
          {p | gapArg κ xL xR ρL ρR p < ncFR ⟨0, hn⟩ p} := by
        ext p; simp only [mem_ofPred_eq]; exact ⟨fun h => h hn, fun h _ => h⟩
      rw [e]
      exact isOpen_lt hg (contDiff_ncFR _ (n := 0)).continuous
    · have e : {p : SCoord nL nR × ℝ | ∀ h : 0 < nR, gapArg κ xL xR ρL ρR p < ncFR ⟨0, h⟩ p} = univ := by
        ext p; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact fun h => absurd h hn
      rw [e]; exact isOpen_univ
  exact h1.inter (h2.inter h3)

variable {κ xL xR ρL ρR}

theorem ncX_pos {p : SCoord nL nR × ℝ} (hp : p ∈ ncRegion κ xL xR ρL ρR) (h : 0 < nL) :
    0 < ncX κ xL xR ρL ρR ⟨0, h⟩ p := by
  obtain ⟨hg, hL, -⟩ := hp
  have := Real.log_lt_log (hL h).1 (hL h).2
  simp only [ncX]; linarith

theorem ncY_pos {p : SCoord nL nR × ℝ} (hp : p ∈ ncRegion κ xL xR ρL ρR) (h : 0 < nR) :
    0 < ncY κ xL xR ρL ρR ⟨0, h⟩ p := by
  obtain ⟨hg, -, hR⟩ := hp
  have := Real.log_lt_log hg (hR h)
  simp only [ncY]; linarith

theorem contDiffAt_ncX {p : SCoord nL nR × ℝ} (hp : p ∈ ncRegion κ xL xR ρL ρR) (h : 0 < nL)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (ncX κ xL xR ρL ρR ⟨0, h⟩) p := by
  obtain ⟨hg, hL, -⟩ := hp
  exact ((contDiff_gapArg κ xL xR ρL ρR).contDiffAt.log hg.ne').sub
    ((contDiff_ncEL _).contDiffAt.log (hL h).1.ne')

theorem contDiffAt_ncY {p : SCoord nL nR × ℝ} (hp : p ∈ ncRegion κ xL xR ρL ρR) (h : 0 < nR)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (ncY κ xL xR ρL ρR ⟨0, h⟩) p := by
  obtain ⟨hg, -, hR⟩ := hp
  exact ((contDiff_ncFR _).contDiffAt.log (hg.trans (hR h)).ne').sub
    ((contDiff_gapArg κ xL xR ρL ρR).contDiffAt.log hg.ne')

theorem contDiffAt_ncH {β c₁ c₂ x : ℝ} (hx : 0 < x) : ContDiffAt ℝ 3 (ncH β c₁ c₂) x :=
  (contDiffOn_ncH (n := 3)).contDiffAt (Ioi_mem_nhds hx)

theorem contDiffAt_ncPsi {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ 3 ncPsi x :=
  (contDiffOn_ncPsi (n := 3)).contDiffAt (Ioi_mem_nhds hx)

theorem contDiffAt_ncObs {β c₁ c₂ : ℝ} {p : SCoord nL nR × ℝ} (hp : p ∈ ncRegion κ xL xR ρL ρR) :
    ContDiffAt ℝ 3 (ncObs κ xL xR ρL ρR β c₁ c₂) p := by
  have h1 : ContDiffAt ℝ 3 (fun q => ncPsi (gapArg κ xL xR ρL ρR q)) p :=
    (contDiffAt_ncPsi hp.1).comp p (contDiff_gapArg κ xL xR ρL ρR).contDiffAt
  have h2 : ContDiffAt ℝ 3 (fun q => if h : 0 < nL then ncH β c₁ c₂ (ncX κ xL xR ρL ρR ⟨0, h⟩ q)
      else 0) p := by
    by_cases hn : 0 < nL
    · simp only [hn, ↓reduceDIte]
      exact (contDiffAt_ncH (ncX_pos hp hn)).comp p (contDiffAt_ncX hp hn)
    · simp only [hn, ↓reduceDIte]; exact contDiffAt_const
  have h3 : ContDiffAt ℝ 3 (fun q => if h : 0 < nR then ncH β c₁ c₂ (ncY κ xL xR ρL ρR ⟨0, h⟩ q)
      else 0) p := by
    by_cases hn : 0 < nR
    · simp only [hn, ↓reduceDIte]
      exact (contDiffAt_ncH (ncY_pos hp hn)).comp p (contDiffAt_ncY hp hn)
    · simp only [hn, ↓reduceDIte]; exact contDiffAt_const
  exact (h1.add h2).add h3

theorem contDiffOn_ncObs {β c₁ c₂ : ℝ} :
    ContDiffOn ℝ 3 (ncObs κ xL xR ρL ρR β c₁ c₂) (ncRegion κ xL xR ρL ρR) :=
  fun _ hp => (contDiffAt_ncObs hp).contDiffWithinAt

theorem contDiffOn_ncLyap {β c₁ c₂ lam : ℝ} :
    ContDiffOn ℝ 3 (ncLyap κ xL xR ρL ρR β c₁ c₂ lam) (ncRegion κ xL xR ρL ρR) := by
  have h : ContDiff ℝ 3 (fun p : SCoord nL nR × ℝ => Real.exp (-(lam * p.1.2.2))) := by fun_prop
  exact h.contDiffOn.mul contDiffOn_ncObs

end Obs

/-! ### Generators of the pieces -/

section Pieces

variable {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}

theorem itoGen_ncEL (i : Fin nL) (p : SCoord nL nR × ℝ) (v : SCoord nL nR) :
    Ito.itoGen (ncEL i) p v = v.1 i.castSucc - v.1 (Fin.last nL) ∧ Ito.partialSnd (ncEL i) p = 0 := by
  have hf : ContDiff ℝ 2 (fun q : SCoord nL nR => q.1 i.castSucc - q.1 (Fin.last nL)) := by fun_prop
  refine itoGen_of_fst hf p v ?_
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const (v.1 i.castSucc - v.1 (Fin.last nL))).const_add
    (p.1.1 i.castSucc - p.1.1 (Fin.last nL))
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv (by simp)
  simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul, id]
  ring

theorem itoGen_ncFR (j : Fin nR) (p : SCoord nL nR × ℝ) (v : SCoord nL nR) :
    Ito.itoGen (ncFR j) p v = v.2.1 j - v.1 (Fin.last nL) ∧ Ito.partialSnd (ncFR j) p = 0 := by
  have hf : ContDiff ℝ 2 (fun q : SCoord nL nR => q.2.1 j - q.1 (Fin.last nL)) := by fun_prop
  refine itoGen_of_fst hf p v ?_
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const (v.2.1 j - v.1 (Fin.last nL))).const_add
    (p.1.2.1 j - p.1.1 (Fin.last nL))
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv (by simp)
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, id]
  ring

theorem itoGen_ncPsi_gapArg (hκ : 0 ≤ κ) {p : SCoord nL nR × ℝ} (hg : 0 < gapArg κ xL xR ρL ρR p)
    (v : SCoord nL nR) :
    Ito.itoGen (fun q => ncPsi (gapArg κ xL xR ρL ρR q)) p v =
      ncPsiD (gapArg κ xL xR ρL ρR p) * (driftLin₀ ρL ρR v - v.1 (Fin.last nL)) +
        1 / 2 * ncPsiDD (gapArg κ xL xR ρL ρR p) * κ := by
  rw [itoGen_comp_of_hasDerivAt (φ' := ncPsiD) ((contDiffAt_ncPsi hg).of_le (by norm_num))
    (contDiff_gapArg κ xL xR ρL ρR).contDiffAt
    ((eventually_gt_nhds hg).mono fun x hx => hasDerivAt_ncPsi hx) (hasDerivAt_ncPsiD hg) v,
    itoGen_gapArg, partialSnd_gapArg, Real.sq_sqrt hκ]

theorem itoGen_ncX (hκ : 0 ≤ κ) {p : SCoord nL nR × ℝ} (hp : p ∈ ncRegion κ xL xR ρL ρR) (h : 0 < nL)
    (v : SCoord nL nR) :
    Ito.itoGen (ncX κ xL xR ρL ρR ⟨0, h⟩) p v =
      (gapArg κ xL xR ρL ρR p)⁻¹ * (driftLin₀ ρL ρR v - v.1 (Fin.last nL))
        - 1 / 2 * ((gapArg κ xL xR ρL ρR p) ^ 2)⁻¹ * κ
        - (ncEL ⟨0, h⟩ p)⁻¹ * (v.1 (⟨0, h⟩ : Fin nL).castSucc - v.1 (Fin.last nL)) ∧
      Ito.partialSnd (ncX κ xL xR ρL ρR ⟨0, h⟩) p = (gapArg κ xL xR ρL ρR p)⁻¹ * Real.sqrt κ := by
  obtain ⟨hg, hL, -⟩ := hp
  have hG : ContDiffAt ℝ 2 (gapArg κ xL xR ρL ρR) p := (contDiff_gapArg κ xL xR ρL ρR).contDiffAt
  have hE : ContDiffAt ℝ 2 (ncEL (nR := nR) ⟨0, h⟩) p := (contDiff_ncEL _).contDiffAt
  obtain ⟨hE1, hE2⟩ := itoGen_ncEL (nR := nR) ⟨0, h⟩ p v
  have e : ncX κ xL xR ρL ρR ⟨0, h⟩ = fun q => Real.log (gapArg κ xL xR ρL ρR q) -
      Real.log (ncEL ⟨0, h⟩ q) := rfl
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [itoGen_sub (hG.log hg.ne') (hE.log (hL h).1.ne'), itoGen_log hG hg, itoGen_log hE (hL h).1,
      itoGen_gapArg, partialSnd_gapArg, Real.sq_sqrt hκ, hE1, hE2]
    ring
  · rw [partialSnd_sub ((hG.log hg.ne').differentiableAt (by norm_num))
      ((hE.log (hL h).1.ne').differentiableAt (by norm_num)),
      partialSnd_log (hG.differentiableAt (by norm_num)) hg,
      partialSnd_log (hE.differentiableAt (by norm_num)) (hL h).1, partialSnd_gapArg, hE2]
    ring

theorem itoGen_ncY (hκ : 0 ≤ κ) {p : SCoord nL nR × ℝ} (hp : p ∈ ncRegion κ xL xR ρL ρR) (h : 0 < nR)
    (v : SCoord nL nR) :
    Ito.itoGen (ncY κ xL xR ρL ρR ⟨0, h⟩) p v =
      (ncFR ⟨0, h⟩ p)⁻¹ * (v.2.1 ⟨0, h⟩ - v.1 (Fin.last nL))
        - ((gapArg κ xL xR ρL ρR p)⁻¹ * (driftLin₀ ρL ρR v - v.1 (Fin.last nL))
          - 1 / 2 * ((gapArg κ xL xR ρL ρR p) ^ 2)⁻¹ * κ) ∧
      Ito.partialSnd (ncY κ xL xR ρL ρR ⟨0, h⟩) p = -((gapArg κ xL xR ρL ρR p)⁻¹ * Real.sqrt κ) := by
  obtain ⟨hg, -, hR⟩ := hp
  have hf : 0 < ncFR (nL := nL) ⟨0, h⟩ p := hg.trans (hR h)
  have hG : ContDiffAt ℝ 2 (gapArg κ xL xR ρL ρR) p := (contDiff_gapArg κ xL xR ρL ρR).contDiffAt
  have hF : ContDiffAt ℝ 2 (ncFR (nL := nL) ⟨0, h⟩) p := (contDiff_ncFR _).contDiffAt
  obtain ⟨hF1, hF2⟩ := itoGen_ncFR (nL := nL) ⟨0, h⟩ p v
  have e : ncY κ xL xR ρL ρR ⟨0, h⟩ = fun q => Real.log (ncFR ⟨0, h⟩ q) -
      Real.log (gapArg κ xL xR ρL ρR q) := rfl
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [itoGen_sub (hF.log hf.ne') (hG.log hg.ne'), itoGen_log hG hg, itoGen_log hF hf,
      itoGen_gapArg, partialSnd_gapArg, Real.sq_sqrt hκ, hF1, hF2]
    ring
  · rw [partialSnd_sub ((hF.log hf.ne').differentiableAt (by norm_num))
      ((hG.log hg.ne').differentiableAt (by norm_num)),
      partialSnd_log (hF.differentiableAt (by norm_num)) hf,
      partialSnd_log (hG.differentiableAt (by norm_num)) hg, partialSnd_gapArg, hF2]
    ring

theorem hasDerivAt_deriv_ncH {β c₁ c₂ x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv (ncH β c₁ c₂)) (deriv (deriv (ncH β c₁ c₂)) x) x := by
  have hD : ContDiffOn ℝ 2 (deriv (ncH β c₁ c₂)) (Ioi 0) :=
    (contDiffOn_ncH (n := 3)).deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ((hD.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt

/-- The generator of `h ∘ F` at a point where `F > 0`. -/
theorem itoGen_ncH_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E × ℝ → ℝ}
    {p : E × ℝ} {β c₁ c₂ : ℝ} (hF : ContDiffAt ℝ 2 F p) (hpos : 0 < F p) (v : E) :
    Ito.itoGen (fun q => ncH β c₁ c₂ (F q)) p v =
      deriv (ncH β c₁ c₂) (F p) * Ito.itoGen F p v +
        1 / 2 * deriv (deriv (ncH β c₁ c₂)) (F p) * Ito.partialSnd F p ^ 2 :=
  itoGen_comp_of_hasDerivAt ((contDiffAt_ncH hpos).of_le (by norm_num)) hF
    ((eventually_gt_nhds hpos).mono fun x hx =>
      (((contDiffAt_ncH (β := β) (c₁ := c₁) (c₂ := c₂) hx).differentiableAt (by norm_num)).hasDerivAt))
    (hasDerivAt_deriv_ncH hpos) v

end Pieces

/-! ### The generator along the strip density -/

section Strip

variable {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}

theorem itoGen_const' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (p : E × ℝ) (v : E) :
    Ito.itoGen (fun _ : E × ℝ => c) p v = 0 := by
  simp [Ito.itoGen, Ito.partialFst, Ito.partialSndSnd]

/-- The force sum of the driver at the strip density: `A = G (ℓ'(λ) − λ_v)`, `G = W − v`. -/
def ncA (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ) (w : ℝ) (vL : Fin (nL + 1) → ℝ) (vR : Fin nR → ℝ) : ℝ :=
  (w - vL (Fin.last nL)) * (driftLin₀ ρL ρR (stripDens w vL vR) - (stripDens w vL vR).1 (Fin.last nL))

theorem alg_ncX {G e D κ : ℝ} (hG : 0 < G) (he : 0 < e) (heG : e < G) :
    G ^ 2 * (G⁻¹ * D - 1 / 2 * (G ^ 2)⁻¹ * κ - e⁻¹ * (2 / ((e - G)) - 2 / (-G))) =
      G * D - κ / 2 + 2 * (G / (G - e)) := by
  have h1 : e - G ≠ 0 := by linarith
  have h2 : G - e ≠ 0 := by linarith
  field_simp
  ring

theorem alg_ncY {G f D κ : ℝ} (hG : 0 < G) (hf : G < f) :
    G ^ 2 * (f⁻¹ * (2 / (f - G) - 2 / (-G)) - (G⁻¹ * D - 1 / 2 * (G ^ 2)⁻¹ * κ)) =
      -(G * D) + κ / 2 + 2 * (G / (f - G)) := by
  have h1 : f - G ≠ 0 := by linarith
  have h2 : f ≠ 0 := by linarith
  field_simp
  ring

theorem uOf_log_sub {G e : ℝ} (hG : 0 < G) (he : 0 < e) (heG : e < G) :
    uOf (Real.log G - Real.log e) = G / (G - e) := by
  have h : Real.exp (-(Real.log G - Real.log e)) = e / G := by
    rw [neg_sub, Real.exp_sub, Real.exp_log he, Real.exp_log hG]
  have h2 : G - e ≠ 0 := by linarith
  rw [uOf, h]
  field_simp

theorem wOf_log_sub {G f : ℝ} (hG : 0 < G) (hf : G < f) :
    wOf (Real.log f - Real.log G) = G / (f - G) := by
  have hf0 : 0 < f := hG.trans hf
  have h : Real.exp (-(Real.log f - Real.log G)) = G / f := by
    rw [neg_sub, Real.exp_sub, Real.exp_log hG, Real.exp_log hf0]
  have h2 : f - G ≠ 0 := by linarith
  rw [wOf, h]
  field_simp

/-- **The generator identity** for `H` along the strip density: `G² itoGen H = Gψ'(G)A + (κ/2)G²ψ''(G) + genL X A
+ genR Y A` (side terms only for nonempty sides). -/
theorem sq_mul_itoGen_ncObs (hκ : 0 ≤ κ) {β c₁ c₂ : ℝ} {vL : Fin (nL + 1) → ℝ} {vR : Fin nR → ℝ} {T b w : ℝ}
    (hw : w = Real.sqrt κ * b + driftLin xL xR ρL ρR (vL, vR, T))
    (hp : ((vL, vR, T), b) ∈ ncRegion κ xL xR ρL ρR) :
    (w - vL (Fin.last nL)) ^ 2 * Ito.itoGen (ncObs κ xL xR ρL ρR β c₁ c₂) ((vL, vR, T), b)
        (stripDens w vL vR) =
      ((w - vL (Fin.last nL)) * ncPsiD (w - vL (Fin.last nL)) * ncA ρL ρR w vL vR
        + κ / 2 * ((w - vL (Fin.last nL)) ^ 2 * ncPsiDD (w - vL (Fin.last nL))))
      + (if h : 0 < nL then genL β c₁ c₂ κ (ncX κ xL xR ρL ρR ⟨0, h⟩ ((vL, vR, T), b))
          (ncA ρL ρR w vL vR) else 0)
      + (if h : 0 < nR then genR β c₁ c₂ κ (ncY κ xL xR ρL ρR ⟨0, h⟩ ((vL, vR, T), b))
          (ncA ρL ρR w vL vR) else 0) := by
  set p : SCoord nL nR × ℝ := ((vL, vR, T), b) with hpdef
  set lam := stripDens w vL vR with hlam
  have hgap : gapArg κ xL xR ρL ρR p = w - vL (Fin.last nL) := by simp only [hpdef, gapArg, hw]
  set G := w - vL (Fin.last nL) with hGdef
  have hG : 0 < G := hgap ▸ hp.1
  set D := driftLin₀ ρL ρR lam - lam.1 (Fin.last nL) with hD
  have hA : ncA ρL ρR w vL vR = G * D := rfl
  have hlast : lam.1 (Fin.last nL) = 2 / (-G) := by
    simp only [hlam, stripDens, hGdef]; congr 1; ring
  -- the three pieces
  have h1 : ContDiffAt ℝ 2 (fun q => ncPsi (gapArg κ xL xR ρL ρR q)) p :=
    ((contDiffAt_ncPsi hp.1).comp p (contDiff_gapArg κ xL xR ρL ρR).contDiffAt).of_le (by norm_num)
  set Lp : SCoord nL nR × ℝ → ℝ := fun q => if h : 0 < nL then ncH β c₁ c₂ (ncX κ xL xR ρL ρR ⟨0, h⟩ q)
    else 0 with hLp
  set Rp : SCoord nL nR × ℝ → ℝ := fun q => if h : 0 < nR then ncH β c₁ c₂ (ncY κ xL xR ρL ρR ⟨0, h⟩ q)
    else 0 with hRp
  have hL : ContDiffAt ℝ 2 Lp p ∧ G ^ 2 * Ito.itoGen Lp p lam =
      (if h : 0 < nL then genL β c₁ c₂ κ (ncX κ xL xR ρL ρR ⟨0, h⟩ p) (G * D) else 0) := by
    by_cases hn : 0 < nL
    · have e : Lp = fun q => ncH β c₁ c₂ (ncX κ xL xR ρL ρR ⟨0, hn⟩ q) := by
        funext q; simp only [hLp, hn, ↓reduceDIte]
      have hX := contDiffAt_ncX (n := 2) hp hn
      have hXp := ncX_pos hp hn
      refine ⟨e ▸ ((contDiffAt_ncH hXp).comp p (contDiffAt_ncX hp hn)).of_le (by norm_num), ?_⟩
      rw [e, itoGen_ncH_comp hX hXp, (itoGen_ncX hκ hp hn lam).1, (itoGen_ncX hκ hp hn lam).2]
      simp only [hn, ↓reduceDIte, genL]
      obtain ⟨-, hLr, -⟩ := hp
      have he := (hLr hn).1
      have heG := (hLr hn).2
      rw [hgap] at heG
      have hEL : ncEL (nR := nR) ⟨0, hn⟩ p = vL (⟨0, hn⟩ : Fin nL).castSucc - vL (Fin.last nL) := rfl
      have hlam0 : lam.1 (⟨0, hn⟩ : Fin nL).castSucc = 2 / (ncEL (nR := nR) ⟨0, hn⟩ p - G) := by
        simp only [hlam, stripDens, hEL, hGdef]; congr 1; ring
      have hXe : ncX κ xL xR ρL ρR ⟨0, hn⟩ p = Real.log G - Real.log (ncEL ⟨0, hn⟩ p) := by
        simp only [ncX, hgap]
      rw [← hD, hgap, hlam0, hlast]
      rw [hXe, uOf_log_sub hG he heG]
      have hs : (G⁻¹ * Real.sqrt κ) ^ 2 = κ * (G ^ 2)⁻¹ := by
        rw [mul_pow, Real.sq_sqrt hκ, inv_pow]; ring
      rw [hs]
      have halg := alg_ncX (D := D) (κ := κ) hG he heG
      have hG2 : G ^ 2 ≠ 0 := by positivity
      calc G ^ 2 * (deriv (ncH β c₁ c₂) (Real.log G - Real.log (ncEL ⟨0, hn⟩ p)) *
            (G⁻¹ * D - 1 / 2 * (G ^ 2)⁻¹ * κ - (ncEL ⟨0, hn⟩ p)⁻¹ *
              (2 / (ncEL ⟨0, hn⟩ p - G) - 2 / -G)) +
            1 / 2 * deriv (deriv (ncH β c₁ c₂)) (Real.log G - Real.log (ncEL ⟨0, hn⟩ p)) *
              (κ * (G ^ 2)⁻¹))
          = deriv (ncH β c₁ c₂) (Real.log G - Real.log (ncEL ⟨0, hn⟩ p)) *
              (G ^ 2 * (G⁻¹ * D - 1 / 2 * (G ^ 2)⁻¹ * κ - (ncEL ⟨0, hn⟩ p)⁻¹ *
                (2 / (ncEL ⟨0, hn⟩ p - G) - 2 / -G))) +
            κ / 2 * deriv (deriv (ncH β c₁ c₂)) (Real.log G - Real.log (ncEL ⟨0, hn⟩ p)) *
              (G ^ 2 * (G ^ 2)⁻¹) := by ring
        _ = _ := by rw [halg, mul_inv_cancel₀ hG2]; ring
    · have e : Lp = fun _ => 0 := by funext q; simp only [hLp, hn, ↓reduceDIte]
      refine ⟨e ▸ contDiffAt_const, ?_⟩
      rw [e, itoGen_const']; simp only [hn, ↓reduceDIte, mul_zero]
  have hR : ContDiffAt ℝ 2 Rp p ∧ G ^ 2 * Ito.itoGen Rp p lam =
      (if h : 0 < nR then genR β c₁ c₂ κ (ncY κ xL xR ρL ρR ⟨0, h⟩ p) (G * D) else 0) := by
    by_cases hn : 0 < nR
    · have e : Rp = fun q => ncH β c₁ c₂ (ncY κ xL xR ρL ρR ⟨0, hn⟩ q) := by
        funext q; simp only [hRp, hn, ↓reduceDIte]
      have hY := contDiffAt_ncY (n := 2) hp hn
      have hYp := ncY_pos hp hn
      refine ⟨e ▸ ((contDiffAt_ncH hYp).comp p (contDiffAt_ncY hp hn)).of_le (by norm_num), ?_⟩
      rw [e, itoGen_ncH_comp hY hYp, (itoGen_ncY hκ hp hn lam).1, (itoGen_ncY hκ hp hn lam).2]
      simp only [hn, ↓reduceDIte, genR]
      obtain ⟨-, -, hRr⟩ := hp
      have hf := hRr hn
      rw [hgap] at hf
      have hFR : ncFR (nL := nL) ⟨0, hn⟩ p = vR ⟨0, hn⟩ - vL (Fin.last nL) := rfl
      have hlam0 : lam.2.1 ⟨0, hn⟩ = 2 / (ncFR (nL := nL) ⟨0, hn⟩ p - G) := by
        simp only [hlam, stripDens, hFR, hGdef]; congr 1; ring
      have hYe : ncY κ xL xR ρL ρR ⟨0, hn⟩ p = Real.log (ncFR ⟨0, hn⟩ p) - Real.log G := by
        simp only [ncY, hgap]
      rw [← hD, hgap, hlam0, hlast]
      rw [hYe, wOf_log_sub hG hf]
      have hs : (-(G⁻¹ * Real.sqrt κ)) ^ 2 = κ * (G ^ 2)⁻¹ := by
        rw [neg_sq, mul_pow, Real.sq_sqrt hκ, inv_pow]; ring
      rw [hs]
      have halg := alg_ncY (D := D) (κ := κ) hG hf
      have hG2 : G ^ 2 ≠ 0 := by positivity
      calc G ^ 2 * (deriv (ncH β c₁ c₂) (Real.log (ncFR ⟨0, hn⟩ p) - Real.log G) *
            ((ncFR ⟨0, hn⟩ p)⁻¹ * (2 / (ncFR ⟨0, hn⟩ p - G) - 2 / -G) -
              (G⁻¹ * D - 1 / 2 * (G ^ 2)⁻¹ * κ)) +
            1 / 2 * deriv (deriv (ncH β c₁ c₂)) (Real.log (ncFR ⟨0, hn⟩ p) - Real.log G) *
              (κ * (G ^ 2)⁻¹))
          = deriv (ncH β c₁ c₂) (Real.log (ncFR ⟨0, hn⟩ p) - Real.log G) *
              (G ^ 2 * ((ncFR ⟨0, hn⟩ p)⁻¹ * (2 / (ncFR ⟨0, hn⟩ p - G) - 2 / -G) -
                (G⁻¹ * D - 1 / 2 * (G ^ 2)⁻¹ * κ))) +
            κ / 2 * deriv (deriv (ncH β c₁ c₂)) (Real.log (ncFR ⟨0, hn⟩ p) - Real.log G) *
              (G ^ 2 * (G ^ 2)⁻¹) := by ring
        _ = _ := by rw [halg, mul_inv_cancel₀ hG2]; ring
    · have e : Rp = fun _ => 0 := by funext q; simp only [hRp, hn, ↓reduceDIte]
      refine ⟨e ▸ contDiffAt_const, ?_⟩
      rw [e, itoGen_const']; simp only [hn, ↓reduceDIte, mul_zero]
  have eobs : ncObs κ xL xR ρL ρR β c₁ c₂ =
      fun q => ((fun q => ncPsi (gapArg κ xL xR ρL ρR q)) q + Lp q) + Rp q := rfl
  rw [eobs, Ito.itoGen_add (h1.add hL.1) hR.1, Ito.itoGen_add h1 hL.1, itoGen_ncPsi_gapArg hκ hp.1,
    hgap, mul_add, mul_add, hL.2, hR.2, hA]
  have hG2 : G ^ 2 ≠ 0 := by positivity
  congr 2
  rw [← hD]
  field_simp

end Strip

/-! ### The force sum: decomposition and Abel bounds -/

section Force

theorem hasGroupEndSums_of_prefix {n : ℕ} {c : ℝ} {ρ : Fin n → ℝ}
    (h : ∀ j : Fin n, c ≤ ∑ i ∈ Finset.Iic j, ρ i) : Sec4.HasGroupEndSums c ρ (fun i => (i : ℝ)) := by
  intro j _
  have e : Finset.univ.filter (fun i => i ≤ j) = Finset.Iic j := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
  rw [e]; exact h j

/-- `A = Σ_L + τ₋ + Σ_R + 2` with `Σ_L = G Σ_{i<nL} ρ_i/(W − V^{L,i})`, `Σ_R = G Σ_j ρ_j/(W − V^{R,j})`. -/
theorem ncA_eq (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ) {w : ℝ} {vL : Fin (nL + 1) → ℝ}
    (vR : Fin nR → ℝ) (hG : vL (Fin.last nL) < w) :
    ncA ρL ρR w vL vR = (w - vL (Fin.last nL)) * ∑ i : Fin nL, ρL i.castSucc / (w - vL i.castSucc)
      + ρL (Fin.last nL) + (w - vL (Fin.last nL)) * ∑ j, ρR j / (w - vR j) + 2 := by
  have hG' : w - vL (Fin.last nL) ≠ 0 := (sub_pos.2 hG).ne'
  have hterm : ∀ (ρ a : ℝ), -(1 / 2) * (ρ * (2 / (a - w))) = ρ / (w - a) := by
    intro ρ a
    rcases eq_or_ne a w with h | h
    · subst h; simp
    · have h1 : a - w ≠ 0 := sub_ne_zero.2 h
      have h2 : w - a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      field_simp; ring
  have hLs : -(1 / 2) * ∑ i, ρL i * (2 / (vL i - w)) =
      ∑ i : Fin nL, ρL i.castSucc / (w - vL i.castSucc) + ρL (Fin.last nL) / (w - vL (Fin.last nL)) := by
    rw [Finset.mul_sum, Fin.sum_univ_castSucc]
    simp only [hterm]
  have hRs : 1 / 2 * ∑ j, ρR j * (2 / (vR j - w)) = -∑ j, ρR j / (w - vR j) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hterm]; ring
  simp only [ncA, driftLin₀, stripDens]
  rw [hLs, hRs]
  have e3 : 2 / (vL (Fin.last nL) - w) = -(2 / (w - vL (Fin.last nL))) := by
    rw [← neg_sub, div_neg]
  rw [e3]
  field_simp
  ring

/-- **Abel bound, left side** ((3.12)): `c G/(W − V^{L,0}) ≤ Σ_L ≤ ...` and `|Σ_L| ≤ B_L G/(W − V^{L,0})`. -/
theorem sideL_bounds {c BL G w : ℝ} {ρ : Fin nL → ℝ} {vL : Fin nL → ℝ} (hn : 0 < nL)
    (hpre : ∀ j : Fin nL, c ≤ ∑ i ∈ Finset.Iic j, ρ i) (hBL : ∑ i, |ρ i| ≤ BL) (hG : 0 < G)
    (hanti : Antitone vL) (h0 : vL ⟨0, hn⟩ < w) :
    c * (G / (w - vL ⟨0, hn⟩)) ≤ G * ∑ i, ρ i / (w - vL i) ∧
      |G * ∑ i, ρ i / (w - vL i)| ≤ BL * (G / (w - vL ⟨0, hn⟩)) := by
  set d : Fin nL → ℝ := fun i => w - vL i with hd
  have hd0 : 0 < d ⟨0, hn⟩ := sub_pos.2 h0
  have hmono : Monotone d := fun i j hij => by simp only [hd]; linarith [hanti hij]
  have hle : ∀ i, d ⟨0, hn⟩ ≤ d i := fun i => hmono (Fin.le_def.2 (Nat.zero_le _))
  have hpos : ∀ i, 0 < d i := fun i => hd0.trans_le (hle i)
  have habel := Sec4.le_sum_div_of_hasGroupEndSums hn (x := fun i => (i : ℝ))
    (fun i j hij => by dsimp only; exact_mod_cast hij) (hasGroupEndSums_of_prefix hpre) hmono hpos
    (fun i j hij => by rw [Fin.ext (by exact_mod_cast hij : (i : ℕ) = j)])
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left habel hG.le
    calc c * (G / (w - vL ⟨0, hn⟩)) = G * (c / d ⟨0, hn⟩) := by simp only [hd]; ring
      _ ≤ _ := this
  · rw [abs_mul, abs_of_pos hG]
    have h1 : |∑ i, ρ i / d i| ≤ ∑ i, |ρ i| / d ⟨0, hn⟩ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_div, abs_of_pos (hpos i)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hd0 (hle i)
    have h2 : ∑ i, |ρ i| / d ⟨0, hn⟩ ≤ BL / d ⟨0, hn⟩ := by
      rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hBL hd0.le
    calc G * |∑ i, ρ i / d i| ≤ G * (BL / d ⟨0, hn⟩) := mul_le_mul_of_nonneg_left (h1.trans h2) hG.le
      _ = BL * (G / (w - vL ⟨0, hn⟩)) := by simp only [hd]; ring

/-- **Abel bound, right side**: `Σ_R ≤ −c G/(V^{R,0} − W)` and `|Σ_R| ≤ B_R G/(V^{R,0} − W)`. -/
theorem sideR_bounds {c BR G w : ℝ} {ρ : Fin nR → ℝ} {vR : Fin nR → ℝ} (hn : 0 < nR)
    (hpre : ∀ j : Fin nR, c ≤ ∑ i ∈ Finset.Iic j, ρ i) (hBR : ∑ i, |ρ i| ≤ BR) (hG : 0 < G)
    (hmono : Monotone vR) (h0 : w < vR ⟨0, hn⟩) :
    G * ∑ j, ρ j / (w - vR j) ≤ -(c * (G / (vR ⟨0, hn⟩ - w))) ∧
      |G * ∑ j, ρ j / (w - vR j)| ≤ BR * (G / (vR ⟨0, hn⟩ - w)) := by
  set d : Fin nR → ℝ := fun j => vR j - w with hd
  have hd0 : 0 < d ⟨0, hn⟩ := sub_pos.2 h0
  have hmono' : Monotone d := fun i j hij => by simp only [hd]; linarith [hmono hij]
  have hle : ∀ i, d ⟨0, hn⟩ ≤ d i := fun i => hmono' (Fin.le_def.2 (Nat.zero_le _))
  have hpos : ∀ i, 0 < d i := fun i => hd0.trans_le (hle i)
  have habel := Sec4.le_sum_div_of_hasGroupEndSums hn (x := fun i => (i : ℝ))
    (fun i j hij => by dsimp only; exact_mod_cast hij) (hasGroupEndSums_of_prefix hpre) hmono' hpos
    (fun i j hij => by rw [Fin.ext (by exact_mod_cast hij : (i : ℕ) = j)])
  have hneg : ∑ j, ρ j / (w - vR j) = -∑ j, ρ j / d j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hd]; rw [← neg_sub, div_neg]
  rw [hneg]
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left habel hG.le
    calc G * -∑ j, ρ j / d j = -(G * ∑ j, ρ j / d j) := by ring
      _ ≤ -(G * (c / d ⟨0, hn⟩)) := neg_le_neg this
      _ = -(c * (G / (vR ⟨0, hn⟩ - w))) := by simp only [hd]; ring
  · rw [abs_mul, abs_neg, abs_of_pos hG]
    have h1 : |∑ i, ρ i / d i| ≤ ∑ i, |ρ i| / d ⟨0, hn⟩ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_div, abs_of_pos (hpos i)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hd0 (hle i)
    have h2 : ∑ i, |ρ i| / d ⟨0, hn⟩ ≤ BR / d ⟨0, hn⟩ := by
      rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hBR hd0.le
    calc G * |∑ i, ρ i / d i| ≤ G * (BR / d ⟨0, hn⟩) := mul_le_mul_of_nonneg_left (h1.trans h2) hG.le
      _ = BR * (G / (vR ⟨0, hn⟩ - w)) := by simp only [hd]; ring

end Force

/-! ### The generator of `Ψ = e^{−λT} H` is nonpositive -/

section Sign

variable {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}

theorem itoGen_ncLyap_eq (β c₁ c₂ lam : ℝ) {p : SCoord nL nR × ℝ} (hp : p ∈ ncRegion κ xL xR ρL ρR)
    (v : SCoord nL nR) :
    Ito.itoGen (ncLyap κ xL xR ρL ρR β c₁ c₂ lam) p v = Real.exp (-(lam * p.1.2.2)) *
      (Ito.itoGen (ncObs κ xL xR ρL ρR β c₁ c₂) p v - lam * v.2.2 * ncObs κ xL xR ρL ρR β c₁ c₂ p) := by
  have hf : ContDiff ℝ 2 (fun q : SCoord nL nR => Real.exp (-(lam * q.2.2))) := by fun_prop
  obtain ⟨hE1, hE2⟩ := itoGen_of_fst hf p v (d := Real.exp (-(lam * p.1.2.2)) * (-(lam * v.2.2))) (by
    have h1 : HasDerivAt (fun t : ℝ => -(lam * (p.1.2.2 + t * v.2.2))) (-(lam * v.2.2)) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const (-(lam * v.2.2))).const_add (-(lam * p.1.2.2))
      refine (this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv (by simp)
      simp only [id]; ring
    have h2 := h1.exp
    have e : (fun t : ℝ => Real.exp (-(lam * (p.1 + t • v).2.2))) =
        fun t => Real.exp (-(lam * (p.1.2.2 + t * v.2.2))) := by
      funext t; simp
    rw [e]; simpa using h2)
  have hE : ContDiffAt ℝ 2 (fun q : SCoord nL nR × ℝ => Real.exp (-(lam * q.1.2.2))) p :=
    (hf.comp contDiff_fst).contDiffAt
  have e : ncLyap κ xL xR ρL ρR β c₁ c₂ lam =
      fun q => Real.exp (-(lam * q.1.2.2)) * ncObs κ xL xR ρL ρR β c₁ c₂ q := rfl
  rw [e, Ito.itoGen_mul hE ((contDiffAt_ncObs hp).of_le (by norm_num)), hE1, hE2]
  ring

theorem log_two_le_ncObs {β c₁ c₂ : ℝ} (hβ : 0 ≤ β) {p : SCoord nL nR × ℝ}
    (hp : p ∈ ncRegion κ xL xR ρL ρR) : Real.log 2 ≤ ncObs κ xL xR ρL ρR β c₁ c₂ p := by
  have h1 := log_two_le_ncPsi hp.1
  have h2 : 0 ≤ (if h : 0 < nL then ncH β c₁ c₂ (ncX κ xL xR ρL ρR ⟨0, h⟩ p) else 0) := by
    by_cases hn : 0 < nL
    · simp only [hn, ↓reduceDIte]; exact ncH_nonneg hβ (ncX_pos hp hn)
    · simp only [hn, ↓reduceDIte, le_refl]
  have h3 : 0 ≤ (if h : 0 < nR then ncH β c₁ c₂ (ncY κ xL xR ρL ρR ⟨0, h⟩ p) else 0) := by
    by_cases hn : 0 < nR
    · simp only [hn, ↓reduceDIte]; exact ncH_nonneg hβ (ncY_pos hp hn)
    · simp only [hn, ↓reduceDIte, le_refl]
  simp only [ncObs]; linarith

/-- **The generator of the Lyapunov process is nonpositive.** Fix `κ > 0`, cutoffs `0 < c₁ < c₂`, bounds `B_L`,
`B_R` of the sums of `|ρ|` of the lower marks, and prefix sums `≥ κ/2 − 2` on both sides. There is `λ ≥ 0` such
that at every state in the region with ordered marks whose two nearest strip gaps satisfy `X + Y > 2c₂` (the
increasing strip distance of the nearest lower marks), the chordal Itô generator of `Ψ = e^{−λT} H` along the strip
density is `≤ 0`. -/
theorem exists_itoGen_ncLyap_nonpos (hκ : 0 < κ) {c₁ c₂ BL BR : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂)
    (hBL : ∑ i : Fin nL, |ρL i.castSucc| ≤ BL) (hBR : ∑ j, |ρR j| ≤ BR)
    (hpreL : ∀ j : Fin nL, κ / 2 - 2 ≤ ∑ i ∈ Finset.Iic j, ρL i.castSucc)
    (hpreR : ∀ j : Fin nR, κ / 2 - 2 ≤ ∑ i ∈ Finset.Iic j, ρR i) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ (vL : Fin (nL + 1) → ℝ) (vR : Fin nR → ℝ) (T b w : ℝ),
      w = Real.sqrt κ * b + driftLin xL xR ρL ρR (vL, vR, T) →
      ((vL, vR, T), b) ∈ ncRegion κ xL xR ρL ρR → Antitone vL → Monotone vR →
      (∀ (hL : 0 < nL) (hR : 0 < nR), 2 * c₂ < ncX κ xL xR ρL ρR ⟨0, hL⟩ ((vL, vR, T), b) +
        ncY κ xL xR ρL ρR ⟨0, hR⟩ ((vL, vR, T), b)) →
      Ito.itoGen (ncLyap κ xL xR ρL ρR (ncBeta κ c₂ BL BR (ρL (Fin.last nL))) c₁ c₂ lam)
        ((vL, vR, T), b) (stripDens w vL vR) ≤ 0 := by
  have hBL0 : 0 ≤ BL := (Finset.sum_nonneg fun i _ => abs_nonneg _).trans hBL
  have hBR0 : 0 ≤ BR := (Finset.sum_nonneg fun i _ => abs_nonneg _).trans hBR
  have hc₂ : 0 < c₂ := hc₁.trans hc
  set τ := ρL (Fin.last nL) with hτ
  obtain ⟨M, hM⟩ := ncGen_bound hκ hc₁ hc (τ := τ) hBL0 hBR0
  set β := ncBeta κ c₂ BL BR τ with hβdef
  have hβ : 0 ≤ β := by
    simp only [hβdef, ncBeta]
    have : 0 ≤ BL * uOf c₂ := mul_nonneg hBL0 (uOf_pos hc₂).le
    have : 0 ≤ BR * wOf c₂ := mul_nonneg hBR0 (wOf_pos hc₂).le
    have := abs_nonneg τ
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max M 0 / Real.log 2, div_nonneg (le_max_right _ _) hlog2.le, ?_⟩
  intro vL vR T b w hw hp hanti hmono hD
  set p : SCoord nL nR × ℝ := ((vL, vR, T), b) with hpdef
  have hgap : gapArg κ xL xR ρL ρR p = w - vL (Fin.last nL) := by simp only [hpdef, gapArg, hw]
  set G := w - vL (Fin.last nL) with hGdef
  have hG : 0 < G := hgap ▸ hp.1
  set A := ncA ρL ρR w vL vR with hAdef
  set lam := max M 0 / Real.log 2 with hlam
  rw [itoGen_ncLyap_eq _ _ _ _ hp]
  refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
  -- the strip variables
  set Xv : ℝ := if h : 0 < nL then ncX κ xL xR ρL ρR ⟨0, h⟩ p else c₂ + 1 with hXv
  set Yv : ℝ := if h : 0 < nR then ncY κ xL xR ρL ρR ⟨0, h⟩ p else c₂ + 1 with hYv
  have hXv0 : 0 < Xv := by
    by_cases hn : 0 < nL
    · simp only [hXv, hn, ↓reduceDIte]; exact ncX_pos hp hn
    · simp only [hXv, hn, ↓reduceDIte]; linarith
  have hYv0 : 0 < Yv := by
    by_cases hn : 0 < nR
    · simp only [hYv, hn, ↓reduceDIte]; exact ncY_pos hp hn
    · simp only [hYv, hn, ↓reduceDIte]; linarith
  have hLterm : (if h : 0 < nL then genL β c₁ c₂ κ (ncX κ xL xR ρL ρR ⟨0, h⟩ p) A else 0) =
      genL β c₁ c₂ κ Xv A := by
    by_cases hn : 0 < nL
    · simp only [hXv, hn, ↓reduceDIte]
    · simp only [hXv, hn, ↓reduceDIte]; rw [genL_eq_zero hc (by linarith)]
  have hRterm : (if h : 0 < nR then genR β c₁ c₂ κ (ncY κ xL xR ρL ρR ⟨0, h⟩ p) A else 0) =
      genR β c₁ c₂ κ Yv A := by
    by_cases hn : 0 < nR
    · simp only [hYv, hn, ↓reduceDIte]
    · simp only [hYv, hn, ↓reduceDIte]; rw [genR_eq_zero hc (by linarith)]
  have hgen := sq_mul_itoGen_ncObs (β := β) (c₁ := c₁) (c₂ := c₂) hκ.le hw hp
  rw [← hGdef, ← hAdef, hLterm, hRterm] at hgen
  -- the side sums
  have hAeq := ncA_eq ρL ρR vR (by linarith [hG, hGdef] : vL (Fin.last nL) < w)
  rw [← hAdef, ← hGdef, ← hτ] at hAeq
  set SL := G * ∑ i : Fin nL, ρL i.castSucc / (w - vL i.castSucc) with hSL
  set SR := G * ∑ j, ρR j / (w - vR j) with hSR
  have hXu : ∀ hn : 0 < nL, uOf Xv = G / (w - vL (⟨0, hn⟩ : Fin nL).castSucc) := by
    intro hn
    obtain ⟨-, hLr, -⟩ := hp
    have he := (hLr hn).1
    have heG := (hLr hn).2
    rw [hgap] at heG
    simp only [hXv, hn, ↓reduceDIte, ncX, hgap]
    rw [uOf_log_sub hG he heG]
    congr 1; simp only [ncEL, hpdef, hGdef]; ring
  have hYw : ∀ hn : 0 < nR, wOf Yv = G / (vR ⟨0, hn⟩ - w) := by
    intro hn
    obtain ⟨-, -, hRr⟩ := hp
    have hf := hRr hn
    rw [hgap] at hf
    simp only [hYv, hn, ↓reduceDIte, ncY, hgap]
    rw [wOf_log_sub hG hf]
    congr 1; simp only [ncFR, hpdef, hGdef]; ring
  have hLb : (0 < nL → (κ / 2 - 2) * uOf Xv ≤ SL) ∧ |SL| ≤ BL * uOf Xv := by
    by_cases hn : 0 < nL
    · obtain ⟨-, hLr, -⟩ := hp
      have h0 : vL (⟨0, hn⟩ : Fin nL).castSucc < w := by
        have := (hLr hn).2; rw [hgap] at this; simp only [ncEL, hpdef] at this; linarith
      have hb := sideL_bounds (vL := fun i : Fin nL => vL i.castSucc) (w := w) hn hpreL hBL hG
        (fun i j hij => hanti (Fin.castSucc_le_castSucc_iff.2 hij)) h0
      rw [hXu hn]
      exact ⟨fun _ => hb.1, hb.2⟩
    · have hn0 : nL = 0 := by omega
      have hz : SL = 0 := by
        simp only [hSL]; subst hn0; simp
      rw [hz, abs_zero]
      exact ⟨fun h => absurd h hn, mul_nonneg hBL0 (uOf_pos hXv0).le⟩
  have hRb : (0 < nR → SR ≤ -((κ / 2 - 2) * wOf Yv)) ∧ |SR| ≤ BR * wOf Yv := by
    by_cases hn : 0 < nR
    · obtain ⟨-, -, hRr⟩ := hp
      have h0 : w < vR ⟨0, hn⟩ := by
        have := hRr hn; rw [hgap] at this; simp only [ncFR, hpdef] at this; linarith
      have hb := sideR_bounds (w := w) hn hpreR hBR hG hmono h0
      rw [hYw hn]
      exact ⟨fun _ => hb.1, hb.2⟩
    · have hn0 : nR = 0 := by omega
      have hz : SR = 0 := by
        simp only [hSR]; subst hn0; simp
      rw [hz, abs_zero]
      exact ⟨fun h => absurd h hn, mul_nonneg hBR0 (wOf_pos hYv0).le⟩
  -- the hypotheses of the generator bound
  have hXY : Xv ≤ c₂ → c₂ < Yv := by
    intro hx
    by_cases hnL : 0 < nL
    · by_cases hnR : 0 < nR
      · have := hD hnL hnR
        simp only [hXv, hnL, ↓reduceDIte] at hx
        simp only [hYv, hnR, ↓reduceDIte]
        linarith
      · simp only [hYv, hnR, ↓reduceDIte]; linarith
    · simp only [hXv, hnL, ↓reduceDIte] at hx; linarith
  have hYX : Yv ≤ c₂ → c₂ < Xv := by
    intro hy
    by_cases hnR : 0 < nR
    · by_cases hnL : 0 < nL
      · have := hD hnL hnR
        simp only [hYv, hnR, ↓reduceDIte] at hy
        simp only [hXv, hnL, ↓reduceDIte]
        linarith
      · simp only [hXv, hnL, ↓reduceDIte]; linarith
    · simp only [hYv, hnR, ↓reduceDIte] at hy; linarith
  have hAl : Xv < c₁ → (κ / 2 - 2) * uOf Xv - BR * wOf Yv + τ + 2 ≤ A := by
    intro hx
    have hnL : 0 < nL := by
      by_contra hn; simp only [hXv, hn, ↓reduceDIte] at hx; linarith
    have h1 := hLb.1 hnL
    have h2 := neg_abs_le SR
    rw [hAeq]; linarith [hRb.2]
  have hAr : Yv < c₁ → A ≤ -((κ / 2 - 2) * wOf Yv) + BL * uOf Xv + τ + 2 := by
    intro hy
    have hnR : 0 < nR := by
      by_contra hn; simp only [hYv, hn, ↓reduceDIte] at hy; linarith
    have h1 := hRb.1 hnR
    have h2 := le_abs_self SL
    rw [hAeq]; linarith [hLb.2]
  have hAabs : |A| ≤ BL * uOf Xv + BR * wOf Yv + |τ| + 2 := by
    rw [hAeq]
    have := abs_add_le (SL + τ + SR) 2
    have := abs_add_le (SL + τ) SR
    have := abs_add_le SL τ
    rw [abs_two] at *
    linarith [hLb.2, hRb.2]
  have hg : G * ncPsiD G * A + κ / 2 * (G ^ 2 * ncPsiDD G) ≤ |A| + 2 * κ := by
    have h1 : G * ncPsiD G * A ≤ |A| := by
      calc G * ncPsiD G * A ≤ |G * ncPsiD G * A| := le_abs_self _
        _ = |G * ncPsiD G| * |A| := abs_mul _ _
        _ ≤ 1 * |A| := mul_le_mul_of_nonneg_right (abs_mul_ncPsiD_le hG) (abs_nonneg _)
        _ = |A| := one_mul _
    have h2 : κ / 2 * (G ^ 2 * ncPsiDD G) ≤ κ / 2 * 3 :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_sq_mul_ncPsiDD_le hG)) (by positivity)
    linarith
  have hbound := hM Xv Yv A _ hXv0 hYv0 hXY hYX hAl hAr hAabs hg
  rw [← hgen, ← hpdef] at hbound
  -- conclude
  have hH := log_two_le_ncObs (β := β) (c₁ := c₁) (c₂ := c₂) hβ hp
  have hlamH : max M 0 ≤ lam * ncObs κ xL xR ρL ρR β c₁ c₂ p := by
    have : lam * Real.log 2 = max M 0 := by simp only [hlam]; field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left hH (div_nonneg (le_max_right _ _) hlog2.le)
  have hT : (stripDens w vL vR).2.2 = (G ^ 2)⁻¹ := by simp only [stripDens, hGdef]
  rw [hT]
  have hG2 : 0 < G ^ 2 := by positivity
  have key : G ^ 2 * (Ito.itoGen (ncObs κ xL xR ρL ρR β c₁ c₂) p (stripDens w vL vR) -
      lam * (G ^ 2)⁻¹ * ncObs κ xL xR ρL ρR β c₁ c₂ p) ≤ 0 := by
    have e : G ^ 2 * (Ito.itoGen (ncObs κ xL xR ρL ρR β c₁ c₂) p (stripDens w vL vR) -
        lam * (G ^ 2)⁻¹ * ncObs κ xL xR ρL ρR β c₁ c₂ p) =
        G ^ 2 * Ito.itoGen (ncObs κ xL xR ρL ρR β c₁ c₂) p (stripDens w vL vR) -
          lam * ncObs κ xL xR ρL ρR β c₁ c₂ p := by
      field_simp
    rw [e]
    linarith [le_max_left M 0]
  by_contra hpos
  push Not at hpos
  have := mul_pos hG2 hpos
  linarith

end Sign

end Zhan

end InteractingSLE
