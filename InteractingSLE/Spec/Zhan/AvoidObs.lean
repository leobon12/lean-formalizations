/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.AvoidMart
import InteractingSLE.Spec.Ito.Observable

/-!
# The strip-clock observable and its Itô drift

Packet PROVE-ZHAN-B. Astra, *Formalization proofs and dependency audit* (`source/external/AstraIG1/`,
text dump L1336–1376, (3.21), ruling R35), in half-plane coordinates.

The state is `(A, C, P, J, (v^L, v^R))` together with the Brownian coordinate `b`: `A = g(r₋)`,
`C = g(r₊)` are the images of the two real points left of `0` that become the strip ends, `P = g(r)` the
image of a real point `0 < r ≤ x^{1,R}`, `J = W − √κ b` the drift integral of the driver, and
`v^{L}, v^{R}` the force points; the driver is `W = √κ b + J`. With `α = W − A`, `γ = W − C`,
`p = 1/α − 1/γ` (the square root of the strip clock rate) the observable is

`Φ = log(γ/α) + m log((P − C)/(P − A))`,

the strip position `X_∞ = log(γ/α) > 0` of the target `∞` plus the compensator of the right forces
(`(P − A)/(P − C)` increases at rate `2p/(P − W)`). Its Itô drift is

`itoGen Φ = c p (1/α + 1/γ) − p D − 2mp/(P − W)`, `c = κ/2 − 2`, `D = Σ ρ/(W − v)`

(`itoGen_stripObs`), and `∂_b Φ = −√κ p` (`partialSnd_stripObs`). When `c ≤ 0`, the left marks lie in
`(C, A)` with Abel bound `Σ ρ^L/(W − v^L) ≥ c/(W − v^{1,L})` (RP4), the right marks lie right of `P`, and
`m = ½ Σ|ρ^R|`, the drift is `≤ c p/γ ≤ 0` (`itoGen_stripObs_nonpos`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Finset
open scoped NNReal

namespace InteractingSLE

namespace Zhan

variable {nL nR : ℕ}

/-- The state space `(A, C, P, J, (v^L, v^R))`. -/
abbrev ObsE (nL nR : ℕ) : Type := ℝ × ℝ × ℝ × ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ))

section Coords

variable (p : ObsE nL nR × ℝ)

/-- The driver `W = √κ b + J`. -/
def obsW (κ : ℝ) : ℝ := Real.sqrt κ * p.2 + p.1.2.2.2.1

/-- The image `A` of `r₋`. -/
def obsA : ℝ := p.1.1
/-- The image `C` of `r₊`. -/
def obsC : ℝ := p.1.2.1
/-- The image `P` of the right reference point. -/
def obsP : ℝ := p.1.2.2.1
/-- The left force points. -/
def obsVL : Fin nL → ℝ := p.1.2.2.2.2.1
/-- The right force points. -/
def obsVR : Fin nR → ℝ := p.1.2.2.2.2.2

end Coords

/-- **The strip-clock observable** `Φ = log(γ/α) + m log((P − C)/(P − A))`. -/
def stripObs (κ m : ℝ) (p : ObsE nL nR × ℝ) : ℝ :=
  Real.log (obsW p κ - obsC p) - Real.log (obsW p κ - obsA p) +
    m * (Real.log (obsP p - obsC p) - Real.log (obsP p - obsA p))

/-- The open region `C < A < W < P`, `v^L < W < v^R`. -/
def stripRegion (κ : ℝ) : Set (ObsE nL nR × ℝ) :=
  {p | obsA p < obsW p κ ∧ obsC p < obsA p ∧ obsW p κ < obsP p ∧ (∀ i, obsVL p i < obsW p κ) ∧
    ∀ j, obsW p κ < obsVR p j}

/-- The force drift `D = Σ ρ^L/(W − v^L) + Σ ρ^R/(W − v^R)`. -/
def obsDrift (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (p : ObsE nL nR × ℝ) : ℝ :=
  (∑ i, ρL i / (obsW p κ - obsVL p i)) + ∑ j, ρR j / (obsW p κ - obsVR p j)

/-- **The vector field** of the state: Loewner flow of `A, C, P, v`, and `J' = D`. -/
def stripField (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (p : ObsE nL nR × ℝ) : ObsE nL nR :=
  (2 / (obsA p - obsW p κ), 2 / (obsC p - obsW p κ), 2 / (obsP p - obsW p κ),
    obsDrift κ ρL ρR p,
    (fun i => 2 / (obsVL p i - obsW p κ), fun j => 2 / (obsVR p j - obsW p κ)))

theorem continuous_obsW (κ : ℝ) : Continuous fun p : ObsE nL nR × ℝ => obsW p κ := by
  unfold obsW; fun_prop

theorem continuous_obsA : Continuous fun p : ObsE nL nR × ℝ => obsA p := by unfold obsA; fun_prop
theorem continuous_obsC : Continuous fun p : ObsE nL nR × ℝ => obsC p := by unfold obsC; fun_prop
theorem continuous_obsP : Continuous fun p : ObsE nL nR × ℝ => obsP p := by unfold obsP; fun_prop
theorem continuous_obsVL (i : Fin nL) : Continuous fun p : ObsE nL nR × ℝ => obsVL p i := by
  unfold obsVL; fun_prop
theorem continuous_obsVR (j : Fin nR) : Continuous fun p : ObsE nL nR × ℝ => obsVR p j := by
  unfold obsVR; fun_prop

theorem isOpen_stripRegion (κ : ℝ) : IsOpen (stripRegion κ : Set (ObsE nL nR × ℝ)) := by
  have hW := continuous_obsW (nL := nL) (nR := nR) κ
  refine (isOpen_lt continuous_obsA hW).inter ((isOpen_lt continuous_obsC continuous_obsA).inter
    ((isOpen_lt hW continuous_obsP).inter ?_))
  have h1 : IsOpen {p : ObsE nL nR × ℝ | ∀ i, obsVL p i < obsW p κ} := by
    have : {p : ObsE nL nR × ℝ | ∀ i, obsVL p i < obsW p κ} =
        ⋂ i, {p | obsVL p i < obsW p κ} := by ext; simp
    rw [this]; exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_obsVL i) hW
  have h2 : IsOpen {p : ObsE nL nR × ℝ | ∀ j, obsW p κ < obsVR p j} := by
    have : {p : ObsE nL nR × ℝ | ∀ j, obsW p κ < obsVR p j} =
        ⋂ j, {p | obsW p κ < obsVR p j} := by ext; simp
    rw [this]; exact isOpen_iInter_of_finite fun j => isOpen_lt hW (continuous_obsVR j)
  exact h1.inter h2

theorem compl_stripRegion_nonempty (κ : ℝ) : (stripRegion κ : Set (ObsE nL nR × ℝ))ᶜ.Nonempty :=
  ⟨0, fun h => by
    have := h.1
    simp only [obsA, obsW, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] at this
    exact lt_irrefl _ this⟩

/-! ### Smoothness -/

section Smooth

variable {κ m : ℝ}

theorem contDiff_obsW (κ : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n fun p : ObsE nL nR × ℝ => obsW p κ := by
  unfold obsW; fun_prop

theorem contDiff_obsA {n : WithTop ℕ∞} : ContDiff ℝ n fun p : ObsE nL nR × ℝ => obsA p := by
  unfold obsA; fun_prop
theorem contDiff_obsC {n : WithTop ℕ∞} : ContDiff ℝ n fun p : ObsE nL nR × ℝ => obsC p := by
  unfold obsC; fun_prop
theorem contDiff_obsP {n : WithTop ℕ∞} : ContDiff ℝ n fun p : ObsE nL nR × ℝ => obsP p := by
  unfold obsP; fun_prop

/-- On the region: `α = W − A`, `γ = W − C`, `P − A`, `P − C` are positive and `α < γ`. -/
theorem stripRegion_pos {p : ObsE nL nR × ℝ} (hp : p ∈ stripRegion κ) :
    0 < obsW p κ - obsA p ∧ 0 < obsW p κ - obsC p ∧ 0 < obsP p - obsA p ∧ 0 < obsP p - obsC p ∧
      obsW p κ - obsA p < obsW p κ - obsC p := by
  obtain ⟨h1, h2, h3, -, -⟩ := hp
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem contDiffOn_stripObs (κ m : ℝ) :
    ContDiffOn ℝ 3 (stripObs (nL := nL) (nR := nR) κ m) (stripRegion κ) := by
  unfold stripObs
  have hW := (contDiff_obsW (nL := nL) (nR := nR) κ (n := 3)).contDiffOn (s := stripRegion κ)
  have hA := (contDiff_obsA (nL := nL) (nR := nR) (n := 3)).contDiffOn (s := stripRegion κ)
  have hC := (contDiff_obsC (nL := nL) (nR := nR) (n := 3)).contDiffOn (s := stripRegion κ)
  have hP := (contDiff_obsP (nL := nL) (nR := nR) (n := 3)).contDiffOn (s := stripRegion κ)
  refine ((hW.sub hC).log fun p hp => (stripRegion_pos hp).2.1.ne').sub
    ((hW.sub hA).log fun p hp => (stripRegion_pos hp).1.ne') |>.add
    (contDiffOn_const.mul (((hP.sub hC).log fun p hp => (stripRegion_pos hp).2.2.2.1.ne').sub
      ((hP.sub hA).log fun p hp => (stripRegion_pos hp).2.2.1.ne')))

theorem stripObs_nonneg (hm : 0 ≤ m) {p : ObsE nL nR × ℝ} (hp : p ∈ stripRegion κ) :
    0 ≤ stripObs κ m p := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := stripRegion_pos hp
  unfold stripObs
  have e1 : Real.log (obsW p κ - obsA p) ≤ Real.log (obsW p κ - obsC p) :=
    Real.log_le_log h1 h5.le
  have e2 : Real.log (obsP p - obsA p) ≤ Real.log (obsP p - obsC p) :=
    Real.log_le_log h3 (by obtain ⟨-, h, -⟩ := hp; linarith)
  nlinarith

theorem continuousOn_stripField (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    ContinuousOn (stripField κ ρL ρR) (stripRegion κ) := by
  have hW := (continuous_obsW (nL := nL) (nR := nR) κ).continuousOn (s := stripRegion κ)
  unfold stripField
  refine ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_
    (ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ ?_))))
  · exact continuousOn_const.div (continuous_obsA.continuousOn.sub hW) fun p hp =>
      (sub_neg.2 hp.1).ne
  · exact continuousOn_const.div (continuous_obsC.continuousOn.sub hW) fun p hp =>
      (sub_neg.2 (hp.2.1.trans hp.1)).ne
  · exact continuousOn_const.div (continuous_obsP.continuousOn.sub hW) fun p hp =>
      (sub_pos.2 hp.2.2.1).ne'
  · unfold obsDrift
    refine (continuousOn_finsetSum _ fun i _ => continuousOn_const.div
      (hW.sub (continuous_obsVL i).continuousOn) fun p hp => (sub_pos.2 (hp.2.2.2.1 i)).ne').add
      (continuousOn_finsetSum _ fun j _ => continuousOn_const.div
        (hW.sub (continuous_obsVR j).continuousOn) fun p hp => (sub_neg.2 (hp.2.2.2.2 j)).ne)
  · exact continuousOn_pi.2 fun i => continuousOn_const.div
      ((continuous_obsVL i).continuousOn.sub hW) fun p hp => (sub_neg.2 (hp.2.2.2.1 i)).ne
  · exact continuousOn_pi.2 fun j => continuousOn_const.div
      ((continuous_obsVR j).continuousOn.sub hW) fun p hp => (sub_pos.2 (hp.2.2.2.2 j)).ne'

end Smooth

/-! ### The Itô drift -/

section Gen

variable {κ m : ℝ}

theorem hasDerivAt_log_affine {a b : ℝ} (ha : 0 < a) :
    HasDerivAt (fun t : ℝ => Real.log (a + t * b)) (b / a) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a
  have := h1.log (by simp; exact ha.ne')
  simpa using this

theorem differentiableAt_stripObs {p : ObsE nL nR × ℝ} (hp : p ∈ stripRegion κ) :
    DifferentiableAt ℝ (stripObs κ m) p :=
  ((contDiffOn_stripObs κ m).contDiffAt ((isOpen_stripRegion κ).mem_nhds hp)).differentiableAt
    (by norm_num)

/-- `∂_b Φ = √κ/γ − √κ/α`. -/
theorem partialSnd_stripObs {p : ObsE nL nR × ℝ} (hp : p ∈ stripRegion κ) :
    Ito.partialSnd (stripObs κ m) p =
      Real.sqrt κ / (obsW p κ - obsC p) - Real.sqrt κ / (obsW p κ - obsA p) := by
  obtain ⟨h1, h2, -, -, -⟩ := stripRegion_pos hp
  refine Ito.partialSnd_eq_of_hasDerivAt (differentiableAt_stripObs hp) ?_
  have hlin : ∀ c : ℝ, HasDerivAt (fun y : ℝ => Real.sqrt κ * y + p.1.2.2.2.1 - c) (Real.sqrt κ)
      p.2 := fun c => by
    simpa using (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).add_const p.1.2.2.2.1).sub_const c
  have hC := (hlin (obsC p)).log (by simpa [obsW] using h2.ne')
  have hA := (hlin (obsA p)).log (by simpa [obsW] using h1.ne')
  have h := (hC.sub hA).add_const (m * (Real.log (obsP p - obsC p) - Real.log (obsP p - obsA p)))
  simpa [stripObs, obsW, obsA, obsC, obsP] using h

/-- `∂²_b Φ = κ/α² − κ/γ²`. -/
theorem partialSndSnd_stripObs (hκ : 0 ≤ κ) {p : ObsE nL nR × ℝ} (hp : p ∈ stripRegion κ) :
    Ito.partialSndSnd (stripObs κ m) p =
      κ / (obsW p κ - obsA p) ^ 2 - κ / (obsW p κ - obsC p) ^ 2 := by
  obtain ⟨h1, h2, -, -, -⟩ := stripRegion_pos hp
  have hcd : ContDiffAt ℝ 2 (stripObs κ m) p :=
    ((contDiffOn_stripObs κ m).contDiffAt ((isOpen_stripRegion κ).mem_nhds hp)).of_le (by norm_num)
  set g : ℝ → ℝ := fun y => Real.sqrt κ / (Real.sqrt κ * y + p.1.2.2.2.1 - obsC p) -
    Real.sqrt κ / (Real.sqrt κ * y + p.1.2.2.2.1 - obsA p) with hg
  have hline : ContinuousAt (fun y : ℝ => ((p.1, y) : ObsE nL nR × ℝ)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : ObsE nL nR × ℝ) ∈ stripRegion κ :=
    hline.eventually ((isOpen_stripRegion κ).mem_nhds (by simpa using hp))
  refine Ito.partialSndSnd_eq_of_hasDerivAt hcd (g := g) (hev.mono fun y hy => ?_) ?_
  · rw [partialSnd_stripObs hy]; rfl
  · have hlin : ∀ c : ℝ, HasDerivAt (fun y : ℝ => Real.sqrt κ * y + p.1.2.2.2.1 - c) (Real.sqrt κ)
        p.2 := fun c => by
      simpa using (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).add_const p.1.2.2.2.1).sub_const c
    have hC := ((hlin (obsC p)).inv (by simpa [obsW] using h2.ne')).const_mul (Real.sqrt κ)
    have hA := ((hlin (obsA p)).inv (by simpa [obsW] using h1.ne')).const_mul (Real.sqrt κ)
    have h := hC.sub hA
    have hsq : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
    · simp only [hg, Pi.sub_apply, Pi.inv_apply, div_eq_mul_inv]
    · have e1 : Real.sqrt κ * p.2 + p.1.2.2.2.1 - obsC p = obsW p κ - obsC p := rfl
      have e2 : Real.sqrt κ * p.2 + p.1.2.2.2.1 - obsA p = obsW p κ - obsA p := rfl
      rw [e1, e2]
      field_simp
      rw [Real.sq_sqrt hκ]
      ring

/-- `∂_Λ Φ · v`. -/
theorem partialFst_stripObs {p : ObsE nL nR × ℝ} (hp : p ∈ stripRegion κ) (v : ObsE nL nR) :
    Ito.partialFst (stripObs κ m) p v =
      (v.2.2.2.1 - v.2.1) / (obsW p κ - obsC p) - (v.2.2.2.1 - v.1) / (obsW p κ - obsA p) +
        m * ((v.2.2.1 - v.2.1) / (obsP p - obsC p) - (v.2.2.1 - v.1) / (obsP p - obsA p)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := stripRegion_pos hp
  refine Ito.partialFst_eq_of_hasDerivAt (differentiableAt_stripObs hp) ?_
  have hd := ((hasDerivAt_log_affine (b := v.2.2.2.1 - v.2.1) h2).sub
    (hasDerivAt_log_affine (b := v.2.2.2.1 - v.1) h1)).add
    (((hasDerivAt_log_affine (b := v.2.2.1 - v.2.1) h4).sub
      (hasDerivAt_log_affine (b := v.2.2.1 - v.1) h3)).const_mul m)
  refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, stripObs, obsW, obsA, obsC, obsP, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring_nf

/-- **The Itô drift of `Φ`.** -/
theorem itoGen_stripObs (hκ : 0 ≤ κ) {p : ObsE nL nR × ℝ} (hp : p ∈ stripRegion κ)
    (v : ObsE nL nR) :
    Ito.itoGen (stripObs κ m) p v =
      (v.2.2.2.1 - v.2.1) / (obsW p κ - obsC p) - (v.2.2.2.1 - v.1) / (obsW p κ - obsA p) +
        m * ((v.2.2.1 - v.2.1) / (obsP p - obsC p) - (v.2.2.1 - v.1) / (obsP p - obsA p)) +
        1 / 2 * (κ / (obsW p κ - obsA p) ^ 2 - κ / (obsW p κ - obsC p) ^ 2) := by
  rw [Ito.itoGen, partialFst_stripObs hp, partialSndSnd_stripObs hκ hp]

end Gen

/-! ### The drift is nonpositive -/

section Drift

variable {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The drift of `Φ` is nonpositive** (`κ ≤ 4`), with `m = ½ Σ|ρ^R|`, when the left marks lie in
`(C, A)`, the right marks right of `P`, and the left marks satisfy the Abel bound (RP4). -/
theorem itoGen_stripObs_nonpos (hκ : 0 ≤ κ) (hκ4 : κ ≤ 4) {p : ObsE nL nR × ℝ}
    (hp : p ∈ stripRegion κ) (hL : ∀ i, obsVL p i ≤ obsA p) (hR : ∀ j, obsP p ≤ obsVR p j)
    (hRP4 : ∀ h : 0 < nL,
      (κ / 2 - 2) / (obsW p κ - obsVL p ⟨0, h⟩) ≤ ∑ i, ρL i / (obsW p κ - obsVL p i)) :
    Ito.itoGen (stripObs κ ((∑ j, |ρR j|) / 2)) p (stripField κ ρL ρR p) ≤ 0 := by
  obtain ⟨hα, hγ, -, -, hαγ⟩ := stripRegion_pos hp
  have hπ' : obsW p κ < obsP p := hp.2.2.1
  rw [itoGen_stripObs hκ hp]
  set W := obsW p κ with hWdef
  set A := obsA p
  set C := obsC p
  set P := obsP p
  set m := (∑ j, |ρR j|) / 2 with hmdef
  have hπ : 0 < P - W := by linarith
  set c := κ / 2 - 2 with hcdef
  have hc : c ≤ 0 := by rw [hcdef]; linarith
  set SL := ∑ i, ρL i / (W - obsVL p i) with hSL
  set SR := ∑ j, ρR j / (obsVR p j - W) with hSR
  have hD : obsDrift κ ρL ρR p = SL - SR := by
    simp only [obsDrift, hSL, hSR, ← hWdef]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← div_neg, neg_sub]
  -- the components of the field
  have hf1 : (stripField κ ρL ρR p).1 = 2 / (A - W) := rfl
  have hf2 : (stripField κ ρL ρR p).2.1 = 2 / (C - W) := rfl
  have hf3 : (stripField κ ρL ρR p).2.2.1 = 2 / (P - W) := rfl
  have hf4 : (stripField κ ρL ρR p).2.2.2.1 = SL - SR := hD
  rw [hf1, hf2, hf3, hf4]
  set α := W - A with hαdef
  set γ := W - C with hγdef
  set π' := P - W with hπdef
  have hAW : A - W = -α := by rw [hαdef]; ring
  have hCW : C - W = -γ := by rw [hγdef]; ring
  have hPA : P - A = π' + α := by rw [hπdef, hαdef]; ring
  have hPC : P - C = π' + γ := by rw [hπdef, hγdef]; ring
  rw [hAW, hCW, hPA, hPC]
  set q := 1 / α - 1 / γ with hqdef
  have hq : 0 < q := by
    rw [hqdef, sub_pos]; exact one_div_lt_one_div_of_lt hα hαγ
  -- the identity
  have hid : (SL - SR - 2 / -γ) / γ - (SL - SR - 2 / -α) / α +
      m * ((2 / π' - 2 / -γ) / (π' + γ) - (2 / π' - 2 / -α) / (π' + α)) +
      1 / 2 * (κ / α ^ 2 - κ / γ ^ 2) =
      q * (SR - SL) + c * q * (1 / α + 1 / γ) - 2 * m * q / π' := by
    rw [hqdef, hcdef]
    field_simp
    ring
  rw [hid]
  -- the bounds
  have hSRle : SR ≤ 2 * m / π' := by
    rw [hSR, hmdef, mul_div_cancel₀ _ (two_ne_zero), Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    have hvj : π' ≤ obsVR p j - W := by rw [hπdef]; linarith [hR j]
    have hvj0 : 0 < obsVR p j - W := lt_of_lt_of_le hπ hvj
    calc ρR j / (obsVR p j - W) ≤ |ρR j| / (obsVR p j - W) :=
          div_le_div_of_nonneg_right (le_abs_self _) hvj0.le
      _ ≤ |ρR j| / π' := div_le_div_of_nonneg_left (abs_nonneg _) hπ hvj
  have hSLge : c / α ≤ SL := by
    rcases Nat.eq_zero_or_pos nL with h0 | hpos
    · subst h0
      simp only [hSL, Finset.univ_eq_empty, Finset.sum_empty]
      exact div_nonpos_of_nonpos_of_nonneg hc hα.le
    · refine le_trans ?_ (hRP4 hpos)
      have hv : α ≤ W - obsVL p ⟨0, hpos⟩ := by rw [hαdef]; linarith [hL ⟨0, hpos⟩]
      rw [div_eq_mul_one_div c α, div_eq_mul_one_div c]
      exact mul_le_mul_of_nonpos_left (one_div_le_one_div_of_le hα hv) hc
  have hm0 : 0 ≤ m := by rw [hmdef]; positivity
  have h1 : q * (SR - SL) ≤ q * (2 * m / π' - c / α) :=
    mul_le_mul_of_nonneg_left (by linarith) hq.le
  have h2 : c * q * (1 / α + 1 / γ) = c * q / α + c * q / γ := by ring
  have h3 : c * q / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc hq.le)
    hγ.le
  have h4 : q * (2 * m / π' - c / α) = 2 * m * q / π' - c * q / α := by ring
  linarith

end Drift

end Zhan

end InteractingSLE
