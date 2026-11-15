/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MTildeFrozen
import InteractingSLE.Spec.ZhanGT4.ItoField

/-!
# The log-density of `M̃` with the other curve frozen is a regular log-field; the cut-off generator vanishes

Packet PROVE-ZHAN-GT4-A7. Source: Astra, *Follow-up proofs*, §A.1.1–A.1.3 (`ig1_followup_proofs.txt` L190–L341, R38).

With the frozen data `d : FrzData n` (driver `W` of the growing curve, image chain `W', a`, the frozen map `φ`, the
parameter `κ`, the charges `r_m = ρ_m/κ`, the other source `ζ₀` and the marks `ζ_m` in the `φ`-chart), the logarithm
of `M̃` is `ℓ(t, x) = d.LT t + d.LS t x` (`dualLogTime`, `dualLogSpace` of `MTilde.lean` at the factors of
`MTildeFrozen.lean`, with `x` the position of the driver). On a box (`OwnData` box hypotheses of PROVE-ZHAN-GT4-A4)
where the conformal factors do not degenerate, `ℓ` is a regular log-field (`IsLogField`), and the generator of the
cut-off field vanishes at the driver (`cutField_gen_eq_zero`) — the drift identity of §A.1.2 for the field that enters
Itô's formula.

## Main results

* `FrzData`, `FrzData.F` (`Re F_t^{(k)}(x)`), `FrzData.LT`, `FrzData.LS`, `FrzData.LSX`, `FrzData.LSXX`, `FrzData.LSXXX`,
  `FrzData.LST`, `FrzData.LTT`, `FrzData.ell`, `FrzData.ellT`;
* `ContinuousOn.dualLogSpace` and the other continuity lemmas for the formal derivatives;
* **`FrzData.isLogField`**: `ℓ` is a regular log-field on the box (given nondegeneracy and a bound `K`);
* **`FrzData.cutField_gen_eq_zero`**: `∂_t Φ + (κ/2) ∂²_x Φ = 0` at `x = W_t` for the cut-off field `Φ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

/-! ### Continuity of the formal derivatives -/

section Cont

variable {X : Type*} [TopologicalSpace X] {s : Set X} {κ : ℝ} {n : ℕ} {r : Fin n → ℝ}
  {f f1 f2 f3 f4 A0 : X → ℝ} {B0 : X → Fin n → ℝ}

theorem continuousOn_pairSum {g : X → Fin n → Fin n → ℝ} (hg : ∀ m k, ContinuousOn (fun p => g p m k) s) :
    ContinuousOn (fun p => pairSum (g p)) s := by
  unfold pairSum
  exact continuousOn_finsetSum _ fun q _ => hg q.1 q.2

theorem continuousOn_dualLogSpace (hf : ContinuousOn f s) (hf1 : ContinuousOn f1 s) (hA0 : ContinuousOn A0 s)
    (hB0 : ∀ m, ContinuousOn (fun p => B0 p m) s) (h1 : ∀ p ∈ s, f1 p ≠ 0) (h0 : ∀ p ∈ s, f p - A0 p ≠ 0)
    (hm : ∀ p ∈ s, ∀ m, f p - B0 p m ≠ 0) :
    ContinuousOn (fun p => dualLogSpace κ r (f p) (f1 p) (A0 p) (B0 p)) s := by
  unfold dualLogSpace
  exact ((continuousOn_const.mul (hf1.log h1)).sub (continuousOn_const.mul ((hf.sub hA0).log h0))).add
    (continuousOn_finsetSum _ fun m _ => continuousOn_const.mul ((hf.sub (hB0 m)).log fun p hp => hm p hp m))

theorem continuousOn_dualLogSpaceX (hf : ContinuousOn f s) (hf1 : ContinuousOn f1 s) (hf2 : ContinuousOn f2 s)
    (hA0 : ContinuousOn A0 s) (hB0 : ∀ m, ContinuousOn (fun p => B0 p m) s) (h1 : ∀ p ∈ s, f1 p ≠ 0)
    (h0 : ∀ p ∈ s, f p - A0 p ≠ 0) (hm : ∀ p ∈ s, ∀ m, f p - B0 p m ≠ 0) :
    ContinuousOn (fun p => dualLogSpaceX κ r (f p) (f1 p) (f2 p) (A0 p) (B0 p)) s := by
  unfold dualLogSpaceX
  exact ((continuousOn_const.mul (hf2.div hf1 h1)).sub (continuousOn_const.mul (hf1.div (hf.sub hA0) h0))).add
    (continuousOn_finsetSum _ fun m _ => continuousOn_const.mul (hf1.div (hf.sub (hB0 m)) fun p hp => hm p hp m))

theorem continuousOn_dualLogSpaceXX (hf : ContinuousOn f s) (hf1 : ContinuousOn f1 s) (hf2 : ContinuousOn f2 s)
    (hf3 : ContinuousOn f3 s) (hA0 : ContinuousOn A0 s) (hB0 : ∀ m, ContinuousOn (fun p => B0 p m) s)
    (h1 : ∀ p ∈ s, f1 p ≠ 0) (h0 : ∀ p ∈ s, f p - A0 p ≠ 0) (hm : ∀ p ∈ s, ∀ m, f p - B0 p m ≠ 0) :
    ContinuousOn (fun p => dualLogSpaceXX κ r (f p) (f1 p) (f2 p) (f3 p) (A0 p) (B0 p)) s := by
  unfold dualLogSpaceXX
  have hd : ∀ (g : X → ℝ), ContinuousOn g s → (∀ p ∈ s, g p ≠ 0) →
      ContinuousOn (fun p => f2 p / g p - (f1 p / g p) ^ 2) s := fun g hg hg0 =>
    (hf2.div hg hg0).sub ((hf1.div hg hg0).pow 2)
  exact ((continuousOn_const.mul ((hf3.div hf1 h1).sub ((hf2.div hf1 h1).pow 2))).sub
    (continuousOn_const.mul (hd _ (hf.sub hA0) h0))).add
    (continuousOn_finsetSum _ fun m _ => continuousOn_const.mul (hd _ (hf.sub (hB0 m)) fun p hp => hm p hp m))

theorem continuousOn_dualLogSpaceT {df df1 dA0 : X → ℝ} {dB0 : X → Fin n → ℝ} (hf : ContinuousOn f s)
    (hf1 : ContinuousOn f1 s) (hA0 : ContinuousOn A0 s) (hB0 : ∀ m, ContinuousOn (fun p => B0 p m) s)
    (hdf : ContinuousOn df s) (hdf1 : ContinuousOn df1 s) (hdA0 : ContinuousOn dA0 s)
    (hdB0 : ∀ m, ContinuousOn (fun p => dB0 p m) s) (h1 : ∀ p ∈ s, f1 p ≠ 0) (h0 : ∀ p ∈ s, f p - A0 p ≠ 0)
    (hm : ∀ p ∈ s, ∀ m, f p - B0 p m ≠ 0) :
    ContinuousOn (fun p => dualLogSpaceT κ r (f p) (f1 p) (A0 p) (B0 p) (df p) (df1 p) (dA0 p) (dB0 p)) s := by
  unfold dualLogSpaceT
  exact ((continuousOn_const.mul (hdf1.div hf1 h1)).sub
    (continuousOn_const.mul ((hdf.sub hdA0).div (hf.sub hA0) h0))).add
    (continuousOn_finsetSum _ fun m _ => continuousOn_const.mul (((hdf.sub (hdB0 m)).div (hf.sub (hB0 m))
      fun p hp => hm p hp m)))

theorem continuousOn_dualLogTime {A21 L A20 : X → ℝ} {B1 : X → Fin n → ℝ} (h21 : ContinuousOn A21 s)
    (hL : ContinuousOn L s) (h20 : ContinuousOn A20 s) (hB0 : ∀ m, ContinuousOn (fun p => B0 p m) s)
    (hB1 : ∀ m, ContinuousOn (fun p => B1 p m) s) (h21z : ∀ p ∈ s, A21 p ≠ 0) (hB1z : ∀ p ∈ s, ∀ m, B1 p m ≠ 0)
    (h2m : ∀ p ∈ s, ∀ m, A20 p - B0 p m ≠ 0) (hmn : ∀ p ∈ s, ∀ m k, m ≠ k → B0 p m - B0 p k ≠ 0) :
    ContinuousOn (fun p => dualLogTime κ r (A21 p) (L p) (A20 p) (B0 p) (B1 p)) s := by
  unfold dualLogTime
  refine (((continuousOn_const.mul (h21.log h21z)).sub (continuousOn_const.mul hL)).add
    (continuousOn_finsetSum _ fun m _ => (continuousOn_const.mul ((hB1 m).log fun p hp => hB1z p hp m)).add
      (continuousOn_const.mul ((h20.sub (hB0 m)).log fun p hp => h2m p hp m)))).add ?_
  unfold pairSum
  refine continuousOn_finsetSum _ fun q hq => continuousOn_const.mul (((hB0 q.1).sub (hB0 q.2)).log
    fun p hp => hmn p hp _ _ (Finset.mem_filter.1 hq).2.ne)

theorem continuousOn_dualLogTimeT {A21 A20 dA21 dL dA20 : X → ℝ} {B1 dB0 dB1 : X → Fin n → ℝ}
    (h21 : ContinuousOn A21 s) (h20 : ContinuousOn A20 s) (hB0 : ∀ m, ContinuousOn (fun p => B0 p m) s)
    (hB1 : ∀ m, ContinuousOn (fun p => B1 p m) s) (hd21 : ContinuousOn dA21 s) (hdL : ContinuousOn dL s)
    (hd20 : ContinuousOn dA20 s) (hdB0 : ∀ m, ContinuousOn (fun p => dB0 p m) s)
    (hdB1 : ∀ m, ContinuousOn (fun p => dB1 p m) s) (h21z : ∀ p ∈ s, A21 p ≠ 0)
    (hB1z : ∀ p ∈ s, ∀ m, B1 p m ≠ 0) (h2m : ∀ p ∈ s, ∀ m, A20 p - B0 p m ≠ 0)
    (hmn : ∀ p ∈ s, ∀ m k, m ≠ k → B0 p m - B0 p k ≠ 0) :
    ContinuousOn (fun p => dualLogTimeT κ r (A21 p) (A20 p) (B0 p) (B1 p) (dA21 p) (dL p) (dA20 p) (dB0 p)
      (dB1 p)) s := by
  unfold dualLogTimeT
  refine (((continuousOn_const.mul (hd21.div h21 h21z)).sub (continuousOn_const.mul hdL)).add
    (continuousOn_finsetSum _ fun m _ => (continuousOn_const.mul ((hdB1 m).div (hB1 m) fun p hp => hB1z p hp m)).add
      (continuousOn_const.mul ((hd20.sub (hdB0 m)).div (h20.sub (hB0 m)) fun p hp => h2m p hp m)))).add ?_
  unfold pairSum
  refine continuousOn_finsetSum _ fun q hq => continuousOn_const.mul ((((hdB0 q.1).sub (hdB0 q.2)).div
    ((hB0 q.1).sub (hB0 q.2))) fun p hp => hmn p hp _ _ (Finset.mem_filter.1 hq).2.ne)

end Cont

/-! ### The frozen data and the log-density -/

/-- **The frozen data of the one-curve step**: the growing driver `W`, the image chain `W', a`, the frozen map `φ`,
the parameter `κ`, the reduced charges `r_m = ρ_m/κ`, the other source `ζ₀` and the marks `ζ_m` (`φ`-chart). -/
structure FrzData (n : ℕ) where
  W : ℝ → ℝ
  W' : ℝ → ℝ
  a : ℝ → ℝ
  φ : ℂ → ℂ
  κ : ℝ
  r : Fin n → ℝ
  ζ₀ : ℝ
  ζ : Fin n → ℝ

namespace FrzData

variable {n : ℕ} (d : FrzData n)

/-- `Re F_t^{(k)}(x)`, `F_t = ownExt … t` (the reflected `h_j`), at a real point `x`. -/
def F (k : ℕ) (t x : ℝ) : ℝ := (deriv^[k] (ownExt d.W d.W' d.a d.φ t) x).re

/-- `A_{j,k}(t)`. -/
def A (k : ℕ) (t : ℝ) : ℝ := frzA d.W d.W' d.a d.φ k t

/-- `A_{k,0}(t)`. -/
def A20 (t : ℝ) : ℝ := frzImg d.W' d.a d.ζ₀ t

/-- `A_{k,1}(t)`. -/
def A21 (t : ℝ) : ℝ := frzImgD d.W' d.a d.ζ₀ t

/-- `B_{m,0}(t)`. -/
def B0 (t : ℝ) : Fin n → ℝ := fun m => frzImg d.W' d.a (d.ζ m) t

/-- `B_{m,1}(t)/φ'(p_m)`. -/
def B1 (t : ℝ) : Fin n → ℝ := fun m => frzImgD d.W' d.a (d.ζ m) t

/-- `∂_t A_{k,0}` ((D3)). -/
def dA20 (t : ℝ) : ℝ := 2 * d.A 1 t ^ 2 / (d.A20 t - d.A 0 t)

/-- `∂_t B_{m,0}` ((D3)). -/
def dB0 (t : ℝ) : Fin n → ℝ := fun m => 2 * d.A 1 t ^ 2 / (d.B0 t m - d.A 0 t)

/-- `∂_t A_{k,1}` ((D3)). -/
def dA21 (t : ℝ) : ℝ := -2 * d.A 1 t ^ 2 * d.A21 t / (d.A20 t - d.A 0 t) ^ 2

/-- `∂_t B_{m,1}` ((D3)). -/
def dB1 (t : ℝ) : Fin n → ℝ := fun m => -2 * d.A 1 t ^ 2 * d.B1 t m / (d.B0 t m - d.A 0 t) ^ 2

/-- The time part of `log M̃`. -/
def LT (t : ℝ) : ℝ := dualLogTime d.κ d.r (d.A21 t) (frzLogF d.W d.W' d.a d.φ t) (d.A20 t) (d.B0 t) (d.B1 t)

/-- Its time derivative. -/
def LTT (t : ℝ) : ℝ :=
  dualLogTimeT d.κ d.r (d.A21 t) (d.A20 t) (d.B0 t) (d.B1 t) (d.dA21 t) (frzRate d.W d.W' d.a d.φ t) (d.dA20 t)
    (d.dB0 t) (d.dB1 t)

/-- The space part of `log M̃` at the position `x` of the driver. -/
def LS (t x : ℝ) : ℝ := dualLogSpace d.κ d.r (d.F 0 t x) (d.F 1 t x) (d.A20 t) (d.B0 t)

def LSX (t x : ℝ) : ℝ := dualLogSpaceX d.κ d.r (d.F 0 t x) (d.F 1 t x) (d.F 2 t x) (d.A20 t) (d.B0 t)

def LSXX (t x : ℝ) : ℝ :=
  dualLogSpaceXX d.κ d.r (d.F 0 t x) (d.F 1 t x) (d.F 2 t x) (d.F 3 t x) (d.A20 t) (d.B0 t)

def LSXXX (t x : ℝ) : ℝ :=
  dualLogSpaceXXX d.κ d.r (d.F 0 t x) (d.F 1 t x) (d.F 2 t x) (d.F 3 t x) (d.F 4 t x) (d.A20 t) (d.B0 t)

/-- The time derivative of the space part at a fixed `x` ((D1)). -/
def LST (t x : ℝ) : ℝ :=
  dualLogSpaceT d.κ d.r (d.F 0 t x) (d.F 1 t x) (d.A20 t) (d.B0 t)
    ((dHat (ownExt d.W d.W' d.a d.φ t) (d.W t) x).re) ((deriv (dHat (ownExt d.W d.W' d.a d.φ t) (d.W t)) x).re)
    (d.dA20 t) (d.dB0 t)

/-- **`log M̃(t)` at driver position `x`**: `ℓ(t, x)`. -/
def ell (t x : ℝ) : ℝ := d.LT t + d.LS t x

/-- `∂_t ℓ(t, x)`. -/
def ellT (t x : ℝ) : ℝ := d.LTT t + d.LST t x

end FrzData

/-! ### The time part -/

namespace FrzData

variable {n : ℕ} (d : FrzData n) {A : Set ℂ} {T : ℝ} (h : OwnData d.W A d.φ T d.a d.W')
  {v₀ : ℝ → ℂ} (hv₀ : IsForwardSol d.W' d.ζ₀ (d.a T) v₀) {v : Fin n → ℝ → ℂ}
  (hv : ∀ m, IsForwardSol d.W' (d.ζ m) (d.a T) (v m)) (hζ₀ : ∀ m, d.ζ m ≠ d.ζ₀) (hζ : Function.Injective d.ζ)

section Time

include h hv₀ hv hζ₀ hζ

/-- The nondegeneracy of the time factors on `[0, T]`. -/
theorem time_ne {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    d.A 1 t ≠ 0 ∧ d.A21 t ≠ 0 ∧ (∀ m, d.B1 t m ≠ 0) ∧ d.A20 t - d.A 0 t ≠ 0 ∧ (∀ m, d.B0 t m - d.A 0 t ≠ 0) ∧
      (∀ m, d.A20 t - d.B0 t m ≠ 0) ∧ (∀ m k, m ≠ k → d.B0 t m - d.B0 t k ≠ 0) :=
  ⟨(h.frzA_one_pos ht).ne', (deriv_fwdMap_real h.contW' hv₀ (h.mapsTo_clock ht)).2.ne',
    fun m => (deriv_fwdMap_real h.contW' (hv m) (h.mapsTo_clock ht)).2.ne', h.frzImg_sub_ne_zero hv₀ ht,
    fun m => h.frzImg_sub_ne_zero (hv m) ht, fun m => h.frzImg_sub_frzImg_ne_zero hv₀ (hv m) (hζ₀ m).symm ht,
    fun m k hmk => h.frzImg_sub_frzImg_ne_zero (hv m) (hv k) (hζ.ne hmk) ht⟩

theorem hasDerivWithinAt_LT {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt d.LT (d.LTT t) (Icc 0 T) t := by
  obtain ⟨-, h21, hB1, -, -, h2m, hmn⟩ := d.time_ne h hv₀ hv hζ₀ hζ ht
  exact hasDerivWithinAt_dualLogTime (A21 := d.A21) (L := frzLogF d.W d.W' d.a d.φ) (A20 := d.A20)
    (B0 := d.B0) (B1 := d.B1) (h.hasDerivWithinAt_frzImgD hv₀ ht) (h.hasDerivWithinAt_frzLogF ht)
    (h.hasDerivWithinAt_frzImg hv₀ ht) (fun m => h.hasDerivWithinAt_frzImg (hv m) ht)
    (fun m => h.hasDerivWithinAt_frzImgD (hv m) ht) h21 hB1 h2m hmn

theorem continuousOn_LT : ContinuousOn d.LT (Icc 0 T) := fun _t ht =>
  (d.hasDerivWithinAt_LT h hv₀ hv hζ₀ hζ ht).continuousWithinAt

omit hv hζ₀ hζ in
theorem continuousOn_A20 : ContinuousOn d.A20 (Icc 0 T) := fun _t ht =>
  (h.hasDerivWithinAt_frzImg hv₀ ht).continuousWithinAt

omit hv hζ₀ hζ in
theorem continuousOn_A21 : ContinuousOn d.A21 (Icc 0 T) := fun _t ht =>
  (h.hasDerivWithinAt_frzImgD hv₀ ht).continuousWithinAt

omit hv₀ hζ₀ hζ in
theorem continuousOn_B0 (m : Fin n) : ContinuousOn (fun t => d.B0 t m) (Icc 0 T) := fun _t ht =>
  (h.hasDerivWithinAt_frzImg (hv m) ht).continuousWithinAt

omit hv₀ hζ₀ hζ in
theorem continuousOn_B1 (m : Fin n) : ContinuousOn (fun t => d.B1 t m) (Icc 0 T) := fun _t ht =>
  (h.hasDerivWithinAt_frzImgD (hv m) ht).continuousWithinAt

theorem continuousOn_dA20 : ContinuousOn d.dA20 (Icc 0 T) :=
  (continuousOn_const.mul ((h.continuousOn_frzA 1).pow 2)).div
    ((d.continuousOn_A20 h hv₀).sub (h.continuousOn_frzA 0)) fun _t ht => (d.time_ne h hv₀ hv hζ₀ hζ ht).2.2.2.1

theorem continuousOn_dB0 (m : Fin n) : ContinuousOn (fun t => d.dB0 t m) (Icc 0 T) :=
  (continuousOn_const.mul ((h.continuousOn_frzA 1).pow 2)).div
    ((d.continuousOn_B0 h hv m).sub (h.continuousOn_frzA 0)) fun _t ht =>
      (d.time_ne h hv₀ hv hζ₀ hζ ht).2.2.2.2.1 m

theorem continuousOn_LTT : ContinuousOn d.LTT (Icc 0 T) := by
  have hA1 := h.continuousOn_frzA 1
  have hA0 := h.continuousOn_frzA 0
  have h20 := d.continuousOn_A20 h hv₀
  have h21 := d.continuousOn_A21 h hv₀
  have hd21 : ContinuousOn d.dA21 (Icc 0 T) :=
    ((continuousOn_const.mul (hA1.pow 2)).mul h21).div ((h20.sub hA0).pow 2) fun t ht =>
      pow_ne_zero 2 (d.time_ne h hv₀ hv hζ₀ hζ ht).2.2.2.1
  have hdB1 : ∀ m, ContinuousOn (fun t => d.dB1 t m) (Icc 0 T) := fun m =>
    ((continuousOn_const.mul (hA1.pow 2)).mul (d.continuousOn_B1 h hv m)).div
      (((d.continuousOn_B0 h hv m).sub hA0).pow 2) fun t ht =>
        pow_ne_zero 2 ((d.time_ne h hv₀ hv hζ₀ hζ ht).2.2.2.2.1 m)
  exact continuousOn_dualLogTimeT (A21 := d.A21) (A20 := d.A20) (B0 := d.B0) (B1 := d.B1) (dA21 := d.dA21)
    (dL := frzRate d.W d.W' d.a d.φ) (dA20 := d.dA20) (dB0 := d.dB0) (dB1 := d.dB1) h21 h20
    (d.continuousOn_B0 h hv) (d.continuousOn_B1 h hv) hd21 h.continuousOn_frzRate
    (d.continuousOn_dA20 h hv₀ hv hζ₀ hζ) (d.continuousOn_dB0 h hv₀ hv hζ₀ hζ) hdB1
    (fun t ht => (d.time_ne h hv₀ hv hζ₀ hζ ht).2.1) (fun t ht => (d.time_ne h hv₀ hv hζ₀ hζ ht).2.2.1)
    (fun t ht => (d.time_ne h hv₀ hv hζ₀ hζ ht).2.2.2.2.2.1)
    (fun t ht => (d.time_ne h hv₀ hv hζ₀ hζ ht).2.2.2.2.2.2)

end Time

end FrzData

/-! ### The space part on a box: `ℓ` is a regular log-field -/

namespace FrzData

variable {n : ℕ} (d : FrzData n) {A : Set ℂ} {T : ℝ} (h : OwnData d.W A d.φ T d.a d.W')
  {v₀ : ℝ → ℂ} (hv₀ : IsForwardSol d.W' d.ζ₀ (d.a T) v₀) {v : Fin n → ℝ → ℂ}
  (hv : ∀ m, IsForwardSol d.W' (d.ζ m) (d.a T) (v m)) (hζ₀ : ∀ m, d.ζ m ≠ d.ζ₀) (hζ : Function.Injective d.ζ)
  {b c y rb : ℝ} (hJ : Icc b c ⊆ Icc 0 T)
  (hdisj : ∀ t ∈ Icc b c, Disjoint (ball (y : ℂ) (2 * rb)) ((fun z => fwdMap d.W t z + d.W t) '' A))
  (hWm : ∀ t ∈ Icc b c, (d.W t : ℂ) ∈ ball (y : ℂ) rb)
  (hq0 : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) rb, dslope (ownExt d.W d.W' d.a d.φ t) (d.W t) z ≠ 0)
  {ρ : ℝ} (h3 : 3 * ρ ≤ rb)
  (hnd : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * ρ →
    d.F 1 t x ≠ 0 ∧ d.F 0 t x - d.A20 t ≠ 0 ∧ ∀ m, d.F 0 t x - d.B0 t m ≠ 0)

omit d in
theorem mem_ball_of_near {y rb ρ : ℝ} (h3 : 3 * ρ ≤ rb) {x : ℝ} (hx : |x - y| < 3 * ρ) :
    (x : ℂ) ∈ ball (y : ℂ) rb := by
  rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  linarith

include h hJ hdisj in
/-- On a box the iterated derivatives of `F_t` are holomorphic and jointly continuous. -/
theorem box_iterDeriv (k : ℕ) :
    (∀ s ∈ Icc b c, DifferentiableOn ℂ (deriv^[k] (ownExt d.W d.W' d.a d.φ s)) (ball (y : ℂ) rb)) ∧
      ContinuousOn (fun q : ℝ × ℂ => deriv^[k] (ownExt d.W d.W' d.a d.φ q.1) q.2) (Icc b c ×ˢ ball (y : ℂ) rb) := by
  induction k with
  | zero => exact ⟨fun s hs => (h.box_props hJ hdisj hs).1, h.continuousOn_box hJ hdisj⟩
  | succ j ih =>
    refine ⟨fun s hs => ?_, ?_⟩
    · rw [Function.iterate_succ_apply']
      exact (ih.1 s hs).deriv isOpen_ball
    · have := continuousOn_deriv_of_holo (F := fun s => deriv^[j] (ownExt d.W d.W' d.a d.φ s)) ih.1 ih.2
      simpa only [Function.iterate_succ_apply'] using this

/-- The embedding of the real region into the box. -/
theorem mapsTo_region (h3 : 3 * ρ ≤ rb) : MapsTo (fun p : ℝ × ℝ => (p.1, (p.2 : ℂ)))
    (Icc b c ×ˢ {x | |x - y| < 3 * ρ}) (Icc b c ×ˢ ball (y : ℂ) rb) :=
  fun _p hp => ⟨hp.1, mem_ball_of_near h3 hp.2⟩

theorem continuous_region : Continuous fun p : ℝ × ℝ => (p.1, (p.2 : ℂ)) :=
  continuous_fst.prodMk (Complex.continuous_ofReal.comp continuous_snd)

include h hJ hdisj h3 in
theorem continuousOn_F (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => d.F k p.1 p.2) (Icc b c ×ˢ {x | |x - y| < 3 * ρ}) := by
  have := (d.box_iterDeriv h hJ hdisj k).2.comp continuous_region.continuousOn (mapsTo_region h3)
  exact continuous_re.comp_continuousOn this

include h hv₀ hv hζ₀ hζ hJ hdisj hWm hq0 h3 hnd in
/-- **`log M̃` is a regular log-field on the box** (given nondegeneracy of the space factors on the region and a
bound `K` for the log-field and its derivatives). -/
theorem isLogField {K : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Icc b c, ∀ x, |x - y| < 3 * ρ → |d.ell t x| ≤ K ∧ |d.LSX t x| ≤ K ∧ |d.LSXX t x| ≤ K ∧
      |d.LSXXX t x| ≤ K ∧ |d.ellT t x| ≤ K) :
    IsLogField d.ell d.LSX d.LSXX d.LSXXX d.ellT b c y ρ K := by
  have hF : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * ρ → ∀ k, HasDerivAt (d.F k t) (d.F (k + 1) t x) x :=
    fun t ht x hx k => h.hasDerivAt_re_iterDeriv_box hJ hdisj ht (mem_ball_of_near h3 hx) k
  set R := Icc b c ×ˢ {x : ℝ | |x - y| < 3 * ρ} with hR
  have hfst : MapsTo Prod.fst R (Icc 0 T) := fun _p hp => hJ hp.1
  have cF := fun k => d.continuousOn_F h hJ hdisj h3 k
  have c20 : ContinuousOn (fun p : ℝ × ℝ => d.A20 p.1) R :=
    (d.continuousOn_A20 h hv₀).comp continuousOn_fst hfst
  have cB0 : ∀ m, ContinuousOn (fun p : ℝ × ℝ => d.B0 p.1 m) R := fun m =>
    (d.continuousOn_B0 h hv m).comp continuousOn_fst hfst
  have n1 : ∀ p ∈ R, d.F 1 p.1 p.2 ≠ 0 := fun p hp => (hnd p.1 hp.1 p.2 hp.2).1
  have n0 : ∀ p ∈ R, d.F 0 p.1 p.2 - d.A20 p.1 ≠ 0 := fun p hp => (hnd p.1 hp.1 p.2 hp.2).2.1
  have nm : ∀ p ∈ R, ∀ m, d.F 0 p.1 p.2 - d.B0 p.1 m ≠ 0 := fun p hp => (hnd p.1 hp.1 p.2 hp.2).2.2
  refine ⟨hρ, hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb⟩
  · intro t ht x hx
    obtain ⟨h1, h0, hm⟩ := hnd t ht x hx
    exact (hasDerivAt_dualLogSpace (hF t ht x hx 0) (hF t ht x hx 1) h1 h0 hm).const_add (d.LT t)
  · intro t ht x hx
    obtain ⟨h1, h0, hm⟩ := hnd t ht x hx
    exact hasDerivAt_dualLogSpaceX (hF t ht x hx 0) (hF t ht x hx 1) (hF t ht x hx 2) h1 h0 hm
  · intro t ht x hx
    obtain ⟨h1, h0, hm⟩ := hnd t ht x hx
    exact hasDerivAt_dualLogSpaceXX (hF t ht x hx 0) (hF t ht x hx 1) (hF t ht x hx 2) (hF t ht x hx 3) h1 h0 hm
  · intro t ht x hx
    obtain ⟨h1, h0, hm⟩ := hnd t ht x hx
    have hxb := mem_ball_of_near h3 hx
    have hLT := (d.hasDerivWithinAt_LT h hv₀ hv hζ₀ hζ (hJ ht)).mono hJ
    have hLS := hasDerivWithinAt_dualLogSpace_time (κ := d.κ) (r := d.r) (J := Icc b c)
      (f := fun s => d.F 0 s x) (f1 := fun s => d.F 1 s x) (A0 := d.A20) (B0 := d.B0)
      (h.hasDerivWithinAt_re_ownExt_box hJ hdisj hWm hq0 ht hxb)
      (h.hasDerivWithinAt_re_deriv_ownExt_box hJ hdisj hWm hq0 ht hxb)
      ((h.hasDerivWithinAt_frzImg hv₀ (hJ ht)).mono hJ) (fun m => (h.hasDerivWithinAt_frzImg (hv m) (hJ ht)).mono hJ)
      h1 h0 hm
    exact hLT.add hLS
  · exact ((d.continuousOn_LT h hv₀ hv hζ₀ hζ).comp continuousOn_fst hfst).add
      (continuousOn_dualLogSpace (cF 0) (cF 1) c20 cB0 n1 n0 nm)
  · exact continuousOn_dualLogSpaceX (cF 0) (cF 1) (cF 2) c20 cB0 n1 n0 nm
  · exact continuousOn_dualLogSpaceXX (cF 0) (cF 1) (cF 2) (cF 3) c20 cB0 n1 n0 nm
  · have hdf0 := (h.continuousOn_dHat_box hJ hdisj hWm hq0).comp continuous_region.continuousOn
      (mapsTo_region (b := b) (c := c) (y := y) h3)
    have hdf := continuous_re.comp_continuousOn hdf0
    have hdf10 := (h.continuousOn_deriv_dHat_box hJ hdisj hWm hq0).comp continuous_region.continuousOn
      (mapsTo_region (b := b) (c := c) (y := y) h3)
    have hdf1 := continuous_re.comp_continuousOn hdf10
    simp only [Function.comp_def] at hdf hdf1
    exact ((d.continuousOn_LTT h hv₀ hv hζ₀ hζ).comp continuousOn_fst hfst).add
      (continuousOn_dualLogSpaceT (cF 0) (cF 1) c20 cB0 hdf hdf1
        ((d.continuousOn_dA20 h hv₀ hv hζ₀ hζ).comp continuousOn_fst hfst)
        (fun m => (d.continuousOn_dB0 h hv₀ hv hζ₀ hζ m).comp continuousOn_fst hfst) n1 n0 nm)

include h hv₀ hv hζ₀ hζ hJ hdisj hWm hq0 in
/-- **The generator of the cut-off field vanishes at the driver** (§A.1.2): if `|W_t − y| < ρ`, then
`∂_t Φ + (κ/2) ∂²_x Φ = 0` at `x = W_t` for `Φ = χ((x − y)/ρ) e^{ℓ(t, x)}`. -/
theorem cutField_gen_eq_zero (hκ : d.κ ≠ 0) (hρ : 0 < ρ) {t : ℝ} (ht : t ∈ Icc b c)
    (hWy : |d.W t - y| < ρ) :
    cutFieldT d.ell d.ellT y ρ t (d.W t) + d.κ / 2 * cutField2 d.ell d.LSX d.LSXX y ρ t (d.W t) = 0 := by
  have hg := h.frzGen_eq_zero hJ hdisj hWm hq0 hκ d.r hv₀ hv hζ₀ hζ ht
  have key : d.ellT t (d.W t) + d.κ / 2 * (d.LSXX t (d.W t) + d.LSX t (d.W t) ^ 2) = 0 := by
    simp only [FrzData.ellT, FrzData.LTT, FrzData.LST, FrzData.LSXX, FrzData.LSX, FrzData.A, FrzData.A20,
      FrzData.A21, FrzData.dA20, FrzData.dA21, FrzData.F]
    exact hg
  have e0 := cutChi_zero_eq_one hρ hWy
  have e1 := cutChi_succ_eq_zero hρ hWy (k := 1) one_pos
  have e2 := cutChi_succ_eq_zero hρ hWy (k := 2) two_pos
  have hexp : cutFieldT d.ell d.ellT y ρ t (d.W t) + d.κ / 2 * cutField2 d.ell d.LSX d.LSXX y ρ t (d.W t) =
      Real.exp (d.ell t (d.W t)) * (d.ellT t (d.W t) + d.κ / 2 * (d.LSXX t (d.W t) + d.LSX t (d.W t) ^ 2)) := by
    simp only [cutFieldT, cutField2, cutExp2, e0, e1, e2]
    ring
  rw [hexp, key, mul_zero]

end FrzData

end InteractingSLE.ZhanGT4
