/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalIdent
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalLevels

/-!
# The staged cross-conditioning law: the image stage word and the staged mean identification

Packet PROVE-CROSSCOND-STAGED4 (S2). For a staged prefix (one simple trace `α` of the concatenated driver `Wα`, pieces
`j = 0, …, ℓ` starting at the switch times `S j`, angles `θ_j`, `θ_0 = 0`) and the counterflow of CROSSCOND-THETA, the
union mean of `A_t ∪ G_s` read in the joint chart `f′_T ∘ Ψ` is the bounded harmonic extension of the **image stage
word** minus `θ_ℓ χ`:

* `imgStageRhoL`, `imgStageVL` (and right): the image stage word — the marks born at the switches in the image chart,
  `chartAL (shiftDrive W′ (A m)) (T − A m)` (`A m` the image time of the switch point `α (S m)`) with the switch weights
  `−(θ_m − θ_{m−1}) χ/λ` (right: `+(θ_m − θ_{m−1}) χ/λ`), followed by the root image word of CROSSCOND-THETA (the
  images of the root marks and the junction mark, weights `imgRhoLT ρL θ κ`);
* **`eqOn_imgChart_stage`**: the per-sample identification: if the flow-side word `c` (the stage word in the prefix
  chart) has the side heights `∓λ − θ_j χ` between the base images of the shifted chain (`IsLeftLevels`,
  `IsRightLevels`, as `isLeftLevels_pastWord` and `levLs_eq_chartAL` give for the iterated stop word), the flow side's
  own mean is `c.mean ∘ f_t − χ arg f_t′` near the prefix (`hFl`) and the counterflow side is CROSSCOND-THETA's, then
  `w + 𝔥₀ = u ∘ f′_T ∘ Ψ − θ_ℓ χ − χ (arg f′_T′ ∘ Ψ + arg Ψ′)` on `ℍ ∖ (A ∪ G)`, `u` the bounded harmonic extension of
  the image stage word.

The slit data match piece by piece: a slit point `x` lies between the image born marks of switches `j` and `j + 1` iff
its flow-chart preimage `x₁` lies between the flow born marks (`StagedLaw.mem_Ioo_chartA_iff_of_imgTheta`), where the
flow data are `−λ − θ_j χ` (levels) and the image data are `−λ (1 + Σ_{m > j} w_m) − θ_ℓ χ = −λ − θ_j χ` (telescoping);
off the slit every born mark lies on one side, so the image data are the root image data plus `−λ Σ_m w_m − θ_ℓ χ = 0`.
Deterministic; R48: no Theorem 1.2/1.3 input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.RS (shiftDrive)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped Real

namespace InteractingSLE.Sec5.CrossCond.StagedFinal

open WangWu hiding ratPt exists_ratPt_dist_lt
open GlueImg Theta Cond44Ref Word49 Sec7.StripSysField StagedLaw
open MartChar.RealFlow Restart.RetAux79 Restart

/-! ### Elementary helpers -/

section Helpers

/-- A bounded harmonic extension minus a constant extends the data minus the constant. -/
theorem IsBoundedHarmonicExtension.sub_const {b : ℝ → ℝ} {J : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension b J u) (c : ℝ) :
    IsBoundedHarmonicExtension (fun x => b x - c) J (fun z => u z - c) := by
  obtain ⟨hh, ⟨M, hM⟩, hlim⟩ := hu
  refine ⟨fun z hz => (hh z hz).sub (InnerProductSpace.harmonicAt_const c), ⟨M + |c|, fun z hz => ?_⟩,
    fun x hx => (hlim x hx).sub_const c⟩
  exact (abs_sub _ _).trans (by linarith [hM z hz])

/-- **Telescoping of the switch weights**: `Σ_{j ≤ i < ℓ} (θ (i + 1) − θ i) = θ ℓ − θ j`. -/
theorem sum_switch_telescope (θ : ℕ → ℝ) : ∀ (ℓ j : ℕ), j ≤ ℓ →
    (∑ i ∈ Finset.range ℓ, if j ≤ i then θ (i + 1) - θ i else 0) = θ ℓ - θ j
  | 0, j, hj => by
    obtain rfl := Nat.le_zero.1 hj
    simp
  | ℓ + 1, j, hj => by
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge j (ℓ + 1) with hjl | hjl
    · rw [sum_switch_telescope θ ℓ j (Nat.lt_succ_iff.1 hjl)]
      simp only [Nat.lt_succ_iff.1 hjl, ↓reduceIte]
      ring
    · obtain rfl : j = ℓ + 1 := le_antisymm hj hjl
      have h0 : (∑ i ∈ Finset.range ℓ, if ℓ + 1 ≤ i then θ (i + 1) - θ i else 0) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          have := Finset.mem_range.1 hi
          simp only [show ¬ ℓ + 1 ≤ i by omega, ↓reduceIte]
      rw [h0]
      simp only [show ¬ ℓ + 1 ≤ ℓ by omega, ↓reduceIte]
      ring

/-- **The interval index of a point between monotone levels** (left side): if `p 0 < x < 0 = p K`, `p` increases on
`[0, K]` and `x` is no intermediate level, then `x` lies strictly between two consecutive levels. -/
theorem exists_between_levels {p : ℕ → ℝ} {K : ℕ} (hpK : p K = 0) {x : ℝ} (h0 : p 0 < x) (hx : x < 0)
    (hne : ∀ m, 1 ≤ m → m < K → x ≠ p m) : ∃ j < K, p j < x ∧ x < p (j + 1) := by
  classical
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with rfl | h
    · rw [hpK] at h0; linarith
    · exact h
  have hex : ∃ j, x < p (j + 1) := ⟨K - 1, by rw [Nat.sub_add_cancel hK, hpK]; exact hx⟩
  set j₀ := Nat.find hex with hj₀
  have hj₀s : x < p (j₀ + 1) := Nat.find_spec hex
  have hj₀K : j₀ < K := by
    have := Nat.find_min' hex (show x < p (K - 1 + 1) by rw [Nat.sub_add_cancel hK, hpK]; exact hx)
    omega
  refine ⟨j₀, hj₀K, ?_, hj₀s⟩
  rcases Nat.eq_zero_or_pos j₀ with h | h
  · rw [h]; exact h0
  · obtain ⟨j', hj'⟩ : ∃ j', j₀ = j' + 1 := ⟨j₀ - 1, by omega⟩
    have hmin : ¬ x < p (j' + 1) := Nat.find_min hex (by omega)
    rw [hj']
    exact lt_of_le_of_ne (not_lt.1 hmin) fun h => hne (j' + 1) (by omega) (by omega) h.symm

/-- **The interval index of a point between monotone levels** (right side, mirror). -/
theorem exists_between_levels_right {q : ℕ → ℝ} {K : ℕ} (hqK : q K = 0) {x : ℝ} (h0 : x < q 0) (hx : 0 < x)
    (hne : ∀ m, 1 ≤ m → m < K → x ≠ q m) : ∃ j < K, q (j + 1) < x ∧ x < q j := by
  have h := exists_between_levels (p := fun j => -q j) (K := K) (by simp [hqK]) (x := -x) (by linarith)
    (by linarith) fun m hm1 hmK he => hne m hm1 hmK (by linarith)
  obtain ⟨j, hjK, h1, h2⟩ := h
  exact ⟨j, hjK, by linarith, by linarith⟩

/-- The left base image of a shifted chain lies right of the root's left base image (flow property and
monotonicity of the record positions; gap hypothesis on `[a, T]`). -/
theorem chartAL_le_chartAL_shiftDrive {W : ℝ → ℝ} (hW : Continuous W) {a T : ℝ} (ha : 0 < a)
    (haT : a ≤ T) (hgap : ∀ r ∈ Icc a T, chartAL W r < 0) :
    chartAL W T ≤ chartAL (shiftDrive W a) (T - a) := by
  have hws := QuantumZipper.RS.continuous_shiftDrive hW a
  have h1 := markPosL_shiftDrive_chartAL hW ha (sub_nonneg.2 haT) (U := T - a) (by
    intro r hr; exact hgap r ⟨hr.1, by linarith [hr.2]⟩)
  rw [show a + (T - a) = T by ring] at h1
  rw [← h1, ← markPosL_zero_eq_chartAL hws (shiftDrive_zero_apply W a) (sub_nonneg.2 haT)]
  exact Sec7.StripSideHeightProb.markPosL_anti hws (shiftDrive_zero_apply W a) (sub_nonneg.2 haT) le_rfl
    (hgap a ⟨le_rfl, haT⟩).le

/-- The right base image of a shifted chain lies left of the root's right base image. -/
theorem chartAR_shiftDrive_le_chartAR {W : ℝ → ℝ} (hW : Continuous W) {a T : ℝ} (ha : 0 < a)
    (haT : a ≤ T) (hgap : ∀ r ∈ Icc a T, 0 < chartAR W r) :
    chartAR (shiftDrive W a) (T - a) ≤ chartAR W T := by
  have hws := QuantumZipper.RS.continuous_shiftDrive hW a
  have h1 := markPos_shiftDrive_chartAR hW ha (sub_nonneg.2 haT) (U := T - a) (by
    intro r hr; exact hgap r ⟨hr.1, by linarith [hr.2]⟩)
  rw [show a + (T - a) = T by ring] at h1
  rw [← h1, ← markPos_zero_eq_chartAR hws (shiftDrive_zero_apply W a) (sub_nonneg.2 haT)]
  exact Sec7.StripSideHeightProb.markPos_mono hws (shiftDrive_zero_apply W a) (sub_nonneg.2 haT) le_rfl
    (hgap a ⟨le_rfl, haT⟩).le

end Helpers
/-! ### The image stage word -/

section Word

variable {nL nR : ℕ}

/-- The left weight of the mark born at switch `m` (`m ≥ 1`): `−(θ_m − θ_{m−1}) χ/λ`. -/
def swL (κ : ℝ) (ang : ℕ → ℝ) (m : ℕ) : ℝ := -((ang m - ang (m - 1)) * chiC κ / sleLambda κ)

/-- The right weight of the mark born at switch `m`: `(θ_m − θ_{m−1}) χ/λ`. -/
def swR (κ : ℝ) (ang : ℕ → ℝ) (m : ℕ) : ℝ := (ang m - ang (m - 1)) * chiC κ / sleLambda κ

/-- The left image born mark of switch `m`: the left base image of the image chain shifted at the image time `A m`. -/
def imgBornL (W' : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ) (m : ℕ) : ℝ := chartAL (shiftDrive W' (A m)) (T - A m)

/-- The right image born mark of switch `m`. -/
def imgBornR (W' : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ) (m : ℕ) : ℝ := chartAR (shiftDrive W' (A m)) (T - A m)

/-- The root image left marks of CROSSCOND-THETA (images of the root marks and the junction mark). -/
def rootVL (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (T : ℝ) : Fin (nL + 1) → ℝ :=
  fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T

/-- The root image right marks of CROSSCOND-THETA. -/
def rootVR (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (T : ℝ) : Fin (nR + 1) → ℝ :=
  fun j => rightImg W' (imgMarkR xR ω s j) T - W' T

/-- **The left weights of the image stage word**: the switch weights of switches `1, …, ℓ`, then the root image
weights `imgRhoLT ρL θ κ`. -/
def imgStageRhoL (κ θ : ℝ) (ρL : Fin nL → ℝ) (ang : ℕ → ℝ) (ℓ : ℕ) : Fin (ℓ + (nL + 1)) → ℝ :=
  Fin.append (fun j : Fin ℓ => swL κ ang (j + 1)) (imgRhoLT ρL θ κ)

/-- The right weights of the image stage word. -/
def imgStageRhoR (κ θ : ℝ) (ρR : Fin nR → ℝ) (ang : ℕ → ℝ) (ℓ : ℕ) : Fin (ℓ + (nR + 1)) → ℝ :=
  Fin.append (fun j : Fin ℓ => swR κ ang (j + 1)) (imgRhoRT ρR θ κ)

/-- **The left marks of the image stage word**: the image born marks of switches `1, …, ℓ`, then the root image
marks. -/
def imgStageVL (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ) (ℓ : ℕ) :
    Fin (ℓ + (nL + 1)) → ℝ :=
  Fin.append (fun j : Fin ℓ => imgBornL W' T A (j + 1)) (rootVL xL ω s W' T)

/-- The right marks of the image stage word. -/
def imgStageVR (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ) (ℓ : ℕ) :
    Fin (ℓ + (nR + 1)) → ℝ :=
  Fin.append (fun j : Fin ℓ => imgBornR W' T A (j + 1)) (rootVR xR ω s W' T)

variable {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {ang : ℕ → ℝ} {ℓ : ℕ} {xL : Fin nL → ℝ}
  {xR : Fin nR → ℝ} {ω W' A : ℝ → ℝ} {s T : ℝ}

/-- The image stage data left of the seed, split into the born and the root parts. -/
theorem forceBoundaryData_imgStage_neg {A : ℕ → ℝ} {x : ℝ} (hx : x < 0) :
    forceBoundaryData κ (imgStageRhoL κ θ ρL ang ℓ) (imgStageRhoR κ θ ρR ang ℓ) (imgStageVL xL ω s W' T A ℓ)
      (imgStageVR xR ω s W' T A ℓ) x =
      -(Real.pi / Real.sqrt κ) * (1 + (∑ j : Fin ℓ, if x < imgBornL W' T A (j + 1) then swL κ ang (j + 1) else 0) +
        ∑ i ∈ Finset.univ.filter (fun i => x < rootVL xL ω s W' T i), imgRhoLT ρL θ κ i) := by
  unfold forceBoundaryData
  simp only [hx, ↓reduceIte]
  rw [Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter]
  simp only [imgStageRhoL, imgStageVL, Fin.append_left, Fin.append_right]
  ring

/-- The image stage data right of the seed, split into the born and the root parts. -/
theorem forceBoundaryData_imgStage_nonneg {A : ℕ → ℝ} {x : ℝ} (hx : 0 ≤ x) :
    forceBoundaryData κ (imgStageRhoL κ θ ρL ang ℓ) (imgStageRhoR κ θ ρR ang ℓ) (imgStageVL xL ω s W' T A ℓ)
      (imgStageVR xR ω s W' T A ℓ) x =
      (Real.pi / Real.sqrt κ) * (1 + (∑ j : Fin ℓ, if imgBornR W' T A (j + 1) ≤ x then swR κ ang (j + 1) else 0) +
        ∑ i ∈ Finset.univ.filter (fun i => rootVR xR ω s W' T i ≤ x), imgRhoRT ρR θ κ i) := by
  unfold forceBoundaryData
  simp only [not_lt.2 hx, ↓reduceIte]
  rw [Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter]
  simp only [imgStageRhoR, imgStageVR, Fin.append_left, Fin.append_right]
  ring

/-- **The born part of the left image data** when exactly the switches after `j₀` are right of `x`:
`Σ_{j₀ ≤ j < ℓ} w_{j+1} = −(θ_ℓ − θ_{j₀}) χ/λ`. -/
theorem sum_swL_of_iff {P : Fin ℓ → Prop} [DecidablePred P] {j₀ : ℕ} (hj₀ : j₀ ≤ ℓ) (hP : ∀ j, P j ↔ j₀ ≤ (j : ℕ)) :
    (∑ j : Fin ℓ, if P j then swL κ ang (j + 1) else 0) = -((ang ℓ - ang j₀) * chiC κ / sleLambda κ) := by
  have e : ∀ j : Fin ℓ, (if P j then swL κ ang (j + 1) else 0) =
      -(chiC κ / sleLambda κ) * (if j₀ ≤ (j : ℕ) then ang ((j : ℕ) + 1) - ang j else 0) := fun j => by
    by_cases h : j₀ ≤ (j : ℕ)
    · simp only [(hP j).2 h, h, ↓reduceIte, swL, Nat.add_sub_cancel]
      ring
    · simp only [show ¬ P j from fun h' => h ((hP j).1 h'), h, ↓reduceIte]
      ring
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun j => if j₀ ≤ j then ang (j + 1) - ang j else 0) ℓ,
    sum_switch_telescope ang ℓ j₀ hj₀]
  ring

/-- **The born part of the right image data** (mirror of `sum_swL_of_iff`). -/
theorem sum_swR_of_iff {P : Fin ℓ → Prop} [DecidablePred P] {j₀ : ℕ} (hj₀ : j₀ ≤ ℓ) (hP : ∀ j, P j ↔ j₀ ≤ (j : ℕ)) :
    (∑ j : Fin ℓ, if P j then swR κ ang (j + 1) else 0) = (ang ℓ - ang j₀) * chiC κ / sleLambda κ := by
  have e : ∀ j : Fin ℓ, (if P j then swR κ ang (j + 1) else 0) =
      (chiC κ / sleLambda κ) * (if j₀ ≤ (j : ℕ) then ang ((j : ℕ) + 1) - ang j else 0) := fun j => by
    by_cases h : j₀ ≤ (j : ℕ)
    · simp only [(hP j).2 h, h, ↓reduceIte, swR, Nat.add_sub_cancel]
      ring
    · simp only [show ¬ P j from fun h' => h ((hP j).1 h'), h, ↓reduceIte]
      ring
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun j => if j₀ ≤ j then ang (j + 1) - ang j else 0) ℓ,
    sum_switch_telescope ang ℓ j₀ hj₀]
  ring

end Word
/-! ### The image stage data on and off the slit -/

section Data

variable {nL nR : ℕ} {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {ang : ℕ → ℝ} {ℓ : ℕ} {xL : Fin nL → ℝ}
  {xR : Fin nR → ℝ} {Wα ω W' : ℝ → ℝ} {t s T : ℝ} {A S : ℕ → ℝ}

theorem shiftDrive_zero_eq {W : ℝ → ℝ} (hW0 : W 0 = 0) : shiftDrive W 0 = W := by
  funext r
  simp only [shiftDrive, zero_add, hW0, sub_zero]

theorem mem_forceJumpSet_imgBornL (j : Fin ℓ) :
    imgBornL W' T A (j + 1) ∈ forceJumpSet (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ) :=
  Set.mem_insert_of_mem 0 (Or.inl ⟨Fin.castAdd (nL + 1) j, by simp only [imgStageVL, Fin.append_left]⟩)

theorem mem_forceJumpSet_imgBornR (j : Fin ℓ) :
    imgBornR W' T A (j + 1) ∈ forceJumpSet (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ) :=
  Set.mem_insert_of_mem 0 (Or.inr ⟨Fin.castAdd (nR + 1) j, by simp only [imgStageVR, Fin.append_left]⟩)

theorem sleLambda_mul_div (hκ : 0 < κ) (a : ℝ) : Real.pi / Real.sqrt κ * (a / sleLambda κ) = a := by
  have h : Real.pi / Real.sqrt κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  unfold sleLambda
  field_simp

/-- **The image stage data off the closed slit are the root image data** (all born marks lie on the slit side of
`x`; the switch weights add up to `−θ_ℓ χ/λ` on the left, `θ_ℓ χ/λ` on the right; `θ_0 = 0`). -/
theorem physData_stage (hκ : 0 < κ) (hW' : Continuous W') (hT : 0 < T) (hang0 : ang 0 = 0)
    (hA : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < A m ∧ A m < T)
    (hgapI : ∀ r ∈ Ioc 0 T, chartAL W' r < 0 ∧ 0 < chartAR W' r) {x : ℝ}
    (hx : x < chartAL W' T ∨ chartAR W' T < x) :
    forceBoundaryData κ (imgStageRhoL κ θ ρL ang ℓ) (imgStageRhoR κ θ ρR ang ℓ) (imgStageVL xL ω s W' T A ℓ)
        (imgStageVR xR ω s W' T A ℓ) x - ang ℓ * chiC κ =
      forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ) (rootVL xL ω s W' T) (rootVR xR ω s W' T) x := by
  have hA' : ∀ j : Fin ℓ, 0 < A (j + 1) ∧ A (j + 1) < T := fun j => hA (j + 1) (by omega) (by omega)
  rcases hx with hx | hx
  · have hx0 : x < 0 := hx.trans_le (chartAL_nonpos hW' hT.le)
    have hborn : ∀ j : Fin ℓ, x < imgBornL W' T A (j + 1) ↔ 0 ≤ (j : ℕ) := fun j => by
      refine ⟨fun _ => Nat.zero_le _, fun _ => hx.trans_le ?_⟩
      exact chartAL_le_chartAL_shiftDrive hW' (hA' j).1 (hA' j).2.le fun r hr =>
        (hgapI r ⟨(hA' j).1.trans_le hr.1, hr.2⟩).1
    rw [forceBoundaryData_imgStage_neg hx0, sum_swL_of_iff (Nat.zero_le ℓ) hborn, hang0]
    unfold forceBoundaryData
    simp only [hx0, ↓reduceIte]
    have e := sleLambda_mul_div hκ ((ang ℓ - 0) * chiC κ)
    unfold rootVL
    linear_combination e
  · have hx0 : 0 ≤ x := (chartAR_nonneg hW' hT.le).trans hx.le
    have hborn : ∀ j : Fin ℓ, imgBornR W' T A (j + 1) ≤ x ↔ 0 ≤ (j : ℕ) := fun j => by
      refine ⟨fun _ => Nat.zero_le _, fun _ => le_trans ?_ hx.le⟩
      exact chartAR_shiftDrive_le_chartAR hW' (hA' j).1 (hA' j).2.le fun r hr =>
        (hgapI r ⟨(hA' j).1.trans_le hr.1, hr.2⟩).2
    rw [forceBoundaryData_imgStage_nonneg hx0, sum_swR_of_iff (Nat.zero_le ℓ) hborn, hang0]
    unfold forceBoundaryData
    simp only [not_lt.2 hx0, ↓reduceIte]
    have e := sleLambda_mul_div hκ ((ang ℓ - 0) * chiC κ)
    unfold rootVR
    linear_combination e
/-- The root image left marks lie left of the image slit. -/
theorem rootVL_le_chartAL (hω : Continuous ω) (hs : 0 ≤ s) (hjL : 0 < rightImg ω 0 s - ω s)
    (hxL : ∀ i, xL i ≤ 0) (hW' : Continuous W') (hT : 0 ≤ T) (i : Fin (nL + 1)) :
    rootVL xL ω s W' T i ≤ chartAL W' T := by
  have h := rightImg_mono_index (w := fun r => -W' r) hW'.neg hT
    (neg_nonneg.2 (imgMarkL_nonpos hω hs hjL hxL i))
  unfold rootVL chartAL
  linarith

/-- The root image right marks lie right of the image slit. -/
theorem chartAR_le_rootVR (hω : Continuous ω) (hs : 0 ≤ s) (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0)
    (hxR : ∀ j, 0 ≤ xR j) (hW' : Continuous W') (hT : 0 ≤ T) (j : Fin (nR + 1)) :
    chartAR W' T ≤ rootVR xR ω s W' T j := by
  have h := rightImg_mono_index hW' hT (imgMarkR_nonneg hω hs hjR hxR j)
  unfold rootVR chartAR
  linarith

variable {α : ℝ → ℂ} {η' : ℝ → ℂ}

/-- **The slit data match, left side.** At a left image slit point `x` (not an image jump) with flow-chart limit `x₁`,
`x₁` is not a jump of the stage word and its data equal the image stage data at `x` minus `θ_ℓ χ`. -/
theorem slitData_stage_neg (hκ : 0 < κ) (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv ω s))
    (hKs : ∀ z ∈ closure (fwdHull ω s), z.im = 0 → z = 0) (hjL : 0 < rightImg ω 0 s - ω s)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 < T) (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') (hGc : IsClosed (negInv '' fwdHull ω s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hdis : Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t))
    (hS0 : S 0 = 0) (hS : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < S m ∧ S m < t)
    (hA : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < A m ∧ A m < T ∧ η' (A m) = revChart ω s (α (S m)))
    {c : BoundaryWord}
    (hLc : IsLeftLevels c (ℓ + 1) (fun j => chartAL (shiftDrive Wα (S j)) (t - S j))
      (fun j => -sleLambda κ - ang j * chiC κ))
    (hroot : ∀ i, rootVL xL ω s W' T i ≤ chartAL W' T) {x x₁ : ℝ}
    (hxJ : x ∉ forceJumpSet (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ))
    (hxL : chartAL W' T < x) (hx0 : x < 0) (hΘ : Tendsto (imgTheta Wα t ω s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ))) :
    x₁ ∉ c.jumps ∧ c.fn x₁ = forceBoundaryData κ (imgStageRhoL κ θ ρL ang ℓ) (imgStageRhoR κ θ ρR ang ℓ)
      (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ) x - ang ℓ * chiC κ := by
  obtain ⟨x₂, hx₂0, hx₂L, hΘ₂, -⟩ := slit_left_limits hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjL hW' hW'0 hT
    hη' hη'p hGc hdisj hdis hK' htip hxL hx0
  have := nhdsWithin_H_neBot x
  have hx₁₂ : x₁ = x₂ := by exact_mod_cast tendsto_nhds_unique hΘ hΘ₂
  subst hx₁₂
  have hxH : extendFrom H (fwdMapInv W' T) x ∈ H :=
    extendFrom_mem_H_of_chartAL_lt hη' hη'p hW' hW'0 hT hxL (hx0.trans_le (chartAR_nonneg hW' hT.le))
  set p : ℕ → ℝ := fun j => chartAL (shiftDrive Wα (S j)) (t - S j) with hpdef
  have hp0 : p 0 = chartAL Wα t := by simp only [hpdef, hS0, sub_zero, shiftDrive_zero_eq hWα0]
  obtain ⟨hpk, hpm, hpJ, hpf⟩ := hLc
  have hmono := le_of_succ_le' hpm
  have hne : ∀ m, 1 ≤ m → m < ℓ + 1 → x₁ ≠ p m := by
    intro m hm1 hm hxm
    obtain ⟨hSm, hSmt⟩ := hS m hm1 (Nat.lt_succ_iff.1 hm)
    obtain ⟨hAm, hAmT, hAe⟩ := hA m hm1 (Nat.lt_succ_iff.1 hm)
    rcases eq_imgChartA_of_eq_chartA hα hαp hWα hWα0 ht.le hω hω0 hs hη' hη'p hW' hW'0 hT.le hdisj hK' hSm hSmt
      hAm hAmT hAe hxH hΘ (Or.inl hxm) with h | h
    · obtain ⟨j, hj⟩ : ∃ j : Fin ℓ, (j : ℕ) + 1 = m := ⟨⟨m - 1, by omega⟩, by simp only; omega⟩
      subst hj
      exact hxJ (by rw [h]; exact mem_forceJumpSet_imgBornL j)
    · have := chartAR_nonneg (QuantumZipper.RS.continuous_shiftDrive hW' (A m)) (sub_pos.2 hAmT).le
      rw [← h] at this
      linarith
  have hp0x : p 0 < x₁ := by rw [hp0]; exact hx₂L
  obtain ⟨j₀, hj₀, h1, h2⟩ := exists_between_levels hpk hp0x hx₂0 hne
  have hJ : x₁ ∉ c.jumps := fun hJ => by
    obtain ⟨m, hm1, hm, he⟩ := hpJ x₁ hJ hp0x hx₂0
    exact hne m hm1 hm he
  refine ⟨hJ, ?_⟩
  rw [hpf j₀ hj₀ x₁ h1 h2 hJ, forceBoundaryData_imgStage_neg hx0]
  have hborn : ∀ j : Fin ℓ, x < imgBornL W' T A (j + 1) ↔ j₀ ≤ (j : ℕ) := by
    intro j
    obtain ⟨hSm, hSmt⟩ := hS (j + 1) (by omega) (by omega)
    obtain ⟨hAm, hAmT, hAe⟩ := hA (j + 1) (by omega) (by omega)
    have htr := mem_Ioo_chartA_iff_of_imgTheta hα hαp hWα hWα0 ht.le hω hω0 hs hη' hη'p hW' hW'0 hT.le hdisj hK'
      htip hSm hSmt hAm hAmT hAe hxH hΘ
    have hq : x₁ < chartAR (shiftDrive Wα (S (j + 1))) (t - S (j + 1)) :=
      hx₂0.trans_le (chartAR_nonneg (QuantumZipper.RS.continuous_shiftDrive hWα _) (sub_pos.2 hSmt).le)
    have hq' : x < chartAR (shiftDrive W' (A (j + 1))) (T - A (j + 1)) :=
      hx0.trans_le (chartAR_nonneg (QuantumZipper.RS.continuous_shiftDrive hW' _) (sub_pos.2 hAmT).le)
    have hiff : p (j + 1) < x₁ ↔ imgBornL W' T A (j + 1) < x :=
      ⟨fun h => (htr.1 ⟨h, hq⟩).1, fun h => (htr.2 ⟨h, hq'⟩).1⟩
    have hxne : x ≠ imgBornL W' T A (j + 1) := fun h => hxJ (h ▸ mem_forceJumpSet_imgBornL j)
    constructor
    · intro hlt
      by_contra hj
      push Not at hj
      have h3 : p (j + 1) < x₁ := (hmono (j + 1) j₀ hj (by omega)).trans_lt h1
      exact absurd (hiff.1 h3) (not_lt.2 hlt.le)
    · intro hj
      have h3 : x₁ < p (j + 1) := h2.trans_le (hmono (j₀ + 1) (j + 1) (by omega) (by omega))
      rcases lt_or_gt_of_ne hxne with h | h
      · exact h
      · exact absurd (hiff.2 h) (not_lt.2 h3.le)
  have hrootE : (Finset.univ.filter fun i => x < rootVL xL ω s W' T i) = ∅ :=
    Finset.filter_false_of_mem fun i _ => not_lt.2 ((hroot i).trans hxL.le)
  rw [sum_swL_of_iff (Nat.lt_succ_iff.1 hj₀) hborn, hrootE, Finset.sum_empty]
  have e := sleLambda_mul_div hκ ((ang ℓ - ang j₀) * chiC κ)
  have hlam : sleLambda κ = Real.pi / Real.sqrt κ := rfl
  linear_combination -e - hlam
/-- **The slit data match, right side** (mirror of `slitData_stage_neg`). -/
theorem slitData_stage_pos (hκ : 0 < κ) (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv ω s))
    (hKs : ∀ z ∈ closure (fwdHull ω s), z.im = 0 → z = 0) (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 < T) (hη' : IsLoewnerTrace W' η')
    (hη'p : IsProperArc η') (hGc : IsClosed (negInv '' fwdHull ω s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hdis : Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t))
    (hS0 : S 0 = 0) (hS : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < S m ∧ S m < t)
    (hA : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < A m ∧ A m < T ∧ η' (A m) = revChart ω s (α (S m)))
    {c : BoundaryWord}
    (hRc : IsRightLevels c (ℓ + 1) (fun j => chartAR (shiftDrive Wα (S j)) (t - S j))
      (fun j => sleLambda κ - ang j * chiC κ))
    (hroot : ∀ j, chartAR W' T ≤ rootVR xR ω s W' T j) {x x₁ : ℝ}
    (hxJ : x ∉ forceJumpSet (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ))
    (hxR : x < chartAR W' T) (hx0 : 0 < x) (hΘ : Tendsto (imgTheta Wα t ω s W' T) (𝓝[H] (x : ℂ)) (𝓝 (x₁ : ℂ))) :
    x₁ ∉ c.jumps ∧ c.fn x₁ = forceBoundaryData κ (imgStageRhoL κ θ ρL ang ℓ) (imgStageRhoR κ θ ρR ang ℓ)
      (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ) x - ang ℓ * chiC κ := by
  obtain ⟨x₂, hx₂0, hx₂R, hΘ₂, -⟩ := slit_right_limits hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjR hW' hW'0 hT
    hη' hη'p hGc hdisj hdis hK' htip hxR hx0
  have := nhdsWithin_H_neBot x
  have hx₁₂ : x₁ = x₂ := by exact_mod_cast tendsto_nhds_unique hΘ hΘ₂
  subst hx₁₂
  have hxH : extendFrom H (fwdMapInv W' T) x ∈ H :=
    extendFrom_mem_H_of_chartAL_lt hη' hη'p hW' hW'0 hT ((chartAL_nonpos hW' hT.le).trans_lt hx0) hxR
  set q : ℕ → ℝ := fun j => chartAR (shiftDrive Wα (S j)) (t - S j) with hqdef
  have hq0 : q 0 = chartAR Wα t := by simp only [hqdef, hS0, sub_zero, shiftDrive_zero_eq hWα0]
  obtain ⟨hqk, hqm, hqJ, hqf⟩ := hRc
  have hmono := ge_of_succ_ge' hqm
  have hne : ∀ m, 1 ≤ m → m < ℓ + 1 → x₁ ≠ q m := by
    intro m hm1 hm hxm
    obtain ⟨hSm, hSmt⟩ := hS m hm1 (Nat.lt_succ_iff.1 hm)
    obtain ⟨hAm, hAmT, hAe⟩ := hA m hm1 (Nat.lt_succ_iff.1 hm)
    rcases eq_imgChartA_of_eq_chartA hα hαp hWα hWα0 ht.le hω hω0 hs hη' hη'p hW' hW'0 hT.le hdisj hK' hSm hSmt
      hAm hAmT hAe hxH hΘ (Or.inr hxm) with h | h
    · have := chartAL_nonpos (QuantumZipper.RS.continuous_shiftDrive hW' (A m)) (sub_pos.2 hAmT).le
      rw [← h] at this
      linarith
    · obtain ⟨j, hj⟩ : ∃ j : Fin ℓ, (j : ℕ) + 1 = m := ⟨⟨m - 1, by omega⟩, by simp only; omega⟩
      subst hj
      exact hxJ (by rw [h]; exact mem_forceJumpSet_imgBornR j)
  have hq0x : x₁ < q 0 := by rw [hq0]; exact hx₂R
  obtain ⟨j₀, hj₀, h1, h2⟩ := exists_between_levels_right hqk hq0x hx₂0 hne
  have hJ : x₁ ∉ c.jumps := fun hJ => by
    obtain ⟨m, hm1, hm, he⟩ := hqJ x₁ hJ hx₂0 hq0x
    exact hne m hm1 hm he
  refine ⟨hJ, ?_⟩
  rw [hqf j₀ hj₀ x₁ h1 h2 hJ, forceBoundaryData_imgStage_nonneg hx0.le]
  have hborn : ∀ j : Fin ℓ, imgBornR W' T A (j + 1) ≤ x ↔ j₀ ≤ (j : ℕ) := by
    intro j
    obtain ⟨hSm, hSmt⟩ := hS (j + 1) (by omega) (by omega)
    obtain ⟨hAm, hAmT, hAe⟩ := hA (j + 1) (by omega) (by omega)
    have htr := mem_Ioo_chartA_iff_of_imgTheta hα hαp hWα hWα0 ht.le hω hω0 hs hη' hη'p hW' hW'0 hT.le hdisj hK'
      htip hSm hSmt hAm hAmT hAe hxH hΘ
    have hp : chartAL (shiftDrive Wα (S (j + 1))) (t - S (j + 1)) < x₁ :=
      (chartAL_nonpos (QuantumZipper.RS.continuous_shiftDrive hWα _) (sub_pos.2 hSmt).le).trans_lt hx₂0
    have hp' : chartAL (shiftDrive W' (A (j + 1))) (T - A (j + 1)) < x :=
      (chartAL_nonpos (QuantumZipper.RS.continuous_shiftDrive hW' _) (sub_pos.2 hAmT).le).trans_lt hx0
    have hiff : x₁ < q (j + 1) ↔ x < imgBornR W' T A (j + 1) :=
      ⟨fun h => (htr.1 ⟨hp, h⟩).2, fun h => (htr.2 ⟨hp', h⟩).2⟩
    have hxne : x ≠ imgBornR W' T A (j + 1) := fun h => hxJ (h ▸ mem_forceJumpSet_imgBornR j)
    constructor
    · intro hle
      by_contra hj
      push Not at hj
      have h3 : x₁ < q (j + 1) := h2.trans_le (hmono (j + 1) j₀ hj (by omega))
      exact absurd hle (not_le.2 (hiff.1 h3))
    · intro hj
      have h3 : q (j + 1) < x₁ := (hmono (j₀ + 1) (j + 1) (by omega) (by omega)).trans_lt h1
      by_contra hlt
      exact absurd (hiff.2 (not_le.1 hlt)) (not_lt.2 h3.le)
  have hrootE : (Finset.univ.filter fun j => rootVR xR ω s W' T j ≤ x) = ∅ :=
    Finset.filter_false_of_mem fun j _ => not_le.2 (hxR.trans_le (hroot j))
  rw [sum_swR_of_iff (Nat.lt_succ_iff.1 hj₀) hborn, hrootE, Finset.sum_empty]
  have e := sleLambda_mul_div hκ ((ang ℓ - ang j₀) * chiC κ)
  have hlam : sleLambda κ = Real.pi / Real.sqrt κ := rfl
  linear_combination hlam - e

end Data
/-! ### The staged mean identification, per sample -/

section Main

variable {nL nR : ℕ} {κ : ℝ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (θ : ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {Wα ω W' : ℝ → ℝ} {t s T : ℝ} {ang : ℕ → ℝ} {ℓ : ℕ} {A S : ℕ → ℝ}

/-- **The staged mean identification, per sample** (S2). Let the staged prefix be the simple trace `α` of the
concatenated driver `Wα` up to `t`, with pieces `j = 0, …, ℓ` starting at `S j` (`S 0 = 0`, `0 < S m < t` for the
switches `m = 1, …, ℓ`), angles `θ_j` (`θ_0 = 0`), and let `c` be the stage word in the prefix chart, with the side
heights `∓λ − θ_j χ` between the base images of the shifted chain (`IsLeftLevels`, `IsRightLevels`). Let the image
chain `W′` (image trace `η′`, time `T`) have its base images off the driver (`hgapI`) and let `A m` be the image times
of the switch points. If the union mean `M` satisfies CROSSCOND-THETA's counterflow-side hypotheses (`hv`, `hG`,
`hInf`, `hId`), the flow side's limit with the stage word's own mean (`hFl`) and Aux. 28's uniqueness (`huniq`), then
on `ℍ ∖ (A ∪ G)`, `w + 𝔥₀ = u ∘ f′_T ∘ Ψ − θ_ℓ χ − χ (arg f′_T′ ∘ Ψ + arg Ψ′)` with `u` the bounded harmonic
extension of the image stage word. -/
theorem eqOn_imgChart_stage {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hκ : 0 < κ)
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv ω s))
    (hKs : ∀ z ∈ closure (fwdHull ω s), z.im = 0 → z = 0) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hGc : IsClosed (negInv '' fwdHull ω s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hdis : Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)))
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 < T) (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t))
    (hS0 : S 0 = 0) (hS : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < S m ∧ S m < t)
    (hA : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < A m ∧ A m < T ∧ η' (A m) = revChart ω s (α (S m)))
    (hgapI : ∀ r ∈ Ioc 0 T, chartAL W' r < 0 ∧ 0 < chartAR W' r) (hang0 : ang 0 = 0)
    {c : BoundaryWord} (hc : c.IsSorted)
    (hLc : IsLeftLevels c (ℓ + 1) (fun j => chartAL (shiftDrive Wα (S j)) (t - S j))
      (fun j => -sleLambda κ - ang j * chiC κ))
    (hRc : IsRightLevels c (ℓ + 1) (fun j => chartAR (shiftDrive Wα (S j)) (t - S j))
      (fun j => sleLambda κ - ang j * chiC κ))
    {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (imgStageRhoL κ θ ρL ang ℓ) (imgStageRhoR κ θ ρR ang ℓ)
      (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ))
      (forceJumpSet (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ)) u)
    (hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + θ * chiC κ -
        (c.mean (fwdMap Wα t z) - chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (α v)) (𝓝 0))
    {w u₀ : ℂ → ℝ} (hMw : ∀ z, M z + θ * chiC κ = w z + u₀ z)
    (huniq : ∀ z₀ ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s), ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - chiC κ * L (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀,
        w z + u₀ z = G (φc z) - chiC κ * L z) :
    ∀ z ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s), w z + u₀ z =
      (u (fwdMap W' T (revChart ω s z)) - ang ℓ * chiC κ) -
        chiC κ * ((logDerivFwd W' T (revChart ω s z)).im + (logDerivPsi ω s z).im) := by
  have hJ' : (forceJumpSet (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ)).Finite := by
    simp only [forceJumpSet]
    exact ((Set.finite_range _).union (Set.finite_range _)).insert 0
  have hrootL := rootVL_le_chartAL hω hs hjL hxL hW' hT.le (W' := W') (T := T)
  have hrootR := chartAR_le_rootVR hω hs hjR hxR hW' hT.le (W' := W') (T := T)
  refine eqOn_imgChart_slitData ρL ρR θ hα hαp hWα hWα0 ht hKt hκ hω hω0 hs hB hKs hjL hjR hGc hdisj hdis hxL hxR hv
    hG hInf hId hW' hW'0 hη' hη'p hT hK' htip hJ' (c.isBoundedHarmonicExtension_mean hc)
    (IsBoundedHarmonicExtension.sub_const hu _) ?_ ?_ hFl
    hMw huniq
  · intro x x₁ hxJ hxL' hxR' hx0 hΘ
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · exact slitData_stage_neg hκ hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjL hW' hW'0 hT hη' hη'p hGc hdisj hdis
        hK' htip hS0 hS hA hLc hrootL hxJ hxL' hneg hΘ
    · exact slitData_stage_pos hκ hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjR hW' hW'0 hT hη' hη'p hGc hdisj hdis
        hK' htip hS0 hS hA hRc hrootR hxJ hxR' hpos hΘ
  · intro x _ hx
    exact physData_stage hκ hW' hT hang0 (fun m h1 h2 => ⟨(hA m h1 h2).1, (hA m h1 h2).2.1⟩) hgapI hx

end Main

end InteractingSLE.Sec5.CrossCond.StagedFinal
