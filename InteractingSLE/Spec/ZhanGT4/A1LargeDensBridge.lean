/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ForcesLaw
import InteractingSLE.Spec.ZhanGT4.DualIdent

/-!
# Zhan's A.1 (R80): the large-curve direction's capacity Brownian motion from the frozen-curve line

Packet PROVE-A1-LARGEDENS. Source: Astra, *Follow-up proofs* §A.1.3 (`ig1_followup_proofs.txt` L341–L355, R38):
"By (D8) and Girsanov, with the other curve stopped, the new drift of `W_j` is `κ_j q_j` … (D10) … The time change
`du = A²_{j,1} dt_j`, Lévy's characterization, …"; follow-up 4 §2.5 item 3 (R71): away from the seeds of the growing
curve "the mapped force equation" and "the mapped driver equation is (D10)".

In the large-curve direction of A.1 the growing curve is the large curve and every image mark is a mark of the frozen
chart (PROVE-A1-MULTIMARK: the images of the small curve's seeds, its tip and its ordinary marks). When the growing
curve is ordinary `SLE_κ` before its rectangle exit (`W = √κB`; in A.1 (Eight) the large curve's only mark has weight
`0`), the landed frozen-curve line A8–A17 (`FrzD10Hyp`) already gives, under `Q = (M̃_S/M̃_0)·P`
(`girsMeasure`), a Brownian motion `B̂` of the capacity-time filtration and the force-point equation of the image
driver (`FrzD10Hyp.isFilteredBrownianReal_bm`, `FrzD10Hyp.sub_eq_bm_add_sum`). This file transports it to the seeded
capacity coordinates of PROVE-A1-FORCES:

* **`seedQuadClock_eq_bmClk`**: the seeded quadratic clock `∫₀ᵗ (seedCapacityCoeff)²` is the full capacity clock
  `C'_t = a(t ∧ S) + (t − t ∧ S)` of the frozen-curve line; hence **`seedFilt_eq_timeChangeFilt`**: A1-FAMILY's
  capacity-time filtration `seedFilt` is the frozen-curve line's time-changed filtration;
* **`seedCapacityDriver_eq_W'`**, **`capForce_frzImg_eq_imgV`**: up to the capacity horizon the seeded capacity driver
  and the capacity coordinate of a frozen-chart mark are the image driver `W'(u) − W'(0)` and the image mark
  `Ṽ(u) − W'(0)` of the frozen-curve line;
* **`seedCapacityBrownian_of_frzD10Hyp`**: PROVE-A1-FORCES's capacity Brownian input `SeedCapacityBrownian` (the
  premise `hBh` of `isSeedSampleLaw_of_capacityBrownian`) under `Q = girsMeasure …`, for frozen-chart marks `pL`, `pR`
  sorted from the frozen data by any `e : Fin nL ⊕ Fin nR ≃ Option (Fin n)`;
* **`isSeedSampleLaw_of_frzD10Hyp`**: A1-FAMILY's one-sample law `IsSeedSampleLaw` under `Q = girsMeasure …`, all clock
  and adaptedness premises of `isSeedSampleLaw_of_capacityBrownian` discharged from `FrzD10Hyp`.

The seeded data `d` only have to carry the frozen-curve line's image chain (`(d ω).a = a ω`, `(d ω).W' = W' ω`) with
their own `OwnData` up to `S`; their driver, hull and chart are not otherwise constrained.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1LargeDens

open A1Family A1MultiMark A1Forces

/-! ### The seeded quadratic clock is the full capacity clock -/

section Clock

variable {Ω : Type*} {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {a : Ω → ℝ → ℝ}

/-- After the own horizon the continued coefficient is `1`. -/
theorem seedCapacityCoeff_of_lt {u : ℝ≥0} {ω : Ω} (hu : S ω < u) : seedCapacityCoeff d S u ω = 1 := by
  simp only [seedCapacityCoeff, positiveStopped, not_le.2 hu, and_false, ite_false, add_zero]

/-- **The seeded quadratic clock is the full capacity clock** `C'_t = a(t ∧ S) + (t − t ∧ S)`. -/
theorem seedQuadClock_eq_bmClk (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hda : ∀ ω, (d ω).a = a ω) : seedQuadClock (seedCapacityCoeff d S) = bmClk a S := by
  funext ω t
  rcases le_total t (S ω) with ht | ht
  · rw [seedCapacityCoeff_clock_eq hown ω ht, bmClk, min_eq_left ht, hda, sub_self, add_zero]
  · have hS := seedCapacityCoeff_clock_eq hown ω (le_refl (S ω))
    rw [bmClk, min_eq_right ht, ← hda, ← hS]
    have hS0 : (0 : ℝ) ≤ S ω := (S ω).coe_nonneg
    have hSt : (S ω : ℝ) ≤ t := NNReal.coe_le_coe.2 ht
    have hc : ContinuousOn (fun u => (d ω).A 1 u ^ 2) (Icc 0 (S ω)) := ((hown ω).continuousOn_frzA 1).pow 2
    have h1 : IntervalIntegrable (fun u : ℝ => seedCapacityCoeff d S u.toNNReal ω ^ 2) volume 0 (S ω) := by
      refine (hc.intervalIntegrable_of_Icc hS0).congr fun u hu => ?_
      rw [uIoc_of_le hS0] at hu
      have hu0 : 0 < u.toNNReal := Real.toNNReal_pos.2 hu.1
      have huS : u.toNNReal ≤ S ω := by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
      simp only [seedCapacityCoeff_eq hu0 huS, Real.coe_toNNReal _ hu.1.le]
    have hone : EqOn (fun u : ℝ => seedCapacityCoeff d S u.toNNReal ω ^ 2) (fun _ => (1 : ℝ)) (Ioc (S ω : ℝ) t) :=
      fun u hu => by
        have hlt : S ω < u.toNNReal := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hS0.trans hu.1.le)]; exact hu.1
        simp only [seedCapacityCoeff_of_lt hlt, one_pow]
    have h2 : IntervalIntegrable (fun u : ℝ => seedCapacityCoeff d S u.toNNReal ω ^ 2) volume (S ω) t := by
      refine (intervalIntegrable_const (c := (1 : ℝ))).congr fun u hu => ?_
      rw [uIoc_of_le hSt] at hu
      exact (hone hu).symm
    show (∫ u in (0 : ℝ)..(t : ℝ), seedCapacityCoeff d S u.toNNReal ω ^ 2) =
      (∫ u in (0 : ℝ)..((S ω : ℝ≥0) : ℝ), seedCapacityCoeff d S u.toNNReal ω ^ 2) + ((t : ℝ) - S ω)
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
      intervalIntegral.integral_congr_Ioo_of_le hSt fun u hu => hone ⟨hu.1, hu.2.le⟩,
      intervalIntegral.integral_const, smul_eq_mul, mul_one]

end Clock

/-! ### The capacity-time filtrations agree -/

section Filt

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- Equal clocks give equal time-changed filtrations (whatever the proofs of the clock facts). -/
theorem timeChangeFilt_invClock_congr {C C' : Ω → ℝ≥0 → ℝ} (h : C = C') (hCc : ∀ ω, Continuous (C ω))
    (hCm : ∀ ω, Monotone (C ω)) (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => C ω r)
    (hCc' : ∀ ω, Continuous (C' ω)) (hCm' : ∀ ω, Monotone (C' ω))
    (hmeas' : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => C' ω r) :
    Zhan.Retarget.timeChangeFilt 𝓕 (isStoppingTime_invClock hCc hCm hmeas) (invClock_mono hCc hCm) =
      Zhan.Retarget.timeChangeFilt 𝓕 (isStoppingTime_invClock hCc' hCm' hmeas') (invClock_mono hCc' hCm') := by
  subst h
  rfl

/-- **A1-FAMILY's `seedFilt` is the frozen-curve line's capacity-time filtration** when the seeded data carry the
image clock `a`. -/
theorem seedFilt_eq_timeChangeFilt {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {a : Ω → ℝ → ℝ}
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W') (hda : ∀ ω, (d ω).a = a ω)
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d S) ω))
    (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => seedQuadClock (seedCapacityCoeff d S) ω r)
    (hCc' : ∀ ω, Continuous (bmClk a S ω)) (hCm' : ∀ ω, Monotone (bmClk a S ω))
    (hmeas' : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => bmClk a S ω r) :
    seedFilt 𝓕 d S hCc hCm hmeas =
      Zhan.Retarget.timeChangeFilt 𝓕 (isStoppingTime_invClock hCc' hCm' hmeas') (invClock_mono hCc' hCm') :=
  timeChangeFilt_invClock_congr (seedQuadClock_eq_bmClk hown hda) hCc hCm hmeas hCc' hCm' hmeas'

end Filt

/-! ### The seeded capacity coordinates are the frozen-curve line's image coordinates -/

section Coords

variable {Ω : Type*} {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {a W' : Ω → ℝ → ℝ}
  (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W') (hda : ∀ ω, (d ω).a = a ω)
  (hdW' : ∀ ω, (d ω).W' = W' ω) {c : ℝ} (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
  (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω)) (hc : 0 < c)
  (hlb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r)

include hown hda hdW'

omit hdW' in
/-- Below the capacity horizon in capacity time is below `a(S)`. -/
theorem coe_le_a_of_le_horizon {ω : Ω} {u : ℝ≥0} (hu : u ≤ seedCapacityHorizon d S ω) : (u : ℝ) ≤ a ω (S ω) := by
  have h0 : 0 ≤ (d ω).a (S ω) := by
    rw [← (hown ω).a0]
    exact (hown ω).mono.monotoneOn ⟨le_rfl, (hown ω).pos.le⟩ ⟨(S ω).coe_nonneg, le_rfl⟩ (S ω).coe_nonneg
  have hh : (u : ℝ) ≤ (seedCapacityHorizon d S ω : ℝ) := hu
  rwa [seedCapacityHorizon, Real.coe_toNNReal _ h0, hda] at hh

/-- The mapped driver of the seeded data is the image driver read at the image clock. -/
theorem A_zero_eq {ω : Ω} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (S ω)) : (d ω).A 0 t = W' ω (a ω t) := by
  show frzA (d ω).W (d ω).W' (d ω).a (d ω).φ 0 t = _
  rw [(hown ω).frzA_zero ht, hdW', hda]

include hCc hCs hc hlb

/-- **The seeded capacity driver is the image driver** up to the capacity horizon: `W'(u) − W'(0)`. -/
theorem seedCapacityDriver_eq_W' {ω : Ω} {u : ℝ≥0} (hu : u ≤ seedCapacityHorizon d S ω) :
    seedCapacityDriver d S u ω = W' ω u - W' ω 0 := by
  obtain ⟨hτ, haτ⟩ := seedCapacityTime_spec hown hCc hCs hc hlb ω hu
  have hmem : ((seedCapacityTime d S u ω : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (S ω) :=
    ⟨(seedCapacityTime d S u ω).coe_nonneg, NNReal.coe_le_coe.2 hτ⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (S ω) := ⟨le_rfl, (S ω).coe_nonneg⟩
  rw [seedCapacityDriver, A_zero_eq hown hda hdW' hmem, A_zero_eq hown hda hdW' h0, ← hda ω, haτ, (hown ω).a0]

/-- **The capacity coordinate of a frozen-chart mark is the image mark** up to the capacity horizon:
`Ṽ_p(u) − W'(0)`. -/
theorem capForce_frzImg_eq_imgV (p : ℝ) {ω : Ω} {u : ℝ≥0} (hu : u ≤ seedCapacityHorizon d S ω) :
    capForce d S (fun ω => frzImg (d ω).W' (d ω).a p) u ω = imgV (W' ω) p u - W' ω 0 := by
  obtain ⟨hτ, haτ⟩ := seedCapacityTime_spec hown hCc hCs hc hlb ω hu
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (S ω) := ⟨le_rfl, (S ω).coe_nonneg⟩
  rw [capForce, A_zero_eq hown hda hdW' h0]
  show (QuantumZipper.fwdMap (d ω).W' ((d ω).a _) (p : ℂ)).re + (d ω).W' ((d ω).a _) - W' ω (a ω 0) = _
  rw [haτ, hdW', imgV, ← hda ω, (hown ω).a0]

end Coords

/-! ### The capacity Brownian motion of the large-curve direction -/

section Bridge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ}
  {φ : ℂ → ℂ} {rr : Fin n → ℝ} {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}
  {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {n' : ℕ} {d : Ω → SeedData n'} {A' : Ω → Set ℂ}

/-- **The clock facts of the seeded quadratic clock** from the frozen-curve hypotheses. -/
theorem seedClock_facts (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
    (hown : ∀ ω, OwnData (d ω).W (A' ω) (d ω).φ (S ω) (d ω).a (d ω).W') (hda : ∀ ω, (d ω).a = a ω)
    (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    (∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω)) ∧
      (∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω)) ∧
      (∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => seedQuadClock (seedCapacityCoeff d S) ω r) ∧
      ∀ ω (u : ℝ≥0), min (a₀ ^ 2) 1 * (u : ℝ) ≤ seedQuadClock (seedCapacityCoeff d S) ω u := by
  rw [seedQuadClock_eq_bmClk hown hda]
  exact ⟨hH.continuous_bmClk, hH.strictMono_bmClk, hH.measurable_bmClk hBm hBc hS, hH.le_bmClk⟩

/-- **PROVE-A1-FORCES's capacity Brownian input in the large-curve direction** (the premise `hBh` of
`isSeedSampleLaw_of_capacityBrownian`). The growing curve is ordinary `SLE_κ` (`W = √κB`) with the other curve frozen
and the (D9) hypotheses up to `S` (`FrzD10Hyp`); the seeded data `d` carry its image chain. Under
`Q = (M̃_S/M̃_0)·P` the frozen-curve line's capacity Brownian motion `B̂_u = Y_{C'⁻¹(u)}` is a Brownian motion of
A1-FAMILY's capacity-time filtration `seedFilt` and, up to the capacity horizon, the residual of the seeded capacity
driver against the capacity coordinates of the frozen-chart marks `pL`, `pR` (the marks of the frozen data sorted by
`e`, with their weights). -/
theorem seedCapacityBrownian_of_frzD10Hyp (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
    (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {NB : ℝ} (hBb : ∀ ω (t : ℝ≥0), t ≤ S ω → |B t ω| ≤ NB)
    (hown : ∀ ω, OwnData (d ω).W (A' ω) (d ω).φ (S ω) (d ω).a (d ω).W') (hda : ∀ ω, (d ω).a = a ω)
    (hdW' : ∀ ω, (d ω).W' = W' ω) {nL nR : ℕ} (e : Fin nL ⊕ Fin nR ≃ Option (Fin n))
    {pL : Fin nL → ℝ} {pR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hpL : ∀ i, pL i = markPos ζ₀ ζ (e (.inl i))) (hpR : ∀ j, pR j = markPos ζ₀ ζ (e (.inr j)))
    (hρL : ∀ i, ρL i = markWt κ rr (e (.inl i))) (hρR : ∀ j, ρR j = markWt κ rr (e (.inr j)))
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d S) ω))
    (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => seedQuadClock (seedCapacityCoeff d S) ω r) :
    SeedCapacityBrownian κ ρL ρR (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell)
      (seedFilt 𝓕 d S hCc hCm hmeas) (seedCapacityDriver d S)
      (fun i => capForce d S (fun ω => frzImg (d ω).W' (d ω).a (pL i)))
      (fun j => capForce d S (fun ω => frzImg (d ω).W' (d ω).a (pR j))) (seedCapacityHorizon d S)
      (fun u ω => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω) := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  obtain ⟨-, hCs, -, hlb⟩ := seedClock_facts hH hown hda hBm hBc hS
  refine ⟨?_, fun ω t ht => ?_⟩
  · rw [seedFilt_eq_timeChangeFilt hown hda hCc hCm hmeas hH.continuous_bmClk
      (fun ω => (hH.strictMono_bmClk ω).monotone) (hH.measurable_bmClk hBm hBc hS)]
    exact hH.isFilteredBrownianReal_bm hκ hB hBc hS hBb
  have hc : 0 < min (a₀ ^ 2) 1 := lt_min (pow_pos (hH.d9 ω).a0 2) one_pos
  have hta := coe_le_a_of_le_horizon hown hda ht
  have hsum := hH.sub_eq_bm_add_sum e hκ hta
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  -- the integrands agree on `[0, t]`
  have hgap (p : ℝ) {v : ℝ} (hv : v ∈ uIcc (0 : ℝ) t) :
      seedCapacityDriver d S v.toNNReal ω - capForce d S (fun ω => frzImg (d ω).W' (d ω).a p) v.toNNReal ω =
        W' ω v - imgV (W' ω) p v := by
    rw [uIcc_of_le t.coe_nonneg] at hv
    have hvt : v.toNNReal ≤ seedCapacityHorizon d S ω :=
      (Real.toNNReal_le_iff_le_coe.2 hv.2).trans ht
    rw [seedCapacityDriver_eq_W' hown hda hdW' hCc hCs hc hlb hvt,
      capForce_frzImg_eq_imgV hown hda hdW' hCc hCs hc hlb p hvt, Real.coe_toNNReal _ hv.1]
    ring
  have hL : ∀ i, ∫ v in (0 : ℝ)..t, ρL i / (seedCapacityDriver d S v.toNNReal ω -
      capForce d S (fun ω => frzImg (d ω).W' (d ω).a (pL i)) v.toNNReal ω) =
      ∫ v in (0 : ℝ)..t, markWt κ rr (e (.inl i)) / (W' ω v - imgV (W' ω) (markPos ζ₀ ζ (e (.inl i))) v) :=
    fun i => intervalIntegral.integral_congr fun v hv => by
      simp only [hgap (pL i) hv]; rw [hpL, hρL]
  have hR : ∀ j, ∫ v in (0 : ℝ)..t, ρR j / (seedCapacityDriver d S v.toNNReal ω -
      capForce d S (fun ω => frzImg (d ω).W' (d ω).a (pR j)) v.toNNReal ω) =
      ∫ v in (0 : ℝ)..t, markWt κ rr (e (.inr j)) / (W' ω v - imgV (W' ω) (markPos ζ₀ ζ (e (.inr j))) v) :=
    fun j => intervalIntegral.integral_congr fun v hv => by
      simp only [hgap (pR j) hv]; rw [hpR, hρR]
  rw [seedCapacityNoise, Finset.sum_congr rfl fun i _ => hL i, Finset.sum_congr rfl fun j _ => hR j,
    seedCapacityDriver_eq_W' hown hda hdW' hCc hCs hc hlb ht, eq_div_iff hs]
  linear_combination -hsum

/-- **A1-FAMILY's one-sample law in the large-curve direction** under `Q = (M̃_S/M̃_0)·P`: the image data equal, up
to the cap `Scap m` (the capacity horizon), the seeded capacity driver and the capacity coordinates of the frozen-chart
marks `pL`, `pR`, and the noise `N` the residual; the other caps are image capacities at own-time stopping times. All
clock, filtration, Brownian and adaptedness premises of `isSeedSampleLaw_of_capacityBrownian` are discharged from the
frozen-curve hypotheses `FrzD10Hyp`. -/
theorem isSeedSampleLaw_of_frzD10Hyp (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
    (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {NB : ℝ} (hBb : ∀ ω (t : ℝ≥0), t ≤ S ω → |B t ω| ≤ NB)
    (hown : ∀ ω, OwnData (d ω).W (A' ω) (d ω).φ (S ω) (d ω).a (d ω).W') (hda : ∀ ω, (d ω).a = a ω)
    (hdW' : ∀ ω, (d ω).W' = W' ω) {nL nR : ℕ} (e : Fin nL ⊕ Fin nR ≃ Option (Fin n))
    {pL : Fin nL → ℝ} {pR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hpL : ∀ i, pL i = markPos ζ₀ ζ (e (.inl i))) (hpR : ∀ j, pR j = markPos ζ₀ ζ (e (.inr j)))
    (hρL : ∀ i, ρL i = markWt κ rr (e (.inl i))) (hρR : ∀ j, ρR j = markWt κ rr (e (.inr j)))
    {Wi : ℝ≥0 → Ω → ℝ} {ζi : Ω → ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {N : ℝ≥0 → Ω → ℝ} {Scap : ℕ → Ω → ℝ≥0} {m : ℕ}
    (hSm : ∀ ω, Scap m ω = seedCapacityHorizon d S ω)
    (hW : ∀ ω t, t ≤ Scap m ω → Wi t ω = seedCapacityDriver d S t ω)
    (hVL : ∀ ω i t, t ≤ Scap m ω → VL i t ω = capForce d S (fun ω => frzImg (d ω).W' (d ω).a (pL i)) t ω)
    (hVR : ∀ ω j t, t ≤ Scap m ω → VR j t ω = capForce d S (fun ω => frzImg (d ω).W' (d ω).a (pR j)) t ω)
    (hN : ∀ ω t, t ≤ Scap m ω → N t ω = seedCapacityNoise κ ρL ρR (Wi · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) t)
    (hζ : ∀ ω, (Scap m ω : ℝ≥0∞) ≤ ζi ω)
    (Tk : ℕ → Ω → ℝ≥0) (hT : ∀ k, IsStoppingTime 𝓕 fun ω => (Tk k ω : WithTop ℝ≥0))
    (hcap₁ : ∀ k ω, Tk k ω ≤ S ω → (Scap k ω : ℝ) = (d ω).a (Tk k ω))
    (hcap₂ : ∀ k ω, S ω ≤ Tk k ω → Scap m ω ≤ Scap k ω) :
    IsSeedSampleLaw (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) Wi ζi VL VR N
      Scap m := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  obtain ⟨hCc, hCs, hmeas, hlb⟩ := seedClock_facts hH hown hda hBm hBc hS
  obtain ⟨c, hc, hlbc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ ω (u : ℝ≥0), c * (u : ℝ) ≤ seedQuadClock (seedCapacityCoeff d S) ω u := by
    rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω₀⟩⟩
    · exact ⟨1, one_pos, fun ω => isEmptyElim ω⟩
    · exact ⟨_, lt_min (pow_pos (hH.d9 ω₀).a0 2) one_pos, hlb⟩
  have h0 (ω : Ω) : (0 : ℝ) ∈ Icc (0 : ℝ) (S ω) := ⟨le_rfl, (S ω).coe_nonneg⟩
  have hmin (u : ℝ≥0) (ω : Ω) : ((min u (S ω) : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (S ω) :=
    ⟨(min u (S ω)).coe_nonneg, NNReal.coe_le_coe.2 (min_le_right _ _)⟩
  -- the starting value of the mapped driver is `𝓕 0`-measurable
  have hA00 : Measurable[𝓕 0] fun ω => (d ω).A 0 0 := by
    have e0 : (fun ω => (d ω).A 0 0) = fun ω => W' ω (a ω ((min 0 (S ω) : ℝ≥0) : ℝ)) := by
      funext ω
      rw [A_zero_eq hown hda hdW' (h0 ω), zero_min, NNReal.coe_zero]
    rw [e0]
    exact hH.measurable_W'_min hBm hBc hS 0
  -- the forces of the frozen-chart marks, as image marks of the frozen data
  have hX (p : ℝ) (hp : ∃ o, p = markPos ζ₀ ζ o) :
      IsStronglyProgressive 𝓕 fun u ω => frzImg (d ω).W' (d ω).a p ((min u (S ω) : ℝ≥0) : ℝ) - (d ω).A 0 0 := by
    obtain ⟨o, rfl⟩ := hp
    have he (ω : Ω) (t : ℝ) : frzImg (d ω).W' (d ω).a (markPos ζ₀ ζ o) t = imgV (W' ω) (markPos ζ₀ ζ o) (a ω t) := by
      rw [hdW', hda]
      rfl
    refine isStronglyProgressive_stopped_sub (f := fun ω => frzImg (d ω).W' (d ω).a (markPos ζ₀ ζ o)) ?_ ?_ _ hA00
    · exact fun ω => (hH.continuousOn_imgV_a ω o).congr fun t _ => he ω t
    · intro u
      have he' : (fun ω => frzImg (d ω).W' (d ω).a (markPos ζ₀ ζ o) ((min u (S ω) : ℝ≥0) : ℝ)) =
          fun ω => imgV (W' ω) (markPos ζ₀ ζ o) (a ω ((min u (S ω) : ℝ≥0) : ℝ)) := funext fun ω => he ω _
      rw [he']
      exact hH.measurable_imgV_min hBm hBc hS o u
  refine isSeedSampleLaw_of_capacityBrownian hown hCc (fun ω => (hCs ω).monotone) hmeas hCs hc hlbc
    (seedCapacityBrownian_of_frzD10Hyp hH hκ hB hBc hS hBb hown hda hdW' e hpL hpR hρL hρR hCc
      (fun ω => (hCs ω).monotone) hmeas) (fun ω => ?_) hS ?_ (fun i => hX (pL i) ⟨_, hpL i⟩)
    (fun j => hX (pR j) ⟨_, hpR j⟩) hSm hW hVL hVR hN hζ Tk hT hcap₁ hcap₂
  · exact (hH.continuous_bmY hBc ω).comp (continuous_invClockT hH.continuous_bmClk hH.strictMono_bmClk
      hH.bmClk_zero (lt_min (pow_pos (hH.d9 ω).a0 2) one_pos) hH.le_bmClk ω)
  · refine isStronglyProgressive_stopped_sub (f := fun ω => (d ω).A 0) (fun ω => (hown ω).continuousOn_frzA 0)
      (fun u => ?_) _ hA00
    have e1 : (fun ω => (d ω).A 0 ((min u (S ω) : ℝ≥0) : ℝ)) =
        fun ω => W' ω (a ω ((min u (S ω) : ℝ≥0) : ℝ)) := by
      funext ω
      rw [A_zero_eq hown hda hdW' (hmin u ω)]
    rw [e1]
    exact hH.measurable_W'_min hBm hBc hS u

end Bridge

end InteractingSLE.ZhanGT4.A1LargeDens
