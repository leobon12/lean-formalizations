/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmSlit
import InteractingSLE.Spec.Supplement.GW2RootB23Scale
import InteractingSLE.Spec.Supplement.GW2ScheduleL25
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Restart.R1Flow
import InteractingSLE.Foundations.Loewner.YuanCorollary13
import InteractingSLE.Foundations.Loewner.YuanCorollary13Tip
import InteractingSLE.Foundations.SLE.All
import InteractingSLE.WangWu.Prop418Side

/-!
# Mapping out a prefix of a generating trace, rescaled (tools for J32's tip)

Packet PROVE-GW2-GEOM2. J32's tip is the trace of the joint driver `u ↦ k (V(A₀ + u/k²) − V(A₀))`, where `V` is
the driver of the relative capacity tip and `A₀` the capacity at the root's entry. This file gives the
deterministic Loewner facts used to read that tip:

* `loewnerTrace_mem_Hbar`; **`notMem_diff_of_shiftTip_notMem_H`** (if the tip of the chain mapped out at time
  `a` is real at `u`, the original trace at `a + u` is not an interior point of `ℍ \ K_a`, via [Yua22]
  Corollary 1.3 and the boundary fibres of `F̄_a`); `mem_diff_of_shiftTip_mem_H` (the easy converse);
* `volume_loewnerTrace_notMem_H` (Lemma 2.5 for a global Loewner trace);
* `endVal_eq_of_continuousAt` (the dyadic left-limit reader returns the value at a continuity point);
* **`exists_jointShiftTip`**: for a driver `V` generating `η` on `[0, B)`, a level `A₀ < σ < B` and `k > 0`,
  there is a continuous `ψ` such that the trace (`LP.traceAt`) of any driver equal to `k (V(A₀ + ·/k²) − V(A₀))`
  on `[0, u]` is `k ψ(u/k²)` whenever `A₀ + u/k² ≤ σ`, and `ψ τ ∉ ℍ` forces `η(A₀ + τ) ∉ ℍ \ K_{A₀}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

/-! ### Mapping out a prefix of a global trace -/

section Global

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- The values of a Loewner trace lie in `ℍ̄`. -/
theorem loewnerTrace_mem_Hbar (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) : η t ∈ Hbar :=
  YuanCorollary13.mem_Hbar_of_tendsto hW hW0 ht (hη.tendsto_fwdMapInv_tip hW hW0 ht)

/-- **Mapping out a prefix, the boundary direction**: if the tip of the chain mapped out at time `a` is real at
time `u`, then the original trace at `a + u` is not an interior point of `ℍ \ K_a`. -/
theorem notMem_diff_of_shiftTip_notMem_H (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (h : loewnerTip (shiftDrive W a) u ∉ H) : η (a + u) ∉ H \ fwdHull W a := by
  obtain ⟨hψ, hF⟩ := hη.isLoewnerTrace_shift_and_extendFrom hW hW0 ha
  have hbar := loewnerTrace_mem_Hbar hψ (QuantumZipper.RS.continuous_shiftDrive hW a)
    (QuantumZipper.RS.shiftDrive_zero W a) hu
  have him : (loewnerTip (shiftDrive W a) u).im = 0 := le_antisymm (not_lt.1 h) hbar
  obtain ⟨-, -, -, hnot⟩ := hη.fiber_hyps hW hW0 ha
  rw [← hF u hu]
  intro hmem
  exact hnot _ him ⟨fwdMap W a (extendFrom H (fwdMapInv W a) (loewnerTip (shiftDrive W a) u)),
    QuantumZipper.FwdHolo.mapsTo_fwdMap hW ha hmem, WangWu.extendFrom_fwdMap hW hW0 ha hmem⟩

/-- **Mapping out a prefix, the interior direction**: if the tip of the chain mapped out at time `a` is in `ℍ` at
time `u`, then the original trace at `a + u` is in `ℍ \ K_a`. -/
theorem mem_diff_of_shiftTip_mem_H (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) (h : loewnerTip (shiftDrive W a) u ∈ H) :
    η (a + u) ∈ H \ fwdHull W a := by
  obtain ⟨-, hF⟩ := hη.isLoewnerTrace_shift_and_extendFrom hW hW0 ha
  rw [← hF u hu, WangWu.extendFrom_fwdMapInv_eq hW hW0 ha h]
  exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ha h

/-- **Lemma 2.5 for a global Loewner trace**: it spends zero Lebesgue time off `ℍ`. -/
theorem volume_loewnerTrace_notMem_H (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) : volume {t : ℝ | 0 ≤ t ∧ η t ∉ H} = 0 := by
  refine measure_mono_null (t := ⋃ n : ℕ, {t | t ∈ Ico 0 (n : ℝ) ∧ η t ∉ H}) ?_
    (measure_iUnion_null fun n => ?_)
  · rintro t ⟨ht, htH⟩
    obtain ⟨n, hn⟩ := exists_nat_gt t
    exact mem_iUnion.2 ⟨n, ⟨ht, hn⟩, htH⟩
  · have hL : IsLoewnerTraceLT W n η :=
      ⟨hη.1, hη.2.1.mono Ico_subset_Ici_self, fun t ht _ => hη.2.2 t ht⟩
    exact hL.volume_setOf_notMem_H hW hW0

/-- The shifted tips of a global trace have null boundary time. -/
theorem volume_shiftTip_notMem_H (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {a : ℝ} (ha : 0 ≤ a) : volume {t : ℝ | 0 ≤ t ∧ loewnerTip (shiftDrive W a) t ∉ H} = 0 :=
  volume_loewnerTrace_notMem_H (hη.isLoewnerTrace_shift hW hW0 ha)
    (QuantumZipper.RS.continuous_shiftDrive hW a) (QuantumZipper.RS.shiftDrive_zero W a)

end Global

/-! ### The dyadic left-limit reader -/

/-- The dyadic left-limit reader returns the value at a continuity point. -/
theorem endVal_eq_of_continuousAt {f : ℝ≥0 → ℂ} {u : ℝ≥0} (hf : ContinuousAt f u) :
    Restart.endVal ((u : ℝ≥0∞), f) = f u := by
  unfold Restart.endVal
  by_cases hu : u = 0
  · subst hu
    simp
  · have hne : ((u : ℝ≥0∞)) ≠ 0 := by exact_mod_cast hu
    rw [ite_eq_right hne, ENNReal.toNNReal_coe]
    exact (hf.tendsto.comp (LP.tendsto_dyadicBelow u)).limUnder_eq

/-- The `⊤`-lifetime driving trace of a driver is its `LP.traceAt` reader. -/
theorem drivingTrace_top_snd (J : ℝ≥0 → ℝ) :
    (LP.drivingTrace (⊤, J)).2 = fun t => LP.traceAt t J := by
  funext t
  show (if (t : ℝ≥0∞) < (⊤ : ℝ≥0∞) then LP.traceAt t J else LP.endpointTrace ⊤ J) = LP.traceAt t J
  exact ite_eq_left ENNReal.coe_lt_top

/-! ### The joint trace: a prefix mapped out and rescaled -/

section Joint

variable {V : ℝ≥0 → ℝ} {B : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- The driver frozen at `σ`, on the real line. -/
def frozenReal (V : ℝ≥0 → ℝ) (σ : ℝ≥0) : ℝ → ℝ := fun r => V (min r.toNNReal σ)

/-- The tip, at real time, of the chain of the frozen driver mapped out at `A₀`. -/
def jointShiftTip (V : ℝ≥0 → ℝ) (σ A₀ : ℝ≥0) : ℝ → ℂ :=
  loewnerTip (shiftDrive (frozenReal V σ) A₀)

theorem continuous_frozenReal {σ : ℝ≥0} (hV : ContinuousOn V (Icc 0 σ)) :
    Continuous (frozenReal V σ) :=
  hV.comp_continuous ((continuous_real_toNNReal).min continuous_const)
    fun _ => ⟨zero_le, min_le_right _ _⟩

/-- **The joint trace.** For a driver `V` generating `η` before `B`, levels `A₀ < σ < B` and `k > 0`: the tips `ψ`
of the frozen chain mapped out at `A₀` are continuous; the trace of any driver equal to `k (V(A₀ + ·/k²) − V(A₀))`
on `[0, u]` is `k ψ(u/k²)` when `A₀ + u/k² ≤ σ`; and if `ψ τ ∉ ℍ` then `η(A₀ + τ)` is not an interior point of
`ℍ \ K_{A₀}`. -/
theorem exists_jointShiftTip (hη : IsGeneratingTrace V B η)
    (hV : ContinuousOn V {t | (t : ℝ≥0∞) < B}) (hV0 : V 0 = 0) {σ A₀ k : ℝ≥0}
    (hσB : (σ : ℝ≥0∞) < B) (hA₀ : A₀ < σ) (hk : 0 < k) :
    Continuous (fun τ : ℝ≥0 => jointShiftTip V σ A₀ τ) ∧
      (∀ (Jt : ℝ≥0 → ℝ) (u : ℝ≥0), A₀ + u / k ^ 2 ≤ σ →
        (∀ r ≤ u, Jt r = k * (V (A₀ + r / k ^ 2) - V A₀)) →
          LP.traceAt u Jt = k * jointShiftTip V σ A₀ ((u / k ^ 2 : ℝ≥0) : ℝ)) ∧
      (∀ τ : ℝ≥0, A₀ + τ ≤ σ → jointShiftTip V σ A₀ τ ∉ H →
        η (A₀ + τ) ∉ H \ fwdHull (fun r : ℝ => V r.toNNReal) A₀) := by
  have hVσ : ContinuousOn V (Icc 0 σ) := hV.mono fun t ht =>
    (ENNReal.coe_le_coe.2 ht.2).trans_lt hσB
  obtain ⟨η', hη', hηη'⟩ := exists_isGeneratingTrace_frozen hVσ hV0 (hη.mono_horizon hσB.le)
  have hWc := continuous_frozenReal hVσ
  have hW0 : frozenReal V σ 0 = 0 := by simp [frozenReal, hV0]
  have hL : IsLoewnerTrace (frozenReal V σ) (fun r : ℝ => η' r.toNNReal) :=
    isLoewnerTrace_of_isGeneratingTrace hη'
  have hS := hL.isLoewnerTrace_shift hWc hW0 A₀.coe_nonneg
  -- the shifted chain as a generating trace of an `ℝ≥0` driver
  set D : ℝ≥0 → ℝ := fun u => V (min (A₀ + u) σ) - V (min A₀ σ) with hD
  have hDc : Continuous D := by
    refine (hVσ.comp_continuous ((continuous_const.add continuous_id).min continuous_const)
      fun _ => ⟨zero_le, min_le_right _ _⟩).sub continuous_const
  have hS' : IsLoewnerTrace (fun s : ℝ => D s.toNNReal) (jointShiftTip V σ A₀) := by
    refine (isLoewnerTrace_congr_drive fun t ht => ?_).1 hS
    have h1 : ((A₀ : ℝ) + t).toNNReal = A₀ + t.toNNReal := by
      have : (A₀ : ℝ) + t = ((A₀ + t.toNNReal : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_add, Real.coe_toNNReal _ ht]
      rw [this, Real.toNNReal_coe]
    show V (min ((A₀ : ℝ) + t).toNNReal σ) - V (min (A₀ : ℝ).toNNReal σ) =
      V (min (A₀ + t.toNNReal) σ) - V (min A₀ σ)
    rw [h1, Real.toNNReal_coe]
  have hgen : IsGeneratingTrace D ⊤ (fun t : ℝ≥0 => jointShiftTip V σ A₀ t) :=
    IsLoewnerTrace.isGeneratingTrace hS'
  have hscale := RootB23.isGeneratingTrace_scale hgen hk
  have htop : (((k ^ 2 : ℝ≥0) : ℝ≥0∞) * ⊤) = ⊤ :=
    ENNReal.mul_top (by exact_mod_cast (pow_ne_zero 2 hk.ne'))
  rw [htop] at hscale
  have hψc : Continuous (fun τ : ℝ≥0 => jointShiftTip V σ A₀ τ) :=
    continuousOn_univ.1 (hgen.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  refine ⟨hψc, fun Jt u hu hJt => ?_, fun τ hτ hψ => ?_⟩
  · -- the trace of the joint driver
    have hcong : ∀ r ≤ u, Jt r = (fun u => (k : ℝ) * D (u / k ^ 2)) r := by
      intro r hr
      have hr' : A₀ + r / k ^ 2 ≤ σ :=
        le_trans ((add_le_add_iff_left A₀).2 (div_le_div_of_nonneg_right hr (zero_le))) hu
      rw [hJt r hr]
      simp only [hD, min_eq_left hr', min_eq_left hA₀.le]
    rw [LP.traceAt_congr hcong]
    exact LP.traceAt_eq_of_isGeneratingTrace hscale
      ((continuous_const.mul (hDc.comp (continuous_id.div_const _))).continuousOn)
      (by simp [hD]) ENNReal.coe_lt_top
  · -- the boundary direction
    have h := notMem_diff_of_shiftTip_notMem_H hL hWc hW0 A₀.coe_nonneg τ.coe_nonneg hψ
    have hval : η' ((A₀ : ℝ) + τ).toNNReal = η (A₀ + τ) := by
      rw [← NNReal.coe_add, Real.toNNReal_coe]
      exact hηη' _ hτ
    have hK : fwdHull (frozenReal V σ) A₀ = fwdHull (fun r : ℝ => V r.toNNReal) A₀ := by
      refine InteractingSLE.fwdHull_eq_of_eqOn A₀.coe_nonneg (t₂ := σ)
        (NNReal.coe_lt_coe.2 hA₀) fun r hr => ?_
      show V (min r.toNNReal σ) = V r.toNNReal
      rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
    rwa [hval, hK] at h

end Joint

end InteractingSLE.Theorem14.GW2TipSystem.Gm
