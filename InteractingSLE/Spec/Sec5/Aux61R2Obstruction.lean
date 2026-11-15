/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61WinFibreRef

/-!
# Why `Aux61Win.RestartFibre` cannot carry the window event

Packet PROVE-AUX61-R2. PROVE-AUX61-WIN's fibre (`Aux61Win.RestartFibre`) carries a fixed **odd** smooth cutoff `Fq` of
`q` on an open set `Nq` containing every pre-contact hull (`IsCutoffOn Fq q Nq O₀`, `buffer ⊆ Nq`). An odd continuous
function vanishes on `ℝ`; so if `q` has a nonzero boundary limit `c` at a real point `y`, then `Nq ∩ ℍ` does not
accumulate at `y`, the pre-contact hulls stay away from `y`, and the fibre's path never reaches `y` at its first real
contact.

In the window fibres of Aux. lemma 64, `q = M − u₀` is the actual chart mean minus the basic mean `−λ | λ`
(forced by the kernel at time `0`), and on the comparison interval `I` the actual mean has the constant boundary value
`b` (Astra's follow-up 4, (1.2): `b > λ + πχ`), so `q → b − λ ≠ 0` (on the negative side `b + λ ≠ 0`) at every
point of `I`. Hence in every such fibre the path almost surely does not end in `I`, the sets `L i` of a fibre cover
are null for the fibres' laws, and `Aux61Win.HasFibreCover` for the window event holds only if the event is already
null. The corrected fibre `Aux61R2.RefFibre` (`Aux61R2Fibre`) uses the reference word's mean as its base, so that `q`
vanishes on `I` as well.

* `IsCutoffOn.notMem_closure_of_tendsto`: the deterministic core;
* `WinFibre.ae_notMem_closure_hulls`: the pre-contact hulls of a fibre stay away from `y`;
* **`WinFibre.Comparison.Clock.ae_ne_of_tendsto`**: the fibre's path almost surely does not reach `y` at a time
  `v ≤ e` before which it stayed in `ℍ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE.Sec5.Aux61R2

open QuantumZipper (H fwdHull)
open Restart.FlowStopIdentCMI (CMCut)
open Aux61Win (IsCutoffOn RestartFibre)

universe u

/-- **An odd cutoff cannot follow a nonzero boundary limit**: if `F` is a cutoff of `q` on `N` and `q → c ≠ 0` at the
real point `y` (from `ℍ`), then `y` is not in the closure of `N ∩ ℍ`. -/
theorem IsCutoffOn.notMem_closure_of_tendsto {F : CMCut} {q : ℂ → ℝ} {N : Set ℂ} {O₀ : Set ℝ}
    (hF : IsCutoffOn F q N O₀) {y : ℝ} {c : ℝ} (hc : c ≠ 0) (hq : Tendsto q (𝓝[H] (y : ℂ)) (𝓝 c)) :
    (y : ℂ) ∉ closure (N ∩ H) := by
  intro hy
  have : (𝓝[N ∩ H] (y : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hy
  have h0 : F.f (y : ℂ) = 0 := by
    have h := F.odd (y : ℂ)
    rw [Complex.conj_ofReal] at h
    linarith
  have h1 : Tendsto F.f (𝓝[N ∩ H] (y : ℂ)) (𝓝 0) :=
    h0 ▸ (F.smooth.continuous.tendsto _).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto q (𝓝[N ∩ H] (y : ℂ)) (𝓝 c) := hq.mono_left (nhdsWithin_mono _ inter_subset_right)
  have h3 : Tendsto F.f (𝓝[N ∩ H] (y : ℂ)) (𝓝 c) :=
    h2.congr' (eventually_nhdsWithin_of_forall fun z hz => (hF.eq z hz.1 hz.2).symm)
  exact hc (tendsto_nhds_unique h3 h1)

namespace WinFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : RestartFibre S)

/-- **The pre-contact hulls of a fibre stay away from a real point where `q` has a nonzero limit.** -/
theorem ae_notMem_closure_hulls {y : ℝ} {c : ℝ} (hc : c ≠ 0) (hq : Tendsto D.q (𝓝[H] (y : ℂ)) (𝓝 c)) :
    ∀ᵐ ω ∂D.P, (y : ℂ) ∉ closure (⋃ t : ℝ≥0, ⋃ (_ : (t : ℝ≥0∞) < D.e ω), fwdHull (Ito.rpath (D.W · ω)) t) := by
  filter_upwards [D.hull_buffer] with ω hb hy
  refine IsCutoffOn.notMem_closure_of_tendsto D.cut hc hq (closure_mono (fun z hz => ?_) hy)
  simp only [mem_iUnion] at hz
  obtain ⟨t, ht, hzK⟩ := hz
  exact ⟨D.buffer_sub (hb t ht (subset_closure hzK)), hzK.1⟩

variable {D}

/-- A point of a generating trace in `ℍ` lies in the hull at its time. -/
theorem mem_fwdHull_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T) (hH : η s ∈ H) : η s ∈ fwdHull (fun r : ℝ => w r.toNNReal) s := by
  by_contra hK
  obtain ⟨z, -, hz⟩ := (hη.2.2 s hs).1
  have hmem : η s ∈ H \ fwdHull (fun r : ℝ => w r.toNNReal) s := ⟨hH, hK⟩
  rw [← hz] at hmem
  exact (connectedComponentIn_subset _ _ hmem).2 ⟨s, ⟨zero_le, le_rfl⟩, rfl⟩

/-- **The fibre's path does not reach `y` at its first real contact** (`q → c ≠ 0` at `y`): almost surely, for every
`0 < v ≤ e` such that the path stayed in `ℍ` on `(0, v)`, its point at `v` is not `y`. -/
theorem Comparison.Clock.ae_ne_of_tendsto {C : D.Comparison} (K : C.Clock) {y : ℝ} {c : ℝ} (hc : c ≠ 0)
    (hq : Tendsto D.q (𝓝[H] (y : ℂ)) (𝓝 c)) :
    ∀ᵐ ω ∂D.P, ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) ≤ D.e ω → (∀ s : ℝ≥0, 0 < s → s < v → K.Γ ω s ∈ H) →
      K.Γ ω v ≠ (y : ℂ) := by
  filter_upwards [ae_notMem_closure_hulls D hc hq, C.tilt_equivalent.2.ae_le K.trace] with ω hcl htr v hv hve hH hy
  have htr' : IsGeneratingTrace (D.W · ω) (D.e ω) (K.Γ ω) := by simpa only [sub_zero] using htr
  apply hcl
  rw [← hy]
  -- the path at `v` is a limit of points of the earlier hulls
  have hcont : Tendsto (K.Γ ω) (𝓝[<] v) (𝓝 (K.Γ ω v)) :=
    ((htr'.2.1 v hve).tendsto).mono_left (nhdsWithin_mono _ fun s hs => (ENNReal.coe_le_coe.2 (le_of_lt hs)).trans hve)
  have : (𝓝[<] v).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hv⟩
  refine mem_closure_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsLT hv] with s hs
  have hse : (s : ℝ≥0∞) < D.e ω := (ENNReal.coe_lt_coe.2 hs.2).trans_le hve
  simp only [mem_iUnion]
  exact ⟨s, hse, mem_fwdHull_of_isGeneratingTrace htr' hse (hH s hs.1 hs.2)⟩

end WinFibre

end InteractingSLE.Sec5.Aux61R2
