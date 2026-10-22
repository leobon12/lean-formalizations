import HigherDimLQGMetric.DGZ.NondegFinite

/-! Connectedness of the cubical shell in dimension at least two. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

private def nd_toSup (x : Rd d) : PiLp (⊤ : ENNReal) (fun _ : Fin d => ℝ) :=
  WithLp.toLp _ x.ofLp

private def nd_fromSup (x : PiLp (⊤ : ENNReal) (fun _ : Fin d => ℝ)) : Rd d :=
  WithLp.toLp _ x.ofLp

private theorem nd_toSup_norm (x : Rd d) :
    ‖nd_toSup x‖ = ⨆ i : Fin d, |x i| := by
  simp [nd_toSup, PiLp.norm_eq_ciSup, Real.norm_eq_abs]

private theorem nd_fromSup_toSup (x : Rd d) : nd_fromSup (nd_toSup x) = x := rfl

private theorem nd_toSup_fromSup
    (x : PiLp (⊤ : ENNReal) (fun _ : Fin d => ℝ)) : nd_toSup (nd_fromSup x) = x := rfl

private theorem nd_lsph_eq_supSphere (hd : 0 < d) (r : ℝ) (x : Rd d) :
    x ∈ lsph (0 : Rd d) r ↔ ‖nd_toSup x‖ = r := by
  have hfin : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  letI := hfin
  rw [nd_toSup_norm]
  constructor
  · intro hx
    have hall : ∀ i : Fin d, |x i| ≤ r := by
      intro i
      simpa [lsph, cbox] using hx.1 i
    have hnall : ¬ ∀ i : Fin d, |x i| < r := by
      simpa [lsph, obox] using hx.2
    have hle : (⨆ i : Fin d, |x i|) ≤ r := ciSup_le hall
    have ⟨i, hi⟩ : ∃ i : Fin d, r ≤ |x i| := by
      simpa only [not_forall, not_lt] using hnall
    exact le_antisymm hle (hi.trans
      (le_ciSup (Set.finite_range (fun k : Fin d => |x k|)).bddAbove i))
  · intro hnorm
    have hall : ∀ i : Fin d, |x i| ≤ r := by
      intro i
      rw [← hnorm]
      exact le_ciSup (Set.finite_range (fun k : Fin d => |x k|)).bddAbove i
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin d => |x i|)
    refine ⟨?_, ?_⟩
    · intro k
      simpa [cbox] using hall k
    · intro hbox
      have hlt : |x i| < r := by simpa [obox] using hbox i
      rw [hi, hnorm] at hlt
      exact (lt_irrefl r) hlt

theorem nd_isConnected_lsph (hd : 2 ≤ d) {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (lsph (0 : Rd d) r) := by
  have hrank : 1 < Module.rank ℝ (PiLp (⊤ : ENNReal) (fun _ : Fin d => ℝ)) := by
    rw [← Module.finrank_eq_rank,
      Module.finrank_eq_card_basis (PiLp.basisFun (⊤ : ENNReal) ℝ (Fin d))]
    simpa using (show 1 < d by omega)
  have hcont : Continuous (nd_fromSup (d := d)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
      (PiLp.continuous_ofLp (⊤ : ENNReal) (fun _ : Fin d => ℝ))
  have himg : nd_fromSup '' Metric.sphere
      (0 : PiLp (⊤ : ENNReal) (fun _ : Fin d => ℝ)) r = lsph (0 : Rd d) r := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      apply (nd_lsph_eq_supSphere (by omega : 0 < d) r _).2
      rw [nd_toSup_fromSup]
      simpa only [Metric.mem_sphere, dist_zero_right] using hv
    · intro hx
      refine ⟨nd_toSup x, ?_, nd_fromSup_toSup x⟩
      simpa only [Metric.mem_sphere, dist_zero_right] using
        (nd_lsph_eq_supSphere (by omega : 0 < d) r x).1 hx
  rw [← himg]
  exact (isConnected_sphere hrank 0 hr).image _ hcont.continuousOn

end HigherDimLQGMetric.DGZ
