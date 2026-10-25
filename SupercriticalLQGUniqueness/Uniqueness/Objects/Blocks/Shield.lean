import LQGMetric.Topo.Disconnect
import Mathlib




 




















set_option autoImplicit false

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Blocks

 
theorem mem_range_truncateOfLE {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) {w : X} (hw : w ∈ range (γ.truncateOfLE h)) :
    ∃ τ ∈ Icc t₀ t₁, γ.extend τ = w := by
  obtain ⟨σ, rfl⟩ := hw
  exact ⟨min (max (σ : ℝ) t₀) t₁, ⟨le_min (le_max_right _ _) h, min_le_right _ _⟩, rfl⟩

 
theorem shield_hits {z x y : ℂ} {t : ℝ} (ht : 0 < t) {T : Set ℂ} (hT : IsClosed T)
    (hTA : T ⊆ {w | t < dist w z ∧ dist w z < 2 * t})
    (hdis : LQGMetric.Disconnects T (sphere z t) (sphere z (2 * t)))
    (γ : Path x y) (hx : x ∈ closedBall z t) (hy : y ∈ closedBall z t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hfar : 3 * t ≤ dist (γ.extend t₀) z) :
    ∃ τa τb : ℝ, 0 ≤ τa ∧ τa < t₀ ∧ t₀ < τb ∧ τb ≤ 1 ∧
      γ.extend τa ∈ T ∧ γ.extend τb ∈ T ∧
      (∀ s ∈ Icc 0 τa, dist (γ.extend s) z < 2 * t) ∧
      (∀ s ∈ Icc τb 1, dist (γ.extend s) z < 2 * t) ∧
      ∃ c d : ℝ, τa ≤ c ∧ c < d ∧ d ≤ t₀ ∧
        dist (γ.extend c) z = 2 * t ∧ dist (γ.extend d) z = 3 * t ∧
        ∀ s ∈ Icc c d, 2 * t ≤ dist (γ.extend s) z ∧ dist (γ.extend s) z ≤ 3 * t := by
  have hgc : Continuous γ.extend := γ.continuous_extend
  have hdis' := LQGMetric.Disconnects.closedBall_compl_ball (by linarith : t ≤ 2 * t) hdis
  have hT2 : ∀ w ∈ T, dist w z < 2 * t := fun w hw => (hTA hw).2
  
  have hit_fwd : ∀ s, 0 ≤ s → 2 * t ≤ dist (γ.extend s) z → ∃ τ ∈ Icc 0 s, γ.extend τ ∈ T := by
    intro s hs hfs
    obtain ⟨w, hw, hwT⟩ := hdis' (γ.extend 0) (γ.extend s) (γ.truncateOfLE hs)
      (by rw [Path.extend_zero]; exact hx) (by simpa [mem_ball, not_lt] using hfs)
    obtain ⟨τ, hτ, rfl⟩ := mem_range_truncateOfLE γ hs hw
    exact ⟨τ, hτ, hwT⟩
  
  have hit_bwd : ∀ s, s ≤ 1 → 2 * t ≤ dist (γ.extend s) z → ∃ τ ∈ Icc s 1, γ.extend τ ∈ T := by
    intro s hs hfs
    obtain ⟨w, hw, hwT⟩ := hdis' (γ.extend 1) (γ.extend s) (γ.truncateOfLE hs).symm
      (by rw [Path.extend_one]; exact hy) (by simpa [mem_ball, not_lt] using hfs)
    rw [Path.symm_range] at hw
    obtain ⟨τ, hτ, rfl⟩ := mem_range_truncateOfLE γ hs hw
    exact ⟨τ, hτ, hwT⟩
  have hft₀ : 2 * t ≤ dist (γ.extend t₀) z := by linarith
  
  set Hs : Set ℝ := Icc 0 t₀ ∩ γ.extend ⁻¹' T with hHs
  have hHs_closed : IsClosed Hs := isClosed_Icc.inter (hT.preimage hgc)
  have hHs_ne : Hs.Nonempty := by
    obtain ⟨τ, hτ, hτT⟩ := hit_fwd t₀ ht₀.1 hft₀
    exact ⟨τ, hτ, hτT⟩
  have hHs_bdd : BddBelow Hs := ⟨0, fun s hs => hs.1.1⟩
  set τa := sInf Hs with hτa
  have hτa_mem : τa ∈ Hs := hHs_closed.csInf_mem hHs_ne hHs_bdd
  have hτa_le : ∀ s ∈ Hs, τa ≤ s := fun s hs => csInf_le hHs_bdd hs
  have hpre : ∀ s ∈ Icc 0 τa, dist (γ.extend s) z < 2 * t := by
    intro s hs
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨τ, hτ, hτT⟩ := hit_fwd s hs.1 hcon
    have hτHs : τ ∈ Hs := ⟨⟨hτ.1, hτ.2.trans (hs.2.trans hτa_mem.1.2)⟩, hτT⟩
    have hsτa : s = τa := le_antisymm hs.2 ((hτa_le τ hτHs).trans hτ.2)
    have h2 := hT2 _ hτa_mem.2
    rw [← hsτa] at h2
    linarith
  have hτa_lt : τa < t₀ := by
    rcases lt_or_eq_of_le hτa_mem.1.2 with h | h
    · exact h
    · exfalso
      have h2 := hT2 _ hτa_mem.2
      rw [h] at h2
      linarith
  
  set Ks : Set ℝ := Icc t₀ 1 ∩ γ.extend ⁻¹' T with hKs
  have hKs_closed : IsClosed Ks := isClosed_Icc.inter (hT.preimage hgc)
  have hKs_ne : Ks.Nonempty := by
    obtain ⟨τ, hτ, hτT⟩ := hit_bwd t₀ ht₀.2 hft₀
    exact ⟨τ, hτ, hτT⟩
  have hKs_bdd : BddAbove Ks := ⟨1, fun s hs => hs.1.2⟩
  set τb := sSup Ks with hτb
  have hτb_mem : τb ∈ Ks := hKs_closed.csSup_mem hKs_ne hKs_bdd
  have hτb_ge : ∀ s ∈ Ks, s ≤ τb := fun s hs => le_csSup hKs_bdd hs
  have hpost : ∀ s ∈ Icc τb 1, dist (γ.extend s) z < 2 * t := by
    intro s hs
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨τ, hτ, hτT⟩ := hit_bwd s hs.2 hcon
    have hτKs : τ ∈ Ks := ⟨⟨hτb_mem.1.1.trans (hs.1.trans hτ.1), hτ.2⟩, hτT⟩
    have hsτb : s = τb := le_antisymm (hτ.1.trans (hτb_ge τ hτKs)) hs.1
    have h2 := hT2 _ hτb_mem.2
    rw [← hsτb] at h2
    linarith
  have hτb_gt : t₀ < τb := by
    rcases lt_or_eq_of_le hτb_mem.1.1 with h | h
    · exact h
    · exfalso
      have h2 := hT2 _ hτb_mem.2
      rw [← h] at h2
      linarith
  
  have hfc : Continuous fun s => dist (γ.extend s) z := hgc.dist continuous_const
  have hfτa : dist (γ.extend τa) z < 2 * t := hpre τa ⟨hτa_mem.1.1, le_rfl⟩
  set Ds : Set ℝ := Icc τa t₀ ∩ {s | 3 * t ≤ dist (γ.extend s) z} with hDs
  have hDs_closed : IsClosed Ds := isClosed_Icc.inter (isClosed_le continuous_const hfc)
  have hDs_ne : Ds.Nonempty := ⟨t₀, ⟨hτa_lt.le, le_rfl⟩, hfar⟩
  have hDs_bdd : BddBelow Ds := ⟨τa, fun s hs => hs.1.1⟩
  set d := sInf Ds with hd
  have hd_mem : d ∈ Ds := hDs_closed.csInf_mem hDs_ne hDs_bdd
  have hd_le : ∀ s ∈ Ds, d ≤ s := fun s hs => csInf_le hDs_bdd hs
  have hd3 : 3 * t ≤ dist (γ.extend d) z := hd_mem.2
  have hτa_lt_d : τa < d := by
    rcases lt_or_eq_of_le hd_mem.1.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hd3
      linarith
  have hfd : dist (γ.extend d) z = 3 * t := by
    rcases lt_or_eq_of_le hd3 with h | h
    · exfalso
      obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hτa_lt_d.le hfc.continuousOn
        (⟨by linarith, h.le⟩ : 3 * t ∈ Icc (dist (γ.extend τa) z) (dist (γ.extend d) z))
      have hfs' : dist (γ.extend s) z = 3 * t := hfs
      have hsDs : s ∈ Ds := ⟨⟨hs.1, hs.2.trans hd_mem.1.2⟩, hfs'.ge⟩
      have hsd : s = d := le_antisymm hs.2 (hd_le s hsDs)
      rw [hsd] at hfs'
      linarith
    · exact h.symm
  have hbelow3 : ∀ s ∈ Ico τa d, dist (γ.extend s) z < 3 * t := by
    intro s hs
    by_contra hcon
    rw [not_lt] at hcon
    have := hd_le s ⟨⟨hs.1, hs.2.le.trans hd_mem.1.2⟩, hcon⟩
    linarith [hs.2]
  set Cs : Set ℝ := Icc τa d ∩ {s | dist (γ.extend s) z ≤ 2 * t} with hCs
  have hCs_closed : IsClosed Cs := isClosed_Icc.inter (isClosed_le hfc continuous_const)
  have hCs_ne : Cs.Nonempty := ⟨τa, ⟨le_rfl, hτa_lt_d.le⟩, hfτa.le⟩
  have hCs_bdd : BddAbove Cs := ⟨d, fun s hs => hs.1.2⟩
  set c := sSup Cs with hc
  have hc_mem : c ∈ Cs := hCs_closed.csSup_mem hCs_ne hCs_bdd
  have hc_ge : ∀ s ∈ Cs, s ≤ c := fun s hs => le_csSup hCs_bdd hs
  have hc2 : dist (γ.extend c) z ≤ 2 * t := hc_mem.2
  have hc_lt_d : c < d := by
    rcases lt_or_eq_of_le hc_mem.1.2 with h | h
    · exact h
    · exfalso
      rw [h, hfd] at hc2
      linarith
  have hfc2 : dist (γ.extend c) z = 2 * t := by
    rcases lt_or_eq_of_le hc2 with h | h
    · exfalso
      obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hc_lt_d.le hfc.continuousOn
        (⟨h.le, by rw [hfd]; linarith⟩ : 2 * t ∈ Icc (dist (γ.extend c) z) (dist (γ.extend d) z))
      have hfs' : dist (γ.extend s) z = 2 * t := hfs
      have hsCs : s ∈ Cs := ⟨⟨hc_mem.1.1.trans hs.1, hs.2⟩, hfs'.le⟩
      have hsc : s = c := le_antisymm (hc_ge s hsCs) hs.1
      rw [hsc] at hfs'
      linarith
    · exact h
  have habove2 : ∀ s ∈ Ioc c d, 2 * t < dist (γ.extend s) z := by
    intro s hs
    by_contra hcon
    rw [not_lt] at hcon
    have := hc_ge s ⟨⟨hc_mem.1.1.trans hs.1.le, hs.2⟩, hcon⟩
    linarith [hs.1]
  refine ⟨τa, τb, hτa_mem.1.1, hτa_lt, hτb_gt, hτb_mem.1.2, hτa_mem.2, hτb_mem.2, hpre, hpost,
    c, d, hc_mem.1.1, hc_lt_d, hd_mem.1.2, hfc2, hfd, ?_⟩
  intro s hs
  constructor
  · rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact hfc2.ge
    · exact (habove2 s ⟨h, hs.2⟩).le
  · rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h]; exact hfd.le
    · exact (hbelow3 s ⟨hc_mem.1.1.trans hs.1, h⟩).le

end SupercriticalLQGUniqueness.Uniqueness.Objects.Blocks

