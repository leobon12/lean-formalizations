import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBMeetDetour

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

abbrev LaneBDetourDatum := (ℝ → ℂ) × ℝ × ℝ

def laneBDetourStep (P : ℝ → ℂ) (d : LaneBDetourDatum) : ℝ → ℂ :=
  laneBMeetDetour P d.1 d.2.1 d.2.2

def laneBDetourFold (P : ℝ → ℂ) (ds : List LaneBDetourDatum) : ℝ → ℂ :=
  ds.foldl laneBDetourStep P

 
def LaneBValidDetours (P : ℝ → ℂ) : List LaneBDetourDatum → Prop
  | [] => True
  | d :: ds => d.2.1 ∈ Icc (0 : ℝ) 1 ∧ d.2.2 ∈ Icc (0 : ℝ) 1 ∧
      P d.2.1 = d.1 d.2.2 ∧ LaneBValidDetours (laneBDetourStep P d) ds

 



theorem laneB_detourFold_len_le (ξ : ℝ) (f : ℂ → ℝ)
    (ds : List LaneBDetourDatum) (P : ℝ → ℂ)
    (hds : LaneBValidDetours P ds) :
    lfppLen ξ f (laneBDetourFold P ds) ≤
      lfppLen ξ f P + 3 * (ds.map fun d => lfppLen ξ f d.1).sum := by
  induction ds generalizing P with
  | nil => simp [laneBDetourFold]
  | cons d ds ih =>
      obtain ⟨hs, ht, hm, htail⟩ := hds
      have hstep : lfppLen ξ f (laneBDetourStep P d) ≤
          lfppLen ξ f P + 3 * lfppLen ξ f d.1 :=
        laneB_meetDetour_len_le_add hs ht hm
      have hrest := ih (laneBDetourStep P d) htail
      simp only [laneBDetourFold, List.foldl_cons, List.map_cons,
        List.sum_cons] at hrest ⊢
      calc
        _ ≤ lfppLen ξ f (laneBDetourStep P d) +
            3 * (ds.map fun d => lfppLen ξ f d.1).sum := hrest
        _ ≤ (lfppLen ξ f P + 3 * lfppLen ξ f d.1) +
            3 * (ds.map fun d => lfppLen ξ f d.1).sum := by gcongr
        _ = lfppLen ξ f P +
            3 * (lfppLen ξ f d.1 + (ds.map fun d => lfppLen ξ f d.1).sum) := by
          rw [mul_add]
          ac_rfl

 

theorem laneB_detourFold_contains_base (ds : List LaneBDetourDatum)
    (P : ℝ → ℂ) (hds : LaneBValidDetours P ds) :
    P '' Icc (0 : ℝ) 1 ⊆ laneBDetourFold P ds '' Icc (0 : ℝ) 1 := by
  induction ds generalizing P with
  | nil => simp [laneBDetourFold]
  | cons d ds ih =>
      obtain ⟨hs, _ht, hm, htail⟩ := hds
      have hstep : P '' Icc (0 : ℝ) 1 ⊆
          laneBDetourStep P d '' Icc (0 : ℝ) 1 := by
        simpa only [laneBDetourStep] using
          (laneB_meetDetour_contains_base hs hm)
      exact hstep.trans
        (by simpa only [laneBDetourFold, List.foldl_cons] using
          ih (laneBDetourStep P d) htail)

 


theorem laneB_detourFold_contains_inserted (ds : List LaneBDetourDatum)
    (P : ℝ → ℂ) (hds : LaneBValidDetours P ds)
    (d : LaneBDetourDatum) (hd : d ∈ ds) :
    d.1 '' Icc (0 : ℝ) 1 ⊆ laneBDetourFold P ds '' Icc (0 : ℝ) 1 := by
  induction ds generalizing P with
  | nil => simp at hd
  | cons e es ih =>
      obtain ⟨hs, _ht, hm, htail⟩ := hds
      rcases List.mem_cons.mp hd with rfl | hd'
      · have hstep : d.1 '' Icc (0 : ℝ) 1 ⊆
            laneBDetourStep P d '' Icc (0 : ℝ) 1 := by
          simpa only [laneBDetourStep] using
            (laneB_meetDetour_contains_crossing hm)
        exact hstep.trans
          (by simpa only [laneBDetourFold, List.foldl_cons] using
            laneB_detourFold_contains_base es (laneBDetourStep P d) htail)
      · simpa only [laneBDetourFold, List.foldl_cons] using
          ih (laneBDetourStep P e) htail hd'

 

theorem laneB_detourFold_piecewise (ds : List LaneBDetourDatum)
    {P : ℝ → ℂ} {a b : ℂ} (hP : IsPiecewiseC1Path P a b)
    (hds : LaneBValidDetours P ds)
    (hQ : ∀ d ∈ ds, ∃ c e : ℂ, IsPiecewiseC1Path d.1 c e) :
    IsPiecewiseC1Path (laneBDetourFold P ds) a b := by
  induction ds generalizing P with
  | nil => simpa [laneBDetourFold] using hP
  | cons d ds ih =>
      obtain ⟨hs, ht, hm, htail⟩ := hds
      obtain ⟨c, e, hpiece⟩ := hQ d (by simp)
      have hstep : IsPiecewiseC1Path (laneBDetourStep P d) a b := by
        simpa only [laneBDetourStep] using
          (laneB_meetDetour_piecewise hP hpiece hs ht hm)
      have hQtail : ∀ x ∈ ds, ∃ c e : ℂ, IsPiecewiseC1Path x.1 c e := by
        intro x hx
        exact hQ x (by simp [hx])
      simpa only [laneBDetourFold, List.foldl_cons] using
        ih hstep htail hQtail

 

theorem laneB_detourFold_mapsTo (ds : List LaneBDetourDatum)
    (P : ℝ → ℂ) {U : Set ℂ}
    (hds : LaneBValidDetours P ds)
    (hP : MapsTo P (Icc (0 : ℝ) 1) U)
    (hQ : ∀ d ∈ ds, MapsTo d.1 (Icc (0 : ℝ) 1) U) :
    MapsTo (laneBDetourFold P ds) (Icc (0 : ℝ) 1) U := by
  induction ds generalizing P with
  | nil => simpa [laneBDetourFold] using hP
  | cons d ds ih =>
      obtain ⟨hs, ht, hm, htail⟩ := hds
      have hstep := laneB_meetDetour_mapsTo hs ht hm hP (hQ d (by simp))
      have hQtail : ∀ e ∈ ds, MapsTo e.1 (Icc (0 : ℝ) 1) U := by
        intro e he
        exact hQ e (by simp [he])
      simpa only [laneBDetourFold, List.foldl_cons] using
        ih (laneBDetourStep P d) htail hstep hQtail

end SupercriticalLQGUniqueness.B2.DG20Conc
