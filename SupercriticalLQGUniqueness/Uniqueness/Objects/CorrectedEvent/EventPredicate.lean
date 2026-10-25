import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LQGMetric.Topo.Disconnect
import LQGMetric.Field.CameronMartin
import Mathlib




 






set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 
def ann (w : ℂ) (a b : ℝ) : Set ℂ := {x | a < dist x w ∧ dist x w < b}

 
def cann (w : ℂ) (a b : ℝ) : Set ℂ := {x | a ≤ dist x w ∧ dist x w ≤ b}

 
def around (D : LSCMetric) (w : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ), ⨅ (t : ℝ), ⨅ (u : ℝ), ⨅ (_ : D.IsCurve P t u),
    ⨅ (_ : P '' Icc t u ⊆ ann w a b),
    ⨅ (_ : LQGMetric.Disconnects (P '' Icc t u) (sphere w a) (sphere w b)),
    D.len P t u

 
def acr (D : LSCMetric) (w : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ), ⨅ (t : ℝ), ⨅ (u : ℝ), ⨅ (_ : D.IsCurve P t u),
    ⨅ (_ : P '' Icc t u ⊆ cann w a b),
    ⨅ (_ : P t ∈ sphere w a), ⨅ (_ : P u ∈ sphere w b), D.len P t u

 
def ambientAcross (D : LSCMetric) (w : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ x ∈ sphere w a, ⨅ y ∈ sphere w b, D (x,y)

 
def polar (s θ : ℝ) : ℂ := (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

 
def segment (a b : ℂ) : Set ℂ :=
  {z | ∃ t ∈ Icc (0:ℝ) 1, z = (1-t)*a+t*b}

 
def arc (s θ0 θ1 : ℝ) : Set ℂ :=
  {z | ∃ θ ∈ Icc (min θ0 θ1) (max θ0 θ1), z = polar s θ}

 

structure TubeData where
  r : ℝ
  rho : ℝ
  alpha : ℝ
  K : ℕ
  Kpos : 0 < K
  orientation : ℂ
  psiU : ℝ
  psiV : ℝ
  blockRadius : ℝ
  lambda : ℝ
  A_endpt : ℝ
  mollifier : LQGMetric.TestC
  bump : LQGMetric.TestC
  netRadius : ℝ
  netSites : Finset ℂ

 
def site (T : TubeData) (k : Fin T.K) : ℂ :=
  polar (2*T.r) (2*Real.pi*(k.val:ℝ)/(T.K:ℝ))

 
def tangent (T : TubeData) (k : Fin T.K) : ℂ :=
  Complex.I * Complex.exp ((2*Real.pi*(k.val:ℝ)/(T.K:ℝ) : ℝ) * Complex.I)

 
def moduleMap (T : TubeData) (k : Fin T.K) (w : ℂ) : ℂ :=
  site T k + ((T.rho*T.r : ℝ) : ℂ)*T.orientation*w

 
def blockNorm (T : TubeData) : Set ℂ :=
  {w | T.alpha < ‖w‖ ∧ ‖w‖ < 1 ∧ 0 < w.re}

 
def uNorm (T : TubeData) : ℂ := polar T.alpha T.psiU
def vNorm (T : TubeData) : ℂ := polar 1 T.psiV

 
def sPrime (T : TubeData) : ℝ := T.blockRadius/(T.rho*T.r)

 
def inStub (T : TubeData) : Set ℂ :=
  segment 0 (polar (T.alpha-3*sPrime T/4) T.psiU) ∪
    segment (-(2.5:ℂ)) 0

 
def outStub (T : TubeData) : Set ℂ :=
  {w | ∃ t ∈ Icc (1+3*sPrime T/4) (1.5:ℝ), w = polar t T.psiV} ∪
    arc 1.5 T.psiV 0 ∪ segment (1.5:ℂ) (2.5:ℂ)

 
def twistAngle (T : TubeData) (k : Fin T.K) : ℝ :=
  Complex.arg (tangent T k / T.orientation)

 
def outTwist (T : TubeData) (k : Fin T.K) : Set ℂ :=
  let d := twistAngle T k
  arc 2.5 0 (d/2) ∪
    {w | ∃ t ∈ Icc (2.5:ℝ) 3.5, w = polar t (d/2)} ∪
    arc 3.5 (d/2) d ∪
    {w | ∃ t ∈ Icc (3.5:ℝ) 4, w = polar t d}

 
def gatePlus (T : TubeData) (k : Fin T.K) : ℂ :=
  site T k + (4*T.rho*T.r:ℝ)*tangent T k
def gateMinus (T : TubeData) (k : Fin T.K) : ℂ :=
  site T k - (4*T.rho*T.r:ℝ)*tangent T k

 
def nextSite (T : TubeData) (k : Fin T.K) : Fin T.K :=
  ⟨(k.val+1) % T.K, Nat.mod_lt _ T.Kpos⟩

 

def connector (T : TubeData) (k : Fin T.K) : Set ℂ :=
  (moduleMap T k) '' (outStub T ∪ outTwist T k) ∪
  segment (gatePlus T k) (gateMinus T (nextSite T k)) ∪
  (moduleMap T (nextSite T k)) ''
    ((fun w : ℂ => -w) '' outTwist T (nextSite T k) ∪ inStub T)

 
def block (T : TubeData) (k : Fin T.K) : Set ℂ :=
  (moduleMap T k) '' blockNorm T

 
def innerCenter (T : TubeData) (k : Fin T.K) : ℂ := moduleMap T k (uNorm T)
def outerCenter (T : TubeData) (k : Fin T.K) : ℂ := moduleMap T k (vNorm T)

 
def tubeWidth (T : TubeData) : ℝ := T.lambda*T.A_endpt*T.rho*T.r

 
def tubeSet (T : TubeData) : Set ℂ :=
  ⋃ k : Fin T.K, block T k ∪ ball (innerCenter T k) T.blockRadius ∪
    ball (outerCenter T k) T.blockRadius ∪
    {x | ∃ y ∈ connector T k, dist x y < tubeWidth T}

 
def tubeV (T : TubeData) (A_sup : ℝ) : Set ℂ :=
  {x | ∃ y ∈ tubeSet T, dist x y < A_sup*T.r}

 


def bumpFormula (T : TubeData) (A_max A_sup : ℝ) (x : ℂ) : ℝ :=
  by
    classical
    exact A_max * ∫ y : ℂ,
      (if y ∈ tubeV T (A_sup/2) then (1:ℝ) else 0) * T.mollifier (x-y)

 
structure Cell where
  lo : ℝ
  hi : ℝ

 
def cellCenter (c : ℂ) (s : ℝ) (l : Cell) : ℂ :=
  c + (s : ℂ) * Complex.exp (((l.lo + l.hi) / 2 : ℝ) * Complex.I)

 





structure Constants where
  ξ : ℝ
  Q : ℝ
  r : ℝ
  lamConst : ℝ
  ρ : ℝ
  A_loc : ℝ
  K_ann : ℝ
  A_across : ℝ
  A_around : ℝ
  c_reg : ℝ
  k0 : ℕ
  A_sp : ℝ
  A_nar : ℝ
  A_set : ℝ
  A_internal : ℝ
  A_max : ℝ
  A_sup : ℝ
  A_endpt : ℝ
  A_RN : ℝ
  rPos : 0 < r
  ξPos : 0 < ξ
  QPos : 0 < Q
  lamPos : 0 < lamConst
  rhoPos : 0 < ρ
  supPos : 0 < A_sup
  regPos : 0 < c_reg
  regLtOne : c_reg < 1
  k0Large : 48 ≤ k0
  acrossPos : 0 < A_across
  aroundGtOne : 1 < A_around
  spPos : 0 < A_sp
  spLtEp : A_sp < (2:ℝ) ^ (-(k0:ℝ))
  rhoLt : ρ < lamConst*A_sp
  narPos : 0 < A_nar
  narLe : A_nar ≤ lamConst*(1-K_ann)*A_endpt*ρ
  narLeQ : A_nar ≤ 20/21
   

  narrowQScale : (2 : ℝ) ^ ((8*Q+12)/3) ≤ lamConst/A_nar
  setPos : 0 < A_set
  setLtNar : A_set < A_nar
  internalPos : 0 < A_internal
  maxPos : 0 < A_max
  endptPos : 0 < A_endpt
  supLtSet : A_sup < A_set
  supLe : A_sup ≤ 1/64
  rnPos : 0 < A_RN

 

def DataMatch (C : Constants) (T : TubeData) : Prop :=
  T.r = C.r ∧ T.rho = C.ρ ∧ T.lambda = C.lamConst ∧
  T.A_endpt = C.A_endpt ∧ T.alpha = C.K_ann ∧
  T.K = Nat.ceil (C.lamConst/(C.A_loc*C.ρ)) ∧
  T.orientation ^ 4 = 1 ∧
  T.psiU ∈ Icc (-Real.pi/2) (Real.pi/2) ∧
  T.psiV ∈ Icc (-Real.pi/2) (Real.pi/2) ∧
  C.A_endpt*C.ρ*C.r ≤ T.blockRadius ∧
  T.blockRadius ≤ Real.sqrt C.A_endpt*C.ρ*C.r ∧
  0 < T.netRadius ∧ T.netRadius ≤ C.A_set*C.r/4 ∧
  T.netSites.Nonempty ∧
  (∀ x ∈ T.netSites, closedBall x (2*T.netRadius) ⊆ tubeSet T) ∧
  (∀ x ∈ T.netSites, ∀ y ∈ T.netSites,
    Relation.ReflTransGen
      (fun u v : ℂ => u ∈ T.netSites ∧ v ∈ T.netSites ∧
        T.netRadius < dist u v ∧ dist u v < 2*T.netRadius) x y) ∧
  LQGMetric.Disconnects
    (⋃ x ∈ T.netSites, ball x T.netRadius)
    (closedBall 0 (1.5*C.r)) (ball 0 (2.5*C.r))ᶜ ∧
  (∀ y ∈ closure (tubeSet T), ∃ x ∈ T.netSites, dist y x ≤ C.A_set*C.r/2) ∧
  (∀ x, 0 ≤ T.mollifier x) ∧
  (∀ x, C.A_sup*C.r/4 ≤ dist x 0 → T.mollifier x = 0) ∧
  (∫ x : ℂ, T.mollifier x) = 1 ∧
  (∀ x, T.bump x = bumpFormula T C.A_max C.A_sup x) ∧
  (∀ x, 0 ≤ T.bump x ∧ T.bump x ≤ C.A_max) ∧
  (∀ x ∈ closure (tubeSet T), T.bump x = C.A_max) ∧
  (∀ x ∉ tubeV T C.A_sup, T.bump x = 0)

 
def normalizer (C : Constants) (g : LQGMetric.DistC) (s : ℝ) (w : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (s ^ (C.ξ * C.Q) * Real.exp (C.ξ * LQGMetric.circleAvg g s w))

 
def lam (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℝ))

 
def regK (k : ℕ) : ℕ := k / 12 - 1

 
def grid (a : ℝ) : Set ℂ :=
  {z | ∃ m n : ℤ, z = ((a * m : ℝ) : ℂ) + ((a * n : ℝ) : ℂ) * Complex.I}

 
def regSites (C : Constants) (k : ℕ) : Set ℂ :=
  {z | z ∈ grid (lam k * C.r / 4) ∧
    ball z (2 * 4 ^ (regK k) * lam k * C.r) ⊆ ann 0 C.r (4 * C.r)}

 
def regGood (C : Constants) (D : LSCMetric) (s : ℝ) (w : ℂ) : Prop :=
  0 < around D w s (2*s) ∧ around D w s (2*s) < ⊤ ∧
  0 < acr D w s (2*s) ∧ acr D w s (2*s) < ⊤ ∧
  around D w s (2*s) ≤ ENNReal.ofReal C.c_reg⁻¹ * acr D w s (2*s)

 
def S1 (C : Constants) (D : LSCMetric) (g : LQGMetric.DistC) : Prop :=
  ENNReal.ofReal C.A_across * normalizer C g C.r 0 ≤ acr D 0 C.r (1.5*C.r) ∧
  ENNReal.ofReal C.A_across * normalizer C g C.r 0 ≤ acr D 0 (2.5*C.r) (3*C.r)

 
def S2 (C : Constants) (D : LSCMetric) (g : LQGMetric.DistC) : Prop :=
  around D 0 (3*C.r) (4*C.r) ≤
    ENNReal.ofReal C.A_around * normalizer C g C.r 0

 
def S3 (C : Constants) (D : LSCMetric) : Prop :=
  by
    classical
    exact ∀ k : ℕ, C.k0 ≤ k → ∀ z ∈ regSites C k,
      2 * ((Finset.Icc 1 (regK k)).filter
        (fun j => regGood C D (4 ^ j * lam k * C.r) z)).card ≥ regK k

 
def onArc (r θ0 θ1 : ℝ) (z : ℂ) : Prop :=
  ∃ θ ∈ Icc θ0 θ1, z = (2*r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

 

def S4 (C : Constants) (T : TubeData) (F : ℂ → Prop) : Prop :=
  ∀ θ0 θ1 : ℝ, 0 ≤ θ1 - θ0 → θ1 - θ0 ≤ 2 * Real.pi →
    C.A_sp * C.r / 2 ≤ 2 * C.r * (θ1 - θ0) →
    ∃ k : Fin T.K, onArc C.r θ0 θ1 (site T k) ∧ F (site T k)

 
def compareScale (k : ℕ) : ℝ := ((21 : ℝ) / 20) ^ (-(k : ℝ))

 
def compareSites (C : Constants) (k : ℕ) : Set ℂ :=
  let t := compareScale k
  {z | z ∈ grid (t*C.r/100) ∧
    Metric.infDist z (cann 0 (1.5*C.r) (3*C.r)) ≤ t*C.r/100}

 
def S5 (C : Constants) (D : LSCMetric) : Prop :=
  ∀ k : ℕ, compareScale k ≤ C.A_nar → ∀ z ∈ compareSites C k,
    let t := compareScale k
    let outer := around D z ((11/5)*t*C.r) ((14/5)*t*C.r)
    let inner := acr D z ((3/10)*t*C.r) ((9/20)*t*C.r)
    outer ≤ ENNReal.ofReal (t ^ (-(1:ℝ)/8)) * inner ∧ outer < ⊤ ∧
      0 < inner ∧ inner < ⊤

 
def zeta (C : Constants) : ℝ := C.ξ / (4*(1+C.ξ))

 
def narrowStart (C : Constants) : ℕ := Nat.floor (Real.logb 2 (C.lamConst/C.A_nar)) + 1

 
def narrowScale (C : Constants) (n : ℕ) : ℝ := (2:ℝ) ^ (-(n:ℝ)-1) * C.r

 
def narrowSites (C : Constants) (n : ℕ) : Set ℂ :=
  let a := (2:ℝ) ^ (-(n:ℝ)-4) * C.r
  {z | z ∈ grid a ∧ Metric.infDist z (cann 0 (1.5*C.r) (3*C.r)) ≤ a}

 
def S6 (C : Constants) (D : LSCMetric) (g : LQGMetric.DistC) : Prop :=
  ∀ n : ℕ, narrowStart C ≤ n → ∀ v ∈ narrowSites C n,
    ENNReal.ofReal ((2:ℝ) ^ (-(zeta C)*(n:ℝ))) *
        normalizer C g (narrowScale C n) v ≤
      acr D v (narrowScale C n / 4) (narrowScale C n) ∧
    |LQGMetric.circleAvg g (narrowScale C n) v - LQGMetric.circleAvg g C.r 0| ≤
      (2+zeta C)*(n:ℝ)*Real.log 2

 
def S7 (C : Constants) (T : TubeData) (D : LSCMetric)
    (g : LQGMetric.DistC) : Prop :=
  ∀ x ∈ T.netSites,
    around D x T.netRadius (2*T.netRadius) <
      ENNReal.ofReal (C.A_internal / (2*T.netSites.card)) * normalizer C g C.r 0

 
def supRadius (C : Constants) (k : ℕ) : ℝ := 4 ^ k * (2*C.A_sup) * C.r

 
def supK (C : Constants) : ℕ := Nat.floor (Real.logb 4 (1/(16*C.A_sup)))

 

def numCells (C : Constants) (s : ℝ) : ℕ :=
  Nat.ceil (2*Real.pi / ((1/20:ℝ)*supRadius C 1/(4*s)))

 
def circleCell (C : Constants) (s : ℝ) (l : ℕ) : Cell where
  lo := 2*Real.pi*(l:ℝ)/(numCells C s:ℝ)
  hi := 2*Real.pi*((l+1:ℕ):ℝ)/(numCells C s:ℝ)

 
def supGood (C : Constants) (D : LSCMetric) (c : ℂ) (s : ℝ)
    (l : Cell) (k : ℕ) : Prop :=
  let R := supRadius C k
  let w := cellCenter c s l
  let outer := around D w ((2+1/20)*R) ((3-1/20)*R)
  let inner := acr D w ((1+1/20)*R) ((2-1/20)*R)
  outer < ⊤ ∧ 0 < inner ∧ inner < ⊤ ∧
    outer ≤ ENNReal.ofReal (1/2 * Real.exp (-C.ξ*C.A_max)) * inner

 
def badCell (C : Constants) (D : LSCMetric) (c : ℂ) (s : ℝ) (l : Cell) : Prop :=
  ∀ k ∈ Finset.Icc 1 (supK C), ¬ supGood C D c s l k

 
def badLength (C : Constants) (D : LSCMetric) (c : ℂ) (s : ℝ) : ℝ :=
  by
    classical
    exact ∑ l ∈ Finset.range (numCells C s),
      if badCell C D c s (circleCell C s l) then
        s * ((circleCell C s l).hi-(circleCell C s l).lo) else 0

 
def S8 (C : Constants) (T : TubeData) (D : LSCMetric) : Prop :=
  ∀ k : Fin T.K,
    badLength C D (innerCenter T k) T.blockRadius ≤
      C.lamConst*C.A_endpt*C.ρ*C.r ∧
    badLength C D (outerCenter T k) T.blockRadius ≤
      C.lamConst*C.A_endpt*C.ρ*C.r

 
def S9 (C : Constants) (T : TubeData) (g : LQGMetric.DistC) : Prop :=
  |LQGMetric.pair0 g (LQGMetric.cmTest0 T.bump)| ≤ C.A_RN

 


def correctedEvent (C : Constants) (T : TubeData) (_hData : DataMatch C T)
    (F : ℂ → LQGMetric.DistC → Prop)
    (D D' : LQGMetric.DistC → LSCMetric) (g : LQGMetric.DistC) : Prop :=
  let _ := D' g
  S1 C (D g) g ∧ S2 C (D g) g ∧ S3 C (D g) ∧ S4 C T (fun z => F z g) ∧
    S5 C (D g) ∧ S6 C (D g) g ∧ S7 C T (D g) g ∧
    S8 C T (D g) ∧ S9 C T g

 
def sampleEvent {Ω : Type*} (C : Constants) (T : TubeData)
    (hData : DataMatch C T)
    (F : ℂ → LQGMetric.DistC → Prop)
    (D D' : LQGMetric.DistC → LSCMetric) (h : Ω → LQGMetric.DistC)
    (ω : Ω) : Prop := correctedEvent C T hData F D D' (h ω)

 


def regularityEvent {Ω : Type*} (weyl barrier : Set Ω) : Set Ω := weyl ∩ barrier

 

theorem regularityEvent_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (weyl barrier : Set Ω)
    (hWeyl : ∀ᵐ ω ∂P, ω ∈ weyl) (hBarrier : ∀ᵐ ω ∂P, ω ∈ barrier) :
    ∀ᵐ ω ∂P, ω ∈ regularityEvent weyl barrier := by
  filter_upwards [hWeyl, hBarrier] with ω hW hB
  exact ⟨hW, hB⟩

 
theorem event_around {C : Constants} {T : TubeData}
    {hData : DataMatch C T}
    {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g) :
    around (D g) 0 (3*C.r) (4*C.r) ≤
      ENNReal.ofReal C.A_around * normalizer C g C.r 0 := by
  exact h.2.1

 
theorem event_reg {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g) : S3 C (D g) := by
  exact h.2.2.1

 
theorem event_block_arcs {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g) : S4 C T (fun z => F z g) := by
  exact h.2.2.2.1

 


theorem event_across_of_barrier_equalities {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g)
    (hInner : ambientAcross (D g) 0 C.r (1.5*C.r) =
      acr (D g) 0 C.r (1.5*C.r))
    (hOuter : ambientAcross (D g) 0 (2.5*C.r) (3*C.r) =
      acr (D g) 0 (2.5*C.r) (3*C.r)) :
    ENNReal.ofReal C.A_across * normalizer C g C.r 0 ≤
      ambientAcross (D g) 0 C.r (1.5*C.r) ∧
    ENNReal.ofReal C.A_across * normalizer C g C.r 0 ≤
      ambientAcross (D g) 0 (2.5*C.r) (3*C.r) := by
  rw [hInner, hOuter]
  exact h.1

 
theorem event_compare_test {C : Constants} {T : TubeData}
    {hData : DataMatch C T}
    {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g) {k : ℕ} (hk : compareScale k ≤ C.A_nar)
    {z : ℂ} (hz : z ∈ compareSites C k) :
    let t := compareScale k
    let outer := around (D g) z ((11/5)*t*C.r) ((14/5)*t*C.r)
    let inner := acr (D g) z ((3/10)*t*C.r) ((9/20)*t*C.r)
    outer ≤ ENNReal.ofReal (t ^ (-(1:ℝ)/8)) * inner ∧ outer < ⊤ ∧
      0 < inner ∧ inner < ⊤ := by
  exact h.2.2.2.2.1 k hk z hz

 
theorem event_narrow_test {C : Constants} {T : TubeData}
    {hData : DataMatch C T}
    {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g) {n : ℕ} (hn : narrowStart C ≤ n)
    {v : ℂ} (hv : v ∈ narrowSites C n) :
    ENNReal.ofReal ((2:ℝ) ^ (-(zeta C)*(n:ℝ))) *
        normalizer C g (narrowScale C n) v ≤
      acr (D g) v (narrowScale C n/4) (narrowScale C n) ∧
    |LQGMetric.circleAvg g (narrowScale C n) v - LQGMetric.circleAvg g C.r 0| ≤
      (2+zeta C)*(n:ℝ)*Real.log 2 := by
  exact h.2.2.2.2.2.1 n hn v hv

 

theorem network_annulus_inside_tube {C : Constants} {T : TubeData}
    (hData : DataMatch C T) {x : ℂ} (hx : x ∈ T.netSites) :
    ann x T.netRadius (2*T.netRadius) ⊆ tubeSet T := by
  have hM1 : ∀ y ∈ T.netSites, closedBall y (2*T.netRadius) ⊆ tubeSet T := by
    unfold DataMatch at hData
    tauto
  intro y hy
  exact hM1 x hx (by
    change dist y x ≤ 2*T.netRadius
    exact hy.2.le)

 
theorem event_network_test {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g)
    {x : ℂ} (hx : x ∈ T.netSites) :
    around (D g) x T.netRadius (2*T.netRadius) <
      ENNReal.ofReal (C.A_internal / (2*T.netSites.card)) * normalizer C g C.r 0 := by
  exact h.2.2.2.2.2.2.1 x hx

 
theorem event_sup_bad_length {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g) : S8 C T (D g) := by
  exact h.2.2.2.2.2.2.2.1

 
theorem event_rn_pair {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g) :
    |LQGMetric.pair0 g (LQGMetric.cmTest0 T.bump)| ≤ C.A_RN := by
  exact h.2.2.2.2.2.2.2.2

 
theorem bump_energy_nonneg (f : LQGMetric.TestC) : 0 ≤ LQGMetric.gradEnergy f := by
  unfold LQGMetric.gradEnergy
  positivity

 

theorem event_rn_window {C : Constants} {T : TubeData}
    {hData : DataMatch C T}
    {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g) (Emax : ℝ)
    (hEnergy : LQGMetric.gradEnergy T.bump ≤ Emax) :
    (Real.exp (C.A_RN + Emax/2))⁻¹ ≤
      LQGMetric.cmDensity T.bump (LQGMetric.pair0 g) ∧
      LQGMetric.cmDensity T.bump (LQGMetric.pair0 g) ≤ Real.exp C.A_RN := by
  have hPair : |LQGMetric.pair0 g (LQGMetric.cmTest0 T.bump)| ≤ C.A_RN :=
    h.2.2.2.2.2.2.2.2
  have hLo := (abs_le.mp hPair).1
  have hHi := (abs_le.mp hPair).2
  have hNonneg := bump_energy_nonneg T.bump
  constructor
  · rw [LQGMetric.cmDensity, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith only [hLo, hEnergy]
  · rw [LQGMetric.cmDensity]
    apply Real.exp_le_exp.mpr
    linarith only [hHi, hNonneg]

 

theorem no_event_of_no_good_blocks {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (hArc : C.A_sp*C.r/2 ≤ 2*C.r*(2*Real.pi))
    (hNo : ∀ k : Fin T.K, ¬ F (site T k) g) :
    ¬ correctedEvent C T hData F D D' g := by
  intro h
  have hS4 : S4 C T (fun z => F z g) := h.2.2.2.1
  obtain ⟨k, _, hk⟩ := hS4 0 (2*Real.pi)
    (by have := Real.pi_pos; linarith)
    (by norm_num) (by simpa using hArc)
  exact hNo k hk


end SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent
