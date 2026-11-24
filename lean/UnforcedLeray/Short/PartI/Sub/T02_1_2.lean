import UnforcedLeray.Short.PartI.Sub.T02_1

/-!
# Part I, task `PartI:T02/1/2`: `H^k` persistence of the mild `H³` solution (conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1: the solution is smooth for positive time and the datum is
in `BUC ∩ H^k` for every `k`; here the same `[0,T]`).

The target is `HkPersistence` (`Short/PartI/Sub/T02_1.lean`): the compact mild `H³` solution `u` of
`trainDatum c` lifts to `C([0,T], H^{k+3})` for every `k`.  The library only has `H³` heat and
Duhamel machinery, so the proof is organised by *derivative paths* instead of by `H^{k+3}` norms:

* `HasDerivPath c T j a a'`: for each `t`, `a'(t) ∈ H³` is the periodic weak `∂_j`-derivative of
  `a(t) ∈ H³`.
* `SmoothPath c T n a`: `a` has derivative paths in `C([0,T], H³)` along every word of length `≤ n`
  (defined recursively: `∂_j a` exists in `C([0,T],H³)` and is itself `SmoothPath (n-1)`).

Proof structure (all of it compiled below; only the leaves are open):

1. `ProjectedDatumPersistent` (A): the projected datum lies in every `H^{k+3}`.
2. `SeedDerivative` (S): `∂_j` commutes with the projected heat orbit `t ↦ P₀ e^{νtΔ} x`.
3. `BilDuhamelDerivative` (P): `∂_j (a ⋆ b) = a' ⋆ b + a ⋆ b'` for the polarised Duhamel map
   `bilDuhamel` (product rule for `u ⊗ w` in `H³` and `∂_j` commutes with the Duhamel integral).
4. `BaseDerivative` (B0): the mild solution has a `∂_j`-derivative path solving the linearised
   equation `u' = s' + Λ_u u'` (the nonlinear first step; `∂_j u ∈ C(H²)` solves it in `H²`/`L²`,
   the `H³` solution exists and is unique in the weak space).
5. `StepDerivative` (S1): a solution `w` of the *linear* equation `w = h + Λ_u w` (with `u, h`
   having `∂_j`-derivative paths) has a `∂_j`-derivative path solving the differentiated linear
   equation.
6. `SmoothPathsPersistent` (Z): `SmoothPath n u` for all `n` gives `PersistentFamily`
   (Sobolev bookkeeping: `Sob.W.ofFields` and `partialDeriv`).

`smoothPath_linear` (all `n`: linear solutions inherit smoothness) and `mildTrain_smoothPath`
are proved here from (S), (P), (B0), (S1), (A); `hkPersistence_of` then gives `HkPersistence`
from (A), (S), (P), (B0), (S1), (Z).  The unconditional statement is task `PartI:T02/1/2`
(`Short/PartI/Tasks/LocalClassicalBounded/HkPersistence.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-! ### Paths, the polarised Duhamel map and derivative paths -/

/-- A continuous `H³` path on `[0,T]`. -/
abbrev MPath (c T : ℝ) : Type _ := ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)

/-- The tensor path `r ↦ a(r) ⊗ b(r)` of two continuous vector `H³` paths. -/
def bilStressPath {c : ℝ} (hc1 : 1 ≤ c) (a b : ContinuousMap ℝ (VectorH3 c)) :
    ContinuousMap ℝ (TensorH3 c) where
  toFun r := tensorH3Bilinear hc1 (a r) (b r)
  continuous_toFun := by
    have happly : Continuous
        (fun p : (VectorH3 c →L[ℝ] TensorH3 c) × VectorH3 c => p.1 p.2) := by
      fun_prop
    have hfirst : Continuous (fun r : ℝ => tensorH3Bilinear hc1 (a r)) :=
      (tensorH3Bilinear hc1).continuous.comp a.continuous
    exact happly.comp (hfirst.prodMk b.continuous)

theorem bilStressPath_self {c : ℝ} (hc1 : 1 ≤ c) (a : ContinuousMap ℝ (VectorH3 c)) :
    bilStressPath hc1 a a = tensorH3StressPath hc1 a := rfl

/-- **The polarised Duhamel map** `(a, b) ↦ -∫₀ᵗ P₀ e^{ν(t-r)Δ} div (a(r) ⊗ b(r)) dr` on
`C([0,T], H³)`; `projectedNonlinearDuhamelCompactMap u = bilDuhamel u u`. -/
def bilDuhamel {c ν T : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 ≤ T)
    (a b : MPath c T) : MPath c T :=
  -((projectedHeatDuhamelContinuousMap (ν := ν) hc hν
      (M := 1536 * ‖a‖ * ‖b‖)
      (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _))
      (bilStressPath hc1 (extendCompactPath hT a) (extendCompactPath hT b))
      (fun r => by
        change ‖tensorH3Bilinear hc1 (extendCompactPath hT a r) (extendCompactPath hT b r)‖ ≤ _
        calc _ ≤ 1536 * ‖extendCompactPath hT a r‖ * ‖extendCompactPath hT b r‖ :=
              norm_tensorH3Bilinear_apply_le hc1 _ _
          _ ≤ 1536 * ‖a‖ * ‖b‖ :=
              mul_le_mul (mul_le_mul_of_nonneg_left (norm_extendCompactPath_le hT a r)
                (by norm_num)) (norm_extendCompactPath_le hT b r) (norm_nonneg _)
                (mul_nonneg (by norm_num) (norm_nonneg _)))).comp compactTimeInclusion)

/-- The nonlinear Duhamel map is the diagonal of `bilDuhamel`. -/
theorem projectedNonlinearDuhamelCompactMap_eq_bilDuhamel {c ν T : ℝ} (hc : 0 < c)
    (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 ≤ T) (u : MPath c T) :
    projectedNonlinearDuhamelCompactMap hc hc1 hν hT u = bilDuhamel hc hc1 hν hT u u := rfl

/-- The linearisation `Λ_u w = (a, b) ↦ u ⋆ w + w ⋆ u` of the nonlinear Duhamel map at `u`. -/
def linDuhamel {c ν T : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 ≤ T)
    (u w : MPath c T) : MPath c T :=
  bilDuhamel hc hc1 hν hT u w + bilDuhamel hc hc1 hν hT w u

/-- The heat seed path `t ↦ P₀ e^{νtΔ} x` on `[0,T]`. -/
def seedPath {c ν : ℝ} (T : ℝ) (hc : 0 < c) (hν : 0 < ν) (x : VectorH3 c) : MPath c T :=
  (projectedHeatSeedPath hc hν x).comp compactTimeInclusion

/-- `a'(t)` is the periodic weak `∂_j`-derivative of `a(t)` for every `t ∈ [0,T]`. -/
def HasDerivPath (c T : ℝ) (j : Fin 2) (a a' : MPath c T) : Prop :=
  ∀ t, Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
    (Cyl.H.val (a t) : Plane → Vec) (Cyl.H.val (a' t) : Plane → Vec)

/-! ### The six open leaves -/

/-- **Leaf A** (datum side, source lines 261-288): the projected datum lies in every `H^{k+3}`
(the periodised Gaussian `trainDatum c` is smooth with all `L²` jets,
`UnforcedLeray.B0141.memHAll_datum`, `hasWeakDeriv_cylinder_word_of_smooth_periodic`, and is
divergence free so `P₀` fixes it).  Note `Sob.W.ofCylSmooth` does not apply (`IsCylSmooth` needs
compact support in `η`). -/
def ProjectedDatumPersistent : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (k : ℕ), ∃ x : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3),
    Sob.W.restrict (Nat.le_add_left 3 k) x = projectedInitialDatumH3 hc

/-- **Leaf S** (`∂_j` commutes with the projected heat orbit): if `x' = ∂_j x` weakly then
`t ↦ P₀ e^{νtΔ} x'` is the `∂_j`-derivative path of `t ↦ P₀ e^{νtΔ} x`.  (Translation invariance of
the Gaussian kernel and of `P₀`; library: `Lib/HeatCylinder/HeatVecH3Derivative*.lean`,
`HeatVecH3DerivativeTransport.lean`, `Lib/TrainB/P0H3Operator.lean`.) -/
def SeedDerivative : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (j : Fin 2) (x x' : VectorH3 c),
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → Vec) (Cyl.H.val x' : Plane → Vec) →
    HasDerivPath c T j (seedPath T hc hν x) (seedPath T hc hν x')

/-- **Leaf P** (product rule for the polarised Duhamel map): if `a, b ∈ C([0,T],H³)` have
`∂_j`-derivative paths `a', b' ∈ C([0,T],H³)`, then `a ⋆ b` has the derivative path
`a' ⋆ b + a ⋆ b'`.  Two ingredients: the weak product rule for `tensorH3Bilinear`
(`∂_j(a ⊗ b) = a' ⊗ b + a ⊗ b'` in `H³`, since `H³ ⊂ W^{1,∞} ∩ H¹` in `ℝ²`) and the commutation
of `∂_j` with the projected Duhamel integral (translation invariance). -/
def BilDuhamelDerivative : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T) (j : Fin 2)
    (a a' b b' : MPath c T),
    HasDerivPath c T j a a' → HasDerivPath c T j b b' →
    HasDerivPath c T j (bilDuhamel hc hc1 hν hT.le a b)
      (bilDuhamel hc hc1 hν hT.le a' b + bilDuhamel hc hc1 hν hT.le a b')

/-- **Leaf B0** (first derivative of the mild solution, source lines 261-288): if
`u = s + u ⋆ u` and the seed `s` has a `∂_j`-derivative path `s'`, then `u` has a `∂_j`-derivative
path `u'` and `u' = s' + Λ_u u'`.  Proof: `z = ∂_j u(t) ∈ H²` (so `L²`) solves the linearised
Duhamel equation in the weak space; the `H³` solution of `w = s' + Λ_u w` exists and is unique
(Bielecki weighted norm with the kernel bound `heatDivL2Coeff`, no restart needed), and
uniqueness in `C([0,T], L²)` identifies `z = w`. -/
def BaseDerivative : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T) (j : Fin 2)
    (s s' u : MPath c T),
    u = s + bilDuhamel hc hc1 hν hT.le u u → HasDerivPath c T j s s' →
    ∃ u' : MPath c T, HasDerivPath c T j u u' ∧
      u' = s' + linDuhamel hc hc1 hν hT.le u u'

/-- **Leaf S1** (one derivative of a linear solution): if `u, h` have `∂_j`-derivative paths
`u', h'` and `w = h + Λ_u w` in `C([0,T],H³)`, then `w` has a `∂_j`-derivative path `w'` and
`w' = (h' + u' ⋆ w + w ⋆ u') + Λ_u w'`.  Same proof as `BaseDerivative`, with the extra
forcing `u' ⋆ w + w ⋆ u' ∈ C([0,T],H³)`. -/
def StepDerivative : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T) (j : Fin 2)
    (u u' h h' w : MPath c T),
    HasDerivPath c T j u u' → HasDerivPath c T j h h' →
    w = h + linDuhamel hc hc1 hν hT.le u w →
    ∃ w' : MPath c T, HasDerivPath c T j w w' ∧
      w' = (h' + bilDuhamel hc hc1 hν hT.le u' w + bilDuhamel hc hc1 hν hT.le w u') +
        linDuhamel hc hc1 hν hT.le u w'

/-- `SmoothPath c T n a`: `a` has derivative paths in `C([0,T],H³)` along every word of length
`≤ n` (recursively: all first derivatives exist and are `SmoothPath (n-1)`). -/
def SmoothPath (c T : ℝ) : ℕ → MPath c T → Prop
  | 0, _ => True
  | n + 1, a => ∀ j : Fin 2, ∃ a' : MPath c T, HasDerivPath c T j a a' ∧ SmoothPath c T n a'

theorem smoothPath_succ {c T : ℝ} {n : ℕ} {a : MPath c T} :
    SmoothPath c T (n + 1) a ↔
      ∀ j : Fin 2, ∃ a' : MPath c T, HasDerivPath c T j a a' ∧ SmoothPath c T n a' := Iff.rfl

/-- **Leaf Z** (Sobolev bookkeeping): `SmoothPath n u` for all `n` gives the lifts
`u_k ∈ C([0,T], H^{k+3})`: by induction on `k`, build `u_{k+1}(t) ∈ H^{k+4}` from `u(t)` and the
two lifted derivative paths with `Sob.W.ofFields` (each `Idx 2 (k+1)` is `zero` or `cons i β`),
`partialDeriv` and `restrict`; continuity in `t` from the continuity of the components. -/
def SmoothPathsPersistent : Prop :=
  ∀ (c T : ℝ), 0 < c → 0 < T → ∀ u : MPath c T,
    (∀ n : ℕ, SmoothPath c T n u) → PersistentFamily c T u

/-! ### Derivative paths: sum, uniqueness, closure -/

theorem val_add_ae {c : ℝ} (x y : VectorH3 c) :
    (Cyl.H.val (x + y) : Plane → Vec) =ᵐ[(Sob.cylinder c).μ]
      (Cyl.H.val x : Plane → Vec) + (Cyl.H.val y : Plane → Vec) := by
  have e : Cyl.H.val (x + y) = Cyl.H.val x + Cyl.H.val y := map_add _ x y
  have h := Lp.coeFn_add (Cyl.H.val x) (Cyl.H.val y)
  rw [e]
  exact (Sob.ae_eq_wμ_iff _ _).mp h

theorem HasDerivPath.add {c T : ℝ} {j : Fin 2} {a a' b b' : MPath c T}
    (ha : HasDerivPath c T j a a') (hb : HasDerivPath c T j b b') :
    HasDerivPath c T j (a + b) (a' + b') := by
  intro t
  refine ((ha t).add (hb t)).congr_ae ?_ ?_
  · exact (val_add_ae (a t) (b t)).symm
  · exact (val_add_ae (a' t) (b' t)).symm

/-- Derivative paths are unique (uniqueness of weak derivatives and `Sob.W.ext`). -/
theorem HasDerivPath.unique {c T : ℝ} {j : Fin 2} {a d₁ d₂ : MPath c T}
    (h₁ : HasDerivPath c T j a d₁) (h₂ : HasDerivPath c T j a d₂) : d₁ = d₂ := by
  ext t : 1
  apply Sob.W.ext
  apply Lp.ext
  refine (Sob.ae_eq_wμ_iff _ _).mpr ?_
  exact (h₁ t).ae_unique (h₂ t) (Sob.locallyIntegrable_of_memLp (Lp.memLp _))
    (Sob.locallyIntegrable_of_memLp (Lp.memLp _))

theorem SmoothPath.mono {c T : ℝ} (n : ℕ) {a : MPath c T} :
    SmoothPath c T (n + 1) a → SmoothPath c T n a := by
  induction n generalizing a with
  | zero => intro _; trivial
  | succ n ih =>
    intro h j
    obtain ⟨a', ha', has⟩ := smoothPath_succ.mp h j
    exact ⟨a', ha', ih has⟩

theorem SmoothPath.add {c T : ℝ} (n : ℕ) {a b : MPath c T} :
    SmoothPath c T n a → SmoothPath c T n b → SmoothPath c T n (a + b) := by
  induction n generalizing a b with
  | zero => intro _ _; trivial
  | succ n ih =>
    intro ha hb j
    obtain ⟨a', ha', has⟩ := smoothPath_succ.mp ha j
    obtain ⟨b', hb', hbs⟩ := smoothPath_succ.mp hb j
    exact ⟨a' + b', ha'.add hb', ih has hbs⟩

theorem SmoothPath.bil (hP : BilDuhamelDerivative) {ν c T : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (hc1 : 1 ≤ c) (hT : 0 < T) :
    ∀ (n : ℕ) (a b : MPath c T), SmoothPath c T n a → SmoothPath c T n b →
      SmoothPath c T n (bilDuhamel hc hc1 hν hT.le a b) := by
  intro n
  induction n with
  | zero => intro a b _ _; trivial
  | succ n ih =>
    intro a b ha hb j
    obtain ⟨a', ha', has⟩ := smoothPath_succ.mp ha j
    obtain ⟨b', hb', hbs⟩ := smoothPath_succ.mp hb j
    refine ⟨bilDuhamel hc hc1 hν hT.le a' b + bilDuhamel hc hc1 hν hT.le a b',
      hP ν c T hν hc hc1 hT j a a' b b' ha' hb', ?_⟩
    exact SmoothPath.add n (ih a' b has (SmoothPath.mono n hb))
      (ih a b' (SmoothPath.mono n ha) hbs)

/-- **Linear solutions inherit smoothness**: `u, h` smooth of order `m` and `w = h + Λ_u w` give
`w` smooth of order `m`.  By induction on `m`, with `StepDerivative` and the product rule. -/
theorem smoothPath_linear (hP : BilDuhamelDerivative) (hSt : StepDerivative) {ν c T : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T) :
    ∀ (m : ℕ) (u h w : MPath c T), SmoothPath c T m u → SmoothPath c T m h →
      w = h + linDuhamel hc hc1 hν hT.le u w → SmoothPath c T m w := by
  intro m
  induction m with
  | zero => intro u h w _ _ _; trivial
  | succ m ih =>
    intro u h w hu hh hw j
    obtain ⟨u', hu', hus⟩ := smoothPath_succ.mp hu j
    obtain ⟨h', hh', hhs⟩ := smoothPath_succ.mp hh j
    obtain ⟨w', hw', hw'eq⟩ := hSt ν c T hν hc hc1 hT j u u' h h' w hu' hh' hw
    have hwS : SmoothPath c T m w :=
      ih u h w (SmoothPath.mono m hu) (SmoothPath.mono m hh) hw
    have hH : SmoothPath c T m
        ((h' + bilDuhamel hc hc1 hν hT.le u' w) + bilDuhamel hc hc1 hν hT.le w u') :=
      SmoothPath.add m
        (SmoothPath.add m hhs (SmoothPath.bil hP hν hc hc1 hT m u' w hus hwS))
        (SmoothPath.bil hP hν hc hc1 hT m w u' hwS hus)
    exact ⟨w', hw', ih u _ w' (SmoothPath.mono m hu) hH hw'eq⟩

/-! ### The seed path of a datum in `H^{n+3}` is smooth of order `n` -/

theorem hasWeakDeriv_partialDeriv {c : ℝ} {k : ℕ} (j : Fin 2)
    (y : Cyl.H ℝ Cyl.Vec2 c 0 (k + 1)) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val y : Plane → Cyl.Vec2) (Cyl.H.val (Sob.W.partialDeriv j y) : Plane → Cyl.Vec2) := by
  have h1 := Sob.W.hasWeakDeriv y (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 k))
  rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_zero] at h1
  exact h1

theorem seedPath_smooth (hS : SeedDerivative) {ν c : ℝ} (T : ℝ) (hν : 0 < ν) (hc : 0 < c) :
    ∀ (n : ℕ) (x : VectorH3 c),
      (∃ y : Cyl.H ℝ Cyl.Vec2 c 0 (n + 3), Sob.W.restrict (Nat.le_add_left 3 n) y = x) →
      SmoothPath c T n (seedPath T hc hν x) := by
  intro n
  induction n with
  | zero => intro x _; trivial
  | succ n ih =>
    intro x hx j
    obtain ⟨y, hy⟩ := hx
    let yj : Cyl.H ℝ Cyl.Vec2 c 0 (n + 3) := Sob.W.partialDeriv j y
    let xj : VectorH3 c := Sob.W.restrict (Nat.le_add_left 3 n) yj
    refine ⟨seedPath T hc hν xj, ?_, ih xj ⟨yj, rfl⟩⟩
    refine hS ν c T hν hc j x xj ?_
    have h1 := hasWeakDeriv_partialDeriv (c := c) (k := n + 3) j y
    subst hy
    exact h1

/-! ### The mild solution is smooth of every order -/

theorem mildTrain_smoothPath (hA : ProjectedDatumPersistent) (hS : SeedDerivative)
    (hP : BilDuhamelDerivative) (hB : BaseDerivative) (hSt : StepDerivative)
    {ν c T : ℝ} (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T) (u : MPath c T)
    (hu : IsMildTrain ν c T hν hc hc1 hT u) : ∀ n : ℕ, SmoothPath c T n u := by
  have hmild : u = seedPath T hc hν (projectedInitialDatumH3 hc) +
      bilDuhamel hc hc1 hν hT.le u u := hu.1
  intro n
  induction n with
  | zero => trivial
  | succ n ih =>
    intro j
    have hs : SmoothPath c T (n + 1) (seedPath T hc hν (projectedInitialDatumH3 hc)) :=
      seedPath_smooth hS T hν hc (n + 1) _ (hA c hc (n + 1))
    obtain ⟨s', hs', hs's⟩ := smoothPath_succ.mp hs j
    obtain ⟨u', hu', hu'eq⟩ := hB ν c T hν hc hc1 hT j _ s' u hmild hs'
    exact ⟨u', hu', smoothPath_linear hP hSt hν hc hc1 hT n u s' u' ih hs's hu'eq⟩

/-- **`HkPersistence` from the six leaves.** -/
theorem hkPersistence_of (hA : ProjectedDatumPersistent) (hS : SeedDerivative)
    (hP : BilDuhamelDerivative) (hB : BaseDerivative) (hSt : StepDerivative)
    (hZ : SmoothPathsPersistent) : HkPersistence := by
  intro ν c T hν hc hc1 hT u hu
  exact hZ c T hc hT u (mildTrain_smoothPath hA hS hP hB hSt hν hc hc1 hT u hu)

end UnforcedLeray.Short.PartI
