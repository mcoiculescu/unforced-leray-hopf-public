import UnforcedLeray.Short.PartI.Sub.T02_1

/-!
# Part I, task `PartI:T02/1/3`: `SpatialRepFromPersistent` (conditional decomposition)

Source of record: `the November 2 reference manuscript`, lines 261-288 ("smooth for
positive time", `BUC ∩ H^k`: the Sobolev embedding `H^{k+2}(cell) ⊂ C^k_b` on the periodic
cylinder, applied to the lifts `u_k ∈ C([0,T], H^{k+3})`).

The target is `SpatialRepFromPersistent` (`Short/PartI/Sub/T02_1.lean`): the `H³`-valued path `u`
that lifts to `C([0,T], H^{k+3})` for every `k` has a spatially smooth periodic representative `w`
with all spatial derivatives bounded uniformly on `[0,T]` and jointly continuous in `(s, z)`.

## What is proved here

`spatialRepFromPersistent_of` derives `SpatialRepFromPersistent` from two statements about the
periodic cylinder `Cyl.H ℝ Vec2 c 0 (k + 3)` (nothing about the Navier-Stokes system is used: the
hypothesis `IsMildTrain` is not needed for the representative):

1. `CylSobolevRep` (the Sobolev embedding on the cylinder, linear in the element): for every
   `k` there is an `ℝ`-linear map `g : H^{k+3} → (Plane → Vec2)` sending `x` to a `C^{k+1}`
   periodic function `g x` that represents `x` and its weak derivatives of order `≤ k + 1`
   a.e. on the cell and satisfies `‖D^j (g x)‖_∞ ≤ C ‖x‖` for `j ≤ k + 1`.
2. `AePeriodicEq` (uniqueness): two continuous `c`-periodic functions that agree a.e. on the cell
   agree everywhere.

The assembly: the level-`k` representatives of the lifts `u_k(s)` all represent the same
`H³` element `u(s)` (the lifts are compatible with `Sob.W.restrict`), hence coincide by
`AePeriodicEq`; so `w(s) := g_0 (u_0(s))` is `C^{k+1}` for every `k`, i.e. `C^∞`, its derivative
of order `k` is bounded by `C_k sup_s ‖u_k(s)‖`, and joint continuity follows from the linearity
of `g_k` and the bound (`D^k g_k(u_k(s)) - D^k g_k(u_k(s_0)) = D^k g_k(u_k(s) - u_k(s_0))`).

`CylSobolevRep` itself is cut further, by the density argument, into `CylSmoothDensity`,
`CylSmoothSobolevBound`, `ContDiffLimitCauchy` and `AePeriodicEq` (see the section below; that
assembly is the task `PartI:T02/1/3/1`).

The unconditional statement is task `PartI:T02/1/3`
(`Short/PartI/Tasks/LocalClassicalBounded/SpatialRepFromPersistent.lean`).
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

/-- The cell realisation (as a function on the plane, defined a.e. on the cell) of the `α`-th
weak derivative of an element of the periodic cylinder space `H^m`. -/
def cellDeriv (c : ℝ) {m : ℕ} (α : Sob.Idx 2 m) (x : Cyl.H ℝ Cyl.Vec2 c 0 m) : Plane → Vec :=
  ⇑(weightedToCellL2Isometry c
    (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 α x))

/-- **Sobolev embedding on the periodic cylinder** (`H^{k+3} ⊂ C^{k+1}_b`, source lines 261-288,
`BUC ∩ H^k`; the cell is `[-c/2, c/2) × ℝ`, and `H^{k+3}` is the space of the library
`Cyl.H ℝ Vec2 c 0 (k + 3) = Sob.W (Sob.cylinder c) (ρw^0) ℝ Vec2 (k + 3) 2`): for each `k` there
is an `ℝ`-linear choice `x ↦ g x` of continuous representatives such that `g x` is `C^{k+1}` and
`c`-periodic, represents every weak derivative `∂^β x`, `β` a word of length `≤ k + 1`, a.e. on
the cell (the word `β : Idx 2 (k + 1)` is regarded in `Idx 2 (k + 3)` by `Idx.castLE`; for
`β = Idx.zero` this is the value of `x`), and `‖D^j (g x) z‖ ≤ C ‖x‖` for all `j ≤ k + 1`, `z`. -/
def CylSobolevRep : Prop :=
  ∀ c : ℝ, 0 < c → 1 ≤ c → ∀ k : ℕ,
    ∃ (g : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3) →ₗ[ℝ] (Plane → Vec)) (C : ℝ),
      (∀ x, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (g x) ∧ Cyl.IsPeriodic c (g x)) ∧
      (∀ (x : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)) (β : Sob.Idx 2 (k + 1)),
        cellDeriv c (Sob.Idx.castLE (by omega : k + 1 ≤ k + 3) β) x =ᵐ[Cyl.cellμ c]
          Sob.iterD ((Sob.cylinder c).word β) (g x)) ∧
      (∀ x, ∀ j : ℕ, j ≤ k + 1 → ∀ z : Plane, ‖iteratedFDeriv ℝ j (g x) z‖ ≤ C * ‖x‖)

/-- **Uniqueness of continuous periodic representatives**: two continuous `c`-periodic functions
that agree a.e. on the cell `[-c/2, c/2) × ℝ` are equal (continuity gives equality on the closed
cell, periodicity everywhere). -/
def AePeriodicEq : Prop :=
  ∀ c : ℝ, 0 < c → ∀ g₁ g₂ : Plane → Vec, Continuous g₁ → Continuous g₂ →
    Cyl.IsPeriodic c g₁ → Cyl.IsPeriodic c g₂ → g₁ =ᵐ[Cyl.cellμ c] g₂ → g₁ = g₂


/-! ### Suggested cut of `CylSobolevRep` (density route; statements type-checked, assembly not yet
proved)

`CylSobolevRep` is obtained from the three statements below by the density argument: for
`x ∈ H^{k+3}` take smooth approximants `y_n = ofCylSmooth (u n) → x` (`CylSmoothDensity`); by
`CylSmoothSobolevBound` and the linearity of `ofCylSmooth`, `D^j (u n)` is uniformly Cauchy for
`j ≤ k + 1`, so `ContDiffLimitCauchy` gives the `C^{k+1}` limit `g x`; periodicity passes to the
limit; the cell `L²` convergence of the weak derivatives (continuity of `cellDeriv`) and the
uniform convergence of the classical derivatives give the a.e. identification (an a.e. convergent
subsequence); the bound passes to the limit; linearity of `x ↦ g x` follows from `AePeriodicEq`. -/

/-- **Density of smooth periodic fields at level `k + 3`** (`Sob.W.exists_seq_cylSmooth`,
`Lib/SobolevC/CylDensity.lean:760`; the level-`3` instance is `exists_smoothVecH3_sequence`,
`Lib/TrainB/P0RoughH3.lean:19`). -/
def CylSmoothDensity : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (k : ℕ) (x : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)),
    ∃ (u : ℕ → Plane → Vec) (hu : ∀ n, Sob.IsCylSmooth c (u n)),
      Tendsto (fun n => Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Cyl.Vec2) (k := k + 3) (p := 2) hc (u n) (hu n)) atTop (𝓝 x)

/-- **The Sobolev inequality for smooth periodic fields** (`H^{k+3}(cell) ⊂ C^{k+1}_b`, the
quantitative core of the Sobolev embedding on the cylinder): there is `C` (depending on `c`, `k`)
with `‖D^j f z‖ ≤ C ‖f‖_{H^{k+3}}` for every smooth periodic field `f` (vanishing for `|η|`
large), `j ≤ k + 1`, `z`.  (Only `c ≥ 1` is needed (and available in the application), which is the hypothesis of the library
`H²` bound; real-valued, centred-cell version of it:
`B0151.enorm_le_H2`, `B0151.enorm_derivWord_le` in `Units/B0151/Linf.lean`; `sq_norm_le_cyl`,
`sq_sup_q_le` in `Lib/Cylinder/SupBound.lean`; cell change `Lib/TrainB/CellBridge.lean`,
`Short/PartI/Tasks/CylinderInterpolation/CellBridge.lean`.) -/
def CylSmoothSobolevBound : Prop :=
  ∀ (c : ℝ) (hc : 0 < c), 1 ≤ c → ∀ k : ℕ, ∃ C : ℝ, ∀ (f : Plane → Vec) (hf : Sob.IsCylSmooth c f),
    ∀ j : ℕ, j ≤ k + 1 → ∀ z : Plane,
      ‖iteratedFDeriv ℝ j f z‖ ≤ C * ‖Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Cyl.Vec2) (k := k + 3) (p := 2) hc f hf‖

/-- **Limits of uniformly Cauchy `C^m` sequences** (Mathlib gap; induction on the order using
`hasFDerivAt_of_tendstoUniformly`, `Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`): if
`f n` is `C^m`, `f n → g` pointwise and `D^j (f n)` is uniformly Cauchy on the plane for `j ≤ m`, then `g` is
`C^m` and `D^j (f n) → D^j g` uniformly for `j ≤ m`. -/
def ContDiffLimitCauchy : Prop :=
  ∀ (m : ℕ) (f : ℕ → Plane → Vec) (g : Plane → Vec),
    (∀ n, ContDiff ℝ (m : WithTop ℕ∞) (f n)) →
    (∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) →
    (∀ j : ℕ, j ≤ m → UniformCauchySeqOn (fun n => iteratedFDeriv ℝ j (f n)) atTop univ) →
    ContDiff ℝ (m : WithTop ℕ∞) g ∧
      ∀ j : ℕ, j ≤ m →
        TendstoUniformly (fun n => iteratedFDeriv ℝ j (f n)) (iteratedFDeriv ℝ j g) atTop

/-- **`SpatialRepFromPersistent` from the cylinder Sobolev embedding and uniqueness.** -/
theorem spatialRepFromPersistent_of (h1 : CylSobolevRep) (h2 : AePeriodicEq) :
    SpatialRepFromPersistent := by
  intro ν c T hν hc hc1 hT u _ hP
  choose uk huk using hP
  choose g C hgC using fun k => h1 c hc hc1 k
  have hcont : ∀ k x, Continuous (g k x) := fun k x => ((hgC k).1 x).1.continuous
  have hper : ∀ k x, Cyl.IsPeriodic c (g k x) := fun k x => ((hgC k).1 x).2
  -- the lifts all have the value of `u`
  have hval : ∀ (k : ℕ) (t : Icc (0 : ℝ) T),
      cellDeriv c (Sob.Idx.zero : Sob.Idx 2 (k + 3)) (uk k t) =
        cellDeriv c (Sob.Idx.zero : Sob.Idx 2 3) (u t) := by
    intro k t
    rw [← huk k t]
    rfl
  -- level independence of the continuous representative
  have key : ∀ (k : ℕ) (t : Icc (0 : ℝ) T), g k (uk k t) = g 0 (uk 0 t) := by
    intro k t
    refine h2 c hc _ _ (hcont k _) (hcont 0 _) (hper k _) (hper 0 _) ?_
    have e1 := (hgC k).2.1 (uk k t) Sob.Idx.zero
    have e0 := (hgC 0).2.1 (uk 0 t) Sob.Idx.zero
    simp only [Sob.Idx.castLE_zero, Sob.TestDomain.word_zero, Sob.iterD_nil] at e1 e0
    rw [hval k t] at e1
    rw [hval 0 t] at e0
    exact e1.symm.trans e0
  let w : ℝ → Plane → Vec := fun s => g 0 (uk 0 (Set.projIcc 0 T hT.le s))
  have hw : ∀ (k : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T), w s = g k (uk k ⟨s, hs⟩) := by
    intro k s hs
    simp only [w, Set.projIcc_of_mem hT.le hs]
    exact (key k ⟨s, hs⟩).symm
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [contDiff_infty]
    intro n
    rw [hw n s hs]
    exact ((hgC n).1 _).1.of_le (by exact_mod_cast Nat.le_succ n)
  · intro s hs
    rw [hw 0 s hs]
    exact hper 0 _
  · intro s α
    have e := (hgC 2).2.1 (uk 2 s) α
    have hs : w s.1 = g 2 (uk 2 s) := hw 2 s.1 s.2
    rw [hs]
    have : (vecH3CellDerivCLM α (u s) : Plane → Vec) =
        cellDeriv c (Sob.Idx.castLE (by omega : 2 + 1 ≤ 2 + 3) α) (uk 2 s) := by
      rw [← huk 2 s]
      rfl
    rw [this]
    exact e
  · intro k
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ t : Icc (0 : ℝ) T, ‖uk k t‖ ≤ B := by
      obtain ⟨B, hB⟩ := (isCompact_univ (X := Icc (0 : ℝ) T)).exists_bound_of_continuousOn
        (uk k).continuous.continuousOn
      exact ⟨B, fun t => hB t (mem_univ t)⟩
    refine ⟨|C k| * B, fun s hs z => ?_⟩
    rw [hw k s hs]
    calc ‖iteratedFDeriv ℝ k (g k (uk k ⟨s, hs⟩)) z‖ ≤ C k * ‖uk k ⟨s, hs⟩‖ :=
          (hgC k).2.2 _ k (Nat.le_succ k) z
      _ ≤ |C k| * ‖uk k ⟨s, hs⟩‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |C k| * B := mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
  · intro k
    rw [Metric.continuousOn_iff]
    rintro ⟨s0, z0⟩ ⟨hs0, -⟩ ε hε
    have hK : 0 < |C k| + 1 := by positivity
    have hε2 : 0 < ε / (2 * (|C k| + 1)) := by positivity
    obtain ⟨δ1, hδ1, hu1⟩ :=
      Metric.continuous_iff.1 (uk k).continuous ⟨s0, hs0⟩ (ε / (2 * (|C k| + 1))) hε2
    have hD0 : Continuous (iteratedFDeriv ℝ k (g k (uk k ⟨s0, hs0⟩))) :=
      ((hgC k).1 _).1.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_succ k)
    obtain ⟨δ2, hδ2, hz2⟩ := Metric.continuous_iff.1 hD0 z0 (ε / 2) (by positivity)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
    rintro ⟨s, z⟩ ⟨hs, -⟩ hdist
    have hds : dist s s0 < min δ1 δ2 := lt_of_le_of_lt (le_max_left _ _) hdist
    have hdz : dist z z0 < min δ1 δ2 := lt_of_le_of_lt (le_max_right _ _) hdist
    have hu : dist (uk k ⟨s, hs⟩) (uk k ⟨s0, hs0⟩) < ε / (2 * (|C k| + 1)) :=
      hu1 _ (lt_of_lt_of_le hds (min_le_left _ _))
    have hzz : dist (iteratedFDeriv ℝ k (g k (uk k ⟨s0, hs0⟩)) z)
        (iteratedFDeriv ℝ k (g k (uk k ⟨s0, hs0⟩)) z0) < ε / 2 :=
      hz2 z (lt_of_lt_of_le hdz (min_le_right _ _))
    show dist (iteratedFDeriv ℝ k (w s) z) (iteratedFDeriv ℝ k (w s0) z0) < ε
    rw [hw k s hs, hw k s0 hs0]
    have hsub : iteratedFDeriv ℝ k (g k (uk k ⟨s, hs⟩)) z -
        iteratedFDeriv ℝ k (g k (uk k ⟨s0, hs0⟩)) z =
        iteratedFDeriv ℝ k (g k (uk k ⟨s, hs⟩ - uk k ⟨s0, hs0⟩)) z := by
      rw [map_sub]
      exact (iteratedFDeriv_sub_apply (((hgC k).1 _).1.contDiffAt.of_le
        (by exact_mod_cast Nat.le_succ k)) (((hgC k).1 _).1.contDiffAt.of_le
        (by exact_mod_cast Nat.le_succ k))).symm
    have h1' : dist (iteratedFDeriv ℝ k (g k (uk k ⟨s, hs⟩)) z)
        (iteratedFDeriv ℝ k (g k (uk k ⟨s0, hs0⟩)) z) < ε / 2 := by
      rw [dist_eq_norm, hsub]
      refine lt_of_le_of_lt ((hgC k).2.2 _ k (Nat.le_succ k) z) ?_
      rw [dist_eq_norm] at hu
      calc C k * ‖uk k ⟨s, hs⟩ - uk k ⟨s0, hs0⟩‖
          ≤ |C k| * ‖uk k ⟨s, hs⟩ - uk k ⟨s0, hs0⟩‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ ≤ (|C k| + 1) * ‖uk k ⟨s, hs⟩ - uk k ⟨s0, hs0⟩‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        _ < (|C k| + 1) * (ε / (2 * (|C k| + 1))) :=
            mul_lt_mul_of_pos_left hu hK
        _ = ε / 2 := by field_simp
    calc dist (iteratedFDeriv ℝ k (g k (uk k ⟨s, hs⟩)) z)
          (iteratedFDeriv ℝ k (g k (uk k ⟨s0, hs0⟩)) z0)
        ≤ dist (iteratedFDeriv ℝ k (g k (uk k ⟨s, hs⟩)) z)
            (iteratedFDeriv ℝ k (g k (uk k ⟨s0, hs0⟩)) z) +
          dist (iteratedFDeriv ℝ k (g k (uk k ⟨s0, hs0⟩)) z)
            (iteratedFDeriv ℝ k (g k (uk k ⟨s0, hs0⟩)) z0) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1' hzz
      _ = ε := by ring

end UnforcedLeray.Short.PartI
