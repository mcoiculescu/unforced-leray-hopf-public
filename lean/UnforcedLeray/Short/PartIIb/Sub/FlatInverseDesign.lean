import UnforcedLeray.Short.PartIIb.StatementsMixed
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5

/-!
# Part II-b, `ORG:PartII-b/flat-inverse-design`: unserialized design of the `FlatInverse` chain

Source of record: `the November 2 reference manuscript` (SP), lines 2119–2344.

This module defines the concrete intermediate structures and exact Lean `Prop`s for the 8-step
chain proving `FlatInverse` (`PartII-b:F10`, SP 2326–2344), with fixed slow data
`(Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile)` (`0 < Sig`,
`Blueprint.Planar.IsGrowingEigenpair lam q`, `0 < dm`, `BgRegime p d dm dp`, `p.ν ≤ ν₀`,


* `F1` (`Sub/PartII-b_F1.lean`, imported): `InteractionCylinderComparison` and
  `InteractionCollectiveCompact` (SP 2119–2140, `short-bg:interaction-cylinder`);
* `F2` (`BlockDichotomy`, SP 2141–2171): coupled cylinder vorticity propagator `U(t, s)` on
  `X_{m,c}` (`IsCoupledPropagator`), frozen growing/complementary coordinate splittings at block
  grid times `t_n = n L` (`N L = T = Σ/ν`), and block matrix bounds
  `‖a_n⁻¹‖ ≤ ½ e^{-b'L}`, `‖d_n‖ ≤ ½ e^{a'L}`, `‖b_n‖, ‖c_n‖ ≤ η` (`BlockFactorizationData.Valid`);
* `F3` (`DichotomyProjections`, SP 2172–2188, `short-bg:graphs`): forward and backward graph
  transforms `ξ_n, ζ_n` from `BlockDichotomy` and `GraphTransformLemma` (`PartII-b:T06`), yielding
  complementary invariant projections `Π_n^u, Π_n^c` with forward center bound `e^{a'(t_k - t_j)}`
  and backward unstable bound `e^{-b'(t_k - t_j)}` (`DiscreteDichotomyData.Valid`);
* `F4` (`MixedGreenSelector`, SP 2189–2210, `short-bg:green`, `short-bg:green-bound`):
  intermediate-time projections `Π^u(t) = J_t B_n⁻¹ F_t`, `Π^c(t) = I - Π^u(t)`, and the linear
  Green selector `(ω, α)` solving the forced coupled vorticity equation on `[0, T]` with initial
  value in the entrance pair span, vanishing terminal growing coordinate, zero circulation, and
  `sup_{[0, T]} ‖ω(s)‖_{X_{m,c}} + ‖α‖ ≤ C e^{a'T} ‖f‖_{L¹(0, T; X_{m,c})}`;
* `F5` (`Sub/PartII-b_F5.lean`, imported): `BodySourceBound` (SP 2211–2242, `short-bg:source`);
* `F6` (`EarlyBound`, SP 2254–2268, `short-bg:early`): zero-circulation cylinder Biot–Savart
  `X_{m,c} → H¹(C_c)` bound with polynomial `c` cost (`CylinderBiotSavartH1`) and the early
  meridional correction bound `sup_{(0, T]} ‖z(s)‖_{H¹} + ‖α‖ ≤ C ν^{-k} e^{a'T} ‖F‖_{H_p}`;
* `F7` (`TailSourceAndGlobalEnergy`, SP 2269–2295, `short-bg:tail-source`,
  `short-bg:global-energy`): tail source bound on `s ≥ 1` (`TailSource`) and global continuation of
  the meridional correction `z` with
  `M_z = sup_{s > 0} ‖z(s)‖_{H¹} ≤ C ν^{-k} exp((a'Σ + C_late/(1+Σ))/ν + C_late ν³) ‖F‖_{H_p}`
  (`GlobalEnergy`, where `C_late > 0` from `short-bg:train-late` is independent of `Σ` and `a'`);
* `F8` (`LocalSmoothing`, SP 2296–2312): `H¹ → H²` local smoothing of the meridional correction
  equation on `(0, T]` in `L^p(s^{13/8} ds; H²)` and on `(T, ∞)` in `L^p(s^{-9/8} ds; H²)`, and the
  resulting `H_p` bound on the convective interaction `s B_v z = flatK p.train z zq zη`;
* `F9` (`FlatReconstruction`, SP 2313–2341, `short-bg:flat-reconstruction`): explicit `s < T` and
  `s > T` bounds on `s B_v b_0` in `H_p`, `H_p` bound on `flatColumn`, and the global flat
  reconstruction `b_0 + z = Eα + T_0 f` with `f = F - s B_v(b_0 + z) - s(∂_s - νΔ)Eα`;
* `F10` (`FlatInverse`, `StatementsMixed.lean`, SP 2326–2344): existence of `K_0, 𝒞_0` and of the
  bounded linear right inverse `R_0 : H_p → H_p × ℝ²` with `‖R_0‖ ≤ C ν^{-k} e^{m/ν}` by choosing
  `Σ` large and then `a'` small.

## Proved here (zero `sorry`)

* `graphCoordU_comp_graphEmbedU`, `graphProjU_idem`: algebraic idempotence of the graph-transform
  projection `(ι + κ ξ)(I - ζ ξ)⁻¹(π - ζ ρ)` for `PartII-b:F3`;
* `intermProjU_idem`: algebraic idempotence of the intermediate-time projection
  `Π^u(t) = J_t B_n⁻¹ F_t` for `PartII-b:F4`;
* `flatInverse_rate_le_of_thresholds`: the threshold inequality
  `(a' Σ + C_late / (1 + Σ)) / ν + C_late ν³ ≤ m / ν` for `Σ ≥ max 1 (4 C_late / m)`,
  `a' ≤ m / (4 Σ)`, and small `ν`, used in `PartII-b:F10`;
* `flatInverse_of_chain`: full chain assembly of `FlatInverse` from `F1` through `F10`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Periodized planar entrance modes and the coupled cylinder propagator (`F2`–`F4`) -/

/-- The angular factor `e^{2iϑ} = (q + iη)² / (q² + η²)` on `B0579.Plane = ℝ × ℝ`. -/
def angTwoPlanar (x : B0579.Plane) : ℂ :=
  ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) ^ 2 / ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ)

/-- The 2D planar angular-two mode `q(|x|) e^{2iϑ}` of a radial profile `q`. -/
def planarMode2D (q : Blueprint.Planar.Profile) (x : B0579.Plane) : ℂ :=
  q (Real.sqrt (x.1 ^ 2 + x.2 ^ 2)) * angTwoPlanar x

/-- The dilated planar mode `(J_a q)(x) = a^{-2} (q e^{2iϑ})(x / √a)` at scale `a = 1 + ν t`
(SP 931–953, 2119–2121). -/
def dilPlanarMode (q : Blueprint.Planar.Profile) (a : ℝ) (x : B0579.Plane) : ℂ :=
  ((a ^ (-2 : ℝ) : ℝ) : ℂ) * planarMode2D q (x.1 / Real.sqrt a, x.2 / Real.sqrt a)

/-- Periodization `(P_c g)(q, η) = ∑_{k ∈ ℤ} g(q + k c, η)` on the cylinder of period `c`. -/
def periodizePlanar (c : ℝ) (g : B0579.Plane → ℂ) (x : B0579.Plane) : ℂ :=
  ∑' k : ℤ, g (x.1 + k * c, x.2)

/-- The two real periodized direct vorticity modes `(2 Re P_c J_a q, -2 Im P_c J_a q)` spanning
the frozen growing subspace `E_t` at scale `a = 1 + ν t` (SP 2167–2171, 2347–2358). -/
def frozenDirectMode (q : Blueprint.Planar.Profile) (c a : ℝ) (i : Fin 2) (x : B0579.Plane) : ℝ :=
  ![2 * (periodizePlanar c (dilPlanarMode q a) x).re,
    -2 * (periodizePlanar c (dilPlanarMode q a) x).im] i

/-- At `t = 0` (`a = 1`), the `i`-th entrance vorticity mode on the cylinder of period `p.c`,
equal to `Δ(p.frozenStream i)`. -/
def entranceVorticity (p : Params) (i : Fin 2) (x : B0579.Plane) : ℝ :=
  frozenDirectMode p.mode p.c 1 i x

/-- Linear combination `∑_{i=0}^1 α_i entranceVorticity p i` for an entrance coefficient
`α ∈ ℝ² = E2`. -/
def entranceVorticityComb (p : Params) (α : E2) (x : B0579.Plane) : ℝ :=
  ∑ i : Fin 2, α i * entranceVorticity p i x

/-- Zero circulation on the centered cell `B0579.cell c` for a real vorticity field. -/
def HasZeroCirculationR (c : ℝ) (f : B0579.Plane → ℝ) : Prop :=
  IntegrableOn f (B0579.cell c) volume ∧ ∫ x in B0579.cell c, f x = 0

/-- The tested integrand of the unforced coupled cylinder vorticity equation
`ω_s = (ν Δ - v_c(s)·∇ + A_c(s)) ω` at age `r` against a cylinder test `φ` (SP 2080,
`short-bg:actual-cylinder`). -/
def cylCoupledIntegrand {ν c : ℝ} (tr : B0140.TrainSol ν c) (ω : B0579.Plane → ℝ) (r : ℝ)
    (φ : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  cylFreeIntegrand tr ω r φ x + cylAc tr r ω x * φ x

/-- `U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)` is the coupled cylinder vorticity propagator on
`[0, p.H]` (`p.H = p.ageCut / p.ν`, SP 2076–2082, 2147–2155): it obeys the evolution-family laws
`U(s, s) = I` and `U(t, r) U(r, s) = U(t, s)` for `0 ≤ s ≤ r ≤ t ≤ p.H`, is strongly continuous in
`t`, preserves zero circulation (`HasZeroCirculationR p.c`), and solves the weak coupled cylinder
vorticity equation `(short-bg:actual-cylinder)`. -/
structure IsCoupledPropagator (m : ℝ) (p : Params)
    (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)) : Prop where
  id_self : ∀ s ∈ Icc 0 p.H, U s s = ContinuousLinearMap.id ℝ (Xmc p.c m)
  comp_cocycle : ∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → t ≤ p.H →
    (U t r).comp (U r s) = U t s
  strongCont : ∀ s ∈ Icc 0 p.H, ∀ f : Xmc p.c m,
    ContinuousOn (fun t => U t s f) (Icc s p.H)
  zeroCirc : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
    ∀ f : Xmc p.c m, HasZeroCirculationR p.c f → HasZeroCirculationR p.c (U t s f)
  integrable : ∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ →
    ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ p.H → ∀ f : Xmc p.c m,
      IntegrableOn (cylCoupledIntegrand p.train (U r s f) r φ) (B0579.cell p.c) volume
  timeIntegrable : ∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ∀ f : Xmc p.c m,
      IntervalIntegrable
        (fun r => ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (U r s f) r φ x) volume s t
  weak : ∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → ∀ f : Xmc p.c m,
      ∫ x in B0579.cell p.c, (U t s f) x * φ x =
        (∫ x in B0579.cell p.c, f x * φ x) +
          ∫ r in s..t, ∫ x in B0579.cell p.c, cylCoupledIntegrand p.train (U r s f) r φ x

/-! ## 2. `PartII-b:F2`: Block factorization and dichotomy (`BlockDichotomy`, SP 2141–2171) -/

/-- Data of the frozen growing/complementary block decomposition of the coupled propagator `U` on
the grid `t_n = n * L` (`0 ≤ n ≤ N`, `N * L = p.H = Σ / ν`) on `Xmc p.c m` (SP 2145–2171).
The complementary spaces at the grid times are parameterized by a single closed reference subspace
`F : Submodule ℝ (Xmc p.c m)` (e.g. `ker π_0`), so that the block operators `(a_n, b_n, c_n, d_n)`
acts on `E2 ⊕ F` with fixed Banach spaces `E2` and `F` matching `GraphTransformLemma`. -/
structure BlockFactorizationData (m : ℝ) (p : Params)
    (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)) where
  /-- Number of blocks covering `[0, p.H]`. -/
  N : ℕ
  /-- Block length `L`, with `N * L = p.H`. -/
  L : ℝ
  /-- Reference closed complementary subspace `F ⊂ X_{m,c}`. -/
  F : Submodule ℝ (Xmc p.c m)
  /-- Completeness of `F`. -/
  complete_F : CompleteSpace F
  /-- Frozen 2-dimensional growing-space embeddings `ι_n : ℝ² → X_{m,c}` at `t_n = n * L`. -/
  ι : ℕ → (E2 →L[ℝ] Xmc p.c m)
  /-- Frozen 2-dimensional growing-space projections `π_n : X_{m,c} → ℝ²` at `t_n = n * L`. -/
  π : ℕ → (Xmc p.c m →L[ℝ] E2)
  /-- Frozen complementary-space embeddings `κ_n : F → X_{m,c}` at `t_n = n * L`. -/
  κ : ℕ → (F →L[ℝ] Xmc p.c m)
  /-- Frozen complementary-space projections `ρ_n : X_{m,c} → F` at `t_n = n * L`. -/
  ρ : ℕ → (Xmc p.c m →L[ℝ] F)
  /-- Inverse `a_n⁻¹` of the growing block `a_n = π_{n+1} U(t_{n+1}, t_n) ι_n` on `[t_n, t_{n+1}]`. -/
  ainv : ℕ → (E2 →L[ℝ] E2)

namespace BlockFactorizationData

variable {m : ℝ} {p : Params} {U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
  (D : BlockFactorizationData m p U)

/-- Grid time `t_n = n * L`. -/
def t (n : ℕ) : ℝ := (n : ℝ) * D.L

/-- Upper-left growing block `a_n = π_{n+1} U(t_{n+1}, t_n) ι_n : E2 →L[ℝ] E2`. -/
def a (n : ℕ) : E2 →L[ℝ] E2 :=
  (D.π (n + 1)).comp ((U (D.t (n + 1)) (D.t n)).comp (D.ι n))

/-- Upper-right coupling block `b_n = π_{n+1} U(t_{n+1}, t_n) κ_n : F →L[ℝ] E2`. -/
def b (n : ℕ) : D.F →L[ℝ] E2 :=
  (D.π (n + 1)).comp ((U (D.t (n + 1)) (D.t n)).comp (D.κ n))

/-- Lower-left coupling block `c_n = ρ_{n+1} U(t_{n+1}, t_n) ι_n : E2 →L[ℝ] F`. -/
def c (n : ℕ) : E2 →L[ℝ] D.F :=
  (D.ρ (n + 1)).comp ((U (D.t (n + 1)) (D.t n)).comp (D.ι n))

/-- Lower-right complementary block `d_n = ρ_{n+1} U(t_{n+1}, t_n) κ_n : F →L[ℝ] F`. -/
def d (n : ℕ) : D.F →L[ℝ] D.F :=
  (D.ρ (n + 1)).comp ((U (D.t (n + 1)) (D.t n)).comp (D.κ n))

/-- Validity of the block factorization data with block-length window `[L₀, 2 L₀]`, dichotomy
exponents `(a', b')`, coordinate/short-time constant `M_coord`, and off-diagonal tolerance `η`
(SP 2145–2171): `‖a_n⁻¹‖ ≤ ½ e^{-b' L}`, `‖d_n‖ ≤ ½ e^{a' L}` (strict margins below
`e^{-b' L}, e^{a' L}`, SP 2161–2162), `‖b_n‖ ≤ η`, `‖c_n‖ ≤ η`. -/
structure Valid (L₀ a' b' M_coord η : ℝ) : Prop where
  N_pos : 1 ≤ D.N
  L_bounds : L₀ ≤ D.L ∧ D.L ≤ 2 * L₀
  total_age : (D.N : ℝ) * D.L = p.H
  entrance_eq : ∀ α : E2,
    (D.ι 0 α : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α
  zeroCirc_ι : ∀ n ≤ D.N, ∀ α : E2, HasZeroCirculationR p.c (D.ι n α)
  proj_id_E : ∀ n ≤ D.N, (D.π n).comp (D.ι n) = ContinuousLinearMap.id ℝ E2
  proj_id_F : ∀ n ≤ D.N, (D.ρ n).comp (D.κ n) = ContinuousLinearMap.id ℝ D.F
  proj_orth_EF : ∀ n ≤ D.N, (D.π n).comp (D.κ n) = 0
  proj_orth_FE : ∀ n ≤ D.N, (D.ρ n).comp (D.ι n) = 0
  decomp_id : ∀ n ≤ D.N,
    (D.ι n).comp (D.π n) + (D.κ n).comp (D.ρ n) = ContinuousLinearMap.id ℝ (Xmc p.c m)
  coord_norm : ∀ n ≤ D.N,
    ‖D.ι n‖ ≤ M_coord ∧ ‖D.π n‖ ≤ M_coord ∧ ‖D.κ n‖ ≤ M_coord ∧ ‖D.ρ n‖ ≤ M_coord
  short_prop_norm : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H → t - s ≤ 2 * L₀ → ‖U t s‖ ≤ M_coord
  block_inv_left : ∀ n < D.N, D.ainv n * D.a n = 1
  block_inv_right : ∀ n < D.N, D.a n * D.ainv n = 1
  block_ainv_norm : ∀ n < D.N, ‖D.ainv n‖ ≤ (1 / 2 : ℝ) * Real.exp (-b' * D.L)
  block_d_norm : ∀ n < D.N, ‖D.d n‖ ≤ (1 / 2 : ℝ) * Real.exp (a' * D.L)
  block_b_norm : ∀ n < D.N, ‖D.b n‖ ≤ η
  block_c_norm : ∀ n < D.N, ‖D.c n‖ ≤ η

end BlockFactorizationData

/-- **Target `Prop` of `PartII-b:F2` (`BlockDichotomy`, SP 2141–2171)**: for every `m > 8`, fixed
slow data `(Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile)` (`0 < Sig`,
`IsGrowingEigenpair lam q`), dichotomy rates `0 < a' < b' < Re λ / (1 + Σ)²`, and regime bounds
`0 < d₋ ≤ d₊`, there exist a base block length `L₀ ≥ 1` and a uniform coordinate/short-time
bound `M_coord ≥ 1` such that for every off-diagonal tolerance `η > 0`, there is `ν₀ > 0` such that
at every parameter point of `BgRegime` with `p.ν ≤ ν₀`, `p.ageCut = Sig`, `p.mode = q`, the coupled
cylinder vorticity propagator `U` exists and admits a valid block factorization with off-diagonal
norm at most `η`. -/
def BlockDichotomy : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < lam.re / (1 + Sig) ^ 2 →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (L₀ M_coord : ℝ), 1 ≤ L₀ ∧ 1 ≤ M_coord ∧
      ∀ η : ℝ, 0 < η → ∃ ν₀ : ℝ, 0 < ν₀ ∧
        ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
          ∃ (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
            (D : BlockFactorizationData m p U),
            IsCoupledPropagator m p U ∧ D.Valid L₀ a' b' M_coord η

/-! ## 3. `PartII-b:F3`: Discrete invariant projections (`DichotomyProjections`, SP 2172–2188) -/

/-- Algebraic helper for `PartII-b:F3`: unstable graph embedding `I^u = ι + κ ∘ ξ`. -/
def graphEmbedU {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : E2 →L[ℝ] X) (κ : F →L[ℝ] X) (ξ : E2 →L[ℝ] F) : E2 →L[ℝ] X :=
  ι + κ.comp ξ

/-- Algebraic helper for `PartII-b:F3`: unstable graph coordinate map
`P^u = W ∘ (π - ζ ∘ ρ)` where `W = (I - ζ ∘ ξ)⁻¹`. -/
def graphCoordU {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (π : X →L[ℝ] E2) (ρ : X →L[ℝ] F) (ζ : F →L[ℝ] E2) (W : E2 →L[ℝ] E2) : X →L[ℝ] E2 :=
  W.comp (π - ζ.comp ρ)

/-- Algebraic helper for `PartII-b:F3`: unstable projection `Π^u = I^u ∘ P^u`. -/
def graphProjU {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : E2 →L[ℝ] X) (π : X →L[ℝ] E2) (κ : F →L[ℝ] X) (ρ : X →L[ℝ] F)
    (ξ : E2 →L[ℝ] F) (ζ : F →L[ℝ] E2) (W : E2 →L[ℝ] E2) : X →L[ℝ] X :=
  (graphEmbedU ι κ ξ).comp (graphCoordU π ρ ζ W)

theorem graphCoordU_comp_graphEmbedU {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : E2 →L[ℝ] X) (π : X →L[ℝ] E2) (κ : F →L[ℝ] X) (ρ : X →L[ℝ] F)
    (ξ : E2 →L[ℝ] F) (ζ : F →L[ℝ] E2) (W : E2 →L[ℝ] E2)
    (hπι : π.comp ι = ContinuousLinearMap.id ℝ E2)
    (hρκ : ρ.comp κ = ContinuousLinearMap.id ℝ F)
    (hπκ : π.comp κ = 0) (hρι : ρ.comp ι = 0)
    (hW : W * (1 - ζ.comp ξ) = 1) :
    (graphCoordU π ρ ζ W).comp (graphEmbedU ι κ ξ) = ContinuousLinearMap.id ℝ E2 := by
  have h1 : (π - ζ.comp ρ).comp (ι + κ.comp ξ) = 1 - ζ.comp ξ := by
    apply ContinuousLinearMap.ext
    intro w
    simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply, map_add]
    have hπι_w := DFunLike.congr_fun hπι w
    have hπκ_w := DFunLike.congr_fun hπκ (ξ w)
    have hρι_w := DFunLike.congr_fun hρι w
    have hρκ_w := DFunLike.congr_fun hρκ (ξ w)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      zero_apply] at hπι_w hπκ_w hρι_w hρκ_w
    rw [hπι_w, hπκ_w, hρι_w, hρκ_w, map_zero, sub_zero, zero_sub,
      one_apply_eq_self, sub_eq_add_neg]
  unfold graphCoordU graphEmbedU
  rw [ContinuousLinearMap.comp_assoc, h1]
  exact hW

theorem graphProjU_idem {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : E2 →L[ℝ] X) (π : X →L[ℝ] E2) (κ : F →L[ℝ] X) (ρ : X →L[ℝ] F)
    (ξ : E2 →L[ℝ] F) (ζ : F →L[ℝ] E2) (W : E2 →L[ℝ] E2)
    (hπι : π.comp ι = ContinuousLinearMap.id ℝ E2)
    (hρκ : ρ.comp κ = ContinuousLinearMap.id ℝ F)
    (hπκ : π.comp κ = 0) (hρι : ρ.comp ι = 0)
    (hW : W * (1 - ζ.comp ξ) = 1) :
    (graphProjU ι π κ ρ ξ ζ W).comp (graphProjU ι π κ ρ ξ ζ W) =
      graphProjU ι π κ ρ ξ ζ W := by
  unfold graphProjU
  rw [ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (graphCoordU π ρ ζ W),
    graphCoordU_comp_graphEmbedU ι π κ ρ ξ ζ W hπι hρκ hπκ hρι hW,
    ContinuousLinearMap.id_comp]

/-- Discrete invariant splitting data at the grid times `t_n = n * L` (`0 ≤ n ≤ N`, `N * L = p.H`)
constructed by the forward/backward graph recursion `short-bg:graphs` (SP 2172–2188). -/
structure DiscreteDichotomyData (m : ℝ) (p : Params)
    (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)) where
  /-- Number of blocks covering `[0, p.H]`. -/
  N : ℕ
  /-- Block length `L`, with `N * L = p.H`. -/
  L : ℝ
  /-- Unstable-subspace embeddings `I_n^u : E2 →L[ℝ] X_{m,c}` at `t_n = n * L`. -/
  Iu : ℕ → (E2 →L[ℝ] Xmc p.c m)
  /-- Unstable-subspace coordinate projections `P_n^u : X_{m,c} →L[ℝ] E2` at `t_n = n * L`. -/
  Pu : ℕ → (Xmc p.c m →L[ℝ] E2)
  /-- Unstable projections `Π_n^u = I_n^u ∘ P_n^u` on `X_{m,c}` at `t_n = n * L`. -/
  Piu : ℕ → (Xmc p.c m →L[ℝ] Xmc p.c m)
  /-- Center/complementary projections `Π_n^c = I - Π_n^u` on `X_{m,c}` at `t_n = n * L`. -/
  Pic : ℕ → (Xmc p.c m →L[ℝ] Xmc p.c m)
  /-- Invertible 2×2 unstable block `B_n = P_{n+1}^u U(t_{n+1}, t_n) I_n^u` on `[t_n, t_{n+1}]`. -/
  Bn : ℕ → (E2 →L[ℝ] E2)
  /-- Inverse `M_n = B_n⁻¹ : E2 →L[ℝ] E2`. -/
  Mn : ℕ → (E2 →L[ℝ] E2)

namespace DiscreteDichotomyData

variable {m : ℝ} {p : Params} {U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
  (D : DiscreteDichotomyData m p U)

/-- Grid time `t_n = n * L`. -/
def t (n : ℕ) : ℝ := (n : ℝ) * D.L

/-- Validity of the discrete invariant splitting (`short-bg:graphs`, SP 2172–2188):
projections are uniformly bounded by `C_proj`, commute with `U(t_{n+1}, t_n)`, have `ξ_0 = 0`
(so `Iu 0` is the entrance pair) and `ζ_N = 0`, and obey the forward center bound
`C_proj e^{a'(t_k - t_j)}` and backward unstable bound `C_proj e^{-b'(t_k - t_j)}`. -/
structure Valid (L₀ a' b' C_proj : ℝ) : Prop where
  N_pos : 1 ≤ D.N
  L_bounds : L₀ ≤ D.L ∧ D.L ≤ 2 * L₀
  total_age : (D.N : ℝ) * D.L = p.H
  entrance_eq : ∀ α : E2,
    (D.Iu 0 α : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α
  zeroCirc_Iu : ∀ n ≤ D.N, ∀ α : E2, HasZeroCirculationR p.c (D.Iu n α)
  proj_rel : ∀ n ≤ D.N,
    (D.Pu n).comp (D.Iu n) = ContinuousLinearMap.id ℝ E2 ∧
    D.Piu n = (D.Iu n).comp (D.Pu n) ∧
    D.Pic n = ContinuousLinearMap.id ℝ (Xmc p.c m) - D.Piu n
  norm_bounds : ∀ n ≤ D.N,
    ‖D.Iu n‖ ≤ C_proj ∧ ‖D.Pu n‖ ≤ C_proj ∧ ‖D.Piu n‖ ≤ C_proj ∧ ‖D.Pic n‖ ≤ C_proj
  short_prop_norm : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ p.H → r - s ≤ D.L → ‖U r s‖ ≤ C_proj
  block_inv : ∀ n < D.N,
    D.Mn n * D.Bn n = 1 ∧ D.Bn n * D.Mn n = 1 ∧ ‖D.Mn n‖ ≤ Real.exp (-b' * D.L)
  block_intertwine : ∀ n < D.N,
    (U (D.t (n + 1)) (D.t n)).comp (D.Iu n) = (D.Iu (n + 1)).comp (D.Bn n) ∧
    (D.Pu (n + 1)).comp (U (D.t (n + 1)) (D.t n)) = (D.Bn n).comp (D.Pu n)
  forward_center_bound : ∀ j k : ℕ, j ≤ k → k ≤ D.N →
    ‖(U (D.t k) (D.t j)).comp (D.Pic j)‖ ≤ C_proj * Real.exp (a' * (D.t k - D.t j))
  backward_unstable_bound : ∀ j k : ℕ, j ≤ k → k ≤ D.N →
    ∃ M_jk : E2 →L[ℝ] E2,
      (U (D.t k) (D.t j)).comp ((D.Iu j).comp M_jk) = D.Iu k ∧
      M_jk.comp ((D.Pu k).comp (U (D.t k) (D.t j))) = D.Pu j ∧
      ‖M_jk‖ ≤ Real.exp (-b' * (D.t k - D.t j)) ∧
      ‖(D.Iu j).comp (M_jk.comp (D.Pu k))‖ ≤ C_proj * Real.exp (-b' * (D.t k - D.t j))

end DiscreteDichotomyData

/-- **Target `Prop` of `PartII-b:F3` (`DichotomyProjections`, SP 2172–2188)**: from
`BlockDichotomy` and `GraphTransformLemma` (`PartII-b:T06`), the discrete invariant projections
`Π_n^u, Π_n^c` exist at the grid times `t_n = n * L` (`N * L = p.H`), are uniformly bounded,
commute with the block propagators, and satisfy the `e^{a'(t_k - t_j)}` forward center bound and
`e^{-b'(t_k - t_j)}` backward unstable bound. -/
def DichotomyProjections : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < lam.re / (1 + Sig) ^ 2 →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (L₀ C_proj ν₀ : ℝ), 1 ≤ L₀ ∧ 1 ≤ C_proj ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∃ (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
          (D : DiscreteDichotomyData m p U),
          IsCoupledPropagator m p U ∧ D.Valid L₀ a' b' C_proj

/-! ## 4. `PartII-b:F4`: Intermediate-time projections and Green selector (`MixedGreenSelector`, SP 2189–2210) -/

/-- Algebraic helper for `PartII-b:F4`: intermediate-time projection
`Π^u(t) = J_t ∘ M_n ∘ F_t` where `F_t ∘ J_t = B_n` and `M_n = B_n⁻¹` (SP 2189–2194). -/
def intermProjU {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Jt : E2 →L[ℝ] X) (Mn : E2 →L[ℝ] E2) (Ft : X →L[ℝ] E2) : X →L[ℝ] X :=
  Jt.comp (Mn.comp Ft)

theorem intermProjU_idem {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Jt : E2 →L[ℝ] X) (Bn Mn : E2 →L[ℝ] E2) (Ft : X →L[ℝ] E2)
    (hFJ : Ft.comp Jt = Bn) (hMB : Mn * Bn = 1) :
    (intermProjU Jt Mn Ft).comp (intermProjU Jt Mn Ft) = intermProjU Jt Mn Ft := by
  unfold intermProjU
  have h1 : (Mn.comp Ft).comp (Jt.comp (Mn.comp Ft)) = Mn.comp Ft := by
    apply ContinuousLinearMap.ext
    intro x
    change Mn (Ft (Jt (Mn (Ft x)))) = Mn (Ft x)
    have hFJ_x := DFunLike.congr_fun hFJ (Mn (Ft x))
    simp only [ContinuousLinearMap.comp_apply] at hFJ_x
    rw [hFJ_x]
    exact DFunLike.congr_fun hMB (Mn (Ft x))
  rw [ContinuousLinearMap.comp_assoc, h1]

/-- **Target `Prop` of `PartII-b:F4` (`MixedGreenSelector`, SP 2189–2210, displays `short-bg:green`
at 2199 and `short-bg:green-bound` at 2206)**: at every intermediate age `t ∈ [0, T]` (`T = p.H = Σ/ν`),
the projections `Π^u(t) = J_t B_n⁻¹ F_t` and `Π^c(t) = I - Π^u(t)` are uniformly bounded and
commute with `U`, and the linear Green operator kernels `G_c(s, t) = U(s, t) Π^c(t)` (`0 ≤ t ≤ s ≤ T`),
`G_u(s, t)` (`0 ≤ s ≤ t ≤ T`, with `U(t, s) G_u(s, t) = Π^u(t)`), and entrance functional
`Γ_α(t) = -P_0^u G_u(0, t)` define for every Bochner-integrable zero-circulation vorticity source
`f : ℝ → Xmc p.c m` on `(0, T]` the Green solution
`ω(s) = ∫_0^s G_c(s, t) f(t) dt - ∫_s^T G_u(s, t) f(t) dt` and entrance coefficient
`α = ∫_0^T Γ_α(t) f(t) dt`, which solves the forced coupled cylinder vorticity equation on `[0, T]`,
has initial value `ω(0) = entranceVorticityComb p α`, vanishing terminal growing coordinate
`P_term(ω(T)) = 0`, zero circulation, and satisfies
`sup_{s ∈ [0, T]} ‖ω(s)‖_{X_{m,c}} + ‖α‖ ≤ C_green e^{a'T} ∫_0^T ‖f(t)‖_{X_{m,c}} dt`. -/
def MixedGreenSelector : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < lam.re / (1 + Sig) ^ 2 →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_green ν₀ : ℝ), 0 < C_green ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∃ (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
          (P_term : Xmc p.c m →L[ℝ] E2)
          (Piu Pic : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
          (G_c G_u : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
          (Γ_α : ℝ → (Xmc p.c m →L[ℝ] E2)),
          IsCoupledPropagator m p U ∧
          (∀ t ∈ Icc 0 p.H,
            (Piu t).comp (Piu t) = Piu t ∧
            Pic t = ContinuousLinearMap.id ℝ (Xmc p.c m) - Piu t ∧
            ‖Piu t‖ ≤ C_green ∧ ‖Pic t‖ ≤ C_green ∧
            ‖Γ_α t‖ ≤ C_green * Real.exp (-b' * t)) ∧
          (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
            (U t s).comp (Piu s) = (Piu t).comp (U t s) ∧
            (U t s).comp (Pic s) = (Pic t).comp (U t s) ∧
            G_c t s = (U t s).comp (Pic s) ∧
            (U t s).comp (G_u s t) = Piu t ∧
            ‖G_c t s‖ ≤ C_green * Real.exp (a' * (t - s)) ∧
            ‖G_u s t‖ ≤ C_green * Real.exp (-b' * (t - s))) ∧
          ∀ f : ℝ → Xmc p.c m, IntegrableOn f (Ioc 0 p.H) volume →
            (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (f t)) →
            let ω : ℝ → Xmc p.c m := fun s =>
              (∫ t in Ioc 0 s, G_c s t (f t)) - (∫ t in Ioc s p.H, G_u s t (f t))
            let α : E2 := ∫ t in Ioc 0 p.H, Γ_α t (f t)
            ((ω 0 : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α) ∧
            P_term (ω p.H) = 0 ∧
            (∀ s ∈ Icc 0 p.H, HasZeroCirculationR p.c (ω s)) ∧
            (∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ → ∀ s ∈ Icc 0 p.H,
              ∫ x in B0579.cell p.c, ω s x * φ x =
                (∫ x in B0579.cell p.c, ω 0 x * φ x) +
                  ∫ r in (0 : ℝ)..s, ∫ x in B0579.cell p.c,
                    (cylCoupledIntegrand p.train (ω r) r φ x + f r x * φ x)) ∧
            (∀ s ∈ Icc 0 p.H,
              ‖ω s‖ + ‖α‖ ≤ C_green * Real.exp (a' * p.H) * ∫ t in Ioc 0 p.H, ‖f t‖)

/-! ## 5. `PartII-b:F6`: Cylinder Biot–Savart `H¹` bound and `EarlyBound` (SP 2254–2268) -/

/-- The complex inlet profile `E(s)α = ∑_{i=0}^1 α_i cplx(inletE0 p i)` of the cutoff frozen stream
(SP 2313–2316, `StatementsMixed.lean`). -/
def inletProf (p : Params) (α : E2) (x : Coord) : CMerid :=
  ∑ i : Fin 2, ((α i : ℝ) : ℂ) • cplx (inletE0 p i) x

/-- The weak spatial `q`-derivative `∂_q(E(s)α)` of `inletProf p α`. -/
def inletProfQ (p : Params) (α : E2) (x : Coord) : CMerid :=
  ∑ i : Fin 2, ((α i : ℝ) : ℂ) • cplx (Axi.dQ (inletE0 p i)) x

/-- The weak spatial `η`-derivative `∂_η(E(s)α)` of `inletProf p α`. -/
def inletProfEta (p : Params) (α : E2) (x : Coord) : CMerid :=
  ∑ i : Fin 2, ((α i : ℝ) : ℂ) • cplx (Axi.dEta (inletE0 p i)) x

/-- The Lebesgue transpose of `∂_s - ν Δ_{q,η}` on a planar solenoidal test `Ψ` (`s > 0`):
`-∂_s Ψ - ν(∂_q² Ψ + ∂_η² Ψ)` (SP 2216, `short-bg:body-eq`). -/
def meridTranspose (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) : ℂ :=
  -((cpd 0 (fun y => Ψ y i) x : ℝ) : ℂ) -
    ((ν * (cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x +
      cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x) : ℝ) : ℂ)

/-- `z` (with weak spatial derivatives `zq = ∂_q z`, `zη = ∂_η z` and entrance coefficient `α : E2`)
solves the meridional correction equation `(short-bg:body-eq)` (SP 2216) on `(0, T)` (`T ≤ ∞` or
tested on `Ψ` supported in `Ioo 0 T ×ˢ univ`):
1. `z` is `c`-periodic in `q` and weakly solenoidal in `(q, η)` on `s > 0`,
2. for every planar solenoidal test `Ψ` (`IsPlanarSolTest Ψ`) supported in `(0, T) × ℝ²`,
   `∫ (z · (-∂_s Ψ - νΔΨ) + B_v z · Ψ) = ∫ g · Ψ`,
3. as `s → 0⁺`, `z(s)` has entrance trace `E(0)α`: on `(0, min 1 (T/4)]`, `z - Eα` is controlled in
   `L²(cell)` by `O(s)` plus the integrated source (SP 2315–2319). -/
structure IsMeridionalCorrectionOn (p : Params) (T : ℝ)
    (g z zq zη : CProf) (α : E2) : Prop where
  periodic : QPeriodic p.c z
  weak_q : HasWeakVec vQ0 dZero z zq
  weak_eta : HasWeakVec vEta dZero z zη
  solenoidal : ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 T ×ˢ univ →
    Integrable (fun x => z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) ∧
      ∫ x, (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) = 0
  equation : ∀ Ψ, IsPlanarSolTest Ψ →
    (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo 0 T ×ˢ univ) →
    Integrable (fun x => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) ∧
      Integrable (cdot (flatBv p.train z zq zη) Ψ) ∧
      Integrable (cdot g Ψ) ∧
      ∫ x, (∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train z zq zη) Ψ x) =
        ∫ x, cdot g Ψ x
  initial_curl :
    Tendsto (fun s => eLpNorm
        (fun x => profCurl zq zη (s, x) - ((entranceVorticityComb p α x : ℝ) : ℂ))
        2 (B0579.cellMeasure p.c 0))
      (𝓝[Ioi 0] 0) (𝓝 0)

/-- Global meridional correction on `(0, ∞)`: `z` is `c`-periodic, weakly solenoidal on all `s > 0`,
solves `z_s - νΔz + P_0(B_v z) = g` against every `IsPlanarSolTest Ψ`, and has entrance vorticity
trace `entranceVorticityComb p α` as `s → 0⁺`. -/
structure IsGlobalMeridionalCorrection (p : Params)
    (g z zq zη : CProf) (α : E2) : Prop where
  periodic : QPeriodic p.c z
  weak_q : HasWeakVec vQ0 dZero z zq
  weak_eta : HasWeakVec vEta dZero z zη
  solenoidal : ∀ φ, IsCoordTest φ →
    Integrable (fun x => z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) ∧
      ∫ x, (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) = 0
  equation : ∀ Ψ, IsPlanarSolTest Ψ →
    Integrable (fun x => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) ∧
      Integrable (cdot (flatBv p.train z zq zη) Ψ) ∧
      Integrable (cdot g Ψ) ∧
      ∫ x, (∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train z zq zη) Ψ x) =
        ∫ x, cdot g Ψ x
  initial_curl :
    Tendsto (fun s => eLpNorm
        (fun x => profCurl zq zη (s, x) - ((entranceVorticityComb p α x : ℝ) : ℂ))
        2 (B0579.cellMeasure p.c 0))
      (𝓝[Ioi 0] 0) (𝓝 0)

/-- **Zero-circulation cylinder Biot–Savart `X_{m,c} → H¹(C_c)` bound** (SP 2258–2261):
the zero-circulation cylinder Biot–Savart map sends `X_{m,c}` (`m > 8`) to `H¹(C_c)` with
polynomial `c` cost (on nonzero horizontal modes use the gap `2π/c`; on the mean mode use
`|ω̂(0, ξ)| ≤ |ξ| ∫ |η ω̄(η)| dη` before dividing by `ξ`). -/
def CylinderBiotSavartH1 : Prop :=
  ∀ m : ℝ, 8 < m → ∃ (C_bs : ℝ) (N_bs : ℕ), 0 < C_bs ∧
    ∀ c : ℝ, 1 ≤ c → ∀ w : Xmc c m, HasZeroCirculationR c w →
      ∃ u uq uη : B0579.Plane → Fin 2 → ℂ,
        IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ)) u ∧
        (∀ j : Fin 2, IIIa.HasWeakCellDerivC c 0 (fun x => u x j) (fun x => uq x j) ∧
          IIIa.HasWeakCellDerivC c 1 (fun x => u x j) (fun x => uη x j)) ∧
        (∑ j : Fin 2,
          (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun x => uq x j) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun x => uη x j) 2 (volume.restrict (B0579.cell c)))) ≤
          ENNReal.ofReal (C_bs * c ^ N_bs * ‖w‖)

/-- **Target `Prop` of `PartII-b:F6` (`EarlyBound`, SP 2254–2268, display `short-bg:early` at 2263)**:
combining `MixedGreenSelector` (`F4`), `BodySourceBound` (`F5`), `HardyL1` (`T01`), and
`CylinderBiotSavartH1`, for every fixed slow data `(Sig, lam, q)` and dichotomy rate
`0 < a' < Re λ / (1 + Σ)²`, there are `C > 0`, `k : ℕ`, `ν₀ > 0` such that at every parameter point
of `BgRegime` with `p.ν ≤ ν₀`, `p.ageCut = Sig`, `p.mode = q`, there are a bounded linear entrance
functional `αMap : HpR p.c →L[ℝ] E2` and a linear assignment `F ↦ (b0, b0q, b0η, g, gq, gη, z, zq, zη)`
solving the meridional correction equation on `(0, p.H]` (`p.H = Σ/ν`) with
`sup_{s ∈ (0, T]} ‖z(s)‖_{H¹} + ‖αMap F‖ ≤ C ν^{-k} e^{a'T} ‖F‖_{H_p}`. -/
def EarlyBound : Prop :=
  CylinderBiotSavartH1 ∧
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ a' : ℝ, 0 < a' → a' < lam.re / (1 + Sig) ^ 2 →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∃ (αMap : HpR p.c →L[ℝ] E2)
          (b0Of b0qOf b0ηOf gOf gqOf gηOf zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf),
          (∀ F : HpR p.c,
            InFlatClass p.c bgp (b0Of F) ∧
            IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
            HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
            HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
            QPeriodic p.c (gOf F) ∧
            HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
            HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
            IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
            IsMeridionalCorrectionOn p p.H (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
            Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ∧
            Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) ∧
            sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
              ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * ‖F‖) ∧
            ∀ s ∈ Ioc 0 p.H,
              sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
                ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖))

/-! ## 6. `PartII-b:F7`: `TailSource` and `GlobalEnergy` (`TailSourceAndGlobalEnergy`, SP 2269–2295) -/

/-- Weighted free-response slice quantity `B_0(s) = ‖b_0(s)‖_p` (SP 2277). -/
def sliceB0 (c : ℝ) (b0' : CProf) (s : ℝ) : ℝ≥0∞ :=
  sliceLpNorm c b0' s

/-- Weighted free-response gradient slice quantity `B_1(s) = (νs)^{1/2} ‖Db_0(s)‖_p` (SP 2277). -/
def sliceB1 (ν c : ℝ) (b0q b0η : CProf) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (ν * s)) * (sliceLpNorm c b0q s + sliceLpNorm c b0η s)

/-- Weighted free-response Hessian slice quantity `B_2(s) = (νs) ‖D²b_0(s)‖_p` (SP 2277). -/
def sliceB2 (ν c : ℝ) (D2 : Fin 2 → Fin 2 → CProf) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (ν * s) * ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s

/-- **`short-bg:tail-source`** (SP 2269–2288, display at 2281): for `s ≥ 1`, spatial Hölder with
`r = 22/3` (`1/2 = 3/22 + 4/11`) and the Part I train decay bounds
`‖D^j v(s)‖_{22/3} ≤ 𝒫_ν s^{-(41+22j)/44}`, `‖v(s)‖_∞ ≤ 𝒫_ν s⁻¹`, `‖Dv(s)‖_∞ ≤ 𝒫_ν s^{-3/2}` give
`‖g(s)‖_{H¹} ≤ 𝒫_ν [ν⁻¹ s^{-85/44} B_2(s) + s^{-63/44}(ν^{-1/2} B_1(s) + B_0(s))]`,
and weighted Hölder on `(T, ∞)` (`T ≥ 1`) bounds `g` in `L¹((T, ∞); H¹)` and in
`L^p((max 1 (T - 1), ∞), s^{-9/8} ds; H¹)` by `𝒫_ν ‖F‖_{H_p}`. -/
def TailSource : Prop :=
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ (F b0 b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
        InHr p.c bgp F → InFlatClass p.c bgp b0 → IsFlatResponse p.ν 0 F b0 →
        (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) →
        InHr p.c bgp b0' → InHr p.c bgp (sqrtS b0q) → InHr p.c bgp (sqrtS b0η) →
        (∀ i j, InHr p.c bgp (mulS (D2 i j))) →
        StronglyMeasurable b0' → StronglyMeasurable b0q → StronglyMeasurable b0η →
        (∀ i j, StronglyMeasurable (D2 i j)) →
        HasWeakVec vQ0 dZero b0 b0q → HasWeakVec vEta dZero b0 b0η →
        HasWeakVec vQ0 dZero b0q (D2 0 0) → HasWeakVec vEta dZero b0q (D2 0 1) →
        HasWeakVec vQ0 dZero b0η (D2 1 0) → HasWeakVec vEta dZero b0η (D2 1 1) →
        ∃ g gq gη : CProf,
          QPeriodic p.c g ∧ HasWeakVec vQ0 dZero g gq ∧ HasWeakVec vEta dZero g gη ∧
          IsBodySource p.train b0 b0q b0η g ∧
          Measurable (sliceH1Norm p.c g gq gη) ∧
          (∀ᵐ s ∂volume, 1 ≤ s →
            sliceH1Norm p.c g gq gη s ≤
              ENNReal.ofReal (C * (p.ν ^ k)⁻¹) *
                (ENNReal.ofReal (p.ν⁻¹ * s ^ (-85 / 44 : ℝ)) * sliceB2 p.ν p.c D2 s +
                  ENNReal.ofReal (s ^ (-63 / 44 : ℝ)) *
                    (ENNReal.ofReal (p.ν ^ (-1 / 2 : ℝ)) * sliceB1 p.ν p.c b0q b0η s +
                      sliceB0 p.c b0' s))) ∧
          ∀ T : ℝ, 1 ≤ T →
            (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) +
              (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) ≤
                ENNReal.ofReal (C * (p.ν ^ k)⁻¹) * hNorm p.c bgp F

/-- **`short-bg:global-energy`** (SP 2289–2295, display at 2294): there is a late-train constant
`C_late > 0` (from `short-bg:train-late`, SP 2054–2057, independent of `Σ` and `a'`) such that for
every fixed slow data `(Sig, lam, q)` and dichotomy rate `0 < a' < Re λ / (1 + Σ)²`, continuing the
Green-selected meridional correction `z` from `(0, p.H]` to `(0, ∞)` by differentiated velocity
energy and `(short-bg:train-late)` gives
`M_z := sup_{s > 0} ‖z(s)‖_{H¹} + ‖αMap F‖ ≤ C ν^{-k} exp((a'Σ + C_late/(1+Σ))/ν + C_late ν³) ‖F‖_{H_p}`,
together with the `L^p(s^{13/8} ds; H¹)` bound of `g` on `(0, p.H]` and the `L^p(s^{-9/8} ds; H¹)`
bound of `g` on `(p.H - 1, ∞)`. -/
def GlobalEnergy : Prop :=
  ∃ C_late : ℝ, 0 < C_late ∧
    ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
      Blueprint.Planar.IsGrowingEigenpair lam q →
    ∀ a' : ℝ, 0 < a' → a' < lam.re / (1 + Sig) ^ 2 →
    ∀ dm dp : ℝ, 0 < dm →
      ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
        ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
          ∃ (αMap : HpR p.c →L[ℝ] E2)
            (b0Of b0qOf b0ηOf gOf gqOf gηOf zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf),
            (∀ F : HpR p.c,
              let M_exp := Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3)
              InFlatClass p.c bgp (b0Of F) ∧
              IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
              HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
              HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
              QPeriodic p.c (gOf F) ∧
              HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
              HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
              IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
              IsGlobalMeridionalCorrection p (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
              Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ∧
              Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) ∧
              sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
                ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * ‖F‖) ∧
              (∫⁻ s in Ioi (max 1 (p.H - 1)),
                  sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s ^ bgp ∂sMeas (-9 / 8)) ^
                    (4 / 11 : ℝ) ≤
                ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * ‖F‖) ∧
              ∀ s : ℝ, 0 < s →
                sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
                  ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * M_exp * ‖F‖))

/-- **Target `Prop` of `PartII-b:F7` (`TailSourceAndGlobalEnergy`, SP 2269–2295)**: the conjunction
of `TailSource` (`short-bg:tail-source`, SP 2281) and `GlobalEnergy` (`short-bg:global-energy`,
SP 2294). -/
def TailSourceAndGlobalEnergy : Prop :=
  TailSource ∧ GlobalEnergy

/-! ## 7. `PartII-b:F8`: Local `H¹ → H²` smoothing and `s B_v z` bound (`LocalSmoothing`, SP 2296–2312) -/

/-- The cylinder `H²(C_c)` slice norm of a profile `z` with first derivatives `zq, zη` and second
spatial derivatives `D2z : Fin 2 → Fin 2 → CProf` at age `s`. -/
def sliceH2Norm (c : ℝ) (z zq zη : CProf) (D2z : Fin 2 → Fin 2 → CProf) (s : ℝ) : ℝ≥0∞ :=
  sliceH1Norm c z zq zη s +
    ∑ i : Fin 2, ∑ j : Fin 2, eLpNorm (fun x => D2z i j (s, x)) 2 (volume.restrict (B0579.cell c))

/-- **Target `Prop` of `PartII-b:F8` (`LocalSmoothing`, SP 2296–2312)**:
for the meridional correction equation, `E_j' + ν E_{j+1} ≤ C ∑_{i ≤ j} E_i` (`j ≤ 2`) gives
`H¹ → H²` smoothing norm `C [ν(t - s)]^{-1/2}` for `t - s ≤ 1`; Duhamel and `HardySingular`
(`PartII-b:T04`) bound `z` in `L^p((0, T], s^{13/8} ds; H²)` on `(0, T]` and unit-interval Duhamel
on `[s - 1, s]` gives
`‖z‖_{L^p((T, ∞), s^{-9/8} ds; H²)} ≤ C ν^{-1/2} [T^{-1/22} M_z + ‖g‖_{L^p((T-1, ∞), s^{-9/8} ds; H¹)}]`;
combining with `s ‖v(s)‖_∞ + s ‖Dv(s)‖_∞ ≤ 𝒫_ν` (`s ≥ 1`) bounds `s B_v z = flatK p.train z zq zη`
in `H_p` with the right-hand side of `short-bg:global-energy`. -/
def LocalSmoothing : Prop :=
  ∃ C_late : ℝ, 0 < C_late ∧
    ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
      Blueprint.Planar.IsGrowingEigenpair lam q →
    ∀ a' : ℝ, 0 < a' → a' < lam.re / (1 + Sig) ^ 2 →
    ∀ dm dp : ℝ, 0 < dm →
      ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
        ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
          ∃ (αMap : HpR p.c →L[ℝ] E2)
            (b0Of b0qOf b0ηOf gOf gqOf gηOf zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf)
            (D2zOf : Fin 2 → Fin 2 → HpR p.c →ₗ[ℝ] CProf),
            (∀ F : HpR p.c,
              let M_z := C * (p.ν ^ k)⁻¹ *
                Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) * ‖F‖
              let gH1_tail :=
                (∫⁻ s in Ioi (max 1 (p.H - 1)),
                  sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ)
              InFlatClass p.c bgp (b0Of F) ∧
              IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
              HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
              HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
              QPeriodic p.c (gOf F) ∧
              HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
              HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
              IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
              IsGlobalMeridionalCorrection p (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
              HasWeakVec vQ0 dZero (zqOf F) (D2zOf 0 0 F) ∧
              HasWeakVec vEta dZero (zqOf F) (D2zOf 0 1 F) ∧
              HasWeakVec vQ0 dZero (zηOf F) (D2zOf 1 0 F) ∧
              HasWeakVec vEta dZero (zηOf F) (D2zOf 1 1 F) ∧
              Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) ∧
              Measurable (sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)) ∧
              (∀ s : ℝ, 0 < s →
                sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
                  ENNReal.ofReal M_z) ∧
              sLpNorm (13 / 8) p.H
                  (sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)) ≤
                ENNReal.ofReal M_z ∧
              (∫⁻ s in Ioi p.H,
                  sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F) s ^ bgp
                    ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) ≤
                ENNReal.ofReal (C * p.ν ^ (-1 / 2 : ℝ)) *
                  (ENNReal.ofReal (p.H ^ (-1 / 22 : ℝ) * M_z) + gH1_tail) ∧
              InHr p.c bgp (flatK p.train (zOf F) (zqOf F) (zηOf F)) ∧
              hNorm p.c bgp (flatK p.train (zOf F) (zqOf F) (zηOf F)) ≤
                ENNReal.ofReal M_z)

/-! ## 8. `PartII-b:F9`: Global flat reconstruction (`FlatReconstruction`, SP 2313–2341) -/

/-- **Target `Prop` of `PartII-b:F9` (`FlatReconstruction`, SP 2313–2341, display
`short-bg:flat-reconstruction` at 2326)**:
1. For every `F ∈ H_p` and its flat response `b_0 = T_0 F`, the free interaction
   `s B_v b_0 = flatK p.train b_0 b0q b0η` belongs to `H_p`, obeying
   `‖s B_v b_0‖_{H_p(s < T)} ≤ C ν^{-k}(ν^{-1/2}√T + T) ‖F‖_{H_p}` on `s ∈ (0, T]` and
   `‖s B_v b_0‖_{H_p(s > T)} ≤ C ν^{-k} T^{-1/2}(ν^{-1/2} + 1) ‖F‖_{H_p}` on `s ∈ (T, ∞)`.
2. Each flat inlet column `flatColumn p i` (`i : Fin 2`) belongs to `H_p` with
   `‖flatColumn p i‖_{H_p} ≤ C ν^{-k}`.
3. Using the first Hardy estimate (`HardyMean`, `PartII-b:T03`) at `s → 0`, the tail integral
   `∫_T^∞ s^{-9/8} ds = 8 T^{-1/8}`, and flat uniqueness (`ProfileGraphFlat`, `PartII-b:T14`),
   `z - Eα ∈ H_p`, and setting `f = F - s B_v(b_0 + z) - s(∂_s - νΔ)Eα` gives the exact global
   identity `b_0 + z = Eα + T_0 f` (`InFlatClass p.c bgp (b_0 + z - Eα)` and
   `IsFlatResponse p.ν 0 (toProf p.c f) (b_0 + z - Eα)`), with a continuous linear reconstruction
   map `R0 : HpR p.c →L[ℝ] RowSpace p.c` (`F ↦ (f, α)`) satisfying
   `‖R0‖ ≤ C ν^{-k} exp((a'Σ + C_late/(1+Σ))/ν + C_late ν³)`. -/
def FlatReconstruction : Prop :=
  ∃ C_late : ℝ, 0 < C_late ∧
    ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
      Blueprint.Planar.IsGrowingEigenpair lam q →
    ∀ a' : ℝ, 0 < a' → a' < lam.re / (1 + Sig) ^ 2 →
    ∀ dm dp : ℝ, 0 < dm →
      ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
        ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
          (∀ F b0 : CProf, InHr p.c bgp F → InFlatClass p.c bgp b0 → IsFlatResponse p.ν 0 F b0 →
            ∃ b0q b0η : CProf,
              HasWeakVec vQ0 dZero b0 b0q ∧ HasWeakVec vEta dZero b0 b0η ∧
              InHr p.c bgp (flatK p.train b0 b0q b0η) ∧
              eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
                  ((hMeas p.c bgp).restrict (Ioc 0 p.H ×ˢ univ)) ≤
                ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H)) *
                  hNorm p.c bgp F ∧
              eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
                  ((hMeas p.c bgp).restrict (Ioi p.H ×ˢ univ)) ≤
                ENNReal.ofReal
                    (C * (p.ν ^ k)⁻¹ * p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1)) *
                  hNorm p.c bgp F) ∧
          (∀ i : Fin 2,
            InHr p.c bgp (flatColumn p i) ∧
            hNorm p.c bgp (flatColumn p i) ≤ ENNReal.ofReal (C * (p.ν ^ k)⁻¹)) ∧
          ∃ R0 : HpR p.c →L[ℝ] RowSpace p.c,
            ‖R0‖ ≤ C * (p.ν ^ k)⁻¹ *
              Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) ∧
            ∀ F : HpR p.c,
              let f : HpR p.c := (WithLp.fstL 1 ℝ (HpR p.c) E2) (R0 F)
              let α : E2 := (WithLp.sndL 1 ℝ (HpR p.c) E2) (R0 F)
              ∃ b0 b0q b0η z zq zη : CProf,
                InFlatClass p.c bgp b0 ∧
                IsFlatResponse p.ν 0 (toProf p.c F) b0 ∧
                HasWeakVec vQ0 dZero b0 b0q ∧
                HasWeakVec vEta dZero b0 b0η ∧
                HasWeakVec vQ0 dZero z zq ∧
                HasWeakVec vEta dZero z zη ∧
                InHr p.c bgp (fun x => z x - inletProf p α x) ∧
                InFlatClass p.c bgp (fun x => b0 x + z x - inletProf p α x) ∧
                IsFlatResponse p.ν 0 (toProf p.c f) (fun x => b0 x + z x - inletProf p α x) ∧
                toProf p.c f =ᵐ[hMeas p.c bgp] fun x =>
                  toProf p.c F x -
                    flatK p.train (fun y => b0 y + z y - inletProf p α y)
                      (fun y => b0q y + zq y - inletProfQ p α y)
                      (fun y => b0η y + zη y - inletProfEta p α y) x -
                    ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i x

/-! ## 9. Threshold arithmetic for `PartII-b:F10` and full chain assembly (proved) -/

/-- **Threshold arithmetic for `PartII-b:F10`** (SP 2337–2342: "Choosing `Σ` large and then `a'`
small proves, for every fixed `m > 0`, `‖f‖_{H_p} + |α| ≤ 𝒫_ν e^{m/ν} ‖F‖_{H_p}`"):
if `C_late > 0`, `m > 0`, `Sig ≥ max 1 (4 * C_late / m)`, `a' ≤ m / (4 * Sig)`, `0 < ν`, and
`C_late * ν ^ 4 ≤ m / 4`, then
`(a' * Sig + C_late / (1 + Sig)) / ν + C_late * ν ^ 3 ≤ m / ν`. -/
theorem flatInverse_rate_le_of_thresholds
    {C_late m Sig a' ν : ℝ} (_hCl : 0 < C_late) (hm : 0 < m) (hν : 0 < ν)
    (hSig : max 1 (4 * C_late / m) ≤ Sig)
    (ha' : a' ≤ m / (4 * Sig))
    (hν4 : C_late * ν ^ 4 ≤ m / 4) :
    (a' * Sig + C_late / (1 + Sig)) / ν + C_late * ν ^ 3 ≤ m / ν := by
  have hSig1 : 1 ≤ Sig := le_trans (le_max_left _ _) hSig
  have hSig0 : 0 < Sig := lt_of_lt_of_le zero_lt_one hSig1
  have h1Sig0 : 0 < 1 + Sig := by linarith
  have hSig_cl : 4 * C_late / m ≤ Sig := le_trans (le_max_right _ _) hSig
  have h1 : a' * Sig ≤ m / 4 := by
    calc a' * Sig ≤ (m / (4 * Sig)) * Sig := mul_le_mul_of_nonneg_right ha' hSig0.le
      _ = m / 4 := by field_simp [hSig0.ne']
  have h2 : C_late / (1 + Sig) ≤ m / 4 := by
    rw [div_le_div_iff₀ h1Sig0 (by positivity)]
    have hcl_le : 4 * C_late ≤ Sig * m := (div_le_iff₀ hm).mp hSig_cl
    nlinarith
  have h3 : C_late * ν ^ 3 ≤ (m / 4) / ν := by
    rw [le_div_iff₀ hν]
    calc C_late * ν ^ 3 * ν = C_late * ν ^ 4 := by ring
      _ ≤ m / 4 := hν4
  calc (a' * Sig + C_late / (1 + Sig)) / ν + C_late * ν ^ 3
      = (a' * Sig) / ν + (C_late / (1 + Sig)) / ν + C_late * ν ^ 3 := by ring
    _ ≤ (m / 4) / ν + (m / 4) / ν + (m / 4) / ν := by
        gcongr
    _ = (3 * m / 4) / ν := by ring
    _ ≤ m / ν := by
        gcongr
        linarith

/-- **Full chain assembly of `FlatInverse`** from `F1` (`InteractionCylinderComparison`,
`InteractionCollectiveCompact`), `F2` (`BlockDichotomy`), `F3` (`DichotomyProjections`),
`F4` (`MixedGreenSelector`), `F5` (`BodySourceBound`), `F6` (`EarlyBound`),
`F7` (`TailSourceAndGlobalEnergy`), `F8` (`LocalSmoothing`), `F9` (`FlatReconstruction`), and
`F10` (`FlatReconstruction → FlatInverse`). -/
theorem flatInverse_of_chain
    (hF1a : InteractionCylinderComparison)
    (hF1b : InteractionCollectiveCompact)
    (hF2 : InteractionCylinderComparison → InteractionCollectiveCompact → BlockDichotomy)
    (hF3 : BlockDichotomy → DichotomyProjections)
    (hF4 : DichotomyProjections → MixedGreenSelector)
    (hF5 : BodySourceBound)
    (hF6 : MixedGreenSelector → BodySourceBound → EarlyBound)
    (hF7 : EarlyBound → BodySourceBound → TailSourceAndGlobalEnergy)
    (hF8 : TailSourceAndGlobalEnergy → LocalSmoothing)
    (hF9 : TailSourceAndGlobalEnergy → LocalSmoothing → FlatReconstruction)
    (hF10 : FlatReconstruction → FlatInverse) :
    FlatInverse :=
  let h2 := hF2 hF1a hF1b
  let h3 := hF3 h2
  let h4 := hF4 h3
  let h6 := hF6 h4 hF5
  let h7 := hF7 h6 hF5
  let h8 := hF8 h7
  let h9 := hF9 h7 h8
  hF10 h9

end UnforcedLeray.Short.IIb

end
