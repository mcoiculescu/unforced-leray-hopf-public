import UnforcedLeray.Short.Spine.Objects
import UnforcedLeray.Short.PartIIb.StatementsNonlinear

/-!
# The exact background of one level, as Part II constructs it (shorter proof)

Source of record: `the November 2 reference manuscript` (73 pages).

Part II (lines 1181-2645) constructs, at the parameters `c = ν^{-2}`, `R = ε⁻¹`, `P = 2εc` of one
level, one exact unforced background around one fixed inlet: "the fixed inlet stream with an age
cutoff equal to one near zero and zero before the terminal time" (lines 2316-2318), built from the
periodized Gaussian angular-two eigenstream (lines 2345-2360), with the slow terminal age `Σ`
chosen large from `m` (lines 2337-2342). The background is the contraction-ball solution of
`short-bg:result` (lines 2505-2524): `U = V₀ + E_εα + w` with
`‖w‖_{X_p} + R^{8/11}|α| ≤ 𝒫_νe^{m/ν}ε^{3/11}` and `|α| ≤ 𝒫_νe^{m/ν}ε`. Part III uses exactly this
background: `ρ_b = P_νε^{3/11}e^{m₀/ν}` is "a fixed upper bound from the exact-background
construction" (lines 2701-2713), "The background construction realizes this `m₀`; all its
internal choices are then fixed" (lines 5856-5857), and the background is constructed once per
level and held fixed while `σ` varies (lines 5951-5954).

The background is recorded in the Part II-b encoding (`Short/PartII-b/StatementsNonlinear.lean`,
the concrete objects of `Cons/L2/BackgroundConcrete/`), so nothing is a free predicate:
* `levelParams P hν hε hΣ T`: the parameter record `Cons.C03.Concrete.Params` of the level:
  `ν`, `c = Train.per ν = ν^{-2}`, `ε`, the slow age `Σ` of the inlet cutoff
  (`Concrete.ageCutoff (Σ/ν)`, lines 2316-2318), the eigenprofile `q = P.mode` of the inlet
  streams (lines 2345-2360), the actual train `T`;
* `ShortBackground`: a parameter record `par`, a state `z = (w, A) ∈ par.Z`, a datum `a`, a heat
  remainder `Q`, a pressure `pres`. Its background is `U = IIb.bgField par z = U_raw + Σᵢ αᵢE_i + w`
  (lines 2519-2524) with `α = par.coord z = ε^{8/11}A`; `r_b = w = par.corr z` is the energy repair
  and `V = U_raw + E_εα`, so `U = V + r_b` (lines 2669-2672);
* `IsShortBackground P ν ε m C N Σ B`: everything Part II delivers that Part III and
  `prop:unstable-background` use (see the structure).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- **The parameter record of a level** (lines 2028-2040, 2316-2318, 2345-2360): viscosity `ν`,
cell `c = Train.per ν = ν^{-2}`, ring parameter `ε = R⁻¹`, the slow terminal age `Σ` of the fixed
inlet cutoff (`H = Σ/ν`), the planar eigenprofile `q = P.mode` of the inlet streams, and the
actual train `T`. Its period `2εc` is `shortPeriod ν ε` (`ShortBackground.period_levelParams`). -/
def levelParams (P : PlanarData) {ν ε Sig : ℝ} (hν : 0 < ν) (hε : 0 < ε) (hSig : 0 < Sig)
    (T : B0140.TrainSol ν (Train.per ν)) : Params where
  ν := ν
  c := Train.per ν
  ε := ε
  ageCut := Sig
  mode := P.mode
  ν_pos := hν
  c_pos := by unfold Train.per; positivity
  ε_pos := hε
  ageCut_pos := hSig
  trainData := T

/-- **The exact background of one level, as Part II constructs it** (lines 2505-2524, 2563-2645,
2664-2672): the parameter record `par` of the level (with its fixed inlet), the state
`z = (w, A) ∈ par.Z` of `short-bg:result`, the datum `a`, the heat remainder `Q` and the global
pressure `pres` (`p_U = Σ R_iR_j(U_iU_j)`, lines 2641-2642). -/
structure ShortBackground where
  /-- The parameter record of the level. -/
  par : Params
  /-- The state `z = (w, A)`, `A = R^{8/11}α` (lines 2505-2520). -/
  z : par.Z
  /-- The DSS datum `a` (lines 2563-2600). -/
  a : SpatialField
  /-- The heat remainder `Q = U - H_ν[a] ∈ C_per H²` (lines 2601-2640). -/
  Q : ℝ → SobolevGraph.H2
  /-- The global pressure (lines 2641-2642). -/
  pres : ℝ → Space → ℝ

namespace ShortBackground

variable (B : ShortBackground)

/-- The entrance coefficients `α = ε^{8/11}A` (lines 2513-2520). -/
def α : Fin 2 → ℝ := B.par.coord B.z

/-- The energy repair `r_b = w` (lines 2669-2672). -/
def rb : ℝ → SpatialField := B.par.corr B.z

/-- `V = U_raw + E_εα` (lines 2669-2672): the raw lift of the actual train and the fixed inlet. -/
def V : ℝ → SpatialField := fun τ y => B.par.raw τ y + ∑ i : Fin 2, B.α i • B.par.inlet i τ y

/-- The exact background `U = U_raw + E_εα + w` (`IIb.bgField`, lines 2519-2524). -/
def U : ℝ → SpatialField := UnforcedLeray.Short.IIb.bgField B.par B.z

/-- `U = V + r_b` (lines 2669-2672). -/
theorem U_apply (τ : ℝ) (y : Space) : B.U τ y = B.V τ y + B.rb τ y := rfl

/-- Off the axis, `U_raw` is the ring lift `𝒩_v` of the raw profile of the train (`sct:lift`,
lines 1205-1230): `U = 𝒩_v b_raw + E_εα + r_b` there. -/
theorem U_eq_off_axis (τ : ℝ) (y : Space) (hy : y ∉ Axi.axis) :
    B.U τ y = Axi.Nv B.par.ε⁻¹ (Cons.C03.rawProfile B.par.ε B.par.train.v B.par.train.ψ) τ y
      + ∑ i : Fin 2, B.α i • B.par.inlet i τ y + B.rb τ y := by
  rw [U_apply, V, B.par.raw_eq_off_axis τ y hy]

/-- A parameter record is the record of its fields (`ν, c, ε, Σ, q`, and its train transported
along the field equalities). Identifies `par` with the record of another encoding of the level. -/
theorem params_eq_mk (p : Params) {ν c ε Sig : ℝ} {q : Profile} (h1 : p.ν = ν) (h2 : p.c = c)
    (h3 : p.ε = ε) (h4 : p.ageCut = Sig) (h5 : p.mode = q) (hν : 0 < ν) (hc : 0 < c)
    (hε : 0 < ε) (hSig : 0 < Sig) :
    p = { ν := ν, c := c, ε := ε, ageCut := Sig, mode := q, ν_pos := hν, c_pos := hc,
          ε_pos := hε, ageCut_pos := hSig,
          trainData := cast (by rw [h1, h2]) p.trainData } := by
  cases p
  subst h1 h2 h3 h4 h5
  rfl

/-- The period of the level record is `shortPeriod ν ε = 2ε Train.per ν`. -/
theorem period_levelParams (P : PlanarData) {ν ε Sig : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hSig : 0 < Sig) (T : B0140.TrainSol ν (Train.per ν)) :
    (levelParams P hν hε hSig T).period = shortPeriod ν ε := rfl

end ShortBackground

/-- **The exact unforced background of Part II at one level, with everything Part III uses**
(`short-bg:result`, `short-bg:strong`, lines 2028-2065, 2316-2318, 2505-2561, 2563-2645,
2664-2713, 5125-5135). The background `B` is at the level `(ν, ε)` with the fixed inlet of slow
age `Σ` and eigenprofile `q = P.mode`, on a BUC train, and:
* `equation`, `ball`: its state `z = (w, A)` solves the projected equation
  `A_0U + 𝔓(U·∇U) = 0` (`IIb.ProjectedEquation`, lines 2519-2524) and lies in the contraction
  ball, `‖w‖_{X_p} + R^{8/11}|α| = ‖z‖_Z ≤ P_νe^{m/ν}ε^{3/11}` with `P_ν = Cν^{-N}` (lines
  2507-2520); consequently `|α| ≤ P_νe^{m/ν}ε` (`entrance_bound` below, line 2523);
* `b3`: `U` is the exact periodic similarity solution of `∂_τU = νΔU + ½y·∇U + ½U - 𝔓div(U⊗U)`
  with datum `a`, heat remainder `Q = U - H_ν[a] ∈ C_per H²` and global pressure `pres`, period
  `P = 2εc` (the library's `IsB3Output`, lines 2563-2645);
* `smooth`: `U` is jointly smooth in `(τ, y)` through the axis (line 2561);
* `rb_smooth`: the repair `r_b = w` is jointly smooth through the axis (`U` is, line 2561; the raw
  lift is smooth through the axis for positive time, line 1219; the inlet cutoff vanishes near the
  axis, line 2556; all spatial orders of `w`, lines 2524-2557), so the `fderiv`, `iteratedFDeriv`
  in the bounds below are the genuine derivatives at every point;
* `rb_sup`, `rb_Lp`, `rb_derivatives`: `‖r_b‖_{L^{11/4}} + ‖r_b‖_{W^{1,∞}} +
  ∑_{j=1,2}‖D^jr_b‖_{𝒴_{11/4}} ≤ P_νε^{3/11}e^{m/ν}` (lines 2538-2543, 5131-5134; the
  `𝒴_{11/4}` norm is phase-normalized, hence the factor `P^{4/11}` on the slab). -/
structure IsShortBackground (P : PlanarData) (ν ε m C : ℝ) (N : ℕ) (Sig : ℝ)
    (B : ShortBackground) : Prop where
  /-- The level: `ν`, `ε = R⁻¹`, `c = ν^{-2}` (lines 2031-2033). -/
  nu_eq : B.par.ν = ν
  eps_eq : B.par.ε = ε
  c_eq : B.par.c = Train.per ν
  /-- The fixed inlet: the slow age `Σ` of its age cutoff (lines 2316-2318, 2337-2342). -/
  ageCut_eq : B.par.ageCut = Sig
  /-- The fixed inlet: the eigenprofile `q` of the planar reference (lines 2345-2360). -/
  mode_eq : B.par.mode = P.mode
  /-- The actual train is the BUC train of Part I (lines 270-288, 2040). -/
  train_buc : UnforcedLeray.Short.PartI.IsBUCTrain B.par.train
  /-- The projected equation of the state (lines 2519-2524). -/
  equation : UnforcedLeray.Short.IIb.ProjectedEquation B.par B.z
  /-- The contraction ball of `short-bg:result` (lines 2507-2520). -/
  ball : ‖B.z‖ ≤ lossRadius ν ε m C N
  b3 : IsB3Output ν (shortPeriod ν ε) B.a B.U B.Q B.pres
  /-- "On positive physical-time compact intervals the resulting `C_τW^{k,4}` regularity and
  the projected equation give all time derivatives, so `U` is jointly smooth through the axis"
  (lines 2557-2561). -/
  smooth : ContDiff ℝ ∞ (fun x : SpaceTime => B.U x.1 x.2)
  rb_smooth : ContDiff ℝ ∞ (fun x : SpaceTime => B.rb x.1 x.2)
  rb_sup : ∀ τ y, ‖B.rb τ y‖ ≤ lossRadius ν ε m C N ∧
    ‖fderiv ℝ (B.rb τ) y‖ ≤ lossRadius ν ε m C N
  rb_Lp : ∀ τ, MemLp (B.rb τ) (11 / 4 : ℝ≥0∞) volume ∧
    (eLpNorm (B.rb τ) (11 / 4 : ℝ≥0∞) volume).toReal ≤ lossRadius ν ε m C N
  rb_derivatives : ∀ j : ℕ, 1 ≤ j → j ≤ 2 →
    MemLp (fun x : SpaceTime => iteratedFDeriv ℝ j (B.rb x.1) x.2) (11 / 4 : ℝ≥0∞)
        (volume.restrict (periodSlab (shortPeriod ν ε))) ∧
      (eLpNorm (fun x : SpaceTime => iteratedFDeriv ℝ j (B.rb x.1) x.2) (11 / 4 : ℝ≥0∞)
        (volume.restrict (periodSlab (shortPeriod ν ε)))).toReal ≤
        shortPeriod ν ε ^ ((4 : ℝ) / 11) * lossRadius ν ε m C N

namespace IsShortBackground

variable {P : PlanarData} {ν ε m C : ℝ} {N : ℕ} {Sig : ℝ} {B : ShortBackground}

theorem nu_pos (h : IsShortBackground P ν ε m C N Sig B) : 0 < ν := h.nu_eq ▸ B.par.ν_pos

theorem eps_pos (h : IsShortBackground P ν ε m C N Sig B) : 0 < ε := h.eps_eq ▸ B.par.ε_pos

theorem sig_pos (h : IsShortBackground P ν ε m C N Sig B) : 0 < Sig :=
  h.ageCut_eq ▸ B.par.ageCut_pos

/-- The period of the level record is `P = 2εc = shortPeriod ν ε`. -/
theorem period_eq (h : IsShortBackground P ν ε m C N Sig B) :
    B.par.period = shortPeriod ν ε := by
  rw [Cons.C03.Concrete.Params.period, h.eps_eq, h.c_eq, shortPeriod]

/-- **`|α| ≤ P_νe^{m/ν}ε`** (`short-bg:result`, line 2523), from the ball: `α = ε^{8/11}A` and
`|A| ≤ ‖z‖_Z ≤ P_νe^{m/ν}ε^{3/11}`. -/
theorem entrance_bound (h : IsShortBackground P ν ε m C N Sig B) (i : Fin 2) :
    |B.α i| ≤ entranceRadius ν ε m C N := by
  have hε : 0 < ε := h.eps_pos
  have hA : |(Cons.C03.Concrete.cA B.par.period (B.z : Cons.C03.Concrete.Amb B.par.period)) i|
      ≤ ‖B.z‖ := by
    rw [← Real.norm_eq_abs]
    refine (PiLp.norm_apply_le _ i).trans ?_
    have h4 := Cons.C03.Concrete.norm_amb B.par.period (B.z : Cons.C03.Concrete.Amb B.par.period)
    have e : ‖(B.z : Cons.C03.Concrete.Amb B.par.period)‖ = ‖B.z‖ := rfl
    rw [← e, h4]
    have := norm_nonneg (Cons.C03.Concrete.cw B.par.period (B.z : Cons.C03.Concrete.Amb B.par.period))
    have := norm_nonneg (Cons.C03.Concrete.cΔ B.par.period (B.z : Cons.C03.Concrete.Amb B.par.period))
    have := norm_nonneg (Cons.C03.Concrete.cT B.par.period (B.z : Cons.C03.Concrete.Amb B.par.period))
    linarith
  have hpow : (0 : ℝ) ≤ ε ^ (8 / 11 : ℝ) := Real.rpow_nonneg hε.le _
  have hα : |B.α i| ≤ ε ^ (8 / 11 : ℝ) * ‖B.z‖ := by
    show |B.par.ε ^ (8 / 11 : ℝ) * _| ≤ _
    rw [abs_mul, h.eps_eq, abs_of_nonneg hpow]
    exact mul_le_mul_of_nonneg_left hA hpow
  have hsplit : ε = ε ^ (3 / 11 : ℝ) * ε ^ (8 / 11 : ℝ) := by
    rw [← Real.rpow_add hε]
    norm_num
  calc |B.α i| ≤ ε ^ (8 / 11 : ℝ) * ‖B.z‖ := hα
    _ ≤ ε ^ (8 / 11 : ℝ) * lossRadius ν ε m C N := mul_le_mul_of_nonneg_left h.ball hpow
    _ = entranceRadius ν ε m C N := by
        rw [lossRadius, entranceRadius]
        conv_rhs => rw [hsplit]
        ring

/-- Every phase `U(τ)` is smooth in space (from the joint smoothness, line 2561). -/
theorem contDiff_slice (h : IsShortBackground P ν ε m C N Sig B) (τ : ℝ) :
    ContDiff ℝ ∞ (B.U τ) := by
  have h1 : ContDiff ℝ ∞
      ((fun x : SpaceTime => B.U x.1 x.2) ∘ fun y : Space => ((τ, y) : SpaceTime)) :=
    h.smooth.comp (contDiff_const.prodMk contDiff_id)
  have h2 : ((fun x : SpaceTime => B.U x.1 x.2) ∘ fun y : Space => ((τ, y) : SpaceTime)) =
      B.U τ := by
    funext y
    rfl
  rwa [h2] at h1

/-- Every phase `r_b(τ)` is smooth in space. -/
theorem rb_contDiff_slice (h : IsShortBackground P ν ε m C N Sig B) (τ : ℝ) :
    ContDiff ℝ ∞ (B.rb τ) := by
  have h1 : ContDiff ℝ ∞
      ((fun x : SpaceTime => B.rb x.1 x.2) ∘ fun y : Space => ((τ, y) : SpaceTime)) :=
    h.rb_smooth.comp (contDiff_const.prodMk contDiff_id)
  have h2 : ((fun x : SpaceTime => B.rb x.1 x.2) ∘ fun y : Space => ((τ, y) : SpaceTime)) =
      B.rb τ := by
    funext y
    rfl
  rwa [h2] at h1

/-- The Lipschitz form of the `W^{1,∞}` bound on `r_b` (`short-bg:strong`, lines 2540-2543;
line 5133): `‖r_b(τ,y) - r_b(τ,y')‖ ≤ P_νρ ‖y - y'‖` (mean value inequality on `ℝ³`). -/
theorem rb_norm_sub_le (h : IsShortBackground P ν ε m C N Sig B) (τ : ℝ) (y y' : Space) :
    ‖B.rb τ y - B.rb τ y'‖ ≤ lossRadius ν ε m C N * ‖y - y'‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => ((h.rb_contDiff_slice τ).differentiable (by simp)).differentiableAt)
    (fun x _ => (h.rb_sup τ x).2) (mem_univ y') (mem_univ y)

end IsShortBackground

end UnforcedLeray.Short.Spine
