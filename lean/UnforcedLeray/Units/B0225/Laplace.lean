import UnforcedLeray.Units.B0224
import UnforcedLeray.Lib.BochnerTime.Slices
import UnforcedLeray.Lib.Semigroups.Laplace

/-!
# B0225 helper: the Laplace transform `R_0(μ) = ∫_0^∞ e^{-μt} T_0(t) dt` on `H`

Blueprint unit B0225 (label `eq:st18-t00118`), `paper/main.tex` lines 3379–3392, depending on
B0224 (`eq:st18-t00117`, the limiting semigroup `T_0(t)`, tex lines 3370–3379) and B0223
(`eq:st18-t00116`, the free inverses as Laplace transforms, tex lines 3341–3368).

`R_0(μ)` is the `ε = 0` member of the family `R_ε(μ) = (μ - A_ε)^{-1}`; following the bypass BP4

`physRes`) it is defined as the Laplace transform of the explicit semigroup,
`R_0(μ)f = ∫_{(0,∞)} e^{-μt} T_0(t) f dt`, an `H`-valued Bochner integral (`R0`, `R0_apply`).

* `jointRep c ν F (t, p)`: the explicit formula of B0224 for `T_0(t)F` as a function of the pair
  `(t, p)`; it is jointly strongly measurable (`stronglyMeasurable_jointRep`) and represents
  `T_0(t)f` for every `t` (`T0_ae_jointRep`).
* `t ↦ T_0(t)f` is strongly measurable in `H` (`stronglyMeasurable_T0_path`, through the slice
  map `BochnerTime.toPathLq` of `Lib/BochnerTime/Slices.lean`).
* `T_0(t)` commutes with complex scalars (`T0_csmul`), so `R_0(μ)` is complex linear.
* For `γ = Re μ + 1/4 > 0`: the integrand is integrable (`integrableOn_lapT0`) and
  `‖R_0(μ)‖ ≤ γ⁻¹` (`norm_R0_le`), the `ε = 0` case of B0223 `norm_Reps_le`.

Outside the half-plane `R0` is the junk value `0`; every statement carries `0 < Re μ + 1/4`.
Fields are complex valued (`E` a complex Banach space: `ℂ` scalar, `ℂ²` meridional), because
`μ` is complex; the heat acts componentwise.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.B0225

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0220 UnforcedLeray.B0224

/-- `H = L²(s^{-3/2} ds dq dη)` on the cell is σ-finite. -/
instance sigmaFinite_measureH (c : ℝ) : SigmaFinite (measureH c) := by
  unfold measureH weightH cellMeasure
  infer_instance

/-! ### The joint representative of `T_0(t)F` -/

section Joint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The explicit formula of `T_0(t)F` (tex line 3373) as a function of `(t, p)`, `p = (s, q, η)`:
`e^{νs(1-e^{-t})Δ_{q,η}} F̃(se^{-t}, ·)(q, η)`, `F̃` the `c`-periodic extension in `q`. -/
def jointRep (c ν : ℝ) (F : Profile → E) (x : ℝ × Profile) : E :=
  planeHeat (ν * x.2.1 * (1 - Real.exp (-x.1)))
    (fun z => periodize c F (Real.exp (-x.1) * x.2.1, z)) x.2.2

theorem jointRep_eq_ite (c ν : ℝ) (F : Profile → E) :
    jointRep c ν F = fun x => if 0 < ν * x.2.1 * (1 - Real.exp (-x.1)) then
      ∫ y : Euc 2, gaussKernel 2 (ν * x.2.1 * (1 - Real.exp (-x.1))) y •
        periodize c F (Real.exp (-x.1) * x.2.1, x.2.2 - planeι y)
      else periodize c F (Real.exp (-x.1) * x.2.1, x.2.2) := by
  funext x
  by_cases h : 0 < ν * x.2.1 * (1 - Real.exp (-x.1))
  · simp only [jointRep, planeHeat_of_pos h, h, ↓reduceIte]
  · simp only [jointRep, planeHeat_of_nonpos (not_lt.1 h), h, ↓reduceIte]

theorem measurable_jointTime (ν : ℝ) :
    Measurable fun x : ℝ × Profile => ν * x.2.1 * (1 - Real.exp (-x.1)) :=
  ((measurable_fst.comp measurable_snd).const_mul ν).mul
    (measurable_const.sub (Real.measurable_exp.comp measurable_fst.neg))

theorem measurable_jointAge :
    Measurable fun x : ℝ × Profile => Real.exp (-x.1) * x.2.1 :=
  (Real.measurable_exp.comp measurable_fst.neg).mul (measurable_fst.comp measurable_snd)

theorem stronglyMeasurable_jointRep (c ν : ℝ) {F : Profile → E} (hF : StronglyMeasurable F) :
    StronglyMeasurable (jointRep c ν F) := by
  rw [jointRep_eq_ite]
  have hθ := measurable_jointTime ν
  have ha := measurable_jointAge
  refine StronglyMeasurable.ite (measurableSet_lt measurable_const hθ) ?_ ?_
  · refine StronglyMeasurable.integral_prod_right' (f := fun q : (ℝ × Profile) × Euc 2 =>
      gaussKernel 2 (ν * q.1.2.1 * (1 - Real.exp (-q.1.1))) q.2 •
        periodize c F (Real.exp (-q.1.1) * q.1.2.1, q.1.2.2 - planeι q.2)) ?_
    refine (measurable_gaussKernel_two.comp ((hθ.comp measurable_fst).prodMk
      measurable_snd)).stronglyMeasurable.smul ?_
    exact (stronglyMeasurable_periodize hF).comp_measurable
      ((ha.comp measurable_fst).prodMk
        ((measurable_snd.comp (measurable_snd.comp measurable_fst)).sub
          (measurable_planeι.comp measurable_snd)))
  · exact (stronglyMeasurable_periodize hF).comp_measurable
      (ha.prodMk (measurable_snd.comp measurable_snd))

/-- The time-`t` slice of `jointRep` is B0224's `H_{θ_t} D_{e^{-t}} F`. -/
theorem jointRep_slice (c ν t : ℝ) (F : Profile → E) :
    (fun p => jointRep c ν F (t, p)) = fiberHeat c (heatTime ν t) (dil (Real.exp (-t)) F) := by
  funext p
  simp only [jointRep, fiberHeat, dil, periodize, heatTime]

variable {c : ℝ}

/-- `jointRep` represents `T_0(t)f` for every `t`, starting from any strongly measurable
representative `F` of `f`. -/
theorem T0_ae_jointRep (hc : 0 < c) (ν t : ℝ) (f : HSpace c E) {F : Profile → E}
    (hF : StronglyMeasurable F) (hFf : F =ᵐ[measureH c] f) :
    (T0 hc ν t f : Profile → E) =ᵐ[measureH c] fun p => jointRep c ν F (t, p) := by
  have h1 := coeFn_T0 hc ν t f
  have h2 : (fun p => jointRep c ν (f : Profile → E) (t, p)) =ᵐ[measureH c]
      fun p => jointRep c ν F (t, p) := by
    rw [jointRep_slice, jointRep_slice]
    exact fiberHeat_congr_ae hc (measurable_heatTime ν t)
      (stronglyMeasurable_dil _ (Lp.stronglyMeasurable f)) (stronglyMeasurable_dil _ hF)
      (dil_congr_ae (Real.exp_pos _) (Lp.stronglyMeasurable f) hF hFf.symm)
  exact h1.trans h2

theorem memLp_jointRep (hc : 0 < c) (ν t : ℝ) (f : HSpace c E) {F : Profile → E}
    (hF : StronglyMeasurable F) (hFf : F =ᵐ[measureH c] f) :
    MemLp (fun p => jointRep c ν F (t, p)) 2 (measureH c) :=
  (Lp.memLp _).ae_eq (T0_ae_jointRep hc ν t f hF hFf)

/-- `t ↦ T_0(t)f` is the slice path of the joint representative. -/
theorem T0_path_eq (hc : 0 < c) (ν : ℝ) (f : HSpace c E) :
    (fun t => T0 hc ν t f) =
      BochnerTime.toPathLq 2 (measureH c) (jointRep c ν (f : Profile → E)) := by
  funext t
  have h := T0_ae_jointRep hc ν t f (Lp.stronglyMeasurable f) EventuallyEq.rfl
  have hm := memLp_jointRep hc ν t f (Lp.stronglyMeasurable f) EventuallyEq.rfl
  rw [BochnerTime.toPathLq_of_memLp hm]
  calc T0 hc ν t f = (Lp.memLp (T0 hc ν t f)).toLp (T0 hc ν t f) := (Lp.toLp_coeFn _ _).symm
    _ = hm.toLp _ := (MemLp.toLp_eq_toLp_iff _ _).2 h

/-- **`t ↦ T_0(t)f` is strongly measurable in `H`.** -/
theorem stronglyMeasurable_T0_path [TopologicalSpace.SeparableSpace E] (hc : 0 < c) (ν : ℝ)
    (f : HSpace c E) : StronglyMeasurable fun t => T0 hc ν t f := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  rw [T0_path_eq]
  exact BochnerTime.stronglyMeasurable_toPathLq
    (stronglyMeasurable_jointRep c ν (Lp.stronglyMeasurable f))

end Joint

/-! ### Complex scalars -/

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The cylinder heat commutes with complex scalars. -/
theorem planeHeat_csmul (θ : ℝ) (a : ℂ) (u : ℝ × ℝ → E) :
    planeHeat θ (fun x => a • u x) = fun x => a • planeHeat θ u x := by
  funext x
  by_cases hθ : 0 < θ
  · simp only [planeHeat_of_pos hθ, smul_comm _ a, integral_smul]
  · simp only [planeHeat_of_nonpos (not_lt.1 hθ)]

theorem jointRep_csmul (c ν : ℝ) (a : ℂ) (F : Profile → E) (x : ℝ × Profile) :
    jointRep c ν (fun p => a • F p) x = a • jointRep c ν F x :=
  congrFun (planeHeat_csmul (ν * x.2.1 * (1 - Real.exp (-x.1))) a
    (fun z => periodize c F (Real.exp (-x.1) * x.2.1, z))) x.2.2

variable {c : ℝ}

/-- `T_0(t)(a f) = a T_0(t) f` for complex `a`. -/
theorem T0_csmul (hc : 0 < c) (ν t : ℝ) (a : ℂ) (f : HSpace c E) :
    T0 hc ν t (a • f) = a • T0 hc ν t f := by
  refine Lp.ext ?_
  have hF : StronglyMeasurable fun p => a • (f : Profile → E) p :=
    (Lp.stronglyMeasurable f).const_smul a
  have h1 := T0_ae_jointRep hc ν t (a • f) hF (Lp.coeFn_smul a f).symm
  have h2 := T0_ae_jointRep hc ν t f (Lp.stronglyMeasurable f) EventuallyEq.rfl
  filter_upwards [h1, h2, Lp.coeFn_smul a (T0 hc ν t f)] with p hp1 hp2 hp3
  rw [hp1, hp3, Pi.smul_apply, hp2]
  exact jointRep_csmul c ν a _ (t, p)

/-! ### The Laplace transform -/

/-- The Laplace integrand `e^{-μt} T_0(t) f`. -/
def lapT0 (hc : 0 < c) (ν : ℝ) (μ : ℂ) (f : HSpace c E) (t : ℝ) : HSpace c E :=
  Complex.exp (-(μ * t)) • T0 hc ν t f

theorem norm_lapT0_le (hc : 0 < c) (ν : ℝ) (μ : ℂ) (f : HSpace c E) (t : ℝ) :
    ‖lapT0 hc ν μ f t‖ ≤ ‖f‖ * Real.exp (-(μ.re + 1 / 4) * t) := by
  have hT : ‖(T0 hc ν t : HSpace c E →L[ℝ] HSpace c E)‖ ≤ Real.exp (-t / 4) :=
    norm_T0_le hc ν t
  have h1 : ‖T0 hc ν t f‖ ≤ Real.exp (-t / 4) * ‖f‖ :=
    (T0 hc ν t : HSpace c E →L[ℝ] HSpace c E).le_of_opNorm_le hT f
  rw [lapT0, norm_smul, Infra.ExpSemigroup.norm_cexp_neg_mul]
  calc Real.exp (-(μ.re * t)) * ‖T0 hc ν t f‖
      ≤ Real.exp (-(μ.re * t)) * (Real.exp (-t / 4) * ‖f‖) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = ‖f‖ * Real.exp (-(μ.re + 1 / 4) * t) := by
        rw [show -(μ.re + 1 / 4) * t = -(μ.re * t) + -t / 4 by ring, Real.exp_add]
        ring

theorem integrableOn_lapT0 [TopologicalSpace.SeparableSpace E] (hc : 0 < c) (ν : ℝ) {μ : ℂ}
    (hμ : 0 < μ.re + 1 / 4) (f : HSpace c E) : IntegrableOn (lapT0 hc ν μ f) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hμ).const_mul ‖f‖) ?_
    (Eventually.of_forall fun t => norm_lapT0_le hc ν μ f t)
  exact ((Continuous.stronglyMeasurable (by fun_prop :
    Continuous fun t : ℝ => Complex.exp (-(μ * t)))).smul
      (stronglyMeasurable_T0_path hc ν f)).aestronglyMeasurable

theorem norm_integral_lapT0_le (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    (f : HSpace c E) : ‖∫ t in Ioi 0, lapT0 hc ν μ f t‖ ≤ (μ.re + 1 / 4)⁻¹ * ‖f‖ := by
  refine (norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hμ).const_mul ‖f‖)
    (Eventually.of_forall fun t => norm_lapT0_le hc ν μ f t)).trans (le_of_eq ?_)
  rw [Infra.ExpSemigroup.integral_exp_bound hμ, div_eq_inv_mul]

variable [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

/-- The Laplace transform as a complex linear map, for `Re μ > -1/4`. -/
def R0LM (hc : 0 < c) (ν : ℝ) (μ : ℂ) (hμ : 0 < μ.re + 1 / 4) : HSpace c E →ₗ[ℂ] HSpace c E where
  toFun f := ∫ t in Ioi 0, lapT0 hc ν μ f t
  map_add' f g := by
    have h : ∀ t, lapT0 hc ν μ (f + g) t = lapT0 hc ν μ f t + lapT0 hc ν μ g t := fun t => by
      simp only [lapT0, map_add, smul_add]
    simp_rw [h]
    exact integral_add (integrableOn_lapT0 hc ν hμ f) (integrableOn_lapT0 hc ν hμ g)
  map_smul' a f := by
    have h : ∀ t, lapT0 hc ν μ (a • f) t = a • lapT0 hc ν μ f t := fun t => by
      rw [lapT0, lapT0, T0_csmul, smul_comm]
    simp_rw [h]
    rw [integral_smul, RingHom.id_apply]

/-- **The limiting free inverse** `R_0(μ) = ∫_0^∞ e^{-μt} T_0(t) dt` on `H` (the `ε = 0` member
of `R_ε(μ)`, tex lines 3355–3361 and 3379–3383; bypass BP4). Junk value `0` for
`Re μ ≤ -1/4`. -/
def R0 (hc : 0 < c) (ν : ℝ) (μ : ℂ) : HSpace c E →L[ℂ] HSpace c E :=
  if hμ : 0 < μ.re + 1 / 4 then
    (R0LM hc ν μ hμ).mkContinuous (μ.re + 1 / 4)⁻¹ (norm_integral_lapT0_le hc ν hμ)
  else 0

theorem R0_apply (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (f : HSpace c E) :
    R0 hc ν μ f = ∫ t : ℝ in Ioi 0, Complex.exp (-(μ * t)) • T0 hc ν t f := by
  rw [R0, dif_pos hμ]
  rfl

/-- **`‖R_0(μ)‖_{H→H} ≤ γ⁻¹`**, `γ = Re μ + 1/4 > 0` (the `ε = 0` case of tex line 3363). -/
theorem norm_R0_le (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) :
    ‖(R0 hc ν μ : HSpace c E →L[ℂ] HSpace c E)‖ ≤ (μ.re + 1 / 4)⁻¹ := by
  rw [R0, dif_pos hμ]
  exact LinearMap.mkContinuous_norm_le _ (inv_nonneg.2 hμ.le) _

end Complex

end UnforcedLeray.B0225
