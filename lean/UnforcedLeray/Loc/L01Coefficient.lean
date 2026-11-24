import UnforcedLeray.Loc.L01Coefficient.HeatPeriodic

/-!
# Step L1 `CoefficientStep`: the coefficient maps `𝓑_*` (lines 267–290)

`paper/main.tex` lines 267–290 (`loc:eq:coefficient-maps`), blueprint units B0709, B0710,
B0711; the step is `Blueprint/Localization/Linear.lean`, `CoefficientStep` (line 76).

Main result: `coefficientStep_of`, the step from two named hypotheses, each a missing
theorem of a theory the project does not have yet:

* `H2EmbedsC0` (INF11): the Sobolev embedding `H²(ℝ³) ⊂ C₀(ℝ³)`, used for `r_heat(τ)`
  (line 280: `U_* ∈ C_per C₀`) and for `‖g‖_∞ ≤ C‖g‖_{H²}` in the `Z → X` bound (line 285).
* `HeatProfileRegularity` (INF04, B0710): the heat profile `H_h[u_dss]` of a field with
  `|D^k u| ≤ C|x|^{-1-k}` is continuous in phase with values in `C₀`, its gradient in `L³`
  and its Hessian in `L²` (lines 275–281: `|D^j H_h[u_dss]| ≤ C_j⟨y⟩^{-1-j}`, `j ≤ 2`).

Everything else is proved here and in `Loc/L01Coefficient/`:
* `Basic`, `Leibniz`: `H¹ ⊂ L³`, `C₀ → L^∞`, the weak product rule (mollification);
* `Operators`, `SecondOrder`: `div(U ⊗ f + f ⊗ U)` as bounded bilinear maps of
  `(U, ∇U, ∇²U) ∈ L^∞ × (L³)³ × (L²)^{3×3}` and `f ∈ X` or `g ∈ Z`, through Hölder
  (`‖U‖_∞‖∇f‖₂ + ‖∇U‖₃‖f‖₆`, line 282), and its weak derivatives;
* `Maps`: `𝓑 = -𝔓 div(…)` into `L²_div` and, with the compiled `Leray.h1Projection`, into
  `X` (lines 287–290); the literal weak characterization `IsMinusLerayDiv`;
* `HeatPeriodic`: `H_h[u_dss](·, τ + 𝒯) = H_h[u_dss](·, τ)` from `loc:eq:dss`.

The coefficient path is `U_* = H_h[u_dss] + r_heat` (line 167, `Ustar_decomposition`):
`(U, ∇U, ∇²U)(τ) = (V_H + E r_heat, W_H + ∇r_heat, Y_H + ∇²r_heat)(τ)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint

open SobolevGraph

/-! ## The two missing theorems -/

/-- **Missing theorem `H2EmbedsC0`** (infrastructure INF11; blueprint B0711, "`H²(ℝ³) ⊂
C₀ ∩ L^∞`"): every `H²(ℝ³;ℝ³)` class has a continuous representative vanishing at infinity,
with sup norm at most `C‖F‖_{H²}`. Used at lines 280 (`r_heat ∈ C_per H²` gives
`r_heat ∈ C_per C₀`) and 285 (`‖g‖_∞` for `g ∈ Z`). Not in Mathlib or the project; a proof
would go through `F = e^{Δ}F - ∫₀¹ e^{tΔ}ΔF dt` and `‖e^{tΔ}‖_{L²→L^∞} ≤ Ct^{-3/4}`, or
Fourier transform. -/
def H2EmbedsC0 : Prop :=
  ∃ C : ℝ, ∀ F : H2, ∃ v : ZeroAtInftyContinuousMap Space Space,
    (v : SpatialField) =ᵐ[volume] (F.value : SpatialField) ∧ ‖v‖ ≤ C * ‖F‖

/-- **Missing theorem `HeatProfileRegularity`** (infrastructure INF04; blueprint B0710 and the
continuity in phase of B0711; tex lines 275–281). For `h > 0` and a field `u` smooth off `0`
with the package's law `u(e^{𝒯/2}x) = e^{-𝒯/2}u(x)` and bounds
`|D^k u(x)| ≤ C_k|x|^{-1-k}` (`k ≤ 4`, lines 152–156), the heat profile
`H(τ) = H_h[u](·, τ)` of lines 159–163 has
* a representative `V(τ) ∈ C₀(ℝ³;ℝ³)`, continuous in `τ` for the sup norm;
* weak first derivatives `W(τ)ᵢ ∈ L³`, continuous in `τ`;
* weak second derivatives `Y(τ)ᵢⱼ = ∂ⱼW(τ)ᵢ ∈ L²`, continuous in `τ`.

The manuscript derives this from `|D^j H| ≤ C_j⟨y⟩^{-1-j}` (`j ≤ 2`, near/far splitting of the
heat integral); continuity in phase follows from joint continuity of `D^jH` and these
uniform tails. Periodicity is not assumed: it is proved (`heatProfile_add_period`).
The project's heat theory is `L²`-based, and `H` is not in `L²`. -/
def HeatProfileRegularity : Prop :=
  ∀ (h period : ℝ) (u : SpatialField), 0 < h → 0 < period → ContDiffOn ℝ ∞ u {0}ᶜ →
    (∀ x : Space, x ≠ 0 → u (Real.exp (period / 2) • x) = Real.exp (-(period / 2)) • u x) →
    (∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k u x‖ * ‖x‖ ^ (k + 1) ≤ C) →
    ∃ (V : ℝ → ZeroAtInftyContinuousMap Space Space)
      (W : ℝ → Fin 3 → Lp Space 3 (volume : Measure Space))
      (Y : ℝ → Fin 3 → Fin 3 → L2Space),
      Continuous V ∧ Continuous W ∧ Continuous Y ∧
      (∀ τ, (V τ : SpatialField) =ᵐ[volume] heatProfile h u τ) ∧
      (∀ τ i, HasWeakSpatialDerivative i (heatProfile h u τ) (W τ i : SpatialField)) ∧
      (∀ τ i j, HasWeakSpatialDerivative j (W τ i : SpatialField) (Y τ i j : SpatialField))

namespace L01

/-! ## `H² → C₀` as a bounded operator -/

theorem C0_eq_of_ae_eq {a b : ZeroAtInftyContinuousMap Space Space}
    (h : (a : SpatialField) =ᵐ[volume] (b : SpatialField)) : a = b :=
  ZeroAtInftyContinuousMap.ext (congrFun ((a.continuous.ae_eq_iff_eq volume b.continuous).mp h))

/-- The embedding of `H2EmbedsC0` as a bounded linear map (representatives are unique). -/
theorem exists_h2ToC0 (hE : H2EmbedsC0) :
    ∃ E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space,
      ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField) := by
  obtain ⟨C, hC⟩ := hE
  choose v hv hvC using hC
  let L : H2 →ₗ[ℝ] ZeroAtInftyContinuousMap Space Space :=
    { toFun := v
      map_add' := fun F G => C0_eq_of_ae_eq (by
        have e : (F + G).value = F.value + G.value := map_add H2.valueCLM F G
        filter_upwards [hv (F + G), hv F, hv G, Lp.coeFn_add F.value G.value] with x h1 h2 h3 h4
        rw [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, h1, h2, h3, e, h4, Pi.add_apply])
      map_smul' := fun a F => C0_eq_of_ae_eq (by
        have e : (a • F).value = a • F.value := map_smul H2.valueCLM a F
        filter_upwards [hv (a • F), hv F, Lp.coeFn_smul a F.value] with x h1 h2 h3
        rw [RingHom.id_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, h1, h2, e, h3,
          Pi.smul_apply]) }
  exact ⟨L.mkContinuous C hvC, hv⟩

/-! ## The coefficient path of `U_* = H_h[u_dss] + r_heat` -/

/-- `(U, ∇U, ∇²U)(τ) = (V_H + E r, W_H + ∇r, Y_H + ∇²r)(τ)`. -/
def coefPath (E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space)
    (VH : ℝ → ZeroAtInftyContinuousMap Space Space) (WH : ℝ → Fin 3 → L3Space)
    (YH : ℝ → Fin 3 → Fin 3 → L2Space) (r : ℝ → H2) (τ : ℝ) : Coef :=
  (toLinf (VH τ + E (r τ)), fun k => WH τ k + h1ToL3 (h2FirstToH1 k (r τ)),
    fun j k => YH τ j k + (r τ).second j k)

section Path

variable {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
  {VH : ℝ → ZeroAtInftyContinuousMap Space Space} {WH : ℝ → Fin 3 → L3Space}
  {YH : ℝ → Fin 3 → Fin 3 → L2Space} {r : ℝ → H2}

theorem continuous_coefPath (hVc : Continuous VH) (hWc : Continuous WH) (hYc : Continuous YH)
    (hr : Continuous r) : Continuous (coefPath E VH WH YH r) := by
  refine (toLinf.continuous.comp (hVc.add (E.continuous.comp hr))).prodMk
    ((continuous_pi fun k => ?_).prodMk (continuous_pi fun j => continuous_pi fun k => ?_))
  · exact ((continuous_apply k).comp hWc).add
      ((h1ToL3.comp (h2FirstToH1 k)).continuous.comp hr)
  · exact ((continuous_apply k).comp ((continuous_apply j).comp hYc)).add
      ((H2.secondCLM j k).continuous.comp hr)

theorem periodic_coefPath {T : ℝ} (hVp : Function.Periodic VH T) (hWp : Function.Periodic WH T)
    (hYp : Function.Periodic YH T) (hr : Function.Periodic r T) :
    Function.Periodic (coefPath E VH WH YH r) T := fun τ => by
  simp only [coefPath, hVp τ, hWp τ, hYp τ, hr τ]

theorem coefPath_fst_ae (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField))
    {h : ℝ} {u : SpatialField}
    (hVrep : ∀ τ, (VH τ : SpatialField) =ᵐ[volume] heatProfile h u τ) (τ : ℝ) :
    ((coefPath E VH WH YH r τ).1 : SpatialField) =ᵐ[volume]
      heatProfile h u τ + ((r τ).value : SpatialField) := by
  filter_upwards [coeFn_toLinf (VH τ + E (r τ)), hVrep τ, hE (r τ)] with x h1 h2 h3
  simp only [coefPath, h1, ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, h2, h3]

theorem isConsistentCoef_coefPath
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField))
    {h : ℝ} {u : SpatialField}
    (hVrep : ∀ τ, (VH τ : SpatialField) =ᵐ[volume] heatProfile h u τ)
    (hWd : ∀ τ i, HasWeakSpatialDerivative i (heatProfile h u τ) (WH τ i : SpatialField))
    (hYd : ∀ τ i j, HasWeakSpatialDerivative j (WH τ i : SpatialField) (YH τ i j : SpatialField))
    (τ : ℝ) : IsConsistentCoef (coefPath E VH WH YH r τ) := by
  have hW : ∀ k, ((coefPath E VH WH YH r τ).2.1 k : SpatialField) =ᵐ[volume]
      (WH τ k : SpatialField) + ((r τ).first k : SpatialField) := by
    intro k
    filter_upwards [Lp.coeFn_add (WH τ k) (h1ToL3 (h2FirstToH1 k (r τ))),
      coeFn_h1ToL3 (h2FirstToH1 k (r τ))] with x h1 h2
    simp only [coefPath, h1, Pi.add_apply, h2, h2FirstToH1_value]
  refine ⟨fun k => ?_, fun j k => ?_⟩
  · exact ((hWd τ k).add ((r τ).hasWeakFirst k)).congr (coefPath_fst_ae hE hVrep τ).symm
      (hW k).symm
  · refine ((hYd τ j k).add ((r τ).hasWeakSecond j k)).congr (hW j).symm ?_
    filter_upwards [Lp.coeFn_add (YH τ j k) ((r τ).second j k)] with x h1
    simp only [coefPath, h1, Pi.add_apply]

end Path

end L01

open L01

/-- **Step L1, conditional form.** `loc:eq:coefficient-maps` (lines 279–290) for every
package background, from the Sobolev embedding `H2EmbedsC0` and the heat-profile regularity
`HeatProfileRegularity` (B0710). The maps are
`𝓑_*(τ) = -𝔓 div(U_*(τ) ⊗ · + · ⊗ U_*(τ))` (`L01.Bop`, `L01.BZop`), with the literal weak
characterization; units B0709, B0710, B0711. -/
theorem coefficientStep_of (hE : H2EmbedsC0) (hH : HeatProfileRegularity) :
    CoefficientStep := by
  intro D hD
  have hB := hD.1
  obtain ⟨E, hErep⟩ := exists_h2ToC0 hE
  obtain ⟨VH, WH, YH, hVc, hWc, hYc, hVrep, hWd, hYd⟩ :=
    hH D.h D.period D.udss hB.h_pos hB.period_pos hB.udss_smooth hB.udss_dss hB.udss_bounds
  -- periodicity in phase, from `loc:eq:dss` and uniqueness of representatives
  have hprofile : ∀ τ, heatProfile D.h D.udss (τ + D.period) = heatProfile D.h D.udss τ :=
    fun τ => funext (heatProfile_add_period hB.h_pos hB.udss_dss τ)
  have hVp : Function.Periodic VH D.period := fun τ => by
    have h1 := hVrep (τ + D.period)
    rw [hprofile τ] at h1
    exact C0_eq_of_ae_eq (h1.trans (hVrep τ).symm)
  have hWp : Function.Periodic WH D.period := fun τ => funext fun i => by
    have h1 := hWd (τ + D.period) i
    rw [hprofile τ] at h1
    exact Lp_eq_of_weakDerivative h1 (hWd τ i)
  have hYp : Function.Periodic YH D.period := fun τ => funext fun i => funext fun j => by
    have h1 := hYd (τ + D.period) i j
    rw [hWp τ] at h1
    exact Lp_eq_of_weakDerivative h1 (hYd τ i j)
  -- `U_* = H_h[u_dss] + r_heat`
  have hdec : ∀ τ, heatProfile D.h D.udss τ + ((D.rheat τ).value : SpatialField) =ᵐ[volume]
      D.Ustar τ := fun τ => (hB.Ustar_decomposition τ).symm
  have hV : ∀ τ, ((VH τ + E (D.rheat τ) : ZeroAtInftyContinuousMap Space Space) : SpatialField)
      =ᵐ[volume] D.Ustar τ := by
    intro τ
    refine EventuallyEq.trans ?_ (hdec τ)
    filter_upwards [hVrep τ, hErep (D.rheat τ)] with x h1 h2
    simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, h1, h2]
  have hcons := isConsistentCoef_coefPath (r := D.rheat) hErep hVrep hWd hYd
  exact ⟨_, isCoefficients_of_path D hErep (coefPath E VH WH YH D.rheat)
    (continuous_coefPath hVc hWc hYc hB.rheat_continuous)
    (periodic_coefPath hVp hWp hYp hB.rheat_periodic) hcons
    (fun τ => (coefPath_fst_ae hErep hVrep τ).trans (hdec τ))
    (fun τ => VH τ + E (D.rheat τ)) (hVc.add (E.continuous.comp hB.rheat_continuous))
    (fun τ => by simp only [hVp τ, hB.rheat_periodic τ]) hV⟩

end UnforcedLeray.Blueprint

#print axioms UnforcedLeray.Blueprint.coefficientStep_of
