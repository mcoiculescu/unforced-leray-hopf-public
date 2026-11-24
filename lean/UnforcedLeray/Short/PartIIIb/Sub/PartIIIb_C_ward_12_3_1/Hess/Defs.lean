import UnforcedLeray.Short.PartIIa.Sub.F03
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.PeriodAverageBound
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.SliceIntegralYq
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.YqRepNorm
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.NormFromPower

/-!
# The Cartesian Hessian of a body solution (source 1377-1441)

Task `PartIII-b:C/ward/12/3/1/2/2/org`.  Source of record
`the November 2 reference manuscript`.

The free heat estimate `free:heat-estimate` (lines 1377-1424) bounds the whole spatial Hessian,
`‖ν D²u‖_r + ‖u_t‖_r ≤ C_{d,r} ‖F‖_r`; it is proved in the library as
`B0423.heat_estimate_complex` (componentwise `‖ν ∂_i∂_j u‖_q ≤ C ‖F‖_q`, kernel bounds 1384-1404,
Calderón–Zygmund 1405-1418, identification of the limit 1419-1424).  The window reduction
(lines 1426-1441: pull back `v(t,x) = e^{-t/2} w(τ₀+t, e^{-t/2}x)`, cut off, `θ = e^t`, average
over the centres with no inverse-period factor) was carried out for `νΔw` in
`Short/PartII-a` (`LocalWindowEstimate`, `GlobalFieldWindowBound`, `LaplacianFieldToYRep`,
`bodyLaplacianBound_of`).  "The same reasoning applies to any distributional `Y_r` solution"
(line 1442) and, with `ν D²u` in place of `νΔu`, gives `ν ∂_j∂_k w ∈ Y_r` with the same bound.

This file states the Hessian versions of the window objects and proves the averaging step
`bodyHessianBound_of` from the proved period-averaging leaves of Part II-a.  The transport back
from the window is the same as for the Laplacian (`∂_{y_j}∂_{y_k} = e^t ∂_{x_j}∂_{x_k}` under
`x = e^{t/2}y`, the factor of `Δ`), so the window field is `windowLap` of the single component
`D2 c j k` of the heat-estimate Hessian.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS IsSTTest sD2)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowLap winSet)

/-- The transpose of `ν ∂_{y_j}∂_{y_k}` on phase tests (source 1379 `ν D²u`, Cartesian
derivatives). -/
def nuHessT (ν : ℝ) (j k : Fin 3) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  ν • dy j (dy k Φ)

theorem isPhaseTest_nuHessT {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (ν : ℝ)
    (j k : Fin 3) : IsPhaseTest P (nuHessT ν j k Φ) :=
  ((hΦ.dy k).dy j).const_smul ν

/-- `H` is a weak `ν∂_j∂_kW` on the window `(τ₀-1, τ₀+1) × ℝ³`: against every smooth compactly
supported `ℂ³`-valued `ψ` supported in the window, `∫ W · ν∂_j∂_kψ = ∫ H · ψ` (bilinear dot
product), both integrands integrable.  (The Hessian analogue of `PartIIa.IsWindowLaplacian`.) -/
def IsWindowHess (ν τ₀ : ℝ) (j k : Fin 3) (W H : ℝ × Space → CVec3) : Prop :=
  ∀ ψ : ℝ × Space → CVec3, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) →
      Integrable (fun p => dotL (W p) (nuHessT ν j k ψ p)) ∧
        Integrable (fun p => dotL (H p) (ψ p)) ∧
        ∫ p, dotL (W p) (nuHessT ν j k ψ p) = ∫ p, dotL (H p) (ψ p)

/-! ### The window estimate (source 1426-1441) -/

/-- **Transport back of the window Hessian** (source 1429-1431; Hessian analogue of
`PartIIa.WindowBackEquation`): if the components `u_c = windowField χ τ₀ W c` of the cutoff
pull-back have weak second derivatives `D2 c i j ∈ L^r` (as produced by
`B0423.heat_estimate_complex`), then `windowLap` of the single component `D2 c j k` is a weak
`ν∂_j∂_kW` on the window. -/
def WindowBackHess : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (w : Yq P r)
    (W : ℝ × Space → CVec3), IsRep w W → ∀ χ : ℝ → ℝ, WindowCutoff χ → ∀ τ₀ : ℝ,
      ∀ D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ,
        (∀ c i j, MemLp (D2 c i j) (ENNReal.ofReal r.toReal) volume ∧
          UnforcedLeray.B0423.HasWeakSpaceDeriv2C (d := 3) (windowField χ τ₀ W c) i j
            (D2 c i j)) →
        ∀ j k : Fin 3, IsWindowHess ν τ₀ j k W (windowLap ν τ₀ fun c X => D2 c j k X)

/-- **The fixed-window Hessian estimate** (source 1426-1441 with the full `ν D²` of
`free:heat-estimate` 1379): for a distributional solution `(μ + L₀)w = f` in `Y_r`, every
centre `τ₀` and every `j, k`, there is a window Hessian `H` with
`∫_{τ₀-1}^{τ₀+1}‖H(τ)‖_r^r ≤ C_r^r ∫_{τ₀-2}^{τ₀+2}[‖f(τ)‖_r^r + (1+|μ|)^r‖w(τ)‖_r^r]`,
`C_r` independent of `P ≤ 1`, `ν`, `μ`, `τ₀`.  (Hessian analogue of
`PartIIa.LocalWindowEstimate`.) -/
def LocalWindowHess : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f → ∀ W : ℝ × Space → CVec3, IsRep w W →
        ∀ (j k : Fin 3) (τ₀ : ℝ), ∃ H : ℝ × Space → CVec3, IsWindowHess ν τ₀ j k W H ∧
          ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖H (τ, y)‖ₑ ^ r.toReal ≤
            ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
              (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
                ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)

/-! ### Gluing the window Hessians (source 1437-1441) -/

/-- **Measurability** (Hessian analogue of `PartIIa.WindowLapAEMeas`): a window Hessian is a.e.
strongly measurable on its window. -/
def WindowHessAEMeas : Prop :=
  ∀ (ν τ₀ : ℝ) (j k : Fin 3) (W H : ℝ × Space → CVec3), IsWindowHess ν τ₀ j k W H →
    AEStronglyMeasurable H (volume.restrict (winSet τ₀))

/-- **Uniqueness on a common interval** (Hessian analogue of `PartIIa.WindowLapUnique`). -/
def WindowHessUnique : Prop :=
  ∀ (ν τ₀ τ₁ a b : ℝ) (j k : Fin 3) (W H H' : ℝ × Space → CVec3),
    τ₀ - 1 ≤ a → b ≤ τ₀ + 1 → τ₁ - 1 ≤ a → b ≤ τ₁ + 1 →
    IsWindowHess ν τ₀ j k W H → IsWindowHess ν τ₁ j k W H' →
    LocallyIntegrableOn H (Ioo a b ×ˢ (univ : Set Space)) →
    LocallyIntegrableOn H' (Ioo a b ×ˢ (univ : Set Space)) →
      H =ᵐ[volume.restrict (Ioo a b ×ˢ (univ : Set Space))] H'

/-- **Partition of unity in `τ`** (Hessian analogue of `PartIIa.WindowLapPoU`): a field equal
a.e. to a window Hessian on each integer window is a window Hessian on every window
(`∂_j∂_k(χ(τ)ψ) = χ(τ)∂_j∂_kψ`). -/
def WindowHessPoU : Prop :=
  ∀ (ν : ℝ) (j k : Fin 3) (W H : ℝ × Space → CVec3) (Hk : ℤ → ℝ × Space → CVec3),
    (∀ n : ℤ, IsWindowHess ν (n : ℝ) j k W (Hk n)) →
    (∀ n : ℤ, H =ᵐ[volume.restrict (winSet (n : ℝ))] Hk n) →
      ∀ τ₀ : ℝ, IsWindowHess ν τ₀ j k W H

/-- **Periodicity** (Hessian analogue of `PartIIa.WindowLapPeriodic`). -/
def WindowHessPeriodic : Prop :=
  ∀ (P ν : ℝ), 0 < P → ∀ (j k : Fin 3) (W H : ℝ × Space → CVec3), StronglyMeasurable W →
    StronglyMeasurable H →
    (∀ᵐ τ : ℝ, (fun y => W (τ + P, y)) =ᵐ[volume] fun y => W (τ, y)) →
    (∀ τ₀ : ℝ, IsWindowHess ν τ₀ j k W H) →
    (∀ n : ℤ, LocallyIntegrableOn H (winSet (n : ℝ))) →
      ∀ᵐ τ : ℝ, (fun y => H (τ + P, y)) =ᵐ[volume] fun y => H (τ, y)

/-- **One global window Hessian with the window bound at every centre** (source 1437-1441;
Hessian analogue of `PartIIa.GlobalFieldWindowBound`). -/
def GlobalHessFieldWindowBound : Prop :=
  LocalWindowHess → ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f → ∀ W : ℝ × Space → CVec3, IsRep w W →
        ∀ j k : Fin 3, ∃ H : ℝ × Space → CVec3, StronglyMeasurable H ∧
          (∀ τ₀ : ℝ, IsWindowHess ν τ₀ j k W H) ∧
          (∀ᵐ τ : ℝ, (fun y => H (τ + P, y)) =ᵐ[volume] fun y => H (τ, y)) ∧
          ∀ τ₀ : ℝ, ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖H (τ, y)‖ₑ ^ r.toReal ≤
            ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
              (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
                ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)

/-! ### From the global field to `Y_r` -/

/-- **The window identity against `η(τ)Φ(τ,y)`** (Hessian analogue of
`PartIIa.WindowTestIdentityF04`). -/
def WindowTestIdentityHess : Prop :=
  ∀ (P ν τ₀ : ℝ) (j k : Fin 3) (W H : ℝ × Space → CVec3), IsWindowHess ν τ₀ j k W H →
    ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo (τ₀ - 1) (τ₀ + 1) →
      ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
        ∫ t, (η t : ℂ) * ∫ y, dotL (nuHessT ν j k Φ (t, y)) (W (t, y)) =
          ∫ t, (η t : ℂ) * ∫ y, dotL (Φ (t, y)) (H (t, y))

/-- **The field-to-`Y_r` step with representative** (Hessian analogue of
`PartIIa.LaplacianFieldToYRep`): a strongly measurable, a.e. periodic window Hessian of
`w`, `L^r` on a period, represents `a ∈ Y_r` with `ν∂_j∂_kw = a` against every phase test. -/
def HessFieldToYRep : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (j k : Fin 3)
    (w : Yq P r) (W : ℝ × Space → CVec3), IsRep w W → ∀ H : ℝ × Space → CVec3,
      StronglyMeasurable H → (∀ τ₀ : ℝ, IsWindowHess ν τ₀ j k W H) →
      (∀ᵐ τ : ℝ, (fun y => H (τ + P, y)) =ᵐ[volume] fun y => H (τ, y)) →
      ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖H (τ, y)‖ₑ ^ r.toReal < ⊤ →
        ∃ a : Yq P r, IsRep a H ∧ HasPhaseOp (nuHessT ν j k) w a

/-! ### The quantitative Hessian bound (source 1431-1441) -/

/-- **Quantitative body Hessian bound** (source 1377-1441; Hessian analogue of
`PartIIa.BodyLaplacianBound`): for `1 < r < ∞` there is `C ≥ 0` independent of `P ≤ 1`,
`ν > 0`, `μ` such that every distributional `Y_r` solution of `(μ + L₀)w = f` has
`ν∂_j∂_kw = a` in `Y_r` with `‖a‖ ≤ C(‖f‖ + (1+|μ|)‖w‖)`. -/
def BodyHessianBound : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f → ∀ j k : Fin 3,
        ∃ a : Yq P r, HasPhaseOp (nuHessT ν j k) w a ∧ ‖a‖ ≤ C * (‖f‖ + (1 + ‖μ‖) * ‖w‖)

/-- `BodyHessianBound` from the window estimate, the gluing and the field-to-`Y_r` step, with the
proved averaging leaves of Part II-a (`periodAverageBound`, `sliceIntegralYq`, `yqRepNorm`,
`normFromPower`); the proof is that of `PartIIa.bodyLaplacianBound_of`. -/
theorem bodyHessianBound_of (hloc : LocalWindowHess) (h1 : GlobalHessFieldWindowBound)
    (h4 : HessFieldToYRep) : BodyHessianBound := by
  intro r _ hr1 hrt
  obtain ⟨C, hC0, hC⟩ := h1 hloc r hr1 hrt
  have hs : 1 < r.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hrt).2 hr1
    simpa using this
  obtain ⟨K', hK0, hK'⟩ := UnforcedLeray.Short.PartIIa.normFromPower r.toReal hs C hC0
  refine ⟨K', hK0, ?_⟩
  intro P _ hP ν hν μ f w hf j k
  obtain ⟨W, hW⟩ := exists_isRep hrt w
  obtain ⟨H, hm, hwin, hper, hbd⟩ := hC P hP ν hν μ f w hf W hW j k
  have hav := UnforcedLeray.Short.PartIIa.periodAverageBound r hrt P C μ f w H hm hper hbd
  have hP3 := UnforcedLeray.Short.PartIIa.sliceIntegralYq r hrt P μ f w
  set R : ℝ≥0∞ := ‖f‖ₑ ^ r.toReal +
    ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w‖ₑ ^ r.toReal with hR
  have hRtop : R < ⊤ := by
    rw [hR]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        enorm_ne_top, ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        ENNReal.ofReal_ne_top) (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        enorm_ne_top)⟩
  have hfin : ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖H (τ, y)‖ₑ ^ r.toReal < ⊤ := by
    refine lt_of_le_of_lt hav ?_
    rw [hP3]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRtop)
  obtain ⟨a, haR, haOp⟩ := h4 r hrt P ν j k w W hW H hm hwin hper hfin
  refine ⟨a, haOp, ?_⟩
  have h5' := UnforcedLeray.Short.PartIIa.yqRepNorm r hrt P a H haR
  have key : ‖a‖ₑ ^ r.toReal ≤ 2 * ENNReal.ofReal C ^ r.toReal * R := by
    have hle : ENNReal.ofReal P * ‖a‖ₑ ^ r.toReal ≤
        ENNReal.ofReal P * (2 * ENNReal.ofReal C ^ r.toReal * R) := by
      rw [h5']
      calc _ ≤ 2 * ENNReal.ofReal C ^ r.toReal * (ENNReal.ofReal P * R) := by
            rw [← hP3]; exact hav
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_right
      (by simpa using Fact.out (p := 0 < P)) ENNReal.ofReal_ne_top).1 hle
  have := hK' ‖a‖ ‖f‖ ‖w‖ (1 + ‖μ‖) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (by positivity)
  refine this ?_
  simp only [ofReal_norm]
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
