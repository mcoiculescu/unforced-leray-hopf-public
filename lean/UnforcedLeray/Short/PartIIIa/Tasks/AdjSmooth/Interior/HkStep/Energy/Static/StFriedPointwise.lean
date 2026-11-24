import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.FriedDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellPeriodicLocInt

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2/6`: Friedrichs' commutator, pointwise (`StFriedPointwise`)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071.
The commutator `stFried n a f` is written as one convolution integral per component,
`∫ φ_l(y) f(x - y) dy` with `φ_l(y) = ∂_lρ_n(y) (a_l(x - y) - a_l(x))`, and bounded by the
Lipschitz constant times the convolution of `Σ_l |∂_lρ_n| ‖·‖` with `|f|`.
Continuity uses `HasCompactSupport.continuous_convolution_left`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem stfp_integrable_C {k : ℝ × ℝ → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    {g : ℝ × ℝ → ℂ} (hg : LocallyIntegrable g volume) (x : ℝ × ℝ) :
    Integrable (fun y => k y • g (x - y)) volume := by
  have h := (hks.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk hg) x
  simpa [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply] using h

theorem stfp_integrable_R {k g : ℝ × ℝ → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    (hg : LocallyIntegrable g volume) (x : ℝ × ℝ) :
    Integrable (fun y => k y * g (x - y)) volume := by
  have h := (hks.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk hg) x
  simpa [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h

theorem stfp_cont_C {k : ℝ × ℝ → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    {g : ℝ × ℝ → ℂ} (hg : LocallyIntegrable g volume) :
    Continuous (cellConv k g) := by
  rw [cellConv_eq_convolution]
  exact hks.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk hg

theorem stFriedPointwise : UnforcedLeray.Short.IIIa.StFriedPointwise := by
  unfold StFriedPointwise
  intro c m n a A L f hc hacont hA hLip hper hf
  have hloc : LocallyIntegrable f volume := (cellPeriodicLocInt c m f hc hper hf).2
  have hnl : LocallyIntegrable (fun y => ‖f y‖) volume :=
    locallyIntegrableOn_univ.1 (hloc.locallyIntegrableOn univ).norm
  have hKc : ∀ l, Continuous (B0579.pd l (molKer n)) := fun l =>
    (st_pd_contDiff (st_molKer_contDiff n) l).continuous
  have hKs : ∀ l, HasCompactSupport (B0579.pd l (molKer n)) := fun l =>
    (st_molKer_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (B0579.dir l)
  have hAc : ∀ l, Continuous (fun y => ((a l y : ℝ) : ℂ)) := fun l =>
    Complex.continuous_ofReal.comp (hacont l)
  have hAloc : ∀ l, LocallyIntegrable (fun y => ((a l y : ℝ) : ℂ) * f y) volume := fun l => by
    have e : (fun y => ((a l y : ℝ) : ℂ) * f y) = fun y => f y * ((a l y : ℝ) : ℂ) :=
      funext fun y => mul_comm _ _
    rw [e]
    exact hloc.mul_continuous (hAc l)
  -- continuity
  have hcont : Continuous (stFried n a f) := by
    unfold stFried
    refine continuous_finsetSum _ fun l _ => ?_
    exact (stfp_cont_C (hKc l) (hKs l) (hAloc l)).sub
      ((hAc l).mul (stfp_cont_C (hKc l) (hKs l) hloc))
  -- one component as a single convolution integral
  have hsplit : ∀ (l : Fin 2) (x : ℝ × ℝ),
      cellConv (B0579.pd l (molKer n)) (fun y => ((a l y : ℝ) : ℂ) * f y) x -
        ((a l x : ℝ) : ℂ) * cellConv (B0579.pd l (molKer n)) f x =
      ∫ y, ((B0579.pd l (molKer n) y * (a l (x - y) - a l x) : ℝ) : ℂ) * f (x - y) := by
    intro l x
    have hi1 : Integrable
        (fun y => B0579.pd l (molKer n) y • (((a l (x - y) : ℝ) : ℂ) * f (x - y))) volume := by
      refine (stfp_integrable_C (k := fun y => B0579.pd l (molKer n) y * a l (x - y))
        ((hKc l).mul ((hacont l).comp (continuous_const.sub continuous_id)))
        ((hKs l).mul_right (f' := fun y => a l (x - y))) hloc x).congr (ae_of_all _ fun y => ?_)
      simp only [Complex.real_smul]
      push_cast
      ring
    have hi2 : Integrable
        (fun y => ((a l x : ℝ) : ℂ) * (B0579.pd l (molKer n) y • f (x - y))) volume :=
      (stfp_integrable_C (hKc l) (hKs l) hloc x).const_mul _
    unfold cellConv
    rw [← integral_const_mul, ← integral_sub hi1 hi2]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [Complex.real_smul]
    push_cast
    ring
  have hrep : ∀ x : ℝ × ℝ, stFried n a f x = ∑ l : Fin 2,
      ∫ y, ((B0579.pd l (molKer n) y * (a l (x - y) - a l x) : ℝ) : ℂ) * f (x - y) := by
    intro x
    unfold stFried
    exact Finset.sum_congr rfl fun l _ => hsplit l x
  -- kernels for the bound
  have hbk : ∀ l, Continuous (fun y => |B0579.pd l (molKer n) y| * ‖y‖) := fun l =>
    ((hKc l).abs).mul continuous_norm
  have hbks : ∀ l, HasCompactSupport (fun y => |B0579.pd l (molKer n) y| * ‖y‖) := fun l =>
    (hKs l).abs.mul_right (f' := fun y => ‖y‖)
  have hbint : ∀ (l : Fin 2) (x : ℝ × ℝ),
      Integrable (fun y => L * (|B0579.pd l (molKer n) y| * ‖y‖ * ‖f (x - y)‖)) volume :=
    fun l x => (stfp_integrable_R (hbk l) (hbks l) hnl x).const_mul L
  have hpt : ∀ (l : Fin 2) (x y : ℝ × ℝ),
      ‖((B0579.pd l (molKer n) y * (a l (x - y) - a l x) : ℝ) : ℂ) * f (x - y)‖ ≤
        L * (|B0579.pd l (molKer n) y| * ‖y‖ * ‖f (x - y)‖) := by
    intro l x y
    have hb : |a l (x - y) - a l x| ≤ L * ‖y‖ := by
      have h := hLip l (x - y) x
      rwa [sub_sub_cancel_left, norm_neg] at h
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have h1 : |B0579.pd l (molKer n) y| * |a l (x - y) - a l x| ≤
        |B0579.pd l (molKer n) y| * (L * ‖y‖) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (f (x - y)))
    calc |B0579.pd l (molKer n) y| * |a l (x - y) - a l x| * ‖f (x - y)‖
        ≤ |B0579.pd l (molKer n) y| * (L * ‖y‖) * ‖f (x - y)‖ := h2
      _ = L * (|B0579.pd l (molKer n) y| * ‖y‖ * ‖f (x - y)‖) := by ring
  -- the right-hand side as a real integral
  have hRHS : ∀ x : ℝ × ℝ,
      cellConv (fun y => ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖)
        (fun y => ((‖f y‖ : ℝ) : ℂ)) x =
      ((∫ y, ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖ * ‖f (x - y)‖ : ℝ) : ℂ) := by
    intro x
    have e : ∀ y : ℝ × ℝ,
        (∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖) • ((‖f (x - y)‖ : ℝ) : ℂ) =
          (((∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖ * ‖f (x - y)‖ : ℝ)) : ℂ) := by
      intro y
      simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sum, Finset.sum_mul]
    unfold cellConv
    exact (integral_congr_ae (ae_of_all _ e)).trans integral_ofReal
  have hRnonneg : ∀ x : ℝ × ℝ,
      0 ≤ ∫ y, ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖ * ‖f (x - y)‖ :=
    fun x => integral_nonneg fun y => Finset.sum_nonneg fun l _ => by positivity
  refine ⟨hcont, fun x => ?_⟩
  rw [hRHS x, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hRnonneg x), hrep x]
  calc ‖∑ l : Fin 2, ∫ y, ((B0579.pd l (molKer n) y * (a l (x - y) - a l x) : ℝ) : ℂ) *
        f (x - y)‖
      ≤ ∑ l : Fin 2, ‖∫ y, ((B0579.pd l (molKer n) y * (a l (x - y) - a l x) : ℝ) : ℂ) *
        f (x - y)‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 2, ∫ y, L * (|B0579.pd l (molKer n) y| * ‖y‖ * ‖f (x - y)‖) :=
        Finset.sum_le_sum fun l _ => (norm_integral_le_integral_norm _).trans
          (integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _) (hbint l x)
            (ae_of_all _ fun y => hpt l x y))
    _ = ∫ y, ∑ l : Fin 2, L * (|B0579.pd l (molKer n) y| * ‖y‖ * ‖f (x - y)‖) :=
        (integral_finsetSum _ fun l _ => hbint l x).symm
    _ = ∫ y, L * ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖ * ‖f (x - y)‖ :=
        integral_congr_ae (ae_of_all _ fun y => by simp only [Finset.mul_sum])
    _ = L * ∫ y, ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖ * ‖f (x - y)‖ :=
        integral_const_mul _ _

end UnforcedLeray.Short.IIIa
