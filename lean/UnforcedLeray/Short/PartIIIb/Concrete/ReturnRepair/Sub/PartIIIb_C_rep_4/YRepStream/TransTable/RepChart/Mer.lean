import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.RepChart.Chart
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_2.AxiU
import UnforcedLeray.Short.PartIIIa.Compose

/-!
# `RepChart/Mer`: the meridional trace of a continuous periodic axisymmetric field
(source 121-124, 2031, 2522-2523, 2706, 5134-5139)

For a jointly continuous `V`, the meridional trace `merTr V` is jointly continuous; for a
`P`-periodic `V` it is `P`-periodic; for `V(τ)` axisymmetric without swirl (pointwise) it is at
most `|V(τ, y)|` at every point (`|V(τ,y)| = |V(τ,(ϱ y,0,y₃))|`, `axiDens_azimuth`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace RC

theorem merTr_continuous {V : ℝ → Space → Space}
    (hV : Continuous (fun x : ℝ × Space => V x.1 x.2)) :
    Continuous (fun x : ℝ × Space => merTr V x.1 x.2) := by
  have hpt : Continuous (fun x : ℝ × Space =>
      ((x.1, (!₂[ϱ x.2, 0, x.2 2] : Space)) : ℝ × Space)) := by
    refine continuous_fst.prodMk ?_
    refine (PiLp.continuous_toLp 2 _).comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      unfold ϱ
      fun_prop
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact continuous_const
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons]
      exact (PiLp.continuous_apply 2 _ 2).comp continuous_snd
  have hW : Continuous (fun x : ℝ × Space => V x.1 (!₂[ϱ x.2, 0, x.2 2])) :=
    hV.comp hpt
  have h0 : Continuous (fun x : ℝ × Space => V x.1 (!₂[ϱ x.2, 0, x.2 2]) 0) :=
    (PiLp.continuous_apply 2 _ 0).comp hW
  have h2 : Continuous (fun x : ℝ × Space => V x.1 (!₂[ϱ x.2, 0, x.2 2]) 2) :=
    (PiLp.continuous_apply 2 _ 2).comp hW
  unfold merTr
  refine continuous_norm.comp ?_
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i
  · simpa using h0
  · simpa using h2

theorem merTr_measurable {V : ℝ → Space → Space}
    (hV : Continuous (fun x : ℝ × Space => V x.1 x.2)) :
    Measurable (Function.uncurry fun τ y => ENNReal.ofReal (merTr V τ y)) :=
  ENNReal.measurable_ofReal.comp (merTr_continuous hV).measurable

theorem merTr_periodic {V : ℝ → Space → Space} {P : ℝ} (h : ∀ τ, V (τ + P) = V τ) (τ : ℝ)
    (y : Space) : merTr V (τ + P) y = merTr V τ y := by
  unfold merTr
  rw [h τ]

theorem merTr_le {V : ℝ → Space → Space} {τ : ℝ} (h : AxiNoSwirlPt (V τ)) (y : Space) :
    merTr V τ y ≤ ‖V τ y‖ := by
  rw [(axiDens_azimuth h y).1]
  exact UnforcedLeray.Short.IIIa.norm_meridPart_le _

theorem merTr_lintegral_le {V : ℝ → Space → Space} {τ : ℝ} (h : AxiNoSwirlPt (V τ)) :
    ∫⁻ y, ENNReal.ofReal (merTr V τ y) ^ (11 / 4 : ℝ) ≤ ∫⁻ y, ‖V τ y‖ₑ ^ (11 / 4 : ℝ) := by
  refine lintegral_mono fun y => ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (merTr_le h y)

end RC

end UnforcedLeray.Short.PartIIIb.Concrete

end
