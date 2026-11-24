import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Setting
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique
import UnforcedLeray.Short.PartIIIa.Clock.Existence.BiotSavartField
import UnforcedLeray.Short.PartIIIa.T20_5_VelNormEqLp
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.RealBiotSavart

/-!


Source of record: `the November 2 reference manuscript`, lines 3228-3240
(`eq:ct-embeddings`) and 3176-3184.

Proof. `kcLp ξ` is the real part of the library velocity `V = B0583.velocity` of `reX ξ`, so
`‖kcLp ξ‖ ≤ ‖V‖` (`norm_realPartVelocityLp_le`). `V` is a Biot-Savart velocity of the vorticity
`reX ξ`, which agrees a.e. with `re (xFn ξ)` on the cell (`coeFn_reX`), so it is a Biot-Savart
velocity of `re (xFn ξ)` (`velocityIsBiotSavart_one`, `isBS_congr_omega` below). Uniqueness
(`CTE.isBiotSavart_unique`) gives `u = V` a.e. on the cell, hence `velNorm c u = velNorm c V`, and
`velNorm c V = ‖V‖` (`CTE.velNorm_eq_lp`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- Replacing the vorticity by an a.e. equal one (on the cell) keeps the Biot-Savart property. -/
theorem isBS_congr_omega {c : ℝ} {ω ω' : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (h : UnforcedLeray.Short.IIIa.IsBiotSavart c ω u)
    (hae : ω =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)] ω') :
    UnforcedLeray.Short.IIIa.IsBiotSavart c ω' u := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun ψ hψ => ?_⟩
  rw [← h3 ψ hψ]
  exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])

/-- **`kcLp_norm_le_velNorm`** (source 3228-3240, `eq:ct-embeddings`): the `L²` norm of `K_c ξ` is
bounded by `velNorm c u` for every Biot-Savart velocity `u` of the real part of `xFn ξ`. -/
theorem kcLp_norm_le_velNorm {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m)
    (u : ℝ × ℝ → Fin 2 → ℂ)
    (h : UnforcedLeray.Short.IIIa.IsBiotSavart c (fun x => (((xFn ξ x).re : ℝ) : ℂ)) u) :
    ENNReal.ofReal ‖kcLp ξ‖ ≤ UnforcedLeray.Short.IIIa.velNorm c u := by
  have hm : 1 ≤ m := (Fact.out : 1 < m).le
  have hc : 0 < c := Fact.out
  set V := UnforcedLeray.B0583.velocity c hm (reX ξ.1) (reX_circ ξ) with hVdef
  have hA : ‖kcLp ξ‖ ≤ ‖V‖ :=
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_realPartVelocityLp_le V
  have hB : UnforcedLeray.Short.IIIa.velNorm c (fun x j => (V : ℝ × ℝ → UnforcedLeray.B0581.Vel) x j)
      = ENNReal.ofReal ‖V‖ :=
    UnforcedLeray.Short.IIIa.CTE.velNorm_eq_lp c V
  have hV := UnforcedLeray.Short.IIIa.CTE.velocityIsBiotSavart_one c m hm (reX ξ.1) (reX_circ ξ)
  have hae : (fun x => (((reX ξ.1) x : ℝ) : ℂ)) =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)]
      (fun x => (((xFn ξ x).re : ℝ) : ℂ)) := by
    filter_upwards [ae_cell_of_ae_cellMeasure (coeFn_reX ξ.1)] with x hx
    rw [hx]
    rfl
  have hV' : UnforcedLeray.Short.IIIa.IsBiotSavart c (fun x => (((xFn ξ x).re : ℝ) : ℂ))
      (fun x j => (V : ℝ × ℝ → UnforcedLeray.B0581.Vel) x j) :=
    isBS_congr_omega hV hae
  have huniq := UnforcedLeray.Short.IIIa.CTE.isBiotSavart_unique c hc
    (fun x => (((xFn ξ x).re : ℝ) : ℂ)) u (fun x j => (V : ℝ × ℝ → UnforcedLeray.B0581.Vel) x j) h hV'
  have hEq : UnforcedLeray.Short.IIIa.velNorm c u =
      UnforcedLeray.Short.IIIa.velNorm c (fun x j => (V : ℝ × ℝ → UnforcedLeray.B0581.Vel) x j) := by
    unfold UnforcedLeray.Short.IIIa.velNorm
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : (fun x => u x j) =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)]
        (fun x => (V : ℝ × ℝ → UnforcedLeray.B0581.Vel) x j) :=
      huniq.mono fun x hx => congrFun hx j
    rw [eLpNorm_congr_ae hj]
  rw [hEq, hB]
  exact ENNReal.ofReal_le_ofReal hA

end UnforcedLeray.Short.PartIIIb.Concrete
