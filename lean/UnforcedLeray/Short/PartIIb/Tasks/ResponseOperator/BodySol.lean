import UnforcedLeray.Short.PartIIb.Tasks.ResponseOperator.Lift
import UnforcedLeray.Short.PartIIb.Tasks.ResponseOperator.RealGraph
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.YqOSymm
import UnforcedLeray.Short.PartIIb.Bridge.Consequences
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.LerayPairSol
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.SolSeparation
import UnforcedLeray.Short.PartIIb.StatementsMixed

/-!
# Helper `ResponseOperator/BodySol`: solving the free body equation on `HpR p.c`

For `p : Params` with `p.period ≤ 1` and `f : HpR p.c`, `solD p hp1 f : D p.period p.ν q0E` is the
solenoidal solution of `bodyOp p.period p.ν q0E 0 w = lerayY (liftY p f)` given by
`commonBodyProjected_of lerayYResolventComm`. By injectivity of `bodyOp p.period p.ν q0E 0` and
`commonBodyGraphBound`:
* `solD p hp1` is `ℝ`-linear in `f`,
* `(solD p hp1 f : Yq p.period q0E) ∈ Ysigma p.period q0E` and `∈ realSub p.period q0E`,
* `graphNormD (solD p hp1 f) ≤ C_body * (π R²)^{1/p} * ‖f‖` for a universal constant `C_body > 0`,
* for any profile `b` with `IsResponse p.ν p.c p.ε 0 bgp (toProf p.c f) b`, `solD p hp1 f` has
  representative `NvC p.R b` (`HasRep` and `rep =ᵃᵉ NvC p.R b`), and hence lies in `Osym` whenever
  `IsKop p Ke`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.RespOp

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.RieszLp UnforcedLeray.Short.PartIIa UnforcedLeray.Short.IIb

/-- The solenoidal `D p.period p.ν q0E` solution of `L₀ w = 𝔓 (liftY p f)`. -/
def solD (p : Params) (hp1 : p.period ≤ 1) (f : HpR p.c) : D p.period p.ν q0E :=
  (commonBodyProjected_of lerayYResolventComm q0E one_lt_q0E q0E_lt_three
    p.period hp1 p.ν p.ν_pos 0 gammaR_q0E_pos (liftY p f)).choose

theorem solD_mem_Ysigma (p : Params) (hp1 : p.period ≤ 1) (f : HpR p.c) :
    (solD p hp1 f : Yq p.period q0E) ∈ Ysigma p.period q0E :=
  (commonBodyProjected_of lerayYResolventComm q0E one_lt_q0E q0E_lt_three
    p.period hp1 p.ν p.ν_pos 0 gammaR_q0E_pos (liftY p f)).choose_spec.1

theorem bodyOp_solD (p : Params) (hp1 : p.period ≤ 1) (f : HpR p.c) :
    bodyOp p.period p.ν q0E 0 (solD p hp1 f) =
      lerayY p.period q0E one_lt_q0E q0E_ne_top (liftY p f) :=
  (commonBodyProjected_of lerayYResolventComm q0E one_lt_q0E q0E_lt_three
    p.period hp1 p.ν p.ν_pos 0 gammaR_q0E_pos (liftY p f)).choose_spec.2

theorem solD_mem_realSub (p : Params) (hp1 : p.period ≤ 1) (f : HpR p.c) :
    (solD p hp1 f : Yq p.period q0E) ∈ realSub p.period q0E := by
  refine mem_realSub_of_bodyOp_zero hp1 p.ν_pos (solD p hp1 f) ?_
  rw [bodyOp_solD]
  exact lerayY_mem_realSub p.period (liftY p f) (liftY_mem_realSub p f)

theorem solD_add (p : Params) (hp1 : p.period ≤ 1) (f₁ f₂ : HpR p.c) :
    solD p hp1 (f₁ + f₂) = solD p hp1 f₁ + solD p hp1 f₂ := by
  apply bodyOp_zero_injective hp1 p.ν_pos
  rw [bodyOp_solD, liftY_add, map_add, map_add, bodyOp_solD, bodyOp_solD]

theorem solD_smul (p : Params) (hp1 : p.period ≤ 1) (a : ℝ) (f : HpR p.c) :
    solD p hp1 (a • f) = a • solD p hp1 f := by
  apply bodyOp_zero_injective hp1 p.ν_pos
  have hsmD : (a • solD p hp1 f : D p.period p.ν q0E) = (a : ℂ) • solD p hp1 f := rfl
  have hsmY : ∀ u : Yq p.period q0E, a • u = (a : ℂ) • u := fun _ => rfl
  rw [bodyOp_solD, liftY_smul, hsmY, map_smul, hsmD, map_smul, bodyOp_solD]

/-- Universal constant from `commonBodyGraphBound` at `q0E`. -/
def C_graph : ℝ := (commonBodyGraphBound q0E one_lt_q0E q0E_lt_three).choose

theorem C_graph_nonneg : 0 ≤ C_graph :=
  (commonBodyGraphBound q0E one_lt_q0E q0E_lt_three).choose_spec.1

/-- Universal constant for the `D`-graph norm of `solD`. -/
def C_body : ℝ := C_graph * 23 * ‖lerayC q0E one_lt_q0E q0E_ne_top‖ + 1

theorem C_body_pos : 0 < C_body := by
  unfold C_body
  have h1 : 0 ≤ C_graph := C_graph_nonneg
  have h2 : 0 ≤ ‖lerayC q0E one_lt_q0E q0E_ne_top‖ := norm_nonneg _
  positivity

theorem gammaR_q0E_eq : gammaR q0E = 1 / 22 := by
  unfold q0E B0281.q0 gammaR
  rw [ENNReal.toReal_ofReal (by norm_num)]
  norm_num

theorem graphNormD_solD_le (p : Params) (hp1 : p.period ≤ 1) (f : HpR p.c) :
    graphNormD (solD p hp1 f) ≤ C_body * (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖f‖ := by
  obtain ⟨g, -, hbound⟩ := (commonBodyGraphBound q0E one_lt_q0E q0E_lt_three).choose_spec.2
    p.period hp1 p.ν p.ν_pos 0 gammaR_q0E_pos (solD p hp1 f)
  have hsqrt : 0 ≤ Real.sqrt p.ν * ∑ j, ‖g j‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hfac : 1 + (1 + ‖(0 : ℂ)‖) / ((0 : ℂ).re + gammaR q0E) = 23 := by
    rw [norm_zero, Complex.zero_re, zero_add, add_zero, gammaR_q0E_eq]
    norm_num
  have h1 : graphNormD (solD p hp1 f) ≤
      C_graph * 23 * ‖bodyOp p.period p.ν q0E 0 (solD p hp1 f)‖ := by
    change graphNormD (solD p hp1 f) + Real.sqrt p.ν * ∑ j, ‖g j‖ ≤
      C_graph * (1 + (1 + ‖(0 : ℂ)‖) / ((0 : ℂ).re + gammaR q0E)) *
        ‖bodyOp p.period p.ν q0E 0 (solD p hp1 f)‖ at hbound
    rw [hfac] at hbound
    linarith
  have h2 : ‖bodyOp p.period p.ν q0E 0 (solD p hp1 f)‖ ≤
      ‖lerayC q0E one_lt_q0E q0E_ne_top‖ * ‖liftY p f‖ := by
    rw [bodyOp_solD]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_lerayY_le one_lt_q0E q0E_ne_top) (norm_nonneg _))
  have h3 : ‖bodyOp p.period p.ν q0E 0 (solD p hp1 f)‖ ≤
      ‖lerayC q0E one_lt_q0E q0E_ne_top‖ * ((Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖f‖) := by
    rw [← norm_liftY p f]
    exact h2
  have hCg : 0 ≤ C_graph * 23 := mul_nonneg C_graph_nonneg (by norm_num)
  have h4 : graphNormD (solD p hp1 f) ≤
      C_graph * 23 * ‖lerayC q0E one_lt_q0E q0E_ne_top‖ *
        (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖f‖ := by
    calc graphNormD (solD p hp1 f)
        ≤ C_graph * 23 * ‖bodyOp p.period p.ν q0E 0 (solD p hp1 f)‖ := h1
      _ ≤ C_graph * 23 *
            (‖lerayC q0E one_lt_q0E q0E_ne_top‖ * ((Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖f‖)) :=
          mul_le_mul_of_nonneg_left h3 hCg
      _ = C_graph * 23 * ‖lerayC q0E one_lt_q0E q0E_ne_top‖ *
            (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖f‖ := by ring
  have hR : 0 ≤ (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖f‖ := by
    have : 0 < p.R := p.R_pos
    positivity
  unfold C_body
  nlinarith

theorem solD_hasRep_of_isResponse (p : Params) (hp1 : p.period ≤ 1) (f : HpR p.c) (b : CProf)
    (hb : IsResponse p.ν p.c p.ε 0 bgp (toProf p.c f) b) :
    (∀ᵐ x : ℝ × Space, rep (solD p hp1 f : Yq p.period q0E) x.1 x.2 = NvC p.R b x) ∧
      HasRep (solD p hp1 f : Yq p.period q0E) (NvC p.R b) := by
  have hr : 0 < bgp := by norm_num [bgp]
  have h1 : 1 < bgp := by norm_num [bgp]
  have hfr : IsFreeResponse p.ν 0 bgp p.period (NvC p.R (toProf p.c f)) (NvC p.R b) := hb
  obtain ⟨Wq, hWrep, -⟩ := exists_hasRepY p.period bgp hr (NvC p.R b) hfr.mem_w
  obtain ⟨-, hD, -, hb_op⟩ :=
    (isFreeResponse_iff hr lerayPairSol solSeparation h1 (hasRepY_liftY p f) hWrep).1 hfr
  have hEqD : (⟨Wq, hD⟩ : D p.period p.ν q0E) = solD p hp1 f :=
    bodyOp_zero_injective hp1 p.ν_pos (hb_op.trans (bodyOp_solD p hp1 f).symm)
  have hEqY : Wq = (solD p hp1 f : Yq p.period q0E) := congrArg Subtype.val hEqD
  rw [hEqY] at hWrep
  exact ⟨rep_ae_eq_of_hasRepY hWrep, hasRepY_iff_hasRep.1 hWrep⟩

theorem solD_mem_Osym_of_isKop (p : Params) (hp1 : p.period ≤ 1)
    {Ke : HpR p.c →L[ℝ] HpR p.c} (hK : IsKop p Ke) (f : HpR p.c) :
    (solD p hp1 f : Yq p.period q0E) ∈ Osym p.period q0E := by
  obtain ⟨b, -, hb, -⟩ := hK f
  have hRep := (solD_hasRep_of_isResponse p hp1 f b hb).2
  exact yqOSymm p.period (solD p hp1 f : Yq p.period q0E) (NvC p.R b) hRep
    (fun g hg τ y => NvCInvariantHelp.nvC_equiv p.R b g hg (τ, y))

end UnforcedLeray.Short.IIb.RespOp

end
