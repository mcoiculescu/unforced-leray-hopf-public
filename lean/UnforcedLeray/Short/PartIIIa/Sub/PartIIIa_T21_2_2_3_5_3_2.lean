import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.ChangeVar

/-!
# `PartIII-a:T21/2/2/3/5/3/2` (`E1PhysRate`): decomposition

Source of record: `the November 2 reference manuscript` (SP) lines 2860-2864
(`w(s,x) = a⁻²W(z, x/√a)`, `d_z/d = -1/(2θ)`), 2945-2957 and 3137-3139 ("Reynolds' boundary term
cancels the dilation seam term. All calculations below may first be made on the fixed physical
cylinder and then rescaled"), 3060-3062 (`β = θ⁻¹`).

At `r = revAge ν s ζ`, `a = a(r)`, `β = νa`, `d = c/√a`, `Φ = mvPhi`, `w = p_d⁻¹`, `y = x/√a`, the
explicit fixed-cell derivative `physDerivForm` (`Sub/PartIIIa_T21_2_2_3_5_3.lean`) is rescaled term
by term; no integration by parts is needed, the seam bookkeeping being inside the fixed-cell
derivative:
* `(a⁻²)' = -2νa⁻³` and `∫_{C_c} wh|∂_kφ|² = a²∫_{C_d} w|∂_kΦ|²` (`adjF1_eq_fixed`) give `2β E_1`;
* `∂_r wh(√a y) = -a⁻²(∂_ζw + (β/2) y·∇w)` (`PhysWDeriv`, `∂_ζw = dtW`) gives
  `∫ (dtW + (β/2) y·∇w)|∂_kΦ|²` (`E1ScaleW`);
* `∂_kφ(√a y) = √a ∂_kΦ(y)` gives `2∫ w Re(conj ∂_kΦ · ψ_k)`, `ψ_k = -a^{3/2}(∂_k∂_rφ)(√a y)`
  (`E1ScaleR`, `psiK`).
From the moving equation (`hder`) and the chain rule `dr/dζ = -a²` (`MvPhiDt`),
`a ∂_rφ(√a y) = -(βΔΦ + V·∇Φ - χ)` (the terms `βΦ - (β/2)y·∇Φ` of `∂_ζΦ` cancel those of
`adjGen`); differentiating in `y_k` (`PsiDiff`) gives `ψ_k = xiRed_k - (β/2)∂_kΦ`. Finally
`(β/2)∫(2w + y·∇w)|∂_kΦ|² = β∫w|∂_kΦ|² + (β/2)∫ y·∇w|∂_kΦ|²` (`E1RateAlg`, with the integrability
`E1PsiInt`) identifies the sum with `e1Rate`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

/-- The rescaled `∂_k∂_rφ`: `ψ_k(y) = -a^{3/2} (∂_k∂_rφ)(r, √a y)`, `r = revAge ν s ζ`, `a = a(r)`
(SP 2860-2864, 3036-3037; `∂_k∂_rφ = pdCx k (adjDt t s φ r)`). -/
def psiK (ν t s : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ) (k : Fin 2) (y : ℝ × ℝ) : ℂ :=
  -((clockA ν (revAge ν s ζ) * Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ) : ℂ) *
    pdCx k (adjDt t s φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)

/-- **Leaf (calculus of the weight)** (SP 2860, 3044-3047): at the dilated point `x = √a y`,
`∂_r physW(r, √a y) = -a⁻²(dtW + (β/2) y·∇w)(y)`, `β = νa`, `w = p_d⁻¹`, `d = c/√a`. With
`physW(r', √a y) = (1 + K/a(r'))^{-m}`, `K = a y₂² + (c/π)² sin²(π√a y₁/c)`, and
`Q_d = 1 + y₂² + (d/π)² sin²(π y₁/d)`, this is `d∂_dQ_d + y·∇Q_d = 2(Q_d - 1)`. -/
def PhysWDeriv (m : ℝ) : Prop :=
  ∀ (ν c r : ℝ) (y : ℝ × ℝ), 0 < c → 0 < clockA ν r →
    deriv (fun r' => physW ν c m r' (Real.sqrt (clockA ν r) • y)) r =
      -((clockA ν r)⁻¹ ^ 2) *
        (dtW m (cellLen c (clockA ν r)) (ν * clockA ν r) y +
          ν * clockA ν r / 2 *
            (y.1 * B0579.pd 0 (periodicWeight (-m) (cellLen c (clockA ν r))) y +
              y.2 * B0579.pd 1 (periodicWeight (-m) (cellLen c (clockA ν r))) y))

/-- **Leaf (rescaling of the weight-derivative term)** (SP 2860-2864, 3036-3037), given the
pointwise identity `PhysWDeriv`: change of variables `x = √a y` (`integral_cell_scale`,
`|∂_kφ(√a y)|² = a|∂_kΦ(y)|²` by `pdCx_movingPhi`). No integrability is needed. -/
def E1ScaleW (m : ℝ) : Prop :=
  PhysWDeriv m →
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ → ∀ k : Fin 2,
      -(∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          deriv (fun r' => physW ν (ν ^ (-2 : ℝ)) m r' x) (revAge ν s ζ) *
            ‖pdCx k (φ (revAge ν s ζ)) x‖ ^ 2) =
        ∫ y in B0579.cell (mvLen ν (ν ^ (-2 : ℝ)) s ζ),
          (dtW m (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvBeta ν s ζ) y +
            mvBeta ν s ζ / 2 *
              (y.1 * B0579.pd 0 (periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ)) y +
                y.2 * B0579.pd 1 (periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ)) y)) *
            ‖pdCx k (mvPhi ν φ s ζ) y‖ ^ 2

/-- **Leaf (rescaling of the field-derivative term)** (SP 2860-2864, 3036-3037): change of
variables `x = √a y`, `physW(r, √a y) = w(y)`, `∂_kφ(√a y) = √a ∂_kΦ(y)` (`pdCx_movingPhi`).
No integrability is needed. -/
def E1ScaleR (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ → ∀ k : Fin 2,
      -(2 * ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          physW ν (ν ^ (-2 : ℝ)) m (revAge ν s ζ) x *
            ((starRingEnd ℂ) (pdCx k (φ (revAge ν s ζ)) x) *
              pdCx k (adjDt t s φ (revAge ν s ζ)) x).re) =
        2 * ∫ y in B0579.cell (mvLen ν (ν ^ (-2 : ℝ)) s ζ),
          periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) y *
            ((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) * psiK ν t s φ ζ k y).re

/-- **Leaf (chain rule of the moving adjoint)** (SP 2857-2862): `∂_rφ(r, ·)` is differentiable
(joint smoothness at the interior age), and with `dr/dζ = -a²`, `(a⁻¹)' = ν`, `(√a)' = -(ν/2)a^{3/2}`,
`∂_ζΦ(y) = βΦ(y) - (β/2) y·∇Φ(y) - a ∂_rφ(r, √a y)`. -/
def MvPhiDt (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ →
    Differentiable ℝ (adjDt t s φ (revAge ν s ζ)) ∧
    ∀ y : ℝ × ℝ, HasDerivAt (fun ζ' => mvPhi ν φ s ζ' y)
      ((mvBeta ν s ζ : ℂ) * mvPhi ν φ s ζ y -
        (mvBeta ν s ζ : ℂ) / 2 * radC (mvPhi ν φ s ζ) y -
        ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) *
          adjDt t s φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) • y)) ζ

/-- **Leaf (calculus: `∂_k` of the reduced equation)** (SP 2858-2862): if
`a g(√a y) = -(βΔΦ + V·∇Φ - χ)(y)` for all `y`, then
`-a^{3/2} ∂_kg(√a y) = β Δ∂_kΦ + V·∇∂_kΦ + (∂_kV)·∇Φ - ∂_kχ = xiRed_k - (β/2)∂_kΦ`
(`∂_k∂_l = ∂_l∂_k` for the smooth `Φ`). -/
def PsiDiff : Prop :=
  ∀ (a β : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (Φ χ g : ℝ × ℝ → ℂ), 0 < a →
    ContDiff ℝ ∞ Φ → ContDiff ℝ 1 V → ContDiff ℝ 1 χ → Differentiable ℝ g →
    (∀ y : ℝ × ℝ, ((a : ℝ) : ℂ) * g (Real.sqrt a • y) =
      -((β : ℂ) * lapC Φ y + transC V Φ y - χ y)) →
    ∀ (k : Fin 2) (y : ℝ × ℝ),
      -((a * Real.sqrt a : ℝ) : ℂ) * pdCx k g (Real.sqrt a • y) =
        xiRed β V Φ χ k y - (β : ℂ) / 2 * pdCx k Φ y

/-- **Leaf (integral algebra on the moving cell)** (SP 3062): with `ψ_k = xiRed_k - (β/2)∂_kΦ` and
`w Re(conj ∂_kΦ ψ_k)` integrable, `Σ_k [2β∫w|∂_kΦ|² + ∫(dtW + (β/2)y·∇w)|∂_kΦ|² + 2∫w Re(conj ∂_kΦ ψ_k)]`
is `e1Rate` (`(β/2)∫(2w + y·∇w)|∂_kΦ|² = β∫w|∂_kΦ|² + (β/2)∫y·∇w|∂_kΦ|²`; `dtW|∂_kΦ|²`,
`y·∇w|∂_kΦ|²` are integrable by `periodicWeightLogBounds`, `|y·∇w|, |d∂_dw| ≤ C w` on the cell). -/
def E1RateAlg (m : ℝ) : Prop :=
  ∀ (d β : ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (Φ χ : ℝ × ℝ → ℂ) (ψ : Fin 2 → ℝ × ℝ → ℂ),
    0 < d → MovRegLow m d Φ →
    (∀ k : Fin 2, IntegrableOn (fun y => periodicWeight (-m) d y *
      ((starRingEnd ℂ) (pdCx k Φ y) * ψ k y).re) (B0579.cell d)) →
    (∀ (k : Fin 2) (y : ℝ × ℝ), ψ k y = xiRed β V Φ χ k y - (β : ℂ) / 2 * pdCx k Φ y) →
    ∑ k : Fin 2,
        (2 * β * (∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k Φ y‖ ^ 2) +
          (∫ y in B0579.cell d,
            (dtW m d β y + β / 2 * (y.1 * B0579.pd 0 (periodicWeight (-m) d) y +
              y.2 * B0579.pd 1 (periodicWeight (-m) d) y)) * ‖pdCx k Φ y‖ ^ 2) +
          2 * ∫ y in B0579.cell d, periodicWeight (-m) d y *
            ((starRingEnd ℂ) (pdCx k Φ y) * ψ k y).re) =
      e1Rate m d β V Φ χ

/-- **Leaf (integrability of the rescaled field-derivative term)** (SP 3060-3073): `w|∂_kΦ|²` is
integrable (`MovAdjBasicReg`) and `w|ψ_k|² = a³ w|∂_k∂_rφ(√a ·)|²` is integrable on the moving
cell (rescaling of `∂_k∂_rφ ∈ X_{-m,c}`, `IsAdjointFlow.higherCont`, with
`periodicWeight_le_jb`, `transfer_weight_int`), hence `w Re(conj ∂_kΦ ψ_k)` by Cauchy-Schwarz. -/
def E1PsiInt (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ζ : ℝ), AdjFlowAt m ν tr t s φ ζ → ∀ k : Fin 2,
      IntegrableOn (fun y => periodicWeight (-m) (mvLen ν (ν ^ (-2 : ℝ)) s ζ) y *
        ((starRingEnd ℂ) (pdCx k (mvPhi ν φ s ζ) y) * psiK ν t s φ ζ k y).re)
        (B0579.cell (mvLen ν (ν ^ (-2 : ℝ)) s ζ))

/-- `(a(r)⁻²)' = -2ν a(r)⁻³`. -/
theorem deriv_clockA_inv_sq (ν r : ℝ) (ha : 0 < clockA ν r) :
    deriv (fun r' => (clockA ν r')⁻¹ ^ 2) r = -2 * ν * (clockA ν r)⁻¹ ^ 3 := by
  have hA : HasDerivAt (fun r' => clockA ν r') ν r := by
    have h := ((hasDerivAt_id r).const_mul ν).const_add 1
    simpa [clockA] using h
  have h : HasDerivAt (fun r' => (clockA ν r')⁻¹ ^ 2)
      ((2 : ℕ) * (clockA ν r)⁻¹ ^ (2 - 1) * (-ν / clockA ν r ^ 2)) r :=
    (hA.inv ha.ne').pow 2
  have ha' : clockA ν r ≠ 0 := ha.ne'
  rw [h.deriv]
  have e : (2 - 1 : ℕ) = 1 := rfl
  rw [e, pow_one, div_eq_mul_inv]
  push_cast
  ring

/-- **`E1PhysRate` from the leaves** (and the compiled `MovAdjBasicReg`, `MovingTrainVReg`). -/
theorem e1PhysRate_of (m : ℝ) (hD : PhysWDeriv m) (hW : E1ScaleW m) (hR : E1ScaleR m)
    (hP : MvPhiDt m) (hQ : PsiDiff) (hA : E1RateAlg m) (hI : E1PsiInt m)
    (hL : MovAdjBasicReg m) (hV : MovingTrainVReg) : E1PhysRate m := by
  intro ν tr t s φ ζ hζ χ hχ hper hder hint
  obtain ⟨hr, ha⟩ := adjFlowAt_age hζ
  have hν : 0 < ν := hζ.1
  have ht0 : 0 ≤ t := hζ.2.1
  obtain ⟨G, _, hF⟩ := hζ.2.2.2.1
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hr0 : 0 ≤ revAge ν s ζ := le_trans ht0 hr.1.le
  have hsm : ContDiff ℝ ∞ (φ (revAge ν s ζ)) := hF.smooth _ (Ioo_subset_Ico_self hr)
  have hreg : MovRegLow m (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvPhi ν φ s ζ) := hL ν tr t s φ ζ hζ
  have hd : 0 < mvLen ν (ν ^ (-2 : ℝ)) s ζ := by
    unfold mvLen cellLen
    exact div_pos hc (Real.sqrt_pos.mpr ha)
  -- the moving equation at the age `r`, differentiated in `y_k`
  obtain ⟨hgd, hdt⟩ := hP ν tr t s φ ζ hζ
  have hpt : ∀ y : ℝ × ℝ, ((clockA ν (revAge ν s ζ) : ℝ) : ℂ) *
      adjDt t s φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) • y) =
      -((mvBeta ν s ζ : ℂ) * lapC (mvPhi ν φ s ζ) y +
        transC (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) y - χ y) := by
    intro y
    have e := (hder y).unique (hdt y)
    unfold adjGen at e
    linear_combination e
  have hψ : ∀ (k : Fin 2) (y : ℝ × ℝ), psiK ν t s φ ζ k y =
      xiRed (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) χ k y -
        (mvBeta ν s ζ : ℂ) / 2 * pdCx k (mvPhi ν φ s ζ) y :=
    hQ (clockA ν (revAge ν s ζ)) (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ))
      (mvPhi ν φ s ζ) χ (adjDt t s φ (revAge ν s ζ)) ha hreg.smooth
      (hV ν (ν ^ (-2 : ℝ)) tr (revAge ν s ζ) hr0 ha).1 hχ hgd hpt
  have h6 := hA (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ))
    (mvPhi ν φ s ζ) χ (psiK ν t s φ ζ) hd hreg (hI ν tr t s φ ζ hζ) hψ
  rw [← h6]
  -- the rescaling of the three terms of `physDerivForm`
  have hS1 : adjE1 (mvLen ν (ν ^ (-2 : ℝ)) s ζ) m (mvPhi ν φ s ζ) =
      (clockA ν (revAge ν s ζ))⁻¹ ^ 2 * ∑ k : Fin 2, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν (revAge ν s ζ)))
          (x.1 / Real.sqrt (clockA ν (revAge ν s ζ)), x.2 / Real.sqrt (clockA ν (revAge ν s ζ))) *
          ‖pdCx k (φ (revAge ν s ζ)) x‖ ^ 2 :=
    adjF1_eq_fixed hν hc hr0 hsm
  have hW0 := hW hD ν tr t s φ ζ hζ 0
  have hW1 := hW hD ν tr t s φ ζ hζ 1
  have hR0 := hR ν tr t s φ ζ hζ 0
  have hR1 := hR ν tr t s φ ζ hζ 1
  simp only [physW] at hW0 hW1 hR0 hR1
  unfold adjE1 at hS1
  unfold physDerivForm
  rw [deriv_clockA_inv_sq ν _ ha]
  simp only [Fin.sum_univ_two] at hS1 ⊢
  have ha' : clockA ν (revAge ν s ζ) ≠ 0 := ha.ne'
  have hS := congrArg (fun z => clockA ν (revAge ν s ζ) ^ 2 * z) hS1
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ ha', one_pow, one_mul] at hS
  rw [← hS, neg_eq_iff_eq_neg.mp hW0, neg_eq_iff_eq_neg.mp hW1, neg_eq_iff_eq_neg.mp hR0,
    neg_eq_iff_eq_neg.mp hR1]
  have hb : mvBeta ν s ζ = ν * clockA ν (revAge ν s ζ) := rfl
  rw [hb]
  field_simp
  ring

end UnforcedLeray.Short.IIIa.AdjE1
