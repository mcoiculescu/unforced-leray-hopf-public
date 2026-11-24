import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGradOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7.L2

/-!
# `MeanJetScaleBound` from six calculus leaves (`PartIII-b:C/rep/8/2/pres/5/3`)

Source of record: `the November 2 reference manuscript`
lines 4784 (`W^mt(y) = ε²V(εy)`), 5455 (`Y^mt = D_{μ+1}X^mt = (-½y·∇ - νΔ + μ + ½)X^mt`),
5267-5268.  Notation `F = Xsc X ε = ε²X(ε·)`, `v = ofLp y`, `w = ε • v`.
-/

set_option autoImplicit false

noncomputable section

open WithLp

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace MeanScaleSub

/-- WithLp transport, first order: the Fréchet derivative of `y ↦ toLp 2 (G (ofLp y))` has
operator norm at most `2‖DG‖` (`‖toLp u‖₂ ≤ √3‖u‖_∞ ≤ 2‖u‖`, `‖ofLp h‖_∞ ≤ ‖h‖₂`). -/
def TrFd : Prop := ∀ (G : Vec3 → Vec3) (y : Space), DifferentiableAt ℝ G (ofLp y) →
  ‖fderiv ℝ (fun y' : Space => toLp 2 (G (ofLp y'))) y‖ ≤ 2 * ‖fderiv ℝ G (ofLp y)‖

/-- `‖physPd (toLp ∘ G ∘ ofLp) j y‖ ≤ 2‖DG(ofLp y)‖`
(`physPd f j y = fderiv ℝ f y (coordinateVector j)`, `‖coordinateVector j‖ = 1`). -/
def TrPd : Prop := ∀ (G : Vec3 → Vec3) (j : Fin 3) (y : Space), Differentiable ℝ G →
  ‖physPd (fun y' : Space => toLp 2 (G (ofLp y'))) j y‖ ≤ 2 * ‖fderiv ℝ G (ofLp y)‖

/-- `‖physPd2 (toLp ∘ G ∘ ofLp) j l y‖ ≤ 2‖D²G(ofLp y)‖`
(`physPd2 f j l = physPd (physPd f l ·) j`; apply the transport to `v ↦ DG(v)e_l`). -/
def TrPd2 : Prop := ∀ (G : Vec3 → Vec3) (j l : Fin 3) (y : Space), ContDiff ℝ 2 G →
  ‖physPd2 (fun y' : Space => toLp 2 (G (ofLp y'))) j l y‖ ≤
    2 * ‖fderiv ℝ (fderiv ℝ G) (ofLp y)‖

/-- `‖D(ε²X(ε·))(v)‖ ≤ ε³‖DX(εv)‖` (`JetClockCore.fderiv_Xsc`; `‖iteratedFDeriv ℝ 1 X w‖ = ‖fderiv ℝ X w‖`
via `norm_iteratedFDeriv_fderiv`). -/
def ScD1 : Prop := ∀ (X : Vec3 → Vec3) (ε : ℝ) (v : Vec3), ContDiff ℝ 3 X → 0 < ε →
  ‖fderiv ℝ (JetClockCore.Xsc X ε) v‖ ≤ ε ^ 3 * ‖iteratedFDeriv ℝ 1 X (ε • v)‖

/-- `‖D²(ε²X(ε·))(v)‖ ≤ ε⁴‖D²X(εv)‖` (apply `JetClockCore.fderiv_scale` to `fderiv (Xsc X ε)`
= `(ε²ε) • fderiv X (ε·)`, then `norm_iteratedFDeriv_fderiv`). -/
def ScD2 : Prop := ∀ (X : Vec3 → Vec3) (ε : ℝ) (v : Vec3), ContDiff ℝ 3 X → 0 < ε →
  ‖fderiv ℝ (fderiv ℝ (JetClockCore.Xsc X ε)) v‖ ≤ ε ^ 4 * ‖iteratedFDeriv ℝ 2 X (ε • v)‖

/-- `‖D(ΔF)(v)‖ ≤ 3ε⁵‖D³X(εv)‖` for `F = ε²X(ε·)`
(`JetClockCore.fderiv_vecLap_Xsc` : `ε⁵ • fderiv (vecLap X) (ε•v)`; then
`StreamThird.fderiv_vecLap_apply`, `StreamThird.third_le`, `StreamThird.norm_single_le`,
`ContinuousLinearMap.opNorm_le_bound`). -/
def ScLap : Prop := ∀ (X : Vec3 → Vec3) (ε : ℝ) (v : Vec3), ContDiff ℝ 3 X → 0 < ε →
  ‖fderiv ℝ (vecLap (JetClockCore.Xsc X ε)) v‖ ≤ 3 * ε ^ 5 * ‖iteratedFDeriv ℝ 3 X (ε • v)‖

end MeanScaleSub

open MeanScaleSub

theorem meanJetScaleBound_of (h1 : TrFd) (h2 : TrPd) (h3 : TrPd2) (h4 : ScD1) (h5 : ScD2)
    (h6 : ScLap) : MeanJetScaleBound := by
  intro X ε ν μ hX hε hε1 hν hμ hμ1 y
  have hF : ContDiff ℝ 3 (JetClockCore.Xsc X ε) := JetClockCore.Xsc_contDiff hX ε
  set v : Vec3 := ofLp y with hv
  set F := JetClockCore.Xsc X ε with hFdef
  set a1 := ‖iteratedFDeriv ℝ 1 X (ε • v)‖ with ha1
  set a2 := ‖iteratedFDeriv ℝ 2 X (ε • v)‖ with ha2
  set a3 := ‖iteratedFDeriv ℝ 3 X (ε • v)‖ with ha3
  set r := Real.sqrt (eucSq (ε • v)) with hr
  have ha1n : 0 ≤ a1 := norm_nonneg _
  have ha2n : 0 ≤ a2 := norm_nonneg _
  have ha3n : 0 ≤ a3 := norm_nonneg _
  have hrn : 0 ≤ r := Real.sqrt_nonneg _
  have hε3 : 0 < ε ^ 3 := by positivity
  have hε4 : 0 < ε ^ 4 := by positivity
  have hε5 : 0 < ε ^ 5 := by positivity
  have b1 := h4 X ε v hX hε
  have b2 := h5 X ε v hX hε
  have b3 := h6 X ε v hX hε
  -- sup norm ≤ euclidean norm
  have hw : ‖ε • v‖ ≤ r := by
    rw [hr, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    unfold eucSq
    have := Finset.single_le_sum (f := fun k : Fin 3 => (ε • v) k ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    simpa using this
  have hnorm : ε * ‖v‖ = ‖ε • v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  -- derivative of Yf
  have hY : ‖fderiv ℝ (JetClockCore.Yf F ν μ) v‖ ≤
      5 / 4 * (ε ^ 3 * a1) + 1 / 2 * (ε ^ 3 * (r * a2)) + ν * (3 * ε ^ 5 * a3) := by
    rw [(JetClockCore.hasFDeriv_Yf hF ν μ v).fderiv]
    have hflip : ‖(fderiv ℝ (fderiv ℝ F) v).flip v‖ ≤ ‖fderiv ℝ (fderiv ℝ F) v‖ * ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
      have e1 : ‖(fderiv ℝ (fderiv ℝ F) v).flip v u‖ =
          ‖fderiv ℝ (fderiv ℝ F) v u v‖ := rfl
      rw [e1]
      calc ‖fderiv ℝ (fderiv ℝ F) v u v‖
          ≤ ‖fderiv ℝ (fderiv ℝ F) v u‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ (fderiv ℝ F) v‖ * ‖u‖ * ‖v‖ := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (fderiv ℝ F) v‖ * ‖v‖ * ‖u‖ := by ring
    have hflip2 : ‖(fderiv ℝ (fderiv ℝ F) v).flip v‖ ≤ ε ^ 3 * (r * a2) := by
      calc _ ≤ ‖fderiv ℝ (fderiv ℝ F) v‖ * ‖v‖ := hflip
        _ ≤ (ε ^ 4 * a2) * ‖v‖ := by gcongr
        _ = ε ^ 3 * (a2 * (ε * ‖v‖)) := by ring
        _ ≤ ε ^ 3 * (a2 * r) := by rw [hnorm]; gcongr
        _ = ε ^ 3 * (r * a2) := by ring
    have c1 : ‖(-(1 / 2 : ℝ)) • (fderiv ℝ F v + (fderiv ℝ (fderiv ℝ F) v).flip v)‖ ≤
        1 / 2 * (ε ^ 3 * a1 + ε ^ 3 * (r * a2)) := by
      rw [norm_smul]
      simp only [norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      gcongr
      exact (norm_add_le _ _).trans (add_le_add b1 hflip2)
    have c2 : ‖ν • fderiv ℝ (vecLap F) v‖ ≤ ν * (3 * ε ^ 5 * a3) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hν]
      gcongr
    have c3 : ‖(μ + 1 / 2) • fderiv ℝ F v‖ ≤ (μ + 1 / 2) * (ε ^ 3 * a1) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      gcongr
    have := (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add c1 c2)) c3)
    refine this.trans ?_
    nlinarith [mul_nonneg hε3.le ha1n, mul_nonneg hε3.le (mul_nonneg hrn ha2n)]
  -- the three pieces of the density
  have dY := h1 (JetClockCore.Yf F ν μ) y
    ((JetClockCore.hasFDeriv_Yf hF ν μ v).differentiableAt)
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have dP : ∀ j : Fin 3, ‖physPd (fun y' : Space => toLp 2 (F (ofLp y'))) j y‖ ≤
      2 * (ε ^ 3 * a1) := fun j =>
    (h2 F j y hFd).trans (by gcongr)
  have dP2 : ∀ j l : Fin 3, ‖physPd2 (fun y' : Space => toLp 2 (F (ofLp y'))) j l y‖ ≤
      2 * (ε ^ 4 * a2) := fun j l =>
    (h3 F j l y (hF.of_le (by norm_num))).trans (by gcongr)
  have sP : ∑ j : Fin 3, ‖physPd (fun y' : Space => toLp 2 (F (ofLp y'))) j y‖ ≤
      3 * (2 * (ε ^ 3 * a1)) := by
    refine (Finset.sum_le_sum fun j _ => dP j).trans ?_
    simp
  have sP2 : ∑ j : Fin 3, ∑ l : Fin 3,
      ‖physPd2 (fun y' : Space => toLp 2 (F (ofLp y'))) j l y‖ ≤ 3 * (3 * (2 * (ε ^ 4 * a2))) := by
    refine (Finset.sum_le_sum fun j _ => (Finset.sum_le_sum fun l _ => dP2 j l)).trans ?_
    simp
  unfold meanJetDens
  have hε4le : ε ^ 4 ≤ ε ^ 3 := by
    have : ε ^ 4 = ε ^ 3 * ε := by ring
    rw [this]; nlinarith
  have hε5le : ε ^ 5 ≤ ε ^ 3 := by
    have : ε ^ 5 = ε ^ 3 * ε ^ 2 := by ring
    rw [this]; nlinarith [pow_le_one₀ hε.le hε1 (n := 2)]
  have e4 : ε ^ 4 * a2 ≤ ε ^ 3 * a2 := by gcongr
  have e5 : ν * (3 * ε ^ 5 * a3) ≤ ν * (3 * ε ^ 3 * a3) := by gcongr
  have p1 := mul_nonneg hε3.le ha1n
  have p2 := mul_nonneg hε3.le ha2n
  have p3 := mul_nonneg hν (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hε3.le) ha3n)
  have p4 := mul_nonneg hε3.le (mul_nonneg hrn ha2n)
  have goal : 100 * ε ^ 3 * (a1 + (1 + r) * a2 + ν * a3) =
      100 * (ε ^ 3 * a1) + 100 * (ε ^ 3 * a2) + 100 * (ε ^ 3 * (r * a2)) +
        100 * (ν * (ε ^ 3 * a3)) := by ring
  rw [goal]
  have e5' : ν * (3 * ε ^ 3 * a3) = 3 * (ν * (ε ^ 3 * a3)) := by ring
  nlinarith [dY, hY, sP, sP2, e4, e5, e5', p1, p2, p3, p4]

end UnforcedLeray.Short.PartIIIb.Concrete
