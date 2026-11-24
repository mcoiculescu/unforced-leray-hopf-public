import UnforcedLeray.Lib.EvolutionFamilies.Dyson
import UnforcedLeray.Infra.EvolutionContinuity.Volterra
import UnforcedLeray.Lib.BudgetsGronwall.VariationOfConstants

/-!
# Bridges: drafted Volterra evolutions as evolution families; nested spaces (INF08 T8.1, T8.2)

* `EvolutionFamily.ofForwardEvolution`: a `ForwardEvolution` of the drafted
  `Infra/EvolutionContinuity` (evolution law, strip bounds, joint strong continuity) restricts to
  an `EvolutionFamily` on every `[a,b]`.
* `EvolutionFamily.ofVolterra`: the Volterra evolution of the drafted `Infra/VolterraEvolution`
  (compatible data with `S₀ 0 = 1`; `paper/main.tex`, lines 292-306) is an `EvolutionFamily` on
  every `[a,b]`. This is how T8.1 is a corollary of the audited Volterra draft; the Dyson series
  of `Dyson.lean` is needed separately because a general two-parameter free family `F(t,s)` is
  not of the convolution form `S₀(t-s)`, `S(t-r)` treated there.
* `dyson_compat` (INF08 T8.2; B0657): Dyson evolutions on nested spaces `ι : Y →L X` with
  compatible data are compatible.
* `norm_dyson_le_integral` (INF08 T8.2; B0119, t00098): `‖U(t,s)‖ ≤ M e^{M ∫_s^t κ}` for a
  continuous majorant `‖A(r)‖ ≤ κ(r)`, by the Gronwall inequality
  `UnforcedLeray.Gronwall.le_exp_of_integral_le` of the draft `Lib/BudgetsGronwall`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Evolution

open UnforcedLeray.Infra.EvolutionContinuity UnforcedLeray.Infra.VolterraEvolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

namespace EvolutionFamily

/-- A `ForwardEvolution` (drafted `Infra/EvolutionContinuity/Abstract.lean`) restricted to
`[a,b]`. -/
def ofForwardEvolution (E : ℝ → ℝ → X →L[ℂ] X) (hE : ForwardEvolution E) (a b : ℝ) :
    EvolutionFamily X a b where
  U := E
  U_diag t _ := hE.self_eq t
  U_comp s r t _ hsr hrt _ := hE.comp s r t hsr hrt
  U_cont x := (hE.continuousOn x).comp continuous_swap.continuousOn
    fun p hp => (hp.2.1 : p.1 ≤ p.2)
  U_bdd := by
    obtain ⟨C, hC⟩ := hE.bounded (b - a)
    exact ⟨C, fun s t hs hst ht => hC s t hst (by linarith)⟩

@[simp] theorem ofForwardEvolution_U (E : ℝ → ℝ → X →L[ℂ] X) (hE : ForwardEvolution E)
    (a b : ℝ) : (ofForwardEvolution E hE a b).U = E := rfl

/-- **The Volterra evolution as an evolution family** (`paper/main.tex`, lines 292-306): for
compatible `VolterraData` with `S₀ 0 = 1`, the global Volterra evolution restricted to `[a,b]`. -/
def ofVolterra [CompleteSpace X] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (D : VolterraData ℂ X Y) (hD : D.Compatible) (hS₀ : D.S₀ 0 = 1) (a b : ℝ) :
    EvolutionFamily X a b :=
  ofForwardEvolution D.evolution (forwardEvolution_volterra hD hS₀) a b

@[simp] theorem ofVolterra_U [CompleteSpace X] {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] (D : VolterraData ℂ X Y) (hD : D.Compatible) (hS₀ : D.S₀ 0 = 1)
    (a b : ℝ) : (ofVolterra D hD hS₀ a b).U = D.evolution := rfl

end EvolutionFamily

/-- **Nested spaces** (INF08 T8.2 `dyson_compat`; B0657): if `ι : Y →L X` intertwines the free
families and the interactions, `ι ∘ F_Y(t,s) = F_X(t,s) ∘ ι` and `ι ∘ A_Y(r) = A_X(r) ∘ ι`, then
`ι ∘ U_Y(t,s) = U_X(t,s) ∘ ι` for the Dyson evolutions. -/
theorem dyson_compat [CompleteSpace X] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [CompleteSpace Y] {a b : ℝ} (ι : Y →L[ℂ] X) (FY : EvolutionFamily Y a b)
    (AY : BoundedPert Y a b) (FX : EvolutionFamily X a b) (AX : BoundedPert X a b)
    (hF : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ι.comp (FY.U t s) = (FX.U t s).comp ι)
    (hA : ∀ r ∈ Icc a b, ι.comp (AY.A r) = (AX.A r).comp ι) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ι.comp ((dyson FY AY).U t s) = ((dyson FX AX).U t s).comp ι := by
  have hterm : ∀ k s t, a ≤ s → s ≤ t → t ≤ b → ∀ y,
      ι (dysonTerm FY AY k t s y) = dysonTerm FX AX k t s (ι y) := by
    intro k
    induction k with
    | zero =>
      intro s t hs hst ht y
      exact congrArg (fun T : Y →L[ℂ] X => T y) (hF s t hs hst ht)
    | succ k ih =>
      intro s t hs hst ht y
      simp only [dysonTerm_succ]
      rw [← ι.intervalIntegral_comp_comm (FY.intervalIntegrable_integrand AY hs hst ht
        ((continuousOn_dysonTerm_fst FY AY k y hs).mono (Icc_subset_Icc le_rfl ht)))]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hst] at hr
      have h1 : ι (FY.U t r (AY.A r (dysonTerm FY AY k r s y))) =
          FX.U t r (ι (AY.A r (dysonTerm FY AY k r s y))) :=
        congrArg (fun T : Y →L[ℂ] X => T (AY.A r (dysonTerm FY AY k r s y)))
          (hF r t (hs.trans hr.1) hr.2 ht)
      have h2 : ι (AY.A r (dysonTerm FY AY k r s y)) = AX.A r (ι (dysonTerm FY AY k r s y)) :=
        congrArg (fun T : Y →L[ℂ] X => T (dysonTerm FY AY k r s y))
          (hA r ⟨hs.trans hr.1, hr.2.trans ht⟩)
      simp only [h1, h2, ih s r hs hr.1 (hr.2.trans ht) y]
  intro s t hs hst ht
  ext y
  show ι ((dyson FY AY).U t s y) = (dyson FX AX).U t s (ι y)
  exact (ι.hasSum (hasSum_dyson FY AY ⟨hs, hst, ht⟩ y)).unique
    ((hasSum_dyson FX AX ⟨hs, hst, ht⟩ (ι y)).congr_fun fun k => hterm k s t hs hst ht y)

/-- **Exponential bound with an integrated interaction** (INF08 T8.2 `norm_dyson_le_integral`;
`paper/main.tex`, lines 1828-1840, B0119, t00098): if `‖F(t,s)‖ ≤ M` and `‖A(r)‖ ≤ κ(r)` with
`κ` continuous on `[a,b]`, then `‖U(t,s)‖ ≤ M exp(M ∫_s^t κ)`. -/
theorem norm_dyson_le_integral [CompleteSpace X] {a b : ℝ} (F : EvolutionFamily X a b)
    (A : BoundedPert X a b) {M : ℝ} {κ : ℝ → ℝ}
    (hF : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ‖F.U t s‖ ≤ M)
    (hκ : ContinuousOn κ (Icc a b)) (hA : ∀ r ∈ Icc a b, ‖A.A r‖ ≤ κ r) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖(dyson F A).U t s‖ ≤ M * Real.exp (M * ∫ r in s..t, κ r) := by
  intro s t hs hst ht
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF s s hs le_rfl (hst.trans ht))
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (Real.exp_pos _).le) fun x => ?_
  set U := dyson F A with hU
  have hκs : ContinuousOn κ (Icc s t) := hκ.mono (Icc_subset_Icc hs ht)
  have hyc : ContinuousOn (fun τ => ‖U.U τ s x‖) (Icc s t) :=
    continuous_norm.comp_continuousOn ((U.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl ht))
  have hG := UnforcedLeray.Gronwall.le_exp_of_integral_le (y := fun τ => ‖U.U τ s x‖)
    (β := fun r => M * κ r) (A := M * ‖x‖) hyc (continuousOn_const.mul hκs)
    (fun r hr => mul_nonneg hM ((norm_nonneg _).trans (hA r ⟨hs.trans hr.1, hr.2.trans ht⟩)))
    (fun τ hτ => ?_) t ⟨hst, le_rfl⟩
  · rw [intervalIntegral.integral_const_mul] at hG
    calc ‖U.U t s x‖ ≤ M * ‖x‖ * Real.exp (M * ∫ r in s..t, κ r) := hG
      _ = M * Real.exp (M * ∫ r in s..t, κ r) * ‖x‖ := by ring
  · rw [hU, dyson_left F A ⟨hs, hτ.1, hτ.2.trans ht⟩ x, ← hU]
    refine (norm_add_le _ _).trans (add_le_add ((F.U τ s).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right (hF s τ hs hτ.1 (hτ.2.trans ht)) (norm_nonneg _))) ?_)
    refine intervalIntegral.norm_integral_le_of_norm_le hτ.1 (ae_of_all _ fun r hr => ?_)
      ((continuousOn_const.mul hκs).mul hyc |>.mono (Icc_subset_Icc le_rfl hτ.2)
        |>.intervalIntegrable_of_Icc hτ.1)
    calc ‖F.U τ r (A.A r (U.U r s x))‖ ≤ M * (κ r * ‖U.U r s x‖) :=
          ((F.U τ r).le_opNorm _).trans (mul_le_mul (hF r τ (hs.trans hr.1.le) hr.2
            (hτ.2.trans ht)) (((A.A r).le_opNorm _).trans (mul_le_mul_of_nonneg_right
              (hA r ⟨hs.trans hr.1.le, hr.2.trans (hτ.2.trans ht)⟩) (norm_nonneg _)))
            (norm_nonneg _) hM)
      _ = M * κ r * ‖U.U r s x‖ := by ring

end UnforcedLeray.Evolution
