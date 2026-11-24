import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# `farOutMeasurable` (source 3905-3912, 3604-3621)

Joint measurability of the masked dilation integral `farOut` in the chart variable `x`.  The mask
depends on the output age `s = x.1`, so the parametric integrand is `PsiMs` (the `PsiM` of
`T8_1` with the output age as an extra parameter); the `z`- and `l`-integrals are measurable by
`StronglyMeasurable.integral_prod_right'`, as in `T8_1.measurable_sepW_comp`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.Concrete.T8_1

/-- The masked `z`-integrand of `farOut`, at `p = ((s, (τ, y)), l)`. -/
def PsiMs (ν : ℝ) (i : Fin 3) (R δ : ℝ) (cf : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (p : (ℝ × ℝ × Space) × ℝ) (z : Space) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3,
    ((Gm k i j (ν * (1 - p.2 ^ 2), p.1.2.2 - p.2 • z) : ℝ) : ℂ) *
      ((if Real.exp δ * p.1.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
        then cf (p.1.2.1 + 2 * Real.log p.2) z j k else 0 : ℝ) : ℂ)

lemma sepWfar_eq_PsiMs (ν : ℝ) (μ : ℂ) (R δ : ℝ) (cf : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (i : Fin 3) (q : ℝ × ℝ × Space) :
    NearInst.sepWfar ν μ R δ q.1 (fun τ z => cf τ z) q.2.2 q.2.1 i =
      -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
        ∫ z : Space, PsiMs ν i R δ cf ((q, l)) z := by
  have h := sepW_eq_PsiM ν μ (fun τ' z => if Real.exp δ * q.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
    then cf τ' z else 0) i (q.2.1, q.2.2)
  dsimp only at h
  unfold NearInst.sepWfar
  rw [h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo (fun l _ => ?_)
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [PsiM, PsiMs]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  congr 1
  by_cases hc : Real.exp δ * q.1 < R ^ 2 / (z.ofLp 0 ^ 2 + z.ofLp 1 ^ 2)
  · simp [hc]
  · simp [hc]

lemma measurable_coord_space (i : Fin 3) : Measurable fun z : Space => z i := by
  first
    | exact (PiLp.continuous_apply _ i).measurable
    | fun_prop
    | exact (measurable_pi_apply i).comp WithLp.measurable_ofLp

lemma measurable_PsiMs (ν : ℝ) (i : Fin 3) (R δ : ℝ)
    (cf : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => cf s.1 s.2 j k) :
    Measurable fun p : ((ℝ × ℝ × Space) × ℝ) × Space => PsiMs ν i R δ cf p.1 p.2 := by
  have hs : Measurable fun p : ((ℝ × ℝ × Space) × ℝ) × Space => p.1.1.1 :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hτ : Measurable fun p : ((ℝ × ℝ × Space) × ℝ) × Space => p.1.1.2.1 :=
    measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hy : Measurable fun p : ((ℝ × ℝ × Space) × ℝ) × Space => p.1.1.2.2 :=
    measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hl : Measurable fun p : ((ℝ × ℝ × Space) × ℝ) × Space => p.1.2 :=
    measurable_snd.comp measurable_fst
  have ht : Measurable fun p : ((ℝ × ℝ × Space) × ℝ) × Space => ν * (1 - p.1.2 ^ 2) :=
    measurable_const.mul (measurable_const.sub (hl.pow_const 2))
  have hx : Measurable fun p : ((ℝ × ℝ × Space) × ℝ) × Space => p.1.1.2.2 - p.1.2 • p.2 :=
    hy.sub (hl.smul measurable_snd)
  have hlog : Measurable fun p : ((ℝ × ℝ × Space) × ℝ) × Space =>
      p.1.1.2.1 + 2 * Real.log p.1.2 :=
    hτ.add (measurable_const.mul hl.log)
  unfold PsiMs
  refine Finset.measurable_sum _ (fun j _ => ?_)
  refine Finset.measurable_sum _ (fun k _ => ?_)
  refine Measurable.mul (Complex.measurable_ofReal.comp ?_) (Complex.measurable_ofReal.comp ?_)
  · exact (measurable_Gm k i j).comp (ht.prodMk hx)
  · refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt (measurable_const.mul hs)
        (measurable_const.div ((((measurable_coord_space 0).comp measurable_snd).pow_const 2).add
          (((measurable_coord_space 1).comp measurable_snd).pow_const 2)))
    · exact (hT j k).comp (hlog.prodMk measurable_snd)

lemma measurable_sepWfar_joint (ν : ℝ) (μ : ℂ) (R δ : ℝ) (i : Fin 3)
    (cf : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => cf s.1 s.2 j k) :
    Measurable fun q : ℝ × ℝ × Space =>
      NearInst.sepWfar ν μ R δ q.1 (fun τ z => cf τ z) q.2.2 q.2.1 i := by
  have e : (fun q : ℝ × ℝ × Space =>
      NearInst.sepWfar ν μ R δ q.1 (fun τ z => cf τ z) q.2.2 q.2.1 i) =
      fun q : ℝ × ℝ × Space => -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
        ∫ z : Space, PsiMs ν i R δ cf ((q, l)) z :=
    funext fun q => sepWfar_eq_PsiMs ν μ R δ cf i q
  rw [e]
  have hP := measurable_PsiMs ν i R δ cf hT
  have hI : StronglyMeasurable fun r : (ℝ × ℝ × Space) × ℝ => ∫ z : Space, PsiMs ν i R δ cf r z :=
    StronglyMeasurable.integral_prod_right' (ν := volume)
      (f := fun p : ((ℝ × ℝ × Space) × ℝ) × Space => PsiMs ν i R δ cf p.1 p.2)
      hP.stronglyMeasurable
  have hO : Measurable fun r : (ℝ × ℝ × Space) × ℝ =>
      (r.2 : ℂ) ^ (2 * μ + 2) * ∫ z : Space, PsiMs ν i R δ cf r z :=
    ((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul hI.measurable
  have hOS : StronglyMeasurable fun q : ℝ × ℝ × Space =>
      ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) * ∫ z : Space, PsiMs ν i R δ cf ((q, l)) z :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))
      (f := fun p : (ℝ × ℝ × Space) × ℝ => (p.2 : ℂ) ^ (2 * μ + 2) * ∫ z : Space, PsiMs ν i R δ cf p z)
      hO.stronglyMeasurable
  exact hOS.measurable.const_mul (-2)

lemma measurable_merRe_fn : Measurable fun w : Fin 3 → ℂ => merRe w := by
  unfold merRe
  refine (WithLp.measurable_toLp 2 _).comp ?_
  refine measurable_pi_lambda _ (fun j => ?_)
  fin_cases j
  · exact Complex.measurable_re.comp (measurable_pi_apply 0)
  · exact Complex.measurable_re.comp (measurable_pi_apply 2)

lemma measurable_chartTau_fn (R : ℝ) : Measurable fun p : Chart => NearInst.chartTau R p := by
  unfold NearInst.chartTau
  have h1 : Measurable fun p : Chart => p.2.1 := measurable_fst.comp measurable_snd
  exact ((measurable_const.mul h1).div_const R |>.add (Real.measurable_log.comp measurable_fst))

lemma measurable_chartY_fn (R : ℝ) : Measurable fun p : Chart => NearInst.chartY R p := by
  unfold NearInst.chartY
  refine (WithLp.measurable_toLp 2 _).comp ?_
  refine measurable_pi_lambda _ (fun j => ?_)
  fin_cases j
  · exact measurable_const.div measurable_fst.sqrt
  · exact measurable_const
  · exact (measurable_snd.comp measurable_snd).div measurable_fst.sqrt

lemma measurable_farOut_fn (R c ν μ δ S : ℝ) (f : Chart → Ten3) (hf : Measurable f) :
    Measurable (farOut R c ν μ δ S f) := by
  have hcf : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => NearInst.cartLift R c f s.1 s.2 j k :=
    fun j k => T8_1.measurable_cartLift_entry R c f hf j k
  have hΦ : Measurable fun x : Chart =>
      ((x.1, NearInst.chartTau R x, NearInst.chartY R x) : ℝ × ℝ × Space) :=
    measurable_fst.prodMk ((measurable_chartTau_fn R).prodMk (measurable_chartY_fn R))
  have hW : ∀ i : Fin 3, Measurable fun x : Chart =>
      -NearInst.sepWfar ν (μ : ℂ) R δ x.1 (fun τ z => NearInst.cartLift R c f τ z)
        (NearInst.chartY R x) (NearInst.chartTau R x) i := by
    intro i
    exact ((measurable_sepWfar_joint ν (μ : ℂ) R δ i (NearInst.cartLift R c f) hcf).comp hΦ).neg
  have hWv : Measurable fun x : Chart =>
      (fun i : Fin 3 => -NearInst.sepWfar ν (μ : ℂ) R δ x.1
        (fun τ z => NearInst.cartLift R c f τ z) (NearInst.chartY R x) (NearInst.chartTau R x) i) :=
    measurable_pi_lambda _ hW
  have hR : Measurable fun x : Chart => merRe
      (fun i : Fin 3 => -NearInst.sepWfar ν (μ : ℂ) R δ x.1
        (fun τ z => NearInst.cartLift R c f τ z) (NearInst.chartY R x) (NearInst.chartTau R x) i) :=
    measurable_merRe_fn.comp hWv
  unfold farOut
  refine Measurable.ite (measurableSet_lt measurable_fst measurable_const) ?_ measurable_const
  exact (measurable_fst.sqrt.inv).smul hR

theorem farOutMeasurable : FarOutMeasurable := by
  intro R c ν δ S μ _ _ _ _ _ _ f hf
  exact (measurable_farOut_fn R c ν μ δ S f hf.measurable).aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
