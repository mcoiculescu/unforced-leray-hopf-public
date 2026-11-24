import UnforcedLeray.Units.B0224.Operators

/-!
# B0224 helper: the semigroup law `T_0(t + t') = T_0(t) T_0(t')`

Blueprint unit B0224 (label `eq:st18-t00117`), `paper/main.tex` lines 3370–3379 ("the limiting
semigroup"); proof outline: "the semigroup law follows from the heat semigroup law and
`s(1 - e^{-t}) + s e^{-t}(1 - e^{-t'}) = s(1 - e^{-(t+t')})`".

* the cylinder heat of a periodic field is periodic (`isPeriodic_planeHeat`);
* the planar heat semigroup law at a point (INF04 T3, `Heat.heatConv_add_time_of_lt_top`) gives
  `H_α H_β = H_{α+β}` on `H` for nonnegative heat times (`heatH_comp_heatH`);
* `D_a D_b = D_{ba}` (`dilH_comp_dilH`), and `D_a H_β = H_{β(a ·)} D_a` (`dilH_comp_heatH`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.B0224

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0220

variable {c : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The cylinder heat of a periodic field is periodic. -/
theorem isPeriodic_planeHeat {θ : ℝ} {u : ℝ × ℝ → E} (hu : Cyl.IsPeriodic c u) :
    Cyl.IsPeriodic c (planeHeat θ u) := by
  intro z
  by_cases h : 0 < θ
  · rw [planeHeat_of_pos h, planeHeat_of_pos h]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have h1 := isPeriodic_comp_sub hu (planeι y) z
    simp only at h1
    simp only [h1]
  · rw [planeHeat_of_nonpos (not_lt.1 h)]
    exact hu z

theorem planeHeat_reduceIoc {θ : ℝ} {u : ℝ × ℝ → E} (hu : Cyl.IsPeriodic c u) (z : ℝ × ℝ) :
    planeHeat θ u (reduceIoc c z.1, z.2) = planeHeat θ u z := by
  have hper : Function.Periodic (fun q => planeHeat θ u (q, z.2)) c :=
    fun q => isPeriodic_planeHeat hu (q, z.2)
  rw [reduceIoc_eq_sub]
  exact hper.sub_int_mul_eq _

/-- The fibre of `H_β F`, extended periodically, is the heat of the fibre of `F`. -/
theorem periodize_fiberHeat (hc : 0 < c) (β : ℝ → ℝ) (F : Profile → E) (s : ℝ) (z : ℝ × ℝ) :
    periodize c (fiberHeat c β F) (s, z) =
      planeHeat (β s) (fun w => periodize c F (s, w)) z := by
  simp only [periodize, fiberHeat]
  exact planeHeat_reduceIoc (isPeriodic_periodize_slice hc F s) z

/-- The planar heat semigroup law `e^{aΔ}e^{bΔ}u = e^{(a+b)Δ}u` at a point, `a, b ≥ 0`. -/
theorem planeHeat_planeHeat {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (u : ℝ × ℝ → E) (x : ℝ × ℝ)
    (hm : AEStronglyMeasurable (fun y : Euc 2 => u (x - planeι y)))
    (hx : 0 < a → 0 < b → Heat.heatAbs planeι (a + b) u x < ∞) :
    planeHeat a (planeHeat b u) x = planeHeat (a + b) u x := by
  rcases ha.eq_or_lt with ha0 | ha0
  · subst ha0
    rw [planeHeat_of_nonpos le_rfl, zero_add]
  rcases hb.eq_or_lt with hb0 | hb0
  · subst hb0
    rw [planeHeat_of_nonpos le_rfl, add_zero]
  have hb' : planeHeat b u = Heat.heatConv planeι b u := by
    simp only [planeHeat, hb0, ↓reduceIte]
  rw [hb', planeHeat, if_pos ha0, planeHeat, if_pos (add_pos ha0 hb0)]
  exact (Heat.heatConv_add_time_of_lt_top planeι ha0 hb0 hm (hx ha0 hb0)).symm

theorem heatAbs_lt_top {θ : ℝ} (hθ : 0 < θ) {u : ℝ × ℝ → E} {x : ℝ × ℝ}
    (hfin : ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ‖u (x - planeι y)‖ₑ ^ 2 < ∞) :
    Heat.heatAbs planeι θ u x < ∞ := by
  unfold Heat.heatAbs
  have hle : ∫⁻ y : Euc 2, ‖gaussKernel 2 θ y‖ₑ * ‖u (x - planeι y)‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal (gaussKernel 2 θ y) * (1 + ‖u (x - planeι y)‖ₑ ^ 2) := by
    refine lintegral_mono fun y => ?_
    rw [Real.enorm_of_nonneg (Gaussian.gaussKernel_nonneg hθ y)]
    gcongr
    exact le_one_add_sq _
  refine lt_of_le_of_lt hle ?_
  simp_rw [mul_add, mul_one]
  rw [lintegral_add_left (measurable_ofReal_gauss θ), lintegral_ofReal_gauss hθ]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hfin⟩

/-- **The heat semigroup law on `H`**: `H_α H_β = H_{α+β}` for heat times `α, β ≥ 0` on
`s > 0`. -/
theorem heatH_comp_heatH (hc : 0 < c) {α β : ℝ → ℝ} (hα : Measurable α) (hβ : Measurable β)
    (hα0 : ∀ s, 0 < s → 0 ≤ α s) (hβ0 : ∀ s, 0 < s → 0 ≤ β s) :
    (heatH hc hα : HSpace c E →L[ℝ] HSpace c E) ∘L heatH hc hβ = heatH hc (hα.add hβ) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  have hf := Lp.stronglyMeasurable f
  have h1 : (heatH hc hα (heatH hc hβ f) : Profile → E) =ᵐ[measureH c]
      fiberHeat c α (heatH hc hβ f : Profile → E) := coeFn_heatH hc hα _
  have h2 : fiberHeat c α (heatH hc hβ f : Profile → E) =ᵐ[measureH c]
      fiberHeat c α (fiberHeat c β (f : Profile → E)) :=
    fiberHeat_congr_ae hc hα (Lp.stronglyMeasurable _) (stronglyMeasurable_fiberHeat hβ hf)
      (coeFn_heatH hc hβ f)
  have h4 : (heatH hc (hα.add hβ) f : Profile → E) =ᵐ[measureH c]
      fiberHeat c (α + β) (f : Profile → E) := coeFn_heatH hc _ f
  have hfin : ∀ᵐ p ∂measureH c, fiberAbs c (α + β) (fun p => ‖f p‖ₑ ^ 2) p < ∞ := by
    refine ae_lt_top (measurable_fiberAbs (hα.add hβ) (hf.enorm.pow_const 2)) ?_
    rw [lintegral_measureH_fiberAbs hc (hα.add hβ) (hf.enorm.pow_const 2)]
    exact (lintegral_sq_lt_top f).ne
  rw [ContinuousLinearMap.comp_apply]
  refine h1.trans (h2.trans (EventuallyEq.trans ?_ h4.symm))
  filter_upwards [ae_cell_measureH c, hfin] with p hp hpfin
  have hs : 0 < p.1 := hp.1
  have e1 : fiberHeat c α (fiberHeat c β (f : Profile → E)) p =
      planeHeat (α p.1) (planeHeat (β p.1) fun w => periodize c (f : Profile → E) (p.1, w)) p.2 := by
    simp only [fiberHeat]
    congr 1
    funext z
    exact periodize_fiberHeat hc β _ p.1 z
  rw [e1]
  have e2 : fiberHeat c (α + β) (f : Profile → E) p =
      planeHeat (α p.1 + β p.1) (fun w => periodize c (f : Profile → E) (p.1, w)) p.2 := rfl
  rw [e2]
  refine planeHeat_planeHeat (hα0 _ hs) (hβ0 _ hs) _ _ ?_ ?_
  · exact ((stronglyMeasurable_periodize hf).comp_measurable
      (measurable_const.prodMk (measurable_const.sub measurable_planeι))).aestronglyMeasurable
  · intro ha hb
    have hpos : 0 < (α + β) p.1 := add_pos ha hb
    simp only [fiberAbs, hpos, ↓reduceIte] at hpfin
    exact heatAbs_lt_top (add_pos ha hb) hpfin

/-- `D_a D_b = D_{ba}`. -/
theorem dilH_comp_dilH {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (dilH ha : HSpace c E →L[ℝ] HSpace c E) ∘L dilH hb = dilH (mul_pos hb ha) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  have hf := Lp.stronglyMeasurable f
  have h1 : (dilH ha (dilH hb f) : Profile → E) =ᵐ[measureH c]
      dil a (dilH hb f : Profile → E) := coeFn_dilH ha _
  have h2 : dil a (dilH hb f : Profile → E) =ᵐ[measureH c] dil a (dil b (f : Profile → E)) :=
    dil_congr_ae ha (Lp.stronglyMeasurable _) (stronglyMeasurable_dil b hf) (coeFn_dilH hb f)
  have h3 : (dilH (mul_pos hb ha) f : Profile → E) =ᵐ[measureH c] dil (b * a) (f : Profile → E) :=
    coeFn_dilH _ f
  rw [ContinuousLinearMap.comp_apply]
  refine h1.trans (h2.trans (EventuallyEq.trans (Eventually.of_forall fun p => ?_) h3.symm))
  show (f : Profile → E) (b * (a * p.1), p.2) = (f : Profile → E) (b * a * p.1, p.2)
  rw [mul_assoc]

theorem heatTime_nonneg {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) {s : ℝ} (hs : 0 < s) :
    0 ≤ heatTime ν t s := by
  unfold heatTime
  have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have := mul_nonneg (mul_nonneg hν hs.le) (sub_nonneg.2 this)
  exact this

theorem T0_eq (hc : 0 < c) (ν t : ℝ) :
    (T0 hc ν t : HSpace c E →L[ℝ] HSpace c E) =
      heatH hc (measurable_heatTime ν t) ∘L dilH (Real.exp_pos (-t)) := rfl

theorem heatTime_add (ν t t' : ℝ) :
    (fun s => heatTime ν t s + heatTime ν t' (Real.exp (-t) * s)) = heatTime ν (t + t') := by
  funext s
  simp only [heatTime]
  rw [neg_add, Real.exp_add]
  ring

theorem exp_neg_mul_exp_neg (t t' : ℝ) :
    Real.exp (-t') * Real.exp (-t) = Real.exp (-(t + t')) := by
  rw [← Real.exp_add, neg_add, add_comm]

theorem T0_add_aux1 (hc : 0 < c) {ν t t' : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (hθ' : Measurable fun s => heatTime ν t' (Real.exp (-t) * s)) :
    (heatH hc ((measurable_heatTime ν t).add hθ') : HSpace c E →L[ℝ] HSpace c E) ∘L
        dilH (mul_pos (Real.exp_pos (-t')) (Real.exp_pos (-t))) =
      (heatH hc (measurable_heatTime ν t) ∘L heatH hc hθ') ∘L
        (dilH (Real.exp_pos (-t)) ∘L dilH (Real.exp_pos (-t'))) := by
  rw [heatH_comp_heatH hc (measurable_heatTime ν t) hθ'
    (fun s hs => heatTime_nonneg hν ht hs)
    (fun s hs => heatTime_nonneg hν ht' (mul_pos (Real.exp_pos _) hs)),
    dilH_comp_dilH (Real.exp_pos (-t)) (Real.exp_pos (-t'))]

theorem T0_add_aux2 (hc : 0 < c) {ν t t' : ℝ}
    (hθ' : Measurable fun s => heatTime ν t' (Real.exp (-t) * s)) :
    (heatH hc (measurable_heatTime ν t) ∘L heatH hc hθ' : HSpace c E →L[ℝ] HSpace c E) ∘L
        (dilH (Real.exp_pos (-t)) ∘L dilH (Real.exp_pos (-t'))) =
      T0 hc ν t ∘L T0 hc ν t' := by
  refine ContinuousLinearMap.ext fun f => ?_
  have h := congrArg (fun A : HSpace c E →L[ℝ] HSpace c E => A (dilH (Real.exp_pos (-t')) f))
    (dilH_comp_heatH (E := E) hc (measurable_heatTime ν t') (Real.exp_pos (-t)) hθ')
  simp only [ContinuousLinearMap.comp_apply] at h
  have e1 : (T0 hc ν t ∘L T0 hc ν t') f = heatH hc (measurable_heatTime ν t)
      (dilH (Real.exp_pos (-t)) (heatH hc (measurable_heatTime ν t')
        (dilH (Real.exp_pos (-t')) f))) := rfl
  rw [e1, h]
  rfl

theorem T0_add_aux (hc : 0 < c) {ν t t' : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (hθ' : Measurable fun s => heatTime ν t' (Real.exp (-t) * s)) :
    (heatH hc ((measurable_heatTime ν t).add hθ') : HSpace c E →L[ℝ] HSpace c E) ∘L
        dilH (mul_pos (Real.exp_pos (-t')) (Real.exp_pos (-t))) =
      T0 hc ν t ∘L T0 hc ν t' :=
  (T0_add_aux1 hc hν ht ht' hθ').trans (T0_add_aux2 hc hθ')

/-- **The semigroup law** `T_0(t + t') = T_0(t) T_0(t')` for `t, t' ≥ 0`, `ν ≥ 0`. -/
theorem T0_add (hc : 0 < c) {ν t t' : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    (T0 hc ν (t + t') : HSpace c E →L[ℝ] HSpace c E) = T0 hc ν t ∘L T0 hc ν t' := by
  have hθ' : Measurable fun s => heatTime ν t' (Real.exp (-t) * s) :=
    (measurable_heatTime ν t').comp (measurable_id.const_mul _)
  rw [← T0_add_aux hc hν ht ht' hθ', T0_eq,
    heatH_congr hc (heatTime_add ν t t').symm (measurable_heatTime ν (t + t'))
      ((measurable_heatTime ν t).add hθ'),
    dilH_congr (exp_neg_mul_exp_neg t t').symm (Real.exp_pos (-(t + t')))
      (mul_pos (Real.exp_pos (-t')) (Real.exp_pos (-t)))]

end UnforcedLeray.B0224
