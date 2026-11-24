import UnforcedLeray.Short.PartIIb.Sub.T15

/-!
# Part II-b, task `PartII-b:T15/3`: the weak `q`-decomposition (proof)

Source of record: `the November 2 reference manuscript`, lines 1960-1966
(`∂_q = Q_ε + ε L_1`, `L_1 = 2S + η∂_η + 1`) and lines 1617-1653 (`Q_ε = ∂_q - ε(K+1)`,
`K = 2S + η∂_η`).

Proves `WeakQDecomposition` (`Sub/T15.lean`) with no extra hypotheses.

Strategy. For a smooth test `φ` in `{s > 0}`, the transposes of the four chart fields satisfy the
pointwise identity `ε φ = -Q_ε^T φ + ∂_q^T φ - 2ε S^T φ - ε (η∂_η)^T φ`, where the last term is
applied to the test `η φ`. Multiplying by `b` and using the four weak equations turns
`∫ (Db - (Qb + ε(2Sb + ηEb + b))) φ` into zero for all tests. The fundamental lemma on the open
set `{s > 0}` then gives a.e. vanishing for Lebesgue measure there, and `hMeas c 2 = ageμ c _` is
absolutely continuous with respect to Lebesgue measure and carried by `{s > 0}`.

Every auxiliary declaration is prefixed `qd_` to avoid clashes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ### Calculus of `cpd` (directional derivative along `cdir j`) -/

theorem qd_cpd_mul (j : Fin 3) {f g : Coord → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : Coord) :
    cpd j (fun y => f y * g y) x = f x * cpd j g x + g x * cpd j f x := by
  unfold cpd
  rw [fderiv_fun_mul (hf x) (hg x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem qd_cpd_const_mul (j : Fin 3) (k : ℝ) {f : Coord → ℝ} (hf : Differentiable ℝ f)
    (x : Coord) : cpd j (fun y => k * f y) x = k * cpd j f x := by
  unfold cpd
  rw [fderiv_const_mul (hf x) k]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem qd_cpd_fst (j : Fin 3) (x : Coord) : cpd j (fun y : Coord => y.1) x = (cdir j).1 := by
  unfold cpd
  have h : (fun y : Coord => y.1) = ⇑(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) := rfl
  rw [h, ContinuousLinearMap.fderiv]
  rfl

theorem qd_cpd_snd (j : Fin 3) (x : Coord) :
    cpd j (fun y : Coord => y.2.2) x = (cdir j).2.2 := by
  unfold cpd
  have h : (fun y : Coord => y.2.2) =
      ⇑((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) := rfl
  rw [h, ContinuousLinearMap.fderiv]
  rfl

theorem qd_cpd_const (j : Fin 3) (k : ℝ) (x : Coord) : cpd j (fun _ : Coord => k) x = 0 := by
  unfold cpd
  simp

theorem qd_cpd_fst_mul (ψ : Coord → ℝ) (hψ : Differentiable ℝ ψ) (x : Coord) :
    cpd 0 (fun y : Coord => y.1 * ψ y) x = ψ x + x.1 * cpd 0 ψ x := by
  have hf : Differentiable ℝ (fun y : Coord => y.1) := by fun_prop
  have h0 : (cdir 0).1 = 1 := rfl
  rw [qd_cpd_mul 0 hf hψ x, qd_cpd_fst, h0]
  ring

theorem qd_cpd_snd_mul (ψ : Coord → ℝ) (hψ : Differentiable ℝ ψ) (x : Coord) :
    cpd 2 (fun y : Coord => y.2.2 * ψ y) x = ψ x + x.2.2 * cpd 2 ψ x := by
  have hf : Differentiable ℝ (fun y : Coord => y.2.2) := by fun_prop
  have h2 : (cdir 2).2.2 = 1 := rfl
  rw [qd_cpd_mul 2 hf hψ x, qd_cpd_snd, h2]
  ring

/-! ### Transposes of the chart fields on a test function -/

theorem qd_coordT_eq (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (ψ : Coord → ℝ) (x : Coord) :
    coordTranspose v d ψ x = -(cpd 0 (fun y => v y 0 * ψ y) x + cpd 1 (fun y => v y 1 * ψ y) x
      + cpd 2 (fun y => v y 2 * ψ y) x) + d x * ψ x := by
  unfold coordTranspose
  rw [Fin.sum_univ_three]

theorem qd_T_Q0 (ψ : Coord → ℝ) (x : Coord) :
    coordTranspose vQ0 dZero ψ x = -cpd 1 ψ x := by
  have h0 : cpd 0 (fun y : Coord => vQ0 y 0 * ψ y) x = 0 := by
    have e : (fun y : Coord => vQ0 y 0 * ψ y) = fun _ => (0 : ℝ) := by
      funext y
      rw [show vQ0 y 0 = 0 from rfl, zero_mul]
    rw [e, qd_cpd_const]
  have h1 : cpd 1 (fun y : Coord => vQ0 y 1 * ψ y) x = cpd 1 ψ x := by
    have e : (fun y : Coord => vQ0 y 1 * ψ y) = ψ := by
      funext y
      rw [show vQ0 y 1 = 1 from rfl, one_mul]
    rw [e]
  have h2 : cpd 2 (fun y : Coord => vQ0 y 2 * ψ y) x = 0 := by
    have e : (fun y : Coord => vQ0 y 2 * ψ y) = fun _ => (0 : ℝ) := by
      funext y
      rw [show vQ0 y 2 = 0 from rfl, zero_mul]
    rw [e, qd_cpd_const]
  rw [qd_coordT_eq, h0, h1, h2, show dZero x = 0 from rfl]
  ring

theorem qd_T_E (ψ : Coord → ℝ) (x : Coord) :
    coordTranspose vEta dZero ψ x = -cpd 2 ψ x := by
  have h0 : cpd 0 (fun y : Coord => vEta y 0 * ψ y) x = 0 := by
    have e : (fun y : Coord => vEta y 0 * ψ y) = fun _ => (0 : ℝ) := by
      funext y
      rw [show vEta y 0 = 0 from rfl, zero_mul]
    rw [e, qd_cpd_const]
  have h1 : cpd 1 (fun y : Coord => vEta y 1 * ψ y) x = 0 := by
    have e : (fun y : Coord => vEta y 1 * ψ y) = fun _ => (0 : ℝ) := by
      funext y
      rw [show vEta y 1 = 0 from rfl, zero_mul]
    rw [e, qd_cpd_const]
  have h2 : cpd 2 (fun y : Coord => vEta y 2 * ψ y) x = cpd 2 ψ x := by
    have e : (fun y : Coord => vEta y 2 * ψ y) = ψ := by
      funext y
      rw [show vEta y 2 = 1 from rfl, one_mul]
    rw [e]
  rw [qd_coordT_eq, h0, h1, h2, show dZero x = 0 from rfl]
  ring

theorem qd_T_S (ψ : Coord → ℝ) (hψ : Differentiable ℝ ψ) (x : Coord) :
    coordTranspose vS dZero ψ x = -(ψ x + x.1 * cpd 0 ψ x) := by
  have h0 : cpd 0 (fun y : Coord => vS y 0 * ψ y) x = ψ x + x.1 * cpd 0 ψ x := by
    have e : (fun y : Coord => vS y 0 * ψ y) = fun y => y.1 * ψ y := by
      funext y
      rw [show vS y 0 = y.1 from rfl]
    rw [e, qd_cpd_fst_mul ψ hψ x]
  have h1 : cpd 1 (fun y : Coord => vS y 1 * ψ y) x = 0 := by
    have e : (fun y : Coord => vS y 1 * ψ y) = fun _ => (0 : ℝ) := by
      funext y
      rw [show vS y 1 = 0 from rfl, zero_mul]
    rw [e, qd_cpd_const]
  have h2 : cpd 2 (fun y : Coord => vS y 2 * ψ y) x = 0 := by
    have e : (fun y : Coord => vS y 2 * ψ y) = fun _ => (0 : ℝ) := by
      funext y
      rw [show vS y 2 = 0 from rfl, zero_mul]
    rw [e, qd_cpd_const]
  rw [qd_coordT_eq, h0, h1, h2, show dZero x = 0 from rfl]
  ring

theorem qd_T_Q (ε : ℝ) (φ : Coord → ℝ) (hφ : Differentiable ℝ φ) (x : Coord) :
    coordTranspose (vQ ε) (dQ ε) φ x = -cpd 1 φ x + 2 * ε * φ x + 2 * ε * (x.1 * cpd 0 φ x)
      + ε * (x.2.2 * cpd 2 φ x) := by
  have h0 : cpd 0 (fun y : Coord => vQ ε y 0 * φ y) x = -2 * ε * (φ x + x.1 * cpd 0 φ x) := by
    have e : (fun y : Coord => vQ ε y 0 * φ y) = fun y => (-2 * ε) * (y.1 * φ y) := by
      funext y
      rw [show vQ ε y 0 = -2 * ε * y.1 from rfl]
      ring
    rw [e, qd_cpd_const_mul 0 (-2 * ε) (f := fun y : Coord => y.1 * φ y) (by fun_prop),
      qd_cpd_fst_mul φ hφ]
  have h1 : cpd 1 (fun y : Coord => vQ ε y 1 * φ y) x = cpd 1 φ x := by
    have e : (fun y : Coord => vQ ε y 1 * φ y) = φ := by
      funext y
      rw [show vQ ε y 1 = 1 from rfl, one_mul]
    rw [e]
  have h2 : cpd 2 (fun y : Coord => vQ ε y 2 * φ y) x = -ε * (φ x + x.2.2 * cpd 2 φ x) := by
    have e : (fun y : Coord => vQ ε y 2 * φ y) = fun y => (-ε) * (y.2.2 * φ y) := by
      funext y
      rw [show vQ ε y 2 = -ε * y.2.2 from rfl]
      ring
    rw [e, qd_cpd_const_mul 2 (-ε) (f := fun y : Coord => y.2.2 * φ y) (by fun_prop),
      qd_cpd_snd_mul φ hφ]
  rw [qd_coordT_eq, h0, h1, h2, show dQ ε x = -ε from rfl]
  ring

/-- The pointwise identity behind the decomposition: `ε φ = -Q_ε^T φ + ∂_q^T φ - 2ε S^T φ - ε (η∂_η)^T(ηφ)`
with `∂_q^T φ = -cpd 1 φ`, `(η∂_η)^T` applied to the test `ηφ` (`qd_T_E`). -/
theorem qd_real (ε : ℝ) (φ : Coord → ℝ) (hφ : Differentiable ℝ φ) (x : Coord) :
    ε * φ x = -(coordTranspose (vQ ε) (dQ ε) φ x) + coordTranspose vQ0 dZero φ x
      - 2 * ε * coordTranspose vS dZero φ x
      - ε * coordTranspose vEta dZero (fun y => y.2.2 * φ y) x := by
  rw [qd_T_Q ε φ hφ, qd_T_Q0, qd_T_S φ hφ, qd_T_E, qd_cpd_snd_mul φ hφ]
  ring

/-- The test function `η φ` is again a coordinate test function. -/
theorem qd_test_mul_snd {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsCoordTest (fun x : Coord => x.2.2 * φ x) where
  smooth := (contDiff_snd.comp contDiff_snd).mul hφ.smooth
  compact := hφ.compact.mul_left (f := fun x : Coord => x.2.2)
  supp := tsupport_mul_subset_right.trans hφ.supp

/-! ### The measure `hMeas` is carried by `{s > 0}` and is absolutely continuous -/

theorem qd_ageμ_ac (c a : ℝ) : Axi.ageμ c a ≪ (volume : Measure Coord) := by
  rw [Axi.ageμ, Measure.volume_eq_prod]
  refine Measure.AbsolutelyContinuous.prod ?_ ?_
  · exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  · unfold Cyl.avgμ
    exact (Measure.smul_absolutelyContinuous).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- A weak identity against all coordinate tests, for a function `G` on `{s > 0}`, gives an
almost-everywhere identity for `ageμ c a`. -/
theorem qd_ae_zero (c a : ℝ) (hc : 0 < c) (G : Coord → ℂ)
    (hint : ∀ φ : Coord → ℝ, IsCoordTest φ →
      Integrable (fun x => G x * (φ x : ℂ)) ∧ ∫ x, G x * (φ x : ℂ) = 0) :
    ∀ᵐ x ∂(Axi.ageμ c a), G x = 0 := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hloc : LocallyIntegrableOn G (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
    let f : ContDiffBump x :=
      { rIn := r / 4, rOut := r / 2, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
    have hf : IsCoordTest (⇑f) :=
      { smooth := f.contDiff
        compact := f.hasCompactSupport
        supp := by
          rw [f.tsupport_eq]
          exact (Metric.closedBall_subset_ball (show f.rOut < r by
            show r / 2 < r; linarith)).trans hball }
    refine ⟨Metric.ball x (r / 4), mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds x (by linarith)), ?_⟩
    refine IntegrableOn.congr_fun (hint (⇑f) hf).1.integrableOn ?_ Metric.isOpen_ball.measurableSet
    intro y hy
    have hy1 : f y = 1 := f.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp only [hy1, Complex.ofReal_one, mul_one]
  have hzero : ∀ g : Coord → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) → ∫ x, g x • G x = 0 := by
    intro g hg hgc hgs
    have e : (fun x => g x • G x) = fun x => G x * ((g x : ℝ) : ℂ) := by
      funext x
      rw [Complex.real_smul, mul_comm]
    rw [e]
    exact (hint g ⟨hg, hgc, hgs⟩).2
  have hfund := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hzero
  have h2 := (qd_ageμ_ac c a).ae_le hfund
  filter_upwards [h2, Axi.ae_ageμ_mem hc a] with x hx1 hx2
  exact hx1 ⟨hx2.1, mem_univ _⟩

/-! ### The scalar identity against one test function -/

theorem qd_scalar (ε : ℝ) (u Du Qu Su Eu : Coord → ℂ)
    (hD : HasWeakFO vQ0 dZero u Du) (hQ : HasWeakFO (vQ ε) (dQ ε) u Qu)
    (hS : HasWeakFO vS dZero u Su) (hE : HasWeakFO vEta dZero u Eu)
    (φ : Coord → ℝ) (hφ : IsCoordTest φ) :
    Integrable (fun x => (Du x - (Qu x + (ε : ℂ) * (2 * Su x + (x.2.2 : ℂ) * Eu x + u x)))
        * (φ x : ℂ)) ∧
      ∫ x, (Du x - (Qu x + (ε : ℂ) * (2 * Su x + (x.2.2 : ℂ) * Eu x + u x))) * (φ x : ℂ) = 0 := by
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hη := qd_test_mul_snd hφ
  have hI0 := (hD.1 φ hφ).1
  have hIQ := (hQ.1 φ hφ).1
  have hIS := (hS.1 φ hφ).1
  have hIE := (hE.1 _ hη).1
  have hF1 := (hD.1 φ hφ).2
  have hF2 := (hQ.1 φ hφ).2
  have hF3 := (hS.1 φ hφ).2
  have hF4 := (hE.1 _ hη).2
  have eD := hD.2 φ hφ
  have eQ := hQ.2 φ hφ
  have eS := hS.2 φ hφ
  have eE := hE.2 _ hη
  have i1 : Integrable (fun x => Du x * (φ x : ℂ)
      - u x * ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ)) := hF1.sub hI0
  have i2 : Integrable (fun x => Qu x * (φ x : ℂ)
      - u x * ((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ)) := hF2.sub hIQ
  have i3 : Integrable (fun x => Su x * (φ x : ℂ)
      - u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ)) := hF3.sub hIS
  have i4 : Integrable (fun x => Eu x * ((x.2.2 * φ x : ℝ) : ℂ)
      - u x * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ)) := hF4.sub hIE
  have z1 : ∫ x, (Du x * (φ x : ℂ) - u x * ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ)) = 0 := by
    rw [integral_sub hF1 hI0, eD, sub_self]
  have z2 : ∫ x, (Qu x * (φ x : ℂ)
      - u x * ((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ)) = 0 := by
    rw [integral_sub hF2 hIQ, eQ, sub_self]
  have z3 : ∫ x, (Su x * (φ x : ℂ) - u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ)) = 0 := by
    rw [integral_sub hF3 hIS, eS, sub_self]
  have z4 : ∫ x, (Eu x * ((x.2.2 * φ x : ℝ) : ℂ)
      - u x * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ)) = 0 := by
    rw [integral_sub hF4 hIE, eE, sub_self]
  have hpt : ∀ x : Coord,
      (Du x - (Qu x + (ε : ℂ) * (2 * Su x + (x.2.2 : ℂ) * Eu x + u x))) * (φ x : ℂ)
        = ((Du x * (φ x : ℂ) - u x * ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ))
            - (Qu x * (φ x : ℂ) - u x * ((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ)))
          - 2 * (ε : ℂ) * (Su x * (φ x : ℂ) - u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ))
          - (ε : ℂ) * (Eu x * ((x.2.2 * φ x : ℝ) : ℂ)
              - u x * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ)) := by
    intro x
    have Rc : (ε : ℂ) * (φ x : ℂ) = -((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ)
        + ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ)
        - 2 * (ε : ℂ) * ((coordTranspose vS dZero φ x : ℝ) : ℂ)
        - (ε : ℂ) * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ) := by
      exact_mod_cast qd_real ε φ hφd x
    push_cast
    linear_combination (-u x) * Rc
  have hint_int : Integrable (fun x => (Du x - (Qu x + (ε : ℂ) * (2 * Su x
      + (x.2.2 : ℂ) * Eu x + u x))) * (φ x : ℂ)) :=
    (((i1.sub i2).sub (i3.const_mul (2 * (ε : ℂ)))).sub (i4.const_mul (ε : ℂ))).congr
      (ae_of_all _ fun x => (hpt x).symm)
  refine ⟨hint_int, ?_⟩
  have i12 : Integrable (fun x => (Du x * (φ x : ℂ)
      - u x * ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ))
      - (Qu x * (φ x : ℂ) - u x * ((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ))) :=
    i1.sub i2
  have i123 : Integrable (fun x => ((Du x * (φ x : ℂ)
      - u x * ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ))
      - (Qu x * (φ x : ℂ) - u x * ((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ)))
      - 2 * (ε : ℂ) * (Su x * (φ x : ℂ) - u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ))) :=
    i12.sub (i3.const_mul (2 * (ε : ℂ)))
  rw [integral_congr_ae (ae_of_all _ hpt)]
  rw [integral_sub i123 (i4.const_mul (ε : ℂ)), integral_sub i12 (i3.const_mul (2 * (ε : ℂ))),
    integral_sub i1 i2, integral_const_mul, integral_const_mul, z1, z2, z3, z4]
  ring

/-! ### The weak `q`-decomposition -/

theorem weakQDecomposition : WeakQDecomposition := by
  intro c ε b Db Qb Sb Eb hc hD hQ hS hE
  have key : ∀ i : Fin 2, ∀ᵐ x ∂(hMeas c 2),
      Db x i = Qb x i + (ε : ℂ) * (2 * Sb x i + (x.2.2 : ℂ) * Eb x i + b x i) := by
    intro i
    unfold hMeas
    have h := qd_ae_zero c (2 / 2 - 5 / 2) hc
      (fun x => Db x i - (Qb x i + (ε : ℂ) * (2 * Sb x i + (x.2.2 : ℂ) * Eb x i + b x i)))
      (fun φ hφ => qd_scalar ε (fun x => b x i) (fun x => Db x i) (fun x => Qb x i)
        (fun x => Sb x i) (fun x => Eb x i) (hD i) (hQ i) (hS i) (hE i) φ hφ)
    filter_upwards [h] with x hx
    exact sub_eq_zero.mp hx
  exact ae_all_iff.2 key

end UnforcedLeray.Short.IIb
