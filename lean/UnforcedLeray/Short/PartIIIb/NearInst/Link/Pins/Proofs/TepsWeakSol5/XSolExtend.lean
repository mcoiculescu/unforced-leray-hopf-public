import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellHolder
import UnforcedLeray.Lib.PhaseSpace.Cutoff
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest

/-!
# `XSolExtend` (task `PartIII-b:C/near/pins/3/5/3`)

Source `the November 2 reference manuscript` lines 1339-1362, 1675-1677,
4139-4146: weak solenoidality of `F ∈ X`, tested on phase tests, extends to `H¹`-type tests `χ`
(`χ, ∇χ ∈ L²` over one period) by the spatial cutoffs `χₙ(y) = ψ(y/(n+1))`
(`Lib/PhaseSpace/Cutoff.lean`): `φₙ = χₙ χ` is a phase test, `∇φₙ = χₙ ∇χ + χ ∇χₙ`, the factors
are uniformly bounded and converge pointwise to `1` and `0`, and the pairings
`⟨∇φₙ, F⟩ = 0` converge to `⟨∇χ, F⟩` by dominated convergence on the phase space `ℝ³ × ℝ/Pℤ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0223 (MeridC SpaceC X PSpace volume_pspace)

/-! ### Lifting periodic functions to the phase space -/

section Lift

variable {P : ℝ} [Fact (0 < P)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The phase-space lift `(y, s) ↦ Φ(τ, y)` of a `P`-periodic function (`τ` any lift of `s`). -/
def xlift (Φ : ℝ × Space → E) (hΦ : ∀ τ y, Φ (τ + P, y) = Φ (τ, y)) : PSpace P → E :=
  fun z => (Function.Periodic.lift
    (f := fun τ : ℝ => fun y : Space => Φ (τ, y)) (fun τ => funext fun y => hΦ τ y) z.2) z.1

theorem xlift_coe {Φ : ℝ × Space → E} (hΦ : ∀ τ y, Φ (τ + P, y) = Φ (τ, y)) (t : ℝ) (y : Space) :
    xlift Φ hΦ (y, (t : AddCircle P)) = Φ (t, y) := by
  simp only [xlift]
  exact congrFun (Function.Periodic.lift_coe (fun τ => funext fun y => hΦ τ y) t) y

theorem xlift_continuous {Φ : ℝ × Space → E} (hΦ : ∀ τ y, Φ (τ + P, y) = Φ (τ, y))
    (hc : Continuous Φ) : Continuous (xlift Φ hΦ) := by
  have h1 : IsOpenQuotientMap
      (Prod.map (id : Space → Space) (QuotientAddGroup.mk : ℝ → AddCircle P)) :=
    IsOpenQuotientMap.prodMap IsOpenQuotientMap.id QuotientAddGroup.isOpenQuotientMap_mk
  have h2 : IsOpenQuotientMap (Prod.swap : ℝ × Space → Space × ℝ) :=
    (Homeomorph.prodComm ℝ Space).isOpenQuotientMap
  have hq : Topology.IsQuotientMap (fun x : ℝ × Space => ((x.2, (x.1 : AddCircle P)) : PSpace P)) :=
    (h1.comp h2).isQuotientMap
  refine hq.continuous_iff.mpr ?_
  have hcomp : (xlift Φ hΦ) ∘ (fun x : ℝ × Space => ((x.2, (x.1 : AddCircle P)) : PSpace P))
      = Φ := by
    funext x
    exact xlift_coe hΦ x.1 x.2
  rw [hcomp]
  exact hc

theorem xlift_memLp {Φ : ℝ × Space → E} (hΦ : ∀ τ y, Φ (τ + P, y) = Φ (τ, y))
    (hc : Continuous Φ)
    (hint : IntegrableOn (fun x : ℝ × Space => ‖Φ x‖ ^ 2) (Ioc (0 : ℝ) P ×ˢ univ)) :
    MemLp (xlift Φ hΦ) 2 (volume : Measure (PSpace P)) := by
  have hcont := xlift_continuous hΦ hc
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  refine ⟨(hcont.norm.pow 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hm : Measurable (fun z : PSpace P => ‖‖xlift Φ hΦ z‖ ^ 2‖ₑ) :=
    (hcont.norm.pow 2).measurable.enorm
  rw [volume_pspace, lintegral_prod_symm _ hm.aemeasurable]
  have h := AddCircle.lintegral_preimage P 0
    (fun s : AddCircle P => ∫⁻ y, ‖‖xlift Φ hΦ (y, s)‖ ^ 2‖ₑ)
  simp only [zero_add] at h
  rw [← h]
  have e : ∀ t : ℝ, ∫⁻ y, ‖‖xlift Φ hΦ (y, (t : AddCircle P))‖ ^ 2‖ₑ
      = ∫⁻ y, ‖‖Φ (t, y)‖ ^ 2‖ₑ := fun t => by simp only [xlift_coe]
  simp only [e]
  have h3 := hint.2
  unfold HasFiniteIntegral at h3
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at h3
  have hm2 : Measurable (fun x : ℝ × Space => ‖‖Φ x‖ ^ 2‖ₑ) :=
    (hc.norm.pow 2).measurable.enorm
  rwa [lintegral_prod _ hm2.aemeasurable] at h3

end Lift

/-! ### The pairing as a phase-space integral -/

theorem pairX_eq_xlift {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3}
    (hΦ : ∀ τ y, Φ (τ + P, y) = Φ (τ, y)) (F : X SpaceC P)
    (hint : Integrable (fun z : PSpace P => dotL (xlift Φ hΦ z) ((F : PSpace P → SpaceC) z))
      (volume : Measure (PSpace P))) :
    pairX P Φ F = (P⁻¹ : ℝ) • ∫ z : PSpace P, dotL (xlift Φ hΦ z) ((F : PSpace P → SpaceC) z) := by
  have e1 : (∫ t in Ioc (0 : ℝ) P, (∫ y : Space,
      dotL (Φ (t, y)) ((F : PSpace P → SpaceC) (y, (t : AddCircle P))))) =
      ∫ t in Ioc (0 : ℝ) P, (∫ y : Space,
        dotL (xlift Φ hΦ (y, (t : AddCircle P)))
          ((F : PSpace P → SpaceC) (y, (t : AddCircle P)))) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp only [xlift_coe]
  have e2 : (∫ t in Ioc (0 : ℝ) P, (∫ y : Space,
      dotL (xlift Φ hΦ (y, (t : AddCircle P)))
        ((F : PSpace P → SpaceC) (y, (t : AddCircle P))))) =
      ∫ s : AddCircle P, ∫ y : Space,
        dotL (xlift Φ hΦ (y, s)) ((F : PSpace P → SpaceC) (y, s)) := by
    have h := AddCircle.integral_preimage P 0
      (fun s : AddCircle P => ∫ y : Space,
        dotL (xlift Φ hΦ (y, s)) ((F : PSpace P → SpaceC) (y, s)))
    simpa only [zero_add] using h
  have e3 : ∫ z : PSpace P, dotL (xlift Φ hΦ z) ((F : PSpace P → SpaceC) z)
      = ∫ s : AddCircle P, ∫ y : Space,
        dotL (xlift Φ hΦ (y, s)) ((F : PSpace P → SpaceC) (y, s)) :=
    integral_prod_symm _ hint
  show (P⁻¹ : ℝ) • ∫ t in Ioc (0 : ℝ) P, (∫ y : Space,
      dotL (Φ (t, y)) ((F : PSpace P → SpaceC) (y, (t : AddCircle P)))) =
      (P⁻¹ : ℝ) • ∫ z : PSpace P, dotL (xlift Φ hΦ z) ((F : PSpace P → SpaceC) z)
  rw [e1, e2, e3]

/-! ### The cutoff products -/

/-- The cut-off scalar test `φₙ = χₙ(y) χ(τ, y)`. -/
def cutTest (n : ℕ) (χ : ℝ × Space → ℂ) : ℝ × Space → ℂ :=
  fun x => ((cutχ n x.2 : ℝ) : ℂ) * χ x

theorem dy_cutTest (n : ℕ) (j : Fin 3) {χ : ℝ × Space → ℂ} (hχ : ContDiff ℝ ∞ χ) (p : ℝ × Space) :
    dy j (cutTest n χ) p
      = ((cutχ n p.2 : ℝ) : ℂ) * dy j χ p + ((sd j (cutχ n) p.2 : ℝ) : ℂ) * χ p := by
  have hc : DifferentiableAt ℝ (cutχ n) p.2 :=
    ((contDiff_cutχ n).differentiable (by simp)) p.2
  have h1 : HasFDerivAt (fun x : ℝ × Space => cutχ n x.2)
      ((fderiv ℝ (cutχ n) p.2).comp (ContinuousLinearMap.snd ℝ ℝ Space)) p :=
    hc.hasFDerivAt.comp p hasFDerivAt_snd
  have h2 : HasFDerivAt (fun x : ℝ × Space => ((cutχ n x.2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (cutχ n) p.2).comp (ContinuousLinearMap.snd ℝ ℝ Space)))
      p := Complex.ofRealCLM.hasFDerivAt.comp p h1
  have h3 : HasFDerivAt (fun x : ℝ × Space => ((cutχ n x.2 : ℝ) : ℂ) * χ x) _ p :=
    h2.mul ((hχ.differentiable (by simp)) p).hasFDerivAt
  have h4 : cutTest n χ = fun x : ℝ × Space => ((cutχ n x.2 : ℝ) : ℂ) * χ x := rfl
  show fderiv ℝ (cutTest n χ) p (0, coordinateVector j) = _
  rw [h4, h3.fderiv]
  simp [sd, dy, smul_eq_mul]
  ring

/-- The cutoff gradient: `∇ φₙ = χₙ ∇χ + χ w ₙ`. -/
def wvec (n : ℕ) (y : Space) : CVec3 :=
  ∑ j : Fin 3, ((sd j (cutχ n) y : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)

theorem gradT_cutTest (n : ℕ) {χ : ℝ × Space → ℂ} (hχ : ContDiff ℝ ∞ χ) (p : ℝ × Space) :
    gradT (cutTest n χ) p = ((cutχ n p.2 : ℝ) : ℂ) • gradT χ p + χ p • wvec n p.2 := by
  simp only [gradT, wvec, dy_cutTest n _ hχ, add_smul, Finset.sum_add_distrib, Finset.smul_sum,
    mul_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, smul_smul, mul_comm]

theorem isPhaseTest_cutTest {P : ℝ} (n : ℕ) {χ : ℝ × Space → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hper : ∀ τ y, χ (τ + P, y) = χ (τ, y)) : IsPhaseTest P (cutTest n χ) where
  smooth := by
    have : ContDiff ℝ ∞ (fun x : ℝ × Space => ((cutχ n x.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((contDiff_cutχ n).comp contDiff_snd)
    exact this.mul hχ
  periodic τ y := by simp [cutTest, hper τ y]
  bounded_support := ⟨2 * ((n : ℝ) + 1), fun τ y hy => by
    simp [cutTest, cutχ_eq_zero n hy.le]⟩

theorem norm_cutχ_le (n : ℕ) (y : Space) : ‖((cutχ n y : ℝ) : ℂ)‖ ≤ 1 := by
  have h0 : 0 ≤ cutχ n y := unitBump.nonneg' _
  have h1 : cutχ n y ≤ 1 := unitBump.le_one
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

theorem exists_norm_wvec_le : ∃ B : ℝ, ∀ n y, ‖wvec n y‖ ≤ B := by
  have h : ∀ j : Fin 3, ∃ L : ℝ, ∀ n y, |sd j (cutχ n) y| ≤ L := fun j => by
    obtain ⟨L, hL⟩ := (goodMult_sd_cutχ j 1).bound
    exact ⟨L, fun n y => by simpa using hL n y⟩
  choose L hL using h
  refine ⟨∑ j : Fin 3, L j, fun n y => ?_⟩
  unfold wvec
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, PiLp.norm_single]
  simpa [Complex.norm_real] using hL j n y

/-! ### The cutoff extension -/

theorem xSolExtend : XSolExtend := by
  intro P _ F hF χ hχ
  obtain ⟨hsm, hper, hint⟩ := hχ
  have hgper : ∀ τ y, gradT χ (τ + P, y) = gradT χ (τ, y) := fun τ y =>
    Finset.sum_congr rfl fun j _ => by rw [periodic_dy hper j τ y]
  have hdyc : ∀ j : Fin 3, Continuous (dy j χ) := fun j =>
    (hsm.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgc : Continuous (gradT χ) := by
    unfold gradT
    exact continuous_finset_sum _ fun j _ => (hdyc j).smul continuous_const
  have hint1 : IntegrableOn (fun x : ℝ × Space => ‖χ x‖ ^ 2) (Ioc (0 : ℝ) P ×ˢ univ) :=
    Integrable.mono' hint (hsm.continuous.norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        nlinarith [sq_nonneg ‖gradT χ x‖])
  have hint2 : IntegrableOn (fun x : ℝ × Space => ‖gradT χ x‖ ^ 2) (Ioc (0 : ℝ) P ×ˢ univ) :=
    Integrable.mono' hint (hgc.norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        nlinarith [sq_nonneg ‖χ x‖])
  have hLχ : MemLp (xlift χ hper) 2 (volume : Measure (PSpace P)) :=
    xlift_memLp hper hsm.continuous hint1
  have hLg : MemLp (xlift (gradT χ) hgper) 2 (volume : Measure (PSpace P)) :=
    xlift_memLp hgper hgc hint2
  have hH : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hFm : MemLp (F : PSpace P → SpaceC) 2 (volume : Measure (PSpace P)) := Lp.memLp F
  have hintg : Integrable (fun z : PSpace P =>
      dotL (xlift (gradT χ) hgper z) ((F : PSpace P → SpaceC) z)) (volume : Measure (PSpace P)) :=
    integrable_dotL_of_memLp_holder hLg hFm
  rw [pairX_eq_xlift hgper F hintg]
  obtain ⟨B, hB⟩ := exists_norm_wvec_le
  have hφ : ∀ n : ℕ, IsPhaseTest P (cutTest n χ) := fun n => isPhaseTest_cutTest n hsm hper
  have hΦper : ∀ n : ℕ, ∀ τ y, gradT (cutTest n χ) (τ + P, y) = gradT (cutTest n χ) (τ, y) :=
    fun n => (hφ n).gradT.periodic
  have hptw : ∀ (n : ℕ) (z : PSpace P), ‖xlift (gradT (cutTest n χ)) (hΦper n) z‖ ≤
      ‖xlift (gradT χ) hgper z‖ + B * ‖xlift χ hper z‖ := by
    intro n z
    obtain ⟨y, s⟩ := z
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective s
    simp only [xlift_coe, gradT_cutTest n hsm]
    calc ‖((cutχ n y : ℝ) : ℂ) • gradT χ (t, y) + χ (t, y) • wvec n y‖
        ≤ ‖((cutχ n y : ℝ) : ℂ) • gradT χ (t, y)‖ + ‖χ (t, y) • wvec n y‖ := norm_add_le _ _
      _ ≤ ‖gradT χ (t, y)‖ + B * ‖χ (t, y)‖ := by
        rw [norm_smul, norm_smul]
        have h1 := norm_cutχ_le n y
        have h2 := hB n y
        have h3 := norm_nonneg (gradT χ (t, y))
        have h4 := norm_nonneg (χ (t, y))
        nlinarith [mul_le_mul_of_nonneg_right h1 h3, mul_le_mul_of_nonneg_left h2 h4]
  have hbm : MemLp (fun z : PSpace P => ‖xlift (gradT χ) hgper z‖ + B * ‖xlift χ hper z‖) 2
      (volume : Measure (PSpace P)) := hLg.norm.add (hLχ.norm.const_mul B)
  have hLn : ∀ n : ℕ, MemLp (xlift (gradT (cutTest n χ)) (hΦper n)) 2
      (volume : Measure (PSpace P)) := fun n =>
    hbm.mono' (xlift_continuous (hΦper n) (hφ n).gradT.continuous).aestronglyMeasurable
      (ae_of_all _ (hptw n))
  have hintn : ∀ n : ℕ, Integrable (fun z : PSpace P =>
      dotL (xlift (gradT (cutTest n χ)) (hΦper n) z) ((F : PSpace P → SpaceC) z))
      (volume : Measure (PSpace P)) := fun n => integrable_dotL_of_memLp_holder (hLn n) hFm
  have hzero : ∀ n : ℕ, ∫ z : PSpace P,
      dotL (xlift (gradT (cutTest n χ)) (hΦper n) z) ((F : PSpace P → SpaceC) z) = 0 := by
    intro n
    have h := hF (cutTest n χ) (hφ n)
    rw [pairX_eq_xlift (hΦper n) F (hintn n)] at h
    exact (smul_eq_zero.mp h).resolve_left (by
      have : (0 : ℝ) < P⁻¹ := inv_pos.mpr (Fact.out : (0 : ℝ) < P)
      exact this.ne')
  have hFn : MemLp (fun z : PSpace P => ‖(F : PSpace P → SpaceC) z‖) 2
      (volume : Measure (PSpace P)) := hFm.norm
  obtain ⟨K, hK0, hKle⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : CVec3, ‖dotL a b‖ ≤ K * ‖a‖ * ‖b‖ :=
    ⟨‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖, ContinuousLinearMap.opNorm_nonneg _, fun a b =>
      ContinuousLinearMap.le_opNorm₂ _ _ _⟩
  have hbound_int : Integrable (fun z : PSpace P =>
      K * ((‖xlift (gradT χ) hgper z‖ + B * ‖xlift χ hper z‖) * ‖(F : PSpace P → SpaceC) z‖))
      (volume : Measure (PSpace P)) :=
    (hbm.integrable_mul hFn).const_mul K
  have hdom : ∀ (n : ℕ) (z : PSpace P),
      ‖dotL (xlift (gradT (cutTest n χ)) (hΦper n) z) ((F : PSpace P → SpaceC) z)‖ ≤
        K * ((‖xlift (gradT χ) hgper z‖ + B * ‖xlift χ hper z‖) *
          ‖(F : PSpace P → SpaceC) z‖) := by
    intro n z
    calc _ ≤ K * ‖xlift (gradT (cutTest n χ)) (hΦper n) z‖ * ‖(F : PSpace P → SpaceC) z‖ :=
          hKle _ _
      _ ≤ K * (‖xlift (gradT χ) hgper z‖ + B * ‖xlift χ hper z‖) *
            ‖(F : PSpace P → SpaceC) z‖ := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hptw n z) hK0)
            (norm_nonneg _)
      _ = _ := by ring
  have hlim : ∀ z : PSpace P, Tendsto (fun n : ℕ =>
      dotL (xlift (gradT (cutTest n χ)) (hΦper n) z) ((F : PSpace P → SpaceC) z)) atTop
      (𝓝 (dotL (xlift (gradT χ) hgper z) ((F : PSpace P → SpaceC) z))) := by
    intro z
    obtain ⟨y, s⟩ := z
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective s
    have hc1 : Tendsto (fun n : ℕ => ((cutχ n y : ℝ) : ℂ)) atTop (𝓝 1) := by
      have h := (goodMult_cutχ_sub_one).lim y
      have h' : Tendsto (fun n : ℕ => cutχ n y) atTop (𝓝 1) := by
        have := h.add_const 1
        simpa using this
      have h2 := (Complex.continuous_ofReal.tendsto 1).comp h'
      rwa [Complex.ofReal_one] at h2
    have hw : Tendsto (fun n : ℕ => wvec n y) atTop (𝓝 0) := by
      have hj : ∀ j : Fin 3, Tendsto (fun n : ℕ =>
          ((sd j (cutχ n) y : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)) atTop (𝓝 0) := by
        intro j
        have h := (goodMult_sd_cutχ j 1).lim y
        simp only [one_mul] at h
        simpa using ((Complex.continuous_ofReal.tendsto 0).comp h).smul_const
          (EuclideanSpace.single j (1 : ℂ))
      have := tendsto_finsetSum Finset.univ fun j _ => hj j
      simpa [wvec] using this
    have ha : Tendsto (fun n : ℕ => xlift (gradT (cutTest n χ)) (hΦper n) (y, (t : AddCircle P)))
        atTop (𝓝 (xlift (gradT χ) hgper (y, (t : AddCircle P)))) := by
      simp only [xlift_coe, gradT_cutTest _ hsm]
      have := (hc1.smul_const (gradT χ (t, y))).add
        ((tendsto_const_nhds (x := χ (t, y))).smul hw)
      simpa using this
    have hd : Tendsto (fun n : ℕ => dotL (xlift (gradT (cutTest n χ)) (hΦper n) (y, (t : AddCircle P))))
        atTop (𝓝 (dotL (xlift (gradT χ) hgper (y, (t : AddCircle P))))) :=
      (dotL.continuous.tendsto _).comp ha
    exact ((ContinuousLinearMap.apply ℂ ℂ ((F : PSpace P → SpaceC) (y, (t : AddCircle P)))).continuous.tendsto _).comp hd
  have hT := tendsto_integral_of_dominated_convergence
    (fun z : PSpace P => K * ((‖xlift (gradT χ) hgper z‖ + B * ‖xlift χ hper z‖) *
        ‖(F : PSpace P → SpaceC) z‖))
    (fun n => (hintn n).aestronglyMeasurable) hbound_int
    (fun n => ae_of_all _ (hdom n)) (ae_of_all _ hlim)
  have h0 : ∫ z : PSpace P, dotL (xlift (gradT χ) hgper z) ((F : PSpace P → SpaceC) z) = 0 :=
    tendsto_nhds_unique hT (by simpa only [hzero] using tendsto_const_nhds)
  rw [h0, smul_zero]

end UnforcedLeray.Short.PartIIIb.NearInst
