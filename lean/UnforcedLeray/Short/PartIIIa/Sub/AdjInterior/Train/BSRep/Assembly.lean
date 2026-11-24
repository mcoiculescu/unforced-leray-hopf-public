import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.BSRep.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# `PartIII-a:T21/2/7/2/1/1/2/10`: `TjTrainBSRep` from its leaves

Source: `the November 2 reference manuscript` (SP) lines 261-266 (`v = ∇^⊥ψ`),
270-288 (the `BUC` train, zero circulation, `v(-x) = -v(x)`), 2081-2084 (`E_c = curl v_c`, `K_c`
with the horizontal mean mode), 3121. Vocabulary and leaves: `BSRep/Defs.lean`.

* `bsrKcDivCurl_of`: `K_cω` is differentiable, `div K_cω = 0`, `curl K_cω = ω` (from
  `BsrWeightIntShift`, `BsrKcHasFDeriv`, `BsrKcFDerivEval`, `BsrKerPointwiseDecay`);
* `tjTrainBSRep_of`: `TjTrainBSRep m` (from `TjTrainVort`, `TjVortDecay m`, `TjLadGrad m`,
  `TjKcBound`, `BsrFDerivNorm`, `BsrKcDivCurl`, `BsrLiouville`, `BsrKcOdd`);
* `tjTrainBSRep_of_leaves`: the composition.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Calculus helpers -/

/-- The partials of a component of a field with Fréchet derivative `L` at `x`. -/
theorem bsr_partial_comp {u : ℝ × ℝ → UnforcedLeray.Cyl.Vec2}
    {L : ℝ × ℝ →L[ℝ] UnforcedLeray.Cyl.Vec2} {x : ℝ × ℝ} (hL : HasFDerivAt u L x) (j : Fin 2) :
    UnforcedLeray.Cyl.partialQ (fun z => u z j) x = L (1, 0) j ∧
      UnforcedLeray.Cyl.partialEta (fun z => u z j) x = L (0, 1) j := by
  have hLj : HasFDerivAt (fun z => u z j)
      ((EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).comp L) x :=
    (EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).hasFDerivAt.comp x hL
  constructor
  · have h0 : HasDerivAt (fun q : ℝ => ((q, x.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) x.1 :=
      (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
    exact (hLj.comp_hasDerivAt x.1 h0).deriv
  · have h0 : HasDerivAt (fun η : ℝ => ((x.1, η) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) x.2 :=
      (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
    exact (hLj.comp_hasDerivAt x.2 h0).deriv

theorem bsr_comp_differentiable {u : ℝ × ℝ → UnforcedLeray.Cyl.Vec2} (hu : Differentiable ℝ u)
    (j : Fin 2) : Differentiable ℝ (fun z => u z j) :=
  (EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).differentiable.comp hu

theorem bsr_partialQ_sub {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : ℝ × ℝ) : UnforcedLeray.Cyl.partialQ (fun w => f w - g w) z =
      UnforcedLeray.Cyl.partialQ f z - UnforcedLeray.Cyl.partialQ g z := by
  have hl : DifferentiableAt ℝ (fun q : ℝ => ((q, z.2) : ℝ × ℝ)) z.1 :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  exact deriv_sub ((hf _).comp z.1 hl) ((hg _).comp z.1 hl)

theorem bsr_partialEta_sub {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : ℝ × ℝ) : UnforcedLeray.Cyl.partialEta (fun w => f w - g w) z =
      UnforcedLeray.Cyl.partialEta f z - UnforcedLeray.Cyl.partialEta g z := by
  have hl : DifferentiableAt ℝ (fun η : ℝ => ((z.1, η) : ℝ × ℝ)) z.2 :=
    (differentiableAt_const _).prodMk differentiableAt_id
  exact deriv_sub ((hf _).comp z.2 hl) ((hg _).comp z.2 hl)

theorem bsr_divergence_sub {v u : ℝ × ℝ → UnforcedLeray.Cyl.Vec2} (hv : Differentiable ℝ v)
    (hu : Differentiable ℝ u) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.divergence (fun w => v w - u w) z =
      UnforcedLeray.Cyl.divergence v z - UnforcedLeray.Cyl.divergence u z := by
  unfold UnforcedLeray.Cyl.divergence
  have e0 : (fun w => (v w - u w) 0) = fun w => v w 0 - u w 0 := by
    funext w; simp
  have e1 : (fun w => (v w - u w) 1) = fun w => v w 1 - u w 1 := by
    funext w; simp
  rw [e0, e1, bsr_partialQ_sub (bsr_comp_differentiable hv 0) (bsr_comp_differentiable hu 0),
    bsr_partialEta_sub (bsr_comp_differentiable hv 1) (bsr_comp_differentiable hu 1)]
  ring

theorem bsr_curl_sub {v u : ℝ × ℝ → UnforcedLeray.Cyl.Vec2} (hv : Differentiable ℝ v)
    (hu : Differentiable ℝ u) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.curl (fun w => v w - u w) z =
      UnforcedLeray.Cyl.curl v z - UnforcedLeray.Cyl.curl u z := by
  unfold UnforcedLeray.Cyl.curl
  have e0 : (fun w => (v w - u w) 0) = fun w => v w 0 - u w 0 := by
    funext w; simp
  have e1 : (fun w => (v w - u w) 1) = fun w => v w 1 - u w 1 := by
    funext w; simp
  rw [e0, e1, bsr_partialQ_sub (bsr_comp_differentiable hv 1) (bsr_comp_differentiable hu 1),
    bsr_partialEta_sub (bsr_comp_differentiable hv 0) (bsr_comp_differentiable hu 0)]
  ring

theorem bsr_pd0 {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    B0579.pd 0 f z = UnforcedLeray.Cyl.partialQ f z := by
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hf z]
  simp [B0579.pd, B0579.dir]

theorem bsr_pd1 {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    B0579.pd 1 f z = UnforcedLeray.Cyl.partialEta f z := by
  rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hf z]
  simp [B0579.pd, B0579.dir]

theorem bsr_bsKernel_neg (c : ℝ) (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.bsKernel c (-z) = -UnforcedLeray.Cyl.bsKernel c z := by
  ext j
  rw [PiLp.neg_apply]
  exact bsKernel_neg' c z j

theorem bsr_eq_zero_of_eq_neg {a : UnforcedLeray.Cyl.Vec2} (h : a = -a) : a = 0 := by
  have h2 : (2 : ℝ) • a = 0 := by
    rw [two_smul]
    calc a + a = a + -a := by rw [← h]
      _ = 0 := add_neg_cancel a
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-! ## The divergence and curl of `K_cω` -/

/-- **`BsrKcDivCurl` from its leaves**: `∂_j(K_cω) = K_c(∂_jω)` (`BsrKcHasFDeriv`,
`BsrKcFDerivEval`); the components of `K_c(∂_jω)(x)` are the scalar integrals
`∫_cell ∂_jω(y) K_c(x - y)_i dy` (`BsrWeightIntShift`); with `K_c(x - y) = -K_c(y - x)` the
divergence and the curl are the two identities of `BsrKerPointwiseDecay` at the point `x`. -/
theorem bsrKcDivCurl_of (hW : BsrWeightIntShift) (hD : BsrKcHasFDeriv) (hE : BsrKcFDerivEval)
    (hP : BsrKerPointwiseDecay) : BsrKcDivCurl := by
  intro c β A hc hβ g hg hper hA hA'
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hgd : Differentiable ℝ g := hg1.differentiable one_ne_zero
  have hder := hD c β A hc hβ g hg1 hper hA hA'
  refine ⟨fun x => (hder x).differentiableAt, fun x => ?_⟩
  obtain ⟨hEq, hEe⟩ := hE c β A hc hβ g hg1 hper hA' x
  -- the partials of the components of `K_c g`
  have hpart : ∀ j : Fin 2,
      UnforcedLeray.Cyl.partialQ (fun z => UnforcedLeray.Cyl.K c g z j) x =
        UnforcedLeray.Cyl.K c (UnforcedLeray.Cyl.partialQ g) x j ∧
      UnforcedLeray.Cyl.partialEta (fun z => UnforcedLeray.Cyl.K c g z j) x =
        UnforcedLeray.Cyl.K c (UnforcedLeray.Cyl.partialEta g) x j := by
    intro j
    obtain ⟨h1, h2⟩ := bsr_partial_comp (hder x) j
    rw [hEq] at h1
    rw [hEe] at h2
    exact ⟨h1, h2⟩
  -- the partials of `g` are continuous and weighted-bounded
  have hpq : ∀ y : ℝ × ℝ, |UnforcedLeray.Cyl.partialQ g y| ≤ ‖fderiv ℝ g y‖ := by
    intro y
    rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hgd y, ← Real.norm_eq_abs]
    calc ‖fderiv ℝ g y ((1 : ℝ), (0 : ℝ))‖ ≤ ‖fderiv ℝ g y‖ * ‖((1 : ℝ), (0 : ℝ))‖ :=
          (fderiv ℝ g y).le_opNorm _
      _ = ‖fderiv ℝ g y‖ := by simp
  have hpe : ∀ y : ℝ × ℝ, |UnforcedLeray.Cyl.partialEta g y| ≤ ‖fderiv ℝ g y‖ := by
    intro y
    rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hgd y, ← Real.norm_eq_abs]
    calc ‖fderiv ℝ g y ((0 : ℝ), (1 : ℝ))‖ ≤ ‖fderiv ℝ g y‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
          (fderiv ℝ g y).le_opNorm _
      _ = ‖fderiv ℝ g y‖ := by simp
  have hwq : ∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ (β / 2) * |UnforcedLeray.Cyl.partialQ g y| ≤ A :=
    fun y => (mul_le_mul_of_nonneg_left (hpq y) (Real.rpow_nonneg (by positivity) _)).trans (hA' y)
  have hwe : ∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ (β / 2) * |UnforcedLeray.Cyl.partialEta g y| ≤ A :=
    fun y => (mul_le_mul_of_nonneg_left (hpe y) (Real.rpow_nonneg (by positivity) _)).trans (hA' y)
  have hcq : Continuous (UnforcedLeray.Cyl.partialQ g) := by
    have e : UnforcedLeray.Cyl.partialQ g = fun y => fderiv ℝ g y ((1 : ℝ), (0 : ℝ)) :=
      funext (UnforcedLeray.Cyl.partialQ_eq_fderiv hgd)
    rw [e]
    exact (hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hce : Continuous (UnforcedLeray.Cyl.partialEta g) := by
    have e : UnforcedLeray.Cyl.partialEta g = fun y => fderiv ℝ g y ((0 : ℝ), (1 : ℝ)) :=
      funext (UnforcedLeray.Cyl.partialEta_eq_fderiv hgd)
    rw [e]
    exact (hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- the components of `K_c f (x)` as scalar integrals
  have hcomp : ∀ f : ℝ × ℝ → ℝ, Continuous f →
      (∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ (β / 2) * |f y| ≤ A) → ∀ j : Fin 2,
      IntegrableOn (fun y => f y * UnforcedLeray.Cyl.bsKernel c (x - y) j)
          (UnforcedLeray.Cyl.cell c) ∧
        UnforcedLeray.Cyl.K c f x j =
          ∫ y in UnforcedLeray.Cyl.cell c, f y * UnforcedLeray.Cyl.bsKernel c (x - y) j := by
    intro f hf hfA j
    have hvec : IntegrableOn (fun y => f y • UnforcedLeray.Cyl.bsKernel c (x - y))
        (UnforcedLeray.Cyl.cell c) := by
      refine Integrable.mono' ((hW c β hc hβ x).const_mul A) ?_ ?_
      · exact hf.aestronglyMeasurable.smul ((UnforcedLeray.Cyl.measurable_bsKernel c).comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable
      · refine Eventually.of_forall (fun y => ?_)
        have hxy : x - y = -(y - x) := by abel
        rw [norm_smul, Real.norm_eq_abs, hxy, bsr_bsKernel_neg, norm_neg]
        have hwpos : 0 < (1 + y.2 ^ 2) ^ (β / 2) := Real.rpow_pos_of_pos (by positivity) _
        have hfy : |f y| ≤ A * (1 + y.2 ^ 2) ^ (-(β / 2)) := by
          rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hwpos, mul_comm]
          exact hfA y
        calc |f y| * ‖UnforcedLeray.Cyl.bsKernel c (y - x)‖
            ≤ (A * (1 + y.2 ^ 2) ^ (-(β / 2))) * ‖UnforcedLeray.Cyl.bsKernel c (y - x)‖ :=
              mul_le_mul_of_nonneg_right hfy (norm_nonneg _)
          _ = A * ((1 + y.2 ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel c (y - x)‖) := by
              ring
    have hj := (EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).integral_comp_comm hvec
    refine ⟨?_, ?_⟩
    · have hi := (EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).integrable_comp hvec
      refine hi.congr (Eventually.of_forall fun y => ?_)
      simp
    · calc UnforcedLeray.Cyl.K c f x j
          = (EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ)
              (∫ y in UnforcedLeray.Cyl.cell c, f y • UnforcedLeray.Cyl.bsKernel c (x - y)) := rfl
        _ = ∫ y in UnforcedLeray.Cyl.cell c, (EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ)
              (f y • UnforcedLeray.Cyl.bsKernel c (x - y)) := hj.symm
        _ = ∫ y in UnforcedLeray.Cyl.cell c, f y * UnforcedLeray.Cyl.bsKernel c (x - y) j := by
              refine integral_congr_ae (Eventually.of_forall fun y => ?_)
              simp
  -- the kernel identities at the point `x`
  obtain ⟨hdiv, hcurl⟩ := hP c β A hc hβ g hg hper hA hA' x
  rw [cell_eq_Cyl'] at hdiv hcurl
  have hker : ∀ (y : ℝ × ℝ) (j : Fin 2),
      kerD c (y - x) j = -UnforcedLeray.Cyl.bsKernel c (x - y) j := by
    intro y j
    have e : y - x = -(x - y) := by abel
    rw [kerD, e, bsKernel_neg']
  have hQ0 := hcomp _ hcq hwq 0
  have hQ1 := hcomp _ hcq hwq 1
  have hE0 := hcomp _ hce hwe 0
  have hE1 := hcomp _ hce hwe 1
  refine ⟨?_, ?_⟩
  · unfold UnforcedLeray.Cyl.divergence
    rw [(hpart 0).1, (hpart 1).2, hQ0.2, hE1.2, ← integral_add hQ0.1 hE1.1]
    have e : (fun y => UnforcedLeray.Cyl.partialQ g y * UnforcedLeray.Cyl.bsKernel c (x - y) 0 +
        UnforcedLeray.Cyl.partialEta g y * UnforcedLeray.Cyl.bsKernel c (x - y) 1) =
        fun y => -(kerD c (y - x) 0 * B0579.pd 0 g y + kerD c (y - x) 1 * B0579.pd 1 g y) := by
      funext y
      rw [hker, hker, bsr_pd0 hgd, bsr_pd1 hgd]
      ring
    rw [e, integral_neg, hdiv, neg_zero]
  · unfold UnforcedLeray.Cyl.curl
    rw [(hpart 1).1, (hpart 0).2, hQ1.2, hE0.2, ← integral_sub hQ1.1 hE0.1]
    have e : (fun y => UnforcedLeray.Cyl.partialQ g y * UnforcedLeray.Cyl.bsKernel c (x - y) 1 -
        UnforcedLeray.Cyl.partialEta g y * UnforcedLeray.Cyl.bsKernel c (x - y) 0) =
        fun y => kerD c (y - x) 0 * B0579.pd 1 g y - kerD c (y - x) 1 * B0579.pd 0 g y := by
      funext y
      rw [hker, hker, bsr_pd0 hgd, bsr_pd1 hgd]
      ring
    rw [e, hcurl]

/-! ## The Biot-Savart law of the train -/

/-- **`TjTrainBSRep m` from its leaves** (SP 261-266, 270-288, 2081-2084): at a fixed age `ρ ≥ 0`
the slice `ω = E(ρ)` is `C^∞`, `c`-periodic, even, and `ω`, `Dω` carry the weight
`(1 + x₂²)^{(m+1)/2}` (`TjVortDecay`, `TjLadGrad`, `BsrFDerivNorm`); `u = K_cω` is differentiable
with `div u = 0`, `curl u = ω` (`BsrKcDivCurl`); `w = v(ρ) - u` is bounded (`IsBUCTrain`,
`TjKcBound`), divergence free and curl free, hence constant (`BsrLiouville`); `v(ρ)` and `u` are
odd (`IsTrain.odd`, `BsrKcOdd`), so `w = w(0) = 0`. -/
theorem tjTrainBSRep_of (m : ℝ) (hm : 8 < m) (hV : TjTrainVort) (hDec : TjVortDecay m)
    (hG : TjLadGrad m) (hKb : TjKcBound) (hFN : BsrFDerivNorm) (hDC : BsrKcDivCurl)
    (hL : BsrLiouville) (hO : BsrKcOdd) : TjTrainBSRep m := by
  intro ν hν hν1 tr hbuc hB p hp
  obtain ⟨ρ, x⟩ := p
  have hρ : 0 ≤ ρ := hp.1
  have hρmem : ρ ∈ Icc (0 : ℝ) ρ := ⟨hρ, le_rfl⟩
  have hc1 : 1 ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hc0 : 0 < ν ^ (-2 : ℝ) := by linarith
  obtain ⟨hEs, -, -⟩ := hV ν (ν ^ (-2 : ℝ)) tr
  have hg : ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr ρ) :=
    hEs.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => ⟨mem_Ici.2 hρ, mem_univ _⟩)
  have hgd : Differentiable ℝ (UnforcedLeray.B0238.Ec tr ρ) := hg.differentiable (by simp)
  have hper : UnforcedLeray.Cyl.IsPeriodic (ν ^ (-2 : ℝ)) (UnforcedLeray.B0238.Ec tr ρ) :=
    UnforcedLeray.Short.PartI.vjl_curl_periodic tr hρ
  -- the weighted bounds of `ω = E(ρ)` and `Dω`
  have hdec := hDec ν hν hν1 tr hbuc hB
  obtain ⟨C₀, hC₀⟩ := hdec ρ hρ
  obtain ⟨A₁, hA₁⟩ := hG ν (ν ^ (-2 : ℝ)) tr hc0 hB 1 (by decide) ρ hρ
  obtain ⟨A₂, hA₂⟩ := hG ν (ν ^ (-2 : ℝ)) tr hc0 hB 2 (by decide) ρ hρ
  have h0 : ∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ ((m + 1) / 2) * |UnforcedLeray.B0238.Ec tr ρ y| ≤
      max C₀ (A₁ + A₂) := fun y => (hC₀ ρ hρmem y).trans (le_max_left _ _)
  have h1 : ∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ ((m + 1) / 2) *
      ‖fderiv ℝ (UnforcedLeray.B0238.Ec tr ρ) y‖ ≤ max C₀ (A₁ + A₂) := by
    intro y
    have hw1 : 1 ≤ 1 + y.2 ^ 2 := by nlinarith [sq_nonneg y.2]
    have hmono : (1 + y.2 ^ 2) ^ ((m + 1) / 2) ≤ (1 + y.2 ^ 2) ^ ((m + 2) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
    have hq : UnforcedLeray.Cyl.partialQ (UnforcedLeray.B0238.Ec tr ρ) y =
        tjW [1] (tjE tr) (ρ, y) := (tjW_one_apply hEs hρ y).symm
    have he : UnforcedLeray.Cyl.partialEta (UnforcedLeray.B0238.Ec tr ρ) y =
        tjW [2] (tjE tr) (ρ, y) := (tjW_two_apply hEs hρ y).symm
    have hAq := hA₁ ρ hρmem y
    have hAe := hA₂ ρ hρmem y
    rw [← hq] at hAq
    rw [← he] at hAe
    have hwnn : 0 ≤ (1 + y.2 ^ 2) ^ ((m + 1) / 2) := Real.rpow_nonneg (by positivity) _
    calc (1 + y.2 ^ 2) ^ ((m + 1) / 2) * ‖fderiv ℝ (UnforcedLeray.B0238.Ec tr ρ) y‖
        ≤ (1 + y.2 ^ 2) ^ ((m + 1) / 2) *
            (|UnforcedLeray.Cyl.partialQ (UnforcedLeray.B0238.Ec tr ρ) y| +
              |UnforcedLeray.Cyl.partialEta (UnforcedLeray.B0238.Ec tr ρ) y|) :=
          mul_le_mul_of_nonneg_left (hFN _ y (hgd y)) hwnn
      _ ≤ (1 + y.2 ^ 2) ^ ((m + 2) / 2) *
            |UnforcedLeray.Cyl.partialQ (UnforcedLeray.B0238.Ec tr ρ) y| +
          (1 + y.2 ^ 2) ^ ((m + 2) / 2) *
            |UnforcedLeray.Cyl.partialEta (UnforcedLeray.B0238.Ec tr ρ) y| := by
          rw [mul_add]
          exact add_le_add (mul_le_mul_of_nonneg_right hmono (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hmono (abs_nonneg _))
      _ ≤ A₁ + A₂ := add_le_add hAq hAe
      _ ≤ max C₀ (A₁ + A₂) := le_max_right _ _
  -- `u = K_cω`: differentiable, divergence free, curl `ω`
  obtain ⟨hud, hdc⟩ := hDC (ν ^ (-2 : ℝ)) (m + 1) (max C₀ (A₁ + A₂)) hc1 (by linarith) _ hg hper
    h0 h1
  -- `w = v(ρ) - u`
  have hvd : Differentiable ℝ (tr.v ρ) :=
    (UnforcedLeray.B0238.contDiff_Vc tr hρ).differentiable (by simp)
  have hwd : Differentiable ℝ (fun z => tr.v ρ z -
      UnforcedLeray.Cyl.K (ν ^ (-2 : ℝ)) (UnforcedLeray.B0238.Ec tr ρ) z) := hvd.sub hud
  have hdivw : ∀ z : ℝ × ℝ, UnforcedLeray.Cyl.divergence (fun z => tr.v ρ z -
      UnforcedLeray.Cyl.K (ν ^ (-2 : ℝ)) (UnforcedLeray.B0238.Ec tr ρ) z) z = 0 := by
    intro z
    rw [bsr_divergence_sub hvd hud z, tr.isTrain.solenoidal ρ hρ z, (hdc z).1, sub_zero]
  have hcurlw : ∀ z : ℝ × ℝ, UnforcedLeray.Cyl.curl (fun z => tr.v ρ z -
      UnforcedLeray.Cyl.K (ν ^ (-2 : ℝ)) (UnforcedLeray.B0238.Ec tr ρ) z) z = 0 := by
    intro z
    rw [bsr_curl_sub hvd hud z, (hdc z).2]
    exact sub_self _
  obtain ⟨M, hM⟩ := hbuc.sup_bound hρ
  obtain ⟨C₁, hC₁⟩ := hKb (ν ^ (-2 : ℝ)) m hc1 (by linarith) (tjE tr) hEs.continuousOn
    (fun ρ' hρ' y => UnforcedLeray.Short.PartI.vjl_curl_periodic tr hρ' y) hdec ρ hρ
  have hwb : ∃ M' : ℝ, ∀ z : ℝ × ℝ, ‖tr.v ρ z -
      UnforcedLeray.Cyl.K (ν ^ (-2 : ℝ)) (UnforcedLeray.B0238.Ec tr ρ) z‖ ≤ M' :=
    ⟨M + C₁, fun z => (norm_sub_le _ _).trans (add_le_add (hM ρ hρmem z) (hC₁ ρ hρmem z))⟩
  have hconst := hL _ hwd hdivw hcurlw hwb
  -- `w(0) = 0`
  have hv0 : tr.v ρ 0 = 0 := by
    have h := tr.isTrain.odd ρ hρ 0
    rw [neg_zero] at h
    exact bsr_eq_zero_of_eq_neg h
  have hu0 : UnforcedLeray.Cyl.K (ν ^ (-2 : ℝ)) (UnforcedLeray.B0238.Ec tr ρ) 0 = 0 := by
    have h := hO (ν ^ (-2 : ℝ)) hc0 _ hper (fun y => UnforcedLeray.B0238.Ec_even tr hρ y) 0
    rw [neg_zero] at h
    exact bsr_eq_zero_of_eq_neg h
  have hx := hconst x 0
  rw [hv0, hu0, sub_zero] at hx
  show tr.v ρ x = UnforcedLeray.Cyl.K (ν ^ (-2 : ℝ)) (UnforcedLeray.B0238.Ec tr ρ) x
  exact sub_eq_zero.1 hx

/-- **`TjTrainBSRep m` from all its leaves**. -/
theorem tjTrainBSRep_of_leaves (m : ℝ) (hm : 8 < m) (hV : TjTrainVort) (hDec : TjVortDecay m)
    (hG : TjLadGrad m) (hKb : TjKcBound) (hFN : BsrFDerivNorm) (hW : BsrWeightIntShift)
    (hD : BsrKcHasFDeriv) (hE : BsrKcFDerivEval) (hP : BsrKerPointwiseDecay)
    (hL : BsrLiouville) (hO : BsrKcOdd) : TjTrainBSRep m :=
  tjTrainBSRep_of m hm hV hDec hG hKb hFN (bsrKcDivCurl_of hW hD hE hP) hL hO

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.bsrKcDivCurl_of
#print axioms UnforcedLeray.Short.IIIa.tjTrainBSRep_of
#print axioms UnforcedLeray.Short.IIIa.tjTrainBSRep_of_leaves
