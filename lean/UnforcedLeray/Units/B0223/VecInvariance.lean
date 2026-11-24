import UnforcedLeray.Units.B0223.Invariance

/-!
# B0223 helper: the outer semigroup preserves axisymmetric meridional (no-swirl) fields

Blueprint unit B0223 (label `eq:st18-t00116`), `paper/main.tex` lines 3327–3347 and 3364–3366
("the same statement holds for `eq:st18-t00115`"; blueprint proof outline: "the meridional
subspace is invariant").

We prove `LiftInvariant` for the meridional lift `liftVec`. The vector semigroup acts on
`ℂ³`-valued fields componentwise; the meridional class is characterized by equivariance under
the reflections `reflR n` of `ℝ³` in planes containing the `e₃` axis (`n ⊥ e₃`):
`u(reflR n y, τ) = reflC n (u(y, τ))`, `reflC n` the complexified reflection (`AxEquiv`).

* The lift representative `a (b_r e_r + b_z e_z)` is `AxEquiv` (`e_r(gy) = g e_r(y)`).
* `AxEquiv` is preserved by the phase shift, by the dilation and by the Gaussian average
  (rotation invariance of the Gaussian; `reflC n` commutes with the Bochner integral since it is
  an involution).
* For an `AxEquiv` field `R`: the reflection in the `x₁ = 0` plane fixes `(r, 0, z)`, so
  `R(r, 0, z)` has no second component; the reflection `rotTo x` maps `(r, 0, z)` to `x`, so
  `R(x) = rotTo x R(r, 0, z) = R₀ e_r(x) + R₂ e_z`, a meridional lift (`exists_liftVec_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace
open UnforcedLeray.Gaussian (Euc gaussKernel)

namespace UnforcedLeray.B0223

open UnforcedLeray.B0220 UnforcedLeray.Infra

/-! ### Real reflections fixing `e₃` -/

/-- The reflection of `ℝ³` in the plane orthogonal to `n`. -/
def reflR (n : Space) : Space ≃ₗᵢ[ℝ] Space := Submodule.reflection (ℝ ∙ n)ᗮ

theorem reflR_apply (n w : Space) : reflR n w = w - (2 * (⟪n, w⟫ / ‖n‖ ^ 2)) • n := by
  rw [reflR, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  module

theorem rotTo_eq_reflR (x : Space) : rotTo x = reflR (axisPt x - x) := rfl

theorem reflR_e3 {n : Space} (hn : n 2 = 0) :
    reflR n (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1 := by
  refine Submodule.reflection_mem_subspace_eq_self ?_
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_single_right]
  simp [hn]

theorem two_of_fix {g : Space ≃ₗᵢ[ℝ] Space}
    (hg : g (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1) (y : Space) :
    g y 2 = y 2 := by
  rw [coord2_eq_inner, coord2_eq_inner y]
  conv_lhs => rw [← hg]
  exact LinearIsometryEquiv.inner_map_map _ _ _

theorem radius_of_fix {g : Space ≃ₗᵢ[ℝ] Space}
    (hg : g (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1) (y : Space) :
    radius (g y) = radius y := by
  have h1 := norm_sq_eq_radius (g y)
  have h2 := norm_sq_eq_radius y
  rw [LinearIsometryEquiv.norm_map, two_of_fix hg] at h1
  have h : radius (g y) ^ 2 = radius y ^ 2 := by linarith
  exact (pow_left_inj₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) two_ne_zero).1 h

theorem unitR_eq (y : Space) :
    unitR y = (radius y)⁻¹ • (y - y 2 • EuclideanSpace.single 2 1) := by
  ext i
  fin_cases i <;> simp [unitR, EuclideanSpace.single_apply, div_eq_inv_mul]

theorem unitR_of_fix {g : Space ≃ₗᵢ[ℝ] Space}
    (hg : g (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1) (y : Space) :
    unitR (g y) = g (unitR y) := by
  rw [unitR_eq, unitR_eq, map_smul, map_sub, map_smul, hg, two_of_fix hg, radius_of_fix hg]

/-! ### Complexification -/

/-- A real vector as a complex vector. -/
def ofRealVec (w : Space) : SpaceC := WithLp.toLp 2 fun i => ((w i : ℝ) : ℂ)

@[simp] theorem ofRealVec_apply (w : Space) (i : Fin 3) : ofRealVec w i = (w i : ℂ) := rfl

/-- `Σ_j n_j v_j`. -/
def pairC (n : Space) (v : SpaceC) : ℂ := ∑ j, (n j : ℂ) * v j

theorem pairC_add (n : Space) (u v : SpaceC) : pairC n (u + v) = pairC n u + pairC n v := by
  simp only [pairC, PiLp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairC_smul (n : Space) (k : ℂ) (v : SpaceC) : pairC n (k • v) = k * pairC n v := by
  simp only [pairC, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The complexified reflection `v ↦ v - (2 ⟨n, v⟩/‖n‖²) n`. -/
def reflCL (n : Space) : SpaceC →ₗ[ℂ] SpaceC where
  toFun v := v - (((2 / ‖n‖ ^ 2 : ℝ) : ℂ) * pairC n v) • ofRealVec n
  map_add' u v := by
    rw [pairC_add, mul_add, add_smul]
    abel
  map_smul' k v := by
    rw [pairC_smul, RingHom.id_apply, smul_sub, smul_smul]
    congr 2
    ring

/-- The complexified reflection as a continuous linear map. -/
def reflC (n : Space) : SpaceC →L[ℂ] SpaceC := LinearMap.toContinuousLinearMap (reflCL n)

theorem reflC_apply (n : Space) (v : SpaceC) :
    reflC n v = v - (((2 / ‖n‖ ^ 2 : ℝ) : ℂ) * pairC n v) • ofRealVec n := rfl

theorem pairC_ofRealVec (n w : Space) : pairC n (ofRealVec w) = ((⟪n, w⟫ : ℝ) : ℂ) := by
  simp only [pairC, ofRealVec_apply, PiLp.inner_apply, Fin.sum_univ_three]
  push_cast
  simp only [conj_trivial, RCLike.inner_apply]
  push_cast
  ring

theorem norm_sq_eq_sum (n : Space) : ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem reflC_ofRealVec (n w : Space) : reflC n (ofRealVec w) = ofRealVec (reflR n w) := by
  rw [reflC_apply, reflR_apply, pairC_ofRealVec]
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, ofRealVec_apply, smul_eq_mul]
  push_cast
  ring

theorem reflC_reflC (n : Space) (v : SpaceC) : reflC n (reflC n v) = v := by
  by_cases hn : n = 0
  · subst hn
    simp [reflC_apply, pairC]
  have hn2 : ‖n‖ ^ 2 ≠ 0 := by positivity
  have hpair : pairC n (ofRealVec n) = ((‖n‖ ^ 2 : ℝ) : ℂ) := by
    rw [pairC_ofRealVec, real_inner_self_eq_norm_sq]
  have hlin : ∀ (a : ℂ) (u : SpaceC), pairC n (u - a • ofRealVec n) =
      pairC n u - a * pairC n (ofRealVec n) := by
    intro a u
    simp only [pairC, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [reflC_apply, reflC_apply, hlin, hpair]
  have hc : ((2 / ‖n‖ ^ 2 : ℝ) : ℂ) * ((‖n‖ ^ 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hn2]; norm_num
  have : (((2 / ‖n‖ ^ 2 : ℝ) : ℂ) * (pairC n v - ((2 / ‖n‖ ^ 2 : ℝ) : ℂ) * pairC n v *
      ((‖n‖ ^ 2 : ℝ) : ℂ))) = -(((2 / ‖n‖ ^ 2 : ℝ) : ℂ) * pairC n v) := by
    linear_combination (-(((2 / ‖n‖ ^ 2 : ℝ) : ℂ) * pairC n v)) * hc
  rw [this, neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- An involution commutes with the Bochner integral (no integrability needed). -/
theorem integral_reflC {α : Type*} [MeasurableSpace α] {μ : Measure α} (n : Space)
    (φ : α → SpaceC) : ∫ x, reflC n (φ x) ∂μ = reflC n (∫ x, φ x ∂μ) := by
  by_cases hφ : Integrable φ μ
  · exact (reflC n).integral_comp_comm hφ
  · have h : ¬Integrable (fun x => reflC n (φ x)) μ := fun h => hφ (by
      simpa [reflC_reflC] using (reflC n).integrable_comp h)
    rw [integral_undef h, integral_undef hφ, map_zero]

theorem unitRC_eq (y : Space) : unitRC y = ofRealVec (unitR y) := by
  ext i
  fin_cases i <;> simp [unitRC, unitR, EuclideanSpace.single_apply]

theorem unitZC_eq : unitZC = ofRealVec unitZ := by
  ext i
  fin_cases i <;> simp [unitZC, unitZ, EuclideanSpace.single_apply]

/-- The meridional frame is equivariant under the reflections fixing `e₃`. -/
theorem frameC_reflR {n : Space} (hn : n 2 = 0) (y : Space) (v : MeridC) :
    frameC (reflR n y) v = reflC n (frameC y v) := by
  have he3 := reflR_e3 hn
  have hz : reflR n unitZ = unitZ := he3
  rw [frameC_apply, frameC_apply, map_add, map_smul, map_smul, unitRC_eq, unitRC_eq, unitZC_eq,
    reflC_ofRealVec, reflC_ofRealVec, unitR_of_fix he3, hz]

/-! ### Equivariant fields -/

variable {P : ℝ} [Fact (0 < P)]

/-- `u` is equivariant under the reflections of `ℝ³` fixing `e₃` (pointwise, everywhere). -/
def AxEquiv (u : PSpace P → SpaceC) : Prop :=
  ∀ n : Space, n 2 = 0 → ∀ (y : Space) (θ : AddCircle P), u (reflR n y, θ) = reflC n (u (y, θ))

theorem AxEquiv.shift {u : PSpace P → SpaceC} (hu : AxEquiv u) (t : ℝ) :
    AxEquiv fun w : PSpace P => u (w.1, w.2 - (t : AddCircle P)) :=
  fun n hn y θ => hu n hn y _

theorem AxEquiv.dil {u : PSpace P → SpaceC} (hu : AxEquiv u) (k a : ℝ) :
    AxEquiv fun z : PSpace P => k • u (a • z.1, z.2) := by
  intro n hn y θ
  simp only
  rw [← map_smul, hu n hn (a • y) θ, ← ContinuousLinearMap.map_smul_of_tower]

theorem heatConv_axEquiv {u : PSpace P → SpaceC} (hu : AxEquiv u) (θ : ℝ) :
    AxEquiv (Heat.heatConv (ιx P) θ u) := by
  intro n hn x φ
  set g := reflR n
  have hmp := g.measurePreserving
  have hemb := g.toHomeomorph.measurableEmbedding
  simp only [Heat.heatConv, ιx_apply, Prod.mk_sub_mk, sub_zero]
  rw [← hmp.integral_comp hemb, ← integral_reflC]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [show (g w : Euc 3) = g w from rfl, Gaussian.gaussKernel_isometry g θ w, ← map_sub,
    hu n hn, ContinuousLinearMap.map_smul_of_tower]

/-- The meridional lift representative is equivariant. -/
theorem liftVecRep_axEquiv {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (b : Profile → MeridC) : AxEquiv ((liftVecWC hε hc hP).compFun b) := by
  intro n hn y θ
  have he3 := reflR_e3 hn
  change (jConst ε * liftA (reflR n y)) • frameC (reflR n y)
      (b (cellChart ε c (reflR n y, (toCell P (reflR n y, θ)).2))) =
    reflC n ((jConst ε * liftA y) • frameC y (b (cellChart ε c (y, (toCell P (y, θ)).2))))
  have hτ : (toCell P (reflR n y, θ)).2 = (toCell P (y, θ)).2 := rfl
  rw [hτ, cellChart_congr (radius_of_fix he3 y) (two_of_fix he3 y), liftA, liftA,
    radius_of_fix he3 y, frameC_reflR hn, ContinuousLinearMap.map_smul_of_tower]

/-- At `(r, 0, z)` an equivariant vector has no second component. -/
theorem AxEquiv.apply_one {u : PSpace P → SpaceC} (hu : AxEquiv u) (r w : ℝ)
    (θ : AddCircle P) : u (axisVec r w, θ) 1 = 0 := by
  have hn : (EuclideanSpace.single 1 (1 : ℝ) : Space) 2 = 0 := by
    simp [EuclideanSpace.single_apply]
  have hfix : reflR (EuclideanSpace.single 1 1) (axisVec r w) = axisVec r w := by
    refine Submodule.reflection_mem_subspace_eq_self ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, EuclideanSpace.inner_single_right]
    simp [(axisVec_apply r w).2.1]
  have h := hu _ hn (axisVec r w) θ
  rw [hfix] at h
  have h1 := congrArg (fun v : SpaceC => v 1) h
  simp only [reflC_apply, PiLp.sub_apply, PiLp.smul_apply, ofRealVec_apply, smul_eq_mul,
    pairC, Fin.sum_univ_three] at h1
  simp at h1
  linear_combination h1 / 2

/-! ### Fields of `(r, z, τ)` in the meridional frame are lifts -/

variable {ε c : ℝ}

/-- **An `L²` field equal a.e. to `B_r(r, z, τ) e_r + B_z(r, z, τ) e_z`, `B` measurable, is a
meridional lift** `J_ε b` (the complex periodic analogue of B0220 `range_J`). -/
theorem exists_liftVec_eq (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    {B : ℝ × ℝ × ℝ → MeridC} (hB : Measurable B) {F : X SpaceC P}
    (hF : (F : PSpace P → SpaceC) =ᵐ[volume]
      fun z => frameC z.1 (B (radius z.1, z.1 2, (toCell P z).2))) :
    ∃ b : HSpace c MeridC, liftVec hε hc hP b = F := by
  set W := liftVecWC hε hc hP with hW
  set b₀ : Profile → MeridC := fun p =>
    (√(2 * Real.pi) * ε * invR p) • B (invR p, invZ ε p, invTau ε c p) with hb₀
  have hb₀m : Measurable b₀ :=
    (measurable_invR.const_mul _).smul
      (hB.comp (measurable_invR.prodMk ((measurable_invZ ε).prodMk (measurable_invTau ε c))))
  have hpt : W.compFun b₀ =ᵐ[volume]
      fun z => frameC z.1 (B (radius z.1, z.1 2, (toCell P z).2)) := by
    filter_upwards [ae_offAxis hP] with z ⟨hr, hτ⟩
    obtain ⟨h1, h2, h3⟩ := invChart hε hc hr hτ
    have hk : (jConst ε * liftA z.1) * (√(2 * Real.pi) * ε * radius (toCell P z).1) = 1 := by
      have hr' : radius z.1 ≠ 0 := hr
      have : √(2 * Real.pi) ≠ 0 := by positivity
      change (jConst ε * liftA z.1) * (√(2 * Real.pi) * ε * radius z.1) = 1
      simp only [jConst, liftA]
      field_simp
    simp only [WeightedComp.compFun, hW, liftVecWC, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply, hb₀]
    rw [h1, h2, h3, LinearMap.map_smul_of_tower, smul_smul, hk, one_smul]
    rfl
  have hb₀L : MemLp b₀ 2 (measureH c) :=
    ⟨hb₀m.aestronglyMeasurable, by
      rw [← W.eLpNorm_compFun hb₀m, eLpNorm_congr_ae (hpt.trans hF.symm)]
      exact Lp.eLpNorm_lt_top F⟩
  refine ⟨hb₀L.toLp b₀, Lp.ext ?_⟩
  exact (W.coeFn_toLI_toLp hb₀L).trans (hpt.trans hF.symm)

/-- An equivariant field is, off the axis, `R₀(r, 0, z) e_r(x) + R₂(r, 0, z) e_z`. -/
theorem AxEquiv.eq_frame {u : PSpace P → SpaceC} (hu : AxEquiv u) {x : Space}
    (hx : radius x ≠ 0) (θ : AddCircle P) :
    u (x, θ) = frameC x ((u (axisPt x, θ) 0) • EuclideanSpace.single 0 1 +
      (u (axisPt x, θ) 2) • EuclideanSpace.single 1 1) := by
  have hn : (axisPt x - x) 2 = 0 := by simp [axisPt_two]
  have h0 : frameC (axisPt x) ((u (axisPt x, θ) 0) • EuclideanSpace.single 0 1 +
      (u (axisPt x, θ) 2) • EuclideanSpace.single 1 1) = u (axisPt x, θ) := by
    have h1 := hu.apply_one (radius x) (x 2) θ
    have hr : 0 < radius x := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hx)
    obtain ⟨a0, a1, a2⟩ := axisVec_apply (radius x) (x 2)
    have hR : radius (axisPt x) = radius x := radius_axisPt x
    ext i
    fin_cases i
    · have hR' : radius (axisVec (radius x) (x 2)) = radius x := hR
      simp [frameC_apply, unitRC, unitZC, axisPt, a0, a1]
      rw [hR', div_self (Complex.ofReal_ne_zero.mpr hx), mul_one]
    · simp [frameC_apply, unitRC, unitZC, EuclideanSpace.single_apply, axisPt, a1]
      exact h1.symm
    · simp [frameC_apply, unitRC, unitZC, EuclideanSpace.single_apply]
  conv_lhs => rw [← rotTo_axisPt x, rotTo_eq_reflR, hu _ hn, ← h0]
  rw [← frameC_reflR hn, ← rotTo_eq_reflR, rotTo_axisPt]

/-! ### The invariance -/

/-- **`S_ε(t)` maps meridional lifts to meridional lifts**: `LiftInvariant` for the outer
semigroup on `ℂ³`-valued fields and the meridional lift, `h > 0`, `ε, c > 0`, `P = 2εc`. -/
theorem liftInvariant_vec {h : ℝ} (hh : 0 < h) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) :
    LiftInvariant (outerSemigroup (E := SpaceC) (P := P) h hh.le) (liftVec hε hc hP) := by
  intro t ht b
  rcases ht.eq_or_lt with h0 | ht'
  · refine ⟨b, ?_⟩
    rw [← h0, outerSemigroup_T, Sop_zero]
    rfl
  obtain ⟨Jrep, hJrep⟩ : ∃ f : PSpace P → SpaceC,
      f = (liftVecWC hε hc hP).compFun (b : Profile → MeridC) := ⟨_, rfl⟩
  have hJ : (liftVec hε hc hP b : PSpace P → SpaceC) =ᵐ[volume] Jrep := by
    rw [hJrep]; exact (liftVecWC hε hc hP).coeFn_toLI b
  have hrep := Sop_rep' hh ht' hJ
  obtain ⟨U, hUdef⟩ : ∃ U : PSpace P → SpaceC,
      U = fun w => Jrep (w.1, w.2 - (t : AddCircle P)) := ⟨_, rfl⟩
  have hUeq : AxEquiv U := by
    rw [hUdef, hJrep]; exact (liftVecRep_axEquiv hε hc hP _).shift t
  have hUm : Measurable U := by
    rw [hUdef, hJrep]
    exact ((liftVecWC hε hc hP).measurable_compFun (Lp.stronglyMeasurable b).measurable).comp
      (measurable_fst.prodMk (measurable_snd.sub_const _))
  obtain ⟨R, hRdef⟩ : ∃ R : PSpace P → SpaceC, R = fun z => Real.exp (t / 2) •
      Heat.heatConv (ιx P) (h * (Real.exp t - 1)) U (Real.exp (t / 2) • z.1, z.2) := ⟨_, rfl⟩
  have hReq : AxEquiv R := by
    rw [hRdef]; exact (heatConv_axEquiv hUeq _).dil _ _
  have hRm : Measurable R := by
    have hm1 : Measurable fun z : PSpace P => ((Real.exp (t / 2) • z.1, z.2) : PSpace P) :=
      by fun_prop
    have hm2 : Measurable fun z : PSpace P =>
        Heat.heatConv (ιx P) (h * (Real.exp t - 1)) U (Real.exp (t / 2) • z.1, z.2) :=
      (measurable_heatConv hUm (h * (Real.exp t - 1))).comp hm1
    rw [hRdef]
    exact hm2.const_smul (Real.exp (t / 2))
  have hrep' : ((outerSemigroup (E := SpaceC) (P := P) h hh.le).T t (liftVec hε hc hP b) :
      PSpace P → SpaceC) =ᵐ[volume] R := by
    rw [hRdef, hUdef]; exact hrep
  set Bf : ℝ × ℝ × ℝ → MeridC := fun p =>
    (R (axisVec p.1 p.2.1, (p.2.2 : AddCircle P)) 0) • EuclideanSpace.single 0 1 +
      (R (axisVec p.1 p.2.1, (p.2.2 : AddCircle P)) 2) • EuclideanSpace.single 1 1 with hBf
  have hRc : Measurable fun p : ℝ × ℝ × ℝ => R (axisVec p.1 p.2.1, (p.2.2 : AddCircle P)) :=
    hRm.comp ((continuous_axisVec.measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (AddCircle.measurable_mk'.comp (measurable_snd.comp measurable_snd)))
  have hBm : Measurable Bf :=
    (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 0).measurable.comp hRc).smul_const _).add
      (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 2).measurable.comp hRc).smul_const _)
  have hRB : ∀ᵐ z ∂(volume : Measure (PSpace P)),
      R z = frameC z.1 (Bf (radius z.1, z.1 2, (toCell P z).2)) := by
    filter_upwards [ae_offAxis hP] with z hz
    have hr : radius z.1 ≠ 0 := hz.1
    have hcoe : (((toCell P z).2 : ℝ) : AddCircle P) = z.2 := AddCircle.coe_equivIoc
    simp only [hBf, hcoe]
    exact hReq.eq_frame hr z.2
  obtain ⟨b', hb'⟩ := exists_liftVec_eq hε hc hP hBm (hrep'.trans hRB)
  exact ⟨b', hb'.symm⟩

end UnforcedLeray.B0223
