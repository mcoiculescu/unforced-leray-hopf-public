import UnforcedLeray.Units.B0224.PlaneSymm

/-!
# B0224 helper: the cylinder heat with an age-dependent time, on `H`

Blueprint unit B0224 (label `eq:st18-t00117`), `paper/main.tex` lines 3370–3379. On
`H = L²(s^{-3/2} ds dq dη)` (B0220, `HSpace`, tex lines 3305–3308) the semigroup `T_0(t)` applies
the cylinder heat `e^{θΔ_{q,η}}` at every age `s`, with a heat time `θ(s)` that depends on `s`
(`θ(s) = νs(1 - e^{-t})`). For a measurable `θ : ℝ → ℝ` this file builds

  `(H_θ F)(s, q, η) = (e^{θ(s)Δ_{q,η}} F(s, ·))(q, η)`   (`fiberHeat`, the `c`-periodic extension
  of `F(s, ·)` in `q` is used, B0220 `periodize`)

and proves that it is a self-adjoint contraction of `H` (`heatH`, `norm_heatH_le`,
`isSelfAdjoint_heatH`). The heat acts at fixed `s`, so the weight `s^{-3/2}` plays no role:

* contraction: Jensen `|e^{θΔ}F|² ≤ e^{θΔ}|F|²` pointwise and conservation of the strip mass
  (`lintegral_measureH_fiberAbs`);
* self-adjointness: Fubini in `(s, (q, η))` and the symmetry of the heat on each fibre
  (`integral_strip_inner_planeHeat`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.B0224

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0220

/-! ### Measurability -/

theorem measurable_gaussKernel_two : Measurable fun q : ℝ × Euc 2 => gaussKernel 2 q.1 q.2 := by
  unfold gaussKernel
  exact ((measurable_const.mul measurable_fst).pow_const _).mul
    (Real.measurable_exp.comp ((measurable_snd.norm.pow_const 2).neg.div
      (measurable_const.mul measurable_fst)))

/-- The map `(s, q, η) ↦ (s, q reduced into (0, c], η)`. -/
theorem measurable_reducePt (c : ℝ) :
    Measurable fun p : Profile => ((p.1, reduceIoc c p.2.1, p.2.2) : Profile) :=
  measurable_fst.prodMk (((measurable_reduceIoc c).comp (measurable_fst.comp
    measurable_snd)).prodMk (measurable_snd.comp measurable_snd))

theorem stronglyMeasurable_periodize {E : Type*} [TopologicalSpace E] {c : ℝ} {F : Profile → E}
    (hF : StronglyMeasurable F) : StronglyMeasurable (periodize c F) :=
  hF.comp_measurable (measurable_reducePt c)

theorem measurable_periodize' {c : ℝ} {Φ : Profile → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable (periodize c Φ) :=
  hΦ.comp (measurable_reducePt c)

/-- The fibre `z ↦ F̃(s, z)` of the periodic extension is `c`-periodic in `q`. -/
theorem isPeriodic_periodize_slice {E : Type*} {c : ℝ} (hc : 0 < c) (F : Profile → E) (s : ℝ) :
    Cyl.IsPeriodic c (fun z : ℝ × ℝ => periodize c F (s, z)) := by
  intro z
  simp only [periodize, reduceIoc_add hc]

theorem periodize_slice_of_mem {E : Type*} {c : ℝ} (hc : 0 < c) (F : Profile → E) (s : ℝ)
    {z : ℝ × ℝ} (hz : z ∈ strip c) : periodize c F (s, z) = F (s, z) := by
  simp only [periodize, reduceIoc_of_mem hc hz.1]

/-! ### The fibre heat and its majorant -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cylinder heat at the age-dependent time `θ(s)`, fibre by fibre:
`(H_θ F)(s, z) = e^{θ(s)Δ}[F̃(s, ·)](z)`, `F̃` the `c`-periodic extension in `q`. -/
def fiberHeat (c : ℝ) (θ : ℝ → ℝ) (F : Profile → E) (p : Profile) : E :=
  planeHeat (θ p.1) (fun z => periodize c F (p.1, z)) p.2

/-- The `[0, ∞]`-valued majorant: `e^{θ(s)Δ}` applied to a nonnegative function. -/
def fiberAbs (c : ℝ) (θ : ℝ → ℝ) (Φ : Profile → ℝ≥0∞) (p : Profile) : ℝ≥0∞ :=
  if 0 < θ p.1 then
    ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 (θ p.1) y) * periodize c Φ (p.1, p.2 - planeι y)
  else periodize c Φ p

variable {c : ℝ} {θ : ℝ → ℝ}

theorem fiberHeat_of_pos (F : Profile → E) {p : Profile} (h : 0 < θ p.1) :
    fiberHeat c θ F p =
      ∫ y : Euc 2, gaussKernel 2 (θ p.1) y • periodize c F (p.1, p.2 - planeι y) :=
  planeHeat_of_pos h _ _

theorem fiberHeat_of_nonpos (F : Profile → E) {p : Profile} (h : θ p.1 ≤ 0) :
    fiberHeat c θ F p = periodize c F p := by
  simp only [fiberHeat, planeHeat_of_nonpos h]

theorem fiberHeat_eq_ite (F : Profile → E) :
    fiberHeat c θ F = fun p => if 0 < θ p.1 then
      ∫ y : Euc 2, gaussKernel 2 (θ p.1) y • periodize c F (p.1, p.2 - planeι y)
      else periodize c F p := by
  funext p
  by_cases h : 0 < θ p.1
  · simp only [fiberHeat_of_pos F h, h, ↓reduceIte]
  · simp only [fiberHeat_of_nonpos F (not_lt.1 h), h, ↓reduceIte]

theorem fiberHeat_smul (r : ℝ) (F : Profile → E) :
    fiberHeat c θ (fun p => r • F p) = fun p => r • fiberHeat c θ F p := by
  funext p
  exact congrFun (planeHeat_smul (θ p.1) r (fun z => periodize c F (p.1, z))) p.2

theorem stronglyMeasurable_fiberHeat (hθ : Measurable θ) {F : Profile → E}
    (hF : StronglyMeasurable F) : StronglyMeasurable (fiberHeat c θ F) := by
  rw [fiberHeat_eq_ite]
  refine StronglyMeasurable.ite (measurableSet_lt measurable_const (hθ.comp measurable_fst))
    ?_ (stronglyMeasurable_periodize hF)
  refine StronglyMeasurable.integral_prod_right' (f := fun q : Profile × Euc 2 =>
    gaussKernel 2 (θ q.1.1) q.2 • periodize c F (q.1.1, q.1.2 - planeι q.2)) ?_
  refine (measurable_gaussKernel_two.comp ((hθ.comp (measurable_fst.comp measurable_fst)).prodMk
    measurable_snd)).stronglyMeasurable.smul ?_
  exact (stronglyMeasurable_periodize hF).comp_measurable
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub (measurable_planeι.comp measurable_snd)))

theorem measurable_fiberAbs (hθ : Measurable θ) {Φ : Profile → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable (fiberAbs c θ Φ) := by
  unfold fiberAbs
  refine Measurable.ite (measurableSet_lt measurable_const (hθ.comp measurable_fst)) ?_
    (measurable_periodize' hΦ)
  refine Measurable.lintegral_prod_right' (f := fun q : Profile × Euc 2 =>
    ENNReal.ofReal (gaussKernel 2 (θ q.1.1) q.2) * periodize c Φ (q.1.1, q.1.2 - planeι q.2)) ?_
  refine (ENNReal.measurable_ofReal.comp (measurable_gaussKernel_two.comp
    ((hθ.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))).mul ?_
  exact (measurable_periodize' hΦ).comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).sub (measurable_planeι.comp measurable_snd)))

/-- Jensen's inequality fibre by fibre: `|H_θ F|² ≤ H_θ |F|²`. -/
theorem enorm_fiberHeat_sq_le {F : Profile → E} (hF : StronglyMeasurable F) (p : Profile) :
    ‖fiberHeat c θ F p‖ₑ ^ 2 ≤ fiberAbs c θ (fun p => ‖F p‖ₑ ^ 2) p := by
  by_cases h : 0 < θ p.1
  · rw [fiberHeat_of_pos F h]
    simp only [fiberAbs, h, ↓reduceIte]
    exact enorm_integral_gauss_sq_le h ((stronglyMeasurable_periodize hF).comp_measurable
      (measurable_const.prodMk (measurable_const.sub measurable_planeι))).aestronglyMeasurable
  · rw [fiberHeat_of_nonpos F (not_lt.1 h)]
    simp only [fiberAbs, h, ↓reduceIte]
    rfl

end Defs

/-! ### Conservation of mass and the contraction -/

section Mass

variable {c : ℝ} {θ : ℝ → ℝ}

theorem cellMeasure_eq_prod' (c : ℝ) :
    cellMeasure c = (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (strip c)) := by
  rw [strip, Measure.prod_restrict]
  rfl

/-- The heat preserves the mass of every fibre, against any weight in `s`:
`∫_cell ψ(s) H_θΦ = ∫_cell ψ(s) Φ`. -/
theorem lintegral_cell_fiberAbs (hc : 0 < c) (hθ : Measurable θ) {Φ : Profile → ℝ≥0∞}
    (hΦ : Measurable Φ) {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ p, ψ p.1 * fiberAbs c θ Φ p ∂cellMeasure c = ∫⁻ p, ψ p.1 * Φ p ∂cellMeasure c := by
  rw [cellMeasure_eq_prod',
    lintegral_prod (fun p : Profile => ψ p.1 * fiberAbs c θ Φ p)
      ((hψ.comp measurable_fst).mul (measurable_fiberAbs hθ hΦ)).aemeasurable,
    lintegral_prod (fun p : Profile => ψ p.1 * Φ p)
      ((hψ.comp measurable_fst).mul hΦ).aemeasurable]
  refine lintegral_congr fun s => ?_
  have hm1 : Measurable fun x : ℝ × ℝ => fiberAbs c θ Φ (s, x) :=
    (measurable_fiberAbs hθ hΦ).comp measurable_prodMk_left
  have hm2 : Measurable fun x : ℝ × ℝ => Φ (s, x) := hΦ.comp measurable_prodMk_left
  dsimp only
  rw [lintegral_const_mul _ hm1, lintegral_const_mul _ hm2]
  congr 1
  have hslice : ∫⁻ x in strip c, periodize c Φ (s, x) = ∫⁻ x in strip c, Φ (s, x) :=
    setLIntegral_congr_fun (measurableSet_strip c) fun x hx => periodize_slice_of_mem hc Φ s hx
  by_cases h : 0 < θ s
  · simp only [fiberAbs, h, ↓reduceIte]
    rw [lintegral_strip_gauss (φ := fun z => periodize c Φ (s, z)) hc h
      ((measurable_periodize' hΦ).comp measurable_prodMk_left)
      (isPeriodic_periodize_slice hc Φ s)]
    exact hslice
  · simp only [fiberAbs, h, ↓reduceIte]
    exact hslice

theorem lintegral_measureH_eq (Φ : Profile → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ p, Φ p ∂measureH c = ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * Φ p ∂cellMeasure c :=
  lintegral_withDensity_eq_lintegral_mul _ measurable_weightH hΦ

/-- Conservation of mass in `H`: `∫ H_θΦ dH = ∫ Φ dH`. -/
theorem lintegral_measureH_fiberAbs (hc : 0 < c) (hθ : Measurable θ) {Φ : Profile → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ p, fiberAbs c θ Φ p ∂measureH c = ∫⁻ p, Φ p ∂measureH c := by
  rw [lintegral_measureH_eq _ (measurable_fiberAbs hθ hΦ), lintegral_measureH_eq _ hΦ]
  exact lintegral_cell_fiberAbs hc hθ hΦ
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lintegral_fiberHeat_sq_le (hc : 0 < c) (hθ : Measurable θ) {F : Profile → E}
    (hF : StronglyMeasurable F) :
    ∫⁻ p, ‖fiberHeat c θ F p‖ₑ ^ 2 ∂measureH c ≤ ∫⁻ p, ‖F p‖ₑ ^ 2 ∂measureH c :=
  (lintegral_mono fun p => enorm_fiberHeat_sq_le hF p).trans
    (le_of_eq (lintegral_measureH_fiberAbs hc hθ (hF.enorm.pow_const 2)))

theorem eLpNorm_two_eq (μ : Measure Profile) (F : Profile → E) :
    eLpNorm F 2 μ = (∫⁻ p, ‖F p‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- The heat is a contraction of `H`. -/
theorem eLpNorm_fiberHeat_le (hc : 0 < c) (hθ : Measurable θ) {F : Profile → E}
    (hF : StronglyMeasurable F) :
    eLpNorm (fiberHeat c θ F) 2 (measureH c) ≤ eLpNorm F 2 (measureH c) := by
  rw [eLpNorm_two_eq, eLpNorm_two_eq]
  exact ENNReal.rpow_le_rpow (lintegral_fiberHeat_sq_le hc hθ hF) (by norm_num)

theorem lintegral_sq_lt_top (f : HSpace c E) : ∫⁻ p, ‖f p‖ₑ ^ 2 ∂measureH c < ∞ := by
  have h := (Lp.memLp f).2
  rw [eLpNorm_two_eq] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h

end Mass

/-! ### Congruence and linearity -/

section Linear

variable {c : ℝ} {θ : ℝ → ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fiberHeat_congr_ae (hc : 0 < c) (hθ : Measurable θ) {F G : Profile → E}
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G) (h : F =ᵐ[measureH c] G) :
    fiberHeat c θ F =ᵐ[measureH c] fiberHeat c θ G := by
  set Φ : Profile → ℝ≥0∞ := fun p => ‖F p - G p‖ₑ with hΦ
  have hΦm : Measurable Φ := (hF.sub hG).enorm
  have h0 : ∫⁻ p, Φ p ∂measureH c = 0 := by
    rw [lintegral_eq_zero_iff hΦm]
    filter_upwards [h] with p hp
    simp [hΦ, hp]
  have h1 : ∫⁻ p, fiberAbs c θ Φ p ∂measureH c = 0 := by
    rw [lintegral_measureH_fiberAbs hc hθ hΦm, h0]
  rw [lintegral_eq_zero_iff (measurable_fiberAbs hθ hΦm)] at h1
  filter_upwards [h1] with p hp
  by_cases hθp : 0 < θ p.1
  · simp only [fiberAbs, hθp, ↓reduceIte, Pi.zero_apply] at hp
    have hmy : Measurable fun y : Euc 2 =>
        ENNReal.ofReal (gaussKernel 2 (θ p.1) y) * periodize c Φ (p.1, p.2 - planeι y) :=
      (measurable_ofReal_gauss _).mul ((measurable_periodize' hΦm).comp
        (measurable_const.prodMk (measurable_const.sub measurable_planeι)))
    rw [lintegral_eq_zero_iff hmy] at hp
    rw [fiberHeat_of_pos F hθp, fiberHeat_of_pos G hθp]
    refine integral_congr_ae ?_
    filter_upwards [hp] with y hy
    have hGy : ENNReal.ofReal (gaussKernel 2 (θ p.1) y) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Gaussian.gaussKernel_pos hθp y)).ne'
    have h2 := (mul_eq_zero.1 hy).resolve_left hGy
    simp only [periodize, hΦ, enorm_eq_zero, sub_eq_zero] at h2
    simp only [periodize, h2]
  · simp only [fiberAbs, hθp, ↓reduceIte, Pi.zero_apply] at hp
    rw [fiberHeat_of_nonpos F (not_lt.1 hθp), fiberHeat_of_nonpos G (not_lt.1 hθp)]
    simp only [periodize, hΦ, enorm_eq_zero, sub_eq_zero] at hp ⊢
    exact hp

theorem fiberHeat_add_ae (hc : 0 < c) (hθ : Measurable θ) {F G : Profile → E}
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (hF2 : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂measureH c < ∞) (hG2 : ∫⁻ p, ‖G p‖ₑ ^ 2 ∂measureH c < ∞) :
    fiberHeat c θ (fun p => F p + G p) =ᵐ[measureH c]
      fun p => fiberHeat c θ F p + fiberHeat c θ G p := by
  have hfin : ∀ {K : Profile → E}, StronglyMeasurable K →
      ∫⁻ p, ‖K p‖ₑ ^ 2 ∂measureH c < ∞ →
      ∀ᵐ p ∂measureH c, fiberAbs c θ (fun p => ‖K p‖ₑ ^ 2) p < ∞ := by
    intro K hK hK2
    refine ae_lt_top (measurable_fiberAbs hθ (hK.enorm.pow_const 2)) ?_
    rw [lintegral_measureH_fiberAbs hc hθ (hK.enorm.pow_const 2)]
    exact hK2.ne
  filter_upwards [hfin hF hF2, hfin hG hG2] with p hpF hpG
  by_cases hθp : 0 < θ p.1
  · simp only [fiberAbs, hθp, ↓reduceIte] at hpF hpG
    have hsm : ∀ {K : Profile → E}, StronglyMeasurable K →
        AEStronglyMeasurable fun y : Euc 2 => periodize c K (p.1, p.2 - planeι y) :=
      fun hK => ((stronglyMeasurable_periodize hK).comp_measurable
        (measurable_const.prodMk (measurable_const.sub measurable_planeι))).aestronglyMeasurable
    have iF : Integrable fun y : Euc 2 =>
        gaussKernel 2 (θ p.1) y • periodize c F (p.1, p.2 - planeι y) :=
      integrable_gauss_smul hθp (hsm hF) hpF
    have iG : Integrable fun y : Euc 2 =>
        gaussKernel 2 (θ p.1) y • periodize c G (p.1, p.2 - planeι y) :=
      integrable_gauss_smul hθp (hsm hG) hpG
    rw [fiberHeat_of_pos _ hθp, fiberHeat_of_pos _ hθp, fiberHeat_of_pos _ hθp,
      ← integral_add iF iG]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [periodize, smul_add]
  · rw [fiberHeat_of_nonpos _ (not_lt.1 hθp), fiberHeat_of_nonpos _ (not_lt.1 hθp),
      fiberHeat_of_nonpos _ (not_lt.1 hθp)]
    simp only [periodize]

end Linear

/-! ### The operator on `H` -/

section Operator

variable {c : ℝ} {θ : ℝ → ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem memLp_fiberHeat (hc : 0 < c) (hθ : Measurable θ) (f : HSpace c E) :
    MemLp (fiberHeat c θ f) 2 (measureH c) :=
  ⟨(stronglyMeasurable_fiberHeat hθ (Lp.stronglyMeasurable f)).aestronglyMeasurable,
    (eLpNorm_fiberHeat_le hc hθ (Lp.stronglyMeasurable f)).trans_lt (Lp.memLp f).2⟩

/-- The cylinder heat `H_θ` at the age-dependent time `θ(s)` as a bounded operator on
`H = L²(s^{-3/2} ds dq dη)` (`θ` measurable). -/
def heatH (hc : 0 < c) (hθ : Measurable θ) : HSpace c E →L[ℝ] HSpace c E :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_fiberHeat hc hθ f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        refine (fiberHeat_congr_ae hc hθ (Lp.stronglyMeasurable _)
          ((Lp.stronglyMeasurable f).add (Lp.stronglyMeasurable g)) (Lp.coeFn_add f g)).trans ?_
        exact fiberHeat_add_ae hc hθ (Lp.stronglyMeasurable f) (Lp.stronglyMeasurable g)
          (lintegral_sq_lt_top f) (lintegral_sq_lt_top g)
      map_smul' := fun r f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        refine (fiberHeat_congr_ae hc hθ (Lp.stronglyMeasurable _)
          ((Lp.stronglyMeasurable f).const_smul r) (Lp.coeFn_smul r f)).trans ?_
        exact Eventually.of_forall fun p => congrFun (fiberHeat_smul r (f : Profile → E)) p }
    1 (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_fiberHeat_le hc hθ (Lp.stronglyMeasurable f)))

theorem coeFn_heatH (hc : 0 < c) (hθ : Measurable θ) (f : HSpace c E) :
    heatH hc hθ f =ᵐ[measureH c] fiberHeat c θ f :=
  MemLp.coeFn_toLp (memLp_fiberHeat hc hθ f)

theorem norm_heatH_le (hc : 0 < c) (hθ : Measurable θ) :
    ‖(heatH hc hθ : HSpace c E →L[ℝ] HSpace c E)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Operator

end UnforcedLeray.B0224
