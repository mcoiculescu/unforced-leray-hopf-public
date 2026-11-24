import UnforcedLeray.Lib.PlanarSectorsB.EulerGroup

/-!
# Frozen heat dilation of the sector generators (INF12 target P7, part 3: B0102)


§5, Level P, target **P7** (`dilation_conj`), and bypass B1 of the note ("the frozen dilation is
a uniformly bounded conjugation on `L²_M`: `‖J_af‖² ≤ a^{M-3}‖f‖²`"); plan `scoping/README.md`
§5, block 2H.

Manuscript (`paper/main.tex`, lines 1569–1580, `eq:st18-t00074`, blueprint unit `B0102`):
`J_af(y) = a⁻²f(y/√a)`, `E_a = J_aE₀`, `V_a(y) = a^{-3/2}V₀(y/√a)`, the frozen generator
`𝓛_af = -V_a·∇f - (Kf)·∇E_a`, and "scaling Biot–Savart gives the exact identity
`𝓛_a = a⁻²J_a𝓛J_a⁻¹`"; "for `a ∈ [1,A]`, `J_a` and its inverse are uniformly bounded".

On the angular sector `w(r)e^{inϑ}` the dilation acts on the profile only,
`(J_aw)(r) = a⁻²w(r/√a)`. Since `V_a(y) = a⁻²Ω(|y|/√a)y^⊥` (`frozenVelocity_eq`) and
`E_a'(r)/r = a⁻³k(r/√a)` (`frozenK_eq`), the frozen generator on sector `n` is
`w ↦ -in a⁻²Ω(r/√a) w + i n a⁻³ k(r/√a) Δ_{|n|}⁻¹w` (the same computation as for `Lsec`,
`Sector.lean`, with `Ω, k` replaced by their frozen versions). This module defines it by that
formula (`LsecDil`, `coeFn_LsecDil`) and proves the conjugacy on every sector.

Main declarations (namespace `UnforcedLeray.Planar`):
* `dilFun a w r = a⁻²w(r/√a)`, `dilP hM ha : ProfL2 M →L[ℂ] ProfL2 M` (`coeFn_dilP`),
  `norm_sq_dilP_le` (`‖J_aw‖² ≤ a⁻³ max(1,a)^M ‖w‖²`), `norm_dilP_le_of_one_le`
  (`‖J_a‖ ≤ a^{(M-3)/2}` for `a ≥ 1`), `norm_dilP_inv_le_of_one_le` (`‖J_a⁻¹‖ ≤ a^{3/2}`),
  `dilP_comp` (`J_aJ_b = J_{ab}`), `dilP_one`, `dilUnit` (`J_a` as a unit, inverse `J_{a⁻¹}`);
* `greenN_comp_mul`: Biot–Savart (Green) scaling `Δ_n⁻¹[w(c·)](r) = c⁻²(Δ_n⁻¹w)(cr)`;
* `frozenK_eq`, `frozenVelocity_eq`: the coefficients of the frozen generator;
* `LsecDil hM ha n` (the frozen sector generator, defined by its formula `lsecDilFun`) and
  **`dilation_conj_sec`**: `LsecDil hM ha n = a⁻² • (J_a ∘ Lsec hM n ∘ J_a⁻¹)`;
  `LsecDil_one`: `𝓛_1 = 𝓛`;
* `exp_LsecDil`: `exp(t𝓛_{a,n}) = J_a exp((t/a²)𝓛ₙ) J_a⁻¹`; `norm_exp_LsecDil_le` and the
  uniform form `norm_exp_LsecDil_le_uniform` (`a ∈ [1,A]`: `≤ A^{M/2} e^{|t|B_M}`).

No junk value enters a statement: every dilation carries `0 < a`, so `√a > 0` and `r/√a` is a
genuine division.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK radialVorticity radialOmega_pos)

/-! ### The dilation of profiles -/

/-- The frozen heat dilation of a radial profile, `(J_aw)(r) = a⁻²w(r/√a)` (`paper/main.tex`
line 1571, unit `B0102`, on the sector `w(r)e^{inϑ}`). -/
def dilFun (a : ℝ) (w : ℝ → ℂ) (r : ℝ) : ℂ := (((a ^ 2)⁻¹ : ℝ) : ℂ) * w (r / √a)

theorem qmp_div_sqrt_restrict {a : ℝ} (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (fun r : ℝ => r / √a)
      (volume.restrict (Ioi 0)) (volume.restrict (Ioi 0)) := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have h1 : Measure.QuasiMeasurePreserving (fun r : ℝ => (√a)⁻¹ • r) volume volume :=
    Measure.quasiMeasurePreserving_smul (μ := volume) (inv_ne_zero hs.ne')
  have h2 := h1.restrict (s := Ioi (0 : ℝ)) (t := Ioi (0 : ℝ)) (fun r hr => by
    simp only [mem_Ioi, smul_eq_mul] at hr ⊢
    positivity)
  have e : (fun r : ℝ => r / √a) = fun r : ℝ => (√a)⁻¹ • r := by
    funext r
    rw [smul_eq_mul, div_eq_inv_mul]
  rw [e]
  exact h2

/-- `r ↦ r/√a` is quasi-measure-preserving for the profile measure. -/
theorem qmp_div_sqrt {M a : ℝ} (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (fun r : ℝ => r / √a) (profileMeasure M) (profileMeasure M) :=
  (qmp_div_sqrt_restrict ha).mono (profileMeasure_ac M) (ac_profileMeasure M)

theorem aestronglyMeasurable_dilFun {M a : ℝ} (ha : 0 < a) {w : ℝ → ℂ}
    (hw : AEStronglyMeasurable w (profileMeasure M)) :
    AEStronglyMeasurable (dilFun a w) (profileMeasure M) :=
  aestronglyMeasurable_const.mul (hw.comp_quasiMeasurePreserving (qmp_div_sqrt ha))

/-- Almost everywhere, `w(r/√a) = v(r/√a)` when `w = v` almost everywhere. -/
theorem ae_comp_div_sqrt {M a : ℝ} (ha : 0 < a) {w v : ℝ → ℂ} (h : w =ᵐ[profileMeasure M] v) :
    ∀ᵐ r ∂profileMeasure M, w (r / √a) = v (r / √a) := by
  filter_upwards [(qmp_div_sqrt ha).ae_eq_comp h] with r hr
  simpa only [Function.comp_apply] using hr

theorem dilFun_congr {M a : ℝ} (ha : 0 < a) {w v : ℝ → ℂ} (h : w =ᵐ[profileMeasure M] v) :
    dilFun a w =ᵐ[profileMeasure M] dilFun a v := by
  filter_upwards [ae_comp_div_sqrt ha h] with r hr
  simp only [dilFun, hr]

theorem norm_sq_dilFun (a : ℝ) (w : ℝ → ℂ) (r : ℝ) :
    ‖dilFun a w r‖ ^ 2 = (a ^ 4)⁻¹ * ‖w (r / √a)‖ ^ 2 := by
  rw [dilFun, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  rw [inv_pow, ← pow_mul]

/-- `(1 + a x²)^M ≤ max(1,a)^M (1 + x²)^M` for `M ≥ 0`, `a ≥ 0`. -/
theorem one_add_mul_sq_rpow_le {M a : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (x : ℝ) :
    (1 + a * x ^ 2) ^ M ≤ max 1 a ^ M * (1 + x ^ 2) ^ M := by
  have h1 : (1 : ℝ) ≤ max 1 a := le_max_left _ _
  have h2 : a ≤ max 1 a := le_max_right _ _
  rw [← Real.mul_rpow (zero_le_one.trans h1) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ hM
  have h3 : a * x ^ 2 ≤ max 1 a * x ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg x)
  nlinarith

/-- **Change of variables** `r = √a s` in the profile norm (no integrability hypothesis: both
sides are Bochner integrals related by `integral_comp_mul_left_Ioi`). -/
theorem integral_dilFun_sq {a : ℝ} (ha : 0 < a) (M : ℝ) (w : ℝ → ℂ) :
    ∫ s in Ioi (0 : ℝ), ‖dilFun a w s‖ ^ 2 * (1 + s ^ 2) ^ M * s =
      (a ^ 3)⁻¹ * ∫ x in Ioi (0 : ℝ), ‖w x‖ ^ 2 * (1 + a * x ^ 2) ^ M * x := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have h := integral_comp_mul_left_Ioi (fun s => ‖dilFun a w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) 0 hs
  rw [mul_zero] at h
  have e : (fun x : ℝ => ‖dilFun a w (√a * x)‖ ^ 2 * (1 + (√a * x) ^ 2) ^ M * (√a * x)) =
      fun x => √a * (a ^ 4)⁻¹ * (‖w x‖ ^ 2 * (1 + a * x ^ 2) ^ M * x) := by
    funext x
    rw [norm_sq_dilFun, mul_div_cancel_left₀ x hs.ne', mul_pow, Real.sq_sqrt ha.le]
    ring
  rw [e, integral_const_mul, smul_eq_mul] at h
  set I := ∫ x in Ioi (0 : ℝ), ‖w x‖ ^ 2 * (1 + a * x ^ 2) ^ M * x
  set J := ∫ s in Ioi (0 : ℝ), ‖dilFun a w s‖ ^ 2 * (1 + s ^ 2) ^ M * s
  have h' : J = √a * (√a * (a ^ 4)⁻¹ * I) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [h', ← mul_assoc, ← mul_assoc, Real.mul_self_sqrt ha.le]
  congr 1
  field_simp

theorem integrableOn_profile_sq {M : ℝ} {w : ℝ → ℂ} (hw : MemLp w 2 (profileMeasure M)) :
    IntegrableOn (fun s => ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) (Ioi 0) := by
  have h := (memLp_profile_iff ((aestronglyMeasurable_profileMeasure_iff M).1 hw.1)).1 hw
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  ring

theorem norm_sq_profile {M : ℝ} (w : ProfL2 M) :
    ‖w‖ ^ 2 = 2 * π * ∫ s in Ioi (0 : ℝ), ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s := by
  rw [norm_sq_Lp_eq_integral, integral_sq_profileMeasure]

theorem memLp_dilFun {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) {w : ℝ → ℂ}
    (hw : MemLp w 2 (profileMeasure M)) : MemLp (dilFun a w) 2 (profileMeasure M) := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have hm := aestronglyMeasurable_dilFun ha hw.1
  rw [memLp_profile_iff ((aestronglyMeasurable_profileMeasure_iff M).1 hm)]
  have key := integrableOn_Ioi_comp_mul_left_iff
    (fun s => ‖dilFun a w s‖ ^ 2 * (s * (1 + s ^ 2) ^ M)) 0 hs
  rw [mul_zero] at key
  refine key.1 ?_
  have e : (fun x : ℝ => ‖dilFun a w (√a * x)‖ ^ 2 * (√a * x * (1 + (√a * x) ^ 2) ^ M)) =
      fun x => √a * (a ^ 4)⁻¹ * (‖w x‖ ^ 2 * (1 + a * x ^ 2) ^ M * x) := by
    funext x
    rw [norm_sq_dilFun, mul_div_cancel_left₀ x hs.ne', mul_pow, Real.sq_sqrt ha.le]
    ring
  rw [e]
  refine Integrable.const_mul ?_ _
  have hw' := integrableOn_profile_sq hw
  have hwm : AEStronglyMeasurable w (volume.restrict (Ioi 0)) :=
    (aestronglyMeasurable_profileMeasure_iff M).1 hw.1
  refine (hw'.const_mul (max 1 a ^ M)).mono' ?_ ?_
  · refine ((hwm.norm.pow 2).mul ?_).mul continuous_id.aestronglyMeasurable
    exact (Continuous.rpow_const (by fun_prop) fun x => Or.inl (by positivity)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : (0 : ℝ) < x := hx
    have hb := one_add_mul_sq_rpow_le (M := M) (by linarith) ha.le x
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖w x‖ ^ 2 * (1 + a * x ^ 2) ^ M * x
        ≤ ‖w x‖ ^ 2 * (max 1 a ^ M * (1 + x ^ 2) ^ M) * x := by gcongr
      _ = max 1 a ^ M * (‖w x‖ ^ 2 * (1 + x ^ 2) ^ M * x) := by ring

/-- The dilation as a linear map of `ProfL2 M`. -/
def dilLin {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) : ProfL2 M →ₗ[ℂ] ProfL2 M where
  toFun w := (memLp_dilFun hM ha (Lp.memLp w)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [dilFun_congr ha (Lp.coeFn_add f g)] with r hr
    rw [hr]
    simp only [dilFun, Pi.add_apply]
    ring
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [dilFun_congr ha (Lp.coeFn_smul c f)] with r hr
    rw [hr]
    simp only [dilFun, Pi.smul_apply, smul_eq_mul]
    ring

theorem norm_sq_dilLin_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (w : ProfL2 M) :
    ‖dilLin hM ha w‖ ^ 2 ≤ (a ^ 3)⁻¹ * max 1 a ^ M * ‖w‖ ^ 2 := by
  have h1 : ‖dilLin hM ha w‖ ^ 2 =
      2 * π * ((a ^ 3)⁻¹ * ∫ x in Ioi (0 : ℝ), ‖w x‖ ^ 2 * (1 + a * x ^ 2) ^ M * x) := by
    rw [norm_sq_Lp_eq_integral, ← integral_dilFun_sq ha M w, ← integral_sq_profileMeasure]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_dilFun hM ha (Lp.memLp w)).coeFn_toLp] with r hr
    show ‖((memLp_dilFun hM ha (Lp.memLp w)).toLp _ : ProfL2 M) r‖ ^ 2 = _
    rw [hr]
  have h2 : ∫ x in Ioi (0 : ℝ), ‖w x‖ ^ 2 * (1 + a * x ^ 2) ^ M * x ≤
      max 1 a ^ M * ∫ x in Ioi (0 : ℝ), ‖w x‖ ^ 2 * (1 + x ^ 2) ^ M * x := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ((integrableOn_profile_sq (Lp.memLp w)).const_mul _) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : (0 : ℝ) < x := hx
      positivity
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : (0 : ℝ) < x := hx
      have hb := one_add_mul_sq_rpow_le (M := M) (by linarith) ha.le x
      calc ‖w x‖ ^ 2 * (1 + a * x ^ 2) ^ M * x
          ≤ ‖w x‖ ^ 2 * (max 1 a ^ M * (1 + x ^ 2) ^ M) * x := by gcongr
        _ = max 1 a ^ M * (‖w x‖ ^ 2 * (1 + x ^ 2) ^ M * x) := by ring
  rw [h1, norm_sq_profile]
  have hpi : 0 ≤ 2 * π := by positivity
  have ha3 : 0 ≤ (a ^ 3)⁻¹ := by positivity
  calc 2 * π * ((a ^ 3)⁻¹ * ∫ x in Ioi (0 : ℝ), ‖w x‖ ^ 2 * (1 + a * x ^ 2) ^ M * x)
      ≤ 2 * π * ((a ^ 3)⁻¹ *
          (max 1 a ^ M * ∫ x in Ioi (0 : ℝ), ‖w x‖ ^ 2 * (1 + x ^ 2) ^ M * x)) := by
        gcongr
    _ = (a ^ 3)⁻¹ * max 1 a ^ M *
          (2 * π * ∫ s in Ioi (0 : ℝ), ‖w s‖ ^ 2 * (1 + s ^ 2) ^ M * s) := by ring

/-- The norm constant `√(a⁻³ max(1,a)^M)` of the dilation. -/
def dilConst (M a : ℝ) : ℝ := √((a ^ 3)⁻¹ * max 1 a ^ M)

theorem dilConst_nonneg (M a : ℝ) : 0 ≤ dilConst M a := Real.sqrt_nonneg _

theorem norm_dilLin_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (w : ProfL2 M) :
    ‖dilLin hM ha w‖ ≤ dilConst M a * ‖w‖ := by
  have hK : 0 ≤ (a ^ 3)⁻¹ * max 1 a ^ M := by
    have : (0 : ℝ) ≤ max 1 a := zero_le_one.trans (le_max_left _ _)
    positivity
  rw [← Real.sqrt_sq (norm_nonneg (dilLin hM ha w)), dilConst,
    ← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul hK]
  exact Real.sqrt_le_sqrt (norm_sq_dilLin_le hM ha w)

/-- **The frozen heat dilation** `J_a` on `ProfL2 M`, `(J_aw)(r) = a⁻²w(r/√a)` (`paper/main.tex`
line 1571, unit `B0102`). -/
def dilP {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) : ProfL2 M →L[ℂ] ProfL2 M :=
  (dilLin hM ha).mkContinuous (dilConst M a) (norm_dilLin_le hM ha)

theorem coeFn_dilP {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (w : ProfL2 M) :
    ⇑(dilP hM ha w) =ᵐ[profileMeasure M] dilFun a w :=
  (memLp_dilFun hM ha (Lp.memLp w)).coeFn_toLp

theorem norm_sq_dilP_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (w : ProfL2 M) :
    ‖dilP hM ha w‖ ^ 2 ≤ (a ^ 3)⁻¹ * max 1 a ^ M * ‖w‖ ^ 2 :=
  norm_sq_dilLin_le hM ha w

theorem norm_dilP_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    ‖dilP hM ha‖ ≤ dilConst M a :=
  LinearMap.mkContinuous_norm_le _ (dilConst_nonneg M a) _

theorem dilConst_of_one_le {M a : ℝ} (ha : 1 ≤ a) : dilConst M a = a ^ ((M - 3) / 2) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  rw [dilConst, max_eq_right ha, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg ha0.le,
    ← Real.rpow_add ha0, ← Real.rpow_mul ha0.le]
  congr 1
  push_cast
  ring

theorem dilConst_inv_of_one_le {M a : ℝ} (ha : 1 ≤ a) : dilConst M a⁻¹ = a ^ (3 / 2 : ℝ) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have h1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
  rw [dilConst, max_eq_left h1, Real.one_rpow, mul_one, inv_pow, inv_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
  norm_num

/-- **`‖J_a‖ ≤ a^{(M-3)/2}` for `a ≥ 1`** (`paper/main.tex` line 1580; scoping note §4, B1). -/
theorem norm_dilP_le_of_one_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 1 ≤ a) :
    ‖dilP hM (zero_lt_one.trans_le ha)‖ ≤ a ^ ((M - 3) / 2) :=
  (norm_dilP_le hM _).trans (le_of_eq (dilConst_of_one_le ha))

/-- **`‖J_a⁻¹‖ = ‖J_{a⁻¹}‖ ≤ a^{3/2}` for `a ≥ 1`**. -/
theorem norm_dilP_inv_le_of_one_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 1 ≤ a) :
    ‖dilP hM (inv_pos.2 (zero_lt_one.trans_le ha))‖ ≤ a ^ (3 / 2 : ℝ) :=
  (norm_dilP_le hM _).trans (le_of_eq (dilConst_inv_of_one_le ha))

theorem dilP_congr {M : ℝ} (hM : 1 < M) {a b : ℝ} (h : a = b) (ha : 0 < a) (hb : 0 < b) :
    dilP (M := M) hM ha = dilP hM hb := by
  subst h
  rfl

/-- `J_aJ_b = J_{ab}`. -/
theorem dilP_comp {M : ℝ} (hM : 1 < M) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    dilP hM ha ∘L dilP hM hb = dilP (M := M) hM (mul_pos ha hb) := by
  ext1 w
  apply Lp.ext
  filter_upwards [coeFn_dilP hM ha (dilP hM hb w), dilFun_congr ha (coeFn_dilP hM hb w),
    coeFn_dilP hM (mul_pos ha hb) w] with r h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, h1, h2, h3]
  have e : r / √a / √b = r / √(a * b) := by rw [div_div, Real.sqrt_mul ha.le]
  simp only [dilFun]
  rw [e]
  push_cast
  ring

/-- `J_1 = 1`. -/
theorem dilP_one {M : ℝ} (hM : 1 < M) : dilP (M := M) hM one_pos = 1 := by
  ext1 w
  apply Lp.ext
  filter_upwards [coeFn_dilP hM one_pos w] with r h1
  rw [h1]
  simp [dilFun]

theorem dilP_mul_inv {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    dilP hM ha * dilP (M := M) hM (inv_pos.2 ha) = 1 := by
  rw [ContinuousLinearMap.mul_def, dilP_comp,
    dilP_congr hM (mul_inv_cancel₀ ha.ne') _ one_pos, dilP_one]

theorem dilP_inv_mul {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    dilP (M := M) hM (inv_pos.2 ha) * dilP hM ha = 1 := by
  rw [ContinuousLinearMap.mul_def, dilP_comp,
    dilP_congr hM (inv_mul_cancel₀ ha.ne') _ one_pos, dilP_one]

/-- `J_a` as a unit of the operator algebra, with inverse `J_{a⁻¹}`. -/
def dilUnit {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) : (ProfL2 M →L[ℂ] ProfL2 M)ˣ where
  val := dilP hM ha
  inv := dilP hM (inv_pos.2 ha)
  val_inv := dilP_mul_inv hM ha
  inv_val := dilP_inv_mul hM ha

/-! ### Green (Biot–Savart) scaling and the frozen coefficients -/

theorem minmax_mul_left {c r ρ : ℝ} (hc : 0 < c) :
    min (c * r) (c * ρ) / max (c * r) (c * ρ) = min r ρ / max r ρ := by
  rw [← mul_min_of_nonneg _ _ hc.le, ← mul_max_of_nonneg _ _ hc.le, mul_div_mul_left _ _ hc.ne']

/-- **Scaling of the Green inverse** (Biot–Savart scaling, `paper/main.tex` line 1574):
`Δ_n⁻¹[w(c·)](r) = c⁻²(Δ_n⁻¹w)(cr)` for `c > 0` (no integrability hypothesis). -/
theorem greenN_comp_mul (n : ℕ) (w : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (r : ℝ) :
    greenN n (fun s => w (c * s)) r = (((c ^ 2)⁻¹ : ℝ) : ℂ) * greenN n w (c * r) := by
  unfold greenN
  set F : ℝ → ℂ := fun x => (((min (c * r) x / max (c * r) x) ^ n : ℝ) : ℂ) * w x * (x : ℂ)
  have e : (fun ρ : ℝ => (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * w (c * ρ) * (ρ : ℂ)) =
      fun ρ => ((c⁻¹ : ℝ) : ℂ) * F (c * ρ) := by
    funext ρ
    simp only [F]
    rw [minmax_mul_left hc]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    push_cast
    field_simp
  have h := integral_comp_mul_left_Ioi F 0 hc
  rw [mul_zero] at h
  rw [e, integral_const_mul, h, Complex.real_smul]
  push_cast
  ring

/-- `Δ_n⁻¹(cw) = cΔ_n⁻¹w` pointwise, for any function (no integrability hypothesis). -/
theorem greenN_const_mul (n : ℕ) (c : ℂ) (w : ℝ → ℂ) (r : ℝ) :
    greenN n (fun s => c * w s) r = c * greenN n w r := by
  unfold greenN
  have e : (fun ρ : ℝ => (((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * (c * w ρ) * (ρ : ℂ)) =
      fun ρ => c * ((((min r ρ / max r ρ) ^ n : ℝ) : ℂ) * w ρ * (ρ : ℂ)) := by
    funext ρ
    ring
  rw [e, integral_const_mul]
  ring

/-- The frozen vorticity `E_a = J_aE₀` has `E_a'(r)/r = a⁻³k(r/√a)` (`paper/main.tex` lines
1571 and 647, `k = E₀'/r`). -/
theorem frozenK_eq {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r ≠ 0) :
    deriv (fun ρ => (a ^ 2)⁻¹ * radialVorticity (ρ / √a)) r / r =
      (a ^ 3)⁻¹ * radialK (r / √a) := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have hd : HasDerivAt (fun ρ => (a ^ 2)⁻¹ * radialVorticity (ρ / √a))
      ((a ^ 2)⁻¹ * ((r / √a * radialK (r / √a)) * (1 / √a))) r := by
    have h1 : HasDerivAt (fun ρ : ℝ => ρ / √a) (1 / √a) r := (hasDerivAt_id r).div_const _
    exact ((GaussianVortex.hasDerivAt_radialVorticity (r / √a)).comp r h1).const_mul _
  rw [hd.deriv]
  have hsq : √a * √a = a := Real.mul_self_sqrt ha.le
  have e : r / √a * radialK (r / √a) * (1 / √a) = r * radialK (r / √a) / (√a * √a) := by
    field_simp
  rw [e, hsq]
  field_simp

/-- The frozen velocity `V_a(y) = a^{-3/2}V₀(y/√a)`, `V₀(y) = Ω(|y|)y^⊥` (`y^⊥ = iy` in `ℂ`),
is the rotation `V_a(y) = a⁻²Ω(|y|/√a) y^⊥` (`paper/main.tex` lines 638 and 1572). -/
theorem frozenVelocity_eq {a : ℝ} (ha : 0 < a) (y : ℂ) :
    ((a * √a)⁻¹ : ℝ) • ((radialOmega ‖(√a)⁻¹ • y‖ : ℝ) • (Complex.I * ((√a)⁻¹ • y))) =
      ((a ^ 2)⁻¹ * radialOmega (‖y‖ / √a) : ℝ) • (Complex.I * y) := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have hsq : √a * √a = a := Real.mul_self_sqrt ha.le
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_eq_div]
  set s := √a with hs_def
  rw [← hsq]
  simp only [Complex.real_smul]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp

/-! ### The frozen sector generator and the conjugacy -/

/-- The frozen sector generator on profiles,
`w ↦ -in a⁻²Ω(r/√a) w + i n a⁻³k(r/√a) Δ_{|n|}⁻¹w`: the generator `-V_a·∇ - (K·)·∇E_a` of
`paper/main.tex` line 1572 on `w(r)e^{inϑ}` (compare `coeFn_Lsec`, with the frozen coefficients
of `frozenVelocity_eq` and `frozenK_eq`). -/
def lsecDilFun (a : ℝ) (n : ℤ) (w : ℝ → ℂ) (r : ℝ) : ℂ :=
  -(Complex.I * n) * (((a ^ 2)⁻¹ * radialOmega (r / √a) : ℝ) : ℂ) * w r +
    Complex.I * n * (((a ^ 3)⁻¹ * radialK (r / √a) : ℝ) : ℂ) * greenN n.natAbs w r

/-- The conjugated operator `a⁻²J_a𝓛ₙJ_a⁻¹`. -/
def conjSec {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) : ProfL2 M →L[ℂ] ProfL2 M :=
  (((a ^ 2)⁻¹ : ℝ) : ℂ) • (dilP hM ha ∘L Lsec hM n ∘L dilP hM (inv_pos.2 ha))

theorem dilFun_inv_eq (a : ℝ) (w : ℝ → ℂ) :
    dilFun a⁻¹ w = fun s => ((a ^ 2 : ℝ) : ℂ) * w (√a * s) := by
  funext s
  rw [dilFun, Real.sqrt_inv, div_inv_eq_mul, inv_pow, inv_inv, mul_comm s]

/-- **The sector conjugacy, pointwise**: `a⁻²J_a𝓛ₙJ_a⁻¹w` is the frozen generator applied to
`w`, almost everywhere. -/
theorem coeFn_conjSec {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) (w : ProfL2 M) :
    ⇑(conjSec hM ha n w) =ᵐ[profileMeasure M] lsecDilFun a n w := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have ha' : 0 < a⁻¹ := inv_pos.2 ha
  set v := dilP hM ha' w with hv
  set u := Lsec hM n v with hu
  have e0 : conjSec hM ha n w = (((a ^ 2)⁻¹ : ℝ) : ℂ) • dilP hM ha u := rfl
  -- the greenN term of `v`
  have hg : ∀ ρ, greenN n.natAbs v ρ =
      ((a ^ 2 : ℝ) : ℂ) * ((((√a) ^ 2)⁻¹ : ℝ) : ℂ) * greenN n.natAbs w (√a * ρ) := by
    intro ρ
    rw [greenN_congr n.natAbs (coeFn_dilP hM ha' w) ρ, dilFun_inv_eq a,
      greenN_const_mul n.natAbs _ (fun s => w (√a * s)), greenN_comp_mul n.natAbs w hs, mul_assoc]
  rw [e0]
  filter_upwards [Lp.coeFn_smul (((a ^ 2)⁻¹ : ℝ) : ℂ) (dilP hM ha u), coeFn_dilP hM ha u,
    dilFun_congr ha (coeFn_Lsec hM n v), ae_comp_div_sqrt ha (coeFn_dilP hM ha' w)]
    with r h1 h2 h3 h4
  rw [h1, Pi.smul_apply, h2, h3, smul_eq_mul]
  simp only [dilFun] at h4 ⊢
  rw [h4, hg, Real.sqrt_inv, div_inv_eq_mul, div_mul_cancel₀ r hs.ne',
    mul_div_cancel₀ r hs.ne', Real.sq_sqrt ha.le, lsecDilFun]
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp

theorem memLp_lsecDilFun {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) (w : ProfL2 M) :
    MemLp (lsecDilFun a n w) 2 (profileMeasure M) :=
  (Lp.memLp (conjSec hM ha n w)).ae_eq (coeFn_conjSec hM ha n w)

theorem toLp_lsecDilFun_eq {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) (w : ProfL2 M) :
    (memLp_lsecDilFun hM ha n w).toLp _ = conjSec hM ha n w := by
  apply Lp.ext
  filter_upwards [(memLp_lsecDilFun hM ha n w).coeFn_toLp, coeFn_conjSec hM ha n w]
    with r h1 h2
  rw [h1, h2]

/-- The frozen sector generator as a linear map (defined by the formula `lsecDilFun`). -/
def LsecDilLin {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) : ProfL2 M →ₗ[ℂ] ProfL2 M where
  toFun w := (memLp_lsecDilFun hM ha n w).toLp _
  map_add' f g := by
    change (memLp_lsecDilFun hM ha n (f + g)).toLp _ =
      (memLp_lsecDilFun hM ha n f).toLp _ + (memLp_lsecDilFun hM ha n g).toLp _
    rw [toLp_lsecDilFun_eq hM ha n, toLp_lsecDilFun_eq hM ha n, toLp_lsecDilFun_eq hM ha n,
      map_add]
  map_smul' c f := by
    change (memLp_lsecDilFun hM ha n (c • f)).toLp _ = c • (memLp_lsecDilFun hM ha n f).toLp _
    rw [toLp_lsecDilFun_eq hM ha n, toLp_lsecDilFun_eq hM ha n, map_smul]

/-- **The frozen sector generator** `𝓛_{a,n}` on `ProfL2 M` (`paper/main.tex` line 1572 on the
sector `w(r)e^{inϑ}`): the bounded operator acting by `lsecDilFun a n` (`coeFn_LsecDil`). -/
def LsecDil {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) : ProfL2 M →L[ℂ] ProfL2 M :=
  (LsecDilLin hM ha n).mkContinuous ‖conjSec hM ha n‖ fun w => by
    show ‖(memLp_lsecDilFun hM ha n w).toLp _‖ ≤ _
    rw [toLp_lsecDilFun_eq]
    exact (conjSec hM ha n).le_opNorm w

theorem coeFn_LsecDil {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) (w : ProfL2 M) :
    ⇑(LsecDil hM ha n w) =ᵐ[profileMeasure M] fun r =>
      -(Complex.I * n) * (((a ^ 2)⁻¹ * radialOmega (r / √a) : ℝ) : ℂ) * w r +
        Complex.I * n * (((a ^ 3)⁻¹ * radialK (r / √a) : ℝ) : ℂ) * greenN n.natAbs w r :=
  (memLp_lsecDilFun hM ha n w).coeFn_toLp

/-- **P7, dilation conjugacy on every sector** (`eq:st18-t00074`, `paper/main.tex` lines
1574–1578, unit `B0102`): `𝓛_{a,n} = a⁻² J_a 𝓛ₙ J_a⁻¹`, where `J_a⁻¹ = J_{a⁻¹}`
(`dilUnit`). -/
theorem dilation_conj_sec {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) :
    LsecDil hM ha n =
      (((a ^ 2)⁻¹ : ℝ) : ℂ) • (dilP hM ha ∘L Lsec hM n ∘L dilP hM (inv_pos.2 ha)) := by
  ext1 w
  exact toLp_lsecDilFun_eq hM ha n w

/-- At `a = 1` the frozen generator is `𝓛ₙ`. -/
theorem LsecDil_one {M : ℝ} (hM : 1 < M) (n : ℤ) : LsecDil hM one_pos n = Lsec hM n := by
  rw [dilation_conj_sec, dilP_congr hM inv_one (inv_pos.2 one_pos) one_pos, dilP_one]
  ext1 w
  simp

/-! ### The frozen sector exponentials -/

/-- Conjugation by a unit commutes with the exponential in the Banach algebra of operators
(Mathlib's `NormedSpace.exp_units_conj` over `ℂ` instead of `ℚ`). -/
theorem exp_units_conj_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (U : (E →L[ℂ] E)ˣ) (x : E →L[ℂ] E) :
    NormedSpace.exp ((U : E →L[ℂ] E) * x * ↑U⁻¹) = U * NormedSpace.exp x * ↑U⁻¹ := by
  have hx : x ∈ Metric.eball (0 : E →L[ℂ] E) (NormedSpace.expSeries ℂ (E →L[ℂ] E)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  set f := MulSemiringAction.toRingHom (ConjAct (E →L[ℂ] E)ˣ) (E →L[ℂ] E)
    (ConjAct.toConjAct U) with hf
  have hf_apply : ∀ y, f y = (U : E →L[ℂ] E) * y * ↑U⁻¹ := fun y => by
    rw [hf, MulSemiringAction.toRingHom_apply, ConjAct.units_smul_def,
      ConjAct.ofConjAct_toConjAct]
  have hfc : Continuous f := by
    have e : (f : (E →L[ℂ] E) → (E →L[ℂ] E)) = fun y => (U : E →L[ℂ] E) * y * ↑U⁻¹ :=
      funext hf_apply
    rw [e]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) f hfc x hx
  rw [hf_apply, hf_apply] at h
  exact h.symm

/-- **Conjugacy of the sector evolutions**: `exp(t𝓛_{a,n}) = J_a exp((t/a²)𝓛ₙ) J_a⁻¹`. -/
theorem exp_LsecDil {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • LsecDil hM ha n) =
      dilP hM ha ∘L expSec hM (t / a ^ 2) n ∘L dilP hM (inv_pos.2 ha) := by
  have e : (t : ℂ) • LsecDil hM ha n =
      (dilUnit hM ha : ProfL2 M →L[ℂ] ProfL2 M) * (((t / a ^ 2 : ℝ) : ℂ) • Lsec hM n) *
        ((dilUnit hM ha)⁻¹ : (ProfL2 M →L[ℂ] ProfL2 M)ˣ) := by
    rw [dilation_conj_sec, smul_smul, mul_smul_comm, smul_mul_assoc]
    congr 1
    · push_cast
      ring
  rw [e, exp_units_conj_clm]
  rfl

theorem norm_exp_LsecDil_le {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (n : ℤ) (t : ℝ) :
    ‖NormedSpace.exp ((t : ℂ) • LsecDil hM ha n)‖ ≤
      dilConst M a * dilConst M a⁻¹ * Real.exp (|t / a ^ 2| * lsecBound hM) := by
  rw [exp_LsecDil]
  calc ‖dilP hM ha ∘L expSec hM (t / a ^ 2) n ∘L dilP hM (inv_pos.2 ha)‖
      ≤ ‖dilP hM ha‖ * (‖expSec hM (t / a ^ 2) n‖ * ‖dilP hM (inv_pos.2 ha)‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ dilConst M a * (Real.exp (|t / a ^ 2| * lsecBound hM) * dilConst M a⁻¹) :=
        mul_le_mul (norm_dilP_le hM ha)
          (mul_le_mul (norm_expSec_le hM _ n) (norm_dilP_le hM _) (norm_nonneg _)
            (Real.exp_pos _).le)
          (by positivity) (dilConst_nonneg M a)
    _ = dilConst M a * dilConst M a⁻¹ * Real.exp (|t / a ^ 2| * lsecBound hM) := by ring

/-- **Uniformity for `a ∈ [1,A]`** (`paper/main.tex` line 1580): `‖J_a‖‖J_a⁻¹‖ ≤ a^{M/2}`. -/
theorem dilConst_mul_inv_le {M a A : ℝ} (hM : 1 < M) (ha : 1 ≤ a) (haA : a ≤ A) :
    dilConst M a * dilConst M a⁻¹ ≤ A ^ (M / 2) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  rw [dilConst_of_one_le ha, dilConst_inv_of_one_le ha, ← Real.rpow_add ha0]
  have e : (M - 3) / 2 + 3 / 2 = M / 2 := by ring
  rw [e]
  exact Real.rpow_le_rpow ha0.le haA (by linarith)

/-- **Uniform frozen sector bounds for `a ∈ [1,A]`**:
`‖exp(t𝓛_{a,n})‖ ≤ A^{M/2} e^{|t| B_M}`, uniformly in `a ∈ [1,A]`, `n ∈ ℤ`, `t ∈ ℝ`. -/
theorem norm_exp_LsecDil_le_uniform {M : ℝ} (hM : 1 < M) {a A : ℝ} (ha : 1 ≤ a) (haA : a ≤ A)
    (n : ℤ) (t : ℝ) :
    ‖NormedSpace.exp ((t : ℂ) • LsecDil hM (zero_lt_one.trans_le ha) n)‖ ≤
      A ^ (M / 2) * Real.exp (|t| * lsecBound hM) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  refine (norm_exp_LsecDil_le hM ha0 n t).trans ?_
  have hB := lsecBound_nonneg hM
  have h1 : |t / a ^ 2| ≤ |t| := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < a ^ 2)]
    exact div_le_self (abs_nonneg t) (one_le_pow₀ ha)
  exact mul_le_mul (dilConst_mul_inv_le hM ha haA)
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h1 hB)) (Real.exp_pos _).le
    (Real.rpow_nonneg (by linarith) _)

end UnforcedLeray.Planar
