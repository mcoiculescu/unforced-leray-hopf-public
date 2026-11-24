import UnforcedLeray.Units.B0583.TestModes
import UnforcedLeray.Units.B0582

/-!
# B0583 helper: the zero-mode velocity `(-∫_{-∞}^η ω̄, 0)`

Blueprint unit **B0583** (`prepared:p1.4`), `paper/main.tex` lines 9412–9433: "For `k = 0`, the
velocity is a primitive of `ω̄(η)`. Its limits at both ends are zero by zero total circulation.
The one-dimensional Hardy inequality gives (`prepared:p1.3`) ... The gradient is bounded ...".

For `ω ∈ X_m` (`B0579.X c m`, `paper/main.tex:9373`) we set

* `omegaBar c ω η = ω̄(η) = c⁻¹ ∫_{-c/2}^{c/2} ω(q, η) dq`, the horizontal mean (line 9409);
* `zeroVel c ω = (-F(η), 0)` with `F = ∫_{-∞}^η ω̄` (`B0582.zeroModePrimitive`): the
  Biot–Savart velocity `∇^⊥Δ^{-1}` of the zero mode, `∇^⊥ = (-∂_η, ∂_q)` (`paper/main.tex:2138`);
* `zeroVelEta c ω = (-ω̄(η), 0)`, its `η`-derivative (its `q`-derivative is `0`).

Main facts (for `m ≥ 1`, and `m > 1` with zero total circulation where needed):

* `lintegral_weighted_omegaBar_le`: `‖⟨η⟩ ω̄‖²_{L²(ℝ)} ≤ c⁻¹ ‖ω‖²_{X_m}` (Cauchy–Schwarz in `q`);
* `integrable_of_X`: `m ≥ 1` (in particular the manuscript's `m > 1`) makes `ω ∈ L¹(cell)`, so
  the total circulation `∫_cell ω` is a genuine integral; `integral_omegaBar_eq_zero`:
  `∫ ω̄ = c⁻¹ ∫_cell ω = 0`;
* (in `B0583/ZeroVel.lean`) `norm_zeroVelLp_le`: `‖(F, 0)‖_{L²(cell)} ≤ 2 ‖ω‖_{X_m}` (Hardy,
  `B0582.hardy_zero_mode`), and `norm_zeroVelEtaLp_le`: `‖(ω̄, 0)‖_{L²(cell)} ≤ ‖ω‖_{X_m}`;
* the distributional identities `integral_pd0_mul_prof` (`∫_cell ∂_qφ · h(η) = 0`) and
  `integral_pd1_mul_primitive` (`∫_cell ∂_ηφ · F(η) = -∫_cell φ · ω̄(η)`), the latter from the
  one-dimensional identity `integral_deriv_mul_primitive` (Fubini).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex Topology
open scoped ENNReal NNReal InnerProductSpace Real ComplexConjugate

namespace UnforcedLeray.B0583

open B0581

/-! ### Generalities on the cell -/

theorem setIntegral_qInt_real {c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℝ) :
    ∫ q in qInt c, f q = ∫ q in (-(c / 2))..(c / 2), f q := by
  rw [intervalIntegral.integral_of_le (by linarith), qInt, integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]

theorem μq_univ {c : ℝ} (_hc : 0 ≤ c) : μq c univ = ENNReal.ofReal c := by
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, qInt, Real.volume_Ico]
  congr 1
  ring

theorem eLpNorm_two_eq' {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  simp_rw [ENNReal.rpow_two]

/-- A function of `η` alone on the cell: `‖h(η)‖_{L²(cell)} = √c ‖h‖_{L²(ℝ)}`. -/
theorem eLpNorm_comp_snd_cell {c : ℝ} (hc : 0 ≤ c) {E : Type} [NormedAddCommGroup E]
    {h : ℝ → E} (hh : AEStronglyMeasurable h volume) :
    eLpNorm (fun x : B0579.Plane => h x.2) 2 (cellVol c) =
      ENNReal.ofReal c ^ (1 / 2 : ℝ) * eLpNorm h 2 volume := by
  rw [cellVol_eq]
  have hmap : Measure.map Prod.snd ((μq c).prod (volume : Measure ℝ)) =
      (μq c univ) • (volume : Measure ℝ) := Measure.map_snd_prod
  have h1 : AEStronglyMeasurable h (Measure.map Prod.snd ((μq c).prod (volume : Measure ℝ))) := by
    rw [hmap]; exact hh.smul_measure _
  have h2 := eLpNorm_map_measure (p := 2) h1 measurable_snd.aemeasurable
  rw [← show (h ∘ Prod.snd) = (fun x : B0579.Plane => h x.2) from rfl, ← h2, hmap,
    eLpNorm_smul_measure_of_ne_top (by norm_num), μq_univ hc]
  norm_num

/-! ### The horizontal mean `ω̄` -/

/-- **The horizontal mean** `ω̄(η) = c⁻¹ ∫_{-c/2}^{c/2} ω(q, η) dq` (`paper/main.tex:9409`). -/
def omegaBar (c : ℝ) (ω : B0579.Plane → ℝ) (η : ℝ) : ℝ := c⁻¹ * ∫ q in qInt c, ω (q, η)

theorem measurable_omegaBar (c : ℝ) {ω : B0579.Plane → ℝ} (hω : StronglyMeasurable ω) :
    Measurable (omegaBar c ω) := by
  have h : StronglyMeasurable fun η => ∫ q, (fun q η => ω (q, η)) q η ∂μq c :=
    StronglyMeasurable.integral_prod_left (μ := μq c) (f := fun q η => ω (q, η)) hω
  exact h.measurable.const_mul _

/-- `(∫ g)² ≤ μ(univ) ∫ g²` in `[0, ∞]`. -/
theorem sq_lintegral_le {α : Type} [MeasurableSpace α] (μ : Measure α) {g : α → ℝ≥0∞}
    (hg : AEMeasurable g μ) : (∫⁻ x, g x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, g x ^ 2 ∂μ := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := g) aemeasurable_const hg
  simp only [one_mul, ENNReal.one_rpow, lintegral_const] at hH
  have e : (fun x => (1 : ℝ≥0∞) * g x) = g := by funext x; rw [one_mul]
  simp only [Pi.mul_apply] at hH
  calc (∫⁻ x, g x ∂μ) ^ 2 ≤ ((μ univ) ^ (1 / 2 : ℝ) * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' (by simpa [e] using hH) 2
    _ = μ univ * ∫⁻ x, g x ^ 2 ∂μ := by
        rw [B0582.sq_rpow_half_mul]
        simp_rw [ENNReal.rpow_two]

/-- Cauchy–Schwarz in `q`: `|ω̄(η)|² ≤ c⁻¹ ∫ |ω(q, η)|² dq`. -/
theorem enorm_omegaBar_sq_le {c : ℝ} (hc : 0 < c) {ω : B0579.Plane → ℝ}
    (hω : StronglyMeasurable ω) (η : ℝ) :
    ‖omegaBar c ω η‖ₑ ^ 2 ≤ ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ ^ 2 := by
  have hg : AEMeasurable (fun q => ‖ω (q, η)‖ₑ) (μq c) :=
    (hω.measurable.comp (measurable_id.prodMk measurable_const)).enorm.aemeasurable
  have h1 : ‖∫ q in qInt c, ω (q, η)‖ₑ ≤ ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ :=
    enorm_integral_le_lintegral_enorm _
  have h2 := sq_lintegral_le (μq c) hg
  rw [μq_univ hc.le] at h2
  rw [omegaBar, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.mpr hc.le), mul_pow]
  have hcc : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  calc ENNReal.ofReal c⁻¹ ^ 2 * ‖∫ q in qInt c, ω (q, η)‖ₑ ^ 2
      ≤ ENNReal.ofReal c⁻¹ ^ 2 * (ENNReal.ofReal c * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ ^ 2) := by
        gcongr
        exact (pow_le_pow_left' h1 2).trans h2
    _ = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) * ENNReal.ofReal c⁻¹ *
          ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ ^ 2 := by ring
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ ^ 2 := by rw [hcc, one_mul]

theorem one_add_sq_le_jb_rpow {m : ℝ} (hm : 1 ≤ m) (x : B0579.Plane) :
    1 + x.2 ^ 2 ≤ B0579.jb x ^ m := by
  have h1 : 1 ≤ B0579.jb x := by unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  calc 1 + x.2 ^ 2 ≤ B0579.jb x := by unfold B0579.jb; nlinarith [sq_nonneg x.1]
    _ = B0579.jb x ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ B0579.jb x ^ m := Real.rpow_le_rpow_of_exponent_le h1 hm

/-- The squared `X_m` norm as a lintegral over the cell. -/
def wNormSq (c m : ℝ) (ω : B0579.Plane → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ‖B0579.jb x ^ (m / 2) * ω x‖ₑ ^ 2 ∂cellVol c

theorem eLpNorm_X_eq (c m : ℝ) (ω : B0579.Plane → ℝ) :
    eLpNorm ω 2 (B0579.cellMeasure c m) = wNormSq c m ω ^ (1 / 2 : ℝ) := by
  rw [B0579.eLpNorm_cellMeasure, eLpNorm_two_eq', wNormSq]

theorem wNormSq_lt_top {c m : ℝ} (ω : B0579.X c m) : wNormSq c m ω < ∞ := by
  have h := Lp.eLpNorm_lt_top ω
  rw [eLpNorm_X_eq] at h
  have h2 : (wNormSq c m ω ^ (1 / 2 : ℝ)) ^ (2 : ℝ) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne
  rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2

/-- **Weighted bound for the zero mode**: `‖⟨η⟩ ω̄‖²_{L²(ℝ)} ≤ c⁻¹ ‖ω‖²_{X_m}` for `m ≥ 1`. -/
theorem lintegral_weighted_omegaBar_le {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    {ω : B0579.Plane → ℝ} (hω : StronglyMeasurable ω) :
    ∫⁻ η, ‖B0582.jb η * omegaBar c ω η‖ₑ ^ 2 ≤ ENNReal.ofReal c⁻¹ * wNormSq c m ω := by
  have hpt : ∀ η, ‖B0582.jb η * omegaBar c ω η‖ₑ ^ 2 =
      ENNReal.ofReal (1 + η ^ 2) * ‖omegaBar c ω η‖ₑ ^ 2 := by
    intro η
    rw [enorm_mul, mul_pow, Real.enorm_eq_ofReal (B0582.jb_pos η).le, ← ENNReal.ofReal_pow
      (B0582.jb_pos η).le, B0582.jb_sq]
  have hpt2 : ∀ x : B0579.Plane, ENNReal.ofReal (1 + x.2 ^ 2) * ‖ω x‖ₑ ^ 2 ≤
      ‖B0579.jb x ^ (m / 2) * ω x‖ₑ ^ 2 := by
    intro x
    have hj : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
    have key : 1 + x.2 ^ 2 ≤ (B0579.jb x ^ (m / 2)) ^ 2 := by
      rw [sq (B0579.jb x ^ (m / 2)), ← Real.rpow_add (B0579.jb_pos x), add_halves]
      exact one_add_sq_le_jb_rpow hm x
    rw [enorm_mul, mul_pow, Real.enorm_eq_ofReal hj, ← ENNReal.ofReal_pow hj]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal key) _
  simp_rw [hpt]
  calc ∫⁻ η, ENNReal.ofReal (1 + η ^ 2) * ‖omegaBar c ω η‖ₑ ^ 2
      ≤ ∫⁻ η, ENNReal.ofReal (1 + η ^ 2) *
          (ENNReal.ofReal c⁻¹ * ∫⁻ q in qInt c, ‖ω (q, η)‖ₑ ^ 2) := by
        gcongr with η
        exact enorm_omegaBar_sq_le hc hω η
    _ = ∫⁻ η, ENNReal.ofReal c⁻¹ *
          ∫⁻ q in qInt c, ENNReal.ofReal (1 + η ^ 2) * ‖ω (q, η)‖ₑ ^ 2 := by
        congr 1
        funext η
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring
    _ = ENNReal.ofReal c⁻¹ *
          ∫⁻ η, ∫⁻ q in qInt c, ENNReal.ofReal (1 + η ^ 2) * ‖ω (q, η)‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c⁻¹ *
          ∫⁻ η, ∫⁻ q in qInt c, ‖B0579.jb (q, η) ^ (m / 2) * ω (q, η)‖ₑ ^ 2 := by
        gcongr with η q
        exact hpt2 (q, η)
    _ = ENNReal.ofReal c⁻¹ * wNormSq c m ω := by
        congr 1
        rw [wNormSq, cellVol_eq, lintegral_prod_symm]
        exact ((((B0579.continuous_jb_rpow (m / 2)).measurable.mul
          hω.measurable).enorm).pow_const 2).aemeasurable

theorem memLp_weighted_omegaBar {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) (ω : B0579.X c m) :
    MemLp (fun η => B0582.jb η * omegaBar c ω η) 2 volume := by
  refine ⟨(B0582.continuous_jb.measurable.mul
    (measurable_omegaBar c (Lp.stronglyMeasurable ω))).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_two_eq']
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  refine ne_top_of_le_ne_top ?_ (lintegral_weighted_omegaBar_le hc hm (Lp.stronglyMeasurable ω))
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (wNormSq_lt_top ω).ne

/-! ### Integrability and zero circulation -/

/-- `⟨x⟩^{-m} ∈ L²(cell)` for `m ≥ 1`. -/
theorem memLp_bracket_neg {c m : ℝ} (hm : 1 ≤ m) :
    MemLp (fun x => B0579.bracket x ^ (-m)) 2 (cellVol c) := by
  have hcont : Continuous fun x => B0579.bracket x ^ (-m) := B0579.continuous_bracket_rpow (-m)
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  have hint : Integrable (fun x : B0579.Plane => (1 + x.2 ^ 2)⁻¹) (cellVol c) := by
    rw [cellVol_eq]; exact integrable_inv_one_add_sq.comp_snd (μq c)
  refine hint.mono' (hcont.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hj := B0579.jb_pos x
  have h1 : B0579.bracket x ^ (-m) = (B0579.jb x ^ m)⁻¹ ^ (1 / 2 : ℝ) := by
    rw [B0579.bracket_rpow, Real.inv_rpow (Real.rpow_nonneg hj.le _), ← Real.rpow_mul hj.le,
      ← Real.rpow_neg hj.le]
    congr 1; ring
  have hjm : 0 < B0579.jb x ^ m := Real.rpow_pos_of_pos hj m
  rw [Real.norm_eq_abs, abs_pow, h1, abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hjm.le) _),
    ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hjm.le), Nat.cast_ofNat,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
  exact inv_anti₀ (by positivity) (one_add_sq_le_jb_rpow hm x)

/-- For `m ≥ 1` (in particular `m > 1`), `X_m ⊂ L¹(cell)`: the total circulation is a genuine
integral. -/
theorem integrable_of_X {c m : ℝ} (hm : 1 ≤ m) (ω : B0579.X c m) :
    Integrable (ω : B0579.Plane → ℝ) (cellVol c) := by
  have hg : MemLp (fun x => B0579.bracket x ^ m * ω x) 2 (cellVol c) :=
    (B0579.memLp_cellMeasure_iff c m).1 (Lp.memLp ω)
  have h := (memLp_bracket_neg (c := c) hm).integrable_mul hg
  refine h.congr (Eventually.of_forall fun x => ?_)
  have hb := B0579.bracket_rpow_pos m x
  simp only [Pi.mul_apply]
  rw [Real.rpow_neg (show 0 ≤ B0579.bracket x from Real.sqrt_nonneg _), ← mul_assoc,
    inv_mul_cancel₀ hb.ne', one_mul]

/-- **Zero circulation of the zero mode**: `∫ ω̄ = c⁻¹ ∫_cell ω = 0` (`paper/main.tex:9413-9414`). -/
theorem integral_omegaBar_eq_zero {c m : ℝ} (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) : ∫ η, omegaBar c ω η = 0 := by
  have hint := integrable_of_X (c := c) hm ω
  rw [cellVol_eq] at hint
  have h := integral_prod_symm _ hint
  simp only [omegaBar]
  rw [integral_const_mul]
  change c⁻¹ * ∫ η, ∫ q, ω (q, η) ∂μq c = 0
  rw [← h, ← cellVol_eq]
  change c⁻¹ * ∫ x in B0579.cell c, ω x = 0
  rw [hcirc, mul_zero]

/-! ### Fields depending on `η` only -/

/-- The field `(h(η), 0)` on the cell. -/
def profField (h : ℝ → ℝ) (x : B0579.Plane) : Vel :=
  ((h x.2 : ℝ) : ℂ) • EuclideanSpace.single 0 (1 : ℂ)

theorem norm_profField (h : ℝ → ℝ) (x : B0579.Plane) : ‖profField h x‖ = ‖h x.2‖ := by
  simp [profField, norm_smul]

theorem aestronglyMeasurable_profField (c : ℝ) {h : ℝ → ℝ} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (profField h) (cellVol c) := by
  have h1 : AEStronglyMeasurable (fun x : B0579.Plane => h x.2) (cellVol c) := by
    rw [cellVol_eq]; exact hh.comp_snd
  exact (show Continuous fun z : ℝ => ((z : ℂ)) • EuclideanSpace.single (0 : Fin 2) (1 : ℂ) from
    continuous_ofReal.smul continuous_const).comp_aestronglyMeasurable h1

theorem eLpNorm_profField {c : ℝ} (hc : 0 ≤ c) {h : ℝ → ℝ} (hh : AEStronglyMeasurable h volume) :
    eLpNorm (profField h) 2 (cellVol c) = ENNReal.ofReal c ^ (1 / 2 : ℝ) * eLpNorm h 2 volume := by
  rw [← eLpNorm_comp_snd_cell hc hh]
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => norm_profField h x)

theorem memLp_profField (c : ℝ) {h : ℝ → ℝ} (hh : MemLp h 2 volume) :
    MemLp (profField h) 2 (cellVol c) := by
  have h1 : MemLp (fun x : B0579.Plane => h x.2) 2 (cellVol c) := by
    rw [cellVol_eq]; exact hh.comp_snd (μq c)
  exact h1.of_le (aestronglyMeasurable_profField c hh.1)
    (Eventually.of_forall fun x => (norm_profField h x).le)

/-- `⟪ψ e_j, (h(η), 0)⟫ = (∫_cell ψ h(η)) δ_{j0}`. -/
theorem inner_testLp_profField (c : ℝ) {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ)
    (j : Fin 2) {h : ℝ → ℝ} (hh : MemLp h 2 volume) :
    ⟪testLp c hψ j, (memLp_profField c hh).toLp (profField h)⟫_ℂ =
      ((∫ x, ψ x * h x.2 ∂cellVol c : ℝ) : ℂ) * (EuclideanSpace.single 0 (1 : ℂ) : Vel) j := by
  rw [inner_testLp, ← integral_complex_ofReal, ← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_profField c hh)] with x hx
  rw [hx, profField]
  simp only [PiLp.smul_apply, smul_eq_mul]
  push_cast
  ring

/-! ### Distributional identities for the zero mode -/

/-- `∫_cell ∂_q φ · h(η) = 0`: `∫_{-c/2}^{c/2} ∂_q φ dq = 0` by periodicity. -/
theorem integral_pd0_mul_prof {c : ℝ} (hc : 0 < c) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) {h : ℝ → ℝ} (hh : MemLp h 2 volume) :
    ∫ x, B0579.pd 0 φ x * h x.2 ∂cellVol c = 0 := by
  have hh2 : MemLp (fun x : B0579.Plane => h x.2) 2 (cellVol c) := by
    rw [cellVol_eq]; exact hh.comp_snd (μq c)
  have hint : Integrable (fun x => B0579.pd 0 φ x * h x.2) (cellVol c) :=
    (memLp_cellVol_of_isCylTest (hφ.pd 0)).integrable_mul hh2
  rw [integral_cellVol, integral_prod_symm _ (by rwa [← cellVol_eq])]
  have hzero : ∀ η, ∫ q, B0579.pd 0 φ (q, η) * h η ∂μq c = 0 := by
    intro η
    rw [integral_mul_const]
    have hcont : Continuous (B0579.pd 0 φ) := (hφ.pd 0).continuous
    have h0 : ∫ q in qInt c, B0579.pd 0 φ (q, η) = 0 := by
      rw [setIntegral_qInt_real hc.le, intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_pd0 hφ.differentiable x η)
        ((hcont.comp (Continuous.prodMk_left η)).intervalIntegrable _ _)]
      have := hφ.periodic (-(c / 2), η)
      simp only at this
      rw [show -(c / 2) + c = c / 2 by ring] at this
      rw [this, sub_self]
    rw [h0, zero_mul]
  simp only [hzero, integral_zero]

/-- One-dimensional identity: for `w ∈ L¹(ℝ)` and `ψ ∈ C¹_c(ℝ)`,
`∫ ψ'(η) ∫_{-∞}^η w = -∫ ψ w` (Fubini; no differentiability of the primitive is used). -/
theorem integral_deriv_mul_primitive {ψ ψ' : ℝ → ℝ} (hψ : ∀ η, HasDerivAt ψ (ψ' η) η)
    (hψ'c : Continuous ψ') {R : ℝ} (hR : ∀ η, R < |η| → ψ η = 0) {w : ℝ → ℝ}
    (hw : Integrable w) :
    ∫ η, ψ' η * B0582.zeroModePrimitive w η = -∫ y, ψ y * w y := by
  have hR' : ∀ η, R < |η| → ψ' η = 0 := by
    intro η hη
    have hev : ψ =ᶠ[𝓝 η] fun _ => 0 := by
      have hopen : IsOpen {y : ℝ | R < |y|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds hη] with y hy using hR y hy
    exact (hψ η).unique ((hasDerivAt_const η (0 : ℝ)).congr_of_eventuallyEq hev)
  have hcs : HasCompactSupport ψ' := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun η hη => hR' η ?_
    by_contra h
    push Not at h
    exact hη ⟨by linarith [neg_abs_le η], by linarith [le_abs_self η]⟩
  have hψ'int : Integrable ψ' := hψ'c.integrable_of_hasCompactSupport hcs
  -- the integrand of the double integral
  set G : ℝ → ℝ → ℝ := fun η y => ψ' η * (Iic η).indicator w y with hG
  have hGint : Integrable (Function.uncurry G) ((volume : Measure ℝ).prod volume) := by
    have hb : Integrable (fun p : ℝ × ℝ => ψ' p.1 * w p.2) ((volume : Measure ℝ).prod volume) :=
      hψ'int.mul_prod hw
    have hmeas : AEStronglyMeasurable (Function.uncurry G) ((volume : Measure ℝ).prod volume) := by
      have e : Function.uncurry G = fun p : ℝ × ℝ =>
          ψ' p.1 * ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p => w p.2) p) := by
        funext p
        simp only [Function.uncurry, hG, Set.indicator_apply, mem_Iic, Set.mem_ofPred_eq]
      rw [e]
      exact (hψ'c.comp continuous_fst).aestronglyMeasurable.mul
        ((hw.1.comp_snd).indicator (measurableSet_le measurable_snd measurable_fst))
    refine hb.mono hmeas (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hG, norm_mul]
    gcongr
    rw [Set.indicator_apply]
    split_ifs
    · exact le_rfl
    · simp
  have h1 : ∀ η, ψ' η * B0582.zeroModePrimitive w η = ∫ y, G η y := by
    intro η
    rw [← B0582.integral_indicator_Iic, ← integral_const_mul]
  have htend : Tendsto ψ atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (|R|)] with η hη
    exact (hR η (lt_of_le_of_lt (le_abs_self R) (lt_of_lt_of_le hη (le_abs_self η)))).symm
  have h2 : ∀ y, ∫ η, G η y = -(ψ y * w y) := by
    intro y
    have e : (fun η => G η y) = (Ici y).indicator (fun η => ψ' η * w y) := by
      funext η
      simp only [hG, Set.indicator_apply, mem_Iic, mem_Ici]
      split_ifs <;> simp
    rw [e, integral_indicator measurableSet_Ici, integral_mul_const, integral_Ici_eq_integral_Ioi,
      integral_Ioi_of_hasDerivAt_of_tendsto (hψ y).continuousAt.continuousWithinAt
        (fun x _ => hψ x) hψ'int.integrableOn htend]
    ring
  simp_rw [h1]
  rw [integral_integral_swap hGint]
  simp_rw [h2]
  rw [integral_neg]

/-- `∫_cell ∂_η φ · F(η) = -∫_cell φ · w(η)` for `F = ∫_{-∞}^η w`, `w ∈ L¹ ∩ L²`, `F ∈ L²`. -/
theorem integral_pd1_mul_primitive {c : ℝ} {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ)
    {w : ℝ → ℝ} (hw : Integrable w) (hw2 : MemLp w 2 volume)
    (hF : MemLp (B0582.zeroModePrimitive w) 2 volume) :
    ∫ x, B0579.pd 1 φ x * B0582.zeroModePrimitive w x.2 ∂cellVol c =
      -∫ x, φ x * w x.2 ∂cellVol c := by
  have hF2 : MemLp (fun x : B0579.Plane => B0582.zeroModePrimitive w x.2) 2 (cellVol c) := by
    rw [cellVol_eq]; exact hF.comp_snd (μq c)
  have hw22 : MemLp (fun x : B0579.Plane => w x.2) 2 (cellVol c) := by
    rw [cellVol_eq]; exact hw2.comp_snd (μq c)
  have hint1 : Integrable (fun x => B0579.pd 1 φ x * B0582.zeroModePrimitive w x.2) (cellVol c) :=
    (memLp_cellVol_of_isCylTest (hφ.pd 1)).integrable_mul hF2
  have hint2 : Integrable (fun x => φ x * w x.2) (cellVol c) :=
    (memLp_cellVol_of_isCylTest hφ).integrable_mul hw22
  rw [cellVol_eq] at hint1 hint2
  rw [integral_cellVol, integral_cellVol, integral_prod _ hint1, integral_prod _ hint2,
    ← integral_neg]
  congr 1
  funext q
  obtain ⟨R, hR⟩ := hφ.band
  exact integral_deriv_mul_primitive (ψ := fun η => φ (q, η))
    (fun η => hasDerivAt_pd1 hφ.differentiable q η)
    ((hφ.pd 1).continuous.comp (Continuous.prodMk_right q)) (R := R)
    (fun η hη => hR (q, η) hη) hw

/-! ### The zero-mode velocity and its gradient -/

/-- **The zero-mode velocity** `(-∫_{-∞}^η ω̄, 0)` (`paper/main.tex:9412-9413`), the
Biot–Savart velocity `∇^⊥Δ^{-1}ω̄` of the horizontal mean. -/
def zeroVel (c : ℝ) (ω : B0579.Plane → ℝ) : B0579.Plane → Vel :=
  profField fun η => -B0582.zeroModePrimitive (omegaBar c ω) η

/-- Its `η`-derivative `(-ω̄(η), 0)`. -/
def zeroVelEta (c : ℝ) (ω : B0579.Plane → ℝ) : B0579.Plane → Vel :=
  profField fun η => -omegaBar c ω η

end UnforcedLeray.B0583
