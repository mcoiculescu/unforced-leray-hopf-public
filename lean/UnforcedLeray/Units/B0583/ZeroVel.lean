import UnforcedLeray.Units.B0583.ZeroMode

/-!
# B0583 helper: the zero-mode velocity in `L²(cell)` and its weak gradient

Blueprint unit **B0583** (`prepared:p1.4`), `paper/main.tex` lines 9412–9426: "For `k = 0`, the
velocity is a primitive of `ω̄(η)`. Its limits at both ends are zero by zero total circulation.
The one-dimensional Hardy inequality gives [`prepared:p1.3`, unit `B0582`] ... The gradient is
bounded by the Fourier multiplier of order zero."

For `ω ∈ X_m` (`m ≥ 1`, which contains the manuscript's `m > 1`) with zero total circulation
`∫_cell ω = 0`, and `c > 0`:

* `zeroMode_facts`: `ω̄ ∈ L¹ ∩ L²(ℝ)`, the primitive `F = ∫_{-∞}^η ω̄` tends to `0` at both ends
  and lies in `L²(ℝ)`, with `‖F‖₂ ≤ 2 c^{-1/2} ‖ω‖_{X_m}` (Hardy, `B0582.hardy_zero_mode`) and
  `‖ω̄‖₂ ≤ c^{-1/2} ‖ω‖_{X_m}` (Cauchy–Schwarz in `q`);
* `zeroVelLp`, `zeroVelEtaLp`: the zero-mode velocity `(-F(η), 0)` and its `η`-derivative
  `(-ω̄(η), 0)` as elements of `L²(cell; ℂ²)`, with `‖zeroVelLp‖ ≤ 2 ‖ω‖_{X_m}` and
  `‖zeroVelEtaLp‖ ≤ ‖ω‖_{X_m}` (`norm_zeroVelLp_le`, `norm_zeroVelEtaLp_le`): the factor
  `√c` from the `q`-integration cancels the factor `c^{-1/2}` above, so these constants do not
  depend on `c`;
* the weak-derivative identities against cylinder test fields `φ e_j`
  (`inner_pd0_zeroVelLp`: `∂_q` of the zero-mode velocity is `0`; `inner_pd1_zeroVelLp`: its
  `∂_η` is `zeroVelEtaLp`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex Topology
open scoped ENNReal NNReal InnerProductSpace Real ComplexConjugate

namespace UnforcedLeray.B0583

open B0581

/-! ### Norms of the zero mode -/

/-- `‖⟨η⟩ ω̄‖_{L²(ℝ)} ≤ c^{-1/2} ‖ω‖_{X_m}` for `m ≥ 1`. -/
theorem eLpNorm_weighted_omegaBar_le {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) (ω : B0579.X c m) :
    eLpNorm (fun η => B0582.jb η * omegaBar c ω η) 2 volume ≤
      ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) *
        eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) := by
  rw [eLpNorm_two_eq', eLpNorm_X_eq, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow (lintegral_weighted_omegaBar_le hc hm (Lp.stronglyMeasurable ω))
    (by norm_num)

theorem ofReal_rpow_half_mul_inv {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal c ^ (1 / 2 : ℝ) * ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) = 1 := by
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.ofReal_mul hc.le,
    mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, ENNReal.one_rpow]

theorem one_le_jb (η : ℝ) : 1 ≤ B0582.jb η := by
  nlinarith [B0582.jb_sq η, B0582.jb_pos η, sq_nonneg η]

/-- **The zero mode** (`paper/main.tex:9412-9425`). For `ω ∈ X_m`, `m ≥ 1`, with zero total
circulation: `ω̄ ∈ L¹ ∩ L²(ℝ)`; its primitive `F(η) = ∫_{-∞}^η ω̄` tends to `0` at both ends
(line 9414) and lies in `L²(ℝ)` with `‖F‖₂ ≤ 2 c^{-1/2} ‖ω‖_{X_m}` (Hardy, `B0582`); and
`‖ω̄‖₂ ≤ c^{-1/2} ‖ω‖_{X_m}`. -/
theorem zeroMode_facts {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    Integrable (omegaBar c ω) ∧ MemLp (omegaBar c ω) 2 volume ∧
      Tendsto (B0582.zeroModePrimitive (omegaBar c ω)) atBot (𝓝 0) ∧
      Tendsto (B0582.zeroModePrimitive (omegaBar c ω)) atTop (𝓝 0) ∧
      MemLp (B0582.zeroModePrimitive (omegaBar c ω)) 2 volume ∧
      eLpNorm (B0582.zeroModePrimitive (omegaBar c ω)) 2 volume ≤
        2 * (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) *
          eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m)) ∧
      eLpNorm (omegaBar c ω) 2 volume ≤
        ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) *
          eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) := by
  have hw := memLp_weighted_omegaBar hc hm ω
  have hmean := integral_omegaBar_eq_zero hm ω hcirc
  obtain ⟨hint, hbot, htop, hF, hle⟩ := B0582.hardy_zero_mode _ hw hmean
  have hwle := eLpNorm_weighted_omegaBar_le hc hm ω
  have hpt : ∀ η, ‖omegaBar c ω η‖ ≤ ‖B0582.jb η * omegaBar c ω η‖ := by
    intro η
    rw [norm_mul]
    refine le_mul_of_one_le_left (norm_nonneg _) ?_
    rw [Real.norm_eq_abs, abs_of_pos (B0582.jb_pos η)]
    exact one_le_jb η
  have hmeas : AEStronglyMeasurable (omegaBar c ω) volume :=
    (measurable_omegaBar c (Lp.stronglyMeasurable ω)).aestronglyMeasurable
  refine ⟨hint, hw.of_le hmeas (Eventually.of_forall hpt), hbot, htop, hF,
    hle.trans (by gcongr), (eLpNorm_mono hpt).trans hwle⟩

/-! ### The zero-mode velocity in `L²(cell; ℂ²)` -/

section Lp

variable (c : ℝ) [hc : Fact (0 < c)] {m : ℝ}

/-- **The zero-mode velocity** `(-∫_{-∞}^η ω̄, 0)` (`zeroVel`) as an element of `L²(cell; ℂ²)`,
for `ω ∈ X_m`, `m ≥ 1`, with zero total circulation (`paper/main.tex:9412-9414`). -/
def zeroVelLp (hm : 1 ≤ m) (ω : B0579.X c m) (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    Lp Vel 2 (cellVol c) :=
  (memLp_profField c (zeroMode_facts hc.out hm ω hcirc).2.2.2.2.1.neg).toLp
    (profField fun η => -B0582.zeroModePrimitive (omegaBar c ω) η)

/-- Its `η`-derivative `(-ω̄(η), 0)` (`zeroVelEta`) as an element of `L²(cell; ℂ²)`. -/
def zeroVelEtaLp (hm : 1 ≤ m) (ω : B0579.X c m) (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    Lp Vel 2 (cellVol c) :=
  (memLp_profField c (zeroMode_facts hc.out hm ω hcirc).2.1.neg).toLp
    (profField fun η => -omegaBar c ω η)

theorem coeFn_zeroVelLp (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    zeroVelLp c hm ω hcirc =ᵐ[cellVol c] zeroVel c ω :=
  MemLp.coeFn_toLp _

theorem coeFn_zeroVelEtaLp (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) :
    zeroVelEtaLp c hm ω hcirc =ᵐ[cellVol c] zeroVelEta c ω :=
  MemLp.coeFn_toLp _

/-- `‖(-F(η), 0)‖_{L²(cell)} ≤ 2 ‖ω‖_{X_m}` (Hardy; the constant does not depend on `c`). -/
theorem norm_zeroVelLp_le (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) : ‖zeroVelLp c hm ω hcirc‖ ≤ 2 * ‖ω‖ := by
  obtain ⟨-, -, -, -, hF, hle, -⟩ := zeroMode_facts hc.out hm ω hcirc
  have hF' : MemLp (fun η => -B0582.zeroModePrimitive (omegaBar c ω) η) 2 volume := hF.neg
  have h : eLpNorm (profField fun η => -B0582.zeroModePrimitive (omegaBar c ω) η) 2 (cellVol c) ≤
      2 * eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) := by
    rw [eLpNorm_profField hc.out.le hF'.1,
      show (fun η => -B0582.zeroModePrimitive (omegaBar c ω) η) =
        -B0582.zeroModePrimitive (omegaBar c ω) from rfl, eLpNorm_neg]
    calc ENNReal.ofReal c ^ (1 / 2 : ℝ) * eLpNorm (B0582.zeroModePrimitive (omegaBar c ω)) 2 volume
        ≤ ENNReal.ofReal c ^ (1 / 2 : ℝ) * (2 * (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) *
            eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m))) := by gcongr
      _ = 2 * ((ENNReal.ofReal c ^ (1 / 2 : ℝ) * ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ)) *
            eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m)) := by ring
      _ = 2 * eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) := by
          rw [ofReal_rpow_half_mul_inv hc.out, one_mul]
  rw [zeroVelLp, Lp.norm_toLp, Lp.norm_def]
  have hfin : 2 * eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (Lp.eLpNorm_ne_top ω)
  have := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this

/-- `‖(-ω̄(η), 0)‖_{L²(cell)} ≤ ‖ω‖_{X_m}`. -/
theorem norm_zeroVelEtaLp_le (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) : ‖zeroVelEtaLp c hm ω hcirc‖ ≤ ‖ω‖ := by
  obtain ⟨-, hw2, -, -, -, -, hle⟩ := zeroMode_facts hc.out hm ω hcirc
  have hw2' : MemLp (fun η => -omegaBar c ω η) 2 volume := hw2.neg
  have h : eLpNorm (profField fun η => -omegaBar c ω η) 2 (cellVol c) ≤
      eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) := by
    rw [eLpNorm_profField hc.out.le hw2'.1,
      show (fun η => -omegaBar c ω η) = -omegaBar c ω from rfl, eLpNorm_neg]
    calc ENNReal.ofReal c ^ (1 / 2 : ℝ) * eLpNorm (omegaBar c ω) 2 volume
        ≤ ENNReal.ofReal c ^ (1 / 2 : ℝ) * (ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) *
            eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m)) := by gcongr
      _ = (ENNReal.ofReal c ^ (1 / 2 : ℝ) * ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ)) *
            eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) := by ring
      _ = eLpNorm (ω : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) := by
          rw [ofReal_rpow_half_mul_inv hc.out, one_mul]
  rw [zeroVelEtaLp, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top ω) h

/-! ### Weak derivatives of the zero-mode velocity -/

/-- `∂_q (-F(η), 0) = 0` weakly: `⟪∂_q φ e_j, (-F, 0)⟫ = 0` for every cylinder test function. -/
theorem inner_pd0_zeroVelLp (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ)
    (j : Fin 2) : ⟪testLp c (hφ.pd 0) j, zeroVelLp c hm ω hcirc⟫_ℂ = 0 := by
  have hF : MemLp (fun η => -B0582.zeroModePrimitive (omegaBar c ω) η) 2 volume :=
    (zeroMode_facts hc.out hm ω hcirc).2.2.2.2.1.neg
  rw [show zeroVelLp c hm ω hcirc = (memLp_profField c hF).toLp
      (profField fun η => -B0582.zeroModePrimitive (omegaBar c ω) η) from rfl,
    inner_testLp_profField c (hφ.pd 0) j hF, integral_pd0_mul_prof hc.out hφ hF]
  simp

/-- `∂_η (-F(η), 0) = (-ω̄(η), 0)` weakly:
`⟪∂_η φ e_j, (-F, 0)⟫ = -⟪φ e_j, (-ω̄, 0)⟫` for every cylinder test function. -/
theorem inner_pd1_zeroVelLp (hm : 1 ≤ m) (ω : B0579.X c m)
    (hcirc : ∫ x in B0579.cell c, ω x = 0) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ)
    (j : Fin 2) :
    ⟪testLp c (hφ.pd 1) j, zeroVelLp c hm ω hcirc⟫_ℂ =
      -⟪testLp c hφ j, zeroVelEtaLp c hm ω hcirc⟫_ℂ := by
  obtain ⟨hint, hw2, -, -, hF, -, -⟩ := zeroMode_facts hc.out hm ω hcirc
  have hF' : MemLp (fun η => -B0582.zeroModePrimitive (omegaBar c ω) η) 2 volume := hF.neg
  have hw2' : MemLp (fun η => -omegaBar c ω η) 2 volume := hw2.neg
  rw [show zeroVelLp c hm ω hcirc = (memLp_profField c hF').toLp
      (profField fun η => -B0582.zeroModePrimitive (omegaBar c ω) η) from rfl,
    show zeroVelEtaLp c hm ω hcirc = (memLp_profField c hw2').toLp
      (profField fun η => -omegaBar c ω η) from rfl,
    inner_testLp_profField c (hφ.pd 1) j hF', inner_testLp_profField c hφ j hw2']
  have h1 : ∫ x, B0579.pd 1 φ x * -B0582.zeroModePrimitive (omegaBar c ω) x.2 ∂cellVol c =
      ∫ x, φ x * omegaBar c ω x.2 ∂cellVol c := by
    simp only [mul_neg]
    rw [integral_neg, integral_pd1_mul_primitive hφ hint hw2 hF, neg_neg]
  have h2 : ∫ x, φ x * -omegaBar c ω x.2 ∂cellVol c = -∫ x, φ x * omegaBar c ω x.2 ∂cellVol c := by
    simp only [mul_neg]
    rw [integral_neg]
  beta_reduce
  rw [h1, h2]
  push_cast
  ring

end Lp

end UnforcedLeray.B0583
