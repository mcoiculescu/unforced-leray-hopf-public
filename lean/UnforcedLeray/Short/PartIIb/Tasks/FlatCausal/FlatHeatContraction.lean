import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Lib.CylinderB.Periodize
import UnforcedLeray.Units.B0284.Contraction

/-!
# Part II-b, leaf `PartII-b:T12/8` (`FlatHeatContraction`): flat heat contraction on the cylinder

Source of record: `the November 2 reference manuscript`, SP 1923-1927 ("the cylinder
heat estimate", used by `T12/4`). The statement is `FlatHeatContraction` of `Sub/T12.lean`.

Proof outline.
* `flatHeatKernel θ = B0284.heatKernel2 θ` pointwise (product of two one-dimensional kernels), so the
  kernel is nonnegative with unit mass (`flatHeat_eLpNorm_kernel_one`).
* `g` agrees almost everywhere with a strongly measurable, everywhere `c`-periodic `g'`, namely the
  floor-shifted copy `g'(q, η) = g₀(q - c⌊q/c⌋, η)` of a measurable representative `g₀`. The a.e.
  periodicity of `g` gives `g' = g` a.e. (`flatHeat_ae_intShift`), and `flatHeat θ g = flatHeat θ g'`
  pointwise (translation of a null set).
* The periodic planar convolution bound `UnforcedLeray.Cyl.eLpNorm_planarConv_periodic_le` (Minkowski
  plus translation invariance of the cell norm) gives
  `‖flatHeat θ g'‖_{L^r(cellμ c)} ≤ ‖flatHeatKernel θ‖_{L¹} ‖g'‖_{L^r(cellμ c)}`. The normalized
  measure `Cyl.avgμ c = ofReal c⁻¹ • cellμ c` only contributes a common factor on both sides.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-! ## The flat heat kernel is the planar heat kernel of B0284 -/

/-- The flat heat kernel `(4πθ)⁻¹ exp(-|w|²/(4θ))` is the product kernel `heatKernel2 θ` of B0284
(`θ > 0`). -/
theorem flatHeat_kernel_eq {θ : ℝ} (hθ : 0 < θ) (w : ℝ × ℝ) :
    flatHeatKernel θ w = UnforcedLeray.B0284.heatKernel2 θ w := by
  unfold flatHeatKernel UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
  have hnn : (0 : ℝ) ≤ 4 * Real.pi * 1 * θ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) zero_le_one) hθ.le
  have hs : Real.sqrt (4 * Real.pi * 1 * θ) * Real.sqrt (4 * Real.pi * 1 * θ) =
      4 * Real.pi * θ := by
    rw [Real.mul_self_sqrt hnn]; ring
  have he : Real.exp (-w.1 ^ 2 / (4 * 1 * θ)) * Real.exp (-w.2 ^ 2 / (4 * 1 * θ)) =
      Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * θ)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (4 * Real.pi * θ)⁻¹ * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * θ))
      = (Real.sqrt (4 * Real.pi * 1 * θ) * Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ *
          (Real.exp (-w.1 ^ 2 / (4 * 1 * θ)) * Real.exp (-w.2 ^ 2 / (4 * 1 * θ))) := by
        rw [hs, he]
    _ = (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ * Real.exp (-w.1 ^ 2 / (4 * 1 * θ)) *
          ((Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ * Real.exp (-w.2 ^ 2 / (4 * 1 * θ))) := by
        ring

/-- The flat heat kernel has unit `L¹` norm (`θ > 0`). -/
theorem flatHeat_eLpNorm_kernel_one {θ : ℝ} (hθ : 0 < θ) :
    eLpNorm (flatHeatKernel θ) 1 volume = 1 := by
  have hk : flatHeatKernel θ = UnforcedLeray.B0284.heatKernel2 θ :=
    funext (flatHeat_kernel_eq hθ)
  have hnn : ∀ w : ℝ × ℝ, 0 ≤ UnforcedLeray.B0284.heatKernel2 θ w :=
    fun w => UnforcedLeray.B0284.heatKernel2_nonneg hθ w
  have hint : Integrable (UnforcedLeray.B0284.heatKernel2 θ) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [UnforcedLeray.B0284.integral_heatKernel2 hθ]
    exact one_ne_zero
  have h := ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)
  rw [UnforcedLeray.B0284.integral_heatKernel2 hθ, ENNReal.ofReal_one] at h
  rw [hk, eLpNorm_one_eq_lintegral_enorm]
  have hcongr : ∫⁻ w, ‖UnforcedLeray.B0284.heatKernel2 θ w‖ₑ ∂volume =
      ∫⁻ w, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 θ w) ∂volume :=
    lintegral_congr fun w => Real.enorm_of_nonneg (hnn w)
  rw [hcongr]
  exact h.symm

/-! ## Integer shifts of an a.e. periodic function -/

/-- An almost everywhere `c`-periodic function is almost everywhere invariant under the integer shift
`q ↦ q + k c`, for every `k ∈ ℤ`. -/
theorem flatHeat_ae_intShift {c : ℝ} {g : ℝ × ℝ → CMerid}
    (hper : ∀ᵐ z : ℝ × ℝ, g (z.1 + c, z.2) = g z) (k : ℤ) :
    ∀ᵐ z : ℝ × ℝ, g (z.1 + (k : ℝ) * c, z.2) = g z := by
  have up : ∀ k : ℤ, (∀ᵐ z : ℝ × ℝ, g (z.1 + (k : ℝ) * c, z.2) = g z) →
      ∀ᵐ z : ℝ × ℝ, g (z.1 + ((k + 1 : ℤ) : ℝ) * c, z.2) = g z := by
    intro k hk
    have h1 : ∀ᵐ z : ℝ × ℝ, g (z.1 + (k : ℝ) * c + c, z.2) = g (z.1 + (k : ℝ) * c, z.2) :=
      (UnforcedLeray.Cyl.measurePreserving_shift ((k : ℝ) * c)).quasiMeasurePreserving.ae hper
    filter_upwards [h1, hk] with z h1z hkz
    have e : z.1 + ((k + 1 : ℤ) : ℝ) * c = z.1 + (k : ℝ) * c + c := by
      push_cast; ring
    rw [e, h1z, hkz]
  have down : ∀ k : ℤ, (∀ᵐ z : ℝ × ℝ, g (z.1 + (k : ℝ) * c, z.2) = g z) →
      ∀ᵐ z : ℝ × ℝ, g (z.1 + ((k - 1 : ℤ) : ℝ) * c, z.2) = g z := by
    intro k hk
    have h1 : ∀ᵐ z : ℝ × ℝ, g (z.1 + ((k - 1 : ℤ) : ℝ) * c + c, z.2) =
        g (z.1 + ((k - 1 : ℤ) : ℝ) * c, z.2) :=
      (UnforcedLeray.Cyl.measurePreserving_shift (((k - 1 : ℤ) : ℝ) * c)).quasiMeasurePreserving.ae
        hper
    filter_upwards [h1, hk] with z h1z hkz
    have e : z.1 + ((k - 1 : ℤ) : ℝ) * c + c = z.1 + (k : ℝ) * c := by
      push_cast; ring
    rw [← h1z, e, hkz]
  refine Int.induction_on k ?_ (fun i ih => up _ ih) (fun i ih => down _ ih)
  exact Filter.Eventually.of_forall fun z => by simp

/-! ## The target -/

/-- **Leaf `PartII-b:T12/8`** (SP 1923-1927, "the cylinder heat estimate"): the flat heat operator
`flatHeat θ` is an `L^r(dq/c dη)` contraction for `1 ≤ r`, on `c`-periodic a.e. strongly measurable
fields. -/
theorem flatHeatContraction : FlatHeatContraction := by
  unfold FlatHeatContraction
  intro r c θ g hr hc hθ hgper hg
  have hc0 : c ≠ 0 := hc.ne'
  -- (1) a strongly measurable representative `g₀` of `g`
  obtain ⟨g₀, hg₀m, hg₀⟩ : ∃ g₀ : ℝ × ℝ → CMerid, StronglyMeasurable g₀ ∧
      ∀ᵐ z : ℝ × ℝ, g₀ z = g z :=
    ⟨hg.mk g, hg.stronglyMeasurable_mk, hg.ae_eq_mk.symm⟩
  -- (2) the floor-shifted, everywhere `c`-periodic copy `g' (q, η) = g₀ (q - c⌊q/c⌋, η)`
  have hfl : Measurable (fun z : ℝ × ℝ => ((⌊z.1 / c⌋ : ℤ) : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      (Int.measurable_floor.comp (measurable_fst.div_const c))
  have hS : Measurable (fun z : ℝ × ℝ => (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2)) :=
    (measurable_fst.sub (hfl.mul_const c)).prodMk measurable_snd
  obtain ⟨g', hg'def⟩ : ∃ g' : ℝ × ℝ → CMerid, ∀ z : ℝ × ℝ,
      g' z = g₀ (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2) :=
    ⟨fun z => g₀ (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2), fun _ => rfl⟩
  have hper' : ∀ z : ℝ × ℝ, g' (z.1 + c, z.2) = g' z := by
    intro z
    rw [hg'def, hg'def]
    dsimp only
    have hfl1 : ⌊(z.1 + c) / c⌋ = ⌊z.1 / c⌋ + 1 := by
      rw [add_div, div_self hc0]
      exact Int.floor_add_one _
    rw [hfl1]
    have e : z.1 + c - ((⌊z.1 / c⌋ + 1 : ℤ) : ℝ) * c =
        z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c := by
      push_cast; ring
    rw [e]
  have hg'm : StronglyMeasurable g' := by
    have hfun : g' = fun z : ℝ × ℝ => g₀ (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2) :=
      funext hg'def
    rw [hfun]
    exact hg₀m.comp_measurable hS
  -- (3) `g'` agrees with `g` almost everywhere
  have hA : ∀ k : ℤ, ∀ᵐ z : ℝ × ℝ, g₀ (z.1 - (k : ℝ) * c, z.2) = g z := by
    intro k
    have h1 : ∀ᵐ z : ℝ × ℝ, g₀ (z.1 + ((-k : ℤ) : ℝ) * c, z.2) =
        g (z.1 + ((-k : ℤ) : ℝ) * c, z.2) :=
      (UnforcedLeray.Cyl.measurePreserving_shift (((-k : ℤ) : ℝ) * c)).quasiMeasurePreserving.ae
        hg₀
    filter_upwards [h1, flatHeat_ae_intShift hgper (-k)] with z h1z h2z
    have e : z.1 - (k : ℝ) * c = z.1 + ((-k : ℤ) : ℝ) * c := by
      push_cast; ring
    rw [e, h1z, h2z]
  have hall : ∀ᵐ z : ℝ × ℝ, ∀ k : ℤ, g₀ (z.1 - (k : ℝ) * c, z.2) = g z :=
    (ae_all_iff (p := fun (z : ℝ × ℝ) (k : ℤ) => g₀ (z.1 - (k : ℝ) * c, z.2) = g z)).2 hA
  have hgg' : ∀ᵐ z : ℝ × ℝ, g' z = g z := by
    filter_upwards [hall] with z hz
    rw [hg'def]
    exact hz ⌊z.1 / c⌋
  have hgg2 : ∀ᵐ z : ℝ × ℝ, g z = g' z := hgg'.mono fun z hz => hz.symm
  -- (4) the flat heat operator only depends on `g` almost everywhere
  have hflat : flatHeat θ g = flatHeat θ g' := by
    funext z
    unfold flatHeat
    refine integral_congr_ae ?_
    have hq := quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure (ℝ × ℝ)) z
    filter_upwards [hq.ae hgg2] with w hw
    simp only [hw]
  have hgeq : eLpNorm g (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) =
      eLpNorm g' (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
    refine eLpNorm_congr_ae ?_
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    exact Measure.ae_smul_measure (ae_restrict_of_ae hgg2) _
  -- (5) the periodic planar convolution bound for `g'`, with the unit-mass kernel
  have hkc : Continuous (flatHeatKernel θ) := by
    unfold flatHeatKernel
    fun_prop
  have hplanar := UnforcedLeray.Cyl.eLpNorm_planarConv_periodic_le hc hkc.stronglyMeasurable hg'm
    hper' (ENNReal.one_le_ofReal.2 hr) ENNReal.ofReal_ne_top
  rw [flatHeat_eLpNorm_kernel_one hθ, one_mul] at hplanar
  -- (6) the normalized measure `avgμ c = ofReal c⁻¹ • cellμ c` contributes a common factor
  rw [hflat, hgeq]
  unfold UnforcedLeray.Cyl.avgμ
  rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofReal_ne_top,
    eLpNorm_smul_measure_of_ne_top ENNReal.ofReal_ne_top]
  rw [smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hplanar zero_le

end UnforcedLeray.Short.IIb
