import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.HrStripLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.CutLocInt

/-!
# Part II-b, leaf `PartII-b:T11/6/15` (`MollLp`): `s`-slices of the mollification are in `L^r(cell)`

Source of record: `the November 2 reference manuscript`, SP 1900-1903 and 2618.
Statement: `MollLp` of `Sub/T11_6.lean`, unchanged.

Proof. Write `g = cutC δ (b · i)`, `G = ‖g‖ₑ`, `a z x = ‖ρ₁(s - x₁)‖ₑ ‖ρ₂(z - x₂)‖ₑ`.
1. `‖M(z)‖ₑ ≤ ∫⁻ a z x G x` (`enorm_integral_le_lintegral_enorm`).
2. Hölder (`mlpJensen`): `‖M(z)‖ₑ^r ≤ (∫⁻ a z)^(r-1) · ∫⁻ a z G^r`, and `∫⁻ a z ≤ K₀` uniformly in `z`.
3. The `z`-integral over the cell is bounded by a Tonelli swap against
   `Ψ(z, x) = 1_E(z,x) · A² · 1_S(x) G(x)^r`, where `E` is the box condition and `S` the strip
   `[δ, s+δ] × [-R, R] × ℝ`, `R = c/2 + δ`. The `z`-volume of each slice is `(2δ)²`.
4. `∫_S G^r ≤ ∫_S ‖b‖ₑ^r < ∞` by `hrStripLp`, using `‖b i‖ₑ ≤ ‖b‖ₑ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Jensen/Hölder step: `(∫ a G)^r ≤ (∫ a)^(r-1) · ∫ a G^r` for `r > 1`. -/
theorem mlpJensen {α : Type*} [MeasurableSpace α] (μ : Measure α) {r : ℝ} (hr : 1 < r)
    {a G : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hG : AEMeasurable G μ) :
    (∫⁻ x, a x * G x ∂μ) ^ r ≤ (∫⁻ x, a x ∂μ) ^ (r - 1) * ∫⁻ x, a x * G x ^ r ∂μ := by
  have hr0 : 0 < r := by linarith
  have hrq : r.HolderConjugate (Real.conjExponent r) := Real.HolderConjugate.conjExponent hr
  set q : ℝ := Real.conjExponent r with hq_def
  have hqr : q.HolderConjugate r := hrq.symm
  have hq0 : 0 < q := hqr.pos
  have hsum : 1 / q + 1 / r = 1 := by
    rw [one_div, one_div]; exact hqr.inv_add_inv_eq_one
  have hqr' : (1 / q) * r = r - 1 := by
    rw [hq_def, Real.conjExponent]
    have hr1 : r - 1 ≠ 0 := (sub_pos.2 hr).ne'
    field_simp
  have hfq : ∀ x, (a x ^ (1 / q)) ^ q = a x := by
    intro x
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have hfg : ∀ x, a x ^ (1 / q) * (a x ^ (1 / r) * G x) = a x * G x := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (one_div_nonneg.2 hq0.le)
      (one_div_nonneg.2 hr0.le), hsum, ENNReal.rpow_one]
  have hgr : ∀ x, (a x ^ (1 / r) * G x) ^ r = a x * G x ^ r := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne',
      ENNReal.rpow_one]
  have h1 : ∫⁻ x, a x * G x ∂μ ≤ (∫⁻ x, a x ∂μ) ^ (1 / q) * (∫⁻ x, a x * G x ^ r ∂μ) ^ (1 / r) := by
    have hH' := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hqr (ha.pow_const (1 / q))
      ((ha.pow_const (1 / r)).mul hG)
    simpa only [Pi.mul_apply, hfq, hfg, hgr] using hH'
  calc (∫⁻ x, a x * G x ∂μ) ^ r
      ≤ ((∫⁻ x, a x ∂μ) ^ (1 / q) * (∫⁻ x, a x * G x ^ r ∂μ) ^ (1 / r)) ^ r :=
        ENNReal.rpow_le_rpow h1 hr0.le
    _ = (∫⁻ x, a x ∂μ) ^ (r - 1) * ∫⁻ x, a x * G x ^ r ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hqr',
          one_div_mul_cancel hr0.ne', ENNReal.rpow_one]

/-- A uniform bound for an admissible kernel pair: `‖ρ₁ t‖ₑ ≤ A` and `‖ρ₂ w‖ₑ ≤ A`. -/
theorem mlpKernelBound {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (h : IsMollKer δ ρ₁ ρ₂) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ (∀ t, ‖ρ₁ t‖ₑ ≤ A) ∧ (∀ w, ‖ρ₂ w‖ₑ ≤ A) := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := -δ) (b := δ)).exists_bound_of_continuousOn
    h.smooth₁.continuous.continuousOn
  obtain ⟨C₂, hC₂⟩ := ((isCompact_Icc (a := -δ) (b := δ)).prod
    (isCompact_Icc (a := -δ) (b := δ))).exists_bound_of_continuousOn
    h.smooth₂.continuous.continuousOn
  refine ⟨ENNReal.ofReal (max (max C₁ C₂) 0), ENNReal.ofReal_ne_top, fun t => ?_, fun w => ?_⟩
  · rw [← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    by_cases ht : |t| ≤ δ
    · have := hC₁ t ⟨(abs_le.1 ht).1, (abs_le.1 ht).2⟩
      exact this.trans ((le_max_left C₁ C₂).trans (le_max_left _ _))
    · rw [h.supp₁ t (not_le.1 ht)]
      simp only [norm_zero]
      exact le_max_right _ _
  · rw [← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    by_cases hw : |w.1| ≤ δ ∧ |w.2| ≤ δ
    · have := hC₂ w ⟨⟨(abs_le.1 hw.1).1, (abs_le.1 hw.1).2⟩, ⟨(abs_le.1 hw.2).1, (abs_le.1 hw.2).2⟩⟩
      exact this.trans ((le_max_right C₁ C₂).trans (le_max_left _ _))
    · have hsupp : δ < |w.1| ∨ δ < |w.2| := by
        rcases not_and_or.1 hw with h1 | h1
        · exact Or.inl (not_le.1 h1)
        · exact Or.inr (not_le.1 h1)
      rw [h.supp₂ w hsupp]
      simp only [norm_zero]
      exact le_max_right _ _

/-- Off the box, the product of the two mollifier values vanishes. -/
theorem mlpAZero {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (h : IsMollKer δ ρ₁ ρ₂) (s : ℝ)
    (z : ℝ × ℝ) (x : Coord)
    (hn : ¬ (|s - x.1| ≤ δ ∧ |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ)) :
    ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ = 0 := by
  by_cases h1 : |s - x.1| ≤ δ
  · have hn' : ¬ (|z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ) := fun hh => hn ⟨h1, hh.1, hh.2⟩
    have h2 : δ < |(z - x.2).1| ∨ δ < |(z - x.2).2| := by
      rcases not_and_or.1 hn' with h3 | h3
      · exact Or.inl (by rw [Prod.fst_sub]; exact not_le.1 h3)
      · exact Or.inr (by rw [Prod.snd_sub]; exact not_le.1 h3)
    rw [h.supp₂ _ h2, enorm_zero, mul_zero]
  · rw [h.supp₁ _ (not_le.1 h1), enorm_zero, zero_mul]

/-- The `z`-slice of the tensor box has volume `(2δ)²`. -/
theorem mlpZvol (δ u v : ℝ) :
    volume {z : ℝ × ℝ | |z.1 - u| ≤ δ ∧ |z.2 - v| ≤ δ} =
      ENNReal.ofReal (2 * δ) * ENNReal.ofReal (2 * δ) := by
  have hset : {z : ℝ × ℝ | |z.1 - u| ≤ δ ∧ |z.2 - v| ≤ δ} =
      Icc (u - δ) (u + δ) ×ˢ Icc (v - δ) (v + δ) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc, abs_le]
    constructor <;> intro h <;> obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := h <;>
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have e1 : u + δ - (u - δ) = 2 * δ := by ring
  have e2 : v + δ - (v - δ) = 2 * δ := by ring
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, e1, e2]

/-- The full `x`-box of the tensor kernel has volume `(2δ)³`. -/
theorem mlpBvol (δ s z1 z2 : ℝ) :
    volume {x : Coord | |s - x.1| ≤ δ ∧ |z1 - x.2.1| ≤ δ ∧ |z2 - x.2.2| ≤ δ} =
      ENNReal.ofReal (2 * δ) * (ENNReal.ofReal (2 * δ) * ENNReal.ofReal (2 * δ)) := by
  have hset : {x : Coord | |s - x.1| ≤ δ ∧ |z1 - x.2.1| ≤ δ ∧ |z2 - x.2.2| ≤ δ} =
      Icc (s - δ) (s + δ) ×ˢ (Icc (z1 - δ) (z1 + δ) ×ˢ Icc (z2 - δ) (z2 + δ)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc, abs_le]
    constructor <;> intro h <;> obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩, ⟨a5, a6⟩⟩ := h <;>
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have e0 : s + δ - (s - δ) = 2 * δ := by ring
  have e1 : z1 + δ - (z1 - δ) = 2 * δ := by ring
  have e2 : z2 + δ - (z2 - δ) = 2 * δ := by ring
  rw [hset]
  simp only [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, e0, e1, e2]

/-- Left multiplication is monotone (ENNReal). -/
theorem mlpMulLeft {b c : ℝ≥0∞} (h : b ≤ c) (a : ℝ≥0∞) : a * b ≤ a * c := mul_le_mul' le_rfl h

/-- Right multiplication is monotone (ENNReal). -/
theorem mlpMulRight {b c : ℝ≥0∞} (h : b ≤ c) (a : ℝ≥0∞) : b * a ≤ c * a := mul_le_mul' h le_rfl

/-- The complex cast of a real has the same extended norm. -/
theorem mlpCEnorm (t : ℝ) : ‖(t : ℂ)‖ₑ = ‖t‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

/-- Measurability of a three-fold box condition. -/
theorem mlpMeas3 {α : Type*} [MeasurableSpace α] (f g h : α → ℝ) (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (δ : ℝ) :
    MeasurableSet {x : α | |f x| ≤ δ ∧ |g x| ≤ δ ∧ |h x| ≤ δ} := by
  rw [Set.setOf_and, Set.setOf_and]
  exact (measurableSet_le (continuous_abs.measurable.comp hf) measurable_const).inter
    ((measurableSet_le (continuous_abs.measurable.comp hg) measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp hh) measurable_const))

/-- Measurability of a two-fold box condition. -/
theorem mlpMeas2 {α : Type*} [MeasurableSpace α] (f g : α → ℝ) (hf : Measurable f)
    (hg : Measurable g) (δ : ℝ) :
    MeasurableSet {x : α | |f x| ≤ δ ∧ |g x| ≤ δ} := by
  rw [Set.setOf_and]
  exact (measurableSet_le (continuous_abs.measurable.comp hf) measurable_const).inter
    (measurableSet_le (continuous_abs.measurable.comp hg) measurable_const)

/-- **Leaf `PartII-b:T11/6/15`** (the `s`-slices of the mollification are in `L^r(cell)`). -/
theorem mollLp : UnforcedLeray.Short.IIb.MollLp := by
  intro c r b hc hr hb δ ρ₁ ρ₂ hδ hK s i
  have hr0 : 0 < r := by linarith
  obtain ⟨A, hAtop, hA1, hA2⟩ := mlpKernelBound hK
  have hρ1m : Measurable ρ₁ := hK.smooth₁.continuous.measurable
  have hρ2m : Measurable ρ₂ := hK.smooth₂.continuous.measurable
  set g : Coord → ℂ := cutC δ (fun x => b x i) with hg_def
  set R : ℝ := c / 2 + δ with hR_def
  set S : Set Coord := Icc δ (s + δ) ×ˢ (Icc (-R) R ×ˢ (univ : Set ℝ)) with hS_def
  set F : Coord → ℝ≥0∞ := fun x => ‖g x‖ₑ ^ r with hF_def
  set E : Set ((ℝ × ℝ) × Coord) :=
    {p | |s - p.2.1| ≤ δ ∧ |p.1.1 - p.2.2.1| ≤ δ ∧ |p.1.2 - p.2.2.2| ≤ δ} with hE_def
  set K0 : ℝ≥0∞ := A * A * (ENNReal.ofReal (2 * δ) * (ENNReal.ofReal (2 * δ) *
    ENNReal.ofReal (2 * δ))) with hK0_def
  set C2 : ℝ≥0∞ := A * A * (ENNReal.ofReal (2 * δ) * ENNReal.ofReal (2 * δ)) with hC2_def
  have hgm : AEMeasurable (fun x => ‖g x‖ₑ) volume :=
    ((cutLocInt c r δ b hc hr hδ hb i).aestronglyMeasurable).enorm
  have hFm : AEMeasurable F volume := hgm.pow_const r
  have hSm : MeasurableSet S := measurableSet_Icc.prod (measurableSet_Icc.prod MeasurableSet.univ)
  have hCellm : MeasurableSet (Cyl.cell c) := measurableSet_Ico.prod MeasurableSet.univ
  have hEm : MeasurableSet E := by
    exact mlpMeas3 (fun p : (ℝ × ℝ) × Coord => s - p.2.1)
      (fun p : (ℝ × ℝ) × Coord => p.1.1 - p.2.2.1)
      (fun p : (ℝ × ℝ) × Coord => p.1.2 - p.2.2.2)
      (by fun_prop) (by fun_prop) (by fun_prop) δ
  -- `‖g x‖ₑ ≤ ‖b x‖ₑ` pointwise
  have hGb : ∀ x : Coord, ‖g x‖ₑ ≤ ‖b x‖ₑ := by
    intro x
    by_cases hx : δ < x.1
    · have hgx : g x = b x i := Set.indicator_of_mem (show x ∈ {x : Coord | δ < x.1} from hx) _
      rw [hgx, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le (b x) i)
    · have hgx : g x = 0 := Set.indicator_of_notMem (show x ∉ {x : Coord | δ < x.1} from hx) _
      rw [hgx, enorm_zero]
      exact zero_le
  have hGr : ∀ x, ‖g x‖ₑ ^ r ≤ ‖b x‖ₑ ^ r := fun x => ENNReal.rpow_le_rpow (hGb x) hr0.le
  -- finiteness of the strip integral
  have hfinS : (∫⁻ x, S.indicator F x) ≠ ⊤ := by
    rw [lintegral_indicator hSm]
    exact ne_top_of_le_ne_top (hrStripLp c r b hc hr hb δ (s + δ) R hδ)
      (lintegral_mono fun x => hGr x)
  have hK0top : K0 ≠ ⊤ := by
    simp only [hK0_def]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hAtop hAtop)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
  have hKc_top : K0 ^ (r - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) hK0top
  have hC2top : C2 ≠ ⊤ := by
    simp only [hC2_def]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hAtop hAtop)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hA_mul : ∀ (t : ℝ) (w : ℝ × ℝ), ‖ρ₁ t‖ₑ * ‖ρ₂ w‖ₑ ≤ A * A :=
    fun t w => mul_le_mul' (hA1 t) (hA2 w)
  -- the `z`-integral of `a` is bounded uniformly
  have hAint : ∀ z : ℝ × ℝ, (∫⁻ x : Coord, ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ ∂volume) ≤ K0 := by
    intro z
    have hBzm : MeasurableSet {x : Coord | |s - x.1| ≤ δ ∧ |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ} :=
      mlpMeas3 (fun x : Coord => s - x.1) (fun x : Coord => z.1 - x.2.1)
        (fun x : Coord => z.2 - x.2.2) (by fun_prop) (by fun_prop) (by fun_prop) δ
    calc (∫⁻ x : Coord, ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ ∂volume)
        ≤ ∫⁻ x, {x : Coord | |s - x.1| ≤ δ ∧ |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ}.indicator
            (fun _ => A * A) x ∂volume := by
          refine lintegral_mono fun x => ?_
          by_cases hn : |s - x.1| ≤ δ ∧ |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ
          · rw [Set.indicator_of_mem (show x ∈ {x : Coord | |s - x.1| ≤ δ ∧
                |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ} from hn)]
            exact hA_mul _ _
          · rw [mlpAZero hK s z x hn]
            exact zero_le
      _ = A * A * volume {x : Coord | |s - x.1| ≤ δ ∧ |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ} :=
          lintegral_indicator_const hBzm _
      _ = K0 := by rw [mlpBvol, hK0_def]
  -- pointwise Jensen bound for each slice
  have hJ : ∀ z : ℝ × ℝ, ‖mollSlice δ ρ₁ ρ₂ (fun x => b x i) s z‖ₑ ^ r ≤
      K0 ^ (r - 1) * ∫⁻ x : Coord, ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ * ‖g x‖ₑ ^ r ∂volume := by
    intro z
    have hMz : ‖mollSlice δ ρ₁ ρ₂ (fun x => b x i) s z‖ₑ ≤
        ∫⁻ x : Coord, ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ * ‖g x‖ₑ ∂volume := by
      unfold mollSlice mollC mollG
      dsimp only
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
      rw [enorm_mul, mlpCEnorm, enorm_mul]
    have ha : AEMeasurable (fun x : Coord => ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ) volume :=
      ((hρ1m.comp (measurable_const.sub measurable_fst)).enorm.mul
        (hρ2m.comp (measurable_const.sub measurable_snd)).enorm).aemeasurable
    have hJ1 := mlpJensen volume hr ha hgm
    calc ‖mollSlice δ ρ₁ ρ₂ (fun x => b x i) s z‖ₑ ^ r
        ≤ (∫⁻ x : Coord, ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ * ‖g x‖ₑ ∂volume) ^ r :=
          ENNReal.rpow_le_rpow hMz hr0.le
      _ ≤ (∫⁻ x : Coord, ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ ∂volume) ^ (r - 1) *
            ∫⁻ x : Coord, ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ * ‖g x‖ₑ ^ r ∂volume := hJ1
      _ ≤ K0 ^ (r - 1) * ∫⁻ x : Coord, ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ * ‖g x‖ₑ ^ r ∂volume :=
          mlpMulRight (ENNReal.rpow_le_rpow (hAint z) (by linarith)) _
  -- the Tonelli kernel
  set Ψ : (ℝ × ℝ) → Coord → ℝ≥0∞ :=
    fun z x => E.indicator (fun p => A * A * S.indicator F p.2) (z, x) with hΨ_def
  have hP : ∀ z ∈ Cyl.cell c, ∀ x : Coord,
      ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ * ‖g x‖ₑ ^ r ≤ Ψ z x := by
    intro z hz x
    by_cases hn : |s - x.1| ≤ δ ∧ |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ
    · have hmem : (z, x) ∈ E := show |s - x.1| ≤ δ ∧ |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ from hn
      have hΨ : Ψ z x = A * A * S.indicator F x := by
        simp only [hΨ_def]
        rw [Set.indicator_of_mem hmem]
      rw [hΨ]
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]
        exact mul_le_mul' (hA_mul _ _) le_rfl
      · have hx1 : x.1 ≤ δ := by
          by_contra hcon
          have hcon' : δ < x.1 := not_le.1 hcon
          exfalso
          apply hxS
          have hz1 := hz.1
          obtain ⟨hz1a, hz1b⟩ := hz1
          have h1 := abs_le.1 hn.1
          have h2 := abs_le.1 hn.2.1
          exact ⟨⟨hcon'.le, by linarith [h1.1]⟩, ⟨by linarith [h2.2], by linarith [h2.1]⟩,
            trivial⟩
        have hg0 : g x = 0 :=
          Set.indicator_of_notMem (show x ∉ {x : Coord | δ < x.1} from fun h => absurd h
            (not_lt.2 hx1)) _
        rw [Set.indicator_of_notMem hxS]
        simp only [hF_def, hg0, enorm_zero]
        rw [ENNReal.zero_rpow_of_pos hr0, mul_zero]
        exact zero_le
    · have hE0 : ¬ (z, x) ∈ E := fun hh => hn hh
      have hzero := mlpAZero hK s z x hn
      rw [hzero, zero_mul]
      exact zero_le
  -- joint measurability of Ψ
  have hΨm : AEMeasurable (Function.uncurry Ψ) (volume.prod volume) := by
    have hfun : Function.uncurry Ψ = E.indicator (fun p => A * A * S.indicator F p.2) := by
      funext q
      simp [Function.uncurry, hΨ_def]
    rw [hfun]
    have hSF : AEMeasurable (S.indicator F) volume := hFm.indicator hSm
    exact ((aemeasurable_const.mul hSF.comp_snd)).indicator hEm
  -- `z`-integral of `Ψ` over each slice
  have hZx : ∀ x : Coord, (∫⁻ z, Ψ z x) ≤ C2 * S.indicator F x := by
    intro x
    have hZm : MeasurableSet {z : ℝ × ℝ | |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ} :=
      mlpMeas2 (fun z : ℝ × ℝ => z.1 - x.2.1) (fun z : ℝ × ℝ => z.2 - x.2.2)
        (by fun_prop) (by fun_prop) δ
    calc (∫⁻ z, Ψ z x)
        ≤ ∫⁻ z, {z : ℝ × ℝ | |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ}.indicator
            (fun _ => A * A * S.indicator F x) z := by
          refine lintegral_mono fun z => ?_
          by_cases hE' : (z, x) ∈ E
          · have hn : |z.1 - x.2.1| ≤ δ ∧ |z.2 - x.2.2| ≤ δ := ⟨hE'.2.1, hE'.2.2⟩
            have hΨ : Ψ z x = A * A * S.indicator F x := by
              simp only [hΨ_def]
              rw [Set.indicator_of_mem hE']
            rw [hΨ, Set.indicator_of_mem (show z ∈ {z : ℝ × ℝ | |z.1 - x.2.1| ≤ δ ∧
              |z.2 - x.2.2| ≤ δ} from hn)]
          · have hΨ : Ψ z x = 0 := by
              simp only [hΨ_def]
              rw [Set.indicator_of_notMem hE']
            rw [hΨ]
            exact zero_le
      _ = (A * A * S.indicator F x) * volume {z : ℝ × ℝ | |z.1 - x.2.1| ≤ δ ∧
              |z.2 - x.2.2| ≤ δ} := lintegral_indicator_const hZm _
      _ = C2 * S.indicator F x := by rw [mlpZvol, hC2_def]; ring
  -- assembly
  have hfinal : (∫⁻ z in Cyl.cell c, ‖mollSlice δ ρ₁ ρ₂ (fun x => b x i) s z‖ₑ ^ r) ≤
      K0 ^ (r - 1) * (C2 * ∫⁻ x, S.indicator F x) := by
    calc (∫⁻ z in Cyl.cell c, ‖mollSlice δ ρ₁ ρ₂ (fun x => b x i) s z‖ₑ ^ r)
        ≤ ∫⁻ z in Cyl.cell c, K0 ^ (r - 1) *
            ∫⁻ x : Coord, ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ * ‖g x‖ₑ ^ r ∂volume :=
          lintegral_mono fun z => hJ z
      _ = K0 ^ (r - 1) * ∫⁻ z in Cyl.cell c, ∫⁻ x,
            ‖ρ₁ (s - x.1)‖ₑ * ‖ρ₂ (z - x.2)‖ₑ * ‖g x‖ₑ ^ r ∂volume :=
          lintegral_const_mul' _ _ hKc_top
      _ ≤ K0 ^ (r - 1) * ∫⁻ z in Cyl.cell c, ∫⁻ x, Ψ z x ∂volume :=
          mlpMulLeft (setLIntegral_mono' hCellm fun z hz =>
            lintegral_mono fun x => hP z hz x) _
      _ ≤ K0 ^ (r - 1) * ∫⁻ z, ∫⁻ x, Ψ z x ∂volume :=
          mlpMulLeft (setLIntegral_le_lintegral _ _) _
      _ = K0 ^ (r - 1) * ∫⁻ x, ∫⁻ z, Ψ z x ∂volume := by
          rw [lintegral_lintegral_swap hΨm]
      _ ≤ K0 ^ (r - 1) * ∫⁻ x, C2 * S.indicator F x ∂volume :=
          mlpMulLeft (lintegral_mono hZx) _
      _ = K0 ^ (r - 1) * (C2 * ∫⁻ x, S.indicator F x ∂volume) := by
          rw [lintegral_const_mul' C2 _ hC2top]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hKc_top
    (ENNReal.mul_ne_top hC2top hfinS)) hfinal

end UnforcedLeray.Short.IIb
