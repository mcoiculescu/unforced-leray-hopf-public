import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3
import UnforcedLeray.Lib.CylinderB.Leray

/-!


Source of record: `the November 2 reference manuscript`, lines 1684-1689.

Method: the gradient map `ψ ↦ ∇ψ` sends cylinder tests into the separable Hilbert-type space
`L²(cell; ℝ²)` (`UnforcedLeray.Cyl.L2v c`, `Lp Vec2 2 (cellμ c)`, second countable because
`cellμ c` is a restricted Lebesgue measure).  A countable dense subset of the image gives, after
choosing a preimage test for each point, a countable family `D` of tests.  The pointwise bound
`‖L‖ ≤ 2 max(|L e₁|,|L e₂|)` for the operator norm of a difference of derivatives converts the
`L²` distance of gradients into the `∫⁻ ‖fderiv ψ - fderiv ψ'‖ₑ²` bound required by `CylDense`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.Sub

/-- A linear form `L` with `L v = v₁ a + v₂ b` and `|a|, |b| ≤ N` has `‖L‖ ≤ 2 N`. -/
private lemma cd_opNorm_le (L : ℝ × ℝ →L[ℝ] ℝ) (a b N : ℝ) (hN : 0 ≤ N)
    (hL : ∀ v : ℝ × ℝ, L v = v.1 * a + v.2 * b) (ha : |a| ≤ N) (hb : |b| ≤ N) :
    ‖L‖ ≤ 2 * N := by
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) fun v => ?_
  rw [hL, Real.norm_eq_abs]
  have hv1 : |v.1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le v
  have hv2 : |v.2| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le v
  calc |v.1 * a + v.2 * b| ≤ |v.1 * a| + |v.2 * b| := abs_add_le _ _
    _ = |v.1| * |a| + |v.2| * |b| := by rw [abs_mul, abs_mul]
    _ ≤ ‖v‖ * N + ‖v‖ * N :=
        add_le_add (mul_le_mul hv1 ha (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul hv2 hb (abs_nonneg _) (norm_nonneg _))
    _ = 2 * N * ‖v‖ := by ring

/-- Pointwise: the `ℓ²`-type gradient distance dominates the operator-norm distance. -/
private lemma cd_pointwise {c : ℝ} {ψ ψ' : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.Sob.IsCylTest c ψ)
    (hψ' : UnforcedLeray.Sob.IsCylTest c ψ') (z : ℝ × ℝ) :
    ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ₑ ^ 2 ≤
      4 * ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT ψ' z‖ₑ ^ (2 : ℝ) := by
  have hL : ∀ v : ℝ × ℝ, (fderiv ℝ ψ z - fderiv ℝ ψ' z) v =
      v.1 * (UnforcedLeray.Cyl.partialQ ψ z - UnforcedLeray.Cyl.partialQ ψ' z) +
        v.2 * (UnforcedLeray.Cyl.partialEta ψ z - UnforcedLeray.Cyl.partialEta ψ' z) := by
    intro v
    rw [ContinuousLinearMap.sub_apply, UnforcedLeray.Cyl.fderiv_apply_eq_partial hψ.differentiable,
      UnforcedLeray.Cyl.fderiv_apply_eq_partial hψ'.differentiable]
    ring
  have hp0 : (UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT ψ' z) 0 =
      UnforcedLeray.Cyl.partialQ ψ z - UnforcedLeray.Cyl.partialQ ψ' z := by
    simp [UnforcedLeray.Cyl.gradT, UnforcedLeray.Cyl.vec]
  have hp1 : (UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT ψ' z) 1 =
      UnforcedLeray.Cyl.partialEta ψ z - UnforcedLeray.Cyl.partialEta ψ' z := by
    simp [UnforcedLeray.Cyl.gradT, UnforcedLeray.Cyl.vec]
  have hb := cd_opNorm_le (fderiv ℝ ψ z - fderiv ℝ ψ' z)
    (UnforcedLeray.Cyl.partialQ ψ z - UnforcedLeray.Cyl.partialQ ψ' z)
    (UnforcedLeray.Cyl.partialEta ψ z - UnforcedLeray.Cyl.partialEta ψ' z)
    ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT ψ' z‖ (norm_nonneg _) hL
    (by rw [← hp0, ← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ 0)
    (by rw [← hp1, ← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ 1)
  have hL' : ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ₑ ≤
      2 * ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT ψ' z‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    calc ENNReal.ofReal ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖
        ≤ ENNReal.ofReal (2 * ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT ψ' z‖) :=
          ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal 2 * ENNReal.ofReal ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT ψ' z‖ :=
          ENNReal.ofReal_mul (by norm_num)
      _ = 2 * ENNReal.ofReal ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT ψ' z‖ := by
          rw [ENNReal.ofReal_ofNat]
  calc ‖fderiv ℝ ψ z - fderiv ℝ ψ' z‖ₑ ^ 2 ≤ (2 * ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT ψ' z‖ₑ) ^ 2 := by
        gcongr
    _ = 4 * ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT ψ' z‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.rpow_two, mul_pow]
        norm_num

/-- The Prop `CylDense` (source lines 1684-1689). -/
theorem cylDense : UnforcedLeray.Short.PartIIa.N01.Sub.CylDense := by
  intro c hc
  classical
  haveI hne : Nonempty {ψ : ℝ × ℝ → ℝ // UnforcedLeray.Sob.IsCylTest c ψ} :=
    ⟨⟨fun _ => 0, ⟨contDiff_const, fun _ => rfl, 0, fun _ _ => rfl⟩⟩⟩
  let Φ : {ψ : ℝ × ℝ → ℝ // UnforcedLeray.Sob.IsCylTest c ψ} → UnforcedLeray.Cyl.L2v c :=
    fun ψ => (UnforcedLeray.Cyl.memLp_gradT ψ.2).toLp _
  have hsep : TopologicalSpace.IsSeparable (Set.range Φ) :=
    TopologicalSpace.IsSeparable.mono
      (TopologicalSpace.isSeparable_univ_iff.2 inferInstance) (Set.subset_univ _)
  obtain ⟨t, hts, htc, hst⟩ := hsep.exists_countable_dense_subset
  have hpre : ∀ g ∈ t, ∃ ψ, Φ ψ = g := fun g hg => by
    obtain ⟨ψ, hψ⟩ := hts hg
    exact ⟨ψ, hψ⟩
  choose! pickS hpickS using hpre
  refine ⟨(fun g => (pickS g).1) '' t, htc.image _, ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact (pickS g).2
  · intro ψ hψ ε hε
    have hmem : Φ ⟨ψ, hψ⟩ ∈ closure t := hst ⟨⟨ψ, hψ⟩, rfl⟩
    have hδ : 0 < Real.sqrt ε / 4 := div_pos (Real.sqrt_pos.2 hε) (by norm_num)
    obtain ⟨g, hgt, hdist⟩ :=
      EMetric.mem_closure_iff.1 hmem (ENNReal.ofReal (Real.sqrt ε / 4)) (ENNReal.ofReal_pos.2 hδ)
    have hg : Φ (pickS g) = g := hpickS g hgt
    refine ⟨(pickS g).1, ⟨g, hgt, rfl⟩, ?_⟩
    rw [← hg, MeasureTheory.Lp.edist_def] at hdist
    have h1 : ⇑(Φ ⟨ψ, hψ⟩) =ᵐ[UnforcedLeray.Cyl.cellμ c] UnforcedLeray.Cyl.gradT ψ :=
      (UnforcedLeray.Cyl.memLp_gradT hψ).coeFn_toLp
    have h2 : ⇑(Φ (pickS g)) =ᵐ[UnforcedLeray.Cyl.cellμ c]
        UnforcedLeray.Cyl.gradT (pickS g).1 :=
      (UnforcedLeray.Cyl.memLp_gradT (pickS g).2).coeFn_toLp
    have hae : (⇑(Φ ⟨ψ, hψ⟩) - ⇑(Φ (pickS g))) =ᵐ[UnforcedLeray.Cyl.cellμ c]
        fun z => UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT (pickS g).1 z := by
      filter_upwards [h1, h2] with z e1 e2
      rw [Pi.sub_apply, e1, e2]
    rw [eLpNorm_congr_ae hae, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
      ENNReal.ofNat_ne_top] at hdist
    simp only [ENNReal.toReal_ofNat] at hdist
    have hsq : ∫⁻ z in UnforcedLeray.Cyl.cell c,
        ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT (pickS g).1 z‖ₑ ^ (2 : ℝ) <
          ENNReal.ofReal (Real.sqrt ε / 4) ^ (2 : ℝ) := by
      have h := ENNReal.rpow_lt_rpow hdist (by norm_num : (0 : ℝ) < 2)
      rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = (1 : ℝ) by norm_num,
        ENNReal.rpow_one] at h
      exact h
    have hnum : (4 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt ε / 4) ^ (2 : ℝ) =
        ENNReal.ofReal (ε / 4) := by
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hδ.le,
        show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      have h2 := Real.sq_sqrt hε.le
      rw [div_pow, h2]
      ring
    calc ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖fderiv ℝ ψ z - fderiv ℝ (pickS g).1 z‖ₑ ^ 2
        ≤ ∫⁻ z in UnforcedLeray.Cyl.cell c,
            4 * ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT (pickS g).1 z‖ₑ ^ (2 : ℝ) :=
          lintegral_mono fun z => cd_pointwise hψ (pickS g).2 z
      _ = 4 * ∫⁻ z in UnforcedLeray.Cyl.cell c,
            ‖UnforcedLeray.Cyl.gradT ψ z - UnforcedLeray.Cyl.gradT (pickS g).1 z‖ₑ ^ (2 : ℝ) :=
          lintegral_const_mul' _ _ (by norm_num)
      _ < 4 * ENNReal.ofReal (Real.sqrt ε / 4) ^ (2 : ℝ) :=
          ENNReal.mul_lt_mul_right (show (4 : ℝ≥0∞) ≠ 0 by norm_num) (show (4 : ℝ≥0∞) ≠ ⊤ by norm_num) hsq
      _ = ENNReal.ofReal (ε / 4) := hnum
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

end UnforcedLeray.Short.PartIIa.N01.Sub
