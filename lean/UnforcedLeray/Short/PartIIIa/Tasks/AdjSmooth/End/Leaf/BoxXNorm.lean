import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_4

/-!
# `PartIII-a` leaf: `BoxXNorm`

Source of record: `the November 2 reference manuscript` (SP) lines 2823-2827
(the `X_{m,c}` norm is `B0579.cellMeasure c m`) and lines 3060-3061.

Proof route. Let `T = [-c/2, c/2) × [-M, M]` (a subset of the cell). Every point of the box
`Metric.closedBall 0 M` is a translate `x + (-n c, 0)` of a point of `T` for some `n ∈ ℤ` with
`|n| ≤ N`, so the box is covered by finitely many preimages of `T`. Translation invariance of the
lintegral and `c`-periodicity give `∫_{translate} g = ∫_T g` for `g = ‖f‖ₑ²`, and on `T` the
density `jb^m` is bounded, which turns `∫_T g` into a bound by the weighted cell integral.
Only lintegral monotonicity, finite union bounds and translation invariance are used, so no
measurability of `f` is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Finite union bound for lintegrals over sets (no measurability of the integrand needed). -/
theorem lintegral_biUnion_finset_le_sum' {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    [DecidableEq ι] (g : α → ENNReal) (A : ι → Set α) (s : Finset ι) :
    ∫⁻ x in (⋃ i ∈ s, A i), g x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in A i, g x ∂μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le g _ _).trans (add_le_add le_rfl ih)

theorem boxXNorm : UnforcedLeray.Short.IIIa.BoxXNorm := by
  intro c m M hc
  set N : ℕ := ⌈(M + c) / c⌉₊ with hN
  have hNc : M + c ≤ (N : ℝ) * c := by
    have h1 : (M + c) / c ≤ (N : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hc] at h1
    exact h1
  set S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hS
  set D : ℝ := (1 + (c / 2) ^ 2 + M ^ 2) ^ |m| with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  refine ⟨((S.card : ℝ) * D) ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro f hf
  set g : ℝ × ℝ → ENNReal := fun x => ‖f x‖ₑ ^ (2 : ℝ) with hg
  set T : Set (ℝ × ℝ) := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-M) M with hT
  set w : ℤ → ℝ × ℝ := fun n => ((-(n : ℝ) * c), (0 : ℝ)) with hw
  -- periodicity under all integer shifts
  have hper : ∀ (n : ℤ) (x : ℝ × ℝ), f (x.1 + n * c, x.2) = f x := by
    intro n x
    have hp : Function.Periodic (fun t : ℝ => f (t, x.2)) c := fun t => hf (t, x.2)
    exact hp.int_mul n x.1
  -- translation invariance of the restricted lintegral for the periodic integrand
  have htrans : ∀ n : ℤ, ∫⁻ x in (fun x : ℝ × ℝ => x + w n) ⁻¹' T, g x ∂volume
      = ∫⁻ y in T, g y ∂volume := by
    intro n
    have hmp : MeasurePreserving (fun x : ℝ × ℝ => x + w n) volume volume :=
      measurePreserving_add_right volume _
    have hemb : MeasurableEmbedding (fun x : ℝ × ℝ => x + w n) :=
      (MeasurableEquiv.addRight (w n)).measurableEmbedding
    have hgper : ∀ y : ℝ × ℝ, g (y - w n) = g y := by
      intro y
      have hyw : y - w n = (y.1 + n * c, y.2) := by
        ext
        · simp [hw]
        · simp [hw]
      simp only [hg, hyw, hper n y]
    have key := hmp.setLIntegral_comp_preimage_emb hemb (fun y => g (y - w n)) T
    simp only [add_sub_cancel_right] at key
    rw [key]
    simp only [hgper]
  -- pointwise weight bound on `T`
  have hT_cell : T ⊆ UnforcedLeray.B0579.cell c := fun y hy => ⟨hy.1, mem_univ _⟩
  have hJ : ∀ y ∈ T, g y ≤ ENNReal.ofReal D *
      ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) := by
    intro y hy
    have hy1 : -(c / 2) ≤ y.1 ∧ y.1 < c / 2 := hy.1
    have hy2 : -M ≤ y.2 ∧ y.2 ≤ M := hy.2
    have hjb1 : 1 ≤ UnforcedLeray.B0579.jb y := by
      unfold UnforcedLeray.B0579.jb
      nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    have hjbB : UnforcedLeray.B0579.jb y ≤ 1 + (c / 2) ^ 2 + M ^ 2 := by
      unfold UnforcedLeray.B0579.jb
      have e1 : y.1 ^ 2 ≤ (c / 2) ^ 2 := sq_le_sq' (by linarith [hy1.1]) (le_of_lt hy1.2)
      have e2 : y.2 ^ 2 ≤ M ^ 2 := sq_le_sq' hy2.1 hy2.2
      linarith
    have hpow : UnforcedLeray.B0579.jb y ^ m ≤ D := by
      have a1 : UnforcedLeray.B0579.jb y ^ m ≤ UnforcedLeray.B0579.jb y ^ |m| :=
        Real.rpow_le_rpow_of_exponent_le hjb1 (le_abs_self m)
      have a2 : UnforcedLeray.B0579.jb y ^ |m| ≤ (1 + (c / 2) ^ 2 + M ^ 2) ^ |m| :=
        Real.rpow_le_rpow (by linarith) hjbB (abs_nonneg m)
      exact a1.trans a2
    have hprod : UnforcedLeray.B0579.density (-m) y * UnforcedLeray.B0579.density m y = 1 := by
      apply NNReal.eq
      rw [NNReal.coe_mul, UnforcedLeray.B0579.coe_density, UnforcedLeray.B0579.coe_density,
        ← Real.rpow_add (UnforcedLeray.B0579.jb_pos y), neg_add_cancel, Real.rpow_zero]
      simp
    have h1 : (UnforcedLeray.B0579.density (-m) y : ENNReal) *
        (UnforcedLeray.B0579.density m y : ENNReal) = 1 := by
      rw [← ENNReal.coe_mul, hprod, ENNReal.coe_one]
    have h2 : (UnforcedLeray.B0579.density m y : ENNReal) ≤ ENNReal.ofReal D := by
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      rw [UnforcedLeray.B0579.coe_density]
      exact hpow
    calc g y = ((UnforcedLeray.B0579.density (-m) y : ENNReal) *
          (UnforcedLeray.B0579.density m y : ENNReal)) * g y := by rw [h1, one_mul]
      _ ≤ ((UnforcedLeray.B0579.density (-m) y : ENNReal) * ENNReal.ofReal D) * g y := by
          gcongr
      _ = ENNReal.ofReal D * ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) := by ring
  -- the integral over `T` is bounded by the weighted cell integral
  have hTbound : ∫⁻ y in T, g y ∂volume ≤ ENNReal.ofReal D *
      ∫⁻ y in UnforcedLeray.B0579.cell c,
        ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) ∂volume := by
    have hTm : MeasurableSet T := measurableSet_Ico.prod measurableSet_Icc
    calc ∫⁻ y in T, g y ∂volume
        ≤ ∫⁻ y in T, ENNReal.ofReal D *
            ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) ∂volume :=
          setLIntegral_mono' hTm (fun y hy => hJ y hy)
      _ ≤ ∫⁻ y in UnforcedLeray.B0579.cell c, ENNReal.ofReal D *
            ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) ∂volume :=
          lintegral_mono_set hT_cell
      _ = ENNReal.ofReal D * ∫⁻ y in UnforcedLeray.B0579.cell c,
            ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) ∂volume :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- covering of the box by translates of `T`
  have hcov : Metric.closedBall (0 : ℝ × ℝ) M ⊆
      ⋃ n ∈ S, (fun x : ℝ × ℝ => x + w n) ⁻¹' T := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have hx1 : -M ≤ x.1 ∧ x.1 ≤ M := by
      have h1 : ‖x.1‖ ≤ M := (norm_fst_le x).trans hx
      rw [Real.norm_eq_abs] at h1
      exact abs_le.mp h1
    have hx2 : -M ≤ x.2 ∧ x.2 ≤ M := by
      have h1 : ‖x.2‖ ≤ M := (norm_snd_le x).trans hx
      rw [Real.norm_eq_abs] at h1
      exact abs_le.mp h1
    set n : ℤ := ⌊(x.1 + c / 2) / c⌋ with hn
    have hfl1 : (n : ℝ) ≤ (x.1 + c / 2) / c := Int.floor_le _
    have hfl2 : (x.1 + c / 2) / c < (n : ℝ) + 1 := Int.lt_floor_add_one _
    have h1 : (n : ℝ) * c ≤ x.1 + c / 2 := (le_div_iff₀ hc).1 hfl1
    have h2 : x.1 + c / 2 < (n : ℝ) * c + c := by
      have := (div_lt_iff₀ hc).1 hfl2
      linarith
    have hnle : (n : ℝ) ≤ N := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have hnge : -(N : ℝ) ≤ (n : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have hn1 : (n : ℝ) + 1 ≤ -(N : ℝ) := by
        have : n + 1 ≤ -(N : ℤ) := by
          have : n < -(N : ℤ) := by exact_mod_cast hcon
          omega
        exact_mod_cast this
      have h3 := mul_le_mul_of_nonneg_right hn1 hc.le
      nlinarith
    have hnS : n ∈ S := by
      rw [hS, Finset.mem_Icc]
      constructor
      · have : (-(N : ℤ) : ℝ) ≤ (n : ℝ) := by push_cast; exact hnge
        exact_mod_cast this
      · exact_mod_cast hnle
    refine mem_iUnion₂.2 ⟨n, hnS, ?_⟩
    simp only [mem_preimage, hT, hw, mem_prod, mem_Ico, mem_Icc, Prod.fst_add, Prod.snd_add,
      add_zero]
    exact ⟨⟨by linarith [h1], by linarith [h2]⟩, hx2⟩
  -- union bound, translation, and the periodic bound
  have hI : ∫⁻ x in Metric.closedBall (0 : ℝ × ℝ) M, g x ∂volume ≤
      ENNReal.ofReal ((S.card : ℝ) * D) *
        ∫⁻ y in UnforcedLeray.B0579.cell c,
          ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) ∂volume := by
    have hC : ∑ n ∈ S, ∫⁻ x in (fun x : ℝ × ℝ => x + w n) ⁻¹' T, g x ∂volume ≤
        ∑ n ∈ S, ENNReal.ofReal D *
          ∫⁻ y in UnforcedLeray.B0579.cell c,
            ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) ∂volume := by
      apply Finset.sum_le_sum
      intro n _
      rw [htrans n]
      exact hTbound
    rw [Finset.sum_const, nsmul_eq_mul] at hC
    calc ∫⁻ x in Metric.closedBall (0 : ℝ × ℝ) M, g x ∂volume
        ≤ ∫⁻ x in ⋃ n ∈ S, (fun x : ℝ × ℝ => x + w n) ⁻¹' T, g x ∂volume :=
          lintegral_mono_set hcov
      _ ≤ ∑ n ∈ S, ∫⁻ x in (fun x : ℝ × ℝ => x + w n) ⁻¹' T, g x ∂volume :=
          lintegral_biUnion_finset_le_sum' volume g _ S
      _ ≤ _ := hC
      _ = ENNReal.ofReal ((S.card : ℝ) * D) *
            ∫⁻ y in UnforcedLeray.B0579.cell c,
              ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) ∂volume := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]
  -- the two `eLpNorm`s in terms of the lintegrals
  have hEbox : eLpNorm f 2 (volume.restrict (Metric.closedBall (0 : ℝ × ℝ) M)) =
      (∫⁻ x in Metric.closedBall (0 : ℝ × ℝ) M, g x ∂volume) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      ENNReal.toReal_ofNat]
  have hEc : eLpNorm f 2 (UnforcedLeray.B0579.cellMeasure c (-m)) =
      (∫⁻ y in UnforcedLeray.B0579.cell c,
        ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) ∂volume) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      ENNReal.toReal_ofNat, UnforcedLeray.B0579.cellMeasure,
      lintegral_withDensity_eq_lintegral_mul_non_measurable _
        (UnforcedLeray.B0579.measurable_density (-m)).coe_nnreal_ennreal
        (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
    rfl
  have hX0 : 0 ≤ (S.card : ℝ) * D := by positivity
  unfold xNorm
  rw [hEc]
  rw [hEbox]
  calc (∫⁻ x in Metric.closedBall (0 : ℝ × ℝ) M, g x ∂volume) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((S.card : ℝ) * D) *
          ∫⁻ y in UnforcedLeray.B0579.cell c,
            ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) ∂volume) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hI (by norm_num)
    _ = ENNReal.ofReal (((S.card : ℝ) * D) ^ (1 / 2 : ℝ)) *
          (∫⁻ y in UnforcedLeray.B0579.cell c,
            ((UnforcedLeray.B0579.density (-m) y : ENNReal) * g y) ∂volume) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hX0 (by norm_num)]

end UnforcedLeray.Short.IIIa
