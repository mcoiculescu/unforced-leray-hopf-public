import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Transfer
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.MultYoung
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.HtUng

/-!
# `PartIII-b:C/rep/4/4/1/org/3/org` (a): window norms, the late-output gain, the multiplier

Source `the November 2 reference manuscript` 5312-5316 (both transitions are
supported on `0.8/ν < s < 1/ν`), 5317-5318 (late output `g(s)^{-1} ≤ e^{-4γ/(9ν)}`), 5322-5333 (the
table is "in the split stress norm" `‖g⁻¹T‖_Z = ‖g⁻¹T₁‖_{Z₁} + ρ_b^{-1/2}‖g⁻¹T₂‖_{H_T}`, 2697-2700,
5609), 2706, 3876-3878 (`M_Uw = U⊗w + w⊗U`, thin part with `V`, repair part with `r_b`, pointwise in
the chart point), 2683 (`𝒩_v b = √s b`).

The tools of the repair-source transition table (all proved here):

* the ungained window norms: `z1Ung` (`LateRepThinOrg/Transfer.lean`) on the thin receiver and
  `htUng` (the norm of `ρ_b^{-1/2}H_T` without the gain) on the repair receiver;
* the gain transfer on the repair receiver `tt_gainHT_le` (the `H_T` analogue of `lrt_gainZ1_le`):
  a repair stress vanishing at ages `s < 0.8/ν` has gained norm at most `e^{-4γ/(9ν)}` times its
  ungained norm (`lrt_ginv_late`, the local copy of `ftGain_late`, 5318);
* the majorant norms `z1Maj`, `htMaj` of nonnegative chart functions and the chart majorant
  `multMaj R A f p = |a(p)| s^{-1/2} f(τ(p), y(p))` of `M_A` applied to the chart coefficient of a
  physical field dominated by `f` (`a = IIIa.chartCoeff R A`); `tt_pt_le`, `tt_L2_le` pass from a
  pointwise domination of the physical field to the window norms of the multiplied coefficient;
* `tt_reps_ae`, `tt_oldPhys_ae`: two representatives of the old repair source have a.e. equal
  physical lifts (`chartOfNullPullback`), so they have the same separated responses
  (`sepWCongrAE`);
* `tt_chain`: a four-step `ENNReal` chain.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Window norms -/

/-- The `Z₁` norm without the gain of a nonnegative chart function (source 2697). -/
def z1Maj (c mZ : ℝ) (h : Chart → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ p, h p ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ)

/-- The `ρ_b^{-1/2}H_T` norm without the gain of a nonnegative chart function (source 2698-2700). -/
def htMaj (c ρb : ℝ) (h : Chart → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ p, h p ^ (2 : ℝ) ∂(htRhoMeasure c ρb)) ^ (1 / 2 : ℝ)

/-- **The chart majorant of a multiplied coefficient** (source 2706, 3876-3878, 2683): for a
background field `A` (`A = V` on the thin receiver, `A = r_b` on the repair receiver) and a
majorant `f ≥ |F|` of a physical field `F`, `|M_A(coefOf F)(p)| ≤ 2|a(p)||coefOf F(p)| ≤
2|a(p)| s^{-1/2} f(τ(p), y(p))` with `a = IIIa.chartCoeff R A`; `multMaj` is the right side
without the factor `2`. -/
def multMaj (R : ℝ) (A : ℝ → Space → Space) (f : ℝ → Space → ℝ≥0∞) (p : Chart) : ℝ≥0∞ :=
  ENNReal.ofReal (‖IIIa.chartCoeff R A p‖ * (Real.sqrt p.1)⁻¹) *
    f (NearInst.chartTau R p) (NearInst.chartY R p)

/-! ## 2. The gain transfer on the repair receiver -/

/-- **The gain transfer on `H_T`, general form** (source 5318, 5322-5333): if `g⁻¹ ≤ B` a.e. on
the support of a repair stress `f`, then `ρ_b^{-1/2}‖g⁻¹f‖_{H_T} ≤ B ρ_b^{-1/2}‖f‖_{H_T}`. -/
theorem tt_gainHT_le_ae {c ρb γ ν B : ℝ} (hB : 0 ≤ B)
    (f : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))
    (hfg : ∀ᵐ p ∂(gainHTMeasure c ρb γ ν), (f : Chart → Ten3) p ≠ 0 → ginv γ ν p ≤ B) :
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal B * htUng c ρb f := by
  have hf' : ∀ᵐ p ∂(htRhoMeasure c ρb), (f : Chart → Ten3) p ≠ 0 → ginv γ ν p ≤ B := by
    rw [← NearInst.ae_gainHTMeasure c ρb γ ν]; exact hfg
  have hd : Measurable fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((NearInst.ginv_measurable' γ ν).pow_const 2)
  have e1 : ENNReal.ofReal ‖f‖ =
      (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainHTMeasure c ρb γ ν)) ^ (1 / 2 : ℝ) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have step1 : ∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainHTMeasure c ρb γ ν) ≤
      ∫⁻ p, ENNReal.ofReal (B ^ 2) * ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(htRhoMeasure c ρb) := by
    refine le_trans (lintegral_withDensity_le_lintegral_mul (htRhoMeasure c ρb) hd
      (fun p => ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ))) (lintegral_mono_ae (hf'.mono fun p hp => ?_))
    simp only [Pi.mul_apply]
    by_cases ha : (f : Chart → Ten3) p = 0
    · rw [ha]; simp
    · have h1 : ginv γ ν p ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (NearInst.ginv_pos' γ ν p).le (hp ha) 2
      gcongr
  rw [e1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at *
  unfold htUng
  calc (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainHTMeasure c ρb γ ν)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (B ^ 2) *
          ∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(htRhoMeasure c ρb)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow step1 (by norm_num)
    _ = ENNReal.ofReal B *
          (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(htRhoMeasure c ρb)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg B) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hB]

/-- **The gain transfer on `H_T` on an age region** (source 5318): a repair stress vanishing at
ages `s < a` has `ρ_b^{-1/2}‖g⁻¹f‖_{H_T} ≤ B ρ_b^{-1/2}‖f‖_{H_T}` whenever `g(s)^{-1} ≤ B` for
`s ≥ a` (late output: `a = 0.8/ν`, `B = e^{-4γ/(9ν)}`). -/
theorem tt_gainHT_le {c ρb γ ν a B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ p : Chart, a ≤ p.1 → ginv γ ν p ≤ B)
    (f : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))
    (hf : ∀ᵐ p ∂(gainHTMeasure c ρb γ ν), p.1 < a → (f : Chart → Ten3) p = 0) :
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal B * htUng c ρb f := by
  refine tt_gainHT_le_ae hB f (hf.mono fun p hp hne => hg p ?_)
  by_contra h
  exact hne (hp (lt_of_not_ge h))

/-! ## 3. Pointwise multiplier bounds -/

/-- `|a ⊗ b + b ⊗ a| ≤ 2|a||b|`. -/
theorem tt_ten3_symOuter_norm_le (a b : Merid) :
    ‖NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a b)‖ ≤ 2 * ‖a‖ * ‖b‖ := by
  have h1 := NearInst.CoeffMult.norm_sq_ten3Of (UnforcedLeray.Short.IIIa.symOuter a b)
  have h2 := NearInst.CoeffMult.frobSq_symOuter_le' a b
  have h3 : ‖NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a b)‖ ^ 2 ≤
      (2 * ‖a‖ * ‖b‖) ^ 2 := by
    rw [h1]; nlinarith [h2]
  exact le_of_sq_le_sq h3 (by positivity)

/-- `a ⊗ 0 + 0 ⊗ a = 0`. -/
theorem tt_ten3_symOuter_zero (a : Merid) :
    NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a 0) = 0 := by
  have h := NearInst.CoeffMult.ten3_symOuter_smul a 0 0
  simpa using h

/-- The chart coefficient `s^{-1/2}(F_r, F_z)` is at most `s^{-1/2}|F|` (source 2683). -/
theorem tt_coefOf_norm_le (R : ℝ) (F : ℝ → Space → Space) (p : Chart) :
    ‖coefOf R F p‖ ≤
      (Real.sqrt p.1)⁻¹ * ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖ := by
  unfold coefOf
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
  set x := F (NearInst.chartTau R p) (NearInst.chartY R p)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp
  nlinarith [sq_nonneg (x 1)]

/-- **The multiplied coefficient below its chart majorant** (source 2683, 2706, 3876-3878): if
`|F(τ,y)| ≤ K f(τ,y)` at the chart point of `p`, then
`|a ⊗ coefOf F + coefOf F ⊗ a|(p) ≤ 2K · |a| s^{-1/2} f(τ(p), y(p))`. -/
theorem tt_pt_le (R : ℝ) (a : Merid) (F : ℝ → Space → Space) (p : Chart) {K : ℝ} (hK : 0 ≤ K)
    {m : ℝ≥0∞}
    (h : ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖ₑ ≤ ENNReal.ofReal K * m) :
    ‖NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a (coefOf R F p))‖ₑ ≤
      ENNReal.ofReal (2 * K) * (ENNReal.ofReal (‖a‖ * (Real.sqrt p.1)⁻¹) * m) := by
  have h1 : ‖NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a (coefOf R F p))‖ ≤
      2 * (‖a‖ * (Real.sqrt p.1)⁻¹) * ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖ := by
    have h2 := tt_ten3_symOuter_norm_le a (coefOf R F p)
    have h3 := tt_coefOf_norm_le R F p
    calc _ ≤ 2 * ‖a‖ * ‖coefOf R F p‖ := h2
      _ ≤ 2 * ‖a‖ * ((Real.sqrt p.1)⁻¹ *
            ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖) := by gcongr
      _ = _ := by ring
  have h0 : 0 ≤ ‖a‖ * (Real.sqrt p.1)⁻¹ := by positivity
  rw [← ofReal_norm]
  calc ENNReal.ofReal ‖NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a (coefOf R F p))‖
      ≤ ENNReal.ofReal (2 * (‖a‖ * (Real.sqrt p.1)⁻¹) *
          ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal 2 * ENNReal.ofReal (‖a‖ * (Real.sqrt p.1)⁻¹) *
          ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖ₑ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ofReal_norm]
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (‖a‖ * (Real.sqrt p.1)⁻¹) *
          (ENNReal.ofReal K * m) := by gcongr
    _ = ENNReal.ofReal (2 * K) * (ENNReal.ofReal (‖a‖ * (Real.sqrt p.1)⁻¹) * m) := by
        rw [ENNReal.ofReal_mul (p := 2) (q := K) (by norm_num)]; ring

/-- **From a pointwise a.e. domination to the window norms** (any chart measure):
`|f| ≤ K h` a.e. gives `(∫|f|²)^{1/2} ≤ K (∫h²)^{1/2}`. -/
theorem tt_L2_le (μ : Measure Chart) {f : Chart → Ten3} {h : Chart → ℝ≥0∞} {K : ℝ}
    (hf : ∀ᵐ p ∂μ, ‖f p‖ₑ ≤ ENNReal.ofReal K * h p) :
    (∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal K * (∫⁻ p, h p ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have h1 : ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ ≤
      ∫⁻ p, ENNReal.ofReal K ^ (2 : ℝ) * h p ^ (2 : ℝ) ∂μ := by
    refine lintegral_mono_ae (hf.mono fun p hp => ?_)
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.rpow_le_rpow hp (by norm_num)
  rw [lintegral_const_mul' _ _
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)] at h1
  calc (∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal K ^ (2 : ℝ) * ∫⁻ p, h p ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul]
      norm_num

/-! ## 4. Representatives of the old repair source -/

/-- **Two representatives of the old repair source agree a.e.** (source 5153-5157): for
representatives `g₁, g₂` of `χ_o(0, (M_Uw)₂)`, `g₁ + g₂ = repSrcTen w` for a.e. chart point
(`OldRepIsRep`: the thin component is `0`, the repair component `repSrcTen w`). -/
theorem tt_reps_ae (hI : OldRepIsRep) (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hρ : 0 < L.ρb Pl K) (w : LVel Pl L) {g₁ g₂ : Chart → Ten3}
    (hg : IsRep Pl K L (oldRep Pl K L w) g₁ g₂) :
    (g₁ + g₂) =ᵐ[ageμ (cOf L.ν) (-1 / 2)] repSrcTen Pl K L w := by
  obtain ⟨h1, h2⟩ := hI Pl K L w
  have a1 : g₁ =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν] 0 := hg.1.symm.trans h1
  have a2 : g₂ =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν] repSrcTen Pl K L w :=
    hg.2.symm.trans h2
  have b1 : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), g₁ p = (0 : Chart → Ten3) p := by
    have h := a1
    unfold EventuallyEq at h
    rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h
    exact h
  have b2 : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), g₂ p = repSrcTen Pl K L w p := by
    have h := a2
    unfold EventuallyEq at h
    rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at h
    exact h
  filter_upwards [b1, b2] with p e1 e2
  simp only [Pi.add_apply, e1, e2, Pi.zero_apply, zero_add]

/-- **A.e. equal chart tensors have a.e. equal physical lifts** (source 2666-2683): the lift
`oldPhys R c G` at `(τ, z)` reads `G` at `chartOf R c z τ`, and chart-null sets pull back to null
sets (`chartOfNullPullback`). -/
theorem tt_oldPhys_ae {R c : ℝ} (hR : 0 < R) (hc : 0 < c) {G G' : Chart → Ten3}
    (h : G =ᵐ[ageμ c (-1 / 2)] G') :
    ∀ᵐ x : ℝ × Space ∂volume, oldPhys R c G x.1 x.2 = oldPhys R c G' x.1 x.2 := by
  filter_upwards [chartOfNullPullback R c hR hc _ (ae_iff.1 h)] with x hx
  have hx' : G (NearInst.chartOf R c x.2 x.1) = G' (NearInst.chartOf R c x.2 x.1) := by
    by_contra hne
    exact hx hne
  unfold oldPhys NearInst.cartLift
  rw [hx']

/-! ## 5. Bookkeeping -/

/-- A four-step `ENNReal` chain read back in `ℝ`. -/
theorem tt_chain {x e1 e2 e3 X : ℝ} {A B C : ℝ≥0∞}
    (h1 : ENNReal.ofReal x ≤ ENNReal.ofReal e1 * A) (h2 : A ≤ ENNReal.ofReal e2 * B)
    (h3 : B ≤ ENNReal.ofReal e3 * C) (h4 : C ≤ ENNReal.ofReal X)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3) (hX : 0 ≤ X) :
    x ≤ e1 * e2 * e3 * X := by
  have hA : A ≤ ENNReal.ofReal e2 * (ENNReal.ofReal e3 * ENNReal.ofReal X) := by
    calc A ≤ ENNReal.ofReal e2 * B := h2
      _ ≤ ENNReal.ofReal e2 * (ENNReal.ofReal e3 * C) := by gcongr
      _ ≤ ENNReal.ofReal e2 * (ENNReal.ofReal e3 * ENNReal.ofReal X) := by gcongr
  have h : ENNReal.ofReal x ≤ ENNReal.ofReal (e1 * e2 * e3 * X) := by
    calc ENNReal.ofReal x ≤ ENNReal.ofReal e1 * A := h1
      _ ≤ ENNReal.ofReal e1 * (ENNReal.ofReal e2 * (ENNReal.ofReal e3 * ENNReal.ofReal X)) := by
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg he1 he2) he3),
            ENNReal.ofReal_mul (mul_nonneg he1 he2), ENNReal.ofReal_mul he1]
          ring
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (mul_nonneg he1 he2) he3) hX)).1 h

end UnforcedLeray.Short.PartIIIb.Concrete
