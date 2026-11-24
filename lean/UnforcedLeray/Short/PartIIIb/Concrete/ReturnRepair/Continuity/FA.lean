import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FATermSummable
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields

/-!
# The leaf `FACont`: `F_A` is norm continuous in `μ` (source 4957-4985, 5703)

`F_A = s^{3/2} f_A` and `f_A` depends on `μ` only through `B = (A^y)' + μA^y/s`, which is affine in
`μ`.  For two window points `μ₁ < μ₂` and `t(μ) = (μ-μ₁)/(μ₂-μ₁)` one has the pointwise identity
`FAcoef μ = (1-t) FAcoef μ₁ + t FAcoef μ₂` (the lattice sums are summable by `fATermSummable`, so
`tsum` is linear), and pin uniqueness (`Lp.ext`) lifts it to `FAOp μ = (1-t) FAOp μ₁ + t FAOp μ₂`.
The weight `t(μ)` is continuous, so `μ ↦ FAOp μ` is continuous on the window.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Linearity of the lattice-term building blocks -/

theorem merApply_comb_fa (a b : ℝ) (B₁ B₂ : Mat3) (x : ℝ × ℝ) :
    merApply (a • B₁ + b • B₂) x = a • merApply B₁ x + b • merApply B₂ x := by
  unfold merApply
  refine Prod.ext ?_ ?_ <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd] <;> ring

theorem mv_comb_fa (a b : ℝ) (B₁ B₂ : Mat3) (v : Vec3) :
    mv (a • B₁ + b • B₂) v = a • mv B₁ v + b • mv B₂ v := by
  funext i
  simp only [mv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem emb_comb_fa (a b : ℝ) (u v : ℝ × ℝ) : emb (a • u + b • v) = a • emb u + b • emb v := by
  funext i
  fin_cases i <;> simp [emb]

theorem Bmat_comb_fa (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) {μ μ₁ μ₂ t : ℝ}
    (hlin : (1 - t) * μ₁ + t * μ₂ = μ) :
    Bmat ν μ χ A s = (1 - t) • Bmat ν μ₁ χ A s + t • Bmat ν μ₂ χ A s := by
  have h : μ / s = (1 - t) * (μ₁ / s) + t * (μ₂ / s) := by
    rw [← hlin]; ring
  unfold Bmat
  rw [h]
  module

theorem fATerm_comb_fa (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ)
    {μ μ₁ μ₂ t : ℝ} (hlin : (1 - t) * μ₁ + t * μ₂ = μ) :
    fATerm ν μ χ A s x j = (1 - t) • fATerm ν μ₁ χ A s x j + t • fATerm ν μ₂ χ A s x j := by
  unfold fATerm
  rw [Bmat_comb_fa ν χ A s hlin, merApply_comb_fa, map_add, map_smul, map_smul, emb_comb_fa,
    mv_comb_fa]
  module

/-! ## 2. Linearity of the summed field -/

theorem fA_comb_fa (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    {μ μ₁ μ₂ t : ℝ} (hlin : (1 - t) * μ₁ + t * μ₂ = μ)
    (h₁ : Summable (fATerm ν μ₁ χ A s x)) (h₂ : Summable (fATerm ν μ₂ χ A s x)) :
    fA ν μ χ A s x = (1 - t) • fA ν μ₁ χ A s x + t • fA ν μ₂ χ A s x := by
  show -(∑' j, fATerm ν μ χ A s x j) = (1 - t) • -(∑' j, fATerm ν μ₁ χ A s x j)
    + t • -(∑' j, fATerm ν μ₂ χ A s x j)
  have e : ∑' j, fATerm ν μ χ A s x j
      = (1 - t) • ∑' j, fATerm ν μ₁ χ A s x j + t • ∑' j, fATerm ν μ₂ χ A s x j := by
    rw [tsum_congr (fun j => fATerm_comb_fa ν χ A s x j hlin),
      Summable.tsum_add (h₁.const_smul (1 - t)) (h₂.const_smul t),
      h₁.tsum_const_smul (1 - t), h₂.tsum_const_smul t]
  rw [e]
  module

theorem FA_comb_fa (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    {μ μ₁ μ₂ t : ℝ} (hlin : (1 - t) * μ₁ + t * μ₂ = μ)
    (h₁ : Summable (fATerm ν μ₁ χ A s x)) (h₂ : Summable (fATerm ν μ₂ χ A s x)) :
    FA ν μ χ A s x = (1 - t) • FA ν μ₁ χ A s x + t • FA ν μ₂ χ A s x := by
  unfold FA
  rw [fA_comb_fa ν χ A s x hlin h₁ h₂]
  module

/-- The coefficient `F_A` is affine in `μ`, pointwise on the chart. -/
theorem FAcoef_comb_apply (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (hν : 0 < ν)
    {μ μ₁ μ₂ t : ℝ} (hlin : (1 - t) * μ₁ + t * μ₂ = μ) (p : Chart) :
    FAcoef ν μ χ A p = (1 - t) • FAcoef ν μ₁ χ A p + t • FAcoef ν μ₂ χ A p := by
  rcases lt_or_ge 0 p.1 with hs | hs
  · unfold FAcoef
    rw [FA_comb_fa ν χ A p.1 p.2 hlin (fATermSummable ν μ₁ χ A p.1 p.2 hν hs)
      (fATermSummable ν μ₂ χ A p.1 p.2 hν hs)]
    simp only [smul_add, affMerOf_add, affMerOf_smul]
    module
  · have h0 : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.mpr hs
    simp only [FAcoef, h0, inv_zero, zero_smul]
    module

/-- The coefficient `F_A` is affine in `μ` (as an element of the chart-function space). -/
theorem FAcoef_comb (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (hν : 0 < ν)
    {μ μ₁ μ₂ t : ℝ} (hlin : (1 - t) * μ₁ + t * μ₂ = μ) :
    FAcoef ν μ χ A = (1 - t) • FAcoef ν μ₁ χ A + t • FAcoef ν μ₂ χ A := by
  funext p
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  exact FAcoef_comb_apply ν χ A hν hlin p

/-! ## 3. Operators: pin uniqueness gives affinity of `F_A` in `μ` -/

/-- If `F_A` is pinned at `μ₁, μ₂, μ` and `μ = (1-t)μ₁ + tμ₂`, then `FAOp μ = (1-t)FAOp μ₁ + tFAOp μ₂`. -/
theorem FAOp_comb (K : ReturnConsts) (L : ReturnLevel) {μ₁ μ₂ μ t : ℝ}
    (hlin : (1 - t) * μ₁ + t * μ₂ = μ)
    (h₁ : ∃ F : AffSp K.as →L[ℝ] LSrc L, ∀ A,
      (F A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)] FAcoef L.ν μ₁ K.χf (affIota K.as A))
    (h₂ : ∃ F : AffSp K.as →L[ℝ] LSrc L, ∀ A,
      (F A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)] FAcoef L.ν μ₂ K.χf (affIota K.as A))
    (h : ∃ F : AffSp K.as →L[ℝ] LSrc L, ∀ A,
      (F A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)] FAcoef L.ν μ K.χf (affIota K.as A)) :
    FAOp K L μ = (1 - t) • FAOp K L μ₁ + t • FAOp K L μ₂ := by
  have e₀ : ∀ A, (FAOp K L μ A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
      FAcoef L.ν μ K.χf (affIota K.as A) := Classical.epsilon_spec h
  have e₁ : ∀ A, (FAOp K L μ₁ A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
      FAcoef L.ν μ₁ K.χf (affIota K.as A) := Classical.epsilon_spec h₁
  have e₂ : ∀ A, (FAOp K L μ₂ A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
      FAcoef L.ν μ₂ K.χf (affIota K.as A) := Classical.epsilon_spec h₂
  ext1 A
  rw [add_apply, smul_apply,
    smul_apply]
  apply Lp.ext
  have c1 := Lp.coeFn_add ((1 - t) • FAOp K L μ₁ A) (t • FAOp K L μ₂ A)
  have c2 := Lp.coeFn_smul (1 - t) (FAOp K L μ₁ A)
  have c3 := Lp.coeFn_smul t (FAOp K L μ₂ A)
  filter_upwards [e₀ A, c1, c2, c3, e₁ A, e₂ A] with p hp0 hp1 hp2 hp3 hp4 hp5
  rw [hp1, Pi.add_apply, hp2, hp3, Pi.smul_apply, Pi.smul_apply, hp4, hp5, hp0]
  exact FAcoef_comb_apply _ _ _ L.ν_pos hlin p

/-! ## 4. The window weight and the leaf -/

/-- The affine weight `t(μ) = (μ-μ₁)/(μ₂-μ₁)` recovers `μ` from `μ₁, μ₂` when `μ₁ ≠ μ₂`. -/
theorem affine_weight_fa {μ₁ μ₂ μ : ℝ} (h : μ₁ ≠ μ₂) :
    (1 - (μ - μ₁) / (μ₂ - μ₁)) * μ₁ + (μ - μ₁) / (μ₂ - μ₁) * μ₂ = μ := by
  have hd : μ₂ - μ₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp
  ring

/-- **`F_A` is norm continuous in `μ`** (source 4957-4985, 5703). -/
theorem SeqData.faCont (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.FACont := by
  have hνlt : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hst.pins, hνlt] with n hpins hlt
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have hL : 0 < |Real.log (D.level n).ν| :=
    abs_pos.mpr (Real.log_neg hνpos hlt).ne
  have hpos : (0 : ℝ) < 2 * |Real.log (D.level n).ν| := by linarith
  have hdiv : (0 : ℝ) < 1 / (2 * |Real.log (D.level n).ν|) := one_div_pos.mpr hpos
  have hneg : (-1 : ℝ) / (2 * |Real.log (D.level n).ν|)
      = -(1 / (2 * |Real.log (D.level n).ν|)) := by ring
  have hlt12 : D.mu n (-1) < D.mu n 1 := by
    show D.σ₀ + (-1 : ℝ) / (2 * |Real.log (D.level n).ν|)
      < D.σ₀ + 1 / (2 * |Real.log (D.level n).ν|)
    rw [hneg]
    linarith
  have hne : D.mu n (-1) ≠ D.mu n 1 := ne_of_lt hlt12
  have hpin : ∀ z ∈ Icc (-1 : ℝ) 1, ∃ F : AffSp D.K.as →L[ℝ] LSrc (D.level n), ∀ A,
      (F A : Chart → Merid) =ᵐ[srcMeasure (cOf (D.level n).ν)]
        FAcoef (D.level n).ν (D.mu n z) D.K.χf (affIota D.K.as A) :=
    fun z hz => (hpins z hz).fA
  have hμ₁ := hpin (-1) ⟨le_rfl, by norm_num⟩
  have hμ₂ := hpin 1 ⟨by norm_num, le_rfl⟩
  have hcont : Continuous fun μ : ℝ =>
      (1 - (μ - D.mu n (-1)) / (D.mu n 1 - D.mu n (-1))) • FAOp D.K (D.level n) (D.mu n (-1))
        + ((μ - D.mu n (-1)) / (D.mu n 1 - D.mu n (-1))) • FAOp D.K (D.level n) (D.mu n 1) := by
    fun_prop
  refine hcont.continuousOn.congr ?_
  rintro μ ⟨z, hz, rfl⟩
  exact FAOp_comb D.K (D.level n) (affine_weight_fa hne) hμ₁ hμ₂ (hpin z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
