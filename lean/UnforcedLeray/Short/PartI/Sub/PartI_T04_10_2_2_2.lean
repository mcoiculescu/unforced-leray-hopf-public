import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_2_2
import UnforcedLeray.Short.PartI.Sub.T07
import UnforcedLeray.Short.PartI.Sub.T04.APriori
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.Static

/-!
# Part I, `PartI:T04/10/2/2/2`: `SliceDuSup` from the component facts

Source of record: `the November 2 reference manuscript`, lines 285-288.
`SliceDuSup` follows from `CylSupInterp` (applied to the four components of `Du`), `APElliptic`
(`j = 0,1,2`) and one purely structural fact `SliceDuComponents`: the entries of `Du` are smooth
periodic functions whose `j`-th jets are dominated by `‖D^{j+1}u‖`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- **Structural leaf** (lines 285-288, "apply the interpolation to the components of `Du`"):
there are absolute constants `C₀, C₁ ≥ 0` such that for every `SliceOK` slice the four entries
`f_a = ∂_k u_i` (`a = (k,i)`, `fun z => fderiv ℝ u z (Pi.single k 1) i` or the same through
`iteratedFDeriv ℝ 1 u z`) are smooth, `c`-periodic, with `‖Du z‖ ≤ C₀ Σ_a |f_a z|` and
`‖D^j f_a z‖ ≤ C₁ ‖D^{j+1} u z‖` for all `j, z`.
Route: `norm_iteratedFDeriv_fderiv`, `ContinuousLinearMap.norm_iteratedFDeriv_comp_left` /
`norm_iteratedFDeriv_clm_apply_const` with the evaluation at the unit vector and the coordinate
projection (both of norm `≤ 1`); `‖L‖ ≤ C₀ Σ_{k,i} |L e_k i|` for `L : Plane →L Vec`. -/
def SliceDuComponents : Prop :=
  ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ (c : ℝ) (u : Plane → Vec), 1 ≤ c → SliceOK c u →
    ∃ f : Fin 4 → Plane → ℝ, (∀ a, ContDiff ℝ ∞ (f a)) ∧ (∀ a, Cyl.IsPeriodic c (f a)) ∧
      (∀ z, ‖iteratedFDeriv ℝ 1 u z‖ ≤ C₀ * ∑ a, |f a z|) ∧
      ∀ (a : Fin 4) (j : ℕ) (z : Plane),
        ‖iteratedFDeriv ℝ j (f a) z‖ ≤ C₁ * ‖iteratedFDeriv ℝ (j + 1) u z‖

/-- `L²` transfer: a smooth `g` whose `j`-jet is dominated by `C₁ ‖D^{j+1}u‖` has an `L²(cell)` jet
with `‖D^j g‖₂² ≤ C₁² ‖D^{j+1}u‖₂²`. -/
theorem sd_l2 {c : ℝ} {u : Plane → Vec} {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (j : ℕ) {C₁ : ℝ}
    (hb : ∀ z, ‖iteratedFDeriv ℝ j g z‖ ≤ C₁ * ‖iteratedFDeriv ℝ (j + 1) u z‖)
    (hI : IntegrableOn (fun z => ‖iteratedFDeriv ℝ (j + 1) u z‖ ^ 2) (Cyl.cell c)) :
    MemLp (Train.jet j g) 2 (Cyl.cellμ c) ∧
      (Train.cellL2 c (Train.jet j g)).toReal ^ 2 ≤
        C₁ ^ 2 * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) u z‖ ^ 2 := by
  have hcont : Continuous (fun z => ‖iteratedFDeriv ℝ j g z‖ ^ 2) :=
    (hg.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm.pow 2
  have hint : IntegrableOn (fun z => ‖iteratedFDeriv ℝ j g z‖ ^ 2) (Cyl.cell c) := by
    refine Integrable.mono' (hI.const_mul (C₁ ^ 2)) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have h0 := hb z
    have h1 : 0 ≤ ‖iteratedFDeriv ℝ j g z‖ := norm_nonneg _
    have : ‖iteratedFDeriv ℝ j g z‖ ^ 2 ≤ (C₁ * ‖iteratedFDeriv ℝ (j + 1) u z‖) ^ 2 :=
      pow_le_pow_left₀ h1 h0 2
    rw [Real.norm_of_nonneg (by positivity)]
    calc _ ≤ _ := this
      _ = _ := by ring
  have hm : MemLp (Train.jet j g) 2 (Cyl.cellμ c) := apL2s_memLp_jet hg j hint
  refine ⟨hm, ?_⟩
  have hX := hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [ENNReal.toReal_ofNat] at hX
  have hX0 : 0 ≤ ∫ z, ‖Train.jet j g z‖ ^ (2:ℝ) ∂(Cyl.cellμ c) :=
    integral_nonneg fun z => by positivity
  have hXe : ∫ z, ‖Train.jet j g z‖ ^ (2:ℝ) ∂(Cyl.cellμ c) =
      ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j g z‖ ^ 2 := by
    simp only [Real.rpow_two]
    rfl
  have hcell : (Train.cellL2 c (Train.jet j g)).toReal ^ 2 =
      ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j g z‖ ^ 2 := by
    unfold Train.cellL2
    rw [hX, ENNReal.toReal_ofReal (Real.rpow_nonneg hX0 _)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
    norm_num
    simpa only [Real.rpow_two] using hXe
  rw [hcell, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono hint (hI.const_mul _) fun z => ?_
  have h1 : 0 ≤ ‖iteratedFDeriv ℝ j g z‖ := norm_nonneg _
  have : ‖iteratedFDeriv ℝ j g z‖ ^ 2 ≤ (C₁ * ‖iteratedFDeriv ℝ (j + 1) u z‖) ^ 2 :=
    pow_le_pow_left₀ h1 (hb z) 2
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The real form of the sup interpolation for one component. -/
theorem sd_real {C : ℝ} (hCpos : 0 ≤ C)
    (hC : ∀ c : ℝ, 1 ≤ c → ∀ f : Plane → ℝ, ContDiff ℝ ∞ f → Cyl.IsPeriodic c f →
      MemLp f 2 (Cyl.cellμ c) → MemLp (Train.jet 1 f) 2 (Cyl.cellμ c) →
      MemLp (Train.jet 2 f) 2 (Cyl.cellμ c) →
      ∀ z : Plane, ‖f z‖ₑ ≤
        ENNReal.ofReal C * (Train.cellL2 c f * Train.cellL2 c (Train.jet 2 f)) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (C * c ^ (-(1 / 2 : ℝ))) *
            (Train.cellL2 c f * Train.cellL2 c (Train.jet 1 f)) ^ (1 / 2 : ℝ))
    {c : ℝ} (hc : 1 ≤ c) {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hp : Cyl.IsPeriodic c f)
    (h0 : MemLp f 2 (Cyl.cellμ c)) (h1 : MemLp (Train.jet 1 f) 2 (Cyl.cellμ c))
    (h2 : MemLp (Train.jet 2 f) 2 (Cyl.cellμ c)) (z : Plane) :
    |f z| ≤ C * ((Train.cellL2 c f).toReal + (Train.cellL2 c (Train.jet 2 f)).toReal) / 2 +
      C * ((Train.cellL2 c f).toReal + (Train.cellL2 c (Train.jet 1 f)).toReal) / 2 := by
  have key := hC c hc f hf hp h0 h1 h2 z
  have f0 : Train.cellL2 c f ≠ ⊤ := h0.eLpNorm_ne_top
  have f1 : Train.cellL2 c (Train.jet 1 f) ≠ ⊤ := h1.eLpNorm_ne_top
  have f2 : Train.cellL2 c (Train.jet 2 f) ≠ ⊤ := h2.eLpNorm_ne_top
  set l0 := (Train.cellL2 c f).toReal with hl0
  set l1 := (Train.cellL2 c (Train.jet 1 f)).toReal with hl1
  set l2 := (Train.cellL2 c (Train.jet 2 f)).toReal with hl2
  have l0n : 0 ≤ l0 := ENNReal.toReal_nonneg
  have l1n : 0 ≤ l1 := ENNReal.toReal_nonneg
  have l2n : 0 ≤ l2 := ENNReal.toReal_nonneg
  have e0 : Train.cellL2 c f = ENNReal.ofReal l0 := (ENNReal.ofReal_toReal f0).symm
  have e1 : Train.cellL2 c (Train.jet 1 f) = ENNReal.ofReal l1 := (ENNReal.ofReal_toReal f1).symm
  have e2 : Train.cellL2 c (Train.jet 2 f) = ENNReal.ofReal l2 := (ENNReal.ofReal_toReal f2).symm
  rw [e0, e1, e2, ← ENNReal.ofReal_mul l0n, ← ENNReal.ofReal_mul l0n,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg l0n l2n) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg l0n l1n) (by norm_num),
    ← ENNReal.ofReal_mul hCpos,
    ← ENNReal.ofReal_mul (mul_nonneg hCpos (Real.rpow_nonneg (by linarith) _)),
    ← ENNReal.ofReal_add (mul_nonneg hCpos (Real.rpow_nonneg (mul_nonneg l0n l2n) _))
      (mul_nonneg (mul_nonneg hCpos (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg (mul_nonneg l0n l1n) _)),
    Real.enorm_eq_ofReal_abs] at key
  have key2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key
  refine key2.trans ?_
  have hcc : c ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num)
  have s2 : (l0 * l2) ^ (1 / 2 : ℝ) ≤ (l0 + l2) / 2 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (l0 - l2)]
  have s1 : (l0 * l1) ^ (1 / 2 : ℝ) ≤ (l0 + l1) / 2 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (l0 - l1)]
  have p1 : 0 ≤ (l0 * l1) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (mul_nonneg l0n l1n) _
  have p2 : 0 ≤ (l0 * l2) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (mul_nonneg l0n l2n) _
  have q : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have a1 : C * (l0 * l2) ^ (1 / 2 : ℝ) ≤ C * ((l0 + l2) / 2) := mul_le_mul_of_nonneg_left s2 hCpos
  have a2 : C * c ^ (-(1 / 2 : ℝ)) * (l0 * l1) ^ (1 / 2 : ℝ) ≤ C * ((l0 + l1) / 2) := by
    calc _ ≤ C * 1 * (l0 * l1) ^ (1 / 2 : ℝ) := by gcongr
      _ = C * (l0 * l1) ^ (1 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left s1 hCpos
  linarith

/-- **Assembly**: `SliceDuSup` from the component fact, `CylSupInterp` and `APElliptic`. -/
theorem sliceDuSup_of (hComp : SliceDuComponents) (hCSI : CylSupInterp) (hAP : APElliptic) :
    SliceDuSup := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hcomp⟩ := hComp
  obtain ⟨C, hCpos, hC⟩ := hCSI
  obtain ⟨K0, hK0, hE0⟩ := hAP 0
  obtain ⟨K1, hK1, hE1⟩ := hAP 1
  obtain ⟨K2, hK2, hE2⟩ := hAP 2
  intro A
  set Q : ℝ := (1 + C₁ ^ 2 * K0 * |A|) + (1 + C₁ ^ 2 * K1 * |A|) + 1 + C₁ ^ 2 * K2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨4 * C₀ * C * Q, by positivity, ?_⟩
  intro c u hc hS hA0 hW0 hW1 hsup z
  have hS' := hS
  obtain ⟨hu, hper, hdiv, hbdd, hL⟩ := hS'
  have hAnn : 0 ≤ A := le_trans (integral_nonneg fun z => sq_nonneg _) hW0
  rw [abs_of_nonneg hAnn] at hQ
  obtain ⟨f, hfs, hfp, hDu, hjet⟩ := hcomp c u hc hS
  set W : ℝ := ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 2 (Cyl.curl u) z‖ ^ 2 with hW
  have hW_nn : 0 ≤ W := integral_nonneg fun z => sq_nonneg _
  have e1 := hE0 c hc u hu hper hdiv hbdd hL
  have e2 := hE1 c hc u hu hper hdiv hbdd hL
  have e3 := hE2 c hc u hu hper hdiv hbdd hL
  simp only [Nat.reduceAdd] at e1 e2 e3
  -- bound for each component
  have comp : ∀ a : Fin 4, |f a z| ≤ C * Q * (1 + W) := by
    intro a
    have t0 := sd_l2 (hfs a) 0 (fun z => hjet a 0 z) (hL 1)
    have t1 := sd_l2 (hfs a) 1 (fun z => hjet a 1 z) (hL 2)
    have t2 := sd_l2 (hfs a) 2 (fun z => hjet a 2 z) (hL 3)
    have hnorm0 : ∀ z, ‖Train.jet 0 (f a) z‖ = ‖f a z‖ := fun z => by
      simp [Train.jet, norm_iteratedFDeriv_zero]
    have m0 : MemLp (f a) 2 (Cyl.cellμ c) := by
      have h := t0.1
      exact (memLp_congr_norm h.1 (hfs a).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hnorm0)).1 h
    have hcell0 : Train.cellL2 c (Train.jet 0 (f a)) = Train.cellL2 c (f a) :=
      eLpNorm_congr_norm_ae (Filter.Eventually.of_forall hnorm0)
    have key := sd_real hCpos hC hc (hfs a) (hfp a) m0 t1.1 t2.1 z
    rw [hcell0] at t0
    have hK0A : 0 ≤ C₁ ^ 2 * K0 * A := by positivity
    have hK1A : 0 ≤ C₁ ^ 2 * K1 * A := by positivity
    have hK2' : 0 ≤ C₁ ^ 2 * K2 := by positivity
    have p0 : 0 ≤ (Train.cellL2 c (f a)).toReal := ENNReal.toReal_nonneg
    have p1 : 0 ≤ (Train.cellL2 c (Train.jet 1 (f a))).toReal := ENNReal.toReal_nonneg
    have p2 : 0 ≤ (Train.cellL2 c (Train.jet 2 (f a))).toReal := ENNReal.toReal_nonneg
    have n0 : (Train.cellL2 c (f a)).toReal ≤ 1 + C₁ ^ 2 * K0 * A := by
      have hh : (Train.cellL2 c (f a)).toReal ^ 2 ≤ C₁ ^ 2 * K0 * A := by
        refine t0.2.trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (e1.trans (mul_le_mul_of_nonneg_left hW0 hK0))
          (by positivity)
      nlinarith [sq_nonneg ((Train.cellL2 c (f a)).toReal - 1)]
    have n1 : (Train.cellL2 c (Train.jet 1 (f a))).toReal ≤ 1 + C₁ ^ 2 * K1 * A := by
      have hh : (Train.cellL2 c (Train.jet 1 (f a))).toReal ^ 2 ≤ C₁ ^ 2 * K1 * A := by
        refine t1.2.trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (e2.trans (mul_le_mul_of_nonneg_left hW1 hK1))
          (by positivity)
      nlinarith [sq_nonneg ((Train.cellL2 c (Train.jet 1 (f a))).toReal - 1)]
    have n2 : (Train.cellL2 c (Train.jet 2 (f a))).toReal ≤ (1 + C₁ ^ 2 * K2) * (1 + W) := by
      have hh : (Train.cellL2 c (Train.jet 2 (f a))).toReal ^ 2 ≤ C₁ ^ 2 * K2 * W := by
        refine t2.2.trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left e3 (by positivity)
      have h1 : (Train.cellL2 c (Train.jet 2 (f a))).toReal ≤
          1 + (Train.cellL2 c (Train.jet 2 (f a))).toReal ^ 2 := by
        nlinarith [sq_nonneg ((Train.cellL2 c (Train.jet 2 (f a))).toReal - 1)]
      have h2 : 0 ≤ C₁ ^ 2 * K2 * W := by positivity
      have h3 : (1 + C₁ ^ 2 * K2) * (1 + W) = 1 + W + C₁ ^ 2 * K2 + C₁ ^ 2 * K2 * W := by ring
      rw [h3]
      linarith
    have hW1' : (0 : ℝ) ≤ 1 + W := by linarith
    have hW1'' : (1 : ℝ) ≤ 1 + W := by linarith
    have c0 : 1 + C₁ ^ 2 * K0 * A ≤ (1 + C₁ ^ 2 * K0 * A) * (1 + W) :=
      le_mul_of_one_le_right (by positivity) hW1''
    have c1 : 1 + C₁ ^ 2 * K1 * A ≤ (1 + C₁ ^ 2 * K1 * A) * (1 + W) :=
      le_mul_of_one_le_right (by positivity) hW1''
    have hQe : Q * (1 + W) = (1 + C₁ ^ 2 * K0 * A) * (1 + W) +
        (1 + C₁ ^ 2 * K1 * A) * (1 + W) + (1 + C₁ ^ 2 * K2) * (1 + W) := by
      rw [hQ]; ring
    have d0 : 0 ≤ (1 + C₁ ^ 2 * K0 * A) * (1 + W) := by positivity
    have d1 : 0 ≤ (1 + C₁ ^ 2 * K1 * A) * (1 + W) := by positivity
    have d2 : 0 ≤ (1 + C₁ ^ 2 * K2) * (1 + W) := by positivity
    have hL4 : (Train.cellL2 c (f a)).toReal + (Train.cellL2 c (Train.jet 2 (f a))).toReal +
        ((Train.cellL2 c (f a)).toReal + (Train.cellL2 c (Train.jet 1 (f a))).toReal) ≤
        2 * (Q * (1 + W)) := by
      rw [hQe]; linarith
    calc |f a z| ≤ _ := key
      _ = C * (((Train.cellL2 c (f a)).toReal + (Train.cellL2 c (Train.jet 2 (f a))).toReal) +
        ((Train.cellL2 c (f a)).toReal + (Train.cellL2 c (Train.jet 1 (f a))).toReal)) / 2 := by
          ring
      _ ≤ C * (2 * (Q * (1 + W))) / 2 := by gcongr
      _ = C * Q * (1 + W) := by ring
  calc ‖iteratedFDeriv ℝ 1 u z‖ ≤ C₀ * ∑ a, |f a z| := hDu z
    _ ≤ C₀ * ∑ _a : Fin 4, C * Q * (1 + W) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => comp a) hC₀
    _ = 4 * C₀ * C * Q * (1 + W) := by simp; ring
