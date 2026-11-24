import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.CylDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Proof of `SCCylCompOfDeriv` (source 4161-4166, 4178-4186)

Faà di Bruno (`norm_iteratedFDerivWithin_comp_le`) applied to the rescaled outer function
`g s = f (r s)` and the rescaled inner function `h = cylR / r` (`r = cylR y`) at the point `y`
(`h y = 1`); `‖D^i h y‖ ≤ K r^{-i}` and `‖g^{(k)}(1)‖ = r^k |f^{(k)}(r)| ≤ A r^{-p}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem scCylCompOfDeriv : SCCylCompOfDeriv := by
  intro hD
  choose! K hK using hD
  set K' : ℝ := 1 + ∑ i ∈ Finset.range 8, |K i| with hK'
  have hK'1 : 1 ≤ K' := by
    have : 0 ≤ ∑ i ∈ Finset.range 8, |K i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith
  have hKi : ∀ i, i ≤ 7 → K i ≤ K' := by
    intro i hi
    have : |K i| ≤ ∑ j ∈ Finset.range 8, |K j| :=
      Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have := le_abs_self (K i)
    linarith
  refine ⟨(7 : ℕ).factorial * K' ^ 7, ?_⟩
  intro p A f hp0 hp2 hA hf hder m hm y hy
  set r : ℝ := cylR y with hr
  have hrpos : 0 < r := hy
  let g : ℝ → ℝ := fun s => f (r * s)
  let h : Vec3 → ℝ := fun x => r⁻¹ • cylR x
  have hcomp : (fun x => f (cylR x)) = g ∘ h := by
    funext x
    simp only [g, h, Function.comp, smul_eq_mul]
    congr 1
    field_simp
  have hmaps : MapsTo (fun s : ℝ => r * s) (Ioi 0) (Ioi 0) :=
    fun s hs => mul_pos hrpos hs
  have hg : ContDiffOn ℝ 7 g (Ioi 0) :=
    hf.comp (contDiffOn_const.mul contDiffOn_id) hmaps
  have hU := ScCylDerivAux.isOpen_cylPos
  have hh : ContDiffOn ℝ 7 h {z : Vec3 | 0 < cylR z} := fun z hz =>
    (((ScCylDerivAux.contDiffAt_cylR_of_pos hz).contDiffWithinAt).const_smul r⁻¹)
  have hst : MapsTo h {z : Vec3 | 0 < cylR z} (Ioi 0) := by
    intro z hz
    show 0 < r⁻¹ • cylR z
    rw [smul_eq_mul]
    exact mul_pos (inv_pos.2 hrpos) hz
  have hhy : h y = 1 := by
    simp only [h, smul_eq_mul]
    rw [← hr]
    exact inv_mul_cancel₀ hrpos.ne'
  have hmN : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
  have hC : ∀ i, i ≤ m →
      ‖iteratedFDerivWithin ℝ i g (Ioi 0) (h y)‖ ≤ A * r ^ (-p) := by
    intro i hi
    rw [hhy, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    have h1 : (1 : ℝ) ∈ Ioi (0 : ℝ) := by simp
    have hfi : ContDiffOn ℝ i f (Ioi 0) := hf.of_le (by exact_mod_cast (hi.trans hm))
    have e := iteratedDerivWithin_comp_const_smul (n := i) (s := Ioi (0 : ℝ)) h1
      isOpen_Ioi.uniqueDiffOn hfi r hmaps
    simp only [smul_eq_mul, mul_one] at e
    rw [show (fun s => f (r * s)) = g from rfl] at e
    rw [e, iteratedDerivWithin_of_isOpen isOpen_Ioi (show r ∈ Ioi (0 : ℝ) from hrpos),
      Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hrpos i)]
    have hb := hder i (hi.trans hm) r hrpos
    calc r ^ i * |iteratedDeriv i f r| ≤ r ^ i * (A * r ^ (-p - (i : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg hrpos.le _)
      _ = A * r ^ (-p) := by
          rw [Real.rpow_sub hrpos, Real.rpow_natCast]
          field_simp
  have hDi : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDerivWithin ℝ i h {z : Vec3 | 0 < cylR z} y‖ ≤ (K' / r) ^ i := by
    intro i hi1 him
    rw [iteratedFDerivWithin_of_isOpen i hU (show y ∈ {z : Vec3 | 0 < cylR z} from hy)]
    have e : iteratedFDeriv ℝ i h y = r⁻¹ • iteratedFDeriv ℝ i cylR y :=
      iteratedFDeriv_const_smul_apply'
        ((ScCylDerivAux.contDiffAt_cylR_of_pos hy).of_le (by exact_mod_cast (him.trans hm)))
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hrpos.le)]
    have hb := hK i (him.trans hm) y hy
    rw [← hr] at hb
    have hKi' := hKi i (him.trans hm)
    have hrp : r ^ ((1 : ℝ) - i) = r * (r ^ i)⁻¹ := by
      rw [Real.rpow_sub hrpos, Real.rpow_one, Real.rpow_natCast, div_eq_mul_inv]
    have hK'i : K' ≤ K' ^ i := by
      calc K' = K' ^ 1 := (pow_one _).symm
        _ ≤ K' ^ i := pow_le_pow_right₀ hK'1 hi1
    have hrinv : 0 < (r ^ i)⁻¹ := inv_pos.2 (pow_pos hrpos i)
    calc r⁻¹ * ‖iteratedFDeriv ℝ i cylR y‖ ≤ r⁻¹ * (K i * r ^ ((1 : ℝ) - i)) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hrpos.le)
      _ = K i * (r ^ i)⁻¹ := by
          rw [hrp]; field_simp
      _ ≤ K' ^ i * (r ^ i)⁻¹ := by
          apply mul_le_mul_of_nonneg_right (hKi'.trans hK'i) hrinv.le
      _ = (K' / r) ^ i := by rw [div_pow, div_eq_mul_inv]
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := m) (x := y) (N := 7)
    hg hh hmN isOpen_Ioi.uniqueDiffOn hU.uniqueDiffOn hst (show y ∈ {z : Vec3 | 0 < cylR z} from hy)
    hC hDi
  rw [iteratedFDerivWithin_of_isOpen m hU (show y ∈ {z : Vec3 | 0 < cylR z} from hy),
    ← hcomp] at key
  refine key.trans ?_
  have hA' : 0 ≤ A * r ^ (-p) := mul_nonneg hA (Real.rpow_nonneg hrpos.le _)
  have hrm : r ^ (-p - (m : ℝ)) = r ^ (-p) * (r ^ m)⁻¹ := by
    rw [Real.rpow_sub hrpos, Real.rpow_natCast, div_eq_mul_inv]
  rw [hrm, div_pow]
  have hfac : (m.factorial : ℝ) ≤ ((7 : ℕ).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hm
  have hKp : K' ^ m ≤ K' ^ 7 := pow_le_pow_right₀ hK'1 hm
  have hrinv : 0 < (r ^ m)⁻¹ := inv_pos.2 (pow_pos hrpos m)
  have hK0 : 0 ≤ K' ^ m := by positivity
  calc (m.factorial : ℝ) * (A * r ^ (-p)) * (K' ^ m / r ^ m)
      = (m.factorial : ℝ) * K' ^ m * (A * r ^ (-p) * (r ^ m)⁻¹) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ ((7 : ℕ).factorial : ℝ) * K' ^ 7 * (A * r ^ (-p) * (r ^ m)⁻¹) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hfac hKp hK0 (by positivity)
    _ = ((7 : ℕ).factorial : ℝ) * K' ^ 7 * A * (r ^ (-p) * (r ^ m)⁻¹) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
