import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_7

/-!
# `PartII-b:T13/1/7/3` window norms (arithmetic of the bounds)

Source: `the November 2 reference manuscript` lines 1928-1933. Proves `WbdNorms`
from the cylinder bounds, the first weight comparison and the interpolation hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- Unit vector `e_0`. -/
def wbdn_e0 : CMerid := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)

/-- A scalar profile as a meridional vector `g(x) e_0`. -/
def wbdn_vec (g : Coord → ℂ) : CProf := fun x => g x • wbdn_e0

theorem wbdn_vec_norm (g : Coord → ℂ) (x : Coord) : ‖wbdn_vec g x‖ = ‖g x‖ := by
  simp [wbdn_vec, wbdn_e0, norm_smul, EuclideanSpace.norm_single]

theorem wbdn_vec_aesm {g : Coord → ℂ} (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (wbdn_vec g) volume :=
  hg.smul_const wbdn_e0

theorem wbdn_eLpNorm_vec (μ : Measure Coord) (p : ℝ≥0∞) (g : Coord → ℂ) :
    eLpNorm (wbdn_vec g) p μ = eLpNorm g p μ := by
  rw [← eLpNorm_norm (wbdn_vec g), ← eLpNorm_norm g]
  simp only [wbdn_vec_norm]

/-- The first weight comparison for a scalar function on the window `winOpen a`. -/
theorem wbdn_weight (hW : WindowWeightCompare) {c r a : ℝ} (hc : 0 < c) (h1 : 1 < r) (h3 : r < 3)
    (ha : 0 < a) {g : Coord → ℂ} (hg : AEStronglyMeasurable g volume) :
    eLpNorm g (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
      ENNReal.ofReal (16 * a ^ ((r / 2 - 5 / 2) / r)) *
        eLpNorm g (ENNReal.ofReal r) ((cylMeas c).restrict (winOpen a)) := by
  have hA : MeasurableSet (winOpen a) := measurableSet_Ioo.prod MeasurableSet.univ
  have hAs : winOpen a ⊆ winSet2 a := by
    rintro x ⟨⟨hx1, hx2⟩, -⟩
    exact ⟨⟨by linarith, by linarith⟩, trivial⟩
  have h := (hW c r a hc h1 h3 ha (winOpen a) hA hAs (wbdn_vec g) (wbdn_vec_aesm hg)).1
  unfold hNormOn at h
  rwa [wbdn_eLpNorm_vec, wbdn_eLpNorm_vec] at h

theorem wbdn_nu_mul {ν : ℝ} (hν : 0 ≤ ν) (μ : Measure Coord) (p : ℝ≥0∞) (D : Coord → ℂ) :
    eLpNorm (fun x => (ν : ℂ) * D x) p μ = ENNReal.ofReal ν * eLpNorm D p μ := by
  have e : (fun x => (ν : ℂ) * D x) = ν • D := by
    funext x
    simp [Complex.real_smul]
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hν]

theorem wbdn_wmul (μ : Measure Coord) {A : Set Coord} (hA : MeasurableSet A) {K : ℝ} (hK : 0 ≤ K)
    (w : Coord → ℝ) (hw : ∀ x ∈ A, |w x| ≤ K) (D : Coord → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x => (w x : ℂ) * D x) p (μ.restrict A) ≤
      ENNReal.ofReal K * eLpNorm D p (μ.restrict A) := by
  calc eLpNorm (fun x => (w x : ℂ) * D x) p (μ.restrict A)
      ≤ eLpNorm (K • D) p (μ.restrict A) := by
        apply eLpNorm_mono_ae
        filter_upwards [ae_restrict_mem hA] with x hx
        simp only [Pi.smul_apply, norm_mul, Complex.norm_real, norm_smul, Real.norm_of_nonneg hK,
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hw x hx) (norm_nonneg _)
    _ = ENNReal.ofReal K * eLpNorm D p (μ.restrict A) := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hK]

theorem wbdn_T {Q : ℝ} (hQ : 0 ≤ Q) (NG NB : ℝ≥0∞) :
    NG + ENNReal.ofReal Q * NB ≤ ENNReal.ofReal (1 + Q) * (NG + NB) := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + Q) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have h2 : ENNReal.ofReal Q ≤ ENNReal.ofReal (1 + Q) := ENNReal.ofReal_le_ofReal (by linarith)
  rw [mul_add]
  exact add_le_add (le_mul_of_one_le_left zero_le h1) (mul_le_mul_left h2 _)

/-- Part 1: the bound for `s Dt`. -/
theorem wbdn_part1 {c r a : ℝ} (hW : WindowWeightCompare) (hc : 0 < c) (h1 : 1 < r) (h3 : r < 3)
    (ha : 0 < a) {C Q : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q) (G b : CProf) {Dt f : Coord → ℂ}
    (hDt : AEStronglyMeasurable Dt volume)
    (hf : ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) * eLpNorm f (ENNReal.ofReal r) (cylMeas c) ≤
      ENNReal.ofReal (32 / a) * (hNormOn c r (winSet2 a) G + ENNReal.ofReal Q * hNormOn c r (winSet2 a) b))
    (hC3 : eLpNorm Dt (ENNReal.ofReal r) (cylMeas c) ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c)) :
    eLpNorm (fun x => (x.1 : ℂ) * Dt x) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
      ENNReal.ofReal (1024 * C * (1 + Q)) *
        (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
  have hA : MeasurableSet (winOpen a) := measurableSet_Ioo.prod MeasurableSet.univ
  have hg : AEStronglyMeasurable (fun x : Coord => (x.1 : ℂ) * Dt x) volume :=
    (Complex.measurable_ofReal.comp measurable_fst).aestronglyMeasurable.mul hDt
  have hw : ∀ x ∈ winOpen a, |x.1| ≤ 2 * a := fun x hx =>
    abs_le.mpr ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
  have h2a : (0:ℝ) ≤ 2 * a := by linarith
  have hwm := wbdn_wmul (cylMeas c) hA h2a (fun x => x.1) hw Dt (ENNReal.ofReal r)
  have hT := wbdn_T hQ (hNormOn c r (winSet2 a) G) (hNormOn c r (winSet2 a) b)
  have h16 : (0:ℝ) ≤ 16 := by norm_num
  have h16a : (0:ℝ) ≤ 16 * (2 * a) := by linarith
  have h16aC : (0:ℝ) ≤ 16 * (2 * a) * C := mul_nonneg h16a hC
  have h1024 : (0:ℝ) ≤ 1024 * C := by linarith
  have h1024Q : (0:ℝ) ≤ 1024 * C * (1 + Q) := mul_nonneg h1024 (by linarith)
  have ha' : a ≠ 0 := ha.ne'
  have hK : ENNReal.ofReal 16 * ENNReal.ofReal (2 * a) * ENNReal.ofReal C *
      ENNReal.ofReal (32 / a) = ENNReal.ofReal (1024 * C) := by
    rw [← ENNReal.ofReal_mul h16, ← ENNReal.ofReal_mul h16a, ← ENNReal.ofReal_mul h16aC]
    congr 1
    field_simp
    ring
  calc eLpNorm (fun x => (x.1 : ℂ) * Dt x) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a))
      ≤ ENNReal.ofReal (16 * a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (fun x => (x.1 : ℂ) * Dt x) (ENNReal.ofReal r) ((cylMeas c).restrict (winOpen a)) :=
        wbdn_weight hW hc h1 h3 ha hg
    _ ≤ ENNReal.ofReal (16 * a ^ ((r / 2 - 5 / 2) / r)) *
          (ENNReal.ofReal (2 * a) * eLpNorm Dt (ENNReal.ofReal r) ((cylMeas c).restrict (winOpen a))) :=
        mul_le_mul_right hwm _
    _ ≤ ENNReal.ofReal (16 * a ^ ((r / 2 - 5 / 2) / r)) *
          (ENNReal.ofReal (2 * a) * eLpNorm Dt (ENNReal.ofReal r) (cylMeas c)) :=
        mul_le_mul_right (mul_le_mul_right (eLpNorm_mono_measure Dt Measure.restrict_le_self) _) _
    _ ≤ ENNReal.ofReal (16 * a ^ ((r / 2 - 5 / 2) / r)) *
          (ENNReal.ofReal (2 * a) * (ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c))) :=
        mul_le_mul_right (mul_le_mul_right hC3 _) _
    _ = ENNReal.ofReal 16 * ENNReal.ofReal (2 * a) * ENNReal.ofReal C *
          (ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) * eLpNorm f (ENNReal.ofReal r) (cylMeas c)) := by
        rw [ENNReal.ofReal_mul h16]; ring
    _ ≤ ENNReal.ofReal 16 * ENNReal.ofReal (2 * a) * ENNReal.ofReal C *
          (ENNReal.ofReal (32 / a) *
            (hNormOn c r (winSet2 a) G + ENNReal.ofReal Q * hNormOn c r (winSet2 a) b)) :=
        mul_le_mul_right hf _
    _ = ENNReal.ofReal (1024 * C) *
          (hNormOn c r (winSet2 a) G + ENNReal.ofReal Q * hNormOn c r (winSet2 a) b) := by
        rw [← hK]; ring
    _ ≤ ENNReal.ofReal (1024 * C) *
          (ENNReal.ofReal (1 + Q) * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b)) :=
        mul_le_mul_right hT _
    _ = ENNReal.ofReal (1024 * C * (1 + Q)) *
          (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul h1024]

/-- Part 2: the bound for `√ν √s D1`. -/
theorem wbdn_part2 {c r a ν : ℝ} (hc : 0 < c) (h1 : 1 < r) (h3 : r < 3) (ha : 0 < a) (hν : 0 < ν)
    {Ci C Q : ℝ} (hCi : 0 ≤ Ci) (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hW : WindowWeightCompare)
    (G b : CProf) {u f D : Coord → ℂ} {D2 : Fin 2 → Fin 2 → Coord → ℂ}
    (hD : AEStronglyMeasurable D volume)
    (hu : ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) * eLpNorm u (ENNReal.ofReal r) (cylMeas c) ≤
      16 * hNormOn c r (winSet2 a) b)
    (hf : ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) * eLpNorm f (ENNReal.ofReal r) (cylMeas c) ≤
      ENNReal.ofReal (32 / a) * (hNormOn c r (winSet2 a) G + ENNReal.ofReal Q * hNormOn c r (winSet2 a) b))
    (hD2 : ∀ i j, eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal r) (cylMeas c) ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c))
    (hD1 : ∀ lam : ℝ, 0 < lam → eLpNorm D (ENNReal.ofReal r) (cylMeas c) ≤
      ENNReal.ofReal Ci * (ENNReal.ofReal lam⁻¹ * eLpNorm u (ENNReal.ofReal r) (cylMeas c) +
        ENNReal.ofReal lam * ∑ k : Fin 2, ∑ l : Fin 2,
          eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c))) :
    ENNReal.ofReal (Real.sqrt ν) *
        eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * D x) (ENNReal.ofReal r)
          ((hMeas c r).restrict (winOpen a)) ≤
      ENNReal.ofReal (512 * Ci + 4096 * Ci * C * (1 + Q)) *
        (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
  have hA : MeasurableSet (winOpen a) := measurableSet_Ioo.prod MeasurableSet.univ
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hlam : 0 < Real.sqrt (ν * a) := Real.sqrt_pos.mpr (mul_pos hν ha)
  have h2le : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hg : AEStronglyMeasurable (fun x : Coord => (Real.sqrt x.1 : ℂ) * D x) volume :=
    (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_fst)).aestronglyMeasurable.mul hD
  have hw : ∀ x ∈ winOpen a, |Real.sqrt x.1| ≤ Real.sqrt (2 * a) := fun x hx => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith [hx.1.2])
  have hwm := wbdn_wmul (cylMeas c) hA (Real.sqrt_nonneg (2 * a))
    (fun x => Real.sqrt x.1) hw D (ENNReal.ofReal r)
  have hW1 := wbdn_weight hW hc h1 h3 ha hg
  have hW3 : eLpNorm D (ENNReal.ofReal r) ((cylMeas c).restrict (winOpen a)) ≤
      eLpNorm D (ENNReal.ofReal r) (cylMeas c) :=
    eLpNorm_mono_measure D Measure.restrict_le_self
  have hE1 : ENNReal.ofReal (Real.sqrt ν) * ENNReal.ofReal (Real.sqrt (2 * a)) *
      ENNReal.ofReal (Real.sqrt (ν * a))⁻¹ ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) a, Real.sqrt_mul hν.le a]
    have key : Real.sqrt ν * (Real.sqrt 2 * Real.sqrt a) * (Real.sqrt ν * Real.sqrt a)⁻¹
        = Real.sqrt 2 := by
      field_simp
    rw [key]; exact h2le
  have hE2 : ENNReal.ofReal (Real.sqrt ν) * ENNReal.ofReal (Real.sqrt (2 * a)) *
      ENNReal.ofReal (Real.sqrt (ν * a)) ≤ ENNReal.ofReal (2 * (ν * a)) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) a, Real.sqrt_mul hν.le a]
    calc Real.sqrt ν * (Real.sqrt 2 * Real.sqrt a) * (Real.sqrt ν * Real.sqrt a)
        = Real.sqrt 2 * (Real.sqrt ν * Real.sqrt ν) * (Real.sqrt a * Real.sqrt a) := by ring
      _ = Real.sqrt 2 * ν * a := by rw [Real.mul_self_sqrt hν.le, Real.mul_self_sqrt ha.le]
      _ ≤ 2 * ν * a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2le hν.le) ha.le
      _ = 2 * (ν * a) := by ring
  -- Step 1: the chain of bounds, ending with the two cylinder terms.
  have hchain : ENNReal.ofReal (Real.sqrt ν) *
        eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * D x) (ENNReal.ofReal r)
          ((hMeas c r).restrict (winOpen a)) ≤
      ENNReal.ofReal 2 * (ENNReal.ofReal 16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          ENNReal.ofReal Ci) * eLpNorm u (ENNReal.ofReal r) (cylMeas c) +
        ENNReal.ofReal (2 * (ν * a)) *
          (ENNReal.ofReal 16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) * ENNReal.ofReal Ci) *
          (∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c)) := by
    calc ENNReal.ofReal (Real.sqrt ν) *
          eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * D x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a))
        ≤ ENNReal.ofReal (Real.sqrt ν) *
            (ENNReal.ofReal (16 * a ^ ((r / 2 - 5 / 2) / r)) *
              eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * D x) (ENNReal.ofReal r)
                ((cylMeas c).restrict (winOpen a))) :=
          mul_le_mul_right hW1 _
      _ ≤ ENNReal.ofReal (Real.sqrt ν) *
            (ENNReal.ofReal (16 * a ^ ((r / 2 - 5 / 2) / r)) *
              (ENNReal.ofReal (Real.sqrt (2 * a)) *
                eLpNorm D (ENNReal.ofReal r) ((cylMeas c).restrict (winOpen a)))) :=
          mul_le_mul_right (mul_le_mul_right hwm _) _
      _ ≤ ENNReal.ofReal (Real.sqrt ν) *
            (ENNReal.ofReal (16 * a ^ ((r / 2 - 5 / 2) / r)) *
              (ENNReal.ofReal (Real.sqrt (2 * a)) *
                eLpNorm D (ENNReal.ofReal r) (cylMeas c))) :=
          mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hW3 _) _) _
      _ ≤ ENNReal.ofReal (Real.sqrt ν) *
            (ENNReal.ofReal (16 * a ^ ((r / 2 - 5 / 2) / r)) *
              (ENNReal.ofReal (Real.sqrt (2 * a)) *
                (ENNReal.ofReal Ci * (ENNReal.ofReal (Real.sqrt (ν * a))⁻¹ *
                  eLpNorm u (ENNReal.ofReal r) (cylMeas c) +
                  ENNReal.ofReal (Real.sqrt (ν * a)) *
                    ∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c))))) :=
          mul_le_mul_right (mul_le_mul_right (mul_le_mul_right (hD1 _ hlam) _) _) _
      _ = (ENNReal.ofReal (Real.sqrt ν) * ENNReal.ofReal (Real.sqrt (2 * a)) *
              ENNReal.ofReal (Real.sqrt (ν * a))⁻¹) *
            (ENNReal.ofReal 16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
              ENNReal.ofReal Ci) * eLpNorm u (ENNReal.ofReal r) (cylMeas c) +
          (ENNReal.ofReal (Real.sqrt ν) * ENNReal.ofReal (Real.sqrt (2 * a)) *
              ENNReal.ofReal (Real.sqrt (ν * a))) *
            (ENNReal.ofReal 16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
              ENNReal.ofReal Ci) *
            (∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16)]; ring
      _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal 16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
              ENNReal.ofReal Ci) * eLpNorm u (ENNReal.ofReal r) (cylMeas c) +
          ENNReal.ofReal (2 * (ν * a)) *
            (ENNReal.ofReal 16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
              ENNReal.ofReal Ci) *
            (∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c)) :=
          add_le_add (mul_le_mul_left (mul_le_mul_left hE1 _) _)
            (mul_le_mul_left (mul_le_mul_left hE2 _) _)
  -- Step 2: the two terms.
  have hc512 : ENNReal.ofReal (512 * Ci) = 512 * ENNReal.ofReal Ci := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 512), ENNReal.ofReal_ofNat]
  have hT1 : ENNReal.ofReal 2 * (ENNReal.ofReal 16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
      ENNReal.ofReal Ci) * eLpNorm u (ENNReal.ofReal r) (cylMeas c) ≤
      ENNReal.ofReal (512 * Ci) * hNormOn c r (winSet2 a) b := by
    have e : ENNReal.ofReal 2 * (ENNReal.ofReal 16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
        ENNReal.ofReal Ci) * eLpNorm u (ENNReal.ofReal r) (cylMeas c) =
        32 * ENNReal.ofReal Ci * (ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm u (ENNReal.ofReal r) (cylMeas c)) := by
      simp only [ENNReal.ofReal_ofNat]; ring
    rw [e, hc512]
    calc 32 * ENNReal.ofReal Ci * (ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm u (ENNReal.ofReal r) (cylMeas c))
        ≤ 32 * ENNReal.ofReal Ci * (16 * hNormOn c r (winSet2 a) b) := mul_le_mul_right hu _
      _ = 512 * ENNReal.ofReal Ci * hNormOn c r (winSet2 a) b := by ring
  have hνS : ENNReal.ofReal ν * (∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c))
      ≤ 4 * (ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c)) := by
    have h00 := hD2 0 0
    have h01 := hD2 0 1
    have h10 := hD2 1 0
    have h11 := hD2 1 1
    rw [wbdn_nu_mul hν.le] at h00 h01 h10 h11
    have hsum : (∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c)) =
        eLpNorm (D2 0 0) (ENNReal.ofReal r) (cylMeas c) + eLpNorm (D2 0 1) (ENNReal.ofReal r) (cylMeas c) +
        (eLpNorm (D2 1 0) (ENNReal.ofReal r) (cylMeas c) + eLpNorm (D2 1 1) (ENNReal.ofReal r) (cylMeas c)) := by
      simp only [Fin.sum_univ_two]
    rw [hsum]
    simp only [mul_add]
    calc _ ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c) +
            ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c) +
          (ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c) +
            ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c)) :=
          add_le_add (add_le_add h00 h01) (add_le_add h10 h11)
      _ = 4 * (ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c)) := by ring
  have hT2 : ENNReal.ofReal (2 * (ν * a)) *
      (ENNReal.ofReal 16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) * ENNReal.ofReal Ci) *
      (∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c)) ≤
      ENNReal.ofReal (4096 * Ci * C * (1 + Q)) *
        (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
    have e1 : ENNReal.ofReal (2 * (ν * a)) = 2 * ENNReal.ofReal ν * ENNReal.ofReal a := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_mul hν.le,
        ENNReal.ofReal_ofNat]
      ring
    have hA32 : ENNReal.ofReal a * ENNReal.ofReal (32 / a) = 32 := by
      rw [← ENNReal.ofReal_mul ha.le, show a * (32 / a) = 32 by field_simp, ENNReal.ofReal_ofNat]
    have hK2 : ENNReal.ofReal (4096 * Ci * C * (1 + Q)) =
        4096 * ENNReal.ofReal Ci * ENNReal.ofReal C * ENNReal.ofReal (1 + Q) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hCi) hC),
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) hCi),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4096), ENNReal.ofReal_ofNat]
    calc ENNReal.ofReal (2 * (ν * a)) *
          (ENNReal.ofReal 16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) * ENNReal.ofReal Ci) *
          (∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c))
        = (2 * ENNReal.ofReal a * (16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
            ENNReal.ofReal Ci)) * (ENNReal.ofReal ν *
            (∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c))) := by
          rw [e1, ENNReal.ofReal_ofNat]; ring
      _ ≤ (2 * ENNReal.ofReal a * (16 * ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
            ENNReal.ofReal Ci)) * (4 * (ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c))) :=
          mul_le_mul_right hνS _
      _ = (128 * ENNReal.ofReal Ci * ENNReal.ofReal C * ENNReal.ofReal a) *
            (ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) * eLpNorm f (ENNReal.ofReal r) (cylMeas c)) := by
          ring
      _ ≤ (128 * ENNReal.ofReal Ci * ENNReal.ofReal C * ENNReal.ofReal a) *
            (ENNReal.ofReal (32 / a) *
              (hNormOn c r (winSet2 a) G + ENNReal.ofReal Q * hNormOn c r (winSet2 a) b)) :=
          mul_le_mul_right hf _
      _ = (4096 * ENNReal.ofReal Ci * ENNReal.ofReal C) *
            (hNormOn c r (winSet2 a) G + ENNReal.ofReal Q * hNormOn c r (winSet2 a) b) := by
          have e2 : (128 * ENNReal.ofReal Ci * ENNReal.ofReal C * ENNReal.ofReal a) *
              (ENNReal.ofReal (32 / a) *
                (hNormOn c r (winSet2 a) G + ENNReal.ofReal Q * hNormOn c r (winSet2 a) b)) =
              (128 * ENNReal.ofReal Ci * ENNReal.ofReal C) *
                (ENNReal.ofReal a * ENNReal.ofReal (32 / a)) *
                (hNormOn c r (winSet2 a) G + ENNReal.ofReal Q * hNormOn c r (winSet2 a) b) := by
            ring
          rw [e2, hA32]; ring
      _ ≤ (4096 * ENNReal.ofReal Ci * ENNReal.ofReal C) *
            (ENNReal.ofReal (1 + Q) * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b)) :=
          mul_le_mul_right (wbdn_T hQ _ _) _
      _ = ENNReal.ofReal (4096 * Ci * C * (1 + Q)) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
          rw [hK2]; ring
  -- Step 3: assemble.
  have hsplit : ENNReal.ofReal (512 * Ci) * hNormOn c r (winSet2 a) b ≤
      ENNReal.ofReal (512 * Ci) * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) :=
    mul_le_mul_right le_add_self _
  have h512 : (0:ℝ) ≤ 512 * Ci := by linarith
  have h4096 : (0:ℝ) ≤ 4096 * Ci * C * (1 + Q) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCi) hC) (by linarith)
  calc ENNReal.ofReal (Real.sqrt ν) *
        eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * D x) (ENNReal.ofReal r)
          ((hMeas c r).restrict (winOpen a))
      ≤ _ := hchain
    _ ≤ ENNReal.ofReal (512 * Ci) * hNormOn c r (winSet2 a) b +
          ENNReal.ofReal (4096 * Ci * C * (1 + Q)) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) :=
          add_le_add hT1 hT2
    _ ≤ ENNReal.ofReal (512 * Ci) * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) +
          ENNReal.ofReal (4096 * Ci * C * (1 + Q)) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) :=
          add_le_add hsplit le_rfl
    _ = (ENNReal.ofReal (512 * Ci) + ENNReal.ofReal (4096 * Ci * C * (1 + Q))) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := (add_mul _ _ _).symm
    _ = ENNReal.ofReal (512 * Ci + 4096 * Ci * C * (1 + Q)) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
          rw [ENNReal.ofReal_add h512 h4096]

theorem wbdn_main : WbdNorms := by
  intro r M h1 h3 hM μ C Ci hC hCi
  have hQ : 0 ≤ ‖μ‖ + M / 2 := by have := norm_nonneg μ; linarith
  have hpos1 : 0 < 1024 * C * (1 + (‖μ‖ + M / 2)) :=
    mul_pos (mul_pos (by norm_num) hC) (by linarith)
  have hR : 0 ≤ 512 * Ci + 4096 * Ci * C * (1 + (‖μ‖ + M / 2)) := by
    have : 0 ≤ 4096 * Ci * C * (1 + (‖μ‖ + M / 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCi.le) hC.le) (by linarith)
    linarith
  refine ⟨1024 * C * (1 + (‖μ‖ + M / 2)) + (512 * Ci + 4096 * Ci * C * (1 + (‖μ‖ + M / 2))),
    by linarith, ?_⟩
  intro ν c a hν hc ha G b u f Dt D2 D1 hDt hD1m hu hf hDtb hD2 hD1b hW
  refine ⟨?_, ?_⟩
  · have := wbdn_part1 hW hc h1 h3 ha hC.le hQ G b hDt hf hDtb
    refine this.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _
  · intro j
    have := wbdn_part2 hc h1 h3 ha hν hCi.le hC.le hQ hW G b (hD1m j) hu hf hD2 (hD1b j)
    refine this.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _

theorem wbdNorms : UnforcedLeray.Short.IIb.WbdNorms := wbdn_main

end UnforcedLeray.Short.IIb
