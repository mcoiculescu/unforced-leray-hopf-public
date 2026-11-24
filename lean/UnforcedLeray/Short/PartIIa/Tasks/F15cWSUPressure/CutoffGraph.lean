import UnforcedLeray.Lib.PhaseSpace.ExtendedTest
import UnforcedLeray.Lib.PhaseSpace.Leibniz
import UnforcedLeray.Units.B0411

/-!
# Cutoff convergence in the `L0T` graph norm for derivatives of Schwartz-type phase tests

Helper for `PartII-a:F15/3` (`Tasks/F15cWSUPressure.lean`).
For `U : ℝ × Space → CVec3` with `IsPhaseSchwartz P r U` and `∀ j, IsPhaseSchwartz P r (dy j U)`,
we show that `dy j (mulT (cutχ n) U)` converges to `dy j U` in `Y_r` together with `L0T ν`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.F15c

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ### Smoothness and additivity of phase operators -/

theorem dτ_add_diff {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) : dτ (A + B) = dτ A + dτ B := by
  funext p
  simp [dτ, fderiv_add (hA p) (hB p)]

theorem radialT_add_diff {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) : radialT (A + B) = radialT A + radialT B := by
  funext p
  simp only [radialT, Pi.add_apply, dy_add hA hB, smul_add, Finset.sum_add_distrib]

theorem driftT_add_smooth {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : driftT (A + B) = driftT A + driftT B := by
  have dA : Differentiable ℝ A := hA.differentiable (by simp)
  have dB : Differentiable ℝ B := hB.differentiable (by simp)
  funext p
  simp only [driftT, Pi.add_apply, dτ_add_diff dA dB, radialT_add_diff dA dB]
  module

theorem lapT_add_smooth {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : lapT (A + B) = lapT A + lapT B := by
  have dA : Differentiable ℝ A := hA.differentiable (by simp)
  have dB : Differentiable ℝ B := hB.differentiable (by simp)
  have h2 : ∀ j : Fin 3, dy j (dy j (A + B)) = dy j (dy j A) + dy j (dy j B) := fun j => by
    rw [dy_add dA dB j]
    exact dy_add ((contDiff_dy hA j).differentiable (by simp))
      ((contDiff_dy hB j).differentiable (by simp)) j
  funext p
  simp only [lapT, Pi.add_apply, h2, Finset.sum_add_distrib]

theorem L0T_add_smooth (ν : ℝ) {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : L0T ν (A + B) = L0T ν A + L0T ν B := by
  simp only [L0T, nuLapT]
  rw [lapT_add_smooth hA hB, driftT_add_smooth hA hB]
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  module

theorem dτ_const_smul {A : ℝ × Space → CVec3} (hA : Differentiable ℝ A) (c : ℂ) :
    dτ (c • A) = c • dτ A := by
  funext p
  simp [dτ, fderiv_const_smul (hA p) c]

theorem dy_const_smul {A : ℝ × Space → CVec3} (hA : Differentiable ℝ A) (c : ℂ) (j : Fin 3) :
    dy j (c • A) = c • dy j A := by
  funext p
  simp [dy, fderiv_const_smul (hA p) c]

theorem radialT_const_smul {A : ℝ × Space → CVec3} (hA : Differentiable ℝ A) (c : ℂ) :
    radialT (c • A) = c • radialT A := by
  funext p
  simp only [radialT, Pi.smul_apply, dy_const_smul hA c, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => smul_comm _ _ _

theorem driftT_const_smul {A : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A) (c : ℂ) :
    driftT (c • A) = c • driftT A := by
  have dA : Differentiable ℝ A := hA.differentiable (by simp)
  funext p
  simp only [driftT, Pi.smul_apply, dτ_const_smul dA c, radialT_const_smul dA c, smul_add,
    smul_neg, smul_comm (1 / 2 : ℝ) c, smul_comm (3 / 2 : ℝ) c]

theorem lapT_const_smul {A : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A) (c : ℂ) :
    lapT (c • A) = c • lapT A := by
  have dA : Differentiable ℝ A := hA.differentiable (by simp)
  have h2 : ∀ j : Fin 3, dy j (dy j (c • A)) = c • dy j (dy j A) := fun j => by
    rw [dy_const_smul dA c j]
    exact dy_const_smul ((contDiff_dy hA j).differentiable (by simp)) c j
  funext p
  simp only [lapT, Pi.smul_apply, h2, Finset.smul_sum]

theorem L0T_const_smul (ν : ℝ) {A : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A) (c : ℂ) :
    L0T ν (c • A) = c • L0T ν A := by
  simp only [L0T, nuLapT]
  rw [lapT_const_smul hA c, driftT_const_smul hA c]
  funext p
  simp only [Pi.sub_apply, Pi.smul_apply, smul_sub, smul_comm (ν : ℝ) c,
    smul_comm (1 / 2 : ℝ) c]

theorem L0T_neg (ν : ℝ) {A : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A) :
    L0T ν (-A) = -L0T ν A := by
  have h : (-A) = (-1 : ℂ) • A := by funext p; simp
  rw [h, L0T_const_smul ν hA (-1)]
  funext p
  simp

theorem L0T_sub_smooth (ν : ℝ) {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : L0T ν (A - B) = L0T ν A - L0T ν B := by
  have hBn : ContDiff ℝ ∞ (-B) := hB.neg
  rw [sub_eq_add_neg, L0T_add_smooth ν hA hBn, L0T_neg ν hB, ← sub_eq_add_neg]

/-! ### Algebra of `IsPhaseSchwartz` -/

section SchwartzAlgebra

variable {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]

theorem isPhaseSchwartz_zero : IsPhaseSchwartz P r 0 :=
  (IsPhaseTest.zero (P := P)).isPhaseSchwartz r

theorem isPhaseSchwartz_add {A B : ℝ × Space → CVec3} (hA : IsPhaseSchwartz P r A)
    (hB : IsPhaseSchwartz P r B) : IsPhaseSchwartz P r (A + B) where
  smooth := hA.smooth.add hB.smooth
  periodic τ y := by simp [hA.periodic τ y, hB.periodic τ y]
  slice := hA.slice.add hB.slice
  slice_dy j := by
    rw [dy_add (hA.smooth.differentiable (by simp)) (hB.smooth.differentiable (by simp)) j]
    exact (hA.slice_dy j).add (hB.slice_dy j)
  slice_lapT := by
    rw [lapT_add_smooth hA.smooth hB.smooth]
    exact hA.slice_lapT.add hB.slice_lapT
  slice_driftT := by
    rw [driftT_add_smooth hA.smooth hB.smooth]
    exact hA.slice_driftT.add hB.slice_driftT

theorem isPhaseSchwartz_const_smul {A : ℝ × Space → CVec3} (hA : IsPhaseSchwartz P r A)
    (c : ℂ) : IsPhaseSchwartz P r (c • A) where
  smooth := hA.smooth.const_smul c
  periodic τ y := by simp [hA.periodic τ y]
  slice := hA.slice.const_smul c
  slice_dy j := by
    rw [dy_const_smul (hA.smooth.differentiable (by simp)) c j]
    exact (hA.slice_dy j).const_smul c
  slice_lapT := by
    rw [lapT_const_smul hA.smooth c]
    exact hA.slice_lapT.const_smul c
  slice_driftT := by
    rw [driftT_const_smul hA.smooth c]
    exact hA.slice_driftT.const_smul c

theorem isPhaseSchwartz_neg {A : ℝ × Space → CVec3} (hA : IsPhaseSchwartz P r A) :
    IsPhaseSchwartz P r (-A) := by
  have h : (-A) = (-1 : ℂ) • A := by funext p; simp
  rw [h]
  exact isPhaseSchwartz_const_smul hA (-1)

theorem isPhaseSchwartz_sub {A B : ℝ × Space → CVec3} (hA : IsPhaseSchwartz P r A)
    (hB : IsPhaseSchwartz P r B) : IsPhaseSchwartz P r (A - B) := by
  rw [sub_eq_add_neg]
  exact isPhaseSchwartz_add hA (isPhaseSchwartz_neg hB)

theorem isPhaseSchwartz_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ × Space → CVec3}
    (h : ∀ i ∈ s, IsPhaseSchwartz P r (F i)) : IsPhaseSchwartz P r (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isPhaseSchwartz_zero : IsPhaseSchwartz P r 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isPhaseSchwartz_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sliceTest_L0T (ν : ℝ) {A : ℝ × Space → CVec3} (hA : IsPhaseSchwartz P r A) :
    IsSliceTest P r (L0T ν A) := by
  have e : L0T ν A = (driftT A + -((ν : ℂ) • lapT A)) + -(((1 / 2 : ℝ) : ℂ) • A) := by
    funext p
    simp only [L0T, nuLapT, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
      Complex.coe_smul]
    abel
  rw [e]
  exact (hA.sliceTest_driftT.add (hA.sliceTest_lapT.const_smul (ν : ℂ)).neg).add
    (hA.sliceTest.const_smul ((1 / 2 : ℝ) : ℂ)).neg

theorem testElem_L0T (ν : ℝ) {A : ℝ × Space → CVec3}
    (hA : IsPhaseSchwartz P r A) :
    testElem P r (L0T ν A) =
      testElem P r (driftT A) - (ν : ℂ) • testElem P r (lapT A) -
        ((1 / 2 : ℝ) : ℂ) • testElem P r A := by
  have h1 : IsSliceTest P r (driftT A) := hA.sliceTest_driftT
  have h2 : IsSliceTest P r ((ν : ℂ) • lapT A) := hA.sliceTest_lapT.const_smul (ν : ℂ)
  have h3 : IsSliceTest P r (((1 / 2 : ℝ) : ℂ) • A) := hA.sliceTest.const_smul ((1 / 2 : ℝ) : ℂ)
  have e : L0T ν A = (driftT A + -((ν : ℂ) • lapT A)) + -(((1 / 2 : ℝ) : ℂ) • A) := by
    funext p
    simp only [L0T, nuLapT, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
      Complex.coe_smul]
    abel
  rw [e, testElem_add (h1.add h2.neg) h3.neg, testElem_add h1 h2.neg,
    testElem_neg h2, testElem_neg h3,
    testElem_const_smul hA.sliceTest_lapT, testElem_const_smul hA.sliceTest]
  abel

end SchwartzAlgebra

/-! ### Rescaled compact multiplier profiles (`SmallProfile`) -/

/-- A sequence of spatial multipliers of the form `m n y = s n * b (cutC n • y)` with `b` smooth
and compactly supported and `s n → 0` bounded. -/
structure SmallProfile (m : ℕ → Space → ℝ) : Type where
  b : Space → ℝ
  s : ℕ → ℝ
  S : ℝ
  hb : ContDiff ℝ ∞ b
  hbs : HasCompactSupport b
  hS : ∀ n, |s n| ≤ S
  hs : Tendsto s atTop (𝓝 0)
  hm : ∀ n y, m n y = s n * b (cutC n • y)

namespace SmallProfile

theorem goodMult {m : ℕ → Space → ℝ} (h : SmallProfile m) : GoodMult m := by
  obtain ⟨B, hB⟩ := bounded_of_compact h.hb.continuous h.hbs
  have hg := goodMult_of_small h.hb.continuous hB h.hS h.hs
  have heq : m = fun n y => h.s n * h.b (cutC n • y) := funext fun n => funext (h.hm n)
  rwa [heq]

def const_mul {m : ℕ → Space → ℝ} (h : SmallProfile m) (c : ℝ) :
    SmallProfile fun n y => c * m n y where
  b := h.b
  s n := c * h.s n
  S := |c| * max h.S 0
  hb := h.hb
  hbs := h.hbs
  hS n := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((h.hS n).trans (le_max_left _ _)) (abs_nonneg c)
  hs := by simpa using h.hs.const_mul c
  hm n y := by rw [h.hm n y, mul_assoc]

def sd {m : ℕ → Space → ℝ} (h : SmallProfile m) (k : Fin 3) :
    SmallProfile fun n y => PhaseSpace.sd k (m n) y where
  b := PhaseSpace.sd k h.b
  s n := h.s n * cutC n
  S := max h.S 0
  hb := contDiff_sd h.hb k
  hbs := hasCompactSupport_sd h.hbs k
  hS n := by
    rw [abs_mul, abs_of_pos (cutC_pos n)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (cutC_le_one n)).trans
      ((h.hS n).trans (le_max_left _ _))
  hs := by simpa using h.hs.mul tendsto_cutC
  hm n y := by
    have hmn : m n = fun z => h.s n * h.b (cutC n • z) := funext (h.hm n)
    have hbd : Differentiable ℝ h.b := h.hb.differentiable (by simp)
    have hbc : Differentiable ℝ (fun z => h.b (cutC n • z)) :=
      hbd.comp (differentiable_id.const_smul (cutC n))
    rw [hmn, sd_const_mul hbc (h.s n) k, sd_comp_smul hbd (cutC n) k]
    ring

def radS {m : ℕ → Space → ℝ} (h : SmallProfile m) :
    SmallProfile fun n y => PhaseSpace.radS (m n) y where
  b := PhaseSpace.radS h.b
  s := h.s
  S := h.S
  hb := ContDiff.sum fun j _ => (contDiff_coord j).mul (contDiff_sd h.hb j)
  hbs := by
    refine h.hbs.mono' fun z hz => ?_
    by_contra hzt
    apply hz
    simp [PhaseSpace.radS, PhaseSpace.sd, fderiv_of_notMem_tsupport ℝ hzt]
  hS := h.hS
  hs := h.hs
  hm n y := by
    have hsd : ∀ j : Fin 3, PhaseSpace.sd j (m n) y =
        (h.s n * cutC n) * PhaseSpace.sd j h.b (cutC n • y) := fun j => (h.sd j).hm n y
    simp only [PhaseSpace.radS, hsd, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end SmallProfile

def smallProfile_sd_cutχ (j : Fin 3) :
    SmallProfile fun n y => sd j (cutχ n) y where
  b := sd j (unitBump : Space → ℝ)
  s := cutC
  S := 1
  hb := contDiff_sd contDiff_unitBump j
  hbs := hasCompactSupport_sd unitBump.hasCompactSupport j
  hS n := by rw [abs_of_pos (cutC_pos n)]; exact cutC_le_one n
  hs := tendsto_cutC
  hm n y := congrFun (sd_cutχ n j) y

/-! ### Convergence of `dy j (mulT (cutχ n) U)` in the `L0T` graph norm -/

section DyCutGraph

variable {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]

theorem driftT_dy_cut_decomp {U : ℝ × Space → CVec3} (hU : IsPhaseSchwartz P r U)
    (hdU : ∀ j, IsPhaseSchwartz P r (dy j U)) (j : Fin 3) (n : ℕ) :
    driftT (dy j (mulT (cutχ n) U)) =
      driftT (dy j U) +
        ((mulT (fun y => cutχ n y - 1) (driftT (dy j U)) +
          mulT (fun y => (1 / 2 : ℝ) * radS (cutχ n) y) (dy j U)) +
        (mulT (fun y => sd j (cutχ n) y) (driftT U) +
          mulT (fun y => (1 / 2 : ℝ) * radS (sd j (cutχ n)) y) U)) := by
  have h1 : dy j (mulT (cutχ n) U) = mulT (cutχ n) (dy j U) + mulT (sd j (cutχ n)) U :=
    dy_mulT ((contDiff_cutχ n).differentiable (by simp)) (hU.smooth.differentiable (by simp)) j
  rw [h1, driftT_add_smooth (contDiff_mulT (contDiff_cutχ n) (hdU j).smooth)
      (contDiff_mulT (contDiff_sd (contDiff_cutχ n) j) hU.smooth),
    driftT_cut_decomp (hdU j) n]
  funext p
  simp only [Pi.add_apply]
  rw [driftT_mulT_apply (contDiff_sd (contDiff_cutχ n) j) hU.smooth p]
  simp only [mulT]
  module

theorem lapT_dy_cut_decomp {U : ℝ × Space → CVec3} (hU : IsPhaseSchwartz P r U)
    (hdU : ∀ j, IsPhaseSchwartz P r (dy j U)) (j : Fin 3) (n : ℕ) :
    lapT (dy j (mulT (cutχ n) U)) =
      lapT (dy j U) +
        ((mulT (fun y => cutχ n y - 1) (lapT (dy j U)) +
          (∑ k : Fin 3, mulT (fun y => 2 * sd k (cutχ n) y) (dy k (dy j U)) +
            mulT (fun y => lapS (cutχ n) y) (dy j U))) +
        (mulT (fun y => sd j (cutχ n) y) (lapT U) +
          (∑ k : Fin 3, mulT (fun y => 2 * sd k (sd j (cutχ n)) y) (dy k U) +
            ∑ k : Fin 3, mulT (fun y => sd k (sd k (sd j (cutχ n))) y) U))) := by
  have h1 : dy j (mulT (cutχ n) U) = mulT (cutχ n) (dy j U) + mulT (sd j (cutχ n)) U :=
    dy_mulT ((contDiff_cutχ n).differentiable (by simp)) (hU.smooth.differentiable (by simp)) j
  rw [h1, lapT_add_smooth (contDiff_mulT (contDiff_cutχ n) (hdU j).smooth)
      (contDiff_mulT (contDiff_sd (contDiff_cutχ n) j) hU.smooth),
    lapT_cut_decomp (hdU j) n]
  funext p
  simp only [Pi.add_apply]
  rw [lapT_mulT_apply (contDiff_sd (contDiff_cutχ n) j) hU.smooth p]
  simp only [mulT, lapS, Finset.sum_apply, Finset.sum_smul]
  module

variable (hr : r ≠ ⊤)
include hr

theorem tendsto_dy_cut {U : ℝ × Space → CVec3} (hU : IsPhaseSchwartz P r U) (j : Fin 3) :
    Tendsto (fun n => testElem P r (dy j (mulT (cutχ n) U))) atTop
      (𝓝 (testElem P r (dy j U))) := by
  have h := (tendsto_cut_dy hr hU j).neg
  have h1 : ∀ n, -testElem P r (-dy j (mulT (cutχ n) U)) =
      testElem P r (dy j (mulT (cutχ n) U)) := fun n => by
    rw [testElem_neg (((hU.isPhaseTest_cut n).dy j).isSliceTest r), neg_neg]
  have h2 : -testElem P r (-dy j U) = testElem P r (dy j U) := by
    rw [testElem_neg (hU.sliceTest_dy j), neg_neg]
  simpa only [h1, h2] using h

theorem tendsto_driftT_dy_cut {U : ℝ × Space → CVec3} (hU : IsPhaseSchwartz P r U)
    (hdU : ∀ j, IsPhaseSchwartz P r (dy j U)) (j : Fin 3) :
    Tendsto (fun n => testElem P r (driftT (dy j (mulT (cutχ n) U)))) atTop
      (𝓝 (testElem P r (driftT (dy j U)))) :=
  tendsto_testElem_of_null (hdU j).sliceTest_driftT
    (((NullSeq.mulT hr goodMult_cutχ_sub_one (hdU j).sliceTest_driftT).add
      (NullSeq.mulT hr goodMult_radS_cutχ (hdU j).sliceTest)).add
      ((NullSeq.mulT hr (smallProfile_sd_cutχ j).goodMult hU.sliceTest_driftT).add
        (NullSeq.mulT hr (((smallProfile_sd_cutχ j).radS).const_mul (1 / 2 : ℝ)).goodMult
          hU.sliceTest)))
    (driftT_dy_cut_decomp hU hdU j)

theorem tendsto_lapT_dy_cut {U : ℝ × Space → CVec3} (hU : IsPhaseSchwartz P r U)
    (hdU : ∀ j, IsPhaseSchwartz P r (dy j U)) (j : Fin 3) :
    Tendsto (fun n => testElem P r (lapT (dy j (mulT (cutχ n) U)))) atTop
      (𝓝 (testElem P r (lapT (dy j U)))) :=
  tendsto_testElem_of_null (hdU j).sliceTest_lapT
    (((NullSeq.mulT hr goodMult_cutχ_sub_one (hdU j).sliceTest_lapT).add
      ((NullSeq.sum Finset.univ fun k _ =>
          NullSeq.mulT hr (goodMult_sd_cutχ k 2) ((hdU j).sliceTest_dy k)).add
        (NullSeq.mulT hr goodMult_lapS_cutχ (hdU j).sliceTest))).add
      ((NullSeq.mulT hr (smallProfile_sd_cutχ j).goodMult hU.sliceTest_lapT).add
        ((NullSeq.sum Finset.univ fun k _ =>
            NullSeq.mulT hr (((smallProfile_sd_cutχ j).sd k).const_mul 2).goodMult
              (hU.sliceTest_dy k)).add
          (NullSeq.sum Finset.univ fun k _ =>
            NullSeq.mulT hr (((smallProfile_sd_cutχ j).sd k).sd k).goodMult hU.sliceTest))))
    (lapT_dy_cut_decomp hU hdU j)

theorem tendsto_L0T_dy_cut (ν : ℝ) {U : ℝ × Space → CVec3} (hU : IsPhaseSchwartz P r U)
    (hdU : ∀ j, IsPhaseSchwartz P r (dy j U)) (j : Fin 3) :
    Tendsto (fun n => testElem P r (L0T ν (dy j (mulT (cutχ n) U)))) atTop
      (𝓝 (testElem P r (L0T ν (dy j U)))) := by
  have hc : ∀ n, IsPhaseSchwartz P r (dy j (mulT (cutχ n) U)) := fun n =>
    ((hU.isPhaseTest_cut n).dy j).isPhaseSchwartz r
  simp only [testElem_L0T ν (hc _), testElem_L0T ν (hdU j)]
  exact (((tendsto_driftT_dy_cut hr hU hdU j).sub
    ((tendsto_lapT_dy_cut hr hU hdU j).const_smul (ν : ℂ))).sub
    ((tendsto_dy_cut hr hU j).const_smul ((1 / 2 : ℝ) : ℂ)))

end DyCutGraph

end UnforcedLeray.Short.PartIIa.F15c
