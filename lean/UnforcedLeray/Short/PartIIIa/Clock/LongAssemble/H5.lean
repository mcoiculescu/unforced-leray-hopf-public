import UnforcedLeray.Short.PartIIIa.Clock.Moving
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H1
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H3
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H4

/-!
# Part III-a long assembly, H5: frame bounds at a single age

For a moving frame `F` with `ofReal K ≤ k` and an age `r ≥ 0` with `b ≤ θ(r)`:
* `amplNorm F w r ≤ 2 k ‖W(r)‖` (lam_bdd, SP 2991-2997),
* `‖compl F w r‖ ≤ ‖W(r)‖ + k amplNorm` and `‖W(r)‖ ≤ ‖compl F w r‖ + k amplNorm`,
  the two triangle inequalities for `W = compl + Σ α_i E_i`,
* `‖W(r)‖ ≤ ofReal(a^{3/2}) ‖w(r)‖_{X_{m,c}}` with `a = clockA ν r` (L4).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

lemma xNorm_movingW_scale {ν m r : ℝ} {w : ℝ × ℝ → ℂ} (hν : 0 ≤ ν) (hr : 0 ≤ r) (hm : 0 ≤ m)
    (hw : MemLp w 2 (UnforcedLeray.B0579.cellMeasure (ν ^ (-2 : ℝ)) m)) :
    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (JscaleInv (clockA ν r) w) ≤
      ENNReal.ofReal ((clockA ν r) ^ ((3 : ℝ) / 2)) * xNorm (ν ^ (-2 : ℝ)) m w :=
  xNorm_JscaleInv_le _ m _ hm (one_le_clockA hν hr) w hw

lemma amplNorm_le_of {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (w : ℝ → ℝ × ℝ → ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hb : b ≤ clockTheta ν r) (k : ℝ≥0∞) (hk : ENNReal.ofReal K ≤ k) :
    amplNorm F w r ≤ 2 * (k * xNorm (cellLen c (clockA ν r)) m (movingW ν w r)) := by
  have hi : ∀ i : Fin 2, ENNReal.ofReal ‖ampl F w r i‖ ≤
      k * xNorm (cellLen c (clockA ν r)) m (movingW ν w r) := by
    intro i
    have h1 := F.lam_bdd r hr hb i (movingW ν w r)
    unfold ampl
    exact h1.trans (mul_le_mul_of_nonneg_right hk zero_le)
  unfold amplNorm
  calc ∑ i, ENNReal.ofReal ‖ampl F w r i‖
      ≤ ∑ _i : Fin 2, k * xNorm (cellLen c (clockA ν r)) m (movingW ν w r) :=
        Finset.sum_le_sum (fun i _ => hi i)
    _ = 2 * (k * xNorm (cellLen c (clockA ν r)) m (movingW ν w r)) := by
        rw [Fin.sum_univ_two]
        ring

lemma aesm_movingW {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (w : ℝ → ℝ × ℝ → ℂ) {r : ℝ} (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (hw : MemLp (w r) 2 (UnforcedLeray.B0579.cellMeasure (ν ^ (-2 : ℝ)) m)) :
    AEStronglyMeasurable (movingW ν w r) (UnforcedLeray.B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
  aesm_JscaleInv (one_le_clockA hν hr) hw

lemma xNorm_compl_le {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (w : ℝ → ℝ × ℝ → ℂ) {r : ℝ} (hν : 0 ≤ ν) (hr : 0 ≤ r) (hb : b ≤ clockTheta ν r)
    (hw : MemLp (w r) 2 (UnforcedLeray.B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (k : ℝ≥0∞) (hk : ENNReal.ofReal K ≤ k) :
    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) ≤
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movingW ν w r) + k * amplNorm F w r := by
  have hW := aesm_movingW F w hν hr hw
  have hE : ∀ i, AEStronglyMeasurable (F.E r i)
      (UnforcedLeray.B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
    fun i => (F.E_meas r hr hb i).mono_ac (UnforcedLeray.B0579.cellMeasure_ac _ _)
  have hEb : ∀ i, eLpNorm (F.E r i) 2
      (UnforcedLeray.B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) ≤ k :=
    fun i => (F.E_bdd r hr hb i).trans hk
  have h := eLpNorm_sub_sum_le (W := movingW ν w r) (ampl F w r) (F.E r) k hW hE hEb
  unfold xNorm amplNorm
  rw [mul_comm k]
  exact h

lemma xNorm_movingW_le_compl {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (w : ℝ → ℝ × ℝ → ℂ) {r : ℝ} (hν : 0 ≤ ν) (hr : 0 ≤ r) (hb : b ≤ clockTheta ν r)
    (hw : MemLp (w r) 2 (UnforcedLeray.B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (k : ℝ≥0∞) (hk : ENNReal.ofReal K ≤ k) :
    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movingW ν w r) ≤
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) + k * amplNorm F w r := by
  have hW := aesm_movingW F w hν hr hw
  have hE : ∀ i, AEStronglyMeasurable (F.E r i)
      (UnforcedLeray.B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) :=
    fun i => (F.E_meas r hr hb i).mono_ac (UnforcedLeray.B0579.cellMeasure_ac _ _)
  have hEb : ∀ i, eLpNorm (F.E r i) 2
      (UnforcedLeray.B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) ≤ k :=
    fun i => (F.E_bdd r hr hb i).trans hk
  have h := eLpNorm_le_sub_sum_add (W := movingW ν w r) (ampl F w r) (F.E r) k hW hE hEb
  unfold xNorm amplNorm
  rw [mul_comm k]
  exact h

end UnforcedLeray.Short.IIIa
