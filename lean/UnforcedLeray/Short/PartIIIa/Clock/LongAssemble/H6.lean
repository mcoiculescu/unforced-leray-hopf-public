import UnforcedLeray.Short.PartIIIa.Clock.Moving
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H1
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H5
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L2

/-!
# Part III-a long assembly, H6: uniform bounds on `[t, s]` and finiteness of the running supremum

With `S = sup_{r ∈ [t,s]} ‖w(r)‖_{X_{m,c}}` (finite by L2), every quantity of the moving frame is
bounded uniformly on `[t, s]`:
`amplNorm F w r ≤ 2 k a(s)^{3/2} S` and `‖compl F w r‖ ≤ a(s)^{3/2} S + k · amplNorm F w r`.
Dividing by the normaliser `N(t,r) ≥ n₀ > 0` (H1), the running supremum of
`amplNorm F w r / N(t,r)` is finite (SP 3002-3004, the amplitude is continuous in the age).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

lemma pointwise_bounds {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t s : ℝ} {f : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s) (hm : 0 ≤ m) (hb : ∀ r ∈ Icc t s, b ≤ clockTheta ν r)
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (k : ℝ≥0∞) (hk : ENNReal.ofReal K ≤ k) (r : ℝ)
    (hr : r ∈ Icc t s) :
    amplNorm F w r ≤ 2 * (k * (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) *
        ⨆ r' ∈ Icc t s, xNorm (ν ^ (-2 : ℝ)) m (w r'))) ∧
    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) ≤
      ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) * (⨆ r' ∈ Icc t s, xNorm (ν ^ (-2 : ℝ)) m (w r')) +
        k * (2 * (k * (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) *
          ⨆ r' ∈ Icc t s, xNorm (ν ^ (-2 : ℝ)) m (w r')))) := by
  have hr0 : 0 ≤ r := ht.trans hr.1
  have hwr : MemLp (w r) 2 (UnforcedLeray.B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hw.memX r hr.1
  set S := ⨆ r' ∈ Icc t s, xNorm (ν ^ (-2 : ℝ)) m (w r') with hSdef
  have hWS : xNorm (ν ^ (-2 : ℝ)) m (w r) ≤ S := le_iSup₂ (f := fun r' (_ : r' ∈ Icc t s) =>
    xNorm (ν ^ (-2 : ℝ)) m (w r')) r hr
  have hA : ENNReal.ofReal ((clockA ν r) ^ ((3 : ℝ) / 2)) ≤
      ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by linarith [one_le_clockA hν.le hr0])
      (clockA_mono hν.le hr.2) (by norm_num))
  have hXW : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movingW ν w r) ≤
      ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) * S := by
    have h1 := xNorm_movingW_scale hν.le hr0 hm hwr
    calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movingW ν w r)
        ≤ ENNReal.ofReal ((clockA ν r) ^ ((3 : ℝ) / 2)) * xNorm (ν ^ (-2 : ℝ)) m (w r) := h1
      _ ≤ ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) * S := by gcongr
  have hamp := amplNorm_le_of F w hr0 (hb r hr) k hk
  constructor
  · calc amplNorm F w r
        ≤ 2 * (k * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movingW ν w r)) := hamp
      _ ≤ 2 * (k * (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) * S)) := by gcongr
  · have hc := xNorm_compl_le F w hν.le hr0 (hb r hr) hwr k hk
    have hamp' : amplNorm F w r ≤ 2 * (k * (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) * S)) := by
      calc amplNorm F w r
          ≤ 2 * (k * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movingW ν w r)) := hamp
        _ ≤ 2 * (k * (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) * S)) := by gcongr
    calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r)
        ≤ xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movingW ν w r) + k * amplNorm F w r := hc
      _ ≤ ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) * S +
            k * (2 * (k * (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) * S))) := by
          gcongr

lemma sup_ratio_ne_top {P : PlanarData} {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t s : ℝ} {f : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s) (hm : 0 ≤ m) (hb : ∀ r ∈ Icc t s, b ≤ clockTheta ν r)
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (k : ℝ≥0∞) (hk : ENNReal.ofReal K ≤ k)
    (hk' : k ≠ ⊤) :
    (⨆ r ∈ Icc t s, amplNorm F w r / ENNReal.ofReal (clockN P ν t r)) ≠ ⊤ := by
  obtain ⟨n0, hn0, hN⟩ := clockN_lower P hν ht hts
  have hS : (⨆ r ∈ Icc t s, xNorm (ν ^ (-2 : ℝ)) m (w r)) ≠ ⊤ := xNorm_bounded_on_Icc hw
  have hM : 2 * (k * (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) *
        ⨆ r' ∈ Icc t s, xNorm (ν ^ (-2 : ℝ)) m (w r'))) / ENNReal.ofReal n0 ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.mul_ne_top hk' (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS))
    · exact (ENNReal.ofReal_pos.2 hn0).ne'
  refine ne_top_of_le_ne_top hM (iSup₂_le fun r hr => ?_)
  have hpb := (pointwise_bounds F hν ht hts hm hb hw k hk r hr).1
  calc amplNorm F w r / ENNReal.ofReal (clockN P ν t r)
      ≤ amplNorm F w r / ENNReal.ofReal n0 :=
        ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal (hN r hr)) (amplNorm F w r)
    _ ≤ 2 * (k * (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) *
          ⨆ r' ∈ Icc t s, xNorm (ν ^ (-2 : ℝ)) m (w r'))) / ENNReal.ofReal n0 :=
        ENNReal.div_le_div_right hpb _

end UnforcedLeray.Short.IIIa
