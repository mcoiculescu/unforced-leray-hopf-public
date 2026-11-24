import UnforcedLeray.Short.PartIIIa.Clock.Moving
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H1
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H5
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H6
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H7
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L3

/-!
# Part III-a long assembly, H8: the long estimate for one flow, from the frame and the Gronwall budget

For a moving frame `F` satisfying `FrameStable` and `FrameAmplitude` with constant `C'`, and the
Gronwall output for `(a, ρ)` (`a` the normalised amplitude, `ρ` the normalised complement), the
moving-coordinate norm at age `s` is bounded by `C N(t,s) ‖J_{a_t}⁻¹ f‖` with
`C = (1+K⁺)G⁺(1+2K⁺+2K⁺²)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem long_core {P : PlanarData} {ν m b K KG Kp Gp C' h₀ t s : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {f : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s) (hm : 0 ≤ m) (hbs : b ≤ clockTheta ν s)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (hz : HasZeroCirculation (ν ^ (-2 : ℝ)) f)
    (hKp : 0 ≤ Kp) (hK : K ≤ Kp) (hGp : 0 ≤ Gp) (hKG : KG ≤ Gp)
    (hSt : FrameStable P F C' h₀) (hAm : FrameAmplitude P F C')
    (hGr : ∀ a ρ : ℝ → ℝ≥0∞, (∀ r ∈ Icc t s, a r ≠ ⊤ ∧ ρ r ≠ ⊤) →
        AEMeasurable a (volume.restrict (Icc t s)) →
        AEMeasurable ρ (volume.restrict (Icc t s)) →
        (⨆ r ∈ Icc t s, a r) ≠ ⊤ →
        (∀ s' ∈ Icc t s, a s' ≤ a t +
          ∫⁻ r in Ioc t s', ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
            (ENNReal.ofReal (C' * ν ^ 3 / clockTheta ν r) * a r +
              ENNReal.ofReal (C' * (1 / clockTheta ν r + C' * ν ^ 3 / clockTheta ν r)) * ρ r)) →
        (∀ s' ∈ Icc t s, ρ s' ≤
          ENNReal.ofReal (C' * Real.exp (-h₀ * (movingZ ν s' - movingZ ν t))) * ρ t +
            ENNReal.ofReal (C' * (C' * (1 + ν ^ 3) / clockTheta ν s')) * ⨆ r ∈ Icc t s', a r) →
        a s + ρ s ≤ ENNReal.ofReal KG * (a t + ρ t)) :
    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (movingW ν w s) ≤
      ENNReal.ofReal ((1 + Kp) * Gp * (1 + 2 * Kp + 2 * Kp * Kp) * clockN P ν t s) *
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (JscaleInv (clockA ν t) f) := by
  have hbθ : ∀ r ∈ Icc t s, b ≤ clockTheta ν r := fun r hr =>
    hbs.trans (theta_anti hν (ht.trans hr.1) hr.2)
  have hk : ENNReal.ofReal K ≤ ENNReal.ofReal Kp := ENNReal.ofReal_le_ofReal hK
  have hkfin : ENNReal.ofReal Kp ≠ ⊤ := ENNReal.ofReal_ne_top
  have hNtt : ENNReal.ofReal (clockN P ν t t) = 1 := by
    rw [clockN_self P hν ht, ENNReal.ofReal_one]
  have hsup := sup_ratio_ne_top (P := P) F hν ht hts hm hbθ hw (ENNReal.ofReal Kp) hk hkfin
  have hfinS := xNorm_bounded_on_Icc (s := s) hw
  have hpb := fun r hr => pointwise_bounds F hν ht hts hm hbθ hw (ENNReal.ofReal Kp) hk r hr
  have hfin_a : ∀ r ∈ Icc t s,
      amplNorm F w r / ENNReal.ofReal (clockN P ν t r) ≠ ⊤ := fun r hr =>
    ne_top_of_le_ne_top hsup
      (le_iSup₂ (f := fun r' (_ : r' ∈ Icc t s) =>
        amplNorm F w r' / ENNReal.ofReal (clockN P ν t r')) r hr)
  have hfin_ρ : ∀ r ∈ Icc t s,
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) /
        ENNReal.ofReal (clockN P ν t r) ≠ ⊤ := by
    intro r hr
    have hpos : 0 < clockN P ν t r := clockN_pos P hν ht (ht.trans hr.1)
    apply ENNReal.div_ne_top _ (ENNReal.ofReal_pos.2 hpos).ne'
    apply ne_top_of_le_ne_top _ (hpb r hr).2
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinS,
      ENNReal.mul_ne_top hkfin (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.mul_ne_top hkfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinS)))⟩
  have hGap := hSt tr htr t s ht hts hbs f w u hw hz
  -- the Gronwall hypotheses
  have ineqA : ∀ s' ∈ Icc t s,
      amplNorm F w s' / ENNReal.ofReal (clockN P ν t s') ≤
        amplNorm F w t / ENNReal.ofReal (clockN P ν t t) +
          ∫⁻ r in Ioc t s', ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
            (ENNReal.ofReal (C' * ν ^ 3 / clockTheta ν r) *
                (amplNorm F w r / ENNReal.ofReal (clockN P ν t r)) +
              ENNReal.ofReal (C' * (1 / clockTheta ν r + C' * ν ^ 3 / clockTheta ν r)) *
                (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) /
                  ENNReal.ofReal (clockN P ν t r))) := by
    intro s' hs'
    have hA := hAm tr htr t s' ht hs'.1 (hbθ s' hs') f w u hw hz
    rw [hNtt, div_one]
    exact hA
  have ineqR : ∀ s' ∈ Icc t s,
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s')) m (compl F w s') /
          ENNReal.ofReal (clockN P ν t s') ≤
        ENNReal.ofReal (C' * Real.exp (-h₀ * (movingZ ν s' - movingZ ν t))) *
            (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (compl F w t) /
              ENNReal.ofReal (clockN P ν t t)) +
          ENNReal.ofReal (C' * (C' * (1 + ν ^ 3) / clockTheta ν s')) *
            ⨆ r ∈ Icc t s', amplNorm F w r / ENNReal.ofReal (clockN P ν t r) := by
    intro s' hs'
    have hS := (hSt tr htr t s' ht hs'.1 (hbθ s' hs') f w u hw hz).2.2
    rw [hNtt, div_one]
    apply ENNReal.div_le_of_le_mul
    exact hS.trans (le_of_eq (mul_comm _ _))
  have hG := hGr (fun r => amplNorm F w r / ENNReal.ofReal (clockN P ν t r))
    (fun r => xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) /
      ENNReal.ofReal (clockN P ν t r))
    (fun r hr => ⟨hfin_a r hr, hfin_ρ r hr⟩)
    (hGap.1) (hGap.2.1) hsup ineqA ineqR
  have hGpos : 0 < clockN P ν t s := clockN_pos P hν ht (ht.trans hts)
  have hNs : ENNReal.ofReal (clockN P ν t s) ≠ 0 := (ENNReal.ofReal_pos.2 hGpos).ne'
  have hNs' : ENNReal.ofReal (clockN P ν t s) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hW1 := xNorm_movingW_le_compl F w hν.le (ht.trans hts) hbs (hw.memX s hts)
    (ENNReal.ofReal Kp) hk
  have hYs : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) =
      (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) /
        ENNReal.ofReal (clockN P ν t s)) * ENNReal.ofReal (clockN P ν t s) :=
    (ENNReal.div_mul_cancel hNs hNs').symm
  have hAs : amplNorm F w s =
      (amplNorm F w s / ENNReal.ofReal (clockN P ν t s)) * ENNReal.ofReal (clockN P ν t s) :=
    (ENNReal.div_mul_cancel hNs hNs').symm
  have htmem : t ∈ Icc t s := ⟨le_rfl, hts⟩
  have hAt := amplNorm_le_of F w ht (hbθ t htmem) (ENNReal.ofReal Kp) hk
  have hYt := xNorm_compl_le F w hν.le ht (hbθ t htmem) (hw.memX t le_rfl) (ENNReal.ofReal Kp) hk
  have hG2 : amplNorm F w s / ENNReal.ofReal (clockN P ν t s) +
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) /
        ENNReal.ofReal (clockN P ν t s) ≤
      ENNReal.ofReal KG * (amplNorm F w t + xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (compl F w t)) := by
    have h := hG
    simp only [hNtt, div_one] at h
    exact h
  have hG3 : amplNorm F w s / ENNReal.ofReal (clockN P ν t s) +
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) /
        ENNReal.ofReal (clockN P ν t s) ≤
      ENNReal.ofReal Gp * (amplNorm F w t + xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (compl F w t)) :=
    hG2.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hKG) zero_le)
  have hfinal := algebra_step (ENNReal.ofReal Kp) (ENNReal.ofReal Gp) (ENNReal.ofReal (clockN P ν t s))
    (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (movingW ν w s))
    (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s))
    (amplNorm F w s)
    (amplNorm F w s / ENNReal.ofReal (clockN P ν t s))
    (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (compl F w s) / ENNReal.ofReal (clockN P ν t s))
    (amplNorm F w t)
    (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (compl F w t))
    (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (movingW ν w t))
    hW1 hYs hAs hAt hYt hG3
  have hL3 : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (movingW ν w t) =
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (JscaleInv (clockA ν t) f) :=
    xNorm_JscaleInv_ae_eq hw
  rw [ofReal_cout Kp Gp _ hKp hGp (clockN_pos P hν ht (ht.trans hts)).le, ← hL3]
  refine hfinal.trans (le_of_eq ?_)
  ring

end UnforcedLeray.Short.IIIa
