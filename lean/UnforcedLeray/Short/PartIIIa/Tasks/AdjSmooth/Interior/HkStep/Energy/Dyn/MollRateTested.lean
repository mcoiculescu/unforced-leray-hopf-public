import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_8

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The mollifier kernel is smooth, compactly supported, and vanishes outside the unit ball. -/
theorem molKer_props_mrt (n : ℕ) :
    ContDiff ℝ ∞ (molKer n) ∧ HasCompactSupport (molKer n) ∧
      ∀ y : ℝ × ℝ, 1 < ‖y‖ → molKer n y = 0 := by
  refine ⟨(molBump n).contDiff_normed, (molBump n).hasCompactSupport_normed, ?_⟩
  intro y hy
  have hr : (molBump n).rOut ≤ 1 := by
    show 1 / ((n : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hd : (molBump n).rOut ≤ dist y (0 : ℝ × ℝ) := by
    rw [dist_zero_right]; linarith
  show (molBump n).normed volume y = 0
  rw [ContDiffBump.normed_def, (molBump n).zero_of_le_dist hd, zero_div]

/-- Integration by parts twice against a cylinder test. -/
theorem ibp_pdpd_mrt (hIBP : UnforcedLeray.Short.IIIa.CellIBP) (c : ℝ) (hc : 0 < c)
    (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (hGp : ∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x)
    (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest c ψ) (l : Fin 2) :
    ∫ x in B0579.cell c, adjSpatial [l, l] G x * (ψ x : ℂ) =
      ∫ x in B0579.cell c, G x * (B0579.pd l (B0579.pd l ψ) x : ℂ) := by
  have h1 := hIBP c (pdCx l G) ψ hc (UnforcedLeray.Short.IIIa.AdjE1.pdCx_contDiff hG l)
    (UnforcedLeray.Short.IIIa.AdjE1.pdCx_periodic c hGp l) hψ l
  have h2 := hIBP c G (B0579.pd l ψ) hc hG hGp (hψ.pd l) l
  simp only [adjSpatial]
  rw [h2, h1, neg_neg]

theorem mollRateTested (m : ℝ) (hDual : UnforcedLeray.Short.IIIa.MollDual)
    (hIBP : UnforcedLeray.Short.IIIa.CellIBP) (hS : UnforcedLeray.Short.IIIa.AdjIntegrandSplit m)
    (hV : UnforcedLeray.Short.IIIa.VelMulMemX m) (hX : UnforcedLeray.Short.IIIa.XMulTestInt)
    (hD : UnforcedLeray.Short.IIIa.CellConvDeriv) (hM : UnforcedLeray.Short.IIIa.CellMollSmooth) :
    UnforcedLeray.Short.IIIa.MollRateTested m := by
  intro ν tr t s g φ a b χ hctx n ψ hψ u' hK r hr
  have hctx0 := hctx
  obtain ⟨hν, -, -, -, -, hW, -, hta, hab, hbs, hChi⟩ := hctx0
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hrW : r ∈ Ico t s := ⟨le_trans hta hr.1.le, hr.2.trans hbs⟩
  have hrI : r ∈ Icc t s := ⟨le_trans hta hr.1.le, le_trans hr.2.le hbs.le⟩
  have hrC : r ∈ Icc a b := Ioo_subset_Icc_self hr
  have hφp : ∀ x : ℝ × ℝ, φ r (x.1 + ν ^ (-2 : ℝ), x.2) = φ r x := hW.periodic r hrW
  have hφm : MemLp (φ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := hW.memX r hrI
  have hχp : ∀ x : ℝ × ℝ, χ r (x.1 + ν ^ (-2 : ℝ), x.2) = χ r x := (hChi r hrC).1
  have hχm : MemLp (χ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := (hChi r hrC).2.1
  have hVp : ∀ (l : Fin 2) (x : ℝ × ℝ),
      ((tr.v r (x.1 + ν ^ (-2 : ℝ), x.2) l : ℝ) : ℂ) * φ r (x.1 + ν ^ (-2 : ℝ), x.2) =
        ((tr.v r x l : ℝ) : ℂ) * φ r x :=
    fun l => (hV ν tr t s g φ a b χ hctx r hr l).1
  have hVm : ∀ l : Fin 2,
      MemLp (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun l => (hV ν tr t s g φ a b χ hctx r hr l).2
  have hG := hM (ν ^ (-2 : ℝ)) m n (φ r) hc hφp hφm
  have hGc : ContDiff ℝ ∞ (cellMoll n (φ r)) := hG.1
  have hGp : ∀ x : ℝ × ℝ, cellMoll n (φ r) (x.1 + ν ^ (-2 : ℝ), x.2) = cellMoll n (φ r) x := hG.2.1
  have hdu := hDual (ν ^ (-2 : ℝ)) m n hc ψ hψ
  have hψ' : B0579.IsCylTest (ν ^ (-2 : ℝ)) (mollR n ψ) := hdu.1
  have hpd : ∀ l : Fin 2, B0579.pd l (mollR n ψ) = mollR n (B0579.pd l ψ) := hdu.2.1
  have hpdpd : ∀ l : Fin 2,
      B0579.pd l (B0579.pd l (mollR n ψ)) = mollR n (B0579.pd l (B0579.pd l ψ)) := by
    intro l
    rw [hpd l]
    exact (hDual (ν ^ (-2 : ℝ)) m n hc (B0579.pd l ψ) (hψ.pd l)).2.1 l
  have hpart3 : ∀ h : ℝ × ℝ → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) h →
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), cellMoll n (φ r) x * (h x : ℂ) =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r x * (mollR n h x : ℂ) :=
    fun h hh => ((hDual (ν ^ (-2 : ℝ)) m n hc h hh).2.2 (φ r) hφp hφm).2
  -- the kernel identity for the velocity pieces
  have hKV : ∀ (l : Fin 2) (x : ℝ × ℝ),
      cellConv (B0579.pd l (molKer n)) (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y) x =
        pdCx l (cellMoll n (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y)) x := by
    intro l x
    have e := (hD (ν ^ (-2 : ℝ)) m (molKer n) (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y) hc
      (molKer_props_mrt n).1 (molKer_props_mrt n).2.1 (hVp l) (hVm l)).2.2 [l]
    simp only [adjSpatial, pdWordR] at e
    exact congrFun e.symm x
  -- integrability
  have hI00 : IntegrableOn (fun x => adjSpatial [0, 0] (cellMoll n (φ r)) x * (ψ x : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    hX (ν ^ (-2 : ℝ)) m (adjSpatial [0, 0] (cellMoll n (φ r))) ψ hc (hG.2.2 [0, 0]) hψ
  have hI11 : IntegrableOn (fun x => adjSpatial [1, 1] (cellMoll n (φ r)) x * (ψ x : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    hX (ν ^ (-2 : ℝ)) m (adjSpatial [1, 1] (cellMoll n (φ r))) ψ hc (hG.2.2 [1, 1]) hψ
  have hMl0 := hM (ν ^ (-2 : ℝ)) m n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ r y) hc (hVp 0) (hVm 0)
  have hMl1 := hM (ν ^ (-2 : ℝ)) m n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ r y) hc (hVp 1) (hVm 1)
  have hIK0 : IntegrableOn
      (fun x => pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    hX (ν ^ (-2 : ℝ)) m (adjSpatial [0] (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ r y)))
      ψ hc (hMl0.2.2 [0]) hψ
  have hIK1 : IntegrableOn
      (fun x => pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    hX (ν ^ (-2 : ℝ)) m (adjSpatial [1] (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ r y)))
      ψ hc (hMl1.2.2 [1]) hψ
  have hIC : IntegrableOn (fun x => cellMoll n (χ r) x * (ψ x : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    ((hDual (ν ^ (-2 : ℝ)) m n hc ψ hψ).2.2 (χ r) hχp hχm).1
  have hV0 : IntegrableOn (fun x => ((tr.v r x 0 : ℝ) : ℂ) * φ r x * (B0579.pd 0 (mollR n ψ) x : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    hX (ν ^ (-2 : ℝ)) m (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ r y) (B0579.pd 0 (mollR n ψ))
      hc (hVm 0) (hψ'.pd 0)
  have hV1 : IntegrableOn (fun x => ((tr.v r x 1 : ℝ) : ℂ) * φ r x * (B0579.pd 1 (mollR n ψ) x : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    hX (ν ^ (-2 : ℝ)) m (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ r y) (B0579.pd 1 (mollR n ψ))
      hc (hVm 1) (hψ'.pd 1)
  -- the pointwise splitting of the mollified rate
  have hsplit : ∀ x : ℝ × ℝ,
      mollRate ν (tr.v r) n (φ r) (χ r) x * (ψ x : ℂ) =
        -((ν : ℂ) * (adjSpatial [0, 0] (cellMoll n (φ r)) x * (ψ x : ℂ) +
            adjSpatial [1, 1] (cellMoll n (φ r)) x * (ψ x : ℂ)) +
          (pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ) +
            pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ)) -
          cellMoll n (χ r) x * (ψ x : ℂ)) := by
    intro x
    unfold mollRate
    simp only [Fin.sum_univ_two]
    rw [hKV 0 x, hKV 1 x]
    ring
  -- the three pieces
  have hF : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      (adjSpatial [0, 0] (cellMoll n (φ r)) x * (ψ x : ℂ) +
        adjSpatial [1, 1] (cellMoll n (φ r)) x * (ψ x : ℂ)) =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r x * (lapP (mollR n ψ) x : ℂ) := by
    rw [integral_add hI00 hI11,
      ibp_pdpd_mrt hIBP (ν ^ (-2 : ℝ)) hc (cellMoll n (φ r)) hGc hGp ψ hψ 0,
      ibp_pdpd_mrt hIBP (ν ^ (-2 : ℝ)) hc (cellMoll n (φ r)) hGc hGp ψ hψ 1,
      hpart3 _ ((hψ.pd 0).pd 0), hpart3 _ ((hψ.pd 1).pd 1)]
    have hpt : ∀ x : ℝ × ℝ, φ r x * (lapP (mollR n ψ) x : ℂ) =
        φ r x * (mollR n (B0579.pd 0 (B0579.pd 0 ψ)) x : ℂ) +
          φ r x * (mollR n (B0579.pd 1 (B0579.pd 1 ψ)) x : ℂ) := by
      intro x
      unfold lapP
      rw [hpdpd 0, hpdpd 1]
      push_cast
      ring
    have hA0 : IntegrableOn (fun x => φ r x * (mollR n (B0579.pd 0 (B0579.pd 0 ψ)) x : ℂ))
        (B0579.cell (ν ^ (-2 : ℝ))) :=
      hX (ν ^ (-2 : ℝ)) m (φ r) (mollR n (B0579.pd 0 (B0579.pd 0 ψ))) hc hφm
        ((hDual (ν ^ (-2 : ℝ)) m n hc (B0579.pd 0 (B0579.pd 0 ψ)) ((hψ.pd 0).pd 0)).1)
    have hA1 : IntegrableOn (fun x => φ r x * (mollR n (B0579.pd 1 (B0579.pd 1 ψ)) x : ℂ))
        (B0579.cell (ν ^ (-2 : ℝ))) :=
      hX (ν ^ (-2 : ℝ)) m (φ r) (mollR n (B0579.pd 1 (B0579.pd 1 ψ))) hc hφm
        ((hDual (ν ^ (-2 : ℝ)) m n hc (B0579.pd 1 (B0579.pd 1 ψ)) ((hψ.pd 1).pd 1)).1)
    simp only [hpt]
    rw [integral_add hA0 hA1]
  have hl : ∀ l : Fin 2,
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          pdCx l (cellMoll n (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ) =
        -∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ((tr.v r x l : ℝ) : ℂ) * φ r x * (B0579.pd l (mollR n ψ) x : ℂ) := by
    intro l
    have hMl := hM (ν ^ (-2 : ℝ)) m n (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y) hc (hVp l) (hVm l)
    have h1 := hIBP (ν ^ (-2 : ℝ)) (cellMoll n (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y)) ψ hc
      hMl.1 hMl.2.1 hψ l
    have h2 := (hDual (ν ^ (-2 : ℝ)) m n hc (B0579.pd l ψ) (hψ.pd l)).2.2
      (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y) (hVp l) (hVm l)
    have h2' : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        cellMoll n (fun y => ((tr.v r y l : ℝ) : ℂ) * φ r y) x * (B0579.pd l ψ x : ℂ) =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ((tr.v r x l : ℝ) : ℂ) * φ r x * (mollR n (B0579.pd l ψ) x : ℂ) := h2.2
    rw [h2'] at h1
    simp only [hpd l]
    rw [h1, neg_neg]
  have hQ : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      (pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ) +
        pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ)) =
      -∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        φ r x * ((tr.v r x 0 * B0579.pd 0 (mollR n ψ) x + tr.v r x 1 * B0579.pd 1 (mollR n ψ) x : ℝ) : ℂ) := by
    rw [integral_add hIK0 hIK1, hl 0, hl 1, ← neg_add, ← integral_add hV0 hV1]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by push_cast; ring)
  have hC : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), cellMoll n (χ r) x * (ψ x : ℂ) =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        φ r x * ((u' x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
          u' x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) := by
    rw [((hDual (ν ^ (-2 : ℝ)) m n hc ψ hψ).2.2 (χ r) hχp hχm).2]
    exact ((hChi r hrC).2.2 (mollR n ψ) u' hψ' hK).2
  have hI2 : IntegrableOn (fun x => (ν : ℂ) * (adjSpatial [0, 0] (cellMoll n (φ r)) x * (ψ x : ℂ) +
        adjSpatial [1, 1] (cellMoll n (φ r)) x * (ψ x : ℂ))) (B0579.cell (ν ^ (-2 : ℝ))) :=
    Integrable.const_mul (hI00.add hI11) (ν : ℂ)
  have hI3 : IntegrableOn (fun x =>
      pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ) +
        pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) := hIK0.add hIK1
  have hLHS : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), mollRate ν (tr.v r) n (φ r) (χ r) x * (ψ x : ℂ) =
      -((ν : ℂ) * (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          (adjSpatial [0, 0] (cellMoll n (φ r)) x * (ψ x : ℂ) +
            adjSpatial [1, 1] (cellMoll n (φ r)) x * (ψ x : ℂ))) +
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          (pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ) +
            pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ))) -
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), cellMoll n (χ r) x * (ψ x : ℂ))) := by
    have hI4 : IntegrableOn (fun x => (ν : ℂ) * (adjSpatial [0, 0] (cellMoll n (φ r)) x * (ψ x : ℂ) +
        adjSpatial [1, 1] (cellMoll n (φ r)) x * (ψ x : ℂ)) +
        (pdCx 0 (cellMoll n (fun y => ((tr.v r y 0 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ) +
          pdCx 1 (cellMoll n (fun y => ((tr.v r y 1 : ℝ) : ℂ) * φ r y)) x * (ψ x : ℂ)))
        (B0579.cell (ν ^ (-2 : ℝ))) := hI2.add hI3
    simp only [hsplit]
    rw [integral_neg, integral_sub hI4 hIC, integral_add hI2 hI3,
      integral_const_mul]
  rw [hLHS, hS ν tr t s g φ a b χ hctx r hr (mollR n ψ) u' hψ' hK, hF, hQ, hC]
  ring

end UnforcedLeray.Short.IIIa
