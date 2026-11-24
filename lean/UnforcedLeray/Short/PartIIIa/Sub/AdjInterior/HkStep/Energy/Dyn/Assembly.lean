import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.Unique

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/1`: `MollRateDeriv m` from its leaves

Source of record: `the November 2 reference manuscript` lines 3060-3071, 3052-3058.
See `Dyn/Defs.lean` for the route.  The hypothesis `8 < m` is used only through `ChiCont`
(`adjLocalizedCoeff`), so `mollRateDeriv_of` takes it as an argument.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mollRateDeriv_of (m : ℝ) (hm : 8 < m) (hK : MollKerProps) (hJ : MollConvJet)
    (hR : MollRateJetAbs) (hV1 : VelMulMemX m) (hV2 : VelMulCont m) (hC : ChiCont m)
    (hDual : MollDual) (hBS : AdjE1.KernelBSExists) (hT1 : MollTestedAdj m)
    (hT2 : MollRateTested m) (hX : XDerivOfTested) (hU : XDerivUpgrade)
    (hE : EnergyDerivAbs) (hEc : EnergyContAbs) : MollRateDeriv m := by
  intro ν hν hν1 tr hTB t s ht hts g φ hφ hTD a b hta hab hbs χ hχ n j
  have ctx : MollCtx m ν tr t s g φ a b χ :=
    ⟨hν, hν1, hTB, ht, hts, hφ, hTD, hta, hab, hbs, hχ⟩
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hIcc : ∀ r ∈ Icc a b, r ∈ Icc t s := fun r hr => ⟨hta.trans hr.1, hr.2.trans hbs.le⟩
  have hIco : ∀ r ∈ Icc a b, r ∈ Ico t s := fun r hr => ⟨hta.trans hr.1, hr.2.trans_lt hbs⟩
  have hIoo : ∀ r ∈ Ioo a b, r ∈ Icc a b := fun r hr => ⟨hr.1.le, hr.2.le⟩
  -- the families
  have hφX : XFam (ν ^ (-2 : ℝ)) m a b φ :=
    ⟨fun r hr => ⟨hφ.periodic r (hIco r (hIoo r hr)), hφ.memX r (hIcc r (hIoo r hr))⟩,
      fun r hr => (hφ.strongCont r (hIcc r (hIoo r hr))).mono_left
        (nhdsWithin_mono _ (fun x hx => hIcc x (hIoo x hx)))⟩
  have hVX : ∀ l : Fin 2, XFam (ν ^ (-2 : ℝ)) m a b
      (fun r y => ((tr.v r y l : ℝ) : ℂ) * φ r y) :=
    fun l => ⟨fun r hr => hV1 ν tr t s g φ a b χ ctx r hr l, fun r hr => hV2 ν tr t s g φ a b χ ctx r hr l⟩
  have hχX : XFam (ν ^ (-2 : ℝ)) m a b χ :=
    ⟨fun r hr => ⟨(hχ r (hIoo r hr)).1, (hχ r (hIoo r hr)).2.1⟩,
      hC hm ν tr t s g φ a b χ ctx⟩
  obtain ⟨hKs, hKc, hKb⟩ := hK n
  have hFjet : AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b) (fun r => cellMoll n (φ r))
      (fun r w => adjSpatial w (cellMoll n (φ r))) :=
    hJ _ m (molKer n) φ a b hc hKs hKc hKb hφX
  have hRjet : AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b)
      (fun r => mollRate ν (tr.v r) n (φ r) (χ r))
      (fun r w => adjSpatial w (mollRate ν (tr.v r) n (φ r) (χ r))) :=
    hR _ m ν n a b φ χ (fun l r y => ((tr.v r y l : ℝ) : ℂ) * φ r y) hc hφX hVX hχX
  have hmemF : ∀ r ∈ Ioo a b, ∀ w : List (Fin 2),
      MemLp (adjSpatial w (cellMoll n (φ r))) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun r hr w => (hFjet.1 r hr w.length).memX w le_rfl
  have hmemR : ∀ r ∈ Ioo a b, ∀ w : List (Fin 2),
      MemLp (adjSpatial w (mollRate ν (tr.v r) n (φ r) (χ r))) 2
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun r hr w => (hRjet.1 r hr w.length).memX w le_rfl
  -- tested derivative
  have htest : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → ∀ r ∈ Ioo a b,
      HasDerivAt (fun r' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), cellMoll n (φ r') x * (ψ x : ℂ))
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          mollRate ν (tr.v r) n (φ r) (χ r) x * (ψ x : ℂ)) r := by
    intro ψ hψ r hr
    obtain ⟨hψ', -, -⟩ := hDual _ m n hc ψ hψ
    obtain ⟨u', hu'⟩ := hBS _ (mollR n ψ) hc hψ'
    have h1 := hT1 ν tr t s g φ a b χ ctx n ψ hψ u' hu' r hr
    have h2 := hT2 ν tr t s g φ a b χ ctx n ψ hψ u' hu' r hr
    rw [h2]
    exact h1
  have hHas : HasXDerivOn (ν ^ (-2 : ℝ)) m (Ioo a b) (fun r => cellMoll n (φ r))
      (fun r => mollRate ν (tr.v r) n (φ r) (χ r)) :=
    hX _ m a b _ _ hc (fun r hr => hmemF r hr [])
      (fun r hr => hmemR r hr []) (fun r hr => hRjet.2 [] r hr) htest
  have hHasW := hU _ m a b _ _ _ _ hc hFjet hRjet hHas
  refine ⟨hEc _ m j n a b φ hc
    (fun r hr => ⟨hφ.periodic r (hIco r hr), hφ.memX r (hIcc r hr)⟩)
    (fun r hr => (hφ.strongCont r (hIcc r hr)).mono_left
      (nhdsWithin_mono _ (fun x hx => hIcc x hx))), fun r hr => ?_⟩
  exact hE _ m j _ _ a b hc (fun r hr w => ⟨hmemF r hr w, hmemR r hr w⟩) hHasW r hr

end UnforcedLeray.Short.IIIa
