import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2.B.Jets
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStreamSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanStreamDeriv

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4/1/2/2`: `meanStreamGradJets`

Source `the November 2 reference manuscript`
397-404.  With `U = \bar v₁`, `G = \overline{v₁v₂}` (functions of `(s,q,η)`, horizontal averages of
the components of `v`, whose joint jets of order `≤ 3` are bounded by those of `v`:
`PO.hmean_jets`, `PO.JB.mul`), on `s > 0`
`fderiv Φ = (G - ν U_η) ds - U dη` for `Φ(s,q,η) = S(s,η)`
(`S_η = -\bar v₁`: `PartI.trainMeanV1`; `S_s = g - ν ∂_η \bar v₁`: `PartI.trainMeanStreamDeriv`),
so `D^{l}Φ` is a `D^{l-1}` of a combination of `G, U, ∂_ηU` and is bounded for `1 ≤ l ≤ 3`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartIIIb.Concrete.PO

theorem meanStreamGradJets : MeanStreamGradJets := by
  intro ν c hν hc tr hbuc C hC
  have hvs : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) DD :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl)
  have hvJB : JB 3 (fun x : ℝ × Plane => tr.v x.1 x.2) := ⟨hvs, C, hC⟩
  have hV : ∀ i : Fin 2, JB 3 (fun x : ℝ × Plane => tr.v x.1 x.2 i) := fun i =>
    hvJB.clm (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
  have hVU : JB 3 (fun x : ℝ × Plane => tr.v x.1 x.2 0) := hV 0
  have hVG : JB 3 (fun x : ℝ × Plane => tr.v x.1 x.2 0 * tr.v x.1 x.2 1) := (hV 0).mul (hV 1)
  -- horizontal averages
  set U : ℝ × Plane → ℝ := fun x => UnforcedLeray.Short.PartI.hmean c (fun z => tr.v x.1 z 0) x.2.2
    with hUdef
  set G : ℝ × Plane → ℝ := fun x =>
    UnforcedLeray.Short.PartI.hmean c (fun z => tr.v x.1 z 0 * tr.v x.1 z 1) x.2.2 with hGdef
  have hU : JB 3 U := by
    obtain ⟨K, hK⟩ := hVU.2
    obtain ⟨h1, h2⟩ := hmean_jets hc (fun s z => tr.v s z 0) 3 K hVU.1 hK
    exact ⟨h1, K, h2⟩
  have hG : JB 3 G := by
    obtain ⟨K, hK⟩ := hVG.2
    obtain ⟨h1, h2⟩ := hmean_jets hc (fun s z => tr.v s z 0 * tr.v s z 1) 3 K hVG.1 hK
    exact ⟨h1, K, h2⟩
  -- the coefficient functions
  set e : ℝ × Plane := (0, (0, 1)) with he
  set fstL : (ℝ × Plane) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ Plane with hfst
  set sndL : (ℝ × Plane) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane) with hsnd
  have hUη : JB 2 (fun y => fderiv ℝ U y e) :=
    (JB.fderiv (N := 2) hU).clm (ContinuousLinearMap.apply ℝ ℝ e)
  have hA : JB 2 (fun y => G y - ν • fderiv ℝ U y e) :=
    (hG.mono (by norm_num)).sub (hUη.const_smul ν)
  have hR : JB 2 (fun y => (ContinuousLinearMap.toSpanSingleton ℝ fstL)
        (G y - ν • fderiv ℝ U y e) - (ContinuousLinearMap.toSpanSingleton ℝ sndL) (U y)) :=
    (hA.clm (ContinuousLinearMap.toSpanSingleton ℝ fstL)).sub
      ((hU.mono (by norm_num)).clm (ContinuousLinearMap.toSpanSingleton ℝ sndL))
  obtain ⟨-, K, hK⟩ := hR
  refine ⟨K, fun l hl1 hl3 y hy => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  have hfd : ∀ y : ℝ × Plane, 0 < y.1 → fderiv ℝ (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y =
      (ContinuousLinearMap.toSpanSingleton ℝ fstL) (G y - ν • fderiv ℝ U y e) -
        (ContinuousLinearMap.toSpanSingleton ℝ sndL) (U y) := by
    intro y hy
    -- the derivative of `Φ`
    have hSsm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
        (Ioi 0 ×ˢ univ) := UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν c hν hc tr hbuc
    have hopen2 : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hSd : DifferentiableAt ℝ
        (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2) (y.1, y.2.2) :=
      (hSsm.contDiffAt (hopen2.mem_nhds (show ((y.1, y.2.2) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hy, mem_univ _⟩))).differentiableAt (by simp)
    have hUd : DifferentiableAt ℝ U y :=
      (contDiffAt_of_DD hU.1 hy).differentiableAt (by simp)
    have hPd : HasFDerivAt (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ))
        (fstL.prod sndL) y := (fstL.prod sndL).hasFDerivAt
    have hΦ := hSd.hasFDerivAt.comp y hPd
    -- partial derivatives of `S`
    have hs1 : fderiv ℝ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
        (y.1, y.2.2) (1, 0) = UnforcedLeray.Short.PartI.meanStress tr y.1 y.2.2 -
          ν * fderiv ℝ U y e := by
      have hline : HasDerivAt (fun r : ℝ => ((r, y.2.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) y.1 :=
        (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2.2)
      have h1 := (hSd.hasFDerivAt.comp_hasDerivAt y.1 hline).deriv
      have h2 := UnforcedLeray.Short.PartI.trainMeanStreamDeriv ν c hν hc tr hbuc y.1 hy y.2.2
      have hline2 : HasDerivAt (fun t : ℝ => ((y.1, (y.2.1, t)) : ℝ × Plane)) e y.2.2 :=
        (hasDerivAt_const y.2.2 y.1).prodMk ((hasDerivAt_const y.2.2 y.2.1).prodMk (hasDerivAt_id _))
      have h3 := (hUd.hasFDerivAt.comp_hasDerivAt y.2.2 hline2).deriv
      have h3' : deriv (fun t : ℝ => U (y.1, (y.2.1, t))) y.2.2 = deriv (fun t : ℝ =>
          UnforcedLeray.Short.PartI.hmean c (fun z => tr.v y.1 z 0) t) y.2.2 := rfl
      rw [← h1]
      show deriv (fun r => UnforcedLeray.Short.PartI.meanStream tr r y.2.2) y.1 = _
      rw [h2, ← h3, ← h3']
      rfl
    have hs2 : fderiv ℝ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
        (y.1, y.2.2) (0, 1) = - U y := by
      have hline : HasDerivAt (fun t : ℝ => ((y.1, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) y.2.2 :=
        (hasDerivAt_const y.2.2 y.1).prodMk (hasDerivAt_id _)
      have h1 := (hSd.hasFDerivAt.comp_hasDerivAt y.2.2 hline).deriv
      have h2 := UnforcedLeray.Short.PartI.trainMeanV1 ν c hν hc tr y.1 hy y.2.2
      rw [← h1]
      show deriv (fun t => UnforcedLeray.Short.PartI.meanStream tr y.1 t) y.2.2 = _
      have : U y = UnforcedLeray.Short.PartI.hmean c (fun z => tr.v y.1 z 0) y.2.2 := rfl
      rw [this, h2]; ring
    rw [show fderiv ℝ (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y = fderiv ℝ ((fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2) ∘ fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) y from rfl, hΦ.fderiv]
    refine ContinuousLinearMap.ext fun w => ?_
    have hw : ((w.1, w.2.2) : ℝ × ℝ) = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show (fstL w, sndL w) = ((w.1, w.2.2) : ℝ × ℝ) from rfl, hw, map_add, map_smul, map_smul,
      hs1, hs2]
    simp only [smul_eq_mul, hfst, hsnd, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp',
      ContinuousLinearMap.coe_snd', Function.comp_apply]
    show _ = _
    have hG' : G y = UnforcedLeray.Short.PartI.meanStress tr y.1 y.2.2 := rfl
    rw [hG']
    ring
  have hyD : y ∈ DD := ⟨hy, mem_univ _⟩
  have hev : fderiv ℝ (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2)
      =ᶠ[𝓝 y] (fun z => (ContinuousLinearMap.toSpanSingleton ℝ fstL)
        (G z - ν • fderiv ℝ U z e) - (ContinuousLinearMap.toSpanSingleton ℝ sndL) (U z)) := by
    filter_upwards [isOpen_DD.mem_nhds hyD] with z hz
    exact hfd z hz.1
  rw [← norm_iteratedFDeriv_fderiv, (Filter.EventuallyEq.iteratedFDeriv ℝ hev n).eq_of_nhds]
  exact hK n (by omega) y hy

end UnforcedLeray.Short.PartIIIb.Concrete
