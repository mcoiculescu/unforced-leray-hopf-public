import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.B0Expand
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.ChartRuleGen
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.DiffHat
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.DiffParts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.DiffRaw
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.DivZero
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.PerExtHat
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.ProfileEqs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvTasks.RawEv

/-!
# `convChartEq`: the exact chart identity `geoConvPiece = ε s · G`
# (`PartIII-b:C/asrc/ra/9/2/2/10`, source 5034-5044)

Source of record: `the November 2 reference manuscript` (73 pages), lines 5034-5044
(chart rules and the solenoidal completion), 2075-2077 (`U_raw`, `H`), 4980 (`ĥ_A`).

Proof outline.  At a chart point `(s, x)` with `s > 0`:
1. `coefOf` reads its profile at one point `(chartTau, chartY)` with `chartY 0 = R/√s ≠ 0`.
   Near that point the physical fields `p.raw τ` and `hLift τ` agree with the ring lifts
   `Nv ε⁻¹ rawProfile` and `Nv ε⁻¹ hAcoef` (`convRawEv`, `convPerExtHat`), so `physDivSym` agrees.
2. `convChartRuleGen` turns the chart coefficient into `s • toMer (cBil ε rawPl hatPl)`.
3. `cB0` depends only on the slices at `s`, and `rawPl = trPl + ε trHe`, `hatPl = hpPl + ε kEz`
   (`convProfileEqs`); `convB0Expand` gives the bilinear expansion, and `convDivZero` kills the
   divergence terms, leaving `cBil = (cAdv tr hp + cAdv hp tr) + ε • convG`.
4. Subtracting the planar term leaves `(ε s) • toMer (convG)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- `physDivSym` depends only on the two fields near the point. -/
theorem physDivSym_congr_nhds {a a' b b' : Space → Space} {y : Space}
    (ha : a =ᶠ[nhds y] a') (hb : b =ᶠ[nhds y] b') :
    physDivSym a b y = physDivSym a' b' y := by
  unfold physDivSym
  congr 1
  funext i
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hf : (fun z => a z j * b z i + b z j * a z i) =ᶠ[nhds y]
      (fun z => a' z j * b' z i + b' z j * a' z i) := by
    filter_upwards [ha, hb] with z hz1 hz2
    simp only [hz1, hz2]
  rw [hf.fderiv_eq]

/-- `cB0` depends on the profiles only through their slices at `s`. -/
theorem cB0_slice (F F' G G' : ℝ → ℝ × ℝ → ℝ × ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hF : F s = F' s) (hG : G s = G' s) : cB0 F G s x = cB0 F' G' s x := by
  unfold cB0 cAdv cDiv
  rw [hF, hG]

/-- **The exact chart identity** (source 5034-5044, 2075-2077, 4980): for `s > 0`,
`geoConvPiece = ε s · G`. -/
theorem convChartEq (as : ℝ) (χf : ℝ → ℝ) : ConvChartEq as χf := by
  intro hχ dm dp hdm
  refine ⟨1, one_pos, fun p d hreg _hν μ A hA s hs x => ?_⟩
  have hR : p.ε⁻¹ ≠ 0 := inv_ne_zero p.ε_pos.ne'
  have hRpos : 0 < p.ε⁻¹ := inv_pos.2 p.ε_pos
  have hc : p.c = cOf p.ν := hreg.c_eq
  have hDR : DifferentiableAt ℝ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) (s, x) :=
    convDiffRaw dm dp hdm p d hreg s hs x
  have hDH : DifferentiableAt ℝ (hAcoef p.ν p.ε χf A) (s, x) :=
    convDiffHat as χf hχ p.ν p.ε p.ν_pos p.ε_pos A hA s hs x
  obtain ⟨hT, hHe, hHp, hKe⟩ := convDiffParts as χf hχ dm dp hdm p d hreg A hA s hs x
  obtain ⟨hdz1, hdz2⟩ := convDivZero as χf hχ p A hA s hs x
  have hPE := fun y => convProfileEqs as χf p A s hs y
  -- the chart point is off the axis
  have hy0 : (NearInst.chartY p.ε⁻¹ (s, x)) 0 ≠ 0 := by
    have h0 : (NearInst.chartY p.ε⁻¹ (s, x)) 0 = p.ε⁻¹ / Real.sqrt s := by
      simp [NearInst.chartY]
    rw [h0]
    exact div_ne_zero hR (Real.sqrt_ne_zero'.2 hs)
  -- pointwise replacement of the fields near an off-axis point
  have hc0 : Continuous (fun z : Space => z 0) := by fun_prop
  have key : ∀ (τ : ℝ) (y : Space), y 0 ≠ 0 →
      physDivSym (p.raw τ) (hLift p.ν p.ε p.c χf A τ) y =
        physDivSym (fun y' => UnforcedLeray.Axi.Nv p.ε⁻¹
            (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ y')
          (fun y' => UnforcedLeray.Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ y') y := by
    intro τ y hy0
    have hy : y ∉ UnforcedLeray.Axi.axis := fun h => hy0 h.1
    have hev : ∀ᶠ z in nhds y, z 0 ≠ 0 := hc0.continuousAt.eventually_ne hy0
    have ha := convRawEv p τ y hy
    have hb : hLift p.ν p.ε p.c χf A τ =ᶠ[nhds y]
        UnforcedLeray.Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ := by
      filter_upwards [hev] with z hz
      have hzA : z ∉ UnforcedLeray.Axi.axis := fun h => hz h.1
      have hpos : 0 < UnforcedLeray.Axi.age p.ε⁻¹ z := UnforcedLeray.Axi.age_pos hR hzA
      have hper : UnforcedLeray.Axi.perExt (cOf p.ν) (hAcoef p.ν p.ε χf A)
          (UnforcedLeray.Axi.chart p.ε⁻¹ τ z) =
            hAcoef p.ν p.ε χf A (UnforcedLeray.Axi.chart p.ε⁻¹ τ z) :=
        convPerExtHat as χf hχ p.ν p.ε p.ν_pos p.ε_pos A hA _ hpos _
      simp only [hLift, UnforcedLeray.Axi.Nv, hc]
      rw [hper]
    exact physDivSym_congr_nhds ha hb
  -- the coefficient only sees the field at one point
  have hcoefEq : ∀ (F G : ℝ → Space → Space),
      F (NearInst.chartTau p.ε⁻¹ (s, x)) (NearInst.chartY p.ε⁻¹ (s, x)) =
        G (NearInst.chartTau p.ε⁻¹ (s, x)) (NearInst.chartY p.ε⁻¹ (s, x)) →
      coefOf p.ε⁻¹ F (s, x) = coefOf p.ε⁻¹ G (s, x) := by
    intro F G h
    unfold coefOf
    rw [h]
  have hcoef : coefOf p.ε⁻¹ (fun τ y => physDivSym (p.raw τ) (hLift p.ν p.ε p.c χf A τ) y) (s, x) =
      coefOf p.ε⁻¹ (fun τ y => physDivSym
        (fun y' => UnforcedLeray.Axi.Nv p.ε⁻¹
          (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ y')
        (fun y' => UnforcedLeray.Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ y') y) (s, x) :=
    hcoefEq _ _ (key _ _ hy0)
  -- the chart rule
  have hCR := convChartRuleGen p.ε⁻¹ hRpos
    (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) (hAcoef p.ν p.ε χf A) (s, x) hs
    hDR hDH
  rw [inv_inv] at hCR
  have hCR' : coefOf p.ε⁻¹ (fun τ y => physDivSym
        (fun y' => UnforcedLeray.Axi.Nv p.ε⁻¹
          (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ y')
        (fun y' => UnforcedLeray.Axi.Nv p.ε⁻¹ (hAcoef p.ν p.ε χf A) τ y') y) (s, x) =
      s • toMer (cBil p.ε (rawPl p) (hatPl p χf A) s x) := hCR
  -- the geometric piece
  have hgeo : geoConvPiece p μ χf A (s, x) =
      s • toMer (cBil p.ε (rawPl p) (hatPl p χf A) s x) -
        s • toMer (fderiv ℝ (hpA p.ν χf A s) x (trainPl p.train s x) +
          fderiv ℝ (trainPl p.train s) x (hpA p.ν χf A s x)) := by
    show coefOf p.ε⁻¹ (fun τ y => physDivSym (p.raw τ) (hLift p.ν p.ε p.c χf A τ) y) (s, x) -
        s • toMer (fderiv ℝ (hpA p.ν χf A s) x (trainPl p.train s x) +
          fderiv ℝ (trainPl p.train s) x (hpA p.ν χf A s x)) = _
    rw [hcoef, hCR']
  -- the bilinear expansion of the chart form
  have hV : cBil p.ε (rawPl p) (hatPl p χf A) s x =
      cAdv (trPl p) (hpPl p χf A) s x + cAdv (hpPl p χf A) (trPl p) s x +
        p.ε • convG p χf A s x := by
    have hF : rawPl p s = fun y => trPl p s y + p.ε • trHe p s y := by
      funext y
      exact (hPE y).1
    have hG : hatPl p χf A s = fun y => hpPl p χf A s y + p.ε • kEz p χf A s y := by
      funext y
      exact (hPE y).2
    have e0 : cB0 (rawPl p) (hatPl p χf A) s x =
        cB0 (trPl p) (hpPl p χf A) s x +
          p.ε • (cB0 (trHe p) (hpPl p χf A) s x + cB0 (trPl p) (kEz p χf A) s x) +
          p.ε ^ 2 • cB0 (trHe p) (kEz p χf A) s x := by
      rw [cB0_slice (rawPl p) (fun s' y => trPl p s' y + p.ε • trHe p s' y) (hatPl p χf A)
        (fun s' y => hpPl p χf A s' y + p.ε • kEz p χf A s' y) s x hF hG]
      exact convB0Expand (trPl p) (trHe p) (hpPl p χf A) (kEz p χf A) p.ε s x hT hHe hHp hKe
    have hDz : cB0 (trPl p) (hpPl p χf A) s x =
        cAdv (trPl p) (hpPl p χf A) s x + cAdv (hpPl p χf A) (trPl p) s x := by
      simp only [cB0, hdz1, hdz2, zero_smul, add_zero]
    have hcB1 : cBil p.ε (rawPl p) (hatPl p χf A) s x =
        cB0 (rawPl p) (hatPl p χf A) s x + p.ε • cB1 (rawPl p) (hatPl p χf A) s x := rfl
    rw [hcB1, e0, hDz]
    unfold convG
    module
  have hY : fderiv ℝ (hpA p.ν χf A s) x (trainPl p.train s x) +
      fderiv ℝ (trainPl p.train s) x (hpA p.ν χf A s x) =
        cAdv (trPl p) (hpPl p χf A) s x + cAdv (hpPl p χf A) (trPl p) s x := rfl
  have hfin : ∀ (Y G' : ℝ × ℝ), s • toMer (Y + p.ε • G') - s • toMer Y = (p.ε * s) • toMer G' := by
    intro Y G'
    rw [toMer_add, toMer_smul, smul_add, smul_smul, mul_comm s p.ε]
    abel
  rw [hgeo, hV, hY]
  exact hfin _ _

end UnforcedLeray.Short.PartIIIb.Concrete
