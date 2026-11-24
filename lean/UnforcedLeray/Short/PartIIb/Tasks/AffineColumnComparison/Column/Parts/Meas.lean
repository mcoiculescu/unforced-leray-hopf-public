import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.SmoothVanish

/-!
# Part II-b, task `PartII-b:G4/3/7/3` (`ColAEMeas`)

Source of record: `the November 2 reference manuscript`, lines 2347-2348, 2370-2374.
The column `colEps p i` is continuous on the open set `U = {s > 0}` (inlet profile `C^∞`, train
velocity and stream `C^∞` on `s > 0`, so the raw profile `rawProf` is `C^∞` on `U`), and it vanishes
on `s ≤ 0`. Hence it is a.e. strongly measurable for any measure supported in `U`-closure
(`hMeas` is an arbitrary measure here: `indicator` over `U`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

private abbrev colAU : Set Coord := {x : Coord | 0 < x.1}

private theorem colAU_open : IsOpen colAU := isOpen_lt continuous_const continuous_fst

/-- Chart derivatives of a `C^∞` function on an open set are `C^∞` there. -/
private theorem colA_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Coord → E} {U : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (v : Coord) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ G x v) U :=
  (hG.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const

private theorem colA_dS {G : Coord → Axi.Merid} {U : Set Coord} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) : ContDiffOn ℝ ∞ (Axi.dS G) U :=
  colA_fderiv_apply hU hG (1, (0, 0))

private theorem colA_dQ {G : Coord → Axi.Merid} {U : Set Coord} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) : ContDiffOn ℝ ∞ (Axi.dQ G) U :=
  colA_fderiv_apply hU hG (0, (1, 0))

private theorem colA_dEta {G : Coord → Axi.Merid} {U : Set Coord} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) : ContDiffOn ℝ ∞ (Axi.dEta G) U :=
  colA_fderiv_apply hU hG (0, (0, 1))

private theorem colA_kAge {G : Coord → Axi.Merid} {U : Set Coord} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) : ContDiffOn ℝ ∞ (kAge G) U := by
  have h1 : ContDiffOn ℝ ∞ (fun x : Coord => 2 * x.1) U :=
    (contDiff_const.mul contDiff_fst).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun x : Coord => x.2.2) U :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  unfold kAge
  exact (h1.smul (colA_dS hU hG)).add (h2.smul (colA_dEta hU hG))

private theorem colA_coord {G : Coord → Axi.Merid} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (j : Fin 2) : ContDiffOn ℝ ∞ (fun x => G x j) U :=
  (EuclideanSpace.proj j : Axi.Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hG

private theorem colA_qEps {ε : ℝ} {F : Coord → Axi.Merid} {U : Set Coord} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiffOn ℝ ∞ (qEps ε F) U := by
  unfold qEps
  exact (colA_dQ hU hF).sub ((contDiffOn_const (c := ε)).smul ((colA_kAge hU hF).add hF))

set_option maxHeartbeats 800000 in
private theorem colA_vecDiffEps {ε : ℝ} {F : Coord → Axi.Merid} {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) : ContDiffOn ℝ ∞ (vecDiffEps ε F) U := by
  have hdQ := colA_dQ hU hF
  have hdE := colA_dEta hU hF
  have hdQQ := colA_dQ hU hdQ
  have hdEE := colA_dEta hU hdE
  have hk1 := colA_kAge hU hdQ
  have hsum : ContDiffOn ℝ ∞ (fun x => kAge F x + F x) U := (colA_kAge hU hF).add hF
  have hk2 := colA_kAge hU hsum
  have hhoop : ContDiffOn ℝ ∞ (fun x => hoopR (F x)) U :=
    (colA_coord hF 0).smul contDiffOn_const
  unfold vecDiffEps
  exact (((hdQQ.add hdEE).sub ((contDiffOn_const (c := 2 * ε)).smul (hk1.add hdQ))).add
    ((contDiffOn_const (c := ε ^ 2)).smul ((hk2.add hsum).sub hhoop)))

private theorem colA_bEps (p : Params) {F : Coord → Axi.Merid} {U : Set Coord} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hR : ContDiffOn ℝ ∞ (rawProf p) U) :
    ContDiffOn ℝ ∞ (bEps p F) U := by
  unfold bEps
  exact (((colA_coord hR 0).smul (colA_qEps hU hF)).add ((colA_coord hR 1).smul (colA_dEta hU hF))).add
    (((colA_coord hF 0).smul (colA_qEps hU hR)).add ((colA_coord hF 1).smul (colA_dEta hU hR)))

private theorem colA_colDiffR (p : Params) (i : Fin 2) {U : Set Coord} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ (p.inletProfile i) U) : ContDiffOn ℝ ∞ (colDiffR p i) U := by
  unfold colDiffR
  exact (contDiff_fst.contDiffOn.smul ((colA_dS hU hF).sub
    ((contDiffOn_const (c := p.ν)).smul (colA_vecDiffEps hU hF))))

private theorem colA_colIntR (p : Params) (i : Fin 2) {U : Set Coord} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ (p.inletProfile i) U) (hR : ContDiffOn ℝ ∞ (rawProf p) U) :
    ContDiffOn ℝ ∞ (colIntR p i) U := by
  unfold colIntR
  exact contDiff_fst.contDiffOn.smul (colA_bEps p hU hF hR)

/-- Chain rule for the `η`-derivative of a function on the chart. -/
private theorem colA_deriv_eta (Ψ : Coord → ℝ) (x : Coord) (hΨ : DifferentiableAt ℝ Ψ x) :
    deriv (fun t => Ψ (x.1, (x.2.1, t))) x.2.2 = fderiv ℝ Ψ x (0, (0, 1)) := by
  have hline : HasDerivAt (fun t : ℝ => ((x.1, (x.2.1, t)) : Coord)) (0, (0, 1)) x.2.2 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  exact (hΨ.hasFDerivAt.comp_hasDerivAt x.2.2 hline).deriv

/-- Chain rule for the `s`-derivative of a function on the chart. -/
private theorem colA_deriv_s (Ψ : Coord → ℝ) (x : Coord) (hΨ : DifferentiableAt ℝ Ψ x) :
    deriv (fun t => Ψ (t, (x.2.1, x.2.2))) x.1 = fderiv ℝ Ψ x (1, (0, 0)) := by
  have hline : HasDerivAt (fun t : ℝ => ((t, (x.2.1, x.2.2)) : Coord)) (1, (0, 0)) x.1 :=
    (hasDerivAt_id _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
  exact (hΨ.hasFDerivAt.comp_hasDerivAt x.1 hline).deriv

/-- The raw profile is `C^∞` on `s > 0` (train velocity from `IsTrain.smooth_v`, stream from
`BgRegime.train_stream_smooth`, the raised stream through the chart derivatives). -/
private theorem colA_rawProf_cd (p : Params)
    (hψ : ContDiffOn ℝ ∞ (fun x : ℝ × Cyl.Plane => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ContDiffOn ℝ ∞ (rawProf p) colAU := by
  have hU := colAU_open
  have hsub : colAU ⊆ Ioi 0 ×ˢ univ := fun x hx => ⟨hx, trivial⟩
  have hv : ContDiffOn ℝ ∞ (fun x : Coord => p.train.v x.1 x.2) colAU :=
    p.train.isTrain.smooth_v.mono (fun x (hx : 0 < x.1) => ⟨le_of_lt hx, trivial⟩)
  have hΨ : ContDiffOn ℝ ∞ (fun x : Coord => p.train.ψ x.1 x.2) colAU := hψ.mono hsub
  have hΨd : ∀ x ∈ colAU, DifferentiableAt ℝ (fun x : Coord => p.train.ψ x.1 x.2) x :=
    fun x hx => (hΨ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hD1 : ContDiffOn ℝ ∞
      (fun x : Coord => deriv (fun t => p.train.ψ x.1 (x.2.1, t)) x.2.2) colAU := by
    refine (colA_fderiv_apply hU hΨ (0, (0, 1))).congr (fun x hx => ?_)
    exact colA_deriv_eta (fun x : Coord => p.train.ψ x.1 x.2) x (hΨd x hx)
  have hD2 : ContDiffOn ℝ ∞
      (fun x : Coord => deriv (fun t => p.train.ψ t (x.2.1, x.2.2)) x.1) colAU := by
    refine (colA_fderiv_apply hU hΨ (1, (0, 0))).congr (fun x hx => ?_)
    exact colA_deriv_s (fun x : Coord => p.train.ψ x.1 x.2) x (hΨd x hx)
  have hη : ContDiffOn ℝ ∞ (fun x : Coord => x.2.2) colAU :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hs2 : ContDiffOn ℝ ∞ (fun x : Coord => 2 * x.1) colAU :=
    (contDiff_const.mul contDiff_fst).contDiffOn
  have hRS : ContDiffOn ℝ ∞
      (fun x : Coord => UnforcedLeray.Cons.C03.raisedStream p.train.ψ x.1 x.2.1 x.2.2) colAU := by
    unfold UnforcedLeray.Cons.C03.raisedStream
    exact hΨ.sub (hη.mul hD1 |>.add (hs2.mul hD2)) |>.congr (fun _ _ => rfl)
  have hv' : ContDiffOn ℝ ∞ (fun x : Coord => UnforcedLeray.Cons.C03.rawProfile p.ε
      p.train.v p.train.ψ x) colAU := by
    unfold UnforcedLeray.Cons.C03.rawProfile
    exact hv.add (((contDiffOn_const (c := p.ε)).mul hRS).smul
      (contDiffOn_const (c := EuclideanSpace.single (1 : Fin 2) (1 : ℝ))))
  exact hv'

/-- The continuity-level form of the column: on `U = {s > 0}`, `colEpsR` is `C^∞`. -/
private theorem colA_colEpsR_cd (p : Params) (i : Fin 2)
    (hF : ContDiffOn ℝ ∞ (p.inletProfile i) colAU)
    (hR : ContDiffOn ℝ ∞ (rawProf p) colAU) :
    ContDiffOn ℝ ∞ (fun x => colDiffR p i x + colIntR p i x) colAU :=
  (colA_colDiffR p i colAU_open hF).add (colA_colIntR p i colAU_open hF hR)

/-- The complex embedding of a real meridional vector is continuous. -/
private theorem colA_cplx_continuous :
    Continuous (fun v : Axi.Merid => (WithLp.toLp 2 (fun j => ((v j : ℝ) : ℂ)) : CMerid)) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
    (continuous_pi fun j => Complex.continuous_ofReal.comp (EuclideanSpace.proj j).continuous)

/-- **`ColAEMeas`** (SP 2347-2348, 2370-2374). -/
theorem colAEMeas : UnforcedLeray.Short.IIb.ColAEMeas := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₀, hν₀, HV⟩ := inletProfileSmoothVanish Sig lam q hSig hq dm dp hdm
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg i
  obtain ⟨h1, h2, h3, h4⟩ := hreg
  obtain ⟨hC, -⟩ := HV p d h1 h2 h3 h4 i
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × Cyl.Plane => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    h1.train_stream_smooth
  have hF : ContDiffOn ℝ ∞ (p.inletProfile i) colAU := hC.contDiffOn.mono (subset_univ _)
  have hR := colA_rawProf_cd p hψ
  have hcd := colA_colEpsR_cd p i hF hR
  have hcont : ContinuousOn (colEpsR p i) colAU := by
    refine hcd.continuousOn.congr (fun x hx => ?_)
    have hx' : 0 < x.1 := hx
    simp [colEpsR, hx']
  have hcontE : ContinuousOn (colEps p i) colAU :=
    colA_cplx_continuous.comp_continuousOn hcont
  have hind : colEps p i = colAU.indicator (colEps p i) := by
    funext x
    by_cases hx : x ∈ colAU
    · rw [Set.indicator_of_mem hx]
    · have hx' : ¬ (0 < x.1) := hx
      rw [Set.indicator_of_notMem hx]
      ext j
      simp [colEps, cplx, colEpsR, hx']
  have key : AEStronglyMeasurable (colAU.indicator (colEps p i)) (hMeas p.c bgp) :=
    (aestronglyMeasurable_indicator_iff colAU_open.measurableSet).mpr
      (hcontE.aestronglyMeasurable colAU_open.measurableSet)
  rw [← hind] at key
  exact key

end UnforcedLeray.Short.IIb
