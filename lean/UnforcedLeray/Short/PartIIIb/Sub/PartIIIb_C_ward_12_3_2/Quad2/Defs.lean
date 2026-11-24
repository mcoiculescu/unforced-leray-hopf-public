import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.HessEqSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQIbp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEGradL2p

/-!
# `GEQuad2` definitions and top-level reduction (`PartIII-b:C/ward/12/3/2/2/4`)

Source `the November 2 reference manuscript`,
lines 2552-2559, 2525-2533, 1515-1531, 2381-2387.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep phaseInt)

/-- `D_mD_lD_j u` pointwise: classical third derivative `∂_m∂_l∂_j` of the affine inlet
`e = p.eFun (p.coord z)` plus the representative of the weak third derivative `t j l m` of `w`
(`∂_m` of `k j l = ∂_l g_j`, source 2552-2559, 2381-2387). -/
def GEQD3u (p : Params) (z : p.Z)
    (t : Fin 3 → Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j l m : Fin 3)
    (x : ℝ × UnforcedLeray.Space) : UnforcedLeray.PhaseSpace.CVec3 :=
  dy m (dy l (dy j (p.eFun (p.coord z)))) x + rep (t j l m) x.1 x.2

/-- The pointwise order-2 quadratic field `-∂_j(GEQuadField p z g k l)` expanded by the product
rule (source 2552-2559): each term is a product of an order-`≤ 1` factor (`uOf z` or `GEQDu`) and
an order-`2` or order-`3` factor (`GEQDdu` or `GEQD3u`). -/
def GEQuadField2 (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (k : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (t : Fin 3 → Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j l : Fin 3)
    (x : ℝ × UnforcedLeray.Space) : UnforcedLeray.PhaseSpace.CVec3 :=
  WithLp.toLp 2 fun i => ∑ m : Fin 3,
    (GEQD3u p z t m l j x m * p.uOf z x i + GEQDdu p z g k m l x m * GEQDu p z g j x i +
      GEQDdu p z g k m j x m * GEQDu p z g l x i + GEQDu p z g m x m * GEQDdu p z g k l j x i +
      GEQDdu p z g k l j x m * GEQDu p z g m x i + GEQDu p z g l x m * GEQDdu p z g k m j x i +
      GEQDu p z g j x m * GEQDdu p z g k m l x i + p.uOf z x m * GEQD3u p z t m l j x i)

/-- Standing hypotheses of `GEQuad2` at a parameter point: `g_j ∈ D_p`, weak Hessian `k`, and weak
third derivatives `t` in `Y_{q₀}` (source 2552-2559). -/
def GEQHyp2 (p : Params) (_z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (k : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (t : Fin 3 → Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) : Prop :=
  (∀ j : Fin 3, g j ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E) ∧
  (∀ j l : Fin 3, HasPhaseOp (fun Φ => -dy l Φ) (g j) (k j l)) ∧
  (∀ j l m : Fin 3, HasPhaseOp (fun Φ => -dy m Φ) (k j l) (t j l m))

/-- **Single-derivative integration by parts from `GEQuadField` to `GEQuadField2`**
(source 2552-2559): integrating `∂_j` by parts against `GEQuadField p z g k l` produces
`GEQuadField2 p z g k t j l`. -/
def GEQIbp2Step : Prop := GERegime fun p z g => ∀ k t, GEQHyp2 p z g k t →
  ∀ (j l : Fin 3) (Φ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3),
    IsPhaseTest p.period Φ →
    pairF p.period (dy j Φ) (GEQuadField p z g k l) =
      pairF p.period Φ (GEQuadField2 p z g k t j l)

/-- **Order-2 weak integration by parts for the quadratic term** (source 2552-2559, order-2
analogue of `GEQIbp`, `GEQuadSub/Defs.lean:120`): for every phase test `Φ`,
`⟪(u·∇)∂_l∂_jΦ, u⟫ = -⟪Φ, GEQuadField2 p z g k t j l⟫`. -/
def GEQIbp2 : Prop := GERegime fun p z g => ∀ k t, GEQHyp2 p z g k t →
  ∀ (j l : Fin 3) (Φ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3),
    IsPhaseTest p.period Φ →
    pairF p.period (advT (p.uOf z) (dy l (dy j Φ))) (p.uOf z) =
      -pairF p.period Φ (GEQuadField2 p z g k t j l)

/-- **Order-2 quadratic field in `Y_{q₀}`** (source 2552-2559, 1515-1531, 2381-2387, order-2
analogue of `GEQYq`, `GEQuadSub/Defs.lean:129`). -/
def GEQYq2 : Prop := GERegime fun p z g => ∀ k t, GEQHyp2 p z g k t →
  ∀ j l : Fin 3, ∃ F : Yq p.period UnforcedLeray.B0412.q0E,
    ∀ Φ, IsPhaseTest p.period Φ →
      phasePair p.period UnforcedLeray.B0412.q0E Φ F =
        pairF p.period Φ (GEQuadField2 p z g k t j l)

/-- `GEQIbp2` from the already-proved first-order `gEQIbp` and `gEGradL2p` plus the single
additional integration by parts `GEQIbp2Step`. -/
theorem gEQIbp2_of_step (hStep : GEQIbp2Step) : GEQIbp2 := by
  intro lam q hq dm dp hdm
  obtain ⟨n1, hn1, H1⟩ := gEQIbp lam q hq dm dp hdm
  obtain ⟨n2, hn2, H2⟩ := gEGradL2p lam q hq dm dp hdm
  obtain ⟨n3, hn3, H3⟩ := hStep lam q hq dm dp hdm
  refine ⟨min n1 (min n2 n3), lt_min hn1 (lt_min hn2 hn3), ?_⟩
  intro p d hreg hν hmode z g hd k t hyp j l Φ hΦ
  have e1 : p.ν ≤ n1 := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ n2 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : p.ν ≤ n3 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hyp1 : GEQHyp p z g k := ⟨hyp.2.1, H2 p d hreg e2 hmode z g hd⟩
  rw [H1 p d hreg e1 hmode z g hd k hyp1 l (dy j Φ) (hΦ.dy j),
    H3 p d hreg e3 hmode z g hd k t hyp j l Φ hΦ]

/-- `GEQuad2` from `GEQIbp2` and `GEQYq2` (order-2 analogue of `gEQuad_of`). -/
theorem gEQuad2_of (h1 : GEQIbp2) (h2 : GEQYq2) : GEQuad2 := by
  intro lam q hq dm dp hdm
  obtain ⟨n1, hn1, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨n2, hn2, H2⟩ := h2 lam q hq dm dp hdm
  refine ⟨min n1 n2, lt_min hn1 hn2, ?_⟩
  intro p d hreg hν hmode z g hd hgD k t hk ht gQ hQ j l
  have e1 : p.ν ≤ n1 := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ n2 := hν.trans (min_le_right _ _)
  have hyp : GEQHyp2 p z g k t := ⟨hgD, hk, ht⟩
  obtain ⟨F, hF⟩ := H2 p d hreg e2 hmode z g hd k t hyp j l
  refine ⟨F, fun Φ hΦ => ?_⟩
  have hΨ : IsSolTest p.period (dy l (dy j Φ)) := gEW_isSolTest_dy (gEW_isSolTest_dy hΦ j) l
  rw [hQ (dy l (dy j Φ)) hΨ, hF Φ hΦ.1,
    H1 p d hreg e1 hmode z g hd k t hyp j l Φ hΦ.1, neg_neg]

end UnforcedLeray.Short.PartIIIb.Concrete
