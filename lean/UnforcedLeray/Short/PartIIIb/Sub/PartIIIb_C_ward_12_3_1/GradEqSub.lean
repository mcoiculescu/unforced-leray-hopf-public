import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1

/-!
# Decomposition of `BgCorrGradEq` (source 2525-2551, 2555-2570)

Task `PartIII-b:C/ward/12/3/1/2/org`.  Source of record
`the November 2 reference manuscript`.

The differentiated equation `A₀D_jw = f_j + ½D_jw` is obtained in four steps:

* `GEWeak` (a): testing the projected equation `gF + gL + gQ = 0` with the solenoidal test
  `∂_jΦ` and using `∂_j L₀ᵗ = L₀ᵗ∂_j + ½∂_j` (so the commutator `[∂_j, y·∇] = ∂_j` produces the
  `½D_jw`) gives an exact formula for `⟨L₀ᵗΦ, D_jw⟩` on solenoidal tests (2533-2537).
* `GERaw`, `GEInlet`, `GELin`, `GEQuad` (b), (c): every term of that formula is `⟨Φ, F⟩` with
  `F ∈ Y_p` (2531-2533, 2542-2551), from `D²w ∈ Y_p` (`GEHess`, 1415-1424 / 2531), `w ∈ L^∞`
  (1515-1531) and `Dw ∈ Y_{2p}` (`GEGradL2p`, 2531).
* `GELift`: the equation on solenoidal tests lifts to all phase tests (maximal domain with
  uniqueness among solenoidal solutions, 1358-1359, 1393-1400).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep)

/-- The standing data: `z` solves the projected equation and `g` is the distributional gradient
of `w = wOf z` (source 2525-2537). -/
def GEData (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) : Prop :=
  UnforcedLeray.Short.IIb.ProjectedEquation p z ∧
    ∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z) (g j)

/-- The quantifier shell of `BgCorrGradEq`: a statement `C p z g` about the data holds for small
`ν` in the background regime. -/
def GERegime (C : (p : Params) → p.Z → (Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) → Prop) :
    Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.mode = q → ∀ (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E),
        GEData p z g → C p z g

/-- (a) **Weak differentiation** (source 2533-2537): for the three pieces `gF, gL, gQ` of the
projected equation, on every solenoidal test `Φ`, with `Ψ = ∂_jΦ`,
`⟨L₀ᵗΦ, D_jw⟩ = ½⟨Φ, D_jw⟩ + ⟨Ψ, gF⟩ + ⟨Ψ, gQ⟩ + ⟨(∇raw)ᵗΨ - raw·∇Ψ, w⟩
  + ∑ᵢ αᵢ(⟨L₀ᵗΨ, Eᵢ⟩ + ⟨(∇raw)ᵗΨ - raw·∇Ψ, Eᵢ⟩)`;
this uses `∂_j L₀ᵗ = L₀ᵗ∂_j + ½∂_j` (`[∂_j, y·∇] = ∂_j`; `∂_j` commutes with `∂_τ`, `Δ`, and
preserves solenoidal tests), `A₀w` paired as `⟨L₀ᵗ·, w⟩`, and `HasPhaseOp (-∂_j) w D_jw`. -/
def GEWeak : Prop := GERegime fun p z g =>
  ∀ gF gL gQ : Yq p.period UnforcedLeray.B0412.q0E,
    p.RawRel gF → p.OrdRel z gL → p.QuadRel z z gQ → gF + gL + gQ = 0 →
    ∀ (j : Fin 3) (Φ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3),
      IsSolTest p.period Φ →
      phasePair p.period UnforcedLeray.B0412.q0E (UnforcedLeray.B0411.L0T p.ν Φ) (g j) =
        (1 / 2 : ℂ) * phasePair p.period UnforcedLeray.B0412.q0E Φ (g j) +
        phasePair p.period UnforcedLeray.B0412.q0E (dy j Φ) gF +
        phasePair p.period UnforcedLeray.B0412.q0E (dy j Φ) gQ +
        pairF p.period (convT p.raw (dy j Φ)) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          (pairF p.period (UnforcedLeray.B0411.L0T p.ν (dy j Φ)) (p.Efun i) +
            pairF p.period (convT p.raw (dy j Φ)) (p.Efun i))

/-- **`D²w ∈ Y_p`** (source 1415-1424 free heat estimate for the Cartesian second derivatives of
`w ∈ D_p`; used at 2531): the gradient `D_jw` has distributional derivatives in `Y_p`. -/
def GEHess : Prop := GERegime fun p z g =>
  ∃ h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E,
    ∀ j k : Fin 3, HasPhaseOp (fun Φ => -dy k Φ) (g j) (h j k)

/-- **`Dw ∈ Y_{2p}`** (source 2531, `‖Dw‖²_{Y_{2p}} ≤ C‖w‖_∞‖D²w‖_{Y_p}`, by Hölder/difference
quotients with `w ∈ L^∞`, `bg:supremum-embedding` 1515-1531, and `D²w ∈ Y_p`): each `D_jw` is
in `L^{2p}` of the phase measure. -/
def GEGradL2p : Prop := GERegime fun p z g =>
  ∀ j : Fin 3, MemLp (fun x : ℝ × UnforcedLeray.Space => rep (g j) x.1 x.2)
    (2 * UnforcedLeray.B0412.q0E)
    ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume)

/-- (b) **Raw term** (source 2542-2551, `U_raw` derivative bounds 1206-1222): the derivative of
the projected raw residual is in `Y_p`: for every `gF` with `RawRel gF` and each `j` there is
`F ∈ Y_p` with `⟨∂_jΦ, gF⟩ = ⟨Φ, F⟩` on solenoidal tests. -/
def GERaw : Prop := GERegime fun p _ _ =>
  ∀ gF : Yq p.period UnforcedLeray.B0412.q0E, p.RawRel gF → ∀ j : Fin 3,
    ∃ F : Yq p.period UnforcedLeray.B0412.q0E, ∀ Φ, IsSolTest p.period Φ →
      phasePair p.period UnforcedLeray.B0412.q0E (dy j Φ) gF =
        phasePair p.period UnforcedLeray.B0412.q0E Φ F

/-- (b) **Inlet terms** (source 2385-2387 inlet `W^{j,∞}`, 2542-2551): the derivative of the
inlet columns' contribution is in `Y_p`. -/
def GEInlet : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j : Fin 3), ∃ F : Yq p.period UnforcedLeray.B0412.q0E,
    ∀ Φ, IsSolTest p.period Φ →
      pairF p.period (UnforcedLeray.B0411.L0T p.ν (dy j Φ)) (p.Efun i) +
          pairF p.period (convT p.raw (dy j Φ)) (p.Efun i) =
        phasePair p.period UnforcedLeray.B0412.q0E Φ F

/-- (b) **Linear term** (source 2525-2531, with `D²w ∈ Y_p` and the `U_raw` derivative bounds
1206-1222): `⟨(∇raw)ᵗ∂_jΦ - raw·∇∂_jΦ, w⟩ = ⟨Φ, F⟩` with `F ∈ Y_p`. -/
def GELin : Prop := GERegime fun p z g =>
  (∃ h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E,
      ∀ j k : Fin 3, HasPhaseOp (fun Φ => -dy k Φ) (g j) (h j k)) →
  ∀ j : Fin 3, ∃ F : Yq p.period UnforcedLeray.B0412.q0E, ∀ Φ, IsSolTest p.period Φ →
    pairF p.period (convT p.raw (dy j Φ)) (fun x => rep (p.wOf z) x.1 x.2) =
      phasePair p.period UnforcedLeray.B0412.q0E Φ F

/-- (c) **Quadratic term** (source 2525-2533, 2562-2564: in `∂_j(u·∇u)` one factor is in `L^∞`,
the other in `Y_p`; `Dw·Dw ∈ Y_p` from `Dw ∈ Y_{2p}`): given `D²w ∈ Y_p` and `Dw ∈ Y_{2p}`, for
every `gQ` with `QuadRel z z gQ` there is `F ∈ Y_p` with `⟨∂_jΦ, gQ⟩ = ⟨Φ, F⟩`. -/
def GEQuad : Prop := GERegime fun p z g =>
  (∃ h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E,
      ∀ j k : Fin 3, HasPhaseOp (fun Φ => -dy k Φ) (g j) (h j k)) →
  (∀ j : Fin 3, MemLp (fun x : ℝ × UnforcedLeray.Space => rep (g j) x.1 x.2)
    (2 * UnforcedLeray.B0412.q0E)
    ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume)) →
  ∀ gQ : Yq p.period UnforcedLeray.B0412.q0E, p.QuadRel z z gQ → ∀ j : Fin 3,
    ∃ F : Yq p.period UnforcedLeray.B0412.q0E, ∀ Φ, IsSolTest p.period Φ →
      phasePair p.period UnforcedLeray.B0412.q0E (dy j Φ) gQ =
        phasePair p.period UnforcedLeray.B0412.q0E Φ F

/-- **Lift from solenoidal tests to all phase tests** (source 1358-1359 projected inverse,
1393-1400 maximal domain with no hidden null space): `D_jw ∈ Y_σ`; if `L₀ D_jw = F` against
solenoidal tests with `F ∈ Y_p`, then `D_jw` solves it against all phase tests with some
`F' ∈ Y_p` (`F' = L D_jw`: take `u ∈ D_p` with `Lu = 𝐏F`, and uniqueness gives `u = D_jw`). -/
def GELift : Prop := GERegime fun p _ g =>
  ∀ (j : Fin 3) (F : Yq p.period UnforcedLeray.B0412.q0E),
    (∀ Φ, IsSolTest p.period Φ →
      phasePair p.period UnforcedLeray.B0412.q0E (UnforcedLeray.B0411.L0T p.ν Φ) (g j) =
        phasePair p.period UnforcedLeray.B0412.q0E Φ F) →
    ∃ F' : Yq p.period UnforcedLeray.B0412.q0E,
      HasPhaseOp (fun Φ => (0 : ℂ) • Φ + UnforcedLeray.B0411.L0T p.ν Φ) (g j) F'

/-- Combine two regime statements: take the smaller `ν₀`. -/
theorem geRegime_bind {A B C : (p : Params) → p.Z →
      (Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) → Prop}
    (hA : GERegime A) (hB : GERegime B)
    (h : ∀ p z g, GEData p z g → A p z g → B p z g → C p z g) : GERegime C := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₁, hν₁, H1⟩ := hA lam q hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := hB lam q hq dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hreg hν hmode z g hd
  exact h p z g hd (H1 p d hreg (hν.trans (min_le_left _ _)) hmode z g hd)
    (H2 p d hreg (hν.trans (min_le_right _ _)) hmode z g hd)

theorem geRegime_const {C : (p : Params) → p.Z →
      (Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) → Prop}
    (h : ∀ p z g, GEData p z g → C p z g) : GERegime C := by
  intro lam q hq dm dp hdm
  exact ⟨1, one_pos, fun p d _ _ _ z g hd => h p z g hd⟩

/-- `BgCorrGradEq` from the lemmas above. -/
theorem bgCorrGradEq_of (h1 : GEWeak) (h2 : GEHess) (h3 : GEGradL2p) (h4 : GERaw)
    (h5 : GEInlet) (h6 : GELin) (h7 : GEQuad) (h8 : GELift) : BgCorrGradEq := by
  intro lam q hq dm dp hdm
  obtain ⟨n1, hn1, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨n2, hn2, H2⟩ := h2 lam q hq dm dp hdm
  obtain ⟨n3, hn3, H3⟩ := h3 lam q hq dm dp hdm
  obtain ⟨n4, hn4, H4⟩ := h4 lam q hq dm dp hdm
  obtain ⟨n5, hn5, H5⟩ := h5 lam q hq dm dp hdm
  obtain ⟨n6, hn6, H6⟩ := h6 lam q hq dm dp hdm
  obtain ⟨n7, hn7, H7⟩ := h7 lam q hq dm dp hdm
  obtain ⟨n8, hn8, H8⟩ := h8 lam q hq dm dp hdm
  refine ⟨min n1 (min n2 (min n3 (min n4 (min n5 (min n6 (min n7 n8)))))),
    lt_min hn1 (lt_min hn2 (lt_min hn3 (lt_min hn4 (lt_min hn5 (lt_min hn6 (lt_min hn7 hn8)))))),
    ?_⟩
  intro p d hreg hν hmode z hPE g hg j
  have hd : GEData p z g := ⟨hPE, hg⟩
  have e1 : p.ν ≤ n1 := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ n2 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : p.ν ≤ n3 := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have e4 : p.ν ≤ n4 := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have e5 : p.ν ≤ n5 := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have e6 : p.ν ≤ n6 := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _))))))
  have e7 : p.ν ≤ n7 := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))))))
  have e8 : p.ν ≤ n8 := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))))))
  obtain ⟨gF, gL, gQ, hF, hL, hQ, hsum⟩ := hPE
  have W := H1 p d hreg e1 hmode z g hd gF gL gQ hF hL hQ hsum
  have hess := H2 p d hreg e2 hmode z g hd
  have l2p := H3 p d hreg e3 hmode z g hd
  obtain ⟨Fr, hFr⟩ := H4 p d hreg e4 hmode z g hd gF hF j
  choose Fi hFi using fun i : Fin 2 => H5 p d hreg e5 hmode z g hd i j
  obtain ⟨Fl, hFl⟩ := H6 p d hreg e6 hmode z g hd hess j
  obtain ⟨Fq, hFq⟩ := H7 p d hreg e7 hmode z g hd hess l2p gQ hQ j
  refine H8 p d hreg e8 hmode z g hd j
    ((1 / 2 : ℂ) • g j + Fr + Fq + Fl + ∑ i : Fin 2, (p.coord z i : ℂ) • Fi i) ?_
  intro Φ hΦ
  rw [W j Φ hΦ, hFr Φ hΦ, hFq Φ hΦ, hFl Φ hΦ]
  simp only [map_add, map_smul, map_sum, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hFi i Φ hΦ])]

end UnforcedLeray.Short.PartIIIb.Concrete
