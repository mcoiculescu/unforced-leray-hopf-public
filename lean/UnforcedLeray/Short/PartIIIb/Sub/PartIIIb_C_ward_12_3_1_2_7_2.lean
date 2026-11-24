import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs

/-!
# Decomposition of `gEQWeakU` (source 2525-2531, 2385-2387)

Weak `y_j`-derivative of `u = e + rep w`: inlet classically, `w` by `HasPhaseOp (-∂_j)` and
`phasePair_eq_pairF_rep` (tested with `φ e_i`), and the sum by additivity of `phaseInt` on
integrable pieces.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params rep)

/-- Continuous and bounded scalar field on the phase space. -/
def GEQEntry (f : ℝ × UnforcedLeray.Space → ℂ) : Prop :=
  Continuous f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

/-- **Inlet part** (source 2385-2387, 2525-2531): for the affine inlet `e = p.eFun (p.coord z)`
(smooth by `IIb.inletContDiff` with bounded derivatives, `InletJetBound`), the components of
`e`, `∂_j e`, `∂_j∂_k e` are continuous and bounded, `∂_j e_i` is the weak `y_j`-derivative of
`e_i`, and `∂_j∂_k e_i` is the weak `y_k`-derivative of `∂_j e_i` (classical integration by
parts in `y` for compactly supported tests, `dy j (dy k e) = dy k (dy j e)`). -/
def GEQInletWeak : Prop := GERegime fun p z _ => ∀ j k i : Fin 3,
  GEQEntry (fun x => p.eFun (p.coord z) x i) ∧
  GEQEntry (fun x => dy j (p.eFun (p.coord z)) x i) ∧
  GEQEntry (fun x => dy j (dy k (p.eFun (p.coord z))) x i) ∧
  WeakDyS p.period j (fun x => p.eFun (p.coord z) x i) (fun x => dy j (p.eFun (p.coord z)) x i) ∧
  WeakDyS p.period k (fun x => dy j (p.eFun (p.coord z)) x i)
    (fun x => dy j (dy k (p.eFun (p.coord z))) x i)

/-- The weak-derivative conclusion for the components of the representatives of `f, G`, with
`L^{q₀}` integrability on the cell. -/
def RepWeakData (P : ℝ) [Fact (0 < P)] (j : Fin 3) (f G : Yq P UnforcedLeray.B0412.q0E) : Prop :=
  ∀ i : Fin 3,
    WeakDyS P j (fun x => rep f x.1 x.2 i) (fun x => rep G x.1 x.2 i) ∧
    MemLp (fun x : ℝ × UnforcedLeray.Space => rep f x.1 x.2 i) UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) P)).prod volume) ∧
    MemLp (fun x : ℝ × UnforcedLeray.Space => rep G x.1 x.2 i) UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) P)).prod volume)

/-- **`w` part** (source 2525-2531): `HasPhaseOp (-∂_j) f G` gives, componentwise, the weak
`y_j`-derivative of `rep f` equal to `rep G` (test `Φ = φ e_i`, `phasePair_eq_pairF_rep`), and
`rep f, rep G ∈ L^{q₀}` on the cell (`memLp_rep_periodCell`, components by the norm bound). -/
def GEQRepWeak : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (j : Fin 3) (f G : Yq P UnforcedLeray.B0412.q0E),
    HasPhaseOp (fun Φ => -dy j Φ) f G → RepWeakData P j f G

/-- **Sum of weak derivatives**: a continuous bounded `e` with weak derivative `e'` (continuous
bounded) plus an `L^{q₀}` field `r` with weak derivative `r' ∈ L^{q₀}` on the cell: the weak
derivative of `e + r` is `e' + r'`.  (Phase tests are bounded with bounded `y`-support, so all
four products are integrable; split `phaseInt` by Fubini/`integral_add`.) -/
def GEQWeakSum : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (j : Fin 3) (e e' r r' : ℝ × UnforcedLeray.Space → ℂ),
    GEQEntry e → GEQEntry e' →
    MemLp r UnforcedLeray.B0412.q0E ((volume.restrict (Ioc (0 : ℝ) P)).prod volume) →
    MemLp r' UnforcedLeray.B0412.q0E ((volume.restrict (Ioc (0 : ℝ) P)).prod volume) →
    WeakDyS P j e e' → WeakDyS P j r r' →
    WeakDyS P j (fun x => e x + r x) (fun x => e' x + r' x)

theorem gEQWeakU_of (h1 : GEQInletWeak) (h2 : GEQRepWeak) (h3 : GEQWeakSum) : GEQWeakU := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h1 lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hν hmode z g hd h _ j i
  obtain ⟨he, he', -, hw, -⟩ := H p d hreg hν hmode z g hd j j i
  obtain ⟨hr, hm, hm'⟩ := h2 p.period j (p.wOf z) (g j) (hd.2 j) i
  have := h3 p.period j _ _ _ _ he he' hm hm' hw hr
  convert this using 2 <;>
    simp [UnforcedLeray.Cons.C03.Concrete.Params.uOf, GEQDu]

end UnforcedLeray.Short.PartIIIb.Concrete
