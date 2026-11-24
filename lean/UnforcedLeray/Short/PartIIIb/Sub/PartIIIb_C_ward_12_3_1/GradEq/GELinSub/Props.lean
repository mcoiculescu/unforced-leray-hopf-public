import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Defs
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductHilbert

/-!
# `GELin`: the exact statements of the sub-lemmas (source 2525-2533, 1217-1219)

Task `PartIII-b:C/ward/12/3/1/2/6/org`.  Each `Prop` below is the target of one Haiku task; all
statements are compiled here.  Source of record
`the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep phaseCell)

/-- `∂_j raw` as a field `ℝ → SpatialField`. -/
def rawDV (p : Params) (j : Fin 3) : ℝ → UnforcedLeray.SpatialField :=
  fun τ y => rawD p j (τ, y)

/-- A real field `V` which is `C^∞` jointly in `(τ, y)` and `P`-periodic in `τ`. -/
def IsSmoothPer (P : ℝ) (V : ℝ → UnforcedLeray.SpatialField) : Prop :=
  ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2) ∧ ∀ τ y, V (τ + P) y = V τ y

/-- The transposed field of `convT V` against `v` with distributional derivatives `v'`:
`S(V,v,v')ᵢ = ∑ₖ ∂ₖVᵢ vₖ + ∑ₘ (∂ₘVₘ vᵢ + Vₘ (v'ₘ)ᵢ)`, so that
`⟨convT V Φ, v⟩ = ⟨Φ, S(V,v,v')⟩` (the term `-V·∇Φ` is integrated by parts with `∂ₘv = v'ₘ`). -/
def convTAdj {P : ℝ} [Fact (0 < P)] (V : ℝ → UnforcedLeray.SpatialField)
    (v : Yq P UnforcedLeray.B0412.q0E) (v' : Fin 3 → Yq P UnforcedLeray.B0412.q0E)
    (x : ℝ × UnforcedLeray.Space) : UnforcedLeray.PhaseSpace.CVec3 :=
  WithLp.toLp 2 fun i =>
    ∑ k : Fin 3, ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ) * rep v x.1 x.2 k +
      ∑ m : Fin 3, (((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single m 1) m : ℝ) : ℂ) *
          rep v x.1 x.2 i + ((V x.1 x.2 m : ℝ) : ℂ) * rep (v' m) x.1 x.2 i)

/-- Raw hypotheses at one parameter point: joint smoothness, periodicity, global bounds of the
derivatives of orders `k = 0, 1, 2` (`k : Fin 3`, the orders used by `GELinField`;
source 1217-1219). -/
def GELinRawOK (p : Params) : Prop :=
  IsSmoothPer p.period p.raw ∧
    ∀ k : Fin 3, ∃ C : ℝ, ∀ (τ : ℝ) (y : UnforcedLeray.Space),
      ‖iteratedFDeriv ℝ (k : ℕ) (p.raw τ) y‖ ≤ C

/-- Leibniz: `∂_j(convT V Φ) = convT V ∂_jΦ + convT (∂_jV) Φ`. -/
def GELinLeibniz : Prop :=
  ∀ (p : Params), IsSmoothPer p.period p.raw → ∀ (j : Fin 3) (Φ : ℝ × UnforcedLeray.Space → CVec3),
    ContDiff ℝ ∞ Φ →
      dy j (convT p.raw Φ) = convT p.raw (dy j Φ) + convT (rawDV p j) Φ

/-- `∂_j raw` is again smooth and periodic. -/
def GELinRawDVSmooth : Prop :=
  ∀ (p : Params), IsSmoothPer p.period p.raw → ∀ j : Fin 3, IsSmoothPer p.period (rawDV p j)

/-- `convT V Φ` is a phase test for a smooth periodic `V` and a phase test `Φ`. -/
def GELinConvTPhaseTest : Prop :=
  ∀ (P : ℝ) (V : ℝ → UnforcedLeray.SpatialField), IsSmoothPer P V →
    ∀ Φ : ℝ × UnforcedLeray.Space → CVec3, IsPhaseTest P Φ → IsPhaseTest P (convT V Φ)

/-- Weak derivative against a phase test, in `pairF` form:
`⟨∂_mΘ, v⟩ = -⟨Θ, v'ₘ⟩`. -/
def GELinPairDeriv : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (v v' : Yq P UnforcedLeray.B0412.q0E) (m : Fin 3),
    HasPhaseOp (fun Φ => -dy m Φ) v v' →
    ∀ Θ : ℝ × UnforcedLeray.Space → CVec3, IsPhaseTest P Θ →
      pairF P (dy m Θ) (fun x => rep v x.1 x.2) = - pairF P Θ (fun x => rep v' x.1 x.2)

/-- Transposition: `⟨convT V Φ, v⟩ = ⟨Φ, convTAdj V v v'⟩`, with integrability of the right
integrand. -/
def GELinAdjoint : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (V : ℝ → UnforcedLeray.SpatialField), IsSmoothPer P V →
    ∀ (v : Yq P UnforcedLeray.B0412.q0E) (v' : Fin 3 → Yq P UnforcedLeray.B0412.q0E),
      (∀ m, HasPhaseOp (fun Φ => -dy m Φ) v (v' m)) →
      ∀ Φ : ℝ × UnforcedLeray.Space → CVec3, IsPhaseTest P Φ →
        Integrable (fun x => dotL (Φ x) (convTAdj V v v' x)) (volume.restrict (phaseCell P)) ∧
        Integrable (fun x => dotL (convT V Φ x) (rep v x.1 x.2)) (volume.restrict (phaseCell P)) ∧
        pairF P (convT V Φ) (fun x => rep v x.1 x.2) = pairF P Φ (convTAdj V v v')

/-- **Pointwise integration by parts** (the identity behind `GELin`): for every phase test `Φ`,
`⟨convT raw ∂_jΦ, w⟩ = ⟨Φ, GELinField⟩`. -/
def GELinIBP : Prop :=
  ∀ (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3),
    IsSmoothPer p.period p.raw →
    (∀ m, HasPhaseOp (fun Φ => -dy m Φ) (p.wOf z) (g m)) →
    (∀ m, HasPhaseOp (fun Φ => -dy m Φ) (g j) (h j m)) →
    ∀ Φ : ℝ × UnforcedLeray.Space → CVec3, IsPhaseTest p.period Φ →
      pairF p.period (convT p.raw (dy j Φ)) (fun x => rep (p.wOf z) x.1 x.2) =
        pairF p.period Φ (GELinField p z g h j)

/-- Strong measurability of the field. -/
def GELinFieldMeas : Prop :=
  ∀ (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3),
    IsSmoothPer p.period p.raw → StronglyMeasurable (GELinField p z g h j)

/-- Periodicity of the field in the phase. -/
def GELinFieldPer : Prop :=
  ∀ (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3),
    IsSmoothPer p.period p.raw →
    ∀ τ y, GELinField p z g h j (τ + p.period, y) = GELinField p z g h j (τ, y)

/-- `L^{q₀}` bound on a period (Hölder with the bounded derivatives of `raw`). -/
def GELinFieldLp : Prop :=
  ∀ (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3),
    GELinRawOK p →
    ∫⁻ τ in Ioc (0 : ℝ) p.period, ∫⁻ y, ‖GELinField p z g h j (τ, y)‖ₑ ^
      UnforcedLeray.B0412.q0E.toReal < ⊤

/-- The field is (a representative of) an element of `Y_p`, and pairs with phase tests by `pairF`. -/
def GELinFieldYq : Prop :=
  ∀ (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3),
    GELinRawOK p →
    ∃ F : Yq p.period UnforcedLeray.B0412.q0E, ∀ Φ, IsPhaseTest p.period Φ →
      phasePair p.period UnforcedLeray.B0412.q0E Φ F = pairF p.period Φ (GELinField p z g h j)

/-- Raw smoothness: see `RawSmoothBdd` (source 1217-1219), unpacked at a parameter point. -/
theorem rawSmoothBdd_ok {dm dp : ℝ} (H : RawSmoothBdd) (hdm : 0 < dm) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (p : Params) (d : ℝ),
      UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → GELinRawOK p := by
  obtain ⟨ν₀, hν₀, hH⟩ := H dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hH p d hreg hν
  exact ⟨⟨h1, h2⟩, h3⟩

/-- `GELinField` is `-S(raw, g_j, h_j) - S(∂_j raw, w, g)`. -/
theorem gELinField_eq (p : Params) (z : p.Z)
    (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3) :
    GELinField p z g h j = fun x =>
      -(convTAdj p.raw (g j) (h j) x) - convTAdj (rawDV p j) (p.wOf z) g x := by
  funext x
  apply WithLp.ofLp_injective
  funext i
  have e : rawDV p j x.1 = fun y => fderiv ℝ (p.raw x.1) y (EuclideanSpace.single j 1) := rfl
  have e2 : ∀ m : Fin 3, rawDV p j x.1 x.2 m = rawD p j x m := fun m => rfl
  simp only [GELinField, convTAdj, e, rawD, rawDD, WithLp.ofLp_toLp, WithLp.ofLp_neg,
    WithLp.ofLp_sub, Pi.neg_apply, Pi.sub_apply, Finset.sum_add_distrib]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
