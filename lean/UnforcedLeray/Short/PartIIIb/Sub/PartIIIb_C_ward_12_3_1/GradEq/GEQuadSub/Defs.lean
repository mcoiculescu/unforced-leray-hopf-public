import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEqSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEWeak

/-!
# `GEQuad`: concrete objects and the Haiku-sized statements (source 2525-2533, 2562-2564)

Task `PartIII-b:C/ward/12/3/1/2/7/org`.  Source of record
`the November 2 reference manuscript`.

With `u = p.uOf z = e + w`, `QuadRel z z gQ` says `⟨Φ, gQ⟩ = -⟨(u·∇)Φ, u⟩` on solenoidal `Φ`
(`Params.QuadRel`).  For `Φ` solenoidal, `∂_jΦ` is solenoidal (`gEW_isSolTest_dy`), so
`⟨∂_jΦ, gQ⟩ = -⟨(u·∇)∂_jΦ, u⟩ = -∫ ∑_{k,i} u_k ∂_k∂_jΦ_i u_i`.  Two integrations by parts
(first in `y_k`, then in `y_j`; no divergence-free input is used) give
`∫ Φ_i ∂_j∂_k(u_k u_i)`, and
`∂_j∂_k(u_k u_i) = ∂_j∂_k u_k · u_i + ∂_k u_k ∂_j u_i + ∂_j u_k ∂_k u_i + u_k ∂_j∂_k u_i`.
Hence `⟨∂_jΦ, gQ⟩ = ⟨Φ, F⟩` with `F = GEQuadField` (a minus sign built in).  On `div u = 0`
this is the source's `F_i = ∑_k (∂_ju_k ∂_ku_i + u_k ∂_j∂_ku_i)` (2525-2533), the two extra
terms vanishing.

The IBP only needs weak derivatives in the *spatial* variable `y`; the product rule for them
(`WeakMulRule`) is proved by spatial mollification and Fubini in `τ`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep phaseInt)

/-- `D_j u` pointwise: the classical derivative of the affine inlet `e = E_bg α` plus the
representative of the weak gradient `g j` of `w` (source 2525-2531). -/
def GEQDu (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3)
    (x : ℝ × UnforcedLeray.Space) : UnforcedLeray.PhaseSpace.CVec3 :=
  dy j (p.eFun (p.coord z)) x + rep (g j) x.1 x.2

/-- `D_jD_k u` pointwise: inlet second derivative plus the representative of the weak Hessian
`h j k` of `w` (source 2525-2531). -/
def GEQDdu (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j k : Fin 3)
    (x : ℝ × UnforcedLeray.Space) : UnforcedLeray.PhaseSpace.CVec3 :=
  dy j (dy k (p.eFun (p.coord z))) x + rep (h j k) x.1 x.2

/-- The pointwise source `F = -∑_k ∂_j∂_k(u_k u_i)` expanded by the product rule
(see the module docstring); `F_i = -∑_k (∂_j∂_k u_k u_i + ∂_k u_k ∂_j u_i + ∂_j u_k ∂_k u_i
+ u_k ∂_j∂_k u_i)`, where `∂_j∂_k u` is `GEQDdu k j` (`∂_j` of `D_k u`; no Hessian symmetry is
assumed). -/
def GEQuadField (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3)
    (x : ℝ × UnforcedLeray.Space) : UnforcedLeray.PhaseSpace.CVec3 :=
  WithLp.toLp 2 fun i => -∑ k : Fin 3,
    (GEQDdu p z g h k j x k * p.uOf z x i + GEQDu p z g k x k * GEQDu p z g j x i +
      GEQDu p z g j x k * GEQDu p z g k x i + p.uOf z x k * GEQDdu p z g h k j x i)

/-- Weak `y_j`-derivative of scalar fields on the phase cell: `∂_j f = G` tested against
scalar phase tests. -/
def WeakDyS (P : ℝ) (j : Fin 3) (f G : ℝ × UnforcedLeray.Space → ℂ) : Prop :=
  ∀ φ : ℝ × UnforcedLeray.Space → ℂ, IsPhaseTest P φ →
    phaseInt P (fun x => dy j φ x * f x) = - phaseInt P (fun x => φ x * G x)

/-- The standing hypotheses of `GEQuad`: Hessian `h` of `w` and `Dw ∈ L^{2q₀}` on the cell. -/
def GEQHyp (p : Params) (z : p.Z) (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) : Prop :=
  (∀ j k : Fin 3, HasPhaseOp (fun Φ => -dy k Φ) (g j) (h j k)) ∧
  (∀ j : Fin 3, MemLp (fun x : ℝ × UnforcedLeray.Space => rep (g j) x.1 x.2)
    (2 * UnforcedLeray.B0412.q0E)
    ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume))

/-- Local-in-`y` integrability on the phase cell: `L^p` on `(0,P] × B(0,R)` for every `R`
(the cell itself has infinite measure; the affine inlet is bounded but not integrable). -/
def MemLpLoc (P : ℝ) (f : ℝ × UnforcedLeray.Space → ℂ) (q : ENNReal) : Prop :=
  ∀ R : ℝ, MemLp f q
    ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume.restrict (Metric.closedBall 0 R)))

/-- **Weak product rule in `y`** (source 2562-2564, "one factor in `L^∞`, the other in `Y_p`";
here in the form used twice: `u·u` with `u ∈ L^∞ ⊂ L^{2q₀}`, `Du ∈ L^{2q₀}`, and `Du·Du` with
`Du ∈ L^{2q₀}`, `D²u ∈ L^{q₀}`).  If `f, g ∈ L^{2q₀}` and their weak `y_j`-derivatives
`Df, Dg ∈ L^{q₀}` on the cell (`q₀ = 11/4`, so `fDg ∈ L^{11/6} ⊂ L^1_loc`), then
`∂_j(fg) = Df·g + f·Dg` weakly.  Proof: mollify in `y` (Friedrichs), classical product rule,
pass to the limit by Hölder; the `τ`-integral is untouched (Fubini). -/
def WeakMulRule : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (j : Fin 3) (f g Df Dg : ℝ × UnforcedLeray.Space → ℂ),
    MemLpLoc P f (2 * UnforcedLeray.B0412.q0E) →
    MemLpLoc P g (2 * UnforcedLeray.B0412.q0E) →
    MemLpLoc P Df UnforcedLeray.B0412.q0E →
    MemLpLoc P Dg UnforcedLeray.B0412.q0E →
    WeakDyS P j f Df → WeakDyS P j g Dg →
    WeakDyS P j (fun x => f x * g x) (fun x => Df x * g x + f x * Dg x)

/-- **Weak derivative of `u`** (source 2525-2531): componentwise, `∂_j u_i = (D_j u)_i`:
the inlet part classically (`InletContDiff`, `UnforcedLeray.Short.IIb.inletContDiff`, and
boundedness of its first derivatives, source 2385-2387) and `w` by `HasPhaseOp (-∂_j) w (g j)`
with `phasePair_eq_pairF_rep`. -/
def GEQWeakU : Prop := GERegime fun p z g => ∀ h, GEQHyp p z g h →
  ∀ j i : Fin 3, WeakDyS p.period j (fun x => p.uOf z x i) (fun x => GEQDu p z g j x i)

/-- **Weak derivative of `D_ku`**: `∂_j (D_k u)_i = (D_jD_k u)_i` (inlet classically; `w` by
`HasPhaseOp (-∂_j) (g k) (h k j)`; note `GEQDdu j k` uses `h j k`, so the symmetric
slot is `∂_j∂_k = ∂_k∂_j` on the smooth inlet and the hypothesis `GEQHyp` is stated with
`HasPhaseOp (-dy k) (g j) (h j k)`, i.e. `∂_k (D_j w) = h j k`). Statement: for all `j k i`,
`∂_k (D_j u)_i = (D_jD_k u)_i`. -/
def GEQWeakDu : Prop := GERegime fun p z g => ∀ h, GEQHyp p z g h →
  ∀ j k i : Fin 3, WeakDyS p.period k (fun x => GEQDu p z g j x i)
    (fun x => GEQDdu p z g h j k x i)

/-- **Integrability** (source 2531, 1515-1531, 2385-2387): `u ∈ L^{2q₀}` on the cell (indeed
`L^∞` by `PartIIa.graphSupEmbedding`/`commonBodyGraphBound`, `cw_mem_X`, `X_le_D`, plus the
bounded inlet), `D u ∈ L^{2q₀}`, and `D²u ∈ L^{q₀}` on the cell. -/
def GEQMem : Prop := GERegime fun p z g => ∀ h, GEQHyp p z g h →
  (∀ i : Fin 3, MemLpLoc p.period (fun x => p.uOf z x i) (2 * UnforcedLeray.B0412.q0E)) ∧
  (∀ j i : Fin 3, MemLpLoc p.period (fun x => GEQDu p z g j x i) (2 * UnforcedLeray.B0412.q0E)) ∧
  (∀ j k i : Fin 3, MemLpLoc p.period (fun x => GEQDdu p z g h j k x i) UnforcedLeray.B0412.q0E)

/-- **Weak integration by parts for the quadratic term** (source 2525-2533): for every phase
test `Φ`, `⟨(u·∇)∂_jΦ, u⟩ = -⟨Φ, F⟩`.  From `GEQWeakU`, `GEQWeakDu`, `GEQMem`,
`WeakMulRule` applied to `u_k u_i` (`k`-derivative) and then to the resulting terms
`Du·u`, `u·Du` (`j`-derivative), and `dy_j dy_k = dy_k dy_j` on the smooth test. -/
def GEQIbp : Prop := GERegime fun p z g => ∀ h, GEQHyp p z g h →
  ∀ (j : Fin 3) (Φ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3),
    IsPhaseTest p.period Φ →
    pairF p.period (advT (p.uOf z) (dy j Φ)) (p.uOf z) = -pairF p.period Φ (GEQuadField p z g h j)

/-- **`F ∈ Y_{q₀}`** (source 2562-2564, Hölder): `GEQuadField` is strongly measurable,
`P`-periodic in `τ`, and has finite `L^{q₀}` period integral, hence (via
`PartIIa.periodicFieldToYq_proof`) it represents an element of `Yq`. Statement: there is
`F : Yq` with `⟨Φ, F⟩ = pairF Φ (GEQuadField ..)` for every phase test `Φ`. -/
def GEQYq : Prop := GERegime fun p z g => ∀ h, GEQHyp p z g h →
  ∀ j : Fin 3, ∃ F : Yq p.period UnforcedLeray.B0412.q0E,
    ∀ Φ, IsPhaseTest p.period Φ →
      phasePair p.period UnforcedLeray.B0412.q0E Φ F = pairF p.period Φ (GEQuadField p z g h j)

/-- `GEQuad` from the leaves. -/
theorem gEQuad_of (h1 : GEQIbp) (h2 : GEQYq) : GEQuad := by
  intro lam q hq dm dp hdm
  obtain ⟨n1, hn1, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨n2, hn2, H2⟩ := h2 lam q hq dm dp hdm
  refine ⟨min n1 n2, lt_min hn1 hn2, ?_⟩
  intro p d hreg hν hmode z g hd hess l2p gQ hQ j
  have e1 : p.ν ≤ n1 := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ n2 := hν.trans (min_le_right _ _)
  obtain ⟨h, hh⟩ := hess
  have hyp : GEQHyp p z g h := ⟨hh, l2p⟩
  obtain ⟨F, hF⟩ := H2 p d hreg e2 hmode z g hd h hyp j
  refine ⟨F, fun Φ hΦ => ?_⟩
  have hΨ := gEW_isSolTest_dy hΦ j
  rw [hQ (dy j Φ) hΨ, hF Φ hΦ.1,
    H1 p d hreg e1 hmode z g hd h hyp j Φ hΦ.1, neg_neg]

end UnforcedLeray.Short.PartIIIb.Concrete
