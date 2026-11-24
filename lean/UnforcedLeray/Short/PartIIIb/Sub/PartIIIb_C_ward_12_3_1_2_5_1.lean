import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1` (decomposition): `GEInletIBP`

Source `the November 2 reference manuscript`
lines 2385-2387, 2542-2551 (`C_{k,N} ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`, whose `p`-th integral is
`∫_R^∞ ϱ^{2-p(3+k)} dϱ < ∞`; the inlet cutoff vanishes near the axis), 1206-1222, 2563-2569.

With `B_raw E = (raw·∇)E + (E·∇)raw` (`raw` solenoidal), the transpose of `B_raw` is `convT raw`,
and `⟨L₀ᵗψ, E⟩ + ⟨convT raw ψ, E⟩ = ⟨ψ, L₀E + B_raw E⟩`.  Taking `ψ = ∂_jΦ` and integrating by parts
in `y_j` gives the field `inletFn`.  The exponent is `q0E` (not `2 q0E`).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `(E·∇)V`, `((E·∇)V)_i = ∑ₖ E_k ∂_kV_i`, for a real field `V` and complex `E`. -/
def gradAlong (V : ℝ → UnforcedLeray.SpatialField) (E : ℝ × UnforcedLeray.Space → CVec3)
    (x : ℝ × UnforcedLeray.Space) : CVec3 :=
  WithLp.toLp 2 fun i => ∑ k : Fin 3,
    E x k * ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)

/-- The inlet source `L₀E_i + B_raw E_i = L₀E_i + (raw·∇)E_i + (E_i·∇)raw`. -/
def inletSrc (p : Params) (i : Fin 2) : ℝ × UnforcedLeray.Space → CVec3 :=
  UnforcedLeray.B0411.L0 p.ν (p.Efun i) + advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)
    + gradAlong p.raw (p.Efun i)

/-- The integrated-by-parts field `F_n = -∂_j(L₀E_i + B_raw E_i)`. -/
def inletFn (p : Params) (i : Fin 2) (j : Fin 3) : ℝ × UnforcedLeray.Space → CVec3 :=
  -(dy j (inletSrc p i))

/-- **(a) Integrability** (2542-2551, 2563-2569, 1206-1222): `F_n ∈ L^{q0E}` of the phase measure,
by the decay `C ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}` of the unprojected derivatives of `E_i`, the bounds on
`raw`, and vanishing of the inlet cutoff near the axis (uniform in the phase). -/
def InletFnMemLp : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j : Fin 3), MemLp (inletFn p i j) UnforcedLeray.B0412.q0E
    ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume)

/-- **(b) The integration by parts** (2385-2387): for `F_n ∈ L^{q0E}` (so all pairings converge),
`E_i` smooth and `period`-periodic in the phase, `Φ` compactly `y`-supported, no boundary terms. -/
def InletIBPIdentity : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j : Fin 3),
    MemLp (inletFn p i j) UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) →
    ∀ Φ, IsSolTest p.period Φ →
      pairF p.period (UnforcedLeray.B0411.L0T p.ν (dy j Φ)) (p.Efun i) +
          pairF p.period (convT p.raw (dy j Φ)) (p.Efun i) = pairF p.period Φ (inletFn p i j)

theorem gEInletIBP_of (h1 : InletFnMemLp) (h2 : InletIBPIdentity) : GEInletIBP := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨ν₁, hν₁, H2⟩ := h2 lam q hq dm dp hdm
  refine ⟨min ν₀ ν₁, lt_min hν₀ hν₁, fun p d hreg hν hm z g hg i j => ?_⟩
  have hm1 := H1 p d hreg (hν.trans (min_le_left _ _)) hm z g hg i j
  exact ⟨inletFn p i j, hm1, H2 p d hreg (hν.trans (min_le_right _ _)) hm z g hg i j hm1⟩

end UnforcedLeray.Short.PartIIIb.Concrete
