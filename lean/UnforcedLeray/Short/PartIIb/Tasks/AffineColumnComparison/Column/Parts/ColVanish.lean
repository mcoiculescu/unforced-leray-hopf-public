import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.SmoothVanish

/-!
# Part II-b, task `PartII-b:G4/3/7/9` (`ColVanish`)

Source of record: `the November 2 reference manuscript`, lines 2360-2366.
The inlet profile `F = p.inletProfile i` vanishes on the open set `{s > H/2}`
(`inletProfileSmoothVanish`), hence so do all its chart derivatives there, and therefore the
drift part `colDiffR` and the interaction part `colIntR` of the column vanish on that set.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-- The derivative of a function which is eventually zero at `x` is eventually zero in every
direction at `x`. -/
private theorem colV_ev_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : E → F} {x : E}
    (h : ∀ᶠ y in 𝓝 x, G y = 0) (v : E) : ∀ᶠ y in 𝓝 x, fderiv ℝ G y v = 0 := by
  have h' : G =ᶠ[𝓝 x] fun _ => (0 : F) := h
  have h2 : fderiv ℝ G =ᶠ[𝓝 x] fderiv ℝ (fun _ => (0 : F)) := h'.fderiv
  filter_upwards [h2] with y hy
  rw [hy]
  simp

private theorem colV_ev_dS {G : Coord → Axi.Merid} {x : Coord}
    (h : ∀ᶠ y in 𝓝 x, G y = 0) : ∀ᶠ y in 𝓝 x, Axi.dS G y = 0 :=
  colV_ev_fderiv h (1, (0, 0))

private theorem colV_ev_dQ {G : Coord → Axi.Merid} {x : Coord}
    (h : ∀ᶠ y in 𝓝 x, G y = 0) : ∀ᶠ y in 𝓝 x, Axi.dQ G y = 0 :=
  colV_ev_fderiv h (0, (1, 0))

private theorem colV_ev_dEta {G : Coord → Axi.Merid} {x : Coord}
    (h : ∀ᶠ y in 𝓝 x, G y = 0) : ∀ᶠ y in 𝓝 x, Axi.dEta G y = 0 :=
  colV_ev_fderiv h (0, (0, 1))

private theorem colV_ev_kAge {G : Coord → Axi.Merid} {x : Coord}
    (h : ∀ᶠ y in 𝓝 x, G y = 0) : ∀ᶠ y in 𝓝 x, kAge G y = 0 := by
  filter_upwards [colV_ev_dS h, colV_ev_dEta h] with y h1 h2
  simp [kAge, h1, h2]

/-- `vecDiffEps` of an eventually vanishing profile vanishes eventually. -/
private theorem colV_ev_vecDiffEps {ε : ℝ} {F : Coord → Axi.Merid} {x : Coord}
    (h : ∀ᶠ y in 𝓝 x, F y = 0) : ∀ᶠ y in 𝓝 x, vecDiffEps ε F y = 0 := by
  have hdQ := colV_ev_dQ h
  have hdQQ := colV_ev_dQ hdQ
  have hdEE := colV_ev_dEta (colV_ev_dEta h)
  have hk1 := colV_ev_kAge hdQ
  have hsum : ∀ᶠ y in 𝓝 x, kAge F y + F y = 0 := by
    filter_upwards [colV_ev_kAge h, h] with y h1 h2
    simp [h1, h2]
  have hk2 := colV_ev_kAge hsum
  filter_upwards [hdQQ, hdEE, hk1, hk2, hsum, h, hdQ] with y a b c d e f g
  simp only [vecDiffEps, hoopR]
  rw [a, b, c, d, e, g, f]
  simp

/-- `bEps` of an eventually vanishing profile vanishes eventually. -/
private theorem colV_ev_bEps (p : Params) {F : Coord → Axi.Merid} {x : Coord}
    (h : ∀ᶠ y in 𝓝 x, F y = 0) : ∀ᶠ y in 𝓝 x, bEps p F y = 0 := by
  have hdQ := colV_ev_dQ h
  have hdE := colV_ev_dEta h
  have hsum : ∀ᶠ y in 𝓝 x, kAge F y + F y = 0 := by
    filter_upwards [colV_ev_kAge h, h] with y h1 h2
    simp [h1, h2]
  filter_upwards [hdQ, hdE, hsum, h] with y a b c d
  simp only [bEps, qEps]
  rw [c, a, b, d]
  simp

/-- **`ColVanish`** (SP 2360-2366): the column vanishes beyond the cutoff `s > H/2`. -/
theorem colVanish : UnforcedLeray.Short.IIb.ColVanish := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₀, hν₀, HV⟩ := inletProfileSmoothVanish Sig lam q hSig hq dm dp hdm
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg i x hx
  obtain ⟨h1, h2, h3, h4⟩ := hreg
  obtain ⟨-, hvan⟩ := HV p d h1 h2 h3 h4 i
  have hev : ∀ᶠ y in 𝓝 x, p.inletProfile i y = 0 := by
    filter_upwards [(continuous_fst.tendsto x).eventually (lt_mem_nhds hx)] with y hy
    exact hvan y hy
  have hdS : Axi.dS (p.inletProfile i) x = 0 := (colV_ev_dS hev).self_of_nhds
  have hVD : vecDiffEps p.ε (p.inletProfile i) x = 0 := (colV_ev_vecDiffEps hev).self_of_nhds
  have hB : bEps p (p.inletProfile i) x = 0 := (colV_ev_bEps p hev).self_of_nhds
  have hD : colDiffR p i x = 0 := by
    unfold colDiffR
    rw [hdS, hVD]
    simp
  have hI : colIntR p i x = 0 := by
    unfold colIntR
    rw [hB]
    simp
  unfold colEpsR
  split_ifs <;> simp [hD, hI]

end UnforcedLeray.Short.IIb
