import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.WeakH1Exists.H1Volterra

/-!
# Sub-module for `PartII-b:F8/1/org/2/2` (`RealCylOseenSpatialBootstrap`, SP 2052–2053, 2213–2217, 2296–2301)

Splits `RealCylOseenSpatialBootstrap` into two self-contained, parallel `[0, 2]` periodic-cylinder
PDE leaves in `namespace UnforcedLeray.Short.IIb`:

1. **`RealCylOseenWeakMildUnique`** (`PartII-b:F8/1/org/2/2/1`,
   `Short/PartII-b/Sub/PartII-b_F8_1_org_2/SpatialBootstrap/WeakMildUnique.lean`):
   mollified `L²_σ(C_c)` energy-Gronwall uniqueness identifying any weak `C([0, 2]; H¹_σ(C_c))`
   Oseen solution `(W, Wq, Wη)` `cellMeas c`-a.e. on every slice `s ∈ [0, 2]` with the canonical
   Volterra mild `H¹_σ(C_c)` evolution `F8WeakEx.E_oseen hc hν hV s 0 (H1Sol.ofRealDatum hdat)`.

2. **`RealCylOseenMildSpatialBootstrap`** (`PartII-b:F8/1/org/2/2/2`,
   `Short/PartII-b/Sub/PartII-b_F8_1_org_2/SpatialBootstrap/MildBootstrap.lean`):
   interior parabolic spatial `H¹_σ → H^∞_σ` bootstrap on `(0, 2)` for the canonical mild/weak
   evolution `U s := F8WeakEx.E_oseen hc hν hV s 0 u₀`, extracting spatially `C^∞`, `c`-periodic,
   divergence-free slices `w : ℝ → B0579.Plane → F8Ex.RMerid` in `C((0, 2); H^k(C_c))` for every
   `k : ℕ` (`F8Ex.IsRealSpatialSmoothOseenSlices`).

3. **`realCylOseenSpatialBootstrap_of_leaves`**: unconditional (`0 sorry`, `0 axiom`) assembly of
   `RealCylOseenSpatialBootstrap` from `RealCylOseenWeakMildUnique` and
   `RealCylOseenMildSpatialBootstrap`, composed in `PartII-b:F8/1/org/2/2`
   (`Short/PartII-b/Sub/PartII-b_F8_1_org_2/SpatialBootstrap.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

/-- **Leaf 1 for `PartII-b:F8/1/org/2/2` (`RealCylOseenWeakMildUnique`, task
`PartII-b:F8/1/org/2/2/1`)**: every weak `C([0, 2]; H¹_σ(C_c))` Oseen solution `(W, Wq, Wη)` with
`0 < c`, `0 < ν`, smooth BUC drift `V` (`F8Ex.IsSmoothBUCDrift c V`), and initial datum
`(u, uq, uη)` (`F8Ex.IsRealCylH1Datum c u uq uη`) agrees `F8Ex.cellMeas c`-almost everywhere on
each slice `s ∈ [0, 2]` with the canonical Volterra mild evolution
`F8WeakEx.E_oseen hc hν hV s 0 (F8WeakEx.H1Sol.ofRealDatum hdat)`. Composed in
`PartII-b:F8/1/org/2/2`. -/
def RealCylOseenWeakMildUnique : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (hν : 0 < ν),
    ∀ (V : ℝ → B0579.Plane → F8Ex.RMerid) (hV : F8Ex.IsSmoothBUCDrift c V),
      ∀ (u uq uη : B0579.Plane → F8Ex.RMerid)
        (W Wq Wη : ℝ → B0579.Plane → F8Ex.RMerid)
        (hdat : F8Ex.IsRealCylH1Datum c u uq uη),
        F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη →
          ∀ s ∈ Set.Icc (0 : ℝ) 2,
            let U := F8WeakEx.E_oseen hc hν hV s 0 (F8WeakEx.H1Sol.ofRealDatum hdat)
            W s =ᵐ[F8Ex.cellMeas c] (F8WeakEx.val0CLM c U : B0579.Plane → F8Ex.RMerid) ∧
            Wq s =ᵐ[F8Ex.cellMeas c] (F8WeakEx.dqCLM c U : B0579.Plane → F8Ex.RMerid) ∧
            Wη s =ᵐ[F8Ex.cellMeas c] (F8WeakEx.detaCLM c U : B0579.Plane → F8Ex.RMerid)

/-- **Leaf 2 for `PartII-b:F8/1/org/2/2` (`RealCylOseenMildSpatialBootstrap`, task
`PartII-b:F8/1/org/2/2/2`)**: interior parabolic spatial bootstrap on `(0, 2)` for the canonical
`C([0, 2]; H¹_σ(C_c))` mild/weak Oseen evolution `U s := F8WeakEx.E_oseen hc hν hV s 0 u₀` with
`0 < c`, `0 < ν`, smooth BUC drift `V` (`F8Ex.IsSmoothBUCDrift c V`), and arbitrary initial vector
`u₀ : F8WeakEx.H1Sol c`, producing spatially `C^∞`, `c`-periodic, divergence-free slices
`w : ℝ → B0579.Plane → F8Ex.RMerid` in `C((0, 2); H^k(C_c))` for every `k : ℕ`
(`F8Ex.IsRealSpatialSmoothOseenSlices`). Composed in `PartII-b:F8/1/org/2/2`. -/
def RealCylOseenMildSpatialBootstrap : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (hν : 0 < ν),
    ∀ (V : ℝ → B0579.Plane → F8Ex.RMerid) (hV : F8Ex.IsSmoothBUCDrift c V),
      ∀ u₀ : F8WeakEx.H1Sol c,
        ∃ w : ℝ → B0579.Plane → F8Ex.RMerid,
          F8Ex.IsRealSpatialSmoothOseenSlices c w
            (fun s => (F8WeakEx.val0CLM c (F8WeakEx.E_oseen hc hν hV s 0 u₀) :
              B0579.Plane → F8Ex.RMerid))
            (fun s => (F8WeakEx.dqCLM c (F8WeakEx.E_oseen hc hν hV s 0 u₀) :
              B0579.Plane → F8Ex.RMerid))
            (fun s => (F8WeakEx.detaCLM c (F8WeakEx.E_oseen hc hν hV s 0 u₀) :
              B0579.Plane → F8Ex.RMerid))

/-- **Conditional assembly of `RealCylOseenSpatialBootstrap` (`PartII-b:F8/1/org/2/2`)** from its
two `[0, 2]` periodic-cylinder PDE leaves. -/
theorem realCylOseenSpatialBootstrap_of_leaves
    (hUniq : RealCylOseenWeakMildUnique)
    (hBoot : RealCylOseenMildSpatialBootstrap) :
    UnforcedLeray.Short.IIb.RealCylOseenSpatialBootstrap := by
  intro c ν hc hν V hV u uq uη W Wq Wη hdat hwk
  let u₀ : F8WeakEx.H1Sol c := F8WeakEx.H1Sol.ofRealDatum hdat
  obtain ⟨w, hsp⟩ := hBoot c ν hc hν V hV u₀
  refine ⟨w, ?_⟩
  refine
    { ae_val := fun s hs =>
        (hsp.ae_val s hs).trans
          (hUniq c ν hc hν V hV u uq uη W Wq Wη hdat hwk s ⟨hs.1.le, hs.2.le⟩).1.symm
      ae_dq := fun s hs =>
        (hsp.ae_dq s hs).trans
          (hUniq c ν hc hν V hV u uq uη W Wq Wη hdat hwk s ⟨hs.1.le, hs.2.le⟩).2.1.symm
      ae_deta := fun s hs =>
        (hsp.ae_deta s hs).trans
          (hUniq c ν hc hν V hV u uq uη W Wq Wη hdat hwk s ⟨hs.1.le, hs.2.le⟩).2.2.symm
      spatial_smooth := hsp.spatial_smooth
      periodic := hsp.periodic
      div_free := hsp.div_free
      memL2_all := hsp.memL2_all
      cont_all := hsp.cont_all }

end UnforcedLeray.Short.IIb
