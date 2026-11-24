import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Lib.AxisymmetricB.AxisRegularity

/-!
# Part II-b, task `PartII-b:G4/4/1/1/2` (`RawJointSmooth`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1205-1235
(`sct:lift`: the ring lift of the train stream is smooth through the axis for positive time)
and 2355-2383.

The axis extension `p.raw τ = axisExt (Nv ..)` is smooth through the axis exactly when the
off-axis ring lift has the parity form `G(τ, ρ², z)(y₀, y₁, 0) + H(τ, ρ², z) e_z` with `G, H`
smooth on `ρ² ≥ 0` (`AxisRegularity.parityField`, tex 2967-2990).  `rawParityForm` is that
source fact (the stream `ψ` of the train is smooth and decays with all its derivatives in the
age, line 2049; `RawJointSmooth` is then composition with `(τ, y) ↦ (τ, ρ², z)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi

/-- **Parity form of `U_raw`** (SP 1205-1235, `sct:lift`; tex 2967-2990): off the axis,
`p.raw τ y = G(τ, ρ², z) (y₀, y₁, 0) + H(τ, ρ², z) e_z` with `G, H` jointly `C^∞` in
`(τ, ρ², z)` on `ρ² ≥ 0`. -/
def RawParityForm : Prop :=
  InletPiece fun p _ => ∃ G H : ℝ × (ℝ × ℝ) → ℝ,
    ContDiffOn ℝ ∞ G {x | 0 ≤ x.2.1} ∧ ContDiffOn ℝ ∞ H {x | 0 ≤ x.2.1} ∧
    ∀ (τ : ℝ) (y : Space), y ∉ UnforcedLeray.Axi.axis →
      p.raw τ y = G (τ, y 0 ^ 2 + y 1 ^ 2, y 2) • UnforcedLeray.Axi.hor y +
        H (τ, y 0 ^ 2 + y 1 ^ 2, y 2) • UnforcedLeray.Axi.e3


/-- Off-axis points accumulate at every point: `𝓝[axisᶜ] y` is nontrivial. -/
theorem axisCompl_neBot (y : Space) : (𝓝[UnforcedLeray.Axi.axisᶜ] y).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  have key : ∀ t : ℝ, 0 < t → t < ε → y 0 + t ≠ 0 →
      ∃ b ∈ UnforcedLeray.Axi.axisᶜ, dist y b < ε := by
    intro t ht htε hne
    refine ⟨y + t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ), ?_, ?_⟩
    · intro h
      have h0 := h.1
      simp at h0
      exact hne h0
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul]
      simp
      rw [abs_of_pos ht]
      exact htε
  by_cases h2 : y 0 + ε / 2 = 0
  · exact key (ε / 4) (by linarith) (by linarith) (by intro h; linarith)
  · exact key (ε / 2) (by linarith) (by linarith) h2

/-- **`PartII-b:G4/4/1/1/2`, conditional form.** -/
theorem rawJointSmooth_of (h : RawParityForm) : RawJointSmooth := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h Sig lam q hSig hq dm dp hdm
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hν hs hm i
  obtain ⟨G, Hh, hG, hH, heq⟩ := H p d hreg hν hs hm i
  have hmap : ContDiff ℝ ∞ (fun x : ℝ × Space => (x.1, x.2 0 ^ 2 + x.2 1 ^ 2, x.2 2)) := by
    fun_prop
  have hmaps : Set.MapsTo (fun x : ℝ × Space => (x.1, x.2 0 ^ 2 + x.2 1 ^ 2, x.2 2)) Set.univ
      {x : ℝ × (ℝ × ℝ) | 0 ≤ x.2.1} := by
    intro x _
    show 0 ≤ x.2 0 ^ 2 + x.2 1 ^ 2
    positivity
  have hGc : ContDiff ℝ ∞ (fun x : ℝ × Space => G (x.1, x.2 0 ^ 2 + x.2 1 ^ 2, x.2 2)) := by
    rw [← contDiffOn_univ]
    exact hG.comp hmap.contDiffOn hmaps
  have hHc : ContDiff ℝ ∞ (fun x : ℝ × Space => Hh (x.1, x.2 0 ^ 2 + x.2 1 ^ 2, x.2 2)) := by
    rw [← contDiffOn_univ]
    exact hH.comp hmap.contDiffOn hmaps
  have hF : ContDiff ℝ ∞ (fun x : ℝ × Space =>
      G (x.1, x.2 0 ^ 2 + x.2 1 ^ 2, x.2 2) • UnforcedLeray.Axi.hor x.2 +
        Hh (x.1, x.2 0 ^ 2 + x.2 1 ^ 2, x.2 2) • UnforcedLeray.Axi.e3) :=
    (hGc.smul (UnforcedLeray.Axi.contDiff_hor.comp contDiff_snd)).add (hHc.smul contDiff_const)
  have hfun : (fun x : ℝ × Space => p.raw x.1 x.2) = fun x : ℝ × Space =>
      G (x.1, x.2 0 ^ 2 + x.2 1 ^ 2, x.2 2) • UnforcedLeray.Axi.hor x.2 +
        Hh (x.1, x.2 0 ^ 2 + x.2 1 ^ 2, x.2 2) • UnforcedLeray.Axi.e3 := by
    funext x
    obtain ⟨τ, y⟩ := x
    show p.raw τ y = _
    by_cases hy : y ∈ UnforcedLeray.Axi.axis
    · haveI := axisCompl_neBot y
      have hcont : Continuous (fun z : Space => G (τ, z 0 ^ 2 + z 1 ^ 2, z 2) • UnforcedLeray.Axi.hor z +
          Hh (τ, z 0 ^ 2 + z 1 ^ 2, z 2) • UnforcedLeray.Axi.e3) :=
        (hF.continuous.comp (continuous_const.prodMk continuous_id))
      have htend : Tendsto (UnforcedLeray.Cons.C03.Concrete.Params.raw p τ) (𝓝[UnforcedLeray.Axi.axisᶜ] y)
          (𝓝 (G (τ, y 0 ^ 2 + y 1 ^ 2, y 2) • UnforcedLeray.Axi.hor y +
            Hh (τ, y 0 ^ 2 + y 1 ^ 2, y 2) • UnforcedLeray.Axi.e3)) := by
        refine ((hcont.tendsto y).mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (heq τ z hz).symm
      have hlim : UnforcedLeray.Cons.C03.Concrete.axisExt
          (UnforcedLeray.Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ) y
          = G (τ, y 0 ^ 2 + y 1 ^ 2, y 2) • UnforcedLeray.Axi.hor y +
            Hh (τ, y 0 ^ 2 + y 1 ^ 2, y 2) • UnforcedLeray.Axi.e3 := by
        simp only [UnforcedLeray.Cons.C03.Concrete.axisExt, hy, ↓reduceIte]
        refine Tendsto.limUnder_eq ?_
        refine htend.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact p.raw_eq_off_axis τ z hz
      exact hlim
    · exact (heq τ y hy)
  rw [hfun]
  exact hF

end UnforcedLeray.Short.IIb
