import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# `inletFnMemLp` (decomposition): `F_n = -∂_j(L₀E_i + B_raw E_i) ∈ L^{q0E}`

Source `the November 2 reference manuscript`
lines 2542-2551 (large radius: `C_{k,N} ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`, whose `p`-th integral is
`∫_R^∞ ϱ^{2-p(3+k)} dϱ < ∞`; on `ϱ < R` the heat expansion gives arbitrary axial decay and the
inlet cutoff vanishes near the axis; uniform in phase), 2563-2569, 1206-1222.

Three leaves: measurability (`InletFnMeas`), the pointwise envelope (`InletFnEnvelope`), and the
integrability of the envelope (`cylProfile_memLp`).  The assembly `inletFnMemLp_of` is proved.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The cylindrical envelope (2545-2549): `ϱ^{-3}(1+|y₃|/ϱ)^{-2}` for `ϱ > R₀`, and
`(1+|y₃|)^{-2}` on the near-axis region `ϱ ≤ R₀` (arbitrary axial decay). -/
def cylProfile (R0 : ℝ) (y : UnforcedLeray.Space) : ℝ :=
  if Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 then (1 + |y 2|) ^ (-2 : ℝ)
  else Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
    (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ)

/-- **Leaf 1** (cylinder integrability, 2547-2549): `cylProfile R₀ ∈ L^{q0E}(ℝ³)`.  Cylindrical
Fubini: `∫_ℝ (1+|z|/ϱ)^{-2q} dz = c ϱ`, so the radial integral is `∫_R^∞ ϱ^{2-3q} dϱ < ∞`
since `q = 11/4`; near the axis `(1+|z|)^{-2q}` is integrable and the disc has finite area. -/
def CylProfileMemLp : Prop :=
  ∀ R0 : ℝ, 0 < R0 → MemLp (cylProfile R0) UnforcedLeray.B0412.q0E volume

/-- **Leaf 2** (measurability): `F_n` is a.e. strongly measurable for the phase measure (the inlet
and `raw` are jointly smooth in `(τ,y)`, 2563-2569). -/
def InletFnMeas : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j : Fin 3),
    AEStronglyMeasurable (inletFn p i j)
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume)

/-- **Leaf 3** (pointwise envelope, 2542-2551, 2563-2569, 1206-1222): there are `C` and `R₀ > 0`
with `‖F_n(τ,y)‖ ≤ C · cylProfile R₀ y` for every phase `τ ∈ (0,P]` and every `y`: the large-radius
bounds `C ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}` on the unprojected derivatives of `E_i` and `raw`, the heat
expansion near the axis, and the vanishing of the inlet cutoff near the axis (constants may depend
on `p`; only finiteness is needed). -/
def InletFnEnvelope : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j : Fin 3), ∃ C R0 : ℝ, 0 < R0 ∧
    ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
      ‖inletFn p i j (τ, y)‖ ≤ C * cylProfile R0 y

theorem inletFnMemLp_of (h1 : CylProfileMemLp) (h2 : InletFnMeas) (h3 : InletFnEnvelope) :
    InletFnMemLp := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := h2 lam q hq dm dp hdm
  obtain ⟨ν₃, hν₃, H3⟩ := h3 lam q hq dm dp hdm
  refine ⟨min ν₂ ν₃, lt_min hν₂ hν₃, fun p d hreg hν hm z g hg i j => ?_⟩
  have hm2 := H2 p d hreg (hν.trans (min_le_left _ _)) hm z g hg i j
  obtain ⟨C, R0, hR0, hb⟩ := H3 p d hreg (hν.trans (min_le_right _ _)) hm z g hg i j
  have hμ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) p.period)) :=
    ⟨by simp⟩
  have hg1 : MemLp (fun x : ℝ × UnforcedLeray.Space => C * cylProfile R0 x.2)
      UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) :=
    ((h1 R0 hR0).const_mul C).comp_snd (volume.restrict (Ioc (0 : ℝ) p.period))
  refine hg1.mono' hm2 ?_
  have hae : ∀ᵐ x ∂((volume.restrict (Ioc (0 : ℝ) p.period)).prod
      (volume : Measure UnforcedLeray.Space)), x.1 ∈ Ioc (0 : ℝ) p.period :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hae] with x hx
  exact hb x.1 hx x.2

end UnforcedLeray.Short.PartIIIb.Concrete
