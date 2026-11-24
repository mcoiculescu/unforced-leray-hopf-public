import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_of
import UnforcedLeray.Units.B0224.FiberSymm
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0DivFreeC
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0OrthC

/-!
# Audit decomposition of `PepsC0SliceSolenoidal` and `PepsC0SliceOrth`

Source `the November 2 reference manuscript`
1650-1656, 1676.  All integrals over the slice use the profile strip `(0,c] × ℝ`
(the support of `cellMeasure c`); periodicity in `q` moves it to the centred cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (P0C)

/-- The profile strip `(0,c] × ℝ` in the `(q,η)`-plane. -/
def stripSet (c : ℝ) : Set (ℝ × ℝ) := Ioc 0 c ×ˢ (univ : Set ℝ)

/-! ## Solenoidality of `Ψ` -/

/-- **(A1) Fubini for the pairing with a test gradient** (source 1650-1656, 1676).  For a profile
test `Φt` with `cgrad 0 Φt ∈ L²(measureH c)` and `Ψ ∈ L²(measureH c)`:
`⟪cgrad 0 Φt, Ψ⟫ = ∫_{s>0} s^(-3/2) ∫_{strip} Σ_i (cgrad 0 Φt)_i(s,x) Ψ_i(s,x) dx ds`
(`cgrad` is real-valued so no conjugation; `measureH c = s^(-3/2) ds × (Lebesgue on the strip)`,
`B0224.cellMeasure_eq_prod'`, `B0224.integral_measureH_eq_iter`; integrability from Cauchy-Schwarz
of the two `L²` factors). -/
def PepsC0FubiniSol : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (Φt : UnforcedLeray.B0226.ProfileTest c)
    (hg : MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φt.1) 2 (UnforcedLeray.B0220.measureH c))
    (Ψ : Chart → Fin 2 → ℂ)
    (hmem : MemLp (fun p => toMC (Ψ p)) 2 (UnforcedLeray.B0220.measureH c)),
    inner ℂ (hg.toLp _) (hmem.toLp _) =
      ∫ s in Ioi (0 : ℝ), ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ x in stripSet c, ∑ i : Fin 2, (UnforcedLeray.Short.PartIIa.cgrad 0 Φt.1 (s, x)) i * Ψ (s, x) i

/-- **(A2) Each slice pairing vanishes** (source 1650-1656, 1676).  Let `Φt` be a profile test and
`Ψ` `c`-periodic in `q` with `Ψ(σ,·) = P0C Φ_σ` a.e. on the cell for some `Φ_σ`.  Then
`cgrad 0 Φt (σ,·) = (∂_q, ∂_η)` of the slice `Φt(σ,·)`, which is a `B0579.IsCylTest`
(`UnforcedLeray.B0226.Deps_zero`), the strip integral equals the cell integral by periodicity
(`p1_strip_cell`-type shift for `ℂ`-valued integrals, e.g. `B0226.setIntegral_Ioc_add_periodic`),
and `IIIa.p0DivFreeC` gives `0`. -/
def PepsC0SliceDivFreeZero : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (Φt : UnforcedLeray.B0226.ProfileTest c) (Φ Ψ : Chart → Fin 2 → ℂ),
    (∀ s q η, Ψ (s, (q + c, η)) = Ψ (s, (q, η))) →
    ∀ σ : ℝ, 0 < σ →
      (fun y => Ψ (σ, y)) =ᵐ[UnforcedLeray.Cyl.cellμ c] P0C c (fun y => Φ (σ, y)) →
      ∫ x in stripSet c, ∑ i : Fin 2, (UnforcedLeray.Short.PartIIa.cgrad 0 Φt.1 (σ, x)) i * Ψ (σ, x) i = 0

theorem pepsC0SliceSolenoidal_of (h1 : PepsC0FubiniSol) (h2 : PepsC0SliceDivFreeZero) :
    PepsC0SliceSolenoidal := by
  intro c hc f' Φ Ψ hH hmem
  obtain ⟨_, _, _, hΨp, _, hΨ⟩ := hH
  unfold UnforcedLeray.Short.PartIIa.solenoidalHC
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Φt, hg, rfl⟩ := hx
    rw [h1 c hc Φt hg Ψ hmem]
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    rw [h2 c hc Φt Φ Ψ hΨp s hs (hΨ s hs), mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/-! ## Orthogonality of `f' - Ψ` -/

/-- **(B0) Almost every slice of an `L²(measureH c)` field is `L²` on the strip** (source
1650-1656, 1676; Tonelli with `B0224.cellMeasure_eq_prod'`, `B0224.lintegral_measureH_eq`). -/
def PepsC0SliceMemLp : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Chart → Fin 2 → ℂ,
    MemLp (fun p => toMC (F p)) 2 (UnforcedLeray.B0220.measureH c) →
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      MemLp (fun x : ℝ × ℝ => toMC (F (s, x))) 2 (volume.restrict (stripSet c))

/-- **(B1) A.e. slice of `b ∈ solenoidalHC 0 c` is weakly divergence free** (source 1650-1656,
1676).  Test `b` against `cgrad 0 (χ(s) s^(3/2) ψ(q,η))` with `χ ∈ C_c^∞(0,∞)` and `ψ` ranging over a
countable family of `B0579.IsCylTest`s dense in the sense that every cylinder test is a limit in
`C^1` with common support bound (a countable family is needed to exchange "a.e. `s`" and
"for all `ψ`"); the `s`-weight is absorbed since `measureH c` carries `s^(-3/2)`, `χ` arbitrary
gives vanishing for a.e. `s`. -/
def PepsC0SliceDivFreeAE : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ b ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c,
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ →
        ∫ x in stripSet c,
          ((b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 0 *
              (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
            (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 1 *
              (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) = 0

/-- **(B2) Slice orthogonality** (source 1650-1656, 1676; `IIIa.p0OrthC`, `Cyl.inner_P0_comm`,
`Cyl.P0_eq_self`).  `Φs, Ψs` are `c`-periodic in `q`, `L²` on the strip, `Ψs = P0C Φs` a.e. on the
cell; `v` is `L²` on the strip and weakly divergence free against every `B0579.IsCylTest`
(strip integral).  Then `∫_strip Σ conj(Φs - Ψs)_i v_i = 0`.  Proof: the periodic extension of `v`
is weakly divergence free on the cylinder; `Re/Im` parts of `v` lie in `Cyl.divFree c`; `conj(P0 f)
= P0 (conj f)` and `P0 f - f ⟂ divFree` (`Cyl.inner_P0_comm`, `Cyl.P0_eq_self`); periodic strip/cell
shift. -/
def PepsC0SliceOrthCell : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (Φs Ψs v : ℝ × ℝ → Fin 2 → ℂ),
    (∀ q η, Φs (q + c, η) = Φs (q, η)) → (∀ q η, Ψs (q + c, η) = Ψs (q, η)) →
    MemLp (fun x => toMC (Φs x)) 2 (volume.restrict (stripSet c)) →
    MemLp (fun x => toMC (Ψs x)) 2 (volume.restrict (stripSet c)) →
    MemLp (fun x => toMC (v x)) 2 (volume.restrict (stripSet c)) →
    Ψs =ᵐ[UnforcedLeray.Cyl.cellμ c] P0C c Φs →
    (∀ ψ : ℝ × ℝ → ℝ, UnforcedLeray.B0579.IsCylTest c ψ →
      ∫ x in stripSet c,
        (v x 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) + v x 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) = 0) →
    ∫ x in stripSet c, ∑ i : Fin 2, (starRingEnd ℂ) (Φs x i - Ψs x i) * v x i = 0

/-- **(B3) Fubini for the pairing of two `L²(measureH c)` fields** (source 1650-1656, 1676;
`B0224.cellMeasure_eq_prod'`, `B0224.integral_measureH_eq_iter`).  Here `f' = Φ` a.e., `Ψ`
represents `hmem.toLp`. -/
def PepsC0FubiniOrth : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (Φ Ψ : Chart → Fin 2 → ℂ) (_ : SliceHyp c f' Φ Ψ)
    (hmem : MemLp (fun p => toMC (Ψ p)) 2 (UnforcedLeray.B0220.measureH c))
    (b : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC),
    inner ℂ (f' - hmem.toLp _) b =
      ∫ s in Ioi (0 : ℝ), ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ x in stripSet c, ∑ i : Fin 2, (starRingEnd ℂ) (Φ (s, x) i - Ψ (s, x) i) *
          (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) i

theorem pepsC0SliceOrth_of (h0 : PepsC0SliceMemLp) (h1 : PepsC0SliceDivFreeAE)
    (h2 : PepsC0SliceOrthCell) (h3 : PepsC0FubiniOrth) : PepsC0SliceOrth := by
  intro c hc f' Φ Ψ hH hmem b hb
  have hH' : SliceHyp c f' Φ Ψ := hH
  obtain ⟨_, _, hΦp, hΨp, hf, hΨ⟩ := hH'
  rw [h3 c hc f' Φ Ψ hH hmem b]
  have hΦmem : MemLp (fun p => toMC (Φ p)) 2 (UnforcedLeray.B0220.measureH c) :=
    (Lp.memLp f').ae_eq hf
  have hbmem : MemLp (fun p => toMC (fun i => (b : UnforcedLeray.B0220.Profile →
      UnforcedLeray.B0223.MeridC) p i)) 2 (UnforcedLeray.B0220.measureH c) := Lp.memLp b
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, h0 c hc Φ hΦmem, h0 c hc Ψ hmem,
    h0 c hc _ hbmem, h1 c hc b hb] with s hs hΦs hΨs hbs hdiv
  have key := h2 c hc (fun x => Φ (s, x)) (fun x => Ψ (s, x)) (fun x => (b : UnforcedLeray.B0220.Profile →
      UnforcedLeray.B0223.MeridC) (s, x) |>.ofLp) (fun q η => hΦp s q η) (fun q η => hΨp s q η)
    hΦs hΨs hbs (hΨ s hs) (fun ψ hψ => hdiv ψ hψ)
  simp only [Pi.zero_apply]
  rw [key, mul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
